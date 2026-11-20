  /-!
# ProtocolsDolevYao.lean -- Consolidated Shallow Dolev-Yao Proofs

Machine-checked Dolev-Yao attack (and safety) witnesses for the
thirteen High-severity protocols identified by the ML risk ranking
(`risk_analysis_consolidated.ipynb`).

Each protocol is preceded by a plain-language explanation of its
message flow, the vulnerability, and how the code below captures it,
so the file can be read top-to-bottom by someone meeting these
protocols for the first time.

Two complementary modelling styles are used, matched to the attack:

* **Section A -- session-level Dolev-Yao (Parts I-VIII).** Six protocols
  are modelled with a shared symbolic message algebra (`Message`),
  explicit network events (`Event` / `Trace`), and a single Dolev-Yao
  deductive closure (`Derivable`). Attacks are exhibited as concrete
  multi-message witness traces. This suits protocol-message attacks
  (interleavings, replays, downgrades).

* **Section B -- cipher-level / algebraic breaks (Parts IX-XV).** Seven
  protocols whose weakness is a break of a cryptographic primitive
  (key recovery, keystream reuse, encoding inversion, key-space split)
  are each modelled with a small bespoke `Message` / `Derivable` in
  their own namespace, where the documented break is stated as an
  explicit deduction rule and the witness theorem shows the secret
  lies in the attacker's deductive closure. These local definitions
  deliberately shadow the shared ones of Section A within their
  namespaces.

All thirteen protocols and their headline theorems are listed in the
summary at the foot of the file. The file is self-contained: it
imports nothing beyond the Lean 4 core library.

Author     : Raj Guru Suwalka
Supervisor : Dr. Edon Kelmendi
MSc Project, Queen Mary University of London, 2025-26
-/

------------------------------------------------------------------
--  SECTION A.  Session-level Dolev-Yao  (shared message algebra)
--  Six protocols: NS-PK, NS-Lowe, NS-Sym, DH-basic, SSL 3.0, WEP.
------------------------------------------------------------------

------------------------------------------------------------------
-- Part I.  Shared formal framework
------------------------------------------------------------------

/-- The four agents modelled in the protocols of this file:
`A` is the honest initiator, `B` the honest responder, `I` the
network adversary, `S` a trusted server / key-distribution centre. -/
inductive Agent where
  | A
  | B
  | I
  | S
deriving DecidableEq, Repr

/-- The space of symbolic protocol messages.  Encryption is modelled
abstractly in the Dolev-Yao style: `encrypt a m` represents `m`
encrypted under `a`'s public key, and `encryptSym k m` represents
`m` encrypted under symmetric key `k`. -/
inductive Message where
  | nonce       : Nat   → Message
  | timestamp   : Nat   → Message
  | key         : Nat   → Message
  | agent       : Agent → Message
  | pair        : Message → Message → Message
  | encrypt     : Agent → Message → Message
  | encryptSym  : Nat   → Message → Message
deriving DecidableEq, Repr

/-- A network event: agent `sender` sends `payload` to agent
`receiver`.  The intruder I observes every event. -/
structure Event where
  sender   : Agent
  receiver : Agent
  payload  : Message
deriving DecidableEq, Repr

/-- A trace is a list of events; the *head* of the list is the
most-recent event.  Read attack traces bottom-to-top for the natural
chronological order. -/
abbrev Trace := List Event

/-- Project the payloads from a trace — the multiset of messages
observable by the intruder. -/
def Trace.messages : Trace → List Message
  | []         => []
  | e :: rest  => e.payload :: Trace.messages rest

/-- A convenient short notation for constructing an event. -/
private def ev (s r : Agent) (m : Message) : Event := ⟨s, r, m⟩

------------------------------------------------------------------
-- Part II.  Dolev-Yao intruder model
------------------------------------------------------------------

/-- `Derivable ms m` is the standard Dolev-Yao closure: the intruder,
having observed the multiset of messages `ms`, can synthesise `m`.

The rules:
  • directly observed messages are known (`seen`);
  • agent identifiers are public (`agentPub`);
  • pairs may be constructed and projected (`pair`, `proj₁`, `proj₂`);
  • messages may be encrypted under any agent's public key
    (`encryptPub`);
  • the intruder may decrypt messages encrypted under *its own* public
    key (`decryptI`);
  • symmetric encryption is reversible by any holder of the key
    (`encryptSym`, `decryptSym`).

This is a deliberately small but standard fragment of Dolev-Yao,
sufficient for the protocols verified below. -/
inductive Derivable : List Message → Message → Prop where
  | seen       : ∀ {ms m}, m ∈ ms → Derivable ms m
  | agentPub   : ∀ ms a, Derivable ms (Message.agent a)
  | pair       : ∀ {ms m₁ m₂},
      Derivable ms m₁ → Derivable ms m₂ →
        Derivable ms (Message.pair m₁ m₂)
  | proj₁      : ∀ {ms m₁ m₂},
      Derivable ms (Message.pair m₁ m₂) → Derivable ms m₁
  | proj₂      : ∀ {ms m₁ m₂},
      Derivable ms (Message.pair m₁ m₂) → Derivable ms m₂
  | encryptPub : ∀ {ms a m},
      Derivable ms m → Derivable ms (Message.encrypt a m)
  | decryptI   : ∀ {ms m},
      Derivable ms (Message.encrypt Agent.I m) → Derivable ms m
  | encryptSymR : ∀ {ms k m},
      Derivable ms (Message.key k) → Derivable ms m →
        Derivable ms (Message.encryptSym k m)
  | decryptSymR : ∀ {ms k m},
      Derivable ms (Message.key k) →
      Derivable ms (Message.encryptSym k m) →
        Derivable ms m

------------------------------------------------------------------
-- Part III.  Needham-Schroeder Public-Key  —  Lowe's MITM attack
------------------------------------------------------------------

/-!
### Needham-Schroeder Public-Key -- protocol and Lowe's attack (explained)

**What it is.** A 1978 mutual-authentication protocol. A (initiator) and B
(responder) each generate a fresh nonce and prove to the other that they
can decrypt it, using the other party's public key.

**Message flow (the honest run).**
  1.  A -> B :  {N_a, A}_PK(B)      -- A sends a fresh nonce and its name
  2.  B -> A :  {N_a, N_b}_PK(A)    -- B returns A's nonce plus its own
  3.  A -> B :  {N_b}_PK(B)         -- A returns B's nonce
At the end each believes it shares N_a, N_b with the other.

**The flaw (Lowe 1995).** Message 2 does *not* name B inside the
encryption. So if A starts a session with a (malicious) party I, then I can
strip A's outer encryption and *replay the inner content to B as if from A*,
running a second session in parallel. B completes the protocol believing it
spoke to A, when in fact every message B received originated with I, and I
learns B's secret nonce N_b (which A helpfully returned to I under I's own
public key in the first session).

**In this formalisation.** `msg1/msg2/msg3` are the three messages;
`lowe_trace` is the five-event interleaving of the two sessions;
`ns_pk_mitm_attack` certifies that B believes the session completed yet
every event addressed to B was sent by I; `intruder_learns_Nb` certifies
that I derives N_b via the Dolev-Yao rule `decryptI`.
-/
namespace NS_PK

/-- Step 1 :  `init → resp : {Nₐ, init}_PK(resp)`. -/
def msg1 (init resp : Agent) (Na : Nat) : Message :=
  Message.encrypt resp
    (Message.pair (Message.nonce Na) (Message.agent init))

/-- Step 2 (original, *flawed*) :  `resp → init : {Nₐ, N_b}_PK(init)`.
Crucially, the responder's identity does **not** appear inside the
encrypted payload — this is the omission Lowe exploited. -/
def msg2 (init : Agent) (Na Nb : Nat) : Message :=
  Message.encrypt init
    (Message.pair (Message.nonce Na) (Message.nonce Nb))

/-- Step 3 :  `init → resp : {N_b}_PK(resp)`. -/
def msg3 (resp : Agent) (Nb : Nat) : Message :=
  Message.encrypt resp (Message.nonce Nb)

/-- Lowe's MITM trace: A runs a session with the intruder I; I in
parallel reuses A's nonce to impersonate A to B.  Listed
most-recent-first; chronological order is bottom-to-top.

The five events correspond to the five messages of the canonical
Lowe attack.  Specific nonce values 1 (Nₐ) and 2 (N_b) are chosen
for concreteness; any pair would work. -/
def lowe_trace : Trace :=
  [ ev Agent.I Agent.B (msg3 Agent.B 2),         -- 5. I → B : {N_b}_PK(B)
    ev Agent.A Agent.I (msg3 Agent.I 2),         -- 4. A → I : {N_b}_PK(I)
    ev Agent.B Agent.A (msg2 Agent.A 1 2),       -- 3. B → A : {Nₐ, N_b}_PK(A)
    ev Agent.I Agent.B (msg1 Agent.A Agent.B 1), -- 2. I → B : {Nₐ, A}_PK(B)
    ev Agent.A Agent.I (msg1 Agent.A Agent.I 1)  -- 1. A → I : {Nₐ, A}_PK(I)
  ]

/-- B's *protocol-level view*: from B's perspective the session has
completed if B has received messages 1 and 3 addressed to B and
nominally from A (the identity is buried inside the encryption). -/
def B_completed (tr : Trace) (Na Nb : Nat) : Prop :=
  (∃ s, ev s Agent.B (msg1 Agent.A Agent.B Na) ∈ tr) ∧
  (∃ s, ev s Agent.B (msg3 Agent.B Nb)        ∈ tr)

/-- **Lowe's attack, certified at the trace level.**  In `lowe_trace`
B believes he has completed a session with A using nonces 1 and 2,
yet every event addressed to B in the trace was originated by the
intruder I, not by A. -/
theorem ns_pk_mitm_attack :
    B_completed lowe_trace 1 2 ∧
    (∀ e ∈ lowe_trace, e.receiver = Agent.B → e.sender = Agent.I) := by
  refine ⟨⟨⟨Agent.I, ?_⟩, ⟨Agent.I, ?_⟩⟩, ?_⟩
  · -- ev I B (msg1 A B 1) ∈ lowe_trace
    show ev Agent.I Agent.B (msg1 Agent.A Agent.B 1) ∈ lowe_trace
    simp [lowe_trace, ev]
  · -- ev I B (msg3 B 2) ∈ lowe_trace
    show ev Agent.I Agent.B (msg3 Agent.B 2) ∈ lowe_trace
    simp [lowe_trace, ev]
  · -- Every event addressed to B is in fact from I.
    intro e he hrcv
    simp [lowe_trace, ev] at he
    -- `he` is a disjunction of five equalities; case-split.
    rcases he with rfl | rfl | rfl | rfl | rfl
    all_goals first | rfl | (simp at hrcv)

/-- **The intruder learns B's secret nonce N_b.**  The intruder
observes message 4 of the trace — A's reply `{N_b}_PK(I)` — and since
that ciphertext is encrypted under I's own public key, I decrypts it
and learns N_b.  At this point I knows both nonces of the session and
can complete the impersonation. -/
theorem intruder_learns_Nb :
    Derivable (Trace.messages lowe_trace) (Message.nonce 2) := by
  apply Derivable.decryptI
  apply Derivable.seen
  -- {N_b}_PK(I) is in the messages of lowe_trace.
  show Message.encrypt Agent.I (Message.nonce 2) ∈ Trace.messages lowe_trace
  simp [Trace.messages, lowe_trace, ev, msg3]

end NS_PK

------------------------------------------------------------------
-- Part IV.  Needham-Schroeder-Lowe  —  contrast safety proof
------------------------------------------------------------------

/-!
### Needham-Schroeder-Lowe -- the fix, and why it is safe (explained)

**What it is.** Lowe's one-line correction to the protocol above: bind the
responder's identity *inside* message 2.
  2'.  B -> A :  {N_a, N_b, B}_PK(A)    -- now B's name is inside the cipher

**Why it blocks the attack.** In the original attack I replayed B's message
to A. With B's identity now sealed inside the encryption, the message A
expects from B is structurally different from anything I can manufacture by
relaying: A checks for B's name in the agreed position and rejects a message
that lacks it. The attack message and the accepted message are simply not
the same shape.

**In this formalisation.** `msg2_lowe` (fixed) and `msg2_old` (broken) are
placed side by side; `msg2_shape_distinct` proves they can never be equal as
Lean values (different constructor structure); `ns_lowe_blocks_old_attack`
concludes that A's strengthened acceptance predicate rejects every
old-style message. This is a *safety* result -- the contrast that shows the
fix works -- rather than an attack.
-/
namespace NS_Lowe

/-- Lowe's corrected step 2: B's identity is bound *inside* the
encryption.  `resp → init : {Nₐ, N_b, B}_PK(init)`. -/
def msg2_lowe (init resp : Agent) (Na Nb : Nat) : Message :=
  Message.encrypt init
    (Message.pair
      (Message.pair (Message.nonce Na) (Message.nonce Nb))
      (Message.agent resp))

/-- The original (broken) step 2 from Part III, repeated here so the
two can be compared. -/
def msg2_old (init : Agent) (Na Nb : Nat) : Message :=
  Message.encrypt init
    (Message.pair (Message.nonce Na) (Message.nonce Nb))

/-- A's strengthened acceptance predicate: A only accepts a step 2
message that contains B's identity in the expected position. -/
def StrongAcceptance (m : Message) : Prop :=
  ∃ Na Nb, m = msg2_lowe Agent.A Agent.B Na Nb

/-- **Structural safety**: for every choice of nonces, the original
(broken) step 2 message is *not* of the shape Lowe's strengthened
acceptance predicate requires.  The two messages have different
top-level pair structure — `pair (pair _ _) (agent B)` versus
`pair _ _` — so they cannot be equal as Lean values. -/
theorem msg2_shape_distinct (Na Nb Na' Nb' : Nat) :
    msg2_old Agent.A Na Nb ≠ msg2_lowe Agent.A Agent.B Na' Nb' := by
  intro h
  -- After unfolding both definitions, `h` equates
  --   encrypt A (pair (nonce Na) (nonce Nb))
  -- with
  --   encrypt A (pair (pair (nonce Na') (nonce Nb')) (agent B))
  -- The two inner pairs have different first components
  -- (`nonce Na` vs `pair (nonce Na') (nonce Nb')`) which are
  -- distinct constructors of `Message`.
  simp [msg2_old, msg2_lowe] at h

/-- **Lowe's correction blocks the original attack.**  Whatever
nonces the intruder might insert into the old-style message
`msg2_old A Na Nb`, A's strengthened acceptance check rejects it. -/
theorem ns_lowe_blocks_old_attack :
    ∀ Na Nb, ¬ StrongAcceptance (msg2_old Agent.A Na Nb) := by
  intro Na Nb h
  rcases h with ⟨Na', Nb', hEq⟩
  exact msg2_shape_distinct Na Nb Na' Nb' hEq

end NS_Lowe

------------------------------------------------------------------
-- Part V.  Needham-Schroeder Symmetric  —  Denning-Sacco replay
------------------------------------------------------------------

/-!
### Needham-Schroeder Symmetric -- the Denning-Sacco replay (explained)

**What it is.** The symmetric-key sibling of the protocol above (1978). A
trusted server S shares a long-term key with every party and issues session
keys. The step that matters here is the *ticket* A forwards to B:
  3.  A -> B :  {K_ab, A}_K(BS)     -- "here is our session key, from S"
B decrypts the ticket with its long-term key K_BS and accepts K_ab.

**The flaw (Denning-Sacco 1981).** The ticket carries no timestamp and no
value B can check for freshness. If an old session key K_ab is ever
compromised (e.g. recovered offline years later), the attacker can *replay
the old ticket* to B, who has no way to tell it is stale and accepts the
compromised key as current.

**In this formalisation.** `step3` is the ticket; `replayedTicket` is an old
ticket held by the intruder; `replayTrace` is a single-event trace in which
I sends it to B; `ns_sym_concrete_attack` certifies B accepts it, and
`ns_sym_replay_universal` shows this works for *any* compromised key. The
`fake`/`seen` derivation shows the replay needs no decryption at all.
-/
namespace NS_Sym

/-- B's long-term key shared with the KDC `S`, modelled as a fixed
opaque numeric tag. -/
def Kbs : Nat := 100

/-- Step 3 of NS-Sym: A forwards to B the KDC-issued ticket
`{Kab, A}_Kbs`.  The ticket contains no timestamp and no nonce that
B can verify for freshness — this is the Denning-Sacco flaw. -/
def step3 (Kab : Nat) : Message :=
  Message.encryptSym Kbs
    (Message.pair (Message.key Kab) (Message.agent Agent.A))

/-- B's acceptance: B accepts any message of step-3 shape, with no
freshness check on `Kab`. -/
def BAccepts (m : Message) : Prop :=
  ∃ Kab, m = step3 Kab

/-- The Denning-Sacco attack: the intruder has obtained an old
session key `Kab_old` from a previous run of the protocol (perhaps
years ago, via offline cryptanalysis of the DES traffic of that era),
and replays the ticket containing it. -/
def replayedTicket (Kab_old : Nat) : Message :=
  Message.encryptSym Kbs
    (Message.pair (Message.key Kab_old) (Message.agent Agent.A))

/-- Concrete attack trace: I replays an old ticket directly to B,
who accepts.  Listed most-recent-first.

The trace deliberately contains no preceding KDC interaction —
because none is required.  The replay only needs the old ticket. -/
def replayTrace (Kab_old : Nat) : Trace :=
  [ ev Agent.I Agent.B (replayedTicket Kab_old) ]

/-- **Replay is universal.**  For every choice of compromised key
`Kab_old`, B accepts the replayed ticket. -/
theorem ns_sym_replay_universal :
    ∀ Kab_old, BAccepts (replayedTicket Kab_old) := by
  intro Kab_old
  exact ⟨Kab_old, rfl⟩

/-- **A concrete attack trace witnesses the replay.**  There is a
trace `tr` containing a single event in which the intruder sends B
a replayed ticket, and B's acceptance predicate is satisfied by that
event's payload. -/
theorem ns_sym_concrete_attack :
    ∃ (tr : Trace) (e : Event),
      e ∈ tr ∧ e.sender = Agent.I ∧ e.receiver = Agent.B ∧
      BAccepts e.payload := by
  refine ⟨replayTrace 42, ev Agent.I Agent.B (replayedTicket 42),
          ?_, ?_, ?_, ?_⟩
  · -- ev I B (replayedTicket 42) ∈ replayTrace 42
    simp [replayTrace, ev]
  · -- (ev I B _).sender = Agent.I
    simp [ev]
  · -- (ev I B _).receiver = Agent.B
    simp [ev]
  · -- BAccepts (ev I B (replayedTicket 42)).payload
    show BAccepts (replayedTicket 42)
    exact ⟨42, rfl⟩

/-- **The intruder need not learn anything new to mount the attack.**
The ticket payload is already in the intruder's observation set the
moment it is sent, so the intruder trivially derives it.  This is the
Dolev-Yao formalisation of "replay requires no decryption". -/
theorem intruder_can_replay (Kab_old : Nat) :
    Derivable (Trace.messages (replayTrace Kab_old)) (replayedTicket Kab_old) := by
  apply Derivable.seen
  show replayedTicket Kab_old ∈ Trace.messages (replayTrace Kab_old)
  simp [Trace.messages, replayTrace, ev]

end NS_Sym

------------------------------------------------------------------
-- Part VI.  Diffie-Hellman (unauthenticated)  —  MITM
------------------------------------------------------------------

/-!
### Diffie-Hellman (unauthenticated) -- the classic MITM (explained)

**What it is.** The 1976 key-exchange. A and B publish g^a and g^b and each
raises the other's value to its own secret, arriving at the shared secret
g^(ab). No long-term keys, no identities.

**The flaw.** Because nothing authenticates who sent g^a or g^b, an
intruder I in the middle can run *two* exchanges: it sends its own value
g^i to both A and B, so A ends up sharing a key with I (thinking it is B)
and B ends up sharing a different key with I (thinking it is A). I then sits
between them, decrypting and re-encrypting everything.

**In this formalisation.** `dh_pub` models the public value (the modular
arithmetic is irrelevant to the attack); `mitm_trace` is the four-event
trace in which I substitutes its value to each side; `dh_basic_mitm_attack`
certifies both A and B accept I's value as their peer's;
`intruder_learns_both` shows I observes both genuine values on the wire.
-/
namespace DH_Basic

/-- A Diffie-Hellman public value `g^x` carried on the wire.
Modelled symbolically as a nonce; the actual modular-exponentiation
arithmetic is irrelevant for the MITM argument. -/
def dh_pub (x : Nat) : Message := Message.nonce x

/-- A's acceptance: A is willing to take any public value as the
counterparty's contribution, because basic DH has no authentication. -/
def A_accepts (m : Message) : Prop :=
  ∃ x, m = dh_pub x

/-- B's acceptance: symmetric to A's. -/
def B_accepts (m : Message) : Prop :=
  ∃ x, m = dh_pub x

/-- The MITM trace: I sits between A and B, sending its own value
`g^i` to each in place of the genuine value.  Specific exponents
`a = 1`, `b = 2`, `i = 7` are chosen for concreteness.  Listed
most-recent-first.

The protocol-level events (from bottom to top):
  1. A → I : g^a  (A thinks she is sending to B)
  2. B → I : g^b  (B thinks he is sending to A)
  3. I → B : g^i  (I forwards her own value to B as "from A")
  4. I → A : g^i  (I forwards her own value to A as "from B")
-/
def mitm_trace : Trace :=
  [ ev Agent.I Agent.A (dh_pub 7),
    ev Agent.I Agent.B (dh_pub 7),
    ev Agent.B Agent.I (dh_pub 2),
    ev Agent.A Agent.I (dh_pub 1) ]

/-- **DH-basic MITM, certified at the trace level.**  There is a
trace in which both A and B accept the intruder's value `g^i` as if
it were their counterparty's contribution; A's "session with B" is
in fact a session with I, and likewise B's. -/
theorem dh_basic_mitm_attack :
    A_accepts (dh_pub 7) ∧ B_accepts (dh_pub 7) ∧
    ev Agent.I Agent.A (dh_pub 7) ∈ mitm_trace ∧
    ev Agent.I Agent.B (dh_pub 7) ∈ mitm_trace := by
  refine ⟨⟨7, rfl⟩, ⟨7, rfl⟩, ?_, ?_⟩
  · simp [mitm_trace, ev]
  · simp [mitm_trace, ev]

/-- **The intruder learns both genuine public values.**  Because A
and B both transmit on the network in the clear (the only encryption
in basic DH is the implicit modular-exponentiation, modelled as a
nonce here, which the intruder need not invert), I observes `g^a`
and `g^b` directly. -/
theorem intruder_learns_both :
    Derivable (Trace.messages mitm_trace) (dh_pub 1) ∧
    Derivable (Trace.messages mitm_trace) (dh_pub 2) := by
  refine ⟨?_, ?_⟩
  · apply Derivable.seen
    show dh_pub 1 ∈ Trace.messages mitm_trace
    simp [Trace.messages, mitm_trace, ev]
  · apply Derivable.seen
    show dh_pub 2 ∈ Trace.messages mitm_trace
    simp [Trace.messages, mitm_trace, ev]

end DH_Basic

------------------------------------------------------------------
-- Part VII.  SSL 3.0  —  version-downgrade attack
------------------------------------------------------------------

/-!
### SSL 3.0 -- the version-downgrade attack (explained)

**What it is.** A session-layer protocol in which client and server
negotiate which protocol version to use, the client offering a list and the
server picking one.

**The flaw.** In SSL 3.0 the version-negotiation messages are not
integrity-protected, so neither endpoint can tell whether the offered list
was altered in transit. An active man-in-the-middle rewrites the client's
offer to advertise only the oldest, weakest version, forcing the server to
"fall back" to SSL 3.0 -- which is itself broken (this is the pre-condition
the POODLE attack then exploits, see `ProtocolsPaulson.lean`).

**In this formalisation.** `Version` enumerates the versions;
`serverAcceptsVersion` models the server taking whatever is offered;
`attackerDowngradedOffer` is the rewritten single-version list;
`ssl3_downgrade_attack` certifies the server accepts SSL 3.0, and
`ssl3_attacker_controls_version` shows the attacker can force this for *any*
honest offer that did not already contain SSL 3.0.
-/
namespace SSL3

inductive Version where
  | SSL30
  | TLS10
  | TLS12
  | TLS13
deriving DecidableEq, Repr

/-- The server's negotiation behaviour: it accepts whichever version
is offered.  In SSL 3.0 the version-negotiation messages are *not*
integrity-protected, so the server cannot tell whether the offered
list was modified in transit. -/
def serverAcceptsVersion (offered : List Version) (v : Version) : Prop :=
  v ∈ offered

/-- The honest client originally offers only modern versions. -/
def clientOriginalOffer : List Version :=
  [Version.TLS12, Version.TLS13]

/-- The active MITM attacker rewrites the offer to advertise only
SSL 3.0, forcing the server to fall back to a known-broken version. -/
def attackerDowngradedOffer : List Version :=
  [Version.SSL30]

/-- **The downgrade attack succeeds**: the server accepts SSL 3.0
from the rewritten offer. -/
theorem ssl3_downgrade_attack :
    serverAcceptsVersion attackerDowngradedOffer Version.SSL30 := by
  unfold serverAcceptsVersion attackerDowngradedOffer
  decide

/-- **The server cannot detect the modification.**  There exist two
different offer lists — the honest original and the attacker's
rewrite — that both lead the server to accept SSL 3.0.  This
witnesses the absence of negotiation-integrity protection. -/
theorem ssl3_no_negotiation_integrity :
    ∃ orig modified : List Version,
      orig ≠ modified ∧
      serverAcceptsVersion modified Version.SSL30 := by
  refine ⟨clientOriginalOffer, attackerDowngradedOffer, ?_, ?_⟩
  · decide
  · unfold serverAcceptsVersion attackerDowngradedOffer
    decide

/-- **Stronger**: for every honest client offer that does *not*
contain SSL 3.0, there is a modified offer the attacker can produce
which the server accepts as SSL 3.0.  The attacker therefore
unconditionally controls the negotiated version. -/
theorem ssl3_attacker_controls_version :
    ∀ orig : List Version, Version.SSL30 ∉ orig →
      ∃ modified : List Version,
        orig ≠ modified ∧
        serverAcceptsVersion modified Version.SSL30 := by
  intro orig _h
  refine ⟨[Version.SSL30], ?_, ?_⟩
  · intro hEq
    -- orig = [SSL30] would put SSL30 in orig, contradicting _h.
    rw [hEq] at _h
    exact _h (List.Mem.head _)
  · unfold serverAcceptsVersion
    decide

end SSL3

------------------------------------------------------------------
-- Part VIII.  WEP  —  IV-reuse keystream leakage
------------------------------------------------------------------

/-!
### WEP -- IV-reuse keystream leakage (explained)

**What it is.** The original 802.11 wireless encryption. Each packet is
encrypted as ciphertext = plaintext XOR keystream(K, IV), where the
keystream depends on the shared key K and a per-packet initialisation
vector IV.

**The flaw.** The IV is only 24 bits, so by the pigeonhole principle it
repeats after about 16 million packets. Whenever two packets share the same
(K, IV) they share the same keystream, and XORing their two ciphertexts
cancels the keystream entirely: c1 XOR c2 = p1 XOR p2. The attacker learns a
relationship between the two plaintexts with *no knowledge of the key* -- a
purely algebraic break.

**In this formalisation.** `keystream` and `encrypt` model the cipher;
`wep_iv_reuse_leaks_plaintext_xor` proves the identity
c1 XOR c2 = p1 XOR p2 directly, using the core `Nat.xor` lemmas
(commutativity, associativity, self-inverse). This is the algebraic heart
of every keystream-reuse attack on WEP.
-/
namespace WEP

/-- An abstract deterministic keystream function of the (key, IV)
pair.  The specific arithmetic is irrelevant to the vulnerability;
all that matters is that the *same* (K, IV) yields the *same* output. -/
def keystream (K IV : Nat) : Nat := K * 31 + IV

/-- WEP encryption: ciphertext = plaintext XOR keystream(K, IV). -/
def encrypt (K IV plaintext : Nat) : Nat :=
  plaintext ^^^ keystream K IV

/-- **The core structural flaw of WEP, proven as an algebraic
identity.**  Whenever two packets are encrypted under the *same*
(K, IV), the XOR of the two ciphertexts equals the XOR of the
plaintexts.  No knowledge of the key is required.

This is the relationship every keystream-reuse attack on WEP
ultimately exploits.  The 24-bit IV of WEP guarantees a collision
after ≈ 2²⁴ ≈ 16M packets by the pigeonhole principle, after which
the identity below directly leaks plaintext information. -/
theorem wep_iv_reuse_leaks_plaintext_xor (K IV p1 p2 : Nat) :
    (encrypt K IV p1) ^^^ (encrypt K IV p2) = p1 ^^^ p2 := by
  unfold encrypt
  -- Algebraic manipulation using core Nat-XOR lemmas:
  --   (p1 ⊕ ks) ⊕ (p2 ⊕ ks)
  -- = (p1 ⊕ ks) ⊕ (ks ⊕ p2)     (xor_comm on the inner pair)
  -- = ((p1 ⊕ ks) ⊕ ks) ⊕ p2     (re-associate)
  -- = (p1 ⊕ (ks ⊕ ks)) ⊕ p2     (re-associate)
  -- = (p1 ⊕ 0) ⊕ p2             (xor_self)
  -- = p1 ⊕ p2                   (xor_zero)
  rw [Nat.xor_comm p2 (keystream K IV)]
  rw [← Nat.xor_assoc (p1 ^^^ keystream K IV) (keystream K IV) p2]
  rw [Nat.xor_assoc p1 (keystream K IV) (keystream K IV)]
  rw [Nat.xor_self, Nat.xor_zero]

/-- **Concrete witness**: there exist two distinct plaintexts whose
ciphertexts under the same (K, IV) XOR to a non-trivial revealing
value, computable by an attacker observing only the two ciphertexts. -/
theorem wep_iv_reuse_witness :
    ∃ K IV p1 p2,
      p1 ≠ p2 ∧
      (encrypt K IV p1) ^^^ (encrypt K IV p2) = p1 ^^^ p2 := by
  refine ⟨0, 0, 0, 1, ?_, ?_⟩
  · decide
  · exact wep_iv_reuse_leaks_plaintext_xor 0 0 0 1

/-- **Two ciphertexts suffice for the leak.**  Given the two
WEP-encrypted packets observed by a passive attacker, the attacker
can compute the XOR of the plaintexts using only the ciphertexts ---
no key, no decryption oracle, no chosen-plaintext interaction. -/
theorem wep_passive_attack (K IV p1 p2 : Nat) :
    let c1 := encrypt K IV p1
    let c2 := encrypt K IV p2
    c1 ^^^ c2 = p1 ^^^ p2 :=
  wep_iv_reuse_leaks_plaintext_xor K IV p1 p2

end WEP


------------------------------------------------------------------
--  SECTION B.  Cipher-level / algebraic breaks (per-protocol models)
--  Seven protocols: SSL 2.0, Bluetooth Legacy, WPA-TKIP, PAP,
--  HTTP Basic Auth, EAP-MD5, PPTP-MSCHAPv2.  Each carries its own
--  small Message / Derivable, which shadows Section A locally.
------------------------------------------------------------------

/-! ## Part IX. SSL 2.0 -- Cipher-Suite Rollback

Wagner and Schneier (1996) showed that SSL 2.0's handshake does not
authenticate the negotiated cipher-suite list: the `FINISHED`
message covers only the master secret, not the offered ciphers.
A man-in-the-middle can therefore delete strong cipher options
from the client's offer, forcing the server to fall back to a
weak (e.g. 40-bit export-grade) suite that the attacker can later
break offline.

We model the negotiation as a function `negotiate` selecting the
first cipher in the client's offer list, and the attacker's
rewrite as a filter deleting all strong options. -/

/-!
### SSL 2.0 -- cipher-suite rollback (explained)

**Message idea.** The client offers a list of cipher suites; the server
selects one. A closing `FINISHED` handshake message is meant to detect
tampering -- but in SSL 2.0 it covers only the negotiated master secret,
*not* the offered cipher list.

**The flaw.** Because the cipher list is unauthenticated, a
man-in-the-middle deletes the strong ciphers from the client's offer,
leaving only a weak (e.g. 40-bit export-grade) option, which the server
then selects and neither endpoint detects. The attacker breaks the weak
cipher offline afterwards.

**In this formalisation.** `Cipher` is a two-element universe
(strong / weak); `negotiate` picks the first offered cipher;
`attacker_rewrite` filters out the strong ones; `rollback_attack` certifies
that the cipher negotiated with the attacker present differs from the honest
one -- i.e. the session was silently downgraded.
-/
namespace SSL_2_0

/-- Two-element cipher universe: an unbroken strong cipher and a
    weak export-grade cipher. -/
inductive Cipher where
  | strong
  | weak
  deriving DecidableEq

/-- The server picks the first mutually-supported cipher in the
    client's offer list. -/
def negotiate : List Cipher → Cipher
  | []     => Cipher.weak
  | c :: _ => c

/-- The client offers strong first, weak as fall-back. -/
def client_offer : List Cipher := [Cipher.strong, Cipher.weak]

/-- A weakness predicate, used to filter out strong options. -/
def isWeak : Cipher → Bool
  | Cipher.weak => true
  | _           => false

/-- Attacker rewrite: delete all strong ciphers from the offer.
    SSL 2.0's `FINISHED` does not cover the cipher list, so the
    rewrite is undetected by either endpoint. -/
def attacker_rewrite (cs : List Cipher) : List Cipher :=
  cs.filter isWeak

/-- Honest negotiation picks the strong cipher. -/
theorem honest_picks_strong :
    negotiate client_offer = Cipher.strong := rfl

/-- The rewrite leaves only the weak cipher. -/
theorem rewrite_leaves_only_weak :
    attacker_rewrite client_offer = [Cipher.weak] := rfl

/-- After the rewrite, negotiation picks the weak cipher. -/
theorem rollback_negotiated :
    negotiate (attacker_rewrite client_offer) = Cipher.weak := rfl

/-- **Cipher-suite rollback attack, certified.** The negotiated
    cipher with and without the attacker differ -- so the attacker
    has successfully downgraded the session. -/
theorem rollback_attack :
    negotiate client_offer
      ≠ negotiate (attacker_rewrite client_offer) := by
  decide

end SSL_2_0

/-! ## Part X. Bluetooth Legacy -- PIN Brute Force

Jakobsson and Wetzel (2001) demonstrated that the legacy
Bluetooth pairing protocol leaks the PIN to a passive observer.
The initial key `Kinit = E22(IN_RAND, BD_ADDR, PIN)` is derived
from inputs that are either public (`BD_ADDR`, `IN_RAND`) or low-
entropy (`PIN` is typically four decimal digits = 10^4 candidates).
The exchange of `LK_RAND` values is encrypted under `Kinit`; the
attacker enumerates PIN candidates, derives candidate `Kinit`
values, and tests decryption against the observed ciphertext.

We capture this break as a deduction rule `brute_pin` that
recovers the PIN given the public inputs and one ciphertext
encrypted under the derived `Kinit`. -/

/-!
### Bluetooth legacy pairing -- PIN brute force (explained)

**Message idea.** Two devices derive an initial key
K_init = E22(IN_RAND, BD_ADDR, PIN) and then exchange LK_RAND values
encrypted under K_init to build their long-term link key.

**The flaw.** The inputs to K_init are either public and observable
(the device address BD_ADDR and the random IN_RAND) or extremely
low-entropy (the PIN is typically four decimal digits -- 10^4 candidates).
A passive eavesdropper enumerates all PINs, derives the candidate K_init for
each, and tests it against the observed encrypted exchange until one
decrypts correctly -- recovering the PIN in well under a second.

**In this formalisation.** The `Message` type carries the public inputs and
the ciphertext; the `brute_pin` rule encodes the enumeration step (given the
public inputs and the ciphertext, the PIN is derivable); `pin_recoverable`
certifies recovery from a single observed pairing.
-/
namespace Bluetooth_Legacy

inductive Message where
  | bd_addr (a : Nat)
  | in_rand (r : Nat)
  | encrypted_lk_rand (pin a r lk : Nat)
  | pin (p : Nat)
  deriving DecidableEq

inductive Derivable : List Message → Message → Prop where
  /-- Any message on the network is derivable by the attacker. -/
  | seen : ∀ {ms m}, m ∈ ms → Derivable ms m
  /-- **PIN brute force.** Given the public inputs `BD_ADDR` and
      `IN_RAND` together with the `LK_RAND` ciphertext under
      `Kinit`, the attacker enumerates PIN candidates and
      recovers the correct PIN. This rule encodes the
      well-documented practical break of legacy Bluetooth
      pairing. -/
  | brute_pin :
      ∀ {ms} (pin a r lk : Nat),
        Derivable ms (Message.bd_addr a) →
        Derivable ms (Message.in_rand r) →
        Derivable ms (Message.encrypted_lk_rand pin a r lk) →
        Derivable ms (Message.pin pin)

/-- The passive observer's view of a pairing exchange. -/
def pairing_trace (pin a r lk : Nat) : List Message :=
  [ Message.bd_addr a,
    Message.in_rand r,
    Message.encrypted_lk_rand pin a r lk ]

/-- **PIN recovery, certified.** From a single observed pairing
    exchange the attacker recovers the PIN, breaking confidentiality
    of any subsequent session keyed from it. -/
theorem pin_recoverable (pin a r lk : Nat) :
    Derivable (pairing_trace pin a r lk) (Message.pin pin) := by
  apply Derivable.brute_pin pin a r lk
  · exact Derivable.seen (List.Mem.head _)
  · exact Derivable.seen (List.Mem.tail _ (List.Mem.head _))
  · exact Derivable.seen
            (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

end Bluetooth_Legacy

/-! ## Part XI. WPA-TKIP -- Beck-Tews Keystream Recovery

Beck and Tews (2009) showed that TKIP's per-packet keystream can
be recovered from a single short, predictable packet (typically
ARP). The attack proceeds in two stages: (i) a chopchop-style
byte-by-byte ICV brute-force against MIC failure reports reveals
the keystream for the packet's IV; (ii) the recovered keystream
allows forging up to seven new packets of arbitrary plaintext
under the same IV before the IV counter advances.

We model both stages with explicit deduction rules. -/

/-!
### WPA-TKIP -- the Beck-Tews attack (explained)

**Message idea.** TKIP wraps each packet with a keystream and a message
integrity check (MIC), reporting MIC failures back to the sender.

**The flaw (Beck-Tews 2009).** Using the MIC-failure reports as an oracle, a
"chopchop" attack recovers the keystream for a short, predictable packet
(typically ARP) one byte at a time. Once the keystream for an IV is known,
the attacker can forge several new packets of arbitrary content under that
same IV before the IV counter advances.

**In this formalisation.** The attack is modelled in its two stages:
the `chopchop` rule recovers the keystream from a known-plaintext packet and
its ciphertext, and the `forge` rule turns a known keystream into an
arbitrary forged packet. `beck_tews_forgery` composes them to certify that a
single observed ARP packet lets the attacker inject a forged one.
-/
namespace WPA_TKIP

inductive Message where
  | arp_plaintext (data : Nat)
  | tkip_ciphertext (iv data : Nat)
  | keystream (iv : Nat)
  | forged_packet (iv data : Nat)
  deriving DecidableEq

inductive Derivable : List Message → Message → Prop where
  | seen : ∀ {ms m}, m ∈ ms → Derivable ms m
  /-- **Chopchop keystream recovery.** Knowing the ARP
      plaintext and its TKIP ciphertext under IV, the attacker
      recovers the keystream for that IV through the
      byte-by-byte ICV attack. -/
  | chopchop :
      ∀ {ms} (iv data : Nat),
        Derivable ms (Message.arp_plaintext data) →
        Derivable ms (Message.tkip_ciphertext iv data) →
        Derivable ms (Message.keystream iv)
  /-- **Beck-Tews forgery.** With the keystream for an IV in
      hand, the attacker injects packets of arbitrary plaintext
      under the same IV. -/
  | forge :
      ∀ {ms} (iv data : Nat),
        Derivable ms (Message.keystream iv) →
        Derivable ms (Message.forged_packet iv data)

/-- Attacker observation: one ARP packet with known plaintext and
    its TKIP ciphertext. -/
def observed (iv plaintext : Nat) : List Message :=
  [ Message.arp_plaintext plaintext,
    Message.tkip_ciphertext iv plaintext ]

/-- **Beck-Tews forgery, certified.** From a single observed ARP
    packet the attacker injects an arbitrary forged packet under
    the same IV. -/
theorem beck_tews_forgery (iv plaintext malicious : Nat) :
    Derivable (observed iv plaintext)
              (Message.forged_packet iv malicious) := by
  apply Derivable.forge iv malicious
  apply Derivable.chopchop iv plaintext
  · exact Derivable.seen (List.Mem.head _)
  · exact Derivable.seen (List.Mem.tail _ (List.Mem.head _))

end WPA_TKIP

/-! ## Part XII. PAP -- Plaintext Credential Disclosure

The Password Authentication Protocol (RFC 1334) transmits the
username and password in cleartext over PPP. The protocol
provides no cryptographic protection at all: a passive observer
on the link reads the credentials directly. The shallow proof
is correspondingly trivial -- it is precisely the *absence* of
any cryptographic primitive that we wish to certify. -/

/-!
### PAP -- plaintext credential disclosure (explained)

**Message idea.** The PPP Password Authentication Protocol (RFC 1334) sends
the username and password across the link in the clear:
  A -> B :  username, password

**The flaw.** There is no cryptographic protection whatsoever, so a passive
observer on the link simply reads the credentials. The "proof" here is
therefore trivial by design -- its purpose is to certify the *absence* of
any protecting primitive, which is itself the vulnerability.

**In this formalisation.** The `Message` type has only `username` and
`password`; the only derivation rule is `seen` (anything on the wire is
known); `credentials_disclosed` certifies both fields are directly
observable.
-/
namespace PAP

inductive Message where
  | username (u : Nat)
  | password (p : Nat)
  deriving DecidableEq

inductive Derivable : List Message → Message → Prop where
  | seen : ∀ {ms m}, m ∈ ms → Derivable ms m

/-- The PAP exchange: both fields in cleartext. -/
def transmitted (u p : Nat) : List Message :=
  [ Message.username u, Message.password p ]

/-- **PAP credential disclosure, certified.** The username and the
    password are both directly observable to a passive attacker.
    There is no cryptographic primitive to break: the secret is
    transmitted in the clear. -/
theorem credentials_disclosed (u p : Nat) :
    Derivable (transmitted u p) (Message.username u)
    ∧ Derivable (transmitted u p) (Message.password p) := by
  refine ⟨?_, ?_⟩
  · exact Derivable.seen (List.Mem.head _)
  · exact Derivable.seen (List.Mem.tail _ (List.Mem.head _))

end PAP

/-! ## Part XIII. HTTP Basic Auth -- Base64 Disclosure

HTTP Basic Authentication (RFC 7617) transmits credentials as
`base64(username:password)`. Base64 is a *public encoding*, not
an encryption: any observer applies the inverse encoding to
recover the plaintext credentials. This is morally identical to
PAP, with one extra rule documenting that the encoding is
publicly invertible. -/

/-!
### HTTP Basic Authentication -- base64 disclosure (explained)

**Message idea.** The client sends base64(username:password) in an
Authorization header.

**The flaw.** Base64 is a public *encoding*, not encryption -- it has a
publicly known inverse. Anyone who observes the header (over an unencrypted
channel) decodes it back to the plaintext credentials. It is PAP with an
extra, reversible, obfuscation step that provides no security.

**In this formalisation.** `encode` models the (injective, public) encoding;
the `decode` rule encodes the fact that it is publicly invertible;
`credentials_recoverable` certifies the credentials are recovered from the
observed blob.
-/
namespace HTTP_Basic_Auth

/-- A public, publicly-invertible encoding (concretely base64).
    We model the encoding as an injective function on the
    natural numbers; only its publicly-invertible nature
    matters for the attack. -/
def encode (u p : Nat) : Nat := u * 1000000 + p

inductive Message where
  | base64_encoded (data : Nat)
  | credentials (u p : Nat)
  deriving DecidableEq

inductive Derivable : List Message → Message → Prop where
  | seen : ∀ {ms m}, m ∈ ms → Derivable ms m
  /-- **Base64 is publicly invertible.** Anyone seeing the
      encoded blob recovers the plaintext credentials by
      applying the inverse encoding. -/
  | decode :
      ∀ {ms} (u p : Nat),
        Derivable ms (Message.base64_encoded (encode u p)) →
        Derivable ms (Message.credentials u p)

def observed (u p : Nat) : List Message :=
  [ Message.base64_encoded (encode u p) ]

/-- **HTTP Basic Auth credential recovery, certified.** A passive
    observer on an unencrypted channel recovers the credentials
    by applying the base64 inverse. -/
theorem credentials_recoverable (u p : Nat) :
    Derivable (observed u p) (Message.credentials u p) := by
  apply Derivable.decode
  exact Derivable.seen (List.Mem.head _)

end HTTP_Basic_Auth

/-! ## Part XIV. EAP-MD5 -- Offline Dictionary Attack

EAP-MD5 (RFC 3748) is a challenge-response authentication where
the client returns `MD5(identifier || password || challenge)`.
A passive observer captures the challenge and the response.
Because MD5 is a *public* function, the attacker computes
`MD5(identifier || candidate || challenge)` for each entry of
a password dictionary and checks for a match.

We capture the dictionary attack as a deduction rule `dict_attack`
that recovers the password when the attacker observes the
challenge-response pair and the candidate is in their dictionary.
-/

/-!
### EAP-MD5 -- offline dictionary attack (explained)

**Message flow.**
  1.  B -> A :  challenge
  2.  A -> B :  MD5(identifier || password || challenge)
B checks the hash to authenticate A.

**The flaw.** MD5 is a public function and the response is computed from the
observed challenge and the (secret but often weak) password. A passive
eavesdropper who captures the challenge-response pair simply tries each
password in a dictionary, hashing it with the challenge until the result
matches -- recovering the password offline with no interaction.

**In this formalisation.** `md5` models the public hash; `dictionary` is the
attacker's wordlist; the `dict_attack` rule encodes the enumeration
(given the challenge, the response, and a candidate in the dictionary, the
password is derivable); `dictionary_recovery` certifies recovery from one
observed exchange.
-/
namespace EAP_MD5

/-- MD5 modelled abstractly as a public deterministic function.
    Only its public-function nature is used in the proof. -/
def md5 (challenge password : Nat) : Nat :=
  challenge * 7919 + password * 104729

/-- The attacker's password dictionary. Concretely a wordlist
    such as `rockyou.txt`; here a small concrete list so we
    can prove a specific recovery. -/
def dictionary : List Nat := [12345, 67890, 11111, 22222, 99999]

inductive Message where
  | challenge (c : Nat)
  | response (r : Nat)
  | password (p : Nat)
  deriving DecidableEq

inductive Derivable : List Message → Message → Prop where
  | seen : ∀ {ms m}, m ∈ ms → Derivable ms m
  /-- **Offline dictionary attack.** Given the observed
      challenge and the response `MD5(c || p)`, the attacker
      enumerates the dictionary and recovers the password
      whenever it lies in the wordlist. -/
  | dict_attack :
      ∀ {ms} (c p : Nat),
        p ∈ dictionary →
        Derivable ms (Message.challenge c) →
        Derivable ms (Message.response (md5 c p)) →
        Derivable ms (Message.password p)

/-- Attacker observation: one challenge-response pair. -/
def observed (c p : Nat) : List Message :=
  [ Message.challenge c, Message.response (md5 c p) ]

/-- **Dictionary recovery, certified.** When the user's password
    lies in the attacker's dictionary, a single observed
    challenge-response pair suffices to recover it. -/
theorem dictionary_recovery
    (c p : Nat) (hp : p ∈ dictionary) :
    Derivable (observed c p) (Message.password p) := by
  apply Derivable.dict_attack c p hp
  · exact Derivable.seen (List.Mem.head _)
  · exact Derivable.seen (List.Mem.tail _ (List.Mem.head _))

/-- Concrete instance: the dictionary member `12345`. -/
theorem dictionary_recovery_concrete (c : Nat) :
    Derivable (observed c 12345) (Message.password 12345) := by
  apply dictionary_recovery c 12345
  decide

end EAP_MD5

/-! ## Part XV. PPTP-MSCHAPv2 -- DES Key-Space Split

Schneier and Mudge (1999) analysed Microsoft's PPTP MSCHAPv2.
The protocol uses the user's NT hash (16 bytes) split into three
DES keys, each encrypting the same 8-byte challenge:

  K_1 = NT-hash[ 0.. 7]  (7 bytes, 56-bit DES key)
  K_2 = NT-hash[ 7..14]  (7 bytes, 56-bit DES key)
  K_3 = NT-hash[14..16] + 5 zero bytes  (only 2 unknown bytes
                                          -- 2^16 search space)

The attacker observes the challenge and the three resulting
ciphertexts. The third block has only 16 bits of entropy and is
trivially brute-forced (one CPU-second on commodity hardware);
the recovered bytes are then used as a constraint to crack the
remaining 14 bytes of NT hash (DES-MD4 rainbow tables make this
hours rather than years).

We certify the first stage of the attack as a deduction rule
`brute_block3` that recovers the third hash block. -/

/-!
### PPTP MSCHAPv2 -- DES key-space split (explained)

**Message idea.** The client's 16-byte NT password hash is split into three
DES keys, each of which encrypts the *same* server challenge; the three
ciphertexts form the response.

**The flaw (Schneier-Mudge 1999).** The split is uneven. The third DES key
is only the last two bytes of the hash padded with five zero bytes -- just
16 bits of unknown entropy. An attacker who observes the challenge and the
third ciphertext brute-forces those 2^16 possibilities in constant time,
recovering the last two hash bytes; those then constrain and accelerate
cracking the remaining fourteen bytes (turning years into hours with
precomputed tables).

**In this formalisation.** `NT_Hash` is the three-block split and `des` the
(public, deterministic) cipher; the `brute_block3` rule encodes the 16-bit
brute-force of the third block; `block3_recovery` certifies the third block
is recovered from a single observed MSCHAPv2 exchange.
-/
namespace PPTP_MSCHAPv2

/-- The NT hash split into three blocks of (effective) entropy
    7+7+2 bytes. -/
structure NT_Hash where
  block1 : Nat   -- 56 bits
  block2 : Nat   -- 56 bits
  block3 : Nat   -- 16 effective bits (5 trailing zero bytes)
  deriving DecidableEq

/-- DES modelled abstractly as a public deterministic function.
    Only its public, deterministic nature is used in the proof. -/
def des (key challenge : Nat) : Nat :=
  key * 1009 + challenge * 65537

inductive Message where
  | challenge (c : Nat)
  | ciphertext_1 (ct : Nat)
  | ciphertext_2 (ct : Nat)
  | ciphertext_3 (ct : Nat)
  | hash_block (idx b : Nat)   -- (idx, value) tag
  deriving DecidableEq

inductive Derivable : List Message → Message → Prop where
  | seen : ∀ {ms m}, m ∈ ms → Derivable ms m
  /-- **Block-3 brute force.** The third DES key has only 16
      bits of effective entropy. Given the observed challenge
      and the ciphertext of the third block, the attacker
      enumerates the 2^16 candidates and recovers the third
      block in constant time. -/
  | brute_block3 :
      ∀ {ms} (c b3 : Nat),
        Derivable ms (Message.challenge c) →
        Derivable ms (Message.ciphertext_3 (des b3 c)) →
        Derivable ms (Message.hash_block 3 b3)

/-- Attacker observation: the challenge plus the three
    ciphertext blocks of MSCHAPv2's `NT-response`. -/
def observed (c : Nat) (h : NT_Hash) : List Message :=
  [ Message.challenge c,
    Message.ciphertext_1 (des h.block1 c),
    Message.ciphertext_2 (des h.block2 c),
    Message.ciphertext_3 (des h.block3 c) ]

/-- **Block-3 recovery, certified.** The third 16-bit block of
    the NT hash is trivially recoverable from one observed
    MSCHAPv2 exchange. -/
theorem block3_recovery (c : Nat) (h : NT_Hash) :
    Derivable (observed c h) (Message.hash_block 3 h.block3) := by
  apply Derivable.brute_block3 c h.block3
  · exact Derivable.seen (List.Mem.head _)
  · exact Derivable.seen
            (List.Mem.tail _ (List.Mem.tail _
              (List.Mem.tail _ (List.Mem.head _))))

end PPTP_MSCHAPv2


/-! ## Summary -- thirteen protocols

Section A (session-level Dolev-Yao, shared message algebra):
  Part III   NS-PK       `NS_PK.ns_pk_mitm_attack`, `NS_PK.intruder_learns_Nb`
  Part IV    NS-Lowe     `NS_Lowe.ns_lowe_blocks_old_attack` (safety contrast)
  Part V     NS-Sym      `NS_Sym.ns_sym_concrete_attack`
  Part VI    DH-basic    `DH_Basic.dh_basic_mitm_attack`
  Part VII   SSL 3.0     `SSL3.ssl3_downgrade_attack`
  Part VIII  WEP         `WEP.wep_iv_reuse_leaks_plaintext_xor`

Section B (cipher-level / algebraic breaks, per-protocol models):
  Part IX    SSL 2.0            `SSL_2_0.rollback_attack`
  Part X     Bluetooth Legacy   `Bluetooth_Legacy.pin_recoverable`
  Part XI    WPA-TKIP           `WPA_TKIP.beck_tews_forgery`
  Part XII   PAP                `PAP.credentials_disclosed`
  Part XIII  HTTP Basic Auth    `HTTP_Basic_Auth.credentials_recoverable`
  Part XIV   EAP-MD5            `EAP_MD5.dictionary_recovery`
  Part XV    PPTP-MSCHAPv2      `PPTP_MSCHAPv2.block3_recovery`

Thirteen distinct protocols at the shallow Dolev-Yao layer. The deeper
Paulson-style inductive proofs -- for five of these (NS-PK, NS-Sym,
NS-Lowe, SSL 3.0) plus Woo-Lam -- live in `ProtocolsPaulson.lean`.
-/
