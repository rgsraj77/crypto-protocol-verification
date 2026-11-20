/-!
# SafeProtocols.lean -- Certified Safety Results

Where the attack files certify that a vulnerability *exists*, this file
certifies that a class of attack is *absent*. Each result proves a protocol
(or scheme) **safe against one specific, named attack class**, in a different
proof style:

  Part I.   Needham-Schroeder-Lowe -- safe vs the Lowe MITM substitution
            (structural: the corrected message has a shape the attack cannot
            forge).  Copied from `ProtocolsDolevYao.lean`.
  Part II.  One-Time Pad -- perfect secrecy vs ciphertext-only plaintext
            recovery (algebraic).  The safe dual of the WEP keystream-reuse
            attack: WEP breaks *because* it reuses the pad; a single-use pad
            is perfectly secret.
  Part III. Fresh-nonce challenge-response -- safe vs replay (structural
            freshness).  The safe dual of the NS-Sym Denning-Sacco replay:
            a stale, replayed response fails the responder's freshness check.

**Scope, stated honestly.** Every theorem here certifies the *absence of a
named attack*, not unconditional security. Full inductive safety against every
Dolev-Yao strategy over unbounded sessions is a much larger proof (on the scale
of Paulson's original development) and is left as future work. What these
results show is that the same framework used to exhibit attacks can also
*rule specific attacks out*, in more than one style of argument.

The file is self-contained: it imports nothing beyond the Lean 4 core library.

Author     : Raj Guru Suwalka
Supervisor : Dr. Edon Kelmendi
MSc Project, Queen Mary University of London, 2025-26
-/

------------------------------------------------------------------
-- Shared framework (only what Part I needs)
------------------------------------------------------------------

inductive Agent where
  | A | B | I | S
deriving DecidableEq, Repr

inductive Message where
  | nonce      : Nat   → Message
  | timestamp  : Nat   → Message
  | key        : Nat   → Message
  | agent      : Agent → Message
  | pair       : Message → Message → Message
  | encrypt    : Agent → Message → Message
  | encryptSym : Nat   → Message → Message
deriving DecidableEq, Repr

------------------------------------------------------------------
-- Part I.  Needham-Schroeder-Lowe  --  safe vs Lowe's MITM (structural)
------------------------------------------------------------------

namespace NS_Lowe

/-- Lowe's corrected step 2: the responder's identity is bound *inside* the
    encryption. -/
def msg2_lowe (init resp : Agent) (Na Nb : Nat) : Message :=
  Message.encrypt init
    (Message.pair
      (Message.pair (Message.nonce Na) (Message.nonce Nb))
      (Message.agent resp))

/-- The original (broken) step 2, repeated so the two can be compared. -/
def msg2_old (init : Agent) (Na Nb : Nat) : Message :=
  Message.encrypt init
    (Message.pair (Message.nonce Na) (Message.nonce Nb))

/-- A's strengthened acceptance: A only accepts a step-2 message of the
    corrected shape (with B's identity in the expected position). -/
def StrongAcceptance (m : Message) : Prop :=
  ∃ Na Nb, m = msg2_lowe Agent.A Agent.B Na Nb

/-- **Structural distinctness.**  For every choice of nonces, the original
    message and the corrected one have different term shapes and so cannot be
    equal as Lean values. -/
theorem msg2_shape_distinct (Na Nb Na' Nb' : Nat) :
    msg2_old Agent.A Na Nb ≠ msg2_lowe Agent.A Agent.B Na' Nb' := by
  intro h
  simp [msg2_old, msg2_lowe] at h

/-- **Safety vs the Lowe attack.**  Whatever nonces the intruder inserts into
    the old-style message, A's strengthened acceptance check rejects it -- so
    the original man-in-the-middle substitution can no longer be accepted. -/
theorem ns_lowe_blocks_old_attack :
    ∀ Na Nb, ¬ StrongAcceptance (msg2_old Agent.A Na Nb) := by
  intro Na Nb h
  rcases h with ⟨Na', Nb', hEq⟩
  exact msg2_shape_distinct Na Nb Na' Nb' hEq

end NS_Lowe

------------------------------------------------------------------
-- Part II.  One-Time Pad  --  perfect secrecy (algebraic)
------------------------------------------------------------------

namespace OneTimePad

/-- One-time-pad encryption: ciphertext = plaintext XOR key. -/
def encrypt (key plaintext : Nat) : Nat := plaintext ^^^ key

/-- **Perfect secrecy (Shannon), symbolically.**  For every ciphertext `c` and
    every candidate plaintext `p`, there is a key that produces `c` from `p`
    (namely `p ⊕ c`).  So observing the ciphertext rules out no plaintext:
    every plaintext is equally consistent with what the attacker sees. This is
    the exact opposite of WEP, which leaks a plaintext relationship the moment
    a keystream is reused. -/
theorem perfect_secrecy (c p : Nat) : ∃ key, encrypt key p = c := by
  refine ⟨p ^^^ c, ?_⟩
  unfold encrypt
  -- p ^^^ (p ^^^ c) = (p ^^^ p) ^^^ c = 0 ^^^ c = c
  rw [← Nat.xor_assoc, Nat.xor_self, Nat.xor_comm, Nat.xor_zero]

/-- **Indistinguishability.**  The *same* ciphertext is consistent with two
    *different* plaintexts, each under its own key -- so the attacker cannot
    use the ciphertext to tell `p1` from `p2`. -/
theorem indistinguishable (c p1 p2 : Nat) :
    (∃ k1, encrypt k1 p1 = c) ∧ (∃ k2, encrypt k2 p2 = c) :=
  ⟨perfect_secrecy c p1, perfect_secrecy c p2⟩

end OneTimePad

------------------------------------------------------------------
-- Part III.  Fresh-nonce challenge-response  --  safe vs replay
------------------------------------------------------------------

namespace FreshChallenge

/-- The responder issues a fresh challenge nonce each run and accepts a
    response only if the echoed nonce equals that fresh challenge. -/
def accepts (freshChallenge echoed : Nat) : Prop :=
  echoed = freshChallenge

/-- **Non-triviality (liveness).**  A genuine response that echoes the current
    challenge is accepted -- the freshness check does not reject everything. -/
theorem genuine_response_accepted (challenge : Nat) :
    accepts challenge challenge := rfl

/-- **Safety vs replay.**  A response replayed from a previous run echoes that
    run's (now stale) challenge `old`.  Because the responder issues a *fresh*
    challenge each run, the current challenge differs from `old`, and the
    replay is rejected. -/
theorem replay_rejected (current old : Nat) (fresh : current ≠ old)
    (echoed : Nat) (isReplay : echoed = old) :
    ¬ accepts current echoed := by
  intro h                         -- h : echoed = current
  exact fresh (h.symm.trans isReplay)

/-- **Contrast: without a freshness check, the replay succeeds.**  A responder
    that accepts any well-formed response -- the Denning-Sacco / NS-Sym flaw --
    accepts the replayed ticket unconditionally. -/
def acceptsNoFreshness (_echoed : Nat) : Prop := True

theorem replay_succeeds_without_freshness (echoed : Nat) :
    acceptsNoFreshness echoed := trivial

end FreshChallenge

/-! ## Summary

Three certified safety results, each ruling out a *named* attack class in a
different proof style:

| Protocol / scheme            | Safe against            | Theorem                                   | Style       |
|------------------------------|-------------------------|-------------------------------------------|-------------|
| Needham-Schroeder-Lowe       | Lowe MITM substitution  | `NS_Lowe.ns_lowe_blocks_old_attack`       | structural  |
| One-Time Pad                 | ciphertext-only recovery| `OneTimePad.perfect_secrecy`              | algebraic   |
| Fresh-nonce challenge-resp.  | replay                  | `FreshChallenge.replay_rejected`          | structural  |

Each is a *targeted* safety result (safe against the stated attack), not a
claim of unconditional security.  Full inductive safety over unbounded sessions
remains future work.  Together with the attack witnesses in the other files,
these show the framework can certify both the presence and the absence of
attacks.
-/
