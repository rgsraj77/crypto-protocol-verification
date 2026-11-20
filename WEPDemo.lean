/-!
# WEPDemo.lean -- WEP keystream-reuse leak (standalone demonstration extract)

A self-contained extract of the WEP proof used as the live demonstration in
the project presentation.  The definitions and theorems below are **identical**
to Part VIII of `ProtocolsDolevYao.lean`; they are reproduced here as a single
short file so the whole argument -- cipher model, theorem, machine-checked
proof -- fits on one screen and can be read, compiled, and broken in front of
an audience without scrolling through the full consolidated artefact.

Nothing in this file is a new result.  It exists for presentation and for a
reader who wants the smallest possible complete example of what this project
means by "machine-checked".

## The protocol

WEP (Wired Equivalent Privacy, 1997) was the original 802.11 wireless
encryption scheme.  Each packet is encrypted as

    ciphertext = plaintext XOR keystream(K, IV)

where K is the long-term shared key and IV is a per-packet initialisation
vector sent in the clear.

## The flaw

The IV is only 24 bits wide, so by the pigeonhole principle it must repeat
after at most 2^24 (about 16 million) packets.  Two packets sent under the
same (K, IV) share the same keystream, and XORing their ciphertexts cancels
that keystream completely:

    c1 XOR c2 = (p1 XOR ks) XOR (p2 XOR ks) = p1 XOR p2

The attacker learns a relationship between two secret plaintexts with no
knowledge of the key, no decryption, and no interaction -- a purely passive,
purely algebraic break.

The file is self-contained: it imports nothing beyond the Lean 4 core library.

Author     : Raj Guru Suwalka
Supervisor : Dr. Edon Kelmendi
MSc Project, Queen Mary University of London, 2025-26
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
after about 2^24 = 16M packets by the pigeonhole principle, after
which the identity below directly leaks plaintext information.

Note the quantifiers: this holds for *every* key, *every* IV, and
*every* pair of plaintexts.  It is not a statement about one example
run -- it is a guarantee that the leak always happens. -/
theorem wep_iv_reuse_leaks_plaintext_xor (K IV p1 p2 : Nat) :
    (encrypt K IV p1) ^^^ (encrypt K IV p2) = p1 ^^^ p2 := by
  unfold encrypt
  -- Algebraic manipulation using core Nat-XOR lemmas.  Each line below
  -- rewrites the LEFT-hand side only; when it finally reads the same as
  -- the right-hand side, Lean closes the goal by reflexivity.
  --   (p1 ⊕ ks) ⊕ (p2 ⊕ ks)
  -- = (p1 ⊕ ks) ⊕ (ks ⊕ p2)     (xor_comm on the inner pair)
  -- = ((p1 ⊕ ks) ⊕ ks) ⊕ p2     (re-associate)
  -- = (p1 ⊕ (ks ⊕ ks)) ⊕ p2     (re-associate)
  -- = (p1 ⊕ 0) ⊕ p2             (xor_self:  ks ⊕ ks = 0)
  -- = p1 ⊕ p2                   (xor_zero:  p1 ⊕ 0 = p1)
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

/-!
## Demonstration notes (presentation)

The file above compiles clean.  The clearest way to show on camera what
"machine-checked" means is to make the *claim* false and watch Lean refuse
it.  A false statement is unprovable no matter what tactics follow, so it is
guaranteed to fail.

**Break (recommended) -- a false claim, edited inline.**
On the statement of `wep_iv_reuse_leaks_plaintext_xor` (its second line),
delete the `^^^ p2` at the end so it reads:

    (encrypt K IV p1) ^^^ (encrypt K IV p2) = p1 := by

The claim now says the two ciphertexts XOR to `p1` alone, which is false.
Lean immediately reports `unsolved goals` -- it cannot prove a statement that
is not true.  Press undo to restore.

**Break (alternative) -- the false claim as a separate theorem.**
If you would rather not touch the main theorem, uncomment the
`wep_false_claim` block below instead; it states the same false claim and
Lean rejects it in the same way.  Re-comment it to restore.

This is the point worth making: a test suite can only fail to find
a counterexample, whereas the proof assistant refuses to accept an argument
that does not hold.
-/

-- theorem wep_false_claim (K IV p1 p2 : Nat) :
--     (WEP.encrypt K IV p1) ^^^ (WEP.encrypt K IV p2) = p1 := by
--   unfold WEP.encrypt
--   rw [Nat.xor_comm p2 (WEP.keystream K IV)]
--   rw [← Nat.xor_assoc (p1 ^^^ WEP.keystream K IV) (WEP.keystream K IV) p2]
--   rw [Nat.xor_assoc p1 (WEP.keystream K IV) (WEP.keystream K IV)]
--   rw [Nat.xor_self, Nat.xor_zero]
