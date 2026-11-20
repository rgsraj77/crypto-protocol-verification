/-!
# ChallengeResponseSafety.lean -- a full inductive safety proof

A *proof of method*: a genuine Paulson-style inductive safety proof over
**unbounded sessions** for a minimal nonce challenge-response protocol.  Unlike
the structural / algebraic safety results in `SafeProtocols.lean` (which reason
about a single message or a bounded scenario), this file defines a `Reachable`
predicate over arbitrarily long event traces and proves a safety *invariant*
that holds for **every** reachable trace, by induction on the derivation of
reachability.  This is the technique that would scale to Needham-Schroeder-Lowe;
here it is exercised on the smallest protocol that genuinely needs it.

## The protocol (abstracted)

A minimal challenge-response for freshness / anti-replay, of the kind underlying
CHAP (RFC 1994) and the ISO/IEC 9798 entity-authentication protocols:

  * the responder generates a **fresh** nonce and issues it as a challenge;
  * a response echoes a nonce back;
  * the responder **accepts** a response only if the echoed nonce is one it
    issued (a pending challenge) and has **not already accepted**.

## The Dolev-Yao adversary

The `accept` rule places **no constraint on who produced the echo**.  This is
exactly the Dolev-Yao model: the adversary controls all message delivery and may
replay any nonce it has seen.  Safety therefore does not rely on trusting the
sender -- it relies only on the responder's guard (issued, and not yet accepted).
There is consequently no separate `fake`/Spy rule: the adversary's full power is
already subsumed, because acceptance is guarded regardless of the echo's origin.

## What is proved

  * `accept_requires_issue` -- recentness: every accepted nonce was issued
    earlier in the trace (the responder never accepts a challenge it did not
    make).
  * `no_replay` -- replay-freedom: in any reachable trace, no nonce is accepted
    twice (each challenge is consumed once).

## Scope, stated honestly

This is full inductive safety *for the replay / recentness property* of this
minimal protocol -- not a claim of unconditional security, and not a
verification of a named standardised protocol.  Scaling the same `Reachable` +
invariant technique to Needham-Schroeder-Lowe, and handling Diffie-Hellman
protocols (which need equational reasoning better suited to Tamarin), remain
future work.

The file imports nothing beyond the Lean 4 core library.

Author     : Raj Guru Suwalka
Supervisor : Dr. Edon Kelmendi
MSc Project, Queen Mary University of London, 2025-26
-/

------------------------------------------------------------------
-- Events and traces
------------------------------------------------------------------

/-- A protocol event: the responder issues a fresh challenge nonce, or accepts
    a response echoing a nonce. -/
inductive Event where
  | issue  (n : Nat)
  | accept (n : Nat)
deriving DecidableEq, Repr

/-- A trace is a list of events; the head is the most-recent event. -/
abbrev Trace := List Event

/-- The nonces mentioned anywhere in a trace (issued or accepted). -/
def nonces : Trace → List Nat
  | []                    => []
  | Event.issue  n :: t   => n :: nonces t
  | Event.accept n :: t   => n :: nonces t

/-- The nonces the responder has *accepted* in a trace. -/
def accepted : Trace → List Nat
  | []                    => []
  | Event.accept n :: t   => n :: accepted t
  | Event.issue  _ :: t   => accepted t

/-- A self-contained "no duplicates" predicate (core-only, no Mathlib). -/
def Distinct : List Nat → Prop
  | []      => True
  | x :: xs => x ∉ xs ∧ Distinct xs

------------------------------------------------------------------
-- Reachable traces  (the inductive protocol semantics)
------------------------------------------------------------------

/-- `Reachable tr` holds when `tr` is a legal trace of the protocol under a
    Dolev-Yao adversary.  Two honest rules; the adversary is implicit (it
    controls delivery but cannot bypass the responder's `accept` guard). -/
inductive Reachable : Trace → Prop where
  | nil : Reachable []
  /-- The responder issues a *fresh* nonce (one that has never appeared). -/
  | issue :
      ∀ {t : Trace} {n : Nat},
        Reachable t → n ∉ nonces t →
          Reachable (Event.issue n :: t)
  /-- The responder accepts an echo of `n` only if `n` was issued and has not
      already been accepted (each challenge is consumed at most once). -/
  | accept :
      ∀ {t : Trace} {n : Nat},
        Reachable t → Event.issue n ∈ t → Event.accept n ∉ t →
          Reachable (Event.accept n :: t)

------------------------------------------------------------------
-- A legitimate run is reachable (the model is not vacuous)
------------------------------------------------------------------

/-- Issue nonce 1, then accept its echo -- a normal, non-replay run. -/
example : Reachable [Event.accept 1, Event.issue 1] := by
  apply Reachable.accept
  · apply Reachable.issue
    · exact Reachable.nil
    · simp [nonces]
  · simp
  · simp

------------------------------------------------------------------
-- Supporting lemma: the `accepted` projection tracks accept events
------------------------------------------------------------------

/-- A nonce is in `accepted t` iff there is a matching `accept` event in `t`. -/
theorem mem_accepted_iff (n : Nat) (t : Trace) :
    n ∈ accepted t ↔ Event.accept n ∈ t := by
  induction t with
  | nil => simp [accepted]
  | cons e rest ih =>
      cases e with
      | issue m  => simp [accepted, List.mem_cons, ih]
      | accept m => simp [accepted, List.mem_cons, ih]

------------------------------------------------------------------
-- Safety theorem 1 -- recentness
------------------------------------------------------------------

/-- **Recentness.**  In every reachable trace, any accepted nonce was issued
    earlier: the responder never accepts a challenge it did not make. -/
theorem accept_requires_issue {t : Trace} (h : Reachable t) :
    ∀ n, Event.accept n ∈ t → Event.issue n ∈ t := by
  induction h with
  | nil =>
      intro n hn
      simp at hn
  | @issue t m ht hfresh ih =>
      intro n hn
      rcases List.mem_cons.mp hn with h1 | h2
      · exact absurd h1 (by simp)
      · exact List.mem_cons.mpr (Or.inr (ih n h2))
  | @accept t m ht hissued hnotacc ih =>
      intro n hn
      rcases List.mem_cons.mp hn with h1 | h2
      · have hnm : n = m := by injection h1
        subst hnm
        exact List.mem_cons.mpr (Or.inr hissued)
      · exact List.mem_cons.mpr (Or.inr (ih n h2))

------------------------------------------------------------------
-- Safety theorem 2 -- replay-freedom
------------------------------------------------------------------

/-- **Replay-freedom.**  In every reachable trace, no nonce is accepted twice:
    the accepted nonces are all distinct.  A replayed challenge (already
    consumed) can never be accepted again. -/
theorem no_replay {t : Trace} (h : Reachable t) : Distinct (accepted t) := by
  induction h with
  | nil => simp [accepted, Distinct]
  | @issue t m ht hfresh ih =>
      -- `accepted (issue m :: t) = accepted t`
      simpa [accepted] using ih
  | @accept t m ht hissued hnotacc ih =>
      -- `accepted (accept m :: t) = m :: accepted t`
      simp only [accepted]
      refine ⟨?_, ih⟩
      -- need `m ∉ accepted t`; by `mem_accepted_iff` this is `accept m ∉ t`
      intro hc
      exact hnotacc ((mem_accepted_iff m t).mp hc)

/-! ## Summary

For the minimal nonce challenge-response protocol, under a Dolev-Yao adversary
that controls all message delivery, we prove -- by induction over the
`Reachable` predicate, i.e. over unbounded sessions:

  * `accept_requires_issue` : every accepted nonce was previously issued
    (recentness);
  * `no_replay`            : no nonce is ever accepted twice (replay-freedom).

This is a *proof of method*: the same `Reachable` + inductive-invariant
technique scales, with more lemmas, to Needham-Schroeder-Lowe.  It is full
inductive safety for the stated property, not unconditional security.
-/
