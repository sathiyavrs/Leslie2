/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sathiya / Claude
-/

import Leslie2Protocols.ABA.Gather.Ideal
import Leslie2Protocols.ABA.Broadcast.Impl

/-!
# The gather implementation over Bracha's broadcast

The gather aggregation ladder with its reliable-broadcast sub-protocol at
the implementation level: each process's input and each process's `BIND`
payload travel through a Bracha instance (`ABA/Broadcast/Impl.lean`), one per
process and level.

Delivery is derived, not stored (deviation D28): "`j` holds the pair `(k, v)`" is the
predicate `apIn` — an `n − f` `VOTE v` receipt quorum in `k`'s input-BRB
instance at receiver `j` — and likewise `apBind` for the bind payloads. The
approval guards of the gather rows read these predicates at the receiver;
no delivery event or return flag of the broadcast sub-protocol appears.
The broadcast calls are fused as in the tier above: the gather call
broadcasts the input, the `BIND` row broadcasts the payload.
-/

namespace PLTS
namespace ABA
namespace Gather

/-- The state of one gather-over-Bracha instance: the gather boxes and
fabric, the `n` input-BRB implementation instances, and the `n` bind-BRB
implementation instances. -/
structure LowState (n : ℕ) (X : Type) : Type where
  /-- The gather processes' boxes and the instance's message fabric. -/
  ga : SubState n (PRec n X) (GaMsg n X)
  /-- `brbIn k` — the Bracha instance broadcasting `k`'s input. -/
  brbIn : ∀ _ : Fin n, BRB.ImplState n X
  /-- `brbBind k` — the Bracha instance broadcasting `k`'s `BIND` payload. -/
  brbBind : ∀ _ : Fin n, BRB.ImplState n (APSet n X)

namespace LowState

variable {n : ℕ} {X : Type}

/-- The initial instance state. -/
def initial (n : ℕ) (X : Type) : LowState n X where
  ga := SubState.initial n (GaMsg n X) (PRec.initial n X)
  brbIn := fun _ => BRB.ImplState.initial n X
  brbBind := fun _ => BRB.ImplState.initial n (APSet n X)

/-- Corruption (deviation D1): the broadcast transform, corrupting the gather
fabric and every Bracha coordinate in lockstep. -/
def corruptAll (P : Params) (id : Fin P.n) (s : LowState P.n X) : LowState P.n X where
  ga := s.ga.corrupt P id
  brbIn := fun k => (s.brbIn k).corrupt P id
  brbBind := fun k => (s.brbBind k).corrupt P id

end LowState

section Rules

variable {X : Type} [DecidableEq X] {P : Params}

/-- `j` holds the pair `(k, v)`: an `n − f` `VOTE v` receipt quorum in `k`'s
input-BRB instance at receiver `j`. Monotone — receipts only accumulate. -/
def apIn (P : Params) (s : LowState P.n X) (j k : Fin P.n) (v : X) : Prop :=
  P.n - P.f ≤ (s.brbIn k).recvCount j (BRB.BMsg.vote v)

/-- `j` holds `q`'s bind payload `U`. -/
def apBind (P : Params) (s : LowState P.n X) (j q : Fin P.n) (U : APSet P.n X) : Prop :=
  P.n - P.f ≤ (s.brbBind q).recvCount j (BRB.BMsg.vote U)

/-- A payload set is approved at `j` when `j` holds every pair. -/
def approvedAt (P : Params) (s : LowState P.n X) (j : Fin P.n)
    (A : APSet P.n X) : Prop :=
  ∀ p ∈ A, apIn P s j p.1 p.2

/-- The step relation of the gather-over-Bracha instance. All transitions are
Dirac; the Bracha coordinates move by their own implementation rows, embedded
as internal transitions. -/
inductive LowStep (P : Params) :
    LowState P.n X → Lab P.n X → PMF (LowState P.n X) → Prop
  /-- The environment call arrives: record the payload and broadcast it
  through the process's input-BRB instance (the fused call). -/
  | call (s : LowState P.n X) (id : Fin P.n) (x : X)
      (h : (s.ga.proc id).input = none)
      (hb : ((s.brbIn id).proc id).input = none) :
      LowStep P s (.call id x)
        (PMF.pure
        { s with
          ga := s.ga.setProc id { s.ga.proc id with input := some x }
          brbIn := Function.update s.brbIn id
            (((s.brbIn id).setProc id
              { (s.brbIn id).proc id with input := some x }).mcast id (.init x)) })
  /-- Input-enabledness loop for `call`. -/
  | callLoop (s : LowState P.n X) (id : Fin P.n) (x : X) :
      LowStep P s (.call id x) (PMF.pure s)
  /-- An internal step of one input-BRB instance. -/
  | brbInTau (s : LowState P.n X) (k : Fin P.n) (b' : BRB.ImplState P.n X)
      (h : BRB.ImplStep P k (s.brbIn k) BRB.Lab.tau (PMF.pure b')) :
      LowStep P s .tau (PMF.pure { s with brbIn := Function.update s.brbIn k b' })
  /-- An internal step of one bind-BRB instance. -/
  | brbBindTau (s : LowState P.n X) (k : Fin P.n)
      (b' : BRB.ImplState P.n (APSet P.n X))
      (h : BRB.ImplStep P k (s.brbBind k) BRB.Lab.tau (PMF.pure b')) :
      LowStep P s .tau (PMF.pure { s with brbBind := Function.update s.brbBind k b' })
  /-- Asynchronous delivery on the gather fabric. -/
  | deliver (s : LowState P.n X) (i j : Fin P.n) (m : GaMsg P.n X)
      (h : m ∈ s.ga.sent j) :
      LowStep P s .tau (PMF.pure { s with ga := s.ga.recvMsg i j m })
  /-- `ECHO`: the process holds `n − f` pairs. -/
  | echo (s : LowState P.n X) (j : Fin P.n) (A : APSet P.n X)
      (hin : (s.ga.proc j).input ≠ none)
      (happ : approvedAt P s j A) (hcard : P.n - P.f ≤ A.card)
      (hsend : (s.ga.proc j).sentEcho = none) :
      LowStep P s .tau
        (PMF.pure { s with ga := (s.ga.setProc j
          { s.ga.proc j with sentEcho := some A }).mcast j (.echo A) })
  /-- `VOTE`: `n − f` senders' `ECHO` payloads, each held at `j` and
  contained in the vote payload, are delivered. -/
  | vote (s : LowState P.n X) (j : Fin P.n) (U : APSet P.n X)
      (hin : (s.ga.proc j).input ≠ none)
      (happ : approvedAt P s j U)
      (hQ : ∃ Q : Finset (Fin P.n), P.n - P.f ≤ Q.card ∧
        ∀ q ∈ Q, ∃ A, GaMsg.echo A ∈ s.ga.recv j q ∧ approvedAt P s j A ∧ A ⊆ U)
      (hsend : (s.ga.proc j).sentVote = none) :
      LowStep P s .tau
        (PMF.pure { s with ga := (s.ga.setProc j
          { s.ga.proc j with sentVote := some U }).mcast j (.vote U) })
  /-- `BIND`: `n − f` senders' `VOTE` payloads, each held at `j` and
  contained in the bind payload, are delivered; the payload is broadcast
  through the process's own bind-BRB instance. -/
  | bindCall (s : LowState P.n X) (j : Fin P.n) (U : APSet P.n X)
      (hin : (s.ga.proc j).input ≠ none)
      (hbc : ((s.brbBind j).proc j).input = none)
      (happ : approvedAt P s j U)
      (hQ : ∃ Q : Finset (Fin P.n), P.n - P.f ≤ Q.card ∧
        ∀ q ∈ Q, ∃ W, GaMsg.vote W ∈ s.ga.recv j q ∧ approvedAt P s j W ∧ W ⊆ U) :
      LowStep P s .tau
        (PMF.pure
        { s with
          brbBind := Function.update s.brbBind j
            (((s.brbBind j).setProc j
              { (s.brbBind j).proc j with input := some U }).mcast j (.init U)) })
  /-- Byzantine injection on the gather fabric. -/
  | byz (s : LowState P.n X) (j : Fin P.n) (m : GaMsg P.n X) (h : j ∈ s.ga.F) :
      LowStep P s .tau (PMF.pure { s with ga := s.ga.mcast j m })
  /-- Return: `n − f` bind-BRB payloads held at the returner, each a sub-map
  of the output, and the output held pairwise. -/
  | ret (s : LowState P.n X) (id : Fin P.n) (g : Fin P.n → Option X)
      (hin : (s.ga.proc id).input ≠ none)
      (hsubap : ∀ k x, g k = some x → apIn P s id k x)
      (hQ : ∃ Q : Finset (Fin P.n), P.n - P.f ≤ Q.card ∧
        ∀ q ∈ Q, ∃ U, apBind P s id q U ∧ APSet.subMap U g)
      (hr : (s.ga.proc id).returned = false) :
      LowStep P s (.ret id g)
        (PMF.pure
        { s with ga := s.ga.setProc id { s.ga.proc id with returned := true } })
  /-- Corruption (deviation D1), in lockstep across the fabric and every
  Bracha coordinate. -/
  | fail (s : LowState P.n X) (id : Fin P.n) :
      LowStep P s (.fail id) (PMF.pure (s.corruptAll P id))

/-- The gather-over-Bracha instance. -/
noncomputable def lowInst (P : Params) (X : Type) [DecidableEq X] :
    System (LowState P.n X) (Lab P.n X) where
  init := LowState.initial P.n X
  step := LowStep P

@[simp] theorem lowInst_init (P : Params) :
    (lowInst P X).init = LowState.initial P.n X := rfl

@[simp] theorem lowInst_step (P : Params) (s : LowState P.n X)
    (l : Lab P.n X) (μ : PMF (LowState P.n X)) :
    (lowInst P X).step s l μ ↔ LowStep P s l μ := Iff.rfl

/-- Every transition is Dirac: the instance is an LTS. -/
theorem lowInst_isLTS (P : Params) : (lowInst P X).IsLTS := by
  rintro s l μ hstep
  cases hstep <;> exact ⟨_, rfl⟩

end Rules

end Gather
end ABA
end PLTS
