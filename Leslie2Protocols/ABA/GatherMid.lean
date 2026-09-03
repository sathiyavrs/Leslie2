/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sathiya / Claude
-/

import Leslie2Protocols.ABA.GatherSpec
import Leslie2Protocols.ABA.BRBSpec

/-!
# The gather implementation over the BRB specification (blueprint Algorithm 4, deviation D28)

The gather aggregation ladder read over the BRB specification: the source's
Algorithm 4 with its reliable-broadcast sub-protocol replaced by the BRB
specification instances it calls, one per process for the inputs and one per
process for the `BIND` payloads. This is the source's `Gather.Hybrid`
composition, as one flat rule table on the gather alphabet.

Each process, once called:

* contributes its payload through its own input-BRB instance (the call is
  fused with the broadcast);
* `ECHO A` — multicast once it holds `n − f` committed pairs (`approved`:
  every pair of `A` is a committed input-BRB entry);
* `VOTE U` — multicast once `n − f` senders' approved `ECHO` payloads, each
  contained in `U`, are delivered;
* `BIND U` — contributed through the process's own bind-BRB instance, once
  `n − f` senders' approved `VOTE` payloads, each contained in `U`, are
  delivered;
* return `g` — once `n − f` bind-BRB instances hold committed payloads, each
  a sub-map of `g`, with `g` itself a sub-map of the committed inputs.

`ECHO` and `VOTE` are plain multicasts on the instance's message fabric
(`ABA.SubState`, deviations D1/D5). The `BIND` payloads travel by reliable
broadcast instead: the binding argument (`ABA/GatherSim.lean`) freezes a
family of bind payloads at the first return and later returns must be held to
those exact payloads, which a multicast cannot do once the sender is
corrupted — the source's argument pins them by the sender's honesty, sound
against its static adversary and unsound against this development's `fail`
events. A committed bind-BRB entry is pinned mechanically (deviation D25).

There is no gating of the `ECHO`/`VOTE`/`BIND` handlers beyond participation
(D8: a process acts only once called); the handlers are the source's `upon`
clauses, with no own-send ordering between levels.
-/

namespace PLTS
namespace ABA
namespace Gather

/-- The plain-multicast messages of one gather instance: the `ECHO` and
`VOTE` payload sets. The `BIND` payloads travel by reliable broadcast and are
not messages of the fabric. -/
inductive GaMsg (n : ℕ) (X : Type) : Type
  /-- `⟨ECHO, A⟩`. -/
  | echo (A : APSet n X)
  /-- `⟨VOTE, A⟩`. -/
  | vote (A : APSet n X)
  deriving DecidableEq

/-- The local record of one process in one gather instance. The `BIND` slot
is the process's own bind-BRB instance's call record, not a field here. -/
structure PRec (n : ℕ) (X : Type) : Type where
  /-- The payload received via `call` (`none` before the call). -/
  input : Option X
  /-- The `ECHO` payload multicast, if any (write-once). -/
  sentEcho : Option (APSet n X)
  /-- The `VOTE` payload multicast, if any (write-once). -/
  sentVote : Option (APSet n X)
  /-- Whether this process has returned. -/
  returned : Bool
  deriving DecidableEq

/-- The initial local record. -/
def PRec.initial (n : ℕ) (X : Type) : PRec n X where
  input := none
  sentEcho := none
  sentVote := none
  returned := false

/-- The state of one gather-over-BRB-specification instance: the gather boxes
and fabric, the `n` input-BRB specification states, and the `n` bind-BRB
specification states. -/
structure MidState (n : ℕ) (X : Type) : Type where
  /-- The gather processes' boxes and the instance's message fabric. -/
  ga : SubState n (PRec n X) (GaMsg n X)
  /-- `brbIn k` — the BRB specification instance broadcasting `k`'s input. -/
  brbIn : ∀ _ : Fin n, BRB.SpecState n X
  /-- `brbBind k` — the BRB specification instance broadcasting `k`'s `BIND`
  payload. -/
  brbBind : ∀ _ : Fin n, BRB.SpecState n (APSet n X)

namespace MidState

variable {n : ℕ} {X : Type}

/-- The initial instance state. -/
def initial (n : ℕ) (X : Type) : MidState n X where
  ga := SubState.initial n (GaMsg n X) (PRec.initial n X)
  brbIn := fun _ => BRB.SpecState.initial n X
  brbBind := fun _ => BRB.SpecState.initial n (APSet n X)

/-- A payload set is approved when every pair is a committed input-BRB
entry. Monotone: committed entries are written once and never unwritten. -/
def approved (s : MidState n X) (A : APSet n X) : Prop :=
  A.subMap (fun k => (s.brbIn k).val)

/-- Corruption (deviation D1): the broadcast transform, corrupting the gather
fabric and every BRB coordinate in lockstep. -/
def corruptAll (P : Params) (id : Fin P.n) (s : MidState P.n X) : MidState P.n X where
  ga := s.ga.corrupt P id
  brbIn := fun k => (s.brbIn k).corrupt P id
  brbBind := fun k => (s.brbBind k).corrupt P id

@[simp] theorem corruptAll_ga_proc (P : Params) (id : Fin P.n) (s : MidState P.n X) :
    (s.corruptAll P id).ga.proc = s.ga.proc := rfl
@[simp] theorem corruptAll_ga_sent (P : Params) (id : Fin P.n) (s : MidState P.n X) :
    (s.corruptAll P id).ga.sent = s.ga.sent := by
  change (s.ga.corrupt P id).sent = s.ga.sent
  exact SubState.corrupt_sent s.ga id
@[simp] theorem corruptAll_ga_recv (P : Params) (id : Fin P.n) (s : MidState P.n X) :
    (s.corruptAll P id).ga.recv = s.ga.recv := rfl
@[simp] theorem corruptAll_brbIn_input (P : Params) (id : Fin P.n) (s : MidState P.n X)
    (k : Fin P.n) : ((s.corruptAll P id).brbIn k).input = (s.brbIn k).input := by
  change ((s.brbIn k).corrupt P id).input = _
  exact BRB.corrupt_input P (s.brbIn k) id
@[simp] theorem corruptAll_brbIn_val (P : Params) (id : Fin P.n) (s : MidState P.n X)
    (k : Fin P.n) : ((s.corruptAll P id).brbIn k).val = (s.brbIn k).val := by
  change ((s.brbIn k).corrupt P id).val = _
  exact BRB.corrupt_val P (s.brbIn k) id
@[simp] theorem corruptAll_brbBind_input (P : Params) (id : Fin P.n) (s : MidState P.n X)
    (k : Fin P.n) : ((s.corruptAll P id).brbBind k).input = (s.brbBind k).input := by
  change ((s.brbBind k).corrupt P id).input = _
  exact BRB.corrupt_input P (s.brbBind k) id
@[simp] theorem corruptAll_brbBind_val (P : Params) (id : Fin P.n) (s : MidState P.n X)
    (k : Fin P.n) : ((s.corruptAll P id).brbBind k).val = (s.brbBind k).val := by
  change ((s.brbBind k).corrupt P id).val = _
  exact BRB.corrupt_val P (s.brbBind k) id

@[simp] theorem corruptAll_approved (P : Params) (id : Fin P.n) (s : MidState P.n X)
    (A : APSet P.n X) : (s.corruptAll P id).approved A ↔ s.approved A := by
  unfold approved APSet.subMap
  simp

end MidState

variable {X : Type} [DecidableEq X]

/-- The step relation of the gather-over-BRB-specification instance
(blueprint Algorithm 4 read over Transition System 6). All transitions are
Dirac; the BRB coordinates move by their own specification rows, embedded as
internal transitions. -/
inductive MidStep (P : Params) :
    MidState P.n X → Lab P.n X → PMF (MidState P.n X) → Prop
  /-- The environment call arrives: record the payload and contribute it
  through the process's input-BRB instance (the broadcast call is fused). -/
  | call (s : MidState P.n X) (id : Fin P.n) (x : X)
      (h : (s.ga.proc id).input = none) :
      MidStep P s (.call id x)
        (PMF.pure
        { s with
          ga := s.ga.setProc id { s.ga.proc id with input := some x }
          brbIn := Function.update s.brbIn id { s.brbIn id with input := some x } })
  /-- Input-enabledness loop for `call`. -/
  | callLoop (s : MidState P.n X) (id : Fin P.n) (x : X) :
      MidStep P s (.call id x) (PMF.pure s)
  /-- An input-BRB instance commits (its specification's `commit` row). -/
  | commitIn (s : MidState P.n X) (k : Fin P.n) (v : X)
      (hv : (s.brbIn k).val = none)
      (hm : k ∈ s.ga.F ∨ (s.brbIn k).input = some v) :
      MidStep P s .tau
        (PMF.pure
        { s with brbIn := Function.update s.brbIn k { s.brbIn k with val := some v } })
  /-- A bind-BRB instance commits (its specification's `commit` row). -/
  | commitBind (s : MidState P.n X) (k : Fin P.n) (U : APSet P.n X)
      (hv : (s.brbBind k).val = none)
      (hm : k ∈ s.ga.F ∨ (s.brbBind k).input = some U) :
      MidStep P s .tau
        (PMF.pure
        { s with brbBind := Function.update s.brbBind k { s.brbBind k with val := some U } })
  /-- Asynchronous delivery on the gather fabric. -/
  | deliver (s : MidState P.n X) (i j : Fin P.n) (m : GaMsg P.n X)
      (h : m ∈ s.ga.sent j) :
      MidStep P s .tau (PMF.pure { s with ga := s.ga.recvMsg i j m })
  /-- `ECHO`: the process holds `n − f` committed pairs. -/
  | echo (s : MidState P.n X) (j : Fin P.n) (A : APSet P.n X)
      (hin : (s.ga.proc j).input ≠ none)
      (happ : s.approved A) (hcard : P.n - P.f ≤ A.card)
      (hsend : (s.ga.proc j).sentEcho = none) :
      MidStep P s .tau
        (PMF.pure { s with ga := (s.ga.setProc j
          { s.ga.proc j with sentEcho := some A }).mcast j (.echo A) })
  /-- `VOTE`: `n − f` senders' approved `ECHO` payloads, each contained in
  the vote payload, are delivered. -/
  | vote (s : MidState P.n X) (j : Fin P.n) (U : APSet P.n X)
      (hin : (s.ga.proc j).input ≠ none)
      (happ : s.approved U)
      (hQ : ∃ Q : Finset (Fin P.n), P.n - P.f ≤ Q.card ∧
        ∀ q ∈ Q, ∃ A, GaMsg.echo A ∈ s.ga.recv j q ∧ s.approved A ∧ A ⊆ U)
      (hsend : (s.ga.proc j).sentVote = none) :
      MidStep P s .tau
        (PMF.pure { s with ga := (s.ga.setProc j
          { s.ga.proc j with sentVote := some U }).mcast j (.vote U) })
  /-- `BIND`: `n − f` senders' approved `VOTE` payloads, each contained in
  the bind payload, are delivered; the payload is contributed through the
  process's own bind-BRB instance. -/
  | bindCall (s : MidState P.n X) (j : Fin P.n) (U : APSet P.n X)
      (hin : (s.ga.proc j).input ≠ none)
      (hb : (s.brbBind j).input = none)
      (happ : s.approved U)
      (hQ : ∃ Q : Finset (Fin P.n), P.n - P.f ≤ Q.card ∧
        ∀ q ∈ Q, ∃ W, GaMsg.vote W ∈ s.ga.recv j q ∧ s.approved W ∧ W ⊆ U) :
      MidStep P s .tau
        (PMF.pure
        { s with brbBind := Function.update s.brbBind j { s.brbBind j with input := some U } })
  /-- Byzantine injection on the gather fabric. -/
  | byz (s : MidState P.n X) (j : Fin P.n) (m : GaMsg P.n X) (h : j ∈ s.ga.F) :
      MidStep P s .tau (PMF.pure { s with ga := s.ga.mcast j m })
  /-- Return: `n − f` bind-BRB instances hold committed payloads, each a
  sub-map of the output, and the output is a sub-map of the committed
  inputs. -/
  | ret (s : MidState P.n X) (id : Fin P.n) (g : Fin P.n → Option X)
      (hin : (s.ga.proc id).input ≠ none)
      (hsub : ∀ k x, g k = some x → (s.brbIn k).val = some x)
      (hQ : ∃ Q : Finset (Fin P.n), P.n - P.f ≤ Q.card ∧
        ∀ q ∈ Q, ∃ U, (s.brbBind q).val = some U ∧ APSet.subMap U g)
      (hr : (s.ga.proc id).returned = false) :
      MidStep P s (.ret id g)
        (PMF.pure
        { s with ga := s.ga.setProc id { s.ga.proc id with returned := true } })
  /-- Corruption (deviation D1), in lockstep across the fabric and every BRB
  coordinate. -/
  | fail (s : MidState P.n X) (id : Fin P.n) :
      MidStep P s (.fail id) (PMF.pure (s.corruptAll P id))

/-- The gather-over-BRB-specification instance. -/
noncomputable def midInst (P : Params) (X : Type) [DecidableEq X] :
    System (MidState P.n X) (Lab P.n X) where
  init := MidState.initial P.n X
  step := MidStep P

@[simp] theorem midInst_init (P : Params) :
    (midInst P X).init = MidState.initial P.n X := rfl

@[simp] theorem midInst_step (P : Params) (s : MidState P.n X)
    (l : Lab P.n X) (μ : PMF (MidState P.n X)) :
    (midInst P X).step s l μ ↔ MidStep P s l μ := Iff.rfl

/-- Every transition is Dirac: the instance is an LTS. -/
theorem midInst_isLTS (P : Params) : (midInst P X).IsLTS := by
  rintro s l μ hstep
  cases hstep <;> exact ⟨_, rfl⟩

end Gather
end ABA
end PLTS
