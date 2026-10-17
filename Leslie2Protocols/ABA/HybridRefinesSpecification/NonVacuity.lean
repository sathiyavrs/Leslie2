/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sathiya / Claude
-/

import Leslie2Protocols.ABA.Composition.Hybrid
import Leslie2Protocols.ABA.Composition.ABAState

/-!
# Non-vacuity witnesses for the protocol-shaped specification

Machine-checked witnesses that the composed system `hybrid P M` executes a nontrivial prefix, so
that the simulation `ABA.hybridRefinesSpecification` does not hold vacuously through a deadlock
at the initial state.

We fix the parameter set `fourProcesses` (`n = 4`, `f = 1`, `ε = 1/2`) and exhibit a run of 24
steps of `hybrid fourProcesses M` from its initial state to a `retABA`, the decision of a
process. The run is exhibited for every type `M` of round messages, since no step of it carries a
round message. Its steps are these.

* `step_callABA₀/₁/₂`: three external input calls (`callABA`, visible). The addressed round loop
  takes its `input` transition; the other three round loops, the specification family, the ABA
  network and the common coin idle.
* `step_callG₀/₁/₂`: three graded-agreement calls (`callG 0`, hidden). The caller's round loop
  calls with its estimate `true` and enters `awaitG`, the round-`0` specification takes its owned
  `call`, and the ABA network records round `0` among the started rounds (D37).
* `step_bindUnset`: the silent transition `bindUnset` of the round-`0` specification, which
  excludes the bit `false`. The family takes it at round `0`, which lies in its map from the
  first call on. The three callers of `true` meet the quorum `n − f = 3`.
* `step_retG₀/₁/₂`: the three graded-agreement returns of `grade2 true` (`retG 0`, hidden), the
  first of which writes the round's grade 2. Their guard pair, `true ∉ excluded` and
  `false ∈ excluded`, holds from `step_bindUnset` on.
* `step_callW₀`, `step_callW₁`: the coin calls of processes `0` and `1` (`callW 0`, hidden). Each
  call records its caller, and the second carries the caller count to `2 > f`.
* `step_resolve` and `step_resolve_mass`: the silent resolution of the round-`0` coin, a round
  of the map of the common coin's family from the first coin call on. This is the run's single
  probabilistic step: at `val = ⊥` with the caller count above `f`, the resolution draws `val`
  from `wccPMF`, and the successor with `val = bit true` has mass `ε = 1/2 > 0`.
* `step_callW₂`: process `2`'s coin call, which records its caller at a resolved `val`.
* `step_retW₀/₁/₂`: the three coin returns (`retW 0`, hidden). Each process takes the round
  advance, keeps the grade `grade2 true` and enters `toSendDecided` at round `1`.
* `step_decidedSend₀/₁/₂`: the DECIDED send of each process after its coin return
  (`decidedSend`, hidden). The round loop records `true` among its own DECIDED sends, clears the
  grade and enters `toCallG`, and the network records `true` in the sender's DECIDED set.
* `step_deliver₀/₁/₂`: the adversary delivers the three DECIDED messages to process `0`
  (`decidedDeliver`, hidden), which meets the return quorum `n − f = 3`.
* `step_retABA`: process `0` takes `retABA 0 true`. Its round loop reads the quorum and its own
  record of the DECIDED send, and the ABA network idles.

Two further lemmas witness single transitions. `step_boundG` is the announcement of round `0`'s
bound bit `true` after the first return, a silent self-loop (D29). `step_fail` is a `fail`
broadcast at the initial state, which synchronises all four components.

Every step but the resolution has a Dirac successor, and the chosen outcome of the resolution
has mass `ε > 0`, so the run has positive probability: a product of Diracs and one factor `ε`.
The guards discharge by `decide` and `rfl`. A guard on the round-`0` instance of the
specification family is decided once the accessor lemmas of `InstanceFamilyState` rewrite that
instance to a closed term (`decide_at_round_zero`). Round `0` lies in the map of a family from
the family's first transition at round `0` on
(`InstanceFamilyState.mem_keys_setInstanceState_self`), which the silent transitions of
`step_bindUnset` and `step_resolve` require. The Dirac successor distributions collapse through
`prodPMF_pure_pure` and `PMF.pure_map`, and the mass of the resolution's outcome through
`prodPMF_pure_left_apply` and `map_apply_inj`.

A state of the run is a triple: the specification family, one `ABAState` holding the round loops
beside the ABA network, as `ABA/Composition/ABAState.lean` groups them, and the common coin's
family. `hybridStateOf` assembles the triple into the four-component state. Each family starts
from `InstanceFamilyState.initial`, moves by `setInstanceState` at round `0`, and takes `fail` by
`applyBroadcast`.

Each component carries one name per state of the run and one name per update. The states are
`abaInitial`, `gbcaSpecificationsInitial` and `coinInitial`, and then, for each component, the
state the step named in the list above reaches: `abaAfterInput0`, `abaAfterCallG0`,
`abaAfterRetG0`, `abaAfterCallW0`, `abaAfterRetW0`, `abaAfterDecidedSend0`, `abaAfterDeliver0`,
`abaAfterRetABA` and `abaAfterFail`; `gbcaSpecificationsAfterCall0`,
`gbcaSpecificationsAfterBindUnset`, `gbcaSpecificationsAfterReturn0` and
`gbcaSpecificationsAfterFail`; `coinAfterRecordingCall0`, `coinAfterRecordingCall1`,
`coinAfterResolution`, `coinAfterRecordingCall2`, `coinAfterReturn0` and `coinAfterFail`. The
updates are `abaInput`, `abaCallG`, `abaRetG`, `abaCallW` in the ABA component,
`gbcaSpecificationCall` and `gbcaSpecificationRetGrade2` on the specification family, and
`coinCall`, `coinResolve` and `coinReturn` on the common coin's family. Reading a state name gives
the step it follows, and reading an update name gives the transition it belongs to. -/

namespace PLTS
namespace ABA

open Implementation hiding NetworkEvent ExtendedLabel
open Composition

/-- The parameter set of the witnesses: four processes, the corruption budget one, and a coin with
`ε = 1/2` and `δ = 0`. Each bit outcome has mass `ε = 1/2`, so the witnessed resolution can take
the outcome `bit true`. The condition `2 * ε + δ ≤ 1` holds with equality, so the outcome `⊤` and
the outcome `undelivered` both have mass `0`. -/
noncomputable abbrev fourProcesses : Parameters := ⟨4, 1, by omega, 1 / 2, 0, by
  rw [add_zero, one_div, ENNReal.mul_inv_cancel] <;> simp, by simp⟩

namespace NonVacuity

/-! `M` is the type of the messages a graded-agreement round exchanges. -/

variable {M : Type} [DecidableEq M]

/-! ### Assembling and moving the four components -/

/-- The state of the common coin's family at the parameters `fourProcesses`. -/
abbrev CoinFamilyState : Type :=
  InstanceFamilyState (WCC.SpecState.initial fourProcesses.n) (WCC.failAct fourProcesses)

/-- A state of the protocol-shaped specification, assembled from the specification family, the
ABA component and the common coin's family. -/
def hybridStateOf (G : GBCASpecificationFamilyState fourProcesses M) (s : ABAState fourProcesses)
    (o : CoinFamilyState) : HybridState fourProcesses M := (G, s.1, s.2, o)

/-- The round loops on a label one of them owns: the addressed round loop takes its transition,
the others take an idle transition, and the successor of the group is the pointwise update. -/
theorem roundLoops_at {C : ∀ _ : Fin 4, RoundLoopVariables 4} (id : Fin 4) {L : ExtendedLabel 4 M}
    {c' : RoundLoopVariables 4} (hown : RoundLoopStep fourProcesses id (C id) L (PMF.pure c'))
    (hidle : ∀ j, j ≠ id → RoundLoopStep fourProcesses j (C j) L (PMF.pure (C j))) (i : Fin 4) :
    RoundLoopStep fourProcesses i (C i) L (PMF.pure (Function.update C id c' i)) := by
  by_cases h : i = id
  · subst h; rw [Function.update_self]; exact hown
  · rw [Function.update_of_ne h]; exact hidle i h

/-- The common coin's family on a label one of its rounds owns, at a transition whose successor
need not be a point mass: the family's successor is the round's, pushed forward along the update
of the family at that round. -/
theorem wccFamilyStep (o : CoinFamilyState) {l : Label 4} {r : ℕ}
    {μ : PMF (WCC.SpecState 4)} (hr : Label.wccRound l = some r)
    (h : WCC.Step fourProcesses r (o r) l μ) :
    (WCC.specFamily fourProcesses).step o l (μ.map (o.setInstanceState r)) := by
  rw [WCC.specFamily, System.family_step_iff]
  exact Or.inr (Or.inl ⟨r, hr, μ, h, rfl⟩)

/-- The common coin's idle transition on a shared label that is neither `τ`, nor a call or a
return of one of its rounds, nor `fail`. -/
theorem wccIdle (o : CoinFamilyState) {l : Label 4} (hl : l ≠ Label.tau)
    (hr : Label.wccRound l = none) (hf : ¬ Label.isFail l) :
    (coinOverRoundAlphabet fourProcesses M).step o (Sum.inl l) (PMF.pure o) :=
  (System.mapIdle_step_some (coinLabelMap_inl l) (PMF.pure o)).mpr
    (wccFamily_idle fourProcesses o hl hr hf)

/-- Decides a guard on the round-`0` instance of a state of the specification family. The states
of that family are abbreviations, so the accessor lemmas `setInstanceState_apply_same` and
`initial_apply` of `InstanceFamilyState` rewrite the instance to a closed term, free of the
message type `M`, and `decide` evaluates the guard on that term. -/
local macro "decide_at_round_zero" : tactic =>
  `(tactic| (simp only [InstanceFamilyState.setInstanceState_apply_same,
    InstanceFamilyState.initial_apply] <;> decide))

/-! ### Named states of the run -/

/-- The specification family at the start: no round touched, every round initial. -/
noncomputable abbrev gbcaSpecificationsInitial : GBCASpecificationFamilyState fourProcesses M :=
  InstanceFamilyState.initial

/-- The common coin's family at the start: no round touched, every round initial. -/
noncomputable def coinInitial : CoinFamilyState := InstanceFamilyState.initial

/-- The ABA state at the start: every round loop idle, nothing multicast, nobody corrupted, no
round started. -/
noncomputable def abaInitial : ABAState fourProcesses := ABAState.initial fourProcesses

/-- The ABA update of the input `callABA id true`: process `id` enters round `0`, ready to call
graded agreement. -/
noncomputable def abaInput (id : Fin 4) (s : ABAState fourProcesses) : ABAState fourProcesses :=
  s.setProcessVariables id { s.processes id with
    input := some true, estimate := some true, round := 0, phase := .toCallG }

/-- The ABA update of process `id`'s call `callG 0 id true`: the round loop enters `awaitG`, and
the ABA network records round `0` among the started rounds (D37). -/
noncomputable def abaCallG (id : Fin 4) (s : ABAState fourProcesses) : ABAState fourProcesses :=
  ((s.setProcessVariables id { s.processes id with phase := .awaitG }).1,
    s.2.recordStartedRound 0 id)

/-- The ABA update of process `id`'s round-`0` return `grade2 true`: the round loop adopts the
estimate, records the grade and enters `toCallW`. -/
noncomputable def abaRetG (id : Fin 4) (s : ABAState fourProcesses) : ABAState fourProcesses :=
  s.setProcessVariables id { s.processes id with
    estimate := some true, lastGrade := some (.grade2 true), phase := .toCallW }

/-- The ABA update of process `id`'s coin call `callW 0 id`: the round loop enters `awaitW`. -/
noncomputable def abaCallW (id : Fin 4) (s : ABAState fourProcesses) : ABAState fourProcesses :=
  s.setProcessVariables id { s.processes id with phase := .awaitW }

/-- The update of the specification family by the call of `id` with input `true` at round `0`:
the round-`0` specification records the input. -/
noncomputable abbrev gbcaSpecificationCall (id : Fin 4)
    (G : GBCASpecificationFamilyState fourProcesses M) :
    GBCASpecificationFamilyState fourProcesses M :=
  G.setInstanceState 0 { G 0 with call := Function.update (G 0).call id (some true) }

/-- The update of the specification family by the return of `grade2 true` to `id` at round `0`:
the round-`0` specification writes the grade 2 and records the return. -/
noncomputable abbrev gbcaSpecificationRetGrade2 (id : Fin 4)
    (G : GBCASpecificationFamilyState fourProcesses M) :
    GBCASpecificationFamilyState fourProcesses M :=
  G.setInstanceState 0 { G 0 with grade := some true, ret := Function.update (G 0).ret id true }

/-- The update of the common coin's family by the call of `id` at round `0`: the round-`0` coin
records `id` as a caller. -/
noncomputable def coinCall (id : Fin 4) (o : CoinFamilyState) : CoinFamilyState :=
  o.setInstanceState 0 ((o 0).record id)

/-- The update of the common coin's family by the resolution of the round-`0` coin at the outcome
`v`: the round-`0` coin writes `v`. -/
noncomputable def coinResolve (v : CoinValue) (o : CoinFamilyState) : CoinFamilyState :=
  o.setInstanceState 0 { o 0 with val := v }

/-- The update of the common coin's family by the return `retW 0 id true`: the round-`0` coin
records the return. -/
noncomputable def coinReturn (id : Fin 4) (o : CoinFamilyState) : CoinFamilyState :=
  o.setInstanceState 0 { o 0 with ret := Function.update (o 0).ret id true }

/-- ABA states after the three inputs. -/
noncomputable def abaAfterInput0 : ABAState fourProcesses := abaInput 0 abaInitial
noncomputable def abaAfterInput1 : ABAState fourProcesses := abaInput 1 abaAfterInput0
noncomputable def abaAfterInput2 : ABAState fourProcesses := abaInput 2 abaAfterInput1

/-- The specification family after the three round-`0` calls. -/
noncomputable abbrev gbcaSpecificationsAfterCall0 :
    GBCASpecificationFamilyState fourProcesses M :=
  gbcaSpecificationCall 0 gbcaSpecificationsInitial
noncomputable abbrev gbcaSpecificationsAfterCall1 :
    GBCASpecificationFamilyState fourProcesses M :=
  gbcaSpecificationCall 1 gbcaSpecificationsAfterCall0
noncomputable abbrev gbcaSpecificationsAfterCall2 :
    GBCASpecificationFamilyState fourProcesses M :=
  gbcaSpecificationCall 2 gbcaSpecificationsAfterCall1

/-- ABA states after the three round-`0` calls. -/
noncomputable def abaAfterCallG0 : ABAState fourProcesses := abaCallG 0 abaAfterInput2
noncomputable def abaAfterCallG1 : ABAState fourProcesses := abaCallG 1 abaAfterCallG0
noncomputable def abaAfterCallG2 : ABAState fourProcesses := abaCallG 2 abaAfterCallG1

/-- The specification family after `bindUnset` excludes the round-`0` bit `false`. The excluded
set of round `0` is `{false}`, and `true` is not excluded. -/
noncomputable abbrev gbcaSpecificationsAfterBindUnset :
    GBCASpecificationFamilyState fourProcesses M :=
  gbcaSpecificationsAfterCall2.setInstanceState 0
    { gbcaSpecificationsAfterCall2 (M := M) 0 with
      excluded := insert false (gbcaSpecificationsAfterCall2 (M := M) 0).excluded }

/-- The specification family after the three round-`0` returns of `grade2 true`. -/
noncomputable abbrev gbcaSpecificationsAfterReturn0 :
    GBCASpecificationFamilyState fourProcesses M :=
  gbcaSpecificationRetGrade2 0 gbcaSpecificationsAfterBindUnset
noncomputable abbrev gbcaSpecificationsAfterReturn1 :
    GBCASpecificationFamilyState fourProcesses M :=
  gbcaSpecificationRetGrade2 1 gbcaSpecificationsAfterReturn0
noncomputable abbrev gbcaSpecificationsAfterReturn2 :
    GBCASpecificationFamilyState fourProcesses M :=
  gbcaSpecificationRetGrade2 2 gbcaSpecificationsAfterReturn1

/-- ABA states after the three round-`0` graded-agreement returns. -/
noncomputable def abaAfterRetG0 : ABAState fourProcesses := abaRetG 0 abaAfterCallG2
noncomputable def abaAfterRetG1 : ABAState fourProcesses := abaRetG 1 abaAfterRetG0
noncomputable def abaAfterRetG2 : ABAState fourProcesses := abaRetG 2 abaAfterRetG1

/-- ABA states after the three coin calls. -/
noncomputable def abaAfterCallW0 : ABAState fourProcesses := abaCallW 0 abaAfterRetG2
noncomputable def abaAfterCallW1 : ABAState fourProcesses := abaCallW 1 abaAfterCallW0
noncomputable def abaAfterCallW2 : ABAState fourProcesses := abaCallW 2 abaAfterCallW1

/-- The common coin's family after process `0`'s call. -/
noncomputable def coinAfterRecordingCall0 : CoinFamilyState := coinCall 0 coinInitial

/-- The common coin's family after process `1`'s call, which carries the caller count of round
`0` to `2 > f`. -/
noncomputable def coinAfterRecordingCall1 : CoinFamilyState :=
  coinCall 1 coinAfterRecordingCall0

/-- The common coin's family after the resolution of the round-`0` coin, at the outcome
`bit true` of the draw. -/
noncomputable def coinAfterResolution : CoinFamilyState :=
  coinResolve (.bit true) coinAfterRecordingCall1

/-- The common coin's family after process `2`'s call, the third call of round `0`. -/
noncomputable def coinAfterRecordingCall2 : CoinFamilyState :=
  coinCall 2 coinAfterResolution

/-- The common coin's family after the three coin returns. -/
noncomputable def coinAfterReturn0 : CoinFamilyState := coinReturn 0 coinAfterRecordingCall2
noncomputable def coinAfterReturn1 : CoinFamilyState := coinReturn 1 coinAfterReturn0
noncomputable def coinAfterReturn2 : CoinFamilyState := coinReturn 2 coinAfterReturn1

/-- ABA states after the three coin returns and the three DECIDED sends, in the order of the run.
Each coin return is the round advance: the round closed with the grade `grade2 true`, so the
process keeps the grade and enters `toSendDecided` at round `1`. Each DECIDED send records `true`
in the sender's own record and in the sender's DECIDED set at the network, clears the grade and
enters `toCallG`. -/
noncomputable def abaAfterRetW0 : ABAState fourProcesses := abaAfterCallW2.stepRound 0 true
noncomputable def abaAfterDecidedSend0 : ABAState fourProcesses :=
  abaAfterRetW0.sendDecidedOnGrade2 0 true
noncomputable def abaAfterRetW1 : ABAState fourProcesses :=
  abaAfterDecidedSend0.stepRound 1 true
noncomputable def abaAfterDecidedSend1 : ABAState fourProcesses :=
  abaAfterRetW1.sendDecidedOnGrade2 1 true
noncomputable def abaAfterRetW2 : ABAState fourProcesses :=
  abaAfterDecidedSend1.stepRound 2 true
noncomputable def abaAfterDecidedSend2 : ABAState fourProcesses :=
  abaAfterRetW2.sendDecidedOnGrade2 2 true

/-- ABA states after the adversary delivers the three `⟨DECIDED, true⟩` messages to process
`0`. -/
noncomputable def abaAfterDeliver0 : ABAState fourProcesses :=
  abaAfterDecidedSend2.deliverDecided 0 0 true
noncomputable def abaAfterDeliver1 : ABAState fourProcesses :=
  abaAfterDeliver0.deliverDecided 0 1 true
noncomputable def abaAfterDeliver2 : ABAState fourProcesses :=
  abaAfterDeliver1.deliverDecided 0 2 true

/-- The ABA state after process `0` takes `retABA 0 true`. -/
noncomputable def abaAfterRetABA : ABAState fourProcesses :=
  abaAfterDeliver2.setProcessVariables 0 { abaAfterDeliver2.processes 0 with returned := true }

/-- The specification family after the broadcast `fail 0`, which corrupts process `0` at every
round, in the map or not. -/
noncomputable abbrev gbcaSpecificationsAfterFail :
    GBCASpecificationFamilyState fourProcesses M :=
  gbcaSpecificationsInitial.applyBroadcast (Sum.inl (Label.fail (0 : Fin 4)))

/-- The common coin's family after the broadcast `fail 0`. -/
noncomputable def coinAfterFail : CoinFamilyState :=
  coinInitial.applyBroadcast (Label.fail (0 : Fin 4))

/-- The ABA state after `fail 0`: the network's corrupted set holds process `0`, and process
`0`'s round loop carries the replacement flag. -/
noncomputable def abaAfterFail : ABAState fourProcesses :=
  ABAState.corrupt fourProcesses (0 : Fin 4) abaInitial

/-- The initial state of the protocol-shaped specification is
`(gbcaSpecificationsInitial, abaInitial, coinInitial)`. -/
theorem hybrid_init : (hybrid fourProcesses M).init = hybridStateOf gbcaSpecificationsInitial
    abaInitial coinInitial := rfl

/-! ### Steps 1–3: the external input calls (`callABA`, visible) -/

/-- First input: process `0` receives `callABA 0 true`. The label is visible. Process `0`'s round
loop takes `input`; the other round loops, the specification family, the ABA network and the
common coin idle. -/
theorem step_callABA₀ :
    (hybrid fourProcesses M).step (hybridStateOf gbcaSpecificationsInitial abaInitial coinInitial)
      (Label.callABA (0 : Fin 4) true)
      (PMF.pure (hybridStateOf gbcaSpecificationsInitial abaAfterInput0 coinInitial)) := by
  refine hybrid_visible fourProcesses (by simp) ?_
  have h := hybridExtended_visible_step (M := M) fourProcesses
    (G := gbcaSpecificationsInitial) (C := abaInitial.1) (A := abaInitial.2) (o := coinInitial)
    (L := Sum.inl (Label.callABA (0 : Fin 4) true)) (by simp)
    (gbcaSpecificationFamily_idle fourProcesses gbcaSpecificationsInitial (by simp) rfl not_false)
    (roundLoops_at 0 (RoundLoopStep.input (P := fourProcesses) (abaInitial.1 0) true rfl rfl)
      (fun j hj => RoundLoopStep.callABAIdle (P := fourProcesses) (abaInitial.1 j) 0 true
        (Ne.symm hj)))
    (ABANetworkStep.callABAIdle (P := fourProcesses) abaInitial.2 0 true)
    (wccIdle coinInitial (by simp) rfl (by simp [Label.isFail]))
  rw [prodPMF_pure_pure, prodPMF_pure_pure, prodPMF_pure_pure] at h
  exact h

/-- Second input: process `1`. -/
theorem step_callABA₁ :
    (hybrid fourProcesses M).step
      (hybridStateOf gbcaSpecificationsInitial abaAfterInput0 coinInitial)
      (Label.callABA (1 : Fin 4) true)
      (PMF.pure (hybridStateOf gbcaSpecificationsInitial abaAfterInput1 coinInitial)) := by
  refine hybrid_visible fourProcesses (by simp) ?_
  have h := hybridExtended_visible_step (M := M) fourProcesses
    (G := gbcaSpecificationsInitial) (C := abaAfterInput0.1) (A := abaAfterInput0.2)
    (o := coinInitial) (L := Sum.inl (Label.callABA (1 : Fin 4) true)) (by simp)
    (gbcaSpecificationFamily_idle fourProcesses gbcaSpecificationsInitial (by simp) rfl not_false)
    (roundLoops_at 1 (RoundLoopStep.input (P := fourProcesses) (abaAfterInput0.1 1) true
        (by decide) (by decide))
      (fun j hj => RoundLoopStep.callABAIdle (P := fourProcesses) (abaAfterInput0.1 j) 1 true
        (Ne.symm hj)))
    (ABANetworkStep.callABAIdle (P := fourProcesses) abaAfterInput0.2 1 true)
    (wccIdle coinInitial (by simp) rfl (by simp [Label.isFail]))
  rw [prodPMF_pure_pure, prodPMF_pure_pure, prodPMF_pure_pure] at h
  exact h

/-- Third input: process `2`. -/
theorem step_callABA₂ :
    (hybrid fourProcesses M).step
      (hybridStateOf gbcaSpecificationsInitial abaAfterInput1 coinInitial)
      (Label.callABA (2 : Fin 4) true)
      (PMF.pure (hybridStateOf gbcaSpecificationsInitial abaAfterInput2 coinInitial)) := by
  refine hybrid_visible fourProcesses (by simp) ?_
  have h := hybridExtended_visible_step (M := M) fourProcesses
    (G := gbcaSpecificationsInitial) (C := abaAfterInput1.1) (A := abaAfterInput1.2)
    (o := coinInitial) (L := Sum.inl (Label.callABA (2 : Fin 4) true)) (by simp)
    (gbcaSpecificationFamily_idle fourProcesses gbcaSpecificationsInitial (by simp) rfl not_false)
    (roundLoops_at 2 (RoundLoopStep.input (P := fourProcesses) (abaAfterInput1.1 2) true
        (by decide) (by decide))
      (fun j hj => RoundLoopStep.callABAIdle (P := fourProcesses) (abaAfterInput1.1 j) 2 true
        (Ne.symm hj)))
    (ABANetworkStep.callABAIdle (P := fourProcesses) abaAfterInput1.2 2 true)
    (wccIdle coinInitial (by simp) rfl (by simp [Label.isFail]))
  rw [prodPMF_pure_pure, prodPMF_pure_pure, prodPMF_pure_pure] at h
  exact h

/-! ### Steps 4–6: the graded-agreement calls (`callG 0`, hidden) -/

/-- First graded-agreement call: process `0`'s round loop calls with its estimate `true` and
enters `awaitG`, the round-`0` specification takes its owned `call`, and the ABA network records
round `0` among the started rounds. Round `0` enters the map of the specification family. -/
theorem step_callG₀ :
    (hybrid fourProcesses M).step
      (hybridStateOf gbcaSpecificationsInitial abaAfterInput2 coinInitial) Label.tau
      (PMF.pure (hybridStateOf gbcaSpecificationsAfterCall0 abaAfterCallG0 coinInitial)) := by
  refine hybrid_hidden fourProcesses (l := Label.callG 0 (0 : Fin 4) true) (by simp) ?_
  have h := hybridExtended_visible_step (M := M) fourProcesses
    (G := gbcaSpecificationsInitial) (C := abaAfterInput2.1) (A := abaAfterInput2.2)
    (o := coinInitial) (L := Sum.inl (Label.callG 0 (0 : Fin 4) true)) (by simp)
    (gbcaSpecificationFamily_owned fourProcesses rfl rfl
      (GBCA.Step.call (P := fourProcesses) (r := 0) (gbcaSpecificationsInitial (M := M) 0) 0 true
        rfl))
    (roundLoops_at 0
      (RoundLoopStep.callG (P := fourProcesses) (abaAfterInput2.1 0) 0 true (by decide)
        (by decide) (by decide) (by decide))
      (fun j hj => RoundLoopStep.callGIdle (P := fourProcesses) (abaAfterInput2.1 j) 0 0 true
        (Ne.symm hj)))
    (ABANetworkStep.callG (P := fourProcesses) abaAfterInput2.2 0 0 true)
    (wccIdle coinInitial (by simp) rfl (by simp [Label.isFail]))
  rw [prodPMF_pure_pure, prodPMF_pure_pure, prodPMF_pure_pure] at h
  exact h

/-- Second graded-agreement call: process `1`. -/
theorem step_callG₁ :
    (hybrid fourProcesses M).step
      (hybridStateOf gbcaSpecificationsAfterCall0 abaAfterCallG0 coinInitial) Label.tau
      (PMF.pure (hybridStateOf gbcaSpecificationsAfterCall1 abaAfterCallG1 coinInitial)) := by
  refine hybrid_hidden fourProcesses (l := Label.callG 0 (1 : Fin 4) true) (by simp) ?_
  have h := hybridExtended_visible_step (M := M) fourProcesses
    (G := gbcaSpecificationsAfterCall0) (C := abaAfterCallG0.1) (A := abaAfterCallG0.2)
    (o := coinInitial) (L := Sum.inl (Label.callG 0 (1 : Fin 4) true)) (by simp)
    (gbcaSpecificationFamily_owned fourProcesses rfl rfl
      (GBCA.Step.call (P := fourProcesses) (r := 0) (gbcaSpecificationsAfterCall0 (M := M) 0) 1
        true (by decide_at_round_zero)))
    (roundLoops_at 1
      (RoundLoopStep.callG (P := fourProcesses) (abaAfterCallG0.1 1) 0 true (by decide)
        (by decide) (by decide) (by decide))
      (fun j hj => RoundLoopStep.callGIdle (P := fourProcesses) (abaAfterCallG0.1 j) 0 1 true
        (Ne.symm hj)))
    (ABANetworkStep.callG (P := fourProcesses) abaAfterCallG0.2 0 1 true)
    (wccIdle coinInitial (by simp) rfl (by simp [Label.isFail]))
  rw [prodPMF_pure_pure, prodPMF_pure_pure, prodPMF_pure_pure] at h
  exact h

/-- Third graded-agreement call: process `2`. The round-`0` specification holds three inputs. -/
theorem step_callG₂ :
    (hybrid fourProcesses M).step
      (hybridStateOf gbcaSpecificationsAfterCall1 abaAfterCallG1 coinInitial) Label.tau
      (PMF.pure (hybridStateOf gbcaSpecificationsAfterCall2 abaAfterCallG2 coinInitial)) := by
  refine hybrid_hidden fourProcesses (l := Label.callG 0 (2 : Fin 4) true) (by simp) ?_
  have h := hybridExtended_visible_step (M := M) fourProcesses
    (G := gbcaSpecificationsAfterCall1) (C := abaAfterCallG1.1) (A := abaAfterCallG1.2)
    (o := coinInitial) (L := Sum.inl (Label.callG 0 (2 : Fin 4) true)) (by simp)
    (gbcaSpecificationFamily_owned fourProcesses rfl rfl
      (GBCA.Step.call (P := fourProcesses) (r := 0) (gbcaSpecificationsAfterCall1 (M := M) 0) 2
        true (by decide_at_round_zero)))
    (roundLoops_at 2
      (RoundLoopStep.callG (P := fourProcesses) (abaAfterCallG1.1 2) 0 true (by decide)
        (by decide) (by decide) (by decide))
      (fun j hj => RoundLoopStep.callGIdle (P := fourProcesses) (abaAfterCallG1.1 j) 0 2 true
        (Ne.symm hj)))
    (ABANetworkStep.callG (P := fourProcesses) abaAfterCallG1.2 0 2 true)
    (wccIdle coinInitial (by simp) rfl (by simp [Label.isFail]))
  rw [prodPMF_pure_pure, prodPMF_pure_pure, prodPMF_pure_pure] at h
  exact h

/-! ### Step 7: the silent transition `bindUnset` of the round-`0` specification -/

/-- Three of four processes have called round `0`, so the quorum `n − f = 3` is met, and
`bindUnset` excludes the bit `false`: the three callers of `true` give the bit `true` the support
`f + 1`. The specification family takes the transition at round `0`, a round of its map since the
first call, and the other three components do not move. -/
theorem step_bindUnset :
    (hybrid fourProcesses M).step
      (hybridStateOf gbcaSpecificationsAfterCall2 abaAfterCallG2 coinInitial) Label.tau
      (PMF.pure (hybridStateOf gbcaSpecificationsAfterBindUnset abaAfterCallG2 coinInitial)) := by
  refine hybrid_visible fourProcesses (by simp) ?_
  exact hybridExtended_tau_specification (M := M) fourProcesses
    (gbcaSpecificationFamily_tau fourProcesses
      (by exact InstanceFamilyState.mem_keys_setInstanceState_self _ _ _)
      (GBCA.Step.bindUnset (P := fourProcesses) (r := 0) (gbcaSpecificationsAfterCall2 (M := M) 0)
        false (by unfold GBCA.SpecState.quorum; decide_at_round_zero) (by decide_at_round_zero)
        (by decide_at_round_zero)))

/-! ### Steps 8–10: the three graded-agreement returns of `grade2 true` (`retG 0`, hidden) -/

/-- Process `0` takes the return `grade2 true`. The round-`0` specification writes the grade 2 and
records the return, and the round loop adopts the estimate and enters `toCallW`. -/
theorem step_retG₀ :
    (hybrid fourProcesses M).step
      (hybridStateOf gbcaSpecificationsAfterBindUnset abaAfterCallG2 coinInitial) Label.tau
      (PMF.pure (hybridStateOf gbcaSpecificationsAfterReturn0 abaAfterRetG0 coinInitial)) := by
  refine hybrid_hidden fourProcesses (l := Label.retG 0 (0 : Fin 4) (.grade2 true)) (by simp) ?_
  have h := hybridExtended_visible_step (M := M) fourProcesses
    (G := gbcaSpecificationsAfterBindUnset) (C := abaAfterCallG2.1) (A := abaAfterCallG2.2)
    (o := coinInitial) (L := Sum.inl (Label.retG 0 (0 : Fin 4) (.grade2 true))) (by simp)
    (gbcaSpecificationFamily_owned fourProcesses rfl rfl
      (GBCA.Step.retGrade2 (P := fourProcesses) (r := 0)
        (gbcaSpecificationsAfterBindUnset (M := M) 0) 0 true
        (by decide_at_round_zero) (by decide_at_round_zero) (by decide_at_round_zero)
        (by decide_at_round_zero)))
    (roundLoops_at 0
      (RoundLoopStep.retG (P := fourProcesses) (abaAfterCallG2.1 0) 0 (.grade2 true)
        (by decide) (by decide) (by decide))
      (fun j hj => RoundLoopStep.retGIdle (P := fourProcesses) (abaAfterCallG2.1 j) 0 0
        (.grade2 true) (Ne.symm hj)))
    (ABANetworkStep.retGIdle (P := fourProcesses) abaAfterCallG2.2 0 0 (.grade2 true))
    (wccIdle coinInitial (by simp) rfl (by simp [Label.isFail]))
  rw [prodPMF_pure_pure, prodPMF_pure_pure, prodPMF_pure_pure] at h
  exact h

/-- Process `1`'s round-`0` return of `grade2 true`. -/
theorem step_retG₁ :
    (hybrid fourProcesses M).step
      (hybridStateOf gbcaSpecificationsAfterReturn0 abaAfterRetG0 coinInitial) Label.tau
      (PMF.pure (hybridStateOf gbcaSpecificationsAfterReturn1 abaAfterRetG1 coinInitial)) := by
  refine hybrid_hidden fourProcesses (l := Label.retG 0 (1 : Fin 4) (.grade2 true)) (by simp) ?_
  have h := hybridExtended_visible_step (M := M) fourProcesses
    (G := gbcaSpecificationsAfterReturn0) (C := abaAfterRetG0.1) (A := abaAfterRetG0.2)
    (o := coinInitial) (L := Sum.inl (Label.retG 0 (1 : Fin 4) (.grade2 true))) (by simp)
    (gbcaSpecificationFamily_owned fourProcesses rfl rfl
      (GBCA.Step.retGrade2 (P := fourProcesses) (r := 0)
        (gbcaSpecificationsAfterReturn0 (M := M) 0) 1 true
        (by decide_at_round_zero) (by decide_at_round_zero) (by decide_at_round_zero)
        (by decide_at_round_zero)))
    (roundLoops_at 1
      (RoundLoopStep.retG (P := fourProcesses) (abaAfterRetG0.1 1) 0 (.grade2 true)
        (by decide) (by decide) (by decide))
      (fun j hj => RoundLoopStep.retGIdle (P := fourProcesses) (abaAfterRetG0.1 j) 0 1
        (.grade2 true) (Ne.symm hj)))
    (ABANetworkStep.retGIdle (P := fourProcesses) abaAfterRetG0.2 0 1 (.grade2 true))
    (wccIdle coinInitial (by simp) rfl (by simp [Label.isFail]))
  rw [prodPMF_pure_pure, prodPMF_pure_pure, prodPMF_pure_pure] at h
  exact h

/-- Process `2`'s round-`0` return of `grade2 true`. -/
theorem step_retG₂ :
    (hybrid fourProcesses M).step
      (hybridStateOf gbcaSpecificationsAfterReturn1 abaAfterRetG1 coinInitial) Label.tau
      (PMF.pure (hybridStateOf gbcaSpecificationsAfterReturn2 abaAfterRetG2 coinInitial)) := by
  refine hybrid_hidden fourProcesses (l := Label.retG 0 (2 : Fin 4) (.grade2 true)) (by simp) ?_
  have h := hybridExtended_visible_step (M := M) fourProcesses
    (G := gbcaSpecificationsAfterReturn1) (C := abaAfterRetG1.1) (A := abaAfterRetG1.2)
    (o := coinInitial) (L := Sum.inl (Label.retG 0 (2 : Fin 4) (.grade2 true))) (by simp)
    (gbcaSpecificationFamily_owned fourProcesses rfl rfl
      (GBCA.Step.retGrade2 (P := fourProcesses) (r := 0)
        (gbcaSpecificationsAfterReturn1 (M := M) 0) 2 true
        (by decide_at_round_zero) (by decide_at_round_zero) (by decide_at_round_zero)
        (by decide_at_round_zero)))
    (roundLoops_at 2
      (RoundLoopStep.retG (P := fourProcesses) (abaAfterRetG1.1 2) 0 (.grade2 true)
        (by decide) (by decide) (by decide))
      (fun j hj => RoundLoopStep.retGIdle (P := fourProcesses) (abaAfterRetG1.1 j) 0 2
        (.grade2 true) (Ne.symm hj)))
    (ABANetworkStep.retGIdle (P := fourProcesses) abaAfterRetG1.2 0 2 (.grade2 true))
    (wccIdle coinInitial (by simp) rfl (by simp [Label.isFail]))
  rw [prodPMF_pure_pure, prodPMF_pure_pure, prodPMF_pure_pure] at h
  exact h

/-! ### Steps 11–14: the three coin calls (`callW 0`, hidden), and the silent resolution of the
coin after the second call -/

/-- Process `0` calls the round-`0` coin. The call records the caller, and with one caller the
count equals `f`. Round `0` enters the map of the common coin's family. -/
theorem step_callW₀ :
    (hybrid fourProcesses M).step
      (hybridStateOf gbcaSpecificationsAfterReturn2 abaAfterRetG2 coinInitial) Label.tau
      (PMF.pure (hybridStateOf gbcaSpecificationsAfterReturn2 abaAfterCallW0
        coinAfterRecordingCall0)) := by
  refine hybrid_hidden fourProcesses (l := Label.callW 0 (0 : Fin 4)) (by simp) ?_
  have h := hybridExtended_visible_step (M := M) fourProcesses
    (G := gbcaSpecificationsAfterReturn2) (C := abaAfterRetG2.1) (A := abaAfterRetG2.2)
    (o := coinInitial) (L := Sum.inl (Label.callW 0 (0 : Fin 4))) (by simp)
    (gbcaSpecificationFamily_idle fourProcesses gbcaSpecificationsAfterReturn2 (by simp) rfl
      not_false)
    (roundLoops_at 0
      (RoundLoopStep.callW (P := fourProcesses) (abaAfterRetG2.1 0) 0 (by decide) (by decide)
        (by decide))
      (fun j hj => RoundLoopStep.callWIdle (P := fourProcesses) (abaAfterRetG2.1 j) 0 0
        (Ne.symm hj)))
    (ABANetworkStep.callWIdle (P := fourProcesses) abaAfterRetG2.2 0 0)
    ((System.mapIdle_step_some (coinLabelMap_inl (Label.callW 0 (0 : Fin 4))) _).mpr
      (wccFamily_owned fourProcesses coinInitial rfl
        (WCC.Step.call (P := fourProcesses) (r := 0) (coinInitial 0) 0 (by decide))))
  rw [prodPMF_pure_pure, prodPMF_pure_pure, prodPMF_pure_pure] at h
  exact h

/-- Process `1` calls the round-`0` coin. The call records the caller, and the caller count of
round `0` reaches `2 > f`. -/
theorem step_callW₁ :
    (hybrid fourProcesses M).step
      (hybridStateOf gbcaSpecificationsAfterReturn2 abaAfterCallW0 coinAfterRecordingCall0)
      Label.tau
      (PMF.pure (hybridStateOf gbcaSpecificationsAfterReturn2 abaAfterCallW1
        coinAfterRecordingCall1)) := by
  refine hybrid_hidden fourProcesses (l := Label.callW 0 (1 : Fin 4)) (by simp) ?_
  have h := hybridExtended_visible_step (M := M) fourProcesses
    (G := gbcaSpecificationsAfterReturn2) (C := abaAfterCallW0.1) (A := abaAfterCallW0.2)
    (o := coinAfterRecordingCall0) (L := Sum.inl (Label.callW 0 (1 : Fin 4))) (by simp)
    (gbcaSpecificationFamily_idle fourProcesses gbcaSpecificationsAfterReturn2 (by simp) rfl
      not_false)
    (roundLoops_at 1
      (RoundLoopStep.callW (P := fourProcesses) (abaAfterCallW0.1 1) 0 (by decide) (by decide)
        (by decide))
      (fun j hj => RoundLoopStep.callWIdle (P := fourProcesses) (abaAfterCallW0.1 j) 0 1
        (Ne.symm hj)))
    (ABANetworkStep.callWIdle (P := fourProcesses) abaAfterCallW0.2 0 1)
    ((System.mapIdle_step_some (coinLabelMap_inl (Label.callW 0 (1 : Fin 4))) _).mpr
      (wccFamily_owned fourProcesses coinAfterRecordingCall0 rfl
        (WCC.Step.call (P := fourProcesses) (r := 0) (coinAfterRecordingCall0 0) 1
          (by decide))))
  rw [prodPMF_pure_pure, prodPMF_pure_pure, prodPMF_pure_pure] at h
  exact h

/-- The distribution of the common coin's family that the resolution draws: the outcome of
`wccPMF` is written to the round-`0` coin's `val`. -/
noncomputable def resolvedCoinDistribution : PMF CoinFamilyState :=
  (fourProcesses.wccPMF.map
    (fun o => { coinAfterRecordingCall1 0 with val := o.toCoinValue })).map
      (coinAfterRecordingCall1.setInstanceState 0)

/-- The successor distribution of the coin's resolution: the specification family, the round
loops and the ABA network do not move, and the common coin's family resolves round `0`. -/
noncomputable def resolvedHybridDistribution : PMF (HybridState fourProcesses M) :=
  prodPMF (PMF.pure gbcaSpecificationsAfterReturn2) (prodPMF (PMF.pure abaAfterCallW1.1)
    (prodPMF (PMF.pure abaAfterCallW1.2) resolvedCoinDistribution))

/-- The round-`0` coin resolves. Its caller count `2` exceeds `f` at `val = ⊥`, so the silent
resolution draws `val` from `wccPMF`: the run's single probabilistic step. The common coin's
family takes the transition at round `0`, a round of its map since the first coin call, and the
other three components do not move. -/
theorem step_resolve :
    (hybrid fourProcesses M).step
      (hybridStateOf gbcaSpecificationsAfterReturn2 abaAfterCallW1 coinAfterRecordingCall1)
      Label.tau resolvedHybridDistribution := by
  refine hybrid_visible fourProcesses (by simp) ?_
  exact hybridExtended_tau_coin (M := M) fourProcesses
    (by exact InstanceFamilyState.mem_keys_setInstanceState_self _ _ _)
    (WCC.Step.resolve (P := fourProcesses) (r := 0) (coinAfterRecordingCall1 0) (by decide)
      (by simp only [WCC.SpecState.threshold]; decide))

omit [DecidableEq M] in
/-- The draw takes the outcome `bit true`, the outcome that agrees with the bound bit, with mass
`ε = 1/2 > 0`. This is the run's single factor `ε`; every other step is a Dirac, so the run has
positive probability. -/
theorem step_resolve_mass :
    resolvedHybridDistribution (M := M)
      (hybridStateOf gbcaSpecificationsAfterReturn2 abaAfterCallW1 coinAfterResolution) =
    fourProcesses.ε := by
  have hup : Function.Injective (coinAfterRecordingCall1.setInstanceState 0) := by
    intro a b h
    have h0 := congrArg (fun g : CoinFamilyState => g 0) h
    simpa using h0
  have hg : Function.Injective
      (fun o : CoinOutcome =>
        ({ coinAfterRecordingCall1 0 with val := o.toCoinValue } : WCC.SpecState 4)) :=
    fun _ _ h => CoinOutcome.toCoinValue_injective (congrArg (·.val) h)
  change prodPMF (PMF.pure gbcaSpecificationsAfterReturn2) (prodPMF (PMF.pure abaAfterCallW1.1)
    (prodPMF (PMF.pure abaAfterCallW1.2) resolvedCoinDistribution))
      (gbcaSpecificationsAfterReturn2 (M := M), abaAfterCallW1.1, abaAfterCallW1.2,
        coinAfterResolution) = fourProcesses.ε
  rw [prodPMF_pure_left_apply, prodPMF_pure_left_apply, prodPMF_pure_left_apply]
  unfold resolvedCoinDistribution
  rw [show coinAfterResolution
      = coinAfterRecordingCall1.setInstanceState 0
        { coinAfterRecordingCall1 0 with val := CoinValue.bit true } from rfl,
    map_apply_inj hup,
    show ({ coinAfterRecordingCall1 0 with val := CoinValue.bit true } : WCC.SpecState 4)
      = (fun o => { coinAfterRecordingCall1 0 with val := o.toCoinValue })
        (CoinOutcome.bit true) from rfl,
    map_apply_inj hg, Parameters.wccPMF_apply_bit]

/-- Process `2` calls the round-`0` coin. The call records the caller; `val` is resolved, so the
resolution is not enabled. -/
theorem step_callW₂ :
    (hybrid fourProcesses M).step
      (hybridStateOf gbcaSpecificationsAfterReturn2 abaAfterCallW1 coinAfterResolution) Label.tau
      (PMF.pure (hybridStateOf gbcaSpecificationsAfterReturn2 abaAfterCallW2
        coinAfterRecordingCall2)) := by
  refine hybrid_hidden fourProcesses (l := Label.callW 0 (2 : Fin 4)) (by simp) ?_
  have h := hybridExtended_visible_step (M := M) fourProcesses
    (G := gbcaSpecificationsAfterReturn2) (C := abaAfterCallW1.1) (A := abaAfterCallW1.2)
    (o := coinAfterResolution) (L := Sum.inl (Label.callW 0 (2 : Fin 4))) (by simp)
    (gbcaSpecificationFamily_idle fourProcesses gbcaSpecificationsAfterReturn2 (by simp) rfl
      not_false)
    (roundLoops_at 2
      (RoundLoopStep.callW (P := fourProcesses) (abaAfterCallW1.1 2) 0 (by decide) (by decide)
        (by decide))
      (fun j hj => RoundLoopStep.callWIdle (P := fourProcesses) (abaAfterCallW1.1 j) 0 2
        (Ne.symm hj)))
    (ABANetworkStep.callWIdle (P := fourProcesses) abaAfterCallW1.2 0 2)
    ((System.mapIdle_step_some (coinLabelMap_inl (Label.callW 0 (2 : Fin 4))) _).mpr
      (wccFamily_owned fourProcesses coinAfterResolution rfl
        (WCC.Step.call (P := fourProcesses) (r := 0) (coinAfterResolution 0) 2 (by decide))))
  rw [prodPMF_pure_pure, prodPMF_pure_pure, prodPMF_pure_pure] at h
  exact h

/-! ### Steps 15–20: the three coin returns (`retW 0`, hidden), each followed by the DECIDED send
of the grade-2 round (`decidedSend`, a synchronisation of the sending round loop with the
network) -/

/-- Process `0` receives the coin. Its round closed with the grade `grade2 true`, so it enters
`toSendDecided` at round `1` with the grade kept. -/
theorem step_retW₀ :
    (hybrid fourProcesses M).step
      (hybridStateOf gbcaSpecificationsAfterReturn2 abaAfterCallW2 coinAfterRecordingCall2)
      Label.tau
      (PMF.pure (hybridStateOf gbcaSpecificationsAfterReturn2 abaAfterRetW0
        coinAfterReturn0)) := by
  refine hybrid_hidden fourProcesses (l := Label.retW 0 (0 : Fin 4) true) (by simp) ?_
  have h := hybridExtended_visible_step (M := M) fourProcesses
    (G := gbcaSpecificationsAfterReturn2) (C := abaAfterCallW2.1) (A := abaAfterCallW2.2)
    (o := coinAfterRecordingCall2) (L := Sum.inl (Label.retW 0 (0 : Fin 4) true)) (by simp)
    (gbcaSpecificationFamily_idle fourProcesses gbcaSpecificationsAfterReturn2 (by simp) rfl
      not_false)
    (roundLoops_at 0
      (RoundLoopStep.retW (P := fourProcesses) (abaAfterCallW2.1 0) 0 true (by decide)
        (by decide) (by decide))
      (fun j hj => RoundLoopStep.retWIdle (P := fourProcesses) (abaAfterCallW2.1 j) 0 0 true
        (Ne.symm hj)))
    (ABANetworkStep.retWIdle (P := fourProcesses) abaAfterCallW2.2 0 0 true)
    ((System.mapIdle_step_some (coinLabelMap_inl (Label.retW 0 (0 : Fin 4) true)) _).mpr
      (wccFamily_owned fourProcesses coinAfterRecordingCall2 rfl
        (WCC.Step.ret (P := fourProcesses) (r := 0) (coinAfterRecordingCall2 0) 0 true
          (Or.inr (by decide)) (by decide))))
  rw [prodPMF_pure_pure, prodPMF_pure_pure, prodPMF_pure_pure] at h
  exact h

/-- Process `0` sends `⟨DECIDED, true⟩`: its round loop records `true` among its own DECIDED
sends and enters `toCallG` at round `1`, and the network records `true` in process `0`'s DECIDED
set. -/
theorem step_decidedSend₀ :
    (hybrid fourProcesses M).step
      (hybridStateOf gbcaSpecificationsAfterReturn2 abaAfterRetW0 coinAfterReturn0) Label.tau
      (PMF.pure (hybridStateOf gbcaSpecificationsAfterReturn2 abaAfterDecidedSend0
        coinAfterReturn0)) := by
  refine hybrid_synchronisation fourProcesses (e := .decidedSend (0 : Fin 4) true) ?_
  have h := hybridExtended_visible_step (M := M) fourProcesses
    (G := gbcaSpecificationsAfterReturn2) (C := abaAfterRetW0.1) (A := abaAfterRetW0.2)
    (o := coinAfterReturn0) (L := Sum.inr (.decidedSend (0 : Fin 4) true)) (by simp)
    (gbcaSpecificationFamily_idle fourProcesses gbcaSpecificationsAfterReturn2 (by simp) rfl
      not_false)
    (roundLoops_at 0
      (RoundLoopStep.decidedSend (P := fourProcesses) (abaAfterRetW0.1 0) true (by decide)
        (by decide) (by decide))
      (fun j hj => RoundLoopStep.decidedSendIdle (P := fourProcesses) (abaAfterRetW0.1 j) 0 true
        (Ne.symm hj)))
    (ABANetworkStep.decidedSend (P := fourProcesses) abaAfterRetW0.2 0 true)
    ((System.mapIdle_step_none (coinLabelMap_decidedSend (0 : Fin 4) true) _).mpr rfl)
  rw [prodPMF_pure_pure, prodPMF_pure_pure, prodPMF_pure_pure] at h
  exact h

/-- Process `1` receives the coin and enters `toSendDecided`. -/
theorem step_retW₁ :
    (hybrid fourProcesses M).step
      (hybridStateOf gbcaSpecificationsAfterReturn2 abaAfterDecidedSend0 coinAfterReturn0)
      Label.tau
      (PMF.pure (hybridStateOf gbcaSpecificationsAfterReturn2 abaAfterRetW1
        coinAfterReturn1)) := by
  refine hybrid_hidden fourProcesses (l := Label.retW 0 (1 : Fin 4) true) (by simp) ?_
  have h := hybridExtended_visible_step (M := M) fourProcesses
    (G := gbcaSpecificationsAfterReturn2) (C := abaAfterDecidedSend0.1)
    (A := abaAfterDecidedSend0.2) (o := coinAfterReturn0)
    (L := Sum.inl (Label.retW 0 (1 : Fin 4) true)) (by simp)
    (gbcaSpecificationFamily_idle fourProcesses gbcaSpecificationsAfterReturn2 (by simp) rfl
      not_false)
    (roundLoops_at 1
      (RoundLoopStep.retW (P := fourProcesses) (abaAfterDecidedSend0.1 1) 0 true (by decide)
        (by decide) (by decide))
      (fun j hj => RoundLoopStep.retWIdle (P := fourProcesses) (abaAfterDecidedSend0.1 j) 0 1
        true (Ne.symm hj)))
    (ABANetworkStep.retWIdle (P := fourProcesses) abaAfterDecidedSend0.2 0 1 true)
    ((System.mapIdle_step_some (coinLabelMap_inl (Label.retW 0 (1 : Fin 4) true)) _).mpr
      (wccFamily_owned fourProcesses coinAfterReturn0 rfl
        (WCC.Step.ret (P := fourProcesses) (r := 0) (coinAfterReturn0 0) 1 true
          (Or.inr (by decide)) (by decide))))
  rw [prodPMF_pure_pure, prodPMF_pure_pure, prodPMF_pure_pure] at h
  exact h

/-- Process `1` sends `⟨DECIDED, true⟩`. -/
theorem step_decidedSend₁ :
    (hybrid fourProcesses M).step
      (hybridStateOf gbcaSpecificationsAfterReturn2 abaAfterRetW1 coinAfterReturn1) Label.tau
      (PMF.pure (hybridStateOf gbcaSpecificationsAfterReturn2 abaAfterDecidedSend1
        coinAfterReturn1)) := by
  refine hybrid_synchronisation fourProcesses (e := .decidedSend (1 : Fin 4) true) ?_
  have h := hybridExtended_visible_step (M := M) fourProcesses
    (G := gbcaSpecificationsAfterReturn2) (C := abaAfterRetW1.1) (A := abaAfterRetW1.2)
    (o := coinAfterReturn1) (L := Sum.inr (.decidedSend (1 : Fin 4) true)) (by simp)
    (gbcaSpecificationFamily_idle fourProcesses gbcaSpecificationsAfterReturn2 (by simp) rfl
      not_false)
    (roundLoops_at 1
      (RoundLoopStep.decidedSend (P := fourProcesses) (abaAfterRetW1.1 1) true (by decide)
        (by decide) (by decide))
      (fun j hj => RoundLoopStep.decidedSendIdle (P := fourProcesses) (abaAfterRetW1.1 j) 1 true
        (Ne.symm hj)))
    (ABANetworkStep.decidedSend (P := fourProcesses) abaAfterRetW1.2 1 true)
    ((System.mapIdle_step_none (coinLabelMap_decidedSend (1 : Fin 4) true) _).mpr rfl)
  rw [prodPMF_pure_pure, prodPMF_pure_pure, prodPMF_pure_pure] at h
  exact h

/-- Process `2` receives the coin and enters `toSendDecided`. -/
theorem step_retW₂ :
    (hybrid fourProcesses M).step
      (hybridStateOf gbcaSpecificationsAfterReturn2 abaAfterDecidedSend1 coinAfterReturn1)
      Label.tau
      (PMF.pure (hybridStateOf gbcaSpecificationsAfterReturn2 abaAfterRetW2
        coinAfterReturn2)) := by
  refine hybrid_hidden fourProcesses (l := Label.retW 0 (2 : Fin 4) true) (by simp) ?_
  have h := hybridExtended_visible_step (M := M) fourProcesses
    (G := gbcaSpecificationsAfterReturn2) (C := abaAfterDecidedSend1.1)
    (A := abaAfterDecidedSend1.2) (o := coinAfterReturn1)
    (L := Sum.inl (Label.retW 0 (2 : Fin 4) true)) (by simp)
    (gbcaSpecificationFamily_idle fourProcesses gbcaSpecificationsAfterReturn2 (by simp) rfl
      not_false)
    (roundLoops_at 2
      (RoundLoopStep.retW (P := fourProcesses) (abaAfterDecidedSend1.1 2) 0 true (by decide)
        (by decide) (by decide))
      (fun j hj => RoundLoopStep.retWIdle (P := fourProcesses) (abaAfterDecidedSend1.1 j) 0 2
        true (Ne.symm hj)))
    (ABANetworkStep.retWIdle (P := fourProcesses) abaAfterDecidedSend1.2 0 2 true)
    ((System.mapIdle_step_some (coinLabelMap_inl (Label.retW 0 (2 : Fin 4) true)) _).mpr
      (wccFamily_owned fourProcesses coinAfterReturn1 rfl
        (WCC.Step.ret (P := fourProcesses) (r := 0) (coinAfterReturn1 0) 2 true
          (Or.inr (by decide)) (by decide))))
  rw [prodPMF_pure_pure, prodPMF_pure_pure, prodPMF_pure_pure] at h
  exact h

/-- Process `2` sends `⟨DECIDED, true⟩`. Three distinct senders have sent `⟨DECIDED, true⟩`. -/
theorem step_decidedSend₂ :
    (hybrid fourProcesses M).step
      (hybridStateOf gbcaSpecificationsAfterReturn2 abaAfterRetW2 coinAfterReturn2) Label.tau
      (PMF.pure (hybridStateOf gbcaSpecificationsAfterReturn2 abaAfterDecidedSend2
        coinAfterReturn2)) := by
  refine hybrid_synchronisation fourProcesses (e := .decidedSend (2 : Fin 4) true) ?_
  have h := hybridExtended_visible_step (M := M) fourProcesses
    (G := gbcaSpecificationsAfterReturn2) (C := abaAfterRetW2.1) (A := abaAfterRetW2.2)
    (o := coinAfterReturn2) (L := Sum.inr (.decidedSend (2 : Fin 4) true)) (by simp)
    (gbcaSpecificationFamily_idle fourProcesses gbcaSpecificationsAfterReturn2 (by simp) rfl
      not_false)
    (roundLoops_at 2
      (RoundLoopStep.decidedSend (P := fourProcesses) (abaAfterRetW2.1 2) true (by decide)
        (by decide) (by decide))
      (fun j hj => RoundLoopStep.decidedSendIdle (P := fourProcesses) (abaAfterRetW2.1 j) 2 true
        (Ne.symm hj)))
    (ABANetworkStep.decidedSend (P := fourProcesses) abaAfterRetW2.2 2 true)
    ((System.mapIdle_step_none (coinLabelMap_decidedSend (2 : Fin 4) true) _).mpr rfl)
  rw [prodPMF_pure_pure, prodPMF_pure_pure, prodPMF_pure_pure] at h
  exact h

/-! ### Steps 21–23: the adversary delivers the three `⟨DECIDED, true⟩` messages to process `0`
(`decidedDeliver`, a synchronisation of the receiving round loop with the network) -/

/-- Delivery of process `0`'s own `⟨DECIDED, true⟩`. -/
theorem step_deliver₀ :
    (hybrid fourProcesses M).step
      (hybridStateOf gbcaSpecificationsAfterReturn2 abaAfterDecidedSend2 coinAfterReturn2)
      Label.tau
      (PMF.pure (hybridStateOf gbcaSpecificationsAfterReturn2 abaAfterDeliver0
        coinAfterReturn2)) := by
  refine hybrid_synchronisation fourProcesses
    (e := .decidedDeliver (0 : Fin 4) (0 : Fin 4) true) ?_
  have h := hybridExtended_visible_step (M := M) fourProcesses
    (G := gbcaSpecificationsAfterReturn2) (C := abaAfterDecidedSend2.1)
    (A := abaAfterDecidedSend2.2) (o := coinAfterReturn2)
    (L := Sum.inr (.decidedDeliver (0 : Fin 4) (0 : Fin 4) true)) (by simp)
    (gbcaSpecificationFamily_idle fourProcesses gbcaSpecificationsAfterReturn2 (by simp) rfl
      not_false)
    (roundLoops_at 0
      (RoundLoopStep.decidedDeliverReceive (P := fourProcesses) (abaAfterDecidedSend2.1 0) 0
        true (by decide) (by decide))
      (fun j hj => RoundLoopStep.decidedDeliverIdle (P := fourProcesses)
        (abaAfterDecidedSend2.1 j) 0 0 true (Ne.symm hj)))
    (ABANetworkStep.decidedDeliver (P := fourProcesses) abaAfterDecidedSend2.2 0 0 true
      (by decide))
    ((System.mapIdle_step_none (coinLabelMap_decidedDeliver (0 : Fin 4) (0 : Fin 4) true) _).mpr
      rfl)
  rw [prodPMF_pure_pure, prodPMF_pure_pure, prodPMF_pure_pure] at h
  exact h

/-- Delivery of process `1`'s `⟨DECIDED, true⟩` to process `0`. -/
theorem step_deliver₁ :
    (hybrid fourProcesses M).step
      (hybridStateOf gbcaSpecificationsAfterReturn2 abaAfterDeliver0 coinAfterReturn2) Label.tau
      (PMF.pure (hybridStateOf gbcaSpecificationsAfterReturn2 abaAfterDeliver1
        coinAfterReturn2)) := by
  refine hybrid_synchronisation fourProcesses
    (e := .decidedDeliver (0 : Fin 4) (1 : Fin 4) true) ?_
  have h := hybridExtended_visible_step (M := M) fourProcesses
    (G := gbcaSpecificationsAfterReturn2) (C := abaAfterDeliver0.1) (A := abaAfterDeliver0.2)
    (o := coinAfterReturn2) (L := Sum.inr (.decidedDeliver (0 : Fin 4) (1 : Fin 4) true))
    (by simp)
    (gbcaSpecificationFamily_idle fourProcesses gbcaSpecificationsAfterReturn2 (by simp) rfl
      not_false)
    (roundLoops_at 0
      (RoundLoopStep.decidedDeliverReceive (P := fourProcesses) (abaAfterDeliver0.1 0) 1 true
        (by decide) (by decide))
      (fun j hj => RoundLoopStep.decidedDeliverIdle (P := fourProcesses) (abaAfterDeliver0.1 j)
        0 1 true (Ne.symm hj)))
    (ABANetworkStep.decidedDeliver (P := fourProcesses) abaAfterDeliver0.2 0 1 true (by decide))
    ((System.mapIdle_step_none (coinLabelMap_decidedDeliver (0 : Fin 4) (1 : Fin 4) true) _).mpr
      rfl)
  rw [prodPMF_pure_pure, prodPMF_pure_pure, prodPMF_pure_pure] at h
  exact h

/-- Delivery of process `2`'s `⟨DECIDED, true⟩` to process `0`. Process `0` holds the message
from `n − f = 3` distinct senders. -/
theorem step_deliver₂ :
    (hybrid fourProcesses M).step
      (hybridStateOf gbcaSpecificationsAfterReturn2 abaAfterDeliver1 coinAfterReturn2) Label.tau
      (PMF.pure (hybridStateOf gbcaSpecificationsAfterReturn2 abaAfterDeliver2
        coinAfterReturn2)) := by
  refine hybrid_synchronisation fourProcesses
    (e := .decidedDeliver (0 : Fin 4) (2 : Fin 4) true) ?_
  have h := hybridExtended_visible_step (M := M) fourProcesses
    (G := gbcaSpecificationsAfterReturn2) (C := abaAfterDeliver1.1) (A := abaAfterDeliver1.2)
    (o := coinAfterReturn2) (L := Sum.inr (.decidedDeliver (0 : Fin 4) (2 : Fin 4) true))
    (by simp)
    (gbcaSpecificationFamily_idle fourProcesses gbcaSpecificationsAfterReturn2 (by simp) rfl
      not_false)
    (roundLoops_at 0
      (RoundLoopStep.decidedDeliverReceive (P := fourProcesses) (abaAfterDeliver1.1 0) 2 true
        (by decide) (by decide))
      (fun j hj => RoundLoopStep.decidedDeliverIdle (P := fourProcesses) (abaAfterDeliver1.1 j)
        0 2 true (Ne.symm hj)))
    (ABANetworkStep.decidedDeliver (P := fourProcesses) abaAfterDeliver1.2 0 2 true (by decide))
    ((System.mapIdle_step_none (coinLabelMap_decidedDeliver (0 : Fin 4) (2 : Fin 4) true) _).mpr
      rfl)
  rw [prodPMF_pure_pure, prodPMF_pure_pure, prodPMF_pure_pure] at h
  exact h

/-! ### Step 24: the decision (`retABA 0 true`, visible) -/

/-- Process `0` returns `true`. Its round loop holds `⟨DECIDED, true⟩` from `n − f = 3` distinct
senders and has recorded its own DECIDED send of `true`, and the ABA network takes the return on
its idle transition. The run of 24 steps from the initial state, every step a Dirac but the
coin's resolution, whose chosen outcome has mass `ε`, has positive probability and ends in this
`retABA`. -/
theorem step_retABA :
    (hybrid fourProcesses M).step
      (hybridStateOf gbcaSpecificationsAfterReturn2 abaAfterDeliver2 coinAfterReturn2)
      (Label.retABA (0 : Fin 4) true)
      (PMF.pure (hybridStateOf gbcaSpecificationsAfterReturn2 abaAfterRetABA
        coinAfterReturn2)) := by
  refine hybrid_visible fourProcesses (by simp) ?_
  have h := hybridExtended_visible_step (M := M) fourProcesses
    (G := gbcaSpecificationsAfterReturn2) (C := abaAfterDeliver2.1) (A := abaAfterDeliver2.2)
    (o := coinAfterReturn2) (L := Sum.inl (Label.retABA (0 : Fin 4) true)) (by simp)
    (gbcaSpecificationFamily_idle fourProcesses gbcaSpecificationsAfterReturn2 (by simp) rfl
      not_false)
    (roundLoops_at 0
      (RoundLoopStep.ret (P := fourProcesses) (abaAfterDeliver2.1 0) true (by decide)
        (by decide) (by decide) (by decide))
      (fun j hj => RoundLoopStep.retABAIdle (P := fourProcesses) (abaAfterDeliver2.1 j) 0 true
        (Ne.symm hj)))
    (ABANetworkStep.retABAIdle (P := fourProcesses) abaAfterDeliver2.2 0 true)
    (wccIdle coinAfterReturn2 (by simp) rfl (by simp [Label.isFail]))
  rw [prodPMF_pure_pure, prodPMF_pure_pure, prodPMF_pure_pure] at h
  exact h

/-! ### The announcement of round `0`'s bound bit -/

/-- After the first return, round `0` announces its bound bit `true`: `boundG 0 true` is hidden,
and the transition is a self-loop of the four components. The guard `false ∈ excluded` of the
round-`0` specification holds from `step_bindUnset` on, and the announced bit is the bit of the
returns (D29). -/
theorem step_boundG :
    (hybrid fourProcesses M).step
      (hybridStateOf gbcaSpecificationsAfterReturn0 abaAfterRetG0 coinInitial) Label.tau
      (PMF.pure (hybridStateOf gbcaSpecificationsAfterReturn0 abaAfterRetG0 coinInitial)) :=
  hybrid_hidden fourProcesses (l := Label.boundG 0 true) (by simp)
    (hybridExtended_boundG (M := M) fourProcesses (G := gbcaSpecificationsAfterReturn0)
      abaAfterRetG0.1 abaAfterRetG0.2 coinInitial (r := 0) (by decide_at_round_zero))

/-! ### The broadcast `fail 0`, which every component takes -/

/-- Corruption of process `0` at the initial state. The visible label `fail 0` synchronises every
component: the specification family and the common coin's family take the broadcast at every
round, the ABA network takes its own `fail` transition, which carries the guards, the round loop
of process `0` replaces its own program (D23), and the other three round loops idle (D1). -/
theorem step_fail :
    (hybrid fourProcesses M).step (hybridStateOf gbcaSpecificationsInitial abaInitial coinInitial)
      (Label.fail (0 : Fin 4))
      (PMF.pure (hybridStateOf gbcaSpecificationsAfterFail abaAfterFail coinAfterFail)) := by
  refine hybrid_visible fourProcesses (by simp) ?_
  have h := hybridExtended_visible_step (M := M) fourProcesses
    (G := gbcaSpecificationsInitial) (C := abaInitial.1) (A := abaInitial.2) (o := coinInitial)
    (L := Sum.inl (Label.fail (0 : Fin 4))) (by simp)
    (gbcaSpecificationFamily_fail fourProcesses gbcaSpecificationsInitial 0)
    (roundLoops_at 0 (RoundLoopStep.failSelf (P := fourProcesses) (abaInitial.1 0) rfl)
      (fun j hj => RoundLoopStep.failIdle (P := fourProcesses) (abaInitial.1 j) 0 (Ne.symm hj)))
    (ABANetworkStep.fail (P := fourProcesses) abaInitial.2 0 (by decide) (by decide))
    ((System.mapIdle_step_some (coinLabelMap_inl (Label.fail (0 : Fin 4))) _).mpr
      (wccFamily_fail fourProcesses coinInitial 0))
  rw [prodPMF_pure_pure, prodPMF_pure_pure, prodPMF_pure_pure] at h
  exact h

end NonVacuity

end ABA
end PLTS
