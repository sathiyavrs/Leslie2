/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sathiya / Claude
-/

import Leslie2Protocols.ABA.Composition.Hybrid
import Leslie2Protocols.ABA.Composition.ABAState

/-!
# Non-vacuity witnesses for the protocol-shaped specification

Machine-checked witnesses that the composed system `hybrid P M` can execute
a nontrivial prefix: the core simulation `ABA.hybridRefinesSpecification` about it is not
vacuously true through an immediate deadlock.

We fix the small parameter set `fourProcesses` (`n = 4`, `f = 1`, `ε = 1/2`) and exhibit a
concrete **24-step run of `hybrid fourProcesses M` that reaches a genuine `retABA`** — a
complete decision — starting from its initial state. The run is exhibited for every type `M` of
round messages: no step of it carries a round message.

* `step_callABA₀/₁/₂` — three external input calls (`callABA`, *visible*: the addressed round
  loop takes its `input` transition, the other three idle, and the round specifications, the ABA
  network and the common coin idle);
* `step_callG₀/₁/₂` — three graded-agreement calls (`callG 0`, *hidden* to `τ`:
  the caller's round loop hands over its estimate and the round-`0`
  specification takes its owned `call`);
* `step_bindUnset` — the round-`0` specification's `bindUnset` internal
  transition excluding the bit `false` (a family `τ`, `n − f` quorum met at
  `n = 4, f = 1` by the three callers of `true`);
* `step_retG₀/₁/₂` — the three graded-agreement grade-2 returns (`retG 0`, *hidden*), the
  first setting the round's grade to 2. Each return announces the bound bit `true`. Its
  complement is the bit that `step_bindUnset` excluded, which is exactly the return's guard, so
  the ghost output leaves the run intact;
* `step_callW₀`, `step_callW₁` — the coin calls of processes `0` and `1` (`callW 0`, *hidden*),
  each recording its caller: the second carries the caller count to `2 > f`;
* `step_resolve` + `step_resolve_mass` — the coin's silent resolution (a coin `τ`) and the run's
  **single probabilistic step**: at `val = ⊥` with the caller count above `f`, the resolution
  draws `val` from `wccPMF`. The successor lands on the `bit true` branch — the outcome agreeing
  with the bound value — with mass exactly `ε = 1/2 > 0`;
* `step_callW₂` — process `2`'s coin call, recording its caller at a resolved `val`;
* `step_retW₀/₁/₂` — the three coin returns (`retW 0`, *hidden*): each process takes the round
  advance, keeps the grade `grade2 true` and enters `toSendDecided` at round `1`;
* `step_decidedSend₀/₁/₂` — the DECIDED send of each process after its coin return (a
  synchronised step on `decidedSend`, *hidden*): the round loop clears the grade and enters
  `toCallG`, and the network sets `true` in the sender's DECIDED set, giving three distinct
  DECIDED-true senders;
* `step_deliver₀/₁/₂` — the adversary delivers all three DECIDED messages to process `0`
  (a synchronised step on `decidedDeliver`, *hidden*), meeting the `n − f = 3` return quorum;
* `step_retABA` — process `0` fires `retABA 0 true`: the decision.

Plus `step_fail` — a `fail` broadcast synchronising all four components.

Because every step but the resolution is a Dirac and the chosen branch of
the resolution has mass `ε > 0`, the whole path is a positive-probability execution: a
product of Diracs times one `ε` factor. Every guard on these closed numeric
states discharges by `decide`/`rfl`; the Dirac successor distributions collapse
through `prodPMF_pure_pure` and `PMF.pure_map`, and the resolution's branch
mass through `prodPMF_pure_left_apply` and `map_apply_inj`.

The ABA components are named as `ABA/Composition/ABAState.lean` groups them: a state of the run
is a triple — the round specifications, one `ABAState` holding the round loops beside the ABA
network, and the common coin — assembled into the four-component state by `hybridStateOf`.

Each component carries one name per state of the run and one name per update. The states are
`abaInitial`, `gbcaSpecificationsInitial` and `coinInitial`, and then, for each component, the state
the step named in the list above leaves behind: `abaAfterInput0`, `abaAfterCallG0`, `abaAfterRetG0`,
`abaAfterCallW0`, `abaAfterRoundStep0`, `abaAfterDecidedSend0`, `abaAfterDeliver0`, `abaAfterRetABA`
and `abaAfterFail`;
`gbcaSpecificationsAfterCall0`, `gbcaSpecificationsAfterBindUnset`, `gbcaSpecificationsAfterReturn0`
and `gbcaSpecificationsAfterFail`; `coinAfterRecordingCall0`, `coinAfterRecordingCall1`,
`coinAfterResolution`, `coinAfterRecordingCall2`, `coinAfterReturn0` and `coinAfterFail`. The
updates are `abaInput`, `abaCallG`, `abaRetG`, `abaCallW` in the ABA component,
`gbcaSpecificationCall` and `gbcaSpecificationRetGrade2` on the round specifications, and
`coinCall`, `coinResolve` and `coinReturn` on the common coin. Reading a state name gives the step
it follows, and reading an update name gives the transition it belongs to. -/

namespace PLTS
namespace ABA

open Implementation hiding NetworkEvent ExtendedLabel
open Composition

/-- A concrete parameter set: four processes, corruption budget one, and a
never-failing `ε = 1/2` coin, so that each bit outcome carries positive mass
(`ε = 1/2`) and the witnessed resolution can take the `bit true` branch.
`2 * ε + δ ≤ 1` holds with equality (`2 * (1/2) + 0 = 1`); the adversarial `⊤`
outcome and the failure outcome then both have mass `0`. -/
noncomputable abbrev fourProcesses : Parameters := ⟨4, 1, by omega, 1 / 2, 0, by
  rw [add_zero, one_div, ENNReal.mul_inv_cancel] <;> simp, by simp⟩

namespace NonVacuity

/-! `M` is the type of the messages a graded-agreement round exchanges. -/

variable {M : Type} [DecidableEq M]

/-! ### Assembling and moving the four components -/

/-- A state of the protocol-shaped specification, assembled from the round specifications, the ABA
component and the common coin. -/
def hybridStateOf (G : ℕ → GBCA.SpecState 4) (s : ABAState fourProcesses)
  (o : ℕ → WCC.SpecState 4) :
    HybridState fourProcesses := (G, s.1, s.2, o)

/-- The round loops on a label one of them owns: the addressed loop takes its
transition, the others remain unchanged, and the group's successor is the pointwise
update. -/
theorem roundLoops_at {C : ∀ _ : Fin 4, RoundLoopVariables 4} (id : Fin 4) {L : ExtendedLabel 4 M}
    {c' : RoundLoopVariables 4} (hown : RoundLoopStep fourProcesses id (C id) L (PMF.pure c'))
    (hidle : ∀ j, j ≠ id → RoundLoopStep fourProcesses j (C j) L (PMF.pure (C j))) (i : Fin 4) :
    RoundLoopStep fourProcesses i (C i) L (PMF.pure (Function.update C id c' i)) := by
  by_cases h : i = id
  · subst h; rw [Function.update_self]; exact hown
  · rw [Function.update_of_ne h]; exact hidle i h

/-- The common coin on a label one of its rounds owns, at a transition whose successor
need not be a point mass: the family's successor is the round's, pushed forward
along the update at that round. -/
theorem wccFamilyStep (o : ℕ → WCC.SpecState 4) {l : Label 4} {r : ℕ}
    {μ : PMF (WCC.SpecState 4)} (hr : Label.wccRound l = some r)
    (h : WCC.Step fourProcesses r (o r) l μ) :
    (WCC.specFamily fourProcesses).step o l (μ.map (Function.update o r)) := by
  rw [WCC.specFamily, System.family_step_iff]
  exact Or.inr (Or.inl ⟨r, hr, μ, h, rfl⟩)

/-- The common coin's idle transition on a shared label that is neither `τ`, nor one
of its own calls or returns, nor `fail`. -/
theorem wccIdle (o : ℕ → WCC.SpecState 4) {l : Label 4} (hl : l ≠ Label.tau)
    (hr : Label.wccRound l = none) (hf : ¬ Label.isFail l) :
    (coinOverRoundAlphabet fourProcesses M).step o (Sum.inl l) (PMF.pure o) :=
  (System.mapIdle_step_some (coinLabelMap_inl l) (PMF.pure o)).mpr
    (wccFamily_idle fourProcesses o hl hr hf)

/-! ### Named states of the run -/

/-- The round specifications: every round initial. -/
def gbcaSpecificationsInitial : ℕ → GBCA.SpecState 4 := fun _ => GBCA.SpecState.initial 4

/-- The common coin: every round initial. -/
def coinInitial : ℕ → WCC.SpecState 4 := fun _ => WCC.SpecState.initial 4

/-- The ABA state: every round loop idle, nothing multicast, nobody corrupted. -/
noncomputable def abaInitial : ABAState fourProcesses := ABAState.initial fourProcesses

/-- The ABA update of a `callABA id true` input: enter round `0`, ready to call the graded
agreement. -/
noncomputable def abaInput (id : Fin 4) (s : ABAState fourProcesses) : ABAState fourProcesses :=
  s.setProcessVariables id { s.processes id with
    input := some true, estimate := some true, round := 0, phase := .toCallG }

/-- The ABA update of a `callG r id` emit: advance to `awaitG`. -/
noncomputable def abaCallG (id : Fin 4) (s : ABAState fourProcesses) : ABAState fourProcesses :=
  s.setProcessVariables id { s.processes id with phase := .awaitG }

/-- The ABA update of a round-`0` graded-agreement `A true` return: adopt the estimate, record the
grade, head for the coin. -/
noncomputable def abaRetG (id : Fin 4) (s : ABAState fourProcesses) : ABAState fourProcesses :=
  s.setProcessVariables id { s.processes id with
    estimate := some true, lastGrade := some (.grade2 true), phase := .toCallW }

/-- The ABA update of a `callW r id` emit: advance to `awaitW`. -/
noncomputable def abaCallW (id : Fin 4) (s : ABAState fourProcesses) : ABAState fourProcesses :=
  s.setProcessVariables id { s.processes id with phase := .awaitW }

/-- The round-`0` specification update of a `call id true`: record the input. -/
def gbcaSpecificationCall (id : Fin 4) (s : ℕ → GBCA.SpecState 4) : ℕ → GBCA.SpecState 4 :=
  Function.update s 0 { s 0 with call := Function.update (s 0).call id (some true) }

/-- The round-`0` specification update of an `A true` return by `id`: set the grade to 2 and record
the return. -/
def gbcaSpecificationRetGrade2 (id : Fin 4) (s : ℕ → GBCA.SpecState 4) : ℕ → GBCA.SpecState 4 :=
  Function.update s 0 { s 0 with grade := some true, ret := Function.update (s 0).ret id true }

/-- The round-`0` coin update of a recording call by `id`: record `id` as a
caller. -/
def coinCall (id : Fin 4) (s : ℕ → WCC.SpecState 4) : ℕ → WCC.SpecState 4 :=
  Function.update s 0 ((s 0).record id)

/-- The round-`0` coin update of the coin's resolution whose draw lands on `v`: write `v`. -/
def coinResolve (v : CoinValue) (s : ℕ → WCC.SpecState 4) : ℕ → WCC.SpecState 4 :=
  Function.update s 0 { s 0 with val := v }

/-- The round-`0` coin update of a `ret id true`. -/
def coinReturn (id : Fin 4) (s : ℕ → WCC.SpecState 4) : ℕ → WCC.SpecState 4 :=
  Function.update s 0 { s 0 with ret := Function.update (s 0).ret id true }

/-- ABA states after the three inputs. -/
noncomputable def abaAfterInput0 : ABAState fourProcesses := abaInput 0 abaInitial
noncomputable def abaAfterInput1 : ABAState fourProcesses := abaInput 1 abaAfterInput0
noncomputable def abaAfterInput2 : ABAState fourProcesses := abaInput 2 abaAfterInput1

/-- Round specifications after the three round-`0` calls. -/
def gbcaSpecificationsAfterCall0 : ℕ → GBCA.SpecState 4 := gbcaSpecificationCall 0
  gbcaSpecificationsInitial
def gbcaSpecificationsAfterCall1 : ℕ → GBCA.SpecState 4 := gbcaSpecificationCall 1
  gbcaSpecificationsAfterCall0
def gbcaSpecificationsAfterCall2 : ℕ → GBCA.SpecState 4 := gbcaSpecificationCall 2
  gbcaSpecificationsAfterCall1

/-- ABA states after the three round-`0` calls. -/
noncomputable def abaAfterCallG0 : ABAState fourProcesses := abaCallG 0 abaAfterInput2
noncomputable def abaAfterCallG1 : ABAState fourProcesses := abaCallG 1 abaAfterCallG0
noncomputable def abaAfterCallG2 : ABAState fourProcesses := abaCallG 2 abaAfterCallG1

/-- Round specifications after `bindUnset` excludes the round-`0` bit `false`,
sparing `true`. -/
def gbcaSpecificationsAfterBindUnset : ℕ → GBCA.SpecState 4 := Function.update
  gbcaSpecificationsAfterCall2 0 { gbcaSpecificationsAfterCall2 0 with excluded := {false} }

/-- Round specifications after the three round-`0` grade-2 returns. -/
def gbcaSpecificationsAfterReturn0 : ℕ → GBCA.SpecState 4 := gbcaSpecificationRetGrade2 0
  gbcaSpecificationsAfterBindUnset
def gbcaSpecificationsAfterReturn1 : ℕ → GBCA.SpecState 4 := gbcaSpecificationRetGrade2 1
  gbcaSpecificationsAfterReturn0
def gbcaSpecificationsAfterReturn2 : ℕ → GBCA.SpecState 4 := gbcaSpecificationRetGrade2 2
  gbcaSpecificationsAfterReturn1

/-- ABA states after the three round-`0` graded-agreement returns. -/
noncomputable def abaAfterRetG0 : ABAState fourProcesses := abaRetG 0 abaAfterCallG2
noncomputable def abaAfterRetG1 : ABAState fourProcesses := abaRetG 1 abaAfterRetG0
noncomputable def abaAfterRetG2 : ABAState fourProcesses := abaRetG 2 abaAfterRetG1

/-- ABA states after all three processes call the coin. -/
noncomputable def abaAfterCallW0 : ABAState fourProcesses := abaCallW 0 abaAfterRetG2
noncomputable def abaAfterCallW1 : ABAState fourProcesses := abaCallW 1 abaAfterCallW0
noncomputable def abaAfterCallW2 : ABAState fourProcesses := abaCallW 2 abaAfterCallW1

/-- The common coin after process `0`'s recording call. -/
def coinAfterRecordingCall0 : ℕ → WCC.SpecState 4 := coinCall 0 coinInitial

/-- The common coin after process `1`'s recording call, which carries the caller count of round
`0` to `2 > f`. -/
def coinAfterRecordingCall1 : ℕ → WCC.SpecState 4 := coinCall 1 coinAfterRecordingCall0

/-- The common coin after its resolution, on the `bit true` branch of the draw. -/
def coinAfterResolution : ℕ → WCC.SpecState 4 := coinResolve (.bit true) coinAfterRecordingCall1

/-- The common coin after process `2`'s recording call, which closes the round's
three calls. -/
def coinAfterRecordingCall2 : ℕ → WCC.SpecState 4 := coinCall 2 coinAfterResolution

/-- The common coin after all three processes receive the coin. -/
def coinAfterReturn0 : ℕ → WCC.SpecState 4 := coinReturn 0 coinAfterRecordingCall2
def coinAfterReturn1 : ℕ → WCC.SpecState 4 := coinReturn 1 coinAfterReturn0
def coinAfterReturn2 : ℕ → WCC.SpecState 4 := coinReturn 2 coinAfterReturn1

/-- ABA states after the three coin returns and the three DECIDED sends, in the order of the run.
Each coin return is the round advance: the round carried the grade `grade2 true`, so the process
keeps the grade and enters `toSendDecided` at round `1`. Each DECIDED send sets `true` in the
sender's DECIDED set, clears the grade and enters `toCallG`. -/
noncomputable def abaAfterRoundStep0 : ABAState fourProcesses := abaAfterCallW2.stepRound 0 true
noncomputable def abaAfterDecidedSend0 : ABAState fourProcesses :=
  abaAfterRoundStep0.sendDecidedOnGrade2 0 true
noncomputable def abaAfterRoundStep1 : ABAState fourProcesses :=
  abaAfterDecidedSend0.stepRound 1 true
noncomputable def abaAfterDecidedSend1 : ABAState fourProcesses :=
  abaAfterRoundStep1.sendDecidedOnGrade2 1 true
noncomputable def abaAfterRoundStep2 : ABAState fourProcesses :=
  abaAfterDecidedSend1.stepRound 2 true
noncomputable def abaAfterDecidedSend2 : ABAState fourProcesses :=
  abaAfterRoundStep2.sendDecidedOnGrade2 2 true

/-- ABA states after the adversary delivers all three `⟨DECIDED, true⟩` to process `0`. -/
noncomputable def abaAfterDeliver0 : ABAState fourProcesses :=
  abaAfterDecidedSend2.deliverDecided 0 0 true
noncomputable def abaAfterDeliver1 : ABAState fourProcesses := abaAfterDeliver0.deliverDecided 0 1
  true
noncomputable def abaAfterDeliver2 : ABAState fourProcesses := abaAfterDeliver1.deliverDecided 0 2
  true

/-- The ABA state after process `0` fires `retABA 0 true`. -/
noncomputable def abaAfterRetABA : ABAState fourProcesses := abaAfterDeliver2.setProcessVariables 0
  {
  abaAfterDeliver2.processes 0 with returned := true }

/-- The four components after a synchronised `fail 0` broadcast; the ABA state carries the
replacement flag of process `0` beside the corrupted set. -/
noncomputable def gbcaSpecificationsAfterFail : ℕ → GBCA.SpecState 4 := fun r =>
  (gbcaSpecificationsInitial r).corrupt fourProcesses (0 : Fin 4)
noncomputable def coinAfterFail : ℕ → WCC.SpecState 4 := fun r => (coinInitial r).corrupt
  fourProcesses (0 : Fin 4)
noncomputable def abaAfterFail : ABAState fourProcesses := ABAState.corrupt fourProcesses (0 : Fin
  4) abaInitial

/-- The initial protocol-shaped state is `(gbcaSpecificationsInitial, abaInitial, coinInitial)`. -/
theorem hybrid_init : (hybrid fourProcesses M).init = hybridStateOf gbcaSpecificationsInitial
  abaInitial coinInitial := rfl

/-! ### Step 1–3: the external input calls (`callABA`, visible) -/

/-- First input: process `0` receives `callABA 0 true`. Visible label; process
`0`'s round loop takes `input`, the other three and the remaining components
idle. -/
theorem step_callABA₀ :
    (hybrid fourProcesses M).step (hybridStateOf gbcaSpecificationsInitial abaInitial coinInitial)
      (Label.callABA (0 : Fin 4) true)
      (PMF.pure (hybridStateOf gbcaSpecificationsInitial abaAfterInput0 coinInitial)) := by
  refine hybrid_visible fourProcesses (by simp) ?_
  have h := hybridExtended_visible_step (M := M) fourProcesses
    (G := gbcaSpecificationsInitial) (C :=
    abaInitial.1) (A := abaInitial.2) (o := coinInitial)
    (L := Sum.inl (Label.callABA (0 : Fin 4) true)) (by simp)
    (gbcaSpecificationFamily_idle fourProcesses gbcaSpecificationsInitial (by simp) rfl not_false)
    (roundLoops_at 0 (RoundLoopStep.input (P := fourProcesses) (abaInitial.1 0) true rfl rfl)
      (fun j hj => RoundLoopStep.callABAIdle (P := fourProcesses) (abaInitial.1 j) 0 true (Ne.symm
        hj)))
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
    (G := gbcaSpecificationsInitial) (C :=
    abaAfterInput0.1) (A := abaAfterInput0.2) (o := coinInitial)
    (L := Sum.inl (Label.callABA (1 : Fin 4) true)) (by simp)
    (gbcaSpecificationFamily_idle fourProcesses gbcaSpecificationsInitial (by simp) rfl not_false)
    (roundLoops_at 1 (RoundLoopStep.input (P := fourProcesses) (abaAfterInput0.1 1) true (by decide)
      (by decide))
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
    (G := gbcaSpecificationsInitial) (C :=
    abaAfterInput1.1) (A := abaAfterInput1.2) (o := coinInitial)
    (L := Sum.inl (Label.callABA (2 : Fin 4) true)) (by simp)
    (gbcaSpecificationFamily_idle fourProcesses gbcaSpecificationsInitial (by simp) rfl not_false)
    (roundLoops_at 2 (RoundLoopStep.input (P := fourProcesses) (abaAfterInput1.1 2) true (by decide)
      (by decide))
      (fun j hj => RoundLoopStep.callABAIdle (P := fourProcesses) (abaAfterInput1.1 j) 2 true
        (Ne.symm hj)))
    (ABANetworkStep.callABAIdle (P := fourProcesses) abaAfterInput1.2 2 true)
    (wccIdle coinInitial (by simp) rfl (by simp [Label.isFail]))
  rw [prodPMF_pure_pure, prodPMF_pure_pure, prodPMF_pure_pure] at h
  exact h

/-! ### Steps 4–6: the graded-agreement calls (`callG 0`, hidden to `τ`) -/

/-- First graded-agreement call: process `0`'s round loop hands over its
estimate and the round-`0` specification takes its owned `call`. -/
theorem step_callG₀ :
    (hybrid fourProcesses M).step
      (hybridStateOf gbcaSpecificationsInitial abaAfterInput2 coinInitial)
      Label.tau
        (PMF.pure (hybridStateOf gbcaSpecificationsAfterCall0 abaAfterCallG0 coinInitial)) := by
  refine hybrid_hidden fourProcesses (l := Label.callG 0 (0 : Fin 4) true) (by simp) ?_
  have h := hybridExtended_visible_step (M := M) fourProcesses
    (G := gbcaSpecificationsInitial) (C :=
    abaAfterInput2.1) (A := abaAfterInput2.2) (o := coinInitial)
    (L := Sum.inl (Label.callG 0 (0 : Fin 4) true)) (by simp)
    (gbcaSpecificationFamily_owned fourProcesses rfl rfl (GBCA.Step.call (P := fourProcesses) (r :=
      0) (gbcaSpecificationsInitial 0) 0 true rfl))
    (roundLoops_at 0 (RoundLoopStep.callG (P := fourProcesses) (abaAfterInput2.1 0) 0 true (by
      decide) (by decide)
        (by decide) (by decide))
      (fun j hj => RoundLoopStep.callGIdle (P := fourProcesses) (abaAfterInput2.1 j) 0 0 true
        (Ne.symm hj)))
    (ABANetworkStep.callGIdle (P := fourProcesses) abaAfterInput2.2 0 0 true)
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
    (G := gbcaSpecificationsAfterCall0) (C :=
    abaAfterCallG0.1) (A := abaAfterCallG0.2) (o := coinInitial)
    (L := Sum.inl (Label.callG 0 (1 : Fin 4) true)) (by simp)
    (gbcaSpecificationFamily_owned fourProcesses rfl rfl (GBCA.Step.call (P := fourProcesses) (r :=
      0) (gbcaSpecificationsAfterCall0 0) 1 true (by
      decide)))
    (roundLoops_at 1 (RoundLoopStep.callG (P := fourProcesses) (abaAfterCallG0.1 1) 0 true (by
      decide) (by decide)
        (by decide) (by decide))
      (fun j hj => RoundLoopStep.callGIdle (P := fourProcesses) (abaAfterCallG0.1 j) 0 1 true
        (Ne.symm hj)))
    (ABANetworkStep.callGIdle (P := fourProcesses) abaAfterCallG0.2 0 1 true)
    (wccIdle coinInitial (by simp) rfl (by simp [Label.isFail]))
  rw [prodPMF_pure_pure, prodPMF_pure_pure, prodPMF_pure_pure] at h
  exact h

/-- Third graded-agreement call: process `2`. The round-`0` specification now
holds three inputs. -/
theorem step_callG₂ :
    (hybrid fourProcesses M).step
    (hybridStateOf gbcaSpecificationsAfterCall1 abaAfterCallG1 coinInitial) Label.tau
    (PMF.pure (hybridStateOf gbcaSpecificationsAfterCall2 abaAfterCallG2 coinInitial)) := by
  refine hybrid_hidden fourProcesses (l := Label.callG 0 (2 : Fin 4) true) (by simp) ?_
  have h := hybridExtended_visible_step (M := M) fourProcesses
    (G := gbcaSpecificationsAfterCall1) (C :=
    abaAfterCallG1.1) (A := abaAfterCallG1.2) (o := coinInitial)
    (L := Sum.inl (Label.callG 0 (2 : Fin 4) true)) (by simp)
    (gbcaSpecificationFamily_owned fourProcesses rfl rfl (GBCA.Step.call (P := fourProcesses) (r :=
      0) (gbcaSpecificationsAfterCall1 0) 2 true (by
      decide)))
    (roundLoops_at 2 (RoundLoopStep.callG (P := fourProcesses) (abaAfterCallG1.1 2) 0 true (by
      decide) (by decide)
        (by decide) (by decide))
      (fun j hj => RoundLoopStep.callGIdle (P := fourProcesses) (abaAfterCallG1.1 j) 0 2 true
        (Ne.symm hj)))
    (ABANetworkStep.callGIdle (P := fourProcesses) abaAfterCallG1.2 0 2 true)
    (wccIdle coinInitial (by simp) rfl (by simp [Label.isFail]))
  rw [prodPMF_pure_pure, prodPMF_pure_pure, prodPMF_pure_pure] at h
  exact h

/-! ### Step 7: the `bindUnset` internal transition of the round-`0`
specification (family `τ`, interleaved) -/

/-- With three of four processes having called, the round-`0` quorum `n − f = 3` is met, so
`bindUnset` excludes the bit `false` (the three callers of `true` supply the `f + 1` support for the
surviving bit). This is a family `τ`, interleaved on the specification while the other three
components hold. -/
theorem step_bindUnset :
    (hybrid fourProcesses M).step
    (hybridStateOf gbcaSpecificationsAfterCall2 abaAfterCallG2 coinInitial) Label.tau
    (PMF.pure (hybridStateOf gbcaSpecificationsAfterBindUnset abaAfterCallG2 coinInitial)) := by
  refine hybrid_visible fourProcesses (by simp) ?_
  exact hybridExtended_tau_specification (M := M) fourProcesses
    (gbcaSpecificationFamily_tau fourProcesses
    (GBCA.Step.bindUnset (P := fourProcesses) (r := 0) (gbcaSpecificationsAfterCall2 0) false
      (by unfold GBCA.SpecState.quorum; decide) (by decide) (by decide)))

/-! ### Steps 8–10: the three graded-agreement grade-2 returns (`retG 0`, hidden) -/

/-- Process `0` takes a grade-2 return of the bound value `true`: the round-`0`
specification sets the grade and records the return, the round loop adopts the
estimate and heads for the coin. -/
theorem step_retG₀ :
    (hybrid fourProcesses M).step
    (hybridStateOf gbcaSpecificationsAfterBindUnset abaAfterCallG2 coinInitial) Label.tau
    (PMF.pure (hybridStateOf gbcaSpecificationsAfterReturn0 abaAfterRetG0 coinInitial)) := by
  refine hybrid_hidden fourProcesses (l := Label.retG 0 (0 : Fin 4) (.grade2 true) true)
    (by simp) ?_
  have h := hybridExtended_visible_step (M := M) fourProcesses
    (G := gbcaSpecificationsAfterBindUnset) (C :=
    abaAfterCallG2.1) (A := abaAfterCallG2.2) (o := coinInitial)
    (L := Sum.inl (Label.retG 0 (0 : Fin 4) (.grade2 true) true)) (by simp)
    (gbcaSpecificationFamily_owned fourProcesses rfl rfl
      (GBCA.Step.retGrade2 (P := fourProcesses) (r := 0)
        (gbcaSpecificationsAfterBindUnset 0) 0 true true
        (by decide) (by decide) (by decide) (Or.inl rfl) rfl))
    (roundLoops_at 0
      (RoundLoopStep.retG (P := fourProcesses) (abaAfterCallG2.1 0) 0 (.grade2 true) true
        (by decide) (by decide) (by decide))
      (fun j hj =>
        RoundLoopStep.retGIdle (P := fourProcesses) (abaAfterCallG2.1 j) 0 0 (.grade2 true)
          true (Ne.symm hj)))
    (ABANetworkStep.retGIdle (P := fourProcesses) abaAfterCallG2.2 0 0 (.grade2 true) true)
    (wccIdle coinInitial (by simp) rfl (by simp [Label.isFail]))
  rw [prodPMF_pure_pure, prodPMF_pure_pure, prodPMF_pure_pure] at h
  exact h

/-- Process `1`'s round-`0` grade-2 return. -/
theorem step_retG₁ :
    (hybrid fourProcesses M).step
    (hybridStateOf gbcaSpecificationsAfterReturn0 abaAfterRetG0 coinInitial) Label.tau
    (PMF.pure (hybridStateOf gbcaSpecificationsAfterReturn1 abaAfterRetG1 coinInitial)) := by
  refine hybrid_hidden fourProcesses (l := Label.retG 0 (1 : Fin 4) (.grade2 true) true)
    (by simp) ?_
  have h := hybridExtended_visible_step (M := M) fourProcesses
    (G := gbcaSpecificationsAfterReturn0) (C :=
    abaAfterRetG0.1) (A := abaAfterRetG0.2) (o := coinInitial)
    (L := Sum.inl (Label.retG 0 (1 : Fin 4) (.grade2 true) true)) (by simp)
    (gbcaSpecificationFamily_owned fourProcesses rfl rfl
      (GBCA.Step.retGrade2 (P := fourProcesses) (r := 0)
        (gbcaSpecificationsAfterReturn0 0) 1 true true
        (by decide) (by decide) (by decide) (Or.inr rfl) (by decide)))
    (roundLoops_at 1
      (RoundLoopStep.retG (P := fourProcesses) (abaAfterRetG0.1 1) 0 (.grade2 true) true
        (by decide) (by decide) (by decide))
      (fun j hj =>
        RoundLoopStep.retGIdle (P := fourProcesses) (abaAfterRetG0.1 j) 0 1 (.grade2 true)
          true (Ne.symm hj)))
    (ABANetworkStep.retGIdle (P := fourProcesses) abaAfterRetG0.2 0 1 (.grade2 true) true)
    (wccIdle coinInitial (by simp) rfl (by simp [Label.isFail]))
  rw [prodPMF_pure_pure, prodPMF_pure_pure, prodPMF_pure_pure] at h
  exact h

/-- Process `2`'s round-`0` grade-2 return. -/
theorem step_retG₂ :
    (hybrid fourProcesses M).step
    (hybridStateOf gbcaSpecificationsAfterReturn1 abaAfterRetG1 coinInitial) Label.tau
    (PMF.pure (hybridStateOf gbcaSpecificationsAfterReturn2 abaAfterRetG2 coinInitial)) := by
  refine hybrid_hidden fourProcesses (l := Label.retG 0 (2 : Fin 4) (.grade2 true) true)
    (by simp) ?_
  have h := hybridExtended_visible_step (M := M) fourProcesses
    (G := gbcaSpecificationsAfterReturn1) (C :=
    abaAfterRetG1.1) (A := abaAfterRetG1.2) (o := coinInitial)
    (L := Sum.inl (Label.retG 0 (2 : Fin 4) (.grade2 true) true)) (by simp)
    (gbcaSpecificationFamily_owned fourProcesses rfl rfl
      (GBCA.Step.retGrade2 (P := fourProcesses) (r := 0)
        (gbcaSpecificationsAfterReturn1 0) 2 true true
        (by decide) (by decide) (by decide) (Or.inr rfl) (by decide)))
    (roundLoops_at 2
      (RoundLoopStep.retG (P := fourProcesses) (abaAfterRetG1.1 2) 0 (.grade2 true) true
        (by decide) (by decide) (by decide))
      (fun j hj =>
        RoundLoopStep.retGIdle (P := fourProcesses) (abaAfterRetG1.1 j) 0 2 (.grade2 true)
          true (Ne.symm hj)))
    (ABANetworkStep.retGIdle (P := fourProcesses) abaAfterRetG1.2 0 2 (.grade2 true) true)
    (wccIdle coinInitial (by simp) rfl (by simp [Label.isFail]))
  rw [prodPMF_pure_pure, prodPMF_pure_pure, prodPMF_pure_pure] at h
  exact h

/-! ### Steps 11–14: all three call the coin (hidden `callW` calls), and the coin resolves
after the second call (a coin `τ`) -/

/-- Process `0` calls the round-`0` coin. The call records the caller, and one caller leaves the
count at `f`. -/
theorem step_callW₀ :
    (hybrid fourProcesses M).step (hybridStateOf gbcaSpecificationsAfterReturn2 abaAfterRetG2
      coinInitial) Label.tau (PMF.pure (hybridStateOf gbcaSpecificationsAfterReturn2 abaAfterCallW0
        coinAfterRecordingCall0)) := by
  refine hybrid_hidden fourProcesses (l := Label.callW 0 (0 : Fin 4)) (by simp) ?_
  have h := hybridExtended_visible_step (M := M) fourProcesses
    (G := gbcaSpecificationsAfterReturn2) (C :=
    abaAfterRetG2.1) (A := abaAfterRetG2.2) (o := coinInitial)
    (L := Sum.inl (Label.callW 0 (0 : Fin 4))) (by simp)
    (gbcaSpecificationFamily_idle fourProcesses gbcaSpecificationsAfterReturn2 (by simp) rfl
      not_false)
    (roundLoops_at 0 (RoundLoopStep.callW (P := fourProcesses) (abaAfterRetG2.1 0) 0 (by decide) (by
      decide) (by decide))
      (fun j hj => RoundLoopStep.callWIdle (P := fourProcesses) (abaAfterRetG2.1 j) 0 0 (Ne.symm
        hj)))
    (ABANetworkStep.callWIdle (P := fourProcesses) abaAfterRetG2.2 0 0)
    ((System.mapIdle_step_some (coinLabelMap_inl (Label.callW 0 (0 : Fin 4))) _).mpr
      (wccFamily_owned fourProcesses coinInitial rfl (WCC.Step.call (P := fourProcesses) (r :=
        0) (coinInitial 0) 0 (by decide))))
  rw [prodPMF_pure_pure, prodPMF_pure_pure, prodPMF_pure_pure] at h
  exact h

/-- Process `1` calls the round-`0` coin. The call records the caller, and the caller count of
round `0` reaches `2 > f`. -/
theorem step_callW₁ :
    (hybrid fourProcesses M).step (hybridStateOf gbcaSpecificationsAfterReturn2 abaAfterCallW0
      coinAfterRecordingCall0) Label.tau (PMF.pure (hybridStateOf gbcaSpecificationsAfterReturn2
        abaAfterCallW1 coinAfterRecordingCall1)) := by
  refine hybrid_hidden fourProcesses (l := Label.callW 0 (1 : Fin 4)) (by simp) ?_
  have h := hybridExtended_visible_step (M := M) fourProcesses
    (G := gbcaSpecificationsAfterReturn2) (C :=
    abaAfterCallW0.1) (A := abaAfterCallW0.2) (o := coinAfterRecordingCall0)
    (L := Sum.inl (Label.callW 0 (1 : Fin 4))) (by simp)
    (gbcaSpecificationFamily_idle fourProcesses gbcaSpecificationsAfterReturn2 (by simp) rfl
      not_false)
    (roundLoops_at 1 (RoundLoopStep.callW (P := fourProcesses) (abaAfterCallW0.1 1) 0 (by decide)
      (by decide) (by decide))
      (fun j hj => RoundLoopStep.callWIdle (P := fourProcesses) (abaAfterCallW0.1 j) 0 1 (Ne.symm
        hj)))
    (ABANetworkStep.callWIdle (P := fourProcesses) abaAfterCallW0.2 0 1)
    ((System.mapIdle_step_some (coinLabelMap_inl (Label.callW 0 (1 : Fin 4))) _).mpr
      (wccFamily_owned fourProcesses coinAfterRecordingCall0 rfl (WCC.Step.call (P :=
        fourProcesses) (r := 0) (coinAfterRecordingCall0 0) 1 (by decide))))
  rw [prodPMF_pure_pure, prodPMF_pure_pure, prodPMF_pure_pure] at h
  exact h

/-- The coin distribution the resolution draws: the `wccPMF` outcome is written to round `0`'s
`val`. -/
noncomputable def resolvedCoinDistribution : PMF (ℕ → WCC.SpecState 4) :=
  (fourProcesses.wccPMF.map (fun o => { coinAfterRecordingCall1 0 with val := o.toCoinValue })).map
    (Function.update coinAfterRecordingCall1 0)

/-- The successor distribution of the coin's resolution: the round specifications, the round
loops and the ABA network remain unchanged, and the common coin resolves. -/
noncomputable def resolvedHybridDistribution : PMF (HybridState fourProcesses) :=
  prodPMF (PMF.pure gbcaSpecificationsAfterReturn2) (prodPMF (PMF.pure abaAfterCallW1.1) (prodPMF
    (PMF.pure abaAfterCallW1.2) resolvedCoinDistribution))

/-- The round-`0` coin resolves. Its caller count `2` exceeds `f` at `val = ⊥`, so the silent
resolution draws `val` from `wccPMF`: the run's single probabilistic step. This is a family `τ`,
interleaved on the common coin while the other three components hold. -/
theorem step_resolve :
    (hybrid fourProcesses M).step
    (hybridStateOf gbcaSpecificationsAfterReturn2 abaAfterCallW1 coinAfterRecordingCall1) Label.tau
    resolvedHybridDistribution := by
  refine hybrid_visible fourProcesses (by simp) ?_
  exact hybridExtended_tau_coin (M := M) fourProcesses
    (WCC.Step.resolve (P := fourProcesses) (r := 0) (coinAfterRecordingCall1 0) (by decide)
      (by simp only [WCC.SpecState.threshold]; decide))

/-- The draw lands on the `bit true` branch — the outcome that agrees with the
bound value — with mass exactly `ε = 1/2 > 0`. This is the run's single
`ε` factor; every other step is Dirac, so the whole path has positive
probability. -/
theorem step_resolve_mass :
    resolvedHybridDistribution
    (hybridStateOf gbcaSpecificationsAfterReturn2 abaAfterCallW1 coinAfterResolution) =
    fourProcesses.ε := by
  have hup : Function.Injective (Function.update coinAfterRecordingCall1 0) := by
    intro a b h; have h0 := congrFun h 0; simpa using h0
  have hg : Function.Injective
      (fun o : CoinOutcome =>
        ({ coinAfterRecordingCall1 0 with val := o.toCoinValue } : WCC.SpecState 4)) :=
    fun _ _ h => CoinOutcome.toCoinValue_injective (congrArg (·.val) h)
  change prodPMF (PMF.pure gbcaSpecificationsAfterReturn2) (prodPMF (PMF.pure abaAfterCallW1.1)
    (prodPMF (PMF.pure abaAfterCallW1.2) resolvedCoinDistribution))
      (gbcaSpecificationsAfterReturn2, abaAfterCallW1.1, abaAfterCallW1.2,
        coinAfterResolution) = fourProcesses.ε
  rw [prodPMF_pure_left_apply, prodPMF_pure_left_apply, prodPMF_pure_left_apply]
  unfold resolvedCoinDistribution
  rw [show (coinAfterResolution : ℕ → WCC.SpecState 4)
      = Function.update coinAfterRecordingCall1 0
        { coinAfterRecordingCall1 0 with val := CoinValue.bit true } from rfl,
    map_apply_inj hup,
    show ({ coinAfterRecordingCall1 0 with val := CoinValue.bit true } : WCC.SpecState 4)
      = (fun o => { coinAfterRecordingCall1 0 with val := o.toCoinValue })
        (CoinOutcome.bit true) from rfl,
    map_apply_inj hg, Parameters.wccPMF_apply_bit]

/-- Process `2` calls the round-`0` coin. The call records the caller; `val` is resolved, so the
resolution is disabled. -/
theorem step_callW₂ :
    (hybrid fourProcesses M).step (hybridStateOf gbcaSpecificationsAfterReturn2 abaAfterCallW1
      coinAfterResolution) Label.tau (PMF.pure (hybridStateOf gbcaSpecificationsAfterReturn2
        abaAfterCallW2 coinAfterRecordingCall2)) := by
  refine hybrid_hidden fourProcesses (l := Label.callW 0 (2 : Fin 4)) (by simp) ?_
  have h := hybridExtended_visible_step (M := M) fourProcesses
    (G := gbcaSpecificationsAfterReturn2) (C :=
    abaAfterCallW1.1) (A := abaAfterCallW1.2) (o := coinAfterResolution)
    (L := Sum.inl (Label.callW 0 (2 : Fin 4))) (by simp)
    (gbcaSpecificationFamily_idle fourProcesses gbcaSpecificationsAfterReturn2 (by simp) rfl
      not_false)
    (roundLoops_at 2 (RoundLoopStep.callW (P := fourProcesses) (abaAfterCallW1.1 2) 0 (by decide)
      (by decide) (by decide))
      (fun j hj => RoundLoopStep.callWIdle (P := fourProcesses) (abaAfterCallW1.1 j) 0 2 (Ne.symm
        hj)))
    (ABANetworkStep.callWIdle (P := fourProcesses) abaAfterCallW1.2 0 2)
    ((System.mapIdle_step_some (coinLabelMap_inl (Label.callW 0 (2 : Fin 4))) _).mpr
      (wccFamily_owned fourProcesses coinAfterResolution rfl (WCC.Step.call (P :=
        fourProcesses) (r := 0) (coinAfterResolution 0) 2 (by decide))))
  rw [prodPMF_pure_pure, prodPMF_pure_pure, prodPMF_pure_pure] at h
  exact h

/-! ### Steps 15–20: the three coin returns (`retW 0`, hidden), each followed by the DECIDED
send of the grade-2 round (a `decidedSend` synchronisation of the sending round loop with the
network) -/

/-- Process `0` receives the coin. Its round carried the grade `grade2 true`, so it enters
`toSendDecided` at round `1` with the grade kept. -/
theorem step_retW₀ :
    (hybrid fourProcesses M).step (hybridStateOf gbcaSpecificationsAfterReturn2 abaAfterCallW2
      coinAfterRecordingCall2) Label.tau (PMF.pure (hybridStateOf gbcaSpecificationsAfterReturn2
        abaAfterRoundStep0 coinAfterReturn0)) := by
  refine hybrid_hidden fourProcesses (l := Label.retW 0 (0 : Fin 4) true) (by simp) ?_
  have h := hybridExtended_visible_step (M := M) fourProcesses
    (G := gbcaSpecificationsAfterReturn2) (C := abaAfterCallW2.1) (A := abaAfterCallW2.2)
    (o := coinAfterRecordingCall2) (L := Sum.inl (Label.retW 0 (0 : Fin 4) true)) (by simp)
    (gbcaSpecificationFamily_idle fourProcesses gbcaSpecificationsAfterReturn2 (by simp) rfl
      not_false)
    (roundLoops_at 0 (RoundLoopStep.retW (P := fourProcesses) (abaAfterCallW2.1 0) 0 true
        (by decide) (by decide) (by decide))
      (fun j hj => RoundLoopStep.retWIdle (P := fourProcesses) (abaAfterCallW2.1 j) 0 0 true
        (Ne.symm hj)))
    (ABANetworkStep.retWIdle (P := fourProcesses) abaAfterCallW2.2 0 0 true)
    ((System.mapIdle_step_some (coinLabelMap_inl (Label.retW 0 (0 : Fin 4) true)) _).mpr
      (wccFamily_owned fourProcesses coinAfterRecordingCall2 rfl
        (WCC.Step.ret (P := fourProcesses) (r := 0) (coinAfterRecordingCall2 0) 0 true
          (Or.inr (by decide)) (by decide))))
  rw [prodPMF_pure_pure, prodPMF_pure_pure, prodPMF_pure_pure] at h
  exact h

/-- Process `0` sends `⟨DECIDED, true⟩` and enters `toCallG` at round `1`. -/
theorem step_decidedSend₀ :
    (hybrid fourProcesses M).step (hybridStateOf gbcaSpecificationsAfterReturn2 abaAfterRoundStep0
      coinAfterReturn0) Label.tau (PMF.pure (hybridStateOf gbcaSpecificationsAfterReturn2
        abaAfterDecidedSend0 coinAfterReturn0)) := by
  refine hybrid_synchronisation fourProcesses (e := .decidedSend (0 : Fin 4) true) ?_
  have h := hybridExtended_visible_step (M := M) fourProcesses
    (G := gbcaSpecificationsAfterReturn2) (C := abaAfterRoundStep0.1) (A := abaAfterRoundStep0.2)
    (o := coinAfterReturn0) (L := Sum.inr (.decidedSend (0 : Fin 4) true)) (by simp)
    (gbcaSpecificationFamily_idle fourProcesses gbcaSpecificationsAfterReturn2 (by simp) rfl
      not_false)
    (roundLoops_at 0 (RoundLoopStep.decidedSend (P := fourProcesses) (abaAfterRoundStep0.1 0) true
        (by decide) (by decide) (by decide))
      (fun j hj => RoundLoopStep.decidedSendIdle (P := fourProcesses) (abaAfterRoundStep0.1 j) 0
        true (Ne.symm hj)))
    (ABANetworkStep.decidedSend (P := fourProcesses) abaAfterRoundStep0.2 0 true)
    ((System.mapIdle_step_none (coinLabelMap_decidedSend (0 : Fin 4) true) _).mpr rfl)
  rw [prodPMF_pure_pure, prodPMF_pure_pure, prodPMF_pure_pure] at h
  exact h

/-- Process `1` receives the coin and enters `toSendDecided`. -/
theorem step_retW₁ :
    (hybrid fourProcesses M).step (hybridStateOf gbcaSpecificationsAfterReturn2 abaAfterDecidedSend0
      coinAfterReturn0) Label.tau (PMF.pure (hybridStateOf gbcaSpecificationsAfterReturn2
        abaAfterRoundStep1 coinAfterReturn1)) := by
  refine hybrid_hidden fourProcesses (l := Label.retW 0 (1 : Fin 4) true) (by simp) ?_
  have h := hybridExtended_visible_step (M := M) fourProcesses
    (G := gbcaSpecificationsAfterReturn2) (C := abaAfterDecidedSend0.1)
    (A := abaAfterDecidedSend0.2)
    (o := coinAfterReturn0) (L := Sum.inl (Label.retW 0 (1 : Fin 4) true)) (by simp)
    (gbcaSpecificationFamily_idle fourProcesses gbcaSpecificationsAfterReturn2 (by simp) rfl
      not_false)
    (roundLoops_at 1 (RoundLoopStep.retW (P := fourProcesses) (abaAfterDecidedSend0.1 1) 0 true
        (by decide) (by decide) (by decide))
      (fun j hj => RoundLoopStep.retWIdle (P := fourProcesses) (abaAfterDecidedSend0.1 j) 0 1 true
        (Ne.symm hj)))
    (ABANetworkStep.retWIdle (P := fourProcesses) abaAfterDecidedSend0.2 0 1 true)
    ((System.mapIdle_step_some (coinLabelMap_inl (Label.retW 0 (1 : Fin 4) true)) _).mpr
      (wccFamily_owned fourProcesses coinAfterReturn0 rfl
        (WCC.Step.ret (P := fourProcesses) (r := 0) (coinAfterReturn0 0) 1 true
          (Or.inr (by decide)) (by decide))))
  rw [prodPMF_pure_pure, prodPMF_pure_pure, prodPMF_pure_pure] at h
  exact h

/-- Process `1` sends `⟨DECIDED, true⟩`. -/
theorem step_decidedSend₁ :
    (hybrid fourProcesses M).step (hybridStateOf gbcaSpecificationsAfterReturn2 abaAfterRoundStep1
      coinAfterReturn1) Label.tau (PMF.pure (hybridStateOf gbcaSpecificationsAfterReturn2
        abaAfterDecidedSend1 coinAfterReturn1)) := by
  refine hybrid_synchronisation fourProcesses (e := .decidedSend (1 : Fin 4) true) ?_
  have h := hybridExtended_visible_step (M := M) fourProcesses
    (G := gbcaSpecificationsAfterReturn2) (C := abaAfterRoundStep1.1) (A := abaAfterRoundStep1.2)
    (o := coinAfterReturn1) (L := Sum.inr (.decidedSend (1 : Fin 4) true)) (by simp)
    (gbcaSpecificationFamily_idle fourProcesses gbcaSpecificationsAfterReturn2 (by simp) rfl
      not_false)
    (roundLoops_at 1 (RoundLoopStep.decidedSend (P := fourProcesses) (abaAfterRoundStep1.1 1) true
        (by decide) (by decide) (by decide))
      (fun j hj => RoundLoopStep.decidedSendIdle (P := fourProcesses) (abaAfterRoundStep1.1 j) 1
        true (Ne.symm hj)))
    (ABANetworkStep.decidedSend (P := fourProcesses) abaAfterRoundStep1.2 1 true)
    ((System.mapIdle_step_none (coinLabelMap_decidedSend (1 : Fin 4) true) _).mpr rfl)
  rw [prodPMF_pure_pure, prodPMF_pure_pure, prodPMF_pure_pure] at h
  exact h

/-- Process `2` receives the coin and enters `toSendDecided`. -/
theorem step_retW₂ :
    (hybrid fourProcesses M).step (hybridStateOf gbcaSpecificationsAfterReturn2 abaAfterDecidedSend1
      coinAfterReturn1) Label.tau (PMF.pure (hybridStateOf gbcaSpecificationsAfterReturn2
        abaAfterRoundStep2 coinAfterReturn2)) := by
  refine hybrid_hidden fourProcesses (l := Label.retW 0 (2 : Fin 4) true) (by simp) ?_
  have h := hybridExtended_visible_step (M := M) fourProcesses
    (G := gbcaSpecificationsAfterReturn2) (C := abaAfterDecidedSend1.1)
    (A := abaAfterDecidedSend1.2)
    (o := coinAfterReturn1) (L := Sum.inl (Label.retW 0 (2 : Fin 4) true)) (by simp)
    (gbcaSpecificationFamily_idle fourProcesses gbcaSpecificationsAfterReturn2 (by simp) rfl
      not_false)
    (roundLoops_at 2 (RoundLoopStep.retW (P := fourProcesses) (abaAfterDecidedSend1.1 2) 0 true
        (by decide) (by decide) (by decide))
      (fun j hj => RoundLoopStep.retWIdle (P := fourProcesses) (abaAfterDecidedSend1.1 j) 0 2 true
        (Ne.symm hj)))
    (ABANetworkStep.retWIdle (P := fourProcesses) abaAfterDecidedSend1.2 0 2 true)
    ((System.mapIdle_step_some (coinLabelMap_inl (Label.retW 0 (2 : Fin 4) true)) _).mpr
      (wccFamily_owned fourProcesses coinAfterReturn1 rfl
        (WCC.Step.ret (P := fourProcesses) (r := 0) (coinAfterReturn1 0) 2 true
          (Or.inr (by decide)) (by decide))))
  rw [prodPMF_pure_pure, prodPMF_pure_pure, prodPMF_pure_pure] at h
  exact h

/-- Process `2` sends `⟨DECIDED, true⟩`; three distinct senders hold `⟨DECIDED, true⟩`. -/
theorem step_decidedSend₂ :
    (hybrid fourProcesses M).step (hybridStateOf gbcaSpecificationsAfterReturn2 abaAfterRoundStep2
      coinAfterReturn2) Label.tau (PMF.pure (hybridStateOf gbcaSpecificationsAfterReturn2
        abaAfterDecidedSend2 coinAfterReturn2)) := by
  refine hybrid_synchronisation fourProcesses (e := .decidedSend (2 : Fin 4) true) ?_
  have h := hybridExtended_visible_step (M := M) fourProcesses
    (G := gbcaSpecificationsAfterReturn2) (C := abaAfterRoundStep2.1) (A := abaAfterRoundStep2.2)
    (o := coinAfterReturn2) (L := Sum.inr (.decidedSend (2 : Fin 4) true)) (by simp)
    (gbcaSpecificationFamily_idle fourProcesses gbcaSpecificationsAfterReturn2 (by simp) rfl
      not_false)
    (roundLoops_at 2 (RoundLoopStep.decidedSend (P := fourProcesses) (abaAfterRoundStep2.1 2) true
        (by decide) (by decide) (by decide))
      (fun j hj => RoundLoopStep.decidedSendIdle (P := fourProcesses) (abaAfterRoundStep2.1 j) 2
        true (Ne.symm hj)))
    (ABANetworkStep.decidedSend (P := fourProcesses) abaAfterRoundStep2.2 2 true)
    ((System.mapIdle_step_none (coinLabelMap_decidedSend (2 : Fin 4) true) _).mpr rfl)
  rw [prodPMF_pure_pure, prodPMF_pure_pure, prodPMF_pure_pure] at h
  exact h

/-! ### Steps 21–23: the adversary delivers the three `⟨DECIDED, true⟩` to
process `0` (a `decidedDeliver` synchronisation of the receiving round loop with the
network). -/

/-- Deliver process `0`'s own `⟨DECIDED, true⟩`. -/
theorem step_deliver₀ :
    (hybrid fourProcesses M).step (hybridStateOf gbcaSpecificationsAfterReturn2
      abaAfterDecidedSend2 coinAfterReturn2) Label.tau (PMF.pure (hybridStateOf
        gbcaSpecificationsAfterReturn2 abaAfterDeliver0 coinAfterReturn2)) := by
  refine hybrid_synchronisation fourProcesses (e := .decidedDeliver (0 : Fin 4) (0 : Fin 4) true) ?_
  have h := hybridExtended_visible_step (M := M) fourProcesses
    (G := gbcaSpecificationsAfterReturn2) (C :=
    abaAfterDecidedSend2.1) (A := abaAfterDecidedSend2.2) (o := coinAfterReturn2)
    (L := Sum.inr (.decidedDeliver (0 : Fin 4) (0 : Fin 4) true)) (by simp)
    (gbcaSpecificationFamily_idle fourProcesses gbcaSpecificationsAfterReturn2 (by simp) rfl
      not_false)
    (roundLoops_at 0 (RoundLoopStep.decidedDeliverReceive (P := fourProcesses)
      (abaAfterDecidedSend2.1 0) 0 true (by decide) (by decide))
      (fun j hj => RoundLoopStep.decidedDeliverIdle (P := fourProcesses) (abaAfterDecidedSend2.1 j)
        0 0 true (Ne.symm hj)))
    (ABANetworkStep.decidedDeliver (P := fourProcesses) abaAfterDecidedSend2.2 0 0 true
      (by decide))
    ((System.mapIdle_step_none (coinLabelMap_decidedDeliver (0 : Fin 4) (0 : Fin 4) true) _).mpr
      rfl)
  rw [prodPMF_pure_pure, prodPMF_pure_pure, prodPMF_pure_pure] at h
  exact h

/-- Deliver process `1`'s `⟨DECIDED, true⟩` to process `0`. -/
theorem step_deliver₁ :
    (hybrid fourProcesses M).step (hybridStateOf gbcaSpecificationsAfterReturn2 abaAfterDeliver0
      coinAfterReturn2) Label.tau (PMF.pure (hybridStateOf gbcaSpecificationsAfterReturn2
        abaAfterDeliver1 coinAfterReturn2)) := by
  refine hybrid_synchronisation fourProcesses (e := .decidedDeliver (0 : Fin 4) (1 : Fin 4) true) ?_
  have h := hybridExtended_visible_step (M := M) fourProcesses
    (G := gbcaSpecificationsAfterReturn2) (C :=
    abaAfterDeliver0.1) (A := abaAfterDeliver0.2) (o := coinAfterReturn2)
    (L := Sum.inr (.decidedDeliver (0 : Fin 4) (1 : Fin 4) true)) (by simp)
    (gbcaSpecificationFamily_idle fourProcesses gbcaSpecificationsAfterReturn2 (by simp) rfl
      not_false)
    (roundLoops_at 0 (RoundLoopStep.decidedDeliverReceive (P := fourProcesses) (abaAfterDeliver0.1
      0)
      1 true (by decide) (by decide))
      (fun j hj => RoundLoopStep.decidedDeliverIdle (P := fourProcesses) (abaAfterDeliver0.1 j) 0 1
        true (Ne.symm hj)))
    (ABANetworkStep.decidedDeliver (P := fourProcesses) abaAfterDeliver0.2 0 1 true (by decide))
    ((System.mapIdle_step_none (coinLabelMap_decidedDeliver (0 : Fin 4) (1 : Fin 4) true) _).mpr
      rfl)
  rw [prodPMF_pure_pure, prodPMF_pure_pure, prodPMF_pure_pure] at h
  exact h

/-- Deliver process `2`'s `⟨DECIDED, true⟩` to process `0`; process `0` now has
the `n − f = 3` distinct senders it needs. -/
theorem step_deliver₂ :
    (hybrid fourProcesses M).step (hybridStateOf gbcaSpecificationsAfterReturn2 abaAfterDeliver1
      coinAfterReturn2) Label.tau (PMF.pure (hybridStateOf gbcaSpecificationsAfterReturn2
        abaAfterDeliver2 coinAfterReturn2)) := by
  refine hybrid_synchronisation fourProcesses (e := .decidedDeliver (0 : Fin 4) (2 : Fin 4) true) ?_
  have h := hybridExtended_visible_step (M := M) fourProcesses
    (G := gbcaSpecificationsAfterReturn2) (C :=
    abaAfterDeliver1.1) (A := abaAfterDeliver1.2) (o := coinAfterReturn2)
    (L := Sum.inr (.decidedDeliver (0 : Fin 4) (2 : Fin 4) true)) (by simp)
    (gbcaSpecificationFamily_idle fourProcesses gbcaSpecificationsAfterReturn2 (by simp) rfl
      not_false)
    (roundLoops_at 0 (RoundLoopStep.decidedDeliverReceive (P := fourProcesses) (abaAfterDeliver1.1
      0)
      2 true (by decide) (by decide))
      (fun j hj => RoundLoopStep.decidedDeliverIdle (P := fourProcesses) (abaAfterDeliver1.1 j) 0 2
        true (Ne.symm hj)))
    (ABANetworkStep.decidedDeliver (P := fourProcesses) abaAfterDeliver1.2 0 2 true (by decide))
    ((System.mapIdle_step_none (coinLabelMap_decidedDeliver (0 : Fin 4) (2 : Fin 4) true) _).mpr
      rfl)
  rw [prodPMF_pure_pure, prodPMF_pure_pure, prodPMF_pure_pure] at h
  exact h

/-! ### Step 24: the decision (`retABA 0 true`, visible) -/

/-- Process `0` returns `true`: it has multicast `⟨DECIDED, true⟩` — the
network's conjunct — and has received DECIDED-true messages from `n − f = 3` distinct
senders — the round loop's. The whole 23-step run, every step a Dirac except the single
`ε`-mass coin resolution, carries positive probability and ends in a genuine
`retABA`. -/
theorem step_retABA :
    (hybrid fourProcesses M).step (hybridStateOf gbcaSpecificationsAfterReturn2 abaAfterDeliver2
      coinAfterReturn2) (Label.retABA (0 : Fin 4) true)
      (PMF.pure (hybridStateOf gbcaSpecificationsAfterReturn2 abaAfterRetABA coinAfterReturn2)) :=
        by
  refine hybrid_visible fourProcesses (by simp) ?_
  have h := hybridExtended_visible_step (M := M) fourProcesses
    (G := gbcaSpecificationsAfterReturn2) (C :=
    abaAfterDeliver2.1) (A := abaAfterDeliver2.2) (o := coinAfterReturn2)
    (L := Sum.inl (Label.retABA (0 : Fin 4) true)) (by simp)
    (gbcaSpecificationFamily_idle fourProcesses gbcaSpecificationsAfterReturn2 (by simp) rfl
      not_false)
    (roundLoops_at 0 (RoundLoopStep.ret (P := fourProcesses) (abaAfterDeliver2.1 0) true (by decide)
      (by decide) (by decide))
      (fun j hj => RoundLoopStep.retABAIdle (P := fourProcesses) (abaAfterDeliver2.1 j) 0 true
        (Ne.symm hj)))
    (ABANetworkStep.retABA (P := fourProcesses) abaAfterDeliver2.2 0 true (by decide))
    (wccIdle coinAfterReturn2 (by simp) rfl (by simp [Label.isFail]))
  rw [prodPMF_pure_pure, prodPMF_pure_pure, prodPMF_pure_pure] at h
  exact h

/-! ### A `fail` broadcast: all four components corrupt in sync -/

/-- Corruption of process `0`: the visible `fail 0` synchronises every component — the round
specifications and the common coin by global broadcast, the ABA network by its own `fail`
transition, which carries the guards, the named round loop by replacing its own program
(deviation D23), and the other three round loops by unchanged (deviation D1). -/
theorem step_fail :
    (hybrid fourProcesses M).step (hybridStateOf gbcaSpecificationsInitial abaInitial coinInitial)
      (Label.fail (0 : Fin 4))
      (PMF.pure (hybridStateOf gbcaSpecificationsAfterFail abaAfterFail coinAfterFail)) := by
  refine hybrid_visible fourProcesses (by simp) ?_
  have h := hybridExtended_visible_step (M := M) fourProcesses
    (G := gbcaSpecificationsInitial) (C :=
    abaInitial.1) (A := abaInitial.2) (o := coinInitial)
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
