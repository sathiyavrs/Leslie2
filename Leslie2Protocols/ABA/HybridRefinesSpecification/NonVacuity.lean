/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sathiya / Claude
-/

import Leslie2Protocols.ABA.Composition.HybridAndSubstitution
import Leslie2Protocols.ABA.Composition.ABAState

/-!
# Non-vacuity witnesses for the protocol-shaped specification

Machine-checked evidence that the composed system `hybrid P` can actually
execute a nontrivial prefix: the core simulation `ABA.coreSim` about it is not
vacuously true through an immediate deadlock.

We fix the small parameter set `fourProcesses` (`n = 4`, `f = 1`, `ε = 1/2`) and exhibit a
concrete **20-step run of `hybrid fourProcesses` that reaches a genuine `retABA`** — a
complete decision — starting from its initial state:

* `step_callABA₀/₁/₂` — three external input handshakes (`callABA`, *visible*:
  the addressed round loop takes its `input` row, the other three idle, and the
  round specifications, the ABA-side network and the coin oracle idle);
* `step_callG₀/₁/₂` — three graded-agreement calls (`callG 0`, *hidden* to `τ`:
  the caller's round loop hands over its estimate and the round-`0`
  specification takes its owned `call`);
* `step_bindUnset` — the round-`0` specification's `bindUnset` internal
  transition excluding the bit `false` (a family `τ`, `n − f` quorum met at
  `n = 4, f = 1` by the three callers of `true`);
* `step_retG₀/₁/₂` — the three graded-agreement `A`-return handshakes
  (`retG 0`, *hidden*), the first locking the round grade to the `A`-side. Each
  return announces the bound bit `true`. Its complement is the bit that
  `step_bindUnset` excluded, which is exactly the return's guard, so the ghost
  output leaves the run intact;
* `step_callW₀` — process `0`'s coin call (`callW 0`, *hidden*), a recording
  call: a single caller does not carry the count past `f = 1`;
* `step_callW₁` + `step_callW₁_mass` — process `1`'s coin call, the resolving
  call and the run's **single probabilistic step**: that access carries the
  caller count to `2 > f` at `val = ⊥`, so the call records its caller and
  draws `val` from `wccPMF`. The successor lands on the `bit true` branch — the
  outcome agreeing with the bound value — with mass exactly `ε = 1/2 > 0`;
* `step_callW₂` — process `2`'s coin call, recording again: `val` is resolved,
  so the resolving row's guard is closed;
* `step_retW₀/₁/₂` — the three coin returns, each a rendezvous on `retWPublish`
  (*hidden*): the round loop's fused round advance (deviation D10) joined with
  the network's publication of `⟨DECIDED, true⟩`, giving three distinct
  DECIDED-true senders;
* `step_deliver₀/₁/₂` — the adversary delivers all three receipts to process `0`
  (a rendezvous on `decidedDeliver`, *hidden*), meeting the `n − f = 3` return quorum;
* `step_retABA` — process `0` fires `retABA 0 true`: the decision.

Plus `step_fail` — a `fail` broadcast synchronising all four components.

Because every step but the resolving call is a Dirac and the chosen branch of
that call has mass `ε > 0`, the whole path is a positive-probability execution: a
product of Diracs times one `ε` factor. Every guard on these closed numeric
states discharges by `decide`/`rfl`; the Dirac successor distributions collapse
through `prodPMF_pure_pure` and `PMF.pure_map`, and the resolving call's branch
mass through `prodPMF_pure_left_apply` and `map_apply_inj`.

The ABA-side components are named through the view of `ABA/Composition/ABAState.lean`: a
state of the run is a triple — the round specifications, one `ABAState` holding
the round loops beside the ABA-side network, and the coin oracle — assembled
into the four-component state by `hybridStateOf`.

Each component carries one name per state of the run and one name per update.
The states are `abaInitial`, `gbcaSpecificationsInitial` and `coinInitial`, and
then, on each side, the state the step named in the list above leaves behind:
`abaAfterInput0`, `abaAfterCallG0`, `abaAfterRetG0`, `abaAfterCallW0`,
`abaAfterRoundStep0`, `abaAfterDeliver0`, `abaAfterRetABA` and `abaAfterFail`;
`gbcaSpecificationsAfterCall0`, `gbcaSpecificationsAfterBindUnset`,
`gbcaSpecificationsAfterReturn0` and `gbcaSpecificationsAfterFail`; `coinAfterRecordingCall0`,
`coinAfterResolvingCall`, `coinAfterReturn0` and
`coinAfterFail`. The updates are `abaInput`, `abaCallG`, `abaRetG`, `abaCallW`
on the ABA side, `gbcaSpecificationCall` and `gbcaSpecificationRetA` on the
round specifications, and `coinCall`, `coinResolve` and `coinReturn` on the coin
oracle. Reading a state name gives the step it follows, and reading an update
name gives the label it answers.
-/

namespace PLTS
namespace ABA

open Implementation Composition

/-- A concrete parameter set: four processes, corruption budget one, and a
never-failing `ε = 1/2` coin, so that each bit outcome carries positive mass
(`ε = 1/2`) and the witnessed resolution can take the `bit true` branch.
`2 * ε + δ ≤ 1` holds with equality (`2 * (1/2) + 0 = 1`); the adversarial `⊤`
outcome and the failure outcome then both have mass `0`. -/
noncomputable abbrev fourProcesses : Parameters := ⟨4, 1, by omega, 1 / 2, 0, by
  rw [add_zero, one_div, ENNReal.mul_inv_cancel] <;> simp, by simp⟩

namespace NonVacuity

/-! ### Assembling and moving the four components -/

/-- A state of the protocol-shaped specification, assembled from the round
specifications, the ABA-side pair and the coin oracle. -/
def hybridStateOf (G : ℕ → GBCA.SpecState 4) (s : ABAState fourProcesses) (o : ℕ → WCC.SpecState 4)
  :
    HybridState fourProcesses := (G, s.1, s.2, o)

/-- The round loops on a label one of them owns: the addressed loop takes its
row, the others stand still, and the group's successor is the pointwise
update. -/
theorem coreLoops_at {C : ∀ _ : Fin 4, RoundLoopRecord 4} (id : Fin 4) {L : ExtendedLabel 4}
    {c' : RoundLoopRecord 4} (hown : RoundLoopStep fourProcesses id (C id) L (PMF.pure c'))
    (hidle : ∀ j, j ≠ id → RoundLoopStep fourProcesses j (C j) L (PMF.pure (C j))) (i : Fin 4) :
    RoundLoopStep fourProcesses i (C i) L (PMF.pure (Function.update C id c' i)) := by
  by_cases h : i = id
  · subst h; rw [Function.update_self]; exact hown
  · rw [Function.update_of_ne h]; exact hidle i h

/-- The coin oracle on a label one of its rounds owns, at a row whose successor
need not be a point mass: the family's successor is the round's, pushed forward
along the update at that round. -/
theorem wccFamilyStep (o : ℕ → WCC.SpecState 4) {l : Label 4} {r : ℕ}
    {μ : PMF (WCC.SpecState 4)} (hr : Label.wccRound l = some r)
    (h : WCC.Step fourProcesses r (o r) l μ) :
    (WCC.specFamily fourProcesses).step o l (μ.map (Function.update o r)) := by
  rw [WCC.specFamily, System.family_step_iff]
  exact Or.inr (Or.inl ⟨r, hr, μ, h, rfl⟩)

/-- The coin oracle's idle row on a shared label that is neither `τ`, nor one
of its own handshakes, nor `fail`. -/
theorem wccIdle (o : ℕ → WCC.SpecState 4) {l : Label 4} (hl : l ≠ Label.tau)
    (hr : Label.wccRound l = none) (hf : ¬ Label.isFail l) :
    (coinOverRoundAlphabet fourProcesses).step o (Sum.inl l) (PMF.pure o) :=
  (System.mapIdle_step_some (coinLabelMap_inl l) (PMF.pure o)).mpr
    (wccFamily_idle fourProcesses o hl hr hf)

/-! ### Named states of the run -/

/-- The round specifications: every round initial. -/
def gbcaSpecificationsInitial : ℕ → GBCA.SpecState 4 := fun _ => GBCA.SpecState.initial 4

/-- The coin oracle: every round initial. -/
def coinInitial : ℕ → WCC.SpecState 4 := fun _ => WCC.SpecState.initial 4

/-- The ABA-side state: every round loop idle, nothing multicast, nobody
corrupted. -/
noncomputable def abaInitial : ABAState fourProcesses := ABAState.initial fourProcesses

/-- The ABA-side update of a `callABA id true` input: enter round `0`, ready to
call the graded agreement. -/
noncomputable def abaInput (id : Fin 4) (s : ABAState fourProcesses) : ABAState fourProcesses :=
  s.setProcess id { s.processes id with
    input := some true, estimate := some true, round := 0, phase := .toCallG }

/-- The ABA-side update of a `callG r id` emit: advance to `awaitG`. -/
noncomputable def abaCallG (id : Fin 4) (s : ABAState fourProcesses) : ABAState fourProcesses :=
  s.setProcess id { s.processes id with phase := .awaitG }

/-- The ABA-side update of a round-`0` graded-agreement `A true` return: adopt
the estimate, record the grade, head for the coin. -/
noncomputable def abaRetG (id : Fin 4) (s : ABAState fourProcesses) : ABAState fourProcesses :=
  s.setProcess id { s.processes id with
    estimate := some true, lastGrade := some (.A true), phase := .toCallW }

/-- The ABA-side update of a `callW r id` emit: advance to `awaitW`. -/
noncomputable def abaCallW (id : Fin 4) (s : ABAState fourProcesses) : ABAState fourProcesses :=
  s.setProcess id { s.processes id with phase := .awaitW }

/-- The round-`0` specification update of a `call id true`: record the input. -/
def gbcaSpecificationCall (id : Fin 4) (s : ℕ → GBCA.SpecState 4) : ℕ → GBCA.SpecState 4 :=
  Function.update s 0 { s 0 with call := Function.update (s 0).call id (some true) }

/-- The round-`0` specification update of an `A true` return by `id`: lock the
grade to the `A`-side and record the return. -/
def gbcaSpecificationRetA (id : Fin 4) (s : ℕ → GBCA.SpecState 4) : ℕ → GBCA.SpecState 4 :=
  Function.update s 0 { s 0 with grade := some true, ret := Function.update (s 0).ret id true }

/-- The round-`0` coin update of a recording call by `id`: record `id` as a
caller. -/
def coinCall (id : Fin 4) (s : ℕ → WCC.SpecState 4) : ℕ → WCC.SpecState 4 :=
  Function.update s 0 ((s 0).record id)

/-- The round-`0` coin update of a resolving call by `id` whose draw lands on
`v`: record `id` as a caller and write `v`. -/
def coinResolve (id : Fin 4) (v : CoinValue) (s : ℕ → WCC.SpecState 4) : ℕ → WCC.SpecState 4 :=
  Function.update s 0 { (s 0).record id with val := v }

/-- The round-`0` coin update of a `ret id true`. -/
def coinReturn (id : Fin 4) (s : ℕ → WCC.SpecState 4) : ℕ → WCC.SpecState 4 :=
  Function.update s 0 { s 0 with ret := Function.update (s 0).ret id true }

/-- ABA-side states after the three inputs. -/
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

/-- ABA-side states after the three round-`0` calls. -/
noncomputable def abaAfterCallG0 : ABAState fourProcesses := abaCallG 0 abaAfterInput2
noncomputable def abaAfterCallG1 : ABAState fourProcesses := abaCallG 1 abaAfterCallG0
noncomputable def abaAfterCallG2 : ABAState fourProcesses := abaCallG 2 abaAfterCallG1

/-- Round specifications after `bindUnset` excludes the round-`0` bit `false`,
sparing `true`. -/
def gbcaSpecificationsAfterBindUnset : ℕ → GBCA.SpecState 4 := Function.update
  gbcaSpecificationsAfterCall2 0 { gbcaSpecificationsAfterCall2 0 with excluded := {false} }

/-- Round specifications after the three round-`0` `A`-returns. -/
def gbcaSpecificationsAfterReturn0 : ℕ → GBCA.SpecState 4 := gbcaSpecificationRetA 0
  gbcaSpecificationsAfterBindUnset
def gbcaSpecificationsAfterReturn1 : ℕ → GBCA.SpecState 4 := gbcaSpecificationRetA 1
  gbcaSpecificationsAfterReturn0
def gbcaSpecificationsAfterReturn2 : ℕ → GBCA.SpecState 4 := gbcaSpecificationRetA 2
  gbcaSpecificationsAfterReturn1

/-- ABA-side states after the three round-`0` graded-agreement returns. -/
noncomputable def abaAfterRetG0 : ABAState fourProcesses := abaRetG 0 abaAfterCallG2
noncomputable def abaAfterRetG1 : ABAState fourProcesses := abaRetG 1 abaAfterRetG0
noncomputable def abaAfterRetG2 : ABAState fourProcesses := abaRetG 2 abaAfterRetG1

/-- ABA-side states after all three processes call the coin. -/
noncomputable def abaAfterCallW0 : ABAState fourProcesses := abaCallW 0 abaAfterRetG2
noncomputable def abaAfterCallW1 : ABAState fourProcesses := abaCallW 1 abaAfterCallW0
noncomputable def abaAfterCallW2 : ABAState fourProcesses := abaCallW 2 abaAfterCallW1

/-- The coin oracle after process `0`'s recording call. -/
def coinAfterRecordingCall0 : ℕ → WCC.SpecState 4 := coinCall 0 coinInitial

/-- The coin oracle after process `1`'s resolving call, on the `bit true`
branch of the draw. -/
def coinAfterResolvingCall : ℕ → WCC.SpecState 4 := coinResolve 1 (.bit true)
  coinAfterRecordingCall0

/-- The coin oracle after process `2`'s recording call, which closes the round's
three calls. -/
def coinAfterRecordingCall2 : ℕ → WCC.SpecState 4 := coinCall 2 coinAfterResolvingCall

/-- The coin oracle after all three processes receive the coin. -/
def coinAfterReturn0 : ℕ → WCC.SpecState 4 := coinReturn 0 coinAfterRecordingCall2
def coinAfterReturn1 : ℕ → WCC.SpecState 4 := coinReturn 1 coinAfterReturn0
def coinAfterReturn2 : ℕ → WCC.SpecState 4 := coinReturn 2 coinAfterReturn1

/-- ABA-side states after the three coin returns; each is the fused round
advance (deviation D10), which multicasts `⟨DECIDED, true⟩` on the `A true`
grade the round carried. -/
noncomputable def abaAfterRoundStep0 : ABAState fourProcesses := abaAfterCallW2.stepRound 0 true
noncomputable def abaAfterRoundStep1 : ABAState fourProcesses := abaAfterRoundStep0.stepRound 1 true
noncomputable def abaAfterRoundStep2 : ABAState fourProcesses := abaAfterRoundStep1.stepRound 2 true

/-- ABA-side states after the adversary delivers all three `⟨DECIDED, true⟩` to
process `0`. -/
noncomputable def abaAfterDeliver0 : ABAState fourProcesses := abaAfterRoundStep2.deliverDecided 0 0
  true
noncomputable def abaAfterDeliver1 : ABAState fourProcesses := abaAfterDeliver0.deliverDecided 0 1
  true
noncomputable def abaAfterDeliver2 : ABAState fourProcesses := abaAfterDeliver1.deliverDecided 0 2
  true

/-- The ABA-side state after process `0` fires `retABA 0 true`. -/
noncomputable def abaAfterRetABA : ABAState fourProcesses := abaAfterDeliver2.setProcess 0 {
  abaAfterDeliver2.processes 0 with returned := true }

/-- The four components after a synchronised `fail 0` broadcast; the ABA-side
state carries the replacement flag of process `0` beside the corrupted set. -/
noncomputable def gbcaSpecificationsAfterFail : ℕ → GBCA.SpecState 4 := fun r =>
  (gbcaSpecificationsInitial r).corrupt fourProcesses (0 : Fin 4)
noncomputable def coinAfterFail : ℕ → WCC.SpecState 4 := fun r => (coinInitial r).corrupt
  fourProcesses (0 : Fin 4)
noncomputable def abaAfterFail : ABAState fourProcesses := ABAState.corrupt fourProcesses (0 : Fin
  4) abaInitial

/-- The initial protocol-shaped state is `(gbcaSpecificationsInitial, abaInitial, coinInitial)`. -/
theorem hybrid_init : (hybrid fourProcesses).init = hybridStateOf gbcaSpecificationsInitial
  abaInitial coinInitial := rfl

/-! ### Step 1–3: the external input handshakes (`callABA`, visible) -/

/-- First input: process `0` receives `callABA 0 true`. Visible label; process
`0`'s round loop takes `input`, the other three and the remaining components
idle. -/
theorem step_callABA₀ :
    (hybrid fourProcesses).step (hybridStateOf gbcaSpecificationsInitial abaInitial coinInitial)
      (Label.callABA (0 : Fin 4) true)
      (PMF.pure (hybridStateOf gbcaSpecificationsInitial abaAfterInput0 coinInitial)) := by
  refine hybrid_vis fourProcesses (by simp) ?_
  have h := hybridExtended_vis_step fourProcesses (G := gbcaSpecificationsInitial) (C :=
    abaInitial.1) (A := abaInitial.2) (o := coinInitial)
    (L := Sum.inl (Label.callABA (0 : Fin 4) true)) (by simp)
    (gbcaSpecificationFamily_idle fourProcesses gbcaSpecificationsInitial (by simp) rfl not_false)
    (coreLoops_at 0 (RoundLoopStep.input (P := fourProcesses) (abaInitial.1 0) true rfl rfl)
      (fun j hj => RoundLoopStep.callABAIdle (P := fourProcesses) (abaInitial.1 j) 0 true (Ne.symm
        hj)))
    (ABANetworkStep.callABAIdle (P := fourProcesses) abaInitial.2 0 true)
    (wccIdle coinInitial (by simp) rfl (by simp [Label.isFail]))
  rw [prodPMF_pure_pure, prodPMF_pure_pure, prodPMF_pure_pure] at h
  exact h

/-- Second input: process `1`. -/
theorem step_callABA₁ :
    (hybrid fourProcesses).step (hybridStateOf gbcaSpecificationsInitial abaAfterInput0 coinInitial)
      (Label.callABA (1 : Fin 4) true)
      (PMF.pure (hybridStateOf gbcaSpecificationsInitial abaAfterInput1 coinInitial)) := by
  refine hybrid_vis fourProcesses (by simp) ?_
  have h := hybridExtended_vis_step fourProcesses (G := gbcaSpecificationsInitial) (C :=
    abaAfterInput0.1) (A := abaAfterInput0.2) (o := coinInitial)
    (L := Sum.inl (Label.callABA (1 : Fin 4) true)) (by simp)
    (gbcaSpecificationFamily_idle fourProcesses gbcaSpecificationsInitial (by simp) rfl not_false)
    (coreLoops_at 1 (RoundLoopStep.input (P := fourProcesses) (abaAfterInput0.1 1) true (by decide)
      (by decide))
      (fun j hj => RoundLoopStep.callABAIdle (P := fourProcesses) (abaAfterInput0.1 j) 1 true
        (Ne.symm hj)))
    (ABANetworkStep.callABAIdle (P := fourProcesses) abaAfterInput0.2 1 true)
    (wccIdle coinInitial (by simp) rfl (by simp [Label.isFail]))
  rw [prodPMF_pure_pure, prodPMF_pure_pure, prodPMF_pure_pure] at h
  exact h

/-- Third input: process `2`. -/
theorem step_callABA₂ :
    (hybrid fourProcesses).step (hybridStateOf gbcaSpecificationsInitial abaAfterInput1 coinInitial)
      (Label.callABA (2 : Fin 4) true)
      (PMF.pure (hybridStateOf gbcaSpecificationsInitial abaAfterInput2 coinInitial)) := by
  refine hybrid_vis fourProcesses (by simp) ?_
  have h := hybridExtended_vis_step fourProcesses (G := gbcaSpecificationsInitial) (C :=
    abaAfterInput1.1) (A := abaAfterInput1.2) (o := coinInitial)
    (L := Sum.inl (Label.callABA (2 : Fin 4) true)) (by simp)
    (gbcaSpecificationFamily_idle fourProcesses gbcaSpecificationsInitial (by simp) rfl not_false)
    (coreLoops_at 2 (RoundLoopStep.input (P := fourProcesses) (abaAfterInput1.1 2) true (by decide)
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
    (hybrid fourProcesses).step (hybridStateOf gbcaSpecificationsInitial abaAfterInput2 coinInitial)
      Label.tau (PMF.pure (hybridStateOf gbcaSpecificationsAfterCall0 abaAfterCallG0 coinInitial))
        := by
  refine hybrid_hidden fourProcesses (l := Label.callG 0 (0 : Fin 4) true) (by simp) ?_
  have h := hybridExtended_vis_step fourProcesses (G := gbcaSpecificationsInitial) (C :=
    abaAfterInput2.1) (A := abaAfterInput2.2) (o := coinInitial)
    (L := Sum.inl (Label.callG 0 (0 : Fin 4) true)) (by simp)
    (gbcaSpecificationFamily_owned fourProcesses rfl rfl (GBCA.Step.call (P := fourProcesses) (r :=
      0) (gbcaSpecificationsInitial 0) 0 true rfl))
    (coreLoops_at 0 (RoundLoopStep.callG (P := fourProcesses) (abaAfterInput2.1 0) 0 true (by
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
    (hybrid fourProcesses).step (hybridStateOf gbcaSpecificationsAfterCall0 abaAfterCallG0
      coinInitial) Label.tau (PMF.pure (hybridStateOf gbcaSpecificationsAfterCall1 abaAfterCallG1
        coinInitial)) := by
  refine hybrid_hidden fourProcesses (l := Label.callG 0 (1 : Fin 4) true) (by simp) ?_
  have h := hybridExtended_vis_step fourProcesses (G := gbcaSpecificationsAfterCall0) (C :=
    abaAfterCallG0.1) (A := abaAfterCallG0.2) (o := coinInitial)
    (L := Sum.inl (Label.callG 0 (1 : Fin 4) true)) (by simp)
    (gbcaSpecificationFamily_owned fourProcesses rfl rfl (GBCA.Step.call (P := fourProcesses) (r :=
      0) (gbcaSpecificationsAfterCall0 0) 1 true (by
      decide)))
    (coreLoops_at 1 (RoundLoopStep.callG (P := fourProcesses) (abaAfterCallG0.1 1) 0 true (by
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
    (hybrid fourProcesses).step (hybridStateOf gbcaSpecificationsAfterCall1 abaAfterCallG1
      coinInitial) Label.tau (PMF.pure (hybridStateOf gbcaSpecificationsAfterCall2 abaAfterCallG2
        coinInitial)) := by
  refine hybrid_hidden fourProcesses (l := Label.callG 0 (2 : Fin 4) true) (by simp) ?_
  have h := hybridExtended_vis_step fourProcesses (G := gbcaSpecificationsAfterCall1) (C :=
    abaAfterCallG1.1) (A := abaAfterCallG1.2) (o := coinInitial)
    (L := Sum.inl (Label.callG 0 (2 : Fin 4) true)) (by simp)
    (gbcaSpecificationFamily_owned fourProcesses rfl rfl (GBCA.Step.call (P := fourProcesses) (r :=
      0) (gbcaSpecificationsAfterCall1 0) 2 true (by
      decide)))
    (coreLoops_at 2 (RoundLoopStep.callG (P := fourProcesses) (abaAfterCallG1.1 2) 0 true (by
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

/-- With three of four processes having called, the round-`0` quorum `n − f = 3`
is met, so `bindUnset` excludes the bit `false` (the three callers of `true` supply
the `f + 1` support for the surviving bit). This is a family `τ`, interleaved on
the specification side while the other three components hold. -/
theorem step_bindUnset :
    (hybrid fourProcesses).step (hybridStateOf gbcaSpecificationsAfterCall2 abaAfterCallG2
      coinInitial) Label.tau (PMF.pure (hybridStateOf gbcaSpecificationsAfterBindUnset
        abaAfterCallG2 coinInitial)) := by
  refine hybrid_vis fourProcesses (by simp) ?_
  exact hybridExtended_tau_spec fourProcesses (gbcaSpecificationFamily_tau fourProcesses
    (GBCA.Step.bindUnset (P := fourProcesses) (r := 0) (gbcaSpecificationsAfterCall2 0) false
      (by unfold GBCA.SpecState.quorum; decide) (by decide) (by decide)))

/-! ### Steps 8–10: the three graded-agreement `A`-returns (`retG 0`, hidden) -/

/-- Process `0` takes an `A`-return of the bound value `true`: the round-`0`
specification locks the grade and records the return, the round loop adopts the
estimate and heads for the coin. -/
theorem step_retG₀ :
    (hybrid fourProcesses).step (hybridStateOf gbcaSpecificationsAfterBindUnset abaAfterCallG2
      coinInitial) Label.tau (PMF.pure (hybridStateOf gbcaSpecificationsAfterReturn0 abaAfterRetG0
        coinInitial)) := by
  refine hybrid_hidden fourProcesses (l := Label.retG 0 (0 : Fin 4) (.A true) true) (by simp) ?_
  have h := hybridExtended_vis_step fourProcesses (G := gbcaSpecificationsAfterBindUnset) (C :=
    abaAfterCallG2.1) (A := abaAfterCallG2.2) (o := coinInitial)
    (L := Sum.inl (Label.retG 0 (0 : Fin 4) (.A true) true)) (by simp)
    (gbcaSpecificationFamily_owned fourProcesses rfl rfl (GBCA.Step.retA (P := fourProcesses) (r :=
      0) (gbcaSpecificationsAfterBindUnset 0) 0 true true
      (by decide) (by decide) (by decide) (Or.inl rfl) rfl))
    (coreLoops_at 0 (RoundLoopStep.retG (P := fourProcesses) (abaAfterCallG2.1 0) 0 (.A true) true
      (by decide)
        (by decide) (by decide))
      (fun j hj => RoundLoopStep.retGIdle (P := fourProcesses) (abaAfterCallG2.1 j) 0 0 (.A true)
        true (Ne.symm hj)))
    (ABANetworkStep.retGIdle (P := fourProcesses) abaAfterCallG2.2 0 0 (.A true) true)
    (wccIdle coinInitial (by simp) rfl (by simp [Label.isFail]))
  rw [prodPMF_pure_pure, prodPMF_pure_pure, prodPMF_pure_pure] at h
  exact h

/-- Process `1`'s round-`0` `A`-return. -/
theorem step_retG₁ :
    (hybrid fourProcesses).step (hybridStateOf gbcaSpecificationsAfterReturn0 abaAfterRetG0
      coinInitial) Label.tau (PMF.pure (hybridStateOf gbcaSpecificationsAfterReturn1 abaAfterRetG1
        coinInitial)) := by
  refine hybrid_hidden fourProcesses (l := Label.retG 0 (1 : Fin 4) (.A true) true) (by simp) ?_
  have h := hybridExtended_vis_step fourProcesses (G := gbcaSpecificationsAfterReturn0) (C :=
    abaAfterRetG0.1) (A := abaAfterRetG0.2) (o := coinInitial)
    (L := Sum.inl (Label.retG 0 (1 : Fin 4) (.A true) true)) (by simp)
    (gbcaSpecificationFamily_owned fourProcesses rfl rfl (GBCA.Step.retA (P := fourProcesses) (r :=
      0) (gbcaSpecificationsAfterReturn0 0) 1 true true
      (by decide) (by decide) (by decide) (Or.inr rfl) (by decide)))
    (coreLoops_at 1 (RoundLoopStep.retG (P := fourProcesses) (abaAfterRetG0.1 1) 0 (.A true) true
      (by decide)
        (by decide) (by decide))
      (fun j hj => RoundLoopStep.retGIdle (P := fourProcesses) (abaAfterRetG0.1 j) 0 1 (.A true)
        true (Ne.symm hj)))
    (ABANetworkStep.retGIdle (P := fourProcesses) abaAfterRetG0.2 0 1 (.A true) true)
    (wccIdle coinInitial (by simp) rfl (by simp [Label.isFail]))
  rw [prodPMF_pure_pure, prodPMF_pure_pure, prodPMF_pure_pure] at h
  exact h

/-- Process `2`'s round-`0` `A`-return. -/
theorem step_retG₂ :
    (hybrid fourProcesses).step (hybridStateOf gbcaSpecificationsAfterReturn1 abaAfterRetG1
      coinInitial) Label.tau (PMF.pure (hybridStateOf gbcaSpecificationsAfterReturn2 abaAfterRetG2
        coinInitial)) := by
  refine hybrid_hidden fourProcesses (l := Label.retG 0 (2 : Fin 4) (.A true) true) (by simp) ?_
  have h := hybridExtended_vis_step fourProcesses (G := gbcaSpecificationsAfterReturn1) (C :=
    abaAfterRetG1.1) (A := abaAfterRetG1.2) (o := coinInitial)
    (L := Sum.inl (Label.retG 0 (2 : Fin 4) (.A true) true)) (by simp)
    (gbcaSpecificationFamily_owned fourProcesses rfl rfl (GBCA.Step.retA (P := fourProcesses) (r :=
      0) (gbcaSpecificationsAfterReturn1 0) 2 true true
      (by decide) (by decide) (by decide) (Or.inr rfl) (by decide)))
    (coreLoops_at 2 (RoundLoopStep.retG (P := fourProcesses) (abaAfterRetG1.1 2) 0 (.A true) true
      (by decide)
        (by decide) (by decide))
      (fun j hj => RoundLoopStep.retGIdle (P := fourProcesses) (abaAfterRetG1.1 j) 0 2 (.A true)
        true (Ne.symm hj)))
    (ABANetworkStep.retGIdle (P := fourProcesses) abaAfterRetG1.2 0 2 (.A true) true)
    (wccIdle coinInitial (by simp) rfl (by simp [Label.isFail]))
  rw [prodPMF_pure_pure, prodPMF_pure_pure, prodPMF_pure_pure] at h
  exact h

/-! ### Steps 11–13: all three call the coin (hidden `callW` handshakes), the
second call resolving it -/

/-- Process `0` calls the round-`0` coin. One caller leaves the count at `f`, so
the call only records. -/
theorem step_callW₀ :
    (hybrid fourProcesses).step (hybridStateOf gbcaSpecificationsAfterReturn2 abaAfterRetG2
      coinInitial) Label.tau (PMF.pure (hybridStateOf gbcaSpecificationsAfterReturn2 abaAfterCallW0
        coinAfterRecordingCall0)) := by
  refine hybrid_hidden fourProcesses (l := Label.callW 0 (0 : Fin 4)) (by simp) ?_
  have h := hybridExtended_vis_step fourProcesses (G := gbcaSpecificationsAfterReturn2) (C :=
    abaAfterRetG2.1) (A := abaAfterRetG2.2) (o := coinInitial)
    (L := Sum.inl (Label.callW 0 (0 : Fin 4))) (by simp)
    (gbcaSpecificationFamily_idle fourProcesses gbcaSpecificationsAfterReturn2 (by simp) rfl
      not_false)
    (coreLoops_at 0 (RoundLoopStep.callW (P := fourProcesses) (abaAfterRetG2.1 0) 0 (by decide) (by
      decide) (by decide))
      (fun j hj => RoundLoopStep.callWIdle (P := fourProcesses) (abaAfterRetG2.1 j) 0 0 (Ne.symm
        hj)))
    (ABANetworkStep.callWIdle (P := fourProcesses) abaAfterRetG2.2 0 0)
    ((System.mapIdle_step_some (coinLabelMap_inl (Label.callW 0 (0 : Fin 4))) _).mpr
      (wccFamily_owned fourProcesses coinInitial rfl (WCC.Step.callRecord (P := fourProcesses) (r :=
        0) (coinInitial 0) 0 (by decide)
        (by simp only [WCC.SpecState.threshold]; decide))))
  rw [prodPMF_pure_pure, prodPMF_pure_pure, prodPMF_pure_pure] at h
  exact h

/-- The coin distribution the resolving call draws: the `wccPMF` outcome is
written to round `0`'s `val` beside the caller's record. -/
noncomputable def resolvedCoinDistribution : PMF (ℕ → WCC.SpecState 4) :=
  (fourProcesses.wccPMF.map (fun o => { (coinAfterRecordingCall0 0).record 1 with
    val :=
      o.toCoinValue })).map
    (Function.update coinAfterRecordingCall0 0)

/-- The successor distribution of process `1`'s coin call: the round
specifications and the ABA-side network stand still, process `1`'s round loop
advances to `awaitW`, and the coin oracle resolves. -/
noncomputable def resolvedHybridDistribution : PMF (HybridState fourProcesses) :=
  prodPMF (PMF.pure gbcaSpecificationsAfterReturn2) (prodPMF (PMF.pure abaAfterCallW1.1) (prodPMF
    (PMF.pure abaAfterCallW1.2) resolvedCoinDistribution))

/-- Process `1` calls the round-`0` coin. Its access carries the caller count to
`2 > f` at `val = ⊥`, so the call records the caller and draws `val` from
`wccPMF`: the run's single probabilistic step. -/
theorem step_callW₁ :
    (hybrid fourProcesses).step (hybridStateOf gbcaSpecificationsAfterReturn2 abaAfterCallW0
      coinAfterRecordingCall0) Label.tau resolvedHybridDistribution := by
  refine hybrid_hidden fourProcesses (l := Label.callW 0 (1 : Fin 4)) (by simp) ?_
  exact hybridExtended_vis_step fourProcesses (G := gbcaSpecificationsAfterReturn2) (C :=
    abaAfterCallW0.1) (A := abaAfterCallW0.2) (o := coinAfterRecordingCall0)
    (L := Sum.inl (Label.callW 0 (1 : Fin 4))) (by simp)
    (gbcaSpecificationFamily_idle fourProcesses gbcaSpecificationsAfterReturn2 (by simp) rfl
      not_false)
    (coreLoops_at 1 (RoundLoopStep.callW (P := fourProcesses) (abaAfterCallW0.1 1) 0 (by decide) (by
      decide) (by decide))
      (fun j hj => RoundLoopStep.callWIdle (P := fourProcesses) (abaAfterCallW0.1 j) 0 1 (Ne.symm
        hj)))
    (ABANetworkStep.callWIdle (P := fourProcesses) abaAfterCallW0.2 0 1)
    ((System.mapIdle_step_some (coinLabelMap_inl (Label.callW 0 (1 : Fin 4))) _).mpr
      (wccFamilyStep coinAfterRecordingCall0 rfl (WCC.Step.callResolve (P := fourProcesses) (r := 0)
        (coinAfterRecordingCall0 0) 1 (by decide)
        (by decide) (by simp only [WCC.SpecState.threshold]; decide))))

/-- The draw lands on the `bit true` branch — the outcome that agrees with the
bound value — with mass exactly `ε = 1/2 > 0`. This is the run's single
`ε` factor; every other step is Dirac, so the whole path has positive
probability. -/
theorem step_callW₁_mass : resolvedHybridDistribution (hybridStateOf gbcaSpecificationsAfterReturn2
  abaAfterCallW1 coinAfterResolvingCall) = fourProcesses.ε := by
  have hup : Function.Injective (Function.update coinAfterRecordingCall0 0) := by
    intro a b h; have h0 := congrFun h 0; simpa using h0
  have hg : Function.Injective
      (fun o : CoinOutcome =>
        ({ (coinAfterRecordingCall0 0).record 1 with val := o.toCoinValue } : WCC.SpecState 4)) :=
    fun _ _ h => CoinOutcome.toCoinValue_injective (congrArg (·.val) h)
  change prodPMF (PMF.pure gbcaSpecificationsAfterReturn2) (prodPMF (PMF.pure abaAfterCallW1.1)
    (prodPMF (PMF.pure abaAfterCallW1.2) resolvedCoinDistribution))
      (gbcaSpecificationsAfterReturn2, abaAfterCallW1.1, abaAfterCallW1.2,
        coinAfterResolvingCall) = fourProcesses.ε
  rw [prodPMF_pure_left_apply, prodPMF_pure_left_apply, prodPMF_pure_left_apply]
  unfold resolvedCoinDistribution
  rw [show (coinAfterResolvingCall : ℕ → WCC.SpecState 4)
      = Function.update coinAfterRecordingCall0 0 { (coinAfterRecordingCall0 0).record 1 with
        val :=
          CoinValue.bit true } from rfl,
    map_apply_inj hup,
    show ({ (coinAfterRecordingCall0 0).record 1 with val := CoinValue.bit true } : WCC.SpecState 4)
      = (fun o => { (coinAfterRecordingCall0 0).record 1 with val := o.toCoinValue })
        (CoinOutcome.bit true) from rfl,
    map_apply_inj hg, Parameters.wccPMF_apply_bit]

/-- Process `2` calls the round-`0` coin. `val` is resolved, so the resolving
row's guard is closed and this call only records. -/
theorem step_callW₂ :
    (hybrid fourProcesses).step (hybridStateOf gbcaSpecificationsAfterReturn2 abaAfterCallW1
      coinAfterResolvingCall) Label.tau (PMF.pure (hybridStateOf gbcaSpecificationsAfterReturn2
        abaAfterCallW2 coinAfterRecordingCall2)) := by
  refine hybrid_hidden fourProcesses (l := Label.callW 0 (2 : Fin 4)) (by simp) ?_
  have h := hybridExtended_vis_step fourProcesses (G := gbcaSpecificationsAfterReturn2) (C :=
    abaAfterCallW1.1) (A := abaAfterCallW1.2) (o := coinAfterResolvingCall)
    (L := Sum.inl (Label.callW 0 (2 : Fin 4))) (by simp)
    (gbcaSpecificationFamily_idle fourProcesses gbcaSpecificationsAfterReturn2 (by simp) rfl
      not_false)
    (coreLoops_at 2 (RoundLoopStep.callW (P := fourProcesses) (abaAfterCallW1.1 2) 0 (by decide) (by
      decide) (by decide))
      (fun j hj => RoundLoopStep.callWIdle (P := fourProcesses) (abaAfterCallW1.1 j) 0 2 (Ne.symm
        hj)))
    (ABANetworkStep.callWIdle (P := fourProcesses) abaAfterCallW1.2 0 2)
    ((System.mapIdle_step_some (coinLabelMap_inl (Label.callW 0 (2 : Fin 4))) _).mpr
      (wccFamily_owned fourProcesses coinAfterResolvingCall rfl (WCC.Step.callRecord (P :=
        fourProcesses) (r := 0) (coinAfterResolvingCall 0) 2 (by decide)
        (by simp only [WCC.SpecState.threshold]; decide))))
  rw [prodPMF_pure_pure, prodPMF_pure_pure, prodPMF_pure_pure] at h
  exact h

/-! ### Steps 14–16: the three coin returns, each a `retWPublish` rendezvous of the
round loop's fused round advance (deviation D10) with the network's publication
of `⟨DECIDED, true⟩`. -/

/-- Process `0` receives the coin and multicasts `⟨DECIDED, true⟩`. -/
theorem step_retW₀ :
    (hybrid fourProcesses).step (hybridStateOf gbcaSpecificationsAfterReturn2 abaAfterCallW2
      coinAfterRecordingCall2) Label.tau (PMF.pure (hybridStateOf gbcaSpecificationsAfterReturn2
        abaAfterRoundStep0 coinAfterReturn0)) := by
  refine hybrid_rendezvous fourProcesses (e := .retWPublish 0 (0 : Fin 4) true true) ?_
  have h := hybridExtended_vis_step fourProcesses (G := gbcaSpecificationsAfterReturn2) (C :=
    abaAfterCallW2.1) (A := abaAfterCallW2.2) (o := coinAfterRecordingCall2)
    (L := Sum.inr (.retWPublish 0 (0 : Fin 4) true true)) (by simp)
    (gbcaSpecificationFamily_idle fourProcesses gbcaSpecificationsAfterReturn2 (by simp) rfl
      not_false)
    (coreLoops_at 0 (RoundLoopStep.retWPublish (P := fourProcesses) (abaAfterCallW2.1 0) 0 true true
      (by decide)
        (by decide) (by decide) (by decide))
      (fun j hj => RoundLoopStep.retWPublishIdle (P := fourProcesses) (abaAfterCallW2.1 j) 0 0 true
        true (Ne.symm hj)))
    (ABANetworkStep.retWPublish (P := fourProcesses) abaAfterCallW2.2 0 0 true true)
    ((System.mapIdle_step_some (coinLabelMap_retWPublish 0 (0 : Fin 4) true true) _).mpr
      (wccFamily_owned fourProcesses coinAfterRecordingCall2 rfl
        (WCC.Step.ret (P := fourProcesses) (r := 0) (coinAfterRecordingCall2 0) 0 true (Or.inr (by
          decide)) (by decide))))
  rw [prodPMF_pure_pure, prodPMF_pure_pure, prodPMF_pure_pure] at h
  exact h

/-- Process `1` receives the coin and multicasts `⟨DECIDED, true⟩`. -/
theorem step_retW₁ :
    (hybrid fourProcesses).step (hybridStateOf gbcaSpecificationsAfterReturn2 abaAfterRoundStep0
      coinAfterReturn0) Label.tau (PMF.pure (hybridStateOf gbcaSpecificationsAfterReturn2
        abaAfterRoundStep1 coinAfterReturn1)) := by
  refine hybrid_rendezvous fourProcesses (e := .retWPublish 0 (1 : Fin 4) true true) ?_
  have h := hybridExtended_vis_step fourProcesses (G := gbcaSpecificationsAfterReturn2) (C :=
    abaAfterRoundStep0.1) (A := abaAfterRoundStep0.2) (o := coinAfterReturn0)
    (L := Sum.inr (.retWPublish 0 (1 : Fin 4) true true)) (by simp)
    (gbcaSpecificationFamily_idle fourProcesses gbcaSpecificationsAfterReturn2 (by simp) rfl
      not_false)
    (coreLoops_at 1 (RoundLoopStep.retWPublish (P := fourProcesses) (abaAfterRoundStep0.1 1) 0 true
      true (by decide)
        (by decide) (by decide) (by decide))
      (fun j hj => RoundLoopStep.retWPublishIdle (P := fourProcesses) (abaAfterRoundStep0.1 j) 0 1
        true true (Ne.symm hj)))
    (ABANetworkStep.retWPublish (P := fourProcesses) abaAfterRoundStep0.2 0 1 true true)
    ((System.mapIdle_step_some (coinLabelMap_retWPublish 0 (1 : Fin 4) true true) _).mpr
      (wccFamily_owned fourProcesses coinAfterReturn0 rfl
        (WCC.Step.ret (P := fourProcesses) (r := 0) (coinAfterReturn0 0) 1 true (Or.inr (by decide))
          (by decide))))
  rw [prodPMF_pure_pure, prodPMF_pure_pure, prodPMF_pure_pure] at h
  exact h

/-- Process `2` receives the coin and multicasts `⟨DECIDED, true⟩`; three
distinct senders now hold `⟨DECIDED, true⟩`. -/
theorem step_retW₂ :
    (hybrid fourProcesses).step (hybridStateOf gbcaSpecificationsAfterReturn2 abaAfterRoundStep1
      coinAfterReturn1) Label.tau (PMF.pure (hybridStateOf gbcaSpecificationsAfterReturn2
        abaAfterRoundStep2 coinAfterReturn2)) := by
  refine hybrid_rendezvous fourProcesses (e := .retWPublish 0 (2 : Fin 4) true true) ?_
  have h := hybridExtended_vis_step fourProcesses (G := gbcaSpecificationsAfterReturn2) (C :=
    abaAfterRoundStep1.1) (A := abaAfterRoundStep1.2) (o := coinAfterReturn1)
    (L := Sum.inr (.retWPublish 0 (2 : Fin 4) true true)) (by simp)
    (gbcaSpecificationFamily_idle fourProcesses gbcaSpecificationsAfterReturn2 (by simp) rfl
      not_false)
    (coreLoops_at 2 (RoundLoopStep.retWPublish (P := fourProcesses) (abaAfterRoundStep1.1 2) 0 true
      true (by decide)
        (by decide) (by decide) (by decide))
      (fun j hj => RoundLoopStep.retWPublishIdle (P := fourProcesses) (abaAfterRoundStep1.1 j) 0 2
        true true (Ne.symm hj)))
    (ABANetworkStep.retWPublish (P := fourProcesses) abaAfterRoundStep1.2 0 2 true true)
    ((System.mapIdle_step_some (coinLabelMap_retWPublish 0 (2 : Fin 4) true true) _).mpr
      (wccFamily_owned fourProcesses coinAfterReturn1 rfl
        (WCC.Step.ret (P := fourProcesses) (r := 0) (coinAfterReturn1 0) 2 true (Or.inr (by decide))
          (by decide))))
  rw [prodPMF_pure_pure, prodPMF_pure_pure, prodPMF_pure_pure] at h
  exact h

/-! ### Steps 17–19: the adversary delivers the three `⟨DECIDED, true⟩` to
process `0` (a `decidedDeliver` rendezvous of the receiving round loop with the
network). -/

/-- Deliver process `0`'s own `⟨DECIDED, true⟩`. -/
theorem step_deliver₀ :
    (hybrid fourProcesses).step (hybridStateOf gbcaSpecificationsAfterReturn2 abaAfterRoundStep2
      coinAfterReturn2) Label.tau (PMF.pure (hybridStateOf gbcaSpecificationsAfterReturn2
        abaAfterDeliver0 coinAfterReturn2)) := by
  refine hybrid_rendezvous fourProcesses (e := .decidedDeliver (0 : Fin 4) (0 : Fin 4) true) ?_
  have h := hybridExtended_vis_step fourProcesses (G := gbcaSpecificationsAfterReturn2) (C :=
    abaAfterRoundStep2.1) (A := abaAfterRoundStep2.2) (o := coinAfterReturn2)
    (L := Sum.inr (.decidedDeliver (0 : Fin 4) (0 : Fin 4) true)) (by simp)
    (gbcaSpecificationFamily_idle fourProcesses gbcaSpecificationsAfterReturn2 (by simp) rfl
      not_false)
    (coreLoops_at 0 (RoundLoopStep.decidedDeliverReceive (P := fourProcesses) (abaAfterRoundStep2.1
      0) 0 true (by decide) (by decide))
      (fun j hj => RoundLoopStep.decidedDeliverIdle (P := fourProcesses) (abaAfterRoundStep2.1 j) 0
        0 true (Ne.symm hj)))
    (ABANetworkStep.decidedDeliver (P := fourProcesses) abaAfterRoundStep2.2 0 0 true (by decide))
    ((System.mapIdle_step_none (coinLabelMap_decidedDeliver (0 : Fin 4) (0 : Fin 4) true) _).mpr
      rfl)
  rw [prodPMF_pure_pure, prodPMF_pure_pure, prodPMF_pure_pure] at h
  exact h

/-- Deliver process `1`'s `⟨DECIDED, true⟩` to process `0`. -/
theorem step_deliver₁ :
    (hybrid fourProcesses).step (hybridStateOf gbcaSpecificationsAfterReturn2 abaAfterDeliver0
      coinAfterReturn2) Label.tau (PMF.pure (hybridStateOf gbcaSpecificationsAfterReturn2
        abaAfterDeliver1 coinAfterReturn2)) := by
  refine hybrid_rendezvous fourProcesses (e := .decidedDeliver (0 : Fin 4) (1 : Fin 4) true) ?_
  have h := hybridExtended_vis_step fourProcesses (G := gbcaSpecificationsAfterReturn2) (C :=
    abaAfterDeliver0.1) (A := abaAfterDeliver0.2) (o := coinAfterReturn2)
    (L := Sum.inr (.decidedDeliver (0 : Fin 4) (1 : Fin 4) true)) (by simp)
    (gbcaSpecificationFamily_idle fourProcesses gbcaSpecificationsAfterReturn2 (by simp) rfl
      not_false)
    (coreLoops_at 0 (RoundLoopStep.decidedDeliverReceive (P := fourProcesses) (abaAfterDeliver0.1 0)
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
    (hybrid fourProcesses).step (hybridStateOf gbcaSpecificationsAfterReturn2 abaAfterDeliver1
      coinAfterReturn2) Label.tau (PMF.pure (hybridStateOf gbcaSpecificationsAfterReturn2
        abaAfterDeliver2 coinAfterReturn2)) := by
  refine hybrid_rendezvous fourProcesses (e := .decidedDeliver (0 : Fin 4) (2 : Fin 4) true) ?_
  have h := hybridExtended_vis_step fourProcesses (G := gbcaSpecificationsAfterReturn2) (C :=
    abaAfterDeliver1.1) (A := abaAfterDeliver1.2) (o := coinAfterReturn2)
    (L := Sum.inr (.decidedDeliver (0 : Fin 4) (2 : Fin 4) true)) (by simp)
    (gbcaSpecificationFamily_idle fourProcesses gbcaSpecificationsAfterReturn2 (by simp) rfl
      not_false)
    (coreLoops_at 0 (RoundLoopStep.decidedDeliverReceive (P := fourProcesses) (abaAfterDeliver1.1 0)
      2 true (by decide) (by decide))
      (fun j hj => RoundLoopStep.decidedDeliverIdle (P := fourProcesses) (abaAfterDeliver1.1 j) 0 2
        true (Ne.symm hj)))
    (ABANetworkStep.decidedDeliver (P := fourProcesses) abaAfterDeliver1.2 0 2 true (by decide))
    ((System.mapIdle_step_none (coinLabelMap_decidedDeliver (0 : Fin 4) (2 : Fin 4) true) _).mpr
      rfl)
  rw [prodPMF_pure_pure, prodPMF_pure_pure, prodPMF_pure_pure] at h
  exact h

/-! ### Step 20: the decision (`retABA 0 true`, visible) -/

/-- Process `0` returns `true`: it has multicast `⟨DECIDED, true⟩` — the
network's conjunct — and holds `n − f = 3` distinct DECIDED-true receipts — the
round loop's. The whole 20-step run, every step a Dirac except the single
`ε`-mass coin resolution, carries positive probability and ends in a genuine
`retABA`. -/
theorem step_retABA :
    (hybrid fourProcesses).step (hybridStateOf gbcaSpecificationsAfterReturn2 abaAfterDeliver2
      coinAfterReturn2) (Label.retABA (0 : Fin 4) true)
      (PMF.pure (hybridStateOf gbcaSpecificationsAfterReturn2 abaAfterRetABA coinAfterReturn2)) :=
        by
  refine hybrid_vis fourProcesses (by simp) ?_
  have h := hybridExtended_vis_step fourProcesses (G := gbcaSpecificationsAfterReturn2) (C :=
    abaAfterDeliver2.1) (A := abaAfterDeliver2.2) (o := coinAfterReturn2)
    (L := Sum.inl (Label.retABA (0 : Fin 4) true)) (by simp)
    (gbcaSpecificationFamily_idle fourProcesses gbcaSpecificationsAfterReturn2 (by simp) rfl
      not_false)
    (coreLoops_at 0 (RoundLoopStep.ret (P := fourProcesses) (abaAfterDeliver2.1 0) true (by decide)
      (by decide) (by decide))
      (fun j hj => RoundLoopStep.retABAIdle (P := fourProcesses) (abaAfterDeliver2.1 j) 0 true
        (Ne.symm hj)))
    (ABANetworkStep.retABA (P := fourProcesses) abaAfterDeliver2.2 0 true (by decide))
    (wccIdle coinAfterReturn2 (by simp) rfl (by simp [Label.isFail]))
  rw [prodPMF_pure_pure, prodPMF_pure_pure, prodPMF_pure_pure] at h
  exact h

/-! ### A `fail` broadcast: all four components corrupt in sync -/

/-- Corruption of process `0`: the visible `fail 0` synchronises every component —
the round specifications and the coin oracle by global broadcast, the ABA-side
network by its own `fail` row, which carries the guards, the named round loop
by replacing its own program (deviation D23), and the other three round loops
by standing still (deviation D1). -/
theorem step_fail :
    (hybrid fourProcesses).step (hybridStateOf gbcaSpecificationsInitial abaInitial coinInitial)
      (Label.fail (0 : Fin 4))
      (PMF.pure (hybridStateOf gbcaSpecificationsAfterFail abaAfterFail coinAfterFail)) := by
  refine hybrid_vis fourProcesses (by simp) ?_
  have h := hybridExtended_vis_step fourProcesses (G := gbcaSpecificationsInitial) (C :=
    abaInitial.1) (A := abaInitial.2) (o := coinInitial)
    (L := Sum.inl (Label.fail (0 : Fin 4))) (by simp)
    (gbcaSpecificationFamily_fail fourProcesses gbcaSpecificationsInitial 0)
    (coreLoops_at 0 (RoundLoopStep.failSelf (P := fourProcesses) (abaInitial.1 0) rfl)
      (fun j hj => RoundLoopStep.failIdle (P := fourProcesses) (abaInitial.1 j) 0 (Ne.symm hj)))
    (ABANetworkStep.fail (P := fourProcesses) abaInitial.2 0 (by decide) (by decide))
    ((System.mapIdle_step_some (coinLabelMap_inl (Label.fail (0 : Fin 4))) _).mpr
      (wccFamily_fail fourProcesses coinInitial 0))
  rw [prodPMF_pure_pure, prodPMF_pure_pure, prodPMF_pure_pure] at h
  exact h

end NonVacuity

end ABA
end PLTS
