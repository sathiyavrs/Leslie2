/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sathiya / Claude
-/

import Leslie2Protocols.ABA.Vocabulary.Labels

/-!
# The ABA specification (blueprint Transition System 1)

This module is the account of record for what the ABA development specifies.

The state is the record `SpecState`: a ghost record `input` of genuine `callABA` events (D13), the
flags `ret` of the processes that have returned, the corrupted set `F`, the decision value `val`,
and a control mode `mode ∈ {flipEnabled, decisionEnabled, noRuleEnabled}` (D21). Eight rules act on
it. `SpecStep.callSet` and `SpecStep.callLoop` carry the interface call of a correct process,
`SpecStep.coinFlip` is the mode loop, `SpecStep.decide` writes the decision value, `SpecStep.ret`
carries the interface return of a correct process, `SpecStep.fail` is corruption (D1), and
`SpecStep.callByzantine` and `SpecStep.retByzantine` are the corrupted interface. Every transition
is Dirac except `SpecStep.coinFlip`.

The interface is the full adversary's. A corrupted process's call records a
bit unrelated to the one its label declares, and a corrupted process returns
any value at any time without moving the state. The rules for correct processes stay
available to a corrupted process, so the two corrupted rules add behaviour and
remove none. The trace predicates of `Specifications/ABASafety.lean` therefore quantify over
never-corrupted returners: a corrupted return carries an arbitrary bit, which
no property of the system can constrain.

The mode loop is what the specification says about liveness. From `ControlMode.flipEnabled` a flip
enables the decision with probability `ε`, fails to deliver with probability `δ`, and returns to
`ControlMode.flipEnabled` with the remaining mass. At `ControlMode.decisionEnabled` the decision is
the only `τ`-rule the mode can enable, so the enabled decision is never withdrawn;
`ControlMode.noRuleEnabled` enables no `τ`-rule at all (D17). The flip names no coin bit. Reading
`toDecisionEnabled` as the coin agreeing with a round's reference value is an outcome coupling of a
refinement, not a component of this system.

The flip is guarded by both bits carrying `f + 1` support, and each of the two
support counts is monotone on its own: every ghost write is a first write, a
corrupted process's write leaves both counts unchanged, its entry being
counted through `F` whatever it holds, and a corruption leaves neither count
smaller, the process it names being counted at both bits from then on and
possibly at one of them already.
So a state passing that guard leaves both bits supported ever after and the
decision stays enabled at `ControlMode.decisionEnabled`; the Lean lemma is deferred.

Provenance rests on the ghost record and the support guard `InputSupport` (D13).
`SpecStep.decide` is the sole writer of `val`. Its guards are `val = ⊥`,
`InputSupport b` and `mode ≠ terminal`, and the support guard is the entire constraint
on the value decided. The rule is therefore enabled whenever some bit carries
`f + 1` recorded-or-corrupt supporters and the mode is not `ControlMode.noRuleEnabled`; no
count of participating processes is read anywhere in the system.
The record holds each process's first genuine call (D16). `SpecStep.callSet`
writes at an empty entry and `SpecStep.callLoop`, the input-enabledness loop,
loops at a filled one, so the label is enabled at every state and every ghost
write is a first write.
-/

namespace PLTS
namespace ABA

/-- The control mode of the specification: waiting to flip, with the decision enabled, or frozen by
a failed flip. -/
inductive ControlMode : Type
  /-- The flip is enabled and the decision is not. -/
  | flipEnabled
  /-- The decision is the only enabled `τ`-rule. -/
  | decisionEnabled
  /-- The flip failed to deliver (D17): no `τ`-rule is enabled. -/
  | noRuleEnabled
  deriving DecidableEq, Repr

/-- The state of the ABA specification (Transition System 1). -/
structure SpecState (n : ℕ) where
  /-- Ghost input record (D13): `input id = some b` when a genuine
  `callABA id b` event was recorded for `id`. -/
  input : Fin n → Option Bool
  /-- Which processes have returned. -/
  ret : Fin n → Bool
  /-- The corrupted set. -/
  F : Finset (Fin n)
  /-- The decision value: once `some v`, every return carries `v`. -/
  val : Option Bool
  /-- The control mode. -/
  mode : ControlMode
  deriving DecidableEq

namespace SpecState

variable {n : ℕ}

/-- The initial spec state: nothing recorded, nobody returned, nobody
corrupted, nothing decided, and the flip enabled. -/
def initial (n : ℕ) : SpecState n where
  input := fun _ => none
  ret := fun _ => false
  F := ∅
  val := none
  mode := .flipEnabled

/-- Corruption of `id` (deviation D1): total, Dirac, monotone in `F`. -/
def corrupt (P : Parameters) (id : Fin P.n) (s : SpecState P.n) : SpecState P.n :=
  if id ∉ s.F ∧ s.F.card < P.f then { s with F := insert id s.F } else s

end SpecState

/-- D13 support for `v`: `f + 1` ids, each either ghost-recorded as inputting
`v` or corrupted. The count is `F`-blind (D15), hence immune to later
corruptions. -/
def InputSupport (P : Parameters) (s : SpecState P.n) (v : Bool) : Prop :=
  P.f + 1 ≤ (Finset.univ.filter (fun id => s.input id = some v ∨ id ∈ s.F)).card

theorem InputSupport.mono {P : Parameters} {s s' : SpecState P.n} {v : Bool}
    (h : InputSupport P s v) (hin : ∀ id, s.input id = some v → s'.input id = some v)
    (hF : s.F ⊆ s'.F) : InputSupport P s' v := by
  refine le_trans h (Finset.card_le_card ?_)
  intro id hid
  rw [Finset.mem_filter] at hid ⊢
  exact ⟨hid.1, hid.2.imp (hin id) (fun hm => hF hm)⟩

/-- The outcome of one flip: it enables the decision, leaves the flip enabled, or fails to deliver.
No coin bit is named. -/
inductive FlipOutcome : Type
  /-- The flip enables the decision: the mode becomes `ControlMode.decisionEnabled`. -/
  | toDecisionEnabled
  /-- The flip leaves the mode at `ControlMode.flipEnabled`. -/
  | toFlipEnabled
  /-- The flip fails to deliver: the mode becomes `ControlMode.noRuleEnabled` (D17). -/
  | undelivered
  deriving DecidableEq, Repr

/-- The flip distribution: mass `ε` on `toDecisionEnabled`, `1 − ε − δ` on `toFlipEnabled` and `δ`
on `undelivered`. It is the image of the development's single coin distribution `Parameters.wccPMF`
under a map that forgets the bit, one bit going to `toDecisionEnabled` and the other, together with
the adversarial outcome, to `toFlipEnabled`. The three masses are all the rules read; no rule names
a coin bit. -/
noncomputable def flipPMF (P : Parameters) : PMF FlipOutcome :=
  P.wccPMF.map (fun o => match o with
    | .bit true => .toDecisionEnabled
    | .bit false => .toFlipEnabled
    | .adversarial => .toFlipEnabled
    | .undelivered => .undelivered)

/-- The step relation of the ABA specification. -/
inductive SpecStep (P : Parameters) :
    SpecState P.n → Label P.n → PMF (SpecState P.n) → Prop
  /-- Rule 1: an environment call records its bit in the ghost record. The
  guard `h` is the empty entry, so the write is a first write and the record
  holds the bit of the process's first genuine call (D13, D16). -/
  | callSet (s : SpecState P.n) (id : Fin P.n) (b : Bool) (h : s.input id = none) :
      SpecStep P s (.callABA id b)
        (PMF.pure { s with input := Function.update s.input id (some b) })
  /-- Rule 2: the input-enabledness loop for `callABA`, at a process whose
  entry is filled. Rule 1 carries the label at an empty entry and this rule
  carries it at a filled one, so the label is enabled in every state; the loop
  writes nothing (D13). -/
  | callLoop (s : SpecState P.n) (id : Fin P.n) (b : Bool) (h : s.input id ≠ none) :
      SpecStep P s (.callABA id b) (PMF.pure s)
  /-- Rule 3 (the flip): the only non-Dirac rule of the system. From
  `ControlMode.flipEnabled`, with nothing decided, one flip resolves by `flipPMF` into
  `ControlMode.decisionEnabled` with probability `ε`, back into `ControlMode.flipEnabled` with
  probability `1 − ε − δ`, and into `ControlMode.noRuleEnabled` with probability `δ` (D17). It is
  one-shot: the three outcomes are the three modes, and the rule names no coin
  bit.

  The guard `hmix` is the mixedness guard: the flip fires only from a state
  where both bits carry `f + 1` support. Under unanimity among the correct processes on one bit the
  other bit is never supported, so the guard fails at every state such a run
  reaches. The flip is then unreachable, and with it every probabilistic
  branch of the system, so the unanimous path is Dirac. This is the liveness
  half of Validity, held structurally by the guard rather than proven. -/
  | coinFlip (s : SpecState P.n) (hm : s.mode = .flipEnabled) (hv : s.val = none)
      (hmix : ∀ b, InputSupport P s b) :
      SpecStep P s .tau
        ((flipPMF P).map (fun o => match o with
          | .toDecisionEnabled => { s with mode := .decisionEnabled }
          | .toFlipEnabled => s
          | .undelivered => { s with mode := .noRuleEnabled }))
  /-- Rule 4 (decide): the sole writer of `val`. Its guards are `val = ⊥`
  (`hv`), `InputSupport b` (`hs`) and `mode ≠ terminal` (`hm`), and the support guard is
  the entire constraint on the decided value: the bit `b` carries `f + 1`
  recorded-or-corrupt supporters (D13). An undelivered flip disables the rule (D17); at
  `ControlMode.decisionEnabled` it is the only enabled `τ`-rule, and it is enabled there
  whenever some bit carries `f + 1` support. The mode returns to `ControlMode.flipEnabled`. -/
  | decide (s : SpecState P.n) (b : Bool) (hv : s.val = none) (hs : InputSupport P s b)
      (hm : s.mode ≠ .noRuleEnabled) :
      SpecStep P s .tau
        (PMF.pure { s with val := some b, mode := .flipEnabled })
  /-- Rule 5 (return): a process returns the decision value. -/
  | ret (s : SpecState P.n) (id : Fin P.n) (b : Bool)
      (h₁ : s.val = some b) (h₂ : s.ret id = false) :
      SpecStep P s (.retABA id b)
        (PMF.pure { s with ret := Function.update s.ret id true })
  /-- Rule 6 (corruption, deviation D1): a guarded deterministic transform.
  The guards `hnew` and `hbud` are the Failure rule's own: `id` is not already
  corrupted, and the budget has room. They are exactly the condition tested by
  the `if` inside `SpecState.corrupt`, so the effect is unchanged and only the
  enabledness moves into the rule. -/
  | fail (s : SpecState P.n) (id : Fin P.n) (hnew : id ∉ s.F)
      (hbud : s.F.card < P.f) :
      SpecStep P s (.fail id) (PMF.pure (s.corrupt P id))
  /-- Rule 7 (corrupted call): the recorded bit is independent of the label's.
  A corrupted caller's declared input need not be what is recorded, so the rule
  writes an arbitrary `b'` under the sole guard `id ∈ s.F` (D23). -/
  | callByzantine (s : SpecState P.n) (id : Fin P.n) (b b' : Bool) (hF : id ∈ s.F) :
      SpecStep P s (.callABA id b)
        (PMF.pure { s with input := Function.update s.input id (some b') })
  /-- Rule 8 (corrupted return): a corrupted process returns anything at any
  time. The state does not move, and the correct return rule `SpecStep.ret`
  remains available to it (D23). -/
  | retByzantine (s : SpecState P.n) (id : Fin P.n) (b : Bool) (hF : id ∈ s.F) :
      SpecStep P s (.retABA id b) (PMF.pure s)

/-- **Counterexample check (D13).** The Validity-violating trace dies at
`SpecStep.decide (b := true)`: with the inputs `1,0,0,0` recorded at
`n = 4, f = 1` and the sole `1`-inputter corrupted, the supporters of `1` are
that one process alone, so the guard `hs`, demanding `f + 1 = 2` of them,
fails. -/
example :
    let input : Fin 4 → Option Bool := fun i => if i = 0 then some true else some false
    let F : Finset (Fin 4) := {0}
    ¬ (1 + 1 ≤ (Finset.univ.filter (fun id => input id = some true ∨ id ∈ F)).card) := by
  decide

/-- **First-write check (D16).** A call at an uncorrupted process holding no
input is answered by rule 1 alone: rule 2 asks for a filled entry and
`SpecStep.callByzantine` for a corrupted caller, so the bit reaches the ghost
record. -/
example (P : Parameters) (s : SpecState P.n) (id : Fin P.n) (b : Bool)
    (h : s.input id = none) (hF : id ∉ s.F) (μ : PMF (SpecState P.n))
    (hstep : SpecStep P s (.callABA id b) μ) :
    μ = PMF.pure { s with input := Function.update s.input id (some b) } := by
  cases hstep with
  | callSet => rfl
  | callLoop _ _ hne => exact absurd h hne
  | callByzantine _ _ _ hmem => exact absurd hmem hF

/-- The ABA specification system (blueprint Transition System 1). -/
noncomputable def spec (P : Parameters) : System (SpecState P.n) (Label P.n) where
  init := SpecState.initial P.n
  step := SpecStep P

@[simp] theorem spec_init (P : Parameters) : (spec P).init = SpecState.initial P.n := rfl

@[simp] theorem spec_step (P : Parameters) (s : SpecState P.n) (l : Label P.n)
    (μ : PMF (SpecState P.n)) : (spec P).step s l μ ↔ SpecStep P s l μ := Iff.rfl

end ABA
end PLTS
