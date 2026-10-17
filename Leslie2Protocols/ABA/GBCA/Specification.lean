/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sathiya / Claude
-/

import Leslie2Protocols.ABA.Vocabulary.Labels
import Leslie2Protocols.Framework.InputEnabledness

/-!
# The GBCA specification instance (blueprint Transition System 2)

The round-`r` instance of the Graded Binding Crusader Agreement specification.

Binding is *negative* information. The state field `excluded : Finset Bool` is the
set of bits the instance can no longer return; it starts empty. The internal
τ-transition `bindUnset b` excludes one bit — `excluded := insert b excluded` — once a
quorum has called and `f + 1` F-blind supporters support the bit `!b`, which is not excluded.
No transition removes a bit and `bindUnset` requires `excluded = ∅`, so `excluded` is written
at most once per instance — the exclusion commits the round — and is monotone along
every execution; `corrupt` leaves it alone. The once-only guard is what makes
every fair round completable: a second exclusion after a grade-2 return would leave
the processes yet to return with no enabled return: the grade-1 and grade-2 returns need a bit
not excluded, and the grade-2 guard disables `retGrade0`. Every property below is a consequence of
that monotonicity plus the membership guards on the return transitions, with no
auxiliary invariant.

Grades: `grade2 b` (decide `b`), `grade1 b` (adopt `b`), `grade0` (no output; adopt the coin).
The `grade` field (`some true` ≈ grade 2, `some false` ≈ grade 0) enforces the
grade-2 / grade-0 exclusivity of Graded Agreement: once a grade-2 return has happened
no grade-0 return can, and vice versa.

## Graded agreement is the guard pair

Both the grade-1 and the grade-2 return carry the guard pair `v ∉ excluded ∧ (!v) ∈ excluded`: the
returned bit is not excluded, and the other bit is already excluded. That pair *is*
graded agreement, with no supporting argument. A return of `v` puts `!v` into
`excluded`; monotonicity carries `!v ∈ excluded` to every later state of the run; a
later return of `w` needs `w ∉ excluded`, so `w ≠ !v`, so `w = v`. Two returns in
one execution therefore name the same bit whatever their grades. Once a return of grade 1
or 2 has fired, the bit not excluded is the only bit any extension can return.

## The announced bound bit

The transition `announceBound b` announces the bound bit `b` on the label `.boundG r b` under the
guard `(!b) ∈ excluded`. It is a Dirac self-loop: it writes nothing, it is enabled at every state
from the exclusion on, and it may repeat (D29). The bit is a ghost output: it is the value the
specification holds as state, and no program reads it. On a reachable state `excluded` holds at
most one bit, so the guard determines `b` as the complement of the excluded bit, and all the
announcements of a round name one bit. A return of grade 1 or 2 of `v` carries
`(!v) ∈ excluded`, so `v` is the announced bit. Every return requires an excluded bit, so the
announcement is enabled at every state from the round's first return on, and every trace with a
return extends by it. This makes binding a property of the trace alone: the round-`r`
announcements of a trace name a single bit, and each round-`r` return of a value returns that bit.

## `retGrade0` and Graded Binding

The grade-0 return's guard `excluded ≠ ∅` is ABDY22's Graded Binding clause read
on this state: *there is a bit `b` such that no non-faulty party decides `1 − b`
at grade `≥ 1` in any extension*. The witness is the bit not excluded, which the
announcement names, and the bit no extension can return is the excluded bit, because the
grade-1 and grade-2 returns refuse an excluded bit and `excluded` only grows. The witness is
thus valid in every extension of the run and not merely at the moment of the return. A grade-0
return commits the instance: from that point on at most one bit is not excluded in any later
state, which is what makes returning no bit the right answer. `retGrade0`
additionally requires `f + 1` F-blind support for each bit (D15), which is what
witnesses that neither bit was forced.

## The all-⊥ run

In a round where neither bit is decidable the specification still commits to a
single excluded bit, and the run ends with grade-0 returns alone. The announcement
names its complement, so the round is bound to one bit on the trace even
though no process is handed a value. The commitment is sound because the
announced bit is a ghost output: it is program data for no component, so no
process is answered with the internal choice. The excluded bit is a bit that no extension can
return, whether the round goes on to return the bit not excluded or returns no bit at all.

## Where a returned value comes from (D14/D15)

* **D14 (repair, necessary for Validity).** The source blueprint's TS 2 witnesses binding
  by a *single* correct caller (`∃ id ∉ F, call id = b`), and grade-1 / grade-0 dissent
  likewise by a single correct dissenter. That singular witness loses the same
  account of where a value comes from that the D13 repair restores in Transition System 1, one level
  down: the witness may
  be corrupted later in the trace, after which nothing attributes the outcome to
  a never-corrupted input — and `hybrid` built on this TS 2 provably violates
  the papers' Validity (deterministic witness at `n = 4, f = 1`, inputs
  `1,0,0,0`: bind at `1` with the sole holder of `1` as its witness, `retGrade1`-adopt everywhere,
  round-1 unanimity decides `1`, `fail 0`, `retABA 1 1` — never-corrupted
  processes all input `0`). ABDY22's implementation carries the `f + 1` via
  Valid-set relay thresholds; TS 2 abstracted it to one witness.
* **D15 (the repair).** Every witness is a count
  `f + 1 ≤ #{id | call id = some b ∨ id ∈ F}` at the relevant bit — exactly
  TS 1's `InputSupport` shape (D13), directly `F`-blind: the count is monotone in `F`
  and in `call`, so later `fail`s do not decrease it. On the exclusion set the
  counts sit at three places. `bindUnset b` counts support for the bit it
  leaves not excluded, `!b`; the `retGrade1` dissent guard counts support for the bit it does
  *not* return, `!v`; `retGrade0` counts support for both bits. The pigeonhole argument
  applies unchanged: `F` is monotone with `|F_final| ≤ f`, so among `f + 1` distinct
  supporters some member is outside the *final* `F`, hence outside the current
  `F`, hence a never-corrupted genuine caller — corrupt supporters are counted
  against the `F` budget itself, with no record of phantom calls. Chaining the two:
  a bit `v` returned at grade `≥ 1` requires `(!v) ∈ excluded`, and the
  `bindUnset (!v)` that put it there witnessed `f + 1` F-blind supporters of
  `!(!v) = v`; the budget pigeonhole then yields a never-corrupted genuine
  caller of `v` for every return of grade 1 or 2.

* **D19 (the state shape).** The source blueprint's TS 2 carries a bound value
  `bind ∈ {0, 1, ⊥}`. The exclusion set is the excluded-bit form of that
  value: `excluded ∈ {∅, {b}}`, embedding `bind = ⊥ ↦ excluded = ∅` and
  `bind = b ↦ excluded = {!b}`. The two states therefore differ in the guards, not
  in the cardinality. The blueprint's `bind = some v` guard on the
  grade-1 and grade-2 returns becomes the pair `v ∉ excluded ∧ (!v) ∈ excluded`, its
  `bind = none` guard on binding becomes `excluded = ∅`, and the grade-0 return's
  binding obligation `bind ≠ ⊥` becomes `excluded ≠ ∅`. The source puts the
  bound value on every return label, `return(id, x, bind)`; here every return carries
  the returned value alone, and `announceBound` announces the bound value on `boundG r b`
  (D29).

Every transition is Dirac, so the instance is an LTS and the `ForwardLTS`
correspondence applies. `fail` is the determinised D1 `corrupt`; the family
(`GBCA.specFamily`) broadcasts it to all rounds.

## Inputs and outputs

The calls `callG r id b` and the corruptions `fail id` are the inputs of the round-`r` instance,
and the returns `retG r id out` and the announcements `boundG r b` are its outputs
(`GBCA.specInstInputOutputLabels`). `Step.callLoop` takes a call at every state and `Step.fail` a
corruption, so the instance is input-enabled (`GBCA.specInst_inputEnabled`); the guards of the
returns and of the announcement sit on outputs. The family takes every non-silent label other
than a return and an announcement as an input (`GBCA.specFamily_inputEnabled`).
-/

namespace PLTS
namespace ABA
namespace GBCA

/-- The state of one GBCA specification instance. -/
structure SpecState (n : ℕ) where
  /-- Pending inputs: `call id = some b` when `id` has input `b`. -/
  call : Fin n → Option Bool
  /-- Which processes have received their return. -/
  ret : Fin n → Bool
  /-- The exclusion set: the bits the instance can no longer return.
  Monotone, written at most once, by `bindUnset`. -/
  excluded : Finset Bool
  /-- The grade: `some true` after a grade-2 return, `some false` after a
  grade-0 return (`⊥` before either). -/
  grade : Option Bool
  /-- The corrupted set (local copy, kept equal by `fail` broadcast). -/
  F : Finset (Fin n)
  deriving DecidableEq

namespace SpecState

variable {n : ℕ}

/-- The initial GBCA instance state: no bit is excluded yet. -/
def initial (n : ℕ) : SpecState n where
  call := fun _ => none
  ret := fun _ => false
  excluded := ∅
  grade := none
  F := ∅

/-- The quorum guard `|{id ∉ F | call[id] ≠ ⊥} ∪ F| ≥ n − f`. -/
def quorum (P : Parameters) (s : SpecState P.n) : Prop :=
  P.n - P.f ≤ ((Finset.univ.filter (fun id => id ∉ s.F ∧ s.call id ≠ none)) ∪ s.F).card

/-- Corruption (deviation D1): total, Dirac, monotone in `F`, and blind to
`excluded`. -/
def corrupt (P : Parameters) (id : Fin P.n) (s : SpecState P.n) : SpecState P.n :=
  if id ∉ s.F ∧ s.F.card < P.f then { s with F := insert id s.F } else s

end SpecState

/-! ### Corruption preserved by a write elsewhere

`SpecState.corrupt` writes `F` and nothing else, so every other projection
passes through it untouched. These four `@[simp]` lemmas are the canonical
statements of that fact; the refinement, safety and core-simulation files all
read them from here rather than reproving them locally. -/

@[simp] theorem corrupt_call (P : Parameters) (s : SpecState P.n) (id : Fin P.n) :
    (s.corrupt P id).call = s.call := by
  unfold SpecState.corrupt; split <;> rfl

@[simp] theorem corrupt_ret (P : Parameters) (s : SpecState P.n) (id : Fin P.n) :
    (s.corrupt P id).ret = s.ret := by
  unfold SpecState.corrupt; split <;> rfl

@[simp] theorem corrupt_excluded (P : Parameters) (s : SpecState P.n) (id : Fin P.n) :
    (s.corrupt P id).excluded = s.excluded := by
  unfold SpecState.corrupt; split <;> rfl

@[simp] theorem corrupt_grade (P : Parameters) (s : SpecState P.n) (id : Fin P.n) :
    (s.corrupt P id).grade = s.grade := by
  unfold SpecState.corrupt; split <;> rfl

/-- The corrupted set after a corruption. Not a simp lemma: it introduces an
`ite`. -/
theorem SpecState.corrupt_F (P : Parameters) (s : SpecState P.n) (id : Fin P.n) :
    (s.corrupt P id).F = if id ∉ s.F ∧ s.F.card < P.f then insert id s.F else s.F := by
  unfold SpecState.corrupt
  split_ifs <;> rfl

/-- The step relation of the round-`r` GBCA specification instance
(blueprint Transition System 2, deviation D19). -/
inductive Step (P : Parameters) (r : ℕ) :
    SpecState P.n → Label P.n → PMF (SpecState P.n) → Prop
  /-- A process inputs its bit. -/
  | call (s : SpecState P.n) (id : Fin P.n) (b : Bool) (h : s.call id = none) :
      Step P r s (.callG r id b)
        (PMF.pure { s with call := Function.update s.call id (some b) })
  /-- Input-enabledness loop for `call`. -/
  | callLoop (s : SpecState P.n) (id : Fin P.n) (b : Bool) :
      Step P r s (.callG r id b) (PMF.pure s)
  /-- Binding: a quorum has called and `f + 1` processes support the
  bit `!b` (D15, InputSupport form: caller or `F`-member); exclude `b`. Fires at most
  once per instance — the guard is `excluded = ∅` — and `excluded` never shrinks. -/
  | bindUnset (s : SpecState P.n) (b : Bool)
      (hq : s.quorum P)
      (hw : P.f + 1 ≤ (Finset.univ.filter
        (fun id => s.call id = some (!b) ∨ id ∈ s.F)).card)
      (hd0 : s.excluded = ∅) :
      Step P r s .tau (PMF.pure { s with excluded := insert b s.excluded })
  /-- Grade-1 return: adopt the bit `v`, which is not excluded (`f + 1` dissenting supporters,
  D15). The guard pair `v ∉ excluded`, `(!v) ∈ excluded` is graded agreement; the label
  carries the returned value alone. -/
  | retGrade1 (s : SpecState P.n) (id : Fin P.n) (v : Bool)
      (hlive : v ∉ s.excluded) (hexcluded : (!v) ∈ s.excluded)
      (hw : P.f + 1 ≤ (Finset.univ.filter
        (fun id' => s.call id' = some (!v) ∨ id' ∈ s.F)).card)
      (hr : s.ret id = false) :
      Step P r s (.retG r id (.grade1 v))
        (PMF.pure { s with ret := Function.update s.ret id true })
  /-- Grade-2 return: decide the bit `v`, which is not excluded (writes grade 2). Same guard pair
  as `retGrade1`. -/
  | retGrade2 (s : SpecState P.n) (id : Fin P.n) (v : Bool)
      (hlive : v ∉ s.excluded) (hexcluded : (!v) ∈ s.excluded)
      (hg : s.grade = none ∨ s.grade = some true)
      (hr : s.ret id = false) :
      Step P r s (.retG r id (.grade2 v))
        (PMF.pure { s with grade := some true, ret := Function.update s.ret id true })
  /-- Grade-0 return: no output. The guard `excluded ≠ ∅` is the Graded Binding witness, valid in
  every extension because `excluded` only grows, and it enables the announcement of the bit not
  excluded at every state from the return on. Both bits carry `f + 1` F-blind support (D15),
  which is what makes returning no bit the right answer; the grade is written 0. -/
  | retGrade0 (s : SpecState P.n) (id : Fin P.n)
      (hexcluded : s.excluded ≠ ∅)
      (hwT : P.f + 1 ≤ (Finset.univ.filter
        (fun id' => s.call id' = some true ∨ id' ∈ s.F)).card)
      (hwF : P.f + 1 ≤ (Finset.univ.filter
        (fun id' => s.call id' = some false ∨ id' ∈ s.F)).card)
      (hg : s.grade = none ∨ s.grade = some false)
      (hr : s.ret id = false) :
      Step P r s (.retG r id .grade0)
        (PMF.pure { s with grade := some false, ret := Function.update s.ret id true })
  /-- The announcement of the bound bit `b`, under the guard `(!b) ∈ excluded`: a Dirac
  self-loop, enabled at every state from the exclusion on, which may repeat. Every return
  requires an excluded bit, so the announcement is enabled at every state from the round's first
  return on (D29). -/
  | announceBound (s : SpecState P.n) (b : Bool) (h : (!b) ∈ s.excluded) :
      Step P r s (.boundG r b) (PMF.pure s)
  /-- Corruption (deviation D1). -/
  | fail (s : SpecState P.n) (id : Fin P.n) :
      Step P r s (.fail id) (PMF.pure (s.corrupt P id))

/-- The transition of the announcement: a self-loop under the guard `(!b) ∈ excluded`. -/
theorem step_boundG_cases {P : Parameters} {r : ℕ} {s : SpecState P.n} {b : Bool}
    {μ : PMF (SpecState P.n)} (h : Step P r s (.boundG r b) μ) :
    (!b) ∈ s.excluded ∧ μ = PMF.pure s := by
  cases h with
  | announceBound _ h => exact ⟨h, rfl⟩

/-- The round-`r` GBCA specification instance. -/
noncomputable def specInst (P : Parameters) (r : ℕ) : System (SpecState P.n) (Label P.n) where
  init := SpecState.initial P.n
  step := Step P r

@[simp] theorem specInst_init (P : Parameters) (r : ℕ) :
    (specInst P r).init = SpecState.initial P.n := rfl

@[simp] theorem specInst_step (P : Parameters) (r : ℕ) (s : SpecState P.n)
    (l : Label P.n) (μ : PMF (SpecState P.n)) :
    (specInst P r).step s l μ ↔ Step P r s l μ := Iff.rfl

/-- Every GBCA spec transition is Dirac: the instance is an LTS. -/
theorem specInst_isLTS (P : Parameters) (r : ℕ) : (specInst P r).IsLTS := by
  rintro s l μ hstep
  cases hstep <;> exact ⟨_, rfl⟩

/-- The broadcast transform of the GBCA family: corruption on `fail id`,
identity on every other label. -/
def failAct (P : Parameters) : Label P.n → SpecState P.n → SpecState P.n
  | .fail id, s => s.corrupt P id
  | _, s => s

/-- The ℕ-indexed family of GBCA specification instances. -/
noncomputable def specFamily (P : Parameters) :
    System (InstanceFamilyState (SpecState.initial P.n) (failAct P)) (Label P.n) :=
  System.family (specInst P) Label.gbcaRound Label.isFail (failAct P) (SpecState.initial P.n)

/-- The family starts from the instances' initial states. -/
theorem specFamily_init_apply (P : Parameters) (r : ℕ) :
    (specFamily P).init r = (specInst P r).init :=
  System.family_init_apply _ _ _ (specInst_init P) r

/-- The GBCA spec family is an LTS. -/
theorem specFamily_isLTS (P : Parameters) : (specFamily P).IsLTS :=
  System.family_isLTS (specInst_isLTS P) _ _ _ _

/-! ### Inputs and outputs -/

/-- The input labels and the output labels of the round-`r` instance: the calls and the
corruptions are its inputs, the returns and the announcements its outputs. -/
def specInstInputOutputLabels (P : Parameters) (r : ℕ) : InputOutputLabels (Label P.n) where
  inputLabels := {l | ∃ id b, l = .callG r id b} ∪ {l | ∃ id, l = .fail id}
  outputLabels := {l | ∃ id out, l = .retG r id out} ∪ {l | ∃ b, l = .boundG r b}

/-- **The round-`r` instance is input-enabled.** `Step.callLoop` takes a call at every state,
beside `Step.call` at a process holding no input, and `Step.fail` takes a corruption. -/
theorem specInst_inputEnabled (P : Parameters) (r : ℕ) :
    (specInst P r).InputEnabled (specInstInputOutputLabels P r).inputLabels := by
  rintro s _ (⟨id, b, rfl⟩ | ⟨id, rfl⟩)
  · exact ⟨_, Step.callLoop s id b⟩
  · exact ⟨_, Step.fail s id⟩

/-- The input labels and the output labels of the family: the returns and the announcements of
every round are its outputs, and every other non-silent label is an input. -/
def specFamilyInputOutputLabels (P : Parameters) : InputOutputLabels (Label P.n) where
  inputLabels := {l | l ≠ .tau ∧ (∀ r id out, l ≠ .retG r id out) ∧ ∀ r b, l ≠ .boundG r b}
  outputLabels := {l | ∃ r id out, l = .retG r id out} ∪ {l | ∃ r b, l = .boundG r b}

/-- **The family is input-enabled.** A call of round `r` is taken by the round-`r` instance, a
corruption by the broadcast, and every other non-silent label other than a return and an
announcement by the family's idle transition (`System.InputEnabled.family`). -/
theorem specFamily_inputEnabled (P : Parameters) :
    (specFamily P).InputEnabled (specFamilyInputOutputLabels P).inputLabels := by
  refine (System.InputEnabled.family (specInst_inputEnabled P) Label.gbcaRound Label.isFail
    (failAct P) (SpecState.initial P.n)).mono ?_
  rintro l ⟨hτ, hret, hbound⟩
  cases l with
  | tau => exact absurd rfl hτ
  | callG r id b => exact Or.inr ⟨r, rfl, Or.inl ⟨id, b, rfl⟩⟩
  | retG r id out => exact absurd rfl (hret r id out)
  | boundG r b => exact absurd rfl (hbound r b)
  | _ => exact Or.inl ⟨hτ, rfl⟩

end GBCA
end ABA
end PLTS
