/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sathiya / Claude
-/

import Leslie2Protocols.ABA.Vocabulary.Labels
import Leslie2Protocols.Framework.LoopsAndInstanceFamilies

/-!
# The GBCA specification instance (blueprint Transition System 2)

The round-`r` instance of the Graded Binding Crusader Agreement specification.

Binding is *negative* information. The state field `excluded : Finset Bool` is the
set of bits the instance can no longer hand out; it starts empty. The internal
τ-transition `bindUnset b` excludes one bit — `excluded := insert b excluded` — once a
quorum has spoken and `f + 1` F-blind supporters back the *surviving* bit `!b`.
No rule removes a bit and `bindUnset` requires `excluded = ∅`, so `excluded` is written
at most once per instance — the exclusion commits the round — and is monotone along
every execution; `corrupt` leaves it alone. The once-only guard is what makes
every fair round completable: a second exclusion after a grade-2 return would strand
the processes yet to return, the value-bearing returns needing a live bit and
`retGrade0` being blocked by the grade-2 guard. Every property below is a consequence of
that monotonicity plus the membership guards on the return rules, with no
auxiliary invariant.

Grades: `grade2 b` (decide `b`), `grade1 b` (adopt `b`), `grade0` (no output; adopt the coin).
The `grade` field (`some true` ≈ the grade-2 lock, `some false` ≈ the
grade-0 lock) enforces the grade-2 / grade-0 exclusivity of Graded Agreement: once a
grade-2 return has happened no grade-0 return can, and vice versa.

## Graded agreement is the guard pair

Both value-bearing returns carry the guard pair `v ∉ excluded ∧ (!v) ∈ excluded`: the
bit handed out is alive, and the other bit is already excluded. That pair *is*
graded agreement, with no supporting argument. A return of `v` pins `!v` into
`excluded`; monotonicity carries `!v ∈ excluded` to every later state of the run; a
later return of `w` needs `w ∉ excluded`, so `w ≠ !v`, so `w = v`. Two returns in
one execution therefore name the same bit whatever their grades, and a single
bit — the unique survivor once any value-bearing return has fired — is the only
bit any extension can ever hand out.

## The bound bit on the label

Every return rule takes a bit `bnd` under the guard `(!bnd) ∈ excluded` and
announces it on the label `.retG r id out bnd`. The bit is a ghost output: it is
the value the specification holds as state, and no program reads it. On a
reachable state `excluded` holds at most one bit, so the guard determines `bnd`
as the complement of the excluded bit. All the returns of a round therefore
announce one bit. A value-bearing return carries `(!v) ∈ excluded` as well, so it
announces `bnd = v`. This makes binding a property of the trace alone: the
round-`r` returns of a trace name a single bit, and each of them that hands out a
value hands out that bit.

## `retGrade0` and Graded Binding

The grade-0 return's guard `(!bnd) ∈ excluded` is ABDY22's Graded Binding clause read
on this state: *there is a bit `b` such that no non-faulty party decides `1 − b`
at grade `≥ 1` in any extension*. The witness is the announced bit `bnd`, and the
bit no extension can hand out is `!bnd`, because the value-bearing returns refuse
an excluded bit and `excluded` only grows. The witness is thus valid in every
extension of the run and not merely at the moment of the return. A grade-0 return
commits the instance: from that point on at most one bit is alive anywhere in the
future, which is what makes handing out no bit the right answer. `retGrade0`
additionally requires `f + 1` F-blind support for each bit (D15), which is what
certifies that neither bit was forced.

## The all-⊥ run

In a round where neither bit is decidable the specification still commits to a
single excluded bit, and the run ends with grade-0 returns alone. Those returns
announce its complement, so the round is bound to one bit on the trace even
though no process is handed a value. The commitment is sound because the
announced bit is a ghost output: it is program data for no component, so no
process is answered with the internal choice. The guard `(!bnd) ∈ excluded` is
the binding witness either way — `!bnd` is a bit that no extension can hand out
— whether the round goes on to hand out `bnd` or hands out nothing at all.

## Provenance (D14/D15)

* **D14 (repair, load-bearing).** The source blueprint's TS 2 certifies binding
  by a *single* correct witness (`∃ id ∉ F, call id = b`), and grade-1 / grade-0 dissent
  likewise by a single correct dissenter. That singular witness is the same
  provenance loss the D13 repair removes from Transition System 1, one level
  down: the witness may
  be corrupted later in the trace, after which nothing attributes the outcome to
  a never-corrupted input — and `hybrid` built on this TS 2 provably violates
  the papers' Validity (deterministic witness at `n = 4, f = 1`, inputs
  `1,0,0,0`: bind at `1` off the sole `1`-holder, `retGrade1`-adopt everywhere,
  round-1 unanimity decides `1`, `fail 0`, `retABA 1 1` — never-corrupted
  processes all input `0`). ABDY22's implementation carries the `f + 1` via
  Valid-set relay thresholds; TS 2 abstracted it to one witness.
* **D15 (the repair).** Every certificate is a count
  `f + 1 ≤ #{id | call id = some b ∨ id ∈ F}` at the relevant bit — exactly
  TS 1's `InputSupport` shape (D13), directly `F`-blind: the count is monotone in `F`
  and in `call`, so it is immune to later `fail`s. On the exclusion set the
  counts sit at three places. `bindUnset b` counts support for the bit it
  *spares*, `!b`; the `retGrade1` dissent guard counts support for the bit it does
  *not* hand out, `!v`; `retGrade0` counts support for both bits. Provenance survives
  verbatim: `F` is monotone with `|F_final| ≤ f`, so among `f + 1` distinct
  supporters some member is outside the *final* `F`, hence outside the current
  `F`, hence a never-corrupted genuine caller — corrupt supporters are paid for
  by the `F` budget itself, with no phantom-call bookkeeping. Chaining the two:
  a bit `v` handed out at grade `≥ 1` requires `(!v) ∈ excluded`, and the
  `bindUnset (!v)` that put it there certified `f + 1` F-blind supporters of
  `!(!v) = v`; the budget pigeonhole then recovers a never-corrupted genuine
  caller of `v` behind every value-bearing return.

* **D19 (the state shape).** The source blueprint's TS 2 carries a bound value
  `bind ∈ {0, 1, ⊥}`. The exclusion set is the excluded-bit form of that
  value: `excluded ∈ {∅, {b}}`, embedding `bind = ⊥ ↦ excluded = ∅` and
  `bind = b ↦ excluded = {!b}`. The two states therefore differ in the guards, not
  in the cardinality. The blueprint's `bind = some v` guard on the
  value-bearing returns becomes the pair `v ∉ excluded ∧ (!v) ∈ excluded`, its
  `bind = none` guard on binding becomes `excluded = ∅`, and the grade-0 return's
  binding obligation `bind ≠ ⊥` becomes `(!bnd) ∈ excluded`. The source puts the
  bound value on the grade-0 return label; here `bnd` is that value, announced on
  every return label as a ghost output.

Every transition is Dirac, so the instance is an LTS and the `ForwardLTS`
correspondence applies. `fail` is the determinised D1 `corrupt`; the family
(`GBCA.specFamily`) broadcasts it to all rounds.
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
  /-- The exclusion set: the bits the instance can no longer hand out.
  Monotone, written at most once, by `bindUnset`. -/
  excluded : Finset Bool
  /-- The grade lock: `some true` after a grade-2 return, `some false` after a
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

/-! ### Corruption frame lemmas

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
  /-- Binding: a quorum has spoken and `f + 1` processes support the surviving
  bit `!b` (D15, InputSupport form: caller or `F`-member); exclude `b`. Fires at most
  once per instance — the guard is `excluded = ∅` — and `excluded` never shrinks. -/
  | bindUnset (s : SpecState P.n) (b : Bool)
      (hq : s.quorum P)
      (hw : P.f + 1 ≤ (Finset.univ.filter
        (fun id => s.call id = some (!b) ∨ id ∈ s.F)).card)
      (hd0 : s.excluded = ∅) :
      Step P r s .tau (PMF.pure { s with excluded := insert b s.excluded })
  /-- Grade-1 return: adopt the surviving bit `v` (`f + 1` dissenting supporters,
  D15). The guard pair `v ∉ excluded`, `(!v) ∈ excluded` is graded agreement; the
  announced bit `bnd` is the one whose complement is excluded. -/
  | retGrade1 (s : SpecState P.n) (id : Fin P.n) (v : Bool) (bnd : Bool)
      (hlive : v ∉ s.excluded) (hexcluded : (!v) ∈ s.excluded)
      (hbnd : (!bnd) ∈ s.excluded)
      (hw : P.f + 1 ≤ (Finset.univ.filter
        (fun id' => s.call id' = some (!v) ∨ id' ∈ s.F)).card)
      (hr : s.ret id = false) :
      Step P r s (.retG r id (.grade1 v) bnd)
        (PMF.pure { s with ret := Function.update s.ret id true })
  /-- Grade-2 return: decide the surviving bit `v` (locks the grade at 2). Same guard pair and same
  announced bit as `retGrade1`. -/
  | retGrade2 (s : SpecState P.n) (id : Fin P.n) (v : Bool) (bnd : Bool)
      (hlive : v ∉ s.excluded) (hexcluded : (!v) ∈ s.excluded)
      (hbnd : (!bnd) ∈ s.excluded)
      (hg : s.grade = none ∨ s.grade = some true)
      (hr : s.ret id = false) :
      Step P r s (.retG r id (.grade2 v) bnd)
        (PMF.pure { s with grade := some true, ret := Function.update s.ret id true })
  /-- Grade-0 return: no output, but the bound bit is announced. The guard `(!bnd) ∈ excluded` is
  the Graded Binding witness, valid in every extension because `excluded` only grows, and it names
  `bnd` as the surviving bit. Both bits carry `f + 1` F-blind support (D15), which is what makes
  handing out no bit the right answer; the grade is locked at 0. -/
  | retGrade0 (s : SpecState P.n) (id : Fin P.n) (bnd : Bool)
      (hbnd : (!bnd) ∈ s.excluded)
      (hwT : P.f + 1 ≤ (Finset.univ.filter
        (fun id' => s.call id' = some true ∨ id' ∈ s.F)).card)
      (hwF : P.f + 1 ≤ (Finset.univ.filter
        (fun id' => s.call id' = some false ∨ id' ∈ s.F)).card)
      (hg : s.grade = none ∨ s.grade = some false)
      (hr : s.ret id = false) :
      Step P r s (.retG r id .grade0 bnd)
        (PMF.pure { s with grade := some false, ret := Function.update s.ret id true })
  /-- Corruption (deviation D1). -/
  | fail (s : SpecState P.n) (id : Fin P.n) :
      Step P r s (.fail id) (PMF.pure (s.corrupt P id))

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
    System (ℕ → SpecState P.n) (Label P.n) :=
  System.family (specInst P) Label.gbcaRound Label.isFail (failAct P)

/-- The GBCA spec family is an LTS. -/
theorem specFamily_isLTS (P : Parameters) : (specFamily P).IsLTS :=
  System.family_isLTS (specInst_isLTS P) _ _ _

end GBCA
end ABA
end PLTS
