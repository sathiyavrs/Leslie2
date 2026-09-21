/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sathiya / Claude
-/

import Leslie2Protocols.ABA.Specifications.ABA
import Leslie2Protocols.Framework.TraceDistributionSupport

/-!
# Safety of the ABA specification

Validity and Agreement, stated as predicates on traces and proven for every
trace in the support of every achievable trace distribution of `ABA.spec`
(`ABA.spec_safe`).

Both predicates are read at never-corrupted returners. `SpecStep.retByzantine` lets
a corrupted process return an arbitrary bit at an arbitrary time, so nothing
constrains such a return and the unconditional forms are false. Corruption is
the trace-level notion `NeverCorrupted`, non-membership in every stage of the
corruption fold `failSet`. `AgreementTrace` requires two returns by
never-corrupted processes to carry the same bit. `ValidityTrace` is the
paper-form statement (D13): a return of `b` by a never-corrupted process is
*preceded* (positionally) by a `callABA id' b` event that is `id'`'s first
`callABA` of the trace, with the caller `id'` itself never corrupted. Both
axes of the witness are faithful to the papers. A process has one input, and
the first call is the event that carries it. The witnessing caller must be
never corrupted, not merely a member of some support set that a later `fail`
could taint.

The proof is invariant reasoning along genuine executions (via
`TraceSupport`), on two invariants:

* `SpecificationInvariant` — the state invariant, in two clauses: the corrupted set respects
  the budget (`F_le`), and the decision value carries `f + 1` F-blind
  supporters (`val_support`). The second clause is `SpecStep.decide`'s own guard
  at the one rule that writes `val`. Every rule that only grows the ghost
  record carries it by `InputSupport.mono`; `SpecStep.callByzantine`, whose write may
  replace a recorded bit, carries it by `InputSupport.callByzantine` instead, the writer
  being counted through the `F` disjunct.
* `ValidityInvariant` — the label-history-aware invariant, in four clauses. The corrupted
  set is exactly the fold of D1-`corrupt` over the labels seen so far
  (`F_eq`), `SpecificationInvariant` holds (`invariant`), and the ghost record agrees with the
  history at every uncorrupted process: a recorded input is attributed either
  to the corruption of its own entry or to the first `callABA` of its process
  (`input_source`), and an uncorrupted process whose first `callABA` carries `b`
  has `b` recorded (`source_input`). The two record clauses carry each other at
  `SpecStep.callSet`, whose guard is the empty entry: by `source_input` such an
  entry says no earlier `callABA` of that process was recorded, so the label
  the rule carries is the first. `SpecStep.callByzantine` takes `input_source`'s
  corruption disjunct.

Both branches run off one locator, `exists_retSite`: a `retABA` at trace
position `m` sits at an execution position whose pre-state carries `ValidityInvariant`
over the label prefix, has corrupted set the fold at `m`, and each process's
first `callABA` of that prefix reappears below `m` in the trace, first there
as well.

Agreement rests on `SpecificationInvariant.val_stable`: `SpecStep.decide` is the sole writer
of `val` and fires only from `val = ⊥`, so the decision value never changes
once written. A never-corrupted returner is outside the fold at `m`, hence
outside the pre-state's corrupted set, so `retABA_inv`'s second disjunct is
impossible and both returns read that one value.

Validity is a budget pigeonhole at the return. `retABA_inv` reads the returned
bit off the pre-state's decision value and `SpecificationInvariant.val_support` yields `f + 1`
supporters of that bit. Every supporter is either ghost-recorded or
ever-corrupted, and at most `f` ids are ever corrupted (`failSet` never
exceeds the budget), so some recorded supporter is never corrupted
(`exists_neverCorrupted_supporter`). Such a supporter lies in no prefix fold,
so `ValidityInvariant.input_source` yields its first `callABA` event.

The same pigeonhole in the state alone is `InputSupport.correct_supporter`: a
supported bit has an uncorrupted recorded inputter. It is what makes the
mixedness guard on `SpecStep.coinFlip` unsatisfiable under honest unanimity,
which is where the specification holds the liveness half of Validity.
-/

open Stream'

namespace PLTS
namespace ABA

variable {P : Parameters}

/-! ### The trace-level corruption fold -/

/-- One D1-`corrupt` on a bare corrupted set: insert when the budget allows. -/
def corruptSet (P : Parameters) (id : Fin P.n) (F : Finset (Fin P.n)) : Finset (Fin P.n) :=
  if id ∉ F ∧ F.card < P.f then insert id F else F

/-- Fold one label into the corrupted set: `corruptSet` on `fail id`, identity
on every other label. -/
def failStep (P : Parameters) (F : Finset (Fin P.n)) : Label P.n → Finset (Fin P.n)
  | .fail id => corruptSet P id F
  | _ => F

/-- The corrupted set determined by a label list: the fold of D1-`corrupt`
over its `fail` labels. -/
def failSetOfList (P : Parameters) (L : List (Label P.n)) : Finset (Fin P.n) :=
  L.foldl (failStep P) ∅

/-- The corrupted set after the first `k` labels of a trace. -/
def failSet (P : Parameters) (t : Seq (Label P.n)) : ℕ → Finset (Fin P.n)
  | 0 => ∅
  | k + 1 =>
    match t.get? k with
    | some l => failStep P (failSet P t k) l
    | none => failSet P t k

/-- `id` is never corrupted along the trace `t`. -/
def NeverCorrupted (P : Parameters) (t : Seq (Label P.n)) (id : Fin P.n) : Prop :=
  ∀ k, id ∉ failSet P t k

/-! ### The trace-level safety predicates -/

/-- **Validity** (paper form, D13): every return of `b` (at any trace
position `m`) by a never-corrupted process is preceded by a `callABA id' b`
event that is `id'`'s first `callABA` of the trace, with the caller `id'`
never corrupted anywhere along the trace. A process has one input, and its
first call is the event that carries it. -/
def ValidityTrace (P : Parameters) (t : Seq (Label P.n)) : Prop :=
  ∀ m id b, t.get? m = some (Label.retABA id b) → NeverCorrupted P t id →
    ∃ k, k < m ∧ ∃ id', t.get? k = some (Label.callABA id' b) ∧
      NeverCorrupted P t id' ∧
      ∀ k' < k, ∀ b', t.get? k' ≠ some (Label.callABA id' b')

/-- **Agreement** (trace form): any two returns by never-corrupted processes
carry the same bit. -/
def AgreementTrace (P : Parameters) (t : Seq (Label P.n)) : Prop :=
  ∀ id b id' b', Label.retABA id b ∈ t → Label.retABA id' b' ∈ t →
    NeverCorrupted P t id → NeverCorrupted P t id' → b = b'

/-! ### Budget and monotonicity of the corruption fold -/

@[simp] theorem failSet_zero (t : Seq (Label P.n)) : failSet P t 0 = ∅ := rfl

theorem failSet_succ (t : Seq (Label P.n)) (k : ℕ) :
    failSet P t (k + 1) =
      match t.get? k with
      | some l => failStep P (failSet P t k) l
      | none => failSet P t k := rfl

theorem subset_failStep (F : Finset (Fin P.n)) (l : Label P.n) :
    F ⊆ failStep P F l := by
  cases l <;> try exact fun _ h => h
  case fail id =>
    change F ⊆ corruptSet P id F
    unfold corruptSet
    split
    · exact Finset.subset_insert _ _
    · exact Finset.Subset.refl _

theorem failStep_card_le {F : Finset (Fin P.n)} (h : F.card ≤ P.f)
    (l : Label P.n) : (failStep P F l).card ≤ P.f := by
  cases l <;> try exact h
  case fail id =>
    change (corruptSet P id F).card ≤ P.f
    unfold corruptSet
    split
    · next hc =>
      have h1 := Finset.card_insert_le id F
      have h2 := hc.2
      omega
    · exact h

theorem failSet_card_le (t : Seq (Label P.n)) :
    ∀ k, (failSet P t k).card ≤ P.f := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
    rw [failSet_succ]
    cases hg : t.get? k with
    | some l => exact failStep_card_le ih l
    | none => exact ih

theorem failSet_mono (t : Seq (Label P.n)) {k k' : ℕ} (h : k ≤ k') :
    failSet P t k ⊆ failSet P t k' := by
  induction k' with
  | zero =>
    obtain rfl : k = 0 := Nat.le_zero.mp h
    exact Finset.Subset.refl _
  | succ m ih =>
    by_cases hk : k = m + 1
    · subst hk; exact Finset.Subset.refl _
    · refine (ih (by omega)).trans ?_
      rw [failSet_succ]
      cases hg : t.get? m with
      | some l => exact subset_failStep _ l
      | none => exact fun _ hx => hx

theorem failSetOfList_append (L : List (Label P.n)) (l : Label P.n) :
    failSetOfList P (L ++ [l]) = failStep P (failSetOfList P L) l := by
  unfold failSetOfList
  rw [List.foldl_append, List.foldl_cons, List.foldl_nil]

/-- The list-level fold is monotone under extending the list by one label. -/
theorem failSetOfList_subset_append (L : List (Label P.n)) (l : Label P.n) :
    failSetOfList P L ⊆ failSetOfList P (L ++ [l]) := by
  rw [failSetOfList_append]
  exact subset_failStep _ l

/-- Folding over a filtered list agrees with folding over the original when
the filter keeps every `fail` label. -/
theorem foldl_failStep_filter {p : Label P.n → Bool}
    (hp : ∀ id : Fin P.n, p (.fail id) = true) :
    ∀ (L : List (Label P.n)) (F : Finset (Fin P.n)),
      (L.filter p).foldl (failStep P) F = L.foldl (failStep P) F := by
  intro L
  induction L with
  | nil => intro F; rfl
  | cons l L ih =>
    intro F
    by_cases hl : p l = true
    · rw [List.filter_cons_of_pos hl, List.foldl_cons, List.foldl_cons]
      exact ih _
    · have hstep : failStep P F l = F := by
        cases l <;> first | rfl | exact absurd (hp _) hl
      rw [List.filter_cons_of_neg (by simpa using hl), List.foldl_cons, hstep]
      exact ih F

/-- `failSetOfList` ignores filtering that keeps every `fail` label. -/
theorem failSetOfList_filter {p : Label P.n → Bool}
    (hp : ∀ id : Fin P.n, p (.fail id) = true) (L : List (Label P.n)) :
    failSetOfList P (L.filter p) = failSetOfList P L :=
  foldl_failStep_filter hp L ∅

/-- The trace-level fold over `Seq.ofList` is the list-level fold of the
`take`-prefix. -/
theorem failSet_ofList (L : List (Label P.n)) :
    ∀ k, failSet P (Seq.ofList L) k = failSetOfList P (L.take k) := by
  intro k
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [failSet_succ]
    cases hg : (Seq.ofList L).get? k with
    | some l =>
      change failStep P (failSet P (Seq.ofList L) k) l = _
      rw [Seq.ofList_get?] at hg
      rw [ih, List.take_add_one, hg, Option.toList_some, failSetOfList_append]
    | none =>
      change failSet P (Seq.ofList L) k = _
      rw [Seq.ofList_get?] at hg
      rw [ih, List.take_add_one, hg, Option.toList_none, List.append_nil]

/-- A finite set each of whose members is eventually corrupted is corrupted
at a single uniform stage (`failSet` is monotone in the stage). -/
theorem exists_uniform_prefix (t : Seq (Label P.n)) (S : Finset (Fin P.n)) :
    (∀ id ∈ S, ∃ k, id ∈ failSet P t k) →
    ∃ K, ∀ id ∈ S, id ∈ failSet P t K := by
  classical
  induction S using Finset.induction_on with
  | empty => exact fun _ => ⟨0, fun id h => absurd h (Finset.notMem_empty id)⟩
  | insert a S ha ih =>
    intro h
    obtain ⟨ka, hka⟩ := h a (Finset.mem_insert_self a S)
    obtain ⟨K, hK⟩ := ih fun id hid => h id (Finset.mem_insert_of_mem hid)
    refine ⟨max ka K, fun id hid => ?_⟩
    rcases Finset.mem_insert.mp hid with rfl | hid
    · exact failSet_mono t (le_max_left ka K) hka
    · exact failSet_mono t (le_max_right ka K) (hK id hid)

/-! ### Two readings of the support count -/

/-- A corrupted call preserves support. The write at `id` may replace a
recorded `v` by the other bit, so `InputSupport.mono` does not apply. The count is
`F`-blind, however, and `id ∈ s.F`, so `id` is counted through the second
disjunct whatever its entry holds; every other entry is untouched. -/
theorem InputSupport.callByzantine {s : SpecState P.n} {id : Fin P.n} {b v : Bool}
    (h : InputSupport P s v) (hF : id ∈ s.F) :
    InputSupport P { s with input := Function.update s.input id (some b) } v := by
  refine le_trans h (Finset.card_le_card ?_)
  intro i hi
  rw [Finset.mem_filter] at hi ⊢
  refine ⟨hi.1, ?_⟩
  by_cases h_eq : i = id
  · subst h_eq; exact Or.inr hF
  · refine hi.2.imp (fun hin => ?_) (fun hm => hm)
    change Function.update s.input id (some b) i = some v
    rwa [Function.update_of_ne h_eq]

/-- **The budget pigeonhole on a single bit.** A bit with `f + 1` supporters
has one that is not corrupted in the state, and that one is recorded. This is
what makes the mixedness guard `SpecStep.coinFlip`'s `hmix` unsatisfiable under
honest unanimity: were both bits supported, each would carry a recorded
uncorrupted inputter, and the two inputters disagree. -/
theorem InputSupport.correct_supporter {s : SpecState P.n} {b : Bool}
    (h : InputSupport P s b) (hF : s.F.card ≤ P.f) :
    ∃ id, id ∉ s.F ∧ s.input id = some b := by
  by_contra hc
  push_neg at hc
  have hsub : Finset.univ.filter (fun id => s.input id = some b ∨ id ∈ s.F) ⊆ s.F := by
    intro i hi
    rcases (Finset.mem_filter.mp hi).2 with hin | hmem
    · by_contra hnot
      exact hc i hnot hin
    · exact hmem
  have h1 := Finset.card_le_card hsub
  unfold InputSupport at h
  omega

/-! ### The state invariant -/

/-- The state invariant of `ABA.spec`: the corrupted set respects the budget,
and the decision value carries `f + 1` F-blind supporters (D13). -/
structure SpecificationInvariant (P : Parameters) (s : SpecState P.n) : Prop where
  /-- The corrupted set stays inside the budget. -/
  F_le : s.F.card ≤ P.f
  /-- The decision value has `f + 1` supporters. -/
  val_support : ∀ v, s.val = some v → InputSupport P s v

theorem SpecificationInvariant.initial (P : Parameters) : SpecificationInvariant P
  (SpecState.initial P.n) where
  F_le := by
    simp [SpecState.initial]
  val_support := fun _ h => absurd h (by simp [SpecState.initial])

/-! Field stability of `corrupt`. -/

section Corrupt

variable (s : SpecState P.n) (id : Fin P.n)

@[simp] theorem corrupt_input : (s.corrupt P id).input = s.input := by
  unfold SpecState.corrupt; split <;> rfl

@[simp] theorem corrupt_ret : (s.corrupt P id).ret = s.ret := by
  unfold SpecState.corrupt; split <;> rfl

@[simp] theorem corrupt_val : (s.corrupt P id).val = s.val := by
  unfold SpecState.corrupt; split <;> rfl

@[simp] theorem corrupt_mode : (s.corrupt P id).mode = s.mode := by
  unfold SpecState.corrupt; split <;> rfl

/-- `corrupt` acts on `F` exactly as the bare-set fold step `corruptSet`. -/
theorem corrupt_F : (s.corrupt P id).F = corruptSet P id s.F := by
  unfold SpecState.corrupt corruptSet
  split <;> rfl

theorem corrupt_F_subset : s.F ⊆ (s.corrupt P id).F := by
  unfold SpecState.corrupt
  split
  · exact Finset.subset_insert _ _
  · exact Finset.Subset.refl _

theorem corrupt_card_le (hF : s.F.card ≤ P.f) : (s.corrupt P id).F.card ≤ P.f := by
  unfold SpecState.corrupt
  split
  · next hc =>
    show (insert id s.F).card ≤ P.f
    have h2 := hc.2
    have h3 := Finset.card_insert_le id s.F
    omega
  · exact hF

end Corrupt

/-- **Invariant preservation.** `SpecificationInvariant` is preserved by every step. -/
theorem SpecificationInvariant.step {s : SpecState P.n} {l : Label P.n} {μ : PMF (SpecState P.n)}
    {s' : SpecState P.n} (hI : SpecificationInvariant P s)
    (hstep : SpecStep P s l μ) (hs' : s' ∈ μ.support) : SpecificationInvariant P s' := by
  cases hstep with
  | callSet id b h =>
    -- the write is at an empty entry, so the record only grows and
    -- `InputSupport.mono` carries the support
    rw [PMF.mem_support_pure_iff] at hs'; subst hs'
    have hnew : ∀ id' v, s.input id' = some v →
        Function.update s.input id (some b) id' = some v := by
      intro id' v hv
      by_cases h_eq : id' = id
      · subst h_eq; rw [hv] at h; exact absurd h (by simp)
      · rw [Function.update_of_ne h_eq]; exact hv
    exact ⟨hI.F_le, fun v hv =>
      (hI.val_support v hv).mono (fun i => hnew i v) (Finset.Subset.refl _)⟩
  | callLoop id b h =>
    -- the loop writes nothing
    rw [PMF.mem_support_pure_iff] at hs'; subst hs'
    exact hI
  | coinFlip hm hv hmix =>
    -- every branch writes `mode` alone
    rw [PMF.mem_support_map_iff] at hs'
    obtain ⟨o, -, rfl⟩ := hs'
    cases o <;> exact ⟨hI.F_le, hI.val_support⟩
  | decide b hv hs hm =>
    -- the guard `hs` is the conclusion
    rw [PMF.mem_support_pure_iff] at hs'; subst hs'
    refine ⟨hI.F_le, fun v hvv => ?_⟩
    obtain rfl : b = v := Option.some.inj (show (some b : Option Bool) = some v from hvv)
    exact hs
  | ret id b h₁ h₂ =>
    rw [PMF.mem_support_pure_iff] at hs'; subst hs'
    exact ⟨hI.F_le, hI.val_support⟩
  | fail id hnew hbud =>
    -- `F` grows inside the budget, and `InputSupport` is monotone in it
    rw [PMF.mem_support_pure_iff] at hs'; subst hs'
    refine ⟨corrupt_card_le s id hI.F_le, fun v hv => ?_⟩
    rw [corrupt_val] at hv
    exact (hI.val_support v hv).mono
      (fun i hh => by rw [corrupt_input]; exact hh) (corrupt_F_subset s id)
  | callByzantine id b b' hF =>
    -- `val` and `F` are untouched; `id ∈ F` keeps the overwritten field counted
    rw [PMF.mem_support_pure_iff] at hs'; subst hs'
    exact ⟨hI.F_le, fun v hv => (hI.val_support v hv).callByzantine hF⟩
  | retByzantine id b hF =>
    rw [PMF.mem_support_pure_iff] at hs'; subst hs'
    exact hI

/-- **Write-once decision.** `SpecStep.decide` is the sole writer of `val` and
fires only from `val = ⊥`, so `val = some b` is preserved by every step. -/
theorem SpecificationInvariant.val_stable {s : SpecState P.n} {l : Label P.n}
    {μ : PMF (SpecState P.n)} {s' : SpecState P.n} {b : Bool}
    (hv : s.val = some b) (hstep : SpecStep P s l μ) (hs' : s' ∈ μ.support) :
    s'.val = some b := by
  cases hstep with
  | callSet id b' h =>
    rw [PMF.mem_support_pure_iff] at hs'; subst hs'; exact hv
  | callLoop id b' h =>
    rw [PMF.mem_support_pure_iff] at hs'; subst hs'; exact hv
  | coinFlip hm hv' hmix =>
    rw [PMF.mem_support_map_iff] at hs'
    obtain ⟨o, -, rfl⟩ := hs'
    cases o <;> exact hv
  | decide b' hv' hs hm =>
    exact absurd hv (by rw [hv']; simp)
  | ret id b' h₁ h₂ =>
    rw [PMF.mem_support_pure_iff] at hs'; subst hs'; exact hv
  | fail id hnew hbud =>
    rw [PMF.mem_support_pure_iff] at hs'; subst hs'
    rw [corrupt_val]; exact hv
  | callByzantine id b' b'' hF =>
    rw [PMF.mem_support_pure_iff] at hs'; subst hs'; exact hv
  | retByzantine id b' hF =>
    rw [PMF.mem_support_pure_iff] at hs'; subst hs'; exact hv

/-! ### The first call of a label list -/

/-- The bit of the first `callABA id _` label of a label list, and `none` when
the list carries no such label. -/
def firstCall {n : ℕ} : List (Label n) → Fin n → Option Bool
  | [], _ => none
  | List.cons (Label.callABA id' b) L, id => if id' = id then some b else firstCall L id
  | List.cons _ L, id => firstCall L id

@[simp] theorem firstCall_nil {n : ℕ} (id : Fin n) :
    firstCall ([] : List (Label n)) id = none := rfl

/-- `firstCall` reads the first of two joined lists that carries a call at
`id`. -/
theorem firstCall_append {n : ℕ} (L L' : List (Label n)) (id : Fin n) :
    firstCall (L ++ L') id = (firstCall L id).or (firstCall L' id) := by
  induction L with
  | nil => simp
  | cons l L ih =>
    cases l <;> simp only [List.cons_append, firstCall, ih]
    split <;> simp

/-- A first call already in the history stays the first call. -/
theorem firstCall_append_of_some {n : ℕ} {L : List (Label n)} {id : Fin n} {b : Bool}
    (h : firstCall L id = some b) (l : Label n) : firstCall (L ++ [l]) id = some b := by
  rw [firstCall_append, h]; rfl

/-- Extending a list that carries no call at `id` by `callABA id b` makes
that label `id`'s first call. -/
theorem firstCall_append_self {n : ℕ} {L : List (Label n)} {id : Fin n}
    (h : firstCall L id = none) (b : Bool) :
    firstCall (L ++ [Label.callABA id b]) id = some b := by
  rw [firstCall_append, h]
  simp [firstCall]

/-- A label that is not a call at `id` leaves `id`'s first call where it is. -/
theorem firstCall_append_of_ne_call {n : ℕ} (L : List (Label n)) {l : Label n}
    {id : Fin n} (h : ∀ b, l ≠ Label.callABA id b) :
    firstCall (L ++ [l]) id = firstCall L id := by
  have hl : firstCall [l] id = none := by
    cases l
    case callABA id' b => exact if_neg (fun hid => h b (by rw [hid]))
    all_goals rfl
  rw [firstCall_append, hl]
  simp

/-- `firstCall` ignores filtering that keeps every `callABA` label. -/
theorem firstCall_filter {n : ℕ} {p : Label n → Bool}
    (hp : ∀ (id : Fin n) (b : Bool), p (.callABA id b) = true) (L : List (Label n))
    (id : Fin n) : firstCall (L.filter p) id = firstCall L id := by
  induction L with
  | nil => rfl
  | cons l L ih =>
    by_cases hl : p l = true
    · rw [List.filter_cons_of_pos hl]
      cases l <;> simp only [firstCall, ih]
    · have hstep : firstCall (l :: L) id = firstCall L id := by
        cases l <;> first | rfl | exact absurd (hp _ _) hl
      rw [List.filter_cons_of_neg (by simpa using hl), hstep]
      exact ih

/-- The first `callABA id _` of a list sits at a position no earlier
`callABA id _` precedes. -/
theorem firstCall_getElem? {n : ℕ} :
    ∀ (L : List (Label n)) {id : Fin n} {b : Bool}, firstCall L id = some b →
      ∃ k : ℕ, L[k]? = some (Label.callABA id b) ∧
        ∀ k' < k, ∀ b', L[k']? ≠ some (Label.callABA id b') := by
  intro L
  induction L with
  | nil => intro id b h; exact absurd h (by simp)
  | cons l L ih =>
    intro id b h
    have hlater : (∀ b', l ≠ Label.callABA id b') → firstCall L id = some b →
        ∃ k : ℕ, (l :: L)[k]? = some (Label.callABA id b) ∧
          ∀ k' < k, ∀ b'', (l :: L)[k']? ≠ some (Label.callABA id b'') := by
      intro hne hL
      obtain ⟨k, hk, hmin⟩ := ih hL
      refine ⟨k + 1, by simpa using hk, ?_⟩
      intro k' hk' b'' hcon
      cases k' with
      | zero => exact hne b'' (by simpa using hcon)
      | succ j => exact hmin j (by omega) b'' (by simpa using hcon)
    cases l
    case callABA id' b₀ =>
      by_cases hid : id' = id
      · subst hid
        rw [firstCall, if_pos rfl] at h
        obtain rfl := Option.some.inj h
        exact ⟨0, rfl, fun k' hk' => absurd hk' (Nat.not_lt_zero k')⟩
      · rw [firstCall, if_neg hid] at h
        exact hlater (fun b'' hcon => by injection hcon with hidd _; exact hid hidd) h
    all_goals exact hlater (by simp) h

/-- A first `callABA id _` inside a prefix is a first `callABA id _` of the
whole list, at a position below the prefix length. -/
theorem firstCall_take_pullback {n : ℕ} {L : List (Label n)} {m : ℕ} {id : Fin n}
    {b : Bool} (h : firstCall (L.take m) id = some b) :
    ∃ k : ℕ, k < m ∧ L[k]? = some (Label.callABA id b) ∧
      ∀ k' < k, ∀ b', L[k']? ≠ some (Label.callABA id b') := by
  obtain ⟨k, hk, hmin⟩ := firstCall_getElem? (L.take m) h
  have hk_lt : k < m := by
    have h1 := (List.getElem?_eq_some_iff.mp hk).1
    have h2 : (L.take m).length ≤ m := by
      simp
    omega
  refine ⟨k, hk_lt, by rwa [List.getElem?_take_of_lt hk_lt] at hk, ?_⟩
  intro k' hk' b' hcon
  exact hmin k' hk' b' (by rw [List.getElem?_take_of_lt (by omega)]; exact hcon)

/-! ### The label-history-aware invariant (for Validity) -/

/-- The history-aware invariant: the ghost record agrees with the label
history at every uncorrupted process, and the corrupted set is exactly the
fold of D1-`corrupt` over the labels seen so far. `input_source` attributes a
recorded input either to the corruption of its own entry or to the process's
first `callABA` in the history. The first disjunct is what `SpecStep.callByzantine`
takes: its write is unrelated to the label it carries, and its guard puts the
writer in the corrupted set. `source_input` is the converse reading at an
uncorrupted process, and it is what reads an empty entry as saying no earlier
`callABA` of that process was recorded. -/
structure ValidityInvariant (P : Parameters) (pre : List (Label P.n)) (s : SpecState P.n) : Prop
  where
  invariant : SpecificationInvariant P s
  input_source : ∀ id b, s.input id = some b →
    id ∈ failSetOfList P pre ∨ firstCall pre id = some b
  source_input : ∀ id b, id ∉ failSetOfList P pre → firstCall pre id = some b →
    s.input id = some b
  F_eq : s.F = failSetOfList P pre

theorem ValidityInvariant.initial (P : Parameters) : ValidityInvariant P [] (SpecState.initial P.n)
  where
  invariant := SpecificationInvariant.initial P
  input_source := fun _ _ h => absurd h (by simp [SpecState.initial])
  source_input := fun _ _ _ h => absurd h (by simp)
  F_eq := rfl

/-- **History-invariant preservation.** -/
theorem ValidityInvariant.step {pre : List (Label P.n)} {s : SpecState P.n} {l : Label P.n}
    {μ : PMF (SpecState P.n)} {s' : SpecState P.n}
    (hI : ValidityInvariant P pre s) (hstep : SpecStep P s l μ) (hs' : s' ∈ μ.support) :
    ValidityInvariant P (pre ++ [l]) s' := by
  have mono : ∀ {id' : Fin P.n} {b' : Bool},
      (id' ∈ failSetOfList P pre ∨ firstCall pre id' = some b') →
      (id' ∈ failSetOfList P (pre ++ [l]) ∨ firstCall (pre ++ [l]) id' = some b') :=
    fun h => h.imp (fun hm => failSetOfList_subset_append pre l hm)
      (fun hf => firstCall_append_of_some hf l)
  have hnc : ∀ {id' : Fin P.n}, id' ∉ failSetOfList P (pre ++ [l]) → id' ∉ failSetOfList P pre :=
    fun h hm => h (failSetOfList_subset_append pre l hm)
  have h_inv' := hI.invariant.step hstep hs'
  cases hstep with
  | callSet id b h =>
    -- the guard is the empty entry, which by `source_input` says no earlier
    -- `callABA id _` was recorded, so this label is `id`'s first call
    rw [PMF.mem_support_pure_iff] at hs'; subst hs'
    have hfresh : id ∈ failSetOfList P pre ∨ firstCall pre id = none := by
      by_cases hmem : id ∈ failSetOfList P pre
      · exact Or.inl hmem
      · refine Or.inr ?_
        cases hf : firstCall pre id with
        | none => rfl
        | some c => exact absurd (hI.source_input id c hmem hf) (by rw [h]; simp)
    refine ⟨h_inv', ?_, ?_, ?_⟩
    · intro id' b' h_in
      replace h_in : Function.update s.input id (some b) id' = some b' := h_in
      by_cases h_eq : id' = id
      · subst h_eq
        rw [Function.update_self] at h_in
        obtain rfl := Option.some.inj h_in
        exact hfresh.imp (fun hm => failSetOfList_subset_append pre _ hm)
          (fun hf => firstCall_append_self hf _)
      · rw [Function.update_of_ne h_eq] at h_in
        exact mono (hI.input_source id' b' h_in)
    · intro id' b' hmem hf
      by_cases h_eq : id' = id
      · subst h_eq
        rw [firstCall_append_self (hfresh.resolve_left (hnc hmem)) b] at hf
        simpa using hf
      · have hne : ∀ b'', Label.callABA id b ≠ Label.callABA id' b'' := by
          intro b'' hcon; injection hcon with hid _; exact h_eq hid.symm
        rw [firstCall_append_of_ne_call pre hne] at hf
        change Function.update s.input id (some b) id' = some b'
        rw [Function.update_of_ne h_eq]
        exact hI.source_input id' b' (hnc hmem) hf
    · change s.F = failSetOfList P (pre ++ [Label.callABA id b])
      rw [failSetOfList_append]
      exact hI.F_eq
  | callLoop id b h =>
    -- the loop writes nothing, and its guard is a filled entry, which by
    -- `input_source` already holds an earlier call's bit at an uncorrupted `id`
    rw [PMF.mem_support_pure_iff] at hs'
    rw [hs'] at h_inv' ⊢
    refine ⟨h_inv', fun id' b' h_in => mono (hI.input_source id' b' h_in), ?_, ?_⟩
    · intro id' b' hmem hf
      by_cases h_eq : id' = id
      · subst h_eq
        obtain ⟨c, hc⟩ : ∃ c, s.input id' = some c := Option.ne_none_iff_exists'.mp h
        have hpre : firstCall pre id' = some c :=
          (hI.input_source id' c hc).resolve_left (hnc hmem)
        rw [firstCall_append_of_some hpre _] at hf
        rw [hc, hf]
      · have hne : ∀ b'', Label.callABA id b ≠ Label.callABA id' b'' := by
          intro b'' hcon; injection hcon with hid _; exact h_eq hid.symm
        rw [firstCall_append_of_ne_call pre hne] at hf
        exact hI.source_input id' b' (hnc hmem) hf
    · rw [failSetOfList_append]
      exact hI.F_eq
  | coinFlip hm hv hmix =>
    rw [PMF.mem_support_map_iff] at hs'
    obtain ⟨o, -, rfl⟩ := hs'
    have hFeq : s.F = failSetOfList P (pre ++ [Label.tau]) := by
      rw [failSetOfList_append]; exact hI.F_eq
    have hsrc : ∀ id' b', id' ∉ failSetOfList P (pre ++ [Label.tau]) →
        firstCall (pre ++ [Label.tau]) id' = some b' → s.input id' = some b' := by
      intro id' b' hmem hf
      rw [firstCall_append_of_ne_call pre (by simp)] at hf
      exact hI.source_input id' b' (hnc hmem) hf
    cases o <;>
      exact ⟨h_inv', fun id' b' h_in => mono (hI.input_source id' b' h_in), hsrc, hFeq⟩
  | decide b hv hs hm =>
    rw [PMF.mem_support_pure_iff] at hs'; subst hs'
    refine ⟨h_inv', fun id' b' h_in => mono (hI.input_source id' b' h_in), ?_, ?_⟩
    · intro id' b' hmem hf
      rw [firstCall_append_of_ne_call pre (by simp)] at hf
      exact hI.source_input id' b' (hnc hmem) hf
    · change s.F = failSetOfList P (pre ++ [Label.tau])
      rw [failSetOfList_append]
      exact hI.F_eq
  | ret id b h₁ h₂ =>
    rw [PMF.mem_support_pure_iff] at hs'; subst hs'
    refine ⟨h_inv', fun id' b' h_in => mono (hI.input_source id' b' h_in), ?_, ?_⟩
    · intro id' b' hmem hf
      rw [firstCall_append_of_ne_call pre (by simp)] at hf
      exact hI.source_input id' b' (hnc hmem) hf
    · change s.F = failSetOfList P (pre ++ [Label.retABA id b])
      rw [failSetOfList_append]
      exact hI.F_eq
  | fail id hnew hbud =>
    rw [PMF.mem_support_pure_iff] at hs'; subst hs'
    refine ⟨h_inv', ?_, ?_, ?_⟩
    · intro id' b' h_in
      rw [corrupt_input] at h_in
      exact mono (hI.input_source id' b' h_in)
    · intro id' b' hmem hf
      rw [firstCall_append_of_ne_call pre (by simp)] at hf
      rw [corrupt_input]
      exact hI.source_input id' b' (hnc hmem) hf
    · rw [failSetOfList_append, corrupt_F, hI.F_eq]
      rfl
  | callByzantine id b b' hF =>
    -- the write is unrelated to the label, and the guard puts `id` in `F`
    rw [PMF.mem_support_pure_iff] at hs'; subst hs'
    have hFeq : s.F = failSetOfList P (pre ++ [Label.callABA id b]) := by
      rw [failSetOfList_append]; exact hI.F_eq
    refine ⟨h_inv', ?_, ?_, hFeq⟩
    · intro id' b'' h_in
      replace h_in : Function.update s.input id (some b') id' = some b'' := h_in
      by_cases h_eq : id' = id
      · subst h_eq
        exact Or.inl (failSetOfList_subset_append pre _ (hI.F_eq ▸ hF))
      · rw [Function.update_of_ne h_eq] at h_in
        exact mono (hI.input_source id' b'' h_in)
    · intro id' b'' hmem hf
      have h_eq : id' ≠ id := by
        rintro rfl; exact hmem (hFeq ▸ hF)
      have hne : ∀ b₀, Label.callABA id b ≠ Label.callABA id' b₀ := by
        intro b₀ hcon; injection hcon with hid _; exact h_eq hid.symm
      rw [firstCall_append_of_ne_call pre hne] at hf
      change Function.update s.input id (some b') id' = some b''
      rw [Function.update_of_ne h_eq]
      exact hI.source_input id' b'' (hnc hmem) hf
  | retByzantine id b hF =>
    -- the rule is a no-op, so the invariant only has to absorb the new label
    rw [PMF.mem_support_pure_iff] at hs'
    rw [hs'] at h_inv' ⊢
    refine ⟨h_inv', fun id' b' h_in => mono (hI.input_source id' b' h_in), ?_, ?_⟩
    · intro id' b' hmem hf
      rw [firstCall_append_of_ne_call pre (by simp)] at hf
      exact hI.source_input id' b' (hnc hmem) hf
    · rw [failSetOfList_append]
      exact hI.F_eq


/-! ### The safety theorem -/

/-- Inverting a `retABA` event: either the pre-state's decision value is the
returned bit, or the returning process is corrupted in the pre-state. The two
disjuncts are the two rules that carry the label, `SpecStep.ret` and
`SpecStep.retByzantine`. -/
private theorem retABA_inv {s : SpecState P.n} {id : Fin P.n} {b : Bool}
    {μ : PMF (SpecState P.n)} (hstep : SpecStep P s (.retABA id b) μ) :
    s.val = some b ∨ id ∈ s.F :=
  match hstep with
  | .ret _ _ _ h₁ _ => Or.inl h₁
  | .retByzantine _ _ _ hF => Or.inr hF

/-- Two decision values read along one genuine execution agree
(`k₁ ≤ k₂` case). -/
private theorem val_agree_le {e : AlterSeq (SpecState P.n) (Label P.n)}
    (he : is_exec e (spec P)) {k₁ k₂ : ℕ} (hk : k₁ ≤ k₂)
    {s₁ s₂ : SpecState P.n} {b b' : Bool}
    (hst₁ : e.stateAt k₁ = some s₁) (hst₂ : e.stateAt k₂ = some s₂)
    (hv₁ : s₁.val = some b) (hv₂ : s₂.val = some b') : b = b' := by
  have h_stable := is_exec_stable (sys := spec P) (fun s => s.val = some b)
    (fun s l μ s' hv hstep hs' => SpecificationInvariant.val_stable hv hstep hs')
    he k₁ k₂ s₁ s₂ hk hst₁ hst₂ hv₁
  rw [h_stable] at hv₂
  exact Option.some.inj hv₂

/-- The budget pigeonhole: `f + 1` supporters minus at most `f`
ever-corrupted ids leave a never-corrupted recorded inputter. -/
theorem exists_neverCorrupted_supporter {t : Seq (Label P.n)} {s : SpecState P.n}
    {v : Bool} {m : ℕ} (hsupp : InputSupport P s v) (hF : s.F = failSet P t m) :
    ∃ id, s.input id = some v ∧ NeverCorrupted P t id := by
  by_contra hc
  push_neg at hc
  have hall : ∀ id ∈ Finset.univ.filter
      (fun id => s.input id = some v ∨ id ∈ s.F), ∃ k, id ∈ failSet P t k := by
    intro id hid
    rcases (Finset.mem_filter.mp hid).2 with hin | hmem
    · have h1 := hc id hin
      unfold NeverCorrupted at h1
      push_neg at h1
      exact h1
    · exact ⟨m, hF ▸ hmem⟩
  obtain ⟨K, hK⟩ := exists_uniform_prefix t _ hall
  have h1 := Finset.card_le_card
    (show Finset.univ.filter (fun id => s.input id = some v ∨ id ∈ s.F)
        ⊆ failSet P t K from fun id hid => hK id hid)
  have h2 := failSet_card_le t K
  have h3 := hsupp
  unfold InputSupport at h3
  omega

/-- **The return locator.** A trace of positive probability is the external
filter of a genuine execution, and every `retABA` event at trace position `m`
sits at some execution position `j`. The pre-state `s` of that event carries
the history invariant over the label prefix, its corrupted set is the
trace-level fold at `m`, and each process's first `callABA` of that prefix
reappears at a trace position below `m`, first there as well. Both safety
predicates are read off this one
statement: Validity needs the invariant and the pushback, Agreement needs the
execution position and the fold. -/
private theorem exists_retSite (P : Parameters) {pe : ProbabilisticExecution (spec P)}
    (h_init : pe.initState = PMF.pure (spec P).init) (t : Seq (Label P.n))
    (h_ne : (spec P).traceProb pe t ≠ 0) :
    ∃ e : AlterSeq (SpecState P.n) (Label P.n), is_exec e (spec P) ∧
      ∀ m id b, t.get? m = some (Label.retABA id b) →
        ∃ (j : ℕ) (s : SpecState P.n) (μ : PMF (SpecState P.n))
          (pre : List (Label P.n)),
          e.stateAt j = some s ∧ SpecStep P s (Label.retABA id b) μ ∧
          ValidityInvariant P pre s ∧ s.F = failSet P t m ∧
          ∀ id' b', firstCall pre id' = some b' →
            ∃ k, k < m ∧ t.get? k = some (Label.callABA id' b') ∧
              ∀ k' < k, ∀ b'', t.get? k' ≠ some (Label.callABA id' b'') := by
  obtain ⟨e, labs, h_exec, h_map, h_t⟩ :=
    exists_exec_of_traceProb_ne_zero_ord pe h_init t h_ne
  rw [Seq.ofList_filter] at h_t
  -- generalise the external-label filter to an opaque Boolean predicate
  obtain ⟨p, hpfail, hpcall, h_t⟩ : ∃ p : Label P.n → Bool,
      (∀ id : Fin P.n, p (.fail id) = true) ∧
      (∀ (id : Fin P.n) (b : Bool), p (.callABA id b) = true) ∧
      Seq.ofList (labs.filter p) = t :=
    ⟨_, fun id => by simp, fun id b => by simp, h_t⟩
  refine ⟨e, h_exec, ?_⟩
  intro m id b h_ret
  -- trace position `m` pulls back to an execution event `j`
  rw [← h_t, Seq.ofList_get?] at h_ret
  obtain ⟨j, hj, hlen⟩ := filter_getElem?_pullback p labs m _ h_ret
  obtain ⟨s'', h_get⟩ : ∃ s'', e.trans.get? j = some (Label.retABA id b, s'') := by
    have hk : (e.trans.get? j).map Prod.fst = labs[j]? := by
      rw [← Seq.map_get?, h_map, Seq.ofList_get?]
    rw [hj] at hk
    cases hg : e.trans.get? j with
    | none => rw [hg] at hk; exact absurd hk (by simp)
    | some q =>
      rw [hg] at hk
      simp only [Option.map_some, Option.some.injEq] at hk
      exact ⟨q.2, by rw [← hk]⟩
  obtain ⟨s, μ, h_state, h_step, -⟩ := h_exec.1 j _ _ h_get
  have h_VI := is_exec_induction_labels (sys := spec P)
    (fun pre s => ValidityInvariant P pre s) (ValidityInvariant.initial P)
    (fun pre s l μ s' hI hstep hs' => hI.step hstep hs') h_exec j s h_state
  rw [AlterSeq.labelsUpTo_eq_take h_map j] at h_VI
  -- the trace-prefix transfer: `s.F` is the trace-level fold at position `m`
  have h_take : (labs.take j).filter p = (labs.filter p).take m :=
    take_filter_eq_take p labs hlen
  have h_transfer : s.F = failSet P t m := by
    rw [h_VI.F_eq, ← failSetOfList_filter hpfail (labs.take j), h_take,
      ← failSet_ofList, h_t]
  refine ⟨j, s, μ, labs.take j, h_state, h_step, h_VI, h_transfer, ?_⟩
  -- a first `callABA` of the prefix is a first `callABA` of the trace, below `m`
  intro id' b' h_first
  have h_firstf : firstCall ((labs.filter p).take m) id' = some b' := by
    rw [← h_take, firstCall_filter hpcall]
    exact h_first
  obtain ⟨k, hk_lt, hk, hmin⟩ := firstCall_take_pullback h_firstf
  refine ⟨k, hk_lt, ?_, ?_⟩
  · rw [← h_t, Seq.ofList_get?]
    exact hk
  · intro k' hk' b'' hcon
    rw [← h_t, Seq.ofList_get?] at hcon
    exact hmin k' hk' b'' hcon

/-- **Safety of the ABA specification**: every trace in the support of every
achievable trace distribution of `ABA.spec` satisfies Validity (paper form,
ordered, with a never-corrupted witness) and Agreement, both read at
never-corrupted returners. -/
theorem spec_safe (P : Parameters) :
    ∀ D ∈ achievableTraceDists (spec P), ∀ t, D t ≠ 0 →
      ValidityTrace P t ∧ AgreementTrace P t := by
  rintro D ⟨pe, h_init, h_D⟩ t h_ne
  rw [← h_D t] at h_ne
  obtain ⟨e, h_exec, hloc⟩ := exists_retSite P h_init t h_ne
  -- a never-corrupted returner is outside the fold at `m`, so `retABA_inv`'s
  -- second disjunct is impossible and the honest rule read `val`
  have h_correct : ∀ m id b, t.get? m = some (Label.retABA id b) →
      NeverCorrupted P t id →
      ∃ (j : ℕ) (s : SpecState P.n) (pre : List (Label P.n)),
        e.stateAt j = some s ∧ ValidityInvariant P pre s ∧ s.val = some b ∧
        s.F = failSet P t m ∧
        ∀ id' b', firstCall pre id' = some b' →
          ∃ k, k < m ∧ t.get? k = some (Label.callABA id' b') ∧
            ∀ k' < k, ∀ b'', t.get? k' ≠ some (Label.callABA id' b'') := by
    intro m id b h_ret h_nc
    obtain ⟨j, s, μ, pre, h_state, h_step, h_VI, h_transfer, h_push⟩ := hloc m id b h_ret
    refine ⟨j, s, pre, h_state, h_VI, ?_, h_transfer, h_push⟩
    rcases retABA_inv h_step with hv | hmem
    · exact hv
    · refine absurd ?_ (h_nc m)
      rw [← h_transfer]
      exact hmem
  constructor
  · -- Validity: the pigeonhole witness, pushed back to a preceding position
    intro m id b h_ret h_nc
    obtain ⟨j, s, pre, h_state, h_VI, h_val, h_transfer, h_push⟩ :=
      h_correct m id b h_ret h_nc
    obtain ⟨id', h_in, h_nc'⟩ :=
      exists_neverCorrupted_supporter (h_VI.invariant.val_support b h_val) h_transfer
    rcases h_VI.input_source id' b h_in with hmem | hcall
    · -- a never-corrupted supporter is in no prefix fold
      refine absurd ?_ (h_nc' m)
      rw [← h_transfer, h_VI.F_eq]
      exact hmem
    · obtain ⟨k, hk_lt, hk, hmin⟩ := h_push id' b hcall
      exact ⟨k, hk_lt, id', hk, h_nc', hmin⟩
  · -- Agreement: two honest returns read the write-once decision value
    intro id b id' b' h₁ h₂ h_nc h_nc'
    obtain ⟨m₁, hm₁⟩ := Seq.mem_iff_exists_get?.mp h₁
    obtain ⟨m₂, hm₂⟩ := Seq.mem_iff_exists_get?.mp h₂
    obtain ⟨j₁, s₁, pre₁, hst₁, -, hv₁, -, -⟩ := h_correct m₁ id b hm₁.symm h_nc
    obtain ⟨j₂, s₂, pre₂, hst₂, -, hv₂, -, -⟩ := h_correct m₂ id' b' hm₂.symm h_nc'
    rcases le_total j₁ j₂ with h | h
    · exact val_agree_le h_exec h hst₁ hst₂ hv₁ hv₂
    · exact (val_agree_le h_exec h hst₂ hst₁ hv₂ hv₁).symm

end ABA
end PLTS
