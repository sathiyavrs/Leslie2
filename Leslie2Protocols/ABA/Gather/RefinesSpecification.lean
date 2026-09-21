/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sathiya / Claude
-/

import Leslie2Protocols.ABA.Gather.CommonCoreCounting
import Leslie2Protocols.ABA.Gather.CommonCoreAtSpecification
import Leslie2Protocols.Framework.FamilySimulation
import Leslie2Protocols.Framework.WeakTransitionsFromChains

/-!
# The refinement of the composed gather instance

`Gather.gatherCore`: the composed gather instance over broadcast
specifications (`ABA/Gather/Composition.lean`) forward-simulates the gather
specification read over the instance's interface, along `Gather.CoreRel`.

A transition of the instance is one row of `StepOverBroadcastSpecification`
(`Gather.instanceOverBroadcastSpecification_step_row`), the row is answered by a weak run of the
gather specification (`coreRel_row`), and that run is lifted to the interface along a
section of `specificationLabelMap` -- which is where the call loop is answered by the
specification's own loop row.

The specification's abstract content is committed lazily, in the
exclude-on-demand style: the committed entries (`val`) and the core (`core`) are
both written inside the return run, at the first return that needs them. The run
is

```
commit*  ;  bindCore?  ;  ret
```

built by recursion with `weakLStep_tauCons` — one `commit` per entry of the
returned map not yet committed, the freeze if the instance has no core yet, then
the return.

* Entry commits are licensed by the invariant's provenance clause: a committed
  input entry of an honest process is that input instance's call record, which
  the relation identifies with the specification's call record.
* The core frozen is `coreOfNet` of the instance's gather network state, and the
  two guards of `bindCore` are `Gather.coreOf_freeze`, which the returner's
  quorum of `n − f` committed bind payloads supplies.
* Every return, the first included, is matched through the count
  `CoreRel.core_cert`: at least `f + 1` bind instances hold a committed payload
  above the frozen core. The count is blind to `F` and monotone — committed
  payloads are written once (`Gather.bindAbove_mono`) — so it survives every
  rule and every corruption. The returner's quorum of `n − f` meets it in a
  coordinate whose committed payload lies above the core and below the returned
  map.

## The call records

The call loop is an interface label of its own, and both the specification and
an input instance answer it on either of their two call rows. The two records
therefore move on exactly the same labels under the same write-once guard, and
the relation identifies them.

## The safety headline

`subDown` sends an interface label to the specification label it stands for.
An execution of `specificationOverInstanceAlphabet` has the states of a `specInst` execution and
labels that `subDown` sends to its labels, so `specificationOverInstanceAlphabet_core` reads
`CoreTrace` off the relabelled trace, and `instanceOverBroadcastSpecification_core` transfers it
along the refinement.
-/


namespace PLTS
namespace ABA
namespace Gather

variable {X : Type} [DecidableEq X] {P : Params}

/-! ### The relation -/

/-- The refinement relation of the composed gather instance. `val_cert` bounds
the specification's committed entries by the input instances' commitments;
`core_cert` is the count, blind to `F` and monotone, pinning the frozen core
below committed bind payloads. -/
structure CoreRel (P : Params) (s : StateOverBroadcastSpecification P.n X) (t : SpecState P.n X) :
  Prop where
  /-- The instance invariant. -/
  inv : IdealInv P s
  /-- The call records agree with the input instances'. -/
  call_eq : ∀ k, t.call k = (brbIn s k).input
  /-- The return flags agree. -/
  ret_eq : ∀ id, t.ret id = ((ga s).proc id).returned
  /-- The corrupted sets agree. -/
  F_eq : t.F = (ga s).F
  /-- A committed specification entry is a committed input entry. -/
  val_cert : ∀ k v, t.val k = some v → (brbIn s k).val = some v
  /-- The two sides hold the same core. -/
  core_eq : t.core = core s
  /-- At least `f + 1` bind instances hold a committed payload above the frozen
  core. -/
  core_cert : ∀ C, core s = some C → P.f + 1 ≤ (bindAbove s C).card

/-- The relation holds initially. -/
theorem coreRel_init :
    CoreRel P ((instanceOverBroadcastSpecification P X).init) ((specificationOverInstanceAlphabet P
      X).init) := by
  refine ⟨IdealInv.initial, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [ga, brbIn, core, SpecState.initial, BRB.SpecState.initial, ProcRec.initial,
      PRec.initial, GaNetState.initial, SubState.proc, SubState.F]

/-- **Broadcast compatibility**: the relation is preserved by corrupting both
sides at once. -/
theorem coreRel_corrupt {s : StateOverBroadcastSpecification P.n X} {t : SpecState P.n X}
    (hR : CoreRel P s t) (id : Fin P.n) :
    CoreRel P (corruptAll P id (BRB.SpecState.corrupt P id) (BRB.SpecState.corrupt P id) s)
      (t.corrupt P id) := by
  refine ⟨hR.inv.step (StepOverBroadcastSpecification.fail s id) (by rw [PMF.mem_support_pure_iff]),
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals dsimp only [ga_corruptAll, brbIn_corruptAll, brbBind_corruptAll, core_corruptAll]
  · intro k
    rw [corrupt_call, BRB.corrupt_input]
    exact hR.call_eq k
  · intro k
    rw [corrupt_ret, SubState.corrupt_proc]
    exact hR.ret_eq k
  · rw [SpecState.corrupt_F, SubState.corrupt_F, hR.F_eq]
  · intro k v hv
    rw [corrupt_val] at hv
    rw [BRB.corrupt_val]
    exact hR.val_cert k v hv
  · rw [corrupt_core]
    exact hR.core_eq
  · intro C hC
    exact le_trans (hR.core_cert C hC) (Finset.card_le_card
      (bindAbove_mono (StepOverBroadcastSpecification.fail s id) (by rw [PMF.mem_support_pure_iff])
        C))

/-! ### The return run

The specification's committed entries are written one at a time, by a chain of
`commit` steps folded over a list of processes; `commitOne` commits one entry of
the returned map if it is not committed yet, and `commitList` folds it. The
chain is prepended to the answering weak step by recursion with
`weakLStep_tauCons`. -/

section Run

variable (g : Fin P.n → Option X)

/-- Commit `g`'s entry at `k`, if `g` has one and it is uncommitted. -/
private def commitOne (k : Fin P.n) (t : SpecState P.n X) : SpecState P.n X :=
  if h : (g k).isSome ∧ t.val k = none
  then { t with val := Function.update t.val k (some ((g k).get h.1)) }
  else t

omit [DecidableEq X] in
private theorem commitOne_call (k : Fin P.n) (t : SpecState P.n X) :
    (commitOne g k t).call = t.call := by
  unfold commitOne; split <;> rfl

omit [DecidableEq X] in
private theorem commitOne_F (k : Fin P.n) (t : SpecState P.n X) :
    (commitOne g k t).F = t.F := by
  unfold commitOne; split <;> rfl

omit [DecidableEq X] in
private theorem commitOne_ret (k : Fin P.n) (t : SpecState P.n X) :
    (commitOne g k t).ret = t.ret := by
  unfold commitOne; split <;> rfl

omit [DecidableEq X] in
private theorem commitOne_core (k : Fin P.n) (t : SpecState P.n X) :
    (commitOne g k t).core = t.core := by
  unfold commitOne; split <;> rfl

omit [DecidableEq X] in
private theorem commitOne_val_mono {k : Fin P.n} {t : SpecState P.n X}
    {k' : Fin P.n} {v : X} (h : t.val k' = some v) :
    (commitOne g k t).val k' = some v := by
  unfold commitOne
  split
  · next hc =>
    by_cases hk : k' = k
    · subst hk
      rw [hc.2] at h
      exact absurd h (by simp)
    · change Function.update t.val k _ k' = some v
      rw [Function.update_of_ne hk]
      exact h
  · exact h

omit [DecidableEq X] in
private theorem commitOne_val_new {k : Fin P.n} {t : SpecState P.n X}
    {k' : Fin P.n} {v : X} (h : (commitOne g k t).val k' = some v) :
    t.val k' = some v ∨ g k' = some v := by
  unfold commitOne at h
  split at h
  · next hc =>
    by_cases hk : k' = k
    · subst hk
      rw [show ({ t with val := Function.update t.val k' (some ((g k').get hc.1)) }
          : SpecState P.n X).val k' = Function.update t.val k' (some ((g k').get hc.1)) k'
          from rfl, Function.update_self] at h
      right
      obtain rfl : (g k').get hc.1 = v := by injection h
      exact (Option.some_get hc.1).symm
    · rw [show ({ t with val := Function.update t.val k (some ((g k).get hc.1)) }
          : SpecState P.n X).val k' = Function.update t.val k (some ((g k).get hc.1)) k'
          from rfl, Function.update_of_ne hk] at h
      exact Or.inl h
  · exact Or.inl h

omit [DecidableEq X] in
private theorem commitOne_covers {k : Fin P.n} {t : SpecState P.n X} {x : X}
    (hx : g k = some x) (hpre : ∀ y, t.val k = some y → y = x) :
    (commitOne g k t).val k = some x := by
  unfold commitOne
  split
  · next hc =>
    change Function.update t.val k (some ((g k).get hc.1)) k = some x
    rw [Function.update_self]
    congr 1
    rw [Option.get_of_mem hc.1 hx]
  · next hc =>
    rw [not_and_or] at hc
    rcases hc with hc | hc
    · rw [hx] at hc
      simp at hc
    · rcases hval : t.val k with _ | y
      · exact absurd hval hc
      · rw [hpre y hval]

/-- One `commitOne` is the identity or a genuine `commit` step. -/
private theorem commitOne_step (k : Fin P.n) (t : SpecState P.n X)
    (hm : ∀ x, g k = some x → t.val k = none → k ∈ t.F ∨ t.call k = some x) :
    commitOne g k t = t ∨
      Step P t Label.tau (PMF.pure (commitOne g k t)) := by
  unfold commitOne
  split
  · next hc =>
    right
    obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp hc.1
    have hget : (g k).get hc.1 = x := Option.get_of_mem hc.1 hx
    rw [hget]
    exact Step.commit t k x hc.2 (hm x hx hc.2)
  · exact Or.inl rfl

/-- Fold `commitOne` over a list of processes. -/
private def commitList : List (Fin P.n) → SpecState P.n X → SpecState P.n X
  | [], t => t
  | k :: l, t => commitList l (commitOne g k t)

omit [DecidableEq X] in
private theorem commitList_call :
    ∀ (l : List (Fin P.n)) (t : SpecState P.n X), (commitList g l t).call = t.call
  | [], _ => rfl
  | k :: l, t => by rw [commitList, commitList_call l, commitOne_call]

omit [DecidableEq X] in
private theorem commitList_F :
    ∀ (l : List (Fin P.n)) (t : SpecState P.n X), (commitList g l t).F = t.F
  | [], _ => rfl
  | k :: l, t => by rw [commitList, commitList_F l, commitOne_F]

omit [DecidableEq X] in
private theorem commitList_ret :
    ∀ (l : List (Fin P.n)) (t : SpecState P.n X), (commitList g l t).ret = t.ret
  | [], _ => rfl
  | k :: l, t => by rw [commitList, commitList_ret l, commitOne_ret]

omit [DecidableEq X] in
private theorem commitList_core :
    ∀ (l : List (Fin P.n)) (t : SpecState P.n X), (commitList g l t).core = t.core
  | [], _ => rfl
  | k :: l, t => by rw [commitList, commitList_core l, commitOne_core]

omit [DecidableEq X] in
private theorem commitList_val_mono :
    ∀ (l : List (Fin P.n)) (t : SpecState P.n X) {k' : Fin P.n} {v : X},
      t.val k' = some v → (commitList g l t).val k' = some v
  | [], _, _, _, h => h
  | k :: l, t, _, _, h =>
    commitList_val_mono l (commitOne g k t) (commitOne_val_mono g h)

omit [DecidableEq X] in
private theorem commitList_val_new :
    ∀ (l : List (Fin P.n)) (t : SpecState P.n X) {k' : Fin P.n} {v : X},
      (commitList g l t).val k' = some v → t.val k' = some v ∨ g k' = some v
  | [], _, _, _, h => Or.inl h
  | k :: l, t, _, _, h => by
    rcases commitList_val_new l (commitOne g k t) h with h' | h'
    · exact commitOne_val_new g h'
    · exact Or.inr h'

omit [DecidableEq X] in
private theorem commitList_covers :
    ∀ (l : List (Fin P.n)) (t : SpecState P.n X),
      (∀ k y x, g k = some x → t.val k = some y → y = x) →
      ∀ k ∈ l, ∀ x, g k = some x → (commitList g l t).val k = some x
  | [], _, _, k, hk, _, _ => absurd hk (by simp)
  | k₀ :: l, t, hpre, k, hk, x, hx => by
    have hpre' : ∀ k' y x', g k' = some x' → (commitOne g k₀ t).val k' = some y → y = x' := by
      intro k' y x' hx' hy
      rcases commitOne_val_new g hy with h' | h'
      · exact hpre k' y x' hx' h'
      · rw [hx'] at h'
        injection h' with h''
        exact h''.symm
    rcases List.mem_cons.mp hk with rfl | hk'
    · exact commitList_val_mono g l _ (commitOne_covers g hx (fun y hy => hpre k y x hx hy))
    · exact commitList_covers l (commitOne g k₀ t) hpre' k hk' x hx

/-- Prepend the commit chain to an answering weak step. -/
private theorem weakLStep_after_commits {l₀ : Label P.n X} {t' : SpecState P.n X} :
    ∀ (l : List (Fin P.n)) (t : SpecState P.n X),
      (∀ k ∈ l, ∀ x, g k = some x → t.val k = none → k ∈ t.F ∨ t.call k = some x) →
      (specInst P X).weakLStep (commitList g l t) l₀ t' →
      (specInst P X).weakLStep t l₀ t'
  | [], _, _, htail => htail
  | k :: rest, t, hg, htail => by
    rcases commitOne_step g k t (fun x hx hv => hg k (by simp) x hx hv) with heq | hstep
    · rw [show commitList g (k :: rest) t = commitList g rest t from by
        rw [commitList, heq]] at htail
      exact weakLStep_after_commits rest t
        (fun k' hk' => hg k' (List.mem_cons_of_mem k hk')) htail
    · refine System.weakLStep_tauCons hstep
        (weakLStep_after_commits rest (commitOne g k t) ?_ htail)
      intro k' hk' x hx hv
      have hvold : t.val k' = none := by
        rcases hval : t.val k' with _ | y
        · rfl
        · rw [commitOne_val_mono g hval] at hv
          exact absurd hv (by simp)
      have h := hg k' (List.mem_cons_of_mem k hk') x hx hvold
      rw [commitOne_F, commitOne_call]
      exact h

/-- The states of the genuine commits of `commitList`, as a list. -/
private def commitChain : List (Fin P.n) → SpecState P.n X → List (SpecState P.n X)
  | [], _ => []
  | k :: l, t =>
    if _h : (g k).isSome ∧ t.val k = none
    then commitOne g k t :: commitChain l (commitOne g k t)
    else commitChain l t

omit [DecidableEq X] in
private theorem commitChain_getLastD :
    ∀ (l : List (Fin P.n)) (t : SpecState P.n X),
      (commitChain g l t).getLastD t = commitList g l t
  | [], _ => rfl
  | k :: l, t => by
    rw [commitChain, commitList]
    split
    · next h =>
      rw [List.getLastD_cons, commitChain_getLastD l]
    · next h =>
      have hid : commitOne g k t = t := by
        unfold commitOne
        rw [dif_neg h]
      rw [hid, commitChain_getLastD l]

private theorem commitChain_isChain :
    ∀ (l : List (Fin P.n)) (t : SpecState P.n X),
      (∀ k ∈ l, ∀ x, g k = some x → t.val k = none → k ∈ t.F ∨ t.call k = some x) →
      List.IsChain (fun a b => Step P a Label.tau (PMF.pure b)) (t :: commitChain g l t)
  | [], t, _ => List.isChain_singleton t
  | k :: l, t, hg => by
    rw [commitChain]
    split
    · next hc =>
      have hstep : Step P t Label.tau (PMF.pure (commitOne g k t)) := by
        have hm := hg k (by simp) ((g k).get hc.1) (Option.some_get hc.1).symm hc.2
        unfold commitOne
        rw [dif_pos hc]
        exact Step.commit t k ((g k).get hc.1) hc.2 hm
      refine List.isChain_cons_cons.mpr ⟨hstep, commitChain_isChain l (commitOne g k t) ?_⟩
      intro k' hk' x hx hv
      have hvold : t.val k' = none := by
        rcases hval : t.val k' with _ | y
        · rfl
        · rw [commitOne_val_mono g hval] at hv
          exact absurd hv (by simp)
      have h := hg k' (List.mem_cons_of_mem k hk') x hx hvold
      rw [commitOne_F, commitOne_call]
      exact h
    · next hc =>
      have hid : commitOne g k t = t := by
        unfold commitOne
        rw [dif_neg hc]
      have := commitChain_isChain l (commitOne g k t)
        (fun k' hk' => by
          rw [hid]
          exact hg k' (List.mem_cons_of_mem k hk'))
      rwa [hid] at this

end Run

/-! ### The return run, as data

The whole return answer of the refinement, packaged as a τ-chain of
specification steps with the return guards at its end and the relation restored
across the pair of return effects — the shape a larger system that embeds the
gather specification's rows can replay without re-proving the run. -/

theorem retRun {s : StateOverBroadcastSpecification P.n X} {t : SpecState P.n X}
    (hR : CoreRel P s t) {id : Fin P.n} {g : Fin P.n → Option X}
    (hin : ((ga s).proc id).input ≠ none)
    (hbind : ((ga s).proc id).sentBind ≠ none)
    (hsub : ∀ k x, g k = some x → holdsIn ((ga s).proc id) k x)
    (hQ : ∃ Q : Finset (Fin P.n), P.n - P.f ≤ Q.card ∧
      ∀ q ∈ Q, ∃ U, holdsBind ((ga s).proc id) q U ∧ APSet.subMap U g)
    (hr : ((ga s).proc id).returned = false) :
    ∃ ts : List (SpecState P.n X),
      List.IsChain (fun a b => Step P a Label.tau (PMF.pure b)) (t :: ts) ∧
      (ts.getLastD t).core = some ((core s).getD (coreOfNet P (ga s).2)) ∧
      APSet.subMap ((core s).getD (coreOfNet P (ga s).2)) g ∧
      (∀ k x, g k = some x → (ts.getLastD t).val k = some x) ∧
      (ts.getLastD t).ret id = false ∧
      CoreRel P
        (setCore (setGa s ((ga s).setProc id { (ga s).proc id with returned := true }))
          (some ((core s).getD (coreOfNet P (ga s).2))))
        { ts.getLastD t with ret := Function.update (ts.getLastD t).ret id true } := by
  classical
  set C : APSet P.n X := (core s).getD (coreOfNet P (ga s).2) with hC_def
  have hInv' := hR.inv.step (StepOverBroadcastSpecification.ret s id g hin hbind hsub hQ hr)
    (by rw [PMF.mem_support_pure_iff])
  have hsubv : ∀ k x, g k = some x → (brbIn s k).val = some x :=
    fun k x hx => hR.inv.delivIn_val id k x (hsub k x hx)
  obtain ⟨Q, hQc, hQm0⟩ := hQ
  have hQm : ∀ q ∈ Q, ∃ U, (brbBind s q).val = some U ∧ APSet.subMap U g := by
    intro q hq
    obtain ⟨U, hU, hUg⟩ := hQm0 q hq
    exact ⟨U, hR.inv.delivBind_val id q U hU, hUg⟩
  set l : List (Fin P.n) := (Finset.univ.filter (fun k => (g k).isSome)).toList with hl
  have hguard : ∀ k ∈ l, ∀ x, g k = some x → t.val k = none →
      k ∈ t.F ∨ t.call k = some x := by
    intro k _ x hx _
    rcases hR.inv.inVal_prov k x (hsubv k x hx) with hF | hin'
    · left
      rw [hR.F_eq]
      exact hF
    · right
      rw [hR.call_eq k]
      exact hin'
  have hpre : ∀ k y x, g k = some x → t.val k = some y → y = x := by
    intro k y x hx hy
    have h1 := hR.val_cert k y hy
    have h2 := hsubv k x hx
    rw [h1] at h2
    injection h2
  have hcov : ∀ k x, g k = some x → (commitList g l t).val k = some x := by
    intro k x hx
    refine commitList_covers g l t hpre k ?_ x hx
    rw [hl, Finset.mem_toList, Finset.mem_filter]
    exact ⟨Finset.mem_univ k, by rw [hx]; rfl⟩
  have hretflag : (commitList g l t).ret id = false := by
    rw [commitList_ret, hR.ret_eq id]
    exact hr
  have hchain := commitChain_isChain g l t hguard
  have hlast := commitChain_getLastD g l t
  set u : Fin P.n → APSet P.n X := fun q =>
    if h : ∃ U, (brbBind s q).val = some U ∧ APSet.subMap U g
    then h.choose else ∅ with hu_def
  have hu : ∀ q ∈ Q, (brbBind s q).val = some (u q) ∧ APSet.subMap (u q) g := by
    intro q hq
    have hex := hQm q hq
    rw [hu_def]
    dsimp only
    rw [dif_pos hex]
    exact hex.choose_spec
  -- A core with `f + 1` committed bind payloads above it is dominated by the
  -- returned map: the count meets the return quorum.
  have key : ∀ C : APSet P.n X, P.f + 1 ≤ (bindAbove s C).card → APSet.subMap C g := by
    intro C hcnt
    obtain ⟨q, hqK, hqQ⟩ := SubState.exists_mem_inter_of_quorum hcnt hQc
    obtain ⟨U, hUval, hCU⟩ := mem_bindAbove.mp hqK
    have h2 := (hu q hqQ).1
    rw [hUval] at h2
    obtain rfl : U = u q := Option.some.inj h2
    exact APSet.subMap_mono hCU (hu q hqQ).2
  -- The relation across the pair of return effects, at the end of the chain.
  have hrel : ∀ (t' : SpecState P.n X), t'.call = (commitList g l t).call →
      t'.ret = (commitList g l t).ret → t'.F = (commitList g l t).F →
      (∀ k v, t'.val k = some v → (commitList g l t).val k = some v) →
      t'.core = some C → P.f + 1 ≤ (bindAbove s C).card →
      CoreRel P
        (setCore (setGa s ((ga s).setProc id { (ga s).proc id with returned := true }))
          (some C))
        { t' with ret := Function.update t'.ret id true } := by
    intro t' hcall hret hF hval hcore hcnt
    refine ⟨hInv', ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals dsimp only [ga_setCore, ga_setGa, brbIn_setCore, brbIn_setGa, core_setCore]
    · intro k
      rw [hcall, commitList_call]
      exact hR.call_eq k
    · intro k
      by_cases hk : k = id
      · subst hk
        rw [Function.update_self, SubState.setProc_proc_self]
      · rw [Function.update_of_ne hk, hret, commitList_ret,
          SubState.setProc_proc_ne _ _ _ hk]
        exact hR.ret_eq k
    · rw [hF, commitList_F]
      exact hR.F_eq
    · intro k v hv
      rcases commitList_val_new g l t (hval k v hv) with hold | hnew
      · exact hR.val_cert k v hold
      · exact hsubv k v hnew
    · exact hcore
    · intro C' hC'
      obtain rfl : C = C' := Option.some.inj hC'
      exact hcnt
  rcases hcore : core s with _ | C₀
  · -- no core yet: freeze `coreOfNet` at the end of the chain
    have hCcore : C = coreOfNet P (ga s).2 := by simp [hC_def, hcore]
    obtain ⟨hcard, -, hcnt⟩ :=
      coreOf_freeze hR.inv hQc (fun q hq => ⟨u q, (hu q hq).1⟩)
    rw [← hCcore] at hcard hcnt
    have hCg : APSet.subMap C g := key _ hcnt
    have hbind : Step P (commitList g l t) Label.tau
        (PMF.pure { commitList g l t with core := some C }) := by
      refine Step.bindCore _ C (by rw [commitList_core, hR.core_eq, hcore]) ?_ hcard
      intro p hp
      exact hcov p.1 p.2 (hCg p hp)
    refine ⟨commitChain g l t ++ [{ commitList g l t with core := some C }],
      ?_, ?_, hCg, ?_, ?_, ?_⟩
    · refine isChain_snoc hchain ?_
      rw [hlast]
      exact hbind
    · rw [List.getLastD_concat]
    · intro k x hx
      rw [List.getLastD_concat]
      exact hcov k x hx
    · rw [List.getLastD_concat]
      exact hretflag
    · rw [List.getLastD_concat]
      exact hrel _ rfl rfl rfl (fun _ _ h => h) rfl hcnt
  · -- a core frozen earlier: the certificate meets the return quorum
    have hCcore : C = C₀ := by simp [hC_def, hcore]
    have hcnt : P.f + 1 ≤ (bindAbove s C).card := by
      rw [hCcore]; exact hR.core_cert C₀ hcore
    have hCg : APSet.subMap C g := key _ hcnt
    have hlastcore : (commitList g l t).core = some C := by
      rw [commitList_core, hR.core_eq, hcore, hCcore]
    refine ⟨commitChain g l t, hchain, ?_, hCg, ?_, ?_, ?_⟩
    · rw [hlast]; exact hlastcore
    · intro k x hx
      rw [hlast]
      exact hcov k x hx
    · rw [hlast]
      exact hretflag
    · rw [hlast]
      exact hrel _ rfl rfl rfl (fun _ _ h => h) hlastcore hcnt


/-! ### Step-level relation transports

The relation across one embedded row, exported for systems that replay the
gather rows inside a larger rule table. -/

/-- The relation across the fused call: the gather record, the input instance
and the specification all record the payload. -/
theorem coreRel_call {s : StateOverBroadcastSpecification P.n X} {t : SpecState P.n X}
    (hR : CoreRel P s t) {id : Fin P.n} {x : X}
    (h : ((ga s).proc id).input = none) (hb : (brbIn s id).input = none) :
    CoreRel P
      (setBrbIn (setGa s ((ga s).setProc id { (ga s).proc id with input := some x }))
        (Function.update (brbIn s) id { brbIn s id with input := some x }))
      { t with call := Function.update t.call id (some x) } := by
  refine ⟨hR.inv.step (StepOverBroadcastSpecification.call s id x h hb) (by rw
    [PMF.mem_support_pure_iff]),
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals dsimp only [ga_setBrbIn, ga_setGa, brbIn_setBrbIn]
  · intro k
    by_cases hk : k = id
    · subst hk
      rw [Function.update_self, Function.update_self]
    · rw [Function.update_of_ne hk, Function.update_of_ne hk]
      exact hR.call_eq k
  · intro k
    by_cases hk : k = id
    · subst hk
      rw [SubState.setProc_proc_self]
      exact hR.ret_eq k
    · rw [SubState.setProc_proc_ne _ _ _ hk]
      exact hR.ret_eq k
  · exact hR.F_eq
  · intro k v hv
    by_cases hk : k = id
    · subst hk
      rw [Function.update_self]
      exact hR.val_cert k v hv
    · rw [Function.update_of_ne hk]
      exact hR.val_cert k v hv
  · exact hR.core_eq
  · exact hR.core_cert

/-- The relation across any internal row, the specification stuttering. -/
theorem coreRel_tau {s s' : StateOverBroadcastSpecification P.n X} {t : SpecState P.n X}
    (hR : CoreRel P s t) (hstep : StepOverBroadcastSpecification P s Gather.Label.tau (PMF.pure s'))
      :
    CoreRel P s' t := by
  have hInv' := hR.inv.step hstep (by rw [PMF.mem_support_pure_iff])
  generalize hμ : (PMF.pure s' : PMF (StateOverBroadcastSpecification P.n X)) = μ at hstep
  cases hstep with
  | commitIn k v hv hm =>
    have hs' := PMF.pure_injective hμ
    subst hs'
    refine ⟨hInv', ?_, hR.ret_eq, hR.F_eq, ?_, hR.core_eq, hR.core_cert⟩
    all_goals dsimp only [brbIn_setBrbIn]
    · intro k'
      by_cases hk : k' = k
      · subst hk; rw [Function.update_self]; exact hR.call_eq k'
      · rw [Function.update_of_ne hk]; exact hR.call_eq k'
    · intro k' v' hv'
      have hold := hR.val_cert k' v' hv'
      by_cases hk : k' = k
      · subst hk; rw [hv] at hold; exact absurd hold (by simp)
      · rw [Function.update_of_ne hk]; exact hold
  | commitBind q U hv hm =>
    have hs' := PMF.pure_injective hμ
    subst hs'
    refine ⟨hInv', hR.call_eq, hR.ret_eq, hR.F_eq, hR.val_cert, hR.core_eq, ?_⟩
    intro C hC
    exact le_trans (hR.core_cert C hC) (Finset.card_le_card
      (bindAbove_mono (StepOverBroadcastSpecification.commitBind s q U hv hm)
        (by rw [PMF.mem_support_pure_iff]) C))
  | deliver i j m h =>
    have hs' := PMF.pure_injective hμ
    subst hs'
    refine ⟨hInv', hR.call_eq, ?_, hR.F_eq, hR.val_cert, hR.core_eq, hR.core_cert⟩
    dsimp only [ga_setGa]
    intro k
    rw [SubState.recvMsg_proc]
    exact hR.ret_eq k
  | echo j hin hcard hsend =>
    have hs' := PMF.pure_injective hμ
    subst hs'
    refine ⟨hInv', hR.call_eq, ?_, hR.F_eq, hR.val_cert, hR.core_eq, hR.core_cert⟩
    dsimp only [ga_setGa]
    intro k
    by_cases hk : k = j
    · subst hk
      rw [SubState.mcast_proc, SubState.setProc_proc_self]
      exact hR.ret_eq k
    · rw [SubState.mcast_proc, SubState.setProc_proc_ne _ _ _ hk]
      exact hR.ret_eq k
  | vote j U hin hech happ hQ hsend =>
    have hs' := PMF.pure_injective hμ
    subst hs'
    refine ⟨hInv', hR.call_eq, ?_, hR.F_eq, hR.val_cert, hR.core_eq, hR.core_cert⟩
    dsimp only [ga_setGa]
    intro k
    by_cases hk : k = j
    · subst hk
      rw [SubState.mcast_proc, SubState.setProc_proc_self]
      exact hR.ret_eq k
    · rw [SubState.mcast_proc, SubState.setProc_proc_ne _ _ _ hk]
      exact hR.ret_eq k
  | bindCall j U hin hvot hsnd happ hQ hb =>
    have hs' := PMF.pure_injective hμ
    subst hs'
    refine ⟨hInv', hR.call_eq, ?_, hR.F_eq, hR.val_cert, hR.core_eq, ?_⟩
    · dsimp only [ga_setBrbBind, ga_setGa]
      intro k
      by_cases hk : k = j
      · subst hk
        rw [SubState.setProc_proc_self]
        exact hR.ret_eq k
      · rw [SubState.setProc_proc_ne _ _ _ hk]
        exact hR.ret_eq k
    · intro C hC
      exact le_trans (hR.core_cert C hC) (Finset.card_le_card
        (bindAbove_mono (StepOverBroadcastSpecification.bindCall s j U hin hvot hsnd happ hQ hb)
          (by rw [PMF.mem_support_pure_iff]) C))
  | bindCallSpecLoop j U hin hvot hsnd happ hQ =>
    have hs' := PMF.pure_injective hμ
    subst hs'
    refine ⟨hInv', hR.call_eq, ?_, hR.F_eq, hR.val_cert, hR.core_eq, hR.core_cert⟩
    dsimp only [ga_setGa]
    intro k
    by_cases hk : k = j
    · subst hk
      rw [SubState.setProc_proc_self]
      exact hR.ret_eq k
    · rw [SubState.setProc_proc_ne _ _ _ hk]
      exact hR.ret_eq k
  | byzantine j m hmem =>
    have hs' := PMF.pure_injective hμ
    subst hs'
    refine ⟨hInv', hR.call_eq, ?_, hR.F_eq, hR.val_cert, hR.core_eq, hR.core_cert⟩
    dsimp only [ga_setGa]
    intro k
    rw [SubState.mcast_proc]
    exact hR.ret_eq k
  | inRet k j v hv hr =>
    have hs' := PMF.pure_injective hμ
    subst hs'
    refine ⟨hInv', ?_, ?_, hR.F_eq, ?_, hR.core_eq, hR.core_cert⟩
    all_goals dsimp only [ga_setBrbIn, ga_setGa, brbIn_setBrbIn]
    · intro k'
      by_cases hk : k' = k
      · subst hk; rw [Function.update_self]; exact hR.call_eq k'
      · rw [Function.update_of_ne hk]; exact hR.call_eq k'
    · intro id'
      by_cases hj : id' = j
      · subst hj; rw [SubState.setProc_proc_self]; exact hR.ret_eq id'
      · rw [SubState.setProc_proc_ne _ _ _ hj]; exact hR.ret_eq id'
    · intro k' v' hv'
      by_cases hk : k' = k
      · subst hk; rw [Function.update_self]; exact hR.val_cert k' v' hv'
      · rw [Function.update_of_ne hk]; exact hR.val_cert k' v' hv'
  | bindRet q j U hv hr =>
    have hs' := PMF.pure_injective hμ
    subst hs'
    refine ⟨hInv', hR.call_eq, ?_, hR.F_eq, hR.val_cert, hR.core_eq, ?_⟩
    · dsimp only [ga_setBrbBind, ga_setGa]
      intro id'
      by_cases hj : id' = j
      · subst hj; rw [SubState.setProc_proc_self]; exact hR.ret_eq id'
      · rw [SubState.setProc_proc_ne _ _ _ hj]; exact hR.ret_eq id'
    · intro C hC
      exact le_trans (hR.core_cert C hC) (Finset.card_le_card
        (bindAbove_mono (StepOverBroadcastSpecification.bindRet s q j U hv hr)
          (by rw [PMF.mem_support_pure_iff]) C))


/-! ### The relation across one row -/

/-- **The relation across one row**: every row of `StepOverBroadcastSpecification` at a related
pair is answered by a weak run of the gather specification, and the answer is
again related. Internal rows stutter; the four call rows and `fail` are answered
by the specification's own rows; a return is answered by the run
`commit* ; bindCore? ; ret`. -/
theorem coreRel_row (P : Params) (X : Type) [DecidableEq X] (q₁ : StateOverBroadcastSpecification
  P.n X)
    (q₂ : SpecState P.n X) (hR : CoreRel P q₁ q₂) (l₀ : Label P.n X)
    (μ : PMF (StateOverBroadcastSpecification P.n X)) (hrow : StepOverBroadcastSpecification P q₁ l₀
      μ)
    (q₁' : StateOverBroadcastSpecification P.n X) (hq₁' : q₁' ∈ μ.support) :
    ∃ q₂', ((l₀ = Silent.τ ∧ (specInst P X).weakLSilent q₂ q₂') ∨
      (¬ l₀ = Silent.τ ∧ (specInst P X).weakLStep q₂ l₀ q₂')) ∧
      CoreRel P q₁' q₂' := by
  cases hrow with
  | call id x h hb =>
    rw [PMF.mem_support_pure_iff] at hq₁'
    subst hq₁'
    exact ⟨{ q₂ with call := Function.update q₂.call id (some x) },
      Or.inr ⟨by simp, System.weakLStep_of_step (by simp)
        (Step.call q₂ id x (by rw [hR.call_eq id]; exact hb))⟩,
      coreRel_call hR h hb⟩
  | callSpecLoop id x h =>
    rw [PMF.mem_support_pure_iff] at hq₁'
    subst hq₁'
    refine ⟨q₂, Or.inr ⟨by simp, System.weakLStep_of_step (by simp)
      (Step.callLoop q₂ id x)⟩, ?_⟩
    refine ⟨hR.inv.step (StepOverBroadcastSpecification.callSpecLoop q₁ id x h)
      (by rw [PMF.mem_support_pure_iff]),
      hR.call_eq, ?_, hR.F_eq, hR.val_cert, hR.core_eq, hR.core_cert⟩
    dsimp only [ga_setGa]
    intro k
    by_cases hk : k = id
    · subst hk
      rw [SubState.setProc_proc_self]
      exact hR.ret_eq k
    · rw [SubState.setProc_proc_ne _ _ _ hk]
      exact hR.ret_eq k
  | callProcLoop id x hb =>
    rw [PMF.mem_support_pure_iff] at hq₁'
    subst hq₁'
    refine ⟨{ q₂ with call := Function.update q₂.call id (some x) },
      Or.inr ⟨by simp, System.weakLStep_of_step (by simp)
        (Step.call q₂ id x (by rw [hR.call_eq id]; exact hb))⟩, ?_⟩
    refine ⟨hR.inv.step (StepOverBroadcastSpecification.callProcLoop q₁ id x hb)
      (by rw [PMF.mem_support_pure_iff]),
      ?_, hR.ret_eq, hR.F_eq, ?_, hR.core_eq, hR.core_cert⟩
    all_goals dsimp only [brbIn_setBrbIn]
    · intro k
      by_cases hk : k = id
      · subst hk
        rw [Function.update_self, Function.update_self]
      · rw [Function.update_of_ne hk, Function.update_of_ne hk]
        exact hR.call_eq k
    · intro k v hv
      by_cases hk : k = id
      · subst hk
        rw [Function.update_self]
        exact hR.val_cert k v hv
      · rw [Function.update_of_ne hk]
        exact hR.val_cert k v hv
  | callLoop id x =>
    rw [PMF.mem_support_pure_iff] at hq₁'
    subst hq₁'
    exact ⟨q₂, Or.inr ⟨by simp, System.weakLStep_of_step (by simp)
      (Step.callLoop q₂ id x)⟩, hR⟩
  | commitIn k v hv hm =>
    rw [PMF.mem_support_pure_iff] at hq₁'
    subst hq₁'
    exact ⟨q₂, Or.inl ⟨rfl, System.weakLSilent_refl _ q₂⟩,
      coreRel_tau hR (StepOverBroadcastSpecification.commitIn q₁ k v hv hm)⟩
  | commitBind q U hv hm =>
    rw [PMF.mem_support_pure_iff] at hq₁'
    subst hq₁'
    exact ⟨q₂, Or.inl ⟨rfl, System.weakLSilent_refl _ q₂⟩,
      coreRel_tau hR (StepOverBroadcastSpecification.commitBind q₁ q U hv hm)⟩
  | deliver i j m h =>
    rw [PMF.mem_support_pure_iff] at hq₁'
    subst hq₁'
    exact ⟨q₂, Or.inl ⟨rfl, System.weakLSilent_refl _ q₂⟩,
      coreRel_tau hR (StepOverBroadcastSpecification.deliver q₁ i j m h)⟩
  | echo j hin hcard hsend =>
    rw [PMF.mem_support_pure_iff] at hq₁'
    subst hq₁'
    exact ⟨q₂, Or.inl ⟨rfl, System.weakLSilent_refl _ q₂⟩,
      coreRel_tau hR (StepOverBroadcastSpecification.echo q₁ j hin hcard hsend)⟩
  | vote j U hin hech happ hQ hsend =>
    rw [PMF.mem_support_pure_iff] at hq₁'
    subst hq₁'
    exact ⟨q₂, Or.inl ⟨rfl, System.weakLSilent_refl _ q₂⟩,
      coreRel_tau hR (StepOverBroadcastSpecification.vote q₁ j U hin hech happ hQ hsend)⟩
  | bindCall j U hin hvot hsnd happ hQ hb =>
    rw [PMF.mem_support_pure_iff] at hq₁'
    subst hq₁'
    exact ⟨q₂, Or.inl ⟨rfl, System.weakLSilent_refl _ q₂⟩,
      coreRel_tau hR (StepOverBroadcastSpecification.bindCall q₁ j U hin hvot hsnd happ hQ hb)⟩
  | bindCallSpecLoop j U hin hvot hsnd happ hQ =>
    rw [PMF.mem_support_pure_iff] at hq₁'
    subst hq₁'
    exact ⟨q₂, Or.inl ⟨rfl, System.weakLSilent_refl _ q₂⟩,
      coreRel_tau hR (StepOverBroadcastSpecification.bindCallSpecLoop q₁ j U hin hvot hsnd happ hQ)⟩
  | byzantine j m h =>
    rw [PMF.mem_support_pure_iff] at hq₁'
    subst hq₁'
    exact ⟨q₂, Or.inl ⟨rfl, System.weakLSilent_refl _ q₂⟩,
      coreRel_tau hR (StepOverBroadcastSpecification.byzantine q₁ j m h)⟩
  | inRet k j v hv hr =>
    rw [PMF.mem_support_pure_iff] at hq₁'
    subst hq₁'
    exact ⟨q₂, Or.inl ⟨rfl, System.weakLSilent_refl _ q₂⟩,
      coreRel_tau hR (StepOverBroadcastSpecification.inRet q₁ k j v hv hr)⟩
  | bindRet q j U hv hr =>
    rw [PMF.mem_support_pure_iff] at hq₁'
    subst hq₁'
    exact ⟨q₂, Or.inl ⟨rfl, System.weakLSilent_refl _ q₂⟩,
      coreRel_tau hR (StepOverBroadcastSpecification.bindRet q₁ q j U hv hr)⟩
  | ret id g hin hbind hsub hQ hr =>
    rw [PMF.mem_support_pure_iff] at hq₁'
    subst hq₁'
    obtain ⟨ts, hchain, hcore, hmem, hcov, hret1, hRel⟩ :=
      retRun hR hin hbind hsub hQ hr
    have hretstep : Step P (ts.getLastD q₂)
        (Label.ret id g ((core q₁).getD (coreOfNet P (ga q₁).2)))
        (PMF.pure { ts.getLastD q₂ with
          ret := Function.update (ts.getLastD q₂).ret id true }) :=
      Step.ret _ id g _ hcore hmem hcov hret1
    exact ⟨_, Or.inr ⟨by simp,
      System.weakLStep_tausThen hchain hretstep (by simp)⟩, hRel⟩
  | fail id =>
    rw [PMF.mem_support_pure_iff] at hq₁'
    subst hq₁'
    exact ⟨q₂.corrupt P id, Or.inr ⟨by simp, System.weakLStep_of_step (by simp)
      (Step.fail q₂ id)⟩, coreRel_corrupt hR id⟩

/-! ### The refinement -/

/-- **The refinement of the composed gather instance**: the instance over
broadcast specifications forward-simulates the gather specification read over
the instance's interface. A transition of the instance is one row of
`StepOverBroadcastSpecification` (`Gather.instanceOverBroadcastSpecification_step_row`), the row is
answered by a weak run of the specification (`coreRel_row`), and that run is lifted to the interface
along a section of `specificationLabelMap`. -/
theorem gatherCore (P : Params) (X : Type) [DecidableEq X] :
    ForwardSimulation (instanceOverBroadcastSpecification P X) (specificationOverInstanceAlphabet P
      X) (CoreRel P) := by
  constructor
  intro q₁ q₂ hR l μ hstep q₁' hq₁'
  obtain ⟨l₀, hpull, hrow⟩ := instanceOverBroadcastSpecification_step_row P q₁ l μ hstep
  obtain ⟨t', hdis, hrel⟩ := coreRel_row P X q₁ q₂ hR l₀ μ hrow q₁' hq₁'
  refine ⟨t', ?_, hrel⟩
  rcases hdis with ⟨hτ, hweak⟩ | ⟨hτ, hweak⟩
  · exact Or.inl ⟨specificationLabelMap_eq_tau (by rw [hpull, hτ]; rfl),
      weakLSilent_specificationOverInstanceAlphabet P hweak⟩
  · refine Or.inr ⟨?_, weakLStep_specificationOverInstanceAlphabet P hτ hpull hweak⟩
    intro hl
    refine hτ ?_
    have h2 : specificationLabelMap P.n X (Silent.τ : InstanceLabel P.n X) = some l₀ := by
      rw [← hl]; exact hpull
    rw [specificationLabelMap_tau] at h2
    exact (Option.some.inj h2).symm


/-! ### The safety headline at the composition -/

/-- The specification label an interface label stands for: the call loop stands
for the call it loops on. -/
def subDown {n : ℕ} : InstanceLabel n X → Label n X
  | Sum.inl l => l
  | Sum.inr (.callLoop id x) => .call id x

omit [DecidableEq X] in
/-- The specification's alphabet read off an interface label is `subDown`. -/
theorem specificationLabelMap_eq_subDown {n : ℕ} (l : InstanceLabel n X) :
    specificationLabelMap n X l = some (subDown l) := by
  cases l with
  | inl l₀ => rfl
  | inr e => cases e; rfl

/-- A transition of the lifted specification is a transition of the
specification at the label `subDown` names. -/
theorem specificationOverInstanceAlphabet_step_down (P : Params) {s : SpecState P.n X} {l :
  InstanceLabel P.n X}
    {μ : PMF (SpecState P.n X)} (h : (specificationOverInstanceAlphabet P X).step s l μ) :
    (specInst P X).step s (subDown l) μ :=
  (System.mapIdle_step_some (specificationLabelMap_eq_subDown l) μ).mp h

/-- **The lifted specification binds one core.** An execution of `specificationOverInstanceAlphabet`
has the states of a `specInst` execution and labels that `subDown` sends to its
labels, so the guards of a return are read off the specification's own rows. -/
theorem specificationOverInstanceAlphabet_core (P : Params) (X : Type) [DecidableEq X] :
    ∀ D ∈ achievableTraceDists (specificationOverInstanceAlphabet P X), ∀ t, D t ≠ 0 →
      CoreTrace P (t.map subDown) := by
  rintro D ⟨pe, h_init, h_D⟩ t h_ne
  rw [← h_D t] at h_ne
  obtain ⟨e, h_exec, h_char⟩ := exists_exec_of_traceProb_ne_zero pe h_init t h_ne
  have h_exec' : is_exec (e.mapLab subDown) (specInst P X) :=
    ⟨is_partial_exec_mapLab subDown (fun _ _ _ h => specificationOverInstanceAlphabet_step_down P h)
      h_exec.1,
      h_exec.2⟩
  have hret : ∀ (id : Fin P.n) (g : Fin P.n → Option X) (C : APSet P.n X),
      Label.ret id g C ∈ t.map subDown →
      ∃ (k : ℕ) (s : SpecState P.n X), (e.mapLab subDown).stateAt k = some s ∧
        s.core = some C ∧ APSet.subMap C g := by
    intro id g C h₁
    obtain ⟨l, hl, hdown⟩ := Stream'.Seq.exists_of_mem_map h₁
    obtain ⟨-, k, s', hg⟩ := (h_char l).mp hl
    obtain ⟨s, μ, hst, hstep, -⟩ := h_exec.1 k _ _ hg
    have hstep' : Step P s (Label.ret id g C) μ := by
      have h2 := specificationOverInstanceAlphabet_step_down P hstep
      rwa [hdown] at h2
    obtain ⟨hC, hmem⟩ := ret_guards hstep'
    exact ⟨k, s, by rw [AlterSeq.stateAt_mapLab]; exact hst, hC, hmem⟩
  refine ⟨?_, ?_⟩
  · intro id g C h₁
    obtain ⟨k, s, hst, hC, hmem⟩ := hret id g C h₁
    exact ⟨core_card h_exec' k s hst C hC, hmem⟩
  · intro id₁ id₂ g₁ g₂ C₁ C₂ h₁ h₂
    obtain ⟨k₁, s₁, hst₁, hC₁, -⟩ := hret id₁ g₁ C₁ h₁
    obtain ⟨k₂, s₂, hst₂, hC₂, -⟩ := hret id₂ g₂ C₂ h₂
    rcases le_total k₁ k₂ with hk | hk
    · have hcarry := is_exec_stable (sys := specInst P X)
        (fun s => s.core = some C₁) (fun s l μ s' => core_stable s l μ s')
        h_exec' k₁ k₂ s₁ s₂ hk hst₁ hst₂ hC₁
      rw [hcarry] at hC₂
      exact Option.some.inj hC₂
    · have hcarry := is_exec_stable (sys := specInst P X)
        (fun s => s.core = some C₂) (fun s l μ s' => core_stable s l μ s')
        h_exec' k₂ k₁ s₂ s₁ hk hst₂ hst₁ hC₂
      rw [hcarry] at hC₁
      exact (Option.some.inj hC₁).symm

/-- Trace-distribution inclusion of the composed gather instance in the gather
specification read over the instance's interface, the soundness of
`gatherCore`. -/
theorem instanceOverBroadcastSpecification_refines (P : Params) (X : Type) [DecidableEq X] :
    achievableTraceDists (instanceOverBroadcastSpecification P X) ⊆ achievableTraceDists
      (specificationOverInstanceAlphabet P X) :=
  (ForwardSimulation.toProbabilistic (instanceOverBroadcastSpecification_isLTS P)
    (specificationOverInstanceAlphabet_isLTS P)
    coreRel_init (gatherCore P X)).achievableTraceDists_subset

/-- **The composed gather instance binds one core.** -/
theorem instanceOverBroadcastSpecification_core (P : Params) (X : Type) [DecidableEq X] :
    ∀ D ∈ achievableTraceDists (instanceOverBroadcastSpecification P X), ∀ t, D t ≠ 0 →
      CoreTrace P (t.map subDown) :=
  safety_transfer (instanceOverBroadcastSpecification_refines P X)
    (specificationOverInstanceAlphabet_core P X)

/-! ### Mechanical axiom check -/

/-- info: 'PLTS.ABA.Gather.gatherCore' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms gatherCore

/-- info: 'PLTS.ABA.Gather.single_core' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms single_core

/-- info: 'PLTS.ABA.Gather.specificationOverInstanceAlphabet_core' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms specificationOverInstanceAlphabet_core

/-- info: 'PLTS.ABA.Gather.instanceOverBroadcastSpecification_core' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms instanceOverBroadcastSpecification_core


end Gather
end ABA
end PLTS
