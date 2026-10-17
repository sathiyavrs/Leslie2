/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sathiya / Claude
-/

import Leslie2Protocols.ABA.Gather.SpecificationRelation
import Leslie2Protocols.Framework.WeakTransitionsFromChains

/-!
# The refinement of the composed gather instance

`Gather.refinesSpecification`: the composed gather instance over broadcast
specifications (`ABA/Gather/Composition.lean`) forward-simulates the gather
specification `Gather.specInst`, along `Gather.SpecificationRelation`
(`ABA/Gather/SpecificationRelation.lean`).

A transition of the instance is one transition of `AlgorithmOverBroadcastSpecification` at the
same label (`Gather.instanceOverBroadcastSpecification_step_algorithm`), and that transition is
matched by a weak run of the gather specification at that label
(`specificationRelation_transition`). `instanceOverBroadcastSpecification_refines` is the
trace-distribution inclusion the simulation yields.

The specification's abstract content is committed lazily, in the
exclude-on-demand style: the committed entries (`val`) and the core (`core`) are
both written inside the return run, at the first return that needs them. The run
is

```
commit*  ;  bindCore?  ;  ret
```

built by recursion with `weakLStep_tauCons` -- one `commit` per entry of the
returned map not yet committed, the core write if the instance has no core yet, then
the return.

* Entry commits are licensed by two clauses of the invariant: a committed input entry of a correct
  process is the payload that input instance was called with
  (`inputBroadcastVal_of_instanceInput`), and that payload is the one the process's own variables
  hold (`inputBroadcastCall_backed`), which the relation identifies with the specification's
  call.
* The core written is `coreOfNetwork` of the instance's gather network state, and the
  two guards of `bindCore` are `Gather.coreOf_recorded`, which the returner's
  quorum of `n − f` delivered `BIND` payloads supplies.
* Every return, the first included, is matched through the witness `withoutBindAbove`: at most `f`
  processes outside `F` have sent no `BIND` payload containing the recorded core
  (`SpecificationRelation.withoutBindAbove_card`, and `coreOf_recorded` at the first return, which
  bounds it by `n − |Q| ≤ f`). The returner's quorum of `n − f` therefore has a member outside `F`
  whose one `BIND` payload contains the core and was delivered to the returner, so it is a sub-map
  of the returned map (`subMap_of_withoutBindAbove_card`).
* The announcement of the core is matched by the specification's `announceCore`: the instance
  announces a written core alone, and the relation identifies the two cores
  (`SpecificationRelation.core_eq`).

Three lemmas beside the refinement hold the relation across one transition:
`specificationRelation_call` for the call, `specificationRelation_inputBroadcastCall` for the call
of an input instance, and `specificationRelation_tau` for an internal transition under a stuttering
specification. `specificationRelation_transition` is assembled from the three.

## The calls

The call label carries two transitions at the instance and at the specification. The gather
program's variables move on the call at a program holding no input and stand on the loop at a
program holding one; the specification's `call` moves under the same write-once guard, which the
relation identifies, and its `callLoop` stands at every state. The call of an input instance is an
event of the instance's own alphabet, at which the specification stands, whichever of its two
transitions the input instance takes.
-/

namespace PLTS
namespace ABA
namespace Gather

variable {X : Type} [DecidableEq X] {P : Parameters}

/-! ### The return run

The specification's committed entries are written one at a time, by a chain of
`commit` steps folded over a list of processes; `commitOne` commits one entry of
the returned map if it is not committed yet, and `commitList` folds it. The
chain is prepended to the matching weak step by recursion with
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
      obtain rfl : (g k').get hc.1 = v := by
        injection h
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
  | k :: l, t, _, _, h =>
    by
    rcases commitList_val_new l (commitOne g k t) h with h' | h'
    · exact commitOne_val_new g h'
    · exact Or.inr h'

omit [DecidableEq X] in
private theorem commitList_covers :
    ∀ (l : List (Fin P.n)) (t : SpecState P.n X),
      (∀ k y x, g k = some x → t.val k = some y → y = x) →
      ∀ k ∈ l, ∀ x, g k = some x → (commitList g l t).val k = some x
  | [], _, _, k, hk, _, _ => absurd hk (by simp)
  | k₀ :: l, t, hpre, k, hk, x, hx =>
    by
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

/-- Prepend the commit chain to a matching weak step. -/
private theorem weakLStep_after_commits {l₀ : Label P.n X} {t' : SpecState P.n X} :
    ∀ (l : List (Fin P.n)) (t : SpecState P.n X),
      (∀ k ∈ l, ∀ x, g k = some x → t.val k = none → k ∈ t.F ∨ t.call k = some x) →
      (specInst P X).weakLStep (commitList g l t) l₀ t' →
      (specInst P X).weakLStep t l₀ t'
  | [], _, _, htail => htail
  | k :: rest, t, hg, htail =>
    by
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
  | k :: l, t =>
    by
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
  | k :: l, t, hg =>
    by
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

The whole matching run of a return, packaged as a τ-chain of
specification steps with the return guards at its end and the relation restored
across the pair of return effects — the shape a larger system that embeds the
gather specification's transitions can replay without re-proving the run. -/

omit [DecidableEq X] in
/-- **A core below the returned map.** If at most `f` processes outside `F` have sent no `BIND`
payload containing `C`, and the returner `id` has received from each member of an `n − f` quorum a
`BIND` payload that is a sub-map of `g`, then `C` is a sub-map of `g`. The quorum has a member `d`
outside `F` that has sent a `BIND` payload containing `C`. The payload `d` sent to `id` is the same
one, since a process outside `F` sends a single `BIND` payload (`bind_confirmed`). -/
private theorem subMap_of_withoutBindAbove_card {s : StateOverBroadcastSpecification P.n X}
    (hInv : Invariant P s) {id : Fin P.n} {g : Fin P.n → Option X} {Q : Finset (Fin P.n)}
    {C : AcceptedPairs P.n X} (hQ : P.n - P.f ≤ Q.card)
    (hQm : ∀ q ∈ Q, ∃ U, Message.bind U ∈ (gatherProgramsAndNetwork s).received id q ∧
      AcceptedPairs.subMap U g)
    (hcard : (withoutBindAbove s C).card ≤ P.f) :
    AcceptedPairs.subMap C g := by
  obtain ⟨d, hdQ, hdF, U, hU, hCU⟩ := exists_correct_bindAbove_of_quorum hInv.F_card hQ hcard
  obtain ⟨Ud, hUd, hUdg⟩ := hQm d hdQ
  have h1 := hInv.bind_confirmed d hdF U hU
  have h2 := hInv.bind_confirmed d hdF Ud (hInv.received_subset_sent id d hUd)
  rw [h1] at h2
  obtain rfl : U = Ud := Option.some.inj h2
  exact AcceptedPairs.subMap_mono hCU hUdg

theorem retRun {s : StateOverBroadcastSpecification P.n X} {t : SpecState P.n X}
    (hR : SpecificationRelation P s t) {id : Fin P.n} {g : Fin P.n → Option X}
    (hin : ((gatherProgramsAndNetwork s).processVariables id).input ≠ none)
    (hbind : ((gatherProgramsAndNetwork s).processVariables id).sentBind ≠ none)
    (hsub : ∀ k x, g k = some x → holdsInputBroadcastReturn ((gatherProgramsAndNetwork
      s).processVariables id) k
      x)
    (hQ : ∃ Q : Finset (Fin P.n), P.n - P.f ≤ Q.card ∧
      ∀ q ∈ Q, ∃ U,
        Message.bind U ∈ (gatherProgramsAndNetwork s).received id q ∧ AcceptedPairs.subMap U g)
    (hr : ((gatherProgramsAndNetwork s).processVariables id).returned = false) :
    ∃ ts : List (SpecState P.n X),
      List.IsChain (fun a b => Step P a Label.tau (PMF.pure b)) (t :: ts) ∧
      (ts.getLastD t).core = some ((core s).getD (coreOfNetwork P (gatherProgramsAndNetwork s).2)) ∧
      AcceptedPairs.subMap ((core s).getD (coreOfNetwork P (gatherProgramsAndNetwork s).2)) g ∧
      (∀ k x, g k = some x → (ts.getLastD t).val k = some x) ∧
      (ts.getLastD t).ret id = false ∧
      SpecificationRelation P
        (setCore (setGatherProgramsAndNetwork s ((gatherProgramsAndNetwork s).setProcessVariables id
          { (gatherProgramsAndNetwork
          s).processVariables id with
          returned := true }))
          (some ((core s).getD (coreOfNetwork P (gatherProgramsAndNetwork s).2))))
        { ts.getLastD t with ret := Function.update (ts.getLastD t).ret id true } := by classical
  set C : AcceptedPairs P.n X := (core s).getD (coreOfNetwork P (gatherProgramsAndNetwork s).2) with
    hC_def
  have hInv' := hR.invariant.step
    (AlgorithmOverBroadcastSpecification.ret s id g hin hbind hsub hQ hr)
    (by rw [PMF.mem_support_pure_iff])
  have hsubv : ∀ k x, g k = some x → (inputBroadcasts s k).val = some x :=
    fun k x hx => hR.invariant.inputBroadcastReturned_val id k x (hsub k x hx)
  obtain ⟨Q, hQc, hQm⟩ := hQ
  set l : List (Fin P.n) := (Finset.univ.filter (fun k => (g k).isSome)).toList with hl
  have hguard : ∀ k ∈ l, ∀ x, g k = some x → t.val k = none →
      k ∈ t.F ∨ t.call k = some x := by
    intro k _ x hx _
    by_cases hF : k ∈ (gatherProgramsAndNetwork s).F
    · left
      rw [hR.F_eq]
      exact hF
    · right
      rcases hR.invariant.inputBroadcastVal_of_instanceInput k x (hsubv k x hx) with hF' | hin'
      · exact absurd hF' hF
      · rw [hR.call_eq k]
        exact hR.invariant.inputBroadcastCall_backed k hF x hin'
  have hpre : ∀ k y x, g k = some x → t.val k = some y → y = x := by
    intro k y x hx hy
    have h1 := hR.val_witness k y hy
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
  -- The relation across the pair of return effects, at the end of the chain.
  have hrel : ∀ (t' : SpecState P.n X), t'.call = (commitList g l t).call →
      t'.ret = (commitList g l t).ret → t'.F = (commitList g l t).F →
      (∀ k v, t'.val k = some v → (commitList g l t).val k = some v) →
      t'.core = some C → (withoutBindAbove s C).card ≤ P.f →
      SpecificationRelation P
        (setCore (setGatherProgramsAndNetwork s ((gatherProgramsAndNetwork s).setProcessVariables id
          { (gatherProgramsAndNetwork
          s).processVariables id with
          returned := true }))
          (some C))
        { t' with ret := Function.update t'.ret id true } := by
    intro t' hcall hret hF hval hcore hcount
    refine ⟨hInv', ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals dsimp only [gatherProgramsAndNetwork_setCore,
      gatherProgramsAndNetwork_setGatherProgramsAndNetwork, inputBroadcasts_setCore,
      inputBroadcasts_setGatherProgramsAndNetwork, core_setCore]
    · intro k
      rw [hcall, commitList_call]
      by_cases hk : k = id
      · subst hk
        rw [InstanceState.setProcessVariables_processVariables_self]
        exact hR.call_eq k
      · rw [InstanceState.setProcessVariables_processVariables_ne _ _ _ hk]
        exact hR.call_eq k
    · intro k
      by_cases hk : k = id
      · subst hk
        rw [Function.update_self, InstanceState.setProcessVariables_processVariables_self]
      · rw [Function.update_of_ne hk, hret, commitList_ret,
          InstanceState.setProcessVariables_processVariables_ne _ _ _ hk]
        exact hR.ret_eq k
    · rw [hF, commitList_F]
      exact hR.F_eq
    · intro k v hv
      rcases commitList_val_new g l t (hval k v hv) with hold | hnew
      · exact hR.val_witness k v hold
      · exact hsubv k v hnew
    · exact hcore
    · intro C' hC'
      obtain rfl : C = C' := Option.some.inj hC'
      refine le_trans (Finset.card_le_card (withoutBindAbove_step
        (AlgorithmOverBroadcastSpecification.ret s id g hin hbind hsub ⟨Q, hQc, hQm⟩ hr)
        (by rw [PMF.mem_support_pure_iff]) C)) hcount
  rcases hcore : core s with _ | C₀
  · -- no core yet: write `coreOfNetwork` at the end of the chain
    have hCcore : C = coreOfNetwork P (gatherProgramsAndNetwork s).2 := by
      simp [hC_def, hcore]
    obtain ⟨hcard, -, hcount⟩ :=
      coreOf_recorded hR.invariant hQc (fun q hq => (hQm q hq).imp fun _ h => h.1)
    rw [← hCcore] at hcard hcount
    have hCg : AcceptedPairs.subMap C g :=
      subMap_of_withoutBindAbove_card hR.invariant hQc hQm hcount
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
      exact hrel _ rfl rfl rfl (fun _ _ h => h) rfl hcount
  · -- a core written earlier: the witness meets the return quorum
    have hCcore : C = C₀ := by
      simp [hC_def, hcore]
    have hcount : (withoutBindAbove s C).card ≤ P.f := by
      rw [hCcore]; exact hR.withoutBindAbove_card C₀ hcore
    have hCg : AcceptedPairs.subMap C g :=
      subMap_of_withoutBindAbove_card hR.invariant hQc hQm hcount
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
      exact hrel _ rfl rfl rfl (fun _ _ h => h) hlastcore hcount


/-! ### The relation across the internal and the call transitions

The two lemmas `specificationRelation_transition` is assembled from. -/

omit [DecidableEq X] in
/-- The relation across the call: the gather program and the specification both record the
payload. -/
theorem specificationRelation_call {s : StateOverBroadcastSpecification P.n X} {t : SpecState P.n X}
    (hR : SpecificationRelation P s t) {id : Fin P.n} {x : X}
    (h : ((gatherProgramsAndNetwork s).processVariables id).input = none) :
    SpecificationRelation P
      (setGatherProgramsAndNetwork s ((gatherProgramsAndNetwork s).setProcessVariables id {
        (gatherProgramsAndNetwork s).processVariables id
        with input := some x }))
      { t with call := Function.update t.call id (some x) } := by
  classical
  refine ⟨hR.invariant.step (AlgorithmOverBroadcastSpecification.call s id x h) (by rw
    [PMF.mem_support_pure_iff]),
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals dsimp only [gatherProgramsAndNetwork_setGatherProgramsAndNetwork,
    inputBroadcasts_setGatherProgramsAndNetwork]
  · intro k
    by_cases hk : k = id
    · subst hk
      rw [Function.update_self, InstanceState.setProcessVariables_processVariables_self]
    · rw [Function.update_of_ne hk, InstanceState.setProcessVariables_processVariables_ne _ _ _ hk]
      exact hR.call_eq k
  · intro k
    by_cases hk : k = id
    · subst hk
      rw [InstanceState.setProcessVariables_processVariables_self]
      exact hR.ret_eq k
    · rw [InstanceState.setProcessVariables_processVariables_ne _ _ _ hk]
      exact hR.ret_eq k
  · exact hR.F_eq
  · exact hR.val_witness
  · exact hR.core_eq
  · exact hR.withoutBindAbove_card

omit [DecidableEq X] in
/-- The relation across the call of an input instance: the instance records the payload and the
specification stands. -/
theorem specificationRelation_inputBroadcastCall {s : StateOverBroadcastSpecification P.n X}
    {t : SpecState P.n X} (hR : SpecificationRelation P s t) {j : Fin P.n} {x : X}
    (hin : ((gatherProgramsAndNetwork s).processVariables j).input = some x) (hb : (inputBroadcasts
      s j).input =
      none) :
    SpecificationRelation P
      (setInputBroadcasts s
        (Function.update (inputBroadcasts s) j
          { inputBroadcasts s j with input := some x })) t := by
  classical
  refine ⟨hR.invariant.step (AlgorithmOverBroadcastSpecification.inputBroadcastCall s j x hin hb)
    (by rw [PMF.mem_support_pure_iff]),
    hR.call_eq, hR.ret_eq, hR.F_eq, ?_, hR.core_eq, ?_⟩
  · intro k v hv
    dsimp only [inputBroadcasts_setInputBroadcasts]
    by_cases hk : k = j
    · subst hk
      rw [Function.update_self]
      exact hR.val_witness k v hv
    · rw [Function.update_of_ne hk]
      exact hR.val_witness k v hv
  · intro C hC
    exact le_trans (Finset.card_le_card (withoutBindAbove_step
      (AlgorithmOverBroadcastSpecification.inputBroadcastCall s j x hin hb)
      (by rw [PMF.mem_support_pure_iff]) C)) (hR.withoutBindAbove_card C hC)

/-- The relation across any internal transition, the specification stuttering. -/
theorem specificationRelation_tau {s s' : StateOverBroadcastSpecification P.n X}
    {t : SpecState P.n X} (hR : SpecificationRelation P s t)
    (hstep : AlgorithmOverBroadcastSpecification P s Gather.Label.tau (PMF.pure s')) :
    SpecificationRelation P s' t := by
  have hInv' := hR.invariant.step hstep (by rw [PMF.mem_support_pure_iff])
  have hW : ∀ C, core s = some C → (withoutBindAbove s' C).card ≤ P.f := fun C hC =>
    le_trans (Finset.card_le_card
      (withoutBindAbove_step hstep (by rw [PMF.mem_support_pure_iff]) C))
      (hR.withoutBindAbove_card C hC)
  generalize hμ : (PMF.pure s' : PMF (StateOverBroadcastSpecification P.n X)) = μ at hstep
  cases hstep with
  | inputBroadcastCall j x hin hb =>
    have hs' := PMF.pure_injective hμ
    subst hs'
    exact specificationRelation_inputBroadcastCall hR hin hb
  | inputBroadcastCallLoop j x hin =>
    have hs' := PMF.pure_injective hμ
    subst hs'
    exact hR
  | commitInputEntry k v hv hm =>
    have hs' := PMF.pure_injective hμ
    subst hs'
    refine ⟨hInv', hR.call_eq, hR.ret_eq, hR.F_eq, ?_, hR.core_eq, hW⟩
    all_goals dsimp only [inputBroadcasts_setInputBroadcasts]
    · intro k' v' hv'
      have hold := hR.val_witness k' v' hv'
      by_cases hk : k' = k
      · subst hk; rw [hv] at hold; exact absurd hold (by simp)
      · rw [Function.update_of_ne hk]; exact hold
  | deliver i j m h =>
    have hs' := PMF.pure_injective hμ
    subst hs'
    refine ⟨hInv', ?_, ?_, hR.F_eq, hR.val_witness, hR.core_eq, hW⟩
    all_goals dsimp only [gatherProgramsAndNetwork_setGatherProgramsAndNetwork]
    · intro k
      rw [InstanceState.receiveMessage_processVariables]
      exact hR.call_eq k
    · intro k
      rw [InstanceState.receiveMessage_processVariables]
      exact hR.ret_eq k
  | echo j hin hcard hsend =>
    have hs' := PMF.pure_injective hμ
    subst hs'
    refine ⟨hInv', ?_, ?_, hR.F_eq, hR.val_witness, hR.core_eq, hW⟩
    all_goals dsimp only [gatherProgramsAndNetwork_setGatherProgramsAndNetwork]
    · intro k
      by_cases hk : k = j
      · subst hk
        rw [InstanceState.multicast_processVariables,
          InstanceState.setProcessVariables_processVariables_self]
        exact hR.call_eq k
      · rw [InstanceState.multicast_processVariables,
          InstanceState.setProcessVariables_processVariables_ne _ _ _ hk]
        exact hR.call_eq k
    · intro k
      by_cases hk : k = j
      · subst hk
        rw [InstanceState.multicast_processVariables,
          InstanceState.setProcessVariables_processVariables_self]
        exact hR.ret_eq k
      · rw [InstanceState.multicast_processVariables,
          InstanceState.setProcessVariables_processVariables_ne _ _ _ hk]
        exact hR.ret_eq k
  | vote j U hin hech happ hQ hsend =>
    have hs' := PMF.pure_injective hμ
    subst hs'
    refine ⟨hInv', ?_, ?_, hR.F_eq, hR.val_witness, hR.core_eq, hW⟩
    all_goals dsimp only [gatherProgramsAndNetwork_setGatherProgramsAndNetwork]
    · intro k
      by_cases hk : k = j
      · subst hk
        rw [InstanceState.multicast_processVariables,
          InstanceState.setProcessVariables_processVariables_self]
        exact hR.call_eq k
      · rw [InstanceState.multicast_processVariables,
          InstanceState.setProcessVariables_processVariables_ne _ _ _ hk]
        exact hR.call_eq k
    · intro k
      by_cases hk : k = j
      · subst hk
        rw [InstanceState.multicast_processVariables,
          InstanceState.setProcessVariables_processVariables_self]
        exact hR.ret_eq k
      · rw [InstanceState.multicast_processVariables,
          InstanceState.setProcessVariables_processVariables_ne _ _ _ hk]
        exact hR.ret_eq k
  | bind j U hin hvot happ hQ hsend =>
    have hs' := PMF.pure_injective hμ
    subst hs'
    refine ⟨hInv', ?_, ?_, hR.F_eq, hR.val_witness, hR.core_eq, hW⟩
    all_goals dsimp only [gatherProgramsAndNetwork_setGatherProgramsAndNetwork]
    · intro k
      by_cases hk : k = j
      · subst hk
        rw [InstanceState.multicast_processVariables,
          InstanceState.setProcessVariables_processVariables_self]
        exact hR.call_eq k
      · rw [InstanceState.multicast_processVariables,
          InstanceState.setProcessVariables_processVariables_ne _ _ _ hk]
        exact hR.call_eq k
    · intro k
      by_cases hk : k = j
      · subst hk
        rw [InstanceState.multicast_processVariables,
          InstanceState.setProcessVariables_processVariables_self]
        exact hR.ret_eq k
      · rw [InstanceState.multicast_processVariables,
          InstanceState.setProcessVariables_processVariables_ne _ _ _ hk]
        exact hR.ret_eq k
  | byzantine j m hmem =>
    have hs' := PMF.pure_injective hμ
    subst hs'
    refine ⟨hInv', ?_, ?_, hR.F_eq, hR.val_witness, hR.core_eq, hW⟩
    all_goals dsimp only [gatherProgramsAndNetwork_setGatherProgramsAndNetwork]
    · intro k
      rw [InstanceState.multicast_processVariables]
      exact hR.call_eq k
    · intro k
      rw [InstanceState.multicast_processVariables]
      exact hR.ret_eq k
  | inputBroadcastRet k j v hv hr =>
    have hs' := PMF.pure_injective hμ
    subst hs'
    refine ⟨hInv', ?_, ?_, hR.F_eq, ?_, hR.core_eq, hW⟩
    all_goals dsimp only [gatherProgramsAndNetwork_setInputBroadcasts,
      gatherProgramsAndNetwork_setGatherProgramsAndNetwork,
      inputBroadcasts_setInputBroadcasts]
    · intro id'
      by_cases hj : id' = j
      · subst hj; rw [InstanceState.setProcessVariables_processVariables_self]; exact hR.call_eq id'
      · rw [InstanceState.setProcessVariables_processVariables_ne _ _ _ hj]; exact hR.call_eq id'
    · intro id'
      by_cases hj : id' = j
      · subst hj; rw [InstanceState.setProcessVariables_processVariables_self]; exact hR.ret_eq id'
      · rw [InstanceState.setProcessVariables_processVariables_ne _ _ _ hj]; exact hR.ret_eq id'
    · intro k' v' hv'
      by_cases hk : k' = k
      · subst hk; rw [Function.update_self]; exact hR.val_witness k' v' hv'
      · rw [Function.update_of_ne hk]; exact hR.val_witness k' v' hv'


/-! ### The relation across one transition -/

/-- **The relation across one transition**: every transition of
`AlgorithmOverBroadcastSpecification` at a related pair is matched by a weak run of the gather
specification, ending at a related state. Internal transitions stutter, the call of an input
instance among them; the call, the call loop, the announcement of the core and `fail` are matched
by the specification's own transitions; a return is matched by the run
`commit* ; bindCore? ; ret`. -/
theorem specificationRelation_transition (P : Parameters) (X : Type) [DecidableEq X]
    (q₁ : StateOverBroadcastSpecification P.n X) (q₂ : SpecState P.n X)
    (hR : SpecificationRelation P q₁ q₂) (l₀ : Label P.n X)
    (μ : PMF (StateOverBroadcastSpecification P.n X))
    (htransition : AlgorithmOverBroadcastSpecification P q₁ l₀ μ)
    (q₁' : StateOverBroadcastSpecification P.n X) (hq₁' : q₁' ∈ μ.support) :
    ∃ q₂', ((l₀ = Silent.τ ∧ (specInst P X).weakLSilent q₂ q₂') ∨
      (¬ l₀ = Silent.τ ∧ (specInst P X).weakLStep q₂ l₀ q₂')) ∧
      SpecificationRelation P q₁' q₂' := by
  cases htransition with
  | call id x h =>
    rw [PMF.mem_support_pure_iff] at hq₁'
    subst hq₁'
    exact ⟨{ q₂ with call := Function.update q₂.call id (some x) },
      Or.inr ⟨by simp, System.weakLStep_of_step (by simp)
        (Step.call q₂ id x (by rw [hR.call_eq id]; exact h))⟩,
      specificationRelation_call hR h⟩
  | callLoop id x hin =>
    rw [PMF.mem_support_pure_iff] at hq₁'
    subst hq₁'
    exact ⟨q₂, Or.inr ⟨by simp, System.weakLStep_of_step (by simp)
      (Step.callLoop q₂ id x)⟩, hR⟩
  | inputBroadcastCall j x hin hb =>
    rw [PMF.mem_support_pure_iff] at hq₁'
    subst hq₁'
    exact ⟨q₂, Or.inl ⟨rfl, System.weakLSilent_refl _ q₂⟩,
      specificationRelation_inputBroadcastCall hR hin hb⟩
  | inputBroadcastCallLoop j x hin =>
    rw [PMF.mem_support_pure_iff] at hq₁'
    subst hq₁'
    exact ⟨q₂, Or.inl ⟨rfl, System.weakLSilent_refl _ q₂⟩, hR⟩
  | commitInputEntry k v hv hm =>
    rw [PMF.mem_support_pure_iff] at hq₁'
    subst hq₁'
    exact ⟨q₂, Or.inl ⟨rfl, System.weakLSilent_refl _ q₂⟩,
      specificationRelation_tau hR
        (AlgorithmOverBroadcastSpecification.commitInputEntry q₁ k v hv hm)⟩
  | deliver i j m h =>
    rw [PMF.mem_support_pure_iff] at hq₁'
    subst hq₁'
    exact ⟨q₂, Or.inl ⟨rfl, System.weakLSilent_refl _ q₂⟩,
      specificationRelation_tau hR (AlgorithmOverBroadcastSpecification.deliver q₁ i j m h)⟩
  | echo j hin hcard hsend =>
    rw [PMF.mem_support_pure_iff] at hq₁'
    subst hq₁'
    exact ⟨q₂, Or.inl ⟨rfl, System.weakLSilent_refl _ q₂⟩,
      specificationRelation_tau hR (AlgorithmOverBroadcastSpecification.echo q₁ j hin hcard hsend)⟩
  | vote j U hin hech happ hQ hsend =>
    rw [PMF.mem_support_pure_iff] at hq₁'
    subst hq₁'
    exact ⟨q₂, Or.inl ⟨rfl, System.weakLSilent_refl _ q₂⟩,
      specificationRelation_tau hR (AlgorithmOverBroadcastSpecification.vote q₁ j U hin hech happ hQ
        hsend)⟩
  | bind j U hin hvot happ hQ hsend =>
    rw [PMF.mem_support_pure_iff] at hq₁'
    subst hq₁'
    exact ⟨q₂, Or.inl ⟨rfl, System.weakLSilent_refl _ q₂⟩,
      specificationRelation_tau hR
        (AlgorithmOverBroadcastSpecification.bind q₁ j U hin hvot happ hQ hsend)⟩
  | byzantine j m h =>
    rw [PMF.mem_support_pure_iff] at hq₁'
    subst hq₁'
    exact ⟨q₂, Or.inl ⟨rfl, System.weakLSilent_refl _ q₂⟩,
      specificationRelation_tau hR (AlgorithmOverBroadcastSpecification.byzantine q₁ j m h)⟩
  | inputBroadcastRet k j v hv hr =>
    rw [PMF.mem_support_pure_iff] at hq₁'
    subst hq₁'
    exact ⟨q₂, Or.inl ⟨rfl, System.weakLSilent_refl _ q₂⟩,
      specificationRelation_tau hR
        (AlgorithmOverBroadcastSpecification.inputBroadcastRet q₁ k j v hv hr)⟩
  | ret id g hin hbind hsub hQ hr =>
    rw [PMF.mem_support_pure_iff] at hq₁'
    subst hq₁'
    obtain ⟨ts, hchain, hcore, hmem, hcov, hret1, hRel⟩ :=
      retRun hR hin hbind hsub hQ hr
    have hretstep : Step P (ts.getLastD q₂) (Label.ret id g)
        (PMF.pure { ts.getLastD q₂ with
          ret := Function.update (ts.getLastD q₂).ret id true }) :=
      Step.ret _ id g _ hcore hmem hcov hret1
    exact ⟨_, Or.inr ⟨by simp,
      System.weakLStep_tausThen hchain hretstep (by simp)⟩, hRel⟩
  | announceCore C h =>
    rw [PMF.mem_support_pure_iff] at hq₁'
    subst hq₁'
    exact ⟨q₂, Or.inr ⟨by simp, System.weakLStep_of_step (by simp)
      (Step.announceCore q₂ C (by rw [hR.core_eq]; exact h))⟩, hR⟩
  | fail id =>
    rw [PMF.mem_support_pure_iff] at hq₁'
    subst hq₁'
    exact ⟨q₂.corrupt P id, Or.inr ⟨by simp, System.weakLStep_of_step (by simp)
      (Step.fail q₂ id)⟩, specificationRelation_corrupt hR id⟩

/-! ### The refinement -/

/-- **The refinement of the composed gather instance**: the instance over
broadcast specifications forward-simulates the gather specification. A transition of the instance
is one transition of `AlgorithmOverBroadcastSpecification` at the same label
(`Gather.instanceOverBroadcastSpecification_step_algorithm`), and that transition is matched by a
weak run of the specification at that label (`specificationRelation_transition`). -/
theorem refinesSpecification (P : Parameters) (X : Type) [DecidableEq X] :
    ForwardSimulation (instanceOverBroadcastSpecification P X) (specInst P X)
      (SpecificationRelation P) :=
  ⟨fun q₁ q₂ hR l μ hstep q₁' hq₁' => specificationRelation_transition P X q₁ q₂ hR l μ
    (instanceOverBroadcastSpecification_step_algorithm P q₁ l μ hstep) q₁' hq₁'⟩

/-- Trace-distribution inclusion of the composed gather instance in the gather
specification, the soundness of `refinesSpecification`. -/
theorem instanceOverBroadcastSpecification_refines (P : Parameters) (X : Type) [DecidableEq X] :
    achievableTraceDists (instanceOverBroadcastSpecification P X) ⊆ achievableTraceDists
      (specInst P X) :=
  (ForwardSimulation.toProbabilistic (instanceOverBroadcastSpecification_isLTS P)
    (specInst_isLTS P)
    specificationRelation_init (refinesSpecification P X)).achievableTraceDists_subset

/-! ### Mechanical axiom check -/

/-- info: 'PLTS.ABA.Gather.refinesSpecification' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms refinesSpecification

/-- info: 'PLTS.ABA.Gather.single_core' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms single_core

end Gather
end ABA
end PLTS
