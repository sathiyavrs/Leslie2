/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sathiya / Claude
-/

import Leslie2Protocols.ABA.Gather.Core
import Leslie2Protocols.Framework.FamilySim
import Leslie2Protocols.Framework.WeakRun

/-!
# The gather refinement: the ECHO/VOTE rounds implement the specification

`Gather.gatherCore`: the gather-over-BRB-specification instance
(`ABA/Gather/Ideal.lean`) forward-simulates the gather specification
(`ABA/Gather/Spec.lean`), along `Gather.CoreRel`.

The specification's abstract content is committed lazily, in the
exclude-on-demand style: the committed entries (`val`) and the core (`core`)
are both written inside the return run, at the first return that needs them.
The run is

```
commit*  ;  bindCore?  ;  ret
```

built by recursion with `weakLStep_tauCons` — one `commit` per entry of the
returned map not yet committed, the freeze if the instance has no core yet,
then the return.

* Entry commits are licensed by the invariant's provenance clause: a
  committed input-BRB entry of an honest process is that process's input,
  which the relation identifies with the specification's call record.
* The core frozen is `coreOf` of the instance's message state, and the two
  guards of `bindCore` are `Gather.coreOf_freeze`, which the returner's
  quorum of `n − f` committed bind payloads supplies.
* Every return, the first included, is matched through the count
  `CoreRel.core_cert`: at least `f + 1` bind-BRB instances hold a committed
  payload above the frozen core. The count is blind to `F` and monotone —
  committed payloads are written once (`Gather.bindAbove_mono`) — so it
  survives every rule and every corruption. The returner's quorum of `n − f`
  meets it in a coordinate whose committed payload lies above the core and
  below the returned map.

The last point is where the `BIND`-by-reliable-broadcast design of the
implementation pays: the count reads *committed* payloads, which a sender
corrupted after the freeze cannot rewrite.

The relation carries the implementation's `core` field and the
specification's as equal, so the core a return label carries is the same on
both sides.
-/

namespace PLTS
namespace ABA
namespace Gather

variable {X : Type} [DecidableEq X] {P : Params}

/-! ### The relation -/

/-- The gather refinement relation. `val_cert` bounds the specification's
committed entries by the input-BRB commitments; `core_cert` is the count,
blind to `F` and monotone, pinning the frozen core below committed bind
payloads. -/
structure CoreRel (P : Params) (s : IdealState P.n X) (t : SpecState P.n X) : Prop where
  /-- The implementation invariant. -/
  inv : IdealInv P s
  /-- The call records agree. -/
  call_eq : ∀ k, t.call k = (s.ga.proc k).input
  /-- The return flags agree. -/
  ret_eq : ∀ id, t.ret id = (s.ga.proc id).returned
  /-- The corrupted sets agree. -/
  F_eq : t.F = s.ga.F
  /-- A committed specification entry is a committed input-BRB entry. -/
  val_cert : ∀ k v, t.val k = some v → (s.brbIn k).val = some v
  /-- The two sides hold the same core. -/
  core_eq : t.core = s.core
  /-- At least `f + 1` bind-BRB instances hold a committed payload above the
  frozen core. -/
  core_cert : ∀ C, s.core = some C → P.f + 1 ≤ (bindAbove s C).card

/-- The relation holds initially. -/
theorem coreRel_init :
    CoreRel P (IdealState.initial P.n X) (SpecState.initial P.n X) := by
  refine ⟨IdealInv.initial, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [IdealState.initial, SpecState.initial, PRec.initial]

/-- **Broadcast compatibility**: the relation is preserved by corrupting both
sides at once. -/
theorem coreRel_corrupt {s : IdealState P.n X} {t : SpecState P.n X}
    (hR : CoreRel P s t) (id : Fin P.n) :
    CoreRel P (s.corruptAll P id) (t.corrupt P id) := by
  refine ⟨hR.inv.step (IdealStep.fail s id) (by rw [PMF.mem_support_pure_iff]),
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro k
    rw [corrupt_call, IdealState.corruptAll_ga_proc]
    exact hR.call_eq k
  · intro k
    rw [corrupt_ret, IdealState.corruptAll_ga_proc]
    exact hR.ret_eq k
  · show (t.corrupt P id).F = (s.ga.corrupt P id).F
    rw [SpecState.corrupt_F, SubState.corrupt_F, hR.F_eq]
  · intro k v hv
    rw [corrupt_val] at hv
    rw [IdealState.corruptAll_brbIn_val]
    exact hR.val_cert k v hv
  · rw [corrupt_core, IdealState.corruptAll_core]
    exact hR.core_eq
  · intro C hC
    rw [IdealState.corruptAll_core] at hC
    exact le_trans (hR.core_cert C hC) (Finset.card_le_card
      (bindAbove_mono (IdealStep.fail s id) (by rw [PMF.mem_support_pure_iff]) C))

/-! ### The return run

The specification's committed entries are written one at a time, by a chain
of `commit` steps folded over a list of processes; `commitOne` commits one
entry of the returned map if it is not committed yet, and `commitList` folds
it. The chain is prepended to the answering weak step by recursion with
`weakLStep_tauCons`. -/

section Run

variable (g : Fin P.n → Option X)

/-- Commit `g`'s entry at `k`, if `g` has one and it is uncommitted. -/
private def commitOne (k : Fin P.n) (t : SpecState P.n X) : SpecState P.n X :=
  if h : (g k).isSome ∧ t.val k = none
  then { t with val := Function.update t.val k (some ((g k).get h.1)) }
  else t

private theorem commitOne_call (k : Fin P.n) (t : SpecState P.n X) :
    (commitOne g k t).call = t.call := by
  unfold commitOne; split <;> rfl

private theorem commitOne_F (k : Fin P.n) (t : SpecState P.n X) :
    (commitOne g k t).F = t.F := by
  unfold commitOne; split <;> rfl

private theorem commitOne_ret (k : Fin P.n) (t : SpecState P.n X) :
    (commitOne g k t).ret = t.ret := by
  unfold commitOne; split <;> rfl

private theorem commitOne_core (k : Fin P.n) (t : SpecState P.n X) :
    (commitOne g k t).core = t.core := by
  unfold commitOne; split <;> rfl

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
    · show Function.update t.val k _ k' = some v
      rw [Function.update_of_ne hk]
      exact h
  · exact h

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

private theorem commitOne_covers {k : Fin P.n} {t : SpecState P.n X} {x : X}
    (hx : g k = some x) (hpre : ∀ y, t.val k = some y → y = x) :
    (commitOne g k t).val k = some x := by
  unfold commitOne
  split
  · next hc =>
    show Function.update t.val k (some ((g k).get hc.1)) k = some x
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
      Step P t Lab.tau (PMF.pure (commitOne g k t)) := by
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

private theorem commitList_call :
    ∀ (l : List (Fin P.n)) (t : SpecState P.n X), (commitList g l t).call = t.call
  | [], _ => rfl
  | k :: l, t => by rw [commitList, commitList_call l, commitOne_call]

private theorem commitList_F :
    ∀ (l : List (Fin P.n)) (t : SpecState P.n X), (commitList g l t).F = t.F
  | [], _ => rfl
  | k :: l, t => by rw [commitList, commitList_F l, commitOne_F]

private theorem commitList_ret :
    ∀ (l : List (Fin P.n)) (t : SpecState P.n X), (commitList g l t).ret = t.ret
  | [], _ => rfl
  | k :: l, t => by rw [commitList, commitList_ret l, commitOne_ret]

private theorem commitList_core :
    ∀ (l : List (Fin P.n)) (t : SpecState P.n X), (commitList g l t).core = t.core
  | [], _ => rfl
  | k :: l, t => by rw [commitList, commitList_core l, commitOne_core]

private theorem commitList_val_mono :
    ∀ (l : List (Fin P.n)) (t : SpecState P.n X) {k' : Fin P.n} {v : X},
      t.val k' = some v → (commitList g l t).val k' = some v
  | [], _, _, _, h => h
  | k :: l, t, _, _, h =>
    commitList_val_mono l (commitOne g k t) (commitOne_val_mono g h)

private theorem commitList_val_new :
    ∀ (l : List (Fin P.n)) (t : SpecState P.n X) {k' : Fin P.n} {v : X},
      (commitList g l t).val k' = some v → t.val k' = some v ∨ g k' = some v
  | [], _, _, _, h => Or.inl h
  | k :: l, t, _, _, h => by
    rcases commitList_val_new l (commitOne g k t) h with h' | h'
    · exact commitOne_val_new g h'
    · exact Or.inr h'

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
private theorem weakLStep_after_commits {l₀ : Lab P.n X} {t' : SpecState P.n X} :
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
    if h : (g k).isSome ∧ t.val k = none
    then commitOne g k t :: commitChain l (commitOne g k t)
    else commitChain l t

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
      List.IsChain (fun a b => Step P a Lab.tau (PMF.pure b)) (t :: commitChain g l t)
  | [], t, _ => List.isChain_singleton t
  | k :: l, t, hg => by
    rw [commitChain]
    split
    · next hc =>
      have hstep : Step P t Lab.tau (PMF.pure (commitOne g k t)) := by
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
specification steps with the return guards at its end and the relation
restored across the pair of return effects — the shape a larger system that
embeds the gather specification's rows can replay without re-proving the
run. -/

theorem retRun {s : IdealState P.n X} {t : SpecState P.n X}
    (hR : CoreRel P s t) {id : Fin P.n} {g : Fin P.n → Option X}
    (hin : (s.ga.proc id).input ≠ none)
    (hsub : ∀ k x, g k = some x → (s.brbIn k).val = some x)
    (hQ : ∃ Q : Finset (Fin P.n), P.n - P.f ≤ Q.card ∧
      ∀ q ∈ Q, ∃ U, (s.brbBind q).val = some U ∧ APSet.subMap U g)
    (hr : (s.ga.proc id).returned = false) :
    ∃ ts : List (SpecState P.n X),
      List.IsChain (fun a b => Step P a Lab.tau (PMF.pure b)) (t :: ts) ∧
      (ts.getLastD t).core = some (s.core.getD (coreOf P s.ga)) ∧
      APSet.subMap (s.core.getD (coreOf P s.ga)) g ∧
      (∀ k x, g k = some x → (ts.getLastD t).val k = some x) ∧
      (ts.getLastD t).ret id = false ∧
      CoreRel P
        { s with
          ga := s.ga.setProc id { s.ga.proc id with returned := true }
          core := some (s.core.getD (coreOf P s.ga)) }
        { ts.getLastD t with ret := Function.update (ts.getLastD t).ret id true } := by
  classical
  set C : APSet P.n X := s.core.getD (coreOf P s.ga) with hC_def
  have hInv' : IdealInv P
      { s with
        ga := s.ga.setProc id { s.ga.proc id with returned := true }
        core := some (s.core.getD (coreOf P s.ga)) } :=
    hR.inv.step (IdealStep.ret s id g hin hsub hQ hr) (by rw [PMF.mem_support_pure_iff])
  obtain ⟨Q, hQc, hQm⟩ := hQ
  set l : List (Fin P.n) := (Finset.univ.filter (fun k => (g k).isSome)).toList with hl
  have hguard : ∀ k ∈ l, ∀ x, g k = some x → t.val k = none →
      k ∈ t.F ∨ t.call k = some x := by
    intro k _ x hx _
    rcases hR.inv.inVal_prov k x (hsub k x hx) with hF | hin'
    · left
      rw [hR.F_eq]
      exact hF
    · right
      rw [hR.call_eq k, ← hR.inv.input_eq k]
      exact hin'
  have hpre : ∀ k y x, g k = some x → t.val k = some y → y = x := by
    intro k y x hx hy
    have h1 := hR.val_cert k y hy
    have h2 := hsub k x hx
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
    if h : ∃ U, (s.brbBind q).val = some U ∧ APSet.subMap U g
    then h.choose else ∅ with hu_def
  have hu : ∀ q ∈ Q, (s.brbBind q).val = some (u q) ∧ APSet.subMap (u q) g := by
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
      t'.core = some (s.core.getD (coreOf P s.ga)) →
      P.f + 1 ≤ (bindAbove s (s.core.getD (coreOf P s.ga))).card →
      CoreRel P
        { s with
          ga := s.ga.setProc id { s.ga.proc id with returned := true }
          core := some (s.core.getD (coreOf P s.ga)) }
        { t' with ret := Function.update t'.ret id true } := by
    intro t' hcall hret hF hval hcore hcnt
    refine ⟨hInv', ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> dsimp only
    · intro k
      rw [hcall, commitList_call]
      by_cases hk : k = id
      · subst hk
        rw [SubState.setProc_proc_self]
        exact hR.call_eq k
      · rw [SubState.setProc_proc_ne _ _ _ hk]
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
      · exact hsub k v hnew
    · exact hcore
    · intro C hC
      obtain rfl : s.core.getD (coreOf P s.ga) = C := Option.some.inj hC
      exact hcnt
  rcases hcore : s.core with _ | C₀
  · -- no core yet: freeze `coreOf` at the end of the chain
    have hCcore : C = coreOf P s.ga := by simp [hC_def, hcore]
    obtain ⟨hcard, -, hcnt⟩ :=
      coreOf_freeze hR.inv hQc (fun q hq => ⟨u q, (hu q hq).1⟩)
    rw [← hCcore] at hcard hcnt
    have hCg : APSet.subMap C g := key _ hcnt
    have hbind : Step P (commitList g l t) Lab.tau
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

/-- The relation across the fused call: the gather record and input-BRB call
effects against the specification's call effect. -/
theorem coreRel_call {s : IdealState P.n X} {t : SpecState P.n X}
    (hR : CoreRel P s t) {id : Fin P.n} {x : X}
    (h : (s.ga.proc id).input = none) :
    CoreRel P
      { s with
        ga := s.ga.setProc id { s.ga.proc id with input := some x }
        brbIn := Function.update s.brbIn id { s.brbIn id with input := some x } }
      { t with call := Function.update t.call id (some x) } := by
  refine ⟨hR.inv.step (IdealStep.call s id x h) (by rw [PMF.mem_support_pure_iff]),
    ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> dsimp only
  · intro k
    by_cases hk : k = id
    · subst hk
      rw [Function.update_self, SubState.setProc_proc_self]
    · rw [Function.update_of_ne hk, SubState.setProc_proc_ne _ _ _ hk]
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
theorem coreRel_tau {s s' : IdealState P.n X} {t : SpecState P.n X}
    (hR : CoreRel P s t) (hstep : IdealStep P s Gather.Lab.tau (PMF.pure s')) :
    CoreRel P s' t := by
  have hInv' := hR.inv.step hstep (by rw [PMF.mem_support_pure_iff])
  generalize hμ : (PMF.pure s' : PMF (IdealState P.n X)) = μ at hstep
  cases hstep with
  | commitIn k v hv hm =>
    have hs' := PMF.pure_injective hμ
    subst hs'
    refine ⟨hInv', hR.call_eq, hR.ret_eq, hR.F_eq, ?_, hR.core_eq, hR.core_cert⟩
    intro k' v' hv'
    have hold := hR.val_cert k' v' hv'
    dsimp only
    by_cases hk : k' = k
    · subst hk
      rw [hv] at hold
      exact absurd hold (by simp)
    · rw [Function.update_of_ne hk]
      exact hold
  | commitBind k U hv hm =>
    have hs' := PMF.pure_injective hμ
    subst hs'
    refine ⟨hInv', hR.call_eq, hR.ret_eq, hR.F_eq, hR.val_cert, hR.core_eq, ?_⟩
    intro C hC
    exact le_trans (hR.core_cert C hC) (Finset.card_le_card
      (bindAbove_mono (IdealStep.commitBind _ k U hv hm)
        (by rw [PMF.mem_support_pure_iff]) C))
  | deliver i j m h =>
    have hs' := PMF.pure_injective hμ
    subst hs'
    refine ⟨hInv', ?_, ?_, hR.F_eq, hR.val_cert, hR.core_eq, hR.core_cert⟩ <;> dsimp only
    · intro k
      rw [SubState.recvMsg_proc]
      exact hR.call_eq k
    · intro k
      rw [SubState.recvMsg_proc]
      exact hR.ret_eq k
  | echo j A hin happ hcard hsend =>
    have hs' := PMF.pure_injective hμ
    subst hs'
    refine ⟨hInv', ?_, ?_, hR.F_eq, hR.val_cert, hR.core_eq, hR.core_cert⟩ <;> dsimp only
    · intro k
      by_cases hk : k = j
      · subst hk
        rw [SubState.mcast_proc, SubState.setProc_proc_self]
        exact hR.call_eq k
      · rw [SubState.mcast_proc, SubState.setProc_proc_ne _ _ _ hk]
        exact hR.call_eq k
    · intro k
      by_cases hk : k = j
      · subst hk
        rw [SubState.mcast_proc, SubState.setProc_proc_self]
        exact hR.ret_eq k
      · rw [SubState.mcast_proc, SubState.setProc_proc_ne _ _ _ hk]
        exact hR.ret_eq k
  | vote j U hin happ hQ hsend =>
    have hs' := PMF.pure_injective hμ
    subst hs'
    refine ⟨hInv', ?_, ?_, hR.F_eq, hR.val_cert, hR.core_eq, hR.core_cert⟩ <;> dsimp only
    · intro k
      by_cases hk : k = j
      · subst hk
        rw [SubState.mcast_proc, SubState.setProc_proc_self]
        exact hR.call_eq k
      · rw [SubState.mcast_proc, SubState.setProc_proc_ne _ _ _ hk]
        exact hR.call_eq k
    · intro k
      by_cases hk : k = j
      · subst hk
        rw [SubState.mcast_proc, SubState.setProc_proc_self]
        exact hR.ret_eq k
      · rw [SubState.mcast_proc, SubState.setProc_proc_ne _ _ _ hk]
        exact hR.ret_eq k
  | bindCall j U hin hb happ hQ =>
    have hs' := PMF.pure_injective hμ
    subst hs'
    refine ⟨hInv', hR.call_eq, hR.ret_eq, hR.F_eq, hR.val_cert, hR.core_eq, ?_⟩
    intro C hC
    exact le_trans (hR.core_cert C hC) (Finset.card_le_card
      (bindAbove_mono (IdealStep.bindCall _ j U hin hb happ hQ)
        (by rw [PMF.mem_support_pure_iff]) C))
  | byz j m hmem =>
    have hs' := PMF.pure_injective hμ
    subst hs'
    exact ⟨hInv', hR.call_eq, hR.ret_eq, hR.F_eq, hR.val_cert, hR.core_eq, hR.core_cert⟩

/-! ### The refinement -/

/-- **The gather refinement**: the gather-over-BRB-specification instance
forward-simulates the gather specification. -/
theorem gatherCore (P : Params) (X : Type) [DecidableEq X] :
    ForwardSimulation (idealInst P X) (specInst P X) (CoreRel P) := by
  constructor
  intro q₁ q₂ hR l μ hstep q₁' hq₁'
  rw [idealInst_step] at hstep
  have hInv' := hR.inv.step hstep hq₁'
  cases hstep with
  | call id x h =>
    rw [PMF.mem_support_pure_iff] at hq₁'
    subst hq₁'
    refine ⟨{ q₂ with call := Function.update q₂.call id (some x) },
      Or.inr ⟨by simp, System.weakLStep_of_step (by simp)
        (Step.call q₂ id x (by rw [hR.call_eq id]; exact h))⟩,
      hInv', ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> dsimp only
    · intro k
      by_cases hk : k = id
      · subst hk
        rw [Function.update_self, SubState.setProc_proc_self]
      · rw [Function.update_of_ne hk, SubState.setProc_proc_ne _ _ _ hk]
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
        have hold := hR.val_cert k v hv
        exact hold
      · rw [Function.update_of_ne hk]
        exact hR.val_cert k v hv
    · exact hR.core_eq
    · exact hR.core_cert
  | callLoop id x =>
    rw [PMF.mem_support_pure_iff] at hq₁'
    subst hq₁'
    exact ⟨q₂, Or.inr ⟨by simp, System.weakLStep_of_step (by simp)
      (Step.callLoop q₂ id x)⟩, hR⟩
  | commitIn k v hv hm =>
    rw [PMF.mem_support_pure_iff] at hq₁'
    subst hq₁'
    refine ⟨q₂, Or.inl ⟨rfl, System.weakLSilent_refl _ q₂⟩,
      hInv', hR.call_eq, hR.ret_eq, hR.F_eq, ?_, hR.core_eq, hR.core_cert⟩
    intro k' v' hv'
    have hold := hR.val_cert k' v' hv'
    dsimp only
    by_cases hk : k' = k
    · subst hk
      rw [hv] at hold
      exact absurd hold (by simp)
    · rw [Function.update_of_ne hk]
      exact hold
  | commitBind k U hv hm =>
    rw [PMF.mem_support_pure_iff] at hq₁'
    subst hq₁'
    refine ⟨q₂, Or.inl ⟨rfl, System.weakLSilent_refl _ q₂⟩,
      hInv', hR.call_eq, hR.ret_eq, hR.F_eq, hR.val_cert, hR.core_eq, ?_⟩
    intro C hC
    exact le_trans (hR.core_cert C hC) (Finset.card_le_card
      (bindAbove_mono (IdealStep.commitBind _ k U hv hm)
        (by rw [PMF.mem_support_pure_iff]) C))
  | deliver i j m h =>
    rw [PMF.mem_support_pure_iff] at hq₁'
    subst hq₁'
    refine ⟨q₂, Or.inl ⟨rfl, System.weakLSilent_refl _ q₂⟩,
      hInv', ?_, ?_, hR.F_eq, hR.val_cert, hR.core_eq, hR.core_cert⟩ <;> dsimp only
    · intro k
      rw [SubState.recvMsg_proc]
      exact hR.call_eq k
    · intro k
      rw [SubState.recvMsg_proc]
      exact hR.ret_eq k
  | echo j A hin happ hcard hsend =>
    rw [PMF.mem_support_pure_iff] at hq₁'
    subst hq₁'
    refine ⟨q₂, Or.inl ⟨rfl, System.weakLSilent_refl _ q₂⟩,
      hInv', ?_, ?_, hR.F_eq, hR.val_cert, hR.core_eq, hR.core_cert⟩ <;> dsimp only
    · intro k
      by_cases hk : k = j
      · subst hk
        rw [SubState.mcast_proc, SubState.setProc_proc_self]
        exact hR.call_eq k
      · rw [SubState.mcast_proc, SubState.setProc_proc_ne _ _ _ hk]
        exact hR.call_eq k
    · intro k
      by_cases hk : k = j
      · subst hk
        rw [SubState.mcast_proc, SubState.setProc_proc_self]
        exact hR.ret_eq k
      · rw [SubState.mcast_proc, SubState.setProc_proc_ne _ _ _ hk]
        exact hR.ret_eq k
  | vote j U hin happ hQ hsend =>
    rw [PMF.mem_support_pure_iff] at hq₁'
    subst hq₁'
    refine ⟨q₂, Or.inl ⟨rfl, System.weakLSilent_refl _ q₂⟩,
      hInv', ?_, ?_, hR.F_eq, hR.val_cert, hR.core_eq, hR.core_cert⟩ <;> dsimp only
    · intro k
      by_cases hk : k = j
      · subst hk
        rw [SubState.mcast_proc, SubState.setProc_proc_self]
        exact hR.call_eq k
      · rw [SubState.mcast_proc, SubState.setProc_proc_ne _ _ _ hk]
        exact hR.call_eq k
    · intro k
      by_cases hk : k = j
      · subst hk
        rw [SubState.mcast_proc, SubState.setProc_proc_self]
        exact hR.ret_eq k
      · rw [SubState.mcast_proc, SubState.setProc_proc_ne _ _ _ hk]
        exact hR.ret_eq k
  | bindCall j U hin hb happ hQ =>
    rw [PMF.mem_support_pure_iff] at hq₁'
    subst hq₁'
    refine ⟨q₂, Or.inl ⟨rfl, System.weakLSilent_refl _ q₂⟩,
      hInv', hR.call_eq, hR.ret_eq, hR.F_eq, hR.val_cert, hR.core_eq, ?_⟩
    intro C hC
    exact le_trans (hR.core_cert C hC) (Finset.card_le_card
      (bindAbove_mono (IdealStep.bindCall _ j U hin hb happ hQ)
        (by rw [PMF.mem_support_pure_iff]) C))
  | byz j m hmem =>
    rw [PMF.mem_support_pure_iff] at hq₁'
    subst hq₁'
    exact ⟨q₂, Or.inl ⟨rfl, System.weakLSilent_refl _ q₂⟩,
      hInv', hR.call_eq, hR.ret_eq, hR.F_eq, hR.val_cert, hR.core_eq, hR.core_cert⟩
  | ret id g hin hsub hQ hr =>
    rw [PMF.mem_support_pure_iff] at hq₁'
    subst hq₁'
    obtain ⟨ts, hchain, hcore, hmem, hcov, hret1, hRel⟩ :=
      retRun hR hin hsub hQ hr
    have hretstep : Step P (ts.getLastD q₂)
        (Lab.ret id g (q₁.core.getD (coreOf P q₁.ga)))
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

/-- info: 'PLTS.ABA.Gather.gatherCore' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms gatherCore

end Gather
end ABA
end PLTS
