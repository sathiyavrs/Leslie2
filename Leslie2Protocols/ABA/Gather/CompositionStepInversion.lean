/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sathiya / Claude
-/

import Leslie2Protocols.ABA.Gather.SpecificationOverInstanceAlphabet
import Leslie2Protocols.Framework.SynchronisedProduct
import Leslie2Protocols.Framework.SynchronisedProductAlongPullbacks

/-!
# The transitions of the gather composition, read off their labels

The composition is `relabel ∘ abstract ∘ parallel` over three synchronised products. The
lemmas here unfold that pipeline in both directions.

`instanceOverBroadcasts_step_iff` splits a transition of the instance into a hidden gather
event and an interface label. Over the instance-internal alphabet, a visible label moves all
four factors — the gather programs, the gather network, the input instances and the bind
instances — and the joint distribution is their Dirac product. A silent label moves exactly
one of the gather network, one input instance or one bind instance.
`instanceOverBroadcastsExtended_joint_inversion` and
`instanceOverBroadcastsExtended_tau_inversion` read a joint step that way, and the `_step`
lemmas build one from the factors' rows. The pullbacks `inputBroadcastLabelMap` and
`bindBroadcastLabelMap` are computed label by label.

`programStep_*` reads one gather program's row off its label: the participant's row as its
guards together with the Dirac it produces, and the idle row of a non-participant as the
identity. `networkStep_*` does the same for the gather network.

A joint step delivers a program function given pointwise, by its value at the acting process
and its agreement with the old function elsewhere. `programFunction_update` identifies that
function with the old one updated at the acting process, and the `stateOverBroadcasts_*`
lemmas identify the state a row writes with `setGatherTier`, `setCore`, `setInputBroadcasts`,
`setBindBroadcasts` or `corruptAll` applied to the old state.
-/

namespace PLTS
namespace ABA
namespace Gather

variable {X : Type}

/-! ### Reading and building instance transitions

The pipeline is `relabel ∘ abstract ∘ parallel ∘ (synchronisedProduct, synchronisedProduct,
synchronisedProduct)`; the lemmas below unfold it once and for all, in both
directions. -/

/-- The instance's step relation, unfolded to the hidden-event case and the
interface-label case. -/
theorem instanceOverBroadcasts_step_iff (P : Parameters) (X : Type) [DecidableEq X] {B B' : Type}
    (BIn : ∀ _ : Fin P.n, System B (BRB.InstanceLabel P.n X))
    (BBind : ∀ _ : Fin P.n, System B' (BRB.InstanceLabel P.n (AcceptedPairs P.n X)))
    (s : StateOverBroadcasts P.n X B B') (l : InstanceLabel P.n X)
    (μ : PMF (StateOverBroadcasts P.n X B B')) :
    (instanceOverBroadcasts P X BIn BBind).step s l μ ↔
      (l = Sum.inl Label.tau ∧ ∃ e : GatherEvent P.n X,
        (instanceOverBroadcastsExtended P X BIn BBind).step s (Sum.inr e) μ) ∨
      (instanceOverBroadcastsExtended P X BIn BBind).step s (Sum.inl l) μ := by
  constructor
  · rintro (⟨hτ, l', ⟨e, rfl⟩, hstep⟩ | ⟨-, hstep⟩)
    · exact Or.inl ⟨Sum.inl_injective hτ, e, hstep⟩
    · exact Or.inr hstep
  · rintro (⟨rfl, e, hstep⟩ | hstep)
    · exact Or.inl ⟨rfl, _, inr_mem_gatherEvents e, hstep⟩
    · exact Or.inr ⟨inl_notMem_gatherEvents l, hstep⟩

/-! ### The synchronised group of gather programs -/

section GatherPrograms
variable [DecidableEq X] {P : Parameters}
  {u x : ∀ _ : Fin P.n,
    LocalState P.n (ProcessRecord P.n X) (Message P.n X)} {l : GatherLabel P.n X}

/-- A synchronised transition of the gather programs on a visible label: every
program steps, and the joint distribution is Dirac. -/
theorem gatherProgramProduct_inversion
    {μ : PMF (∀ _ : Fin P.n, LocalState P.n (ProcessRecord P.n X) (Message P.n X))}
    (h : (System.synchronisedProduct (gatherProgram P (X := X))).step u l μ) :
    ∃ x : ∀ _ : Fin P.n, LocalState P.n (ProcessRecord P.n X) (Message P.n X), μ = PMF.pure x ∧ ∀ i,
    ProgramStep P i (u i) l (PMF.pure (x i)) := by
  rw [System.synchronisedProduct_step] at h
  rcases h with ⟨-, μ_, hall, rfl⟩ | ⟨rfl, i, μ_i, hstep, -⟩
  · have hx : ∀ i, ∃ p', μ_ i = PMF.pure p' := fun i => programStep_dirac (hall i)
    choose y hy using hx
    refine ⟨y, ?_, fun i => ?_⟩
    · rw [show μ_ = fun i => PMF.pure (y i) from funext hy]
      exact piPMF_pure y
    · rw [← hy i]; exact hall i
  · exact absurd hstep programStep_no_tau

/-- Build a synchronised transition of the gather programs from per-process
Dirac steps. -/
theorem gatherProgramProduct_pure (hl : l ≠ Silent.τ)
    (h : ∀ i, ProgramStep P i (u i) l (PMF.pure (x i))) :
    (System.synchronisedProduct (gatherProgram P (X := X))).step u l (PMF.pure x) := by
  rw [System.synchronisedProduct_step]
  exact Or.inl ⟨hl, fun i => PMF.pure (x i), h, (piPMF_pure x).symm⟩

/-- The gather programs have no silent transition: no program has a `τ` row. -/
theorem gatherProgramProduct_no_tau
    {μ : PMF (∀ _ : Fin P.n, LocalState P.n (ProcessRecord P.n X) (Message P.n X))}
    (h : (System.synchronisedProduct (gatherProgram P (X := X))).step u
      (Silent.τ : GatherLabel P.n X) μ)
    : False := by
  rcases h with ⟨hτ, -⟩ | ⟨-, i, μ_i, hstep, -⟩
  · exact hτ rfl
  · exact programStep_no_tau hstep

end GatherPrograms
/-! ### The two tiers in parallel

A visible label moves all four factors — the programs, the gather network, the
input instances and the bind instances — and the joint distribution is their
Dirac product. A silent label moves exactly one of the gather network, one
input instance or one bind instance. -/

section Factors
variable [DecidableEq X] {P : Parameters} {B B' : Type}
  {BIn : ∀ _ : Fin P.n, System B (BRB.InstanceLabel P.n X)}
  {BBind : ∀ _ : Fin P.n, System B' (BRB.InstanceLabel P.n (AcceptedPairs P.n X))}
  {u x : ∀ _ : Fin P.n, LocalState P.n (ProcessRecord P.n X) (Message P.n X)}
  {w w' : NetworkState P.n X} {a a' : ∀ _ : Fin P.n, B} {b b' : ∀ _ : Fin P.n, B'}
  {L : GatherLabel P.n X}

/-- **The joint inversion.** A visible transition of the two tiers: every
factor steps on the label, and the joint distribution is their Dirac
product. -/
theorem instanceOverBroadcastsExtended_joint_inversion (hIn : ∀ k, (BIn k).IsLTS)
    (hBind : ∀ q, (BBind q).IsLTS) {μ : PMF (StateOverBroadcasts P.n X B B')}
    (hL : L ≠ (Silent.τ : GatherLabel P.n X))
    (h : (instanceOverBroadcastsExtended P X BIn BBind).step ((u, w), (a, b)) L μ) :
    ∃ (x : ∀ _ : Fin P.n,
      LocalState P.n (ProcessRecord P.n X) (Message P.n X)) (w' : NetworkState P.n X) (a' : ∀ _ :
        Fin P.n, B) (b' : ∀ _ : Fin P.n, B'),
      μ = PMF.pure ((x, w'), (a', b')) ∧
      (∀ i, ProgramStep P i (u i) L (PMF.pure (x i))) ∧ NetworkStep P w L (PMF.pure w') ∧
      (∀ k, ((BIn k).mapIdle (inputBroadcastLabelMap P.n X k)).step (a k) L (PMF.pure (a' k))) ∧
      (∀ q, ((BBind q).mapIdle (bindBroadcastLabelMap P.n X q)).step (b q) L (PMF.pure (b' q))) :=
    by
  rw [instanceOverBroadcastsExtended, System.parallel_step] at h
  rcases h with ⟨-, μ₁, μ₂, hga, hbr, rfl⟩ | ⟨hτ, -⟩ | ⟨hτ, -⟩
  · rw [gatherPrograms, System.parallel_step] at hga
    rcases hga with ⟨-, ν₁, ν₂, hs, hn, rfl⟩ | ⟨hτ, -⟩ | ⟨hτ, -⟩
    · obtain ⟨y, rfl, hall⟩ := gatherProgramProduct_inversion hs
      obtain ⟨v, rfl⟩ := networkStep_dirac hn
      rw [System.parallel_step] at hbr
      rcases hbr with ⟨-, ρ₁, ρ₂, hi, hb, rfl⟩ | ⟨hτ, -⟩ | ⟨hτ, -⟩
      · obtain ⟨c, rfl, hic⟩ := System.synchronisedProductMapIdle_inversion hIn hL hi
        obtain ⟨d, rfl, hbd⟩ := System.synchronisedProductMapIdle_inversion hBind hL hb
        exact ⟨y, v, c, d, by rw [prodPMF_pure_pure, prodPMF_pure_pure, prodPMF_pure_pure],
          hall, hn, hic, hbd⟩
      · exact absurd hτ hL
      · exact absurd hτ hL
    · exact absurd hτ hL
    · exact absurd hτ hL
  · exact absurd hτ hL
  · exact absurd hτ hL

/-- **The silent inversion.** A silent transition of the two tiers is an
injection of the gather network, a silent step of one input instance, or a
silent step of one bind instance: no gather program has a `τ` row. -/
theorem instanceOverBroadcastsExtended_tau_inversion (hIn : ∀ k, (BIn k).IsLTS)
    (hBind : ∀ q, (BBind q).IsLTS) {μ : PMF (StateOverBroadcasts P.n X B B')}
    (h : (instanceOverBroadcastsExtended P X BIn BBind).step ((u, w), (a, b))
      (Silent.τ : GatherLabel P.n X) μ) :
    (∃ v, μ = PMF.pure ((u, v), (a, b)) ∧
      NetworkStep P w (Silent.τ : GatherLabel P.n X) (PMF.pure v)) ∨
    (∃ (k : Fin P.n) (c : B), μ = PMF.pure ((u, w), (Function.update a k c, b)) ∧
      (BIn k).step (a k) (Silent.τ : BRB.InstanceLabel P.n X) (PMF.pure c)) ∨
    (∃ (q : Fin P.n) (d : B'), μ = PMF.pure ((u, w), (a, Function.update b q d)) ∧
      (BBind q).step (b q) (Silent.τ : BRB.InstanceLabel P.n (AcceptedPairs P.n X)) (PMF.pure d)) :=
        by
  rw [instanceOverBroadcastsExtended, System.parallel_step] at h
  rcases h with ⟨hτ, -⟩ | ⟨-, μ₁, hga, rfl⟩ | ⟨-, μ₂, hbr, rfl⟩
  · exact absurd rfl hτ
  · rw [gatherPrograms, System.parallel_step] at hga
    rcases hga with ⟨hτ, -⟩ | ⟨-, ν₁, hs, rfl⟩ | ⟨-, ν₂, hn, rfl⟩
    · exact absurd rfl hτ
    · exact absurd hs gatherProgramProduct_no_tau
    · obtain ⟨v, rfl⟩ := networkStep_dirac hn
      exact Or.inl ⟨v, by rw [prodPMF_pure_pure, prodPMF_pure_pure], hn⟩
  · rw [System.parallel_step] at hbr
    rcases hbr with ⟨hτ, -⟩ | ⟨-, ρ₁, hi, rfl⟩ | ⟨-, ρ₂, hb, rfl⟩
    · exact absurd rfl hτ
    · obtain ⟨k, c, rfl, hstep⟩ :=
        System.synchronisedProductMapIdle_tau_inversion hIn
          (fun k => inputBroadcastLabelMap_tau P.n X k) hi
      exact Or.inr
        (Or.inl ⟨k, c, by rw [prodPMF_pure_pure, prodPMF_pure_pure], hstep⟩)
    · obtain ⟨q, d, rfl, hstep⟩ :=
        System.synchronisedProductMapIdle_tau_inversion hBind
          (fun q => bindBroadcastLabelMap_tau P.n X q) hb
      exact Or.inr
        (Or.inr ⟨q, d, by rw [prodPMF_pure_pure, prodPMF_pure_pure], hstep⟩)

/-- Build a visible transition of the two tiers from the four factors' Dirac
steps. -/
theorem instanceOverBroadcastsExtended_label_step (hL : L ≠ (Silent.τ : GatherLabel P.n X))
    (hproc : ∀ i, ProgramStep P i (u i) L (PMF.pure (x i))) (hnet : NetworkStep P w L (PMF.pure w'))
    (hin : ∀ k, ((BIn k).mapIdle (inputBroadcastLabelMap P.n X k)).step (a k) L (PMF.pure (a' k)))
    (hbind : ∀ q, ((BBind q).mapIdle (bindBroadcastLabelMap P.n X q)).step (b q) L
      (PMF.pure (b' q)))
    :
    (instanceOverBroadcastsExtended P X BIn BBind).step ((u, w), (a, b)) L
    (PMF.pure ((x, w'), (a', b'))) := by
  rw [instanceOverBroadcastsExtended, System.parallel_step]
  refine Or.inl ⟨hL, PMF.pure (x, w'), PMF.pure (a', b'), ?_, ?_,
    (prodPMF_pure_pure _ _).symm⟩
  · rw [gatherPrograms, System.parallel_step]
    exact Or.inl ⟨hL, PMF.pure x, PMF.pure w', gatherProgramProduct_pure hL hproc, hnet,
      (prodPMF_pure_pure _ _).symm⟩
  · rw [System.parallel_step]
    exact Or.inl ⟨hL, PMF.pure a', PMF.pure b', System.synchronisedProductMapIdle_pure hL hin,
      System.synchronisedProductMapIdle_pure hL hbind, (prodPMF_pure_pure _ _).symm⟩

/-- Build a silent transition of the two tiers from an injection of the gather
network. -/
theorem instanceOverBroadcastsExtended_tau_network
    (hn : NetworkStep P w (Silent.τ : GatherLabel P.n X) (PMF.pure w')) :
    (instanceOverBroadcastsExtended P X BIn BBind).step ((u, w), (a, b))
    (Silent.τ : GatherLabel P.n X) (PMF.pure ((u, w'), (a, b))) := by
  rw [instanceOverBroadcastsExtended, System.parallel_step]
  refine Or.inr (Or.inl ⟨rfl, PMF.pure (u, w'), ?_, (prodPMF_pure_pure _ _).symm⟩)
  rw [gatherPrograms, System.parallel_step]
  exact Or.inr (Or.inr ⟨rfl, PMF.pure w', hn, (prodPMF_pure_pure _ _).symm⟩)

/-- Build a silent transition of the two tiers from a silent step of one input
instance. -/
theorem instanceOverBroadcastsExtended_tau_input {k : Fin P.n} {c : B}
    (h : (BIn k).step (a k) (Silent.τ : BRB.InstanceLabel P.n X) (PMF.pure c)) :
    (instanceOverBroadcastsExtended P X BIn BBind).step ((u, w), (a, b))
    (Silent.τ : GatherLabel P.n X) (PMF.pure ((u, w), (Function.update a k c, b))) := by
  rw [instanceOverBroadcastsExtended, System.parallel_step]
  refine Or.inr (Or.inr ⟨rfl, PMF.pure (Function.update a k c, b), ?_,
    (prodPMF_pure_pure _ _).symm⟩)
  rw [System.parallel_step]
  exact Or.inr (Or.inl ⟨rfl, PMF.pure (Function.update a k c),
    System.synchronisedProductMapIdle_tau_step (inputBroadcastLabelMap_tau P.n X k) h,
      (prodPMF_pure_pure _ _).symm⟩)

/-- Build a silent transition of the two tiers from a silent step of one bind
instance. -/
theorem instanceOverBroadcastsExtended_tau_bind {q : Fin P.n} {d : B'}
    (h : (BBind q).step (b q) (Silent.τ : BRB.InstanceLabel P.n (AcceptedPairs P.n X)) (PMF.pure d))
    :
    (instanceOverBroadcastsExtended P X BIn BBind).step ((u, w), (a, b))
    (Silent.τ : GatherLabel P.n X) (PMF.pure ((u, w), (a, Function.update b q d))) := by
  rw [instanceOverBroadcastsExtended, System.parallel_step]
  refine Or.inr (Or.inr ⟨rfl, PMF.pure (a, Function.update b q d), ?_,
    (prodPMF_pure_pure _ _).symm⟩)
  rw [System.parallel_step]
  exact Or.inr (Or.inr ⟨rfl, PMF.pure (Function.update b q d),
    System.synchronisedProductMapIdle_tau_step (bindBroadcastLabelMap_tau P.n X q) h,
      (prodPMF_pure_pure _ _).symm⟩)

/-- A hidden event is a silent transition of the instance. -/
theorem instanceOverBroadcasts_event_step (e : GatherEvent P.n X)
    (hproc : ∀ i, ProgramStep P i (u i) (Sum.inr e) (PMF.pure (x i)))
    (hnet : NetworkStep P w (Sum.inr e) (PMF.pure w'))
    (hin : ∀ k,
      ((BIn k).mapIdle (inputBroadcastLabelMap P.n X k)).step (a k) (Sum.inr e) (PMF.pure (a' k)))
    (hbind : ∀ q, ((BBind q).mapIdle (bindBroadcastLabelMap P.n X q)).step (b q) (Sum.inr e)
      (PMF.pure (b' q))) :
    (instanceOverBroadcasts P X BIn BBind).step ((u, w), (a, b)) (Sum.inl Label.tau)
      (PMF.pure ((x, w'), (a', b'))) :=
  (instanceOverBroadcasts_step_iff P X BIn BBind _ _ _).mpr
    (Or.inl ⟨rfl, e, instanceOverBroadcastsExtended_label_step (by simp) hproc hnet hin hbind⟩)

/-- A visible interface label is a transition of the instance. -/
theorem instanceOverBroadcasts_label_step {l : InstanceLabel P.n X} (hl : l ≠ Sum.inl Label.tau)
    (hproc : ∀ i, ProgramStep P i (u i) (Sum.inl l) (PMF.pure (x i)))
    (hnet : NetworkStep P w (Sum.inl l) (PMF.pure w'))
    (hin : ∀ k, ((BIn k).mapIdle (inputBroadcastLabelMap P.n X k)).step (a k) (Sum.inl l)
      (PMF.pure (a' k)))
    (hbind : ∀ q, ((BBind q).mapIdle (bindBroadcastLabelMap P.n X q)).step (b q) (Sum.inl l)
      (PMF.pure (b' q)))
    :
    (instanceOverBroadcasts P X BIn BBind).step ((u, w), (a, b)) l (PMF.pure ((x, w'), (a', b'))) :=
    by
  refine (instanceOverBroadcasts_step_iff P X BIn BBind _ _ _).mpr (Or.inr
    (instanceOverBroadcastsExtended_label_step ?_ hproc hnet hin hbind))
  rw [gatherLabel_tau]
  simpa using hl

/-- An injection of the gather network is a silent transition of the
instance. -/
theorem instanceOverBroadcasts_tau_network
    (hn : NetworkStep P w (Silent.τ : GatherLabel P.n X) (PMF.pure w')) :
    (instanceOverBroadcasts P X BIn BBind).step ((u, w), (a, b)) (Sum.inl Label.tau)
    (PMF.pure ((u, w'), (a, b))) :=
  (instanceOverBroadcasts_step_iff P X BIn BBind _ _ _).mpr (Or.inr
    (instanceOverBroadcastsExtended_tau_network hn))

/-- A silent step of one input instance is a silent transition of the
instance. -/
theorem instanceOverBroadcasts_tau_input {k : Fin P.n} {c : B}
    (h : (BIn k).step (a k) (Silent.τ : BRB.InstanceLabel P.n X) (PMF.pure c)) :
    (instanceOverBroadcasts P X BIn BBind).step ((u, w), (a, b)) (Sum.inl Label.tau)
      (PMF.pure ((u, w), (Function.update a k c, b))) :=
  (instanceOverBroadcasts_step_iff P X BIn BBind _ _ _).mpr (Or.inr
    (instanceOverBroadcastsExtended_tau_input h))

/-- A silent step of one bind instance is a silent transition of the
instance. -/
theorem instanceOverBroadcasts_tau_bind {q : Fin P.n} {d : B'}
    (h : (BBind q).step (b q) (Silent.τ : BRB.InstanceLabel P.n (AcceptedPairs P.n X)) (PMF.pure d))
      :
    (instanceOverBroadcasts P X BIn BBind).step ((u, w), (a, b)) (Sum.inl Label.tau)
      (PMF.pure ((u, w), (a, Function.update b q d))) :=
  (instanceOverBroadcasts_step_iff P X BIn BBind _ _ _).mpr (Or.inr
    (instanceOverBroadcastsExtended_tau_bind h))

end Factors
/-! ### The pullbacks, label by label -/

section Pullbacks
variable {n : ℕ} (X : Type) (k q id j q' k' i : Fin n)

@[simp] theorem inputBroadcastLabelMap_call (x : X) :
    inputBroadcastLabelMap n X k (Sum.inl (Sum.inl (.call id x))) =
      if k = id then some (Sum.inl (.call x)) else none := rfl
@[simp] theorem inputBroadcastLabelMap_fail :
    inputBroadcastLabelMap n X k (Sum.inl (Sum.inl (Label.fail (X := X) id))) = some (Sum.inl (.fail
      id)) := rfl
@[simp] theorem inputBroadcastLabelMap_ret (g : Fin n → Option X) (C : AcceptedPairs n X) :
    inputBroadcastLabelMap n X k (Sum.inl (Sum.inl (.ret id g C))) = none := rfl
@[simp] theorem inputBroadcastLabelMap_callLoop (x : X) :
    inputBroadcastLabelMap n X k (Sum.inl (Sum.inr (.callLoop id x))) =
      if k = id then some (Sum.inr (.callLoop x)) else none := rfl
@[simp] theorem inputBroadcastLabelMap_send (m : Message n X) :
    inputBroadcastLabelMap n X k (Sum.inr (.send j m)) = none := rfl
@[simp] theorem inputBroadcastLabelMap_deliver (m : Message n X) :
    inputBroadcastLabelMap n X k (Sum.inr (.deliver i j m)) = none := rfl
@[simp] theorem inputBroadcastLabelMap_inputBroadcastRet (v : X) :
    inputBroadcastLabelMap n X k (Sum.inr (.inputBroadcastRet k' j v)) =
      if k = k' then some (Sum.inl (.ret j v)) else none := rfl
@[simp] theorem inputBroadcastLabelMap_bindCall (U : AcceptedPairs n X) :
    inputBroadcastLabelMap n X k (Sum.inr (.bindCall j U)) = none := rfl
@[simp] theorem inputBroadcastLabelMap_bindRet (U : AcceptedPairs n X) :
    inputBroadcastLabelMap n X k (Sum.inr (.bindRet q' j U)) = none := rfl

@[simp] theorem bindBroadcastLabelMap_call (x : X) :
    bindBroadcastLabelMap n X q (Sum.inl (Sum.inl (.call id x))) = none := rfl
@[simp] theorem bindBroadcastLabelMap_fail :
    bindBroadcastLabelMap n X q (Sum.inl (Sum.inl (Label.fail (X := X) id))) = some (Sum.inl (.fail
      id)) := rfl
@[simp] theorem bindBroadcastLabelMap_ret (g : Fin n → Option X) (C : AcceptedPairs n X) :
    bindBroadcastLabelMap n X q (Sum.inl (Sum.inl (.ret id g C))) = none := rfl
@[simp] theorem bindBroadcastLabelMap_callLoop (x : X) :
    bindBroadcastLabelMap n X q (Sum.inl (Sum.inr (.callLoop id x))) = none := rfl
@[simp] theorem bindBroadcastLabelMap_send (m : Message n X) :
    bindBroadcastLabelMap n X q (Sum.inr (.send j m)) = none := rfl
@[simp] theorem bindBroadcastLabelMap_deliver (m : Message n X) :
    bindBroadcastLabelMap n X q (Sum.inr (.deliver i j m)) = none := rfl
@[simp] theorem bindBroadcastLabelMap_inputBroadcastRet (v : X) :
    bindBroadcastLabelMap n X q (Sum.inr (.inputBroadcastRet k' j v)) = none := rfl
@[simp] theorem bindBroadcastLabelMap_bindCall (U : AcceptedPairs n X) :
    bindBroadcastLabelMap n X q (Sum.inr (.bindCall j U)) =
      if q = j then some (Sum.inl (.call U)) else none := rfl
@[simp] theorem bindBroadcastLabelMap_bindRet (U : AcceptedPairs n X) :
    bindBroadcastLabelMap n X q (Sum.inr (.bindRet q' j U)) =
      if q = q' then some (Sum.inl (.ret j U)) else none := rfl

end Pullbacks
/-! ### One gather program's rules, by label class

Each lemma reads a row of the table off its label: the participant's row as its
guards together with the Dirac it produces, and the idle row of a
non-participant as the identity. The state and the distribution are variables,
so `cases` unifies against any state of the program. -/

section ProgramStepInversion
variable [DecidableEq X] {P : Parameters} {j : Fin P.n}
  {p : LocalState P.n (ProcessRecord P.n X) (Message P.n X)}
  {ν : PMF (LocalState P.n (ProcessRecord P.n X) (Message P.n X))}

theorem programStep_call_own {x : X} (h : ProgramStep P j p (Sum.inl (Sum.inl (.call j x))) ν) :
    p.process.input = none ∧ ν = PMF.pure (p.setProcess { p.process with input := some x }) := by
  cases h
  case call => exact ⟨by assumption, rfl⟩
  case callIdle => exact absurd rfl ‹_ ≠ j›

theorem programStep_call_foreign {i : Fin P.n} {x : X} (hi : i ≠ j)
    (h : ProgramStep P j p (Sum.inl (Sum.inl (.call i x))) ν) : ν = PMF.pure p := by
  cases h
  case call => exact absurd rfl hi
  case callIdle => rfl

theorem programStep_callLoop {i : Fin P.n} {x : X}
    (h : ProgramStep P j p (Sum.inl (Sum.inr (.callLoop i x))) ν) : ν = PMF.pure p := by
  cases h
  case callLoop => rfl
  case callLoopIdle => rfl

theorem programStep_ret_own {g : Fin P.n → Option X} {C : AcceptedPairs P.n X}
    (h : ProgramStep P j p (Sum.inl (Sum.inl (.ret j g C))) ν) :
    p.process.input ≠ none ∧ p.process.sentBind ≠ none ∧
      (∀ k x, g k = some x → holdsInputBroadcastReturn p.process k x) ∧
      (∃ Q : Finset (Fin P.n), P.n - P.f ≤ Q.card ∧
        ∀ q ∈ Q, ∃ U, holdsBindBroadcastReturn p.process q U ∧ AcceptedPairs.subMap U g) ∧
      p.process.returned = false ∧ ν = PMF.pure
        (p.setProcess { p.process with returned := true }) := by
  cases h
  case ret =>
    exact ⟨by assumption, by assumption, by assumption, by assumption, by assumption, rfl⟩
  case retIdle => exact absurd rfl ‹_ ≠ j›

theorem programStep_ret_foreign {i : Fin P.n} {g : Fin P.n → Option X} {C : AcceptedPairs P.n X}
    (hi : i ≠ j) (h : ProgramStep P j p (Sum.inl (Sum.inl (.ret i g C))) ν) : ν = PMF.pure p := by
  cases h
  case ret => exact absurd rfl hi
  case retIdle => rfl

theorem programStep_fail {i : Fin P.n} (h : ProgramStep P j p (Sum.inl (Sum.inl (.fail i))) ν) :
    ν = PMF.pure p := by
  cases h
  case failIdle => rfl

theorem programStep_send_echo_own {A : AcceptedPairs P.n X}
    (h : ProgramStep P j p (Sum.inr (.send j (.echo A))) ν) :
    A = p.process.accepted ∧ p.process.input ≠ none ∧ P.n - P.f ≤ p.process.accepted.card ∧
      p.process.sentEcho = none ∧
      ν = PMF.pure (p.setProcess { p.process with sentEcho := some p.process.accepted }) := by
  cases h
  case sendEcho => exact ⟨rfl, by assumption, by assumption, by assumption, rfl⟩
  case sendIdle => exact absurd rfl ‹_ ≠ j›

theorem programStep_send_vote_own {U : AcceptedPairs P.n X}
    (h : ProgramStep P j p (Sum.inr (.send j (.vote U))) ν) :
    p.process.input ≠ none ∧ p.process.sentEcho ≠ none ∧ approvedBy p.process U ∧
      (∃ Q : Finset (Fin P.n), P.n - P.f ≤ Q.card ∧
        ∀ q ∈ Q, ∃ A, Message.echo A ∈ p.received q ∧ approvedBy p.process A ∧ A ⊆ U) ∧
      p.process.sentVote = none ∧ ν = PMF.pure
        (p.setProcess { p.process with sentVote := some U }) := by
  cases h
  case sendVote =>
    exact ⟨by assumption, by assumption, by assumption, by assumption, by assumption, rfl⟩
  case sendIdle => exact absurd rfl ‹_ ≠ j›

theorem programStep_send_foreign {i : Fin P.n} {m : Message P.n X} (hi : i ≠ j)
    (h : ProgramStep P j p (Sum.inr (.send i m)) ν) : ν = PMF.pure p := by
  cases h
  case sendIdle => rfl
  all_goals exact absurd rfl hi

theorem programStep_deliver_own {k : Fin P.n} {m : Message P.n X}
    (h : ProgramStep P j p (Sum.inr (.deliver j k m)) ν) : ν = PMF.pure (p.deliverTo k m) := by
  cases h
  case deliverReceive => rfl
  case deliverIdle => exact absurd rfl ‹_ ≠ j›

theorem programStep_deliver_foreign {i k : Fin P.n} {m : Message P.n X} (hi : i ≠ j)
    (h : ProgramStep P j p (Sum.inr (.deliver i k m)) ν) : ν = PMF.pure p := by
  cases h
  case deliverReceive => exact absurd rfl hi
  case deliverIdle => rfl

theorem programStep_inputBroadcastRet_own {k : Fin P.n} {v : X}
    (h : ProgramStep P j p (Sum.inr (.inputBroadcastRet k j v)) ν) :
    ν = PMF.pure (p.setProcess { p.process with
      inputBroadcastReturned :=
        Function.update p.process.inputBroadcastReturned k (some v) }) := by
  cases h
  case inputBroadcastRetReceive => rfl
  case inputBroadcastRetIdle => exact absurd rfl ‹_ ≠ j›

theorem programStep_inputBroadcastRet_foreign {k i : Fin P.n} {v : X} (hi : i ≠ j)
    (h : ProgramStep P j p (Sum.inr (.inputBroadcastRet k i v)) ν) : ν = PMF.pure p := by
  cases h
  case inputBroadcastRetReceive => exact absurd rfl hi
  case inputBroadcastRetIdle => rfl

theorem programStep_bindCall_own {U : AcceptedPairs P.n X}
    (h : ProgramStep P j p (Sum.inr (.bindCall j U)) ν) :
    p.process.input ≠ none ∧ p.process.sentVote ≠ none ∧ p.process.sentBind = none ∧
      approvedBy p.process U ∧
      (∃ Q : Finset (Fin P.n), P.n - P.f ≤ Q.card ∧
        ∀ q ∈ Q, ∃ W, Message.vote W ∈ p.received q ∧ approvedBy p.process W ∧ W ⊆ U) ∧
      ν = PMF.pure (p.setProcess { p.process with sentBind := some U }) := by
  cases h
  case bindCall =>
    exact ⟨by assumption, by assumption, by assumption, by assumption, by assumption, rfl⟩
  case bindCallIdle => exact absurd rfl ‹_ ≠ j›

theorem programStep_bindCall_foreign {i : Fin P.n} {U : AcceptedPairs P.n X} (hi : i ≠ j)
    (h : ProgramStep P j p (Sum.inr (.bindCall i U)) ν) : ν = PMF.pure p := by
  cases h
  case bindCall => exact absurd rfl hi
  case bindCallIdle => rfl

theorem programStep_bindRet_own {q : Fin P.n} {U : AcceptedPairs P.n X}
    (h : ProgramStep P j p (Sum.inr (.bindRet q j U)) ν) :
    ν = PMF.pure
      (p.setProcess { p.process with
        bindBroadcastReturned :=
          Function.update p.process.bindBroadcastReturned q (some U) }) := by
  cases h
  case bindRetReceive => rfl
  case bindRetIdle => exact absurd rfl ‹_ ≠ j›

theorem programStep_bindRet_foreign {q i : Fin P.n} {U : AcceptedPairs P.n X} (hi : i ≠ j)
    (h : ProgramStep P j p (Sum.inr (.bindRet q i U)) ν) : ν = PMF.pure p := by
  cases h
  case bindRetReceive => exact absurd rfl hi
  case bindRetIdle => rfl

end ProgramStepInversion
/-! ### The gather network's rules, by label class -/

section NetworkStepInversion
variable [DecidableEq X] {P : Parameters} {w : NetworkState P.n X} {μ : PMF (NetworkState P.n X)}

theorem networkStep_call {id : Fin P.n} {x : X}
    (h : NetworkStep P w (Sum.inl (Sum.inl (.call id x))) μ) : μ = PMF.pure w := by
  cases h; rfl

theorem networkStep_callLoop {id : Fin P.n} {x : X}
    (h : NetworkStep P w (Sum.inl (Sum.inr (.callLoop id x))) μ) : μ = PMF.pure w := by
  cases h; rfl

theorem networkStep_ret {id : Fin P.n} {g : Fin P.n → Option X} {C : AcceptedPairs P.n X}
    (h : NetworkStep P w (Sum.inl (Sum.inl (.ret id g C))) μ) :
    C = w.core.getD (coreOfNetwork P w.network) ∧ μ = PMF.pure { w with core := some C } := by
  cases h; exact ⟨rfl, rfl⟩

theorem networkStep_fail {i : Fin P.n} (h : NetworkStep P w (Sum.inl (Sum.inl (.fail i))) μ) :
    μ = PMF.pure { w with network := w.network.corrupt P i } := by
  cases h; rfl

theorem networkStep_send {j : Fin P.n} {m : Message P.n X}
    (h : NetworkStep P w (Sum.inr (.send j m)) μ) :
    μ = PMF.pure { w with network := w.network.recordSent j m } := by
  cases h; rfl

theorem networkStep_deliver {i j : Fin P.n} {m : Message P.n X}
    (h : NetworkStep P w (Sum.inr (.deliver i j m)) μ) : m ∈ w.network.sent j ∧ μ = PMF.pure w := by
  cases h; exact ⟨by assumption, rfl⟩

theorem networkStep_inputBroadcastRet {k j : Fin P.n} {v : X}
    (h : NetworkStep P w (Sum.inr (.inputBroadcastRet k j v)) μ) : μ = PMF.pure w := by
  cases h; rfl

theorem networkStep_bindCall {j : Fin P.n} {U : AcceptedPairs P.n X}
    (h : NetworkStep P w (Sum.inr (.bindCall j U)) μ) : μ = PMF.pure w := by
  cases h; rfl

theorem networkStep_bindRet {q j : Fin P.n} {U : AcceptedPairs P.n X}
    (h : NetworkStep P w (Sum.inr (.bindRet q j U)) μ) : μ = PMF.pure w := by
  cases h; rfl

theorem networkStep_tau (h : NetworkStep P w (Sum.inl (Sum.inl .tau)) μ) :
    ∃ (j : Fin P.n) (m : Message P.n X), j ∈ w.network.F ∧
      μ = PMF.pure { w with network := w.network.recordSent j m } := by
  cases h
  case byzantine j m hF => exact ⟨j, m, hF, rfl⟩

end NetworkStepInversion
/-- A function fixed at `i` and unchanged elsewhere is the old one updated at
`i`. -/
theorem funUpdate {ι β : Type} [DecidableEq ι] {f g : ι → β} {i : ι} {y : β}
    (hi : g i = y) (hne : ∀ i', i' ≠ i → g i' = f i') : g = Function.update f i y := by
  funext i'
  by_cases h : i' = i
  · subst h; rw [hi, Function.update_self]
  · rw [hne i' h, Function.update_of_ne h]

/-! ### The write a row makes on the composed state

A joint step delivers a program function pointwise: its value at the acting
process, and its agreement with the old one elsewhere. A row writes with
`setGatherTier` and `InstanceState.setProcess`. The lemmas here identify the
two. -/

section Writes

/-! ### The writes that leave the sent sets alone -/

section

variable {P : Parameters} {B B' : Type}
  {u x : ∀ _ : Fin P.n, LocalState P.n (ProcessRecord P.n X) (Message P.n X)}
  {w : NetworkState P.n X} {a : ∀ _ : Fin P.n, B} {b : ∀ _ : Fin P.n, B'}

/-- A program function fixed at `j` and unchanged elsewhere is the old one
updated at `j`. -/
theorem programFunction_update {j : Fin P.n}
    {r : LocalState P.n (ProcessRecord P.n X) (Message P.n X)} (hj : x j = r)
    (hne : ∀ i, i ≠ j → x i = u i) : x = Function.update u j r := by
  funext i
  by_cases hi : i = j
  · subst hi; rw [hj, Function.update_self]
  · rw [hne i hi, Function.update_of_ne hi]

/-- A record write at one program, with the network state untouched. -/
theorem stateOverBroadcasts_setProcess {j : Fin P.n} {pr : ProcessRecord P.n X}
    (hj : x j = (u j).setProcess pr) (hne : ∀ i, i ≠ j → x i = u i) :
    (((x, w), (a, b)) : StateOverBroadcasts P.n X B B') = setGatherTier ((u, w), (a, b))
    (InstanceState.setProcess (gatherTier ((u, w), (a, b))) j pr) := by
  rw [programFunction_update hj hne]; rfl

/-- The programs remain unchanged and the network state is untouched. -/
theorem stateOverBroadcasts_idle (hall : ∀ i, x i = u i) :
    (((x, w), (a, b)) : StateOverBroadcasts P.n X B B') = ((u, w), (a, b)) := by
  rw [funext hall]

/-- A return: the returner's flag and the instance's core. -/
theorem stateOverBroadcasts_ret {id : Fin P.n} {pr : ProcessRecord P.n X} {C : AcceptedPairs P.n X}
    (hj : x id = (u id).setProcess pr) (hne : ∀ i, i ≠ id → x i = u i) :
    (((x, { w with core := some C }), (a, b)) : StateOverBroadcasts P.n X B B') = setCore
    (setGatherTier ((u, w), (a, b)) (InstanceState.setProcess (gatherTier ((u, w), (a, b))) id pr))
    (some C) := by
  rw [programFunction_update hj hne]; rfl

/-- Corruption is the network state's own write beside the broadcast
coordinates' (D1). -/
theorem stateOverBroadcasts_corrupt {id : Fin P.n} {cIn : B → B} {cBind : B' → B'} (hall : ∀ i,
    x i = u i) : (((x, { w with network := w.network.corrupt P id }),
        ((fun k => cIn (a k)), fun q => cBind (b q))) : StateOverBroadcasts P.n X B B') =
      corruptAll P id cIn cBind ((u, w), (a, b)) := by
  rw [funext hall]; rfl

/-- A write at one input instance. -/
theorem stateOverBroadcasts_setInputBroadcasts {k : Fin P.n} {c : B} :
    (((u, w), (Function.update a k c, b)) : StateOverBroadcasts P.n X B B') =
      setInputBroadcasts ((u, w), (a, b)) (Function.update (inputBroadcasts ((u, w), (a,
        b))) k c) := rfl

/-- A write at one bind instance. -/
theorem stateOverBroadcasts_setBindBroadcasts {q : Fin P.n} {d : B'} :
    (((u, w), (a, Function.update b q d)) : StateOverBroadcasts P.n X B B') =
      setBindBroadcasts ((u, w), (a, b)) (Function.update (bindBroadcasts ((u, w), (a,
        b))) q d) := rfl

end

/-! ### The writes that record or deliver a message, and the program group's row -/

section

variable [DecidableEq X] {P : Parameters} {B B' : Type}
  {u x : ∀ _ : Fin P.n, LocalState P.n (ProcessRecord P.n X) (Message P.n X)}
  {w : NetworkState P.n X} {a : ∀ _ : Fin P.n, B} {b : ∀ _ : Fin P.n, B'}

/-- The participant's row beside the idle rows of every other program is the
program group stepping into the updated function. -/
theorem programStep_update {j : Fin P.n} {r : LocalState P.n (ProcessRecord P.n X) (Message P.n X)}
    {l : GatherLabel P.n X} (hj : ProgramStep P j (u j) l (PMF.pure r))
    (hne : ∀ i, i ≠ j → ProgramStep P i (u i) l (PMF.pure (u i))) :
    ∀ i, ProgramStep P i (u i) l (PMF.pure (Function.update u j r i)) := by
  intro i
  by_cases hi : i = j
  · subst hi; rw [Function.update_self]; exact hj
  · rw [Function.update_of_ne hi]; exact hne i hi

/-- A record write at one program together with the network state recording the
message that write multicasts. -/
theorem stateOverBroadcasts_setProcess_recordSent {j : Fin P.n} {pr : ProcessRecord P.n X}
    {m : Message P.n X} (hj : x j = (u j).setProcess pr) (hne : ∀ i, i ≠ j → x i = u i) :
    (((x, { w with network := w.network.recordSent j m }), (a, b)) : StateOverBroadcasts P.n X B B')
    = setGatherTier ((u, w), (a, b))
    ((InstanceState.setProcess (gatherTier ((u, w), (a, b))) j pr).multicast j m) := by
  rw [programFunction_update hj hne]; rfl

/-- A delivery: the receiver files the message under its sender's row. -/
theorem stateOverBroadcasts_deliver {i k : Fin P.n} {m : Message P.n X}
    (hi : x i = (u i).deliverTo k m) (hne : ∀ i', i' ≠ i → x i' = u i') :
    (((x, w), (a, b)) : StateOverBroadcasts P.n X B B') = setGatherTier ((u, w), (a, b))
    (InstanceState.receiveMessage (gatherTier ((u, w), (a, b))) i k m) := by
  rw [programFunction_update hi hne]; rfl

/-- A Byzantine injection: the network state records a message under a
corrupted sender. -/
theorem stateOverBroadcasts_recordSent {k : Fin P.n} {m : Message P.n X} :
    (((u, { w with network := w.network.recordSent k m }), (a,
      b)) : StateOverBroadcasts P.n X B B') = setGatherTier ((u, w), (a,
        b)) (InstanceState.multicast (gatherTier ((u, w), (a, b))) k m) := rfl

end

end Writes
end Gather
end ABA
end PLTS
