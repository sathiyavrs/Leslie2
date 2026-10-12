/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sathiya / Claude
-/

import Leslie2Protocols.ABA.Gather.SpecificationOverInstanceAlphabet
import Leslie2Protocols.Framework.SynchronisedProduct
import Leslie2Protocols.Framework.SynchronisedProductAlongPullbacks

/-!
# The transitions of the gather composition, determined by their labels

The composition is `relabel ∘ abstract ∘ parallel` over two synchronised products. The
lemmas here unfold that pipeline in both directions.

`instanceOverBroadcasts_step_iff` splits a transition of the instance into a hidden gather
event and an interface label. Over the instance-internal alphabet, a visible label moves all
three factors — the gather programs, the gather network and the input instances — and the
product distribution is their Dirac product. A silent label moves exactly one of the gather
network or one input instance.
`instanceOverBroadcastsExtended_synchronised_cases` and
`instanceOverBroadcastsExtended_tau_cases` read a synchronised step that way, and the `_step`
lemmas build one from the factors' transitions. The pullback `inputBroadcastLabelMap` is
computed label by label.

`programStep_*` determines one gather program's transition from its label: the participant's
transition as its guards together with the Dirac it produces, and the idle transition of a
non-participant as the identity. `networkStep_*` does the same for the gather network.

A synchronised step delivers a program function given pointwise, by its value at the acting process
and its
agreement with the old function elsewhere. `Function.eq_update_iff` identifies that function with
the old one updated at the acting process, and the `stateOverBroadcasts_*` lemmas identify the state
a transition writes with `setGatherProgramsAndNetwork`, `setCore`, `setInputBroadcasts` or
`corruptAll` applied to the old state.
-/

namespace PLTS
namespace ABA
namespace Gather

variable {X : Type}

/-! ### Reading and building instance transitions

The pipeline is `relabel ∘ abstract ∘ parallel ∘ (synchronisedProduct, synchronisedProduct)`;
the lemmas below unfold it once and for all, in both
directions. -/

/-- The instance's step relation, unfolded to the hidden-event case and the
interface-label case. -/
theorem instanceOverBroadcasts_step_iff (P : Parameters) (X : Type) [DecidableEq X] {B : Type}
    (BIn : ∀ _ : Fin P.n, System B (BRB.InstanceLabel P.n X))
    (s : StateOverBroadcasts P.n X B) (l : InstanceLabel P.n X)
    (μ : PMF (StateOverBroadcasts P.n X B)) :
    (instanceOverBroadcasts P X BIn).step s l μ ↔
      (l = Sum.inl Label.tau ∧ ∃ e : GatherEvent P.n X,
        (instanceOverBroadcastsExtended P X BIn).step s (Sum.inr e) μ) ∨
      (instanceOverBroadcastsExtended P X BIn).step s (Sum.inl l) μ := by
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
    LocalState P.n (ProcessVariables P.n X) (Message P.n X)} {l : GatherLabel P.n X}

/-- A synchronised transition of the gather programs on a visible label: every
program steps, and the product distribution is Dirac. -/
theorem gatherProgramProduct_cases
    {μ : PMF (∀ _ : Fin P.n, LocalState P.n (ProcessVariables P.n X) (Message P.n X))}
    (h : (System.synchronisedProduct (gatherProgram P (X := X))).step u l μ) :
    ∃ x : ∀ _ : Fin P.n, LocalState P.n (ProcessVariables P.n X) (Message P.n X), μ = PMF.pure x ∧ ∀
      i,
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

/-- The gather programs have no silent transition: no program has a `τ` transition. -/
theorem gatherProgramProduct_no_tau
    {μ : PMF (∀ _ : Fin P.n, LocalState P.n (ProcessVariables P.n X) (Message P.n X))}
    (h : (System.synchronisedProduct (gatherProgram P (X := X))).step u
      (Silent.τ : GatherLabel P.n X) μ)
    : False := by
  rcases h with ⟨hτ, -⟩ | ⟨-, i, μ_i, hstep, -⟩
  · exact hτ rfl
  · exact programStep_no_tau hstep

end GatherPrograms
/-! ### The gather and the input instances in parallel

A visible label moves all three factors — the programs, the gather network and
the input instances — and the product distribution is their Dirac product. A
silent label moves exactly one of the gather network or one input instance. -/

section Factors
variable [DecidableEq X] {P : Parameters} {B : Type}
  {BIn : ∀ _ : Fin P.n, System B (BRB.InstanceLabel P.n X)}
  {u x : ∀ _ : Fin P.n, LocalState P.n (ProcessVariables P.n X) (Message P.n X)}
  {w w' : NetworkState P.n X} {a a' : ∀ _ : Fin P.n, B}
  {L : GatherLabel P.n X}

/-- **The synchronised cases.** A visible transition of the gather beside the input instances:
every factor steps on the label, and the product distribution is their Dirac
product. -/
theorem instanceOverBroadcastsExtended_synchronised_cases (hIn : ∀ k, (BIn k).IsLTS)
    {μ : PMF (StateOverBroadcasts P.n X B)}
    (hL : L ≠ (Silent.τ : GatherLabel P.n X))
    (h : (instanceOverBroadcastsExtended P X BIn).step ((u, w), a) L μ) :
    ∃ (x : ∀ _ : Fin P.n,
      LocalState P.n (ProcessVariables P.n X) (Message P.n X)) (w' : NetworkState P.n X)
      (a' : ∀ _ : Fin P.n, B),
      μ = PMF.pure ((x, w'), a') ∧
      (∀ i, ProgramStep P i (u i) L (PMF.pure (x i))) ∧ NetworkStep P w L (PMF.pure w') ∧
      (∀ k, ((BIn k).mapIdle (inputBroadcastLabelMap P.n X k)).step (a k) L (PMF.pure (a' k))) := by
  rw [instanceOverBroadcastsExtended, System.parallel_step] at h
  rcases h with ⟨-, μ₁, μ₂, hga, hi, rfl⟩ | ⟨hτ, -⟩ | ⟨hτ, -⟩
  · rw [gatherPrograms, System.parallel_step] at hga
    rcases hga with ⟨-, ν₁, ν₂, hs, hn, rfl⟩ | ⟨hτ, -⟩ | ⟨hτ, -⟩
    · obtain ⟨y, rfl, hall⟩ := gatherProgramProduct_cases hs
      obtain ⟨v, rfl⟩ := networkStep_dirac hn
      obtain ⟨c, rfl, hic⟩ := System.synchronisedProductMapIdle_cases hIn hL hi
      exact ⟨y, v, c, by rw [prodPMF_pure_pure, prodPMF_pure_pure], hall, hn, hic⟩
    · exact absurd hτ hL
    · exact absurd hτ hL
  · exact absurd hτ hL
  · exact absurd hτ hL

/-- **The silent cases.** A silent transition of the gather beside the input instances is an
injection of the gather network or a silent step of one input instance: no gather program has a
`τ` transition. -/
theorem instanceOverBroadcastsExtended_tau_cases (hIn : ∀ k, (BIn k).IsLTS)
    {μ : PMF (StateOverBroadcasts P.n X B)}
    (h : (instanceOverBroadcastsExtended P X BIn).step ((u, w), a)
      (Silent.τ : GatherLabel P.n X) μ) :
    (∃ v, μ = PMF.pure ((u, v), a) ∧
      NetworkStep P w (Silent.τ : GatherLabel P.n X) (PMF.pure v)) ∨
    (∃ (k : Fin P.n) (c : B), μ = PMF.pure ((u, w), Function.update a k c) ∧
      (BIn k).step (a k) (Silent.τ : BRB.InstanceLabel P.n X) (PMF.pure c)) := by
  rw [instanceOverBroadcastsExtended, System.parallel_step] at h
  rcases h with ⟨hτ, -⟩ | ⟨-, μ₁, hga, rfl⟩ | ⟨-, μ₂, hi, rfl⟩
  · exact absurd rfl hτ
  · rw [gatherPrograms, System.parallel_step] at hga
    rcases hga with ⟨hτ, -⟩ | ⟨-, ν₁, hs, rfl⟩ | ⟨-, ν₂, hn, rfl⟩
    · exact absurd rfl hτ
    · exact absurd hs gatherProgramProduct_no_tau
    · obtain ⟨v, rfl⟩ := networkStep_dirac hn
      exact Or.inl ⟨v, by rw [prodPMF_pure_pure, prodPMF_pure_pure], hn⟩
  · obtain ⟨k, c, rfl, hstep⟩ :=
      System.synchronisedProductMapIdle_tau_cases hIn
        (fun k => inputBroadcastLabelMap_tau P.n X k) hi
    exact Or.inr ⟨k, c, by rw [prodPMF_pure_pure], hstep⟩

/-- Build a visible transition of the gather programs and network beside the input instances
from the three factors' Dirac steps. -/
theorem instanceOverBroadcastsExtended_label_step (hL : L ≠ (Silent.τ : GatherLabel P.n X))
    (hproc : ∀ i, ProgramStep P i (u i) L (PMF.pure (x i))) (hnet : NetworkStep P w L (PMF.pure w'))
    (hin : ∀ k, ((BIn k).mapIdle (inputBroadcastLabelMap P.n X k)).step (a k) L (PMF.pure (a' k))) :
    (instanceOverBroadcastsExtended P X BIn).step ((u, w), a) L (PMF.pure ((x, w'), a')) := by
  rw [instanceOverBroadcastsExtended, System.parallel_step]
  refine Or.inl ⟨hL, PMF.pure (x, w'), PMF.pure a', ?_,
    System.synchronisedProductMapIdle_pure hL hin, (prodPMF_pure_pure _ _).symm⟩
  rw [gatherPrograms, System.parallel_step]
  exact Or.inl ⟨hL, PMF.pure x, PMF.pure w', gatherProgramProduct_pure hL hproc, hnet,
    (prodPMF_pure_pure _ _).symm⟩

/-- Build a silent transition of the gather programs and network beside the input
instances from an injection of the gather network. -/
theorem instanceOverBroadcastsExtended_tau_network
    (hn : NetworkStep P w (Silent.τ : GatherLabel P.n X) (PMF.pure w')) :
    (instanceOverBroadcastsExtended P X BIn).step ((u, w), a)
    (Silent.τ : GatherLabel P.n X) (PMF.pure ((u, w'), a)) := by
  rw [instanceOverBroadcastsExtended, System.parallel_step]
  refine Or.inr (Or.inl ⟨rfl, PMF.pure (u, w'), ?_, (prodPMF_pure_pure _ _).symm⟩)
  rw [gatherPrograms, System.parallel_step]
  exact Or.inr (Or.inr ⟨rfl, PMF.pure w', hn, (prodPMF_pure_pure _ _).symm⟩)

/-- Build a silent transition of the gather programs and network beside the input
instances from a silent step of one input instance. -/
theorem instanceOverBroadcastsExtended_tau_input {k : Fin P.n} {c : B}
    (h : (BIn k).step (a k) (Silent.τ : BRB.InstanceLabel P.n X) (PMF.pure c)) :
    (instanceOverBroadcastsExtended P X BIn).step ((u, w), a)
    (Silent.τ : GatherLabel P.n X) (PMF.pure ((u, w), Function.update a k c)) := by
  rw [instanceOverBroadcastsExtended, System.parallel_step]
  exact Or.inr (Or.inr ⟨rfl, PMF.pure (Function.update a k c),
    System.synchronisedProductMapIdle_tau_step (inputBroadcastLabelMap_tau P.n X k) h,
      (prodPMF_pure_pure _ _).symm⟩)

/-- A hidden event is a silent transition of the instance. -/
theorem instanceOverBroadcasts_event_step (e : GatherEvent P.n X)
    (hproc : ∀ i, ProgramStep P i (u i) (Sum.inr e) (PMF.pure (x i)))
    (hnet : NetworkStep P w (Sum.inr e) (PMF.pure w'))
    (hin : ∀ k,
      ((BIn k).mapIdle (inputBroadcastLabelMap P.n X k)).step (a k) (Sum.inr e) (PMF.pure (a' k))) :
    (instanceOverBroadcasts P X BIn).step ((u, w), a) (Sum.inl Label.tau)
      (PMF.pure ((x, w'), a')) :=
  (instanceOverBroadcasts_step_iff P X BIn _ _ _).mpr
    (Or.inl ⟨rfl, e, instanceOverBroadcastsExtended_label_step (by simp) hproc hnet hin⟩)

/-- A visible interface label is a transition of the instance. -/
theorem instanceOverBroadcasts_label_step {l : InstanceLabel P.n X} (hl : l ≠ Sum.inl Label.tau)
    (hproc : ∀ i, ProgramStep P i (u i) (Sum.inl l) (PMF.pure (x i)))
    (hnet : NetworkStep P w (Sum.inl l) (PMF.pure w'))
    (hin : ∀ k, ((BIn k).mapIdle (inputBroadcastLabelMap P.n X k)).step (a k) (Sum.inl l)
      (PMF.pure (a' k))) :
    (instanceOverBroadcasts P X BIn).step ((u, w), a) l (PMF.pure ((x, w'), a')) := by
  refine (instanceOverBroadcasts_step_iff P X BIn _ _ _).mpr (Or.inr
    (instanceOverBroadcastsExtended_label_step ?_ hproc hnet hin))
  rw [gatherLabel_tau]
  simpa using hl

/-- An injection of the gather network is a silent transition of the
instance. -/
theorem instanceOverBroadcasts_tau_network
    (hn : NetworkStep P w (Silent.τ : GatherLabel P.n X) (PMF.pure w')) :
    (instanceOverBroadcasts P X BIn).step ((u, w), a) (Sum.inl Label.tau)
    (PMF.pure ((u, w'), a)) :=
  (instanceOverBroadcasts_step_iff P X BIn _ _ _).mpr (Or.inr
    (instanceOverBroadcastsExtended_tau_network hn))

/-- A silent step of one input instance is a silent transition of the
instance. -/
theorem instanceOverBroadcasts_tau_input {k : Fin P.n} {c : B}
    (h : (BIn k).step (a k) (Silent.τ : BRB.InstanceLabel P.n X) (PMF.pure c)) :
    (instanceOverBroadcasts P X BIn).step ((u, w), a) (Sum.inl Label.tau)
      (PMF.pure ((u, w), Function.update a k c)) :=
  (instanceOverBroadcasts_step_iff P X BIn _ _ _).mpr (Or.inr
    (instanceOverBroadcastsExtended_tau_input h))

end Factors
/-! ### The pullbacks, label by label -/

section Pullbacks
variable {n : ℕ} (X : Type) (k id j k' i : Fin n)

@[simp] theorem inputBroadcastLabelMap_call (x : X) :
    inputBroadcastLabelMap n X k (Sum.inl (Sum.inl (.call id x))) = none := rfl
@[simp] theorem inputBroadcastLabelMap_fail :
    inputBroadcastLabelMap n X k (Sum.inl (Sum.inl (Label.fail (X := X) id))) = some (Sum.inl (.fail
      id)) := rfl
@[simp] theorem inputBroadcastLabelMap_ret (g : Fin n → Option X) (C : AcceptedPairs n X) :
    inputBroadcastLabelMap n X k (Sum.inl (Sum.inl (.ret id g C))) = none := rfl
@[simp] theorem inputBroadcastLabelMap_callLoop (x : X) :
    inputBroadcastLabelMap n X k (Sum.inl (Sum.inr (.callLoop id x))) = none := rfl
@[simp] theorem inputBroadcastLabelMap_send (m : Message n X) :
    inputBroadcastLabelMap n X k (Sum.inr (.send j m)) = none := rfl
@[simp] theorem inputBroadcastLabelMap_deliver (m : Message n X) :
    inputBroadcastLabelMap n X k (Sum.inr (.deliver i j m)) = none := rfl
@[simp] theorem inputBroadcastLabelMap_inputBroadcastCall (x : X) :
    inputBroadcastLabelMap n X k (Sum.inr (.inputBroadcastCall j x)) =
      if k = j then some (Sum.inl (.call x)) else none := rfl
@[simp] theorem inputBroadcastLabelMap_inputBroadcastRet (v : X) :
    inputBroadcastLabelMap n X k (Sum.inr (.inputBroadcastRet k' j v)) =
      if k = k' then some (Sum.inl (.ret j v)) else none := rfl

end Pullbacks
/-! ### One gather program's transitions, by label class

Each lemma determines a transition of the gather program from its label: the
participant's transition as its guards together with the Dirac it produces, and
the idle transition of a non-participant as the identity. The state and the
distribution are variables, so `cases` unifies against any state of the
program. -/

section ProgramStepCases
variable [DecidableEq X] {P : Parameters} {j : Fin P.n}
  {p : LocalState P.n (ProcessVariables P.n X) (Message P.n X)}
  {ν : PMF (LocalState P.n (ProcessVariables P.n X) (Message P.n X))}

theorem programStep_call_own {x : X} (h : ProgramStep P j p (Sum.inl (Sum.inl (.call j x))) ν) :
    p.processVariables.input = none ∧ ν = PMF.pure (p.setProcessVariables { p.processVariables with
      input := some x }) := by
  cases h
  case call => exact ⟨by assumption, rfl⟩
  case callIdle => exact absurd rfl ‹_ ≠ j›

theorem programStep_call_notOwn {i : Fin P.n} {x : X} (hi : i ≠ j)
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
    p.processVariables.input ≠ none ∧ p.processVariables.sentBind ≠ none ∧
      (∀ k x, g k = some x → holdsInputBroadcastReturn p.processVariables k x) ∧
      (∃ Q : Finset (Fin P.n), P.n - P.f ≤ Q.card ∧
        ∀ q ∈ Q, ∃ U, Message.bind U ∈ p.received q ∧ AcceptedPairs.subMap U g) ∧
      p.processVariables.returned = false ∧ ν = PMF.pure
        (p.setProcessVariables { p.processVariables with returned := true }) := by
  cases h
  case ret =>
    exact ⟨by assumption, by assumption, by assumption, by assumption, by assumption, rfl⟩
  case retIdle => exact absurd rfl ‹_ ≠ j›

theorem programStep_ret_notOwn {i : Fin P.n} {g : Fin P.n → Option X} {C : AcceptedPairs P.n X}
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
    A = p.processVariables.accepted ∧ p.processVariables.input ≠ none ∧ P.n - P.f ≤
      p.processVariables.accepted.card ∧
      p.processVariables.sentEcho = none ∧
      ν = PMF.pure (p.setProcessVariables
        { p.processVariables with sentEcho := some p.processVariables.accepted }) := by
  cases h
  case sendEcho => exact ⟨rfl, by assumption, by assumption, by assumption, rfl⟩
  case sendIdle => exact absurd rfl ‹_ ≠ j›

theorem programStep_send_vote_own {U : AcceptedPairs P.n X}
    (h : ProgramStep P j p (Sum.inr (.send j (.vote U))) ν) :
    p.processVariables.input ≠ none ∧ p.processVariables.sentEcho ≠ none ∧ approvedBy
      p.processVariables U ∧
      (∃ Q : Finset (Fin P.n), P.n - P.f ≤ Q.card ∧
        ∀ q ∈ Q, ∃ A, Message.echo A ∈ p.received q ∧ approvedBy p.processVariables A ∧ A ⊆ U) ∧
      p.processVariables.sentVote = none ∧ ν = PMF.pure
        (p.setProcessVariables { p.processVariables with sentVote := some U }) := by
  cases h
  case sendVote =>
    exact ⟨by assumption, by assumption, by assumption, by assumption, by assumption, rfl⟩
  case sendIdle => exact absurd rfl ‹_ ≠ j›

theorem programStep_send_bind_own {U : AcceptedPairs P.n X}
    (h : ProgramStep P j p (Sum.inr (.send j (.bind U))) ν) :
    p.processVariables.input ≠ none ∧ p.processVariables.sentVote ≠ none ∧ approvedBy
      p.processVariables U ∧
      (∃ Q : Finset (Fin P.n), P.n - P.f ≤ Q.card ∧
        ∀ q ∈ Q, ∃ W, Message.vote W ∈ p.received q ∧ approvedBy p.processVariables W ∧ W ⊆ U) ∧
      p.processVariables.sentBind = none ∧ ν = PMF.pure
        (p.setProcessVariables { p.processVariables with sentBind := some U }) := by
  cases h
  case sendBind =>
    exact ⟨by assumption, by assumption, by assumption, by assumption, by assumption, rfl⟩
  case sendIdle => exact absurd rfl ‹_ ≠ j›

theorem programStep_send_notOwn {i : Fin P.n} {m : Message P.n X} (hi : i ≠ j)
    (h : ProgramStep P j p (Sum.inr (.send i m)) ν) : ν = PMF.pure p := by
  cases h
  case sendIdle => rfl
  all_goals exact absurd rfl hi

theorem programStep_deliver_own {k : Fin P.n} {m : Message P.n X}
    (h : ProgramStep P j p (Sum.inr (.deliver j k m)) ν) : ν = PMF.pure (p.deliverTo k m) := by
  cases h
  case deliverReceive => rfl
  case deliverIdle => exact absurd rfl ‹_ ≠ j›

theorem programStep_deliver_notOwn {i k : Fin P.n} {m : Message P.n X} (hi : i ≠ j)
    (h : ProgramStep P j p (Sum.inr (.deliver i k m)) ν) : ν = PMF.pure p := by
  cases h
  case deliverReceive => exact absurd rfl hi
  case deliverIdle => rfl

theorem programStep_inputBroadcastCall_own {x : X}
    (h : ProgramStep P j p (Sum.inr (.inputBroadcastCall j x)) ν) :
    p.processVariables.input = some x ∧ ν = PMF.pure p := by
  cases h
  case inputBroadcastCall => exact ⟨by assumption, rfl⟩
  case inputBroadcastCallIdle => exact absurd rfl ‹_ ≠ j›

theorem programStep_inputBroadcastCall_notOwn {i : Fin P.n} {x : X} (hi : i ≠ j)
    (h : ProgramStep P j p (Sum.inr (.inputBroadcastCall i x)) ν) : ν = PMF.pure p := by
  cases h
  case inputBroadcastCall => exact absurd rfl hi
  case inputBroadcastCallIdle => rfl

theorem programStep_inputBroadcastRet_own {k : Fin P.n} {v : X}
    (h : ProgramStep P j p (Sum.inr (.inputBroadcastRet k j v)) ν) :
    ν = PMF.pure (p.setProcessVariables { p.processVariables with
      inputBroadcastReturned :=
        Function.update p.processVariables.inputBroadcastReturned k (some v) }) := by
  cases h
  case inputBroadcastRetReceive => rfl
  case inputBroadcastRetIdle => exact absurd rfl ‹_ ≠ j›

theorem programStep_inputBroadcastRet_notOwn {k i : Fin P.n} {v : X} (hi : i ≠ j)
    (h : ProgramStep P j p (Sum.inr (.inputBroadcastRet k i v)) ν) : ν = PMF.pure p := by
  cases h
  case inputBroadcastRetReceive => exact absurd rfl hi
  case inputBroadcastRetIdle => rfl

end ProgramStepCases
/-! ### The gather network's transitions, by label class -/

section NetworkStepCases
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

theorem networkStep_inputBroadcastCall {j : Fin P.n} {x : X}
    (h : NetworkStep P w (Sum.inr (.inputBroadcastCall j x)) μ) : μ = PMF.pure w := by
  cases h; rfl

theorem networkStep_inputBroadcastRet {k j : Fin P.n} {v : X}
    (h : NetworkStep P w (Sum.inr (.inputBroadcastRet k j v)) μ) : μ = PMF.pure w := by
  cases h; rfl

theorem networkStep_tau (h : NetworkStep P w (Sum.inl (Sum.inl .tau)) μ) :
    ∃ (j : Fin P.n) (m : Message P.n X), j ∈ w.network.F ∧
      μ = PMF.pure { w with network := w.network.recordSent j m } := by
  cases h
  case byzantine j m hF => exact ⟨j, m, hF, rfl⟩

end NetworkStepCases
/-! ### The write a transition makes on the composed state

A synchronised step delivers a program function pointwise: its value at the acting
process, and its agreement with the old one elsewhere. `Function.eq_update_iff`
reads that function as the old one updated at the acting process, and the
lemmas here identify the state a transition writes with `setGatherProgramsAndNetwork` and
`InstanceState.setProcessVariables`. -/

section Writes

/-! ### The writes that leave the sent sets alone -/

section

variable {P : Parameters} {B : Type}
  {u x : ∀ _ : Fin P.n, LocalState P.n (ProcessVariables P.n X) (Message P.n X)}
  {w : NetworkState P.n X} {a : ∀ _ : Fin P.n, B}

/-- A write to the variables of one program, with the network state untouched. -/
theorem stateOverBroadcasts_setProcessVariables {j : Fin P.n} {pr : ProcessVariables P.n X}
    (hj : x j = (u j).setProcessVariables pr) (hne : ∀ i, i ≠ j → x i = u i) :
    (((x, w), a) : StateOverBroadcasts P.n X B) = setGatherProgramsAndNetwork ((u, w), a)
    (InstanceState.setProcessVariables (gatherProgramsAndNetwork ((u, w), a)) j pr) := by
  rw [Function.eq_update_iff.mpr ⟨hj, hne⟩]; rfl

/-- The programs remain unchanged and the network state is untouched. -/
theorem stateOverBroadcasts_idle (hall : ∀ i, x i = u i) :
    (((x, w), a) : StateOverBroadcasts P.n X B) = ((u, w), a) := by
  rw [funext hall]

/-- A return: the returner's flag and the instance's core. -/
theorem stateOverBroadcasts_ret {id : Fin P.n} {pr : ProcessVariables P.n X} {C : AcceptedPairs P.n
  X}
    (hj : x id = (u id).setProcessVariables pr) (hne : ∀ i, i ≠ id → x i = u i) :
    (((x, { w with core := some C }), a) : StateOverBroadcasts P.n X B) = setCore
    (setGatherProgramsAndNetwork ((u, w), a) (InstanceState.setProcessVariables
      (gatherProgramsAndNetwork ((u, w), a))
      id pr))
    (some C) := by
  rw [Function.eq_update_iff.mpr ⟨hj, hne⟩]; rfl

/-- Corruption is the network state's own write beside the input instances'
(D1). -/
theorem stateOverBroadcasts_corrupt {id : Fin P.n} {cIn : B → B} (hall : ∀ i,
    x i = u i) : (((x, { w with network := w.network.corrupt P id }),
        (fun k => cIn (a k))) : StateOverBroadcasts P.n X B) =
      corruptAll P id cIn ((u, w), a) := by
  rw [funext hall]; rfl

/-- A write at one input instance. -/
theorem stateOverBroadcasts_setInputBroadcasts {k : Fin P.n} {c : B} :
    (((u, w), Function.update a k c) : StateOverBroadcasts P.n X B) =
      setInputBroadcasts ((u, w), a) (Function.update (inputBroadcasts ((u, w), a)) k c) := rfl

end

/-! ### The writes that record or deliver a message -/

section

variable [DecidableEq X] {P : Parameters} {B : Type}
  {u x : ∀ _ : Fin P.n, LocalState P.n (ProcessVariables P.n X) (Message P.n X)}
  {w : NetworkState P.n X} {a : ∀ _ : Fin P.n, B}

/-- A write to the variables of one program together with the network state recording the
message that write multicasts. -/
theorem stateOverBroadcasts_setProcessVariables_recordSent {j : Fin P.n} {pr : ProcessVariables P.n
  X}
    {m : Message P.n X} (hj : x j = (u j).setProcessVariables pr) (hne : ∀ i, i ≠ j → x i = u i) :
    (((x, { w with network := w.network.recordSent j m }), a) : StateOverBroadcasts P.n X B)
    = setGatherProgramsAndNetwork ((u, w), a)
    ((InstanceState.setProcessVariables (gatherProgramsAndNetwork ((u, w), a)) j pr).multicast
      j m) := by
  rw [Function.eq_update_iff.mpr ⟨hj, hne⟩]; rfl

/-- A delivery: the receiver files the message under the sender it came from. -/
theorem stateOverBroadcasts_deliver {i k : Fin P.n} {m : Message P.n X}
    (hi : x i = (u i).deliverTo k m) (hne : ∀ i', i' ≠ i → x i' = u i') :
    (((x, w), a) : StateOverBroadcasts P.n X B) = setGatherProgramsAndNetwork ((u, w), a)
    (InstanceState.receiveMessage (gatherProgramsAndNetwork ((u, w), a)) i k m) := by
  rw [Function.eq_update_iff.mpr ⟨hi, hne⟩]; rfl

/-- A Byzantine injection: the network state records a message under a
corrupted sender. -/
theorem stateOverBroadcasts_recordSent {k : Fin P.n} {m : Message P.n X} :
    (((u, { w with network := w.network.recordSent k m }), a) : StateOverBroadcasts P.n X B) =
      setGatherProgramsAndNetwork ((u, w), a)
        (InstanceState.multicast (gatherProgramsAndNetwork ((u, w), a)) k m) := rfl

end

end Writes
end Gather
end ABA
end PLTS
