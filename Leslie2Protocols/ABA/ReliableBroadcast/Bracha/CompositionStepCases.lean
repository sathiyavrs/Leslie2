/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sathiya / Claude
-/

import Leslie2Protocols.ABA.ReliableBroadcast.Bracha.SpecificationOverInstanceAlphabet
import Leslie2Protocols.Framework.SynchronisedProduct
import Leslie2Protocols.Framework.SynchronisedProductAlongPullbacks

/-!
# The transitions of the reliable-broadcast composition, read off their labels

The composition is `relabel ∘ abstract ∘ parallel` over the synchronised group of programs
and the instance's network. The lemmas here unfold that pipeline in both directions.

`brachaInstance_step_iff` splits a transition of the instance into a hidden synchronisation and an
interface label. Over the instance-internal alphabet, a visible label moves both factors, the
programs and the network, and the product distribution is their Dirac product. A silent label
moves the network alone. `brachaInstanceExtended_synchronised_cases` and
`brachaInstanceExtended_tau_cases` read a synchronised step that way, and the `_step` lemmas build
one from the transitions of the factors.

`programStep_*` reads one program's transition off its label: the participant's guards together
with the Dirac it produces, and the idle transition of a non-participant as the identity.
`networkStep_*` does the same for the instance's network.

A synchronised step delivers a program function given pointwise, by its value at the acting process
and its agreement with the old function elsewhere. `Function.eq_update_iff` identifies that
function with the old one updated at the acting process, and the `brachaInstance_*` lemmas
identify the state a transition writes with `InstanceState.setProcessVariables`,
`InstanceState.multicast`,
`InstanceState.receiveMessage` or `InstanceState.corrupt` applied to the old state.
-/

namespace PLTS
namespace ABA
namespace BRB

variable {M : Type} [DecidableEq M]

/-! ### Reading and building instance transitions

The pipeline is `relabel ∘ abstract ∘ parallel ∘ synchronisedProduct`; the lemmas below
unfold it once and for all, in both directions. -/

/-- A synchronised transition of the program group on a visible label: every
program steps, and the product distribution is Dirac. -/
theorem broadcastProgramProduct_cases {P : Parameters} {ldr : Fin P.n}
    {u : ∀ _ : Fin P.n, LocalState P.n (ProcessVariables M) (Message M)} {l : BroadcastLabel P.n M}
    {μ : PMF (∀ _ : Fin P.n, LocalState P.n (ProcessVariables M) (Message M))}
    (h : (System.synchronisedProduct (broadcastProgram P ldr (M := M))).step u l μ) :
    ∃ x : ∀ _ : Fin P.n, LocalState P.n (ProcessVariables M) (Message M),
      μ = PMF.pure x ∧ ∀ i, ProgramStep P ldr i (u i) l (PMF.pure (x i)) := by
  rw [System.synchronisedProduct_step] at h
  rcases h with ⟨-, μ_, hall, rfl⟩ | ⟨rfl, i, μ_i, hstep, -⟩
  · have hx : ∀ i, ∃ p', μ_ i = PMF.pure p' := fun i => programStep_dirac (hall i)
    choose x hx using hx
    refine ⟨x, ?_, fun i => ?_⟩
    · rw [show μ_ = fun i => PMF.pure (x i) from funext hx]
      exact piPMF_pure x
    · rw [← hx i]; exact hall i
  · exact absurd hstep programStep_no_tau

/-- Build a synchronised transition of the program group from per-process Dirac
steps. -/
theorem broadcastProgramProduct_pure {P : Parameters} {ldr : Fin P.n}
    {u x : ∀ _ : Fin P.n, LocalState P.n (ProcessVariables M) (Message M)} {l : BroadcastLabel P.n
      M}
    (hl : l ≠ Silent.τ) (h : ∀ i, ProgramStep P ldr i (u i) l (PMF.pure (x i))) :
    (System.synchronisedProduct (broadcastProgram P ldr (M := M))).step u l (PMF.pure x) := by
  rw [System.synchronisedProduct_step]
  exact Or.inl ⟨hl, fun i => PMF.pure (x i), h, (piPMF_pure x).symm⟩

/-- The program group has no silent transition: no program steps on `τ`. -/
theorem broadcastProgramProduct_no_tau {P : Parameters} {ldr : Fin P.n}
    {u : ∀ _ : Fin P.n, LocalState P.n (ProcessVariables M) (Message M)}
    {μ : PMF (∀ _ : Fin P.n, LocalState P.n (ProcessVariables M) (Message M))}
    (h : (System.synchronisedProduct (broadcastProgram P ldr (M := M))).step u
      (Silent.τ : BroadcastLabel P.n M) μ) :
    False := by
  rcases h with ⟨hτ, -⟩ | ⟨-, i, μ_i, hstep, -⟩
  · exact hτ rfl
  · exact programStep_no_tau hstep

/-- The instance's step relation, unfolded to the hidden-synchronisation case and
the interface-label case. -/
theorem brachaInstance_step_iff (P : Parameters) (ldr : Fin P.n) (q : BrachaState P.n M)
    (l : InstanceLabel P.n M) (μ : PMF (BrachaState P.n M)) :
    (brachaInstance P ldr M).step q l μ ↔
      (l = Sum.inl Label.tau ∧ ∃ e : BroadcastEvent P.n M,
        (brachaInstanceExtended P ldr M).step q (Sum.inr e) μ) ∨
      (brachaInstanceExtended P ldr M).step q (Sum.inl l) μ := by
  constructor
  · rintro (⟨hτ, l', ⟨e, rfl⟩, hstep⟩ | ⟨-, hstep⟩)
    · exact Or.inl ⟨Sum.inl_injective hτ, e, hstep⟩
    · exact Or.inr hstep
  · rintro (⟨rfl, e, hstep⟩ | hstep)
    · exact Or.inl ⟨rfl, _, inr_mem_broadcastEvents e, hstep⟩
    · exact Or.inr ⟨inl_notMem_broadcastEvents l, hstep⟩

/-- Build a synchronised transition of the programs and the network on a
synchronisation label. -/
theorem brachaInstanceExtended_event_step (P : Parameters) (ldr : Fin P.n)
    {u x : ∀ _ : Fin P.n, LocalState P.n (ProcessVariables M) (Message M)}
    {w w' : NetworkState P.n (Message M)} (e : BroadcastEvent P.n M)
    (hall : ∀ i, ProgramStep P ldr i (u i) (Sum.inr e) (PMF.pure (x i)))
    (hn : NetworkStep P ldr w (Sum.inr e) (PMF.pure w')) :
    (brachaInstanceExtended P ldr M).step (u, w) (Sum.inr e) (PMF.pure (x, w')) := by
  rw [brachaInstanceExtended, System.parallel_step]
  exact Or.inl ⟨by simp, PMF.pure x, PMF.pure w', broadcastProgramProduct_pure (by simp) hall, hn,
    (prodPMF_pure_pure _ _).symm⟩

/-- Build a synchronised transition of the programs and the network on a visible
interface label. -/
theorem brachaInstanceExtended_label_step (P : Parameters) (ldr : Fin P.n)
    {u x : ∀ _ : Fin P.n, LocalState P.n (ProcessVariables M) (Message M)}
    {w w' : NetworkState P.n (Message M)} {l : InstanceLabel P.n M} (hl : l ≠ Sum.inl Label.tau)
    (hall : ∀ i, ProgramStep P ldr i (u i) (Sum.inl l) (PMF.pure (x i)))
    (hn : NetworkStep P ldr w (Sum.inl l) (PMF.pure w')) :
    (brachaInstanceExtended P ldr M).step (u, w) (Sum.inl l) (PMF.pure (x, w')) := by
  have hne : (Sum.inl l : BroadcastLabel P.n M) ≠ Silent.τ := by
    rw [broadcastLabel_tau]; simpa using hl
  rw [brachaInstanceExtended, System.parallel_step]
  exact Or.inl ⟨hne, PMF.pure x, PMF.pure w', broadcastProgramProduct_pure hne hall, hn,
    (prodPMF_pure_pure _ _).symm⟩

/-- Build a silent transition of the programs and the network from a
network-local one. -/
theorem brachaInstanceExtended_tau_network (P : Parameters) (ldr : Fin P.n)
    {u : ∀ _ : Fin P.n, LocalState P.n (ProcessVariables M) (Message M)}
    {w w' : NetworkState P.n (Message M)}
    (hn : NetworkStep P ldr w (Sum.inl (Sum.inl .tau)) (PMF.pure w')) :
    (brachaInstanceExtended P ldr M).step (u, w) (Sum.inl (Sum.inl .tau)) (PMF.pure (u, w')) := by
  rw [brachaInstanceExtended, System.parallel_step]
  exact Or.inr (Or.inr ⟨rfl, PMF.pure w', hn, (prodPMF_pure_pure _ _).symm⟩)

/-- A hidden synchronisation is a silent transition of the instance. -/
theorem brachaInstance_event_step (P : Parameters) (ldr : Fin P.n)
    {u x : ∀ _ : Fin P.n, LocalState P.n (ProcessVariables M) (Message M)}
    {w w' : NetworkState P.n (Message M)} (e : BroadcastEvent P.n M)
    (hall : ∀ i, ProgramStep P ldr i (u i) (Sum.inr e) (PMF.pure (x i)))
    (hn : NetworkStep P ldr w (Sum.inr e) (PMF.pure w')) :
    (brachaInstance P ldr M).step (u, w) (Sum.inl Label.tau) (PMF.pure (x, w')) :=
  (brachaInstance_step_iff P ldr _ _ _).mpr (Or.inl ⟨rfl, e,
    brachaInstanceExtended_event_step P ldr e hall hn⟩)

/-- A visible interface label is a transition of the instance. -/
theorem brachaInstance_label_step (P : Parameters) (ldr : Fin P.n)
    {u x : ∀ _ : Fin P.n, LocalState P.n (ProcessVariables M) (Message M)}
    {w w' : NetworkState P.n (Message M)} {l : InstanceLabel P.n M} (hl : l ≠ Sum.inl Label.tau)
    (hall : ∀ i, ProgramStep P ldr i (u i) (Sum.inl l) (PMF.pure (x i)))
    (hn : NetworkStep P ldr w (Sum.inl l) (PMF.pure w')) :
    (brachaInstance P ldr M).step (u, w) l (PMF.pure (x, w')) :=
  (brachaInstance_step_iff P ldr _ _ _).mpr (Or.inr (brachaInstanceExtended_label_step P ldr hl hall
    hn))

/-- A network-local injection is a silent transition of the instance. -/
theorem brachaInstance_tau_network (P : Parameters) (ldr : Fin P.n)
    {u : ∀ _ : Fin P.n, LocalState P.n (ProcessVariables M) (Message M)}
    {w w' : NetworkState P.n (Message M)}
    (hn : NetworkStep P ldr w (Sum.inl (Sum.inl .tau)) (PMF.pure w')) :
    (brachaInstance P ldr M).step (u, w) (Sum.inl Label.tau) (PMF.pure (u, w')) :=
  (brachaInstance_step_iff P ldr _ _ _).mpr (Or.inr (brachaInstanceExtended_tau_network P ldr hn))

/-- A visible transition of the programs beside the network: every program and
the network step on the label, and the product distribution is their Dirac
product. -/
theorem brachaInstanceExtended_synchronised_cases {P : Parameters} {ldr : Fin P.n}
    {u : ∀ _ : Fin P.n, LocalState P.n (ProcessVariables M) (Message M)}
    {w : NetworkState P.n (Message M)} {L : BroadcastLabel P.n M} {μ : PMF (BrachaState P.n M)}
    (hL : L ≠ (Silent.τ : BroadcastLabel P.n M))
    (h : (brachaInstanceExtended P ldr M).step (u, w) L μ) :
    ∃ (x : ∀ _ : Fin P.n, LocalState P.n (ProcessVariables M) (Message M))
    (w' : NetworkState P.n (Message M)), μ = PMF.pure (x, w') ∧
    (∀ i, ProgramStep P ldr i (u i) L (PMF.pure (x i))) ∧ NetworkStep P ldr w L (PMF.pure w') := by
  rw [brachaInstanceExtended, System.parallel_step] at h
  rcases h with ⟨-, μ₁, μ₂, hs, hn, rfl⟩ | ⟨hτ, -⟩ | ⟨hτ, -⟩
  · obtain ⟨x, rfl, hall⟩ := broadcastProgramProduct_cases hs
    obtain ⟨w', rfl⟩ := networkStep_dirac hn
    exact ⟨x, w', prodPMF_pure_pure _ _, hall, hn⟩
  · exact absurd hτ hL
  · exact absurd hτ hL

/-- A silent transition of the programs beside the network is a network-local
injection: no program steps on `τ`. -/
theorem brachaInstanceExtended_tau_cases {P : Parameters} {ldr : Fin P.n}
    {u : ∀ _ : Fin P.n, LocalState P.n (ProcessVariables M) (Message M)}
    {w : NetworkState P.n (Message M)} {μ : PMF (BrachaState P.n M)}
    (h : (brachaInstanceExtended P ldr M).step (u, w) (Sum.inl (Sum.inl Label.tau)) μ) :
    ∃ w' : NetworkState P.n (Message M), μ = PMF.pure (u, w') ∧ NetworkStep P ldr w
    (Sum.inl (Sum.inl Label.tau)) (PMF.pure w') := by
  rw [brachaInstanceExtended, System.parallel_step] at h
  rcases h with ⟨hτ, -⟩ | ⟨-, μ₁, hs, rfl⟩ | ⟨-, μ₂, hn, rfl⟩
  · exact absurd rfl hτ
  · exact absurd hs broadcastProgramProduct_no_tau
  · obtain ⟨w', rfl⟩ := networkStep_dirac hn
    exact ⟨w', prodPMF_pure_pure _ _, hn⟩

/-! ### One program's transitions, by label class

Each lemma reads one transition off its label: the participant's guards
together with the Dirac it produces, and the idle transition of a
non-participant as the identity. The state and the distribution are variables,
so `cases` unifies against any state of the program. -/

section ProgramStepCases
variable {P : Parameters} {ldr j : Fin P.n} {p : LocalState P.n (ProcessVariables M) (Message M)}
  {ν : PMF (LocalState P.n (ProcessVariables M) (Message M))}

theorem programStep_call_leader {m : M}
    (h : ProgramStep P ldr ldr p (Sum.inl (Sum.inl (.call m))) ν) :
    p.processVariables.input = none ∧ ν = PMF.pure (p.setProcessVariables { p.processVariables with
      input := some m }) := by
  cases h
  case call => exact ⟨by assumption, rfl⟩
  case callIdle => exact absurd rfl ‹_ ≠ ldr›

theorem programStep_call_notOwn {m : M} (hj : j ≠ ldr)
    (h : ProgramStep P ldr j p (Sum.inl (Sum.inl (.call m))) ν) : ν = PMF.pure p := by
  cases h
  case call => exact absurd ‹j = ldr› hj
  case callIdle => rfl

theorem programStep_callLoop {m : M}
    (h : ProgramStep P ldr j p (Sum.inl (Sum.inr (.callLoop m))) ν) : ν = PMF.pure p := by
  cases h
  case callLoop => rfl

theorem programStep_ret_own {m : M}
    (h : ProgramStep P ldr j p (Sum.inl (Sum.inl (.ret j m))) ν) :
    2 * P.f + 1 ≤ p.receivedCount (.vote m) ∧ p.processVariables.returned = false ∧
      ν = PMF.pure (p.setProcessVariables { p.processVariables with returned := true }) := by
  cases h
  case ret => exact ⟨by assumption, by assumption, rfl⟩
  case retIdle => exact absurd rfl ‹_ ≠ j›

theorem programStep_ret_notOwn {i : Fin P.n} {m : M} (hi : i ≠ j)
    (h : ProgramStep P ldr j p (Sum.inl (Sum.inl (.ret i m))) ν) : ν = PMF.pure p := by
  cases h
  case ret => exact absurd rfl hi
  case retIdle => rfl

theorem programStep_fail {i : Fin P.n}
    (h : ProgramStep P ldr j p (Sum.inl (Sum.inl (.fail i))) ν) : ν = PMF.pure p := by
  cases h
  case failIdle => rfl

theorem programStep_send_init_own {m : M}
    (h : ProgramStep P ldr j p (Sum.inr (.send j (.init m))) ν) : False := by
  cases h
  case sendIdle => exact absurd rfl ‹_ ≠ j›

theorem programStep_send_echo_own {m : M}
    (h : ProgramStep P ldr j p (Sum.inr (.send j (.echo m))) ν) :
    (Message.init m ∈ p.received ldr ∨ P.receivedEchoQuorum ≤ p.receivedCount (.echo m) ∨
        P.f + 1 ≤ p.receivedCount (.vote m)) ∧ p.processVariables.sentEcho = none ∧
      ν = PMF.pure (p.setProcessVariables { p.processVariables with sentEcho := some m }) := by
  cases h
  case sendEcho => exact ⟨by assumption, by assumption, rfl⟩
  case sendIdle => exact absurd rfl ‹_ ≠ j›

theorem programStep_send_vote_own {m : M}
    (h : ProgramStep P ldr j p (Sum.inr (.send j (.vote m))) ν) :
    (P.receivedEchoQuorum ≤ p.receivedCount (.echo m) ∨ P.f + 1 ≤ p.receivedCount (.vote m)) ∧
      p.processVariables.sentVote = none ∧
      ν = PMF.pure (p.setProcessVariables { p.processVariables with sentVote := some m }) := by
  cases h
  case sendVoteQuorum => exact ⟨Or.inl (by assumption), by assumption, rfl⟩
  case sendVoteAmplification => exact ⟨Or.inr (by assumption), by assumption, rfl⟩
  case sendIdle => exact absurd rfl ‹_ ≠ j›

theorem programStep_send_notOwn {i : Fin P.n} {m : Message M} (hi : i ≠ j)
    (h : ProgramStep P ldr j p (Sum.inr (.send i m)) ν) : ν = PMF.pure p := by
  cases h
  case sendIdle => rfl
  all_goals exact absurd rfl hi

theorem programStep_deliver_own {k : Fin P.n} {m : Message M}
    (h : ProgramStep P ldr j p (Sum.inr (.deliver j k m)) ν) : ν = PMF.pure (p.deliverTo k m) := by
  cases h
  case deliverReceive => rfl
  case deliverIdle => exact absurd rfl ‹_ ≠ j›

theorem programStep_deliver_notOwn {i k : Fin P.n} {m : Message M} (hi : i ≠ j)
    (h : ProgramStep P ldr j p (Sum.inr (.deliver i k m)) ν) : ν = PMF.pure p := by
  cases h
  case deliverReceive => exact absurd rfl hi
  case deliverIdle => rfl

end ProgramStepCases
/-! ### The network's transitions, by label class -/

section NetworkStepCases
variable {P : Parameters} {ldr : Fin P.n} {w : NetworkState P.n (Message M)}
  {μ : PMF (NetworkState P.n (Message M))}

theorem networkStep_call {m : M} (h : NetworkStep P ldr w (Sum.inl (Sum.inl (.call m))) μ) :
    μ = PMF.pure (w.recordSent ldr (.init m)) := by
  cases h; rfl

theorem networkStep_callLoop {m : M} (h : NetworkStep P ldr w (Sum.inl (Sum.inr (.callLoop m))) μ) :
    μ = PMF.pure w := by
  cases h; rfl

theorem networkStep_ret {i : Fin P.n} {m : M}
    (h : NetworkStep P ldr w (Sum.inl (Sum.inl (.ret i m))) μ) : μ = PMF.pure w := by
  cases h; rfl

theorem networkStep_fail {i : Fin P.n} (h : NetworkStep P ldr w (Sum.inl (Sum.inl (.fail i))) μ) :
    μ = PMF.pure (w.corrupt P i) := by
  cases h; rfl

theorem networkStep_send {j : Fin P.n} {m : Message M}
    (h : NetworkStep P ldr w (Sum.inr (.send j m)) μ) : μ = PMF.pure (w.recordSent j m) := by
  cases h; rfl

theorem networkStep_deliver {i j : Fin P.n} {m : Message M}
    (h : NetworkStep P ldr w (Sum.inr (.deliver i j m)) μ) : m ∈ w.sent j ∧ μ = PMF.pure w := by
  cases h; exact ⟨by assumption, rfl⟩

theorem networkStep_tau (h : NetworkStep P ldr w (Sum.inl (Sum.inl .tau)) μ) :
    ∃ (j : Fin P.n) (m : Message M), j ∈ w.F ∧ μ = PMF.pure (w.recordSent j m) := by
  cases h
  case byzantine j m hF => exact ⟨j, m, hF, rfl⟩

end NetworkStepCases
/-! ### The write a transition makes on the composed state

The local states and the network state are the two components of `BrachaState`
(`ABA/ReliableBroadcast/Bracha/MessagesAndVariables.lean`), so a synchronised step of the programs
and the
network writes the state the instance's own accessors read. Such a step delivers a program
function pointwise: its value at the acting process, and its agreement with the old one elsewhere.
`Function.eq_update_iff` reads that function as the old one updated at the acting process, and the
lemmas here identify the state written with `InstanceState.setProcessVariables`. -/

section Writes

/-! ### The writes that leave the sent sets alone -/

section

variable {M : Type} {P : Parameters}
  {u x : ∀ _ : Fin P.n, LocalState P.n (ProcessVariables M) (Message M)}
  {w : NetworkState P.n (Message M)}

/-- A write to the variables of one program, with the network state untouched. -/
theorem brachaInstance_setProcessVariables {j : Fin P.n} {pr : ProcessVariables M}
    (hj : x j = (u j).setProcessVariables pr) (hne : ∀ i, i ≠ j → x i = u i) :
    ((x, w) : BrachaState P.n M) = InstanceState.setProcessVariables (u, w) j pr := by
  rw [Function.eq_update_iff.mpr ⟨hj, hne⟩]
  rfl

/-- The programs remain unchanged. -/
theorem brachaInstance_idle (hall : ∀ i, x i = u i) : ((x, w) : BrachaState P.n M) = (u, w) := by
  rw [funext hall]

/-- Corruption is the network state's own write (D1). -/
theorem brachaInstance_corrupt (k : Fin P.n) :
    ((u, w.corrupt P k) : BrachaState P.n M) = InstanceState.corrupt P k (u, w) := rfl

end

/-! ### The writes that record or deliver a message -/

section

variable {M : Type} [DecidableEq M] {P : Parameters}
  {u x : ∀ _ : Fin P.n, LocalState P.n (ProcessVariables M) (Message M)}
  {w : NetworkState P.n (Message M)}

/-- A write to the variables of one program together with the network state recording the
message that write multicasts. -/
theorem brachaInstance_setProcessVariables_recordSent {j : Fin P.n} {pr : ProcessVariables M} {m :
  Message M}
    (hj : x j = (u j).setProcessVariables pr) (hne : ∀ i, i ≠ j → x i = u i) :
    ((x, w.recordSent j m) : BrachaState P.n M) = (InstanceState.setProcessVariables (u, w) j
      pr).multicast j
    m := by
  rw [Function.eq_update_iff.mpr ⟨hj, hne⟩]
  rfl

/-- A delivery: the receiver files the message under its sender. -/
theorem brachaInstance_deliver {i k : Fin P.n} {m : Message M}
    (hi : x i = (u i).deliverTo k m) (hne : ∀ i', i' ≠ i → x i' = u i') :
    ((x, w) : BrachaState P.n M) = InstanceState.receiveMessage (u, w) i k m := by
  rw [Function.eq_update_iff.mpr ⟨hi, hne⟩]
  rfl

/-- A Byzantine injection: the network state records a message under a
corrupted sender. -/
theorem brachaInstance_recordSent {k : Fin P.n} {m : Message M} :
    ((u, w.recordSent k m) : BrachaState P.n M) = InstanceState.multicast (u, w) k m := rfl

end

end Writes

end BRB
end ABA
end PLTS
