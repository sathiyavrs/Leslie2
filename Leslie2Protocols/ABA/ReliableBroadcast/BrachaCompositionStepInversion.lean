/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sathiya / Claude
-/

import Leslie2Protocols.ABA.ReliableBroadcast.BrachaSpecificationOverInstanceAlphabet
import Leslie2Protocols.Framework.SynchronisedProduct

/-!
# The transitions of the reliable-broadcast composition, read off their labels

The composition is `relabel ∘ abstract ∘ parallel` over the synchronised group of programs
and the instance's network. The lemmas here unfold that pipeline in both directions.

`brachaInstance_step_iff` splits a transition of the instance into a hidden rendezvous and an
interface label. Over the instance-internal alphabet, a visible label moves both factors — the
programs and the network — and the joint distribution is their Dirac product. A silent label
moves the network alone. `brachaInstanceExtended_joint_inversion` and
`brachaInstanceExtended_tau_inversion` read a joint step that way, and the `_step` lemmas build
one from the factors' rows.

`programStep_*` reads one program's row off its label: the participant's row as its guards
together with the Dirac it produces, and the idle row of a non-participant as the identity.
`networkStep_*` does the same for the instance's network.

A joint step delivers a program function given pointwise, by its value at the acting process
and its agreement with the old function elsewhere. `programFunction_update` identifies that
function with the old one updated at the acting process, and the `brachaInstance_*` lemmas
identify the state a row writes with `InstanceState.setProcess`, `InstanceState.multicast`,
`InstanceState.receiveMessage` or `InstanceState.corrupt` applied to the old state.

## The rows

`brachaInstance_step_iff_row` is the row characterisation: at a specification label `l₀`, the
transitions of the composition over the labels `specificationLabelMap` sends to `l₀` are
exactly the `l₀`-rows of `BRB.BrachaStep` (`ABA/ReliableBroadcast/BrachaImplementation.lean`),
one constructor per case, on the same product state and with the same distribution. The call
and the call loop are the two rows of `call m`, taken at the two labels; every other
specification label has a single label over it.
-/

namespace PLTS
namespace ABA
namespace BRB

variable {M : Type} [DecidableEq M]

/-! ### Reading and building instance transitions

The pipeline is `relabel ∘ abstract ∘ parallel ∘ synchronisedProduct`; the lemmas below
unfold it once and for all, in both directions. -/

/-- A synchronised transition of the program group on a visible label: every
program steps, and the joint distribution is Dirac. -/
theorem broadcastProgramProduct_inversion {P : Parameters} {ldr : Fin P.n}
    {u : ∀ _ : Fin P.n, LocalState P.n (ProcessRecord M) (Message M)} {l : BroadcastLabel P.n M}
    {μ : PMF (∀ _ : Fin P.n, LocalState P.n (ProcessRecord M) (Message M))}
    (h : (System.synchronisedProduct (broadcastProgram P ldr (M := M))).step u l μ) :
    ∃ x : ∀ _ : Fin P.n, LocalState P.n (ProcessRecord M) (Message M),
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
    {u x : ∀ _ : Fin P.n, LocalState P.n (ProcessRecord M) (Message M)} {l : BroadcastLabel P.n M}
    (hl : l ≠ Silent.τ) (h : ∀ i, ProgramStep P ldr i (u i) l (PMF.pure (x i))) :
    (System.synchronisedProduct (broadcastProgram P ldr (M := M))).step u l (PMF.pure x) := by
  rw [System.synchronisedProduct_step]
  exact Or.inl ⟨hl, fun i => PMF.pure (x i), h, (piPMF_pure x).symm⟩

/-- The program group has no silent transition: no program has a `τ` row. -/
theorem broadcastProgramProduct_no_tau {P : Parameters} {ldr : Fin P.n}
    {u : ∀ _ : Fin P.n, LocalState P.n (ProcessRecord M) (Message M)}
    {μ : PMF (∀ _ : Fin P.n, LocalState P.n (ProcessRecord M) (Message M))}
    (h : (System.synchronisedProduct (broadcastProgram P ldr (M := M))).step u
      (Silent.τ : BroadcastLabel P.n M) μ) :
    False := by
  rcases h with ⟨hτ, -⟩ | ⟨-, i, μ_i, hstep, -⟩
  · exact hτ rfl
  · exact programStep_no_tau hstep

/-- The instance's step relation, unfolded to the hidden-rendezvous case and
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

/-- Build a joint transition of the programs and the network on a rendezvous
label. -/
theorem brachaInstanceExtended_event_step (P : Parameters) (ldr : Fin P.n)
    {u x : ∀ _ : Fin P.n, LocalState P.n (ProcessRecord M) (Message M)}
    {w w' : NetworkState P.n (Message M)} (e : BroadcastEvent P.n M)
    (hall : ∀ i, ProgramStep P ldr i (u i) (Sum.inr e) (PMF.pure (x i)))
    (hn : NetworkStep P ldr w (Sum.inr e) (PMF.pure w')) :
    (brachaInstanceExtended P ldr M).step (u, w) (Sum.inr e) (PMF.pure (x, w')) := by
  rw [brachaInstanceExtended, System.parallel_step]
  exact Or.inl ⟨by simp, PMF.pure x, PMF.pure w', broadcastProgramProduct_pure (by simp) hall, hn,
    (prodPMF_pure_pure _ _).symm⟩

/-- Build a joint transition of the programs and the network on a visible
interface label. -/
theorem brachaInstanceExtended_label_step (P : Parameters) (ldr : Fin P.n)
    {u x : ∀ _ : Fin P.n, LocalState P.n (ProcessRecord M) (Message M)}
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
    {u : ∀ _ : Fin P.n, LocalState P.n (ProcessRecord M) (Message M)}
    {w w' : NetworkState P.n (Message M)}
    (hn : NetworkStep P ldr w (Sum.inl (Sum.inl .tau)) (PMF.pure w')) :
    (brachaInstanceExtended P ldr M).step (u, w) (Sum.inl (Sum.inl .tau)) (PMF.pure (u, w')) := by
  rw [brachaInstanceExtended, System.parallel_step]
  exact Or.inr (Or.inr ⟨rfl, PMF.pure w', hn, (prodPMF_pure_pure _ _).symm⟩)

/-- A hidden rendezvous is a silent transition of the instance. -/
theorem brachaInstance_event_step (P : Parameters) (ldr : Fin P.n)
    {u x : ∀ _ : Fin P.n, LocalState P.n (ProcessRecord M) (Message M)}
    {w w' : NetworkState P.n (Message M)} (e : BroadcastEvent P.n M)
    (hall : ∀ i, ProgramStep P ldr i (u i) (Sum.inr e) (PMF.pure (x i)))
    (hn : NetworkStep P ldr w (Sum.inr e) (PMF.pure w')) :
    (brachaInstance P ldr M).step (u, w) (Sum.inl Label.tau) (PMF.pure (x, w')) :=
  (brachaInstance_step_iff P ldr _ _ _).mpr (Or.inl ⟨rfl, e,
    brachaInstanceExtended_event_step P ldr e hall hn⟩)

/-- A visible interface label is a transition of the instance. -/
theorem brachaInstance_label_step (P : Parameters) (ldr : Fin P.n)
    {u x : ∀ _ : Fin P.n, LocalState P.n (ProcessRecord M) (Message M)}
    {w w' : NetworkState P.n (Message M)} {l : InstanceLabel P.n M} (hl : l ≠ Sum.inl Label.tau)
    (hall : ∀ i, ProgramStep P ldr i (u i) (Sum.inl l) (PMF.pure (x i)))
    (hn : NetworkStep P ldr w (Sum.inl l) (PMF.pure w')) :
    (brachaInstance P ldr M).step (u, w) l (PMF.pure (x, w')) :=
  (brachaInstance_step_iff P ldr _ _ _).mpr (Or.inr (brachaInstanceExtended_label_step P ldr hl hall
    hn))

/-- A network-local injection is a silent transition of the instance. -/
theorem brachaInstance_tau_network (P : Parameters) (ldr : Fin P.n)
    {u : ∀ _ : Fin P.n, LocalState P.n (ProcessRecord M) (Message M)}
    {w w' : NetworkState P.n (Message M)}
    (hn : NetworkStep P ldr w (Sum.inl (Sum.inl .tau)) (PMF.pure w')) :
    (brachaInstance P ldr M).step (u, w) (Sum.inl Label.tau) (PMF.pure (u, w')) :=
  (brachaInstance_step_iff P ldr _ _ _).mpr (Or.inr (brachaInstanceExtended_tau_network P ldr hn))

/-- A visible transition of the programs beside the network: every program and
the network step on the label, and the joint distribution is their Dirac
product. -/
theorem brachaInstanceExtended_joint_inversion {P : Parameters} {ldr : Fin P.n}
    {u : ∀ _ : Fin P.n, LocalState P.n (ProcessRecord M) (Message M)}
    {w : NetworkState P.n (Message M)} {L : BroadcastLabel P.n M} {μ : PMF (BrachaState P.n M)}
    (hL : L ≠ (Silent.τ : BroadcastLabel P.n M))
    (h : (brachaInstanceExtended P ldr M).step (u, w) L μ) :
    ∃ (x : ∀ _ : Fin P.n, LocalState P.n (ProcessRecord M) (Message M))
    (w' : NetworkState P.n (Message M)), μ = PMF.pure (x, w') ∧
    (∀ i, ProgramStep P ldr i (u i) L (PMF.pure (x i))) ∧ NetworkStep P ldr w L (PMF.pure w') := by
  rw [brachaInstanceExtended, System.parallel_step] at h
  rcases h with ⟨-, μ₁, μ₂, hs, hn, rfl⟩ | ⟨hτ, -⟩ | ⟨hτ, -⟩
  · obtain ⟨x, rfl, hall⟩ := broadcastProgramProduct_inversion hs
    obtain ⟨w', rfl⟩ := networkStep_dirac hn
    exact ⟨x, w', prodPMF_pure_pure _ _, hall, hn⟩
  · exact absurd hτ hL
  · exact absurd hτ hL

/-- A silent transition of the programs beside the network is a network-local
injection: no program has a `τ` row. -/
theorem brachaInstanceExtended_tau_inversion {P : Parameters} {ldr : Fin P.n}
    {u : ∀ _ : Fin P.n, LocalState P.n (ProcessRecord M) (Message M)}
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

/-! ### One program's rules, by label class

Each lemma reads a row of the table off its label: the participant's row as its
guards together with the Dirac it produces, and the idle row of a
non-participant as the identity. The state and the distribution are variables,
so `cases` unifies against any state of the program. -/

section ProgramStepInversion
variable {P : Parameters} {ldr j : Fin P.n} {p : LocalState P.n (ProcessRecord M) (Message M)}
  {ν : PMF (LocalState P.n (ProcessRecord M) (Message M))}

theorem programStep_call_leader {m : M}
    (h : ProgramStep P ldr ldr p (Sum.inl (Sum.inl (.call m))) ν) :
    p.process.input = none ∧ ν = PMF.pure (p.setProcess { p.process with input := some m }) := by
  cases h
  case call => exact ⟨by assumption, rfl⟩
  case callIdle => exact absurd rfl ‹_ ≠ ldr›

theorem programStep_call_foreign {m : M} (hj : j ≠ ldr)
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
    2 * P.f + 1 ≤ p.receivedCount (.vote m) ∧ p.process.returned = false ∧
      ν = PMF.pure (p.setProcess { p.process with returned := true }) := by
  cases h
  case ret => exact ⟨by assumption, by assumption, rfl⟩
  case retIdle => exact absurd rfl ‹_ ≠ j›

theorem programStep_ret_foreign {i : Fin P.n} {m : M} (hi : i ≠ j)
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
    (Message.init m ∈ p.received ldr ∨ P.echoReceiptQuorum ≤ p.receivedCount (.echo m) ∨
        P.f + 1 ≤ p.receivedCount (.vote m)) ∧ p.process.sentEcho = none ∧
      ν = PMF.pure (p.setProcess { p.process with sentEcho := some m }) := by
  cases h
  case sendEcho => exact ⟨by assumption, by assumption, rfl⟩
  case sendIdle => exact absurd rfl ‹_ ≠ j›

theorem programStep_send_vote_own {m : M}
    (h : ProgramStep P ldr j p (Sum.inr (.send j (.vote m))) ν) :
    (P.echoReceiptQuorum ≤ p.receivedCount (.echo m) ∨ P.f + 1 ≤ p.receivedCount (.vote m)) ∧
      p.process.sentVote = none ∧
      ν = PMF.pure (p.setProcess { p.process with sentVote := some m }) := by
  cases h
  case sendVoteQuorum => exact ⟨Or.inl (by assumption), by assumption, rfl⟩
  case sendVoteAmplification => exact ⟨Or.inr (by assumption), by assumption, rfl⟩
  case sendIdle => exact absurd rfl ‹_ ≠ j›

theorem programStep_send_foreign {i : Fin P.n} {m : Message M} (hi : i ≠ j)
    (h : ProgramStep P ldr j p (Sum.inr (.send i m)) ν) : ν = PMF.pure p := by
  cases h
  case sendIdle => rfl
  all_goals exact absurd rfl hi

theorem programStep_deliver_own {k : Fin P.n} {m : Message M}
    (h : ProgramStep P ldr j p (Sum.inr (.deliver j k m)) ν) : ν = PMF.pure (p.deliverTo k m) := by
  cases h
  case deliverReceive => rfl
  case deliverIdle => exact absurd rfl ‹_ ≠ j›

theorem programStep_deliver_foreign {i k : Fin P.n} {m : Message M} (hi : i ≠ j)
    (h : ProgramStep P ldr j p (Sum.inr (.deliver i k m)) ν) : ν = PMF.pure p := by
  cases h
  case deliverReceive => exact absurd rfl hi
  case deliverIdle => rfl

end ProgramStepInversion
/-! ### The network's rules, by label class -/

section NetworkStepInversion
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

end NetworkStepInversion
/-! ### The write a row makes on the composed state

The local states and the network state are the two components of `BrachaState`
(`ABA/ReliableBroadcast/BrachaImplementation.lean`), so the instance and the rule table `BrachaStep`
run on the same state and every rule of the one is a rule of the other read in the
instance state's accessors. A joint step delivers a program function pointwise: its value at the
acting process, and its agreement with the old one elsewhere. A row of `BrachaStep` writes with
`InstanceState.setProcess`. The lemmas here identify the two. -/

section Writes

/-! ### The writes that leave the sent sets alone -/

section

variable {M : Type} {P : Parameters}
  {u x : ∀ _ : Fin P.n, LocalState P.n (ProcessRecord M) (Message M)}
  {w : NetworkState P.n (Message M)}

/-- A program function fixed at `j` and unchanged elsewhere is the old one
updated at `j`. -/
theorem programFunction_update {j : Fin P.n} {q : LocalState P.n (ProcessRecord M) (Message M)}
    (hj : x j = q) (hne : ∀ i, i ≠ j → x i = u i) : x = Function.update u j q := by
  funext i
  by_cases hi : i = j
  · subst hi; rw [hj, Function.update_self]
  · rw [hne i hi, Function.update_of_ne hi]

/-- A record write at one program, with the network state untouched. -/
theorem brachaInstance_setProcess {j : Fin P.n} {pr : ProcessRecord M}
    (hj : x j = (u j).setProcess pr) (hne : ∀ i, i ≠ j → x i = u i) :
    ((x, w) : BrachaState P.n M) = InstanceState.setProcess (u, w) j pr := by
  rw [programFunction_update hj hne]
  rfl

/-- The programs remain unchanged. -/
theorem brachaInstance_idle (hall : ∀ i, x i = u i) : ((x, w) : BrachaState P.n M) = (u, w) := by
  rw [funext hall]

/-- Corruption is the network state's own write (D1). -/
theorem brachaInstance_corrupt (k : Fin P.n) :
    ((u, w.corrupt P k) : BrachaState P.n M) = InstanceState.corrupt P k (u, w) := rfl

end

/-! ### The writes that record or deliver a message, and the program group's row -/

section

variable {M : Type} [DecidableEq M] {P : Parameters}
  {u x : ∀ _ : Fin P.n, LocalState P.n (ProcessRecord M) (Message M)}
  {w : NetworkState P.n (Message M)}

/-- A record write at one program together with the network state recording the
message that write multicasts. -/
theorem brachaInstance_setProcess_recordSent {j : Fin P.n} {pr : ProcessRecord M} {m : Message M}
    (hj : x j = (u j).setProcess pr) (hne : ∀ i, i ≠ j → x i = u i) :
    ((x, w.recordSent j m) : BrachaState P.n M) = (InstanceState.setProcess (u, w) j pr).multicast j
    m := by
  rw [programFunction_update hj hne]
  rfl

/-- A delivery: the receiver files the message under its sender's row. -/
theorem brachaInstance_deliver {i k : Fin P.n} {m : Message M}
    (hi : x i = (u i).deliverTo k m) (hne : ∀ i', i' ≠ i → x i' = u i') :
    ((x, w) : BrachaState P.n M) = InstanceState.receiveMessage (u, w) i k m := by
  rw [programFunction_update hi hne]
  rfl

/-- A Byzantine injection: the network state records a message under a
corrupted sender. -/
theorem brachaInstance_recordSent {k : Fin P.n} {m : Message M} :
    ((u, w.recordSent k m) : BrachaState P.n M) = InstanceState.multicast (u, w) k m := rfl

/-- The participant's row beside the idle rows of every other program is the
program group stepping into the updated function. -/
theorem programStep_update {ldr j : Fin P.n} {q : LocalState P.n (ProcessRecord M) (Message M)}
    {l : BroadcastLabel P.n M} (hj : ProgramStep P ldr j (u j) l (PMF.pure q))
    (hne : ∀ i, i ≠ j → ProgramStep P ldr i (u i) l (PMF.pure (u i))) :
    ∀ i, ProgramStep P ldr i (u i) l (PMF.pure (Function.update u j q i)) := by
  intro i
  by_cases hi : i = j
  · subst hi; rw [Function.update_self]; exact hj
  · rw [Function.update_of_ne hi]; exact hne i hi

end

end Writes
/-! ### The rows of the instance

Every transition of the instance is one row of `BrachaStep` at the same state,
and the correspondence is strong — one step answers one step, at the
specification label the interface label projects to, with no stuttering
anywhere:

| instance | row |
| --- | --- |
| `call` (leader writes, network records) | `BrachaStep.call` |
| `callLoop` | `BrachaStep.callLoop` |
| hidden `send` rendezvous, by level | `BrachaStep.echo` / `voteQuorum` / `voteAmplification` |
| hidden `deliver` rendezvous | `BrachaStep.deliver` |
| network-local injection | `BrachaStep.byzantine` |
| `ret` | `BrachaStep.ret` |
| `fail` | `BrachaStep.fail` |

The two hidden rendezvous and the network's injection are silent in both systems, and
`specificationLabelMap` takes `τ` to `τ`. -/

/-- **The projection.** -/
theorem brachaInstance_step_row (P : Parameters) (ldr : Fin P.n) :
    ∀ (s : BrachaState P.n M) (l : InstanceLabel P.n M) (μ : PMF (BrachaState P.n M)),
      (brachaInstance P ldr M).step s l μ →
      ∃ l₀, specificationLabelMap P.n M l = some l₀ ∧ BrachaStep P ldr s l₀ μ := by
  rintro ⟨u, w⟩ l μ hstep
  rcases (brachaInstance_step_iff P ldr (u, w) l μ).mp hstep with ⟨rfl, e, hev⟩ | hlab
  · -- a hidden rendezvous: an internal row
    obtain ⟨x, w', rfl, hall, hn⟩ := brachaInstanceExtended_joint_inversion (by simp) hev
    refine ⟨Label.tau, rfl, ?_⟩
    cases e with
    | send j m =>
      have hfor : ∀ i, i ≠ j → x i = u i :=
        fun i hi => PMF.pure_injective (programStep_send_foreign (Ne.symm hi) (hall i))
      have hw : w' = w.recordSent j m := PMF.pure_injective (networkStep_send hn)
      subst hw
      cases m with
      | init m => exact (programStep_send_init_own (hall j)).elim
      | echo m =>
        obtain ⟨hrecv, hsend, hx⟩ := programStep_send_echo_own (hall j)
        rw [brachaInstance_setProcess_recordSent (PMF.pure_injective hx) hfor]
        exact BrachaStep.echo _ j m hrecv hsend
      | vote m =>
        obtain ⟨hcnt, hsend, hx⟩ := programStep_send_vote_own (hall j)
        rw [brachaInstance_setProcess_recordSent (PMF.pure_injective hx) hfor]
        rcases hcnt with hq | ha
        · exact BrachaStep.voteQuorum _ j m hq hsend
        · exact BrachaStep.voteAmplification _ j m ha hsend
    | deliver i j m =>
      obtain ⟨hmem, hw⟩ := networkStep_deliver hn
      have hw' : w' = w := PMF.pure_injective hw
      subst hw'
      have hfor : ∀ i', i' ≠ i → x i' = u i' :=
        fun i' hi' => PMF.pure_injective (programStep_deliver_foreign (Ne.symm hi') (hall i'))
      rw [brachaInstance_deliver (PMF.pure_injective (programStep_deliver_own (hall i))) hfor]
      exact BrachaStep.deliver _ i j m hmem
  · by_cases hlτ : l = Sum.inl Label.tau
    · -- the network's own injection
      subst hlτ
      obtain ⟨w', rfl, hn⟩ := brachaInstanceExtended_tau_inversion hlab
      obtain ⟨j, m, hF, hw⟩ := networkStep_tau hn
      have hw' : w' = w.recordSent j m := PMF.pure_injective hw
      subst hw'
      refine ⟨Label.tau, rfl, ?_⟩
      rw [brachaInstance_recordSent]
      exact BrachaStep.byzantine _ j m hF
    · obtain ⟨x, w', rfl, hall, hn⟩ :=
        brachaInstanceExtended_joint_inversion (by simpa using hlτ) hlab
      cases l with
      | inl l₀ =>
        cases l₀ with
        | tau => exact absurd rfl hlτ
        | call m =>
          have hw : w' = w.recordSent ldr (.init m) := PMF.pure_injective (networkStep_call hn)
          subst hw
          obtain ⟨hin, hx⟩ := programStep_call_leader (hall ldr)
          have hfor : ∀ i, i ≠ ldr → x i = u i :=
            fun i hi => PMF.pure_injective (programStep_call_foreign hi (hall i))
          refine ⟨_, rfl, ?_⟩
          rw [brachaInstance_setProcess_recordSent (PMF.pure_injective hx) hfor]
          exact BrachaStep.call _ m hin
        | ret id m =>
          have hw : w' = w := PMF.pure_injective (networkStep_ret hn)
          subst hw
          obtain ⟨hcnt, hr, hx⟩ := programStep_ret_own (hall id)
          have hfor : ∀ i, i ≠ id → x i = u i :=
            fun i hi => PMF.pure_injective (programStep_ret_foreign (Ne.symm hi) (hall i))
          refine ⟨_, rfl, ?_⟩
          rw [brachaInstance_setProcess (PMF.pure_injective hx) hfor]
          exact BrachaStep.ret _ id m hcnt hr
        | fail id =>
          have hw : w' = w.corrupt P id := PMF.pure_injective (networkStep_fail hn)
          subst hw
          have hidle : ∀ i, x i = u i := fun i => PMF.pure_injective (programStep_fail (hall i))
          refine ⟨_, rfl, ?_⟩
          rw [brachaInstance_idle hidle, brachaInstance_corrupt]
          exact BrachaStep.fail _ id
      | inr e =>
        cases e with
        | callLoop m =>
          have hw : w' = w := PMF.pure_injective (networkStep_callLoop hn)
          subst hw
          have hidle : ∀ i, x i = u i := fun i => PMF.pure_injective (programStep_callLoop (hall i))
          refine ⟨_, rfl, ?_⟩
          rw [brachaInstance_idle hidle]
          exact BrachaStep.callLoop _ m

/-- **The embedding.** -/
theorem row_brachaInstance_step (P : Parameters) (ldr : Fin P.n) :
    ∀ (s : BrachaState P.n M) (l₀ : Label P.n M) (μ : PMF (BrachaState P.n M)),
      BrachaStep P ldr s l₀ μ →
      ∃ l, specificationLabelMap P.n M l = some l₀ ∧ (brachaInstance P ldr M).step s l μ := by
  rintro ⟨u, w⟩ l₀ μ hrow
  cases hrow with
  | call m h =>
    exact ⟨Sum.inl (.call m), rfl, brachaInstance_label_step P ldr (by simp)
      (programStep_update (ProgramStep.call (u ldr) m rfl h)
        (fun i hi => ProgramStep.callIdle (u i) m hi))
      (NetworkStep.call w m)⟩
  | callLoop m =>
    exact ⟨Sum.inr (.callLoop m), rfl, brachaInstance_label_step P ldr (by simp)
      (fun i => ProgramStep.callLoop (u i) m) (NetworkStep.callLoop w m)⟩
  | deliver i j m h =>
    exact ⟨Sum.inl Label.tau, rfl, brachaInstance_event_step P ldr (BroadcastEvent.deliver i j m)
      (programStep_update (ProgramStep.deliverReceive (u i) j m)
        (fun i' hi' => ProgramStep.deliverIdle (u i') i j m (Ne.symm hi')))
      (NetworkStep.deliver w i j m h)⟩
  | echo j m hrecv hsend =>
    exact ⟨Sum.inl Label.tau, rfl, brachaInstance_event_step P ldr (BroadcastEvent.send j (.echo m))
      (programStep_update (ProgramStep.sendEcho (u j) m hrecv hsend)
        (fun i hi => ProgramStep.sendIdle (u i) j (.echo m) (Ne.symm hi)))
      (NetworkStep.send w j (.echo m))⟩
  | voteQuorum j m hcnt hsend =>
    exact ⟨Sum.inl Label.tau, rfl, brachaInstance_event_step P ldr (BroadcastEvent.send j (.vote m))
      (programStep_update (ProgramStep.sendVoteQuorum (u j) m hcnt hsend)
        (fun i hi => ProgramStep.sendIdle (u i) j (.vote m) (Ne.symm hi)))
      (NetworkStep.send w j (.vote m))⟩
  | voteAmplification j m hcnt hsend =>
    exact ⟨Sum.inl Label.tau, rfl, brachaInstance_event_step P ldr (BroadcastEvent.send j (.vote m))
      (programStep_update (ProgramStep.sendVoteAmplification (u j) m hcnt hsend)
        (fun i hi => ProgramStep.sendIdle (u i) j (.vote m) (Ne.symm hi)))
      (NetworkStep.send w j (.vote m))⟩
  | byzantine j m h =>
    exact ⟨Sum.inl Label.tau, rfl, brachaInstance_tau_network P ldr (NetworkStep.byzantine w j m h)⟩
  | ret id m hcnt hr =>
    exact ⟨Sum.inl (.ret id m), rfl, brachaInstance_label_step P ldr (by simp)
      (programStep_update (ProgramStep.ret (u id) m hcnt hr)
        (fun i hi => ProgramStep.retIdle (u i) id m (Ne.symm hi)))
      (NetworkStep.retIdle w id m)⟩
  | fail id =>
    exact ⟨Sum.inl (.fail id), rfl, brachaInstance_label_step P ldr (by simp)
      (fun i => ProgramStep.failIdle (u i) id) (NetworkStep.fail w id)⟩

/-- **The row characterisation.** At a specification label `l₀`, the
transitions of the instance over the labels `specificationLabelMap` sends to `l₀` are
exactly the `l₀`-rows of `BrachaStep`, on the same state and with the same
distribution. The call and the call loop are the two rows of `call m`, taken at
the two labels `specificationLabelMap` sends to it; every other specification label has a
single interface label over it. -/
theorem brachaInstance_step_iff_row (P : Parameters) (ldr : Fin P.n) (s : BrachaState P.n M)
    (l₀ : Label P.n M) (μ : PMF (BrachaState P.n M)) :
    (∃ l, specificationLabelMap P.n M l = some l₀ ∧ (brachaInstance P ldr M).step s l μ) ↔
    BrachaStep P ldr s l₀ μ := by
  constructor
  · rintro ⟨l, hl, hstep⟩
    obtain ⟨l₁, hl₁, hrow⟩ := brachaInstance_step_row P ldr s l μ hstep
    have hll : l₁ = l₀ := Option.some.inj (show (some l₁ : Option (Label P.n M)) = some l₀ by
      rw [← hl₁, hl])
    subst hll
    exact hrow
  · exact row_brachaInstance_step P ldr s l₀ μ

/-- info: 'PLTS.ABA.BRB.brachaInstance_step_iff_row' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms brachaInstance_step_iff_row

end BRB
end ABA
end PLTS
