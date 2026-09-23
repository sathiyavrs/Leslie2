/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sathiya / Claude
-/

import Leslie2Protocols.ABA.GBCA.ABDY.Components
import Leslie2Protocols.Framework.FamilySimulation
import Leslie2Protocols.Framework.LoopsAndInstanceFamilies

/-!
# The round's graded-agreement instance, composed

`GBCA.ByABDY.composition`: one round of the protocol, assembled from the components of
`ABA/GBCA/ABDY/Components.lean` — the `n` corruption-blind local programs beside the round's own
network. `compositionExtended` is the programs synchronised and put in parallel with the network
over the instance-internal alphabet; `composition` hides the two rendezvous there and reads the
result back over the shared extended alphabet `ExtendedLabel n`. The instance is the unit the
analysis replaces by the graded-agreement specification, so its interface is exactly what that
replacement may see: the round's handshake ports `callG r`, `retG r`, `gbcaCallLoop r` and the
three Byzantine graded-agreement labels of round `r`, and nothing else.

`gbcaInstanceFamily` is the ℕ-indexed family of these instances: `System.family` routes a
round-tagged label to its round, takes `τ` at any round, and broadcasts `fail` to every round at
once. It is built from three functions on the shared extended alphabet. `roundOwnsLabel` gives the
round a label of the interface belongs to, and `none` at every other label — the ABA API, the coin
ports, `fail`, the DECIDED sets and the round rendezvous of the protocol network. `isFailLabel`
picks out the one label every round takes at once. `corruptionAct` is the broadcast corruption act
on an instance state: the round's network state records it and the round records do not (D1).

## Determinacy

Every transition of a local program and of the round's network is Dirac, so the instance and its
family are LTS: the probabilistic transition of the protocol is the coin resolution, which is not
part of a graded-agreement round. No program moves on `τ` either, so the silent transitions of the
instance are exactly the network's injections and the hidden rendezvous.

## Reading and building instance transitions

The pipeline is `relabel ∘ abstract ∘ parallel ∘ synchronisedProduct`. `composition_step_iff`
unfolds it once and for all, into the hidden-rendezvous case and the shared-label case, and
`gbcaProgramProduct_inversion` reads a synchronised transition of the program group back as one
transition per process. In the other direction `composition_event_step`, `composition_label_step`
and `composition_tau_network` build a transition of the instance from the program and network
transitions it is made of.
-/

namespace PLTS
namespace ABA
namespace GBCA.ByABDY

open Implementation Composition

/-- The programs beside the network, over the instance-internal alphabet. -/
noncomputable def compositionExtended (P : Parameters) (r : ℕ) :
    System (GBCA.ByABDY.RoundState P.n) (GBCALabel P.n) :=
  (System.synchronisedProduct (gbcaProgram P r)).parallel (GBCANetwork P r)

/-- **The round-`r` instance**: the programs beside the network, the two
rendezvous hidden, the result read back over the shared extended alphabet. Its
interface is the round's ports — `callG r`, `retG r`, `gbcaCallLoop r` and the
three Byzantine graded-agreement labels of round `r`. -/
noncomputable def composition (P : Parameters) (r : ℕ) :
    System (GBCA.ByABDY.RoundState P.n) (ExtendedLabel P.n) :=
  ((compositionExtended P r).abstract (gbcaEvents P.n)).relabel

/-- The round a label of the instance interface belongs to. Every other label of the shared extended
alphabet — the ABA API, the coin ports, `fail`, the DECIDED sets, and the round rendezvous of the
protocol network — is owned by no round. -/
def roundOwnsLabel {n : ℕ} : ExtendedLabel n → Option ℕ
  | Sum.inl (.callG r _ _) => some r
  | Sum.inl (.retG r _ _ _) => some r
  | Sum.inr (.gbcaCallLoop r _ _) => some r
  | Sum.inr (.byzantineCallG r _ _) => some r
  | Sum.inr (.byzantineCallGLoop r _ _) => some r
  | Sum.inr (.byzantineRetG r _ _ _) => some r
  | _ => none

/-- Corruption is the one label every round takes at once. -/
def isFailLabel {n : ℕ} : ExtendedLabel n → Prop
  | Sum.inl (.fail _) => True
  | _ => False

instance {n : ℕ} : DecidablePred (isFailLabel (n := n)) := fun l => by
  cases l with
  | inl l => cases l <;> simp only [isFailLabel] <;> infer_instance
  | inr e => cases e <;> simp only [isFailLabel] <;> infer_instance

/-- The broadcast corruption act on an instance state: the round's network state records it, the
round records do not (D1). -/
def corruptionAct (P : Parameters) : ExtendedLabel P.n → GBCA.ByABDY.RoundState P.n →
  GBCA.ByABDY.RoundState P.n
  | Sum.inl (.fail k), (u, w) => (u, w.corrupt P k)
  | _, s => s

/-- **The graded-agreement family of the protocol**: the ℕ-indexed family of round instances. A
round-tagged label moves its round alone, `τ` moves one round, and `fail` is the broadcast that
keeps every round's copy of the corrupted set together. -/
noncomputable def gbcaInstanceFamily (P : Parameters) :
    System (ℕ → GBCA.ByABDY.RoundState P.n) (ExtendedLabel P.n) :=
  System.family (composition P) roundOwnsLabel isFailLabel (corruptionAct P)

/-! ### Determinacy

Every transition of a local program and of the round's network
(`ABA/GBCA/ABDY/Components.lean`) is Dirac, so the instance and its family are
LTS: the probabilistic transition of the protocol is the coin
resolution, which is not part of a graded-agreement round. -/

/-- Every program transition is Dirac. -/
theorem gbcaProgramStep_dirac {P : Parameters} {r : ℕ} {j : Fin P.n}
    {p : GBCA.ByABDY.RoundRecord P.n} {l : GBCALabel P.n} {ν : PMF (GBCA.ByABDY.RoundRecord P.n)}
    (h : GBCAProgramStep P r j p l ν) : ∃ p', ν = PMF.pure p' := by
  cases h <;> exact ⟨_, rfl⟩

/-- Every network transition is Dirac. -/
theorem gbcaNetworkStep_dirac {P : Parameters} {r : ℕ} {w : NetworkState P.n} {l : GBCALabel P.n}
    {μ : PMF (NetworkState P.n)} (h : GBCANetworkStep P r w l μ) :
    ∃ w', μ = PMF.pure w' := by
  cases h <;> exact ⟨_, rfl⟩

/-- A local program is an LTS. -/
theorem gbcaProgram_isLTS (P : Parameters) (r : ℕ) (j : Fin P.n) :
    (gbcaProgram P r j).IsLTS :=
  fun _ _ _ h => gbcaProgramStep_dirac h

/-- The network is an LTS. -/
theorem GBCANetwork_isLTS (P : Parameters) (r : ℕ) : (GBCANetwork P r).IsLTS :=
  fun _ _ _ h => gbcaNetworkStep_dirac h

/-- The synchronised group of programs is an LTS. -/
theorem gbcaProgramProduct_isLTS (P : Parameters) (r : ℕ) :
    (System.synchronisedProduct (gbcaProgram P r)).IsLTS :=
  System.synchronisedProduct_isLTS (gbcaProgram_isLTS P r)

/-- The programs beside the network form an LTS. -/
theorem compositionExtended_isLTS (P : Parameters) (r : ℕ) : (compositionExtended P r).IsLTS :=
  System.parallel_isLTS (gbcaProgramProduct_isLTS P r) (GBCANetwork_isLTS P r)

/-- The instance is an LTS. -/
theorem composition_isLTS (P : Parameters) (r : ℕ) : (composition P r).IsLTS :=
  System.relabel_isLTS (System.abstract_isLTS (compositionExtended_isLTS P r) _)

/-- The family of instances is an LTS. -/
theorem gbcaInstanceFamily_isLTS (P : Parameters) : (gbcaInstanceFamily P).IsLTS :=
  System.family_isLTS (composition_isLTS P) roundOwnsLabel isFailLabel (corruptionAct P)

/-- No program transition fires on `τ`: a program only ever moves in a rendezvous or
on one of the round's ports. The instance's silent transitions are therefore
exactly the network's injections and the hidden rendezvous. -/
theorem gbcaProgramStep_no_tau {P : Parameters} {r : ℕ} {j : Fin P.n}
    {p : GBCA.ByABDY.RoundRecord P.n} {ν : PMF (GBCA.ByABDY.RoundRecord P.n)}
    (h : GBCAProgramStep P r j p (Silent.τ : GBCALabel P.n) ν) : False := by
  rw [gbcaLabel_tau] at h; cases h

/-! ### Reading and building instance transitions

The pipeline is `relabel ∘ abstract ∘ parallel ∘ synchronisedProduct`; the lemmas
below unfold it once and for all, in both directions. -/

/-- A synchronised transition of the program group on a visible label: every
program steps, and the joint distribution is Dirac. -/
theorem gbcaProgramProduct_inversion {P : Parameters} {r : ℕ}
    {u : ∀ _ : Fin P.n, GBCA.ByABDY.RoundRecord P.n} {l : GBCALabel P.n}
    {μ : PMF (∀ _ : Fin P.n, GBCA.ByABDY.RoundRecord P.n)}
    (h : (System.synchronisedProduct (gbcaProgram P r)).step u l μ) :
    ∃ x : ∀ _ : Fin P.n, GBCA.ByABDY.RoundRecord P.n, μ = PMF.pure x ∧ ∀ i, GBCAProgramStep P r i
    (u i) l (PMF.pure (x i)) := by
  rw [System.synchronisedProduct_step] at h
  rcases h with ⟨-, μ_, hall, rfl⟩ | ⟨rfl, i, μ_i, hstep, -⟩
  · have hx : ∀ i, ∃ p', μ_ i = PMF.pure p' := fun i => gbcaProgramStep_dirac (hall i)
    choose x hx using hx
    refine ⟨x, ?_, fun i => ?_⟩
    · rw [show μ_ = fun i => PMF.pure (x i) from funext hx]
      exact piPMF_pure x
    · rw [← hx i]; exact hall i
  · exact absurd hstep gbcaProgramStep_no_tau

/-- Build a synchronised transition of the program group from per-process
Dirac steps. -/
theorem gbcaProgramProduct_pure {P : Parameters} {r : ℕ}
    {u x : ∀ _ : Fin P.n, GBCA.ByABDY.RoundRecord P.n} {l : GBCALabel P.n}
    (hl : l ≠ Silent.τ)
    (h : ∀ i, GBCAProgramStep P r i (u i) l (PMF.pure (x i))) :
    (System.synchronisedProduct (gbcaProgram P r)).step u l (PMF.pure x) := by
  rw [System.synchronisedProduct_step]
  exact Or.inl ⟨hl, fun i => PMF.pure (x i), h, (piPMF_pure x).symm⟩

/-- The program group has no silent transition: no program has a `τ` transition. -/
theorem gbcaProgramProduct_no_tau {P : Parameters} {r : ℕ}
    {u : ∀ _ : Fin P.n, GBCA.ByABDY.RoundRecord P.n}
    {μ : PMF (∀ _ : Fin P.n, GBCA.ByABDY.RoundRecord P.n)}
    (h : (System.synchronisedProduct (gbcaProgram P r)).step u (Silent.τ : GBCALabel P.n) μ) :
    False := by
  rcases h with ⟨hτ, -⟩ | ⟨-, i, μ_i, hstep, -⟩
  · exact hτ rfl
  · exact gbcaProgramStep_no_tau hstep

/-- The instance's step relation, unfolded to the hidden-rendezvous case and
the shared-label case. -/
theorem composition_step_iff (P : Parameters) (r : ℕ) (q : GBCA.ByABDY.RoundState P.n)
    (l : ExtendedLabel P.n) (μ : PMF (GBCA.ByABDY.RoundState P.n)) :
    (composition P r).step q l μ ↔
    (l = Sum.inl Label.tau ∧ ∃ e : GBCAEvent P.n, (compositionExtended P r).step q (Sum.inr e) μ) ∨
    (compositionExtended P r).step q (Sum.inl l) μ := by
  constructor
  · rintro (⟨hτ, l', ⟨e, rfl⟩, hstep⟩ | ⟨-, hstep⟩)
    · exact Or.inl ⟨Sum.inl_injective hτ, e, hstep⟩
    · exact Or.inr hstep
  · rintro (⟨rfl, e, hstep⟩ | hstep)
    · exact Or.inl ⟨rfl, _, inr_mem_gbcaEvents e, hstep⟩
    · exact Or.inr ⟨inl_notMem_gbcaEvents l, hstep⟩

/-- Build a joint transition of the programs and the network on a rendezvous
label. -/
theorem compositionExtended_event_step (P : Parameters) (r : ℕ)
    {u x : ∀ _ : Fin P.n, GBCA.ByABDY.RoundRecord P.n} {w w' : NetworkState P.n}
    (e : GBCAEvent P.n)
    (hall : ∀ i, GBCAProgramStep P r i (u i) (Sum.inr e) (PMF.pure (x i)))
    (hn : GBCANetworkStep P r w (Sum.inr e) (PMF.pure w')) :
    (compositionExtended P r).step (u, w) (Sum.inr e) (PMF.pure (x, w')) := by
  rw [compositionExtended, System.parallel_step]
  exact Or.inl ⟨by simp, PMF.pure x, PMF.pure w', gbcaProgramProduct_pure (by simp) hall, hn,
    (prodPMF_pure_pure _ _).symm⟩

/-- Build a joint transition of the programs and the network on a visible
shared label. -/
theorem compositionExtended_label_step (P : Parameters) (r : ℕ)
    {u x : ∀ _ : Fin P.n, GBCA.ByABDY.RoundRecord P.n} {w w' : NetworkState P.n}
    {l : ExtendedLabel P.n} (hl : l ≠ Sum.inl Label.tau)
    (hall : ∀ i, GBCAProgramStep P r i (u i) (Sum.inl l) (PMF.pure (x i)))
    (hn : GBCANetworkStep P r w (Sum.inl l) (PMF.pure w')) :
    (compositionExtended P r).step (u, w) (Sum.inl l) (PMF.pure (x, w')) := by
  have hne : (Sum.inl l : GBCALabel P.n) ≠ Silent.τ := by
    rw [gbcaLabel_tau]; simpa using hl
  rw [compositionExtended, System.parallel_step]
  exact Or.inl ⟨hne, PMF.pure x, PMF.pure w', gbcaProgramProduct_pure hne hall, hn,
    (prodPMF_pure_pure _ _).symm⟩

/-- Build a silent transition of the programs and the network from a
network-local one. -/
theorem compositionExtended_tau_network (P : Parameters) (r : ℕ)
    {u : ∀ _ : Fin P.n, GBCA.ByABDY.RoundRecord P.n} {w w' : NetworkState P.n}
    (hn : GBCANetworkStep P r w (Sum.inl (Sum.inl .tau)) (PMF.pure w')) :
    (compositionExtended P r).step (u, w) (Sum.inl (Sum.inl .tau)) (PMF.pure (u, w')) := by
  rw [compositionExtended, System.parallel_step]
  exact Or.inr (Or.inr ⟨rfl, PMF.pure w', hn, (prodPMF_pure_pure _ _).symm⟩)

/-- A hidden rendezvous is a silent transition of the instance. -/
theorem composition_event_step (P : Parameters) (r : ℕ)
    {u x : ∀ _ : Fin P.n, GBCA.ByABDY.RoundRecord P.n} {w w' : NetworkState P.n}
    (e : GBCAEvent P.n)
    (hall : ∀ i, GBCAProgramStep P r i (u i) (Sum.inr e) (PMF.pure (x i)))
    (hn : GBCANetworkStep P r w (Sum.inr e) (PMF.pure w')) :
    (composition P r).step (u, w) (Sum.inl Label.tau) (PMF.pure (x, w')) :=
  (composition_step_iff P r _ _ _).mpr
    (Or.inl ⟨rfl, e, compositionExtended_event_step P r e hall hn⟩)

/-- A visible shared label is a transition of the instance. -/
theorem composition_label_step (P : Parameters) (r : ℕ)
    {u x : ∀ _ : Fin P.n, GBCA.ByABDY.RoundRecord P.n} {w w' : NetworkState P.n}
    {l : ExtendedLabel P.n} (hl : l ≠ Sum.inl Label.tau)
    (hall : ∀ i, GBCAProgramStep P r i (u i) (Sum.inl l) (PMF.pure (x i)))
    (hn : GBCANetworkStep P r w (Sum.inl l) (PMF.pure w')) :
    (composition P r).step (u, w) l (PMF.pure (x, w')) :=
  (composition_step_iff P r _ _ _).mpr (Or.inr (compositionExtended_label_step P r hl hall hn))

/-- A network-local injection is a silent transition of the instance. -/
theorem composition_tau_network (P : Parameters) (r : ℕ)
    {u : ∀ _ : Fin P.n, GBCA.ByABDY.RoundRecord P.n} {w w' : NetworkState P.n}
    (hn : GBCANetworkStep P r w (Sum.inl (Sum.inl .tau)) (PMF.pure w')) :
    (composition P r).step (u, w) (Sum.inl Label.tau) (PMF.pure (u, w')) :=
  (composition_step_iff P r _ _ _).mpr (Or.inr (compositionExtended_tau_network P r hn))

end GBCA.ByABDY
end ABA
end PLTS
