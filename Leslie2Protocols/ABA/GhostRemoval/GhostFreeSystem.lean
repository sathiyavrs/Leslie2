/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sathiya / Claude
-/

import Leslie2Protocols.ABA.Implementation.NetworkStateWritesAndRemovals
import Leslie2Protocols.Framework.AuxiliaryVariableRemoval

/-!
# Removing the implementation's ghost

The network of the implementation holds one auxiliary variable that no program reads: the ghost
`NetworkState.ghost` of every round, written by `ghostStep`. One transition reads it, the
announcement `NetworkStep.announceBound`, which fires with the bit `ghostBound` reads from the
ghost of its round (D29). This file removes the ghost.

The system left by the removal is `systemGhostFree`, the implementation at the one-element ghost
`Unit`, with the write `fun _ _ _ => ()` and `ghostBound := fun _ => none`. Its programs, its common
coin and its network transitions are those of the implementation, and its network never
announces. The removal is an `AuxiliaryVariableRemoval` (`Framework/AuxiliaryVariableRemoval.lean`)
along the projection

  `forgetGhostState = Prod.map id (Prod.map NetworkState.forgetGhost id)`

at the identity on labels.

The announcements `boundG r b` are the one label that carries a value of the ghost, and at the
network they form the set `K` of the removal, `announcementLabels`. A transition on one of them
leaves the projection where it stands, since the ghost write leaves the state with the ghost
removed where it stands (`Implementation.forgetGhost_writeGhost`). Every other transition is the
transition of the same name of the ghost-free network at the state with the ghost removed, its
guards reading the message record, the DECIDED sets, the corrupted set and the started rounds
alone. Over `Unit` the ghost write is the identity (`Implementation.writeGhost_unit`), so every
transition of the ghost-free network lifts to the transition of the same name.

The pipeline of `Implementation/System.lean` carries the removal from the network to the
implementation. The congruences for parallel composition ask each neighbour to be saturated along
the identity, which every system is (`System.labelSaturated_id`), and to be idle on the announcement
labels. Every program is idle on them (`programStep_boundG`), and so is the common coin, since an
announcement belongs to no coin round and is not a corruption. The composition hides the
synchronisation labels and then the labels of the two sub-protocol interfaces, `Label.hiddenAPI`,
which contains `boundG r b`. The removal at the implementation therefore has the empty set as its
`K`, and `system_ghostRemoval` is an equality of achievable trace distributions.
-/

namespace PLTS
namespace ABA
namespace Implementation

/-! ### The ghost-free system -/

section GhostFreeSystem
variable (P : Parameters) (M E S : Type) [DecidableEq M]
    (roundStep : Fin P.n → ProcessVariables P.n S → ExtendedLabel P.n M E → PMF (ProcessVariables
      P.n S) →
      Prop)

/-- The network of the ghost-free system: the network's transitions at the one-element ghost,
which holds no bit, so that the announcement never fires. -/
noncomputable def networkGhostFree : System (NetworkState P.n M Unit) (ExtendedLabel P.n M E) :=
  network P M E Unit (fun _ _ _ => ()) (fun _ => none)

/-- **The ghost-free system**: the implementation at the one-element ghost, whose network holds
no bit and never announces. -/
noncomputable def systemGhostFree : System (State P M S Unit) (Label P.n) :=
  system P M E S Unit roundStep (fun _ _ _ => ()) (fun _ => none)

end GhostFreeSystem

/-! ### The projection and the announcement labels -/

section Labels

variable {n : ℕ} {M E : Type}

/-- The projection of the implementation's state: the process family and the common coin
stand, and the network's ghost is removed. -/
def forgetGhostState {P : Parameters} {S G : Type} :
    State P M S G → State P M S Unit :=
  Prod.map id (Prod.map NetworkState.forgetGhost id)

/-- The announcement labels: the announcements `boundG r b` of a round's bound bit, the labels
of the one transition of the network that reads the ghost (D29). -/
def announcementLabels (n : ℕ) {M E : Type} : Set (ExtendedLabel n M E) :=
  {l | ∃ (r : ℕ) (b : Bool), l = Sum.inl (Label.boundG r b)}

@[simp] theorem boundG_mem_announcementLabels (r : ℕ) (b : Bool) :
    (Sum.inl (Label.boundG r b) : ExtendedLabel n M E) ∈ announcementLabels n :=
  ⟨r, b, rfl⟩

@[simp] theorem tau_notMem_announcementLabels :
    (Silent.τ : ExtendedLabel n M E) ∉ announcementLabels n := by
  rintro ⟨r, b, h⟩
  simp at h

/-- Every announcement label lies in `Label.hiddenAPI`, so hiding the synchronisation labels and
then `Label.hiddenAPI` leaves no announcement label. -/
theorem announcementLabels_hidden :
    (Sum.inl ⁻¹' (announcementLabels (M := M) (E := E) n \ networkEventLabels n)) \
      Label.hiddenAPI n = ∅ := by
  ext l
  simp only [Set.mem_diff, Set.mem_preimage, Set.mem_empty_iff_false, iff_false]
  rintro ⟨⟨⟨r, b, h⟩, -⟩, hl⟩
  cases Sum.inl_injective h
  exact hl (Label.boundG_mem_hiddenAPI r b)

end Labels

/-! ### The ghost removal at the network

The network is the one component whose state carries the ghost, and the announcement is the one
transition that reads it. -/

section NetworkRemoval
variable {P : Parameters} {M E G : Type} [DecidableEq M] [Inhabited G]
    {ghostStep : ExtendedLabel P.n M E → NetworkState P.n M G → G → G}
    {ghostBound : G → Option Bool}

/-- Over the one-element ghost the successor of a transition is the state its ghost write starts
from, so a transition written with its ghost write is a transition written without it. -/
private theorem networkStepGhostFree_of_writeGhost {s t : NetworkState P.n M Unit}
    {L : ExtendedLabel P.n M E}
    (h : NetworkStep P M E Unit (fun _ _ _ => ()) (fun _ => none) s L
      (PMF.pure (t.writeGhost (fun _ _ _ => ()) L))) :
    NetworkStep P M E Unit (fun _ _ _ => ()) (fun _ => none) s L (PMF.pure t) := by
  rwa [writeGhost_unit] at h

/-- **The network's ghost can be removed.** `NetworkState.forgetGhost` is an auxiliary-variable
removal of the network onto the network of the ghost-free system, at the identity on labels and
with the announcement labels as its set `K`.

A transition on an announcement label leaves the projection where it stands, its successor being
the ghost write of the state it leaves. Every other transition keeps its guards under the removal,
its guards reading the message record, the DECIDED sets, the corrupted set and the started
rounds alone, and its successor is its own successor with the ghost removed. The lift matches a
transition of the ghost-free network by the transition of the same name at the state that holds
the ghost; the announcement of the ghost-free network has the guard `none = some b`, so it never
fires. -/
theorem network_ghostRemoval :
    AuxiliaryVariableRemoval (network P M E G ghostStep ghostBound)
      (networkGhostFree P M E) NetworkState.forgetGhost id (announcementLabels P.n) where
  init := rfl
  silent := separatesSilent_id
  projectUnchanged := by
    rintro s l μ ⟨r, b, rfl⟩ h
    obtain ⟨-, rfl⟩ := networkStep_announceBound h
    rw [PMF.pure_map, forgetGhost_writeGhost]
  project := by
    intro s l μ hl h
    refine Or.inl ?_
    simp only [networkGhostFree, network_step]
    simp only [network_step] at h
    cases h with
    | gbcaSend r j m =>
      rw [PMF.pure_map, forgetGhost_writeGhost, forgetGhost_recordGBCASend]
      exact networkStepGhostFree_of_writeGhost (NetworkStep.gbcaSend _ r j m)
    | gbcaDeliver r i j m hm =>
      rw [PMF.pure_map, forgetGhost_writeGhost]
      exact networkStepGhostFree_of_writeGhost (NetworkStep.gbcaDeliver _ r i j m hm)
    | decidedRelay j b =>
      rw [PMF.pure_map, forgetGhost_writeGhost, forgetGhost_recordDecided]
      exact networkStepGhostFree_of_writeGhost (NetworkStep.decidedRelay _ j b)
    | decidedDeliver i j b hb =>
      rw [PMF.pure_map, forgetGhost_writeGhost]
      exact networkStepGhostFree_of_writeGhost (NetworkStep.decidedDeliver _ i j b hb)
    | decidedSend j b =>
      rw [PMF.pure_map, forgetGhost_writeGhost, forgetGhost_recordDecided]
      exact networkStepGhostFree_of_writeGhost (NetworkStep.decidedSend _ j b)
    | gbcaRoundEvent r j e =>
      rw [PMF.pure_map, forgetGhost_writeGhost]
      exact networkStepGhostFree_of_writeGhost (NetworkStep.gbcaRoundEvent _ r j e)
    | byzantineCallG r k b hF hr =>
      rw [PMF.pure_map, forgetGhost_writeGhost]
      exact networkStepGhostFree_of_writeGhost (NetworkStep.byzantineCallG _ r k b hF hr)
    | byzantineCallW r k hF hr =>
      rw [PMF.pure_map, forgetGhost_writeGhost]
      exact networkStepGhostFree_of_writeGhost (NetworkStep.byzantineCallW _ r k hF hr)
    | callABAIdle id b =>
      rw [PMF.pure_map, forgetGhost_writeGhost]
      exact networkStepGhostFree_of_writeGhost (NetworkStep.callABAIdle _ id b)
    | retABAIdle id b =>
      rw [PMF.pure_map, forgetGhost_writeGhost]
      exact networkStepGhostFree_of_writeGhost (NetworkStep.retABAIdle _ id b)
    | callG r id b =>
      rw [PMF.pure_map, forgetGhost_writeGhost, forgetGhost_recordStartedRound]
      exact networkStepGhostFree_of_writeGhost (NetworkStep.callG _ r id b)
    | retG r id out =>
      rw [PMF.pure_map, forgetGhost_writeGhost]
      exact networkStepGhostFree_of_writeGhost (NetworkStep.retG _ r id out)
    | announceBound r b _ => exact absurd (boundG_mem_announcementLabels r b) hl
    | callWIdle r id =>
      rw [PMF.pure_map, forgetGhost_writeGhost]
      exact networkStepGhostFree_of_writeGhost (NetworkStep.callWIdle _ r id)
    | retWIdle r id c =>
      rw [PMF.pure_map, forgetGhost_writeGhost]
      exact networkStepGhostFree_of_writeGhost (NetworkStep.retWIdle _ r id c)
    | fail k hnew hbud =>
      rw [PMF.pure_map, forgetGhost_writeGhost, forgetGhost_corrupt]
      exact networkStepGhostFree_of_writeGhost (NetworkStep.fail _ k hnew hbud)
    | byzantineGBCA r k m hF hr =>
      rw [PMF.pure_map, forgetGhost_writeGhost, forgetGhost_recordGBCASend]
      exact networkStepGhostFree_of_writeGhost (NetworkStep.byzantineGBCA _ r k m hF hr)
    | byzantineDecided k b hF =>
      rw [PMF.pure_map, forgetGhost_writeGhost, forgetGhost_recordDecided]
      exact networkStepGhostFree_of_writeGhost (NetworkStep.byzantineDecided _ k b hF)
  lift := by
    intro s l μ h
    simp only [networkGhostFree, network_step] at h
    simp only [network_step]
    cases h with
    | gbcaSend r j m =>
      exact ⟨_, _, rfl, NetworkStep.gbcaSend s r j m, by simp [PMF.pure_map]⟩
    | gbcaDeliver r i j m hm =>
      exact ⟨_, _, rfl, NetworkStep.gbcaDeliver s r i j m hm, by simp [PMF.pure_map]⟩
    | decidedRelay j b =>
      exact ⟨_, _, rfl, NetworkStep.decidedRelay s j b, by simp [PMF.pure_map]⟩
    | decidedDeliver i j b hb =>
      exact ⟨_, _, rfl, NetworkStep.decidedDeliver s i j b hb, by simp [PMF.pure_map]⟩
    | decidedSend j b =>
      exact ⟨_, _, rfl, NetworkStep.decidedSend s j b, by simp [PMF.pure_map]⟩
    | gbcaRoundEvent r j e =>
      exact ⟨_, _, rfl, NetworkStep.gbcaRoundEvent s r j e, by simp [PMF.pure_map]⟩
    | byzantineCallG r k b hF hr =>
      exact ⟨_, _, rfl, NetworkStep.byzantineCallG s r k b hF hr, by simp [PMF.pure_map]⟩
    | byzantineCallW r k hF hr =>
      exact ⟨_, _, rfl, NetworkStep.byzantineCallW s r k hF hr, by simp [PMF.pure_map]⟩
    | callABAIdle id b =>
      exact ⟨_, _, rfl, NetworkStep.callABAIdle s id b, by simp [PMF.pure_map]⟩
    | retABAIdle id b =>
      exact ⟨_, _, rfl, NetworkStep.retABAIdle s id b, by simp [PMF.pure_map]⟩
    | callG r id b =>
      exact ⟨_, _, rfl, NetworkStep.callG s r id b, by simp [PMF.pure_map]⟩
    | retG r id out =>
      exact ⟨_, _, rfl, NetworkStep.retG s r id out, by simp [PMF.pure_map]⟩
    | announceBound r b hb => exact absurd hb (by simp)
    | callWIdle r id =>
      exact ⟨_, _, rfl, NetworkStep.callWIdle s r id, by simp [PMF.pure_map]⟩
    | retWIdle r id c =>
      exact ⟨_, _, rfl, NetworkStep.retWIdle s r id c, by simp [PMF.pure_map]⟩
    | fail k hnew hbud =>
      exact ⟨_, _, rfl, NetworkStep.fail s k hnew hbud, by simp [PMF.pure_map]⟩
    | byzantineGBCA r k m hF hr =>
      exact ⟨_, _, rfl, NetworkStep.byzantineGBCA s r k m hF hr, by simp [PMF.pure_map]⟩
    | byzantineDecided k b hF =>
      exact ⟨_, _, rfl, NetworkStep.byzantineDecided s k b hF, by simp [PMF.pure_map]⟩

end NetworkRemoval

/-! ### The neighbours of the network

The network sits in the composition beside the process group and the common coin. Each is a
neighbour of the removal: saturated along the identity, which every system is, and idle on the
announcement labels. -/

section Neighbours

variable (P : Parameters) (M E S : Type)
    (roundStep : Fin P.n → ProcessVariables P.n S → ExtendedLabel P.n M E → PMF (ProcessVariables
      P.n S) →
      Prop)

/-- **Every program is idle on the announcement labels.** A round transition carries a label of
`roundOwn j`, which no announcement is, and the program's two transitions on an announcement,
`boundGIdle` and `corruptedIdle`, leave its state where it stands. -/
theorem program_idleOn [IsRoundStep P M E S roundStep] (j : Fin P.n) :
    (program P M E S roundStep j).IdleOn (announcementLabels P.n) := by
  rintro q l μ ⟨r, b, rfl⟩ hstep
  exact programStep_boundG hstep

/-- **The common coin is idle on the announcement labels.** The pullback `coinLabelMap` carries an
announcement to the same label of the shared alphabet, which belongs to no coin round and is not a
corruption, so the coin's family takes it on its idle transition alone. -/
theorem coinOverExtendedAlphabet_idleOn :
    (coinOverExtendedAlphabet P M E).IdleOn (announcementLabels P.n) := by
  refine System.IdleOn.mapIdle (K := {l | ∃ (r : ℕ) (b : Bool), l = Label.boundG r b}) ?_ ?_
  · rintro o l μ ⟨r, b, rfl⟩ hstep
    rw [WCC.specFamily, System.family_step_iff] at hstep
    rcases hstep with ⟨hτ, -⟩ | ⟨r', hown, -⟩ | ⟨-, -, hfail, -⟩ | ⟨-, -, -, rfl⟩
    · exact absurd hτ (by simp)
    · exact absurd hown (by simp)
    · exact absurd hfail (by simp [Label.isFail])
    · rfl
  · rintro l ⟨r, b, rfl⟩ m hm
    simp only [coinLabelMap_inl, Option.some.injEq] at hm
    exact ⟨r, b, hm.symm⟩

end Neighbours

/-! ### The ghost removal at the implementation -/

section SystemRemoval

variable (P : Parameters) (M E S G : Type) [DecidableEq M] [Inhabited G]
    (roundStep : Fin P.n → ProcessVariables P.n S → ExtendedLabel P.n M E → PMF (ProcessVariables
      P.n S) →
      Prop)
    [IsRoundStep P M E S roundStep]
    (ghostStep : ExtendedLabel P.n M E → NetworkState P.n M G → G → G)
    (ghostBound : G → Option Bool)

/-- **The implementation's ghost can be removed.** The network's removal is carried through the
composition pipeline by four congruences: parallel composition beside the common coin, parallel
composition beside the process group, abstraction of the synchronisation labels, and restriction
along the extended alphabet. Hiding `Label.hiddenAPI` then removes every announcement label from
the set `K`, so the removal at the implementation has the empty set as its `K`. -/
theorem system_auxiliaryVariableRemoval :
    AuxiliaryVariableRemoval (system P M E S G roundStep ghostStep ghostBound)
      (systemGhostFree P M E S roundStep) forgetGhostState id ∅ := by
  have hextended :=
    ((network_ghostRemoval (P := P) (M := M) (E := E) (ghostStep := ghostStep)
      (ghostBound := ghostBound)).parallel_right
      (coinOverExtendedAlphabet P M E).labelSaturated_id
      (coinOverExtendedAlphabet_idleOn P M E)).parallel_left
      (System.synchronisedProduct (program P M E S roundStep)).labelSaturated_id
      (System.IdleOn.synchronisedProduct (program_idleOn P M E S roundStep))
  have habstract := hextended.abstract (networkEventLabels P.n)
    (fun _ _ h => Iff.of_eq (congrArg (· ∈ networkEventLabels P.n) h))
    (fun h => tau_notMem_announcementLabels h.1)
  rw [← Sum.map_id_id] at habstract
  have hsystem := habstract.relabel.abstract (Label.hiddenAPI P.n)
    (fun _ _ h => Iff.of_eq (congrArg (· ∈ Label.hiddenAPI P.n) h))
    (fun h => tau_notMem_announcementLabels (n := P.n) (M := M) (E := E) h.1.1)
  rw [announcementLabels_hidden] at hsystem
  exact hsystem

/-- **The ghost changes no trace distribution.** The ghost enables the announcement and no other
transition, and the announcement is hidden at protocol level, so the implementation and the
ghost-free system achieve the same trace distributions. -/
theorem system_ghostRemoval :
    achievableTraceDists (system P M E S G roundStep ghostStep ghostBound) =
      achievableTraceDists (systemGhostFree P M E S roundStep) :=
  (system_auxiliaryVariableRemoval P M E S G roundStep ghostStep ghostBound).achievableTraceDists_eq
    fun _ hl => absurd hl (Set.notMem_empty _)

end SystemRemoval

/-! ### Mechanical axiom check -/

/-- info: 'PLTS.ABA.Implementation.system_ghostRemoval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms system_ghostRemoval

end Implementation
end ABA
end PLTS
