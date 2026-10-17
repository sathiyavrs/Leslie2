/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sathiya / Claude
-/

import Leslie2Protocols.ABA.AFW.System
import Leslie2Protocols.ABA.AFW.Composition
import Leslie2Protocols.ABA.Implementation.NetworkStateWritesAndRemovals
import Leslie2Protocols.ABA.Gather.AlgorithmOverBracha
import Leslie2Protocols.ABA.ReliableBroadcast.Bracha.RefinesSpecification
import Leslie2Protocols.Framework.FamilySimulation
import Leslie2Protocols.Framework.WeakTransitionsFromChains
import Leslie2Protocols.Framework.Congruence

/-!
# The projection of the gather-based protocol onto its composed system

`AFW.protocol P` is the gather-based protocol as it runs and `AFW.composed P` reads the same
protocol as a composition of components, with the broadcast instances beneath. This file holds two
of the three things the simulation between them rests on: the projection that computes a composed
round from the implementation, and the relation that projection carries. `ABA/AFW/Composition.lean`
holds the third, the builders that assemble a transition of the composed system out of transitions
of its components.

## The composed round is a projection of the implementation

A round of `composed P` is computed from a state of `protocol P` by `roundProjection`. Computing it
undoes the two rearrangements the implementation performs. The local states are transposed back: an
instance's local state vector at round `r` is computed from the variables the `n` processes hold in
that round. And the sent sets are recovered one tag at a time: an instance's network state carries
the messages of its own tag, computed from the adversary's single tagged sent family by
`AFW.messagesOf`. A round has `2n + 2` network states of messages: one for each gather, which
carries that gather's `ECHO`, `VOTE` and `BIND` messages, and one for each input-broadcast instance
of each gather. The untaggings are `AFW.firstGatherMessageOf` and `AFW.secondGatherMessageOf` for
the two gathers, and `firstGatherInputBroadcastMessageOf` and `secondGatherInputBroadcastMessageOf`
for the input-broadcast instances.

## What the broadcast instances returned

A gather program of the composed system holds what each input-broadcast instance has returned to
it, and so does the implementation: the round variables' two gather local states are over
`Gather.ProcessVariables`, which the instance's return writes. The projection is then the identity
on each local state, and the transposition and the untagging of the sent sets are all it performs.

## The ghost is the round's auxiliary state

The composed round holds four values no guard of a program reads: the core of each of its two
gather instances, and the round's network state, which is the first gather's core it has recorded
and whether the round has returned. In the implementation the network holds the ghost of the round
(`AFW.Ghost`): the first gather's core, the second gather's core and the bound bit. The projection
computes each gather's core and the recorded first core from the first two fields, and whether the
round has returned from whether the third field holds a bit: `AFW.ghostStep` writes the bit at the
round's first return, from the recorded first core (`networkProjection`). A transition's ghost write
is therefore the round's write of these values (`roundProjection_writeGhost`,
`roundProjection_writeGhost_ne`, `roundProjection_ghostId`).

## The relation

`ProtocolRelation` relates the round loops, the common coin, the ABA network, the rounds of the
family's map and every round of the family, in the shape of `ABDY.ProtocolRelation`. Its last three
conjuncts are invariants of the protocol state. At a round outside the started rounds no process
has sent, the ghost holds nothing and no process holds variables. Every process of the corrupted
set has a replaced program. `BoundInvariant` states what the projection needs of the ghost. A
process holding a round-`r` candidate has passed that round's first gather return, so the first
gather's core is recorded. At a process returned at round `r` the round's bound bit is recorded.
The recorded bit is the bit `GBCA.boundOfCore P C` of the recorded first core `C`. A process
holding a graded outcome has called the second gather, and a process that has called the second
gather holds a candidate. -/

namespace PLTS
namespace ABA
namespace AFW

open Implementation hiding NetworkEvent ExtendedLabel
open Composition GBCA.ByABDY

/-! ### The two broadcast untaggings

The two gather untaggings and their injectivity are `AFW.firstGatherMessageOf` and
`AFW.secondGatherMessageOf` of `ABA/AFW/System.lean`, where the adversary's ghost
write reads them. -/

variable {n : ℕ}

/-- The messages of input-broadcast instance `i` of the first gather. -/
def firstGatherInputBroadcastMessageOf (i : Fin n) : Message n → Option (BRB.Message Bool)
  | .firstGatherInputBroadcasts i' m => if i' = i then some m else none
  | _ => none

/-- The messages of input-broadcast instance `i` of the second gather. -/
def secondGatherInputBroadcastMessageOf (i : Fin n) : Message n → Option (BRB.Message (Option Bool))
  | .secondGatherInputBroadcasts i' m => if i' = i then some m else none
  | _ => none

theorem firstGatherInputBroadcastMessageOf_inj (i : Fin n) : ∀ a a' (b : BRB.Message Bool),
    b ∈ firstGatherInputBroadcastMessageOf i a → b ∈ firstGatherInputBroadcastMessageOf i a' → a =
      a' := by
  intro a a' b h h'
  cases a <;> cases a' <;> simp_all [firstGatherInputBroadcastMessageOf]

theorem secondGatherInputBroadcastMessageOf_inj (i : Fin n) :
    ∀ a a' (b : BRB.Message (Option Bool)), b ∈ secondGatherInputBroadcastMessageOf i a → b ∈
    secondGatherInputBroadcastMessageOf i a' → a = a' := by
  intro a a' b h h'
  cases a <;> cases a' <;> simp_all [secondGatherInputBroadcastMessageOf]

/-! ### The composed round, assembled -/

variable {P : Parameters}

/-- The round-`r` state of the first gather instance, computed from the implementation's state:
the local state vectors transposed out of the variables the processes hold in that round,
the network states recovered tag by tag from the adversary's tagged sent sets,
and the instance's core the first field of the adversary's ghost. -/
noncomputable def firstGatherProjection (P : Parameters) (u : ∀ _ : Fin P.n, AFW.ProcessVariables
  P.n)
    (w : NetworkState P.n) (r : ℕ) : Gather.StateOverBracha P.n Bool :=
  ((fun i => ((u i).2.roundVariables r).firstGather,
      ⟨⟨messagesOf firstGatherMessageOf firstGatherMessageOf_inj (w.sent r), w.F⟩,
        (w.ghost r).1⟩),
    fun k => (fun i => ((u i).2.roundVariables r).firstGatherInputBroadcasts k,
      ⟨messagesOf (firstGatherInputBroadcastMessageOf k) (firstGatherInputBroadcastMessageOf_inj k)
        (w.sent r), w.F⟩))

/-- The round-`r` state of the second gather instance, computed from the implementation's state,
its core the second field of the adversary's ghost. -/
noncomputable def secondGatherProjection (P : Parameters) (u : ∀ _ : Fin P.n, AFW.ProcessVariables
  P.n)
    (w : NetworkState P.n) (r : ℕ) : Gather.StateOverBracha P.n (Option Bool) :=
  ((fun i => ((u i).2.roundVariables r).secondGather,
      ⟨⟨messagesOf secondGatherMessageOf secondGatherMessageOf_inj (w.sent r), w.F⟩,
        (w.ghost r).2.1⟩),
    fun k => (fun i => ((u i).2.roundVariables r).secondGatherInputBroadcasts k,
      ⟨messagesOf (secondGatherInputBroadcastMessageOf k)
        (secondGatherInputBroadcastMessageOf_inj k) (w.sent r), w.F⟩))

/-- One process's variables in the round, computed from its round variables, field by field: the
first gather's input is the round's input, the candidate and the graded outcome are the two the
round variables hold, the second gather's input marks the second call, and the round has returned
exactly when its second gather has returned and the variables hold no graded outcome, which is the
state the round's own return leaves. -/
def programProjection {n : ℕ} (st : RoundVariables n) : GBCA.ByAFW.ProcessVariables n where
  input := st.firstGather.processVariables.input
  candidate := st.candidate
  secondGatherCalled := st.secondGather.processVariables.input.isSome
  output := st.output
  returned := st.secondGather.processVariables.returned && st.output.isNone

/-- The round's network state, computed from the ghost of the round: the recorded first gather's
core is the ghost's first field, and the round has returned exactly when the ghost holds the bound
bit, which `AFW.ghostStep` writes at the round's first return. -/
def networkProjection {n : ℕ} (G : Ghost n) : GBCA.ByAFW.NetworkState n :=
  ⟨G.1, G.2.2.isSome⟩

/-- The round-`r` state of the composed system, computed from the implementation's state: the
process variables beside the round's network state, and the two gather instances. -/
noncomputable def roundProjection (P : Parameters) (u : ∀ _ : Fin P.n, AFW.ProcessVariables P.n)
    (w : NetworkState P.n) (r : ℕ) : GBCA.ByAFW.RoundStateOverBracha P.n :=
  ((fun j => programProjection ((u j).2.roundVariables r), networkProjection (w.ghost r)),
    (firstGatherProjection P u w r, secondGatherProjection P u w r))

/-! ### The composed round's state computed from the projection -/

section Coordinates

variable (u : ∀ _ : Fin P.n, AFW.ProcessVariables P.n) (w : NetworkState P.n) (r : ℕ)

@[simp] theorem programs_roundProjection (j : Fin P.n) :
    GBCA.ByAFW.programs (roundProjection P u w r) j = programProjection ((u j).2.roundVariables r)
      :=
      rfl

@[simp] theorem network_roundProjection :
    GBCA.ByAFW.network (roundProjection P u w r) = networkProjection (w.ghost r) := rfl

@[simp] theorem firstGatherCore_networkProjection (G : Ghost P.n) :
    (networkProjection G).firstGatherCore = G.1 := rfl

@[simp] theorem returned_networkProjection (G : Ghost P.n) :
    (networkProjection G).returned = G.2.2.isSome := rfl

@[simp] theorem networkProjection_default :
    networkProjection ((none, none, none) : Ghost P.n) = GBCA.ByAFW.NetworkState.initial P.n :=
  rfl

@[simp] theorem firstGather_roundProjection : GBCA.ByAFW.firstGather (roundProjection P u w r) =
  firstGatherProjection P u w r := rfl

@[simp] theorem secondGather_roundProjection : GBCA.ByAFW.secondGather (roundProjection P u w r) =
  secondGatherProjection P u w r := rfl

@[simp] theorem core_firstGatherProjection : Gather.core (firstGatherProjection P u w r) =
  (w.ghost r).1 := rfl

@[simp] theorem core_secondGatherProjection : Gather.core (secondGatherProjection P u w r) =
  (w.ghost r).2.1 := rfl

@[simp] theorem gatherProgramsAndNetwork_firstGatherProjection_processVariables (i : Fin P.n) :
    (Gather.gatherProgramsAndNetwork (firstGatherProjection P u w r)).1 i
      = ((u i).2.roundVariables r).firstGather := rfl

@[simp] theorem gatherProgramsAndNetwork_secondGatherProjection_processVariables (i : Fin P.n) :
    (Gather.gatherProgramsAndNetwork (secondGatherProjection P u w r)).1 i
      = ((u i).2.roundVariables r).secondGather := rfl

@[simp] theorem gatherProgramsAndNetwork_firstGatherProjection_network :
    (Gather.gatherProgramsAndNetwork (firstGatherProjection P u w r)).2 = ⟨messagesOf
      firstGatherMessageOf
      firstGatherMessageOf_inj (w.sent r), w.F⟩ := rfl

@[simp] theorem gatherProgramsAndNetwork_secondGatherProjection_network :
    (Gather.gatherProgramsAndNetwork (secondGatherProjection P u w r)).2 = ⟨messagesOf
      secondGatherMessageOf
      secondGatherMessageOf_inj (w.sent r), w.F⟩ := rfl

@[simp] theorem inputBroadcasts_firstGatherProjection (k : Fin P.n) :
    Gather.inputBroadcasts (firstGatherProjection P u w r) k
      = ((fun i => (((u i).2.roundVariables r).firstGatherInputBroadcasts k)),
          ⟨messagesOf (firstGatherInputBroadcastMessageOf k) (firstGatherInputBroadcastMessageOf_inj
            k) (w.sent r), w.F⟩) := rfl

@[simp] theorem inputBroadcasts_secondGatherProjection (k : Fin P.n) :
    Gather.inputBroadcasts (secondGatherProjection P u w r) k
      = ((fun i => (((u i).2.roundVariables r).secondGatherInputBroadcasts k)),
          ⟨messagesOf (secondGatherInputBroadcastMessageOf k)
            (secondGatherInputBroadcastMessageOf_inj k) (w.sent r), w.F⟩) := rfl

/-- **The two systems of the first gather's core agree**: the instance's core
is computed from its network state alone, and that network state is the one
`AFW.firstGatherOf` computes from the adversary's state. -/
theorem coreOfNetwork_firstGatherProjection :
    Gather.coreOfNetwork P (Gather.gatherProgramsAndNetwork (firstGatherProjection P u w r)).2 =
      Gather.coreOf P
      (firstGatherOf P w r) :=
  (Gather.coreOf_eq_coreOfNetwork P (firstGatherOf P w r)).symm

/-- The same for the second gather's core. -/
theorem coreOfNetwork_secondGatherProjection :
    Gather.coreOfNetwork P (Gather.gatherProgramsAndNetwork (secondGatherProjection P u w r)).2 =
      Gather.coreOf P
      (secondGatherOf P w r) :=
  (Gather.coreOf_eq_coreOfNetwork P (secondGatherOf P w r)).symm

end Coordinates

/-! ### The ghost write

`AFW.ghostStep` writes each field of the ghost once: a recorded first core, second core or bound
bit stays recorded, and the recorded bit is the bound bit of the recorded first core. -/

section GhostStep

variable (L : Implementation.ExtendedLabel P.n (Message P.n) (RoundEvent P.n))
  (v : NetworkState P.n) (G : Ghost P.n)

/-- The ghost write at the first gather's return records the first gather's core where none is
recorded. -/
@[simp] theorem ghostStep_firstGatherReturn (r : ℕ) (j : Fin P.n) (x : Option Bool) :
    ghostStep P (Sum.inr (.gbcaRoundEvent r j (.firstGatherReturn x))) v G
      = (some (G.1.getD (Gather.coreOf P (firstGatherOf P v r))), G.2.1, G.2.2) := rfl

/-- The ghost write at the second gather's return records the second gather's core where none is
recorded. -/
@[simp] theorem ghostStep_secondGatherReturn (r : ℕ) (j : Fin P.n) (out : GBCAOutput) :
    ghostStep P (Sum.inr (.gbcaRoundEvent r j (.secondGatherReturn out))) v G
      = (G.1, some (G.2.1.getD (Gather.coreOf P (secondGatherOf P v r))), G.2.2) := rfl

/-- The ghost write at a graded return records the bound bit of the recorded first core where no
bit is recorded. -/
@[simp] theorem ghostStep_retG (r : ℕ) (j : Fin P.n) (out : GBCAOutput) :
    ghostStep P (Sum.inl (.retG r j out)) v G
      = (G.1, G.2.1, G.2.2.or (G.1.map (GBCA.boundOfCore P))) := rfl

/-- The ghost write never clears the first gather's recorded core. -/
theorem ghostStep_firstGatherCore (h : G.1 ≠ none) : (ghostStep P L v G).1 ≠ none := by
  unfold ghostStep
  split <;> simp_all

/-- The ghost write never clears a round's bound bit: `AFW.ghostStep` writes the third field at a
graded return alone, and keeps a recorded bit there. -/
theorem ghostStep_bound (h : G.2.2 ≠ none) : (ghostStep P L v G).2.2 ≠ none := by
  unfold ghostStep
  split <;> simp_all

/-- The ghost write keeps the recorded bit the bound bit of the recorded first core. -/
theorem ghostStep_boundOfCore
    (h : ∀ b, G.2.2 = some b → ∃ C, G.1 = some C ∧ b = GBCA.boundOfCore P C) :
    ∀ b, (ghostStep P L v G).2.2 = some b →
      ∃ C, (ghostStep P L v G).1 = some C ∧ b = GBCA.boundOfCore P C := by
  obtain ⟨G₁, G₂, G₃⟩ := G
  unfold ghostStep
  split
  · intro b hb
    obtain ⟨C, hC, rfl⟩ := h b hb
    change G₁ = some C at hC
    subst hC
    exact ⟨C, rfl, rfl⟩
  · exact h
  · intro b hb
    cases G₃ with
    | some b' => exact h b hb
    | none =>
      cases G₁ with
      | none => simp at hb
      | some C => exact ⟨C, rfl, by simpa using hb.symm⟩
  · exact h

/-- A ghost is the ghost write of the silent label applied to it. -/
theorem ghostStep_tau : ghostStep P (Sum.inl Label.tau) v G = G := rfl

/-- The round's network state after the ghost write at the first gather's return: the first
gather's core is recorded where none is recorded, as the round's network records it on the first
gather's announcement of that core. -/
theorem networkProjection_ghostStep_firstGatherReturn (r : ℕ) (j : Fin P.n) (x : Option Bool) :
    networkProjection (ghostStep P (Sum.inr (.gbcaRoundEvent r j (.firstGatherReturn x))) v G)
      = { networkProjection G with
          firstGatherCore := some ((networkProjection G).firstGatherCore.getD
            (Gather.coreOf P (firstGatherOf P v r))) } := rfl

/-- The round's network state after the ghost write at a graded return, at a ghost that records
the first gather's core: the round has returned. -/
theorem networkProjection_ghostStep_retG (r : ℕ) (j : Fin P.n) (out : GBCAOutput)
    (h : G.1 ≠ none) :
    networkProjection (ghostStep P (Sum.inl (.retG r j out)) v G)
      = { networkProjection G with returned := true } := by
  obtain ⟨G₁, G₂, G₃⟩ := G
  cases G₁ with
  | none => exact absurd rfl h
  | some C => cases G₃ <;> rfl

end GhostStep

/-! ### The ghost write, read through the projection

The adversary's ghost of round `r` is the round's two gather cores beside its bound bit, so a
transition's ghost write is the round's write of the two cores and of the round's network state.
The lemmas below are that write at the round the transition's label names, at every other round,
and at a transition whose write returns the ghost it found. -/

/-- **The ghost write at the round its label names**, read through the projection: the two cores
and the round's network state are computed from the written ghost, and every other coordinate is the
projection before the write. -/
theorem roundProjection_writeGhost (v : ∀ _ : Fin P.n, AFW.ProcessVariables P.n)
    (w : NetworkState P.n)
    {L : Implementation.ExtendedLabel P.n (Message P.n) (RoundEvent P.n)} {r : ℕ}
    (h : roundOf L = some r) :
    roundProjection P v (w.writeGhost (ghostStep P) L) r
      = ((fun j => programProjection ((v j).2.roundVariables r),
          networkProjection (ghostStep P L w (w.ghost r))),
        (Gather.setCore (firstGatherProjection P v w r) (ghostStep P L w (w.ghost r)).1,
          Gather.setCore (secondGatherProjection P v w r) (ghostStep P L w (w.ghost r)).2.1)) := by
  simp only [roundProjection, firstGatherProjection, secondGatherProjection, Gather.setCore,
    writeGhost_sent, writeGhost_F, writeGhost_ghost_self w h]

/-- The ghost write leaves every other round's projection where it stands. -/
theorem roundProjection_writeGhost_ne (v : ∀ _ : Fin P.n, AFW.ProcessVariables P.n)
    (w : NetworkState P.n)
    {L : Implementation.ExtendedLabel P.n (Message P.n) (RoundEvent P.n)} {r r' : ℕ}
    (h : roundOf L = some r) (hr : r' ≠ r) :
    roundProjection P v (w.writeGhost (ghostStep P) L) r' = roundProjection P v w r' := by
  simp only [roundProjection, firstGatherProjection, secondGatherProjection, writeGhost_sent,
    writeGhost_F, writeGhost_ghost_ne w h hr]

/-- A transition whose ghost write returns the ghost it found leaves the network's state where it
stands. -/
theorem writeGhost_ghostId
    (L : Implementation.ExtendedLabel P.n (Message P.n) (RoundEvent P.n))
    (h : ∀ (v : NetworkState P.n) (G : Ghost P.n), ghostStep P L v G = G)
    (w : NetworkState P.n) : w.writeGhost (ghostStep P) L = w :=
  writeGhost_of_ghostStep_unchanged w (fun r _ => h w (w.ghost r))

/-- A transition whose ghost write returns the ghost it found leaves every round's projection
where it stands. -/
theorem roundProjection_ghostId
    (L : Implementation.ExtendedLabel P.n (Message P.n) (RoundEvent P.n))
    (h : ∀ (v : NetworkState P.n) (G : Ghost P.n), ghostStep P L v G = G)
    (x : ∀ _ : Fin P.n, AFW.ProcessVariables P.n) (w : NetworkState P.n) (r' : ℕ) :
    roundProjection P x (w.writeGhost (ghostStep P) L) r' = roundProjection P x w r' := by
  rw [writeGhost_ghostId L h]

/-- The ghost of every round after the ghost write of a transition is the ghost write of some
label applied to the ghost before it: of the transition's own label at the round it names, and of
the silent label at every other round. -/
theorem ghost_writeGhost (w : NetworkState P.n)
    (L : Implementation.ExtendedLabel P.n (Message P.n) (RoundEvent P.n)) (r : ℕ) :
    ∃ (L' : Implementation.ExtendedLabel P.n (Message P.n) (RoundEvent P.n))
      (v : NetworkState P.n),
      (w.writeGhost (ghostStep P) L).ghost r = ghostStep P L' v (w.ghost r) := by
  cases hL : roundOf L with
  | none => exact ⟨Sum.inl Label.tau, w, by rw [writeGhost_of_round_none w hL]; rfl⟩
  | some r₀ =>
    by_cases hr : r = r₀
    · subst hr; exact ⟨L, w, writeGhost_ghost_self w hL⟩
    · exact ⟨Sum.inl Label.tau, w, by rw [writeGhost_ghost_ne w hL hr]; rfl⟩

/-- The same, from a network state whose ghosts are those of `w`: the ghost of every round after
the ghost write is the ghost write of some label applied to the ghost of `w`. -/
theorem ghost_writeGhost_of_eq {v w : NetworkState P.n} (hv : ∀ r, v.ghost r = w.ghost r)
    (L : Implementation.ExtendedLabel P.n (Message P.n) (RoundEvent P.n)) (r : ℕ) :
    ∃ (L' : Implementation.ExtendedLabel P.n (Message P.n) (RoundEvent P.n))
      (v' : NetworkState P.n),
      (v.writeGhost (ghostStep P) L).ghost r = ghostStep P L' v' (w.ghost r) := by
  obtain ⟨L', v', h⟩ := ghost_writeGhost v L r
  exact ⟨L', v', by rw [h, hv r]⟩

/-- A round's first gather's core, once recorded, stays recorded across any transition. -/
theorem writeGhost_firstGatherCore {w : NetworkState P.n}
    (L : Implementation.ExtendedLabel P.n (Message P.n) (RoundEvent P.n)) {r : ℕ}
    (h : (w.ghost r).1 ≠ none) : ((w.writeGhost (ghostStep P) L).ghost r).1 ≠ none := by
  obtain ⟨L', v, hv⟩ := ghost_writeGhost w L r
  rw [hv]
  exact ghostStep_firstGatherCore L' v _ h

/-- A round's bound bit, once recorded, stays recorded across any transition. -/
theorem writeGhost_bound {w : NetworkState P.n}
    (L : Implementation.ExtendedLabel P.n (Message P.n) (RoundEvent P.n)) {r : ℕ}
    (h : (w.ghost r).2.2 ≠ none) :
    ((w.writeGhost (ghostStep P) L).ghost r).2.2 ≠ none := by
  obtain ⟨L', v, hv⟩ := ghost_writeGhost w L r
  rw [hv]
  exact ghostStep_bound L' v _ h

/-! ### The projection at the initial state -/

/-- The empty sent family projects to the empty sent family. -/
theorem messagesOf_empty {β : Type} (f : Message n → Option β)
    (hf : ∀ a a' b, b ∈ f a → b ∈ f a' → a = a') :
    messagesOf f hf (fun _ => (∅ : Finset (Message n))) = fun _ => (∅ : Finset β) := by
  funext q
  simp [messagesOf]

/-- **Every round of the projection is the composed round's initial state**: an untouched round
reads as the initial variables in the implementation, the empty sent family projects to the empty
sent family, and the initial ghost to the initial network state of the round. -/
theorem roundProjection_init (P : Parameters) (r : ℕ) :
    roundProjection P (protocol P).init.1 (protocol P).init.2.1 r =
    (GBCA.ByAFW.roundOverBracha P r).init := by
  have hproc : (protocol P).init.1
      = fun _ => (RoundLoopVariables.initial P.n,
        Implementation.RoundVariablesMap.initial (RoundVariables P.n)) := rfl
  have hsent : ((protocol P).init.2.1).sent r = fun _ => (∅ : Finset (Message P.n)) := rfl
  have hF : ((protocol P).init.2.1).F = (∅ : Finset (Fin P.n)) := rfl
  have hghost : ((protocol P).init.2.1).ghost r = ((none, none, none) : Ghost P.n) := rfl
  rw [GBCA.ByAFW.roundOverBracha_init, roundProjection, firstGatherProjection,
    secondGatherProjection, hproc, hsent, hF, hghost, networkProjection_default]
  simp [Gather.instanceOverBracha_init, GBCA.ByAFW.ProcessVariables.initial, programProjection,
    RoundVariables.initial, Gather.NetworkState.initial, ABA.NetworkState.initial,
      BRB.BrachaState.initial,
    InstanceState.initial, messagesOf_empty]
  rfl

/-! ### The relation -/

/-- **The facts the projection needs of the round's ghost.** A process holding a round-`r`
candidate has passed that round's first gather return, whose ghost write records the first
gather's core. At a process returned at round `r`, whose second gather has returned and whose
variables hold no graded outcome, the round's bound bit is recorded, since the round's first
return writes it. The recorded bit is the bit `GBCA.boundOfCore P C` of the recorded first core
`C`. A process holding a graded outcome has called the second gather, and a process that has
called the second gather holds a candidate, by the guards of the two transitions that write them.
The round's network state is computed from the first core and the bit (`networkProjection`), and
these facts are what the round's return and its announcement ask of them. -/
structure BoundInvariant (P : Parameters) (u : ∀ _ : Fin P.n, AFW.ProcessVariables P.n)
    (w : NetworkState P.n) : Prop where
  /-- At a process holding a round-`r` candidate, the first gather's core of round `r` is
  recorded. -/
  firstGatherCore_of_candidate : ∀ (r : ℕ) (i : Fin P.n),
    ((u i).2.roundVariables r).candidate ≠ none → (w.ghost r).1 ≠ none
  /-- At a process returned at round `r`, the bound bit of round `r` is recorded. -/
  bound_of_returned : ∀ (r : ℕ) (i : Fin P.n),
    (((u i).2.roundVariables r).secondGather.processVariables).returned = true →
      ((u i).2.roundVariables r).output = none → (w.ghost r).2.2 ≠ none
  /-- The recorded bound bit of round `r` is the bound bit of the recorded first core. -/
  bound_eq_boundOfCore : ∀ (r : ℕ) (b : Bool), (w.ghost r).2.2 = some b →
    ∃ C, (w.ghost r).1 = some C ∧ b = GBCA.boundOfCore P C
  /-- A process holding a round-`r` graded outcome has called the second gather of round `r`. -/
  secondGatherInput_of_output : ∀ (r : ℕ) (i : Fin P.n),
    ((u i).2.roundVariables r).output ≠ none →
      (((u i).2.roundVariables r).secondGather.processVariables).input ≠ none
  /-- A process that has called the second gather of round `r` holds a round-`r` candidate. -/
  candidate_of_secondGatherInput : ∀ (r : ℕ) (i : Fin P.n),
    (((u i).2.roundVariables r).secondGather.processVariables).input ≠ none →
      ((u i).2.roundVariables r).candidate ≠ none

/-- At a process holding a round-`r` graded outcome, the first gather's core of round `r` is
recorded. -/
theorem BoundInvariant.firstGatherCore_of_output {u : ∀ _ : Fin P.n, AFW.ProcessVariables P.n}
    {w : NetworkState P.n} (hI : BoundInvariant P u w) {r : ℕ} {i : Fin P.n}
    (h : ((u i).2.roundVariables r).output ≠ none) : (w.ghost r).1 ≠ none :=
  hI.firstGatherCore_of_candidate r i
    (hI.candidate_of_secondGatherInput r i (hI.secondGatherInput_of_output r i h))

/-- **The announcement, read through the projection.** Where the ghost of round `r` holds the bit
`b`, the round's network state records a first gather's core `C` with `b = GBCA.boundOfCore P C`
and records the round's return, which is what the round's announcement asks. -/
theorem BoundInvariant.announceBound_networkProjection
    {u : ∀ _ : Fin P.n, AFW.ProcessVariables P.n} {w : NetworkState P.n}
    (hI : BoundInvariant P u w) {r : ℕ} {b : Bool} (h : (w.ghost r).2.2 = some b) :
    ∃ C, (networkProjection (w.ghost r)).firstGatherCore = some C ∧
      (networkProjection (w.ghost r)).returned = true ∧ b = GBCA.boundOfCore P C := by
  obtain ⟨C, hC, rfl⟩ := hI.bound_eq_boundOfCore r b h
  exact ⟨C, hC, by simp [networkProjection, h], rfl⟩

/-- **The relation of the protocol presentation to the composed one.** Writing `s = (u, w, o)`
and `t = (G, C, A, o')`, the eight conjuncts are: the round loops agree; the common coin is
shared; the ABA network is the network's DECIDED sets beside its corrupted set and its started
rounds; the rounds of the family's map are the started rounds; every round of the family is the
projection `roundProjection` of the implementation's state; at a round outside the started rounds
no process has sent, the ghost holds nothing and no process holds variables; every process of the
corrupted set has a replaced program (D23, D37); and `BoundInvariant` holds. The relation reads
the family through its accessor and its keys, and leaves the family's list of broadcasts free. -/
def ProtocolRelation (P : Parameters) (s : ProtocolState P) (t : ComposedState P) : Prop :=
  (∀ j, (s.1 j).1 = t.2.1 j) ∧
    s.2.2 = t.2.2.2 ∧
    t.2.2.1 = ⟨s.2.1.decidedSent, s.2.1.F, s.2.1.startedRounds⟩ ∧
    t.1.instanceMap.keys = s.2.1.startedRounds ∧
    (∀ r, t.1 r = roundProjection P s.1 s.2.1 r) ∧
    (∀ r ∉ s.2.1.startedRounds, (∀ j, s.2.1.sent r j = ∅) ∧
      s.2.1.ghost r = (none, none, none) ∧ ∀ j, r ∉ (s.1 j).2.roundVariablesMap) ∧
    (∀ j ∈ s.2.1.F, (s.1 j).1.corrupted = true) ∧
    BoundInvariant P s.1 s.2.1

/-- The relation, read at an explicit pair of states. -/
theorem protocolRelation_mk (P : Parameters) (u : ∀ _ : Fin P.n, AFW.ProcessVariables P.n)
    (w : NetworkState P.n) (o : InstanceFamilyState (WCC.SpecState.initial P.n) (WCC.failAct P))
    (G : RoundFamilyOverBrachaState P) (C : ∀ _ : Fin P.n, RoundLoopVariables P.n)
    (A : ABANetworkState P.n)
    (o' : InstanceFamilyState (WCC.SpecState.initial P.n) (WCC.failAct P)) :
    ProtocolRelation P (u, w, o) (G, C, A, o') ↔
      (∀ j, (u j).1 = C j) ∧ o = o' ∧ A = ⟨w.decidedSent, w.F, w.startedRounds⟩ ∧
        G.instanceMap.keys = w.startedRounds ∧ (∀ r, G r = roundProjection P u w r) ∧
        (∀ r ∉ w.startedRounds, (∀ j, w.sent r j = ∅) ∧ w.ghost r = (none, none, none) ∧
          ∀ j, r ∉ (u j).2.roundVariablesMap) ∧
        (∀ j ∈ w.F, (u j).1.corrupted = true) ∧ BoundInvariant P u w :=
  Iff.rfl

/-- The initial states are related: every round of the projection is the composed round's initial
state, no round is started and none is in the family's map, and no field the bound invariant reads
is written. -/
theorem protocolRelation_init (P : Parameters) :
    ProtocolRelation P (protocol P).init (composed P).init :=
  ⟨fun _ => rfl, rfl, rfl, rfl, fun r => (roundProjection_init P r).symm,
    fun _ _ => ⟨fun _ => rfl, rfl, fun _ => Finmap.notMem_empty⟩,
    fun _ hj => absurd hj (Finset.notMem_empty _),
    ⟨fun _ _ h => absurd rfl h, fun _ _ h => absurd h Bool.false_ne_true,
      fun _ _ h => (Option.some_ne_none _ h.symm).elim, fun _ _ h => absurd rfl h,
      fun _ _ h => absurd rfl h⟩⟩

/-! ### The bound invariant across a transition

Every transition writes the ghost of a round through `AFW.ghostStep` or leaves it, so after a
transition the ghost of every round is a ghost write applied to the ghost before it
(`ghost_writeGhost`), which keeps the three facts the invariant states of the ghost alone. The
four fields of the round variables the invariant reads are written by four transitions: the first
gather's return writes the candidate, the second gather's call its input, the second gather's
return the graded outcome and the return flag, and the round's return clears the graded outcome.
The lemmas below carry the invariant across a transition that leaves the four fields, across a
write of the second gather's input, and across a write of one process's variables of one round. -/

section BoundInvariantPreservation

variable {u x : ∀ _ : Fin P.n, AFW.ProcessVariables P.n} {w v : NetworkState P.n}

/-- The three facts the bound invariant states of the ghost alone, after a transition whose ghost
of every round is a ghost write applied to the ghost before it. -/
private theorem boundInvariant_ghost (hI : BoundInvariant P u w)
    (hghost : ∀ r, ∃ (L : Implementation.ExtendedLabel P.n (Message P.n) (RoundEvent P.n))
      (v' : NetworkState P.n), v.ghost r = ghostStep P L v' (w.ghost r)) :
    (∀ r, (w.ghost r).1 ≠ none → (v.ghost r).1 ≠ none) ∧
      (∀ r, (w.ghost r).2.2 ≠ none → (v.ghost r).2.2 ≠ none) ∧
      ∀ (r : ℕ) (b : Bool), (v.ghost r).2.2 = some b →
        ∃ C, (v.ghost r).1 = some C ∧ b = GBCA.boundOfCore P C := by
  refine ⟨fun r h => ?_, fun r h => ?_, fun r => ?_⟩ <;> obtain ⟨L, v', hv⟩ := hghost r <;>
    rw [hv]
  · exact ghostStep_firstGatherCore L v' _ h
  · exact ghostStep_bound L v' _ h
  · exact ghostStep_boundOfCore L v' _ (hI.bound_eq_boundOfCore r)

/-- **The bound invariant across a transition that leaves the four fields it reads**: the
candidate, the second gather's input and return flag and the graded outcome of every round stand,
and the ghost of every round after the transition is a ghost write applied to the ghost before
it. -/
theorem boundInvariant_of (hI : BoundInvariant P u w)
    (hcand : ∀ i r, ((x i).2.roundVariables r).candidate = ((u i).2.roundVariables r).candidate)
    (hinput : ∀ i r, (((x i).2.roundVariables r).secondGather.processVariables).input
      = (((u i).2.roundVariables r).secondGather.processVariables).input)
    (hreturned : ∀ i r, (((x i).2.roundVariables r).secondGather.processVariables).returned
      = (((u i).2.roundVariables r).secondGather.processVariables).returned)
    (hout : ∀ i r, ((x i).2.roundVariables r).output = ((u i).2.roundVariables r).output)
    (hghost : ∀ r, ∃ (L : Implementation.ExtendedLabel P.n (Message P.n) (RoundEvent P.n))
      (v' : NetworkState P.n), v.ghost r = ghostStep P L v' (w.ghost r)) :
    BoundInvariant P x v := by
  obtain ⟨hfirst, hbound, hcore⟩ := boundInvariant_ghost hI hghost
  refine ⟨fun r i h => hfirst r (hI.firstGatherCore_of_candidate r i (by rwa [← hcand i r])),
    fun r i hr ho => hbound r (hI.bound_of_returned r i (by rwa [← hreturned i r])
      (by rwa [← hout i r])),
    hcore, fun r i h => ?_, fun r i h => ?_⟩
  · rw [hinput i r]; exact hI.secondGatherInput_of_output r i (by rwa [← hout i r])
  · rw [hcand i r]; exact hI.candidate_of_secondGatherInput r i (by rwa [← hinput i r])

/-- The bound invariant across a transition whose round variables of every process and every
round stand. -/
theorem boundInvariant_of_roundVariables (hI : BoundInvariant P u w)
    (hst : ∀ i r, (x i).2.roundVariables r = (u i).2.roundVariables r)
    (hghost : ∀ r, ∃ (L : Implementation.ExtendedLabel P.n (Message P.n) (RoundEvent P.n))
      (v' : NetworkState P.n), v.ghost r = ghostStep P L v' (w.ghost r)) :
    BoundInvariant P x v :=
  boundInvariant_of hI (fun i r => by rw [hst i r]) (fun i r => by rw [hst i r])
    (fun i r => by rw [hst i r]) (fun i r => by rw [hst i r]) hghost

/-- The bound invariant across the second gather's call: the candidate, the second gather's
return flag and the graded outcome stand, and at every round the second gather's input either
stands or is written at variables whose candidate is recorded. -/
theorem boundInvariant_ofSecondGatherCall (hI : BoundInvariant P u w)
    (hcand : ∀ i r, ((x i).2.roundVariables r).candidate = ((u i).2.roundVariables r).candidate)
    (hreturned : ∀ i r, (((x i).2.roundVariables r).secondGather.processVariables).returned
      = (((u i).2.roundVariables r).secondGather.processVariables).returned)
    (hout : ∀ i r, ((x i).2.roundVariables r).output = ((u i).2.roundVariables r).output)
    (hinput : ∀ i r, (((x i).2.roundVariables r).secondGather.processVariables).input
        = (((u i).2.roundVariables r).secondGather.processVariables).input ∨
      ((((x i).2.roundVariables r).secondGather.processVariables).input ≠ none ∧
        ((u i).2.roundVariables r).candidate ≠ none))
    (hghost : ∀ r, ∃ (L : Implementation.ExtendedLabel P.n (Message P.n) (RoundEvent P.n))
      (v' : NetworkState P.n), v.ghost r = ghostStep P L v' (w.ghost r)) :
    BoundInvariant P x v := by
  obtain ⟨hfirst, hbound, hcore⟩ := boundInvariant_ghost hI hghost
  refine ⟨fun r i h => hfirst r (hI.firstGatherCore_of_candidate r i (by rwa [← hcand i r])),
    fun r i hr ho => hbound r (hI.bound_of_returned r i (by rwa [← hreturned i r])
      (by rwa [← hout i r])),
    hcore, fun r i h => ?_, fun r i h => ?_⟩ <;> rcases hinput i r with heq | ⟨hne, hc⟩
  · rw [heq]; exact hI.secondGatherInput_of_output r i (by rwa [← hout i r])
  · exact hne
  · rw [hcand i r]; exact hI.candidate_of_secondGatherInput r i (by rwa [← heq])
  · rw [hcand i r]; exact hc

/-- **The bound invariant across a write of one process's variables of one round**: process `j`
writes its round-loop variables and its variables of round `r`, the ghost of every round after the
transition is a ghost write applied to the ghost before it, and the written variables meet the
four facts the invariant states of a process against the ghost of round `r` after the
transition. -/
theorem boundInvariant_update {j : Fin P.n} {p : RoundVariablesMap P.n}
    (hI : BoundInvariant P u w) (hu : (u j).2 = p) (c' : RoundLoopVariables P.n) (r : ℕ)
    (sr : RoundVariables P.n)
    (hghost : ∀ r', ∃ (L : Implementation.ExtendedLabel P.n (Message P.n) (RoundEvent P.n))
      (v' : NetworkState P.n), v.ghost r' = ghostStep P L v' (w.ghost r'))
    (hcand : sr.candidate ≠ none → (v.ghost r).1 ≠ none)
    (hreturned : sr.secondGather.processVariables.returned = true → sr.output = none →
      (v.ghost r).2.2 ≠ none)
    (hout : sr.output ≠ none → sr.secondGather.processVariables.input ≠ none)
    (hinput : sr.secondGather.processVariables.input ≠ none → sr.candidate ≠ none) :
    BoundInvariant P (Function.update u j (c', p.setRoundVariables r sr)) v := by
  obtain ⟨hfirst, hbound, hcore⟩ := boundInvariant_ghost hI hghost
  have hst : ∀ i r', ¬ (i = j ∧ r' = r) →
      ((Function.update u j (c', p.setRoundVariables r sr) i).2.roundVariables r')
        = (u i).2.roundVariables r' := by
    intro i r' h
    by_cases hi : i = j
    · subst hi
      have hr : r' ≠ r := fun hr => h ⟨rfl, hr⟩
      rw [Function.update_self, ← hu]
      exact Implementation.RoundVariablesMap.roundVariables_setRoundVariables_ne _ _ _ hr
    · rw [Function.update_of_ne hi]
  have hself : (Function.update u j (c', p.setRoundVariables r sr) j).2.roundVariables r = sr := by
    rw [Function.update_self]
    exact Implementation.RoundVariablesMap.roundVariables_setRoundVariables_self _ _ _
  refine ⟨fun r' i h => ?_, fun r' i hr ho => ?_, hcore, fun r' i h => ?_, fun r' i h => ?_⟩ <;>
    by_cases hp : i = j ∧ r' = r
  · obtain ⟨rfl, rfl⟩ := hp; rw [hself] at h; exact hcand h
  · rw [hst i r' hp] at h; exact hfirst r' (hI.firstGatherCore_of_candidate r' i h)
  · obtain ⟨rfl, rfl⟩ := hp; rw [hself] at hr ho; exact hreturned hr ho
  · rw [hst i r' hp] at hr ho; exact hbound r' (hI.bound_of_returned r' i hr ho)
  · obtain ⟨rfl, rfl⟩ := hp; rw [hself] at h ⊢; exact hout h
  · rw [hst i r' hp] at h ⊢; exact hI.secondGatherInput_of_output r' i h
  · obtain ⟨rfl, rfl⟩ := hp; rw [hself] at h ⊢; exact hinput h
  · rw [hst i r' hp] at h ⊢; exact hI.candidate_of_secondGatherInput r' i h

end BoundInvariantPreservation

end AFW

end ABA
end PLTS
