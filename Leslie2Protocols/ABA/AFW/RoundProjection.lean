/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sathiya / Claude
-/

import Leslie2Protocols.ABA.AFW.System
import Leslie2Protocols.ABA.AFW.Composition
import Leslie2Protocols.ABA.Gather.AlgorithmOverBracha
import Leslie2Protocols.ABA.ReliableBroadcast.Bracha.RefinesSpecification
import Leslie2Protocols.Framework.FamilySimulation
import Leslie2Protocols.Framework.WeakTransitionsFromChains
import Leslie2Protocols.Framework.Congruence

/-!
# The view of the gather-based protocol in its composed system

`AFW.protocol P` is the gather-based protocol as it runs and `AFW.composed P` reads the same
protocol as a composition of components, down to the broadcast instances. This file holds two of
the three things the simulation between them rests on: the view that computes a composed state from
the implementation, and the relation that view carries. `ABA/AFW/Composition.lean` holds the third,
the builders that assemble a transition of the composed system out of transitions of its
components.

## The composed state is a view of the implementation

A state of `composed P` is computed from a state of `protocol P`. The round loops and the coin
oracle are shared objects, the ABA network is the DECIDED sets beside the corrupted set, and the
round-`r` state is assembled by `roundProjection`. Assembling it undoes the two rearrangements the
implementation performs. The local states are transposed back: an instance's local state vector at
round `r` is read off the round records the `n` processes hold. And the sent sets are recovered one
tag at a time: an instance's network state carries the messages of its own tag, read off the
adversary's single tagged sent family by `AFW.messagesOf`.

## What the broadcast instances returned

A gather program of the composed system holds two records of what each broadcast instance has
returned to it, and so does the implementation: the round record's two gather local states are
over `Gather.ProcessRecord`, which the instance's return writes. The projection is then the
identity on each local state, and the transposition and the untagging of the sent sets are all it
performs.

## The ghost record is the round's auxiliary state

The round carries three fields no guard of it reads: the core of each of its
two gather instances, and the round's bound bit. In the implementation the network
holds those three as the ghost record of the round (`AFW.Ghost`), so the view
reads them off it, and a transition's ghost write is the round's write of them
(`roundProjection_writeGhost`, `roundProjection_writeGhost_ne`, `roundProjection_ghostId`). The two
projections of a gather's core agree because each is `Gather.coreOf` of the same
network state (`coreOfNetwork_firstGatherProjection`, `coreOfNetwork_secondGatherProjection`).

## The clause that is not a projection

`BoundInvariant` says that a process holding a round-`r` candidate has passed that round's first
gather return, so the round's bound bit is on record, and that a graded outcome on record reaches a
candidate on record through the two fields between them. -/

namespace PLTS
namespace ABA
namespace AFW

open Implementation hiding NetworkEvent ExtendedLabel
open Composition GBCA.ByABDY

/-! ### The four broadcast untaggings

The two gather untaggings and their injectivity are `AFW.firstGatherMessageOf` and
`AFW.secondGatherMessageOf` of `ABA/AFW/System.lean`, where the adversary's ghost
write reads them. -/

variable {n : ℕ}

/-- The messages of input-broadcast instance `i` of the first gather. -/
def firstGatherInputBroadcastMessageOf (i : Fin n) : Message n → Option (BRB.Message Bool)
  | .firstGatherInputBroadcasts i' m => if i' = i then some m else none
  | _ => none

/-- The messages of bind-broadcast instance `i` of the first gather. -/
def firstGatherBindBroadcastMessageOf (i : Fin n) : Message n → Option (BRB.Message
  (Gather.AcceptedPairs n Bool))
  | .firstGatherBindBroadcasts i' m => if i' = i then some m else none
  | _ => none

/-- The messages of input-broadcast instance `i` of the second gather. -/
def secondGatherInputBroadcastMessageOf (i : Fin n) : Message n → Option (BRB.Message (Option Bool))
  | .secondGatherInputBroadcasts i' m => if i' = i then some m else none
  | _ => none

/-- The messages of bind-broadcast instance `i` of the second gather. -/
def secondGatherBindBroadcastMessageOf (i : Fin n) : Message n → Option (BRB.Message
  (Gather.AcceptedPairs n (Option Bool)))
  | .secondGatherBindBroadcasts i' m => if i' = i then some m else none
  | _ => none

theorem firstGatherInputBroadcastMessageOf_inj (i : Fin n) : ∀ a a' (b : BRB.Message Bool),
    b ∈ firstGatherInputBroadcastMessageOf i a → b ∈ firstGatherInputBroadcastMessageOf i a' → a =
      a' := by
  intro a a' b h h'
  cases a <;> cases a' <;> simp_all [firstGatherInputBroadcastMessageOf]

theorem firstGatherBindBroadcastMessageOf_inj (i : Fin n) :
    ∀ a a' (b : BRB.Message (Gather.AcceptedPairs n Bool)), b ∈ firstGatherBindBroadcastMessageOf i
    a → b ∈ firstGatherBindBroadcastMessageOf i a' → a = a' := by
  intro a a' b h h'
  cases a <;> cases a' <;> simp_all [firstGatherBindBroadcastMessageOf]

theorem secondGatherInputBroadcastMessageOf_inj (i : Fin n) :
    ∀ a a' (b : BRB.Message (Option Bool)), b ∈ secondGatherInputBroadcastMessageOf i a → b ∈
    secondGatherInputBroadcastMessageOf i a' → a = a' := by
  intro a a' b h h'
  cases a <;> cases a' <;> simp_all [secondGatherInputBroadcastMessageOf]

theorem secondGatherBindBroadcastMessageOf_inj (i : Fin n) :
    ∀ a a' (b : BRB.Message (Gather.AcceptedPairs n (Option Bool))), b ∈
    secondGatherBindBroadcastMessageOf i a → b ∈ secondGatherBindBroadcastMessageOf i a' → a = a' :=
    by
  intro a a' b h h'
  cases a <;> cases a' <;> simp_all [secondGatherBindBroadcastMessageOf]

variable {X : Type}

/-! ### The composed round, assembled -/

variable {P : Parameters}

/-- The round-`r` state of the first gather instance, read off the implementation's state:
the local state vectors transposed out of the round records the processes hold,
the network states recovered tag by tag from the adversary's tagged sent sets,
and the instance's core the first field of the adversary's ghost record. -/
noncomputable def firstGatherProjection (P : Parameters) (u : ∀ _ : Fin P.n, AFW.ProcessRecord P.n)
    (w : NetworkState P.n) (r : ℕ) : Gather.StateOverBracha P.n Bool :=
  ((fun i => ((u i).2.roundRecord r).firstGather,
      ⟨⟨messagesOf firstGatherMessageOf firstGatherMessageOf_inj (w.sent r), w.F⟩,
        (w.ghostRecord r).1⟩),
    (fun k => (fun i => (((u i).2.roundRecord r).firstGatherInputBroadcasts
      k),
        ⟨messagesOf (firstGatherInputBroadcastMessageOf k) (firstGatherInputBroadcastMessageOf_inj
          k) (w.sent r), w.F⟩),
      fun q => (fun i => (((u i).2.roundRecord r).firstGatherBindBroadcasts
        q),
        ⟨messagesOf (firstGatherBindBroadcastMessageOf q) (firstGatherBindBroadcastMessageOf_inj q)
          (w.sent r), w.F⟩)))

/-- The round-`r` state of the second gather instance, read off the implementation's state,
its core the second field of the adversary's ghost record. -/
noncomputable def secondGatherProjection (P : Parameters) (u : ∀ _ : Fin P.n, AFW.ProcessRecord P.n)
    (w : NetworkState P.n) (r : ℕ) : Gather.StateOverBracha P.n (Option Bool) :=
  ((fun i => ((u i).2.roundRecord r).secondGather,
      ⟨⟨messagesOf secondGatherMessageOf secondGatherMessageOf_inj (w.sent r), w.F⟩,
        (w.ghostRecord r).2.1⟩),
    (fun k => (fun i => (((u i).2.roundRecord r).secondGatherInputBroadcasts
      k),
        ⟨messagesOf (secondGatherInputBroadcastMessageOf k) (secondGatherInputBroadcastMessageOf_inj
          k) (w.sent r), w.F⟩),
      fun q => (fun i => (((u i).2.roundRecord r).secondGatherBindBroadcasts
        q),
        ⟨messagesOf (secondGatherBindBroadcastMessageOf q) (secondGatherBindBroadcastMessageOf_inj
          q) (w.sent r), w.F⟩)))

/-- One process's record in the round, read off its round record, field by field: the first
gather's input is the round's input, the candidate and the graded outcome are the two the round
record holds, the second gather's input marks the second call, and the round has returned exactly
when its second gather has returned and the record holds no graded outcome, which is the state the
round's own return leaves. -/
def programProjection {n : ℕ} (st : RoundRecord n) : GBCA.ByAFW.ProcessRecord n where
  input := st.firstGather.process.input
  candidate := st.candidate
  secondGatherCalled := st.secondGather.process.input.isSome
  output := st.output
  returned := st.secondGather.process.returned && st.output.isNone

/-- The round-`r` state of the composed system, read off the implementation's state: the
process records beside the round's bound bit, and the two gather instances. -/
noncomputable def roundProjection (P : Parameters) (u : ∀ _ : Fin P.n, AFW.ProcessRecord P.n)
    (w : NetworkState P.n) (r : ℕ) : GBCA.ByAFW.RoundStateOverBracha P.n :=
  ((fun j => programProjection ((u j).2.roundRecord r), (w.ghostRecord r).2.2),
    (firstGatherProjection P u w r, secondGatherProjection P u w r))

/-! ### Reading the composed round's state off the view -/

section Readers

variable (u : ∀ _ : Fin P.n, AFW.ProcessRecord P.n) (w : NetworkState P.n) (r : ℕ)

@[simp] theorem programs_roundProjection (j : Fin P.n) :
    GBCA.ByAFW.programs (roundProjection P u w r) j = programProjection ((u j).2.roundRecord r) :=
      rfl

@[simp] theorem bound_roundProjection : GBCA.ByAFW.bound (roundProjection P u w r) = (w.ghostRecord
  r).2.2 := rfl

@[simp] theorem firstGather_roundProjection : GBCA.ByAFW.firstGather (roundProjection P u w r) =
  firstGatherProjection P u w r := rfl

@[simp] theorem secondGather_roundProjection : GBCA.ByAFW.secondGather (roundProjection P u w r) =
  secondGatherProjection P u w r := rfl

@[simp] theorem core_firstGatherProjection : Gather.core (firstGatherProjection P u w r) =
  (w.ghostRecord r).1 := rfl

@[simp] theorem core_secondGatherProjection : Gather.core (secondGatherProjection P u w r) =
  (w.ghostRecord r).2.1 := rfl

@[simp] theorem gatherTier_firstGatherProjection_process (i : Fin P.n) :
    (Gather.gatherTier (firstGatherProjection P u w r)).1 i
      = ((u i).2.roundRecord r).firstGather := rfl

@[simp] theorem gatherTier_secondGatherProjection_process (i : Fin P.n) :
    (Gather.gatherTier (secondGatherProjection P u w r)).1 i
      = ((u i).2.roundRecord r).secondGather := rfl

@[simp] theorem gatherTier_firstGatherProjection_network :
    (Gather.gatherTier (firstGatherProjection P u w r)).2 = ⟨messagesOf firstGatherMessageOf
      firstGatherMessageOf_inj (w.sent r), w.F⟩ := rfl

@[simp] theorem gatherTier_secondGatherProjection_network :
    (Gather.gatherTier (secondGatherProjection P u w r)).2 = ⟨messagesOf secondGatherMessageOf
      secondGatherMessageOf_inj (w.sent r), w.F⟩ := rfl

@[simp] theorem inputBroadcasts_firstGatherProjection (k : Fin P.n) :
    Gather.inputBroadcasts (firstGatherProjection P u w r) k
      = ((fun i => (((u i).2.roundRecord r).firstGatherInputBroadcasts k)),
          ⟨messagesOf (firstGatherInputBroadcastMessageOf k) (firstGatherInputBroadcastMessageOf_inj
            k) (w.sent r), w.F⟩) := rfl

@[simp] theorem bindBroadcasts_firstGatherProjection (q : Fin P.n) :
    Gather.bindBroadcasts (firstGatherProjection P u w r) q
      = ((fun i => (((u i).2.roundRecord r).firstGatherBindBroadcasts q)),
          ⟨messagesOf (firstGatherBindBroadcastMessageOf q) (firstGatherBindBroadcastMessageOf_inj
            q) (w.sent r), w.F⟩) := rfl

@[simp] theorem inputBroadcasts_secondGatherProjection (k : Fin P.n) :
    Gather.inputBroadcasts (secondGatherProjection P u w r) k
      = ((fun i => (((u i).2.roundRecord r).secondGatherInputBroadcasts k)),
          ⟨messagesOf (secondGatherInputBroadcastMessageOf k)
            (secondGatherInputBroadcastMessageOf_inj k) (w.sent r), w.F⟩) := rfl

@[simp] theorem bindBroadcasts_secondGatherProjection (q : Fin P.n) :
    Gather.bindBroadcasts (secondGatherProjection P u w r) q
      = ((fun i => (((u i).2.roundRecord r).secondGatherBindBroadcasts q)),
          ⟨messagesOf (secondGatherBindBroadcastMessageOf q) (secondGatherBindBroadcastMessageOf_inj
            q) (w.sent r), w.F⟩) := rfl

/-- **The two systems of the first gather's core agree**: the instance's core
is read off its network state alone, and that network state is the one
`AFW.firstGatherOf` hands the adversary. -/
theorem coreOfNetwork_firstGatherProjection :
    Gather.coreOfNetwork P (Gather.gatherTier (firstGatherProjection P u w r)).2 = Gather.coreOf P
      (firstGatherOf P w r) :=
  (Gather.coreOf_eq_coreOfNetwork P (firstGatherOf P w r)).symm

/-- The same for the second gather's core. -/
theorem coreOfNetwork_secondGatherProjection :
    Gather.coreOfNetwork P (Gather.gatherTier (secondGatherProjection P u w r)).2 = Gather.coreOf P
      (secondGatherOf P w r) :=
  (Gather.coreOf_eq_coreOfNetwork P (secondGatherOf P w r)).symm

end Readers

/-! ### The ghost write, read through the view

The adversary's ghost record of round `r` is the round's two gather cores
beside its bound bit, so a transition's ghost write is the round's write of
those three fields. The lemmas below are that write at the round the
transition's label names, at every other round, and at a transition whose write
returns the record it found. -/

/-- **The ghost write at the round its label names**, read through the view:
the two cores and the bound bit are the written record, every other coordinate
the view before the write. -/
theorem roundProjection_writeGhost (v : ∀ _ : Fin P.n, AFW.ProcessRecord P.n) (w : NetworkState P.n)
    {L : Implementation.ExtendedLabel P.n (Message P.n) (RoundEvent P.n)} {r : ℕ}
    (h : roundOf L = some r) :
    roundProjection P v (w.writeGhost (ghostStep P) L) r
      = ((fun j => programProjection ((v j).2.roundRecord r),
         (ghostStep P L w (w.ghostRecord r)).2.2),
          (Gather.setCore (firstGatherProjection P v w r) (ghostStep P L w (w.ghostRecord r)).1,
            Gather.setCore (secondGatherProjection P v w r) (ghostStep P L w (w.ghostRecord
              r)).2.1)) := by
  unfold Implementation.NetworkState.writeGhost
  rw [h]
  simp [roundProjection, firstGatherProjection, secondGatherProjection, Gather.setCore]

/-- The ghost write leaves every other round's view where it stands. -/
theorem roundProjection_writeGhost_ne (v : ∀ _ : Fin P.n, AFW.ProcessRecord P.n)
    (w : NetworkState P.n)
    {L : Implementation.ExtendedLabel P.n (Message P.n) (RoundEvent P.n)} {r r' : ℕ}
    (h : roundOf L = some r)
    (hr : r' ≠ r) :
    roundProjection P v (w.writeGhost (ghostStep P) L) r' = roundProjection P v w r' := by
  unfold Implementation.NetworkState.writeGhost
  rw [h]
  simp [roundProjection, firstGatherProjection, secondGatherProjection, Function.update_of_ne hr]

/-- A transition whose ghost write returns the record it found leaves every
round's view where it stands. -/
theorem roundProjection_ghostId
    (L : Implementation.ExtendedLabel P.n (Message P.n) (RoundEvent P.n))
    (h : ∀ (v : NetworkState P.n) (G : Ghost P.n), ghostStep P L v G = G)
    (x : ∀ _ : Fin P.n, AFW.ProcessRecord P.n) (w : NetworkState P.n) (r' : ℕ) :
    roundProjection P x (w.writeGhost (ghostStep P) L) r' = roundProjection P x w r' := by
  unfold Implementation.NetworkState.writeGhost
  cases hL : roundOf L with
  | none => rfl
  | some r => simp only [h, Function.update_eq_self]

/-- The ghost write never clears a round's bound bit: `AFW.ghostStep` writes the third field at the
first gather's return alone, and writes it `some`. -/
theorem ghostStep_bound (L : Implementation.ExtendedLabel P.n (Message P.n) (RoundEvent P.n))
    (v : NetworkState P.n)
    (G : Ghost P.n) (h : G.2.2 ≠ none) : (ghostStep P L v G).2.2 ≠ none := by
  unfold ghostStep
  split <;> simp_all

/-- The bound bit of a round on record stays on record across any transition. -/
theorem writeGhost_bound {w : NetworkState P.n}
    (L : Implementation.ExtendedLabel P.n (Message P.n) (RoundEvent P.n)) {r : ℕ}
    (h : (w.ghostRecord r).2.2 ≠ none) :
    ((w.writeGhost (ghostStep P) L).ghostRecord r).2.2 ≠ none := by
  unfold Implementation.NetworkState.writeGhost
  cases hL : roundOf L with
  | none => exact h
  | some r₀ =>
    by_cases hr : r = r₀
    · subst hr; simpa using ghostStep_bound L w _ h
    · simpa [Function.update_of_ne hr] using h

/-- A send, read through the view with its ghost write: the round's two cores
and its bound bit are the record `AFW.ghostStep` writes, and every other
coordinate is the send's own. -/
theorem roundProjection_gbcaSendGhost (v : ∀ _ : Fin P.n, AFW.ProcessRecord P.n)
    (w : NetworkState P.n) (r : ℕ) (j : Fin P.n) (m : Message P.n) :
    roundProjection P v ((w.recordGBCASend r j m).writeGhost (ghostStep P) (Sum.inr (.gbcaSend r j
      m))) r
      = ((fun i => programProjection ((v i).2.roundRecord r),
            (ghostStep P (Sum.inr (.gbcaSend r j m)) (w.recordGBCASend r j m) (w.ghostRecord
              r)).2.2),
         (Gather.setCore (firstGatherProjection P v (w.recordGBCASend r j m) r)
            (ghostStep P (Sum.inr (.gbcaSend r j m)) (w.recordGBCASend r j m) (w.ghostRecord r)).1,
          Gather.setCore (secondGatherProjection P v (w.recordGBCASend r j m) r)
            (ghostStep P (Sum.inr (.gbcaSend r j m)) (w.recordGBCASend r j m) (w.ghostRecord
              r)).2.1)) :=
  roundProjection_writeGhost v _ rfl

/-! ### The view at the initial state -/

/-- The empty sent family projects to the empty sent family. -/
theorem messagesOf_empty {β : Type} (f : Message n → Option β)
    (hf : ∀ a a' b, b ∈ f a → b ∈ f a' → a = a') :
    messagesOf f hf (fun _ => (∅ : Finset (Message n))) = fun _ => (∅ : Finset β) := by
  funext q
  simp [messagesOf]

/-- **Every round of the view is the composed round's initial state**: an untouched round reads as
the initial record in the implementation, and the empty sent projects to the empty sent. -/
theorem roundProjection_init (P : Parameters) (r : ℕ) :
    roundProjection P (protocol P).init.1 (protocol P).init.2.1 r =
    (GBCA.ByAFW.roundOverBracha P r).init :=
      by
  have hproc : (protocol P).init.1
      = fun _ => (RoundLoopRecord.initial P.n,
        Implementation.RoundRecordMap.initial (RoundRecord P.n)) := rfl
  have hsent : ((protocol P).init.2.1).sent = fun _ _ => (∅ : Finset (Message P.n)) := rfl
  have hF : ((protocol P).init.2.1).F = (∅ : Finset (Fin P.n)) := rfl
  have hghost : ((protocol P).init.2.1).ghostRecord
      = fun _ => ((none, none, none) : Ghost P.n) := rfl
  rw [GBCA.ByAFW.roundOverBracha_init, roundProjection, firstGatherProjection,
    secondGatherProjection, hproc, hsent, hF, hghost]
  simp [Gather.instanceOverBracha_init, GBCA.ByAFW.ProcessRecord.initial, programProjection,
    RoundRecord.initial, Gather.NetworkState.initial, ABA.NetworkState.initial,
      BRB.BrachaState.initial,
    InstanceState.initial, messagesOf_empty]
  rfl

/-! ### The relation -/

/-- **The round's bound bit is on record wherever its candidate is**: a process holding a
round-`r` candidate has passed that round's first gather return, and that return writes the bound
bit. The second conjunct carries a graded outcome on record back to a candidate on record, through
the two record facts that are the guards of the transitions writing the fields between them. This
is what the graded return's announced bit rests on, and it is the one clause of the relation that
is not a projection of the implementation's state. -/
def BoundInvariant (P : Parameters) (u : ∀ _ : Fin P.n, AFW.ProcessRecord P.n)
    (w : NetworkState P.n) : Prop :=
  (∀ (r : ℕ) (i : Fin P.n), ((u i).2.roundRecord r).candidate ≠ none →
      (w.ghostRecord r).2.2 ≠ none) ∧
    ∀ (r : ℕ) (i : Fin P.n),
      (((u i).2.roundRecord r).output ≠ none →
          (((u i).2.roundRecord r).secondGather.process).input ≠ none) ∧
        ((((u i).2.roundRecord r).secondGather.process).input ≠ none →
          ((u i).2.roundRecord r).candidate ≠ none)

/-- **The composition relation**: the round loops and the coin oracle are shared, the ABA network is
the DECIDED sets beside the corrupted set, every round's state is the view `roundProjection` of the
implementation's state, and the bound bit of a called round is on record. The first four conjuncts
are unguarded, so they determine the composed state from the implementation. -/
def ProtocolRelation (P : Parameters) (s : ProtocolState P) (t : ComposedState P) : Prop :=
  (∀ j, (s.1 j).1 = t.2.1 j) ∧
    s.2.2 = t.2.2.2 ∧
    t.2.2.1 = ⟨s.2.1.decidedSent, s.2.1.F⟩ ∧
    t.1 = (fun r => roundProjection P s.1 s.2.1 r) ∧
    BoundInvariant P s.1 s.2.1

theorem protocolRelation_mk (P : Parameters) (u : ∀ _ : Fin P.n, AFW.ProcessRecord P.n)
    (w : NetworkState P.n) (o : ℕ → WCC.SpecState P.n) (G : ℕ → GBCA.ByAFW.RoundStateOverBracha P.n)
    (C : ∀ _ : Fin P.n, RoundLoopRecord P.n) (A : ABANetworkState P.n)
    (o' : ℕ → WCC.SpecState P.n) :
    ProtocolRelation P (u, w, o) (G, C, A, o') ↔
      ((∀ j, (u j).1 = C j) ∧ o = o' ∧ A = ⟨w.decidedSent, w.F⟩ ∧
        (G = fun r => roundProjection P u w r) ∧ BoundInvariant P u w) := Iff.rfl

/-- The bound invariant survives a transition that leaves the three fields it reads where they
stand and keeps on record every bound bit already there. -/
theorem boundInvariant_of {u x : ∀ _ : Fin P.n, AFW.ProcessRecord P.n} {w v : NetworkState P.n}
    (hI : BoundInvariant P u w)
    (hcand : ∀ i r, ((x i).2.roundRecord r).candidate = ((u i).2.roundRecord r).candidate)
    (hinput : ∀ i r, (((x i).2.roundRecord r).secondGather.process).input
      = (((u i).2.roundRecord r).secondGather.process).input)
    (hout : ∀ i r, ((x i).2.roundRecord r).output = ((u i).2.roundRecord r).output)
    (hv : ∀ r, (w.ghostRecord r).2.2 ≠ none → (v.ghostRecord r).2.2 ≠ none) :
    BoundInvariant P x v :=
  ⟨fun r i hne => hv r (hI.1 r i (by rw [← hcand i r]; exact hne)),
    fun r i => ⟨fun ho => by
        rw [hinput i r]; exact (hI.2 r i).1 (by rw [← hout i r]; exact ho),
      fun hs => by rw [hcand i r]; exact (hI.2 r i).2 (by rw [← hinput i r]; exact hs)⟩⟩

/-- The bound invariant survives a transition that clears the graded outcome of a round, the
candidate and the second gather's input standing. -/
theorem boundInvariant_ofOutputCleared {u x : ∀ _ : Fin P.n, AFW.ProcessRecord P.n}
    {w v : NetworkState P.n} (hI : BoundInvariant P u w)
    (hcand : ∀ i r, ((x i).2.roundRecord r).candidate = ((u i).2.roundRecord r).candidate)
    (hinput : ∀ i r, (((x i).2.roundRecord r).secondGather.process).input
      = (((u i).2.roundRecord r).secondGather.process).input)
    (hout : ∀ i r, ((x i).2.roundRecord r).output ≠ none → ((u i).2.roundRecord r).output ≠ none)
    (hv : ∀ r, (w.ghostRecord r).2.2 ≠ none → (v.ghostRecord r).2.2 ≠ none) :
    BoundInvariant P x v :=
  ⟨fun r i hne => hv r (hI.1 r i (by rw [← hcand i r]; exact hne)),
    fun r i => ⟨fun ho => by
        rw [hinput i r]; exact (hI.2 r i).1 (hout i r ho),
      fun hs => by rw [hcand i r]; exact (hI.2 r i).2 (by rw [← hinput i r]; exact hs)⟩⟩

/-- The bound invariant survives the second gather's call: the candidate and the graded outcome
stand, and at every round the second gather's input either stands or is written at a record whose
candidate is on record. -/
theorem boundInvariant_ofSecondGatherCall {u x : ∀ _ : Fin P.n, AFW.ProcessRecord P.n}
    {w v : NetworkState P.n} (hI : BoundInvariant P u w)
    (hcand : ∀ i r, ((x i).2.roundRecord r).candidate = ((u i).2.roundRecord r).candidate)
    (hout : ∀ i r, ((x i).2.roundRecord r).output = ((u i).2.roundRecord r).output)
    (hinput : ∀ i r, (((x i).2.roundRecord r).secondGather.process).input
        = (((u i).2.roundRecord r).secondGather.process).input ∨
      ((((x i).2.roundRecord r).secondGather.process).input ≠ none ∧
        ((u i).2.roundRecord r).candidate ≠ none))
    (hv : ∀ r, (w.ghostRecord r).2.2 ≠ none → (v.ghostRecord r).2.2 ≠ none) :
    BoundInvariant P x v := by
  refine ⟨fun r i hne => hv r (hI.1 r i (by rw [← hcand i r]; exact hne)), fun r i => ?_⟩
  rcases hinput i r with heq | ⟨hne, hc⟩
  · exact ⟨fun ho => by rw [heq]; exact (hI.2 r i).1 (by rw [← hout i r]; exact ho),
      fun hs => by rw [hcand i r]; exact (hI.2 r i).2 (by rw [← heq]; exact hs)⟩
  · exact ⟨fun _ => hne, fun _ => by rw [hcand i r]; exact hc⟩

/-- The initial states are related: every round of the view is the composed
round's initial state. -/
theorem protocolRelation_init (P : Parameters) :
    ProtocolRelation P (protocol P).init (composed P).init := by
  refine ⟨fun _ => rfl, rfl, rfl, ?_,
    fun _ _ h => absurd rfl h, fun _ _ => ⟨fun h => absurd rfl h, fun h => absurd rfl h⟩⟩
  funext r
  exact (roundProjection_init P r).symm

/-! ### Transposing one written record

A transition writes the acting process's round record, so the local state vector the
view reads becomes a one-point update of the old one. Each lemma below is that
observation at one component, stated over the `ite` that reading a written
record produces. -/

section LocalStates
variable {j : Fin n} (Y : Fin n → RoundRecord n) (sr : RoundRecord n)

theorem locals_firstGather_if :
    (fun i => (if i = j then sr else Y i).firstGather)
      = Function.update (fun i => (Y i).firstGather) j sr.firstGather := by
  funext i
  rw [Function.update_apply]
  by_cases hi : i = j <;> simp [hi]

theorem locals_secondGather_if :
    (fun i => (if i = j then sr else Y i).secondGather)
      = Function.update (fun i => (Y i).secondGather) j sr.secondGather := by
  funext i
  rw [Function.update_apply]
  by_cases hi : i = j <;> simp [hi]

theorem locals_firstGatherInputBroadcasts_if (k : Fin n) :
    (fun i => (if i = j then sr else Y i).firstGatherInputBroadcasts k)
      = Function.update (fun i => (Y i).firstGatherInputBroadcasts k) j
        (sr.firstGatherInputBroadcasts k) := by
  funext i
  rw [Function.update_apply]
  by_cases hi : i = j <;> simp [hi]

theorem locals_firstGatherBindBroadcasts_if (k : Fin n) :
    (fun i => (if i = j then sr else Y i).firstGatherBindBroadcasts k) = Function.update
    (fun i => (Y i).firstGatherBindBroadcasts k) j (sr.firstGatherBindBroadcasts k) := by
  funext i
  rw [Function.update_apply]
  by_cases hi : i = j <;> simp [hi]

theorem locals_secondGatherInputBroadcasts_if (k : Fin n) :
    (fun i => (if i = j then sr else Y i).secondGatherInputBroadcasts k)
      = Function.update (fun i => (Y i).secondGatherInputBroadcasts k) j
        (sr.secondGatherInputBroadcasts k) := by
  funext i
  rw [Function.update_apply]
  by_cases hi : i = j <;> simp [hi]

theorem locals_secondGatherBindBroadcasts_if (k : Fin n) :
    (fun i => (if i = j then sr else Y i).secondGatherBindBroadcasts k)
      = Function.update (fun i => (Y i).secondGatherBindBroadcasts k) j
        (sr.secondGatherBindBroadcasts k) := by
  funext i
  rw [Function.update_apply]
  by_cases hi : i = j <;> simp [hi]

end LocalStates

end AFW

end ABA
end PLTS
