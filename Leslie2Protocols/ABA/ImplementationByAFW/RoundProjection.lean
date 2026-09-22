/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sathiya / Claude
-/

import Leslie2Protocols.ABA.ImplementationByAFW.System
import Leslie2Protocols.ABA.ImplementationByAFW.CompositionChain
import Leslie2Protocols.ABA.Gather.StepOverBracha
import Leslie2Protocols.ABA.ReliableBroadcast.BrachaRefinesSpecification
import Leslie2Protocols.Framework.FamilySimulation
import Leslie2Protocols.Framework.WeakTransitionsFromChains
import Leslie2Protocols.Framework.Congruence

/-!
# The view of the gather-based protocol in its composed system

`AFW.protocol P` is the gather-based protocol as it runs and `AFW.composed P` reads the same
protocol as a composition of components, down to the broadcast instances. This file holds the three
things the simulation between them rests on: the view that computes a composed state from the
implementation, the relation that view carries, and the builders that assemble a transition of the
composed system.

## The composed state is a view of the implementation

A state of `composed P` is computed from a state of `protocol P`. The round loops and the coin
oracle are shared objects, the ABA network is the DECIDED sets beside the corrupted set, and the
round-`r` state is assembled by `roundProjection`. Assembling it undoes the two rearrangements the
implementation performs. The local states are transposed back: an instance's local state vector at
round `r` is read off the round records the `n` processes hold. And the sent sets are sliced: an
instance's network state carries the messages of one tag, recovered from the adversary's single
tagged sent family by `AFW.messagesOf`.

## What the broadcast instances returned, and the return flags

A gather program of the composed system holds two records of what each broadcast instance has
returned to it. The implementation keeps no returned value: it reads a receipt quorum on the
process's own local state in that instance (`AFW.firstGatherAcceptedInputs` and its three
companions). `AFW.broadcastReturnsFor` (`ABA/ImplementationByAFW/System.lean`) is that condition as
a function: the value on which the local state holds a `2f + 1` `VOTE` receipt quorum, and `none`
where there is no such value. Under the broadcast invariant `BRB.Invariant` at most one value
carries a quorum (`broadcastReturnsFor_eq_of_quorum`), so the function agrees with the
implementation's guard wherever the implementation's guard fires. The accepted pairs a gather's
`ECHO` carries, `AFW.firstGatherAcceptedPairs` and `AFW.secondGatherAcceptedPairs`, are the accepted
pairs of the gather program the view assembles (`firstGatherAcceptedPairs_gatherLocalState`,
`secondGatherAcceptedPairs_gatherLocalState`).

The composed broadcast program carries a return flag, which the implementation never sets.
`broadcastLocalState` supplies it from the returned value: a process has returned in an instance
exactly when the instance has returned a value.

## The ghost record is the round's auxiliary state

The round carries three fields no guard of it reads: the core of each of its
two gather instances, and the round's bound bit. In the implementation the network
holds those three as the ghost record of the round (`AFW.Ghost`), so the view
reads them off it, and a row's ghost write is the round's write of them
(`roundProjection_writeGhost`, `roundProjection_writeGhost_ne`, `roundProjection_ghostId`). The two
projections of a gather's core agree because each is `Gather.coreOf` of the same
network state (`coreOfNetwork_firstGatherProjection`, `coreOfNetwork_secondGatherProjection`).

## The two clauses that are not projections

`BoundInvariant` says that a process whose round-`r` second-gather local state carries an input has
passed the round's return-then-call step, so the round's bound bit is on record.
`BroadcastReturnsInvariant` says that `BRB.Invariant` holds at each of the round's `4n` broadcast
instances, which is what makes the returned value a function of the implementation's state in the
sense the implementation's guards need. -/

namespace PLTS
namespace ABA
namespace AFW

open Implementation Composition GBCA.ByABDY

/-! ### The four broadcast untaggings

The two gather untaggings and their injectivity are `AFW.firstGatherMessageOf` and
`AFW.secondGatherMessageOf` of `ABA/ImplementationByAFW/System.lean`, where the adversary's ghost
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

theorem firstGatherBindBroadcastMessageOf_inj (i : Fin n) : ∀ a a' (b : BRB.Message
  (Gather.AcceptedPairs n Bool)),
    b ∈ firstGatherBindBroadcastMessageOf i a → b ∈ firstGatherBindBroadcastMessageOf i a' → a = a'
      := by
  intro a a' b h h'
  cases a <;> cases a' <;> simp_all [firstGatherBindBroadcastMessageOf]

theorem secondGatherInputBroadcastMessageOf_inj (i : Fin n) : ∀ a a' (b : BRB.Message (Option
  Bool)),
    b ∈ secondGatherInputBroadcastMessageOf i a → b ∈ secondGatherInputBroadcastMessageOf i a' → a =
      a' := by
  intro a a' b h h'
  cases a <;> cases a' <;> simp_all [secondGatherInputBroadcastMessageOf]

theorem secondGatherBindBroadcastMessageOf_inj (i : Fin n) : ∀ a a' (b : BRB.Message
  (Gather.AcceptedPairs n (Option Bool))),
    b ∈ secondGatherBindBroadcastMessageOf i a → b ∈ secondGatherBindBroadcastMessageOf i a' → a =
      a' := by
  intro a a' b h h'
  cases a <;> cases a' <;> simp_all [secondGatherBindBroadcastMessageOf]

/-! ### What was returned by a broadcast instance -/

variable {X : Type}

/-- A broadcast instance has returned a value exactly when some value has a receipt quorum. -/
theorem broadcastReturnsFor_isSome_iff (P : Parameters) [DecidableEq X]
    (p : LocalState P.n (BRB.ProcessRecord X) (BRB.Message X)) :
    (broadcastReturnsFor P p).isSome ↔ ∃ v, 2 * P.f + 1 ≤ p.receivedCount (BRB.Message.vote v) := by
  unfold broadcastReturnsFor
  by_cases h : ∃ v, 2 * P.f + 1 ≤ p.receivedCount (BRB.Message.vote v)
  · rw [dif_pos h]; exact iff_of_true rfl h
  · rw [dif_neg h]; exact iff_of_false (by simp) h

/-- The value returned has a receipt quorum. -/
theorem broadcastReturnsFor_voteQuorum (P : Parameters) [DecidableEq X]
    {p : LocalState P.n (BRB.ProcessRecord X) (BRB.Message X)} {x : X} (h : broadcastReturnsFor P p
      = some x) :
    2 * P.f + 1 ≤ p.receivedCount (BRB.Message.vote x) := by
  unfold broadcastReturnsFor at h
  by_cases hq : ∃ v, 2 * P.f + 1 ≤ p.receivedCount (BRB.Message.vote v)
  · rw [dif_pos hq] at h
    obtain rfl : Classical.choose hq = x := Option.some.inj h
    exact Classical.choose_spec hq
  · rw [dif_neg hq] at h
    exact absurd h (by simp)

/-- **A broadcast instance returns the value of a receipt quorum.** Under the broadcast invariant a
`VOTE` receipt quorum yields the echo certificate, and at most one value is certified, so the value
returned is the one the quorum carries. -/
theorem broadcastReturnsFor_eq_of_quorum (P : Parameters) [DecidableEq X] {k : Fin P.n}
    {s : BRB.BrachaState P.n X} (hInv : BRB.Invariant P k s) {j : Fin P.n} {x : X}
    (hq : 2 * P.f + 1 ≤ (s.1 j).receivedCount (BRB.Message.vote x)) :
    broadcastReturnsFor P (s.1 j) = some x := by
  have hex : ∃ v, 2 * P.f + 1 ≤ (s.1 j).receivedCount (BRB.Message.vote v) := ⟨x, hq⟩
  unfold broadcastReturnsFor
  rw [dif_pos hex]
  refine congrArg some ?_
  have h1 : 2 * P.f + 1 ≤ s.receivedCount j (BRB.Message.vote (Classical.choose hex)) :=
    Classical.choose_spec hex
  exact BRB.echoCertificate_unique hInv (BRB.echoCertificate_of_vote_quorum hInv h1)
    (BRB.echoCertificate_of_vote_quorum hInv (i := j) (m := x) hq)

/-- An untouched local state has returned nothing: nothing is delivered, and a receipt quorum is at
least one receipt. -/
theorem broadcastReturnsFor_initial (P : Parameters) [DecidableEq X] :
    broadcastReturnsFor P (LocalState.initial P.n (BRB.Message X) (BRB.ProcessRecord.initial X)) =
      none := by
  unfold broadcastReturnsFor
  rw [dif_neg]
  rintro ⟨v, hv⟩
  have h0 : (LocalState.initial P.n (BRB.Message X) (BRB.ProcessRecord.initial X)).receivedCount
      (BRB.Message.vote v) = 0 := by
    simp [LocalState.receivedCount]
  rw [h0] at hv
  omega

/-- One process's local state in a broadcast instance, as the composed broadcast program holds it:
the return flag is whether the instance has returned a value. -/
noncomputable def broadcastLocalState (P : Parameters) [DecidableEq X]
    (p : LocalState P.n (BRB.ProcessRecord X) (BRB.Message X)) :
    LocalState P.n (BRB.ProcessRecord X) (BRB.Message X) :=
  { p with process := { p.process with returned := (broadcastReturnsFor P p).isSome } }

/-- One process's local state in a gather instance, as the composed gather program holds it: the
gather record extended by the returned values of what the broadcast instances have returned here,
over the same delivered sets. -/
noncomputable def gatherLocalState (P : Parameters) (X : Type) [DecidableEq X]
    (gatherTier : LocalState P.n (Gather.BaseProcessRecord P.n X) (Gather.Message P.n X))
    (bIn : Fin P.n → LocalState P.n (BRB.ProcessRecord X) (BRB.Message X))
    (bBind : Fin P.n → LocalState P.n (BRB.ProcessRecord (Gather.AcceptedPairs P.n X))
      (BRB.Message (Gather.AcceptedPairs P.n X))) :
    LocalState P.n (Gather.ProcessRecord P.n X) (Gather.Message P.n X) where
  process :=
    { gatherTier.process with
      inputBroadcastReturned := fun k => broadcastReturnsFor P (bIn k)
      bindBroadcastReturned := fun q => broadcastReturnsFor P (bBind q) }
  received := gatherTier.received

/-- **The first gather's accepted pairs are the accepted pairs of the gather program the view
assembles**: the view supplies what that program's input instances returned as `broadcastReturnsFor`
at each of the `n` input-broadcast instances, and `AFW.firstGatherAcceptedPairs` is the pairs of
that same condition. -/
theorem firstGatherAcceptedPairs_gatherLocalState (P : Parameters) (s : RoundRecord P.n) :
    (gatherLocalState P Bool s.firstGather s.firstGatherInputBroadcasts
      s.firstGatherBindBroadcasts).process.accepted = firstGatherAcceptedPairs P s := by
  ext ⟨k, v⟩
  rw [Gather.ProcessRecord.mem_accepted, mem_firstGatherAcceptedPairs]
  exact Iff.rfl

/-- The same at the second gather. -/
theorem secondGatherAcceptedPairs_gatherLocalState (P : Parameters) (s : RoundRecord P.n) :
    (gatherLocalState P (Option Bool) s.secondGather s.secondGatherInputBroadcasts
      s.secondGatherBindBroadcasts).process.accepted
      = secondGatherAcceptedPairs P s := by
  ext ⟨k, v⟩
  rw [Gather.ProcessRecord.mem_accepted, mem_secondGatherAcceptedPairs]
  exact Iff.rfl

/-! ### The composed round, assembled -/

variable {P : Parameters}

/-- The round-`r` state of the first gather instance, read off the implementation's state:
the local state vectors transposed out of the round records the processes hold,
the network states sliced out of the adversary's tagged sent sets, and the
instance's core the first field of the adversary's ghost record. -/
noncomputable def firstGatherProjection (P : Parameters) (u : ∀ _ : Fin P.n, AFW.ProcessRecord P.n)
    (w : NetworkState P.n) (r : ℕ) : Gather.StateOverBracha P.n Bool :=
  ((fun i => gatherLocalState P Bool ((u i).2.roundRecord r).firstGather ((u i).2.roundRecord
    r).firstGatherInputBroadcasts
        ((u i).2.roundRecord r).firstGatherBindBroadcasts,
      ⟨⟨messagesOf firstGatherMessageOf firstGatherMessageOf_inj (w.sent r), w.F⟩,
        (w.ghostRecord r).1⟩),
    (fun k => (fun i => broadcastLocalState P (((u i).2.roundRecord r).firstGatherInputBroadcasts
      k),
        ⟨messagesOf (firstGatherInputBroadcastMessageOf k) (firstGatherInputBroadcastMessageOf_inj
          k) (w.sent r), w.F⟩),
      fun q => (fun i => broadcastLocalState P (((u i).2.roundRecord r).firstGatherBindBroadcasts
        q),
        ⟨messagesOf (firstGatherBindBroadcastMessageOf q) (firstGatherBindBroadcastMessageOf_inj q)
          (w.sent r), w.F⟩)))

/-- The round-`r` state of the second gather instance, read off the implementation's state,
its core the second field of the adversary's ghost record. -/
noncomputable def secondGatherProjection (P : Parameters) (u : ∀ _ : Fin P.n, AFW.ProcessRecord P.n)
    (w : NetworkState P.n) (r : ℕ) : Gather.StateOverBracha P.n (Option Bool) :=
  ((fun i => gatherLocalState P (Option Bool) ((u i).2.roundRecord r).secondGather ((u
    i).2.roundRecord r).secondGatherInputBroadcasts
        ((u i).2.roundRecord r).secondGatherBindBroadcasts,
      ⟨⟨messagesOf secondGatherMessageOf secondGatherMessageOf_inj (w.sent r), w.F⟩,
        (w.ghostRecord r).2.1⟩),
    (fun k => (fun i => broadcastLocalState P (((u i).2.roundRecord r).secondGatherInputBroadcasts
      k),
        ⟨messagesOf (secondGatherInputBroadcastMessageOf k) (secondGatherInputBroadcastMessageOf_inj
          k) (w.sent r), w.F⟩),
      fun q => (fun i => broadcastLocalState P (((u i).2.roundRecord r).secondGatherBindBroadcasts
        q),
        ⟨messagesOf (secondGatherBindBroadcastMessageOf q) (secondGatherBindBroadcastMessageOf_inj
          q) (w.sent r), w.F⟩)))

/-- One process's record in the round, read off its round record: the first
gather's input is the round's input, the second gather's input is the
candidate and marks the second call, the second gather's return flag is the
round's, and no grade is on record. -/
def programProjection {n : ℕ} (st : RoundRecord n) : GBCA.ByAFW.ProcessRecord n where
  input := st.firstGather.process.input
  candidate := st.secondGather.process.input
  secondGatherCalled := st.secondGather.process.input.isSome
  output := none
  returned := st.secondGather.process.returned

/-- The round-`r` state of the composed system, read off the implementation's state: the
process records beside the round's bound bit, and the two gather instances. -/
noncomputable def roundProjection (P : Parameters) (u : ∀ _ : Fin P.n, AFW.ProcessRecord P.n)
    (w : NetworkState P.n) (r : ℕ) : GBCA.ByAFW.RoundStateOverBracha P.n :=
  ((fun j => programProjection ((u j).2.roundRecord r), (w.ghostRecord r).2.2),
    (firstGatherProjection P u w r, secondGatherProjection P u w r))

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
      = gatherLocalState P Bool ((u i).2.roundRecord r).firstGather ((u i).2.roundRecord
        r).firstGatherInputBroadcasts
          ((u i).2.roundRecord r).firstGatherBindBroadcasts := rfl

@[simp] theorem gatherTier_secondGatherProjection_process (i : Fin P.n) :
    (Gather.gatherTier (secondGatherProjection P u w r)).1 i
      = gatherLocalState P (Option Bool) ((u i).2.roundRecord r).secondGather ((u i).2.roundRecord
        r).secondGatherInputBroadcasts
          ((u i).2.roundRecord r).secondGatherBindBroadcasts := rfl

@[simp] theorem gatherTier_firstGatherProjection_network :
    (Gather.gatherTier (firstGatherProjection P u w r)).2 = ⟨messagesOf firstGatherMessageOf
      firstGatherMessageOf_inj (w.sent r), w.F⟩ := rfl

@[simp] theorem gatherTier_secondGatherProjection_network :
    (Gather.gatherTier (secondGatherProjection P u w r)).2 = ⟨messagesOf secondGatherMessageOf
      secondGatherMessageOf_inj (w.sent r), w.F⟩ := rfl

@[simp] theorem inputBroadcasts_firstGatherProjection (k : Fin P.n) :
    Gather.inputBroadcasts (firstGatherProjection P u w r) k
      = ((fun i => broadcastLocalState P (((u i).2.roundRecord r).firstGatherInputBroadcasts k)),
          ⟨messagesOf (firstGatherInputBroadcastMessageOf k) (firstGatherInputBroadcastMessageOf_inj
            k) (w.sent r), w.F⟩) := rfl

@[simp] theorem bindBroadcasts_firstGatherProjection (q : Fin P.n) :
    Gather.bindBroadcasts (firstGatherProjection P u w r) q
      = ((fun i => broadcastLocalState P (((u i).2.roundRecord r).firstGatherBindBroadcasts q)),
          ⟨messagesOf (firstGatherBindBroadcastMessageOf q) (firstGatherBindBroadcastMessageOf_inj
            q) (w.sent r), w.F⟩) := rfl

@[simp] theorem inputBroadcasts_secondGatherProjection (k : Fin P.n) :
    Gather.inputBroadcasts (secondGatherProjection P u w r) k
      = ((fun i => broadcastLocalState P (((u i).2.roundRecord r).secondGatherInputBroadcasts k)),
          ⟨messagesOf (secondGatherInputBroadcastMessageOf k)
            (secondGatherInputBroadcastMessageOf_inj k) (w.sent r), w.F⟩) := rfl

@[simp] theorem bindBroadcasts_secondGatherProjection (q : Fin P.n) :
    Gather.bindBroadcasts (secondGatherProjection P u w r) q
      = ((fun i => broadcastLocalState P (((u i).2.roundRecord r).secondGatherBindBroadcasts q)),
          ⟨messagesOf (secondGatherBindBroadcastMessageOf q) (secondGatherBindBroadcastMessageOf_inj
            q) (w.sent r), w.F⟩) := rfl

/-- The first gather's `ECHO` payload, read through the view: the accepted
pairs of the sender's round record are the accepted pairs the composed gather
program holds. -/
theorem accepted_firstGatherProjection (j : Fin P.n) :
    ((Gather.gatherTier (firstGatherProjection P u w r)).process j).accepted =
      firstGatherAcceptedPairs P ((u j).2.roundRecord r) :=
  firstGatherAcceptedPairs_gatherLocalState P ((u j).2.roundRecord r)

/-- The same at the second gather. -/
theorem accepted_secondGatherProjection (j : Fin P.n) :
    ((Gather.gatherTier (secondGatherProjection P u w r)).process j).accepted =
      secondGatherAcceptedPairs P ((u j).2.roundRecord r) :=
  secondGatherAcceptedPairs_gatherLocalState P ((u j).2.roundRecord r)

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
beside its bound bit, so a row's ghost write is the round's write of those
three fields. The lemmas below are that write at the round the row's label
names, at every other round, and at a row whose write returns the record it
found. -/

/-- **The ghost write at the round its label names**, read through the view:
the two cores and the bound bit are the written record, every other coordinate
the view before the write. -/
theorem roundProjection_writeGhost (v : ∀ _ : Fin P.n, AFW.ProcessRecord P.n) (w : NetworkState P.n)
    {L : ExtendedLabel P.n (Message P.n)} {r : ℕ} (h : roundOf L = some r) :
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
theorem roundProjection_writeGhost_ne (v : ∀ _ : Fin P.n,
    AFW.ProcessRecord P.n) (w : NetworkState P.n) {L : ExtendedLabel P.n (Message P.n)} {r r' : ℕ}
      (h : roundOf L = some r) (hr : r' ≠ r) :
    roundProjection P v (w.writeGhost (ghostStep P) L) r' = roundProjection P v w r' := by
  unfold Implementation.NetworkState.writeGhost
  rw [h]
  simp [roundProjection, firstGatherProjection, secondGatherProjection, Function.update_of_ne hr]

/-- A row whose ghost write returns the record it found leaves every round's
view where it stands. -/
theorem roundProjection_ghostId (L : ExtendedLabel P.n (Message P.n))
    (h : ∀ (v : NetworkState P.n) (G : Ghost P.n), ghostStep P L v G = G)
    (x : ∀ _ : Fin P.n, AFW.ProcessRecord P.n) (w : NetworkState P.n) (r' : ℕ) :
    roundProjection P x (w.writeGhost (ghostStep P) L) r' = roundProjection P x w r' := by
  unfold Implementation.NetworkState.writeGhost
  cases hL : roundOf L with
  | none => rfl
  | some r => simp only [h, Function.update_eq_self]

/-- The ghost write never clears a round's bound bit: `AFW.ghostStep` writes the third field at the
return-then-call step alone, and writes it `some`. -/
theorem ghostStep_bound (L : ExtendedLabel P.n (Message P.n)) (v : NetworkState P.n)
    (G : Ghost P.n) (h : G.2.2 ≠ none) : (ghostStep P L v G).2.2 ≠ none := by
  unfold ghostStep
  split <;> simp_all

/-- The bound bit of a round on record stays on record across any row. -/
theorem writeGhost_bound {w : NetworkState P.n} (L : ExtendedLabel P.n (Message P.n)) {r : ℕ}
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
theorem roundProjection_gbcaSendGhost (v : ∀ _ : Fin P.n,
    AFW.ProcessRecord P.n) (w : NetworkState P.n) (r : ℕ) (j : Fin P.n) (m : Message P.n) :
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

/-- The gather local state the view assembles from untouched records is the
untouched gather local state: no broadcast instance has returned anything. -/
theorem gatherLocalState_initial (P : Parameters) (X : Type) [DecidableEq X] :
    gatherLocalState P X (LocalState.initial P.n (Gather.Message P.n X)
      (Gather.BaseProcessRecord.initial P.n X))
        (fun _ => LocalState.initial P.n (BRB.Message X) (BRB.ProcessRecord.initial X))
        (fun _ => LocalState.initial P.n (BRB.Message (Gather.AcceptedPairs P.n X))
          (BRB.ProcessRecord.initial (Gather.AcceptedPairs P.n X)))
      = LocalState.initial P.n (Gather.Message P.n X) (Gather.ProcessRecord.initial P.n X) := by
  simp only [gatherLocalState, LocalState.initial_process, broadcastReturnsFor_initial]
  rfl

/-- The broadcast local state the view assembles from an untouched record is
the untouched broadcast local state. -/
theorem broadcastLocalState_initial (P : Parameters) (X : Type) [DecidableEq X] :
    broadcastLocalState P (LocalState.initial P.n (BRB.Message X) (BRB.ProcessRecord.initial X))
      = LocalState.initial P.n (BRB.Message X) (BRB.ProcessRecord.initial X) := by
  unfold broadcastLocalState
  rw [broadcastReturnsFor_initial]
  rfl

/-- The empty sent family projects to the empty sent family. -/
theorem messagesOf_empty {β : Type} (f : Message n → Option β)
    (hf : ∀ a a' b, b ∈ f a → b ∈ f a' → a = a') :
    messagesOf f hf (fun _ => (∅ : Finset (Message n))) = fun _ => (∅ : Finset β) := by
  funext q
  simp [messagesOf]

/-- **Every round of the view is the composed round's initial state**: an untouched round reads as
the initial record in the implementation, and the empty sent projects to the empty sent. -/
theorem roundProjection_init (P : Parameters) (r : ℕ) :
    roundProjection P (protocol P).init.1 (protocol P).init.2.1 r = (GBCA.ByAFW.roundOverBracha P
      r).init :=
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
    InstanceState.initial, messagesOf_empty, gatherLocalState_initial, broadcastLocalState_initial]
  rfl

/-! ### The relation -/

/-- **The round's bound bit is on record wherever its second gather has been called**: a process
whose round-`r` second-gather local state carries an input has passed the round's return-then-call
step, and that step writes the bound bit. This is what the graded return's announced bit rests on,
and it is one of the two clauses of the relation that are not projections of the implementation's
state. -/
def BoundInvariant (P : Parameters) (u : ∀ _ : Fin P.n, AFW.ProcessRecord P.n)
    (w : NetworkState P.n) : Prop :=
  ∀ (r : ℕ) (i : Fin P.n), (((u i).2.roundRecord r).secondGather.process).input ≠ none →
    (w.ghostRecord r).2.2 ≠ none

/-- **The broadcast invariant holds at every instance the view assembles.** It is what identifies
the returned value with the value an implementation receipt quorum carries
(`broadcastReturnsFor_eq_of_quorum`), and it is the second clause of the relation that is not a
projection of the implementation's state. -/
def BroadcastReturnsInvariant (P : Parameters) (u : ∀ _ : Fin P.n, AFW.ProcessRecord P.n)
    (w : NetworkState P.n) : Prop :=
  ∀ (r : ℕ) (k : Fin P.n),
    BRB.Invariant P k (Gather.inputBroadcasts (GBCA.ByAFW.firstGather (roundProjection P u w r)) k)
      ∧
      BRB.Invariant P k (Gather.bindBroadcasts (GBCA.ByAFW.firstGather (roundProjection P u w r)) k)
        ∧
      BRB.Invariant P k (Gather.inputBroadcasts (GBCA.ByAFW.secondGather (roundProjection P u w r))
        k) ∧
      BRB.Invariant P k (Gather.bindBroadcasts (GBCA.ByAFW.secondGather (roundProjection P u w r))
        k)

/-- **The composition relation**: the round loops and the coin oracle are shared, the ABA network is
the DECIDED sets beside the corrupted set, every round's state is the view `roundProjection` of the
implementation's state, the bound bit of a called round is on record, and the broadcast invariant
holds at every instance. The first four conjuncts are unguarded, so they determine the composed
state from the implementation. -/
def ProtocolRelation (P : Parameters) (s : ProtocolState P) (t : ComposedState P) : Prop :=
  (∀ j, (s.1 j).1 = t.2.1 j) ∧
    s.2.2 = t.2.2.2 ∧
    t.2.2.1 = ⟨s.2.1.decidedSent, s.2.1.F⟩ ∧
    t.1 = (fun r => roundProjection P s.1 s.2.1 r) ∧
    BoundInvariant P s.1 s.2.1 ∧
    BroadcastReturnsInvariant P s.1 s.2.1

theorem protocolRelation_mk (P : Parameters) (u : ∀ _ : Fin P.n, AFW.ProcessRecord P.n)
    (w : NetworkState P.n) (o : ℕ → WCC.SpecState P.n) (G : ℕ → GBCA.ByAFW.RoundStateOverBracha P.n)
    (C : ∀ _ : Fin P.n, RoundLoopRecord P.n) (A : ABANetworkState P.n)
    (o' : ℕ → WCC.SpecState P.n) :
    ProtocolRelation P (u, w, o) (G, C, A, o') ↔
      ((∀ j, (u j).1 = C j) ∧ o = o' ∧ A = ⟨w.decidedSent, w.F⟩ ∧
        (G = fun r => roundProjection P u w r) ∧ BoundInvariant P u w ∧ BroadcastReturnsInvariant P
          u w) := Iff.rfl

/-- The bound invariant survives a row that leaves every process's
second-gather local input where it stands and keeps on record every bound bit
already there. -/
theorem boundInvariant_of {u x : ∀ _ : Fin P.n, AFW.ProcessRecord P.n} {w v : NetworkState P.n}
    (hI : BoundInvariant P u w)
    (hx : ∀ i r, (((x i).2.roundRecord r).secondGather.process).input
      = (((u i).2.roundRecord r).secondGather.process).input)
    (hv : ∀ r, (w.ghostRecord r).2.2 ≠ none → (v.ghostRecord r).2.2 ≠ none) :
    BoundInvariant P x v :=
  fun r i hne => hv r (hI r i (by rw [← hx i r]; exact hne))

/-- The initial states are related: every round of the view is the composed
round's initial state, and the broadcast invariant holds at every instance
there. -/
theorem protocolRelation_init (P : Parameters) :
    ProtocolRelation P (protocol P).init (composed P).init := by
  refine ⟨fun _ => rfl, rfl, rfl, ?_, fun _ _ h => absurd rfl h, ?_⟩
  · funext r
    exact (roundProjection_init P r).symm
  · intro r k
    rw [firstGather_roundProjection, secondGather_roundProjection]
    have h1 : firstGatherProjection P (protocol P).init.1 (protocol P).init.2.1 r
        = (Gather.instanceOverBracha P Bool).init := congrArg (fun q => GBCA.ByAFW.firstGather q)
          (roundProjection_init P r)
    have h2 : secondGatherProjection P (protocol P).init.1 (protocol P).init.2.1 r
        = (Gather.instanceOverBracha P (Option Bool)).init := congrArg (fun q =>
          GBCA.ByAFW.secondGather q)
          (roundProjection_init P r)
    rw [h1, h2]
    exact ⟨BRB.Invariant.initial, BRB.Invariant.initial, BRB.Invariant.initial,
      BRB.Invariant.initial⟩


/-! ### Building a transition of the composed system

The composed system's pipeline, read once so that every row of the simulation can be assembled from
its components' rows: the family of rounds beside the round loops, the ABA network and the lifted
oracle. -/

/-- The four components of the gather-based composed system, in parallel. -/
noncomputable def composedExtended (P : Parameters) :
    System (ComposedState P) (ExtendedLabel P.n) :=
  (roundFamilyOverBracha P).parallel
    ((System.synchronisedProduct (roundLoopProgram P)).parallel
      ((ABANetwork P).parallel (coinOverRoundAlphabet P)))

/-- The composed group: the rendezvous alphabet hidden, read back over
`Label n`. -/
noncomputable def composedHidden (P : Parameters) :
    System (ComposedState P) (Label P.n) :=
  ((composedExtended P).abstract (networkEventLabels P.n)).relabel

theorem composed_eq (P : Parameters) :
    composed P = (composedHidden P).abstract (Label.hiddenAPI P.n) := rfl

/-- The round-`r` state moves on a label it owns. -/
theorem roundFamilyOverBracha_owned (P : Parameters) (G : ℕ → GBCA.ByAFW.RoundStateOverBracha P.n)
  (r :
  ℕ)
    {L : ExtendedLabel P.n} (hL : roundOwnsLabel L = some r) {q : GBCA.ByAFW.RoundStateOverBracha
      P.n}
    (h : (GBCA.ByAFW.roundOverBracha P r).step (G r) L (PMF.pure q)) :
    (roundFamilyOverBracha P).step G L (PMF.pure (Function.update G r q)) := by
  rw [roundFamilyOverBracha, System.family_step_iff]
  exact Or.inr (Or.inl ⟨r, hL, PMF.pure q, h, by rw [PMF.pure_map]⟩)

/-- An owned label whose round stands still. -/
theorem roundFamilyOverBracha_owned_id (P : Parameters) (G : ℕ → GBCA.ByAFW.RoundStateOverBracha
  P.n) (r
  : ℕ)
    {L : ExtendedLabel P.n} (hL : roundOwnsLabel L = some r)
    (h : (GBCA.ByAFW.roundOverBracha P r).step (G r) L (PMF.pure (G r))) :
    (roundFamilyOverBracha P).step G L (PMF.pure G) := by
  have hstep := roundFamilyOverBracha_owned P G r hL h
  rwa [Function.update_eq_self] at hstep

/-- The round-`r` state takes one of its own silent rules. -/
theorem roundFamilyOverBracha_tau (P : Parameters) (G : ℕ → GBCA.ByAFW.RoundStateOverBracha P.n) (r
  : ℕ)
    {q : GBCA.ByAFW.RoundStateOverBracha P.n}
    (h : (GBCA.ByAFW.roundOverBracha P r).step (G r) (Sum.inl Label.tau) (PMF.pure q)) :
    (roundFamilyOverBracha P).step G (Sum.inl Label.tau) (PMF.pure (Function.update G r q)) := by
  rw [roundFamilyOverBracha, System.family_step_iff]
  exact Or.inl ⟨rfl, r, PMF.pure q, h, by rw [PMF.pure_map]⟩

/-- A label no round owns and no broadcast: the family idles. -/
theorem roundFamilyOverBracha_idle (P : Parameters) (G : ℕ → GBCA.ByAFW.RoundStateOverBracha P.n) {L
  :
  ExtendedLabel P.n}
    (hτ : L ≠ Silent.τ) (hown : roundOwnsLabel L = none) (hf : ¬ isFailLabel L) :
    (roundFamilyOverBracha P).step G L (PMF.pure G) := by
  rw [roundFamilyOverBracha, System.family_step_iff]
  exact Or.inr (Or.inr (Or.inr ⟨hτ, hown, hf, rfl⟩))

/-- Corruption is broadcast to every round's coordinate. -/
theorem roundFamilyOverBracha_fail (P : Parameters) (G : ℕ → GBCA.ByAFW.RoundStateOverBracha P.n) (k
  :
  Fin P.n) :
    (roundFamilyOverBracha P).step G (Sum.inl (Label.fail k))
      (PMF.pure (fun r => corruptionOverBracha P (Sum.inl (Label.fail k)) (G r))) := by
  rw [roundFamilyOverBracha, System.family_step_iff]
  exact Or.inr (Or.inr (Or.inl ⟨by simp, rfl, trivial, rfl⟩))

/-- The three components beside the graded-agreement family move together on a visible label, the
oracle's successor left free. -/
theorem contextStep (P : Parameters) {C C' : ∀ _ : Fin P.n, RoundLoopRecord P.n}
    {A A' : ABANetworkState P.n} {o : ℕ → WCC.SpecState P.n}
    {ν : PMF (ℕ → WCC.SpecState P.n)} {L : ExtendedLabel P.n} (hL : L ≠ Silent.τ)
    (hC : ∀ i, RoundLoopStep P i (C i) L (PMF.pure (C' i)))
    (hA : ABANetworkStep P A L (PMF.pure A'))
    (hW : (coinOverRoundAlphabet P).step o L ν) :
    ((System.synchronisedProduct (roundLoopProgram P)).parallel ((ABANetwork P).parallel
      (coinOverRoundAlphabet P))).step
      (C, A, o) L (prodPMF (PMF.pure C') (prodPMF (PMF.pure A') ν)) := by
  rw [System.parallel_step]
  refine Or.inl ⟨hL, PMF.pure C', prodPMF (PMF.pure A') ν, roundLoopProduct_pure hL hC, ?_, rfl⟩
  rw [System.parallel_step]
  exact Or.inl ⟨hL, PMF.pure A', ν, hA, hW, rfl⟩

/-- Build a joint transition of the four components on a visible label, the
oracle's successor left free. -/
theorem composedExtended_visible_step (P : Parameters) {G G' : ℕ → GBCA.ByAFW.RoundStateOverBracha P.n}
    {C C' : ∀ _ : Fin P.n, RoundLoopRecord P.n} {A A' : ABANetworkState P.n}
    {o : ℕ → WCC.SpecState P.n} {ν : PMF (ℕ → WCC.SpecState P.n)} {L : ExtendedLabel P.n}
    (hL : L ≠ Silent.τ)
    (hG : (roundFamilyOverBracha P).step G L (PMF.pure G'))
    (hC : ∀ i, RoundLoopStep P i (C i) L (PMF.pure (C' i)))
    (hA : ABANetworkStep P A L (PMF.pure A'))
    (hW : (coinOverRoundAlphabet P).step o L ν) :
    (composedExtended P).step (G, C, A, o) L
      (prodPMF (PMF.pure G') (prodPMF (PMF.pure C') (prodPMF (PMF.pure A') ν))) := by
  rw [composedExtended, System.parallel_step]
  exact Or.inl ⟨hL, PMF.pure G', prodPMF (PMF.pure C') (prodPMF (PMF.pure A') ν),
    hG, contextStep P hL hC hA hW, rfl⟩

/-- Build a silent transition of the four components from a round's own. -/
theorem composedExtended_tau_overBracha (P : Parameters) {G G' : ℕ → GBCA.ByAFW.RoundStateOverBracha
  P.n}
    {C : ∀ _ : Fin P.n, RoundLoopRecord P.n} {A : ABANetworkState P.n}
    {o : ℕ → WCC.SpecState P.n}
    (hG : (roundFamilyOverBracha P).step G (Sum.inl Label.tau) (PMF.pure G')) :
    (composedExtended P).step (G, C, A, o) (Sum.inl Label.tau) (PMF.pure (G', C, A, o)) := by
  rw [composedExtended, System.parallel_step]
  refine Or.inr (Or.inl ⟨rfl, PMF.pure G', hG, ?_⟩)
  rw [prodPMF_pure_pure]

/-- Build a silent transition of the four components from an ABA network injection. -/
theorem composedExtended_tau_ABANetwork (P : Parameters) {G : ℕ → GBCA.ByAFW.RoundStateOverBracha
  P.n}
    {C : ∀ _ : Fin P.n, RoundLoopRecord P.n} {A A' : ABANetworkState P.n}
    {o : ℕ → WCC.SpecState P.n}
    (hA : ABANetworkStep P A (Sum.inl Label.tau) (PMF.pure A')) :
    (composedExtended P).step (G, C, A, o) (Sum.inl Label.tau) (PMF.pure (G, C, A', o)) := by
  rw [composedExtended, System.parallel_step]
  refine Or.inr (Or.inr ⟨rfl,
    prodPMF (PMF.pure C) (prodPMF (PMF.pure A') (PMF.pure o)), ?_, ?_⟩)
  · rw [System.parallel_step]
    refine Or.inr (Or.inr ⟨rfl, prodPMF (PMF.pure A') (PMF.pure o), ?_, rfl⟩)
    rw [System.parallel_step]
    exact Or.inr (Or.inl ⟨rfl, PMF.pure A', hA, rfl⟩)
  · rw [prodPMF_pure_pure, prodPMF_pure_pure, prodPMF_pure_pure]

/-! ### The two hiding frames -/

theorem composedHidden_step_iff (P : Parameters) (q : ComposedState P) (l : Label P.n)
    (μ : PMF (ComposedState P)) :
    (composedHidden P).step q l μ ↔
      (l = .tau ∧ ∃ e : NetworkEvent P.n, (composedExtended P).step q (Sum.inr e) μ) ∨
      (composedExtended P).step q (Sum.inl l) μ := by
  constructor
  · rintro (⟨hτ, l', ⟨e, rfl⟩, hstep⟩ | ⟨-, hstep⟩)
    · exact Or.inl ⟨Sum.inl_injective hτ, e, hstep⟩
    · exact Or.inr hstep
  · rintro (⟨rfl, e, hstep⟩ | hstep)
    · exact Or.inl ⟨rfl, _, inr_mem_networkEventLabels e, hstep⟩
    · exact Or.inr ⟨inl_notMem_networkEventLabels l, hstep⟩

theorem composedHidden_of_event (P : Parameters) {q : ComposedState P}
    (e : NetworkEvent P.n) {μ : PMF (ComposedState P)}
    (h : (composedExtended P).step q (Sum.inr e) μ) :
    (composedHidden P).step q Label.tau μ :=
  (composedHidden_step_iff P _ _ _).mpr (Or.inl ⟨rfl, e, h⟩)

theorem composedHidden_of_tau (P : Parameters) {q : ComposedState P}
    {μ : PMF (ComposedState P)}
    (h : (composedExtended P).step q (Sum.inl Label.tau) μ) :
    (composedHidden P).step q Label.tau μ :=
  (composedHidden_step_iff P _ _ _).mpr (Or.inr h)

/-! ### Transposing one written record

A row writes the acting process's round record, so the local state vector the
view reads becomes a one-point update of the old one. Each lemma below is that
observation at one component, stated over the `ite` that reading a written
record produces. -/

section Locals

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
    (fun i => (if i = j then sr else Y i).firstGatherBindBroadcasts k)
      = Function.update (fun i => (Y i).firstGatherBindBroadcasts k) j (sr.firstGatherBindBroadcasts
        k) := by
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

end Locals

/-! ### Runs of the graded-agreement family

Three rows of the implementation are answered by two transitions of the composed system: the
return-then-call step by the hidden events `firstGatherReturn` and `secondGatherCall`, the graded
return by the hidden event `secondGatherReturn` and the visible `retG`, and a delivery completing a
receipt quorum by the hidden events `deliver` and `inputBroadcastRet` (or `bindRet`). The builders
below carry a run of one round to the graded-agreement family, and a run of that family to the
composed group. -/

/-- A silent run of one round is a silent run of the graded-agreement family at that coordinate. -/
theorem roundFamilyOverBracha_silentRun (P : Parameters) {G : ℕ → GBCA.ByAFW.RoundStateOverBracha
  P.n}
  {r : ℕ}
    {q : GBCA.ByAFW.RoundStateOverBracha P.n} (h : (GBCA.ByAFW.roundOverBracha P r).weakLSilent (G
      r) q) :
    (roundFamilyOverBracha P).weakLSilent G (Function.update G r q) := by
  rw [roundFamilyOverBracha]
  exact System.weakLSilent_family roundOwnsLabel isFailLabel (corruptionOverBracha P) h

/-- A run of one round on a label that round owns is a weak transition of the graded-agreement
family at that coordinate. -/
theorem roundFamilyOverBracha_weakStep (P : Parameters) {G : ℕ → GBCA.ByAFW.RoundStateOverBracha
  P.n} {r
  : ℕ}
    {L : ExtendedLabel P.n} {q : GBCA.ByAFW.RoundStateOverBracha P.n} (hL : roundOwnsLabel L = some
      r)
    (h : (GBCA.ByAFW.roundOverBracha P r).weakLStep (G r) L q) :
    (roundFamilyOverBracha P).weakLStep G L (Function.update G r q) := by
  rw [roundFamilyOverBracha]
  exact System.weakLStep_family roundOwnsLabel isFailLabel (corruptionOverBracha P) hL h

/-- **A silent run of the graded-agreement family is a silent weak transition of the composed
group**: the three other components stand at their states throughout. -/
theorem composedHidden_weakTau (P : Parameters) {G G' : ℕ → GBCA.ByAFW.RoundStateOverBracha P.n}
    (C : ∀ _ : Fin P.n, RoundLoopRecord P.n) (A : ABANetworkState P.n)
    (o : ℕ → WCC.SpecState P.n) (h : (roundFamilyOverBracha P).weakLSilent G G') :
    weakTau (composedHidden P) (PMF.pure ((G, C, A, o) : ComposedState P))
      (PMF.pure ((G', C, A, o) : ComposedState P)) := by
  have h1 : weakTau (roundFamilyOverBracha P) (PMF.pure G) (PMF.pure G') :=
    weakTau_of_weakLSilent (roundFamilyOverBracha P) (roundFamilyOverBracha_isLTS P) h
  have h2 := weakTau_parallel_left (roundFamilyOverBracha P)
    ((System.synchronisedProduct (roundLoopProgram P)).parallel ((ABANetwork P).parallel
      (coinOverRoundAlphabet P)))
    ((C, A, o)) h1
  rw [prodPMF_pure_pure, prodPMF_pure_pure] at h2
  exact weakTau_relabel (weakTau_abstract (composedExtended P) (networkEventLabels P.n) h2)

/-- **A visible label the graded-agreement family answers by a run** and the three other components
by one transition each is a weak transition of the composed group. The oracle's successor is left
free, so the resulting distribution has the shape a probabilistic answer consumes. -/
theorem composedHidden_weakStep (P : Parameters) {G G' : ℕ → GBCA.ByAFW.RoundStateOverBracha P.n}
    {C C' : ∀ _ : Fin P.n, RoundLoopRecord P.n} {A A' : ABANetworkState P.n}
    {o : ℕ → WCC.SpecState P.n} {ν : PMF (ℕ → WCC.SpecState P.n)} {l : Label P.n}
    (hl : l ≠ Label.tau)
    (hG : (roundFamilyOverBracha P).weakLStep G (Sum.inl l) G')
    (hC : ∀ i, RoundLoopStep P i (C i) (Sum.inl l) (PMF.pure (C' i)))
    (hA : ABANetworkStep P A (Sum.inl l) (PMF.pure A'))
    (hW : (coinOverRoundAlphabet P).step o (Sum.inl l) ν) :
    weakStep (composedHidden P) (PMF.pure ((G, C, A, o) : ComposedState P)) l
      (prodPMF (PMF.pure G') (prodPMF (PMF.pure C') (prodPMF (PMF.pure A') ν))) := by
  have hL : (Sum.inl l : ExtendedLabel P.n) ≠ Silent.τ := by
    rw [extendedLabel_tau]
    simpa using hl
  have h1 : weakStep (roundFamilyOverBracha P) (PMF.pure G) (Sum.inl l) (PMF.pure G') :=
    weakStep_of_weakLStep (roundFamilyOverBracha P) (roundFamilyOverBracha_isLTS P) hL hG
  have h2 := weakStep_parallel_sync (roundFamilyOverBracha P)
    ((System.synchronisedProduct (roundLoopProgram P)).parallel ((ABANetwork P).parallel
      (coinOverRoundAlphabet P)))
    hL h1 (contextStep P hL hC hA hW)
  rw [prodPMF_pure_pure] at h2
  exact weakStep_relabel
    (weakStep_abstract (composedExtended P) (networkEventLabels P.n) (by simp) h2)

end AFW

end ABA
end PLTS
