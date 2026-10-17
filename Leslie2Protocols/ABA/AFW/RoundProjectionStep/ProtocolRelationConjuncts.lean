/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sathiya / Claude
-/

import Leslie2Protocols.ABA.AFW.RoundProjectionStep.ProjectionAfterOneWrite

/-!
# The conjuncts of the protocol relation that are not projections

`AFW.ProtocolRelation` relates every round of the composed family to the projection
`AFW.roundProjection`. Four of its conjuncts are not projections: the rounds of the family's map
are the started rounds, a round outside the started rounds is empty in the protocol state, every
process of the corrupted set has a replaced program, and `BoundInvariant`. This file carries them
across a transition.

## The started rounds

The empty-rounds conjunct, read backwards, places every round a transition touches among the
started rounds: a round at which some process holds variables other than the initial ones, some
process has sent, or the ghost holds a value is a started round
(`mem_startedRounds_of_roundVariables`, `mem_startedRounds_of_sent`, `mem_startedRounds_of_ghost`).
A process with an unreplaced program lies outside the corrupted set, so its graded-agreement call
records the called round (`startedRounds_recordStartedRound`).

## The relation across a transition

`protocolRelation_sameRounds` carries the relation across a transition after which the family's
map has the same rounds and every process holds variables at the same rounds, and
`protocolRelation_noRound` across a transition that moves no round. `protocolRelation_oneRound`
carries it across a transition that moves round `r` alone, the family after it given through its
accessor and the rounds of its map, and `protocolRelation_setInstanceState` across such a
transition where the family sets round `r` to the projection of round `r` after the transition.
The call of a process outside the corrupted set inserts its round both among the started rounds
and in the family's map. Every other transition at round `r` reads variables, messages or a ghost
of round `r`, so `r` is a started round by the lemmas above, and inserting it changes neither
set.

## The bound invariant across a transition

`boundInvariant_writeGhost` carries `BoundInvariant` across a transition that leaves the four fields
it reads and writes the ghost, and `boundInvariant_writeRoundVariables` across a write of one
process's variables of one round that leaves the four fields. The four transitions that write one
of the fields each have their own lemma: `boundInvariant_firstGatherReturn`,
`boundInvariant_secondGatherCall`, `boundInvariant_secondGatherReturn` and `boundInvariant_retG`.

## A round transition

A round transition at round `r` leaves the variables the process holds at every other round
(`roundVariablesMap_lookup_roundStep`). A send, a round event and the graded return fire at
variables of round `r` other than the initial ones (`roundVariables_ne_initial_gbcaSend`,
`roundVariables_ne_initial_gbcaRoundEvent`, `roundVariables_ne_initial_retG`), which places `r`
among the started rounds. `boundInvariant_roundStep` carries `BoundInvariant` across every round
transition, through the lemma above for the field the transition writes.
-/

namespace PLTS
namespace ABA
namespace AFW

open Implementation hiding NetworkEvent ExtendedLabel
open Composition GBCA.ByABDY

variable {P : Parameters}

/-! ### The started rounds -/

section StartedRounds

variable {u : ∀ _ : Fin P.n, AFW.ProcessVariables P.n} {w : NetworkState P.n}
  {o o' : InstanceFamilyState (WCC.SpecState.initial P.n) (WCC.failAct P)}
  {G : RoundFamilyOverBrachaState P} {C : ∀ _ : Fin P.n, RoundLoopVariables P.n}
  {A : ABANetworkState P.n}

/-- A process's variables of a round outside the started rounds are the initial ones. -/
theorem roundVariables_of_notMem_startedRounds (hR : ProtocolRelation P (u, w, o) (G, C, A, o'))
    {r : ℕ} (hr : r ∉ w.startedRounds) (j : Fin P.n) :
    (u j).2.roundVariables r = RoundVariables.initial P.n := by
  obtain ⟨-, -, -, -, -, hUntouched, -, -⟩ := (protocolRelation_mk P _ _ _ _ _ _ _).mp hR
  simp only [Implementation.RoundVariablesMap.roundVariables,
    Finmap.lookup_eq_none.mpr ((hUntouched r hr).2.2 j), Option.getD_none]
  rfl

/-- A round at which some process holds variables other than the initial ones is a started
round. -/
theorem mem_startedRounds_of_roundVariables (hR : ProtocolRelation P (u, w, o) (G, C, A, o'))
    {r : ℕ} {j : Fin P.n} (h : (u j).2.roundVariables r ≠ RoundVariables.initial P.n) :
    r ∈ w.startedRounds := by
  by_contra hr
  exact h (roundVariables_of_notMem_startedRounds hR hr j)

/-- A round at which some process has sent is a started round. -/
theorem mem_startedRounds_of_sent (hR : ProtocolRelation P (u, w, o) (G, C, A, o')) {r : ℕ}
    {k : Fin P.n} {m : Message P.n} (h : m ∈ w.sent r k) : r ∈ w.startedRounds := by
  obtain ⟨-, -, -, -, -, hUntouched, -, -⟩ := (protocolRelation_mk P _ _ _ _ _ _ _).mp hR
  by_contra hr
  rw [(hUntouched r hr).1 k] at h
  exact Finset.notMem_empty m h

/-- A round whose ghost holds a value is a started round. -/
theorem mem_startedRounds_of_ghost (hR : ProtocolRelation P (u, w, o) (G, C, A, o')) {r : ℕ}
    (h : w.ghost r ≠ (none, none, none)) : r ∈ w.startedRounds := by
  obtain ⟨-, -, -, -, -, hUntouched, -, -⟩ := (protocolRelation_mk P _ _ _ _ _ _ _).mp hR
  by_contra hr
  exact h (hUntouched r hr).2.1

/-- A round whose ghost holds a bound bit is a started round. -/
theorem mem_startedRounds_of_bound (hR : ProtocolRelation P (u, w, o) (G, C, A, o')) {r : ℕ}
    {b : Bool} (h : (w.ghost r).2.2 = some b) : r ∈ w.startedRounds :=
  mem_startedRounds_of_ghost hR fun hg => by rw [hg] at h; cases h

/-- The started rounds are the rounds of the family's map. -/
theorem mem_keys_of_mem_startedRounds (hR : ProtocolRelation P (u, w, o) (G, C, A, o')) {r : ℕ}
    (h : r ∈ w.startedRounds) : r ∈ G.instanceMap.keys := by
  obtain ⟨-, -, -, hKeys, -, -, -, -⟩ := (protocolRelation_mk P _ _ _ _ _ _ _).mp hR
  rwa [hKeys]

/-- A process with an unreplaced program lies outside the corrupted set. -/
theorem notMem_F_of_corrupted (hR : ProtocolRelation P (u, w, o) (G, C, A, o')) {j : Fin P.n}
    (h : (u j).1.corrupted = false) : j ∉ w.F := by
  obtain ⟨-, -, -, -, -, -, hCorrupted, -⟩ := (protocolRelation_mk P _ _ _ _ _ _ _).mp hR
  intro hj
  have hc := hCorrupted j hj
  rw [h] at hc
  exact Bool.false_ne_true hc

/-- The graded-agreement call of a process with an unreplaced program records the called round
among the started rounds. -/
theorem startedRounds_recordStartedRound (hR : ProtocolRelation P (u, w, o) (G, C, A, o'))
    {j : Fin P.n} (h : (u j).1.corrupted = false) (r : ℕ) :
    (w.recordStartedRound r j).startedRounds = insert r w.startedRounds :=
  recordStartedRound_startedRounds_of_notMem w (notMem_F_of_corrupted hR h)

end StartedRounds

/-! ### The relation across a transition

In each lemma the protocol state after the transition is `(x, w', o')` and the composed state
`(G', C', A', o')`, with the composed round loops and the ABA network after the transition given as
`C'` and `A'`. -/

section Relation

variable {u x : ∀ _ : Fin P.n, AFW.ProcessVariables P.n} {w w' : NetworkState P.n}
  {o o' : InstanceFamilyState (WCC.SpecState.initial P.n) (WCC.failAct P)}
  {G G' : RoundFamilyOverBrachaState P} {C C' : ∀ _ : Fin P.n, RoundLoopVariables P.n}
  {A A' : ABANetworkState P.n}

/-- **The relation across a transition that keeps the rounds**: the family's map has the same
rounds, every round of the family after the transition is the projection after it, the started
rounds, the sent sets and the ghosts stand, every process holds variables at the same rounds, and
every process of the corrupted set after the transition has a replaced program. -/
theorem protocolRelation_sameRounds (hR : ProtocolRelation P (u, w, o) (G, C, A, o))
    (hC' : ∀ j, (x j).1 = C' j) (hA' : A' = ⟨w'.decidedSent, w'.F, w'.startedRounds⟩)
    (hKeys : G'.instanceMap.keys = G.instanceMap.keys)
    (hG' : ∀ r, G' r = roundProjection P x w' r)
    (hStarted : w'.startedRounds = w.startedRounds)
    (hsent : ∀ r, w'.sent r = w.sent r) (hghost : ∀ r, w'.ghost r = w.ghost r)
    (hmap : ∀ j, (x j).2.roundVariablesMap = (u j).2.roundVariablesMap)
    (hCorrupted : ∀ j ∈ w'.F, (x j).1.corrupted = true) (hB : BoundInvariant P x w') :
    ProtocolRelation P (x, w', o') (G', C', A', o') := by
  obtain ⟨-, -, -, hKeys₀, -, hUntouched, -, -⟩ := (protocolRelation_mk P _ _ _ _ _ _ _).mp hR
  refine (protocolRelation_mk P _ _ _ _ _ _ _).mpr ⟨hC', rfl, hA', by rw [hKeys, hKeys₀, hStarted],
    hG', fun r hr => ?_, hCorrupted, hB⟩
  obtain ⟨h1, h2, h3⟩ := hUntouched r (by rwa [hStarted] at hr)
  exact ⟨fun j => by rw [hsent r]; exact h1 j, by rw [hghost r]; exact h2,
    fun j => by rw [hmap j]; exact h3 j⟩

/-- **The relation across a transition that moves no round**: the family stands, every process
holds the same round variables and the same replacement flag, and the sent sets, the ghosts, the
corrupted set and the started rounds stand. -/
theorem protocolRelation_noRound (hR : ProtocolRelation P (u, w, o) (G, C, A, o))
    (hC' : ∀ j, (x j).1 = C' j) (hA' : A' = ⟨w'.decidedSent, w'.F, w'.startedRounds⟩)
    (hmap : ∀ j, (x j).2.roundVariablesMap = (u j).2.roundVariablesMap)
    (hReplacement : ∀ j, (x j).1.corrupted = (u j).1.corrupted)
    (hsent : ∀ r, w'.sent r = w.sent r) (hghost : ∀ r, w'.ghost r = w.ghost r)
    (hF : w'.F = w.F) (hStarted : w'.startedRounds = w.startedRounds) :
    ProtocolRelation P (x, w', o') (G, C', A', o') := by
  obtain ⟨-, -, -, -, hG, -, hCorrupted, hB⟩ := (protocolRelation_mk P _ _ _ _ _ _ _).mp hR
  have hst : ∀ j r, (x j).2.roundVariables r = (u j).2.roundVariables r := fun j r => by
    simp only [Implementation.RoundVariablesMap.roundVariables, hmap j]
  refine protocolRelation_sameRounds hR hC' hA' rfl (fun r => ?_) hStarted hsent hghost hmap
    (fun j hj => ?_) (boundInvariant_of_roundVariables hB hst fun r => ⟨Sum.inl Label.tau, w,
      by rw [hghost r]; rfl⟩)
  · rw [hG r, roundProjection_network_congr (hsent r) hF (hghost r)]
    exact (roundProjection_congr (fun j => hst j r)).symm
  · rw [hReplacement j]; exact hCorrupted j (by rwa [hF] at hj)

/-- **The relation across a transition that moves round `r` alone**: the family's map gains `r`
and every round of the family after the transition is the projection after it, the started rounds
gain `r`, the corrupted set and every process's replacement flag stand, and the sent sets, the
ghosts and every process's variables of every other round stand. -/
theorem protocolRelation_oneRound (hR : ProtocolRelation P (u, w, o) (G, C, A, o)) (r : ℕ)
    (hC' : ∀ j, (x j).1 = C' j) (hA' : A' = ⟨w'.decidedSent, w'.F, w'.startedRounds⟩)
    (hKeys : G'.instanceMap.keys = insert r G.instanceMap.keys)
    (hG' : ∀ r', G' r' = roundProjection P x w' r')
    (hStarted : w'.startedRounds = insert r w.startedRounds) (hF : w'.F = w.F)
    (hsent : ∀ r', r' ≠ r → w'.sent r' = w.sent r')
    (hghost : ∀ r', r' ≠ r → w'.ghost r' = w.ghost r')
    (hmap : ∀ j r', r' ≠ r →
      (x j).2.roundVariablesMap.lookup r' = (u j).2.roundVariablesMap.lookup r')
    (hReplacement : ∀ j, (x j).1.corrupted = (u j).1.corrupted) (hB : BoundInvariant P x w') :
    ProtocolRelation P (x, w', o') (G', C', A', o') := by
  obtain ⟨-, -, -, hKeys₀, -, hUntouched, hCorrupted, -⟩ :=
    (protocolRelation_mk P _ _ _ _ _ _ _).mp hR
  refine (protocolRelation_mk P _ _ _ _ _ _ _).mpr ⟨hC', rfl, hA', ?_, hG', fun r' hr' => ?_,
    fun j hj => ?_, hB⟩
  · rw [hKeys, hKeys₀, hStarted]
  · have hne : r' ≠ r := fun h => hr' (by rw [h, hStarted]; exact Finset.mem_insert_self r _)
    have hold : r' ∉ w.startedRounds := fun h =>
      hr' (by rw [hStarted]; exact Finset.mem_insert_of_mem h)
    obtain ⟨h1, h2, h3⟩ := hUntouched r' hold
    refine ⟨fun j => by rw [hsent r' hne]; exact h1 j, by rw [hghost r' hne]; exact h2,
      fun j => ?_⟩
    rw [← Finmap.lookup_eq_none, hmap j r' hne, Finmap.lookup_eq_none]
    exact h3 j
  · rw [hReplacement j]; exact hCorrupted j (by rwa [hF] at hj)

/-- **The relation across a transition that moves round `r` alone, with the family's round `r`
set to the projection of round `r` after it.** Every other round of the family reads the projection
before the transition, which the transition leaves where it stands. -/
theorem protocolRelation_setInstanceState (hR : ProtocolRelation P (u, w, o) (G, C, A, o))
    (r : ℕ) {X : GBCA.ByAFW.RoundStateOverBracha P.n} (hX : roundProjection P x w' r = X)
    (hC' : ∀ j, (x j).1 = C' j) (hA' : A' = ⟨w'.decidedSent, w'.F, w'.startedRounds⟩)
    (hStarted : w'.startedRounds = insert r w.startedRounds) (hF : w'.F = w.F)
    (hsent : ∀ r', r' ≠ r → w'.sent r' = w.sent r')
    (hghost : ∀ r', r' ≠ r → w'.ghost r' = w.ghost r')
    (hmap : ∀ j r', r' ≠ r →
      (x j).2.roundVariablesMap.lookup r' = (u j).2.roundVariablesMap.lookup r')
    (hReplacement : ∀ j, (x j).1.corrupted = (u j).1.corrupted) (hB : BoundInvariant P x w') :
    ProtocolRelation P (x, w', o') (G.setInstanceState r X, C', A', o') := by
  obtain ⟨-, -, -, -, hG, -, -, -⟩ := (protocolRelation_mk P _ _ _ _ _ _ _).mp hR
  refine protocolRelation_oneRound hR r hC' hA' (InstanceFamilyState.keys_setInstanceState G r X)
    (fun r' => ?_) hStarted hF hsent hghost hmap hReplacement hB
  by_cases hr : r' = r
  · subst hr; rw [InstanceFamilyState.setInstanceState_apply_same, hX]
  · rw [InstanceFamilyState.setInstanceState_apply_ne _ _ hr, hG r',
      roundProjection_network_congr (hsent r' hr) hF (hghost r' hr)]
    refine (roundProjection_congr fun j => ?_).symm
    simp only [Implementation.RoundVariablesMap.roundVariables, hmap j r' hr]

end Relation

/-! ### The bound invariant across a transition

`BoundInvariant` reads four fields of the round variables: the candidate, the second gather's input
and return flag, and the graded outcome. A transition that leaves the four and writes the ghost
keeps the invariant. The first gather's return writes the candidate together with the first
gather's core in the ghost, the second gather's call writes its input at variables holding a
candidate, the second gather's return writes the graded outcome at variables whose second gather
has been called, and the round's return clears the graded outcome together with the write of the
bound bit in the ghost. -/

section Invariants

variable {u x : ∀ _ : Fin P.n, AFW.ProcessVariables P.n} {w v : NetworkState P.n}
  {j : Fin P.n} {p : RoundVariablesMap P.n}

/-- The bound invariant is preserved by a transition that leaves the four fields it reads
unchanged and writes the ghost through `AFW.ghostStep`. -/
theorem boundInvariant_writeGhost (hI : BoundInvariant P u w)
    (hcand : ∀ i r, ((x i).2.roundVariables r).candidate = ((u i).2.roundVariables r).candidate)
    (hinput : ∀ i r, (((x i).2.roundVariables r).secondGather.processVariables).input
      = (((u i).2.roundVariables r).secondGather.processVariables).input)
    (hreturned : ∀ i r, (((x i).2.roundVariables r).secondGather.processVariables).returned
      = (((u i).2.roundVariables r).secondGather.processVariables).returned)
    (hout : ∀ i r, ((x i).2.roundVariables r).output = ((u i).2.roundVariables r).output)
    (hv : ∀ r, v.ghost r = w.ghost r)
    (L : Implementation.ExtendedLabel P.n (Message P.n) (RoundEvent P.n)) :
    BoundInvariant P x (v.writeGhost (ghostStep P) L) :=
  boundInvariant_of hI hcand hinput hreturned hout (ghost_writeGhost_of_eq hv L)

/-- One field of the round variables after process `j` writes its variables of round `r`, where
the written field is the field before the write. -/
private theorem field_update {α : Type} (f : RoundVariables P.n → α) (hu : (u j).2 = p)
    (c' : RoundLoopVariables P.n) (r : ℕ) (sr : RoundVariables P.n)
    (hf : f sr = f (p.roundVariables r)) (i : Fin P.n) (r' : ℕ) :
    f ((Function.update u j (c', p.setRoundVariables r sr) i).2.roundVariables r')
      = f ((u i).2.roundVariables r') := by
  by_cases hr : r' = r
  · subst hr
    rw [roundVariables_update_self hu]
    split_ifs with hi
    · subst hi; rw [hf, hu]
    · rfl
  · rw [roundVariables_update_ne hu hr]

/-- The bound invariant across a write of process `j`'s variables of round `r` that leaves the
four fields the invariant reads, with the ghost write of any label. -/
theorem boundInvariant_writeRoundVariables (hI : BoundInvariant P u w) (hu : (u j).2 = p)
    (c' : RoundLoopVariables P.n) (r : ℕ) (sr : RoundVariables P.n)
    (hv : ∀ r, v.ghost r = w.ghost r)
    (L : Implementation.ExtendedLabel P.n (Message P.n) (RoundEvent P.n))
    (hcand : sr.candidate = (p.roundVariables r).candidate)
    (hinput : sr.secondGather.processVariables.input
      = ((p.roundVariables r).secondGather.processVariables).input)
    (hreturned : sr.secondGather.processVariables.returned
      = ((p.roundVariables r).secondGather.processVariables).returned)
    (hout : sr.output = (p.roundVariables r).output) :
    BoundInvariant P (Function.update u j (c', p.setRoundVariables r sr))
      (v.writeGhost (ghostStep P) L) :=
  boundInvariant_writeGhost hI (field_update (·.candidate) hu c' r sr hcand)
    (field_update (·.secondGather.processVariables.input) hu c' r sr hinput)
    (field_update (·.secondGather.processVariables.returned) hu c' r sr hreturned)
    (field_update (·.output) hu c' r sr hout) hv L

/-- **The bound invariant across the first gather's return**: process `j` records a candidate in
its variables of round `r` and leaves the three other fields, and the ghost write of the first
gather's return records the first gather's core of round `r`. -/
theorem boundInvariant_firstGatherReturn (hI : BoundInvariant P u w) (hu : (u j).2 = p)
    (c' : RoundLoopVariables P.n) (r : ℕ) (sr : RoundVariables P.n) (y : Option Bool)
    (hv : ∀ r, v.ghost r = w.ghost r) (hcand : sr.candidate ≠ none)
    (hinput : sr.secondGather.processVariables.input
      = ((p.roundVariables r).secondGather.processVariables).input)
    (hreturned : sr.secondGather.processVariables.returned
      = ((p.roundVariables r).secondGather.processVariables).returned)
    (hout : sr.output = (p.roundVariables r).output) :
    BoundInvariant P (Function.update u j (c', p.setRoundVariables r sr))
      (v.writeGhost (ghostStep P) (Sum.inr (.gbcaRoundEvent r j (.firstGatherReturn y)))) := by
  have hold : p.roundVariables r = (u j).2.roundVariables r := by rw [hu]
  refine boundInvariant_update hI hu c' r sr (ghost_writeGhost_of_eq hv _) (fun _ => ?_)
    (fun hr ho => ?_) (fun h => ?_) (fun _ => hcand)
  · rw [writeGhost_ghost_self v rfl, ghostStep_firstGatherReturn]
    exact Option.some_ne_none _
  · rw [hreturned, hold] at hr
    rw [hout, hold] at ho
    exact writeGhost_bound _ (by rw [hv r]; exact hI.bound_of_returned r j hr ho)
  · rw [hout, hold] at h
    rw [hinput, hold]
    exact hI.secondGatherInput_of_output r j h

/-- **The bound invariant across the second gather's call**: process `j` writes the second
gather's input in its variables of round `r`, which hold a candidate, and leaves the three other
fields, with the ghost write of any label. -/
theorem boundInvariant_secondGatherCall (hI : BoundInvariant P u w) (hu : (u j).2 = p)
    (c' : RoundLoopVariables P.n) (r : ℕ) (sr : RoundVariables P.n)
    (hv : ∀ r, v.ghost r = w.ghost r)
    (L : Implementation.ExtendedLabel P.n (Message P.n) (RoundEvent P.n))
    (hcand : sr.candidate = (p.roundVariables r).candidate)
    (hc : (p.roundVariables r).candidate ≠ none)
    (hinput : sr.secondGather.processVariables.input ≠ none)
    (hreturned : sr.secondGather.processVariables.returned
      = ((p.roundVariables r).secondGather.processVariables).returned)
    (hout : sr.output = (p.roundVariables r).output) :
    BoundInvariant P (Function.update u j (c', p.setRoundVariables r sr))
      (v.writeGhost (ghostStep P) L) := by
  have hold : p.roundVariables r = (u j).2.roundVariables r := by rw [hu]
  refine boundInvariant_update hI hu c' r sr (ghost_writeGhost_of_eq hv _) (fun h => ?_)
    (fun hr ho => ?_) (fun _ => hinput) (fun _ => by rw [hcand]; exact hc)
  · rw [hcand, hold] at h
    exact writeGhost_firstGatherCore _ (by rw [hv r]; exact hI.firstGatherCore_of_candidate r j h)
  · rw [hreturned, hold] at hr
    rw [hout, hold] at ho
    exact writeGhost_bound _ (by rw [hv r]; exact hI.bound_of_returned r j hr ho)

/-- **The bound invariant across the second gather's return**: process `j` records a graded
outcome in its variables of round `r`, whose second gather has been called, and leaves the
candidate and the second gather's input, with the ghost write of any label. -/
theorem boundInvariant_secondGatherReturn (hI : BoundInvariant P u w) (hu : (u j).2 = p)
    (c' : RoundLoopVariables P.n) (r : ℕ) (sr : RoundVariables P.n)
    (hv : ∀ r, v.ghost r = w.ghost r)
    (L : Implementation.ExtendedLabel P.n (Message P.n) (RoundEvent P.n))
    (hcand : sr.candidate = (p.roundVariables r).candidate)
    (hinput : sr.secondGather.processVariables.input
      = ((p.roundVariables r).secondGather.processVariables).input)
    (hin : ((p.roundVariables r).secondGather.processVariables).input ≠ none)
    (hout : sr.output ≠ none) :
    BoundInvariant P (Function.update u j (c', p.setRoundVariables r sr))
      (v.writeGhost (ghostStep P) L) := by
  have hold : p.roundVariables r = (u j).2.roundVariables r := by rw [hu]
  refine boundInvariant_update hI hu c' r sr (ghost_writeGhost_of_eq hv _) (fun h => ?_)
    (fun _ ho => absurd ho hout) (fun _ => by rw [hinput]; exact hin) (fun h => ?_)
  · rw [hcand, hold] at h
    exact writeGhost_firstGatherCore _ (by rw [hv r]; exact hI.firstGatherCore_of_candidate r j h)
  · rw [hinput, hold] at h
    rw [hcand, hold]
    exact hI.candidate_of_secondGatherInput r j h

/-- **The bound invariant across the round's return**: process `j` clears the graded outcome it
holds in its variables of round `r` and leaves the three other fields, and the ghost write of the
graded return records the bound bit of round `r`, from the first gather's core the invariant
places in the ghost. -/
theorem boundInvariant_retG (hI : BoundInvariant P u w) (hu : (u j).2 = p)
    (c' : RoundLoopVariables P.n) (r : ℕ) (sr : RoundVariables P.n) (out : GBCAOutput)
    (hv : ∀ r, v.ghost r = w.ghost r)
    (hcand : sr.candidate = (p.roundVariables r).candidate)
    (hinput : sr.secondGather.processVariables.input
      = ((p.roundVariables r).secondGather.processVariables).input)
    (hout : sr.output = none) (hheld : (p.roundVariables r).output ≠ none) :
    BoundInvariant P (Function.update u j (c', p.setRoundVariables r sr))
      (v.writeGhost (ghostStep P) (Sum.inl (.retG r j out))) := by
  have hold : p.roundVariables r = (u j).2.roundVariables r := by rw [hu]
  refine boundInvariant_update hI hu c' r sr (ghost_writeGhost_of_eq hv _) (fun h => ?_)
    (fun _ _ => ?_) (fun h => absurd hout h) (fun h => ?_)
  · rw [hcand, hold] at h
    exact writeGhost_firstGatherCore _ (by rw [hv r]; exact hI.firstGatherCore_of_candidate r j h)
  · rw [writeGhost_ghost_self v rfl, hv r, ghostStep_retG]
    obtain ⟨C, hC⟩ := Option.ne_none_iff_exists'.mp
      (hI.firstGatherCore_of_output (i := j) (by rw [← hold]; exact hheld))
    rw [hC]
    cases (w.ghost r).2.2 <;> simp
  · rw [hinput, hold] at h
    rw [hcand, hold]
    exact hI.candidate_of_secondGatherInput r j h

end Invariants

/-! ### A round transition

A round transition at round `r` writes the variables of round `r` alone. A send, a round event and
the graded return read variables of round `r` other than the initial ones, so `r` is a started
round by `mem_startedRounds_of_roundVariables`.
`AFW.BoundInvariant` reads four fields of the variables: the candidate, the second gather's input
and return flag, and the graded outcome. The first gather's return writes the candidate, the second
gather's call writes its input, the second gather's return writes its return flag and the graded
outcome, and the graded return clears the graded outcome. Each of the four has its lemma above,
and every other round transition leaves the four fields. -/

/-- A round transition at round `r` leaves the variables the process holds at every other
round. -/
theorem roundVariablesMap_lookup_roundStep {P : Parameters} {j : Fin P.n}
    {c : RoundLoopVariables P.n} {p : RoundVariablesMap P.n}
    {L : Implementation.ExtendedLabel P.n (Message P.n) (RoundEvent P.n)} {r : ℕ}
    (hL : roundOf L = some r) {x : AFW.ProcessVariables P.n}
    (h : RoundStep P j (c, p) L (PMF.pure x)) {r' : ℕ} (hr' : r' ≠ r) :
    x.2.roundVariablesMap.lookup r' = p.roundVariablesMap.lookup r' := by
  generalize hμ : (PMF.pure x : PMF (AFW.ProcessVariables P.n)) = μ at h
  cases h <;> obtain rfl := pure_inj hμ <;>
    first
    | rfl
    | (obtain rfl := Option.some.inj hL
       exact Finmap.lookup_insert_of_ne _ hr')

/-- **A send fires at variables other than the initial ones**: every multicast is guarded by a
call of its gather or of its input instance, or by messages delivered in that instance. -/
theorem roundVariables_ne_initial_gbcaSend (P : Parameters) {j : Fin P.n}
    {c : RoundLoopVariables P.n} {p : RoundVariablesMap P.n} {r : ℕ} {m : Message P.n}
    {μ : PMF (AFW.ProcessVariables P.n)}
    (h : RoundStep P j (c, p) (Sum.inr (.gbcaSend r j m)) μ) :
    p.roundVariables r ≠ RoundVariables.initial P.n := by
  intro h0
  cases h <;> simp_all [RoundVariables.initial, LocalState.receivedCount,
    Gather.ProcessVariables.initial, Gather.BaseProcessVariables.initial,
    BRB.ProcessVariables.initial, Parameters.receivedEchoQuorum]

/-- **A round event fires at variables other than the initial ones**: every call carries a value
the variables hold, the input of a gather or the candidate, and every return is guarded by the call
of its instance or by messages delivered in its instance. -/
theorem roundVariables_ne_initial_gbcaRoundEvent (P : Parameters) {j : Fin P.n}
    {c : RoundLoopVariables P.n} {p : RoundVariablesMap P.n} {r : ℕ} {e : RoundEvent P.n}
    {μ : PMF (AFW.ProcessVariables P.n)}
    (h : RoundStep P j (c, p) (Sum.inr (.gbcaRoundEvent r j e)) μ) :
    p.roundVariables r ≠ RoundVariables.initial P.n := by
  intro h0
  cases h <;> simp_all [RoundVariables.initial, LocalState.receivedCount,
    Gather.ProcessVariables.initial, Gather.BaseProcessVariables.initial,
    BRB.ProcessVariables.initial]

/-- **The graded return fires at variables other than the initial ones**: it returns the graded
outcome the variables hold. -/
theorem roundVariables_ne_initial_retG (P : Parameters) {j : Fin P.n}
    {c : RoundLoopVariables P.n} {p : RoundVariablesMap P.n} {r : ℕ} {out : GBCAOutput}
    {μ : PMF (AFW.ProcessVariables P.n)}
    (h : RoundStep P j (c, p) (Sum.inl (.retG r j out)) μ) :
    p.roundVariables r ≠ RoundVariables.initial P.n := by
  intro h0
  cases h with
  | retG _ _ _ _ hh hph hr hterm hout hr2 => simp [h0, RoundVariables.initial] at hout

/-- **The bound invariant across a round transition.** Process `j` takes a transition of its round,
and the network writes the ghost of the transition's label from a network state `v` whose ghost at
every round is the ghost of `w`. -/
theorem boundInvariant_roundStep {P : Parameters} {u : ∀ _ : Fin P.n, AFW.ProcessVariables P.n}
    {w v : NetworkState P.n} (hI : BoundInvariant P u w) {j : Fin P.n}
    {c : RoundLoopVariables P.n} {p : RoundVariablesMap P.n} (hu : (u j).2 = p)
    {L : Implementation.ExtendedLabel P.n (Message P.n) (RoundEvent P.n)}
    {x : AFW.ProcessVariables P.n} (h : RoundStep P j (c, p) L (PMF.pure x))
    (hv : ∀ r, v.ghost r = w.ghost r) :
    BoundInvariant P (Function.update u j x) (v.writeGhost (ghostStep P) L) := by
  have hloop : ∀ c' : RoundLoopVariables P.n,
      BoundInvariant P (Function.update u j (c', p)) (v.writeGhost (ghostStep P) L) := by
    intro c'
    have hst : ∀ i, (Function.update u j (c', p) i).2 = (u i).2 := fun i => by
      by_cases hi : i = j
      · subst hi; rw [Function.update_self, hu]
      · rw [Function.update_of_ne hi]
    exact boundInvariant_writeGhost hI (fun i _ => by rw [hst i]) (fun i _ => by rw [hst i])
      (fun i _ => by rw [hst i]) (fun i _ => by rw [hst i]) hv L
  generalize hμ : (PMF.pure x : PMF (AFW.ProcessVariables P.n)) = μ at h
  cases h with
  | callGLoop => obtain rfl := pure_inj hμ; exact hloop _
  | deliverLoop => obtain rfl := pure_inj hμ; exact hloop _
  | firstGatherReturn c p r g hh hterm hin hbind hsubap hQ hr1 hcand =>
    obtain rfl := pure_inj hμ
    exact boundInvariant_firstGatherReturn hI hu c r _ _ hv (Option.some_ne_none _) rfl rfl rfl
  | secondGatherCall c p r y hh hterm hcand hin2 =>
    obtain rfl := pure_inj hμ
    exact boundInvariant_secondGatherCall hI hu c r _ hv _ rfl (by rw [hcand]; simp)
      (Option.some_ne_none _) rfl rfl
  | secondGatherReturn c p r g hh hterm hin hbind hsubap hQ hr2 hout =>
    obtain rfl := pure_inj hμ
    exact boundInvariant_secondGatherReturn hI hu c r _ hv _ rfl rfl hin (Option.some_ne_none _)
  | retG c p r out hh hph hr hterm hout hr2 =>
    obtain rfl := pure_inj hμ
    exact boundInvariant_retG hI hu _ r _ out hv rfl rfl rfl (by rw [hout]; simp)
  | gbcaDeliverReceive c p r k m hh hterm =>
    obtain rfl := pure_inj hμ
    cases m <;> exact boundInvariant_writeRoundVariables hI hu c r _ hv _ rfl rfl rfl rfl
  | _ =>
    obtain rfl := pure_inj hμ
    exact boundInvariant_writeRoundVariables hI hu _ _ _ hv _ rfl rfl rfl rfl

end AFW
end ABA
end PLTS
