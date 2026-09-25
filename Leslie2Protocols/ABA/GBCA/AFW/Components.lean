/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sathiya / Claude
-/

import Leslie2Protocols.ABA.Gather.SpecificationOverInstanceAlphabet
import Leslie2Protocols.ABA.GBCA.AFW.Counting
import Leslie2Protocols.ABA.Composition.Components
import Leslie2Protocols.Framework.SynchronisedProduct
import Leslie2Protocols.Framework.LoopsAndInstanceFamilies

/-!
# The components of the graded-agreement round

The pieces that run the round-`r` graded-agreement round: `n` graded-agreement programs beside the
round's network, and the pullbacks along which those programs and the two gather instances read the
round-internal alphabet.

A program holds one process's record of the round — its input, its candidate, whether it has called
the second gather, its graded outcome and its return flag (`GBCA.ByAFW.ProcessVariables`). Its
guards
read that record and nothing else. `ProgramStep` is the step relation of process `j`'s program and
`NetworkStep` that of the round's network; `gbcaProgram` and `GBCANetwork` are the two systems they
carry, and `roundPrograms` is the round's programs: the `n` of them beside the round's network, each
read along `programLabelMap`.

The round's network exchanges no messages. It holds the round's bound bit alone, auxiliary state
(D29) that no program reads. The `firstGatherReturn` event writes the bit from the core the first
gather's return carries; every graded return announces it on its label.

## The return-then-call step and the two-event return

The first gather's return and the second gather's call are two events, `firstGatherReturn`
and `secondGatherCall`, and so are the second gather's return and the round's graded
return, `secondGatherReturn` and `retG`. A program moves on each of the four: `firstGatherReturn`
records the candidate `GBCA.candidate` of the returned entries, `secondGatherCall` marks the call,
`secondGatherReturn` records the grade `GBCA.gradeOf`, `retG` marks the return. What carries
the round from one event to the next is the program's record.

## The alphabet

The round speaks `ExtendedLabel n Empty` natively, as `GBCA.ByABDY.composition` speaks
`ExtendedLabel n GBCA.ByABDY.Message`. The round exchanges its messages inside its two gather
instances, so it takes the empty type for the family alphabet's round message type: the round
multicast `gbcaSend` and the round delivery `gbcaDeliver` name no label here. The call loop of
the family alphabet, `gbcaCallLoop r id b`, is the round's loop label, and the three Byzantine
handshake labels of round `r` are labels of the interface. A program is read along
`programLabelMap`, the projection that sends a Byzantine call to a call, a Byzantine return to a
return, and the two call loops to the loop.

The gathers' own call loops sit one level down. `firstGatherLabelMap` sends the family's two call
loops to `Gather.LoopLabel.callLoop`, the label of the first gather's loop, and the genuine and
Byzantine calls to `Gather.Label.call`. The second gather is called on the round's own
`secondGatherCall` event, which `secondGatherLabelMap` sends to `Gather.Label.call`; the second
gather's loop label has no label of the family over it.

A family label outside the round's interface — the ABA API, the coin ports and the rendezvous of
the protocol's own networks — has the image `ProgramLabel.outside`, on which neither a program nor
the round's network moves. The round has no transition on such a label, and the family supplies the
idle. Corruption is the exception: it has no image at all, so the round's programs remain unchanged
on it while the two gather instances move.

The round-internal alphabet is `RoundLabel n = ExtendedLabel n Empty ⊕ RoundEvent n`, and
`roundEvents` collects the three events of `RoundEvent n`. They are hidden by the composition of
`ABA/GBCA/AFW/Composition.lean`, which speaks `ExtendedLabel n Empty`.

## Corruption

`fail id` is a label of the interface. Neither a program nor the round's network fires on it: the
round's programs remain unchanged and the two gather instances corrupt together (D1). In the family
of rounds the label is the broadcast act (`GBCA.ByABDY.isFailLabel`), applied to every round at
once, and `GBCA.ByAFW.corruptAll` is the transform it applies — the two gather transforms, the
programs and the bound bit untouched.
-/

namespace PLTS
namespace ABA
namespace GBCA.ByAFW

open Implementation hiding NetworkEvent ExtendedLabel
open Composition

/-! ### The program's record -/

/-- The record of one graded-agreement program: what a process holds between
the events it takes part in. -/
structure ProcessVariables (n : ℕ) : Type where
  /-- The input the call carried. -/
  input : Option Bool
  /-- The candidate the first gather's return determines. -/
  candidate : Option (Option Bool)
  /-- Whether the second gather has been called here. -/
  secondGatherCalled : Bool
  /-- The graded outcome the second gather's return determines. -/
  output : Option GBCAOutput
  /-- Whether the round has returned here. -/
  returned : Bool
  deriving DecidableEq

/-- The initial record: nothing called, nothing determined, nothing
returned. -/
def ProcessVariables.initial (n : ℕ) : ProcessVariables n := ⟨none, none, false, none, false⟩

/-! ### The round-internal alphabet

The three events the family alphabet cannot name. They are untagged: the round
is the identity of the instance they belong to, and they are hidden before the
family sees the round at all. -/

/-- The round's own events: the first gather's return, the second gather's
call, and the second gather's return. -/
inductive RoundEvent (n : ℕ) : Type
  /-- The first gather returns the partial map `g` over the core `C` to
  `id`. -/
  | firstGatherReturn (id : Fin n) (g : Fin n → Option Bool) (C : Gather.AcceptedPairs n Bool)
  /-- Process `id` calls the second gather with `x`. -/
  | secondGatherCall (id : Fin n) (x : Option Bool)
  /-- The second gather returns the partial map `g` over the core `C` to
  `id`. -/
  | secondGatherReturn (id : Fin n) (g : Fin n → Option (Option Bool)) (C : Gather.AcceptedPairs n
    (Option Bool))

/-- The round-internal alphabet: the family alphabet plus the three events. Its
silent label is `Sum.inl (Sum.inl τ)`, so every `Sum.inr` label is observable
and hence hideable. -/
abbrev RoundLabel (n : ℕ) : Type := ExtendedLabel n Empty ⊕ RoundEvent n

/-- The event labels, hidden by the round. -/
def roundEvents (n : ℕ) : Set (RoundLabel n) := {l | ∃ e : RoundEvent n, l = Sum.inr e}

@[simp] theorem inl_notMem_roundEvents {n : ℕ} (l : ExtendedLabel n Empty) :
    Sum.inl l ∉ roundEvents n :=
  by
  simp [roundEvents]

@[simp] theorem inr_mem_roundEvents {n : ℕ} (e : RoundEvent n) : Sum.inr e ∈ roundEvents n := ⟨e,
  rfl⟩

@[simp] theorem roundLabel_tau (n : ℕ) :
    (Silent.τ : RoundLabel n) = Sum.inl (Sum.inl Label.tau) := rfl

/-! ### The program's alphabet -/

/-- The alphabet of one graded-agreement program: the round's two handshake
ports, the loop the family alphabet's call loops stand for, and the round's
three events. -/
inductive ProgramLabel (n : ℕ) : Type
  /-- The silent label. -/
  | tau
  /-- The round's call at `id` with input `b`. -/
  | callG (r : ℕ) (id : Fin n) (b : Bool)
  /-- The round's call against an already-called record. -/
  | callLoop (r : ℕ) (id : Fin n) (b : Bool)
  /-- The first gather's return to `id`. -/
  | firstGatherReturn (id : Fin n) (g : Fin n → Option Bool) (C : Gather.AcceptedPairs n Bool)
  /-- Process `id`'s call of the second gather with `x`. -/
  | secondGatherCall (id : Fin n) (x : Option Bool)
  /-- The second gather's return to `id`. -/
  | secondGatherReturn (id : Fin n) (g : Fin n → Option (Option Bool)) (C : Gather.AcceptedPairs n
    (Option Bool))
  /-- The round's return to `id` of the graded outcome `out`, announcing the
  round's bound bit `bnd`. -/
  | retG (r : ℕ) (id : Fin n) (out : GBCAOutput) (bnd : Bool)
  /-- The image of every family label outside the round's interface. No transition
  fires on it. -/
  | outside

instance {n : ℕ} : Silent (ProgramLabel n) := ⟨ProgramLabel.tau⟩

@[simp] theorem programLabel_tau (n : ℕ) : (Silent.τ : ProgramLabel n) = ProgramLabel.tau := rfl

/-! ### The pullbacks

A program and the round's network are read along `programLabelMap`, the first gather along
`firstGatherLabelMap`, the second along `secondGatherLabelMap`. A label with no image at a component
leaves that component unchanged. -/

/-- The projection of the round-internal alphabet onto a program's alphabet. It
reads a Byzantine call as a call, a Byzantine return as a return, and the two
call loops as the loop. Corruption has no image and leaves a program standing
still; every other family label outside the round's interface has the image
`ProgramLabel.outside`, on which no transition fires. -/
def programLabelMap (n : ℕ) : RoundLabel n → Option (ProgramLabel n)
  | Sum.inl (Sum.inl .tau) => some .tau
  | Sum.inl (Sum.inl (.callG r id b)) => some (.callG r id b)
  | Sum.inl (Sum.inl (.retG r id out bnd)) => some (.retG r id out bnd)
  | Sum.inl (Sum.inr (.gbcaCallLoop r id b)) => some (.callLoop r id b)
  | Sum.inl (Sum.inr (.byzantineCallG r k b)) => some (.callG r k b)
  | Sum.inl (Sum.inr (.byzantineCallGLoop r k b)) => some (.callLoop r k b)
  | Sum.inl (Sum.inr (.byzantineRetG r k out bnd)) => some (.retG r k out bnd)
  | Sum.inr (.firstGatherReturn id g C) => some (.firstGatherReturn id g C)
  | Sum.inr (.secondGatherCall id x) => some (.secondGatherCall id x)
  | Sum.inr (.secondGatherReturn id g C) => some (.secondGatherReturn id g C)
  | Sum.inl (Sum.inl (.fail _)) => none
  | _ => some .outside

/-- The projection of the round-internal alphabet onto the first gather's
interface alphabet. The round's call is the gather's call, the family's call
loops are the gather's loop, and the `firstGatherReturn` event is the gather's return. -/
def firstGatherLabelMap (n : ℕ) : RoundLabel n → Option (Gather.InstanceLabel n Bool)
  | Sum.inl (Sum.inl .tau) => some (Sum.inl .tau)
  | Sum.inl (Sum.inl (.callG _ id b)) => some (Sum.inl (.call id b))
  | Sum.inl (Sum.inl (.fail id)) => some (Sum.inl (.fail id))
  | Sum.inl (Sum.inr (.gbcaCallLoop _ id b)) => some (Sum.inr (.callLoop id b))
  | Sum.inl (Sum.inr (.byzantineCallG _ k b)) => some (Sum.inl (.call k b))
  | Sum.inl (Sum.inr (.byzantineCallGLoop _ k b)) => some (Sum.inr (.callLoop k b))
  | Sum.inr (.firstGatherReturn id g C) => some (Sum.inl (.ret id g C))
  | _ => none

/-- The projection of the round-internal alphabet onto the second gather's
interface alphabet. The `secondGatherCall` event is the gather's call and the `secondGatherReturn`
event its return. -/
def secondGatherLabelMap (n : ℕ) : RoundLabel n → Option (Gather.InstanceLabel n (Option Bool))
  | Sum.inl (Sum.inl .tau) => some (Sum.inl .tau)
  | Sum.inl (Sum.inl (.fail id)) => some (Sum.inl (.fail id))
  | Sum.inr (.secondGatherCall id x) => some (Sum.inl (.call id x))
  | Sum.inr (.secondGatherReturn id g C) => some (Sum.inl (.ret id g C))
  | _ => none

/-- The silent label projects to the silent label. -/
@[simp] theorem programLabelMap_tau (n : ℕ) :
    programLabelMap n (Silent.τ : RoundLabel n) = some (Silent.τ : ProgramLabel n) := rfl

/-- The silent label projects to the silent label. -/
@[simp] theorem firstGatherLabelMap_tau (n : ℕ) :
    firstGatherLabelMap n (Silent.τ : RoundLabel n) = some (Silent.τ : Gather.InstanceLabel n Bool)
      := rfl

/-- The silent label projects to the silent label. -/
@[simp] theorem secondGatherLabelMap_tau (n : ℕ) :
    secondGatherLabelMap n (Silent.τ : RoundLabel n) = some (Silent.τ : Gather.InstanceLabel n
      (Option Bool)) := rfl

/-- Only the silent label reaches a program's silent label. -/
theorem programLabelMap_eq_tau {n : ℕ} {l : RoundLabel n}
    (h : programLabelMap n l = some ProgramLabel.tau) : l = Sum.inl (Sum.inl Label.tau) := by
  rcases l with (l₀ | e) | e
  · cases l₀ <;> simp_all [programLabelMap]
  · cases e <;> simp_all [programLabelMap]
  · cases e <;> simp_all [programLabelMap]

/-- Only the silent label reaches the first gather's silent label. -/
theorem firstGatherLabelMap_eq_tau {n : ℕ} {l : RoundLabel n}
    (h : firstGatherLabelMap n l = some (Silent.τ : Gather.InstanceLabel n Bool)) : l = Silent.τ :=
      by
  rcases l with (l₀ | e) | e
  · cases l₀ <;> simp_all [firstGatherLabelMap]
  · cases e <;> simp_all [firstGatherLabelMap]
  · cases e <;> simp_all [firstGatherLabelMap]

/-- Only the silent label reaches the second gather's silent label. -/
theorem secondGatherLabelMap_eq_tau {n : ℕ} {l : RoundLabel n}
    (h : secondGatherLabelMap n l = some (Silent.τ : Gather.InstanceLabel n (Option Bool))) : l =
      Silent.τ := by
  rcases l with (l₀ | e) | e
  · cases l₀ <;> simp_all [secondGatherLabelMap]
  · cases e <;> simp_all [secondGatherLabelMap]
  · cases e <;> simp_all [secondGatherLabelMap]

/-! ### The pullbacks, label by label -/

section Pullbacks
variable {n : ℕ} (r : ℕ) (id k i j : Fin n) (b c bnd : Bool) (x : Option Bool)
  (out : GBCAOutput) (g : Fin n → Option Bool)
  (h : Fin n → Option (Option Bool)) (C : Gather.AcceptedPairs n Bool)
  (D : Gather.AcceptedPairs n (Option Bool))

@[simp] theorem programLabelMap_callG :
    programLabelMap n (Sum.inl (Sum.inl (.callG r id b))) = some (.callG r id b) := rfl
@[simp] theorem programLabelMap_retG :
    programLabelMap n (Sum.inl (Sum.inl (.retG r id out bnd))) = some (.retG r id out bnd) := rfl
@[simp] theorem programLabelMap_callABA :
    programLabelMap n (Sum.inl (Sum.inl (.callABA id b))) = some .outside := rfl
@[simp] theorem programLabelMap_retABA :
    programLabelMap n (Sum.inl (Sum.inl (.retABA id b))) = some .outside := rfl
@[simp] theorem programLabelMap_callW : programLabelMap n (Sum.inl (Sum.inl (.callW r id))) = some
  .outside := rfl
@[simp] theorem programLabelMap_retW : programLabelMap n (Sum.inl (Sum.inl (.retW r id b))) = some
  .outside := rfl
@[simp] theorem programLabelMap_fail : programLabelMap n (Sum.inl (Sum.inl (.fail id))) = none :=
  rfl
@[simp] theorem programLabelMap_gbcaCallLoop :
    programLabelMap n (Sum.inl (Sum.inr (.gbcaCallLoop r id b))) = some (.callLoop r id b) := rfl
@[simp] theorem programLabelMap_byzantineCallG :
    programLabelMap n (Sum.inl (Sum.inr (.byzantineCallG r k b))) = some (.callG r k b) := rfl
@[simp] theorem programLabelMap_byzantineCallGLoop :
    programLabelMap n (Sum.inl (Sum.inr (.byzantineCallGLoop r k b))) = some (.callLoop r k b) :=
      rfl
@[simp] theorem programLabelMap_byzantineRetG :
    programLabelMap n (Sum.inl (Sum.inr (.byzantineRetG r k out bnd))) = some (.retG r k out bnd) :=
      rfl
@[simp] theorem programLabelMap_decidedSend : programLabelMap n (Sum.inl (Sum.inr (.decidedSend j
  b))) = some .outside := rfl
@[simp] theorem programLabelMap_decidedDeliver : programLabelMap n (Sum.inl (Sum.inr
  (.decidedDeliver i j b))) = some .outside := rfl
@[simp] theorem programLabelMap_retWPublish :
    programLabelMap n (Sum.inl (Sum.inr (.retWPublish r id c b))) = some .outside := rfl
@[simp] theorem programLabelMap_byzantineCallW :
    programLabelMap n (Sum.inl (Sum.inr (.byzantineCallW r k))) = some .outside := rfl
@[simp] theorem programLabelMap_byzantineRetW :
    programLabelMap n (Sum.inl (Sum.inr (.byzantineRetW r k b))) = some .outside := rfl
@[simp] theorem programLabelMap_firstGatherReturn :
    programLabelMap n (Sum.inr (.firstGatherReturn id g C)) = some (.firstGatherReturn id g C) :=
      rfl
@[simp] theorem programLabelMap_secondGatherCall : programLabelMap n (Sum.inr (.secondGatherCall id
  x)) = some (.secondGatherCall id
  x) := rfl
@[simp] theorem programLabelMap_secondGatherReturn :
    programLabelMap n (Sum.inr (.secondGatherReturn id h D)) = some (.secondGatherReturn id h D) :=
      rfl

@[simp] theorem firstGatherLabelMap_callG :
    firstGatherLabelMap n (Sum.inl (Sum.inl (.callG r id b))) = some (Sum.inl (.call id b)) := rfl
@[simp] theorem firstGatherLabelMap_retG :
    firstGatherLabelMap n (Sum.inl (Sum.inl (.retG r id out bnd))) = none := rfl
@[simp] theorem firstGatherLabelMap_callABA : firstGatherLabelMap n (Sum.inl (Sum.inl (.callABA id
  b))) = none := rfl
@[simp] theorem firstGatherLabelMap_retABA : firstGatherLabelMap n (Sum.inl (Sum.inl (.retABA id
  b))) = none := rfl
@[simp] theorem firstGatherLabelMap_callW : firstGatherLabelMap n (Sum.inl (Sum.inl (.callW r id)))
  = none := rfl
@[simp] theorem firstGatherLabelMap_retW : firstGatherLabelMap n (Sum.inl (Sum.inl (.retW r id b)))
  = none := rfl
@[simp] theorem firstGatherLabelMap_fail :
    firstGatherLabelMap n (Sum.inl (Sum.inl (.fail id))) = some (Sum.inl (.fail id)) := rfl
@[simp] theorem firstGatherLabelMap_gbcaCallLoop :
    firstGatherLabelMap n (Sum.inl (Sum.inr (.gbcaCallLoop r id b))) = some (Sum.inr (.callLoop id
      b))
      := rfl
@[simp] theorem firstGatherLabelMap_byzantineCallG :
    firstGatherLabelMap n (Sum.inl (Sum.inr (.byzantineCallG r k b))) = some (Sum.inl (.call k b))
      := rfl
@[simp] theorem firstGatherLabelMap_byzantineCallGLoop :
    firstGatherLabelMap n (Sum.inl (Sum.inr (.byzantineCallGLoop r k b))) = some (Sum.inr (.callLoop
      k b)) := rfl
@[simp] theorem firstGatherLabelMap_byzantineRetG :
    firstGatherLabelMap n (Sum.inl (Sum.inr (.byzantineRetG r k out bnd))) = none := rfl
@[simp] theorem firstGatherLabelMap_decidedSend : firstGatherLabelMap n (Sum.inl (Sum.inr
  (.decidedSend j b))) = none := rfl
@[simp] theorem firstGatherLabelMap_decidedDeliver : firstGatherLabelMap n (Sum.inl (Sum.inr
  (.decidedDeliver i j b))) = none := rfl
@[simp] theorem firstGatherLabelMap_retWPublish : firstGatherLabelMap n (Sum.inl (Sum.inr
  (.retWPublish r id
  c b))) = none := rfl
@[simp] theorem firstGatherLabelMap_byzantineCallW : firstGatherLabelMap n (Sum.inl (Sum.inr
  (.byzantineCallW r k))) = none := rfl
@[simp] theorem firstGatherLabelMap_byzantineRetW : firstGatherLabelMap n (Sum.inl (Sum.inr
  (.byzantineRetW r k b))) = none := rfl
@[simp] theorem firstGatherLabelMap_firstGatherReturn :
    firstGatherLabelMap n (Sum.inr (.firstGatherReturn id g C)) = some (Sum.inl (.ret id g C)) :=
      rfl
@[simp] theorem firstGatherLabelMap_secondGatherCall :
    firstGatherLabelMap n (Sum.inr (.secondGatherCall id x)) = none :=
  rfl
@[simp] theorem firstGatherLabelMap_secondGatherReturn :
    firstGatherLabelMap n (Sum.inr (.secondGatherReturn id h D)) = none :=
  rfl

@[simp] theorem secondGatherLabelMap_callG : secondGatherLabelMap n (Sum.inl (Sum.inl (.callG r id
  b))) = none := rfl
@[simp] theorem secondGatherLabelMap_retG : secondGatherLabelMap n (Sum.inl (Sum.inl (.retG r id out
  bnd))) = none := rfl
@[simp] theorem secondGatherLabelMap_callABA : secondGatherLabelMap n (Sum.inl (Sum.inl (.callABA id
  b))) = none := rfl
@[simp] theorem secondGatherLabelMap_retABA : secondGatherLabelMap n (Sum.inl (Sum.inl (.retABA id
  b))) = none := rfl
@[simp] theorem secondGatherLabelMap_callW : secondGatherLabelMap n (Sum.inl (Sum.inl (.callW r
  id))) = none := rfl
@[simp] theorem secondGatherLabelMap_retW : secondGatherLabelMap n (Sum.inl (Sum.inl (.retW r id
  b))) = none := rfl
@[simp] theorem secondGatherLabelMap_fail :
    secondGatherLabelMap n (Sum.inl (Sum.inl (.fail id))) = some (Sum.inl (.fail id)) := rfl
@[simp] theorem secondGatherLabelMap_gbcaCallLoop : secondGatherLabelMap n (Sum.inl (Sum.inr
  (.gbcaCallLoop r id b))) = none := rfl
@[simp] theorem secondGatherLabelMap_byzantineCallG : secondGatherLabelMap n (Sum.inl (Sum.inr
  (.byzantineCallG r k b))) = none := rfl
@[simp] theorem secondGatherLabelMap_byzantineCallGLoop :
    secondGatherLabelMap n (Sum.inl (Sum.inr (.byzantineCallGLoop r k b))) = none := rfl
@[simp] theorem secondGatherLabelMap_byzantineRetG :
    secondGatherLabelMap n (Sum.inl (Sum.inr (.byzantineRetG r k out bnd))) = none := rfl
@[simp] theorem secondGatherLabelMap_decidedSend : secondGatherLabelMap n (Sum.inl (Sum.inr
  (.decidedSend j b))) = none := rfl
@[simp] theorem secondGatherLabelMap_decidedDeliver : secondGatherLabelMap n (Sum.inl (Sum.inr
  (.decidedDeliver i j b))) = none := rfl
@[simp] theorem secondGatherLabelMap_retWPublish : secondGatherLabelMap n (Sum.inl (Sum.inr
  (.retWPublish r
  id c b))) = none := rfl
@[simp] theorem secondGatherLabelMap_byzantineCallW : secondGatherLabelMap n (Sum.inl (Sum.inr
  (.byzantineCallW r k))) = none := rfl
@[simp] theorem secondGatherLabelMap_byzantineRetW : secondGatherLabelMap n (Sum.inl (Sum.inr
  (.byzantineRetW r k b))) = none := rfl
@[simp] theorem secondGatherLabelMap_firstGatherReturn : secondGatherLabelMap n (Sum.inr
  (.firstGatherReturn id g C)) = none
  := rfl
@[simp] theorem secondGatherLabelMap_secondGatherCall :
    secondGatherLabelMap n (Sum.inr (.secondGatherCall id x)) = some (Sum.inl (.call id x)) := rfl
@[simp] theorem secondGatherLabelMap_secondGatherReturn :
    secondGatherLabelMap n (Sum.inr (.secondGatherReturn id h D)) = some (Sum.inl (.ret id h D)) :=
      rfl

end Pullbacks
/-! ### The graded-agreement program

Process `j`'s program in this round. Every guard reads its own record. The
round's four moves are one transition each: the call records the input, the first
gather's return records the candidate, the second gather's call marks itself,
the second gather's return records the grade, and the round's return marks the
record returned. No transition fires on the silent label. -/

/-- The step relation of the graded-agreement program of process `j` in round
`r`. All transitions are Dirac. -/
inductive ProgramStep (P : Parameters) (r : ℕ) (j : Fin P.n) :
    ProcessVariables P.n → ProgramLabel P.n → PMF (ProcessVariables P.n) → Prop
  /-- The call arrives: record the input. -/
  | callG (p : ProcessVariables P.n) (b : Bool) (h : p.input = none) :
      ProgramStep P r j p (.callG r j b) (PMF.pure { p with input := some b })
  /-- A call addressed elsewhere: not `j`'s business. -/
  | callGIdle (p : ProcessVariables P.n) (i : Fin P.n) (b : Bool) (hi : i ≠ j) :
      ProgramStep P r j p (.callG r i b) (PMF.pure p)
  /-- The call loop: the record does not move. -/
  | callLoop (p : ProcessVariables P.n) (b : Bool) :
      ProgramStep P r j p (.callLoop r j b) (PMF.pure p)
  /-- A call loop at another process: not `j`'s business. -/
  | callLoopIdle (p : ProcessVariables P.n) (i : Fin P.n) (b : Bool) (hi : i ≠ j) :
      ProgramStep P r j p (.callLoop r i b) (PMF.pure p)
  /-- The first gather returns here: record the candidate of its entries. -/
  | firstGatherReturn (p : ProcessVariables P.n) (g : Fin P.n → Option Bool) (C :
      Gather.AcceptedPairs
    P.n Bool)
      (hin : p.input ≠ none) (hc : p.candidate = none) :
      ProgramStep P r j p (.firstGatherReturn j g C) (PMF.pure { p with
        candidate :=
          some (candidate P g) })
  /-- The first gather's return to another process: not `j`'s business. -/
  | firstGatherReturnIdle (p : ProcessVariables P.n) (i : Fin P.n) (g : Fin P.n → Option Bool)
      (C : Gather.AcceptedPairs P.n Bool) (hi : i ≠ j) :
      ProgramStep P r j p (.firstGatherReturn i g C) (PMF.pure p)
  /-- The second gather is called here with the recorded candidate. -/
  | secondGatherCall (p : ProcessVariables P.n) (x : Option Bool) (hc : p.candidate = some x)
      (h2 : p.secondGatherCalled = false) :
      ProgramStep P r j p (.secondGatherCall j x) (PMF.pure { p with secondGatherCalled := true })
  /-- Another process's call of the second gather: not `j`'s business. -/
  | secondGatherCallIdle (p : ProcessVariables P.n) (i : Fin P.n) (x : Option Bool) (hi : i ≠ j) :
      ProgramStep P r j p (.secondGatherCall i x) (PMF.pure p)
  /-- The second gather returns here: record the grade of its entries. -/
  | secondGatherReturn (p : ProcessVariables P.n) (g : Fin P.n → Option (Option Bool))
      (C : Gather.AcceptedPairs P.n (Option Bool)) (h2 : p.secondGatherCalled = true)
      (ho : p.output = none) :
      ProgramStep P r j p (.secondGatherReturn j g C) (PMF.pure
        { p with output := some (gradeOf P g) })
  /-- The second gather's return to another process: not `j`'s business. -/
  | secondGatherReturnIdle (p : ProcessVariables P.n) (i : Fin P.n) (g : Fin P.n → Option (Option
    Bool))
      (C : Gather.AcceptedPairs P.n (Option Bool)) (hi : i ≠ j) :
      ProgramStep P r j p (.secondGatherReturn i g C) (PMF.pure p)
  /-- The round returns the recorded grade. The return announces the grade and the record drops it.
  The announced bit is the round's network's to determine. -/
  | retG (p : ProcessVariables P.n) (out : GBCAOutput) (bnd : Bool) (ho : p.output = some out)
      (hr : p.returned = false) :
      ProgramStep P r j p (.retG r j out bnd)
        (PMF.pure { p with output := none, returned := true })
  /-- A return to another process: not `j`'s business. -/
  | retGIdle (p : ProcessVariables P.n) (i : Fin P.n) (out : GBCAOutput) (bnd : Bool) (hi : i ≠ j) :
      ProgramStep P r j p (.retG r i out bnd) (PMF.pure p)

/-! ### The round's network

The network of the round's programs. It exchanges no message and holds the round's bound
bit alone; no program reads it. The `firstGatherReturn` transition writes the bit from the core the
first gather's return carries if it is unwritten, and the `retG` transition determines the bit the
label announces. No transition fires on the silent label. -/

/-- The step relation of the round's network. All transitions are Dirac. -/
inductive NetworkStep (P : Parameters) (r : ℕ) :
    Option Bool → ProgramLabel P.n → PMF (Option Bool) → Prop
  /-- A call moves nothing. -/
  | callG (w : Option Bool) (id : Fin P.n) (b : Bool) :
      NetworkStep P r w (.callG r id b) (PMF.pure w)
  /-- A call loop moves nothing. -/
  | callLoop (w : Option Bool) (id : Fin P.n) (b : Bool) :
      NetworkStep P r w (.callLoop r id b) (PMF.pure w)
  /-- The first gather's return writes the round's bound bit if it is
  unwritten. -/
  | firstGatherReturn (w : Option Bool) (id : Fin P.n) (g : Fin P.n → Option Bool)
      (C : Gather.AcceptedPairs P.n Bool) :
      NetworkStep P r w (.firstGatherReturn id g C) (PMF.pure (some (w.getD (boundOfCore P C))))
  /-- The second gather's call moves nothing. -/
  | secondGatherCall (w : Option Bool) (id : Fin P.n) (x : Option Bool) :
      NetworkStep P r w (.secondGatherCall id x) (PMF.pure w)
  /-- The second gather's return moves nothing. -/
  | secondGatherReturn (w : Option Bool) (id : Fin P.n) (g : Fin P.n → Option (Option Bool))
      (C : Gather.AcceptedPairs P.n (Option Bool)) :
      NetworkStep P r w (.secondGatherReturn id g C) (PMF.pure w)
  /-- The round's return announces the bit on record, and moves nothing. -/
  | retG (w : Option Bool) (id : Fin P.n) (out : GBCAOutput) :
      NetworkStep P r w (.retG r id out (w.getD (boundOfCore P ∅))) (PMF.pure w)

/-! ### The round's programs and the round -/

/-- The graded-agreement program of process `j` in round `r`. -/
noncomputable def gbcaProgram (P : Parameters) (r : ℕ) (j : Fin P.n) :
    System (ProcessVariables P.n) (ProgramLabel P.n) where
  init := ProcessVariables.initial P.n
  step := ProgramStep P r j

@[simp] theorem gbcaProgram_init (P : Parameters) (r : ℕ) (j : Fin P.n) :
    (gbcaProgram P r j).init = ProcessVariables.initial P.n := rfl

@[simp] theorem gbcaProgram_step (P : Parameters) (r : ℕ) (j : Fin P.n) (p : ProcessVariables P.n)
    (l : ProgramLabel P.n) (ν : PMF (ProcessVariables P.n)) :
    (gbcaProgram P r j).step p l ν ↔ ProgramStep P r j p l ν := Iff.rfl

/-- The round's network of round `r`. -/
noncomputable def GBCANetwork (P : Parameters) (r : ℕ) : System (Option Bool) (ProgramLabel P.n)
  where
  init := none
  step := NetworkStep P r

@[simp] theorem GBCANetwork_init (P : Parameters) (r : ℕ) : (GBCANetwork P r).init = none := rfl

@[simp] theorem GBCANetwork_step (P : Parameters) (r : ℕ) (w : Option Bool) (l : ProgramLabel P.n)
    (μ : PMF (Option Bool)) : (GBCANetwork P r).step w l μ ↔ NetworkStep P r w l μ := Iff.rfl

/-- **The round's programs**: the `n` programs beside the round's network, each read along
`programLabelMap`. -/
noncomputable def roundPrograms (P : Parameters) (r : ℕ) :
    System ((∀ _ : Fin P.n, ProcessVariables P.n) × Option Bool) (RoundLabel P.n) :=
  (System.synchronisedProduct (fun j => (gbcaProgram P r j).mapIdle (programLabelMap P.n))).parallel
    ((GBCANetwork P r).mapIdle (programLabelMap P.n))

@[simp] theorem roundPrograms_init (P : Parameters) (r : ℕ) :
    (roundPrograms P r).init = ((fun _ => ProcessVariables.initial P.n), none) := rfl

end GBCA.ByAFW
end ABA
end PLTS
