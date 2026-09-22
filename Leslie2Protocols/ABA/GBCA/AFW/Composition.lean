/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sathiya / Claude
-/

import Leslie2Protocols.ABA.Gather.CompositionStepInversion
import Leslie2Protocols.ABA.GBCA.AFW.Counting
import Leslie2Protocols.ABA.Composition.GBCAInstanceByABDY
import Leslie2Protocols.Framework.Relabel
import Leslie2Protocols.Framework.SynchronisedProduct
import Leslie2Protocols.Framework.LoopsAndInstanceFamilies
import Leslie2Protocols.Framework.SynchronisedProductAlongPullbacks

/-!
# The graded-agreement round, composed

The round-`r` graded-agreement round over two gather instances, taken apart into the pieces that run
it: `n` graded-agreement programs beside the round's network, in parallel with the two gather
instances, each read along a pullback that names it. The round's own events are hidden, and the
result is read over the family alphabet `ExtendedLabel n`.

A program holds one process's record of the round — its input, its candidate,
whether it has called the second gather, its graded outcome and its return flag
(`GBCA.ByAFW.ProcessRecord`). Its guards read that record and nothing else.

The round's network exchanges no messages. It holds the round's bound bit alone, and no program
reads it. The `firstGatherReturn` event writes the bit from the core the first gather's return
carries; every graded return announces it on its label.

## The return-then-call step and the two-event return

The first gather's return and the second gather's call are two events, `firstGatherReturn`
and `secondGatherCall`, and so are the second gather's return and the round's graded
return, `secondGatherReturn` and `retG`. A program moves on each of the four: `firstGatherReturn`
records the candidate `GBCA.candidate` of the returned entries, `secondGatherCall` marks the call,
`secondGatherReturn` records the grade `GBCA.gradeOf`, `retG` marks the return. What carries
the round from one event to the next is the program's record.

## The alphabet

The round speaks `ExtendedLabel n` natively, as `GBCA.ByABDY.composition` does. The call loop of the
family alphabet, `gbcaCallLoop r id b`, is the round's loop label, and the three
Byzantine handshake rows of round `r` are labels of the interface. A program is
read along `programLabelMap`, the projection that sends a Byzantine call to a call, a
Byzantine return to a return, and the two call loops to the loop.

The gathers' own call loops sit one level down. `firstGatherLabelMap` sends the family's
two call loops to `Gather.LoopLabel.callLoop`, the label of the first gather's loop
row, and the genuine and Byzantine calls to `Gather.Label.call`. The second
gather is called on the round's own `secondGatherCall` event, which `secondGatherLabelMap` sends to
`Gather.Label.call`; the second gather's loop label has no label of the family
over it.

A family label outside the round's interface — the ABA API, the coin ports and the rendezvous of the
protocol's own networks — has the image `ProgramLabel.outside`, on which neither a program nor the
round's network has a row. The round has no transition on such a label, and the family supplies the
idle. Corruption is the exception: it has no image at all, so the round's programs remain unchanged on it
while the two gather instances move.

The round-internal alphabet is `RoundLabel n = ExtendedLabel n ⊕ RoundEvent n`. Its three events are
hidden before anything outside sees the round: `roundOverGathers` speaks `ExtendedLabel n`.

## Corruption

`fail id` is a label of the interface. No program and no row of the round's network fires on it: the
round's programs remain unchanged and the two gather instances corrupt together. In the family of rounds
the label is the broadcast act (`GBCA.ByABDY.isFailLabel`), applied to every round at once, and
`GBCA.ByAFW.corruptAll` is the transform it applies — the two gather transforms, the programs and
the bound bit untouched. -/

namespace PLTS
namespace ABA
namespace GBCA.ByAFW

open Implementation Composition

/-! ### The program's record -/

/-- The record of one graded-agreement program: what a process holds between
the events it takes part in. -/
structure ProcessRecord (n : ℕ) : Type where
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
def ProcessRecord.initial (n : ℕ) : ProcessRecord n := ⟨none, none, false, none, false⟩

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
abbrev RoundLabel (n : ℕ) : Type := ExtendedLabel n ⊕ RoundEvent n

/-- The event labels, hidden by the round. -/
def roundEvents (n : ℕ) : Set (RoundLabel n) := {l | ∃ e : RoundEvent n, l = Sum.inr e}

@[simp] theorem inl_notMem_roundEvents {n : ℕ} (l : ExtendedLabel n) : Sum.inl l ∉ roundEvents n :=
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
  /-- The image of every family label outside the round's interface. No row
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
`ProgramLabel.outside`, on which no row fires. -/
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

section PullRows

variable {n : ℕ} (r : ℕ) (id k i j : Fin n) (b c bnd : Bool) (x : Option Bool)
  (out : GBCAOutput) (m : GBCA.ByABDY.Message) (g : Fin n → Option Bool)
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
@[simp] theorem programLabelMap_gbcaSend :
    programLabelMap n (Sum.inl (Sum.inr (.gbcaSend r j m))) = some .outside := rfl
@[simp] theorem programLabelMap_gbcaDeliver :
    programLabelMap n (Sum.inl (Sum.inr (.gbcaDeliver r i j m))) = some .outside := rfl
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
@[simp] theorem firstGatherLabelMap_gbcaSend : firstGatherLabelMap n (Sum.inl (Sum.inr (.gbcaSend r
  j m))) = none := rfl
@[simp] theorem firstGatherLabelMap_gbcaDeliver : firstGatherLabelMap n (Sum.inl (Sum.inr
  (.gbcaDeliver r i j m))) = none := rfl
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
@[simp] theorem secondGatherLabelMap_gbcaSend : secondGatherLabelMap n (Sum.inl (Sum.inr (.gbcaSend
  r j m))) = none := rfl
@[simp] theorem secondGatherLabelMap_gbcaDeliver : secondGatherLabelMap n (Sum.inl (Sum.inr
  (.gbcaDeliver r i j m))) = none := rfl
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

end PullRows

/-! ### The graded-agreement program

Process `j`'s program in this round. Every guard reads its own record. The
round's four moves are one row each: the call records the input, the first
gather's return records the candidate, the second gather's call marks itself,
the second gather's return records the grade, and the round's return marks the
record returned. No row fires on the silent label. -/

/-- The step relation of the graded-agreement program of process `j` in round
`r`. All transitions are Dirac. -/
inductive ProgramStep (P : Parameters) (r : ℕ) (j : Fin P.n) :
    ProcessRecord P.n → ProgramLabel P.n → PMF (ProcessRecord P.n) → Prop
  /-- The call arrives: record the input. -/
  | callG (p : ProcessRecord P.n) (b : Bool) (h : p.input = none) :
      ProgramStep P r j p (.callG r j b) (PMF.pure { p with input := some b })
  /-- A call addressed elsewhere: not `j`'s business. -/
  | callGIdle (p : ProcessRecord P.n) (i : Fin P.n) (b : Bool) (hi : i ≠ j) :
      ProgramStep P r j p (.callG r i b) (PMF.pure p)
  /-- The call loop: the record does not move. -/
  | callLoop (p : ProcessRecord P.n) (b : Bool) :
      ProgramStep P r j p (.callLoop r j b) (PMF.pure p)
  /-- A call loop at another process: not `j`'s business. -/
  | callLoopIdle (p : ProcessRecord P.n) (i : Fin P.n) (b : Bool) (hi : i ≠ j) :
      ProgramStep P r j p (.callLoop r i b) (PMF.pure p)
  /-- The first gather returns here: record the candidate of its entries. -/
  | firstGatherReturn (p : ProcessRecord P.n) (g : Fin P.n → Option Bool) (C : Gather.AcceptedPairs
    P.n Bool)
      (hin : p.input ≠ none) (hc : p.candidate = none) :
      ProgramStep P r j p (.firstGatherReturn j g C) (PMF.pure { p with
        candidate :=
          some (candidate P g) })
  /-- The first gather's return to another process: not `j`'s business. -/
  | firstGatherReturnIdle (p : ProcessRecord P.n) (i : Fin P.n) (g : Fin P.n → Option Bool)
      (C : Gather.AcceptedPairs P.n Bool) (hi : i ≠ j) :
      ProgramStep P r j p (.firstGatherReturn i g C) (PMF.pure p)
  /-- The second gather is called here with the recorded candidate. -/
  | secondGatherCall (p : ProcessRecord P.n) (x : Option Bool) (hc : p.candidate = some x)
      (h2 : p.secondGatherCalled = false) :
      ProgramStep P r j p (.secondGatherCall j x) (PMF.pure { p with secondGatherCalled := true })
  /-- Another process's call of the second gather: not `j`'s business. -/
  | secondGatherCallIdle (p : ProcessRecord P.n) (i : Fin P.n) (x : Option Bool) (hi : i ≠ j) :
      ProgramStep P r j p (.secondGatherCall i x) (PMF.pure p)
  /-- The second gather returns here: record the grade of its entries. -/
  | secondGatherReturn (p : ProcessRecord P.n) (g : Fin P.n → Option (Option Bool))
      (C : Gather.AcceptedPairs P.n (Option Bool)) (h2 : p.secondGatherCalled = true)
      (ho : p.output = none) :
      ProgramStep P r j p (.secondGatherReturn j g C) (PMF.pure { p with output := some (gradeOf P
        g)
        })
  /-- The second gather's return to another process: not `j`'s business. -/
  | secondGatherReturnIdle (p : ProcessRecord P.n) (i : Fin P.n) (g : Fin P.n → Option (Option
    Bool))
      (C : Gather.AcceptedPairs P.n (Option Bool)) (hi : i ≠ j) :
      ProgramStep P r j p (.secondGatherReturn i g C) (PMF.pure p)
  /-- The round returns the recorded grade. The return announces the grade and the record drops it.
  The announced bit is the round's network's to determine. -/
  | retG (p : ProcessRecord P.n) (out : GBCAOutput) (bnd : Bool) (ho : p.output = some out)
      (hr : p.returned = false) :
      ProgramStep P r j p (.retG r j out bnd)
        (PMF.pure { p with output := none, returned := true })
  /-- A return to another process: not `j`'s business. -/
  | retGIdle (p : ProcessRecord P.n) (i : Fin P.n) (out : GBCAOutput) (bnd : Bool) (hi : i ≠ j) :
      ProgramStep P r j p (.retG r i out bnd) (PMF.pure p)

/-! ### The round's network

The network of the round's programs. It exchanges no message and holds the round's bound
bit alone; no program reads it. The `firstGatherReturn` row writes the bit from the core the first
gather's return carries if it is unwritten, and the `retG` row determines the bit the label
announces. No row fires on the silent label. -/

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
    System (ProcessRecord P.n) (ProgramLabel P.n) where
  init := ProcessRecord.initial P.n
  step := ProgramStep P r j

@[simp] theorem gbcaProgram_init (P : Parameters) (r : ℕ) (j : Fin P.n) :
    (gbcaProgram P r j).init = ProcessRecord.initial P.n := rfl

@[simp] theorem gbcaProgram_step (P : Parameters) (r : ℕ) (j : Fin P.n) (p : ProcessRecord P.n)
    (l : ProgramLabel P.n) (ν : PMF (ProcessRecord P.n)) :
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
    System ((∀ _ : Fin P.n, ProcessRecord P.n) × Option Bool) (RoundLabel P.n) :=
  (System.synchronisedProduct (fun j => (gbcaProgram P r j).mapIdle (programLabelMap P.n))).parallel
    ((GBCANetwork P r).mapIdle (programLabelMap P.n))

@[simp] theorem roundPrograms_init (P : Parameters) (r : ℕ) :
    (roundPrograms P r).init = ((fun _ => ProcessRecord.initial P.n), none) := rfl

/-- The state of the round whose gather instances have states `G₁` and `G₂`. -/
abbrev RoundStateOverGathers (n : ℕ) (G₁ G₂ : Type) : Type :=
  ((∀ _ : Fin n, ProcessRecord n) × Option Bool) × (G₁ × G₂)

/-- The round's programs beside the two gather instances, over the round-internal alphabet. -/
noncomputable def roundOverGathersExtended (P : Parameters) (r : ℕ) {G₁ G₂ : Type}
    (firstGather : System G₁ (Gather.InstanceLabel P.n Bool))
    (secondGather : System G₂ (Gather.InstanceLabel P.n (Option Bool))) :
    System (RoundStateOverGathers P.n G₁ G₂) (RoundLabel P.n) :=
  (roundPrograms P r).parallel ((firstGather.mapIdle (firstGatherLabelMap P.n)).parallel
    (secondGather.mapIdle
    (secondGatherLabelMap P.n)))

/-- **The round-`r` graded-agreement round** over the gather instances `firstGather`,
`secondGather`: the round's programs beside the two of them, the round's events hidden, the result
read over the family alphabet. -/
noncomputable def roundOverGathers (P : Parameters) (r : ℕ) {G₁ G₂ : Type}
    (firstGather : System G₁ (Gather.InstanceLabel P.n Bool))
    (secondGather : System G₂ (Gather.InstanceLabel P.n (Option Bool))) :
    System (RoundStateOverGathers P.n G₁ G₂) (ExtendedLabel P.n) :=
  ((roundOverGathersExtended P r firstGather secondGather).abstract (roundEvents P.n)).relabel

@[simp] theorem roundOverGathers_init (P : Parameters) (r : ℕ) {G₁ G₂ : Type}
    (firstGather : System G₁ (Gather.InstanceLabel P.n Bool))
    (secondGather : System G₂ (Gather.InstanceLabel P.n (Option Bool))) :
    (roundOverGathers P r firstGather secondGather).init =
      (((fun _ => ProcessRecord.initial P.n), none), (firstGather.init, secondGather.init)) := rfl

/-- The state of the round over the gather instances over Bracha's
broadcast. -/
abbrev RoundStateOverBracha (n : ℕ) : Type :=
  RoundStateOverGathers n (Gather.StateOverBracha n Bool) (Gather.StateOverBracha n (Option Bool))

/-- The state of the round over the gather instances over the broadcast
specification. -/
abbrev RoundStateOverBroadcastSpecification (n : ℕ) : Type :=
  RoundStateOverGathers n (Gather.StateOverBroadcastSpecification n Bool)
    (Gather.StateOverBroadcastSpecification n (Option Bool))

/-- The state of the round over the gather specifications. -/
abbrev RoundStateOverGatherSpecifications (n : ℕ) : Type :=
  RoundStateOverGathers n (Gather.SpecState n Bool) (Gather.SpecState n (Option Bool))

/-- **The round over the gather instances over Bracha's broadcast.** -/
noncomputable def roundOverBracha (P : Parameters) (r : ℕ) :
    System (RoundStateOverBracha P.n) (ExtendedLabel P.n) :=
  roundOverGathers P r (Gather.instanceOverBracha P Bool) (Gather.instanceOverBracha P (Option
    Bool))

/-- **The round over the gather instances over the broadcast
specification.** -/
noncomputable def roundOverBroadcastSpecification (P : Parameters) (r : ℕ) :
    System (RoundStateOverBroadcastSpecification P.n) (ExtendedLabel P.n) :=
  roundOverGathers P r (Gather.instanceOverBroadcastSpecification P Bool)
    (Gather.instanceOverBroadcastSpecification P (Option Bool))

/-- **The round over the gather specifications.** -/
noncomputable def roundOverGatherSpecifications (P : Parameters) (r : ℕ) :
    System (RoundStateOverGatherSpecifications P.n) (ExtendedLabel P.n) :=
  roundOverGathers P r (Gather.specificationOverInstanceAlphabet P Bool)
    (Gather.specificationOverInstanceAlphabet P (Option Bool))

@[simp] theorem roundOverBracha_init (P : Parameters) (r : ℕ) :
    (roundOverBracha P r).init =
      (((fun _ => ProcessRecord.initial P.n), none),
        ((Gather.instanceOverBracha P Bool).init,
          (Gather.instanceOverBracha P (Option Bool)).init)) := rfl

@[simp] theorem roundOverBroadcastSpecification_init (P : Parameters) (r : ℕ) :
    (roundOverBroadcastSpecification P r).init =
      (((fun _ => ProcessRecord.initial P.n), none),
        ((Gather.instanceOverBroadcastSpecification P Bool).init,
          (Gather.instanceOverBroadcastSpecification P (Option Bool)).init)) := rfl

@[simp] theorem roundOverGatherSpecifications_init (P : Parameters) (r : ℕ) :
    (roundOverGatherSpecifications P r).init =
      (((fun _ => ProcessRecord.initial P.n), none),
        (Gather.SpecState.initial P.n Bool, Gather.SpecState.initial P.n (Option Bool))) := rfl

/-! ### Views of the round's state

The four components of the round's state, and the four writes that reach one of
them. A row is stated through these, so that a guard reads `programs s id` where a
the implementation reads the program function. -/

section Views

variable {n : ℕ} {G₁ G₂ : Type}

/-- The programs. -/
def programs (s : RoundStateOverGathers n G₁ G₂) : ∀ _ : Fin n, ProcessRecord n := s.1.1

/-- The round's bound bit. -/
def bound (s : RoundStateOverGathers n G₁ G₂) : Option Bool := s.1.2

/-- The first gather instance. -/
def firstGather (s : RoundStateOverGathers n G₁ G₂) : G₁ := s.2.1

/-- The second gather instance. -/
def secondGather (s : RoundStateOverGathers n G₁ G₂) : G₂ := s.2.2

/-- Overwrite the programs. -/
def setPrograms (s : RoundStateOverGathers n G₁ G₂) (u : ∀ _ : Fin n, ProcessRecord n) :
    RoundStateOverGathers n G₁ G₂ := ((u, s.1.2), s.2)

/-- Overwrite the round's bound bit. -/
def setBound (s : RoundStateOverGathers n G₁ G₂) (v : Option Bool) : RoundStateOverGathers n G₁ G₂
  :=
  ((s.1.1, v), s.2)

/-- Overwrite the first gather instance. -/
def setFirstGather (s : RoundStateOverGathers n G₁ G₂) (c : G₁) : RoundStateOverGathers n G₁ G₂ :=
  (s.1, (c, s.2.2))

/-- Overwrite the second gather instance. -/
def setSecondGather (s : RoundStateOverGathers n G₁ G₂) (d : G₂) : RoundStateOverGathers n G₁ G₂ :=
  (s.1, (s.2.1, d))

@[simp] theorem programs_setPrograms (s : RoundStateOverGathers n G₁ G₂) (u : ∀ _ : Fin n,
    ProcessRecord n) : programs (setPrograms s u) = u := rfl
@[simp] theorem bound_setPrograms (s : RoundStateOverGathers n G₁ G₂) (u : ∀ _ : Fin n,
    ProcessRecord n) : bound (setPrograms s u) = bound s := rfl
@[simp] theorem firstGather_setPrograms (s : RoundStateOverGathers n G₁ G₂) (u : ∀ _ : Fin n,
    ProcessRecord n) : firstGather (setPrograms s u) = firstGather s := rfl
@[simp] theorem secondGather_setPrograms (s : RoundStateOverGathers n G₁ G₂) (u : ∀ _ : Fin n,
    ProcessRecord n) : secondGather (setPrograms s u) = secondGather s := rfl

@[simp] theorem programs_setBound (s : RoundStateOverGathers n G₁ G₂) (v : Option Bool) :
    programs (setBound s v) = programs s := rfl
@[simp] theorem bound_setBound (s : RoundStateOverGathers n G₁ G₂) (v : Option Bool) :
    bound (setBound s v) = v := rfl
@[simp] theorem firstGather_setBound (s : RoundStateOverGathers n G₁ G₂) (v : Option Bool) :
    firstGather (setBound s v) = firstGather s := rfl
@[simp] theorem secondGather_setBound (s : RoundStateOverGathers n G₁ G₂) (v : Option Bool) :
    secondGather (setBound s v) = secondGather s := rfl

@[simp] theorem programs_setFirstGather (s : RoundStateOverGathers n G₁ G₂) (c : G₁) :
    programs (setFirstGather s c) = programs s := rfl
@[simp] theorem bound_setFirstGather (s : RoundStateOverGathers n G₁ G₂) (c : G₁) :
    bound (setFirstGather s c) = bound s := rfl
@[simp] theorem firstGather_setFirstGather (s : RoundStateOverGathers n G₁ G₂) (c : G₁) :
  firstGather (setFirstGather s c) = c := rfl
@[simp] theorem secondGather_setFirstGather (s : RoundStateOverGathers n G₁ G₂) (c : G₁) :
    secondGather (setFirstGather s c) = secondGather s := rfl

@[simp] theorem programs_setSecondGather (s : RoundStateOverGathers n G₁ G₂) (d : G₂) :
    programs (setSecondGather s d) = programs s := rfl
@[simp] theorem bound_setSecondGather (s : RoundStateOverGathers n G₁ G₂) (d : G₂) :
    bound (setSecondGather s d) = bound s := rfl
@[simp] theorem firstGather_setSecondGather (s : RoundStateOverGathers n G₁ G₂) (d : G₂) :
    firstGather (setSecondGather s d) = firstGather s := rfl
@[simp] theorem secondGather_setSecondGather (s : RoundStateOverGathers n G₁ G₂) (d : G₂) :
  secondGather (setSecondGather s d) = d := rfl

/-- Corruption (deviation D1): the two gather instances corrupted at `id`, the
programs and the round's bound bit untouched. -/
def corruptAll (P : Parameters) (id : Fin P.n) (corruptFirstGather : Fin P.n → G₁ → G₁)
    (corruptSecondGather : Fin P.n → G₂ → G₂) (s : RoundStateOverGathers P.n G₁ G₂) :
    RoundStateOverGathers P.n G₁ G₂ :=
  (s.1, (corruptFirstGather id s.2.1, corruptSecondGather id s.2.2))

@[simp] theorem programs_corruptAll (P : Parameters) (id : Fin P.n)
    (corruptFirstGather : Fin P.n → G₁ → G₁) (corruptSecondGather : Fin P.n → G₂ → G₂)
    (s : RoundStateOverGathers P.n G₁ G₂) :
    programs (corruptAll P id corruptFirstGather corruptSecondGather s) = programs s := rfl
@[simp] theorem bound_corruptAll (P : Parameters) (id : Fin P.n)
    (corruptFirstGather : Fin P.n → G₁ → G₁) (corruptSecondGather : Fin P.n → G₂ → G₂)
    (s : RoundStateOverGathers P.n G₁ G₂) :
    bound (corruptAll P id corruptFirstGather corruptSecondGather s) = bound s := rfl
@[simp] theorem firstGather_corruptAll (P : Parameters) (id : Fin P.n)
    (corruptFirstGather : Fin P.n → G₁ → G₁) (corruptSecondGather : Fin P.n → G₂ → G₂)
    (s : RoundStateOverGathers P.n G₁ G₂) :
    firstGather (corruptAll P id corruptFirstGather corruptSecondGather s) =
      corruptFirstGather id (firstGather s) := rfl
@[simp] theorem secondGather_corruptAll (P : Parameters) (id : Fin P.n)
    (corruptFirstGather : Fin P.n → G₁ → G₁) (corruptSecondGather : Fin P.n → G₂ → G₂)
    (s : RoundStateOverGathers P.n G₁ G₂) :
    secondGather (corruptAll P id corruptFirstGather corruptSecondGather s) =
      corruptSecondGather id (secondGather s) := rfl

end Views

/-! ### Determinacy

Both rule tables written here are Dirac, so the round is an LTS whenever the
two gather instances are. -/

section Determinacy

variable {P : Parameters} {r : ℕ}

/-- Every program transition is Dirac. -/
theorem programStep_dirac {j : Fin P.n} {p : ProcessRecord P.n} {l : ProgramLabel P.n}
    {ν : PMF (ProcessRecord P.n)} (h : ProgramStep P r j p l ν) : ∃ p', ν = PMF.pure p' := by
  cases h <;> exact ⟨_, rfl⟩

/-- Every transition of the round's network is Dirac. -/
theorem networkStep_dirac {w : Option Bool} {l : ProgramLabel P.n} {μ : PMF (Option Bool)}
    (h : NetworkStep P r w l μ) : ∃ w', μ = PMF.pure w' := by
  cases h <;> exact ⟨_, rfl⟩

/-- A program is an LTS. -/
theorem gbcaProgram_isLTS (P : Parameters) (r : ℕ) (j : Fin P.n) : (gbcaProgram P r j).IsLTS :=
  fun _ _ _ h => programStep_dirac h

/-- The round's network is an LTS. -/
theorem GBCANetwork_isLTS (P : Parameters) (r : ℕ) : (GBCANetwork P r).IsLTS :=
  fun _ _ _ h => networkStep_dirac h

/-- The synchronised group of programs is an LTS. -/
theorem programsProduct_isLTS (P : Parameters) (r : ℕ) :
    (System.synchronisedProduct (fun j => (gbcaProgram P r j).mapIdle (programLabelMap P.n))).IsLTS
      :=
  System.synchronisedProduct_isLTS (fun j => System.mapIdle_isLTS _ (gbcaProgram_isLTS P r j))

/-- The round's programs form an LTS. -/
theorem roundPrograms_isLTS (P : Parameters) (r : ℕ) : (roundPrograms P r).IsLTS :=
  System.parallel_isLTS (programsProduct_isLTS P r)
    (System.mapIdle_isLTS _ (GBCANetwork_isLTS P r))

/-- The round's programs beside the two gather instances is an LTS. -/
theorem roundOverGathersExtended_isLTS (P : Parameters) (r : ℕ) {G₁ G₂ : Type}
    {firstGather : System G₁ (Gather.InstanceLabel P.n Bool)}
    {secondGather : System G₂ (Gather.InstanceLabel P.n (Option Bool))} (h1 : firstGather.IsLTS)
    (h2 : secondGather.IsLTS) : (roundOverGathersExtended P r firstGather secondGather).IsLTS :=
  System.parallel_isLTS (roundPrograms_isLTS P r)
    (System.parallel_isLTS (System.mapIdle_isLTS _ h1) (System.mapIdle_isLTS _ h2))

/-- The round is an LTS. -/
theorem roundOverGathers_isLTS (P : Parameters) (r : ℕ) {G₁ G₂ : Type}
    {firstGather : System G₁ (Gather.InstanceLabel P.n Bool)}
    {secondGather : System G₂ (Gather.InstanceLabel P.n (Option Bool))} (h1 : firstGather.IsLTS)
    (h2 : secondGather.IsLTS) : (roundOverGathers P r firstGather secondGather).IsLTS :=
  System.relabel_isLTS (System.abstract_isLTS (roundOverGathersExtended_isLTS P r h1 h2) _)

/-- The round over the gather instances over Bracha's broadcast is an LTS. -/
theorem roundOverBracha_isLTS (P : Parameters) (r : ℕ) : (roundOverBracha P r).IsLTS :=
  roundOverGathers_isLTS P r (Gather.instanceOverBracha_isLTS P) (Gather.instanceOverBracha_isLTS P)

/-- The round over the gather instances over the broadcast specification is an
LTS. -/
theorem roundOverBroadcastSpecification_isLTS (P : Parameters) (r : ℕ) :
  (roundOverBroadcastSpecification P r).IsLTS :=
  roundOverGathers_isLTS P r (Gather.instanceOverBroadcastSpecification_isLTS P)
    (Gather.instanceOverBroadcastSpecification_isLTS P)

/-- The round over the gather specifications is an LTS. -/
theorem roundOverGatherSpecifications_isLTS (P : Parameters) (r : ℕ) :
    (roundOverGatherSpecifications P r).IsLTS :=
  roundOverGathers_isLTS P r (Gather.specificationOverInstanceAlphabet_isLTS P)
    (Gather.specificationOverInstanceAlphabet_isLTS P)

/-- No program rule fires on the silent label: a program only ever moves on one
of the round's ports or one of its events. -/
theorem programStep_no_tau {j : Fin P.n} {p : ProcessRecord P.n} {ν : PMF (ProcessRecord P.n)}
    (h : ProgramStep P r j p (Silent.τ : ProgramLabel P.n) ν) : False := by
  rw [programLabel_tau] at h; cases h

/-- No rule of the round's network fires on the silent label. -/
theorem networkStep_no_tau {w : Option Bool} {μ : PMF (Option Bool)}
    (h : NetworkStep P r w (Silent.τ : ProgramLabel P.n) μ) : False := by
  rw [programLabel_tau] at h; cases h

/-- No program rule fires on a family label outside the round's interface. -/
theorem programStep_outside {j : Fin P.n} {p : ProcessRecord P.n} {ν : PMF (ProcessRecord P.n)}
    (h : ProgramStep P r j p ProgramLabel.outside ν) : False := by cases h

/-- No rule of the round's network fires on a family label outside the round's interface. -/
theorem networkStep_outside {w : Option Bool} {μ : PMF (Option Bool)}
    (h : NetworkStep P r w ProgramLabel.outside μ) : False := by cases h

/-- The program group has no silent transition. -/
theorem programsProduct_no_tau {u : ∀ _ : Fin P.n, ProcessRecord P.n}
    {μ : PMF (∀ _ : Fin P.n, ProcessRecord P.n)}
    (h : (System.synchronisedProduct (fun j => (gbcaProgram P r j).mapIdle (programLabelMap
      P.n))).step u
      (Silent.τ : RoundLabel P.n) μ) : False := by
  rcases h with ⟨hτ, -⟩ | ⟨-, i, μ_i, hstep, -⟩
  · exact hτ rfl
  · exact programStep_no_tau ((System.mapIdle_step_some (programLabelMap_tau P.n) _).mp hstep)

/-- The round's programs have no silent transition: neither a program nor the round's network fires
on the silent label. -/
theorem roundPrograms_no_tau {u : ∀ _ : Fin P.n, ProcessRecord P.n} {v : Option Bool}
    {μ : PMF ((∀ _ : Fin P.n, ProcessRecord P.n) × Option Bool)}
    (h : (roundPrograms P r).step (u, v) (Silent.τ : RoundLabel P.n) μ) : False := by
  rw [roundPrograms, System.parallel_step] at h
  rcases h with ⟨hτ, -⟩ | ⟨-, μ₁, hs, -⟩ | ⟨-, μ₂, hn, -⟩
  · exact hτ rfl
  · exact programsProduct_no_tau hs
  · exact networkStep_no_tau ((System.mapIdle_step_some (programLabelMap_tau P.n) _).mp hn)

end Determinacy

/-! ### Reading and building the round's transitions

The pipeline is `relabel ∘ abstract ∘ parallel ∘ (parallel ∘ synchronisedProduct,
mapIdle, mapIdle)`; the lemmas below unfold it once and for all, in both
directions. -/

/-- The round's step relation, unfolded to the hidden-event case and the
family-label case. -/
theorem roundOverGathers_step_iff (P : Parameters) (r : ℕ) {G₁ G₂ : Type}
    (firstGather : System G₁ (Gather.InstanceLabel P.n Bool))
    (secondGather : System G₂ (Gather.InstanceLabel P.n (Option Bool)))
    (s : RoundStateOverGathers P.n G₁ G₂) (l : ExtendedLabel P.n)
    (μ : PMF (RoundStateOverGathers P.n G₁ G₂)) :
    (roundOverGathers P r firstGather secondGather).step s l μ ↔
      (l = Sum.inl Label.tau ∧ ∃ e : RoundEvent P.n,
        (roundOverGathersExtended P r firstGather secondGather).step s (Sum.inr e) μ) ∨
      (roundOverGathersExtended P r firstGather secondGather).step s (Sum.inl l) μ := by
  constructor
  · rintro (⟨hτ, l', ⟨e, rfl⟩, hstep⟩ | ⟨-, hstep⟩)
    · exact Or.inl ⟨Sum.inl_injective hτ, e, hstep⟩
    · exact Or.inr hstep
  · rintro (⟨rfl, e, hstep⟩ | hstep)
    · exact Or.inl ⟨rfl, _, inr_mem_roundEvents e, hstep⟩
    · exact Or.inr ⟨inl_notMem_roundEvents l, hstep⟩

/-! ### The transitions of the round's programs

On a label with no image at a program the round's programs remain unchanged. On a label with an image
every program takes its row at that image and the round's network takes its. -/

section RoundPrograms

variable {P : Parameters} {r : ℕ} {u x : ∀ _ : Fin P.n, ProcessRecord P.n} {v v' : Option Bool}
  {L : RoundLabel P.n}

/-- A label with an image other than the silent one is visible. -/
theorem roundLabel_ne_tau {lp : ProgramLabel P.n} (hlp : programLabelMap P.n L = some lp)
    (hlpτ : lp ≠ ProgramLabel.tau) :
    L ≠ (Silent.τ : RoundLabel P.n) := by
  intro hc
  subst hc
  rw [programLabelMap_tau] at hlp
  exact hlpτ (Option.some.inj hlp).symm

/-- A label with no image at a program is visible. -/
theorem roundLabel_ne_tau_of_none (hlp : programLabelMap P.n L = none) :
    L ≠ (Silent.τ : RoundLabel P.n) := by
  intro hc
  subst hc
  rw [programLabelMap_tau] at hlp
  exact Option.some_ne_none _ hlp

/-- A synchronised transition of the program group on a visible label: every
program steps, and the joint distribution is Dirac. -/
theorem programsProduct_inversion (hL : L ≠ (Silent.τ : RoundLabel P.n))
    {μ : PMF (∀ _ : Fin P.n, ProcessRecord P.n)}
    (h : (System.synchronisedProduct (fun j => (gbcaProgram P r j).mapIdle (programLabelMap
      P.n))).step u L
      μ) :
    ∃ x : ∀ _ : Fin P.n, ProcessRecord P.n, μ = PMF.pure x ∧
      ∀ i, ((gbcaProgram P r i).mapIdle (programLabelMap P.n)).step (u i) L (PMF.pure (x i)) :=
  System.synchronisedProductMapIdle_inversion (fun i => gbcaProgram_isLTS P r i) hL h

/-- **The round's programs remain unchanged** on a label with no image at a program. -/
theorem roundPrograms_idle_inversion (hlp : programLabelMap P.n L = none)
    {μ : PMF ((∀ _ : Fin P.n, ProcessRecord P.n) × Option Bool)}
    (h : (roundPrograms P r).step (u, v) L μ) : μ = PMF.pure (u, v) := by
  have hL := roundLabel_ne_tau_of_none hlp
  rw [roundPrograms, System.parallel_step] at h
  rcases h with ⟨-, μ₁, μ₂, hs, hn, rfl⟩ | ⟨hτ, -⟩ | ⟨hτ, -⟩
  · obtain ⟨y, rfl, hall⟩ := programsProduct_inversion hL hs
    have hy : y = u := funext fun i => System.mapIdle_eq_of_step_none hlp (hall i)
    subst hy
    rw [(System.mapIdle_step_none hlp _).mp hn, prodPMF_pure_pure]
  · exact absurd hτ hL
  · exact absurd hτ hL

/-- **The joint transition of the round's programs.** Every program takes its row at the label's
image and the round's network takes its. -/
theorem roundPrograms_label_inversion {lp : ProgramLabel P.n}
    (hlp : programLabelMap P.n L = some lp) (hlpτ : lp ≠ ProgramLabel.tau)
    {μ : PMF ((∀ _ : Fin P.n, ProcessRecord P.n) × Option Bool)}
    (h : (roundPrograms P r).step (u, v) L μ) :
    ∃ (x : ∀ _ : Fin P.n, ProcessRecord P.n) (v' : Option Bool), μ = PMF.pure (x, v') ∧
    (∀ i, ProgramStep P r i (u i) lp (PMF.pure (x i))) ∧ NetworkStep P r v lp (PMF.pure v') := by
  have hL := roundLabel_ne_tau hlp hlpτ
  rw [roundPrograms, System.parallel_step] at h
  rcases h with ⟨-, μ₁, μ₂, hs, hn, rfl⟩ | ⟨hτ, -⟩ | ⟨hτ, -⟩
  · obtain ⟨y, rfl, hall⟩ := programsProduct_inversion hL hs
    have hnet : NetworkStep P r v lp μ₂ := (System.mapIdle_step_some hlp _).mp hn
    obtain ⟨v', rfl⟩ := networkStep_dirac hnet
    exact ⟨y, v', prodPMF_pure_pure _ _, fun i => System.step_of_mapIdle_step hlp (hall i), hnet⟩
  · exact absurd hτ hL
  · exact absurd hτ hL

/-- **The round's programs refuse** a family label outside the round's interface. -/
theorem roundPrograms_outside_inversion (hlp : programLabelMap P.n L = some ProgramLabel.outside)
    {μ : PMF ((∀ _ : Fin P.n, ProcessRecord P.n) × Option Bool)}
    (h : (roundPrograms P r).step (u, v) L μ) : False := by
  obtain ⟨y, w, -, -, hnet⟩ := roundPrograms_label_inversion hlp (by simp) h
  exact networkStep_outside hnet

/-- The stutter of the round's programs, read off a Dirac successor. -/
theorem roundPrograms_idle_pure (hlp : programLabelMap P.n L = none)
    (h : (roundPrograms P r).step (u, v) L (PMF.pure (x, v'))) : x = u ∧ v' = v := by
  have he := PMF.pure_injective (roundPrograms_idle_inversion hlp h)
  rw [Prod.mk.injEq] at he
  exact he

/-- The joint transition of the round's programs, read off a Dirac successor. -/
theorem roundPrograms_label_pure {lp : ProgramLabel P.n} (hlp : programLabelMap P.n L = some lp)
    (hlpτ : lp ≠ ProgramLabel.tau) (h : (roundPrograms P r).step (u, v) L (PMF.pure (x, v'))) :
    (∀ i, ProgramStep P r i (u i) lp (PMF.pure (x i))) ∧ NetworkStep P r v lp (PMF.pure v') := by
  obtain ⟨y, w, hμ, hproc, hnet⟩ := roundPrograms_label_inversion hlp hlpτ h
  have he := PMF.pure_injective hμ
  rw [Prod.mk.injEq] at he
  obtain ⟨rfl, rfl⟩ := he
  exact ⟨hproc, hnet⟩

/-- Build the stutter of the round's programs on a label with no image at a program. -/
theorem roundPrograms_idle_step (hlp : programLabelMap P.n L = none) :
    (roundPrograms P r).step (u, v) L (PMF.pure (u, v)) := by
  rw [roundPrograms, System.parallel_step]
  exact Or.inl ⟨roundLabel_ne_tau_of_none hlp, PMF.pure u, PMF.pure v,
    System.synchronisedProductMapIdle_pure (roundLabel_ne_tau_of_none hlp)
      (fun i => System.mapIdle_unchanged hlp),
    System.mapIdle_unchanged hlp, (prodPMF_pure_pure _ _).symm⟩

/-- Build the joint transition of the round's programs from the programs' rows and the row of the
round's network. -/
theorem roundPrograms_label_step {lp : ProgramLabel P.n} (hlp : programLabelMap P.n L = some lp)
    (hlpτ : lp ≠ ProgramLabel.tau) (hproc : ∀ i, ProgramStep P r i (u i) lp (PMF.pure (x i)))
    (hnet : NetworkStep P r v lp (PMF.pure v')) :
    (roundPrograms P r).step (u, v) L (PMF.pure (x, v')) := by
  rw [roundPrograms, System.parallel_step]
  exact Or.inl ⟨roundLabel_ne_tau hlp hlpτ, PMF.pure x, PMF.pure v',
    System.synchronisedProductMapIdle_pure (roundLabel_ne_tau hlp hlpτ)
      (fun i => System.mapIdle_step_of_step hlp (hproc i)),
    System.mapIdle_step_of_step hlp hnet, (prodPMF_pure_pure _ _).symm⟩

/-- The participant's row beside the idle rows of every other program is the
program group stepping into the updated function. -/
theorem programStep_update {j : Fin P.n} {q : ProcessRecord P.n} {lp : ProgramLabel P.n}
    (hj : ProgramStep P r j (u j) lp (PMF.pure q))
    (hne : ∀ i, i ≠ j → ProgramStep P r i (u i) lp (PMF.pure (u i))) :
    ∀ i, ProgramStep P r i (u i) lp (PMF.pure (Function.update u j q i)) := by
  intro i
  by_cases hi : i = j
  · subst hi; rw [Function.update_self]; exact hj
  · rw [Function.update_of_ne hi]; exact hne i hi

end RoundPrograms

/-! ### The round's programs beside the two gather instances

A visible label moves all three factors, and the joint distribution is their Dirac product. A silent
label moves exactly one of the two gather instances: the round's programs have no silent
transition. -/

section RoundPre

variable {P : Parameters} {r : ℕ} {G₁ G₂ : Type}
  {firstGather : System G₁ (Gather.InstanceLabel P.n Bool)}
  {secondGather : System G₂ (Gather.InstanceLabel P.n (Option Bool))}
  {u x : ∀ _ : Fin P.n, ProcessRecord P.n} {v v' : Option Bool} {c c' : G₁} {d d' : G₂}
  {L : RoundLabel P.n}

/-- **The joint inversion.** A visible transition of the round's programs beside the two gather
instances: every factor steps on the label, and the joint distribution is their Dirac product. -/
theorem roundOverGathersExtended_joint_inversion (h1 : firstGather.IsLTS) (h2 : secondGather.IsLTS)
    (hL : L ≠ (Silent.τ : RoundLabel P.n)) {μ : PMF (RoundStateOverGathers P.n G₁ G₂)}
    (h : (roundOverGathersExtended P r firstGather secondGather).step ((u, v), (c, d)) L μ) :
    ∃ (x : ∀ _ : Fin P.n, ProcessRecord P.n) (v' : Option Bool) (c' : G₁) (d' : G₂),
      μ = PMF.pure ((x, v'), (c', d')) ∧
      (roundPrograms P r).step (u, v) L (PMF.pure (x, v')) ∧
      (firstGather.mapIdle (firstGatherLabelMap P.n)).step c L (PMF.pure c') ∧
      (secondGather.mapIdle (secondGatherLabelMap P.n)).step d L (PMF.pure d') := by
  rw [roundOverGathersExtended, System.parallel_step] at h
  rcases h with ⟨-, μ₁, μ₂, hlay, hga, rfl⟩ | ⟨hτ, -⟩ | ⟨hτ, -⟩
  · obtain ⟨⟨y, w⟩, rfl⟩ := roundPrograms_isLTS P r _ _ _ hlay
    rw [System.parallel_step] at hga
    rcases hga with ⟨-, ρ₁, ρ₂, hc, hd, rfl⟩ | ⟨hτ, -⟩ | ⟨hτ, -⟩
    · obtain ⟨c', rfl⟩ := System.mapIdle_isLTS _ h1 _ _ _ hc
      obtain ⟨d', rfl⟩ := System.mapIdle_isLTS _ h2 _ _ _ hd
      exact ⟨y, w, c', d', by rw [prodPMF_pure_pure, prodPMF_pure_pure], hlay, hc, hd⟩
    · exact absurd hτ hL
    · exact absurd hτ hL
  · exact absurd hτ hL
  · exact absurd hτ hL

/-- **The silent inversion.** A silent transition of the round's programs beside the two gather
instances is a silent step of one gather instance. -/
theorem roundOverGathersExtended_tau_inversion (h1 : firstGather.IsLTS) (h2 : secondGather.IsLTS)
    {μ : PMF (RoundStateOverGathers P.n G₁ G₂)}
    (h : (roundOverGathersExtended P r firstGather secondGather).step ((u, v), (c,
      d)) (Silent.τ : RoundLabel P.n) μ) :
    (∃ c', μ = PMF.pure ((u, v), (c', d)) ∧
      firstGather.step c (Silent.τ : Gather.InstanceLabel P.n Bool) (PMF.pure c')) ∨
    (∃ d', μ = PMF.pure ((u, v), (c, d')) ∧
      secondGather.step d (Silent.τ : Gather.InstanceLabel P.n (Option Bool)) (PMF.pure d')) := by
  rw [roundOverGathersExtended, System.parallel_step] at h
  rcases h with ⟨hτ, -⟩ | ⟨-, μ₁, hlay, rfl⟩ | ⟨-, μ₂, hga, rfl⟩
  · exact absurd rfl hτ
  · exact absurd hlay roundPrograms_no_tau
  · rw [System.parallel_step] at hga
    rcases hga with ⟨hτ, -⟩ | ⟨-, ρ₁, hc, rfl⟩ | ⟨-, ρ₂, hd, rfl⟩
    · exact absurd rfl hτ
    · have hstep := (System.mapIdle_step_some (firstGatherLabelMap_tau P.n) _).mp hc
      obtain ⟨c', rfl⟩ := h1 _ _ _ hstep
      exact Or.inl ⟨c', by rw [prodPMF_pure_pure, prodPMF_pure_pure], hstep⟩
    · have hstep := (System.mapIdle_step_some (secondGatherLabelMap_tau P.n) _).mp hd
      obtain ⟨d', rfl⟩ := h2 _ _ _ hstep
      exact Or.inr ⟨d', by rw [prodPMF_pure_pure, prodPMF_pure_pure], hstep⟩

/-- Build a visible transition of the round's programs beside the two gather instances. -/
theorem roundOverGathersExtended_label_step (hL : L ≠ (Silent.τ : RoundLabel P.n))
    (hRoundPrograms : (roundPrograms P r).step (u, v) L (PMF.pure (x, v')))
    (hga1 : (firstGather.mapIdle (firstGatherLabelMap P.n)).step c L (PMF.pure c'))
    (hga2 : (secondGather.mapIdle (secondGatherLabelMap P.n)).step d L (PMF.pure d')) :
    (roundOverGathersExtended P r firstGather secondGather).step ((u, v), (c, d)) L
    (PMF.pure ((x, v'), (c', d'))) := by
  rw [roundOverGathersExtended, System.parallel_step]
  refine Or.inl ⟨hL, PMF.pure (x, v'), PMF.pure (c', d'), hRoundPrograms, ?_,
    (prodPMF_pure_pure _ _).symm⟩
  rw [System.parallel_step]
  exact Or.inl ⟨hL, PMF.pure c', PMF.pure d', hga1, hga2, (prodPMF_pure_pure _ _).symm⟩

/-- Build a silent transition of the round's programs beside the two gather instances from a silent
step of the first gather. -/
theorem roundOverGathersExtended_tau_firstGather
    (h : firstGather.step c (Silent.τ : Gather.InstanceLabel P.n Bool) (PMF.pure c')) :
    (roundOverGathersExtended P r firstGather secondGather).step ((u, v), (c, d))
    (Silent.τ : RoundLabel P.n) (PMF.pure ((u, v), (c', d))) := by
  rw [roundOverGathersExtended, System.parallel_step]
  refine Or.inr (Or.inr ⟨rfl, PMF.pure (c', d), ?_, (prodPMF_pure_pure _ _).symm⟩)
  rw [System.parallel_step]
  exact Or.inr (Or.inl ⟨rfl, PMF.pure c',
    (System.mapIdle_step_some (firstGatherLabelMap_tau P.n) _).mpr h, (prodPMF_pure_pure _ _).symm⟩)

/-- Build a silent transition of the round's programs beside the two gather instances from a silent
step of the second gather. -/
theorem roundOverGathersExtended_tau_secondGather
    (h : secondGather.step d (Silent.τ : Gather.InstanceLabel P.n (Option Bool)) (PMF.pure d')) :
    (roundOverGathersExtended P r firstGather secondGather).step ((u, v), (c, d))
    (Silent.τ : RoundLabel P.n) (PMF.pure ((u, v), (c, d'))) := by
  rw [roundOverGathersExtended, System.parallel_step]
  refine Or.inr (Or.inr ⟨rfl, PMF.pure (c, d'), ?_, (prodPMF_pure_pure _ _).symm⟩)
  rw [System.parallel_step]
  exact Or.inr (Or.inr ⟨rfl, PMF.pure d',
    (System.mapIdle_step_some (secondGatherLabelMap_tau P.n) _).mpr h,
      (prodPMF_pure_pure _ _).symm⟩)

/-- A hidden event is a silent transition of the round. -/
theorem roundOverGathers_event_step (e : RoundEvent P.n)
    (hRoundPrograms : (roundPrograms P r).step (u, v) (Sum.inr e) (PMF.pure (x, v')))
    (hga1 : (firstGather.mapIdle (firstGatherLabelMap P.n)).step c (Sum.inr e) (PMF.pure c'))
    (hga2 : (secondGather.mapIdle (secondGatherLabelMap P.n)).step d (Sum.inr e) (PMF.pure d')) :
    (roundOverGathers P r firstGather secondGather).step ((u, v), (c, d)) (Sum.inl Label.tau)
      (PMF.pure ((x, v'), (c', d'))) :=
  (roundOverGathers_step_iff P r firstGather secondGather _ _ _).mpr
    (Or.inl ⟨rfl, e, roundOverGathersExtended_label_step (by simp) hRoundPrograms hga1 hga2⟩)

/-- A visible family label is a transition of the round. -/
theorem roundOverGathers_label_step {l : ExtendedLabel P.n} (hl : l ≠ Sum.inl Label.tau)
    (hRoundPrograms : (roundPrograms P r).step (u, v) (Sum.inl l) (PMF.pure (x, v')))
    (hga1 : (firstGather.mapIdle (firstGatherLabelMap P.n)).step c (Sum.inl l) (PMF.pure c'))
    (hga2 : (secondGather.mapIdle (secondGatherLabelMap P.n)).step d (Sum.inl l) (PMF.pure d')) :
    (roundOverGathers P r firstGather secondGather).step ((u, v), (c, d)) l
    (PMF.pure ((x, v'), (c', d'))) := by
  refine (roundOverGathers_step_iff P r firstGather secondGather _ _ _).mpr
    (Or.inr (roundOverGathersExtended_label_step ?_ hRoundPrograms hga1 hga2))
  rw [roundLabel_tau]
  simpa using hl

/-- A silent step of the first gather is a silent transition of the round. -/
theorem roundOverGathers_tau_firstGather
    (h : firstGather.step c (Silent.τ : Gather.InstanceLabel P.n Bool) (PMF.pure c')) :
    (roundOverGathers P r firstGather secondGather).step ((u, v), (c, d)) (Sum.inl Label.tau)
    (PMF.pure ((u, v), (c', d))) :=
  (roundOverGathers_step_iff P r firstGather secondGather _ _ _).mpr (Or.inr
    (roundOverGathersExtended_tau_firstGather h))

/-- A silent step of the second gather is a silent transition of the round. -/
theorem roundOverGathers_tau_secondGather
    (h : secondGather.step d (Silent.τ : Gather.InstanceLabel P.n (Option Bool)) (PMF.pure d')) :
    (roundOverGathers P r firstGather secondGather).step ((u, v), (c, d)) (Sum.inl Label.tau)
      (PMF.pure ((u, v), (c, d'))) :=
  (roundOverGathers_step_iff P r firstGather secondGather _ _ _).mpr (Or.inr
    (roundOverGathersExtended_tau_secondGather h))

end RoundPre

/-! ### One program's rules, by label class

Each lemma reads a row of the table off its label: the participant's row as its
guards together with the Dirac it produces, and the idle row of a
non-participant as the identity. -/

section ProcInversion

variable {P : Parameters} {r : ℕ} {j : Fin P.n} {p : ProcessRecord P.n} {ν : PMF (ProcessRecord
  P.n)}

/-- A call row names the program's own round. -/
theorem programStep_callG_round {r' : ℕ} {i : Fin P.n} {b : Bool}
    (h : ProgramStep P r j p (.callG r' i b) ν) : r' = r := by cases h <;> rfl

/-- A call-loop row names the program's own round. -/
theorem programStep_callLoop_round {r' : ℕ} {i : Fin P.n} {b : Bool}
    (h : ProgramStep P r j p (.callLoop r' i b) ν) : r' = r := by cases h <;> rfl

/-- A return row names the program's own round. -/
theorem programStep_retG_round {r' : ℕ} {i : Fin P.n} {out : GBCAOutput} {bnd : Bool}
    (h : ProgramStep P r j p (.retG r' i out bnd) ν) : r' = r := by cases h <;> rfl

theorem programStep_callG_own {b : Bool} (h : ProgramStep P r j p (.callG r j b) ν) :
    p.input = none ∧ ν = PMF.pure { p with input := some b } := by
  cases h
  case callG => exact ⟨by assumption, rfl⟩
  case callGIdle => exact absurd rfl ‹_ ≠ j›

theorem programStep_callG_foreign {i : Fin P.n} {b : Bool} (hi : i ≠ j)
    (h : ProgramStep P r j p (.callG r i b) ν) : ν = PMF.pure p := by
  cases h
  case callG => exact absurd rfl hi
  case callGIdle => rfl

theorem programStep_callLoop {i : Fin P.n} {b : Bool}
    (h : ProgramStep P r j p (.callLoop r i b) ν) : ν = PMF.pure p := by
  cases h
  case callLoop => rfl
  case callLoopIdle => rfl

theorem programStep_firstGatherReturn_own {g : Fin P.n → Option Bool}
    {C : Gather.AcceptedPairs P.n Bool} (h : ProgramStep P r j p (.firstGatherReturn j g C) ν) :
    p.input ≠ none ∧ p.candidate = none ∧ ν = PMF.pure
    { p with candidate := some (candidate P g) } := by
  cases h
  case firstGatherReturn => exact ⟨by assumption, by assumption, rfl⟩
  case firstGatherReturnIdle => exact absurd rfl ‹_ ≠ j›

theorem programStep_firstGatherReturn_foreign {i : Fin P.n} {g : Fin P.n → Option Bool}
    {C : Gather.AcceptedPairs P.n Bool} (hi : i ≠ j)
    (h : ProgramStep P r j p (.firstGatherReturn i g C) ν) : ν = PMF.pure p := by
  cases h
  case firstGatherReturn => exact absurd rfl hi
  case firstGatherReturnIdle => rfl

theorem programStep_secondGatherCall_own {x : Option Bool}
    (h : ProgramStep P r j p (.secondGatherCall j x) ν) :
    p.candidate = some x ∧ p.secondGatherCalled = false ∧ ν = PMF.pure
    { p with secondGatherCalled := true } := by
  cases h
  case secondGatherCall => exact ⟨by assumption, by assumption, rfl⟩
  case secondGatherCallIdle => exact absurd rfl ‹_ ≠ j›

theorem programStep_secondGatherCall_foreign {i : Fin P.n} {x : Option Bool} (hi : i ≠ j)
    (h : ProgramStep P r j p (.secondGatherCall i x) ν) : ν = PMF.pure p := by
  cases h
  case secondGatherCall => exact absurd rfl hi
  case secondGatherCallIdle => rfl

theorem programStep_secondGatherReturn_own {g : Fin P.n → Option (Option Bool)}
    {C : Gather.AcceptedPairs P.n (Option Bool)}
    (h : ProgramStep P r j p (.secondGatherReturn j g C) ν) :
    p.secondGatherCalled = true ∧ p.output = none ∧ ν = PMF.pure
    { p with output := some (gradeOf P g) } := by
  cases h
  case secondGatherReturn => exact ⟨by assumption, by assumption, rfl⟩
  case secondGatherReturnIdle => exact absurd rfl ‹_ ≠ j›

theorem programStep_secondGatherReturn_foreign {i : Fin P.n} {g : Fin P.n → Option (Option Bool)}
    {C : Gather.AcceptedPairs P.n (Option Bool)} (hi : i ≠ j)
    (h : ProgramStep P r j p (.secondGatherReturn i g C) ν) : ν = PMF.pure p := by
  cases h
  case secondGatherReturn => exact absurd rfl hi
  case secondGatherReturnIdle => rfl

theorem programStep_retG_own {out : GBCAOutput} {bnd : Bool}
    (h : ProgramStep P r j p (.retG r j out bnd) ν) :
    p.output = some out ∧ p.returned = false ∧
      ν = PMF.pure { p with output := none, returned := true } := by
  cases h
  case retG => exact ⟨by assumption, by assumption, rfl⟩
  case retGIdle => exact absurd rfl ‹_ ≠ j›

theorem programStep_retG_foreign {i : Fin P.n} {out : GBCAOutput} {bnd : Bool} (hi : i ≠ j)
    (h : ProgramStep P r j p (.retG r i out bnd) ν) : ν = PMF.pure p := by
  cases h
  case retG => exact absurd rfl hi
  case retGIdle => rfl

end ProcInversion

/-! ### The rules of the round's network, by label class -/

section NetInversion

variable {P : Parameters} {r : ℕ} {w : Option Bool} {μ : PMF (Option Bool)}

theorem networkStep_callG {id : Fin P.n} {b : Bool} (h : NetworkStep P r w (.callG r id b) μ) :
    μ = PMF.pure w := by cases h; rfl

theorem networkStep_callLoop {id : Fin P.n} {b : Bool}
  (h : NetworkStep P r w (.callLoop r id b) μ) :
    μ = PMF.pure w := by cases h; rfl

theorem networkStep_firstGatherReturn {id : Fin P.n} {g : Fin P.n → Option Bool}
    {C : Gather.AcceptedPairs P.n Bool}
    (h : NetworkStep P r w (.firstGatherReturn id g C) μ) :
    μ = PMF.pure (some (w.getD (boundOfCore P C))) := by cases h; rfl

theorem networkStep_secondGatherCall {id : Fin P.n} {x : Option Bool} (h : NetworkStep P r w
  (.secondGatherCall id x) μ) :
    μ = PMF.pure w := by cases h; rfl

theorem networkStep_secondGatherReturn {id : Fin P.n} {g : Fin P.n → Option (Option Bool)}
    {C : Gather.AcceptedPairs P.n (Option Bool)} (h : NetworkStep P r w (.secondGatherReturn id g C)
      μ) :
    μ = PMF.pure w := by cases h; rfl

theorem networkStep_retG {id : Fin P.n} {out : GBCAOutput} {bnd : Bool}
    (h : NetworkStep P r w (.retG r id out bnd) μ) :
    bnd = w.getD (boundOfCore P ∅) ∧ μ = PMF.pure w := by cases h; exact ⟨rfl, rfl⟩

end NetInversion

end GBCA.ByAFW
end ABA
end PLTS
