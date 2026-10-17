/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sathiya / Claude
-/

import Leslie2Protocols.ABA.Gather.Specification
import Leslie2Protocols.ABA.GBCA.AFW.Counting
import Leslie2Protocols.ABA.Composition.Components
import Leslie2Protocols.Framework.SynchronisedProduct
import Leslie2Protocols.Framework.LoopsAndInstanceFamilies

/-!
# The components of the graded-agreement round

The pieces that run the round-`r` graded-agreement round: `n` graded-agreement programs beside the
round's network, and the pullbacks along which those programs and the two gather instances read the
round-internal alphabet.

A program holds one process's variables for the round: its input, its candidate, whether it has
called the second gather, its graded outcome and its return flag (`GBCA.ByAFW.ProcessVariables`).
Its guards read those variables and nothing else. `ProgramStep` is the step relation of process
`j`'s program and `NetworkStep` that of the round's network; `gbcaProgram` and `GBCANetwork` are
the two systems they carry, and `roundPrograms` is the round's programs: the `n` of them beside the
round's network, each read along `programLabelMap`.

## The round's network

The round's network exchanges no messages. Its state (`GBCA.ByAFW.NetworkState`) is the first
gather's core it has recorded and whether the round has returned, auxiliary state (D29) that no
program reads. The first gather's announcement `firstGatherCore C` records `C` where no core is
recorded, the round's return `retG` records the return, and `announceBound` announces the bit
`GBCA.boundOfCore P C` of the recorded core `C` on `boundG r _` once both are recorded. Inside the
round the first gather's announcement and the round's first return occur in either order, so the
announcement waits for both.

## The return-then-call step and the two-event return

The first gather's return and the second gather's call are two events, `firstGatherReturn`
and `secondGatherCall`, and so are the second gather's return and the round's graded
return, `secondGatherReturn` and `retG`. A program moves on each of the four: `firstGatherReturn`
records the candidate `GBCA.candidate` of the returned entries, `secondGatherCall` marks the call,
`secondGatherReturn` records the grade `GBCA.gradeOf`, `retG` marks the return. What carries
the round from one event to the next is the program's variables.

## Inputs and loops

A program takes each of its inputs at every state. The round's call `callG r j b` is recorded at a
program holding no input (`callG`) and leaves a program holding one where it stands (`callLoop`).
A gather's return to `j` is taken on `firstGatherReturn` or `secondGatherReturn` where the
program's guards admit it, and on `firstGatherReturnLoop` or `secondGatherReturnLoop` where they do
not. The first gather's announcement and the round's announcement are not a program's business
(`firstGatherCoreIdle`, `boundGIdle`).

## The alphabet

The round is over `ExtendedLabel n Empty`, as `GBCA.ByABDY.composition` is over
`ExtendedLabel n GBCA.ByABDY.Message`. The round exchanges its messages inside its two gather
instances, so it takes the empty type for the family alphabet's round message type: the round
multicast `gbcaSend` and the round delivery `gbcaDeliver` name no label here. A corrupted process's
call `byzantineCallG r k b` is a label of the interface, and `programLabelMap` reads it as the call
`callG r k b`.

`firstGatherLabelMap` sends the round's call and a corrupted process's call to
`Gather.Label.call`, the `firstGatherReturn` event to `Gather.Label.ret` and the `firstGatherCore`
event to `Gather.Label.core`: the first gather's announcement enters the round as
`firstGatherCore C`. The second gather is called on the round's own `secondGatherCall` event, which
`secondGatherLabelMap` sends to `Gather.Label.call`, and returns on `secondGatherReturn`. No round
label is sent to the second gather's announcement, so it never fires inside the round.

A family label outside the round's interface (the ABA API, the coin ports and the synchronisations
of the protocol's own networks) has the image `ProgramLabel.outside`, on which neither a program
nor the round's network moves. The round has no transition on such a label, and the family supplies
the idle. Corruption is the exception: it has no image at all, so the round's programs remain
unchanged on it while the two gather instances move.

The round-internal alphabet is `RoundLabel n = ExtendedLabel n Empty ⊕ RoundEvent n`, and
`roundEvents` collects the four events of `RoundEvent n`. They are hidden by the composition of
`ABA/GBCA/AFW/Composition.lean`, which is over `ExtendedLabel n Empty`.

## Corruption

`fail id` is a label of the interface. Neither a program nor the round's network fires on it: the
round's programs remain unchanged and the two gather instances corrupt together (D1). In the family
of rounds the label is the broadcast act (`GBCA.ByABDY.isFailLabel`), applied to every round at
once, and `GBCA.ByAFW.corruptAll` is the transform it applies: the two gather transforms, with the
programs and the round's network untouched.
-/

namespace PLTS
namespace ABA
namespace GBCA.ByAFW

open Implementation hiding NetworkEvent ExtendedLabel
open Composition

/-! ### The program's variables -/

/-- The variables of one graded-agreement program: what a process holds between
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

/-- The initial variables: nothing called, nothing determined, nothing
returned. -/
def ProcessVariables.initial (n : ℕ) : ProcessVariables n := ⟨none, none, false, none, false⟩

/-! ### The round-internal alphabet

The four events the family alphabet cannot name. They are untagged: the round
is the identity of the instance they belong to, and they are hidden before the
family sees the round at all. -/

/-- The round's own events: the first gather's return and its announcement of its core, the
second gather's call, and the second gather's return. -/
inductive RoundEvent (n : ℕ) : Type
  /-- The first gather returns the partial map `g` to `id`. -/
  | firstGatherReturn (id : Fin n) (g : Fin n → Option Bool)
  /-- The first gather announces its common core `C`. -/
  | firstGatherCore (C : Gather.AcceptedPairs n Bool)
  /-- Process `id` calls the second gather with `x`. -/
  | secondGatherCall (id : Fin n) (x : Option Bool)
  /-- The second gather returns the partial map `g` to `id`. -/
  | secondGatherReturn (id : Fin n) (g : Fin n → Option (Option Bool))

/-- The round-internal alphabet: the family alphabet plus the four events. Its
silent label is `Sum.inl (Sum.inl τ)`, so every `Sum.inr` label is observable
and hence hideable. -/
abbrev RoundLabel (n : ℕ) : Type := ExtendedLabel n Empty ⊕ RoundEvent n

/-- The event labels, hidden by the round. -/
def roundEvents (n : ℕ) : Set (RoundLabel n) := {l | ∃ e : RoundEvent n, l = Sum.inr e}

@[simp] theorem inl_notMem_roundEvents {n : ℕ} (l : ExtendedLabel n Empty) :
    Sum.inl l ∉ roundEvents n := by
  simp [roundEvents]

@[simp] theorem inr_mem_roundEvents {n : ℕ} (e : RoundEvent n) : Sum.inr e ∈ roundEvents n :=
  ⟨e, rfl⟩

@[simp] theorem roundLabel_tau (n : ℕ) :
    (Silent.τ : RoundLabel n) = Sum.inl (Sum.inl Label.tau) := rfl

/-! ### The program's alphabet -/

/-- The alphabet of one graded-agreement program: the round's call, its return and its
announcement, and the round's four events. -/
inductive ProgramLabel (n : ℕ) : Type
  /-- The silent label. -/
  | tau
  /-- The round's call at `id` with input `b`. -/
  | callG (r : ℕ) (id : Fin n) (b : Bool)
  /-- The first gather's return to `id`. -/
  | firstGatherReturn (id : Fin n) (g : Fin n → Option Bool)
  /-- The first gather's announcement of its core `C`. -/
  | firstGatherCore (C : Gather.AcceptedPairs n Bool)
  /-- Process `id`'s call of the second gather with `x`. -/
  | secondGatherCall (id : Fin n) (x : Option Bool)
  /-- The second gather's return to `id`. -/
  | secondGatherReturn (id : Fin n) (g : Fin n → Option (Option Bool))
  /-- The round's return to `id` of the graded outcome `out`. -/
  | retG (r : ℕ) (id : Fin n) (out : GBCAOutput)
  /-- The announcement of the round's bound bit `b`. -/
  | boundG (r : ℕ) (b : Bool)
  /-- The image of every family label outside the round's interface. No transition
  fires on it. -/
  | outside

instance {n : ℕ} : Silent (ProgramLabel n) := ⟨ProgramLabel.tau⟩

@[simp] theorem programLabel_tau (n : ℕ) : (Silent.τ : ProgramLabel n) = ProgramLabel.tau := rfl

/-! ### The pullbacks

A program and the round's network are read along `programLabelMap`, the first gather along
`firstGatherLabelMap`, the second along `secondGatherLabelMap`. A label with no image at a component
leaves that component unchanged. -/

/-- The projection of the round-internal alphabet onto a program's alphabet. It reads a corrupted
process's call as a call. Corruption has no image and leaves a program unchanged; every other
family label outside the round's interface has the image `ProgramLabel.outside`, on which no
transition fires. -/
def programLabelMap (n : ℕ) : RoundLabel n → Option (ProgramLabel n)
  | Sum.inl (Sum.inl .tau) => some .tau
  | Sum.inl (Sum.inl (.callG r id b)) => some (.callG r id b)
  | Sum.inl (Sum.inl (.retG r id out)) => some (.retG r id out)
  | Sum.inl (Sum.inl (.boundG r b)) => some (.boundG r b)
  | Sum.inl (Sum.inr (.byzantineCallG r k b)) => some (.callG r k b)
  | Sum.inr (.firstGatherReturn id g) => some (.firstGatherReturn id g)
  | Sum.inr (.firstGatherCore C) => some (.firstGatherCore C)
  | Sum.inr (.secondGatherCall id x) => some (.secondGatherCall id x)
  | Sum.inr (.secondGatherReturn id g) => some (.secondGatherReturn id g)
  | Sum.inl (Sum.inl (.fail _)) => none
  | _ => some .outside

/-- The projection of the round-internal alphabet onto the first gather's alphabet. The round's
call and a corrupted process's call are the gather's call, the `firstGatherReturn` event is the
gather's return, and the `firstGatherCore` event is the gather's announcement of its core. -/
def firstGatherLabelMap (n : ℕ) : RoundLabel n → Option (Gather.Label n Bool)
  | Sum.inl (Sum.inl .tau) => some .tau
  | Sum.inl (Sum.inl (.callG _ id b)) => some (.call id b)
  | Sum.inl (Sum.inl (.fail id)) => some (.fail id)
  | Sum.inl (Sum.inr (.byzantineCallG _ k b)) => some (.call k b)
  | Sum.inr (.firstGatherReturn id g) => some (.ret id g)
  | Sum.inr (.firstGatherCore C) => some (.core C)
  | _ => none

/-- The projection of the round-internal alphabet onto the second gather's alphabet. The
`secondGatherCall` event is the gather's call and the `secondGatherReturn` event its return. No
label is sent to the gather's announcement of its core. -/
def secondGatherLabelMap (n : ℕ) : RoundLabel n → Option (Gather.Label n (Option Bool))
  | Sum.inl (Sum.inl .tau) => some .tau
  | Sum.inl (Sum.inl (.fail id)) => some (.fail id)
  | Sum.inr (.secondGatherCall id x) => some (.call id x)
  | Sum.inr (.secondGatherReturn id g) => some (.ret id g)
  | _ => none

/-- The silent label projects to the silent label. -/
@[simp] theorem programLabelMap_tau (n : ℕ) :
    programLabelMap n (Silent.τ : RoundLabel n) = some (Silent.τ : ProgramLabel n) := rfl

/-- The silent label projects to the silent label. -/
@[simp] theorem firstGatherLabelMap_tau (n : ℕ) :
    firstGatherLabelMap n (Silent.τ : RoundLabel n) = some (Silent.τ : Gather.Label n Bool) := rfl

/-- The silent label projects to the silent label. -/
@[simp] theorem secondGatherLabelMap_tau (n : ℕ) :
    secondGatherLabelMap n (Silent.τ : RoundLabel n) =
      some (Silent.τ : Gather.Label n (Option Bool)) := rfl

/-- Only the silent label reaches a program's silent label. -/
theorem programLabelMap_eq_tau {n : ℕ} {l : RoundLabel n}
    (h : programLabelMap n l = some ProgramLabel.tau) : l = Sum.inl (Sum.inl Label.tau) := by
  rcases l with (l₀ | e) | e
  · cases l₀ <;> simp_all [programLabelMap]
  · cases e <;> simp_all [programLabelMap]
  · cases e <;> simp_all [programLabelMap]

/-- Only the silent label reaches the first gather's silent label. -/
theorem firstGatherLabelMap_eq_tau {n : ℕ} {l : RoundLabel n}
    (h : firstGatherLabelMap n l = some (Silent.τ : Gather.Label n Bool)) : l = Silent.τ := by
  rcases l with (l₀ | e) | e
  · cases l₀ <;> simp_all [firstGatherLabelMap]
  · cases e <;> simp_all [firstGatherLabelMap]
  · cases e <;> simp_all [firstGatherLabelMap]

/-- Only the silent label reaches the second gather's silent label. -/
theorem secondGatherLabelMap_eq_tau {n : ℕ} {l : RoundLabel n}
    (h : secondGatherLabelMap n l = some (Silent.τ : Gather.Label n (Option Bool))) :
    l = Silent.τ := by
  rcases l with (l₀ | e) | e
  · cases l₀ <;> simp_all [secondGatherLabelMap]
  · cases e <;> simp_all [secondGatherLabelMap]
  · cases e <;> simp_all [secondGatherLabelMap]

/-! ### The pullbacks, label by label -/

section Pullbacks
variable {n : ℕ} (r : ℕ) (id k i j : Fin n) (b : Bool) (x : Option Bool) (out : GBCAOutput)
  (g : Fin n → Option Bool) (h : Fin n → Option (Option Bool)) (C : Gather.AcceptedPairs n Bool)

@[simp] theorem programLabelMap_callABA :
    programLabelMap n (Sum.inl (Sum.inl (.callABA id b))) = some .outside := rfl
@[simp] theorem programLabelMap_retABA :
    programLabelMap n (Sum.inl (Sum.inl (.retABA id b))) = some .outside := rfl
@[simp] theorem programLabelMap_callG :
    programLabelMap n (Sum.inl (Sum.inl (.callG r id b))) = some (.callG r id b) := rfl
@[simp] theorem programLabelMap_retG :
    programLabelMap n (Sum.inl (Sum.inl (.retG r id out))) = some (.retG r id out) := rfl
@[simp] theorem programLabelMap_boundG :
    programLabelMap n (Sum.inl (Sum.inl (.boundG r b))) = some (.boundG r b) := rfl
@[simp] theorem programLabelMap_callW :
    programLabelMap n (Sum.inl (Sum.inl (.callW r id))) = some .outside := rfl
@[simp] theorem programLabelMap_retW :
    programLabelMap n (Sum.inl (Sum.inl (.retW r id b))) = some .outside := rfl
@[simp] theorem programLabelMap_fail :
    programLabelMap n (Sum.inl (Sum.inl (.fail id))) = none := rfl
@[simp] theorem programLabelMap_decidedSend :
    programLabelMap n (Sum.inl (Sum.inr (.decidedSend j b))) = some .outside := rfl
@[simp] theorem programLabelMap_decidedRelay :
    programLabelMap n (Sum.inl (Sum.inr (.decidedRelay j b))) = some .outside := rfl
@[simp] theorem programLabelMap_decidedDeliver :
    programLabelMap n (Sum.inl (Sum.inr (.decidedDeliver i j b))) = some .outside := rfl
@[simp] theorem programLabelMap_byzantineCallG :
    programLabelMap n (Sum.inl (Sum.inr (.byzantineCallG r k b))) = some (.callG r k b) := rfl
@[simp] theorem programLabelMap_byzantineCallW :
    programLabelMap n (Sum.inl (Sum.inr (.byzantineCallW r k))) = some .outside := rfl
@[simp] theorem programLabelMap_firstGatherReturn :
    programLabelMap n (Sum.inr (.firstGatherReturn id g)) = some (.firstGatherReturn id g) := rfl
@[simp] theorem programLabelMap_firstGatherCore :
    programLabelMap n (Sum.inr (.firstGatherCore C)) = some (.firstGatherCore C) := rfl
@[simp] theorem programLabelMap_secondGatherCall :
    programLabelMap n (Sum.inr (.secondGatherCall id x)) = some (.secondGatherCall id x) := rfl
@[simp] theorem programLabelMap_secondGatherReturn :
    programLabelMap n (Sum.inr (.secondGatherReturn id h)) = some (.secondGatherReturn id h) := rfl

@[simp] theorem firstGatherLabelMap_callABA :
    firstGatherLabelMap n (Sum.inl (Sum.inl (.callABA id b))) = none := rfl
@[simp] theorem firstGatherLabelMap_retABA :
    firstGatherLabelMap n (Sum.inl (Sum.inl (.retABA id b))) = none := rfl
@[simp] theorem firstGatherLabelMap_callG :
    firstGatherLabelMap n (Sum.inl (Sum.inl (.callG r id b))) = some (.call id b) := rfl
@[simp] theorem firstGatherLabelMap_retG :
    firstGatherLabelMap n (Sum.inl (Sum.inl (.retG r id out))) = none := rfl
@[simp] theorem firstGatherLabelMap_boundG :
    firstGatherLabelMap n (Sum.inl (Sum.inl (.boundG r b))) = none := rfl
@[simp] theorem firstGatherLabelMap_callW :
    firstGatherLabelMap n (Sum.inl (Sum.inl (.callW r id))) = none := rfl
@[simp] theorem firstGatherLabelMap_retW :
    firstGatherLabelMap n (Sum.inl (Sum.inl (.retW r id b))) = none := rfl
@[simp] theorem firstGatherLabelMap_fail :
    firstGatherLabelMap n (Sum.inl (Sum.inl (.fail id))) = some (.fail id) := rfl
@[simp] theorem firstGatherLabelMap_decidedSend :
    firstGatherLabelMap n (Sum.inl (Sum.inr (.decidedSend j b))) = none := rfl
@[simp] theorem firstGatherLabelMap_decidedRelay :
    firstGatherLabelMap n (Sum.inl (Sum.inr (.decidedRelay j b))) = none := rfl
@[simp] theorem firstGatherLabelMap_decidedDeliver :
    firstGatherLabelMap n (Sum.inl (Sum.inr (.decidedDeliver i j b))) = none := rfl
@[simp] theorem firstGatherLabelMap_byzantineCallG :
    firstGatherLabelMap n (Sum.inl (Sum.inr (.byzantineCallG r k b))) = some (.call k b) := rfl
@[simp] theorem firstGatherLabelMap_byzantineCallW :
    firstGatherLabelMap n (Sum.inl (Sum.inr (.byzantineCallW r k))) = none := rfl
@[simp] theorem firstGatherLabelMap_firstGatherReturn :
    firstGatherLabelMap n (Sum.inr (.firstGatherReturn id g)) = some (.ret id g) := rfl
@[simp] theorem firstGatherLabelMap_firstGatherCore :
    firstGatherLabelMap n (Sum.inr (.firstGatherCore C)) = some (.core C) := rfl
@[simp] theorem firstGatherLabelMap_secondGatherCall :
    firstGatherLabelMap n (Sum.inr (.secondGatherCall id x)) = none := rfl
@[simp] theorem firstGatherLabelMap_secondGatherReturn :
    firstGatherLabelMap n (Sum.inr (.secondGatherReturn id h)) = none := rfl

@[simp] theorem secondGatherLabelMap_callABA :
    secondGatherLabelMap n (Sum.inl (Sum.inl (.callABA id b))) = none := rfl
@[simp] theorem secondGatherLabelMap_retABA :
    secondGatherLabelMap n (Sum.inl (Sum.inl (.retABA id b))) = none := rfl
@[simp] theorem secondGatherLabelMap_callG :
    secondGatherLabelMap n (Sum.inl (Sum.inl (.callG r id b))) = none := rfl
@[simp] theorem secondGatherLabelMap_retG :
    secondGatherLabelMap n (Sum.inl (Sum.inl (.retG r id out))) = none := rfl
@[simp] theorem secondGatherLabelMap_boundG :
    secondGatherLabelMap n (Sum.inl (Sum.inl (.boundG r b))) = none := rfl
@[simp] theorem secondGatherLabelMap_callW :
    secondGatherLabelMap n (Sum.inl (Sum.inl (.callW r id))) = none := rfl
@[simp] theorem secondGatherLabelMap_retW :
    secondGatherLabelMap n (Sum.inl (Sum.inl (.retW r id b))) = none := rfl
@[simp] theorem secondGatherLabelMap_fail :
    secondGatherLabelMap n (Sum.inl (Sum.inl (.fail id))) = some (.fail id) := rfl
@[simp] theorem secondGatherLabelMap_decidedSend :
    secondGatherLabelMap n (Sum.inl (Sum.inr (.decidedSend j b))) = none := rfl
@[simp] theorem secondGatherLabelMap_decidedRelay :
    secondGatherLabelMap n (Sum.inl (Sum.inr (.decidedRelay j b))) = none := rfl
@[simp] theorem secondGatherLabelMap_decidedDeliver :
    secondGatherLabelMap n (Sum.inl (Sum.inr (.decidedDeliver i j b))) = none := rfl
@[simp] theorem secondGatherLabelMap_byzantineCallG :
    secondGatherLabelMap n (Sum.inl (Sum.inr (.byzantineCallG r k b))) = none := rfl
@[simp] theorem secondGatherLabelMap_byzantineCallW :
    secondGatherLabelMap n (Sum.inl (Sum.inr (.byzantineCallW r k))) = none := rfl
@[simp] theorem secondGatherLabelMap_firstGatherReturn :
    secondGatherLabelMap n (Sum.inr (.firstGatherReturn id g)) = none := rfl
@[simp] theorem secondGatherLabelMap_firstGatherCore :
    secondGatherLabelMap n (Sum.inr (.firstGatherCore C)) = none := rfl
@[simp] theorem secondGatherLabelMap_secondGatherCall :
    secondGatherLabelMap n (Sum.inr (.secondGatherCall id x)) = some (.call id x) := rfl
@[simp] theorem secondGatherLabelMap_secondGatherReturn :
    secondGatherLabelMap n (Sum.inr (.secondGatherReturn id h)) = some (.ret id h) := rfl

end Pullbacks

/-! ### The graded-agreement program

Process `j`'s program in this round. Every guard reads its own variables. The
round's moves are one transition each: the call records the input, the first
gather's return records the candidate, the second gather's call marks itself,
the second gather's return records the grade, and the round's return marks the
variables returned. A call or a gather's return that the guards refuse is taken
on a loop. No transition fires on the silent label. -/

/-- The step relation of the graded-agreement program of process `j` in round
`r`. All transitions are Dirac. -/
inductive ProgramStep (P : Parameters) (r : ℕ) (j : Fin P.n) :
    ProcessVariables P.n → ProgramLabel P.n → PMF (ProcessVariables P.n) → Prop
  /-- The call arrives at a program holding no input: record the input. -/
  | callG (p : ProcessVariables P.n) (b : Bool) (h : p.input = none) :
      ProgramStep P r j p (.callG r j b) (PMF.pure { p with input := some b })
  /-- The call arrives at a program holding an input: the variables do not move. -/
  | callLoop (p : ProcessVariables P.n) (b : Bool) (hin : p.input ≠ none) :
      ProgramStep P r j p (.callG r j b) (PMF.pure p)
  /-- A call addressed elsewhere: not `j`'s business. -/
  | callGIdle (p : ProcessVariables P.n) (i : Fin P.n) (b : Bool) (hi : i ≠ j) :
      ProgramStep P r j p (.callG r i b) (PMF.pure p)
  /-- The first gather returns here to a called program holding no candidate: record the
  candidate of its entries. -/
  | firstGatherReturn (p : ProcessVariables P.n) (g : Fin P.n → Option Bool)
      (hin : p.input ≠ none) (hc : p.candidate = none) :
      ProgramStep P r j p (.firstGatherReturn j g)
        (PMF.pure { p with candidate := some (candidate P g) })
  /-- The first gather returns here to a program that has not called or holds a candidate: the
  variables do not move. -/
  | firstGatherReturnLoop (p : ProcessVariables P.n) (g : Fin P.n → Option Bool)
      (h : ¬ (p.input ≠ none ∧ p.candidate = none)) :
      ProgramStep P r j p (.firstGatherReturn j g) (PMF.pure p)
  /-- The first gather's return to another process: not `j`'s business. -/
  | firstGatherReturnIdle (p : ProcessVariables P.n) (i : Fin P.n) (g : Fin P.n → Option Bool)
      (hi : i ≠ j) :
      ProgramStep P r j p (.firstGatherReturn i g) (PMF.pure p)
  /-- The first gather's announcement of its core: not `j`'s business. -/
  | firstGatherCoreIdle (p : ProcessVariables P.n) (C : Gather.AcceptedPairs P.n Bool) :
      ProgramStep P r j p (.firstGatherCore C) (PMF.pure p)
  /-- The second gather is called here with the recorded candidate. -/
  | secondGatherCall (p : ProcessVariables P.n) (x : Option Bool) (hc : p.candidate = some x)
      (h2 : p.secondGatherCalled = false) :
      ProgramStep P r j p (.secondGatherCall j x) (PMF.pure { p with secondGatherCalled := true })
  /-- Another process's call of the second gather: not `j`'s business. -/
  | secondGatherCallIdle (p : ProcessVariables P.n) (i : Fin P.n) (x : Option Bool) (hi : i ≠ j) :
      ProgramStep P r j p (.secondGatherCall i x) (PMF.pure p)
  /-- The second gather returns here to a program that has called it and holds no grade: record
  the grade of its entries. -/
  | secondGatherReturn (p : ProcessVariables P.n) (g : Fin P.n → Option (Option Bool))
      (h2 : p.secondGatherCalled = true) (ho : p.output = none) :
      ProgramStep P r j p (.secondGatherReturn j g)
        (PMF.pure { p with output := some (gradeOf P g) })
  /-- The second gather returns here to a program that has not called it or holds a grade: the
  variables do not move. -/
  | secondGatherReturnLoop (p : ProcessVariables P.n) (g : Fin P.n → Option (Option Bool))
      (h : ¬ (p.secondGatherCalled = true ∧ p.output = none)) :
      ProgramStep P r j p (.secondGatherReturn j g) (PMF.pure p)
  /-- The second gather's return to another process: not `j`'s business. -/
  | secondGatherReturnIdle (p : ProcessVariables P.n) (i : Fin P.n)
      (g : Fin P.n → Option (Option Bool)) (hi : i ≠ j) :
      ProgramStep P r j p (.secondGatherReturn i g) (PMF.pure p)
  /-- The round returns the recorded grade, and the variables drop it. -/
  | retG (p : ProcessVariables P.n) (out : GBCAOutput) (ho : p.output = some out)
      (hr : p.returned = false) :
      ProgramStep P r j p (.retG r j out) (PMF.pure { p with output := none, returned := true })
  /-- A return to another process: not `j`'s business. -/
  | retGIdle (p : ProcessVariables P.n) (i : Fin P.n) (out : GBCAOutput) (hi : i ≠ j) :
      ProgramStep P r j p (.retG r i out) (PMF.pure p)
  /-- The announcement of the round's bound bit: not `j`'s business. -/
  | boundGIdle (p : ProcessVariables P.n) (b : Bool) :
      ProgramStep P r j p (.boundG r b) (PMF.pure p)

/-! ### The round's network

The network of the round's programs. It exchanges no message. It records the first gather's core
from the gather's announcement and whether the round has returned, and announces the round's bound
bit once both are recorded; no program reads its state. No transition fires on the silent label. -/

/-- The state of the round's network: the first gather's core it has recorded and whether the
round has returned (D29). -/
structure NetworkState (n : ℕ) : Type where
  /-- The first gather's core, recorded from the first gather's announcement. -/
  firstGatherCore : Option (Gather.AcceptedPairs n Bool)
  /-- Whether the round has returned at some process. -/
  returned : Bool

/-- The initial state of the round's network: no core recorded, no return. -/
def NetworkState.initial (n : ℕ) : NetworkState n := ⟨none, false⟩

/-- The step relation of the round's network. All transitions are Dirac. -/
inductive NetworkStep (P : Parameters) (r : ℕ) :
    NetworkState P.n → ProgramLabel P.n → PMF (NetworkState P.n) → Prop
  /-- A call moves nothing. -/
  | callG (w : NetworkState P.n) (id : Fin P.n) (b : Bool) :
      NetworkStep P r w (.callG r id b) (PMF.pure w)
  /-- The first gather's return moves nothing. -/
  | firstGatherReturn (w : NetworkState P.n) (id : Fin P.n) (g : Fin P.n → Option Bool) :
      NetworkStep P r w (.firstGatherReturn id g) (PMF.pure w)
  /-- The first gather's announcement records the announced core where no core is recorded. -/
  | firstGatherCore (w : NetworkState P.n) (C : Gather.AcceptedPairs P.n Bool) :
      NetworkStep P r w (.firstGatherCore C)
        (PMF.pure { w with firstGatherCore := some (w.firstGatherCore.getD C) })
  /-- The second gather's call moves nothing. -/
  | secondGatherCall (w : NetworkState P.n) (id : Fin P.n) (x : Option Bool) :
      NetworkStep P r w (.secondGatherCall id x) (PMF.pure w)
  /-- The second gather's return moves nothing. -/
  | secondGatherReturn (w : NetworkState P.n) (id : Fin P.n)
      (g : Fin P.n → Option (Option Bool)) :
      NetworkStep P r w (.secondGatherReturn id g) (PMF.pure w)
  /-- The round's return records that the round has returned. -/
  | retG (w : NetworkState P.n) (id : Fin P.n) (out : GBCAOutput) :
      NetworkStep P r w (.retG r id out) (PMF.pure { w with returned := true })
  /-- The announcement of the round's bound bit, the bit `GBCA.boundOfCore P C` of the recorded
  core `C`, once the round has returned: a Dirac self-loop, which may repeat (D29). -/
  | announceBound (w : NetworkState P.n) (C : Gather.AcceptedPairs P.n Bool)
      (hC : w.firstGatherCore = some C) (hr : w.returned = true) :
      NetworkStep P r w (.boundG r (boundOfCore P C)) (PMF.pure w)

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
noncomputable def GBCANetwork (P : Parameters) (r : ℕ) :
    System (NetworkState P.n) (ProgramLabel P.n) where
  init := NetworkState.initial P.n
  step := NetworkStep P r

@[simp] theorem GBCANetwork_init (P : Parameters) (r : ℕ) :
    (GBCANetwork P r).init = NetworkState.initial P.n := rfl

@[simp] theorem GBCANetwork_step (P : Parameters) (r : ℕ) (w : NetworkState P.n)
    (l : ProgramLabel P.n) (μ : PMF (NetworkState P.n)) :
    (GBCANetwork P r).step w l μ ↔ NetworkStep P r w l μ := Iff.rfl

/-- **The round's programs**: the `n` programs beside the round's network, each read along
`programLabelMap`. -/
noncomputable def roundPrograms (P : Parameters) (r : ℕ) :
    System ((∀ _ : Fin P.n, ProcessVariables P.n) × NetworkState P.n) (RoundLabel P.n) :=
  (System.synchronisedProduct (fun j => (gbcaProgram P r j).mapIdle (programLabelMap P.n))).parallel
    ((GBCANetwork P r).mapIdle (programLabelMap P.n))

@[simp] theorem roundPrograms_init (P : Parameters) (r : ℕ) :
    (roundPrograms P r).init =
      ((fun _ => ProcessVariables.initial P.n), NetworkState.initial P.n) := rfl

end GBCA.ByAFW
end ABA
end PLTS
