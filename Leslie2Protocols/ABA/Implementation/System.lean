/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sathiya / Claude
-/

import Leslie2Protocols.ABA.Implementation.Alphabet
import Leslie2Protocols.ABA.Vocabulary.RoundLoop
import Leslie2Protocols.Framework.SynchronisedProduct
import Mathlib.Data.Finmap

/-!
# The implementation of a protocol

The implementation presents the protocol as it runs: `n` programs, one per process, beside one
network holding the message sets, the DECIDED sets, the corrupted set with its budget and the
rounds a correct process has started, beside the common coin. A program reads its own
variables, its own received sets and its own replacement flag, and nothing else about corruption:
not the corrupted set, not the budget, not another process's status (D23).

Everything of that shape which does not depend on the graded-agreement implementation is written
here once. The parameters are the round message type `M`, the type `E` of the round's own calls and
returns, the per-process per-round variables `S`, and the implementation's own transitions, given
as a relation `roundStep` embedded in one constructor of the program's step relation. An
implementation supplies the four and inherits the round loop, the DECIDED sets, the coin's call
and return, corruption, the network and the composition pipeline.

## The division of transitions

A program's transition is the implementation's business exactly when its label is one of
`roundOwn j`: the graded-agreement call and return at `j`, `j`'s own round multicast, a round
delivery addressed to `j`, and `j`'s own round-internal call or return. Every other label — the
ABA interface, the coin's call and return, the announcement `boundG`, the DECIDED send, the DECIDED
relay and its delivery, a corrupted process's two sub-protocol calls, corruption, and the same
label classes at another process — has its transition here. `IsRoundStep` states that division: a
program's transition on a label outside `roundOwn j` is one of the transitions here, whichever
implementation is being read.

Each label is output by one component, and every other component takes it as an input on a
transition enabled at every state (`Implementation/InputEnabledness.lean`). A guard on an output
decides whether the component that outputs it acts, and no component guards a label another
component outputs. The program of `j` outputs the labels of `actsAt j`, its DECIDED relay and its
ABA return. The network outputs the deliveries, `fail`, the announcement `boundG`, and a corrupted
process's graded-agreement call `byzantineCallG` and coin call `byzantineCallW`. The common coin
outputs `retW`.

## The network

The adversary's transitions are independent of the implementation except in one place, the
ghost. A graded-agreement call, correct or Byzantine, sends nothing: every round message enters
the sent sets by a round multicast or by a Byzantine injection. The network takes each of its
inputs on one unguarded transition. It outputs a corrupted process's two sub-protocol calls under
`k ∈ F` and at a round of `startedRounds`, the rounds at which a process outside `F` has called
graded agreement, which the network writes on that call; the injection `byzantineGBCA` carries the
same two guards (D11, D37). No transition of a correct process reads `startedRounds`.

The sent sets and the ghosts are finite maps over the rounds with an entry, read through the
accessors `sent r j` and `ghost r`, which give `∅` and `default` at a round with no entry.

## The network's ghost

The adversary holds one further component: for each round `r`, a ghost `ghost r` of a type `G` the
implementation fixes. It belongs to the network and to no program (D30). No program's transition
reads it and no program's variables hold it.

Two parameters carry it. `ghostStep` writes it: on every transition, the ghost of the round the
label names is replaced by `ghostStep` of that label, the network's state and the ghost standing
there, and the ghosts of the other rounds are left where they stand; a label naming no round leaves
the whole ghost alone. `ghostBound` reads it: the bit the ghost of a round holds, if any. The one
guard on the ghost is that of the announcement `announceBound`, a Dirac transition on `boundG r b`
enabled exactly when `ghostBound (ghost r) = some b`, which may repeat (D29).

The content is the implementation's own. ABDY22's implementation and the gather-based one hold
different ghosts and write them at different transitions, so `G`, `ghostStep` and `ghostBound` are
parameters here, as `M`, `E`, `S` and `roundStep` are. Each of the two writes the round's bit at
the round's first return and leaves it where it stands from then on.
-/

namespace PLTS
namespace ABA
namespace Implementation

/-! ### The state of one process -/

/-- The round variables of one process: its variables in every round the process has touched, and
whether it has terminated (D22). -/
structure RoundVariablesMap (S : Type) : Type where
  /-- The finite map of round variables; a round off the map has the initial variables. -/
  roundVariablesMap : Finmap (fun _ : ℕ => S)
  /-- Whether this process has terminated (ABDY22 §3, Termination).
  `terminated` is not `returned`: the round-loop variables' `returned` say the
  process has fired `retABA`; `terminated` says it has stopped participating. -/
  terminated : Bool

namespace RoundVariablesMap

variable {n : ℕ} {M S : Type}

/-- The initial round variables: no round touched, not terminated. -/
def initial (S : Type) : RoundVariablesMap S where
  roundVariablesMap := ∅
  terminated := false

/-- Retain `p` as the variables of round `r`. -/
def setRoundVariables (q : RoundVariablesMap S) (r : ℕ) (p : S) : RoundVariablesMap S :=
  { q with roundVariablesMap := q.roundVariablesMap.insert r p }

end RoundVariablesMap

/-- What the implementation's round variables supply: the variables of a round the process has not
touched, and the filing of a delivered message under its sender. -/
class IsRoundVariables (n : outParam ℕ) (M : outParam Type) (S : Type) where
  /-- The variables of a round the process has not touched. -/
  initial : S
  /-- File a message under its sender. -/
  deliverTo : S → Fin n → M → S

namespace RoundVariablesMap

variable {n : ℕ} {M S : Type} [IsRoundVariables n M S]

/-- The variables of round `r`: the retained variables if the process has touched round `r`, the
initial variables otherwise. -/
def roundVariables (q : RoundVariablesMap S) (r : ℕ) : S :=
  (q.roundVariablesMap.lookup r).getD IsRoundVariables.initial

/-- File `m` under sender `k` in the variables of round `r`. -/
def deliverTo (q : RoundVariablesMap S) (r : ℕ) (k : Fin n) (m : M) : RoundVariablesMap S :=
  q.setRoundVariables r (IsRoundVariables.deliverTo (q.roundVariables r) k m)

@[simp] theorem initial_roundVariables (r : ℕ) :
    (initial S).roundVariables r = (IsRoundVariables.initial : S) := by
  simp [roundVariables, initial]

@[simp] theorem initial_terminated (S : Type) : (initial S).terminated = false := rfl

@[simp] theorem roundVariables_setRoundVariables_self (q : RoundVariablesMap S) (r : ℕ) (p : S) :
    (q.setRoundVariables r p).roundVariables r = p := by
  simp [roundVariables, setRoundVariables, Finmap.lookup_insert]

@[simp] theorem roundVariables_setRoundVariables_ne (q : RoundVariablesMap S) (r : ℕ) (p : S)
    {r' : ℕ} (h : r' ≠ r) : (q.setRoundVariables r p).roundVariables r' = q.roundVariables r' := by
  simp [roundVariables, setRoundVariables, Finmap.lookup_insert_of_ne _ h]

@[simp] theorem terminated_setRoundVariables (q : RoundVariablesMap S) (r : ℕ) (p : S) :
    (q.setRoundVariables r p).terminated = q.terminated := rfl

@[simp] theorem terminated_deliverTo (q : RoundVariablesMap S) (r : ℕ) (k : Fin n)
    (m : M) : (q.deliverTo r k m).terminated = q.terminated := rfl

end RoundVariablesMap

/-- The state of one process: its round-loop variables and its round variables (D22). -/
abbrev ProcessVariables (n : ℕ) (S : Type) : Type := RoundLoopVariables n × RoundVariablesMap S

/-! ### The round a label names -/

/-- The round a label of the extended alphabet names, if any. A shared label names a round when it
is a graded-agreement call, return or announcement, which is `Label.gbcaRound`; a network event
names the round its constructor carries. The ABA interface, the coin's labels, corruption, the
DECIDED send, the DECIDED relay and the DECIDED delivery name no round. This is the round whose
ghost a transition writes. -/
def roundOf {n : ℕ} {M E : Type} : ExtendedLabel n M E → Option ℕ
  | Sum.inl l => l.gbcaRound
  | Sum.inr (.gbcaSend r _ _) => some r
  | Sum.inr (.gbcaDeliver r _ _ _) => some r
  | Sum.inr (.decidedSend _ _) => none
  | Sum.inr (.decidedRelay _ _) => none
  | Sum.inr (.decidedDeliver _ _ _) => none
  | Sum.inr (.gbcaRoundEvent r _ _) => some r
  | Sum.inr (.byzantineCallG r _ _) => some r
  | Sum.inr (.byzantineCallW r _) => some r

@[simp] theorem roundOf_boundG {n : ℕ} {M E : Type} (r : ℕ) (b : Bool) :
    roundOf (M := M) (E := E) (Sum.inl (Label.boundG (n := n) r b)) = some r := rfl

/-! ### The network's state -/

/-- The state of the network: the round-tagged message sets, the DECIDED sets, the corrupted set
with its budget, the ghost of every round, and the rounds a correct process has started.
The message sets and the ghosts are finite maps over the rounds with an entry. -/
structure NetworkState (n : ℕ) (M : Type) (G : Type) : Type where
  /-- The messages each process has multicast in round `r`, at every round with an entry (D5). -/
  sentMap : Finmap (fun _ : ℕ => Fin n → Finset M)
  /-- `decidedSent j` — the DECIDED payloads process `j` has multicast (D12′). -/
  decidedSent : Fin n → Finset Bool
  /-- The corrupted set. -/
  F : Finset (Fin n)
  /-- The ghost the network holds for round `r`, at every round with an entry. No program
  reads it. -/
  ghostMap : Finmap (fun _ : ℕ => G)
  /-- The rounds at which a process outside the corrupted set has called graded agreement, in
  ABDY22's words the rounds a correct process has started (D37). The round instances of a composed
  system exist exactly at these rounds, so an injection or a Byzantine call of the implementation at
  a round of this set is matched by that round's own transitions. -/
  startedRounds : Finset ℕ

namespace NetworkState

variable {n : ℕ} {M E G : Type}

/-- `sent r j` — the round-`r` messages process `j` has multicast, `∅` at a round with no
entry (D5). -/
def sent (s : NetworkState n M G) (r : ℕ) : Fin n → Finset M :=
  (s.sentMap.lookup r).getD fun _ => ∅

/-- `ghost r` — the ghost the network holds for round `r`, `default` at a round with no entry.
No program reads it. -/
def ghost [Inhabited G] (s : NetworkState n M G) (r : ℕ) : G :=
  (s.ghostMap.lookup r).getD default

/-- The initial network: nothing multicast, nobody corrupted, no ghost written, and no round
started. -/
def initial (n : ℕ) (M G : Type) : NetworkState n M G where
  sentMap := ∅
  decidedSent := fun _ => ∅
  F := ∅
  ghostMap := ∅
  startedRounds := ∅

@[simp] theorem initial_sent (r : ℕ) (j : Fin n) : (initial n M G).sent r j = ∅ := rfl

@[simp] theorem initial_decidedSent (j : Fin n) : (initial n M G).decidedSent j = ∅ := rfl

@[simp] theorem initial_F : (initial n M G).F = ∅ := rfl

@[simp] theorem initial_ghost [Inhabited G] (r : ℕ) : (initial n M G).ghost r = default := rfl

@[simp] theorem initial_startedRounds : (initial n M G).startedRounds = ∅ := rfl

/-- Sent `m` under sender `j` in round `r` (D5). -/
def recordGBCASend [DecidableEq M] (s : NetworkState n M G) (r : ℕ) (j : Fin n) (m : M) :
    NetworkState n M G :=
  { s with sentMap := s.sentMap.insert r (Function.update (s.sent r) j (insert m (s.sent r j))) }

/-- Sent `⟨DECIDED, b⟩` under sender `j` (D12′). -/
def recordDecided (s : NetworkState n M G) (j : Fin n) (b : Bool) : NetworkState n M G :=
  { s with decidedSent := Function.update s.decidedSent j (insert b (s.decidedSent j)) }

/-- Corruption (deviation D1): total, Dirac, budget-guarded. -/
def corrupt (P : Parameters) (id : Fin P.n) (s : NetworkState P.n M G) : NetworkState P.n M G :=
  if id ∉ s.F ∧ s.F.card < P.f then { s with F := insert id s.F } else s

/-- The graded-agreement call of `id` at round `r`: where `id` lies outside the corrupted set,
`r` enters the started rounds (D37). -/
def recordStartedRound (s : NetworkState n M G) (r : ℕ) (id : Fin n) : NetworkState n M G :=
  if id ∉ s.F then { s with startedRounds := insert r s.startedRounds } else s

open Classical in
/-- The ghost write of a transition: `ghostStep` applied to the ghost of the round `L` names,
entered in the map at that round where it differs from the ghost standing there. The ghosts of
the other rounds are left where they stand, and a label naming no round, or a write returning the
ghost standing there, leaves the whole state where it stands. -/
noncomputable def writeGhost [Inhabited G] (s : NetworkState n M G)
    (ghostStep : ExtendedLabel n M E → NetworkState n M G → G → G) (L : ExtendedLabel n M E) :
    NetworkState n M G :=
  match roundOf L with
  | some r =>
      if ghostStep L s (s.ghost r) = s.ghost r then s
      else { s with ghostMap := s.ghostMap.insert r (ghostStep L s (s.ghost r)) }
  | none => s

/-- The same network state over the trivial ghost: the message record, the DECIDED sets, the
corrupted set and the started rounds stand, and no round has a ghost entry. -/
def forgetGhost (s : NetworkState n M G) : NetworkState n M Unit where
  sentMap := s.sentMap
  decidedSent := s.decidedSent
  F := s.F
  ghostMap := ∅
  startedRounds := s.startedRounds

end NetworkState

/-! ### The labels a round transition carries -/

/-- The labels on which a program's transition belongs to the graded-agreement implementation:
process `j`'s own call and return at the interface, its own round multicast, a round delivery
addressed to it, and its own round-internal call or return. Every other label has a transition of
`ProgramStep`. -/
def roundOwn {n : ℕ} {M E : Type} (j : Fin n) : ExtendedLabel n M E → Prop
  | Sum.inl (.callG _ id _) => id = j
  | Sum.inl (.retG _ id _) => id = j
  | Sum.inr (.gbcaSend _ k _) => k = j
  | Sum.inr (.gbcaDeliver _ i _ _) => i = j
  | Sum.inr (.gbcaRoundEvent _ k _) => k = j
  | _ => False

/-- A round label other than a delivery is one the process acts on: the replaced program has no
transition on it, and it takes a delivery on its self-loop (D23). -/
theorem actsAt_of_roundOwn {n : ℕ} {M E : Type} {j : Fin n} {L : ExtendedLabel n M E}
    (h : roundOwn j L) (hdeliver : ∀ r k m, L ≠ Sum.inr (.gbcaDeliver r j k m)) : actsAt j L := by
  rcases L with l | e
  · cases l <;> first | exact h | exact h.elim
  · cases e with
    | gbcaDeliver r i k m => subst h; exact absurd rfl (hdeliver r k m)
    | _ => first | exact h | exact h.elim

/-! ### The transitions of one program

Process `j`'s program. Every guard reads the process's own variables and nothing else: none asks
whether another process is correct. The DECIDED relay and the ABA return are participation-guarded
(D8), and each reads the process's own record of its DECIDED sends, LeslieBP Algorithm 1's "having
not sent it" and "having sent it". The DECIDED transitions carry no termination guard, so a
terminated process keeps relaying the payloads it holds. A corrupted process's two sub-protocol
calls are outputs of the network, and every program idles on them (D11). Every label of the
extended alphabet outside `roundOwn j` has a transition here: the participant's, a loop that
takes an input at a state where the participant's transition is not enabled, or an idle one.

A corruption replaces the program of the process it names (D23). Every participant's transition
carries the replacement guard `c.corrupted = false`, so the variables stay as they are at the
corruption; `failSelf` is the transition that writes the flag, and `corruptedIdle` is the replaced
program. That self-loop is taken on every label other than `τ` and the labels of `actsAt j`, on
which the replaced program has no transition at all. -/

/-- The step relation of the program of process `j`, over a graded-agreement implementation given by
its message type, its round variables and its transitions. -/
inductive ProgramStep (P : Parameters) (M E S : Type)
    (roundStep : Fin P.n → ProcessVariables P.n S → ExtendedLabel P.n M E →
      PMF (ProcessVariables P.n S) → Prop) (j : Fin P.n) :
    ProcessVariables P.n S → ExtendedLabel P.n M E → PMF (ProcessVariables P.n S) → Prop
  /-- A transition of the graded-agreement implementation. -/
  | roundTransition (q : ProcessVariables P.n S) (L : ExtendedLabel P.n M E)
      (μ : PMF (ProcessVariables P.n S))
      (h : roundStep j q L μ) : ProgramStep P M E S roundStep j q L μ
  /-- `upon ABA(b)`: record input and estimate, start round `0`. -/
  | input (c : RoundLoopVariables P.n) (p : RoundVariablesMap S) (b : Bool)
      (hh : c.corrupted = false) (h : c.processVariables.input = none) :
      ProgramStep P M E S roundStep j (c, p) (Sum.inl (.callABA j b))
        (PMF.pure (c.setProcessVariables { c.processVariables with
          input := some b, estimate := some b, round := 0, phase := .toCallG }, p))
  /-- Input-enabledness loop on `j`'s own `callABA`: the loop absorbs a call at
  a process holding an input. The `input` transition carries the label at a process
  holding none, so the label is enabled in every state and a first call at an
  unreplaced program commits (D36). -/
  | inputLoop (c : RoundLoopVariables P.n) (p : RoundVariablesMap S) (b : Bool)
      (hh : c.corrupted = false) (hin : c.processVariables.input ≠ none) :
      ProgramStep P M E S roundStep j (c, p) (Sum.inl (.callABA j b)) (PMF.pure (c, p))
  /-- An input addressed elsewhere: not `j`'s business. -/
  | callABAIdle (c : RoundLoopVariables P.n) (p : RoundVariablesMap S)
      (id : Fin P.n) (b : Bool) (hid : id ≠ j) :
      ProgramStep P M E S roundStep j (c, p) (Sum.inl (.callABA id b)) (PMF.pure (c, p))
  /-- Return `b` on an `n − f` DECIDED quorum, having sent `⟨DECIDED, b⟩` (LeslieBP
  Algorithm 1's "having sent it"), the round-loop variables having received the input (D8). -/
  | ret (c : RoundLoopVariables P.n) (p : RoundVariablesMap S) (b : Bool)
      (hh : c.corrupted = false) (hin : c.processVariables.input ≠ none)
      (hcnt : P.n - P.f ≤ c.decidedCount b) (hsent : b ∈ c.decidedSent)
      (hret : c.processVariables.returned = false) :
      ProgramStep P M E S roundStep j (c, p) (Sum.inl (.retABA j b))
        (PMF.pure (c.setProcessVariables { c.processVariables with returned := true }, p))
  /-- A return by another process: not `j`'s business. -/
  | retABAIdle (c : RoundLoopVariables P.n) (p : RoundVariablesMap S)
      (id : Fin P.n) (b : Bool) (hid : id ≠ j) :
      ProgramStep P M E S roundStep j (c, p) (Sum.inl (.retABA id b)) (PMF.pure (c, p))
  /-- The process terminates (ABDY22 Definitions 3.1/3.2 and the p.7 note on
  termination): its own return is fired and DECIDED messages from `2f + 1`
  distinct senders have been received, so every process still running will cross the
  relay threshold without further response from this one. -/
  | terminate (c : RoundLoopVariables P.n) (p : RoundVariablesMap S) (b : Bool)
      (hh : c.corrupted = false) (hret : c.processVariables.returned = true)
      (hcnt : 2 * P.f + 1 ≤ c.decidedCount b)
      (hterm : p.terminated = false) :
      ProgramStep P M E S roundStep j (c, p) (Sum.inl Label.tau)
        (PMF.pure (c, { p with terminated := true }))
  /-- A graded-agreement call by another process: not `j`'s business. -/
  | callGIdle (c : RoundLoopVariables P.n) (p : RoundVariablesMap S)
      (r : ℕ) (id : Fin P.n) (b : Bool) (hid : id ≠ j) :
      ProgramStep P M E S roundStep j (c, p) (Sum.inl (.callG r id b)) (PMF.pure (c, p))
  /-- A graded-agreement return to another process: not `j`'s business. -/
  | retGIdle (c : RoundLoopVariables P.n) (p : RoundVariablesMap S)
      (r : ℕ) (id : Fin P.n) (out : GBCAOutput) (hid : id ≠ j) :
      ProgramStep P M E S roundStep j (c, p) (Sum.inl (.retG r id out)) (PMF.pure (c, p))
  /-- The announcement of a round's bound bit: not `j`'s business. The bit is the network's
  ghost, and no program reads it (D29). -/
  | boundGIdle (c : RoundLoopVariables P.n) (p : RoundVariablesMap S) (r : ℕ) (b : Bool) :
      ProgramStep P M E S roundStep j (c, p) (Sum.inl (.boundG r b)) (PMF.pure (c, p))
  /-- `c ← WCC_r()`, the call half at the round loop. -/
  | callW (c : RoundLoopVariables P.n) (p : RoundVariablesMap S) (r : ℕ)
      (hh : c.corrupted = false)
      (hph : c.processVariables.phase = .toCallW) (hr : c.processVariables.round = r) :
      ProgramStep P M E S roundStep j (c, p) (Sum.inl (.callW r j))
        (PMF.pure (c.setProcessVariables { c.processVariables with phase := .awaitW }, p))
  /-- A coin call by another process: not `j`'s business. -/
  | callWIdle (c : RoundLoopVariables P.n) (p : RoundVariablesMap S)
      (r : ℕ) (id : Fin P.n) (hid : id ≠ j) :
      ProgramStep P M E S roundStep j (c, p) (Sum.inl (.callW r id)) (PMF.pure (c, p))
  /-- The coin return: the round advances and nothing is sent. On a grade-2 outcome the advance
  enters `toSendDecided`, where the DECIDED send follows. The advance starts the next round;
  the round variables the process holds are retained across it (D22). -/
  | retW (c : RoundLoopVariables P.n) (p : RoundVariablesMap S) (r : ℕ) (co : Bool)
      (hh : c.corrupted = false)
      (hph : c.processVariables.phase = .awaitW) (hr : c.processVariables.round = r) :
      ProgramStep P M E S roundStep j (c, p) (Sum.inl (.retW r j co))
        (PMF.pure (c.stepRound co, p))
  /-- Input-enabledness loop on `j`'s own coin return: a program not awaiting the coin of round
  `r` takes the return and stays where it stands. The coin returns to a process that has not
  called it, as Transition System 3 does. -/
  | retWLoop (c : RoundLoopVariables P.n) (p : RoundVariablesMap S) (r : ℕ) (co : Bool)
      (hh : c.corrupted = false)
      (h : ¬ (c.processVariables.phase = .awaitW ∧ c.processVariables.round = r)) :
      ProgramStep P M E S roundStep j (c, p) (Sum.inl (.retW r j co)) (PMF.pure (c, p))
  /-- A coin return to another process: not `j`'s business. -/
  | retWIdle (c : RoundLoopVariables P.n) (p : RoundVariablesMap S)
      (r : ℕ) (id : Fin P.n) (co : Bool) (hid : id ≠ j) :
      ProgramStep P M E S roundStep j (c, p) (Sum.inl (.retW r id co)) (PMF.pure (c, p))
  /-- The process's own corruption: the program is replaced, and the flag that
  carries the replacement is the one write of the transition (D23). -/
  | failSelf (c : RoundLoopVariables P.n) (p : RoundVariablesMap S) (hh : c.corrupted = false) :
      ProgramStep P M E S roundStep j (c, p) (Sum.inl (.fail j))
        (PMF.pure ({ c with corrupted := true }, p))
  /-- Another process's corruption is not this process's business. -/
  | failIdle (c : RoundLoopVariables P.n) (p : RoundVariablesMap S) (k : Fin P.n) (hk : k ≠ j) :
      ProgramStep P M E S roundStep j (c, p) (Sum.inl (.fail k)) (PMF.pure (c, p))
  /-- The replaced program (D23): a self-loop on every label other than `τ` and
  the labels of `actsAt j`, on which the process has no transition at all. -/
  | corruptedIdle (c : RoundLoopVariables P.n) (p : RoundVariablesMap S) (L : ExtendedLabel P.n M E)
      (hh : c.corrupted = true) (hτ : L ≠ Sum.inl Label.tau) (hown : ¬ actsAt j L) :
      ProgramStep P M E S roundStep j (c, p) L (PMF.pure (c, p))
  /-- A round multicast by another process: not `j`'s business. -/
  | gbcaSendIdle (c : RoundLoopVariables P.n) (p : RoundVariablesMap S)
      (r : ℕ) (k : Fin P.n) (m : M) (hk : k ≠ j) :
      ProgramStep P M E S roundStep j (c, p) (Sum.inr (.gbcaSend r k m)) (PMF.pure (c, p))
  /-- A round delivery to another process: not `j`'s business. -/
  | gbcaDeliverIdle (c : RoundLoopVariables P.n) (p : RoundVariablesMap S)
      (r : ℕ) (i k : Fin P.n) (m : M) (hi : i ≠ j) :
      ProgramStep P M E S roundStep j (c, p) (Sum.inr (.gbcaDeliver r i k m)) (PMF.pure (c, p))
  /-- The DECIDED relay on an `f + 1` quorum, having not sent `⟨DECIDED, b⟩` (LeslieBP
  Algorithm 1's "having not sent it"), the round-loop variables having received the input (D8,
  D12′). The process records the send; the network's record is the network's half. -/
  | decidedRelay (c : RoundLoopVariables P.n) (p : RoundVariablesMap S) (b : Bool)
      (hh : c.corrupted = false) (hin : c.processVariables.input ≠ none)
      (hcnt : P.f + 1 ≤ c.decidedCount b) (hnot : b ∉ c.decidedSent) :
      ProgramStep P M E S roundStep j (c, p) (Sum.inr (.decidedRelay j b))
        (PMF.pure (c.recordDecided b, p))
  /-- A DECIDED relay by another process: not `j`'s business. -/
  | decidedRelayIdle (c : RoundLoopVariables P.n) (p : RoundVariablesMap S)
      (k : Fin P.n) (b : Bool) (hk : k ≠ j) :
      ProgramStep P M E S roundStep j (c, p) (Sum.inr (.decidedRelay k b)) (PMF.pure (c, p))
  /-- DECIDED delivery, receiver's half: at most one received message per (sender, bit)
  (D12′). Authenticity is the network's conjunct. -/
  | decidedDeliverReceive (c : RoundLoopVariables P.n) (p : RoundVariablesMap S)
      (k : Fin P.n) (b : Bool) (hh : c.corrupted = false) (hr : b ∉ c.decidedDelivered k) :
      ProgramStep P M E S roundStep j (c, p) (Sum.inr (.decidedDeliver j k b))
        (PMF.pure (c.receiveDecided k b, p))
  /-- Input-enabledness loop on a DECIDED delivery to `j`: a payload already received from the
  sender leaves the variables where they stand (D12′). -/
  | decidedDeliverLoop (c : RoundLoopVariables P.n) (p : RoundVariablesMap S)
      (k : Fin P.n) (b : Bool) (hh : c.corrupted = false) (hr : b ∈ c.decidedDelivered k) :
      ProgramStep P M E S roundStep j (c, p) (Sum.inr (.decidedDeliver j k b)) (PMF.pure (c, p))
  /-- A DECIDED delivery to another process: not `j`'s business. -/
  | decidedDeliverIdle (c : RoundLoopVariables P.n) (p : RoundVariablesMap S)
      (i k : Fin P.n) (b : Bool) (hi : i ≠ j) :
      ProgramStep P M E S roundStep j (c, p) (Sum.inr (.decidedDeliver i k b)) (PMF.pure (c, p))
  /-- The DECIDED send of a grade-2 round: the outcome of the round just closed was
  `grade2 b`, so the process sends `⟨DECIDED, b⟩` to all, records the send, clears the grade and
  enters the next round's `toCallG`. The network's record is the network's half. -/
  | decidedSend (c : RoundLoopVariables P.n) (p : RoundVariablesMap S) (b : Bool)
      (hh : c.corrupted = false) (hph : c.processVariables.phase = .toSendDecided)
      (hgr : c.processVariables.lastGrade = some (.grade2 b)) :
      ProgramStep P M E S roundStep j (c, p) (Sum.inr (.decidedSend j b))
        (PMF.pure ((c.setProcessVariables
          { c.processVariables with lastGrade := none, phase := .toCallG }).recordDecided b, p))
  /-- A DECIDED send by another process: not `j`'s business. -/
  | decidedSendIdle (c : RoundLoopVariables P.n) (p : RoundVariablesMap S)
      (k : Fin P.n) (b : Bool) (hk : k ≠ j) :
      ProgramStep P M E S roundStep j (c, p) (Sum.inr (.decidedSend k b)) (PMF.pure (c, p))
  /-- A round-internal call or return at another process: not `j`'s business. -/
  | gbcaRoundEventIdle (c : RoundLoopVariables P.n) (p : RoundVariablesMap S)
      (r : ℕ) (k : Fin P.n) (e : E) (hk : k ≠ j) :
      ProgramStep P M E S roundStep j (c, p) (Sum.inr (.gbcaRoundEvent r k e))
        (PMF.pure (c, p))
  /-- A corrupted process's graded-agreement call: not `j`'s business, at every process, the one
  the label names included. The network outputs it and the round instance takes it (D11). -/
  | byzantineCallGIdle (c : RoundLoopVariables P.n) (p : RoundVariablesMap S)
      (r : ℕ) (k : Fin P.n) (b : Bool) :
      ProgramStep P M E S roundStep j (c, p) (Sum.inr (.byzantineCallG r k b))
        (PMF.pure (c, p))
  /-- A corrupted process's coin call: not `j`'s business, at every process. The network outputs
  it and the common coin takes it (D11). -/
  | byzantineCallWIdle (c : RoundLoopVariables P.n) (p : RoundVariablesMap S)
      (r : ℕ) (k : Fin P.n) :
      ProgramStep P M E S roundStep j (c, p) (Sum.inr (.byzantineCallW r k)) (PMF.pure (c, p))

/-! ### The network

The one local state that holds what no process may see: the sent sets, the corrupted set with the
budget, and the started rounds. It takes every send on an unguarded transition that records the
message, and it outputs every delivery under the condition that the message is sent. It outputs a
corrupted process's sub-protocol calls and its injections under `k ∈ F`, at a round a process
outside `F` has started (D11, D37), and it announces the bound bit its ghost holds (D29). -/

/-- The step relation of the network. All transitions are Dirac. The successor of every
transition is that transition's effect on the sent sets, the DECIDED sets, the corrupted set and
the started rounds, with the ghost of the round the label names written by `ghostStep`. Every input
of the network has one unguarded transition. -/
inductive NetworkStep (P : Parameters) (M E G : Type) [DecidableEq M] [Inhabited G]
    (ghostStep : ExtendedLabel P.n M E → NetworkState P.n M G → G → G)
    (ghostBound : G → Option Bool) :
    NetworkState P.n M G → ExtendedLabel P.n M E → PMF (NetworkState P.n M G) → Prop
  /-- The network's half of a round multicast: sent the message under its sender. Authenticity is
  the sender's participation in the synchronised step (D5). -/
  | gbcaSend (s : NetworkState P.n M G) (r : ℕ) (j : Fin P.n) (m : M) :
      NetworkStep P M E G ghostStep ghostBound s (Sum.inr (.gbcaSend r j m))
        (PMF.pure ((s.recordGBCASend r j m).writeGhost ghostStep (Sum.inr (.gbcaSend r j m))))
  /-- The network's half of a round delivery: the message must be sent under the named sender.
  Delivery does not consume it (D5). -/
  | gbcaDeliver (s : NetworkState P.n M G) (r : ℕ) (i j : Fin P.n) (m : M)
      (h : m ∈ s.sent r j) :
      NetworkStep P M E G ghostStep ghostBound s (Sum.inr (.gbcaDeliver r i j m))
        (PMF.pure (s.writeGhost ghostStep (Sum.inr (.gbcaDeliver r i j m))))
  /-- The network's half of a DECIDED relay: the payload enters the sender's DECIDED set
  (D12′). -/
  | decidedRelay (s : NetworkState P.n M G) (j : Fin P.n) (b : Bool) :
      NetworkStep P M E G ghostStep ghostBound s (Sum.inr (.decidedRelay j b))
        (PMF.pure ((s.recordDecided j b).writeGhost ghostStep (Sum.inr (.decidedRelay j b))))
  /-- The network's half of a DECIDED delivery: the payload must be sent
  under the named sender (D12′). -/
  | decidedDeliver (s : NetworkState P.n M G) (i j : Fin P.n) (b : Bool) (h : b ∈ s.decidedSent j) :
      NetworkStep P M E G ghostStep ghostBound s (Sum.inr (.decidedDeliver i j b))
        (PMF.pure (s.writeGhost ghostStep (Sum.inr (.decidedDeliver i j b))))
  /-- The network's half of a DECIDED send: the payload enters the sender's DECIDED set
  (D12′). -/
  | decidedSend (s : NetworkState P.n M G) (j : Fin P.n) (b : Bool) :
      NetworkStep P M E G ghostStep ghostBound s (Sum.inr (.decidedSend j b))
        (PMF.pure ((s.recordDecided j b).writeGhost ghostStep (Sum.inr (.decidedSend j b))))
  /-- The network's half of a round-internal call or return: it sends nothing, and it writes the
  ghost of the round the label names. The round's program moves with it, so the ghost write
  of a call or a return of a sub-protocol stands at that call or that return. -/
  | gbcaRoundEvent (s : NetworkState P.n M G) (r : ℕ) (j : Fin P.n) (e : E) :
      NetworkStep P M E G ghostStep ghostBound s (Sum.inr (.gbcaRoundEvent r j e))
        (PMF.pure (s.writeGhost ghostStep (Sum.inr (.gbcaRoundEvent r j e))))
  /-- A corrupted process's graded-agreement call (D11), at a round a process outside `F` has
  started (D37). It sends nothing. -/
  | byzantineCallG (s : NetworkState P.n M G) (r : ℕ) (k : Fin P.n) (b : Bool) (hF : k ∈ s.F)
      (hr : r ∈ s.startedRounds) :
      NetworkStep P M E G ghostStep ghostBound s (Sum.inr (.byzantineCallG r k b))
        (PMF.pure (s.writeGhost ghostStep (Sum.inr (.byzantineCallG r k b))))
  /-- A corrupted process's coin call (D11), at a round a process outside `F` has started
  (D37). -/
  | byzantineCallW (s : NetworkState P.n M G) (r : ℕ) (k : Fin P.n) (hF : k ∈ s.F)
      (hr : r ∈ s.startedRounds) :
      NetworkStep P M E G ghostStep ghostBound s (Sum.inr (.byzantineCallW r k))
        (PMF.pure (s.writeGhost ghostStep (Sum.inr (.byzantineCallW r k))))
  /-- An external input is not the network's business. -/
  | callABAIdle (s : NetworkState P.n M G) (id : Fin P.n) (b : Bool) :
      NetworkStep P M E G ghostStep ghostBound s (Sum.inl (.callABA id b))
        (PMF.pure (s.writeGhost ghostStep (Sum.inl (.callABA id b))))
  /-- An ABA return is not the network's business: the program's own record of its DECIDED sends
  guards it, and a replaced program returns either bit (D23). -/
  | retABAIdle (s : NetworkState P.n M G) (id : Fin P.n) (b : Bool) :
      NetworkStep P M E G ghostStep ghostBound s (Sum.inl (.retABA id b))
        (PMF.pure (s.writeGhost ghostStep (Sum.inl (.retABA id b))))
  /-- A graded-agreement call sends nothing. Where the caller lies outside the corrupted set, the
  called round enters the started rounds (D37). -/
  | callG (s : NetworkState P.n M G) (r : ℕ) (id : Fin P.n) (b : Bool) :
      NetworkStep P M E G ghostStep ghostBound s (Sum.inl (.callG r id b))
        (PMF.pure ((s.recordStartedRound r id).writeGhost ghostStep (Sum.inl (.callG r id b))))
  /-- A graded-agreement return sends nothing, and writes the ghost of its round. -/
  | retG (s : NetworkState P.n M G) (r : ℕ) (id : Fin P.n) (out : GBCAOutput) :
      NetworkStep P M E G ghostStep ghostBound s (Sum.inl (.retG r id out))
        (PMF.pure (s.writeGhost ghostStep (Sum.inl (.retG r id out))))
  /-- The announcement of round `r`'s bound bit (D29): enabled exactly when the round's ghost
  holds the bit `b`, and enabled again after it fires. This is the one transition whose guard
  reads the ghost. -/
  | announceBound (s : NetworkState P.n M G) (r : ℕ) (b : Bool)
      (h : ghostBound (s.ghost r) = some b) :
      NetworkStep P M E G ghostStep ghostBound s (Sum.inl (.boundG r b))
        (PMF.pure (s.writeGhost ghostStep (Sum.inl (.boundG r b))))
  /-- A coin call sends nothing. -/
  | callWIdle (s : NetworkState P.n M G) (r : ℕ) (id : Fin P.n) :
      NetworkStep P M E G ghostStep ghostBound s (Sum.inl (.callW r id))
        (PMF.pure (s.writeGhost ghostStep (Sum.inl (.callW r id))))
  /-- A coin return sends nothing. -/
  | retWIdle (s : NetworkState P.n M G) (r : ℕ) (id : Fin P.n) (c : Bool) :
      NetworkStep P M E G ghostStep ghostBound s (Sum.inl (.retW r id c))
        (PMF.pure (s.writeGhost ghostStep (Sum.inl (.retW r id c))))
  /-- Corruption (deviation D1): total, Dirac, budget-guarded; no process's
  variables keep a copy. -/
  | fail (s : NetworkState P.n M G) (k : Fin P.n) (hnew : k ∉ s.F)
      (hbud : s.F.card < P.f) :
      NetworkStep P M E G ghostStep ghostBound s (Sum.inl (.fail k))
        (PMF.pure ((s.corrupt P k).writeGhost ghostStep (Sum.inl (.fail k))))
  /-- Byzantine round injection (D5, D11): the network multicasts on behalf of a corrupted
  sender, at a round a process outside `F` has started (D37). -/
  | byzantineGBCA (s : NetworkState P.n M G) (r : ℕ) (k : Fin P.n) (m : M) (hF : k ∈ s.F)
      (hr : r ∈ s.startedRounds) :
      NetworkStep P M E G ghostStep ghostBound s (Sum.inl .tau)
        (PMF.pure ((s.recordGBCASend r k m).writeGhost ghostStep (Sum.inl .tau)))
  /-- Byzantine DECIDED injection (D12′): either or both bits, at any time, so
  a corrupted process may equivocate. -/
  | byzantineDecided (s : NetworkState P.n M G) (k : Fin P.n) (b : Bool) (hF : k ∈ s.F) :
      NetworkStep P M E G ghostStep ghostBound s (Sum.inl .tau)
        (PMF.pure ((s.recordDecided k b).writeGhost ghostStep (Sum.inl .tau)))

/-! ### The automata and the composition pipeline -/

section Programs

variable (P : Parameters) (M E S : Type)
    (roundStep : Fin P.n → ProcessVariables P.n S → ExtendedLabel P.n M E → PMF (ProcessVariables
      P.n S) →
      Prop)

/-- The program of process `j`. -/
noncomputable def program (j : Fin P.n) : System (ProcessVariables P.n S) (ExtendedLabel P.n M E)
  where
  init := (RoundLoopVariables.initial P.n, RoundVariablesMap.initial S)
  step := ProgramStep P M E S roundStep j

@[simp] theorem program_init (j : Fin P.n) :
    (program P M E S roundStep j).init
      = (RoundLoopVariables.initial P.n, RoundVariablesMap.initial S) := rfl

@[simp] theorem program_step (j : Fin P.n) (q : ProcessVariables P.n S)
    (l : ExtendedLabel P.n M E) (μ : PMF (ProcessVariables P.n S)) :
    (program P M E S roundStep j).step q l μ ↔ ProgramStep P M E S roundStep j q l μ :=
  Iff.rfl

end Programs

/-- The state of the implementation: the process family, the network and
the common coin's instance family. -/
abbrev State (P : Parameters) (M S G : Type) : Type :=
  (∀ _ : Fin P.n, ProcessVariables P.n S) ×
    (NetworkState P.n M G × InstanceFamilyState (WCC.SpecState.initial P.n) (WCC.failAct P))

/-! ### The network as a system -/

section NetworkAdversary

variable (P : Parameters) (M E G : Type) [DecidableEq M] [Inhabited G]
    (ghostStep : ExtendedLabel P.n M E → NetworkState P.n M G → G → G)
    (ghostBound : G → Option Bool)

/-- The network. -/
noncomputable def network : System (NetworkState P.n M G) (ExtendedLabel P.n M E) where
  init := NetworkState.initial P.n M G
  step := NetworkStep P M E G ghostStep ghostBound

@[simp] theorem network_init :
    (network P M E G ghostStep ghostBound).init
      = NetworkState.initial P.n M G := rfl

@[simp] theorem network_step (s : NetworkState P.n M G) (l : ExtendedLabel P.n M E)
    (μ : PMF (NetworkState P.n M G)) :
    (network P M E G ghostStep ghostBound).step s l μ ↔
      NetworkStep P M E G ghostStep ghostBound s l μ :=
  Iff.rfl

end NetworkAdversary

/-! ### The three components composed -/

section Composition
variable (P : Parameters) (M E S G : Type) [DecidableEq M] [Inhabited G]
    (roundStep : Fin P.n → ProcessVariables P.n S → ExtendedLabel P.n M E → PMF (ProcessVariables
      P.n S) →
      Prop)
    (ghostStep : ExtendedLabel P.n M E → NetworkState P.n M G → G → G)
    (ghostBound : G → Option Bool)

/-- The three components in parallel, over the extended alphabet: the synchronised process group,
the network and the lifted coin. -/
noncomputable def systemExtended : System (State P M S G) (ExtendedLabel P.n M E) :=
  (System.synchronisedProduct (program P M E S roundStep)).parallel
    ((network P M E G ghostStep ghostBound).parallel (coinOverExtendedAlphabet P M E))

/-- The network events hidden, the result read back over `Label n`. -/
noncomputable def systemHidden : System (State P M S G) (Label P.n) :=
  ((systemExtended P M E S G roundStep ghostStep ghostBound).abstract
    (networkEventLabels P.n)).relabel

/-- **The implementation**: the group with the sub-protocol API hidden. -/
noncomputable def system : System (State P M S G) (Label P.n) :=
  (systemHidden P M E S G roundStep ghostStep ghostBound).abstract
    (Label.hiddenAPI P.n)

end Composition

/-! ### What an implementation must supply about its own transitions -/

/-- What the implementation's graded-agreement transitions must satisfy for the lemmas of
`Implementation/StepCases.lean` to determine the remaining transitions from a label, and for the
program to be input-enabled (`Implementation/InputEnabledness.lean`): a transition of process `j`
carries a label of `roundOwn j`, it fires only at a process whose program has not been replaced
(D23), it is Dirac, and the round's transitions take every round delivery addressed to `j` at an
unreplaced program. -/
class IsRoundStep (P : Parameters) (M E S : Type)
    (roundStep : Fin P.n → ProcessVariables P.n S → ExtendedLabel P.n M E →
      PMF (ProcessVariables P.n S) → Prop) : Prop where
  /-- A round transition carries a round label. -/
  own : ∀ {j : Fin P.n} {q : ProcessVariables P.n S} {L : ExtendedLabel P.n M E}
    {μ : PMF (ProcessVariables P.n S)}, roundStep j q L μ → roundOwn j L
  /-- A round transition fires only at an unreplaced program. -/
  correct : ∀ {j : Fin P.n} {q : ProcessVariables P.n S} {L : ExtendedLabel P.n M E}
    {μ : PMF (ProcessVariables P.n S)}, roundStep j q L μ → q.1.corrupted = false
  /-- A round transition is Dirac. -/
  dirac : ∀ {j : Fin P.n} {q : ProcessVariables P.n S} {L : ExtendedLabel P.n M E}
    {μ : PMF (ProcessVariables P.n S)}, roundStep j q L μ → ∃ q', μ = PMF.pure q'
  /-- The round's transitions take every round delivery addressed to `j` at an unreplaced
  program, by a receive or a loop: a delivery is an output of the network and an input of the
  program. -/
  deliveryEnabled : ∀ {j : Fin P.n} {q : ProcessVariables P.n S} {r : ℕ} {k : Fin P.n} {m : M},
    q.1.corrupted = false → ∃ μ, roundStep j q (Sum.inr (.gbcaDeliver r j k m)) μ

end Implementation
end ABA
end PLTS
