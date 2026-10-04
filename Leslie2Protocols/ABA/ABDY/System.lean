/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sathiya / Claude
-/

import Leslie2Protocols.ABA.Composition.Components
import Leslie2Protocols.ABA.GBCA.ABDY.MessagesAndVariables
import Leslie2Protocols.ABA.Implementation.CompositeTransitions

/-!
# The protocol as it runs

The subject of the whole chain: `n` programs, one per process, beside one
network and the common coin. A program reads its own variables, its own
received sets and its own replacement flag, and nothing else about corruption: not
the corrupted set, not the budget, not another process's status (D23). The
adversary holds the round-tagged message sets, the DECIDED sets and the
corrupted set with its budget, and it is the sole authority on the Byzantine
labels. The common coin is held at specification level.

The shape is the parametric implementation of `ABA/Implementation/System.lean`, which
carries the round loop, the DECIDED sets, the coin's call and return, corruption, the
network and the composition pipeline for any graded-agreement
implementation. This file supplies the things an implementation fixes and
nothing else:

* the round message type, `GBCA.ByABDY.Message` — the five message levels of
  `GBCA/ABDY/MessagesAndVariables.lean` (D18);
* the per-process per-round variables, `GBCA.ByABDY.RoundVariables`, held by round in a finite map
(D22);
* the transitions of the implementation, `RoundStep`: the graded-agreement call, the nine round
  multicasts, the round delivery, the call against variables already called, and the three graded
  returns;
* the network's ghost — the type `Option Bool` of a round's bound
  bit, the write `abdyGhostStep`, the read `abdyGhostOutput` and the guard
  `abdyAnnouncedBound` the two return transitions put on the announced bit.

`ABDY.protocol P` is the implementation at those three, named for the authors of the implementation
it runs, as `AFW.protocol P` is named for the authors of the gather-based one. Its per-process
variables are the round-loop variables beside the variables of each round, the variables a process
holds in a round are retained across the round advance, and a round never touched reads as the
initial variables (D22).

## The round transitions

Every guard reads the process's own variables. A round transition reads and writes the variables of
the round its label tags, whichever round the round loop is in, and is guarded by
`p.terminated = false` (D22). The transitions are taken in the wait-until order of ABDY22's
Algorithm 6 from the `BIND` level down, each of those levels requiring the process's own send at
the level below; the `VOTE` transitions ask for no own send, the `ECHO` they read being sent by an
`upon` handler that may still be pending. A synchronised transition carries the process's half of a
synchronised step with the network: on a send the write to its own variables, on a delivery the
write to its received sets. The Byzantine round transitions have no transition at the process they
name (D11, D22). The three return transitions take the bit their label announces free: the bit is
the network's ghost output and the program neither guards on it nor records it. -/

namespace PLTS
namespace ABA
namespace ABDY

open Implementation hiding NetworkEvent ExtendedLabel
open Composition

/-! ### The round vocabulary at ABDY22's implementation -/

/-- The round variables of one process: its variables in every round the process has touched, and
whether it has terminated (D22). -/
abbrev RoundVariablesMap (n : ℕ) : Type := Implementation.RoundVariablesMap
  (GBCA.ByABDY.RoundVariables n)

/-- ABDY22's round variables, as the implementation consumes them. -/
instance instIsRoundVariables (n : ℕ) : IsRoundVariables n GBCA.ByABDY.Message
  (GBCA.ByABDY.RoundVariables n)
  where
  initial := GBCA.ByABDY.RoundVariables.initial n
  deliverTo p k m := p.deliverTo k m

namespace RoundVariablesMap

variable {n : ℕ}

/-- The initial round variables: no round touched, not terminated. -/
def initial (n : ℕ) : RoundVariablesMap n := Implementation.RoundVariablesMap.initial
  (GBCA.ByABDY.RoundVariables n)

@[simp] theorem initial_roundVariables (n r : ℕ) :
    (initial n).roundVariables r = GBCA.ByABDY.RoundVariables.initial n :=
  Implementation.RoundVariablesMap.initial_roundVariables r

@[simp] theorem roundVariables_setRoundVariables_ne (q : RoundVariablesMap n) (r : ℕ)
    (p : GBCA.ByABDY.RoundVariables n) {r' : ℕ} (h : r' ≠ r) :
    (q.setRoundVariables r p).roundVariables r' = q.roundVariables r' :=
  Implementation.RoundVariablesMap.roundVariables_setRoundVariables_ne q r p h

end RoundVariablesMap

/-- The state of one process: its round-loop variables and its variables per round (D22). -/
abbrev ProcessVariables (n : ℕ) : Type := Implementation.ProcessVariables n
  (GBCA.ByABDY.RoundVariables n)

/-! ### The network's state at ABDY22's implementation -/

/-- The state of the network: the round-tagged message sets, the
DECIDED sets, the corrupted set with its budget, and the bound bit of every
round. -/
abbrev NetworkState (n : ℕ) : Type := Implementation.NetworkState n GBCA.ByABDY.Message (Option
  Bool)

/-- Sent `⟨DECIDED, b⟩` under sender `j` (D12′). -/
abbrev NetworkState.recordDecided {n : ℕ} (s : NetworkState n) (j : Fin n) (b : Bool) : NetworkState
  n :=
  Implementation.NetworkState.recordDecided s j b

/-- Corruption (deviation D1): total, Dirac, budget-guarded. -/
abbrev NetworkState.corrupt (P : Parameters) (id : Fin P.n) (s : NetworkState P.n) : NetworkState
  P.n :=
  Implementation.NetworkState.corrupt P id s

/-! ### The network's ghost at ABDY22's implementation

The bound bit of a round is a ghost output: the specification announces it on
every return label (`ABA/GBCA/Specification.lean`) and no program reads it. At this
implementation the network holds it, one bit per round, in the ghost
`Implementation.NetworkState.ghost`.

`abdyGhostStep` writes it. A return records the bit its own label announces
where the ghost holds none for the round and leaves the ghost alone otherwise,
so the ghost is write-once and both returns of a round — the correct one and the
Byzantine one — write it the same way. Every other transition leaves it alone.

`abdyGhostOutput` reads it out: the bit the ghost holds for the round, and
`GBCA.ByABDY.boundOf` of the round's sent sets, the corrupted set and the outcome
otherwise. This is the account of the round's bound bit that
`GBCA/ABDY/MessagesAndVariables.lean` holds in its own network state, computed here from the
network's sent sets instead. `abdyAnnouncedBound` is the guard of the two
return transitions: the bit a return announces is `abdyGhostOutput` of the round. -/

/-- The ghost write of a transition: a return records the bit its label
announces where the ghost holds none for the round; every other transition
leaves the ghost alone. -/
def abdyGhostStep (P : Parameters) :
    ExtendedLabel P.n GBCA.ByABDY.Message → NetworkState P.n → Option Bool → Option Bool
  | Sum.inl (.retG _ _ _ bnd), _, g => some (g.getD bnd)
  | Sum.inr (.byzantineRetG _ _ _ bnd), _, g => some (g.getD bnd)
  | _, _, g => g

/-- The ghost output of a return: the round's bound bit where the ghost holds one, and
`GBCA.ByABDY.boundOf` of the round's messages where there is none. -/
def abdyGhostOutput (P : Parameters) (s : NetworkState P.n) (r : ℕ) (_id : Fin P.n)
    (out : GBCAOutput) : Bool :=
  (s.ghost r).getD (GBCA.ByABDY.boundOf (s.sent r) s.F out)

/-- The bit the network announces on a return: the round's ghost
output, and no other. This is the relation the implementation's `ghostOutput`
parameter takes at this instantiation. It is reducible, so the guard of the two
return transitions is the equation itself. -/
abbrev abdyAnnouncedBound (P : Parameters) (s : NetworkState P.n) (r : ℕ) (id : Fin P.n)
    (out : GBCAOutput) (bnd : Bool) : Prop :=
  bnd = abdyGhostOutput P s r id out


/-- A transition whose ghost write is the identity leaves the adversary's whole
state where it stands. Every transition but the two returns is such a
transition. -/
theorem writeGhost_abdy_id (P : Parameters) (w : NetworkState P.n)
    (L : ExtendedLabel P.n GBCA.ByABDY.Message)
    (h : ∀ g, abdyGhostStep P L w g = g) :
    w.writeGhost (abdyGhostStep P) L = w := by
  unfold Implementation.NetworkState.writeGhost
  split
  · next r _ => rw [h]; simp
  · rfl

/-! ### The ghost write of each transition -/

section GhostWrites
variable (P : Parameters) (w : NetworkState P.n)

@[simp] theorem writeGhost_tau :
    w.writeGhost (abdyGhostStep P) (Sum.inl Label.tau) = w :=
  writeGhost_abdy_id P w _ fun _ => rfl
@[simp] theorem writeGhost_callABA (id : Fin P.n) (b : Bool) :
    w.writeGhost (abdyGhostStep P) (Sum.inl (.callABA id b)) = w :=
  writeGhost_abdy_id P w _ fun _ => rfl
@[simp] theorem writeGhost_retABA (id : Fin P.n) (b : Bool) :
    w.writeGhost (abdyGhostStep P) (Sum.inl (.retABA id b)) = w :=
  writeGhost_abdy_id P w _ fun _ => rfl
@[simp] theorem writeGhost_callG (r : ℕ) (id : Fin P.n) (b : Bool) :
    w.writeGhost (abdyGhostStep P) (Sum.inl (.callG r id b)) = w :=
  writeGhost_abdy_id P w _ fun _ => rfl
@[simp] theorem writeGhost_callW (r : ℕ) (id : Fin P.n) :
    w.writeGhost (abdyGhostStep P) (Sum.inl (.callW r id)) = w :=
  writeGhost_abdy_id P w _ fun _ => rfl
@[simp] theorem writeGhost_retW (r : ℕ) (id : Fin P.n) (b : Bool) :
    w.writeGhost (abdyGhostStep P) (Sum.inl (.retW r id b)) = w :=
  writeGhost_abdy_id P w _ fun _ => rfl
@[simp] theorem writeGhost_fail (k : Fin P.n) :
    w.writeGhost (abdyGhostStep P) (Sum.inl (.fail k)) = w :=
  writeGhost_abdy_id P w _ fun _ => rfl
@[simp] theorem writeGhost_gbcaSend (r : ℕ) (j : Fin P.n) (m : GBCA.ByABDY.Message) :
    w.writeGhost (abdyGhostStep P) (Sum.inr (.gbcaSend r j m)) = w :=
  writeGhost_abdy_id P w _ fun _ => rfl
@[simp] theorem writeGhost_gbcaDeliver (r : ℕ) (i j : Fin P.n) (m : GBCA.ByABDY.Message) :
    w.writeGhost (abdyGhostStep P) (Sum.inr (.gbcaDeliver r i j m)) = w :=
  writeGhost_abdy_id P w _ fun _ => rfl
@[simp] theorem writeGhost_decidedSend (j : Fin P.n) (b : Bool) :
    w.writeGhost (abdyGhostStep P) (Sum.inr (.decidedSend j b)) = w :=
  writeGhost_abdy_id P w _ fun _ => rfl
@[simp] theorem writeGhost_decidedDeliver (i j : Fin P.n) (b : Bool) :
    w.writeGhost (abdyGhostStep P) (Sum.inr (.decidedDeliver i j b)) = w :=
  writeGhost_abdy_id P w _ fun _ => rfl
@[simp] theorem writeGhost_retWPublish (r : ℕ) (id : Fin P.n) (c b : Bool) :
    w.writeGhost (abdyGhostStep P) (Sum.inr (.retWPublish r id c b)) = w :=
  writeGhost_abdy_id P w _ fun _ => rfl
@[simp] theorem writeGhost_gbcaCallLoop (r : ℕ) (id : Fin P.n) (b : Bool) :
    w.writeGhost (abdyGhostStep P) (Sum.inr (.gbcaCallLoop r id b)) = w :=
  writeGhost_abdy_id P w _ fun _ => rfl
@[simp] theorem writeGhost_byzantineCallG (r : ℕ) (k : Fin P.n) (b : Bool) :
    w.writeGhost (abdyGhostStep P) (Sum.inr (.byzantineCallG r k b)) = w :=
  writeGhost_abdy_id P w _ fun _ => rfl
@[simp] theorem writeGhost_byzantineCallGLoop (r : ℕ) (k : Fin P.n) (b : Bool) :
    w.writeGhost (abdyGhostStep P) (Sum.inr (.byzantineCallGLoop r k b)) = w :=
  writeGhost_abdy_id P w _ fun _ => rfl
@[simp] theorem writeGhost_byzantineCallW (r : ℕ) (k : Fin P.n) :
    w.writeGhost (abdyGhostStep P) (Sum.inr (.byzantineCallW r k)) = w :=
  writeGhost_abdy_id P w _ fun _ => rfl
@[simp] theorem writeGhost_byzantineRetW (r : ℕ) (k : Fin P.n) (b : Bool) :
    w.writeGhost (abdyGhostStep P) (Sum.inr (.byzantineRetW r k b)) = w :=
  writeGhost_abdy_id P w _ fun _ => rfl

/-! The two return transitions, which do write. The ghost of the round the
label names holds the announced bit after the write, and the ghost of every
other round is unchanged. -/

@[simp] theorem writeGhost_retG_self (r : ℕ) (id : Fin P.n) (out : GBCAOutput)
    (bnd : Bool) :
    (w.writeGhost (abdyGhostStep P) (Sum.inl (.retG r id out bnd))).ghost r
      = some ((w.ghost r).getD bnd) :=
  writeGhost_ghost_self w rfl

theorem writeGhost_retG_ne (r : ℕ) (id : Fin P.n) (out : GBCAOutput) (bnd : Bool)
    {r' : ℕ} (h : r' ≠ r) :
    (w.writeGhost (abdyGhostStep P) (Sum.inl (.retG r id out bnd))).ghost r'
      = w.ghost r' :=
  writeGhost_ghost_ne w rfl h

@[simp] theorem writeGhost_byzantineRetG_self (r : ℕ) (k : Fin P.n) (out : GBCAOutput)
    (bnd : Bool) :
    (w.writeGhost (abdyGhostStep P) (Sum.inr (.byzantineRetG r k out bnd))).ghost r
      = some ((w.ghost r).getD bnd) :=
  writeGhost_ghost_self w rfl

theorem writeGhost_byzantineRetG_ne (r : ℕ) (k : Fin P.n) (out : GBCAOutput) (bnd : Bool)
    {r' : ℕ} (h : r' ≠ r) :
    (w.writeGhost (abdyGhostStep P) (Sum.inr (.byzantineRetG r k out bnd))).ghost r'
      = w.ghost r' :=
  writeGhost_ghost_ne w rfl h

end GhostWrites
/-! ### The transitions of the graded-agreement implementation -/

/-- The round transitions of process `j`: the graded-agreement call, the nine multicasts of the
five message levels, the round delivery, the call against variables already called, and the three
graded returns. -/
inductive RoundStep (P : Parameters) (j : Fin P.n) :
    ProcessVariables P.n → ExtendedLabel P.n GBCA.ByABDY.Message → PMF (ProcessVariables P.n) → Prop
  /-- The graded-agreement call: the round loop hands its estimate to the variables of round `r`,
  which record it as the input. -/
  | callG_call (c : RoundLoopVariables P.n) (p : RoundVariablesMap P.n) (r : ℕ) (b : Bool)
      (hh : c.corrupted = false)
      (hph : c.processVariables.phase = .toCallG) (hr : c.processVariables.round = r)
      (hterm : p.terminated = false)
      (hest : c.processVariables.estimate = some b) (hin : (p.roundVariables
        r).processVariables.input = none) :
      RoundStep P j (c, p) (Sum.inl (.callG r j b))
        (PMF.pure (c.setProcessVariables { c.processVariables with phase := .awaitG },
          p.setRoundVariables r ((p.roundVariables r).setProcessVariables { (p.roundVariables
            r).processVariables with input := some b })))
  /-- Return with outcome `grade2 v`: an `n − f` `ECHO5 v` quorum. The round's variables are called
  and its own `ECHO5` is out. Case (1) heads the algorithm's chain, so there is no higher case to
  deny. -/
  | retGGrade2 (c : RoundLoopVariables P.n) (p : RoundVariablesMap P.n) (r : ℕ) (v : Bool) (bnd :
      Bool)
      (hh : c.corrupted = false)
      (hph : c.processVariables.phase = .awaitG) (hr : c.processVariables.round = r)
      (hterm : p.terminated = false)
      (hin : (p.roundVariables r).processVariables.input ≠ none)
      (hlv : (p.roundVariables r).processVariables.sentEcho5 ≠ none)
      (hcnt : P.n - P.f ≤ (p.roundVariables r).receivedCount (.echo5 (some v)))
      (hret : (p.roundVariables r).processVariables.returned = false) :
      RoundStep P j (c, p) (Sum.inl (.retG r j (.grade2 v) bnd))
        (PMF.pure (c.setProcessVariables { c.processVariables with
            estimate := (GBCAOutput.grade2 v).estimate, lastGrade := some (.grade2 v),
              phase := .toCallW },
          p.setRoundVariables r ((p.roundVariables r).setProcessVariables { (p.roundVariables
            r).processVariables with
            returned := true })))
  /-- Return with outcome `grade1 v`: an `n − f` any-`ECHO5` quorum containing `ECHO5 v`, `f + 1`
  `BIND v`s and `|Valid| > 1`. The round's variables are called, its own `ECHO5` is out, and
  `hnotGrade2` denies case (1) at either bit. -/
  | retGGrade1 (c : RoundLoopVariables P.n) (p : RoundVariablesMap P.n) (r : ℕ) (v : Bool) (bnd :
      Bool)
      (hh : c.corrupted = false)
      (hph : c.processVariables.phase = .awaitG) (hr : c.processVariables.round = r)
      (hterm : p.terminated = false)
      (hin : (p.roundVariables r).processVariables.input ≠ none)
      (hlv : (p.roundVariables r).processVariables.sentEcho5 ≠ none)
      (hnotGrade2 : ∀ v, (p.roundVariables r).receivedCount (.echo5 (some v)) < P.n - P.f)
      (hcnt : P.n - P.f ≤ (p.roundVariables r).echo5Count)
      (honce : ∃ k, GBCA.ByABDY.Message.echo5 (some v) ∈ (p.roundVariables r).received k)
      (hbind : P.f + 1 ≤ (p.roundVariables r).receivedCount (.bind (some v)))
      (hval : (p.roundVariables r).bothValid P)
      (hret : (p.roundVariables r).processVariables.returned = false) :
      RoundStep P j (c, p) (Sum.inl (.retG r j (.grade1 v) bnd))
        (PMF.pure (c.setProcessVariables { c.processVariables with
            estimate := (GBCAOutput.grade1 v).estimate, lastGrade := some (.grade1 v),
              phase := .toCallW },
          p.setRoundVariables r ((p.roundVariables r).setProcessVariables { (p.roundVariables
            r).processVariables with
            returned := true })))
  /-- Return with outcome `grade0`: an `n − f` `ECHO5 ⊥` quorum and `|Valid| > 1`. The round's
  variables are called, its own `ECHO5` is out, `hnotGrade2` denies case (1) at either bit, and
  `hnotGrade1` denies case (2) in the reduced form `GBCA.ByABDY.Algorithm.retGrade0`
  states. -/
  | retGGrade0 (c : RoundLoopVariables P.n) (p : RoundVariablesMap P.n) (r : ℕ) (bnd : Bool)
      (hh : c.corrupted = false)
      (hph : c.processVariables.phase = .awaitG) (hr : c.processVariables.round = r)
      (hterm : p.terminated = false)
      (hin : (p.roundVariables r).processVariables.input ≠ none)
      (hlv : (p.roundVariables r).processVariables.sentEcho5 ≠ none)
      (hnotGrade2 : ∀ v, (p.roundVariables r).receivedCount (.echo5 (some v)) < P.n - P.f)
      (hnotGrade1 : ∀ v, (∃ k, GBCA.ByABDY.Message.echo5 (some v) ∈ (p.roundVariables r).received k)
        →
        (p.roundVariables r).receivedCount (.bind (some v)) < P.f + 1)
      (hcnt : P.n - P.f ≤ (p.roundVariables r).receivedCount (.echo5 none))
      (hval : (p.roundVariables r).bothValid P)
      (hret : (p.roundVariables r).processVariables.returned = false) :
      RoundStep P j (c, p) (Sum.inl (.retG r j .grade0 bnd))
        (PMF.pure (c.setProcessVariables { c.processVariables with
            estimate := GBCAOutput.grade0.estimate, lastGrade := some .grade0, phase := .toCallW },
          p.setRoundVariables r ((p.roundVariables r).setProcessVariables { (p.roundVariables
            r).processVariables with
            returned := true })))
  /-- The round's `INPUT b`: the process's own input in the variables of round `r`, not yet
  multicast there. ABDY22 Algorithm 6 line 2 and the first statement of LeslieBP Algorithm 2
  (D22). -/
  | gbcaSendInput (c : RoundLoopVariables P.n) (p : RoundVariablesMap P.n) (r : ℕ) (b : Bool)
      (hh : c.corrupted = false)
      (hterm : p.terminated = false)
      (hin : (p.roundVariables r).processVariables.input = some b)
      (hsend : (p.roundVariables r).processVariables.sentInput b = false) :
      RoundStep P j (c, p) (Sum.inr (.gbcaSend r j (.input b)))
        (PMF.pure (c,
          p.setRoundVariables r ((p.roundVariables r).setProcessVariables { (p.roundVariables
            r).processVariables with
            sentInput := Function.update (p.roundVariables r).processVariables.sentInput b true })))
  /-- The round's `INPUT` relay: `f + 1` received `⟨INPUT, b⟩` messages in the variables of round
  `r`, not yet multicast there (D8, D18, D22). -/
  | gbcaSendRelay (c : RoundLoopVariables P.n) (p : RoundVariablesMap P.n) (r : ℕ) (b : Bool)
      (hh : c.corrupted = false)
      (hterm : p.terminated = false)
      (hin : (p.roundVariables r).processVariables.input ≠ none)
      (hcnt : P.f + 1 ≤ (p.roundVariables r).receivedCount (.input b))
      (hsend : (p.roundVariables r).processVariables.sentInput b = false) :
      RoundStep P j (c, p) (Sum.inr (.gbcaSend r j (.input b)))
        (PMF.pure (c,
          p.setRoundVariables r ((p.roundVariables r).setProcessVariables { (p.roundVariables
            r).processVariables with
            sentInput := Function.update (p.roundVariables r).processVariables.sentInput b true })))
  /-- The round's `ECHO`: an `n − f` `INPUT b` quorum (D18, D22). -/
  | gbcaSendEcho (c : RoundLoopVariables P.n) (p : RoundVariablesMap P.n) (r : ℕ) (b : Bool)
      (hh : c.corrupted = false)
      (hterm : p.terminated = false)
      (hin : (p.roundVariables r).processVariables.input ≠ none)
      (hcnt : P.n - P.f ≤ (p.roundVariables r).receivedCount (.input b))
      (hsend : (p.roundVariables r).processVariables.sentEcho = none) :
      RoundStep P j (c, p) (Sum.inr (.gbcaSend r j (.echo b)))
        (PMF.pure (c, p.setRoundVariables r
          ((p.roundVariables r).setProcessVariables { (p.roundVariables r).processVariables with
            sentEcho := some b })))
  /-- The round's `VOTE b`: an `n − f` `ECHO b` quorum. The process's own `ECHO` in that round is
  sent by one of the algorithm's `upon` handlers and may still be pending, so no own-send condition
  applies here (D18, D22). -/
  | gbcaSendVoteBit (c : RoundLoopVariables P.n) (p : RoundVariablesMap P.n) (r : ℕ) (b : Bool)
      (hh : c.corrupted = false)
      (hterm : p.terminated = false)
      (hin : (p.roundVariables r).processVariables.input ≠ none)
      (hcnt : P.n - P.f ≤ (p.roundVariables r).receivedCount (.echo b))
      (hsend : (p.roundVariables r).processVariables.sentVote = none) :
      RoundStep P j (c, p) (Sum.inr (.gbcaSend r j (.vote (some b))))
        (PMF.pure (c, p.setRoundVariables r
          ((p.roundVariables r).setProcessVariables { (p.roundVariables r).processVariables with
            sentVote := some (some b)
            })))
  /-- The round's `VOTE ⊥`: `n − f` `ECHO`s of any payload and `|Valid| > 1`, and no single-bit
  `ECHO` quorum among the received messages. The process's own `ECHO` in that round is sent by one
  of the algorithm's `upon` handlers and may still be pending, so no own-send condition applies here
  (D18, D22). -/
  | gbcaSendVoteBot (c : RoundLoopVariables P.n) (p : RoundVariablesMap P.n) (r : ℕ)
      (hh : c.corrupted = false)
      (hterm : p.terminated = false)
      (hin : (p.roundVariables r).processVariables.input ≠ none)
      (hnot : ∀ b, (p.roundVariables r).receivedCount (.echo b) < P.n - P.f)
      (hcnt : P.n - P.f ≤ (p.roundVariables r).echoCount)
      (hval : (p.roundVariables r).bothValid P) (hsend : (p.roundVariables
        r).processVariables.sentVote = none) :
      RoundStep P j (c, p) (Sum.inr (.gbcaSend r j (.vote none)))
        (PMF.pure (c, p.setRoundVariables r
          ((p.roundVariables r).setProcessVariables { (p.roundVariables r).processVariables with
            sentVote := some none })))
  /-- The round's `BIND b`: an `n − f` `VOTE b` quorum, the process's own `VOTE` in that round
  already out (D18, D22). -/
  | gbcaSendBindBit (c : RoundLoopVariables P.n) (p : RoundVariablesMap P.n) (r : ℕ) (b : Bool)
      (hh : c.corrupted = false)
      (hterm : p.terminated = false)
      (hin : (p.roundVariables r).processVariables.input ≠ none)
      (hlv : (p.roundVariables r).processVariables.sentVote ≠ none)
      (hcnt : P.n - P.f ≤ (p.roundVariables r).receivedCount (.vote (some b)))
      (hsend : (p.roundVariables r).processVariables.sentBind = none) :
      RoundStep P j (c, p) (Sum.inr (.gbcaSend r j (.bind (some b))))
        (PMF.pure (c, p.setRoundVariables r
          ((p.roundVariables r).setProcessVariables { (p.roundVariables r).processVariables with
            sentBind := some (some b)
            })))
  /-- The round's `BIND ⊥`: `n − f` `VOTE`s of any payload and `|Valid| > 1`, the process's own
  `VOTE` in that round already out, and no single-bit `VOTE` quorum among the received messages
  (D18, D22). -/
  | gbcaSendBindBot (c : RoundLoopVariables P.n) (p : RoundVariablesMap P.n) (r : ℕ)
      (hh : c.corrupted = false)
      (hterm : p.terminated = false)
      (hin : (p.roundVariables r).processVariables.input ≠ none)
      (hlv : (p.roundVariables r).processVariables.sentVote ≠ none)
      (hnot : ∀ b, (p.roundVariables r).receivedCount (.vote (some b)) < P.n - P.f)
      (hcnt : P.n - P.f ≤ (p.roundVariables r).voteCount)
      (hval : (p.roundVariables r).bothValid P) (hsend : (p.roundVariables
        r).processVariables.sentBind = none) :
      RoundStep P j (c, p) (Sum.inr (.gbcaSend r j (.bind none)))
        (PMF.pure (c, p.setRoundVariables r
          ((p.roundVariables r).setProcessVariables { (p.roundVariables r).processVariables with
            sentBind := some none })))
  /-- The round's `ECHO5 b`: an `n − f` `BIND b` quorum, the process's own `BIND` in that round
  already out (D18, D22). -/
  | gbcaSendEcho5Bit (c : RoundLoopVariables P.n) (p : RoundVariablesMap P.n) (r : ℕ) (b : Bool)
      (hh : c.corrupted = false)
      (hterm : p.terminated = false)
      (hin : (p.roundVariables r).processVariables.input ≠ none)
      (hlv : (p.roundVariables r).processVariables.sentBind ≠ none)
      (hcnt : P.n - P.f ≤ (p.roundVariables r).receivedCount (.bind (some b)))
      (hsend : (p.roundVariables r).processVariables.sentEcho5 = none) :
      RoundStep P j (c, p) (Sum.inr (.gbcaSend r j (.echo5 (some b))))
        (PMF.pure (c, p.setRoundVariables r
          ((p.roundVariables r).setProcessVariables { (p.roundVariables r).processVariables with
            sentEcho5 := some (some b)
            })))
  /-- The round's `ECHO5 ⊥`: `n − f` `BIND`s of any payload and `|Valid| > 1`, the process's own
  `BIND` in that round already out, and no single-bit `BIND` quorum among the received messages
  (D18, D22). -/
  | gbcaSendEcho5Bot (c : RoundLoopVariables P.n) (p : RoundVariablesMap P.n) (r : ℕ)
      (hh : c.corrupted = false)
      (hterm : p.terminated = false)
      (hin : (p.roundVariables r).processVariables.input ≠ none)
      (hlv : (p.roundVariables r).processVariables.sentBind ≠ none)
      (hnot : ∀ b, (p.roundVariables r).receivedCount (.bind (some b)) < P.n - P.f)
      (hcnt : P.n - P.f ≤ (p.roundVariables r).bindCount)
      (hval : (p.roundVariables r).bothValid P) (hsend : (p.roundVariables
        r).processVariables.sentEcho5 = none) :
      RoundStep P j (c, p) (Sum.inr (.gbcaSend r j (.echo5 none)))
        (PMF.pure (c, p.setRoundVariables r
          ((p.roundVariables r).setProcessVariables { (p.roundVariables r).processVariables with
            sentEcho5 := some none })))
  /-- Round delivery, receiver's half: file the message under `received k`, the messages from the
  sender, in the variables of round `r`, whichever round the round loop is in. Authenticity is
  the network's conjunct (D22). -/
  | gbcaDeliverReceive (c : RoundLoopVariables P.n) (p : RoundVariablesMap P.n)
      (r : ℕ) (k : Fin P.n) (m : GBCA.ByABDY.Message) (hh : c.corrupted = false)
      (hterm : p.terminated = false) :
      RoundStep P j (c, p) (Sum.inr (.gbcaDeliver r j k m))
        (PMF.pure (c, p.deliverTo r k m))
  /-- The graded-agreement call against variables already called: the round loop moves, the
  variables do not. The transition carries no termination guard, so a terminated process in
  `toCallG` whose variables in round `r` are uncalled has no transition on either call label, a
  gap this implementation accepts. -/
  | gbcaCallLoop (c : RoundLoopVariables P.n) (p : RoundVariablesMap P.n) (r : ℕ) (b : Bool)
      (hh : c.corrupted = false)
      (hph : c.processVariables.phase = .toCallG) (hr : c.processVariables.round = r)
      (hest : c.processVariables.estimate = some b)
      (hin : (p.roundVariables r).processVariables.input ≠ none) :
      RoundStep P j (c, p) (Sum.inr (.gbcaCallLoop r j b))
        (PMF.pure (c.setProcessVariables { c.processVariables with phase := .awaitG }, p))

/-- The transitions above meet the implementation's conditions: each carries a label of
`roundOwn j`, each fires only at an unreplaced program, each is Dirac, and each
of the three returns takes the announced bit free (D29). -/
instance instIsRoundStep (P : Parameters) :
    IsRoundStep P GBCA.ByABDY.Message Empty (GBCA.ByABDY.RoundVariables P.n) (RoundStep P) where
  own h := by
    cases h <;> rfl
  correct h := by
    cases h <;> assumption
  dirac h := by
    cases h <;> exact ⟨_, rfl⟩
  boundBitFree h := by cases h <;> constructor <;> assumption

/-! ### The step relations, the automata and the pipeline -/

/-- The step relation of the program of process `j`: the implementation's transitions beside
ABDY22's own round transitions. -/
abbrev ABAProgramStep (P : Parameters) (j : Fin P.n) :
    ProcessVariables P.n → ExtendedLabel P.n GBCA.ByABDY.Message → PMF (ProcessVariables P.n) → Prop
      :=
  ProgramStep P GBCA.ByABDY.Message Empty (GBCA.ByABDY.RoundVariables P.n) (RoundStep P) j

/-- The step relation of the network. -/
abbrev NetworkStep (P : Parameters) :
    NetworkState P.n → ExtendedLabel P.n GBCA.ByABDY.Message → PMF (NetworkState P.n)
  → Prop :=
  Implementation.NetworkStep P GBCA.ByABDY.Message Empty (Option Bool)
    (abdyGhostStep P)
    (abdyAnnouncedBound P)

/-- The program of process `j`. -/
noncomputable abbrev ABAProgram (P : Parameters) (j : Fin P.n) :
    System (ProcessVariables P.n) (ExtendedLabel P.n GBCA.ByABDY.Message) :=
  program P GBCA.ByABDY.Message Empty (GBCA.ByABDY.RoundVariables P.n) (RoundStep P) j

/-- The network. -/
noncomputable abbrev network (P : Parameters) :
    System (NetworkState P.n) (ExtendedLabel P.n GBCA.ByABDY.Message) :=
  Implementation.network P GBCA.ByABDY.Message Empty (Option Bool)
    (abdyGhostStep P)
    (abdyAnnouncedBound P)


/-- The state of the protocol: the process family, the network and
the common coin. -/
abbrev ProtocolState (P : Parameters) : Type :=
  Implementation.State P GBCA.ByABDY.Message (GBCA.ByABDY.RoundVariables P.n) (Option Bool)

/-- The three components in parallel, over the extended alphabet: the synchronised process group,
the network and the lifted common coin. -/
noncomputable def protocolExtended (P : Parameters) : System (ProtocolState P)
  (Composition.ExtendedLabel P.n GBCA.ByABDY.Message) :=
  Implementation.systemExtended P GBCA.ByABDY.Message Empty (GBCA.ByABDY.RoundVariables P.n)
    (Option Bool)
    (ABDY.RoundStep P)
    (ABDY.abdyGhostStep P) (ABDY.abdyAnnouncedBound P)

/-- **The protocol group**: the labels the components synchronise on hidden, the result read
back over `Label n`. -/
noncomputable def protocolHidden (P : Parameters) : System (ProtocolState P) (Label P.n) :=
  Implementation.systemHidden P GBCA.ByABDY.Message Empty (GBCA.ByABDY.RoundVariables P.n)
    (Option Bool)
    (ABDY.RoundStep P)
    (ABDY.abdyGhostStep P) (ABDY.abdyAnnouncedBound P)

/-- **The protocol system**: the group with the sub-protocol API hidden. -/
noncomputable def protocol (P : Parameters) : System (ProtocolState P) (Label P.n) :=
  Implementation.system P GBCA.ByABDY.Message Empty (GBCA.ByABDY.RoundVariables P.n)
    (Option Bool)
    (ABDY.RoundStep
    P)
    (ABDY.abdyGhostStep P) (ABDY.abdyAnnouncedBound P)


/-! ### Reading composite transitions

The implementation's own lemmas, named at this instantiation. -/

theorem protocolHidden_step_iff (P : Parameters) (q : ABDY.ProtocolState P) (l : Label P.n)
    (μ : PMF (ABDY.ProtocolState P)) :
    (ABDY.protocolHidden P).step q l μ ↔
      (l = .tau ∧ ∃ e : NetworkEvent P.n GBCA.ByABDY.Message,
        (ABDY.protocolExtended P).step q (Sum.inr e) μ) ∨
      (ABDY.protocolExtended P).step q (Sum.inl l) μ :=
  systemHidden_step_iff q l μ

theorem protocol_step_iff (P : Parameters) (q : ABDY.ProtocolState P) (l : Label P.n)
    (μ : PMF (ABDY.ProtocolState P)) :
    (ABDY.protocol P).step q l μ ↔
      (l = .tau ∧ ∃ l' ∈ Label.hiddenAPI P.n, (ABDY.protocolHidden P).step q l' μ) ∨
      (l ∉ Label.hiddenAPI P.n ∧ (ABDY.protocolHidden P).step q l μ) :=
  system_step_iff q l μ

/-- A synchronised transition: every process, the network and the lifted common
coin move together, and only the coin's successor can fail to be a Dirac. -/
theorem protocolExtended_event_cases (P : Parameters) {u : ∀ _ : Fin P.n, ProcessVariables P.n}
    {w : NetworkState P.n} {o : ℕ → WCC.SpecState P.n} {e : NetworkEvent P.n GBCA.ByABDY.Message}
    {μ : PMF (ABDY.ProtocolState P)}
    (h : (ABDY.protocolExtended P).step (u, w, o) (Sum.inr e) μ) :
    ∃ (x : ∀ _ : Fin P.n, ProcessVariables P.n) (w' : NetworkState P.n)
      (μ₃ : PMF (ℕ → WCC.SpecState P.n)),
      (∀ i, ABAProgramStep P i (u i) (Sum.inr e) (PMF.pure (x i))) ∧
      NetworkStep P w (Sum.inr e) (PMF.pure w') ∧
      (coinOverRoundAlphabet P GBCA.ByABDY.Message).step o (Sum.inr e) μ₃ ∧
      μ = prodPMF (PMF.pure x) (prodPMF (PMF.pure w') μ₃) :=
  systemExtended_event_cases h

/-- A visible shared-label transition. -/
theorem protocolExtended_label_cases (P : Parameters) {u : ∀ _ : Fin P.n, ProcessVariables P.n}
    {w : NetworkState P.n} {o : ℕ → WCC.SpecState P.n} {l : Label P.n} (hl : l ≠ Label.tau)
    {μ : PMF (ABDY.ProtocolState P)}
    (h : (ABDY.protocolExtended P).step (u, w, o) (Sum.inl l) μ) :
    ∃ (x : ∀ _ : Fin P.n, ProcessVariables P.n) (w' : NetworkState P.n)
      (ω : PMF (ℕ → WCC.SpecState P.n)),
      (∀ i, ABAProgramStep P i (u i) (Sum.inl l) (PMF.pure (x i))) ∧
      NetworkStep P w (Sum.inl l) (PMF.pure w') ∧
      (WCC.specFamily P).step o l ω ∧
      μ = prodPMF (PMF.pure x) (prodPMF (PMF.pure w') ω) :=
  systemExtended_label_cases hl h

/-- A silent shared-label transition: one process terminating, or the network's
own injection. The common coin has no silent transition, so it contributes none. -/
theorem protocolExtended_tau_cases (P : Parameters) {u : ∀ _ : Fin P.n, ProcessVariables P.n}
    {w : NetworkState P.n} {o : ℕ → WCC.SpecState P.n}
    {μ : PMF (ABDY.ProtocolState P)}
    (h : (ABDY.protocolExtended P).step (u, w, o) (Sum.inl Label.tau) μ) :
    (∃ (i : Fin P.n) (y : ProcessVariables P.n),
      ABAProgramStep P i (u i) (Sum.inl Label.tau) (PMF.pure y) ∧
      μ = PMF.pure (Function.update u i y, w, o)) ∨
    (∃ w', NetworkStep P w (Sum.inl .tau) (PMF.pure w') ∧ μ = PMF.pure (u, w', o)) :=
  systemExtended_tau_cases h

/-! ### ABDY22's own transitions, by label class

Each lemma reads a round transition off its label: the participant's transition as its guards
together with the Dirac it produces. The idle transition of a non-participant and the replaced
program's self-loop are read by the implementation's own lemmas; here the label names the acting
process, so those two systems are the ones ruled out. -/

section RoundStepCases

variable {P : Parameters} {j : Fin P.n} {q : ProcessVariables P.n} {ν : PMF (ProcessVariables P.n)}

theorem programStep_callG_own {r : ℕ} {b : Bool}
    (h : ABAProgramStep P j q (Sum.inl (.callG r j b)) ν) :
    q.1.corrupted = false ∧
      q.1.processVariables.phase = .toCallG ∧ q.1.processVariables.round = r ∧ q.2.terminated =
        false ∧
      q.1.processVariables.estimate = some b ∧ (q.2.roundVariables r).processVariables.input = none
        ∧
      ν = PMF.pure (q.1.setProcessVariables { q.1.processVariables with phase := .awaitG },
        q.2.setRoundVariables r ((q.2.roundVariables r).setProcessVariables { (q.2.roundVariables
          r).processVariables with input := some b })) := by
  cases h
  case roundTransition h' =>
    cases h'
    exact ⟨by assumption, by assumption, by assumption, by assumption,
      by assumption, by assumption, rfl⟩
  case callGIdle => exact absurd rfl ‹_ ≠ j›
  case corruptedIdle => rename_i hown; exact absurd rfl hown

theorem programStep_retGGrade2_own {r : ℕ} {v bnd : Bool}
    (h : ABAProgramStep P j q (Sum.inl (.retG r j (.grade2 v) bnd)) ν) :
    q.1.corrupted = false ∧
      q.1.processVariables.phase = .awaitG ∧ q.1.processVariables.round = r ∧ q.2.terminated = false
        ∧
      (q.2.roundVariables r).processVariables.input ≠ none ∧ (q.2.roundVariables
        r).processVariables.sentEcho5 ≠ none ∧
      P.n - P.f ≤ (q.2.roundVariables r).receivedCount (.echo5 (some v)) ∧
      (q.2.roundVariables r).processVariables.returned = false ∧
      ν = PMF.pure (q.1.setProcessVariables { q.1.processVariables with
          estimate := (GBCAOutput.grade2 v).estimate, lastGrade := some (.grade2 v),
            phase := .toCallW },
        q.2.setRoundVariables r
          ((q.2.roundVariables r).setProcessVariables { (q.2.roundVariables r).processVariables with
            returned := true })) :=
            by
  cases h
  case roundTransition h' =>
    cases h'
    exact ⟨by assumption, by assumption, by assumption, by assumption,
      by assumption, by assumption, by assumption, by assumption, rfl⟩
  case retGIdle => exact absurd rfl ‹_ ≠ j›
  case corruptedIdle => rename_i hown; exact absurd rfl hown

theorem programStep_retGGrade1_own {r : ℕ} {v bnd : Bool}
    (h : ABAProgramStep P j q (Sum.inl (.retG r j (.grade1 v) bnd)) ν) :
    q.1.corrupted = false ∧
      q.1.processVariables.phase = .awaitG ∧ q.1.processVariables.round = r ∧ q.2.terminated = false
        ∧
      (q.2.roundVariables r).processVariables.input ≠ none ∧ (q.2.roundVariables
        r).processVariables.sentEcho5 ≠ none ∧
      (∀ v, (q.2.roundVariables r).receivedCount (.echo5 (some v)) < P.n - P.f) ∧
      P.n - P.f ≤ (q.2.roundVariables r).echo5Count ∧
      (∃ k, GBCA.ByABDY.Message.echo5 (some v) ∈ (q.2.roundVariables r).received k) ∧
      P.f + 1 ≤ (q.2.roundVariables r).receivedCount (.bind (some v)) ∧
      (q.2.roundVariables r).bothValid P ∧
      (q.2.roundVariables r).processVariables.returned = false ∧
      ν = PMF.pure (q.1.setProcessVariables { q.1.processVariables with
          estimate := (GBCAOutput.grade1 v).estimate, lastGrade := some (.grade1 v),
            phase := .toCallW },
        q.2.setRoundVariables r
          ((q.2.roundVariables r).setProcessVariables { (q.2.roundVariables r).processVariables with
            returned := true })) :=
            by
  cases h
  case roundTransition h' =>
    cases h'
    exact ⟨by assumption, by assumption, by assumption, by assumption, by assumption,
      by assumption, by assumption, by assumption, by assumption, by assumption,
      by assumption, by assumption, rfl⟩
  case retGIdle => exact absurd rfl ‹_ ≠ j›
  case corruptedIdle => rename_i hown; exact absurd rfl hown

theorem programStep_retGGrade0_own {r : ℕ} {bnd : Bool}
    (h : ABAProgramStep P j q (Sum.inl (.retG r j .grade0 bnd)) ν) :
    q.1.corrupted = false ∧
      q.1.processVariables.phase = .awaitG ∧ q.1.processVariables.round = r ∧ q.2.terminated = false
        ∧
      (q.2.roundVariables r).processVariables.input ≠ none ∧ (q.2.roundVariables
        r).processVariables.sentEcho5 ≠ none ∧
      (∀ v, (q.2.roundVariables r).receivedCount (.echo5 (some v)) < P.n - P.f) ∧
      (∀ v, (∃ k, GBCA.ByABDY.Message.echo5 (some v) ∈ (q.2.roundVariables r).received k) →
        (q.2.roundVariables r).receivedCount (.bind (some v)) < P.f + 1) ∧
      P.n - P.f ≤ (q.2.roundVariables r).receivedCount (.echo5 none) ∧
      (q.2.roundVariables r).bothValid P ∧
      (q.2.roundVariables r).processVariables.returned = false ∧
      ν = PMF.pure (q.1.setProcessVariables { q.1.processVariables with
          estimate := GBCAOutput.grade0.estimate, lastGrade := some .grade0, phase := .toCallW },
        q.2.setRoundVariables r
          ((q.2.roundVariables r).setProcessVariables { (q.2.roundVariables r).processVariables with
            returned := true })) :=
            by
  cases h
  case roundTransition h' =>
    cases h'
    exact ⟨by assumption, by assumption, by assumption, by assumption, by assumption,
      by assumption, by assumption, by assumption, by assumption, by assumption,
      by assumption, rfl⟩
  case retGIdle => exact absurd rfl ‹_ ≠ j›
  case corruptedIdle => rename_i hown; exact absurd rfl hown

/-- A send of `⟨INPUT, b⟩` by the program is the first multicast of its own input or the relay. -/
theorem programStep_gbcaSend_input_self {r : ℕ} {b : Bool}
    (h : ABAProgramStep P j q (Sum.inr (.gbcaSend r j (.input b))) ν) :
    q.1.corrupted = false ∧
      q.2.terminated = false ∧
      ((q.2.roundVariables r).processVariables.input = some b ∨
        (q.2.roundVariables r).processVariables.input ≠ none ∧
        P.f + 1 ≤ (q.2.roundVariables r).receivedCount (.input b)) ∧
      (q.2.roundVariables r).processVariables.sentInput b = false ∧
      ν = PMF.pure (q.1,
        q.2.setRoundVariables r ((q.2.roundVariables r).setProcessVariables { (q.2.roundVariables
          r).processVariables with
          sentInput := Function.update (q.2.roundVariables r).processVariables.sentInput b true }))
            := by
  cases h
  case roundTransition h' =>
    cases h'
    · exact ⟨by assumption, by assumption, Or.inl (by assumption), by assumption, rfl⟩
    · exact ⟨by assumption, by assumption, Or.inr ⟨by assumption, by assumption⟩,
        by assumption, rfl⟩
  case gbcaSendIdle => exact absurd rfl ‹_ ≠ j›
  case corruptedIdle => rename_i hown; exact absurd rfl hown

theorem programStep_gbcaSend_echo_self {r : ℕ} {b : Bool}
    (h : ABAProgramStep P j q (Sum.inr (.gbcaSend r j (.echo b))) ν) :
    q.1.corrupted = false ∧
      q.2.terminated = false ∧ (q.2.roundVariables r).processVariables.input ≠ none ∧
      P.n - P.f ≤ (q.2.roundVariables r).receivedCount (.input b) ∧
      (q.2.roundVariables r).processVariables.sentEcho = none ∧
      ν = PMF.pure (q.1, q.2.setRoundVariables r
        ((q.2.roundVariables r).setProcessVariables { (q.2.roundVariables r).processVariables with
          sentEcho := some b })) :=
          by
  cases h
  case roundTransition h' =>
    cases h'
    exact ⟨by assumption, by assumption, by assumption, by assumption,
      by assumption, rfl⟩
  case gbcaSendIdle => exact absurd rfl ‹_ ≠ j›
  case corruptedIdle => rename_i hown; exact absurd rfl hown

theorem programStep_gbcaSend_voteBit_self {r : ℕ} {b : Bool}
    (h : ABAProgramStep P j q (Sum.inr (.gbcaSend r j (.vote (some b)))) ν) :
    q.1.corrupted = false ∧
      q.2.terminated = false ∧ (q.2.roundVariables r).processVariables.input ≠ none ∧
      P.n - P.f ≤ (q.2.roundVariables r).receivedCount (.echo b) ∧
      (q.2.roundVariables r).processVariables.sentVote = none ∧
      ν = PMF.pure (q.1, q.2.setRoundVariables r
        ((q.2.roundVariables r).setProcessVariables { (q.2.roundVariables r).processVariables with
          sentVote := some (some b)
          })) := by
  cases h
  case roundTransition h' =>
    cases h'
    exact ⟨by assumption, by assumption, by assumption, by assumption,
      by assumption, rfl⟩
  case gbcaSendIdle => exact absurd rfl ‹_ ≠ j›
  case corruptedIdle => rename_i hown; exact absurd rfl hown

theorem programStep_gbcaSend_voteBot_self {r : ℕ}
    (h : ABAProgramStep P j q (Sum.inr (.gbcaSend r j (.vote none))) ν) :
    q.1.corrupted = false ∧
      q.2.terminated = false ∧ (q.2.roundVariables r).processVariables.input ≠ none ∧
      (∀ b, (q.2.roundVariables r).receivedCount (.echo b) < P.n - P.f) ∧
      P.n - P.f ≤ (q.2.roundVariables r).echoCount ∧
      (q.2.roundVariables r).bothValid P ∧ (q.2.roundVariables r).processVariables.sentVote = none ∧
      ν = PMF.pure (q.1, q.2.setRoundVariables r
        ((q.2.roundVariables r).setProcessVariables { (q.2.roundVariables r).processVariables with
          sentVote := some none }))
          := by
  cases h
  case roundTransition h' =>
    cases h'
    exact ⟨by assumption, by assumption, by assumption, by assumption,
      by assumption, by assumption, by assumption, rfl⟩
  case gbcaSendIdle => exact absurd rfl ‹_ ≠ j›
  case corruptedIdle => rename_i hown; exact absurd rfl hown

theorem programStep_gbcaSend_bindBit_self {r : ℕ} {b : Bool}
    (h : ABAProgramStep P j q (Sum.inr (.gbcaSend r j (.bind (some b)))) ν) :
    q.1.corrupted = false ∧
      q.2.terminated = false ∧ (q.2.roundVariables r).processVariables.input ≠ none ∧
      (q.2.roundVariables r).processVariables.sentVote ≠ none ∧
      P.n - P.f ≤ (q.2.roundVariables r).receivedCount (.vote (some b)) ∧
      (q.2.roundVariables r).processVariables.sentBind = none ∧
      ν = PMF.pure (q.1, q.2.setRoundVariables r
        ((q.2.roundVariables r).setProcessVariables { (q.2.roundVariables r).processVariables with
          sentBind := some (some b)
          })) := by
  cases h
  case roundTransition h' =>
    cases h'
    exact ⟨by assumption, by assumption, by assumption, by assumption,
      by assumption, by assumption, rfl⟩
  case gbcaSendIdle => exact absurd rfl ‹_ ≠ j›
  case corruptedIdle => rename_i hown; exact absurd rfl hown

theorem programStep_gbcaSend_bindBot_self {r : ℕ}
    (h : ABAProgramStep P j q (Sum.inr (.gbcaSend r j (.bind none))) ν) :
    q.1.corrupted = false ∧
      q.2.terminated = false ∧ (q.2.roundVariables r).processVariables.input ≠ none ∧
      (q.2.roundVariables r).processVariables.sentVote ≠ none ∧
      (∀ b, (q.2.roundVariables r).receivedCount (.vote (some b)) < P.n - P.f) ∧
      P.n - P.f ≤ (q.2.roundVariables r).voteCount ∧
      (q.2.roundVariables r).bothValid P ∧ (q.2.roundVariables r).processVariables.sentBind = none ∧
      ν = PMF.pure (q.1, q.2.setRoundVariables r
        ((q.2.roundVariables r).setProcessVariables { (q.2.roundVariables r).processVariables with
          sentBind := some none }))
          := by
  cases h
  case roundTransition h' =>
    cases h'
    exact ⟨by assumption, by assumption, by assumption, by assumption,
      by assumption, by assumption, by assumption, by assumption, rfl⟩
  case gbcaSendIdle => exact absurd rfl ‹_ ≠ j›
  case corruptedIdle => rename_i hown; exact absurd rfl hown

theorem programStep_gbcaSend_echo5Bit_self {r : ℕ} {b : Bool}
    (h : ABAProgramStep P j q (Sum.inr (.gbcaSend r j (.echo5 (some b)))) ν) :
    q.1.corrupted = false ∧
      q.2.terminated = false ∧ (q.2.roundVariables r).processVariables.input ≠ none ∧
      (q.2.roundVariables r).processVariables.sentBind ≠ none ∧
      P.n - P.f ≤ (q.2.roundVariables r).receivedCount (.bind (some b)) ∧
      (q.2.roundVariables r).processVariables.sentEcho5 = none ∧
      ν = PMF.pure (q.1, q.2.setRoundVariables r
        ((q.2.roundVariables r).setProcessVariables { (q.2.roundVariables r).processVariables with
          sentEcho5 :=
            some (some b) })) := by
  cases h
  case roundTransition h' =>
    cases h'
    exact ⟨by assumption, by assumption, by assumption, by assumption,
      by assumption, by assumption, rfl⟩
  case gbcaSendIdle => exact absurd rfl ‹_ ≠ j›
  case corruptedIdle => rename_i hown; exact absurd rfl hown

theorem programStep_gbcaSend_echo5Bot_self {r : ℕ}
    (h : ABAProgramStep P j q (Sum.inr (.gbcaSend r j (.echo5 none))) ν) :
    q.1.corrupted = false ∧
      q.2.terminated = false ∧ (q.2.roundVariables r).processVariables.input ≠ none ∧
      (q.2.roundVariables r).processVariables.sentBind ≠ none ∧
      (∀ b, (q.2.roundVariables r).receivedCount (.bind (some b)) < P.n - P.f) ∧
      P.n - P.f ≤ (q.2.roundVariables r).bindCount ∧
      (q.2.roundVariables r).bothValid P ∧ (q.2.roundVariables r).processVariables.sentEcho5 = none
        ∧
      ν = PMF.pure (q.1, q.2.setRoundVariables r
        ((q.2.roundVariables r).setProcessVariables { (q.2.roundVariables r).processVariables with
          sentEcho5 := some none
          })) := by
  cases h
  case roundTransition h' =>
    cases h'
    exact ⟨by assumption, by assumption, by assumption, by assumption,
      by assumption, by assumption, by assumption, by assumption, rfl⟩
  case gbcaSendIdle => exact absurd rfl ‹_ ≠ j›
  case corruptedIdle => rename_i hown; exact absurd rfl hown

theorem programStep_gbcaDeliver_self {r : ℕ} {k : Fin P.n} {m : GBCA.ByABDY.Message}
    (h : ABAProgramStep P j q (Sum.inr (.gbcaDeliver r j k m)) ν) :
    q.1.corrupted = false ∧ q.2.terminated = false ∧
      ν = PMF.pure (q.1, q.2.deliverTo r k m) := by
  cases h
  case roundTransition h' =>
    cases h'
    exact ⟨by assumption, by assumption, rfl⟩
  case gbcaDeliverIdle => exact absurd rfl ‹_ ≠ j›
  case corruptedIdle => rename_i hown; exact absurd rfl hown

theorem programStep_gbcaCallLoop_self {r : ℕ} {b : Bool}
    (h : ABAProgramStep P j q (Sum.inr (.gbcaCallLoop r j b)) ν) :
    q.1.corrupted = false ∧
      q.1.processVariables.phase = .toCallG ∧ q.1.processVariables.round = r ∧
        q.1.processVariables.estimate = some b ∧
      (q.2.roundVariables r).processVariables.input ≠ none ∧
      ν = PMF.pure (q.1.setProcessVariables { q.1.processVariables with phase := .awaitG }, q.2) :=
        by
  cases h
  case roundTransition h' =>
    cases h'
    exact ⟨by assumption, by assumption, by assumption, by assumption,
      by assumption, rfl⟩
  case gbcaCallLoopIdle => exact absurd rfl ‹_ ≠ j›
  case corruptedIdle => rename_i hown; exact absurd rfl hown

end RoundStepCases

end ABDY

end ABA
end PLTS
