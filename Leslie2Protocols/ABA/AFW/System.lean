/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sathiya / Claude
-/

import Leslie2Protocols.ABA.Implementation.System
import Leslie2Protocols.ABA.GBCA.AFW.Counting
import Leslie2Protocols.ABA.Gather.Components
import Leslie2Protocols.ABA.ReliableBroadcast.Bracha.MessagesAndVariables

/-!
# The gather-based protocol as it runs

The gather-based graded agreement, read as a protocol rather than as a composition: `n` programs
beside one network and the common coin. This is the implementation of
`ABA/Implementation/System.lean` at the gather-based implementation, as `ABA/ABDY/System.lean` is
that implementation at ABDY22's. It supplies a round message type, the round's variables, the
round's transitions, and the network's ghost with its write and its read. It sits in the namespace
`AFW`, after Attiya, Flam and Welch, and so `AFW.protocol` is what `ABDY.protocol` is at ABDY22's.

## One sent for every network state

A round of the gather-based implementation carries `2n + 2` network states:
one for each of the two gather instances, which carries that gather's `ECHO`, `VOTE` and `BIND`
messages, and one for each of the `2n` Bracha instances, `n` carrying the inputs in each of the
two gathers. The network of the implementation holds one sent family per round, over the tagged
message type `Message`, whose tag names the network state a message belongs to and, for a Bracha
message, the instance it belongs to. The sent index is the sender, so a threshold counts distinct
senders (D5).

## The variables of one process

A process's data lies in those instances: `j` holds its own local state in each of the `2n + 2` of
them, and the composed system indexes those local states by instance and then by process. A
program holds its own data and no one else's, so `RoundVariables` holds them the other way round:
`j`'s local state in each gather instance, and `j`'s local state in each of the `n` instances of
each Bracha family. Every guard of the gather-based implementation reads the acting process's own
local states and the network states, and the two transitions that read a network state are the
network's delivery and its Byzantine injection, so every guard reads the same values after the
transposition.

## The transitions

The round's transitions are the transitions of the programs of `GBCA.ByAFW.roundOverBracha`,
written over the tagged message type: the transitions of its graded-agreement programs
(`GBCA.ByAFW.ProgramStep`), of its gather programs (`Gather.ProgramStep`) and of the Bracha
programs beneath them (`BRB.ProgramStep`). Each is the process's half of a step whose network half
is a transition of the network. A send writes the sender's own variables and the network records
the message; a delivery files the message in the receiver's own local state, dispatched on the tag.
Every call and every return of a sub-protocol is a transition of its own. The graded-agreement
call, the call of the process's own input-broadcast instance in each of the two gathers, the first
gather's return, the second gather's call, the second gather's return, the round's own return and
the return of each of the `2n` input-broadcast instances are each one transition. A call of an
input-broadcast instance reads the payload its gather variables hold and records it as that
instance's input; the leader's `⟨INIT, ·⟩` is the send that follows,
`firstGatherInputBroadcastInit` and `secondGatherInputBroadcastInit`. A return writes what it
returned in the caller's variables. The round's variables therefore hold the two gather local
states over `Gather.ProcessVariables`, which carries what each input-broadcast instance returned,
and the two intermediate phases `candidate` and `output`. A gather guard reads those variables
and the gather messages delivered here, as the guard of the composed gather program does:
`Gather.ProcessVariables.accepted` is the `ECHO` payload `AP_i` of AFW25's Algorithm 5, line 9,
`Gather.approvedBy` and `Gather.holdsInputBroadcastReturn` are the guards on the variables, and the
gather's return waits for `n − f` delivered `BIND` payloads (AFW25's Algorithm 5, line 18).

The round takes its call label `callG r j b` on two transitions. `callG` records the estimate as
the first gather's input at a round whose first gather holds no input, and `callGLoop` moves the
round loop alone at a round whose first gather holds one, as `input` and `inputLoop` take the ABA
call (D36). A terminated program takes a round delivery on `deliverLoop`, which leaves its
variables where they stand (D22), so an unreplaced program takes every round delivery addressed to
it. A corrupted process's graded-agreement call `byzantineCallG` and its coin call
`byzantineCallW` are outputs of the network, and every program takes them on an idle transition
(D11).

## The network's ghost

The ghost the network holds for round `r` is `AFW.Ghost`: the first gather's recorded core, the
second gather's recorded core, and the round's bound bit, each written once (D30). `AFW.ghostStep`
writes it. The round's first `gbcaRoundEvent r _ (firstGatherReturn _)` records the first core,
`Gather.coreOf` of the round's first gather network state. The round's first
`gbcaRoundEvent r _ (secondGatherReturn _)` records the second core the same way. A return
`retG r _ _` at a ghost holding no bit records the bit `GBCA.boundOfCore P C` of the recorded first
core `C`. A process returns only after its own first gather has returned, so the round's first
return records the bit, and a replaced program takes no transition on `retG` (D23), so that return
is a return by an unreplaced program. Every other label leaves the ghost where it stands.

The network state `Gather.coreOf` is read on is `AFW.firstGatherOf`, the first gather's messages
out of the network's tagged sent sets beside its corrupted set, and `AFW.secondGatherOf` is the
second's. `Gather.coreOf` reads the sent sets and the corrupted set alone
(`Gather.coreOf_networkState_only`), so the network computes the core from its own state.

`AFW.ghostBound` reads the bit. The network's announcement `boundG r b` is enabled exactly when
`ghostBound` of the round's ghost is `some b`, which holds at every state from the round's first
return on, and it may repeat (D29). The return label carries the graded outcome alone, and no
program reads the ghost. -/

namespace PLTS
namespace ABA
namespace AFW

open Implementation Gather

/-! ### The tagged message type -/

/-- A round's messages: the two gather network states and the `2n` Bracha network states,
tagged by the network state they belong to. A Bracha tag carries the instance, whose
index is its leader. -/
inductive Message (n : ℕ) : Type
  /-- A message of the first gather's network state. -/
  | firstGather (m : Gather.Message n Bool)
  /-- A message of the second gather's network state. -/
  | secondGather (m : Gather.Message n (Option Bool))
  /-- A message of the input-broadcast instance `k` of the first gather. -/
  | firstGatherInputBroadcasts (k : Fin n) (m : BRB.Message Bool)
  /-- A message of the input-broadcast instance `k` of the second gather. -/
  | secondGatherInputBroadcasts (k : Fin n) (m : BRB.Message (Option Bool))
  deriving DecidableEq

/-! ### The round's own calls and returns -/

/-- The calls and returns at the boundaries between a round's program and its sub-protocol
instances, each carrying the value of the call or of the return, as `upon X.return(v)` of LeslieBP's
Algorithm 4 carries it. An event carries a value and no map, so the alphabet built over it is
decidable. -/
inductive RoundEvent (n : ℕ) : Type
  /-- The first gather returns the candidate computed from what it gathered (AFW25, Algorithm 4,
  lines 1 and 2). -/
  | firstGatherReturn (x : Option Bool)
  /-- The process calls the second gather with its candidate (AFW25, Algorithm 4, line 4). -/
  | secondGatherCall (x : Option Bool)
  /-- The second gather returns, and the graded outcome is computed from what it gathered (AFW25,
  Algorithm 4, lines 5 to 8). -/
  | secondGatherReturn (out : GBCAOutput)
  /-- The process calls the instance broadcasting its input in the first gather with `v` (AFW25,
  Algorithm 5, line 6). -/
  | firstGatherInputBroadcastCall (v : Bool)
  /-- The process calls the instance broadcasting its input in the second gather with `v` (AFW25,
  Algorithm 5, line 6). -/
  | secondGatherInputBroadcastCall (v : Option Bool)
  /-- The instance broadcasting `k`'s input in the first gather returns `v` (AFW25, Algorithm 5,
  lines 1 and 2). -/
  | firstGatherInputBroadcastReturn (k : Fin n) (v : Bool)
  /-- The instance broadcasting `k`'s input in the second gather returns `v` (AFW25, Algorithm 5,
  lines 1 and 2). -/
  | secondGatherInputBroadcastReturn (k : Fin n) (v : Option Bool)
  deriving DecidableEq

/-! ### The variables of one process in one round -/

/-- One process's data in one round, held by instance: its local state in each gather
instance, and its local state in each of the `n` instances of each input-broadcast family.
This is the composed system's instance-major indexing transposed. -/
structure RoundVariables (n : ℕ) : Type where
  /-- The candidate the first gather's return determines here (AFW25, Algorithm 4, line 2). -/
  candidate : Option (Option Bool)
  /-- The graded outcome the second gather's return determines here (AFW25, Algorithm 4,
  line 7). -/
  output : Option GBCAOutput
  /-- The process's local state in the first gather instance. -/
  firstGather : LocalState n (Gather.ProcessVariables n Bool) (Gather.Message n Bool)
  /-- The process's local state in the second gather instance. -/
  secondGather :
    LocalState n (Gather.ProcessVariables n (Option Bool)) (Gather.Message n (Option Bool))
  /-- The process's local state in each input-broadcast instance of the first
  gather. -/
  firstGatherInputBroadcasts : ∀ _ : Fin n, LocalState n (BRB.ProcessVariables Bool) (BRB.Message
    Bool)
  /-- The process's local state in each input-broadcast instance of the second
  gather. -/
  secondGatherInputBroadcasts : ∀ _ : Fin n,
    LocalState n (BRB.ProcessVariables (Option Bool)) (BRB.Message (Option Bool))

namespace RoundVariables

variable {n : ℕ}

/-- The initial variables: every local state empty over the initial process variables. -/
def initial (n : ℕ) : RoundVariables n where
  candidate := none
  output := none
  firstGather := LocalState.initial n _ (Gather.ProcessVariables.initial n Bool)
  secondGather := LocalState.initial n _ (Gather.ProcessVariables.initial n (Option Bool))
  firstGatherInputBroadcasts := fun _ => LocalState.initial n _ (BRB.ProcessVariables.initial Bool)
  secondGatherInputBroadcasts := fun _ => LocalState.initial n _ (BRB.ProcessVariables.initial
    (Option
    Bool))

/-- File a delivered message in the local state of the network state its tag names. -/
def deliverTo (s : RoundVariables n) (k : Fin n) : Message n → RoundVariables n
  | .firstGather m => { s with firstGather := s.firstGather.deliverTo k m }
  | .secondGather m => { s with secondGather := s.secondGather.deliverTo k m }
  | .firstGatherInputBroadcasts i m =>
      { s with
        firstGatherInputBroadcasts :=
          Function.update s.firstGatherInputBroadcasts i ((s.firstGatherInputBroadcasts i).deliverTo
            k m) }
  | .secondGatherInputBroadcasts i m =>
      { s with
        secondGatherInputBroadcasts :=
          Function.update s.secondGatherInputBroadcasts i ((s.secondGatherInputBroadcasts
            i).deliverTo k m) }

end RoundVariables

/-- The gather-based round variables, as the implementation consumes them. -/
instance instIsRoundVariables (n : ℕ) : IsRoundVariables n (Message n) (RoundVariables n) where
  initial := RoundVariables.initial n
  deliverTo s k m := s.deliverTo k m

@[simp] theorem roundVariables_initial (n : ℕ) :
    (IsRoundVariables.initial : RoundVariables n) = RoundVariables.initial n := rfl

@[simp] theorem roundVariables_deliverTo (n : ℕ) (s : RoundVariables n) (k : Fin n)
    (m : Message n) : (IsRoundVariables.deliverTo s k m : RoundVariables n) = s.deliverTo k m := rfl

/-- The round variables of one process: the variables it holds per round, and whether it has
terminated (D22). -/
abbrev RoundVariablesMap (n : ℕ) : Type := Implementation.RoundVariablesMap (RoundVariables n)

/-- The state of one process: its round-loop variables and its variables per round. -/
abbrev ProcessVariables (n : ℕ) : Type := Implementation.ProcessVariables n (RoundVariables n)

/-! ### The network's ghost -/

/-- The network's ghost for one round: the first gather's recorded core, the second gather's
recorded core, and the round's bound bit. No program reads it (D30). -/
abbrev Ghost (n : ℕ) : Type :=
  Option (AcceptedPairs n Bool) × Option (AcceptedPairs n (Option Bool)) × Option Bool

instance instInhabitedGhost (n : ℕ) : Inhabited (Ghost n) := ⟨(none, none, none)⟩

/-- The state of the network. -/
abbrev NetworkState (n : ℕ) : Type := Implementation.NetworkState n (Message n) (Ghost n)

/-! ### The messages of one tag -/

section TaggedMessages
variable {n : ℕ} {β : Type}

/-- The messages of one tag, recovered from a tagged sent family along a
partial untagging. -/
def messagesOf (f : Message n → Option β)
    (hf : ∀ a a' b, b ∈ f a → b ∈ f a' → a = a')
    (sent : Fin n → Finset (Message n)) : Fin n → Finset β :=
  fun q => (sent q).filterMap f hf

theorem mem_messagesOf {f : Message n → Option β}
    {hf : ∀ a a' b, b ∈ f a → b ∈ f a' → a = a'}
    {sent : Fin n → Finset (Message n)} {q : Fin n} {b : β} :
    b ∈ messagesOf f hf sent q ↔ ∃ m ∈ sent q, f m = some b :=
  Finset.mem_filterMap f

/-- The first gather's network state messages. -/
def firstGatherMessageOf : Message n → Option (Gather.Message n Bool)
  | .firstGather m => some m
  | _ => none

/-- The second gather's network state messages. -/
def secondGatherMessageOf : Message n → Option (Gather.Message n (Option Bool))
  | .secondGather m => some m
  | _ => none

theorem firstGatherMessageOf_inj : ∀ a a' (b : Gather.Message n Bool),
    b ∈ firstGatherMessageOf a → b ∈ firstGatherMessageOf a' → a = a' := by
  intro a a' b h h'
  cases a <;> cases a' <;> simp_all [firstGatherMessageOf]

theorem secondGatherMessageOf_inj : ∀ a a' (b : Gather.Message n (Option Bool)),
    b ∈ secondGatherMessageOf a → b ∈ secondGatherMessageOf a' → a = a' := by
  intro a a' b h h'
  cases a <;> cases a' <;> simp_all [secondGatherMessageOf]

end TaggedMessages
/-- The first gather's instance state of round `r`, computed from the network's
tagged sent sets and its corrupted set. The local states are the initial
ones: `Gather.coreOf` reads the network state alone
(`Gather.coreOf_networkState_only`). -/
def firstGatherOf (P : Parameters) (w : NetworkState P.n) (r : ℕ) :
    InstanceState P.n (Gather.BaseProcessVariables P.n Bool) (Gather.Message P.n Bool) :=
  (fun _ => LocalState.initial P.n _ (Gather.BaseProcessVariables.initial P.n Bool),
    ⟨messagesOf firstGatherMessageOf firstGatherMessageOf_inj (w.sent r), w.F⟩)

/-- The second gather's instance state of round `r`, computed from the network's
tagged sent sets and its corrupted set. -/
def secondGatherOf (P : Parameters) (w : NetworkState P.n) (r : ℕ) :
    InstanceState P.n (Gather.BaseProcessVariables P.n (Option Bool))
    (Gather.Message P.n (Option Bool)) :=
  (fun _ => LocalState.initial P.n _ (Gather.BaseProcessVariables.initial P.n (Option Bool)),
    ⟨messagesOf secondGatherMessageOf secondGatherMessageOf_inj (w.sent r), w.F⟩)

/-- The ghost write. A first gather's return records that gather's core, `Gather.coreOf` of the
round's first gather network state, where the ghost holds no first core; a second gather's return
records the second gather's core the same way; a graded-agreement return records the bound bit
`GBCA.boundOfCore P C` of the recorded first core `C` where the ghost holds no bit. Every other
label leaves the ghost where it stands, and each field is written once (D30). -/
noncomputable def ghostStep (P : Parameters) :
    ExtendedLabel P.n (Message P.n) (RoundEvent P.n) → NetworkState P.n → Ghost P.n → Ghost P.n
  | Sum.inr (.gbcaRoundEvent r _ (.firstGatherReturn _)), w, G =>
      (some (G.1.getD (Gather.coreOf P (firstGatherOf P w r))), G.2.1, G.2.2)
  | Sum.inr (.gbcaRoundEvent r _ (.secondGatherReturn _)), w, G =>
      (G.1, some (G.2.1.getD (Gather.coreOf P (secondGatherOf P w r))), G.2.2)
  | Sum.inl (.retG _ _ _), _, G => (G.1, G.2.1, G.2.2.or (G.1.map (GBCA.boundOfCore P)))
  | _, _, G => G

/-- The bit the ghost of a round holds, if any: its third field. It enables the network's
announcement `boundG`, and no other transition reads it (D29, D30). -/
def ghostBound {n : ℕ} (G : Ghost n) : Option Bool := G.2.2

@[simp] theorem ghostBound_apply {n : ℕ} (G : Ghost n) : ghostBound G = G.2.2 := rfl

/-! ### The round's transitions -/

/-- The transitions of process `j` in the round: the round's calls and returns, the two gather
instances, the `2n` Bracha instances beneath them, and the delivery. -/
inductive RoundStep (P : Parameters) (j : Fin P.n) :
    ProcessVariables P.n → ExtendedLabel P.n (Message P.n) (RoundEvent P.n) →
      PMF (ProcessVariables P.n) → Prop
  /-- The graded-agreement call at a round whose first gather holds no input: the round's first
  gather records the round loop's estimate as its input (AFW25's Algorithm 5, line 5). The call
  sends no message. -/
  | callG (c : RoundLoopVariables P.n) (p : RoundVariablesMap P.n) (r : ℕ) (b : Bool)
      (hh : c.corrupted = false)
      (hph : c.processVariables.phase = .toCallG) (hr : c.processVariables.round = r)
      (hterm : p.terminated = false)
      (hest : c.processVariables.estimate = some b)
      (hin : ((p.roundVariables r).firstGather.processVariables).input = none) :
      RoundStep P j (c, p) (Sum.inl (.callG r j b))
        (PMF.pure (c.setProcessVariables { c.processVariables with phase := .awaitG },
          p.setRoundVariables r
            { (p.roundVariables r) with
              firstGather := (p.roundVariables r).firstGather.setProcessVariables
                { ((p.roundVariables r).firstGather.processVariables) with input := some b } }))
  /-- The graded-agreement call at a round whose first gather holds an input: the round loop
  moves, and the round's variables stand where they are. `callG` and `callGLoop` are the two
  transitions of the call on the label `callG r j b`, as `input` and `inputLoop` are at the ABA
  call (D36). -/
  | callGLoop (c : RoundLoopVariables P.n) (p : RoundVariablesMap P.n) (r : ℕ) (b : Bool)
      (hh : c.corrupted = false)
      (hph : c.processVariables.phase = .toCallG) (hr : c.processVariables.round = r)
      (hest : c.processVariables.estimate = some b)
      (hin : ((p.roundVariables r).firstGather.processVariables).input ≠ none) :
      RoundStep P j (c, p) (Sum.inl (.callG r j b))
        (PMF.pure (c.setProcessVariables { c.processVariables with phase := .awaitG }, p))
  /-- The process calls the input-broadcast instance of the first gather with the payload its
  gather variables hold, and that instance records it as the leader's input (AFW25's Algorithm 5,
  line 6; LeslieBP's Algorithm 4, `BRB_id.call(m)`). The call sends no message. -/
  | firstGatherInputBroadcastCall (c : RoundLoopVariables P.n) (p : RoundVariablesMap P.n) (r : ℕ)
      (b : Bool)
      (hh : c.corrupted = false) (hterm : p.terminated = false)
      (hin : ((p.roundVariables r).firstGather.processVariables).input = some b)
      (hbin : (((p.roundVariables r).firstGatherInputBroadcasts j).processVariables).input = none) :
      RoundStep P j (c, p) (Sum.inr (.gbcaRoundEvent r j (.firstGatherInputBroadcastCall b)))
        (PMF.pure (c, p.setRoundVariables r
          { (p.roundVariables r) with
            firstGatherInputBroadcasts := Function.update (p.roundVariables
              r).firstGatherInputBroadcasts j
              (((p.roundVariables r).firstGatherInputBroadcasts j).setProcessVariables
                { (((p.roundVariables r).firstGatherInputBroadcasts j).processVariables) with
                  input := some b }) }))
  /-- The leader of the input-broadcast instance of the first gather multicasts `⟨INIT, b⟩` for
  the input that instance records (LeslieBP's Algorithm 6, `send ⟨init, m⟩ to all`). The multicast
  is the network's half. -/
  | firstGatherInputBroadcastInit (c : RoundLoopVariables P.n) (p : RoundVariablesMap P.n) (r : ℕ)
      (b : Bool)
      (hh : c.corrupted = false) (hterm : p.terminated = false)
      (hin : (((p.roundVariables r).firstGatherInputBroadcasts j).processVariables).input = some b)
      (hsend :
        (((p.roundVariables r).firstGatherInputBroadcasts j).processVariables).sentInit = none) :
      RoundStep P j (c, p) (Sum.inr (.gbcaSend r j (.firstGatherInputBroadcasts j (.init b))))
        (PMF.pure (c, p.setRoundVariables r
          { (p.roundVariables r) with
            firstGatherInputBroadcasts := Function.update (p.roundVariables
              r).firstGatherInputBroadcasts j
              (((p.roundVariables r).firstGatherInputBroadcasts j).setProcessVariables
                { (((p.roundVariables r).firstGatherInputBroadcasts j).processVariables) with
                  sentInit := some b }) }))
  /-- The first gather's `ECHO`: the process is called and its accepted pairs
  number at least `n − f`, the source blueprint's `|AP| ≥ n − f`. The payload is
  those pairs, `T_i ← AP_i` of AFW25's Algorithm 5, line 9. -/
  | firstGatherEcho (c : RoundLoopVariables P.n) (p : RoundVariablesMap P.n) (r : ℕ)
      (hh : c.corrupted = false) (hterm : p.terminated = false)
      (hin : ((p.roundVariables r).firstGather.processVariables).input ≠ none)
      (hcard : P.n - P.f ≤ (((p.roundVariables r).firstGather.processVariables).accepted).card)
      (hsend : ((p.roundVariables r).firstGather.processVariables).sentEcho = none) :
      RoundStep P j (c, p)
        (Sum.inr (.gbcaSend r j
          (.firstGather (.echo ((p.roundVariables r).firstGather.processVariables).accepted))))
        (PMF.pure (c, p.setRoundVariables r
          { (p.roundVariables r) with
            firstGather := (p.roundVariables r).firstGather.setProcessVariables
              { ((p.roundVariables r).firstGather.processVariables) with
                sentEcho := some (((p.roundVariables r).firstGather.processVariables).accepted) }
                  }))
  /-- The first gather's `VOTE`: `n − f` senders' `ECHO` payloads, each held
  here and contained in the vote payload, are delivered, and the process has
  multicast its own `ECHO`. The main thread of AFW25's Algorithm 5 sends `ECHO`
  before `VOTE`. -/
  | firstGatherVote (c : RoundLoopVariables P.n) (p : RoundVariablesMap P.n) (r : ℕ) (U :
      AcceptedPairs
    P.n Bool)
      (hh : c.corrupted = false) (hterm : p.terminated = false)
      (hin : ((p.roundVariables r).firstGather.processVariables).input ≠ none)
      (hech : ((p.roundVariables r).firstGather.processVariables).sentEcho ≠ none)
      (happ : Gather.approvedBy ((p.roundVariables r).firstGather.processVariables) U)
      (hQ : ∃ Q : Finset (Fin P.n), P.n - P.f ≤ Q.card ∧
        ∀ q ∈ Q, ∃ A, Gather.Message.echo A ∈ ((p.roundVariables r).firstGather.received q) ∧
          Gather.approvedBy ((p.roundVariables r).firstGather.processVariables) A ∧ A ⊆ U)
      (hsend : ((p.roundVariables r).firstGather.processVariables).sentVote = none) :
      RoundStep P j (c, p) (Sum.inr (.gbcaSend r j (.firstGather (.vote U))))
        (PMF.pure (c, p.setRoundVariables r
          { (p.roundVariables r) with
            firstGather := (p.roundVariables r).firstGather.setProcessVariables
              { ((p.roundVariables r).firstGather.processVariables) with sentVote := some U } }))
  /-- The first gather's `BIND`: `n − f` senders' `VOTE` payloads, each held here and contained in
  the bind payload, are delivered, the process has multicast its own `VOTE`, and it has not
  multicast a `BIND`. The main thread of AFW25's Algorithm 5 sends `VOTE` before `BIND`, and sends
  `BIND` to all processes once, at line 17. -/
  | firstGatherBind (c : RoundLoopVariables P.n) (p : RoundVariablesMap P.n) (r : ℕ)
      (U : AcceptedPairs P.n Bool)
      (hh : c.corrupted = false) (hterm : p.terminated = false)
      (hin : ((p.roundVariables r).firstGather.processVariables).input ≠ none)
      (hvot : ((p.roundVariables r).firstGather.processVariables).sentVote ≠ none)
      (happ : Gather.approvedBy ((p.roundVariables r).firstGather.processVariables) U)
      (hQ : ∃ Q : Finset (Fin P.n), P.n - P.f ≤ Q.card ∧
        ∀ q ∈ Q, ∃ W, Gather.Message.vote W ∈ ((p.roundVariables r).firstGather.received q) ∧
          Gather.approvedBy ((p.roundVariables r).firstGather.processVariables) W ∧ W ⊆ U)
      (hsend : ((p.roundVariables r).firstGather.processVariables).sentBind = none) :
      RoundStep P j (c, p) (Sum.inr (.gbcaSend r j (.firstGather (.bind U))))
        (PMF.pure (c, p.setRoundVariables r
          { (p.roundVariables r) with
            firstGather := (p.roundVariables r).firstGather.setProcessVariables
              { ((p.roundVariables r).firstGather.processVariables) with sentBind := some U } }))
  /-- The second gather's `ECHO`. -/
  | secondGatherEcho (c : RoundLoopVariables P.n) (p : RoundVariablesMap P.n) (r : ℕ)
      (hh : c.corrupted = false) (hterm : p.terminated = false)
      (hin : ((p.roundVariables r).secondGather.processVariables).input ≠ none)
      (hcard : P.n - P.f ≤ (((p.roundVariables r).secondGather.processVariables).accepted).card)
      (hsend : ((p.roundVariables r).secondGather.processVariables).sentEcho = none) :
      RoundStep P j (c, p)
        (Sum.inr (.gbcaSend r j
          (.secondGather (.echo ((p.roundVariables r).secondGather.processVariables).accepted))))
        (PMF.pure (c, p.setRoundVariables r
          { (p.roundVariables r) with
            secondGather := (p.roundVariables r).secondGather.setProcessVariables
              { ((p.roundVariables r).secondGather.processVariables) with
                sentEcho := some (((p.roundVariables r).secondGather.processVariables).accepted) }
                  }))
  /-- The second gather's `VOTE`. -/
  | secondGatherVote (c : RoundLoopVariables P.n) (p : RoundVariablesMap P.n) (r : ℕ)
      (U : AcceptedPairs P.n (Option Bool))
      (hh : c.corrupted = false) (hterm : p.terminated = false)
      (hin : ((p.roundVariables r).secondGather.processVariables).input ≠ none)
      (hech : ((p.roundVariables r).secondGather.processVariables).sentEcho ≠ none)
      (happ : Gather.approvedBy ((p.roundVariables r).secondGather.processVariables) U)
      (hQ : ∃ Q : Finset (Fin P.n), P.n - P.f ≤ Q.card ∧
        ∀ q ∈ Q, ∃ A, Gather.Message.echo A ∈ ((p.roundVariables r).secondGather.received q) ∧
          Gather.approvedBy ((p.roundVariables r).secondGather.processVariables) A ∧ A ⊆ U)
      (hsend : ((p.roundVariables r).secondGather.processVariables).sentVote = none) :
      RoundStep P j (c, p) (Sum.inr (.gbcaSend r j (.secondGather (.vote U))))
        (PMF.pure (c, p.setRoundVariables r
          { (p.roundVariables r) with
            secondGather := (p.roundVariables r).secondGather.setProcessVariables
              { ((p.roundVariables r).secondGather.processVariables) with sentVote := some U } }))
  /-- The second gather's `BIND`. -/
  | secondGatherBind (c : RoundLoopVariables P.n) (p : RoundVariablesMap P.n) (r : ℕ)
      (U : AcceptedPairs P.n (Option Bool))
      (hh : c.corrupted = false) (hterm : p.terminated = false)
      (hin : ((p.roundVariables r).secondGather.processVariables).input ≠ none)
      (hvot : ((p.roundVariables r).secondGather.processVariables).sentVote ≠ none)
      (happ : Gather.approvedBy ((p.roundVariables r).secondGather.processVariables) U)
      (hQ : ∃ Q : Finset (Fin P.n), P.n - P.f ≤ Q.card ∧
        ∀ q ∈ Q, ∃ W, Gather.Message.vote W ∈ ((p.roundVariables r).secondGather.received q) ∧
          Gather.approvedBy ((p.roundVariables r).secondGather.processVariables) W ∧ W ⊆ U)
      (hsend : ((p.roundVariables r).secondGather.processVariables).sentBind = none) :
      RoundStep P j (c, p) (Sum.inr (.gbcaSend r j (.secondGather (.bind U))))
        (PMF.pure (c, p.setRoundVariables r
          { (p.roundVariables r) with
            secondGather := (p.roundVariables r).secondGather.setProcessVariables
              { ((p.roundVariables r).secondGather.processVariables) with sentBind := some U } }))
  /-- The first gather returns, and the process records the candidate its returned entries
  determine (AFW25's Algorithm 4, lines 1 and 2; AFW25's Algorithm 5, line 20). The output's
  entries are held here, `n − f` senders' `BIND` payloads delivered here are sub-maps of it, and
  the returner has multicast its own `BIND`: the `BIND` multicast of AFW25's Algorithm 5, line 17,
  precedes the wait of line 18. -/
  | firstGatherReturn (c : RoundLoopVariables P.n) (p : RoundVariablesMap P.n) (r : ℕ)
      (g : Fin P.n → Option Bool)
      (hh : c.corrupted = false) (hterm : p.terminated = false)
      (hin : ((p.roundVariables r).firstGather.processVariables).input ≠ none)
      (hbind : ((p.roundVariables r).firstGather.processVariables).sentBind ≠ none)
      (hsubap : ∀ k x, g k = some x →
        Gather.holdsInputBroadcastReturn ((p.roundVariables r).firstGather.processVariables) k x)
      (hQ : ∃ Q : Finset (Fin P.n), P.n - P.f ≤ Q.card ∧
        ∀ q ∈ Q, ∃ U, Gather.Message.bind U ∈ (p.roundVariables r).firstGather.received q ∧
          AcceptedPairs.subMap U g)
      (hr1 : ((p.roundVariables r).firstGather.processVariables).returned = false)
      (hcand : (p.roundVariables r).candidate = none) :
      RoundStep P j (c, p)
        (Sum.inr (.gbcaRoundEvent r j (.firstGatherReturn (GBCA.candidate P g))))
        (PMF.pure (c, p.setRoundVariables r
          { (p.roundVariables r) with
            candidate := some (GBCA.candidate P g)
            firstGather := (p.roundVariables r).firstGather.setProcessVariables
              { ((p.roundVariables r).firstGather.processVariables) with returned := true } }))
  /-- The process calls the second gather with the recorded candidate, which that gather records
  (AFW25's Algorithm 4, line 4). The call sends no message. -/
  | secondGatherCall (c : RoundLoopVariables P.n) (p : RoundVariablesMap P.n) (r : ℕ) (x : Option
      Bool)
      (hh : c.corrupted = false) (hterm : p.terminated = false)
      (hcand : (p.roundVariables r).candidate = some x)
      (hin2 : ((p.roundVariables r).secondGather.processVariables).input = none) :
      RoundStep P j (c, p)
        (Sum.inr (.gbcaRoundEvent r j (.secondGatherCall x)))
        (PMF.pure (c, p.setRoundVariables r
          { (p.roundVariables r) with
            secondGather := (p.roundVariables r).secondGather.setProcessVariables
              { ((p.roundVariables r).secondGather.processVariables) with input := some x } }))
  /-- The process calls the input-broadcast instance of the second gather with the payload that
  gather's variables hold, and that instance records it as the leader's input (AFW25's Algorithm 5,
  line 6; LeslieBP's Algorithm 4, `BRB_id.call(m)`). The call sends no message. -/
  | secondGatherInputBroadcastCall (c : RoundLoopVariables P.n) (p : RoundVariablesMap P.n) (r : ℕ)
      (x : Option Bool)
      (hh : c.corrupted = false) (hterm : p.terminated = false)
      (hin2 : ((p.roundVariables r).secondGather.processVariables).input = some x)
      (hbin2 : (((p.roundVariables r).secondGatherInputBroadcasts j).processVariables).input = none)
        :
      RoundStep P j (c, p)
        (Sum.inr (.gbcaRoundEvent r j (.secondGatherInputBroadcastCall x)))
        (PMF.pure (c, p.setRoundVariables r
          { (p.roundVariables r) with
            secondGatherInputBroadcasts := Function.update (p.roundVariables
              r).secondGatherInputBroadcasts j
              (((p.roundVariables r).secondGatherInputBroadcasts j).setProcessVariables
                { (((p.roundVariables r).secondGatherInputBroadcasts j).processVariables) with
                  input := some x }) }))
  /-- The leader of the input-broadcast instance of the second gather multicasts `⟨INIT, x⟩` for
  the input that instance records (LeslieBP's Algorithm 6, `send ⟨init, m⟩ to all`). The multicast
  is the network's half. -/
  | secondGatherInputBroadcastInit (c : RoundLoopVariables P.n) (p : RoundVariablesMap P.n) (r : ℕ)
      (x : Option Bool)
      (hh : c.corrupted = false) (hterm : p.terminated = false)
      (hin : (((p.roundVariables r).secondGatherInputBroadcasts j).processVariables).input = some x)
      (hsend :
        (((p.roundVariables r).secondGatherInputBroadcasts j).processVariables).sentInit = none) :
      RoundStep P j (c, p) (Sum.inr (.gbcaSend r j (.secondGatherInputBroadcasts j (.init x))))
        (PMF.pure (c, p.setRoundVariables r
          { (p.roundVariables r) with
            secondGatherInputBroadcasts := Function.update (p.roundVariables
              r).secondGatherInputBroadcasts j
              (((p.roundVariables r).secondGatherInputBroadcasts j).setProcessVariables
                { (((p.roundVariables r).secondGatherInputBroadcasts j).processVariables) with
                  sentInit := some x }) }))
  /-- The second gather returns, and the process records the graded outcome its returned entries
  determine (AFW25's Algorithm 4, lines 5 to 8; AFW25's Algorithm 5, line 20). The returner has
  multicast its own `BIND`. -/
  | secondGatherReturn (c : RoundLoopVariables P.n) (p : RoundVariablesMap P.n) (r : ℕ)
      (g : Fin P.n → Option (Option Bool))
      (hh : c.corrupted = false) (hterm : p.terminated = false)
      (hin : ((p.roundVariables r).secondGather.processVariables).input ≠ none)
      (hbind : ((p.roundVariables r).secondGather.processVariables).sentBind ≠ none)
      (hsubap : ∀ k x, g k = some x →
        Gather.holdsInputBroadcastReturn ((p.roundVariables r).secondGather.processVariables) k x)
      (hQ : ∃ Q : Finset (Fin P.n), P.n - P.f ≤ Q.card ∧
        ∀ q ∈ Q, ∃ U, Gather.Message.bind U ∈ (p.roundVariables r).secondGather.received q ∧
          AcceptedPairs.subMap U g)
      (hr2 : ((p.roundVariables r).secondGather.processVariables).returned = false)
      (hout : (p.roundVariables r).output = none) :
      RoundStep P j (c, p)
        (Sum.inr (.gbcaRoundEvent r j (.secondGatherReturn (GBCA.gradeOf P g))))
        (PMF.pure (c, p.setRoundVariables r
          { (p.roundVariables r) with
            output := some (GBCA.gradeOf P g)
            secondGather := (p.roundVariables r).secondGather.setProcessVariables
              { ((p.roundVariables r).secondGather.processVariables) with returned := true } }))
  /-- The round returns the recorded graded outcome to the round loop (AFW25's Algorithm 4,
  line 3 and line 8). The outcome leaves the round's variables, which is what marks the round
  returned. The label carries the outcome alone, and the network announces the bound bit on
  `boundG` (D29). -/
  | retG (c : RoundLoopVariables P.n) (p : RoundVariablesMap P.n) (r : ℕ) (out : GBCAOutput)
      (hh : c.corrupted = false)
      (hph : c.processVariables.phase = .awaitG) (hr : c.processVariables.round = r)
      (hterm : p.terminated = false)
      (hout : (p.roundVariables r).output = some out)
      (hr2 : ((p.roundVariables r).secondGather.processVariables).returned = true) :
      RoundStep P j (c, p) (Sum.inl (.retG r j out))
        (PMF.pure (c.setProcessVariables { c.processVariables with
            estimate := out.estimate, lastGrade := some out, phase := .toCallW },
          p.setRoundVariables r { (p.roundVariables r) with output := none }))
  /-- `ECHO` in an input-broadcast instance of the first gather: the leader's
  `⟨INIT, m⟩` is delivered here, or a quorum of received `ECHO m` messages is, or `f + 1`
  received `VOTE m` messages are; no `ECHO` is out. -/
  | firstGatherInputBroadcastEcho (c : RoundLoopVariables P.n) (p : RoundVariablesMap P.n) (r : ℕ)
      (i : Fin P.n) (m : Bool) (hh : c.corrupted = false) (hterm : p.terminated = false)
      (hrecv : BRB.Message.init m ∈ ((p.roundVariables r).firstGatherInputBroadcasts i).received i ∨
        P.receivedEchoQuorum ≤ ((p.roundVariables r).firstGatherInputBroadcasts i).receivedCount
          (.echo
          m) ∨
        P.f + 1 ≤ ((p.roundVariables r).firstGatherInputBroadcasts i).receivedCount (.vote m))
      (hsend : (((p.roundVariables r).firstGatherInputBroadcasts i).processVariables).sentEcho =
        none) :
      RoundStep P j (c, p) (Sum.inr (.gbcaSend r j (.firstGatherInputBroadcasts i (.echo m))))
        (PMF.pure (c, p.setRoundVariables r
          { (p.roundVariables r) with
            firstGatherInputBroadcasts := Function.update (p.roundVariables
              r).firstGatherInputBroadcasts i
              (((p.roundVariables r).firstGatherInputBroadcasts i).setProcessVariables
                { (((p.roundVariables r).firstGatherInputBroadcasts i).processVariables) with
                  sentEcho := some m
                  }) }))
  /-- `VOTE` on a quorum of received `ECHO m` messages in an input-broadcast instance of the
  first gather. -/
  | firstGatherInputBroadcastVoteQuorum (c : RoundLoopVariables P.n) (p : RoundVariablesMap P.n) (r
      : ℕ)
    (i : Fin P.n)
      (m : Bool) (hh : c.corrupted = false) (hterm : p.terminated = false)
      (hcnt : P.receivedEchoQuorum ≤ ((p.roundVariables r).firstGatherInputBroadcasts
        i).receivedCount
        (.echo
        m))
      (hsend : (((p.roundVariables r).firstGatherInputBroadcasts i).processVariables).sentVote =
        none) :
      RoundStep P j (c, p) (Sum.inr (.gbcaSend r j (.firstGatherInputBroadcasts i (.vote m))))
        (PMF.pure (c, p.setRoundVariables r
          { (p.roundVariables r) with
            firstGatherInputBroadcasts := Function.update (p.roundVariables
              r).firstGatherInputBroadcasts i
              (((p.roundVariables r).firstGatherInputBroadcasts i).setProcessVariables
                { (((p.roundVariables r).firstGatherInputBroadcasts i).processVariables) with
                  sentVote := some m
                  }) }))
  /-- `VOTE` by amplification, on `f + 1` received `VOTE` messages. -/
  | firstGatherInputBroadcastVoteAmplification (c : RoundLoopVariables P.n) (p : RoundVariablesMap
      P.n) (r
    : ℕ) (i : Fin P.n)
      (m : Bool) (hh : c.corrupted = false) (hterm : p.terminated = false)
      (hcnt : P.f + 1 ≤ ((p.roundVariables r).firstGatherInputBroadcasts i).receivedCount (.vote m))
      (hsend : (((p.roundVariables r).firstGatherInputBroadcasts i).processVariables).sentVote =
        none) :
      RoundStep P j (c, p) (Sum.inr (.gbcaSend r j (.firstGatherInputBroadcasts i (.vote m))))
        (PMF.pure (c, p.setRoundVariables r
          { (p.roundVariables r) with
            firstGatherInputBroadcasts := Function.update (p.roundVariables
              r).firstGatherInputBroadcasts i
              (((p.roundVariables r).firstGatherInputBroadcasts i).setProcessVariables
                { (((p.roundVariables r).firstGatherInputBroadcasts i).processVariables) with
                  sentVote := some m
                  }) }))
  /-- The instance broadcasting `i`'s input in the first gather returns here: a `2f + 1` `VOTE`
  quorum stands in that instance, which has not returned here yet, and the gather variables file
  the value it returned. AFW25's Algorithm 5, lines 1 and 2; LeslieBP's Algorithm 4,
  `upon BRB_k.return(m')`. -/
  | firstGatherInputBroadcastReturn (c : RoundLoopVariables P.n) (p : RoundVariablesMap P.n)
      (r : ℕ) (i : Fin P.n) (v : Bool)
      (hh : c.corrupted = false) (hterm : p.terminated = false)
      (hcnt : 2 * P.f + 1 ≤
        ((p.roundVariables r).firstGatherInputBroadcasts i).receivedCount (.vote v))
      (hret : (((p.roundVariables r).firstGatherInputBroadcasts i).processVariables).returned =
        false) :
      RoundStep P j (c, p) (Sum.inr (.gbcaRoundEvent r j (.firstGatherInputBroadcastReturn i v)))
        (PMF.pure (c, p.setRoundVariables r
          { (p.roundVariables r) with
            firstGather := (p.roundVariables r).firstGather.setProcessVariables
              { ((p.roundVariables r).firstGather.processVariables) with
                inputBroadcastReturned := Function.update
                  ((p.roundVariables r).firstGather.processVariables).inputBroadcastReturned i (some
                    v) }
            firstGatherInputBroadcasts := Function.update
              (p.roundVariables r).firstGatherInputBroadcasts i
              ((((p.roundVariables r).firstGatherInputBroadcasts i).setProcessVariables
                { (((p.roundVariables r).firstGatherInputBroadcasts i).processVariables) with
                  returned := true })) }))
  /-- `ECHO` in an input-broadcast instance of the second gather. -/
  | secondGatherInputBroadcastEcho (c : RoundLoopVariables P.n) (p : RoundVariablesMap P.n) (r : ℕ)
      (i : Fin P.n) (m : Option Bool) (hh : c.corrupted = false) (hterm : p.terminated = false)
      (hrecv : BRB.Message.init m ∈ ((p.roundVariables r).secondGatherInputBroadcasts i).received i
        ∨
        P.receivedEchoQuorum ≤ ((p.roundVariables r).secondGatherInputBroadcasts i).receivedCount
          (.echo
          m) ∨
        P.f + 1 ≤ ((p.roundVariables r).secondGatherInputBroadcasts i).receivedCount (.vote m))
      (hsend : (((p.roundVariables r).secondGatherInputBroadcasts i).processVariables).sentEcho =
        none) :
      RoundStep P j (c, p) (Sum.inr (.gbcaSend r j (.secondGatherInputBroadcasts i (.echo m))))
        (PMF.pure (c, p.setRoundVariables r
          { (p.roundVariables r) with
            secondGatherInputBroadcasts := Function.update (p.roundVariables
              r).secondGatherInputBroadcasts i
              (((p.roundVariables r).secondGatherInputBroadcasts i).setProcessVariables
                { (((p.roundVariables r).secondGatherInputBroadcasts i).processVariables) with
                  sentEcho :=
                    some m }) }))
  /-- `VOTE` on a quorum of received `ECHO m` messages in an input-broadcast instance of the
  second gather. -/
  | secondGatherInputBroadcastVoteQuorum (c : RoundLoopVariables P.n) (p : RoundVariablesMap P.n) (r
      : ℕ)
    (i : Fin P.n)
      (m : Option Bool) (hh : c.corrupted = false) (hterm : p.terminated = false)
      (hcnt : P.receivedEchoQuorum ≤ ((p.roundVariables r).secondGatherInputBroadcasts
        i).receivedCount
        (.echo
        m))
      (hsend : (((p.roundVariables r).secondGatherInputBroadcasts i).processVariables).sentVote =
        none) :
      RoundStep P j (c, p) (Sum.inr (.gbcaSend r j (.secondGatherInputBroadcasts i (.vote m))))
        (PMF.pure (c, p.setRoundVariables r
          { (p.roundVariables r) with
            secondGatherInputBroadcasts := Function.update (p.roundVariables
              r).secondGatherInputBroadcasts i
              (((p.roundVariables r).secondGatherInputBroadcasts i).setProcessVariables
                { (((p.roundVariables r).secondGatherInputBroadcasts i).processVariables) with
                  sentVote :=
                    some m }) }))
  /-- `VOTE` by amplification in an input-broadcast instance of the second
  gather. -/
  | secondGatherInputBroadcastVoteAmplification (c : RoundLoopVariables P.n) (p : RoundVariablesMap
      P.n)
    (r : ℕ) (i : Fin P.n)
      (m : Option Bool) (hh : c.corrupted = false) (hterm : p.terminated = false)
      (hcnt : P.f + 1 ≤ ((p.roundVariables r).secondGatherInputBroadcasts i).receivedCount (.vote
        m))
      (hsend : (((p.roundVariables r).secondGatherInputBroadcasts i).processVariables).sentVote =
        none) :
      RoundStep P j (c, p) (Sum.inr (.gbcaSend r j (.secondGatherInputBroadcasts i (.vote m))))
        (PMF.pure (c, p.setRoundVariables r
          { (p.roundVariables r) with
            secondGatherInputBroadcasts := Function.update (p.roundVariables
              r).secondGatherInputBroadcasts i
              (((p.roundVariables r).secondGatherInputBroadcasts i).setProcessVariables
                { (((p.roundVariables r).secondGatherInputBroadcasts i).processVariables) with
                  sentVote :=
                    some m }) }))
  /-- The instance broadcasting `i`'s input in the second gather returns here. AFW25's Algorithm 5,
  lines 1 and 2. -/
  | secondGatherInputBroadcastReturn (c : RoundLoopVariables P.n) (p : RoundVariablesMap P.n)
      (r : ℕ) (i : Fin P.n) (v : Option Bool)
      (hh : c.corrupted = false) (hterm : p.terminated = false)
      (hcnt : 2 * P.f + 1 ≤
        ((p.roundVariables r).secondGatherInputBroadcasts i).receivedCount (.vote v))
      (hret : (((p.roundVariables r).secondGatherInputBroadcasts i).processVariables).returned =
        false) :
      RoundStep P j (c, p) (Sum.inr (.gbcaRoundEvent r j (.secondGatherInputBroadcastReturn i v)))
        (PMF.pure (c, p.setRoundVariables r
          { (p.roundVariables r) with
            secondGather := (p.roundVariables r).secondGather.setProcessVariables
              { ((p.roundVariables r).secondGather.processVariables) with
                inputBroadcastReturned := Function.update
                  ((p.roundVariables r).secondGather.processVariables).inputBroadcastReturned i
                    (some v) }
            secondGatherInputBroadcasts := Function.update
              (p.roundVariables r).secondGatherInputBroadcasts i
              ((((p.roundVariables r).secondGatherInputBroadcasts i).setProcessVariables
                { (((p.roundVariables r).secondGatherInputBroadcasts i).processVariables) with
                  returned := true })) }))
  /-- Delivery, receiver's half: file the message in the local state of the network state its
  tag names. Authenticity is the network's conjunct. -/
  | gbcaDeliverReceive (c : RoundLoopVariables P.n) (p : RoundVariablesMap P.n) (r : ℕ) (k : Fin
      P.n)
      (m : Message P.n) (hh : c.corrupted = false) (hterm : p.terminated = false) :
      RoundStep P j (c, p) (Sum.inr (.gbcaDeliver r j k m))
        (PMF.pure (c, p.deliverTo r k m))
  /-- Delivery at a terminated program: the program takes the message, and its variables stand
  where they are (D22). `gbcaDeliverReceive` and `deliverLoop` take every round delivery
  addressed to `j` at an unreplaced program. -/
  | deliverLoop (c : RoundLoopVariables P.n) (p : RoundVariablesMap P.n) (r : ℕ) (k : Fin P.n)
      (m : Message P.n) (hh : c.corrupted = false) (hterm : p.terminated = true) :
      RoundStep P j (c, p) (Sum.inr (.gbcaDeliver r j k m)) (PMF.pure (c, p))

/-- The transitions above meet the implementation's conditions: each carries a label of
`roundOwn j`, each fires only at an unreplaced program, each is Dirac, and
`gbcaDeliverReceive` at a program that has not terminated and `deliverLoop` at a terminated one
take every round delivery addressed to `j` at an unreplaced program. -/
instance instIsRoundStep (P : Parameters) :
    IsRoundStep P (Message P.n) (RoundEvent P.n) (RoundVariables P.n) (RoundStep P) where
  own h := by
    cases h <;> rfl
  correct h := by
    cases h <;> assumption
  dirac h := by
    cases h <;> exact ⟨_, rfl⟩
  deliveryEnabled := by
    intro j q r k m hh
    obtain ⟨c, p⟩ := q
    cases hterm : p.terminated
    · exact ⟨_, RoundStep.gbcaDeliverReceive c p r k m hh hterm⟩
    · exact ⟨_, RoundStep.deliverLoop c p r k m hh hterm⟩

/-! ### The transposed variables write one local state at a time

A tagged delivery reaches exactly the local state its tag names and leaves every other local state
of the variables where it stands. These are the facts the substitution into the composed system
rests on, the composed system writing the same local state through its instance-major indexing. -/

section Transposition

variable {n : ℕ}

example (s : RoundVariables n) (k i : Fin n) (m : BRB.Message Bool) :
    ((s.deliverTo k (.firstGatherInputBroadcasts i m)).firstGatherInputBroadcasts i).received k
      = insert m ((s.firstGatherInputBroadcasts i).received k) := by
  simp [RoundVariables.deliverTo, LocalState.deliverTo]

example (s : RoundVariables n) (k i i' : Fin n) (m : BRB.Message Bool) (h : i' ≠ i) :
    (s.deliverTo k (.firstGatherInputBroadcasts i m)).firstGatherInputBroadcasts i' =
      s.firstGatherInputBroadcasts i' := by
  simp [RoundVariables.deliverTo, Function.update_of_ne h]

example (s : RoundVariables n) (k i : Fin n) (m : BRB.Message Bool) :
    (s.deliverTo k (.firstGatherInputBroadcasts i m)).firstGather = s.firstGather := by
  simp [RoundVariables.deliverTo]

example (s : RoundVariables n) (k : Fin n) (m : Gather.Message n Bool) :
    (s.deliverTo k (.firstGather m)).firstGather.received k = insert m (s.firstGather.received k) :=
      by
  simp [RoundVariables.deliverTo, LocalState.deliverTo]

example (s : RoundVariables n) (k : Fin n) (m : Gather.Message n Bool) (i : Fin n) :
    (s.deliverTo k (.firstGather m)).firstGatherInputBroadcasts i = s.firstGatherInputBroadcasts i
      := by
  simp [RoundVariables.deliverTo]

example (P : Parameters) (p : RoundVariablesMap P.n) (r : ℕ) (sr : RoundVariables P.n) :
    (p.setRoundVariables r sr).roundVariables r = sr := by simp

end Transposition

/-! ### The protocol -/

/-- The step relation of the program of process `j`. -/
abbrev ProgramStep (P : Parameters) (j : Fin P.n) :
    ProcessVariables P.n → ExtendedLabel P.n (Message P.n) (RoundEvent P.n) →
      PMF (ProcessVariables P.n) → Prop :=
  Implementation.ProgramStep P (Message P.n) (RoundEvent P.n) (RoundVariables P.n) (RoundStep P) j

/-- The step relation of the network. -/
abbrev NetworkStep (P : Parameters) :
    NetworkState P.n → ExtendedLabel P.n (Message P.n) (RoundEvent P.n) →
      PMF (NetworkState P.n) → Prop :=
  Implementation.NetworkStep P (Message P.n) (RoundEvent P.n) (Ghost P.n) (ghostStep P) ghostBound

/-- The state of the gather-based protocol: the process family, the network and the instance
family of the common coin. -/
abbrev ProtocolState (P : Parameters) : Type :=
  Implementation.State P (Message P.n) (RoundVariables P.n) (Ghost P.n)

/-- The three components in parallel, over the extended alphabet. -/
noncomputable def protocolExtended (P : Parameters) :
    System (ProtocolState P) (Implementation.ExtendedLabel P.n (Message P.n) (RoundEvent P.n)) :=
  Implementation.systemExtended P (Message P.n) (RoundEvent P.n) (RoundVariables P.n) (Ghost P.n)
    (RoundStep P) (ghostStep P) ghostBound

/-- The gather-based protocol group: the labels the components synchronise on
hidden, the result read back over `Label n`. -/
noncomputable def protocolHidden (P : Parameters) : System (ProtocolState P) (Label P.n) :=
  Implementation.systemHidden P (Message P.n) (RoundEvent P.n) (RoundVariables P.n) (Ghost P.n)
    (RoundStep P) (ghostStep P) ghostBound

/-- **The gather-based protocol**: the group with the sub-protocol API
hidden. -/
noncomputable def protocol (P : Parameters) : System (ProtocolState P) (Label P.n) :=
  Implementation.system P (Message P.n) (RoundEvent P.n) (RoundVariables P.n) (Ghost P.n)
    (RoundStep P) (ghostStep P) ghostBound

end AFW

end ABA
end PLTS
