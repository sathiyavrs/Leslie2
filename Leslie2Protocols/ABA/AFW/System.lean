/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sathiya / Claude
-/

import Leslie2Protocols.ABA.Implementation.System
import Leslie2Protocols.ABA.GBCA.AFW.Counting
import Leslie2Protocols.ABA.Gather.Components
import Leslie2Protocols.ABA.ReliableBroadcast.Bracha.MessagesAndRecords

/-!
# The gather-based protocol as it runs

The gather-based graded agreement, read as a protocol rather than as a composition: `n` programs
beside one network and the coin oracle. This is the implementation of
`ABA/Implementation/System.lean` at the gather-based implementation, as
`ABA/ABDY/System.lean` is that implementation at ABDY22's, and it supplies the same
three things — a round message type, a round record, and the implementation's transitions. It sits
in the namespace `AFW`, after Attiya, Flam and Welch, and so `AFW.protocol` is what `ABDY.protocol`
is at ABDY22's.

## One sent for every network state

A round of the gather-based implementation carries `4n + 2` network states:
one for each of the two gather instances, and one for each of the `4n` Bracha
instances — `n` carrying the inputs and `n` carrying the `BIND` payloads, in
each of the two gathers. The adversary here holds one sent family per round
instead, over the tagged message type `Message`, whose tag names the network state a
message belongs to and, for a Bracha message, the instance it belongs to. The
sent index stays the sender, so a threshold still counts distinct senders
(D5).

## The record of one process

A process's data is scattered across those instances: `j` holds its own local state in
each of the `4n + 2` of them, and the composed system indexes those local states by
instance and then by process. A program must hold its own data and no one
else's, so `RoundRecord` holds them the other way round — `j`'s local state in each
gather instance, and `j`'s local state in each of the `n` instances of each Bracha
family. Every guard of the gather-based implementation reads the acting
process's own local states and the network states, and the two transitions that read a network
state are the adversary's delivery and its Byzantine injection, so the transposition
loses nothing.

## The transitions

The round's transitions are the transitions of the programs of `GBCA.ByAFW.roundOverBracha`,
written over the tagged message type: the transitions of its graded-agreement programs
(`GBCA.ByAFW.ProgramStep`), of its gather programs (`Gather.ProgramStep`) and of the Bracha
programs beneath them (`BRB.ProgramStep`). Each is the process's half of a step whose network half
is a transition of the adversary. A send writes the sender's own record and the network records the
message; a delivery files the message in the receiver's own local state, dispatched on the tag.
One transition is fused (D28): a gather's call broadcasts the caller's input through that
gather's own input-broadcast instance, at the graded-agreement call for the first gather and at
`secondGatherCall` for the second.

Every call and every return of a sub-protocol is a transition of its own. The first gather's
return, the second gather's call, the second gather's return, the round's own return and the return
of each of the `4n` broadcast instances are separate transitions, and a return writes what it
returned in the caller's record. The round record therefore holds the two gather local states over
`Gather.ProcessRecord`, which carries what each instance returned, and the two intermediate phases
`candidate` and `output`. A gather guard reads that record, as the guard of the composed gather
program does: `Gather.ProcessRecord.accepted` is the `ECHO` payload `AP_i` of AFW25's Algorithm 5,
line 9, and `Gather.approvedBy`, `Gather.holdsInputBroadcastReturn` and
`Gather.holdsBindBroadcastReturn` are the remaining guards.

## The network's ghost

The record the adversary holds for round `r` is `AFW.Ghost`: the first gather's recorded core, the
second gather's recorded core, and the round's bound bit, each written once. `AFW.ghostStep` writes
it. The first gather's return — the label `gbcaRoundEvent r j (firstGatherReturn _)` — writes the
first core at `Gather.coreOf` of the round's first gather network state and the bound bit at
`GBCA.boundOfCore` of that core; the second gather's return writes the second core the same way,
and so does a Byzantine graded return, at a process whose program has been replaced. Every other
label leaves the record where it stands.

The network state `Gather.coreOf` is read on is `AFW.firstGatherOf`, the first
gather's messages out of the adversary's tagged sent sets beside its corrupted set,
and `AFW.secondGatherOf` is the second's. `Gather.coreOf` reads the sent sets and the
corrupted set alone (`Gather.coreOf_networkState_only`), which is what lets the
adversary compute the core from its own state.

`AFW.ghostOutput` reads the bit back, and `AFW.announcedBound`, the guard of the two
graded-agreement return transitions, is the equation between the bit their label carries and it.
`AFW.ghostOutput` is total: where the ghost holds no bit it computes one from the first gather's
core, and on a reachable state the returner's own first gather return has already written the
bit. -/

namespace PLTS
namespace ABA
namespace AFW

open Implementation Gather

/-! ### The tagged message type -/

/-- A round's messages: the two gather network states and the `4n` Bracha network states,
tagged by the network state they belong to. A Bracha tag carries the instance, whose
index is its leader. -/
inductive Message (n : ℕ) : Type
  /-- A message of the first gather's network state. -/
  | firstGather (m : Gather.Message n Bool)
  /-- A message of the second gather's network state. -/
  | secondGather (m : Gather.Message n (Option Bool))
  /-- A message of the input-broadcast instance `k` of the first gather. -/
  | firstGatherInputBroadcasts (k : Fin n) (m : BRB.Message Bool)
  /-- A message of the bind-broadcast instance `k` of the first gather. -/
  | firstGatherBindBroadcasts (k : Fin n) (m : BRB.Message (AcceptedPairs n Bool))
  /-- A message of the input-broadcast instance `k` of the second gather. -/
  | secondGatherInputBroadcasts (k : Fin n) (m : BRB.Message (Option Bool))
  /-- A message of the bind-broadcast instance `k` of the second gather. -/
  | secondGatherBindBroadcasts (k : Fin n) (m : BRB.Message (AcceptedPairs n (Option Bool)))
  deriving DecidableEq

/-! ### The round's own calls and returns -/

/-- The calls and returns at the boundaries between a round's program and its sub-protocol
instances, each carrying the value the boundary hands over, as `upon X.return(v)` of LeslieBP's
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
  /-- The instance broadcasting `k`'s input in the first gather returns `v` (AFW25, Algorithm 5,
  lines 1 and 2). -/
  | firstGatherInputBroadcastReturn (k : Fin n) (v : Bool)
  /-- The instance broadcasting `q`'s `BIND` payload in the first gather returns `U` (AFW25,
  Algorithm 5, line 18). -/
  | firstGatherBindBroadcastReturn (q : Fin n) (U : AcceptedPairs n Bool)
  /-- The instance broadcasting `k`'s input in the second gather returns `v` (AFW25, Algorithm 5,
  lines 1 and 2). -/
  | secondGatherInputBroadcastReturn (k : Fin n) (v : Option Bool)
  /-- The instance broadcasting `q`'s `BIND` payload in the second gather returns `U` (AFW25,
  Algorithm 5, line 18). -/
  | secondGatherBindBroadcastReturn (q : Fin n) (U : AcceptedPairs n (Option Bool))
  deriving DecidableEq

/-! ### The record of one process in one round -/

/-- One process's data in one round, held by instance: its local state in each gather
instance, and its local state in each of the `n` instances of each broadcast family.
This is the composed system's instance-major indexing transposed. -/
structure RoundRecord (n : ℕ) : Type where
  /-- The candidate the first gather's return determines here (AFW25, Algorithm 4, line 2). -/
  candidate : Option (Option Bool)
  /-- The graded outcome the second gather's return determines here (AFW25, Algorithm 4,
  line 7). -/
  output : Option GBCAOutput
  /-- The process's local state in the first gather instance. -/
  firstGather : LocalState n (Gather.ProcessRecord n Bool) (Gather.Message n Bool)
  /-- The process's local state in the second gather instance. -/
  secondGather :
    LocalState n (Gather.ProcessRecord n (Option Bool)) (Gather.Message n (Option Bool))
  /-- The process's local state in each input-broadcast instance of the first
  gather. -/
  firstGatherInputBroadcasts : ∀ _ : Fin n, LocalState n (BRB.ProcessRecord Bool) (BRB.Message Bool)
  /-- The process's local state in each bind-broadcast instance of the first
  gather. -/
  firstGatherBindBroadcasts : ∀ _ : Fin n,
    LocalState n (BRB.ProcessRecord (AcceptedPairs n Bool)) (BRB.Message (AcceptedPairs n Bool))
  /-- The process's local state in each input-broadcast instance of the second
  gather. -/
  secondGatherInputBroadcasts : ∀ _ : Fin n,
    LocalState n (BRB.ProcessRecord (Option Bool)) (BRB.Message (Option Bool))
  /-- The process's local state in each bind-broadcast instance of the second
  gather. -/
  secondGatherBindBroadcasts : ∀ _ : Fin n,
    LocalState n (BRB.ProcessRecord (AcceptedPairs n (Option Bool))) (BRB.Message (AcceptedPairs n
      (Option Bool)))

namespace RoundRecord

variable {n : ℕ}

/-- The initial record: every local state empty over the initial local record. -/
def initial (n : ℕ) : RoundRecord n where
  candidate := none
  output := none
  firstGather := LocalState.initial n _ (Gather.ProcessRecord.initial n Bool)
  secondGather := LocalState.initial n _ (Gather.ProcessRecord.initial n (Option Bool))
  firstGatherInputBroadcasts := fun _ => LocalState.initial n _ (BRB.ProcessRecord.initial Bool)
  firstGatherBindBroadcasts := fun _ => LocalState.initial n _ (BRB.ProcessRecord.initial
    (AcceptedPairs n Bool))
  secondGatherInputBroadcasts := fun _ => LocalState.initial n _ (BRB.ProcessRecord.initial (Option
    Bool))
  secondGatherBindBroadcasts := fun _ => LocalState.initial n _ (BRB.ProcessRecord.initial
    (AcceptedPairs n (Option Bool)))

/-- File a delivered message in the local state of the network state its tag names. -/
def deliverTo (s : RoundRecord n) (k : Fin n) : Message n → RoundRecord n
  | .firstGather m => { s with firstGather := s.firstGather.deliverTo k m }
  | .secondGather m => { s with secondGather := s.secondGather.deliverTo k m }
  | .firstGatherInputBroadcasts i m =>
      { s with
        firstGatherInputBroadcasts :=
          Function.update s.firstGatherInputBroadcasts i ((s.firstGatherInputBroadcasts i).deliverTo
            k m) }
  | .firstGatherBindBroadcasts i m =>
      { s with
        firstGatherBindBroadcasts :=
          Function.update s.firstGatherBindBroadcasts i ((s.firstGatherBindBroadcasts i).deliverTo k
            m) }
  | .secondGatherInputBroadcasts i m =>
      { s with
        secondGatherInputBroadcasts :=
          Function.update s.secondGatherInputBroadcasts i ((s.secondGatherInputBroadcasts
            i).deliverTo k m) }
  | .secondGatherBindBroadcasts i m =>
      { s with
        secondGatherBindBroadcasts :=
          Function.update s.secondGatherBindBroadcasts i ((s.secondGatherBindBroadcasts i).deliverTo
            k m) }

end RoundRecord

/-- The gather-based round record, as the implementation consumes it. -/
instance instIsRoundRecord (n : ℕ) : IsRoundRecord n (Message n) (RoundRecord n) where
  initial := RoundRecord.initial n
  deliverTo s k m := s.deliverTo k m

@[simp] theorem roundRecord_initial (n : ℕ) :
    (IsRoundRecord.initial : RoundRecord n) = RoundRecord.initial n := rfl

@[simp] theorem roundRecord_deliverTo (n : ℕ) (s : RoundRecord n) (k : Fin n)
    (m : Message n) : (IsRoundRecord.deliverTo s k m : RoundRecord n) = s.deliverTo k m := rfl

/-- The round records of one process: the round records it holds, and whether it has terminated
(D22). -/
abbrev RoundRecordMap (n : ℕ) : Type := Implementation.RoundRecordMap (RoundRecord n)

/-- The state of one process: its round-loop record and its round records. -/
abbrev ProcessRecord (n : ℕ) : Type := Implementation.ProcessRecord n (RoundRecord n)

/-! ### The network's ghost -/

/-- The adversary's record for one round: the first gather's recorded core, the
second gather's recorded core, and the round's bound bit. No program reads
it. -/
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
/-- The first gather's instance state of round `r`, read off the adversary's
tagged sent sets and its corrupted set. The local states are the initial
ones: `Gather.coreOf` reads the network state alone
(`Gather.coreOf_networkState_only`). -/
def firstGatherOf (P : Parameters) (w : NetworkState P.n) (r : ℕ) :
    InstanceState P.n (Gather.BaseProcessRecord P.n Bool) (Gather.Message P.n Bool) :=
  (fun _ => LocalState.initial P.n _ (Gather.BaseProcessRecord.initial P.n Bool),
    ⟨messagesOf firstGatherMessageOf firstGatherMessageOf_inj (w.sent r), w.F⟩)

/-- The second gather's instance state of round `r`, read off the adversary's
tagged sent sets and its corrupted set. -/
def secondGatherOf (P : Parameters) (w : NetworkState P.n) (r : ℕ) :
    InstanceState P.n (Gather.BaseProcessRecord P.n (Option Bool))
    (Gather.Message P.n (Option Bool)) :=
  (fun _ => LocalState.initial P.n _ (Gather.BaseProcessRecord.initial P.n (Option Bool)),
    ⟨messagesOf secondGatherMessageOf secondGatherMessageOf_inj (w.sent r), w.F⟩)

/-- The ghost write: the first gather's return writes that gather's core and the round's bound
bit, the second gather's return writes the second gather's core, and a Byzantine graded return
writes it at a process whose program has been replaced. Every other label leaves the record where
it stands, and each field is written once. -/
noncomputable def ghostStep (P : Parameters) :
    ExtendedLabel P.n (Message P.n) (RoundEvent P.n) → NetworkState P.n → Ghost P.n → Ghost P.n
  | Sum.inr (.gbcaRoundEvent r _ (.firstGatherReturn _)), w, G =>
      (some (G.1.getD (Gather.coreOf P (firstGatherOf P w r))), G.2.1,
        some (G.2.2.getD (GBCA.boundOfCore P
          (G.1.getD (Gather.coreOf P (firstGatherOf P w r))))))
  | Sum.inr (.gbcaRoundEvent r _ (.secondGatherReturn _)), w, G =>
      (G.1, some (G.2.1.getD (Gather.coreOf P (secondGatherOf P w r))), G.2.2)
  | Sum.inr (.byzantineRetG r _ _ _), w, G =>
      (G.1, some (G.2.1.getD (Gather.coreOf P (secondGatherOf P w r))), G.2.2)
  | _, _, G => G

/-- The bound bit the round's graded returns announce: the one the ghost
holds, and the bit of the first gather's core where it holds none. -/
noncomputable def ghostOutput (P : Parameters) (w : NetworkState P.n) (r : ℕ) (_id : Fin P.n)
    (_out : GBCAOutput) : Bool :=
  ((w.ghostRecord r).2.2).getD
    (GBCA.boundOfCore P ((w.ghostRecord r).1.getD (Gather.coreOf P (firstGatherOf P w r))))

/-- The bit the network announces on a return: `AFW.ghostOutput` of the
round, and no other. This is the relation the implementation's `ghostOutput`
parameter takes at this instantiation. It is reducible, so the guard of the two
return transitions is the equation itself. -/
noncomputable abbrev announcedBound (P : Parameters) (w : NetworkState P.n) (r : ℕ)
    (id : Fin P.n) (out : GBCAOutput) (bnd : Bool) : Prop :=
  bnd = ghostOutput P w r id out

/-! ### The round's transitions -/

/-- The transitions of process `j` in the round: the round's calls and returns, the two gather
instances, the `4n` Bracha instances beneath them, and the delivery. -/
inductive RoundStep (P : Parameters) (j : Fin P.n) :
    ProcessRecord P.n → ExtendedLabel P.n (Message P.n) (RoundEvent P.n) →
      PMF (ProcessRecord P.n) → Prop
  /-- The graded-agreement call: the round loop hands its estimate to the
  round's first gather, which records it and broadcasts it through the
  process's own input-broadcast instance. The `⟨INIT, b⟩` multicast is the
  network's half. -/
  | callG (c : RoundLoopRecord P.n) (p : RoundRecordMap P.n) (r : ℕ) (b : Bool)
      (hh : c.corrupted = false)
      (hph : c.process.phase = .toCallG) (hr : c.process.round = r)
      (hterm : p.terminated = false)
      (hest : c.process.estimate = some b)
      (hin : ((p.roundRecord r).firstGather.process).input = none)
      (hbin : (((p.roundRecord r).firstGatherInputBroadcasts j).process).input = none) :
      RoundStep P j (c, p) (Sum.inl (.callG r j b))
        (PMF.pure (c.setProcess { c.process with phase := .awaitG },
          p.setRoundRecord r
            { (p.roundRecord r) with
              firstGather := (p.roundRecord r).firstGather.setProcess
                { ((p.roundRecord r).firstGather.process) with input := some b }
              firstGatherInputBroadcasts := Function.update (p.roundRecord
                r).firstGatherInputBroadcasts j
                (((p.roundRecord r).firstGatherInputBroadcasts j).setProcess
                  { (((p.roundRecord r).firstGatherInputBroadcasts j).process) with input := some b
                    }) }))
  /-- The graded-agreement call against an already-called record: the round
  loop moves, the round record does not. -/
  | gbcaCallLoop (c : RoundLoopRecord P.n) (p : RoundRecordMap P.n) (r : ℕ) (b : Bool)
      (hh : c.corrupted = false)
      (hph : c.process.phase = .toCallG) (hr : c.process.round = r)
      (hest : c.process.estimate = some b)
      (hin : ((p.roundRecord r).firstGather.process).input ≠ none) :
      RoundStep P j (c, p) (Sum.inr (.gbcaCallLoop r j b))
        (PMF.pure (c.setProcess { c.process with phase := .awaitG }, p))
  /-- The first gather's `ECHO`: the process is called and its accepted pairs
  number at least `n − f`, the source blueprint's `|AP| ≥ n − f`. The payload is
  those pairs, `T_i ← AP_i` of AFW25's Algorithm 5, line 9. -/
  | firstGatherEcho (c : RoundLoopRecord P.n) (p : RoundRecordMap P.n) (r : ℕ)
      (hh : c.corrupted = false) (hterm : p.terminated = false)
      (hin : ((p.roundRecord r).firstGather.process).input ≠ none)
      (hcard : P.n - P.f ≤ (((p.roundRecord r).firstGather.process).accepted).card)
      (hsend : ((p.roundRecord r).firstGather.process).sentEcho = none) :
      RoundStep P j (c, p)
        (Sum.inr (.gbcaSend r j
          (.firstGather (.echo ((p.roundRecord r).firstGather.process).accepted))))
        (PMF.pure (c, p.setRoundRecord r
          { (p.roundRecord r) with
            firstGather := (p.roundRecord r).firstGather.setProcess
              { ((p.roundRecord r).firstGather.process) with
                sentEcho := some (((p.roundRecord r).firstGather.process).accepted) } }))
  /-- The first gather's `VOTE`: `n − f` senders' `ECHO` payloads, each held
  here and contained in the vote payload, are delivered, and the process has
  multicast its own `ECHO`. The main thread of AFW25's Algorithm 5 sends `ECHO`
  before `VOTE`. -/
  | firstGatherVote (c : RoundLoopRecord P.n) (p : RoundRecordMap P.n) (r : ℕ) (U : AcceptedPairs
    P.n Bool)
      (hh : c.corrupted = false) (hterm : p.terminated = false)
      (hin : ((p.roundRecord r).firstGather.process).input ≠ none)
      (hech : ((p.roundRecord r).firstGather.process).sentEcho ≠ none)
      (happ : Gather.approvedBy ((p.roundRecord r).firstGather.process) U)
      (hQ : ∃ Q : Finset (Fin P.n), P.n - P.f ≤ Q.card ∧
        ∀ q ∈ Q, ∃ A, Gather.Message.echo A ∈ ((p.roundRecord r).firstGather.received q) ∧
          Gather.approvedBy ((p.roundRecord r).firstGather.process) A ∧ A ⊆ U)
      (hsend : ((p.roundRecord r).firstGather.process).sentVote = none) :
      RoundStep P j (c, p) (Sum.inr (.gbcaSend r j (.firstGather (.vote U))))
        (PMF.pure (c, p.setRoundRecord r
          { (p.roundRecord r) with
            firstGather := (p.roundRecord r).firstGather.setProcess
              { ((p.roundRecord r).firstGather.process) with sentVote := some U } }))
  /-- The first gather's `BIND`: `n − f` senders' `VOTE` payloads, each held
  here and contained in the bind payload, are delivered; the payload is
  broadcast through the process's own bind-broadcast instance and written to the
  gather record. The process has multicast its own `VOTE` and has not called its
  own bind broadcast. The main thread of AFW25's Algorithm 5 sends `VOTE` before
  `BIND`, and sends `BIND` once, at line 17. -/
  | firstGatherBind (c : RoundLoopRecord P.n) (p : RoundRecordMap P.n) (r : ℕ) (U : AcceptedPairs
    P.n Bool)
      (hh : c.corrupted = false) (hterm : p.terminated = false)
      (hin : ((p.roundRecord r).firstGather.process).input ≠ none)
      (hvot : ((p.roundRecord r).firstGather.process).sentVote ≠ none)
      (hsnd : ((p.roundRecord r).firstGather.process).sentBind = none)
      (hbc : (((p.roundRecord r).firstGatherBindBroadcasts j).process).input = none)
      (happ : Gather.approvedBy ((p.roundRecord r).firstGather.process) U)
      (hQ : ∃ Q : Finset (Fin P.n), P.n - P.f ≤ Q.card ∧
        ∀ q ∈ Q, ∃ W, Gather.Message.vote W ∈ ((p.roundRecord r).firstGather.received q) ∧
          Gather.approvedBy ((p.roundRecord r).firstGather.process) W ∧ W ⊆ U) :
      RoundStep P j (c, p) (Sum.inr (.gbcaSend r j (.firstGatherBindBroadcasts j (.init U))))
        (PMF.pure (c, p.setRoundRecord r
          { (p.roundRecord r) with
            firstGather := (p.roundRecord r).firstGather.setProcess
              { ((p.roundRecord r).firstGather.process) with sentBind := some U }
            firstGatherBindBroadcasts := Function.update (p.roundRecord r).firstGatherBindBroadcasts
              j
              (((p.roundRecord r).firstGatherBindBroadcasts j).setProcess
                { (((p.roundRecord r).firstGatherBindBroadcasts j).process) with input := some U })
                  }))
  /-- The second gather's `ECHO`. -/
  | secondGatherEcho (c : RoundLoopRecord P.n) (p : RoundRecordMap P.n) (r : ℕ)
      (hh : c.corrupted = false) (hterm : p.terminated = false)
      (hin : ((p.roundRecord r).secondGather.process).input ≠ none)
      (hcard : P.n - P.f ≤ (((p.roundRecord r).secondGather.process).accepted).card)
      (hsend : ((p.roundRecord r).secondGather.process).sentEcho = none) :
      RoundStep P j (c, p)
        (Sum.inr (.gbcaSend r j
          (.secondGather (.echo ((p.roundRecord r).secondGather.process).accepted))))
        (PMF.pure (c, p.setRoundRecord r
          { (p.roundRecord r) with
            secondGather := (p.roundRecord r).secondGather.setProcess
              { ((p.roundRecord r).secondGather.process) with
                sentEcho := some (((p.roundRecord r).secondGather.process).accepted) } }))
  /-- The second gather's `VOTE`. -/
  | secondGatherVote (c : RoundLoopRecord P.n) (p : RoundRecordMap P.n) (r : ℕ)
      (U : AcceptedPairs P.n (Option Bool))
      (hh : c.corrupted = false) (hterm : p.terminated = false)
      (hin : ((p.roundRecord r).secondGather.process).input ≠ none)
      (hech : ((p.roundRecord r).secondGather.process).sentEcho ≠ none)
      (happ : Gather.approvedBy ((p.roundRecord r).secondGather.process) U)
      (hQ : ∃ Q : Finset (Fin P.n), P.n - P.f ≤ Q.card ∧
        ∀ q ∈ Q, ∃ A, Gather.Message.echo A ∈ ((p.roundRecord r).secondGather.received q) ∧
          Gather.approvedBy ((p.roundRecord r).secondGather.process) A ∧ A ⊆ U)
      (hsend : ((p.roundRecord r).secondGather.process).sentVote = none) :
      RoundStep P j (c, p) (Sum.inr (.gbcaSend r j (.secondGather (.vote U))))
        (PMF.pure (c, p.setRoundRecord r
          { (p.roundRecord r) with
            secondGather := (p.roundRecord r).secondGather.setProcess
              { ((p.roundRecord r).secondGather.process) with sentVote := some U } }))
  /-- The second gather's `BIND`. -/
  | secondGatherBind (c : RoundLoopRecord P.n) (p : RoundRecordMap P.n) (r : ℕ)
      (U : AcceptedPairs P.n (Option Bool))
      (hh : c.corrupted = false) (hterm : p.terminated = false)
      (hin : ((p.roundRecord r).secondGather.process).input ≠ none)
      (hvot : ((p.roundRecord r).secondGather.process).sentVote ≠ none)
      (hsnd : ((p.roundRecord r).secondGather.process).sentBind = none)
      (hbc : (((p.roundRecord r).secondGatherBindBroadcasts j).process).input = none)
      (happ : Gather.approvedBy ((p.roundRecord r).secondGather.process) U)
      (hQ : ∃ Q : Finset (Fin P.n), P.n - P.f ≤ Q.card ∧
        ∀ q ∈ Q, ∃ W, Gather.Message.vote W ∈ ((p.roundRecord r).secondGather.received q) ∧
          Gather.approvedBy ((p.roundRecord r).secondGather.process) W ∧ W ⊆ U) :
      RoundStep P j (c, p) (Sum.inr (.gbcaSend r j (.secondGatherBindBroadcasts j (.init U))))
        (PMF.pure (c, p.setRoundRecord r
          { (p.roundRecord r) with
            secondGather := (p.roundRecord r).secondGather.setProcess
              { ((p.roundRecord r).secondGather.process) with sentBind := some U }
            secondGatherBindBroadcasts := Function.update (p.roundRecord
              r).secondGatherBindBroadcasts j
              (((p.roundRecord r).secondGatherBindBroadcasts j).setProcess
                { (((p.roundRecord r).secondGatherBindBroadcasts j).process) with input := some U })
                  }))
  /-- The first gather returns, and the process records the candidate its returned entries
  determine (AFW25's Algorithm 4, lines 1 and 2; AFW25's Algorithm 5, line 20). The returner has
  called its own bind broadcast: the `BIND` broadcast of AFW25's Algorithm 5, line 17, precedes the
  wait of line 18. -/
  | firstGatherReturn (c : RoundLoopRecord P.n) (p : RoundRecordMap P.n) (r : ℕ)
      (g : Fin P.n → Option Bool)
      (hh : c.corrupted = false) (hterm : p.terminated = false)
      (hin : ((p.roundRecord r).firstGather.process).input ≠ none)
      (hbind : ((p.roundRecord r).firstGather.process).sentBind ≠ none)
      (hsubap : ∀ k x, g k = some x →
        Gather.holdsInputBroadcastReturn ((p.roundRecord r).firstGather.process) k x)
      (hQ : ∃ Q : Finset (Fin P.n), P.n - P.f ≤ Q.card ∧
        ∀ q ∈ Q, ∃ U, Gather.holdsBindBroadcastReturn ((p.roundRecord r).firstGather.process) q U ∧
          AcceptedPairs.subMap U g)
      (hr1 : ((p.roundRecord r).firstGather.process).returned = false)
      (hcand : (p.roundRecord r).candidate = none) :
      RoundStep P j (c, p)
        (Sum.inr (.gbcaRoundEvent r j (.firstGatherReturn (GBCA.candidate P g))))
        (PMF.pure (c, p.setRoundRecord r
          { (p.roundRecord r) with
            candidate := some (GBCA.candidate P g)
            firstGather := (p.roundRecord r).firstGather.setProcess
              { ((p.roundRecord r).firstGather.process) with returned := true } }))
  /-- The process calls the second gather with the candidate on record, broadcasting it through its
  own input-broadcast instance of that gather (AFW25's Algorithm 4, line 4; D28). The `⟨INIT, x⟩`
  multicast is the network's half. -/
  | secondGatherCall (c : RoundLoopRecord P.n) (p : RoundRecordMap P.n) (r : ℕ) (x : Option Bool)
      (hh : c.corrupted = false) (hterm : p.terminated = false)
      (hcand : (p.roundRecord r).candidate = some x)
      (hin2 : ((p.roundRecord r).secondGather.process).input = none)
      (hbin2 : (((p.roundRecord r).secondGatherInputBroadcasts j).process).input = none) :
      RoundStep P j (c, p)
        (Sum.inr (.gbcaSend r j (.secondGatherInputBroadcasts j (.init x))))
        (PMF.pure (c, p.setRoundRecord r
          { (p.roundRecord r) with
            secondGather := (p.roundRecord r).secondGather.setProcess
              { ((p.roundRecord r).secondGather.process) with input := some x }
            secondGatherInputBroadcasts := Function.update (p.roundRecord
              r).secondGatherInputBroadcasts j
              (((p.roundRecord r).secondGatherInputBroadcasts j).setProcess
                { (((p.roundRecord r).secondGatherInputBroadcasts j).process) with
                  input := some x }) }))
  /-- The second gather returns, and the process records the graded outcome its returned entries
  determine (AFW25's Algorithm 4, lines 5 to 8; AFW25's Algorithm 5, line 20). The returner has
  called its own bind broadcast. -/
  | secondGatherReturn (c : RoundLoopRecord P.n) (p : RoundRecordMap P.n) (r : ℕ)
      (g : Fin P.n → Option (Option Bool))
      (hh : c.corrupted = false) (hterm : p.terminated = false)
      (hin : ((p.roundRecord r).secondGather.process).input ≠ none)
      (hbind : ((p.roundRecord r).secondGather.process).sentBind ≠ none)
      (hsubap : ∀ k x, g k = some x →
        Gather.holdsInputBroadcastReturn ((p.roundRecord r).secondGather.process) k x)
      (hQ : ∃ Q : Finset (Fin P.n), P.n - P.f ≤ Q.card ∧
        ∀ q ∈ Q, ∃ U,
          Gather.holdsBindBroadcastReturn ((p.roundRecord r).secondGather.process) q U ∧
            AcceptedPairs.subMap U g)
      (hr2 : ((p.roundRecord r).secondGather.process).returned = false)
      (hout : (p.roundRecord r).output = none) :
      RoundStep P j (c, p)
        (Sum.inr (.gbcaRoundEvent r j (.secondGatherReturn (GBCA.gradeOf P g))))
        (PMF.pure (c, p.setRoundRecord r
          { (p.roundRecord r) with
            output := some (GBCA.gradeOf P g)
            secondGather := (p.roundRecord r).secondGather.setProcess
              { ((p.roundRecord r).secondGather.process) with returned := true } }))
  /-- The round returns the graded outcome on record to the round loop (AFW25's Algorithm 4,
  line 3 and line 8). The outcome leaves the round record, which is what marks the round
  returned. -/
  | retG (c : RoundLoopRecord P.n) (p : RoundRecordMap P.n) (r : ℕ) (out : GBCAOutput) (bnd : Bool)
      (hh : c.corrupted = false)
      (hph : c.process.phase = .awaitG) (hr : c.process.round = r)
      (hterm : p.terminated = false)
      (hout : (p.roundRecord r).output = some out)
      (hr2 : ((p.roundRecord r).secondGather.process).returned = true) :
      RoundStep P j (c, p) (Sum.inl (.retG r j out bnd))
        (PMF.pure (c.setProcess { c.process with
            estimate := out.estimate, lastGrade := some out, phase := .toCallW },
          p.setRoundRecord r { (p.roundRecord r) with output := none }))
  /-- `ECHO` in an input-broadcast instance of the first gather: the leader's
  `⟨INIT, m⟩` is delivered here, or an `ECHO m` receipt quorum is, or `f + 1`
  `VOTE m` receipts are; no `ECHO` is out. -/
  | firstGatherInputBroadcastEcho (c : RoundLoopRecord P.n) (p : RoundRecordMap P.n) (r : ℕ)
      (i : Fin P.n) (m : Bool) (hh : c.corrupted = false) (hterm : p.terminated = false)
      (hrecv : BRB.Message.init m ∈ ((p.roundRecord r).firstGatherInputBroadcasts i).received i ∨
        P.echoReceiptQuorum ≤ ((p.roundRecord r).firstGatherInputBroadcasts i).receivedCount (.echo
          m) ∨
        P.f + 1 ≤ ((p.roundRecord r).firstGatherInputBroadcasts i).receivedCount (.vote m))
      (hsend : (((p.roundRecord r).firstGatherInputBroadcasts i).process).sentEcho = none) :
      RoundStep P j (c, p) (Sum.inr (.gbcaSend r j (.firstGatherInputBroadcasts i (.echo m))))
        (PMF.pure (c, p.setRoundRecord r
          { (p.roundRecord r) with
            firstGatherInputBroadcasts := Function.update (p.roundRecord
              r).firstGatherInputBroadcasts i
              (((p.roundRecord r).firstGatherInputBroadcasts i).setProcess
                { (((p.roundRecord r).firstGatherInputBroadcasts i).process) with sentEcho := some m
                  }) }))
  /-- `VOTE` on an `ECHO m` receipt quorum in an input-broadcast instance of the
  first gather. -/
  | firstGatherInputBroadcastVoteQuorum (c : RoundLoopRecord P.n) (p : RoundRecordMap P.n) (r : ℕ)
    (i : Fin P.n)
      (m : Bool) (hh : c.corrupted = false) (hterm : p.terminated = false)
      (hcnt : P.echoReceiptQuorum ≤ ((p.roundRecord r).firstGatherInputBroadcasts i).receivedCount
        (.echo
        m))
      (hsend : (((p.roundRecord r).firstGatherInputBroadcasts i).process).sentVote = none) :
      RoundStep P j (c, p) (Sum.inr (.gbcaSend r j (.firstGatherInputBroadcasts i (.vote m))))
        (PMF.pure (c, p.setRoundRecord r
          { (p.roundRecord r) with
            firstGatherInputBroadcasts := Function.update (p.roundRecord
              r).firstGatherInputBroadcasts i
              (((p.roundRecord r).firstGatherInputBroadcasts i).setProcess
                { (((p.roundRecord r).firstGatherInputBroadcasts i).process) with sentVote := some m
                  }) }))
  /-- `VOTE` by amplification, on `f + 1` `VOTE` receipts. -/
  | firstGatherInputBroadcastVoteAmplification (c : RoundLoopRecord P.n) (p : RoundRecordMap P.n) (r
    : ℕ) (i : Fin P.n)
      (m : Bool) (hh : c.corrupted = false) (hterm : p.terminated = false)
      (hcnt : P.f + 1 ≤ ((p.roundRecord r).firstGatherInputBroadcasts i).receivedCount (.vote m))
      (hsend : (((p.roundRecord r).firstGatherInputBroadcasts i).process).sentVote = none) :
      RoundStep P j (c, p) (Sum.inr (.gbcaSend r j (.firstGatherInputBroadcasts i (.vote m))))
        (PMF.pure (c, p.setRoundRecord r
          { (p.roundRecord r) with
            firstGatherInputBroadcasts := Function.update (p.roundRecord
              r).firstGatherInputBroadcasts i
              (((p.roundRecord r).firstGatherInputBroadcasts i).setProcess
                { (((p.roundRecord r).firstGatherInputBroadcasts i).process) with sentVote := some m
                  }) }))
  /-- The instance broadcasting `i`'s input in the first gather returns here: a `2f + 1` `VOTE`
  quorum stands in that instance, which has not returned here yet, and the gather record files the
  value it returned. AFW25's Algorithm 5, lines 1 and 2; LeslieBP's Algorithm 4,
  `upon BRB_k.return(m')`. -/
  | firstGatherInputBroadcastReturn (c : RoundLoopRecord P.n) (p : RoundRecordMap P.n)
      (r : ℕ) (i : Fin P.n) (v : Bool)
      (hh : c.corrupted = false) (hterm : p.terminated = false)
      (hcnt : 2 * P.f + 1 ≤
        ((p.roundRecord r).firstGatherInputBroadcasts i).receivedCount (.vote v))
      (hret : (((p.roundRecord r).firstGatherInputBroadcasts i).process).returned = false) :
      RoundStep P j (c, p) (Sum.inr (.gbcaRoundEvent r j (.firstGatherInputBroadcastReturn i v)))
        (PMF.pure (c, p.setRoundRecord r
          { (p.roundRecord r) with
            firstGather := (p.roundRecord r).firstGather.setProcess
              { ((p.roundRecord r).firstGather.process) with
                inputBroadcastReturned := Function.update
                  ((p.roundRecord r).firstGather.process).inputBroadcastReturned i (some v) }
            firstGatherInputBroadcasts := Function.update
              (p.roundRecord r).firstGatherInputBroadcasts i
              ((((p.roundRecord r).firstGatherInputBroadcasts i).setProcess
                { (((p.roundRecord r).firstGatherInputBroadcasts i).process) with
                  returned := true })) }))
  /-- `ECHO` in a bind-broadcast instance of the first gather. -/
  | firstGatherBindBroadcastEcho (c : RoundLoopRecord P.n) (p : RoundRecordMap P.n) (r : ℕ) (i : Fin
    P.n)
      (m : AcceptedPairs P.n Bool) (hh : c.corrupted = false) (hterm : p.terminated = false)
      (hrecv : BRB.Message.init m ∈ ((p.roundRecord r).firstGatherBindBroadcasts i).received i ∨
        P.echoReceiptQuorum ≤ ((p.roundRecord r).firstGatherBindBroadcasts i).receivedCount (.echo
          m) ∨
        P.f + 1 ≤ ((p.roundRecord r).firstGatherBindBroadcasts i).receivedCount (.vote m))
      (hsend : (((p.roundRecord r).firstGatherBindBroadcasts i).process).sentEcho = none) :
      RoundStep P j (c, p) (Sum.inr (.gbcaSend r j (.firstGatherBindBroadcasts i (.echo m))))
        (PMF.pure (c, p.setRoundRecord r
          { (p.roundRecord r) with
            firstGatherBindBroadcasts := Function.update (p.roundRecord r).firstGatherBindBroadcasts
              i
              (((p.roundRecord r).firstGatherBindBroadcasts i).setProcess
                { (((p.roundRecord r).firstGatherBindBroadcasts i).process) with sentEcho := some m
                  }) }))
  /-- `VOTE` on an `ECHO m` receipt quorum in a bind-broadcast instance of the
  first gather. -/
  | firstGatherBindBroadcastVoteQuorum (c : RoundLoopRecord P.n) (p : RoundRecordMap P.n) (r : ℕ) (i
    : Fin P.n)
      (m : AcceptedPairs P.n Bool) (hh : c.corrupted = false) (hterm : p.terminated = false)
      (hcnt : P.echoReceiptQuorum ≤ ((p.roundRecord r).firstGatherBindBroadcasts i).receivedCount
        (.echo
        m))
      (hsend : (((p.roundRecord r).firstGatherBindBroadcasts i).process).sentVote = none) :
      RoundStep P j (c, p) (Sum.inr (.gbcaSend r j (.firstGatherBindBroadcasts i (.vote m))))
        (PMF.pure (c, p.setRoundRecord r
          { (p.roundRecord r) with
            firstGatherBindBroadcasts := Function.update (p.roundRecord r).firstGatherBindBroadcasts
              i
              (((p.roundRecord r).firstGatherBindBroadcasts i).setProcess
                { (((p.roundRecord r).firstGatherBindBroadcasts i).process) with sentVote := some m
                  }) }))
  /-- `VOTE` by amplification in a bind-broadcast instance of the first
  gather. -/
  | firstGatherBindBroadcastVoteAmplification (c : RoundLoopRecord P.n) (p : RoundRecordMap P.n) (r
    : ℕ) (i : Fin P.n)
      (m : AcceptedPairs P.n Bool) (hh : c.corrupted = false) (hterm : p.terminated = false)
      (hcnt : P.f + 1 ≤ ((p.roundRecord r).firstGatherBindBroadcasts i).receivedCount (.vote m))
      (hsend : (((p.roundRecord r).firstGatherBindBroadcasts i).process).sentVote = none) :
      RoundStep P j (c, p) (Sum.inr (.gbcaSend r j (.firstGatherBindBroadcasts i (.vote m))))
        (PMF.pure (c, p.setRoundRecord r
          { (p.roundRecord r) with
            firstGatherBindBroadcasts := Function.update (p.roundRecord r).firstGatherBindBroadcasts
              i
              (((p.roundRecord r).firstGatherBindBroadcasts i).setProcess
                { (((p.roundRecord r).firstGatherBindBroadcasts i).process) with sentVote := some m
                  }) }))
  /-- The instance broadcasting `q`'s `BIND` payload in the first gather returns here, and the
  gather record files the payload it returned. AFW25's Algorithm 5, line 18. -/
  | firstGatherBindBroadcastReturn (c : RoundLoopRecord P.n) (p : RoundRecordMap P.n)
      (r : ℕ) (q : Fin P.n) (U : AcceptedPairs P.n Bool)
      (hh : c.corrupted = false) (hterm : p.terminated = false)
      (hcnt : 2 * P.f + 1 ≤
        ((p.roundRecord r).firstGatherBindBroadcasts q).receivedCount (.vote U))
      (hret : (((p.roundRecord r).firstGatherBindBroadcasts q).process).returned = false) :
      RoundStep P j (c, p) (Sum.inr (.gbcaRoundEvent r j (.firstGatherBindBroadcastReturn q U)))
        (PMF.pure (c, p.setRoundRecord r
          { (p.roundRecord r) with
            firstGather := (p.roundRecord r).firstGather.setProcess
              { ((p.roundRecord r).firstGather.process) with
                bindBroadcastReturned := Function.update
                  ((p.roundRecord r).firstGather.process).bindBroadcastReturned q (some U) }
            firstGatherBindBroadcasts := Function.update
              (p.roundRecord r).firstGatherBindBroadcasts q
              ((((p.roundRecord r).firstGatherBindBroadcasts q).setProcess
                { (((p.roundRecord r).firstGatherBindBroadcasts q).process) with
                  returned := true })) }))
  /-- `ECHO` in an input-broadcast instance of the second gather. -/
  | secondGatherInputBroadcastEcho (c : RoundLoopRecord P.n) (p : RoundRecordMap P.n) (r : ℕ)
      (i : Fin P.n) (m : Option Bool) (hh : c.corrupted = false) (hterm : p.terminated = false)
      (hrecv : BRB.Message.init m ∈ ((p.roundRecord r).secondGatherInputBroadcasts i).received i ∨
        P.echoReceiptQuorum ≤ ((p.roundRecord r).secondGatherInputBroadcasts i).receivedCount (.echo
          m) ∨
        P.f + 1 ≤ ((p.roundRecord r).secondGatherInputBroadcasts i).receivedCount (.vote m))
      (hsend : (((p.roundRecord r).secondGatherInputBroadcasts i).process).sentEcho = none) :
      RoundStep P j (c, p) (Sum.inr (.gbcaSend r j (.secondGatherInputBroadcasts i (.echo m))))
        (PMF.pure (c, p.setRoundRecord r
          { (p.roundRecord r) with
            secondGatherInputBroadcasts := Function.update (p.roundRecord
              r).secondGatherInputBroadcasts i
              (((p.roundRecord r).secondGatherInputBroadcasts i).setProcess
                { (((p.roundRecord r).secondGatherInputBroadcasts i).process) with
                  sentEcho :=
                    some m }) }))
  /-- `VOTE` on an `ECHO m` receipt quorum in an input-broadcast instance of the
  second gather. -/
  | secondGatherInputBroadcastVoteQuorum (c : RoundLoopRecord P.n) (p : RoundRecordMap P.n) (r : ℕ)
    (i : Fin P.n)
      (m : Option Bool) (hh : c.corrupted = false) (hterm : p.terminated = false)
      (hcnt : P.echoReceiptQuorum ≤ ((p.roundRecord r).secondGatherInputBroadcasts i).receivedCount
        (.echo
        m))
      (hsend : (((p.roundRecord r).secondGatherInputBroadcasts i).process).sentVote = none) :
      RoundStep P j (c, p) (Sum.inr (.gbcaSend r j (.secondGatherInputBroadcasts i (.vote m))))
        (PMF.pure (c, p.setRoundRecord r
          { (p.roundRecord r) with
            secondGatherInputBroadcasts := Function.update (p.roundRecord
              r).secondGatherInputBroadcasts i
              (((p.roundRecord r).secondGatherInputBroadcasts i).setProcess
                { (((p.roundRecord r).secondGatherInputBroadcasts i).process) with
                  sentVote :=
                    some m }) }))
  /-- `VOTE` by amplification in an input-broadcast instance of the second
  gather. -/
  | secondGatherInputBroadcastVoteAmplification (c : RoundLoopRecord P.n) (p : RoundRecordMap P.n)
    (r : ℕ) (i : Fin P.n)
      (m : Option Bool) (hh : c.corrupted = false) (hterm : p.terminated = false)
      (hcnt : P.f + 1 ≤ ((p.roundRecord r).secondGatherInputBroadcasts i).receivedCount (.vote m))
      (hsend : (((p.roundRecord r).secondGatherInputBroadcasts i).process).sentVote = none) :
      RoundStep P j (c, p) (Sum.inr (.gbcaSend r j (.secondGatherInputBroadcasts i (.vote m))))
        (PMF.pure (c, p.setRoundRecord r
          { (p.roundRecord r) with
            secondGatherInputBroadcasts := Function.update (p.roundRecord
              r).secondGatherInputBroadcasts i
              (((p.roundRecord r).secondGatherInputBroadcasts i).setProcess
                { (((p.roundRecord r).secondGatherInputBroadcasts i).process) with
                  sentVote :=
                    some m }) }))
  /-- The instance broadcasting `i`'s input in the second gather returns here. AFW25's Algorithm 5,
  lines 1 and 2. -/
  | secondGatherInputBroadcastReturn (c : RoundLoopRecord P.n) (p : RoundRecordMap P.n)
      (r : ℕ) (i : Fin P.n) (v : Option Bool)
      (hh : c.corrupted = false) (hterm : p.terminated = false)
      (hcnt : 2 * P.f + 1 ≤
        ((p.roundRecord r).secondGatherInputBroadcasts i).receivedCount (.vote v))
      (hret : (((p.roundRecord r).secondGatherInputBroadcasts i).process).returned = false) :
      RoundStep P j (c, p) (Sum.inr (.gbcaRoundEvent r j (.secondGatherInputBroadcastReturn i v)))
        (PMF.pure (c, p.setRoundRecord r
          { (p.roundRecord r) with
            secondGather := (p.roundRecord r).secondGather.setProcess
              { ((p.roundRecord r).secondGather.process) with
                inputBroadcastReturned := Function.update
                  ((p.roundRecord r).secondGather.process).inputBroadcastReturned i (some v) }
            secondGatherInputBroadcasts := Function.update
              (p.roundRecord r).secondGatherInputBroadcasts i
              ((((p.roundRecord r).secondGatherInputBroadcasts i).setProcess
                { (((p.roundRecord r).secondGatherInputBroadcasts i).process) with
                  returned := true })) }))
  /-- `ECHO` in a bind-broadcast instance of the second gather. -/
  | secondGatherBindBroadcastEcho (c : RoundLoopRecord P.n) (p : RoundRecordMap P.n) (r : ℕ)
      (i : Fin P.n) (m : AcceptedPairs P.n (Option Bool)) (hh : c.corrupted = false)
      (hterm : p.terminated = false)
      (hrecv : BRB.Message.init m ∈ ((p.roundRecord r).secondGatherBindBroadcasts i).received i ∨
        P.echoReceiptQuorum ≤ ((p.roundRecord r).secondGatherBindBroadcasts i).receivedCount (.echo
          m) ∨
        P.f + 1 ≤ ((p.roundRecord r).secondGatherBindBroadcasts i).receivedCount (.vote m))
      (hsend : (((p.roundRecord r).secondGatherBindBroadcasts i).process).sentEcho = none) :
      RoundStep P j (c, p) (Sum.inr (.gbcaSend r j (.secondGatherBindBroadcasts i (.echo m))))
        (PMF.pure (c, p.setRoundRecord r
          { (p.roundRecord r) with
            secondGatherBindBroadcasts := Function.update (p.roundRecord
              r).secondGatherBindBroadcasts i
              (((p.roundRecord r).secondGatherBindBroadcasts i).setProcess
                { (((p.roundRecord r).secondGatherBindBroadcasts i).process) with sentEcho := some m
                  }) }))
  /-- `VOTE` on an `ECHO m` receipt quorum in a bind-broadcast instance of the
  second gather. -/
  | secondGatherBindBroadcastVoteQuorum (c : RoundLoopRecord P.n) (p : RoundRecordMap P.n) (r : ℕ)
    (i : Fin P.n)
      (m : AcceptedPairs P.n (Option Bool)) (hh : c.corrupted = false)
      (hterm : p.terminated = false)
      (hcnt : P.echoReceiptQuorum ≤ ((p.roundRecord r).secondGatherBindBroadcasts i).receivedCount
        (.echo
        m))
      (hsend : (((p.roundRecord r).secondGatherBindBroadcasts i).process).sentVote = none) :
      RoundStep P j (c, p) (Sum.inr (.gbcaSend r j (.secondGatherBindBroadcasts i (.vote m))))
        (PMF.pure (c, p.setRoundRecord r
          { (p.roundRecord r) with
            secondGatherBindBroadcasts := Function.update (p.roundRecord
              r).secondGatherBindBroadcasts i
              (((p.roundRecord r).secondGatherBindBroadcasts i).setProcess
                { (((p.roundRecord r).secondGatherBindBroadcasts i).process) with sentVote := some m
                  }) }))
  /-- `VOTE` by amplification in a bind-broadcast instance of the second
  gather. -/
  | secondGatherBindBroadcastVoteAmplification (c : RoundLoopRecord P.n) (p : RoundRecordMap P.n) (r
    : ℕ) (i : Fin P.n)
      (m : AcceptedPairs P.n (Option Bool)) (hh : c.corrupted = false)
      (hterm : p.terminated = false)
      (hcnt : P.f + 1 ≤ ((p.roundRecord r).secondGatherBindBroadcasts i).receivedCount (.vote m))
      (hsend : (((p.roundRecord r).secondGatherBindBroadcasts i).process).sentVote = none) :
      RoundStep P j (c, p) (Sum.inr (.gbcaSend r j (.secondGatherBindBroadcasts i (.vote m))))
        (PMF.pure (c, p.setRoundRecord r
          { (p.roundRecord r) with
            secondGatherBindBroadcasts := Function.update (p.roundRecord
              r).secondGatherBindBroadcasts i
              (((p.roundRecord r).secondGatherBindBroadcasts i).setProcess
                { (((p.roundRecord r).secondGatherBindBroadcasts i).process) with sentVote := some m
                  }) }))
  /-- The instance broadcasting `q`'s `BIND` payload in the second gather returns here. AFW25's
  Algorithm 5, line 18. -/
  | secondGatherBindBroadcastReturn (c : RoundLoopRecord P.n) (p : RoundRecordMap P.n)
      (r : ℕ) (q : Fin P.n) (U : AcceptedPairs P.n (Option Bool))
      (hh : c.corrupted = false) (hterm : p.terminated = false)
      (hcnt : 2 * P.f + 1 ≤
        ((p.roundRecord r).secondGatherBindBroadcasts q).receivedCount (.vote U))
      (hret : (((p.roundRecord r).secondGatherBindBroadcasts q).process).returned = false) :
      RoundStep P j (c, p) (Sum.inr (.gbcaRoundEvent r j (.secondGatherBindBroadcastReturn q U)))
        (PMF.pure (c, p.setRoundRecord r
          { (p.roundRecord r) with
            secondGather := (p.roundRecord r).secondGather.setProcess
              { ((p.roundRecord r).secondGather.process) with
                bindBroadcastReturned := Function.update
                  ((p.roundRecord r).secondGather.process).bindBroadcastReturned q (some U) }
            secondGatherBindBroadcasts := Function.update
              (p.roundRecord r).secondGatherBindBroadcasts q
              ((((p.roundRecord r).secondGatherBindBroadcasts q).setProcess
                { (((p.roundRecord r).secondGatherBindBroadcasts q).process) with
                  returned := true })) }))
  /-- Delivery, receiver's half: file the message in the local state of the network state its
  tag names. Authenticity is the network's conjunct. -/
  | gbcaDeliverReceive (c : RoundLoopRecord P.n) (p : RoundRecordMap P.n) (r : ℕ) (k : Fin P.n)
      (m : Message P.n) (hh : c.corrupted = false) (hterm : p.terminated = false) :
      RoundStep P j (c, p) (Sum.inr (.gbcaDeliver r j k m))
        (PMF.pure (c, p.deliverTo r k m))

/-- The transitions above meet the implementation's conditions: each carries a label of
`roundOwn j`, each fires only at an unreplaced program, each is Dirac, and the
return takes the announced bit free (D29). -/
instance instIsRoundStep (P : Parameters) :
    IsRoundStep P (Message P.n) (RoundEvent P.n) (RoundRecord P.n) (RoundStep P) where
  own h := by
    cases h <;> rfl
  correct h := by
    cases h <;> assumption
  dirac h := by
    cases h <;> exact ⟨_, rfl⟩
  boundBitFree h := by cases h; constructor <;> assumption

/-! ### The transposed record writes one local state at a time

A tagged delivery reaches exactly the local state its tag names and leaves every other local state
of the record where it stands. These are the facts the substitution into the composed system rests
on, the composed system writing the same local state through its instance-major indexing. -/

section Transposition

variable {n : ℕ}

example (s : RoundRecord n) (k i : Fin n) (m : BRB.Message Bool) :
    ((s.deliverTo k (.firstGatherInputBroadcasts i m)).firstGatherInputBroadcasts i).received k
      = insert m ((s.firstGatherInputBroadcasts i).received k) := by
  simp [RoundRecord.deliverTo, LocalState.deliverTo]

example (s : RoundRecord n) (k i i' : Fin n) (m : BRB.Message Bool) (h : i' ≠ i) :
    (s.deliverTo k (.firstGatherInputBroadcasts i m)).firstGatherInputBroadcasts i' =
      s.firstGatherInputBroadcasts i' := by
  simp [RoundRecord.deliverTo, Function.update_of_ne h]

example (s : RoundRecord n) (k i : Fin n) (m : BRB.Message Bool) :
    (s.deliverTo k (.firstGatherInputBroadcasts i m)).firstGather = s.firstGather := by
  simp [RoundRecord.deliverTo]

example (s : RoundRecord n) (k : Fin n) (m : Gather.Message n Bool) :
    (s.deliverTo k (.firstGather m)).firstGather.received k = insert m (s.firstGather.received k) :=
      by
  simp [RoundRecord.deliverTo, LocalState.deliverTo]

example (s : RoundRecord n) (k : Fin n) (m : Gather.Message n Bool) (i : Fin n) :
    (s.deliverTo k (.firstGather m)).firstGatherInputBroadcasts i = s.firstGatherInputBroadcasts i
      := by
  simp [RoundRecord.deliverTo]

example (P : Parameters) (p : RoundRecordMap P.n) (r : ℕ) (sr : RoundRecord P.n) :
    (p.setRoundRecord r sr).roundRecord r = sr := by simp

end Transposition

/-! ### The protocol -/

/-- The message the graded-agreement call multicasts: the caller's input,
broadcast through the caller's own input-broadcast instance of the first
gather. -/
def gbcaCallPayload (P : Parameters) : Fin P.n → Bool → Message P.n := fun id b =>
  .firstGatherInputBroadcasts id (.init b)

/-- The step relation of the program of process `j`. -/
abbrev ProgramStep (P : Parameters) (j : Fin P.n) :
    ProcessRecord P.n → ExtendedLabel P.n (Message P.n) (RoundEvent P.n) →
      PMF (ProcessRecord P.n) → Prop :=
  Implementation.ProgramStep P (Message P.n) (RoundEvent P.n) (RoundRecord P.n) (RoundStep P) j

/-- The step relation of the network. -/
abbrev NetworkStep (P : Parameters) :
    NetworkState P.n → ExtendedLabel P.n (Message P.n) (RoundEvent P.n) →
      PMF (NetworkState P.n) → Prop :=
  Implementation.NetworkStep P (Message P.n) (RoundEvent P.n) (Ghost P.n) (gbcaCallPayload P)
    (ghostStep P)
    (announcedBound P)

/-- The state of the gather-based protocol: the process family, the network
adversary and the coin oracle. -/
abbrev ProtocolState (P : Parameters) : Type :=
  Implementation.State P (Message P.n) (RoundRecord P.n) (Ghost P.n)

/-- The three components in parallel, over the extended alphabet. -/
noncomputable def protocolExtended (P : Parameters) :
    System (ProtocolState P) (Implementation.ExtendedLabel P.n (Message P.n) (RoundEvent P.n)) :=
  Implementation.systemExtended P (Message P.n) (RoundEvent P.n) (RoundRecord P.n) (Ghost P.n)
    (RoundStep P)
    (gbcaCallPayload P) (ghostStep P) (announcedBound P)

/-- The gather-based protocol group: the rendezvous alphabet hidden, the
result read back over `Label n`. -/
noncomputable def protocolHidden (P : Parameters) : System (ProtocolState P) (Label P.n) :=
  Implementation.systemHidden P (Message P.n) (RoundEvent P.n) (RoundRecord P.n) (Ghost P.n)
    (RoundStep P)
    (gbcaCallPayload P) (ghostStep P) (announcedBound P)

/-- **The gather-based protocol**: the group with the sub-protocol API
hidden. -/
noncomputable def protocol (P : Parameters) : System (ProtocolState P) (Label P.n) :=
  Implementation.system P (Message P.n) (RoundEvent P.n) (RoundRecord P.n) (Ghost P.n)
    (RoundStep P)
    (gbcaCallPayload P) (ghostStep P) (announcedBound P)

end AFW

end ABA
end PLTS
