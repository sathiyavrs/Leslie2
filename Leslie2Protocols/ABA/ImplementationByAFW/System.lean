/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sathiya / Claude
-/

import Leslie2Protocols.ABA.Implementation.System
import Leslie2Protocols.ABA.GBCA.AFW.Counting
import Leslie2Protocols.ABA.Gather.MessagesAndCommonCore
import Leslie2Protocols.ABA.ReliableBroadcast.BrachaImplementation

/-!
# The gather-based protocol as it runs

The gather-based graded agreement, read as a protocol rather than as a
composition: `n` programs beside one network adversary and the coin oracle.
This is the flat reading of `ABA/Implementation/System.lean` at the gather-based
implementation, as `ABA/ImplementationByABDY/System.lean` is that reading at ABDY22's, and it
supplies the same three things — a stage message type, a stage record, and the
implementation's rows. It sits in the namespace `AFW`, after Attiya, Flam and
Welch, and so `AFW.protocol` is what `ABDY.protocol` is at ABDY22's.

## One sent for every network state

A round of the gather-based implementation carries `4n + 2` network states:
one for each of the two gather instances, and one for each of the `4n` Bracha
instances — `n` carrying the inputs and `n` carrying the `BIND` payloads, in
each of the two gathers. The adversary here holds one sent family per round
instead, over the tagged message type `Msg`, whose tag names the network state a
message belongs to and, for a Bracha message, the instance it belongs to. The
sent index stays the sender, so a threshold still counts distinct senders
(D5).

## The record of one process

A process's data is scattered across those instances: `j` holds its own local state in
each of the `4n + 2` of them, and the composed reading indexes those local states by
instance and then by process. A program must hold its own data and no one
else's, so `StageRec` holds them the other way round — `j`'s local state in each
gather instance, and `j`'s local state in each of the `n` instances of each Bracha
family. Every guard of the gather-based implementation reads the acting
process's own local states and the network states, and the two rows that read a network state are
the adversary's delivery and its Byzantine injection, so the transposition
loses nothing.

## The rows

The stage-side rows are the rows of `Gather.LowStep` and `GBCA.ByAFW.lowPairInst`
cut into their process half and their network half. A send writes the sender's
own record and the network records the message; a delivery files the message in
the receiver's own local state, dispatched on the tag. Three rows are fused
(D28): the graded-agreement call broadcasts the input, the `BIND` send is a
broadcast call, and the first gather's return to a process is that process's
call of the second gather.

The Bracha return is not a row here. A gather guard reads a `2f + 1` `VOTE`
receipt quorum on the acting process's own local state in the instance —
`apIn1` and its three companions — so what an instance has returned to a
process is a receipt count on that process's own record. A gather program of
the composed reading holds the returned value in a store
(`Gather.holdsIn`, `Gather.holdsBind`), and `AFW.storeIn` is the reading that
identifies the two. The first gather's `ECHO` payload is the process's
accepted pairs, `AFW.acceptedIn1`, which is that reading at each of the `n`
input-broadcast instances.

## The network adversary's ghost

The record the adversary holds for round `r` is `AFW.Ghost`: the first
gather's frozen core, the second gather's frozen core, and the round's bound
bit, each written once. `AFW.ghostStep` writes it. The link's broadcast of the
candidate — the label `gsnd r j (brbIn2 j (init _))`, which no other row
carries — freezes the first core at `Gather.coreOf` of the round's first
gather network state and the bound bit at `GBCA.boundOfCore` of that core; a
graded return freezes the second core the same way. Every other label leaves
the record where it stands.

The network state `Gather.coreOf` is read on is `AFW.ga1Of`, the first
gather's slice of the adversary's tagged sent sets beside its corrupted set,
and `AFW.ga2Of` is the second's. `Gather.coreOf` reads the sent sets and the
corrupted set alone (`Gather.coreOf_networkState_only`), which is what lets the
adversary compute the core from its own state.

`AFW.ghostOut` reads the bit back, and `AFW.announcedBound`, the guard of the
two graded-agreement return rows, is the equation between the bit their label
carries and it. `AFW.ghostOut` is total: where the ghost holds no bit it
computes one from the first gather's core, and on a reachable state the
returner's own link has already written the bit.
-/

namespace PLTS
namespace ABA
namespace AFW

open Implementation Gather

/-! ### The tagged message type -/

/-- A round's messages: the two gather network states and the `4n` Bracha network states,
tagged by the network state they belong to. A Bracha tag carries the instance, whose
index is its leader. -/
inductive Msg (n : ℕ) : Type
  /-- A message of the first gather's network state. -/
  | ga1 (m : GaMsg n Bool)
  /-- A message of the second gather's network state. -/
  | ga2 (m : GaMsg n (Option Bool))
  /-- A message of the input-broadcast instance `k` of the first gather. -/
  | brbIn1 (k : Fin n) (m : BRB.BMsg Bool)
  /-- A message of the bind-broadcast instance `k` of the first gather. -/
  | brbBind1 (k : Fin n) (m : BRB.BMsg (APSet n Bool))
  /-- A message of the input-broadcast instance `k` of the second gather. -/
  | brbIn2 (k : Fin n) (m : BRB.BMsg (Option Bool))
  /-- A message of the bind-broadcast instance `k` of the second gather. -/
  | brbBind2 (k : Fin n) (m : BRB.BMsg (APSet n (Option Bool)))
  deriving DecidableEq

/-! ### The record of one process in one round -/

/-- One process's data in one round, held by instance: its local state in each gather
instance, and its local state in each of the `n` instances of each broadcast family.
This is the composed reading's instance-major indexing transposed. -/
structure StageRec (n : ℕ) : Type where
  /-- The process's local state in the first gather instance. -/
  ga1 : LocalState n (PRec n Bool) (GaMsg n Bool)
  /-- The process's local state in the second gather instance. -/
  ga2 : LocalState n (PRec n (Option Bool)) (GaMsg n (Option Bool))
  /-- The process's local state in each input-broadcast instance of the first
  gather. -/
  brbIn1 : ∀ _ : Fin n, LocalState n (BRB.PState Bool) (BRB.BMsg Bool)
  /-- The process's local state in each bind-broadcast instance of the first
  gather. -/
  brbBind1 : ∀ _ : Fin n, LocalState n (BRB.PState (APSet n Bool)) (BRB.BMsg (APSet n Bool))
  /-- The process's local state in each input-broadcast instance of the second
  gather. -/
  brbIn2 : ∀ _ : Fin n, LocalState n (BRB.PState (Option Bool)) (BRB.BMsg (Option Bool))
  /-- The process's local state in each bind-broadcast instance of the second
  gather. -/
  brbBind2 : ∀ _ : Fin n,
    LocalState n (BRB.PState (APSet n (Option Bool))) (BRB.BMsg (APSet n (Option Bool)))

namespace StageRec

variable {n : ℕ}

/-- The initial record: every local state empty over the initial local record. -/
def initial (n : ℕ) : StageRec n where
  ga1 := LocalState.initial n _ (PRec.initial n Bool)
  ga2 := LocalState.initial n _ (PRec.initial n (Option Bool))
  brbIn1 := fun _ => LocalState.initial n _ (BRB.PState.initial Bool)
  brbBind1 := fun _ => LocalState.initial n _ (BRB.PState.initial (APSet n Bool))
  brbIn2 := fun _ => LocalState.initial n _ (BRB.PState.initial (Option Bool))
  brbBind2 := fun _ => LocalState.initial n _ (BRB.PState.initial (APSet n (Option Bool)))

/-- File a delivered message in the local state of the network state its tag names. -/
def deliverTo (s : StageRec n) (k : Fin n) : Msg n → StageRec n
  | .ga1 m => { s with ga1 := s.ga1.deliverTo k m }
  | .ga2 m => { s with ga2 := s.ga2.deliverTo k m }
  | .brbIn1 i m =>
      { s with brbIn1 := Function.update s.brbIn1 i ((s.brbIn1 i).deliverTo k m) }
  | .brbBind1 i m =>
      { s with brbBind1 := Function.update s.brbBind1 i ((s.brbBind1 i).deliverTo k m) }
  | .brbIn2 i m =>
      { s with brbIn2 := Function.update s.brbIn2 i ((s.brbIn2 i).deliverTo k m) }
  | .brbBind2 i m =>
      { s with brbBind2 := Function.update s.brbBind2 i ((s.brbBind2 i).deliverTo k m) }

end StageRec

/-- The gather-based stage record, as the flat reading consumes it. -/
instance instStageRecord (n : ℕ) : StageRecord n (Msg n) (StageRec n) where
  initial := StageRec.initial n
  deliverTo s k m := s.deliverTo k m

@[simp] theorem stageRecord_initial (n : ℕ) :
    (StageRecord.initial : StageRec n) = StageRec.initial n := rfl

@[simp] theorem stageRecord_deliverTo (n : ℕ) (s : StageRec n) (k : Fin n)
    (m : Msg n) : (StageRecord.deliverTo s k m : StageRec n) = s.deliverTo k m := rfl

/-- The stage-side record of one process: the round records it holds, and
whether it has terminated (D22). -/
abbrev StageSideRec (n : ℕ) : Type := StageSideRecP (StageRec n)

/-- The state of one process: its round-loop record and its stage-side
record. -/
abbrev ProcRec (n : ℕ) : Type := ProcRecP n (StageRec n)

/-! ### The network adversary's ghost -/

/-- The adversary's record for one round: the first gather's frozen core, the
second gather's frozen core, and the round's bound bit. No program reads
it. -/
abbrev Ghost (n : ℕ) : Type :=
  Option (APSet n Bool) × Option (APSet n (Option Bool)) × Option Bool

instance instInhabitedGhost (n : ℕ) : Inhabited (Ghost n) := ⟨(none, none, none)⟩

/-- The state of the network adversary. -/
abbrev NetState (n : ℕ) : Type := NetStateP n (Msg n) (Ghost n)

section Slicing

variable {n : ℕ} {β : Type}

/-- The messages of one tag, recovered from a tagged sent family along a
partial untagging. -/
def slice (f : Msg n → Option β)
    (hf : ∀ a a' b, b ∈ f a → b ∈ f a' → a = a')
    (sent : Fin n → Finset (Msg n)) : Fin n → Finset β :=
  fun q => (sent q).filterMap f hf

theorem mem_slice {f : Msg n → Option β}
    {hf : ∀ a a' b, b ∈ f a → b ∈ f a' → a = a'}
    {sent : Fin n → Finset (Msg n)} {q : Fin n} {b : β} :
    b ∈ slice f hf sent q ↔ ∃ m ∈ sent q, f m = some b :=
  Finset.mem_filterMap f

/-- The first gather's network state messages. -/
def unGa1 : Msg n → Option (GaMsg n Bool)
  | .ga1 m => some m
  | _ => none

/-- The second gather's network state messages. -/
def unGa2 : Msg n → Option (GaMsg n (Option Bool))
  | .ga2 m => some m
  | _ => none

theorem unGa1_inj : ∀ a a' (b : GaMsg n Bool),
    b ∈ unGa1 a → b ∈ unGa1 a' → a = a' := by
  intro a a' b h h'
  cases a <;> cases a' <;> simp_all [unGa1]

theorem unGa2_inj : ∀ a a' (b : GaMsg n (Option Bool)),
    b ∈ unGa2 a → b ∈ unGa2 a' → a = a' := by
  intro a a' b h h'
  cases a <;> cases a' <;> simp_all [unGa2]

end Slicing

/-- The first gather's instance state of round `r`, read off the adversary's
tagged sent sets and its corrupted set. The local states are the initial
ones: `Gather.coreOf` reads the network state alone
(`Gather.coreOf_networkState_only`). -/
def ga1Of (P : Params) (w : NetState P.n) (r : ℕ) :
    SubState P.n (PRec P.n Bool) (GaMsg P.n Bool) :=
  (fun _ => LocalState.initial P.n _ (PRec.initial P.n Bool),
    ⟨slice unGa1 unGa1_inj (w.sent r), w.F⟩)

/-- The second gather's instance state of round `r`, read off the adversary's
tagged sent sets and its corrupted set. -/
def ga2Of (P : Params) (w : NetState P.n) (r : ℕ) :
    SubState P.n (PRec P.n (Option Bool)) (GaMsg P.n (Option Bool)) :=
  (fun _ => LocalState.initial P.n _ (PRec.initial P.n (Option Bool)),
    ⟨slice unGa2 unGa2_inj (w.sent r), w.F⟩)

/-- The ghost write: the link's broadcast of the candidate freezes the first
gather's core and the round's bound bit, a graded return freezes the second
gather's core, and every other label leaves the record where it stands. Each
field is written once. -/
noncomputable def ghostStep (P : Params) :
    NLabP P.n (Msg P.n) → NetState P.n → Ghost P.n → Ghost P.n
  | Sum.inr (.gsnd r _ (.brbIn2 _ (.init _))), w, G =>
      (some (G.1.getD (Gather.coreOf P (ga1Of P w r))), G.2.1,
        some (G.2.2.getD (GBCA.boundOfCore P
          (G.1.getD (Gather.coreOf P (ga1Of P w r))))))
  | Sum.inl (.retG r _ _ _), w, G =>
      (G.1, some (G.2.1.getD (Gather.coreOf P (ga2Of P w r))), G.2.2)
  | Sum.inr (.byzRetG r _ _ _), w, G =>
      (G.1, some (G.2.1.getD (Gather.coreOf P (ga2Of P w r))), G.2.2)
  | _, _, G => G

/-- The bound bit the round's graded returns announce: the one the ghost
holds, and the bit of the first gather's core where it holds none. -/
noncomputable def ghostOut (P : Params) (w : NetState P.n) (r : ℕ) (_id : Fin P.n)
    (_out : GbcaOut) : Bool :=
  ((w.ghostRec r).2.2).getD
    (GBCA.boundOfCore P ((w.ghostRec r).1.getD (Gather.coreOf P (ga1Of P w r))))

/-- The bit the network adversary announces on a return: `AFW.ghostOut` of the
round, and no other. This is the relation the flat reading's `ghostOut`
parameter takes at this instantiation. It is reducible, so the guard of the two
return rows is the equation itself. -/
noncomputable abbrev announcedBound (P : Params) (w : NetState P.n) (r : ℕ)
    (id : Fin P.n) (out : GbcaOut) (bnd : Bool) : Prop :=
  bnd = ghostOut P w r id out

/-! ### The receipt predicates

The flat reading has no broadcast return: a gather guard reads a `2f + 1` `VOTE`
receipt quorum on the acting process's own local state in the instance, where a
program of the composed round reads the store that instance's return wrote (D28).
Each predicate below is a count on the acting process's own record. -/

variable {P : Params}

/-- The process holds the pair `(k, v)` of the first gather: a `2f + 1`
`VOTE v` receipt quorum in the input-broadcast instance `k`. -/
def apIn1 (P : Params) (s : StageRec P.n) (k : Fin P.n) (v : Bool) : Prop :=
  2 * P.f + 1 ≤ (s.brbIn1 k).recvCount (BRB.BMsg.vote v)

/-- The process holds `q`'s bind payload of the first gather. -/
def apBind1 (P : Params) (s : StageRec P.n) (q : Fin P.n) (U : APSet P.n Bool) : Prop :=
  2 * P.f + 1 ≤ (s.brbBind1 q).recvCount (BRB.BMsg.vote U)

/-- A payload set of the first gather is approved here: every pair is held. -/
def approved1 (P : Params) (s : StageRec P.n) (A : APSet P.n Bool) : Prop :=
  ∀ p ∈ A, apIn1 P s p.1 p.2

/-- The process holds the pair `(k, v)` of the second gather. -/
def apIn2 (P : Params) (s : StageRec P.n) (k : Fin P.n) (v : Option Bool) : Prop :=
  2 * P.f + 1 ≤ (s.brbIn2 k).recvCount (BRB.BMsg.vote v)

/-- The process holds `q`'s bind payload of the second gather. -/
def apBind2 (P : Params) (s : StageRec P.n) (q : Fin P.n)
    (U : APSet P.n (Option Bool)) : Prop :=
  2 * P.f + 1 ≤ (s.brbBind2 q).recvCount (BRB.BMsg.vote U)

/-- A payload set of the second gather is approved here. -/
def approved2 (P : Params) (s : StageRec P.n) (A : APSet P.n (Option Bool)) : Prop :=
  ∀ p ∈ A, apIn2 P s p.1 p.2

/-! ### The accepted pairs

The `ECHO` payload of a gather is the sender's accepted pairs, `AP_i` of
AFW25's Algorithm 5, line 9. A gather program of the composed reading reads
them off its input store. The flat reading keeps none, so `(k, v)` is accepted
here exactly when the instance broadcasting `k`'s input has returned `v` here.
`storeIn` is that return as a function: the value on which the process's own
local state in the instance holds a `2f + 1` `VOTE` receipt quorum, and `none`
where there is no such value. `acceptedIn1` is its pairs over the first
gather's `n` input-broadcast instances, and `acceptedIn2` over the second
gather's. -/

open scoped Classical in
/-- What a broadcast instance has returned to this process: the value on which
the process's own local state in that instance holds a `2f + 1` `VOTE` receipt
quorum. -/
noncomputable def storeIn (P : Params) {X : Type} [DecidableEq X]
    (p : LocalState P.n (BRB.PState X) (BRB.BMsg X)) : Option X :=
  if h : ∃ v, 2 * P.f + 1 ≤ p.recvCount (BRB.BMsg.vote v) then some (Classical.choose h)
  else none

/-- The accepted pairs of the first gather: the pairs `(k, v)` whose
input-broadcast instance `k` has returned `v` here. -/
noncomputable def acceptedIn1 (P : Params) (s : StageRec P.n) : APSet P.n Bool :=
  Finset.univ.biUnion fun k =>
    match storeIn P (s.brbIn1 k) with
    | some v => {(k, v)}
    | none => ∅

/-- The accepted pairs of the second gather. -/
noncomputable def acceptedIn2 (P : Params) (s : StageRec P.n) : APSet P.n (Option Bool) :=
  Finset.univ.biUnion fun k =>
    match storeIn P (s.brbIn2 k) with
    | some v => {(k, v)}
    | none => ∅

/-- A pair of the first gather is accepted exactly when its input-broadcast
instance has returned its value here. -/
theorem mem_acceptedIn1 {P : Params} {s : StageRec P.n} {k : Fin P.n} {v : Bool} :
    (k, v) ∈ acceptedIn1 P s ↔ storeIn P (s.brbIn1 k) = some v := by
  constructor
  · intro h
    obtain ⟨k', -, hk'⟩ := Finset.mem_biUnion.mp h
    split at hk'
    · rename_i v' hd
      rw [Finset.mem_singleton, Prod.mk.injEq] at hk'
      obtain ⟨rfl, rfl⟩ := hk'
      exact hd
    · exact absurd hk' (by simp)
  · intro h
    refine Finset.mem_biUnion.mpr ⟨k, Finset.mem_univ k, ?_⟩
    rw [h]
    simp

/-- The same at the second gather. -/
theorem mem_acceptedIn2 {P : Params} {s : StageRec P.n} {k : Fin P.n} {v : Option Bool} :
    (k, v) ∈ acceptedIn2 P s ↔ storeIn P (s.brbIn2 k) = some v := by
  constructor
  · intro h
    obtain ⟨k', -, hk'⟩ := Finset.mem_biUnion.mp h
    split at hk'
    · rename_i v' hd
      rw [Finset.mem_singleton, Prod.mk.injEq] at hk'
      obtain ⟨rfl, rfl⟩ := hk'
      exact hd
    · exact absurd hk' (by simp)
  · intro h
    refine Finset.mem_biUnion.mpr ⟨k, Finset.mem_univ k, ?_⟩
    rw [h]
    simp

/-! ### The stage-side rows -/

/-- The stage-side rows of process `j`: the two gather instances, the `4n`
Bracha instances beneath them, the three fused rows, and the delivery. -/
inductive StageStep (P : Params) (j : Fin P.n) :
    ProcRec P.n → NLabP P.n (Msg P.n) → PMF (ProcRec P.n) → Prop
  /-- The graded-agreement call: the round loop hands its estimate to the
  round's first gather, which records it and broadcasts it through the
  process's own input-broadcast instance. The `⟨INIT, b⟩` multicast is the
  network's half. -/
  | callG (c : CoreRec P.n) (p : StageSideRec P.n) (r : ℕ) (b : Bool)
      (hh : c.corrupted = false)
      (hph : c.proc.phase = .toCallG) (hr : c.proc.round = r)
      (hterm : p.terminated = false)
      (hest : c.proc.est = some b)
      (hin : ((p.stage r).ga1.proc).input = none)
      (hbin : (((p.stage r).brbIn1 j).proc).input = none) :
      StageStep P j (c, p) (Sum.inl (.callG r j b))
        (PMF.pure (c.setProc { c.proc with phase := .awaitG },
          p.setStage r
            { (p.stage r) with
              ga1 := (p.stage r).ga1.setP
                { ((p.stage r).ga1.proc) with input := some b }
              brbIn1 := Function.update (p.stage r).brbIn1 j
                (((p.stage r).brbIn1 j).setP
                  { (((p.stage r).brbIn1 j).proc) with input := some b }) }))
  /-- The graded-agreement call against an already-called record: the round
  loop moves, the round record does not. -/
  | gcallLoop (c : CoreRec P.n) (p : StageSideRec P.n) (r : ℕ) (b : Bool)
      (hh : c.corrupted = false)
      (hph : c.proc.phase = .toCallG) (hr : c.proc.round = r)
      (hest : c.proc.est = some b)
      (hin : ((p.stage r).ga1.proc).input ≠ none) :
      StageStep P j (c, p) (Sum.inr (.gcallLoop r j b))
        (PMF.pure (c.setProc { c.proc with phase := .awaitG }, p))
  /-- The first gather's `ECHO`: the process is called and its accepted pairs
  number at least `n − f`, the source blueprint's `|AP| ≥ n − f`. The payload is
  those pairs, `T_i ← AP_i` of AFW25's Algorithm 5, line 9. -/
  | ga1Echo (c : CoreRec P.n) (p : StageSideRec P.n) (r : ℕ)
      (hh : c.corrupted = false) (hterm : p.terminated = false)
      (hin : ((p.stage r).ga1.proc).input ≠ none)
      (hcard : P.n - P.f ≤ (acceptedIn1 P (p.stage r)).card)
      (hsend : ((p.stage r).ga1.proc).sentEcho = none) :
      StageStep P j (c, p) (Sum.inr (.gsnd r j (.ga1 (.echo (acceptedIn1 P (p.stage r))))))
        (PMF.pure (c, p.setStage r
          { (p.stage r) with
            ga1 := (p.stage r).ga1.setP
              { ((p.stage r).ga1.proc) with
                sentEcho := some (acceptedIn1 P (p.stage r)) } }))
  /-- The first gather's `VOTE`: `n − f` senders' `ECHO` payloads, each held
  here and contained in the vote payload, are delivered, and the process has
  multicast its own `ECHO`. The main thread of AFW25's Algorithm 5 sends `ECHO`
  before `VOTE`. -/
  | ga1Vote (c : CoreRec P.n) (p : StageSideRec P.n) (r : ℕ) (U : APSet P.n Bool)
      (hh : c.corrupted = false) (hterm : p.terminated = false)
      (hin : ((p.stage r).ga1.proc).input ≠ none)
      (hech : ((p.stage r).ga1.proc).sentEcho ≠ none)
      (happ : approved1 P (p.stage r) U)
      (hQ : ∃ Q : Finset (Fin P.n), P.n - P.f ≤ Q.card ∧
        ∀ q ∈ Q, ∃ A, GaMsg.echo A ∈ ((p.stage r).ga1.recv q) ∧
          approved1 P (p.stage r) A ∧ A ⊆ U)
      (hsend : ((p.stage r).ga1.proc).sentVote = none) :
      StageStep P j (c, p) (Sum.inr (.gsnd r j (.ga1 (.vote U))))
        (PMF.pure (c, p.setStage r
          { (p.stage r) with
            ga1 := (p.stage r).ga1.setP
              { ((p.stage r).ga1.proc) with sentVote := some U } }))
  /-- The first gather's `BIND`: `n − f` senders' `VOTE` payloads, each held
  here and contained in the bind payload, are delivered; the payload is
  broadcast through the process's own bind-broadcast instance and written to the
  gather record. The process has multicast its own `VOTE` and has not called its
  own bind broadcast. The main thread of AFW25's Algorithm 5 sends `VOTE` before
  `BIND`, and sends `BIND` once, at line 17. -/
  | ga1Bind (c : CoreRec P.n) (p : StageSideRec P.n) (r : ℕ) (U : APSet P.n Bool)
      (hh : c.corrupted = false) (hterm : p.terminated = false)
      (hin : ((p.stage r).ga1.proc).input ≠ none)
      (hvot : ((p.stage r).ga1.proc).sentVote ≠ none)
      (hsnd : ((p.stage r).ga1.proc).sentBind = none)
      (hbc : (((p.stage r).brbBind1 j).proc).input = none)
      (happ : approved1 P (p.stage r) U)
      (hQ : ∃ Q : Finset (Fin P.n), P.n - P.f ≤ Q.card ∧
        ∀ q ∈ Q, ∃ W, GaMsg.vote W ∈ ((p.stage r).ga1.recv q) ∧
          approved1 P (p.stage r) W ∧ W ⊆ U) :
      StageStep P j (c, p) (Sum.inr (.gsnd r j (.brbBind1 j (.init U))))
        (PMF.pure (c, p.setStage r
          { (p.stage r) with
            ga1 := (p.stage r).ga1.setP
              { ((p.stage r).ga1.proc) with sentBind := some U }
            brbBind1 := Function.update (p.stage r).brbBind1 j
              (((p.stage r).brbBind1 j).setP
                { (((p.stage r).brbBind1 j).proc) with input := some U }) }))
  /-- The second gather's `ECHO`. -/
  | ga2Echo (c : CoreRec P.n) (p : StageSideRec P.n) (r : ℕ)
      (hh : c.corrupted = false) (hterm : p.terminated = false)
      (hin : ((p.stage r).ga2.proc).input ≠ none)
      (hcard : P.n - P.f ≤ (acceptedIn2 P (p.stage r)).card)
      (hsend : ((p.stage r).ga2.proc).sentEcho = none) :
      StageStep P j (c, p) (Sum.inr (.gsnd r j (.ga2 (.echo (acceptedIn2 P (p.stage r))))))
        (PMF.pure (c, p.setStage r
          { (p.stage r) with
            ga2 := (p.stage r).ga2.setP
              { ((p.stage r).ga2.proc) with
                sentEcho := some (acceptedIn2 P (p.stage r)) } }))
  /-- The second gather's `VOTE`. -/
  | ga2Vote (c : CoreRec P.n) (p : StageSideRec P.n) (r : ℕ)
      (U : APSet P.n (Option Bool))
      (hh : c.corrupted = false) (hterm : p.terminated = false)
      (hin : ((p.stage r).ga2.proc).input ≠ none)
      (hech : ((p.stage r).ga2.proc).sentEcho ≠ none)
      (happ : approved2 P (p.stage r) U)
      (hQ : ∃ Q : Finset (Fin P.n), P.n - P.f ≤ Q.card ∧
        ∀ q ∈ Q, ∃ A, GaMsg.echo A ∈ ((p.stage r).ga2.recv q) ∧
          approved2 P (p.stage r) A ∧ A ⊆ U)
      (hsend : ((p.stage r).ga2.proc).sentVote = none) :
      StageStep P j (c, p) (Sum.inr (.gsnd r j (.ga2 (.vote U))))
        (PMF.pure (c, p.setStage r
          { (p.stage r) with
            ga2 := (p.stage r).ga2.setP
              { ((p.stage r).ga2.proc) with sentVote := some U } }))
  /-- The second gather's `BIND`. -/
  | ga2Bind (c : CoreRec P.n) (p : StageSideRec P.n) (r : ℕ)
      (U : APSet P.n (Option Bool))
      (hh : c.corrupted = false) (hterm : p.terminated = false)
      (hin : ((p.stage r).ga2.proc).input ≠ none)
      (hvot : ((p.stage r).ga2.proc).sentVote ≠ none)
      (hsnd : ((p.stage r).ga2.proc).sentBind = none)
      (hbc : (((p.stage r).brbBind2 j).proc).input = none)
      (happ : approved2 P (p.stage r) U)
      (hQ : ∃ Q : Finset (Fin P.n), P.n - P.f ≤ Q.card ∧
        ∀ q ∈ Q, ∃ W, GaMsg.vote W ∈ ((p.stage r).ga2.recv q) ∧
          approved2 P (p.stage r) W ∧ W ⊆ U) :
      StageStep P j (c, p) (Sum.inr (.gsnd r j (.brbBind2 j (.init U))))
        (PMF.pure (c, p.setStage r
          { (p.stage r) with
            ga2 := (p.stage r).ga2.setP
              { ((p.stage r).ga2.proc) with sentBind := some U }
            brbBind2 := Function.update (p.stage r).brbBind2 j
              (((p.stage r).brbBind2 j).setP
                { (((p.stage r).brbBind2 j).proc) with input := some U }) }))
  /-- The first gather returns and the process calls the second gather with
  the candidate, broadcasting it through its own input-broadcast instance of
  the second gather (D24, D28). The returner has called its own bind broadcast:
  the `BIND` broadcast of AFW25's Algorithm 5, line 17, precedes the wait of
  line 18. -/
  | link (c : CoreRec P.n) (p : StageSideRec P.n) (r : ℕ)
      (g : Fin P.n → Option Bool)
      (hh : c.corrupted = false) (hterm : p.terminated = false)
      (hin : ((p.stage r).ga1.proc).input ≠ none)
      (hbind : ((p.stage r).ga1.proc).sentBind ≠ none)
      (hsubap : ∀ k x, g k = some x → apIn1 P (p.stage r) k x)
      (hQ : ∃ Q : Finset (Fin P.n), P.n - P.f ≤ Q.card ∧
        ∀ q ∈ Q, ∃ U, apBind1 P (p.stage r) q U ∧ APSet.subMap U g)
      (hr1 : ((p.stage r).ga1.proc).returned = false)
      (hin2 : ((p.stage r).ga2.proc).input = none)
      (hbin2 : (((p.stage r).brbIn2 j).proc).input = none) :
      StageStep P j (c, p)
        (Sum.inr (.gsnd r j (.brbIn2 j (.init (GBCA.cand P g)))))
        (PMF.pure (c, p.setStage r
          { (p.stage r) with
            ga1 := (p.stage r).ga1.setP
              { ((p.stage r).ga1.proc) with returned := true }
            ga2 := (p.stage r).ga2.setP
              { ((p.stage r).ga2.proc) with input := some (GBCA.cand P g) }
            brbIn2 := Function.update (p.stage r).brbIn2 j
              (((p.stage r).brbIn2 j).setP
                { (((p.stage r).brbIn2 j).proc) with
                  input := some (GBCA.cand P g) }) }))
  /-- The second gather returns and the round returns the graded outcome
  (D24). The returner has called its own bind broadcast. -/
  | retG (c : CoreRec P.n) (p : StageSideRec P.n) (r : ℕ)
      (g : Fin P.n → Option (Option Bool)) (bnd : Bool)
      (hh : c.corrupted = false)
      (hph : c.proc.phase = .awaitG) (hr : c.proc.round = r)
      (hterm : p.terminated = false)
      (hin : ((p.stage r).ga2.proc).input ≠ none)
      (hbind : ((p.stage r).ga2.proc).sentBind ≠ none)
      (hsubap : ∀ k x, g k = some x → apIn2 P (p.stage r) k x)
      (hQ : ∃ Q : Finset (Fin P.n), P.n - P.f ≤ Q.card ∧
        ∀ q ∈ Q, ∃ U, apBind2 P (p.stage r) q U ∧ APSet.subMap U g)
      (hr2 : ((p.stage r).ga2.proc).returned = false) :
      StageStep P j (c, p) (Sum.inl (.retG r j (GBCA.gradeOf P g) bnd))
        (PMF.pure (c.setProc { c.proc with
            est := (GBCA.gradeOf P g).est, lastGrade := some (GBCA.gradeOf P g),
            phase := .toCallW },
          p.setStage r
            { (p.stage r) with
              ga2 := (p.stage r).ga2.setP
                { ((p.stage r).ga2.proc) with returned := true } }))
  /-- `ECHO` in an input-broadcast instance of the first gather: the leader's
  `⟨INIT, m⟩` is delivered here, or an `ECHO m` receipt quorum is, or `f + 1`
  `VOTE m` receipts are; no `ECHO` is out. -/
  | in1Echo (c : CoreRec P.n) (p : StageSideRec P.n) (r : ℕ) (i : Fin P.n)
      (m : Bool) (hh : c.corrupted = false) (hterm : p.terminated = false)
      (hrecv : BRB.BMsg.init m ∈ ((p.stage r).brbIn1 i).recv i ∨
        P.echoQuorum ≤ ((p.stage r).brbIn1 i).recvCount (.echo m) ∨
        P.f + 1 ≤ ((p.stage r).brbIn1 i).recvCount (.vote m))
      (hsend : (((p.stage r).brbIn1 i).proc).sentEcho = none) :
      StageStep P j (c, p) (Sum.inr (.gsnd r j (.brbIn1 i (.echo m))))
        (PMF.pure (c, p.setStage r
          { (p.stage r) with
            brbIn1 := Function.update (p.stage r).brbIn1 i
              (((p.stage r).brbIn1 i).setP
                { (((p.stage r).brbIn1 i).proc) with sentEcho := some m }) }))
  /-- `VOTE` on an `ECHO m` receipt quorum in an input-broadcast instance of the
  first gather. -/
  | in1VoteQuorum (c : CoreRec P.n) (p : StageSideRec P.n) (r : ℕ) (i : Fin P.n)
      (m : Bool) (hh : c.corrupted = false) (hterm : p.terminated = false)
      (hcnt : P.echoQuorum ≤ ((p.stage r).brbIn1 i).recvCount (.echo m))
      (hsend : (((p.stage r).brbIn1 i).proc).sentVote = none) :
      StageStep P j (c, p) (Sum.inr (.gsnd r j (.brbIn1 i (.vote m))))
        (PMF.pure (c, p.setStage r
          { (p.stage r) with
            brbIn1 := Function.update (p.stage r).brbIn1 i
              (((p.stage r).brbIn1 i).setP
                { (((p.stage r).brbIn1 i).proc) with sentVote := some m }) }))
  /-- `VOTE` by amplification, on `f + 1` `VOTE` receipts. -/
  | in1VoteAmp (c : CoreRec P.n) (p : StageSideRec P.n) (r : ℕ) (i : Fin P.n)
      (m : Bool) (hh : c.corrupted = false) (hterm : p.terminated = false)
      (hcnt : P.f + 1 ≤ ((p.stage r).brbIn1 i).recvCount (.vote m))
      (hsend : (((p.stage r).brbIn1 i).proc).sentVote = none) :
      StageStep P j (c, p) (Sum.inr (.gsnd r j (.brbIn1 i (.vote m))))
        (PMF.pure (c, p.setStage r
          { (p.stage r) with
            brbIn1 := Function.update (p.stage r).brbIn1 i
              (((p.stage r).brbIn1 i).setP
                { (((p.stage r).brbIn1 i).proc) with sentVote := some m }) }))
  /-- `ECHO` in a bind-broadcast instance of the first gather. -/
  | bind1Echo (c : CoreRec P.n) (p : StageSideRec P.n) (r : ℕ) (i : Fin P.n)
      (m : APSet P.n Bool) (hh : c.corrupted = false) (hterm : p.terminated = false)
      (hrecv : BRB.BMsg.init m ∈ ((p.stage r).brbBind1 i).recv i ∨
        P.echoQuorum ≤ ((p.stage r).brbBind1 i).recvCount (.echo m) ∨
        P.f + 1 ≤ ((p.stage r).brbBind1 i).recvCount (.vote m))
      (hsend : (((p.stage r).brbBind1 i).proc).sentEcho = none) :
      StageStep P j (c, p) (Sum.inr (.gsnd r j (.brbBind1 i (.echo m))))
        (PMF.pure (c, p.setStage r
          { (p.stage r) with
            brbBind1 := Function.update (p.stage r).brbBind1 i
              (((p.stage r).brbBind1 i).setP
                { (((p.stage r).brbBind1 i).proc) with sentEcho := some m }) }))
  /-- `VOTE` on an `ECHO m` receipt quorum in a bind-broadcast instance of the
  first gather. -/
  | bind1VoteQuorum (c : CoreRec P.n) (p : StageSideRec P.n) (r : ℕ) (i : Fin P.n)
      (m : APSet P.n Bool) (hh : c.corrupted = false) (hterm : p.terminated = false)
      (hcnt : P.echoQuorum ≤ ((p.stage r).brbBind1 i).recvCount (.echo m))
      (hsend : (((p.stage r).brbBind1 i).proc).sentVote = none) :
      StageStep P j (c, p) (Sum.inr (.gsnd r j (.brbBind1 i (.vote m))))
        (PMF.pure (c, p.setStage r
          { (p.stage r) with
            brbBind1 := Function.update (p.stage r).brbBind1 i
              (((p.stage r).brbBind1 i).setP
                { (((p.stage r).brbBind1 i).proc) with sentVote := some m }) }))
  /-- `VOTE` by amplification in a bind-broadcast instance of the first
  gather. -/
  | bind1VoteAmp (c : CoreRec P.n) (p : StageSideRec P.n) (r : ℕ) (i : Fin P.n)
      (m : APSet P.n Bool) (hh : c.corrupted = false) (hterm : p.terminated = false)
      (hcnt : P.f + 1 ≤ ((p.stage r).brbBind1 i).recvCount (.vote m))
      (hsend : (((p.stage r).brbBind1 i).proc).sentVote = none) :
      StageStep P j (c, p) (Sum.inr (.gsnd r j (.brbBind1 i (.vote m))))
        (PMF.pure (c, p.setStage r
          { (p.stage r) with
            brbBind1 := Function.update (p.stage r).brbBind1 i
              (((p.stage r).brbBind1 i).setP
                { (((p.stage r).brbBind1 i).proc) with sentVote := some m }) }))
  /-- `ECHO` in an input-broadcast instance of the second gather. -/
  | in2Echo (c : CoreRec P.n) (p : StageSideRec P.n) (r : ℕ) (i : Fin P.n)
      (m : Option Bool) (hh : c.corrupted = false) (hterm : p.terminated = false)
      (hrecv : BRB.BMsg.init m ∈ ((p.stage r).brbIn2 i).recv i ∨
        P.echoQuorum ≤ ((p.stage r).brbIn2 i).recvCount (.echo m) ∨
        P.f + 1 ≤ ((p.stage r).brbIn2 i).recvCount (.vote m))
      (hsend : (((p.stage r).brbIn2 i).proc).sentEcho = none) :
      StageStep P j (c, p) (Sum.inr (.gsnd r j (.brbIn2 i (.echo m))))
        (PMF.pure (c, p.setStage r
          { (p.stage r) with
            brbIn2 := Function.update (p.stage r).brbIn2 i
              (((p.stage r).brbIn2 i).setP
                { (((p.stage r).brbIn2 i).proc) with sentEcho := some m }) }))
  /-- `VOTE` on an `ECHO m` receipt quorum in an input-broadcast instance of the
  second gather. -/
  | in2VoteQuorum (c : CoreRec P.n) (p : StageSideRec P.n) (r : ℕ) (i : Fin P.n)
      (m : Option Bool) (hh : c.corrupted = false) (hterm : p.terminated = false)
      (hcnt : P.echoQuorum ≤ ((p.stage r).brbIn2 i).recvCount (.echo m))
      (hsend : (((p.stage r).brbIn2 i).proc).sentVote = none) :
      StageStep P j (c, p) (Sum.inr (.gsnd r j (.brbIn2 i (.vote m))))
        (PMF.pure (c, p.setStage r
          { (p.stage r) with
            brbIn2 := Function.update (p.stage r).brbIn2 i
              (((p.stage r).brbIn2 i).setP
                { (((p.stage r).brbIn2 i).proc) with sentVote := some m }) }))
  /-- `VOTE` by amplification in an input-broadcast instance of the second
  gather. -/
  | in2VoteAmp (c : CoreRec P.n) (p : StageSideRec P.n) (r : ℕ) (i : Fin P.n)
      (m : Option Bool) (hh : c.corrupted = false) (hterm : p.terminated = false)
      (hcnt : P.f + 1 ≤ ((p.stage r).brbIn2 i).recvCount (.vote m))
      (hsend : (((p.stage r).brbIn2 i).proc).sentVote = none) :
      StageStep P j (c, p) (Sum.inr (.gsnd r j (.brbIn2 i (.vote m))))
        (PMF.pure (c, p.setStage r
          { (p.stage r) with
            brbIn2 := Function.update (p.stage r).brbIn2 i
              (((p.stage r).brbIn2 i).setP
                { (((p.stage r).brbIn2 i).proc) with sentVote := some m }) }))
  /-- `ECHO` in a bind-broadcast instance of the second gather. -/
  | bind2Echo (c : CoreRec P.n) (p : StageSideRec P.n) (r : ℕ) (i : Fin P.n)
      (m : APSet P.n (Option Bool)) (hh : c.corrupted = false)
      (hterm : p.terminated = false)
      (hrecv : BRB.BMsg.init m ∈ ((p.stage r).brbBind2 i).recv i ∨
        P.echoQuorum ≤ ((p.stage r).brbBind2 i).recvCount (.echo m) ∨
        P.f + 1 ≤ ((p.stage r).brbBind2 i).recvCount (.vote m))
      (hsend : (((p.stage r).brbBind2 i).proc).sentEcho = none) :
      StageStep P j (c, p) (Sum.inr (.gsnd r j (.brbBind2 i (.echo m))))
        (PMF.pure (c, p.setStage r
          { (p.stage r) with
            brbBind2 := Function.update (p.stage r).brbBind2 i
              (((p.stage r).brbBind2 i).setP
                { (((p.stage r).brbBind2 i).proc) with sentEcho := some m }) }))
  /-- `VOTE` on an `ECHO m` receipt quorum in a bind-broadcast instance of the
  second gather. -/
  | bind2VoteQuorum (c : CoreRec P.n) (p : StageSideRec P.n) (r : ℕ) (i : Fin P.n)
      (m : APSet P.n (Option Bool)) (hh : c.corrupted = false)
      (hterm : p.terminated = false)
      (hcnt : P.echoQuorum ≤ ((p.stage r).brbBind2 i).recvCount (.echo m))
      (hsend : (((p.stage r).brbBind2 i).proc).sentVote = none) :
      StageStep P j (c, p) (Sum.inr (.gsnd r j (.brbBind2 i (.vote m))))
        (PMF.pure (c, p.setStage r
          { (p.stage r) with
            brbBind2 := Function.update (p.stage r).brbBind2 i
              (((p.stage r).brbBind2 i).setP
                { (((p.stage r).brbBind2 i).proc) with sentVote := some m }) }))
  /-- `VOTE` by amplification in a bind-broadcast instance of the second
  gather. -/
  | bind2VoteAmp (c : CoreRec P.n) (p : StageSideRec P.n) (r : ℕ) (i : Fin P.n)
      (m : APSet P.n (Option Bool)) (hh : c.corrupted = false)
      (hterm : p.terminated = false)
      (hcnt : P.f + 1 ≤ ((p.stage r).brbBind2 i).recvCount (.vote m))
      (hsend : (((p.stage r).brbBind2 i).proc).sentVote = none) :
      StageStep P j (c, p) (Sum.inr (.gsnd r j (.brbBind2 i (.vote m))))
        (PMF.pure (c, p.setStage r
          { (p.stage r) with
            brbBind2 := Function.update (p.stage r).brbBind2 i
              (((p.stage r).brbBind2 i).setP
                { (((p.stage r).brbBind2 i).proc) with sentVote := some m }) }))
  /-- Delivery, receiver's half: file the message in the local state of the network state its
  tag names. Authenticity is the network's conjunct. -/
  | gdlvRecv (c : CoreRec P.n) (p : StageSideRec P.n) (r : ℕ) (k : Fin P.n)
      (m : Msg P.n) (hh : c.corrupted = false) (hterm : p.terminated = false) :
      StageStep P j (c, p) (Sum.inr (.gdlv r j k m))
        (PMF.pure (c, p.deliverTo r k m))

/-- The rows above meet the flat reading's conditions: each carries a label of
`stageOwn j`, each fires only at an unreplaced program, each is Dirac, and the
return takes the announced bit free (D29). -/
instance instIsStageTable (P : Params) :
    IsStageTable P (Msg P.n) (StageRec P.n) (StageStep P) where
  own h := by cases h <;> rfl
  honest h := by cases h <;> assumption
  dirac h := by cases h <;> exact ⟨_, rfl⟩
  bndFree h := by cases h; constructor <;> assumption

/-! ### The transposed record writes one local state at a time

A tagged delivery reaches exactly the local state its tag names and leaves every other
local state of the record where it stands. These are the facts the substitution into
the composed reading rests on, the composed side writing the same local state through
its instance-major indexing. -/

section Transposition

variable {n : ℕ}

example (s : StageRec n) (k i : Fin n) (m : BRB.BMsg Bool) :
    ((s.deliverTo k (.brbIn1 i m)).brbIn1 i).recv k
      = insert m ((s.brbIn1 i).recv k) := by
  simp [StageRec.deliverTo, LocalState.deliverTo]

example (s : StageRec n) (k i i' : Fin n) (m : BRB.BMsg Bool) (h : i' ≠ i) :
    (s.deliverTo k (.brbIn1 i m)).brbIn1 i' = s.brbIn1 i' := by
  simp [StageRec.deliverTo, Function.update_of_ne h]

example (s : StageRec n) (k i : Fin n) (m : BRB.BMsg Bool) :
    (s.deliverTo k (.brbIn1 i m)).ga1 = s.ga1 := by
  simp [StageRec.deliverTo]

example (s : StageRec n) (k : Fin n) (m : GaMsg n Bool) :
    (s.deliverTo k (.ga1 m)).ga1.recv k = insert m (s.ga1.recv k) := by
  simp [StageRec.deliverTo, LocalState.deliverTo]

example (s : StageRec n) (k : Fin n) (m : GaMsg n Bool) (i : Fin n) :
    (s.deliverTo k (.ga1 m)).brbIn1 i = s.brbIn1 i := by
  simp [StageRec.deliverTo]

example (P : Params) (p : StageSideRec P.n) (r : ℕ) (sr : StageRec P.n) :
    (p.setStage r sr).stage r = sr := by simp

end Transposition

/-! ### The protocol -/

/-- The message the graded-agreement call multicasts: the caller's input,
broadcast through the caller's own input-broadcast instance of the first
gather. -/
def gCallPayload (P : Params) : Fin P.n → Bool → Msg P.n := fun id b => .brbIn1 id (.init b)

/-- The step relation of the program of process `j`. -/
abbrev ProcStep (P : Params) (j : Fin P.n) :
    ProcRec P.n → NLabP P.n (Msg P.n) → PMF (ProcRec P.n) → Prop :=
  FlatProcStep P (Msg P.n) (StageRec P.n) (StageStep P) j

/-- The step relation of the network adversary. -/
abbrev NetStep (P : Params) :
    NetState P.n → NLabP P.n (Msg P.n) → PMF (NetState P.n) → Prop :=
  FlatNetStep P (Msg P.n) (Ghost P.n) (gCallPayload P) (ghostStep P) (announcedBound P)

/-- The state of the gather-based protocol: the process family, the network
adversary and the coin oracle. -/
abbrev ProtocolState (P : Params) : Type :=
  Implementation.FlatState P (Msg P.n) (StageRec P.n) (Ghost P.n)

/-- The three components side by side, over the extended alphabet. -/
noncomputable def protocolPre (P : Params) :
    System (ProtocolState P) (Implementation.NLabP P.n (Msg P.n)) :=
  Implementation.flatPre P (Msg P.n) (StageRec P.n) (Ghost P.n) (StageStep P)
    (gCallPayload P) (ghostStep P) (announcedBound P)

/-- The gather-based protocol group: the rendezvous alphabet hidden, the
result read back over `Lab n`. -/
noncomputable def protocolGroup (P : Params) : System (ProtocolState P) (Lab P.n) :=
  Implementation.flatGroup P (Msg P.n) (StageRec P.n) (Ghost P.n) (StageStep P)
    (gCallPayload P) (ghostStep P) (announcedBound P)

/-- **The gather-based protocol**: the group with the sub-protocol API
hidden. -/
noncomputable def protocol (P : Params) : System (ProtocolState P) (Lab P.n) :=
  Implementation.flat P (Msg P.n) (StageRec P.n) (Ghost P.n) (StageStep P)
    (gCallPayload P) (ghostStep P) (announcedBound P)

end AFW

end ABA
end PLTS
