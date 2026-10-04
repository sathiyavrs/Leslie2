/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sathiya / Claude
-/

import Leslie2Protocols.ABA.GBCA.ABDY.CompositionStepCases
import Leslie2Protocols.ABA.GBCA.SpecificationOverRoundAlphabet

/-!
# The algorithm of the round's graded-agreement composition (ABDY22 Algorithm 6)

`Algorithm` is ABDY22's Algorithm 6 as a relation on `GBCA.ByABDY.RoundState`, the composed state
of one graded-agreement round: one transition per line, over the shared alphabet `ABA.Label n`.
It is the algorithm of the round-`r` composition (`GBCA.ByABDY.composition`,
`GBCA/ABDY/Composition.lean`). The messages the round exchanges and the state it runs on are in
`GBCA/ABDY/MessagesAndVariables.lean`.

`composition_projects` is the characterisation: at a label of the round's interface, every
transition of the composition is the algorithm's transition at the specification label the
interface label projects to, one step for one step. The composition assembles `n` programs beside
the round's network, and the composed state is the pair of the round variables and the network
state, which are exactly the local states it puts together; the algorithm reads that same pair
through its own accessors.

*Attribution.* The file transcribes ABDY22's Algorithm 6 — the 6-round Graded Binding Crusader
Agreement for Byzantine faults — directly, under the level mapping

```
INPUT = echo,  ECHO = echo2,  VOTE = echo3,  BIND = echo4,  ECHO5 = echo5
```

and the three returns are the decide conditions of lines 23–29.

Each process runs the message pattern

* `INPUT b` — multicast once the call has recorded the input `b`, a transition of its own after
  the call; relayed once `f + 1` have been received;
* `ECHO b` — multicast once `INPUT b` was received from `n − f` senders
  (which also puts `b` into the derived set `Valid`);
* `VOTE v` (`v ∈ {0,1,⊥}`) — a real bit after an `n − f` `ECHO b` quorum, `⊥`
  after `n − f` `ECHO`s of any payload with `|Valid| > 1`;
* `BIND v` — the same pattern one level up, over `VOTE`s;
* `ECHO5 v` — the same pattern one level up again, over `BIND`s;
* return — grade `2` at `b` after an `n − f` `ECHO5 b` quorum, grade `1` at `b` after an
  `n − f` any-`ECHO5` quorum containing `b` with `f + 1` `BIND b`s and
  `|Valid| > 1`, and grade `0` after an `n − f` `ECHO5 ⊥` quorum with `|Valid| > 1`.

Every transition is Dirac; asynchrony and Byzantine behaviour are modelled
by nondeterministic `τ`-transitions.

## Why the cited algorithm and not the blueprint's `alg:GBCA` (D18)

* **D18 (the five message levels).** This is a deviation from the source
  blueprint's `alg:GBCA`, which presents a **4-round compression** of
  Algorithm 6: the `echo5` round is elided, the decide conditions read one level
  down, and the grade-1 witness is `f + 1` `VOTE v` where Algorithm 6 has
  `t + 1` `echo4 v`. The compression violates the paper's Graded Binding. One
  process held before its `ECHO` through a grade-0 decision can afterwards
  direct its write-once echo at either bit, and one corruption completes
  `f + 1` `VOTE v` for the bit of the adversary's choice — so two extensions of
  a single grade-0 return hand out two different bits. The encoding therefore
  follows the cited algorithm rather than the blueprint's compression; the
  upstream blueprint carries a matching red annotation.

The grade-1 witness is what the depth buys. `f + 1` received `BIND v` messages exceed
the corruption budget, so they guarantee a correct `BIND v` sender, whose own
wait-condition is an `n − f` quorum of received `VOTE v` messages over the write-once `VOTE`
level — and that quorum is the object the paper's binding argument counts
(Lemmas 4.8/4.9 through E.9).

*Transcription note.* The prose preceding Algorithm 6 says "upon receiving
`echo4` messages from `2t + 1` parties" where the pseudocode's lines 19–20 say
`n − t`; the two coincide only at `n = 3t + 1`. The encoding follows the
pseudocode (`n − f`).

## The algorithm

* **D8 (participation guard).** The protocol sends (`input`, `relay`, `echo`, `vote*`,
  `bind*`, `echo5*`) and the three returns require the process to have received
  its input (`input ≠ none`): the algorithm's handlers only run inside a called
  instance. The send transitions are taken in the wait-until order of Algorithm 6
  from the `BIND` level down: each of those transitions requires the process's own
  send at the level below. The `VOTE` transitions ask for no own send, the `ECHO`
  they read being sent by an `upon` handler that may still be pending. The
  return transitions carry the negations that the algorithm's if/else chain implies.
* **D1 (determinised `fail`).** The `fail` transition is `RoundState.corrupt`, the total
  Dirac function of `GBCA/ABDY/MessagesAndVariables.lean`.
* **D5 (set-based network).** `deliver` moves a message from a sender's sent set into a
  receiver's delivered set and does not consume it, and `byzantine` lets a corrupted sender
  multicast anything at any time.

The three return transitions are cases (1), (2), (3) of Algorithm 6's lines 23–29: case (1) an
`n − f` `ECHO5 v` quorum, case (2) an `n − f` any-`ECHO5` quorum containing `ECHO5 v` together with
`f + 1` `BIND v`s and `|Valid| > 1`, case (3) an `n − f` `ECHO5 ⊥` quorum with `|Valid| > 1`.
Beside the received messages of its own case, each return reads the messages named by the cases
above it in the chain, the process's own `ECHO5` field, and whether it has been called. The binding
and grade information that the specification tracks is an abstraction of these patterns of received
messages and lives only on the specification; the simulation relation
(`GBCA/ABDY/SpecificationRelation.lean`) supplies it from the received messages.

Each return also announces the round's bound bit (D29): the label carries
`bound.getD (boundOf sent F out)`, the recorded bit if the round has returned before and
`boundOf`'s otherwise, and the transition writes it back to `NetworkState.bound`. The three
returns are otherwise the returns of Algorithm 6 unchanged: the announced bit enters no guard of
the algorithm and no field a program holds.
-/

namespace PLTS
namespace ABA
namespace GBCA.ByABDY

open Implementation hiding NetworkEvent ExtendedLabel
open Composition

/-- The algorithm of the round-`r` composition: ABDY22's Algorithm 6 over all five message
levels, one transition per line, on the composed state. All transitions are Dirac. -/
inductive Algorithm (P : Parameters) (r : ℕ) :
    RoundState P.n → Label P.n → PMF (RoundState P.n) → Prop
  /-- The environment call arrives: record the input. -/
  | call (s : RoundState P.n) (id : Fin P.n) (b : Bool)
      (h : (s.processVariables id).input = none) :
      Algorithm P r s (.callG r id b)
        (PMF.pure (s.setProcessVariables id { s.processVariables id with input := some b }))
  /-- Input-enabledness loop for `call`. -/
  | callLoop (s : RoundState P.n) (id : Fin P.n) (b : Bool) :
      Algorithm P r s (.callG r id b) (PMF.pure s)
  /-- Asynchronous delivery: the adversary moves a multicast message into a
  receiver's delivered set. -/
  | deliver (s : RoundState P.n) (i j : Fin P.n) (m : Message) (h : m ∈ s.sent j) :
      Algorithm P r s .tau (PMF.pure (s.receiveMessage i j m))
  /-- `INPUT b`: the first multicast of the process's own input, ABDY22 Algorithm 6 line 2 and
  the first statement of LeslieBP Algorithm 2. -/
  | input (s : RoundState P.n) (j : Fin P.n) (b : Bool)
      (hin : (s.processVariables j).input = some b)
      (hsend : (s.processVariables j).sentInput b = false) :
      Algorithm P r s .tau
        (PMF.pure ((s.setProcessVariables j { s.processVariables j with
            sentInput := Function.update (s.processVariables j).sentInput b true }).multicast
          j (.input b)))
  /-- `INPUT` relay: `f + 1` received `⟨INPUT, b⟩` messages, not yet multicast. -/
  | relay (s : RoundState P.n) (j : Fin P.n) (b : Bool)
      (hin : (s.processVariables j).input ≠ none)
      (hcnt : P.f + 1 ≤ s.receivedCount j (.input b))
      (hsend : (s.processVariables j).sentInput b = false) :
      Algorithm P r s .tau
        (PMF.pure ((s.setProcessVariables j { s.processVariables j with
            sentInput := Function.update (s.processVariables j).sentInput b true }).multicast
          j (.input b)))
  /-- `ECHO`: an `n − f` `INPUT b` quorum puts `b` into `Valid` and, if no
  `ECHO` was sent yet, multicasts `⟨ECHO, b⟩`. -/
  | echo (s : RoundState P.n) (j : Fin P.n) (b : Bool)
      (hin : (s.processVariables j).input ≠ none)
      (hcnt : P.n - P.f ≤ s.receivedCount j (.input b))
      (hsend : (s.processVariables j).sentEcho = none) :
      Algorithm P r s .tau
        (PMF.pure ((s.setProcessVariables j
          { s.processVariables j with sentEcho := some b }).multicast
          j (.echo b)))
  /-- `VOTE b` (wait case (a)): an `n − f` `ECHO b` quorum. The vote reads the
  `ECHO` quorum received. The process's own `ECHO` is sent by one of the
  algorithm's `upon` handlers and may still be pending, so no own-send
  condition applies here. The wait-until order is carried from the `BIND` level
  down. -/
  | voteBit (s : RoundState P.n) (j : Fin P.n) (b : Bool)
      (hin : (s.processVariables j).input ≠ none)
      (hcnt : P.n - P.f ≤ s.receivedCount j (.echo b))
      (hsend : (s.processVariables j).sentVote = none) :
      Algorithm P r s .tau
        (PMF.pure ((s.setProcessVariables j
          { s.processVariables j with sentVote := some (some b) }).multicast
          j (.vote (some b))))
  /-- `VOTE ⊥` (wait case (b)): `n − f` `ECHO`s of any payload and
  `|Valid| > 1`, and no single-bit `ECHO` quorum among the received messages. The vote reads
  the `ECHO` quorum received. The process's own `ECHO` is sent by one of the
  algorithm's `upon` handlers and may still be pending, so no own-send
  condition applies here. The wait-until order is carried from the `BIND` level
  down. -/
  | voteBot (s : RoundState P.n) (j : Fin P.n)
      (hin : (s.processVariables j).input ≠ none)
      (hnot : ∀ b, s.receivedCount j (.echo b) < P.n - P.f)
      (hcnt : P.n - P.f ≤ s.echoCount j)
      (hval : s.bothValid P j)
      (hsend : (s.processVariables j).sentVote = none) :
      Algorithm P r s .tau
        (PMF.pure ((s.setProcessVariables j
          { s.processVariables j with sentVote := some none }).multicast
          j (.vote none)))
  /-- `BIND b` (wait case (a)): an `n − f` `VOTE b` quorum, the process's own
  `VOTE` already out. -/
  | bindBit (s : RoundState P.n) (j : Fin P.n) (b : Bool)
      (hin : (s.processVariables j).input ≠ none)
      (hlv : (s.processVariables j).sentVote ≠ none)
      (hcnt : P.n - P.f ≤ s.receivedCount j (.vote (some b)))
      (hsend : (s.processVariables j).sentBind = none) :
      Algorithm P r s .tau
        (PMF.pure ((s.setProcessVariables j
          { s.processVariables j with sentBind := some (some b) }).multicast
          j (.bind (some b))))
  /-- `BIND ⊥` (wait case (b)): `n − f` `VOTE`s of any payload and
  `|Valid| > 1`, the process's own `VOTE` already out, and no single-bit
  `VOTE` quorum among the received messages. -/
  | bindBot (s : RoundState P.n) (j : Fin P.n)
      (hin : (s.processVariables j).input ≠ none)
      (hlv : (s.processVariables j).sentVote ≠ none)
      (hnot : ∀ b, s.receivedCount j (.vote (some b)) < P.n - P.f)
      (hcnt : P.n - P.f ≤ s.voteCount j)
      (hval : s.bothValid P j)
      (hsend : (s.processVariables j).sentBind = none) :
      Algorithm P r s .tau
        (PMF.pure ((s.setProcessVariables j
          { s.processVariables j with sentBind := some none }).multicast
          j (.bind none)))
  /-- `ECHO5 b` (wait case (a)): an `n − f` `BIND b` quorum, the process's own
  `BIND` already out. -/
  | echo5Bit (s : RoundState P.n) (j : Fin P.n) (b : Bool)
      (hin : (s.processVariables j).input ≠ none)
      (hlv : (s.processVariables j).sentBind ≠ none)
      (hcnt : P.n - P.f ≤ s.receivedCount j (.bind (some b)))
      (hsend : (s.processVariables j).sentEcho5 = none) :
      Algorithm P r s .tau
        (PMF.pure ((s.setProcessVariables j
          { s.processVariables j with sentEcho5 := some (some b) }).multicast
          j (.echo5 (some b))))
  /-- `ECHO5 ⊥` (wait case (b)): `n − f` `BIND`s of any payload and
  `|Valid| > 1`, the process's own `BIND` already out, and no single-bit
  `BIND` quorum among the received messages. -/
  | echo5Bot (s : RoundState P.n) (j : Fin P.n)
      (hin : (s.processVariables j).input ≠ none)
      (hlv : (s.processVariables j).sentBind ≠ none)
      (hnot : ∀ b, s.receivedCount j (.bind (some b)) < P.n - P.f)
      (hcnt : P.n - P.f ≤ s.bindCount j)
      (hval : s.bothValid P j)
      (hsend : (s.processVariables j).sentEcho5 = none) :
      Algorithm P r s .tau
        (PMF.pure ((s.setProcessVariables j
          { s.processVariables j with sentEcho5 := some none }).multicast
          j (.echo5 none)))
  /-- Byzantine injection: a corrupted sender multicasts anything. -/
  | byzantine (s : RoundState P.n) (j : Fin P.n) (m : Message) (h : j ∈ s.F) :
      Algorithm P r s .tau (PMF.pure (s.multicast j m))
  /-- Grade-2 return (decide case (1)): an `n − f` `ECHO5 v` quorum. The process
  has called and its own `ECHO5` is out. Case (1) heads the chain, so there is
  no higher case to deny. -/
  | retGrade2 (s : RoundState P.n) (id : Fin P.n) (v : Bool) (bnd : Bool)
      (hin : (s.processVariables id).input ≠ none)
      (hlv : (s.processVariables id).sentEcho5 ≠ none)
      (hcnt : P.n - P.f ≤ s.receivedCount id (.echo5 (some v)))
      (hr : (s.processVariables id).returned = false)
      (hbnd : bnd = s.bound.getD (boundOf s.sent s.F (.grade2 v))) :
      Algorithm P r s (.retG r id (.grade2 v) bnd)
        (PMF.pure ((s.setProcessVariables id
          { s.processVariables id with returned := true }).setBound bnd))
  /-- Grade-1 return (decide case (2)): an `n − f` any-`ECHO5` quorum containing
  `ECHO5 v`, `f + 1` `BIND v`s and `|Valid| > 1`. The `f + 1` received `BIND v` messages
  put a correct `BIND v` sender — hence an `n − f` quorum of received `VOTE v` messages —
  behind every grade-1 output. The process has called, its own `ECHO5` is out,
  and no higher case holds: `hnotGrade2` denies case (1) at either bit. -/
  | retGrade1 (s : RoundState P.n) (id : Fin P.n) (v : Bool) (bnd : Bool)
      (hin : (s.processVariables id).input ≠ none)
      (hlv : (s.processVariables id).sentEcho5 ≠ none)
      (hnotGrade2 : ∀ v, s.receivedCount id (.echo5 (some v)) < P.n - P.f)
      (hcnt : P.n - P.f ≤ s.echo5Count id)
      (honce : ∃ k, Message.echo5 (some v) ∈ s.received id k)
      (hbind : P.f + 1 ≤ s.receivedCount id (.bind (some v)))
      (hval : s.bothValid P id)
      (hr : (s.processVariables id).returned = false)
      (hbnd : bnd = s.bound.getD (boundOf s.sent s.F (.grade1 v))) :
      Algorithm P r s (.retG r id (.grade1 v) bnd)
        (PMF.pure ((s.setProcessVariables id
          { s.processVariables id with returned := true }).setBound bnd))
  /-- Grade-0 return (decide case (3)): an `n − f` `ECHO5 ⊥` quorum and
  `|Valid| > 1`. The process has called, its own `ECHO5` is out, and no higher
  case holds: `hnotGrade2` denies case (1) at either bit, and `hnotGrade1` denies
  case (2). The denial of case (2) is carried in reduced form. Case (2) asks
  for four things at a bit `v`: an `n − f` any-`ECHO5` quorum, a received
  `ECHO5 v`, `f + 1` received `BIND v` messages, and `|Valid| > 1`. This transition's own
  `hcnt` and `hval` already supply the first and the last, an `n − f`
  `ECHO5 ⊥` quorum being in particular an `n − f` any-`ECHO5` quorum. What is
  left to deny is the pair of the received `ECHO5 v` and the `f + 1` received
  `BIND v` messages, which is what `hnotGrade1` states. -/
  | retGrade0 (s : RoundState P.n) (id : Fin P.n) (bnd : Bool)
      (hin : (s.processVariables id).input ≠ none)
      (hlv : (s.processVariables id).sentEcho5 ≠ none)
      (hnotGrade2 : ∀ v, s.receivedCount id (.echo5 (some v)) < P.n - P.f)
      (hnotGrade1 : ∀ v, (∃ k, Message.echo5 (some v) ∈ s.received id k) →
        s.receivedCount id (.bind (some v)) < P.f + 1)
      (hcnt : P.n - P.f ≤ s.receivedCount id (.echo5 none))
      (hval : s.bothValid P id)
      (hr : (s.processVariables id).returned = false)
      (hbnd : bnd = s.bound.getD (boundOf s.sent s.F .grade0)) :
      Algorithm P r s (.retG r id .grade0 bnd)
        (PMF.pure ((s.setProcessVariables id
          { s.processVariables id with returned := true }).setBound bnd))
  /-- Corruption (deviation D1). -/
  | fail (s : RoundState P.n) (id : Fin P.n) :
      Algorithm P r s (.fail id) (PMF.pure (s.corrupt P id))

/-! ### The composition's transitions are the algorithm's

Every transition of the round's composition is one transition of the algorithm at the same state,
and the correspondence is strong — one step matches one step, at the specification label the
interface label projects to, with no stuttering anywhere:

| the composition | the algorithm |
| --- | --- |
| `callG` (caller writes) | `Algorithm.call` |
| `gbcaCallLoop`, `byzantineCallGLoop` | `Algorithm.callLoop` |
| `byzantineCallG` (D11) | `Algorithm.call` |
| `retG` / `byzantineRetG`, by grade | `Algorithm.retGrade2` / `retGrade1` / `retGrade0` |
| hidden `send` synchronisation, by level | the nine silent send transitions |
| hidden `deliver` synchronisation | `Algorithm.deliver` |
| network-local injection | `Algorithm.byzantine` |

The two hidden synchronisations and the network's injection are silent in the composition and in the
algorithm alike, and `specificationLabelMap` takes `τ` to `τ`. -/

/-- **The algorithm of the composition.** At a label of the round's interface, every transition of
the composition is the algorithm's transition at the specification label the interface label
projects to. -/
theorem composition_projects (P : Parameters) (r : ℕ) :
    ∀ (σ : GBCA.ByABDY.RoundState P.n) (l : ExtendedLabel P.n Message)
    (μ : PMF (GBCA.ByABDY.RoundState P.n)), (composition P r).step σ l μ → ∃ l₀,
    specificationLabelMap P.n l = some l₀ ∧ Algorithm P r σ l₀ μ := by
  rintro ⟨u, w⟩ l μ hstep
  rcases (composition_step_iff P r (u, w) l μ).mp hstep with ⟨rfl, e, hev⟩ | hlab
  · -- a hidden synchronisation: a silent transition of the algorithm
    obtain ⟨x, w', rfl, hall, hn⟩ := compositionExtended_synchronised_cases (by simp) hev
    refine ⟨Label.tau, rfl, ?_⟩
    cases e with
    | send j m =>
      have hfor : ∀ i, i ≠ j → x i = u i :=
        fun i hi => PMF.pure_injective (gbcaProgramStep_send_notOwn (Ne.symm hi) (hall i))
      have hw : w' = w.recordGBCASend j m := PMF.pure_injective (gbcaNetworkStep_send hn)
      subst hw
      cases m with
      | input b =>
        obtain ⟨hcase, hsend, hx⟩ := gbcaProgramStep_send_input_own (hall j)
        rw [composition_setProcessVariables_recordGBCASend (PMF.pure_injective hx) hfor]
        rcases hcase with hin | ⟨hin, hcnt⟩
        · exact Algorithm.input _ j b hin hsend
        · exact Algorithm.relay _ j b hin hcnt hsend
      | echo b =>
        obtain ⟨hin, hcnt, hsend, hx⟩ := gbcaProgramStep_send_echo_own (hall j)
        rw [composition_setProcessVariables_recordGBCASend (PMF.pure_injective hx) hfor]
        exact Algorithm.echo _ j b hin hcnt hsend
      | vote v =>
        cases v with
        | some b =>
          obtain ⟨hin, hcnt, hsend, hx⟩ := gbcaProgramStep_send_voteBit_own (hall j)
          rw [composition_setProcessVariables_recordGBCASend (PMF.pure_injective hx) hfor]
          exact Algorithm.voteBit _ j b hin hcnt hsend
        | none =>
          obtain ⟨hin, hnot, hcnt, hval, hsend, hx⟩ :=
            gbcaProgramStep_send_voteBot_own (hall j)
          rw [composition_setProcessVariables_recordGBCASend (PMF.pure_injective hx) hfor]
          exact Algorithm.voteBot _ j hin hnot hcnt hval hsend
      | bind v =>
        cases v with
        | some b =>
          obtain ⟨hin, hlv, hcnt, hsend, hx⟩ := gbcaProgramStep_send_bindBit_own (hall j)
          rw [composition_setProcessVariables_recordGBCASend (PMF.pure_injective hx) hfor]
          exact Algorithm.bindBit _ j b hin hlv hcnt hsend
        | none =>
          obtain ⟨hin, hlv, hnot, hcnt, hval, hsend, hx⟩ :=
            gbcaProgramStep_send_bindBot_own (hall j)
          rw [composition_setProcessVariables_recordGBCASend (PMF.pure_injective hx) hfor]
          exact Algorithm.bindBot _ j hin hlv hnot hcnt hval hsend
      | «echo5» v =>
        cases v with
        | some b =>
          obtain ⟨hin, hlv, hcnt, hsend, hx⟩ := gbcaProgramStep_send_echo5Bit_own (hall j)
          rw [composition_setProcessVariables_recordGBCASend (PMF.pure_injective hx) hfor]
          exact Algorithm.echo5Bit _ j b hin hlv hcnt hsend
        | none =>
          obtain ⟨hin, hlv, hnot, hcnt, hval, hsend, hx⟩ :=
            gbcaProgramStep_send_echo5Bot_own (hall j)
          rw [composition_setProcessVariables_recordGBCASend (PMF.pure_injective hx) hfor]
          exact Algorithm.echo5Bot _ j hin hlv hnot hcnt hval hsend
    | deliver i j m =>
      obtain ⟨hmem, hw⟩ := gbcaNetworkStep_deliver hn
      have hw' : w' = w := PMF.pure_injective hw
      subst hw'
      have hfor : ∀ i', i' ≠ i → x i' = u i' :=
        fun i' hi' => PMF.pure_injective (gbcaProgramStep_deliver_notOwn (Ne.symm hi') (hall i'))
      rw [composition_deliver (PMF.pure_injective (gbcaProgramStep_deliver_own (hall i))) hfor]
      exact Algorithm.deliver _ i j m hmem
  · by_cases hlτ : l = Sum.inl Label.tau
    · -- the network's own injection
      subst hlτ
      obtain ⟨w', rfl, hn⟩ := compositionExtended_tau_cases hlab
      obtain ⟨k, m, hF, hw⟩ := gbcaNetworkStep_tau hn
      have hw' : w' = w.recordGBCASend k m := PMF.pure_injective hw
      subst hw'
      refine ⟨Label.tau, rfl, ?_⟩
      rw [composition_recordGBCASend]
      exact Algorithm.byzantine _ k m hF
    · obtain ⟨x, w', rfl, hall, hn⟩ := compositionExtended_synchronised_cases (by simpa using hlτ)
        hlab
      cases l with
      | inl l₀ =>
        cases l₀ with
        | tau => exact absurd rfl hlτ
        | callABA id b => exact (gbcaNetworkStep_callABA_noStep hn).elim
        | retABA id b => exact (gbcaNetworkStep_retABA_noStep hn).elim
        | callW r' id => exact (gbcaNetworkStep_callW_noStep hn).elim
        | retW r' id b => exact (gbcaNetworkStep_retW_noStep hn).elim
        | fail k => exact (gbcaNetworkStep_fail_noStep hn).elim
        | callG r' id b =>
          obtain ⟨rfl, hw⟩ := gbcaNetworkStep_callG_round hn
          have hw' : w' = w := PMF.pure_injective hw
          subst hw'
          obtain ⟨hin, hx⟩ := gbcaProgramStep_callG_own (hall id)
          have hfor : ∀ i, i ≠ id → x i = u i :=
            fun i hi => PMF.pure_injective (gbcaProgramStep_callG_notOwn (Ne.symm hi) (hall i))
          refine ⟨_, rfl, ?_⟩
          rw [composition_setProcessVariables (PMF.pure_injective hx) hfor]
          exact Algorithm.call _ id b hin
        | retG r' id out bnd =>
          obtain ⟨rfl, hbnd, hw⟩ := gbcaNetworkStep_retG_round hn
          have hw' : w' = w.setBound bnd := PMF.pure_injective hw
          subst hw'
          have hfor : ∀ i, i ≠ id → x i = u i :=
            fun i hi => PMF.pure_injective (gbcaProgramStep_retG_notOwn (Ne.symm hi) (hall i))
          refine ⟨_, rfl, ?_⟩
          cases out with
          | grade2 v =>
            obtain ⟨hin, hlv, hcnt, hret, hx⟩ := gbcaProgramStep_retGGrade2_own (hall id)
            rw [composition_setProcessVariables_setBound (PMF.pure_injective hx) hfor]
            exact Algorithm.retGrade2 _ id v bnd hin hlv hcnt hret hbnd
          | grade1 v =>
            obtain ⟨hin, hlv, hnotGrade2, hcnt, honce, hbind, hval, hret, hx⟩ :=
              gbcaProgramStep_retGGrade1_own (hall id)
            rw [composition_setProcessVariables_setBound (PMF.pure_injective hx) hfor]
            exact Algorithm.retGrade1 _ id v bnd hin hlv hnotGrade2 hcnt honce
              hbind hval
              hret hbnd
          | grade0 =>
            obtain ⟨hin, hlv, hnotGrade2, hnotGrade1, hcnt, hval, hret, hx⟩ :=
              gbcaProgramStep_retGGrade0_own (hall id)
            rw [composition_setProcessVariables_setBound (PMF.pure_injective hx) hfor]
            exact Algorithm.retGrade0 _ id bnd hin hlv hnotGrade2 hnotGrade1
              hcnt hval hret
              hbnd
      | inr ev =>
        cases ev with
        | gbcaRoundEvent r' j e => exact e.elim
        | gbcaSend r' j m => exact (gbcaNetworkStep_gbcaSend_noStep hn).elim
        | gbcaDeliver r' i j m => exact (gbcaNetworkStep_gbcaDeliver_noStep hn).elim
        | decidedRelay j b => exact (gbcaNetworkStep_decidedRelay_noStep hn).elim
        | decidedDeliver i j b => exact (gbcaNetworkStep_decidedDeliver_noStep hn).elim
        | decidedSend j b => exact (gbcaNetworkStep_decidedSend_noStep hn).elim
        | byzantineCallW r' k => exact (gbcaNetworkStep_byzantineCallW_noStep hn).elim
        | byzantineRetW r' k b => exact (gbcaNetworkStep_byzantineRetW_noStep hn).elim
        | gbcaCallLoop r' id b =>
          obtain ⟨rfl, hw⟩ := gbcaNetworkStep_gbcaCallLoop_round hn
          have hw' : w' = w := PMF.pure_injective hw
          subst hw'
          have hidle : ∀ i,
            x i = u i := fun i => PMF.pure_injective (gbcaProgramStep_gbcaCallLoop (hall i))
          refine ⟨_, rfl, ?_⟩
          rw [composition_idle hidle]
          exact Algorithm.callLoop _ id b
        | byzantineCallG r' k b =>
          obtain ⟨rfl, hw⟩ := gbcaNetworkStep_byzantineCallG_round hn
          have hw' : w' = w := PMF.pure_injective hw
          subst hw'
          obtain ⟨hin, hx⟩ := gbcaProgramStep_byzantineCallG_own (hall k)
          have hfor : ∀ i, i ≠ k → x i = u i :=
            fun i hi => PMF.pure_injective (gbcaProgramStep_byzantineCallG_notOwn (Ne.symm hi)
              (hall i))
          refine ⟨_, rfl, ?_⟩
          rw [composition_setProcessVariables (PMF.pure_injective hx) hfor]
          exact Algorithm.call _ k b hin
        | byzantineCallGLoop r' k b =>
          obtain ⟨rfl, hw⟩ := gbcaNetworkStep_byzantineCallGLoop_round hn
          have hw' : w' = w := PMF.pure_injective hw
          subst hw'
          have hidle : ∀ i, x i = u i :=
            fun i => PMF.pure_injective (gbcaProgramStep_byzantineCallGLoop (hall i))
          refine ⟨_, rfl, ?_⟩
          rw [composition_idle hidle]
          exact Algorithm.callLoop _ k b
        | byzantineRetG r' k out bnd =>
          obtain ⟨rfl, hbnd, hw⟩ := gbcaNetworkStep_byzantineRetG_round hn
          have hw' : w' = w.setBound bnd := PMF.pure_injective hw
          subst hw'
          have hfor : ∀ i, i ≠ k → x i = u i :=
            fun i hi => PMF.pure_injective (gbcaProgramStep_byzantineRetG_notOwn (Ne.symm hi) (hall
              i))
          refine ⟨_, rfl, ?_⟩
          cases out with
          | grade2 v =>
            obtain ⟨hin, hlv, hcnt, hret, hx⟩ := gbcaProgramStep_byzantineRetGGrade2_own (hall k)
            rw [composition_setProcessVariables_setBound (PMF.pure_injective hx) hfor]
            exact Algorithm.retGrade2 _ k v bnd hin hlv hcnt hret hbnd
          | grade1 v =>
            obtain ⟨hin, hlv, hnotGrade2, hcnt, honce, hbind, hval, hret, hx⟩ :=
              gbcaProgramStep_byzantineRetGGrade1_own (hall k)
            rw [composition_setProcessVariables_setBound (PMF.pure_injective hx) hfor]
            exact Algorithm.retGrade1 _ k v bnd hin hlv hnotGrade2 hcnt honce
              hbind hval
              hret hbnd
          | grade0 =>
            obtain ⟨hin, hlv, hnotGrade2, hnotGrade1, hcnt, hval, hret, hx⟩ :=
              gbcaProgramStep_byzantineRetGGrade0_own (hall k)
            rw [composition_setProcessVariables_setBound (PMF.pure_injective hx) hfor]
            exact Algorithm.retGrade0 _ k bnd hin hlv hnotGrade2 hnotGrade1
              hcnt hval hret
              hbnd

/-! ### Mechanical axiom check -/

/-- info: 'PLTS.ABA.GBCA.ByABDY.composition_projects' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms composition_projects

end GBCA.ByABDY
end ABA
end PLTS
