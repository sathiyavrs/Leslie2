# Fidelity — the encoding against its sources

A registry of the places where the ABA encoding and the artifacts it answers to do not
coincide, restricted to divergences carrying no D-number — together with §1, where the
sources disagree with each other and the encoding must pick a side —
for a reader holding the sources open beside the Lean.

**Three sources, in a chain.** The *source blueprint* — "Verifying ABA with Leslie",
`Papers/Leslie_blueprint.pdf` — supplies the transition systems (TS 1 = ABA, TS 2 =
GBCA, TS 3 = WCC, pp. 18–19; TS 4 = Gather, TS 6 = BRB, pp. 20–21) and the pseudocode
(Algorithm 1 = the ABA core, p. 14; Algorithm 2 = GBCA, p. 15; Algorithm 4 = gather
over BRB, p. 16; Algorithm 6 = Bracha's BRB, p. 17). It in turn adapts *ABDY22*
(Abraham, Ben-David and Yandamuri, PODC 2022), which numbers independently: ABDY22's
Algorithm 2 is the weak-coin agreement framework `AA_ε` that the source blueprint's
Algorithm 1 realises (ABDY22's Algorithm 1 is the strong-coin framework, not encoded
here), and ABDY22's Algorithm 6 is the GBCA of record. The third source is *AFW25*
(Attiya, Flam and Welch, "Why Canonical Rounds Fail for Optimal Byzantine
Resilience", arXiv:2510.04310v2, the extended version of the PODC 2026 paper; numbers
below are the extended version's): the source blueprint's Algorithm 4 is the binding
form of AFW25's Algorithm 5, and AFW25's Algorithm 4 — graded agreement from two
gather calls — is the source of record for the gather-based GBCA implementation
(D24), which the source blueprint does not contain. Bare algorithm numbers in this
file are the source blueprint's. The encoding
follows the source blueprint; where the source blueprint departs from a paper the
encoding inherits the departure, except at the items of §1.

**The D-registry is elsewhere.** The catalogued deviations — D1, D4, D5, D8–D19, D21–D24,
D26–D35, with D12 refined to D12′ — are cited at the point of use in the ABA module
docstrings and glossed one by one in the blueprint chapter (the Deviations paragraph of
`blueprint/src/content.tex`), which is the registry of record.

## 1. Where the encoding follows a paper against the source blueprint

Five items. Three are places where the encoding follows a paper the source blueprint
departs from, rather than inheriting the departure: ABDY22's Algorithm 6 at the
graded-agreement implementation (D18), AFW25's Algorithm 1 at Bracha's rounds (D34), and
AFW25's Algorithm 5 at the gather rows (D35). The other two are properties the sources
state in different forms, where what the encoding proves is one form and its relation to
the other belongs here.

The verified GBCA implementation (`GBCA.ByABDY.ImplementationStep`) transcribes **ABDY22's Algorithm
6 in full** — six rounds, the message levels INPUT, ECHO, VOTE, BIND, ECHO5 (the paper's
`echo` through `echo5`), and that algorithm's three decide conditions, `retA` an `n − f`
`ECHO5 v` receipt quorum, `retB` an `n − f` any-`ECHO5` quorum containing `ECHO5 v` with
`f + 1` `BIND v` receipts and `|Valid| > 1`, `retC` an `n − f` `ECHO5 ⊥` quorum with
`|Valid| > 1`. That is deviation **D18**, and what it departs from is the source
blueprint's Algorithm 2, a **four-round compression** of Algorithm 6: the `echo5` level
elided, the decide conditions read one message level down, and `f + 1` `VOTE v` receipts
as the grade-1 witness where Algorithm 6 reads `f + 1` `BIND v`.

The compression is not merely shallower; it violates the paper's Graded Binding. One
process held at the echo stage through a grade-0 decision can afterwards direct its
write-once echo at either bit, and one corruption completes the `f + 1` `VOTE v` count
for the bit of the adversary's choice, so two extensions of a single `C`-return hand out
two different bits and no binding-faithful specification simulates the compression. The
concrete violation at `n = 4, f = 1` is written out in `DESIGN-GBCASim.md`. At the D18
evidence level the same attack dies: `f + 1 > |F|` `BIND v` receipts put an honest
`BIND v` sender behind every grade-≥1 output, hence an `n − f` `VOTE v` receipt quorum
over the write-once `VOTE` level — and that quorum is the object the paper's binding
argument counts (Lemmas 4.8/4.9 through E.9).

Annotation lives in `GBCA/ABDY/Implementation.lean`'s module docstring, in the blueprint
chapter's caption for the algorithm and its D18 registry entry, and in the source
blueprint's own TeX (`Leslie/blueprint/src/sections/Algorithm.tex`, a red note at
Algorithm 2's decide conditions); the source's PDF caption reads "Implementation of GBCA
from [ABDY22]" with no such note.

On the specification side the matching item is **D19**. TS 2's bound value
`bind ∈ {0,1,⊥}` is replaced by the exclusion set `excluded : Finset Bool`, the bits the
instance can no longer hand out (`GBCA/Specification.lean`). The exclude fires under the
guard `excluded = ∅`, so reachable states are exactly `excluded ∈ {∅, {b}}`
(`GBCASafety.excluded_card_le_one`) and the bound value embeds onto them — `bind = ⊥` as
`excluded = ∅`, `bind = b` as `excluded = {!b}`. The two state shapes therefore differ in
the guards rather than in the cardinality. `excluded` is monotone and written once, so
Graded Agreement is the return guard pair `v ∉ excluded ∧ !v ∈ excluded` and Binding is
the guard `(!bnd) ∈ excluded` every return carries for the bit `bnd` it announces, both
proved from monotonicity alone in `GBCA/SpecificationSafety.lean` (`retG_value_agree`,
`specInst_binding`, `retC_excluded_nonempty`) with no auxiliary invariant; the same file
carries Validity's safety half (`specInst_validity`, `specInst_no_retC`).

A transcription question of ABDY22's own: the prose preceding Algorithm 6 says "upon
receiving `echo4` messages from `2t + 1` parties" where the pseudocode's lines 19–20 say
`n − t`. The two coincide only at `n = 3t + 1`; the encoding follows the pseudocode
(`n − f`).

**Bracha's rounds follow AFW25's Algorithm 1.** The echo step fires on an `INIT` receipt
from the leader, on more than `(n+f)/2` `ECHO m` receipts, or on `f + 1` `VOTE m`
receipts; the vote step fires on more than `(n+f)/2` `ECHO m` receipts or on `f + 1`
`VOTE m` receipts; and the return takes `2f + 1` `VOTE m` receipts
(`BRB.BrachaStep.echo`, `voteQuorum`, `voteAmplification`, `ret`). Algorithm 6 of the source
blueprint fires the echo step on an `INIT` receipt alone and puts `n − f` at every
quorum. That is deviation **D34**, and the quorum is `Parameters.echoQuorum`, which is
`(n + f) / 2 + 1`; `BRB.EchoCert` is at that size, and the invariant clause `echo_prov`
carries an honest echo of `m` back to `ldr ∈ F ∨ input ldr = some m`.

**The gather rows follow AFW25's Algorithm 5.** Its main thread sends phase 2, waits,
sends phase 3, waits, sends phase 4, waits and returns (lines 10–20), and the rows carry
that order: `Gather.ProgramStep.sendVote` requires the sender's own `ECHO`, `bindCall`
requires its own `VOTE` and no earlier bind call, and `ret` requires the returner's own
bind call, which the write-once field `Gather.BaseProcessRecord.sentBind` holds. Line 9 of the same
algorithm sets the `ECHO` payload to the sender's accepted-pair set, and
`ProcessRecord.accepted` — the entries of the sender's input store — is that payload.
Algorithm 4 of the source blueprint states the rows as `upon` handlers without the order;
that is deviation **D35**.

**Validity in two forms.** ABDY22's Definition 2.2 states Validity as unanimity: if all
non-faulty parties receive the same value `v` as input, all non-faulty parties commit `v`.
The source blueprint states it as provenance (p. 6): if a correct process returns `b` then
a correct process had `b` as input. `ValidityTrace` is the provenance form, and so is the
Validity conjunct of `ABDY.main`. The safety half of the unanimity form follows from it: a
correct return under a unanimous input can only be the bit every correct process holds.
The half asking that every non-faulty party commit at all is liveness, and is out of scope
(§6). Where this file writes "the papers' Validity" elsewhere, the provenance form is
meant.

**Agreement is read at the returns, ABDY22's at the commits.** ABDY22's Definition 2.2
states Agreement of `commit`, and line 7 of its Algorithm 2 commits at grade 2.
Algorithm 1 puts the DECIDED gossip on top of that framework and returns on an `n − f`
DECIDED receipt quorum, and `AgreementTrace` quantifies over those returns, the `retABA`
labels of a trace. A round's graded outputs are `retG` labels, which `Label.hiddenAPI` hides
at the flat reading, so agreement on the grade-`A` outputs is stated by no theorem of the
development. The encoding is faithful to Algorithm 1 here, and ABDY22's Agreement is about
the earlier event.

## 2. Interpretation-level readings

**"Received once."** The wait case (b) of Algorithm 6 requires that "⟨echo5, b⟩ has been
received once". `ImplementationStep.retB` reads this as *from at least one sender*: `honce : ∃ k,
Message.echo5 (some v) ∈ s.recv id k`, not as a cardinality constraint of exactly one
receipt. The hypothesis is a genuine part of the rule, carried through the protocol's
rendering by `ABAProgramStep.retG_B` and through the round instance's Byzantine handshake row
counterpart `GBCAProgramStep.byzantineRetB`, but no proof
consumes it: the refinement's `retB` rows bind it and leave it unused, discharging the
`B`-return's specification-side guards from the `f + 1` `BIND v` receipts and `hval`
instead. Either reading supports the same theorems.

**Unions read as bounds.** Algorithm 4's sends are unions: on `n − f` approved echoes a
process sends `⟨vote, ⋃ AP_id⟩`, and likewise at the BIND and return steps. The gather
rows (`Gather.StepOverBroadcastSpecification.vote`, `bindCall`, `ret`, and their
`StepOverBracha` counterparts) read each union as a bound instead: any approved set
containing the `n − f` collected payloads may be sent, and any map dominating the `n − f`
committed BIND payloads and contained in the committed inputs may be returned. The union is
one such choice, so the reading widens the implementation's nondeterminism; every guard the
proofs consume is monotone in the chosen set, and the refinements hold for the wider
reading, hence for the union.

**The gather `ECHO` size guard.** Algorithm 4 of the source blueprint sends
`⟨echo, AP⟩` on `|AP| ≥ n − f` where line 8 of AFW25's Algorithm 5 waits for
`|AP_id| = n − f`, and the echo rows take the `≥` form, the accepted-pair set growing
one entry per delivery and the row firing at any point past the bound.

**The coin's `⊤` outcome answered at the return.** `WCC.Step.callResolve` draws the coin
inside the access that carries the caller count above `f`, which is Fig. 7 of the
ghost-variables draft against TS 3's separately scheduled resolution; that departure carries
a D-number (D31) and the blueprint registry is where it is glossed. What carries none is how
the outcome `CoinValue.top` is answered. Three of the four outcomes fix what every caller receives.
`⊤`
fixes nothing: `WCC.Step.ret`'s guard `val = .top ∨ val = .bit b` admits either bit, so the
adversary picks a process's returned bit at that process's return. The draft's Fig. 7 fixes the
responses at the resolution instead, one bit per process written when the coin resolves. The
two admit the same per-process assignments, and the encoding lets the adversary choose later,
with more of the run in view, so the encoding's coin is the more permissive of the two. A
specification constrains from above, so the refinements hold for the wider reading, hence for
the narrower one.

The same rule differs from Fig. 7 in a second way, glossed under D31. There every access
joins the caller set, so the coin resolves inside the `(f + 1)`st access. `WCC.Step.callLoop`
is unguarded and records no caller, so a call may be answered by it: the resolution happens
at the `(f + 1)`st recorded access, and the scheduler may defer it by answering calls with
the loop. The loop is what makes the call label input-enabled, and deferral adds executions
to the specification, so the encoding's coin is again the wider of the two and the
refinements hold for it. What the deferral withholds is a return, which is liveness.

The `guess` label and the `guess` state field are omitted under either
reading (D4, §6).

**Line 2's multicast fused into the call.** ABDY22's Algorithm 6 takes its input `x` as a
parameter and multicasts `⟨INPUT, x⟩` at line 2, its first statement.
`GBCA.ByABDY.ImplementationStep.call` writes `input`, `sentInput` and the multicast in one step, so
no state of the implementation holds a called process whose `INPUT` has not been sent. The
sent sets are read by `ImplementationStep.deliver` alone, so a send the adversary would delay is a
delivery it delays instead, and the same receipt patterns are reachable under either
rendering. D28 is the fusion of a sub-protocol's call and return into a caller's row, and
does not cover this one.

**Terminating `return` as state.** The pseudocode's `return` ends the process; the
encoding renders that as a fire-once flag — `ProcessRecord.returned`, guarded by the `hr`
hypothesis of all three GBCA returns `ImplementationStep.retA`, `retB` and `retC`, and
`RoundLoopState.returned`, guarded at `RoundLoopStep.ret`. The
guard has no surface counterpart in Algorithm 1 or Algorithm 2, which name no such
variable; the control-flow fact it expresses does. (At specification level it is no
interpretation: TS 1 and TS 2 carry `ret[id] = ⊥` guards of their own.) At the protocol,
returning and terminating are two fields and two rules: `RoundLoopState.returned` records that
`ABAProgramStep.ret` has fired, and `ABDY.RoundRecordMap.terminated`, whose sole writer is
`ABAProgramStep.terminate`, records that the process has stopped participating (D22, §6).

**The announced values on the return labels (D29).** The source blueprint puts the binding
content on the return label at both levels. Its TS 2 returns `bind` beside the graded
outcome and its TS 4 returns the core beside the map, and its pseudocode writes the same
two returns as `Response((v, g), _bound-value)` and `Response(S, _S^C)` — the second
component of each a value the caller is not handed. The encoding follows that reading.
`Label.retG r id out β` announces the round's bound bit and `Gather.Label.ret id g C`
announces the instance's core, in each case the value the specification holds as state,
written once by an internal rule and read by no program of either algorithm.

The two announced values differ from the sources in what they are guaranteed to be. The
bound bit is a `Bool` under the single guard `(!β) ∈ excluded`, which is D19's reading of
`bind = some β`; a reachable state excludes at most one bit, so the guard determines it.
The core is a payload set of at least `n − f` entries below the returned map, where TS 4's
own bind rule imposes no size bound at all (§5); the encoding's `Gather.Step.bindCore`
carries the size as a guard, and `ABA/Gather/CommonCoreCounting.lean` is the argument that
a reachable state of the implementation determines such a set. On the implementation side
both values are held as ghost state — the bound bit by the round's network state, the core
by the gather instance's network state — so no program reads either, and the announcement
is what makes binding a property of a single trace (`GBCA.specInst_binding`,
`Gather.specInst_core`), transported to each implementation by its own refinement
(`GBCA.ByABDY.implementation_binding`, `GBCA.roundOverBracha_binding`;
`Gather.instanceOverBroadcastSpecification_core`, `Gather.instanceOverBracha_core`). The
rows that do read a ghost — a flat reading's two graded-agreement returns — read it for the
value they announce and not for whether they fire, the read admitting a bit at every state
(`ghostOut_total`). For the bound bit at a flat reading that inertness is a theorem:
`ABDY.protocol_erasure` and `AFW.protocol_erasure` equate the achievable trace distributions
of each protocol with those of the same protocol over a one-element ghost record whose
returns announce any bit.

## 3. A network-model artifact

The source pseudocode has no explicit network: sends and receipts are primitive. The
encoding's set-based authenticated model is D5 and the DECIDED sets are D12′; what
belongs here is the asymmetry *between* the two networks. `RoundLoopStep.decidedDeliverReceive`
carries a freshness guard `hr : b ∉ c.decidedDelivered k`; `ImplementationStep.deliver` carries no
counterpart, its only hypothesis being soundness `h : m ∈ s.sent j`. Both are sound for the
same reason — receipt sets are `Finset`s and re-delivery is `insert` into a set, so the
guard removes redundant transitions rather than reachable states — and the asymmetry
reappears exactly in the protocol's rendering, where each delivery is a rendezvous whose two
halves are held by different components. Soundness is the network adversary's conjunct in
both sent sets: `NetworkStep.gbcaDeliver` requires `h : m ∈ s.sent r j` and
`NetworkStep.decidedDeliver` requires `h : b ∈ s.decidedSent j`, neither consuming the sent
message. Freshness is the receiver's, and only in the DECIDED sent sets:
`ABAProgramStep.decidedDeliverReceive` carries `hr : b ∉ c.decidedDelivered k` while
`ABAProgramStep.gbcaDeliverReceive`
carries no freshness guard, filing the message under the sender's received set row whatever
is already there. Its one hypothesis is the termination guard `hterm : p.terminated = false`
carried by every stage-side row (D22, §6), which is not a freshness condition.

## 4. Guards the specifications do not carry

Algorithm 6's control flow sits in the implementation tables and not in the systems they
refine. A refinement asks only that the implementation move no more freely than its
specification, so the gap is harmless; what is worth having in one place is which side of
it each guard falls on, and whether that placement was chosen or forced.

**Carried by the implementation tables** — `GBCA.ByABDY.ImplementationStep`
(`ABA/GBCA/ABDY/Implementation.lean`), mirrored row for row at `GBCA.GBCAProgramStep`
(`ABA/Composition/GBCAInstanceByABDY.lean`), Byzantine handshake rows included, and at
`ABDY.ABAProgramStep` (`ABA/ImplementationByABDY/System.lean`) with the reads taken through
`p.roundRecord r`.

- **The wait-until order.** The order is carried from the `BIND` level down: each of
  those sends requires the sender's own send at the level below — `hlv : sentVote ≠ none`
  on the two `BIND` rules, `sentBind ≠ none` on the two `ECHO5` rules, and
  `sentEcho5 ≠ none` on all three returns. Algorithm 6 reaches those **wait until** blocks
  only after executing the send the block above them ends with, and `hlv` is that
  reachability written as a guard. The two `VOTE` rules carry no own-send guard, and here
  the encoding follows the paper's own reading rather than tightening it: what precedes
  the first **wait until** block is not a block a process runs to its end but the
  **upon** handler of Algorithm 6's lines 5–7, which multicasts `ECHO`, so a process may
  reach that block and send its `VOTE` with its own `ECHO` still pending. The gather
  tables carry the same chain: `Gather.StepOverBroadcastSpecification.vote` requires the
  sender's own `ECHO`, `bindCall` requires its own `VOTE` and no earlier bind call, and
  `ret` requires the returner's own bind call (D35).
- **The denials of the higher cases.** Each rule carries the denials of the cases above
  it in its own block. In a return block the `⊥` rule denies its block's case (a) at
  either bit
  (`hnot : ∀ b, receivedCount (level below, b) < n − f` at `voteBot`, `bindBot`, `echo5Bot`).
  In the decide block `retB` and `retC` carry `hnotA`, the denial of case (1) at either
  bit, and `retC` carries `hnotB`, the denial of case (2) in reduced form:
  `∀ v, (∃ k, echo5 (some v) ∈ received id k) → receivedCount (.bind (some v)) < f + 1`. Case (2)
  asks at a bit `v` for four things — an `n − f` any-`ECHO5` quorum, a received `ECHO5 v`,
  `f + 1` `BIND v` receipts and `|Valid| > 1` — of which the first and the last are
  `retC`'s own `hcnt` and `hval`, an `n − f` `ECHO5 ⊥` quorum being in particular an
  `n − f` any-`ECHO5` quorum; the reduced `hnotB` denies the remaining pair. The
  docstring of `ImplementationStep.retC` states the reduction.
- **The return call guards.** All three returns require `input ≠ none`, the D8 guard
  carried from the sends over to the returns: a process that was never called does not
  return from the round.
- **The protocol's participation guards.** `ABAProgramStep.ret` and
`ABAProgramStep.decidedSendRelay`
  require `c.process.input ≠ none`, and `ABAProgramStep.gbcaCallLoop` requires
  `(p.roundRecord r).process.input ≠ none`. `gbcaCallLoop` deliberately carries no termination
  guard,
  so a process that has terminated at phase `toCallG` over an uncalled stage record has a
  row on neither call label and takes no further round-loop step. That excluded region is
  accepted rather than repaired: a terminated process is one whose own return has already
  fired, and no statement of the development is about what it does afterwards.

**Absent from the specifications.** Four of the placements below are chosen and two are
forced by where the authorisation of a Byzantine handshake row sits (D11), which cannot be
repaired at the rule; the seventh entry is a cross-reference.

- **`GBCASpec.Step`, every rule (chosen).** No rule of the graded-agreement specification
  requires a send at the level below, denies a higher case, or guards a return on a call.
  The specification abstracts the receipt patterns into `excluded` and `grade` (D19), and its
  return guards are that pair; supplying them from the receipts is exactly the work of
  `GBCASim.refinesSpecification`.
- **`WCC.Step.ret` without `called` (forced).** `WCC.SpecState` carries a `called` field
  and the return rule does not read it. The Byzantine coin row `byzantineRetW` has no row at
  the process it names — `RoundLoopStep.byzantineRetWIdle` stands idle at every process — and
  `coinLabelMap` maps that row onto `retW`, so the coin instance answers it alone. A `called`
  guard there would leave the row unanswerable. This is a consequence of the
  authorisation placement, not a preference.
- **`ImplementationStep.callLoop` and `GBCAProgramStep.callLoop` (forced).** Both are unguarded
  self-loops. `gbcaLabelMap` maps `byzantineCallGLoop` onto `callG`,
  `GBCANetworkStep.byzantineCallGLoop` carries no `k ∈ F`, and the named process's row is
  idle, so the call loop must accept every call label whatever the record holds.
- **`RoundLoopStep`'s DECIDED rows (chosen).** `RoundLoopStep.ret` and
  `RoundLoopStep.decidedSendRelay` read the receipt counts alone, without the `input ≠ none`
  guard their `ABAProgramStep` counterparts carry. The composed reading is the abstraction
  the protocol is carried into, and a guard there would ripple through `ABDY.ProtocolRel` and
  the core simulation.
- **`SpecStep.ret` without an honesty guard (chosen).** The honest return's guards are
  `val = some b` and `ret id = false`, and nothing about the returner, so a corrupted
  process may take it as an honest one does. `SpecStep.retByzantine` (D23) sits beside it and
  carries the arbitrary return, so the rule pair adds behaviour where an honesty guard on
  `SpecStep.ret` would only remove it.
- **`SpecStep.fail` without an input-enabledness loop (chosen).** TS 1 pairs its guarded
  corruption rule with the loop `⊤ --fail(id)--> ⊤`. `SpecStep.fail` carries
  `hnew : id ∉ s.F` and `hbud : s.F.card < P.f` as rule guards, and no other rule of
  `ABA.spec` accepts a `fail id` label, so a repeated or over-budget corruption has no
  transition there. Every other specification of the chain keeps the same test inside
  `corrupt` and leaves the rule total: `GBCA.Step.fail`, `WCC.Step.fail`,
  `Gather.Step.fail` and `BRB.Step.fail` accept every `fail` label and let the transform
  decide what the state does. The network adversary's `fail` row carries the two guards
  `SpecStep.fail` carries, so the two sides enable the same labels and no refinement is
  affected. The guard itself is D1; the loop TS 1 carries beside it is what this entry
  records. TS 1's other input-enabledness loop, the one on `callABA`, is guarded here as
  well: `SpecStep.callLoop` fires at a filled record entry (D36).
- **The `2f + 1` commit read as a relay threshold (cross-reference).**
  `ABAProgramStep.terminate` reads `2f + 1` DECIDED receipts where the paper's condition is
  that the process may stop without holding another back. That delta is the third D22
  residue of §6, and is not restated here.

## 5. Source defects the encoding does not reproduce

- **TS 1 violates Agreement and the papers' Validity.** The source's re-proposal rule
  fires with `val` already written, so the unanimity rule can overwrite it and one run
  returns `v` and then `1 − v`; and the free bind choice together with that same
  re-proposal carries a bit input only by a later-corrupted process through to a return.
  `Specifications/ABA.lean` reproduces neither rule. `PLTS.ABA.SpecStep.decide` is the
  sole writer of `val` and fires only from `val = ⊥`, so the decision value is written
  once and Agreement is structural (`PLTS.ABA.SpecInv.val_stable`); and it carries the D13
  support guard `PLTS.ABA.InputSupport`, which is where the Validity trace dies — the
  counterexample check in `Specifications/ABA.lean` records it, with inputs `1,0,0,0` at
  `n = 4, f = 1` and the sole `1`-inputter corrupted leaving one supporter of `1` against
  the `f + 1 = 2` the guard demands. The eight-rule shape this leaves, with the control
  mode carrying the flip, is deviation **D21**.
- **TS 2's singular binding witness** (`∃ id ∉ F, call[id] = b`, source p. 19) loses
  provenance one level down, and `hybrid` over it violates Validity; the deterministic
  trace is in `GBCA/Specification.lean`'s module docstring, under D14. Both TS 1 defects
  and this one are annotated in the source blueprint's TeX
  (`Leslie/blueprint/src/sections/Specification.tex`, red notes at the affected rules).
  D14 and D15 replace every such witness with an `F`-blind count.
- **Algorithm 2 violates Binding**, being a four-round compression of ABDY22's Algorithm
  6; the encoding follows Algorithm 6 instead (D18) — §1.
- **The Graded Agreement clause is ill-typed** as stated: "if two correct processes return
  `(b, X)` and `(b′, X′)` then `b = 0 ⟹ b′ ≠ 1` and `X = A ⟹ X′ ≠ ⊥`" (p. 6), with `⊥` in
  a grade position ranging over `{A, B, C}`. It reads as grade `C`, and is realized as the
  `grade` guard's `A`/`C` exclusivity, the `hg` guards of `PLTS.ABA.GBCA.Step.retA` and
  `PLTS.ABA.GBCA.Step.retC`.
- **TS 1's `Initial` clause names an undeclared field** `out` (source p. 18), absent from
  the same system's `State` line. It is omitted: `PLTS.ABA.SpecState` declares `input`,
  `ret`, `F`, `val` and `mode`, and nothing else.
- **TS 6 pins the delivered value at the call, which Bracha's rounds do not.** Under TS 6
  an honest `call(m)` sets the single `call` field to `m`, every return hands out `call`,
  and the corrupted-leader rule can only spoil the field (`call = ⊤`, no returns) before
  the first return. Bracha's rounds with the leader corrupted *after* its `INIT` multicast
  leave more open: until some correct process holds an ECHO quorum of more than `(n+f)/2`
  senders, the corrupted leader's injections can make the rounds deliver a value other
  than `m`, and no resolution of TS 6's nondeterminism returns it — the specification
  excludes its own implementation under D1's dynamic corruption. `BRB.SpecState` splits
  the recorded `input` from the committed `val` and guards the commit by
  `ldr ∈ F ∨ input = some m` (D27), which is the window the implementation actually leaves
  open: at a never-corrupted leader the commit is pinned to the input, and Validity
  survives in the form the property states it.
- **TS 4's bound core is what a reachable state determines.** The core is an honest
  sender's `ECHO` payload heard by `f + 1` honest rows, and the counting of
  `ABA/Gather/CommonCoreCounting.lean` locates it in the prefix of a run. Two independent
  points stand behind that reading. As written (source p. 20), the bind rule constrains
  its set `S` only to identifiers already called — no size bound, the empty set included,
  so the `n − f` size clause of Binding Common Core is not enforced by the rules (its
  return guard also reads `bind ≠ ⊥` where the unset marker is `∅`). And a size guard on
  `S` carries only as far as an argument about the implementation does: AFW25's Remark 22
  reads the core of a gather *without* binding as fixed only in hindsight, and a
  specification whose internal rule fires at a reachable state can bind only what a
  reachable state determines. `Gather.SpecState.core` therefore carries the size as the
  guard `hcard` of `Gather.Step.bindCore` and domination as the return's, and
  `ABA/Gather/CommonCoreCounting.lean` discharges both from the prefix: the core is the
  `ECHO` payload of a sender outside `F` dominated by `f + 1` processes outside `F`, a
  counting argument over the sent sets locates such a sender, and
  BIND-by-reliable-broadcast is what keeps the payloads the certificate counts write-once
  under D1's adaptive corruption. The two guards of `bindCore` are needed together. `S` is
  a set of pairs, so `hcard : P.n - P.f ≤ S.card` counts entries and not identifiers;
  `hval`, which is `AcceptedPairs.subMap S s.val`, holds `S` below the write-once map `val` and so
  forces the first components apart, and `AcceptedPairs.card_le_domainCount` is the step from the
  two to
  `n − f` distinct identifiers. That broadcast of the `BIND` payloads is D32, and the
  binding form of both of the round's gathers, which is what makes the second gather's
  core a history variable rather than the prophecy variable of Remark 22, is D33.
  `DESIGN-GatherTiers.md` carries the counting argument in full.

## 6. Scope boundaries

Beyond D4 — the WCC `guess` label and state field, whose omission `Vocabulary/Labels.lean`
and `Specifications/WCC.lean` both record in their module docstrings — they exist solely
for Unpredictability, inexpressible once the guess is dropped.

- **Per-transition fairness markings.** Every transition system in the source carries the
  line "all transitions are fair except those labelled by fail and the call loops" (pp.
  18–19). The encoding has none; they bear on liveness only.
- **Partial-information adversaries.** The source equips a system with a pair of
  observation functions (Definition 9, p. 4) and a belief construction turning such an
  adversary into an omniscient one (Definition 10, p. 5). Every adversary in the ABA chain
  is declared omniscient there (Definitions 11–15, Specifications 1–3, pp. 6–7), which the
  encoding's unrestricted schedulers match; belief has no counterpart.
- **The Byzantine `⟨ECHO, ⊥⟩`.** `GBCA.ByABDY.Message.echo` carries a `Bool` where `Message.vote`,
  `Message.bind` and `Message.echo5` carry an `Option Bool`, so `ImplementationStep.byzantine`
  cannot inject an
  `ECHO` of non-bit payload, which ABDY22 permits a corrupted sender. The restriction
  falls on the adversary and costs nothing. Two guards read `ECHO`: at a named bit,
  `receivedCount j (.echo b)`, in `voteBit`'s quorum and in `voteBot`'s denial `hnot`; and
  payload-blind, `echoCount j`, in `voteBot`'s quorum. A non-bit `ECHO` raises
  `echoCount j` alone, so its one use to the adversary is to reach `voteBot`'s quorum
  without carrying either bit to `n − f` and breaking `hnot`. An injection of a bit does
  the same whenever some bit has `receivedCount j (.echo b) < n − f − 1`. When neither has,
  both stand at `n − f − 1`; an honest sender's `sentEcho` is write-once, so only the `f`
  corrupted senders are counted at both bits and `echoCount j ≥ 2(n − f − 1) − f`, which
  `3f < n` puts at `n − f` or above (`f ≥ 1`, which an injection presupposes). `voteBot`
  is then enabled already and no injection is wanted. So the bit-valued injection reaches
  every guard the non-bit one would, and no safety- or termination-relevant behaviour is
  lost. `GBCA.ByABDY.Message.input` carries a `Bool` as well, so `⟨INPUT, ⊥⟩` cannot be
  injected either. That restriction needs no argument of its own. Every guard reading
  `INPUT` reads it at a named bit: `hcnt` of `ImplementationStep.relay`, `hcnt` of
  `ImplementationStep.echo`,
  and the two counts of `bothValid`. There is no payload-blind `INPUT` count for a non-bit
  payload to raise.
- **Termination.** ABA's ε-sure Termination, GBCA's Termination and WCC's ε′-sure
  Termination (pp. 6–7) are unclaimed — `ABDY.main` is Validity ∧ Agreement. The same
  holds one level down: gather's Termination and BRB's Totality (pp. 7–9) are liveness
  properties and are unclaimed; TS 6's own stated scope is the linear properties, Totality
  living in the fairness markings that are outside the model. See
  `NOTES-Liveness-Roadmap.md`.
- **The approximate-agreement subroutine of AFW25's Algorithm 4.** Lines 7 and 8 set the
  grade by an approximate-agreement subroutine on an input of `R` or `0`, so a process
  there reaches the top grade only when enough others also chose `R`. AFW25's Appendix B
  gives that subroutine concretely, as a two-input approximate agreement over a primitive
  with its own `f + 1` relay and `n − f` thresholds. Neither is encoded: the grade is the
  local count on the second gather's return (D24), which drops a communication stage. Line
  5 takes the returned bit from the `f + 1` test and line 6 the grade from the `|T| − f`
  test, and grade `A` ties both to the latter — sound because `|T| − f ≥ n − 2f ≥ f + 1`
  carries the heavy bit past the `f + 1` bar, where AFW25's Lemma 18 makes it unique.
- **SRSD and AVSS (TS 5 and TS 7).** Not encoded, nor is the source's Algorithm 3, the
  coin implementation over gather and SRSD that they serve. In the source, gather serves
  the coin construction through SRSD; here the coin stays at specification level — its
  gather/SRSD implementation is not modelled, as the scope note of `Results.lean` records
  — and the encoded gather serves the gather-based GBCA implementation instead.
- **Participation past the round advance.** ABDY22 separates deciding from terminating: a
  process decides and then eventually terminates (Definitions 3.1 and 3.2), and the
  amplification argument counts the echoes a decided process keeps sending (Lemmas 4.6 and
  E.5, stated under the hypothesis that no non-faulty party terminates). The encoding
  carries that shape, as deviation **D22**; what belongs here is what the shape leaves
  uncovered. A process record holds the stage record of every round the process has
  touched, in a `Finmap` read through `ABDY.RoundRecordMap.roundRecord`; each stage-side rule
  reads and writes the stage record of the round its own label tags, under an
  instance-local guard and no round guard; and the round advance, `ABAProgramStep.retW` and
  `ABAProgramStep.retWPublish`, resets nothing. A process therefore answers prior-round messages
  and files deliveries of any round. `ABAProgramStep.terminate` is the terminating step. It
  fires when the process's own return has fired and DECIDED receipts from `2f + 1`
  distinct senders are on record, and it writes `terminated` alone, so the stage records
  freeze where they stand. Three residues remain.
    - The amplification rule `ABAProgramStep.gbcaSendRelay` is guarded by the process holding an
      input in that round's stage record (`hin : (p.roundRecord r).process.input ≠ none`, D8, and
      `ImplementationStep.relay` carries the same guard one level down), where lines 3–4 of ABDY22's
      Algorithm 6 guard the relay on the receipt count alone.
    - A stage delivery at a process that has terminated is disabled rather than ignored.
      `ABAProgramStep.gbcaDeliverReceive` carries `hterm : p.terminated = false` and
      `ABAProgramStep.gbcaDeliverIdle` demands a different receiver, so the adversary has no
      composite step delivering a stage message there at all.
    - The `2f + 1` receipt count of `ABAProgramStep.terminate` is the encoding's commit
      point. At most `f` senders are corrupted, so `2f + 1` receipts stand behind `f + 1`
      honest senders of the payload, which is the threshold `ABAProgramStep.decidedSendRelay`
      reads; the paper's own condition is that the process may stop without holding back
      any other.
- **The scope of `terminate`.** The flag is read by the stage-side rows and by nothing
  else: `callG_call`, the three `retG_*`, `gbcaSendRelay`, `gbcaSendEcho`, the six level rows
  `gbcaSendVoteBit` through `gbcaSendEcho5Bot`, `gbcaDeliverReceive`, and `terminate` itself;
  `gbcaCallLoop` is
  the stage-side row that does not read it (§4). A process that has terminated still
  finishes a pending coin handshake (`callW`, `retW`), publishes `⟨DECIDED, b⟩` through
  `retWPublish`, and both relays and receives DECIDED (`decidedSendRelay`, `decidedDeliverReceive`).
  That
  placement is the design and not an oversight: what the flag records is that the process
  has stopped participating in graded agreement, and the D12′ broadcast it keeps carrying
  is what lets the processes still running cross the relay threshold without it.

The returner axis carries no divergence. The ABA interface is modelled for a corrupted
process at every level of the chain (D23). At the protocol and in the composed reading, a
corruption replaces the process's program: the honest rows are guarded by the replacement
flag, the replaced program self-loops on `callABA` and `retABA`, and the network's own
`retByzantine` row authorises the return under `k ∈ F` with none of the DECIDED evidence
`ABAProgramStep.ret` demands. At the specification the same behaviour is `SpecStep.callByzantine`,
which records a bit unrelated to the one its label declares, and `SpecStep.retByzantine`, which
returns any bit at any time without moving the state.

`ValidityTrace` and `AgreementTrace` are accordingly read at never-corrupted returners,
which is the quantification of the source's own contracts ("if a correct process returns
`b` then a correct process had `b` as input", p. 6) and of ABDY22's. It is also the only
quantification the model admits: a corrupted return carries an arbitrary bit, so the
unconditional forms are false of the system. Corruption is read at the trace level, as
non-membership in every stage of `failSet`, the fold of the D1 transform over the `fail`
labels seen so far, so a process corrupted at any point of the trace is excluded at every
point of it. The witness axis stays as strong as the papers': the caller `ValidityTrace`
produces must itself be never corrupted, not merely a member of a support set a later
`fail` could taint, and the call it produces is that caller's first `callABA` of the
trace, the event that carries the caller's input.

One level down the interface binds corrupted returners too. At the composed reading
`GBCAProgramStep.byzantineRetA`, `byzantineRetB` and `byzantineRetC` repeat the honest
rules' guards, and `GBCA.ByABDY.gbcaLabelMap` sends the Byzantine return onto
`GBCA.Step.retA`, `retB` and `retC`, which carry no honesty exemption.
`GBCA.specInst_binding`, `retG_value_agree` and `specInst_validity` therefore quantify over
every returner of a round, where ABDY22's Definition 3.2 quantifies over the non-faulty
parties. A corrupted process's graded return is held to the guards an honest one's is held
to, so the round's contract is the stronger of the two and the theorems above it lose nothing.

## 7. An adjacent open item

It sits under Future work in `ABA/README.md`, and it is not a fidelity gap.
**Achievability** — `HybridRefinesSpecification/NonVacuity.lean` carries the non-vacuity
run on `hybrid`, the system the core simulation takes as its subject, and a
machine-checked positive-mass trace for `ABDY.protocol`, the system `ABDY.main` is about,
is outstanding.
