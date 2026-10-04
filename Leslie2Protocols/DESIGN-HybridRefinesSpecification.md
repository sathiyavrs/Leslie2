# Design — the core simulation `hybrid ⊑ ABA.spec` (`hybridRefinesSpecification`)

Companion design document to the Lean proof in
`ABA/HybridRefinesSpecification/Relation.lean` (relation + invariant),
`ABA/HybridRefinesSpecification/InvariantPreservation/` (the step cases and invariant
preservation), `ABA/HybridRefinesSpecification/AbstractStatePreservation.lean` (the
stutter transitions and the assembly), `ABA/HybridRefinesSpecification/WeakTransitions.lean`
(the abstract τ-run lemmas), and `ABA/HybridRefinesSpecification/Simulation.lean` (the simulation
proof, transition by transition). It is the narrative account of that proof: what the relation is, why it
has the shape it has, and how each class of concrete step is matched. Each Lean file's
module docstring is the account of record for its own contents. The `hybridRefinesSpecification`
proof prose in `blueprint/src/content.tex` condenses this document. The spec-level repairs the
simulation depends on are labelled D13/D14/D15 (Validity: where a decided bit came from) and D12′
(DECIDED equivocation).

## Systems

```
hybridExtended := gbcaSpecificationFamily ∥ (synchronisedProduct roundLoopProgram ∥ (ABANetwork ∥ coinOverRoundAlphabet))
hybrid    := ((hybridExtended.abstract networkEventLabels).relabel).abstract hiddenAPI
target    : ProbabilisticForwardSimulation hybrid (ABA.spec P) hybridSpecificationRelation
```

The four components are the round specifications, the `n` round loops, the ABA network and the
common coin, and their alphabet is the extended alphabet of the protocol; the labels the components
synchronise on are hidden, the result is read back over `Label n`, and the sub-protocol API is
hidden in turn (`Composition/Hybrid.lean`). Corrupted processes' calls and returns are covered by
the Byzantine call and return transitions, authorised by `k ∈ F` at `ABANetwork` (D11). See
`Vocabulary/RoundLoop.lean`'s module docstring for the per-process algorithm and deviations D9–D12′
(0-based rounds, the DECIDED send `decidedSend` of a grade-2 round taken after the coin return
`retW`, the Byzantine call and return transitions, per-process DECIDED sets — see § D12′ below).

Concrete state: `(g, (C, (A, w)))` with `g : ℕ → GBCA.SpecState`, `C : ∀ j, RoundLoopVariables`, `A :
ABANetworkState`, `w : ℕ → WCC.SpecState`. The two ABA components are read as one object `c :
ABAState := (C, A)` through the accessors of `Composition/ABAState.lean` — `processes`,
`decidedSent`, `decidedReceived`, `F` — and every clause below names them, so the relation reads the
hybrid state with no change of system. Abstract state: `a : ABA.SpecState`.

## The relation: the lazy two-phase abstract state (deviation D16)

`hybridSpecificationRelation := diracRel R₀` with `R₀ (g,(c,w)) a := Invariant (g,c,w) ∧
AbstractState (g,c,w) a` — all randomness couples outcome-to-outcome, so the abstract system stays
Dirac.

The abstract state is **lazy** and **never-flipping**. It never fires `SpecStep.coinFlip`, so its
mode is `ControlMode.flipEnabled` at every state it reaches (field `mode_flipEnabled`),
`SpecStep.decide` is
enabled throughout, and the concrete coin's resolving call couples to a stutter. And it never
decides *between* transitions: it occupies one of two phases, keyed on `a.val`, and crosses from
the first to the second at the visible `retABA` that opens phase 2.

### `AbstractState` fields (`HybridRefinesSpecification/Relation.lean`)

- `F_eq : a.F = c.F`
- `ret_eq : ∀ id, a.ret id = (c.processes id).returned`
- `mode_flipEnabled : a.mode = .idle` (the abstract state never fires `SpecStep.coinFlip`)
- `input_sync : ∀ id, id ∉ c.F → a.input id = (c.processes id).input` — the ghost and
  the committed input agree at every correct process. The clause is an equality and it
  sits outside the phase disjunction, so it holds in both phases. At a corrupted process
  it says nothing, and the counts that read the ghost carry such a process through their
  `id ∈ F` disjunct.
- `phase` — the two-phase disjunction on `a.val`:
  - **Phase 1** (pre-first-return): `a.val = none`.
  - **Phase 2** (post-first-return): `∃ v, a.val = some v`, `v` is permanently witnessed
    by a concrete round bound at grade 2 (`∃ r, Grade2Witness P g c r v` — § Witnesses), and every
    correct holder of a grade-2 decision names `v`
    (`∀ j b', j ∉ c.F → Grade2Holder P c j b' → b' = v`, the `F`-free universal that survives
    corruption of the original witnesses).

A `callABA` at a correct process is matched transition by transition. The commit transition fires at
`input = none` and is matched by `SpecStep.callSet`, whose guard is the empty ghost entry
`input_sync` supplies; the concrete loop fires at `input ≠ none` and is matched by
`SpecStep.callLoop`, whose guard is the filled entry the same clause supplies. The ghost
write happens at `SpecStep.callSet` alone and is a first write, matched with the concrete
commit, so `input_sync` is restored on the nose. In phase 1 the abstract state stays
undecided and matches every hidden transition with a stutter. The matching run for `retABA` runs
`SpecStep.decide` as the τ-tail leading the return (§ Transition dispositions), landing the
abstract state in phase 2. From there `a.val` fixes the decided value for good, so every
later transition is a stutter, one of the two `callABA` matching steps, or a direct `SpecStep.ret`.

### `AbstractState` is preserved by a write elsewhere

`AbstractState` reads only three projections of the concrete state: `F`, the per-process
`input`/`returned` fields, and phase 2's witness-and-holder pair. `AbstractState.unchangedBy`
packages exactly this — `AbstractState` transfers along any write preserving `F`, `input`,
`returned` and carrying an `AbstractStateUnchanged` (§ Witnesses) for the last; the coin state is
not among them, so `AbstractState` transfers along any change of it. That lemma replaces the
stutter argument at each transition: every hidden transition preserves the three projections, so its
`AbstractState`-match is one `AbstractState.unchangedBy` invocation rather than a bespoke
re-derivation (the seven Stage-C stutter lemmas of
`HybridRefinesSpecification/AbstractStatePreservation.lean` are all instances).

### Witnesses: decided values stated without the live pair

Under D19 the state of a GBCA round records exclusion: `(g r).excluded : Finset Bool`
is written by `bindUnset`, and a value-bearing return needs the *live pair*
`(!v) ∈ (g r).excluded ∧ v ∉ (g r).excluded`. The relation does not state decided values through
that pair. It states them through witnesses, which name their bit off a single
permanent membership `(!b) ∈ (g r).excluded` plus commitments that only `call`, `F` and the
correct `processes` fields can affect. That is the design, and it is sound; the witnesses are
what `Invariant.decided_source`, `Invariant.grade2_source` and phase 2 of `AbstractState` carry.

The witness form is stronger than the specification requires. `bindUnset`
carries the guard `excluded = ∅`, so a round excludes at most once
(`GBCASafety.excluded_card_le_one`) and `excluded = {0,1}` is unreachable: a live pair
established by a return is in fact permanent, and pair-form invariants are maintainable.
Trading the witnesses for the pair is therefore available as a simplification. It is
recorded here as an option and is not scheduled work: the exchange would touch
`decided_source`, `grade2_source`, `AbstractState`'s phase 2 and every `AbstractStateUnchanged`
obligation, and the witness form needs no reachability argument of its own.

- **`Grade2Commitment P g c r b`** — the permanent commitments of a round bound at grade 2: the live
  pair at every round `r' ≥ r` (round `r` itself included), every correct call above `r`,
  every estimate of a correct process past `r`, and
  every correct `OutcomeHolder` of round `r`'s outcome names `b`. `OutcomeHolder` is the
  outcome-holder
  predicate — a round-`(r + 1)` GBCA call of `v`, or a committed est of `v` in the window
  between `retG r` and `retG (r + 1)`. Each component is monotone-stable: the first only
  loses instances as `excluded` grows, the rest read write-once `call` and correct `processes`
  fields.
- **`Grade2Witness P g c r b`** := `(g r).grade = some true ∧ (!b) ∈ (g r).excluded ∧
  Grade2Commitment P g c r b` — a round bound at grade 2 whose surviving bit at the
  grade-2 return was `b`,
  plus those commitments. `(!b) ∈ excluded` is permanent (`excluded` only grows), so a witness
  names `b` forever whatever else the round does. This, not a live pair, is what
  `Invariant.decided_source` and `Invariant.grade2_source` produce and what phase 2 of
  `AbstractState` holds. `Grade2Commitment.of_unchanged` / `Grade2Witness.of_unchanged`
  preserve both along any step that keeps `excluded`, `call`, correct `round`/`estimate`, reflects
  carriers and only grows `F` (`hF : c.F ⊆ c'.F` — the correctness premises are all of the form `id
  ∉ F`, so they must be re-derived through the larger set); `Grade2Witness.of_unchanged`
  additionally requires the round's grade preserved.
- **`Invariant.excluded_support` (I28)** — every exclusion keeps its D15 guard: `b ∈ (g r).excluded`
  implies `f + 1` F-blind call support for the spared bit `!b` at round `r`. Both `call` and `F`
  only grow, so the count is permanent, and `GBCA.exists_correct_caller` derives it into a
  never-corrupted caller of `!b`. That derivation is what recovers a round's value from the
  membership alone, with no live pair in hand.
- **`Invariant.outcomeHolder_agree` (I29)** — any two correct carriers of round `r`'s outcome agree,
  unless the round is graded 0. This is the state residue of the order argument "two
  opposite value-bearing returns cannot both fire at one round": the first excludes the
  rival bit, and the second's liveness guard then fails. The conjunct carries that
  argument as state, so no transition has to replay it.
- **`Invariant.grade2Bound_agree` (I30)** — any two correct `Grade2Holder`s agree globally, across
  rounds, where `Grade2Holder P c id b` is a live grade-2 `lastGrade = some (.grade2 b)` or a sent
  `b ∈ decidedSent id`. Each new holder is compared at its own `retG` transition, where the fresh return's
  live pair meets the existing holder's witness.
- **`AbstractStateUnchanged P g g' c c'`** — what a transition hands back about the abstract state:
  every `Grade2Witness` on the pre-state has a `Grade2Witness` on the post-state *at some
  round* (`∃ r1` — the bit is preserved, the round is re-existentialized, which is what lets a
  transition relocate a witness), and phase 2's holder universal survives given its witness.
  `AbstractStateUnchanged.refl` covers every transition that touches neither witnesses nor holders. Each
  `Invariant.step_*` lemma returns `Invariant ∧ AbstractStateUnchanged`, and
  `AbstractState.unchangedBy` consumes exactly that; the witness is what supplies a *fresh* holder
  in the corner where every original witness has been corrupted away.

## Transition dispositions

Concrete steps are read through the Stage-A case lemmas of
`HybridRefinesSpecification/InvariantPreservation/StepCases.lean`, which take a `hybrid`
transition back through the two hidings to the transitions of its four components; each class
is one case of `HybridRefinesSpecification/Simulation.lean`.

Three of the four Stage-A lemmas — `hybrid_step_callABA`, `hybrid_step_retABA`, `hybrid_step_tau` —
take I0 as a hypothesis. A round loop's transition is guarded by its own replacement flag and the
ABA network's transition by the corrupted set; the two live in separate components, and I0 is what identifies
them, so that what each lemma delivers is on `F` alone (D23). `corrupted_eq_false_iff` is the
one-line form of that translation.

| concrete transition | label | matching abstract run |
|---|---|---|
| every hidden call and return (`callG`/`retG`/`callW`/`retW`), `bindUnset`, the DECIDED send of a grade-2 round (`decidedSend`), DECIDED gossip τ | τ | stutter (`AbstractState.unchangedBy`; only `Invariant` moves) |
| `callW` at the transition that resolves `WCC_r`'s coin | τ | constant-coupled stutter via the generic `stutter_step` (`HybridRefinesSpecification/Simulation.lean`): coupling `Ω := μ_C.map (·, pure a)`, so `ω = pure (pure a)` and `ω.bind id = pure a` (the abstract state never flips, so every outcome of the draw lands on the same `a`) |
| `callABA id b`, `id ∉ F`, the commit transition (`input = none`) | `callABA id b` | `SpecStep.callSet` (a first write at the empty ghost entry `input_sync` supplies; both systems commit `b`) |
| `callABA id b`, `id ∉ F`, the concrete loop (`input ≠ none`) | `callABA id b` | `SpecStep.callLoop` (the filled ghost entry `input_sync` supplies; neither system moves) |
| `callABA id b`, `id ∈ F` | `callABA id b` | `SpecStep.callByzantine` (D23): the ghost at a corrupted id is unconstrained |
| `retABA id b`, `id ∉ F`, phase 1 | `retABA id b` | `decide_step` then `SpecStep.ret` (`weakStep_of_run_then_step`) — see below |
| `retABA id b`, `id ∉ F`, phase 2 | `retABA id b` | `SpecStep.ret` directly (phase 2's holder universal, applied to the correct DECIDED sender it derives, gives `b = v`) |
| `retABA id b`, `id ∈ F` | `retABA id b` | `SpecStep.retByzantine` (D23): neither system moves, in either phase |
| `fail id` | `fail id` | `SpecStep.fail` (same two guards via `F_eq`; robust in both phases) |

A `retG` label carries the round's bound bit beside the graded outcome (D29). The whole alphabet
the components synchronise on is hidden before the core simulation sees it, so that bit reaches the abstract system on no
label, and the transition that reads it — the round instance's return — is a τ of `hybrid` matched by a
stutter. `AbstractState` holds no field for it, and no invariant conjunct reads it: the round's
binding content enters the core simulation through `(g r).excluded`, which the bit is a projection
of.

The single run is `decide_step` (`HybridRefinesSpecification/WeakTransitions.lean`), fired
at the phase-1 `retABA`. `SpecStep.decide` is Dirac, so the run is one step; what the transition
supplies is its three guards, each read off the concrete state at the round `rA` of the
`Grade2Witness` derived from a never-corrupted DECIDED sender of `b`.

- `hv : a.val = none` — phase 1 itself.
- `hm : a.mode ≠ .terminal` — the `mode_flipEnabled` field: an abstract state that never flips
  never reaches it.
- `hs : InputSupport P a b` — `inputSupport_of_roundLoopInputSupport`
  (`HybridRefinesSpecification/Relation.lean`) reads the concrete input-or-`F` sent set
  `Invariant.bind_support rA b` through phase 1's ghost sync.

The step writes `val := some b` and returns the mode to `ControlMode.flipEnabled`, so
`mode_flipEnabled`
survives it and phase 2 is entered with the witness at `rA` in hand. The trailing
`SpecStep.ret` is joined on by `weakStep_of_run_then_step`: the run is the leading
τ-closure and the visible `retABA` the middle hyper-step.

## The spec repairs as design

Four spec-level repairs make the simulation possible; each is a permanent, `F`-blind discipline on
where a decided bit came from. D13/D14 repair the abstract specs (TS 1 = `ABA.spec`, TS 2 = the `GBCA` specification)
against the papers' Validity; D15 is the F-blind counting form of their support guards, discharged
at the implementation by the derivation of `DESIGN-GBCARefinesSpecification.md`; D12′ closes a DECIDED-equivocation gap.

### D13 — TS 1 Validity (the ghost input)

The source blueprint's TS 1 fails the papers' Validity: its free re-propose (while
`val = ⊥`) and its free mixed-bind lose the tie between a decided bit and a correct input, so a bit
input only by a later-corrupted process can win. The repair principle: a value may circulate only with
`f + 1` distinct supporters — at most `f` processes are *ever* corrupted, so `f + 1`
supporters always include a never-corrupted one, and the tie to a correct input survives dynamic
corruption with no future-peeking guard (`3f < n` supplies `n − 2f ≥ f + 1`).

What `Specifications/ABA.lean` carries:

- **Ghost** `input : Fin n → Option Bool` in `SpecState`. `SpecStep.callSet` records
  under the guard `s.input id = none`, so its write is a first write; `SpecStep.callLoop`
  carries the call label at a filled entry and writes nothing (D36). Both are sound —
  every event of either transition is a genuine `callABA` trace event — and the ghost holds
  each never-corrupted process's first call, which is the witness `ValidityTrace` names
  (§ Why this shape, item 7). No correctness guards anywhere; every support count is
  `F`-blind, hence immune to later `fail`s.
- **`SpecStep.decide`** is the sole writer of `val`, and its support guard
  `hs : InputSupport P s b`, the `f + 1` recorded-or-corrupt supporters of `b`, is the entire
  constraint on the value decided. It restricts which bit may be decided, and does so by
  design: `n − 2f` correct callers can split as low as `⌈(f+1)/2⌉` per bit, so a given bit
  need not be supported. The transition is enabled at `ControlMode.decisionEnabled`, where it is the
  only enabled silent transition, exactly when some bit is supported. Each of the two counts is
  monotone on its own: every ghost write is a first write, and `SpecStep.fail` and
  `SpecStep.callByzantine` move an id into the `id ∈ s.F` disjunct, which counts it at both
  bits. So a state that has passed the flip's mixedness guard leaves both bits supported
  ever after. Spec liveness is unclaimed beyond that.
- **The mode loop (D21) carries no value.** `SpecStep.coinFlip` names no coin bit and writes nothing
  but `mode`, so no bit can enter the system through the one probabilistic transition; licensing a coin
  bit would re-admit a Validity-breaking decision at probability `ε`. Its `hmix` guard, `f + 1`
  support at *each* bit, is where the specification holds the liveness half of Validity: under
  unanimity among the correct processes the other bit is never supported
  (`InputSupport.correct_supporter`), so the flip is unreachable and the unanimous path is Dirac.
- **The corrupted interface (D23) constrains nothing.** `SpecStep.retByzantine` moves no field,
  and `SpecStep.callByzantine` writes only at ids the `id ∈ s.F` disjunct already counts at both
  bits, so neither changes which bits are supported. What they add is trace behaviour,
  which is why both trace predicates are read at never-corrupted returners.
- **No specification fill transition.** The concrete adversary fills GBCA call entries through
  hidden byzantine `callG` transitions that carry no `callABA` event. Those entries are paid for by the `F` budget
  inside the count itself — the `id ∈ s.F` disjunct of `InputSupport` — rather than by a phantom
  ghost entry. A fill transition would have to place its entries knowing which process is corrupted later,
  a prophecy no forward simulation has (§ Why this shape, item 6).

The support invariant (`SpecSafety.SpecificationInvariant`), with
`InputSupport s v := f + 1 ≤ #{id | s.input id = some v ∨ id ∈ s.F}` (monotone in `F` and
`input`, `InputSupport.mono`), in two clauses: `F_le`, the corrupted set within budget, and
`val_support`, `val = some v → InputSupport s v`. The second is `SpecStep.decide`'s own guard at
the one transition that writes `val`; every transition that only grows the ghost carries it by
`InputSupport.mono`, and `SpecStep.callByzantine`, whose write may replace a recorded bit, carries
it
by `InputSupport.callByzantine`, the writer being counted through the `F` disjunct. Attribution of
the ghost's entries to genuine trace events is the separate label-history invariant
`SpecSafety.ValidityInvariant`, whose `input_source` clause the two correct `callABA` transitions restore
by recording the bit their own label carries; `SpecStep.callByzantine` takes that clause's second
disjunct, the corruption of its own entry. Validity endgame (the budget pigeonhole): at any `retABA
_ v` by a never-corrupted returner, `val_support` gives `f + 1` supporters; they cannot all lie in
the final `F` (`|F| ≤ f`), so some supporter is never corrupted (`exists_neverCorrupted_supporter`)
and its recorded input is a genuine prior `callABA`.

### D14 — TS 2 Validity (InputSupport guards)

The blueprint's TS 2 witnesses its binding step by a *single* correct process
(`∃ id ∉ F, call id = b`), and grade-1 / grade-0 dissent by a single correct dissenter — the same
singular-witness loss one level down, and `hybrid` built on it provably
violates Validity (§ Why this shape). ABDY22's implementation carries the `f + 1` via
Valid-set relay thresholds; TS 2 abstracts it to one witness.

`GBCA/Specification.lean` instead uses TS 1's `InputSupport` shape at every support guard, as
a count `f + 1 ≤ #{id | call id = some b ∨ id ∈ F}` at the bit that guard is about.
Binding here is negative (D19): the state carries `excluded : Finset Bool`, the bits the
instance can no longer hand out, and the internal τ-transition `bindUnset b` excludes one
bit at a time, write-once per bit and `excluded` monotone.

- `bindUnset b` counts support for the bit it spares, `!b`, alongside a quorum on the
  calls and `b ∉ excluded`;
- `retGrade1 v` counts support for the dissenting bit `!v`, alongside the live pair
  `v ∉ excluded ∧ (!v) ∈ excluded` for the bit it hands out — the same pair `retGrade2 v` reads;
- `retGrade0` hands out no bit and reads no live pair, only `(!bnd) ∈ excluded` for the bit
  `bnd` it announces: it carries one such count for **each** bit — which is exactly what
  witnesses that no single bit is the right answer — plus the grade-0 guard
  enforcing grade-2 / grade-0 exclusivity.

Directly `F`-blind — the count is monotone in `F` and `call`, so it is immune to later `fail`s — and
the budget pigeonhole transfers verbatim: among `f + 1` supporters some member is outside the final
`F`, hence a never-corrupted genuine caller. Corrupt supporters are paid for by the `F` budget
itself, with no phantom-call bookkeeping and no specification fills.

### D15 — the implementation derivation (`DESIGN-GBCARefinesSpecification.md`)

D14's superset counts must be discharged from the algorithm `GBCA.ByABDY.Algorithm`. The
connection is the `Invariant`
conjunct `input_support`:

```
∀ b j, j ∉ F → Message.input b ∈ sent j →
  (process j).input = some b ∨ f + 1 ≤ #{id | (process id).input = some b ∨ id ∈ F}
```

Preservation: `call` adds a holder; a `relay`'s `f + 1` senders of received messages are each in
`F`, a holder, or a prior correct non-holder sender (the pre-state conjunct closes); `byzantine`
senders are in `F`; `fail` grows the count and shrinks the triggers; the count is
monotone throughout. The derivation splits by D14 site.

- **The exclusion witness.** The relation's `exclusion_witness` bounds `excluded` from above
  by a monotone *exclusion witness* `ExclusionWitness P s b` (the opposite bit owns the unique
  quorum of `n − f` received `ECHO` messages, or an `n − f` quorum of processes is each corrupted or
  committed to a non-`b` `VOTE` payload — the two ways an `n − f` `VOTE b` quorum is made impossible
  forever). A value-bearing return restores it from its own ECHO5-level quorums: `retGrade2`'s
  `n − f` `ECHO5 v` quorum, and `retGrade1`'s `f + 1` received `BIND v` messages as the grade-1
  witness (all five D18 levels, not the source's compressed `VOTE`-level reading). Both route to a
  quorum of `n − f` received `VOTE v` messages at a correct process
  (`received_binds_of_echo5_quorum` then `voteQuorum_of_received_binds`); that quorum is itself the
  quorum, so `exclusionWitness_of_voteQuorum` witnesses `!v` excluded, and
  `not_exclusionWitness_of_voteQuorum` refutes any witness for `v` — the live half `v ∉
  excluded` of the guard pair, read against `exclusion_witness`.
- **The `bindUnset` guards.** These are derived separately, from an `ReceivedEchoQuorum` — at
  both value-bearing transitions via `receivedEchoQuorum_of_received_votes`, off the same correct
  process's received `VOTE v` messages. `bindUnset_guards` gets *both* `bindUnset` guards out of
  that one `n − f` `ECHO v` witness: refine it to a quorum of `n − f` received `INPUT v` messages
  (`inputQuorum_of_receivedEchoQuorum`), whose correct senders hold an input
  (`input_called`, D8) — that is the quorum guard (`quorum_of_messageQuorum`) — and whose
  count feeds `Invariant.support_of_received_inputs` for the `f + 1` InputSupport count.
- The `retGrade1`/`retGrade0` counts ride on the `|Valid| > 1` witness the returner itself holds:
  it is a quorum of `n − f ≥ f + 1` received `INPUT` messages for *each* bit, so
  `inputSupport_of_bothValid`
  closes both bits at once — which is what `retGrade0`'s two per-bit guards need, and what
  covers `retGrade1`'s dissent bit with no separate dissent-relay argument.

`SpecificationRelation.callSupport` carries every such count to the specification along
`call_eq`/`F_eq`. `call_eq` stays exact and the corruption transition needs no extra work — the superset
guards need nothing from the concrete relation but the entries of correct processes it already
mirrors.

Since the specification excludes by an internal τ-transition, an implementation return
meeting a specification state whose needed bit is not yet excluded is matched by the
two-step weak run `bindUnset (!v) ; retGrade2 v` (resp. `; retGrade1 v`),
`excludeThenRetGrade2_run`/`excludeThenRetGrade1_run`. `retGrade0` reads no live pair, but it does
need `1 ≤ excluded.card`, so it too takes the run (`excludeThenRetGrade0_run`) from an all-alive
state; every return transition runs the same decidable case split on `excluded`.

### D12′ — the DECIDED equivocation gap

D12 models DECIDED gossip as a single per-process entry, which cannot send `DECIDED 0` to
X and `DECIDED 1` to Y — an under-approximation inconsistent with the equivocating D5 sent
sets of graded agreement. D12′ mirrors D5 in the DECIDED sets: the network's `decidedSent` and
the round-loop variables' received sets, read as one object (`Composition/ABAState.lean`) as
`decidedSent : Fin n → Finset Bool` and `decidedReceived : Fin n → Fin n → Finset Bool`,
two maps that only grow. `sendDecided` inserts; delivery is the `decidedDeliver` synchronisation, per
(receiver, sender, bit), with soundness `b ∈ decidedSent j` on the network's half and an
at-most-once `b ∉ decidedReceived i j` guard on the receiver's; `byzantineDecided` is guarded *only*
by
`k ∈ F`. Correct sent sets stay at card ≤ 1 in reachable states (grade-2 witnesses fix
one bit), but no card invariant is needed. The invariant rewiring
(`HybridRefinesSpecification/Relation.lean`): `received_sound` becomes per-bit and
*correctness-free* (`b ∈ decidedReceived i j → b ∈ decidedSent j`, preserved by pure monotonicity,
since sent sets never shrink); `decided_source` becomes per sent bit
(`id ∉ F → b ∈ decidedSent id → ∃ r` grade-2 witness for `b`) — the equivocation-robust
form: corrupted equivocators may pad any bit's tally, but the pigeonhole at the `retABA` transition (`n − f`
distinct senders of `b`, `|F| ≤ f`, `n − f > f`) recovers a never-corrupted sender of `b`, whose
sent `b` carries the grade-2 witness that the phase-1 `SpecStep.decide` step and phase 2's
`AbstractState` witness both need.

## `Invariant`: the concrete invariant (`HybridRefinesSpecification/Relation.lean`)

Forty fields, docstring-numbered I0–I30 (a few numbers cover a small group of
fields), grouped:

- **The replacement flag against the corrupted set (I0)**: `corrupted_F`, the first field —
  `c.corrupted id = true ↔ id ∈ c.F`. The flag and the corrupted set live in separate
  components, written by the two halves of one `fail` transition, and this conjunct is what ties
  them (D23).
- **`F` equality**: `F_gbca`, `F_wcc` (every instance's `F` equals `c.F`), `F_card`.
- **Round structure**, keyed throughout on
  `RoundSettled g r := (g r).excluded ≠ ∅ ∨ (g r).grade = some false` — "round `r` is finished",
  which is strictly weaker than "round `r` has excluded a bit", since a grade-0 return excludes
  nothing itself:
  `down_settled` (closed rounds downward-closed), `quiescent` (cofinitely many rounds open),
  `round_bound`, `call_round`, `wcc_callRound`, `wcc_bound`/`wcc_called` (coin resolutions and
  W-calls only at closed rounds), `wcc_order`, `round_flip`.
  `RoundSettled.congr`/`RoundSettled.of_unchanged`
  are the two preservation lemmas every transition's unchanged facts feed.
- **The coin clauses, established at the resolving call**: `wcc_bound`, `wcc_order` and
  `flip_witness` are the conjuncts that read `(w r).val`, and the one transition that writes it
  is `callW`'s resolving call, so `Invariant.step_callW_resolve` carries all three. Its input is
  `Invariant.exists_correct_wccCaller`: the threshold counts more than `f` callers of round `r`
  and `F_card` bounds the corrupted set by `f`, so the callers outnumber it and one of
  them is never corrupted. That caller's `wcc_called`, `wcc_callRound` and `wccCalled_witness`
  carry `wcc_bound`, `wcc_order` and `flip_witness` in turn. `agree_bound`'s round-`r` corner is
  vacuous, `round_flip` at a correct process past round `r` contradicting `val = ⊥`. The
  other two transitions of `callW` — the input-enabledness loop and the recording call — move
  neither `val` nor `F`, and both go through `Invariant.step_callW_dirac`; `Invariant.step_callW`
  assembles the three off `WCC.step_callW_cases`.
- **Where an input and an estimate come from**: `input_gbcaRound0`, `input_gbcaRound0_permanent`,
  `input_called`,
  `phase_input`, `estimate0`, `estimate_ret`, `estimate_previous`, `estimate_previous_ne`,
  `call_of_previousRound`, `bind_succ` (a bit excluded at round `r + 1` was already excluded at round `r`,
  or round `r` closed graded 0 with round `r`'s coin at `.bit v` *or* `.top` — a `⊤` coin lets
  the adopting return pick any matching bit, so the coin disjunct alone does not determine `v`; only the
  grade 0 does, and every downstream use reads just that half), `grade0_chain`.
- **Bound rounds and DECIDED**: `grade2Bound_commit` (a round bound at grade 2 whose surviving
  bit `b` is
  still alive yields `Grade2Commitment` for `b` — the live-pair form, hypothesis-guarded so that no
  transition has to establish the pair to use it), `agree_bound` (keyed on the frontier reading
  `IsLastBound g r := (g r).excluded ≠ ∅ ∧ (g (r + 1)).excluded = ∅`), `grade2_needs_bind` (grade 2
  only: `retGrade2` reads the live pair, so a round graded `2` has a non-empty exclusion
  set — a grade-0 return reads no pair and constrains none), `grade2_source` and
  `decided_source` (both producing a `Grade2Witness`, the pair-free form),
  `received_sound` (D12′ per-bit and correctness-free — see above), `bound_quorum` (a round with
  a non-empty exclusion set has met the quorum).
- **Witnesses**: `excluded_support` (I28), `outcomeHolder_agree` (I29), `grade2Bound_agree` (I30)
  — the three conjuncts that state a round's value without the live pair; see § Witnesses.
- **Support sent sets**: `bind_support` (I26) — a round whose exclusion set names `!v` carries a
  permanent `f + 1` input-or-`F` sent set for `v` (`RoundLoopInputSupport`, the concrete mirror of
  TS 1's
  `InputSupport`), established
  at `bindUnset` — and `grade0_support` (I27), which keeps the `retGrade0` guards themselves at
  a round graded 0: `f + 1` F-blind call-or-`F` support for *each* bit, in count form. Both are
  permanent and monotone (`call` and `F` only grow). `support_of_call_count` reads any such count
  back as an input sent set by strong induction on the round — round 0 wholesale via
  `input_gbcaRound0_permanent`, `r ≥ 1` by deriving one correct caller whose `call_of_previousRound`
  routes into the previous round's `bind_support` or into its `grade0_support` count,
  a smaller instance of the same statement — and that is what supplies `SpecStep.decide`'s `hs`
  through phase 1's ghost sync, by `inputSupport_of_roundLoopInputSupport`. The both-bit shape of
  `grade0_support` is also what keeps grade 0 incompatible with an agreeing coin
  underneath it (`no_grade0_succ_of_support`), and what forces grade 0 one round down
  (`grade0_chain_of_both_supports`): `exists_correct_caller` turns the two counts into correct
  round-`(r + 1)` callers of opposite bits, which are opposite-valued carriers of round `r`'s
  outcome, and `outcomeHolder_agree` admits those only at a round graded 0.
- **Dissent bookkeeping**: `flip_witness`, `retG_witness`, `wccCalled_witness`,
  `idle_no_wccCall`, each keyed on the permanent `F`-free `DissentWitness` (with its
  `preserved` lemma, preservation whatever the transition writes). The support sent sets
  `bind_support`/`grade0_support` latently subsume much of this residue machinery — both are
  permanent `F`-free facts about a correct input — so folding the residue conjuncts into the sent sets is a
  recorded future refactor.

Each case of `HybridRefinesSpecification/Simulation.lean` proves `Invariant`-preservation for its
step class and then the `AbstractState`-level match above.

## The run lemmas (`HybridRefinesSpecification/WeakTransitions.lean`)

Pure `ABA.spec` weak-τ lemmas, no `Invariant`/`AbstractState` reasoning and no mention of the
concrete `(g, c, w)` state:

- `decide_step` — `SpecStep.decide` as a one-step `weakTau` run, built by
  `weakTau_of_step`. The transition is Dirac, so there is no chain to assemble.
- `weakStep_of_run_then_step` — packaging: a τ-run followed by a genuine step is a
  `weakStep`, with the run as the leading τ-closure, the step as the middle hyper-step
  (`hyperStep_pure_of_step`), and `weakTau_refl` as the trailing closure.

Those are all the run lemmas. The specification has two silent transitions, `SpecStep.coinFlip` and
`SpecStep.decide`; the abstract state never fires the first and fires the second once, so no case
needs a multi-step τ-chain and every guard discharge sits in the `Invariant`
(§ Transition dispositions).

## Why this shape

Each of the following adversarial-timing traces excludes a natural simpler alternative;
recording them is what fixes the design.

1. **Eager functional abstraction fails.** If the abstract state is a total function of
   the concrete (`a = absMap (g,c,w)`) with `a.val` tied to the concrete `bindUnset` transition,
   `SpecStep.decide` is forced the moment a round excludes the dissenting bit under unanimous
   calls — but a
   late joiner can then submit a dissenting `callABA`, enable a grade-0 at that round,
   steer the next round to spare the opposite value, grade it 2, and DECIDE against the
   already-committed abstract `val`. Hence laziness: the abstract state commits as late as possible.
2. **A flipping abstract state fails.** The abstract state could in principle match the concrete
coin transition with `SpecStep.coinFlip` rather than a stutter. Two things break. `coinFlip` is the
system's one non-Dirac transition, and `hybridSpecificationRelation` is a `diracRel`, so the abstract
system must stay a point mass at every reachable pair. And `flipPMF` puts mass `δ` on `exclude`:
that branch reaches `ControlMode.noTransitionEnabled`, where `SpecStep.decide` is disabled forever,
so on positive mass the abstract state could no longer match the `retABA` that arrives later. Hence
`mode_flipEnabled`: the abstract state stutters at every flip and keeps `SpecStep.decide` enabled.
3. **Unconditional correct-unanimity fails.** Requiring pairwise agreement of correct
   inputs whenever the abstract state is undecided is too strong: two opposite fresh inputs with
   nothing decided yet are reachable and would force a decision no support count backs. The
   lazy abstract state sidesteps the question entirely — it carries no unanimity constraint,
   because phase 1 decides nothing.
4. **Free re-propose loses the tie to a correct input (TS 1).** In the source blueprint's TS 1, the free
   re-propose and the free mixed-bind let a bit input only by a later-corrupted
   process win a return: input `1` from a lone process that is then `fail`ed is
   re-proposed and bound while every never-corrupted process input `0`. This forces the
   D13 `f + 1` `F`-blind support discipline.
5. **The singular witness loses the tie to a correct input (TS 2).** Deterministically at `n = 4, f = 1`,
   inputs `1,0,0,0`: TS 2's single-witness exclude of `0` fires off the sole `1`-holder,
   leaving `1` as round 0's surviving bit; `retGrade1`-adopt
   propagates `estimate := 1`, round-1 unanimity decides `1`, `fail 0`, `retABA 1 1` — yet
   every never-corrupted process input `0`. A single witness is exactly the
   D13 loss one level down; hence the D14 InputSupport guards.
6. **Fill-only designs cannot fix the value (the vote quorum).** One might try to discharge the
   D14 counts specification, filling empty `F`-entries at the *implementation* relation instead of
   counting them. This dies on a pre-corruption genuine call: at `n = 4, f = 1`, a genuine `callG 3
   0` forces the correct entry 3 to mirror `0`; after `fail 3` the adversary amplifies `INPUT 1` to
   a `BIND 1` and a visible `retGrade2 0 1`, but the spec state has `#callers(1) = 1 < 2` and entry
   3 is *genuinely full* — no τ fills it, since a fill needs an *empty* `F`-field. The spec does
   emit the trace, via a different run that answers `callG 3 0` with a loop and byzantine-fills
   entry 3 with `1` after `fail 3`; but that choice needs knowledge of the later `fail`, a prophecy
   out of reach of any forward simulation. So the tie to a correct input must be carried by `F`-blind *counts*
   (D14/`input_support`), not by specification fills — the sent set guards beat the fills.
7. **The first call commits, so the ghost takes no junk.** `RoundLoopStep.inputLoop` carries
   `c.processVariables.input ≠ none` and the commit transition `RoundLoopStep.input` carries `c.processVariables.input =
   none`, so a `callABA` at a correct process whose input is unset commits, and a process's first
   call is never absorbed by the loop (D36). On the abstract system `SpecStep.callSet` fires at the
   empty ghost entry and `SpecStep.callLoop` at the filled one, and `input_sync` is what matches the
   two guards to the concrete transition that fired. Every ghost write is therefore a first write, matched
   with the concrete commit, and the ghost holds each never-corrupted process's first call. The
   two-phase abstract state (D16) is a valid relation over this shape and is what
   `hybridRefinesSpecification` is built on; an eager abstract state, deciding before the first
   visible return, is not pursued.
