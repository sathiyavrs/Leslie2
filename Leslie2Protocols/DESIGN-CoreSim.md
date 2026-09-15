# Design — the core simulation `hybrid ⊑ ABA.spec` (`coreSim`)

Companion design document to the Lean proof in `ABA/Core/Rel.lean` (relation +
invariant), `ABA/Core/Inv.lean` (step inversion and invariant preservation),
`ABA/Core/Abs.lean` (the stutter rows and the assembly),
`ABA/Core/Run.lean` (abstract τ-run kit), and `ABA/Core/Sim.lean`
(the per-row simulation proof). It is the narrative account of that proof: what the
relation is, why it has the shape it has, and how each class of concrete step is answered.
Each Lean file's module docstring is the account of record for its own contents. The
`coreSim` proof prose in `blueprint/src/content.tex` condenses this document. The
spec-level repairs the simulation depends on are labelled D13/D14/D15 (Validity
provenance) and D12′ (DECIDED equivocation).

## Systems

```
hybridPre := specSide ∥ (syncProduct coreProcN ∥ (aNet ∥ wccLift))
hybrid    := ((hybridPre.abstract netEvtLabels).relabel).abstract hiddenAPI
target    : ProbabilisticForwardSimulation hybrid (ABA.spec P) coreRel
```

The four components are the round specifications, the `n` round loops, the ABA-side
network and the coin oracle, and they speak the extended alphabet of the protocol;
the rendezvous labels are hidden, the result is read back over `Lab n`, and
the sub-protocol API is hidden in turn (`ABDY/Hybrid.lean`). Corrupted-process
handshakes are covered by the Byzantine handshake rows, authorised by `k ∈ F` at `aNet`
(D11). See `Vocabulary/RoundLoop.lean`'s module docstring for the per-process algorithm and
deviations D9–D12′ (0-based rounds, the fused DECIDED-send in `retWPub`/`stepRound`,
per-process DECIDED sets — see § D12′ below).

Concrete state: `(g, (C, (A, w)))` with `g : ℕ → GBCA.SpecState`,
`C : ∀ j, CoreRec`, `A : ANetState`, `w : ℕ → WCC.SpecState`. The two ABA-side
components are read as one object `c : ABAState := (C, A)` through the accessors of
`ABDY/ABAState.lean` — `procs`, `decidedSent`, `decidedRecv`, `F` — and every clause below
names them, so the relation reads the hybrid state with no change of system.
Abstract state: `a : ABA.SpecState`.

## The relation: the lazy two-phase abstract state (deviation D16)

`coreRel := diracRel R₀` with `R₀ (g,(c,w)) a := Inv (g,c,w) ∧ Abs (g,c,w) a` — all
randomness couples outcome-to-outcome, so the abstract side stays Dirac.

The abstract state is **lazy** and **never-flipping**. It never fires `SpecStep.coinFlip`, so its
mode is `Mode.idle` at every state it reaches (field `mode_idle`), `SpecStep.decide` is
enabled throughout, and the concrete coin's resolving call couples to a stutter. And it never
decides *between* rows: it occupies one of two phases, keyed on `a.val`, and crosses from
the first to the second at the visible `retABA` that opens phase 2.

### `Abs` fields (`Core/Rel.lean`)

- `F_eq : a.F = c.F`
- `ret_eq : ∀ id, a.ret id = (c.procs id).returned`
- `mode_idle : a.mode = .idle` (the abstract state never fires `SpecStep.coinFlip`)
- `phase` — the two-phase disjunction on `a.val`:
  - **Phase 1** (pre-first-return): `a.val = none`, and the ghost record is synced on
    every committed input
    (`∀ id b, (c.procs id).input = some b → a.input id = some b`). The clause is
    one-way: it constrains `a.input` only at the entries where the concrete input is
    committed, and says nothing about the others.
  - **Phase 2** (post-first-return): `∃ v, a.val = some v`, `v` is permanently certified
    by a concrete `A`-lock (`∃ r, ACert P g c r v` — § Certificates), and every honest
    holder of an `A`-decision names `v` (`∀ j b', j ∉ c.F → AHolder P c j b' → b' = v`,
    the `F`-free universal that survives corruption of the original witnesses).

Phase 1 banks each genuine `callABA` with `SpecStep.callSet`, whose ghost overwrite —
licensed by the guard `val = ⊥` — restores the sync however much junk a concrete
self-loop has banked through `SpecStep.callLoop`. The abstract state stays undecided and answers
every hidden row with a stutter. The single `retABA` answer runs `SpecStep.decide` as the
τ-tail leading the return (§ Row dispositions), landing the abstract state in phase 2. From there
`a.val` pins the decided value for good, so every later row is a stutter, a
`SpecStep.callLoop`, or a direct `SpecStep.ret`.

### The frame lemma

`Abs` reads only three projections of the concrete state: `F`, the per-process
`input`/`returned` fields, and phase 2's certificate-and-holder pair. `Abs.frame` packages
exactly this — `Abs` transfers along any frame preserving `F`, `input`, `returned` and
carrying an `AbsFrame` (§ Certificates) for the last; the coin state is not among them,
so `Abs` transfers along any change of it. The frame lemma replaces the
per-row stutter arguments: every hidden row preserves the three projections, so its
`Abs`-match is one `Abs.frame` invocation rather than a bespoke
re-derivation (the six Stage-C stutter lemmas of `Core/Abs.lean` are all instances).

### Certificates: decided values stated without the live pair

Under D19 the state of a GBCA round records exclusion: `(g r).excluded : Finset Bool`
is written by `bindUnset`, and a value-bearing return needs the *live pair*
`(!v) ∈ (g r).excluded ∧ v ∉ (g r).excluded`. The relation does not state decided values through
that pair. It states them through certificates, which name their bit off a single
permanent membership `(!b) ∈ (g r).excluded` plus commitments that only `call`, `F` and the
honest `procs` fields can affect. That is the design, and it is sound; the certificates are what `Inv.decided_src`, `Inv.grade_A_src` and phase 2 of
`Abs` carry.

The certificate form is stronger than the specification requires. `bindUnset`
carries the guard `excluded = ∅`, so a round excludes at most once
(`GBCASafety.excluded_card_le_one`) and `excluded = {0,1}` is unreachable: a live pair
established by a return is in fact permanent, and pair-form invariants are maintainable.
Trading the certificates for the pair is therefore available as a simplification. It is
recorded here as an option and is not scheduled work: the exchange would touch
`decided_src`, `grade_A_src`, `Abs`'s phase 2 and every `AbsFrame` obligation, and the
certificate form needs no reachability argument of its own.

- **`ACommit P g c r b`** — the permanent commitments of an `A`-locked round: the live
  pair at every round `r' ≥ r` (round `r` itself included), every honest call above `r`,
  every honest est past `r`, and
  every honest `Carrier` of round `r`'s outcome names `b`. `Carrier` is the outcome-holder
  predicate — a round-`(r + 1)` GBCA call of `v`, or a committed est of `v` in the window
  between `retG r` and `retG (r + 1)`. Each component is monotone-stable: the first only
  loses instances as `excluded` grows, the rest read write-once `call` and honest `procs`
  fields.
- **`ACert P g c r b`** := `(g r).grade = some true ∧ (!b) ∈ (g r).excluded ∧ ACommit P g c r b`
  — an `A`-locked round whose surviving bit at lock time was `b`, plus those commitments.
  `(!b) ∈ excluded` is permanent (`excluded` only grows), so a certificate names `b` forever
  whatever else the round does. This, not a live pair, is what `Inv.decided_src` and
  `Inv.grade_A_src` produce and what phase 2 of `Abs` holds. `ACommit.of_frame` /
  `ACert.of_frame` transport both along any step that keeps `excluded`, `call`, honest
  `round`/`est`, reflects carriers and only grows `F` (`hF : c.F ⊆ c'.F` — the honesty
  side conditions are all of the form `id ∉ F`, so they must be re-derived through the
  larger set); `ACert.of_frame` additionally requires the round's grade preserved.
- **`Inv.excluded_supp` (I28)** — every exclusion keeps its D15 guard: `b ∈ (g r).excluded` implies
  `f + 1` F-blind call support for the spared bit `!b` at round `r`. Both `call` and `F`
  only grow, so the count is permanent, and `GBCA.exists_honest_caller` derives it into a
  never-corrupted caller of `!b`. That derivation is what recovers a round's value from the
  membership alone, with no live pair in hand.
- **`Inv.carrier_agree` (I29)** — any two honest carriers of round `r`'s outcome agree,
  unless the round is `C`-locked. This is the state residue of the order argument "two
  opposite value-bearing returns cannot both fire at one round": the first excludes the
  rival bit, and the second's liveness guard then fails. The conjunct carries that
  argument as state, so no row has to replay it.
- **`Inv.alock_agree` (I30)** — any two honest `AHolder`s agree globally, across rounds,
  where `AHolder P c id b` is a live `A`-grade `lastGrade = some (.A b)` or a sent
  `b ∈ decidedSent id`. Each new holder is compared at its own `retG` row, where the
  fresh return's live pair meets the existing holder's certificate.
- **`AbsFrame P g g' c c'`** — the `Abs`-side transport a step row hands back: every
  `ACert` on the pre-state has an `ACert` on the post-state *at some round* (`∃ r1` — the
  bit is preserved, the round is re-existentialized, which is what lets a row relocate a
  certificate), and phase 2's holder universal survives given its certificate. `AbsFrame.refl` covers every row that touches
  neither certificates nor holders. Each `Inv.step_*` lemma returns `Inv ∧ AbsFrame`,
  and `Abs.frame` consumes exactly that; the certificate is what pins a *fresh* holder
  in the corner where every original witness has been corrupted away.

## Row dispositions

Concrete steps are read through the Stage-A inversion lemmas of `Core/Inv.lean`,
which take a `hybrid` transition back through the two hiding frames to the rows of
its four components; each class is one row of `Core/Sim.lean`.

Three of the four Stage-A lemmas — `hybrid_step_callABA`, `hybrid_step_retABA`,
`hybrid_step_tau` — take I0 as a hypothesis. A round loop's row is guarded by its own
replacement flag and the ABA-side network's row by the corrupted set; the two live in
separate components, and I0 is what identifies them, so that the reading each lemma
delivers speaks of `F` alone (D23). `corrupted_eq_false_iff` is the one-line form of that
translation.

| concrete row | label | abstract answer |
|---|---|---|
| every hidden handshake (`callG`/`retG`/`callW`/`retW`), `bindUnset`, DECIDED gossip τ | τ | stutter (`Abs.frame`; only `Inv` moves) |
| `callW` at the row that resolves `WCC_r`'s coin | τ | constant-coupled stutter via the generic `stutter_step` (`Core/Sim.lean`): coupling `Ω := μ_C.map (·, pure a)`, so `ω = pure (pure a)` and `ω.bind id = pure a` (the abstract state never flips, so every outcome of the draw lands on the same `a`) |
| `callABA id b`, phase 1, genuine (idle-exit input) | `callABA id b` | `SpecStep.callSet` (the overwrite banks the concrete input and restores the ghost sync) |
| `callABA id b`, otherwise (phase 2, or a concrete self-loop) | `callABA id b` | `SpecStep.callLoop` (first-write-wins; no `Abs`-field change) |
| `retABA id b`, `id ∉ F`, phase 1 | `retABA id b` | `decide_step` then `SpecStep.ret` (`weakStep_of_run_then_step`) — see below |
| `retABA id b`, `id ∉ F`, phase 2 | `retABA id b` | `SpecStep.ret` directly (phase 2's holder universal, applied to the honest DECIDED sender it derives, pins `b = v`) |
| `retABA id b`, `id ∈ F` | `retABA id b` | `SpecStep.retByz` (D23): neither side moves, in either phase |
| `fail id` | `fail id` | `SpecStep.fail` (same two guards via `F_eq`; robust in both phases) |

A `retG` label carries the round's bound bit beside the graded outcome (D29). The whole
rendezvous alphabet is hidden before the core simulation sees it, so that bit reaches the
abstract side on no label, and the row that reads it — the round instance's return — is a
τ of `hybrid` answered by a stutter. `Abs` holds no field for it, and no invariant conjunct
reads it: the round's binding content enters the core simulation through `(g r).excluded`,
which the bit is a reading of.

The single run is `decide_step` (`Core/Run.lean`), fired at the phase-1 `retABA`.
`SpecStep.decide` is Dirac, so the run is one step; what the row supplies is its three
guards, each read off the concrete state at the round `rA` of the `ACert` derived from a
never-corrupted DECIDED sender of `b`.

- `hv : a.val = none` — phase 1 itself.
- `hm : a.mode ≠ .terminal` — the `mode_idle` field: an abstract state that never flips never reaches it.
- `hs : SuppOK P a b` — `suppOK_of_inputSupp` (`Core/Rel.lean`) reads the concrete
  input-or-`F` sent set `Inv.bind_supp rA b` through phase 1's ghost sync.

The step writes `val := some b` and returns the mode to `Mode.idle`, so `mode_idle`
survives it and phase 2 is entered with the certificate at `rA` in hand. The trailing
`SpecStep.ret` is glued on by `weakStep_of_run_then_step`: the run is the leading
τ-closure and the visible `retABA` the middle hyper-step.

## The spec repairs as design

Four spec-level repairs make the simulation possible; each is a permanent, `F`-blind
provenance discipline. D13/D14 repair the abstract specs (TS 1 = `ABA.spec`,
TS 2 = the `GBCA` specification) against the papers' Validity; D15 is the F-blind counting
form of their support guards, discharged implementation-side by the `GBCASim`
derivation; D12′ closes a DECIDED-equivocation gap.

### D13 — TS 1 Validity (ghost provenance)

The source blueprint's TS 1 fails the papers' Validity: its free re-propose (while
`val = ⊥`) and its free mixed-bind lose input provenance, so a bit input only by a
later-corrupted process can win. The repair principle: a value may circulate only with
`f + 1` distinct supporters — at most `f` processes are *ever* corrupted, so `f + 1`
supporters always include a never-corrupted one, and provenance survives dynamic
corruption with no future-peeking guard (`3f < n` supplies `n − 2f ≥ f + 1`).

What `Spec/ABA.lean` carries:

- **Ghost** `input : Fin n → Option Bool` in `SpecState`. `SpecStep.callSet` records by
  overwrite under the guard `val = ⊥`; `SpecStep.callLoop` is unguarded and records
  first-write-wins (`input := if s.input id = none then update … else s.input`). Both are
  sound — every event of either rule is a genuine `callABA` trace event — and the
  overwrite is load-bearing: it is what keeps the record revisable while the abstract state is
  undecided (§ Why this shape, item 7). No honesty guards anywhere; every support count
  is `F`-blind, hence immune to later `fail`s.
- **`SpecStep.decide`** is the sole writer of `val`, and its provenance guard
  `hs : SuppOK P s b`, the `f + 1` recorded-or-corrupt supporters of `b`, is the entire
  constraint on the value decided. It restricts which bit may be decided, and does so by
  design: `n − 2f` honest callers can split as low as `⌈(f+1)/2⌉` per bit, so a given bit
  need not be supported. The rule is enabled at `Mode.locked`, where it is the only
  enabled `τ`-rule, exactly when some bit is supported. No individual count is monotone —
  `SpecStep.callSet`'s overwrite takes its writer out of one of the two supporter sets —
  but the sum of the two counts is, so a state that has passed the flip's mixedness guard
  leaves some bit supported ever after. Spec liveness is unclaimed beyond that.
- **The mode loop (D21) carries no value.** `SpecStep.coinFlip` names no coin bit and
  writes nothing but `mode`, so no bit can enter the system through the one probabilistic
  rule; licensing a coin bit would re-admit a Validity-breaking decision at probability
  `ε`. Its `hmix` guard, `f + 1` support at *each* bit, is where the specification holds
  the liveness half of Validity: under honest unanimity the other bit is never supported
  (`SuppOK.honest_supporter`), so the flip is unreachable and the unanimous path is Dirac.
- **The corrupted interface (D23) constrains nothing.** `SpecStep.retByz` moves no field,
  and `SpecStep.callByz` writes only at ids the `id ∈ s.F` disjunct already counts at both
  bits, so neither changes which bits are supported. What they add is trace behaviour,
  which is why both trace predicates are read at never-corrupted returners.
- **No spec-side fill rule.** The concrete adversary fills GBCA call entries through hidden
  byz `callG` rows that carry no `callABA` event. Those entries are paid for by the
  `F` budget inside the count itself — the `id ∈ s.F` disjunct of `SuppOK` — rather than
  by a phantom ghost entry. A fill rule would have to place its entries knowing which
  process is corrupted later, a prophecy no forward simulation has
  (§ Why this shape, item 6).

Provenance invariant (`SpecSafety.SpecInv`), with
`SuppOK s v := f + 1 ≤ #{id | s.input id = some v ∨ id ∈ s.F}` (monotone in `F` and
`input`, `SuppOK.mono`), in two clauses: `F_le`, the corrupted set within budget, and
`val_supp`, `val = some v → SuppOK s v`. The second is `SpecStep.decide`'s own guard at
the one rule that writes `val`; every rule that only grows the ghost record carries it by
`SuppOK.mono`, and `SpecStep.callByz`, whose write may replace a recorded bit, carries it
by `SuppOK.callByz`, the writer being counted through the `F` disjunct. Attribution of the
record to genuine trace events is the separate label-history invariant `SpecSafety.ValInv`,
whose `input_src` clause the two honest `callABA` rules restore by recording the bit their
own label carries; `SpecStep.callByz` takes that clause's second disjunct, the corruption
of its own entry.
Validity endgame (the budget pigeonhole): at any `retABA _ v` by a never-corrupted
returner, `val_supp` gives `f + 1` supporters; they cannot all lie in the final `F`
(`|F| ≤ f`), so some supporter is never corrupted
(`exists_neverCorrupted_supporter`) and its recorded input is a genuine prior `callABA`.

### D14 — TS 2 Validity (SuppOK guards)

The blueprint's TS 2 certifies its binding step by a *single* honest witness
(`∃ id ∉ F, call id = b`), and `B`/`C` dissent by a single honest dissenter — the same
singular-witness provenance loss one level down, and `hybrid` built on it provably
violates Validity (§ Why this shape). ABDY22's implementation carries the `f + 1` via
Valid-set relay thresholds; TS 2 abstracts it to one witness.

`Spec/GBCA.lean` instead uses TS 1's `SuppOK` shape at every provenance guard, as a count
`f + 1 ≤ #{id | call id = some b ∨ id ∈ F}` at the bit that guard is about. Binding here
is negative (D19): the state carries `excluded : Finset Bool`, the bits the instance can no
longer hand out, and the internal τ-transition `bindUnset b` excludes one bit at a time,
write-once per bit and `excluded` monotone.

- `bindUnset b` counts support for the bit it spares, `!b`, alongside a quorum on the
  calls and `b ∉ excluded`;
- `retB v` counts support for the dissenting bit `!v`, alongside the live pair
  `v ∉ excluded ∧ (!v) ∈ excluded` for the bit it hands out — the same pair `retA v` reads;
- `retC` hands out no bit and reads no live pair, only `(!bnd) ∈ excluded` for the bit
  `bnd` it announces: it carries one such count for **each** bit — which is exactly what
  certifies that no single bit is the right answer — plus the `C`-side grade guard
  enforcing A/C exclusivity.

Directly `F`-blind — the count is monotone in `F` and `call`, so it is
immune to later `fail`s — and the budget pigeonhole transfers verbatim: among `f + 1`
supporters some member is outside the final `F`, hence a never-corrupted genuine caller.
Corrupt supporters are paid for by the `F` budget itself, with no phantom-call
bookkeeping and no spec-side fills.

### D15 — the implementation derivation (`GBCASim`)

D14's superset counts must be discharged from `GBCA.Impl`. The link is the `Inv`
conjunct `input_supp`:

```
∀ b j, j ∉ F → Msg.input b ∈ sent j →
  (proc j).input = some b ∨ f + 1 ≤ #{id | (proc id).input = some b ∨ id ∈ F}
```

Preservation: `call` adds a holder; a `relay`'s `f + 1` receipt senders are each in
`F`, a holder, or a prior honest non-holder sender (the pre-state conjunct closes); `byz`
senders are in `F`; `fail` grows the count and shrinks the triggers; the count is
monotone throughout. The derivation splits by D14 site.

- **The exclude certificate.** The relation's `excluded_cert` bounds `excluded` from above by a
  monotone *exclude certificate* `ExcludedCert P s b` (the opposite bit owns the unique `n − f`
  `ECHO` receipt quorum, or an `n − f` wall of processes is each corrupted or committed to
  a non-`b` `VOTE` payload — the two ways an `n − f` `VOTE b` quorum is made impossible
  forever). A value-bearing return restores it from its own ECHO5-level evidence: `retA`'s
  `n − f` `ECHO5 v` quorum, and `retB`'s `f + 1` `BIND v` receipts as the grade-1 witness
  (all five D18 levels, not the source's compressed `VOTE`-level reading). Both route to
  an `n − f` `VOTE v` receipt quorum at an honest process
  (`bind_receipts_of_echo5_quorum` then `voteQuorum_of_bind_receipts`); that quorum is
  itself the wall, so `excludedCert_of_voteQuorum` certifies `!v` excluded, and
  `not_excludedCert_of_voteQuorum` refutes any certificate for `v` — the live half `v ∉ excluded`
  of the guard pair, read against `excluded_cert`.
- **The `bindUnset` guards.** These are derived separately, from an `EchoQuorum` — at
  both value-bearing rows via `echoQuorum_of_vote_receipts`, off the same honest process's
  `VOTE v` receipts. `bindUnset_guards` gets *both* `bindUnset` guards out of that one
  `n − f` `ECHO v` certificate: refine it to an `n − f` `INPUT v`
  receipt quorum (`inputQuorum_of_echoQuorum`), whose honest senders hold an input
  (`input_called`, D8) — that is the quorum guard (`quorum_of_msg_quorum`) — and whose
  count feeds `Inv.supp_of_input_receipts` for the `f + 1` SuppOK count.
- The `retB`/`retC` counts ride on the `|Valid| > 1` evidence the returner itself holds:
  it is an `n − f ≥ f + 1` `INPUT` receipt quorum for *each* bit, so `suppI_of_valid`
  closes both bits at once — which is what `retC`'s two per-bit guards need, and what
  covers `retB`'s dissent bit with no separate dissent-relay argument.

`InstRel.spec_supp` carries every such count to the specification side along
`call_eq`/`F_eq`. `call_eq` stays exact and the corruption row needs no extra work — the
superset guards need nothing from the concrete relation but the honest entries it already
mirrors.

Since the specification excludes by an internal τ-transition, an implementation return
meeting a specification state whose needed bit is not yet excluded is answered by the
two-step weak run `bindUnset (!v) ; retA v` (resp. `; retB v`),
`excludeThenRetA_run`/`excludeThenRetB_run`. `retC` reads no live pair, but it does need
`1 ≤ excluded.card`, so it too takes the run (`excludeThenRetC_run`) from an all-alive
state; every return row runs the same decidable case split on `excluded`.

### D12′ — the DECIDED equivocation gap

D12 models DECIDED gossip as a single per-process entry, which cannot send `DECIDED 0`
to X and `DECIDED 1` to Y — an under-approximation inconsistent with the equivocating
D5 sent sets of graded agreement. D12′ mirrors D5 in the DECIDED sets: the network's
`dsent` and the round-loop records' receipt rows, read as one object (`ABDY/ABAState.lean`)
as `decidedSent : Fin n → Finset Bool` and
`decidedRecv : Fin n → Fin n → Finset Bool`, records that only grow. `sendDecided`
inserts; delivery is the `ddlv` rendezvous, per (receiver, sender, bit), with soundness
`b ∈ decidedSent j` on the network's half and an at-most-once `b ∉ decidedRecv i j`
guard on the receiver's; `byzD` is guarded *only* by `k ∈ F`. Honest sent sets stay at card ≤ 1 in reachable
states (A-grade certificates pin one bit), but no card invariant is needed. The invariant
rewiring (`Core/Rel.lean`): `recv_sound` becomes per-bit and *honesty-free*
(`b ∈ decidedRecv i j → b ∈ decidedSent j`, preserved by pure monotonicity, since sent
sets never shrink); `decided_src` becomes per sent bit
(`id ∉ F → b ∈ decidedSent id → ∃ r` A-lock cert for `b`) — the equivocation-robust
form: corrupted equivocators may pad any bit's tally, but the `retABA`-row pigeonhole
(`n − f` distinct senders of `b`, `|F| ≤ f`, `n − f > f`) recovers a never-corrupted
sender of `b`, whose sent `b` carries the A-lock certificate that the phase-1
`SpecStep.decide` step and phase 2's `Abs` certificate both need.

## `Inv`: the concrete invariant (`Core/Rel.lean`)

Forty fields, docstring-numbered I0–I30 (a few numbers cover a small group of
fields), grouped:

- **The replacement flag against the corrupted set (I0)**: `corrupted_F`, the first field —
  `c.corrupted id = true ↔ id ∈ c.F`. The flag and the corrupted set live in separate
  components, written by the two halves of one `fail` row, and this conjunct is what ties
  them (D23).
- **F-lockstep**: `F_g`, `F_w` (every instance's `F` equals `c.F`), `F_card`.
- **Round structure**, keyed throughout on
  `Closed g r := (g r).excluded ≠ ∅ ∨ (g r).grade = some false` — "round `r` is finished",
  which is strictly weaker than "round `r` has excluded a bit", since a `C`-return excludes
  nothing itself:
  `down_closed` (closed rounds downward-closed), `quiescent` (cofinitely many rounds open),
  `round_bound`, `call_round`, `w_call_round`, `w_bound`/`w_called` (coin resolutions and
  W-calls only at closed rounds), `w_order`, `round_flip`. `Closed.congr`/`Closed.of_frame` are the two
  transport lemmas every row's frame facts feed.
- **The coin clauses, established at the resolving call**: `w_bound`, `w_order` and
  `flip_alock` are the conjuncts that read `(w r).val`, and the one row that writes it is
  `callW`'s resolving row, so `Inv.step_callW_resolve` carries all three. Its input is
  `Inv.exists_honest_wcaller`: the threshold counts more than `f` callers of round `r`
  and `F_card` bounds the corrupted set by `f`, so the callers outnumber it and one of
  them is never corrupted. That caller's `w_called`, `w_call_round` and `wcalled_residue`
  carry `w_bound`, `w_order` and `flip_alock` in turn. `agree_locked`'s round-`r` corner is
  vacuous, `round_flip` at an honest process past round `r` contradicting `val = ⊥`. The
  other two rows of `callW` — the input-enabledness loop and the recording call — move
  neither `val` nor `F`, and both go through `Inv.step_callW_dirac`; `Inv.step_callW`
  assembles the three off `WCC.step_callW_inv`.
- **Input/est provenance**: `input_g0`, `input_g0_perm`, `input_called`, `phase_input`,
  `est0`, `est_ret`, `est_prev`, `est_prev_ne`, `call_prov`, `bind_succ` (a bit excluded at
  round `r + 1` was already excluded at round `r`, or round `r` closed `C`-locked with round
  `r`'s coin at `.bit v` *or* `.top` — a `⊤` coin lets the adopting return pick any
  matching bit, so the coin disjunct alone does not pin `v`; only the `C`-lock does, and
  every downstream use reads just that half), `c_chain`.
- **Locks and DECIDED**: `a_commit` (an `A`-locked round whose surviving bit `b` is still
  alive yields `ACommit` for `b` — the live-pair form, hypothesis-guarded so that no row
  has to establish the pair to use it), `agree_locked` (keyed on the frontier reading
  `IsLastBound g r := (g r).excluded ≠ ∅ ∧ (g (r + 1)).excluded = ∅`), `gradeA_needs_bind`
  (A-side only: `retA` reads the live pair, so an `A`-graded round has a non-empty
  exclusion set — a `C`-return reads no pair and constrains none), `grade_A_src` and
  `decided_src` (both producing an `ACert`, the pair-free form), `recv_sound` (D12′
  per-bit and honesty-free — see above), `bound_quorum` (a round with a non-empty
  exclusion set has met the quorum).
- **Certificates**: `excluded_supp` (I28), `carrier_agree` (I29), `alock_agree` (I30) — the
  three conjuncts that state a round's value without the live pair; see § Certificates.
- **Support sent sets**: `bind_supp` (I26) — a round whose exclusion set names `!v` carries a
  permanent `f + 1` input-or-`F` sent set for `v` (`InputSupp`, the concrete mirror of TS 1's
  `SuppOK`), established
  at `bindUnset` — and `clock_supp` (I27), which keeps a `C`-locked round's `retC` guards
  themselves: `f + 1` F-blind call-or-`F` support for *each* bit, in count form. Both are
  permanent and monotone (`call` and `F` only grow). `supp_of_call_count` reads any such
  count back as an input sent set by strong induction on the round — round 0 wholesale via
  `input_g0_perm`, `r ≥ 1` by deriving one honest caller whose `call_prov` provenance
  routes into the previous round's `bind_supp` or into its `clock_supp` count, a smaller
  instance of the same statement — and that is what supplies `SpecStep.decide`'s `hs`
  through phase 1's ghost sync, by `suppOK_of_inputSupp`. The both-bit shape of `clock_supp` is also
  what keeps a `C`-lock incompatible with an agreeing coin underneath it
  (`no_cgrade_succ_of_supp`), and what forces a `C`-lock one round down
  (`c_chain_of_both_supports`): `exists_honest_caller` turns the two counts into honest
  round-`(r + 1)` callers of opposite bits, which are opposite-valued carriers of round
  `r`'s outcome, and `carrier_agree` admits those only at a `C`-locked round.
- **Dissent bookkeeping**: `flip_alock`, `retg_residue`, `wcalled_residue`,
  `idle_no_wcall`, each keyed on the permanent `F`-free `DissentResidue` (with its
  `transport` lemma for frame-agnostic preservation). The support sent sets `bind_supp`/
  `clock_supp` latently subsume much of this residue machinery — both are permanent
  `F`-free provenance facts — so folding the residue conjuncts into the sent sets is a
  recorded future refactor.

Each row of `Core/Sim.lean` proves `Inv`-preservation for its step class and then the
`Abs`-level match above.

## The run kit (`Core/Run.lean`)

Pure `ABA.spec`-side weak-τ lemmas, no `Inv`/`Abs` reasoning and no mention of the
concrete `(g, c, w)` state:

- `decide_step` — `SpecStep.decide` as a one-step `weakTau` run, built by
  `weakTau_of_step`. The rule is Dirac, so there is no chain to assemble.
- `weakStep_of_run_then_step` — packaging: a τ-run followed by a genuine step is a
  `weakStep`, with the run as the leading τ-closure, the step as the middle hyper-step
  (`hyperStep_pure_of_step`), and `weakTau_refl` as the trailing closure.

That is the whole kit. The specification has two `τ`-rules, `SpecStep.coinFlip` and
`SpecStep.decide`; the abstract state never fires the first and fires the second once, so no row
needs a multi-step τ-chain and every guard discharge sits on the `Inv` side
(§ Row dispositions).

## Why this shape

Each of the following adversarial-timing traces excludes a natural simpler alternative;
recording them is what pins the design.

1. **Eager functional abstraction fails.** If the abstract state is a total function of
   the concrete (`a = absMap (g,c,w)`) with `a.val` tied to the concrete `bindUnset` row,
   `SpecStep.decide` is forced the moment a round excludes the dissenting bit under unanimous
   calls — but a
   late joiner can then submit a dissenting `callABA`, enable a `C`-grade at that round,
   steer the next round to spare the opposite value, `A`-lock it, and DECIDE against the
   already-committed abstract `val`. Hence laziness: the abstract state commits as late as possible.
2. **A flipping abstract state fails.** The abstract state could in principle answer the concrete coin row
   with `SpecStep.coinFlip` rather than a stutter. Two things break. `coinFlip` is the
   system's one non-Dirac rule, and `coreRel` is a `diracRel`, so the abstract side must
   stay a point mass at every reachable pair. And `flipPMF` puts mass `δ` on `exclude`: that
   branch reaches `Mode.terminal`, where `SpecStep.decide` is disabled forever, so on positive
   mass the abstract state could no longer answer the `retABA` that arrives later. Hence
   `mode_idle`: the abstract state stutters at every flip and keeps `SpecStep.decide` enabled.
3. **Unconditional honest-unanimity fails.** Requiring pairwise agreement of honest
   inputs whenever the abstract state is undecided is too strong: two opposite fresh inputs with
   nothing decided yet are reachable and would force a decision no support count backs. The
   lazy abstract state sidesteps the question entirely — it carries no unanimity constraint,
   because phase 1 decides nothing.
4. **Free re-propose loses provenance (TS 1).** In the source blueprint's TS 1, the free
   re-propose and the free mixed-bind let a bit input only by a later-corrupted
   process win a return: input `1` from a lone process that is then `fail`ed is
   re-proposed and bound while every never-corrupted process input `0`. This forces the
   D13 `f + 1` `F`-blind support discipline.
5. **The singular witness loses provenance (TS 2).** Deterministically at `n = 4, f = 1`,
   inputs `1,0,0,0`: TS 2's single-witness exclude of `0` fires off the sole `1`-holder,
   leaving `1` as round 0's surviving bit; `retB`-adopt
   propagates `est := 1`, round-1 unanimity decides `1`, `fail 0`, `retABA 1 1` — yet
   every never-corrupted process input `0`. A single certifying witness is exactly the
   D13 loss one level down; hence the D14 SuppOK guards.
6. **Fill-only designs cannot be value-pinned (the wall).** One might try to discharge
   the D14 counts spec-side, filling empty `F`-entries at the *implementation* relation
   instead of counting them. This dies on a pre-corruption genuine call: at `n = 4,
   f = 1`, a genuine `callG 3 0` forces the honest entry 3 to mirror `0`; after `fail 3`
   the adversary amplifies `INPUT 1` to a `BIND 1` and a visible `retA 0 1`, but the spec
   state has `#callers(1) = 1 < 2` and entry 3 is *genuinely full* — no τ fills it, since a
   fill needs an *empty* `F`-field. The spec does emit the trace, via a different run that
   answers `callG 3 0` with a loop and byz-fills entry 3 with `1` after `fail 3`; but that
   choice needs knowledge of the later `fail`, a prophecy out of reach of any forward
   simulation. So provenance must be carried by `F`-blind *counts* (D14/`input_supp`), not
   by spec-side fills — the sent set guards beat the fills.
7. **Deciding early junks the ghost (the lazy wall).** This is the argument D16 rests on,
   and with it `SpecStep.callSet`'s overwrite. `SpecStep.callLoop`'s ghost write is
   first-write-wins, and `SpecStep.callSet` is guarded by `val = ⊥`, so once the abstract state has
   decided, a `callABA` row can only answer with `callLoop` and the record is frozen
   wherever it is already set. Suppose the abstract state decided before the first return. A
   concrete `inputLoop` answers `callABA id b̂` as a no-op while `id`'s input is
   uncommitted; the decided abstract state must answer it with `callLoop`, banking ghost `b̂`; and a
   later genuine `callABA id b` (`b ≠ b̂`) can never overwrite it, leaving `a.input id`
   permanently wrong. At `n = 4, f = 1`, mixed round-0 inputs force the early decision,
   pre-emptive self-loops junk every future `b`-inputter, and a round-0 `retC` plus a
   `⊤`-coin flip develop an `A`-lock for `b` whose `f + 1` support is carried entirely by
   junked inputters — leaving `SpecStep.decide`'s `hs` for `b` undischargeable. Hence the
   two-phase abstract state (D16): it decides only under the first return, so a genuine call always
   answers `SpecStep.callSet` and the overwrite repairs whatever a self-loop banked. The
   overwrite and the laziness are one design: each is useless without the other.
