# Design — the GBCA refinement `GBCA.ByABDY.composition ⊑ GBCA.specificationOverRoundAlphabet`
(`refinesSpecification`)

Companion design document to the Lean proof in `ABA/GBCA/ABDY/Invariant.lean` (the inductive
invariant), `ABA/GBCA/ABDY/ExclusionWitness.lean` (the exclusion witnesses),
`ABA/GBCA/ABDY/SpecificationRelation.lean` (the relation, the specification guards and the run
lemmas) and `ABA/GBCA/ABDY/RefinesSpecification.lean` (the matching and the simulation), against the
algorithm in
`ABA/GBCA/ABDY/Algorithm.lean` (deviation D18: all five message levels of ABDY22's Algorithm 6)
and the specification shape in `ABA/GBCA/Specification.lean` (deviation D19: the exclusion set
`excluded : Finset Bool` as the state shape, with the bound value announced on the return labels,
D29). The refinement paragraphs of `blueprint/src/content.tex` — the exclusion witness, the
`VOTE` quorum, and the two-step exclusion-then-return run — are a condensation of this document.

## Systems

```
composition P r : System (RoundState P.n) (ExtendedLabel P.n)     -- ABDY22 Algorithm 6, D1/D5/D8/D18
specificationOverRoundAlphabet P r : System (SpecState P.n) (ExtendedLabel P.n)     -- graded-binding spec, D1/D14/D15/D19
target : ForwardSimulation (composition P r) (specificationOverRoundAlphabet P r) (specificationRelation P r)
```

Both systems are Dirac-transition LTSs. The refinement reaches the ℕ-indexed families through
`ForwardSimulation.family` (`ABA/ABDY/Substitution.lean`), whose family lifting
takes its broadcast ingredient from `GBCA.ByABDY.specificationRelation_corrupt`.

### The algorithm (D18): the five message levels

The algorithm transcribes ABDY22's Algorithm 6. The message type is

```lean
inductive Message : Type
  | input (b : Bool)         -- ⟨echo,  b⟩ of Algorithm 6
  | echo  (b : Bool)         -- ⟨echo2, b⟩
  | vote  (v : Option Bool)  -- ⟨echo3, v⟩,  v ∈ {0, 1, ⊥}
  | bind  (v : Option Bool)  -- ⟨echo4, v⟩
  | echo5  (v : Option Bool)  -- ⟨echo5, v⟩
```

and `ProcessVariables` carries one write-once field per level above `INPUT`: `sentEcho : Option Bool`,
`sentVote sentBind sentEcho5 : Option (Option Bool)`, next to `input`, `sentInput : Bool → Bool` and
`returned`. `RoundState` is the pair of the per-process round variables and the round's
network state, the latter carrying the D5 set-based network (`sent`, `received`), the corrupted set
`F`, and the write-once ghost field `bound : Option Bool`. Derived counts: `receivedCount i m`
(distinct senders of the exact message `m` delivered to `i`), `echoCount`/`voteCount`/`bindCount`/
`echo5Count i` (distinct senders of *any* payload at that level), and `bothValid P s i` (a quorum
of `n − f` received `INPUT b` messages at `i` for **each** bit — Algorithm 6's
`|approvedVals| > 1`).

The transitions, all silent except the labelled API ones. Three conditions run across the
algorithm. The D8 participation guard (`input ≠ none`) is on every protocol send,
including the echo5 level, and on all three returns. The levels are taken in the
wait-until order of Algorithm 6 from the `BIND` level down: each of those levels
requires the sender's own send at the level below (`hlv`), the returns requiring
the sender's own `ECHO5`. The vote level requires no own send, the `ECHO` it
reads being multicast by an `upon` handler and not on the main thread. And the
block boundaries are denials: within a return block the `⊥` transition denies its
block's case (a) at either bit, and the returns read as Algorithm 6's
`if (a) … elif (b) … else …`, each carrying the denials of the cases above it.

* `call` / `callLoop` — record the input, multicast `INPUT b` / input-enabled
  self-loop;
* `deliver` — adversarial move of a sent message into a `received` cell;
* `relay` — `f + 1` received `INPUT b` messages, re-multicast `INPUT b` (amplification);
* `echo` — `n − f` received `INPUT b` messages, multicast `ECHO b` (write-once);
* `voteBit` — `n − f` received `ECHO b` messages, multicast `VOTE b` (write-once);
* `voteBot` — `n − f` received `ECHO` messages of any payload, `bothValid`, and no `n − f` `ECHO b`
  quorum at either bit, multicast `VOTE ⊥`;
* `bindBit` — `n − f` received `VOTE b` messages and own `VOTE` out, multicast `BIND b`
  (write-once);
* `bindBot` — `n − f` received `VOTE` messages of any payload, own `VOTE` out, `bothValid`, and no
  `n − f` `VOTE b` quorum at either bit, multicast `BIND ⊥`;
* `echo5Bit` — `n − f` received `BIND b` messages and own `BIND` out, multicast `ECHO5 b`
  (write-once);
* `echo5Bot` — `n − f` received `BIND` messages of any payload, own `BIND` out, `bothValid`, and no
  `n − f` `BIND b` quorum at either bit, multicast `ECHO5 ⊥`;
* `byzantine` — a corrupted sender multicasts anything;
* `retGrade2 id v` — a quorum of `n − f` received `ECHO5 v` messages, the process called and its
  own `ECHO5` out (grade 2 — case (a), which heads the chain and denies nothing);
* `retGrade1 id v` — `n − f` received `ECHO5` messages of any payload, at least one received
  `ECHO5 v` message, **`f + 1` received `BIND v` messages**, and `bothValid`, the process called,
  its own `ECHO5` out and case (a) denied at either bit (`hnotGrade2`) (grade 1 — Algorithm 6's
  line-25 condition: the `t + 1` `echo4` check is what puts a correct `BIND v`
  behind every grade-1 output);
* `retGrade0 id` — a quorum of `n − f` received `ECHO5 ⊥` messages and `bothValid`, the process
  called, its own `ECHO5` out, case (a) denied at either bit (`hnotGrade2`), and
  case (b) denied in reduced form (`hnotGrade1`: `∀ v, (∃ k, echo5 (some v) ∈ received id k)
  → receivedCount (.bind (some v)) < f + 1`) — the reduction is sound because case
  (b)'s other two conjuncts, the `n − f` any-`ECHO5` quorum and `bothValid`, are
  this transition's own `hcnt` and `hval`, an `n − f` `ECHO5 ⊥` quorum being in
  particular an `n − f` any-`ECHO5` quorum (grade 0);
* `fail` — D1 determinised corruption.

The three return transitions each announce a bit and write it back, and no other transition
touches the field. `GBCA.ByABDY.boundOf sent F out` is the bit a return of outcome
`out` announces where the round has none on record: `v` at a value-bearing
outcome, and at grade `0` the payload of a correct `⟨VOTE, b⟩` sender, `true` where
there is none. A correct `⟨VOTE, b⟩` sender holds a quorum of `n − f` received `⟨ECHO, b⟩`
messages and at most one bit carries such a quorum, so on a reachable
state at most one branch applies. A return announces
`bound.getD (boundOf sent F out)`, so the round announces one bit on all of its
returns. The bit is a ghost output (D29): it enters no guard of Algorithm 6 and
no field a program holds.

The load-bearing depth of the witness a return carries: **every grade-≥1 output names a
bit with a correct `BIND` behind it** — `retGrade2` via `n − f` `ECHO5 v` →
correct `ECHO5` sender → `n − f` received `BIND v` messages → correct binder; `retGrade1` via
`f + 1 > |F|` received `BIND v` messages directly — and a correct `BIND v` sits on a quorum of
`n − f` received `VOTE v` messages. The `VOTE` level is write-once, so that
quorum is the object the binding argument counts (paper Lemmas 4.8/4.9 through
E.9).

### The specification (D19): the exclusion set

`SpecState` is `call : Fin n → Option Bool`, `ret : Fin n → Bool`,
`excluded : Finset Bool`, `grade : Option Bool`, `F : Finset (Fin n)`; initially
`excluded = ∅`. Binding is *negative* information: `excluded` is the set of bits the
instance can no longer hand out. The transitions:

* `call` / `callLoop` — as in every instance spec (D15 file conventions);
* `bindUnset b` (τ) — guards `s.quorum P`,
  `f + 1 ≤ #{id | s.call id = some (!b) ∨ id ∈ s.F}` (the D15 InputSupport count,
  at the *surviving* bit `!b`), and `hd0 : s.excluded = ∅`; effect
  `excluded := insert b s.excluded`;
* `retGrade2 id v bnd` — guards `v ∉ s.excluded`, `(!v) ∈ s.excluded`,
  `(!bnd) ∈ s.excluded`, `s.grade = none ∨ s.grade = some true`,
  `s.ret id = false`; effect `grade := some true`, mark returned;
* `retGrade1 id v bnd` — guards `v ∉ s.excluded`, `(!v) ∈ s.excluded`,
  `(!bnd) ∈ s.excluded`, the D15 dissent count
  `f + 1 ≤ #{id' | s.call id' = some (!v) ∨ id' ∈ s.F}`, `s.ret id = false`;
  effect: mark returned;
* `retGrade0 id bnd` — guards `(!bnd) ∈ s.excluded`, the two D15 counts (one per
  bit), `s.grade = none ∨ s.grade = some false`, `s.ret id = false`; effect
  `grade := some false`, mark returned;
* `fail` — D1 corruption, `excluded` untouched.

Each return announces `bnd` on its label `.retG r id out bnd` under the single
guard `(!bnd) ∈ s.excluded`. A reachable state excludes at most one bit, so the
guard determines `bnd` as the complement of the excluded one, and all the
returns of a round announce one bit. A value-bearing return carries
`(!v) ∈ s.excluded` too, so it announces `bnd = v`. This is what makes binding a
property of the trace alone (`GBCA.BindingTrace`, `specInst_binding`).

The `hd0` guard admits `bindUnset` from the empty set only, so an instance excludes
at most once and every reachable state has `excluded ∈ {∅, {b}}`
(`GBCASafety.excluded_card_le_one`). The once-only exclude is also what keeps a round
completable: after a grade-2 return a second exclusion would leave no live bit for the
value-bearing returns while the grade-2 guard blocks `retGrade0`, stranding the processes
yet to return.

`excluded` is monotone (only `bindUnset` writes it, by `insert`), so the graded
binding property is structural: an excluded bit is never handed out (`v ∉ excluded`
guards both value-bearing returns), every grade-2 or grade-1 return establishes `(!v) ∈ excluded`
whence any two value-bearing returns agree on the surviving bit, and a
grade-0 return forces `excluded ≠ ∅` permanently — from that moment at most one bit is
ever alive, which is the paper's Binding. Where a handed-out bit came from (D14/D15) is carried by
`bindUnset`'s InputSupport count for the surviving bit: a bit `v` handed out at
grade ≥ 1 requires `(!v) ∈ excluded`, whose `bindUnset (!v)` witnessed `f + 1`
F-blind callers of `v`; the budget pigeonhole (`|F| ≤ f` forever) recovers a
never-corrupted genuine caller of `v`.

## The relation

```lean
structure SpecificationRelation (P : Parameters) (s : RoundState P.n) (t : SpecState P.n) : Prop where
  invariant       : Invariant P s
  call_eq   : ∀ id, t.call id = (s.processVariables id).input
  ret_eq    : ∀ id, t.ret id = (s.processVariables id).returned
  F_eq      : t.F = s.F
  exclusion_witness : ∀ b, b ∈ t.excluded → ExclusionWitness P s b
  bound_excluded : t.excluded = excludedOf s.bound
  grade2_witness : t.grade = some true  → ∃ v i, P.n - P.f ≤ s.receivedCount i (.echo5 (some v))
  grade0_witness : t.grade = some false → ∃ i,   P.n - P.f ≤ s.receivedCount i (.echo5 none)
```

`call_eq`/`ret_eq`/`F_eq` are the exact abstraction clauses, identical in shape to every other instance
relation of the development. `grade2_witness`/`grade0_witness` are the grade-2/grade-0 exclusivity
witnesses, read at the `ECHO5` level (the level the returns read): two opposing `n − f` `ECHO5`
quorums intersect in a correct process with two different `ECHO5` payloads, contradicting the
write-once `echo5_once` — which is what discharges the spec's grade guards.

`exclusion_witness` is the load-bearing novelty: the spec's `excluded` is bookkeeping the
protocol records nothing, so the relation carries a *witness on the pattern of received messages*
for every excluded bit. Note the direction — the clause bounds `excluded` from above (`excluded ⊆ {b |
ExclusionWitness P s b}`) and never from below.

`bound_excluded` is the one clause that bounds `excluded` from below, through the
implementation's ghost field: `excludedOf` is `∅` at `bound = none` and
`{!β}` at `bound = some β`, and the equation holds because the exclusion fires
inside the round's first return, which is also the transition that writes the bit. Two
things follow. It discharges the guard `(!bnd) ∈ excluded` of a return that
announces a bit already on record, and with `exclusion_witness` it gives
`SpecificationRelation.bound_witness`: the bit on record carries an exclusion witness for its
complement. Each return transition therefore splits on `bound`: with a bit on record
the guard is discharged and the transition is matched by `ret` alone, and with the field
unwritten `excluded` is empty and the transition is matched by the two-step run.

## The exclusion witnesses

```lean
/-- Case A: the opposite bit owns the (unique) quorum of `n − f` received
`ECHO` messages. -/
def ReceivedEchoQuorum (P : Parameters) (s : RoundState P.n) (v : Bool) : Prop :=
  ∃ i, P.n - P.f ≤ s.receivedCount i (.echo v)

/-- Case B: an `n − f` quorum of processes each of which is corrupted or has
committed its write-once `VOTE` field to a payload other than `some b`. -/
def VoteQuorumAgainst (P : Parameters) (s : RoundState P.n) (b : Bool) : Prop :=
  P.n - P.f ≤ (Finset.univ.filter
    (fun j => j ∈ s.F ∨ ∃ w, (s.processVariables j).sentVote = some w ∧ w ≠ some b)).card

/-- The exclusion witness licensing `b ∈ excluded` at the specification. -/
def ExclusionWitness (P : Parameters) (s : RoundState P.n) (b : Bool) : Prop :=
  ReceivedEchoQuorum P s (!b) ∨ VoteQuorumAgainst P s b
```

Both disjuncts exclude `b` by making a quorum of `n − f` received `VOTE b` messages — the
sole source of any grade-≥1 witness for `b` — impossible forever:

* **Case A** (`ReceivedEchoQuorum P s (!b)`). Any `VOTE b` quorum contains a correct
  `VOTE b` sender (`n − f > f ≥ |F|`), whose `vote_confirmed` quorum is an
  `n − f` `ECHO b` quorum; two same-level `n − f` quorums for different bits
  share a correct sender (`exists_correct_received_of_two_quorums`, `(n−f)+(n−f)−n > f`) that
  multicast two `ECHO` payloads, contradicting the write-once `echo_once`.
  This is `receivedEchoQuorum_unique`.
* **Case B** (`VoteQuorumAgainst P s b`). Any later `n − f` `VOTE b` quorum `Q` has all its non-`F`
  members committed to `sentVote = some (some b)` (`received_subset_sent` + `vote_once`), so `Q`
  meets the quorum `D` only inside `F`: `|Q| + |D| ≤ n + |Q ∩ D| ≤ n + f`, i.e. `2(n − f) ≤ n + f`,
  i.e. `n ≤ 3f` — against `P.hResilience`. The quorum is the state-predicate form of the paper's
  Lemma 4.9 counting argument ("`n − f` received messages give `≥ n − f − |F|` correct committed
  voters, leaving
  `≤ f < n − 2f` free correct votes").

The three obligations on the witness:

**(i) Monotonicity.** The received sets only grow (`deliver`), `sentVote` is
write-once and never unset (guard `sentVote = none` on `voteBit`/`voteBot`,
no transition clears it), and `F` only grows (`fail`); every other transition touches
neither `received`, `sentVote` nor `F`. Packaged as

```lean
theorem ExclusionWitness.mono {s s' : RoundState P.n} {b : Bool}
    (hrecv : ∀ i j m, m ∈ s.received i j → m ∈ s'.received i j)
    (hvote : ∀ j w, (s.processVariables j).sentVote = some w → (s'.processVariables j).sentVote = some w)
    (hF : s.F ⊆ s'.F) : ExclusionWitness P s b → ExclusionWitness P s' b
```

applied per transition exactly like `InputSupport.mono`. This is
what keeps `exclusion_witness` a stutter-stable field: `excluded` never shrinks and the
witnesses never expire.

**(ii) Availability at the exclusion moments.** The simulation fires `bindUnset`
only inside return runs, and each return's own quorum yields the needed
witness:

```lean
/-- Any quorum of `n − f` received `VOTE v` messages excludes the opposite bit … -/
theorem exclusionWitness_of_voteQuorum (hI : Invariant P s) {i v}
    (h : P.n - P.f ≤ s.receivedCount i (.vote (some v))) : ExclusionWitness P s (!v)

/-- … and witnesses that `v` itself is alive. -/
theorem not_exclusionWitness_of_voteQuorum (hI : Invariant P s) {i v}
    (h : P.n - P.f ≤ s.receivedCount i (.vote (some v))) : ¬ ExclusionWitness P s v
```

`exclusionWitness_of_voteQuorum` lands in `VoteQuorumAgainst (!v)` — the quorum's members are
each in `F` or committed to `some v ≠ some (!v)`, so the quorum itself is the quorum.
`not_exclusionWitness_of_voteQuorum` is the two Case A/B refutations above. Both value-bearing
returns route into a `VOTE` quorum by the derivation chain

```lean
theorem voteQuorum_of_received_binds (hI : Invariant P s) {i v}
    (h : P.f + 1 ≤ s.receivedCount i (.bind (some v))) :
    ∃ k, k ∉ s.F ∧ P.n - P.f ≤ s.receivedCount k (.vote (some v))

theorem received_binds_of_echo5_quorum (hI : Invariant P s) {i v}
    (h : P.n - P.f ≤ s.receivedCount i (.echo5 (some v))) :
    ∃ k, k ∉ s.F ∧ P.n - P.f ≤ s.receivedCount k (.bind (some v))
```

(`retGrade2`: echo5 quorum → correct `ECHO5` sender → `echo5_confirmed`; then `n − f ≥ f + 1` and
the first chain: received `BIND` messages → correct binder (`f + 1 > |F|`) → `bind_confirmed`.
`retGrade1`: its `f + 1` received `BIND v` messages enter the first chain directly.) The
grade-0 return has no distinguished bit; its quorum yields a witness for
*some* bit:

```lean
theorem exclusionWitness_of_echo5Bot_quorum (hI : Invariant P s) {i}
    (h : P.n - P.f ≤ s.receivedCount i (.echo5 none)) : ∃ b, ExclusionWitness P s b
```

Proof shape (this is the sketch's Case A/Case B dichotomy, formalised): the
quorum contains a correct `ECHO5 ⊥` sender `p` (`n − f > f`); `echo5Bot_confirmed`
gives `n − f ≤ s.bindCount p`, so `p` holds an any-payload `BIND` from a correct process
sender `k`. Classical case split on `∃ m b', m ∉ s.F ∧ Message.vote (some b') ∈
s.sent m` (a correct bit-voter exists somewhere):

* **yes** — `vote_confirmed` at `m` is an `n − f` `ECHO b'` quorum, so
  `ReceivedEchoQuorum P s b'` and `ExclusionWitness P s (!b')` by Case A;
* **no** — then `k` cannot have sent `BIND (some v')` (its `bind_confirmed`
  `VOTE v'` quorum would contain a correct bit-voter), so `k` sent `BIND ⊥`
  and `bindBot_confirmed` gives `n − f ≤ s.voteCount k`: every non-`F` sender in
  that quorum committed a vote (`vote_once`) that is not a bit (no correct
  bit-voter exists), i.e. `sentVote = some none ≠ some (some b)` for **both**
  bits — `VoteQuorumAgainst` holds for both bits, `ExclusionWitness` for either.

**(iii) The `bindUnset` guards are discharged.** `bindUnset b` needs the
quorum guard and `f + 1` F-blind caller support for `!b`. At a value-bearing
return of `v` (excluding `b = !v`, support bit `!(!v) = v`), both come from one
`ECHO` witness:

```lean
theorem bindUnset_guards (hR : SpecificationRelation P s t) {v} (hq : ReceivedEchoQuorum P s v) :
    t.quorum P ∧ P.f + 1 ≤ (Finset.univ.filter
      (fun id => t.call id = some v ∨ id ∈ t.F)).card
```

— refine the `ECHO v` quorum to a quorum of `n − f` received `INPUT v` messages
(`inputQuorum_of_receivedEchoQuorum`), whose correct senders hold an input
(`input_called`, D8): that is the quorum guard (`quorum_of_messageQuorum`), and
its count feeds `Invariant.support_of_received_inputs` → `SpecificationRelation.callSupport` for the
InputSupport count. The `ReceivedEchoQuorum v` input is supplied by
`receivedEchoQuorum_of_received_votes` off the derived `VOTE v` quorum
(`n − f ≥ f + 1`). At the grade-0 return (excluding an arbitrary witnessed `b*`,
support bit `!b*`), both guards come from the returner's own
`bothValid`: the per-bit quorum of `n − f` received `INPUT` messages gives the quorum guard
through `quorum_of_messageQuorum`/`input_called`, and `inputSupport_of_bothValid` gives the
`f + 1` count for **either** bit — so the guard is available no matter which
bit the witness names.

### Case A / Case B as named invariants

The soundness fact "the surviving bit at any grade-0 return is determined by the messages received
in the prefix" is not a lemma of the simulation file; it is the conjunction of the
properties of the witness above, and it is what makes a *plain forward*
simulation sufficient (no prophecy): at every moment the simulation must
commit an exclusion, the impl state already contains a monotone witness naming
the excluded bit, and no extension ever produces the quorum a return needs for a witnessed
bit (`not_exclusionWitness_of_voteQuorum` against `ExclusionWitness.mono`). The two named
carriers:

* **Case A** — `exclusionWitness_of_voteQuorum` (a correct `VOTE v`, equivalently an
  `ECHO v` quorum, excludes `!v` forever): quorum intersection on the write-once
  `ECHO` level.
* **Case B** — the **no**-branch of `exclusionWitness_of_echo5Bot_quorum` (a
  grade-0 return over an all-⊥ correct vote prefix excludes both bits): the
  `VoteQuorumAgainst` counting on the write-once `VOTE` level.

## Exclusion scheduling and run shapes

The specification excludes by an internal τ-transition, so an implementation
return that needs a not-yet-excluded bit excluded is matched by a two-step weak
run through `weakLStep_tauThen`. **Every** return transition does the same decidable
case split on the specification's `excluded`, and the run is enabled whenever
the exclusion is missing, whatever returns came before. Every run carries
`hd0 : t.excluded = ∅`, the `bindUnset` guard, and each run's label carries the
bit the transition announces:

```lean
/-- `bindUnset (!v) ; retGrade2 v` from an all-alive state (`excluded = ∅`). -/
theorem excludeThenRetGrade2_run {r t id v}
    (hq : t.quorum P)
    (hw : P.f + 1 ≤ (Finset.univ.filter
      (fun k => t.call k = some v ∨ k ∈ t.F)).card)
    (hlive : v ∉ t.excluded) (hd0 : t.excluded = ∅)
    (hg : t.grade = none ∨ t.grade = some true) (hr : t.ret id = false) :
    (specInst P r).weakLStep t (.retG r id (.grade2 v) v)
      { t with excluded := insert (!v) t.excluded, grade := some true,
               ret := Function.update t.ret id true }
```

(the `bindUnset (!v)` support guard reads `some (!(!v))`; `Bool.not_not` rewrites it to `hw`'s `some
v`, and `retGrade2`'s `v ∉ insert (!v) t.excluded` follows from `hlive` and `v ≠ !v`).
`excludeThenRetGrade1_run` is the same with the dissent count `f + 1 ≤ #{k | t.call k = some (!v) ∨
k ∈ t.F}` in place of the grade guard, landing in `{ t with excluded := insert (!v) t.excluded, ret
:= … }`. The grade-0 run excludes one arbitrary bit:

```lean
/-- `bindUnset b ; retGrade0` from an all-alive state (`excluded = ∅`). -/
theorem excludeThenRetGrade0_run {r t id b}
    (hq : t.quorum P)
    (hw : P.f + 1 ≤ (Finset.univ.filter
      (fun k => t.call k = some (!b) ∨ k ∈ t.F)).card)
    (hd0 : t.excluded = ∅)
    (hwT : P.f + 1 ≤ #{k | t.call k = some true  ∨ k ∈ t.F})
    (hwF : P.f + 1 ≤ #{k | t.call k = some false ∨ k ∈ t.F})
    (hg : t.grade = none ∨ t.grade = some false) (hr : t.ret id = false) :
    (specInst P r).weakLStep t (.retG r id .grade0)
      { t with excluded := insert b t.excluded, grade := some false,
               ret := Function.update t.ret id true }
```

(`retGrade0`'s `1 ≤ excluded.card` holds because `insert` is nonempty).

### Where `hd0` comes from at the call sites

The two value-return transitions derive it from the branch they are in rather than
carrying it in the relation. At `retGrade2`/`retGrade1` the transition already holds
`hlive : v ∉ t.excluded` (the witness refutation) and enters the run branch
under `hexcluded : (!v) ∉ t.excluded`, and a `Finset Bool` missing both `v` and `!v` is
empty:

```lean
theorem excluded_empty_of_both {d : Finset Bool} {v : Bool}
    (h1 : v ∉ d) (h2 : (!v) ∉ d) : d = ∅
```

so the call sites read `excludeThenRetGrade2_run hq hw hlive (excluded_empty_of_both
hlive hexcluded) hgr hret`, and likewise for `retGrade1`. The `retGrade0` transition splits on
`Finset.eq_empty_or_nonempty t.excluded` outright, so its empty branch *is* `hd0`
and its nonempty branch is matched by a single `Step.retGrade0`.

### Which bit the grade-0 return excludes

`retGrade0` fires the run only from `t.excluded = ∅` (otherwise `1 ≤ t.excluded.card` already holds
and a single `Step.retGrade0` is the matching step). The excluded bit is `b* := Classical.choose
(exclusionWitness_of_echo5Bot_quorum …)` — the witnessed bit its quorum names: the opposite of
the unique bit voted by a correct process when one exists (Case A branch), and canonically `false`
in the neither-bit-decidable case (Case B branch, where both bits are witnessed and the choice is
arbitrary). Soundness never depends on the choice: both specification guards of `bindUnset b*` hold
for either bit (they read `bothValid`), and a witnessed bit can never carry a later return's quorum,
so no future transition is obstructed by the pick — if some later `retGrade1 v` were to need `v`
alive, its quorum proves `¬ ExclusionWitness P s' v`, and `ExclusionWitness.mono` shows `v` was
never witnessed, hence never picked.

### The matching table

| implementation transition | label | matching specification run | relation obligations beyond `Invariant.step` |
|---|---|---|---|
| `call` | `callG r id b` | `Step.call` (guard via `call_eq`) | `call_eq`/`ret_eq` re-pointwise; `exclusion_witness` by `ExclusionWitness.mono` (input write only); the grade witnesses untouched |
| `callLoop` | `callG r id b` | `Step.callLoop` | all fields unchanged |
| `deliver` | τ | stutter (`weakLSilent_refl`) | `exclusion_witness` via `ExclusionWitness.mono` (received grows); the grade witnesses via `receivedCount_le_receiveMessage` |
| `relay` | τ | stutter | unchanged but the sender's `sentInput` |
| `echo` | τ | stutter | unchanged but the sender's `sentEcho` |
| `voteBit` / `voteBot` | τ | stutter | `sentVote` goes `none → some _`: `ExclusionWitness.mono`'s persistence hypothesis holds vacuously-forward (quorum members already committed) |
| `bindBit` / `bindBot` | τ | stutter | unchanged but the sender's `sentBind` |
| `echo5Bit` / `echo5Bot` | τ | stutter | unchanged but the sender's `sentEcho5` (nothing in the relation reads `sentEcho5` outside `Invariant`) |
| `byzantine` | τ | stutter | unchanged but the `sent` set of a corrupted sender |
| `retGrade2 id v` | `retG r id (A v)` | `(!v) ∈ excluded`: single `Step.retGrade2`; else: `excludeThenRetGrade2_run` | see below |
| `retGrade1 id v` | `retG r id (B v)` | `(!v) ∈ excluded`: single `Step.retGrade1`; else: `excludeThenRetGrade1_run` | see below |
| `retGrade0 id` | `retG r id C` | `excluded ≠ ∅`: single `Step.retGrade0`; else: `excludeThenRetGrade0_run` on `b*` | see below |
| `fail id` | `fail id` | `Step.fail` (`corrupt` on both) | `corrupt_F_eq`; `excluded` untouched by spec `corrupt`; `exclusion_witness` via `ExclusionWitness.mono` (`corrupt_received`/`corrupt_processVariables`/`corrupt_F_subset`); the grade witnesses via `corrupt_receivedCount` |

The three return transitions in detail. Common first move: derive the correct
`VOTE`-level quorum —

* `retGrade2`: `hcnt : n − f ≤ receivedCount id (.echo5 (some v))` →
  `received_binds_of_echo5_quorum` → `voteQuorum_of_received_binds` (via
  `n − f ≥ f + 1`) → `hvq : n − f ≤ receivedCount k (.vote (some v))`;
* `retGrade1`: `hbind : f + 1 ≤ receivedCount id (.bind (some v))` →
  `voteQuorum_of_received_binds` → `hvq`;

then

1. `hlive : v ∉ t.excluded` — from `exclusion_witness` contraposed by
   `not_exclusionWitness_of_voteQuorum hvq`;
2. grade guard (`retGrade2` only) — `grade_ne_false_of_echo5_quorum`: the `ECHO5 v`
   quorum against `grade0_witness`'s `ECHO5 ⊥` quorum meets in a correct
   double `ECHO5` sender, contradicting `echo5_once`;
3. dissent count (`retGrade1` only) — `callSupport (inputSupport_of_bothValid hval (!v))`;
4. case `(!v) ∈ t.excluded`: single labelled step. Case `(!v) ∉ t.excluded`: run, with
   `bindUnset_guards` fed by `receivedEchoQuorum_of_received_votes hvq` and `hd0` by
   `excluded_empty_of_both hlive hexcluded`;
5. restore: `exclusion_witness` — old bits by `ExclusionWitness.mono` (the step only sets
   `returned`), the new bit `!v` by `exclusionWitness_of_voteQuorum hvq`;
   `grade2_witness := ⟨v, id, hcnt⟩` (`retGrade2`), the other grade witnesses by
   monotonicity or vacuity.

`retGrade0`: `hwT`/`hwF` from `inputSupport_of_bothValid hval`, the grade-0 guard from
`grade_ne_true_of_echo5Bot_quorum` (`ECHO5 ⊥` quorum against `grade2_witness`'s
`ECHO5 v` quorum, correct double `ECHO5` sender, `echo5_once`), the run's `b*` and its
witness from `exclusionWitness_of_echo5Bot_quorum`, the `bindUnset` quorum guard
from `quorum_of_messageQuorum` on `bothValid`'s `INPUT` quorum; restore
`grade0_witness := ⟨id, hcnt⟩` and `exclusion_witness` as above with `ExclusionWitness b*`
for the new member.

Value agreement needs no dedicated lemmas: agreement between successive returns
is the guard pair `v ∉ excluded ∧ (!v) ∈ excluded` itself, discharged per transition by
`not_exclusionWitness_of_voteQuorum` (for `∉`) and the case analysis (for `∈`).

The announced bit is discharged the same way. A value-bearing return announces its own value
(`SpecificationRelation.retBound_eq`): the return's quorum of `n − f` received `VOTE v` messages
refutes a witness for `v`, so a bit already on record is `v` by
`SpecificationRelation.bound_witness`, and a bit computed here is `v` by `boundOf`. A grade-0 return
announces `boundOf`'s bit, whose complement is witnessed by `exclusionWitness_boundOf_grade0`: a
correct bit-voter's `vote_confirmed` quorum is Case A for the opposite bit, and where there is no
correct bit-voter the all-⊥ quorum (`exclusionWitness_of_noCorrectVote`) witnesses both bits at
once. In
that all-⊥ run no bit is ever handed out, and the bit the grade-0 returns announce is the surviving
one — `boundOf` reads `true` there, and the run excludes `false` — which is sound because the bit is
a ghost output and answers no process.

## The full list of invariants

### Shared machinery

The lemmas the proof draws on, most of them common to the instance refinements of
the development; the `ECHO5`-level silent transitions (`echo5Bit`/`echo5Bot`) preserve every clause
by a write elsewhere, identically in shape to `bindBit`/`bindBot`, and need nothing beyond it:

* the weak-transition lemmas of `Framework/FamilySimulation.lean`:
  `System.weakLStep_of_step` and `weakLStep_tauThen`;
* network plumbing: `received_subset_sent`, `receivedCount_le_receiveMessage`, `mem_multicast_sent`,
  `mem_receiveMessage_received`, `exists_sender_notMem`, `exists_correct_received_of_two_quorums`,
  the `corrupt_*` lemmas on what a corruption leaves unchanged, `corrupt_F_eq`;
* the corruption budget `F_card` and the D15 input machinery: `InputSupport`,
  `InputSupport.mono`, `input_origin`, `input_support`, `input_called`,
  `Invariant.support_of_received_inputs`, `inputSupport_of_bothValid`,
  `SpecificationRelation.callSupport`, `quorum_of_messageQuorum`, `inputQuorum_of_receivedEchoQuorum`;
* the `ECHO`-level witness: `ReceivedEchoQuorum`, `receivedEchoQuorum_unique`,
  `receivedEchoQuorum_of_received_votes`, and `bindUnset_guards` (quorum + InputSupport count
  out of one `ReceivedEchoQuorum`);
* conformance and write-once clauses `echo_confirmed`, `echo_once`, `vote_input`,
  `vote_confirmed`, `bind_once`, `bind_confirmed` (`bind_once` serves here as a
  conformance fact only — grade exclusivity is read at the `ECHO5` level).

### `Invariant` clauses at the `VOTE` and `ECHO5` levels

```lean
/-- Correct `VOTE` multicasts are recorded in the write-once `sentVote`. -/
vote_once : ∀ j w, j ∉ s.F → Message.vote w ∈ s.sent j → (s.processVariables j).sentVote = some w
/-- Correct `BIND ⊥` is backed by `n − f` received `VOTE` messages of any payload. -/
bindBot_confirmed : ∀ j, j ∉ s.F → Message.bind none ∈ s.sent j → P.n - P.f ≤ s.voteCount j
/-- Correct `ECHO5` multicasts are recorded in the write-once `sentEcho5`. -/
echo5_once : ∀ j w, j ∉ s.F → Message.echo5 w ∈ s.sent j → (s.processVariables j).sentEcho5 = some w
/-- Correct `ECHO5 b` is backed by a quorum of `n − f` received `BIND b` messages. -/
echo5_confirmed : ∀ j b, j ∉ s.F → Message.echo5 (some b) ∈ s.sent j →
  P.n - P.f ≤ s.receivedCount j (.bind (some b))
/-- Correct `ECHO5 ⊥` is backed by `n − f` received `BIND` messages of any payload. -/
echo5Bot_confirmed : ∀ j, j ∉ s.F → Message.echo5 none ∈ s.sent j → P.n - P.f ≤ s.bindCount j
/-- Correct `ECHO5` senders hold an input (D8, one level up). -/
echo5_input : ∀ j w, j ∉ s.F → Message.echo5 w ∈ s.sent j → (s.processVariables j).input ≠ none
```

`vote_once` and `bindBot_confirmed` are forced by the exclusion witnesses (`VoteQuorumAgainst`
counting and the Case B branch of `exclusionWitness_of_echo5Bot_quorum`); the echo5
clauses mirror the per-level pattern one level up, with
`echo5_once`/`echo5_confirmed`/`echo5Bot_confirmed` load-bearing (grade exclusivity and the
two derivation chains) and `echo5_input` kept for pattern uniformity only.
Preservation is by the same three schemas as every other clause: the
`_once` clauses by the `sentEcho5 = none`/`sentVote = none` send guards, the
`_confirmed` clauses by the sending transition's own guard on received messages plus count
monotonicity, and everything else is preserved by a write elsewhere. Count monotonicity needs the
any-payload analogues of `receivedCount_le_receiveMessage`:

```lean
theorem voteCount_le_receiveMessage (s : RoundState n) (i j : Fin n) (m : Message) (i' : Fin n) :
    s.voteCount i' ≤ (s.receiveMessage i j m).voteCount i'
-- likewise bindCount_le_receiveMessage
```

(same one-line `Finset.card_le_card` proof at both levels).

### The witness and derivation lemmas

Collected statements (all defined in `GBCA/ABDY/ExclusionWitness.lean`, the two grade lemmas
in `GBCA/ABDY/SpecificationRelation.lean`):

```lean
def VoteQuorumAgainst (P : Parameters) (s : RoundState P.n) (b : Bool) : Prop := …   -- § the exclusion witnesses
def ExclusionWitness (P : Parameters) (s : RoundState P.n) (b : Bool) : Prop :=
  ReceivedEchoQuorum P s (!b) ∨ VoteQuorumAgainst P s b

theorem ExclusionWitness.mono {s s' : RoundState P.n} {b : Bool}
    (hrecv : ∀ i j m, m ∈ s.received i j → m ∈ s'.received i j)
    (hvote : ∀ j w, (s.processVariables j).sentVote = some w → (s'.processVariables j).sentVote = some w)
    (hF : s.F ⊆ s'.F) : ExclusionWitness P s b → ExclusionWitness P s' b

theorem voteQuorum_of_received_binds {s : RoundState P.n} (hI : Invariant P s)
    {i : Fin P.n} {v : Bool} (h : P.f + 1 ≤ s.receivedCount i (.bind (some v))) :
    ∃ k, k ∉ s.F ∧ P.n - P.f ≤ s.receivedCount k (.vote (some v))

theorem received_binds_of_echo5_quorum {s : RoundState P.n} (hI : Invariant P s)
    {i : Fin P.n} {v : Bool} (h : P.n - P.f ≤ s.receivedCount i (.echo5 (some v))) :
    ∃ k, k ∉ s.F ∧ P.n - P.f ≤ s.receivedCount k (.bind (some v))

theorem exclusionWitness_of_voteQuorum {s : RoundState P.n} (hI : Invariant P s)
    {i : Fin P.n} {v : Bool} (h : P.n - P.f ≤ s.receivedCount i (.vote (some v))) :
    ExclusionWitness P s (!v)

theorem not_exclusionWitness_of_voteQuorum {s : RoundState P.n} (hI : Invariant P s)
    {i : Fin P.n} {v : Bool} (h : P.n - P.f ≤ s.receivedCount i (.vote (some v))) :
    ¬ ExclusionWitness P s v

theorem exclusionWitness_of_echo5Bot_quorum {s : RoundState P.n} (hI : Invariant P s)
    {i : Fin P.n} (h : P.n - P.f ≤ s.receivedCount i (.echo5 none)) :
    ∃ b, ExclusionWitness P s b

theorem grade_ne_false_of_echo5_quorum {s : RoundState P.n} {t : SpecState P.n}
    (hR : SpecificationRelation P s t) {id : Fin P.n} {v : Bool}
    (hcnt : P.n - P.f ≤ s.receivedCount id (.echo5 (some v))) : t.grade ≠ some false

theorem grade_ne_true_of_echo5Bot_quorum {s : RoundState P.n} {t : SpecState P.n}
    (hR : SpecificationRelation P s t) {id : Fin P.n}
    (hcnt : P.n - P.f ≤ s.receivedCount id (.echo5 none)) : t.grade ≠ some true
```

The counting core shared by `not_exclusionWitness_of_voteQuorum` (Case B refutation)
and worth stating once:

```lean
/-- Two `n − f`-sized subsets of `Fin n` meeting only inside `F` contradict
`|F| ≤ f < n − 2f`. -/
theorem no_disjoint_quorums {P : Parameters} {Q D F : Finset (Fin P.n)}
    (hQ : P.n - P.f ≤ Q.card) (hD : P.n - P.f ≤ D.card)
    (hQD : Q ∩ D ⊆ F) (hF : F.card ≤ P.f) : False
```

(`|Q| + |D| = |Q ∪ D| + |Q ∩ D| ≤ n + f`, against `2(n − f) > n + f` from
`P.hResilience` — the same arithmetic as `exists_correct_received_of_two_quorums`, exposed as a set
statement because `VoteQuorumAgainst` is a set of *processes*, not a set of received messages).

## Why this shape: the compression attack dies at `n = 4, f = 1`

A one-level-shallower reading of the grade-1 witness — `f + 1` received `VOTE v`
messages for `f + 1` received `BIND v` messages, with the `ECHO5` level elided
and the returns reading `BIND` quorums — admits the following binding
violation, which fixes both D18 and the design of the witness. Prefix: `p1`, `p2`,
`p3` are called and echo `0`, `1`, `0` respectively; with both bits `Valid`
everywhere, all three vote ⊥, bind ⊥ (and echo5 ⊥), and `p1` grade-0 returns off the
three received ⊥ messages while `p4` is held unscheduled before its `ECHO`. Extension
A: `p4` echoes `0` and votes `0` off the `ECHO 0` senders `{p1, p3, p4}`;
`p2` is corrupted and injects `VOTE 0` and `BIND 0`; `p3` collects `f + 1 = 2`
received `VOTE 0` messages from `{p4, p2}` and grade-1 returns `0`. Extension B is the
mirror image (corrupt `p1`, hand out `1`) — one grade-0 return, two extensions,
two different surviving bits: binding fails, and no forward simulation into
any binding-faithful spec exists.

Against D18's witness level the attack dies: in extension A, `p3`'s
`retGrade1 0` needs `f + 1 = 2` received `BIND 0` messages, hence a correct `BIND 0` sender
(`2 > |F| = 1`), hence an `n − f = 3`-strong quorum of received `VOTE 0` messages at that
sender. But the prefix fixed the write-once votes of `p1`, `p2`, `p3` at ⊥,
and `p2` is the corrupted process position, so the `VOTE 0` senders available in any
extension are at most `{p4} ∪ F = {p4, p2}` — `2 < 3`, no quorum, no correct
`BIND 0`, no `retGrade1 0` (and a fortiori no `retGrade2 0`: a correct `ECHO5 0` needs
three `BIND 0` senders). Symmetrically for bit `1` in extension B. In
witness terms: at `p1`'s grade-0 return the correct `BIND ⊥` senders' vote
quorums identify `{p1, p2, p3}` as committed-⊥-or-`F`, which is `VoteQuorumAgainst` at
`n − f = 3` for **both** bits — exactly the `∃ b, ExclusionWitness` the `retGrade0` run
consumes, and exactly why no later pattern of received messages can contradict the exclusion.

## Where the shapes surface downstream

The exclusion set and the exclusion witness are read directly by the files above this one. The
`HybridRefinesSpecification/Relation.lean` chain and `HybridRefinesSpecification/Simulation.lean`
phrase the round skeleton over `excluded`: `IsLastBound g r` is `(g r).excluded ≠ ∅ ∧ (g (r +
1)).excluded = ∅`, `RoundSettled g r` is `(g r).excluded ≠ ∅ ∨ (g r).grade = some false`, and
`grade2Lock_commit`, `grade2_needs_bind`, `bind_support` and the grade-2 lock witnesses are keyed
on the guard pair `(!b) ∈ excluded ∧ b ∉ excluded` — the D19 rendering of `bind = some b`, with
`bind ≠ none` rendered as `excluded ≠ ∅`. `GBCA.ByABDY.specificationRelation_corrupt` carries the
`exclusion_witness` clause through `ExclusionWitness.mono`, whose three hypotheses it
discharges by `corrupt_received`, `corrupt_processVariables` and `corrupt_F_subset`.
`ABDY/System.lean`'s rendering carries the same levels inside one process: the round variables
`GBCA.ByABDY.RoundVariables` keep the write-once `sentEcho5` field in their `processVariables` field
and carry their own `echo5Count` over their received sets, the synchronised transitions
`gbcaSendEcho5Bit`/`gbcaSendEcho5Bot` are the echo5 multicasts read off those variables, and the
three `retG` transitions (and their `byzantineRetG` counterparts) read the echo5 level off them. No
translation to the protocol's state is needed: the round-`r` `RoundState` *is* the round instance's
own state — the round variables with their received sets beside the round's network state, which
holds the
per-sender sent sets and the corrupted set — and `RoundState.echo5Count` reads the
receiving program's received sets directly. So `refinesSpecification` runs in two halves: the
characterisation `composition_projects` (`ABA/GBCA/ABDY/Algorithm.lean`) matches every transition of
the round's composition with the algorithm's at that same state, one step for one step, and the
matching `specificationRelation_transition` gives the weak run of the specification, read back at the round
instance's interface — which is what licenses replacing a round's instance by the graded agreement
specification.

## Risks and open points

1. **`Bool` negation syntax.** Two elaboration traps. (a) `bindUnset b`'s
   support guard mentions `some (!b)`; instantiating `b := !v` produces
   `some (!(!v))`, which is not
   definitionally `some v` — the run lemmas carry one
   `simpa only [Bool.not_not]` at the `bindUnset` application. (b) `!` binds
   looser than `∈`/`∉`, so `!v ∈ s.excluded` silently elaborates as the coerced
   `!(decide (v ∈ s.excluded))`; every membership guard on the negated bit must be
   written `(!v) ∈ s.excluded` / `(!v) ∉ t.excluded`.
2. **`retGrade1`'s `honce` guard.** The implementation's `retGrade1` keeps the
   algorithm's "at least one received `ECHO5 v` message" guard. The simulation never
   reads it (the `f + 1` received `BIND v` messages carry the whole witness), so it rides
   along as pure conformance; it must not be dropped from the transition — the transition
   is the algorithm's line.
3. **Canonical grade-0 exclude via `Classical.choose`.** The `retGrade0` transition consumes `∃ b,
   ExclusionWitness P s b` nonconstructively. If a later development (e.g. a quantitative or
   decidability development) needs the choice computable, replace it with the explicit case split
   (`if ReceivedEchoQuorum … true then false else …`); nothing in the simulation depends on which
   witnessed bit is chosen.
4. **`excluded.card ≤ 1` carries no conjunct of its own.** It holds at every
   state of every execution of the specification instance
   (`GBCASafety.excluded_card_le_one`), by the `hd0 : excluded = ∅` guard on the
   single writer, and it is a consequence of `bound_excluded`, `excludedOf`
   taking only `∅` and singletons. A separate conjunct would create restoration
   obligations on every transition for no benefit, and each run gets its `hd0` from the
   branch analysis of its own transition (`excluded_empty_of_both` at the value
   returns, the `bound` split at `retGrade0`). Recorded so nobody "strengthens" the
   relation into extra work.
5. **`VoteQuorumAgainst` reads process-local fields.** Unlike `ReceivedEchoQuorum` it counts
   `sentVote` fields, not received messages — monotone in `F` (a corrupted field stays in the quorum
   via the `j ∈ F` disjunct) and in `sentVote` (write-once), which is all the simulation needs. Any
   per-process decomposition must therefore be read through the same accessors as the other
   `process`-field predicates — `RoundState.processVariables` for the field and
   `RoundState.F` for the corrupted set, the latter reading the set held by the round's own
   network state, which is the state's second component.
6. **Vacuous-fill hazard in `exclusionWitness_of_echo5Bot_quorum`.** The Case B branch
   needs the global classical split "some correct bit-voter exists"; its
   **no**-branch uses `bindBot_confirmed` on a *specific* correct `BIND` sender
   derived from `echo5Bot_confirmed`'s any-`BIND` count. That derivation wants
   `exists_sender_notMem` on an any-payload count, i.e. the payload-returning
   variant `RoundState.exists_bind_sender_notMem`:
   `∃ k w, k ∉ F ∧ Message.bind w ∈ s.received p k`, same proof as the exact-message
   version.
