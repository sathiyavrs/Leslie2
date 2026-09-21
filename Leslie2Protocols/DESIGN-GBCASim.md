# Design — the per-instance GBCA refinement `GBCA.ByABDY.implInst ⊑ GBCA.specInst` (`implRefines`)

Companion design document to the Lean proof in `ABA/GBCA/ABDY/RefinesSpecification.lean`
(relation, invariant, run lemmas, per-row simulation), against the implementation shape in
`ABA/GBCA/ABDY/Implementation.lean` (deviation D18: all five message levels of ABDY22's
Algorithm 6) and the specification shape in `ABA/GBCA/Specification.lean` (deviation D19:
the exclusion set `excluded : Finset Bool` as the state shape, with the bound value
announced on the return labels, D29). The refinement paragraphs of
`blueprint/src/content.tex` — the exclusion certificate, the `VOTE` wall, and the two-step
exclusion-then-return run — are a condensation of this document.

## Systems

```
implInst P r : System (ImplState P.n) (Label P.n)     -- ABDY22 Algorithm 6, D1/D5/D8/D18
specInst P r : System (SpecState P.n) (Label P.n)     -- graded-binding spec, D1/D14/D15/D19
target       : ForwardSimulation (implInst P r) (specInst P r) (instRel P r)
```

Both systems are Dirac-transition LTSs. The instance refinement reaches the ℕ-indexed
families through the round instance (`ABA/Composition/GBCAInstanceByABDY.lean`), whose
family lifting takes its broadcast ingredient from `GBCASim.instRel_corrupt`.

### The implementation (D18): the five message levels

The implementation transcribes ABDY22's Algorithm 6. The message type is

```lean
inductive Msg : Type
  | input (b : Bool)         -- ⟨echo,  b⟩ of Algorithm 6
  | echo  (b : Bool)         -- ⟨echo2, b⟩
  | vote  (v : Option Bool)  -- ⟨echo3, v⟩,  v ∈ {0, 1, ⊥}
  | bind  (v : Option Bool)  -- ⟨echo4, v⟩
  | echo5  (v : Option Bool)  -- ⟨echo5, v⟩
```

and `ProcState` carries one write-once field per level above `INPUT`:
`sentEcho : Option Bool`, `sentVote sentBind sentEcho5 : Option (Option Bool)`,
next to `input`, `sentInput : Bool → Bool` and `returned`. `ImplState` is the
pair of the per-process stage records and the round's network state, the
latter carrying the D5 set-based network (`sent`, `recv`), the corrupted set
`F`, and the write-once ghost field `bound : Option Bool`. Derived counts: `recvCount i m` (distinct senders of the
exact message `m` delivered to `i`), `echoCount`/`voteCount`/`bindCount`/
`echo5Count i` (distinct senders of *any* payload at that level), and
`bothValid P s i` (an `n − f` `INPUT b` receipt quorum at `i` for **each**
bit — Algorithm 6's `|approvedVals| > 1`).

The rules, all τ except the labelled API rows. Three conditions run across the
table. The D8 participation guard (`input ≠ none`) is on every protocol send,
including the echo5 level, and on all three returns. The levels are taken in the
wait-until order of Algorithm 6 from the `BIND` level down: each of those levels
requires the sender's own send at the level below (`hlv`), the returns requiring
the sender's own `ECHO5`. The vote level requires no own send, the `ECHO` it
reads being multicast by an `upon` handler and not on the main thread. And the
block boundaries are denials: within a return block the `⊥` rule denies its
block's case (a) at either bit, and the returns read as Algorithm 6's
`if (a) … elif (b) … else …`, each carrying the denials of the cases above it.

* `call` / `callLoop` — record the input, multicast `INPUT b` / input-enabled
  self-loop;
* `deliver` — adversarial move of a sent message into a `recv` cell;
* `relay` — `f + 1` `INPUT b` receipts, re-multicast `INPUT b` (amplification);
* `echo` — `n − f` `INPUT b` receipts, multicast `ECHO b` (write-once);
* `voteBit` — `n − f` `ECHO b` receipts, multicast `VOTE b` (write-once);
* `voteBot` — `n − f` any-`ECHO` receipts, `bothValid`, and no `n − f` `ECHO b`
  quorum at either bit, multicast `VOTE ⊥`;
* `bindBit` — `n − f` `VOTE b` receipts and own `VOTE` out, multicast `BIND b`
  (write-once);
* `bindBot` — `n − f` any-`VOTE` receipts, own `VOTE` out, `bothValid`, and no
  `n − f` `VOTE b` quorum at either bit, multicast `BIND ⊥`;
* `echo5Bit` — `n − f` `BIND b` receipts and own `BIND` out, multicast `ECHO5 b`
  (write-once);
* `echo5Bot` — `n − f` any-`BIND` receipts, own `BIND` out, `bothValid`, and no
  `n − f` `BIND b` quorum at either bit, multicast `ECHO5 ⊥`;
* `byzantine` — a corrupted sender multicasts anything;
* `retA id v` — an `n − f` `ECHO5 v` receipt quorum, the process called and its
  own `ECHO5` out (grade 2 — case (a), which heads the chain and denies nothing);
* `retB id v` — `n − f` any-`ECHO5` receipts, at least one `ECHO5 v` receipt,
  **`f + 1` `BIND v` receipts**, and `bothValid`, the process called, its own
  `ECHO5` out and case (a) denied at either bit (`hnotA`) (grade 1 — Algorithm 6's
  line-25 condition: the `t + 1` `echo4` check is what puts an honest `BIND v`
  behind every grade-1 output);
* `retC id` — an `n − f` `ECHO5 ⊥` receipt quorum and `bothValid`, the process
  called, its own `ECHO5` out, case (a) denied at either bit (`hnotA`), and
  case (b) denied in reduced form (`hnotB`: `∀ v, (∃ k, echo5 (some v) ∈ recv id k)
  → recvCount (.bind (some v)) < f + 1`) — the reduction is sound because case
  (b)'s other two conjuncts, the `n − f` any-`ECHO5` quorum and `bothValid`, are
  this row's own `hcnt` and `hval`, an `n − f` `ECHO5 ⊥` quorum being in
  particular an `n − f` any-`ECHO5` quorum (grade 0);
* `fail` — D1 determinised corruption.

The three return rows each announce a bit and write it back, and no other row
touches the field. `GBCA.ByABDY.boundOf sent F out` is the bit a return of outcome
`out` announces where the round has none on record: `v` at a value-bearing
outcome, and at `C` the payload of an honest `⟨VOTE, b⟩` sender, `true` where
there is none. An honest `⟨VOTE, b⟩` sender holds an `n − f` `⟨ECHO, b⟩`
receipt quorum and at most one bit carries such a quorum, so on a reachable
state at most one branch applies. A return announces
`bound.getD (boundOf sent F out)`, so the round announces one bit on all of its
returns. The bit is a ghost output (D29): it enters no guard of Algorithm 6 and
no field a program holds.

The load-bearing depth of the return evidence: **every grade-≥1 output names a
bit with an honest `BIND` behind it** — `retA` via `n − f` `ECHO5 v` →
honest `ECHO5` sender → `n − f` `BIND v` receipts → honest binder; `retB` via
`f + 1 > |F|` `BIND v` receipts directly — and an honest `BIND v` sits on an
`n − f` `VOTE v` receipt quorum. The `VOTE` level is write-once, so that
quorum is the object the binding argument counts (paper Lemmas 4.8/4.9 through
E.9).

### The specification (D19): the exclusion set

`SpecState` is `call : Fin n → Option Bool`, `ret : Fin n → Bool`,
`excluded : Finset Bool`, `grade : Option Bool`, `F : Finset (Fin n)`; initially
`excluded = ∅`. Binding is *negative* information: `excluded` is the set of bits the
instance can no longer hand out. The rules:

* `call` / `callLoop` — as in every instance spec (D15 file conventions);
* `bindUnset b` (τ) — guards `s.quorum P`,
  `f + 1 ≤ #{id | s.call id = some (!b) ∨ id ∈ s.F}` (the D15 SuppOK count,
  at the *surviving* bit `!b`), and `hd0 : s.excluded = ∅`; effect
  `excluded := insert b s.excluded`;
* `retA id v bnd` — guards `v ∉ s.excluded`, `(!v) ∈ s.excluded`,
  `(!bnd) ∈ s.excluded`, `s.grade = none ∨ s.grade = some true`,
  `s.ret id = false`; effect `grade := some true`, mark returned;
* `retB id v bnd` — guards `v ∉ s.excluded`, `(!v) ∈ s.excluded`,
  `(!bnd) ∈ s.excluded`, the D15 dissent count
  `f + 1 ≤ #{id' | s.call id' = some (!v) ∨ id' ∈ s.F}`, `s.ret id = false`;
  effect: mark returned;
* `retC id bnd` — guards `(!bnd) ∈ s.excluded`, the two D15 counts (one per
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
completable: after an `A`-return a second exclusion would leave no live bit for the
value-bearing returns while the `A` grade guard blocks `retC`, stranding the processes
yet to return.

`excluded` is monotone (only `bindUnset` writes it, by `insert`), so the graded
binding property is structural: an excluded bit is never handed out (`v ∉ excluded`
guards both value-bearing returns), every `A`/`B`-return pins `(!v) ∈ excluded`
whence any two value-bearing returns agree on the surviving bit, and a
`C`-return forces `excluded ≠ ∅` permanently — from that moment at most one bit is
ever alive, which is the paper's Binding. Provenance (D14/D15) is carried by
`bindUnset`'s SuppOK count for the surviving bit: a bit `v` handed out at
grade ≥ 1 requires `(!v) ∈ excluded`, whose `bindUnset (!v)` certified `f + 1`
F-blind callers of `v`; the budget pigeonhole (`|F| ≤ f` forever) recovers a
never-corrupted genuine caller of `v`.

## The relation

```lean
structure InstRel (P : Params) (s : ImplState P.n) (t : SpecState P.n) : Prop where
  inv       : Inv P s
  call_eq   : ∀ id, t.call id = (s.proc id).input
  ret_eq    : ∀ id, t.ret id = (s.proc id).returned
  F_eq      : t.F = s.F
  excluded_cert : ∀ b, b ∈ t.excluded → ExcludedCert P s b
  bound_excluded : t.excluded = excludedOf s.bound
  gradeA_ev : t.grade = some true  → ∃ v i, P.n - P.f ≤ s.recvCount i (.echo5 (some v))
  gradeC_ev : t.grade = some false → ∃ i,   P.n - P.f ≤ s.recvCount i (.echo5 none)
```

`call_eq`/`ret_eq`/`F_eq` are the exact abstraction rows, identical in shape
to every other instance relation of the development. `gradeA_ev`/`gradeC_ev`
are the A/C-exclusivity certificates, read at the `ECHO5` level (the level the
returns read): two opposing `n − f` `ECHO5` quorums intersect in an honest
process with two different `ECHO5` payloads, contradicting the write-once
`echo5_once` — which is what discharges the spec's grade guards.

`excluded_cert` is the load-bearing novelty: the spec's `excluded` is bookkeeping the
protocol never stores, so the relation carries a receipt-pattern *exclude
certificate* for every excluded bit. Note the direction — the clause bounds
`excluded` from above (`excluded ⊆ {b | ExcludedCert P s b}`) and never from below.

`bound_excluded` is the one clause that pins `excluded` from below, through the
implementation's ghost field: `excludedOf` is `∅` at `bound = none` and
`{!β}` at `bound = some β`, and the equation holds because the exclusion fires
inside the round's first return, which is also the row that writes the bit. Two
things follow. It discharges the guard `(!bnd) ∈ excluded` of a return that
announces a bit already on record, and with `excluded_cert` it gives
`InstRel.bound_cert`: the bit on record carries an exclude certificate for its
complement. Each return row therefore splits on `bound`: with a bit on record
the guard is discharged and the row answers with `ret` alone, and with the field
unwritten `excluded` is empty and the row answers with the two-step run.

## The exclude certificates

```lean
/-- Case A: the opposite bit owns the (unique) `n − f` `ECHO` receipt
quorum. -/
def EchoQuorum (P : Params) (s : ImplState P.n) (v : Bool) : Prop :=
  ∃ i, P.n - P.f ≤ s.recvCount i (.echo v)

/-- Case B: an `n − f` wall of processes each of which is corrupted or has
committed its write-once `VOTE` field to a payload other than `some b`. -/
def VoteWall (P : Params) (s : ImplState P.n) (b : Bool) : Prop :=
  P.n - P.f ≤ (Finset.univ.filter
    (fun j => j ∈ s.F ∨ ∃ w, (s.proc j).sentVote = some w ∧ w ≠ some b)).card

/-- The exclude certificate licensing `b ∈ excluded` on the specification side. -/
def ExcludedCert (P : Params) (s : ImplState P.n) (b : Bool) : Prop :=
  EchoQuorum P s (!b) ∨ VoteWall P s b
```

Both disjuncts exclude `b` by making an `n − f` `VOTE b` receipt quorum — the
sole source to any grade-≥1 evidence for `b` — impossible forever:

* **Case A** (`EchoQuorum P s (!b)`). Any `VOTE b` quorum contains an honest
  `VOTE b` sender (`n − f > f ≥ |F|`), whose `vote_conf` receipt quorum is an
  `n − f` `ECHO b` quorum; two same-level `n − f` quorums for different bits
  share an honest sender (`exists_honest_recv₂`, `(n−f)+(n−f)−n > f`) that
  multicast two `ECHO` payloads, contradicting the write-once `echo_once`.
  This is `echoQuorum_unique`.
* **Case B** (`VoteWall P s b`). Any later `n − f` `VOTE b` quorum `Q` has all
  its non-`F` members committed to `sentVote = some (some b)` (`recv_sub` +
  `vote_once`), so `Q` meets the wall `D` only inside `F`:
  `|Q| + |D| ≤ n + |Q ∩ D| ≤ n + f`, i.e. `2(n − f) ≤ n + f`, i.e. `n ≤ 3f` —
  against `P.hf`. The wall is the state-predicate form of the paper's
  Lemma 4.9 pinning count ("`n − f` receipts pin `≥ n − f − |F|` honest
  committed voters, leaving `≤ f < n − 2f` free honest votes").

The three certificate obligations:

**(i) Monotonicity.** Receipts only grow (`deliver`), `sentVote` is
write-once and never unset (guard `sentVote = none` on `voteBit`/`voteBot`,
no rule clears it), and `F` only grows (`fail`); every other rule touches
neither `recv`, `sentVote` nor `F`. Packaged as

```lean
theorem ExcludedCert.mono {s s' : ImplState P.n} {b : Bool}
    (hrecv : ∀ i j m, m ∈ s.recv i j → m ∈ s'.recv i j)
    (hvote : ∀ j w, (s.proc j).sentVote = some w → (s'.proc j).sentVote = some w)
    (hF : s.F ⊆ s'.F) : ExcludedCert P s b → ExcludedCert P s' b
```

applied per row exactly like `ImplSupp.mono`. This is
what keeps `excluded_cert` a stutter-stable field: `excluded` never shrinks and the
certificates never expire.

**(ii) Availability at the exclusion moments.** The simulation fires `bindUnset`
only inside return runs, and each return's own evidence yields the needed
certificate:

```lean
/-- Any `n − f` `VOTE v` receipt quorum excludes the opposite bit … -/
theorem excludedCert_of_voteQuorum (hI : Inv P s) {i v}
    (h : P.n - P.f ≤ s.recvCount i (.vote (some v))) : ExcludedCert P s (!v)

/-- … and certifies that `v` itself is alive. -/
theorem not_excludedCert_of_voteQuorum (hI : Inv P s) {i v}
    (h : P.n - P.f ≤ s.recvCount i (.vote (some v))) : ¬ ExcludedCert P s v
```

`excludedCert_of_voteQuorum` lands in `VoteWall (!v)` — the quorum's members are
each in `F` or committed to `some v ≠ some (!v)`, so the quorum itself is the
wall. `not_excludedCert_of_voteQuorum` is the two Case A/B refutations above.
Both value-bearing returns route into a `VOTE` quorum by the derivation chain

```lean
theorem voteQuorum_of_bind_receipts (hI : Inv P s) {i v}
    (h : P.f + 1 ≤ s.recvCount i (.bind (some v))) :
    ∃ k, k ∉ s.F ∧ P.n - P.f ≤ s.recvCount k (.vote (some v))

theorem bind_receipts_of_echo5_quorum (hI : Inv P s) {i v}
    (h : P.n - P.f ≤ s.recvCount i (.echo5 (some v))) :
    ∃ k, k ∉ s.F ∧ P.n - P.f ≤ s.recvCount k (.bind (some v))
```

(`retA`: echo5 quorum → honest `ECHO5` sender → `echo5_conf`; then `n − f ≥ f + 1` and
the first chain: bind receipts → honest binder (`f + 1 > |F|`) → `bind_conf`.
`retB`: its `f + 1` `BIND v` receipts enter the first chain directly.) The
`C`-return has no distinguished bit; its evidence yields a certificate for
*some* bit:

```lean
theorem excludedCert_of_echo5Bot_quorum (hI : Inv P s) {i}
    (h : P.n - P.f ≤ s.recvCount i (.echo5 none)) : ∃ b, ExcludedCert P s b
```

Proof shape (this is the sketch's Case A/Case B dichotomy, formalised): the
quorum contains an honest `ECHO5 ⊥` sender `p` (`n − f > f`); `echo5Bot_conf`
gives `n − f ≤ s.bindCount p`, so `p` holds an honest any-payload `BIND`
sender `k`. Classical case split on `∃ m b', m ∉ s.F ∧ Msg.vote (some b') ∈
s.sent m` (an honest bit-voter exists somewhere):

* **yes** — `vote_conf` at `m` is an `n − f` `ECHO b'` quorum, so
  `EchoQuorum P s b'` and `ExcludedCert P s (!b')` by Case A;
* **no** — then `k` cannot have sent `BIND (some v')` (its `bind_conf`
  `VOTE v'` quorum would contain an honest bit-voter), so `k` sent `BIND ⊥`
  and `bindBot_conf` gives `n − f ≤ s.voteCount k`: every non-`F` sender in
  that quorum committed a vote (`vote_once`) that is not a bit (no honest
  bit-voter exists), i.e. `sentVote = some none ≠ some (some b)` for **both**
  bits — `VoteWall` holds for both bits, `ExcludedCert` for either.

**(iii) The `bindUnset` guards are discharged.** `bindUnset b` needs the
quorum guard and `f + 1` F-blind caller support for `!b`. At a value-bearing
return of `v` (excluding `b = !v`, support bit `!(!v) = v`), both come from one
`ECHO` certificate:

```lean
theorem bindUnset_guards (hR : InstRel P s t) {v} (hq : EchoQuorum P s v) :
    t.quorum P ∧ P.f + 1 ≤ (Finset.univ.filter
      (fun id => t.call id = some v ∨ id ∈ t.F)).card
```

— refine the `ECHO v` quorum to an `n − f` `INPUT v` receipt quorum
(`inputQuorum_of_echoQuorum`), whose honest senders hold an input
(`input_called`, D8): that is the quorum guard (`quorum_of_msg_quorum`), and
its count feeds `Inv.supp_of_input_receipts` → `InstRel.spec_supp` for the
SuppOK count. The `EchoQuorum v` input is supplied by
`echoQuorum_of_vote_receipts` off the derived `VOTE v` quorum
(`n − f ≥ f + 1`). At the `C`-return (excluding an arbitrary certified `b*`,
support bit `!b*`), both guards come instead from the returner's own
`bothValid`: the per-bit `n − f` `INPUT` receipt quorum gives the quorum guard
through `quorum_of_msg_quorum`/`input_called`, and `suppI_of_valid` gives the
`f + 1` count for **either** bit — so the guard is available no matter which
bit the certificate names.

### Case A / Case B as named invariants

The soundness fact "the surviving bit at any C-return is determined by prefix
receipts" is not a lemma of the simulation file; it is the conjunction of the
certificate properties above, and it is what makes a *plain forward*
simulation sufficient (no prophecy): at every moment the simulation must
commit an exclusion, the impl state already contains a monotone certificate naming
the excluded bit, and no extension ever produces return evidence for a certified
bit (`not_excludedCert_of_voteQuorum` against `ExcludedCert.mono`). The two named
carriers:

* **Case A** — `excludedCert_of_voteQuorum` (an honest `VOTE v`, equivalently an
  `ECHO v` quorum, excludes `!v` forever): quorum intersection on the write-once
  `ECHO` level.
* **Case B** — the **no**-branch of `excludedCert_of_echo5Bot_quorum` (a
  `C`-return over an all-⊥ honest vote prefix excludes both bits): the
  `VoteWall` counting on the write-once `VOTE` level.

## Exclusion scheduling and run shapes

The specification excludes by an internal τ-transition, so an implementation
return that needs a not-yet-excluded bit excluded is answered by a two-step weak
run through `weakLStep_tauThen`. **Every** return row does the same decidable
case split on the specification's `excluded`, and the run is enabled whenever
the exclusion is missing, whatever returns came before. Every run carries
`hd0 : t.excluded = ∅`, the `bindUnset` guard, and each run's label carries the
bit the row announces:

```lean
/-- `bindUnset (!v) ; retA v` from an all-alive state (`excluded = ∅`). -/
theorem excludeThenRetA_run {r t id v}
    (hq : t.quorum P)
    (hw : P.f + 1 ≤ (Finset.univ.filter
      (fun k => t.call k = some v ∨ k ∈ t.F)).card)
    (hlive : v ∉ t.excluded) (hd0 : t.excluded = ∅)
    (hg : t.grade = none ∨ t.grade = some true) (hr : t.ret id = false) :
    (specInst P r).weakLStep t (.retG r id (.A v) v)
      { t with excluded := insert (!v) t.excluded, grade := some true,
               ret := Function.update t.ret id true }
```

(the `bindUnset (!v)` support guard reads `some (!(!v))`; `Bool.not_not`
rewrites it to `hw`'s `some v`, and `retA`'s `v ∉ insert (!v) t.excluded` follows
from `hlive` and `v ≠ !v`). `excludeThenRetB_run` is the same with the dissent
count `f + 1 ≤ #{k | t.call k = some (!v) ∨ k ∈ t.F}` in place of the grade
guard, landing in `{ t with excluded := insert (!v) t.excluded, ret := … }`. The
`C`-side run excludes one arbitrary bit:

```lean
/-- `bindUnset b ; retC` from an all-alive state (`excluded = ∅`). -/
theorem excludeThenRetC_run {r t id b}
    (hq : t.quorum P)
    (hw : P.f + 1 ≤ (Finset.univ.filter
      (fun k => t.call k = some (!b) ∨ k ∈ t.F)).card)
    (hd0 : t.excluded = ∅)
    (hwT : P.f + 1 ≤ #{k | t.call k = some true  ∨ k ∈ t.F})
    (hwF : P.f + 1 ≤ #{k | t.call k = some false ∨ k ∈ t.F})
    (hg : t.grade = none ∨ t.grade = some false) (hr : t.ret id = false) :
    (specInst P r).weakLStep t (.retG r id .C)
      { t with excluded := insert b t.excluded, grade := some false,
               ret := Function.update t.ret id true }
```

(`retC`'s `1 ≤ excluded.card` holds because `insert` is nonempty).

### Where `hd0` comes from at the call sites

The two value-return rows derive it from the branch they are in rather than
carrying it in the relation. At `retA`/`retB` the row already holds
`hlive : v ∉ t.excluded` (the certificate refutation) and enters the run branch
under `hexcluded : (!v) ∉ t.excluded`, and a `Finset Bool` missing both `v` and `!v` is
empty:

```lean
theorem excluded_empty_of_both {d : Finset Bool} {v : Bool}
    (h1 : v ∉ d) (h2 : (!v) ∉ d) : d = ∅
```

so the call sites read `excludeThenRetA_run hq hw hlive (excluded_empty_of_both
hlive hexcluded) hgr hret`, and likewise for `retB`. The `retC` row splits on
`Finset.eq_empty_or_nonempty t.excluded` outright, so its empty branch *is* `hd0`
and its nonempty branch answers with a single `Step.retC`.

### Which bit the `C`-return excludes

`retC` fires the run only from `t.excluded = ∅` (otherwise `1 ≤ t.excluded.card`
already holds and a single `Step.retC` answers). The excluded bit is
`b* := Classical.choose (excludedCert_of_echo5Bot_quorum …)` — the certified bit
its evidence names: the opposite of the unique honestly-voted bit when one
exists (Case A branch), and canonically `false` in the neither-bit-decidable
case (Case B branch, where both bits are certified and the choice is
arbitrary). Soundness never depends on the choice: both spec-side guards of
`bindUnset b*` hold for either bit (they read `bothValid`), and a certified
bit can never carry later return evidence, so no future row is obstructed by
the pick — if some later `retB v` were to need `v` alive, its evidence proves
`¬ ExcludedCert P s' v`, and `ExcludedCert.mono` shows `v` was never certified, hence
never picked.

### The matching table

| impl rule | label | spec answer | relation obligations beyond `Inv.step` |
|---|---|---|---|
| `call` | `callG r id b` | `Step.call` (guard via `call_eq`) | `call_eq`/`ret_eq` re-pointwise; `excluded_cert` by `ExcludedCert.mono` (input write only); grade evs untouched |
| `callLoop` | `callG r id b` | `Step.callLoop` | all fields unchanged |
| `deliver` | τ | stutter (`weakLSilent_refl`) | `excluded_cert` via `ExcludedCert.mono` (recv grows); grade evs via `recvCount_le_recvMsg` |
| `relay` | τ | stutter | frame: sender's `sentInput` only |
| `echo` | τ | stutter | frame: sender's `sentEcho` only |
| `voteBit` / `voteBot` | τ | stutter | `sentVote` goes `none → some _`: `ExcludedCert.mono`'s persistence hypothesis holds vacuously-forward (wall members already committed) |
| `bindBit` / `bindBot` | τ | stutter | frame: sender's `sentBind` only |
| `echo5Bit` / `echo5Bot` | τ | stutter | frame: sender's `sentEcho5` only (nothing in the relation reads `sentEcho5` outside `Inv`) |
| `byzantine` | τ | stutter | frame: `sent` set of a corrupted sender only |
| `retA id v` | `retG r id (A v)` | `(!v) ∈ excluded`: single `Step.retA`; else: `excludeThenRetA_run` | see below |
| `retB id v` | `retG r id (B v)` | `(!v) ∈ excluded`: single `Step.retB`; else: `excludeThenRetB_run` | see below |
| `retC id` | `retG r id C` | `excluded ≠ ∅`: single `Step.retC`; else: `excludeThenRetC_run` on `b*` | see below |
| `fail id` | `fail id` | `Step.fail` (lockstep `corrupt`) | `corrupt_F_eq`; `excluded` untouched by spec `corrupt`; `excluded_cert` via `ExcludedCert.mono` (`corrupt_recv`/`corrupt_proc`/`corrupt_F_subset`); grade evs via `corrupt_recvCount` |

The three return rows in detail. Common first move: derive the honest
`VOTE`-level quorum —

* `retA`: `hcnt : n − f ≤ recvCount id (.echo5 (some v))` →
  `bind_receipts_of_echo5_quorum` → `voteQuorum_of_bind_receipts` (via
  `n − f ≥ f + 1`) → `hvq : n − f ≤ recvCount k (.vote (some v))`;
* `retB`: `hbind : f + 1 ≤ recvCount id (.bind (some v))` →
  `voteQuorum_of_bind_receipts` → `hvq`;

then

1. `hlive : v ∉ t.excluded` — from `excluded_cert` contraposed by
   `not_excludedCert_of_voteQuorum hvq`;
2. grade guard (`retA` only) — `grade_ne_false_of_echo5_quorum`: the `ECHO5 v`
   quorum against `gradeC_ev`'s `ECHO5 ⊥` quorum meets in an honest
   double `ECHO5` sender, contradicting `echo5_once`;
3. dissent count (`retB` only) — `spec_supp (suppI_of_valid hval (!v))`;
4. case `(!v) ∈ t.excluded`: single labelled step. Case `(!v) ∉ t.excluded`: run, with
   `bindUnset_guards` fed by `echoQuorum_of_vote_receipts hvq` and `hd0` by
   `excluded_empty_of_both hlive hexcluded`;
5. restore: `excluded_cert` — old bits by `ExcludedCert.mono` (the step only sets
   `returned`), the new bit `!v` by `excludedCert_of_voteQuorum hvq`;
   `gradeA_ev := ⟨v, id, hcnt⟩` (`retA`), other grade evidence by
   monotonicity or vacuity.

`retC`: `hwT`/`hwF` from `suppI_of_valid hval`, the `C` grade guard from
`grade_ne_true_of_echo5Bot_quorum` (`ECHO5 ⊥` quorum against `gradeA_ev`'s
`ECHO5 v` quorum, honest double `ECHO5` sender, `echo5_once`), the run's `b*` and its
certificate from `excludedCert_of_echo5Bot_quorum`, the `bindUnset` quorum guard
from `quorum_of_msg_quorum` on `bothValid`'s `INPUT` quorum; restore
`gradeC_ev := ⟨id, hcnt⟩` and `excluded_cert` as above with `ExcludedCert b*` for the
new member.

Value agreement needs no dedicated lemmas: agreement between successive returns
is the guard pair `v ∉ excluded ∧ (!v) ∈ excluded` itself, discharged per row by
`not_excludedCert_of_voteQuorum` (for `∉`) and the case analysis (for `∈`).

The announced bit is discharged the same way. A value-bearing return announces
its own value (`InstRel.retBound_eq`): the return's `n − f` `VOTE v` receipt
quorum refutes a certificate for `v`, so a bit already on record is `v` by
`InstRel.bound_cert`, and a bit computed here is `v` by `boundOf`. A `C`-return
announces `boundOf`'s bit, whose complement is certified by
`excludedCert_boundOf_C`: an honest bit-voter's `vote_conf` receipt quorum is
Case A for the opposite bit, and where there is no honest bit-voter the all-⊥
wall (`excludedCert_of_noHonestVote`) certifies both bits at once. In that
all-⊥ run no bit is ever handed out, and the bit the `C`-returns announce is
the surviving one — `boundOf` reads `true` there, and the run excludes `false`
— which is sound because the bit is a ghost output and answers no process.

## Invariant inventory

### Shared machinery

The kit the proof draws on, most of it common to the instance refinements of
the development; the `ECHO5`-level τ-rows (`echo5Bit`/`echo5Bot`) are frame cases
identical in shape to `bindBit`/`bindBot` and need nothing beyond it:

* the weak-transition kit of `Framework/FamilySimulation.lean`:
  `System.weakLStep_of_step` and `weakLStep_tauThen`;
* network plumbing: `recv_sub`, `recvCount_le_recvMsg`, `mem_mcast_sent`,
  `mem_recvMsg_recv`, `exists_sender_notMem`, `exists_honest_recv₂`,
  `corrupt_*` frame lemmas, `corrupt_F_eq`;
* the corruption budget `F_card` and the D15 input machinery: `ImplSupp`,
  `ImplSupp.mono`, `input_orig`, `input_supp`, `input_called`,
  `Inv.supp_of_input_receipts`, `suppI_of_valid`, `InstRel.spec_supp`,
  `quorum_of_msg_quorum`, `inputQuorum_of_echoQuorum`;
* the `ECHO`-level certificate: `EchoQuorum`, `echoQuorum_unique`,
  `echoQuorum_of_vote_receipts`, and `bindUnset_guards` (quorum + SuppOK count
  out of one `EchoQuorum`);
* conformance and write-once clauses `echo_conf`, `echo_once`, `vote_input`,
  `vote_conf`, `bind_once`, `bind_conf` (`bind_once` serves here as a
  conformance fact only — grade exclusivity is read at the `ECHO5` level).

### `Inv` clauses at the `VOTE` and `ECHO5` levels

```lean
/-- Honest `VOTE` multicasts are recorded in the write-once `sentVote`. -/
vote_once : ∀ j w, j ∉ s.F → Msg.vote w ∈ s.sent j → (s.proc j).sentVote = some w
/-- Honest `BIND ⊥` is backed by `n − f` any-`VOTE` receipts. -/
bindBot_conf : ∀ j, j ∉ s.F → Msg.bind none ∈ s.sent j → P.n - P.f ≤ s.voteCount j
/-- Honest `ECHO5` multicasts are recorded in the write-once `sentEcho5`. -/
echo5_once : ∀ j w, j ∉ s.F → Msg.echo5 w ∈ s.sent j → (s.proc j).sentEcho5 = some w
/-- Honest `ECHO5 b` is backed by an `n − f` `BIND b` receipt quorum. -/
echo5_conf : ∀ j b, j ∉ s.F → Msg.echo5 (some b) ∈ s.sent j →
  P.n - P.f ≤ s.recvCount j (.bind (some b))
/-- Honest `ECHO5 ⊥` is backed by `n − f` any-`BIND` receipts. -/
echo5Bot_conf : ∀ j, j ∉ s.F → Msg.echo5 none ∈ s.sent j → P.n - P.f ≤ s.bindCount j
/-- Honest `ECHO5` senders hold an input (D8, one level up). -/
echo5_input : ∀ j w, j ∉ s.F → Msg.echo5 w ∈ s.sent j → (s.proc j).input ≠ none
```

`vote_once` and `bindBot_conf` are forced by the exclusion certificates (`VoteWall`
counting and the Case B branch of `excludedCert_of_echo5Bot_quorum`); the echo5
clauses mirror the per-level pattern one level up, with
`echo5_once`/`echo5_conf`/`echo5Bot_conf` load-bearing (grade exclusivity and the
two derivation chains) and `echo5_input` kept for pattern uniformity only.
Preservation is by the same three schemas as every other clause: the
`_once` clauses by the `sentEcho5 = none`/`sentVote = none` send guards, the
`_conf` clauses by the sending rule's own receipt guard plus count
monotonicity, everything by frame elsewhere. Count monotonicity needs the
any-payload analogues of `recvCount_le_recvMsg`:

```lean
theorem voteCount_le_recvMsg (s : ImplState n) (i j : Fin n) (m : Msg) (i' : Fin n) :
    s.voteCount i' ≤ (s.recvMsg i j m).voteCount i'
-- likewise bindCount_le_recvMsg
```

(same one-line `Finset.card_le_card` proof at both levels).

### Certificate and derivation lemmas

Collected statements (all defined in `GBCA/ABDY/RefinesSpecification.lean` unless noted):

```lean
def VoteWall (P : Params) (s : ImplState P.n) (b : Bool) : Prop := …   -- § exclude certificates
def ExcludedCert (P : Params) (s : ImplState P.n) (b : Bool) : Prop :=
  EchoQuorum P s (!b) ∨ VoteWall P s b

theorem ExcludedCert.mono {s s' : ImplState P.n} {b : Bool}
    (hrecv : ∀ i j m, m ∈ s.recv i j → m ∈ s'.recv i j)
    (hvote : ∀ j w, (s.proc j).sentVote = some w → (s'.proc j).sentVote = some w)
    (hF : s.F ⊆ s'.F) : ExcludedCert P s b → ExcludedCert P s' b

theorem voteQuorum_of_bind_receipts {s : ImplState P.n} (hI : Inv P s)
    {i : Fin P.n} {v : Bool} (h : P.f + 1 ≤ s.recvCount i (.bind (some v))) :
    ∃ k, k ∉ s.F ∧ P.n - P.f ≤ s.recvCount k (.vote (some v))

theorem bind_receipts_of_echo5_quorum {s : ImplState P.n} (hI : Inv P s)
    {i : Fin P.n} {v : Bool} (h : P.n - P.f ≤ s.recvCount i (.echo5 (some v))) :
    ∃ k, k ∉ s.F ∧ P.n - P.f ≤ s.recvCount k (.bind (some v))

theorem excludedCert_of_voteQuorum {s : ImplState P.n} (hI : Inv P s)
    {i : Fin P.n} {v : Bool} (h : P.n - P.f ≤ s.recvCount i (.vote (some v))) :
    ExcludedCert P s (!v)

theorem not_excludedCert_of_voteQuorum {s : ImplState P.n} (hI : Inv P s)
    {i : Fin P.n} {v : Bool} (h : P.n - P.f ≤ s.recvCount i (.vote (some v))) :
    ¬ ExcludedCert P s v

theorem excludedCert_of_echo5Bot_quorum {s : ImplState P.n} (hI : Inv P s)
    {i : Fin P.n} (h : P.n - P.f ≤ s.recvCount i (.echo5 none)) :
    ∃ b, ExcludedCert P s b

theorem grade_ne_false_of_echo5_quorum {s : ImplState P.n} {t : SpecState P.n}
    (hR : InstRel P s t) {id : Fin P.n} {v : Bool}
    (hcnt : P.n - P.f ≤ s.recvCount id (.echo5 (some v))) : t.grade ≠ some false

theorem grade_ne_true_of_echo5Bot_quorum {s : ImplState P.n} {t : SpecState P.n}
    (hR : InstRel P s t) {id : Fin P.n}
    (hcnt : P.n - P.f ≤ s.recvCount id (.echo5 none)) : t.grade ≠ some true
```

The counting core shared by `not_excludedCert_of_voteQuorum` (Case B refutation)
and worth stating once:

```lean
/-- Two `n − f`-sized subsets of `Fin n` meeting only inside `F` contradict
`|F| ≤ f < n − 2f`. -/
theorem no_disjoint_quorums {P : Params} {Q D F : Finset (Fin P.n)}
    (hQ : P.n - P.f ≤ Q.card) (hD : P.n - P.f ≤ D.card)
    (hQD : Q ∩ D ⊆ F) (hF : F.card ≤ P.f) : False
```

(`|Q| + |D| = |Q ∪ D| + |Q ∩ D| ≤ n + f`, against `2(n − f) > n + f` from
`P.hf` — the same arithmetic as `exists_honest_recv₂`, exposed as a set
statement because `VoteWall` is a set of *processes*, not a receipt row).

## Why this shape: the compression attack dies at `n = 4, f = 1`

A one-level-shallower reading of the grade-1 evidence — `f + 1` `VOTE v`
receipts in place of `f + 1` `BIND v` receipts, with the `ECHO5` level elided
and the returns reading `BIND` quorums — admits the following binding
violation, which pins both D18 and the certificate design. Prefix: `p1`, `p2`,
`p3` are called and echo `0`, `1`, `0` respectively; with both bits `Valid`
everywhere, all three vote ⊥, bind ⊥ (and echo5 ⊥), and `p1` C-returns off the
three ⊥-receipts while `p4` is held unscheduled at the echo stage. Extension
A: `p4` echoes `0` and votes `0` off the `ECHO 0` senders `{p1, p3, p4}`;
`p2` is corrupted and injects `VOTE 0` and `BIND 0`; `p3` collects `f + 1 = 2`
`VOTE 0` receipts from `{p4, p2}` and B-returns `0`. Extension B is the
mirror image (corrupt `p1`, hand out `1`) — one C-return, two extensions,
two different surviving bits: binding fails, and no forward simulation into
any binding-faithful spec exists.

Against the D18 evidence level the attack dies: in extension A, `p3`'s
`retB 0` needs `f + 1 = 2` `BIND 0` receipts, hence an honest `BIND 0` sender
(`2 > |F| = 1`), hence an `n − f = 3`-strong `VOTE 0` receipt quorum at that
sender. But the prefix pinned the write-once votes of `p1`, `p2`, `p3` at ⊥,
and `p2` is the corrupted process position, so the `VOTE 0` senders available in any
extension are at most `{p4} ∪ F = {p4, p2}` — `2 < 3`, no quorum, no honest
`BIND 0`, no `retB 0` (and a fortiori no `retA 0`: an honest `ECHO5 0` needs
three `BIND 0` senders). Symmetrically for bit `1` in extension B. In
certificate terms: at `p1`'s C-return the honest `BIND ⊥` senders' vote
quorums pin `{p1, p2, p3}` as committed-⊥-or-`F`, which is `VoteWall` at
`n − f = 3` for **both** bits — exactly the `∃ b, ExcludedCert` the `retC` run
consumes, and exactly why no later receipt pattern can contradict the exclusion.

## Where the shapes surface downstream

The exclusion set and the exclusion certificate are read directly by the files above this
one. The `HybridRefinesSpecification/Relation.lean` chain and
`HybridRefinesSpecification/Simulation.lean` phrase the round skeleton over `excluded`:
`IsLastBound g r` is `(g r).excluded ≠ ∅ ∧ (g (r + 1)).excluded = ∅`, `Closed g r` is
`(g r).excluded ≠ ∅ ∨ (g r).grade = some false`, and `a_commit`, `gradeA_needs_bind`,
`bind_supp` and the A-lock certificates are keyed on the guard pair
`(!b) ∈ excluded ∧ b ∉ excluded` — the D19 rendering of `bind = some b`, with
`bind ≠ none` rendered as `excluded ≠ ∅`. `GBCASim.instRel_corrupt` carries the
`excluded_cert` row through `ExcludedCert.mono`, whose three hypotheses it discharges by
`corrupt_recv`, `corrupt_proc` and `corrupt_F_subset`.
`ImplementationByABDY/System.lean`'s rendering carries the same levels inside one process:
the stage record `GBCA.ByABDY.StageRec` keeps the write-once `sentEcho5` field in its
`proc` record and carries its own `echo5Count` over its received set rows, the rendezvous
rows `gsndEcho5Bit`/`gsndEcho5Bot` are the echo5 multicasts read off that record, and the
three `retG` rows (and their `byzantineRetG` counterparts) read the echo5 level off it. No
translation is needed to the global view: the round-`r` `ImplState` *is* the round
instance's own state — the stage records with their received set rows beside the round's
network state, which holds the per-sender sent sets and the corrupted set — and
`ImplState.echo5Count` reads the receiving program's received set rows directly. So
`GBCA.ByABDY.subSim` consumes `implRefines` as it stands: the projection `composition_projects`
(`ABA/Composition/GBCAInstanceByABDY.lean`) matches every round-instance transition with
the implementation instance's at that same state, one step for one step, and this file's
refinement answers it, its weak answer read back at the round instance's interface — which
is what licenses replacing a round's instance by the graded agreement specification.

## Risks and open points

1. **`Bool` negation syntax.** Two elaboration traps. (a) `bindUnset b`'s
   support guard mentions `some (!b)`; instantiating `b := !v` produces
   `some (!(!v))`, which is not
   definitionally `some v` — the run lemmas carry one
   `simpa only [Bool.not_not]` at the `bindUnset` application. (b) `!` binds
   looser than `∈`/`∉`, so `!v ∈ s.excluded` silently elaborates as the coerced
   `!(decide (v ∈ s.excluded))`; every membership guard on the negated bit must be
   written `(!v) ∈ s.excluded` / `(!v) ∉ t.excluded`.
2. **`retB`'s `honce` receipt.** The implementation's `retB` keeps the
   algorithm's "at least one `ECHO5 v` receipt" guard. The simulation never
   reads it (the `f + 1` `BIND v` receipts carry all evidence), so it rides
   along as pure conformance; it must not be dropped from the rule — the rule
   is the algorithm.
3. **Canonical `C`-exclude via `Classical.choose`.** The `retC` row consumes
   `∃ b, ExcludedCert P s b` nonconstructively. If a later development (e.g. a
   quantitative or decidability layer) needs the choice computable, replace it
   with the explicit case split (`if EchoQuorum … true then false else …`);
   nothing in the simulation depends on which certified bit is chosen.
4. **`excluded.card ≤ 1` carries no conjunct of its own.** It holds at every
   state of every execution of the specification instance
   (`GBCASafety.excluded_card_le_one`), by the `hd0 : excluded = ∅` guard on the
   single writer, and it is a consequence of `bound_excluded`, `excludedOf`
   taking only `∅` and singletons. A separate conjunct would create restoration
   obligations on every row for no benefit, and each run gets its `hd0` from the
   branch analysis of its own row (`excluded_empty_of_both` at the value
   returns, the `bound` split at `retC`). Recorded so nobody "strengthens" the
   relation into extra work.
5. **`VoteWall` reads process-local fields.** Unlike `EchoQuorum` it counts
   `sentVote` fields, not receipts — still monotone in `F` (a corrupted field
   stays in the wall via the `j ∈ F` disjunct) and in `sentVote` (write-once),
   which is all the simulation needs. Any per-process decomposition must
   therefore be read through the same accessors as the other `proc`-field
   predicates — `ImplState.proc` for the field and `ImplState.F` for the
   corrupted set, the latter reading the set held by the round's own
   network state, which is the state's second component.
6. **Vacuous-fill hazard in `excludedCert_of_echo5Bot_quorum`.** The Case B branch
   needs the global classical split "some honest bit-voter exists"; its
   **no**-branch uses `bindBot_conf` on a *specific* honest `BIND` sender
   derived from `echo5Bot_conf`'s any-`BIND` count. That derivation wants
   `exists_sender_notMem` on an any-payload count, i.e. the payload-returning
   variant `ImplState.exists_bind_sender_notMem`:
   `∃ k w, k ∉ F ∧ Msg.bind w ∈ s.recv p k`, same proof as the exact-message
   version.
