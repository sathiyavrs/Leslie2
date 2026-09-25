/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sathiya / Claude
-/

import Leslie2Protocols.ABA.Gather.Invariant

/-!
# The counting argument for the common core

`coreOfNetwork` is a bound core of the gather instance over the broadcast specifications
(`Gather.instanceOverBroadcastSpecification`, `ABA/Gather/Composition.lean`). At every state at
which some process outside `F` holds a committed `BIND` payload, it has at least `n − f` entries
(`single_core`), its entries are committed input entries (`single_core_approved`), and it lies
below the committed `BIND` payload of every process outside `F` (`single_core`). `coreOf_recorded`
is the pair of guards the specification's `bindCore` consumes, read off an `n − f` quorum of
coordinates holding a committed `BIND` payload.

The argument runs on one incidence on the gather network state: `j` is dominated by `q` when `q`'s
committed `BIND` payload contains `j`'s `ECHO` payload. The invariant of
`ABA/Gather/Invariant.lean` makes every `dominatedBy` set large -- a process outside `F` dominates
at least `n − f` senders (`dominatedBy_card`) -- and the pigeonhole
(`exists_dominators`) then gives a sender outside `F` with at least `f + 1` dominators, whose
write-once `ECHO` payload is the core (`transfer`, `core_witness`).

The counting is over that one incidence on the gather network state, so the lemmas that read that
state alone -- `mem_correct`, `mem_dominatedBy`, `correct_filter_dominatedBy`, `sum_dominatedBy` --
are the ones of `ABA/Gather/MessagesAndCommonCore.lean`, applied to `networkOf`.

`bindAbove` is the write-once witness the refinement carries: the coordinates holding a
committed `BIND` payload above a given set. It is blind to the corrupted set and monotone
(`bindVal_mono`, `bindAbove_mono`), so it survives every transition and every corruption.
-/

namespace PLTS
namespace ABA
namespace Gather

variable {X : Type} [DecidableEq X] {P : Parameters}

/-- The gather network state of the composition, read as an instance state over
the gather's base variables. The core and the incidence read the sent sets and the
corrupted set, and no program's variables. -/
def networkOf {n : ℕ} (s : StateOverBroadcastSpecification n X) :
    InstanceState n (BaseProcessVariables n X) (Message n X) :=
  ((fun _ => LocalState.initial n (Message n X) (BaseProcessVariables.initial n X)),
    (gatherProgramsAndNetwork
    s).2)

omit [DecidableEq X] in
@[simp] theorem networkOf_sent {n : ℕ} (s : StateOverBroadcastSpecification n X) :
    (networkOf s).sent = (gatherProgramsAndNetwork s).sent := rfl

omit [DecidableEq X] in
@[simp] theorem networkOf_F {n : ℕ} (s : StateOverBroadcastSpecification n X) : (networkOf s).F =
  (gatherProgramsAndNetwork s).F
  := rfl

omit [DecidableEq X] in
/-- The core of the composition's gather network state. -/
theorem coreOf_networkOf (s : StateOverBroadcastSpecification P.n X) :
    coreOf P (networkOf s) = coreOfNetwork P (gatherProgramsAndNetwork s).2 := rfl

/-! ### The incidence on the gather network state

The incidence reads the sent sets and the corrupted set, so
`mem_correct`, `card_correct`, `mem_dominatedBy`, `correct_filter_dominatedBy` and
`sum_dominatedBy` apply to `networkOf` as they stand. What the invariant supplies is
the size of each `dominatedBy` set. -/

omit [DecidableEq X] in
/-- The `ECHO` payload of a process outside `F` is the one its `sentEcho` field
holds. -/
theorem echoOf_eq {s : StateOverBroadcastSpecification P.n X} (hInv : Invariant P s) {j : Fin P.n}
    (hj : j ∉ (gatherProgramsAndNetwork s).F) {A : AcceptedPairs P.n X}
    (hA : Message.echo A ∈ (gatherProgramsAndNetwork s).sent j) : echoOf (networkOf s) j = A := by
  classical
  have hex : ∃ A : AcceptedPairs P.n X, Message.echo A ∈ (networkOf s).sent j := ⟨A, hA⟩
  rw [echoOf, dif_pos hex]
  have h1 := hInv.echo_confirmed j hj _ hex.choose_spec
  have h2 := hInv.echo_confirmed j hj A hA
  rw [h1] at h2
  exact Option.some.inj h2

omit [DecidableEq X] in
/-- **Every `dominatedBy` set is large**: a process outside `F` dominates at
least `n − f` senders. Its `VOTE` payload, if it has one, is backed by `n − f`
received `ECHO` messages; if it has none the condition is vacuous and the set is
everything. -/
theorem dominatedBy_card {s : StateOverBroadcastSpecification P.n X} (hInv : Invariant P s)
    {q : Fin P.n} (hq : q ∉ (gatherProgramsAndNetwork s).F) : P.n - P.f ≤ (dominatedBy (networkOf s)
      q).card := by
  classical
  by_cases hv : ∃ W : AcceptedPairs P.n X, Message.vote W ∈ (gatherProgramsAndNetwork s).sent q
  · obtain ⟨W, hW⟩ := hv
    have hslot := hInv.vote_confirmed q hq W hW
    obtain ⟨Q, hQc, hQm⟩ := hInv.vote_backed q hq W hslot
    refine le_trans hQc (Finset.card_le_card fun j hj => ?_)
    rw [mem_dominatedBy]
    intro W' hW'
    have hslot' := hInv.vote_confirmed q hq W' hW'
    rw [hslot] at hslot'
    obtain rfl : W = W' := Option.some.inj hslot'
    obtain ⟨A, hA, hAW⟩ := hQm j hj
    exact ⟨A, hInv.received_subset_sent q j hA, hAW⟩
  · have hall : dominatedBy (networkOf s) q = Finset.univ := by
      refine Finset.eq_univ_iff_forall.mpr fun j => ?_
      rw [mem_dominatedBy]
      intro W hW
      exact absurd ⟨W, hW⟩ hv
    rw [hall, Finset.card_univ, Fintype.card_fin]
    omega

open scoped Classical in
omit [DecidableEq X] in
/-- The `dominatedBy` set of a process outside `F` meets the processes outside
`F` in at least `n − f − |F|` of them. -/
theorem dominatedBy_correct_card {s : StateOverBroadcastSpecification P.n X} (hInv : Invariant P s)
    {q : Fin P.n} (hq : q ∉ (gatherProgramsAndNetwork s).F) :
    P.n - P.f - (gatherProgramsAndNetwork s).F.card ≤
      ((correct (networkOf s)).filter (fun j => j ∈ dominatedBy (networkOf s) q)).card := by
  rw [correct_filter_dominatedBy, networkOf_F]
  have h1 := Finset.le_card_sdiff (gatherProgramsAndNetwork s).F (dominatedBy (networkOf s) q)
  have h2 := dominatedBy_card hInv hq
  omega

open scoped Classical in
omit [DecidableEq X] in
/-- **The pigeonhole.** Some sender outside `F` has at least `n − f − |F|`
dominators. -/
theorem exists_dominators {s : StateOverBroadcastSpecification P.n X} (hInv : Invariant P s) :
    ∃ j₀, j₀ ∈ correct (networkOf s) ∧
      P.n - P.f - (gatherProgramsAndNetwork s).F.card ≤ (dominators (networkOf s) j₀).card := by
  by_contra hc
  push Not at hc
  have hF := hInv.F_card
  have hf := P.hResilience
  set H : Finset (Fin P.n) := correct (networkOf s) with hH
  set m : ℕ := P.n - P.f - (gatherProgramsAndNetwork s).F.card with hm
  have hHcard : H.card = P.n - (gatherProgramsAndNetwork s).F.card := card_correct
  have hpos : 0 < H.card := by
    omega
  have hlow : ∀ q ∈ H, m ≤ ((correct (networkOf s)).filter
      (fun j => j ∈ dominatedBy (networkOf s) q)).card :=
    fun q hq => dominatedBy_correct_card hInv (mem_correct.mp (hH ▸ hq))
  have hsum2 : H.card * m
      ≤ ∑ q ∈ H, ((correct (networkOf s)).filter
        (fun j => j ∈ dominatedBy (networkOf s) q)).card := by
    simpa [smul_eq_mul] using Finset.card_nsmul_le_sum H _ m hlow
  rw [sum_dominatedBy, ← hH] at hsum2
  have hle : ∀ j ∈ H, (dominators (networkOf s) j).card ≤ m - 1 := fun j hj => by
    have := hc j (hH ▸ hj); omega
  have hsum1 : ∑ j ∈ H, (dominators (networkOf s) j).card ≤ H.card * (m - 1) := by
    simpa [smul_eq_mul] using Finset.sum_le_card_nsmul H _ (m - 1) hle
  have hstrict : H.card * (m - 1) < H.card * m :=
    mul_lt_mul_of_pos_left (by omega) hpos
  omega

/-! ### The single core -/

open scoped Classical in
omit [DecidableEq X] in
/-- **The transfer.** A sender outside `F` with at least `f + 1` dominators has
its `ECHO` payload below every committed `BIND` payload of a process outside
`F`: the dominators meet that payload's backing `VOTE` quorum of `n − f`, and
the meeting process's write-once `VOTE` payload lies above the `ECHO` payload
and below the `BIND` payload. -/
theorem transfer {s : StateOverBroadcastSpecification P.n X} (hInv : Invariant P s) {j₀ : Fin P.n}
    (hj₀ : j₀ ∉ (gatherProgramsAndNetwork s).F) (hcnt : P.f + 1 ≤ (dominators (networkOf s)
      j₀).card)
    {k : Fin P.n} (hk : k ∉ (gatherProgramsAndNetwork s).F) {U : AcceptedPairs P.n X}
    (hU : (bindBroadcasts s k).val = some U) :
    ∃ A, Message.echo A ∈ (gatherProgramsAndNetwork s).sent j₀ ∧ P.n - P.f ≤ A.card ∧ A ⊆ U := by
  obtain ⟨V, hVc, hVm⟩ :=
    hInv.bind_backed k hk U ((hInv.bindBroadcastVal_of_instanceInput k U hU).resolve_left hk)
  obtain ⟨q, hqK, hqV⟩ := InstanceState.exists_mem_inter_of_quorum hcnt hVc
  rw [dominators, Finset.mem_filter] at hqK
  obtain ⟨W, hWrecv, hWU⟩ := hVm q hqV
  obtain ⟨A, hA, hAW⟩ := mem_dominatedBy.mp hqK.2 W (hInv.received_subset_sent k q hWrecv)
  exact ⟨A, hA, hInv.echo_card j₀ hj₀ A (hInv.echo_confirmed j₀ hj₀ A hA),
    subset_trans hAW hWU⟩

open scoped Classical in
omit [DecidableEq X] in
/-- The core is the write-once `ECHO` payload of a sender outside `F` with at
least `f + 1` dominators, as soon as some process outside `F` holds a committed
`BIND` payload. -/
theorem core_witness {s : StateOverBroadcastSpecification P.n X} (hInv : Invariant P s)
    {k₀ : Fin P.n} (hk₀ : k₀ ∉ (gatherProgramsAndNetwork s).F) {U₀ : AcceptedPairs P.n X}
    (hU₀ : (bindBroadcasts s k₀).val = some U₀) :
    ∃ j₁, j₁ ∉ (gatherProgramsAndNetwork s).F ∧ P.f + 1 ≤ (dominators (networkOf s) j₁).card ∧
      Message.echo (coreOfNetwork P (gatherProgramsAndNetwork s).2) ∈ (gatherProgramsAndNetwork
        s).sent j₁ ∧
      ((gatherProgramsAndNetwork s).processVariables j₁).sentEcho = some (coreOfNetwork P
        (gatherProgramsAndNetwork s).2) := by
  have hF := hInv.F_card
  have hf := P.hResilience
  have hex : ∃ j, j ∈ correct (networkOf s) ∧ P.f + 1 ≤ (dominators (networkOf s) j).card := by
    obtain ⟨j₀, hj₀, hcnt⟩ := exists_dominators hInv
    exact ⟨j₀, hj₀, by omega⟩
  have hspec := hex.choose_spec
  have hj₁F : hex.choose ∉ (gatherProgramsAndNetwork s).F := mem_correct.mp hspec.1
  obtain ⟨A, hA, -, -⟩ := transfer hInv hj₁F hspec.2 hk₀ hU₀
  have hcore : coreOfNetwork P (gatherProgramsAndNetwork s).2 = A := by
    rw [← coreOf_networkOf, coreOf, dif_pos hex]
    exact echoOf_eq hInv hj₁F hA
  exact ⟨hex.choose, hj₁F, hspec.2, by rw [hcore]; exact hA,
    by rw [hcore]; exact hInv.echo_confirmed _ hj₁F A hA⟩

omit [DecidableEq X] in
/-- **The single core.** Once some process outside `F` holds a committed `BIND`
payload, the core has at least `n − f` entries and lies below the committed
`BIND` payload of every process outside `F`. -/
theorem single_core {s : StateOverBroadcastSpecification P.n X} (hInv : Invariant P s)
    {k₀ : Fin P.n} (hk₀ : k₀ ∉ (gatherProgramsAndNetwork s).F) {U₀ : AcceptedPairs P.n X}
    (hU₀ : (bindBroadcasts s k₀).val = some U₀) :
    P.n - P.f ≤ (coreOfNetwork P (gatherProgramsAndNetwork s).2).card ∧
      ∀ k ∉ (gatherProgramsAndNetwork s).F, ∀ U : AcceptedPairs P.n X, (bindBroadcasts s k).val =
        some U →
        coreOfNetwork P (gatherProgramsAndNetwork s).2 ⊆ U := by
  obtain ⟨j₁, hj₁F, hcnt, hsent, hslot⟩ := core_witness hInv hk₀ hU₀
  refine ⟨hInv.echo_card j₁ hj₁F _ hslot, ?_⟩
  intro k hk U hU
  obtain ⟨A, hA, -, hAU⟩ := transfer hInv hj₁F hcnt hk hU
  have hEq : A = coreOfNetwork P (gatherProgramsAndNetwork s).2 := by
    have h1 := hInv.echo_confirmed j₁ hj₁F A hA
    rw [hslot] at h1
    exact (Option.some.inj h1).symm
  rw [← hEq]
  exact hAU

omit [DecidableEq X] in
/-- **The core is approved**: its entries are committed input entries, the
`ECHO` field it comes from carrying only such entries. -/
theorem single_core_approved {s : StateOverBroadcastSpecification P.n X} (hInv : Invariant P s)
    {k₀ : Fin P.n} (hk₀ : k₀ ∉ (gatherProgramsAndNetwork s).F) {U₀ : AcceptedPairs P.n X}
    (hU₀ : (bindBroadcasts s k₀).val = some U₀) :
    approved s (coreOfNetwork P (gatherProgramsAndNetwork s).2) := by
  obtain ⟨j₁, -, -, -, hslot⟩ := core_witness hInv hk₀ hU₀
  exact hInv.echo_approved j₁ _ hslot

/-! ### The witness that the core is written once -/

open scoped Classical in
/-- The coordinates holding a committed `BIND` payload above `C`. The condition
is blind to `F`. -/
noncomputable def bindAbove (s : StateOverBroadcastSpecification P.n X) (C : AcceptedPairs P.n X) :
    Finset (Fin P.n) :=
  Finset.univ.filter (fun q => ∃ U, (bindBroadcasts s q).val = some U ∧ C ⊆ U)

open scoped Classical in
theorem mem_bindAbove {s : StateOverBroadcastSpecification P.n X} {C : AcceptedPairs P.n X}
    {q : Fin P.n} : q ∈ bindAbove s C ↔ ∃ U, (bindBroadcasts s q).val = some U ∧ C ⊆ U := by
  rw [bindAbove, Finset.mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ _, h⟩⟩

/-- A committed `BIND` payload is never rewritten. -/
theorem bindVal_mono {s s' : StateOverBroadcastSpecification P.n X} {l : Label P.n X}
    {μ : PMF (StateOverBroadcastSpecification P.n X)}
    (hstep : AlgorithmOverBroadcastSpecification P s l μ) (hs' : s' ∈ μ.support) {q : Fin P.n}
    {U : AcceptedPairs P.n X} (h : (bindBroadcasts s q).val = some U) :
    (bindBroadcasts s' q).val = some U := by
  cases hstep with
  | commitBindEntry q' U' hv hm =>
      rw [PMF.mem_support_pure_iff] at hs'; subst hs'
      dsimp only [bindBroadcasts_setBindBroadcasts]
      by_cases hq : q = q'
      · subst hq; rw [hv] at h; exact absurd h (by simp)
      · rw [Function.update_of_ne hq]; exact h
  | bindCall j U' hin hvot hsnd happ hQ hb =>
      rw [PMF.mem_support_pure_iff] at hs'; subst hs'
      dsimp only [bindBroadcasts_setBindBroadcasts]
      by_cases hq : q = j
      · subst hq; rw [Function.update_self]; exact h
      · rw [Function.update_of_ne hq]; exact h
  | bindRet q' j U' hv hr =>
      rw [PMF.mem_support_pure_iff] at hs'; subst hs'
      dsimp only [bindBroadcasts_setBindBroadcasts]
      by_cases hq : q = q'
      · subst hq; rw [Function.update_self]; exact h
      · rw [Function.update_of_ne hq]; exact h
  | fail id =>
      rw [PMF.mem_support_pure_iff] at hs'; subst hs'
      dsimp only [bindBroadcasts_corruptAll]
      rw [BRB.corrupt_val]; exact h
  | _ => rw [PMF.mem_support_pure_iff] at hs'; subst hs'; exact h

/-- **The witness is monotone.** The coordinates holding a committed `BIND`
payload above `C` only accumulate, under every transition and every corruption. -/
theorem bindAbove_mono {s s' : StateOverBroadcastSpecification P.n X} {l : Label P.n X}
    {μ : PMF (StateOverBroadcastSpecification P.n X)}
    (hstep : AlgorithmOverBroadcastSpecification P s l μ) (hs' : s' ∈ μ.support)
    (C : AcceptedPairs P.n X) : bindAbove s C ⊆ bindAbove s' C := by
  intro q hq
  rw [mem_bindAbove] at hq ⊢
  obtain ⟨U, hU, hCU⟩ := hq
  exact ⟨U, bindVal_mono hstep hs' hU, hCU⟩

/-- **The core write.** At a state where an `n − f` quorum of coordinates holds
committed `BIND` payloads, the core has at least `n − f` entries, its entries
are committed input entries, and at least `f + 1` coordinates hold a committed
`BIND` payload above it. The last is the witness that holds the returns
after the first to this core: it is blind to `F` and monotone
(`bindAbove_mono`), and an `n − f` return quorum meets it. -/
theorem coreOf_recorded {s : StateOverBroadcastSpecification P.n X} (hInv : Invariant P s)
    {Q : Finset (Fin P.n)} (hQc : P.n - P.f ≤ Q.card)
    (hQm : ∀ q ∈ Q, ∃ U : AcceptedPairs P.n X, (bindBroadcasts s q).val = some U) :
    P.n - P.f ≤ (coreOfNetwork P (gatherProgramsAndNetwork s).2).card ∧ approved s
    (coreOfNetwork P (gatherProgramsAndNetwork s).2) ∧ P.f + 1 ≤
    (bindAbove s (coreOfNetwork P (gatherProgramsAndNetwork s).2)).card := by
  classical
  have hF := hInv.F_card
  have hf := P.hResilience
  have hH : P.f + 1 ≤ (Q \ (gatherProgramsAndNetwork s).F).card := by
    have h1 := Finset.le_card_sdiff (gatherProgramsAndNetwork s).F Q
    omega
  obtain ⟨H, hHsub, hHcard⟩ := Finset.exists_subset_card_eq hH
  have hHQ : ∀ q ∈ H, q ∈ Q := fun q hq => (Finset.mem_sdiff.mp (hHsub hq)).1
  have hHF : ∀ q ∈ H, q ∉ (gatherProgramsAndNetwork s).F := fun q hq => (Finset.mem_sdiff.mp (hHsub
    hq)).2
  have hHne : H.Nonempty := by
    rw [← Finset.card_pos, hHcard]; omega
  obtain ⟨q₀, hq₀⟩ := hHne
  obtain ⟨U₀, hU₀⟩ := hQm q₀ (hHQ q₀ hq₀)
  obtain ⟨hcard, hsub⟩ := single_core hInv (hHF q₀ hq₀) hU₀
  refine ⟨hcard, single_core_approved hInv (hHF q₀ hq₀) hU₀, ?_⟩
  refine le_trans (le_of_eq hHcard.symm) (Finset.card_le_card fun q hq => ?_)
  obtain ⟨U, hU⟩ := hQm q (hHQ q hq)
  exact mem_bindAbove.mpr ⟨U, hU, hsub q (hHF q hq) U hU⟩

end Gather
end ABA
end PLTS
