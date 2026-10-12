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
which the sent set of some process outside `F` holds a `BIND` payload, the core has at least
`n − f` entries (`single_core`), its entries are committed input entries (`single_core_approved`),
and it lies below every `BIND` payload in the sent set of a process outside `F` (`single_core`).

The argument runs on one incidence on the gather network state: `j` is dominated by `q` when every
`VOTE` payload `q` sent contains an `ECHO` payload `j` sent. The invariant of
`ABA/Gather/Invariant.lean` makes every `dominatedBy` set large -- a process outside `F` dominates
at least `n − f` senders (`dominatedBy_card`) -- and the pigeonhole
(`exists_dominators`) then gives a sender outside `F` with at least `f + 1` dominators, whose
write-once `ECHO` payload is the core (`core_witness`). A `BIND` payload multicast by a process
outside `F` is its write-once `BIND` field (`bind_confirmed`), backed by `n − f` received `VOTE`
payloads (`bind_backed`). The `f + 1` dominators meet that quorum, so the core lies below the
`BIND` payload (`transfer`).

The counting is over that one incidence on the gather network state, so the lemmas that read that
state alone -- `mem_correct`, `mem_dominatedBy`, `correct_filter_dominatedBy`, `sum_dominatedBy` --
are the ones of `ABA/Gather/MessagesAndCommonCore.lean`, applied to `networkOf`.

## The witness held after the first return

`withoutBindAbove s C` is the set of processes outside `F` whose sent set holds no `BIND` payload
containing `C`. The first return writes the core `C`. Its returner has received `BIND` payloads
from `n − f` senders, and each of them outside `F` has sent a `BIND` payload containing `C`, so
the set has at most `f` members (`coreOf_recorded`). Along every transition `F` and every sent set
only grow, so the set only loses members (`withoutBindAbove_step`, `withoutBindAbove_corruptAll`).
At a later return, the `n − f` senders of the returner's received `BIND` payloads include at least
`n − 3f ≥ 1` processes outside `F` and outside the set (`exists_correct_bindAbove_of_quorum`).
Such a process has sent exactly one `BIND` payload, and that payload contains `C`.
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
its `ECHO` payload below every `BIND` payload in the sent set of a process
outside `F`: the dominators meet that payload's backing `VOTE` quorum of `n − f`,
and the meeting process's write-once `VOTE` payload lies above the `ECHO` payload
and below the `BIND` payload. -/
theorem transfer {s : StateOverBroadcastSpecification P.n X} (hInv : Invariant P s) {j₀ : Fin P.n}
    (hj₀ : j₀ ∉ (gatherProgramsAndNetwork s).F) (hcnt : P.f + 1 ≤ (dominators (networkOf s)
      j₀).card)
    {k : Fin P.n} (hk : k ∉ (gatherProgramsAndNetwork s).F) {U : AcceptedPairs P.n X}
    (hU : Message.bind U ∈ (gatherProgramsAndNetwork s).sent k) :
    ∃ A, Message.echo A ∈ (gatherProgramsAndNetwork s).sent j₀ ∧ P.n - P.f ≤ A.card ∧ A ⊆ U := by
  obtain ⟨V, hVc, hVm⟩ := hInv.bind_backed k hk U (hInv.bind_confirmed k hk U hU)
  obtain ⟨q, hqK, hqV⟩ := InstanceState.exists_mem_inter_of_quorum hcnt hVc
  rw [dominators, Finset.mem_filter] at hqK
  obtain ⟨W, hWrecv, hWU⟩ := hVm q hqV
  obtain ⟨A, hA, hAW⟩ := mem_dominatedBy.mp hqK.2 W (hInv.received_subset_sent k q hWrecv)
  exact ⟨A, hA, hInv.echo_card j₀ hj₀ A (hInv.echo_confirmed j₀ hj₀ A hA),
    subset_trans hAW hWU⟩

open scoped Classical in
omit [DecidableEq X] in
/-- The core is the write-once `ECHO` payload of a sender outside `F` with at
least `f + 1` dominators, as soon as the sent set of some process outside `F`
holds a `BIND` payload. -/
theorem core_witness {s : StateOverBroadcastSpecification P.n X} (hInv : Invariant P s)
    {k₀ : Fin P.n} (hk₀ : k₀ ∉ (gatherProgramsAndNetwork s).F) {U₀ : AcceptedPairs P.n X}
    (hU₀ : Message.bind U₀ ∈ (gatherProgramsAndNetwork s).sent k₀) :
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
/-- **The single core.** Once the sent set of some process outside `F` holds a
`BIND` payload, the core has at least `n − f` entries and lies below every `BIND`
payload in the sent set of a process outside `F`. -/
theorem single_core {s : StateOverBroadcastSpecification P.n X} (hInv : Invariant P s)
    {k₀ : Fin P.n} (hk₀ : k₀ ∉ (gatherProgramsAndNetwork s).F) {U₀ : AcceptedPairs P.n X}
    (hU₀ : Message.bind U₀ ∈ (gatherProgramsAndNetwork s).sent k₀) :
    P.n - P.f ≤ (coreOfNetwork P (gatherProgramsAndNetwork s).2).card ∧
      ∀ k ∉ (gatherProgramsAndNetwork s).F, ∀ U : AcceptedPairs P.n X,
        Message.bind U ∈ (gatherProgramsAndNetwork s).sent k →
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
    (hU₀ : Message.bind U₀ ∈ (gatherProgramsAndNetwork s).sent k₀) :
    approved s (coreOfNetwork P (gatherProgramsAndNetwork s).2) := by
  obtain ⟨j₁, -, -, -, hslot⟩ := core_witness hInv hk₀ hU₀
  exact hInv.echo_approved j₁ _ hslot

/-! ### The witness that the core is written once -/

open scoped Classical in
/-- The processes outside `F` whose sent set holds no `BIND` payload containing `C`. -/
noncomputable def withoutBindAbove (s : StateOverBroadcastSpecification P.n X)
    (C : AcceptedPairs P.n X) : Finset (Fin P.n) :=
  Finset.univ.filter (fun d => d ∉ (gatherProgramsAndNetwork s).F ∧
    ∀ U, Message.bind U ∈ (gatherProgramsAndNetwork s).sent d → ¬ C ⊆ U)

open scoped Classical in
omit [DecidableEq X] in
/-- A process is in `withoutBindAbove s C` exactly when it is outside `F` and no `BIND` payload in
its sent set contains `C`. -/
@[simp] theorem mem_withoutBindAbove {s : StateOverBroadcastSpecification P.n X}
    {C : AcceptedPairs P.n X} {d : Fin P.n} :
    d ∈ withoutBindAbove s C ↔ d ∉ (gatherProgramsAndNetwork s).F ∧
      ∀ U, Message.bind U ∈ (gatherProgramsAndNetwork s).sent d → ¬ C ⊆ U := by
  rw [withoutBindAbove, Finset.mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ _, h⟩⟩

omit [DecidableEq X] in
/-- A state whose corrupted set and sent sets contain those of `s` has a smaller
`withoutBindAbove` set. -/
theorem withoutBindAbove_subset_of_subset {s s' : StateOverBroadcastSpecification P.n X}
    {C : AcceptedPairs P.n X}
    (hF : (gatherProgramsAndNetwork s).F ⊆ (gatherProgramsAndNetwork s').F)
    (hsent : ∀ d, (gatherProgramsAndNetwork s).sent d ⊆ (gatherProgramsAndNetwork s').sent d) :
    withoutBindAbove s' C ⊆ withoutBindAbove s C := by
  intro d hd
  rw [mem_withoutBindAbove] at hd ⊢
  exact ⟨fun h => hd.1 (hF h), fun U hU => hd.2 U (hsent d hU)⟩

omit [DecidableEq X] in
/-- A corruption grows `F` and leaves every sent set, so the `withoutBindAbove` set
only loses members. -/
theorem withoutBindAbove_corruptAll (s : StateOverBroadcastSpecification P.n X) (id : Fin P.n)
    (cIn : BRB.SpecState P.n X → BRB.SpecState P.n X) (C : AcceptedPairs P.n X) :
    withoutBindAbove (corruptAll P id cIn s) C ⊆ withoutBindAbove s C := by
  refine withoutBindAbove_subset_of_subset ?_ (fun d m hm => ?_)
  · rw [gatherProgramsAndNetwork_corruptAll]
    exact InstanceState.corrupt_F_subset _ id
  · rwa [gatherProgramsAndNetwork_corruptAll, InstanceState.corrupt_sent]

/-- **The witness only loses members.** Along every transition the corrupted set
and every sent set only grow, so the `withoutBindAbove` set only shrinks. -/
theorem withoutBindAbove_step {s s' : StateOverBroadcastSpecification P.n X} {l : Label P.n X}
    {μ : PMF (StateOverBroadcastSpecification P.n X)}
    (hstep : AlgorithmOverBroadcastSpecification P s l μ) (hs' : s' ∈ μ.support)
    (C : AcceptedPairs P.n X) : withoutBindAbove s' C ⊆ withoutBindAbove s C := by
  cases hstep with
  | fail id =>
    rw [PMF.mem_support_pure_iff] at hs'
    subst hs'
    exact withoutBindAbove_corruptAll s id _ C
  | _ =>
    rw [PMF.mem_support_pure_iff] at hs'
    subst hs'
    refine withoutBindAbove_subset_of_subset (fun x hx => ?_) (fun d m hm => ?_)
    · simpa using hx
    · simp [InstanceState.mem_multicast_sent, hm]

omit [DecidableEq X] in
/-- **The core write.** At a state where the returner `id` has received `BIND`
payloads from an `n − f` quorum, the core has at least `n − f` entries, its
entries are committed input entries, and at most `f` processes outside `F` have
sent no `BIND` payload containing it. The last is the witness that holds the
returns after the first: it only loses members (`withoutBindAbove_step`), and an
`n − f` return quorum meets its complement outside `F`
(`exists_correct_bindAbove_of_quorum`). -/
theorem coreOf_recorded {s : StateOverBroadcastSpecification P.n X} (hInv : Invariant P s)
    {id : Fin P.n} {Q : Finset (Fin P.n)} (hQ : P.n - P.f ≤ Q.card)
    (hrecv : ∀ q ∈ Q, ∃ U : AcceptedPairs P.n X,
      Message.bind U ∈ (gatherProgramsAndNetwork s).received id q) :
    P.n - P.f ≤ (coreOfNetwork P (gatherProgramsAndNetwork s).2).card ∧
      approved s (coreOfNetwork P (gatherProgramsAndNetwork s).2) ∧
      (withoutBindAbove s (coreOfNetwork P (gatherProgramsAndNetwork s).2)).card ≤ P.f := by
  have hF := hInv.F_card
  have hf := P.hResilience
  have hsent : ∀ q ∈ Q, ∃ U : AcceptedPairs P.n X,
      Message.bind U ∈ (gatherProgramsAndNetwork s).sent q := fun q hq => by
    obtain ⟨U, hU⟩ := hrecv q hq
    exact ⟨U, hInv.received_subset_sent id q hU⟩
  have hlt : (gatherProgramsAndNetwork s).F.card < Q.card := by
    omega
  obtain ⟨k₀, hk₀Q, hk₀F⟩ := InstanceState.exists_correct_of_card_lt hlt
  obtain ⟨U₀, hU₀⟩ := hsent k₀ hk₀Q
  obtain ⟨hcard, hsub⟩ := single_core hInv hk₀F hU₀
  refine ⟨hcard, single_core_approved hInv hk₀F hU₀, ?_⟩
  have hle : withoutBindAbove s (coreOfNetwork P (gatherProgramsAndNetwork s).2) ⊆ Qᶜ := by
    intro d hd
    rw [mem_withoutBindAbove] at hd
    rw [Finset.mem_compl]
    intro hdQ
    obtain ⟨U, hU⟩ := hsent d hdQ
    exact hd.2 U hU (hsub d hd.1 U hU)
  have h1 := Finset.card_le_card hle
  rw [Finset.card_compl, Fintype.card_fin] at h1
  omega

omit [DecidableEq X] in
/-- **A correct sender above the core.** If at most `f` processes outside `F` have
sent no `BIND` payload containing `C`, then every `n − f` quorum has a member
outside `F` whose sent set holds a `BIND` payload containing `C`: the quorum has at
least `n − 2f` members outside `F`, at most `f` of them in `withoutBindAbove s C`,
and `n − 3f ≥ 1`. -/
theorem exists_correct_bindAbove_of_quorum {s : StateOverBroadcastSpecification P.n X}
    {C : AcceptedPairs P.n X} {Q : Finset (Fin P.n)}
    (hF : (gatherProgramsAndNetwork s).F.card ≤ P.f) (hQ : P.n - P.f ≤ Q.card)
    (hcard : (withoutBindAbove s C).card ≤ P.f) :
    ∃ d ∈ Q, d ∉ (gatherProgramsAndNetwork s).F ∧
      ∃ U, Message.bind U ∈ (gatherProgramsAndNetwork s).sent d ∧ C ⊆ U := by
  have hf := P.hResilience
  have h1 := Finset.le_card_sdiff (gatherProgramsAndNetwork s).F Q
  have h2 := Finset.le_card_sdiff (withoutBindAbove s C) (Q \ (gatherProgramsAndNetwork s).F)
  have hpos : 0 < ((Q \ (gatherProgramsAndNetwork s).F) \ withoutBindAbove s C).card := by
    omega
  obtain ⟨d, hd⟩ := Finset.card_pos.mp hpos
  rw [Finset.mem_sdiff, Finset.mem_sdiff] at hd
  obtain ⟨⟨hdQ, hdF⟩, hdJ⟩ := hd
  refine ⟨d, hdQ, hdF, ?_⟩
  by_contra hne
  exact hdJ (mem_withoutBindAbove.mpr ⟨hdF, fun U hU hCU => hne ⟨U, hU, hCU⟩⟩)

end Gather
end ABA
end PLTS
