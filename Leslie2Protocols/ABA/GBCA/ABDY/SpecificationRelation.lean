/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sathiya / Claude
-/

import Leslie2Protocols.ABA.GBCA.ABDY.ExclusionCertificate

/-!
# The simulation relation

`SpecificationRelation P s t` relates a state of the round-`r` implementation instance
(`GBCA.ByABDY.implementation`, D18) to a state of the round-`r` specification instance
(`GBCA.specInst`, the exclusion-set specification, D19). `specificationRelation P r` is the family
form, and `specificationRelation_init` holds it at the two initial states.

The implementation state is the protocol's own data, so only `call`, `ret` and `F` are read off it
directly (`SpecificationRelation.call_eq`, `ret_eq`, `F_eq`). The specification's `excluded` and
`grade` are bookkeeping the protocol records nothing; the relation carries receipt evidence for them
instead:

* `exclusion_certificate` — every excluded bit `b` is covered by an exclude certificate
  `ExclusionCertificate P s b`. The relation bounds `excluded` from above and never from below:
  which bits are actually excluded is recovered by case analysis at the return rows, not recorded.
* `grade2_evidence` / `grade0_evidence` — a grade-2 lock is backed by an `n − f`
  `ECHO5 v` receipt quorum, a grade-0 lock by an `n − f` `ECHO5 ⊥` quorum. Two
  opposing quorums intersect in a correct process that would have multicast
  two different `ECHO5` payloads, contradicting the write-once `echo5_once` —
  which is the grade-2 / grade-0 exclusivity the specification's grade guard demands
  (`grade_ne_false_of_echo5_quorum`, `grade_ne_true_of_echo5Bot_quorum`).
* `bound_excluded` — the round's bound bit and the specification's `excluded` determine each other:
  `excluded = excludedOf bound`, empty while the bit is unwritten and the singleton of its
  complement once a return has written it. This is the one clause that bounds `excluded` from below,
  and it holds because the exclusion fires with the round's first return. It supplies the guard
  `(!bnd) ∈ excluded` of a return that announces a bit already on record, and with
  `exclusion_certificate` it yields `SpecificationRelation.bound_certificate`: the bit on record
  carries an exclude certificate for its complement. A value-bearing return then announces its own
  value (`SpecificationRelation.retBound_eq`) — the return's `n − f` `VOTE v` receipt quorum refutes
  a certificate for `v` (`not_exclusionCertificate_of_voteQuorum`), so a bit on record is `v`, and a
  bit computed here is `v` by `boundOf`. A grade-0 return announces `boundOf`'s bit, whose
  complement is certified by `exclusionCertificate_boundOf_grade0`.

Both `bindUnset` guards come from one `ECHO` certificate (`bindUnset_guards`): refine it to an `n −
f` `INPUT v` receipt quorum (`inputQuorum_of_echoReceiptQuorum`), whose correct senders hold an
input (`input_called`, D8) — that is the quorum guard (`quorum_of_messageQuorum`) — and whose count
feeds `Invariant.support_of_input_receipts` for the `f + 1` InputSupport count (D15). At the grade-0
return the guards read the returner's own `|Valid| > 1` evidence instead
(`inputSupport_of_bothValid` closes both bits at once), so they are available whichever bit the
certificate names. `SpecificationRelation.callSupport` transports the counts to the specification
along `call_eq`/`F_eq`.

The specification excludes a bit by the internal τ-transition `bindUnset`, so an
implementation return that needs a not-yet-excluded bit excluded is answered by a
two-step weak run (`weakLStep_tauThen`; `excludeThenRetGrade2_run`,
`excludeThenRetGrade1_run`, `excludeThenRetGrade0_run`).
-/

open Stream'

namespace PLTS
namespace ABA
namespace GBCA.ByABDY

variable {P : Parameters}

/-! ### The simulation relation -/

/-- The exclusion set the specification holds against a bound bit: empty while
the bit is unwritten, and the singleton of its complement once it is written. -/
def excludedOf : Option Bool → Finset Bool
  | none => ∅
  | some β => {!β}

@[simp] theorem excludedOf_none : excludedOf none = (∅ : Finset Bool) := rfl

@[simp] theorem excludedOf_some (β : Bool) : excludedOf (some β) = {!β} := rfl

/-- The simulation relation: the concrete invariant, the abstraction map for
the fields the protocol itself holds (spec `call` = concrete input, spec
`ret` = concrete return flags, spec `F` = concrete `F`), and receipt evidence
for the two fields it does not. `exclusion_certificate` bounds `excluded` from above — an exclusion
certificate for every excluded bit — and never from below. -/
structure SpecificationRelation (P : Parameters) (s : ImplementationState P.n) (t : SpecState P.n) :
  Prop where
  /-- The concrete inductive invariant. -/
  invariant : Invariant P s
  /-- Spec inputs are the concrete inputs. -/
  call_eq : ∀ id, t.call id = (s.process id).input
  /-- Spec return flags are the concrete return flags. -/
  ret_eq : ∀ id, t.ret id = (s.process id).returned
  /-- The corrupted sets agree. -/
  F_eq : t.F = s.F
  /-- Every excluded bit carries a monotone exclude certificate. -/
  exclusion_certificate : ∀ b, b ∈ t.excluded → ExclusionCertificate P s b
  /-- A grade-2 lock is backed by an `n − f` `ECHO5 v` receipt quorum
  for some bit `v`. -/
  grade2_evidence : t.grade = some true →
    ∃ v i, P.n - P.f ≤ s.receivedCount i (.echo5 (some v))
  /-- A grade-0 lock is backed by an `n − f` `ECHO5 ⊥` receipt
  quorum. -/
  grade0_evidence : t.grade = some false →
    ∃ i, P.n - P.f ≤ s.receivedCount i (.echo5 none)
  /-- The round's bound bit determines the exclusion set: nothing is excluded
  while the bit is unwritten, and the complement of the bit is the one excluded
  bit once a return has written it. The exclusion fires with the round's first
  return, so the two records move together. -/
  bound_excluded : t.excluded = excludedOf s.bound

/-- The simulation relation of the round-`r` instance (the round index is
phantom: every round runs the same protocol). -/
def specificationRelation (P : Parameters) (_r : ℕ) (s : ImplementationState P.n)
    (t : SpecState P.n) : Prop :=
  SpecificationRelation P s t

/-- The initial states are related. -/
theorem specificationRelation_init (P : Parameters) (r : ℕ) :
    specificationRelation P r (implementation P r).init (specInst P r).init where
  invariant := Invariant.initial P
  call_eq := fun _ => rfl
  ret_eq := fun _ => rfl
  F_eq := rfl
  exclusion_certificate := fun b hb => absurd hb (Finset.notMem_empty b)
  grade2_evidence := fun h => absurd h (by simp [SpecState.initial])
  grade0_evidence := fun h => absurd h (by simp [SpecState.initial])
  bound_excluded := rfl

/-- The bound bit on record carries an exclude certificate for its complement:
the specification has excluded that complement, and every excluded bit is
certified. -/
theorem SpecificationRelation.bound_certificate {s : ImplementationState P.n} {t : SpecState P.n}
    (hR : SpecificationRelation P s t) (β : Bool) (hb : s.bound = some β) :
    ExclusionCertificate P s (!β) := by
  refine hR.exclusion_certificate (!β) ?_
  rw [hR.bound_excluded, hb, excludedOf_some]
  exact Finset.mem_singleton_self _

/-- **The announced bit of a value-bearing return.** A return of `v` carries an
`n − f` `VOTE v` receipt quorum, which refutes an exclude certificate for `v`; so a bound bit
already on record, whose complement is certified, is `v` itself,
and one computed here is `v` by `boundOf`. -/
theorem SpecificationRelation.retBound_eq {s : ImplementationState P.n} {t : SpecState P.n}
    (hR : SpecificationRelation P s t) {i : Fin P.n} {v : Bool} {out : GBCAOutput}
    (hvq : P.n - P.f ≤ s.receivedCount i (.vote (some v)))
    (hout : boundOf s.sent s.F out = v) :
    s.bound.getD (boundOf s.sent s.F out) = v := by
  cases hb : s.bound with
  | none => exact hout
  | some β =>
    refine Option.getD_some.trans ?_
    by_contra hne
    refine not_exclusionCertificate_of_voteQuorum hR.invariant hvq ?_
    have hv : (!β) = v := by
      cases β <;> cases v <;> simp_all
    rw [← hv]
    exact hR.bound_certificate β hb

/-! ### Deriving the spec guards -/

/-- D15 derivation at `retGrade1`/`retGrade0`: `|Valid| > 1` evidence yields the
`f + 1` F-blind genuine-holder support for either bit — its `n − f ≥ f + 1`
`INPUT` receipt quorum for that bit sits at the returner itself. -/
theorem inputSupport_of_bothValid {s : ImplementationState P.n} (hI : Invariant P s)
    {i : Fin P.n} (hv : s.bothValid P i) (b : Bool) : InputSupport P s b := by
  have hfn := P.f_lt_n_sub_f
  exact hI.support_of_input_receipts
    (le_trans (by omega) (ImplementationState.bothValid_le hv b))

/-- Transport an implementation support count to the specification along `call_eq`/`F_eq`: the spec
guards' InputSupport counts (D15). -/
theorem SpecificationRelation.callSupport {s : ImplementationState P.n} {t : SpecState P.n}
    (hR : SpecificationRelation P s t) {b : Bool} (h : InputSupport P s b) :
    P.f + 1 ≤ (Finset.univ.filter (fun id => t.call id = some b ∨ id ∈ t.F)).card := by
  unfold InputSupport at h
  refine le_trans h (Finset.card_le_card fun k hk => ?_)
  rw [Finset.mem_filter] at hk ⊢
  refine ⟨hk.1, ?_⟩
  rw [hR.call_eq, hR.F_eq]
  exact hk.2

/-- D8 quorum derivation: any `n − f` receipt quorum of a message whose correct
senders must hold an input yields the spec's call quorum; corrupted senders
are absorbed into the `∪ F`. -/
theorem quorum_of_messageQuorum {s : ImplementationState P.n} {t : SpecState P.n}
    (hR : SpecificationRelation P s t) {i : Fin P.n} {m : Message}
    (hpart : ∀ j, j ∉ s.F → m ∈ s.sent j → (s.process j).input ≠ none)
    (h : P.n - P.f ≤ s.receivedCount i m) : t.quorum P := by
  unfold SpecState.quorum
  unfold ImplementationState.receivedCount at h
  refine le_trans h (Finset.card_le_card ?_)
  intro k hk
  rw [Finset.mem_filter] at hk
  rw [Finset.mem_union]
  by_cases hkF : k ∈ t.F
  · exact Or.inr hkF
  · refine Or.inl ?_
    rw [Finset.mem_filter]
    have hkF' : k ∉ s.F := by
      rwa [hR.F_eq] at hkF
    refine ⟨Finset.mem_univ _, hkF, ?_⟩
    rw [hR.call_eq]
    exact hpart k hkF' (hR.invariant.received_subset_sent i k _ hk.2)

/-- **Both `bindUnset` guards from the single certificate.** -/
theorem bindUnset_guards {s : ImplementationState P.n} {t : SpecState P.n}
    (hR : SpecificationRelation P s t) {v : Bool} (hq : EchoReceiptQuorum P s v) :
    t.quorum P ∧ P.f + 1 ≤ (Finset.univ.filter (fun id => t.call id = some v ∨ id ∈ t.F)).card := by
  obtain ⟨m, hm⟩ := inputQuorum_of_echoReceiptQuorum hR.invariant hq
  have hfn := P.f_lt_n_sub_f
  refine ⟨quorum_of_messageQuorum hR
    (fun j hj hm' => hR.invariant.input_called j v hj hm') hm, ?_⟩
  exact hR.callSupport (hR.invariant.support_of_input_receipts (le_trans (by omega) hm))

/-- Grade exclusivity, grade 2: an `n − f` `ECHO5 v` receipt quorum rules out a grade-0 lock (the
two `ECHO5` quorums would intersect in a correct process with two different `ECHO5` payloads,
against `echo5_once`). -/
theorem grade_ne_false_of_echo5_quorum {s : ImplementationState P.n} {t : SpecState P.n}
    (hR : SpecificationRelation P s t) {id : Fin P.n} {v : Bool}
    (hcnt : P.n - P.f ≤ s.receivedCount id (.echo5 (some v))) :
    t.grade ≠ some false := by
  intro hg
  obtain ⟨i', hc⟩ := hR.grade0_evidence hg
  obtain ⟨j, hjF, hj1,
    hj2⟩ := ImplementationState.exists_correct_received_of_two_quorums hR.invariant.F_card hcnt hc
  have e1 := hR.invariant.echo5_once j (some v) hjF (hR.invariant.received_subset_sent id j _ hj1)
  have e2 := hR.invariant.echo5_once j none hjF (hR.invariant.received_subset_sent i' j _ hj2)
  rw [e1] at e2
  exact absurd (Option.some.inj e2) (by simp)

/-- Grade exclusivity, grade 0: an `n − f` `ECHO5 ⊥` receipt quorum rules out a grade-2 lock. -/
theorem grade_ne_true_of_echo5Bot_quorum {s : ImplementationState P.n} {t : SpecState P.n}
    (hR : SpecificationRelation P s t) {id : Fin P.n}
    (hcnt : P.n - P.f ≤ s.receivedCount id (.echo5 none)) :
    t.grade ≠ some true := by
  intro hg
  obtain ⟨v', i', hc⟩ := hR.grade2_evidence hg
  obtain ⟨j, hjF, hj1,
    hj2⟩ := ImplementationState.exists_correct_received_of_two_quorums hR.invariant.F_card hc hcnt
  have e1 := hR.invariant.echo5_once j (some v') hjF (hR.invariant.received_subset_sent i' j _ hj1)
  have e2 := hR.invariant.echo5_once j none hjF (hR.invariant.received_subset_sent id j _ hj2)
  rw [e1] at e2
  exact absurd (Option.some.inj e2) (by simp)

/-! ### Answering a return by an exclusion run -/

/-- A `Finset Bool` that omits both `v` and `!v` omits everything. -/
theorem excluded_empty_of_both {d : Finset Bool} {v : Bool}
    (h1 : v ∉ d) (h2 : (!v) ∉ d) : d = ∅ := by
  ext b; cases b <;> cases v <;> simp_all

/-- A `Finset Bool` that holds `!v` and not `v` is the singleton `{!v}`. -/
theorem excluded_eq_singleton {d : Finset Bool} {v : Bool}
    (h1 : v ∉ d) (h2 : (!v) ∈ d) : d = {!v} := by
  ext b; cases b <;> cases v <;> simp_all

/-- `bindUnset (!v) ; retGrade2 v` from an all-alive state (`excluded = ∅`, the
`bindUnset` guard). The `bindUnset (!v)` support guard reads `some (!(!v))`; `Bool.not_not` rewrites
it to `hw`'s `some v`. The exclusion of `!v` is also
the announced bit's guard, so the return announces `v`. -/
theorem excludeThenRetGrade2_run {r : ℕ} {t : SpecState P.n} {id : Fin P.n} {v : Bool}
    (hq : t.quorum P)
    (hw : P.f + 1 ≤ (Finset.univ.filter
      (fun k => t.call k = some v ∨ k ∈ t.F)).card)
    (hlive : v ∉ t.excluded) (hd0 : t.excluded = ∅)
    (hg : t.grade = none ∨ t.grade = some true)
    (hr : t.ret id = false) :
    (specInst P r).weakLStep t (.retG r id (.grade2 v) v)
      { t with
        excluded := insert (!v) t.excluded, grade := some true,
               ret := Function.update t.ret id true } := by
  have h1 : (specInst P r).LStep t Silent.τ { t with excluded := insert (!v) t.excluded } :=
    Step.bindUnset t (!v) hq (by simpa only [Bool.not_not] using hw) hd0
  have h2 : (specInst P r).LStep { t with excluded := insert (!v) t.excluded }
      (.retG r id (.grade2 v) v)
      { t with
        excluded := insert (!v) t.excluded, grade := some true,
               ret := Function.update t.ret id true } := by
    refine Step.retGrade2 { t with excluded := insert (!v) t.excluded } id v v ?_
      (Finset.mem_insert_self (!v) t.excluded)
      (Finset.mem_insert_self (!v) t.excluded) hg hr
    rw [Finset.mem_insert]
    rintro (hv | hv)
    · cases v <;> exact absurd hv (by decide)
    · exact hlive hv
  exact weakLStep_tauThen h1 h2 (by simp)

/-- `bindUnset (!v) ; retGrade1 v`: the same run with the dissent count in
place of the grade guard. -/
theorem excludeThenRetGrade1_run {r : ℕ} {t : SpecState P.n} {id : Fin P.n} {v : Bool}
    (hq : t.quorum P)
    (hw : P.f + 1 ≤ (Finset.univ.filter (fun k => t.call k = some v ∨ k ∈ t.F)).card)
    (hlive : v ∉ t.excluded) (hd0 : t.excluded = ∅)
    (hd : P.f + 1 ≤ (Finset.univ.filter (fun k => t.call k = some (!v) ∨ k ∈ t.F)).card)
    (hr : t.ret id = false) :
    (specInst P r).weakLStep t (.retG r id (.grade1 v) v)
    { t with excluded := insert (!v) t.excluded, ret := Function.update t.ret id true } := by
  have h1 : (specInst P r).LStep t Silent.τ { t with excluded := insert (!v) t.excluded } :=
    Step.bindUnset t (!v) hq (by simpa only [Bool.not_not] using hw) hd0
  have h2 : (specInst P r).LStep { t with excluded := insert (!v) t.excluded }
      (.retG r id (.grade1 v) v)
      { t with
        excluded := insert (!v) t.excluded,
               ret := Function.update t.ret id true } := by
    refine Step.retGrade1 { t with excluded := insert (!v) t.excluded } id v v ?_
      (Finset.mem_insert_self (!v) t.excluded)
      (Finset.mem_insert_self (!v) t.excluded) hd hr
    rw [Finset.mem_insert]
    rintro (hv | hv)
    · cases v <;> exact absurd hv (by decide)
    · exact hlive hv
  exact weakLStep_tauThen h1 h2 (by simp)

/-- `bindUnset (!bnd) ; retGrade0` from an all-alive state (`excluded = ∅`, the
`bindUnset` guard): the exclusion of `!bnd` is the announced bit's guard, so the
return announces `bnd`. -/
theorem excludeThenRetGrade0_run {r : ℕ} {t : SpecState P.n} {id : Fin P.n} {bnd : Bool}
    (hq : t.quorum P)
    (hw : P.f + 1 ≤ (Finset.univ.filter
      (fun k => t.call k = some bnd ∨ k ∈ t.F)).card)
    (hd0 : t.excluded = ∅)
    (hwT : P.f + 1 ≤ (Finset.univ.filter
      (fun k => t.call k = some true ∨ k ∈ t.F)).card)
    (hwF : P.f + 1 ≤ (Finset.univ.filter
      (fun k => t.call k = some false ∨ k ∈ t.F)).card)
    (hg : t.grade = none ∨ t.grade = some false)
    (hr : t.ret id = false) :
    (specInst P r).weakLStep t (.retG r id .grade0 bnd)
      { t with
        excluded := insert (!bnd) t.excluded, grade := some false,
               ret := Function.update t.ret id true } := by
  have h1 : (specInst P r).LStep t Silent.τ
      { t with excluded := insert (!bnd) t.excluded } :=
    Step.bindUnset t (!bnd) hq (by simpa only [Bool.not_not] using hw) hd0
  have h2 : (specInst P r).LStep { t with excluded := insert (!bnd) t.excluded }
      (.retG r id .grade0 bnd)
      { t with
        excluded := insert (!bnd) t.excluded, grade := some false,
               ret := Function.update t.ret id true } :=
    Step.retGrade0 { t with excluded := insert (!bnd) t.excluded } id bnd
      (Finset.mem_insert_self (!bnd) t.excluded) hwT hwF hg hr
  exact weakLStep_tauThen h1 h2 (by simp)

end GBCA.ByABDY
end ABA
end PLTS
