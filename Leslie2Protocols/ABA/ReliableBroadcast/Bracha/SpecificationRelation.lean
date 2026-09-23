/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sathiya / Claude
-/

import Leslie2Protocols.ABA.ReliableBroadcast.Bracha.Invariant
import Leslie2Protocols.Framework.FamilySimulation

/-!
# The relation between the reliable-broadcast instance and its specification

`BRB.SpecificationRelation P ldr s t` relates a state of the reliable-broadcast instance to a
state of the broadcast specification with the same leader. The call records, the return flags and
the corrupted sets agree, the instance invariant holds at `s`, and `val_certificate` bounds the
specification's committed value by `BRB.EchoCertificate`.

`specificationRelation_init` holds the relation at the two initial states, and
`specificationRelation_corrupt` carries it across a corruption of both systems at once, which is
the shape the family lifting consumes.

`specificationRelation_row` is the matching, one transition of `BRB.BrachaAlgorithm` at a time.
The internal transitions stutter. The call and corruption are answered by the specification's own
transitions. A return is answered by `ret` alone when `val` is already committed, the certificates
identifying the two values, and by the two-step run `commit ; ret` when it is not, with `commit`'s
guard discharged by `input_of_echoCertificate` under a correct leader and by membership in the
corrupted set otherwise.
-/

namespace PLTS
namespace ABA
namespace BRB

variable {M : Type} [DecidableEq M] {P : Parameters} {ldr : Fin P.n}

/-! ### The relation -/

/-- The relation the reliable-broadcast refinement runs along. `val_certificate` bounds the
specification's committed value by the certificate; the other clauses are projections. -/
structure SpecificationRelation (P : Parameters) (ldr : Fin P.n) (s : BrachaState P.n M)
    (t : SpecState P.n M) : Prop where
  /-- The implementation invariant. -/
  invariant : Invariant P ldr s
  /-- The call records agree. -/
  input_eq : t.input = (s.process ldr).input
  /-- The return flags agree. -/
  ret_eq : ∀ id, t.ret id = (s.process id).returned
  /-- The corrupted sets agree. -/
  F_eq : t.F = s.F
  /-- A committed value is echo-certified. -/
  val_certificate : ∀ m, t.val = some m → EchoCertificate P s m

/-- The relation holds initially. -/
theorem specificationRelation_init :
    SpecificationRelation P ldr (BrachaState.initial P.n M) (SpecState.initial P.n M) := by
  refine ⟨Invariant.initial, ?_, ?_, ?_, ?_⟩ <;>
    simp [BrachaState.initial, SpecState.initial, ProcessRecord.initial]

/-- **Broadcast compatibility**: the relation is preserved by corrupting both systems at once — the
abstract state the family lifting consumes. -/
theorem specificationRelation_corrupt {s : BrachaState P.n M} {t : SpecState P.n M}
    (hR : SpecificationRelation P ldr s t) (id : Fin P.n) :
    SpecificationRelation P ldr (s.corrupt P id) (t.corrupt P id) := by
  refine ⟨hR.invariant.step (BrachaAlgorithm.fail s id) (by rw [PMF.mem_support_pure_iff]),
    ?_, ?_, ?_, ?_⟩
  · rw [corrupt_input, InstanceState.corrupt_process]
    exact hR.input_eq
  · intro k
    rw [corrupt_ret, InstanceState.corrupt_process]
    exact hR.ret_eq k
  · rw [SpecState.corrupt_F, InstanceState.corrupt_F, hR.F_eq]
  · intro m hm
    rw [corrupt_val] at hm
    rw [echoCertificate_corrupt]
    exact hR.val_certificate m hm

/-- **The relation across one transition**: every transition of `BrachaAlgorithm` at a related
pair is answered by a weak run of the specification instance, and the answer is again related. The
internal transitions stutter; `call` and `fail` are answered by the specification's own
transitions; `ret id m` is answered by `ret` alone when `val` is already committed, and by the
two-step run `commit ; ret` when it is not. -/
theorem specificationRelation_row (P : Parameters) (ldr : Fin P.n) (q₁ : BrachaState P.n M)
    (q₂ : SpecState P.n M) (hR : SpecificationRelation P ldr q₁ q₂) (l : Label P.n M)
    (μ : PMF (BrachaState P.n M)) (hstep : BrachaAlgorithm P ldr q₁ l μ)
    (q₁' : BrachaState P.n M) (hq₁' : q₁' ∈ μ.support) :
    ∃ q₂', ((l = Silent.τ ∧ (specInst P ldr M).weakLSilent q₂ q₂') ∨
      (¬ l = Silent.τ ∧ (specInst P ldr M).weakLStep q₂ l q₂')) ∧
      SpecificationRelation P ldr q₁' q₂' := by
  have hInv' := hR.invariant.step hstep hq₁'
  cases hstep with
  | call m h =>
    rw [PMF.mem_support_pure_iff] at hq₁'
    subst hq₁'
    refine ⟨{ q₂ with input := some m },
      Or.inr ⟨by simp, System.weakLStep_of_step (by simp)
        (Step.call q₂ m (by rw [hR.input_eq]; exact h))⟩, hInv', ?_, ?_, ?_, ?_⟩
    · simp
    · intro k
      by_cases hkl : k = ldr
      · subst hkl
        rw [InstanceState.multicast_process, InstanceState.setProcess_process_self]
        exact hR.ret_eq k
      · rw [InstanceState.multicast_process, InstanceState.setProcess_process_ne _ _ _ hkl]
        exact hR.ret_eq k
    · simpa using hR.F_eq
    · intro m' hm'
      rw [echoCertificate_multicast, echoCertificate_setProcess]
      exact hR.val_certificate m' hm'
  | callLoop m =>
    rw [PMF.mem_support_pure_iff] at hq₁'
    subst hq₁'
    exact ⟨q₂, Or.inr ⟨by simp, System.weakLStep_of_step (by simp)
      (Step.callLoop q₂ m)⟩, hR⟩
  | deliver i j m h =>
    rw [PMF.mem_support_pure_iff] at hq₁'
    subst hq₁'
    refine ⟨q₂, Or.inl ⟨rfl, System.weakLSilent_refl _ q₂⟩,
      hInv', ?_, ?_, ?_, ?_⟩
    · rw [InstanceState.receiveMessage_process]
      exact hR.input_eq
    · intro k
      rw [InstanceState.receiveMessage_process]
      exact hR.ret_eq k
    · simpa using hR.F_eq
    · intro m' hm'
      exact (hR.val_certificate m' hm').receiveMessage i j m
  | echo j m hrecv hsend =>
    rw [PMF.mem_support_pure_iff] at hq₁'
    subst hq₁'
    refine ⟨q₂, Or.inl ⟨rfl, System.weakLSilent_refl _ q₂⟩,
      hInv', ?_, ?_, ?_, ?_⟩
    · by_cases hkl : ldr = j
      · rw [InstanceState.multicast_process, hkl, InstanceState.setProcess_process_self]
        rw [hR.input_eq, hkl]
      · rw [InstanceState.multicast_process, InstanceState.setProcess_process_ne _ _ _ hkl]
        exact hR.input_eq
    · intro k
      by_cases hkl : k = j
      · subst hkl
        rw [InstanceState.multicast_process, InstanceState.setProcess_process_self]
        exact hR.ret_eq k
      · rw [InstanceState.multicast_process, InstanceState.setProcess_process_ne _ _ _ hkl]
        exact hR.ret_eq k
    · simpa using hR.F_eq
    · intro m' hm'
      rw [echoCertificate_multicast, echoCertificate_setProcess]
      exact hR.val_certificate m' hm'
  | voteQuorum j m hcnt hsend =>
    rw [PMF.mem_support_pure_iff] at hq₁'
    subst hq₁'
    refine ⟨q₂, Or.inl ⟨rfl, System.weakLSilent_refl _ q₂⟩,
      hInv', ?_, ?_, ?_, ?_⟩
    · by_cases hkl : ldr = j
      · rw [InstanceState.multicast_process, hkl, InstanceState.setProcess_process_self]
        rw [hR.input_eq, hkl]
      · rw [InstanceState.multicast_process, InstanceState.setProcess_process_ne _ _ _ hkl]
        exact hR.input_eq
    · intro k
      by_cases hkl : k = j
      · subst hkl
        rw [InstanceState.multicast_process, InstanceState.setProcess_process_self]
        exact hR.ret_eq k
      · rw [InstanceState.multicast_process, InstanceState.setProcess_process_ne _ _ _ hkl]
        exact hR.ret_eq k
    · simpa using hR.F_eq
    · intro m' hm'
      rw [echoCertificate_multicast, echoCertificate_setProcess]
      exact hR.val_certificate m' hm'
  | voteAmplification j m hcnt hsend =>
    rw [PMF.mem_support_pure_iff] at hq₁'
    subst hq₁'
    refine ⟨q₂, Or.inl ⟨rfl, System.weakLSilent_refl _ q₂⟩,
      hInv', ?_, ?_, ?_, ?_⟩
    · by_cases hkl : ldr = j
      · rw [InstanceState.multicast_process, hkl, InstanceState.setProcess_process_self]
        rw [hR.input_eq, hkl]
      · rw [InstanceState.multicast_process, InstanceState.setProcess_process_ne _ _ _ hkl]
        exact hR.input_eq
    · intro k
      by_cases hkl : k = j
      · subst hkl
        rw [InstanceState.multicast_process, InstanceState.setProcess_process_self]
        exact hR.ret_eq k
      · rw [InstanceState.multicast_process, InstanceState.setProcess_process_ne _ _ _ hkl]
        exact hR.ret_eq k
    · simpa using hR.F_eq
    · intro m' hm'
      rw [echoCertificate_multicast, echoCertificate_setProcess]
      exact hR.val_certificate m' hm'
  | byzantine j m hj =>
    rw [PMF.mem_support_pure_iff] at hq₁'
    subst hq₁'
    refine ⟨q₂, Or.inl ⟨rfl, System.weakLSilent_refl _ q₂⟩,
      hInv', ?_, ?_, ?_, ?_⟩
    · rw [InstanceState.multicast_process]
      exact hR.input_eq
    · intro k
      rw [InstanceState.multicast_process]
      exact hR.ret_eq k
    · simpa using hR.F_eq
    · intro m' hm'
      rw [echoCertificate_multicast]
      exact hR.val_certificate m' hm'
  | ret id m hcnt hr =>
    rw [PMF.mem_support_pure_iff] at hq₁'
    subst hq₁'
    have hcert : EchoCertificate P q₁ m := echoCertificate_of_vote_quorum hR.invariant hcnt
    have hretQ : q₂.ret id = false := by
      rw [hR.ret_eq id]; exact hr
    have hRel : ∀ t' : SpecState P.n M, t'.val = some m →
        t'.input = q₂.input → t'.F = q₂.F →
        t'.ret = q₂.ret →
        SpecificationRelation P ldr (q₁.setProcess id { q₁.process id with returned := true })
          { t' with ret := Function.update t'.ret id true } := by
      intro t' hval hinput hF hret
      refine ⟨hInv', ?_, ?_, ?_, ?_⟩
      · rw [hinput]
        by_cases hkl : ldr = id
        · rw [hkl, InstanceState.setProcess_process_self]
          rw [hR.input_eq, hkl]
        · rw [InstanceState.setProcess_process_ne _ _ _ hkl]
          exact hR.input_eq
      · intro k
        by_cases hkl : k = id
        · subst hkl
          rw [InstanceState.setProcess_process_self]
          change Function.update t'.ret k true k = true
          rw [Function.update_self]
        · rw [InstanceState.setProcess_process_ne _ _ _ hkl]
          change Function.update t'.ret id true k = _
          rw [Function.update_of_ne hkl, hret]
          exact hR.ret_eq k
      · rw [InstanceState.setProcess_F]
        rw [hF]
        exact hR.F_eq
      · intro m' hm'
        rw [echoCertificate_setProcess]
        obtain rfl : m = m' := by
          have := hval
          rw [show ({ t' with ret := Function.update t'.ret id true } :
            SpecState P.n M).val = t'.val from rfl] at hm'
          rw [hval] at hm'
          injection hm'
        exact hcert
    cases hval : q₂.val with
    | some m' =>
      obtain rfl : m = m' :=
        echoCertificate_unique hR.invariant hcert (hR.val_certificate m' hval)
      refine ⟨{ q₂ with ret := Function.update q₂.ret id true },
        Or.inr ⟨by simp, System.weakLStep_of_step (by simp)
          (Step.ret q₂ id m hval hretQ)⟩, ?_⟩
      exact hRel q₂ hval rfl rfl rfl
    | none =>
      have hcommit : (specInst P ldr M).LStep q₂ Silent.τ
          { q₂ with val := some m } := by
        refine Step.commit q₂ m hval ?_
        by_cases hldr : ldr ∈ q₁.F
        · exact Or.inl (by rw [hR.F_eq]; exact hldr)
        · exact Or.inr (by
            rw [hR.input_eq]
            exact input_of_echoCertificate hR.invariant hldr hcert)
      have hret : (specInst P ldr M).LStep { q₂ with val := some m }
          (.ret id m)
          { q₂ with val := some m, ret := Function.update q₂.ret id true } :=
        Step.ret _ id m rfl hretQ
      refine ⟨_, Or.inr ⟨by simp, weakLStep_tauThen hcommit hret (by simp)⟩, ?_⟩
      exact hRel { q₂ with val := some m } rfl rfl rfl rfl
  | fail id =>
    rw [PMF.mem_support_pure_iff] at hq₁'
    subst hq₁'
    exact ⟨q₂.corrupt P id, Or.inr ⟨by simp, System.weakLStep_of_step (by simp)
      (Step.fail q₂ id)⟩, specificationRelation_corrupt hR id⟩

end BRB
end ABA
end PLTS
