/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sathiya / Claude
-/

import Leslie2Protocols.ABA.Gather.Ideal

/-!
# The core of the composed gather instance over broadcast specifications

The invariant of `Gather.idealInst` (`ABA/Gather/Sub.lean`), stated over the
composition's state through the views `ga`, `brbIn`, `brbBind`, `core`, and the
argument that `coreOfNet` is a bound core. At every state at which some process
outside `F` holds a committed `BIND` payload, `coreOfNet` has at least `n − f`
entries, its entries are committed input entries, and it lies below the
committed `BIND` payload of every process outside `F`.

The counting is over one incidence on the gather network state, so the lemmas
that read that state alone — `mem_honest`, `mem_dominatedBy`,
`honest_filter_dominatedBy`, `sum_dominatedBy` — are the ones of
`ABA/Gather/Vocabulary.lean`, applied to `netOf`.

## The stores

A gather program reads what a broadcast instance returned to it out of its own
record. The clauses `delivIn_val` and `delivBind_val` carry a store entry back
to the commitment that wrote it: they are established at the `inRet` and
`bindRet` rows, whose guards are the broadcast specification's `val = some v`,
and they survive because a committed value is written once.

## The call records

The composition answers `call id x` on four rows and the call loop is a label
of its own, so an input instance may record a payload on a label at which the
gather record stands still. The provenance of a commitment therefore reads the
input instance's own call record, which is what `inVal_prov` states.
-/

namespace PLTS
namespace ABA
namespace Gather

variable {X : Type} [DecidableEq X] {P : Params}

/-- The gather network state of the composition, read as an instance state over
the gather record. The core and the incidence read the sent sets and the
corrupted set, and no local record. -/
def netOf {n : ℕ} (s : IdealState n X) : SubState n (PRec n X) (GaMsg n X) :=
  ((fun _ => LocalState.initial n (GaMsg n X) (PRec.initial n X)), (ga s).2)

omit [DecidableEq X] in
@[simp] theorem netOf_sent {n : ℕ} (s : IdealState n X) :
    (netOf s).sent = (ga s).sent := rfl

omit [DecidableEq X] in
@[simp] theorem netOf_F {n : ℕ} (s : IdealState n X) : (netOf s).F = (ga s).F := rfl

omit [DecidableEq X] in
/-- The core of the composition's gather network state. -/
theorem coreOf_netOf (s : IdealState P.n X) :
    coreOf P (netOf s) = coreOfNet P (ga s).2 := rfl

/-! ### The conformance clauses -/

/-- The conformance clauses. The `*_conf` clauses tie an honest sender's sent to
its write-once field, the `*_backed` clauses tie the fields to the receipts that
justified them, the store clauses tie a program's store to the commitment that
wrote it, and the provenance clauses are the broadcast commit guards, recorded
per instance. -/
structure IdealConf (P : Params) (s : IdealState P.n X) : Prop where
  /-- The corruption budget. -/
  F_card : (ga s).F.card ≤ P.f
  /-- The input instances' corrupted sets are in lockstep with the gather
  network state's. -/
  F_in_eq : ∀ k, (brbIn s k).F = (ga s).F
  /-- The bind instances' corrupted sets are in lockstep with the gather
  network state's. -/
  F_bind_eq : ∀ k, (brbBind s k).F = (ga s).F
  /-- Delivered messages were multicast. -/
  recv_sub : ∀ i k, (ga s).recv i k ⊆ (ga s).sent k
  /-- A value in a program's input store is the committed value of the instance
  that returned it. -/
  delivIn_val : ∀ j k v, ((ga s).proc j).delivIn k = some v → (brbIn s k).val = some v
  /-- A payload in a program's bind store is the committed payload of the
  instance that returned it. -/
  delivBind_val : ∀ j q U, ((ga s).proc j).delivBind q = some U →
    (brbBind s q).val = some U
  /-- A committed input entry of an honest process is the payload its input
  instance recorded. -/
  inVal_prov : ∀ k v, (brbIn s k).val = some v →
    k ∈ (ga s).F ∨ (brbIn s k).input = some v
  /-- A committed bind payload of an honest process is the payload its bind
  instance recorded. -/
  bindVal_prov : ∀ k U, (brbBind s k).val = some U →
    k ∈ (ga s).F ∨ (brbBind s k).input = some U
  /-- An honest sender's sent `ECHO` matches its write-once field. -/
  echo_conf : ∀ j ∉ (ga s).F, ∀ A, GaMsg.echo A ∈ (ga s).sent j →
    ((ga s).proc j).sentEcho = some A
  /-- An honest echo payload has at least `n − f` entries. -/
  echo_card : ∀ j ∉ (ga s).F, ∀ A, ((ga s).proc j).sentEcho = some A →
    P.n - P.f ≤ A.card
  /-- An honest sender's sent `VOTE` matches its write-once field. -/
  vote_conf : ∀ j ∉ (ga s).F, ∀ W, GaMsg.vote W ∈ (ga s).sent j →
    ((ga s).proc j).sentVote = some W
  /-- An honest vote is backed by `n − f` senders' echo payloads, each contained
  in it. -/
  vote_backed : ∀ j ∉ (ga s).F, ∀ W, ((ga s).proc j).sentVote = some W →
    ∃ Q : Finset (Fin P.n), P.n - P.f ≤ Q.card ∧
      ∀ q ∈ Q, ∃ A, GaMsg.echo A ∈ (ga s).recv j q ∧ A ⊆ W
  /-- An honest contributed bind payload is backed by `n − f` senders' vote
  payloads, each contained in it. -/
  bind_backed : ∀ j ∉ (ga s).F, ∀ U, (brbBind s j).input = some U →
    ∃ Q : Finset (Fin P.n), P.n - P.f ≤ Q.card ∧
      ∀ q ∈ Q, ∃ W, GaMsg.vote W ∈ (ga s).recv j q ∧ W ⊆ U

/-- The conformance clauses hold initially. -/
theorem IdealConf.initial : IdealConf P ((idealInst P X).init) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [ga, brbIn, brbBind, ProcRec.initial, PRec.initial, BRB.SpecState.initial,
      GaNetState.initial, SubState.proc, SubState.sent, SubState.recv, SubState.F]

/-- The conformance clauses are preserved by every step. -/
theorem IdealConf.step {s : IdealState P.n X} {l : Lab P.n X}
    {μ : PMF (IdealState P.n X)} (hInv : IdealConf P s) (hstep : IdealStep P s l μ)
    {s' : IdealState P.n X} (hs' : s' ∈ μ.support) : IdealConf P s' := by
  cases hstep with
  | call id x h hb =>
    rw [PMF.mem_support_pure_iff] at hs'
    subst hs'
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals dsimp only [ga_setBrbIn, ga_setGa, brbIn_setBrbIn, brbBind_setBrbIn,
      brbBind_setGa]
    · exact hInv.F_card
    · intro k
      by_cases hk : k = id
      · subst hk
        rw [Function.update_self]
        exact hInv.F_in_eq k
      · rw [Function.update_of_ne hk]
        exact hInv.F_in_eq k
    · exact hInv.F_bind_eq
    · intro i k m hm
      rw [SubState.setProc_recv] at hm
      rw [SubState.setProc_sent]
      exact hInv.recv_sub i k hm
    · intro j k v hv
      have hv0 : ((ga s).proc j).delivIn k = some v := by
        by_cases hj : j = id
        · subst hj
          rw [SubState.setProc_proc_self] at hv
          exact hv
        · rw [SubState.setProc_proc_ne _ _ _ hj] at hv
          exact hv
      by_cases hk : k = id
      · subst hk
        rw [Function.update_self]
        exact hInv.delivIn_val j k v hv0
      · rw [Function.update_of_ne hk]
        exact hInv.delivIn_val j k v hv0
    · intro j q U hU
      by_cases hj : j = id
      · subst hj
        rw [SubState.setProc_proc_self] at hU
        exact hInv.delivBind_val j q U hU
      · rw [SubState.setProc_proc_ne _ _ _ hj] at hU
        exact hInv.delivBind_val j q U hU
    · intro k v hv
      by_cases hk : k = id
      · subst hk
        rw [Function.update_self] at hv ⊢
        rcases hInv.inVal_prov k v hv with hF | hin
        · exact Or.inl hF
        · rw [hb] at hin
          exact absurd hin (by simp)
      · rw [Function.update_of_ne hk] at hv ⊢
        exact hInv.inVal_prov k v hv
    · exact hInv.bindVal_prov
    · intro j hj A hA
      rw [SubState.setProc_sent] at hA
      have hpre := hInv.echo_conf j hj A hA
      by_cases hk : j = id
      · subst hk
        rw [SubState.setProc_proc_self]
        exact hpre
      · rw [SubState.setProc_proc_ne _ _ _ hk]
        exact hpre
    · intro j hj A hA
      by_cases hk : j = id
      · subst hk
        rw [SubState.setProc_proc_self] at hA
        exact hInv.echo_card j hj A hA
      · rw [SubState.setProc_proc_ne _ _ _ hk] at hA
        exact hInv.echo_card j hj A hA
    · intro j hj W hW
      rw [SubState.setProc_sent] at hW
      have hpre := hInv.vote_conf j hj W hW
      by_cases hk : j = id
      · subst hk
        rw [SubState.setProc_proc_self]
        exact hpre
      · rw [SubState.setProc_proc_ne _ _ _ hk]
        exact hpre
    · intro j hj W hW
      rw [SubState.setProc_recv]
      by_cases hk : j = id
      · subst hk
        rw [SubState.setProc_proc_self] at hW
        exact hInv.vote_backed j hj W hW
      · rw [SubState.setProc_proc_ne _ _ _ hk] at hW
        exact hInv.vote_backed j hj W hW
    · intro j hj U hU
      rw [SubState.setProc_recv]
      exact hInv.bind_backed j hj U hU
  | callSpecLoop id x h =>
    rw [PMF.mem_support_pure_iff] at hs'
    subst hs'
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals dsimp only [ga_setGa, brbIn_setGa, brbBind_setGa]
    · exact hInv.F_card
    · exact hInv.F_in_eq
    · exact hInv.F_bind_eq
    · intro i k m hm
      rw [SubState.setProc_recv] at hm
      rw [SubState.setProc_sent]
      exact hInv.recv_sub i k hm
    · intro j k v hv
      by_cases hj : j = id
      · subst hj
        rw [SubState.setProc_proc_self] at hv
        exact hInv.delivIn_val j k v hv
      · rw [SubState.setProc_proc_ne _ _ _ hj] at hv
        exact hInv.delivIn_val j k v hv
    · intro j q U hU
      by_cases hj : j = id
      · subst hj
        rw [SubState.setProc_proc_self] at hU
        exact hInv.delivBind_val j q U hU
      · rw [SubState.setProc_proc_ne _ _ _ hj] at hU
        exact hInv.delivBind_val j q U hU
    · exact hInv.inVal_prov
    · exact hInv.bindVal_prov
    · intro j hj A hA
      rw [SubState.setProc_sent] at hA
      have hpre := hInv.echo_conf j hj A hA
      by_cases hk : j = id
      · subst hk
        rw [SubState.setProc_proc_self]
        exact hpre
      · rw [SubState.setProc_proc_ne _ _ _ hk]
        exact hpre
    · intro j hj A hA
      by_cases hk : j = id
      · subst hk
        rw [SubState.setProc_proc_self] at hA
        exact hInv.echo_card j hj A hA
      · rw [SubState.setProc_proc_ne _ _ _ hk] at hA
        exact hInv.echo_card j hj A hA
    · intro j hj W hW
      rw [SubState.setProc_sent] at hW
      have hpre := hInv.vote_conf j hj W hW
      by_cases hk : j = id
      · subst hk
        rw [SubState.setProc_proc_self]
        exact hpre
      · rw [SubState.setProc_proc_ne _ _ _ hk]
        exact hpre
    · intro j hj W hW
      rw [SubState.setProc_recv]
      by_cases hk : j = id
      · subst hk
        rw [SubState.setProc_proc_self] at hW
        exact hInv.vote_backed j hj W hW
      · rw [SubState.setProc_proc_ne _ _ _ hk] at hW
        exact hInv.vote_backed j hj W hW
    · intro j hj U hU
      rw [SubState.setProc_recv]
      exact hInv.bind_backed j hj U hU
  | callProcLoop id x hb =>
    rw [PMF.mem_support_pure_iff] at hs'
    subst hs'
    refine ⟨hInv.F_card, ?_, hInv.F_bind_eq, hInv.recv_sub, ?_, hInv.delivBind_val, ?_,
      hInv.bindVal_prov, hInv.echo_conf, hInv.echo_card, hInv.vote_conf,
      hInv.vote_backed, hInv.bind_backed⟩
    all_goals dsimp only [ga_setBrbIn, brbIn_setBrbIn]
    · intro k
      by_cases hk : k = id
      · subst hk
        rw [Function.update_self]
        exact hInv.F_in_eq k
      · rw [Function.update_of_ne hk]
        exact hInv.F_in_eq k
    · intro j k v hv
      by_cases hk : k = id
      · subst hk
        rw [Function.update_self]
        exact hInv.delivIn_val j k v hv
      · rw [Function.update_of_ne hk]
        exact hInv.delivIn_val j k v hv
    · intro k v hv
      by_cases hk : k = id
      · subst hk
        rw [Function.update_self] at hv ⊢
        rcases hInv.inVal_prov k v hv with hF | hin
        · exact Or.inl hF
        · rw [hb] at hin
          exact absurd hin (by simp)
      · rw [Function.update_of_ne hk] at hv ⊢
        exact hInv.inVal_prov k v hv
  | callLoop id x =>
    rw [PMF.mem_support_pure_iff] at hs'
    subst hs'
    exact hInv
  | commitIn k v hv hm =>
    rw [PMF.mem_support_pure_iff] at hs'
    subst hs'
    refine ⟨hInv.F_card, ?_, hInv.F_bind_eq, hInv.recv_sub, ?_, hInv.delivBind_val, ?_,
      hInv.bindVal_prov, hInv.echo_conf, hInv.echo_card, hInv.vote_conf,
      hInv.vote_backed, hInv.bind_backed⟩
    all_goals dsimp only [ga_setBrbIn, brbIn_setBrbIn]
    · intro k'
      by_cases hk : k' = k
      · subst hk
        rw [Function.update_self]
        exact hInv.F_in_eq k'
      · rw [Function.update_of_ne hk]
        exact hInv.F_in_eq k'
    · intro j k' v' hv'
      by_cases hk : k' = k
      · subst hk
        have hold := hInv.delivIn_val j k' v' hv'
        rw [hv] at hold
        exact absurd hold (by simp)
      · rw [Function.update_of_ne hk]
        exact hInv.delivIn_val j k' v' hv'
    · intro k' v' hv'
      by_cases hk : k' = k
      · subst hk
        rw [Function.update_self] at hv' ⊢
        have hvv : some v = some v' := hv'
        obtain rfl : v = v' := by injection hvv
        rcases hm with hF | hin
        · exact Or.inl (hInv.F_in_eq k' ▸ hF)
        · exact Or.inr hin
      · rw [Function.update_of_ne hk] at hv' ⊢
        exact hInv.inVal_prov k' v' hv'
  | commitBind q U hv hm =>
    rw [PMF.mem_support_pure_iff] at hs'
    subst hs'
    refine ⟨hInv.F_card, hInv.F_in_eq, ?_, hInv.recv_sub, hInv.delivIn_val, ?_,
      hInv.inVal_prov, ?_, hInv.echo_conf, hInv.echo_card, hInv.vote_conf,
      hInv.vote_backed, ?_⟩
    all_goals dsimp only [ga_setBrbBind, brbBind_setBrbBind]
    · intro q'
      by_cases hq : q' = q
      · subst hq
        rw [Function.update_self]
        exact hInv.F_bind_eq q'
      · rw [Function.update_of_ne hq]
        exact hInv.F_bind_eq q'
    · intro j q' U' hU'
      by_cases hq : q' = q
      · subst hq
        have hold := hInv.delivBind_val j q' U' hU'
        rw [hv] at hold
        exact absurd hold (by simp)
      · rw [Function.update_of_ne hq]
        exact hInv.delivBind_val j q' U' hU'
    · intro q' U' hU'
      by_cases hq : q' = q
      · subst hq
        rw [Function.update_self] at hU' ⊢
        have hUU : some U = some U' := hU'
        obtain rfl : U = U' := by injection hUU
        rcases hm with hF | hin
        · exact Or.inl (hInv.F_bind_eq q' ▸ hF)
        · exact Or.inr hin
      · rw [Function.update_of_ne hq] at hU' ⊢
        exact hInv.bindVal_prov q' U' hU'
    · intro j hj U' hU'
      by_cases hq : j = q
      · subst hq
        rw [Function.update_self] at hU'
        exact hInv.bind_backed j hj U' hU'
      · rw [Function.update_of_ne hq] at hU'
        exact hInv.bind_backed j hj U' hU'
  | deliver i j m h =>
    rw [PMF.mem_support_pure_iff] at hs'
    subst hs'
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals dsimp only [ga_setGa, brbIn_setGa, brbBind_setGa]
    · exact hInv.F_card
    · exact hInv.F_in_eq
    · exact hInv.F_bind_eq
    · intro i' k m' hm'
      rw [SubState.mem_recvMsg_recv] at hm'
      rw [SubState.recvMsg_sent]
      rcases hm' with ⟨-, rfl, rfl⟩ | hold
      · exact h
      · exact hInv.recv_sub i' k hold
    · intro j' k v hv
      rw [SubState.recvMsg_proc] at hv
      exact hInv.delivIn_val j' k v hv
    · intro j' q U hU
      rw [SubState.recvMsg_proc] at hU
      exact hInv.delivBind_val j' q U hU
    · exact hInv.inVal_prov
    · exact hInv.bindVal_prov
    · intro j' hj A hA
      rw [SubState.recvMsg_sent] at hA
      rw [SubState.recvMsg_proc]
      exact hInv.echo_conf j' hj A hA
    · intro j' hj A hA
      rw [SubState.recvMsg_proc] at hA
      exact hInv.echo_card j' hj A hA
    · intro j' hj W hW
      rw [SubState.recvMsg_sent] at hW
      rw [SubState.recvMsg_proc]
      exact hInv.vote_conf j' hj W hW
    · intro j' hj W hW
      rw [SubState.recvMsg_proc] at hW
      obtain ⟨Q, hQc, hQ⟩ := hInv.vote_backed j' hj W hW
      exact ⟨Q, hQc, fun q hq => by
        obtain ⟨A, hA, hAW⟩ := hQ q hq
        exact ⟨A, SubState.mem_recvMsg_recv.mpr (Or.inr hA), hAW⟩⟩
    · intro j' hj U hU
      obtain ⟨Q, hQc, hQ⟩ := hInv.bind_backed j' hj U hU
      exact ⟨Q, hQc, fun q hq => by
        obtain ⟨W, hW, hWU⟩ := hQ q hq
        exact ⟨W, SubState.mem_recvMsg_recv.mpr (Or.inr hW), hWU⟩⟩
  | echo j A hin happ hcard hsend =>
    rw [PMF.mem_support_pure_iff] at hs'
    subst hs'
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals dsimp only [ga_setGa, brbIn_setGa, brbBind_setGa]
    · exact hInv.F_card
    · exact hInv.F_in_eq
    · exact hInv.F_bind_eq
    · intro i k m hm
      simp only [SubState.mcast_recv, SubState.setProc_recv] at hm
      rw [SubState.mem_mcast_sent, SubState.setProc_sent]
      exact Or.inr (hInv.recv_sub i k hm)
    · intro j' k v hv
      rw [SubState.mcast_proc] at hv
      by_cases hk : j' = j
      · subst hk
        rw [SubState.setProc_proc_self] at hv
        exact hInv.delivIn_val j' k v hv
      · rw [SubState.setProc_proc_ne _ _ _ hk] at hv
        exact hInv.delivIn_val j' k v hv
    · intro j' q U hU
      rw [SubState.mcast_proc] at hU
      by_cases hk : j' = j
      · subst hk
        rw [SubState.setProc_proc_self] at hU
        exact hInv.delivBind_val j' q U hU
      · rw [SubState.setProc_proc_ne _ _ _ hk] at hU
        exact hInv.delivBind_val j' q U hU
    · exact hInv.inVal_prov
    · exact hInv.bindVal_prov
    · intro j' hj A' hA'
      rw [SubState.mem_mcast_sent, SubState.setProc_sent] at hA'
      rcases hA' with ⟨rfl, hm'⟩ | hold
      · obtain rfl : A' = A := by injection hm'
        rw [SubState.mcast_proc, SubState.setProc_proc_self]
      · have hpre := hInv.echo_conf j' hj A' hold
        by_cases hk : j' = j
        · subst hk
          rw [hsend] at hpre
          exact absurd hpre (by simp)
        · rw [SubState.mcast_proc, SubState.setProc_proc_ne _ _ _ hk]
          exact hpre
    · intro j' hj A' hA'
      by_cases hk : j' = j
      · subst hk
        rw [SubState.mcast_proc, SubState.setProc_proc_self] at hA'
        obtain rfl : A = A' := by injection hA'
        exact hcard
      · rw [SubState.mcast_proc, SubState.setProc_proc_ne _ _ _ hk] at hA'
        exact hInv.echo_card j' hj A' hA'
    · intro j' hj W hW
      rw [SubState.mem_mcast_sent, SubState.setProc_sent] at hW
      rcases hW with ⟨-, hm'⟩ | hold
      · exact absurd hm' (by simp)
      · have hpre := hInv.vote_conf j' hj W hold
        by_cases hk : j' = j
        · subst hk
          rw [SubState.mcast_proc, SubState.setProc_proc_self]
          exact hpre
        · rw [SubState.mcast_proc, SubState.setProc_proc_ne _ _ _ hk]
          exact hpre
    · intro j' hj W hW
      simp only [SubState.mcast_recv, SubState.setProc_recv]
      by_cases hk : j' = j
      · subst hk
        rw [SubState.mcast_proc, SubState.setProc_proc_self] at hW
        exact hInv.vote_backed j' hj W hW
      · rw [SubState.mcast_proc, SubState.setProc_proc_ne _ _ _ hk] at hW
        exact hInv.vote_backed j' hj W hW
    · intro j' hj U hU
      simp only [SubState.mcast_recv, SubState.setProc_recv]
      exact hInv.bind_backed j' hj U hU
  | vote j U hin happ hQ hsend =>
    rw [PMF.mem_support_pure_iff] at hs'
    subst hs'
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals dsimp only [ga_setGa, brbIn_setGa, brbBind_setGa]
    · exact hInv.F_card
    · exact hInv.F_in_eq
    · exact hInv.F_bind_eq
    · intro i k m hm
      simp only [SubState.mcast_recv, SubState.setProc_recv] at hm
      rw [SubState.mem_mcast_sent, SubState.setProc_sent]
      exact Or.inr (hInv.recv_sub i k hm)
    · intro j' k v hv
      rw [SubState.mcast_proc] at hv
      by_cases hk : j' = j
      · subst hk
        rw [SubState.setProc_proc_self] at hv
        exact hInv.delivIn_val j' k v hv
      · rw [SubState.setProc_proc_ne _ _ _ hk] at hv
        exact hInv.delivIn_val j' k v hv
    · intro j' q U' hU'
      rw [SubState.mcast_proc] at hU'
      by_cases hk : j' = j
      · subst hk
        rw [SubState.setProc_proc_self] at hU'
        exact hInv.delivBind_val j' q U' hU'
      · rw [SubState.setProc_proc_ne _ _ _ hk] at hU'
        exact hInv.delivBind_val j' q U' hU'
    · exact hInv.inVal_prov
    · exact hInv.bindVal_prov
    · intro j' hj A' hA'
      rw [SubState.mem_mcast_sent, SubState.setProc_sent] at hA'
      rcases hA' with ⟨-, hm'⟩ | hold
      · exact absurd hm' (by simp)
      · have hpre := hInv.echo_conf j' hj A' hold
        by_cases hk : j' = j
        · subst hk
          rw [SubState.mcast_proc, SubState.setProc_proc_self]
          exact hpre
        · rw [SubState.mcast_proc, SubState.setProc_proc_ne _ _ _ hk]
          exact hpre
    · intro j' hj A' hA'
      by_cases hk : j' = j
      · subst hk
        rw [SubState.mcast_proc, SubState.setProc_proc_self] at hA'
        exact hInv.echo_card j' hj A' hA'
      · rw [SubState.mcast_proc, SubState.setProc_proc_ne _ _ _ hk] at hA'
        exact hInv.echo_card j' hj A' hA'
    · intro j' hj W hW
      rw [SubState.mem_mcast_sent, SubState.setProc_sent] at hW
      rcases hW with ⟨rfl, hm'⟩ | hold
      · obtain rfl : W = U := by injection hm'
        rw [SubState.mcast_proc, SubState.setProc_proc_self]
      · have hpre := hInv.vote_conf j' hj W hold
        by_cases hk : j' = j
        · subst hk
          rw [hsend] at hpre
          exact absurd hpre (by simp)
        · rw [SubState.mcast_proc, SubState.setProc_proc_ne _ _ _ hk]
          exact hpre
    · intro j' hj W hW
      simp only [SubState.mcast_recv, SubState.setProc_recv]
      by_cases hk : j' = j
      · subst hk
        rw [SubState.mcast_proc, SubState.setProc_proc_self] at hW
        obtain rfl : U = W := by injection hW
        obtain ⟨Q, hQc, hQm⟩ := hQ
        exact ⟨Q, hQc, fun q hq => by
          obtain ⟨A, hA, -, hAU⟩ := hQm q hq
          exact ⟨A, hA, hAU⟩⟩
      · rw [SubState.mcast_proc, SubState.setProc_proc_ne _ _ _ hk] at hW
        exact hInv.vote_backed j' hj W hW
    · intro j' hj U' hU'
      simp only [SubState.mcast_recv, SubState.setProc_recv]
      exact hInv.bind_backed j' hj U' hU'
  | bindCall j U hin happ hQ hb =>
    rw [PMF.mem_support_pure_iff] at hs'
    subst hs'
    refine ⟨hInv.F_card, hInv.F_in_eq, ?_, hInv.recv_sub, hInv.delivIn_val, ?_,
      hInv.inVal_prov, ?_, hInv.echo_conf, hInv.echo_card, hInv.vote_conf,
      hInv.vote_backed, ?_⟩
    all_goals dsimp only [ga_setBrbBind, brbBind_setBrbBind]
    · intro q
      by_cases hq : q = j
      · subst hq
        rw [Function.update_self]
        exact hInv.F_bind_eq q
      · rw [Function.update_of_ne hq]
        exact hInv.F_bind_eq q
    · intro j' q U' hU'
      by_cases hq : q = j
      · subst hq
        rw [Function.update_self]
        exact hInv.delivBind_val j' q U' hU'
      · rw [Function.update_of_ne hq]
        exact hInv.delivBind_val j' q U' hU'
    · intro q U' hU'
      by_cases hq : q = j
      · subst hq
        rw [Function.update_self] at hU' ⊢
        rcases hInv.bindVal_prov q U' hU' with hF | hin'
        · exact Or.inl hF
        · rw [hb] at hin'
          exact absurd hin' (by simp)
      · rw [Function.update_of_ne hq] at hU' ⊢
        exact hInv.bindVal_prov q U' hU'
    · intro j' hj U' hU'
      by_cases hq : j' = j
      · subst hq
        rw [Function.update_self] at hU'
        have hUU : some U = some U' := hU'
        obtain rfl : U = U' := by injection hUU
        obtain ⟨Q, hQc, hQm⟩ := hQ
        exact ⟨Q, hQc, fun q hq => by
          obtain ⟨W, hW, -, hWU⟩ := hQm q hq
          exact ⟨W, hW, hWU⟩⟩
      · rw [Function.update_of_ne hq] at hU'
        exact hInv.bind_backed j' hj U' hU'
  | bindCallSpecLoop j U hin happ hQ =>
    rw [PMF.mem_support_pure_iff] at hs'
    subst hs'
    exact hInv
  | byz j m h =>
    rw [PMF.mem_support_pure_iff] at hs'
    subst hs'
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals dsimp only [ga_setGa, brbIn_setGa, brbBind_setGa]
    · exact hInv.F_card
    · exact hInv.F_in_eq
    · exact hInv.F_bind_eq
    · intro i k m' hm'
      rw [SubState.mcast_recv] at hm'
      rw [SubState.mem_mcast_sent]
      exact Or.inr (hInv.recv_sub i k hm')
    · intro j' k v hv
      rw [SubState.mcast_proc] at hv
      exact hInv.delivIn_val j' k v hv
    · intro j' q U hU
      rw [SubState.mcast_proc] at hU
      exact hInv.delivBind_val j' q U hU
    · exact hInv.inVal_prov
    · exact hInv.bindVal_prov
    · intro j' hj A hA
      rw [SubState.mem_mcast_sent] at hA
      rw [SubState.mcast_proc]
      rcases hA with ⟨rfl, -⟩ | hold
      · exact absurd h hj
      · exact hInv.echo_conf j' hj A hold
    · intro j' hj A hA
      rw [SubState.mcast_proc] at hA
      exact hInv.echo_card j' hj A hA
    · intro j' hj W hW
      rw [SubState.mem_mcast_sent] at hW
      rw [SubState.mcast_proc]
      rcases hW with ⟨rfl, -⟩ | hold
      · exact absurd h hj
      · exact hInv.vote_conf j' hj W hold
    · intro j' hj W hW
      rw [SubState.mcast_proc] at hW
      rw [SubState.mcast_recv]
      exact hInv.vote_backed j' hj W hW
    · intro j' hj U hU
      rw [SubState.mcast_recv]
      exact hInv.bind_backed j' hj U hU
  | inRet k j v hv hr =>
    rw [PMF.mem_support_pure_iff] at hs'
    subst hs'
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals dsimp only [ga_setBrbIn, ga_setGa, brbIn_setBrbIn, brbBind_setBrbIn,
      brbBind_setGa]
    · exact hInv.F_card
    · intro k'
      by_cases hk : k' = k
      · subst hk
        rw [Function.update_self]
        exact hInv.F_in_eq k'
      · rw [Function.update_of_ne hk]
        exact hInv.F_in_eq k'
    · exact hInv.F_bind_eq
    · intro i k' m hm
      rw [SubState.setProc_recv] at hm
      rw [SubState.setProc_sent]
      exact hInv.recv_sub i k' hm
    · intro j' k' v' hv'
      by_cases hj : j' = j
      · subst hj
        rw [SubState.setProc_proc_self] at hv'
        dsimp only at hv'
        by_cases hk : k' = k
        · subst hk
          rw [Function.update_self] at hv'
          rw [Function.update_self]
          obtain rfl : v = v' := by injection hv'
          exact hv
        · rw [Function.update_of_ne hk] at hv'
          rw [Function.update_of_ne hk]
          exact hInv.delivIn_val j' k' v' hv'
      · rw [SubState.setProc_proc_ne _ _ _ hj] at hv'
        by_cases hk : k' = k
        · subst hk
          rw [Function.update_self]
          exact hInv.delivIn_val j' k' v' hv'
        · rw [Function.update_of_ne hk]
          exact hInv.delivIn_val j' k' v' hv'
    · intro j' q U hU
      by_cases hj : j' = j
      · subst hj
        rw [SubState.setProc_proc_self] at hU
        exact hInv.delivBind_val j' q U hU
      · rw [SubState.setProc_proc_ne _ _ _ hj] at hU
        exact hInv.delivBind_val j' q U hU
    · intro k' v' hv'
      by_cases hk : k' = k
      · subst hk
        rw [Function.update_self] at hv' ⊢
        exact hInv.inVal_prov k' v' hv'
      · rw [Function.update_of_ne hk] at hv' ⊢
        exact hInv.inVal_prov k' v' hv'
    · exact hInv.bindVal_prov
    · intro j' hj A hA
      rw [SubState.setProc_sent] at hA
      have hpre := hInv.echo_conf j' hj A hA
      by_cases hk : j' = j
      · subst hk
        rw [SubState.setProc_proc_self]
        exact hpre
      · rw [SubState.setProc_proc_ne _ _ _ hk]
        exact hpre
    · intro j' hj A hA
      by_cases hk : j' = j
      · subst hk
        rw [SubState.setProc_proc_self] at hA
        exact hInv.echo_card j' hj A hA
      · rw [SubState.setProc_proc_ne _ _ _ hk] at hA
        exact hInv.echo_card j' hj A hA
    · intro j' hj W hW
      rw [SubState.setProc_sent] at hW
      have hpre := hInv.vote_conf j' hj W hW
      by_cases hk : j' = j
      · subst hk
        rw [SubState.setProc_proc_self]
        exact hpre
      · rw [SubState.setProc_proc_ne _ _ _ hk]
        exact hpre
    · intro j' hj W hW
      rw [SubState.setProc_recv]
      by_cases hk : j' = j
      · subst hk
        rw [SubState.setProc_proc_self] at hW
        exact hInv.vote_backed j' hj W hW
      · rw [SubState.setProc_proc_ne _ _ _ hk] at hW
        exact hInv.vote_backed j' hj W hW
    · intro j' hj U hU
      rw [SubState.setProc_recv]
      exact hInv.bind_backed j' hj U hU
  | bindRet q j U hv hr =>
    rw [PMF.mem_support_pure_iff] at hs'
    subst hs'
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals dsimp only [ga_setBrbBind, ga_setGa, brbBind_setBrbBind, brbIn_setBrbBind,
      brbIn_setGa]
    · exact hInv.F_card
    · exact hInv.F_in_eq
    · intro q'
      by_cases hq : q' = q
      · subst hq
        rw [Function.update_self]
        exact hInv.F_bind_eq q'
      · rw [Function.update_of_ne hq]
        exact hInv.F_bind_eq q'
    · intro i k m hm
      rw [SubState.setProc_recv] at hm
      rw [SubState.setProc_sent]
      exact hInv.recv_sub i k hm
    · intro j' k v hv'
      by_cases hj : j' = j
      · subst hj
        rw [SubState.setProc_proc_self] at hv'
        exact hInv.delivIn_val j' k v hv'
      · rw [SubState.setProc_proc_ne _ _ _ hj] at hv'
        exact hInv.delivIn_val j' k v hv'
    · intro j' q' U' hU'
      by_cases hj : j' = j
      · subst hj
        rw [SubState.setProc_proc_self] at hU'
        dsimp only at hU'
        by_cases hq : q' = q
        · subst hq
          rw [Function.update_self] at hU'
          rw [Function.update_self]
          obtain rfl : U = U' := by injection hU'
          exact hv
        · rw [Function.update_of_ne hq] at hU'
          rw [Function.update_of_ne hq]
          exact hInv.delivBind_val j' q' U' hU'
      · rw [SubState.setProc_proc_ne _ _ _ hj] at hU'
        by_cases hq : q' = q
        · subst hq
          rw [Function.update_self]
          exact hInv.delivBind_val j' q' U' hU'
        · rw [Function.update_of_ne hq]
          exact hInv.delivBind_val j' q' U' hU'
    · exact hInv.inVal_prov
    · intro q' U' hU'
      by_cases hq : q' = q
      · subst hq
        rw [Function.update_self] at hU' ⊢
        exact hInv.bindVal_prov q' U' hU'
      · rw [Function.update_of_ne hq] at hU' ⊢
        exact hInv.bindVal_prov q' U' hU'
    · intro j' hj A hA
      rw [SubState.setProc_sent] at hA
      have hpre := hInv.echo_conf j' hj A hA
      by_cases hk : j' = j
      · subst hk
        rw [SubState.setProc_proc_self]
        exact hpre
      · rw [SubState.setProc_proc_ne _ _ _ hk]
        exact hpre
    · intro j' hj A hA
      by_cases hk : j' = j
      · subst hk
        rw [SubState.setProc_proc_self] at hA
        exact hInv.echo_card j' hj A hA
      · rw [SubState.setProc_proc_ne _ _ _ hk] at hA
        exact hInv.echo_card j' hj A hA
    · intro j' hj W hW
      rw [SubState.setProc_sent] at hW
      have hpre := hInv.vote_conf j' hj W hW
      by_cases hk : j' = j
      · subst hk
        rw [SubState.setProc_proc_self]
        exact hpre
      · rw [SubState.setProc_proc_ne _ _ _ hk]
        exact hpre
    · intro j' hj W hW
      rw [SubState.setProc_recv]
      by_cases hk : j' = j
      · subst hk
        rw [SubState.setProc_proc_self] at hW
        exact hInv.vote_backed j' hj W hW
      · rw [SubState.setProc_proc_ne _ _ _ hk] at hW
        exact hInv.vote_backed j' hj W hW
    · intro j' hj U' hU'
      rw [SubState.setProc_recv]
      by_cases hq : j' = q
      · subst hq
        rw [Function.update_self] at hU'
        exact hInv.bind_backed j' hj U' hU'
      · rw [Function.update_of_ne hq] at hU'
        exact hInv.bind_backed j' hj U' hU'
  | ret id g hin hsub hQ hr =>
    rw [PMF.mem_support_pure_iff] at hs'
    subst hs'
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals dsimp only [ga_setCore, ga_setGa, brbIn_setCore, brbIn_setGa,
      brbBind_setCore, brbBind_setGa]
    · exact hInv.F_card
    · exact hInv.F_in_eq
    · exact hInv.F_bind_eq
    · intro i k m hm
      rw [SubState.setProc_recv] at hm
      rw [SubState.setProc_sent]
      exact hInv.recv_sub i k hm
    · intro j k v hv
      by_cases hj : j = id
      · subst hj
        rw [SubState.setProc_proc_self] at hv
        exact hInv.delivIn_val j k v hv
      · rw [SubState.setProc_proc_ne _ _ _ hj] at hv
        exact hInv.delivIn_val j k v hv
    · intro j q U hU
      by_cases hj : j = id
      · subst hj
        rw [SubState.setProc_proc_self] at hU
        exact hInv.delivBind_val j q U hU
      · rw [SubState.setProc_proc_ne _ _ _ hj] at hU
        exact hInv.delivBind_val j q U hU
    · exact hInv.inVal_prov
    · exact hInv.bindVal_prov
    · intro j hj A hA
      rw [SubState.setProc_sent] at hA
      have hpre := hInv.echo_conf j hj A hA
      by_cases hk : j = id
      · subst hk
        rw [SubState.setProc_proc_self]
        exact hpre
      · rw [SubState.setProc_proc_ne _ _ _ hk]
        exact hpre
    · intro j hj A hA
      by_cases hk : j = id
      · subst hk
        rw [SubState.setProc_proc_self] at hA
        exact hInv.echo_card j hj A hA
      · rw [SubState.setProc_proc_ne _ _ _ hk] at hA
        exact hInv.echo_card j hj A hA
    · intro j hj W hW
      rw [SubState.setProc_sent] at hW
      have hpre := hInv.vote_conf j hj W hW
      by_cases hk : j = id
      · subst hk
        rw [SubState.setProc_proc_self]
        exact hpre
      · rw [SubState.setProc_proc_ne _ _ _ hk]
        exact hpre
    · intro j hj W hW
      rw [SubState.setProc_recv]
      by_cases hk : j = id
      · subst hk
        rw [SubState.setProc_proc_self] at hW
        exact hInv.vote_backed j hj W hW
      · rw [SubState.setProc_proc_ne _ _ _ hk] at hW
        exact hInv.vote_backed j hj W hW
    · intro j hj U hU
      rw [SubState.setProc_recv]
      exact hInv.bind_backed j hj U hU
  | fail id =>
    rw [PMF.mem_support_pure_iff] at hs'
    subst hs'
    have hF : ∀ k, k ∉ (SubState.corrupt P id (ga s)).F → k ∉ (ga s).F :=
      fun k hk hkF => hk (SubState.corrupt_F_subset (ga s) id hkF)
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals dsimp only [ga_corruptAll, brbIn_corruptAll, brbBind_corruptAll]
    · exact SubState.corrupt_card_le (ga s) id hInv.F_card
    · intro k
      rw [BRB.SpecState.corrupt_F, SubState.corrupt_F, hInv.F_in_eq k]
    · intro k
      rw [BRB.SpecState.corrupt_F, SubState.corrupt_F, hInv.F_bind_eq k]
    · intro i k m hm
      rw [SubState.corrupt_recv] at hm
      rw [SubState.corrupt_sent]
      exact hInv.recv_sub i k hm
    · intro j k v hv
      rw [SubState.corrupt_proc] at hv
      rw [BRB.corrupt_val]
      exact hInv.delivIn_val j k v hv
    · intro j q U hU
      rw [SubState.corrupt_proc] at hU
      rw [BRB.corrupt_val]
      exact hInv.delivBind_val j q U hU
    · intro k v hv
      rw [BRB.corrupt_val] at hv
      rw [BRB.corrupt_input]
      rcases hInv.inVal_prov k v hv with hkF | hin
      · exact Or.inl (SubState.corrupt_F_subset (ga s) id hkF)
      · exact Or.inr hin
    · intro k U hU
      rw [BRB.corrupt_val] at hU
      rw [BRB.corrupt_input]
      rcases hInv.bindVal_prov k U hU with hkF | hin
      · exact Or.inl (SubState.corrupt_F_subset (ga s) id hkF)
      · exact Or.inr hin
    · intro j hj A hA
      rw [SubState.corrupt_sent] at hA
      rw [SubState.corrupt_proc]
      exact hInv.echo_conf j (hF j hj) A hA
    · intro j hj A hA
      rw [SubState.corrupt_proc] at hA
      exact hInv.echo_card j (hF j hj) A hA
    · intro j hj W hW
      rw [SubState.corrupt_sent] at hW
      rw [SubState.corrupt_proc]
      exact hInv.vote_conf j (hF j hj) W hW
    · intro j hj W hW
      rw [SubState.corrupt_proc] at hW
      rw [SubState.corrupt_recv]
      exact hInv.vote_backed j (hF j hj) W hW
    · intro j hj U hU
      rw [BRB.corrupt_input] at hU
      rw [SubState.corrupt_recv]
      exact hInv.bind_backed j (hF j hj) U hU


/-! ### The approval of an echo field -/

omit [DecidableEq X] in
/-- A payload set approved by one program's input store is approved at the
instance: each entry of the store is the committed value of the instance that
returned it. -/
theorem approved_of_approvedBy {s : IdealState P.n X} (hConf : IdealConf P s)
    {j : Fin P.n} {A : APSet P.n X} (h : approvedBy ((ga s).proc j) A) :
    approved s A :=
  fun p hp => hConf.delivIn_val j p.1 p.2 (h p hp)

/-- Committed input entries are write-once, so `approved` is monotone along
every rule. -/
theorem approved_mono {s s' : IdealState P.n X} {l : Lab P.n X}
    {μ : PMF (IdealState P.n X)} (hstep : IdealStep P s l μ)
    (hs' : s' ∈ μ.support) {A : APSet P.n X} (h : approved s A) : approved s' A := by
  have key : ∀ t : IdealState P.n X,
      (∀ k v, (brbIn s k).val = some v → (brbIn t k).val = some v) → approved t A :=
    fun t ht p hp => ht p.1 p.2 (h p hp)
  cases hstep with
  | call id x hc hb =>
      rw [PMF.mem_support_pure_iff] at hs'; subst hs'
      refine key _ (fun k v hv => ?_)
      dsimp only [brbIn_setBrbIn]
      by_cases hk : k = id
      · subst hk; rw [Function.update_self]; exact hv
      · rw [Function.update_of_ne hk]; exact hv
  | callProcLoop id x hb =>
      rw [PMF.mem_support_pure_iff] at hs'; subst hs'
      refine key _ (fun k v hv => ?_)
      dsimp only [brbIn_setBrbIn]
      by_cases hk : k = id
      · subst hk; rw [Function.update_self]; exact hv
      · rw [Function.update_of_ne hk]; exact hv
  | commitIn k v hv hm =>
      rw [PMF.mem_support_pure_iff] at hs'; subst hs'
      refine key _ (fun k' v' hv' => ?_)
      dsimp only [brbIn_setBrbIn]
      by_cases hk : k' = k
      · subst hk; rw [hv] at hv'; exact absurd hv' (by simp)
      · rw [Function.update_of_ne hk]; exact hv'
  | inRet k j v hv hr =>
      rw [PMF.mem_support_pure_iff] at hs'; subst hs'
      refine key _ (fun k' v' hv' => ?_)
      dsimp only [brbIn_setBrbIn]
      by_cases hk : k' = k
      · subst hk; rw [Function.update_self]; exact hv'
      · rw [Function.update_of_ne hk]; exact hv'
  | fail id =>
      rw [PMF.mem_support_pure_iff] at hs'; subst hs'
      refine key _ (fun k v hv => ?_)
      dsimp only [brbIn_corruptAll]
      rw [BRB.corrupt_val]; exact hv
  | _ => rw [PMF.mem_support_pure_iff] at hs'; subst hs'; exact h

/-- The `ECHO` fields of the initial state are empty. -/
theorem echoAppr_initial :
    ∀ (j : Fin P.n) (A : APSet P.n X),
      ((ga ((idealInst P X).init)).proc j).sentEcho = some A →
        approved ((idealInst P X).init) A := by
  intro j A hA
  simp [ga, SubState.proc, ProcRec.initial, PRec.initial] at hA

/-- **The approval of an `ECHO` field is inductive**: only `IdealStep.echo`
writes the field, and its guard is the approval of the payload it writes by the
writer's own store. -/
theorem echoAppr_step {s s' : IdealState P.n X} {l : Lab P.n X}
    {μ : PMF (IdealState P.n X)} (hConf : IdealConf P s)
    (hEA : ∀ (j : Fin P.n) (A : APSet P.n X),
      ((ga s).proc j).sentEcho = some A → approved s A)
    (hstep : IdealStep P s l μ) (hs' : s' ∈ μ.support) :
    ∀ (j : Fin P.n) (A : APSet P.n X),
      ((ga s').proc j).sentEcho = some A → approved s' A := by
  intro j A hA
  refine approved_mono hstep hs' ?_
  cases hstep with
  | call id x hc hb =>
      rw [PMF.mem_support_pure_iff] at hs'; subst hs'
      refine hEA j A ?_
      dsimp only [ga_setBrbIn, ga_setGa] at hA
      by_cases hk : j = id
      · subst hk; rw [SubState.setProc_proc_self] at hA; exact hA
      · rw [SubState.setProc_proc_ne _ _ _ hk] at hA; exact hA
  | callSpecLoop id x hc =>
      rw [PMF.mem_support_pure_iff] at hs'; subst hs'
      refine hEA j A ?_
      dsimp only [ga_setGa] at hA
      by_cases hk : j = id
      · subst hk; rw [SubState.setProc_proc_self] at hA; exact hA
      · rw [SubState.setProc_proc_ne _ _ _ hk] at hA; exact hA
  | echo j₀ A₀ hin happ hcard hsend =>
      rw [PMF.mem_support_pure_iff] at hs'; subst hs'
      dsimp only [ga_setGa] at hA
      rw [SubState.mcast_proc] at hA
      by_cases hk : j = j₀
      · subst hk
        rw [SubState.setProc_proc_self] at hA
        obtain rfl : A₀ = A := Option.some.inj hA
        exact approved_of_approvedBy hConf happ
      · rw [SubState.setProc_proc_ne _ _ _ hk] at hA
        exact hEA j A hA
  | vote j₀ U hin happ hQ hsend =>
      rw [PMF.mem_support_pure_iff] at hs'; subst hs'
      refine hEA j A ?_
      dsimp only [ga_setGa] at hA
      rw [SubState.mcast_proc] at hA
      by_cases hk : j = j₀
      · subst hk; rw [SubState.setProc_proc_self] at hA; exact hA
      · rw [SubState.setProc_proc_ne _ _ _ hk] at hA; exact hA
  | inRet k j₀ v hv hr =>
      rw [PMF.mem_support_pure_iff] at hs'; subst hs'
      refine hEA j A ?_
      dsimp only [ga_setBrbIn, ga_setGa] at hA
      by_cases hk : j = j₀
      · subst hk; rw [SubState.setProc_proc_self] at hA; exact hA
      · rw [SubState.setProc_proc_ne _ _ _ hk] at hA; exact hA
  | bindRet q j₀ U hv hr =>
      rw [PMF.mem_support_pure_iff] at hs'; subst hs'
      refine hEA j A ?_
      dsimp only [ga_setBrbBind, ga_setGa] at hA
      by_cases hk : j = j₀
      · subst hk; rw [SubState.setProc_proc_self] at hA; exact hA
      · rw [SubState.setProc_proc_ne _ _ _ hk] at hA; exact hA
  | ret id g hin hsub hQ hr =>
      rw [PMF.mem_support_pure_iff] at hs'; subst hs'
      refine hEA j A ?_
      dsimp only [ga_setCore, ga_setGa] at hA
      by_cases hk : j = id
      · subst hk; rw [SubState.setProc_proc_self] at hA; exact hA
      · rw [SubState.setProc_proc_ne _ _ _ hk] at hA; exact hA
  | deliver i j₀ m hm =>
      rw [PMF.mem_support_pure_iff] at hs'; subst hs'
      refine hEA j A ?_
      dsimp only [ga_setGa] at hA
      rw [SubState.recvMsg_proc] at hA; exact hA
  | byz j₀ m hj =>
      rw [PMF.mem_support_pure_iff] at hs'; subst hs'
      refine hEA j A ?_
      dsimp only [ga_setGa] at hA
      rw [SubState.mcast_proc] at hA; exact hA
  | fail id =>
      rw [PMF.mem_support_pure_iff] at hs'; subst hs'
      refine hEA j A ?_
      dsimp only [ga_corruptAll] at hA
      rw [SubState.corrupt_proc] at hA; exact hA
  | _ => rw [PMF.mem_support_pure_iff] at hs'; subst hs'; exact hEA j A hA

/-! ### The invariant -/

/-- **The invariant of the composed gather instance**: the conformance clauses,
together with the approval of every `ECHO` field. -/
structure IdealInv (P : Params) (s : IdealState P.n X) : Prop extends IdealConf P s where
  /-- The payload set in a process's `ECHO` field consists of committed input
  entries. No honesty side condition: only `IdealStep.echo` writes the field,
  and its guard holds of a corrupted sender too. -/
  echo_appr : ∀ (j : Fin P.n) (A : APSet P.n X),
    ((ga s).proc j).sentEcho = some A → approved s A

/-- The invariant holds initially. -/
theorem IdealInv.initial : IdealInv P ((idealInst P X).init) :=
  ⟨IdealConf.initial, echoAppr_initial⟩

/-- The invariant is preserved by every step. -/
theorem IdealInv.step {s : IdealState P.n X} {l : Lab P.n X}
    {μ : PMF (IdealState P.n X)} (hInv : IdealInv P s) (hstep : IdealStep P s l μ)
    {s' : IdealState P.n X} (hs' : s' ∈ μ.support) : IdealInv P s' :=
  ⟨hInv.toIdealConf.step hstep hs', echoAppr_step hInv.toIdealConf hInv.echo_appr hstep hs'⟩


/-! ### The incidence on the gather network state

The rows of the incidence read the sent sets and the corrupted set, so
`mem_honest`, `card_honest`, `mem_dominatedBy`, `honest_filter_dominatedBy` and
`sum_dominatedBy` apply to `netOf` as they stand. What the invariant supplies is
the width of a row. -/

omit [DecidableEq X] in
/-- The `ECHO` payload of a process outside `F` is the one its `sentEcho` field
holds. -/
theorem echoOf_eq {s : IdealState P.n X} (hInv : IdealInv P s) {j : Fin P.n}
    (hj : j ∉ (ga s).F) {A : APSet P.n X} (hA : GaMsg.echo A ∈ (ga s).sent j) :
    echoOf (netOf s) j = A := by
  classical
  have hex : ∃ A : APSet P.n X, GaMsg.echo A ∈ (netOf s).sent j := ⟨A, hA⟩
  rw [echoOf, dif_pos hex]
  have h1 := hInv.echo_conf j hj _ hex.choose_spec
  have h2 := hInv.echo_conf j hj A hA
  rw [h1] at h2
  exact Option.some.inj h2

omit [DecidableEq X] in
/-- **Every row is wide**: a process outside `F` dominates at least `n − f`
senders. Its `VOTE` payload, if it has one, is backed by `n − f` `ECHO`
receipts; if it has none the condition is vacuous and the row is
everything. -/
theorem dominatedBy_card {s : IdealState P.n X} (hInv : IdealInv P s) {q : Fin P.n}
    (hq : q ∉ (ga s).F) : P.n - P.f ≤ (dominatedBy (netOf s) q).card := by
  classical
  by_cases hv : ∃ W : APSet P.n X, GaMsg.vote W ∈ (ga s).sent q
  · obtain ⟨W, hW⟩ := hv
    have hslot := hInv.vote_conf q hq W hW
    obtain ⟨Q, hQc, hQm⟩ := hInv.vote_backed q hq W hslot
    refine le_trans hQc (Finset.card_le_card fun j hj => ?_)
    rw [mem_dominatedBy]
    intro W' hW'
    have hslot' := hInv.vote_conf q hq W' hW'
    rw [hslot] at hslot'
    obtain rfl : W = W' := Option.some.inj hslot'
    obtain ⟨A, hA, hAW⟩ := hQm j hj
    exact ⟨A, hInv.recv_sub q j hA, hAW⟩
  · have hall : dominatedBy (netOf s) q = Finset.univ := by
      refine Finset.eq_univ_iff_forall.mpr fun j => ?_
      rw [mem_dominatedBy]
      intro W hW
      exact absurd ⟨W, hW⟩ hv
    rw [hall, Finset.card_univ, Fintype.card_fin]
    omega

open scoped Classical in
omit [DecidableEq X] in
/-- A row of a process outside `F` meets the processes outside `F` in at least
`n − f − |F|` of them. -/
theorem dominatedBy_honest_card {s : IdealState P.n X} (hInv : IdealInv P s)
    {q : Fin P.n} (hq : q ∉ (ga s).F) :
    P.n - P.f - (ga s).F.card ≤
      ((honest (netOf s)).filter (fun j => j ∈ dominatedBy (netOf s) q)).card := by
  rw [honest_filter_dominatedBy, netOf_F]
  have h1 := Finset.le_card_sdiff (ga s).F (dominatedBy (netOf s) q)
  have h2 := dominatedBy_card hInv hq
  omega

open scoped Classical in
omit [DecidableEq X] in
/-- **The pigeonhole.** Some sender outside `F` has at least `n − f − |F|`
dominators. -/
theorem exists_dominators {s : IdealState P.n X} (hInv : IdealInv P s) :
    ∃ j₀, j₀ ∈ honest (netOf s) ∧
      P.n - P.f - (ga s).F.card ≤ (dominators (netOf s) j₀).card := by
  by_contra hc
  push Not at hc
  have hF := hInv.F_card
  have hf := P.hf
  set H : Finset (Fin P.n) := honest (netOf s) with hH
  set m : ℕ := P.n - P.f - (ga s).F.card with hm
  have hHcard : H.card = P.n - (ga s).F.card := card_honest
  have hpos : 0 < H.card := by omega
  have hlow : ∀ q ∈ H, m ≤ ((honest (netOf s)).filter
      (fun j => j ∈ dominatedBy (netOf s) q)).card :=
    fun q hq => dominatedBy_honest_card hInv (mem_honest.mp (hH ▸ hq))
  have hsum2 : H.card * m
      ≤ ∑ q ∈ H, ((honest (netOf s)).filter
        (fun j => j ∈ dominatedBy (netOf s) q)).card := by
    simpa [smul_eq_mul] using Finset.card_nsmul_le_sum H _ m hlow
  rw [sum_dominatedBy, ← hH] at hsum2
  have hle : ∀ j ∈ H, (dominators (netOf s) j).card ≤ m - 1 := fun j hj => by
    have := hc j (hH ▸ hj); omega
  have hsum1 : ∑ j ∈ H, (dominators (netOf s) j).card ≤ H.card * (m - 1) := by
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
theorem transfer {s : IdealState P.n X} (hInv : IdealInv P s) {j₀ : Fin P.n}
    (hj₀ : j₀ ∉ (ga s).F) (hcnt : P.f + 1 ≤ (dominators (netOf s) j₀).card)
    {k : Fin P.n} (hk : k ∉ (ga s).F) {U : APSet P.n X}
    (hU : (brbBind s k).val = some U) :
    ∃ A, GaMsg.echo A ∈ (ga s).sent j₀ ∧ P.n - P.f ≤ A.card ∧ A ⊆ U := by
  obtain ⟨V, hVc, hVm⟩ :=
    hInv.bind_backed k hk U ((hInv.bindVal_prov k U hU).resolve_left hk)
  obtain ⟨q, hqK, hqV⟩ := SubState.exists_mem_inter_of_quorum hcnt hVc
  rw [dominators, Finset.mem_filter] at hqK
  obtain ⟨W, hWrecv, hWU⟩ := hVm q hqV
  obtain ⟨A, hA, hAW⟩ := mem_dominatedBy.mp hqK.2 W (hInv.recv_sub k q hWrecv)
  exact ⟨A, hA, hInv.echo_card j₀ hj₀ A (hInv.echo_conf j₀ hj₀ A hA),
    subset_trans hAW hWU⟩

open scoped Classical in
omit [DecidableEq X] in
/-- The core is the write-once `ECHO` payload of a sender outside `F` with at
least `f + 1` dominators, as soon as some process outside `F` holds a committed
`BIND` payload. -/
theorem core_witness {s : IdealState P.n X} (hInv : IdealInv P s)
    {k₀ : Fin P.n} (hk₀ : k₀ ∉ (ga s).F) {U₀ : APSet P.n X}
    (hU₀ : (brbBind s k₀).val = some U₀) :
    ∃ j₁, j₁ ∉ (ga s).F ∧ P.f + 1 ≤ (dominators (netOf s) j₁).card ∧
      GaMsg.echo (coreOfNet P (ga s).2) ∈ (ga s).sent j₁ ∧
      ((ga s).proc j₁).sentEcho = some (coreOfNet P (ga s).2) := by
  have hF := hInv.F_card
  have hf := P.hf
  have hex : ∃ j, j ∈ honest (netOf s) ∧ P.f + 1 ≤ (dominators (netOf s) j).card := by
    obtain ⟨j₀, hj₀, hcnt⟩ := exists_dominators hInv
    exact ⟨j₀, hj₀, by omega⟩
  have hspec := hex.choose_spec
  have hj₁F : hex.choose ∉ (ga s).F := mem_honest.mp hspec.1
  obtain ⟨A, hA, -, -⟩ := transfer hInv hj₁F hspec.2 hk₀ hU₀
  have hcore : coreOfNet P (ga s).2 = A := by
    rw [← coreOf_netOf, coreOf, dif_pos hex]
    exact echoOf_eq hInv hj₁F hA
  exact ⟨hex.choose, hj₁F, hspec.2, by rw [hcore]; exact hA,
    by rw [hcore]; exact hInv.echo_conf _ hj₁F A hA⟩

omit [DecidableEq X] in
/-- **The single core.** Once some process outside `F` holds a committed `BIND`
payload, the core has at least `n − f` entries and lies below the committed
`BIND` payload of every process outside `F`. -/
theorem single_core {s : IdealState P.n X} (hInv : IdealInv P s)
    {k₀ : Fin P.n} (hk₀ : k₀ ∉ (ga s).F) {U₀ : APSet P.n X}
    (hU₀ : (brbBind s k₀).val = some U₀) :
    P.n - P.f ≤ (coreOfNet P (ga s).2).card ∧
      ∀ k ∉ (ga s).F, ∀ U : APSet P.n X, (brbBind s k).val = some U →
        coreOfNet P (ga s).2 ⊆ U := by
  obtain ⟨j₁, hj₁F, hcnt, hsent, hslot⟩ := core_witness hInv hk₀ hU₀
  refine ⟨hInv.echo_card j₁ hj₁F _ hslot, ?_⟩
  intro k hk U hU
  obtain ⟨A, hA, -, hAU⟩ := transfer hInv hj₁F hcnt hk hU
  have hEq : A = coreOfNet P (ga s).2 := by
    have h1 := hInv.echo_conf j₁ hj₁F A hA
    rw [hslot] at h1
    exact (Option.some.inj h1).symm
  rw [← hEq]
  exact hAU

omit [DecidableEq X] in
/-- **The core is approved**: its entries are committed input entries, the
`ECHO` field it comes from carrying only such entries. -/
theorem single_core_approved {s : IdealState P.n X} (hInv : IdealInv P s)
    {k₀ : Fin P.n} (hk₀ : k₀ ∉ (ga s).F) {U₀ : APSet P.n X}
    (hU₀ : (brbBind s k₀).val = some U₀) :
    approved s (coreOfNet P (ga s).2) := by
  obtain ⟨j₁, -, -, -, hslot⟩ := core_witness hInv hk₀ hU₀
  exact hInv.echo_appr j₁ _ hslot

/-! ### The freeze certificate -/

open scoped Classical in
/-- The coordinates holding a committed `BIND` payload above `C`. The condition
is blind to `F`. -/
noncomputable def bindAbove (s : IdealState P.n X) (C : APSet P.n X) :
    Finset (Fin P.n) :=
  Finset.univ.filter (fun q => ∃ U, (brbBind s q).val = some U ∧ C ⊆ U)

open scoped Classical in
theorem mem_bindAbove {s : IdealState P.n X} {C : APSet P.n X} {q : Fin P.n} :
    q ∈ bindAbove s C ↔ ∃ U, (brbBind s q).val = some U ∧ C ⊆ U := by
  rw [bindAbove, Finset.mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ _, h⟩⟩

/-- A committed `BIND` payload is never rewritten. -/
theorem bindVal_mono {s s' : IdealState P.n X} {l : Lab P.n X}
    {μ : PMF (IdealState P.n X)} (hstep : IdealStep P s l μ) (hs' : s' ∈ μ.support)
    {q : Fin P.n} {U : APSet P.n X} (h : (brbBind s q).val = some U) :
    (brbBind s' q).val = some U := by
  cases hstep with
  | commitBind q' U' hv hm =>
      rw [PMF.mem_support_pure_iff] at hs'; subst hs'
      dsimp only [brbBind_setBrbBind]
      by_cases hq : q = q'
      · subst hq; rw [hv] at h; exact absurd h (by simp)
      · rw [Function.update_of_ne hq]; exact h
  | bindCall j U' hin happ hQ hb =>
      rw [PMF.mem_support_pure_iff] at hs'; subst hs'
      dsimp only [brbBind_setBrbBind]
      by_cases hq : q = j
      · subst hq; rw [Function.update_self]; exact h
      · rw [Function.update_of_ne hq]; exact h
  | bindRet q' j U' hv hr =>
      rw [PMF.mem_support_pure_iff] at hs'; subst hs'
      dsimp only [brbBind_setBrbBind]
      by_cases hq : q = q'
      · subst hq; rw [Function.update_self]; exact h
      · rw [Function.update_of_ne hq]; exact h
  | fail id =>
      rw [PMF.mem_support_pure_iff] at hs'; subst hs'
      dsimp only [brbBind_corruptAll]
      rw [BRB.corrupt_val]; exact h
  | _ => rw [PMF.mem_support_pure_iff] at hs'; subst hs'; exact h

/-- **The certificate is monotone.** The coordinates holding a committed `BIND`
payload above `C` only accumulate, under every rule and every corruption. -/
theorem bindAbove_mono {s s' : IdealState P.n X} {l : Lab P.n X}
    {μ : PMF (IdealState P.n X)} (hstep : IdealStep P s l μ) (hs' : s' ∈ μ.support)
    (C : APSet P.n X) : bindAbove s C ⊆ bindAbove s' C := by
  intro q hq
  rw [mem_bindAbove] at hq ⊢
  obtain ⟨U, hU, hCU⟩ := hq
  exact ⟨U, bindVal_mono hstep hs' hU, hCU⟩

/-- **The freeze.** At a state where an `n − f` quorum of coordinates holds
committed `BIND` payloads, the core has at least `n − f` entries, its entries
are committed input entries, and at least `f + 1` coordinates hold a committed
`BIND` payload above it. The last is the certificate that holds the returns
after the first to this core: it is blind to `F` and monotone
(`bindAbove_mono`), and an `n − f` return quorum meets it. -/
theorem coreOf_freeze {s : IdealState P.n X} (hInv : IdealInv P s)
    {Q : Finset (Fin P.n)} (hQc : P.n - P.f ≤ Q.card)
    (hQm : ∀ q ∈ Q, ∃ U : APSet P.n X, (brbBind s q).val = some U) :
    P.n - P.f ≤ (coreOfNet P (ga s).2).card ∧ approved s (coreOfNet P (ga s).2) ∧
      P.f + 1 ≤ (bindAbove s (coreOfNet P (ga s).2)).card := by
  classical
  have hF := hInv.F_card
  have hf := P.hf
  have hH : P.f + 1 ≤ (Q \ (ga s).F).card := by
    have h1 := Finset.le_card_sdiff (ga s).F Q
    omega
  obtain ⟨H, hHsub, hHcard⟩ := Finset.exists_subset_card_eq hH
  have hHQ : ∀ q ∈ H, q ∈ Q := fun q hq => (Finset.mem_sdiff.mp (hHsub hq)).1
  have hHF : ∀ q ∈ H, q ∉ (ga s).F := fun q hq => (Finset.mem_sdiff.mp (hHsub hq)).2
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
