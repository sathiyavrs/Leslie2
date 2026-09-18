/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sathiya / Claude
-/

import Leslie2Protocols.ABA.Gather.Ideal

/-!
# The core of a gather-over-BRB instance

The invariant of the instance (`ABA/Gather/Ideal.lean`), and the argument
that `coreOf` is a bound core. At every state at which some process outside
`F` holds a committed `BIND` payload, `coreOf` has at least `n − f` entries,
its entries are committed input-BRB entries, and it lies below the committed
`BIND` payload of every process outside `F`.

The counting is over one incidence on the network state. `dominatedBy w q`
is the set of senders an `ECHO` payload of which lies below every `VOTE`
payload `q` has multicast, and `dominators w j` the set of processes outside
`F` that dominate `j` in that sense. A `VOTE` of a process outside `F` is
backed by `n − f` `ECHO` receipts, so `n − f ≤ (dominatedBy w q).card` for
every `q` outside `F`, vacuously so for one that has multicast no `VOTE`.
Summing the bound over the rows outside `F` and exchanging the order of
summation yields a sender `j₀` outside `F` with
`n − f − |F| ≤ (dominators w j₀).card`, and `n − f − |F| ≥ f + 1`. The core
is `j₀`'s `ECHO` payload.

Those `f + 1` dominators meet the `n − f` `VOTE` quorum backing any
committed `BIND` payload `U` of a process outside `F`, in a process whose
write-once `VOTE` payload lies above the core and below `U` (`single_core`).
Every `ECHO` field holds committed input-BRB entries — the clause
`echo_appr` — so the core's entries are committed input-BRB entries
(`single_core_approved`).

`coreOf_freeze` packages the three facts with the count the specification's
freeze needs: at least `f + 1` coordinates hold a committed `BIND` payload
above the core. That count is blind to `F` and monotone under every rule, so
it survives every later corruption, which is what holds the returns after
the first to the core the first one freezes.
-/

namespace PLTS
namespace ABA
namespace Gather

variable {X : Type} [DecidableEq X] {P : Params}

/-! ### The conformance clauses -/

/-- The conformance clauses. The `*_conf` clauses tie an honest
sender's sent to its write-once field, the `*_backed` clauses tie the fields to
the receipts that justified them, and the provenance clauses are the BRB
commit guards, recorded per coordinate. -/
structure IdealConf (P : Params) (s : IdealState P.n X) : Prop where
  /-- The corruption budget. -/
  F_card : s.ga.F.card ≤ P.f
  /-- The input-BRB corrupted sets are in lockstep with the network state's. -/
  F_in_eq : ∀ k, (s.brbIn k).F = s.ga.F
  /-- The bind-BRB corrupted sets are in lockstep with the network state's. -/
  F_bind_eq : ∀ k, (s.brbBind k).F = s.ga.F
  /-- Delivered messages were multicast. -/
  recv_sub : ∀ i k, s.ga.recv i k ⊆ s.ga.sent k
  /-- The input-BRB call records are the gather call records (the fused
  call). -/
  input_eq : ∀ k, (s.brbIn k).input = (s.ga.proc k).input
  /-- A committed input entry of an honest process is its input. -/
  inVal_prov : ∀ k v, (s.brbIn k).val = some v →
    k ∈ s.ga.F ∨ (s.brbIn k).input = some v
  /-- A committed bind payload of an honest process is its contributed
  payload. -/
  bindVal_prov : ∀ k U, (s.brbBind k).val = some U →
    k ∈ s.ga.F ∨ (s.brbBind k).input = some U
  /-- An honest sender's sent `ECHO` matches its write-once field. -/
  echo_conf : ∀ j ∉ s.ga.F, ∀ A, GaMsg.echo A ∈ s.ga.sent j →
    (s.ga.proc j).sentEcho = some A
  /-- An honest echo payload has at least `n − f` entries. -/
  echo_card : ∀ j ∉ s.ga.F, ∀ A, (s.ga.proc j).sentEcho = some A →
    P.n - P.f ≤ A.card
  /-- An honest sender's sent `VOTE` matches its write-once field. -/
  vote_conf : ∀ j ∉ s.ga.F, ∀ W, GaMsg.vote W ∈ s.ga.sent j →
    (s.ga.proc j).sentVote = some W
  /-- An honest vote is backed by `n − f` senders' echo payloads, each
  contained in it. -/
  vote_backed : ∀ j ∉ s.ga.F, ∀ W, (s.ga.proc j).sentVote = some W →
    ∃ Q : Finset (Fin P.n), P.n - P.f ≤ Q.card ∧
      ∀ q ∈ Q, ∃ A, GaMsg.echo A ∈ s.ga.recv j q ∧ A ⊆ W
  /-- An honest contributed bind payload is backed by `n − f` senders' vote
  payloads, each contained in it. -/
  bind_backed : ∀ j ∉ s.ga.F, ∀ U, (s.brbBind j).input = some U →
    ∃ Q : Finset (Fin P.n), P.n - P.f ≤ Q.card ∧
      ∀ q ∈ Q, ∃ W, GaMsg.vote W ∈ s.ga.recv j q ∧ W ⊆ U

omit [DecidableEq X] in
/-- The conformance clauses hold initially. -/
theorem IdealConf.initial : IdealConf P (IdealState.initial P.n X) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [IdealState.initial, PRec.initial, BRB.SpecState.initial]

/-- The conformance clauses are preserved by every step. -/
theorem IdealConf.step {s : IdealState P.n X} {l : Lab P.n X}
    {μ : PMF (IdealState P.n X)} (hInv : IdealConf P s) (hstep : IdealStep P s l μ)
    {s' : IdealState P.n X} (hs' : s' ∈ μ.support) : IdealConf P s' := by
  cases hstep with
  | call id x h =>
    rw [PMF.mem_support_pure_iff] at hs'
    subst hs'
    refine ⟨hInv.F_card, ?_, hInv.F_bind_eq, ?_,
      ?_, ?_, hInv.bindVal_prov, ?_, ?_, ?_, ?_, ?_⟩
    all_goals dsimp only
    · intro k
      by_cases hk : k = id
      · subst hk
        rw [Function.update_self]
        exact hInv.F_in_eq k
      · rw [Function.update_of_ne hk]
        exact hInv.F_in_eq k
    · intro i k x hx
      rw [SubState.setProc_recv] at hx
      rw [SubState.setProc_sent]
      exact hInv.recv_sub i k hx
    · intro k
      by_cases hk : k = id
      · subst hk
        rw [Function.update_self, SubState.setProc_proc_self]
      · rw [Function.update_of_ne hk, SubState.setProc_proc_ne _ _ _ hk]
        exact hInv.input_eq k
    · intro k v hv
      by_cases hk : k = id
      · subst hk
        rw [Function.update_self] at hv
        have hv0 : (s.brbIn k).val = some v := hv
        rcases hInv.inVal_prov k v hv0 with hF | hin
        · exact Or.inl hF
        · rw [hInv.input_eq k, h] at hin
          exact absurd hin (by simp)
      · rw [Function.update_of_ne hk] at hv ⊢
        exact hInv.inVal_prov k v hv
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
      rw [show (s.ga.setProc id { s.ga.proc id with input := some x }).recv
          = s.ga.recv from SubState.setProc_recv ..]
      by_cases hk : j = id
      · subst hk
        rw [SubState.setProc_proc_self] at hW
        exact hInv.vote_backed j hj W hW
      · rw [SubState.setProc_proc_ne _ _ _ hk] at hW
        exact hInv.vote_backed j hj W hW
    · intro j hj U hU
      rw [show (s.ga.setProc id { s.ga.proc id with input := some x }).recv
          = s.ga.recv from SubState.setProc_recv ..]
      exact hInv.bind_backed j hj U hU
  | callLoop id x =>
    rw [PMF.mem_support_pure_iff] at hs'
    subst hs'
    exact hInv
  | commitIn k v hv hm =>
    rw [PMF.mem_support_pure_iff] at hs'
    subst hs'
    refine ⟨hInv.F_card, ?_, hInv.F_bind_eq, hInv.recv_sub, ?_, ?_,
      hInv.bindVal_prov, hInv.echo_conf, hInv.echo_card, hInv.vote_conf,
      hInv.vote_backed, hInv.bind_backed⟩
    all_goals dsimp only
    · intro k'
      by_cases hk : k' = k
      · subst hk
        rw [Function.update_self]
        exact hInv.F_in_eq k'
      · rw [Function.update_of_ne hk]
        exact hInv.F_in_eq k'
    · intro k'
      by_cases hk : k' = k
      · subst hk
        rw [Function.update_self]
        exact hInv.input_eq k'
      · rw [Function.update_of_ne hk]
        exact hInv.input_eq k'
    · intro k' v' hv'
      by_cases hk : k' = k
      · subst hk
        rw [Function.update_self] at hv' ⊢
        have : some v = some v' := hv'
        obtain rfl : v = v' := by injection this
        exact hm
      · rw [Function.update_of_ne hk] at hv' ⊢
        exact hInv.inVal_prov k' v' hv'
  | commitBind k U hv hm =>
    rw [PMF.mem_support_pure_iff] at hs'
    subst hs'
    refine ⟨hInv.F_card, hInv.F_in_eq, ?_, hInv.recv_sub, hInv.input_eq,
      hInv.inVal_prov, ?_, hInv.echo_conf, hInv.echo_card, hInv.vote_conf,
      hInv.vote_backed, ?_⟩
    all_goals dsimp only
    · intro k'
      by_cases hk : k' = k
      · subst hk
        rw [Function.update_self]
        exact hInv.F_bind_eq k'
      · rw [Function.update_of_ne hk]
        exact hInv.F_bind_eq k'
    · intro k' U' hU'
      by_cases hk : k' = k
      · subst hk
        rw [Function.update_self] at hU' ⊢
        have : some U = some U' := hU'
        obtain rfl : U = U' := by injection this
        exact hm
      · rw [Function.update_of_ne hk] at hU' ⊢
        exact hInv.bindVal_prov k' U' hU'
    · intro j hj U' hU'
      by_cases hk : j = k
      · subst hk
        rw [Function.update_self] at hU'
        have hin : (s.brbBind j).input = some U' := hU'
        exact hInv.bind_backed j hj U' hin
      · rw [Function.update_of_ne hk] at hU'
        exact hInv.bind_backed j hj U' hU'
  | deliver i j m h =>
    rw [PMF.mem_support_pure_iff] at hs'
    subst hs'
    refine ⟨hInv.F_card, hInv.F_in_eq, hInv.F_bind_eq, ?_, ?_,
      hInv.inVal_prov, hInv.bindVal_prov, ?_, ?_, ?_, ?_, ?_⟩
    all_goals dsimp only
    · intro i' k x hx
      rw [SubState.mem_recvMsg_recv] at hx
      rw [SubState.recvMsg_sent]
      rcases hx with ⟨-, rfl, rfl⟩ | hold
      · exact h
      · exact hInv.recv_sub i' k hold
    · intro k
      rw [SubState.recvMsg_proc]
      exact hInv.input_eq k
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
    refine ⟨hInv.F_card, hInv.F_in_eq, hInv.F_bind_eq, ?_, ?_,
      hInv.inVal_prov, hInv.bindVal_prov, ?_, ?_, ?_, ?_, ?_⟩
    all_goals dsimp only
    · intro i k x hx
      simp only [SubState.mcast_recv, SubState.setProc_recv] at hx
      rw [SubState.mem_mcast_sent, SubState.setProc_sent]
      exact Or.inr (hInv.recv_sub i k hx)
    · intro k
      by_cases hk : k = j
      · subst hk
        rw [SubState.mcast_proc, SubState.setProc_proc_self]
        exact hInv.input_eq k
      · rw [SubState.mcast_proc, SubState.setProc_proc_ne _ _ _ hk]
        exact hInv.input_eq k
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
    refine ⟨hInv.F_card, hInv.F_in_eq, hInv.F_bind_eq, ?_, ?_,
      hInv.inVal_prov, hInv.bindVal_prov, ?_, ?_, ?_, ?_, ?_⟩
    all_goals dsimp only
    · intro i k x hx
      simp only [SubState.mcast_recv, SubState.setProc_recv] at hx
      rw [SubState.mem_mcast_sent, SubState.setProc_sent]
      exact Or.inr (hInv.recv_sub i k hx)
    · intro k
      by_cases hk : k = j
      · subst hk
        rw [SubState.mcast_proc, SubState.setProc_proc_self]
        exact hInv.input_eq k
      · rw [SubState.mcast_proc, SubState.setProc_proc_ne _ _ _ hk]
        exact hInv.input_eq k
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
  | bindCall j U hin hb happ hQ =>
    rw [PMF.mem_support_pure_iff] at hs'
    subst hs'
    refine ⟨hInv.F_card, hInv.F_in_eq, ?_, hInv.recv_sub, hInv.input_eq,
      hInv.inVal_prov, ?_, hInv.echo_conf, hInv.echo_card, hInv.vote_conf,
      hInv.vote_backed, ?_⟩
    all_goals dsimp only
    · intro k
      by_cases hk : k = j
      · subst hk
        rw [Function.update_self]
        exact hInv.F_bind_eq k
      · rw [Function.update_of_ne hk]
        exact hInv.F_bind_eq k
    · intro k U' hU'
      by_cases hk : k = j
      · subst hk
        rw [Function.update_self] at hU'
        have hU0 : (s.brbBind k).val = some U' := hU'
        rcases hInv.bindVal_prov k U' hU0 with hF | hin'
        · exact Or.inl hF
        · rw [hb] at hin'
          exact absurd hin' (by simp)
      · rw [Function.update_of_ne hk] at hU' ⊢
        exact hInv.bindVal_prov k U' hU'
    · intro j' hj U' hU'
      by_cases hk : j' = j
      · subst hk
        rw [Function.update_self] at hU'
        have : some U = some U' := hU'
        obtain rfl : U = U' := by injection this
        obtain ⟨Q, hQc, hQm⟩ := hQ
        exact ⟨Q, hQc, fun q hq => by
          obtain ⟨W, hW, -, hWU⟩ := hQm q hq
          exact ⟨W, hW, hWU⟩⟩
      · rw [Function.update_of_ne hk] at hU'
        exact hInv.bind_backed j' hj U' hU'
  | byz j m h =>
    rw [PMF.mem_support_pure_iff] at hs'
    subst hs'
    refine ⟨hInv.F_card, hInv.F_in_eq, hInv.F_bind_eq, ?_, hInv.input_eq,
      hInv.inVal_prov, hInv.bindVal_prov, ?_, hInv.echo_card, ?_,
      hInv.vote_backed, hInv.bind_backed⟩
    all_goals dsimp only
    · intro i k x hx
      rw [SubState.mcast_recv] at hx
      rw [SubState.mem_mcast_sent]
      exact Or.inr (hInv.recv_sub i k hx)
    · intro j' hj A hA
      rw [SubState.mem_mcast_sent] at hA
      rw [SubState.mcast_proc]
      rcases hA with ⟨rfl, -⟩ | hold
      · exact absurd h hj
      · exact hInv.echo_conf j' hj A hold
    · intro j' hj W hW
      rw [SubState.mem_mcast_sent] at hW
      rw [SubState.mcast_proc]
      rcases hW with ⟨rfl, -⟩ | hold
      · exact absurd h hj
      · exact hInv.vote_conf j' hj W hold
  | ret id g hin hsub hQ hr =>
    rw [PMF.mem_support_pure_iff] at hs'
    subst hs'
    refine ⟨hInv.F_card, hInv.F_in_eq, hInv.F_bind_eq, ?_, ?_,
      hInv.inVal_prov, hInv.bindVal_prov, ?_, ?_, ?_, ?_, ?_⟩
    all_goals dsimp only
    · intro i k x hx
      rw [SubState.setProc_recv] at hx
      rw [SubState.setProc_sent]
      exact hInv.recv_sub i k hx
    · intro k
      by_cases hk : k = id
      · subst hk
        rw [SubState.setProc_proc_self]
        exact hInv.input_eq k
      · rw [SubState.setProc_proc_ne _ _ _ hk]
        exact hInv.input_eq k
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
      rw [show (s.ga.setProc id { s.ga.proc id with returned := true }).recv
          = s.ga.recv from SubState.setProc_recv ..]
      by_cases hk : j = id
      · subst hk
        rw [SubState.setProc_proc_self] at hW
        exact hInv.vote_backed j hj W hW
      · rw [SubState.setProc_proc_ne _ _ _ hk] at hW
        exact hInv.vote_backed j hj W hW
    · intro j hj U hU
      rw [show (s.ga.setProc id { s.ga.proc id with returned := true }).recv
          = s.ga.recv from SubState.setProc_recv ..]
      exact hInv.bind_backed j hj U hU
  | fail id =>
    rw [PMF.mem_support_pure_iff] at hs'
    subst hs'
    have hF : ∀ k, k ∉ (s.corruptAll P id).ga.F → k ∉ s.ga.F := by
      intro k hk hkF
      exact hk (SubState.corrupt_F_subset s.ga id hkF)
    refine ⟨SubState.corrupt_card_le s.ga id hInv.F_card, ?_, ?_, ?_, ?_,
      ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro k
      change ((s.brbIn k).corrupt P id).F = (s.ga.corrupt P id).F
      rw [BRB.SpecState.corrupt_F, SubState.corrupt_F, hInv.F_in_eq k]
    · intro k
      change ((s.brbBind k).corrupt P id).F = (s.ga.corrupt P id).F
      rw [BRB.SpecState.corrupt_F, SubState.corrupt_F, hInv.F_bind_eq k]
    · intro i k x hx
      rw [show (s.corruptAll P id).ga.recv = s.ga.recv from rfl] at hx
      rw [show (s.corruptAll P id).ga.sent = s.ga.sent from
        IdealState.corruptAll_ga_sent P id s]
      exact hInv.recv_sub i k hx
    · intro k
      rw [IdealState.corruptAll_brbIn_input, IdealState.corruptAll_ga_proc]
      exact hInv.input_eq k
    · intro k v hv
      rw [IdealState.corruptAll_brbIn_val] at hv
      rw [IdealState.corruptAll_brbIn_input]
      rcases hInv.inVal_prov k v hv with hkF | hin
      · exact Or.inl (SubState.corrupt_F_subset s.ga id hkF)
      · exact Or.inr hin
    · intro k U hU
      rw [IdealState.corruptAll_brbBind_val] at hU
      rw [IdealState.corruptAll_brbBind_input]
      rcases hInv.bindVal_prov k U hU with hkF | hin
      · exact Or.inl (SubState.corrupt_F_subset s.ga id hkF)
      · exact Or.inr hin
    · intro j hj A hA
      rw [show (s.corruptAll P id).ga.sent = s.ga.sent from
        IdealState.corruptAll_ga_sent P id s] at hA
      rw [IdealState.corruptAll_ga_proc]
      exact hInv.echo_conf j (hF j hj) A hA
    · intro j hj A hA
      rw [IdealState.corruptAll_ga_proc] at hA
      exact hInv.echo_card j (hF j hj) A hA
    · intro j hj W hW
      rw [show (s.corruptAll P id).ga.sent = s.ga.sent from
        IdealState.corruptAll_ga_sent P id s] at hW
      rw [IdealState.corruptAll_ga_proc]
      exact hInv.vote_conf j (hF j hj) W hW
    · intro j hj W hW
      rw [IdealState.corruptAll_ga_proc] at hW
      rw [show (s.corruptAll P id).ga.recv = s.ga.recv from rfl]
      exact hInv.vote_backed j (hF j hj) W hW
    · intro j hj U hU
      rw [IdealState.corruptAll_brbBind_input] at hU
      rw [show (s.corruptAll P id).ga.recv = s.ga.recv from rfl]
      exact hInv.bind_backed j (hF j hj) U hU


/-! ### The approval of an echo field -/

/-- Committed input entries are write-once, so `approved` is monotone along
every rule. -/
theorem approved_mono {s s' : IdealState P.n X} {l : Lab P.n X}
    {μ : PMF (IdealState P.n X)} (hstep : IdealStep P s l μ)
    (hs' : s' ∈ μ.support) {A : APSet P.n X} (h : s.approved A) : s'.approved A := by
  have key : ∀ t : IdealState P.n X,
      (∀ k v, (s.brbIn k).val = some v → (t.brbIn k).val = some v) → t.approved A :=
    fun t ht p hp => ht p.1 p.2 (h p hp)
  cases hstep with
  | call id x hc =>
      rw [PMF.mem_support_pure_iff] at hs'; subst hs'
      refine key _ (fun k v hv => ?_)
      dsimp only
      by_cases hk : k = id
      · subst hk; rw [Function.update_self]; exact hv
      · rw [Function.update_of_ne hk]; exact hv
  | commitIn k v hv hm =>
      rw [PMF.mem_support_pure_iff] at hs'; subst hs'
      refine key _ (fun k' v' hv' => ?_)
      dsimp only
      by_cases hk : k' = k
      · subst hk; rw [hv] at hv'; exact absurd hv' (by simp)
      · rw [Function.update_of_ne hk]; exact hv'
  | fail id =>
      rw [PMF.mem_support_pure_iff] at hs'; subst hs'
      refine key _ (fun k v hv => ?_)
      rw [IdealState.corruptAll_brbIn_val]; exact hv
  | _ => rw [PMF.mem_support_pure_iff] at hs'; subst hs'; exact h

omit [DecidableEq X] in
/-- The `ECHO` fields of the initial state are empty. -/
theorem echoAppr_initial :
    ∀ (j : Fin P.n) (A : APSet P.n X),
      ((IdealState.initial P.n X).ga.proc j).sentEcho = some A →
        (IdealState.initial P.n X).approved A := by
  intro j A hA
  simp [IdealState.initial, PRec.initial] at hA

/-- **The approval of an `ECHO` field is inductive**: only `IdealStep.echo`
writes the field, and its guard is the approval of the payload it writes. -/
theorem echoAppr_step {s s' : IdealState P.n X} {l : Lab P.n X}
    {μ : PMF (IdealState P.n X)}
    (hEA : ∀ (j : Fin P.n) (A : APSet P.n X),
      (s.ga.proc j).sentEcho = some A → s.approved A)
    (hstep : IdealStep P s l μ) (hs' : s' ∈ μ.support) :
    ∀ (j : Fin P.n) (A : APSet P.n X),
      (s'.ga.proc j).sentEcho = some A → s'.approved A := by
  intro j A hA
  refine approved_mono hstep hs' ?_
  cases hstep with
  | call id x hc =>
      rw [PMF.mem_support_pure_iff] at hs'; subst hs'
      refine hEA j A ?_
      dsimp only at hA
      rw [SubState.proc_setProc] at hA
      by_cases hk : j = id
      · subst hk; rw [if_pos rfl] at hA; exact hA
      · rw [if_neg hk] at hA; exact hA
  | echo j₀ A₀ hin happ hcard hsend =>
      rw [PMF.mem_support_pure_iff] at hs'; subst hs'
      dsimp only at hA
      rw [SubState.mcast_proc, SubState.proc_setProc] at hA
      by_cases hk : j = j₀
      · subst hk; rw [if_pos rfl] at hA
        obtain rfl : A₀ = A := Option.some.inj hA
        exact happ
      · rw [if_neg hk] at hA; exact hEA j A hA
  | vote j₀ U hin happ hQ hsend =>
      rw [PMF.mem_support_pure_iff] at hs'; subst hs'
      refine hEA j A ?_
      dsimp only at hA
      rw [SubState.mcast_proc, SubState.proc_setProc] at hA
      by_cases hk : j = j₀
      · subst hk; rw [if_pos rfl] at hA; exact hA
      · rw [if_neg hk] at hA; exact hA
  | ret id g hin hsub hQ hr =>
      rw [PMF.mem_support_pure_iff] at hs'; subst hs'
      refine hEA j A ?_
      dsimp only at hA
      rw [SubState.proc_setProc] at hA
      by_cases hk : j = id
      · subst hk; rw [if_pos rfl] at hA; exact hA
      · rw [if_neg hk] at hA; exact hA
  | deliver i k m hm =>
      rw [PMF.mem_support_pure_iff] at hs'; subst hs'
      refine hEA j A ?_
      dsimp only at hA
      rw [SubState.recvMsg_proc] at hA; exact hA
  | byz k m hk =>
      rw [PMF.mem_support_pure_iff] at hs'; subst hs'
      refine hEA j A ?_
      dsimp only at hA
      rw [SubState.mcast_proc] at hA; exact hA
  | fail id =>
      rw [PMF.mem_support_pure_iff] at hs'; subst hs'
      exact hEA j A hA
  | _ => rw [PMF.mem_support_pure_iff] at hs'; subst hs'; exact hEA j A hA

/-! ### The invariant -/

/-- **The gather-over-BRB invariant**: the conformance clauses, together with
the approval of every `ECHO` field. -/
structure IdealInv (P : Params) (s : IdealState P.n X) : Prop extends IdealConf P s where
  /-- The payload set in a process's `ECHO` field consists of committed
  input-BRB entries. No honesty side condition: only `IdealStep.echo` writes
  the field, and its guard holds of a corrupted sender too. -/
  echo_appr : ∀ (j : Fin P.n) (A : APSet P.n X),
    (s.ga.proc j).sentEcho = some A → s.approved A

omit [DecidableEq X] in
/-- The invariant holds initially. -/
theorem IdealInv.initial : IdealInv P (IdealState.initial P.n X) :=
  ⟨IdealConf.initial, echoAppr_initial⟩

/-- The invariant is preserved by every step. -/
theorem IdealInv.step {s : IdealState P.n X} {l : Lab P.n X}
    {μ : PMF (IdealState P.n X)} (hInv : IdealInv P s) (hstep : IdealStep P s l μ)
    {s' : IdealState P.n X} (hs' : s' ∈ μ.support) : IdealInv P s' :=
  ⟨hInv.toIdealConf.step hstep hs', echoAppr_step hInv.echo_appr hstep hs'⟩

/-! ### The incidence on the network state -/

section Incidence

variable {w : SubState P.n (PRec P.n X) (GaMsg P.n X)}

omit [DecidableEq X] in
theorem mem_honest {j : Fin P.n} : j ∈ honest w ↔ j ∉ w.F := by
  simp [honest]

omit [DecidableEq X] in
/-- There are `n − |F|` processes outside `F`. -/
theorem card_honest : (honest w).card = P.n - w.F.card := by
  have h : honest w = w.Fᶜ := by rw [honest, Finset.compl_eq_univ_sdiff]
  rw [h, Finset.card_compl, Fintype.card_fin]

open scoped Classical in
omit [DecidableEq X] in
theorem mem_dominatedBy {q j : Fin P.n} :
    j ∈ dominatedBy w q ↔ ∀ W : APSet P.n X, GaMsg.vote W ∈ w.sent q →
      ∃ A, GaMsg.echo A ∈ w.sent j ∧ A ⊆ W := by
  rw [dominatedBy, Finset.mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ _, h⟩⟩

omit [DecidableEq X] in
/-- The `ECHO` payload of a process outside `F` is the one its `sentEcho`
field holds. -/
theorem echoOf_eq {s : IdealState P.n X} (hInv : IdealInv P s) {j : Fin P.n}
    (hj : j ∉ s.ga.F) {A : APSet P.n X} (hA : GaMsg.echo A ∈ s.ga.sent j) :
    echoOf s.ga j = A := by
  classical
  have hex : ∃ A : APSet P.n X, GaMsg.echo A ∈ s.ga.sent j := ⟨A, hA⟩
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
    (hq : q ∉ s.ga.F) : P.n - P.f ≤ (dominatedBy s.ga q).card := by
  classical
  by_cases hv : ∃ W : APSet P.n X, GaMsg.vote W ∈ s.ga.sent q
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
  · have : dominatedBy s.ga q = Finset.univ := by
      refine Finset.eq_univ_iff_forall.mpr fun j => ?_
      rw [mem_dominatedBy]
      intro W hW
      exact absurd ⟨W, hW⟩ hv
    rw [this, Finset.card_univ, Fintype.card_fin]
    omega

open scoped Classical in
omit [DecidableEq X] in
theorem honest_filter_dominatedBy {q : Fin P.n} :
    (honest w).filter (fun j => j ∈ dominatedBy w q) = dominatedBy w q \ w.F := by
  ext j
  simp only [Finset.mem_filter, Finset.mem_sdiff, mem_honest]
  tauto

open scoped Classical in
omit [DecidableEq X] in
/-- A row of a process outside `F` meets the processes outside `F` in at
least `n − f − |F|` of them. -/
theorem dominatedBy_honest_card {s : IdealState P.n X} (hInv : IdealInv P s)
    {q : Fin P.n} (hq : q ∉ s.ga.F) :
    P.n - P.f - s.ga.F.card ≤
      ((honest s.ga).filter (fun j => j ∈ dominatedBy s.ga q)).card := by
  rw [honest_filter_dominatedBy]
  have h1 := Finset.le_card_sdiff s.ga.F (dominatedBy s.ga q)
  have h2 := dominatedBy_card hInv hq
  omega

open scoped Classical in
omit [DecidableEq X] in
/-- The two readings of the incidence agree: summing the rows outside `F`
over the columns outside `F` is summing the columns over the rows. -/
theorem sum_dominatedBy (w : SubState P.n (PRec P.n X) (GaMsg P.n X)) :
    ∑ q ∈ honest w, ((honest w).filter (fun j => j ∈ dominatedBy w q)).card
      = ∑ j ∈ honest w, (dominators w j).card := by
  simp only [dominators, Finset.card_filter]
  exact Finset.sum_comm

open scoped Classical in
omit [DecidableEq X] in
/-- **The pigeonhole.** Some sender outside `F` has at least `n − f − |F|`
dominators. -/
theorem exists_dominators {s : IdealState P.n X} (hInv : IdealInv P s) :
    ∃ j₀, j₀ ∈ honest s.ga ∧ P.n - P.f - s.ga.F.card ≤ (dominators s.ga j₀).card := by
  by_contra hc
  push_neg at hc
  have hF := hInv.F_card
  have hf := P.hf
  set H : Finset (Fin P.n) := honest s.ga with hH
  set m : ℕ := P.n - P.f - s.ga.F.card with hm
  have hHcard : H.card = P.n - s.ga.F.card := card_honest
  have hpos : 0 < H.card := by omega
  have hlow : ∀ q ∈ H, m ≤ ((honest s.ga).filter (fun j => j ∈ dominatedBy s.ga q)).card :=
    fun q hq => dominatedBy_honest_card hInv (mem_honest.mp (hH ▸ hq))
  have hsum2 : H.card * m
      ≤ ∑ q ∈ H, ((honest s.ga).filter (fun j => j ∈ dominatedBy s.ga q)).card := by
    simpa [smul_eq_mul] using Finset.card_nsmul_le_sum H _ m hlow
  rw [sum_dominatedBy, ← hH] at hsum2
  have hle : ∀ j ∈ H, (dominators s.ga j).card ≤ m - 1 := fun j hj => by
    have := hc j (hH ▸ hj); omega
  have hsum1 : ∑ j ∈ H, (dominators s.ga j).card ≤ H.card * (m - 1) := by
    simpa [smul_eq_mul] using Finset.sum_le_card_nsmul H _ (m - 1) hle
  have hstrict : H.card * (m - 1) < H.card * m :=
    mul_lt_mul_of_pos_left (by omega) hpos
  omega

end Incidence

/-! ### The single core -/

open scoped Classical in
omit [DecidableEq X] in
/-- **The transfer.** A sender outside `F` with at least `f + 1` dominators
has its `ECHO` payload below every committed `BIND` payload of a process
outside `F`: the dominators meet that payload's backing `VOTE` quorum of
`n − f`, and the meeting process's write-once `VOTE` payload lies above the
`ECHO` payload and below the `BIND` payload. -/
theorem transfer {s : IdealState P.n X} (hInv : IdealInv P s) {j₀ : Fin P.n}
    (hj₀ : j₀ ∉ s.ga.F) (hcnt : P.f + 1 ≤ (dominators s.ga j₀).card)
    {k : Fin P.n} (hk : k ∉ s.ga.F) {U : APSet P.n X}
    (hU : (s.brbBind k).val = some U) :
    ∃ A, GaMsg.echo A ∈ s.ga.sent j₀ ∧ P.n - P.f ≤ A.card ∧ A ⊆ U := by
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
/-- The core is the write-once `ECHO` payload of a sender outside `F` with
at least `f + 1` dominators, as soon as some process outside `F` holds a
committed `BIND` payload. -/
theorem core_witness {s : IdealState P.n X} (hInv : IdealInv P s)
    {k₀ : Fin P.n} (hk₀ : k₀ ∉ s.ga.F) {U₀ : APSet P.n X}
    (hU₀ : (s.brbBind k₀).val = some U₀) :
    ∃ j₁, j₁ ∉ s.ga.F ∧ P.f + 1 ≤ (dominators s.ga j₁).card ∧
      GaMsg.echo (coreOf P s.ga) ∈ s.ga.sent j₁ ∧
      (s.ga.proc j₁).sentEcho = some (coreOf P s.ga) := by
  have hF := hInv.F_card
  have hf := P.hf
  have hex : ∃ j, j ∈ honest s.ga ∧ P.f + 1 ≤ (dominators s.ga j).card := by
    obtain ⟨j₀, hj₀, hcnt⟩ := exists_dominators hInv
    exact ⟨j₀, hj₀, by omega⟩
  have hspec := hex.choose_spec
  have hj₁F : hex.choose ∉ s.ga.F := mem_honest.mp hspec.1
  obtain ⟨A, hA, -, -⟩ := transfer hInv hj₁F hspec.2 hk₀ hU₀
  have hcore : coreOf P s.ga = A := by
    rw [coreOf, dif_pos hex]
    exact echoOf_eq hInv hj₁F hA
  exact ⟨hex.choose, hj₁F, hspec.2, by rw [hcore]; exact hA,
    by rw [hcore]; exact hInv.echo_conf _ hj₁F A hA⟩

omit [DecidableEq X] in
/-- **The single core.** Once some process outside `F` holds a committed
`BIND` payload, the core has at least `n − f` entries and lies below the
committed `BIND` payload of every process outside `F`. -/
theorem single_core {s : IdealState P.n X} (hInv : IdealInv P s)
    {k₀ : Fin P.n} (hk₀ : k₀ ∉ s.ga.F) {U₀ : APSet P.n X}
    (hU₀ : (s.brbBind k₀).val = some U₀) :
    P.n - P.f ≤ (coreOf P s.ga).card ∧
      ∀ k ∉ s.ga.F, ∀ U : APSet P.n X, (s.brbBind k).val = some U →
        coreOf P s.ga ⊆ U := by
  obtain ⟨j₁, hj₁F, hcnt, hsent, hslot⟩ := core_witness hInv hk₀ hU₀
  refine ⟨hInv.echo_card j₁ hj₁F _ hslot, ?_⟩
  intro k hk U hU
  obtain ⟨A, hA, -, hAU⟩ := transfer hInv hj₁F hcnt hk hU
  have hEq : A = coreOf P s.ga := by
    have h1 := hInv.echo_conf j₁ hj₁F A hA
    rw [hslot] at h1
    exact (Option.some.inj h1).symm
  rw [← hEq]
  exact hAU

omit [DecidableEq X] in
/-- **The core is approved**: its entries are committed input-BRB entries,
the `ECHO` field it comes from carrying only such entries. -/
theorem single_core_approved {s : IdealState P.n X} (hInv : IdealInv P s)
    {k₀ : Fin P.n} (hk₀ : k₀ ∉ s.ga.F) {U₀ : APSet P.n X}
    (hU₀ : (s.brbBind k₀).val = some U₀) :
    s.approved (coreOf P s.ga) := by
  obtain ⟨j₁, -, -, -, hslot⟩ := core_witness hInv hk₀ hU₀
  exact hInv.echo_appr j₁ _ hslot

/-! ### The freeze certificate -/

open scoped Classical in
/-- The coordinates holding a committed `BIND` payload above `C`. The
condition is blind to `F`. -/
noncomputable def bindAbove (s : IdealState P.n X) (C : APSet P.n X) :
    Finset (Fin P.n) :=
  Finset.univ.filter (fun q => ∃ U, (s.brbBind q).val = some U ∧ C ⊆ U)

open scoped Classical in
theorem mem_bindAbove {s : IdealState P.n X} {C : APSet P.n X} {q : Fin P.n} :
    q ∈ bindAbove s C ↔ ∃ U, (s.brbBind q).val = some U ∧ C ⊆ U := by
  rw [bindAbove, Finset.mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ _, h⟩⟩

/-- A committed `BIND` payload is never rewritten. -/
theorem bindVal_mono {s s' : IdealState P.n X} {l : Lab P.n X}
    {μ : PMF (IdealState P.n X)} (hstep : IdealStep P s l μ) (hs' : s' ∈ μ.support)
    {q : Fin P.n} {U : APSet P.n X} (h : (s.brbBind q).val = some U) :
    (s'.brbBind q).val = some U := by
  cases hstep with
  | commitBind k U' hv hm =>
      rw [PMF.mem_support_pure_iff] at hs'; subst hs'
      dsimp only
      by_cases hk : q = k
      · subst hk; rw [hv] at h; exact absurd h (by simp)
      · rw [Function.update_of_ne hk]; exact h
  | bindCall j U' hin hb happ hQ =>
      rw [PMF.mem_support_pure_iff] at hs'; subst hs'
      dsimp only
      by_cases hk : q = j
      · subst hk; rw [Function.update_self]; exact h
      · rw [Function.update_of_ne hk]; exact h
  | fail id =>
      rw [PMF.mem_support_pure_iff] at hs'; subst hs'
      rw [IdealState.corruptAll_brbBind_val]; exact h
  | _ => rw [PMF.mem_support_pure_iff] at hs'; subst hs'; exact h

/-- **The certificate is monotone.** The coordinates holding a committed
`BIND` payload above `C` only accumulate, under every rule and every
corruption. -/
theorem bindAbove_mono {s s' : IdealState P.n X} {l : Lab P.n X}
    {μ : PMF (IdealState P.n X)} (hstep : IdealStep P s l μ) (hs' : s' ∈ μ.support)
    (C : APSet P.n X) : bindAbove s C ⊆ bindAbove s' C := by
  intro q hq
  rw [mem_bindAbove] at hq ⊢
  obtain ⟨U, hU, hCU⟩ := hq
  exact ⟨U, bindVal_mono hstep hs' hU, hCU⟩

/-- **The freeze.** At a state where an `n − f` quorum of coordinates holds
committed `BIND` payloads, the core has at least `n − f` entries, its entries
are committed input-BRB entries, and at least `f + 1` coordinates hold a
committed `BIND` payload above it. The last is the certificate that holds the
returns after the first to this core: it is blind to `F` and monotone
(`bindAbove_mono`), and an `n − f` return quorum meets it. -/
theorem coreOf_freeze {s : IdealState P.n X} (hInv : IdealInv P s)
    {Q : Finset (Fin P.n)} (hQc : P.n - P.f ≤ Q.card)
    (hQm : ∀ q ∈ Q, ∃ U : APSet P.n X, (s.brbBind q).val = some U) :
    P.n - P.f ≤ (coreOf P s.ga).card ∧ s.approved (coreOf P s.ga) ∧
      P.f + 1 ≤ (bindAbove s (coreOf P s.ga)).card := by
  classical
  have hF := hInv.F_card
  have hf := P.hf
  have hH : P.f + 1 ≤ (Q \ s.ga.F).card := by
    have h1 := Finset.le_card_sdiff s.ga.F Q
    omega
  obtain ⟨H, hHsub, hHcard⟩ := Finset.exists_subset_card_eq hH
  have hHQ : ∀ q ∈ H, q ∈ Q := fun q hq => (Finset.mem_sdiff.mp (hHsub hq)).1
  have hHF : ∀ q ∈ H, q ∉ s.ga.F := fun q hq => (Finset.mem_sdiff.mp (hHsub hq)).2
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
