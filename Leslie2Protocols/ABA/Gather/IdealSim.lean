/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sathiya / Claude
-/

import Leslie2Protocols.ABA.Gather.Ideal
import Leslie2Protocols.Framework.FamilySim
import Leslie2Protocols.Framework.WeakBurst

/-!
# The gather refinement: the aggregation ladder implements the specification

`Gather.gatherCore`: the gather-over-BRB-specification instance
(`ABA/Gather/Ideal.lean`) forward-simulates the gather specification
(`ABA/Gather/Spec.lean`), along `Gather.CoreRel`.

The specification's abstract content is committed lazily, in the
kill-on-demand style: the committed entries (`val`) and the core family
(`cores`) are both written inside the return burst, at the first return that
needs them. The burst is

```
commit*  ;  bindCores?  ;  ret
```

built by recursion with `weakLStep_tauCons` — one `commit` per entry of the
returned map not yet committed, the family freeze if the instance has none
yet, then the return.

* Entry commits are licensed by the invariant's provenance clause: a
  committed input-BRB entry of an honest process is that process's input,
  which the relation identifies with the specification's call record.
* The fresh family is the bind-BRB payloads of `f + 1` honest members of the
  returner's quorum — a quorum of `n − f` holds at least `n − 2f ≥ f + 1`
  honest members. Any two members share an honest voter of both backing
  quorums, whose write-once `VOTE` payload of at least `n − f` entries lies
  in both — the pairwise guard of `bindCores`.
* Against a family frozen earlier, a return is matched through the count
  `CoreRel.cores_cert`: at least `f + 1` bind-BRB instances hold members as
  their committed payloads. The count is `F`-blind and monotone — committed
  payloads are written once — so it survives every rule and every
  corruption; the returner's quorum of `n − f` meets it, and the committed
  payload identifies the member.

The second point is where the `BIND`-by-reliable-broadcast design of the
implementation pays: the count pins members to *committed* payloads, which a
sender corrupted after the freeze cannot rewrite.
-/

namespace PLTS
namespace ABA
namespace Gather

variable {X : Type} [DecidableEq X] {P : Params}

/-! ### The invariant -/

/-- The gather-over-BRB invariant. The `*_conf` clauses tie an honest
sender's pool to its write-once slot, the `*_backed` clauses tie the slots to
the receipts that justified them, and the provenance clauses are the BRB
commit guards, recorded per coordinate. -/
structure IdealInv (P : Params) (s : IdealState P.n X) : Prop where
  /-- The corruption budget. -/
  F_card : s.ga.F.card ≤ P.f
  /-- The input-BRB corrupted sets are in lockstep with the fabric's. -/
  F_in_eq : ∀ k, (s.brbIn k).F = s.ga.F
  /-- The bind-BRB corrupted sets are in lockstep with the fabric's. -/
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
  /-- An honest sender's pooled `ECHO` matches its write-once slot. -/
  echo_conf : ∀ j ∉ s.ga.F, ∀ A, GaMsg.echo A ∈ s.ga.sent j →
    (s.ga.proc j).sentEcho = some A
  /-- An honest echo payload has at least `n − f` entries. -/
  echo_card : ∀ j ∉ s.ga.F, ∀ A, (s.ga.proc j).sentEcho = some A →
    P.n - P.f ≤ A.card
  /-- An honest sender's pooled `VOTE` matches its write-once slot. -/
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
/-- The invariant holds initially. -/
theorem IdealInv.initial : IdealInv P (IdealState.initial P.n X) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [IdealState.initial, PRec.initial, BRB.SpecState.initial]

/-- The invariant is preserved by every step. -/
theorem IdealInv.step {s : IdealState P.n X} {l : Lab P.n X}
    {μ : PMF (IdealState P.n X)} (hInv : IdealInv P s) (hstep : IdealStep P s l μ)
    {s' : IdealState P.n X} (hs' : s' ∈ μ.support) : IdealInv P s' := by
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

/-! ### The harvest -/

/-- A quorum contains an honest member. -/
theorem exists_honest_quorum_mem {F Q : Finset (Fin P.n)} (hF : F.card ≤ P.f)
    (hQ : P.n - P.f ≤ Q.card) : ∃ q ∈ Q, q ∉ F :=
  SubState.exists_honest_of_card_lt (lt_of_le_of_lt hF (lt_of_lt_of_le P.f_lt_n_sub_f hQ))

omit [DecidableEq X] in
/-- An honest vote payload has at least `n − f` entries: its backing quorum
contains an honest echoer, whose write-once payload of at least `n − f`
entries it contains. -/
theorem vote_card {s : IdealState P.n X} (hInv : IdealInv P s) {j : Fin P.n}
    (hj : j ∉ s.ga.F) {W : APSet P.n X} (hW : (s.ga.proc j).sentVote = some W) :
    P.n - P.f ≤ W.card := by
  obtain ⟨Q, hQc, hQ⟩ := hInv.vote_backed j hj W hW
  obtain ⟨q, hqQ, hqF⟩ := exists_honest_quorum_mem hInv.F_card hQc
  obtain ⟨A, hA, hAW⟩ := hQ q hqQ
  have hsent := hInv.recv_sub j q hA
  have hslot := hInv.echo_conf q hqF A hsent
  exact le_trans (hInv.echo_card q hqF A hslot) (Finset.card_le_card hAW)

/-- Two honest contributed bind payloads share at least `n − f` entries: the
backing vote quorums share an honest voter, whose write-once payload lies in
both. -/
theorem bindInput_inter {s : IdealState P.n X} (hInv : IdealInv P s)
    {j j' : Fin P.n} (hj : j ∉ s.ga.F) (hj' : j' ∉ s.ga.F)
    {U U' : APSet P.n X} (hU : (s.brbBind j).input = some U)
    (hU' : (s.brbBind j').input = some U') :
    P.n - P.f ≤ (U ∩ U').card := by
  obtain ⟨Q, hQc, hQ⟩ := hInv.bind_backed j hj U hU
  obtain ⟨Q', hQ'c, hQ'⟩ := hInv.bind_backed j' hj' U' hU'
  obtain ⟨q, hqQ, hqQ', hqF⟩ := SubState.exists_honest_inter hInv.F_card hQc hQ'c
  obtain ⟨W, hW, hWU⟩ := hQ q hqQ
  obtain ⟨W', hW', hW'U⟩ := hQ' q hqQ'
  have h1 := hInv.vote_conf q hqF W (hInv.recv_sub j q hW)
  have h2 := hInv.vote_conf q hqF W' (hInv.recv_sub j' q hW')
  rw [h1] at h2
  obtain rfl : W = W' := by injection h2
  have hsub : W ⊆ U ∩ U' := Finset.subset_inter hWU hW'U
  exact le_trans (vote_card hInv hqF h1) (Finset.card_le_card hsub)

/-- Two honest committed bind payloads share at least `n − f` entries. -/
theorem bindVal_inter {s : IdealState P.n X} (hInv : IdealInv P s)
    {j j' : Fin P.n} (hj : j ∉ s.ga.F) (hj' : j' ∉ s.ga.F)
    {U U' : APSet P.n X} (hU : (s.brbBind j).val = some U)
    (hU' : (s.brbBind j').val = some U') :
    P.n - P.f ≤ (U ∩ U').card := by
  rcases hInv.bindVal_prov j U hU with hF | hin
  · exact absurd hF hj
  rcases hInv.bindVal_prov j' U' hU' with hF | hin'
  · exact absurd hF hj'
  exact bindInput_inter hInv hj hj' hin hin'

/-! ### The relation -/

/-- The gather refinement relation. `val_cert` bounds the specification's
committed entries by the input-BRB commitments; `cores_cert` is the `F`-blind
monotone count pinning the frozen family to committed bind payloads. -/
structure CoreRel (P : Params) (s : IdealState P.n X) (t : SpecState P.n X) : Prop where
  /-- The implementation invariant. -/
  inv : IdealInv P s
  /-- The call records agree. -/
  call_eq : ∀ k, t.call k = (s.ga.proc k).input
  /-- The return flags agree. -/
  ret_eq : ∀ id, t.ret id = (s.ga.proc id).returned
  /-- The corrupted sets agree. -/
  F_eq : t.F = s.ga.F
  /-- A committed specification entry is a committed input-BRB entry. -/
  val_cert : ∀ k v, t.val k = some v → (s.brbIn k).val = some v
  /-- At least `f + 1` bind-BRB instances hold members of the frozen family
  as their committed payloads. -/
  cores_cert : ∀ Cs, t.cores = some Cs →
    P.f + 1 ≤ (Finset.univ.filter
      (fun q => ∃ U ∈ Cs, (s.brbBind q).val = some U)).card

/-- The relation holds initially. -/
theorem coreRel_init :
    CoreRel P (IdealState.initial P.n X) (SpecState.initial P.n X) := by
  refine ⟨IdealInv.initial, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [IdealState.initial, SpecState.initial, PRec.initial]

/-- **Broadcast compatibility**: the relation is preserved by corrupting both
sides at once. -/
theorem coreRel_corrupt {s : IdealState P.n X} {t : SpecState P.n X}
    (hR : CoreRel P s t) (id : Fin P.n) :
    CoreRel P (s.corruptAll P id) (t.corrupt P id) := by
  refine ⟨hR.inv.step (IdealStep.fail s id) (by rw [PMF.mem_support_pure_iff]),
    ?_, ?_, ?_, ?_, ?_⟩
  · intro k
    rw [corrupt_call, IdealState.corruptAll_ga_proc]
    exact hR.call_eq k
  · intro k
    rw [corrupt_ret, IdealState.corruptAll_ga_proc]
    exact hR.ret_eq k
  · show (t.corrupt P id).F = (s.ga.corrupt P id).F
    rw [SpecState.corrupt_F, SubState.corrupt_F, hR.F_eq]
  · intro k v hv
    rw [corrupt_val] at hv
    rw [IdealState.corruptAll_brbIn_val]
    exact hR.val_cert k v hv
  · intro Cs hCs
    rw [corrupt_cores] at hCs
    have := hR.cores_cert Cs hCs
    refine le_trans this (Finset.card_le_card ?_)
    intro q hq
    rw [Finset.mem_filter] at hq ⊢
    obtain ⟨-, U, hU, hval⟩ := hq
    exact ⟨Finset.mem_univ q, U, hU, by rw [IdealState.corruptAll_brbBind_val]; exact hval⟩

/-! ### The return burst

The specification's committed entries are written one at a time, by a chain
of `commit` steps folded over a list of processes; `commitOne` commits one
entry of the returned map if it is not committed yet, and `commitList` folds
it. The chain is prepended to the answering weak step by recursion with
`weakLStep_tauCons`. -/

section Burst

variable (g : Fin P.n → Option X)

/-- Commit `g`'s entry at `k`, if `g` has one and it is uncommitted. -/
private def commitOne (k : Fin P.n) (t : SpecState P.n X) : SpecState P.n X :=
  if h : (g k).isSome ∧ t.val k = none
  then { t with val := Function.update t.val k (some ((g k).get h.1)) }
  else t

private theorem commitOne_call (k : Fin P.n) (t : SpecState P.n X) :
    (commitOne g k t).call = t.call := by
  unfold commitOne; split <;> rfl

private theorem commitOne_F (k : Fin P.n) (t : SpecState P.n X) :
    (commitOne g k t).F = t.F := by
  unfold commitOne; split <;> rfl

private theorem commitOne_ret (k : Fin P.n) (t : SpecState P.n X) :
    (commitOne g k t).ret = t.ret := by
  unfold commitOne; split <;> rfl

private theorem commitOne_cores (k : Fin P.n) (t : SpecState P.n X) :
    (commitOne g k t).cores = t.cores := by
  unfold commitOne; split <;> rfl

private theorem commitOne_val_mono {k : Fin P.n} {t : SpecState P.n X}
    {k' : Fin P.n} {v : X} (h : t.val k' = some v) :
    (commitOne g k t).val k' = some v := by
  unfold commitOne
  split
  · next hc =>
    by_cases hk : k' = k
    · subst hk
      rw [hc.2] at h
      exact absurd h (by simp)
    · show Function.update t.val k _ k' = some v
      rw [Function.update_of_ne hk]
      exact h
  · exact h

private theorem commitOne_val_new {k : Fin P.n} {t : SpecState P.n X}
    {k' : Fin P.n} {v : X} (h : (commitOne g k t).val k' = some v) :
    t.val k' = some v ∨ g k' = some v := by
  unfold commitOne at h
  split at h
  · next hc =>
    by_cases hk : k' = k
    · subst hk
      rw [show ({ t with val := Function.update t.val k' (some ((g k').get hc.1)) }
          : SpecState P.n X).val k' = Function.update t.val k' (some ((g k').get hc.1)) k'
          from rfl, Function.update_self] at h
      right
      obtain rfl : (g k').get hc.1 = v := by injection h
      exact (Option.some_get hc.1).symm
    · rw [show ({ t with val := Function.update t.val k (some ((g k).get hc.1)) }
          : SpecState P.n X).val k' = Function.update t.val k (some ((g k).get hc.1)) k'
          from rfl, Function.update_of_ne hk] at h
      exact Or.inl h
  · exact Or.inl h

private theorem commitOne_covers {k : Fin P.n} {t : SpecState P.n X} {x : X}
    (hx : g k = some x) (hpre : ∀ y, t.val k = some y → y = x) :
    (commitOne g k t).val k = some x := by
  unfold commitOne
  split
  · next hc =>
    show Function.update t.val k (some ((g k).get hc.1)) k = some x
    rw [Function.update_self]
    congr 1
    rw [Option.get_of_mem hc.1 hx]
  · next hc =>
    rw [not_and_or] at hc
    rcases hc with hc | hc
    · rw [hx] at hc
      simp at hc
    · rcases hval : t.val k with _ | y
      · exact absurd hval hc
      · rw [hpre y hval]

/-- One `commitOne` is the identity or a genuine `commit` step. -/
private theorem commitOne_step (k : Fin P.n) (t : SpecState P.n X)
    (hm : ∀ x, g k = some x → t.val k = none → k ∈ t.F ∨ t.call k = some x) :
    commitOne g k t = t ∨
      Step P t Lab.tau (PMF.pure (commitOne g k t)) := by
  unfold commitOne
  split
  · next hc =>
    right
    obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp hc.1
    have hget : (g k).get hc.1 = x := Option.get_of_mem hc.1 hx
    rw [hget]
    exact Step.commit t k x hc.2 (hm x hx hc.2)
  · exact Or.inl rfl

/-- Fold `commitOne` over a list of processes. -/
private def commitList : List (Fin P.n) → SpecState P.n X → SpecState P.n X
  | [], t => t
  | k :: l, t => commitList l (commitOne g k t)

private theorem commitList_call :
    ∀ (l : List (Fin P.n)) (t : SpecState P.n X), (commitList g l t).call = t.call
  | [], _ => rfl
  | k :: l, t => by rw [commitList, commitList_call l, commitOne_call]

private theorem commitList_F :
    ∀ (l : List (Fin P.n)) (t : SpecState P.n X), (commitList g l t).F = t.F
  | [], _ => rfl
  | k :: l, t => by rw [commitList, commitList_F l, commitOne_F]

private theorem commitList_ret :
    ∀ (l : List (Fin P.n)) (t : SpecState P.n X), (commitList g l t).ret = t.ret
  | [], _ => rfl
  | k :: l, t => by rw [commitList, commitList_ret l, commitOne_ret]

private theorem commitList_cores :
    ∀ (l : List (Fin P.n)) (t : SpecState P.n X), (commitList g l t).cores = t.cores
  | [], _ => rfl
  | k :: l, t => by rw [commitList, commitList_cores l, commitOne_cores]

private theorem commitList_val_mono :
    ∀ (l : List (Fin P.n)) (t : SpecState P.n X) {k' : Fin P.n} {v : X},
      t.val k' = some v → (commitList g l t).val k' = some v
  | [], _, _, _, h => h
  | k :: l, t, _, _, h =>
    commitList_val_mono l (commitOne g k t) (commitOne_val_mono g h)

private theorem commitList_val_new :
    ∀ (l : List (Fin P.n)) (t : SpecState P.n X) {k' : Fin P.n} {v : X},
      (commitList g l t).val k' = some v → t.val k' = some v ∨ g k' = some v
  | [], _, _, _, h => Or.inl h
  | k :: l, t, _, _, h => by
    rcases commitList_val_new l (commitOne g k t) h with h' | h'
    · exact commitOne_val_new g h'
    · exact Or.inr h'

private theorem commitList_covers :
    ∀ (l : List (Fin P.n)) (t : SpecState P.n X),
      (∀ k y x, g k = some x → t.val k = some y → y = x) →
      ∀ k ∈ l, ∀ x, g k = some x → (commitList g l t).val k = some x
  | [], _, _, k, hk, _, _ => absurd hk (by simp)
  | k₀ :: l, t, hpre, k, hk, x, hx => by
    have hpre' : ∀ k' y x', g k' = some x' → (commitOne g k₀ t).val k' = some y → y = x' := by
      intro k' y x' hx' hy
      rcases commitOne_val_new g hy with h' | h'
      · exact hpre k' y x' hx' h'
      · rw [hx'] at h'
        injection h' with h''
        exact h''.symm
    rcases List.mem_cons.mp hk with rfl | hk'
    · exact commitList_val_mono g l _ (commitOne_covers g hx (fun y hy => hpre k y x hx hy))
    · exact commitList_covers l (commitOne g k₀ t) hpre' k hk' x hx

/-- Prepend the commit chain to an answering weak step. -/
private theorem weakLStep_after_commits {l₀ : Lab P.n X} {t' : SpecState P.n X} :
    ∀ (l : List (Fin P.n)) (t : SpecState P.n X),
      (∀ k ∈ l, ∀ x, g k = some x → t.val k = none → k ∈ t.F ∨ t.call k = some x) →
      (specInst P X).weakLStep (commitList g l t) l₀ t' →
      (specInst P X).weakLStep t l₀ t'
  | [], _, _, htail => htail
  | k :: rest, t, hg, htail => by
    rcases commitOne_step g k t (fun x hx hv => hg k (by simp) x hx hv) with heq | hstep
    · rw [show commitList g (k :: rest) t = commitList g rest t from by
        rw [commitList, heq]] at htail
      exact weakLStep_after_commits rest t
        (fun k' hk' => hg k' (List.mem_cons_of_mem k hk')) htail
    · refine System.weakLStep_tauCons hstep
        (weakLStep_after_commits rest (commitOne g k t) ?_ htail)
      intro k' hk' x hx hv
      have hvold : t.val k' = none := by
        rcases hval : t.val k' with _ | y
        · rfl
        · rw [commitOne_val_mono g hval] at hv
          exact absurd hv (by simp)
      have h := hg k' (List.mem_cons_of_mem k hk') x hx hvold
      rw [commitOne_F, commitOne_call]
      exact h

/-- The states of the genuine commits of `commitList`, as a list. -/
private def commitChain : List (Fin P.n) → SpecState P.n X → List (SpecState P.n X)
  | [], _ => []
  | k :: l, t =>
    if h : (g k).isSome ∧ t.val k = none
    then commitOne g k t :: commitChain l (commitOne g k t)
    else commitChain l t

private theorem commitChain_getLastD :
    ∀ (l : List (Fin P.n)) (t : SpecState P.n X),
      (commitChain g l t).getLastD t = commitList g l t
  | [], _ => rfl
  | k :: l, t => by
    rw [commitChain, commitList]
    split
    · next h =>
      rw [List.getLastD_cons, commitChain_getLastD l]
    · next h =>
      have hid : commitOne g k t = t := by
        unfold commitOne
        rw [dif_neg h]
      rw [hid, commitChain_getLastD l]

private theorem commitChain_isChain :
    ∀ (l : List (Fin P.n)) (t : SpecState P.n X),
      (∀ k ∈ l, ∀ x, g k = some x → t.val k = none → k ∈ t.F ∨ t.call k = some x) →
      List.IsChain (fun a b => Step P a Lab.tau (PMF.pure b)) (t :: commitChain g l t)
  | [], t, _ => List.isChain_singleton t
  | k :: l, t, hg => by
    rw [commitChain]
    split
    · next hc =>
      have hstep : Step P t Lab.tau (PMF.pure (commitOne g k t)) := by
        have hm := hg k (by simp) ((g k).get hc.1) (Option.some_get hc.1).symm hc.2
        unfold commitOne
        rw [dif_pos hc]
        exact Step.commit t k ((g k).get hc.1) hc.2 hm
      refine List.isChain_cons_cons.mpr ⟨hstep, commitChain_isChain l (commitOne g k t) ?_⟩
      intro k' hk' x hx hv
      have hvold : t.val k' = none := by
        rcases hval : t.val k' with _ | y
        · rfl
        · rw [commitOne_val_mono g hval] at hv
          exact absurd hv (by simp)
      have h := hg k' (List.mem_cons_of_mem k hk') x hx hvold
      rw [commitOne_F, commitOne_call]
      exact h
    · next hc =>
      have hid : commitOne g k t = t := by
        unfold commitOne
        rw [dif_neg hc]
      have := commitChain_isChain l (commitOne g k t)
        (fun k' hk' => by
          rw [hid]
          exact hg k' (List.mem_cons_of_mem k hk'))
      rwa [hid] at this

end Burst

/-! ### The return burst, as data

The whole return answer of the refinement, packaged as a τ-chain of
specification steps with the return guards at its end and the relation
restored across the pair of return effects — the shape a larger system that
embeds the gather specification's rows can replay without re-proving the
burst. -/

theorem retBurst {s : IdealState P.n X} {t : SpecState P.n X}
    (hR : CoreRel P s t) {id : Fin P.n} {g : Fin P.n → Option X}
    (hin : (s.ga.proc id).input ≠ none)
    (hsub : ∀ k x, g k = some x → (s.brbIn k).val = some x)
    (hQ : ∃ Q : Finset (Fin P.n), P.n - P.f ≤ Q.card ∧
      ∀ q ∈ Q, ∃ U, (s.brbBind q).val = some U ∧ APSet.subMap U g)
    (hr : (s.ga.proc id).returned = false) :
    ∃ (ts : List (SpecState P.n X)) (Cs : Finset (APSet P.n X)),
      List.IsChain (fun a b => Step P a Lab.tau (PMF.pure b)) (t :: ts) ∧
      (ts.getLastD t).cores = some Cs ∧
      (∃ U ∈ Cs, APSet.subMap U g) ∧
      (∀ k x, g k = some x → (ts.getLastD t).val k = some x) ∧
      (ts.getLastD t).ret id = false ∧
      CoreRel P { s with ga := s.ga.setProc id { s.ga.proc id with returned := true } }
        { ts.getLastD t with ret := Function.update (ts.getLastD t).ret id true } := by
  classical
  have hInv' : IdealInv P
      { s with ga := s.ga.setProc id { s.ga.proc id with returned := true } } :=
    hR.inv.step (IdealStep.ret s id g hin hsub hQ hr) (by rw [PMF.mem_support_pure_iff])
  obtain ⟨Q, hQc, hQm⟩ := hQ
  set l : List (Fin P.n) := (Finset.univ.filter (fun k => (g k).isSome)).toList with hl
  have hguard : ∀ k ∈ l, ∀ x, g k = some x → t.val k = none →
      k ∈ t.F ∨ t.call k = some x := by
    intro k _ x hx _
    rcases hR.inv.inVal_prov k x (hsub k x hx) with hF | hin'
    · left
      rw [hR.F_eq]
      exact hF
    · right
      rw [hR.call_eq k, ← hR.inv.input_eq k]
      exact hin'
  have hpre : ∀ k y x, g k = some x → t.val k = some y → y = x := by
    intro k y x hx hy
    have h1 := hR.val_cert k y hy
    have h2 := hsub k x hx
    rw [h1] at h2
    injection h2
  have hcov : ∀ k x, g k = some x → (commitList g l t).val k = some x := by
    intro k x hx
    refine commitList_covers g l t hpre k ?_ x hx
    rw [hl, Finset.mem_toList, Finset.mem_filter]
    exact ⟨Finset.mem_univ k, by rw [hx]; rfl⟩
  have hretflag : (commitList g l t).ret id = false := by
    rw [commitList_ret, hR.ret_eq id]
    exact hr
  have hchain := commitChain_isChain g l t hguard
  have hlast := commitChain_getLastD g l t
  set u : Fin P.n → APSet P.n X := fun q =>
    if h : ∃ U, (s.brbBind q).val = some U ∧ APSet.subMap U g
    then h.choose else ∅ with hu_def
  have hu : ∀ q ∈ Q, (s.brbBind q).val = some (u q) ∧ APSet.subMap (u q) g := by
    intro q hq
    have hex := hQm q hq
    rw [hu_def]
    dsimp only
    rw [dif_pos hex]
    exact hex.choose_spec
  rcases hcores : t.cores with _ | Cs₀
  · -- no family yet: freeze a fresh one at the end of the chain
    have hH : P.f + 1 ≤ (Q \ s.ga.F).card := by
      have h1 := Finset.le_card_sdiff s.ga.F Q
      have h2 := hR.inv.F_card
      have hf := P.hf
      omega
    obtain ⟨H', hH'sub, hH'card⟩ := Finset.exists_subset_card_eq hH
    have hH'Q : ∀ q ∈ H', q ∈ Q := fun q hq => (Finset.mem_sdiff.mp (hH'sub hq)).1
    have hH'F : ∀ q ∈ H', q ∉ s.ga.F := fun q hq => (Finset.mem_sdiff.mp (hH'sub hq)).2
    have hH'ne : H'.Nonempty := by
      rw [← Finset.card_pos, hH'card]
      omega
    obtain ⟨q₀, hq₀⟩ := hH'ne
    set Cs : Finset (APSet P.n X) := H'.image u with hCs_def
    have hCsne : Cs.Nonempty := Finset.Nonempty.image ⟨q₀, hq₀⟩ u
    have hbind : Step P (commitList g l t) Lab.tau
        (PMF.pure { commitList g l t with cores := some Cs }) := by
      refine Step.bindCores _ Cs (by rw [commitList_cores, hcores]) hCsne ?_ ?_
      · intro U hU
        obtain ⟨q, hqH', rfl⟩ := Finset.mem_image.mp hU
        intro p hp
        exact hcov p.1 p.2 ((hu q (hH'Q q hqH')).2 p hp)
      · intro U hU V hV
        obtain ⟨q, hqH', rfl⟩ := Finset.mem_image.mp hU
        obtain ⟨q', hq'H', rfl⟩ := Finset.mem_image.mp hV
        exact bindVal_inter hR.inv (hH'F q hqH') (hH'F q' hq'H')
          (hu q (hH'Q q hqH')).1 (hu q' (hH'Q q' hq'H')).1
    refine ⟨commitChain g l t ++ [{ commitList g l t with cores := some Cs }], Cs,
      ?_, ?_, ?_, ?_, ?_, ?_⟩
    · refine isChain_snoc hchain ?_
      rw [hlast]
      exact hbind
    · rw [List.getLastD_concat]
    · exact ⟨u q₀, Finset.mem_image_of_mem u hq₀, (hu q₀ (hH'Q q₀ hq₀)).2⟩
    · intro k x hx
      rw [List.getLastD_concat]
      exact hcov k x hx
    · rw [List.getLastD_concat]
      exact hretflag
    · rw [List.getLastD_concat]
      refine ⟨hInv', ?_, ?_, ?_, ?_, ?_⟩ <;> dsimp only
      · intro k
        rw [commitList_call]
        by_cases hk : k = id
        · subst hk
          rw [SubState.setProc_proc_self]
          exact hR.call_eq k
        · rw [SubState.setProc_proc_ne _ _ _ hk]
          exact hR.call_eq k
      · intro k
        by_cases hk : k = id
        · subst hk
          rw [Function.update_self, SubState.setProc_proc_self]
        · rw [Function.update_of_ne hk, commitList_ret,
            SubState.setProc_proc_ne _ _ _ hk]
          exact hR.ret_eq k
      · rw [commitList_F]
        exact hR.F_eq
      · intro k v hv
        rcases commitList_val_new g l t hv with hold | hnew
        · exact hR.val_cert k v hold
        · exact hsub k v hnew
      · intro Cs' hCs'
        obtain rfl : Cs = Cs' := by injection hCs'
        refine le_trans (le_of_eq hH'card.symm) (Finset.card_le_card ?_)
        intro q hq
        rw [Finset.mem_filter]
        exact ⟨Finset.mem_univ q, u q, Finset.mem_image_of_mem u hq,
          (hu q (hH'Q q hq)).1⟩
  · -- family frozen earlier: locate the dominated member through the count
    have hcount := hR.cores_cert Cs₀ hcores
    obtain ⟨qh, hqhK, hqhQ⟩ := SubState.exists_mem_inter_of_quorum hcount hQc
    rw [Finset.mem_filter] at hqhK
    obtain ⟨-, U₀, hU₀Cs, hU₀val⟩ := hqhK
    have h2 := (hu qh hqhQ).1
    rw [hU₀val] at h2
    obtain rfl : U₀ = u qh := by injection h2
    refine ⟨commitChain g l t, Cs₀, hchain, ?_, ⟨u qh, hU₀Cs, (hu qh hqhQ).2⟩,
      ?_, ?_, ?_⟩
    · rw [hlast, commitList_cores, hcores]
    · intro k x hx
      rw [hlast]
      exact hcov k x hx
    · rw [hlast]
      exact hretflag
    · rw [hlast]
      refine ⟨hInv', ?_, ?_, ?_, ?_, ?_⟩ <;> dsimp only
      · intro k
        rw [commitList_call]
        by_cases hk : k = id
        · subst hk
          rw [SubState.setProc_proc_self]
          exact hR.call_eq k
        · rw [SubState.setProc_proc_ne _ _ _ hk]
          exact hR.call_eq k
      · intro k
        by_cases hk : k = id
        · subst hk
          rw [Function.update_self, SubState.setProc_proc_self]
        · rw [Function.update_of_ne hk, commitList_ret,
            SubState.setProc_proc_ne _ _ _ hk]
          exact hR.ret_eq k
      · rw [commitList_F]
        exact hR.F_eq
      · intro k v hv
        rcases commitList_val_new g l t hv with hold | hnew
        · exact hR.val_cert k v hold
        · exact hsub k v hnew
      · intro Cs' hCs'
        rw [commitList_cores, hcores] at hCs'
        obtain rfl : Cs₀ = Cs' := by injection hCs'
        exact hR.cores_cert Cs₀ hcores


/-! ### Step-level relation transports

The relation across one embedded row, exported for systems that replay the
gather rows inside a larger rule table. -/

/-- The relation across the fused call: the gather record and input-BRB call
effects against the specification's call effect. -/
theorem coreRel_call {s : IdealState P.n X} {t : SpecState P.n X}
    (hR : CoreRel P s t) {id : Fin P.n} {x : X}
    (h : (s.ga.proc id).input = none) :
    CoreRel P
      { s with
        ga := s.ga.setProc id { s.ga.proc id with input := some x }
        brbIn := Function.update s.brbIn id { s.brbIn id with input := some x } }
      { t with call := Function.update t.call id (some x) } := by
  refine ⟨hR.inv.step (IdealStep.call s id x h) (by rw [PMF.mem_support_pure_iff]),
    ?_, ?_, ?_, ?_, ?_⟩ <;> dsimp only
  · intro k
    by_cases hk : k = id
    · subst hk
      rw [Function.update_self, SubState.setProc_proc_self]
    · rw [Function.update_of_ne hk, SubState.setProc_proc_ne _ _ _ hk]
      exact hR.call_eq k
  · intro k
    by_cases hk : k = id
    · subst hk
      rw [SubState.setProc_proc_self]
      exact hR.ret_eq k
    · rw [SubState.setProc_proc_ne _ _ _ hk]
      exact hR.ret_eq k
  · exact hR.F_eq
  · intro k v hv
    by_cases hk : k = id
    · subst hk
      rw [Function.update_self]
      exact hR.val_cert k v hv
    · rw [Function.update_of_ne hk]
      exact hR.val_cert k v hv
  · intro Cs hCs
    refine le_trans (hR.cores_cert Cs hCs) (Finset.card_le_card ?_)
    intro q hq
    rw [Finset.mem_filter] at hq ⊢
    exact hq

/-- The relation across any internal row, the specification stuttering. -/
theorem coreRel_tau {s s' : IdealState P.n X} {t : SpecState P.n X}
    (hR : CoreRel P s t) (hstep : IdealStep P s Gather.Lab.tau (PMF.pure s')) :
    CoreRel P s' t := by
  have hInv' := hR.inv.step hstep (by rw [PMF.mem_support_pure_iff])
  generalize hμ : (PMF.pure s' : PMF (IdealState P.n X)) = μ at hstep
  cases hstep with
  | commitIn k v hv hm =>
    have hs' := PMF.pure_injective hμ
    subst hs'
    refine ⟨hInv', hR.call_eq, hR.ret_eq, hR.F_eq, ?_, hR.cores_cert⟩
    intro k' v' hv'
    have hold := hR.val_cert k' v' hv'
    dsimp only
    by_cases hk : k' = k
    · subst hk
      rw [hv] at hold
      exact absurd hold (by simp)
    · rw [Function.update_of_ne hk]
      exact hold
  | commitBind k U hv hm =>
    have hs' := PMF.pure_injective hμ
    subst hs'
    refine ⟨hInv', hR.call_eq, hR.ret_eq, hR.F_eq, hR.val_cert, ?_⟩
    intro Cs hCs
    refine le_trans (hR.cores_cert Cs hCs) (Finset.card_le_card ?_)
    intro q hq
    rw [Finset.mem_filter] at hq ⊢
    obtain ⟨-, U', hU', hval⟩ := hq
    refine ⟨Finset.mem_univ q, U', hU', ?_⟩
    dsimp only
    by_cases hk : q = k
    · subst hk
      rw [hv] at hval
      exact absurd hval (by simp)
    · rw [Function.update_of_ne hk]
      exact hval
  | deliver i j m h =>
    have hs' := PMF.pure_injective hμ
    subst hs'
    refine ⟨hInv', ?_, ?_, hR.F_eq, hR.val_cert, hR.cores_cert⟩ <;> dsimp only
    · intro k
      rw [SubState.recvMsg_proc]
      exact hR.call_eq k
    · intro k
      rw [SubState.recvMsg_proc]
      exact hR.ret_eq k
  | echo j A hin happ hcard hsend =>
    have hs' := PMF.pure_injective hμ
    subst hs'
    refine ⟨hInv', ?_, ?_, hR.F_eq, hR.val_cert, hR.cores_cert⟩ <;> dsimp only
    · intro k
      by_cases hk : k = j
      · subst hk
        rw [SubState.mcast_proc, SubState.setProc_proc_self]
        exact hR.call_eq k
      · rw [SubState.mcast_proc, SubState.setProc_proc_ne _ _ _ hk]
        exact hR.call_eq k
    · intro k
      by_cases hk : k = j
      · subst hk
        rw [SubState.mcast_proc, SubState.setProc_proc_self]
        exact hR.ret_eq k
      · rw [SubState.mcast_proc, SubState.setProc_proc_ne _ _ _ hk]
        exact hR.ret_eq k
  | vote j U hin happ hQ hsend =>
    have hs' := PMF.pure_injective hμ
    subst hs'
    refine ⟨hInv', ?_, ?_, hR.F_eq, hR.val_cert, hR.cores_cert⟩ <;> dsimp only
    · intro k
      by_cases hk : k = j
      · subst hk
        rw [SubState.mcast_proc, SubState.setProc_proc_self]
        exact hR.call_eq k
      · rw [SubState.mcast_proc, SubState.setProc_proc_ne _ _ _ hk]
        exact hR.call_eq k
    · intro k
      by_cases hk : k = j
      · subst hk
        rw [SubState.mcast_proc, SubState.setProc_proc_self]
        exact hR.ret_eq k
      · rw [SubState.mcast_proc, SubState.setProc_proc_ne _ _ _ hk]
        exact hR.ret_eq k
  | bindCall j U hin hb happ hQ =>
    have hs' := PMF.pure_injective hμ
    subst hs'
    refine ⟨hInv', hR.call_eq, hR.ret_eq, hR.F_eq, hR.val_cert, ?_⟩
    intro Cs hCs
    refine le_trans (hR.cores_cert Cs hCs) (Finset.card_le_card ?_)
    intro q hq
    rw [Finset.mem_filter] at hq ⊢
    obtain ⟨-, U', hU', hval⟩ := hq
    refine ⟨Finset.mem_univ q, U', hU', ?_⟩
    dsimp only
    by_cases hk : q = j
    · subst hk
      rw [Function.update_self]
      exact hval
    · rw [Function.update_of_ne hk]
      exact hval
  | byz j m hmem =>
    have hs' := PMF.pure_injective hμ
    subst hs'
    exact ⟨hInv', hR.call_eq, hR.ret_eq, hR.F_eq, hR.val_cert, hR.cores_cert⟩

/-! ### The refinement -/

/-- **The gather refinement**: the gather-over-BRB-specification instance
forward-simulates the gather specification. -/
theorem gatherCore (P : Params) (X : Type) [DecidableEq X] :
    ForwardSimulation (idealInst P X) (specInst P X) (CoreRel P) := by
  constructor
  intro q₁ q₂ hR l μ hstep q₁' hq₁'
  rw [idealInst_step] at hstep
  have hInv' := hR.inv.step hstep hq₁'
  cases hstep with
  | call id x h =>
    rw [PMF.mem_support_pure_iff] at hq₁'
    subst hq₁'
    refine ⟨{ q₂ with call := Function.update q₂.call id (some x) },
      Or.inr ⟨by simp, System.weakLStep_of_step (by simp)
        (Step.call q₂ id x (by rw [hR.call_eq id]; exact h))⟩,
      hInv', ?_, ?_, ?_, ?_, ?_⟩ <;> dsimp only
    · intro k
      by_cases hk : k = id
      · subst hk
        rw [Function.update_self, SubState.setProc_proc_self]
      · rw [Function.update_of_ne hk, SubState.setProc_proc_ne _ _ _ hk]
        exact hR.call_eq k
    · intro k
      by_cases hk : k = id
      · subst hk
        rw [SubState.setProc_proc_self]
        exact hR.ret_eq k
      · rw [SubState.setProc_proc_ne _ _ _ hk]
        exact hR.ret_eq k
    · exact hR.F_eq
    · intro k v hv
      by_cases hk : k = id
      · subst hk
        rw [Function.update_self]
        have hold := hR.val_cert k v hv
        exact hold
      · rw [Function.update_of_ne hk]
        exact hR.val_cert k v hv
    · intro Cs hCs
      exact hR.cores_cert Cs hCs
  | callLoop id x =>
    rw [PMF.mem_support_pure_iff] at hq₁'
    subst hq₁'
    exact ⟨q₂, Or.inr ⟨by simp, System.weakLStep_of_step (by simp)
      (Step.callLoop q₂ id x)⟩, hR⟩
  | commitIn k v hv hm =>
    rw [PMF.mem_support_pure_iff] at hq₁'
    subst hq₁'
    refine ⟨q₂, Or.inl ⟨rfl, System.weakLSilent_refl _ q₂⟩,
      hInv', hR.call_eq, hR.ret_eq, hR.F_eq, ?_, hR.cores_cert⟩
    intro k' v' hv'
    have hold := hR.val_cert k' v' hv'
    dsimp only
    by_cases hk : k' = k
    · subst hk
      rw [hv] at hold
      exact absurd hold (by simp)
    · rw [Function.update_of_ne hk]
      exact hold
  | commitBind k U hv hm =>
    rw [PMF.mem_support_pure_iff] at hq₁'
    subst hq₁'
    refine ⟨q₂, Or.inl ⟨rfl, System.weakLSilent_refl _ q₂⟩,
      hInv', hR.call_eq, hR.ret_eq, hR.F_eq, hR.val_cert, ?_⟩
    intro Cs hCs
    refine le_trans (hR.cores_cert Cs hCs) (Finset.card_le_card ?_)
    intro q hq
    rw [Finset.mem_filter] at hq ⊢
    obtain ⟨-, U', hU', hval⟩ := hq
    refine ⟨Finset.mem_univ q, U', hU', ?_⟩
    dsimp only
    by_cases hk : q = k
    · subst hk
      rw [hv] at hval
      exact absurd hval (by simp)
    · rw [Function.update_of_ne hk]
      exact hval
  | deliver i j m h =>
    rw [PMF.mem_support_pure_iff] at hq₁'
    subst hq₁'
    refine ⟨q₂, Or.inl ⟨rfl, System.weakLSilent_refl _ q₂⟩,
      hInv', ?_, ?_, hR.F_eq, hR.val_cert, hR.cores_cert⟩ <;> dsimp only
    · intro k
      rw [SubState.recvMsg_proc]
      exact hR.call_eq k
    · intro k
      rw [SubState.recvMsg_proc]
      exact hR.ret_eq k
  | echo j A hin happ hcard hsend =>
    rw [PMF.mem_support_pure_iff] at hq₁'
    subst hq₁'
    refine ⟨q₂, Or.inl ⟨rfl, System.weakLSilent_refl _ q₂⟩,
      hInv', ?_, ?_, hR.F_eq, hR.val_cert, hR.cores_cert⟩ <;> dsimp only
    · intro k
      by_cases hk : k = j
      · subst hk
        rw [SubState.mcast_proc, SubState.setProc_proc_self]
        exact hR.call_eq k
      · rw [SubState.mcast_proc, SubState.setProc_proc_ne _ _ _ hk]
        exact hR.call_eq k
    · intro k
      by_cases hk : k = j
      · subst hk
        rw [SubState.mcast_proc, SubState.setProc_proc_self]
        exact hR.ret_eq k
      · rw [SubState.mcast_proc, SubState.setProc_proc_ne _ _ _ hk]
        exact hR.ret_eq k
  | vote j U hin happ hQ hsend =>
    rw [PMF.mem_support_pure_iff] at hq₁'
    subst hq₁'
    refine ⟨q₂, Or.inl ⟨rfl, System.weakLSilent_refl _ q₂⟩,
      hInv', ?_, ?_, hR.F_eq, hR.val_cert, hR.cores_cert⟩ <;> dsimp only
    · intro k
      by_cases hk : k = j
      · subst hk
        rw [SubState.mcast_proc, SubState.setProc_proc_self]
        exact hR.call_eq k
      · rw [SubState.mcast_proc, SubState.setProc_proc_ne _ _ _ hk]
        exact hR.call_eq k
    · intro k
      by_cases hk : k = j
      · subst hk
        rw [SubState.mcast_proc, SubState.setProc_proc_self]
        exact hR.ret_eq k
      · rw [SubState.mcast_proc, SubState.setProc_proc_ne _ _ _ hk]
        exact hR.ret_eq k
  | bindCall j U hin hb happ hQ =>
    rw [PMF.mem_support_pure_iff] at hq₁'
    subst hq₁'
    refine ⟨q₂, Or.inl ⟨rfl, System.weakLSilent_refl _ q₂⟩,
      hInv', hR.call_eq, hR.ret_eq, hR.F_eq, hR.val_cert, ?_⟩
    intro Cs hCs
    refine le_trans (hR.cores_cert Cs hCs) (Finset.card_le_card ?_)
    intro q hq
    rw [Finset.mem_filter] at hq ⊢
    obtain ⟨-, U', hU', hval⟩ := hq
    refine ⟨Finset.mem_univ q, U', hU', ?_⟩
    dsimp only
    by_cases hk : q = j
    · subst hk
      rw [Function.update_self]
      exact hval
    · rw [Function.update_of_ne hk]
      exact hval
  | byz j m hmem =>
    rw [PMF.mem_support_pure_iff] at hq₁'
    subst hq₁'
    exact ⟨q₂, Or.inl ⟨rfl, System.weakLSilent_refl _ q₂⟩,
      hInv', hR.call_eq, hR.ret_eq, hR.F_eq, hR.val_cert, hR.cores_cert⟩
  | ret id g hin hsub hQ hr =>
    rw [PMF.mem_support_pure_iff] at hq₁'
    subst hq₁'
    obtain ⟨ts, Cs, hchain, hCs, hmem, hcov, hret1, hRel⟩ :=
      retBurst hR hin hsub hQ hr
    have hretstep : Step P (ts.getLastD q₂) (Lab.ret id g)
        (PMF.pure { ts.getLastD q₂ with
          ret := Function.update (ts.getLastD q₂).ret id true }) :=
      Step.ret _ id g Cs hCs hmem hcov hret1
    exact ⟨_, Or.inr ⟨by simp,
      System.weakLStep_tausThen hchain hretstep (by simp)⟩, hRel⟩
  | fail id =>
    rw [PMF.mem_support_pure_iff] at hq₁'
    subst hq₁'
    exact ⟨q₂.corrupt P id, Or.inr ⟨by simp, System.weakLStep_of_step (by simp)
      (Step.fail q₂ id)⟩, coreRel_corrupt hR id⟩

/-- info: 'PLTS.ABA.Gather.gatherCore' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms gatherCore

end Gather
end ABA
end PLTS
