/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sathiya / Claude
-/

import Leslie2Protocols.ABA.Broadcast.Sub
import Leslie2Protocols.Framework.FamilySim

/-!
# The BRB refinement: Bracha's protocol implements Transition System 6

`BRB.brbRefines`: the reliable-broadcast instance `BRB.implInst`
(`ABA/Broadcast/Sub.lean`) is forward simulated by the BRB specification
instance with the same leader, read over the instance's interface
(`BRB.liftedSpec`), along `BRB.InstRel`.

The refinement runs in two legs. The first is strong and functional: a
transition of the instance is one row of `BRB.ImplStep` at the same state, at
the specification label the interface label projects to (`BRB.implInst_step_row`).
The second is the row-level matching `instRel_row`, whose answer is a weak run
of the specification over `BRB.Lab`; it is lifted to the interface along a
section of `BRB.specPull`, which is where the call loop is answered by the
specification's own loop row.

The one piece of abstract information the specification tracks and the
implementation does not is the committed value `val`. The refinement supplies
it as a receipt-pattern certificate, in the exclusion-on-demand style of the GBCA
refinement: the specification's `commit` is fired inside the return run, at
the first return that needs it.

* `BRB.EchoCert s m` — some receiver holds an `n − f` `ECHO m` receipt
  quorum. F-blind (it counts receipts, not honesty) and monotone (receipts
  only accumulate), so it survives every rule and every corruption.
* At most one value is ever echo-certified (`echoCert_unique`): two `ECHO`
  receipt quorums share an honest sender, whose `sentEcho` field is
  write-once.
* Every return guard yields a certificate (`echoCert_of_vote_quorum`): an
  `n − f` `VOTE m` receipt quorum contains an honest voter, whose vote is
  backed — through the amplification chain, collapsed by the invariant clause
  `vote_backed` — by an `ECHO m` receipt quorum.
* A certificate identifies the honest leader's input
  (`input_of_echoCert`): an `ECHO` quorum contains an honest echoer, whose
  echo is backed by an `⟨INIT, m⟩` receipt from the leader's sent.

The matching: internal rules stutter; `call` and `fail` are answered by their
specification rows; `ret id m` is answered by `ret` alone when `val` is
already committed (the certificates identify the values), and by the two-step
run `commit ; ret` (`weakLStep_tauThen`) when it is not — with `commit`'s
guard discharged by `input_of_echoCert` under an honest leader and by
membership in `F` otherwise.
-/

namespace PLTS
namespace ABA
namespace BRB

variable {M : Type} [DecidableEq M] {P : Params} {ldr : Fin P.n}

/-! ### The certificate -/

/-- `m` is echo-certified: some receiver holds an `n − f` `ECHO m` receipt
quorum. F-blind and monotone — receipts only accumulate. -/
def EchoCert (P : Params) (s : ImplState P.n M) (m : M) : Prop :=
  ∃ i, P.n - P.f ≤ s.recvCount i (.echo m)

@[simp] theorem echoCert_setProc (s : ImplState P.n M) (j : Fin P.n)
    (p : PState M) (m : M) :
    EchoCert P (s.setProc j p) m ↔ EchoCert P s m := by
  simp [EchoCert]

@[simp] theorem echoCert_mcast (s : ImplState P.n M) (j : Fin P.n)
    (x : BMsg M) (m : M) :
    EchoCert P (s.mcast j x) m ↔ EchoCert P s m := by
  simp [EchoCert]

@[simp] theorem echoCert_corrupt (s : ImplState P.n M) (id : Fin P.n) (m : M) :
    EchoCert P (s.corrupt P id) m ↔ EchoCert P s m := by
  simp [EchoCert]

/-- Deliveries preserve the certificate: counts only grow. -/
theorem EchoCert.recvMsg {s : ImplState P.n M} {m : M} (h : EchoCert P s m)
    (i j : Fin P.n) (x : BMsg M) : EchoCert P (s.recvMsg i j x) m := by
  obtain ⟨i', hi'⟩ := h
  exact ⟨i', le_trans hi' (SubState.recvCount_le_recvMsg s i j x i' _)⟩

/-! ### The invariant -/

/-- The BRB implementation invariant. The `*_conf` clauses tie an honest
sender's sent to its write-once field; `echo_backed` / `vote_backed` tie the
fields to the receipts that justified them, with the amplification chain
collapsed into `EchoCert`. -/
structure Inv (P : Params) (ldr : Fin P.n) (s : ImplState P.n M) : Prop where
  /-- The corruption budget. -/
  F_card : s.F.card ≤ P.f
  /-- Delivered messages were multicast. -/
  recv_sub : ∀ i k, s.recv i k ⊆ s.sent k
  /-- An honest leader's sent `INIT` carries its input. -/
  init_conf : ldr ∉ s.F → ∀ m, BMsg.init m ∈ s.sent ldr →
    (s.proc ldr).input = some m
  /-- An honest sender's sent `ECHO` matches its write-once field. -/
  echo_conf : ∀ k ∉ s.F, ∀ m, BMsg.echo m ∈ s.sent k →
    (s.proc k).sentEcho = some m
  /-- An honest echo is backed by an `INIT` receipt from the leader. -/
  echo_backed : ∀ k ∉ s.F, ∀ m, (s.proc k).sentEcho = some m →
    BMsg.init m ∈ s.recv k ldr
  /-- An honest sender's sent `VOTE` matches its write-once field. -/
  vote_conf : ∀ k ∉ s.F, ∀ m, BMsg.vote m ∈ s.sent k →
    (s.proc k).sentVote = some m
  /-- An honest vote is backed by an `ECHO` receipt quorum somewhere: the
  quorum rule witnesses itself, and the amplification rule inherits the
  witness from an honest backer. -/
  vote_backed : ∀ k ∉ s.F, ∀ m, (s.proc k).sentVote = some m → EchoCert P s m

/-- The invariant holds initially. -/
theorem Inv.initial : Inv P ldr (ImplState.initial P.n M) := by
  refine ⟨by simp [ImplState.initial], ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [ImplState.initial, PState.initial]

/-- The invariant is preserved by every implementation step. -/
theorem Inv.step {s : ImplState P.n M} {l : Lab P.n M} {μ : PMF (ImplState P.n M)}
    (hInv : Inv P ldr s) (hstep : ImplStep P ldr s l μ)
    {s' : ImplState P.n M} (hs' : s' ∈ μ.support) : Inv P ldr s' := by
  cases hstep with
  | call m h =>
    rw [PMF.mem_support_pure_iff] at hs'
    subst hs'
    refine ⟨by simpa using hInv.F_card, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro i k x hx
      simp only [SubState.mcast_recv, SubState.setProc_recv] at hx
      rw [SubState.mem_mcast_sent, SubState.setProc_sent]
      exact Or.inr (hInv.recv_sub i k hx)
    · intro hldr m' hmem
      rw [SubState.mem_mcast_sent, SubState.setProc_sent] at hmem
      rcases hmem with ⟨-, hm'⟩ | hold
      · obtain rfl : m' = m := by injection hm'
        simp
      · have hin := hInv.init_conf (by simpa using hldr) m' hold
        rw [h] at hin
        exact absurd hin (by simp)
    · intro k hk m' hmem
      rw [SubState.mem_mcast_sent, SubState.setProc_sent] at hmem
      rcases hmem with ⟨-, hm'⟩ | hold
      · exact absurd hm' (by simp)
      · have hpre := hInv.echo_conf k (by simpa using hk) m' hold
        by_cases hkl : k = ldr
        · subst hkl
          rw [SubState.mcast_proc, SubState.setProc_proc_self]
          exact hpre
        · rw [SubState.mcast_proc, SubState.setProc_proc_ne _ _ _ hkl]
          exact hpre
    · intro k hk m' hslot
      simp only [SubState.mcast_recv, SubState.setProc_recv]
      by_cases hkl : k = ldr
      · subst hkl
        rw [SubState.mcast_proc, SubState.setProc_proc_self] at hslot
        exact hInv.echo_backed k (by simpa using hk) m' hslot
      · rw [SubState.mcast_proc, SubState.setProc_proc_ne _ _ _ hkl] at hslot
        exact hInv.echo_backed k (by simpa using hk) m' hslot
    · intro k hk m' hmem
      rw [SubState.mem_mcast_sent, SubState.setProc_sent] at hmem
      rcases hmem with ⟨-, hm'⟩ | hold
      · exact absurd hm' (by simp)
      · have hpre := hInv.vote_conf k (by simpa using hk) m' hold
        by_cases hkl : k = ldr
        · subst hkl
          rw [SubState.mcast_proc, SubState.setProc_proc_self]
          exact hpre
        · rw [SubState.mcast_proc, SubState.setProc_proc_ne _ _ _ hkl]
          exact hpre
    · intro k hk m' hslot
      rw [echoCert_mcast, echoCert_setProc]
      by_cases hkl : k = ldr
      · subst hkl
        rw [SubState.mcast_proc, SubState.setProc_proc_self] at hslot
        exact hInv.vote_backed k (by simpa using hk) m' hslot
      · rw [SubState.mcast_proc, SubState.setProc_proc_ne _ _ _ hkl] at hslot
        exact hInv.vote_backed k (by simpa using hk) m' hslot
  | callLoop m =>
    rw [PMF.mem_support_pure_iff] at hs'
    subst hs'
    exact hInv
  | deliver i j m h =>
    rw [PMF.mem_support_pure_iff] at hs'
    subst hs'
    refine ⟨by simpa using hInv.F_card, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro i' k x hx
      rw [SubState.mem_recvMsg_recv] at hx
      rw [SubState.recvMsg_sent]
      rcases hx with ⟨-, rfl, rfl⟩ | hold
      · exact h
      · exact hInv.recv_sub i' k hold
    · intro hldr m' hmem
      rw [SubState.recvMsg_sent] at hmem
      rw [SubState.recvMsg_proc]
      exact hInv.init_conf (by simpa using hldr) m' hmem
    · intro k hk m' hmem
      rw [SubState.recvMsg_sent] at hmem
      rw [SubState.recvMsg_proc]
      exact hInv.echo_conf k (by simpa using hk) m' hmem
    · intro k hk m' hslot
      rw [SubState.recvMsg_proc] at hslot
      exact SubState.mem_recvMsg_recv.mpr
        (Or.inr (hInv.echo_backed k (by simpa using hk) m' hslot))
    · intro k hk m' hmem
      rw [SubState.recvMsg_sent] at hmem
      rw [SubState.recvMsg_proc]
      exact hInv.vote_conf k (by simpa using hk) m' hmem
    · intro k hk m' hslot
      rw [SubState.recvMsg_proc] at hslot
      exact (hInv.vote_backed k (by simpa using hk) m' hslot).recvMsg i j m
  | echo j m hrecv hsend =>
    rw [PMF.mem_support_pure_iff] at hs'
    subst hs'
    refine ⟨by simpa using hInv.F_card, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro i k x hx
      simp only [SubState.mcast_recv, SubState.setProc_recv] at hx
      rw [SubState.mem_mcast_sent, SubState.setProc_sent]
      exact Or.inr (hInv.recv_sub i k hx)
    · intro hldr m' hmem
      rw [SubState.mem_mcast_sent, SubState.setProc_sent] at hmem
      rcases hmem with ⟨-, hm'⟩ | hold
      · exact absurd hm' (by simp)
      · have hpre := hInv.init_conf (by simpa using hldr) m' hold
        by_cases hkl : ldr = j
        · rw [SubState.mcast_proc, hkl, SubState.setProc_proc_self]
          rw [hkl] at hpre
          exact hpre
        · rw [SubState.mcast_proc, SubState.setProc_proc_ne _ _ _ hkl]
          exact hpre
    · intro k hk m' hmem
      rw [SubState.mem_mcast_sent, SubState.setProc_sent] at hmem
      rcases hmem with ⟨rfl, hm'⟩ | hold
      · obtain rfl : m' = m := by injection hm'
        simp
      · have hpre := hInv.echo_conf k (by simpa using hk) m' hold
        by_cases hkl : k = j
        · subst hkl
          rw [hsend] at hpre
          exact absurd hpre (by simp)
        · rw [SubState.mcast_proc, SubState.setProc_proc_ne _ _ _ hkl]
          exact hpre
    · intro k hk m' hslot
      simp only [SubState.mcast_recv, SubState.setProc_recv]
      by_cases hkl : k = j
      · subst hkl
        rw [SubState.mcast_proc, SubState.setProc_proc_self] at hslot
        obtain rfl : m = m' := by injection hslot
        exact hrecv
      · rw [SubState.mcast_proc, SubState.setProc_proc_ne _ _ _ hkl] at hslot
        exact hInv.echo_backed k (by simpa using hk) m' hslot
    · intro k hk m' hmem
      rw [SubState.mem_mcast_sent, SubState.setProc_sent] at hmem
      rcases hmem with ⟨-, hm'⟩ | hold
      · exact absurd hm' (by simp)
      · have hpre := hInv.vote_conf k (by simpa using hk) m' hold
        by_cases hkl : k = j
        · subst hkl
          rw [SubState.mcast_proc, SubState.setProc_proc_self]
          exact hpre
        · rw [SubState.mcast_proc, SubState.setProc_proc_ne _ _ _ hkl]
          exact hpre
    · intro k hk m' hslot
      rw [echoCert_mcast, echoCert_setProc]
      by_cases hkl : k = j
      · subst hkl
        rw [SubState.mcast_proc, SubState.setProc_proc_self] at hslot
        exact hInv.vote_backed k (by simpa using hk) m' hslot
      · rw [SubState.mcast_proc, SubState.setProc_proc_ne _ _ _ hkl] at hslot
        exact hInv.vote_backed k (by simpa using hk) m' hslot
  | voteQuorum j m hcnt hsend =>
    rw [PMF.mem_support_pure_iff] at hs'
    subst hs'
    refine ⟨by simpa using hInv.F_card, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro i k x hx
      simp only [SubState.mcast_recv, SubState.setProc_recv] at hx
      rw [SubState.mem_mcast_sent, SubState.setProc_sent]
      exact Or.inr (hInv.recv_sub i k hx)
    · intro hldr m' hmem
      rw [SubState.mem_mcast_sent, SubState.setProc_sent] at hmem
      rcases hmem with ⟨-, hm'⟩ | hold
      · exact absurd hm' (by simp)
      · have hpre := hInv.init_conf (by simpa using hldr) m' hold
        by_cases hkl : ldr = j
        · rw [SubState.mcast_proc, hkl, SubState.setProc_proc_self]
          rw [hkl] at hpre
          exact hpre
        · rw [SubState.mcast_proc, SubState.setProc_proc_ne _ _ _ hkl]
          exact hpre
    · intro k hk m' hmem
      rw [SubState.mem_mcast_sent, SubState.setProc_sent] at hmem
      rcases hmem with ⟨-, hm'⟩ | hold
      · exact absurd hm' (by simp)
      · have hpre := hInv.echo_conf k (by simpa using hk) m' hold
        by_cases hkl : k = j
        · subst hkl
          rw [SubState.mcast_proc, SubState.setProc_proc_self]
          exact hpre
        · rw [SubState.mcast_proc, SubState.setProc_proc_ne _ _ _ hkl]
          exact hpre
    · intro k hk m' hslot
      simp only [SubState.mcast_recv, SubState.setProc_recv]
      by_cases hkl : k = j
      · subst hkl
        rw [SubState.mcast_proc, SubState.setProc_proc_self] at hslot
        exact hInv.echo_backed k (by simpa using hk) m' hslot
      · rw [SubState.mcast_proc, SubState.setProc_proc_ne _ _ _ hkl] at hslot
        exact hInv.echo_backed k (by simpa using hk) m' hslot
    · intro k hk m' hmem
      rw [SubState.mem_mcast_sent, SubState.setProc_sent] at hmem
      rcases hmem with ⟨rfl, hm'⟩ | hold
      · obtain rfl : m' = m := by injection hm'
        simp
      · have hpre := hInv.vote_conf k (by simpa using hk) m' hold
        by_cases hkl : k = j
        · subst hkl
          rw [hsend] at hpre
          exact absurd hpre (by simp)
        · rw [SubState.mcast_proc, SubState.setProc_proc_ne _ _ _ hkl]
          exact hpre
    · intro k hk m' hslot
      rw [echoCert_mcast, echoCert_setProc]
      by_cases hkl : k = j
      · subst hkl
        rw [SubState.mcast_proc, SubState.setProc_proc_self] at hslot
        obtain rfl : m = m' := by injection hslot
        exact ⟨k, hcnt⟩
      · rw [SubState.mcast_proc, SubState.setProc_proc_ne _ _ _ hkl] at hslot
        exact hInv.vote_backed k (by simpa using hk) m' hslot
  | voteAmp j m hcnt hsend =>
    rw [PMF.mem_support_pure_iff] at hs'
    subst hs'
    refine ⟨by simpa using hInv.F_card, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro i k x hx
      simp only [SubState.mcast_recv, SubState.setProc_recv] at hx
      rw [SubState.mem_mcast_sent, SubState.setProc_sent]
      exact Or.inr (hInv.recv_sub i k hx)
    · intro hldr m' hmem
      rw [SubState.mem_mcast_sent, SubState.setProc_sent] at hmem
      rcases hmem with ⟨-, hm'⟩ | hold
      · exact absurd hm' (by simp)
      · have hpre := hInv.init_conf (by simpa using hldr) m' hold
        by_cases hkl : ldr = j
        · rw [SubState.mcast_proc, hkl, SubState.setProc_proc_self]
          rw [hkl] at hpre
          exact hpre
        · rw [SubState.mcast_proc, SubState.setProc_proc_ne _ _ _ hkl]
          exact hpre
    · intro k hk m' hmem
      rw [SubState.mem_mcast_sent, SubState.setProc_sent] at hmem
      rcases hmem with ⟨-, hm'⟩ | hold
      · exact absurd hm' (by simp)
      · have hpre := hInv.echo_conf k (by simpa using hk) m' hold
        by_cases hkl : k = j
        · subst hkl
          rw [SubState.mcast_proc, SubState.setProc_proc_self]
          exact hpre
        · rw [SubState.mcast_proc, SubState.setProc_proc_ne _ _ _ hkl]
          exact hpre
    · intro k hk m' hslot
      simp only [SubState.mcast_recv, SubState.setProc_recv]
      by_cases hkl : k = j
      · subst hkl
        rw [SubState.mcast_proc, SubState.setProc_proc_self] at hslot
        exact hInv.echo_backed k (by simpa using hk) m' hslot
      · rw [SubState.mcast_proc, SubState.setProc_proc_ne _ _ _ hkl] at hslot
        exact hInv.echo_backed k (by simpa using hk) m' hslot
    · intro k hk m' hmem
      rw [SubState.mem_mcast_sent, SubState.setProc_sent] at hmem
      rcases hmem with ⟨rfl, hm'⟩ | hold
      · obtain rfl : m' = m := by injection hm'
        simp
      · have hpre := hInv.vote_conf k (by simpa using hk) m' hold
        by_cases hkl : k = j
        · subst hkl
          rw [hsend] at hpre
          exact absurd hpre (by simp)
        · rw [SubState.mcast_proc, SubState.setProc_proc_ne _ _ _ hkl]
          exact hpre
    · intro k hk m' hslot
      rw [echoCert_mcast, echoCert_setProc]
      by_cases hkl : k = j
      · subst hkl
        rw [SubState.mcast_proc, SubState.setProc_proc_self] at hslot
        obtain rfl : m = m' := by injection hslot
        -- amplification: an honest backer supplies the certificate
        have hlt : s.F.card < s.recvCount k (.vote m) :=
          lt_of_lt_of_le (Nat.lt_succ_of_le hInv.F_card) hcnt
        obtain ⟨k', hk'F, hk'recv⟩ := SubState.exists_sender_notMem s.F hlt
        have hk'sent := hInv.recv_sub k k' hk'recv
        have hk'field := hInv.vote_conf k' hk'F m hk'sent
        exact hInv.vote_backed k' hk'F m hk'field
      · rw [SubState.mcast_proc, SubState.setProc_proc_ne _ _ _ hkl] at hslot
        exact hInv.vote_backed k (by simpa using hk) m' hslot
  | byz j m hj =>
    rw [PMF.mem_support_pure_iff] at hs'
    subst hs'
    refine ⟨by simpa using hInv.F_card, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro i k x hx
      rw [SubState.mcast_recv] at hx
      rw [SubState.mem_mcast_sent]
      exact Or.inr (hInv.recv_sub i k hx)
    · intro hldr m' hmem
      rw [SubState.mem_mcast_sent] at hmem
      rw [SubState.mcast_proc]
      rcases hmem with ⟨rfl, -⟩ | hold
      · exact absurd hj (by simpa using hldr)
      · exact hInv.init_conf (by simpa using hldr) m' hold
    · intro k hk m' hmem
      rw [SubState.mem_mcast_sent] at hmem
      rw [SubState.mcast_proc]
      rcases hmem with ⟨rfl, -⟩ | hold
      · exact absurd hj (by simpa using hk)
      · exact hInv.echo_conf k (by simpa using hk) m' hold
    · intro k hk m' hslot
      rw [SubState.mcast_proc] at hslot
      rw [SubState.mcast_recv]
      exact hInv.echo_backed k (by simpa using hk) m' hslot
    · intro k hk m' hmem
      rw [SubState.mem_mcast_sent] at hmem
      rw [SubState.mcast_proc]
      rcases hmem with ⟨rfl, -⟩ | hold
      · exact absurd hj (by simpa using hk)
      · exact hInv.vote_conf k (by simpa using hk) m' hold
    · intro k hk m' hslot
      rw [SubState.mcast_proc] at hslot
      rw [echoCert_mcast]
      exact hInv.vote_backed k (by simpa using hk) m' hslot
  | ret id m hcnt hr =>
    rw [PMF.mem_support_pure_iff] at hs'
    subst hs'
    refine ⟨by simpa using hInv.F_card, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro i k x hx
      rw [SubState.setProc_recv] at hx
      rw [SubState.setProc_sent]
      exact hInv.recv_sub i k hx
    · intro hldr m' hmem
      rw [SubState.setProc_sent] at hmem
      have hpre := hInv.init_conf (by simpa using hldr) m' hmem
      by_cases hkl : ldr = id
      · rw [hkl, SubState.setProc_proc_self]
        rw [hkl] at hpre
        exact hpre
      · rw [SubState.setProc_proc_ne _ _ _ hkl]
        exact hpre
    · intro k hk m' hmem
      rw [SubState.setProc_sent] at hmem
      have hpre := hInv.echo_conf k (by simpa using hk) m' hmem
      by_cases hkl : k = id
      · subst hkl
        rw [SubState.setProc_proc_self]
        exact hpre
      · rw [SubState.setProc_proc_ne _ _ _ hkl]
        exact hpre
    · intro k hk m' hslot
      rw [SubState.setProc_recv]
      by_cases hkl : k = id
      · subst hkl
        rw [SubState.setProc_proc_self] at hslot
        exact hInv.echo_backed k (by simpa using hk) m' hslot
      · rw [SubState.setProc_proc_ne _ _ _ hkl] at hslot
        exact hInv.echo_backed k (by simpa using hk) m' hslot
    · intro k hk m' hmem
      rw [SubState.setProc_sent] at hmem
      have hpre := hInv.vote_conf k (by simpa using hk) m' hmem
      by_cases hkl : k = id
      · subst hkl
        rw [SubState.setProc_proc_self]
        exact hpre
      · rw [SubState.setProc_proc_ne _ _ _ hkl]
        exact hpre
    · intro k hk m' hslot
      rw [echoCert_setProc]
      by_cases hkl : k = id
      · subst hkl
        rw [SubState.setProc_proc_self] at hslot
        exact hInv.vote_backed k (by simpa using hk) m' hslot
      · rw [SubState.setProc_proc_ne _ _ _ hkl] at hslot
        exact hInv.vote_backed k (by simpa using hk) m' hslot
  | fail id =>
    rw [PMF.mem_support_pure_iff] at hs'
    subst hs'
    have hF : ∀ k, k ∉ (s.corrupt P id).F → k ∉ s.F := fun k hk hkF =>
      hk (SubState.corrupt_F_subset s id hkF)
    refine ⟨SubState.corrupt_card_le s id hInv.F_card, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro i k x hx
      rw [SubState.corrupt_recv] at hx
      rw [SubState.corrupt_sent]
      exact hInv.recv_sub i k hx
    · intro hldr m' hmem
      rw [SubState.corrupt_sent] at hmem
      rw [SubState.corrupt_proc]
      exact hInv.init_conf (hF ldr hldr) m' hmem
    · intro k hk m' hmem
      rw [SubState.corrupt_sent] at hmem
      rw [SubState.corrupt_proc]
      exact hInv.echo_conf k (hF k hk) m' hmem
    · intro k hk m' hslot
      rw [SubState.corrupt_proc] at hslot
      rw [SubState.corrupt_recv]
      exact hInv.echo_backed k (hF k hk) m' hslot
    · intro k hk m' hmem
      rw [SubState.corrupt_sent] at hmem
      rw [SubState.corrupt_proc]
      exact hInv.vote_conf k (hF k hk) m' hmem
    · intro k hk m' hslot
      rw [SubState.corrupt_proc] at hslot
      rw [echoCert_corrupt]
      exact hInv.vote_backed k (hF k hk) m' hslot

/-! ### Deriving the certificate -/

/-- At most one value is ever echo-certified: two `ECHO` receipt quorums share
an honest sender, whose `sentEcho` field is write-once. -/
theorem echoCert_unique {s : ImplState P.n M} (hInv : Inv P ldr s) {m m' : M}
    (h : EchoCert P s m) (h' : EchoCert P s m') : m = m' := by
  obtain ⟨i, hi⟩ := h
  obtain ⟨i', hi'⟩ := h'
  obtain ⟨k, hkF, hkm, hkm'⟩ := SubState.exists_honest_recv₂ hInv.F_card hi hi'
  have h1 := hInv.echo_conf k hkF m (hInv.recv_sub i k hkm)
  have h2 := hInv.echo_conf k hkF m' (hInv.recv_sub i' k hkm')
  rw [h1] at h2
  injection h2

/-- Every `n − f` `VOTE m` receipt quorum yields the certificate: it contains
an honest voter, and honest votes are backed. -/
theorem echoCert_of_vote_quorum {s : ImplState P.n M} (hInv : Inv P ldr s)
    {i : Fin P.n} {m : M} (hcnt : P.n - P.f ≤ s.recvCount i (.vote m)) :
    EchoCert P s m := by
  have hlt : s.F.card < s.recvCount i (.vote m) :=
    lt_of_le_of_lt hInv.F_card (lt_of_lt_of_le P.f_lt_n_sub_f hcnt)
  obtain ⟨k, hkF, hkrecv⟩ := SubState.exists_sender_notMem s.F hlt
  exact hInv.vote_backed k hkF m
    (hInv.vote_conf k hkF m (hInv.recv_sub i k hkrecv))

/-- Under an honest leader, the certificate identifies the leader's input: the
`ECHO` quorum contains an honest echoer, backed by an `INIT` receipt from the
leader's sent. -/
theorem input_of_echoCert {s : ImplState P.n M} (hInv : Inv P ldr s)
    (hldr : ldr ∉ s.F) {m : M} (hc : EchoCert P s m) :
    (s.proc ldr).input = some m := by
  obtain ⟨i, hi⟩ := hc
  have hlt : s.F.card < s.recvCount i (.echo m) :=
    lt_of_le_of_lt hInv.F_card (lt_of_lt_of_le P.f_lt_n_sub_f hi)
  obtain ⟨k, hkF, hkrecv⟩ := SubState.exists_sender_notMem s.F hlt
  have hslot := hInv.echo_conf k hkF m (hInv.recv_sub i k hkrecv)
  have hinit := hInv.echo_backed k hkF m hslot
  exact hInv.init_conf hldr m (hInv.recv_sub k ldr hinit)

/-! ### The relation -/

/-- The BRB refinement relation. `val_cert` bounds the specification's
committed value by the certificate; the other clauses are projections. -/
structure InstRel (P : Params) (ldr : Fin P.n) (s : ImplState P.n M)
    (t : SpecState P.n M) : Prop where
  /-- The implementation invariant. -/
  inv : Inv P ldr s
  /-- The call records agree. -/
  input_eq : t.input = (s.proc ldr).input
  /-- The return flags agree. -/
  ret_eq : ∀ id, t.ret id = (s.proc id).returned
  /-- The corrupted sets agree. -/
  F_eq : t.F = s.F
  /-- A committed value is echo-certified. -/
  val_cert : ∀ m, t.val = some m → EchoCert P s m

/-- The relation holds initially. -/
theorem instRel_init :
    InstRel P ldr (ImplState.initial P.n M) (SpecState.initial P.n M) := by
  refine ⟨Inv.initial, ?_, ?_, ?_, ?_⟩ <;>
    simp [ImplState.initial, SpecState.initial, PState.initial]

/-- **Broadcast compatibility**: the relation is preserved by corrupting both
sides at once — the abstract state the family lifting consumes. -/
theorem instRel_corrupt {s : ImplState P.n M} {t : SpecState P.n M}
    (hR : InstRel P ldr s t) (id : Fin P.n) :
    InstRel P ldr (s.corrupt P id) (t.corrupt P id) := by
  refine ⟨hR.inv.step (ImplStep.fail s id) (by rw [PMF.mem_support_pure_iff]),
    ?_, ?_, ?_, ?_⟩
  · rw [corrupt_input, SubState.corrupt_proc]
    exact hR.input_eq
  · intro k
    rw [corrupt_ret, SubState.corrupt_proc]
    exact hR.ret_eq k
  · rw [SpecState.corrupt_F, SubState.corrupt_F, hR.F_eq]
  · intro m hm
    rw [corrupt_val] at hm
    rw [echoCert_corrupt]
    exact hR.val_cert m hm

/-- **The relation across one row**: every row of `ImplStep` at a related pair
is answered by a weak run of the specification instance, and the answer is
again related. Internal rows stutter; `call` and `fail` are answered by their
specification rows; `ret id m` is answered by `ret` alone when `val` is already
committed, and by the two-step run `commit ; ret` when it is not. -/
theorem instRel_row (P : Params) (ldr : Fin P.n) (q₁ : ImplState P.n M)
    (q₂ : SpecState P.n M) (hR : InstRel P ldr q₁ q₂) (l : Lab P.n M)
    (μ : PMF (ImplState P.n M)) (hstep : ImplStep P ldr q₁ l μ)
    (q₁' : ImplState P.n M) (hq₁' : q₁' ∈ μ.support) :
    ∃ q₂', ((l = Silent.τ ∧ (specInst P ldr M).weakLSilent q₂ q₂') ∨
      (¬ l = Silent.τ ∧ (specInst P ldr M).weakLStep q₂ l q₂')) ∧
      InstRel P ldr q₁' q₂' := by
  have hInv' := hR.inv.step hstep hq₁'
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
        rw [SubState.mcast_proc, SubState.setProc_proc_self]
        exact hR.ret_eq k
      · rw [SubState.mcast_proc, SubState.setProc_proc_ne _ _ _ hkl]
        exact hR.ret_eq k
    · simpa using hR.F_eq
    · intro m' hm'
      rw [echoCert_mcast, echoCert_setProc]
      exact hR.val_cert m' hm'
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
    · rw [SubState.recvMsg_proc]
      exact hR.input_eq
    · intro k
      rw [SubState.recvMsg_proc]
      exact hR.ret_eq k
    · simpa using hR.F_eq
    · intro m' hm'
      exact (hR.val_cert m' hm').recvMsg i j m
  | echo j m hrecv hsend =>
    rw [PMF.mem_support_pure_iff] at hq₁'
    subst hq₁'
    refine ⟨q₂, Or.inl ⟨rfl, System.weakLSilent_refl _ q₂⟩,
      hInv', ?_, ?_, ?_, ?_⟩
    · by_cases hkl : ldr = j
      · rw [SubState.mcast_proc, hkl, SubState.setProc_proc_self]
        rw [hR.input_eq, hkl]
      · rw [SubState.mcast_proc, SubState.setProc_proc_ne _ _ _ hkl]
        exact hR.input_eq
    · intro k
      by_cases hkl : k = j
      · subst hkl
        rw [SubState.mcast_proc, SubState.setProc_proc_self]
        exact hR.ret_eq k
      · rw [SubState.mcast_proc, SubState.setProc_proc_ne _ _ _ hkl]
        exact hR.ret_eq k
    · simpa using hR.F_eq
    · intro m' hm'
      rw [echoCert_mcast, echoCert_setProc]
      exact hR.val_cert m' hm'
  | voteQuorum j m hcnt hsend =>
    rw [PMF.mem_support_pure_iff] at hq₁'
    subst hq₁'
    refine ⟨q₂, Or.inl ⟨rfl, System.weakLSilent_refl _ q₂⟩,
      hInv', ?_, ?_, ?_, ?_⟩
    · by_cases hkl : ldr = j
      · rw [SubState.mcast_proc, hkl, SubState.setProc_proc_self]
        rw [hR.input_eq, hkl]
      · rw [SubState.mcast_proc, SubState.setProc_proc_ne _ _ _ hkl]
        exact hR.input_eq
    · intro k
      by_cases hkl : k = j
      · subst hkl
        rw [SubState.mcast_proc, SubState.setProc_proc_self]
        exact hR.ret_eq k
      · rw [SubState.mcast_proc, SubState.setProc_proc_ne _ _ _ hkl]
        exact hR.ret_eq k
    · simpa using hR.F_eq
    · intro m' hm'
      rw [echoCert_mcast, echoCert_setProc]
      exact hR.val_cert m' hm'
  | voteAmp j m hcnt hsend =>
    rw [PMF.mem_support_pure_iff] at hq₁'
    subst hq₁'
    refine ⟨q₂, Or.inl ⟨rfl, System.weakLSilent_refl _ q₂⟩,
      hInv', ?_, ?_, ?_, ?_⟩
    · by_cases hkl : ldr = j
      · rw [SubState.mcast_proc, hkl, SubState.setProc_proc_self]
        rw [hR.input_eq, hkl]
      · rw [SubState.mcast_proc, SubState.setProc_proc_ne _ _ _ hkl]
        exact hR.input_eq
    · intro k
      by_cases hkl : k = j
      · subst hkl
        rw [SubState.mcast_proc, SubState.setProc_proc_self]
        exact hR.ret_eq k
      · rw [SubState.mcast_proc, SubState.setProc_proc_ne _ _ _ hkl]
        exact hR.ret_eq k
    · simpa using hR.F_eq
    · intro m' hm'
      rw [echoCert_mcast, echoCert_setProc]
      exact hR.val_cert m' hm'
  | byz j m hj =>
    rw [PMF.mem_support_pure_iff] at hq₁'
    subst hq₁'
    refine ⟨q₂, Or.inl ⟨rfl, System.weakLSilent_refl _ q₂⟩,
      hInv', ?_, ?_, ?_, ?_⟩
    · rw [SubState.mcast_proc]
      exact hR.input_eq
    · intro k
      rw [SubState.mcast_proc]
      exact hR.ret_eq k
    · simpa using hR.F_eq
    · intro m' hm'
      rw [echoCert_mcast]
      exact hR.val_cert m' hm'
  | ret id m hcnt hr =>
    rw [PMF.mem_support_pure_iff] at hq₁'
    subst hq₁'
    have hcert : EchoCert P q₁ m := echoCert_of_vote_quorum hR.inv hcnt
    have hretQ : q₂.ret id = false := by rw [hR.ret_eq id]; exact hr
    have hRel : ∀ t' : SpecState P.n M, t'.val = some m →
        t'.input = q₂.input → t'.F = q₂.F →
        t'.ret = q₂.ret →
        InstRel P ldr (q₁.setProc id { q₁.proc id with returned := true })
          { t' with ret := Function.update t'.ret id true } := by
      intro t' hval hinput hF hret
      refine ⟨hInv', ?_, ?_, ?_, ?_⟩
      · rw [hinput]
        by_cases hkl : ldr = id
        · rw [hkl, SubState.setProc_proc_self]
          rw [hR.input_eq, hkl]
        · rw [SubState.setProc_proc_ne _ _ _ hkl]
          exact hR.input_eq
      · intro k
        by_cases hkl : k = id
        · subst hkl
          rw [SubState.setProc_proc_self]
          change Function.update t'.ret k true k = true
          rw [Function.update_self]
        · rw [SubState.setProc_proc_ne _ _ _ hkl]
          change Function.update t'.ret id true k = _
          rw [Function.update_of_ne hkl, hret]
          exact hR.ret_eq k
      · rw [SubState.setProc_F]
        rw [hF]
        exact hR.F_eq
      · intro m' hm'
        rw [echoCert_setProc]
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
        echoCert_unique hR.inv hcert (hR.val_cert m' hval)
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
            exact input_of_echoCert hR.inv hldr hcert)
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
      (Step.fail q₂ id)⟩, instRel_corrupt hR id⟩

/-- **The BRB refinement**: the reliable-broadcast instance is forward
simulated by the specification instance with the same leader, read over the
instance's interface. A transition of the instance is one row of `ImplStep`
(`BRB.implInst_step_row`), the row is answered by a weak run of the specification
(`instRel_row`), and that run is lifted to the interface along a section of
`specPull` — which is where the call loop is answered by the specification's
own loop row. -/
theorem brbRefines (P : Params) (ldr : Fin P.n) :
    ForwardSimulation (implInst P ldr M) (liftedSpec P ldr M) (InstRel P ldr) := by
  constructor
  intro q₁ q₂ hR l μ hstep q₁' hq₁'
  obtain ⟨l₀, hpull, hrow⟩ := implInst_step_row P ldr q₁ l μ hstep
  obtain ⟨s', hdis, hrel⟩ := instRel_row P ldr q₁ q₂ hR l₀ μ hrow q₁' hq₁'
  refine ⟨s', ?_, hrel⟩
  rcases hdis with ⟨hτ, hweak⟩ | ⟨hτ, hweak⟩
  · exact Or.inl ⟨specPull_eq_tau (by rw [hpull, hτ]; rfl),
      weakLSilent_liftedSpec P ldr hweak⟩
  · refine Or.inr ⟨?_, weakLStep_liftedSpec P ldr hτ hpull hweak⟩
    intro hl
    refine hτ ?_
    have h2 : specPull P.n M (Silent.τ : InstLab P.n M) = some l₀ := by rw [← hl]; exact hpull
    rw [specPull_tau] at h2
    exact (Option.some.inj h2).symm

/-! ### Step-level relation transports

The relation across one row, exported for systems that replay the BRB rows
inside a larger rule table: internal rows under a specification stutter, the
call across the fused effects, and the on-demand commit that a derived
delivery licenses. -/

/-- The relation across any internal row, the specification stuttering. -/
theorem instRel_tau {P : Params} {ldr : Fin P.n} {s s' : ImplState P.n M}
    {t : SpecState P.n M} (hR : InstRel P ldr s t)
    (hstep : ImplStep P ldr s Lab.tau (PMF.pure s')) : InstRel P ldr s' t := by
  have hInv' := hR.inv.step hstep (by rw [PMF.mem_support_pure_iff])
  generalize hμ : (PMF.pure s' : PMF (ImplState P.n M)) = μ at hstep
  cases hstep with
  | deliver i j m h =>
    have hs' := PMF.pure_injective hμ
    subst hs'
    refine ⟨hInv', ?_, ?_, ?_, ?_⟩
    · rw [SubState.recvMsg_proc]
      exact hR.input_eq
    · intro k
      rw [SubState.recvMsg_proc]
      exact hR.ret_eq k
    · simpa using hR.F_eq
    · intro m' hm'
      exact (hR.val_cert m' hm').recvMsg i j m
  | echo j m hrecv hsend =>
    have hs' := PMF.pure_injective hμ
    subst hs'
    refine ⟨hInv', ?_, ?_, ?_, ?_⟩
    · by_cases hkl : ldr = j
      · rw [SubState.mcast_proc, hkl, SubState.setProc_proc_self]
        rw [hR.input_eq, hkl]
      · rw [SubState.mcast_proc, SubState.setProc_proc_ne _ _ _ hkl]
        exact hR.input_eq
    · intro k
      by_cases hkl : k = j
      · subst hkl
        rw [SubState.mcast_proc, SubState.setProc_proc_self]
        exact hR.ret_eq k
      · rw [SubState.mcast_proc, SubState.setProc_proc_ne _ _ _ hkl]
        exact hR.ret_eq k
    · simpa using hR.F_eq
    · intro m' hm'
      rw [echoCert_mcast, echoCert_setProc]
      exact hR.val_cert m' hm'
  | voteQuorum j m hcnt hsend =>
    have hs' := PMF.pure_injective hμ
    subst hs'
    refine ⟨hInv', ?_, ?_, ?_, ?_⟩
    · by_cases hkl : ldr = j
      · rw [SubState.mcast_proc, hkl, SubState.setProc_proc_self]
        rw [hR.input_eq, hkl]
      · rw [SubState.mcast_proc, SubState.setProc_proc_ne _ _ _ hkl]
        exact hR.input_eq
    · intro k
      by_cases hkl : k = j
      · subst hkl
        rw [SubState.mcast_proc, SubState.setProc_proc_self]
        exact hR.ret_eq k
      · rw [SubState.mcast_proc, SubState.setProc_proc_ne _ _ _ hkl]
        exact hR.ret_eq k
    · simpa using hR.F_eq
    · intro m' hm'
      rw [echoCert_mcast, echoCert_setProc]
      exact hR.val_cert m' hm'
  | voteAmp j m hcnt hsend =>
    have hs' := PMF.pure_injective hμ
    subst hs'
    refine ⟨hInv', ?_, ?_, ?_, ?_⟩
    · by_cases hkl : ldr = j
      · rw [SubState.mcast_proc, hkl, SubState.setProc_proc_self]
        rw [hR.input_eq, hkl]
      · rw [SubState.mcast_proc, SubState.setProc_proc_ne _ _ _ hkl]
        exact hR.input_eq
    · intro k
      by_cases hkl : k = j
      · subst hkl
        rw [SubState.mcast_proc, SubState.setProc_proc_self]
        exact hR.ret_eq k
      · rw [SubState.mcast_proc, SubState.setProc_proc_ne _ _ _ hkl]
        exact hR.ret_eq k
    · simpa using hR.F_eq
    · intro m' hm'
      rw [echoCert_mcast, echoCert_setProc]
      exact hR.val_cert m' hm'
  | byz j m hj =>
    have hs' := PMF.pure_injective hμ
    subst hs'
    refine ⟨hInv', ?_, ?_, ?_, ?_⟩
    · rw [SubState.mcast_proc]
      exact hR.input_eq
    · intro k
      rw [SubState.mcast_proc]
      exact hR.ret_eq k
    · simpa using hR.F_eq
    · intro m' hm'
      rw [echoCert_mcast]
      exact hR.val_cert m' hm'

/-- An internal row leaves the corrupted set alone. -/
theorem implStep_tau_F {P : Params} {ldr : Fin P.n} {s s' : ImplState P.n M}
    (hstep : ImplStep P ldr s Lab.tau (PMF.pure s')) : s'.F = s.F := by
  generalize hμ : (PMF.pure s' : PMF (ImplState P.n M)) = μ at hstep
  cases hstep with
  | deliver i j m h =>
    have hs' := PMF.pure_injective hμ
    subst hs'
    rfl
  | echo j m hrecv hsend =>
    have hs' := PMF.pure_injective hμ
    subst hs'
    simp
  | voteQuorum j m hcnt hsend =>
    have hs' := PMF.pure_injective hμ
    subst hs'
    simp
  | voteAmp j m hcnt hsend =>
    have hs' := PMF.pure_injective hμ
    subst hs'
    simp
  | byz j m hj =>
    have hs' := PMF.pure_injective hμ
    subst hs'
    simp

/-- The relation across the leader's call, the specification calling too. -/
theorem instRel_call {P : Params} {ldr : Fin P.n} {s : ImplState P.n M}
    {t : SpecState P.n M} (hR : InstRel P ldr s t) {m : M}
    (h : (s.proc ldr).input = none) :
    InstRel P ldr
      ((s.setProc ldr { s.proc ldr with input := some m }).mcast ldr (.init m))
      { t with input := some m } := by
  refine ⟨hR.inv.step (ImplStep.call s m h) (by rw [PMF.mem_support_pure_iff]),
    ?_, ?_, ?_, ?_⟩
  · dsimp only
    rw [SubState.mcast_proc, SubState.setProc_proc_self]
  · intro k
    by_cases hkl : k = ldr
    · subst hkl
      rw [SubState.mcast_proc, SubState.setProc_proc_self]
      exact hR.ret_eq k
    · rw [SubState.mcast_proc, SubState.setProc_proc_ne _ _ _ hkl]
      exact hR.ret_eq k
  · simpa using hR.F_eq
  · intro m' hm'
    rw [echoCert_mcast, echoCert_setProc]
    exact hR.val_cert m' hm'

/-- **The on-demand commit.** A `VOTE` receipt quorum licenses the
specification's committed value: either it is already this value, or the
`commit` guard holds towards it, the relation restored either way. -/
theorem commitReach {P : Params} {ldr : Fin P.n} {s : ImplState P.n M}
    {t : SpecState P.n M} (hR : InstRel P ldr s t) {id : Fin P.n} {m : M}
    (hcnt : P.n - P.f ≤ s.recvCount id (.vote m)) :
    (t.val = some m ∧ InstRel P ldr s t) ∨
    (t.val = none ∧ (ldr ∈ t.F ∨ t.input = some m) ∧
      InstRel P ldr s { t with val := some m }) := by
  have hcert : EchoCert P s m := echoCert_of_vote_quorum hR.inv hcnt
  rcases hval : t.val with _ | m'
  · right
    have hcommit : ldr ∈ t.F ∨ t.input = some m := by
      by_cases hldr : ldr ∈ s.F
      · exact Or.inl (by rw [hR.F_eq]; exact hldr)
      · exact Or.inr (by
          rw [hR.input_eq]
          exact input_of_echoCert hR.inv hldr hcert)
    refine ⟨rfl, hcommit, hR.inv, ?_, hR.ret_eq, hR.F_eq, ?_⟩
    · dsimp only
      exact hR.input_eq
    · intro m'' hm''
      dsimp only at hm''
      obtain rfl : m = m'' := by injection hm''
      exact hcert
  · left
    obtain rfl : m' = m :=
      echoCert_unique hR.inv (hR.val_cert m' hval) hcert
    exact ⟨rfl, hR⟩

/-- info: 'PLTS.ABA.BRB.brbRefines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms brbRefines

end BRB
end ABA
end PLTS
