/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sathiya / Claude
-/

import Leslie2Protocols.ABA.Params

/-!
# The two boxes of a sub-protocol instance, generically

The data of one message-passing sub-protocol instance sits in two boxes:
each process holds its own local record beside the messages delivered to it,
and the instance's message fabric holds the per-sender pools and the corrupted
set. The GBCA implementation introduced this shape for one concrete message
type; the sub-protocol towers (BRB, Gather) repeat it at their own payload
types, so the shape is stated here once, generically:

* `ABA.Fabric n M` — the fabric: per-sender pools over payload type `M`, and
  the corrupted set;
* `ABA.Box n Pr M` — one process's box: its local record `Pr` and its
  delivered sets, indexed by sender;
* `ABA.SubState n Pr M` — the instance state, the pair of the box vector and
  the fabric, with the multicast / delivery / corruption updates
  (`mcast`, `recvMsg`, `corrupt`), the receipt counts (`recvCount`), the
  frame lemmas each update leaves behind, and the quorum-counting kit
  (`exists_sender_notMem`, `exists_honest_recv₂`).

The model conventions are the development's D1 (corruption is the total Dirac
budget-guarded transform of the fabric, the boxes are corruption-blind) and
D5 (the network is a set: multicasts are idempotent, thresholds count distinct
senders in the receiver's delivered sets).
-/

namespace PLTS
namespace ABA

/-! ### The fabric -/

/-- The message fabric of one sub-protocol instance: the per-sender pools over
payload type `M`, and the corrupted set. -/
structure Fabric (n : ℕ) (M : Type) : Type where
  /-- `pool j` — the messages process `j` has multicast in this instance (D5). -/
  pool : Fin n → Finset M
  /-- The corrupted set. -/
  F : Finset (Fin n)
  deriving DecidableEq

namespace Fabric

variable {n : ℕ} {M : Type}

/-- The initial fabric: nothing multicast, nobody corrupted. -/
def initial (n : ℕ) (M : Type) : Fabric n M where
  pool := fun _ => ∅
  F := ∅

@[simp] theorem initial_pool (j : Fin n) : (initial n M).pool j = ∅ := rfl
@[simp] theorem initial_F : (initial n M).F = ∅ := rfl

/-- Corruption (deviation D1): total, Dirac, budget-guarded. -/
def corrupt (P : Params) (id : Fin P.n) (w : Fabric P.n M) : Fabric P.n M :=
  if id ∉ w.F ∧ w.F.card < P.f then { w with F := insert id w.F } else w

@[simp] theorem corrupt_pool {P : Params} (w : Fabric P.n M) (id : Fin P.n) :
    (w.corrupt P id).pool = w.pool := by
  unfold corrupt; split <;> rfl

section Post

variable [DecidableEq M]

/-- Pool `m` under sender `j` (D5). -/
def post (w : Fabric n M) (j : Fin n) (m : M) : Fabric n M :=
  { w with pool := Function.update w.pool j (insert m (w.pool j)) }

@[simp] theorem post_F (w : Fabric n M) (j : Fin n) (m : M) :
    (w.post j m).F = w.F := rfl

/-- Membership in a pool after a multicast. -/
theorem mem_post {w : Fabric n M} {j : Fin n} {m : M} {k : Fin n} {m' : M} :
    m' ∈ (w.post j m).pool k ↔ (k = j ∧ m' = m) ∨ m' ∈ w.pool k := by
  change m' ∈ Function.update w.pool j (insert m (w.pool j)) k ↔ _
  by_cases hk : k = j
  · subst hk
    rw [Function.update_self, Finset.mem_insert]
    simp
  · rw [Function.update_of_ne hk]
    simp [hk]

end Post

end Fabric

/-! ### The box of one process -/

/-- The box of one process: its own local record and the messages delivered to
it, indexed by sender. There is no record of what it has sent — the sender's
pool lives in the fabric. -/
structure Box (n : ℕ) (Pr M : Type) : Type where
  /-- The process's own local record. -/
  proc : Pr
  /-- `inbox k` — the messages from sender `k` delivered here. -/
  inbox : Fin n → Finset M
  deriving DecidableEq

namespace Box

variable {n : ℕ} {Pr M : Type}

/-- The initial box over the initial local record `p₀`. -/
def initial (n : ℕ) (M : Type) (p₀ : Pr) : Box n Pr M where
  proc := p₀
  inbox := fun _ => ∅

@[simp] theorem initial_proc (p₀ : Pr) : (initial n M p₀).proc = p₀ := rfl
@[simp] theorem initial_inbox (p₀ : Pr) (k : Fin n) :
    (initial n M p₀).inbox k = ∅ := rfl

/-- Overwrite the local record. -/
def setP (p : Box n Pr M) (pr : Pr) : Box n Pr M := { p with proc := pr }

/-- File `m` under the inbox row of sender `k`. -/
def deliverTo [DecidableEq M] (p : Box n Pr M) (k : Fin n) (m : M) : Box n Pr M :=
  { p with inbox := Function.update p.inbox k (insert m (p.inbox k)) }

end Box

/-! ### The instance state -/

/-- **The state of one sub-protocol instance**: the `n` boxes beside the
instance's message fabric. -/
abbrev SubState (n : ℕ) (Pr M : Type) : Type := (∀ _ : Fin n, Box n Pr M) × Fabric n M

namespace SubState

variable {n : ℕ} {Pr M : Type}

/-- Per-process local records. -/
def proc (s : SubState n Pr M) : Fin n → Pr := fun j => (s.1 j).proc

/-- `sent j` — the messages process `j` has multicast (D5). -/
def sent (s : SubState n Pr M) : Fin n → Finset M := s.2.pool

/-- `recv i j` — the messages from sender `j` delivered to receiver `i`. -/
def recv (s : SubState n Pr M) : Fin n → Fin n → Finset M := fun i => (s.1 i).inbox

/-- The corrupted set (the fabric's, kept in lockstep by `fail` broadcast). -/
def F (s : SubState n Pr M) : Finset (Fin n) := s.2.F

@[simp] theorem proc_apply (u : ∀ _ : Fin n, Box n Pr M) (w : Fabric n M)
    (j : Fin n) : proc (u, w) j = (u j).proc := rfl
@[simp] theorem sent_apply (u : ∀ _ : Fin n, Box n Pr M) (w : Fabric n M) :
    sent (u, w) = w.pool := rfl
@[simp] theorem recv_apply (u : ∀ _ : Fin n, Box n Pr M) (w : Fabric n M)
    (i : Fin n) : recv (u, w) i = (u i).inbox := rfl
@[simp] theorem F_apply (u : ∀ _ : Fin n, Box n Pr M) (w : Fabric n M) :
    F (u, w) = w.F := rfl

/-- The initial instance state over the initial local record `p₀`. -/
def initial (n : ℕ) (M : Type) (p₀ : Pr) : SubState n Pr M :=
  (fun _ => Box.initial n M p₀, Fabric.initial n M)

@[simp] theorem initial_proc (p₀ : Pr) (j : Fin n) :
    (initial n M p₀).proc j = p₀ := rfl
@[simp] theorem initial_sent (p₀ : Pr) (j : Fin n) :
    (initial n M p₀).sent j = ∅ := rfl
@[simp] theorem initial_recv (p₀ : Pr) (i j : Fin n) :
    (initial n M p₀).recv i j = ∅ := rfl
@[simp] theorem initial_F (p₀ : Pr) : (initial n M p₀).F = ∅ := rfl

/-- Update the local record of process `j`. -/
def setProc (s : SubState n Pr M) (j : Fin n) (p : Pr) : SubState n Pr M :=
  (Function.update s.1 j ((s.1 j).setP p), s.2)

@[simp] theorem setProc_sent (s : SubState n Pr M) (j : Fin n) (p : Pr) :
    (s.setProc j p).sent = s.sent := rfl
@[simp] theorem setProc_F (s : SubState n Pr M) (j : Fin n) (p : Pr) :
    (s.setProc j p).F = s.F := rfl

@[simp] theorem setProc_recv (s : SubState n Pr M) (j : Fin n) (p : Pr) :
    (s.setProc j p).recv = s.recv := by
  funext i
  by_cases hi : i = j
  · subst hi; simp [setProc, recv, Box.setP]
  · simp [setProc, recv, Function.update_of_ne hi]

@[simp] theorem setProc_proc_self (s : SubState n Pr M) (j : Fin n) (p : Pr) :
    (s.setProc j p).proc j = p := by
  simp [setProc, proc, Box.setP]

theorem setProc_proc_ne (s : SubState n Pr M) (j : Fin n) (p : Pr)
    {k : Fin n} (h : k ≠ j) : (s.setProc j p).proc k = s.proc k := by
  simp [setProc, proc, Function.update_of_ne h]

/-- The record vector after a record write, as one `ite`. -/
theorem proc_setProc (s : SubState n Pr M) (j : Fin n) (p : Pr) (k : Fin n) :
    (s.setProc j p).proc k = if k = j then p else s.proc k := by
  by_cases hk : k = j
  · subst hk; simp
  · simp [setProc_proc_ne _ _ _ hk, hk]

/-- Corruption (deviation D1): total, Dirac, the fabric's own row — the boxes
are corruption-blind. -/
def corrupt (P : Params) (id : Fin P.n) (s : SubState P.n Pr M) : SubState P.n Pr M :=
  (s.1, s.2.corrupt P id)

@[simp] theorem corrupt_proc {P : Params} (s : SubState P.n Pr M) (id : Fin P.n) :
    (s.corrupt P id).proc = s.proc := rfl
@[simp] theorem corrupt_recv {P : Params} (s : SubState P.n Pr M) (id : Fin P.n) :
    (s.corrupt P id).recv = s.recv := rfl
@[simp] theorem corrupt_sent {P : Params} (s : SubState P.n Pr M) (id : Fin P.n) :
    (s.corrupt P id).sent = s.sent := by
  unfold corrupt sent Fabric.corrupt; split <;> rfl

/-- The corrupted set after a corruption. Not a simp lemma: it introduces an
`ite`. -/
theorem corrupt_F {P : Params} (s : SubState P.n Pr M) (id : Fin P.n) :
    (s.corrupt P id).F = if id ∉ s.F ∧ s.F.card < P.f then insert id s.F else s.F := by
  unfold corrupt F Fabric.corrupt
  split_ifs <;> rfl

theorem corrupt_F_subset {P : Params} (s : SubState P.n Pr M) (id : Fin P.n) :
    s.F ⊆ (s.corrupt P id).F := by
  rw [corrupt_F]
  split
  · exact Finset.subset_insert _ _
  · exact Finset.Subset.refl _

theorem corrupt_card_le {P : Params} (s : SubState P.n Pr M) (id : Fin P.n)
    (hF : s.F.card ≤ P.f) : (s.corrupt P id).F.card ≤ P.f := by
  rw [corrupt_F]
  split
  · next hc =>
    have h2 := hc.2
    have h3 := Finset.card_insert_le id s.F
    omega
  · exact hF

/-- A set strictly larger than `G` has a member outside `G`. -/
theorem exists_honest_of_card_lt {Q G : Finset (Fin n)} (h : G.card < Q.card) :
    ∃ j ∈ Q, j ∉ G := by
  by_contra hc
  refine absurd (Finset.card_le_card fun j hj => ?_) (not_le.mpr h)
  by_contra hjF
  exact hc ⟨j, hj, hjF⟩

/-- Two `n − f` quorums share an honest member:
`(n−f) + (n−f) − n = n − 2f > f ≥ |F|`. -/
theorem exists_honest_inter {P : Params} {F Q Q' : Finset (Fin P.n)}
    (hF : F.card ≤ P.f) (hQ : P.n - P.f ≤ Q.card) (hQ' : P.n - P.f ≤ Q'.card) :
    ∃ q, q ∈ Q ∧ q ∈ Q' ∧ q ∉ F := by
  have hcard := Finset.card_union_add_card_inter Q Q'
  have hun : (Q ∪ Q').card ≤ P.n := by
    refine le_trans (Finset.card_le_univ _) ?_
    simp
  have hf := P.hf
  have hlt : F.card < (Q ∩ Q').card := by omega
  obtain ⟨q, hq, hqF⟩ := exists_honest_of_card_lt hlt
  rw [Finset.mem_inter] at hq
  exact ⟨q, hq.1, hq.2, hqF⟩

/-- An `f + 1`-set and an `n − f` quorum intersect: `(f+1) + (n−f) > n`. -/
theorem exists_mem_inter_of_quorum {P : Params} {K Q : Finset (Fin P.n)}
    (hK : P.f + 1 ≤ K.card) (hQ : P.n - P.f ≤ Q.card) :
    ∃ q, q ∈ K ∧ q ∈ Q := by
  have hcard := Finset.card_union_add_card_inter K Q
  have hun : (K ∪ Q).card ≤ P.n := by
    refine le_trans (Finset.card_le_univ _) ?_
    simp
  have hf := P.hf
  have hlt : 0 < (K ∩ Q).card := by omega
  obtain ⟨q, hq⟩ := Finset.card_pos.mp hlt
  rw [Finset.mem_inter] at hq
  exact ⟨q, hq.1, hq.2⟩

section Counting

variable [DecidableEq M]

/-- The number of distinct senders from which `i` has received `m`. -/
def recvCount (s : SubState n Pr M) (i : Fin n) (m : M) : ℕ :=
  (Finset.univ.filter (fun j => m ∈ s.recv i j)).card

@[simp] theorem setProc_recvCount (s : SubState n Pr M) (j : Fin n) (p : Pr)
    (i : Fin n) (m : M) : (s.setProc j p).recvCount i m = s.recvCount i m := by
  simp [recvCount]

@[simp] theorem corrupt_recvCount {P : Params} (s : SubState P.n Pr M) (id : Fin P.n)
    (i : Fin P.n) (m : M) :
    (s.corrupt P id).recvCount i m = s.recvCount i m := rfl

/-- Process `j` multicasts `m`: the fabric pools it under `j`. -/
def mcast (s : SubState n Pr M) (j : Fin n) (m : M) : SubState n Pr M :=
  (s.1, s.2.post j m)

@[simp] theorem mcast_proc (s : SubState n Pr M) (j : Fin n) (m : M) :
    (s.mcast j m).proc = s.proc := rfl
@[simp] theorem mcast_recv (s : SubState n Pr M) (j : Fin n) (m : M) :
    (s.mcast j m).recv = s.recv := rfl
@[simp] theorem mcast_F (s : SubState n Pr M) (j : Fin n) (m : M) :
    (s.mcast j m).F = s.F := rfl
@[simp] theorem mcast_recvCount (s : SubState n Pr M) (j : Fin n) (m : M)
    (i : Fin n) (m' : M) : (s.mcast j m).recvCount i m' = s.recvCount i m' := rfl

/-- Membership in a sent pool after a multicast. -/
theorem mem_mcast_sent {s : SubState n Pr M} {j : Fin n} {m : M} {k : Fin n}
    {m' : M} :
    m' ∈ (s.mcast j m).sent k ↔ (k = j ∧ m' = m) ∨ m' ∈ s.sent k := by
  change m' ∈ (s.2.post j m).pool k ↔ (k = j ∧ m' = m) ∨ m' ∈ s.2.pool k
  exact Fabric.mem_post

theorem sent_subset_mcast (s : SubState n Pr M) (j : Fin n) (m : M) (k : Fin n) :
    s.sent k ⊆ (s.mcast j m).sent k :=
  fun _ h => mem_mcast_sent.mpr (Or.inr h)

/-- The adversary delivers `m` from sender `j` to receiver `i`: the receiver's
box files it under `j`'s row. -/
def recvMsg (s : SubState n Pr M) (i j : Fin n) (m : M) : SubState n Pr M :=
  (Function.update s.1 i ((s.1 i).deliverTo j m), s.2)

@[simp] theorem recvMsg_sent (s : SubState n Pr M) (i j : Fin n) (m : M) :
    (s.recvMsg i j m).sent = s.sent := rfl
@[simp] theorem recvMsg_F (s : SubState n Pr M) (i j : Fin n) (m : M) :
    (s.recvMsg i j m).F = s.F := rfl

@[simp] theorem recvMsg_proc (s : SubState n Pr M) (i j : Fin n) (m : M) :
    (s.recvMsg i j m).proc = s.proc := by
  funext k
  by_cases hk : k = i
  · subst hk; simp [recvMsg, proc, Box.deliverTo]
  · simp [recvMsg, proc, Function.update_of_ne hk]

/-- Membership in a delivered set after a delivery. -/
theorem mem_recvMsg_recv {s : SubState n Pr M} {i j : Fin n} {m : M}
    {i' j' : Fin n} {m' : M} :
    m' ∈ (s.recvMsg i j m).recv i' j' ↔
      (i' = i ∧ j' = j ∧ m' = m) ∨ m' ∈ s.recv i' j' := by
  by_cases hi : i' = i
  · subst hi
    change m' ∈ (Function.update s.1 i' ((s.1 i').deliverTo j m) i').inbox j' ↔ _
    rw [Function.update_self]
    change m' ∈ Function.update ((s.1 i').inbox) j (insert m ((s.1 i').inbox j)) j' ↔ _
    by_cases hj : j' = j
    · subst hj
      rw [Function.update_self, Finset.mem_insert]
      simp [recv]
    · rw [Function.update_of_ne hj]
      simp [hj, recv]
  · change m' ∈ (Function.update s.1 i ((s.1 i).deliverTo j m) i').inbox j' ↔ _
    rw [Function.update_of_ne hi]
    simp [hi, recv]

/-- Deliveries only grow the receiver counts. -/
theorem recvCount_le_recvMsg (s : SubState n Pr M) (i j : Fin n) (m : M)
    (i' : Fin n) (m' : M) :
    s.recvCount i' m' ≤ (s.recvMsg i j m).recvCount i' m' := by
  refine Finset.card_le_card fun k hk => ?_
  rw [Finset.mem_filter] at hk ⊢
  exact ⟨hk.1, mem_recvMsg_recv.mpr (Or.inr hk.2)⟩

/-- A receipt count exceeding `|G|` yields a sender outside `G`. -/
theorem exists_sender_notMem {P : Params} {s : SubState P.n Pr M}
    (G : Finset (Fin P.n)) {i : Fin P.n} {m : M} (h : G.card < s.recvCount i m) :
    ∃ j, j ∉ G ∧ m ∈ s.recv i j := by
  unfold recvCount at h
  obtain ⟨j, hjQ, hjF⟩ := exists_honest_of_card_lt h
  rw [Finset.mem_filter] at hjQ
  exact ⟨j, hjF, hjQ.2⟩

/-- Two `n − f` receipt quorums (at possibly different receivers) share an
honest sender: `(n−f) + (n−f) − n = n − 2f > f ≥ |F|`. -/
theorem exists_honest_recv₂ {P : Params} {s : SubState P.n Pr M} (hF : s.F.card ≤ P.f)
    {i i' : Fin P.n} {m m' : M}
    (h : P.n - P.f ≤ s.recvCount i m) (h' : P.n - P.f ≤ s.recvCount i' m') :
    ∃ j, j ∉ s.F ∧ m ∈ s.recv i j ∧ m' ∈ s.recv i' j := by
  unfold recvCount at h h'
  have hcard := Finset.card_union_add_card_inter
    (Finset.univ.filter (fun j => m ∈ s.recv i j))
    (Finset.univ.filter (fun j => m' ∈ s.recv i' j))
  have hun : ((Finset.univ.filter (fun j => m ∈ s.recv i j)) ∪
      (Finset.univ.filter (fun j => m' ∈ s.recv i' j))).card ≤ P.n := by
    refine le_trans (Finset.card_le_univ _) ?_
    simp
  have hf := P.hf
  have hlt : s.F.card < ((Finset.univ.filter (fun j => m ∈ s.recv i j)) ∩
      (Finset.univ.filter (fun j => m' ∈ s.recv i' j))).card := by omega
  obtain ⟨j, hj, hjF⟩ := exists_honest_of_card_lt hlt
  rw [Finset.mem_inter, Finset.mem_filter, Finset.mem_filter] at hj
  exact ⟨j, hjF, hj.1.2, hj.2.2⟩

end Counting

end SubState

end ABA
end PLTS
