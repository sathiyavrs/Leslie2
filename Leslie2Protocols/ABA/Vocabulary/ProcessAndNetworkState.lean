/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sathiya / Claude
-/

import Leslie2Protocols.ABA.Vocabulary.Parameters

/-!
# The two halves of a sub-protocol instance state, generically

The data of one message-passing sub-protocol instance sits in two halves:
each process holds its own local record beside the messages delivered to it,
and the instance's network state holds the per-sender sent sets and the corrupted
set. The GBCA implementation introduced this shape for one concrete message
type; the sub-protocol tiers (BRB, Gather) repeat it at their own payload
types, so the shape is stated here once, generically:

* `ABA.NetworkState n M` — the network state: per-sender sent sets over payload type `M`, and
  the corrupted set;
* `ABA.LocalState n Pr M` — one process's local state: its local record `Pr` and its
  delivered sets, indexed by sender;
* `ABA.InstanceState n Pr M` — the instance state, the pair of the local state vector and
  the network state, with the multicast / delivery / corruption updates
  (`multicast`, `receiveMessage`, `corrupt`), the receipt counts (`receivedCount`), the
  frame lemmas each update leaves behind, and the quorum-counting kit
  (`exists_sender_notMem`, `exists_correct_received₂`, `exists_correct_received₂_echoQuorum`).

The model conventions are the development's D1 (corruption is the total Dirac
budget-guarded transform of the network state, the local states are corruption-blind) and
D5 (the network is a set: multicasts are idempotent, thresholds count distinct
senders in the receiver's delivered sets).
-/

namespace PLTS
namespace ABA

/-! ### The network state -/

/-- The network state of one sub-protocol instance: the per-sender sent sets over
payload type `M`, and the corrupted set. -/
structure NetworkState (n : ℕ) (M : Type) : Type where
  /-- `sent j` — the messages process `j` has multicast in this instance (D5). -/
  sent : Fin n → Finset M
  /-- The corrupted set. -/
  F : Finset (Fin n)
  deriving DecidableEq

namespace NetworkState

variable {n : ℕ} {M : Type}

/-- The initial network state: nothing multicast, nobody corrupted. -/
def initial (n : ℕ) (M : Type) : NetworkState n M where
  sent := fun _ => ∅
  F := ∅

@[simp] theorem initial_sent (j : Fin n) : (initial n M).sent j = ∅ := rfl
@[simp] theorem initial_F : (initial n M).F = ∅ := rfl

/-- Corruption (deviation D1): total, Dirac, budget-guarded. -/
def corrupt (P : Parameters) (id : Fin P.n) (w : NetworkState P.n M) : NetworkState P.n M :=
  if id ∉ w.F ∧ w.F.card < P.f then { w with F := insert id w.F } else w

@[simp] theorem corrupt_sent {P : Parameters} (w : NetworkState P.n M) (id : Fin P.n) :
    (w.corrupt P id).sent = w.sent := by
  unfold corrupt; split <;> rfl

section Post

variable [DecidableEq M]

/-- Sent `m` under sender `j` (D5). -/
def recordSent (w : NetworkState n M) (j : Fin n) (m : M) : NetworkState n M :=
  { w with sent := Function.update w.sent j (insert m (w.sent j)) }

@[simp] theorem recordSent_F (w : NetworkState n M) (j : Fin n) (m : M) :
    (w.recordSent j m).F = w.F := rfl

/-- Membership in a sent after a multicast. -/
theorem mem_recordSent {w : NetworkState n M} {j : Fin n} {m : M} {k : Fin n} {m' : M} :
    m' ∈ (w.recordSent j m).sent k ↔ (k = j ∧ m' = m) ∨ m' ∈ w.sent k := by
  change m' ∈ Function.update w.sent j (insert m (w.sent j)) k ↔ _
  by_cases hk : k = j
  · subst hk
    rw [Function.update_self, Finset.mem_insert]
    simp
  · rw [Function.update_of_ne hk]
    simp [hk]

end Post

end NetworkState

/-! ### The local state of one process -/

/-- The local state of one process: its own local record and the messages delivered to
it, indexed by sender. There is no record of what it has sent — the sender's
sent lives in the network state. -/
structure LocalState (n : ℕ) (Pr M : Type) : Type where
  /-- The process's own local record. -/
  process : Pr
  /-- `received k` — the messages from sender `k` delivered here. -/
  received : Fin n → Finset M
  deriving DecidableEq

namespace LocalState

variable {n : ℕ} {Pr M : Type}

/-- The initial local state over the initial local record `p₀`. -/
def initial (n : ℕ) (M : Type) (p₀ : Pr) : LocalState n Pr M where
  process := p₀
  received := fun _ => ∅

@[simp] theorem initial_process (p₀ : Pr) : (initial n M p₀).process = p₀ := rfl
@[simp] theorem initial_received (p₀ : Pr) (k : Fin n) :
    (initial n M p₀).received k = ∅ := rfl

/-- Overwrite the local record. -/
def setProcess (p : LocalState n Pr M) (pr : Pr) : LocalState n Pr M := { p with process := pr }

/-- File `m` under the recv row of sender `k`. -/
def deliverTo [DecidableEq M] (p : LocalState n Pr M) (k : Fin n) (m : M) : LocalState n Pr M :=
  { p with received := Function.update p.received k (insert m (p.received k)) }

/-- The number of distinct senders from which this local state holds `m`. A receipt
threshold read at one process is a count on that process's local state alone, which is
what lets a flat reading state it locally. -/
def receivedCount [DecidableEq M] (p : LocalState n Pr M) (m : M) : ℕ :=
  (Finset.univ.filter (fun q => m ∈ p.received q)).card

end LocalState

/-! ### The instance state -/

/-- **The state of one sub-protocol instance**: the `n` local states beside the
instance's network state. -/
abbrev InstanceState (n : ℕ) (Pr M : Type) : Type :=
  (∀ _ : Fin n, LocalState n Pr M) × NetworkState n M

namespace InstanceState

variable {n : ℕ} {Pr M : Type}

/-- Per-process local records. -/
def process (s : InstanceState n Pr M) : Fin n → Pr := fun j => (s.1 j).process

/-- `sent j` — the messages process `j` has multicast (D5). -/
def sent (s : InstanceState n Pr M) : Fin n → Finset M := s.2.sent

/-- `received i j` — the messages from sender `j` delivered to receiver `i`. -/
def received (s : InstanceState n Pr M) : Fin n → Fin n → Finset M := fun i => (s.1 i).received

/-- The corrupted set (the network state's, kept in lockstep by `fail` broadcast). -/
def F (s : InstanceState n Pr M) : Finset (Fin n) := s.2.F

@[simp] theorem process_apply (u : ∀ _ : Fin n, LocalState n Pr M) (w : NetworkState n M)
    (j : Fin n) : process (u, w) j = (u j).process := rfl
@[simp] theorem sent_apply (u : ∀ _ : Fin n, LocalState n Pr M) (w : NetworkState n M) :
    sent (u, w) = w.sent := rfl
@[simp] theorem received_apply (u : ∀ _ : Fin n, LocalState n Pr M) (w : NetworkState n M)
    (i : Fin n) : received (u, w) i = (u i).received := rfl
@[simp] theorem F_apply (u : ∀ _ : Fin n, LocalState n Pr M) (w : NetworkState n M) :
    F (u, w) = w.F := rfl

/-- The initial instance state over the initial local record `p₀`. -/
def initial (n : ℕ) (M : Type) (p₀ : Pr) : InstanceState n Pr M :=
  (fun _ => LocalState.initial n M p₀, NetworkState.initial n M)

@[simp] theorem initial_process (p₀ : Pr) (j : Fin n) :
    (initial n M p₀).process j = p₀ := rfl
@[simp] theorem initial_sent (p₀ : Pr) (j : Fin n) :
    (initial n M p₀).sent j = ∅ := rfl
@[simp] theorem initial_received (p₀ : Pr) (i j : Fin n) :
    (initial n M p₀).received i j = ∅ := rfl
@[simp] theorem initial_F (p₀ : Pr) : (initial n M p₀).F = ∅ := rfl

/-- Update the local record of process `j`. -/
def setProcess (s : InstanceState n Pr M) (j : Fin n) (p : Pr) : InstanceState n Pr M :=
  (Function.update s.1 j ((s.1 j).setProcess p), s.2)

@[simp] theorem setProcess_sent (s : InstanceState n Pr M) (j : Fin n) (p : Pr) :
    (s.setProcess j p).sent = s.sent := rfl
@[simp] theorem setProcess_F (s : InstanceState n Pr M) (j : Fin n) (p : Pr) :
    (s.setProcess j p).F = s.F := rfl

@[simp] theorem setProcess_received (s : InstanceState n Pr M) (j : Fin n) (p : Pr) :
    (s.setProcess j p).received = s.received := by
  funext i
  by_cases hi : i = j
  · subst hi; simp [setProcess, received, LocalState.setProcess]
  · simp [setProcess, received, Function.update_of_ne hi]

@[simp] theorem setProcess_process_self (s : InstanceState n Pr M) (j : Fin n) (p : Pr) :
    (s.setProcess j p).process j = p := by
  simp [setProcess, process, LocalState.setProcess]

theorem setProcess_process_ne (s : InstanceState n Pr M) (j : Fin n) (p : Pr)
    {k : Fin n} (h : k ≠ j) : (s.setProcess j p).process k = s.process k := by
  simp [setProcess, process, Function.update_of_ne h]

/-- The record vector after a record write, as one `ite`. -/
theorem process_setProcess (s : InstanceState n Pr M) (j : Fin n) (p : Pr) (k : Fin n) :
    (s.setProcess j p).process k = if k = j then p else s.process k := by
  by_cases hk : k = j
  · subst hk; simp
  · simp [setProcess_process_ne _ _ _ hk, hk]

/-- Corruption (deviation D1): total, Dirac, the network state's own row — the local states
are corruption-blind. -/
def corrupt (P : Parameters) (id : Fin P.n) (s : InstanceState P.n Pr M) : InstanceState P.n Pr M :=
  (s.1, s.2.corrupt P id)

@[simp] theorem corrupt_process {P : Parameters} (s : InstanceState P.n Pr M) (id : Fin P.n) :
    (s.corrupt P id).process = s.process := rfl
@[simp] theorem corrupt_received {P : Parameters} (s : InstanceState P.n Pr M) (id : Fin P.n) :
    (s.corrupt P id).received = s.received := rfl
@[simp] theorem corrupt_sent {P : Parameters} (s : InstanceState P.n Pr M) (id : Fin P.n) :
    (s.corrupt P id).sent = s.sent := by
  unfold corrupt sent NetworkState.corrupt; split <;> rfl

/-- The corrupted set after a corruption. Not a simp lemma: it introduces an
`ite`. -/
theorem corrupt_F {P : Parameters} (s : InstanceState P.n Pr M) (id : Fin P.n) :
    (s.corrupt P id).F = if id ∉ s.F ∧ s.F.card < P.f then insert id s.F else s.F := by
  unfold corrupt F NetworkState.corrupt
  split_ifs <;> rfl

theorem corrupt_F_subset {P : Parameters} (s : InstanceState P.n Pr M) (id : Fin P.n) :
    s.F ⊆ (s.corrupt P id).F := by
  rw [corrupt_F]
  split
  · exact Finset.subset_insert _ _
  · exact Finset.Subset.refl _

theorem corrupt_card_le {P : Parameters} (s : InstanceState P.n Pr M) (id : Fin P.n)
    (hF : s.F.card ≤ P.f) : (s.corrupt P id).F.card ≤ P.f := by
  rw [corrupt_F]
  split
  · next hc =>
    have h2 := hc.2
    have h3 := Finset.card_insert_le id s.F
    omega
  · exact hF

/-- A set strictly larger than `G` has a member outside `G`. -/
theorem exists_correct_of_card_lt {Q G : Finset (Fin n)} (h : G.card < Q.card) :
    ∃ j ∈ Q, j ∉ G := by
  by_contra hc
  refine absurd (Finset.card_le_card fun j hj => ?_) (not_le.mpr h)
  by_contra hjF
  exact hc ⟨j, hj, hjF⟩

/-- Two `n − f` quorums share an honest member:
`(n−f) + (n−f) − n = n − 2f > f ≥ |F|`. -/
theorem exists_correct_inter {P : Parameters} {F Q Q' : Finset (Fin P.n)}
    (hF : F.card ≤ P.f) (hQ : P.n - P.f ≤ Q.card) (hQ' : P.n - P.f ≤ Q'.card) :
    ∃ q, q ∈ Q ∧ q ∈ Q' ∧ q ∉ F := by
  have hcard := Finset.card_union_add_card_inter Q Q'
  have hun : (Q ∪ Q').card ≤ P.n := by
    refine le_trans (Finset.card_le_univ _) ?_
    simp
  have hf := P.hf
  have hlt : F.card < (Q ∩ Q').card := by
    omega
  obtain ⟨q, hq, hqF⟩ := exists_correct_of_card_lt hlt
  rw [Finset.mem_inter] at hq
  exact ⟨q, hq.1, hq.2, hqF⟩

/-- An `f + 1`-set and an `n − f` quorum intersect: `(f+1) + (n−f) > n`. -/
theorem exists_mem_inter_of_quorum {P : Parameters} {K Q : Finset (Fin P.n)}
    (hK : P.f + 1 ≤ K.card) (hQ : P.n - P.f ≤ Q.card) :
    ∃ q, q ∈ K ∧ q ∈ Q := by
  have hcard := Finset.card_union_add_card_inter K Q
  have hun : (K ∪ Q).card ≤ P.n := by
    refine le_trans (Finset.card_le_univ _) ?_
    simp
  have hf := P.hf
  have hlt : 0 < (K ∩ Q).card := by
    omega
  obtain ⟨q, hq⟩ := Finset.card_pos.mp hlt
  rw [Finset.mem_inter] at hq
  exact ⟨q, hq.1, hq.2⟩

section Counting

variable [DecidableEq M]

/-- The number of distinct senders from which `i` has received `m`. -/
def receivedCount (s : InstanceState n Pr M) (i : Fin n) (m : M) : ℕ :=
  (Finset.univ.filter (fun j => m ∈ s.received i j)).card

/-- The instance's receipt count at `i` is the count on `i`'s own local state. -/
theorem receivedCount_eq_localState (s : InstanceState n Pr M) (i : Fin n) (m : M) :
    s.receivedCount i m = (s.1 i).receivedCount m := rfl

@[simp] theorem setProcess_receivedCount (s : InstanceState n Pr M) (j : Fin n) (p : Pr)
    (i : Fin n) (m : M) : (s.setProcess j p).receivedCount i m = s.receivedCount i m := by
  simp [receivedCount]

@[simp] theorem corrupt_receivedCount {P : Parameters} (s : InstanceState P.n Pr M) (id : Fin P.n)
    (i : Fin P.n) (m : M) :
    (s.corrupt P id).receivedCount i m = s.receivedCount i m := rfl

/-- Process `j` multicasts `m`: the network state records it under `j`. -/
def multicast (s : InstanceState n Pr M) (j : Fin n) (m : M) : InstanceState n Pr M :=
  (s.1, s.2.recordSent j m)

@[simp] theorem multicast_process (s : InstanceState n Pr M) (j : Fin n) (m : M) :
    (s.multicast j m).process = s.process := rfl
@[simp] theorem multicast_received (s : InstanceState n Pr M) (j : Fin n) (m : M) :
    (s.multicast j m).received = s.received := rfl
@[simp] theorem multicast_F (s : InstanceState n Pr M) (j : Fin n) (m : M) :
    (s.multicast j m).F = s.F := rfl
@[simp] theorem multicast_receivedCount (s : InstanceState n Pr M) (j : Fin n) (m : M)
    (i : Fin n) (m' : M) : (s.multicast j m).receivedCount i m' = s.receivedCount i m' := rfl

/-- Membership in a sent set after a multicast. -/
theorem mem_multicast_sent {s : InstanceState n Pr M} {j : Fin n} {m : M} {k : Fin n}
    {m' : M} :
    m' ∈ (s.multicast j m).sent k ↔ (k = j ∧ m' = m) ∨ m' ∈ s.sent k := by
  change m' ∈ (s.2.recordSent j m).sent k ↔ (k = j ∧ m' = m) ∨ m' ∈ s.2.sent k
  exact NetworkState.mem_recordSent

theorem sent_subset_multicast (s : InstanceState n Pr M) (j : Fin n) (m : M) (k : Fin n) :
    s.sent k ⊆ (s.multicast j m).sent k :=
  fun _ h => mem_multicast_sent.mpr (Or.inr h)

/-- The adversary delivers `m` from sender `j` to receiver `i`: the receiver's
local state files it under `j`'s row. -/
def receiveMessage (s : InstanceState n Pr M) (i j : Fin n) (m : M) : InstanceState n Pr M :=
  (Function.update s.1 i ((s.1 i).deliverTo j m), s.2)

@[simp] theorem receiveMessage_sent (s : InstanceState n Pr M) (i j : Fin n) (m : M) :
    (s.receiveMessage i j m).sent = s.sent := rfl
@[simp] theorem receiveMessage_F (s : InstanceState n Pr M) (i j : Fin n) (m : M) :
    (s.receiveMessage i j m).F = s.F := rfl

@[simp] theorem receiveMessage_process (s : InstanceState n Pr M) (i j : Fin n) (m : M) :
    (s.receiveMessage i j m).process = s.process := by
  funext k
  by_cases hk : k = i
  · subst hk; simp [receiveMessage, process, LocalState.deliverTo]
  · simp [receiveMessage, process, Function.update_of_ne hk]

/-- Membership in a delivered set after a delivery. -/
theorem mem_receiveMessage_received {s : InstanceState n Pr M} {i j : Fin n} {m : M}
    {i' j' : Fin n} {m' : M} :
    m' ∈ (s.receiveMessage i j m).received i' j' ↔
      (i' = i ∧ j' = j ∧ m' = m) ∨ m' ∈ s.received i' j' := by
  by_cases hi : i' = i
  · subst hi
    change m' ∈ (Function.update s.1 i' ((s.1 i').deliverTo j m) i').received j' ↔ _
    rw [Function.update_self]
    change m' ∈ Function.update ((s.1 i').received) j (insert m ((s.1 i').received j)) j' ↔ _
    by_cases hj : j' = j
    · subst hj
      rw [Function.update_self, Finset.mem_insert]
      simp [received]
    · rw [Function.update_of_ne hj]
      simp [hj, received]
  · change m' ∈ (Function.update s.1 i ((s.1 i).deliverTo j m) i').received j' ↔ _
    rw [Function.update_of_ne hi]
    simp [hi, received]

/-- Deliveries only grow the receiver counts. -/
theorem receivedCount_le_receiveMessage (s : InstanceState n Pr M) (i j : Fin n) (m : M)
    (i' : Fin n) (m' : M) :
    s.receivedCount i' m' ≤ (s.receiveMessage i j m).receivedCount i' m' := by
  refine Finset.card_le_card fun k hk => ?_
  rw [Finset.mem_filter] at hk ⊢
  exact ⟨hk.1, mem_receiveMessage_received.mpr (Or.inr hk.2)⟩

/-- A receipt count exceeding `|G|` yields a sender outside `G`. -/
theorem exists_sender_notMem {P : Parameters} {s : InstanceState P.n Pr M}
    (G : Finset (Fin P.n)) {i : Fin P.n} {m : M} (h : G.card < s.receivedCount i m) :
    ∃ j, j ∉ G ∧ m ∈ s.received i j := by
  unfold receivedCount at h
  obtain ⟨j, hjQ, hjF⟩ := exists_correct_of_card_lt h
  rw [Finset.mem_filter] at hjQ
  exact ⟨j, hjF, hjQ.2⟩

/-- Two `n − f` receipt quorums (at possibly different receivers) share an
honest sender: `(n−f) + (n−f) − n = n − 2f > f ≥ |F|`. -/
theorem exists_correct_received₂ {P : Parameters} {s : InstanceState P.n Pr M} (hF : s.F.card ≤ P.f)
    {i i' : Fin P.n} {m m' : M}
    (h : P.n - P.f ≤ s.receivedCount i m) (h' : P.n - P.f ≤ s.receivedCount i' m') :
    ∃ j, j ∉ s.F ∧ m ∈ s.received i j ∧ m' ∈ s.received i' j := by
  unfold receivedCount at h h'
  have hcard := Finset.card_union_add_card_inter
    (Finset.univ.filter (fun j => m ∈ s.received i j))
    (Finset.univ.filter (fun j => m' ∈ s.received i' j))
  have hun : ((Finset.univ.filter (fun j => m ∈ s.received i j)) ∪
      (Finset.univ.filter (fun j => m' ∈ s.received i' j))).card ≤ P.n := by
    refine le_trans (Finset.card_le_univ _) ?_
    simp
  have hf := P.hf
  have hlt : s.F.card < ((Finset.univ.filter (fun j => m ∈ s.received i j)) ∩
      (Finset.univ.filter (fun j => m' ∈ s.received i' j))).card := by
        omega
  obtain ⟨j, hj, hjF⟩ := exists_correct_of_card_lt hlt
  rw [Finset.mem_inter, Finset.mem_filter, Finset.mem_filter] at hj
  exact ⟨j, hjF, hj.1.2, hj.2.2⟩

/-- Two `echoQuorum` receipt quorums (at possibly different receivers) share an
honest sender: `2 * echoQuorum − n > f ≥ |F|`. -/
theorem exists_correct_received₂_echoQuorum {P : Parameters} {s : InstanceState P.n Pr M}
    (hF : s.F.card ≤ P.f) {i i' : Fin P.n} {m m' : M}
    (h : P.echoQuorum ≤ s.receivedCount i m) (h' : P.echoQuorum ≤ s.receivedCount i' m') :
    ∃ j, j ∉ s.F ∧ m ∈ s.received i j ∧ m' ∈ s.received i' j := by
  unfold receivedCount at h h'
  have hcard := Finset.card_union_add_card_inter
    (Finset.univ.filter (fun j => m ∈ s.received i j))
    (Finset.univ.filter (fun j => m' ∈ s.received i' j))
  have hun : ((Finset.univ.filter (fun j => m ∈ s.received i j)) ∪
      (Finset.univ.filter (fun j => m' ∈ s.received i' j))).card ≤ P.n := by
    refine le_trans (Finset.card_le_univ _) ?_
    simp
  have hq := P.n_add_f_lt_two_mul_echoQuorum
  have hlt : s.F.card < ((Finset.univ.filter (fun j => m ∈ s.received i j)) ∩
      (Finset.univ.filter (fun j => m' ∈ s.received i' j))).card := by
        omega
  obtain ⟨j, hj, hjF⟩ := exists_correct_of_card_lt hlt
  rw [Finset.mem_inter, Finset.mem_filter, Finset.mem_filter] at hj
  exact ⟨j, hjF, hj.1.2, hj.2.2⟩

end Counting

end InstanceState

end ABA
end PLTS
