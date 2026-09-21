/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sathiya / Claude
-/

import Leslie2Protocols.ABA.Gather.Specification
import Leslie2Protocols.ABA.ReliableBroadcast.Specification

/-!
# The vocabulary of a gather instance

The records a gather instance is written over and the core of its network
state.

A gather instance's plain-multicast messages are the `ECHO` and `VOTE` payload
sets (`Message`); the `BIND` payloads travel by reliable broadcast and are not
messages of the network. `BaseProcessRecord` is the local record of one process: its input,
the `ECHO` and the `VOTE` payload it has multicast, the `BIND` payload it has
handed to its own bind broadcast, and its return flag.

`coreOf` reads a payload set off the sent sets and the corrupted set of a gather
network state, and nothing else. The incidence lemmas stated beneath it read
that state alone, and are the rows and the columns the counting argument of
`ABA/Gather/CommonCoreCounting.lean` sums.
-/

namespace PLTS
namespace ABA
namespace Gather

/-- The plain-multicast messages of one gather instance: the `ECHO` and
`VOTE` payload sets. The `BIND` payloads travel by reliable broadcast and are
not messages of the network. -/
inductive Message (n : ℕ) (X : Type) : Type
  /-- `⟨ECHO, A⟩`. -/
  | echo (A : AcceptedPairs n X)
  /-- `⟨VOTE, A⟩`. -/
  | vote (A : AcceptedPairs n X)
  deriving DecidableEq

/-- The local record of one process in one gather instance. The payload handed
to the process's own bind broadcast is a field here; the payloads a bind
broadcast has returned here are fields of `ProcessRecord` (`ABA/Gather/Composition.lean`). -/
structure BaseProcessRecord (n : ℕ) (X : Type) : Type where
  /-- The payload received via `call` (`none` before the call). -/
  input : Option X
  /-- The `ECHO` payload multicast, if any (write-once). -/
  sentEcho : Option (AcceptedPairs n X)
  /-- The `VOTE` payload multicast, if any (write-once). -/
  sentVote : Option (AcceptedPairs n X)
  /-- The `BIND` payload handed to the process's own bind broadcast, if any
  (write-once). -/
  sentBind : Option (AcceptedPairs n X)
  /-- Whether this process has returned. -/
  returned : Bool
  deriving DecidableEq

/-- The initial local record. -/
def BaseProcessRecord.initial (n : ℕ) (X : Type) : BaseProcessRecord n X where
  input := none
  sentEcho := none
  sentVote := none
  sentBind := none
  returned := false

/-! ### The core of a gather network state

`coreOf` reads a payload set off the sent sets and the corrupted set of a
gather network state, and nothing else (`coreOf_networkState_only`). It is the
`ECHO` payload of a sender whose payload lies below the `VOTE` payloads of
many processes outside `F`. `Gather/CommonCoreCounting.lean` is the argument that it has at
least `n − f` entries and lies below every committed `BIND` payload of a
process outside `F`. -/

section Core

variable {n : ℕ} {X : Type} (w : InstanceState n (BaseProcessRecord n X) (Message n X))

/-- The processes outside the corrupted set. -/
def correct : Finset (Fin n) := Finset.univ \ w.F

open scoped Classical in
/-- `dominatedBy w q` — the senders an `ECHO` payload of which lies below
every `VOTE` payload `q` has multicast. The condition is vacuous for a `q`
that has multicast no `VOTE`, and `dominatedBy w q` is then everything. -/
noncomputable def dominatedBy (q : Fin n) : Finset (Fin n) :=
  Finset.univ.filter
    (fun j => ∀ W : AcceptedPairs n X, Message.vote W ∈ w.sent q →
      ∃ A, Message.echo A ∈ w.sent j ∧ A ⊆ W)

open scoped Classical in
/-- `dominators w j` — the processes outside the corrupted set that dominate
`j`, that is, whose every `VOTE` payload lies above an `ECHO` payload of
`j`. -/
noncomputable def dominators (j : Fin n) : Finset (Fin n) :=
  (correct w).filter (fun q => j ∈ dominatedBy w q)

open scoped Classical in
/-- The `ECHO` payload `j` has multicast, and `∅` if it has multicast
none. -/
noncomputable def echoOf (j : Fin n) : AcceptedPairs n X :=
  if h : ∃ A : AcceptedPairs n X, Message.echo A ∈ w.sent j then h.choose else ∅

open scoped Classical in
/-- **The core of a gather network state**: the `ECHO` payload of a sender
outside the corrupted set with at least `f + 1` dominators, and `∅` if there
is no such sender. -/
noncomputable def coreOf (P : Parameters) (w : InstanceState P.n (BaseProcessRecord P.n X) (Message
  P.n X)) :
    AcceptedPairs P.n X :=
  if h : ∃ j, j ∈ correct w ∧ P.f + 1 ≤ (dominators w j).card
  then echoOf w h.choose else ∅

end Core

/-- **The core is a function of the network state**: `coreOf` reads the sent
sets and the corrupted set, so a network component holding those computes
it. -/
theorem coreOf_networkState_only {X : Type} {P : Parameters}
    (w w' : InstanceState P.n (BaseProcessRecord P.n X) (Message P.n X)) (h : w.2 = w'.2) :
    coreOf P w = coreOf P w' := by
  obtain ⟨u, m⟩ := w
  obtain ⟨u', m'⟩ := w'
  cases h
  rfl

/-! ### The incidence on the network state

`dominatedBy` is a relation between senders and processes outside `F`, read as
an incidence: the row of `q` is `dominatedBy w q`, the column of `j` is
`dominators w j`, and `sum_dominatedBy` is the identity between the two
readings of its size. -/

section Incidence

variable {n : ℕ} {X : Type} {w : InstanceState n (BaseProcessRecord n X) (Message n X)}

theorem mem_correct {j : Fin n} : j ∈ correct w ↔ j ∉ w.F := by
  simp [correct]

/-- There are `n − |F|` processes outside `F`. -/
theorem card_correct : (correct w).card = n - w.F.card := by
  have h : correct w = w.Fᶜ := by
    rw [correct, Finset.compl_eq_univ_sdiff]
  rw [h, Finset.card_compl, Fintype.card_fin]

open scoped Classical in
theorem mem_dominatedBy {q j : Fin n} :
    j ∈ dominatedBy w q ↔ ∀ W : AcceptedPairs n X, Message.vote W ∈ w.sent q →
      ∃ A, Message.echo A ∈ w.sent j ∧ A ⊆ W := by
  rw [dominatedBy, Finset.mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ _, h⟩⟩

open scoped Classical in
theorem correct_filter_dominatedBy {q : Fin n} :
    (correct w).filter (fun j => j ∈ dominatedBy w q) = dominatedBy w q \ w.F := by
  ext j
  simp only [Finset.mem_filter, Finset.mem_sdiff, mem_correct]
  tauto

open scoped Classical in
/-- The two readings of the incidence agree: summing the rows outside `F`
over the columns outside `F` is summing the columns over the rows. -/
theorem sum_dominatedBy (w : InstanceState n (BaseProcessRecord n X) (Message n X)) :
    ∑ q ∈ correct w, ((correct w).filter (fun j => j ∈ dominatedBy w q)).card
      = ∑ j ∈ correct w, (dominators w j).card := by
  simp only [dominators, Finset.card_filter]
  exact Finset.sum_comm

end Incidence

end Gather
end ABA
end PLTS
