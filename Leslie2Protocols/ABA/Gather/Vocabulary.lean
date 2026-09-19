/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sathiya / Claude
-/

import Leslie2Protocols.ABA.Gather.Spec
import Leslie2Protocols.ABA.Broadcast.Spec

/-!
# The vocabulary of a gather instance

The records a gather instance is written over and the core of its network
state.

A gather instance's plain-multicast messages are the `ECHO` and `VOTE` payload
sets (`GaMsg`); the `BIND` payloads travel by reliable broadcast and are not
messages of the network. `PRec` is the local record of one process: its input,
the `ECHO` and the `VOTE` payload it has multicast, and its return flag.

`coreOf` reads a payload set off the sent sets and the corrupted set of a gather
network state, and nothing else. The incidence lemmas stated beneath it read
that state alone, and are the rows and the columns the counting argument of
`ABA/Gather/Core.lean` sums.
-/

namespace PLTS
namespace ABA
namespace Gather

/-- The plain-multicast messages of one gather instance: the `ECHO` and
`VOTE` payload sets. The `BIND` payloads travel by reliable broadcast and are
not messages of the network. -/
inductive GaMsg (n : ℕ) (X : Type) : Type
  /-- `⟨ECHO, A⟩`. -/
  | echo (A : APSet n X)
  /-- `⟨VOTE, A⟩`. -/
  | vote (A : APSet n X)
  deriving DecidableEq

/-- The local record of one process in one gather instance. The `BIND` field
is the process's own bind-BRB instance's call record, not a field here. -/
structure PRec (n : ℕ) (X : Type) : Type where
  /-- The payload received via `call` (`none` before the call). -/
  input : Option X
  /-- The `ECHO` payload multicast, if any (write-once). -/
  sentEcho : Option (APSet n X)
  /-- The `VOTE` payload multicast, if any (write-once). -/
  sentVote : Option (APSet n X)
  /-- Whether this process has returned. -/
  returned : Bool
  deriving DecidableEq

/-- The initial local record. -/
def PRec.initial (n : ℕ) (X : Type) : PRec n X where
  input := none
  sentEcho := none
  sentVote := none
  returned := false

/-! ### The core of a gather network state

`coreOf` reads a payload set off the sent sets and the corrupted set of a
gather network state, and nothing else (`coreOf_networkState_only`). It is the
`ECHO` payload of a sender whose payload lies below the `VOTE` payloads of
many processes outside `F`. `Gather/Core.lean` is the argument that it has at
least `n − f` entries and lies below every committed `BIND` payload of a
process outside `F`. -/

section Core

variable {n : ℕ} {X : Type} (w : SubState n (PRec n X) (GaMsg n X))

/-- The processes outside the corrupted set. -/
def honest : Finset (Fin n) := Finset.univ \ w.F

open scoped Classical in
/-- `dominatedBy w q` — the senders an `ECHO` payload of which lies below
every `VOTE` payload `q` has multicast. The condition is vacuous for a `q`
that has multicast no `VOTE`, and `dominatedBy w q` is then everything. -/
noncomputable def dominatedBy (q : Fin n) : Finset (Fin n) :=
  Finset.univ.filter
    (fun j => ∀ W : APSet n X, GaMsg.vote W ∈ w.sent q →
      ∃ A, GaMsg.echo A ∈ w.sent j ∧ A ⊆ W)

open scoped Classical in
/-- `dominators w j` — the processes outside the corrupted set that dominate
`j`, that is, whose every `VOTE` payload lies above an `ECHO` payload of
`j`. -/
noncomputable def dominators (j : Fin n) : Finset (Fin n) :=
  (honest w).filter (fun q => j ∈ dominatedBy w q)

open scoped Classical in
/-- The `ECHO` payload `j` has multicast, and `∅` if it has multicast
none. -/
noncomputable def echoOf (j : Fin n) : APSet n X :=
  if h : ∃ A : APSet n X, GaMsg.echo A ∈ w.sent j then h.choose else ∅

open scoped Classical in
/-- **The core of a gather network state**: the `ECHO` payload of a sender
outside the corrupted set with at least `f + 1` dominators, and `∅` if there
is no such sender. -/
noncomputable def coreOf (P : Params) (w : SubState P.n (PRec P.n X) (GaMsg P.n X)) :
    APSet P.n X :=
  if h : ∃ j, j ∈ honest w ∧ P.f + 1 ≤ (dominators w j).card
  then echoOf w h.choose else ∅

end Core

/-- **The core is a function of the network state**: `coreOf` reads the sent
sets and the corrupted set, so a network component holding those computes
it. -/
theorem coreOf_networkState_only {X : Type} {P : Params}
    (w w' : SubState P.n (PRec P.n X) (GaMsg P.n X)) (h : w.2 = w'.2) :
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

variable {n : ℕ} {X : Type} {w : SubState n (PRec n X) (GaMsg n X)}

theorem mem_honest {j : Fin n} : j ∈ honest w ↔ j ∉ w.F := by
  simp [honest]

/-- There are `n − |F|` processes outside `F`. -/
theorem card_honest : (honest w).card = n - w.F.card := by
  have h : honest w = w.Fᶜ := by rw [honest, Finset.compl_eq_univ_sdiff]
  rw [h, Finset.card_compl, Fintype.card_fin]

open scoped Classical in
theorem mem_dominatedBy {q j : Fin n} :
    j ∈ dominatedBy w q ↔ ∀ W : APSet n X, GaMsg.vote W ∈ w.sent q →
      ∃ A, GaMsg.echo A ∈ w.sent j ∧ A ⊆ W := by
  rw [dominatedBy, Finset.mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ _, h⟩⟩

open scoped Classical in
theorem honest_filter_dominatedBy {q : Fin n} :
    (honest w).filter (fun j => j ∈ dominatedBy w q) = dominatedBy w q \ w.F := by
  ext j
  simp only [Finset.mem_filter, Finset.mem_sdiff, mem_honest]
  tauto

open scoped Classical in
/-- The two readings of the incidence agree: summing the rows outside `F`
over the columns outside `F` is summing the columns over the rows. -/
theorem sum_dominatedBy (w : SubState n (PRec n X) (GaMsg n X)) :
    ∑ q ∈ honest w, ((honest w).filter (fun j => j ∈ dominatedBy w q)).card
      = ∑ j ∈ honest w, (dominators w j).card := by
  simp only [dominators, Finset.card_filter]
  exact Finset.sum_comm

end Incidence

end Gather
end ABA
end PLTS
