/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sathiya / Claude
-/

import Leslie2Protocols.ABA.AFW.Flat
import Leslie2Protocols.ABA.AFW.Chain
import Leslie2Protocols.ABA.Gather.Low
import Leslie2Protocols.ABA.Broadcast.ImplSim
import Leslie2Protocols.Framework.FamilySim
import Leslie2Protocols.Framework.WeakRun
import Leslie2Protocols.Framework.Congruence

/-!
# The view of the gather-based protocol in its composed reading

`AFW.protocol P` is the gather-based protocol as it runs and `AFW.composed
P` reads the same protocol as a composition of components, down to the
broadcast instances. This file holds the three things the link between them
rests on: the view that computes a composed state from a flat one, the relation
that view carries, and the builders that assemble a transition of the composed
reading.

## The composed state is a view of the flat one

A state of `composed P` is computed from a state of `protocol P`. The round
loops and the coin oracle are shared objects, the ABA-side network is the
DECIDED sets beside the corrupted set, and the round-`r` state is assembled by
`toRound`. Assembling it undoes the two rearrangements the flat reading
performs. The local states are transposed back: an instance's local state
vector at round `r` is read off the round records the `n` processes hold. And
the sent sets are sliced: an instance's network state carries the messages of
one tag, recovered from the adversary's single tagged sent family by
`AFW.slice`.

## The stores and the return flags

A gather program of the composed reading holds two stores — what each
broadcast instance has returned to it. The flat reading keeps no store: it
reads a receipt quorum on the process's own local state in that instance
(`AFW.apIn1` and its three companions). `AFW.storeIn` (`ABA/AFW/Flat.lean`) is
that reading as a function: the value on which the local state holds a
`2f + 1` `VOTE` receipt quorum, and `none` where there is no such value. Under
the broadcast invariant `BRB.Inv` at most one value carries a quorum
(`storeIn_eq_of_quorum`), so the function agrees with the flat guard wherever
the flat guard fires. The accepted pairs a gather's `ECHO` carries,
`AFW.acceptedIn1` and `AFW.acceptedIn2`, are the accepted pairs of the gather
program the view assembles (`acceptedIn1_gaProcView`, `acceptedIn2_gaProcView`).

The composed broadcast program carries a return flag, which the flat reading
never sets. `brbLocal` supplies it from the store: a process has returned in an
instance exactly when the store holds a value.

## The ghost record is the round's auxiliary state

The round carries three fields no guard of it reads: the core of each of its
two gather instances, and the round's bound bit. On the flat side the adversary
holds those three as the ghost record of the round (`AFW.Ghost`), so the view
reads them off it, and a row's ghost write is the round's write of them
(`toRound_writeGhost`, `toRound_writeGhost_ne`, `toRound_ghostId`). The two
readings of a gather's core agree because each is `Gather.coreOf` of the same
network state (`coreOfNet_toGa1`, `coreOfNet_toGa2`).

## The two clauses that are not readings

`BoundInv` says that a process whose round-`r` second-gather local state
carries an input has passed the round's link, so the round's bound bit is on
record. `StoreInv` says that `BRB.Inv` holds at each of the round's `4n`
broadcast instances, which is what makes the store a function of the flat state
in the sense the flat guards need.
-/

namespace PLTS
namespace ABA
namespace AFW

open Net Comp GSub

/-! ### The four broadcast untaggings

The two gather untaggings and their injectivity are `AFW.unGa1` and `AFW.unGa2`
of `ABA/AFW/Flat.lean`, where the adversary's ghost write reads them. -/

variable {n : ℕ}

/-- The messages of input-broadcast instance `i` of the first gather. -/
def unIn1 (i : Fin n) : Msg n → Option (BRB.BMsg Bool)
  | .brbIn1 i' m => if i' = i then some m else none
  | _ => none

/-- The messages of bind-broadcast instance `i` of the first gather. -/
def unBind1 (i : Fin n) : Msg n → Option (BRB.BMsg (Gather.APSet n Bool))
  | .brbBind1 i' m => if i' = i then some m else none
  | _ => none

/-- The messages of input-broadcast instance `i` of the second gather. -/
def unIn2 (i : Fin n) : Msg n → Option (BRB.BMsg (Option Bool))
  | .brbIn2 i' m => if i' = i then some m else none
  | _ => none

/-- The messages of bind-broadcast instance `i` of the second gather. -/
def unBind2 (i : Fin n) : Msg n → Option (BRB.BMsg (Gather.APSet n (Option Bool)))
  | .brbBind2 i' m => if i' = i then some m else none
  | _ => none

theorem unIn1_inj (i : Fin n) : ∀ a a' (b : BRB.BMsg Bool),
    b ∈ unIn1 i a → b ∈ unIn1 i a' → a = a' := by
  intro a a' b h h'
  cases a <;> cases a' <;> simp_all [unIn1]

theorem unBind1_inj (i : Fin n) : ∀ a a' (b : BRB.BMsg (Gather.APSet n Bool)),
    b ∈ unBind1 i a → b ∈ unBind1 i a' → a = a' := by
  intro a a' b h h'
  cases a <;> cases a' <;> simp_all [unBind1]

theorem unIn2_inj (i : Fin n) : ∀ a a' (b : BRB.BMsg (Option Bool)),
    b ∈ unIn2 i a → b ∈ unIn2 i a' → a = a' := by
  intro a a' b h h'
  cases a <;> cases a' <;> simp_all [unIn2]

theorem unBind2_inj (i : Fin n) : ∀ a a' (b : BRB.BMsg (Gather.APSet n (Option Bool))),
    b ∈ unBind2 i a → b ∈ unBind2 i a' → a = a' := by
  intro a a' b h h'
  cases a <;> cases a' <;> simp_all [unBind2]

/-! ### The store of a broadcast instance -/

variable {X : Type}

/-- The store holds a value exactly when some value has a receipt quorum. -/
theorem storeIn_isSome_iff (P : Params) [DecidableEq X]
    (p : LocalState P.n (BRB.PState X) (BRB.BMsg X)) :
    (storeIn P p).isSome ↔ ∃ v, 2 * P.f + 1 ≤ p.recvCount (BRB.BMsg.vote v) := by
  unfold storeIn
  by_cases h : ∃ v, 2 * P.f + 1 ≤ p.recvCount (BRB.BMsg.vote v)
  · rw [dif_pos h]; exact iff_of_true rfl h
  · rw [dif_neg h]; exact iff_of_false (by simp) h

/-- The value the store holds has a receipt quorum. -/
theorem storeIn_spec (P : Params) [DecidableEq X]
    {p : LocalState P.n (BRB.PState X) (BRB.BMsg X)} {x : X} (h : storeIn P p = some x) :
    2 * P.f + 1 ≤ p.recvCount (BRB.BMsg.vote x) := by
  unfold storeIn at h
  by_cases hq : ∃ v, 2 * P.f + 1 ≤ p.recvCount (BRB.BMsg.vote v)
  · rw [dif_pos hq] at h
    obtain rfl : Classical.choose hq = x := Option.some.inj h
    exact Classical.choose_spec hq
  · rw [dif_neg hq] at h
    exact absurd h (by simp)

/-- **The store holds the value of a receipt quorum.** Under the broadcast
invariant a `VOTE` receipt quorum yields the echo certificate, and at most one
value is certified, so the value the store chooses is the one the quorum
carries. -/
theorem storeIn_eq_of_quorum (P : Params) [DecidableEq X] {k : Fin P.n}
    {s : BRB.ImplState P.n X} (hInv : BRB.Inv P k s) {j : Fin P.n} {x : X}
    (hq : 2 * P.f + 1 ≤ (s.1 j).recvCount (BRB.BMsg.vote x)) :
    storeIn P (s.1 j) = some x := by
  have hex : ∃ v, 2 * P.f + 1 ≤ (s.1 j).recvCount (BRB.BMsg.vote v) := ⟨x, hq⟩
  unfold storeIn
  rw [dif_pos hex]
  refine congrArg some ?_
  have h1 : 2 * P.f + 1 ≤ s.recvCount j (BRB.BMsg.vote (Classical.choose hex)) :=
    Classical.choose_spec hex
  exact BRB.echoCert_unique hInv (BRB.echoCert_of_vote_quorum hInv h1)
    (BRB.echoCert_of_vote_quorum hInv (i := j) (m := x) hq)

/-- The store of an untouched local state is empty: nothing is delivered, and
a receipt quorum is at least one receipt. -/
theorem storeIn_initial (P : Params) [DecidableEq X] :
    storeIn P (LocalState.initial P.n (BRB.BMsg X) (BRB.PState.initial X)) = none := by
  unfold storeIn
  rw [dif_neg]
  rintro ⟨v, hv⟩
  have h0 : (LocalState.initial P.n (BRB.BMsg X) (BRB.PState.initial X)).recvCount
      (BRB.BMsg.vote v) = 0 := by
    simp [LocalState.recvCount]
  rw [h0] at hv
  omega

/-- One process's local state in a broadcast instance, as the composed
broadcast program holds it: the return flag is whether the store holds a
value. -/
noncomputable def brbLocal (P : Params) [DecidableEq X]
    (p : LocalState P.n (BRB.PState X) (BRB.BMsg X)) :
    LocalState P.n (BRB.PState X) (BRB.BMsg X) :=
  { p with proc := { p.proc with returned := (storeIn P p).isSome } }

/-- One process's local state in a gather instance, as the composed gather
program holds it: the gather record extended by the stores of what the
broadcast instances have returned here, over the same delivered sets. -/
noncomputable def gaProcView (P : Params) (X : Type) [DecidableEq X]
    (ga : LocalState P.n (Gather.PRec P.n X) (Gather.GaMsg P.n X))
    (bIn : Fin P.n → LocalState P.n (BRB.PState X) (BRB.BMsg X))
    (bBind : Fin P.n → LocalState P.n (BRB.PState (Gather.APSet P.n X))
      (BRB.BMsg (Gather.APSet P.n X))) :
    LocalState P.n (Gather.ProcRec P.n X) (Gather.GaMsg P.n X) where
  proc :=
    { ga.proc with
      delivIn := fun k => storeIn P (bIn k)
      delivBind := fun q => storeIn P (bBind q) }
  recv := ga.recv

/-- **The first gather's accepted pairs are the accepted pairs of the gather
program the view assembles**: the view supplies that program's input store as
`storeIn` at each of the `n` input-broadcast instances, and `AFW.acceptedIn1`
is the pairs of that same reading. -/
theorem acceptedIn1_gaProcView (P : Params) (s : StageRec P.n) :
    (gaProcView P Bool s.ga1 s.brbIn1 s.brbBind1).proc.accepted = acceptedIn1 P s := by
  ext ⟨k, v⟩
  rw [Gather.ProcRec.mem_accepted, mem_acceptedIn1]
  exact Iff.rfl

/-- The same at the second gather. -/
theorem acceptedIn2_gaProcView (P : Params) (s : StageRec P.n) :
    (gaProcView P (Option Bool) s.ga2 s.brbIn2 s.brbBind2).proc.accepted
      = acceptedIn2 P s := by
  ext ⟨k, v⟩
  rw [Gather.ProcRec.mem_accepted, mem_acceptedIn2]
  exact Iff.rfl

/-! ### The composed round, assembled -/

variable {P : Params}

/-- The round-`r` state of the first gather instance, read off the flat state:
the local state vectors transposed out of the round records the processes hold,
the network states sliced out of the adversary's tagged sent sets, and the
instance's core the first field of the adversary's ghost record. -/
noncomputable def toGa1 (P : Params) (u : ∀ _ : Fin P.n, AFW.ProcRec P.n)
    (w : NetState P.n) (r : ℕ) : Gather.LowState P.n Bool :=
  ((fun i => gaProcView P Bool ((u i).2.stage r).ga1 ((u i).2.stage r).brbIn1
        ((u i).2.stage r).brbBind1,
      ⟨⟨slice unGa1 unGa1_inj (w.sent r), w.F⟩, (w.ghostRec r).1⟩),
    (fun k => (fun i => brbLocal P (((u i).2.stage r).brbIn1 k),
        ⟨slice (unIn1 k) (unIn1_inj k) (w.sent r), w.F⟩),
      fun q => (fun i => brbLocal P (((u i).2.stage r).brbBind1 q),
        ⟨slice (unBind1 q) (unBind1_inj q) (w.sent r), w.F⟩)))

/-- The round-`r` state of the second gather instance, read off the flat state,
its core the second field of the adversary's ghost record. -/
noncomputable def toGa2 (P : Params) (u : ∀ _ : Fin P.n, AFW.ProcRec P.n)
    (w : NetState P.n) (r : ℕ) : Gather.LowState P.n (Option Bool) :=
  ((fun i => gaProcView P (Option Bool) ((u i).2.stage r).ga2 ((u i).2.stage r).brbIn2
        ((u i).2.stage r).brbBind2,
      ⟨⟨slice unGa2 unGa2_inj (w.sent r), w.F⟩, (w.ghostRec r).2.1⟩),
    (fun k => (fun i => brbLocal P (((u i).2.stage r).brbIn2 k),
        ⟨slice (unIn2 k) (unIn2_inj k) (w.sent r), w.F⟩),
      fun q => (fun i => brbLocal P (((u i).2.stage r).brbBind2 q),
        ⟨slice (unBind2 q) (unBind2_inj q) (w.sent r), w.F⟩)))

/-- One process's record in the round, read off its round record: the first
gather's input is the round's input, the second gather's input is the
candidate and marks the second call, the second gather's return flag is the
round's, and no grade is on record. -/
def toProc {n : ℕ} (st : StageRec n) : GBCA.ProcRec n where
  input := st.ga1.proc.input
  cand := st.ga2.proc.input
  called2 := st.ga2.proc.input.isSome
  out := none
  returned := st.ga2.proc.returned

/-- The round-`r` state of the composed reading, read off the flat state: the
process records beside the round's bound bit, and the two gather instances. -/
noncomputable def toRound (P : Params) (u : ∀ _ : Fin P.n, AFW.ProcRec P.n)
    (w : NetState P.n) (r : ℕ) : GBCA.LowPairState P.n :=
  ((fun j => toProc ((u j).2.stage r), (w.ghostRec r).2.2),
    (toGa1 P u w r, toGa2 P u w r))

section Readers

variable (u : ∀ _ : Fin P.n, AFW.ProcRec P.n) (w : NetState P.n) (r : ℕ)

@[simp] theorem procs_toRound (j : Fin P.n) :
    GBCA.procs (toRound P u w r) j = toProc ((u j).2.stage r) := rfl

@[simp] theorem bound_toRound : GBCA.bound (toRound P u w r) = (w.ghostRec r).2.2 := rfl

@[simp] theorem ga1_toRound : GBCA.ga1 (toRound P u w r) = toGa1 P u w r := rfl

@[simp] theorem ga2_toRound : GBCA.ga2 (toRound P u w r) = toGa2 P u w r := rfl

@[simp] theorem core_toGa1 : Gather.core (toGa1 P u w r) = (w.ghostRec r).1 := rfl

@[simp] theorem core_toGa2 : Gather.core (toGa2 P u w r) = (w.ghostRec r).2.1 := rfl

@[simp] theorem ga_toGa1_proc (i : Fin P.n) :
    (Gather.ga (toGa1 P u w r)).1 i
      = gaProcView P Bool ((u i).2.stage r).ga1 ((u i).2.stage r).brbIn1
          ((u i).2.stage r).brbBind1 := rfl

@[simp] theorem ga_toGa2_proc (i : Fin P.n) :
    (Gather.ga (toGa2 P u w r)).1 i
      = gaProcView P (Option Bool) ((u i).2.stage r).ga2 ((u i).2.stage r).brbIn2
          ((u i).2.stage r).brbBind2 := rfl

@[simp] theorem ga_toGa1_net :
    (Gather.ga (toGa1 P u w r)).2 = ⟨slice unGa1 unGa1_inj (w.sent r), w.F⟩ := rfl

@[simp] theorem ga_toGa2_net :
    (Gather.ga (toGa2 P u w r)).2 = ⟨slice unGa2 unGa2_inj (w.sent r), w.F⟩ := rfl

@[simp] theorem brbIn_toGa1 (k : Fin P.n) :
    Gather.brbIn (toGa1 P u w r) k
      = ((fun i => brbLocal P (((u i).2.stage r).brbIn1 k)),
          ⟨slice (unIn1 k) (unIn1_inj k) (w.sent r), w.F⟩) := rfl

@[simp] theorem brbBind_toGa1 (q : Fin P.n) :
    Gather.brbBind (toGa1 P u w r) q
      = ((fun i => brbLocal P (((u i).2.stage r).brbBind1 q)),
          ⟨slice (unBind1 q) (unBind1_inj q) (w.sent r), w.F⟩) := rfl

@[simp] theorem brbIn_toGa2 (k : Fin P.n) :
    Gather.brbIn (toGa2 P u w r) k
      = ((fun i => brbLocal P (((u i).2.stage r).brbIn2 k)),
          ⟨slice (unIn2 k) (unIn2_inj k) (w.sent r), w.F⟩) := rfl

@[simp] theorem brbBind_toGa2 (q : Fin P.n) :
    Gather.brbBind (toGa2 P u w r) q
      = ((fun i => brbLocal P (((u i).2.stage r).brbBind2 q)),
          ⟨slice (unBind2 q) (unBind2_inj q) (w.sent r), w.F⟩) := rfl

/-- The first gather's `ECHO` payload, read through the view: the accepted
pairs of the sender's round record are the accepted pairs the composed gather
program holds. -/
theorem accepted_toGa1 (j : Fin P.n) :
    ((Gather.ga (toGa1 P u w r)).proc j).accepted = acceptedIn1 P ((u j).2.stage r) :=
  acceptedIn1_gaProcView P ((u j).2.stage r)

/-- The same at the second gather. -/
theorem accepted_toGa2 (j : Fin P.n) :
    ((Gather.ga (toGa2 P u w r)).proc j).accepted = acceptedIn2 P ((u j).2.stage r) :=
  acceptedIn2_gaProcView P ((u j).2.stage r)

/-- **The two readings of the first gather's core agree**: the instance's core
is read off its network state alone, and that network state is the one
`AFW.ga1Of` hands the adversary. -/
theorem coreOfNet_toGa1 :
    Gather.coreOfNet P (Gather.ga (toGa1 P u w r)).2 = Gather.coreOf P (ga1Of P w r) :=
  (Gather.coreOf_eq_coreOfNet P (ga1Of P w r)).symm

/-- The same for the second gather's core. -/
theorem coreOfNet_toGa2 :
    Gather.coreOfNet P (Gather.ga (toGa2 P u w r)).2 = Gather.coreOf P (ga2Of P w r) :=
  (Gather.coreOf_eq_coreOfNet P (ga2Of P w r)).symm

end Readers

/-! ### The ghost write, read through the view

The adversary's ghost record of round `r` is the round's two gather cores
beside its bound bit, so a row's ghost write is the round's write of those
three fields. The lemmas below are that write at the round the row's label
names, at every other round, and at a row whose write returns the record it
found. -/

/-- **The ghost write at the round its label names**, read through the view:
the two cores and the bound bit are the written record, every other coordinate
the view before the write. -/
theorem toRound_writeGhost (v : ∀ _ : Fin P.n, AFW.ProcRec P.n) (w : NetState P.n)
    {L : NLabP P.n (Msg P.n)} {r : ℕ} (h : roundOf L = some r) :
    toRound P v (w.writeGhost (ghostStep P) L) r
      = ((fun j => toProc ((v j).2.stage r), (ghostStep P L w (w.ghostRec r)).2.2),
         (Gather.setCore (toGa1 P v w r) (ghostStep P L w (w.ghostRec r)).1,
          Gather.setCore (toGa2 P v w r) (ghostStep P L w (w.ghostRec r)).2.1)) := by
  unfold NetStateP.writeGhost
  rw [h]
  simp [toRound, toGa1, toGa2, Gather.setCore]

/-- The ghost write leaves every other round's view where it stands. -/
theorem toRound_writeGhost_ne (v : ∀ _ : Fin P.n, AFW.ProcRec P.n) (w : NetState P.n)
    {L : NLabP P.n (Msg P.n)} {r r' : ℕ} (h : roundOf L = some r) (hr : r' ≠ r) :
    toRound P v (w.writeGhost (ghostStep P) L) r' = toRound P v w r' := by
  unfold NetStateP.writeGhost
  rw [h]
  simp [toRound, toGa1, toGa2, Function.update_of_ne hr]

/-- A row whose ghost write returns the record it found leaves every round's
view where it stands. -/
theorem toRound_ghostId (L : NLabP P.n (Msg P.n))
    (h : ∀ (v : NetState P.n) (G : Ghost P.n), ghostStep P L v G = G)
    (x : ∀ _ : Fin P.n, AFW.ProcRec P.n) (w : NetState P.n) (r' : ℕ) :
    toRound P x (w.writeGhost (ghostStep P) L) r' = toRound P x w r' := by
  unfold NetStateP.writeGhost
  cases hL : roundOf L with
  | none => rfl
  | some r => simp only [h, Function.update_eq_self]

/-- The ghost write never clears a round's bound bit: `AFW.ghostStep` writes
the third field at the link alone, and writes it `some`. -/
theorem ghostStep_bound (L : NLabP P.n (Msg P.n)) (v : NetState P.n)
    (G : Ghost P.n) (h : G.2.2 ≠ none) : (ghostStep P L v G).2.2 ≠ none := by
  unfold ghostStep
  split <;> simp_all

/-- The bound bit of a round on record stays on record across any row. -/
theorem writeGhost_bound {w : NetState P.n} (L : NLabP P.n (Msg P.n)) {r : ℕ}
    (h : (w.ghostRec r).2.2 ≠ none) :
    ((w.writeGhost (ghostStep P) L).ghostRec r).2.2 ≠ none := by
  unfold NetStateP.writeGhost
  cases hL : roundOf L with
  | none => exact h
  | some r₀ =>
    by_cases hr : r = r₀
    · subst hr; simpa using ghostStep_bound L w _ h
    · simpa [Function.update_of_ne hr] using h

/-- A send, read through the view with its ghost write: the round's two cores
and its bound bit are the record `AFW.ghostStep` writes, and every other
coordinate is the send's own. -/
theorem toRound_gsndGhost (v : ∀ _ : Fin P.n, AFW.ProcRec P.n) (w : NetState P.n)
    (r : ℕ) (j : Fin P.n) (m : Msg P.n) :
    toRound P v ((w.gsent r j m).writeGhost (ghostStep P) (Sum.inr (.gsnd r j m))) r
      = ((fun i => toProc ((v i).2.stage r),
            (ghostStep P (Sum.inr (.gsnd r j m)) (w.gsent r j m) (w.ghostRec r)).2.2),
         (Gather.setCore (toGa1 P v (w.gsent r j m) r)
            (ghostStep P (Sum.inr (.gsnd r j m)) (w.gsent r j m) (w.ghostRec r)).1,
          Gather.setCore (toGa2 P v (w.gsent r j m) r)
            (ghostStep P (Sum.inr (.gsnd r j m)) (w.gsent r j m) (w.ghostRec r)).2.1)) :=
  toRound_writeGhost v _ rfl

/-! ### The view at the initial state -/

/-- The gather local state the view assembles from untouched records is the
untouched gather local state: no broadcast instance has returned anything. -/
theorem gaProcView_initial (P : Params) (X : Type) [DecidableEq X] :
    gaProcView P X (LocalState.initial P.n (Gather.GaMsg P.n X) (Gather.PRec.initial P.n X))
        (fun _ => LocalState.initial P.n (BRB.BMsg X) (BRB.PState.initial X))
        (fun _ => LocalState.initial P.n (BRB.BMsg (Gather.APSet P.n X))
          (BRB.PState.initial (Gather.APSet P.n X)))
      = LocalState.initial P.n (Gather.GaMsg P.n X) (Gather.ProcRec.initial P.n X) := by
  simp only [gaProcView, LocalState.initial_proc, storeIn_initial]
  rfl

/-- The broadcast local state the view assembles from an untouched record is
the untouched broadcast local state. -/
theorem brbLocal_initial (P : Params) (X : Type) [DecidableEq X] :
    brbLocal P (LocalState.initial P.n (BRB.BMsg X) (BRB.PState.initial X))
      = LocalState.initial P.n (BRB.BMsg X) (BRB.PState.initial X) := by
  unfold brbLocal
  rw [storeIn_initial]
  rfl

/-- The empty sent family slices to the empty sent family. -/
theorem slice_empty {β : Type} (f : Msg n → Option β)
    (hf : ∀ a a' b, b ∈ f a → b ∈ f a' → a = a') :
    slice f hf (fun _ => (∅ : Finset (Msg n))) = fun _ => (∅ : Finset β) := by
  funext q
  simp [slice]

/-- **Every round of the view is the composed round's initial state**: an
untouched round reads as the initial record on the flat side, and the empty
sent slices to the empty sent. -/
theorem toRound_init (P : Params) (r : ℕ) :
    toRound P (protocol P).init.1 (protocol P).init.2.1 r = (GBCA.lowPairInst P r).init := by
  have hproc : (protocol P).init.1
      = fun _ => (CoreRec.initial P.n, StageSideRecP.initial (StageRec P.n)) := rfl
  have hsent : ((protocol P).init.2.1).sent = fun _ _ => (∅ : Finset (Msg P.n)) := rfl
  have hF : ((protocol P).init.2.1).F = (∅ : Finset (Fin P.n)) := rfl
  have hghost : ((protocol P).init.2.1).ghostRec
      = fun _ => ((none, none, none) : Ghost P.n) := rfl
  rw [GBCA.lowPairInst_init, toRound, toGa1, toGa2, hproc, hsent, hF, hghost]
  simp [Gather.lowInst_init, GBCA.ProcRec.initial, toProc, StageRec.initial,
    Gather.GaNetState.initial, NetworkState.initial, BRB.ImplState.initial,
    SubState.initial, slice_empty, gaProcView_initial, brbLocal_initial]
  rfl

/-! ### The relation -/

/-- **The round's bound bit is on record wherever its second gather has been
called**: a process whose round-`r` second-gather local state carries an input
has passed the round's link, and the link writes the bound bit. This is what
the graded return's announced bit rests on, and it is one of the two clauses of
the relation that are not readings of the flat state. -/
def BoundInv (P : Params) (u : ∀ _ : Fin P.n, AFW.ProcRec P.n)
    (w : NetState P.n) : Prop :=
  ∀ (r : ℕ) (i : Fin P.n), (((u i).2.stage r).ga2.proc).input ≠ none →
    (w.ghostRec r).2.2 ≠ none

/-- **The broadcast invariant holds at every instance the view assembles.** It
is what identifies the store with the value a flat receipt quorum carries
(`storeIn_eq_of_quorum`), and it is the second clause of the relation that is
not a reading of the flat state. -/
def StoreInv (P : Params) (u : ∀ _ : Fin P.n, AFW.ProcRec P.n)
    (w : NetState P.n) : Prop :=
  ∀ (r : ℕ) (k : Fin P.n),
    BRB.Inv P k (Gather.brbIn (GBCA.ga1 (toRound P u w r)) k) ∧
      BRB.Inv P k (Gather.brbBind (GBCA.ga1 (toRound P u w r)) k) ∧
      BRB.Inv P k (Gather.brbIn (GBCA.ga2 (toRound P u w r)) k) ∧
      BRB.Inv P k (Gather.brbBind (GBCA.ga2 (toRound P u w r)) k)

/-- **The composition relation**: the round loops and the coin oracle are
shared, the ABA-side network is the DECIDED sets beside the corrupted set,
every round's state is the view `toRound` of the flat state, the bound bit of a
called round is on record, and the broadcast invariant holds at every instance.
The first four conjuncts are unguarded, so they determine the composed state
from the flat one. -/
def ProtocolRel (P : Params) (s : ProtocolState P) (t : ComposedState P) : Prop :=
  (∀ j, (s.1 j).1 = t.2.1 j) ∧
    s.2.2 = t.2.2.2 ∧
    t.2.2.1 = ⟨s.2.1.dsent, s.2.1.F⟩ ∧
    t.1 = (fun r => toRound P s.1 s.2.1 r) ∧
    BoundInv P s.1 s.2.1 ∧
    StoreInv P s.1 s.2.1

theorem protocolRel_mk (P : Params) (u : ∀ _ : Fin P.n, AFW.ProcRec P.n)
    (w : NetState P.n) (o : ℕ → WCC.SpecState P.n) (G : ℕ → GBCA.LowPairState P.n)
    (C : ∀ _ : Fin P.n, CoreRec P.n) (A : ANetState P.n)
    (o' : ℕ → WCC.SpecState P.n) :
    ProtocolRel P (u, w, o) (G, C, A, o') ↔
      ((∀ j, (u j).1 = C j) ∧ o = o' ∧ A = ⟨w.dsent, w.F⟩ ∧
        (G = fun r => toRound P u w r) ∧ BoundInv P u w ∧ StoreInv P u w) := Iff.rfl

/-- The bound invariant survives a row that leaves every process's
second-gather local input where it stands and keeps on record every bound bit
already there. -/
theorem boundInv_of {u x : ∀ _ : Fin P.n, AFW.ProcRec P.n} {w v : NetState P.n}
    (hI : BoundInv P u w)
    (hx : ∀ i r, (((x i).2.stage r).ga2.proc).input
      = (((u i).2.stage r).ga2.proc).input)
    (hv : ∀ r, (w.ghostRec r).2.2 ≠ none → (v.ghostRec r).2.2 ≠ none) :
    BoundInv P x v :=
  fun r i hne => hv r (hI r i (by rw [← hx i r]; exact hne))

/-- The initial states are related: every round of the view is the composed
round's initial state, and the broadcast invariant holds at every instance
there. -/
theorem protocolRel_init (P : Params) :
    ProtocolRel P (protocol P).init (composed P).init := by
  refine ⟨fun _ => rfl, rfl, rfl, ?_, fun _ _ h => absurd rfl h, ?_⟩
  · funext r
    exact (toRound_init P r).symm
  · intro r k
    rw [ga1_toRound, ga2_toRound]
    have h1 : toGa1 P (protocol P).init.1 (protocol P).init.2.1 r
        = (Gather.lowInst P Bool).init := congrArg (fun q => GBCA.ga1 q) (toRound_init P r)
    have h2 : toGa2 P (protocol P).init.1 (protocol P).init.2.1 r
        = (Gather.lowInst P (Option Bool)).init := congrArg (fun q => GBCA.ga2 q) (toRound_init P r)
    rw [h1, h2]
    exact ⟨BRB.Inv.initial, BRB.Inv.initial, BRB.Inv.initial, BRB.Inv.initial⟩


/-! ### Building a transition of the composed reading

The composed reading's pipeline, read once so that every row of the link can be
assembled from its components' rows: the family of rounds beside the round
loops, the ABA-side network and the lifted oracle. -/

/-- The four components of the gather-based composed reading, side by side. -/
noncomputable def composedPre (P : Params) :
    System (ComposedState P) (NLab P.n) :=
  (lowSide P).parallel
    ((System.syncProduct (coreProcN P)).parallel
      ((aNet P).parallel (wccLift P)))

/-- The composed group: the rendezvous alphabet hidden, read back over
`Lab n`. -/
noncomputable def composedGroup (P : Params) :
    System (ComposedState P) (Lab P.n) :=
  ((composedPre P).abstract (netEvtLabels P.n)).relabel

theorem composed_eq (P : Params) :
    composed P = (composedGroup P).abstract (Lab.hiddenAPI P.n) := rfl

/-- The round-`r` state moves on a label it owns. -/
theorem lowSide_owned (P : Params) (G : ℕ → GBCA.LowPairState P.n) (r : ℕ)
    {L : NLab P.n} (hL : gOwns L = some r) {q : GBCA.LowPairState P.n}
    (h : (GBCA.lowPairInst P r).step (G r) L (PMF.pure q)) :
    (lowSide P).step G L (PMF.pure (Function.update G r q)) := by
  rw [lowSide, System.family_step_iff]
  exact Or.inr (Or.inl ⟨r, hL, PMF.pure q, h, by rw [PMF.pure_map]⟩)

/-- An owned label whose round stands still. -/
theorem lowSide_owned_id (P : Params) (G : ℕ → GBCA.LowPairState P.n) (r : ℕ)
    {L : NLab P.n} (hL : gOwns L = some r)
    (h : (GBCA.lowPairInst P r).step (G r) L (PMF.pure (G r))) :
    (lowSide P).step G L (PMF.pure G) := by
  have hstep := lowSide_owned P G r hL h
  rwa [Function.update_eq_self] at hstep

/-- The round-`r` state takes one of its own silent rules. -/
theorem lowSide_tau (P : Params) (G : ℕ → GBCA.LowPairState P.n) (r : ℕ)
    {q : GBCA.LowPairState P.n}
    (h : (GBCA.lowPairInst P r).step (G r) (Sum.inl Lab.tau) (PMF.pure q)) :
    (lowSide P).step G (Sum.inl Lab.tau) (PMF.pure (Function.update G r q)) := by
  rw [lowSide, System.family_step_iff]
  exact Or.inl ⟨rfl, r, PMF.pure q, h, by rw [PMF.pure_map]⟩

/-- A label no round owns and no broadcast: the family idles. -/
theorem lowSide_idle (P : Params) (G : ℕ → GBCA.LowPairState P.n) {L : NLab P.n}
    (hτ : L ≠ Silent.τ) (hown : gOwns L = none) (hf : ¬ isFailN L) :
    (lowSide P).step G L (PMF.pure G) := by
  rw [lowSide, System.family_step_iff]
  exact Or.inr (Or.inr (Or.inr ⟨hτ, hown, hf, rfl⟩))

/-- Corruption is broadcast to every round's coordinate. -/
theorem lowSide_fail (P : Params) (G : ℕ → GBCA.LowPairState P.n) (k : Fin P.n) :
    (lowSide P).step G (Sum.inl (Lab.fail k))
      (PMF.pure (fun r => gActLow P (Sum.inl (Lab.fail k)) (G r))) := by
  rw [lowSide, System.family_step_iff]
  exact Or.inr (Or.inr (Or.inl ⟨by simp, rfl, trivial, rfl⟩))

/-- The three components beside the graded-agreement side move together on a
visible label, the oracle's successor left free. -/
theorem contextStep (P : Params) {C C' : ∀ _ : Fin P.n, CoreRec P.n}
    {A A' : ANetState P.n} {o : ℕ → WCC.SpecState P.n}
    {ν : PMF (ℕ → WCC.SpecState P.n)} {L : NLab P.n} (hL : L ≠ Silent.τ)
    (hC : ∀ i, CoreProcStepN P i (C i) L (PMF.pure (C' i)))
    (hA : ANetStep P A L (PMF.pure A'))
    (hW : (wccLift P).step o L ν) :
    ((System.syncProduct (coreProcN P)).parallel ((aNet P).parallel (wccLift P))).step
      (C, A, o) L (prodPMF (PMF.pure C') (prodPMF (PMF.pure A') ν)) := by
  rw [System.parallel_step]
  refine Or.inl ⟨hL, PMF.pure C', prodPMF (PMF.pure A') ν, syncCore_pure hL hC, ?_, rfl⟩
  rw [System.parallel_step]
  exact Or.inl ⟨hL, PMF.pure A', ν, hA, hW, rfl⟩

/-- Build a joint transition of the four components on a visible label, the
oracle's successor left free. -/
theorem composedPre_vis_step (P : Params) {G G' : ℕ → GBCA.LowPairState P.n}
    {C C' : ∀ _ : Fin P.n, CoreRec P.n} {A A' : ANetState P.n}
    {o : ℕ → WCC.SpecState P.n} {ν : PMF (ℕ → WCC.SpecState P.n)} {L : NLab P.n}
    (hL : L ≠ Silent.τ)
    (hG : (lowSide P).step G L (PMF.pure G'))
    (hC : ∀ i, CoreProcStepN P i (C i) L (PMF.pure (C' i)))
    (hA : ANetStep P A L (PMF.pure A'))
    (hW : (wccLift P).step o L ν) :
    (composedPre P).step (G, C, A, o) L
      (prodPMF (PMF.pure G') (prodPMF (PMF.pure C') (prodPMF (PMF.pure A') ν))) := by
  rw [composedPre, System.parallel_step]
  exact Or.inl ⟨hL, PMF.pure G', prodPMF (PMF.pure C') (prodPMF (PMF.pure A') ν),
    hG, contextStep P hL hC hA hW, rfl⟩

/-- Build a silent transition of the four components from a round's own. -/
theorem composedPre_tau_low (P : Params) {G G' : ℕ → GBCA.LowPairState P.n}
    {C : ∀ _ : Fin P.n, CoreRec P.n} {A : ANetState P.n}
    {o : ℕ → WCC.SpecState P.n}
    (hG : (lowSide P).step G (Sum.inl Lab.tau) (PMF.pure G')) :
    (composedPre P).step (G, C, A, o) (Sum.inl Lab.tau) (PMF.pure (G', C, A, o)) := by
  rw [composedPre, System.parallel_step]
  refine Or.inr (Or.inl ⟨rfl, PMF.pure G', hG, ?_⟩)
  rw [prodPMF_pure_pure]

/-- Build a silent transition of the four components from an ABA-side network
injection. -/
theorem composedPre_tau_aNet (P : Params) {G : ℕ → GBCA.LowPairState P.n}
    {C : ∀ _ : Fin P.n, CoreRec P.n} {A A' : ANetState P.n}
    {o : ℕ → WCC.SpecState P.n}
    (hA : ANetStep P A (Sum.inl Lab.tau) (PMF.pure A')) :
    (composedPre P).step (G, C, A, o) (Sum.inl Lab.tau) (PMF.pure (G, C, A', o)) := by
  rw [composedPre, System.parallel_step]
  refine Or.inr (Or.inr ⟨rfl,
    prodPMF (PMF.pure C) (prodPMF (PMF.pure A') (PMF.pure o)), ?_, ?_⟩)
  · rw [System.parallel_step]
    refine Or.inr (Or.inr ⟨rfl, prodPMF (PMF.pure A') (PMF.pure o), ?_, rfl⟩)
    rw [System.parallel_step]
    exact Or.inr (Or.inl ⟨rfl, PMF.pure A', hA, rfl⟩)
  · rw [prodPMF_pure_pure, prodPMF_pure_pure, prodPMF_pure_pure]

/-! ### The two hiding frames -/

theorem composedGroup_step_iff (P : Params) (q : ComposedState P) (l : Lab P.n)
    (μ : PMF (ComposedState P)) :
    (composedGroup P).step q l μ ↔
      (l = .tau ∧ ∃ e : NetEvt P.n, (composedPre P).step q (Sum.inr e) μ) ∨
      (composedPre P).step q (Sum.inl l) μ := by
  constructor
  · rintro (⟨hτ, l', ⟨e, rfl⟩, hstep⟩ | ⟨-, hstep⟩)
    · exact Or.inl ⟨Sum.inl_injective hτ, e, hstep⟩
    · exact Or.inr hstep
  · rintro (⟨rfl, e, hstep⟩ | hstep)
    · exact Or.inl ⟨rfl, _, inr_mem_netEvtLabels e, hstep⟩
    · exact Or.inr ⟨inl_notMem_netEvtLabels l, hstep⟩

theorem composedGroup_of_event (P : Params) {q : ComposedState P}
    (e : NetEvt P.n) {μ : PMF (ComposedState P)}
    (h : (composedPre P).step q (Sum.inr e) μ) :
    (composedGroup P).step q Lab.tau μ :=
  (composedGroup_step_iff P _ _ _).mpr (Or.inl ⟨rfl, e, h⟩)

theorem composedGroup_of_tau (P : Params) {q : ComposedState P}
    {μ : PMF (ComposedState P)}
    (h : (composedPre P).step q (Sum.inl Lab.tau) μ) :
    (composedGroup P).step q Lab.tau μ :=
  (composedGroup_step_iff P _ _ _).mpr (Or.inr h)

/-! ### Transposing one written record

A row writes the acting process's round record, so the local state vector the
view reads becomes a one-point update of the old one. Each lemma below is that
observation at one component, stated over the `ite` that reading a written
record produces. -/

section Locals

variable {j : Fin n} (Y : Fin n → StageRec n) (sr : StageRec n)

theorem locals_ga1_if :
    (fun i => (if i = j then sr else Y i).ga1)
      = Function.update (fun i => (Y i).ga1) j sr.ga1 := by
  funext i
  rw [Function.update_apply]
  by_cases hi : i = j <;> simp [hi]

theorem locals_ga2_if :
    (fun i => (if i = j then sr else Y i).ga2)
      = Function.update (fun i => (Y i).ga2) j sr.ga2 := by
  funext i
  rw [Function.update_apply]
  by_cases hi : i = j <;> simp [hi]

theorem locals_brbIn1_if (k : Fin n) :
    (fun i => (if i = j then sr else Y i).brbIn1 k)
      = Function.update (fun i => (Y i).brbIn1 k) j (sr.brbIn1 k) := by
  funext i
  rw [Function.update_apply]
  by_cases hi : i = j <;> simp [hi]

theorem locals_brbBind1_if (k : Fin n) :
    (fun i => (if i = j then sr else Y i).brbBind1 k)
      = Function.update (fun i => (Y i).brbBind1 k) j (sr.brbBind1 k) := by
  funext i
  rw [Function.update_apply]
  by_cases hi : i = j <;> simp [hi]

theorem locals_brbIn2_if (k : Fin n) :
    (fun i => (if i = j then sr else Y i).brbIn2 k)
      = Function.update (fun i => (Y i).brbIn2 k) j (sr.brbIn2 k) := by
  funext i
  rw [Function.update_apply]
  by_cases hi : i = j <;> simp [hi]

theorem locals_brbBind2_if (k : Fin n) :
    (fun i => (if i = j then sr else Y i).brbBind2 k)
      = Function.update (fun i => (Y i).brbBind2 k) j (sr.brbBind2 k) := by
  funext i
  rw [Function.update_apply]
  by_cases hi : i = j <;> simp [hi]

end Locals

/-! ### Runs of the graded-agreement side

Three rows of the flat reading are answered by two transitions of the composed
reading: the link by the hidden events `ret1` and `call2`, the graded return by
the hidden event `ret2` and the visible `retG`, and a delivery completing a
receipt quorum by the hidden events `dlv` and `inRet` (or `bindRet`). The
builders below carry a run of one round to the graded-agreement side, and a run
of that side to the composed group. -/

/-- A silent run of one round is a silent run of the graded-agreement side at
that coordinate. -/
theorem lowSide_silentRun (P : Params) {G : ℕ → GBCA.LowPairState P.n} {r : ℕ}
    {q : GBCA.LowPairState P.n} (h : (GBCA.lowPairInst P r).weakLSilent (G r) q) :
    (lowSide P).weakLSilent G (Function.update G r q) := by
  rw [lowSide]
  exact System.weakLSilent_family gOwns isFailN (gActLow P) h

/-- A run of one round on a label that round owns is a weak transition of the
graded-agreement side at that coordinate. -/
theorem lowSide_weakStep (P : Params) {G : ℕ → GBCA.LowPairState P.n} {r : ℕ}
    {L : NLab P.n} {q : GBCA.LowPairState P.n} (hL : gOwns L = some r)
    (h : (GBCA.lowPairInst P r).weakLStep (G r) L q) :
    (lowSide P).weakLStep G L (Function.update G r q) := by
  rw [lowSide]
  exact System.weakLStep_family gOwns isFailN (gActLow P) hL h

/-- **A silent run of the graded-agreement side is a silent weak transition of
the composed group**: the three other components stand at their states
throughout. -/
theorem composedGroup_weakTau (P : Params) {G G' : ℕ → GBCA.LowPairState P.n}
    (C : ∀ _ : Fin P.n, CoreRec P.n) (A : ANetState P.n)
    (o : ℕ → WCC.SpecState P.n) (h : (lowSide P).weakLSilent G G') :
    weakTau (composedGroup P) (PMF.pure ((G, C, A, o) : ComposedState P))
      (PMF.pure ((G', C, A, o) : ComposedState P)) := by
  have h1 : weakTau (lowSide P) (PMF.pure G) (PMF.pure G') :=
    weakTau_of_weakLSilent (lowSide P) (lowSide_isLTS P) h
  have h2 := weakTau_parallel_left (lowSide P)
    ((System.syncProduct (coreProcN P)).parallel ((aNet P).parallel (wccLift P)))
    ((C, A, o)) h1
  rw [prodPMF_pure_pure, prodPMF_pure_pure] at h2
  exact weakTau_relabel (weakTau_abstract (composedPre P) (netEvtLabels P.n) h2)

/-- **A visible label the graded-agreement side answers by a run** and the three
other components by one transition each is a weak transition of the composed
group. The oracle's successor is left free, so the resulting distribution has
the shape a probabilistic answer consumes. -/
theorem composedGroup_weakStep (P : Params) {G G' : ℕ → GBCA.LowPairState P.n}
    {C C' : ∀ _ : Fin P.n, CoreRec P.n} {A A' : ANetState P.n}
    {o : ℕ → WCC.SpecState P.n} {ν : PMF (ℕ → WCC.SpecState P.n)} {l : Lab P.n}
    (hl : l ≠ Lab.tau)
    (hG : (lowSide P).weakLStep G (Sum.inl l) G')
    (hC : ∀ i, CoreProcStepN P i (C i) (Sum.inl l) (PMF.pure (C' i)))
    (hA : ANetStep P A (Sum.inl l) (PMF.pure A'))
    (hW : (wccLift P).step o (Sum.inl l) ν) :
    weakStep (composedGroup P) (PMF.pure ((G, C, A, o) : ComposedState P)) l
      (prodPMF (PMF.pure G') (prodPMF (PMF.pure C') (prodPMF (PMF.pure A') ν))) := by
  have hL : (Sum.inl l : NLab P.n) ≠ Silent.τ := by
    rw [nlab_tau]
    simpa using hl
  have h1 : weakStep (lowSide P) (PMF.pure G) (Sum.inl l) (PMF.pure G') :=
    weakStep_of_weakLStep (lowSide P) (lowSide_isLTS P) hL hG
  have h2 := weakStep_parallel_sync (lowSide P)
    ((System.syncProduct (coreProcN P)).parallel ((aNet P).parallel (wccLift P)))
    hL h1 (contextStep P hL hC hA hW)
  rw [prodPMF_pure_pure] at h2
  exact weakStep_relabel
    (weakStep_abstract (composedPre P) (netEvtLabels P.n) (by simp) h2)

end AFW

end ABA
end PLTS
