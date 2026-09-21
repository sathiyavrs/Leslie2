/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sathiya / Claude
-/

import Leslie2Protocols.ABA.Gather.Composition
import Leslie2Protocols.ABA.GBCA.AFW.Counting
import Leslie2Protocols.ABA.Composition.GBCAInstanceByABDY
import Leslie2Protocols.Framework.Relabel
import Leslie2Protocols.Framework.SynchronisedProduct
import Leslie2Protocols.Framework.LoopsAndInstanceFamilies

/-!
# The graded-agreement round, composed

The round-`r` graded-agreement round over two gather instances, taken apart
into the pieces that run it: `n` graded-agreement programs beside the network
of the graded-agreement layer, in parallel with the two gather instances, each
read along a pullback that names it. The round's own events are hidden, and the
result is read over the family alphabet `NLab n`.

A program holds one process's record of the round — its input, its candidate,
whether it has called the second gather, its graded outcome and its return flag
(`GBCA.ByAFW.ProcRec`). Its guards read that record and nothing else.

The network of the graded-agreement layer exchanges no messages. It holds the
round's bound bit alone, and no program reads it. The `ret1` event writes the
bit from the core the first gather's return carries; every graded return
announces it on its label.

## The two-event link and the two-event return

The first gather's return and the second gather's call are two events, `ret1`
and `call2`, and so are the second gather's return and the round's graded
return, `ret2` and `retG`. A program moves on each of the four: `ret1` records
the candidate `GBCA.cand` of the returned entries, `call2` marks the call,
`ret2` records the grade `GBCA.gradeOf`, `retG` marks the return. What carries
the round from one event to the next is the program's record.

## The alphabet

The round speaks `NLab n` natively, as `GBCA.ByABDY.sub` does. The call loop of the
family alphabet, `gcallLoop r id b`, is the round's loop label, and the three
Byzantine handshake rows of round `r` are labels of the interface. A program is
read along `procPull`, the projection that sends a Byzantine call to a call, a
Byzantine return to a return, and the two call loops to the loop.

The gathers' own call loops sit one level down. `ga1Pull` sends the family's
two call loops to `Gather.Extra.callLoop`, the label of the first gather's loop
row, and the genuine and Byzantine calls to `Gather.Lab.call`. The second
gather is called on the round's own `call2` event, which `ga2Pull` sends to
`Gather.Lab.call`; the second gather's loop label has no label of the family
over it.

A family label outside the round's interface — the ABA API, the coin ports and
the rendezvous of the protocol's own networks — has the image `PLab.outside`,
on which neither a program nor the layer's network has a row. The round has no
transition on such a label, and the family supplies the idle. Corruption is the
exception: it has no image at all, so the layer stands still on it while the
two gather instances move.

The round-internal alphabet is `RLab n = NLab n ⊕ REvt n`. Its three events are
hidden before anything outside sees the round: `roundInstAt` speaks `NLab n`.

## Corruption

`fail id` is a label of the interface. No program and no row of the layer's
network fires on it: the layer stands still and the two gather instances
corrupt in lockstep. In the family of rounds the label is the broadcast act
(`GBCA.ByABDY.isFailN`), applied to every round at once, and `GBCA.ByAFW.corruptAll` is the
transform it applies — the two gather transforms, the programs and the bound
bit untouched.
-/

namespace PLTS
namespace ABA
namespace GBCA.ByAFW

open Implementation Composition

/-! ### The program's record -/

/-- The record of one graded-agreement program: what a process holds between
the events it takes part in. -/
structure ProcRec (n : ℕ) : Type where
  /-- The input the call carried. -/
  input : Option Bool
  /-- The candidate the first gather's return determines. -/
  cand : Option (Option Bool)
  /-- Whether the second gather has been called here. -/
  called2 : Bool
  /-- The graded outcome the second gather's return determines. -/
  out : Option GbcaOut
  /-- Whether the round has returned here. -/
  returned : Bool
  deriving DecidableEq

/-- The initial record: nothing called, nothing determined, nothing
returned. -/
def ProcRec.initial (n : ℕ) : ProcRec n := ⟨none, none, false, none, false⟩

/-! ### The round-internal alphabet

The three events the family alphabet cannot name. They are untagged: the round
is the identity of the instance they belong to, and they are hidden before the
family sees the round at all. -/

/-- The round's own events: the first gather's return, the second gather's
call, and the second gather's return. -/
inductive REvt (n : ℕ) : Type
  /-- The first gather returns the partial map `g` over the core `C` to
  `id`. -/
  | ret1 (id : Fin n) (g : Fin n → Option Bool) (C : Gather.APSet n Bool)
  /-- Process `id` calls the second gather with `x`. -/
  | call2 (id : Fin n) (x : Option Bool)
  /-- The second gather returns the partial map `g` over the core `C` to
  `id`. -/
  | ret2 (id : Fin n) (g : Fin n → Option (Option Bool)) (C : Gather.APSet n (Option Bool))

/-- The round-internal alphabet: the family alphabet plus the three events. Its
silent label is `Sum.inl (Sum.inl τ)`, so every `Sum.inr` label is observable
and hence hideable. -/
abbrev RLab (n : ℕ) : Type := NLab n ⊕ REvt n

/-- The event labels, hidden by the round. -/
def rEvents (n : ℕ) : Set (RLab n) := {l | ∃ e : REvt n, l = Sum.inr e}

@[simp] theorem inl_notMem_rEvents {n : ℕ} (l : NLab n) : Sum.inl l ∉ rEvents n := by
  simp [rEvents]

@[simp] theorem inr_mem_rEvents {n : ℕ} (e : REvt n) : Sum.inr e ∈ rEvents n := ⟨e, rfl⟩

@[simp] theorem rlab_tau (n : ℕ) : (Silent.τ : RLab n) = Sum.inl (Sum.inl Lab.tau) := rfl

/-! ### The program's alphabet -/

/-- The alphabet of one graded-agreement program: the round's two handshake
ports, the loop the family alphabet's call loops stand for, and the round's
three events. -/
inductive PLab (n : ℕ) : Type
  /-- The silent label. -/
  | tau
  /-- The round's call at `id` with input `b`. -/
  | callG (r : ℕ) (id : Fin n) (b : Bool)
  /-- The round's call against an already-called record. -/
  | callLoop (r : ℕ) (id : Fin n) (b : Bool)
  /-- The first gather's return to `id`. -/
  | ret1 (id : Fin n) (g : Fin n → Option Bool) (C : Gather.APSet n Bool)
  /-- Process `id`'s call of the second gather with `x`. -/
  | call2 (id : Fin n) (x : Option Bool)
  /-- The second gather's return to `id`. -/
  | ret2 (id : Fin n) (g : Fin n → Option (Option Bool)) (C : Gather.APSet n (Option Bool))
  /-- The round's return to `id` of the graded outcome `out`, announcing the
  round's bound bit `bnd`. -/
  | retG (r : ℕ) (id : Fin n) (out : GbcaOut) (bnd : Bool)
  /-- The image of every family label outside the round's interface. No row
  fires on it. -/
  | outside

instance {n : ℕ} : Silent (PLab n) := ⟨PLab.tau⟩

@[simp] theorem plab_tau (n : ℕ) : (Silent.τ : PLab n) = PLab.tau := rfl

/-! ### The pullbacks

A program and the layer's network are read along `procPull`, the first gather
along `ga1Pull`, the second along `ga2Pull`. A label with no image at a
component leaves that component standing still. -/

/-- The projection of the round-internal alphabet onto a program's alphabet. It
reads a Byzantine call as a call, a Byzantine return as a return, and the two
call loops as the loop. Corruption has no image and leaves a program standing
still; every other family label outside the round's interface has the image
`PLab.outside`, on which no row fires. -/
def procPull (n : ℕ) : RLab n → Option (PLab n)
  | Sum.inl (Sum.inl .tau) => some .tau
  | Sum.inl (Sum.inl (.callG r id b)) => some (.callG r id b)
  | Sum.inl (Sum.inl (.retG r id out bnd)) => some (.retG r id out bnd)
  | Sum.inl (Sum.inr (.gcallLoop r id b)) => some (.callLoop r id b)
  | Sum.inl (Sum.inr (.byzCallG r k b)) => some (.callG r k b)
  | Sum.inl (Sum.inr (.byzCallGLoop r k b)) => some (.callLoop r k b)
  | Sum.inl (Sum.inr (.byzRetG r k out bnd)) => some (.retG r k out bnd)
  | Sum.inr (.ret1 id g C) => some (.ret1 id g C)
  | Sum.inr (.call2 id x) => some (.call2 id x)
  | Sum.inr (.ret2 id g C) => some (.ret2 id g C)
  | Sum.inl (Sum.inl (.fail _)) => none
  | _ => some .outside

/-- The projection of the round-internal alphabet onto the first gather's
interface alphabet. The round's call is the gather's call, the family's call
loops are the gather's loop, and the `ret1` event is the gather's return. -/
def ga1Pull (n : ℕ) : RLab n → Option (Gather.InstLab n Bool)
  | Sum.inl (Sum.inl .tau) => some (Sum.inl .tau)
  | Sum.inl (Sum.inl (.callG _ id b)) => some (Sum.inl (.call id b))
  | Sum.inl (Sum.inl (.fail id)) => some (Sum.inl (.fail id))
  | Sum.inl (Sum.inr (.gcallLoop _ id b)) => some (Sum.inr (.callLoop id b))
  | Sum.inl (Sum.inr (.byzCallG _ k b)) => some (Sum.inl (.call k b))
  | Sum.inl (Sum.inr (.byzCallGLoop _ k b)) => some (Sum.inr (.callLoop k b))
  | Sum.inr (.ret1 id g C) => some (Sum.inl (.ret id g C))
  | _ => none

/-- The projection of the round-internal alphabet onto the second gather's
interface alphabet. The `call2` event is the gather's call and the `ret2` event
its return. -/
def ga2Pull (n : ℕ) : RLab n → Option (Gather.InstLab n (Option Bool))
  | Sum.inl (Sum.inl .tau) => some (Sum.inl .tau)
  | Sum.inl (Sum.inl (.fail id)) => some (Sum.inl (.fail id))
  | Sum.inr (.call2 id x) => some (Sum.inl (.call id x))
  | Sum.inr (.ret2 id g C) => some (Sum.inl (.ret id g C))
  | _ => none

/-- The silent label projects to the silent label. -/
@[simp] theorem procPull_tau (n : ℕ) :
    procPull n (Silent.τ : RLab n) = some (Silent.τ : PLab n) := rfl

/-- The silent label projects to the silent label. -/
@[simp] theorem ga1Pull_tau (n : ℕ) :
    ga1Pull n (Silent.τ : RLab n) = some (Silent.τ : Gather.InstLab n Bool) := rfl

/-- The silent label projects to the silent label. -/
@[simp] theorem ga2Pull_tau (n : ℕ) :
    ga2Pull n (Silent.τ : RLab n) = some (Silent.τ : Gather.InstLab n (Option Bool)) := rfl

/-- Only the silent label reaches a program's silent label. -/
theorem procPull_eq_tau {n : ℕ} {l : RLab n} (h : procPull n l = some PLab.tau) :
    l = Sum.inl (Sum.inl Lab.tau) := by
  rcases l with (l₀ | e) | e
  · cases l₀ <;> simp_all [procPull]
  · cases e <;> simp_all [procPull]
  · cases e <;> simp_all [procPull]

/-- Only the silent label reaches the first gather's silent label. -/
theorem ga1Pull_eq_tau {n : ℕ} {l : RLab n}
    (h : ga1Pull n l = some (Silent.τ : Gather.InstLab n Bool)) : l = Silent.τ := by
  rcases l with (l₀ | e) | e
  · cases l₀ <;> simp_all [ga1Pull]
  · cases e <;> simp_all [ga1Pull]
  · cases e <;> simp_all [ga1Pull]

/-- Only the silent label reaches the second gather's silent label. -/
theorem ga2Pull_eq_tau {n : ℕ} {l : RLab n}
    (h : ga2Pull n l = some (Silent.τ : Gather.InstLab n (Option Bool))) : l = Silent.τ := by
  rcases l with (l₀ | e) | e
  · cases l₀ <;> simp_all [ga2Pull]
  · cases e <;> simp_all [ga2Pull]
  · cases e <;> simp_all [ga2Pull]

/-! ### The pullbacks, label by label -/

section PullRows

variable {n : ℕ} (r : ℕ) (id k i j : Fin n) (b c bnd : Bool) (x : Option Bool)
  (out : GbcaOut) (m : GBCA.ByABDY.Msg) (g : Fin n → Option Bool)
  (h : Fin n → Option (Option Bool)) (C : Gather.APSet n Bool)
  (D : Gather.APSet n (Option Bool))

@[simp] theorem procPull_callG :
    procPull n (Sum.inl (Sum.inl (.callG r id b))) = some (.callG r id b) := rfl
@[simp] theorem procPull_retG :
    procPull n (Sum.inl (Sum.inl (.retG r id out bnd))) = some (.retG r id out bnd) := rfl
@[simp] theorem procPull_callABA :
    procPull n (Sum.inl (Sum.inl (.callABA id b))) = some .outside := rfl
@[simp] theorem procPull_retABA :
    procPull n (Sum.inl (Sum.inl (.retABA id b))) = some .outside := rfl
@[simp] theorem procPull_callW : procPull n (Sum.inl (Sum.inl (.callW r id))) = some .outside := rfl
@[simp] theorem procPull_retW : procPull n (Sum.inl (Sum.inl (.retW r id b))) = some .outside := rfl
@[simp] theorem procPull_fail : procPull n (Sum.inl (Sum.inl (.fail id))) = none := rfl
@[simp] theorem procPull_gcallLoop :
    procPull n (Sum.inl (Sum.inr (.gcallLoop r id b))) = some (.callLoop r id b) := rfl
@[simp] theorem procPull_byzCallG :
    procPull n (Sum.inl (Sum.inr (.byzCallG r k b))) = some (.callG r k b) := rfl
@[simp] theorem procPull_byzCallGLoop :
    procPull n (Sum.inl (Sum.inr (.byzCallGLoop r k b))) = some (.callLoop r k b) := rfl
@[simp] theorem procPull_byzRetG :
    procPull n (Sum.inl (Sum.inr (.byzRetG r k out bnd))) = some (.retG r k out bnd) := rfl
@[simp] theorem procPull_gsnd :
    procPull n (Sum.inl (Sum.inr (.gsnd r j m))) = some .outside := rfl
@[simp] theorem procPull_gdlv :
    procPull n (Sum.inl (Sum.inr (.gdlv r i j m))) = some .outside := rfl
@[simp] theorem procPull_dsnd : procPull n (Sum.inl (Sum.inr (.dsnd j b))) = some .outside := rfl
@[simp] theorem procPull_ddlv : procPull n (Sum.inl (Sum.inr (.ddlv i j b))) = some .outside := rfl
@[simp] theorem procPull_retWPub :
    procPull n (Sum.inl (Sum.inr (.retWPub r id c b))) = some .outside := rfl
@[simp] theorem procPull_byzCallW :
    procPull n (Sum.inl (Sum.inr (.byzCallW r k))) = some .outside := rfl
@[simp] theorem procPull_byzRetW :
    procPull n (Sum.inl (Sum.inr (.byzRetW r k b))) = some .outside := rfl
@[simp] theorem procPull_ret1 :
    procPull n (Sum.inr (.ret1 id g C)) = some (.ret1 id g C) := rfl
@[simp] theorem procPull_call2 : procPull n (Sum.inr (.call2 id x)) = some (.call2 id x) := rfl
@[simp] theorem procPull_ret2 :
    procPull n (Sum.inr (.ret2 id h D)) = some (.ret2 id h D) := rfl

@[simp] theorem ga1Pull_callG :
    ga1Pull n (Sum.inl (Sum.inl (.callG r id b))) = some (Sum.inl (.call id b)) := rfl
@[simp] theorem ga1Pull_retG :
    ga1Pull n (Sum.inl (Sum.inl (.retG r id out bnd))) = none := rfl
@[simp] theorem ga1Pull_callABA : ga1Pull n (Sum.inl (Sum.inl (.callABA id b))) = none := rfl
@[simp] theorem ga1Pull_retABA : ga1Pull n (Sum.inl (Sum.inl (.retABA id b))) = none := rfl
@[simp] theorem ga1Pull_callW : ga1Pull n (Sum.inl (Sum.inl (.callW r id))) = none := rfl
@[simp] theorem ga1Pull_retW : ga1Pull n (Sum.inl (Sum.inl (.retW r id b))) = none := rfl
@[simp] theorem ga1Pull_fail :
    ga1Pull n (Sum.inl (Sum.inl (.fail id))) = some (Sum.inl (.fail id)) := rfl
@[simp] theorem ga1Pull_gcallLoop :
    ga1Pull n (Sum.inl (Sum.inr (.gcallLoop r id b))) = some (Sum.inr (.callLoop id b)) := rfl
@[simp] theorem ga1Pull_byzCallG :
    ga1Pull n (Sum.inl (Sum.inr (.byzCallG r k b))) = some (Sum.inl (.call k b)) := rfl
@[simp] theorem ga1Pull_byzCallGLoop :
    ga1Pull n (Sum.inl (Sum.inr (.byzCallGLoop r k b))) = some (Sum.inr (.callLoop k b)) := rfl
@[simp] theorem ga1Pull_byzRetG :
    ga1Pull n (Sum.inl (Sum.inr (.byzRetG r k out bnd))) = none := rfl
@[simp] theorem ga1Pull_gsnd : ga1Pull n (Sum.inl (Sum.inr (.gsnd r j m))) = none := rfl
@[simp] theorem ga1Pull_gdlv : ga1Pull n (Sum.inl (Sum.inr (.gdlv r i j m))) = none := rfl
@[simp] theorem ga1Pull_dsnd : ga1Pull n (Sum.inl (Sum.inr (.dsnd j b))) = none := rfl
@[simp] theorem ga1Pull_ddlv : ga1Pull n (Sum.inl (Sum.inr (.ddlv i j b))) = none := rfl
@[simp] theorem ga1Pull_retWPub : ga1Pull n (Sum.inl (Sum.inr (.retWPub r id c b))) = none := rfl
@[simp] theorem ga1Pull_byzCallW : ga1Pull n (Sum.inl (Sum.inr (.byzCallW r k))) = none := rfl
@[simp] theorem ga1Pull_byzRetW : ga1Pull n (Sum.inl (Sum.inr (.byzRetW r k b))) = none := rfl
@[simp] theorem ga1Pull_ret1 :
    ga1Pull n (Sum.inr (.ret1 id g C)) = some (Sum.inl (.ret id g C)) := rfl
@[simp] theorem ga1Pull_call2 : ga1Pull n (Sum.inr (.call2 id x)) = none := rfl
@[simp] theorem ga1Pull_ret2 : ga1Pull n (Sum.inr (.ret2 id h D)) = none := rfl

@[simp] theorem ga2Pull_callG : ga2Pull n (Sum.inl (Sum.inl (.callG r id b))) = none := rfl
@[simp] theorem ga2Pull_retG : ga2Pull n (Sum.inl (Sum.inl (.retG r id out bnd))) = none := rfl
@[simp] theorem ga2Pull_callABA : ga2Pull n (Sum.inl (Sum.inl (.callABA id b))) = none := rfl
@[simp] theorem ga2Pull_retABA : ga2Pull n (Sum.inl (Sum.inl (.retABA id b))) = none := rfl
@[simp] theorem ga2Pull_callW : ga2Pull n (Sum.inl (Sum.inl (.callW r id))) = none := rfl
@[simp] theorem ga2Pull_retW : ga2Pull n (Sum.inl (Sum.inl (.retW r id b))) = none := rfl
@[simp] theorem ga2Pull_fail :
    ga2Pull n (Sum.inl (Sum.inl (.fail id))) = some (Sum.inl (.fail id)) := rfl
@[simp] theorem ga2Pull_gcallLoop : ga2Pull n (Sum.inl (Sum.inr (.gcallLoop r id b))) = none := rfl
@[simp] theorem ga2Pull_byzCallG : ga2Pull n (Sum.inl (Sum.inr (.byzCallG r k b))) = none := rfl
@[simp] theorem ga2Pull_byzCallGLoop :
    ga2Pull n (Sum.inl (Sum.inr (.byzCallGLoop r k b))) = none := rfl
@[simp] theorem ga2Pull_byzRetG :
    ga2Pull n (Sum.inl (Sum.inr (.byzRetG r k out bnd))) = none := rfl
@[simp] theorem ga2Pull_gsnd : ga2Pull n (Sum.inl (Sum.inr (.gsnd r j m))) = none := rfl
@[simp] theorem ga2Pull_gdlv : ga2Pull n (Sum.inl (Sum.inr (.gdlv r i j m))) = none := rfl
@[simp] theorem ga2Pull_dsnd : ga2Pull n (Sum.inl (Sum.inr (.dsnd j b))) = none := rfl
@[simp] theorem ga2Pull_ddlv : ga2Pull n (Sum.inl (Sum.inr (.ddlv i j b))) = none := rfl
@[simp] theorem ga2Pull_retWPub : ga2Pull n (Sum.inl (Sum.inr (.retWPub r id c b))) = none := rfl
@[simp] theorem ga2Pull_byzCallW : ga2Pull n (Sum.inl (Sum.inr (.byzCallW r k))) = none := rfl
@[simp] theorem ga2Pull_byzRetW : ga2Pull n (Sum.inl (Sum.inr (.byzRetW r k b))) = none := rfl
@[simp] theorem ga2Pull_ret1 : ga2Pull n (Sum.inr (.ret1 id g C)) = none := rfl
@[simp] theorem ga2Pull_call2 :
    ga2Pull n (Sum.inr (.call2 id x)) = some (Sum.inl (.call id x)) := rfl
@[simp] theorem ga2Pull_ret2 :
    ga2Pull n (Sum.inr (.ret2 id h D)) = some (Sum.inl (.ret id h D)) := rfl

end PullRows

/-! ### The graded-agreement program

Process `j`'s program in this round. Every guard reads its own record. The
round's four moves are one row each: the call records the input, the first
gather's return records the candidate, the second gather's call marks itself,
the second gather's return records the grade, and the round's return marks the
record returned. No row fires on the silent label. -/

/-- The step relation of the graded-agreement program of process `j` in round
`r`. All transitions are Dirac. -/
inductive ProcStep (P : Params) (r : ℕ) (j : Fin P.n) :
    ProcRec P.n → PLab P.n → PMF (ProcRec P.n) → Prop
  /-- The call arrives: record the input. -/
  | callG (p : ProcRec P.n) (b : Bool) (h : p.input = none) :
      ProcStep P r j p (.callG r j b) (PMF.pure { p with input := some b })
  /-- A call addressed elsewhere: not `j`'s business. -/
  | callGIdle (p : ProcRec P.n) (i : Fin P.n) (b : Bool) (hi : i ≠ j) :
      ProcStep P r j p (.callG r i b) (PMF.pure p)
  /-- The call loop: the record does not move. -/
  | callLoop (p : ProcRec P.n) (b : Bool) :
      ProcStep P r j p (.callLoop r j b) (PMF.pure p)
  /-- A call loop at another process: not `j`'s business. -/
  | callLoopIdle (p : ProcRec P.n) (i : Fin P.n) (b : Bool) (hi : i ≠ j) :
      ProcStep P r j p (.callLoop r i b) (PMF.pure p)
  /-- The first gather returns here: record the candidate of its entries. -/
  | ret1 (p : ProcRec P.n) (g : Fin P.n → Option Bool) (C : Gather.APSet P.n Bool)
      (hin : p.input ≠ none) (hc : p.cand = none) :
      ProcStep P r j p (.ret1 j g C) (PMF.pure { p with cand := some (cand P g) })
  /-- The first gather's return to another process: not `j`'s business. -/
  | ret1Idle (p : ProcRec P.n) (i : Fin P.n) (g : Fin P.n → Option Bool)
      (C : Gather.APSet P.n Bool) (hi : i ≠ j) :
      ProcStep P r j p (.ret1 i g C) (PMF.pure p)
  /-- The second gather is called here with the recorded candidate. -/
  | call2 (p : ProcRec P.n) (x : Option Bool) (hc : p.cand = some x)
      (h2 : p.called2 = false) :
      ProcStep P r j p (.call2 j x) (PMF.pure { p with called2 := true })
  /-- Another process's call of the second gather: not `j`'s business. -/
  | call2Idle (p : ProcRec P.n) (i : Fin P.n) (x : Option Bool) (hi : i ≠ j) :
      ProcStep P r j p (.call2 i x) (PMF.pure p)
  /-- The second gather returns here: record the grade of its entries. -/
  | ret2 (p : ProcRec P.n) (g : Fin P.n → Option (Option Bool))
      (C : Gather.APSet P.n (Option Bool)) (h2 : p.called2 = true) (ho : p.out = none) :
      ProcStep P r j p (.ret2 j g C) (PMF.pure { p with out := some (gradeOf P g) })
  /-- The second gather's return to another process: not `j`'s business. -/
  | ret2Idle (p : ProcRec P.n) (i : Fin P.n) (g : Fin P.n → Option (Option Bool))
      (C : Gather.APSet P.n (Option Bool)) (hi : i ≠ j) :
      ProcStep P r j p (.ret2 i g C) (PMF.pure p)
  /-- The round returns the recorded grade. The return announces the grade and
  the record drops it. The announced bit is the layer's network's to
  determine. -/
  | retG (p : ProcRec P.n) (out : GbcaOut) (bnd : Bool) (ho : p.out = some out)
      (hr : p.returned = false) :
      ProcStep P r j p (.retG r j out bnd)
        (PMF.pure { p with out := none, returned := true })
  /-- A return to another process: not `j`'s business. -/
  | retGIdle (p : ProcRec P.n) (i : Fin P.n) (out : GbcaOut) (bnd : Bool) (hi : i ≠ j) :
      ProcStep P r j p (.retG r i out bnd) (PMF.pure p)

/-! ### The network of the graded-agreement layer

The network adversary of the layer. It exchanges no message and holds the
round's bound bit alone; no program reads it. The `ret1` row writes the bit
from the core the first gather's return carries if it is unwritten, and the
`retG` row determines the bit the label announces. No row fires on the silent
label. -/

/-- The step relation of the layer's network. All transitions are Dirac. -/
inductive NetStep (P : Params) (r : ℕ) :
    Option Bool → PLab P.n → PMF (Option Bool) → Prop
  /-- A call moves nothing. -/
  | callG (w : Option Bool) (id : Fin P.n) (b : Bool) :
      NetStep P r w (.callG r id b) (PMF.pure w)
  /-- A call loop moves nothing. -/
  | callLoop (w : Option Bool) (id : Fin P.n) (b : Bool) :
      NetStep P r w (.callLoop r id b) (PMF.pure w)
  /-- The first gather's return writes the round's bound bit if it is
  unwritten. -/
  | ret1 (w : Option Bool) (id : Fin P.n) (g : Fin P.n → Option Bool)
      (C : Gather.APSet P.n Bool) :
      NetStep P r w (.ret1 id g C) (PMF.pure (some (w.getD (boundOfCore P C))))
  /-- The second gather's call moves nothing. -/
  | call2 (w : Option Bool) (id : Fin P.n) (x : Option Bool) :
      NetStep P r w (.call2 id x) (PMF.pure w)
  /-- The second gather's return moves nothing. -/
  | ret2 (w : Option Bool) (id : Fin P.n) (g : Fin P.n → Option (Option Bool))
      (C : Gather.APSet P.n (Option Bool)) :
      NetStep P r w (.ret2 id g C) (PMF.pure w)
  /-- The round's return announces the bit on record, and moves nothing. -/
  | retG (w : Option Bool) (id : Fin P.n) (out : GbcaOut) :
      NetStep P r w (.retG r id out (w.getD (boundOfCore P ∅))) (PMF.pure w)

/-! ### The layer and the round -/

/-- The graded-agreement program of process `j` in round `r`. -/
noncomputable def gbcaProc (P : Params) (r : ℕ) (j : Fin P.n) :
    System (ProcRec P.n) (PLab P.n) where
  init := ProcRec.initial P.n
  step := ProcStep P r j

@[simp] theorem gbcaProc_init (P : Params) (r : ℕ) (j : Fin P.n) :
    (gbcaProc P r j).init = ProcRec.initial P.n := rfl

@[simp] theorem gbcaProc_step (P : Params) (r : ℕ) (j : Fin P.n) (p : ProcRec P.n)
    (l : PLab P.n) (ν : PMF (ProcRec P.n)) :
    (gbcaProc P r j).step p l ν ↔ ProcStep P r j p l ν := Iff.rfl

/-- The network of the graded-agreement layer of round `r`. -/
noncomputable def gbcaNet (P : Params) (r : ℕ) : System (Option Bool) (PLab P.n) where
  init := none
  step := NetStep P r

@[simp] theorem gbcaNet_init (P : Params) (r : ℕ) : (gbcaNet P r).init = none := rfl

@[simp] theorem gbcaNet_step (P : Params) (r : ℕ) (w : Option Bool) (l : PLab P.n)
    (μ : PMF (Option Bool)) : (gbcaNet P r).step w l μ ↔ NetStep P r w l μ := Iff.rfl

/-- **The graded-agreement layer**: the `n` programs beside the layer's
network, each read along `procPull`. -/
noncomputable def layer (P : Params) (r : ℕ) :
    System ((∀ _ : Fin P.n, ProcRec P.n) × Option Bool) (RLab P.n) :=
  (System.syncProduct (fun j => (gbcaProc P r j).mapIdle (procPull P.n))).parallel
    ((gbcaNet P r).mapIdle (procPull P.n))

@[simp] theorem layer_init (P : Params) (r : ℕ) :
    (layer P r).init = ((fun _ => ProcRec.initial P.n), none) := rfl

/-- The state of the round whose gather instances have states `G₁` and `G₂`. -/
abbrev RoundStateAt (n : ℕ) (G₁ G₂ : Type) : Type :=
  ((∀ _ : Fin n, ProcRec n) × Option Bool) × (G₁ × G₂)

/-- The layer beside the two gather instances, over the round-internal
alphabet. -/
noncomputable def roundPreAt (P : Params) (r : ℕ) {G₁ G₂ : Type}
    (ga1 : System G₁ (Gather.InstLab P.n Bool))
    (ga2 : System G₂ (Gather.InstLab P.n (Option Bool))) :
    System (RoundStateAt P.n G₁ G₂) (RLab P.n) :=
  (layer P r).parallel ((ga1.mapIdle (ga1Pull P.n)).parallel (ga2.mapIdle (ga2Pull P.n)))

/-- **The round-`r` graded-agreement round** over the gather instances `ga1`,
`ga2`: the layer beside the two of them, the round's events hidden, the result
read over the family alphabet. -/
noncomputable def roundInstAt (P : Params) (r : ℕ) {G₁ G₂ : Type}
    (ga1 : System G₁ (Gather.InstLab P.n Bool))
    (ga2 : System G₂ (Gather.InstLab P.n (Option Bool))) :
    System (RoundStateAt P.n G₁ G₂) (NLab P.n) :=
  ((roundPreAt P r ga1 ga2).abstract (rEvents P.n)).relabel

@[simp] theorem roundInstAt_init (P : Params) (r : ℕ) {G₁ G₂ : Type}
    (ga1 : System G₁ (Gather.InstLab P.n Bool))
    (ga2 : System G₂ (Gather.InstLab P.n (Option Bool))) :
    (roundInstAt P r ga1 ga2).init =
      (((fun _ => ProcRec.initial P.n), none), (ga1.init, ga2.init)) := rfl

/-- The state of the round over the gather instances over Bracha's
broadcast. -/
abbrev LowPairState (n : ℕ) : Type :=
  RoundStateAt n (Gather.LowState n Bool) (Gather.LowState n (Option Bool))

/-- The state of the round over the gather instances over the broadcast
specification. -/
abbrev IdealState (n : ℕ) : Type :=
  RoundStateAt n (Gather.IdealState n Bool) (Gather.IdealState n (Option Bool))

/-- The state of the round over the gather specifications. -/
abbrev PairState (n : ℕ) : Type :=
  RoundStateAt n (Gather.SpecState n Bool) (Gather.SpecState n (Option Bool))

/-- **The round over the gather instances over Bracha's broadcast.** -/
noncomputable def lowPairInst (P : Params) (r : ℕ) :
    System (LowPairState P.n) (NLab P.n) :=
  roundInstAt P r (Gather.lowInst P Bool) (Gather.lowInst P (Option Bool))

/-- **The round over the gather instances over the broadcast
specification.** -/
noncomputable def idealInst (P : Params) (r : ℕ) :
    System (IdealState P.n) (NLab P.n) :=
  roundInstAt P r (Gather.idealInst P Bool) (Gather.idealInst P (Option Bool))

/-- **The round over the gather specifications.** -/
noncomputable def pairInst (P : Params) (r : ℕ) :
    System (PairState P.n) (NLab P.n) :=
  roundInstAt P r (Gather.liftedSpec P Bool) (Gather.liftedSpec P (Option Bool))

@[simp] theorem lowPairInst_init (P : Params) (r : ℕ) :
    (lowPairInst P r).init =
      (((fun _ => ProcRec.initial P.n), none),
        ((Gather.lowInst P Bool).init, (Gather.lowInst P (Option Bool)).init)) := rfl

@[simp] theorem idealInst_init (P : Params) (r : ℕ) :
    (idealInst P r).init =
      (((fun _ => ProcRec.initial P.n), none),
        ((Gather.idealInst P Bool).init, (Gather.idealInst P (Option Bool)).init)) := rfl

@[simp] theorem pairInst_init (P : Params) (r : ℕ) :
    (pairInst P r).init =
      (((fun _ => ProcRec.initial P.n), none),
        (Gather.SpecState.initial P.n Bool, Gather.SpecState.initial P.n (Option Bool))) := rfl

/-! ### Views of the round's state

The four components of the round's state, and the four writes that reach one of
them. A row is stated through these, so that a guard reads `procs s id` where a
flat reading reads the program function. -/

section Views

variable {n : ℕ} {G₁ G₂ : Type}

/-- The programs. -/
def procs (s : RoundStateAt n G₁ G₂) : ∀ _ : Fin n, ProcRec n := s.1.1

/-- The round's bound bit. -/
def bound (s : RoundStateAt n G₁ G₂) : Option Bool := s.1.2

/-- The first gather instance. -/
def ga1 (s : RoundStateAt n G₁ G₂) : G₁ := s.2.1

/-- The second gather instance. -/
def ga2 (s : RoundStateAt n G₁ G₂) : G₂ := s.2.2

/-- Overwrite the programs. -/
def setProcs (s : RoundStateAt n G₁ G₂) (u : ∀ _ : Fin n, ProcRec n) :
    RoundStateAt n G₁ G₂ := ((u, s.1.2), s.2)

/-- Overwrite the round's bound bit. -/
def setBound (s : RoundStateAt n G₁ G₂) (v : Option Bool) : RoundStateAt n G₁ G₂ :=
  ((s.1.1, v), s.2)

/-- Overwrite the first gather instance. -/
def setGa1 (s : RoundStateAt n G₁ G₂) (c : G₁) : RoundStateAt n G₁ G₂ := (s.1, (c, s.2.2))

/-- Overwrite the second gather instance. -/
def setGa2 (s : RoundStateAt n G₁ G₂) (d : G₂) : RoundStateAt n G₁ G₂ := (s.1, (s.2.1, d))

@[simp] theorem procs_setProcs (s : RoundStateAt n G₁ G₂) (u : ∀ _ : Fin n, ProcRec n) :
    procs (setProcs s u) = u := rfl
@[simp] theorem bound_setProcs (s : RoundStateAt n G₁ G₂) (u : ∀ _ : Fin n, ProcRec n) :
    bound (setProcs s u) = bound s := rfl
@[simp] theorem ga1_setProcs (s : RoundStateAt n G₁ G₂) (u : ∀ _ : Fin n, ProcRec n) :
    ga1 (setProcs s u) = ga1 s := rfl
@[simp] theorem ga2_setProcs (s : RoundStateAt n G₁ G₂) (u : ∀ _ : Fin n, ProcRec n) :
    ga2 (setProcs s u) = ga2 s := rfl

@[simp] theorem procs_setBound (s : RoundStateAt n G₁ G₂) (v : Option Bool) :
    procs (setBound s v) = procs s := rfl
@[simp] theorem bound_setBound (s : RoundStateAt n G₁ G₂) (v : Option Bool) :
    bound (setBound s v) = v := rfl
@[simp] theorem ga1_setBound (s : RoundStateAt n G₁ G₂) (v : Option Bool) :
    ga1 (setBound s v) = ga1 s := rfl
@[simp] theorem ga2_setBound (s : RoundStateAt n G₁ G₂) (v : Option Bool) :
    ga2 (setBound s v) = ga2 s := rfl

@[simp] theorem procs_setGa1 (s : RoundStateAt n G₁ G₂) (c : G₁) :
    procs (setGa1 s c) = procs s := rfl
@[simp] theorem bound_setGa1 (s : RoundStateAt n G₁ G₂) (c : G₁) :
    bound (setGa1 s c) = bound s := rfl
@[simp] theorem ga1_setGa1 (s : RoundStateAt n G₁ G₂) (c : G₁) : ga1 (setGa1 s c) = c := rfl
@[simp] theorem ga2_setGa1 (s : RoundStateAt n G₁ G₂) (c : G₁) :
    ga2 (setGa1 s c) = ga2 s := rfl

@[simp] theorem procs_setGa2 (s : RoundStateAt n G₁ G₂) (d : G₂) :
    procs (setGa2 s d) = procs s := rfl
@[simp] theorem bound_setGa2 (s : RoundStateAt n G₁ G₂) (d : G₂) :
    bound (setGa2 s d) = bound s := rfl
@[simp] theorem ga1_setGa2 (s : RoundStateAt n G₁ G₂) (d : G₂) :
    ga1 (setGa2 s d) = ga1 s := rfl
@[simp] theorem ga2_setGa2 (s : RoundStateAt n G₁ G₂) (d : G₂) : ga2 (setGa2 s d) = d := rfl

/-- Corruption (deviation D1): the two gather instances corrupted at `id`, the
programs and the round's bound bit untouched. -/
def corruptAll (P : Params) (id : Fin P.n) (cGa1 : Fin P.n → G₁ → G₁)
    (cGa2 : Fin P.n → G₂ → G₂) (s : RoundStateAt P.n G₁ G₂) : RoundStateAt P.n G₁ G₂ :=
  (s.1, (cGa1 id s.2.1, cGa2 id s.2.2))

@[simp] theorem procs_corruptAll (P : Params) (id : Fin P.n) (cGa1 : Fin P.n → G₁ → G₁)
    (cGa2 : Fin P.n → G₂ → G₂) (s : RoundStateAt P.n G₁ G₂) :
    procs (corruptAll P id cGa1 cGa2 s) = procs s := rfl
@[simp] theorem bound_corruptAll (P : Params) (id : Fin P.n) (cGa1 : Fin P.n → G₁ → G₁)
    (cGa2 : Fin P.n → G₂ → G₂) (s : RoundStateAt P.n G₁ G₂) :
    bound (corruptAll P id cGa1 cGa2 s) = bound s := rfl
@[simp] theorem ga1_corruptAll (P : Params) (id : Fin P.n) (cGa1 : Fin P.n → G₁ → G₁)
    (cGa2 : Fin P.n → G₂ → G₂) (s : RoundStateAt P.n G₁ G₂) :
    ga1 (corruptAll P id cGa1 cGa2 s) = cGa1 id (ga1 s) := rfl
@[simp] theorem ga2_corruptAll (P : Params) (id : Fin P.n) (cGa1 : Fin P.n → G₁ → G₁)
    (cGa2 : Fin P.n → G₂ → G₂) (s : RoundStateAt P.n G₁ G₂) :
    ga2 (corruptAll P id cGa1 cGa2 s) = cGa2 id (ga2 s) := rfl

end Views

/-! ### Determinacy

Both rule tables written here are Dirac, so the round is an LTS whenever the
two gather instances are. -/

section Determinacy

variable {P : Params} {r : ℕ}

/-- Every program transition is Dirac. -/
theorem procStep_dirac {j : Fin P.n} {p : ProcRec P.n} {l : PLab P.n}
    {ν : PMF (ProcRec P.n)} (h : ProcStep P r j p l ν) : ∃ p', ν = PMF.pure p' := by
  cases h <;> exact ⟨_, rfl⟩

/-- Every transition of the layer's network is Dirac. -/
theorem netStep_dirac {w : Option Bool} {l : PLab P.n} {μ : PMF (Option Bool)}
    (h : NetStep P r w l μ) : ∃ w', μ = PMF.pure w' := by
  cases h <;> exact ⟨_, rfl⟩

/-- A program is an LTS. -/
theorem gbcaProc_isLTS (P : Params) (r : ℕ) (j : Fin P.n) : (gbcaProc P r j).IsLTS :=
  fun _ _ _ h => procStep_dirac h

/-- The layer's network is an LTS. -/
theorem gbcaNet_isLTS (P : Params) (r : ℕ) : (gbcaNet P r).IsLTS :=
  fun _ _ _ h => netStep_dirac h

/-- The synchronised group of programs is an LTS. -/
theorem syncProc_isLTS (P : Params) (r : ℕ) :
    (System.syncProduct (fun j => (gbcaProc P r j).mapIdle (procPull P.n))).IsLTS :=
  System.syncProduct_isLTS (fun j => System.mapIdle_isLTS _ (gbcaProc_isLTS P r j))

/-- The layer is an LTS. -/
theorem layer_isLTS (P : Params) (r : ℕ) : (layer P r).IsLTS :=
  System.parallel_isLTS (syncProc_isLTS P r)
    (System.mapIdle_isLTS _ (gbcaNet_isLTS P r))

/-- The layer beside the two gather instances is an LTS. -/
theorem roundPreAt_isLTS (P : Params) (r : ℕ) {G₁ G₂ : Type}
    {ga1 : System G₁ (Gather.InstLab P.n Bool)}
    {ga2 : System G₂ (Gather.InstLab P.n (Option Bool))}
    (h1 : ga1.IsLTS) (h2 : ga2.IsLTS) : (roundPreAt P r ga1 ga2).IsLTS :=
  System.parallel_isLTS (layer_isLTS P r)
    (System.parallel_isLTS (System.mapIdle_isLTS _ h1) (System.mapIdle_isLTS _ h2))

/-- The round is an LTS. -/
theorem roundInstAt_isLTS (P : Params) (r : ℕ) {G₁ G₂ : Type}
    {ga1 : System G₁ (Gather.InstLab P.n Bool)}
    {ga2 : System G₂ (Gather.InstLab P.n (Option Bool))}
    (h1 : ga1.IsLTS) (h2 : ga2.IsLTS) : (roundInstAt P r ga1 ga2).IsLTS :=
  System.relabel_isLTS (System.abstract_isLTS (roundPreAt_isLTS P r h1 h2) _)

/-- The round over the gather instances over Bracha's broadcast is an LTS. -/
theorem lowPairInst_isLTS (P : Params) (r : ℕ) : (lowPairInst P r).IsLTS :=
  roundInstAt_isLTS P r (Gather.lowInst_isLTS P) (Gather.lowInst_isLTS P)

/-- The round over the gather instances over the broadcast specification is an
LTS. -/
theorem idealInst_isLTS (P : Params) (r : ℕ) : (idealInst P r).IsLTS :=
  roundInstAt_isLTS P r (Gather.idealInst_isLTS P) (Gather.idealInst_isLTS P)

/-- The round over the gather specifications is an LTS. -/
theorem pairInst_isLTS (P : Params) (r : ℕ) : (pairInst P r).IsLTS :=
  roundInstAt_isLTS P r (Gather.liftedSpec_isLTS P) (Gather.liftedSpec_isLTS P)

/-- No program rule fires on the silent label: a program only ever moves on one
of the round's ports or one of its events. -/
theorem procStep_no_tau {j : Fin P.n} {p : ProcRec P.n} {ν : PMF (ProcRec P.n)}
    (h : ProcStep P r j p (Silent.τ : PLab P.n) ν) : False := by
  rw [plab_tau] at h; cases h

/-- No rule of the layer's network fires on the silent label. -/
theorem netStep_no_tau {w : Option Bool} {μ : PMF (Option Bool)}
    (h : NetStep P r w (Silent.τ : PLab P.n) μ) : False := by
  rw [plab_tau] at h; cases h

/-- No program rule fires on a family label outside the round's interface. -/
theorem procStep_outside {j : Fin P.n} {p : ProcRec P.n} {ν : PMF (ProcRec P.n)}
    (h : ProcStep P r j p PLab.outside ν) : False := by cases h

/-- No rule of the layer's network fires on a family label outside the round's
interface. -/
theorem netStep_outside {w : Option Bool} {μ : PMF (Option Bool)}
    (h : NetStep P r w PLab.outside μ) : False := by cases h

/-- The program group has no silent transition. -/
theorem syncProc_no_tau {u : ∀ _ : Fin P.n, ProcRec P.n}
    {μ : PMF (∀ _ : Fin P.n, ProcRec P.n)}
    (h : (System.syncProduct (fun j => (gbcaProc P r j).mapIdle (procPull P.n))).step u
      (Silent.τ : RLab P.n) μ) : False := by
  rcases h with ⟨hτ, -⟩ | ⟨-, i, μ_i, hstep, -⟩
  · exact hτ rfl
  · exact procStep_no_tau ((System.mapIdle_step_some (procPull_tau P.n) _).mp hstep)

/-- The layer has no silent transition: neither a program nor the layer's
network fires on the silent label. -/
theorem layer_no_tau {u : ∀ _ : Fin P.n, ProcRec P.n} {v : Option Bool}
    {μ : PMF ((∀ _ : Fin P.n, ProcRec P.n) × Option Bool)}
    (h : (layer P r).step (u, v) (Silent.τ : RLab P.n) μ) : False := by
  rw [layer, System.parallel_step] at h
  rcases h with ⟨hτ, -⟩ | ⟨-, μ₁, hs, -⟩ | ⟨-, μ₂, hn, -⟩
  · exact hτ rfl
  · exact syncProc_no_tau hs
  · exact netStep_no_tau ((System.mapIdle_step_some (procPull_tau P.n) _).mp hn)

end Determinacy

/-! ### Reading and building the round's transitions

The pipeline is `relabel ∘ abstract ∘ parallel ∘ (parallel ∘ syncProduct,
mapIdle, mapIdle)`; the lemmas below unfold it once and for all, in both
directions. -/

/-- The round's step relation, unfolded to the hidden-event case and the
family-label case. -/
theorem roundInstAt_step_iff (P : Params) (r : ℕ) {G₁ G₂ : Type}
    (ga1 : System G₁ (Gather.InstLab P.n Bool))
    (ga2 : System G₂ (Gather.InstLab P.n (Option Bool)))
    (s : RoundStateAt P.n G₁ G₂) (l : NLab P.n) (μ : PMF (RoundStateAt P.n G₁ G₂)) :
    (roundInstAt P r ga1 ga2).step s l μ ↔
      (l = Sum.inl Lab.tau ∧ ∃ e : REvt P.n, (roundPreAt P r ga1 ga2).step s (Sum.inr e) μ) ∨
      (roundPreAt P r ga1 ga2).step s (Sum.inl l) μ := by
  constructor
  · rintro (⟨hτ, l', ⟨e, rfl⟩, hstep⟩ | ⟨-, hstep⟩)
    · exact Or.inl ⟨Sum.inl_injective hτ, e, hstep⟩
    · exact Or.inr hstep
  · rintro (⟨rfl, e, hstep⟩ | hstep)
    · exact Or.inl ⟨rfl, _, inr_mem_rEvents e, hstep⟩
    · exact Or.inr ⟨inl_notMem_rEvents l, hstep⟩

/-! ### The layer's transitions

On a label with no image at a program the layer stands still. On a label with
an image every program takes its row at that image and the layer's network
takes its. -/

section Layer

variable {P : Params} {r : ℕ} {u x : ∀ _ : Fin P.n, ProcRec P.n} {v v' : Option Bool}
  {L : RLab P.n}

/-- A label with an image other than the silent one is visible. -/
theorem rlab_ne_tau {lp : PLab P.n} (hlp : procPull P.n L = some lp) (hlpτ : lp ≠ PLab.tau) :
    L ≠ (Silent.τ : RLab P.n) := by
  intro hc
  subst hc
  rw [procPull_tau] at hlp
  exact hlpτ (Option.some.inj hlp).symm

/-- A label with no image at a program is visible. -/
theorem rlab_ne_tau_of_none (hlp : procPull P.n L = none) : L ≠ (Silent.τ : RLab P.n) := by
  intro hc
  subst hc
  rw [procPull_tau] at hlp
  exact Option.some_ne_none _ hlp

/-- A synchronised transition of the program group on a visible label: every
program steps, and the joint distribution is Dirac. -/
theorem syncProc_inv (hL : L ≠ (Silent.τ : RLab P.n))
    {μ : PMF (∀ _ : Fin P.n, ProcRec P.n)}
    (h : (System.syncProduct (fun j => (gbcaProc P r j).mapIdle (procPull P.n))).step u L μ) :
    ∃ x : ∀ _ : Fin P.n, ProcRec P.n, μ = PMF.pure x ∧
      ∀ i, ((gbcaProc P r i).mapIdle (procPull P.n)).step (u i) L (PMF.pure (x i)) :=
  Gather.syncLift_inv (fun i => gbcaProc_isLTS P r i) hL h

/-- **The layer stands still** on a label with no image at a program. -/
theorem layer_idle_inv (hlp : procPull P.n L = none)
    {μ : PMF ((∀ _ : Fin P.n, ProcRec P.n) × Option Bool)}
    (h : (layer P r).step (u, v) L μ) : μ = PMF.pure (u, v) := by
  have hL := rlab_ne_tau_of_none hlp
  rw [layer, System.parallel_step] at h
  rcases h with ⟨-, μ₁, μ₂, hs, hn, rfl⟩ | ⟨hτ, -⟩ | ⟨hτ, -⟩
  · obtain ⟨y, rfl, hall⟩ := syncProc_inv hL hs
    have hy : y = u := funext fun i => Gather.lift_step_none hlp (hall i)
    subst hy
    rw [(System.mapIdle_step_none hlp _).mp hn, prodPMF_pure_pure]
  · exact absurd hτ hL
  · exact absurd hτ hL

/-- **The layer's joint transition.** Every program takes its row at the
label's image and the layer's network takes its. -/
theorem layer_lab_inv {lp : PLab P.n} (hlp : procPull P.n L = some lp) (hlpτ : lp ≠ PLab.tau)
    {μ : PMF ((∀ _ : Fin P.n, ProcRec P.n) × Option Bool)}
    (h : (layer P r).step (u, v) L μ) :
    ∃ (x : ∀ _ : Fin P.n, ProcRec P.n) (v' : Option Bool), μ = PMF.pure (x, v') ∧
      (∀ i, ProcStep P r i (u i) lp (PMF.pure (x i))) ∧ NetStep P r v lp (PMF.pure v') := by
  have hL := rlab_ne_tau hlp hlpτ
  rw [layer, System.parallel_step] at h
  rcases h with ⟨-, μ₁, μ₂, hs, hn, rfl⟩ | ⟨hτ, -⟩ | ⟨hτ, -⟩
  · obtain ⟨y, rfl, hall⟩ := syncProc_inv hL hs
    have hnet : NetStep P r v lp μ₂ := (System.mapIdle_step_some hlp _).mp hn
    obtain ⟨v', rfl⟩ := netStep_dirac hnet
    exact ⟨y, v', prodPMF_pure_pure _ _, fun i => Gather.lift_step_some hlp (hall i), hnet⟩
  · exact absurd hτ hL
  · exact absurd hτ hL

/-- **The layer refuses** a family label outside the round's interface. -/
theorem layer_outside_inv (hlp : procPull P.n L = some PLab.outside)
    {μ : PMF ((∀ _ : Fin P.n, ProcRec P.n) × Option Bool)}
    (h : (layer P r).step (u, v) L μ) : False := by
  obtain ⟨y, w, -, -, hnet⟩ := layer_lab_inv hlp (by simp) h
  exact netStep_outside hnet

/-- The layer's stutter, read off a Dirac successor. -/
theorem layer_idle_pure (hlp : procPull P.n L = none)
    (h : (layer P r).step (u, v) L (PMF.pure (x, v'))) : x = u ∧ v' = v := by
  have he := PMF.pure_injective (layer_idle_inv hlp h)
  rw [Prod.mk.injEq] at he
  exact he

/-- The layer's joint transition, read off a Dirac successor. -/
theorem layer_lab_pure {lp : PLab P.n} (hlp : procPull P.n L = some lp) (hlpτ : lp ≠ PLab.tau)
    (h : (layer P r).step (u, v) L (PMF.pure (x, v'))) :
    (∀ i, ProcStep P r i (u i) lp (PMF.pure (x i))) ∧ NetStep P r v lp (PMF.pure v') := by
  obtain ⟨y, w, hμ, hproc, hnet⟩ := layer_lab_inv hlp hlpτ h
  have he := PMF.pure_injective hμ
  rw [Prod.mk.injEq] at he
  obtain ⟨rfl, rfl⟩ := he
  exact ⟨hproc, hnet⟩

/-- Build the layer's stutter on a label with no image at a program. -/
theorem layer_idle_step (hlp : procPull P.n L = none) :
    (layer P r).step (u, v) L (PMF.pure (u, v)) := by
  rw [layer, System.parallel_step]
  exact Or.inl ⟨rlab_ne_tau_of_none hlp, PMF.pure u, PMF.pure v,
    Gather.syncLift_pure (rlab_ne_tau_of_none hlp) (fun i => Gather.lift_idle hlp),
    Gather.lift_idle hlp, (prodPMF_pure_pure _ _).symm⟩

/-- Build the layer's joint transition from the programs' rows and the row of
the layer's network. -/
theorem layer_lab_step {lp : PLab P.n} (hlp : procPull P.n L = some lp) (hlpτ : lp ≠ PLab.tau)
    (hproc : ∀ i, ProcStep P r i (u i) lp (PMF.pure (x i)))
    (hnet : NetStep P r v lp (PMF.pure v')) :
    (layer P r).step (u, v) L (PMF.pure (x, v')) := by
  rw [layer, System.parallel_step]
  exact Or.inl ⟨rlab_ne_tau hlp hlpτ, PMF.pure x, PMF.pure v',
    Gather.syncLift_pure (rlab_ne_tau hlp hlpτ)
      (fun i => Gather.row_lift_step hlp (hproc i)),
    Gather.row_lift_step hlp hnet, (prodPMF_pure_pure _ _).symm⟩

/-- The participant's row beside the idle rows of every other program is the
program group stepping into the updated function. -/
theorem procStep_update {j : Fin P.n} {q : ProcRec P.n} {lp : PLab P.n}
    (hj : ProcStep P r j (u j) lp (PMF.pure q))
    (hne : ∀ i, i ≠ j → ProcStep P r i (u i) lp (PMF.pure (u i))) :
    ∀ i, ProcStep P r i (u i) lp (PMF.pure (Function.update u j q i)) := by
  intro i
  by_cases hi : i = j
  · subst hi; rw [Function.update_self]; exact hj
  · rw [Function.update_of_ne hi]; exact hne i hi

end Layer

/-! ### The layer beside the two gather instances

A visible label moves all three factors, and the joint distribution is their
Dirac product. A silent label moves exactly one of the two gather instances:
the layer has no silent transition. -/

section RoundPre

variable {P : Params} {r : ℕ} {G₁ G₂ : Type}
  {ga1 : System G₁ (Gather.InstLab P.n Bool)}
  {ga2 : System G₂ (Gather.InstLab P.n (Option Bool))}
  {u x : ∀ _ : Fin P.n, ProcRec P.n} {v v' : Option Bool} {c c' : G₁} {d d' : G₂}
  {L : RLab P.n}

/-- **The joint inversion.** A visible transition of the layer beside the two
gather instances: every factor steps on the label, and the joint distribution
is their Dirac product. -/
theorem roundPreAt_joint_inv (h1 : ga1.IsLTS) (h2 : ga2.IsLTS)
    (hL : L ≠ (Silent.τ : RLab P.n)) {μ : PMF (RoundStateAt P.n G₁ G₂)}
    (h : (roundPreAt P r ga1 ga2).step ((u, v), (c, d)) L μ) :
    ∃ (x : ∀ _ : Fin P.n, ProcRec P.n) (v' : Option Bool) (c' : G₁) (d' : G₂),
      μ = PMF.pure ((x, v'), (c', d')) ∧
      (layer P r).step (u, v) L (PMF.pure (x, v')) ∧
      (ga1.mapIdle (ga1Pull P.n)).step c L (PMF.pure c') ∧
      (ga2.mapIdle (ga2Pull P.n)).step d L (PMF.pure d') := by
  rw [roundPreAt, System.parallel_step] at h
  rcases h with ⟨-, μ₁, μ₂, hlay, hga, rfl⟩ | ⟨hτ, -⟩ | ⟨hτ, -⟩
  · obtain ⟨⟨y, w⟩, rfl⟩ := layer_isLTS P r _ _ _ hlay
    rw [System.parallel_step] at hga
    rcases hga with ⟨-, ρ₁, ρ₂, hc, hd, rfl⟩ | ⟨hτ, -⟩ | ⟨hτ, -⟩
    · obtain ⟨c', rfl⟩ := System.mapIdle_isLTS _ h1 _ _ _ hc
      obtain ⟨d', rfl⟩ := System.mapIdle_isLTS _ h2 _ _ _ hd
      exact ⟨y, w, c', d', by rw [prodPMF_pure_pure, prodPMF_pure_pure], hlay, hc, hd⟩
    · exact absurd hτ hL
    · exact absurd hτ hL
  · exact absurd hτ hL
  · exact absurd hτ hL

/-- **The silent inversion.** A silent transition of the layer beside the two
gather instances is a silent step of one gather instance. -/
theorem roundPreAt_tau_inv (h1 : ga1.IsLTS) (h2 : ga2.IsLTS)
    {μ : PMF (RoundStateAt P.n G₁ G₂)}
    (h : (roundPreAt P r ga1 ga2).step ((u, v), (c, d)) (Silent.τ : RLab P.n) μ) :
    (∃ c', μ = PMF.pure ((u, v), (c', d)) ∧
      ga1.step c (Silent.τ : Gather.InstLab P.n Bool) (PMF.pure c')) ∨
    (∃ d', μ = PMF.pure ((u, v), (c, d')) ∧
      ga2.step d (Silent.τ : Gather.InstLab P.n (Option Bool)) (PMF.pure d')) := by
  rw [roundPreAt, System.parallel_step] at h
  rcases h with ⟨hτ, -⟩ | ⟨-, μ₁, hlay, rfl⟩ | ⟨-, μ₂, hga, rfl⟩
  · exact absurd rfl hτ
  · exact absurd hlay layer_no_tau
  · rw [System.parallel_step] at hga
    rcases hga with ⟨hτ, -⟩ | ⟨-, ρ₁, hc, rfl⟩ | ⟨-, ρ₂, hd, rfl⟩
    · exact absurd rfl hτ
    · have hstep := (System.mapIdle_step_some (ga1Pull_tau P.n) _).mp hc
      obtain ⟨c', rfl⟩ := h1 _ _ _ hstep
      exact Or.inl ⟨c', by rw [prodPMF_pure_pure, prodPMF_pure_pure], hstep⟩
    · have hstep := (System.mapIdle_step_some (ga2Pull_tau P.n) _).mp hd
      obtain ⟨d', rfl⟩ := h2 _ _ _ hstep
      exact Or.inr ⟨d', by rw [prodPMF_pure_pure, prodPMF_pure_pure], hstep⟩

/-- Build a visible transition of the layer beside the two gather instances. -/
theorem roundPreAt_lab_step (hL : L ≠ (Silent.τ : RLab P.n))
    (hlayer : (layer P r).step (u, v) L (PMF.pure (x, v')))
    (hga1 : (ga1.mapIdle (ga1Pull P.n)).step c L (PMF.pure c'))
    (hga2 : (ga2.mapIdle (ga2Pull P.n)).step d L (PMF.pure d')) :
    (roundPreAt P r ga1 ga2).step ((u, v), (c, d)) L (PMF.pure ((x, v'), (c', d'))) := by
  rw [roundPreAt, System.parallel_step]
  refine Or.inl ⟨hL, PMF.pure (x, v'), PMF.pure (c', d'), hlayer, ?_,
    (prodPMF_pure_pure _ _).symm⟩
  rw [System.parallel_step]
  exact Or.inl ⟨hL, PMF.pure c', PMF.pure d', hga1, hga2, (prodPMF_pure_pure _ _).symm⟩

/-- Build a silent transition of the layer beside the two gather instances from
a silent step of the first gather. -/
theorem roundPreAt_tau_ga1 (h : ga1.step c (Silent.τ : Gather.InstLab P.n Bool) (PMF.pure c')) :
    (roundPreAt P r ga1 ga2).step ((u, v), (c, d)) (Silent.τ : RLab P.n)
      (PMF.pure ((u, v), (c', d))) := by
  rw [roundPreAt, System.parallel_step]
  refine Or.inr (Or.inr ⟨rfl, PMF.pure (c', d), ?_, (prodPMF_pure_pure _ _).symm⟩)
  rw [System.parallel_step]
  exact Or.inr (Or.inl ⟨rfl, PMF.pure c',
    (System.mapIdle_step_some (ga1Pull_tau P.n) _).mpr h, (prodPMF_pure_pure _ _).symm⟩)

/-- Build a silent transition of the layer beside the two gather instances from
a silent step of the second gather. -/
theorem roundPreAt_tau_ga2
    (h : ga2.step d (Silent.τ : Gather.InstLab P.n (Option Bool)) (PMF.pure d')) :
    (roundPreAt P r ga1 ga2).step ((u, v), (c, d)) (Silent.τ : RLab P.n)
      (PMF.pure ((u, v), (c, d'))) := by
  rw [roundPreAt, System.parallel_step]
  refine Or.inr (Or.inr ⟨rfl, PMF.pure (c, d'), ?_, (prodPMF_pure_pure _ _).symm⟩)
  rw [System.parallel_step]
  exact Or.inr (Or.inr ⟨rfl, PMF.pure d',
    (System.mapIdle_step_some (ga2Pull_tau P.n) _).mpr h, (prodPMF_pure_pure _ _).symm⟩)

/-- A hidden event is a silent transition of the round. -/
theorem roundInstAt_event_step (e : REvt P.n)
    (hlayer : (layer P r).step (u, v) (Sum.inr e) (PMF.pure (x, v')))
    (hga1 : (ga1.mapIdle (ga1Pull P.n)).step c (Sum.inr e) (PMF.pure c'))
    (hga2 : (ga2.mapIdle (ga2Pull P.n)).step d (Sum.inr e) (PMF.pure d')) :
    (roundInstAt P r ga1 ga2).step ((u, v), (c, d)) (Sum.inl Lab.tau)
      (PMF.pure ((x, v'), (c', d'))) :=
  (roundInstAt_step_iff P r ga1 ga2 _ _ _).mpr
    (Or.inl ⟨rfl, e, roundPreAt_lab_step (by simp) hlayer hga1 hga2⟩)

/-- A visible family label is a transition of the round. -/
theorem roundInstAt_lab_step {l : NLab P.n} (hl : l ≠ Sum.inl Lab.tau)
    (hlayer : (layer P r).step (u, v) (Sum.inl l) (PMF.pure (x, v')))
    (hga1 : (ga1.mapIdle (ga1Pull P.n)).step c (Sum.inl l) (PMF.pure c'))
    (hga2 : (ga2.mapIdle (ga2Pull P.n)).step d (Sum.inl l) (PMF.pure d')) :
    (roundInstAt P r ga1 ga2).step ((u, v), (c, d)) l (PMF.pure ((x, v'), (c', d'))) := by
  refine (roundInstAt_step_iff P r ga1 ga2 _ _ _).mpr
    (Or.inr (roundPreAt_lab_step ?_ hlayer hga1 hga2))
  rw [rlab_tau]
  simpa using hl

/-- A silent step of the first gather is a silent transition of the round. -/
theorem roundInstAt_tau_ga1 (h : ga1.step c (Silent.τ : Gather.InstLab P.n Bool) (PMF.pure c')) :
    (roundInstAt P r ga1 ga2).step ((u, v), (c, d)) (Sum.inl Lab.tau)
      (PMF.pure ((u, v), (c', d))) :=
  (roundInstAt_step_iff P r ga1 ga2 _ _ _).mpr (Or.inr (roundPreAt_tau_ga1 h))

/-- A silent step of the second gather is a silent transition of the round. -/
theorem roundInstAt_tau_ga2
    (h : ga2.step d (Silent.τ : Gather.InstLab P.n (Option Bool)) (PMF.pure d')) :
    (roundInstAt P r ga1 ga2).step ((u, v), (c, d)) (Sum.inl Lab.tau)
      (PMF.pure ((u, v), (c, d'))) :=
  (roundInstAt_step_iff P r ga1 ga2 _ _ _).mpr (Or.inr (roundPreAt_tau_ga2 h))

end RoundPre

/-! ### One program's rules, by label class

Each lemma reads a row of the table off its label: the participant's row as its
guards together with the Dirac it produces, and the idle row of a
non-participant as the identity. -/

section ProcInversion

variable {P : Params} {r : ℕ} {j : Fin P.n} {p : ProcRec P.n} {ν : PMF (ProcRec P.n)}

/-- A call row names the program's own round. -/
theorem procStep_callG_round {r' : ℕ} {i : Fin P.n} {b : Bool}
    (h : ProcStep P r j p (.callG r' i b) ν) : r' = r := by cases h <;> rfl

/-- A call-loop row names the program's own round. -/
theorem procStep_callLoop_round {r' : ℕ} {i : Fin P.n} {b : Bool}
    (h : ProcStep P r j p (.callLoop r' i b) ν) : r' = r := by cases h <;> rfl

/-- A return row names the program's own round. -/
theorem procStep_retG_round {r' : ℕ} {i : Fin P.n} {out : GbcaOut} {bnd : Bool}
    (h : ProcStep P r j p (.retG r' i out bnd) ν) : r' = r := by cases h <;> rfl

theorem procStep_callG_own {b : Bool} (h : ProcStep P r j p (.callG r j b) ν) :
    p.input = none ∧ ν = PMF.pure { p with input := some b } := by
  cases h
  case callG => exact ⟨by assumption, rfl⟩
  case callGIdle => exact absurd rfl ‹_ ≠ j›

theorem procStep_callG_foreign {i : Fin P.n} {b : Bool} (hi : i ≠ j)
    (h : ProcStep P r j p (.callG r i b) ν) : ν = PMF.pure p := by
  cases h
  case callG => exact absurd rfl hi
  case callGIdle => rfl

theorem procStep_callLoop {i : Fin P.n} {b : Bool}
    (h : ProcStep P r j p (.callLoop r i b) ν) : ν = PMF.pure p := by
  cases h
  case callLoop => rfl
  case callLoopIdle => rfl

theorem procStep_ret1_own {g : Fin P.n → Option Bool} {C : Gather.APSet P.n Bool}
    (h : ProcStep P r j p (.ret1 j g C) ν) :
    p.input ≠ none ∧ p.cand = none ∧ ν = PMF.pure { p with cand := some (cand P g) } := by
  cases h
  case ret1 => exact ⟨by assumption, by assumption, rfl⟩
  case ret1Idle => exact absurd rfl ‹_ ≠ j›

theorem procStep_ret1_foreign {i : Fin P.n} {g : Fin P.n → Option Bool}
    {C : Gather.APSet P.n Bool} (hi : i ≠ j) (h : ProcStep P r j p (.ret1 i g C) ν) :
    ν = PMF.pure p := by
  cases h
  case ret1 => exact absurd rfl hi
  case ret1Idle => rfl

theorem procStep_call2_own {x : Option Bool} (h : ProcStep P r j p (.call2 j x) ν) :
    p.cand = some x ∧ p.called2 = false ∧ ν = PMF.pure { p with called2 := true } := by
  cases h
  case call2 => exact ⟨by assumption, by assumption, rfl⟩
  case call2Idle => exact absurd rfl ‹_ ≠ j›

theorem procStep_call2_foreign {i : Fin P.n} {x : Option Bool} (hi : i ≠ j)
    (h : ProcStep P r j p (.call2 i x) ν) : ν = PMF.pure p := by
  cases h
  case call2 => exact absurd rfl hi
  case call2Idle => rfl

theorem procStep_ret2_own {g : Fin P.n → Option (Option Bool)}
    {C : Gather.APSet P.n (Option Bool)} (h : ProcStep P r j p (.ret2 j g C) ν) :
    p.called2 = true ∧ p.out = none ∧ ν = PMF.pure { p with out := some (gradeOf P g) } := by
  cases h
  case ret2 => exact ⟨by assumption, by assumption, rfl⟩
  case ret2Idle => exact absurd rfl ‹_ ≠ j›

theorem procStep_ret2_foreign {i : Fin P.n} {g : Fin P.n → Option (Option Bool)}
    {C : Gather.APSet P.n (Option Bool)} (hi : i ≠ j) (h : ProcStep P r j p (.ret2 i g C) ν) :
    ν = PMF.pure p := by
  cases h
  case ret2 => exact absurd rfl hi
  case ret2Idle => rfl

theorem procStep_retG_own {out : GbcaOut} {bnd : Bool}
    (h : ProcStep P r j p (.retG r j out bnd) ν) :
    p.out = some out ∧ p.returned = false ∧
      ν = PMF.pure { p with out := none, returned := true } := by
  cases h
  case retG => exact ⟨by assumption, by assumption, rfl⟩
  case retGIdle => exact absurd rfl ‹_ ≠ j›

theorem procStep_retG_foreign {i : Fin P.n} {out : GbcaOut} {bnd : Bool} (hi : i ≠ j)
    (h : ProcStep P r j p (.retG r i out bnd) ν) : ν = PMF.pure p := by
  cases h
  case retG => exact absurd rfl hi
  case retGIdle => rfl

end ProcInversion

/-! ### The rules of the layer's network, by label class -/

section NetInversion

variable {P : Params} {r : ℕ} {w : Option Bool} {μ : PMF (Option Bool)}

theorem netStep_callG {id : Fin P.n} {b : Bool} (h : NetStep P r w (.callG r id b) μ) :
    μ = PMF.pure w := by cases h; rfl

theorem netStep_callLoop {id : Fin P.n} {b : Bool} (h : NetStep P r w (.callLoop r id b) μ) :
    μ = PMF.pure w := by cases h; rfl

theorem netStep_ret1 {id : Fin P.n} {g : Fin P.n → Option Bool} {C : Gather.APSet P.n Bool}
    (h : NetStep P r w (.ret1 id g C) μ) :
    μ = PMF.pure (some (w.getD (boundOfCore P C))) := by cases h; rfl

theorem netStep_call2 {id : Fin P.n} {x : Option Bool} (h : NetStep P r w (.call2 id x) μ) :
    μ = PMF.pure w := by cases h; rfl

theorem netStep_ret2 {id : Fin P.n} {g : Fin P.n → Option (Option Bool)}
    {C : Gather.APSet P.n (Option Bool)} (h : NetStep P r w (.ret2 id g C) μ) :
    μ = PMF.pure w := by cases h; rfl

theorem netStep_retG {id : Fin P.n} {out : GbcaOut} {bnd : Bool}
    (h : NetStep P r w (.retG r id out bnd) μ) :
    bnd = w.getD (boundOfCore P ∅) ∧ μ = PMF.pure w := by cases h; exact ⟨rfl, rfl⟩

end NetInversion

end GBCA.ByAFW
end ABA
end PLTS
