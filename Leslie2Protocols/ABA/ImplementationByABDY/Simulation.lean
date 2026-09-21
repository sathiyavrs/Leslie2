/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sathiya / Claude
-/

import Leslie2Protocols.ABA.ImplementationByABDY.System
import Leslie2Protocols.ABA.Composition.HybridAndSubstitution

/-!
# The protocol under its composed reading

The protocol reading of `ABA/ImplementationByABDY/System.lean` and the composed reading of
`ABA/Composition/HybridAndSubstitution.lean` present one protocol at two cuts. A process record of
the protocol carries the round-loop record beside the stage record of every round
the process has touched (D22). A composed state carries one graded-agreement
instance per round, at every moment. The stage record of round `r` at a
process is the entry of that process in the instance of round `r`, so the two
cuts hold the same stage data indexed two ways: by process on one side, by
round on the other.

Everything here is read in the namespace `ABDY`, where each name is that of its
counterpart in the gather-based chain's `AFW`, and the qualifier is dropped below.

## The relation

`ProtocolRelation` pins every coordinate of a composed state, in five conjuncts and
under no guard. Both returns of a round read the ghost record of that round for
the bit they announce and write it back, so the two sides announce one bit and
the fourth conjunct is restored by `rel_setBound`.

* The round loops are the first components of the process records.
* The coin oracle is the same component on both sides.
* The ABA-side network is the protocol adversary's DECIDED sets beside its
  corrupted set.
* The network state of round `r` is the adversary's round-`r` message sets beside the
  same corrupted set and the adversary's ghost record of round `r`. Corruption
  is one broadcast on both sides, so every copy of the corrupted set is the
  adversary's; the round's bound bit is the adversary's ghost record of that
  round, which is the composed reading of the bit the instance's network state
  holds.
* The entry of process `j` in the instance of round `r` is the stage record of
  round `r` that `j` holds. This is one equation for each pair `(j, r)`. A
  round `j` has not touched reads as the initial stage record on the protocol
  side, and the equation asks the composed entry to be initial there too.

A composed state is therefore determined by any protocol state related to it.
The determination is not injective: no composed state carries a termination
flag, so two protocol states differing only in which processes have terminated
are related to the same composed state.

## What this file supplies

`protocolSim`, a probabilistic forward simulation of `composed P` by
`protocol P` along the Dirac lift of `ProtocolRelation P`, and the trace-distribution
inclusion `protocol_composed` it yields. The inclusion is one-directional
because the composed reading takes transitions the protocol declines. A round
instance has a row for the Byzantine graded-agreement rows, and no protocol
program has one (D11, D22); the instance's stage rules carry no termination
guard, so the instance answers a send or a delivery at a process the protocol
has terminated. In the other direction the protocol's `terminate` row writes a
field the relation does not read, and the composed answer to it is a stutter.
-/

namespace PLTS
namespace ABA

open Implementation Composition

namespace ABDY

/-- **The relation of the protocol presentation to the composed one.** Writing
`u = (processes, w, o)` and `t = (G, C, A, o')`, the five conjuncts are: the round
loops agree; the oracle is shared; the ABA-side network is the adversary's
DECIDED sets beside its corrupted set; each round's network state is that round's
messagesOf of the adversary's sent sets beside the same corrupted set and the
adversary's ghost record of that round; and the entry of process `j` in the
instance of round `r` is the stage record of round `r` that `j` holds (D22). No
conjunct is guarded, so the composed state is determined. -/
def ProtocolRelation (P : Parameters) (u : ProtocolState P) (t : ComposedState P) : Prop :=
  (∀ j, (u.1 j).1 = t.2.1 j) ∧
  u.2.2 = t.2.2.2 ∧
  t.2.2.1 = ⟨u.2.1.decidedSent, u.2.1.F⟩ ∧
  (∀ r, (t.1 r).2 = ⟨u.2.1.sent r, u.2.1.F, u.2.1.ghostRecord r⟩) ∧
  (∀ j r, (t.1 r).1 j = (u.1 j).2.roundRecord r)

/-- The relation, read at an explicit pair of states. -/
theorem protocolRelation_mk (P : Parameters) (processes : ∀ _ : Fin P.n,
    ProcessRecord P.n) (w : NetworkState P.n) (o : ℕ → WCC.SpecState P.n) (G : ℕ →
      GBCA.ByABDY.ImplementationState P.n)
    (C : ∀ _ : Fin P.n, RoundLoopRecord P.n) (A : ABANetworkState P.n)
    (o' : ℕ → WCC.SpecState P.n) :
    ProtocolRelation P (processes, w, o) (G, C, A, o') ↔
      (∀ j, (processes j).1 = C j) ∧
      o = o' ∧
      A = ⟨w.decidedSent, w.F⟩ ∧
      (∀ r, (G r).2 = ⟨w.sent r, w.F, w.ghostRecord r⟩) ∧
      (∀ j r, (G r).1 j = (processes j).2.roundRecord r) :=
  Iff.rfl

/-! ### Couplings

Every protocol transition is a product of Dirac factors beside the oracle's
successor distribution, and so is the composed transition that answers it. The
coupling is functional in the oracle coordinate: the two presentations carry the
same oracle, so a protocol outcome and the composed outcome that matches it
differ in no coordinate the relation constrains. -/

/-- A Dirac protocol outcome matched by a single related composed state. -/
private theorem match_pure (P : Parameters) {s : ProtocolState P} {t : ComposedState P}
    (h : ProtocolRelation P s t) :
    ∃ Ω : PMF (PMF (ComposedState P)),
      PMFRel (diracRel (ProtocolRelation P)) (PMF.pure s) Ω ∧ Ω.bind id = PMF.pure t := by
  refine ⟨PMF.pure (PMF.pure t), ⟨PMF.pure (s, PMF.pure t), ?_, ?_, ?_⟩, ?_⟩
  · rw [PMF.pure_map]
  · rw [PMF.pure_map]
  · intro p hp
    rw [PMF.mem_support_pure_iff] at hp
    subst hp
    exact ⟨t, rfl, h⟩
  · rw [PMF.pure_bind]
    rfl

/-- A protocol outcome whose only free coordinate is the oracle's, matched
outcome by outcome. -/
private theorem match_prod (P : Parameters) {x : ∀ _ : Fin P.n, ProcessRecord P.n}
    {w : NetworkState P.n} {G : ℕ → GBCA.ByABDY.ImplementationState P.n}
    {C : ∀ _ : Fin P.n, RoundLoopRecord P.n} {A : ABANetworkState P.n}
    {ν : PMF (ℕ → WCC.SpecState P.n)}
    (h : ∀ o ∈ ν.support, ProtocolRelation P (x, w, o) (G, C, A, o)) :
    ∃ Ω : PMF (PMF (ComposedState P)),
      PMFRel (diracRel (ProtocolRelation P)) (prodPMF (PMF.pure x) (prodPMF (PMF.pure w) ν)) Ω ∧
      Ω.bind id =
        prodPMF (PMF.pure G) (prodPMF (PMF.pure C) (prodPMF (PMF.pure A) ν)) := by
  refine ⟨ν.map (fun o => PMF.pure ((G, C, A, o) : ComposedState P)),
    ⟨ν.map (fun o => (((x, w, o) : ProtocolState P),
      PMF.pure ((G, C, A, o) : ComposedState P))), ?_, ?_, ?_⟩, ?_⟩
  · rw [PMF.map_comp, prodPMF_pure₂]
    rfl
  · rw [PMF.map_comp]
    rfl
  · intro p hp
    rw [PMF.mem_support_map_iff] at hp
    obtain ⟨o, ho, rfl⟩ := hp
    exact ⟨(G, C, A, o), rfl, h o ho⟩
  · rw [PMF.bind_map, prodPMF_pure₃]
    rfl

/-! ### Updating one round

A label owned by round `r` moves that round's instance and no other. The two
lemmas below read the stage columns and the network states of the updated family. -/

/-- Updating round `r` by a state whose stage columns are the ones it already
had leaves every stage column where it was. -/
private theorem update_fst {P : Parameters} (G : ℕ → GBCA.ByABDY.ImplementationState P.n) (r : ℕ)
    {X : GBCA.ByABDY.ImplementationState P.n} (hX : X.1 = (G r).1) (r' : ℕ) :
    (Function.update G r X r').1 = (G r').1 := by
  by_cases h : r' = r
  · subst h; rw [Function.update_self, hX]
  · rw [Function.update_of_ne h]

/-- Updating round `r` by a state whose network state is the one it already had leaves
every network state where it was. -/
private theorem update_snd {P : Parameters} (G : ℕ → GBCA.ByABDY.ImplementationState P.n) (r : ℕ)
    (u : ∀ _ : Fin P.n, GBCA.ByABDY.RoundRecord P.n) (r' : ℕ) :
    (Function.update G r (u, (G r).2) r').2 = (G r').2 := by
  by_cases h : r' = r
  · subst h; rw [Function.update_self]
  · rw [Function.update_of_ne h]

/-- The network state conjunct after a stage multicast in round `r`. -/
private theorem rel_recordGBCASend {P : Parameters} {G : ℕ → GBCA.ByABDY.ImplementationState P.n}
    {w : NetworkState P.n} (hG : ∀ r, (G r).2 = ⟨w.sent r, w.F, w.ghostRecord r⟩)
    (r : ℕ) (k : Fin P.n) (m : GBCA.ByABDY.Message) (u : ∀ _ : Fin P.n, GBCA.ByABDY.RoundRecord P.n)
    (r' : ℕ) :
    ((Function.update G r (u, ((G r).2).recordGBCASend k m)) r').2 =
      ⟨(w.recordGBCASend r k m).sent r', (w.recordGBCASend r k m).F,
        (w.recordGBCASend r k m).ghostRecord r'⟩ := by
  by_cases hr : r' = r
  · subst hr
    rw [Function.update_self]
    change ((G r').2).recordGBCASend k m = _
    rw [hG r']
    simp [GBCA.ByABDY.NetworkState.recordGBCASend]
  · rw [Function.update_of_ne hr, hG r', recordGBCASend_sent_ne w r k m hr]
    simp

/-- The bit a return announces is the round's bound bit after the write: the
record is write-once, so a return that announces a bit already on record leaves
the record where it stands. -/
private theorem ghostOut_getD {P : Parameters} {w : NetworkState P.n} {r : ℕ} {id : Fin P.n}
    {out : GBCAOutput} {bnd : Bool} (h : bnd = abdyGhostOut P w r id out) :
    (w.ghostRecord r).getD bnd = bnd := by
  unfold abdyGhostOut at h
  cases hg : w.ghostRecord r with
  | none => rfl
  | some β => rw [hg] at h; exact h.symm

/-- The network state conjunct after a return of round `r`. The instance's bound
bit and the adversary's ghost record of round `r` take the same bit, and every
other round's record stands still. -/
private theorem rel_setBound {P : Parameters} {G : ℕ → GBCA.ByABDY.ImplementationState P.n}
    {w : NetworkState P.n} (hG : ∀ r', (G r').2 = ⟨w.sent r', w.F, w.ghostRecord r'⟩)
    (r : ℕ) (bnd : Bool) (u : ∀ _ : Fin P.n, GBCA.ByABDY.RoundRecord P.n)
    (hfix : (w.ghostRecord r).getD bnd = bnd) {L : ExtendedLabel P.n}
    (hself : (w.writeGhost (abdyGhostStep P) L).ghostRecord r
      = some ((w.ghostRecord r).getD bnd))
    (hne : ∀ r', r' ≠ r →
      (w.writeGhost (abdyGhostStep P) L).ghostRecord r' = w.ghostRecord r')
    (r' : ℕ) :
    ((Function.update G r (u, ((G r).2).setBound bnd)) r').2
      = ⟨(w.writeGhost (abdyGhostStep P) L).sent r',
         (w.writeGhost (abdyGhostStep P) L).F,
         (w.writeGhost (abdyGhostStep P) L).ghostRecord r'⟩ := by
  by_cases hr : r' = r
  · subst hr
    rw [Function.update_self, hG r', hself, hfix]
    simp [GBCA.ByABDY.NetworkState.setBound]
  · rw [Function.update_of_ne hr, hG r', hne r' hr]
    simp

/-- The network state's corruption act and the adversary's agree. -/
private theorem corrupt_gbcaNetwork {P : Parameters} (w : NetworkState P.n) (k : Fin P.n) (r : ℕ) :
    (⟨w.sent r, w.F, w.ghostRecord r⟩ : GBCA.ByABDY.NetworkState P.n).corrupt P k =
      ⟨(NetworkState.corrupt P k w).sent r, (NetworkState.corrupt P k w).F,
        (NetworkState.corrupt P k w).ghostRecord r⟩ := by
  by_cases hc : k ∉ w.F ∧ w.F.card < P.f <;>
    simp [GBCA.ByABDY.NetworkState.corrupt, Implementation.NetworkState.corrupt, hc]

/-- The ABA-side network's corruption act and the adversary's agree. -/
private theorem corrupt_abaNetwork {P : Parameters} (w : NetworkState P.n) (k : Fin P.n) :
    ABANetworkState.corrupt P k ⟨w.decidedSent, w.F⟩ =
      ⟨(NetworkState.corrupt P k w).decidedSent, (NetworkState.corrupt P k w).F⟩ := by
  by_cases hc : k ∉ w.F ∧ w.F.card < P.f <;>
    simp [ABANetworkState.corrupt, Implementation.NetworkState.corrupt, hc]

/-! ### Transporting the columns conjunct

The conjunct that speaks of the stage columns is read process by process.
Under a transition at which one process writes and the composed family leaves
every other column alone, it follows from the conjunct before the step and from
the mover's own family of new-column equations. -/

/-- The columns conjunct under a write at one process. -/
private theorem rel_roundRecord (P : Parameters) {processes x : ∀ _ : Fin P.n, ProcessRecord P.n}
    {G G' : ℕ → GBCA.ByABDY.ImplementationState P.n} (id : Fin P.n)
    (hst : ∀ j r, (G r).1 j = (processes j).2.roundRecord r)
    (hfor : ∀ i, i ≠ id → x i = processes i)
    (hGfor : ∀ j r, j ≠ id → (G' r).1 j = (G r).1 j)
    (hown : ∀ r, (G' r).1 id = (x id).2.roundRecord r) :
    ∀ j r, (G' r).1 j = (x j).2.roundRecord r := by
  intro j r
  by_cases h : j = id
  · subst h; exact hown r
  · rw [hGfor j r h, hfor j h]; exact hst j r

/-- The columns conjunct under a transition at which no process writes. -/
private theorem rel_none (P : Parameters) {processes x : ∀ _ : Fin P.n, ProcessRecord P.n}
    {G G' : ℕ → GBCA.ByABDY.ImplementationState P.n}
    (hst : ∀ j r, (G r).1 j = (processes j).2.roundRecord r)
    (hfor : ∀ i, x i = processes i)
    (hGfor : ∀ j r, (G' r).1 j = (G r).1 j) :
    ∀ j r, (G' r).1 j = (x j).2.roundRecord r := by
  intro j r
  rw [hGfor j r, hfor j]; exact hst j r

/-! ### Assembling a composed transition

Two shapes of answer. A label the composed system takes on the nose is
answered by the rows of its four components. A stage rendezvous has no row at
three of them: it is internal to a round instance, and the family carries it
as its own silent rule. -/

/-- A visible label of the extended alphabet answered by the four composed
rows, the oracle's successor carried across. -/
private theorem match_vis (P : Parameters) {x : ∀ _ : Fin P.n, ProcessRecord P.n}
    {w' : NetworkState P.n} {o : ℕ → WCC.SpecState P.n}
    {ω : PMF (ℕ → WCC.SpecState P.n)}
    {G G' : ℕ → GBCA.ByABDY.ImplementationState P.n} {C C' : ∀ _ : Fin P.n, RoundLoopRecord P.n}
    {A A' : ABANetworkState P.n} {L : ExtendedLabel P.n} (hL : L ≠ Silent.τ)
    (hrel : ∀ o' ∈ ω.support, ProtocolRelation P (x, w', o') (G', C', A', o'))
    (hGs : (GBCA.ByABDY.gbcaInstanceFamily P).step G L (PMF.pure G'))
    (hCs : ∀ i, RoundLoopStep P i (C i) L (PMF.pure (C' i)))
    (hAs : ABANetworkStep P A L (PMF.pure A'))
    (hWs : (coinOverRoundAlphabet P).step o L ω) :
    ∃ Ω : PMF (PMF (ComposedState P)),
      PMFRel (diracRel (ProtocolRelation P))
        (prodPMF (PMF.pure x) (prodPMF (PMF.pure w') ω)) Ω ∧
      (composedExtended P).step (G, C, A, o) L (Ω.bind id) := by
  obtain ⟨Ω, hr, hbind⟩ := match_prod P hrel
  exact ⟨Ω, hr, hbind ▸ composedExtended_vis_step P hL hGs hCs hAs hWs⟩

/-- A rendezvous the composed reading answers inside one round: the
instance of round `r` takes it as its own silent rule. -/
private theorem match_round (P : Parameters) {x : ∀ _ : Fin P.n, ProcessRecord P.n}
    {w' : NetworkState P.n} {o : ℕ → WCC.SpecState P.n} {ν : PMF (ℕ → WCC.SpecState P.n)}
    {G : ℕ → GBCA.ByABDY.ImplementationState P.n} {C : ∀ _ : Fin P.n, RoundLoopRecord P.n}
    {A : ABANetworkState P.n} {r : ℕ} {X : GBCA.ByABDY.ImplementationState P.n} (hν : ν = PMF.pure
      o)
    (hrel : ProtocolRelation P (x, w', o) (Function.update G r X, C, A, o))
    (hsub : (GBCA.ByABDY.composition P r).step (G r) (Sum.inl Label.tau) (PMF.pure X)) :
    ∃ Ω : PMF (PMF (ComposedState P)),
      PMFRel (diracRel (ProtocolRelation P))
        (prodPMF (PMF.pure x) (prodPMF (PMF.pure w') ν)) Ω ∧
      (composedHidden P).step (G, C, A, o) Label.tau (Ω.bind id) := by
  subst hν
  obtain ⟨Ω, hr, hbind⟩ := match_pure P hrel
  refine ⟨Ω, ?_, ?_⟩
  · rw [prodPMF_pure_pure, prodPMF_pure_pure]; exact hr
  · rw [hbind]
    exact composedHidden_of_tau P (composedExtended_tau_gbca P (gbcaInstanceFamily_tau P G r hsub))

/-! ### The handshake rows the protocol process group cannot take

A Byzantine graded-agreement call or return names a process, and the protocol
program of that process has no row for it (D11, D22). Neither has the replaced
program of a corrupted process, those labels lying in `actsAt` (D23). The
process group is a full synchronisation, so no protocol transition carries
either label. -/


/-! ### The matching, by label class

A transition of the protocol group is a hidden rendezvous, a visible shared
label, or the silent label. Each is answered by a transition of the composed
group on the same label, built from the rows of the four composed components.
A corrupted process's replaced program is matched loop for loop: where the
protocol program self-loops, the composed round loop takes `corruptedIdle`.
The return that self-loop carries without DECIDED evidence is authorised on the
composed side by the ABA-side network's Byzantine row (D23). -/

/-- The matching on the rendezvous alphabet. -/
theorem match_event (P : Parameters) {processes : ∀ _ : Fin P.n, ProcessRecord P.n}
    {w : NetworkState P.n} {o : ℕ → WCC.SpecState P.n}
    {G : ℕ → GBCA.ByABDY.ImplementationState P.n} {C : ∀ _ : Fin P.n, RoundLoopRecord P.n}
    {A : ABANetworkState P.n} (hR : ProtocolRelation P (processes, w, o) (G, C, A, o))
    (e : NetworkEvent P.n) {μ : PMF (ProtocolState P)}
    (h : (protocolExtended P).step (processes, w, o) (Sum.inr e) μ) :
    ∃ Ω : PMF (PMF (ComposedState P)),
      PMFRel (diracRel (ProtocolRelation P)) μ Ω ∧
      (composedHidden P).step (G, C, A, o) Label.tau (Ω.bind id) := by
  obtain ⟨hC, -, hA, hG, hst⟩ := (protocolRelation_mk P _ _ _ _ _ _ _).mp hR
  have hCeq : ∀ i, C i = (processes i).1 := fun i => (hC i).symm
  obtain ⟨x, w', ν, hall, hn, hWs, rfl⟩ := protocolExtended_event_inv P h
  have hLne : (Sum.inr e : ExtendedLabel P.n) ≠ Silent.τ := by
    simp
  have hvis : ∀ {G' : ℕ → GBCA.ByABDY.ImplementationState P.n} {A' : ABANetworkState P.n},
      (∀ o' ∈ ν.support, ProtocolRelation P (x, w', o') (G', fun i => (x i).1, A', o')) →
      (GBCA.ByABDY.gbcaInstanceFamily P).step G (Sum.inr e) (PMF.pure G') →
      (∀ i, RoundLoopStep P i (C i) (Sum.inr e) (PMF.pure ((x i).1))) →
      ABANetworkStep P A (Sum.inr e) (PMF.pure A') →
      ∃ Ω : PMF (PMF (ComposedState P)),
        PMFRel (diracRel (ProtocolRelation P))
          (prodPMF (PMF.pure x) (prodPMF (PMF.pure w') ν)) Ω ∧
        (composedHidden P).step (G, C, A, o) Label.tau (Ω.bind id) := by
    intro G' A' hrel hGs hCs hAs
    obtain ⟨Ω, hr, hs⟩ := match_vis P hLne hrel hGs hCs hAs hWs
    exact ⟨Ω, hr, composedHidden_of_event P e hs⟩
  cases e with
  | gbcaSend r j m =>
    obtain rfl : ν = PMF.pure o :=
      (System.mapIdle_step_none (coinLabelMap_gbcaSend r j m) ν).mp hWs
    obtain rfl : w' = w.recordGBCASend r j m := by
      simpa using pure_inj (networkStep_gbcaSend hn)
    have hcol : (G r).1 j = (processes j).2.roundRecord r := hst j r
    have hstage : ∃ nd : GBCA.ByABDY.RoundRecord P.n,
        GBCA.ByABDY.GBCAProgramStep P r j ((G r).1 j) (Sum.inr (GBCA.ByABDY.GBCAEvent.send j m))
          (PMF.pure nd) ∧
        x j = ((processes j).1, (processes j).2.setRoundRecord r nd) := by
      cases m with
      | input b =>
        obtain ⟨-, -, hin, hcnt, hsend, hxid⟩ := programStep_gbcaSend_input_self (hall j)
        exact ⟨_, GBCA.ByABDY.GBCAProgramStep.sendRelay _ b (by rw [hcol]; exact hin)
          (by rw [hcol]; exact hcnt) (by rw [hcol]; exact hsend),
          by rw [hcol]; exact pure_inj hxid⟩
      | echo b =>
        obtain ⟨-, -, hin, hcnt, hsend, hxid⟩ := programStep_gbcaSend_echo_self (hall j)
        exact ⟨_, GBCA.ByABDY.GBCAProgramStep.sendEcho _ b (by rw [hcol]; exact hin)
          (by rw [hcol]; exact hcnt) (by rw [hcol]; exact hsend),
          by rw [hcol]; exact pure_inj hxid⟩
      | vote v =>
        cases v with
        | some b =>
          obtain ⟨-, -, hin, hcnt, hsend, hxid⟩ := programStep_gbcaSend_voteBit_self (hall j)
          exact ⟨_, GBCA.ByABDY.GBCAProgramStep.sendVoteBit _ b (by rw [hcol]; exact hin)
            (by rw [hcol]; exact hcnt)
            (by rw [hcol]; exact hsend),
            by rw [hcol]; exact pure_inj hxid⟩
        | none =>
          obtain ⟨-, -, hin, hnot, hcnt, hval, hsend, hxid⟩ :=
            programStep_gbcaSend_voteBot_self (hall j)
          exact ⟨_, GBCA.ByABDY.GBCAProgramStep.sendVoteBot _ (by rw [hcol]; exact hin)
            (by rw [hcol]; exact hnot)
            (by rw [hcol]; exact hcnt) (by rw [hcol]; exact hval)
            (by rw [hcol]; exact hsend),
            by rw [hcol]; exact pure_inj hxid⟩
      | bind v =>
        cases v with
        | some b =>
          obtain ⟨-, -, hin, hlv, hcnt, hsend, hxid⟩ := programStep_gbcaSend_bindBit_self (hall j)
          exact ⟨_, GBCA.ByABDY.GBCAProgramStep.sendBindBit _ b (by rw [hcol]; exact hin)
            (by rw [hcol]; exact hlv) (by rw [hcol]; exact hcnt)
            (by rw [hcol]; exact hsend),
            by rw [hcol]; exact pure_inj hxid⟩
        | none =>
          obtain ⟨-, -, hin, hlv, hnot, hcnt, hval, hsend, hxid⟩ :=
            programStep_gbcaSend_bindBot_self (hall j)
          exact ⟨_, GBCA.ByABDY.GBCAProgramStep.sendBindBot _ (by rw [hcol]; exact hin)
            (by rw [hcol]; exact hlv) (by rw [hcol]; exact hnot)
            (by rw [hcol]; exact hcnt) (by rw [hcol]; exact hval)
            (by rw [hcol]; exact hsend),
            by rw [hcol]; exact pure_inj hxid⟩
      | «echo5» v =>
        cases v with
        | some b =>
          obtain ⟨-, -, hin, hlv, hcnt, hsend, hxid⟩ := programStep_gbcaSend_echo5Bit_self (hall j)
          exact ⟨_, GBCA.ByABDY.GBCAProgramStep.sendEcho5Bit _ b (by rw [hcol]; exact hin)
            (by rw [hcol]; exact hlv) (by rw [hcol]; exact hcnt)
            (by rw [hcol]; exact hsend),
            by rw [hcol]; exact pure_inj hxid⟩
        | none =>
          obtain ⟨-, -, hin, hlv, hnot, hcnt, hval, hsend, hxid⟩ :=
            programStep_gbcaSend_echo5Bot_self (hall j)
          exact ⟨_, GBCA.ByABDY.GBCAProgramStep.sendEcho5Bot _ (by rw [hcol]; exact hin)
            (by rw [hcol]; exact hlv) (by rw [hcol]; exact hnot)
            (by rw [hcol]; exact hcnt) (by rw [hcol]; exact hval)
            (by rw [hcol]; exact hsend),
            by rw [hcol]; exact pure_inj hxid⟩
    obtain ⟨nd, hrow, hx⟩ := hstage
    have hfor : ∀ i, i ≠ j → x i = processes i := fun i hi =>
      pure_inj (programStep_gbcaSend_foreign (Ne.symm hi) (hall i))
    have hGfor : ∀ i r', i ≠ j →
        ((Function.update G r
          (Function.update ((G r).1) j nd, ((G r).2).recordGBCASend j m)) r').1 i =
            (G r').1 i := by
      intro i r' hi
      by_cases hr' : r' = r
      · subst hr'; rw [Function.update_self]; exact Function.update_of_ne hi _ _
      · rw [Function.update_of_ne hr']
    have hown : ∀ r', ((Function.update G r
        (Function.update ((G r).1) j nd, ((G r).2).recordGBCASend j m)) r').1 j =
          (x j).2.roundRecord r' := by
      intro r'
      simp only [hx]
      by_cases hr' : r' = r
      · subst hr'; simp
      · rw [Function.update_of_ne hr', RoundRecordMap.roundRecord_setRoundRecord_ne _ _ _ hr']
        exact hst j r'
    have hxcore : ∀ i, (x i).1 = C i := by
      intro i
      by_cases hi : i = j
      · subst hi; rw [hx]; exact hC i
      · rw [hfor i hi]; exact hC i
    have h5 := rel_roundRecord P j hst hfor hGfor hown
    exact match_round P rfl ((protocolRelation_mk P _ _ _ _ _ _ _).mpr
      ⟨hxcore, rfl, by simpa using hA, rel_recordGBCASend hG r j m _, h5⟩)
      (GBCA.ByABDY.composition_event_step P r (GBCA.ByABDY.GBCAEvent.send j m)
        (gprocs_family j nd hrow
          (fun i hi => GBCA.ByABDY.GBCAProgramStep.sendIdle _ j m (Ne.symm hi)))
        (GBCA.ByABDY.GBCANetworkStep.send _ j m))
  | gbcaDeliver r i k m =>
    obtain rfl : ν = PMF.pure o :=
      (System.mapIdle_step_none (coinLabelMap_gbcaDeliver r i k m) ν).mp hWs
    obtain ⟨hmem, hw⟩ := networkStep_gbcaDeliver hn
    obtain rfl : w' = w := by
      simpa using pure_inj hw
    obtain ⟨-, -, hxid⟩ := programStep_gbcaDeliver_self (hall i)
    have hcol : (G r).1 i = (processes i).2.roundRecord r := hst i r
    have hx : x i = ((processes i).1,
      (processes i).2.setRoundRecord r (((G r).1 i).deliverTo k m)) := by
        rw [hcol]; exact pure_inj hxid
    have hfor : ∀ i', i' ≠ i → x i' = processes i' := fun i' hi' =>
      pure_inj (programStep_gbcaDeliver_foreign (Ne.symm hi') (hall i'))
    have hGfor : ∀ i' r', i' ≠ i →
        ((Function.update G r
          (Function.update ((G r).1) i (((G r).1 i).deliverTo k m), (G r).2)) r').1 i' =
            (G r').1 i' := by
      intro i' r' hi'
      by_cases hr' : r' = r
      · subst hr'; rw [Function.update_self]; exact Function.update_of_ne hi' _ _
      · rw [Function.update_of_ne hr']
    have hown : ∀ r', ((Function.update G r
        (Function.update ((G r).1) i (((G r).1 i).deliverTo k m), (G r).2)) r').1 i =
          (x i).2.roundRecord r' := by
      intro r'
      simp only [hx]
      by_cases hr' : r' = r
      · subst hr'; simp
      · rw [Function.update_of_ne hr', RoundRecordMap.roundRecord_setRoundRecord_ne _ _ _ hr']
        exact hst i r'
    have hxcore : ∀ i', (x i').1 = C i' := by
      intro i'
      by_cases hi' : i' = i
      · subst hi'; rw [hx]; exact hC i'
      · rw [hfor i' hi']; exact hC i'
    have h5 := rel_roundRecord P i hst hfor hGfor hown
    exact match_round P rfl ((protocolRelation_mk P _ _ _ _ _ _ _).mpr
      ⟨hxcore, rfl, hA, fun r' => by rw [update_snd G r _ r']; exact hG r', h5⟩)
      (GBCA.ByABDY.composition_event_step P r (GBCA.ByABDY.GBCAEvent.deliver i k m)
        (gprocs_family i _ (GBCA.ByABDY.GBCAProgramStep.deliverReceive _ k m)
          (fun i' hi' => GBCA.ByABDY.GBCAProgramStep.deliverIdle _ i k m (Ne.symm hi')))
        (GBCA.ByABDY.GBCANetworkStep.deliver _ i k m (by rw [hG r]; exact hmem)))
  | decidedSend j b =>
    obtain ⟨hdp, hw⟩ := networkStep_decidedSend hn
    obtain rfl : w' = w.recordDecided j b := pure_inj hw
    have hx : ∀ i, x i = processes i := by
      intro i
      by_cases hi : i = j
      · subst hi
        rcases programStep_decidedSend_self (hall i) with ⟨-, -, -, hdx⟩ | ⟨-, hdx⟩ <;>
          exact pure_inj hdx
      · exact pure_inj (programStep_decidedSend_foreign (Ne.symm hi) (hall i))
    have h5 := rel_none P (G' := G) hst hx (fun _ _ => rfl)
    refine hvis (A' := A.recordDecided j b) (fun o' _ => (protocolRelation_mk P _ _ _ _ _ _ _).mpr
      ⟨fun _ => rfl, rfl, by rw [hA]; simp [ABANetworkState.recordDecided,
        NetworkState.recordDecided], fun r => by rw [hG r]; simp [NetworkState.recordDecided], h5⟩)
      (gbcaInstanceFamily_idle P G hLne (by simp) not_false) (fun i => ?_)
      (ABANetworkStep.decidedSend A j b (by rw [hA]; exact hdp))
    rw [hCeq i, hx i]
    by_cases hi : i = j
    · subst hi
      rcases programStep_decidedSend_self (hall i) with ⟨hh, -, hdcnt, -⟩ | ⟨hh, -⟩
      · exact RoundLoopStep.decidedSendRelay _ b hh hdcnt
      · exact RoundLoopStep.corruptedIdle _ _ hh (by simp) not_false
    · exact RoundLoopStep.decidedSendIdle _ j b (Ne.symm hi)
  | decidedDeliver i k b =>
    obtain ⟨hdp, hw⟩ := networkStep_decidedDeliver hn
    obtain rfl : w' = w := pure_inj hw
    obtain ⟨hhd, hnotin, hxid⟩ := programStep_decidedDeliver_self (hall i)
    have hx : x i = ((processes i).1.receiveDecided k b, (processes i).2) := pure_inj hxid
    have hfor : ∀ i', i' ≠ i → x i' = processes i' := fun i' hi' =>
      pure_inj (programStep_decidedDeliver_foreign (Ne.symm hi') (hall i'))
    have hown : ∀ r, (G r).1 i = (x i).2.roundRecord r := by
      intro r; simp only [hx]; exact hst i r
    have h5 := rel_roundRecord P i hst hfor (fun _ _ _ => rfl) hown
    refine hvis (A' := A) (fun o' _ => (protocolRelation_mk P _ _ _ _ _ _ _).mpr
      ⟨fun _ => rfl, rfl, hA, hG, h5⟩)
      (gbcaInstanceFamily_idle P G hLne (by simp) not_false) (fun i' => ?_)
      (ABANetworkStep.decidedDeliver A i k b (by rw [hA]; exact hdp))
    by_cases hi' : i' = i
    · subst hi'; rw [hCeq i', hx]; exact RoundLoopStep.decidedDeliverReceive _ k b hhd hnotin
    · rw [hCeq i', hfor i' hi']; exact RoundLoopStep.decidedDeliverIdle _ i k b (Ne.symm hi')
  | retWPublish r id co b =>
    obtain rfl : w' = w.recordDecided id b := by
      simpa using pure_inj (networkStep_retWPublish hn)
    obtain ⟨hh, hph, hrr, hgr, hxid⟩ := programStep_retWPublish_self (hall id)
    have hx : x id = ((processes id).1.stepRound co, (processes id).2) := pure_inj hxid
    have hfor : ∀ i, i ≠ id → x i = processes i := fun i hi =>
      pure_inj (programStep_retWPublish_foreign (Ne.symm hi) (hall i))
    have hown : ∀ r, (G r).1 id = (x id).2.roundRecord r := by
      intro r; simp only [hx]; exact hst id r
    have h5 := rel_roundRecord P id hst hfor (fun _ _ _ => rfl) hown
    refine hvis (A' := A.recordDecided id b) (fun o' _ => (protocolRelation_mk P _ _ _ _ _ _ _).mpr
      ⟨fun _ => rfl, rfl, by rw [hA]; simp [ABANetworkState.recordDecided,
        NetworkState.recordDecided], fun r' => by rw [hG r']; simp [NetworkState.recordDecided],
          h5⟩)
      (gbcaInstanceFamily_idle P G hLne (by simp) not_false) (fun i => ?_)
      (ABANetworkStep.retWPublish A r id co b)
    by_cases hi : i = id
    · subst hi; rw [hCeq i, hx]; exact RoundLoopStep.retWPublish _ r co b hh hph hrr hgr
    · rw [hCeq i, hfor i hi]
      exact RoundLoopStep.retWPublishIdle _ r id co b (Ne.symm hi)
  | gbcaCallLoop r id b =>
    obtain rfl : w' = w := by
      simpa using pure_inj (networkStep_gbcaCallLoop hn)
    obtain ⟨hh, hph, hrr, hest, -, hxid⟩ := programStep_gbcaCallLoop_self (hall id)
    have hx : x id = ((processes id).1.setProcess { (processes id).1.process with phase := .awaitG
      },
      (processes id).2) := pure_inj hxid
    have hfor : ∀ i, i ≠ id → x i = processes i := fun i hi =>
      pure_inj (programStep_gbcaCallLoop_foreign (Ne.symm hi) (hall i))
    have hown : ∀ r, (G r).1 id = (x id).2.roundRecord r := by
      intro r; simp only [hx]; exact hst id r
    have h5 := rel_roundRecord P id hst hfor (fun _ _ _ => rfl) hown
    refine hvis (A' := A) (fun o' _ => (protocolRelation_mk P _ _ _ _ _ _ _).mpr
      ⟨fun _ => rfl, rfl, hA, hG, h5⟩)
      (gbcaInstanceFamily_owned_id P G r (by simp)
        (GBCA.ByABDY.composition_label_step P r (by simp)
          (fun i => GBCA.ByABDY.GBCAProgramStep.callLoop _ id b)
          (GBCA.ByABDY.GBCANetworkStep.gbcaCallLoop _ id b))) (fun i => ?_)
      (ABANetworkStep.gbcaCallLoop A r id b)
    by_cases hi : i = id
    · subst hi; rw [hCeq i, hx]; exact RoundLoopStep.gbcaCallLoop _ r b hh hph hrr hest
    · rw [hCeq i, hfor i hi]
      exact RoundLoopStep.gbcaCallLoopIdle _ r id b (Ne.symm hi)
  | byzantineCallG r k b => exact (programStep_byzantineCallG_noStep (hall k)).elim
  | byzantineRetG r k out => exact (programStep_byzantineRetG_noStep (hall k)).elim
  | byzantineCallGLoop r k b =>
    obtain ⟨hF, hw⟩ := networkStep_byzantineCallGLoop hn
    obtain rfl : w' = w := by
      simpa using pure_inj hw
    have hx : ∀ i, x i = processes i := fun i => pure_inj (programStep_byzantineCallGLoop (hall i))
    have h5 := rel_none P (G' := G) hst hx (fun _ _ => rfl)
    refine hvis (A' := A) (fun o' _ => (protocolRelation_mk P _ _ _ _ _ _ _).mpr
      ⟨fun _ => rfl, rfl, hA, hG, h5⟩)
      (gbcaInstanceFamily_owned_id P G r (by simp)
        (GBCA.ByABDY.composition_label_step P r (by simp)
          (fun i => GBCA.ByABDY.GBCAProgramStep.byzantineCallLoop _ k b)
          (GBCA.ByABDY.GBCANetworkStep.byzantineCallGLoop _ k b))) (fun i => ?_)
      (ABANetworkStep.byzantineCallGLoop A r k b (by rw [hA]; exact hF))
    rw [hCeq i, hx i]; exact RoundLoopStep.byzantineCallGLoopIdle _ r k b
  | byzantineCallW r k =>
    obtain ⟨hF, hw⟩ := networkStep_byzantineCallW hn
    obtain rfl : w' = w := by
      simpa using pure_inj hw
    have hx : ∀ i, x i = processes i := fun i => pure_inj (programStep_byzantineCallW (hall i))
    have h5 := rel_none P (G' := G) hst hx (fun _ _ => rfl)
    refine hvis (A' := A) (fun o' _ => (protocolRelation_mk P _ _ _ _ _ _ _).mpr
      ⟨fun _ => rfl, rfl, hA, hG, h5⟩)
      (gbcaInstanceFamily_idle P G hLne (by simp) not_false) (fun i => ?_)
      (ABANetworkStep.byzantineCallW A r k (by rw [hA]; exact hF))
    rw [hCeq i, hx i]; exact RoundLoopStep.byzantineCallWIdle _ r k
  | byzantineRetW r k b =>
    obtain ⟨hF, hw⟩ := networkStep_byzantineRetW hn
    obtain rfl : w' = w := by
      simpa using pure_inj hw
    have hx : ∀ i, x i = processes i := fun i => pure_inj (programStep_byzantineRetW (hall i))
    have h5 := rel_none P (G' := G) hst hx (fun _ _ => rfl)
    refine hvis (A' := A) (fun o' _ => (protocolRelation_mk P _ _ _ _ _ _ _).mpr
      ⟨fun _ => rfl, rfl, hA, hG, h5⟩)
      (gbcaInstanceFamily_idle P G hLne (by simp) not_false) (fun i => ?_)
      (ABANetworkStep.byzantineRetW A r k b (by rw [hA]; exact hF))
    rw [hCeq i, hx i]; exact RoundLoopStep.byzantineRetWIdle _ r k b

/-- The matching on a visible shared label. -/
theorem match_label (P : Parameters) {processes : ∀ _ : Fin P.n, ProcessRecord P.n}
    {w : NetworkState P.n} {o : ℕ → WCC.SpecState P.n}
    {G : ℕ → GBCA.ByABDY.ImplementationState P.n} {C : ∀ _ : Fin P.n, RoundLoopRecord P.n}
    {A : ABANetworkState P.n} (hR : ProtocolRelation P (processes, w, o) (G, C, A, o))
    {l : Label P.n} (hl : l ≠ Label.tau) {μ : PMF (ProtocolState P)}
    (h : (protocolExtended P).step (processes, w, o) (Sum.inl l) μ) :
    ∃ Ω : PMF (PMF (ComposedState P)),
      PMFRel (diracRel (ProtocolRelation P)) μ Ω ∧
      (composedHidden P).step (G, C, A, o) l (Ω.bind id) := by
  obtain ⟨hC, -, hA, hG, hst⟩ := (protocolRelation_mk P _ _ _ _ _ _ _).mp hR
  have hCeq : ∀ i, C i = (processes i).1 := fun i => (hC i).symm
  obtain ⟨x, w', ω, hall, hn, hOr, rfl⟩ := protocolExtended_label_inv P hl h
  have hWl : (coinOverRoundAlphabet P).step o (Sum.inl l) ω :=
    (System.mapIdle_step_some (coinLabelMap_inl l) ω).mpr hOr
  have hLne : (Sum.inl l : ExtendedLabel P.n) ≠ Silent.τ := by
    simpa using hl
  suffices hsuf : ∃ Ω : PMF (PMF (ComposedState P)),
      PMFRel (diracRel (ProtocolRelation P))
        (prodPMF (PMF.pure x) (prodPMF (PMF.pure w') ω)) Ω ∧
      (composedExtended P).step (G, C, A, o) (Sum.inl l) (Ω.bind id) by
    obtain ⟨Ω, hr, hs⟩ := hsuf
    exact ⟨Ω, hr, (composedHidden_step_iff P _ _ _).mpr (Or.inr hs)⟩
  cases l with
  | tau => exact absurd rfl hl
  | callABA id b =>
    obtain rfl : w' = w := pure_inj (networkStep_callABA hn)
    have hfor : ∀ i, i ≠ id → x i = processes i := fun i hi =>
      pure_inj (programStep_callABA_foreign (Ne.symm hi) (hall i))
    have hGs : (GBCA.ByABDY.gbcaInstanceFamily P).step G (Sum.inl (Label.callABA id b)) (PMF.pure G)
      :=
      gbcaInstanceFamily_idle P G hLne (by simp) not_false
    rcases programStep_callABA_own (hall id) with ⟨hh, hin, hxid⟩ | ⟨hloop, hxid⟩
    · have hx : x id = ((processes id).1.setProcess { (processes id).1.process with
          input := some b, estimate := some b, round := 0, phase := .toCallG },
          (processes id).2) := pure_inj hxid
      have hown : ∀ r, (G r).1 id = (x id).2.roundRecord r := by
        intro r; simp only [hx]; exact hst id r
      have h5 := rel_roundRecord P id hst hfor (fun _ _ _ => rfl) hown
      refine match_vis P hLne (fun o' _ => (protocolRelation_mk P _ _ _ _ _ _ _).mpr
        ⟨fun _ => rfl, rfl, hA, hG, h5⟩) hGs (fun i => ?_)
        (ABANetworkStep.callABAIdle A id b) hWl
      by_cases hi : i = id
      · subst hi; rw [hCeq i, hx]; exact RoundLoopStep.input _ b hh hin
      · rw [hCeq i, hfor i hi]; exact RoundLoopStep.callABAIdle _ id b (Ne.symm hi)
    · have hx : ∀ i, x i = processes i := by
        intro i
        by_cases hi : i = id
        · subst hi; exact pure_inj hxid
        · exact hfor i hi
      have h5 := rel_none P (G' := G) hst hx (fun _ _ => rfl)
      refine match_vis P hLne (fun o' _ => (protocolRelation_mk P _ _ _ _ _ _ _).mpr
        ⟨fun _ => rfl, rfl, hA, hG, h5⟩) hGs (fun i => ?_)
        (ABANetworkStep.callABAIdle A id b) hWl
      rw [hCeq i, hx i]
      by_cases hi : i = id
      · subst hi
        by_cases hc : (processes i).1.corrupted = true
        · exact RoundLoopStep.corruptedIdle _ _ hc (by simp) not_false
        · exact RoundLoopStep.inputLoop _ b (by simpa using hc) (hloop.resolve_left hc)
      · exact RoundLoopStep.callABAIdle _ id b (Ne.symm hi)
  | retABA id b =>
    obtain ⟨hdp, hw⟩ := networkStep_retABA hn
    obtain rfl : w' = w := pure_inj hw
    have hfor : ∀ i, i ≠ id → x i = processes i := fun i hi =>
      pure_inj (programStep_retABA_foreign (Ne.symm hi) (hall i))
    have hGs : (GBCA.ByABDY.gbcaInstanceFamily P).step G (Sum.inl (Label.retABA id b)) (PMF.pure G)
      :=
      gbcaInstanceFamily_idle P G hLne (by simp) not_false
    have hAs : ABANetworkStep P A (Sum.inl (Label.retABA id b)) (PMF.pure A) := by
      rcases hdp with hd | hF
      · exact ABANetworkStep.retABA A id b (by rw [hA]; exact hd)
      · exact ABANetworkStep.retByzantine A id b (by rw [hA]; exact hF)
    rcases programStep_retABA_own (hall id) with ⟨hh, -, hcnt, hret, hxid⟩ | ⟨hh, hxid⟩
    · have hx : x id =
          ((processes id).1.setProcess { (processes id).1.process with returned := true },
            (processes id).2) := pure_inj hxid
      have hown : ∀ r, (G r).1 id = (x id).2.roundRecord r := by
        intro r; simp only [hx]; exact hst id r
      have h5 := rel_roundRecord P id hst hfor (fun _ _ _ => rfl) hown
      refine match_vis P hLne (fun o' _ => (protocolRelation_mk P _ _ _ _ _ _ _).mpr
        ⟨fun _ => rfl, rfl, hA, hG, h5⟩) hGs (fun i => ?_) hAs hWl
      by_cases hi : i = id
      · subst hi; rw [hCeq i, hx]; exact RoundLoopStep.ret _ b hh hcnt hret
      · rw [hCeq i, hfor i hi]; exact RoundLoopStep.retABAIdle _ id b (Ne.symm hi)
    · have hx : ∀ i, x i = processes i := by
        intro i
        by_cases hi : i = id
        · subst hi; exact pure_inj hxid
        · exact hfor i hi
      have h5 := rel_none P (G' := G) hst hx (fun _ _ => rfl)
      refine match_vis P hLne (fun o' _ => (protocolRelation_mk P _ _ _ _ _ _ _).mpr
        ⟨fun _ => rfl, rfl, hA, hG, h5⟩) hGs (fun i => ?_) hAs hWl
      rw [hCeq i, hx i]
      by_cases hi : i = id
      · subst hi; exact RoundLoopStep.corruptedIdle _ _ hh (by simp) not_false
      · exact RoundLoopStep.retABAIdle _ id b (Ne.symm hi)
  | callW r id =>
    obtain rfl : w' = w := pure_inj (networkStep_callW hn)
    have hfor : ∀ i, i ≠ id → x i = processes i := fun i hi =>
      pure_inj (programStep_callW_foreign (Ne.symm hi) (hall i))
    have hGs : (GBCA.ByABDY.gbcaInstanceFamily P).step G (Sum.inl (Label.callW r id)) (PMF.pure G)
      :=
      gbcaInstanceFamily_idle P G hLne (by simp) not_false
    rcases programStep_callW_own (hall id) with ⟨hh, hph, hrr, hxid⟩ | ⟨hh, hxid⟩
    · have hx : x id =
          ((processes id).1.setProcess { (processes id).1.process with phase := .awaitW },
            (processes id).2) := pure_inj hxid
      have hown : ∀ r, (G r).1 id = (x id).2.roundRecord r := by
        intro r; simp only [hx]; exact hst id r
      have h5 := rel_roundRecord P id hst hfor (fun _ _ _ => rfl) hown
      refine match_vis P hLne (fun o' _ => (protocolRelation_mk P _ _ _ _ _ _ _).mpr
        ⟨fun _ => rfl, rfl, hA, hG, h5⟩) hGs (fun i => ?_)
        (ABANetworkStep.callWIdle A r id) hWl
      by_cases hi : i = id
      · subst hi; rw [hCeq i, hx]; exact RoundLoopStep.callW _ r hh hph hrr
      · rw [hCeq i, hfor i hi]; exact RoundLoopStep.callWIdle _ r id (Ne.symm hi)
    · have hx : ∀ i, x i = processes i := by
        intro i
        by_cases hi : i = id
        · subst hi; exact pure_inj hxid
        · exact hfor i hi
      have h5 := rel_none P (G' := G) hst hx (fun _ _ => rfl)
      refine match_vis P hLne (fun o' _ => (protocolRelation_mk P _ _ _ _ _ _ _).mpr
        ⟨fun _ => rfl, rfl, hA, hG, h5⟩) hGs (fun i => ?_)
        (ABANetworkStep.callWIdle A r id) hWl
      rw [hCeq i, hx i]
      by_cases hi : i = id
      · subst hi; exact RoundLoopStep.corruptedIdle _ _ hh (by simp) not_false
      · exact RoundLoopStep.callWIdle _ r id (Ne.symm hi)
  | retW r id co =>
    obtain rfl : w' = w := pure_inj (networkStep_retW hn)
    have hfor : ∀ i, i ≠ id → x i = processes i := fun i hi =>
      pure_inj (programStep_retW_foreign (Ne.symm hi) (hall i))
    have hGs : (GBCA.ByABDY.gbcaInstanceFamily P).step G (Sum.inl (Label.retW r id co)) (PMF.pure G)
      :=
      gbcaInstanceFamily_idle P G hLne (by simp) not_false
    rcases programStep_retW_own (hall id) with ⟨hh, hph, hrr, hgr, hxid⟩ | ⟨hh, hxid⟩
    · have hx : x id = ((processes id).1.stepRound co, (processes id).2) := pure_inj hxid
      have hown : ∀ r, (G r).1 id = (x id).2.roundRecord r := by
        intro r; simp only [hx]; exact hst id r
      have h5 := rel_roundRecord P id hst hfor (fun _ _ _ => rfl) hown
      refine match_vis P hLne (fun o' _ => (protocolRelation_mk P _ _ _ _ _ _ _).mpr
        ⟨fun _ => rfl, rfl, hA, hG, h5⟩) hGs (fun i => ?_)
        (ABANetworkStep.retWIdle A r id co) hWl
      by_cases hi : i = id
      · subst hi; rw [hCeq i, hx]; exact RoundLoopStep.retW _ r co hh hph hrr hgr
      · rw [hCeq i, hfor i hi]; exact RoundLoopStep.retWIdle _ r id co (Ne.symm hi)
    · have hx : ∀ i, x i = processes i := by
        intro i
        by_cases hi : i = id
        · subst hi; exact pure_inj hxid
        · exact hfor i hi
      have h5 := rel_none P (G' := G) hst hx (fun _ _ => rfl)
      refine match_vis P hLne (fun o' _ => (protocolRelation_mk P _ _ _ _ _ _ _).mpr
        ⟨fun _ => rfl, rfl, hA, hG, h5⟩) hGs (fun i => ?_)
        (ABANetworkStep.retWIdle A r id co) hWl
      rw [hCeq i, hx i]
      by_cases hi : i = id
      · subst hi; exact RoundLoopStep.corruptedIdle _ _ hh (by simp) not_false
      · exact RoundLoopStep.retWIdle _ r id co (Ne.symm hi)
  | fail k =>
    obtain ⟨hnew, hbud, hw⟩ := networkStep_fail hn
    obtain rfl : w' = NetworkState.corrupt P k w := pure_inj hw
    have hfor : ∀ i, i ≠ k → x i = processes i := fun i hi =>
      pure_inj (programStep_fail_foreign (Ne.symm hi) (hall i))
    have hstg : (x k).2 = (processes k).2 := by
      rcases programStep_fail_own (hall k) with ⟨-, hxk⟩ | ⟨-, hxk⟩ <;> rw [pure_inj hxk]
    have h5 := rel_roundRecord P k (G' := fun r =>
      GBCA.ByABDY.corruptionAct P (Sum.inl (Label.fail k)) (G r)) hst hfor
      (fun _ _ _ => by simp only [corruptionAct_fail])
      (fun r => by simp only [corruptionAct_fail]; rw [hstg]; exact hst k r)
    have hrel : ∀ o' : ℕ → WCC.SpecState P.n,
        ProtocolRelation P ((x, NetworkState.corrupt P k w, o') : ProtocolState P)
          (((fun r => GBCA.ByABDY.corruptionAct P (Sum.inl (Label.fail k)) (G r)),
            (fun i => (x i).1), ABANetworkState.corrupt P k A, o') : ComposedState P) := by
      intro o'
      refine (protocolRelation_mk P _ _ _ _ _ _ _).mpr ⟨fun _ => rfl, rfl, ?_, ?_, h5⟩
      · rw [hA]; exact corrupt_abaNetwork w k
      · intro r
        simp only [corruptionAct_fail]
        rw [hG r]
        exact corrupt_gbcaNetwork w k r
    refine match_vis P hLne (fun o' _ => hrel o') (gbcaInstanceFamily_fail P G k) (fun i => ?_)
      (ABANetworkStep.fail A k (by rw [hA]; exact hnew) (by rw [hA]; exact hbud)) hWl
    by_cases hi : i = k
    · subst hi
      rcases programStep_fail_own (hall i) with ⟨hh, hxk⟩ | ⟨hh, hxk⟩
      · rw [hCeq i, pure_inj hxk]; exact RoundLoopStep.failSelf _ hh
      · rw [hCeq i, pure_inj hxk]
        exact RoundLoopStep.corruptedIdle _ _ hh (by simp) not_false
    · rw [hCeq i, hfor i hi]; exact RoundLoopStep.failIdle _ k (Ne.symm hi)
  | callG r id b =>
    obtain rfl : w' = w.recordGBCASend r id (.input b) := by
      simpa [gbcaCallPayload] using pure_inj (networkStep_callG hn)
    have hfor : ∀ i, i ≠ id → x i = processes i := fun i hi =>
      pure_inj (programStep_callG_foreign (Ne.symm hi) (hall i))
    obtain ⟨hh, hph, hrr, -, hest, hin, hxid⟩ := programStep_callG_own (hall id)
    have hcol : (G r).1 id = (processes id).2.roundRecord r := hst id r
    have hx : x id = ((processes id).1.setProcess { (processes id).1.process with phase := .awaitG
      },
        (processes id).2.setRoundRecord r (((processes id).2.roundRecord r).setProcess
          { ((processes id).2.roundRecord r).process with
            input := some b,
            sentInput :=
              Function.update ((processes id).2.roundRecord r).process.sentInput b true })) :=
      pure_inj hxid
    have hGs : (GBCA.ByABDY.gbcaInstanceFamily P).step G (Sum.inl (Label.callG r id b))
        (PMF.pure (Function.update G r
          (Function.update ((G r).1) id (((G r).1 id).setProcess { ((G r).1 id).process with
            input := some b,
            sentInput := Function.update ((G r).1 id).process.sentInput b true }),
          ((G r).2).recordGBCASend id (.input b)))) :=
      gbcaInstanceFamily_owned P G r (by simp)
        (GBCA.ByABDY.composition_label_step P r (by simp)
          (gprocs_family id _
            (GBCA.ByABDY.GBCAProgramStep.call _ b (by rw [hcol]; exact hin))
            (fun i hi => GBCA.ByABDY.GBCAProgramStep.callIdle _ id b (Ne.symm hi)))
          (GBCA.ByABDY.GBCANetworkStep.callG _ id b))
    have hGfor : ∀ j r', j ≠ id →
        ((Function.update G r
          (Function.update ((G r).1) id (((G r).1 id).setProcess { ((G r).1 id).process with
            input := some b,
            sentInput := Function.update ((G r).1 id).process.sentInput b true }),
          ((G r).2).recordGBCASend id (.input b))) r').1 j = (G r').1 j := by
      intro j r' hj
      by_cases hr' : r' = r
      · subst hr'; rw [Function.update_self]; exact Function.update_of_ne hj _ _
      · rw [Function.update_of_ne hr']
    have hown : ∀ r', ((Function.update G r
        (Function.update ((G r).1) id (((G r).1 id).setProcess { ((G r).1 id).process with
          input := some b,
          sentInput := Function.update ((G r).1 id).process.sentInput b true }),
        ((G r).2).recordGBCASend id (.input b))) r').1 id = (x id).2.roundRecord r' := by
      intro r'
      simp only [hx]
      by_cases hr' : r' = r
      · subst hr'; simp [hcol]
      · rw [Function.update_of_ne hr', RoundRecordMap.roundRecord_setRoundRecord_ne _ _ _ hr']
        exact hst id r'
    have h5 := rel_roundRecord P id hst hfor hGfor hown
    refine match_vis P hLne (fun o' _ => (protocolRelation_mk P _ _ _ _ _ _ _).mpr
      ⟨fun _ => rfl, rfl, by simpa using hA, rel_recordGBCASend hG r id (.input b) _,
        h5⟩) hGs (fun i => ?_) (ABANetworkStep.callGIdle A r id b) hWl
    by_cases hi : i = id
    · subst hi; rw [hCeq i, hx]; exact RoundLoopStep.callG _ r b hh hph hrr hest
    · rw [hCeq i, hfor i hi]; exact RoundLoopStep.callGIdle _ r id b (Ne.symm hi)
  | retG r id out bnd =>
    obtain ⟨hbnd, hw⟩ := networkStep_retG hn
    obtain rfl :
        w' = w.writeGhost (abdyGhostStep P) (Sum.inl (Label.retG r id out bnd)) :=
      pure_inj hw
    have hfix : (w.ghostRecord r).getD bnd = bnd := ghostOut_getD hbnd
    have hfor : ∀ i, i ≠ id → x i = processes i := fun i hi =>
      pure_inj (programStep_retG_foreign (Ne.symm hi) (hall i))
    have hcol : (G r).1 id = (processes id).2.roundRecord r := hst id r
    have hbnd' : bnd = ((G r).2).bound.getD
        (GBCA.ByABDY.boundOf ((G r).2).sent ((G r).2).F out) := by
      rw [hG r]; exact hbnd
    have hstage : ∃ hph : (processes id).1.process.phase = Phase.awaitG,
        (processes id).1.process.round = r ∧ (processes id).1.corrupted = false ∧
        GBCA.ByABDY.GBCAProgramStep P r id ((G r).1 id) (Sum.inl (Sum.inl (Label.retG r id out
          bnd)))
          (PMF.pure (((G r).1 id).setProcess { ((G r).1 id).process with returned := true })) ∧
        x id = ((processes id).1.setProcess { (processes id).1.process with
          estimate := out.estimate, lastGrade := some out, phase := .toCallW },
          (processes id).2.setRoundRecord r (((processes id).2.roundRecord r).setProcess
            { ((processes id).2.roundRecord r).process with returned := true })) := by
      cases out with
      | A v =>
        obtain ⟨hh, hph, hrr, -, hin, hlv, hcnt, hret, hxid⟩ := programStep_retG_A_own (hall id)
        exact ⟨hph, hrr, hh, GBCA.ByABDY.GBCAProgramStep.retA _ v bnd (by rw [hcol]; exact hin)
          (by rw [hcol]; exact hlv) (by rw [hcol]; exact hcnt)
          (by rw [hcol]; exact hret), pure_inj hxid⟩
      | B v =>
        obtain ⟨hh, hph, hrr, -, hin, hlv, hnotA, hcnt, honce, hbind, hval, hret,
          hxid⟩ := programStep_retG_B_own (hall id)
        exact ⟨hph, hrr, hh, GBCA.ByABDY.GBCAProgramStep.retB _ v bnd (by rw [hcol]; exact hin)
          (by rw [hcol]; exact hlv) (by rw [hcol]; exact hnotA)
          (by rw [hcol]; exact hcnt) (by rw [hcol]; exact honce)
          (by rw [hcol]; exact hbind)
          (by rw [hcol]; exact hval) (by rw [hcol]; exact hret),
          pure_inj hxid⟩
      | C =>
        obtain ⟨hh, hph, hrr, -, hin, hlv, hnotA, hnotB, hcnt, hval, hret, hxid⟩ :=
          programStep_retG_C_own (hall id)
        exact ⟨hph, hrr, hh, GBCA.ByABDY.GBCAProgramStep.retC _ bnd (by rw [hcol]; exact hin)
          (by rw [hcol]; exact hlv) (by rw [hcol]; exact hnotA)
          (by rw [hcol]; exact hnotB) (by rw [hcol]; exact hcnt)
          (by rw [hcol]; exact hval) (by rw [hcol]; exact hret),
          pure_inj hxid⟩
    obtain ⟨hph, hrr, hh, hrow, hx⟩ := hstage
    have hGs : (GBCA.ByABDY.gbcaInstanceFamily P).step G (Sum.inl (Label.retG r id out bnd))
        (PMF.pure (Function.update G r
          (Function.update ((G r).1) id
            (((G r).1 id).setProcess { ((G r).1 id).process with returned := true }),
          ((G r).2).setBound bnd))) :=
      gbcaInstanceFamily_owned P G r (by simp)
        (GBCA.ByABDY.composition_label_step P r (by simp)
          (gprocs_family id _ hrow
            (fun i hi => GBCA.ByABDY.GBCAProgramStep.retIdle _ id out bnd (Ne.symm hi)))
          (GBCA.ByABDY.GBCANetworkStep.retGIdle _ id out bnd hbnd'))
    have hGfor : ∀ j r', j ≠ id →
        ((Function.update G r
          (Function.update ((G r).1) id
            (((G r).1 id).setProcess { ((G r).1 id).process with returned := true }),
          ((G r).2).setBound bnd)) r').1 j = (G r').1 j := by
      intro j r' hj
      by_cases hr' : r' = r
      · subst hr'; rw [Function.update_self]; exact Function.update_of_ne hj _ _
      · rw [Function.update_of_ne hr']
    have hown : ∀ r', ((Function.update G r
        (Function.update ((G r).1) id
          (((G r).1 id).setProcess { ((G r).1 id).process with returned := true }),
        ((G r).2).setBound bnd)) r').1 id = (x id).2.roundRecord r' := by
      intro r'
      simp only [hx]
      by_cases hr' : r' = r
      · subst hr'; simp [hcol]
      · rw [Function.update_of_ne hr', RoundRecordMap.roundRecord_setRoundRecord_ne _ _ _ hr']
        exact hst id r'
    have h5 := rel_roundRecord P id hst hfor hGfor hown
    refine match_vis P hLne (fun o' _ => (protocolRelation_mk P _ _ _ _ _ _ _).mpr
      ⟨fun _ => rfl, rfl, by simpa using hA,
        rel_setBound hG r bnd _ hfix (by simp) (fun r' hr' =>
          writeGhost_retG_ne P w r id out bnd hr'), h5⟩) hGs (fun i => ?_)
      (ABANetworkStep.retGIdle A r id out bnd) hWl
    by_cases hi : i = id
    · subst hi; rw [hCeq i, hx]; exact RoundLoopStep.retG _ r out bnd hh hph hrr
    · rw [hCeq i, hfor i hi]
      exact RoundLoopStep.retGIdle _ r id out bnd (Ne.symm hi)

/-- The matching on the silent label. The protocol's own `terminate` row writes
no coordinate the relation reads, so the composed answer to it is to stand
still; the adversary's two injections are answered by a transition. -/
theorem match_tau (P : Parameters) {processes : ∀ _ : Fin P.n, ProcessRecord P.n}
    {w : NetworkState P.n} {o : ℕ → WCC.SpecState P.n}
    {G : ℕ → GBCA.ByABDY.ImplementationState P.n} {C : ∀ _ : Fin P.n, RoundLoopRecord P.n}
    {A : ABANetworkState P.n} (hR : ProtocolRelation P (processes, w, o) (G, C, A, o))
    {μ : PMF (ProtocolState P)}
    (h : (protocolExtended P).step (processes, w, o) (Sum.inl Label.tau) μ) :
    ∃ Ω : PMF (PMF (ComposedState P)),
      PMFRel (diracRel (ProtocolRelation P)) μ Ω ∧
      ((composedHidden P).step (G, C, A, o) Label.tau (Ω.bind id) ∨
        Ω.bind id = PMF.pure (G, C, A, o)) := by
  obtain ⟨hC, -, hA, hG, hst⟩ := (protocolRelation_mk P _ _ _ _ _ _ _).mp hR
  rcases protocolExtended_tau_inv P h with ⟨i, y, hy, rfl⟩ | ⟨w', hn, rfl⟩
  · obtain ⟨-, -, -, -, -, hyeq⟩ := programStep_tau_terminate hy
    obtain rfl : y = ((processes i).1, { (processes i).2 with terminated := true }) :=
      pure_inj hyeq
    have hrel' : ProtocolRelation P
        ((Function.update processes i ((processes i).1,
          { (processes i).2 with terminated := true }), w, o) : ProtocolState P)
        ((G, C, A, o) : ComposedState P) := by
      refine (protocolRelation_mk P _ _ _ _ _ _ _).mpr ⟨fun j => ?_, rfl, hA, hG, fun j r => ?_⟩
      · by_cases hj : j = i
        · subst hj; rw [Function.update_self]; exact hC j
        · rw [Function.update_of_ne hj]; exact hC j
      · by_cases hj : j = i
        · subst hj; rw [Function.update_self]; exact hst j r
        · rw [Function.update_of_ne hj]; exact hst j r
    obtain ⟨Ω, hrel, hbind⟩ := match_pure P hrel'
    exact ⟨Ω, hrel, Or.inr hbind⟩
  · rcases networkStep_tau hn with ⟨r, k, m, hF, hw⟩ | ⟨k, b, hF, hw⟩
    · obtain rfl : w' = w.recordGBCASend r k m := pure_inj hw
      have hFG : k ∈ ((G r).2).F := by
        rw [hG r]; exact hF
      have hfst := update_fst G r (X := ((G r).1, ((G r).2).recordGBCASend k m)) rfl
      have hrel' : ProtocolRelation P ((processes, w.recordGBCASend r k m, o) : ProtocolState P)
          ((Function.update G r ((G r).1, ((G r).2).recordGBCASend k m), C, A, o) :
            ComposedState P) := by
        refine (protocolRelation_mk P _ _ _ _ _ _ _).mpr
          ⟨hC, rfl, by simpa using hA, ?_, ?_⟩
        · intro r'
          by_cases hr : r' = r
          · subst hr
            rw [Function.update_self]
            change ((G r').2).recordGBCASend k m = _
            rw [hG r']
            simp [GBCA.ByABDY.NetworkState.recordGBCASend]
          · rw [Function.update_of_ne hr, hG r', recordGBCASend_sent_ne w r k m hr]
            simp
        · intro j r'; rw [hfst]; exact hst j r'
      obtain ⟨Ω, hrel, hbind⟩ := match_pure P hrel'
      refine ⟨Ω, hrel, Or.inl ?_⟩
      rw [hbind]
      exact composedHidden_of_tau P (composedExtended_tau_gbca P (gbcaInstanceFamily_tau P G r
        (GBCA.ByABDY.composition_tau_network P r (GBCA.ByABDY.GBCANetworkStep.byzantineGBCA _ k m
          hFG))))
    · obtain rfl : w' = w.recordDecided k b := pure_inj hw
      have hFA : k ∈ A.F := by
        rw [hA]; exact hF
      have hrel' : ProtocolRelation P ((processes, w.recordDecided k b, o) : ProtocolState P)
          ((G, C, A.recordDecided k b, o) : ComposedState P) := by
        refine (protocolRelation_mk P _ _ _ _ _ _ _).mpr ⟨hC, rfl, ?_, ?_, hst⟩
        · rw [hA]; simp [ABANetworkState.recordDecided, NetworkState.recordDecided]
        · intro r; rw [hG r]; simp [NetworkState.recordDecided]
      obtain ⟨Ω, hrel, hbind⟩ := match_pure P hrel'
      refine ⟨Ω, hrel, Or.inl ?_⟩
      rw [hbind]
      exact composedHidden_of_tau P (composedExtended_tau_ABANetwork P
        (ABANetworkStep.byzantineDecided A k b
        hFA))

/-! ### The simulation -/

/-- The matching at the group level: the rendezvous alphabet is hidden on both
sides, so a hidden protocol rendezvous is answered by a silent transition of
the composed group. The second disjunct is the composed answer to `terminate`:
the state stands still under a silent protocol label. -/
theorem match_hidden (P : Parameters) {u : ProtocolState P} {t : ComposedState P}
    (hR : ProtocolRelation P u t) {l : Label P.n} {μ : PMF (ProtocolState P)}
    (h : (protocolHidden P).step u l μ) :
    ∃ Ω : PMF (PMF (ComposedState P)),
      PMFRel (diracRel (ProtocolRelation P)) μ Ω ∧
        ((composedHidden P).step t l (Ω.bind id) ∨
          (l = Label.tau ∧ Ω.bind id = PMF.pure t)) := by
  obtain ⟨processes, w, o⟩ := u
  obtain ⟨G, C, A, o'⟩ := t
  obtain ⟨hC, ho, hA, hG, hst⟩ := (protocolRelation_mk P _ _ _ _ _ _ _).mp hR
  subst ho
  have hR : ProtocolRelation P (processes, w, o) (G, C, A, o) :=
    (protocolRelation_mk P _ _ _ _ _ _ _).mpr ⟨hC, rfl, hA, hG, hst⟩
  rcases (protocolHidden_step_iff P _ _ _).mp h with ⟨rfl, e, hstep⟩ | hstep
  · obtain ⟨Ω, hrel, hs⟩ := match_event P hR e hstep
    exact ⟨Ω, hrel, Or.inl hs⟩
  · by_cases hl : l = Label.tau
    · subst hl
      obtain ⟨Ω, hrel, hs⟩ := match_tau P hR hstep
      exact ⟨Ω, hrel, hs.imp id (fun hp => ⟨rfl, hp⟩)⟩
    · obtain ⟨Ω, hrel, hs⟩ := match_label P hR hl hstep
      exact ⟨Ω, hrel, Or.inl hs⟩

/-- The matching at the system level: a hidden sub-protocol label is silent on
both sides, and every other label is answered on the nose or by standing
still. A hidden label is never `τ`, so the standing-still answer arises only
under `τ`, where the reflexivity of `weakTau` discharges it. -/
theorem match_step (P : Parameters) {u : ProtocolState P} {t : ComposedState P}
    (hR : ProtocolRelation P u t) {l : Label P.n} {μ : PMF (ProtocolState P)}
    (h : (protocol P).step u l μ) :
    ∃ Ω : PMF (PMF (ComposedState P)),
      PMFRel (diracRel (ProtocolRelation P)) μ Ω ∧
        ((l = Silent.τ ∧ weakTau (composed P) (PMF.pure t) (Ω.bind id)) ∨
         (¬ (l = Silent.τ) ∧ weakStep (composed P) (PMF.pure t) l (Ω.bind id))) := by
  rcases (protocol_step_iff P u l μ).mp h with ⟨rfl, l', hmem, hg⟩ | ⟨hnm, hg⟩
  · obtain ⟨Ω, hrel, hlay⟩ := match_hidden P hR hg
    rcases hlay with hlay | ⟨rfl, -⟩
    · exact ⟨Ω, hrel, Or.inl ⟨rfl, weakTau_of_step rfl
        ((System.abstract_step _ _ _ _ _).mpr (Or.inl ⟨rfl, l', hmem, hlay⟩))⟩⟩
    · exact absurd hmem Label.tau_not_mem_hiddenAPI
  · obtain ⟨Ω, hrel, hlay⟩ := match_hidden P hR hg
    rcases hlay with hlay | ⟨rfl, hpure⟩
    · have hstep : (composed P).step t l (Ω.bind id) :=
        (System.abstract_step _ _ _ _ _).mpr (Or.inr ⟨hnm, hlay⟩)
      by_cases hτ : l = Silent.τ
      · exact ⟨Ω, hrel, Or.inl ⟨hτ, weakTau_of_step hτ hstep⟩⟩
      · exact ⟨Ω, hrel, Or.inr ⟨hτ, weakStep_strong hstep⟩⟩
    · exact ⟨Ω, hrel, Or.inl ⟨rfl, hpure ▸ weakTau_refl (composed P) (PMF.pure t)⟩⟩

/-- The two initial states are related: everything is initial, so every column
is the initial stage record, which is what an untouched round reads as on the
protocol side. -/
theorem protocolRelation_init (P : Parameters) :
    ProtocolRelation P (protocol P).init (composed P).init :=
  ⟨fun _ => rfl, rfl, rfl, fun _ => rfl,
    fun _ r => (RoundRecordMap.initial_roundRecord P.n r).symm⟩

/-- **The protocol forward-simulates into its composed reading**
along the Dirac lift of `ProtocolRelation`. -/
theorem protocolSim (P : Parameters) :
    ProbabilisticForwardSimulation (protocol P) (composed P)
      (diracRel (ProtocolRelation P)) where
  init := ⟨PMF.pure (composed P).init,
    fun _ hs => by rwa [PMF.mem_support_pure_iff] at hs,
    (composed P).init, rfl, protocolRelation_init P⟩
  step := by
    rintro s_C μ_A ⟨t, rfl, hR⟩ l μ_C hstep
    exact match_step P hR hstep

/-- **The composition inclusion**: every trace distribution the protocol
achieves is achieved by its composed reading. -/
theorem protocol_composed (P : Parameters) :
    achievableTraceDists (protocol P) ⊆ achievableTraceDists (composed P) :=
  (protocolSim P).achievableTraceDists_subset

/-! ### Mechanical axiom check

The composition step of the chain may not acquire a `sorryAx` dependence. -/

/-- info: 'PLTS.ABA.ABDY.protocol_composed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms protocol_composed

end ABDY

end ABA
end PLTS
