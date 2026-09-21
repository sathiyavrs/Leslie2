/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sathiya / Claude
-/

import Leslie2Protocols.ABA.Implementation.System
import Leslie2Protocols.Framework.Erasure

/-!
# Erasing a flat reading's ghost

The network adversary of a flat reading holds one record no program reads: the ghost
record `NetworkState.ghostRecord` of every round, written by `ghostStep` and read out by
`ghostOut` at the two graded-agreement returns. That read decides the bit a return
announces and not whether the return fires: the hypothesis `ghostOut_total` below asks it
to admit a bit at every state. This file erases it.

The reading it is erased to is `systemGhostFree`, the reading over the trivial ghost `Unit` whose
`ghostOut` is the full relation: the same programs, the same network rows, and a
graded-agreement return free to announce either bit. The erasure is a `StateErasure`
(`Framework/Erasure.lean`) along the projection

  `π = Prod.map id (Prod.map NetworkState.forgetGhost id)`

and the label identification `φ = Sum.map forgetBound id`, which sends a
graded-agreement return to the return of the same round, process and graded outcome with
the announced bit fixed at `false` and is the identity on every other label.

Two clauses carry the content. The projection is exact on labels: every row of the
adversary is a row of the ghost-free adversary at the erased state, on the same label,
because the ghost write leaves the erasure where it stands
(`NetworkState.forgetGhost_writeGhost`) and over `Unit` it is the identity
(`NetworkState.writeGhost_unit`). The lift is exact up to `φ`: a ghost-free return
announcing `bnd` is answered by the return announcing a bit the relation `ghostOut`
admits, which is what the hypothesis `ghostOut_total` supplies. Both algorithms satisfy
it, their `ghostOut` being an equation.

The pipeline of `Implementation/System.lean` carries the erasure from the adversary to the
reading. The three congruences of `Framework/Erasure.lean` ask the neighbours to be
saturated along `φ`: the process group is, because a program's return row takes the
announced bit free (`IsRoundRuleTable.boundBitFree`), and the coin oracle is, because a
graded-agreement return is foreign to every coin round. Hiding `Label.hiddenAPI` collapses
the erasure to the identity on labels, since every label `φ` identifies with a different
one is a graded-agreement return, and those are hidden. The conclusion `system_erasure` is
therefore an equality of achievable trace distributions, with no label map in the
statement.
-/

namespace PLTS
namespace ABA
namespace Implementation

/-! ### The ghost-free reading -/

section Free

variable (P : Parameters) (M S : Type) [DecidableEq M]
    (roundStep : Fin P.n → ProcessRecord P.n S → ExtendedLabel P.n M → PMF (ProcessRecord P.n S) →
      Prop)
    (callPayload : Fin P.n → Bool → M)

/-- The adversary of the ghost-free reading: the network's table over the trivial ghost,
its two graded-agreement returns free to announce either bit. -/
noncomputable def networkGhostFree : System (NetworkState P.n M Unit) (ExtendedLabel P.n M) :=
  network P M Unit callPayload (fun _ _ _ => ()) (fun _ _ _ _ _ => True)

/-- **The ghost-free reading**: the flat reading whose adversary holds no ghost record
and announces any bit on a graded-agreement return. -/
noncomputable def systemGhostFree : System (State P M S Unit) (Label P.n) :=
  system P M S Unit roundStep callPayload (fun _ _ _ => ()) (fun _ _ _ _ _ => True)

end Free

/-! ### The projection and the label identification -/

section Labels

variable {n : ℕ} {M : Type}

/-- The projection of a flat reading's state: the process family and the coin oracle
stand, and the adversary's ghost record is dropped. -/
def forgetGhostState {P : Parameters} {S G : Type} :
    State P M S G → State P M S Unit :=
  Prod.map id (Prod.map NetworkState.forgetGhost id)

/-- The label with the announced bound bit dropped on the rendezvous alphabet: a
Byzantine graded-agreement return keeps its round, the process it answers and its graded
outcome, and every other rendezvous label stands. -/
def forgetBoundEvent : NetworkEvent n M → NetworkEvent n M
  | .byzantineRetG r k out _ => .byzantineRetG r k out false
  | e => e

@[simp] theorem forgetBoundEvent_byzantineRetG (r : ℕ) (k : Fin n) (out : GBCAOutput)
    (bnd : Bool) :
    forgetBoundEvent (NetworkEvent.byzantineRetG (M := M) r k out bnd) = .byzantineRetG r k out
      false
      := rfl

/-- Two rendezvous labels agree under the erasure exactly when they are equal, or are
Byzantine graded-agreement returns of the same round, process and graded outcome. -/
theorem forgetBoundEvent_eq_iff (e e' : NetworkEvent n M) :
    forgetBoundEvent e = forgetBoundEvent e' ↔
      e = e' ∨ ∃ (r : ℕ) (k : Fin n) (out : GBCAOutput) (b b' : Bool),
        e = .byzantineRetG r k out b ∧ e' = .byzantineRetG r k out b' := by
  constructor
  · intro h
    cases e <;> cases e' <;> simp_all [forgetBoundEvent]
  · rintro (rfl | ⟨r, k, out, b, b', rfl, rfl⟩) <;> rfl

/-- The label identification of the erasure: the announced bound bit dropped on both
graded-agreement returns, every other label untouched. -/
abbrev forgetBoundExtended : ExtendedLabel n M → ExtendedLabel n M := Sum.map forgetBound
  forgetBoundEvent

/-- Two labels of the extended alphabet agree under the erasure exactly when they are
equal, or are graded-agreement returns — honest or Byzantine — of the same round,
process and graded outcome. -/
theorem forgetBoundExtended_eq_iff (l l' : ExtendedLabel n M) :
    forgetBoundExtended l = forgetBoundExtended l' ↔
      l = l' ∨
      (∃ (r : ℕ) (id : Fin n) (out : GBCAOutput) (b b' : Bool),
        l = Sum.inl (.retG r id out b) ∧ l' = Sum.inl (.retG r id out b')) ∨
      (∃ (r : ℕ) (k : Fin n) (out : GBCAOutput) (b b' : Bool),
        l = Sum.inr (.byzantineRetG r k out b) ∧ l' = Sum.inr (.byzantineRetG r k out b')) := by
  constructor
  · intro h
    match l, l' with
    | Sum.inl a, Sum.inl a' =>
      rcases (forgetBound_eq_iff a a').mp (Sum.inl_injective h) with
        rfl | ⟨r, id, out, b, b', rfl, rfl⟩
      · exact Or.inl rfl
      · exact Or.inr (Or.inl ⟨r, id, out, b, b', rfl, rfl⟩)
    | Sum.inl a, Sum.inr e => exact absurd h (by simp)
    | Sum.inr e, Sum.inl a => exact absurd h (by simp)
    | Sum.inr e, Sum.inr e' =>
      rcases (forgetBoundEvent_eq_iff e e').mp (Sum.inr_injective h) with
        rfl | ⟨r, k, out, b, b', rfl, rfl⟩
      · exact Or.inl rfl
      · exact Or.inr (Or.inr ⟨r, k, out, b, b', rfl, rfl⟩)
  · rintro (rfl | ⟨r, id, out, b, b', rfl, rfl⟩ | ⟨r, k, out, b, b', rfl, rfl⟩) <;>
      rfl

/-- The erasure separates the silent label: `τ` is a graded-agreement return of no
round. -/
theorem separatesSilent_forgetBoundExtended :
    SeparatesSilent (forgetBoundExtended (n := n) (M := M)) := by
  intro l hl
  rcases (forgetBoundExtended_eq_iff l (Silent.τ : ExtendedLabel n M)).mp hl with
    rfl | ⟨r, id, out, b, b', -, hτ⟩ | ⟨r, k, out, b, b', -, hτ⟩
  · rfl
  · exact absurd hτ (by simp)
  · exact absurd hτ (by simp)

/-- The rendezvous alphabet is saturated along the erasure: the identification keeps a
label in its summand. -/
theorem networkEventLabels_forgetBoundExtended (l l' : ExtendedLabel n M)
    (h : forgetBoundExtended l = forgetBoundExtended l') :
    l ∈ networkEventLabels (M := M) n ↔ l' ∈ networkEventLabels (M := M) n := by
  match l, l' with
  | Sum.inl a, Sum.inl a' => simp
  | Sum.inl a, Sum.inr e => exact absurd h (by simp)
  | Sum.inr e, Sum.inl a => exact absurd h (by simp)
  | Sum.inr e, Sum.inr e' => simp
/-- The sub-protocol API is saturated along the erasure. -/
theorem hiddenAPI_forgetBound (l l' : Label n) (h : forgetBound l = forgetBound l') :
    l ∈ Label.hiddenAPI n ↔ l' ∈ Label.hiddenAPI n := by
  rw [← forgetBound_mem_hiddenAPI l, ← forgetBound_mem_hiddenAPI l', h]

/-- Every discrepancy of the erasure lies in the sub-protocol API: two distinct labels
with the same image are graded-agreement returns, and those are hidden. -/
theorem hiddenAPI_of_forgetBound_ne (l l' : Label n) (h : forgetBound l = forgetBound l')
    (hne : l ≠ l') : l ∈ Label.hiddenAPI n := by
  rcases (forgetBound_eq_iff l l').mp h with rfl | ⟨r, id, out, b, b', rfl, -⟩
  · exact absurd rfl hne
  · simp

end Labels

/-! ### The adversary's erasure

The network adversary is the one component whose state carries the ghost, and the two
graded-agreement returns are the one pair of rows that read it. -/

section NetErasure

variable {P : Parameters} {M G : Type} [DecidableEq M] [Inhabited G]
    {callPayload : Fin P.n → Bool → M}
    {ghostStep : ExtendedLabel P.n M → NetworkState P.n M G → G → G}
    {ghostOut : NetworkState P.n M G → ℕ → Fin P.n → GBCAOutput → Bool → Prop}

/-- Over the trivial ghost a row's successor is the state its write starts from, so a
row written with its ghost write is a row written without it. -/
private theorem networkStep₀_drop {s t : NetworkState P.n M Unit} {L : ExtendedLabel P.n M}
    (h : NetworkStep P M Unit callPayload (fun _ _ _ => ()) (fun _ _ _ _ _ => True) s L
      (PMF.pure (t.writeGhost (fun _ _ _ => ()) L))) :
    NetworkStep P M Unit callPayload (fun _ _ _ => ()) (fun _ _ _ _ _ => True) s L
      (PMF.pure t) := by
  rwa [writeGhost_unit] at h

/-- **The adversary's ghost is erasable**, provided every round, process and graded
outcome admits an announced bit: `NetworkState.forgetGhost` is a state erasure of the
adversary onto the ghost-free adversary along `forgetBoundExtended`.

The projection is exact on labels. Every row keeps its guards under the erasure, its
guards reading the message record, the DECIDED sets and the corrupted set alone; its
successor is the erasure of its own successor, the ghost write leaving the erasure where
it stands; and the two returns lose their guard, the ghost-free relation being the full
one.

The lift answers a ghost-free row by the row of the same name at the unerased state. On
a graded-agreement return the announced bit is replaced by one the relation `ghostOut`
admits, which `ghostOut_total` supplies, and the two bits agree under
`forgetBoundExtended`. -/
theorem network_erasure
    (ghostOut_total : ∀ (s : NetworkState P.n M G) (r : ℕ) (id : Fin P.n) (out : GBCAOutput),
      ∃ bnd, ghostOut s r id out bnd) :
    StateErasure (network P M G callPayload ghostStep ghostOut)
      (networkGhostFree P M callPayload) NetworkState.forgetGhost forgetBoundExtended where
  init := rfl
  silent := separatesSilent_forgetBoundExtended
  project := by
    intro s l μ h
    simp only [network_step] at h
    simp only [networkGhostFree, network_step]
    cases h <;>
      simp only [PMF.pure_map, forgetGhost_writeGhost, forgetGhost_recordGBCASend,
        forgetGhost_recordDecided, forgetGhost_corrupt] <;>
      apply networkStep₀_drop <;>
      first
        | exact NetworkStep.retByzantine _ _ _ (by assumption)
        | exact NetworkStep.byzantineDecided _ _ _ (by assumption)
        | exact NetworkStep.byzantineGBCA _ _ _ _ (by assumption)
        | (constructor <;> first | assumption | exact trivial)
  lift := by
    intro s l μ h
    simp only [networkGhostFree, network_step] at h
    simp only [network_step]
    cases h
    case gbcaSend r j m =>
      exact ⟨_, _, rfl, NetworkStep.gbcaSend s r j m, by simp [PMF.pure_map]⟩
    case gbcaDeliver r i j m hm =>
      exact ⟨_, _, rfl, NetworkStep.gbcaDeliver s r i j m hm, by simp [PMF.pure_map]⟩
    case decidedSend j b hb =>
      exact ⟨_, _, rfl, NetworkStep.decidedSend s j b hb, by simp [PMF.pure_map]⟩
    case decidedDeliver i j b hb =>
      exact ⟨_, _, rfl, NetworkStep.decidedDeliver s i j b hb, by simp [PMF.pure_map]⟩
    case retWPublish r id c b =>
      exact ⟨_, _, rfl, NetworkStep.retWPublish s r id c b, by simp [PMF.pure_map]⟩
    case gbcaCallLoop r id b =>
      exact ⟨_, _, rfl, NetworkStep.gbcaCallLoop s r id b, by simp [PMF.pure_map]⟩
    case byzantineCallG r k b hF =>
      exact ⟨_, _, rfl, NetworkStep.byzantineCallG s r k b hF, by simp [PMF.pure_map]⟩
    case byzantineCallGLoop r k b hF =>
      exact ⟨_, _, rfl, NetworkStep.byzantineCallGLoop s r k b hF, by simp [PMF.pure_map]⟩
    case byzantineRetG r k out bnd hF _ =>
      obtain ⟨b, hb⟩ := ghostOut_total s r k out
      exact ⟨Sum.inr (.byzantineRetG r k out b), _, rfl,
        NetworkStep.byzantineRetG s r k out b hF hb, by simp [PMF.pure_map]⟩
    case byzantineCallW r k hF =>
      exact ⟨_, _, rfl, NetworkStep.byzantineCallW s r k hF, by simp [PMF.pure_map]⟩
    case byzantineRetW r k b hF =>
      exact ⟨_, _, rfl, NetworkStep.byzantineRetW s r k b hF, by simp [PMF.pure_map]⟩
    case callABAIdle id b =>
      exact ⟨_, _, rfl, NetworkStep.callABAIdle s id b, by simp [PMF.pure_map]⟩
    case retABA id b hb =>
      exact ⟨_, _, rfl, NetworkStep.retABA s id b hb, by simp [PMF.pure_map]⟩
    case retByzantine id b hF =>
      exact ⟨_, _, rfl, NetworkStep.retByzantine s id b hF, by simp [PMF.pure_map]⟩
    case callG r id b =>
      exact ⟨_, _, rfl, NetworkStep.callG s r id b, by simp [PMF.pure_map]⟩
    case retG r id out bnd _ =>
      obtain ⟨b, hb⟩ := ghostOut_total s r id out
      exact ⟨Sum.inl (.retG r id out b), _, rfl,
        NetworkStep.retG s r id out b hb, by simp [PMF.pure_map]⟩
    case callWIdle r id =>
      exact ⟨_, _, rfl, NetworkStep.callWIdle s r id, by simp [PMF.pure_map]⟩
    case retWIdle r id c =>
      exact ⟨_, _, rfl, NetworkStep.retWIdle s r id c, by simp [PMF.pure_map]⟩
    case fail k hnew hbud =>
      exact ⟨_, _, rfl, NetworkStep.fail s k hnew hbud, by simp [PMF.pure_map]⟩
    case byzantineGBCA r k m hF =>
      exact ⟨_, _, rfl, NetworkStep.byzantineGBCA s r k m hF, by simp [PMF.pure_map]⟩
    case byzantineDecided k b hF =>
      exact ⟨_, _, rfl, NetworkStep.byzantineDecided s k b hF, by simp [PMF.pure_map]⟩

end NetErasure

/-! ### The neighbours of the erasure

The network adversary sits in the composition beside the process group and the coin
oracle, and each has to accept whichever representative of a `forgetBoundExtended`-fibre the
adversary announces. -/

section Saturation

variable (P : Parameters) (M S : Type)
    (roundStep : Fin P.n → ProcessRecord P.n S → ExtendedLabel P.n M → PMF (ProcessRecord P.n S) →
      Prop)

/-- **A program is saturated along the erasure.** The announced bound bit is the
network's business: a program's return row takes it free (`IsRoundRuleTable.boundBitFree`), the
idle row of a non-participant carries it as a bound variable, and the replaced program's
self-loop reads no label at all. -/
theorem program_labelSaturated [IsRoundRuleTable P M S roundStep] (j : Fin P.n) :
    (program P M S roundStep j).LabelSaturated (forgetBoundExtended (M := M)) := by
  intro q l l' μ hlab hstep
  simp only [program_step] at hstep ⊢
  rcases (forgetBoundExtended_eq_iff l l').mp hlab with
    rfl | ⟨r, id, out, b, b', rfl, rfl⟩ | ⟨r, k, out, b, b', rfl, rfl⟩
  · exact hstep
  · cases hstep with
    | roundRow _ _ _ h => exact .roundRow _ _ _ (IsRoundRuleTable.boundBitFree h)
    | retGIdle c p _ _ _ _ hid => exact .retGIdle c p r id out b' hid
    | corruptedIdle c p _ hh _ hown => exact .corruptedIdle c p _ hh (by simp) hown
  · cases hstep with
    | roundRow _ _ _ h => exact (IsRoundRuleTable.own h).elim
    | byzantineRetGIdle c p _ _ _ _ hk => exact .byzantineRetGIdle c p r k out b' hk
    | corruptedIdle c p _ hh _ hown => exact .corruptedIdle c p _ hh (by simp) hown

/-- **The process group is saturated along the erasure**: full synchronisation carries
the saturation of every program. -/
theorem programSyncProduct_labelSaturated [IsRoundRuleTable P M S roundStep] :
    (System.syncProduct (program P M S roundStep)).LabelSaturated
      (forgetBoundExtended (M := M)) :=
  System.LabelSaturated.syncProduct (program_labelSaturated P M S roundStep)
    separatesSilent_forgetBoundExtended

/-- **The coin family is saturated along the erasure of the announced bound bit.** A
graded-agreement return belongs to no coin round and is not a corruption, so the family
answers it by the global idle self-loop, whichever bit it announces. -/
theorem wccSpecFamily_labelSaturated :
    (WCC.specFamily P).LabelSaturated (forgetBound (n := P.n)) := by
  intro o l l' μ hlab hstep
  rcases (forgetBound_eq_iff l l').mp hlab with rfl | ⟨r, id, out, b, b', rfl, rfl⟩
  · exact hstep
  · rw [WCC.specFamily, System.family_step_iff] at hstep ⊢
    rcases hstep with
      ⟨hτ, -⟩ | ⟨r', hown, -⟩ | ⟨-, -, hg, -⟩ | ⟨-, -, -, rfl⟩
    · exact absurd hτ (by simp)
    · exact absurd hown (by simp [Label.wccRound])
    · exact absurd hg (by simp [Label.isFail])
    · exact Or.inr (Or.inr (Or.inr ⟨by simp, rfl, by simp [Label.isFail], rfl⟩))

/-- **The lifted coin oracle is saturated along the erasure.** Two labels the erasure
identifies are both outside the pullback's image, or delegate to two labels the coin
family cannot tell apart. -/
theorem coinOverExtendedAlphabet_labelSaturated : (coinOverExtendedAlphabet P M).LabelSaturated
  (forgetBoundExtended (M := M)) := by
  refine System.LabelSaturated.mapIdle (wccSpecFamily_labelSaturated P) ?_
  intro l₁ l₂ hlab
  rcases (forgetBoundExtended_eq_iff l₁ l₂).mp hlab with
    rfl | ⟨r, id, out, b, b', rfl, rfl⟩ | ⟨r, k, out, b, b', rfl, rfl⟩
  · rcases hw : coinLabelMap P.n l₁ with _ | m
    · exact Or.inl ⟨rfl, rfl⟩
    · exact Or.inr ⟨m, m, rfl, rfl, rfl⟩
  · exact Or.inr ⟨_, _, rfl, rfl, rfl⟩
  · exact Or.inl ⟨rfl, rfl⟩

end Saturation

/-! ### The erasure of a flat reading -/

section FlatErasure

variable (P : Parameters) (M S G : Type) [DecidableEq M] [Inhabited G]
    (roundStep : Fin P.n → ProcessRecord P.n S → ExtendedLabel P.n M → PMF (ProcessRecord P.n S) →
      Prop)
    [IsRoundRuleTable P M S roundStep]
    (callPayload : Fin P.n → Bool → M)
    (ghostStep : ExtendedLabel P.n M → NetworkState P.n M G → G → G)
    (ghostOut : NetworkState P.n M G → ℕ → Fin P.n → GBCAOutput → Bool → Prop)

/-- **A flat reading's ghost is erasable.** The adversary's erasure is carried through
the composition pipeline by four congruences: parallel composition against the coin
oracle, parallel composition against the process group, abstraction of the rendezvous
alphabet, and restriction along the shared alphabet. Hiding `Label.hiddenAPI` then
collapses the label identification to the identity, every label the identification moves
being a graded-agreement return. -/
theorem system_stateErasure
    (ghostOut_total : ∀ (s : NetworkState P.n M G) (r : ℕ) (id : Fin P.n) (out : GBCAOutput),
      ∃ bnd, ghostOut s r id out bnd) :
    StateErasure (system P M S G roundStep callPayload ghostStep ghostOut)
      (systemGhostFree P M S roundStep callPayload) forgetGhostState id := by
  have hnet := network_erasure (callPayload := callPayload) (ghostStep := ghostStep)
    ghostOut_total
  have hpre := (hnet.parallel_right (coinOverExtendedAlphabet_labelSaturated P M)).parallel_left
    (programSyncProduct_labelSaturated P M S roundStep)
  have hgroup := (hpre.abstract (networkEventLabels P.n)
    networkEventLabels_forgetBoundExtended).relabel
  exact hgroup.abstract_collapse (Label.hiddenAPI P.n) hiddenAPI_forgetBound
    hiddenAPI_of_forgetBound_ne

/-- **The ghost changes no trace distribution.** The ghost decides no row's firing, the
read admitting a bit at every state, and the bit it announces is hidden at protocol level,
so the reading and the ghost-free reading achieve the same trace distributions. -/
theorem system_erasure
    (ghostOut_total : ∀ (s : NetworkState P.n M G) (r : ℕ) (id : Fin P.n) (out : GBCAOutput),
      ∃ bnd, ghostOut s r id out bnd) :
    achievableTraceDists (system P M S G roundStep callPayload ghostStep ghostOut) =
      achievableTraceDists (systemGhostFree P M S roundStep callPayload) :=
  (system_stateErasure P M S G roundStep callPayload ghostStep ghostOut
    ghostOut_total).achievableTraceDists_eq

end FlatErasure

/-! ### Mechanical axiom check -/

/-- info: 'PLTS.ABA.Implementation.system_erasure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms system_erasure

end Implementation
end ABA
end PLTS
