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
record `NetStateP.ghostRec` of every round, written by `ghostStep` and read out by
`ghostOut` at the two graded-agreement returns. That read decides the bit a return
announces and not whether the return fires: the hypothesis `ghostOut_total` below asks it
to admit a bit at every state. This file erases it.

The reading it is erased to is `flat₀`, the reading over the trivial ghost `Unit` whose
`ghostOut` is the full relation: the same programs, the same network rows, and a
graded-agreement return free to announce either bit. The erasure is a `StateErasure`
(`Framework/Erasure.lean`) along the projection

  `π = Prod.map id (Prod.map NetStateP.forgetGhost id)`

and the label identification `φ = Sum.map forgetBound id`, which sends a
graded-agreement return to the return of the same round, process and graded outcome with
the announced bit fixed at `false` and is the identity on every other label.

Two clauses carry the content. The projection is exact on labels: every row of the
adversary is a row of the ghost-free adversary at the erased state, on the same label,
because the ghost write leaves the erasure where it stands
(`NetStateP.forgetGhost_writeGhost`) and over `Unit` it is the identity
(`NetStateP.writeGhost_unit`). The lift is exact up to `φ`: a ghost-free return
announcing `bnd` is answered by the return announcing a bit the relation `ghostOut`
admits, which is what the hypothesis `ghostOut_total` supplies. Both algorithms satisfy
it, their `ghostOut` being an equation.

The pipeline of `Implementation/System.lean` carries the erasure from the adversary to the
reading. The three congruences of `Framework/Erasure.lean` ask the neighbours to be
saturated along `φ`: the process group is, because a program's return row takes the
announced bit free (`IsStageTable.bndFree`), and the coin oracle is, because a
graded-agreement return is foreign to every coin round. Hiding `Lab.hiddenAPI` collapses
the erasure to the identity on labels, since every label `φ` identifies with a different
one is a graded-agreement return, and those are hidden. The conclusion `flat_erasure` is
therefore an equality of achievable trace distributions, with no label map in the
statement.
-/

namespace PLTS
namespace ABA
namespace Implementation

/-! ### The ghost-free reading -/

section Free

variable (P : Params) (M S : Type) [DecidableEq M]
    (stageStep : Fin P.n → ProcRecP P.n S → NLabP P.n M → PMF (ProcRecP P.n S) → Prop)
    (callPayload : Fin P.n → Bool → M)

/-- The adversary of the ghost-free reading: the network's table over the trivial ghost,
its two graded-agreement returns free to announce either bit. -/
noncomputable def flatNetAdv₀ : System (NetStateP P.n M Unit) (NLabP P.n M) :=
  flatNetAdv P M Unit callPayload (fun _ _ _ => ()) (fun _ _ _ _ _ => True)

/-- **The ghost-free reading**: the flat reading whose adversary holds no ghost record
and announces any bit on a graded-agreement return. -/
noncomputable def flat₀ : System (FlatState P M S Unit) (Lab P.n) :=
  flat P M S Unit stageStep callPayload (fun _ _ _ => ()) (fun _ _ _ _ _ => True)

end Free

/-! ### The projection and the label identification -/

section Labels

variable {n : ℕ} {M : Type}

/-- The projection of a flat reading's state: the process family and the coin oracle
stand, and the adversary's ghost record is dropped. -/
def forgetGhostState {P : Params} {S G : Type} :
    FlatState P M S G → FlatState P M S Unit :=
  Prod.map id (Prod.map NetStateP.forgetGhost id)

/-- The label with the announced bound bit dropped on the rendezvous alphabet: a
Byzantine graded-agreement return keeps its round, the process it answers and its graded
outcome, and every other rendezvous label stands. -/
def forgetBoundEvt : NetEvtP n M → NetEvtP n M
  | .byzRetG r k out _ => .byzRetG r k out false
  | e => e

@[simp] theorem forgetBoundEvt_byzRetG (r : ℕ) (k : Fin n) (out : GbcaOut)
    (bnd : Bool) :
    forgetBoundEvt (NetEvtP.byzRetG (M := M) r k out bnd) = .byzRetG r k out false := rfl

/-- Two rendezvous labels agree under the erasure exactly when they are equal, or are
Byzantine graded-agreement returns of the same round, process and graded outcome. -/
theorem forgetBoundEvt_eq_iff (e e' : NetEvtP n M) :
    forgetBoundEvt e = forgetBoundEvt e' ↔
      e = e' ∨ ∃ (r : ℕ) (k : Fin n) (out : GbcaOut) (b b' : Bool),
        e = .byzRetG r k out b ∧ e' = .byzRetG r k out b' := by
  constructor
  · intro h
    cases e <;> cases e' <;> simp_all [forgetBoundEvt]
  · rintro (rfl | ⟨r, k, out, b, b', rfl, rfl⟩) <;> rfl

/-- The label identification of the erasure: the announced bound bit dropped on both
graded-agreement returns, every other label untouched. -/
abbrev forgetBoundN : NLabP n M → NLabP n M := Sum.map forgetBound forgetBoundEvt

/-- Two labels of the extended alphabet agree under the erasure exactly when they are
equal, or are graded-agreement returns — honest or Byzantine — of the same round,
process and graded outcome. -/
theorem forgetBoundN_eq_iff (l l' : NLabP n M) :
    forgetBoundN l = forgetBoundN l' ↔
      l = l' ∨
      (∃ (r : ℕ) (id : Fin n) (out : GbcaOut) (b b' : Bool),
        l = Sum.inl (.retG r id out b) ∧ l' = Sum.inl (.retG r id out b')) ∨
      (∃ (r : ℕ) (k : Fin n) (out : GbcaOut) (b b' : Bool),
        l = Sum.inr (.byzRetG r k out b) ∧ l' = Sum.inr (.byzRetG r k out b')) := by
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
      rcases (forgetBoundEvt_eq_iff e e').mp (Sum.inr_injective h) with
        rfl | ⟨r, k, out, b, b', rfl, rfl⟩
      · exact Or.inl rfl
      · exact Or.inr (Or.inr ⟨r, k, out, b, b', rfl, rfl⟩)
  · rintro (rfl | ⟨r, id, out, b, b', rfl, rfl⟩ | ⟨r, k, out, b, b', rfl, rfl⟩) <;>
      rfl

/-- The erasure separates the silent label: `τ` is a graded-agreement return of no
round. -/
theorem separatesSilent_forgetBoundN :
    SeparatesSilent (forgetBoundN (n := n) (M := M)) := by
  intro l hl
  rcases (forgetBoundN_eq_iff l (Silent.τ : NLabP n M)).mp hl with
    rfl | ⟨r, id, out, b, b', -, hτ⟩ | ⟨r, k, out, b, b', -, hτ⟩
  · rfl
  · exact absurd hτ (by simp)
  · exact absurd hτ (by simp)

/-- The rendezvous alphabet is saturated along the erasure: the identification keeps a
label in its summand. -/
theorem netEvtLabels_forgetBoundN (l l' : NLabP n M)
    (h : forgetBoundN l = forgetBoundN l') :
    l ∈ netEvtLabels (M := M) n ↔ l' ∈ netEvtLabels (M := M) n := by
  match l, l' with
  | Sum.inl a, Sum.inl a' => simp
  | Sum.inl a, Sum.inr e => exact absurd h (by simp)
  | Sum.inr e, Sum.inl a => exact absurd h (by simp)
  | Sum.inr e, Sum.inr e' => simp
/-- The sub-protocol API is saturated along the erasure. -/
theorem hiddenAPI_forgetBound (l l' : Lab n) (h : forgetBound l = forgetBound l') :
    l ∈ Lab.hiddenAPI n ↔ l' ∈ Lab.hiddenAPI n := by
  rw [← forgetBound_mem_hiddenAPI l, ← forgetBound_mem_hiddenAPI l', h]

/-- Every discrepancy of the erasure lies in the sub-protocol API: two distinct labels
with the same image are graded-agreement returns, and those are hidden. -/
theorem hiddenAPI_of_forgetBound_ne (l l' : Lab n) (h : forgetBound l = forgetBound l')
    (hne : l ≠ l') : l ∈ Lab.hiddenAPI n := by
  rcases (forgetBound_eq_iff l l').mp h with rfl | ⟨r, id, out, b, b', rfl, -⟩
  · exact absurd rfl hne
  · simp

end Labels

/-! ### The adversary's erasure

The network adversary is the one component whose state carries the ghost, and the two
graded-agreement returns are the one pair of rows that read it. -/

section NetErasure

variable {P : Params} {M G : Type} [DecidableEq M] [Inhabited G]
    {callPayload : Fin P.n → Bool → M}
    {ghostStep : NLabP P.n M → NetStateP P.n M G → G → G}
    {ghostOut : NetStateP P.n M G → ℕ → Fin P.n → GbcaOut → Bool → Prop}

/-- Over the trivial ghost a row's successor is the state its write starts from, so a
row written with its ghost write is a row written without it. -/
private theorem netStep₀_drop {s t : NetStateP P.n M Unit} {L : NLabP P.n M}
    (h : FlatNetStep P M Unit callPayload (fun _ _ _ => ()) (fun _ _ _ _ _ => True) s L
      (PMF.pure (t.writeGhost (fun _ _ _ => ()) L))) :
    FlatNetStep P M Unit callPayload (fun _ _ _ => ()) (fun _ _ _ _ _ => True) s L
      (PMF.pure t) := by
  rwa [writeGhost_unit] at h

/-- **The adversary's ghost is erasable**, provided every round, process and graded
outcome admits an announced bit: `NetStateP.forgetGhost` is a state erasure of the
adversary onto the ghost-free adversary along `forgetBoundN`.

The projection is exact on labels. Every row keeps its guards under the erasure, its
guards reading the message record, the DECIDED sets and the corrupted set alone; its
successor is the erasure of its own successor, the ghost write leaving the erasure where
it stands; and the two returns lose their guard, the ghost-free relation being the full
one.

The lift answers a ghost-free row by the row of the same name at the unerased state. On
a graded-agreement return the announced bit is replaced by one the relation `ghostOut`
admits, which `ghostOut_total` supplies, and the two bits agree under
`forgetBoundN`. -/
theorem netAdv_erasure
    (ghostOut_total : ∀ (s : NetStateP P.n M G) (r : ℕ) (id : Fin P.n) (out : GbcaOut),
      ∃ bnd, ghostOut s r id out bnd) :
    StateErasure (flatNetAdv P M G callPayload ghostStep ghostOut)
      (flatNetAdv₀ P M callPayload) NetStateP.forgetGhost forgetBoundN where
  init := rfl
  silent := separatesSilent_forgetBoundN
  project := by
    intro s l μ h
    simp only [flatNetAdv_step] at h
    simp only [flatNetAdv₀, flatNetAdv_step]
    cases h <;>
      simp only [PMF.pure_map, forgetGhost_writeGhost, forgetGhost_gsent,
        forgetGhost_dput, forgetGhost_corrupt] <;>
      apply netStep₀_drop <;>
      first
        | exact FlatNetStep.retByz _ _ _ (by assumption)
        | exact FlatNetStep.byzD _ _ _ (by assumption)
        | exact FlatNetStep.byzG _ _ _ _ (by assumption)
        | (constructor <;> first | assumption | exact trivial)
  lift := by
    intro s l μ h
    simp only [flatNetAdv₀, flatNetAdv_step] at h
    simp only [flatNetAdv_step]
    cases h
    case gsnd r j m =>
      exact ⟨_, _, rfl, FlatNetStep.gsnd s r j m, by simp [PMF.pure_map]⟩
    case gdlv r i j m hm =>
      exact ⟨_, _, rfl, FlatNetStep.gdlv s r i j m hm, by simp [PMF.pure_map]⟩
    case dsnd j b hb =>
      exact ⟨_, _, rfl, FlatNetStep.dsnd s j b hb, by simp [PMF.pure_map]⟩
    case ddlv i j b hb =>
      exact ⟨_, _, rfl, FlatNetStep.ddlv s i j b hb, by simp [PMF.pure_map]⟩
    case retWPub r id c b =>
      exact ⟨_, _, rfl, FlatNetStep.retWPub s r id c b, by simp [PMF.pure_map]⟩
    case gcallLoop r id b =>
      exact ⟨_, _, rfl, FlatNetStep.gcallLoop s r id b, by simp [PMF.pure_map]⟩
    case byzCallG r k b hF =>
      exact ⟨_, _, rfl, FlatNetStep.byzCallG s r k b hF, by simp [PMF.pure_map]⟩
    case byzCallGLoop r k b hF =>
      exact ⟨_, _, rfl, FlatNetStep.byzCallGLoop s r k b hF, by simp [PMF.pure_map]⟩
    case byzRetG r k out bnd hF _ =>
      obtain ⟨b, hb⟩ := ghostOut_total s r k out
      exact ⟨Sum.inr (.byzRetG r k out b), _, rfl,
        FlatNetStep.byzRetG s r k out b hF hb, by simp [PMF.pure_map]⟩
    case byzCallW r k hF =>
      exact ⟨_, _, rfl, FlatNetStep.byzCallW s r k hF, by simp [PMF.pure_map]⟩
    case byzRetW r k b hF =>
      exact ⟨_, _, rfl, FlatNetStep.byzRetW s r k b hF, by simp [PMF.pure_map]⟩
    case callABAIdle id b =>
      exact ⟨_, _, rfl, FlatNetStep.callABAIdle s id b, by simp [PMF.pure_map]⟩
    case retABA id b hb =>
      exact ⟨_, _, rfl, FlatNetStep.retABA s id b hb, by simp [PMF.pure_map]⟩
    case retByz id b hF =>
      exact ⟨_, _, rfl, FlatNetStep.retByz s id b hF, by simp [PMF.pure_map]⟩
    case callG r id b =>
      exact ⟨_, _, rfl, FlatNetStep.callG s r id b, by simp [PMF.pure_map]⟩
    case retG r id out bnd _ =>
      obtain ⟨b, hb⟩ := ghostOut_total s r id out
      exact ⟨Sum.inl (.retG r id out b), _, rfl,
        FlatNetStep.retG s r id out b hb, by simp [PMF.pure_map]⟩
    case callWIdle r id =>
      exact ⟨_, _, rfl, FlatNetStep.callWIdle s r id, by simp [PMF.pure_map]⟩
    case retWIdle r id c =>
      exact ⟨_, _, rfl, FlatNetStep.retWIdle s r id c, by simp [PMF.pure_map]⟩
    case fail k hnew hbud =>
      exact ⟨_, _, rfl, FlatNetStep.fail s k hnew hbud, by simp [PMF.pure_map]⟩
    case byzG r k m hF =>
      exact ⟨_, _, rfl, FlatNetStep.byzG s r k m hF, by simp [PMF.pure_map]⟩
    case byzD k b hF =>
      exact ⟨_, _, rfl, FlatNetStep.byzD s k b hF, by simp [PMF.pure_map]⟩

end NetErasure

/-! ### The neighbours of the erasure

The network adversary sits in the composition beside the process group and the coin
oracle, and each has to accept whichever representative of a `forgetBoundN`-fibre the
adversary announces. -/

section Saturation

variable (P : Params) (M S : Type)
    (stageStep : Fin P.n → ProcRecP P.n S → NLabP P.n M → PMF (ProcRecP P.n S) → Prop)

/-- **A program is saturated along the erasure.** The announced bound bit is the
network's business: a program's return row takes it free (`IsStageTable.bndFree`), the
idle row of a non-participant carries it as a bound variable, and the replaced program's
self-loop reads no label at all. -/
theorem flatProcN_labelSaturated [IsStageTable P M S stageStep] (j : Fin P.n) :
    (flatProcN P M S stageStep j).LabelSaturated (forgetBoundN (M := M)) := by
  intro q l l' μ hlab hstep
  simp only [flatProcN_step] at hstep ⊢
  rcases (forgetBoundN_eq_iff l l').mp hlab with
    rfl | ⟨r, id, out, b, b', rfl, rfl⟩ | ⟨r, k, out, b, b', rfl, rfl⟩
  · exact hstep
  · cases hstep with
    | stageRow _ _ _ h => exact .stageRow _ _ _ (IsStageTable.bndFree h)
    | retGIdle c p _ _ _ _ hid => exact .retGIdle c p r id out b' hid
    | corruptedIdle c p _ hh _ hown => exact .corruptedIdle c p _ hh (by simp) hown
  · cases hstep with
    | stageRow _ _ _ h => exact (IsStageTable.own h).elim
    | byzRetGIdle c p _ _ _ _ hk => exact .byzRetGIdle c p r k out b' hk
    | corruptedIdle c p _ hh _ hown => exact .corruptedIdle c p _ hh (by simp) hown

/-- **The process group is saturated along the erasure**: full synchronisation carries
the saturation of every program. -/
theorem flatProcGroup_labelSaturated [IsStageTable P M S stageStep] :
    (System.syncProduct (flatProcN P M S stageStep)).LabelSaturated
      (forgetBoundN (M := M)) :=
  System.LabelSaturated.syncProduct (flatProcN_labelSaturated P M S stageStep)
    separatesSilent_forgetBoundN

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
    · exact absurd hown (by simp [Lab.wccRound])
    · exact absurd hg (by simp [Lab.isFail])
    · exact Or.inr (Or.inr (Or.inr ⟨by simp, rfl, by simp [Lab.isFail], rfl⟩))

/-- **The lifted coin oracle is saturated along the erasure.** Two labels the erasure
identifies are both outside the pullback's image, or delegate to two labels the coin
family cannot tell apart. -/
theorem wccLiftP_labelSaturated : (wccLiftP P M).LabelSaturated (forgetBoundN (M := M)) := by
  refine System.LabelSaturated.mapIdle (wccSpecFamily_labelSaturated P) ?_
  intro l₁ l₂ hlab
  rcases (forgetBoundN_eq_iff l₁ l₂).mp hlab with
    rfl | ⟨r, id, out, b, b', rfl, rfl⟩ | ⟨r, k, out, b, b', rfl, rfl⟩
  · rcases hw : wccPull P.n l₁ with _ | m
    · exact Or.inl ⟨rfl, rfl⟩
    · exact Or.inr ⟨m, m, rfl, rfl, rfl⟩
  · exact Or.inr ⟨_, _, rfl, rfl, rfl⟩
  · exact Or.inl ⟨rfl, rfl⟩

end Saturation

/-! ### The erasure of a flat reading -/

section FlatErasure

variable (P : Params) (M S G : Type) [DecidableEq M] [Inhabited G]
    (stageStep : Fin P.n → ProcRecP P.n S → NLabP P.n M → PMF (ProcRecP P.n S) → Prop)
    [IsStageTable P M S stageStep]
    (callPayload : Fin P.n → Bool → M)
    (ghostStep : NLabP P.n M → NetStateP P.n M G → G → G)
    (ghostOut : NetStateP P.n M G → ℕ → Fin P.n → GbcaOut → Bool → Prop)

/-- **A flat reading's ghost is erasable.** The adversary's erasure is carried through
the composition pipeline by four congruences: parallel composition against the coin
oracle, parallel composition against the process group, abstraction of the rendezvous
alphabet, and restriction along the shared alphabet. Hiding `Lab.hiddenAPI` then
collapses the label identification to the identity, every label the identification moves
being a graded-agreement return. -/
theorem flat_stateErasure
    (ghostOut_total : ∀ (s : NetStateP P.n M G) (r : ℕ) (id : Fin P.n) (out : GbcaOut),
      ∃ bnd, ghostOut s r id out bnd) :
    StateErasure (flat P M S G stageStep callPayload ghostStep ghostOut)
      (flat₀ P M S stageStep callPayload) forgetGhostState id := by
  have hnet := netAdv_erasure (callPayload := callPayload) (ghostStep := ghostStep)
    ghostOut_total
  have hpre := (hnet.parallel_right (wccLiftP_labelSaturated P M)).parallel_left
    (flatProcGroup_labelSaturated P M S stageStep)
  have hgroup := (hpre.abstract (netEvtLabels P.n) netEvtLabels_forgetBoundN).relabel
  exact hgroup.abstract_collapse (Lab.hiddenAPI P.n) hiddenAPI_forgetBound
    hiddenAPI_of_forgetBound_ne

/-- **The ghost changes no trace distribution.** The ghost decides no row's firing, the
read admitting a bit at every state, and the bit it announces is hidden at protocol level,
so the reading and the ghost-free reading achieve the same trace distributions. -/
theorem flat_erasure
    (ghostOut_total : ∀ (s : NetStateP P.n M G) (r : ℕ) (id : Fin P.n) (out : GbcaOut),
      ∃ bnd, ghostOut s r id out bnd) :
    achievableTraceDists (flat P M S G stageStep callPayload ghostStep ghostOut) =
      achievableTraceDists (flat₀ P M S stageStep callPayload) :=
  (flat_stateErasure P M S G stageStep callPayload ghostStep ghostOut
    ghostOut_total).achievableTraceDists_eq

end FlatErasure

/-! ### Mechanical axiom check -/

/-- info: 'PLTS.ABA.Implementation.flat_erasure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms flat_erasure

end Implementation
end ABA
end PLTS
