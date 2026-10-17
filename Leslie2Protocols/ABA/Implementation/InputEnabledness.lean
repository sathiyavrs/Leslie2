/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sathiya / Claude
-/

import Leslie2Protocols.ABA.Implementation.CompositeTransitions
import Leslie2Protocols.Framework.InputEnabledness

/-!
# The input-output discipline of the implementation

`Implementation.systemExtended` composes the `n` programs, the network and the lifted common coin
under full synchronisation. LeslieBP §1.3 and the simulations paper (Assumption 1 and
Definition 2) restrict such a composition to components whose input labels are enabled at every
state and whose output labels are distinct. This file states the label sets of the three kinds of
component and proves both conditions.

* `programInputOutputLabels P M E j`: the program of `j` outputs the labels of `actsAt j`, its
  DECIDED relay and its ABA return, and takes every other non-silent label as an input.
* `networkInputOutputLabels P M E`: the network outputs the round delivery, the DECIDED delivery,
  `fail`, a corrupted process's two sub-protocol calls and the announcement `boundG`. It takes as
  inputs the ABA interface, the graded-agreement call and return, the coin's call and return, the
  round multicast, the round-internal calls and returns, the DECIDED send and the DECIDED relay.
  Its silent transitions are the two injections.
* `coinInputOutputLabels P M E`: the common coin outputs `retW` and takes every other non-silent
  label as an input.

`program_inputEnabled`, `network_inputEnabled` and `coin_inputEnabled` state that each component
has a transition on each of its input labels at every state. `systemExtended_compatible` states
that the output labels of any two components are disjoint.
-/

namespace PLTS
namespace ABA
namespace Implementation

/-! ### The label sets of the three components -/

section Labels

variable (P : Parameters) (M E : Type)

/-- The label sets of the program of process `j`. Its outputs are the labels of `actsAt j`, its
DECIDED relay and its ABA return; its inputs are every other non-silent label. -/
def programInputOutputLabels (j : Fin P.n) : InputOutputLabels (ExtendedLabel P.n M E) where
  inputLabels := {l | l ≠ Sum.inl Label.tau ∧ ¬ actsAt j l ∧
    (∀ b, l ≠ Sum.inr (.decidedRelay j b)) ∧ ∀ b, l ≠ Sum.inl (.retABA j b)}
  outputLabels := {l | actsAt j l} ∪ {l | ∃ b, l = Sum.inr (.decidedRelay j b)} ∪
    {l | ∃ b, l = Sum.inl (.retABA j b)}

/-- The label sets of the network. Its outputs are the round delivery, the DECIDED delivery,
`fail`, a corrupted process's graded-agreement call and coin call, and the announcement of a
round's bound bit. Its inputs are the ABA call and return, the graded-agreement call and return,
the coin's call and return, the round multicast, the round-internal calls and returns, the
DECIDED send and the DECIDED relay. -/
def networkInputOutputLabels : InputOutputLabels (ExtendedLabel P.n M E) where
  inputLabels := {l | match l with
    | Sum.inl (.callABA _ _) | Sum.inl (.retABA _ _) | Sum.inl (.callG _ _ _)
    | Sum.inl (.retG _ _ _) | Sum.inl (.callW _ _) | Sum.inl (.retW _ _ _)
    | Sum.inr (.gbcaSend _ _ _) | Sum.inr (.gbcaRoundEvent _ _ _)
    | Sum.inr (.decidedSend _ _) | Sum.inr (.decidedRelay _ _) => True
    | _ => False}
  outputLabels := {l | match l with
    | Sum.inr (.gbcaDeliver _ _ _ _) | Sum.inr (.decidedDeliver _ _ _) | Sum.inl (.fail _)
    | Sum.inr (.byzantineCallG _ _ _) | Sum.inr (.byzantineCallW _ _)
    | Sum.inl (.boundG _ _) => True
    | _ => False}

/-- The label sets of the common coin. Its outputs are the coin's returns; its inputs are every
other non-silent label. -/
def coinInputOutputLabels : InputOutputLabels (ExtendedLabel P.n M E) where
  inputLabels := {l | l ≠ Sum.inl Label.tau ∧ ∀ r id b, l ≠ Sum.inl (.retW r id b)}
  outputLabels := {l | ∃ r id b, l = Sum.inl (.retW r id b)}

end Labels

/-! ### Input-enabledness of the three components -/

/-- **A program is input-enabled.** At an unreplaced program, each input label has the
participant's transition, the loop that takes it where the participant's transition is not
enabled, or the idle transition on a label of another process: `input` and `inputLoop` (D36),
`retW` and `retWLoop`, the round's transition on a delivery (`IsRoundStep.deliveryEnabled`),
`decidedDeliverReceive` and `decidedDeliverLoop`, `failSelf`, `boundGIdle` and the idle
transitions on a corrupted process's two calls. A replaced program takes every input label on
`corruptedIdle` (D23). -/
theorem program_inputEnabled (P : Parameters) (M E S : Type)
    (roundStep : Fin P.n → ProcessVariables P.n S → ExtendedLabel P.n M E →
      PMF (ProcessVariables P.n S) → Prop) [IsRoundStep P M E S roundStep] (j : Fin P.n) :
    (program P M E S roundStep j).InputEnabled (programInputOutputLabels P M E j).inputLabels := by
  refine System.InputEnabled.of_forall_step ?_
  rintro l ⟨hτ, hact, hrelay, hret⟩ ⟨c, p⟩
  simp only [program_step]
  by_cases hc : c.corrupted = true
  · exact ⟨_, .corruptedIdle c p l hc hτ hact⟩
  have hh : c.corrupted = false := by simpa using hc
  rcases l with l | e
  · cases l with
    | tau => exact absurd rfl hτ
    | callABA id b =>
      by_cases hid : id = j
      · rw [hid]
        by_cases hin : c.processVariables.input = none
        · exact ⟨_, .input c p b hh hin⟩
        · exact ⟨_, .inputLoop c p b hh hin⟩
      · exact ⟨_, .callABAIdle c p id b hid⟩
    | retABA id b => exact ⟨_, .retABAIdle c p id b fun h => hret b (by rw [h])⟩
    | callG r id b => exact ⟨_, .callGIdle c p r id b hact⟩
    | retG r id out => exact ⟨_, .retGIdle c p r id out hact⟩
    | boundG r b => exact ⟨_, .boundGIdle c p r b⟩
    | callW r id => exact ⟨_, .callWIdle c p r id hact⟩
    | retW r id co =>
      by_cases hid : id = j
      · rw [hid]
        by_cases hw : c.processVariables.phase = .awaitW ∧ c.processVariables.round = r
        · exact ⟨_, .retW c p r co hh hw.1 hw.2⟩
        · exact ⟨_, .retWLoop c p r co hh hw⟩
      · exact ⟨_, .retWIdle c p r id co hid⟩
    | fail k =>
      by_cases hk : k = j
      · rw [hk]; exact ⟨_, .failSelf c p hh⟩
      · exact ⟨_, .failIdle c p k hk⟩
  · cases e with
    | gbcaSend r k m => exact ⟨_, .gbcaSendIdle c p r k m hact⟩
    | gbcaDeliver r i k m =>
      by_cases hi : i = j
      · rw [hi]
        obtain ⟨μ, hμ⟩ := IsRoundStep.deliveryEnabled (roundStep := roundStep) (j := j)
          (q := (c, p)) (r := r) (k := k) (m := m) hh
        exact ⟨μ, .roundTransition _ _ _ hμ⟩
      · exact ⟨_, .gbcaDeliverIdle c p r i k m hi⟩
    | decidedSend k b => exact ⟨_, .decidedSendIdle c p k b hact⟩
    | decidedRelay k b => exact ⟨_, .decidedRelayIdle c p k b fun h => hrelay b (by rw [h])⟩
    | decidedDeliver i k b =>
      by_cases hi : i = j
      · rw [hi]
        by_cases hr : b ∈ c.decidedDelivered k
        · exact ⟨_, .decidedDeliverLoop c p k b hh hr⟩
        · exact ⟨_, .decidedDeliverReceive c p k b hh hr⟩
      · exact ⟨_, .decidedDeliverIdle c p i k b hi⟩
    | gbcaRoundEvent r k e => exact ⟨_, .gbcaRoundEventIdle c p r k e hact⟩
    | byzantineCallG r k b => exact ⟨_, .byzantineCallGIdle c p r k b⟩
    | byzantineCallW r k => exact ⟨_, .byzantineCallWIdle c p r k⟩

/-- **The network is input-enabled.** It takes each of its input labels on one unguarded
transition: the ABA call and return, the graded-agreement call and return, the coin's call and
return, the round multicast, the round-internal calls and returns, the DECIDED send and the
DECIDED relay. -/
theorem network_inputEnabled (P : Parameters) (M E G : Type) [DecidableEq M] [Inhabited G]
    (ghostStep : ExtendedLabel P.n M E → NetworkState P.n M G → G → G)
    (ghostBound : G → Option Bool) :
    (network P M E G ghostStep ghostBound).InputEnabled
      (networkInputOutputLabels P M E).inputLabels := by
  refine System.InputEnabled.of_forall_step ?_
  intro l hl s
  simp only [network_step]
  rcases l with l | e
  · cases l with
    | callABA id b => exact ⟨_, .callABAIdle s id b⟩
    | retABA id b => exact ⟨_, .retABAIdle s id b⟩
    | callG r id b => exact ⟨_, .callG s r id b⟩
    | retG r id out => exact ⟨_, .retG s r id out⟩
    | callW r id => exact ⟨_, .callWIdle s r id⟩
    | retW r id c => exact ⟨_, .retWIdle s r id c⟩
    | _ => exact (hl : False).elim
  · cases e with
    | gbcaSend r j m => exact ⟨_, .gbcaSend s r j m⟩
    | gbcaRoundEvent r j e => exact ⟨_, .gbcaRoundEvent s r j e⟩
    | decidedSend j b => exact ⟨_, .decidedSend s j b⟩
    | decidedRelay j b => exact ⟨_, .decidedRelay s j b⟩
    | _ => exact (hl : False).elim

/-- **The common coin is input-enabled.** A shared label other than `τ` and `retW` is an input of
the coin's family (`WCC.specFamily_inputEnabled`), a corrupted process's coin call is read as
the coin's call, and every other synchronisation label leaves the coin idle through
`coinLabelMap`. -/
theorem coin_inputEnabled (P : Parameters) (M E : Type) :
    (coinOverExtendedAlphabet P M E).InputEnabled (coinInputOutputLabels P M E).inputLabels := by
  refine ((WCC.specFamily_inputEnabled P).mapIdle (coinLabelMap P.n)).mono ?_
  rintro l ⟨hτ, hret⟩
  rcases l with l | e
  · exact Or.inr ⟨l, ⟨fun h => hτ (by rw [h]), fun r id b h => hret r id b (by rw [h])⟩, rfl⟩
  · cases e with
    | byzantineCallW r k => exact Or.inr ⟨.callW r k, ⟨by simp, by simp⟩, rfl⟩
    | _ => exact Or.inl rfl

/-! ### Compatibility -/

/-- A label two processes act on names one process. -/
theorem eq_of_actsAt {n : ℕ} {M E : Type} {j j' : Fin n} {l : ExtendedLabel n M E}
    (h : actsAt j l) (h' : actsAt j' l) : j = j' := by
  rcases l with l | e
  · cases l <;> first | exact (Eq.symm h).trans h' | exact (h : False).elim
  · cases e <;> first | exact (Eq.symm h).trans h' | exact (h : False).elim

/-- **The components of the implementation are compatible** (the simulations paper,
Definition 2): the output labels of two distinct programs, of a program and the network, of a
program and the common coin, and of the network and the common coin are disjoint. -/
theorem systemExtended_compatible (P : Parameters) (M E : Type) :
    (∀ j j' : Fin P.n, j ≠ j' →
      (programInputOutputLabels P M E j).Compatible (programInputOutputLabels P M E j')) ∧
    (∀ j : Fin P.n,
      (programInputOutputLabels P M E j).Compatible (networkInputOutputLabels P M E)) ∧
    (∀ j : Fin P.n,
      (programInputOutputLabels P M E j).Compatible (coinInputOutputLabels P M E)) ∧
    (networkInputOutputLabels P M E).Compatible (coinInputOutputLabels P M E) := by
  refine ⟨fun j j' hjj' => ?_, fun j => ?_, fun j => ?_, ?_⟩ <;>
    rw [InputOutputLabels.Compatible, Set.disjoint_left]
  · rintro l ((hl | ⟨b, rfl⟩) | ⟨b, rfl⟩) ((hl' | ⟨b', hb'⟩) | ⟨b', hb'⟩)
    · exact hjj' (eq_of_actsAt hl hl')
    · subst hb'; exact (hl : False).elim
    · subst hb'; exact (hl : False).elim
    · exact (hl' : False).elim
    · cases hb'; exact absurd rfl hjj'
    · cases hb'
    · exact (hl' : False).elim
    · cases hb'
    · cases hb'; exact absurd rfl hjj'
  · rintro l ((hl | ⟨b, rfl⟩) | ⟨b, rfl⟩) hl'
    · rcases l with l | e
      · cases l <;> first | exact (hl : False).elim | exact (hl' : False).elim
      · cases e <;> first | exact (hl : False).elim | exact (hl' : False).elim
    · exact (hl' : False).elim
    · exact (hl' : False).elim
  · rintro l ((hl | ⟨b, rfl⟩) | ⟨b, rfl⟩) ⟨r, id, b', hb'⟩
    · subst hb'; exact (hl : False).elim
    · cases hb'
    · cases hb'
  · rintro l hl ⟨r, id, b, rfl⟩
    exact (hl : False).elim

end Implementation
end ABA
end PLTS
