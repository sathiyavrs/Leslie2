/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sathiya / Claude
-/

import Leslie2Protocols.Framework.LoopsAndInstanceFamilies
import Leslie2.Simulation.ForwardLTS

/-!
# Forward simulation is a congruence for `System.family`

Per-instance forward simulations lift to the ℕ-indexed families of `System.family`
(`Framework/LoopsAndInstanceFamilies.lean`). Let every instance `instC r` forward-simulate
`instA r` along `R r`, and let the broadcast transformations preserve `R` (`hglob`). Then the
concrete family forward-simulates the abstract family along the relation that asks for the same
broadcasts, the same rounds in the two maps, and related instances at every round
(`ForwardSimulation.family`).

The family takes a silent transition only at a round of its map. A concrete visible step at an
untouched round is matched by the abstract family from an untouched round as well, and there the
abstract family cannot take the silent transitions with which a weak run may begin. The congruence
therefore asks of each round one more hypothesis, `hUntouchedFirstStep`: from a related pair of
untouched instances, a concrete step on a label the round owns is matched by an abstract run whose
first transition carries that label, followed by a silent run. Every simulation of the ABA
development satisfies it: the first transition of a round is a call, and a call is matched by a
call. `ForwardSimulation.family_of_noSilentAtUntouched` derives the hypothesis from the
per-round simulations when the abstract instance has no silent transition at an untouched state.

The proof maps the abstract instance's witness execution into the family along
`AlterSeq.map (g.setInstanceState r)`, which leaves the instance at every round `r' ≠ r` unchanged:

* `System.weakLStep_of_step` — a single Dirac step is a weak run of one transition;
  `weakLStep_tauThen` is the run of two, a silent step followed by an external one;
* `System.weakLSilent_of_step_weakLSilent`, `System.weakLStep_of_step_weakLSilent` — a
  transition followed by a silent run is a weak run, and
  `System.exists_step_weakLSilent_of_weakLStep` is the converse at a state with no silent
  transition;
* `AlterSeq.stateAt_succ_cons`, `AlterSeq.endState_cons`, `is_partial_exec_cons` — a run whose
  first transition is prepended: its states after the first are those of the run it extends, its
  end state is that run's end state, and it is a partial execution when that run is one and the
  prepended transition is a transition of the system;
* `AlterSeq.stateAt_map`, `AlterSeq.endState_map`, `System.trace_map_state` — the
  `AlterSeq.map` lemmas: a state map commutes with `stateAt` and `endState` and leaves the trace
  unchanged, since the trace reads labels alone;
* `System.weakLSilent_family`, `System.weakLStep_family` — a weak run of the instance `inst r`
  from a round of the map is a weak run of the family, which moves round `r` alone;
  `System.weakLSilent_family_of_step` and `System.weakLStep_family_of_step` are the same for a run
  whose first transition is owned by round `r`, at any round.

The broadcast and idle disjuncts of the family are matched by the abstract family's own one-step
broadcast and idle transitions, so no instance simulation is consulted there: `hglob` gives the
relation after a broadcast, and an idle step preserves it.
-/

open Stream'

namespace PLTS

variable {State State' σ Label : Type}

/-! ### Single-step weak transitions -/

section SingleStep

variable {sys : System State Label}

private theorem singleStep_partial_exec {q q' : State} {l : Label}
    (h : sys.step q l (PMF.pure q')) :
    is_partial_exec ⟨q, Seq.cons (l, q') Seq.nil⟩ sys := by
  intro k l' s' hk
  cases k with
  | zero =>
    rw [Stream'.Seq.get?_cons_zero] at hk
    injection hk with hk
    injection hk with h1 h2
    subst h1
    subst h2
    exact ⟨q, PMF.pure q', rfl, h, by rw [PMF.mem_support_pure_iff]⟩
  | succ k =>
    rw [Stream'.Seq.get?_cons_succ, Stream'.Seq.get?_nil] at hk
    exact absurd hk (by simp)

private theorem terminates_of_two_transitions {l₀ l₁ : Label} {q₁ q₂ : State} :
    (Seq.cons (l₀, q₁) (Seq.cons (l₁, q₂) Seq.nil) : Seq (Label × State)).Terminates :=
  Seq.terminates_cons_iff.mpr (Seq.terminates_cons_iff.mpr Seq.terminates_nil)

/-- `endState` of a two-transition alternating sequence. -/
private theorem endState_of_two_transitions (q₀ : State) (l₀ : Label) (q₁ : State) (l₁ : Label)
    (q₂ : State) :
    (⟨q₀, Seq.cons (l₀, q₁) (Seq.cons (l₁, q₂) Seq.nil)⟩ : AlterSeq State Label).endState
      terminates_of_two_transitions = q₂ := by
  classical
  set e : AlterSeq State Label := ⟨q₀, Seq.cons (l₀, q₁) (Seq.cons (l₁, q₂) Seq.nil)⟩ with he
  have hterm : e.trans.Terminates := terminates_of_two_transitions
  have hfind : Nat.find hterm = 2 := by
    refine le_antisymm (Nat.find_le (show e.trans.TerminatedAt 2 from rfl)) ?_
    rw [Nat.le_find_iff]
    intro m hm
    interval_cases m
    · exact Seq.cons_not_terminatedAt_zero
    · intro hc
      exact absurd (hc : e.trans.get? 1 = none) (by simp [he])
  have hstate := AlterSeq.stateAt_find_eq_endState e hterm
  rw [hfind] at hstate
  have h2 : e.stateAt 2 = some q₂ := rfl
  rw [h2] at hstate
  exact (Option.some.inj hstate).symm

variable [Silent Label]

/-- A single external Dirac step is a weak transition. -/
theorem System.weakLStep_of_step {q q' : State} {l : Label}
    (hl : ¬ l = Silent.τ) (h : sys.step q l (PMF.pure q')) :
    sys.weakLStep q l q' :=
  ⟨⟨q, Seq.cons (l, q') Seq.nil⟩,
    Stream'.Seq.terminates_cons_iff.mpr Stream'.Seq.terminates_nil,
    singleStep_partial_exec h, rfl,
    AlterSeq.endState_singleton_cons q l q',
    by rw [System.trace_cons_external sys q l q' Seq.nil hl, System.trace_init]⟩

/-- **The run.** A silent step followed by an external step is a weak
`l`-transition: the τ-step is the leading τ-closure. -/
theorem weakLStep_tauThen {q q₁ q' : State} {l : Label}
    (h1 : sys.LStep q Silent.τ q₁) (h2 : sys.LStep q₁ l q')
    (hl : ¬ l = Silent.τ) : sys.weakLStep q l q' := by
  refine ⟨⟨q, Seq.cons (Silent.τ, q₁) (Seq.cons (l, q') Seq.nil)⟩, terminates_of_two_transitions,
    ?_, rfl, endState_of_two_transitions q Silent.τ q₁ l q', ?_⟩
  · intro k l' s' hk
    match k with
    | 0 =>
      rw [Seq.get?_cons_zero] at hk
      injection hk with hk
      injection hk with ha hb
      subst ha; subst hb
      exact ⟨q, PMF.pure q₁, rfl, h1, by rw [PMF.mem_support_pure_iff]⟩
    | 1 =>
      rw [Seq.get?_cons_succ, Seq.get?_cons_zero] at hk
      injection hk with hk
      injection hk with ha hb
      subst ha; subst hb
      exact ⟨q₁, PMF.pure q', rfl, h2, by rw [PMF.mem_support_pure_iff]⟩
    | (k + 2) =>
      rw [Seq.get?_cons_succ, Seq.get?_cons_succ, Seq.get?_nil] at hk
      exact absurd hk (by simp)
  · have htail : sys.trace ⟨q₁, Seq.cons (l, q') Seq.nil⟩ = Seq.cons l Seq.nil := by
      rw [System.trace_cons_external sys q₁ l q' Seq.nil hl, System.trace_init]
    unfold System.trace at htail ⊢
    rw [Seq.filter_cons_neg _ _ (by simp)]
    exact htail

end SingleStep

/-! ### A transition followed by a silent run -/

section StepThenSilent

variable {sys : System State Label}

/-- The state after `n + 1` transitions of a run whose first transition is `(l₀, q₁)` is the
state after `n` transitions of the run from `q₁`. -/
theorem AlterSeq.stateAt_succ_cons (q q₁ : State) (l₀ : Label) (T : Seq (Label × State))
    (n : ℕ) :
    (⟨q, Seq.cons (l₀, q₁) T⟩ : AlterSeq State Label).stateAt (n + 1)
      = (⟨q₁, T⟩ : AlterSeq State Label).stateAt n := by
  cases n with
  | zero => rfl
  | succ k => rfl

/-- Prepending a transition to a partial execution gives a partial execution. -/
theorem is_partial_exec_cons {q q₁ : State} {l₀ : Label} {μ : PMF State}
    {T : Seq (Label × State)} (h : sys.step q l₀ μ) (hq₁ : q₁ ∈ μ.support)
    (hpe : is_partial_exec ⟨q₁, T⟩ sys) :
    is_partial_exec ⟨q, Seq.cons (l₀, q₁) T⟩ sys := by
  intro n l s' hn
  cases n with
  | zero =>
    rw [Stream'.Seq.get?_cons_zero, Option.some.injEq, Prod.mk.injEq] at hn
    obtain ⟨rfl, rfl⟩ := hn
    exact ⟨q, μ, rfl, h, hq₁⟩
  | succ k =>
    rw [Stream'.Seq.get?_cons_succ] at hn
    obtain ⟨s, ν, hs, hstep, hmem⟩ := hpe k l s' hn
    exact ⟨s, ν, by rw [AlterSeq.stateAt_succ_cons]; exact hs, hstep, hmem⟩

/-- The run after the first transition of a partial execution is a partial execution. -/
private theorem is_partial_exec_of_cons {q q₁ : State} {l₀ : Label} {T : Seq (Label × State)}
    (hpe : is_partial_exec ⟨q, Seq.cons (l₀, q₁) T⟩ sys) : is_partial_exec ⟨q₁, T⟩ sys := by
  intro n l s' hn
  obtain ⟨s, ν, hs, hstep, hmem⟩ :=
    hpe (n + 1) l s' (by rw [Stream'.Seq.get?_cons_succ]; exact hn)
  exact ⟨s, ν, by rw [← AlterSeq.stateAt_succ_cons q q₁ l₀]; exact hs, hstep, hmem⟩

/-- Prepending a transition does not change the end state. -/
theorem AlterSeq.endState_cons (q q₁ : State) (l₀ : Label) {T : Seq (Label × State)}
    (hT : T.Terminates) (h : (Seq.cons (l₀, q₁) T).Terminates) :
    (⟨q, Seq.cons (l₀, q₁) T⟩ : AlterSeq State Label).endState h
      = (⟨q₁, T⟩ : AlterSeq State Label).endState hT := by
  rw [AlterSeq.endState_eq_getLast?, AlterSeq.endState_eq_getLast?, Stream'.Seq.toList_cons h,
    List.getLast?_cons]
  change Prod.snd (((T.toList hT).getLast?).getD (l₀, q₁))
    = ((T.toList hT).getLast?).elim q₁ Prod.snd
  cases (T.toList hT).getLast? <;> rfl

variable [Silent Label]

/-- A run that begins with a transition `q -l₀→ μ` to `q₁ ∈ μ.support` and continues with a
silent run from `q₁` to `q'`. -/
private theorem exists_run_of_step_weakLSilent {q q₁ q' : State} {l₀ : Label} {μ : PMF State}
    (h : sys.step q l₀ μ) (hq₁ : q₁ ∈ μ.support) (htail : sys.weakLSilent q₁ q') :
    ∃ (T : Seq (Label × State)) (hterm : (Seq.cons (l₀, q₁) T).Terminates),
      is_partial_exec ⟨q, Seq.cons (l₀, q₁) T⟩ sys ∧
      (⟨q, Seq.cons (l₀, q₁) T⟩ : AlterSeq State Label).endState hterm = q' ∧
      sys.trace ⟨q₁, T⟩ = Seq.nil := by
  obtain ⟨⟨i, T⟩, hT, hpe, hinit, hend, htr⟩ := htail
  change i = q₁ at hinit
  subst hinit
  exact ⟨T, Stream'.Seq.terminates_cons_iff.mpr hT, is_partial_exec_cons h hq₁ hpe,
    (AlterSeq.endState_cons q i l₀ hT _).trans hend, htr⟩

/-- A silent transition followed by a silent run is a silent run. -/
theorem System.weakLSilent_of_step_weakLSilent {q q₁ q' : State} {μ : PMF State}
    (h : sys.step q Silent.τ μ) (hq₁ : q₁ ∈ μ.support) (htail : sys.weakLSilent q₁ q') :
    sys.weakLSilent q q' := by
  obtain ⟨T, hterm, hpe, hend, htr⟩ := exists_run_of_step_weakLSilent h hq₁ htail
  refine ⟨⟨q, Seq.cons (Silent.τ, q₁) T⟩, hterm, hpe, rfl, hend, ?_⟩
  unfold System.trace at htr ⊢
  rw [Seq.filter_cons_neg _ _ (by simp)]
  exact htr

/-- An external transition followed by a silent run is a weak transition on its label. -/
theorem System.weakLStep_of_step_weakLSilent {q q₁ q' : State} {l : Label} {μ : PMF State}
    (hl : ¬ l = Silent.τ) (h : sys.step q l μ) (hq₁ : q₁ ∈ μ.support)
    (htail : sys.weakLSilent q₁ q') : sys.weakLStep q l q' := by
  obtain ⟨T, hterm, hpe, hend, htr⟩ := exists_run_of_step_weakLSilent h hq₁ htail
  refine ⟨⟨q, Seq.cons (l, q₁) T⟩, hterm, hpe, rfl, hend, ?_⟩
  rw [System.trace_cons_external sys q l q₁ T hl, htr]

/-- **The first transition of a weak run.** At a state with no silent transition, a weak
`l`-transition begins with an `l`-transition, followed by a silent run. -/
theorem System.exists_step_weakLSilent_of_weakLStep {q q' : State} {l : Label}
    (hNoSilent : ∀ μ, ¬ sys.step q Silent.τ μ) (h : sys.weakLStep q l q') :
    ∃ μ, sys.step q l μ ∧ ∃ q₁ ∈ μ.support, sys.weakLSilent q₁ q' := by
  obtain ⟨⟨i, T⟩, hterm, hpe, hinit, hend, htr⟩ := h
  change i = q at hinit
  subst hinit
  cases T with
  | nil =>
    rw [System.trace_init] at htr
    exact absurd htr.symm Stream'.Seq.cons_ne_nil
  | cons x T =>
    obtain ⟨l₀, q₁⟩ := x
    obtain ⟨s, μ, hs, hstep, hq₁⟩ := hpe 0 l₀ q₁ (Stream'.Seq.get?_cons_zero _ _)
    change some i = some s at hs
    obtain rfl := Option.some.inj hs
    have hl₀ : ¬ l₀ = Silent.τ := by
      rintro rfl
      exact hNoSilent μ hstep
    rw [System.trace_cons_external sys i l₀ q₁ T hl₀, Stream'.Seq.cons_eq_cons] at htr
    obtain ⟨rfl, htail⟩ := htr
    have hT : T.Terminates := Stream'.Seq.terminates_cons_iff.mp hterm
    exact ⟨μ, hstep, q₁, hq₁,
      ⟨⟨q₁, T⟩, hT, is_partial_exec_of_cons hpe, rfl,
        (AlterSeq.endState_cons i q₁ l₀ hT hterm).symm.trans hend, htail⟩⟩

end StepThenSilent

/-! ### What `AlterSeq.map` leaves alone -/

/-- `AlterSeq.map` commutes with `stateAt`. -/
theorem AlterSeq.stateAt_map (f : State → State') (e : AlterSeq State Label) (n : ℕ) :
    (e.map f).stateAt n = (e.stateAt n).map f := by
  cases n with
  | zero => rfl
  | succ k =>
    change ((e.trans.map fun lq => (lq.1, f lq.2)).get? k).map Prod.snd
      = ((e.trans.get? k).map Prod.snd).map f
    rw [Stream'.Seq.map_get?]
    cases e.trans.get? k with
    | none => rfl
    | some lq => rfl

/-- `AlterSeq.map` commutes with `endState`. -/
theorem AlterSeq.endState_map (f : State → State') (e : AlterSeq State Label)
    (h : e.trans.Terminates) (h' : (e.map f).trans.Terminates) :
    (e.map f).endState h' = f (e.endState h) := by
  have hterm_iff : ∀ n, (e.map f).trans.TerminatedAt n ↔ e.trans.TerminatedAt n := by
    intro n
    change (e.trans.map fun lq => (lq.1, f lq.2)).get? n = none ↔ e.trans.get? n = none
    rw [Stream'.Seq.map_get?]
    cases e.trans.get? n <;> simp
  have hfind : Nat.find h' = Nat.find h := by
    apply le_antisymm
    · exact Nat.find_le ((hterm_iff _).mpr (Nat.find_spec h))
    · exact Nat.find_le ((hterm_iff _).mp (Nat.find_spec h'))
  have h1 := AlterSeq.stateAt_find_eq_endState (e.map f) h'
  rw [hfind, AlterSeq.stateAt_map, AlterSeq.stateAt_find_eq_endState e h] at h1
  simp only [Option.map_some, Option.some.injEq] at h1
  exact h1.symm

/-- The trace only reads labels, so it is invariant under pointwise state maps
(for any two systems over the same label type). -/
theorem System.trace_map_state [Silent Label] (sys' : System State' Label)
    (sys : System State Label) (f : State → State') (e : AlterSeq State Label) :
    sys'.trace (e.map f) = sys.trace e := by
  unfold System.trace
  rw [show (e.map f).trans = e.trans.map (fun lq : Label × State => (lq.1, f lq.2)) from rfl,
    Stream'.Seq.filter_map, ← Stream'.Seq.map_comp]
  rfl


/-! ### A run of one instance, embedded in the family -/

section FamilyEmbedding

variable [Silent Label]

/-- Every external label occurring in a terminating execution occurs in its
trace. -/
theorem mem_trace_of_external {sys : System State Label}
    {e : AlterSeq State Label} (hterm : e.trans.Terminates) {n : ℕ} {l : Label}
    {s' : State} (hn : e.trans.get? n = some (l, s')) (hl : ¬ l = Silent.τ) :
    ∃ m, (sys.trace e).get? m = some l := by
  classical
  have hLn : (e.trans.toList hterm)[n]? = some (l, s') := by
    have h1 : (Seq.ofList (e.trans.toList hterm)).get? n = some (l, s') := by
      rw [Stream'.Seq.ofList_toList e.trans hterm]
      exact hn
    rwa [Stream'.Seq.ofList_get?] at h1
  have htr : sys.trace e = ((Seq.ofList (e.trans.toList hterm)).filter
      (fun p => ¬ (p.1 = Silent.τ))).map Prod.fst := by
    unfold System.trace
    conv_lhs => rw [← Stream'.Seq.ofList_toList e.trans hterm]
  rw [htr, Stream'.Seq.ofList_filter, Stream'.Seq.map_ofList_pub]
  simp only [Stream'.Seq.ofList_get?]
  rw [← List.mem_iff_getElem?]
  refine List.mem_map.mpr ⟨(l, s'),
    List.mem_filter.mpr ⟨List.mem_of_getElem? hLn, ?_⟩, rfl⟩
  simpa using hl


/-- The image of a partial execution of the instance `inst r` under `g.setInstanceState r` is a
partial execution of the family, provided every transition label is silent or owned by round `r`.
Every state of the image is a state `g.setInstanceState r x`, whose map holds round `r`, so a
silent transition of the instance is one of the family. -/
private theorem is_partial_exec_map_family {inst : ℕ → System σ Label}
    {owns : Label → Option ℕ} {glob : Label → Prop} {act : Label → σ → σ} {initial : σ}
    {r : ℕ} (g : InstanceFamilyState initial act) {e : AlterSeq σ Label}
    (hpe : is_partial_exec e (inst r))
    (hlab : ∀ n l s', e.trans.get? n = some (l, s') → l = Silent.τ ∨ owns l = some r) :
    is_partial_exec (e.map (g.setInstanceState r))
      (System.family inst owns glob act initial) := by
  intro n l s' hn
  rw [show (e.map (g.setInstanceState r)).trans
      = e.trans.map (fun lq : Label × σ => (lq.1, g.setInstanceState r lq.2)) from rfl,
    Stream'.Seq.map_get?] at hn
  cases hg : e.trans.get? n with
  | none =>
    rw [hg] at hn
    exact absurd hn (by simp)
  | some lq =>
    obtain ⟨l₀, x⟩ := lq
    rw [hg] at hn
    simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hn
    obtain ⟨rfl, rfl⟩ := hn
    obtain ⟨sn, μ, hsn, hstep, hmem⟩ := hpe n l₀ x hg
    have hstep' : (inst r).step ((g.setInstanceState r sn) r) l₀ μ := by
      rw [InstanceFamilyState.setInstanceState_apply_same]
      exact hstep
    refine ⟨g.setInstanceState r sn,
      μ.map ((g.setInstanceState r sn).setInstanceState r), ?_, ?_, ?_⟩
    · rw [AlterSeq.stateAt_map, hsn]
      rfl
    · refine (System.family_step_iff inst owns glob act initial).mpr ?_
      rcases hlab n l₀ x hg with hτ | howns
      · exact Or.inl ⟨hτ, r, InstanceFamilyState.mem_keys_setInstanceState_self g r sn, μ,
          hstep', rfl⟩
      · exact Or.inr (Or.inl ⟨r, howns, μ, hstep', rfl⟩)
    · rw [PMF.mem_support_map_iff]
      exact ⟨x, hmem, InstanceFamilyState.setInstanceState_setInstanceState g r sn x⟩

/-- A silent weak run of the instance at a round `r` of the map is a silent weak run of the
family, which moves round `r` alone. -/
theorem System.weakLSilent_family {inst : ℕ → System σ Label}
    (owns : Label → Option ℕ) (glob : Label → Prop) (act : Label → σ → σ) {initial : σ}
    {r : ℕ} {g : InstanceFamilyState initial act} {q' : σ} (hr : r ∈ g.instanceMap.keys)
    (h : (inst r).weakLSilent (g r) q') :
    (System.family inst owns glob act initial).weakLSilent g (g.setInstanceState r q') := by
  obtain ⟨e, hterm, hpe, hinit, hend, htr⟩ := h
  refine ⟨e.map (g.setInstanceState r),
    (AlterSeq.map_trans_terminates_iff (g.setInstanceState r) e).mpr hterm,
    ?_, ?_, ?_, ?_⟩
  · refine is_partial_exec_map_family g hpe ?_
    intro n l₀ s₀ hn
    left
    by_contra hl₀
    obtain ⟨m, hm⟩ := mem_trace_of_external (sys := inst r) hterm hn hl₀
    rw [htr, Stream'.Seq.get?_nil] at hm
    exact absurd hm (by simp)
  · change g.setInstanceState r e.init = g
    rw [hinit]
    exact InstanceFamilyState.setInstanceState_apply_self hr
  · rw [AlterSeq.endState_map (g.setInstanceState r) e hterm, hend]
  · rw [System.trace_map_state _ (inst r)]
    exact htr

/-- A labelled weak run of the instance at a round `r` of the map, on a label owned by `r`, is a
weak run of the family, which moves round `r` alone. -/
theorem System.weakLStep_family {inst : ℕ → System σ Label}
    (owns : Label → Option ℕ) (glob : Label → Prop) (act : Label → σ → σ) {initial : σ}
    {r : ℕ} {g : InstanceFamilyState initial act} {l : Label} {q' : σ}
    (howns : owns l = some r) (hr : r ∈ g.instanceMap.keys)
    (h : (inst r).weakLStep (g r) l q') :
    (System.family inst owns glob act initial).weakLStep g l (g.setInstanceState r q') := by
  obtain ⟨e, hterm, hpe, hinit, hend, htr⟩ := h
  refine ⟨e.map (g.setInstanceState r),
    (AlterSeq.map_trans_terminates_iff (g.setInstanceState r) e).mpr hterm,
    ?_, ?_, ?_, ?_⟩
  · refine is_partial_exec_map_family g hpe ?_
    intro n l₀ s₀ hn
    by_cases hl₀ : l₀ = Silent.τ
    · exact Or.inl hl₀
    · obtain ⟨m, hm⟩ := mem_trace_of_external (sys := inst r) hterm hn hl₀
      rw [htr] at hm
      cases m with
      | zero =>
        rw [Stream'.Seq.get?_cons_zero] at hm
        obtain rfl := Option.some.inj hm
        exact Or.inr howns
      | succ k =>
        rw [Stream'.Seq.get?_cons_succ, Stream'.Seq.get?_nil] at hm
        exact absurd hm (by simp)
  · change g.setInstanceState r e.init = g
    rw [hinit]
    exact InstanceFamilyState.setInstanceState_apply_self hr
  · rw [AlterSeq.endState_map (g.setInstanceState r) e hterm, hend]
  · rw [System.trace_map_state _ (inst r)]
    exact htr

/-- The family takes the transition of the instance at round `r` on a label `r` owns, in the map
or not, and the instance then lies in the map. -/
private theorem family_step_owned {inst : ℕ → System σ Label}
    {owns : Label → Option ℕ} {glob : Label → Prop} {act : Label → σ → σ} {initial : σ}
    {r : ℕ} {g : InstanceFamilyState initial act} {l : Label} {μ : PMF σ} {q₁ q' : σ}
    (howns : owns l = some r) (hstep : (inst r).step (g r) l μ) (hq₁ : q₁ ∈ μ.support)
    (h : (inst r).weakLSilent q₁ q') :
    (System.family inst owns glob act initial).step g l (μ.map (g.setInstanceState r)) ∧
      g.setInstanceState r q₁ ∈ (μ.map (g.setInstanceState r)).support ∧
      (System.family inst owns glob act initial).weakLSilent (g.setInstanceState r q₁)
        (g.setInstanceState r q') := by
  refine ⟨(System.family_step_iff inst owns glob act initial).mpr
      (Or.inr (Or.inl ⟨r, howns, μ, hstep, rfl⟩)),
    (PMF.mem_support_map_iff _ _ _).mpr ⟨q₁, hq₁, rfl⟩, ?_⟩
  have htail := System.weakLSilent_family (inst := inst) owns glob act
    (InstanceFamilyState.mem_keys_setInstanceState_self g r q₁)
    (by rw [InstanceFamilyState.setInstanceState_apply_same]; exact h)
  rwa [InstanceFamilyState.setInstanceState_setInstanceState] at htail

/-- A run of the instance at round `r` whose first transition is an external label owned by `r`,
followed by a silent run, is a weak run of the family, at a round in the map or not. -/
theorem System.weakLStep_family_of_step {inst : ℕ → System σ Label}
    (owns : Label → Option ℕ) (glob : Label → Prop) (act : Label → σ → σ) {initial : σ}
    {r : ℕ} {g : InstanceFamilyState initial act} {l : Label} {μ : PMF σ} {q₁ q' : σ}
    (howns : owns l = some r) (hl : ¬ l = Silent.τ) (hstep : (inst r).step (g r) l μ)
    (hq₁ : q₁ ∈ μ.support) (h : (inst r).weakLSilent q₁ q') :
    (System.family inst owns glob act initial).weakLStep g l (g.setInstanceState r q') := by
  obtain ⟨hfamily, hmem, htail⟩ := family_step_owned (glob := glob) howns hstep hq₁ h
  exact System.weakLStep_of_step_weakLSilent hl hfamily hmem htail

/-- A run of the instance at round `r` whose first transition is a silent transition owned by
`r`, followed by a silent run, is a silent run of the family, at a round in the map or not. -/
theorem System.weakLSilent_family_of_step {inst : ℕ → System σ Label}
    (owns : Label → Option ℕ) (glob : Label → Prop) (act : Label → σ → σ) {initial : σ}
    {r : ℕ} {g : InstanceFamilyState initial act} {μ : PMF σ} {q₁ q' : σ}
    (howns : owns Silent.τ = some r) (hstep : (inst r).step (g r) Silent.τ μ)
    (hq₁ : q₁ ∈ μ.support) (h : (inst r).weakLSilent q₁ q') :
    (System.family inst owns glob act initial).weakLSilent g (g.setInstanceState r q') := by
  obtain ⟨hfamily, hmem, htail⟩ := family_step_owned (glob := glob) howns hstep hq₁ h
  exact System.weakLSilent_of_step_weakLSilent hfamily hmem htail

end FamilyEmbedding

/-! ### The congruence -/

/-- Setting related instances at one round preserves the relation of `ForwardSimulation.family`:
the broadcasts are unchanged, both maps gain the round, and the instances at every round are
related. -/
private theorem familyRelation_setInstanceState {σC σA : Type} {Label : Type}
    {R : ℕ → σC → σA → Prop} {actC : Label → σC → σC} {actA : Label → σA → σA}
    {initialC : σC} {initialA : σA}
    {gC : InstanceFamilyState initialC actC} {gA : InstanceFamilyState initialA actA}
    (hBroadcasts : gC.broadcasts = gA.broadcasts)
    (hKeys : gC.instanceMap.keys = gA.instanceMap.keys) (hR : ∀ r, R r (gC r) (gA r))
    {r : ℕ} {x : σC} {y : σA} (hxy : R r x y) :
    (gC.setInstanceState r x).broadcasts = (gA.setInstanceState r y).broadcasts ∧
      (gC.setInstanceState r x).instanceMap.keys = (gA.setInstanceState r y).instanceMap.keys ∧
      ∀ r', R r' ((gC.setInstanceState r x) r') ((gA.setInstanceState r y) r') := by
  refine ⟨hBroadcasts, ?_, fun r' => ?_⟩
  · rw [InstanceFamilyState.keys_setInstanceState, InstanceFamilyState.keys_setInstanceState,
      hKeys]
  · by_cases hr' : r' = r
    · subst hr'
      rw [InstanceFamilyState.setInstanceState_apply_same,
        InstanceFamilyState.setInstanceState_apply_same]
      exact hxy
    · rw [InstanceFamilyState.setInstanceState_apply_ne _ _ hr',
        InstanceFamilyState.setInstanceState_apply_ne _ _ hr']
      exact hR r'

/-- **Forward simulation is a congruence for `System.family`.** Per-instance forward simulations
`R r` lift to the relation that asks for the same broadcasts, the same rounds in the two maps,
and instances related by `R r` at every round `r`. The hypotheses: the broadcast transformations
preserve `R` (`hglob`), and from a related pair of untouched instances, a concrete step on a label
owned by the round is matched by an abstract transition on that label followed by a silent run
(`hUntouchedFirstStep`). Silent and owned steps at a round of the map are matched through the
per-instance simulation; owned steps at an untouched round through `hUntouchedFirstStep`;
broadcast and idle steps by the abstract family's own one-step broadcast and idle transitions. -/
theorem ForwardSimulation.family {σC σA : Type} {Label : Type} [Silent Label]
    {instC : ℕ → System σC Label} {instA : ℕ → System σA Label}
    {R : ℕ → σC → σA → Prop} (owns : Label → Option ℕ) (glob : Label → Prop)
    (actC : Label → σC → σC) (actA : Label → σA → σA) (initialC : σC) (initialA : σA)
    (sim : ∀ r, ForwardSimulation (instC r) (instA r) (R r))
    (hglob : ∀ l, glob l → ∀ r x y, R r x y → R r (actC l x) (actA l y))
    (hUntouchedFirstStep : ∀ (r : ℕ) (broadcasts : List Label) (l : Label), owns l = some r →
      R r (broadcasts.foldr actC initialC) (broadcasts.foldr actA initialA) →
      ∀ μ, (instC r).step (broadcasts.foldr actC initialC) l μ → ∀ x ∈ μ.support,
        ∃ y, R r x y ∧ ∃ ν, (instA r).step (broadcasts.foldr actA initialA) l ν ∧
          ∃ z ∈ ν.support, (instA r).weakLSilent z y) :
    ForwardSimulation (System.family instC owns glob actC initialC)
      (System.family instA owns glob actA initialA)
      (fun gC gA => gC.broadcasts = gA.broadcasts ∧
        gC.instanceMap.keys = gA.instanceMap.keys ∧ ∀ r, R r (gC r) (gA r)) := by
  constructor
  rintro gC gA ⟨hb, hk, hR⟩ l μ hstep g' hg'
  rw [System.family_step_iff instC owns glob actC initialC] at hstep
  rcases hstep with ⟨hτ, r, hr, μr, hstepr, rfl⟩ | ⟨r, howns, μr, hstepr, rfl⟩ |
    ⟨hnτ, hnowns, hg, rfl⟩ | ⟨hnτ, hnowns, hng, rfl⟩
  · -- (i) silent step at a round of the map: match through `sim r`, embed silently.
    rw [PMF.mem_support_map_iff] at hg'
    obtain ⟨x, hx, rfl⟩ := hg'
    obtain ⟨y, hdisj, hRxy⟩ := (sim r).step (gC r) (gA r) (hR r) l μr hstepr x hx
    rcases hdisj with ⟨-, hsil⟩ | ⟨hnτ, -⟩
    · exact ⟨gA.setInstanceState r y,
        Or.inl ⟨hτ, System.weakLSilent_family owns glob actA (hk ▸ hr) hsil⟩,
        familyRelation_setInstanceState hb hk hR hRxy⟩
    · exact absurd hτ hnτ
  · -- (ii) owned step.
    rw [PMF.mem_support_map_iff] at hg'
    obtain ⟨x, hx, rfl⟩ := hg'
    by_cases hr : r ∈ gC.instanceMap.keys
    · -- At a round of the map: match through `sim r`; a τ label goes through the silent
      -- embedding, an external one through the labelled embedding.
      have hrA : r ∈ gA.instanceMap.keys := hk ▸ hr
      obtain ⟨y, hdisj, hRxy⟩ := (sim r).step (gC r) (gA r) (hR r) l μr hstepr x hx
      rcases hdisj with ⟨hτ, hsil⟩ | ⟨hnτ, hlab⟩
      · exact ⟨gA.setInstanceState r y,
          Or.inl ⟨hτ, System.weakLSilent_family owns glob actA hrA hsil⟩,
          familyRelation_setInstanceState hb hk hR hRxy⟩
      · exact ⟨gA.setInstanceState r y,
          Or.inr ⟨hnτ, System.weakLStep_family owns glob actA howns hrA hlab⟩,
          familyRelation_setInstanceState hb hk hR hRxy⟩
    · -- At an untouched round: match through `hUntouchedFirstStep`.
      have hrA : r ∉ gA.instanceMap.keys := hk ▸ hr
      have hC : gC r = gC.broadcasts.foldr actC initialC :=
        InstanceFamilyState.apply_of_notMem hr
      have hA : gA r = gC.broadcasts.foldr actA initialA := by
        rw [InstanceFamilyState.apply_of_notMem hrA, hb, InstanceFamilyState.untouchedInstance]
      have hRr := hR r
      rw [hC, hA] at hRr
      rw [hC] at hstepr
      obtain ⟨y, hRxy, ν, hstepA, z, hz, hsil⟩ :=
        hUntouchedFirstStep r gC.broadcasts l howns hRr μr hstepr x hx
      rw [← hA] at hstepA
      by_cases hτ : l = Silent.τ
      · subst hτ
        exact ⟨gA.setInstanceState r y,
          Or.inl ⟨rfl, System.weakLSilent_family_of_step owns glob actA howns hstepA hz hsil⟩,
          familyRelation_setInstanceState hb hk hR hRxy⟩
      · exact ⟨gA.setInstanceState r y,
          Or.inr ⟨hτ, System.weakLStep_family_of_step owns glob actA howns hτ hstepA hz hsil⟩,
          familyRelation_setInstanceState hb hk hR hRxy⟩
  · -- (iii) broadcast: the abstract family broadcasts in one step.
    rw [PMF.mem_support_pure_iff] at hg'
    subst hg'
    refine ⟨gA.applyBroadcast l,
      Or.inr ⟨hnτ, System.weakLStep_of_step hnτ
        ((System.family_step_iff instA owns glob actA initialA).mpr
          (Or.inr (Or.inr (Or.inl ⟨hnτ, hnowns, hg, rfl⟩))))⟩, ?_, ?_, fun r' => ?_⟩
    · rw [InstanceFamilyState.broadcasts_applyBroadcast,
        InstanceFamilyState.broadcasts_applyBroadcast, hb]
    · rw [InstanceFamilyState.keys_applyBroadcast, InstanceFamilyState.keys_applyBroadcast]
      exact hk
    · rw [InstanceFamilyState.applyBroadcast_apply, InstanceFamilyState.applyBroadcast_apply]
      exact hglob l hg r' _ _ (hR r')
  · -- (iv) idle: the abstract family idles in one step.
    rw [PMF.mem_support_pure_iff] at hg'
    subst hg'
    exact ⟨gA, Or.inr ⟨hnτ, System.weakLStep_of_step hnτ
      ((System.family_step_iff instA owns glob actA initialA).mpr
        (Or.inr (Or.inr (Or.inr ⟨hnτ, hnowns, hng, rfl⟩))))⟩, hb, hk, hR⟩

/-- **The congruence when an untouched abstract instance takes no silent transition.** Let no
label owned by a round be silent, and let the abstract instance have no silent transition at an
untouched state, the initial instance under any list of broadcasts. Then every weak run that
matches a step from an untouched state begins with its visible transition
(`System.exists_step_weakLSilent_of_weakLStep`), and `ForwardSimulation.family` applies with
`hUntouchedFirstStep` derived from the per-round simulations. -/
theorem ForwardSimulation.family_of_noSilentAtUntouched {σC σA : Type} {Label : Type}
    [Silent Label] {instC : ℕ → System σC Label} {instA : ℕ → System σA Label}
    {R : ℕ → σC → σA → Prop} (owns : Label → Option ℕ) (glob : Label → Prop)
    (actC : Label → σC → σC) (actA : Label → σA → σA) (initialC : σC) (initialA : σA)
    (sim : ∀ r, ForwardSimulation (instC r) (instA r) (R r))
    (hglob : ∀ l, glob l → ∀ r x y, R r x y → R r (actC l x) (actA l y))
    (hOwnsSilent : owns Silent.τ = none)
    (hNoSilentAtUntouched : ∀ (r : ℕ) (broadcasts : List Label) (μ : PMF σA),
      ¬ (instA r).step (broadcasts.foldr actA initialA) Silent.τ μ) :
    ForwardSimulation (System.family instC owns glob actC initialC)
      (System.family instA owns glob actA initialA)
      (fun gC gA => gC.broadcasts = gA.broadcasts ∧
        gC.instanceMap.keys = gA.instanceMap.keys ∧ ∀ r, R r (gC r) (gA r)) := by
  refine ForwardSimulation.family owns glob actC actA initialC initialA sim hglob ?_
  intro r broadcasts l howns hR μ hstep x hx
  have hl : ¬ l = Silent.τ := by
    rintro rfl
    rw [hOwnsSilent] at howns
    exact absurd howns (by simp)
  obtain ⟨y, hdisj, hRxy⟩ := (sim r).step _ _ hR l μ hstep x hx
  rcases hdisj with ⟨hτ, -⟩ | ⟨-, hlab⟩
  · exact absurd hτ hl
  · obtain ⟨ν, hstepA, z, hz, hsil⟩ :=
      System.exists_step_weakLSilent_of_weakLStep (hNoSilentAtUntouched r broadcasts) hlab
    exact ⟨y, hRxy, ν, hstepA, z, hz, hsil⟩

end PLTS
