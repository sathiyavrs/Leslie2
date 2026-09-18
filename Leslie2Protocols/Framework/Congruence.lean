/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sathiya / Claude
-/

import Leslie2Protocols.Framework.WeakRun
import Leslie2Protocols.Framework.SyncProduct
import Leslie2Protocols.Framework.Relabel

/-!
# Forward simulation is a congruence for the composition operators

A forward simulation between labelled transition systems (`ForwardSimulation`,
`Simulation/ForwardLTS.lean`) survives each of the operators a composition is
built from: binary parallel composition, on either side
(`ForwardSimulation.parallel_right`, `ForwardSimulation.parallel_left`); the
full-synchronisation product of a finite family
(`ForwardSimulation.syncProduct`); hiding a set of labels
(`ForwardSimulation.abstract`); and restriction along the left summand of an
extended alphabet (`ForwardSimulation.relabel`).

The proofs share one decomposition. A weak transition `q =l=> q'` is a
finite run whose trace is the single label `l`, so it splits into a silent run,
one transition on `l`, and a second silent run (`System.weakLStep_split`);
`System.weakLStep_ofSplit` assembles a weak transition from those three pieces.
A silent run transports along any state map carrying silent steps to silent
steps (`System.weakLSilent_transport`), which embeds the moving component's
internal run into the composite with the other components held. The transition
on `l` is then matched in one step by the composite itself: a synchronised step
of the product, a `τ`-step of the abstraction when `l` is hidden, or an
`l`-step of the restricted system.

Chains of `LStep`s are the other reading of a weak run, and on a system all of
whose transitions are Dirac (`System.IsLTS`) the two readings agree:
`System.weakLSilent_chain` and `System.weakLStep_chains` invert a run into
chains, where `System.weakLSilent_ofChain` and `System.weakLStep_tausThen`
(`Framework/WeakRun.lean`) build a run from chains.
-/

open Stream'

namespace PLTS

/-! ### Prepending and dropping the first transition of a run -/

section Executions

variable {State Label : Type} {sys : System State Label}

/-- `Option.elim` of `getLast?` peels the head: the last element of `x :: M` is
read from `M`, falling back to `x`'s second component when `M` is empty. -/
theorem getLast?_elim_cons (x : Label × State) (M : List (Label × State)) (d : State) :
    ((x :: M).getLast?).elim d Prod.snd = (M.getLast?).elim x.2 Prod.snd := by
  induction M generalizing x d with
  | nil => rfl
  | cons a rest ih => rw [List.getLast?_cons_cons, ih a d, ih a x.2]

/-- The end state of a transition list is read from its tail. -/
theorem AlterSeq.endStList_cons (q q₁ : State) (l₀ : Label) (L : List (Label × State)) :
    AlterSeq.endStList q ((l₀, q₁) :: L) = AlterSeq.endStList q₁ L :=
  getLast?_elim_cons (l₀, q₁) L q

/-- The end state of a run over a transition list is the list's end state. -/
theorem AlterSeq.endState_ofList (q : State) (L : List (Label × State)) :
    (⟨q, Seq.ofList L⟩ : AlterSeq State Label).endState (Stream'.Seq.terminates_ofList L)
      = AlterSeq.endStList q L := by
  rw [AlterSeq.endState_eq_getLast?, Stream'.Seq.toList_ofList]
  rfl

/-- Prepending a transition does not change the end state: the run
`⟨q, cons (l₀, q₁) T⟩` ends where `⟨q₁, T⟩` ends. -/
theorem AlterSeq.endState_cons (q q₁ : State) (l₀ : Label) {T : Seq (Label × State)}
    (hT : T.Terminates) (h : (Seq.cons (l₀, q₁) T).Terminates) :
    (⟨q, Seq.cons (l₀, q₁) T⟩ : AlterSeq State Label).endState h
      = (⟨q₁, T⟩ : AlterSeq State Label).endState hT := by
  have h1 : (⟨q, Seq.cons (l₀, q₁) T⟩ : AlterSeq State Label).endState h
      = (((Seq.cons (l₀, q₁) T).toList h).getLast?).elim q Prod.snd :=
    AlterSeq.endState_eq_getLast? _ h
  have h2 : (⟨q₁, T⟩ : AlterSeq State Label).endState hT
      = ((T.toList hT).getLast?).elim q₁ Prod.snd :=
    AlterSeq.endState_eq_getLast? _ hT
  rw [h1, h2, Stream'.Seq.toList_cons h]
  exact getLast?_elim_cons (l₀, q₁) (T.toList _) q

/-- Prepending a transition preserves validity: consing a genuine first
transition onto a valid partial execution yields a valid partial execution. -/
theorem is_partial_exec_cons {q q₁ : State} {l₀ : Label} {T : Seq (Label × State)}
    {μ : PMF State} (hstep : sys.step q l₀ μ) (hmem : q₁ ∈ μ.support)
    (hpe : is_partial_exec ⟨q₁, T⟩ sys) :
    is_partial_exec ⟨q, Seq.cons (l₀, q₁) T⟩ sys := by
  intro n l s' hn
  cases n with
  | zero =>
    rw [Stream'.Seq.get?_cons_zero] at hn
    injection hn with hn
    injection hn with ha hb
    subst ha
    subst hb
    exact ⟨q, μ, rfl, hstep, hmem⟩
  | succ k =>
    rw [Stream'.Seq.get?_cons_succ] at hn
    obtain ⟨s, μ', hst, hstep', hmem'⟩ := hpe k l s' hn
    refine ⟨s, μ', ?_, hstep', hmem'⟩
    cases k with
    | zero =>
      change ((Seq.cons (l₀, q₁) T).get? 0).map Prod.snd = some s
      rw [Stream'.Seq.get?_cons_zero]
      exact hst
    | succ m =>
      change ((Seq.cons (l₀, q₁) T).get? (m + 1)).map Prod.snd = some s
      rw [Stream'.Seq.get?_cons_succ]
      exact hst

/-- Dropping the first transition preserves validity: the tail `⟨q₁, T⟩` of a
valid partial execution `⟨q, cons (l₀, q₁) T⟩` is again a valid partial
execution. -/
theorem is_partial_exec_tail {q q₁ : State} {l₀ : Label} {T : Seq (Label × State)}
    (hpe : is_partial_exec ⟨q, Seq.cons (l₀, q₁) T⟩ sys) :
    is_partial_exec ⟨q₁, T⟩ sys := by
  intro n l s' hn
  have hn1 : (Seq.cons (l₀, q₁) T).get? (n + 1) = some (l, s') := by
    rw [Stream'.Seq.get?_cons_succ]; exact hn
  obtain ⟨s, μ, hst, hstep, hmem⟩ := hpe (n + 1) l s' hn1
  refine ⟨s, μ, ?_, hstep, hmem⟩
  rw [← hst]
  cases n with
  | zero =>
    change (some q₁ : Option State) = ((Seq.cons (l₀, q₁) T).get? 0).map Prod.snd
    simp [Stream'.Seq.get?_cons_zero]
  | succ k =>
    change (T.get? k).map Prod.snd = ((Seq.cons (l₀, q₁) T).get? (k + 1)).map Prod.snd
    rw [Stream'.Seq.get?_cons_succ]

/-- The first transition of a valid partial execution is a genuine step with
the second state in its support. -/
theorem is_partial_exec_head {q q₁ : State} {l₀ : Label} {T : Seq (Label × State)}
    (hpe : is_partial_exec ⟨q, Seq.cons (l₀, q₁) T⟩ sys) :
    ∃ μ, sys.step q l₀ μ ∧ q₁ ∈ μ.support := by
  obtain ⟨s, μ, hst, hstep, hmem⟩ := hpe 0 l₀ q₁ (Stream'.Seq.get?_cons_zero (l₀, q₁) T)
  have hs0 : (⟨q, Seq.cons (l₀, q₁) T⟩ : AlterSeq State Label).stateAt 0 = some q := rfl
  rw [hs0] at hst
  obtain rfl : q = s := Option.some.inj hst
  exact ⟨μ, hstep, hmem⟩

/-- On a system all of whose transitions are Dirac, the first transition of a
valid partial execution is an `LStep`. -/
theorem System.IsLTS.lstep_head (hLTS : sys.IsLTS) {q q₁ : State} {l₀ : Label}
    {T : Seq (Label × State)} (hpe : is_partial_exec ⟨q, Seq.cons (l₀, q₁) T⟩ sys) :
    sys.LStep q l₀ q₁ := by
  obtain ⟨μ, hstep, hmem⟩ := is_partial_exec_head hpe
  obtain ⟨x, rfl⟩ := hLTS q l₀ μ hstep
  rw [PMF.mem_support_pure_iff] at hmem
  rw [hmem]
  exact hstep

variable [Silent Label]

/-- Prepending a `τ`-transition does not change the observable trace. -/
theorem System.trace_cons_internal (sys : System State Label) (q q₁ : State)
    (T : Seq (Label × State)) :
    sys.trace ⟨q, Seq.cons (Silent.τ, q₁) T⟩ = sys.trace ⟨q₁, T⟩ := by
  unfold System.trace
  rw [Stream'.Seq.filter_cons_neg (Silent.τ, q₁) T (by simp)]

end Executions

/-! ### Weak runs over a transition list -/

section WeakRuns

variable {State Label : Type} [Silent Label] {sys : System State Label}

/-- A valid empty-trace run over a transition list is a silent weak run. -/
theorem System.weakLSilent_ofList {q : State} {L : List (Label × State)}
    (hpe : is_partial_exec ⟨q, Seq.ofList L⟩ sys)
    (htr : sys.trace ⟨q, Seq.ofList L⟩ = (Seq.nil : Seq Label)) :
    sys.weakLSilent q (AlterSeq.endStList q L) :=
  ⟨⟨q, Seq.ofList L⟩, Stream'.Seq.terminates_ofList L, hpe, rfl,
    AlterSeq.endState_ofList q L, htr⟩

/-- Every silent weak run is carried by a transition list. -/
theorem System.weakLSilent_exists_list {q q' : State} (h : sys.weakLSilent q q') :
    ∃ L : List (Label × State), is_partial_exec ⟨q, Seq.ofList L⟩ sys ∧
      sys.trace ⟨q, Seq.ofList L⟩ = (Seq.nil : Seq Label) ∧
      AlterSeq.endStList q L = q' := by
  obtain ⟨e, hterm, hpe, hinit, hend, htr⟩ := h
  subst hinit
  have he : (⟨e.init, Seq.ofList (e.trans.toList hterm)⟩ : AlterSeq State Label) = e := by
    rw [Stream'.Seq.ofList_toList]
  refine ⟨e.trans.toList hterm, ?_, ?_, ?_⟩
  · rw [he]; exact hpe
  · rw [he]; exact htr
  · rw [← AlterSeq.endState_ofList e.init (e.trans.toList hterm),
      AlterSeq.endState_congr_pub he (Stream'.Seq.terminates_ofList _) hterm]
    exact hend

/-- Every labelled weak run is carried by a transition list. -/
theorem System.weakLStep_exists_list {q q' : State} {l : Label} (h : sys.weakLStep q l q') :
    ∃ L : List (Label × State), is_partial_exec ⟨q, Seq.ofList L⟩ sys ∧
      sys.trace ⟨q, Seq.ofList L⟩ = (Seq.cons l Seq.nil : Seq Label) ∧
      AlterSeq.endStList q L = q' := by
  obtain ⟨e, hterm, hpe, hinit, hend, htr⟩ := h
  subst hinit
  have he : (⟨e.init, Seq.ofList (e.trans.toList hterm)⟩ : AlterSeq State Label) = e := by
    rw [Stream'.Seq.ofList_toList]
  refine ⟨e.trans.toList hterm, ?_, ?_, ?_⟩
  · rw [he]; exact hpe
  · rw [he]; exact htr
  · rw [← AlterSeq.endState_ofList e.init (e.trans.toList hterm),
      AlterSeq.endState_congr_pub he (Stream'.Seq.terminates_ofList _) hterm]
    exact hend

/-! ### Prepending a transition to a weak run -/

/-- Prepending a silent transition to a silent weak run. -/
theorem System.weakLSilent_stepCons {q q₁ q' : State} {μ : PMF State}
    (hstep : sys.step q Silent.τ μ) (hmem : q₁ ∈ μ.support)
    (h : sys.weakLSilent q₁ q') : sys.weakLSilent q q' := by
  obtain ⟨e, hterm, hpe, hinit, hend, htr⟩ := h
  subst hinit
  refine ⟨⟨q, Seq.cons (Silent.τ, e.init) e.trans⟩,
    Stream'.Seq.terminates_cons_iff.mpr hterm,
    is_partial_exec_cons hstep hmem hpe, rfl, ?_, ?_⟩
  · rw [AlterSeq.endState_cons q e.init Silent.τ hterm]
    exact hend
  · rw [System.trace_cons_internal sys q e.init e.trans]
    exact htr

/-- Prepending a silent transition to a labelled weak run. -/
theorem System.weakLStep_stepCons {q q₁ q' : State} {l : Label} {μ : PMF State}
    (hstep : sys.step q Silent.τ μ) (hmem : q₁ ∈ μ.support)
    (h : sys.weakLStep q₁ l q') : sys.weakLStep q l q' := by
  obtain ⟨e, hterm, hpe, hinit, hend, htr⟩ := h
  subst hinit
  refine ⟨⟨q, Seq.cons (Silent.τ, e.init) e.trans⟩,
    Stream'.Seq.terminates_cons_iff.mpr hterm,
    is_partial_exec_cons hstep hmem hpe, rfl, ?_, ?_⟩
  · rw [AlterSeq.endState_cons q e.init Silent.τ hterm]
    exact hend
  · rw [System.trace_cons_internal sys q e.init e.trans]
    exact htr

/-- An external transition followed by a silent weak run is a weak transition
on that label. -/
theorem System.weakLStep_ofStepSilent {q q₁ q' : State} {l : Label} {μ : PMF State}
    (hl : ¬ l = Silent.τ) (hstep : sys.step q l μ) (hmem : q₁ ∈ μ.support)
    (h : sys.weakLSilent q₁ q') : sys.weakLStep q l q' := by
  obtain ⟨e, hterm, hpe, hinit, hend, htr⟩ := h
  subst hinit
  refine ⟨⟨q, Seq.cons (l, e.init) e.trans⟩,
    Stream'.Seq.terminates_cons_iff.mpr hterm,
    is_partial_exec_cons hstep hmem hpe, rfl, ?_, ?_⟩
  · rw [AlterSeq.endState_cons q e.init l hterm]
    exact hend
  · rw [System.trace_cons_external sys q l e.init e.trans hl, htr]

/-! ### Induction along a silent run -/

private theorem weakLSilent_induction_ofList {State Label : Type} [Silent Label]
    {sys : System State Label} {P : State → Prop}
    (hcons : ∀ s μ x, sys.step s Silent.τ μ → x ∈ μ.support → P x → P s) :
    ∀ (L : List (Label × State)) (q : State), is_partial_exec ⟨q, Seq.ofList L⟩ sys →
      sys.trace ⟨q, Seq.ofList L⟩ = (Seq.nil : Seq Label) →
      P (AlterSeq.endStList q L) → P q := by
  intro L
  induction L with
  | nil => intro q _ _ hP; exact hP
  | cons p rest ih =>
    intro q hpe htr hP
    obtain ⟨l₀, q₁⟩ := p
    rw [Stream'.Seq.ofList_cons] at hpe htr
    have hl0 : l₀ = Silent.τ := by
      by_contra hne
      rw [System.trace_cons_external sys q l₀ q₁ (Seq.ofList rest) hne] at htr
      exact absurd htr Stream'.Seq.cons_ne_nil
    subst hl0
    obtain ⟨μ, hstep, hmem⟩ := is_partial_exec_head hpe
    rw [AlterSeq.endStList_cons] at hP
    rw [System.trace_cons_internal sys q q₁ (Seq.ofList rest)] at htr
    exact hcons q μ q₁ hstep hmem (ih q₁ (is_partial_exec_tail hpe) htr hP)

/-- **Induction along a silent run.** A property that holds at the run's end
state and is inherited backwards across a silent transition holds at its start
state. -/
theorem System.weakLSilent_induction {P : State → Prop} {q q' : State}
    (hbase : P q') (hcons : ∀ s μ x, sys.step s Silent.τ μ → x ∈ μ.support → P x → P s)
    (h : sys.weakLSilent q q') : P q := by
  obtain ⟨L, hpe, htr, hend⟩ := System.weakLSilent_exists_list h
  refine weakLSilent_induction_ofList hcons L q hpe htr ?_
  rw [hend]
  exact hbase

/-- Silent runs compose. -/
theorem System.weakLSilent_trans {q q₁ q' : State}
    (h₁ : sys.weakLSilent q q₁) (h₂ : sys.weakLSilent q₁ q') : sys.weakLSilent q q' :=
  System.weakLSilent_induction (P := fun s => sys.weakLSilent s q') h₂
    (fun _ _ _ hs hx hP => System.weakLSilent_stepCons hs hx hP) h₁

/-- Prefixing a weak transition by a silent run. -/
theorem System.weakLStep_silentCons {q q₁ q' : State} {l : Label}
    (h₁ : sys.weakLSilent q q₁) (h₂ : sys.weakLStep q₁ l q') : sys.weakLStep q l q' :=
  System.weakLSilent_induction (P := fun s => sys.weakLStep s l q') h₂
    (fun _ _ _ hs hx hP => System.weakLStep_stepCons hs hx hP) h₁

/-- **Assembling a weak transition** from a silent run, one external transition
and a second silent run. -/
theorem System.weakLStep_ofSplit {q q₁ q₂ q' : State} {l : Label} {μ : PMF State}
    (hl : ¬ l = Silent.τ) (h₁ : sys.weakLSilent q q₁) (hstep : sys.step q₁ l μ)
    (hmem : q₂ ∈ μ.support) (h₂ : sys.weakLSilent q₂ q') : sys.weakLStep q l q' :=
  System.weakLStep_silentCons h₁ (System.weakLStep_ofStepSilent hl hstep hmem h₂)

/-! ### Splitting a weak transition -/

private theorem weakLStep_split_ofList {State Label : Type} [Silent Label]
    {sys : System State Label} {l : Label} :
    ∀ (L : List (Label × State)) (q : State), is_partial_exec ⟨q, Seq.ofList L⟩ sys →
      sys.trace ⟨q, Seq.ofList L⟩ = (Seq.cons l Seq.nil : Seq Label) →
      ¬ l = Silent.τ ∧ ∃ (q₁ q₂ : State) (μ : PMF State), sys.weakLSilent q q₁ ∧
        sys.step q₁ l μ ∧ q₂ ∈ μ.support ∧
        sys.weakLSilent q₂ (AlterSeq.endStList q L) := by
  intro L
  induction L with
  | nil =>
    intro q _ htr
    rw [Stream'.Seq.ofList_nil, System.trace_init] at htr
    exact absurd htr.symm Stream'.Seq.cons_ne_nil
  | cons p rest ih =>
    intro q hpe htr
    obtain ⟨l₀, q₁⟩ := p
    rw [Stream'.Seq.ofList_cons] at hpe htr
    obtain ⟨μ, hstep, hmem⟩ := is_partial_exec_head hpe
    have hpe' : is_partial_exec ⟨q₁, Seq.ofList rest⟩ sys := is_partial_exec_tail hpe
    rw [AlterSeq.endStList_cons]
    by_cases hl0 : l₀ = Silent.τ
    · subst hl0
      rw [System.trace_cons_internal sys q q₁ (Seq.ofList rest)] at htr
      obtain ⟨hl, a, b, ν, hpre, hstepA, hmemA, hpost⟩ := ih q₁ hpe' htr
      exact ⟨hl, a, b, ν, System.weakLSilent_stepCons hstep hmem hpre, hstepA, hmemA, hpost⟩
    · rw [System.trace_cons_external sys q l₀ q₁ (Seq.ofList rest) hl0] at htr
      obtain ⟨rfl, htail⟩ := Stream'.Seq.cons_eq_cons.mp htr
      exact ⟨hl0, q, q₁, μ, System.weakLSilent_refl sys q, hstep, hmem,
        System.weakLSilent_ofList hpe' htail⟩

/-- **Splitting a weak transition.** A weak transition on `l` is a silent run,
one transition on `l`, and a second silent run; its label is external. -/
theorem System.weakLStep_split {q q' : State} {l : Label} (h : sys.weakLStep q l q') :
    ¬ l = Silent.τ ∧ ∃ (q₁ q₂ : State) (μ : PMF State), sys.weakLSilent q q₁ ∧
      sys.step q₁ l μ ∧ q₂ ∈ μ.support ∧ sys.weakLSilent q₂ q' := by
  obtain ⟨L, hpe, htr, hend⟩ := System.weakLStep_exists_list h
  rw [← hend]
  exact weakLStep_split_ofList L q hpe htr

/-- Appending a silent run to a weak transition. -/
theorem System.weakLStep_silentSnoc {q q₁ q' : State} {l : Label}
    (h₁ : sys.weakLStep q l q₁) (h₂ : sys.weakLSilent q₁ q') : sys.weakLStep q l q' := by
  obtain ⟨hl, a, b, μ, hpre, hstep, hmem, hpost⟩ := System.weakLStep_split h₁
  exact System.weakLStep_ofSplit hl hpre hstep hmem (System.weakLSilent_trans hpost h₂)

end WeakRuns

/-! ### Transporting a silent run -/

/-- **A silent run transports along a state map** that carries every silent
transition to a silent transition, outcome by outcome. The two systems may
range over different state spaces and different alphabets. -/
theorem System.weakLSilent_transport {S S' L L' : Type} [Silent L] [Silent L']
    {sys : System S L} {sys' : System S' L'} (f : S → S')
    (hf : ∀ s μ x, sys.step s (Silent.τ : L) μ → x ∈ μ.support →
      ∃ ν, sys'.step (f s) (Silent.τ : L') ν ∧ f x ∈ ν.support)
    {q q' : S} (h : sys.weakLSilent q q') : sys'.weakLSilent (f q) (f q') :=
  System.weakLSilent_induction (P := fun s => sys'.weakLSilent (f s) (f q'))
    (System.weakLSilent_refl sys' (f q'))
    (fun s μ x hs hx hP => by
      obtain ⟨ν, hν, hfx⟩ := hf s μ x hs hx
      exact System.weakLSilent_stepCons hν hfx hP) h

/-! ### Weak runs as chains of `LStep`s -/

section Chains

variable {State Label : Type} [Silent Label] {sys : System State Label}

/-- **A silent run of an LTS is a chain of silent `LStep`s**, the converse of
`System.weakLSilent_ofChain`. -/
theorem System.weakLSilent_chain (hLTS : sys.IsLTS) {q q' : State}
    (h : sys.weakLSilent q q') :
    ∃ qs : List State, List.IsChain (fun a b => sys.LStep a Silent.τ b) (q :: qs) ∧
      qs.getLastD q = q' := by
  refine System.weakLSilent_induction
    (P := fun s => ∃ qs : List State,
      List.IsChain (fun a b => sys.LStep a Silent.τ b) (s :: qs) ∧ qs.getLastD s = q')
    ⟨[], List.isChain_singleton q', rfl⟩ ?_ h
  rintro s μ x hs hx ⟨qs, hchain, hlast⟩
  obtain ⟨y, rfl⟩ := hLTS s Silent.τ μ hs
  rw [PMF.mem_support_pure_iff] at hx
  subst hx
  refine ⟨x :: qs, List.isChain_cons_cons.mpr ⟨hs, hchain⟩, ?_⟩
  rw [List.getLastD_cons]
  exact hlast

/-- **A weak transition of an LTS is two chains of silent `LStep`s around one
external `LStep`**, the converse of `System.weakLStep_tausThen` followed by a
silent chain. -/
theorem System.weakLStep_chains (hLTS : sys.IsLTS) {q q' : State} {l : Label}
    (h : sys.weakLStep q l q') :
    ∃ (qs₁ : List State) (q₂ : State) (qs₂ : List State),
      List.IsChain (fun a b => sys.LStep a Silent.τ b) (q :: qs₁) ∧
      sys.LStep (qs₁.getLastD q) l q₂ ∧
      List.IsChain (fun a b => sys.LStep a Silent.τ b) (q₂ :: qs₂) ∧
      qs₂.getLastD q₂ = q' := by
  obtain ⟨-, a, b, μ, hpre, hstep, hmem, hpost⟩ := System.weakLStep_split h
  obtain ⟨qs₁, hchain₁, hlast₁⟩ := System.weakLSilent_chain hLTS hpre
  obtain ⟨qs₂, hchain₂, hlast₂⟩ := System.weakLSilent_chain hLTS hpost
  obtain ⟨y, rfl⟩ := hLTS a l μ hstep
  rw [PMF.mem_support_pure_iff] at hmem
  subst hmem
  refine ⟨qs₁, b, qs₂, hchain₁, ?_, hchain₂, hlast₂⟩
  rw [hlast₁]
  exact hstep

end Chains

/-! ### Binary parallel composition -/

section Parallel

variable {S₁ S₂ Label : Type} [Silent Label] {sys₁ : System S₁ Label} {sys₂ : System S₂ Label}

/-- A silent run of the left component embeds into the composition, the right
component held. -/
theorem System.weakLSilent_parallel_left (b : S₂) {a a' : S₁}
    (h : sys₁.weakLSilent a a') : (sys₁.parallel sys₂).weakLSilent (a, b) (a', b) := by
  refine System.weakLSilent_transport (f := fun x => (x, b)) ?_ h
  intro s μ x hs hx
  refine ⟨prodPMF μ (PMF.pure b),
    (System.parallel_step sys₁ sys₂ (s, b) Silent.τ _).mpr (Or.inr (Or.inl ⟨rfl, μ, hs, rfl⟩)),
    ?_⟩
  exact mem_support_prodPMF.mpr ⟨hx, (PMF.mem_support_pure_iff _ _).mpr rfl⟩

/-- A silent run of the right component embeds into the composition, the left
component held. -/
theorem System.weakLSilent_parallel_right (a : S₁) {b b' : S₂}
    (h : sys₂.weakLSilent b b') : (sys₁.parallel sys₂).weakLSilent (a, b) (a, b') := by
  refine System.weakLSilent_transport (f := fun y => (a, y)) ?_ h
  intro s μ x hs hx
  refine ⟨prodPMF (PMF.pure a) μ,
    (System.parallel_step sys₁ sys₂ (a, s) Silent.τ _).mpr (Or.inr (Or.inr ⟨rfl, μ, hs, rfl⟩)),
    ?_⟩
  exact mem_support_prodPMF.mpr ⟨(PMF.mem_support_pure_iff _ _).mpr rfl, hx⟩

end Parallel

section ParallelCongruence

variable {SC SA SB Label : Type} [Silent Label]
  {sysC : System SC Label} {sysA : System SA Label} {R : SC → SA → Prop}

/-- **Forward simulation is a congruence for `System.parallel`, the held
component on the right.** The composite relation pairs the simulation on the
first coordinate with equality on the second: the held component is the same
system on both sides, so its state is matched by itself. -/
theorem ForwardSimulation.parallel_right (sim : ForwardSimulation sysC sysA R)
    (sysB : System SB Label) :
    ForwardSimulation (sysC.parallel sysB) (sysA.parallel sysB)
      (fun p q => R p.1 q.1 ∧ p.2 = q.2) := by
  constructor
  rintro ⟨c, b⟩ ⟨a, b₂⟩ ⟨hR, rfl⟩ l μ hstep ⟨c', b'⟩ hmem
  rw [System.parallel_step] at hstep
  rcases hstep with ⟨hl, μ₁, μ₂, hC, hB, rfl⟩ | ⟨hτ, μ₁, hC, rfl⟩ | ⟨hτ, μ₂, hB, rfl⟩
  · -- synchronised visible step: both components move on `l`
    rw [mem_support_prodPMF] at hmem
    obtain ⟨hc', hb'⟩ := hmem
    obtain ⟨a₂, hdisj, hR'⟩ := sim.step c a hR l μ₁ hC c' hc'
    rcases hdisj with ⟨hτ, -⟩ | ⟨-, hlab⟩
    · exact absurd hτ hl
    · obtain ⟨-, x, y, ν, hpre, hstepA, hmemA, hpost⟩ := System.weakLStep_split hlab
      have hsync : (sysA.parallel sysB).step (x, b) l (prodPMF ν μ₂) :=
        (System.parallel_step sysA sysB (x, b) l _).mpr (Or.inl ⟨hl, ν, μ₂, hstepA, hB, rfl⟩)
      refine ⟨(a₂, b'), Or.inr ⟨hl, ?_⟩, hR', rfl⟩
      exact System.weakLStep_ofSplit hl (System.weakLSilent_parallel_left b hpre) hsync
        (mem_support_prodPMF.mpr ⟨hmemA, hb'⟩) (System.weakLSilent_parallel_left b' hpost)
  · -- interleaved silent step of the simulated component
    subst hτ
    rw [mem_support_prodPMF, PMF.mem_support_pure_iff] at hmem
    obtain ⟨hc', rfl⟩ := hmem
    obtain ⟨a₂, hdisj, hR'⟩ := sim.step c a hR Silent.τ μ₁ hC c' hc'
    rcases hdisj with ⟨-, hsil⟩ | ⟨hnτ, -⟩
    · exact ⟨(a₂, b'), Or.inl ⟨rfl, System.weakLSilent_parallel_left b' hsil⟩, hR', rfl⟩
    · exact absurd rfl hnτ
  · -- interleaved silent step of the held component
    subst hτ
    rw [mem_support_prodPMF, PMF.mem_support_pure_iff] at hmem
    obtain ⟨rfl, hb'⟩ := hmem
    refine ⟨(a, b'), Or.inl ⟨rfl, ?_⟩, hR, rfl⟩
    exact System.weakLSilent_parallel_right a
      (System.weakLSilent_stepCons hB hb' (System.weakLSilent_refl sysB b'))

/-- **Forward simulation is a congruence for `System.parallel`, the held
component on the left.** -/
theorem ForwardSimulation.parallel_left (sim : ForwardSimulation sysC sysA R)
    (sysB : System SB Label) :
    ForwardSimulation (sysB.parallel sysC) (sysB.parallel sysA)
      (fun p q => p.1 = q.1 ∧ R p.2 q.2) := by
  constructor
  rintro ⟨b, c⟩ ⟨b₂, a⟩ ⟨rfl, hR⟩ l μ hstep ⟨b', c'⟩ hmem
  rw [System.parallel_step] at hstep
  rcases hstep with ⟨hl, μ₁, μ₂, hB, hC, rfl⟩ | ⟨hτ, μ₁, hB, rfl⟩ | ⟨hτ, μ₂, hC, rfl⟩
  · -- synchronised visible step: both components move on `l`
    rw [mem_support_prodPMF] at hmem
    obtain ⟨hb', hc'⟩ := hmem
    obtain ⟨a₂, hdisj, hR'⟩ := sim.step c a hR l μ₂ hC c' hc'
    rcases hdisj with ⟨hτ, -⟩ | ⟨-, hlab⟩
    · exact absurd hτ hl
    · obtain ⟨-, x, y, ν, hpre, hstepA, hmemA, hpost⟩ := System.weakLStep_split hlab
      have hsync : (sysB.parallel sysA).step (b, x) l (prodPMF μ₁ ν) :=
        (System.parallel_step sysB sysA (b, x) l _).mpr (Or.inl ⟨hl, μ₁, ν, hB, hstepA, rfl⟩)
      refine ⟨(b', a₂), Or.inr ⟨hl, ?_⟩, rfl, hR'⟩
      exact System.weakLStep_ofSplit hl (System.weakLSilent_parallel_right b hpre) hsync
        (mem_support_prodPMF.mpr ⟨hb', hmemA⟩) (System.weakLSilent_parallel_right b' hpost)
  · -- interleaved silent step of the held component
    subst hτ
    rw [mem_support_prodPMF, PMF.mem_support_pure_iff] at hmem
    obtain ⟨hb', rfl⟩ := hmem
    refine ⟨(b', a), Or.inl ⟨rfl, ?_⟩, rfl, hR⟩
    exact System.weakLSilent_parallel_left a
      (System.weakLSilent_stepCons hB hb' (System.weakLSilent_refl sysB b'))
  · -- interleaved silent step of the simulated component
    subst hτ
    rw [mem_support_prodPMF, PMF.mem_support_pure_iff] at hmem
    obtain ⟨rfl, hc'⟩ := hmem
    obtain ⟨a₂, hdisj, hR'⟩ := sim.step c a hR Silent.τ μ₂ hC c' hc'
    rcases hdisj with ⟨-, hsil⟩ | ⟨hnτ, -⟩
    · exact ⟨(b', a₂), Or.inl ⟨rfl, System.weakLSilent_parallel_right b' hsil⟩, rfl, hR'⟩
    · exact absurd rfl hnτ

end ParallelCongruence

/-! ### The full-synchronisation product of a finite family -/

section SyncProduct

variable {ι : Type} [Fintype ι] [DecidableEq ι] {SA : ι → Type} {Label : Type} [Silent Label]

/-- A silent run at one coordinate embeds into the product, the other
coordinates held. -/
theorem System.weakLSilent_syncProduct_update {A : ∀ i, System (SA i) Label}
    (t : ∀ i, SA i) (i : ι) {x y : SA i} (h : (A i).weakLSilent x y) :
    (System.syncProduct A).weakLSilent (Function.update t i x) (Function.update t i y) := by
  refine System.weakLSilent_transport (f := fun z => Function.update t i z) ?_ h
  intro u μ z hu hz
  refine ⟨piPMF (Function.update (fun j => PMF.pure (Function.update t i u j)) i μ),
    (System.syncProduct_step A (Function.update t i u) Silent.τ _).mpr
      (Or.inr ⟨rfl, i, μ, by rw [Function.update_self]; exact hu, rfl⟩), ?_⟩
  rw [piPMF_update_pure, PMF.mem_support_map_iff]
  exact ⟨z, hz, Function.update_idem ..⟩

/-- Silent runs at every coordinate embed into the product: the coordinates are
moved one at a time, the others held. -/
theorem System.weakLSilent_syncProduct {A : ∀ i, System (SA i) Label} {t u : ∀ i, SA i}
    (h : ∀ i, (A i).weakLSilent (t i) (u i)) : (System.syncProduct A).weakLSilent t u := by
  classical
  suffices H : ∀ S : Finset ι,
      (System.syncProduct A).weakLSilent t (fun j => if j ∈ S then u j else t j) by
    have h1 := H Finset.univ
    simpa using h1
  intro S
  induction S using Finset.induction_on with
  | empty => simpa using System.weakLSilent_refl (System.syncProduct A) t
  | @insert i S hi ih =>
    have hkey : (fun j => if j ∈ insert i S then u j else t j)
        = Function.update (fun j => if j ∈ S then u j else t j) i (u i) := by
      funext j
      by_cases hj : j = i
      · subst hj; rw [Function.update_self]; simp
      · rw [Function.update_of_ne hj]; simp [hj, Finset.mem_insert]
    rw [hkey]
    refine System.weakLSilent_trans ih ?_
    have heq : Function.update (fun j => if j ∈ S then u j else t j) i (t i)
        = (fun j => if j ∈ S then u j else t j) := by
      funext j
      by_cases hj : j = i
      · subst hj; rw [Function.update_self]; simp [hi]
      · rw [Function.update_of_ne hj]
    have hrun := System.weakLSilent_syncProduct_update
      (fun j => if j ∈ S then u j else t j) i (h i)
    rwa [heq] at hrun

end SyncProduct

/-- **Forward simulation is a congruence for `System.syncProduct`.** Per-component
forward simulations lift to the pointwise relation on the product. A silent step
moves one component, which the component's own silent answer matches with the
others held; a visible step moves every component at once, and the product of
the components' answers is a silent run of the product, one synchronised
transition on the label, and a second silent run. -/
theorem ForwardSimulation.syncProduct {ι : Type} [Fintype ι] [DecidableEq ι]
    {SC SA : ι → Type} {Label : Type} [Silent Label]
    {C : ∀ i, System (SC i) Label} {A : ∀ i, System (SA i) Label}
    {R : ∀ i, SC i → SA i → Prop} (sim : ∀ i, ForwardSimulation (C i) (A i) (R i)) :
    ForwardSimulation (System.syncProduct C) (System.syncProduct A)
      (fun s t => ∀ i, R i (s i) (t i)) := by
  classical
  constructor
  intro s t hR l μ hstep s' hmem
  rw [System.syncProduct_step] at hstep
  rcases hstep with ⟨hl, μ_, hsteps, rfl⟩ | ⟨hτ, i, μ_i, hstepi, rfl⟩
  · -- synchronised visible step: every component moves on `l`
    rw [mem_support_piPMF] at hmem
    have hans : ∀ i, ∃ y, (A i).weakLStep (t i) l y ∧ R i (s' i) y := by
      intro i
      obtain ⟨y, hdisj, hR'⟩ :=
        (sim i).step (s i) (t i) (hR i) l (μ_ i) (hsteps i) (s' i) (hmem i)
      rcases hdisj with ⟨hτ, -⟩ | ⟨-, hlab⟩
      · exact absurd hτ hl
      · exact ⟨y, hlab, hR'⟩
    choose y hy hRy using hans
    have hsplit : ∀ i, ∃ (x z : SA i) (ν : PMF (SA i)),
        (A i).weakLSilent (t i) x ∧ (A i).step x l ν ∧ z ∈ ν.support ∧
          (A i).weakLSilent z (y i) := by
      intro i
      obtain ⟨-, x, z, ν, h1, h2, h3, h4⟩ := System.weakLStep_split (hy i)
      exact ⟨x, z, ν, h1, h2, h3, h4⟩
    choose x z ν hpre hstepA hmemA hpost using hsplit
    have hsync : (System.syncProduct A).step x l (piPMF ν) :=
      (System.syncProduct_step A x l _).mpr (Or.inl ⟨hl, ν, hstepA, rfl⟩)
    exact ⟨y, Or.inr ⟨hl, System.weakLStep_ofSplit hl (System.weakLSilent_syncProduct hpre)
      hsync (mem_support_piPMF.mpr hmemA) (System.weakLSilent_syncProduct hpost)⟩, hRy⟩
  · -- interleaved silent step: one component moves
    subst hτ
    rw [piPMF_update_pure, PMF.mem_support_map_iff] at hmem
    obtain ⟨w, hw, rfl⟩ := hmem
    obtain ⟨v, hdisj, hR'⟩ := (sim i).step (s i) (t i) (hR i) Silent.τ μ_i hstepi w hw
    rcases hdisj with ⟨-, hsil⟩ | ⟨hnτ, -⟩
    · refine ⟨Function.update t i v, Or.inl ⟨rfl, ?_⟩, ?_⟩
      · have hrun := System.weakLSilent_syncProduct_update t i hsil
        rwa [Function.update_eq_self] at hrun
      · intro j
        by_cases hj : j = i
        · subst hj
          rw [Function.update_self, Function.update_self]
          exact hR'
        · rw [Function.update_of_ne hj, Function.update_of_ne hj]
          exact hR j
    · exact absurd rfl hnτ

/-! ### Hiding a set of labels -/

section Abstract

variable {S T Label : Type} [Silent Label] {sysC : System S Label} {sysA : System T Label}

/-- A silent transition of a system is a silent transition of its abstraction:
hiding only adds `τ`-transitions. -/
theorem System.abstract_tau_step {sys : System S Label} (L : Set Label) {s : S} {μ : PMF S}
    (h : sys.step s Silent.τ μ) : (sys.abstract L).step s Silent.τ μ := by
  by_cases hτ : (Silent.τ : Label) ∈ L
  · exact Or.inl ⟨rfl, Silent.τ, hτ, h⟩
  · exact Or.inr ⟨hτ, h⟩

/-- A silent run survives hiding. -/
theorem System.weakLSilent_abstract {sys : System S Label} (L : Set Label) {q q' : S}
    (h : sys.weakLSilent q q') : (sys.abstract L).weakLSilent q q' :=
  System.weakLSilent_transport (f := id)
    (fun _ μ _ hs hx => ⟨μ, System.abstract_tau_step L hs, hx⟩) h

/-- **Forward simulation is a congruence for `System.abstract`.** A transition
on a hidden label is a `τ`-transition of the abstraction, so the abstract
answer to it is the answer's silent prefix, its transition on the hidden label
read as a `τ`-transition, and its silent suffix; a transition on a label
outside `L` keeps its label on both sides. -/
theorem ForwardSimulation.abstract {R : S → T → Prop} (sim : ForwardSimulation sysC sysA R)
    (L : Set Label) : ForwardSimulation (sysC.abstract L) (sysA.abstract L) R := by
  constructor
  intro q₁ q₂ hR l' μ hstep q₁' hq₁'
  rw [System.abstract_step] at hstep
  rcases hstep with ⟨rfl, l, hlL, hC⟩ | ⟨hl'L, hC⟩
  · -- a hidden label, read as `τ`
    obtain ⟨q₂', hdisj, hR'⟩ := sim.step q₁ q₂ hR l μ hC q₁' hq₁'
    rcases hdisj with ⟨-, hsil⟩ | ⟨-, hlab⟩
    · exact ⟨q₂', Or.inl ⟨rfl, System.weakLSilent_abstract L hsil⟩, hR'⟩
    · obtain ⟨-, x, z, ν, hpre, hstepA, hmemA, hpost⟩ := System.weakLStep_split hlab
      have hmid : (sysA.abstract L).step x Silent.τ ν := Or.inl ⟨rfl, l, hlL, hstepA⟩
      refine ⟨q₂', Or.inl ⟨rfl, ?_⟩, hR'⟩
      exact System.weakLSilent_trans (System.weakLSilent_abstract L hpre)
        (System.weakLSilent_stepCons hmid hmemA (System.weakLSilent_abstract L hpost))
  · -- a label outside the hidden set
    obtain ⟨q₂', hdisj, hR'⟩ := sim.step q₁ q₂ hR l' μ hC q₁' hq₁'
    rcases hdisj with ⟨hτ, hsil⟩ | ⟨hnτ, hlab⟩
    · exact ⟨q₂', Or.inl ⟨hτ, System.weakLSilent_abstract L hsil⟩, hR'⟩
    · obtain ⟨-, x, z, ν, hpre, hstepA, hmemA, hpost⟩ := System.weakLStep_split hlab
      have hmid : (sysA.abstract L).step x l' ν := Or.inr ⟨hl'L, hstepA⟩
      refine ⟨q₂', Or.inr ⟨hnτ, ?_⟩, hR'⟩
      exact System.weakLStep_ofSplit hnτ (System.weakLSilent_abstract L hpre) hmid hmemA
        (System.weakLSilent_abstract L hpost)

end Abstract

/-! ### Restriction along the left summand of an extended alphabet -/

section Relabel

variable {S T Label Extra : Type} [Silent Label]
  {sysC : System S (Label ⊕ Extra)} {sysA : System T (Label ⊕ Extra)}

/-- A silent run survives the restriction: the silent label of the extended
alphabet is the silent label of the base alphabet, injected on the left. -/
theorem System.weakLSilent_relabel {sys : System S (Label ⊕ Extra)} {q q' : S}
    (h : sys.weakLSilent q q') : sys.relabel.weakLSilent q q' :=
  System.weakLSilent_transport (sys := sys) (sys' := sys.relabel) (f := id)
    (fun _ μ _ hs hx => ⟨μ, hs, hx⟩) h

/-- **Forward simulation is a congruence for `System.relabel`.** Both systems
are read over the base alphabet along the same left embedding: a transition of
the restricted system on `l` is a transition on `Sum.inl l`, and the abstract
answer to it is built from its silent prefix, its transition on `Sum.inl l`
read as a transition on `l`, and its silent suffix. -/
theorem ForwardSimulation.relabel {R : S → T → Prop} (sim : ForwardSimulation sysC sysA R) :
    ForwardSimulation sysC.relabel sysA.relabel R := by
  constructor
  intro q₁ q₂ hR l μ hstep q₁' hq₁'
  obtain ⟨q₂', hdisj, hR'⟩ := sim.step q₁ q₂ hR (Sum.inl l) μ hstep q₁' hq₁'
  rcases hdisj with ⟨hτ, hsil⟩ | ⟨hnτ, hlab⟩
  · exact ⟨q₂', Or.inl ⟨(inl_eq_tau_iff l).mp hτ, System.weakLSilent_relabel hsil⟩, hR'⟩
  · have hlτ : ¬ l = (Silent.τ : Label) := fun h => hnτ ((inl_eq_tau_iff l).mpr h)
    obtain ⟨-, x, z, ν, hpre, hstepA, hmemA, hpost⟩ := System.weakLStep_split hlab
    have hmid : sysA.relabel.step x l ν := hstepA
    refine ⟨q₂', Or.inr ⟨hlτ, ?_⟩, hR'⟩
    exact System.weakLStep_ofSplit hlτ (System.weakLSilent_relabel hpre) hmid hmemA
      (System.weakLSilent_relabel hpost)

end Relabel

/-! ### Reading a system over a twice-refined alphabet -/

/-- Two successive read-backs are the read-back along the composite partial
label map. -/
theorem System.mapIdle_mapIdle {S L L' L'' : Type} (φ : L' → Option L) (ψ : L'' → Option L')
    (sys : System S L) :
    (sys.mapIdle φ).mapIdle ψ = sys.mapIdle (fun l => (ψ l).bind φ) := by
  unfold System.mapIdle
  congr 1
  funext s l'' μ
  cases hψ : ψ l'' with
  | none => simp [hψ]
  | some l' => cases hφ : φ l' <;> simp [hψ, hφ]

/-! ### Axiom check

The five congruences are pinned to the clean axiom list
`[propext, Classical.choice, Quot.sound]`. -/

/-- info: 'PLTS.ForwardSimulation.parallel_right' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ForwardSimulation.parallel_right

/-- info: 'PLTS.ForwardSimulation.parallel_left' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ForwardSimulation.parallel_left

/-- info: 'PLTS.ForwardSimulation.syncProduct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ForwardSimulation.syncProduct

/-- info: 'PLTS.ForwardSimulation.abstract' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ForwardSimulation.abstract

/-- info: 'PLTS.ForwardSimulation.relabel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ForwardSimulation.relabel

end PLTS
