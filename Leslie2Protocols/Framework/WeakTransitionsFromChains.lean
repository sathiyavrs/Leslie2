/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sathiya / Claude
-/

import Leslie2Protocols.Framework.FamilySimulation

/-!
# Weak runs from step chains

`Framework/FamilySimulation.lean` builds the two smallest weak runs by hand: the
single external step (`System.weakLStep_of_step`) and the two-step run
(`weakLStep_tauThen`). Simulations whose abstract side must fire several
internal rules before answering — a chain of Byzantine call registrations, a
core bind, then the return — need runs of unbounded length. This file
supplies them:

* `System.weakLSilent_tauCons` / `System.weakLStep_tauCons` — prepending a
  silent `LStep` to a weak run preserves it;
* `System.weakLSilent_ofChain` — a `List.IsChain` of silent `LStep`s is a
  silent weak run to the chain's last state;
* `System.weakLStep_tausThen` — a `List.IsChain` of silent `LStep`s followed
  by one external `LStep` is a weak `l`-transition, the k-fold generalisation
  of `weakLStep_tauThen`.

The construction is by front-cons on the witness execution: each prepend
extends the run by one transition, so a chain folds into a single terminating
`AlterSeq` without any list-surgery on executions.
-/

open Stream'

namespace PLTS

variable {State Label : Type} [Silent Label] {sys : System State Label}

/-! ### Front-cons surgery on executions -/

omit [Silent Label] in
/-- `Option.elim` of `getLast?` peels the head: the last element of `x :: M` is
read from `M` (falling back to `x`'s second component when `M` is empty). -/
private theorem getLast?_elim_cons (x : Label × State) (M : List (Label × State)) (d : State) :
    ((x :: M).getLast?).elim d Prod.snd = (M.getLast?).elim x.2 Prod.snd := by
  induction M generalizing x d with
  | nil => rfl
  | cons a rest ih => rw [List.getLast?_cons_cons, ih a d, ih a x.2]

/-- Prepending a transition does not change the end state: the run
`⟨q, cons (l₀, q₁) T⟩` ends where `⟨q₁, T⟩` ends. -/
private theorem endState_cons (q q₁ : State) (l₀ : Label) {T : Seq (Label × State)}
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

omit [Silent Label] in
/-- Prepending an `LStep` preserves validity: consing a genuine first
transition onto a valid partial execution yields a valid partial execution. -/
private theorem isPartialExec_cons {q q₁ : State} {l₀ : Label} {T : Seq (Label × State)}
    (hstep : sys.LStep q l₀ q₁) (hpe : is_partial_exec ⟨q₁, T⟩ sys) :
    is_partial_exec ⟨q, Seq.cons (l₀, q₁) T⟩ sys := by
  intro n l s' hn
  cases n with
  | zero =>
    rw [Stream'.Seq.get?_cons_zero] at hn
    injection hn with hn
    injection hn with ha hb
    subst ha
    subst hb
    exact ⟨q, PMF.pure q₁, rfl, hstep, by rw [PMF.mem_support_pure_iff]⟩
  | succ k =>
    rw [Stream'.Seq.get?_cons_succ] at hn
    obtain ⟨s, μ, hst, hstep', hmem⟩ := hpe k l s' hn
    refine ⟨s, μ, ?_, hstep', hmem⟩
    cases k with
    | zero =>
      change ((Seq.cons (l₀, q₁) T).get? 0).map Prod.snd = some s
      rw [Stream'.Seq.get?_cons_zero]
      exact hst
    | succ m =>
      change ((Seq.cons (l₀, q₁) T).get? (m + 1)).map Prod.snd = some s
      rw [Stream'.Seq.get?_cons_succ]
      exact hst

/-- Prepending a `τ`-transition does not change the observable trace. -/
private theorem trace_cons_internal (q q₁ : State) (T : Seq (Label × State)) :
    sys.trace ⟨q, Seq.cons (Silent.τ, q₁) T⟩ = sys.trace ⟨q₁, T⟩ := by
  unfold System.trace
  rw [Stream'.Seq.filter_cons_neg (Silent.τ, q₁) T (by simp)]

/-! ### Prepending a silent step -/

/-- Prepending a silent `LStep` to a silent weak run: `q -τ→ q₁ =ε=> q'` is
`q =ε=> q'`. -/
theorem System.weakLSilent_tauCons {q q₁ q' : State}
    (h : sys.LStep q Silent.τ q₁) (htail : sys.weakLSilent q₁ q') :
    sys.weakLSilent q q' := by
  obtain ⟨e, hterm, hpe, hinit, hend, htr⟩ := htail
  have h' : sys.LStep q Silent.τ e.init := by
    rw [hinit]
    exact h
  refine ⟨⟨q, Seq.cons (Silent.τ, e.init) e.trans⟩,
    Stream'.Seq.terminates_cons_iff.mpr hterm,
    isPartialExec_cons h' hpe, rfl, ?_, ?_⟩
  · rw [endState_cons q e.init Silent.τ hterm]
    exact hend
  · rw [trace_cons_internal q e.init e.trans]
    exact htr

/-- Prepending a silent `LStep` to a labelled weak run: `q -τ→ q₁ =l=> q'` is
`q =l=> q'`. -/
theorem System.weakLStep_tauCons {q q₁ q' : State} {l : Label}
    (h : sys.LStep q Silent.τ q₁) (htail : sys.weakLStep q₁ l q') :
    sys.weakLStep q l q' := by
  obtain ⟨e, hterm, hpe, hinit, hend, htr⟩ := htail
  have h' : sys.LStep q Silent.τ e.init := by
    rw [hinit]
    exact h
  refine ⟨⟨q, Seq.cons (Silent.τ, e.init) e.trans⟩,
    Stream'.Seq.terminates_cons_iff.mpr hterm,
    isPartialExec_cons h' hpe, rfl, ?_, ?_⟩
  · rw [endState_cons q e.init Silent.τ hterm]
    exact hend
  · rw [trace_cons_internal q e.init e.trans]
    exact htr

/-! ### Chains -/

/-- The last entry of a mapped list, read through the map: mapping commutes
with `getLastD` when the default is mapped with it. -/
theorem getLastD_map {α β : Type*} (f : α → β) (d : α) (l : List α) :
    (l.map f).getLastD (f d) = f (l.getLastD d) := by
  induction l generalizing d with
  | nil => rfl
  | cons a t ih => rw [List.map_cons, List.getLastD_cons, List.getLastD_cons, ih]

/-- Extending a chain by one related element. -/
theorem isChain_snoc {α : Type*} {R : α → α → Prop} {a : α} {l : List α} {x : α}
    (h : List.IsChain R (a :: l)) (hx : R (l.getLastD a) x) :
    List.IsChain R (a :: (l ++ [x])) := by
  induction l generalizing a with
  | nil =>
    exact List.isChain_cons_cons.mpr ⟨hx, List.isChain_singleton x⟩
  | cons b l ih =>
    rw [List.cons_append]
    obtain ⟨hab, hbl⟩ := List.isChain_cons_cons.mp h
    refine List.isChain_cons_cons.mpr ⟨hab, ih hbl ?_⟩
    rwa [List.getLastD_cons] at hx

/-- Concatenating two chains that meet at the first one's last state. -/
theorem isChain_trans {α : Type*} {R : α → α → Prop} {a : α} {l₁ l₂ : List α}
    (h₁ : List.IsChain R (a :: l₁)) (h₂ : List.IsChain R (l₁.getLastD a :: l₂)) :
    List.IsChain R (a :: (l₁ ++ l₂)) := by
  induction l₁ generalizing a with
  | nil => exact h₂
  | cons b l ih =>
    rw [List.cons_append]
    obtain ⟨hab, hbl⟩ := List.isChain_cons_cons.mp h₁
    refine List.isChain_cons_cons.mpr ⟨hab, ih hbl ?_⟩
    rwa [List.getLastD_cons] at h₂

/-- A chain of silent `LStep`s is a silent weak run to the chain's last
state. -/
theorem System.weakLSilent_ofChain {q : State} {qs : List State}
    (hchain : List.IsChain (fun a b => sys.LStep a Silent.τ b) (q :: qs)) :
    sys.weakLSilent q (qs.getLastD q) := by
  induction qs generalizing q with
  | nil => exact System.weakLSilent_refl sys q
  | cons q₁ rest ih =>
    rw [List.getLastD_cons]
    obtain ⟨hhead, htail⟩ := List.isChain_cons_cons.mp hchain
    exact System.weakLSilent_tauCons hhead (ih htail)

/-- **The k-fold run.** A chain of silent `LStep`s followed by one external
`LStep` is a weak `l`-transition — the generalisation of `weakLStep_tauThen`
to runs of any length. -/
theorem System.weakLStep_tausThen {q q' : State} {qs : List State} {l : Label}
    (hchain : List.IsChain (fun a b => sys.LStep a Silent.τ b) (q :: qs))
    (hlast : sys.LStep (qs.getLastD q) l q') (hl : ¬ l = Silent.τ) :
    sys.weakLStep q l q' := by
  induction qs generalizing q with
  | nil => exact System.weakLStep_of_step hl hlast
  | cons q₁ rest ih =>
    rw [List.getLastD_cons] at hlast
    obtain ⟨hhead, htail⟩ := List.isChain_cons_cons.mp hchain
    exact System.weakLStep_tauCons hhead (ih htail hlast)

end PLTS
