/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sathiya / Claude
-/

import Leslie2Protocols.Framework.TraceDistributionSupport
import Leslie2.Systems.LTS
import Mathlib.Data.Finmap

/-!
# Idle padding, label pullbacks and ℕ-indexed instance families

The three combinators that make the full-synchronisation `System.parallel`
emulate the blueprint's sync-set composition `∥_S`:

* `System.withIdle sys busy` — `sys` plus idle self-loops `s —l→ δ_s` on every
  label outside `busy`. Under full synchronisation, a non-participant is then
  unchanged on every label it does not own.

* `System.mapIdle φ sys` — `sys` read over a finer alphabet `L'` along the
  partial label map `φ : L' → Option L`: a label `l'` with `φ l' = some l`
  delegates to the `l`-transitions, and a label outside the image of `φ`
  leaves the system idle. This is how a component whose alphabet is coarser
  joins a composition over a finer one.

* `System.family inst owns glob act initial` — the ℕ-indexed family of the instances
  `inst r` over a shared alphabet. Its state, `InstanceFamilyState initial act`, records the
  broadcast labels applied so far and a finite map of the instances the family has touched. A
  round not in the map is untouched and reads as `untouchedInstance`, the instance `initial`
  under the recorded broadcasts. The family has four step disjuncts:
  1. *silent*: on `τ`, the instance at one round of the map moves; the successor
     distribution is `μr.map (g.setInstanceState r)`, so no product of distributions arises.
  2. *owned*: on a label owned by round `r` (`owns l = some r`), the instance at `r` moves,
     in the map or not.
  3. *broadcast* (`glob l`, the corruption `fail id`): every instance applies the
     deterministic transformation `act l`, the untouched instance included (a Dirac step,
     `InstanceFamilyState.applyBroadcast`). The copies of a shared variable (the corrupted
     set) are thereby equal at every instance, which a step at one instance could not ensure.
  4. *idle*: on an unowned label that is not a broadcast, the family does not move.

  The broadcast disjunct applies `act` unconditionally: no instance transition justifies it.
  The actions of the development are total corruption functions, as D1 has it. The silent
  disjunct ranges over the rounds of the map: the untouched rounds are infinitely many, and the
  family would not be finitely branching if each of them could take a silent transition.

All three combinators preserve `System.IsLTS`, so an LTS instance family is
again an LTS and the `ForwardLTS` correspondence applies at family level.

Both weak transitions of a system are carried along `mapIdle` by any *section*
`g` of `φ` that respects the silent label. A section is what makes the
relabelling trivial on transitions: `φ (g x) = some x` turns every `x`-step into
a `g x`-step of the read-back system, with no condition on which labels occur
in the witness execution. The second hypothesis, `g x = τ ↔ x = τ`, is what
makes it trivial on traces: the relabelled execution hides exactly the
transitions the original hid, so its trace is the original trace relabelled by
`g` (`System.trace_mapLabels`, in `Framework/TraceDistributionSupport.lean`).
-/

namespace PLTS

variable {State σ Label : Type}

/-! ### Idle padding -/

/-- `sys` with idle self-loops on every label outside `busy`. -/
def System.withIdle (sys : System State Label) (busy : Label → Prop) :
    System State Label where
  init := sys.init
  step s l μ := sys.step s l μ ∨ (¬ busy l ∧ μ = PMF.pure s)

@[simp] theorem System.withIdle_init (sys : System State Label) (busy : Label → Prop) :
    (sys.withIdle busy).init = sys.init := rfl

/-- Idle padding preserves the LTS property. -/
theorem System.IsLTS.withIdle {sys : System State Label} (h : sys.IsLTS)
    (busy : Label → Prop) : (sys.withIdle busy).IsLTS := by
  rintro s l μ (hstep | ⟨-, rfl⟩)
  · exact h s l μ hstep
  · exact ⟨s, rfl⟩

/-! ### Pulling a system back along a partial label map -/

/-- Read a system over `L` as a system over `L'`: a label `l'` with
`φ l' = some l` delegates to the `l`-transitions, and a label outside the
image of `φ` leaves the system idle. -/
def System.mapIdle {S L L' : Type} (φ : L' → Option L) (sys : System S L) :
    System S L' where
  init := sys.init
  step s l' μ :=
    match φ l' with
    | some l => sys.step s l μ
    | none => μ = PMF.pure s

@[simp] theorem System.mapIdle_init {S L L' : Type} (φ : L' → Option L)
    (sys : System S L) : (sys.mapIdle φ).init = sys.init := rfl

theorem System.mapIdle_step {S L L' : Type} (φ : L' → Option L) (sys : System S L)
    (s : S) (l' : L') (μ : PMF S) :
    (sys.mapIdle φ).step s l' μ ↔
      (∃ l, φ l' = some l ∧ sys.step s l μ) ∨ (φ l' = none ∧ μ = PMF.pure s) := by
  change (match φ l' with
        | some l => sys.step s l μ
        | none => μ = PMF.pure s) ↔ _
  cases hφ : φ l' with
  | none => simp
  | some l => simp

/-- A delegated label has the transitions of the underlying system on the label it maps to. -/
theorem System.mapIdle_step_some {S L L' : Type} {φ : L' → Option L}
    {sys : System S L} {s : S} {l' : L'} {l : L} (hφ : φ l' = some l)
    (μ : PMF S) : (sys.mapIdle φ).step s l' μ ↔ sys.step s l μ := by
  rw [System.mapIdle_step]
  simp [hφ]

/-- Unmapped labels are idle self-loops. -/
theorem System.mapIdle_step_none {S L L' : Type} {φ : L' → Option L}
    {sys : System S L} {s : S} {l' : L'} (hφ : φ l' = none) (μ : PMF S) :
    (sys.mapIdle φ).step s l' μ ↔ μ = PMF.pure s := by
  rw [System.mapIdle_step]
  simp [hφ]

/-- **`mapIdle` preserves the LTS property**: a delegated label keeps the
underlying system's distribution, an idle one is a Dirac by construction. -/
theorem System.mapIdle_isLTS {S L L' : Type} (φ : L' → Option L)
    {sys : System S L} (h : sys.IsLTS) : (sys.mapIdle φ).IsLTS := by
  intro s l' μ hstep
  rw [System.mapIdle_step] at hstep
  rcases hstep with ⟨l, -, hs⟩ | ⟨-, rfl⟩
  · exact h s l μ hs
  · exact ⟨s, rfl⟩

/-! ### A weak run carried along a pullback with a section -/

section MapIdleWeak

variable {S L L' : Type} [Silent L] [Silent L'] {sys : System S L}
  {φ : L' → Option L} {s s' : S}

/-- **A silent weak run of `sys` is one of `sys.mapIdle φ`**: `q =ε=> q'` of `sys` is
`q =ε=> q'` of `sys.mapIdle φ`, the witness execution relabelled along a
section `g` of `φ`. -/
theorem System.weakLSilent_mapIdle (g : L → L') (hsec : ∀ x, φ (g x) = some x)
    (hgτ : ∀ x, g x = (Silent.τ : L') ↔ x = (Silent.τ : L))
    (h : sys.weakLSilent s s') : (sys.mapIdle φ).weakLSilent s s' := by
  obtain ⟨e, hterm, hpe, hinit, hend, htr⟩ := h
  refine ⟨e.mapLabels g, (AlterSeq.mapLabels_trans_terminates_iff g e).mpr hterm,
    is_partial_exec_mapLabels g
      (fun _ x _ hx => (System.mapIdle_step_some (hsec x) _).mpr hx) hpe,
    hinit, ?_, ?_⟩
  · rw [AlterSeq.endState_mapLabels g e hterm]; exact hend
  · rw [System.trace_mapLabels _ sys g hgτ, htr, Stream'.Seq.map_nil]

/-- **A labelled weak run of `sys` is one of `sys.mapIdle φ`**: `q =l=> q'` of `sys` is
`q =l'=> q'` of `sys.mapIdle φ` at any label `l'` the section `g` puts over
`l`. -/
theorem System.weakLStep_mapIdle (g : L → L') (hsec : ∀ x, φ (g x) = some x)
    (hgτ : ∀ x, g x = (Silent.τ : L') ↔ x = (Silent.τ : L))
    {l : L} {l' : L'} (hgl : g l = l') (h : sys.weakLStep s l s') :
    (sys.mapIdle φ).weakLStep s l' s' := by
  obtain ⟨e, hterm, hpe, hinit, hend, htr⟩ := h
  refine ⟨e.mapLabels g, (AlterSeq.mapLabels_trans_terminates_iff g e).mpr hterm,
    is_partial_exec_mapLabels g
      (fun _ x _ hx => (System.mapIdle_step_some (hsec x) _).mpr hx) hpe,
    hinit, ?_, ?_⟩
  · rw [AlterSeq.endState_mapLabels g e hterm]; exact hend
  · rw [System.trace_mapLabels _ sys g hgτ, htr, Stream'.Seq.map_cons,
      Stream'.Seq.map_nil, hgl]

end MapIdleWeak

/-! ### The state of a family of instances -/

/-- The state of a family of instances indexed by ℕ: the broadcasts applied so far, and the
instances the family has touched. A round not in the map is untouched and reads as the initial
instance under the recorded broadcasts. -/
structure InstanceFamilyState {σ L : Type} (initial : σ) (act : L → σ → σ) where
  /-- The broadcast labels applied, the latest first. -/
  broadcasts : List L
  /-- The instances the family has touched, by round. -/
  instanceMap : Finmap (fun _ : ℕ => σ)

namespace InstanceFamilyState

/-- The family state with no broadcast applied and no instance touched: every round reads
`initial`. -/
def initial {L : Type} {initial : σ} {act : L → σ → σ} : InstanceFamilyState initial act :=
  ⟨[], ∅⟩

variable {L : Type} {initial : σ} {act : L → σ → σ}

/-- The instance at every round not in the map: `initial` under the recorded broadcasts, the
oldest broadcast applied first. -/
def untouchedInstance (g : InstanceFamilyState initial act) : σ :=
  g.broadcasts.foldr act initial

/-- The instance at round `r`: its entry in the map, or the untouched instance. -/
@[coe] def instanceState (g : InstanceFamilyState initial act) : ℕ → σ :=
  fun r => (g.instanceMap.lookup r).getD g.untouchedInstance

instance : CoeFun (InstanceFamilyState initial act) (fun _ => ℕ → σ) := ⟨instanceState⟩

/-- The instance at round `r`, unfolded. -/
theorem apply_eq (g : InstanceFamilyState initial act) (r : ℕ) :
    g r = (g.instanceMap.lookup r).getD g.untouchedInstance := rfl

/-- A round of the map reads its entry. -/
theorem apply_of_lookup {g : InstanceFamilyState initial act} {r : ℕ} {x : σ}
    (h : g.instanceMap.lookup r = some x) : g r = x := by
  rw [apply_eq, h, Option.getD_some]

/-- A round not in the map reads the untouched instance. -/
theorem apply_of_notMem {g : InstanceFamilyState initial act} {r : ℕ}
    (h : r ∉ g.instanceMap.keys) : g r = g.untouchedInstance := by
  rw [Finmap.mem_keys, ← Finmap.lookup_eq_none] at h
  rw [apply_eq, h, Option.getD_none]

/-- A round of the map has the entry its accessor reads. -/
theorem lookup_of_mem {g : InstanceFamilyState initial act} {r : ℕ}
    (h : r ∈ g.instanceMap.keys) : g.instanceMap.lookup r = some (g r) := by
  rw [Finmap.mem_keys, Finmap.mem_iff] at h
  obtain ⟨x, hx⟩ := h
  rw [hx, apply_of_lookup hx]

/-- Two family states are equal when their broadcasts and their maps are. Equal accessors do not
give equal states: a map entry equal to the untouched instance reads as an absent entry does. -/
@[ext] theorem ext {g g' : InstanceFamilyState initial act}
    (hBroadcasts : g.broadcasts = g'.broadcasts) (hInstanceMap : g.instanceMap = g'.instanceMap) :
    g = g' := by
  cases g
  cases g'
  cases hBroadcasts
  cases hInstanceMap
  rfl

/-- Two family states with the same broadcasts and the same rounds in their maps are equal when
their accessors are. -/
theorem ext_of_keys {g g' : InstanceFamilyState initial act}
    (hBroadcasts : g.broadcasts = g'.broadcasts)
    (hKeys : g.instanceMap.keys = g'.instanceMap.keys) (hApply : ∀ r, g r = g' r) : g = g' := by
  refine ext hBroadcasts (Finmap.ext_lookup fun r => ?_)
  by_cases hr : r ∈ g.instanceMap.keys
  · rw [lookup_of_mem hr, lookup_of_mem (hKeys ▸ hr), hApply r]
  · have hr' : r ∉ g'.instanceMap.keys := hKeys ▸ hr
    rw [Finmap.mem_keys, ← Finmap.lookup_eq_none] at hr hr'
    rw [hr, hr']

/-! #### The initial state -/

@[simp] theorem initial_broadcasts :
    (InstanceFamilyState.initial : InstanceFamilyState initial act).broadcasts = [] := rfl

@[simp] theorem initial_instanceMap :
    (InstanceFamilyState.initial : InstanceFamilyState initial act).instanceMap = ∅ := rfl

@[simp] theorem initial_apply (r : ℕ) :
    (InstanceFamilyState.initial : InstanceFamilyState initial act) r = initial := rfl

@[simp] theorem keys_initial :
    (InstanceFamilyState.initial : InstanceFamilyState initial act).instanceMap.keys = ∅ := rfl

/-! #### Setting the instance at one round -/

/-- Insert `x` as the instance at round `r`. -/
def setInstanceState (g : InstanceFamilyState initial act) (r : ℕ) (x : σ) :
    InstanceFamilyState initial act :=
  { g with instanceMap := g.instanceMap.insert r x }

@[simp] theorem broadcasts_setInstanceState (g : InstanceFamilyState initial act) (r : ℕ)
    (x : σ) : (g.setInstanceState r x).broadcasts = g.broadcasts := rfl

@[simp] theorem untouchedInstance_setInstanceState (g : InstanceFamilyState initial act) (r : ℕ)
    (x : σ) : (g.setInstanceState r x).untouchedInstance = g.untouchedInstance := rfl

@[simp] theorem setInstanceState_apply_same (g : InstanceFamilyState initial act) (r : ℕ)
    (x : σ) : (g.setInstanceState r x) r = x :=
  apply_of_lookup (Finmap.lookup_insert _)

@[simp] theorem setInstanceState_apply_ne (g : InstanceFamilyState initial act) {r r' : ℕ}
    (x : σ) (h : r' ≠ r) : (g.setInstanceState r x) r' = g r' := by
  rw [apply_eq, apply_eq, untouchedInstance_setInstanceState]
  exact congrArg (·.getD g.untouchedInstance) (Finmap.lookup_insert_of_ne g.instanceMap h)

/-- The accessor of `g.setInstanceState r x` is the accessor of `g` updated at `r`. -/
theorem instanceState_setInstanceState (g : InstanceFamilyState initial act) (r : ℕ) (x : σ) :
    (g.setInstanceState r x).instanceState = Function.update g.instanceState r x := by
  funext r'
  by_cases h : r' = r
  · subst h
    rw [Function.update_self]
    exact setInstanceState_apply_same g r' x
  · rw [Function.update_of_ne h]
    exact setInstanceState_apply_ne g x h

theorem keys_setInstanceState (g : InstanceFamilyState initial act) (r : ℕ) (x : σ) :
    (g.setInstanceState r x).instanceMap.keys = insert r g.instanceMap.keys := by
  ext r'
  rw [Finset.mem_insert, Finmap.mem_keys, Finmap.mem_keys]
  exact Finmap.mem_insert

theorem mem_keys_setInstanceState_self (g : InstanceFamilyState initial act) (r : ℕ) (x : σ) :
    r ∈ (g.setInstanceState r x).instanceMap.keys := by
  rw [keys_setInstanceState]
  exact Finset.mem_insert_self r _

@[simp] theorem setInstanceState_setInstanceState (g : InstanceFamilyState initial act) (r : ℕ)
    (x y : σ) : (g.setInstanceState r x).setInstanceState r y = g.setInstanceState r y :=
  ext rfl (Finmap.insert_insert _)

/-- Setting a round of the map to the instance it reads leaves the state where it is. -/
theorem setInstanceState_apply_self {g : InstanceFamilyState initial act} {r : ℕ}
    (h : r ∈ g.instanceMap.keys) : g.setInstanceState r (g r) = g := by
  refine ext_of_keys rfl ?_ fun r' => ?_
  · rw [keys_setInstanceState, Finset.insert_eq_of_mem h]
  · by_cases hr : r' = r
    · subst hr
      exact setInstanceState_apply_same g r' _
    · exact setInstanceState_apply_ne g _ hr

/-! #### Applying a broadcast -/

/-- The entries of a map with `f` applied to every value have the keys of the map. -/
private theorem keys_map_values (s : Finmap (fun _ : ℕ => σ)) (f : σ → σ) :
    (s.entries.map (fun e : (Σ _ : ℕ, σ) => (⟨e.1, f e.2⟩ : Σ _ : ℕ, σ))).keys
      = s.entries.keys := by
  rw [Multiset.keys, Multiset.keys, Multiset.map_map]
  rfl

/-- Apply the broadcast `l`: record it, and apply `act l` to every instance of the map. The
untouched instance reads the recorded broadcasts, so `act l` applies to it as well
(`applyBroadcast_apply`). -/
def applyBroadcast (g : InstanceFamilyState initial act) (l : L) :
    InstanceFamilyState initial act where
  broadcasts := l :: g.broadcasts
  instanceMap :=
    { entries := g.instanceMap.entries.map
        (fun e : (Σ _ : ℕ, σ) => (⟨e.1, act l e.2⟩ : Σ _ : ℕ, σ))
      nodupKeys := Multiset.nodup_keys.mp
        ((keys_map_values g.instanceMap (act l)).symm ▸ g.instanceMap.nodupKeys.nodup_keys) }

@[simp] theorem broadcasts_applyBroadcast (g : InstanceFamilyState initial act) (l : L) :
    (g.applyBroadcast l).broadcasts = l :: g.broadcasts := rfl

@[simp] theorem untouchedInstance_applyBroadcast (g : InstanceFamilyState initial act) (l : L) :
    (g.applyBroadcast l).untouchedInstance = act l g.untouchedInstance := rfl

@[simp] theorem keys_applyBroadcast (g : InstanceFamilyState initial act) (l : L) :
    (g.applyBroadcast l).instanceMap.keys = g.instanceMap.keys :=
  Finset.val_injective (keys_map_values g.instanceMap (act l))

theorem lookup_applyBroadcast (g : InstanceFamilyState initial act) (l : L) (r : ℕ) :
    (g.applyBroadcast l).instanceMap.lookup r = (g.instanceMap.lookup r).map (act l) := by
  cases h : g.instanceMap.lookup r with
  | none =>
    rw [Option.map_none, Finmap.lookup_eq_none, ← Finmap.mem_keys, keys_applyBroadcast,
      Finmap.mem_keys, ← Finmap.lookup_eq_none]
    exact h
  | some x =>
    rw [Option.map_some, Finmap.lookup_eq_some_iff]
    exact Multiset.mem_map.mpr ⟨⟨r, x⟩, Finmap.lookup_eq_some_iff.mp h, rfl⟩

/-- A broadcast applies `act l` at every round, in the map or not. -/
@[simp] theorem applyBroadcast_apply (g : InstanceFamilyState initial act) (l : L) (r : ℕ) :
    (g.applyBroadcast l) r = act l (g r) := by
  rw [apply_eq, apply_eq, lookup_applyBroadcast, untouchedInstance_applyBroadcast,
    Option.getD_map]

end InstanceFamilyState

/-! ### ℕ-indexed instance families -/

variable [Silent Label]

/-- The ℕ-indexed family of the instances `inst r` over a shared alphabet, on the state
`InstanceFamilyState initial act`. `owns` assigns a label to the round of the instance it belongs
to, `glob` marks the broadcast labels (corruption), and `act l` is the deterministic transformation
the broadcast `l` applies to every instance. The family starts with no instance touched, so every
round reads `initial`; it equals `(inst r).init` at every round when `initial` is the instances'
common initial state (`System.family_init_apply`). -/
def System.family (inst : ℕ → System σ Label)
    (owns : Label → Option ℕ) (glob : Label → Prop) (act : Label → σ → σ) (initial : σ) :
    System (InstanceFamilyState initial act) Label where
  init := InstanceFamilyState.initial
  step g l μ :=
    (l = Silent.τ ∧ ∃ r ∈ g.instanceMap.keys, ∃ μr, (inst r).step (g r) l μr ∧
      μ = μr.map (g.setInstanceState r)) ∨
    ((∃ r, owns l = some r ∧ ∃ μr, (inst r).step (g r) l μr ∧
      μ = μr.map (g.setInstanceState r))) ∨
    (¬ l = Silent.τ ∧ owns l = none ∧ glob l ∧ μ = PMF.pure (g.applyBroadcast l)) ∨
    (¬ l = Silent.τ ∧ owns l = none ∧ ¬ glob l ∧ μ = PMF.pure g)

@[simp] theorem System.family_init (inst : ℕ → System σ Label)
    (owns : Label → Option ℕ) (glob : Label → Prop) (act : Label → σ → σ) (initial : σ) :
    (System.family inst owns glob act initial).init = InstanceFamilyState.initial := rfl

/-- When every instance starts from `initial`, the family starts from the instances' initial
states. -/
theorem System.family_init_apply {inst : ℕ → System σ Label}
    (owns : Label → Option ℕ) (glob : Label → Prop) (act : Label → σ → σ) {initial : σ}
    (hInitial : ∀ r, (inst r).init = initial) (r : ℕ) :
    (System.family inst owns glob act initial).init r = (inst r).init := by
  rw [hInitial r]
  rfl

/-- The step disjunction of `System.family`, by name. -/
theorem System.family_step_iff (inst : ℕ → System σ Label)
    (owns : Label → Option ℕ) (glob : Label → Prop) (act : Label → σ → σ) (initial : σ)
    {g : InstanceFamilyState initial act} {l : Label} {μ : PMF (InstanceFamilyState initial act)} :
    (System.family inst owns glob act initial).step g l μ ↔
      (l = Silent.τ ∧ ∃ r ∈ g.instanceMap.keys, ∃ μr, (inst r).step (g r) l μr ∧
        μ = μr.map (g.setInstanceState r)) ∨
      ((∃ r, owns l = some r ∧ ∃ μr, (inst r).step (g r) l μr ∧
        μ = μr.map (g.setInstanceState r))) ∨
      (¬ l = Silent.τ ∧ owns l = none ∧ glob l ∧ μ = PMF.pure (g.applyBroadcast l)) ∨
      (¬ l = Silent.τ ∧ owns l = none ∧ ¬ glob l ∧ μ = PMF.pure g) := Iff.rfl

/-- A family of LTS instances is an LTS: every disjunct's successor distribution is a Dirac,
the image of a Dirac under `setInstanceState` included. -/
theorem System.family_isLTS {inst : ℕ → System σ Label}
    (h : ∀ r, (inst r).IsLTS)
    (owns : Label → Option ℕ) (glob : Label → Prop) (act : Label → σ → σ) (initial : σ) :
    (System.family inst owns glob act initial).IsLTS := by
  rintro g l μ (⟨-, r, -, μr, hstep, rfl⟩ | ⟨r, -, μr, hstep, rfl⟩ |
    ⟨-, -, -, rfl⟩ | ⟨-, -, -, rfl⟩)
  · obtain ⟨x, rfl⟩ := h r _ _ _ hstep
    exact ⟨g.setInstanceState r x, by rw [PMF.pure_map]⟩
  · obtain ⟨x, rfl⟩ := h r _ _ _ hstep
    exact ⟨g.setInstanceState r x, by rw [PMF.pure_map]⟩
  · exact ⟨_, rfl⟩
  · exact ⟨g, rfl⟩

end PLTS
