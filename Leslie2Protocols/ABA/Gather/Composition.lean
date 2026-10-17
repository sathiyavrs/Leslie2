/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sathiya / Claude
-/

import Leslie2Protocols.ABA.ReliableBroadcast.Bracha.Composition
import Leslie2Protocols.ABA.Gather.Components
import Leslie2Protocols.Framework.Relabel
import Leslie2Protocols.Framework.SynchronisedProduct
import Leslie2Protocols.Framework.LoopsAndInstanceFamilies

/-!
# The gather instance, composed

`Gather.instanceOverBroadcasts`: one gather instance over an arbitrary payload type `X`, assembled
from the `n` gather programs beside the gather network (`ABA/Gather/Components.lean`) and the `n`
reliable-broadcast instances carrying the inputs, one per process, each read along the pullback
that names it.
`instanceOverBroadcastsExtended` puts the two in parallel over the instance-internal
alphabet; `instanceOverBroadcasts` hides the instance's four events there and reads the result back
over the gather specification's alphabet `Label n X`.

The composition is generic in the broadcast instances, each over the BRB specification's alphabet
`BRB.Label n X`: `instanceOverBroadcasts` takes the `n` instances as arguments,
`instanceOverBracha` supplies Bracha instances (`BRB.brachaInstance`) and
`instanceOverBroadcastSpecification` supplies broadcast specifications (`BRB.specInst`). Both run
on `StateOverBroadcasts n X B`, and the three `init` lemmas are the states they start from.

## Projections of the composed state

`gatherProgramsAndNetwork`, `inputBroadcasts` and `core` read the three components of that
state, and `setGatherProgramsAndNetwork`, `setInputBroadcasts` and `setCore` are the three
writes that reach one of them. `corruptAll` corrupts the gather network state and every broadcast
coordinate at once, the programs untouched (D1). A transition of the gather or of a broadcast
instance is stated through these, so that a guard reads `gatherProgramsAndNetwork s` where the
implementation reads the gather instance state. `approved` is the payload sets whose every pair is a
committed entry of the input instance that carries it, read at the composition over the broadcast
specification.

## Determinacy

The gather program's and the gather network's transitions are Dirac
(`ABA/Gather/Components.lean`), so the composition is an LTS whenever the broadcast instances are:
`instanceOverBracha_isLTS` and `instanceOverBroadcastSpecification_isLTS` are the two instances of
that.
-/

namespace PLTS
namespace ABA
namespace Gather

variable {X : Type}

section Transitions

variable [DecidableEq X]

/-! ### The gather instance over the broadcast instances -/

/-- The state of the composition whose input instances have state `B`. -/
abbrev StateOverBroadcasts (n : ℕ) (X B : Type) : Type :=
  ((∀ _ : Fin n, LocalState n (ProcessVariables n X) (Message n X)) × NetworkState n X) ×
    (∀ _ : Fin n, B)

/-- The gather programs and network beside the input instances, over the
instance-internal alphabet. -/
noncomputable def instanceOverBroadcastsExtended (P : Parameters) (X : Type) [DecidableEq X]
    {B : Type} (BIn : ∀ _ : Fin P.n, System B (BRB.Label P.n X)) :
    System (StateOverBroadcasts P.n X B) (GatherLabel P.n X) :=
  (gatherPrograms P X).parallel
    (System.synchronisedProduct (fun k => (BIn k).mapIdle (inputBroadcastLabelMap P.n X k)))

/-- **The gather instance** over the input instances `BIn`: the two in
parallel, the instance's events hidden, the result read back over the gather
specification's alphabet. -/
noncomputable def instanceOverBroadcasts (P : Parameters) (X : Type) [DecidableEq X] {B : Type}
    (BIn : ∀ _ : Fin P.n, System B (BRB.Label P.n X)) :
    System (StateOverBroadcasts P.n X B) (Label P.n X) :=
  ((instanceOverBroadcastsExtended P X BIn).abstract (gatherEvents P.n X)).relabel

/-- The state of the gather instance over Bracha's broadcast. -/
abbrev StateOverBracha (n : ℕ) (X : Type) : Type :=
  StateOverBroadcasts n X (BRB.BrachaState n X)

/-- The state of the gather instance over the broadcast specification. -/
abbrev StateOverBroadcastSpecification (n : ℕ) (X : Type) : Type :=
  StateOverBroadcasts n X (BRB.SpecState n X)

/-- **The gather instance over Bracha's broadcast.** -/
noncomputable def instanceOverBracha (P : Parameters) (X : Type) [DecidableEq X] :
    System (StateOverBracha P.n X) (Label P.n X) :=
  instanceOverBroadcasts P X (fun k => BRB.brachaInstance P k X)

/-- **The gather instance over the broadcast specification.** -/
noncomputable def instanceOverBroadcastSpecification (P : Parameters) (X : Type) [DecidableEq X] :
    System (StateOverBroadcastSpecification P.n X) (Label P.n X) :=
  instanceOverBroadcasts P X (fun k => BRB.specInst P k X)

@[simp] theorem instanceOverBroadcasts_init (P : Parameters) {B : Type}
    (BIn : ∀ _ : Fin P.n, System B (BRB.Label P.n X)) :
    (instanceOverBroadcasts P X BIn).init =
      (((fun _ => LocalState.initial P.n (Message P.n X) (ProcessVariables.initial P.n X)),
        NetworkState.initial P.n X), (fun k => (BIn k).init)) := rfl

@[simp] theorem instanceOverBracha_init (P : Parameters) :
    (instanceOverBracha P X).init =
      (((fun _ => LocalState.initial P.n (Message P.n X) (ProcessVariables.initial P.n X)),
        NetworkState.initial P.n X), (fun _ => BRB.BrachaState.initial P.n X)) := rfl

@[simp] theorem instanceOverBroadcastSpecification_init (P : Parameters) :
    (instanceOverBroadcastSpecification P X).init =
      (((fun _ => LocalState.initial P.n (Message P.n X) (ProcessVariables.initial P.n X)),
        NetworkState.initial P.n X), (fun _ => BRB.SpecState.initial P.n X)) := rfl

end Transitions

/-! ### Projections of the instance state

The three components of the instance state, and the three writes that reach one
of them. A transition of the gather or of a broadcast instance is stated through these, so that a
guard reads `gatherProgramsAndNetwork s` where the implementation reads the gather instance
state. -/

section Projections

variable {n : ℕ} {B : Type}

/-- The gather's instance state: the programs beside the gather network
state. -/
def gatherProgramsAndNetwork (s : StateOverBroadcasts n X B) :
    InstanceState n (ProcessVariables n X) (Message n X) := (s.1.1, s.1.2.network)

/-- The input instances. One per process, carrying that process's input; these are the `n`
reliable-broadcast instances of a gather instance. -/
def inputBroadcasts (s : StateOverBroadcasts n X B) : ∀ _ : Fin n, B := s.2

/-- The instance's core. -/
def core (s : StateOverBroadcasts n X B) : Option (AcceptedPairs n X) := s.1.2.core

/-- Overwrite the gather's instance state. -/
def setGatherProgramsAndNetwork (s : StateOverBroadcasts n X B)
    (t : InstanceState n (ProcessVariables n X) (Message n X)) :
    StateOverBroadcasts n X B := ((t.1, { s.1.2 with network := t.2 }), s.2)

/-- Overwrite the input instances. -/
def setInputBroadcasts (s : StateOverBroadcasts n X B) (b : ∀ _ : Fin n, B) :
    StateOverBroadcasts n X B := (s.1, b)

/-- Overwrite the core. -/
def setCore (s : StateOverBroadcasts n X B) (c : Option (AcceptedPairs n X)) :
    StateOverBroadcasts n X B :=
  ((s.1.1, { s.1.2 with core := c }), s.2)

@[simp] theorem gatherProgramsAndNetwork_setGatherProgramsAndNetwork (s : StateOverBroadcasts n X B)
    (t : InstanceState n (ProcessVariables n X) (Message n X)) :
    gatherProgramsAndNetwork (setGatherProgramsAndNetwork s t) = t := rfl
@[simp] theorem inputBroadcasts_setGatherProgramsAndNetwork (s : StateOverBroadcasts n X B)
    (t : InstanceState n (ProcessVariables n X) (Message n X)) :
    inputBroadcasts (setGatherProgramsAndNetwork s t) = inputBroadcasts s := rfl
@[simp] theorem core_setGatherProgramsAndNetwork (s : StateOverBroadcasts n X B)
    (t : InstanceState n (ProcessVariables n X) (Message n X)) :
    core (setGatherProgramsAndNetwork s t) = core s := rfl

@[simp] theorem gatherProgramsAndNetwork_setInputBroadcasts (s : StateOverBroadcasts n X B)
    (b : ∀ _ : Fin n, B) :
    gatherProgramsAndNetwork (setInputBroadcasts s b) = gatherProgramsAndNetwork s := rfl
@[simp] theorem inputBroadcasts_setInputBroadcasts (s : StateOverBroadcasts n X B)
    (b : ∀ _ : Fin n, B) :
    inputBroadcasts (setInputBroadcasts s b) = b := rfl
@[simp] theorem core_setInputBroadcasts (s : StateOverBroadcasts n X B) (b : ∀ _ : Fin n, B) :
    core (setInputBroadcasts s b) = core s := rfl

@[simp] theorem gatherProgramsAndNetwork_setCore (s : StateOverBroadcasts n X B)
    (c : Option (AcceptedPairs n X)) :
    gatherProgramsAndNetwork (setCore s c) = gatherProgramsAndNetwork s := rfl
@[simp] theorem inputBroadcasts_setCore (s : StateOverBroadcasts n X B)
    (c : Option (AcceptedPairs n X)) :
    inputBroadcasts (setCore s c) = inputBroadcasts s := rfl
@[simp] theorem core_setCore (s : StateOverBroadcasts n X B) (c : Option (AcceptedPairs n X)) :
    core (setCore s c) = c := rfl

/-- Corruption (deviation D1): the gather network state and every input instance corrupted
together, the programs untouched. The transform `cIn` is the corruption of an input instance. -/
def corruptAll (P : Parameters) (id : Fin P.n) (cIn : B → B)
    (s : StateOverBroadcasts P.n X B) : StateOverBroadcasts P.n X B :=
  ((s.1.1, { s.1.2 with network := s.1.2.network.corrupt P id }), fun k => cIn (s.2 k))

@[simp] theorem gatherProgramsAndNetwork_corruptAll (P : Parameters) (id : Fin P.n) (cIn : B → B)
    (s : StateOverBroadcasts P.n X B) :
    gatherProgramsAndNetwork (corruptAll P id cIn s) = InstanceState.corrupt P id
      (gatherProgramsAndNetwork s) := rfl
@[simp] theorem inputBroadcasts_corruptAll (P : Parameters) (id : Fin P.n) (cIn : B → B)
    (s : StateOverBroadcasts P.n X B) (k : Fin P.n) :
    inputBroadcasts (corruptAll P id cIn s) k = cIn (inputBroadcasts s k) := rfl
@[simp] theorem core_corruptAll (P : Parameters) (id : Fin P.n) (cIn : B → B)
    (s : StateOverBroadcasts P.n X B) : core (corruptAll P id cIn s) = core s := rfl

end Projections

/-- A payload set is approved at the composition over the broadcast specification when every pair
is a
committed entry of the input instance that carries it. -/
def approved {n : ℕ} (s : StateOverBroadcastSpecification n X) (A : AcceptedPairs n X) : Prop :=
  A.subMap (fun k => (inputBroadcasts s k).val)

section Determinacy

variable [DecidableEq X]

/-! ### Determinacy

The gather program's and the gather network's transitions are Dirac
(`ABA/Gather/Components.lean`), so the composition is an LTS whenever the broadcast instances
are. -/

/-- Every gather program transition is Dirac. -/
theorem programStep_dirac {P : Parameters} {j : Fin P.n}
    {p : LocalState P.n (ProcessVariables P.n X) (Message P.n X)} {l : GatherLabel P.n X}
    {ν : PMF (LocalState P.n (ProcessVariables P.n X) (Message P.n X))} (h : ProgramStep P j p l ν)
      :
    ∃ p', ν = PMF.pure p' := by
  cases h <;> exact ⟨_, rfl⟩

/-- Every gather network transition is Dirac. -/
theorem networkStep_dirac {P : Parameters} {w : NetworkState P.n X} {l : GatherLabel P.n X}
    {μ : PMF (NetworkState P.n X)} (h : NetworkStep P w l μ) : ∃ w', μ = PMF.pure w' := by
  cases h <;> exact ⟨_, rfl⟩

/-- A gather program is an LTS. -/
theorem gatherProgram_isLTS (P : Parameters) (j : Fin P.n) : (gatherProgram P j (X := X)).IsLTS :=
  fun _ _ _ h => programStep_dirac h

/-- The gather network is an LTS. -/
theorem gatherNetwork_isLTS (P : Parameters) : (gatherNetwork P X).IsLTS := fun _ _ _ h =>
  networkStep_dirac
  h

/-- The synchronised group of gather programs is an LTS. -/
theorem gatherProgramProduct_isLTS (P : Parameters) :
    (System.synchronisedProduct (gatherProgram P (X := X))).IsLTS :=
  System.synchronisedProduct_isLTS (gatherProgram_isLTS P)

/-- The gather programs beside the gather network form an LTS. -/
theorem gatherPrograms_isLTS (P : Parameters) : (gatherPrograms P X).IsLTS :=
  System.parallel_isLTS (gatherProgramProduct_isLTS P) (gatherNetwork_isLTS P)

/-- The gather programs and network beside the input instances form an LTS. -/
theorem instanceOverBroadcastsExtended_isLTS (P : Parameters) {B : Type}
    {BIn : ∀ _ : Fin P.n, System B (BRB.Label P.n X)}
    (hIn : ∀ k, (BIn k).IsLTS) :
    (instanceOverBroadcastsExtended P X BIn).IsLTS :=
  System.parallel_isLTS (gatherPrograms_isLTS P)
    (System.synchronisedProduct_isLTS (fun k => System.mapIdle_isLTS _ (hIn k)))

/-- The gather instance is an LTS. -/
theorem instanceOverBroadcasts_isLTS (P : Parameters) {B : Type}
    {BIn : ∀ _ : Fin P.n, System B (BRB.Label P.n X)}
    (hIn : ∀ k, (BIn k).IsLTS) :
    (instanceOverBroadcasts P X BIn).IsLTS :=
  System.relabel_isLTS (System.abstract_isLTS (instanceOverBroadcastsExtended_isLTS P hIn) _)

/-- The gather instance over Bracha's broadcast is an LTS. -/
theorem instanceOverBracha_isLTS (P : Parameters) : (instanceOverBracha P X).IsLTS :=
  instanceOverBroadcasts_isLTS P (fun k => BRB.brachaInstance_isLTS P k)

/-- The gather instance over the broadcast specification is an LTS. -/
theorem instanceOverBroadcastSpecification_isLTS (P : Parameters) :
    (instanceOverBroadcastSpecification P X).IsLTS :=
  instanceOverBroadcasts_isLTS P (fun k => BRB.specInst_isLTS P k)

/-- No gather program transition fires on `τ`: a program only ever moves in an event
or on one of the interface labels. The composition's silent transitions are
therefore the gather network's injections, the hidden events and the broadcast
instances' own silent steps. -/
theorem programStep_no_tau {P : Parameters} {j : Fin P.n}
    {p : LocalState P.n (ProcessVariables P.n X) (Message P.n X)}
    {ν : PMF (LocalState P.n (ProcessVariables P.n X) (Message P.n X))}
    (h : ProgramStep P j p (Silent.τ : GatherLabel P.n X) ν) : False := by
  rw [gatherLabel_tau] at h; cases h

end Determinacy

end Gather
end ABA
end PLTS
