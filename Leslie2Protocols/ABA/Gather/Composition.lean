/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sathiya / Claude
-/

import Leslie2Protocols.ABA.ReliableBroadcast.Bracha.SpecificationOverInstanceAlphabet
import Leslie2Protocols.ABA.Gather.Components
import Leslie2Protocols.Framework.Relabel
import Leslie2Protocols.Framework.SynchronisedProduct
import Leslie2Protocols.Framework.LoopsAndInstanceFamilies

/-!
# The gather instance, composed

`Gather.instanceOverBroadcasts`: one gather instance over an arbitrary payload type `X`, assembled
from the gather tier of `ABA/Gather/Components.lean` -- the `n` gather programs beside the gather
network -- and a broadcast tier of `2n` reliable-broadcast instances, one per process for the
inputs and one per process for the `BIND` payloads (D32), each lifted along the pullback that names
it. `instanceOverBroadcastsExtended` is the two tiers in parallel over the instance-internal
alphabet; `instanceOverBroadcasts` hides the instance's six events there and reads the result back
over the interface alphabet `InstanceLabel n X`, the gather alphabet extended by the call loop.

The composition is generic in the broadcast tier: `instanceOverBroadcasts` takes the `2n` instances
as arguments, `instanceOverBracha` supplies Bracha instances (`BRB.brachaInstance`) and
`instanceOverBroadcastSpecification` supplies lifted broadcast specifications
(`BRB.specificationOverInstanceAlphabet`). Both run on `StateOverBroadcasts n X B B'`, and the three
`init` lemmas are the states they start from.

## Projections of the composed state

`gatherProgramsAndNetwork`, `inputBroadcasts`, `bindBroadcasts` and `core` read the four components
of that
state, and `setGatherProgramsAndNetwork`, `setInputBroadcasts`, `setBindBroadcasts` and `setCore`
are the four
writes that reach one of them. `corruptAll` corrupts the gather network state and every broadcast
coordinate at once, the programs untouched (D1). A transition of either tier is stated through
these, so that a guard reads `gatherProgramsAndNetwork s` where the implementation reads the gather
instance
state. `approved` is the payload sets whose every pair is a committed entry of the input instance
that carries it, read at the tier over the broadcast specification.

## Determinacy

The gather program's and the gather network's transitions are Dirac
(`ABA/Gather/Components.lean`), so the composition is an LTS whenever the broadcast tier is:
`instanceOverBracha_isLTS` and `instanceOverBroadcastSpecification_isLTS` are the two instances of
that.
-/

namespace PLTS
namespace ABA
namespace Gather

variable {X : Type}

section Transitions

variable [DecidableEq X]

/-! ### The gather instance over a broadcast tier -/

/-- The state of the composition whose broadcast instances have state `B` for
the inputs and `B'` for the `BIND` payloads. -/
abbrev StateOverBroadcasts (n : ℕ) (X B B' : Type) : Type :=
  ((∀ _ : Fin n, LocalState n (ProcessVariables n X) (Message n X)) × NetworkState n X) ×
    ((∀ _ : Fin n, B) × (∀ _ : Fin n, B'))

/-- The gather tier beside the broadcast tier, over the instance-internal
alphabet. -/
noncomputable def instanceOverBroadcastsExtended (P : Parameters) (X : Type) [DecidableEq X]
    {B B' : Type} (BIn : ∀ _ : Fin P.n, System B (BRB.InstanceLabel P.n X))
    (BBind : ∀ _ : Fin P.n, System B' (BRB.InstanceLabel P.n (AcceptedPairs P.n X))) :
    System (StateOverBroadcasts P.n X B B') (GatherLabel P.n X) :=
  (gatherPrograms P X).parallel
    ((System.synchronisedProduct (fun k => (BIn k).mapIdle (inputBroadcastLabelMap P.n X
      k))).parallel
      (System.synchronisedProduct (fun q => (BBind q).mapIdle (bindBroadcastLabelMap P.n X q))))

/-- **The gather instance** over the broadcast tier `BIn`, `BBind`: the two
tiers in parallel, the instance's events hidden, the result read back over the
interface alphabet. -/
noncomputable def instanceOverBroadcasts (P : Parameters) (X : Type) [DecidableEq X] {B B' : Type}
    (BIn : ∀ _ : Fin P.n, System B (BRB.InstanceLabel P.n X))
    (BBind : ∀ _ : Fin P.n, System B' (BRB.InstanceLabel P.n (AcceptedPairs P.n X))) :
    System (StateOverBroadcasts P.n X B B') (InstanceLabel P.n X) :=
  ((instanceOverBroadcastsExtended P X BIn BBind).abstract (gatherEvents P.n X)).relabel

/-- The state of the gather instance over Bracha's broadcast. -/
abbrev StateOverBracha (n : ℕ) (X : Type) : Type :=
  StateOverBroadcasts n X (BRB.BrachaState n X) (BRB.BrachaState n (AcceptedPairs n X))

/-- The state of the gather instance over the broadcast specification. -/
abbrev StateOverBroadcastSpecification (n : ℕ) (X : Type) : Type :=
  StateOverBroadcasts n X (BRB.SpecState n X) (BRB.SpecState n (AcceptedPairs n X))

/-- **The gather instance over Bracha's broadcast.** -/
noncomputable def instanceOverBracha (P : Parameters) (X : Type) [DecidableEq X] :
    System (StateOverBracha P.n X) (InstanceLabel P.n X) :=
  instanceOverBroadcasts P X (fun k => BRB.brachaInstance P k X) (fun q => BRB.brachaInstance P q
    (AcceptedPairs P.n X))

/-- **The gather instance over the broadcast specification.** -/
noncomputable def instanceOverBroadcastSpecification (P : Parameters) (X : Type) [DecidableEq X] :
    System (StateOverBroadcastSpecification P.n X) (InstanceLabel P.n X) :=
  instanceOverBroadcasts P X (fun k => BRB.specificationOverInstanceAlphabet P k X) (fun q =>
    BRB.specificationOverInstanceAlphabet P q (AcceptedPairs P.n X))

@[simp] theorem instanceOverBroadcasts_init (P : Parameters) {B B' : Type}
    (BIn : ∀ _ : Fin P.n, System B (BRB.InstanceLabel P.n X))
    (BBind : ∀ _ : Fin P.n, System B' (BRB.InstanceLabel P.n (AcceptedPairs P.n X))) :
    (instanceOverBroadcasts P X BIn BBind).init =
      (((fun _ => LocalState.initial P.n (Message P.n X) (ProcessVariables.initial P.n X)),
        NetworkState.initial P.n X),
        ((fun k => (BIn k).init), (fun q => (BBind q).init))) := rfl

@[simp] theorem instanceOverBracha_init (P : Parameters) :
    (instanceOverBracha P X).init =
      (((fun _ => LocalState.initial P.n (Message P.n X) (ProcessVariables.initial P.n X)),
        NetworkState.initial P.n X),
        ((fun _ => BRB.BrachaState.initial P.n X),
          (fun _ => BRB.BrachaState.initial P.n (AcceptedPairs P.n X)))) := rfl

@[simp] theorem instanceOverBroadcastSpecification_init (P : Parameters) :
    (instanceOverBroadcastSpecification P X).init =
      (((fun _ => LocalState.initial P.n (Message P.n X) (ProcessVariables.initial P.n X)),
        NetworkState.initial P.n X),
        ((fun _ => BRB.SpecState.initial P.n X),
          (fun _ => BRB.SpecState.initial P.n (AcceptedPairs P.n X)))) := rfl

end Transitions

/-! ### Projections of the instance state

The four components of the instance state, and the four writes that reach one
of them. A transition of either tier is stated through these, so that a guard reads
`gatherProgramsAndNetwork s` where the implementation reads the gather instance state. -/

section Projections

variable {n : ℕ} {B B' : Type}

/-- The gather tier's instance state: the programs beside the gather network
state. -/
def gatherProgramsAndNetwork (s : StateOverBroadcasts n X B B') : InstanceState n (ProcessVariables
  n X) (Message
  n
  X) := (s.1.1, s.1.2.network)

/-- The input instances. One per process, carrying that process's input; these and the `n` bind
instances are the `2n` reliable-broadcast instances of a gather instance. -/
def inputBroadcasts (s : StateOverBroadcasts n X B B') : ∀ _ : Fin n, B := s.2.1

/-- The bind instances. -/
def bindBroadcasts (s : StateOverBroadcasts n X B B') : ∀ _ : Fin n, B' := s.2.2

/-- The instance's core. -/
def core (s : StateOverBroadcasts n X B B') : Option (AcceptedPairs n X) := s.1.2.core

/-- Overwrite the gather tier's instance state. -/
def setGatherProgramsAndNetwork (s : StateOverBroadcasts n X B B') (t : InstanceState n
  (ProcessVariables n X)
  (Message n X)) :
    StateOverBroadcasts n X B B' := ((t.1, { s.1.2 with network := t.2 }), s.2)

/-- Overwrite the input instances. -/
def setInputBroadcasts (s : StateOverBroadcasts n X B B') (b : ∀ _ : Fin n,
  B) : StateOverBroadcasts n X B B' := (s.1, (b, s.2.2))

/-- Overwrite the bind instances. -/
def setBindBroadcasts (s : StateOverBroadcasts n X B B') (b : ∀ _ : Fin n,
  B') : StateOverBroadcasts n X B B' := (s.1, (s.2.1, b))

/-- Overwrite the core. -/
def setCore (s : StateOverBroadcasts n X B B') (c : Option (AcceptedPairs n X)) :
  StateOverBroadcasts n X B B' :=
  ((s.1.1, { s.1.2 with core := c }), s.2)

@[simp] theorem gatherProgramsAndNetwork_setGatherProgramsAndNetwork (s : StateOverBroadcasts n X B
  B') (t : InstanceState n
  (ProcessVariables n X) (Message n X)) :
    gatherProgramsAndNetwork (setGatherProgramsAndNetwork s t) = t := rfl
@[simp] theorem inputBroadcasts_setGatherProgramsAndNetwork (s : StateOverBroadcasts n X B B') (t :
  InstanceState
  n (ProcessVariables n X) (Message n X)) :
    inputBroadcasts (setGatherProgramsAndNetwork s t) = inputBroadcasts s := rfl
@[simp] theorem bindBroadcasts_setGatherProgramsAndNetwork (s : StateOverBroadcasts n X B B')
    (t : InstanceState n (ProcessVariables n X) (Message n X)) : bindBroadcasts
      (setGatherProgramsAndNetwork s t)
      =
      bindBroadcasts s := rfl
@[simp] theorem core_setGatherProgramsAndNetwork (s : StateOverBroadcasts n X B B') (t :
  InstanceState n
  (ProcessVariables n X) (Message n X)) :
    core (setGatherProgramsAndNetwork s t) = core s := rfl

@[simp] theorem gatherProgramsAndNetwork_setInputBroadcasts (s : StateOverBroadcasts n X B B') (b :
  ∀ _ : Fin n,
    B) : gatherProgramsAndNetwork (setInputBroadcasts s b) = gatherProgramsAndNetwork s := rfl
@[simp] theorem inputBroadcasts_setInputBroadcasts (s : StateOverBroadcasts n X B B') (b : ∀ _ : Fin
  n, B) :
    inputBroadcasts (setInputBroadcasts s b) = b := rfl
@[simp] theorem bindBroadcasts_setInputBroadcasts (s : StateOverBroadcasts n X B B') (b : ∀ _ : Fin
  n, B) :
    bindBroadcasts (setInputBroadcasts s b) = bindBroadcasts s := rfl
@[simp] theorem core_setInputBroadcasts (s : StateOverBroadcasts n X B B') (b : ∀ _ : Fin n, B) :
    core (setInputBroadcasts s b) = core s := rfl

@[simp] theorem gatherProgramsAndNetwork_setBindBroadcasts (s : StateOverBroadcasts n X B B') (b : ∀
  _ : Fin n,
    B') : gatherProgramsAndNetwork (setBindBroadcasts s b) = gatherProgramsAndNetwork s := rfl
@[simp] theorem inputBroadcasts_setBindBroadcasts (s : StateOverBroadcasts n X B B') (b : ∀ _ : Fin
  n, B') :
    inputBroadcasts (setBindBroadcasts s b) = inputBroadcasts s := rfl
@[simp] theorem bindBroadcasts_setBindBroadcasts (s : StateOverBroadcasts n X B B') (b : ∀ _ : Fin
  n, B') :
    bindBroadcasts (setBindBroadcasts s b) = b := rfl
@[simp] theorem core_setBindBroadcasts (s : StateOverBroadcasts n X B B') (b : ∀ _ : Fin n, B') :
    core (setBindBroadcasts s b) = core s := rfl

@[simp] theorem gatherProgramsAndNetwork_setCore (s : StateOverBroadcasts n X B B') (c : Option
  (AcceptedPairs n
  X)) :
    gatherProgramsAndNetwork (setCore s c) = gatherProgramsAndNetwork s := rfl
@[simp] theorem inputBroadcasts_setCore (s : StateOverBroadcasts n X B B') (c : Option
  (AcceptedPairs n X)) :
    inputBroadcasts (setCore s c) = inputBroadcasts s := rfl
@[simp] theorem bindBroadcasts_setCore (s : StateOverBroadcasts n X B B') (c : Option (AcceptedPairs
  n X)) :
    bindBroadcasts (setCore s c) = bindBroadcasts s := rfl
@[simp] theorem core_setCore (s : StateOverBroadcasts n X B B') (c : Option (AcceptedPairs n X)) :
    core (setCore s c) = c := rfl

/-- Corruption (deviation D1): the gather network state and every broadcast coordinate corrupted
together, the programs untouched. The two transforms are the corruption of the tier's broadcast
instances. -/
def corruptAll (P : Parameters) (id : Fin P.n) (cIn : B → B) (cBind : B' → B')
    (s : StateOverBroadcasts P.n X B B') : StateOverBroadcasts P.n X B B' :=
  ((s.1.1, { s.1.2 with network := s.1.2.network.corrupt P id }),
    (fun k => cIn (s.2.1 k), fun q => cBind (s.2.2 q)))

@[simp] theorem gatherProgramsAndNetwork_corruptAll (P : Parameters) (id : Fin P.n) (cIn : B → B)
  (cBind : B' →
  B')
    (s : StateOverBroadcasts P.n X B B') :
    gatherProgramsAndNetwork (corruptAll P id cIn cBind s) = InstanceState.corrupt P id
      (gatherProgramsAndNetwork s) := rfl
@[simp] theorem inputBroadcasts_corruptAll (P : Parameters) (id : Fin P.n) (cIn : B → B) (cBind : B'
  → B')
    (s : StateOverBroadcasts P.n X B B') (k : Fin P.n) :
    inputBroadcasts (corruptAll P id cIn cBind s) k = cIn (inputBroadcasts s k) := rfl
@[simp] theorem bindBroadcasts_corruptAll (P : Parameters) (id : Fin P.n) (cIn : B → B) (cBind : B'
  → B')
    (s : StateOverBroadcasts P.n X B B') (q : Fin P.n) :
    bindBroadcasts (corruptAll P id cIn cBind s) q = cBind (bindBroadcasts s q) := rfl
@[simp] theorem core_corruptAll (P : Parameters) (id : Fin P.n) (cIn : B → B) (cBind : B' → B')
    (s : StateOverBroadcasts P.n X B B') : core (corruptAll P id cIn cBind s) = core s := rfl

end Projections

/-- A payload set is approved at the tier over the broadcast specification when every pair is a
committed entry of the input instance that carries it. -/
def approved {n : ℕ} (s : StateOverBroadcastSpecification n X) (A : AcceptedPairs n X) : Prop :=
  A.subMap (fun k => (inputBroadcasts s k).val)

section Determinacy

variable [DecidableEq X]

/-! ### Determinacy

The gather program's and the gather network's transitions are Dirac
(`ABA/Gather/Components.lean`), so the composition is an LTS whenever the broadcast tier is. -/

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

/-- The gather tier is an LTS. -/
theorem gatherPrograms_isLTS (P : Parameters) : (gatherPrograms P X).IsLTS :=
  System.parallel_isLTS (gatherProgramProduct_isLTS P) (gatherNetwork_isLTS P)

/-- The two tiers in parallel form an LTS. -/
theorem instanceOverBroadcastsExtended_isLTS (P : Parameters) {B B' : Type}
    {BIn : ∀ _ : Fin P.n, System B (BRB.InstanceLabel P.n X)}
    {BBind : ∀ _ : Fin P.n, System B' (BRB.InstanceLabel P.n (AcceptedPairs P.n X))}
    (hIn : ∀ k, (BIn k).IsLTS) (hBind : ∀ q, (BBind q).IsLTS) :
    (instanceOverBroadcastsExtended P X BIn BBind).IsLTS :=
  System.parallel_isLTS (gatherPrograms_isLTS P)
    (System.parallel_isLTS
      (System.synchronisedProduct_isLTS (fun k => System.mapIdle_isLTS _ (hIn k)))
      (System.synchronisedProduct_isLTS (fun q => System.mapIdle_isLTS _ (hBind q))))

/-- The gather instance is an LTS. -/
theorem instanceOverBroadcasts_isLTS (P : Parameters) {B B' : Type}
    {BIn : ∀ _ : Fin P.n, System B (BRB.InstanceLabel P.n X)}
    {BBind : ∀ _ : Fin P.n, System B' (BRB.InstanceLabel P.n (AcceptedPairs P.n X))}
    (hIn : ∀ k, (BIn k).IsLTS) (hBind : ∀ q, (BBind q).IsLTS) :
    (instanceOverBroadcasts P X BIn BBind).IsLTS :=
  System.relabel_isLTS (System.abstract_isLTS (instanceOverBroadcastsExtended_isLTS P hIn hBind) _)

/-- The gather instance over Bracha's broadcast is an LTS. -/
theorem instanceOverBracha_isLTS (P : Parameters) : (instanceOverBracha P X).IsLTS :=
  instanceOverBroadcasts_isLTS P (fun k => BRB.brachaInstance_isLTS P k) (fun q =>
    BRB.brachaInstance_isLTS P q)

/-- The gather instance over the broadcast specification is an LTS. -/
theorem instanceOverBroadcastSpecification_isLTS (P : Parameters) :
    (instanceOverBroadcastSpecification P X).IsLTS :=
  instanceOverBroadcasts_isLTS P (fun k => BRB.specificationOverInstanceAlphabet_isLTS P k) (fun q
    =>
    BRB.specificationOverInstanceAlphabet_isLTS P q)

/-- No gather program transition fires on `τ`: a program only ever moves in an event
or on one of the interface labels. The composition's silent transitions are
therefore the gather network's injections, the hidden events and the broadcast
tier's own silent steps. -/
theorem programStep_no_tau {P : Parameters} {j : Fin P.n}
    {p : LocalState P.n (ProcessVariables P.n X) (Message P.n X)}
    {ν : PMF (LocalState P.n (ProcessVariables P.n X) (Message P.n X))}
    (h : ProgramStep P j p (Silent.τ : GatherLabel P.n X) ν) : False := by
  rw [gatherLabel_tau] at h; cases h

end Determinacy

end Gather
end ABA
end PLTS
