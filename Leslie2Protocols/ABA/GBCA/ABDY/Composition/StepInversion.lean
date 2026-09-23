/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sathiya / Claude
-/

import Leslie2Protocols.ABA.GBCA.ABDY.Composition.SpecificationOverRoundAlphabet

/-!
# The transitions of the round instance, read off their labels

`gbcaProgramStep_*` reads one program's row off its label: the participant's row as its guards
together with the Dirac it produces, and the idle row of a non-participant as the identity.
`gbcaNetworkStep_*` does the same for the round's network on the two rendezvous and on the silent
label.

The round records and the network state are the two components of `GBCA.ByABDY.ImplementationState`
(`GBCA/ABDY/Implementation.lean`), so the round instance and the implementation instance run on the
same state. What a joint step delivers is a program function given pointwise, by its value at the
acting process and its agreement with the old function elsewhere, where the implementation's rules
write with `Function.update`. `Function.eq_update_iff` identifies the two, and the `composition_*`
lemmas identify the state a row writes with `setProcess`, `recordGBCASend`, `setBound`, `deliverTo`
or `corrupt` applied to the old state.

`compositionExtended_joint_inversion` and `compositionExtended_tau_inversion` read a transition of
the programs beside the network backwards: on a visible label of the internal alphabet every
program and the network step together, and on the silent label only the network moves.

`gbcaNetworkStep_*_round` reads the network's row off a round-tagged label. The network has a row
only for its own round, so these readers return the round equation together with the network's
move, and a handshake label of another round carries no transition of the instance at all.
-/

namespace PLTS
namespace ABA
namespace GBCA.ByABDY

open Implementation Composition

/-! ### One program's rules, by label class

Each lemma reads a row of the table off its label: the participant's row as its
guards together with the Dirac it produces, and the idle row of a
non-participant as the identity. The state and the distribution are variables,
so `cases` unifies against any state of the program. -/

section ProgramStepInversion
variable {P : Parameters} {r : ℕ} {j : Fin P.n} {p : GBCA.ByABDY.RoundRecord P.n}
  {ν : PMF (GBCA.ByABDY.RoundRecord P.n)}

theorem gbcaProgramStep_callG_own {b : Bool}
    (h : GBCAProgramStep P r j p (Sum.inl (Sum.inl (.callG r j b))) ν) :
    p.process.input = none ∧
      ν = PMF.pure (p.setProcess { p.process with
        input := some b,
        sentInput := Function.update p.process.sentInput b true }) := by
  cases h
  case call => exact ⟨by assumption, rfl⟩
  case callIdle => exact absurd rfl ‹_ ≠ j›

theorem gbcaProgramStep_callG_foreign {id : Fin P.n} {b : Bool} (hid : id ≠ j)
    (h : GBCAProgramStep P r j p (Sum.inl (Sum.inl (.callG r id b))) ν) :
    ν = PMF.pure p := by
  cases h
  case call => exact absurd rfl hid
  case callIdle => rfl

theorem gbcaProgramStep_gbcaCallLoop {id : Fin P.n} {b : Bool}
    (h : GBCAProgramStep P r j p (Sum.inl (Sum.inr (.gbcaCallLoop r id b))) ν) :
    ν = PMF.pure p := by
  cases h
  case callLoop => rfl

theorem gbcaProgramStep_retGGrade2_own {v bnd : Bool}
    (h : GBCAProgramStep P r j p (Sum.inl (Sum.inl (.retG r j (.grade2 v) bnd))) ν) :
    p.process.input ≠ none ∧ p.process.sentEcho5 ≠ none ∧
      P.n - P.f ≤ p.receivedCount (.echo5 (some v)) ∧ p.process.returned = false ∧
      ν = PMF.pure (p.setProcess { p.process with returned := true }) := by
  cases h
  case retGrade2 =>
    exact ⟨by assumption, by assumption, by assumption, by assumption, rfl⟩
  case retIdle => exact absurd rfl ‹_ ≠ j›

theorem gbcaProgramStep_retGGrade1_own {v bnd : Bool}
    (h : GBCAProgramStep P r j p (Sum.inl (Sum.inl (.retG r j (.grade1 v) bnd))) ν) :
    p.process.input ≠ none ∧ p.process.sentEcho5 ≠ none ∧
      (∀ v, p.receivedCount (.echo5 (some v)) < P.n - P.f) ∧
      P.n - P.f ≤ p.echo5Count ∧ (∃ k, GBCA.ByABDY.Message.echo5 (some v) ∈ p.received k) ∧
      P.f + 1 ≤ p.receivedCount (.bind (some v)) ∧ p.bothValid P ∧
      p.process.returned = false ∧
      ν = PMF.pure (p.setProcess { p.process with returned := true }) := by
  cases h
  case retGrade1 =>
    exact ⟨by assumption, by assumption, by assumption, by assumption,
      by assumption, by assumption, by assumption, by assumption, rfl⟩
  case retIdle => exact absurd rfl ‹_ ≠ j›

theorem gbcaProgramStep_retGGrade0_own {bnd : Bool}
    (h : GBCAProgramStep P r j p (Sum.inl (Sum.inl (.retG r j .grade0 bnd))) ν) :
    p.process.input ≠ none ∧ p.process.sentEcho5 ≠ none ∧
      (∀ v, p.receivedCount (.echo5 (some v)) < P.n - P.f) ∧
      (∀ v, (∃ k, GBCA.ByABDY.Message.echo5 (some v) ∈ p.received k) →
        p.receivedCount (.bind (some v)) < P.f + 1) ∧
      P.n - P.f ≤ p.receivedCount (.echo5 none) ∧ p.bothValid P ∧
      p.process.returned = false ∧
      ν = PMF.pure (p.setProcess { p.process with returned := true }) := by
  cases h
  case retGrade0 =>
    exact ⟨by assumption, by assumption, by assumption, by assumption,
      by assumption, by assumption, by assumption, rfl⟩
  case retIdle => exact absurd rfl ‹_ ≠ j›

theorem gbcaProgramStep_retG_foreign {id : Fin P.n} {out : GBCAOutput} {bnd : Bool} (hid : id ≠ j)
    (h : GBCAProgramStep P r j p (Sum.inl (Sum.inl (.retG r id out bnd))) ν) :
    ν = PMF.pure p := by
  cases h
  case retIdle => rfl
  all_goals exact absurd rfl hid

theorem gbcaProgramStep_byzantineCallG_own {b : Bool}
    (h : GBCAProgramStep P r j p (Sum.inl (Sum.inr (.byzantineCallG r j b))) ν) :
    p.process.input = none ∧
      ν = PMF.pure (p.setProcess { p.process with
        input := some b,
        sentInput := Function.update p.process.sentInput b true }) := by
  cases h
  case byzantineCall => exact ⟨by assumption, rfl⟩
  case byzantineCallIdle => exact absurd rfl ‹_ ≠ j›

theorem gbcaProgramStep_byzantineCallG_foreign {k : Fin P.n} {b : Bool} (hk : k ≠ j)
    (h : GBCAProgramStep P r j p (Sum.inl (Sum.inr (.byzantineCallG r k b))) ν) :
    ν = PMF.pure p := by
  cases h
  case byzantineCall => exact absurd rfl hk
  case byzantineCallIdle => rfl

theorem gbcaProgramStep_byzantineCallGLoop {k : Fin P.n} {b : Bool}
    (h : GBCAProgramStep P r j p (Sum.inl (Sum.inr (.byzantineCallGLoop r k b))) ν) :
    ν = PMF.pure p := by
  cases h
  case byzantineCallLoop => rfl

theorem gbcaProgramStep_byzantineRetGGrade2_own {v bnd : Bool}
    (h : GBCAProgramStep P r j p (Sum.inl (Sum.inr (.byzantineRetG r j (.grade2 v) bnd))) ν) :
    p.process.input ≠ none ∧ p.process.sentEcho5 ≠ none ∧
      P.n - P.f ≤ p.receivedCount (.echo5 (some v)) ∧ p.process.returned = false ∧
      ν = PMF.pure (p.setProcess { p.process with returned := true }) := by
  cases h
  case byzantineRetGrade2 =>
    exact ⟨by assumption, by assumption, by assumption, by assumption, rfl⟩
  case byzantineRetIdle => exact absurd rfl ‹_ ≠ j›

theorem gbcaProgramStep_byzantineRetGGrade1_own {v bnd : Bool}
    (h : GBCAProgramStep P r j p (Sum.inl (Sum.inr (.byzantineRetG r j (.grade1 v) bnd))) ν) :
    p.process.input ≠ none ∧ p.process.sentEcho5 ≠ none ∧
      (∀ v, p.receivedCount (.echo5 (some v)) < P.n - P.f) ∧
      P.n - P.f ≤ p.echo5Count ∧ (∃ k, GBCA.ByABDY.Message.echo5 (some v) ∈ p.received k) ∧
      P.f + 1 ≤ p.receivedCount (.bind (some v)) ∧ p.bothValid P ∧
      p.process.returned = false ∧
      ν = PMF.pure (p.setProcess { p.process with returned := true }) := by
  cases h
  case byzantineRetGrade1 =>
    exact ⟨by assumption, by assumption, by assumption, by assumption,
      by assumption, by assumption, by assumption, by assumption, rfl⟩
  case byzantineRetIdle => exact absurd rfl ‹_ ≠ j›

theorem gbcaProgramStep_byzantineRetGGrade0_own {bnd : Bool}
    (h : GBCAProgramStep P r j p (Sum.inl (Sum.inr (.byzantineRetG r j .grade0 bnd))) ν) :
    p.process.input ≠ none ∧ p.process.sentEcho5 ≠ none ∧
      (∀ v, p.receivedCount (.echo5 (some v)) < P.n - P.f) ∧
      (∀ v, (∃ k, GBCA.ByABDY.Message.echo5 (some v) ∈ p.received k) →
        p.receivedCount (.bind (some v)) < P.f + 1) ∧
      P.n - P.f ≤ p.receivedCount (.echo5 none) ∧ p.bothValid P ∧
      p.process.returned = false ∧
      ν = PMF.pure (p.setProcess { p.process with returned := true }) := by
  cases h
  case byzantineRetGrade0 =>
    exact ⟨by assumption, by assumption, by assumption, by assumption,
      by assumption, by assumption, by assumption, rfl⟩
  case byzantineRetIdle => exact absurd rfl ‹_ ≠ j›

theorem gbcaProgramStep_byzantineRetG_foreign {k : Fin P.n} {out : GBCAOutput} {bnd : Bool}
    (hk : k ≠ j) (h : GBCAProgramStep P r j p (Sum.inl (Sum.inr (.byzantineRetG r k out bnd))) ν) :
    ν = PMF.pure p := by
  cases h
  case byzantineRetIdle => rfl
  all_goals exact absurd rfl hk

theorem gbcaProgramStep_send_input_own {b : Bool}
    (h : GBCAProgramStep P r j p (Sum.inr (.send j (.input b))) ν) :
    p.process.input ≠ none ∧ P.f + 1 ≤ p.receivedCount (.input b) ∧ p.process.sentInput b = false ∧
    ν = PMF.pure
    (p.setProcess { p.process with sentInput := Function.update p.process.sentInput b true }) := by
  cases h
  case sendRelay =>
    exact ⟨by assumption, by assumption, by assumption, rfl⟩
  case sendIdle => exact absurd rfl ‹_ ≠ j›

theorem gbcaProgramStep_send_echo_own {b : Bool}
    (h : GBCAProgramStep P r j p (Sum.inr (.send j (.echo b))) ν) :
    p.process.input ≠ none ∧ P.n - P.f ≤ p.receivedCount (.input b) ∧
      p.process.sentEcho = none ∧
      ν = PMF.pure (p.setProcess { p.process with sentEcho := some b }) := by
  cases h
  case sendEcho => exact ⟨by assumption, by assumption, by assumption, rfl⟩
  case sendIdle => exact absurd rfl ‹_ ≠ j›

theorem gbcaProgramStep_send_voteBit_own {b : Bool}
    (h : GBCAProgramStep P r j p (Sum.inr (.send j (.vote (some b)))) ν) :
    p.process.input ≠ none ∧
      P.n - P.f ≤ p.receivedCount (.echo b) ∧ p.process.sentVote = none ∧
      ν = PMF.pure (p.setProcess { p.process with sentVote := some (some b) }) := by
  cases h
  case sendVoteBit =>
    exact ⟨by assumption, by assumption, by assumption, rfl⟩
  case sendIdle => exact absurd rfl ‹_ ≠ j›

theorem gbcaProgramStep_send_voteBot_own
    (h : GBCAProgramStep P r j p (Sum.inr (.send j (.vote none))) ν) :
    p.process.input ≠ none ∧
      (∀ b, p.receivedCount (.echo b) < P.n - P.f) ∧
      P.n - P.f ≤ p.echoCount ∧ p.bothValid P ∧
      p.process.sentVote = none ∧
      ν = PMF.pure (p.setProcess { p.process with sentVote := some none }) := by
  cases h
  case sendVoteBot =>
    exact ⟨by assumption, by assumption, by assumption, by assumption,
      by assumption, rfl⟩
  case sendIdle => exact absurd rfl ‹_ ≠ j›

theorem gbcaProgramStep_send_bindBit_own {b : Bool}
    (h : GBCAProgramStep P r j p (Sum.inr (.send j (.bind (some b)))) ν) :
    p.process.input ≠ none ∧ p.process.sentVote ≠ none ∧
      P.n - P.f ≤ p.receivedCount (.vote (some b)) ∧ p.process.sentBind = none ∧
      ν = PMF.pure (p.setProcess { p.process with sentBind := some (some b) }) := by
  cases h
  case sendBindBit =>
    exact ⟨by assumption, by assumption, by assumption, by assumption, rfl⟩
  case sendIdle => exact absurd rfl ‹_ ≠ j›

theorem gbcaProgramStep_send_bindBot_own
    (h : GBCAProgramStep P r j p (Sum.inr (.send j (.bind none))) ν) :
    p.process.input ≠ none ∧ p.process.sentVote ≠ none ∧
      (∀ b, p.receivedCount (.vote (some b)) < P.n - P.f) ∧
      P.n - P.f ≤ p.voteCount ∧ p.bothValid P ∧
      p.process.sentBind = none ∧
      ν = PMF.pure (p.setProcess { p.process with sentBind := some none }) := by
  cases h
  case sendBindBot =>
    exact ⟨by assumption, by assumption, by assumption, by assumption,
      by assumption, by assumption, rfl⟩
  case sendIdle => exact absurd rfl ‹_ ≠ j›

theorem gbcaProgramStep_send_echo5Bit_own {b : Bool}
    (h : GBCAProgramStep P r j p (Sum.inr (.send j (.echo5 (some b)))) ν) :
    p.process.input ≠ none ∧ p.process.sentBind ≠ none ∧
      P.n - P.f ≤ p.receivedCount (.bind (some b)) ∧ p.process.sentEcho5 = none ∧
      ν = PMF.pure (p.setProcess { p.process with sentEcho5 := some (some b) }) := by
  cases h
  case sendEcho5Bit =>
    exact ⟨by assumption, by assumption, by assumption, by assumption, rfl⟩
  case sendIdle => exact absurd rfl ‹_ ≠ j›

theorem gbcaProgramStep_send_echo5Bot_own
    (h : GBCAProgramStep P r j p (Sum.inr (.send j (.echo5 none))) ν) :
    p.process.input ≠ none ∧ p.process.sentBind ≠ none ∧
      (∀ b, p.receivedCount (.bind (some b)) < P.n - P.f) ∧
      P.n - P.f ≤ p.bindCount ∧ p.bothValid P ∧
      p.process.sentEcho5 = none ∧
      ν = PMF.pure (p.setProcess { p.process with sentEcho5 := some none }) := by
  cases h
  case sendEcho5Bot =>
    exact ⟨by assumption, by assumption, by assumption, by assumption,
      by assumption, by assumption, rfl⟩
  case sendIdle => exact absurd rfl ‹_ ≠ j›

theorem gbcaProgramStep_send_foreign {k : Fin P.n} {m : GBCA.ByABDY.Message} (hk : k ≠ j)
    (h : GBCAProgramStep P r j p (Sum.inr (.send k m)) ν) : ν = PMF.pure p := by
  cases h
  case sendIdle => rfl
  all_goals exact absurd rfl hk

theorem gbcaProgramStep_deliver_own {k : Fin P.n} {m : GBCA.ByABDY.Message}
    (h : GBCAProgramStep P r j p (Sum.inr (.deliver j k m)) ν) :
    ν = PMF.pure (p.deliverTo k m) := by
  cases h
  case deliverReceive => rfl
  case deliverIdle => exact absurd rfl ‹_ ≠ j›

theorem gbcaProgramStep_deliver_foreign {i k : Fin P.n} {m : GBCA.ByABDY.Message} (hi : i ≠ j)
    (h : GBCAProgramStep P r j p (Sum.inr (.deliver i k m)) ν) : ν = PMF.pure p := by
  cases h
  case deliverReceive => exact absurd rfl hi
  case deliverIdle => rfl

end ProgramStepInversion
/-! ### The network's rules, by label class -/

section NetworkStepInversion
variable {P : Parameters} {r : ℕ} {w : NetworkState P.n} {μ : PMF (NetworkState P.n)}

theorem gbcaNetworkStep_send {j : Fin P.n} {m : GBCA.ByABDY.Message}
    (h : GBCANetworkStep P r w (Sum.inr (.send j m)) μ) :
    μ = PMF.pure (w.recordGBCASend j m) := by
  cases h; rfl

theorem gbcaNetworkStep_deliver {i j : Fin P.n} {m : GBCA.ByABDY.Message}
    (h : GBCANetworkStep P r w (Sum.inr (.deliver i j m)) μ) :
    m ∈ w.sent j ∧ μ = PMF.pure w := by
  cases h; exact ⟨by assumption, rfl⟩

theorem gbcaNetworkStep_tau (h : GBCANetworkStep P r w (Sum.inl (Sum.inl .tau)) μ) :
    ∃ (k : Fin P.n) (m : GBCA.ByABDY.Message), k ∈ w.F ∧ μ = PMF.pure (w.recordGBCASend k m) := by
  cases h
  case byzantineGBCA k m hF => exact ⟨k, m, hF, rfl⟩

end NetworkStepInversion
/-! ### The write a row makes on the composed state

The round records and the network state are the two components of `GBCA.ByABDY.ImplementationState`
(`GBCA/ABDY/Implementation.lean`), so the round instance and the implementation instance run on the
same state and every rule of the one is a rule of the other read in the implementation's accessors.
A joint step delivers a program function pointwise: its value at the acting process, and its
agreement with the old one elsewhere. `Function.eq_update_iff` reads that function as the old one
updated at the acting process, and the lemmas here identify the state a row of the implementation
writes with `Function.update`. -/

section Writes
variable {P : Parameters} {u x : ∀ _ : Fin P.n, GBCA.ByABDY.RoundRecord P.n} {w : NetworkState P.n}

/-- A record write at one program, with the network state untouched. -/
theorem composition_setProcess {j : Fin P.n} {pr : GBCA.ByABDY.ProcessRecord}
    (hj : x j = (u j).setProcess pr) (hne : ∀ i, i ≠ j → x i = u i) :
    ((x, w) : GBCA.ByABDY.ImplementationState P.n) = GBCA.ByABDY.ImplementationState.setProcess
    (u, w) j pr := by
  rw [Function.eq_update_iff.mpr ⟨hj, hne⟩]
  rfl

/-- A record write at one program together with the network state recording the message
that write multicasts. -/
theorem composition_setProcess_recordGBCASend {j : Fin P.n} {pr : GBCA.ByABDY.ProcessRecord}
    {m : GBCA.ByABDY.Message} (hj : x j = (u j).setProcess pr) (hne : ∀ i, i ≠ j → x i = u i) :
    ((x, w.recordGBCASend j m) : GBCA.ByABDY.ImplementationState P.n) =
    (GBCA.ByABDY.ImplementationState.setProcess (u, w) j pr).multicast j m := by
  rw [Function.eq_update_iff.mpr ⟨hj, hne⟩]
  rfl

/-- A record write at one program together with the network state's write of
the round's bound bit. -/
theorem composition_setProcess_setBound {j : Fin P.n} {pr : GBCA.ByABDY.ProcessRecord} {β : Bool}
    (hj : x j = (u j).setProcess pr) (hne : ∀ i, i ≠ j → x i = u i) :
    ((x, w.setBound β) : GBCA.ByABDY.ImplementationState P.n)
      = (GBCA.ByABDY.ImplementationState.setProcess (u, w) j pr).setBound β := by
  rw [Function.eq_update_iff.mpr ⟨hj, hne⟩]
  rfl

/-- The programs remain unchanged. -/
theorem composition_idle (hall : ∀ i, x i = u i) :
    ((x, w) : GBCA.ByABDY.ImplementationState P.n) = (u, w) := by
  rw [funext hall]

/-- A delivery: the receiver files the message under its sender's row. -/
theorem composition_deliver {i k : Fin P.n} {m : GBCA.ByABDY.Message}
    (hi : x i = (u i).deliverTo k m) (hne : ∀ i', i' ≠ i → x i' = u i') :
    ((x, w) : GBCA.ByABDY.ImplementationState P.n) = GBCA.ByABDY.ImplementationState.receiveMessage
    (u, w) i k m := by
  rw [Function.eq_update_iff.mpr ⟨hi, hne⟩]
  rfl

/-- A Byzantine injection: the network state records a message under a corrupted
sender. -/
theorem composition_recordGBCASend {k : Fin P.n} {m : GBCA.ByABDY.Message} :
    ((u, w.recordGBCASend k m) : GBCA.ByABDY.ImplementationState P.n)
      = GBCA.ByABDY.ImplementationState.multicast (u, w) k m := rfl

/-- Corruption is the network state's own write, which is the implementation's (D1). -/
theorem composition_corrupt (k : Fin P.n) :
    ((u, w.corrupt P k) : GBCA.ByABDY.ImplementationState P.n)
      = GBCA.ByABDY.ImplementationState.corrupt P k (u, w) := rfl

end Writes
/-! ### Reading an instance transition backwards

Two inversions of the composition, the counterparts of `compositionExtended_event_step` /
`compositionExtended_label_step` / `compositionExtended_tau_network`: on a visible label of the
internal alphabet every program and the network step together, and on the silent label
only the network moves. -/

/-- A visible transition of the programs beside the network: every program and
the network step on the label, and the joint distribution is their Dirac
product. -/
theorem compositionExtended_joint_inversion {P : Parameters} {r : ℕ}
    {u : ∀ _ : Fin P.n, GBCA.ByABDY.RoundRecord P.n} {w : NetworkState P.n} {L : GBCALabel P.n}
    {μ : PMF (GBCA.ByABDY.ImplementationState P.n)} (hL : L ≠ (Silent.τ : GBCALabel P.n))
    (h : (compositionExtended P r).step (u, w) L μ) :
    ∃ (x : ∀ _ : Fin P.n, GBCA.ByABDY.RoundRecord P.n) (w' : NetworkState P.n),
      μ = PMF.pure (x, w') ∧ (∀ i, GBCAProgramStep P r i (u i) L (PMF.pure (x i))) ∧
        GBCANetworkStep P r w L (PMF.pure w') := by
  rw [compositionExtended, System.parallel_step] at h
  rcases h with ⟨-, μ₁, μ₂, hs, hn, rfl⟩ | ⟨hτ, -⟩ | ⟨hτ, -⟩
  · obtain ⟨x, rfl, hall⟩ := gbcaProgramProduct_inversion hs
    obtain ⟨w', rfl⟩ := gbcaNetworkStep_dirac hn
    exact ⟨x, w', prodPMF_pure_pure _ _, hall, hn⟩
  · exact absurd hτ hL
  · exact absurd hτ hL

/-- A silent transition of the programs beside the network is a network-local
injection: no program has a `τ` row. -/
theorem compositionExtended_tau_inversion {P : Parameters} {r : ℕ}
    {u : ∀ _ : Fin P.n, GBCA.ByABDY.RoundRecord P.n} {w : NetworkState P.n}
    {μ : PMF (GBCA.ByABDY.ImplementationState P.n)}
    (h : (compositionExtended P r).step (u, w) (Sum.inl (Sum.inl Label.tau)) μ) :
    ∃ w' : NetworkState P.n, μ = PMF.pure (u, w') ∧
      GBCANetworkStep P r w (Sum.inl (Sum.inl Label.tau)) (PMF.pure w') := by
  rw [compositionExtended, System.parallel_step] at h
  rcases h with ⟨hτ, -⟩ | ⟨-, μ₁, hs, rfl⟩ | ⟨-, μ₂, hn, rfl⟩
  · exact absurd rfl hτ
  · exact absurd hs gbcaProgramProduct_no_tau
  · obtain ⟨w', rfl⟩ := gbcaNetworkStep_dirac hn
    exact ⟨w', prodPMF_pure_pure _ _, hn⟩

/-! ### The network's rules read off a round-tagged label

The network has a row only for its own round: a handshake label of another round
carries no transition of the instance at all. These readers therefore return
the round equation together with the network's move. -/

section RoundTaggedNetworkStepInversion
variable {P : Parameters} {r : ℕ} {w : NetworkState P.n} {μ : PMF (NetworkState P.n)}

theorem gbcaNetworkStep_callG_round {r' : ℕ} {id : Fin P.n} {b : Bool}
    (h : GBCANetworkStep P r w (Sum.inl (Sum.inl (.callG r' id b))) μ) :
    r' = r ∧ μ = PMF.pure (w.recordGBCASend id (.input b)) := by
  cases h; exact ⟨rfl, rfl⟩

theorem gbcaNetworkStep_retG_round {r' : ℕ} {id : Fin P.n} {out : GBCAOutput} {bnd : Bool}
    (h : GBCANetworkStep P r w (Sum.inl (Sum.inl (.retG r' id out bnd))) μ) :
    r' = r ∧ bnd = w.bound.getD (GBCA.ByABDY.boundOf w.sent w.F out) ∧
      μ = PMF.pure (w.setBound bnd) := by
  cases h with
  | retGIdle _ _ _ hbnd => exact ⟨rfl, hbnd, rfl⟩

theorem gbcaNetworkStep_gbcaCallLoop_round {r' : ℕ} {id : Fin P.n} {b : Bool}
    (h : GBCANetworkStep P r w (Sum.inl (Sum.inr (.gbcaCallLoop r' id b))) μ) :
    r' = r ∧ μ = PMF.pure w := by
  cases h; exact ⟨rfl, rfl⟩

theorem gbcaNetworkStep_byzantineCallG_round {r' : ℕ} {k : Fin P.n} {b : Bool}
    (h : GBCANetworkStep P r w (Sum.inl (Sum.inr (.byzantineCallG r' k b))) μ) :
    r' = r ∧ μ = PMF.pure (w.recordGBCASend k (.input b)) := by
  cases h; exact ⟨rfl, rfl⟩

theorem gbcaNetworkStep_byzantineCallGLoop_round {r' : ℕ} {k : Fin P.n} {b : Bool}
    (h : GBCANetworkStep P r w (Sum.inl (Sum.inr (.byzantineCallGLoop r' k b))) μ) :
    r' = r ∧ μ = PMF.pure w := by
  cases h; exact ⟨rfl, rfl⟩

theorem gbcaNetworkStep_byzantineRetG_round {r' : ℕ} {k : Fin P.n} {out : GBCAOutput} {bnd : Bool}
    (h : GBCANetworkStep P r w (Sum.inl (Sum.inr (.byzantineRetG r' k out bnd))) μ) :
    r' = r ∧ bnd = w.bound.getD (GBCA.ByABDY.boundOf w.sent w.F out) ∧
      μ = PMF.pure (w.setBound bnd) := by
  cases h with
  | byzantineRetG _ _ _ hbnd => exact ⟨rfl, hbnd, rfl⟩

/-! The labels the network does not offer at all: the ABA API, the coin ports,
corruption, and the protocol network's own rendezvous. -/

theorem gbcaNetworkStep_callABA_noStep {id : Fin P.n} {b : Bool}
    (h : GBCANetworkStep P r w (Sum.inl (Sum.inl (.callABA id b))) μ) : False := by cases h

theorem gbcaNetworkStep_retABA_noStep {id : Fin P.n} {b : Bool}
    (h : GBCANetworkStep P r w (Sum.inl (Sum.inl (.retABA id b))) μ) : False := by cases h

theorem gbcaNetworkStep_callW_noStep {r' : ℕ} {id : Fin P.n}
    (h : GBCANetworkStep P r w (Sum.inl (Sum.inl (.callW r' id))) μ) : False := by cases h

theorem gbcaNetworkStep_retW_noStep {r' : ℕ} {id : Fin P.n} {b : Bool}
    (h : GBCANetworkStep P r w (Sum.inl (Sum.inl (.retW r' id b))) μ) : False := by cases h

theorem gbcaNetworkStep_fail_noStep {k : Fin P.n}
    (h : GBCANetworkStep P r w (Sum.inl (Sum.inl (.fail k))) μ) : False := by cases h

theorem gbcaNetworkStep_gbcaSend_noStep {r' : ℕ} {j : Fin P.n} {m : GBCA.ByABDY.Message}
    (h : GBCANetworkStep P r w (Sum.inl (Sum.inr (.gbcaSend r' j m))) μ) : False := by cases h

theorem gbcaNetworkStep_gbcaDeliver_noStep {r' : ℕ} {i j : Fin P.n} {m : GBCA.ByABDY.Message}
    (h : GBCANetworkStep P r w (Sum.inl (Sum.inr (.gbcaDeliver r' i j m))) μ) : False := by cases h

theorem gbcaNetworkStep_decidedSend_noStep {j : Fin P.n} {b : Bool}
    (h : GBCANetworkStep P r w (Sum.inl (Sum.inr (.decidedSend j b))) μ) : False := by cases h

theorem gbcaNetworkStep_decidedDeliver_noStep {i j : Fin P.n} {b : Bool}
    (h : GBCANetworkStep P r w (Sum.inl (Sum.inr (.decidedDeliver i j b))) μ) : False := by cases h

theorem gbcaNetworkStep_retWPublish_noStep {r' : ℕ} {id : Fin P.n} {c b : Bool}
    (h : GBCANetworkStep P r w (Sum.inl (Sum.inr (.retWPublish r' id c b))) μ) : False := by cases h

theorem gbcaNetworkStep_byzantineCallW_noStep {r' : ℕ} {k : Fin P.n}
    (h : GBCANetworkStep P r w (Sum.inl (Sum.inr (.byzantineCallW r' k))) μ) : False := by cases h

theorem gbcaNetworkStep_byzantineRetW_noStep {r' : ℕ} {k : Fin P.n} {b : Bool}
    (h : GBCANetworkStep P r w (Sum.inl (Sum.inr (.byzantineRetW r' k b))) μ) : False := by cases h

end RoundTaggedNetworkStepInversion
end GBCA.ByABDY
end ABA
end PLTS
