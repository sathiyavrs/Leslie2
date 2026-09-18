/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sathiya / Claude
-/

import Leslie2Protocols.ABA.Gather.Sub

/-!
# The rows of the gather instance over the broadcast specification

`IdealSubStep` is the rule table of `Gather.idealSub` (`ABA/Gather/Sub.lean`) —
the `n` gather programs beside the gather network, in parallel with `2n` lifted
broadcast specifications — stated over the composition's state through the four
views `ga`, `brbIn`, `brbBind`, `core`. It is a relation on that state; the
system is the composition.

`idealSub_step_iff_row` is the row characterisation: at a specification label
`l₀`, the transitions of the composition over the labels `specPull` sends to
`l₀` are exactly the `l₀`-rows of `IdealSubStep`, on the same state and with the
same distribution.

## The four rows of a call

A broadcast specification answers `call x` on two rows, the call and the
input-enabledness loop, and the composition reads it along `inPull id`, which
puts both rows under the gather label `call id x` and both under the gather call
loop. The gather program writes its record on the first label and stands still
on the second. The four combinations are four rows: `call` (both record),
`callSpecLoop` (the program records, the instance loops), `callProcLoop` (the
instance records, the program loops) and `callLoop` (neither moves). The same
split reaches the bind call, whose two rows are `bindCall` and
`bindCallSpecLoop`.

## The corrupted set

Each broadcast specification carries its own corrupted set, kept in lockstep
with the gather network's by the `fail` row. A commit guard therefore reads the
corrupted set of the instance it commits in.
-/

namespace PLTS
namespace ABA
namespace Gather

variable {X : Type} [DecidableEq X]

/-! ### Reading a lifted broadcast specification

A lifted broadcast specification is the specification read along `BRB.specPull`
and then along the composition's pullback. The lemmas below pass between its
transitions and the specification's rows. -/

/-- A transition of a lifted broadcast specification is a specification row at
the label `BRB.specPull` projects to. -/
theorem liftedSpec_step_row {M : Type} {P : Params} {ldr : Fin P.n}
    {s s' : BRB.SpecState P.n M} {l : BRB.SubLab P.n M} {l₀ : BRB.Lab P.n M}
    (hl : BRB.specPull P.n M l = some l₀)
    (h : (BRB.liftedSpec P ldr M).step s l (PMF.pure s')) : BRB.Step P ldr s l₀ (PMF.pure s') :=
  (System.mapIdle_step_some hl _).mp h

/-- A specification row is a transition of the lifted specification at any
label `BRB.specPull` projects to it. -/
theorem row_liftedSpec_step {M : Type} {P : Params} {ldr : Fin P.n}
    {s s' : BRB.SpecState P.n M} {l : BRB.SubLab P.n M} {l₀ : BRB.Lab P.n M}
    (hl : BRB.specPull P.n M l = some l₀)
    (h : BRB.Step P ldr s l₀ (PMF.pure s')) : (BRB.liftedSpec P ldr M).step s l (PMF.pure s') :=
  (System.mapIdle_step_some hl _).mpr h

section SpecInversion

variable {M : Type} {P : Params} {ldr : Fin P.n} {s : BRB.SpecState P.n M}
  {μ : PMF (BRB.SpecState P.n M)}

/-- The two rows of a call: the record write and the loop. -/
theorem specStep_call {m : M} (h : BRB.Step P ldr s (.call m) μ) :
    (s.input = none ∧ μ = PMF.pure { s with input := some m }) ∨ μ = PMF.pure s := by
  cases h
  case call => exact Or.inl ⟨by assumption, rfl⟩
  case callLoop => exact Or.inr rfl

/-- The one silent row: the commit. -/
theorem specStep_tau (h : BRB.Step P ldr s .tau μ) :
    ∃ m : M, s.val = none ∧ (ldr ∈ s.F ∨ s.input = some m) ∧
      μ = PMF.pure { s with val := some m } := by
  cases h
  case commit m hv hm => exact ⟨m, hv, hm, rfl⟩

/-- The one return row. -/
theorem specStep_ret {id : Fin P.n} {m : M} (h : BRB.Step P ldr s (.ret id m) μ) :
    s.val = some m ∧ s.ret id = false ∧
      μ = PMF.pure { s with ret := Function.update s.ret id true } := by
  cases h; exact ⟨by assumption, by assumption, rfl⟩

/-- The one corruption row. -/
theorem specStep_fail {id : Fin P.n} (h : BRB.Step P ldr s (.fail id) μ) :
    μ = PMF.pure (s.corrupt P id) := by
  cases h; rfl

end SpecInversion

/-! ### The rows -/

/-- The rows of the gather instance over the broadcast specification
(`Gather.idealSub`), stated over the composition's state: one constructor per
case of `Gather.idealSub_step_iff_row`. All transitions are Dirac. -/
inductive IdealSubStep (P : Params) :
    IdealSubState P.n X → Lab P.n X → PMF (IdealSubState P.n X) → Prop
  /-- The call arrives: the gather record and the input instance both record
  the payload. -/
  | call (s : IdealSubState P.n X) (id : Fin P.n) (x : X)
      (h : ((ga s).proc id).input = none) (hb : (brbIn s id).input = none) :
      IdealSubStep P s (.call id x)
        (PMF.pure (setBrbIn (setGa s ((ga s).setProc id { (ga s).proc id with input := some x }))
          (Function.update (brbIn s) id { brbIn s id with input := some x })))
  /-- The call arrives and the input instance answers on its loop row: the
  gather record alone moves. -/
  | callSpecLoop (s : IdealSubState P.n X) (id : Fin P.n) (x : X)
      (h : ((ga s).proc id).input = none) :
      IdealSubStep P s (.call id x)
        (PMF.pure (setGa s ((ga s).setProc id { (ga s).proc id with input := some x })))
  /-- The gather program answers on its loop row and the input instance records
  the payload: the input instance alone moves. -/
  | callProcLoop (s : IdealSubState P.n X) (id : Fin P.n) (x : X)
      (hb : (brbIn s id).input = none) :
      IdealSubStep P s (.call id x)
        (PMF.pure (setBrbIn s (Function.update (brbIn s) id
          { brbIn s id with input := some x })))
  /-- Input-enabledness loop for `call`: nothing moves. -/
  | callLoop (s : IdealSubState P.n X) (id : Fin P.n) (x : X) :
      IdealSubStep P s (.call id x) (PMF.pure s)
  /-- An input instance commits: anything under a corrupted leader, the
  leader's input otherwise. -/
  | commitIn (s : IdealSubState P.n X) (k : Fin P.n) (v : X)
      (hv : (brbIn s k).val = none) (hm : k ∈ (brbIn s k).F ∨ (brbIn s k).input = some v) :
      IdealSubStep P s .tau
        (PMF.pure (setBrbIn s (Function.update (brbIn s) k { brbIn s k with val := some v })))
  /-- A bind instance commits. -/
  | commitBind (s : IdealSubState P.n X) (q : Fin P.n) (U : APSet P.n X)
      (hv : (brbBind s q).val = none)
      (hm : q ∈ (brbBind s q).F ∨ (brbBind s q).input = some U) :
      IdealSubStep P s .tau
        (PMF.pure (setBrbBind s (Function.update (brbBind s) q
          { brbBind s q with val := some U })))
  /-- Asynchronous delivery on the gather network. -/
  | deliver (s : IdealSubState P.n X) (i j : Fin P.n) (m : GaMsg P.n X)
      (h : m ∈ (ga s).sent j) :
      IdealSubStep P s .tau (PMF.pure (setGa s ((ga s).recvMsg i j m)))
  /-- `ECHO`: the process holds every pair of a payload set of at least `n − f`
  pairs. -/
  | echo (s : IdealSubState P.n X) (j : Fin P.n) (A : APSet P.n X)
      (hin : ((ga s).proc j).input ≠ none) (happ : approvedBy ((ga s).proc j) A)
      (hcard : P.n - P.f ≤ A.card) (hsend : ((ga s).proc j).sentEcho = none) :
      IdealSubStep P s .tau
        (PMF.pure (setGa s (((ga s).setProc j
          { (ga s).proc j with sentEcho := some A }).mcast j (.echo A))))
  /-- `VOTE`: `n − f` senders' approved `ECHO` payloads, each contained in the
  vote payload, are delivered here. -/
  | vote (s : IdealSubState P.n X) (j : Fin P.n) (U : APSet P.n X)
      (hin : ((ga s).proc j).input ≠ none) (happ : approvedBy ((ga s).proc j) U)
      (hQ : ∃ Q : Finset (Fin P.n), P.n - P.f ≤ Q.card ∧
        ∀ q ∈ Q, ∃ A, GaMsg.echo A ∈ (ga s).recv j q ∧ approvedBy ((ga s).proc j) A ∧ A ⊆ U)
      (hsend : ((ga s).proc j).sentVote = none) :
      IdealSubStep P s .tau
        (PMF.pure (setGa s (((ga s).setProc j
          { (ga s).proc j with sentVote := some U }).mcast j (.vote U))))
  /-- `BIND`: `n − f` senders' approved `VOTE` payloads, each contained in the
  bind payload, are delivered here, and the bind instance records it. -/
  | bindCall (s : IdealSubState P.n X) (j : Fin P.n) (U : APSet P.n X)
      (hin : ((ga s).proc j).input ≠ none) (happ : approvedBy ((ga s).proc j) U)
      (hQ : ∃ Q : Finset (Fin P.n), P.n - P.f ≤ Q.card ∧
        ∀ q ∈ Q, ∃ W, GaMsg.vote W ∈ (ga s).recv j q ∧ approvedBy ((ga s).proc j) W ∧ W ⊆ U)
      (hb : (brbBind s j).input = none) :
      IdealSubStep P s .tau
        (PMF.pure (setBrbBind s (Function.update (brbBind s) j
          { brbBind s j with input := some U })))
  /-- `BIND` with the bind instance answering on its loop row: nothing
  moves. -/
  | bindCallSpecLoop (s : IdealSubState P.n X) (j : Fin P.n) (U : APSet P.n X)
      (hin : ((ga s).proc j).input ≠ none) (happ : approvedBy ((ga s).proc j) U)
      (hQ : ∃ Q : Finset (Fin P.n), P.n - P.f ≤ Q.card ∧
        ∀ q ∈ Q, ∃ W, GaMsg.vote W ∈ (ga s).recv j q ∧ approvedBy ((ga s).proc j) W ∧ W ⊆ U) :
      IdealSubStep P s .tau (PMF.pure s)
  /-- Byzantine injection on the gather network. -/
  | byz (s : IdealSubState P.n X) (j : Fin P.n) (m : GaMsg P.n X) (h : j ∈ (ga s).F) :
      IdealSubStep P s .tau (PMF.pure (setGa s ((ga s).mcast j m)))
  /-- An input instance returns its committed value to `j`, which files it in
  its store. -/
  | inRet (s : IdealSubState P.n X) (k j : Fin P.n) (v : X)
      (hv : (brbIn s k).val = some v) (hr : (brbIn s k).ret j = false) :
      IdealSubStep P s .tau
        (PMF.pure (setBrbIn (setGa s ((ga s).setProc j
            { (ga s).proc j with
              delivIn := Function.update ((ga s).proc j).delivIn k (some v) }))
          (Function.update (brbIn s) k
            { brbIn s k with ret := Function.update (brbIn s k).ret j true })))
  /-- A bind instance returns its committed payload to `j`, which files it in
  its store. -/
  | bindRet (s : IdealSubState P.n X) (q j : Fin P.n) (U : APSet P.n X)
      (hv : (brbBind s q).val = some U) (hr : (brbBind s q).ret j = false) :
      IdealSubStep P s .tau
        (PMF.pure (setBrbBind (setGa s ((ga s).setProc j
            { (ga s).proc j with
              delivBind := Function.update ((ga s).proc j).delivBind q (some U) }))
          (Function.update (brbBind s) q
            { brbBind s q with ret := Function.update (brbBind s q).ret j true })))
  /-- Return: the output's entries are held here, and `n − f` bind payloads
  held here are sub-maps of it. The label carries the instance's core, which
  this row writes if it is unwritten. -/
  | ret (s : IdealSubState P.n X) (id : Fin P.n) (g : Fin P.n → Option X)
      (hin : ((ga s).proc id).input ≠ none)
      (hsub : ∀ k x, g k = some x → holdsIn ((ga s).proc id) k x)
      (hQ : ∃ Q : Finset (Fin P.n), P.n - P.f ≤ Q.card ∧
        ∀ q ∈ Q, ∃ U, holdsBind ((ga s).proc id) q U ∧ APSet.subMap U g)
      (hr : ((ga s).proc id).returned = false) :
      IdealSubStep P s (.ret id g ((core s).getD (coreOfNet P (ga s).2)))
        (PMF.pure (setCore (setGa s ((ga s).setProc id
          { (ga s).proc id with returned := true }))
          (some ((core s).getD (coreOfNet P (ga s).2)))))
  /-- Corruption (deviation D1), in lockstep across the gather network state
  and every broadcast coordinate. -/
  | fail (s : IdealSubState P.n X) (id : Fin P.n) :
      IdealSubStep P s (.fail id)
        (PMF.pure (corruptAll P id (BRB.SpecState.corrupt P id)
          (BRB.SpecState.corrupt P id) s))


omit [DecidableEq X] in
/-- A specification row read through the composition's pullback. -/
theorem liftSpec_row {M : Type} {P : Params} {ldr : Fin P.n}
    {ψ : GaLab P.n X → Option (BRB.SubLab P.n M)} {L : GaLab P.n X}
    {lb : BRB.SubLab P.n M} {l₀ : BRB.Lab P.n M} {s s' : BRB.SpecState P.n M}
    (hφ : ψ L = some lb) (hl : BRB.specPull P.n M lb = some l₀)
    (h : ((BRB.liftedSpec P ldr M).mapIdle ψ).step s L (PMF.pure s')) :
    BRB.Step P ldr s l₀ (PMF.pure s') :=
  liftedSpec_step_row hl ((System.mapIdle_step_some hφ _).mp h)

omit [DecidableEq X] in
/-- A specification row is a transition of the instance read through the
composition's pullback. -/
theorem row_liftSpec {M : Type} {P : Params} {ldr : Fin P.n}
    {ψ : GaLab P.n X → Option (BRB.SubLab P.n M)} {L : GaLab P.n X}
    {lb : BRB.SubLab P.n M} {l₀ : BRB.Lab P.n M} {s s' : BRB.SpecState P.n M}
    (hφ : ψ L = some lb) (hl : BRB.specPull P.n M lb = some l₀)
    (h : BRB.Step P ldr s l₀ (PMF.pure s')) :
    ((BRB.liftedSpec P ldr M).mapIdle ψ).step s L (PMF.pure s') :=
  (System.mapIdle_step_some hφ _).mpr (row_liftedSpec_step hl h)

/-! ### The row characterisation -/

/-- **The projection.** -/
theorem idealSub_step_row (P : Params) :
    ∀ (s : IdealSubState P.n X) (l : SubLab P.n X) (μ : PMF (IdealSubState P.n X)),
      (idealSub P X).step s l μ →
      ∃ l₀, specPull P.n X l = some l₀ ∧ IdealSubStep P s l₀ μ := by
  have hIn : ∀ k : Fin P.n, (BRB.liftedSpec P k X).IsLTS := fun k => BRB.liftedSpec_isLTS P k
  have hBind : ∀ q : Fin P.n, (BRB.liftedSpec P q (APSet P.n X)).IsLTS :=
    fun q => BRB.liftedSpec_isLTS P q
  rintro ⟨⟨u, w⟩, a, b⟩ l μ hstep
  rcases (subAt_step_iff P X (fun k => BRB.liftedSpec P k X)
      (fun q => BRB.liftedSpec P q (APSet P.n X)) _ l μ).mp hstep with ⟨rfl, e, hev⟩ | hlab
  · obtain ⟨x, w', a', b', rfl, hproc, hnet, hin, hbind⟩ :=
      preAt_joint_inv hIn hBind (by simp) hev
    refine ⟨Lab.tau, rfl, ?_⟩
    cases e with
    | snd j m =>
      have hfor : ∀ i, i ≠ j → x i = u i :=
        fun i hi => PMF.pure_injective (stepG_snd_foreign (Ne.symm hi) (hproc i))
      have hw : w' = { w with net := w.net.post j m } := PMF.pure_injective (netStep_snd hnet)
      have ha : a' = a := funext fun k => lift_step_none rfl (hin k)
      have hb : b' = b := funext fun q => lift_step_none rfl (hbind q)
      subst hw; subst ha; subst hb
      cases m with
      | echo A =>
        obtain ⟨hinp, happ, hcard, hsend, hx⟩ := stepG_snd_echo_own (hproc j)
        rw [sub_setProc_post (PMF.pure_injective hx) hfor]
        exact IdealSubStep.echo _ j A hinp happ hcard hsend
      | vote U =>
        obtain ⟨hinp, happ, hQ, hsend, hx⟩ := stepG_snd_vote_own (hproc j)
        rw [sub_setProc_post (PMF.pure_injective hx) hfor]
        exact IdealSubStep.vote _ j U hinp happ hQ hsend
    | dlv i j m =>
      obtain ⟨hmem, hw⟩ := netStep_dlv hnet
      have hw' : w' = w := PMF.pure_injective hw
      have ha : a' = a := funext fun k => lift_step_none rfl (hin k)
      have hb : b' = b := funext fun q => lift_step_none rfl (hbind q)
      subst hw'; subst ha; subst hb
      have hfor : ∀ i', i' ≠ i → x i' = u i' :=
        fun i' hi' => PMF.pure_injective (stepG_dlv_foreign (Ne.symm hi') (hproc i'))
      rw [sub_deliver (PMF.pure_injective (stepG_dlv_own (hproc i))) hfor]
      exact IdealSubStep.deliver _ i j m hmem
    | inRet k j v =>
      have hw : w' = w := PMF.pure_injective (netStep_inRet hnet)
      have hb : b' = b := funext fun q => lift_step_none rfl (hbind q)
      subst hw; subst hb
      obtain ⟨hval, hret, hak⟩ :=
        specStep_ret (liftSpec_row (lb := Sum.inl (BRB.Lab.ret j v)) (by simp) rfl (hin k))
      have haf : ∀ k', k' ≠ k → a' k' = a k' :=
        fun k' hk' => lift_step_none (by simp [hk']) (hin k')
      have ha : a' = Function.update a k { a k with ret := Function.update (a k).ret j true } :=
        funPin (PMF.pure_injective hak) haf
      have hfor : ∀ i, i ≠ j → x i = u i :=
        fun i hi => PMF.pure_injective (stepG_inRet_foreign (Ne.symm hi) (hproc i))
      have hxj := PMF.pure_injective (stepG_inRet_own (hproc j))
      subst ha
      rw [procFun_update hxj hfor]
      exact IdealSubStep.inRet _ k j v hval hret
    | bindCall j U =>
      have hw : w' = w := PMF.pure_injective (netStep_bindCall hnet)
      have ha : a' = a := funext fun k => lift_step_none rfl (hin k)
      subst hw; subst ha
      obtain ⟨hinp, happ, hQ, hxj⟩ := stepG_bindCall_own (hproc j)
      have hxall : ∀ i, x i = u i := by
        intro i
        by_cases hi : i = j
        · subst hi; exact PMF.pure_injective hxj
        · exact PMF.pure_injective (stepG_bindCall_foreign (Ne.symm hi) (hproc i))
      have hbf : ∀ q, q ≠ j → b' q = b q :=
        fun q hq => lift_step_none (by simp [hq]) (hbind q)
      rcases specStep_call (liftSpec_row (lb := Sum.inl (BRB.Lab.call U)) (by simp) rfl
          (hbind j)) with ⟨hbin, hbq⟩ | hbq
      · have hb : b' = Function.update b j { b j with input := some U } :=
          funPin (PMF.pure_injective hbq) hbf
        subst hb
        rw [sub_idle hxall, sub_setBrbBind]
        exact IdealSubStep.bindCall _ j U hinp happ hQ hbin
      · have hb : b' = b := funext fun q => by
          by_cases hq : q = j
          · subst hq; exact PMF.pure_injective hbq
          · exact hbf q hq
        subst hb
        rw [sub_idle hxall]
        exact IdealSubStep.bindCallSpecLoop _ j U hinp happ hQ
    | bindRet q j U =>
      have hw : w' = w := PMF.pure_injective (netStep_bindRet hnet)
      have ha : a' = a := funext fun k => lift_step_none rfl (hin k)
      subst hw; subst ha
      obtain ⟨hval, hret, hbq⟩ :=
        specStep_ret (liftSpec_row (lb := Sum.inl (BRB.Lab.ret j U)) (by simp) rfl (hbind q))
      have hbf : ∀ q', q' ≠ q → b' q' = b q' :=
        fun q' hq' => lift_step_none (by simp [hq']) (hbind q')
      have hb : b' = Function.update b q { b q with ret := Function.update (b q).ret j true } :=
        funPin (PMF.pure_injective hbq) hbf
      have hfor : ∀ i, i ≠ j → x i = u i :=
        fun i hi => PMF.pure_injective (stepG_bindRet_foreign (Ne.symm hi) (hproc i))
      have hxj := PMF.pure_injective (stepG_bindRet_own (hproc j))
      subst hb
      rw [procFun_update hxj hfor]
      exact IdealSubStep.bindRet _ q j U hval hret
  · by_cases hlτ : l = Sum.inl Lab.tau
    · subst hlτ
      refine ⟨Lab.tau, rfl, ?_⟩
      rcases preAt_tau_inv hIn hBind hlab with ⟨v, rfl, hn⟩ | ⟨k, c, rfl, hs⟩ | ⟨q, d, rfl, hs⟩
      · obtain ⟨jj, m, hF, hv⟩ := netStep_tau hn
        have hv' : v = { w with net := w.net.post jj m } := PMF.pure_injective hv
        subst hv'
        rw [sub_post]
        exact IdealSubStep.byz _ jj m hF
      · obtain ⟨v, hval, hm, hc⟩ := specStep_tau (liftedSpec_step_row rfl hs)
        have hc' : c = { a k with val := some v } := PMF.pure_injective hc
        subst hc'
        rw [sub_setBrbIn]
        exact IdealSubStep.commitIn _ k v hval hm
      · obtain ⟨U, hval, hm, hd⟩ := specStep_tau (liftedSpec_step_row rfl hs)
        have hd' : d = { b q with val := some U } := PMF.pure_injective hd
        subst hd'
        rw [sub_setBrbBind]
        exact IdealSubStep.commitBind _ q U hval hm
    · obtain ⟨x, w', a', b', rfl, hproc, hnet, hin, hbind⟩ :=
        preAt_joint_inv hIn hBind (by simpa using hlτ) hlab
      cases l with
      | inl l₀ =>
        cases l₀ with
        | tau => exact absurd rfl hlτ
        | call id y =>
          have hw : w' = w := PMF.pure_injective (netStep_call hnet)
          have hb : b' = b := funext fun q => lift_step_none rfl (hbind q)
          subst hw; subst hb
          obtain ⟨hinp, hxj⟩ := stepG_call_own (hproc id)
          have hfor : ∀ i, i ≠ id → x i = u i :=
            fun i hi => PMF.pure_injective (stepG_call_foreign (Ne.symm hi) (hproc i))
          have haf : ∀ k, k ≠ id → a' k = a k :=
            fun k hk => lift_step_none (by simp [hk]) (hin k)
          refine ⟨Lab.call id y, rfl, ?_⟩
          rcases specStep_call (liftSpec_row (lb := Sum.inl (BRB.Lab.call y)) (by simp) rfl
              (hin id)) with ⟨hbin, haq⟩ | haq
          · have ha : a' = Function.update a id { a id with input := some y } :=
              funPin (PMF.pure_injective haq) haf
            subst ha
            rw [procFun_update (PMF.pure_injective hxj) hfor]
            exact IdealSubStep.call _ id y hinp hbin
          · have ha : a' = a := funext fun k => by
              by_cases hk : k = id
              · subst hk; exact PMF.pure_injective haq
              · exact haf k hk
            subst ha
            rw [sub_setProc (PMF.pure_injective hxj) hfor]
            exact IdealSubStep.callSpecLoop _ id y hinp
        | ret id g C =>
          obtain ⟨hC, hw⟩ := netStep_ret hnet
          subst hC
          have hw' : w' = { w with core := some (w.core.getD (coreOfNet P w.net)) } :=
            PMF.pure_injective hw
          have ha : a' = a := funext fun k => lift_step_none rfl (hin k)
          have hb : b' = b := funext fun q => lift_step_none rfl (hbind q)
          subst hw'; subst ha; subst hb
          obtain ⟨hinp, hsub, hQ, hr, hxj⟩ := stepG_ret_own (hproc id)
          have hfor : ∀ i, i ≠ id → x i = u i :=
            fun i hi => PMF.pure_injective (stepG_ret_foreign (Ne.symm hi) (hproc i))
          refine ⟨_, rfl, ?_⟩
          rw [sub_ret (PMF.pure_injective hxj) hfor]
          exact IdealSubStep.ret _ id g hinp hsub hQ hr
        | fail id =>
          have hw : w' = { w with net := w.net.corrupt P id } :=
            PMF.pure_injective (netStep_fail hnet)
          have hxall : ∀ i, x i = u i := fun i => PMF.pure_injective (stepG_fail (hproc i))
          have ha : ∀ k, a' k = (a k).corrupt P id := fun k =>
            PMF.pure_injective (specStep_fail
              (liftSpec_row (lb := Sum.inl (BRB.Lab.fail id)) (by simp) rfl (hin k)))
          have hb : ∀ q, b' q = (b q).corrupt P id := fun q =>
            PMF.pure_injective (specStep_fail
              (liftSpec_row (lb := Sum.inl (BRB.Lab.fail id)) (by simp) rfl (hbind q)))
          subst hw
          refine ⟨_, rfl, ?_⟩
          rw [funext ha, funext hb, sub_corrupt hxall]
          exact IdealSubStep.fail _ id
      | inr ev =>
        cases ev with
        | callLoop id y =>
          have hw : w' = w := PMF.pure_injective (netStep_callLoop hnet)
          have hb : b' = b := funext fun q => lift_step_none rfl (hbind q)
          subst hw; subst hb
          have hxall : ∀ i, x i = u i := fun i => PMF.pure_injective (stepG_callLoop (hproc i))
          have haf : ∀ k, k ≠ id → a' k = a k :=
            fun k hk => lift_step_none (by simp [hk]) (hin k)
          refine ⟨Lab.call id y, rfl, ?_⟩
          rcases specStep_call (liftSpec_row (lb := Sum.inr (BRB.Extra.callLoop y)) (by simp) rfl
              (hin id)) with ⟨hbin, haq⟩ | haq
          · have ha : a' = Function.update a id { a id with input := some y } :=
              funPin (PMF.pure_injective haq) haf
            subst ha
            rw [sub_idle hxall, sub_setBrbIn]
            exact IdealSubStep.callProcLoop _ id y hbin
          · have ha : a' = a := funext fun k => by
              by_cases hk : k = id
              · subst hk; exact PMF.pure_injective haq
              · exact haf k hk
            subst ha
            rw [sub_idle hxall]
            exact IdealSubStep.callLoop _ id y

/-- **The embedding.** -/
theorem row_idealSub_step (P : Params) :
    ∀ (s : IdealSubState P.n X) (l₀ : Lab P.n X) (μ : PMF (IdealSubState P.n X)),
      IdealSubStep P s l₀ μ →
      ∃ l, specPull P.n X l = some l₀ ∧ (idealSub P X).step s l μ := by
  rintro ⟨⟨u, w⟩, a, b⟩ l₀ μ hrow
  cases hrow with
  | call id x h hb =>
    exact ⟨Sum.inl (.call id x), rfl, subAt_lab_step (by simp)
      (procStep_update (ProcStep.call (u id) x h)
        (fun i hi => ProcStep.callIdle (u i) id x (Ne.symm hi)))
      (NetStep.call w id x)
      (lift_update (by simp) (fun k hk => by simp [hk])
        (row_liftedSpec_step (l := Sum.inl (BRB.Lab.call x)) rfl (BRB.Step.call (a id) x hb)))
      (fun q => lift_idle rfl)⟩
  | callSpecLoop id x h =>
    refine ⟨Sum.inl (.call id x), rfl, subAt_lab_step (a' := a) (b' := b) (by simp)
      (procStep_update (ProcStep.call (u id) x h)
        (fun i hi => ProcStep.callIdle (u i) id x (Ne.symm hi)))
      (NetStep.call w id x) (fun k => ?_) (fun q => lift_idle rfl)⟩
    by_cases hk : k = id
    · subst hk
      exact row_lift_step (by simp)
        (row_liftedSpec_step (l := Sum.inl (BRB.Lab.call x)) rfl (BRB.Step.callLoop (a k) x))
    · exact lift_idle (by simp [hk])
  | callProcLoop id x hb =>
    refine ⟨Sum.inr (.callLoop id x), rfl,
      subAt_lab_step (x := u) (w' := w) (b' := b) (by simp) (fun i => ?_)
        (NetStep.callLoop w id x)
        (lift_update (by simp) (fun k hk => by simp [hk])
          (row_liftedSpec_step (l := Sum.inr (BRB.Extra.callLoop x)) rfl
            (BRB.Step.call (a id) x hb)))
        (fun q => lift_idle rfl)⟩
    by_cases hi : i = id
    · subst hi; exact ProcStep.callLoop (u i) x
    · exact ProcStep.callLoopIdle (u i) id x (Ne.symm hi)
  | callLoop id x =>
    refine ⟨Sum.inr (.callLoop id x), rfl,
      subAt_lab_step (x := u) (w' := w) (a' := a) (b' := b) (by simp) (fun i => ?_)
        (NetStep.callLoop w id x) (fun k => ?_) (fun q => lift_idle rfl)⟩
    · by_cases hi : i = id
      · subst hi; exact ProcStep.callLoop (u i) x
      · exact ProcStep.callLoopIdle (u i) id x (Ne.symm hi)
    · by_cases hk : k = id
      · subst hk
        exact row_lift_step (by simp)
          (row_liftedSpec_step (l := Sum.inr (BRB.Extra.callLoop x)) rfl
            (BRB.Step.callLoop (a k) x))
      · exact lift_idle (by simp [hk])
  | commitIn k v hv hm =>
    exact ⟨Sum.inl Lab.tau, rfl, subAt_tau_in
      (row_liftedSpec_step (l := (Silent.τ : BRB.SubLab P.n X)) rfl
        (BRB.Step.commit (a k) v hv hm))⟩
  | commitBind q U hv hm =>
    exact ⟨Sum.inl Lab.tau, rfl, subAt_tau_bind
      (row_liftedSpec_step (l := (Silent.τ : BRB.SubLab P.n (APSet P.n X))) rfl
        (BRB.Step.commit (b q) U hv hm))⟩
  | deliver i j m h =>
    exact ⟨Sum.inl Lab.tau, rfl, subAt_event_step (a' := a) (b' := b) (GaEvt.dlv i j m)
      (procStep_update (ProcStep.dlvRecv (u i) j m)
        (fun i' hi' => ProcStep.dlvIdle (u i') i j m (Ne.symm hi')))
      (NetStep.dlv w i j m h) (fun k => lift_idle rfl) (fun q => lift_idle rfl)⟩
  | echo j A hin happ hcard hsend =>
    exact ⟨Sum.inl Lab.tau, rfl, subAt_event_step (a' := a) (b' := b) (GaEvt.snd j (.echo A))
      (procStep_update (ProcStep.sndEcho (u j) A hin happ hcard hsend)
        (fun i hi => ProcStep.sndIdle (u i) j (.echo A) (Ne.symm hi)))
      (NetStep.snd w j (.echo A)) (fun k => lift_idle rfl) (fun q => lift_idle rfl)⟩
  | vote j U hin happ hQ hsend =>
    exact ⟨Sum.inl Lab.tau, rfl, subAt_event_step (a' := a) (b' := b) (GaEvt.snd j (.vote U))
      (procStep_update (ProcStep.sndVote (u j) U hin happ hQ hsend)
        (fun i hi => ProcStep.sndIdle (u i) j (.vote U) (Ne.symm hi)))
      (NetStep.snd w j (.vote U)) (fun k => lift_idle rfl) (fun q => lift_idle rfl)⟩
  | bindCall j U hin happ hQ hb =>
    refine ⟨Sum.inl Lab.tau, rfl,
      subAt_event_step (x := u) (w' := w) (a' := a) (GaEvt.bindCall j U) (fun i => ?_)
        (NetStep.bindCallIdle w j U) (fun k => lift_idle rfl)
        (lift_update (by simp) (fun q hq => by simp [hq])
          (row_liftedSpec_step (l := Sum.inl (BRB.Lab.call U)) rfl
            (BRB.Step.call (b j) U hb)))⟩
    by_cases hi : i = j
    · subst hi; exact ProcStep.bindCall (u i) U hin happ hQ
    · exact ProcStep.bindCallIdle (u i) j U (Ne.symm hi)
  | bindCallSpecLoop j U hin happ hQ =>
    refine ⟨Sum.inl Lab.tau, rfl,
      subAt_event_step (x := u) (w' := w) (a' := a) (b' := b) (GaEvt.bindCall j U)
        (fun i => ?_) (NetStep.bindCallIdle w j U) (fun k => lift_idle rfl) (fun q => ?_)⟩
    · by_cases hi : i = j
      · subst hi; exact ProcStep.bindCall (u i) U hin happ hQ
      · exact ProcStep.bindCallIdle (u i) j U (Ne.symm hi)
    · by_cases hq : q = j
      · subst hq
        exact row_lift_step (by simp)
          (row_liftedSpec_step (l := Sum.inl (BRB.Lab.call U)) rfl (BRB.Step.callLoop (b q) U))
      · exact lift_idle (by simp [hq])
  | byz j m h =>
    exact ⟨Sum.inl Lab.tau, rfl, subAt_tau_net (NetStep.byz w j m h)⟩
  | inRet k j v hv hr =>
    exact ⟨Sum.inl Lab.tau, rfl, subAt_event_step (w' := w) (b' := b) (GaEvt.inRet k j v)
      (procStep_update (ProcStep.inRetRecv (u j) k v)
        (fun i hi => ProcStep.inRetIdle (u i) k j v (Ne.symm hi)))
      (NetStep.inRetIdle w k j v)
      (lift_update (by simp) (fun k' hk' => by simp [hk'])
        (row_liftedSpec_step (l := Sum.inl (BRB.Lab.ret j v)) rfl
          (BRB.Step.ret (a k) j v hv hr)))
      (fun q => lift_idle rfl)⟩
  | bindRet q j U hv hr =>
    exact ⟨Sum.inl Lab.tau, rfl, subAt_event_step (w' := w) (a' := a) (GaEvt.bindRet q j U)
      (procStep_update (ProcStep.bindRetRecv (u j) q U)
        (fun i hi => ProcStep.bindRetIdle (u i) q j U (Ne.symm hi)))
      (NetStep.bindRetIdle w q j U) (fun k => lift_idle rfl)
      (lift_update (by simp) (fun q' hq' => by simp [hq'])
        (row_liftedSpec_step (l := Sum.inl (BRB.Lab.ret j U)) rfl
          (BRB.Step.ret (b q) j U hv hr)))⟩
  | ret id g hin hsub hQ hr =>
    exact ⟨Sum.inl (.ret id g (w.core.getD (coreOfNet P w.net))), rfl,
      subAt_lab_step (a' := a) (b' := b) (by simp)
        (procStep_update (ProcStep.ret (u id) g _ hin hsub hQ hr)
          (fun i hi => ProcStep.retIdle (u i) id g _ (Ne.symm hi)))
        (NetStep.ret w id g) (fun k => lift_idle rfl) (fun q => lift_idle rfl)⟩
  | fail id =>
    exact ⟨Sum.inl (.fail id), rfl, subAt_lab_step (x := u) (by simp)
      (fun i => ProcStep.failIdle (u i) id) (NetStep.fail w id)
      (lift_all (l₀ := fun _ => Sum.inl (BRB.Lab.fail id)) (fun k => rfl)
        (fun k => row_liftedSpec_step (l := Sum.inl (BRB.Lab.fail id)) rfl
          (BRB.Step.fail (a k) id)))
      (lift_all (l₀ := fun _ => Sum.inl (BRB.Lab.fail id)) (fun q => rfl)
        (fun q => row_liftedSpec_step (l := Sum.inl (BRB.Lab.fail id)) rfl
          (BRB.Step.fail (b q) id)))⟩

/-- **The row characterisation.** At a specification label `l₀`, the
transitions of the instance over the labels `specPull` sends to `l₀` are exactly
the `l₀`-rows of `IdealSubStep`, on the same state and with the same
distribution. -/
theorem idealSub_step_iff_row (P : Params) (s : IdealSubState P.n X) (l₀ : Lab P.n X)
    (μ : PMF (IdealSubState P.n X)) :
    (∃ l, specPull P.n X l = some l₀ ∧ (idealSub P X).step s l μ) ↔ IdealSubStep P s l₀ μ := by
  constructor
  · rintro ⟨l, hl, hstep⟩
    obtain ⟨l₁, hl₁, hrow⟩ := idealSub_step_row P s l μ hstep
    have hll : l₁ = l₀ := Option.some.inj (show (some l₁ : Option (Lab P.n X)) = some l₀ by
      rw [← hl₁, hl])
    subst hll
    exact hrow
  · exact row_idealSub_step P s l₀ μ

/-- info: 'PLTS.ABA.Gather.idealSub_step_iff_row' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms idealSub_step_iff_row

end Gather
end ABA
end PLTS
