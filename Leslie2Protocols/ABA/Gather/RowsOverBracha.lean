/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sathiya / Claude
-/

import Leslie2Protocols.ABA.Gather.Composition

/-!
# The rows of the gather instance over Bracha's broadcast

`LowStep` is the rule table of `Gather.lowInst` (`ABA/Gather/Composition.lean`) — the
`n` gather programs beside the gather network, in parallel with `2n` composed
reliable-broadcast instances — stated over the composition's state through the
four views `ga`, `brbIn`, `brbBind`, `core`. It is a relation on that state; the
system is the composition.

`lowInst_step_iff_row` is the row characterisation: at a specification label
`l₀`, the transitions of the composition over the labels `specPull` sends to
`l₀` are exactly the `l₀`-rows of `LowStep`, on the same state and with the
same distribution.

## The broadcast tier

A broadcast instance's own rows are `BRB.ImplStep`
(`ABA/ReliableBroadcast/BrachaImplementation.lean`), and `BRB.implInst_step_iff_row` matches them
against the instance's transitions. Each label of the composition reaches an instance at one label
of its interface alphabet, and the rows there carry over: a silent step, a return and a
corruption are the hypotheses `BRB.ImplStep P k (brbIn s k) l₀ (PMF.pure c)` of
the rows `brbInTau`, `inRet` and `fail`.

The call is the exception. `BRB.ImplStep` answers `call x` on two rows, the
broadcast of `⟨INIT, x⟩` and the input-enabledness loop, and the two sit at the
two labels of the instance's interface — the broadcast under `call x`, the loop
under `Extra.callLoop x`. The composition puts the gather call over the first
and the gather call loop over the second, so the gather call carries the
broadcast and the gather call loop moves nothing. The rows `call` and
`callLoop` state that directly, as does `bindCall`.
-/

namespace PLTS
namespace ABA
namespace Gather

variable {X : Type} [DecidableEq X]

/-! ### Reading a composed broadcast instance -/

omit [DecidableEq X] in
/-- A transition of a composed broadcast instance is a `BRB.ImplStep` row at the
label `BRB.specPull` projects to. -/
theorem implInst_step_at {M : Type} [DecidableEq M] {P : Params} {ldr : Fin P.n}
    {s s' : BRB.ImplState P.n M} {l : BRB.InstLab P.n M} {l₀ : BRB.Lab P.n M}
    (hl : BRB.specPull P.n M l = some l₀)
    (h : (BRB.implInst P ldr M).step s l (PMF.pure s')) : BRB.ImplStep P ldr s l₀ (PMF.pure s') := by
  obtain ⟨l₁, hl₁, hrow⟩ := BRB.implInst_step_row P ldr s l _ h
  rwa [Option.some.inj (hl₁.symm.trans hl)] at hrow

omit [DecidableEq X] in
/-- A `BRB.ImplStep` row at a label other than a call is a transition of the
instance at the interface label over it. -/
theorem row_implInst_step_inl {M : Type} [DecidableEq M] {P : Params} {ldr : Fin P.n}
    {s s' : BRB.ImplState P.n M} {l₀ : BRB.Lab P.n M} (h0 : ∀ m : M, l₀ ≠ BRB.Lab.call m)
    (h : BRB.ImplStep P ldr s l₀ (PMF.pure s')) :
    (BRB.implInst P ldr M).step s (Sum.inl l₀) (PMF.pure s') := by
  obtain ⟨l, hl, hstep⟩ := BRB.row_implInst_step P ldr s l₀ _ h
  cases l with
  | inl y => rwa [Option.some.inj hl] at hstep
  | inr e => cases e with
    | callLoop m => exact absurd (Option.some.inj hl).symm (h0 m)

omit [DecidableEq X] in
/-- The one corruption row. -/
theorem implStep_fail {M : Type} [DecidableEq M] {P : Params} {ldr : Fin P.n}
    {s : BRB.ImplState P.n M} {id : Fin P.n} {μ : PMF (BRB.ImplState P.n M)}
    (h : BRB.ImplStep P ldr s (.fail id) μ) : μ = PMF.pure (s.corrupt P id) := by
  cases h; rfl

omit [DecidableEq X] in
/-- At the call label the instance broadcasts: the leader records the payload
and the network records `⟨INIT, m⟩`. -/
theorem implInst_call_row {M : Type} [DecidableEq M] {P : Params} {ldr : Fin P.n}
    {s s' : BRB.ImplState P.n M} {m : M}
    (h : (BRB.implInst P ldr M).step s (Sum.inl (BRB.Lab.call m)) (PMF.pure s')) :
    (s.proc ldr).input = none ∧
      s' = (s.setProc ldr { s.proc ldr with input := some m }).mcast ldr (.init m) := by
  obtain ⟨u, w⟩ := s
  rcases (BRB.implInst_step_iff P ldr (u, w) (Sum.inl (BRB.Lab.call m)) _).mp h with ⟨hτ, -⟩ | hlab
  · exact absurd hτ (by simp)
  · obtain ⟨x, w', hμ, hall, hn⟩ := BRB.implPre_joint_inv (by simp) hlab
    obtain ⟨hinp, hx⟩ := BRB.stepB_call_leader (hall ldr)
    have hfor : ∀ i, i ≠ ldr → x i = u i :=
      fun i hi => PMF.pure_injective (BRB.stepB_call_foreign hi (hall i))
    have hw : w' = w.post ldr (.init m) := PMF.pure_injective (BRB.netStep_call hn)
    subst hw
    refine ⟨hinp, ?_⟩
    rw [PMF.pure_injective hμ, BRB.implInst_setProc_post (PMF.pure_injective hx) hfor]
    rfl

omit [DecidableEq X] in
/-- At the call-loop label the instance stands still. -/
theorem implInst_callLoop_row {M : Type} [DecidableEq M] {P : Params} {ldr : Fin P.n}
    {s s' : BRB.ImplState P.n M} {m : M}
    (h : (BRB.implInst P ldr M).step s (Sum.inr (BRB.Extra.callLoop m)) (PMF.pure s')) : s' = s := by
  obtain ⟨u, w⟩ := s
  rcases (BRB.implInst_step_iff P ldr (u, w) (Sum.inr (BRB.Extra.callLoop m)) _).mp h with
    ⟨hτ, -⟩ | hlab
  · exact absurd hτ (by simp)
  · obtain ⟨x, w', hμ, hall, hn⟩ := BRB.implPre_joint_inv (by simp) hlab
    have hw : w' = w := PMF.pure_injective (BRB.netStep_callLoop hn)
    subst hw
    have hidle : ∀ i, x i = u i := fun i => PMF.pure_injective (BRB.stepB_callLoop (hall i))
    rw [PMF.pure_injective hμ, BRB.implInst_idle hidle]

omit [DecidableEq X] in
/-- Build the instance's broadcast at the call label. -/
theorem row_implInst_call_step {M : Type} [DecidableEq M] (P : Params) (ldr : Fin P.n)
    (s : BRB.ImplState P.n M) (m : M) (h : (s.proc ldr).input = none) :
    (BRB.implInst P ldr M).step s (Sum.inl (BRB.Lab.call m))
      (PMF.pure ((s.setProc ldr { s.proc ldr with input := some m }).mcast ldr (.init m))) := by
  obtain ⟨u, w⟩ := s
  exact BRB.implInst_lab_step P ldr (by simp)
    (BRB.procStep_update (BRB.ProcStep.call (u ldr) m rfl h)
      (fun i hi => BRB.ProcStep.callIdle (u i) m hi))
    (BRB.NetStep.call w m)

omit [DecidableEq X] in
/-- Build the instance's stutter at the call-loop label. -/
theorem row_implInst_callLoop_step {M : Type} [DecidableEq M] (P : Params) (ldr : Fin P.n)
    (s : BRB.ImplState P.n M) (m : M) :
    (BRB.implInst P ldr M).step s (Sum.inr (BRB.Extra.callLoop m)) (PMF.pure s) := by
  obtain ⟨u, w⟩ := s
  exact BRB.implInst_lab_step P ldr (by simp) (fun i => BRB.ProcStep.callLoop (u i) m)
    (BRB.NetStep.callLoop w m)

/-! ### The rows -/

/-- The rows of the gather instance over Bracha's broadcast (`Gather.lowInst`),
stated over the composition's state: one constructor per case of
`Gather.lowInst_step_iff_row`. All transitions are Dirac. -/
inductive LowStep (P : Params) :
    LowState P.n X → Lab P.n X → PMF (LowState P.n X) → Prop
  /-- The call arrives: the gather record records the payload and the input
  instance broadcasts it. -/
  | call (s : LowState P.n X) (id : Fin P.n) (x : X)
      (h : ((ga s).proc id).input = none) (hb : ((brbIn s id).proc id).input = none) :
      LowStep P s (.call id x)
        (PMF.pure (setBrbIn (setGa s ((ga s).setProc id { (ga s).proc id with input := some x }))
          (Function.update (brbIn s) id
            (((brbIn s id).setProc id
              { (brbIn s id).proc id with input := some x }).mcast id (.init x)))))
  /-- Input-enabledness loop for `call`: nothing moves. -/
  | callLoop (s : LowState P.n X) (id : Fin P.n) (x : X) :
      LowStep P s (.call id x) (PMF.pure s)
  /-- A silent step of one input instance. -/
  | brbInTau (s : LowState P.n X) (k : Fin P.n) (c : BRB.ImplState P.n X)
      (hb : BRB.ImplStep P k (brbIn s k) .tau (PMF.pure c)) :
      LowStep P s .tau (PMF.pure (setBrbIn s (Function.update (brbIn s) k c)))
  /-- A silent step of one bind instance. -/
  | brbBindTau (s : LowState P.n X) (q : Fin P.n) (d : BRB.ImplState P.n (APSet P.n X))
      (hb : BRB.ImplStep P q (brbBind s q) .tau (PMF.pure d)) :
      LowStep P s .tau (PMF.pure (setBrbBind s (Function.update (brbBind s) q d)))
  /-- Asynchronous delivery on the gather network. -/
  | deliver (s : LowState P.n X) (i j : Fin P.n) (m : GaMsg P.n X)
      (h : m ∈ (ga s).sent j) :
      LowStep P s .tau (PMF.pure (setGa s ((ga s).recvMsg i j m)))
  /-- `ECHO`: the process is called and its accepted pairs number at least
  `n − f`, the source blueprint's `|AP| ≥ n − f`. The payload is those pairs,
  `T_i ← AP_i` of AFW25's Algorithm 5, line 9. -/
  | echo (s : LowState P.n X) (j : Fin P.n)
      (hin : ((ga s).proc j).input ≠ none)
      (hcard : P.n - P.f ≤ ((ga s).proc j).accepted.card)
      (hsend : ((ga s).proc j).sentEcho = none) :
      LowStep P s .tau
        (PMF.pure (setGa s (((ga s).setProc j
          { (ga s).proc j with sentEcho := some ((ga s).proc j).accepted }).mcast j
            (.echo ((ga s).proc j).accepted))))
  /-- `VOTE`: `n − f` senders' approved `ECHO` payloads, each contained in the
  vote payload, are delivered here, and the process has multicast its own
  `ECHO`. The main thread of AFW25's Algorithm 5 sends `ECHO` before `VOTE`. -/
  | vote (s : LowState P.n X) (j : Fin P.n) (U : APSet P.n X)
      (hin : ((ga s).proc j).input ≠ none)
      (hech : ((ga s).proc j).sentEcho ≠ none)
      (happ : approvedBy ((ga s).proc j) U)
      (hQ : ∃ Q : Finset (Fin P.n), P.n - P.f ≤ Q.card ∧
        ∀ q ∈ Q, ∃ A, GaMsg.echo A ∈ (ga s).recv j q ∧ approvedBy ((ga s).proc j) A ∧ A ⊆ U)
      (hsend : ((ga s).proc j).sentVote = none) :
      LowStep P s .tau
        (PMF.pure (setGa s (((ga s).setProc j
          { (ga s).proc j with sentVote := some U }).mcast j (.vote U))))
  /-- `BIND`: `n − f` senders' approved `VOTE` payloads, each contained in the
  bind payload, are delivered here, and the bind instance broadcasts the payload.
  The process has multicast its own `VOTE` and has not called its own bind
  broadcast. The main thread of AFW25's Algorithm 5 sends `VOTE` before `BIND`,
  and sends `BIND` once, at line 17. The payload handed to the broadcast is
  written to the gather record. -/
  | bindCall (s : LowState P.n X) (j : Fin P.n) (U : APSet P.n X)
      (hin : ((ga s).proc j).input ≠ none)
      (hvot : ((ga s).proc j).sentVote ≠ none)
      (hsnd : ((ga s).proc j).sentBind = none)
      (happ : approvedBy ((ga s).proc j) U)
      (hQ : ∃ Q : Finset (Fin P.n), P.n - P.f ≤ Q.card ∧
        ∀ q ∈ Q, ∃ W, GaMsg.vote W ∈ (ga s).recv j q ∧ approvedBy ((ga s).proc j) W ∧ W ⊆ U)
      (hbc : ((brbBind s j).proc j).input = none) :
      LowStep P s .tau
        (PMF.pure (setBrbBind (setGa s ((ga s).setProc j
            { (ga s).proc j with sentBind := some U }))
          (Function.update (brbBind s) j
            (((brbBind s j).setProc j
              { (brbBind s j).proc j with input := some U }).mcast j (.init U)))))
  /-- Byzantine injection on the gather network. -/
  | byz (s : LowState P.n X) (j : Fin P.n) (m : GaMsg P.n X) (h : j ∈ (ga s).F) :
      LowStep P s .tau (PMF.pure (setGa s ((ga s).mcast j m)))
  /-- An input instance returns to `j`, which files the value in its store. -/
  | inRet (s : LowState P.n X) (k j : Fin P.n) (v : X) (c : BRB.ImplState P.n X)
      (hb : BRB.ImplStep P k (brbIn s k) (.ret j v) (PMF.pure c)) :
      LowStep P s .tau
        (PMF.pure (setBrbIn (setGa s ((ga s).setProc j
            { (ga s).proc j with
              delivIn := Function.update ((ga s).proc j).delivIn k (some v) }))
          (Function.update (brbIn s) k c)))
  /-- A bind instance returns to `j`, which files the payload in its store. -/
  | bindRet (s : LowState P.n X) (q j : Fin P.n) (U : APSet P.n X)
      (d : BRB.ImplState P.n (APSet P.n X))
      (hb : BRB.ImplStep P q (brbBind s q) (.ret j U) (PMF.pure d)) :
      LowStep P s .tau
        (PMF.pure (setBrbBind (setGa s ((ga s).setProc j
            { (ga s).proc j with
              delivBind := Function.update ((ga s).proc j).delivBind q (some U) }))
          (Function.update (brbBind s) q d)))
  /-- Return: the output's entries are held here, `n − f` bind payloads held
  here are sub-maps of it, and the returner has called its own bind broadcast.
  The `BIND` broadcast of AFW25's Algorithm 5, line 17, precedes the wait of line
  18. The label carries the instance's core, which this row writes if it is
  unwritten. -/
  | ret (s : LowState P.n X) (id : Fin P.n) (g : Fin P.n → Option X)
      (hin : ((ga s).proc id).input ≠ none)
      (hbind : ((ga s).proc id).sentBind ≠ none)
      (hsub : ∀ k x, g k = some x → holdsIn ((ga s).proc id) k x)
      (hQ : ∃ Q : Finset (Fin P.n), P.n - P.f ≤ Q.card ∧
        ∀ q ∈ Q, ∃ U, holdsBind ((ga s).proc id) q U ∧ APSet.subMap U g)
      (hr : ((ga s).proc id).returned = false) :
      LowStep P s (.ret id g ((core s).getD (coreOfNet P (ga s).2)))
        (PMF.pure (setCore (setGa s ((ga s).setProc id
          { (ga s).proc id with returned := true }))
          (some ((core s).getD (coreOfNet P (ga s).2)))))
  /-- Corruption (deviation D1), in lockstep across the gather network state and
  every broadcast coordinate. -/
  | fail (s : LowState P.n X) (id : Fin P.n) :
      LowStep P s (.fail id)
        (PMF.pure (corruptAll P id (SubState.corrupt P id) (SubState.corrupt P id) s))

/-! ### The row characterisation -/

/-- **The projection.** -/
theorem lowInst_step_row (P : Params) :
    ∀ (s : LowState P.n X) (l : InstLab P.n X) (μ : PMF (LowState P.n X)),
      (lowInst P X).step s l μ →
      ∃ l₀, specPull P.n X l = some l₀ ∧ LowStep P s l₀ μ := by
  have hIn : ∀ k : Fin P.n, (BRB.implInst P k X).IsLTS := fun k => BRB.implInst_isLTS P k
  have hBind : ∀ q : Fin P.n, (BRB.implInst P q (APSet P.n X)).IsLTS := fun q => BRB.implInst_isLTS P q
  rintro ⟨⟨u, w⟩, a, b⟩ l μ hstep
  rcases (instAt_step_iff P X (fun k => BRB.implInst P k X)
      (fun q => BRB.implInst P q (APSet P.n X)) _ l μ).mp hstep with ⟨rfl, e, hev⟩ | hlab
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
        obtain ⟨rfl, hinp, hcard, hsend, hx⟩ := stepG_snd_echo_own (hproc j)
        rw [sub_setProc_post (PMF.pure_injective hx) hfor]
        exact LowStep.echo _ j hinp hcard hsend
      | vote U =>
        obtain ⟨hinp, hech, happ, hQ, hsend, hx⟩ := stepG_snd_vote_own (hproc j)
        rw [sub_setProc_post (PMF.pure_injective hx) hfor]
        exact LowStep.vote _ j U hinp hech happ hQ hsend
    | dlv i j m =>
      obtain ⟨hmem, hw⟩ := netStep_dlv hnet
      have hw' : w' = w := PMF.pure_injective hw
      have ha : a' = a := funext fun k => lift_step_none rfl (hin k)
      have hb : b' = b := funext fun q => lift_step_none rfl (hbind q)
      subst hw'; subst ha; subst hb
      have hfor : ∀ i', i' ≠ i → x i' = u i' :=
        fun i' hi' => PMF.pure_injective (stepG_dlv_foreign (Ne.symm hi') (hproc i'))
      rw [sub_deliver (PMF.pure_injective (stepG_dlv_own (hproc i))) hfor]
      exact LowStep.deliver _ i j m hmem
    | inRet k j v =>
      have hw : w' = w := PMF.pure_injective (netStep_inRet hnet)
      have hb : b' = b := funext fun q => lift_step_none rfl (hbind q)
      subst hw; subst hb
      have himpl : BRB.ImplStep P k (a k) (.ret j v) (PMF.pure (a' k)) :=
        implInst_step_at (l := Sum.inl (BRB.Lab.ret j v)) rfl
          (lift_step_some (l₀ := Sum.inl (BRB.Lab.ret j v)) (by simp) (hin k))
      have haf : ∀ k', k' ≠ k → a' k' = a k' :=
        fun k' hk' => lift_step_none (by simp [hk']) (hin k')
      have ha : a' = Function.update a k (a' k) := funPin rfl haf
      have hfor : ∀ i, i ≠ j → x i = u i :=
        fun i hi => PMF.pure_injective (stepG_inRet_foreign (Ne.symm hi) (hproc i))
      have hxj := PMF.pure_injective (stepG_inRet_own (hproc j))
      rw [procFun_update hxj hfor, ha]
      exact LowStep.inRet _ k j v (a' k) himpl
    | bindCall j U =>
      have hw : w' = w := PMF.pure_injective (netStep_bindCall hnet)
      have ha : a' = a := funext fun k => lift_step_none rfl (hin k)
      subst hw; subst ha
      obtain ⟨hinp, hvot, hsnd, happ, hQ, hxj⟩ := stepG_bindCall_own (hproc j)
      have hfor : ∀ i, i ≠ j → x i = u i :=
        fun i hi => PMF.pure_injective (stepG_bindCall_foreign (Ne.symm hi) (hproc i))
      obtain ⟨hbc, hbj⟩ := implInst_call_row
        (lift_step_some (l₀ := Sum.inl (BRB.Lab.call U)) (by simp) (hbind j))
      have hbf : ∀ q, q ≠ j → b' q = b q :=
        fun q hq => lift_step_none (by simp [hq]) (hbind q)
      have hb : b' = Function.update b j
          (((b j).setProc j { (b j).proc j with input := some U }).mcast j (.init U)) :=
        funPin hbj hbf
      subst hb
      rw [procFun_update (PMF.pure_injective hxj) hfor]
      exact LowStep.bindCall _ j U hinp hvot hsnd happ hQ hbc
    | bindRet q j U =>
      have hw : w' = w := PMF.pure_injective (netStep_bindRet hnet)
      have ha : a' = a := funext fun k => lift_step_none rfl (hin k)
      subst hw; subst ha
      have himpl : BRB.ImplStep P q (b q) (.ret j U) (PMF.pure (b' q)) :=
        implInst_step_at (l := Sum.inl (BRB.Lab.ret j U)) rfl
          (lift_step_some (l₀ := Sum.inl (BRB.Lab.ret j U)) (by simp) (hbind q))
      have hbf : ∀ q', q' ≠ q → b' q' = b q' :=
        fun q' hq' => lift_step_none (by simp [hq']) (hbind q')
      have hb : b' = Function.update b q (b' q) := funPin rfl hbf
      have hfor : ∀ i, i ≠ j → x i = u i :=
        fun i hi => PMF.pure_injective (stepG_bindRet_foreign (Ne.symm hi) (hproc i))
      have hxj := PMF.pure_injective (stepG_bindRet_own (hproc j))
      rw [procFun_update hxj hfor, hb]
      exact LowStep.bindRet _ q j U (b' q) himpl
  · by_cases hlτ : l = Sum.inl Lab.tau
    · subst hlτ
      refine ⟨Lab.tau, rfl, ?_⟩
      rcases preAt_tau_inv hIn hBind hlab with ⟨v, rfl, hn⟩ | ⟨k, c, rfl, hs⟩ | ⟨q, d, rfl, hs⟩
      · obtain ⟨jj, m, hF, hv⟩ := netStep_tau hn
        have hv' : v = { w with net := w.net.post jj m } := PMF.pure_injective hv
        subst hv'
        rw [sub_post]
        exact LowStep.byz _ jj m hF
      · have himpl : BRB.ImplStep P k (a k) BRB.Lab.tau (PMF.pure c) :=
          implInst_step_at (l := (Silent.τ : BRB.InstLab P.n X)) rfl hs
        rw [sub_setBrbIn]
        exact LowStep.brbInTau _ k c himpl
      · have himpl : BRB.ImplStep P q (b q) BRB.Lab.tau (PMF.pure d) :=
          implInst_step_at (l := (Silent.τ : BRB.InstLab P.n (APSet P.n X))) rfl hs
        rw [sub_setBrbBind]
        exact LowStep.brbBindTau _ q d himpl
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
          obtain ⟨hbin, haid⟩ := implInst_call_row
            (lift_step_some (l₀ := Sum.inl (BRB.Lab.call y)) (by simp) (hin id))
          have haf : ∀ k, k ≠ id → a' k = a k :=
            fun k hk => lift_step_none (by simp [hk]) (hin k)
          have ha : a' = Function.update a id
              (((a id).setProc id { (a id).proc id with input := some y }).mcast id (.init y)) :=
            funPin haid haf
          subst ha
          refine ⟨Lab.call id y, rfl, ?_⟩
          rw [procFun_update (PMF.pure_injective hxj) hfor]
          exact LowStep.call _ id y hinp hbin
        | ret id g C =>
          obtain ⟨hC, hw⟩ := netStep_ret hnet
          subst hC
          have hw' : w' = { w with core := some (w.core.getD (coreOfNet P w.net)) } :=
            PMF.pure_injective hw
          have ha : a' = a := funext fun k => lift_step_none rfl (hin k)
          have hb : b' = b := funext fun q => lift_step_none rfl (hbind q)
          subst hw'; subst ha; subst hb
          obtain ⟨hinp, hbnd, hsub, hQ, hr, hxj⟩ := stepG_ret_own (hproc id)
          have hfor : ∀ i, i ≠ id → x i = u i :=
            fun i hi => PMF.pure_injective (stepG_ret_foreign (Ne.symm hi) (hproc i))
          refine ⟨_, rfl, ?_⟩
          rw [sub_ret (PMF.pure_injective hxj) hfor]
          exact LowStep.ret _ id g hinp hbnd hsub hQ hr
        | fail id =>
          have hw : w' = { w with net := w.net.corrupt P id } :=
            PMF.pure_injective (netStep_fail hnet)
          have hxall : ∀ i, x i = u i := fun i => PMF.pure_injective (stepG_fail (hproc i))
          have ha : ∀ k, a' k = SubState.corrupt P id (a k) := fun k =>
            PMF.pure_injective (implStep_fail (implInst_step_at (l := Sum.inl (BRB.Lab.fail id)) rfl
              (lift_step_some (l₀ := Sum.inl (BRB.Lab.fail id)) rfl (hin k))))
          have hb : ∀ q, b' q = SubState.corrupt P id (b q) := fun q =>
            PMF.pure_injective (implStep_fail (implInst_step_at (l := Sum.inl (BRB.Lab.fail id)) rfl
              (lift_step_some (l₀ := Sum.inl (BRB.Lab.fail id)) rfl (hbind q))))
          subst hw
          refine ⟨_, rfl, ?_⟩
          rw [funext ha, funext hb, sub_corrupt hxall]
          exact LowStep.fail _ id
      | inr ev =>
        cases ev with
        | callLoop id y =>
          have hw : w' = w := PMF.pure_injective (netStep_callLoop hnet)
          have hb : b' = b := funext fun q => lift_step_none rfl (hbind q)
          subst hw; subst hb
          have hxall : ∀ i, x i = u i := fun i => PMF.pure_injective (stepG_callLoop (hproc i))
          have haid : a' id = a id := implInst_callLoop_row
            (lift_step_some (l₀ := Sum.inr (BRB.Extra.callLoop y)) (by simp) (hin id))
          have haf : ∀ k, k ≠ id → a' k = a k :=
            fun k hk => lift_step_none (by simp [hk]) (hin k)
          have ha : a' = a := funext fun k => by
            by_cases hk : k = id
            · subst hk; exact haid
            · exact haf k hk
          subst ha
          refine ⟨Lab.call id y, rfl, ?_⟩
          rw [sub_idle hxall]
          exact LowStep.callLoop _ id y

/-- **The embedding.** -/
theorem row_lowInst_step (P : Params) :
    ∀ (s : LowState P.n X) (l₀ : Lab P.n X) (μ : PMF (LowState P.n X)),
      LowStep P s l₀ μ →
      ∃ l, specPull P.n X l = some l₀ ∧ (lowInst P X).step s l μ := by
  rintro ⟨⟨u, w⟩, a, b⟩ l₀ μ hrow
  cases hrow with
  | call id x h hb =>
    exact ⟨Sum.inl (.call id x), rfl, instAt_lab_step (b' := b) (by simp)
      (procStep_update (ProcStep.call (u id) x h)
        (fun i hi => ProcStep.callIdle (u i) id x (Ne.symm hi)))
      (NetStep.call w id x)
      (lift_update (by simp) (fun k hk => by simp [hk]) (row_implInst_call_step P id (a id) x hb))
      (fun q => lift_idle rfl)⟩
  | callLoop id x =>
    refine ⟨Sum.inr (.callLoop id x), rfl,
      instAt_lab_step (x := u) (w' := w) (a' := a) (b' := b) (by simp) (fun i => ?_)
        (NetStep.callLoop w id x) (fun k => ?_) (fun q => lift_idle rfl)⟩
    · by_cases hi : i = id
      · subst hi; exact ProcStep.callLoop (u i) x
      · exact ProcStep.callLoopIdle (u i) id x (Ne.symm hi)
    · by_cases hk : k = id
      · subst hk; exact row_lift_step (by simp) (row_implInst_callLoop_step P k (a k) x)
      · exact lift_idle (by simp [hk])
  | brbInTau k c hb =>
    exact ⟨Sum.inl Lab.tau, rfl, instAt_tau_in (row_implInst_step_inl (by simp) hb)⟩
  | brbBindTau q d hb =>
    exact ⟨Sum.inl Lab.tau, rfl, instAt_tau_bind (row_implInst_step_inl (by simp) hb)⟩
  | deliver i j m h =>
    exact ⟨Sum.inl Lab.tau, rfl, instAt_event_step (a' := a) (b' := b) (GaEvt.dlv i j m)
      (procStep_update (ProcStep.dlvRecv (u i) j m)
        (fun i' hi' => ProcStep.dlvIdle (u i') i j m (Ne.symm hi')))
      (NetStep.dlv w i j m h) (fun k => lift_idle rfl) (fun q => lift_idle rfl)⟩
  | echo j hin hcard hsend =>
    exact ⟨Sum.inl Lab.tau, rfl, instAt_event_step (a' := a) (b' := b)
      (GaEvt.snd j (.echo (u j).proc.accepted))
      (procStep_update (ProcStep.sndEcho (u j) hin hcard hsend)
        (fun i hi => ProcStep.sndIdle (u i) j (.echo (u j).proc.accepted) (Ne.symm hi)))
      (NetStep.snd w j (.echo (u j).proc.accepted)) (fun k => lift_idle rfl)
      (fun q => lift_idle rfl)⟩
  | vote j U hin hech happ hQ hsend =>
    exact ⟨Sum.inl Lab.tau, rfl, instAt_event_step (a' := a) (b' := b) (GaEvt.snd j (.vote U))
      (procStep_update (ProcStep.sndVote (u j) U hin hech happ hQ hsend)
        (fun i hi => ProcStep.sndIdle (u i) j (.vote U) (Ne.symm hi)))
      (NetStep.snd w j (.vote U)) (fun k => lift_idle rfl) (fun q => lift_idle rfl)⟩
  | bindCall j U hin hvot hsnd happ hQ hbc =>
    exact ⟨Sum.inl Lab.tau, rfl,
      instAt_event_step (w' := w) (a' := a) (GaEvt.bindCall j U)
        (procStep_update (ProcStep.bindCall (u j) U hin hvot hsnd happ hQ)
          (fun i hi => ProcStep.bindCallIdle (u i) j U (Ne.symm hi)))
        (NetStep.bindCallIdle w j U) (fun k => lift_idle rfl)
        (lift_update (by simp) (fun q hq => by simp [hq])
          (row_implInst_call_step P j (b j) U hbc))⟩
  | byz j m h =>
    exact ⟨Sum.inl Lab.tau, rfl, instAt_tau_net (NetStep.byz w j m h)⟩
  | inRet k j v c hb =>
    exact ⟨Sum.inl Lab.tau, rfl, instAt_event_step (w' := w) (b' := b) (GaEvt.inRet k j v)
      (procStep_update (ProcStep.inRetRecv (u j) k v)
        (fun i hi => ProcStep.inRetIdle (u i) k j v (Ne.symm hi)))
      (NetStep.inRetIdle w k j v)
      (lift_update (by simp) (fun k' hk' => by simp [hk']) (row_implInst_step_inl (by simp) hb))
      (fun q => lift_idle rfl)⟩
  | bindRet q j U d hb =>
    exact ⟨Sum.inl Lab.tau, rfl, instAt_event_step (w' := w) (a' := a) (GaEvt.bindRet q j U)
      (procStep_update (ProcStep.bindRetRecv (u j) q U)
        (fun i hi => ProcStep.bindRetIdle (u i) q j U (Ne.symm hi)))
      (NetStep.bindRetIdle w q j U) (fun k => lift_idle rfl)
      (lift_update (by simp) (fun q' hq' => by simp [hq']) (row_implInst_step_inl (by simp) hb))⟩
  | ret id g hin hbind hsub hQ hr =>
    exact ⟨Sum.inl (.ret id g (w.core.getD (coreOfNet P w.net))), rfl,
      instAt_lab_step (a' := a) (b' := b) (by simp)
        (procStep_update (ProcStep.ret (u id) g _ hin hbind hsub hQ hr)
          (fun i hi => ProcStep.retIdle (u i) id g _ (Ne.symm hi)))
        (NetStep.ret w id g) (fun k => lift_idle rfl) (fun q => lift_idle rfl)⟩
  | fail id =>
    exact ⟨Sum.inl (.fail id), rfl, instAt_lab_step (x := u) (by simp)
      (fun i => ProcStep.failIdle (u i) id) (NetStep.fail w id)
      (lift_all (l₀ := fun _ => Sum.inl (BRB.Lab.fail id)) (fun k => rfl)
        (fun k => row_implInst_step_inl (by simp) (BRB.ImplStep.fail (a k) id)))
      (lift_all (l₀ := fun _ => Sum.inl (BRB.Lab.fail id)) (fun q => rfl)
        (fun q => row_implInst_step_inl (by simp) (BRB.ImplStep.fail (b q) id)))⟩

/-- **The row characterisation.** At a specification label `l₀`, the transitions
of the instance over the labels `specPull` sends to `l₀` are exactly the
`l₀`-rows of `LowStep`, on the same state and with the same distribution. -/
theorem lowInst_step_iff_row (P : Params) (s : LowState P.n X) (l₀ : Lab P.n X)
    (μ : PMF (LowState P.n X)) :
    (∃ l, specPull P.n X l = some l₀ ∧ (lowInst P X).step s l μ) ↔ LowStep P s l₀ μ := by
  constructor
  · rintro ⟨l, hl, hstep⟩
    obtain ⟨l₁, hl₁, hrow⟩ := lowInst_step_row P s l μ hstep
    have hll : l₁ = l₀ := Option.some.inj (show (some l₁ : Option (Lab P.n X)) = some l₀ by
      rw [← hl₁, hl])
    subst hll
    exact hrow
  · exact row_lowInst_step P s l₀ μ

/-- info: 'PLTS.ABA.Gather.lowInst_step_iff_row' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms lowInst_step_iff_row

end Gather
end ABA
end PLTS
