/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sathiya / Claude
-/

import Leslie2Protocols.ABA.Round.Sub
import Leslie2Protocols.ABA.Gather.SubLow
import Leslie2Protocols.ABA.Gather.SubSim
import Leslie2Protocols.Framework.Congruence
import Leslie2Protocols.Framework.MapIdleSim
import Leslie2.Results

/-!
# The two gather substitutions inside the round

The round over the gather instances over Bracha's broadcast
(`GBCA.lowPairSub`) is forward simulated by the round over the gather instances
over the broadcast specification (`GBCA.idealSub`), and that one by the round
over the gather specifications (`GBCA.pairSub`). The two relations are
`GBCA.Sub.LowPairRel` and `GBCA.Sub.IdealRel`: the layer held equal, and each
of the two gather coordinates related by the substitution of that tier
(`Gather.Sub.LowRel`, `Gather.Sub.CoreRel`).

Each proof is the congruence argument alone. The three rounds are one
expression over three gather tiers, so the gather substitution is carried
through the operators that expression is built from:
`ForwardSimulation.mapIdle` reads one gather instance over the round-internal
alphabet, `ForwardSimulation.parallel_right` and
`ForwardSimulation.parallel_left` hold the other gather instance and then the
layer, and `ForwardSimulation.abstract` and `ForwardSimulation.relabel` hide
the round's events and read the result back over the family alphabet. The two
gather instances are replaced one after the other and the two steps are joined
by `ForwardSimulation.trans`. `ForwardSimulation.congr` then reshapes the
composite relation: the intermediate state the composite quantifies over is the
first coordinate of the abstract side beside the second coordinate of the
concrete side.

All three rounds are LTS, so each substitution reads as an inclusion of
achievable trace distributions.

`Gather.Sub.lowRel_corrupt`, `GBCA.Sub.lowPairRel_corrupt` and
`GBCA.Sub.idealRel_corrupt` state that each relation is preserved by corrupting
both sides at once, in the shape the family congruence consumes
(`ForwardSimulation.family`, `hglob`).
-/

namespace PLTS
namespace ABA

namespace Gather
namespace Sub

/-- **Broadcast compatibility at the gather instance**: the broadcast
substitution relation is preserved by corrupting both instances at once. -/
theorem lowRel_corrupt {X : Type} [DecidableEq X] {P : Params} {s : LowSubState P.n X}
    {t : IdealSubState P.n X} (hR : LowRel P s t) (id : Fin P.n) :
    LowRel P (corruptAll P id (SubState.corrupt P id) (SubState.corrupt P id) s)
      (corruptAll P id (BRB.SpecState.corrupt P id) (BRB.SpecState.corrupt P id) t) :=
  ⟨congrArg (fun x => (x.1, { x.2 with net := x.2.net.corrupt P id })) hR.ga_eq,
    fun k => BRB.instRel_corrupt (hR.inRel k) id,
    fun q => BRB.instRel_corrupt (hR.bindRel q) id⟩

end Sub
end Gather

namespace GBCA
namespace Sub

/-! ### The broadcast substitution -/

/-- The broadcast substitution relation of the round: the layer equal, and each
gather coordinate related to its broadcast-specification coordinate by the
gather substitution relation. -/
structure LowPairRel (P : Params) (s : LowPairSubState P.n) (t : IdealSubState P.n) : Prop where
  /-- The programs and the round's bound bit are untouched by the
  substitution. -/
  layer_eq : s.1 = t.1
  /-- The first gather coordinate is substituted. -/
  ga1Rel : Gather.Sub.LowRel P (ga1 s) (ga1 t)
  /-- The second gather coordinate is substituted. -/
  ga2Rel : Gather.Sub.LowRel P (ga2 s) (ga2 t)

/-- The relation holds initially. -/
theorem lowPairRel_init (P : Params) (r : ℕ) :
    LowPairRel P (lowPairSub P r).init (idealSub P r).init :=
  ⟨rfl, Gather.Sub.lowRel_init, Gather.Sub.lowRel_init⟩

/-- **The broadcast substitution inside the round.** The round over the gather
instances over Bracha's broadcast is forward simulated by the round over the
gather instances over the broadcast specification. Each gather coordinate
carries the substitution; the congruences carry it through the round. -/
theorem lowPairRefines (P : Params) (r : ℕ) :
    ForwardSimulation (lowPairSub P r) (idealSub P r) (LowPairRel P) := by
  have h1 : ForwardSimulation ((Gather.lowSub P Bool).mapIdle (ga1Pull P.n))
      ((Gather.idealSub P Bool).mapIdle (ga1Pull P.n)) (Gather.Sub.LowRel P) :=
    ForwardSimulation.mapIdle (ga1Pull P.n) (ga1Pull_tau P.n)
      (fun _ h => ga1Pull_eq_tau h) (Gather.Sub.gatherLow P Bool)
  have h2 : ForwardSimulation ((Gather.lowSub P (Option Bool)).mapIdle (ga2Pull P.n))
      ((Gather.idealSub P (Option Bool)).mapIdle (ga2Pull P.n)) (Gather.Sub.LowRel P) :=
    ForwardSimulation.mapIdle (ga2Pull P.n) (ga2Pull_tau P.n)
      (fun _ h => ga2Pull_eq_tau h) (Gather.Sub.gatherLow P (Option Bool))
  have hGa := (h1.parallel_right ((Gather.lowSub P (Option Bool)).mapIdle (ga2Pull P.n))).trans
    (h2.parallel_left ((Gather.idealSub P Bool).mapIdle (ga1Pull P.n)))
  have hRound := ((hGa.parallel_left (layer P r)).abstract (rEvents P.n)).relabel
  refine ForwardSimulation.congr (fun s t => ?_) hRound
  constructor
  · rintro ⟨hlayer, ⟨c₁, c₂⟩, ⟨h1', rfl⟩, rfl, h2'⟩
    exact ⟨hlayer, h1', h2'⟩
  · rintro ⟨hlayer, h1', h2'⟩
    exact ⟨hlayer, (t.2.1, s.2.2), ⟨h1', rfl⟩, rfl, h2'⟩

/-! ### The gather substitution -/

/-- The gather substitution relation of the round: the layer equal, and each
gather coordinate related to its specification coordinate by the gather
refinement relation. -/
structure IdealRel (P : Params) (s : IdealSubState P.n) (t : PairSubState P.n) : Prop where
  /-- The programs and the round's bound bit are untouched by the
  substitution. -/
  layer_eq : s.1 = t.1
  /-- The first gather coordinate is substituted. -/
  ga1Rel : Gather.Sub.CoreRel P (ga1 s) (ga1 t)
  /-- The second gather coordinate is substituted. -/
  ga2Rel : Gather.Sub.CoreRel P (ga2 s) (ga2 t)

/-- The relation holds initially. -/
theorem idealRel_init (P : Params) (r : ℕ) :
    IdealRel P (idealSub P r).init (pairSub P r).init :=
  ⟨rfl, Gather.Sub.coreRel_init, Gather.Sub.coreRel_init⟩

/-- **The gather substitution inside the round.** The round over the gather
instances over the broadcast specification is forward simulated by the round
over the gather specifications. -/
theorem idealRefines (P : Params) (r : ℕ) :
    ForwardSimulation (idealSub P r) (pairSub P r) (IdealRel P) := by
  have h1 : ForwardSimulation ((Gather.idealSub P Bool).mapIdle (ga1Pull P.n))
      ((Gather.liftedSpec P Bool).mapIdle (ga1Pull P.n)) (Gather.Sub.CoreRel P) :=
    ForwardSimulation.mapIdle (ga1Pull P.n) (ga1Pull_tau P.n)
      (fun _ h => ga1Pull_eq_tau h) (Gather.Sub.gatherCore P Bool)
  have h2 : ForwardSimulation ((Gather.idealSub P (Option Bool)).mapIdle (ga2Pull P.n))
      ((Gather.liftedSpec P (Option Bool)).mapIdle (ga2Pull P.n)) (Gather.Sub.CoreRel P) :=
    ForwardSimulation.mapIdle (ga2Pull P.n) (ga2Pull_tau P.n)
      (fun _ h => ga2Pull_eq_tau h) (Gather.Sub.gatherCore P (Option Bool))
  have hGa := (h1.parallel_right ((Gather.idealSub P (Option Bool)).mapIdle (ga2Pull P.n))).trans
    (h2.parallel_left ((Gather.liftedSpec P Bool).mapIdle (ga1Pull P.n)))
  have hRound := ((hGa.parallel_left (layer P r)).abstract (rEvents P.n)).relabel
  refine ForwardSimulation.congr (fun s t => ?_) hRound
  constructor
  · rintro ⟨hlayer, ⟨c₁, c₂⟩, ⟨h1', rfl⟩, rfl, h2'⟩
    exact ⟨hlayer, h1', h2'⟩
  · rintro ⟨hlayer, h1', h2'⟩
    exact ⟨hlayer, (t.2.1, s.2.2), ⟨h1', rfl⟩, rfl, h2'⟩

/-! ### Trace-distribution inclusion -/

/-- Trace-distribution inclusion of the round over the gather instances over
Bracha's broadcast in the round over the gather instances over the broadcast
specification. -/
theorem lowPairSub_refines (P : Params) (r : ℕ) :
    achievableTraceDists (lowPairSub P r) ⊆ achievableTraceDists (idealSub P r) :=
  (ForwardSimulation.toProbabilistic (lowPairSub_isLTS P r) (idealSub_isLTS P r)
    (lowPairRel_init P r) (lowPairRefines P r)).achievableTraceDists_subset

/-- Trace-distribution inclusion of the round over the gather instances over
the broadcast specification in the round over the gather specifications. -/
theorem idealSub_refines (P : Params) (r : ℕ) :
    achievableTraceDists (idealSub P r) ⊆ achievableTraceDists (pairSub P r) :=
  (ForwardSimulation.toProbabilistic (idealSub_isLTS P r) (pairSub_isLTS P r)
    (idealRel_init P r) (idealRefines P r)).achievableTraceDists_subset

/-! ### Broadcast compatibility -/

/-- **Broadcast compatibility of the broadcast substitution**: the relation is
preserved by corrupting both rounds at once. -/
theorem lowPairRel_corrupt {P : Params} {s : LowPairSubState P.n} {t : IdealSubState P.n}
    (hR : LowPairRel P s t) (id : Fin P.n) :
    LowPairRel P
      (corruptAll P id
        (fun i => Gather.corruptAll P i (SubState.corrupt P i) (SubState.corrupt P i))
        (fun i => Gather.corruptAll P i (SubState.corrupt P i) (SubState.corrupt P i)) s)
      (corruptAll P id
        (fun i => Gather.corruptAll P i (BRB.SpecState.corrupt P i) (BRB.SpecState.corrupt P i))
        (fun i => Gather.corruptAll P i (BRB.SpecState.corrupt P i) (BRB.SpecState.corrupt P i))
        t) :=
  ⟨hR.layer_eq, Gather.Sub.lowRel_corrupt hR.ga1Rel id, Gather.Sub.lowRel_corrupt hR.ga2Rel id⟩

/-- **Broadcast compatibility of the gather substitution**: the relation is
preserved by corrupting both rounds at once. -/
theorem idealRel_corrupt {P : Params} {s : IdealSubState P.n} {t : PairSubState P.n}
    (hR : IdealRel P s t) (id : Fin P.n) :
    IdealRel P
      (corruptAll P id
        (fun i => Gather.corruptAll P i (BRB.SpecState.corrupt P i) (BRB.SpecState.corrupt P i))
        (fun i => Gather.corruptAll P i (BRB.SpecState.corrupt P i) (BRB.SpecState.corrupt P i))
        s)
      (corruptAll P id (fun i => Gather.SpecState.corrupt P i)
        (fun i => Gather.SpecState.corrupt P i) t) :=
  ⟨hR.layer_eq, Gather.Sub.coreRel_corrupt hR.ga1Rel id, Gather.Sub.coreRel_corrupt hR.ga2Rel id⟩

/-! ### Mechanical axiom check -/

/-- info: 'PLTS.ABA.GBCA.Sub.lowPairRefines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms lowPairRefines

/-- info: 'PLTS.ABA.GBCA.Sub.idealRefines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms idealRefines

/-- info: 'PLTS.ABA.GBCA.Sub.lowPairSub_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms lowPairSub_refines

/-- info: 'PLTS.ABA.GBCA.Sub.idealSub_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms idealSub_refines

end Sub
end GBCA
end ABA
end PLTS
