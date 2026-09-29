import DifferentialGeometry.Analysis.Integration.Integral.DominatedConvergence
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.LocalPullback
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Cost.Continuity.CarrierBaseTime
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Geodesic.ClosedIntervalExtension
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Geodesic.SmoothExtension
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.LGeometry.Action.AbsoluteContinuity
import DifferentialGeometry.Topology.Manifold.SmoothInterval
import Mathlib.Algebra.BigOperators.Fin
import DifferentialGeometry.Analysis.Integration.Integral.DominatedConvergenceQuadraticWeight
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Geodesic.SmoothTail
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Index.FiniteVariation
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.LGeometry.Action.ClosedIntervalRegularity
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.LGeometry.Action.SpatialMinimum
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.LGeometry.Action.Basic
noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

open Set Filter _root_.MeasureTheory
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian.Variation
open DifferentialGeometry.PDE.RicciFlow.Perelman
open scoped _root_.Manifold ContDiff _root_.Topology BigOperators Interval

universe u v z uSmoothJoin uPositiveStages uStageSmooth

private theorem exists_three_piece_stage_curve
    (H : ObservedHistory.{u}) (j : Fin (H.eventCount + 1)) (T : ℝ)
    (alpha beta gamma : ℝ → (H.stage j).Carrier) {a b c d : ℝ}
    (hab : a ≤ b) (hbc : b ≤ c) (hcd : c ≤ d)
    (ha : Manifold.absolutelyContinuousOnInterval ThreeModel alpha a b)
    (hb : Manifold.absolutelyContinuousOnInterval ThreeModel beta b c)
    (hc : Manifold.absolutelyContinuousOnInterval ThreeModel gamma c d)
    (hia : IntervalIntegrable (H.stageRegularizedLagrangian j T alpha) volume a b)
    (hib : IntervalIntegrable (H.stageRegularizedLagrangian j T beta) volume b c)
    (hic : IntervalIntegrable (H.stageRegularizedLagrangian j T gamma) volume c d)
    (habc : alpha b = beta b) (hbcd : beta c = gamma c) :
    ∃ delta : ℝ → (H.stage j).Carrier,
      Manifold.absolutelyContinuousOnInterval ThreeModel delta a d ∧
      IntervalIntegrable (H.stageRegularizedLagrangian j T delta) volume a d ∧
      EqOn delta alpha (Icc a b) ∧ EqOn delta beta (Icc b c) ∧
      EqOn delta gamma (Icc c d) ∧
      H.stageRegularizedAction j T delta a d =
        H.stageRegularizedAction j T alpha a b +
        H.stageRegularizedAction j T beta b c + H.stageRegularizedAction j T gamma c d := by
  classical
  let eta : ℝ → (H.stage j).Carrier := (Iic b).piecewise alpha beta
  obtain ⟨hetaAC, hetaInt, hetaLeft, hetaRight, hetaAction⟩ :=
    H.stageRegularizedAction_piecewise_Iic j T hab hbc alpha beta ha hb hia hib habc
  let delta : ℝ → (H.stage j).Carrier := (Iic c).piecewise eta gamma
  obtain ⟨hdeltaAC, hdeltaInt, hdeltaLeft, hdeltaRight, hdeltaAction⟩ :=
    H.stageRegularizedAction_piecewise_Iic j T (hab.trans hbc) hcd eta gamma
      hetaAC hc hetaInt hic ((hetaRight ⟨hbc, le_rfl⟩).trans hbcd)
  refine ⟨delta, hdeltaAC, hdeltaInt, ?_, ?_, hdeltaRight, ?_⟩
  · intro r hr
    exact (hdeltaLeft ⟨hr.1, hr.2.trans hbc⟩).trans (hetaLeft hr)
  · intro r hr
    exact (hdeltaLeft ⟨hab.trans hr.1, hr.2⟩).trans (hetaRight hr)
  · exact hdeltaAction.trans (congrArg
      (fun A => A + H.stageRegularizedAction j T gamma c d) hetaAction)

private theorem sum_stage_parts_eq_endpoints_add_events
    (H : ObservedHistory.{u}) (first last : Fin (H.eventCount + 1)) (hle : first ≤ last)
    (L M R : H.StageInterval first last → ℝ) :
    (∑ j : H.StageInterval first last, (L j + M j + R j)) =
      L ⟨last, hle, le_rfl⟩ + (∑ j, M j) +
      (∑ i : {i : Fin H.eventCount // first ≤ i.castSucc ∧ i.succ ≤ last},
        (R ⟨i.val.succ, i.property.1.trans i.val.castSucc_le_succ, i.property.2⟩ +
          L ⟨i.val.castSucc, i.property.1, i.val.castSucc_le_succ.trans i.property.2⟩)) +
      R ⟨first, le_rfl, hle⟩ := by
  classical
  let jf : H.StageInterval first last := ⟨first, le_rfl, hle⟩
  let jl : H.StageInterval first last := ⟨last, hle, le_rfl⟩
  let E := {i : Fin H.eventCount // first ≤ i.castSucc ∧ i.succ ≤ last}
  let eo : {j : H.StageInterval first last // j ≠ jl} ≃ E :=
    { toFun := fun j =>
        ⟨⟨j.val.val.val, by
          have hj := j.val.property.2
          have hn : j.val.val ≠ last := fun he => j.property (Subtype.ext he)
          have hl := last.isLt
          omega⟩, j.val.property.1, by
            have hj := j.val.property.2
            have hn : j.val.val ≠ last := fun he => j.property (Subtype.ext he)
            change j.val.val.val + 1 ≤ last.val
            have hneq : j.val.val.val ≠ last.val := fun he => hn (Fin.ext he)
            omega⟩
      invFun := fun i => ⟨⟨i.val.castSucc, i.property.1,
        i.val.castSucc_le_succ.trans i.property.2⟩, by
          intro he
          have hv := congrArg (fun j : H.StageInterval first last => j.val.val) he
          have hi := i.property.2
          change i.val.val + 1 ≤ last.val at hi
          change i.val.val = last.val at hv
          omega⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  let en : {j : H.StageInterval first last // j ≠ jf} ≃ E :=
    { toFun := fun j =>
        ⟨⟨j.val.val.val - 1, by
          have hj := j.val.val.isLt
          have hf := j.val.property.1
          have hn : first.val ≠ j.val.val.val := by
            intro he
            exact j.property (Subtype.ext (Fin.ext he.symm))
          omega⟩, by
            have hj := j.val.property.1
            have hn : first.val ≠ j.val.val.val := by
              intro he
              exact j.property (Subtype.ext (Fin.ext he.symm))
            change first.val ≤ j.val.val.val - 1
            omega, by
            have hj := j.val.property.2
            change j.val.val.val - 1 + 1 ≤ last.val
            have hpos : 0 < j.val.val.val := by
              have hjf := j.val.property.1
              have hn : first.val ≠ j.val.val.val := by
                intro he
                exact j.property (Subtype.ext (Fin.ext he.symm))
              omega
            omega⟩
      invFun := fun i => ⟨⟨i.val.succ,
        i.property.1.trans i.val.castSucc_le_succ, i.property.2⟩, by
          intro he
          have hv := congrArg (fun j : H.StageInterval first last => j.val.val) he
          have hi := i.property.1
          change first.val ≤ i.val.val at hi
          change i.val.val + 1 = first.val at hv
          omega⟩
      left_inv := fun j => by
        apply Subtype.ext
        apply Subtype.ext
        apply Fin.ext
        change j.val.val.val - 1 + 1 = j.val.val.val
        have hjf := j.val.property.1
        have hn : first.val ≠ j.val.val.val := by
          intro he
          exact j.property (Subtype.ext (Fin.ext he.symm))
        omega
      right_inv := fun i => by
        apply Subtype.ext
        apply Fin.ext
        change i.val.val + 1 - 1 = i.val.val
        omega }
  have hL := Fintype.sum_equiv eo (fun j => L j.val)
    (fun i => L ⟨i.val.castSucc, i.property.1, i.val.castSucc_le_succ.trans i.property.2⟩)
    (fun _ => rfl)
  have hR := Fintype.sum_equiv en (fun j => R j.val)
    (fun i => R ⟨i.val.succ, i.property.1.trans i.val.castSucc_le_succ, i.property.2⟩)
    (fun j => by
      congr 1
      apply Subtype.ext
      apply Fin.ext
      change j.val.val.val = j.val.val.val - 1 + 1
      have hjf := j.val.property.1
      have hn : first.val ≠ j.val.val.val := by
        intro he
        exact j.property (Subtype.ext (Fin.ext he.symm))
      omega)
  simp only [Finset.sum_add_distrib]
  rw [Fintype.sum_eq_add_sum_subtype_ne L jl, hL,
    Fintype.sum_eq_add_sum_subtype_ne R jf, hR]
  ring

private theorem exists_stage_family_of_collar_pieces
    (H : ObservedHistory.{u}) (first last : Fin (H.eventCount + 1)) (hle : first ≤ last)
    {T v : ℝ} (hv : 0 ≤ v)
    (hupper : T ∈ Icc (H.time last) (H.stageEndTime last))
    (hpast : T - v ^ 2 ∈ H.stageDomain first) :
    let J := H.StageInterval first last;
    let E := {i : Fin H.eventCount // first ≤ i.castSucc ∧ i.succ ≤ last};
    let jo (i : E) : J := ⟨i.val.castSucc, i.property.1,
      i.val.castSucc_le_succ.trans i.property.2⟩;
    let jn (i : E) : J := ⟨i.val.succ,
      i.property.1.trans i.val.castSucc_le_succ, i.property.2⟩;
    ∀ (lo hi : J → ℝ) (left middle right : (j : J) → ℝ → (H.stage j.val).Carrier),
      (∀ j, H.regularizedStageStart T 0 j.val ≤ lo j ∧ lo j ≤ hi j ∧
        hi j ≤ H.regularizedStageEnd T v j.val) →
      (∀ j, Manifold.absolutelyContinuousOnInterval ThreeModel (left j)
        (H.regularizedStageStart T 0 j.val) (lo j)) →
      (∀ j, Manifold.absolutelyContinuousOnInterval ThreeModel (middle j) (lo j) (hi j)) →
      (∀ j, Manifold.absolutelyContinuousOnInterval ThreeModel (right j)
        (hi j) (H.regularizedStageEnd T v j.val)) →
      (∀ j, IntervalIntegrable (H.stageRegularizedLagrangian j.val T (left j)) volume
        (H.regularizedStageStart T 0 j.val) (lo j)) →
      (∀ j, IntervalIntegrable (H.stageRegularizedLagrangian j.val T (middle j)) volume
        (lo j) (hi j)) →
      (∀ j, IntervalIntegrable (H.stageRegularizedLagrangian j.val T (right j)) volume
        (hi j) (H.regularizedStageEnd T v j.val)) →
      (∀ j, left j (lo j) = middle j (lo j)) →
      (∀ j, middle j (hi j) = right j (hi j)) →
    ∀ (W : (i : E) → TopologicalSpace.Opens (H.event i.val).incoming.terminalRegularOpen)
      (F : (i : E) → PartialDiffeomorph ThreeModel ThreeModel
        (H.event i.val).incoming.terminalRegularOpen (H.stage i.val.succ).Carrier ∞)
      (D : E → RealTimeInterval)
      (S : (i : E) → SolutionOn (I := ThreeModel) (M := W i) (D i))
      (eta : (i : E) → ℝ → W i),
      (∀ i z, (H.event i.val).RegularCrossing (z : W i).val.val (F i z.val)) →
      (∀ i, left (jo i) (Real.sqrt (T - H.time i.val.succ)) =
        (eta i (Real.sqrt (T - H.time i.val.succ))).val.val) →
      (∀ i, right (jn i) (Real.sqrt (T - H.time i.val.succ)) =
        F i (eta i (Real.sqrt (T - H.time i.val.succ))).val) →
      (∀ i, lRegularizedAction (S i) T (eta i) (hi (jn i)) (lo (jo i)) =
        H.stageRegularizedAction i.val.succ T (right (jn i)) (hi (jn i))
          (Real.sqrt (T - H.time i.val.succ)) +
        H.stageRegularizedAction i.val.castSucc T (left (jo i))
          (Real.sqrt (T - H.time i.val.succ)) (lo (jo i))) →
    ∃ delta : (j : J) → ℝ → (H.stage j.val).Carrier,
      (∀ j, Manifold.absolutelyContinuousOnInterval ThreeModel (delta j)
        (H.regularizedStageStart T 0 j.val) (H.regularizedStageEnd T v j.val)) ∧
      (∀ j, IntervalIntegrable (H.stageRegularizedLagrangian j.val T (delta j)) volume
        (H.regularizedStageStart T 0 j.val) (H.regularizedStageEnd T v j.val)) ∧
      (∀ j, EqOn (delta j) (left j) (Icc (H.regularizedStageStart T 0 j.val) (lo j)) ∧
        EqOn (delta j) (middle j) (Icc (lo j) (hi j)) ∧
        EqOn (delta j) (right j) (Icc (hi j) (H.regularizedStageEnd T v j.val))) ∧
      EqOn (delta ⟨last, hle, le_rfl⟩) (left ⟨last, hle, le_rfl⟩)
        (Icc 0 (lo ⟨last, hle, le_rfl⟩)) ∧
      delta ⟨last, hle, le_rfl⟩ 0 = left ⟨last, hle, le_rfl⟩ 0 ∧
      delta ⟨first, le_rfl, hle⟩ v = right ⟨first, le_rfl, hle⟩ v ∧
      (∀ (i : Fin H.eventCount) (hf : first ≤ i.castSucc) (hl : i.succ ≤ last),
        ∃ z : (H.event i).old,
          z.val.val = delta ⟨i.castSucc, hf, i.castSucc_le_succ.trans hl⟩
            (Real.sqrt (T - H.time i.succ)) ∧
          (H.event i).oldOutput z =
            delta ⟨i.succ, hf.trans i.castSucc_le_succ, hl⟩
              (Real.sqrt (T - H.time i.succ))) ∧
      (∑ j : J, H.stageRegularizedAction j.val T (delta j)
        (H.regularizedStageStart T 0 j.val) (H.regularizedStageEnd T v j.val)) =
        H.stageRegularizedAction last T (left ⟨last, hle, le_rfl⟩)
          0 (lo ⟨last, hle, le_rfl⟩) +
        (∑ j : J, H.stageRegularizedAction j.val T (middle j) (lo j) (hi j)) +
        (∑ i : E, lRegularizedAction (S i) T (eta i) (hi (jn i)) (lo (jo i))) +
        H.stageRegularizedAction first T (right ⟨first, le_rfl, hle⟩)
          (hi ⟨first, le_rfl, hle⟩) v := by
  classical
  intro J E jo jn lo hi left middle right hbounds hleftAC hmidAC hrightAC
    hleftInt hmidInt hrightInt hmatchL hmatchR W F D S eta hcross hnodeL hnodeR hseam
  have hpieces (j : J) := H.exists_three_piece_stage_curve j.val T
    (left j) (middle j) (right j) (hbounds j).1 (hbounds j).2.1 (hbounds j).2.2
    (hleftAC j) (hmidAC j) (hrightAC j) (hleftInt j) (hmidInt j) (hrightInt j)
    (hmatchL j) (hmatchR j)
  choose delta hAC hint hleft hmid hright haction using hpieces
  have hupper0 : T - (0 : ℝ) ^ 2 ∈ Icc (H.time last) (H.stageEndTime last) := by
    simpa only [zero_pow two_ne_zero, sub_zero] using hupper
  have hstart : H.regularizedStageStart T 0 last = 0 :=
    H.regularizedStageStart_eq_of_mem_Icc (show (0 : ℝ) ≤ 0 from le_rfl) hupper0
  have hend : H.regularizedStageEnd T v first = v :=
    H.regularizedStageEnd_eq_of_mem_stageDomain hv hpast
  have ho (i : E) : H.regularizedStageStart T 0 i.val.castSucc =
      Real.sqrt (T - H.time i.val.succ) :=
    H.regularizedStageStart_castSucc_eq_event_clock hupper0 i.val i.property.2
  have hn (i : E) : H.regularizedStageEnd T v i.val.succ =
      Real.sqrt (T - H.time i.val.succ) :=
    H.regularizedStageEnd_succ_eq_event_clock hpast i.val i.property.1
  have hprefix : EqOn (delta ⟨last, hle, le_rfl⟩) (left ⟨last, hle, le_rfl⟩)
      (Icc 0 (lo ⟨last, hle, le_rfl⟩)) := by
    simpa only [hstart] using hleft ⟨last, hle, le_rfl⟩
  refine ⟨delta, hAC, hint, fun j => ⟨hleft j, hmid j, hright j⟩, hprefix,
    hprefix ⟨le_rfl, ?_⟩, ?_, ?_, ?_⟩
  · simpa only [hstart] using (hbounds ⟨last, hle, le_rfl⟩).1
  · apply hright ⟨first, le_rfl, hle⟩
    constructor
    · simpa only [hend] using (hbounds ⟨first, le_rfl, hle⟩).2.2
    · exact hend.ge
  · intro i hf hl
    let k : E := ⟨i, hf, hl⟩
    have hoEq : delta (jo k) (Real.sqrt (T - H.time i.succ)) =
        (eta k (Real.sqrt (T - H.time i.succ))).val.val := by
      rw [← hnodeL k]
      apply hleft (jo k)
      constructor
      · exact (ho k).le
      · simpa only [jo, ho k] using (hbounds (jo k)).1
    have hnEq : delta (jn k) (Real.sqrt (T - H.time i.succ)) =
        F k (eta k (Real.sqrt (T - H.time i.succ))).val := by
      rw [← hnodeR k]
      apply hright (jn k)
      constructor
      · simpa only [jn, hn k] using (hbounds (jn k)).2.2
      · exact (hn k).ge
    obtain ⟨z, _, hzOld, hzNew⟩ := hcross k (eta k (Real.sqrt (T - H.time i.succ)))
    exact ⟨z, hzOld.trans hoEq.symm, hzNew.trans hnEq.symm⟩
  · calc
      _ = ∑ j : J, (H.stageRegularizedAction j.val T (left j)
          (H.regularizedStageStart T 0 j.val) (lo j) +
          H.stageRegularizedAction j.val T (middle j) (lo j) (hi j) +
          H.stageRegularizedAction j.val T (right j)
            (hi j) (H.regularizedStageEnd T v j.val)) :=
        Finset.sum_congr rfl (fun j _ => haction j)
      _ = _ := by
        rw [H.sum_stage_parts_eq_endpoints_add_events first last hle]
        simp only [hstart, hend]
        congr 2
        apply Finset.sum_congr rfl
        intro i _
        change H.stageRegularizedAction i.val.succ T (right (jn i))
          (hi (jn i)) (H.regularizedStageEnd T v i.val.succ) +
          H.stageRegularizedAction i.val.castSucc T (left (jo i))
            (H.regularizedStageStart T 0 i.val.castSucc) (lo (jo i)) = _
        rw [ho, hn]
        exact (hseam i).symm

private theorem extend_stage_family_by_zero_pole_stage
    (H : ObservedHistory.{u}) (first : Fin (H.eventCount + 1)) (i : Fin H.eventCount)
    (hf : first ≤ i.castSucc) (v : ℝ)
    (gamma : (j : H.StageInterval first i.succ) → ℝ → (H.stage j.val).Carrier)
    (delta : (j : H.StageInterval first i.castSucc) → ℝ → (H.stage j.val).Carrier)
    (hAC : ∀ j, Manifold.absolutelyContinuousOnInterval ThreeModel (delta j)
      (H.regularizedStageStart (H.time i.succ) 0 j.val)
      (H.regularizedStageEnd (H.time i.succ) v j.val))
    (hint : ∀ j, IntervalIntegrable
      (H.stageRegularizedLagrangian j.val (H.time i.succ) (delta j)) volume
      (H.regularizedStageStart (H.time i.succ) 0 j.val)
      (H.regularizedStageEnd (H.time i.succ) v j.val))
    (hnodes : ∀ (k : Fin H.eventCount) (hkf : first ≤ k.castSucc) (hkl : k.succ ≤ i.castSucc),
      ∃ z : (H.event k).old,
        z.val.val = delta ⟨k.castSucc, hkf, k.castSucc_le_succ.trans hkl⟩
          (Real.sqrt (H.time i.succ - H.time k.succ)) ∧
        (H.event k).oldOutput z = delta ⟨k.succ, hkf.trans k.castSucc_le_succ, hkl⟩
          (Real.sqrt (H.time i.succ - H.time k.succ)))
    (hstart : delta ⟨i.castSucc, hf, le_rfl⟩ 0 =
      gamma ⟨i.castSucc, hf, i.castSucc_le_succ⟩ 0)
    (hpole : ∃ z : (H.event i).old,
      z.val.val = gamma ⟨i.castSucc, hf, i.castSucc_le_succ⟩ 0 ∧
      (H.event i).oldOutput z = gamma ⟨i.succ, hf.trans i.castSucc_le_succ, le_rfl⟩ 0) :
    ∃ beta : (j : H.StageInterval first i.succ) → ℝ → (H.stage j.val).Carrier,
      (∀ j, Manifold.absolutelyContinuousOnInterval ThreeModel (beta j)
        (H.regularizedStageStart (H.time i.succ) 0 j.val)
        (H.regularizedStageEnd (H.time i.succ) v j.val)) ∧
      (∀ j, IntervalIntegrable
        (H.stageRegularizedLagrangian j.val (H.time i.succ) (beta j)) volume
        (H.regularizedStageStart (H.time i.succ) 0 j.val)
        (H.regularizedStageEnd (H.time i.succ) v j.val)) ∧
      (∀ j : H.StageInterval first i.castSucc,
        beta ⟨j.val, j.property.1, j.property.2.trans i.castSucc_le_succ⟩ = delta j) ∧
      beta ⟨i.succ, hf.trans i.castSucc_le_succ, le_rfl⟩ =
        gamma ⟨i.succ, hf.trans i.castSucc_le_succ, le_rfl⟩ ∧
      (∀ (k : Fin H.eventCount) (hkf : first ≤ k.castSucc) (hkl : k.succ ≤ i.succ),
        ∃ z : (H.event k).old,
          z.val.val = beta ⟨k.castSucc, hkf, k.castSucc_le_succ.trans hkl⟩
            (Real.sqrt (H.time i.succ - H.time k.succ)) ∧
          (H.event k).oldOutput z = beta ⟨k.succ, hkf.trans k.castSucc_le_succ, hkl⟩
            (Real.sqrt (H.time i.succ - H.time k.succ))) ∧
      (∑ j : H.StageInterval first i.succ,
        H.stageRegularizedAction j.val (H.time i.succ) (beta j)
          (H.regularizedStageStart (H.time i.succ) 0 j.val)
          (H.regularizedStageEnd (H.time i.succ) v j.val)) =
        ∑ j : H.StageInterval first i.castSucc,
          H.stageRegularizedAction j.val (H.time i.succ) (delta j)
            (H.regularizedStageStart (H.time i.succ) 0 j.val)
            (H.regularizedStageEnd (H.time i.succ) v j.val) := by
  classical
  let beta (j : H.StageInterval first i.succ) : ℝ → (H.stage j.val).Carrier :=
    if hj : j.val ≤ i.castSucc then delta ⟨j.val, j.property.1, hj⟩ else gamma j
  have hbetaOld (j : H.StageInterval first i.castSucc) :
      beta ⟨j.val, j.property.1, j.property.2.trans i.castSucc_le_succ⟩ = delta j := by
    simp only [beta, dite_eq_left j.property.2]
  have hbetaLast : beta ⟨i.succ, hf.trans i.castSucc_le_succ, le_rfl⟩ =
      gamma ⟨i.succ, hf.trans i.castSucc_le_succ, le_rfl⟩ := by
    simp only [beta, dite_eq_right (not_le_of_gt i.castSucc_lt_succ)]
  have hs : H.regularizedStageStart (H.time i.succ) 0 i.succ = 0 := by
    apply H.regularizedStageStart_eq_of_mem_Icc le_rfl
    simpa only [zero_pow two_ne_zero, sub_zero] using
      (show H.time i.succ ∈ Icc (H.time i.succ) (H.stageEndTime i.succ) from
        ⟨le_rfl, H.time_le_stageEndTime i.succ⟩)
  have he : H.regularizedStageEnd (H.time i.succ) v i.succ = 0 := by
    simp only [regularizedStageEnd, max_eq_right (sub_le_self _ (sq_nonneg v)),
      sub_self, Real.sqrt_zero]
  have hjLast (j : H.StageInterval first i.succ) (hj : ¬j.val ≤ i.castSucc) :
      j = ⟨i.succ, hf.trans i.castSucc_le_succ, le_rfl⟩ := by
    apply Subtype.ext
    apply Fin.ext
    have hh := j.property.2
    change j.val.val ≤ i.val + 1 at hh
    change ¬j.val.val ≤ i.val at hj
    change j.val.val = i.val + 1
    omega
  have hbetaAC (j : H.StageInterval first i.succ) :
      Manifold.absolutelyContinuousOnInterval ThreeModel (beta j)
        (H.regularizedStageStart (H.time i.succ) 0 j.val)
        (H.regularizedStageEnd (H.time i.succ) v j.val) := by
    by_cases hj : j.val ≤ i.castSucc
    · simpa only [beta, dite_eq_left hj] using hAC ⟨j.val, j.property.1, hj⟩
    · rw [hjLast j hj, hs, he]
      apply Manifold.absolutelyContinuousOnInterval_of_contMDiffOn
      apply (contMDiffOn_const (c := beta ⟨i.succ, hf.trans i.castSucc_le_succ, le_rfl⟩ 0)).congr
      intro r hr
      have hr0 : r = 0 := by simpa only [uIcc_self, mem_singleton_iff] using hr
      simp only [hr0]
  have hbetaInt (j : H.StageInterval first i.succ) :
      IntervalIntegrable (H.stageRegularizedLagrangian j.val (H.time i.succ) (beta j)) volume
        (H.regularizedStageStart (H.time i.succ) 0 j.val)
        (H.regularizedStageEnd (H.time i.succ) v j.val) := by
    by_cases hj : j.val ≤ i.castSucc
    · simpa only [beta, dite_eq_left hj] using hint ⟨j.val, j.property.1, hj⟩
    · rw [hjLast j hj, hs, he]
  refine ⟨beta, hbetaAC, hbetaInt, hbetaOld, hbetaLast, ?_, ?_⟩
  · intro k hkf hkl
    by_cases hki : k = i
    · subst k
      obtain ⟨z, hzOld, hzNew⟩ := hpole
      simp only [sub_self, Real.sqrt_zero]
      refine ⟨z, ?_, ?_⟩
      · rw [hbetaOld ⟨i.castSucc, hf, le_rfl⟩]
        exact hzOld.trans hstart.symm
      · rw [hbetaLast]
        exact hzNew
    · have hkOld : k.succ ≤ i.castSucc := by
        have hval : k.val ≠ i.val := fun h => hki (Fin.ext h)
        change k.val + 1 ≤ i.val
        change k.val + 1 ≤ i.val + 1 at hkl
        omega
      obtain ⟨z, hzOld, hzNew⟩ := hnodes k hkf hkOld
      refine ⟨z, ?_, ?_⟩
      · rw [hbetaOld ⟨k.castSucc, hkf, k.castSucc_le_succ.trans hkOld⟩]
        exact hzOld
      · rw [hbetaOld ⟨k.succ, hkf.trans k.castSucc_le_succ, hkOld⟩]
        exact hzNew
  · let jl : H.StageInterval first i.succ := ⟨i.succ, hf.trans i.castSucc_le_succ, le_rfl⟩
    let action (j : H.StageInterval first i.succ) :=
      H.stageRegularizedAction j.val (H.time i.succ) (beta j)
        (H.regularizedStageStart (H.time i.succ) 0 j.val)
        (H.regularizedStageEnd (H.time i.succ) v j.val)
    have hzero : action jl = 0 := by
      dsimp only [action, jl]
      rw [hs, he]
      exact intervalIntegral.integral_same
    let e : {j : H.StageInterval first i.succ // j ≠ jl} ≃
        H.StageInterval first i.castSucc :=
      { toFun := fun j => ⟨j.val.val, j.val.property.1, by
          by_contra hj
          exact j.property (hjLast j.val hj)⟩
        invFun := fun j => ⟨⟨j.val, j.property.1, j.property.2.trans i.castSucc_le_succ⟩, by
          intro h
          have hv := congrArg (fun j : H.StageInterval first i.succ => j.val.val) h
          have hj := j.property.2
          change j.val.val ≤ i.val at hj
          change j.val.val = i.val + 1 at hv
          omega⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    change (∑ j, action j) = _
    rw [Fintype.sum_eq_add_sum_subtype_ne action jl, hzero, zero_add]
    exact Fintype.sum_equiv e (fun j => action j.val) _ (fun j => by
      have hbj := hbetaOld (e j)
      change beta j.val = delta (e j) at hbj
      dsimp only [action]
      rw [hbj]
      rfl)

private theorem smooth_curve_projected_action
    (H : ObservedHistory.{u}) (j : Fin (H.eventCount + 1))
    {X : Type v} [TopologicalSpace X] [ChartedSpace ThreeSpace X]
    [IsManifold ThreeModel ∞ X] [T2Space X]
    {D : RealTimeInterval} (S : SolutionOn (I := ThreeModel) (M := X) D)
    (f : X → (H.stage j).Carrier) (hf : IsLocalDiffeomorph ThreeModel ThreeModel ∞ f)
    (T c d : ℝ) (eta : ℝ → X) (heta : ContMDiff 𝓘(ℝ, ℝ) ThreeModel 1 eta)
    (hint : IntervalIntegrable (lRegularizedLagrangian S T eta) volume c d)
    (hmetric : ∀ r ∈ uIoo c d, S.base.metric (T - r ^ 2) =
      localPullMetric (H.stageMetric j (T - r ^ 2)) f hf) :
    Manifold.absolutelyContinuousOnInterval ThreeModel (f ∘ eta) c d ∧
      IntervalIntegrable (H.stageRegularizedLagrangian j T (f ∘ eta)) volume c d ∧
      H.stageRegularizedAction j T (f ∘ eta) c d = lRegularizedAction S T eta c d := by
  have hcomp : ContMDiff 𝓘(ℝ, ℝ) ThreeModel 1 (f ∘ eta) :=
    (hf.contMDiff.of_le (by decide : (1 : WithTop ℕ∞) ≤ ∞)).comp heta
  have heq : EqOn (lRegularizedLagrangian S T eta)
      (H.stageRegularizedLagrangian j T (f ∘ eta)) (uIoo c d) := by
    intro r hr
    exact (H.stageRegularizedLagrangian_comp_eq_of_localPullMetric j S f hf T
      (heta.mdifferentiable one_ne_zero r) (hmetric r hr)).symm
  exact ⟨Manifold.absolutelyContinuousOnInterval_of_contMDiffOn hcomp.contMDiffOn,
    hint.congr_uIoo heq, H.stageRegularizedAction_comp_eq_of_localPullMetric j S f hf T c d
      eta heta hmetric⟩

private theorem smooth_survivor_curve_projected_actions
    (H : ObservedHistory.{u}) (i : Fin H.eventCount)
    {X : Type v} [TopologicalSpace X] [ChartedSpace ThreeSpace X]
    [IsManifold ThreeModel ∞ X] [T2Space X]
    {D : RealTimeInterval} (S : SolutionOn (I := ThreeModel) (M := X) D)
    (hS : IsSolutionOn S)
    (oldMap : X → (H.stage i.castSucc).Carrier)
    (newMap : X → (H.stage i.succ).Carrier)
    (hold : IsLocalDiffeomorph ThreeModel ThreeModel ∞ oldMap)
    (hnew : IsLocalDiffeomorph ThreeModel ThreeModel ∞ newMap)
    (hcross : ∀ x, (H.event i).RegularCrossing (oldMap x) (newMap x))
    (T : ℝ) {c w d : ℝ} (hcw : c ≤ w) (hwd : w ≤ d)
    (hclock : ∀ r ∈ Icc c d, T - r ^ 2 ∈ D.carrier)
    (hmetricOld : ∀ r ∈ Ioo w d, S.base.metric (T - r ^ 2) =
      localPullMetric (H.stageMetric i.castSucc (T - r ^ 2)) oldMap hold)
    (hmetricNew : ∀ r ∈ Ioo c w, S.base.metric (T - r ^ 2) =
      localPullMetric (H.stageMetric i.succ (T - r ^ 2)) newMap hnew)
    (eta : ℝ → X) (heta : ContMDiff 𝓘(ℝ, ℝ) ThreeModel 1 eta) :
    Manifold.absolutelyContinuousOnInterval ThreeModel (newMap ∘ eta) c w ∧
      Manifold.absolutelyContinuousOnInterval ThreeModel (oldMap ∘ eta) w d ∧
      IntervalIntegrable (H.stageRegularizedLagrangian i.succ T (newMap ∘ eta)) volume c w ∧
      IntervalIntegrable (H.stageRegularizedLagrangian i.castSucc T (oldMap ∘ eta)) volume w d ∧
      (∃ z : (H.event i).old, z.val.val = oldMap (eta w) ∧
        (H.event i).oldOutput z = newMap (eta w)) ∧
      H.stageRegularizedAction i.succ T (newMap ∘ eta) c w +
          H.stageRegularizedAction i.castSucc T (oldMap ∘ eta) w d =
        lRegularizedAction S T eta c d := by
  have hcd := hcw.trans hwd
  have hc := lRegularizedLagrangian_continuousOn_carrier S hS eta heta
  have hLag := hc.comp (s := Icc c d)
    (f := fun r : ℝ => (T, r))
    (continuous_const.prodMk continuous_id).continuousOn (fun r hr => hclock r hr)
  have hint : IntervalIntegrable (lRegularizedLagrangian S T eta) volume c d :=
    hLag.intervalIntegrable_of_Icc hcd
  have hintLeft : IntervalIntegrable (lRegularizedLagrangian S T eta) volume c w :=
    hint.mono_set (by
      simpa only [uIcc_of_le hcw, uIcc_of_le hcd] using Icc_subset_Icc le_rfl hwd)
  have hintRight : IntervalIntegrable (lRegularizedLagrangian S T eta) volume w d :=
    hint.mono_set (by
      simpa only [uIcc_of_le hwd, uIcc_of_le hcd] using Icc_subset_Icc hcw le_rfl)
  obtain ⟨hACLeft, hIntLeft, hActionLeft⟩ :=
    H.smooth_curve_projected_action i.succ S newMap hnew T c w eta heta hintLeft
      (by simpa only [uIoo_of_le hcw] using hmetricNew)
  obtain ⟨hACRight, hIntRight, hActionRight⟩ :=
    H.smooth_curve_projected_action i.castSucc S oldMap hold T w d eta heta hintRight
      (by simpa only [uIoo_of_le hwd] using hmetricOld)
  refine ⟨hACLeft, hACRight, hIntLeft, hIntRight, ?_, ?_⟩
  · obtain ⟨z, _, hz, hzout⟩ := hcross (eta w)
    exact ⟨z, hz, hzout⟩
  · rw [hActionLeft, hActionRight]
    exact lRegularizedAction_add S T eta c w d hintLeft hintRight

private theorem isLocalMin_collar_action_of_action_minimum
    (H : ObservedHistory.{u}) (first last : Fin (H.eventCount + 1)) (hle : first ≤ last)
    {T v : ℝ} (hv : 0 ≤ v)
    (hupper : T ∈ Icc (H.time last) (H.stageEndTime last))
    (hpast : T - v ^ 2 ∈ H.stageDomain first) :
    let J := H.StageInterval first last;
    let E := {i : Fin H.eventCount // first ≤ i.castSucc ∧ i.succ ≤ last};
    let jo (i : E) : J := ⟨i.val.castSucc, i.property.1,
      i.val.castSucc_le_succ.trans i.property.2⟩;
    let jn (i : E) : J := ⟨i.val.succ,
      i.property.1.trans i.val.castSucc_le_succ, i.property.2⟩;
    let jf : J := ⟨first, le_rfl, hle⟩;
    let jl : J := ⟨last, hle, le_rfl⟩;
    ∀ (gamma : (j : J) → ℝ → (H.stage j.val).Carrier)
      (lo hi : J → ℝ)
      (left middle right : ℝ → (j : J) → ℝ → (H.stage j.val).Carrier),
      (∀ j, H.regularizedStageStart T 0 j.val ≤ lo j ∧ lo j ≤ hi j ∧
        hi j ≤ H.regularizedStageEnd T v j.val) →
      (∀ j, EqOn (left 0 j) (gamma j)
          (Icc (H.regularizedStageStart T 0 j.val) (lo j)) ∧
        EqOn (middle 0 j) (gamma j) (Icc (lo j) (hi j)) ∧
        EqOn (right 0 j) (gamma j)
          (Icc (hi j) (H.regularizedStageEnd T v j.val))) →
      (∀ delta : (j : J) → ℝ → (H.stage j.val).Carrier,
        (∀ j, Manifold.absolutelyContinuousOnInterval ThreeModel (delta j)
          (H.regularizedStageStart T 0 j.val) (H.regularizedStageEnd T v j.val)) →
        (∀ j, IntervalIntegrable (H.stageRegularizedLagrangian j.val T (delta j)) volume
          (H.regularizedStageStart T 0 j.val) (H.regularizedStageEnd T v j.val)) →
        delta jl 0 = gamma jl 0 →
        (∀ (i : Fin H.eventCount) (hf : first ≤ i.castSucc) (hl : i.succ ≤ last),
          ∃ z : (H.event i).old,
            z.val.val = delta ⟨i.castSucc, hf, i.castSucc_le_succ.trans hl⟩
              (Real.sqrt (T - H.time i.succ)) ∧
            (H.event i).oldOutput z = delta ⟨i.succ, hf.trans i.castSucc_le_succ, hl⟩
              (Real.sqrt (T - H.time i.succ))) →
        (∑ j : J, H.stageRegularizedAction j.val T (gamma j)
          (H.regularizedStageStart T 0 j.val) (H.regularizedStageEnd T v j.val)) ≤
        (∑ j : J, H.stageRegularizedAction j.val T (delta j)
          (H.regularizedStageStart T 0 j.val) (H.regularizedStageEnd T v j.val))) →
    ∀ (W : (i : E) → TopologicalSpace.Opens (H.event i.val).incoming.terminalRegularOpen)
      (F : (i : E) → PartialDiffeomorph ThreeModel ThreeModel
        (H.event i.val).incoming.terminalRegularOpen (H.stage i.val.succ).Carrier ∞)
      (D : E → RealTimeInterval)
      (S : (i : E) → SolutionOn (I := ThreeModel) (M := W i) (D i))
      (hold : ∀ i, IsLocalDiffeomorph ThreeModel ThreeModel ∞
        (fun z : W i => z.val.val))
      (hnew : ∀ i, IsLocalDiffeomorph ThreeModel ThreeModel ∞
        (fun z : W i => F i z.val))
      (eta : ℝ → (i : E) → ℝ → W i),
      (∀ i, IsSolutionOn (S i)) →
      (∀ i z, (H.event i.val).RegularCrossing (z : W i).val.val (F i z.val)) →
      (∀ i, ∀ r ∈ Icc (hi (jn i)) (lo (jo i)), T - r ^ 2 ∈ (D i).carrier) →
      (∀ i, ∀ r ∈ Ioo (Real.sqrt (T - H.time i.val.succ)) (lo (jo i)),
        (S i).base.metric (T - r ^ 2) =
          localPullMetric (H.stageMetric i.val.castSucc (T - r ^ 2))
            (fun z : W i => z.val.val) (hold i)) →
      (∀ i, ∀ r ∈ Ioo (hi (jn i)) (Real.sqrt (T - H.time i.val.succ)),
        (S i).base.metric (T - r ^ 2) =
          localPullMetric (H.stageMetric i.val.succ (T - r ^ 2))
            (fun z : W i => F i z.val) (hnew i)) →
      (∀ᶠ e in 𝓝 (0 : ℝ),
        (∀ j, Manifold.absolutelyContinuousOnInterval ThreeModel (left e j)
          (H.regularizedStageStart T 0 j.val) (lo j)) ∧
        (∀ j, Manifold.absolutelyContinuousOnInterval ThreeModel (middle e j) (lo j) (hi j)) ∧
        (∀ j, Manifold.absolutelyContinuousOnInterval ThreeModel (right e j)
          (hi j) (H.regularizedStageEnd T v j.val)) ∧
        (∀ j, IntervalIntegrable (H.stageRegularizedLagrangian j.val T (left e j)) volume
          (H.regularizedStageStart T 0 j.val) (lo j)) ∧
        (∀ j, IntervalIntegrable (H.stageRegularizedLagrangian j.val T (middle e j)) volume
          (lo j) (hi j)) ∧
        (∀ j, IntervalIntegrable (H.stageRegularizedLagrangian j.val T (right e j)) volume
          (hi j) (H.regularizedStageEnd T v j.val)) ∧
        (∀ j, left e j (lo j) = middle e j (lo j)) ∧
        (∀ j, middle e j (hi j) = right e j (hi j)) ∧
        EqOn (left e jl) (gamma jl) (Icc 0 (lo jl)) ∧
        (∀ i, ContMDiff 𝓘(ℝ, ℝ) ThreeModel 1 (eta e i)) ∧
        (∀ i, EqOn (left e (jo i)) (fun r => (eta e i r).val.val)
          (Icc (Real.sqrt (T - H.time i.val.succ)) (lo (jo i)))) ∧
        (∀ i, EqOn (right e (jn i)) (fun r => F i (eta e i r).val)
          (Icc (hi (jn i)) (Real.sqrt (T - H.time i.val.succ))))) →
      IsLocalMin (fun e =>
        (∑ j : J, H.stageRegularizedAction j.val T (middle e j) (lo j) (hi j)) +
        (∑ i : E, lRegularizedAction (S i) T (eta e i) (hi (jn i)) (lo (jo i))) +
        H.stageRegularizedAction first T (right e jf) (hi jf) v) 0 := by
  classical
  intro J E jo jn jf jl gamma lo hi left middle right hbounds hcenter hminimum
    W F D S hold hnew eta hS hcross hclock hmetricOld hmetricNew hlocal
  have hupper0 : T - (0 : ℝ) ^ 2 ∈ Icc (H.time last) (H.stageEndTime last) := by
    simpa only [zero_pow two_ne_zero, sub_zero] using hupper
  have hstart : H.regularizedStageStart T 0 last = 0 :=
    H.regularizedStageStart_eq_of_mem_Icc le_rfl hupper0
  have ho (i : E) : H.regularizedStageStart T 0 i.val.castSucc =
      Real.sqrt (T - H.time i.val.succ) :=
    H.regularizedStageStart_castSucc_eq_event_clock hupper0 i.val i.property.2
  have hn (i : E) : H.regularizedStageEnd T v i.val.succ =
      Real.sqrt (T - H.time i.val.succ) :=
    H.regularizedStageEnd_succ_eq_event_clock hpast i.val i.property.1
  have hcw (i : E) : hi (jn i) ≤ Real.sqrt (T - H.time i.val.succ) := by
    simpa only [jn, hn i] using (hbounds (jn i)).2.2
  have hwd (i : E) : Real.sqrt (T - H.time i.val.succ) ≤ lo (jo i) := by
    simpa only [jo, ho i] using (hbounds (jo i)).1
  let headAction := H.stageRegularizedAction last T (gamma jl) 0 (lo jl)
  let action (e : ℝ) :=
    (∑ j : J, H.stageRegularizedAction j.val T (middle e j) (lo j) (hi j)) +
    (∑ i : E, lRegularizedAction (S i) T (eta e i) (hi (jn i)) (lo (jo i))) +
    H.stageRegularizedAction first T (right e jf) (hi jf) v
  have hproduce : ∀ᶠ e in 𝓝 (0 : ℝ),
      ∃ delta : (j : J) → ℝ → (H.stage j.val).Carrier,
        (∀ j, Manifold.absolutelyContinuousOnInterval ThreeModel (delta j)
          (H.regularizedStageStart T 0 j.val) (H.regularizedStageEnd T v j.val)) ∧
        (∀ j, IntervalIntegrable (H.stageRegularizedLagrangian j.val T (delta j)) volume
          (H.regularizedStageStart T 0 j.val) (H.regularizedStageEnd T v j.val)) ∧
        (∀ j, EqOn (delta j) (left e j)
            (Icc (H.regularizedStageStart T 0 j.val) (lo j)) ∧
          EqOn (delta j) (middle e j) (Icc (lo j) (hi j)) ∧
          EqOn (delta j) (right e j)
            (Icc (hi j) (H.regularizedStageEnd T v j.val))) ∧
        delta jl 0 = gamma jl 0 ∧
        (∀ (i : Fin H.eventCount) (hf : first ≤ i.castSucc) (hl : i.succ ≤ last),
          ∃ z : (H.event i).old,
            z.val.val = delta ⟨i.castSucc, hf, i.castSucc_le_succ.trans hl⟩
              (Real.sqrt (T - H.time i.succ)) ∧
            (H.event i).oldOutput z = delta ⟨i.succ, hf.trans i.castSucc_le_succ, hl⟩
              (Real.sqrt (T - H.time i.succ))) ∧
        (∑ j : J, H.stageRegularizedAction j.val T (delta j)
          (H.regularizedStageStart T 0 j.val) (H.regularizedStageEnd T v j.val)) =
            headAction + action e := by
    filter_upwards [hlocal] with e he
    obtain ⟨hleftAC, hmidAC, hrightAC, hleftInt, hmidInt, hrightInt,
      hmatchL, hmatchR, hprefix, heta, hprojOld, hprojNew⟩ := he
    have hseam (i : E) : lRegularizedAction (S i) T (eta e i) (hi (jn i)) (lo (jo i)) =
        H.stageRegularizedAction i.val.succ T (right e (jn i)) (hi (jn i))
          (Real.sqrt (T - H.time i.val.succ)) +
        H.stageRegularizedAction i.val.castSucc T (left e (jo i))
          (Real.sqrt (T - H.time i.val.succ)) (lo (jo i)) := by
      obtain ⟨_, _, _, _, _, hh⟩ := H.smooth_survivor_curve_projected_actions i.val
        (S i) (hS i) (fun z : W i => z.val.val) (fun z : W i => F i z.val)
        (hold i) (hnew i) (hcross i) T (hcw i) (hwd i) (hclock i)
        (hmetricOld i) (hmetricNew i) (eta e i) (heta i)
      rw [← hh]
      congr 1
      · apply H.stageRegularizedAction_congr
        intro r hr
        rw [uIoo_of_le (hcw i)] at hr
        exact (hprojNew i (Ioo_subset_Icc_self hr)).symm
      · apply H.stageRegularizedAction_congr
        intro r hr
        rw [uIoo_of_le (hwd i)] at hr
        exact (hprojOld i (Ioo_subset_Icc_self hr)).symm
    obtain ⟨delta, hAC, hint, hpieces, _, hrecent, _, hnodes, hsum⟩ :=
      H.exists_stage_family_of_collar_pieces first last hle hv hupper hpast
        lo hi (left e) (middle e) (right e) hbounds hleftAC hmidAC hrightAC
        hleftInt hmidInt hrightInt hmatchL hmatchR W F D S (eta e) hcross
        (fun i => hprojOld i ⟨le_rfl, hwd i⟩)
        (fun i => hprojNew i ⟨hcw i, le_rfl⟩) hseam
    have hlo0 : 0 ≤ lo jl := by simpa only [jl, hstart] using (hbounds jl).1
    refine ⟨delta, hAC, hint, hpieces, hrecent.trans (hprefix ⟨le_rfl, hlo0⟩), hnodes, ?_⟩
    have hprefixAction : H.stageRegularizedAction last T (left e jl) 0 (lo jl) = headAction := by
      apply H.stageRegularizedAction_congr
      intro r hr
      rw [uIoo_of_le hlo0] at hr
      exact hprefix (Ioo_subset_Icc_self hr)
    change _ = headAction + action e
    rw [hsum, hprefixAction]
    dsimp only [action]
    ring
  have hcenterAction :
      (∑ j : J, H.stageRegularizedAction j.val T (gamma j)
        (H.regularizedStageStart T 0 j.val) (H.regularizedStageEnd T v j.val)) =
          headAction + action 0 := by
    obtain ⟨delta, _, _, hpieces, _, _, hsum⟩ := hproduce.self_of_nhds
    rw [← hsum]
    apply Finset.sum_congr rfl
    intro j _
    apply H.stageRegularizedAction_congr
    intro r hr
    have hordered := (hbounds j).1.trans ((hbounds j).2.1.trans (hbounds j).2.2)
    rw [uIoo_of_le hordered] at hr
    have hδ : delta j r = gamma j r := by
      by_cases hrl : r ≤ lo j
      · exact ((hpieces j).1 ⟨hr.1.le, hrl⟩).trans ((hcenter j).1 ⟨hr.1.le, hrl⟩)
      · by_cases hrh : r ≤ hi j
        · exact ((hpieces j).2.1 ⟨(not_le.mp hrl).le, hrh⟩).trans
            ((hcenter j).2.1 ⟨(not_le.mp hrl).le, hrh⟩)
        · exact ((hpieces j).2.2 ⟨(not_le.mp hrh).le, hr.2.le⟩).trans
            ((hcenter j).2.2 ⟨(not_le.mp hrh).le, hr.2.le⟩)
    exact hδ.symm
  change ∀ᶠ e in 𝓝 (0 : ℝ), action 0 ≤ action e
  filter_upwards [hproduce] with e he
  obtain ⟨delta, hAC, hint, _, hrecent, hnodes, hsum⟩ := he
  have hh := hminimum delta hAC hint hrecent hnodes
  rw [hcenterAction, hsum] at hh
  linarith

private theorem isLocalMin_smooth_piece_action_of_action_minimum
    (H : ObservedHistory.{u}) (first last : Fin (H.eventCount + 1)) (hle : first ≤ last)
    {T v : ℝ} (hv : 0 ≤ v)
    (hupper : T ∈ Icc (H.time last) (H.stageEndTime last))
    (hpast : T - v ^ 2 ∈ H.stageDomain first) :
    let J := H.StageInterval first last;
    let E := {i : Fin H.eventCount // first ≤ i.castSucc ∧ i.succ ≤ last};
    let jo (i : E) : J := ⟨i.val.castSucc, i.property.1,
      i.val.castSucc_le_succ.trans i.property.2⟩;
    let jn (i : E) : J := ⟨i.val.succ,
      i.property.1.trans i.val.castSucc_le_succ, i.property.2⟩;
    let jf : J := ⟨first, le_rfl, hle⟩;
    let jl : J := ⟨last, hle, le_rfl⟩;
    ∀ (gamma : (j : J) → ℝ → (H.stage j.val).Carrier) (lo hi : J → ℝ),
      (∀ j, H.regularizedStageStart T 0 j.val ≤ lo j ∧ lo j ≤ hi j ∧
        hi j ≤ H.regularizedStageEnd T v j.val) →
      Manifold.absolutelyContinuousOnInterval ThreeModel (gamma jl) 0 (lo jl) →
      IntervalIntegrable (H.stageRegularizedLagrangian last T (gamma jl)) volume 0 (lo jl) →
      (∀ delta : (j : J) → ℝ → (H.stage j.val).Carrier,
        (∀ j, Manifold.absolutelyContinuousOnInterval ThreeModel (delta j)
          (H.regularizedStageStart T 0 j.val) (H.regularizedStageEnd T v j.val)) →
        (∀ j, IntervalIntegrable (H.stageRegularizedLagrangian j.val T (delta j)) volume
          (H.regularizedStageStart T 0 j.val) (H.regularizedStageEnd T v j.val)) →
        delta jl 0 = gamma jl 0 →
        (∀ (i : Fin H.eventCount) (hf : first ≤ i.castSucc) (hl : i.succ ≤ last),
          ∃ z : (H.event i).old,
            z.val.val = delta ⟨i.castSucc, hf, i.castSucc_le_succ.trans hl⟩
              (Real.sqrt (T - H.time i.succ)) ∧
            (H.event i).oldOutput z = delta ⟨i.succ, hf.trans i.castSucc_le_succ, hl⟩
              (Real.sqrt (T - H.time i.succ))) →
        (∑ j : J, H.stageRegularizedAction j.val T (gamma j)
          (H.regularizedStageStart T 0 j.val) (H.regularizedStageEnd T v j.val)) ≤
        (∑ j : J, H.stageRegularizedAction j.val T (delta j)
          (H.regularizedStageStart T 0 j.val) (H.regularizedStageEnd T v j.val))) →
    ∀ (W : (i : E) → TopologicalSpace.Opens (H.event i.val).incoming.terminalRegularOpen)
      (F : (i : E) → PartialDiffeomorph ThreeModel ThreeModel
        (H.event i.val).incoming.terminalRegularOpen (H.stage i.val.succ).Carrier ∞)
      (DO : J → RealTimeInterval) (DS : E → RealTimeInterval) (DT : RealTimeInterval)
      (SO : (j : J) → SolutionOn (I := ThreeModel) (M := (H.stage j.val).Carrier) (DO j))
      (SS : (i : E) → SolutionOn (I := ThreeModel) (M := W i) (DS i))
      (ST : SolutionOn (I := ThreeModel) (M := (H.stage first).Carrier) DT)
      (hold : ∀ i, IsLocalDiffeomorph ThreeModel ThreeModel ∞ (fun z : W i => z.val.val))
      (hnew : ∀ i, IsLocalDiffeomorph ThreeModel ThreeModel ∞ (fun z : W i => F i z.val))
      (ordinary : (j : J) → ℝ → ℝ → (H.stage j.val).Carrier)
      (survivor : (i : E) → ℝ → ℝ → W i) (tail : ℝ → ℝ → (H.stage first).Carrier),
      (∀ j, IsSolutionOn (SO j)) → (∀ i, IsSolutionOn (SS i)) → IsSolutionOn ST →
      (∀ j t, (SO j).base.metric t = H.stageMetric j.val t) →
      (∀ t, ST.base.metric t = H.stageMetric first t) →
      (∀ j, ∀ r ∈ Icc (lo j) (hi j), T - r ^ 2 ∈ (DO j).carrier) →
      (∀ r ∈ Icc (hi jf) v, T - r ^ 2 ∈ DT.carrier) →
      (∀ i z, (H.event i.val).RegularCrossing (z : W i).val.val (F i z.val)) →
      (∀ i, ∀ r ∈ Icc (hi (jn i)) (lo (jo i)), T - r ^ 2 ∈ (DS i).carrier) →
      (∀ i, ∀ r ∈ Ioo (Real.sqrt (T - H.time i.val.succ)) (lo (jo i)),
        (SS i).base.metric (T - r ^ 2) =
          localPullMetric (H.stageMetric i.val.castSucc (T - r ^ 2))
            (fun z : W i => z.val.val) (hold i)) →
      (∀ i, ∀ r ∈ Ioo (hi (jn i)) (Real.sqrt (T - H.time i.val.succ)),
        (SS i).base.metric (T - r ^ 2) =
          localPullMetric (H.stageMetric i.val.succ (T - r ^ 2))
            (fun z : W i => F i z.val) (hnew i)) →
      (∀ j, IsSmoothVariation (I := ThreeModel) (ordinary j)) →
      (∀ i, IsSmoothVariation (I := ThreeModel) (survivor i)) →
      IsSmoothVariation (I := ThreeModel) tail →
      (∀ j, EqOn (ordinary j 0) (gamma j) (Icc (lo j) (hi j))) →
      EqOn (tail 0) (gamma jf) (Icc (hi jf) v) →
      (∀ i, EqOn (fun r => (survivor i 0 r).val.val) (gamma (jo i))
        (Icc (Real.sqrt (T - H.time i.val.succ)) (lo (jo i)))) →
      (∀ i, EqOn (fun r => F i (survivor i 0 r).val) (gamma (jn i))
        (Icc (hi (jn i)) (Real.sqrt (T - H.time i.val.succ)))) →
      (∀ᶠ epsilon in 𝓝 (0 : ℝ),
        ordinary jl epsilon (lo jl) = gamma jl (lo jl) ∧
        (∀ i, ordinary (jo i) epsilon (lo (jo i)) =
          (survivor i epsilon (lo (jo i))).val.val) ∧
        (∀ i, ordinary (jn i) epsilon (hi (jn i)) =
          F i (survivor i epsilon (hi (jn i))).val) ∧
        ordinary jf epsilon (hi jf) = tail epsilon (hi jf)) →
      IsLocalMin (fun epsilon =>
        (∑ j : J, lRegularizedAction (SO j) T (ordinary j epsilon) (lo j) (hi j)) +
        (∑ i : E, lRegularizedAction (SS i) T (survivor i epsilon) (hi (jn i)) (lo (jo i))) +
        lRegularizedAction ST T (tail epsilon) (hi jf) v) 0 := by
  classical
  intro J E jo jn jf jl gamma lo hi hbounds hprefixAC hprefixInt hminimum
    W F DO DS DT SO SS ST hold hnew ordinary survivor tail hSO hSS hST
    hmetricO hmetricT hclockO hclockT hcross hclockS hmetricOld hmetricNew
    hordinary hsurvivor htail hcenterO hcenterT hcenterOld hcenterNew hmatch
  have hupper0 : T - (0 : ℝ) ^ 2 ∈ Icc (H.time last) (H.stageEndTime last) := by
    simpa only [zero_pow two_ne_zero, sub_zero] using hupper
  have hstart : H.regularizedStageStart T 0 last = 0 :=
    H.regularizedStageStart_eq_of_mem_Icc le_rfl hupper0
  have hend : H.regularizedStageEnd T v first = v :=
    H.regularizedStageEnd_eq_of_mem_stageDomain hv hpast
  have ho (i : E) : H.regularizedStageStart T 0 i.val.castSucc =
      Real.sqrt (T - H.time i.val.succ) :=
    H.regularizedStageStart_castSucc_eq_event_clock hupper0 i.val i.property.2
  have hn (i : E) : H.regularizedStageEnd T v i.val.succ =
      Real.sqrt (T - H.time i.val.succ) :=
    H.regularizedStageEnd_succ_eq_event_clock hpast i.val i.property.1
  have hcw (i : E) : hi (jn i) ≤ Real.sqrt (T - H.time i.val.succ) := by
    simpa only [jn, hn i] using (hbounds (jn i)).2.2
  have hwd (i : E) : Real.sqrt (T - H.time i.val.succ) ≤ lo (jo i) := by
    simpa only [jo, ho i] using (hbounds (jo i)).1
  have hoinj : Function.Injective jo := by
    intro i k h
    apply Subtype.ext
    apply Fin.ext
    exact congrArg (fun j : J => j.val.val) h
  have hninj : Function.Injective jn := by
    intro i k h
    apply Subtype.ext
    apply Fin.ext
    have hv := congrArg (fun j : J => j.val.val) h
    change i.val.val + 1 = k.val.val + 1 at hv
    omega
  have hone (i : E) : jo i ≠ jl := by
    intro h
    have he := congrArg (fun j : J => j.val.val) h
    have hi := i.property.2
    change i.val.val = last.val at he
    change i.val.val + 1 ≤ last.val at hi
    omega
  have hnne (i : E) : jn i ≠ jf := by
    intro h
    have he := congrArg (fun j : J => j.val.val) h
    have hi := i.property.1
    change i.val.val + 1 = first.val at he
    change first.val ≤ i.val.val at hi
    omega
  have hocover (j : J) : j = jl ∨ ∃ i, jo i = j := by
    by_cases hj : j = jl
    · exact Or.inl hj
    · right
      have hneq : j.val.val ≠ last.val := fun h => hj (Subtype.ext (Fin.ext h))
      let i : Fin H.eventCount := ⟨j.val.val, by
        have hbound := j.property.2
        have hlast := last.isLt
        change j.val.val ≤ last.val at hbound
        omega⟩
      refine ⟨⟨i, j.property.1, ?_⟩, rfl⟩
      change j.val.val + 1 ≤ last.val
      have hbound := j.property.2
      change j.val.val ≤ last.val at hbound
      omega
  have hncover (j : J) : j = jf ∨ ∃ i, jn i = j := by
    by_cases hj : j = jf
    · exact Or.inl hj
    · right
      have hneq : j.val.val ≠ first.val := fun h => hj (Subtype.ext (Fin.ext h))
      have hpos : 0 < j.val.val := by
        have hbound := j.property.1
        change first.val ≤ j.val.val at hbound
        omega
      let i : Fin H.eventCount := ⟨j.val.val - 1, by have hb := j.val.isLt; omega⟩
      refine ⟨⟨i, ?_, ?_⟩, ?_⟩
      · change first.val ≤ j.val.val - 1
        have hbound := j.property.1
        change first.val ≤ j.val.val at hbound
        omega
      · change j.val.val - 1 + 1 ≤ last.val
        have hbound := j.property.2
        change j.val.val ≤ last.val at hbound
        omega
      · apply Subtype.ext
        apply Fin.ext
        change j.val.val - 1 + 1 = j.val.val
        omega
  have hfill (V : J → Type u) (endpoint : J) (p : E → J)
      (hinj : Function.Injective p) (hne : ∀ i, p i ≠ endpoint)
      (hcover : ∀ j, j = endpoint ∨ ∃ i, p i = j)
      (v0 : V endpoint) (vE : ∀ i, V (p i)) :
      ∃ out : ∀ j, V j, out endpoint = v0 ∧ ∀ i, out (p i) = vE i := by
    have hchoose (j : J) : ∃ y : V j,
        (j = endpoint → HEq y v0) ∧ (∀ i, p i = j → HEq y (vE i)) := by
      rcases hcover j with rfl | ⟨i, rfl⟩
      · exact ⟨v0, fun _ => HEq.rfl, fun i h => (hne i h).elim⟩
      · refine ⟨vE i, fun h => (hne i h).elim, ?_⟩
        intro k hk
        have he := hinj hk
        subst k
        rfl
    choose out hout using hchoose
    exact ⟨out, eq_of_heq ((hout endpoint).1 rfl),
      fun i => eq_of_heq ((hout (p i)).2 i rfl)⟩
  obtain ⟨L, hLlast, hLold⟩ := hfill (fun j => ℝ → ℝ → (H.stage j.val).Carrier)
    jl jo hoinj hone hocover (fun _ => gamma jl) (fun i epsilon r => (survivor i epsilon r).val.val)
  obtain ⟨R, hRfirst, hRnew⟩ := hfill (fun j => ℝ → ℝ → (H.stage j.val).Carrier)
    jf jn hninj hnne hncover tail (fun i epsilon r => F i (survivor i epsilon r).val)
  let left (epsilon : ℝ) (j : J) := L j epsilon
  let right (epsilon : ℝ) (j : J) := R j epsilon
  have hleftLast (epsilon : ℝ) : left epsilon jl = gamma jl := congrFun hLlast epsilon
  have hleftOld (epsilon : ℝ) (i : E) :
      left epsilon (jo i) = fun r => (survivor i epsilon r).val.val := congrFun (hLold i) epsilon
  have hrightFirst (epsilon : ℝ) : right epsilon jf = tail epsilon := congrFun hRfirst epsilon
  have hrightNew (epsilon : ℝ) (i : E) :
      right epsilon (jn i) = fun r => F i (survivor i epsilon r).val := congrFun (hRnew i) epsilon
  have hslice {X : Type u} [TopologicalSpace X] [ChartedSpace ThreeSpace X]
      [IsManifold ThreeModel ∞ X] [T2Space X] (f : ℝ → ℝ → X)
      (hf : IsSmoothVariation (I := ThreeModel) f) (epsilon : ℝ) :
      ContMDiff 𝓘(ℝ, ℝ) ThreeModel 1 (f epsilon) := by
    have hp : ContMDiff 𝓘(ℝ, ℝ) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) (8 : ℕ)
        (fun r : ℝ => (epsilon, r)) := contMDiff_const.prodMk contMDiff_id
    exact ((hf : ContMDiff _ _ (8 : ℕ) _).comp hp).of_le (by norm_num)
  have hpiece (j : J) {D : RealTimeInterval}
      (S : SolutionOn (I := ThreeModel) (M := (H.stage j.val).Carrier) D)
      (hS : IsSolutionOn S) (hmetric : ∀ t, S.base.metric t = H.stageMetric j.val t)
      (eta : ℝ → (H.stage j.val).Carrier) (heta : ContMDiff 𝓘(ℝ, ℝ) ThreeModel 1 eta)
      {a b : ℝ} (hab : a ≤ b) (hclock : ∀ r ∈ Icc a b, T - r ^ 2 ∈ D.carrier) :
      Manifold.absolutelyContinuousOnInterval ThreeModel eta a b ∧
        IntervalIntegrable (H.stageRegularizedLagrangian j.val T eta) volume a b ∧
        H.stageRegularizedAction j.val T eta a b = lRegularizedAction S T eta a b := by
    have hlag : H.stageRegularizedLagrangian j.val T eta = lRegularizedLagrangian S T eta := by
      funext r
      simp only [stageRegularizedLagrangian, lRegularizedLagrangian,
        SolutionOn.scalar, SolutionFamily.scalar, hmetric]
    have hc := lRegularizedLagrangian_continuousOn_carrier S hS eta heta
    have hcont := hc.comp (s := Icc a b) (f := fun r : ℝ => (T, r))
      (continuous_const.prodMk continuous_id).continuousOn (fun r hr => hclock r hr)
    refine ⟨Manifold.absolutelyContinuousOnInterval_of_contMDiffOn heta.contMDiffOn, ?_, ?_⟩
    · rw [hlag]
      exact hcont.intervalIntegrable_of_Icc hab
    · unfold stageRegularizedAction lRegularizedAction
      rw [hlag]
  have hO (epsilon : ℝ) (j : J) := hpiece j (SO j) (hSO j) (hmetricO j)
    (ordinary j epsilon) (hslice _ (hordinary j) epsilon) (hbounds j).2.1 (hclockO j)
  have htailBound : hi jf ≤ v := by simpa only [jf, hend] using (hbounds jf).2.2
  have hT (epsilon : ℝ) := hpiece jf ST hST hmetricT (tail epsilon)
    (hslice _ htail epsilon) htailBound hclockT
  have hSproj (epsilon : ℝ) (i : E) := H.smooth_survivor_curve_projected_actions i.val
    (SS i) (hSS i) (fun z : W i => z.val.val) (fun z : W i => F i z.val)
    (hold i) (hnew i) (hcross i) T (hcw i) (hwd i) (hclockS i)
    (hmetricOld i) (hmetricNew i) (survivor i epsilon) (hslice _ (hsurvivor i) epsilon)
  have hcenter : ∀ j, EqOn (left 0 j) (gamma j)
        (Icc (H.regularizedStageStart T 0 j.val) (lo j)) ∧
      EqOn (ordinary j 0) (gamma j) (Icc (lo j) (hi j)) ∧
      EqOn (right 0 j) (gamma j)
        (Icc (hi j) (H.regularizedStageEnd T v j.val)) := by
    intro j
    refine ⟨?_, hcenterO j, ?_⟩
    · rcases hocover j with rfl | ⟨i, rfl⟩
      · rw [hleftLast]
        exact fun _ _ => rfl
      · rw [hleftOld]
        simpa only [jo, ho i] using hcenterOld i
    · rcases hncover j with rfl | ⟨i, rfl⟩
      · rw [hrightFirst]
        simpa only [jf, hend] using hcenterT
      · rw [hrightNew]
        simpa only [jn, hn i] using hcenterNew i
  have hlocal : ∀ᶠ epsilon in 𝓝 (0 : ℝ),
      (∀ j, Manifold.absolutelyContinuousOnInterval ThreeModel (left epsilon j)
        (H.regularizedStageStart T 0 j.val) (lo j)) ∧
      (∀ j, Manifold.absolutelyContinuousOnInterval ThreeModel (ordinary j epsilon) (lo j) (hi j)) ∧
      (∀ j, Manifold.absolutelyContinuousOnInterval ThreeModel (right epsilon j)
        (hi j) (H.regularizedStageEnd T v j.val)) ∧
      (∀ j, IntervalIntegrable (H.stageRegularizedLagrangian j.val T (left epsilon j)) volume
        (H.regularizedStageStart T 0 j.val) (lo j)) ∧
      (∀ j, IntervalIntegrable (H.stageRegularizedLagrangian j.val T (ordinary j epsilon)) volume
        (lo j) (hi j)) ∧
      (∀ j, IntervalIntegrable (H.stageRegularizedLagrangian j.val T (right epsilon j)) volume
        (hi j) (H.regularizedStageEnd T v j.val)) ∧
      (∀ j, left epsilon j (lo j) = ordinary j epsilon (lo j)) ∧
      (∀ j, ordinary j epsilon (hi j) = right epsilon j (hi j)) ∧
      EqOn (left epsilon jl) (gamma jl) (Icc 0 (lo jl)) ∧
      (∀ i, ContMDiff 𝓘(ℝ, ℝ) ThreeModel 1 (survivor i epsilon)) ∧
      (∀ i, EqOn (left epsilon (jo i)) (fun r => (survivor i epsilon r).val.val)
        (Icc (Real.sqrt (T - H.time i.val.succ)) (lo (jo i)))) ∧
      (∀ i, EqOn (right epsilon (jn i)) (fun r => F i (survivor i epsilon r).val)
        (Icc (hi (jn i)) (Real.sqrt (T - H.time i.val.succ)))) := by
    filter_upwards [hmatch] with epsilon he
    obtain ⟨hfix, hjoinOld, hjoinNew, hjoinTail⟩ := he
    refine ⟨?_, fun j => (hO epsilon j).1, ?_, ?_, fun j => (hO epsilon j).2.1,
      ?_, ?_, ?_, ?_, fun i => hslice _ (hsurvivor i) epsilon, ?_, ?_⟩
    · intro j
      rcases hocover j with rfl | ⟨i, rfl⟩
      · rw [hleftLast]
        simpa only [jl, hstart] using hprefixAC
      · rw [hleftOld]
        simpa only [jo, ho i, Function.comp_def] using (hSproj epsilon i).2.1
    · intro j
      rcases hncover j with rfl | ⟨i, rfl⟩
      · rw [hrightFirst]
        simpa only [jf, hend] using (hT epsilon).1
      · rw [hrightNew]
        simpa only [jn, hn i, Function.comp_def] using (hSproj epsilon i).1
    · intro j
      rcases hocover j with rfl | ⟨i, rfl⟩
      · rw [hleftLast]
        simpa only [jl, hstart] using hprefixInt
      · rw [hleftOld]
        simpa only [jo, ho i, Function.comp_def] using (hSproj epsilon i).2.2.2.1
    · intro j
      rcases hncover j with rfl | ⟨i, rfl⟩
      · rw [hrightFirst]
        simpa only [jf, hend] using (hT epsilon).2.1
      · rw [hrightNew]
        simpa only [jn, hn i, Function.comp_def] using (hSproj epsilon i).2.2.1
    · intro j
      rcases hocover j with rfl | ⟨i, rfl⟩
      · rw [hleftLast]
        exact hfix.symm
      · rw [hleftOld]
        exact (hjoinOld i).symm
    · intro j
      rcases hncover j with rfl | ⟨i, rfl⟩
      · rw [hrightFirst]
        exact hjoinTail
      · rw [hrightNew]
        exact hjoinNew i
    · rw [hleftLast]
      exact fun _ _ => rfl
    · intro i
      rw [hleftOld]
      exact fun _ _ => rfl
    · intro i
      rw [hrightNew]
      exact fun _ _ => rfl
  have hmin := H.isLocalMin_collar_action_of_action_minimum first last hle hv hupper hpast
    gamma lo hi left (fun epsilon j => ordinary j epsilon) right hbounds hcenter hminimum
    W F DS SS hold hnew (fun epsilon i => survivor i epsilon) hSS hcross
    hclockS hmetricOld hmetricNew hlocal
  have haction (epsilon : ℝ) :
      (∑ j : J, H.stageRegularizedAction j.val T (ordinary j epsilon) (lo j) (hi j)) +
          (∑ i : E, lRegularizedAction (SS i) T (survivor i epsilon) (hi (jn i)) (lo (jo i))) +
          H.stageRegularizedAction first T (right epsilon jf) (hi jf) v =
        (∑ j : J, lRegularizedAction (SO j) T (ordinary j epsilon) (lo j) (hi j)) +
          (∑ i : E, lRegularizedAction (SS i) T (survivor i epsilon) (hi (jn i)) (lo (jo i))) +
          lRegularizedAction ST T (tail epsilon) (hi jf) v := by
    rw [hrightFirst, (hT epsilon).2.2]
    congr 2
    exact Finset.sum_congr rfl (fun j _ => (hO epsilon j).2.2)
  change ∀ᶠ epsilon in 𝓝 (0 : ℝ), _ ≤ _
  filter_upwards [hmin] with epsilon he
  exact (haction 0).symm.le.trans (he.trans (haction epsilon).le)

private def interleavedPieceEquiv (N : ℕ) :
    (Fin (N + 1) ⊕ (Fin N ⊕ Fin 1)) ≃ Fin (2 * N + 2) := by
  let f : (Fin (N + 1) ⊕ (Fin N ⊕ Fin 1)) → Fin (2 * N + 2)
    | .inl k => ⟨2 * k.val, by omega⟩
    | .inr (.inl k) => ⟨2 * k.val + 1, by omega⟩
    | .inr (.inr _) => ⟨2 * N + 1, by omega⟩
  apply Equiv.ofBijective f
  constructor
  · intro x y h
    have hv := congrArg Fin.val h
    rcases x with k | (k | k) <;> rcases y with l | (l | l)
    all_goals simp only [f] at hv
    all_goals simp only [Sum.inl.injEq, Sum.inr.injEq, Sum.inl_ne_inr, Sum.inr_ne_inl]
    all_goals first | apply Fin.ext; omega | exact Subsingleton.elim _ _ | omega
  · intro i
    by_cases hi : i.val = 2 * N + 1
    · exact ⟨.inr (.inr 0), Fin.ext hi.symm⟩
    · rcases Nat.mod_two_eq_zero_or_one i.val with h | h
      · refine ⟨.inl ⟨i.val / 2, by omega⟩, ?_⟩
        apply Fin.ext
        dsimp only [f]
        omega
      · refine ⟨.inr (.inl ⟨i.val / 2, by omega⟩), ?_⟩
        apply Fin.ext
        dsimp only [f]
        omega

private theorem interleavedPieceEquiv_values (N : ℕ) :
    (∀ k : Fin (N + 1), interleavedPieceEquiv N (.inl k) =
      ⟨2 * k.val, by omega⟩) ∧
    (∀ k : Fin N, interleavedPieceEquiv N (.inr (.inl k)) =
      ⟨2 * k.val + 1, by omega⟩) ∧
    interleavedPieceEquiv N (.inr (.inr 0)) = Fin.last (2 * N + 1) := by
  exact ⟨fun _ => rfl, fun _ => rfl, rfl⟩

section Carrier

variable (H : ObservedHistory.{u}) (first last : Fin (H.eventCount + 1)) {N : ℕ}
variable (j : Fin (N + 1) ≃ H.StageInterval first last)
variable (e : Fin N ≃ {i : Fin H.eventCount // first ≤ i.castSucc ∧ i.succ ≤ last})
variable (W : (k : Fin N) → TopologicalSpace.Opens (H.event (e k).val).incoming.terminalRegularOpen)

private abbrev ActualPieceCarrier : (Fin (N + 1) ⊕ (Fin N ⊕ Fin 1)) → Type u :=
  Sum.elim (fun k => (H.stage (j k).val).Carrier)
    (Sum.elim (fun k => W k) (fun _ => (H.stage first).Carrier))

private instance actualPieceTop (k) : TopologicalSpace (ActualPieceCarrier H first last j e W k) := by
  rcases k with k | (k | k) <;> dsimp only [ActualPieceCarrier, Sum.elim] <;> infer_instance

private instance actualPieceChart (k) : ChartedSpace ThreeSpace
    (ActualPieceCarrier H first last j e W k) := by
  rcases k with k | (k | k) <;> dsimp only [ActualPieceCarrier, actualPieceTop, Sum.elim] <;>
    infer_instance

private instance actualPieceManifold (k) : IsManifold ThreeModel ∞
    (ActualPieceCarrier H first last j e W k) := by
  rcases k with k | (k | k) <;>
    dsimp only [ActualPieceCarrier, actualPieceTop, actualPieceChart, Sum.elim] <;> infer_instance

private instance actualPieceT2 (k) : T2Space (ActualPieceCarrier H first last j e W k) := by
  rcases k with k | (k | k) <;> dsimp only [ActualPieceCarrier, actualPieceTop, Sum.elim] <;>
    infer_instance

end Carrier

private theorem interleaved_actual_flow_variations
    (H : ObservedHistory.{u}) (first last : Fin (H.eventCount + 1)) {N : ℕ}
    (j : Fin (N + 1) ≃ H.StageInterval first last)
    (e : Fin N ≃ {i : Fin H.eventCount // first ≤ i.castSucc ∧ i.succ ≤ last})
    (W : (k : Fin N) → TopologicalSpace.Opens (H.event (e k).val).incoming.terminalRegularOpen)
    (DO : Fin (N + 1) → RealTimeInterval) (DS : Fin N → RealTimeInterval)
    (DT : RealTimeInterval)
    (SO : (k : Fin (N + 1)) →
      SolutionOn (I := ThreeModel) (M := (H.stage (j k).val).Carrier) (DO k))
    (SS : (k : Fin N) → SolutionOn (I := ThreeModel) (M := W k) (DS k))
    (ST : SolutionOn (I := ThreeModel) (M := (H.stage first).Carrier) DT)
    (hSO : ∀ k, IsSolutionOn (SO k)) (hSS : ∀ k, IsSolutionOn (SS k)) (hST : IsSolutionOn ST)
    (alphaO : (k : Fin (N + 1)) → ℝ → (H.stage (j k).val).Carrier)
    (alphaS : (k : Fin N) → ℝ → W k) (alphaT : ℝ → (H.stage first).Carrier)
    (T : ℝ) (s : Fin (2 * N + 3) → ℝ) :
    let K := Fin (N + 1) ⊕ (Fin N ⊕ Fin 1);
    let M0 : K → Type u := ActualPieceCarrier H first last j e W;
    let D0 : K → RealTimeInterval := Sum.elim DO (Sum.elim DS (fun _ => DT));
    let S0 : (k : K) → SolutionOn (I := ThreeModel) (M := M0 k) (D0 k) :=
      Sum.rec (fun k => SO k) (Sum.rec (fun k => SS k) (fun _ => ST));
    let alpha0 : (k : K) → ℝ → M0 k :=
      Sum.rec (fun k => alphaO k) (Sum.rec (fun k => alphaS k) (fun _ => alphaT));
    let q := interleavedPieceEquiv N;
    let M : Fin (2 * N + 2) → Type u := fun i => M0 (q.symm i);
    let D : Fin (2 * N + 2) → RealTimeInterval := fun i => D0 (q.symm i);
    let S : (i : Fin (2 * N + 2)) → SolutionOn (I := ThreeModel) (M := M i) (D i) :=
      fun i => S0 (q.symm i);
    let alpha : (i : Fin (2 * N + 2)) → ℝ → M i := fun i => alpha0 (q.symm i);
    (∀ i, IsSolutionOn (S i)) ∧
    (∀ k, HEq (S (q (.inl k))) (SO k)) ∧
    (∀ k, HEq (S (q (.inr (.inl k)))) (SS k)) ∧
    HEq (S (Fin.last (2 * N + 1))) ST ∧
    ∀ f : (i : Fin (2 * N + 2)) → ℝ → ℝ → M i,
      let g := (Equiv.piCongrLeft' (fun k => ℝ → ℝ → M0 k) q).symm f;
      (∀ i epsilon r, f i epsilon r = g (q.symm i) epsilon r) ∧
      ((∀ i, IsSmoothVariation (I := ThreeModel) (f i)) →
        (∀ k, IsSmoothVariation (I := ThreeModel) (g (.inl k))) ∧
        (∀ k, IsSmoothVariation (I := ThreeModel) (g (.inr (.inl k)))) ∧
        IsSmoothVariation (I := ThreeModel) (g (.inr (.inr 0)))) ∧
      ((∀ i r, r ∈ Icc (s i.castSucc) (s i.succ) → f i 0 =ᶠ[𝓝 r] alpha i) →
        (∀ k r, r ∈ Icc (s (q (.inl k)).castSucc) (s (q (.inl k)).succ) →
          g (.inl k) 0 =ᶠ[𝓝 r] alphaO k) ∧
        (∀ k r, r ∈ Icc (s (q (.inr (.inl k))).castSucc)
          (s (q (.inr (.inl k))).succ) → g (.inr (.inl k)) 0 =ᶠ[𝓝 r] alphaS k) ∧
        (∀ r ∈ Icc (s ⟨2 * N + 1, by omega⟩) (s (Fin.last (2 * N + 2))),
          g (.inr (.inr 0)) 0 =ᶠ[𝓝 r] alphaT)) ∧
      (∀ (weight : ℝ → ℝ) (epsilon : ℝ),
        (∑ i, ∫ r in (s i.castSucc)..(s i.succ),
          weight r * lRegularizedLagrangian (S i) T (f i epsilon) r) =
        (∑ k, ∫ r in (s (q (.inl k)).castSucc)..(s (q (.inl k)).succ),
          weight r * lRegularizedLagrangian (SO k) T (g (.inl k) epsilon) r) +
        (∑ k, ∫ r in (s (q (.inr (.inl k))).castSucc)..(s (q (.inr (.inl k))).succ),
          weight r * lRegularizedLagrangian (SS k) T (g (.inr (.inl k)) epsilon) r) +
        ∫ r in (s ⟨2 * N + 1, by omega⟩)..(s (Fin.last (2 * N + 2))),
          weight r * lRegularizedLagrangian ST T (g (.inr (.inr 0)) epsilon) r) ∧
      (∀ epsilon : ℝ,
        (∑ i, lRegularizedAction (S i) T (f i epsilon) (s i.castSucc) (s i.succ)) =
        (∑ k, lRegularizedAction (SO k) T (g (.inl k) epsilon)
          (s (q (.inl k)).castSucc) (s (q (.inl k)).succ)) +
        (∑ k, lRegularizedAction (SS k) T (g (.inr (.inl k)) epsilon)
          (s (q (.inr (.inl k))).castSucc) (s (q (.inr (.inl k))).succ)) +
        lRegularizedAction ST T (g (.inr (.inr 0)) epsilon)
          (s ⟨2 * N + 1, by omega⟩) (s (Fin.last (2 * N + 2)))) := by
  intro K M0 D0 S0 alpha0 q M D S alpha
  have hS0 (k : K) : IsSolutionOn (S0 k) := by
    rcases k with k | (k | k)
    · exact hSO k
    · exact hSS k
    · exact hST
  have hflow (k : K) : HEq (S (q k)) (S0 k) :=
    congr_arg_heq S0 (q.symm_apply_apply k)
  have hlast : q (.inr (.inr 0)) = Fin.last (2 * N + 1) :=
    (interleavedPieceEquiv_values N).2.2
  have hlastLeft : (Fin.last (2 * N + 1)).castSucc =
      (⟨2 * N + 1, by omega⟩ : Fin (2 * N + 3)) := rfl
  have hlastRight : (Fin.last (2 * N + 1)).succ = Fin.last (2 * N + 2) := rfl
  refine ⟨fun i => hS0 _, fun k => hflow (.inl k),
    fun k => hflow (.inr (.inl k)), ?_, ?_⟩
  · exact (congr_arg_heq S hlast.symm).trans (hflow (.inr (.inr 0)))
  intro f g
  have hg (i : Fin (2 * N + 2)) : g (q.symm i) = f i :=
    Equiv.piCongrLeft'_symm_apply_apply _ _ _ _
  have hweight (weight : ℝ → ℝ) (epsilon : ℝ) := by
    let A : K → ℝ := fun k => ∫ r in (s (q k).castSucc)..(s (q k).succ),
      weight r * lRegularizedLagrangian (S0 k) T (g k epsilon) r
    have heq : (∑ i, ∫ r in (s i.castSucc)..(s i.succ),
        weight r * lRegularizedLagrangian (S i) T (f i epsilon) r) = ∑ k, A k := by
      rw [← q.symm.sum_comp A]
      apply Finset.sum_congr rfl
      intro i _
      simp only [A, q.apply_symm_apply, hg]
      rfl
    have hsplit := heq.trans (Fintype.sum_sum_type A)
    simpa only [A, Fintype.sum_sum_type, Fin.sum_univ_one, hlast, add_assoc] using hsplit
  refine ⟨fun i epsilon r => congrFun (congrFun (hg i).symm epsilon) r, ?_, ?_, ?_, ?_⟩
  · intro hf
    have hgSmooth (k : K) : IsSmoothVariation (I := ThreeModel) (g k) := by
      obtain ⟨i, rfl⟩ := q.symm.surjective k
      rw [hg]
      exact hf i
    exact ⟨fun k => hgSmooth (.inl k), fun k => hgSmooth (.inr (.inl k)),
      hgSmooth (.inr (.inr 0))⟩
  · intro hf
    have hgCenter (k : K) (r : ℝ)
        (hr : r ∈ Icc (s (q k).castSucc) (s (q k).succ)) :
        g k 0 =ᶠ[𝓝 r] alpha0 k := by
      obtain ⟨i, rfl⟩ := q.symm.surjective k
      rw [hg]
      exact hf i r (by simpa only [q.apply_symm_apply] using hr)
    refine ⟨fun k r hr => hgCenter (.inl k) r hr,
      fun k r hr => hgCenter (.inr (.inl k)) r hr, ?_⟩
    intro r hr
    exact hgCenter (.inr (.inr 0)) r (by simpa only [hlast, hlastLeft, hlastRight] using hr)
  · intro weight epsilon
    convert hweight weight epsilon using 1
    simp only [S0, hlastLeft, hlastRight, ← add_assoc]
    rfl
  · intro epsilon
    convert hweight (fun _ => 1) epsilon using 1 <;>
      simp only [S0, lRegularizedAction, one_mul, hlastLeft, hlastRight, ← add_assoc]
    rfl

private def interleavedJoinEquiv (N : ℕ) :
    (Fin N ⊕ (Fin N ⊕ Fin 1)) ≃ Fin (2 * N + 1) := by
  let f : (Fin N ⊕ (Fin N ⊕ Fin 1)) → Fin (2 * N + 1)
    | .inl k => ⟨2 * k.val, by omega⟩
    | .inr (.inl k) => ⟨2 * k.val + 1, by omega⟩
    | .inr (.inr _) => ⟨2 * N, by omega⟩
  apply Equiv.ofBijective f
  constructor
  · intro x y h
    have hv := congrArg Fin.val h
    rcases x with k | (k | k) <;> rcases y with l | (l | l)
    all_goals simp only [f] at hv
    all_goals simp only [Sum.inl.injEq, Sum.inr.injEq, Sum.inl_ne_inr, Sum.inr_ne_inl]
    all_goals first | apply Fin.ext; omega | exact Subsingleton.elim _ _ | omega
  · intro i
    by_cases hi : i.val = 2 * N
    · exact ⟨.inr (.inr 0), Fin.ext hi.symm⟩
    · rcases Nat.mod_two_eq_zero_or_one i.val with h | h
      · refine ⟨.inl ⟨i.val / 2, by omega⟩, ?_⟩
        apply Fin.ext
        dsimp only [f]
        omega
      · refine ⟨.inr (.inl ⟨i.val / 2, by omega⟩), ?_⟩
        apply Fin.ext
        dsimp only [f]
        omega

private theorem interleavedJoinEquiv_values (N : ℕ) :
    let L : (Fin N ⊕ (Fin N ⊕ Fin 1)) → (Fin (N + 1) ⊕ (Fin N ⊕ Fin 1)) :=
      Sum.elim (fun k => .inl k.castSucc)
        (Sum.elim (fun k => .inr (.inl k)) (fun _ => .inl (Fin.last N)));
    let R : (Fin N ⊕ (Fin N ⊕ Fin 1)) → (Fin (N + 1) ⊕ (Fin N ⊕ Fin 1)) :=
      Sum.elim (fun k => .inr (.inl k))
        (Sum.elim (fun k => .inl k.succ) (fun k => .inr (.inr k)));
    (∀ k : Fin N, interleavedJoinEquiv N (.inl k) = ⟨2 * k.val, by omega⟩) ∧
    (∀ k : Fin N, interleavedJoinEquiv N (.inr (.inl k)) = ⟨2 * k.val + 1, by omega⟩) ∧
    interleavedJoinEquiv N (.inr (.inr 0)) = Fin.last (2 * N) ∧
    (∀ k, interleavedPieceEquiv N (L k) = (interleavedJoinEquiv N k).castSucc) ∧
    (∀ k, interleavedPieceEquiv N (R k) = (interleavedJoinEquiv N k).succ) := by
  intro L R
  refine ⟨fun _ => rfl, fun _ => rfl, rfl, ?_, ?_⟩
  · intro k
    rcases k with k | (k | k) <;> rfl
  · intro k
    rcases k with k | (k | k)
    · rfl
    · apply Fin.ext
      change 2 * (k.val + 1) = 2 * k.val + 1 + 1
      omega
    · rfl

private theorem exists_stage_identity_join
    (H : ObservedHistory.{u}) (j k : Fin (H.eventCount + 1)) (hjk : j = k)
    {DJ DK : RealTimeInterval}
    (SJ : SolutionOn (I := ThreeModel) (M := (H.stage j).Carrier) DJ)
    (SK : SolutionOn (I := ThreeModel) (M := (H.stage k).Carrier) DK)
    (hJ : ∀ t, SJ.base.metric t = H.stageMetric j t)
    (hK : ∀ t, SK.base.metric t = H.stageMetric k t)
    (alpha : ℝ → (H.stage j).Carrier) (beta : ℝ → (H.stage k).Carrier)
    (T r : ℝ) (hcurve : (hjk ▸ alpha) =ᶠ[𝓝 r] beta) :
    ∃ F : PartialDiffeomorph ThreeModel ThreeModel (H.stage j).Carrier (H.stage k).Carrier ∞,
      F.source = univ ∧ (∀ x, HEq (F x) x) ∧
      alpha r ∈ F.source ∧ F (alpha r) = beta r ∧ F ∘ alpha =ᶠ[𝓝 r] beta ∧
      (∀ x ∈ F.source, ∀ V W : TangentSpace ThreeModel x,
        (SJ.base.metric (T - r ^ 2)).inner x V W =
          (SK.base.metric (T - r ^ 2)).inner (F x)
            (mfderiv ThreeModel ThreeModel (F : (H.stage j).Carrier → (H.stage k).Carrier) x V)
            (mfderiv ThreeModel ThreeModel (F : (H.stage j).Carrier → (H.stage k).Carrier) x W)) ∧
      (mfderiv ThreeModel ThreeModel (F : (H.stage j).Carrier → (H.stage k).Carrier) (alpha r)
        (lVelocity (I := ThreeModel) alpha r) : ThreeSpace) = lVelocity (I := ThreeModel) beta r ∧
      SJ.scalar (T - r ^ 2) (alpha r) = SK.scalar (T - r ^ 2) (beta r) ∧
      lRegularizedLagrangian SJ T alpha r = lRegularizedLagrangian SK T beta r := by
  subst k
  change alpha =ᶠ[𝓝 r] beta at hcurve
  let F := (Diffeomorph.refl ThreeModel (H.stage j).Carrier ∞).toPartialDiffeomorph
  have hcoe : (F : (H.stage j).Carrier → (H.stage j).Carrier) = id := rfl
  have hmetric (t : ℝ) : SJ.base.metric t = SK.base.metric t := (hJ t).trans (hK t).symm
  have hvel : lVelocity (I := ThreeModel) alpha r = lVelocity (I := ThreeModel) beta r := by
    unfold lVelocity
    rw [hcurve.mfderiv_eq]
    rfl
  refine ⟨F, rfl, fun _ => HEq.rfl, mem_univ _, hcurve.self_of_nhds, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [hcoe, Function.id_comp] using hcurve
  · intro x _ V W
    rw [hcoe, mfderiv_id]
    simpa only [ContinuousLinearMap.id_apply, id_eq] using
      congrArg (fun g => g.inner x V W) (hmetric (T - r ^ 2))
  · rw [hcoe, mfderiv_id]
    exact hvel
  · change metricScalarAt (SJ.base.metric (T - r ^ 2)) (alpha r) =
      metricScalarAt (SK.base.metric (T - r ^ 2)) (beta r)
    rw [hmetric, hcurve.self_of_nhds]
  · simp only [lRegularizedLagrangian, SolutionOn.scalar, SolutionFamily.scalar,
      hmetric, hvel, hcurve.self_of_nhds]
    exact congrArg (fun x =>
      (1 / 2 : ℝ) * (SK.base.metric (T - r ^ 2)).inner x
        (lVelocity (I := ThreeModel) beta r) (lVelocity (I := ThreeModel) beta r) +
      2 * r ^ 2 * metricScalarAt (SK.base.metric (T - r ^ 2)) (beta r)) hcurve.self_of_nhds

private theorem exists_interleaved_actual_joins
    (H : ObservedHistory.{u}) (first last : Fin (H.eventCount + 1)) {N : ℕ}
    (j : Fin (N + 1) ≃ H.StageInterval first last)
    (e : Fin N ≃ {i : Fin H.eventCount // first ≤ i.castSucc ∧ i.succ ≤ last})
    (hfirst : (j (Fin.last N)).val = first)
    (W : (k : Fin N) → TopologicalSpace.Opens (H.event (e k).val).incoming.terminalRegularOpen)
    (DO : Fin (N + 1) → RealTimeInterval) (DS : Fin N → RealTimeInterval)
    (DT : RealTimeInterval)
    (SO : (k : Fin (N + 1)) →
      SolutionOn (I := ThreeModel) (M := (H.stage (j k).val).Carrier) (DO k))
    (SS : (k : Fin N) → SolutionOn (I := ThreeModel) (M := W k) (DS k))
    (ST : SolutionOn (I := ThreeModel) (M := (H.stage first).Carrier) DT)
    (hmetricO : ∀ t, (SO (Fin.last N)).base.metric t = H.stageMetric (j (Fin.last N)).val t)
    (hmetricT : ∀ t, ST.base.metric t = H.stageMetric first t)
    (alphaO : (k : Fin (N + 1)) → ℝ → (H.stage (j k).val).Carrier)
    (alphaS : (k : Fin N) → ℝ → W k) (alphaT : ℝ → (H.stage first).Carrier)
    (T : ℝ) (s : Fin (2 * N + 3) → ℝ)
    (Fn : (k : Fin N) → PartialDiffeomorph ThreeModel ThreeModel (W k)
      (H.stage (j k.castSucc).val).Carrier ∞)
    (Fo : (k : Fin N) → PartialDiffeomorph ThreeModel ThreeModel (W k)
      (H.stage (j k.succ).val).Carrier ∞)
    (newProjection : (k : Fin N) → W k → (H.stage (j k.castSucc).val).Carrier)
    (oldProjection : (k : Fin N) → W k → (H.stage (j k.succ).val).Carrier)
    (hnewMap : ∀ k, EqOn (newProjection k) (Fn k) (Fn k).source)
    (holdMap : ∀ k, EqOn (oldProjection k) (Fo k) (Fo k).source)
    (htail : (hfirst ▸ alphaO (Fin.last N)) =ᶠ[𝓝 (s ⟨2 * N + 1, by omega⟩)] alphaT)
    (hnew : ∀ k : Fin N,
      let c := s ⟨2 * k.val + 1, by omega⟩;
      (alphaO k.castSucc) c ∈ (Fn k).symm.source ∧
      ((Fn k).symm : _ → _) ∘ (alphaO k.castSucc) =ᶠ[𝓝 c] (alphaS k) ∧
      (∀ x ∈ (Fn k).symm.source, ∀ V W : TangentSpace ThreeModel x,
        ((SO k.castSucc).base.metric (T - c ^ 2)).inner x V W =
          ((SS k).base.metric (T - c ^ 2)).inner ((Fn k).symm x)
            (mfderiv ThreeModel ThreeModel ((Fn k).symm : _ → _) x V)
            (mfderiv ThreeModel ThreeModel ((Fn k).symm : _ → _) x W)) ∧
      (mfderiv ThreeModel ThreeModel ((Fn k).symm : _ → _) ((alphaO k.castSucc) c)
        (lVelocity (I := ThreeModel) (alphaO k.castSucc) c) : ThreeSpace) =
          lVelocity (I := ThreeModel) (alphaS k) c ∧
      (SO k.castSucc).scalar (T - c ^ 2) ((alphaO k.castSucc) c) = (SS k).scalar (T - c ^ 2) ((alphaS k) c) ∧
      lRegularizedLagrangian (SO k.castSucc) T (alphaO k.castSucc) c = lRegularizedLagrangian (SS k) T (alphaS k) c)
    (hold : ∀ k : Fin N,
      let d := s ⟨2 * k.val + 2, by omega⟩;
      (alphaS k) d ∈ (Fo k).source ∧
      ((Fo k) : _ → _) ∘ (alphaS k) =ᶠ[𝓝 d] (alphaO k.succ) ∧
      (∀ x ∈ (Fo k).source, ∀ V W : TangentSpace ThreeModel x,
        ((SS k).base.metric (T - d ^ 2)).inner x V W =
          ((SO k.succ).base.metric (T - d ^ 2)).inner ((Fo k) x)
            (mfderiv ThreeModel ThreeModel ((Fo k) : _ → _) x V)
            (mfderiv ThreeModel ThreeModel ((Fo k) : _ → _) x W)) ∧
      (mfderiv ThreeModel ThreeModel ((Fo k) : _ → _) ((alphaS k) d)
        (lVelocity (I := ThreeModel) (alphaS k) d) : ThreeSpace) =
          lVelocity (I := ThreeModel) (alphaO k.succ) d ∧
      (SS k).scalar (T - d ^ 2) ((alphaS k) d) = (SO k.succ).scalar (T - d ^ 2) ((alphaO k.succ) d) ∧
      lRegularizedLagrangian (SS k) T (alphaS k) d = lRegularizedLagrangian (SO k.succ) T (alphaO k.succ) d) :
    let K := Fin (N + 1) ⊕ (Fin N ⊕ Fin 1);
    let M0 : K → Type u := ActualPieceCarrier H first last j e W;
    let D0 : K → RealTimeInterval := Sum.elim DO (Sum.elim DS (fun _ => DT));
    let S0 : (k : K) → SolutionOn (I := ThreeModel) (M := M0 k) (D0 k) :=
      Sum.rec (fun k => SO k) (Sum.rec (fun k => SS k) (fun _ => ST));
    let alpha0 : (k : K) → ℝ → M0 k :=
      Sum.rec (fun k => alphaO k) (Sum.rec (fun k => alphaS k) (fun _ => alphaT));
    let q := interleavedPieceEquiv N;
    let z := interleavedJoinEquiv N;
    let M : Fin (2 * N + 2) → Type u := fun i => M0 (q.symm i);
    let D : Fin (2 * N + 2) → RealTimeInterval := fun i => D0 (q.symm i);
    let S : (i : Fin (2 * N + 2)) → SolutionOn (I := ThreeModel) (M := M i) (D i) :=
      fun i => S0 (q.symm i);
    let alpha : (i : Fin (2 * N + 2)) → ℝ → M i := fun i => alpha0 (q.symm i);
    ∃ F : (i : Fin (2 * N + 1)) →
      PartialDiffeomorph ThreeModel ThreeModel (M i.castSucc) (M i.succ) ∞,
      (∀ i : Fin (2 * N + 1),
        let r := s i.castSucc.succ;
        (alpha i.castSucc) r ∈ (F i).source ∧
      (F i) ((alpha i.castSucc) r) = (alpha i.succ) r ∧
      ((F i) : _ → _) ∘ (alpha i.castSucc) =ᶠ[𝓝 r] (alpha i.succ) ∧
      (∀ x ∈ (F i).source, ∀ V W : TangentSpace ThreeModel x,
        ((S i.castSucc).base.metric (T - r ^ 2)).inner x V W =
          ((S i.succ).base.metric (T - r ^ 2)).inner ((F i) x)
            (mfderiv ThreeModel ThreeModel ((F i) : _ → _) x V)
            (mfderiv ThreeModel ThreeModel ((F i) : _ → _) x W)) ∧
      (mfderiv ThreeModel ThreeModel ((F i) : _ → _) ((alpha i.castSucc) r)
        (lVelocity (I := ThreeModel) (alpha i.castSucc) r) : ThreeSpace) =
          lVelocity (I := ThreeModel) (alpha i.succ) r ∧
      (S i.castSucc).scalar (T - r ^ 2) ((alpha i.castSucc) r) = (S i.succ).scalar (T - r ^ 2) ((alpha i.succ) r) ∧
      lRegularizedLagrangian (S i.castSucc) T (alpha i.castSucc) r = lRegularizedLagrangian (S i.succ) T (alpha i.succ) r) ∧
      (∀ k, HEq (F (z (.inl k))) (Fn k).symm) ∧
      (∀ k, HEq (F (z (.inr (.inl k)))) (Fo k)) ∧
      (∃ FT : PartialDiffeomorph ThreeModel ThreeModel
          (H.stage (j (Fin.last N)).val).Carrier (H.stage first).Carrier ∞,
        FT.source = univ ∧ (∀ x, HEq (FT x) x) ∧ HEq (F (Fin.last (2 * N))) FT) ∧
      (∀ f : (i : Fin (2 * N + 2)) → ℝ → ℝ → M i,
        let g := (Equiv.piCongrLeft' (fun k => ℝ → ℝ → M0 k) q).symm f;
        ∀ epsilon : ℝ,
        (∀ i : Fin (2 * N + 1),
          f i.castSucc epsilon (s i.castSucc.succ) ∈ (F i).source ∧
          F i (f i.castSucc epsilon (s i.castSucc.succ)) =
            f i.succ epsilon (s i.castSucc.succ)) →
        (∀ k : Fin N,
          newProjection k (g (.inr (.inl k)) epsilon (s ⟨2 * k.val + 1, by omega⟩)) =
            g (.inl k.castSucc) epsilon (s ⟨2 * k.val + 1, by omega⟩)) ∧
        (∀ k : Fin N,
          oldProjection k (g (.inr (.inl k)) epsilon (s ⟨2 * k.val + 2, by omega⟩)) =
            g (.inl k.succ) epsilon (s ⟨2 * k.val + 2, by omega⟩)) ∧
        HEq (g (.inl (Fin.last N)) epsilon (s ⟨2 * N + 1, by omega⟩))
          (g (.inr (.inr 0)) epsilon (s ⟨2 * N + 1, by omega⟩))) := by
  intro K M0 D0 S0 alpha0 q z M D S alpha
  let J := Fin N ⊕ (Fin N ⊕ Fin 1)
  let b := s ⟨2 * N + 1, by omega⟩
  obtain ⟨FT, hFTsource, hFTid, hFTmem, hFTpoint, hFTcenter, hFTmetric,
      hFTvelocity, hFTscalar, hFTlag⟩ :=
    H.exists_stage_identity_join (j (Fin.last N)).val first hfirst
      (SO (Fin.last N)) ST hmetricO hmetricT (alphaO (Fin.last N)) alphaT T b htail
  let L : J → K := Sum.elim (fun k => .inl k.castSucc)
    (Sum.elim (fun k => .inr (.inl k)) (fun _ => .inl (Fin.last N)))
  let R : J → K := Sum.elim (fun k => .inr (.inl k))
    (Sum.elim (fun k => .inl k.succ) (fun k => .inr (.inr k)))
  let F0 : (k : J) → PartialDiffeomorph ThreeModel ThreeModel (M0 (L k)) (M0 (R k)) ∞ :=
    Sum.rec (fun k => (Fn k).symm) (Sum.rec (fun k => Fo k) (fun _ => FT))
  let rho (k : J) := s (z k).castSucc.succ
  have hL (k : J) : q (L k) = (z k).castSucc := (interleavedJoinEquiv_values N).2.2.2.1 k
  have hR (k : J) : q (R k) = (z k).succ := (interleavedJoinEquiv_values N).2.2.2.2 k
  have hleft (i : Fin (2 * N + 1)) : q.symm i.castSucc = L (z.symm i) := by
    apply q.injective
    simp only [q.apply_symm_apply, hL, z.apply_symm_apply]
  have hright (i : Fin (2 * N + 1)) : q.symm i.succ = R (z.symm i) := by
    apply q.injective
    simp only [q.apply_symm_apply, hR, z.apply_symm_apply]
  have h0 (k : J) :
      (alpha0 (L k)) (rho k) ∈ (F0 k).source ∧
      ((F0 k) : _ → _) ∘ (alpha0 (L k)) =ᶠ[𝓝 (rho k)] (alpha0 (R k)) ∧
      (∀ x ∈ (F0 k).source, ∀ V W : TangentSpace ThreeModel x,
        ((S0 (L k)).base.metric (T - (rho k) ^ 2)).inner x V W =
          ((S0 (R k)).base.metric (T - (rho k) ^ 2)).inner ((F0 k) x)
            (mfderiv ThreeModel ThreeModel ((F0 k) : _ → _) x V)
            (mfderiv ThreeModel ThreeModel ((F0 k) : _ → _) x W)) ∧
      (mfderiv ThreeModel ThreeModel ((F0 k) : _ → _) ((alpha0 (L k)) (rho k))
        (lVelocity (I := ThreeModel) (alpha0 (L k)) (rho k)) : ThreeSpace) =
          lVelocity (I := ThreeModel) (alpha0 (R k)) (rho k) ∧
      (S0 (L k)).scalar (T - (rho k) ^ 2) ((alpha0 (L k)) (rho k)) = (S0 (R k)).scalar (T - (rho k) ^ 2) ((alpha0 (R k)) (rho k)) ∧
      lRegularizedLagrangian (S0 (L k)) T (alpha0 (L k)) (rho k) = lRegularizedLagrangian (S0 (R k)) T (alpha0 (R k)) (rho k) := by
    rcases k with k | (k | k)
    · exact hnew k
    · exact hold k
    · fin_cases k
      exact ⟨hFTmem, hFTcenter, hFTmetric, hFTvelocity, hFTscalar, hFTlag⟩
  have hex (i : Fin (2 * N + 1)) :
      ∃ Fi : PartialDiffeomorph ThreeModel ThreeModel (M i.castSucc) (M i.succ) ∞,
        HEq Fi (F0 (z.symm i)) ∧
        (let r := s i.castSucc.succ;
          (alpha i.castSucc) r ∈ Fi.source ∧
      Fi ((alpha i.castSucc) r) = (alpha i.succ) r ∧
      (Fi : _ → _) ∘ (alpha i.castSucc) =ᶠ[𝓝 r] (alpha i.succ) ∧
      (∀ x ∈ Fi.source, ∀ V W : TangentSpace ThreeModel x,
        ((S i.castSucc).base.metric (T - r ^ 2)).inner x V W =
          ((S i.succ).base.metric (T - r ^ 2)).inner (Fi x)
            (mfderiv ThreeModel ThreeModel (Fi : _ → _) x V)
            (mfderiv ThreeModel ThreeModel (Fi : _ → _) x W)) ∧
      (mfderiv ThreeModel ThreeModel (Fi : _ → _) ((alpha i.castSucc) r)
        (lVelocity (I := ThreeModel) (alpha i.castSucc) r) : ThreeSpace) =
          lVelocity (I := ThreeModel) (alpha i.succ) r ∧
      (S i.castSucc).scalar (T - r ^ 2) ((alpha i.castSucc) r) = (S i.succ).scalar (T - r ^ 2) ((alpha i.succ) r) ∧
      lRegularizedLagrangian (S i.castSucc) T (alpha i.castSucc) r = lRegularizedLagrangian (S i.succ) T (alpha i.succ) r) := by
    have htransport (kl kr : K) (hl : kl = L (z.symm i)) (hr : kr = R (z.symm i)) :
      ∃ Fi : PartialDiffeomorph ThreeModel ThreeModel (M0 kl) (M0 kr) ∞,
        HEq Fi (F0 (z.symm i)) ∧
        (let r := s i.castSucc.succ;
          (alpha0 kl) r ∈ Fi.source ∧
      Fi ((alpha0 kl) r) = (alpha0 kr) r ∧
      (Fi : _ → _) ∘ (alpha0 kl) =ᶠ[𝓝 r] (alpha0 kr) ∧
      (∀ x ∈ Fi.source, ∀ V W : TangentSpace ThreeModel x,
        ((S0 kl).base.metric (T - r ^ 2)).inner x V W =
          ((S0 kr).base.metric (T - r ^ 2)).inner (Fi x)
            (mfderiv ThreeModel ThreeModel (Fi : _ → _) x V)
            (mfderiv ThreeModel ThreeModel (Fi : _ → _) x W)) ∧
      (mfderiv ThreeModel ThreeModel (Fi : _ → _) ((alpha0 kl) r)
        (lVelocity (I := ThreeModel) (alpha0 kl) r) : ThreeSpace) =
          lVelocity (I := ThreeModel) (alpha0 kr) r ∧
      (S0 kl).scalar (T - r ^ 2) ((alpha0 kl) r) = (S0 kr).scalar (T - r ^ 2) ((alpha0 kr) r) ∧
      lRegularizedLagrangian (S0 kl) T (alpha0 kl) r = lRegularizedLagrangian (S0 kr) T (alpha0 kr) r) := by
      subst kl
      subst kr
      have hi := h0 (z.symm i)
      simp only [rho, z.apply_symm_apply] at hi
      refine ⟨F0 (z.symm i), HEq.rfl, hi.1, hi.2.1.self_of_nhds,
        hi.2.1, hi.2.2.1, ?_, hi.2.2.2.2⟩
      have hv := (h0 (z.symm i)).2.2.2.1
      have hc : rho (z.symm i) = s i.castSucc.succ := by
        simp only [rho, z.apply_symm_apply]
      exact hc ▸ hv
    exact htransport _ _ (hleft i) (hright i)
  choose F hFeq hF using hex
  refine ⟨F, hF, ?_, ?_, ⟨FT, hFTsource, hFTid, ?_⟩, ?_⟩
  · intro k
    exact (hFeq (z (.inl k))).trans (congr_arg_heq F0 (z.symm_apply_apply (.inl k)))
  · intro k
    exact (hFeq (z (.inr (.inl k)))).trans
      (congr_arg_heq F0 (z.symm_apply_apply (.inr (.inl k))))
  · have hz : z (.inr (.inr 0)) = Fin.last (2 * N) :=
      (interleavedJoinEquiv_values N).2.2.1
    exact (congr_arg_heq F hz.symm).trans ((hFeq (z (.inr (.inr 0)))).trans
      (congr_arg_heq F0 (z.symm_apply_apply (.inr (.inr 0)))))
  · intro f g epsilon hf
    have hg (i : Fin (2 * N + 2)) : g (q.symm i) = f i :=
      Equiv.piCongrLeft'_symm_apply_apply _ _ _ _
    have hcompat (k : J) :
        g (L k) epsilon (rho k) ∈ (F0 k).source ∧
        F0 k (g (L k) epsilon (rho k)) = g (R k) epsilon (rho k) := by
      have htransport (kl kr : K) (hl : kl = L k) (hr : kr = R k)
          (G : PartialDiffeomorph ThreeModel ThreeModel (M0 kl) (M0 kr) ∞)
          (hG : HEq G (F0 k))
          (hmem : g kl epsilon (rho k) ∈ G.source)
          (hpoint : G (g kl epsilon (rho k)) = g kr epsilon (rho k)) :
          g (L k) epsilon (rho k) ∈ (F0 k).source ∧
          F0 k (g (L k) epsilon (rho k)) = g (R k) epsilon (rho k) := by
        subst kl
        subst kr
        cases eq_of_heq hG
        exact ⟨hmem, hpoint⟩
      apply htransport _ _
        ((hleft (z k)).trans (congrArg L (z.symm_apply_apply k)))
        ((hright (z k)).trans (congrArg R (z.symm_apply_apply k))) (F (z k))
        ((hFeq (z k)).trans (congr_arg_heq F0 (z.symm_apply_apply k)))
      · simpa only [rho, hg] using (hf (z k)).1
      · simpa only [rho, hg] using (hf (z k)).2
    refine ⟨?_, ?_, ?_⟩
    · intro k
      have hk := hcompat (.inl k)
      have hmem : g (.inr (.inl k)) epsilon (rho (.inl k)) ∈ (Fn k).source :=
        hk.2 ▸ (Fn k).symm.map_source hk.1
      exact (hnewMap k hmem).trans
        ((congrArg (Fn k) hk.2).symm.trans ((Fn k).right_inv hk.1))
    · intro k
      have hk := hcompat (.inr (.inl k))
      exact (holdMap k hk.1).trans hk.2
    · have hk := hcompat (.inr (.inr 0))
      exact (hFTid _).symm.trans (heq_of_eq hk.2)

private theorem interleaved_weighted_trace_bound_of_action_minimum
    (H : ObservedHistory.{u}) (first last : Fin (H.eventCount + 1)) (hle : first ≤ last)
    {T v : ℝ} (hv : 0 ≤ v)
    (hupper : T ∈ Icc (H.time last) (H.stageEndTime last))
    (hpast : T - v ^ 2 ∈ H.stageDomain first) :
    let J := H.StageInterval first last;
    let E := {i : Fin H.eventCount // first ≤ i.castSucc ∧ i.succ ≤ last};
    let jo (i : E) : J := ⟨i.val.castSucc, i.property.1,
      i.val.castSucc_le_succ.trans i.property.2⟩;
    let jn (i : E) : J := ⟨i.val.succ,
      i.property.1.trans i.val.castSucc_le_succ, i.property.2⟩;
    let jf : J := ⟨first, le_rfl, hle⟩;
    let jl : J := ⟨last, hle, le_rfl⟩;
    ∀ (gamma : (j : J) → ℝ → (H.stage j.val).Carrier) (lo hi : J → ℝ),
      (∀ j, H.regularizedStageStart T 0 j.val ≤ lo j ∧ lo j ≤ hi j ∧
        hi j ≤ H.regularizedStageEnd T v j.val) →
      Manifold.absolutelyContinuousOnInterval ThreeModel (gamma jl) 0 (lo jl) →
      IntervalIntegrable (H.stageRegularizedLagrangian last T (gamma jl)) volume 0 (lo jl) →
      (∀ delta : (j : J) → ℝ → (H.stage j.val).Carrier,
        (∀ j, Manifold.absolutelyContinuousOnInterval ThreeModel (delta j)
          (H.regularizedStageStart T 0 j.val) (H.regularizedStageEnd T v j.val)) →
        (∀ j, IntervalIntegrable (H.stageRegularizedLagrangian j.val T (delta j)) volume
          (H.regularizedStageStart T 0 j.val) (H.regularizedStageEnd T v j.val)) →
        delta jl 0 = gamma jl 0 →
        (∀ (i : Fin H.eventCount) (hf : first ≤ i.castSucc) (hl : i.succ ≤ last),
          ∃ z : (H.event i).old,
            z.val.val = delta ⟨i.castSucc, hf, i.castSucc_le_succ.trans hl⟩
              (Real.sqrt (T - H.time i.succ)) ∧
            (H.event i).oldOutput z = delta ⟨i.succ, hf.trans i.castSucc_le_succ, hl⟩
              (Real.sqrt (T - H.time i.succ))) →
        (∑ j : J, H.stageRegularizedAction j.val T (gamma j)
          (H.regularizedStageStart T 0 j.val) (H.regularizedStageEnd T v j.val)) ≤
        (∑ j : J, H.stageRegularizedAction j.val T (delta j)
          (H.regularizedStageStart T 0 j.val) (H.regularizedStageEnd T v j.val))) →
    ∀ {N : ℕ} (j : Fin (N + 1) ≃ J) (e : Fin N ≃ E)
      (_ : j (Fin.last N) = jf) (_ : j 0 = jl)
      (hjn : ∀ k : Fin N, j k.castSucc = jn (e k))
      (hjo : ∀ k : Fin N, j k.succ = jo (e k))
      (W : (i : E) → TopologicalSpace.Opens (H.event i.val).incoming.terminalRegularOpen)
      (FC : (i : E) → PartialDiffeomorph ThreeModel ThreeModel
        (H.event i.val).incoming.terminalRegularOpen (H.stage i.val.succ).Carrier ∞)
      (DO : J → RealTimeInterval) (DS : E → RealTimeInterval) (DT : RealTimeInterval)
      (SO : (x : J) → SolutionOn (I := ThreeModel) (M := (H.stage x.val).Carrier) (DO x))
      (SS : (i : E) → SolutionOn (I := ThreeModel) (M := W i) (DS i))
      (ST : SolutionOn (I := ThreeModel) (M := (H.stage first).Carrier) DT)
      (hold : ∀ i, IsLocalDiffeomorph ThreeModel ThreeModel ∞ (fun z : W i => z.val.val))
      (hnew : ∀ i, IsLocalDiffeomorph ThreeModel ThreeModel ∞ (fun z : W i => FC i z.val))
      (alphaO : (x : J) → ℝ → (H.stage x.val).Carrier)
      (alphaS : (i : E) → ℝ → W i) (alphaT : ℝ → (H.stage first).Carrier)
      (s : Fin (2 * N + 3) → ℝ),
      (∀ x, IsSolutionOn (SO x)) → (∀ i, IsSolutionOn (SS i)) → IsSolutionOn ST →
      (∀ x t, (SO x).base.metric t = H.stageMetric x.val t) →
      (∀ t, ST.base.metric t = H.stageMetric first t) →
      (∀ i z, (H.event i.val).RegularCrossing (z : W i).val.val (FC i z.val)) →
      (∀ i, ∀ r ∈ Ioo (Real.sqrt (T - H.time i.val.succ)) (lo (jo i)),
        (SS i).base.metric (T - r ^ 2) =
          localPullMetric (H.stageMetric i.val.castSucc (T - r ^ 2))
            (fun z : W i => z.val.val) (hold i)) →
      (∀ i, ∀ r ∈ Ioo (hi (jn i)) (Real.sqrt (T - H.time i.val.succ)),
        (SS i).base.metric (T - r ^ 2) =
          localPullMetric (H.stageMetric i.val.succ (T - r ^ 2))
            (fun z : W i => FC i z.val) (hnew i)) →
      (∀ x, ContMDiff 𝓘(ℝ, ℝ) ThreeModel ∞ (alphaO x)) →
      (∀ i, ContMDiff 𝓘(ℝ, ℝ) ThreeModel ∞ (alphaS i)) →
      ContMDiff 𝓘(ℝ, ℝ) ThreeModel ∞ alphaT →
      (∀ x, IsLRegularizedGeodesicOn (SO x) T (alphaO x) (Icc (lo x) (hi x))) →
      (∀ i, IsLRegularizedGeodesicOn (SS i) T (alphaS i) (Icc (hi (jn i)) (lo (jo i)))) →
      IsLRegularizedGeodesicOn ST T alphaT (Icc (hi jf) v) →
      (∀ x, EqOn (alphaO x) (gamma x) (Icc (lo x) (hi x))) →
      EqOn alphaT (gamma jf) (Icc (hi jf) v) →
      (∀ i, EqOn (fun r => (alphaS i r).val.val) (gamma (jo i))
        (Icc (Real.sqrt (T - H.time i.val.succ)) (lo (jo i)))) →
      (∀ i, EqOn (fun r => FC i (alphaS i r).val) (gamma (jn i))
        (Icc (hi (jn i)) (Real.sqrt (T - H.time i.val.succ)))) →
      lVelocity (I := ThreeModel) alphaT v = 0 →
      StrictMono s → 0 < s 0 →
    ∀ (_ : ∀ k, s (interleavedPieceEquiv N (.inl k)).castSucc = lo (j k))
      (_ : ∀ k, s (interleavedPieceEquiv N (.inl k)).succ = hi (j k))
      (_ : ∀ k, s (interleavedPieceEquiv N (.inr (.inl k))).castSucc = hi (jn (e k)))
      (_ : ∀ k, s (interleavedPieceEquiv N (.inr (.inl k))).succ = lo (jo (e k)))
      (_ : s (Fin.last (2 * N + 1)).castSucc = hi jf)
      (_ : s (Fin.last (2 * N + 2)) = v)
      (lowO highO : J → ℝ) (lowS highS : E → ℝ) (lowT highT : ℝ),
      (∀ x, lowO x < lo x ∧ hi x < highO x) →
      (∀ i, lowS i < hi (jn i) ∧ lo (jo i) < highS i) →
      lowT < hi jf → v < highT →
      (∀ (x : J) (r : ℝ), r ∈ Ioo (lowO x) (highO x) → T - r ^ 2 ∈ (DO x).regular) →
      (∀ (i : E) (r : ℝ), r ∈ Ioo (lowS i) (highS i) → T - r ^ 2 ∈ (DS i).regular) →
      (∀ (r : ℝ), r ∈ Ioo lowT highT → T - r ^ 2 ∈ DT.regular) →
    ∀ (Fn : (k : Fin N) → PartialDiffeomorph ThreeModel ThreeModel (W (e k))
        (H.stage (j k.castSucc).val).Carrier ∞)
      (Fo : (k : Fin N) → PartialDiffeomorph ThreeModel ThreeModel (W (e k))
        (H.stage (j k.succ).val).Carrier ∞),
      (∀ k, EqOn (fun z : W (e k) => cast (congrArg (fun x : J => (H.stage x.val).Carrier) (hjn k).symm) (FC (e k) z.val)) (Fn k) (Fn k).source) →
      (∀ k, EqOn (fun z : W (e k) => cast (congrArg (fun x : J => (H.stage x.val).Carrier) (hjo k).symm) z.val.val) (Fo k) (Fo k).source) →
      alphaO jf =ᶠ[𝓝 (hi jf)] alphaT →
    ∀ (_ : ∀ k : Fin N,
      let c := s (interleavedPieceEquiv N (.inr (.inl k))).castSucc;
      (alphaO (j k.castSucc)) c ∈ (Fn k).symm.source ∧
      ((Fn k).symm : _ → _) ∘ (alphaO (j k.castSucc)) =ᶠ[𝓝 c] (alphaS (e k)) ∧
      (∀ x ∈ (Fn k).symm.source, ∀ V W : TangentSpace ThreeModel x,
        ((SO (j k.castSucc)).base.metric (T - c ^ 2)).inner x V W =
          ((SS (e k)).base.metric (T - c ^ 2)).inner ((Fn k).symm x)
            (mfderiv ThreeModel ThreeModel ((Fn k).symm : _ → _) x V)
            (mfderiv ThreeModel ThreeModel ((Fn k).symm : _ → _) x W)) ∧
      (mfderiv ThreeModel ThreeModel ((Fn k).symm : _ → _) ((alphaO (j k.castSucc)) c)
        (lVelocity (I := ThreeModel) (alphaO (j k.castSucc)) c) : ThreeSpace) =
          lVelocity (I := ThreeModel) (alphaS (e k)) c ∧
      (SO (j k.castSucc)).scalar (T - c ^ 2) ((alphaO (j k.castSucc)) c) = (SS (e k)).scalar (T - c ^ 2) ((alphaS (e k)) c) ∧
      lRegularizedLagrangian (SO (j k.castSucc)) T (alphaO (j k.castSucc)) c = lRegularizedLagrangian (SS (e k)) T (alphaS (e k)) c)
    (_ : ∀ k : Fin N,
      let d := s (interleavedPieceEquiv N (.inr (.inl k))).succ;
      (alphaS (e k)) d ∈ (Fo k).source ∧
      ((Fo k) : _ → _) ∘ (alphaS (e k)) =ᶠ[𝓝 d] (alphaO (j k.succ)) ∧
      (∀ x ∈ (Fo k).source, ∀ V W : TangentSpace ThreeModel x,
        ((SS (e k)).base.metric (T - d ^ 2)).inner x V W =
          ((SO (j k.succ)).base.metric (T - d ^ 2)).inner ((Fo k) x)
            (mfderiv ThreeModel ThreeModel ((Fo k) : _ → _) x V)
            (mfderiv ThreeModel ThreeModel ((Fo k) : _ → _) x W)) ∧
      (mfderiv ThreeModel ThreeModel ((Fo k) : _ → _) ((alphaS (e k)) d)
        (lVelocity (I := ThreeModel) (alphaS (e k)) d) : ThreeSpace) =
          lVelocity (I := ThreeModel) (alphaO (j k.succ)) d ∧
      (SS (e k)).scalar (T - d ^ 2) ((alphaS (e k)) d) = (SO (j k.succ)).scalar (T - d ^ 2) ((alphaO (j k.succ)) d) ∧
      lRegularizedLagrangian (SS (e k)) T (alphaS (e k)) d = lRegularizedLagrangian (SO (j k.succ)) T (alphaO (j k.succ)) d),
      (∑ x : J, ∫ r in lo x..hi x,
        (1 - (s 0) ^ 2 / r ^ 2) * lRegularizedLagrangian (SO x) T (alphaO x) r) +
      (∑ i : E, ∫ r in hi (jn i)..lo (jo i),
        (1 - (s 0) ^ 2 / r ^ 2) * lRegularizedLagrangian (SS i) T (alphaS i) r) +
      (∫ r in hi jf..v, (1 - (s 0) ^ 2 / r ^ 2) * lRegularizedLagrangian ST T alphaT r) +
      2 * v * ST.scalar (T - v ^ 2) (alphaT v) * (v - s 0) ^ 2 ≤ 6 * (v - s 0) := by
  classical
  intro J E jo jn jf jl gamma lo hi hbounds hprefixAC hprefixInt hminimum
    N j e hfirst hlast hjn hjo W FC DO DS DT SO SS ST hold hnew alphaO alphaS alphaT s
    hSO hSS hST hmetricO hmetricT hcross hmetricOld hmetricNew hsmO hsmS hsmT
    hgeoO hgeoS hgeoT hcenterO hcenterT hcenterOld hcenterNew hfinal hs ha
    hOL hOR hSL hSR hTL hEnd lowO highO lowS highS lowT highT
    hmarginO hmarginS hlowT hhighT hregO hregS hregT
    Fn Fo hnewMap holdMap htail hgeomNew hgeomOld
  let q := interleavedPieceEquiv N
  have hOL : ∀ k, s (q (.inl k)).castSucc = lo (j k) := hOL
  have hOR : ∀ k, s (q (.inl k)).succ = hi (j k) := hOR
  have hSL : ∀ k, s (q (.inr (.inl k))).castSucc = hi (jn (e k)) := hSL
  have hSR : ∀ k, s (q (.inr (.inl k))).succ = lo (jo (e k)) := hSR
  have hTLlit : s ⟨2 * N + 1, by omega⟩ = hi jf := hTL
  let newProjection (k : Fin N) (z : W (e k)) : (H.stage (j k.castSucc).val).Carrier :=
      cast (congrArg (fun x : J => (H.stage x.val).Carrier) (hjn k).symm) (FC (e k) z.val)
  let oldProjection (k : Fin N) (z : W (e k)) : (H.stage (j k.succ).val).Carrier :=
      cast (congrArg (fun x : J => (H.stage x.val).Carrier) (hjo k).symm) z.val.val
  let K := Fin (N + 1) ⊕ (Fin N ⊕ Fin 1)
  let M0 : K → Type u := ActualPieceCarrier H first last j e (fun k => W (e k))
  let D0 : K → RealTimeInterval :=
    Sum.elim (fun k => DO (j k)) (Sum.elim (fun k => DS (e k)) (fun _ => DT))
  let S0 : (k : K) → SolutionOn (I := ThreeModel) (M := M0 k) (D0 k) :=
    Sum.rec (fun k => SO (j k)) (Sum.rec (fun k => SS (e k)) (fun _ => ST))
  let alpha0 : (k : K) → ℝ → M0 k :=
    Sum.rec (fun k => alphaO (j k)) (Sum.rec (fun k => alphaS (e k)) (fun _ => alphaT))
  let M : Fin (2 * N + 2) → Type u := fun i => M0 (q.symm i)
  let D : Fin (2 * N + 2) → RealTimeInterval := fun i => D0 (q.symm i)
  let S : (i : Fin (2 * N + 2)) → SolutionOn (I := ThreeModel) (M := M i) (D i) :=
    fun i => S0 (q.symm i)
  let alpha : (i : Fin (2 * N + 2)) → ℝ → M i := fun i => alpha0 (q.symm i)
  have hcarrier := H.interleaved_actual_flow_variations first last j e (fun k => W (e k))
    (fun k => DO (j k)) (fun k => DS (e k)) DT
    (fun k => SO (j k)) (fun k => SS (e k)) ST
    (fun k => hSO (j k)) (fun k => hSS (e k)) hST
    (fun k => alphaO (j k)) (fun k => alphaS (e k)) alphaT T s
  have hjfirst : (j (Fin.last N)).val = first := congrArg Subtype.val hfirst
  obtain ⟨F, hF, _, _, _, hcompat⟩ := H.exists_interleaved_actual_joins first last
    j e hjfirst (fun k => W (e k)) (fun k => DO (j k)) (fun k => DS (e k)) DT
    (fun k => SO (j k)) (fun k => SS (e k)) ST (hmetricO (j (Fin.last N))) hmetricT
    (fun k => alphaO (j k)) (fun k => alphaS (e k)) alphaT T s Fn Fo
    newProjection oldProjection hnewMap holdMap
    (by
      have heq : HEq (hjfirst ▸ alphaO (j (Fin.last N))) (alphaO jf) :=
        eqRec_heq_iff.mpr (congr_arg_heq alphaO hfirst)
      rw [eq_of_heq heq]
      simpa only [hTLlit] using htail) hgeomNew hgeomOld
  have hqTail : q (.inr (.inr 0)) = Fin.last (2 * N + 1) :=
    (interleavedPieceEquiv_values N).2.2
  have hqZero : q (.inl 0) = 0 := rfl
  let low0 : K → ℝ := Sum.elim (fun k => lowO (j k))
    (Sum.elim (fun k => lowS (e k)) (fun _ => lowT))
  let high0 : K → ℝ := Sum.elim (fun k => highO (j k))
    (Sum.elim (fun k => highS (e k)) (fun _ => highT))
  have hsm0 (k : K) : ContMDiff 𝓘(ℝ, ℝ) ThreeModel ∞ (alpha0 k) := by
    rcases k with k | (k | k)
    · exact hsmO (j k)
    · exact hsmS (e k)
    · exact hsmT
  have hlo0 (k : K) : low0 k < s (q k).castSucc := by
    rcases k with k | (k | k)
    · simpa only [low0, Sum.elim, hOL] using (hmarginO (j k)).1
    · simpa only [low0, Sum.elim, hSL] using (hmarginS (e k)).1
    · fin_cases k
      change lowT < s (q (.inr (.inr 0))).castSucc
      rw [hqTail, hTL]
      exact hlowT
  have hhi0 (k : K) : s (q k).succ < high0 k := by
    rcases k with k | (k | k)
    · simpa only [high0, Sum.elim, hOR] using (hmarginO (j k)).2
    · simpa only [high0, Sum.elim, hSR] using (hmarginS (e k)).2
    · fin_cases k
      change s (q (.inr (.inr 0))).succ < highT
      rw [hqTail, Fin.succ_last, hEnd]
      exact hhighT
  have hreg0 (k : K) : ∀ r ∈ Ioo (low0 k) (high0 k), T - r ^ 2 ∈ (D0 k).regular := by
    rcases k with k | (k | k)
    · exact hregO (j k)
    · exact hregS (e k)
    · exact hregT
  have hgeo0 (k : K) : IsLRegularizedGeodesicOn (S0 k) T (alpha0 k)
      (Icc (s (q k).castSucc) (s (q k).succ)) := by
    rcases k with k | (k | k)
    · intro r hr
      rw [hOL, hOR] at hr
      exact hgeoO (j k) r hr
    · intro r hr
      rw [hSL, hSR] at hr
      exact hgeoS (e k) r hr
    · fin_cases k
      change IsLRegularizedGeodesicOn ST T alphaT
        (Icc (s (q (.inr (.inr 0))).castSucc) (s (q (.inr (.inr 0))).succ))
      rw [hqTail, hTL, Fin.succ_last, hEnd]
      exact hgeoT
  have hsmFlat (i) : ContMDiff 𝓘(ℝ, ℝ) ThreeModel ∞ (alpha i) := hsm0 (q.symm i)
  have hloFlat (i) : low0 (q.symm i) < s i.castSucc := by
    simpa only [q.apply_symm_apply] using hlo0 (q.symm i)
  have hhiFlat (i) : s i.succ < high0 (q.symm i) := by
    simpa only [q.apply_symm_apply] using hhi0 (q.symm i)
  have hgeoFlat (i) : IsLRegularizedGeodesicOn (S i) T (alpha i)
      (Icc (s i.castSucc) (s i.succ)) := by
    simpa only [q.apply_symm_apply] using hgeo0 (q.symm i)
  have htailIndex : q.symm (Fin.last (2 * N + 1)) = .inr (.inr 0) := by
    rw [← hqTail, q.symm_apply_apply]
  have hfinalFlat : lVelocity (I := ThreeModel) (alpha (Fin.last (2 * N + 1)))
      (s (Fin.last (2 * N + 2))) = (0 : ThreeSpace) := by
    have hvalue (k : K) (hk : k = .inr (.inr 0)) :
        (lVelocity (I := ThreeModel) (alpha0 k) v : ThreeSpace) = (0 : ThreeSpace) := by
      subst k
      exact hfinal
    rw [hEnd]
    exact hvalue _ htailIndex
  have hupper0 : T - (0 : ℝ) ^ 2 ∈ Icc (H.time last) (H.stageEndTime last) := by
    simpa only [zero_pow two_ne_zero, sub_zero] using hupper
  have ho (i : E) : H.regularizedStageStart T 0 i.val.castSucc =
      Real.sqrt (T - H.time i.val.succ) :=
    H.regularizedStageStart_castSucc_eq_event_clock hupper0 i.val i.property.2
  have hn (i : E) : H.regularizedStageEnd T v i.val.succ =
      Real.sqrt (T - H.time i.val.succ) :=
    H.regularizedStageEnd_succ_eq_event_clock hpast i.val i.property.1
  have hcw (i : E) : hi (jn i) ≤ Real.sqrt (T - H.time i.val.succ) := by
    simpa only [jn, hn i] using (hbounds (jn i)).2.2
  have hwd (i : E) : Real.sqrt (T - H.time i.val.succ) ≤ lo (jo i) := by
    simpa only [jo, ho i] using (hbounds (jo i)).1
  have hminFlat (f : (i : Fin (2 * N + 2)) → ℝ → ℝ → M i)
      (hf : ∀ i, IsSmoothVariation (I := ThreeModel) (f i))
      (hcenter : ∀ i r, r ∈ Icc (s i.castSucc) (s i.succ) → f i 0 =ᶠ[𝓝 r] alpha i)
      (hfix : ∀ᶠ epsilon in 𝓝 (0 : ℝ), f 0 epsilon (s 0) = alpha 0 (s 0))
      (hjoin : ∀ᶠ epsilon in 𝓝 (0 : ℝ), ∀ i : Fin (2 * N + 1),
        f i.castSucc epsilon (s i.castSucc.succ) ∈ (F i).source ∧
        F i (f i.castSucc epsilon (s i.castSucc.succ)) = f i.succ epsilon (s i.castSucc.succ)) :
      IsLocalMin (fun epsilon => ∑ i, lRegularizedAction (S i) T (f i epsilon)
        (s i.castSucc) (s i.succ)) 0 := by
    let g := (Equiv.piCongrLeft' (fun k : K => ℝ → ℝ → M0 k) q).symm f
    obtain ⟨_, hgsmooth, hgcenter, _, hgaction⟩ := hcarrier.2.2.2.2 f
    have hgsm := hgsmooth hf
    have hgc := hgcenter hcenter
    let ordinary := (Equiv.piCongrLeft' (fun x : J => ℝ → ℝ → (H.stage x.val).Carrier)
      j.symm).symm (fun k => g (.inl k))
    let survivor := (Equiv.piCongrLeft' (fun i : E => ℝ → ℝ → W i)
      e.symm).symm (fun k => g (.inr (.inl k)))
    let tail := g (.inr (.inr 0))
    have hOeq (k) : ordinary (j k) = g (.inl k) :=
      Equiv.piCongrLeft'_symm_apply_apply _ _ _ _
    have hSeq (k) : survivor (e k) = g (.inr (.inl k)) :=
      Equiv.piCongrLeft'_symm_apply_apply _ _ _ _
    have hOSmooth (x) : IsSmoothVariation (I := ThreeModel) (ordinary x) := by
      obtain ⟨k, rfl⟩ := j.surjective x
      rw [hOeq]
      exact hgsm.1 k
    have hSSmooth (i) : IsSmoothVariation (I := ThreeModel) (survivor i) := by
      obtain ⟨k, rfl⟩ := e.surjective i
      rw [hSeq]
      exact hgsm.2.1 k
    have hOCenter (x) (r : ℝ) (hr : r ∈ Icc (lo x) (hi x)) :
        ordinary x 0 r = gamma x r := by
      obtain ⟨k, rfl⟩ := j.surjective x
      rw [hOeq]
      exact ((hgc.1 k r (by change r ∈ Icc (s (q (.inl k)).castSucc) (s (q (.inl k)).succ); simpa only [hOL, hOR] using hr)).self_of_nhds).trans (hcenterO _ hr)
    have hSCenter (i) (r : ℝ) (hr : r ∈ Icc (hi (jn i)) (lo (jo i))) :
        survivor i 0 r = alphaS i r := by
      obtain ⟨k, rfl⟩ := e.surjective i
      rw [hSeq]
      exact (hgc.2.1 k r (by change r ∈ Icc (s (q (.inr (.inl k))).castSucc) (s (q (.inr (.inl k))).succ); simpa only [hSL, hSR] using hr)).self_of_nhds
    have hTCenter (r : ℝ) (hr : r ∈ Icc (hi jf) v) : tail 0 r = gamma jf r :=
      (hgc.2.2 r (by simpa only [hTLlit, hEnd] using hr)).self_of_nhds.trans (hcenterT hr)
    have hFirstClock : lo jl = s 0 := by
      simpa only [hlast, hqZero, Fin.castSucc_zero] using (hOL 0).symm
    have hFirstValue (epsilon : ℝ) : HEq (ordinary jl epsilon (lo jl)) (f 0 epsilon (s 0)) := by
      have hidx : q.symm 0 = .inl 0 := by rw [← hqZero, q.symm_apply_apply]
      have heq : g (q.symm 0) epsilon (s 0) = f 0 epsilon (s 0) := by
        have hf0 : g (q.symm 0) = f 0 := Equiv.piCongrLeft'_symm_apply_apply _ _ _ _
        exact congrFun (congrFun hf0 epsilon) (s 0)
      have hpoint := (congr_arg_heq (fun k => g k epsilon (s 0)) hidx.symm).trans (heq_of_eq heq)
      have hOzero : HEq (ordinary jl epsilon (lo jl)) (ordinary (j 0) epsilon (lo jl)) :=
        congr_arg_heq (fun x => ordinary x epsilon (lo jl)) hlast.symm
      rw [hOeq, hFirstClock] at hOzero
      simpa only [hFirstClock] using hOzero.trans hpoint
    have hFirstCenter : HEq (gamma jl (lo jl)) (alpha 0 (s 0)) := by
      have hidx : q.symm 0 = .inl 0 := by rw [← hqZero, q.symm_apply_apply]
      have hleft : HEq (alpha 0 (s 0)) (alphaO (j 0) (s 0)) := by
        change HEq (alpha0 (q.symm 0) (s 0)) _
        exact congr_arg_heq (fun k => alpha0 k (s 0)) hidx
      have hlo : lo jl ≤ hi jl := (hbounds jl).2.1
      have hv := hcenterO jl (left_mem_Icc.mpr hlo)
      have hEq : HEq (gamma jl (lo jl)) (alphaO (j 0) (s 0)) := by
        have hpoint := congr_arg_heq (fun x => alphaO x (lo jl)) hlast.symm
        rw [hFirstClock] at hpoint
        exact (heq_of_eq hv.symm).trans (by simpa only [hFirstClock] using hpoint)
      exact hEq.trans hleft.symm
    have hmatches : ∀ᶠ epsilon in 𝓝 (0 : ℝ),
        ordinary jl epsilon (lo jl) = gamma jl (lo jl) ∧
        (∀ i, ordinary (jo i) epsilon (lo (jo i)) = (survivor i epsilon (lo (jo i))).val.val) ∧
        (∀ i, ordinary (jn i) epsilon (hi (jn i)) = FC i (survivor i epsilon (hi (jn i))).val) ∧
        ordinary jf epsilon (hi jf) = tail epsilon (hi jf) := by
      filter_upwards [hfix, hjoin] with epsilon he hj
      obtain ⟨hN, hO, hT⟩ := hcompat f epsilon hj
      refine ⟨eq_of_heq ((hFirstValue epsilon).trans ((heq_of_eq he).trans hFirstCenter.symm)), ?_, ?_, ?_⟩
      · intro i
        obtain ⟨k, rfl⟩ := e.surjective i
        have hh := (heq_of_eq (hO k)).symm.trans (cast_heq _ _)
        change HEq (g (.inl k.succ) epsilon (s ⟨2 * k.val + 2, by omega⟩))
          ((g (.inr (.inl k)) epsilon (s ⟨2 * k.val + 2, by omega⟩)).val.val) at hh
        have hc : s ⟨2 * k.val + 2, by omega⟩ = lo (jo (e k)) := hSR k
        rw [hc, ← hOeq, ← hSeq] at hh
        exact eq_of_heq ((congr_arg_heq
          (fun x => ordinary x epsilon (lo (jo (e k)))) (hjo k).symm).trans hh)
      · intro i
        obtain ⟨k, rfl⟩ := e.surjective i
        have hh := (heq_of_eq (hN k)).symm.trans (cast_heq _ _)
        change HEq (g (.inl k.castSucc) epsilon (s ⟨2 * k.val + 1, by omega⟩))
          (FC (e k) (g (.inr (.inl k)) epsilon (s ⟨2 * k.val + 1, by omega⟩)).val) at hh
        have hc : s ⟨2 * k.val + 1, by omega⟩ = hi (jn (e k)) := hSL k
        rw [hc, ← hOeq, ← hSeq] at hh
        exact eq_of_heq ((congr_arg_heq
          (fun x => ordinary x epsilon (hi (jn (e k)))) (hjn k).symm).trans hh)
      · have hh := hT
        change HEq (g (.inl (Fin.last N)) epsilon (s ⟨2 * N + 1, by omega⟩))
          (tail epsilon (s ⟨2 * N + 1, by omega⟩)) at hh
        rw [hTLlit, ← hOeq] at hh
        exact eq_of_heq ((congr_arg_heq
          (fun x => ordinary x epsilon (hi jf)) hfirst.symm).trans hh)
    have hm := H.isLocalMin_smooth_piece_action_of_action_minimum first last hle hv hupper hpast
      gamma lo hi hbounds hprefixAC hprefixInt hminimum W FC DO DS DT SO SS ST hold hnew
      ordinary survivor tail hSO hSS hST hmetricO hmetricT
      (fun x r hr => (DO x).regular_subset ((hgeoO x r hr).1))
      (fun r hr => DT.regular_subset ((hgeoT r hr).1)) hcross
      (fun i r hr => (DS i).regular_subset ((hgeoS i r hr).1)) hmetricOld hmetricNew
      hOSmooth hSSmooth hgsm.2.2 hOCenter hTCenter
      (fun i r hr => by dsimp only; rw [hSCenter i r ⟨(hcw i).trans hr.1, hr.2⟩]; exact hcenterOld i hr)
      (fun i r hr => by dsimp only; rw [hSCenter i r ⟨hr.1, hr.2.trans (hwd i)⟩]; exact hcenterNew i hr)
      hmatches
    have haction (epsilon : ℝ) :
        (∑ i, lRegularizedAction (S i) T (f i epsilon) (s i.castSucc) (s i.succ)) =
        (∑ x : J, lRegularizedAction (SO x) T (ordinary x epsilon) (lo x) (hi x)) +
        (∑ i : E, lRegularizedAction (SS i) T (survivor i epsilon) (hi (jn i)) (lo (jo i))) +
        lRegularizedAction ST T (tail epsilon) (hi jf) v := by
      rw [hgaction epsilon]
      simp only [hTLlit, hEnd]
      change
        (∑ k, lRegularizedAction (SO (j k)) T (g (.inl k) epsilon)
          (s (q (.inl k)).castSucc) (s (q (.inl k)).succ)) +
        (∑ k, lRegularizedAction (SS (e k)) T (g (.inr (.inl k)) epsilon)
          (s (q (.inr (.inl k))).castSucc) (s (q (.inr (.inl k))).succ)) +
        lRegularizedAction ST T (tail epsilon) (hi jf) v = _
      simp only [hOL, hOR, hSL, hSR, ← hOeq, ← hSeq]
      exact congrArg₂ (fun a b : ℝ => a + b + lRegularizedAction ST T (tail epsilon) (hi jf) v)
        (j.sum_comp (fun x => lRegularizedAction (SO x) T (ordinary x epsilon) (lo x) (hi x)))
        (e.sum_comp (fun i => lRegularizedAction (SS i) T (survivor i epsilon) (hi (jn i)) (lo (jo i))))
    change ∀ᶠ epsilon in 𝓝 (0 : ℝ), _ ≤ _
    filter_upwards [hm] with epsilon he
    exact (haction 0).le.trans (he.trans (haction epsilon).symm.le)
  have htrace := sum_integral_lRegularizedLagrangian_mul_add_scalar_le_of_variational_minimum
    (n := 2 * N + 1) S hcarrier.1 T alpha hsmFlat s hs ha (fun i => low0 (q.symm i))
    (fun i => high0 (q.symm i)) hloFlat hhiFlat (fun i => hreg0 (q.symm i)) hgeoFlat F
    (fun i => (hF i).1) (fun i => (hF i).2.1)
    (fun i => (hF i).2.2.2.1) (fun i => (hF i).2.2.2.2.1) hfinalFlat hminFlat
  have hsum :
      (∑ i, ∫ r in s i.castSucc..s i.succ,
        (1 - (s 0) ^ 2 / r ^ 2) * lRegularizedLagrangian (S i) T (alpha i) r) =
      (∑ x : J, ∫ r in lo x..hi x,
        (1 - (s 0) ^ 2 / r ^ 2) * lRegularizedLagrangian (SO x) T (alphaO x) r) +
      (∑ i : E, ∫ r in hi (jn i)..lo (jo i),
        (1 - (s 0) ^ 2 / r ^ 2) * lRegularizedLagrangian (SS i) T (alphaS i) r) +
      ∫ r in hi jf..v, (1 - (s 0) ^ 2 / r ^ 2) * lRegularizedLagrangian ST T alphaT r := by
    let A : K → ℝ := fun k => ∫ r in s (q k).castSucc..s (q k).succ,
      (1 - (s 0) ^ 2 / r ^ 2) * lRegularizedLagrangian (S0 k) T (alpha0 k) r
    have heq : (∑ i, ∫ r in s i.castSucc..s i.succ,
        (1 - (s 0) ^ 2 / r ^ 2) * lRegularizedLagrangian (S i) T (alpha i) r) = ∑ k, A k := by
      rw [← q.symm.sum_comp A]
      apply Finset.sum_congr rfl
      intro i _
      simp only [A, q.apply_symm_apply]
      rfl
    rw [heq, Fintype.sum_sum_type]
    simp only [A, Fintype.sum_sum_type, Fin.sum_univ_one, hOL, hOR, hSL, hSR,
      hqTail, hTL, Fin.succ_last, hEnd, S0, alpha0]
    have hsumO := j.sum_comp (fun x => ∫ r in lo x..hi x,
      (1 - (s 0) ^ 2 / r ^ 2) * lRegularizedLagrangian (SO x) T (alphaO x) r)
    have hsumS := e.sum_comp (fun i => ∫ r in hi (jn i)..lo (jo i),
      (1 - (s 0) ^ 2 / r ^ 2) * lRegularizedLagrangian (SS i) T (alphaS i) r)
    exact (congrArg₂ (fun a b : ℝ => a + (b + ∫ r in hi jf..v,
      (1 - (s 0) ^ 2 / r ^ 2) * lRegularizedLagrangian ST T alphaT r)) hsumO hsumS).trans
      (by ring)
  have hscalarTail (k : K) (hk : k = .inr (.inr 0)) :
      (S0 k).scalar (T - v ^ 2) (alpha0 k v) = ST.scalar (T - v ^ 2) (alphaT v) := by
    subst k
    rfl
  rw [hsum, hEnd] at htrace
  change _ + 2 * v * (S0 (q.symm (Fin.last (2 * N + 1)))).scalar (T - v ^ 2)
    (alpha0 (q.symm (Fin.last (2 * N + 1))) v) * (v - s 0) ^ 2 ≤ _ at htrace
  rw [hscalarTail _ htailIndex] at htrace
  simpa only [
    show Module.finrank ℝ ThreeSpace = 3 by simp [ThreeSpace], Nat.cast_ofNat, show (2 : ℝ) * 3 = 6 by norm_num] using htrace

private theorem exists_directed_local_joins_of_pullback_germ
    {X : Type v} [TopologicalSpace X] [ChartedSpace ThreeSpace X]
    [IsManifold ThreeModel ∞ X] [T2Space X]
    {Y : Type z} [TopologicalSpace Y] [ChartedSpace ThreeSpace Y]
    [IsManifold ThreeModel ∞ Y] [T2Space Y]
    {DX DY : RealTimeInterval}
    (A : SolutionOn (I := ThreeModel) (M := X) DX)
    (B : SolutionOn (I := ThreeModel) (M := Y) DY)
    (f : X → Y) (hf : IsLocalDiffeomorph ThreeModel ThreeModel ∞ f)
    (T r : ℝ) (alpha : ℝ → X) (beta : ℝ → Y)
    (halpha : MDifferentiableAt 𝓘(ℝ, ℝ) ThreeModel alpha r)
    (hcurve : f ∘ alpha =ᶠ[𝓝 r] beta)
    (hmetric : A.base.metric (T - r ^ 2) =
      localPullMetric (B.base.metric (T - r ^ 2)) f hf) :
    ∃ F : PartialDiffeomorph ThreeModel ThreeModel X Y ∞,
      EqOn f F F.source ∧ alpha r ∈ F.source ∧ beta r ∈ F.symm.source ∧
      F (alpha r) = beta r ∧ F.symm (beta r) = alpha r ∧
      F ∘ alpha =ᶠ[𝓝 r] beta ∧ F.symm ∘ beta =ᶠ[𝓝 r] alpha ∧
      (∀ x ∈ F.source, ∀ V W : TangentSpace ThreeModel x,
        (A.base.metric (T - r ^ 2)).inner x V W =
          (B.base.metric (T - r ^ 2)).inner (F x)
            (mfderiv ThreeModel ThreeModel (F : X → Y) x V)
            (mfderiv ThreeModel ThreeModel (F : X → Y) x W)) ∧
      (∀ y ∈ F.symm.source, ∀ V W : TangentSpace ThreeModel y,
        (B.base.metric (T - r ^ 2)).inner y V W =
          (A.base.metric (T - r ^ 2)).inner (F.symm y)
            (mfderiv ThreeModel ThreeModel (F.symm : Y → X) y V)
            (mfderiv ThreeModel ThreeModel (F.symm : Y → X) y W)) ∧
      (mfderiv ThreeModel ThreeModel (F : X → Y) (alpha r)
        (lVelocity (I := ThreeModel) alpha r) : ThreeSpace) = lVelocity (I := ThreeModel) beta r ∧
      (mfderiv ThreeModel ThreeModel (F.symm : Y → X) (beta r)
        (lVelocity (I := ThreeModel) beta r) : ThreeSpace) = lVelocity (I := ThreeModel) alpha r ∧
      A.scalar (T - r ^ 2) (alpha r) = B.scalar (T - r ^ 2) (beta r) ∧
      lRegularizedLagrangian A T alpha r = lRegularizedLagrangian B T beta r := by
  obtain ⟨F, hsource, hEq⟩ := hf (alpha r)
  have hstay : ∀ᶠ t in 𝓝 r, alpha t ∈ F.source :=
    halpha.continuousAt.preimage_mem_nhds (F.open_source.mem_nhds hsource)
  have hcenter : F ∘ alpha =ᶠ[𝓝 r] beta := by
    filter_upwards [hstay, hcurve] with t ht hct
    exact (hEq ht).symm.trans hct
  have hpoint : F (alpha r) = beta r := hcenter.self_of_nhds
  have htarget : beta r ∈ F.symm.source := hpoint ▸ F.map_source hsource
  have hpointInv : F.symm (beta r) = alpha r := by
    rw [← hpoint]
    exact F.left_inv hsource
  have hcenterInv : F.symm ∘ beta =ᶠ[𝓝 r] alpha := by
    filter_upwards [hstay, hcenter] with t ht hct
    change F.symm (beta t) = alpha t
    rw [← hct]
    exact F.left_inv ht
  have hderiv (x : X) (hx : x ∈ F.source) :
      (mfderiv ThreeModel ThreeModel f x : ThreeSpace →L[ℝ] ThreeSpace) =
        mfderiv ThreeModel ThreeModel (F : X → Y) x := by
    exact (Filter.eventuallyEq_of_mem (F.open_source.mem_nhds hx) hEq).mfderiv_eq
  have hforward (x : X) (hx : x ∈ F.source) (V W : TangentSpace ThreeModel x) :
      (A.base.metric (T - r ^ 2)).inner x V W =
        (B.base.metric (T - r ^ 2)).inner (F x)
          (mfderiv ThreeModel ThreeModel (F : X → Y) x V)
          (mfderiv ThreeModel ThreeModel (F : X → Y) x W) := by
    rw [hmetric, localPullMetric_inner, hderiv x hx]
    exact congrArg (fun y : Y => (B.base.metric (T - r ^ 2)).inner y
      (mfderiv ThreeModel ThreeModel (F : X → Y) x V)
      (mfderiv ThreeModel ThreeModel (F : X → Y) x W)) (hEq hx)
  have hinverse (y : Y) (hy : y ∈ F.symm.source) (V W : TangentSpace ThreeModel y) :
      (B.base.metric (T - r ^ 2)).inner y V W =
        (A.base.metric (T - r ^ 2)).inner (F.symm y)
          (mfderiv ThreeModel ThreeModel (F.symm : Y → X) y V)
          (mfderiv ThreeModel ThreeModel (F.symm : Y → X) y W) := by
    have hright : (F : X → Y) ∘ (F.symm : Y → X) =ᶠ[𝓝 y] id := by
      filter_upwards [F.symm.open_source.mem_nhds hy] with z hz
      exact F.right_inv hz
    have hcomp (Z : TangentSpace ThreeModel y) :
        mfderiv ThreeModel ThreeModel (F : X → Y) (F.symm y)
          (mfderiv ThreeModel ThreeModel (F.symm : Y → X) y Z) = Z := by
      have hh := mfderiv_comp_apply y
        (F.mdifferentiableAt (by simp) (F.symm.map_source hy))
        (F.symm.mdifferentiableAt (by simp) hy) Z
      rw [hright.mfderiv_eq, mfderiv_id] at hh
      exact hh.symm
    have hm := hforward (F.symm y) (F.symm.map_source hy)
      (mfderiv ThreeModel ThreeModel (F.symm : Y → X) y V)
      (mfderiv ThreeModel ThreeModel (F.symm : Y → X) y W)
    rw [hcomp, hcomp] at hm
    exact (congrArg (fun z : Y => (B.base.metric (T - r ^ 2)).inner z V W)
      (F.right_inv hy)).symm.trans hm.symm
  have hvel : (mfderiv ThreeModel ThreeModel (F : X → Y) (alpha r)
      (lVelocity (I := ThreeModel) alpha r) : ThreeSpace) = lVelocity (I := ThreeModel) beta r := by
    unfold lVelocity
    rw [← hcenter.mfderiv_eq]
    exact (mfderiv_comp_apply r (F.mdifferentiableAt (by simp) hsource) halpha 1).symm
  have hbeta : MDifferentiableAt 𝓘(ℝ, ℝ) ThreeModel beta r :=
    ((F.mdifferentiableAt (by simp) hsource).comp r halpha).congr_of_eventuallyEq hcenter.symm
  have hvelInv : (mfderiv ThreeModel ThreeModel (F.symm : Y → X) (beta r)
      (lVelocity (I := ThreeModel) beta r) : ThreeSpace) = lVelocity (I := ThreeModel) alpha r := by
    unfold lVelocity
    rw [← hcenterInv.mfderiv_eq]
    exact (mfderiv_comp_apply r (F.symm.mdifferentiableAt (by simp) htarget) hbeta 1).symm
  have hscalar : A.scalar (T - r ^ 2) (alpha r) = B.scalar (T - r ^ 2) (beta r) := by
    change metricScalarAt (A.base.metric (T - r ^ 2)) (alpha r) =
      metricScalarAt (B.base.metric (T - r ^ 2)) (beta r)
    rw [hmetric, metricScalarAt_localPull]
    exact congrArg (metricScalarAt (B.base.metric (T - r ^ 2))) hcurve.self_of_nhds
  have hLag : lRegularizedLagrangian A T alpha r = lRegularizedLagrangian B T beta r := by
    calc
      lRegularizedLagrangian A T alpha r =
          lRegularizedLagrangian (B.localPullback f hf) T alpha r := by
        simp only [lRegularizedLagrangian, SolutionOn.scalar, SolutionFamily.scalar,
          SolutionOn.localPullback_metric, hmetric]
      _ = lRegularizedLagrangian B T (f ∘ alpha) r :=
        lRegularizedLagrangian_localPullback B f hf T halpha
      _ = lRegularizedLagrangian B T beta r := by
        simp only [lRegularizedLagrangian, lVelocity, hcurve.mfderiv_eq, hcurve.self_of_nhds]
        exact congrArg (fun y : Y =>
          (1 / 2 : ℝ) * (B.base.metric (T - r ^ 2)).inner y
            (lVelocity (I := ThreeModel) beta r) (lVelocity (I := ThreeModel) beta r) +
          2 * r ^ 2 * B.scalar (T - r ^ 2) (beta r)) hcurve.self_of_nhds
  exact ⟨F, hEq, hsource, htarget, hpoint, hpointInv, hcenter, hcenterInv,
    hforward, hinverse, hvel, hvelInv, hscalar, hLag⟩

private theorem survivor_pullback_at_strict_join_clocks
    (H : ObservedHistory.{u}) (i : Fin H.eventCount)
    {X : Type v} [TopologicalSpace X] [ChartedSpace ThreeSpace X]
    [IsManifold ThreeModel ∞ X] [T2Space X]
    {DS : RealTimeInterval} (S : SolutionOn (I := ThreeModel) (M := X) DS)
    (oldMap : X → (H.stage i.castSucc).Carrier)
    (newMap : X → (H.stage i.succ).Carrier)
    (hold : IsLocalDiffeomorph ThreeModel ThreeModel ∞ oldMap)
    (hnew : IsLocalDiffeomorph ThreeModel ThreeModel ∞ newMap)
    (C D T c w d : ℝ) (hc : 0 ≤ c) (hcw : c < w) (hwd : w < d)
    (hwclock : T - w ^ 2 = H.time i.succ)
    (hcclock : T - c ^ 2 ∈ Ioo C D) (hdclock : T - d ^ 2 ∈ Ioo C D)
    (hOld : ∀ t ∈ Ico C (H.time i.succ), S.base.metric t =
      localPullMetric (H.stageMetric i.castSucc t) oldMap hold)
    (hNew : ∀ t ∈ Icc (H.time i.succ) D, S.base.metric t =
      localPullMetric (H.stageMetric i.succ t) newMap hnew) :
    T - c ^ 2 ∈ Ioo (H.time i.succ) D ∧
      T - d ^ 2 ∈ Ioo C (H.time i.succ) ∧
      S.base.metric (T - c ^ 2) =
        localPullMetric (H.stageMetric i.succ (T - c ^ 2)) newMap hnew ∧
      S.base.metric (T - d ^ 2) =
        localPullMetric (H.stageMetric i.castSucc (T - d ^ 2)) oldMap hold := by
  have hw : 0 ≤ w := hc.trans hcw.le
  have hdc : H.time i.succ < T - c ^ 2 := by
    have hs := (sq_lt_sq₀ hc hw).mpr hcw
    linarith only [hs, hwclock]
  have hdd : T - d ^ 2 < H.time i.succ := by
    have hs := (sq_lt_sq₀ hw (hw.trans hwd.le)).mpr hwd
    linarith only [hs, hwclock]
  exact ⟨⟨hdc, hcclock.2⟩, ⟨hdclock.1, hdd⟩,
    hNew _ ⟨hdc.le, hcclock.2.le⟩, hOld _ ⟨hdclock.1.le, hdd⟩⟩

private theorem exists_smooth_survivor_directed_joins
    (H : ObservedHistory.{uSmoothJoin}) (i : Fin H.eventCount)
    {C D T c d : ℝ} (hiT : H.time i.succ ≤ T) (hc : 0 ≤ c)
    (hcw : c < Real.sqrt (T - H.time i.succ))
    (hwd : Real.sqrt (T - H.time i.succ) < d)
    (W : TopologicalSpace.Opens (H.event i).incoming.terminalRegularOpen)
    (FC : PartialDiffeomorph ThreeModel ThreeModel
      (H.event i).incoming.terminalRegularOpen (H.stage i.succ).Carrier ∞)
    {DS DN DO : RealTimeInterval}
    (SS : SolutionOn (I := ThreeModel) (M := W) DS)
    (SN : SolutionOn (I := ThreeModel) (M := (H.stage i.succ).Carrier) DN)
    (SO : SolutionOn (I := ThreeModel) (M := (H.stage i.castSucc).Carrier) DO)
    (hold : IsLocalDiffeomorph ThreeModel ThreeModel ∞ (fun z : W => z.val.val))
    (hnew : IsLocalDiffeomorph ThreeModel ThreeModel ∞ (fun z : W => FC z.val))
    (hMN : ∀ t, SN.base.metric t = H.stageMetric i.succ t)
    (hMO : ∀ t, SO.base.metric t = H.stageMetric i.castSucc t)
    (hOld : ∀ t ∈ Ico C (H.time i.succ), SS.base.metric t =
      localPullMetric (H.stageMetric i.castSucc t) (fun z : W => z.val.val) hold)
    (hNew : ∀ t ∈ Icc (H.time i.succ) D, SS.base.metric t =
      localPullMetric (H.stageMetric i.succ t) (fun z : W => FC z.val) hnew)
    (hclockc : T - c ^ 2 ∈ Ioo C D) (hclockd : T - d ^ 2 ∈ Ioo C D)
    (eta : ℝ → W) (alphaN gammaN : ℝ → (H.stage i.succ).Carrier)
    (alphaO gammaO : ℝ → (H.stage i.castSucc).Carrier)
    (hmdc : MDifferentiableAt 𝓘(ℝ, ℝ) ThreeModel eta c)
    (hmdd : MDifferentiableAt 𝓘(ℝ, ℝ) ThreeModel eta d)
    (hGermN : ((fun z : W => FC z.val) ∘ eta) =ᶠ[𝓝 c] gammaN)
    (hGermO : ((fun z : W => z.val.val) ∘ eta) =ᶠ[𝓝 d] gammaO)
    (hOrdN : alphaN =ᶠ[𝓝 c] gammaN) (hOrdO : alphaO =ᶠ[𝓝 d] gammaO) :
    ∃ (Fn : PartialDiffeomorph ThreeModel ThreeModel W (H.stage i.succ).Carrier ∞)
      (Fo : PartialDiffeomorph ThreeModel ThreeModel W (H.stage i.castSucc).Carrier ∞),
      EqOn (fun z : W => FC z.val) Fn Fn.source ∧
      EqOn (fun z : W => z.val.val) Fo Fo.source ∧
      (alphaN c ∈ Fn.symm.source ∧
        (Fn.symm : _ → _) ∘ alphaN =ᶠ[𝓝 c] eta ∧
        (∀ y ∈ Fn.symm.source, ∀ V W : TangentSpace ThreeModel y,
          (SN.base.metric (T - c ^ 2)).inner y V W =
            (SS.base.metric (T - c ^ 2)).inner (Fn.symm y)
              (mfderiv ThreeModel ThreeModel (Fn.symm : _ → _) y V)
              (mfderiv ThreeModel ThreeModel (Fn.symm : _ → _) y W)) ∧
        (mfderiv ThreeModel ThreeModel (Fn.symm : _ → _) (alphaN c)
          (lVelocity (I := ThreeModel) alphaN c) : ThreeSpace) =
            lVelocity (I := ThreeModel) eta c ∧
        SN.scalar (T - c ^ 2) (alphaN c) = SS.scalar (T - c ^ 2) (eta c) ∧
        lRegularizedLagrangian SN T alphaN c = lRegularizedLagrangian SS T eta c) ∧
      (eta d ∈ Fo.source ∧
        (Fo : _ → _) ∘ eta =ᶠ[𝓝 d] alphaO ∧
        (∀ y ∈ Fo.source, ∀ V W : TangentSpace ThreeModel y,
          (SS.base.metric (T - d ^ 2)).inner y V W =
            (SO.base.metric (T - d ^ 2)).inner (Fo y)
              (mfderiv ThreeModel ThreeModel (Fo : _ → _) y V)
              (mfderiv ThreeModel ThreeModel (Fo : _ → _) y W)) ∧
        (mfderiv ThreeModel ThreeModel (Fo : _ → _) (eta d)
          (lVelocity (I := ThreeModel) eta d) : ThreeSpace) =
            lVelocity (I := ThreeModel) alphaO d ∧
        SS.scalar (T - d ^ 2) (eta d) = SO.scalar (T - d ^ 2) (alphaO d) ∧
        lRegularizedLagrangian SS T eta d = lRegularizedLagrangian SO T alphaO d) := by
  have hwclock : T - (Real.sqrt (T - H.time i.succ)) ^ 2 = H.time i.succ := by
    rw [Real.sq_sqrt (sub_nonneg.mpr hiT)]
    ring
  have hclocks := H.survivor_pullback_at_strict_join_clocks i SS
    (fun z : W => z.val.val) (fun z : W => FC z.val) hold hnew
    C D T c (Real.sqrt (T - H.time i.succ)) d hc hcw hwd hwclock hclockc hclockd hOld hNew
  have hmN : SS.base.metric (T - c ^ 2) =
      localPullMetric (SN.base.metric (T - c ^ 2)) (fun z : W => FC z.val) hnew := by
    rw [hMN]
    exact hclocks.2.2.1
  have hmO : SS.base.metric (T - d ^ 2) =
      localPullMetric (SO.base.metric (T - d ^ 2)) (fun z : W => z.val.val) hold := by
    rw [hMO]
    exact hclocks.2.2.2
  obtain ⟨Fn, hEqN, _, hTarget, _, _, _, hInv, _, hInvMetric, _, hInvVel, hScalarN, hLagN⟩ :=
    exists_directed_local_joins_of_pullback_germ SS SN (fun z : W => FC z.val) hnew T c
      eta alphaN hmdc (hGermN.trans hOrdN.symm) hmN
  obtain ⟨Fo, hEqO, hSource, _, _, _, hForward, _, hMetric, _, hVel, _, hScalarO, hLagO⟩ :=
    exists_directed_local_joins_of_pullback_germ SS SO (fun z : W => z.val.val) hold T d
      eta alphaO hmdd (hGermO.trans hOrdO.symm) hmO
  exact ⟨Fn, Fo, hEqN, hEqO,
    ⟨hTarget, hInv, hInvMetric, hInvVel, hScalarN.symm, hLagN.symm⟩,
    ⟨hSource, hForward, hMetric, hVel, hScalarO, hLagO⟩⟩

private theorem smooth_collar_weighted_trace_bound_of_action_minimum
    (H : ObservedHistory.{u}) (first last : Fin (H.eventCount + 1)) (hle : first ≤ last)
    {T v : ℝ} (hv : 0 ≤ v)
    (hupper : T ∈ Icc (H.time last) (H.stageEndTime last))
    (hpast : T - v ^ 2 ∈ H.stageDomain first) :
    let J := H.StageInterval first last;
    let E := {i : Fin H.eventCount // first ≤ i.castSucc ∧ i.succ ≤ last};
    let jo (i : E) : J := ⟨i.val.castSucc, i.property.1,
      i.val.castSucc_le_succ.trans i.property.2⟩;
    let jn (i : E) : J := ⟨i.val.succ,
      i.property.1.trans i.val.castSucc_le_succ, i.property.2⟩;
    let jf : J := ⟨first, le_rfl, hle⟩;
    let jl : J := ⟨last, hle, le_rfl⟩;
    ∀ (gamma : (j : J) → ℝ → (H.stage j.val).Carrier) (lo hi : J → ℝ),
      (∀ j, H.regularizedStageStart T 0 j.val ≤ lo j ∧ lo j ≤ hi j ∧
        hi j ≤ H.regularizedStageEnd T v j.val) →
      Manifold.absolutelyContinuousOnInterval ThreeModel (gamma jl) 0 (lo jl) →
      IntervalIntegrable (H.stageRegularizedLagrangian last T (gamma jl)) volume 0 (lo jl) →
      (∀ delta : (j : J) → ℝ → (H.stage j.val).Carrier,
        (∀ j, Manifold.absolutelyContinuousOnInterval ThreeModel (delta j)
          (H.regularizedStageStart T 0 j.val) (H.regularizedStageEnd T v j.val)) →
        (∀ j, IntervalIntegrable (H.stageRegularizedLagrangian j.val T (delta j)) volume
          (H.regularizedStageStart T 0 j.val) (H.regularizedStageEnd T v j.val)) →
        delta jl 0 = gamma jl 0 →
        (∀ (i : Fin H.eventCount) (hf : first ≤ i.castSucc) (hl : i.succ ≤ last),
          ∃ z : (H.event i).old,
            z.val.val = delta ⟨i.castSucc, hf, i.castSucc_le_succ.trans hl⟩
              (Real.sqrt (T - H.time i.succ)) ∧
            (H.event i).oldOutput z = delta ⟨i.succ, hf.trans i.castSucc_le_succ, hl⟩
              (Real.sqrt (T - H.time i.succ))) →
        (∑ j : J, H.stageRegularizedAction j.val T (gamma j)
          (H.regularizedStageStart T 0 j.val) (H.regularizedStageEnd T v j.val)) ≤
        (∑ j : J, H.stageRegularizedAction j.val T (delta j)
          (H.regularizedStageStart T 0 j.val) (H.regularizedStageEnd T v j.val))) →
    ∀ {N : ℕ} (j : Fin (N + 1) ≃ J) (e : Fin N ≃ E)
      (_ : j (Fin.last N) = jf) (_ : j 0 = jl)
      (_ : ∀ k : Fin N, j k.castSucc = jn (e k))
      (_ : ∀ k : Fin N, j k.succ = jo (e k))
      (W : (i : E) → TopologicalSpace.Opens (H.event i.val).incoming.terminalRegularOpen)
      (FC : (i : E) → PartialDiffeomorph ThreeModel ThreeModel
        (H.event i.val).incoming.terminalRegularOpen (H.stage i.val.succ).Carrier ∞)
      (C D : E → ℝ)
      (DO : J → RealTimeInterval) (DS : E → RealTimeInterval) (DT : RealTimeInterval)
      (SO : (x : J) → SolutionOn (I := ThreeModel) (M := (H.stage x.val).Carrier) (DO x))
      (SS : (i : E) → SolutionOn (I := ThreeModel) (M := W i) (DS i))
      (ST : SolutionOn (I := ThreeModel) (M := (H.stage first).Carrier) DT)
      (hold : ∀ i, IsLocalDiffeomorph ThreeModel ThreeModel ∞ (fun z : W i => z.val.val))
      (hnew : ∀ i, IsLocalDiffeomorph ThreeModel ThreeModel ∞ (fun z : W i => FC i z.val))
      (alphaO : (x : J) → ℝ → (H.stage x.val).Carrier)
      (alphaS : (i : E) → ℝ → W i) (alphaT : ℝ → (H.stage first).Carrier)
      (s : Fin (2 * N + 3) → ℝ),
      (∀ x, IsSolutionOn (SO x)) → (∀ i, IsSolutionOn (SS i)) → IsSolutionOn ST →
      (∀ x t, (SO x).base.metric t = H.stageMetric x.val t) →
      (∀ t, ST.base.metric t = H.stageMetric first t) →
      (∀ i z, (H.event i.val).RegularCrossing (z : W i).val.val (FC i z.val)) →
      (∀ i, ∀ t ∈ Ico (C i) (H.time i.val.succ),
        (SS i).base.metric t = localPullMetric (H.stageMetric i.val.castSucc t)
          (fun z : W i => z.val.val) (hold i)) →
      (∀ i, ∀ t ∈ Icc (H.time i.val.succ) (D i),
        (SS i).base.metric t = localPullMetric (H.stageMetric i.val.succ t)
          (fun z : W i => FC i z.val) (hnew i)) →
      (∀ i, hi (jn i) < Real.sqrt (T - H.time i.val.succ) ∧
        Real.sqrt (T - H.time i.val.succ) < lo (jo i)) →
      (∀ i, ∀ r ∈ Icc (hi (jn i)) (lo (jo i)), T - r ^ 2 ∈ Ioo (C i) (D i)) →
      (∀ x, ContMDiff 𝓘(ℝ, ℝ) ThreeModel ∞ (alphaO x)) →
      (∀ i, ContMDiff 𝓘(ℝ, ℝ) ThreeModel ∞ (alphaS i)) →
      ContMDiff 𝓘(ℝ, ℝ) ThreeModel ∞ alphaT →
      (∀ x, IsLRegularizedGeodesicOn (SO x) T (alphaO x) (Icc (lo x) (hi x))) →
      (∀ i, IsLRegularizedGeodesicOn (SS i) T (alphaS i) (Icc (hi (jn i)) (lo (jo i)))) →
      IsLRegularizedGeodesicOn ST T alphaT (Icc (hi jf) v) →
      (∀ x, ∀ r ∈ Icc (lo x) (hi x), alphaO x =ᶠ[𝓝 r] gamma x) →
      EqOn alphaT (gamma jf) (Icc (hi jf) v) →
      alphaT =ᶠ[𝓝 (hi jf)] gamma jf →
      (∀ i, EqOn (fun r => (alphaS i r).val.val) (gamma (jo i))
        (Icc (Real.sqrt (T - H.time i.val.succ)) (lo (jo i)))) →
      (∀ i, EqOn (fun r => FC i (alphaS i r).val) (gamma (jn i))
        (Icc (hi (jn i)) (Real.sqrt (T - H.time i.val.succ)))) →
      (∀ i, ((fun z : W i => z.val.val) ∘ alphaS i) =ᶠ[𝓝 (lo (jo i))] gamma (jo i)) →
      (∀ i, ((fun z : W i => FC i z.val) ∘ alphaS i) =ᶠ[𝓝 (hi (jn i))] gamma (jn i)) →
      lVelocity (I := ThreeModel) alphaT v = 0 →
      StrictMono s → 0 < s 0 →
    ∀ (_ : ∀ k, s (interleavedPieceEquiv N (.inl k)).castSucc = lo (j k))
      (_ : ∀ k, s (interleavedPieceEquiv N (.inl k)).succ = hi (j k))
      (_ : ∀ k, s (interleavedPieceEquiv N (.inr (.inl k))).castSucc = hi (jn (e k)))
      (_ : ∀ k, s (interleavedPieceEquiv N (.inr (.inl k))).succ = lo (jo (e k)))
      (_ : s (Fin.last (2 * N + 1)).castSucc = hi jf)
      (_ : s (Fin.last (2 * N + 2)) = v)
      (lowO highO : J → ℝ) (lowS highS : E → ℝ) (lowT highT : ℝ),
      (∀ x, lowO x < lo x ∧ hi x < highO x) →
      (∀ i, lowS i < hi (jn i) ∧ lo (jo i) < highS i) →
      lowT < hi jf → v < highT →
      (∀ (x : J) (r : ℝ), r ∈ Ioo (lowO x) (highO x) → T - r ^ 2 ∈ (DO x).regular) →
      (∀ (i : E) (r : ℝ), r ∈ Ioo (lowS i) (highS i) → T - r ^ 2 ∈ (DS i).regular) →
      (∀ (r : ℝ), r ∈ Ioo lowT highT → T - r ^ 2 ∈ DT.regular) →
      (∑ x : J, ∫ r in lo x..hi x,
        (1 - (s 0) ^ 2 / r ^ 2) * lRegularizedLagrangian (SO x) T (alphaO x) r) +
      (∑ i : E, ∫ r in hi (jn i)..lo (jo i),
        (1 - (s 0) ^ 2 / r ^ 2) * lRegularizedLagrangian (SS i) T (alphaS i) r) +
      (∫ r in hi jf..v, (1 - (s 0) ^ 2 / r ^ 2) * lRegularizedLagrangian ST T alphaT r) +
      2 * v * ST.scalar (T - v ^ 2) (alphaT v) * (v - s 0) ^ 2 ≤ 6 * (v - s 0) := by
  classical
  intro J E jo jn jf jl gamma lo hi hbounds hprefixAC hprefixInt hminimum
    N j e hfirst hlast hjn hjo W FC C D DO DS DT SO SS ST hold hnew alphaO alphaS alphaT s
    hSO hSS hST hmetricO hmetricT hcross hmetricOld hmetricNew hstrict hphysical
    hsmO hsmS hsmT hgeoO hgeoS hgeoT hGermO hcenterT hGermT
    hcenterOld hcenterNew hGermOld hGermNew hfinal hs ha
    hOL hOR hSL hSR hTL hEnd lowO highO lowS highS lowT highT
    hmarginO hmarginS hlowT hhighT hregO hregS hregT
  have hc (i : E) : 0 ≤ hi (jn i) :=
    (Real.sqrt_nonneg _).trans ((hbounds (jn i)).1.trans (hbounds (jn i)).2.1)
  have hwclock (i : E) : T - (Real.sqrt (T - H.time i.val.succ)) ^ 2 = H.time i.val.succ := by
    rw [Real.sq_sqrt (sub_nonneg.mpr ((H.time_strictMono.monotone i.property.2).trans hupper.1))]
    ring
  have hOldHalf (i : E) (r : ℝ)
      (hr : r ∈ Ioo (Real.sqrt (T - H.time i.val.succ)) (lo (jo i))) :
      (SS i).base.metric (T - r ^ 2) =
        localPullMetric (H.stageMetric i.val.castSucc (T - r ^ 2))
          (fun z : W i => z.val.val) (hold i) := by
    have hpr := hphysical i r ⟨((hstrict i).1.trans hr.1).le, hr.2.le⟩
    have hsq := (sq_lt_sq₀ (Real.sqrt_nonneg _) ((Real.sqrt_nonneg _).trans hr.1.le)).mpr hr.1
    have ht : T - r ^ 2 < H.time i.val.succ := by linarith only [hsq, hwclock i]
    exact hmetricOld i _ ⟨hpr.1.le, ht⟩
  have hNewHalf (i : E) (r : ℝ)
      (hr : r ∈ Ioo (hi (jn i)) (Real.sqrt (T - H.time i.val.succ))) :
      (SS i).base.metric (T - r ^ 2) =
        localPullMetric (H.stageMetric i.val.succ (T - r ^ 2))
          (fun z : W i => FC i z.val) (hnew i) := by
    have hpr := hphysical i r ⟨hr.1.le, (hr.2.trans (hstrict i).2).le⟩
    have hsq := (sq_lt_sq₀ ((hc i).trans hr.1.le) (Real.sqrt_nonneg _)).mpr hr.2
    have ht : H.time i.val.succ < T - r ^ 2 := by linarith only [hsq, hwclock i]
    exact hmetricNew i _ ⟨ht.le, hpr.2.le⟩
  choose Fn0 Fo0 hEqN0 hEqO0 hgeomN0 hgeomO0 using fun i : E =>
    H.exists_smooth_survivor_directed_joins i.val
      ((H.time_strictMono.monotone i.property.2).trans hupper.1) (hc i)
      (hstrict i).1 (hstrict i).2 (W i) (FC i) (SS i) (SO (jn i)) (SO (jo i))
      (hold i) (hnew i) (hmetricO (jn i)) (hmetricO (jo i)) (hmetricOld i) (hmetricNew i)
      (hphysical i _ ⟨le_rfl, ((hstrict i).1.trans (hstrict i).2).le⟩)
      (hphysical i _ ⟨((hstrict i).1.trans (hstrict i).2).le, le_rfl⟩)
      (alphaS i) (alphaO (jn i)) (gamma (jn i)) (alphaO (jo i)) (gamma (jo i))
      ((hsmS i).mdifferentiableAt (by simp)) ((hsmS i).mdifferentiableAt (by simp))
      (hGermNew i) (hGermOld i)
      (hGermO (jn i) _ ⟨(hbounds (jn i)).2.1, le_rfl⟩)
      (hGermO (jo i) _ ⟨le_rfl, (hbounds (jo i)).2.1⟩)
  have hN (i : E) (x : J) (hx : x = jn i) (r : ℝ) (hr : r = hi (jn i)) :
      ∃ F : PartialDiffeomorph ThreeModel ThreeModel (W i) (H.stage x.val).Carrier ∞,
        EqOn (fun z : W i => cast (congrArg (fun x : J => (H.stage x.val).Carrier) hx.symm)
          (FC i z.val)) F F.source ∧
        (alphaO x) r ∈ F.symm.source ∧
        (F.symm : _ → _) ∘ (alphaO x) =ᶠ[𝓝 r] (alphaS i) ∧
        (∀ y ∈ F.symm.source, ∀ V W : TangentSpace ThreeModel y,
          ((SO x).base.metric (T - r ^ 2)).inner y V W =
            ((SS i).base.metric (T - r ^ 2)).inner (F.symm y)
              (mfderiv ThreeModel ThreeModel (F.symm : _ → _) y V)
              (mfderiv ThreeModel ThreeModel (F.symm : _ → _) y W)) ∧
        (mfderiv ThreeModel ThreeModel (F.symm : _ → _) ((alphaO x) r)
          (lVelocity (I := ThreeModel) (alphaO x) r) : ThreeSpace) =
            lVelocity (I := ThreeModel) (alphaS i) r ∧
        (SO x).scalar (T - r ^ 2) ((alphaO x) r) =
          (SS i).scalar (T - r ^ 2) ((alphaS i) r) ∧
        lRegularizedLagrangian (SO x) T (alphaO x) r =
          lRegularizedLagrangian (SS i) T (alphaS i) r := by
    subst x
    subst r
    exact ⟨Fn0 i, hEqN0 i, hgeomN0 i⟩
  have hO (i : E) (x : J) (hx : x = jo i) (r : ℝ) (hr : r = lo (jo i)) :
      ∃ F : PartialDiffeomorph ThreeModel ThreeModel (W i) (H.stage x.val).Carrier ∞,
        EqOn (fun z : W i => cast (congrArg (fun x : J => (H.stage x.val).Carrier) hx.symm)
          z.val.val) F F.source ∧
        (alphaS i) r ∈ F.source ∧
        (F : _ → _) ∘ (alphaS i) =ᶠ[𝓝 r] (alphaO x) ∧
        (∀ y ∈ F.source, ∀ V W : TangentSpace ThreeModel y,
          ((SS i).base.metric (T - r ^ 2)).inner y V W =
            ((SO x).base.metric (T - r ^ 2)).inner (F y)
              (mfderiv ThreeModel ThreeModel (F : _ → _) y V)
              (mfderiv ThreeModel ThreeModel (F : _ → _) y W)) ∧
        (mfderiv ThreeModel ThreeModel (F : _ → _) ((alphaS i) r)
          (lVelocity (I := ThreeModel) (alphaS i) r) : ThreeSpace) =
            lVelocity (I := ThreeModel) (alphaO x) r ∧
        (SS i).scalar (T - r ^ 2) ((alphaS i) r) =
          (SO x).scalar (T - r ^ 2) ((alphaO x) r) ∧
        lRegularizedLagrangian (SS i) T (alphaS i) r =
          lRegularizedLagrangian (SO x) T (alphaO x) r := by
    subst x
    subst r
    exact ⟨Fo0 i, hEqO0 i, hgeomO0 i⟩
  choose Fn hEqn hgeomNew using fun k : Fin N => hN (e k) (j k.castSucc) (hjn k)
    (s (interleavedPieceEquiv N (.inr (.inl k))).castSucc) (hSL k)
  choose Fo hEqo hgeomOld using fun k : Fin N => hO (e k) (j k.succ) (hjo k)
    (s (interleavedPieceEquiv N (.inr (.inl k))).succ) (hSR k)
  have htail : alphaO jf =ᶠ[𝓝 (hi jf)] alphaT :=
    (hGermO jf (hi jf) ⟨(hbounds jf).2.1, le_rfl⟩).trans hGermT.symm
  exact H.interleaved_weighted_trace_bound_of_action_minimum first last hle hv hupper hpast
    gamma lo hi hbounds hprefixAC hprefixInt hminimum j e hfirst hlast hjn hjo
    W FC DO DS DT SO SS ST hold hnew alphaO alphaS alphaT s
    hSO hSS hST hmetricO hmetricT hcross hOldHalf hNewHalf hsmO hsmS hsmT
    hgeoO hgeoS hgeoT (fun x r hr => (hGermO x r hr).self_of_nhds)
    hcenterT hcenterOld hcenterNew hfinal hs ha
    hOL hOR hSL hSR hTL hEnd lowO highO lowS highS lowT highT
    hmarginO hmarginS hlowT hhighT hregO hregS hregT Fn Fo hEqn hEqo htail
    hgeomNew hgeomOld

private theorem restriction_action_minimal_at_zero_pole_of_spatial_cost_minimum
    (H : ObservedHistory.{u}) (first : Fin (H.eventCount + 1)) (i : Fin H.eventCount)
    (hf : first ≤ i.castSucc) {B v : ℝ} (hv : 0 ≤ v)
    (hpast : H.time i.succ - v ^ 2 ∈ H.stageDomain first)
    (gamma : (j : H.StageInterval first i.succ) → ℝ → (H.stage j.val).Carrier)
    (hgammaAC : ∀ j, Manifold.absolutelyContinuousOnInterval ThreeModel (gamma j)
      (H.regularizedStageStart (H.time i.succ) 0 j.val)
      (H.regularizedStageEnd (H.time i.succ) v j.val))
    (hgammaInt : ∀ j, IntervalIntegrable
      (H.stageRegularizedLagrangian j.val (H.time i.succ) (gamma j)) volume
      (H.regularizedStageStart (H.time i.succ) 0 j.val)
      (H.regularizedStageEnd (H.time i.succ) v j.val))
    (hgammaNodes : ∀ (k : Fin H.eventCount) (hkf : first ≤ k.castSucc) (hkl : k.succ ≤ i.succ),
      ∃ z : (H.event k).old,
        z.val.val = gamma ⟨k.castSucc, hkf, k.castSucc_le_succ.trans hkl⟩
          (Real.sqrt (H.time i.succ - H.time k.succ)) ∧
        (H.event k).oldOutput z = gamma ⟨k.succ, hkf.trans k.castSucc_le_succ, hkl⟩
          (Real.sqrt (H.time i.succ - H.time k.succ)))
    (hscalar : ∀ j : H.StageInterval first i.succ,
      ∀ r ∈ Ioo (H.regularizedStageStart (H.time i.succ) 0 j.val)
          (H.regularizedStageEnd (H.time i.succ) v j.val),
      ∀ x : (H.stage j.val).Carrier,
        -B ≤ metricScalarAt (H.stageMetric j.val (H.time i.succ - r ^ 2)) x)
    (hcost : H.regularizedCost first i.succ (hf.trans i.castSucc_le_succ)
      (H.time i.succ) B 0 v (gamma ⟨i.succ, hf.trans i.castSucc_le_succ, le_rfl⟩ 0)
        (gamma ⟨first, le_rfl, hf.trans i.castSucc_le_succ⟩ v) =
      (((∑ j : H.StageInterval first i.succ,
        H.stageRegularizedAction j.val (H.time i.succ) (gamma j)
          (H.regularizedStageStart (H.time i.succ) 0 j.val)
          (H.regularizedStageEnd (H.time i.succ) v j.val)) : ℝ) : WithTop ℝ))
    (hminimum : ∀ q : (H.stage first).Carrier,
      H.regularizedCost first i.succ (hf.trans i.castSucc_le_succ)
        (H.time i.succ) B 0 v (gamma ⟨i.succ, hf.trans i.castSucc_le_succ, le_rfl⟩ 0)
          (gamma ⟨first, le_rfl, hf.trans i.castSucc_le_succ⟩ v) ≤
      H.regularizedCost first i.succ (hf.trans i.castSucc_le_succ)
        (H.time i.succ) B 0 v (gamma ⟨i.succ, hf.trans i.castSucc_le_succ, le_rfl⟩ 0) q) :
    let gammaOld : (j : H.StageInterval first i.castSucc) → ℝ → (H.stage j.val).Carrier :=
      fun j => gamma ⟨j.val, j.property.1, j.property.2.trans i.castSucc_le_succ⟩;
    (∑ j : H.StageInterval first i.succ,
      H.stageRegularizedAction j.val (H.time i.succ) (gamma j)
        (H.regularizedStageStart (H.time i.succ) 0 j.val)
        (H.regularizedStageEnd (H.time i.succ) v j.val)) =
      (∑ j : H.StageInterval first i.castSucc,
        H.stageRegularizedAction j.val (H.time i.succ) (gammaOld j)
          (H.regularizedStageStart (H.time i.succ) 0 j.val)
          (H.regularizedStageEnd (H.time i.succ) v j.val)) ∧
    ∀ delta : (j : H.StageInterval first i.castSucc) → ℝ → (H.stage j.val).Carrier,
      (∀ j, Manifold.absolutelyContinuousOnInterval ThreeModel (delta j)
        (H.regularizedStageStart (H.time i.succ) 0 j.val)
        (H.regularizedStageEnd (H.time i.succ) v j.val)) →
      (∀ j, IntervalIntegrable
        (H.stageRegularizedLagrangian j.val (H.time i.succ) (delta j)) volume
        (H.regularizedStageStart (H.time i.succ) 0 j.val)
        (H.regularizedStageEnd (H.time i.succ) v j.val)) →
      delta ⟨i.castSucc, hf, le_rfl⟩ 0 = gammaOld ⟨i.castSucc, hf, le_rfl⟩ 0 →
      (∀ (k : Fin H.eventCount) (hkf : first ≤ k.castSucc) (hkl : k.succ ≤ i.castSucc),
        ∃ z : (H.event k).old,
          z.val.val = delta ⟨k.castSucc, hkf, k.castSucc_le_succ.trans hkl⟩
            (Real.sqrt (H.time i.succ - H.time k.succ)) ∧
          (H.event k).oldOutput z = delta ⟨k.succ, hkf.trans k.castSucc_le_succ, hkl⟩
            (Real.sqrt (H.time i.succ - H.time k.succ))) →
      (∑ j : H.StageInterval first i.castSucc,
        H.stageRegularizedAction j.val (H.time i.succ) (gammaOld j)
          (H.regularizedStageStart (H.time i.succ) 0 j.val)
          (H.regularizedStageEnd (H.time i.succ) v j.val)) ≤
      (∑ j : H.StageInterval first i.castSucc,
        H.stageRegularizedAction j.val (H.time i.succ) (delta j)
          (H.regularizedStageStart (H.time i.succ) 0 j.val)
          (H.regularizedStageEnd (H.time i.succ) v j.val)) := by
  classical
  intro gammaOld
  have hpole : ∃ z : (H.event i).old,
      z.val.val = gamma ⟨i.castSucc, hf, i.castSucc_le_succ⟩ 0 ∧
      (H.event i).oldOutput z = gamma ⟨i.succ, hf.trans i.castSucc_le_succ, le_rfl⟩ 0 := by
    simpa only [sub_self, Real.sqrt_zero] using hgammaNodes i hf le_rfl
  obtain ⟨beta0, _, _, hbetaOld, hbetaLast, _, hsum0⟩ :=
    H.extend_stage_family_by_zero_pole_stage first i hf v gamma gammaOld
      (fun j => hgammaAC ⟨j.val, j.property.1, j.property.2.trans i.castSucc_le_succ⟩)
      (fun j => hgammaInt ⟨j.val, j.property.1, j.property.2.trans i.castSucc_le_succ⟩)
      (fun k hkf hkl => hgammaNodes k hkf (hkl.trans i.castSucc_le_succ)) rfl hpole
  have hbetaEq (j : H.StageInterval first i.succ) : beta0 j = gamma j := by
    by_cases hj : j.val ≤ i.castSucc
    · exact hbetaOld ⟨j.val, j.property.1, hj⟩
    · have heq : j = ⟨i.succ, hf.trans i.castSucc_le_succ, le_rfl⟩ := by
        apply Subtype.ext
        apply Fin.ext
        have hh := j.property.2
        change j.val.val ≤ i.val + 1 at hh
        change ¬j.val.val ≤ i.val at hj
        change j.val.val = i.val + 1
        omega
      subst j
      exact hbetaLast
  have hfullEq :
      (∑ j : H.StageInterval first i.succ,
        H.stageRegularizedAction j.val (H.time i.succ) (gamma j)
          (H.regularizedStageStart (H.time i.succ) 0 j.val)
          (H.regularizedStageEnd (H.time i.succ) v j.val)) =
      (∑ j : H.StageInterval first i.castSucc,
        H.stageRegularizedAction j.val (H.time i.succ) (gammaOld j)
          (H.regularizedStageStart (H.time i.succ) 0 j.val)
          (H.regularizedStageEnd (H.time i.succ) v j.val)) := by
    simpa only [hbetaEq] using hsum0
  refine ⟨hfullEq, ?_⟩
  intro delta hAC hint hrecent hnodes
  obtain ⟨beta, hbetaAC, hbetaInt, _, hbetaLast, hbetaNodes, hsum⟩ :=
    H.extend_stage_family_by_zero_pole_stage first i hf v gamma delta
      hAC hint hnodes hrecent hpole
  have hupper : H.time i.succ - (0 : ℝ) ^ 2 ∈
      Icc (H.time i.succ) (H.stageEndTime i.succ) := by
    simpa only [zero_pow two_ne_zero, sub_zero] using
      (show H.time i.succ ∈ Icc (H.time i.succ) (H.stageEndTime i.succ) from
        ⟨le_rfl, H.time_le_stageEndTime i.succ⟩)
  have hmember : H.regularizedExtendedAction first i.succ (H.time i.succ) B 0 v beta ∈
      H.regularizedActionValues first i.succ (hf.trans i.castSucc_le_succ)
        (H.time i.succ) B 0 v (gamma ⟨i.succ, hf.trans i.castSucc_le_succ, le_rfl⟩ 0)
          (beta ⟨first, le_rfl, hf.trans i.castSucc_le_succ⟩ v) :=
    ⟨le_rfl, hv, hupper, hpast, beta, hbetaAC, congrFun hbetaLast 0, rfl, hbetaNodes, rfl⟩
  have hh := (hminimum (beta ⟨first, le_rfl, hf.trans i.castSucc_le_succ⟩ v)).trans
    (H.regularizedCost_le_of_competitor first i.succ (hf.trans i.castSucc_le_succ)
      (H.time i.succ) B 0 v _ _ hmember)
  rw [hcost, H.regularizedExtendedAction_eq_sum_action first i.succ le_rfl hv hupper hpast
    beta hbetaInt (fun j => by
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
      exact hscalar j r hr (beta j r))] at hh
  have hreal := WithTop.coe_le_coe.mp hh
  rwa [hfullEq, hsum] at hreal

private theorem exists_positive_regularized_stage_interval
    (H : ObservedHistory.{uPositiveStages})
    (first last : Fin (H.eventCount + 1)) (hle : first ≤ last)
    {T v : ℝ} (hv : 0 < v)
    (hupper : T ∈ Icc (H.time last) (H.stageEndTime last))
    (hpast : T - v ^ 2 ∈ Ioo (H.time first) (H.stageEndTime first)) :
    ∃ lastPos : Fin (H.eventCount + 1),
      first ≤ lastPos ∧ lastPos ≤ last ∧
      (lastPos = last ↔ H.time last < T) ∧
      (T = H.time last → ∃ i : Fin H.eventCount, last = i.succ ∧ lastPos = i.castSucc) ∧
      H.regularizedStageStart T 0 lastPos = 0 ∧
      H.regularizedStageEnd T v first = v ∧
      (∀ j : Fin (H.eventCount + 1), first ≤ j → j ≤ lastPos →
        H.regularizedStageStart T 0 j < H.regularizedStageEnd T v j) ∧
      (∀ j : Fin (H.eventCount + 1), j ≤ last → lastPos < j →
        j = last ∧ H.regularizedStageStart T 0 j = 0 ∧ H.regularizedStageEnd T v j = 0) ∧
      (∀ i : Fin H.eventCount, i.succ ≤ last →
        (0 < Real.sqrt (T - H.time i.succ) ↔ i.succ ≤ lastPos)) := by
  have hfirstT : H.time first < T :=
    hpast.1.trans_le (sub_le_self _ (sq_nonneg v))
  obtain ⟨lastPos, hfirstPos, hposLast, hcharacter, hcases⟩ :
      ∃ lastPos : Fin (H.eventCount + 1), first ≤ lastPos ∧ lastPos ≤ last ∧
        (∀ j : Fin (H.eventCount + 1), j ≤ last →
          (j ≤ lastPos ↔ H.time j < T)) ∧
        (lastPos = last ∨ ∃ i : Fin H.eventCount,
          last = i.succ ∧ lastPos = i.castSucc ∧ T = H.time last) := by
    by_cases hpole : T = H.time last
    · have hfirstLast : first < last :=
        H.time_strictMono.lt_iff_lt.mp (hfirstT.trans_eq hpole)
      cases last using Fin.cases with
      | zero => exact False.elim ((not_lt_of_ge (Fin.zero_le first)) hfirstLast)
      | succ i =>
        refine ⟨i.castSucc, Fin.le_castSucc_iff.mpr hfirstLast, i.castSucc_le_succ, ?_,
          Or.inr ⟨i, rfl, rfl, hpole⟩⟩
        intro j _
        rw [hpole, H.time_strictMono.lt_iff_lt]
        exact Fin.le_castSucc_iff
    · have hlastT : H.time last < T := lt_of_le_of_ne hupper.1 (Ne.symm hpole)
      refine ⟨last, hle, le_rfl, ?_, Or.inl rfl⟩
      intro j hj
      exact iff_of_true hj ((H.time_strictMono.monotone hj).trans_lt hlastT)
  have hposT : H.time lastPos < T := (hcharacter lastPos hposLast).mp le_rfl
  have hlastStart : H.regularizedStageStart T 0 last = 0 :=
    H.regularizedStageStart_eq_of_mem_Icc (show (0 : ℝ) ≤ 0 from le_rfl)
      (by simpa only [zero_pow (by decide : (2 : ℕ) ≠ 0), sub_zero] using hupper)
  have hlastEq : lastPos = last ↔ H.time last < T := by
    constructor
    · intro heq
      simpa only [heq] using hposT
    · intro ht
      exact le_antisymm hposLast ((hcharacter last le_rfl).mpr ht)
  have hpolePred (hpole : T = H.time last) :
      ∃ i : Fin H.eventCount, last = i.succ ∧ lastPos = i.castSucc := by
    rcases hcases with heq | ⟨i, hilast, hipos, _⟩
    · exact False.elim ((hlastEq.mp heq).ne hpole.symm)
    · exact ⟨i, hilast, hipos⟩
  have hposStart : H.regularizedStageStart T 0 lastPos = 0 := by
    rcases hcases with heq | ⟨i, hilast, hipos, hpole⟩
    · simpa only [heq] using hlastStart
    · have htime : H.time i.succ = T := by simpa only [hilast] using hpole.symm
      simp only [hipos, regularizedStageStart, zero_pow (by decide : (2 : ℕ) ≠ 0), sub_zero,
        H.stageEndTime_castSucc, htime, min_self, sub_self, Real.sqrt_zero]
  have hfirstEnd : H.regularizedStageEnd T v first = v :=
    H.regularizedStageEnd_eq_of_mem_stageDomain hv.le (H.mem_stageDomain_of_mem_Ioo hpast)
  refine ⟨lastPos, hfirstPos, hposLast, hlastEq, hpolePred, hposStart, hfirstEnd, ?_, ?_, ?_⟩
  · intro j hfj hjpos
    have hjlast : j ≤ last := hjpos.trans hposLast
    have hjT : H.time j < T := (hcharacter j hjlast).mp hjpos
    have hstage : H.time j < H.stageEndTime j := by
      cases j using Fin.lastCases with
      | last =>
        have hlast : last = Fin.last H.eventCount := le_antisymm (Fin.le_last last) hjlast
        simpa only [hlast] using hjT.trans_le hupper.2
      | cast i =>
        simpa only [H.stageEndTime_castSucc] using H.time_strictMono i.castSucc_lt_succ
    have hpastEnd : T - v ^ 2 < H.stageEndTime j :=
      hpast.2.trans_le (H.stageEndTime_mono hfj)
    have hgap : max (T - v ^ 2) (H.time j) < min T (H.stageEndTime j) :=
      max_lt (lt_min (sub_lt_self T (sq_pos_of_pos hv)) hpastEnd) (lt_min hjT hstage)
    have hsqrt := Real.sqrt_lt_sqrt (sub_nonneg.mpr (min_le_left T (H.stageEndTime j)))
      (sub_lt_sub_left hgap T)
    simpa only [regularizedStageStart, regularizedStageEnd, zero_pow (by decide : (2 : ℕ) ≠ 0), sub_zero] using hsqrt
  · intro j hjlast hposj
    have hnot : ¬H.time j < T := fun h => (not_le_of_gt hposj) ((hcharacter j hjlast).mpr h)
    have hjT : H.time j = T := le_antisymm
      ((H.time_strictMono.monotone hjlast).trans hupper.1) (le_of_not_gt hnot)
    have hlastj : last ≤ j := H.time_strictMono.le_iff_le.mp (hupper.1.trans_eq hjT.symm)
    have heq : j = last := le_antisymm hjlast hlastj
    refine ⟨heq, ?_, ?_⟩
    · simpa only [heq] using hlastStart
    · simp only [regularizedStageEnd, hjT, max_eq_right (sub_le_self T (sq_nonneg v)),
        sub_self, Real.sqrt_zero]
  · intro i hilast
    rw [Real.sqrt_pos, sub_pos]
    exact (hcharacter i.succ hilast).symm

private theorem exists_positive_prefix_action_minimum_of_spatial_minimum
    (H : ObservedHistory.{u}) (first last : Fin (H.eventCount + 1)) (hle : first ≤ last)
    {T B v : ℝ} (hv : 0 < v)
    (hupper : T ∈ Icc (H.time last) (H.stageEndTime last))
    (hpast : T - v ^ 2 ∈ Ioo (H.time first) (H.stageEndTime first))
    (gamma : (j : H.StageInterval first last) → ℝ → (H.stage j.val).Carrier)
    (hAC : ∀ j, Manifold.absolutelyContinuousOnInterval ThreeModel (gamma j)
      (H.regularizedStageStart T 0 j.val) (H.regularizedStageEnd T v j.val))
    (hInt : ∀ j, IntervalIntegrable (H.stageRegularizedLagrangian j.val T (gamma j)) volume
      (H.regularizedStageStart T 0 j.val) (H.regularizedStageEnd T v j.val))
    (hNodes : ∀ (i : Fin H.eventCount) (hf : first ≤ i.castSucc) (hl : i.succ ≤ last),
      ∃ z : (H.event i).old,
        z.val.val = gamma ⟨i.castSucc, hf, i.castSucc_le_succ.trans hl⟩
          (Real.sqrt (T - H.time i.succ)) ∧
        (H.event i).oldOutput z = gamma ⟨i.succ, hf.trans i.castSucc_le_succ, hl⟩
          (Real.sqrt (T - H.time i.succ)))
    (hscalar : ∀ j : H.StageInterval first last,
      ∀ r ∈ Ioo (H.regularizedStageStart T 0 j.val) (H.regularizedStageEnd T v j.val),
      ∀ x : (H.stage j.val).Carrier, -B ≤ metricScalarAt (H.stageMetric j.val (T - r ^ 2)) x)
    (hminimum : ∀ q : (H.stage first).Carrier,
      (((∑ j : H.StageInterval first last, H.stageRegularizedAction j.val T (gamma j)
        (H.regularizedStageStart T 0 j.val) (H.regularizedStageEnd T v j.val)) : ℝ) : WithTop ℝ) ≤
      H.regularizedCost first last hle T B 0 v (gamma ⟨last, hle, le_rfl⟩ 0) q) :
    H.regularizedExtendedAction first last T B 0 v gamma =
      H.regularizedCost first last hle T B 0 v (gamma ⟨last, hle, le_rfl⟩ 0)
        (gamma ⟨first, le_rfl, hle⟩ v) ∧
    ∃ (cut : Fin (H.eventCount + 1)) (hfc : first ≤ cut) (hcl : cut ≤ last),
      H.regularizedStageStart T 0 cut = 0 ∧ H.regularizedStageEnd T v first = v ∧
      T ∈ Ioc (H.time cut) (H.stageEndTime cut) ∧
      (∀ j : H.StageInterval first cut,
        H.regularizedStageStart T 0 j.val < H.regularizedStageEnd T v j.val) ∧
      (∀ j : H.StageInterval first last, cut < j.val →
        H.regularizedStageStart T 0 j.val = H.regularizedStageEnd T v j.val) ∧
      let gammaCut : (j : H.StageInterval first cut) → ℝ → (H.stage j.val).Carrier :=
        fun j => gamma ⟨j.val, j.property.1, j.property.2.trans hcl⟩;
      ∀ delta : (j : H.StageInterval first cut) → ℝ → (H.stage j.val).Carrier,
        (∀ j, Manifold.absolutelyContinuousOnInterval ThreeModel (delta j)
          (H.regularizedStageStart T 0 j.val) (H.regularizedStageEnd T v j.val)) →
        (∀ j, IntervalIntegrable (H.stageRegularizedLagrangian j.val T (delta j)) volume
          (H.regularizedStageStart T 0 j.val) (H.regularizedStageEnd T v j.val)) →
        delta ⟨cut, hfc, le_rfl⟩ 0 = gammaCut ⟨cut, hfc, le_rfl⟩ 0 →
        (∀ (i : Fin H.eventCount) (hf : first ≤ i.castSucc) (hl : i.succ ≤ cut),
          ∃ z : (H.event i).old,
            z.val.val = delta ⟨i.castSucc, hf, i.castSucc_le_succ.trans hl⟩
              (Real.sqrt (T - H.time i.succ)) ∧
            (H.event i).oldOutput z = delta ⟨i.succ, hf.trans i.castSucc_le_succ, hl⟩
              (Real.sqrt (T - H.time i.succ))) →
        (∑ j : H.StageInterval first cut, H.stageRegularizedAction j.val T (gammaCut j)
          (H.regularizedStageStart T 0 j.val) (H.regularizedStageEnd T v j.val)) ≤
        (∑ j : H.StageInterval first cut, H.stageRegularizedAction j.val T (delta j)
          (H.regularizedStageStart T 0 j.val) (H.regularizedStageEnd T v j.val)) := by
  have hupper0 : T - (0 : ℝ) ^ 2 ∈ Icc (H.time last) (H.stageEndTime last) := by
    simpa only [zero_pow two_ne_zero, sub_zero] using hupper
  have hpastD := H.mem_stageDomain_of_mem_Ioo hpast
  have hfull := H.regularizedExtendedAction_eq_sum_action first last le_rfl hv.le hupper0 hpastD
    gamma hInt (fun j => by
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
      exact hscalar j r hr (gamma j r))
  have hmember : H.regularizedExtendedAction first last T B 0 v gamma ∈
      H.regularizedActionValues first last hle T B 0 v
        (gamma ⟨last, hle, le_rfl⟩ 0) (gamma ⟨first, le_rfl, hle⟩ v) :=
    ⟨le_rfl, hv.le, hupper0, hpastD, gamma, hAC, rfl, rfl, hNodes, rfl⟩
  have hcost : H.regularizedCost first last hle T B 0 v
      (gamma ⟨last, hle, le_rfl⟩ 0) (gamma ⟨first, le_rfl, hle⟩ v) =
      (((∑ j : H.StageInterval first last, H.stageRegularizedAction j.val T (gamma j)
        (H.regularizedStageStart T 0 j.val) (H.regularizedStageEnd T v j.val)) : ℝ) : WithTop ℝ) :=
    le_antisymm ((H.regularizedCost_le_of_competitor first last hle T B 0 v _ _ hmember).trans_eq hfull)
      (hminimum _)
  refine ⟨hfull.trans hcost.symm, ?_⟩
  obtain ⟨cut, hfc, hcl, hchar, hpole, hstart, hend, hpos, hzero, _⟩ :=
    H.exists_positive_regularized_stage_interval first last hle hv hupper hpast
  have hcutUpper : T ∈ Ioc (H.time cut) (H.stageEndTime cut) := by
    by_cases hT : H.time last < T
    · simpa only [hchar.mpr hT] using
        (show T ∈ Ioc (H.time last) (H.stageEndTime last) from ⟨hT, hupper.2⟩)
    · have hT0 : T = H.time last := le_antisymm (le_of_not_gt hT) hupper.1
      obtain ⟨i, hlast, hcut⟩ := hpole hT0
      simp only [hcut, H.stageEndTime_castSucc, hT0, hlast]
      exact ⟨H.time_strictMono i.castSucc_lt_succ, le_rfl⟩
  refine ⟨cut, hfc, hcl, hstart, hend, hcutUpper,
    (fun j => hpos j.val j.property.1 j.property.2),
    (fun j hj => ((hzero j.val j.property.2 hj).2.1).trans
      ((hzero j.val j.property.2 hj).2.2).symm), ?_⟩
  by_cases hT : H.time last < T
  · have heq := hchar.mpr hT
    subst cut
    intro gammaCut delta hdeltaAC hdeltaInt hrecent hdeltaNodes
    have hdMember : H.regularizedExtendedAction first last T B 0 v delta ∈
        H.regularizedActionValues first last hle T B 0 v
          (gamma ⟨last, hle, le_rfl⟩ 0) (delta ⟨first, le_rfl, hle⟩ v) :=
      ⟨le_rfl, hv.le, hupper0, hpastD, delta, hdeltaAC, hrecent, rfl, hdeltaNodes, rfl⟩
    have hh := (hminimum (delta ⟨first, le_rfl, hle⟩ v)).trans
      (H.regularizedCost_le_of_competitor first last hle T B 0 v _ _ hdMember)
    rw [H.regularizedExtendedAction_eq_sum_action first last le_rfl hv.le hupper0 hpastD
      delta hdeltaInt (fun j => by
        filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
        exact hscalar j r hr (delta j r))] at hh
    exact WithTop.coe_le_coe.mp hh
  · have hT0 : T = H.time last := le_antisymm (le_of_not_gt hT) hupper.1
    obtain ⟨i, hlast, hcut⟩ := hpole hT0
    subst last
    subst cut
    subst T
    have hminimal := H.restriction_action_minimal_at_zero_pole_of_spatial_cost_minimum first i
      hfc hv.le hpastD gamma hAC hInt hNodes hscalar hcost (fun q => hcost ▸ hminimum q)
    exact hminimal.2

private theorem exists_smooth_terminal_stage_piece
    (H : ObservedHistory.{u}) (first last : Fin (H.eventCount + 1)) (hle : first ≤ last)
    {T B v : ℝ} (hv : 0 < v)
    (hupper : T ∈ Icc (H.time last) (H.stageEndTime last))
    (hpast : T - v ^ 2 ∈ Ioo (H.time first) (H.stageEndTime first))
    (hscalar : ∀ j : H.StageInterval first last,
      ∀ r ∈ Ioo (H.regularizedStageStart T 0 j.val) (H.regularizedStageEnd T v j.val),
      ∀ x : (H.stage j.val).Carrier, -B ≤ metricScalarAt (H.stageMetric j.val (T - r ^ 2)) x)
    (gamma : (j : H.StageInterval first last) → ℝ → (H.stage j.val).Carrier)
    (hgammaAC : ∀ j, Manifold.absolutelyContinuousOnInterval ThreeModel (gamma j)
      (H.regularizedStageStart T 0 j.val) (H.regularizedStageEnd T v j.val))
    (hgammaInt : ∀ j, IntervalIntegrable (H.stageRegularizedLagrangian j.val T (gamma j)) volume
      (H.regularizedStageStart T 0 j.val) (H.regularizedStageEnd T v j.val))
    (hgammaNodes : ∀ (i : Fin H.eventCount) (hf : first ≤ i.castSucc) (hl : i.succ ≤ last),
      ∃ z : (H.event i).old,
        z.val.val = gamma ⟨i.castSucc, hf, i.castSucc_le_succ.trans hl⟩
          (Real.sqrt (T - H.time i.succ)) ∧
        (H.event i).oldOutput z = gamma ⟨i.succ, hf.trans i.castSucc_le_succ, hl⟩
          (Real.sqrt (T - H.time i.succ)))
    (hmin : H.regularizedExtendedAction first last T B 0 v gamma =
      H.regularizedCost first last hle T B 0 v
        (gamma ⟨last, hle, le_rfl⟩ 0) (gamma ⟨first, le_rfl, hle⟩ v))
    (hC1 : ContMDiffAt 𝓘(ℝ, ℝ) ThreeModel 1 (gamma ⟨first, le_rfl, hle⟩) v) :
    ∃ (D : RealTimeInterval)
      (S : SolutionOn (I := ThreeModel) (M := (H.stage first).Carrier) D),
      IsSolutionOn S ∧
      (∀ t, S.base.metric t = H.stageMetric first t) ∧
      (∀ (eta : ℝ → (H.stage first).Carrier) (r : ℝ),
        H.stageRegularizedLagrangian first T eta r = lRegularizedLagrangian S T eta r) ∧
      (∀ (eta : ℝ → (H.stage first).Carrier) (c d : ℝ),
        H.stageRegularizedAction first T eta c d = lRegularizedAction S T eta c d) ∧
      T - v ^ 2 ∈ D.regular ∧
      ∃ cTail b lo hi : ℝ,
        cTail ∈ Ioo (H.regularizedStageStart T 0 first) v ∧
        max cTail ((H.regularizedStageStart T 0 first +
          H.regularizedStageEnd T v first) / 2) < b ∧ b < v ∧ 0 < b ∧
        lo < b ∧ v < hi ∧
        (∀ r ∈ Ioo lo hi, T - r ^ 2 ∈ D.regular) ∧
        ∃ beta : ℝ → (H.stage first).Carrier,
          ContMDiff 𝓘(ℝ, ℝ) ThreeModel ∞ beta ∧
          IsLRegularizedGeodesicOn S T beta (Icc b v) ∧
          EqOn beta (gamma ⟨first, le_rfl, hle⟩) (Icc b v) ∧
          beta =ᶠ[𝓝 b] gamma ⟨first, le_rfl, hle⟩ ∧
          beta v = gamma ⟨first, le_rfl, hle⟩ v ∧
          lVelocity (I := ThreeModel) beta v =
            lVelocity (I := ThreeModel) (gamma ⟨first, le_rfl, hle⟩) v ∧
          lRegularizedAction S T beta b v =
            H.stageRegularizedAction first T (gamma ⟨first, le_rfl, hle⟩) b v := by
  have hpastD := H.mem_stageDomain_of_mem_Ioo hpast
  have hupper0 : T - (0 : ℝ) ^ 2 ∈ Icc (H.time last) (H.stageEndTime last) := by
    simpa only [zero_pow two_ne_zero, sub_zero] using hupper
  have hend : H.regularizedStageEnd T v first = v :=
    H.regularizedStageEnd_eq_of_mem_stageDomain hv.le hpastD
  have hstartV : H.regularizedStageStart T 0 first < v := by
    have hg : T - v ^ 2 < min T (H.stageEndTime first) :=
      lt_min (sub_lt_self T (sq_pos_of_pos hv)) hpast.2
    have hs := Real.sqrt_lt_sqrt
      (sub_nonneg.mpr (min_le_left T (H.stageEndTime first)))
      (show T - min T (H.stageEndTime first) < v ^ 2 by linarith)
    simpa only [regularizedStageStart, zero_pow two_ne_zero, sub_zero,
      Real.sqrt_sq_eq_abs, abs_of_pos hv] using hs
  obtain ⟨D, S, hS, hmetric, hlag, hregv, hgeo⟩ :
      ∃ (D : RealTimeInterval)
        (S : SolutionOn (I := ThreeModel) (M := (H.stage first).Carrier) D),
        IsSolutionOn S ∧
        (∀ t, S.base.metric t = H.stageMetric first t) ∧
        (∀ (eta : ℝ → (H.stage first).Carrier) (r : ℝ),
          H.stageRegularizedLagrangian first T eta r = lRegularizedLagrangian S T eta r) ∧
        T - v ^ 2 ∈ D.regular ∧
        IsLRegularizedGeodesicOn S T (gamma ⟨first, le_rfl, hle⟩)
          (Ioo (H.regularizedStageStart T 0 first) (H.regularizedStageEnd T v first)) := by
    cases first using Fin.lastCases with
    | last =>
      have hfinal : H.time (Fin.last H.eventCount) < H.horizon := by
        simpa only [H.stageEndTime_last] using hpast.1.trans hpast.2
      have hlast : last = Fin.last H.eventCount := le_antisymm (Fin.le_last last) hle
      subst last
      refine ⟨_, (H.finalSlab hfinal).flow, (H.finalSlab hfinal).equation, ?_,
        H.stageRegularizedLagrangian_last hfinal T, ?_, ?_⟩
      · intro t
        simp only [stageMetric, Fin.lastCases_last, dite_eq_left hfinal]
      · simpa only [RealTimeInterval.closed, RealTimeInterval.regular,
          H.stageEndTime_last] using hpast
      · exact H.regularizedGeodesicOn_final_stage_of_regularizedExtendedAction_eq_regularizedCost
          (Fin.last H.eventCount) hfinal le_rfl hv.le
          (by simpa only [H.stageEndTime_last] using hupper0) hpastD hscalar gamma
          hgammaAC hgammaInt (fun i hf => hgammaNodes i hf (Fin.le_last _)) hmin
    | cast i =>
      refine ⟨_, (H.event i).incoming.flow, (H.event i).incoming.equation, ?_,
        H.stageRegularizedLagrangian_castSucc i T, ?_, ?_⟩
      · intro t
        simp only [stageMetric, Fin.lastCases_castSucc]
      · simpa only [RealTimeInterval.closedOpen, RealTimeInterval.regular,
          H.stageEndTime_castSucc] using hpast
      · exact H.regularizedGeodesicOn_incoming_stage_of_regularizedExtendedAction_eq_regularizedCost
          i.castSucc last hle le_rfl hv.le hupper0 hpastD hscalar gamma hgammaAC hgammaInt
          hgammaNodes hmin i le_rfl hle
  have haction (eta : ℝ → (H.stage first).Carrier) (c d : ℝ) :
      H.stageRegularizedAction first T eta c d = lRegularizedAction S T eta c d := by
    unfold stageRegularizedAction lRegularizedAction
    exact intervalIntegral.integral_congr (fun r _ => hlag eta r)
  rw [hend] at hgeo
  obtain ⟨cTail, hcTail, U, hU, hsub, xi, hxi, hxiGeo, hxiEq, hxiVel⟩ :=
    exists_lRegularizedGeodesic_smooth_tail_on_Ioo_of_contMDiffAt_one
      S hS T hstartV hC1 hregv hgeo
  let m := (H.regularizedStageStart T 0 first + H.regularizedStageEnd T v first) / 2
  have hmV : m < v := by dsimp only [m]; rw [hend]; linarith
  have hmaxV : max cTail m < v := max_lt hcTail.2 hmV
  let b := (max cTail m + v) / 2
  have hmaxb : max cTail m < b := by dsimp only [b]; linarith
  have hbV : b < v := by dsimp only [b]; linarith
  have hcTailb : cTail < b := (le_max_left _ _).trans_lt hmaxb
  have hb0 : 0 < b :=
    (Real.sqrt_nonneg _).trans_lt (hcTail.1.trans hcTailb)
  let V := (fun t : ℝ => b + t) ⁻¹' U
  have hV : IsOpen V := hU.preimage (continuous_const.add continuous_id)
  have hseg : Icc (0 : ℝ) (v - b) ⊆ V := by
    intro t ht
    apply hsub
    exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have htranslated : ContMDiffOn 𝓘(ℝ, ℝ) ThreeModel ∞ (fun t => xi (b + t)) V :=
    hxi.comp (contMDiff_const.add contMDiff_id).contMDiffOn (fun _ ht => ht)
  obtain ⟨eta, heta, hetaEq⟩ :=
    DifferentialGeometry.Topology.Manifold.exists_global_smooth_curve_eq_near_interval
      (sub_nonneg.mpr hbV.le) hV hseg htranslated
  let beta : ℝ → (H.stage first).Carrier := fun t => eta (t - b)
  have hbeta : ContMDiff 𝓘(ℝ, ℝ) ThreeModel ∞ beta :=
    heta.comp (contMDiff_id.sub contMDiff_const)
  have hbetaXi (r : ℝ) (hr : r ∈ Icc b v) : beta =ᶠ[𝓝 r] xi := by
    have heq := (hetaEq (r - b) ⟨by linarith [hr.1], by linarith [hr.2]⟩).comp_tendsto
      (continuous_id.sub continuous_const).continuousAt.tendsto
    filter_upwards [heq] with t ht
    change eta (t - b) = xi (b + (t - b)) at ht
    simpa only [beta, show b + (t - b) = t by ring] using ht
  have hxiGeoClosed : IsLRegularizedGeodesicOn S T xi (Icc b v) :=
    fun r hr => hxiGeo r (hsub ⟨hcTailb.le.trans hr.1, hr.2⟩)
  have hbetaGeo : IsLRegularizedGeodesicOn S T beta (Icc b v) :=
    hxiGeoClosed.congr_of_eventuallyEq hbetaXi
  have hbetaEq : EqOn beta (gamma ⟨first, le_rfl, hle⟩) (Icc b v) :=
    fun r hr => (hbetaXi r hr).self_of_nhds.trans (hxiEq ⟨hcTailb.le.trans hr.1, hr.2⟩)
  have hxiGerm : xi =ᶠ[𝓝 b] gamma ⟨first, le_rfl, hle⟩ := by
    filter_upwards [Ioo_mem_nhds hcTailb hbV] with r hr
    exact hxiEq (Ioo_subset_Icc_self hr)
  have hvel : lVelocity (I := ThreeModel) beta v =
      lVelocity (I := ThreeModel) (gamma ⟨first, le_rfl, hle⟩) v := by
    have hm := (hbetaXi v ⟨hbV.le, le_rfl⟩).mfderiv_eq (I := 𝓘(ℝ, ℝ)) (I' := ThreeModel)
    have hbx : lVelocity (I := ThreeModel) beta v = lVelocity (I := ThreeModel) xi v := by
      exact congrArg (fun A => A (1 : ℝ)) hm
    exact hbx.trans hxiVel
  obtain ⟨epsilon, hepsilon, hepsilonU⟩ :=
    DifferentialGeometry.Topology.Manifold.exists_interval_margin
      (sub_nonneg.mpr hbV.le) hV hseg
  let lo := b - epsilon
  let hi := v + epsilon
  have hclock (r : ℝ) (hr : r ∈ Ioo lo hi) : T - r ^ 2 ∈ D.regular := by
    have hrV : r - b ∈ V := hepsilonU ⟨by dsimp only [lo] at hr; linarith [hr.1],
      by dsimp only [hi] at hr; linarith [hr.2]⟩
    have hrU : r ∈ U := by
      change b + (r - b) ∈ U at hrV
      simpa only [show b + (r - b) = r by ring] using hrV
    exact (hxiGeo r hrU).1
  refine ⟨D, S, hS, hmetric, hlag, haction, hregv, cTail, b, lo, hi, hcTail,
    hmaxb, hbV, hb0, by dsimp only [lo]; linarith,
    by dsimp only [hi]; linarith, hclock, beta, hbeta, hbetaGeo, hbetaEq,
    (hbetaXi b ⟨le_rfl, hbV.le⟩).trans hxiGerm,
    hbetaEq ⟨hbV.le, le_rfl⟩, hvel, ?_⟩
  rw [haction]
  apply lRegularizedAction_congr
  intro r hr
  rw [uIoo_of_le hbV.le] at hr
  exact hbetaEq (Ioo_subset_Icc_self hr)

private theorem exists_separated_positive_event_collars
    (H : ObservedHistory.{u}) (first last : Fin (H.eventCount + 1))
    {T v b : ℝ} (hb : b ∈ Ioo 0 v)
    (hupper : T ∈ Icc (H.time last) (H.stageEndTime last))
    (hpast : T - v ^ 2 ∈ H.stageDomain first) :
    let E := {i : Fin H.eventCount //
      first ≤ i.castSucc ∧ i.succ ≤ last ∧ 0 < Real.sqrt (T - H.time i.succ)};
    ∀ c0 d0 : E → ℝ,
      (∀ i, H.regularizedStageStart T 0 i.val.succ < c0 i ∧
        c0 i < Real.sqrt (T - H.time i.val.succ) ∧
        Real.sqrt (T - H.time i.val.succ) < d0 i ∧
        d0 i < H.regularizedStageEnd T v i.val.castSucc) →
      ∃ (c d : E → ℝ) (a0 : ℝ), 0 < a0 ∧ a0 < b ∧
        (∀ i, a0 < c i ∧ c i < Real.sqrt (T - H.time i.val.succ) ∧
          Real.sqrt (T - H.time i.val.succ) < d i ∧
          Icc (c i) (d i) ⊆ Ioo (c0 i) (d0 i) ∧
          (H.regularizedStageStart T 0 i.val.succ +
            H.regularizedStageEnd T v i.val.succ) / 2 < c i ∧
          d i < (H.regularizedStageStart T 0 i.val.castSucc +
            H.regularizedStageEnd T v i.val.castSucc) / 2 ∧
          T - (c i) ^ 2 ∈ Ioo (H.time i.val.succ) (H.stageEndTime i.val.succ) ∧
          T - (d i) ^ 2 ∈ Ioo (H.time i.val.castSucc) (H.stageEndTime i.val.castSucc)) ∧
        (∀ i j, i.val < j.val → d j < c i) ∧
        Pairwise (fun i j => Disjoint (Icc (c i) (d i)) (Icc (c j) (d j))) ∧
        ∀ a ∈ Ioo 0 a0, ∀ (i : Fin H.eventCount),
          first ≤ i.castSucc → i.succ ≤ last → a ≠ Real.sqrt (T - H.time i.succ) := by
  classical
  intro E c0 d0 hcollar
  let m (j : Fin (H.eventCount + 1)) :=
    (H.regularizedStageStart T 0 j + H.regularizedStageEnd T v j) / 2
  let w (i : E) := Real.sqrt (T - H.time i.val.succ)
  have hupper0 : T - (0 : ℝ) ^ 2 ∈ Icc (H.time last) (H.stageEndTime last) := by
    simpa only [zero_pow two_ne_zero, sub_zero] using hupper
  have hnew (i : E) : H.regularizedStageEnd T v i.val.succ = w i :=
    H.regularizedStageEnd_succ_eq_event_clock hpast i.val i.property.1
  have hold (i : E) : H.regularizedStageStart T 0 i.val.castSucc = w i :=
    H.regularizedStageStart_castSucc_eq_event_clock hupper0 i.val i.property.2.1
  have hmnew (i : E) : m i.val.succ < w i := by
    have hh := (hcollar i).1.trans (hcollar i).2.1
    change H.regularizedStageStart T 0 i.val.succ < w i at hh
    dsimp only [m]
    rw [hnew]
    linarith
  have hmold (i : E) : w i < m i.val.castSucc := by
    have hh := (hcollar i).2.2.1.trans (hcollar i).2.2.2
    change w i < H.regularizedStageEnd T v i.val.castSucc at hh
    dsimp only [m]
    rw [hold]
    linarith
  let c (i : E) := (max (c0 i) (m i.val.succ) + w i) / 2
  let d (i : E) := (w i + min (d0 i) (m i.val.castSucc)) / 2
  have hc (i : E) : c0 i < c i ∧ m i.val.succ < c i ∧ c i < w i := by
    have hw : max (c0 i) (m i.val.succ) < w i :=
      max_lt (hcollar i).2.1 (hmnew i)
    have h0 := le_max_left (c0 i) (m i.val.succ)
    have hm := le_max_right (c0 i) (m i.val.succ)
    dsimp only [c]
    constructor
    · linarith
    constructor <;> linarith
  have hd (i : E) : w i < d i ∧ d i < d0 i ∧ d i < m i.val.castSucc := by
    have hw : w i < min (d0 i) (m i.val.castSucc) :=
      lt_min (hcollar i).2.2.1 (hmold i)
    have h0 := min_le_left (d0 i) (m i.val.castSucc)
    have hm := min_le_right (d0 i) (m i.val.castSucc)
    dsimp only [d]
    constructor
    · linarith
    constructor <;> linarith
  have hcpos (i : E) : 0 < c i :=
    (Real.sqrt_nonneg _).trans_lt ((hcollar i).1.trans (hc i).1)
  have hmanti : Antitone m := by
    intro j k hjk
    have hs : H.regularizedStageStart T 0 k ≤ H.regularizedStageStart T 0 j := by
      apply Real.sqrt_le_sqrt
      exact sub_le_sub_left (min_le_min_left _ (H.stageEndTime_mono hjk)) T
    have he : H.regularizedStageEnd T v k ≤ H.regularizedStageEnd T v j := by
      apply Real.sqrt_le_sqrt
      exact sub_le_sub_left (max_le_max_left _ (H.time_strictMono.monotone hjk)) T
    dsimp only [m]
    linarith
  have hsep (i j : E) (hij : i.val < j.val) : d j < c i := by
    have hstage : i.val.succ ≤ j.val.castSucc := by
      change i.val.val + 1 ≤ j.val.val
      exact hij
    exact (hd j).2.2.trans_le (hmanti hstage) |>.trans (hc i).2.1
  let values : Finset ℝ := insert b (Finset.univ.image c)
  have hne : values.Nonempty := Finset.insert_nonempty b _
  have hvalues : ∀ y ∈ values, 0 < y := by
    intro y hy
    rcases Finset.mem_insert.mp hy with rfl | hy
    · exact hb.1
    · obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hy
      exact hcpos i
  have hmin : 0 < values.min' hne := hvalues _ (Finset.min'_mem values hne)
  let a0 := values.min' hne / 2
  have ha0 : 0 < a0 := half_pos hmin
  have hab : a0 < b := by
    have hle := Finset.min'_le values b (Finset.mem_insert_self b _)
    dsimp only [a0]
    linarith
  have hac (i : E) : a0 < c i := by
    have hmem : c i ∈ values :=
      Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩)
    have hle := Finset.min'_le values (c i) hmem
    dsimp only [a0]
    linarith
  refine ⟨c, d, a0, ha0, hab, ?_, hsep, ?_, ?_⟩
  · intro i
    refine ⟨hac i, (hc i).2.2, (hd i).1, ?_, (hc i).2.1, (hd i).2.2, ?_, ?_⟩
    · intro r hr
      exact ⟨(hc i).1.trans_le hr.1, hr.2.trans_lt (hd i).2.1⟩
    · apply H.mapsTo_regularizedStage_Ioo_Ioo T 0 v i.val.succ
      exact ⟨(hcollar i).1.trans (hc i).1, (hc i).2.2.trans_eq (hnew i).symm⟩
    · apply H.mapsTo_regularizedStage_Ioo_Ioo T 0 v i.val.castSucc
      exact ⟨(hold i).trans_lt (hd i).1, (hd i).2.1.trans (hcollar i).2.2.2⟩
  · intro i j hij
    have hneval : i.val ≠ j.val := fun heq => hij (Subtype.ext heq)
    rcases lt_or_gt_of_ne hneval with hlt | hgt
    · apply Set.disjoint_left.mpr
      intro r hri hrj
      exact (not_le_of_gt (hsep i j hlt)) (hri.1.trans hrj.2)
    · apply Set.disjoint_left.mpr
      intro r hri hrj
      exact (not_le_of_gt (hsep j i hgt)) (hrj.1.trans hri.2)
  · intro a ha i hf hl
    by_cases hw : 0 < Real.sqrt (T - H.time i.succ)
    · let j : E := ⟨i, hf, hl, hw⟩
      exact ne_of_lt (ha.2.trans ((hac j).trans (hc j).2.2))
    · have hzero : Real.sqrt (T - H.time i.succ) = 0 :=
        le_antisymm (le_of_not_gt hw) (Real.sqrt_nonneg _)
      rw [hzero]
      exact ne_of_gt ha.1

private theorem exists_positive_prefix_survivor_collars
    (H : ObservedHistory.{u}) (first last : Fin (H.eventCount + 1)) (hle : first ≤ last)
    {T B v : ℝ} (hv : 0 < v)
    (hupper : T ∈ Icc (H.time last) (H.stageEndTime last))
    (hpast : T - v ^ 2 ∈ Ioo (H.time first) (H.stageEndTime first))
    (hscalar : ∀ j : H.StageInterval first last,
      ∀ r ∈ Ioo (H.regularizedStageStart T 0 j.val) (H.regularizedStageEnd T v j.val),
      ∀ x : (H.stage j.val).Carrier, -B ≤ metricScalarAt (H.stageMetric j.val (T - r ^ 2)) x)
    (gamma : (j : H.StageInterval first last) → ℝ → (H.stage j.val).Carrier)
    (hgammaAC : ∀ j, Manifold.absolutelyContinuousOnInterval ThreeModel (gamma j)
      (H.regularizedStageStart T 0 j.val) (H.regularizedStageEnd T v j.val))
    (hgammaInt : ∀ j, IntervalIntegrable (H.stageRegularizedLagrangian j.val T (gamma j)) volume
      (H.regularizedStageStart T 0 j.val) (H.regularizedStageEnd T v j.val))
    (hgammaNodes : ∀ (i : Fin H.eventCount) (hf : first ≤ i.castSucc) (hl : i.succ ≤ last),
      ∃ z : (H.event i).old,
        z.val.val = gamma ⟨i.castSucc, hf, i.castSucc_le_succ.trans hl⟩
          (Real.sqrt (T - H.time i.succ)) ∧
        (H.event i).oldOutput z = gamma ⟨i.succ, hf.trans i.castSucc_le_succ, hl⟩
          (Real.sqrt (T - H.time i.succ)))
    (hmin : H.regularizedExtendedAction first last T B 0 v gamma =
      H.regularizedCost first last hle T B 0 v
        (gamma ⟨last, hle, le_rfl⟩ 0) (gamma ⟨first, le_rfl, hle⟩ v))
    (cut : Fin (H.eventCount + 1)) (hcl : cut ≤ last)
    (hcut : T ∈ Ioc (H.time cut) (H.stageEndTime cut))
    (b : ℝ) (hb : b ∈ Ioo 0 v)
    (hmb : (H.regularizedStageStart T 0 first + H.regularizedStageEnd T v first) / 2 < b)
    (hcross : ∀ (i : Fin H.eventCount) (hf : first ≤ i.castSucc) (hl : i.succ ≤ cut),
      (H.event i).RegularCrossing
        (gamma ⟨i.castSucc, hf, i.castSucc_le_succ.trans (hl.trans hcl)⟩
          (Real.sqrt (T - H.time i.succ)))
        (gamma ⟨i.succ, hf.trans i.castSucc_le_succ, hl.trans hcl⟩
          (Real.sqrt (T - H.time i.succ)))) :
    let E := {i : Fin H.eventCount // first ≤ i.castSucc ∧ i.succ ≤ cut};
    let jo (i : E) : H.StageInterval first last :=
      ⟨i.val.castSucc, i.property.1, i.val.castSucc_le_succ.trans (i.property.2.trans hcl)⟩;
    let jn (i : E) : H.StageInterval first last :=
      ⟨i.val.succ, i.property.1.trans i.val.castSucc_le_succ, i.property.2.trans hcl⟩;
    ∃ (C D : E → ℝ) (hCs : ∀ i, C i < H.time i.val.succ)
      (hsD : ∀ i, H.time i.val.succ < D i)
      (W : (i : E) → TopologicalSpace.Opens (H.event i.val).incoming.terminalRegularOpen)
      (F : (i : E) → PartialDiffeomorph ThreeModel ThreeModel
        (H.event i.val).incoming.terminalRegularOpen (H.stage i.val.succ).Carrier ∞)
      (S : (i : E) → SolutionOn (I := ThreeModel) (M := W i)
        (RealTimeInterval.closed (C i) (D i) ((hCs i).trans (hsD i)).le))
      (hlocalOld : ∀ i, IsLocalDiffeomorph ThreeModel ThreeModel ∞ (fun z : W i => z.val.val))
      (hlocalNew : ∀ i, IsLocalDiffeomorph ThreeModel ThreeModel ∞ (fun z : W i => F i z.val))
      (c0 d0 : E → ℝ) (eta : (i : E) → ℝ → W i),
      (∀ i, 0 < Real.sqrt (T - H.time i.val.succ) ∧
        Real.sqrt (T - H.time i.val.succ) < v ∧
        H.time i.val.castSucc < C i ∧ D i < H.stageEndTime i.val.succ ∧
        (F i).source = W i ∧ IsSolutionOn (S i) ∧
        (∀ z : W i, (H.event i.val).RegularCrossing z.val.val (F i z.val)) ∧
        (∀ t ∈ Ico (C i) (H.time i.val.succ), (S i).base.metric t =
          localPullMetric (H.stageMetric i.val.castSucc t) (fun z : W i => z.val.val) (hlocalOld i)) ∧
        (∀ t ∈ Icc (H.time i.val.succ) (D i), (S i).base.metric t =
          localPullMetric (H.stageMetric i.val.succ t) (fun z : W i => F i z.val) (hlocalNew i)) ∧
        (S i).base.metric (H.time i.val.succ) = (H.event i.val).terminal.metric.restrictOpen (W i) ∧
        0 < c0 i ∧ c0 i < Real.sqrt (T - H.time i.val.succ) ∧
        Real.sqrt (T - H.time i.val.succ) < d0 i ∧ d0 i < v ∧
        H.regularizedStageStart T 0 i.val.succ < c0 i ∧
        d0 i < H.regularizedStageEnd T v i.val.castSucc ∧
        (∀ r ∈ Icc (c0 i) (d0 i), T - r ^ 2 ∈ Ioo (C i) (D i)) ∧
        Manifold.absolutelyContinuousOnInterval ThreeModel (eta i) (c0 i) (d0 i) ∧
        ContMDiffOn 𝓘(ℝ, ℝ) ThreeModel 1 (eta i) (Icc (c0 i) (d0 i)) ∧
        IsLRegularizedGeodesicOn (S i) T (eta i) (Ioo (c0 i) (d0 i)) ∧
        EqOn ((fun z : W i => F i z.val) ∘ eta i) (gamma (jn i))
          (Icc (c0 i) (Real.sqrt (T - H.time i.val.succ))) ∧
        EqOn ((fun z : W i => z.val.val) ∘ eta i) (gamma (jo i))
          (Icc (Real.sqrt (T - H.time i.val.succ)) (d0 i)) ∧
        IntervalIntegrable (lRegularizedLagrangian (S i) T (eta i)) volume (c0 i) (d0 i) ∧
        lRegularizedAction (S i) T (eta i) (c0 i) (d0 i) =
          H.stageRegularizedAction i.val.succ T (gamma (jn i)) (c0 i)
            (Real.sqrt (T - H.time i.val.succ)) +
          H.stageRegularizedAction i.val.castSucc T (gamma (jo i))
            (Real.sqrt (T - H.time i.val.succ)) (d0 i)) ∧
      ∃ (c d : E → ℝ) (a0 : ℝ), 0 < a0 ∧ a0 < b ∧
        (∀ i, a0 < c i ∧ c i < Real.sqrt (T - H.time i.val.succ) ∧
          Real.sqrt (T - H.time i.val.succ) < d i ∧ d i < b ∧
          Icc (c i) (d i) ⊆ Ioo (c0 i) (d0 i) ∧
          (H.regularizedStageStart T 0 i.val.succ + H.regularizedStageEnd T v i.val.succ) / 2 < c i ∧
          d i < (H.regularizedStageStart T 0 i.val.castSucc + H.regularizedStageEnd T v i.val.castSucc) / 2 ∧
          T - (c i) ^ 2 ∈ Ioo (H.time i.val.succ) (H.stageEndTime i.val.succ) ∧
          T - (d i) ^ 2 ∈ Ioo (H.time i.val.castSucc) (H.stageEndTime i.val.castSucc)) ∧
        (∀ i j, i.val < j.val → d j < c i) ∧
        Pairwise (fun i j => Disjoint (Icc (c i) (d i)) (Icc (c j) (d j))) := by
  classical
  intro E jo jn
  have hpastD := H.mem_stageDomain_of_mem_Ioo hpast
  have hupper0 : T - (0 : ℝ) ^ 2 ∈ Icc (H.time last) (H.stageEndTime last) := by
    simpa only [zero_pow two_ne_zero, sub_zero] using hupper
  have hw (i : E) : 0 < Real.sqrt (T - H.time i.val.succ) ∧
      Real.sqrt (T - H.time i.val.succ) < v := by
    have htime : H.time i.val.succ < T :=
      (H.time_strictMono.monotone i.property.2).trans_lt hcut.1
    have hp : T - v ^ 2 < H.time i.val.succ := by
      simpa only [H.stageEndTime_castSucc] using
        hpast.2.trans_le (H.stageEndTime_mono i.property.1)
    refine ⟨Real.sqrt_pos.mpr (sub_pos.mpr htime), ?_⟩
    have hh := Real.sqrt_lt_sqrt (sub_nonneg.mpr htime.le)
      (show T - H.time i.val.succ < v ^ 2 by linarith)
    simpa only [Real.sqrt_sq_eq_abs, abs_of_pos hv] using hh
  have hproducer (i : E) :=
    H.exists_regularizedGeodesic_survivor_lift_of_regularizedExtendedAction_eq_regularizedCost
      first last hle le_rfl hupper0 hpastD hscalar gamma hgammaAC hgammaInt hgammaNodes hmin
      i.val i.property.1 (i.property.2.trans hcl) (hw i).1 (hw i).2
      (hcross i.val i.property.1 i.property.2)
  choose C D hCs hsD W F S hlocalOld hlocalNew htimeOld htimeNew hsource hS hcrossW
    hmetricOld hmetricNew hterminal c0 d0 hc0 hcw hwd hd0 hclipNew hclipOld hclock
    eta hAC hC1 hgeo hnew hold hint haction using hproducer
  refine ⟨C, D, hCs, hsD, W, F, S, hlocalOld, hlocalNew, c0, d0, eta, ?_, ?_⟩
  · intro i
    exact ⟨(hw i).1, (hw i).2, htimeOld i, htimeNew i, hsource i, hS i, hcrossW i,
      hmetricOld i, hmetricNew i, hterminal i, hc0 i, hcw i, hwd i, hd0 i, hclipNew i,
      hclipOld i, hclock i, hAC i, hC1 i, hgeo i, hnew i, hold i, hint i, haction i⟩
  · let EP := {i : Fin H.eventCount //
        first ≤ i.castSucc ∧ i.succ ≤ cut ∧ 0 < Real.sqrt (T - H.time i.succ)}
    let ep : E ≃ EP :=
      { toFun := fun i => ⟨i.val, i.property.1, i.property.2, (hw i).1⟩
        invFun := fun i => ⟨i.val, i.property.1, i.property.2.1⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    obtain ⟨cP, dP, a0, ha0, hab, hcollar, hsep, hdisj, _⟩ :=
      H.exists_separated_positive_event_collars first cut hb ⟨hcut.1.le, hcut.2⟩ hpastD
        (fun i => c0 (ep.symm i)) (fun i => d0 (ep.symm i))
        (fun i => ⟨hclipNew (ep.symm i), hcw (ep.symm i), hwd (ep.symm i), hclipOld (ep.symm i)⟩)
    let c : E → ℝ := fun i => cP (ep i)
    let d : E → ℝ := fun i => dP (ep i)
    have hmid (i : E) :
        (H.regularizedStageStart T 0 i.val.castSucc + H.regularizedStageEnd T v i.val.castSucc) / 2 < b := by
      have hs : H.regularizedStageStart T 0 i.val.castSucc ≤ H.regularizedStageStart T 0 first := by
        apply Real.sqrt_le_sqrt
        exact sub_le_sub_left (min_le_min_left _ (H.stageEndTime_mono i.property.1)) T
      have he : H.regularizedStageEnd T v i.val.castSucc ≤ H.regularizedStageEnd T v first := by
        apply Real.sqrt_le_sqrt
        exact sub_le_sub_left (max_le_max_left _ (H.time_strictMono.monotone i.property.1)) T
      linarith
    refine ⟨c, d, a0, ha0, hab, ?_, ?_, ?_⟩
    · intro i
      have hi := hcollar (ep i)
      simp only [ep.symm_apply_apply] at hi
      exact ⟨hi.1, hi.2.1, hi.2.2.1, hi.2.2.2.2.2.1.trans (hmid i),
        hi.2.2.2⟩
    · intro i j hij
      exact hsep (ep i) (ep j) hij
    · intro i j hij
      exact hdisj (fun heq => hij (ep.injective heq))

private theorem action_scalar_bound_of_finite_weighted_action_bounds
    {ι : Type*} [Fintype ι] (L : ι → ℝ → ℝ) (l r : ι → ℝ)
    (hl : ∀ i, 0 ≤ l i) (hlr : ∀ i, l i < r i)
    (hL : ∀ i, IntervalIntegrable (L i) volume (l i) (r i)) (v R n : ℝ)
    (hbound : ∀ᶠ a in 𝓝[>] (0 : ℝ),
      (∑ i, ∫ t in max a (l i)..r i, (1 - a ^ 2 / t ^ 2) * L i t) +
        2 * v * R * (v - a) ^ 2 ≤ 2 * n * (v - a)) :
    (∑ i, ∫ t in l i..r i, L i t) + 2 * v ^ 3 * R ≤ 2 * n * v := by
  have hsum := tendsto_finsetSum Finset.univ
    (fun i _ => intervalIntegral.tendsto_integral_one_sub_sq_div_sq_mul (hl i) (hlr i) (hL i))
  have hid : Tendsto (fun a : ℝ => a) (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have hden : Tendsto (fun a : ℝ => v - a) (𝓝[>] (0 : ℝ)) (𝓝 v) := by
    simpa only [sub_zero] using tendsto_const_nhds.sub hid
  have hleft := hsum.add ((hden.pow 2).const_mul (2 * v * R))
  have hright := hden.const_mul (2 * n)
  have h := le_of_tendsto_of_tendsto hleft hright hbound
  have heq : (2 * v * R) * v ^ 2 = 2 * v ^ 3 * R := by ring
  simpa only [heq] using h

private theorem regularizedStageStart_eq_max_zero
    (H : ObservedHistory) (T : ℝ) {a : ℝ} (ha : 0 ≤ a)
    (j : Fin (H.eventCount + 1)) :
    H.regularizedStageStart T a j = max a (H.regularizedStageStart T 0 j) := by
  have hmono : Monotone Real.sqrt := fun _ _ h => Real.sqrt_le_sqrt h
  simp only [regularizedStageStart, ← max_sub_sub_left, sub_sub_cancel, hmono.map_max,
    Real.sqrt_sq ha, zero_pow two_ne_zero, Real.sqrt_zero]
  rw [← max_assoc, max_eq_left ha]

private theorem sum_action_scalar_bound_of_weighted_stage_bounds
    (H : ObservedHistory) (first last : Fin (H.eventCount + 1)) (T v R n : ℝ)
    (gamma : (j : H.StageInterval first last) → ℝ → (H.stage j.val).Carrier)
    (hpos : ∀ j : H.StageInterval first last,
      H.regularizedStageStart T 0 j.val < H.regularizedStageEnd T v j.val)
    (hInt : ∀ j : H.StageInterval first last,
      IntervalIntegrable (H.stageRegularizedLagrangian j.val T (gamma j)) volume
        (H.regularizedStageStart T 0 j.val) (H.regularizedStageEnd T v j.val))
    (hbound : ∀ᶠ a in 𝓝[>] (0 : ℝ),
      (∑ j : H.StageInterval first last,
        ∫ r in H.regularizedStageStart T a j.val..H.regularizedStageEnd T v j.val,
          (1 - a ^ 2 / r ^ 2) * H.stageRegularizedLagrangian j.val T (gamma j) r) +
        2 * v * R * (v - a) ^ 2 ≤ 2 * n * (v - a)) :
    (∑ j : H.StageInterval first last,
      H.stageRegularizedAction j.val T (gamma j)
        (H.regularizedStageStart T 0 j.val) (H.regularizedStageEnd T v j.val)) +
        2 * v ^ 3 * R ≤ 2 * n * v := by
  apply action_scalar_bound_of_finite_weighted_action_bounds
    (fun j : H.StageInterval first last => H.stageRegularizedLagrangian j.val T (gamma j))
    (fun j : H.StageInterval first last => H.regularizedStageStart T 0 j.val)
    (fun j : H.StageInterval first last => H.regularizedStageEnd T v j.val)
    (fun _ => Real.sqrt_nonneg _) hpos hInt v R n
  filter_upwards [self_mem_nhdsWithin, hbound] with a ha hba
  simpa only [H.regularizedStageStart_eq_max_zero T ha.le] using hba

private theorem sum_stage_action_eq_of_collapsed_suffix
    (H : ObservedHistory) (first last cut : Fin (H.eventCount + 1))
    (hcut : cut ≤ last) (T u v : ℝ)
    (gamma : (j : H.StageInterval first last) → ℝ → (H.stage j.val).Carrier)
    (hcollapsed : ∀ j : H.StageInterval first last, cut < j.val →
      H.regularizedStageStart T u j.val = H.regularizedStageEnd T v j.val) :
    (∑ j : H.StageInterval first last,
      H.stageRegularizedAction j.val T (gamma j)
        (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val)) =
      ∑ j : H.StageInterval first cut,
        H.stageRegularizedAction j.val T
          (gamma ⟨j.val, j.property.1, j.property.2.trans hcut⟩)
          (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val) := by
  classical
  let A : H.StageInterval first last → ℝ := fun j =>
    H.stageRegularizedAction j.val T (gamma j)
      (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val)
  let e : {j : H.StageInterval first last // j.val ≤ cut} ≃ H.StageInterval first cut :=
    { toFun := fun j => ⟨j.val.val, j.val.property.1, j.property⟩
      invFun := fun j => ⟨⟨j.val, j.property.1, j.property.2.trans hcut⟩, j.property.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hsum := Fintype.sum_equiv e (fun j => A j.val)
    (fun j => A ⟨j.val, j.property.1, j.property.2.trans hcut⟩) (fun _ => rfl)
  have hzero : (∑ j : {j : H.StageInterval first last // ¬j.val ≤ cut}, A j.val) = 0 := by
    apply Finset.sum_eq_zero
    intro j _
    dsimp only [A]
    rw [hcollapsed j.val (lt_of_not_ge j.property)]
    exact intervalIntegral.integral_same
  change (∑ j, A j) = _
  rw [← Fintype.sum_subtype_add_sum_subtype (fun j : H.StageInterval first last => j.val ≤ cut) A,
    hsum, hzero, add_zero]

private theorem sum_action_scalar_bound_of_positive_prefix_weighted_bounds
    (H : ObservedHistory) (first last cut : Fin (H.eventCount + 1))
    (hcut : cut ≤ last) (T v R n : ℝ)
    (gamma : (j : H.StageInterval first last) → ℝ → (H.stage j.val).Carrier)
    (hpos : ∀ j : H.StageInterval first cut,
      H.regularizedStageStart T 0 j.val < H.regularizedStageEnd T v j.val)
    (hcollapsed : ∀ j : H.StageInterval first last, cut < j.val →
      H.regularizedStageStart T 0 j.val = H.regularizedStageEnd T v j.val)
    (hInt : ∀ j : H.StageInterval first last,
      IntervalIntegrable (H.stageRegularizedLagrangian j.val T (gamma j)) volume
        (H.regularizedStageStart T 0 j.val) (H.regularizedStageEnd T v j.val))
    (hbound : ∀ᶠ a in 𝓝[>] (0 : ℝ),
      (∑ j : H.StageInterval first cut,
        ∫ r in H.regularizedStageStart T a j.val..H.regularizedStageEnd T v j.val,
          (1 - a ^ 2 / r ^2) * H.stageRegularizedLagrangian j.val T
            (gamma ⟨j.val, j.property.1, j.property.2.trans hcut⟩) r) +
        2 * v * R * (v - a) ^ 2 ≤ 2 * n * (v - a)) :
    (∑ j : H.StageInterval first last,
      H.stageRegularizedAction j.val T (gamma j)
        (H.regularizedStageStart T 0 j.val) (H.regularizedStageEnd T v j.val)) +
        2 * v ^ 3 * R ≤ 2 * n * v := by
  rw [H.sum_stage_action_eq_of_collapsed_suffix first last cut hcut T 0 v gamma hcollapsed]
  exact H.sum_action_scalar_bound_of_weighted_stage_bounds first cut T v R n
    (fun j => gamma ⟨j.val, j.property.1, j.property.2.trans hcut⟩) hpos
    (fun j => hInt ⟨j.val, j.property.1, j.property.2.trans hcut⟩) hbound

private theorem exists_reverse_stage_event_equivs
    (H : ObservedHistory.{u}) (first last : Fin (H.eventCount + 1)) (hle : first ≤ last) :
    let N := last.val - first.val;
    let E := {i : Fin H.eventCount // first ≤ i.castSucc ∧ i.succ ≤ last};
    ∃ (j : Fin (N + 1) ≃ H.StageInterval first last) (e : Fin N ≃ E),
      (∀ k, (j k).val.val = last.val - k.val) ∧
      (∀ k, (e k).val.val = last.val - (k.val + 1)) ∧
      (j 0).val = last ∧ (j (Fin.last N)).val = first ∧
      (∀ k, (e k).val.succ = (j k.castSucc).val ∧
        (e k).val.castSucc = (j k.succ).val) ∧
      (∀ F : H.StageInterval first last → ℝ, (∑ x, F x) = ∑ k, F (j k)) ∧
      (∀ F : E → ℝ, (∑ x, F x) = ∑ k, F (e k)) := by
  intro N E
  have hfl : first.val ≤ last.val := hle
  let j : Fin (N + 1) ≃ H.StageInterval first last :=
    { toFun := fun k => ⟨⟨last.val - k.val, by omega⟩, by
        have hk := k.isLt
        change first.val ≤ last.val - k.val ∧ last.val - k.val ≤ last.val
        dsimp only [N] at hk
        omega⟩
      invFun := fun x => ⟨last.val - x.val.val, by
        have hl := x.property.1
        have hr := x.property.2
        dsimp only [N]
        omega⟩
      left_inv := fun k => by
        apply Fin.ext
        change last.val - (last.val - k.val) = k.val
        have hk := k.isLt
        dsimp only [N] at hk
        omega
      right_inv := fun x => by
        apply Subtype.ext
        apply Fin.ext
        change last.val - (last.val - x.val.val) = x.val.val
        have hx := x.property.2
        omega }
  let e : Fin N ≃ E :=
    { toFun := fun k => ⟨⟨last.val - (k.val + 1), by
        have hk := k.isLt
        have hl := last.isLt
        dsimp only [N] at hk
        omega⟩, by
        have hk := k.isLt
        change first.val ≤ last.val - (k.val + 1) ∧ last.val - (k.val + 1) + 1 ≤ last.val
        dsimp only [N] at hk
        omega⟩
      invFun := fun i => ⟨last.val - (i.val.val + 1), by
        have hf := i.property.1
        have hl := i.property.2
        change first.val ≤ i.val.val at hf
        change i.val.val + 1 ≤ last.val at hl
        dsimp only [N]
        omega⟩
      left_inv := fun k => by
        apply Fin.ext
        change last.val - (last.val - (k.val + 1) + 1) = k.val
        have hk := k.isLt
        dsimp only [N] at hk
        omega
      right_inv := fun i => by
        apply Subtype.ext
        apply Fin.ext
        change last.val - (last.val - (i.val.val + 1) + 1) = i.val.val
        have hl := i.property.2
        change i.val.val + 1 ≤ last.val at hl
        omega }
  refine ⟨j, e, fun _ => rfl, fun _ => rfl, ?_, ?_, ?_, ?_, ?_⟩
  · apply Fin.ext
    change last.val - 0 = last.val
    omega
  · apply Fin.ext
    change last.val - N = first.val
    dsimp only [N]
    omega
  · intro k
    have hk := k.isLt
    dsimp only [N] at hk
    constructor <;> apply Fin.ext
    · change last.val - (k.val + 1) + 1 = last.val - k.val
      omega
    · rfl
  · intro F
    exact (j.sum_comp F).symm
  · intro F
    exact (e.sum_comp F).symm

private theorem exists_strict_collar_endpoint_list
    {N : ℕ} (a b v : ℝ) (c d : Fin N → ℝ)
    (hab : a < b) (hbv : b < v)
    (hac : ∀ k, a < c k) (hcd : ∀ k, c k < d k)
    (hsep : ∀ k l, k < l → d k < c l) (hdb : ∀ k, d k < b) :
    ∃ s : Fin (2 * N + 3) → ℝ,
      StrictMono s ∧ s 0 = a ∧ s (Fin.last (2 * N + 2)) = v ∧
      s ⟨2 * N + 1, by omega⟩ = b ∧
      (∀ k : Fin N,
        s ⟨2 * k.val + 1, by omega⟩ = c k ∧
        s ⟨2 * k.val + 2, by omega⟩ = d k) := by
  let s (i : Fin (2 * N + 3)) : ℝ :=
    if hzero : i.val = 0 then a else
    if hmid : i.val < 2 * N + 1 then
      if hodd : i.val % 2 = 1 then c ⟨i.val / 2, by omega⟩
      else d ⟨i.val / 2 - 1, by omega⟩
    else if i.val = 2 * N + 1 then b else v
  have hs0 : s 0 = a := by simp [s]
  have hsv : s (Fin.last (2 * N + 2)) = v := by
    simp only [s, Fin.val_last, dite_eq_right (by omega : 2 * N + 2 ≠ 0),
      dite_eq_right (by omega : ¬2 * N + 2 < 2 * N + 1),
      ite_eq_right (by omega : 2 * N + 2 ≠ 2 * N + 1)]
  have hsb : s ⟨2 * N + 1, by omega⟩ = b := by
    simp [s]
  have hsc (k : Fin N) : s ⟨2 * k.val + 1, by omega⟩ = c k := by
    have hk := k.isLt
    simp only [s, dite_eq_right (by omega : 2 * k.val + 1 ≠ 0),
      dite_eq_left (by omega : 2 * k.val + 1 < 2 * N + 1),
      dite_eq_left (by omega : (2 * k.val + 1) % 2 = 1)]
    congr 1
    apply Fin.ext
    dsimp only
    omega
  have hsd (k : Fin N) : s ⟨2 * k.val + 2, by omega⟩ = d k := by
    have hk := k.isLt
    simp only [s, dite_eq_right (by omega : 2 * k.val + 2 ≠ 0),
      dite_eq_left (by omega : 2 * k.val + 2 < 2 * N + 1),
      dite_eq_right (by omega : ¬(2 * k.val + 2) % 2 = 1)]
    congr 1
    apply Fin.ext
    dsimp only
    omega
  refine ⟨s, ?_, hs0, hsv, hsb, fun k => ⟨hsc k, hsd k⟩⟩
  apply Fin.strictMono_iff_lt_succ.mpr
  intro i
  have hi := i.isLt
  by_cases hi0 : i.val = 0
  · have hzero : i.castSucc = 0 := Fin.ext hi0
    rw [hzero, hs0]
    by_cases hN : N = 0
    · have his : i.succ = ⟨2 * N + 1, by omega⟩ := Fin.ext (by simp only [Fin.val_succ]; omega)
      rw [his, hsb]
      exact hab
    · let k : Fin N := ⟨0, by omega⟩
      have his : i.succ = ⟨2 * k.val + 1, by omega⟩ := Fin.ext (by simp only [Fin.val_succ]; dsimp only [k]; omega)
      rw [his, hsc]
      exact hac k
  · by_cases hilast : i.val = 2 * N + 1
    · have hic : i.castSucc = ⟨2 * N + 1, by omega⟩ := Fin.ext hilast
      have his : i.succ = Fin.last (2 * N + 2) := Fin.ext (by simpa only [Fin.val_succ, Fin.val_last] using congrArg (fun n => n + 1) hilast)
      rw [hic, his, hsb, hsv]
      exact hbv
    · have himid : i.val < 2 * N + 1 := by omega
      by_cases hodd : i.val % 2 = 1
      · let k : Fin N := ⟨i.val / 2, by omega⟩
        have hic : i.castSucc = ⟨2 * k.val + 1, by omega⟩ := Fin.ext (by simp only [Fin.val_castSucc]; dsimp only [k]; omega)
        have his : i.succ = ⟨2 * k.val + 2, by omega⟩ := Fin.ext (by simp only [Fin.val_succ]; dsimp only [k]; omega)
        rw [hic, his, hsc, hsd]
        exact hcd k
      · let k : Fin N := ⟨i.val / 2 - 1, by omega⟩
        have hic : i.castSucc = ⟨2 * k.val + 2, by omega⟩ := Fin.ext (by simp only [Fin.val_castSucc]; dsimp only [k]; omega)
        rw [hic, hsd]
        by_cases hk : k.val + 1 < N
        · let l : Fin N := ⟨k.val + 1, hk⟩
          have his : i.succ = ⟨2 * l.val + 1, by omega⟩ := Fin.ext (by simp only [Fin.val_succ]; dsimp only [k, l]; omega)
          rw [his, hsc]
          exact hsep k l (by change k.val < k.val + 1; omega)
        · have his : i.succ = ⟨2 * N + 1, by omega⟩ := Fin.ext (by simp only [Fin.val_succ]; dsimp only [k] at hk; omega)
          rw [his, hsb]
          exact hdb k

private theorem exists_ordered_positive_stage_pieces
    (H : ObservedHistory.{u}) (first last : Fin (H.eventCount + 1)) (hle : first ≤ last)
    {T v b : ℝ}
    (hupper : T ∈ Icc (H.time last) (H.stageEndTime last))
    (hpast : T - v ^ 2 ∈ Ioo (H.time first) (H.stageEndTime first))
    (hbv : b < v)
    (hmb : (H.regularizedStageStart T 0 first + H.regularizedStageEnd T v first) / 2 < b) :
    let E := {i : Fin H.eventCount //
      first ≤ i.castSucc ∧ i.succ ≤ last ∧ 0 < Real.sqrt (T - H.time i.succ)};
    ∀ c0 d0 : E → ℝ,
      (∀ i, H.regularizedStageStart T 0 i.val.succ < c0 i ∧
        c0 i < Real.sqrt (T - H.time i.val.succ) ∧
        Real.sqrt (T - H.time i.val.succ) < d0 i ∧
        d0 i < H.regularizedStageEnd T v i.val.castSucc) →
    ∃ lastPos : Fin (H.eventCount + 1), first ≤ lastPos ∧ lastPos ≤ last ∧
      (lastPos = last ↔ H.time last < T) ∧
      (T = H.time last → ∃ i : Fin H.eventCount, last = i.succ ∧ lastPos = i.castSucc) ∧
      H.regularizedStageStart T 0 lastPos = 0 ∧
      H.regularizedStageEnd T v first = v ∧
      (∀ j : H.StageInterval first lastPos,
        H.regularizedStageStart T 0 j.val < H.regularizedStageEnd T v j.val) ∧
      (∀ j : Fin (H.eventCount + 1), j ≤ last → lastPos < j →
        j = last ∧ H.regularizedStageStart T 0 j = 0 ∧ H.regularizedStageEnd T v j = 0) ∧
      let N := lastPos.val - first.val;
      ∃ (j : Fin (N + 1) ≃ H.StageInterval first lastPos) (e : Fin N ≃ E)
        (c d : E → ℝ) (a0 : ℝ),
        (∀ k, (j k).val.val = lastPos.val - k.val) ∧
        (∀ k, (e k).val.val = lastPos.val - (k.val + 1)) ∧
        (j 0).val = lastPos ∧ (j (Fin.last N)).val = first ∧
        (∀ k, (e k).val.succ = (j k.castSucc).val ∧
          (e k).val.castSucc = (j k.succ).val) ∧
        0 < a0 ∧ a0 < b ∧
        (∀ i, a0 < c i ∧ c i < Real.sqrt (T - H.time i.val.succ) ∧
          Real.sqrt (T - H.time i.val.succ) < d i ∧
          Icc (c i) (d i) ⊆ Ioo (c0 i) (d0 i) ∧
          (H.regularizedStageStart T 0 i.val.succ +
            H.regularizedStageEnd T v i.val.succ) / 2 < c i ∧
          d i < (H.regularizedStageStart T 0 i.val.castSucc +
            H.regularizedStageEnd T v i.val.castSucc) / 2 ∧ d i < b) ∧
        (∀ F : H.StageInterval first lastPos → ℝ, (∑ x, F x) = ∑ k, F (j k)) ∧
        (∀ F : E → ℝ, (∑ x, F x) = ∑ k, F (e k)) ∧
        ∀ a ∈ Ioo 0 a0, ∃ s : Fin (2 * N + 3) → ℝ,
          StrictMono s ∧ s 0 = a ∧ s (Fin.last (2 * N + 2)) = v ∧
          s ⟨2 * N + 1, by omega⟩ = b ∧
          (∀ k : Fin N,
            s ⟨2 * k.val + 1, by omega⟩ = c (e k) ∧
            s ⟨2 * k.val + 2, by omega⟩ = d (e k)) ∧
          (∀ k : Fin (N + 1),
            H.regularizedStageStart T 0 (j k).val < s ⟨2 * k.val, by omega⟩ ∧
            s ⟨2 * k.val + 1, by omega⟩ < H.regularizedStageEnd T v (j k).val) := by
  intro E c0 d0 hcollar
  have hb0 : 0 < b := by
    have hs := Real.sqrt_nonneg (T - min (T - (0 : ℝ) ^ 2) (H.stageEndTime first))
    have he := Real.sqrt_nonneg (T - max (T - v ^ 2) (H.time first))
    change 0 ≤ H.regularizedStageStart T 0 first at hs
    change 0 ≤ H.regularizedStageEnd T v first at he
    linarith
  obtain ⟨lastPos, hfp, hpl, hchar, hpole, hpos0, hfirstV, hpositive, hzero, hclockPos⟩ :=
    H.exists_positive_regularized_stage_interval first last hle (hb0.trans hbv) hupper hpast
  let N := lastPos.val - first.val
  let E0 := {i : Fin H.eventCount // first ≤ i.castSucc ∧ i.succ ≤ lastPos}
  obtain ⟨j, e0, hjVal, he0Val, hj0, hjLast, hjEvent, hsumJ, _⟩ :=
    H.exists_reverse_stage_event_equivs first lastPos hfp
  let ep : E0 ≃ E :=
    { toFun := fun i => ⟨i.val, i.property.1, i.property.2.trans hpl,
        (hclockPos i.val (i.property.2.trans hpl)).mpr i.property.2⟩
      invFun := fun i => ⟨i.val, i.property.1,
        (hclockPos i.val i.property.2.1).mp i.property.2.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  let e : Fin N ≃ E := e0.trans ep
  have heVal (k : Fin N) : (e k).val.val = lastPos.val - (k.val + 1) := he0Val k
  have hEvent (k : Fin N) : (e k).val.succ = (j k.castSucc).val ∧
      (e k).val.castSucc = (j k.succ).val := hjEvent k
  obtain ⟨c, d, a0, ha0, ha0b, hc, hsep, _, _⟩ :=
    H.exists_separated_positive_event_collars first last ⟨hb0, hbv⟩ hupper
      (H.mem_stageDomain_of_mem_Ioo hpast) c0 d0 hcollar
  have hdb (i : E) : d i < b := by
    have hs : H.regularizedStageStart T 0 i.val.castSucc ≤
        H.regularizedStageStart T 0 first := by
      apply Real.sqrt_le_sqrt
      exact sub_le_sub_left (min_le_min_left _ (H.stageEndTime_mono i.property.1)) T
    have he : H.regularizedStageEnd T v i.val.castSucc ≤
        H.regularizedStageEnd T v first := by
      apply Real.sqrt_le_sqrt
      exact sub_le_sub_left (max_le_max_left _ (H.time_strictMono.monotone i.property.1)) T
    have hd := (hc i).2.2.2.2.2.1
    linarith
  have hreverseSep (k l : Fin N) (hkl : k < l) : d (e k) < c (e l) := by
    apply hsep (e l) (e k)
    change (e l).val.val < (e k).val.val
    rw [heVal, heVal]
    have hk := k.isLt
    have hl := l.isLt
    have hfpVal : first.val ≤ lastPos.val := hfp
    change k.val < l.val at hkl
    dsimp only [N] at hk hl
    omega
  refine ⟨lastPos, hfp, hpl, hchar, hpole, hpos0, hfirstV,
    fun k => hpositive k.val k.property.1 k.property.2, hzero,
    j, e, c, d, a0, hjVal, heVal, hj0, hjLast, hEvent, ha0, ha0b,
    (fun i => ⟨(hc i).1, (hc i).2.1, (hc i).2.2.1, (hc i).2.2.2.1,
      (hc i).2.2.2.2.1, (hc i).2.2.2.2.2.1, hdb i⟩),
    hsumJ, (fun F => (e.sum_comp F).symm), ?_⟩
  intro a ha
  obtain ⟨s, hs, hs0, hsv, hsb, hscd⟩ := exists_strict_collar_endpoint_list a b v
    (fun k => c (e k)) (fun k => d (e k)) (ha.2.trans ha0b) hbv
    (fun k => ha.2.trans (hc (e k)).1)
    (fun k => (hc (e k)).2.1.trans (hc (e k)).2.2.1) hreverseSep
    (fun k => hdb (e k))
  refine ⟨s, hs, hs0, hsv, hsb, hscd, ?_⟩
  intro k
  have hk := k.isLt
  have hupper0 : T - (0 : ℝ) ^ 2 ∈ Icc (H.time last) (H.stageEndTime last) := by
    simpa only [zero_pow two_ne_zero, sub_zero] using hupper
  constructor
  · by_cases hk0 : k.val = 0
    · have hkeq : k = 0 := Fin.ext hk0
      have hsidx : (⟨2 * k.val, by omega⟩ : Fin (2 * N + 3)) = 0 := Fin.ext (by simp only [Fin.val_zero]; omega)
      rw [hsidx, hs0, hkeq, hj0, hpos0]
      exact ha.1
    · let l : Fin N := ⟨k.val - 1, by omega⟩
      have hks : l.succ = k := Fin.ext (by change k.val - 1 + 1 = k.val; omega)
      have hsidx : (⟨2 * k.val, by omega⟩ : Fin (2 * N + 3)) =
          ⟨2 * l.val + 2, by omega⟩ := Fin.ext (by change 2 * k.val = 2 * (k.val - 1) + 2; omega)
      rw [hsidx, (hscd l).2, ← hks, ← (hEvent l).2,
        H.regularizedStageStart_castSucc_eq_event_clock hupper0 (e l).val (e l).property.2.1]
      exact (hc (e l)).2.2.1
  · by_cases hkl : k.val = N
    · have hkeq : k = Fin.last N := Fin.ext hkl
      have hsidx : (⟨2 * k.val + 1, by omega⟩ : Fin (2 * N + 3)) =
          ⟨2 * N + 1, by omega⟩ := Fin.ext (by change 2 * k.val + 1 = 2 * N + 1; omega)
      rw [hsidx, hsb, hkeq, hjLast, hfirstV]
      exact hbv
    · let l : Fin N := ⟨k.val, by omega⟩
      have hkc : l.castSucc = k := Fin.ext rfl
      have hsidx : (⟨2 * k.val + 1, by omega⟩ : Fin (2 * N + 3)) =
          ⟨2 * l.val + 1, by omega⟩ := rfl
      rw [hsidx, (hscd l).1, ← hkc, ← (hEvent l).1,
        H.regularizedStageEnd_succ_eq_event_clock (H.mem_stageDomain_of_mem_Ioo hpast)
          (e l).val (e l).property.1]
      exact (hc (e l)).2.1

private theorem exists_ordered_prefix_piece_intervals
    (H : ObservedHistory.{u}) (first cut : Fin (H.eventCount + 1)) (hfc : first ≤ cut)
    {T v b : ℝ} (hcut : T ∈ Ioc (H.time cut) (H.stageEndTime cut))
    (hpast : T - v ^ 2 ∈ Ioo (H.time first) (H.stageEndTime first))
    (hbv : b < v)
    (hmb : (H.regularizedStageStart T 0 first + H.regularizedStageEnd T v first) / 2 < b) :
    let J := H.StageInterval first cut;
    let E := {i : Fin H.eventCount // first ≤ i.castSucc ∧ i.succ ≤ cut};
    let jo (i : E) : J := ⟨i.val.castSucc, i.property.1, i.val.castSucc_le_succ.trans i.property.2⟩;
    let jn (i : E) : J := ⟨i.val.succ, i.property.1.trans i.val.castSucc_le_succ, i.property.2⟩;
    let jf : J := ⟨first, le_rfl, hfc⟩;
    let jl : J := ⟨cut, hfc, le_rfl⟩;
    let N := cut.val - first.val;
    ∀ c0 d0 : E → ℝ,
      (∀ i, H.regularizedStageStart T 0 i.val.succ < c0 i ∧
        c0 i < Real.sqrt (T - H.time i.val.succ) ∧
        Real.sqrt (T - H.time i.val.succ) < d0 i ∧
        d0 i < H.regularizedStageEnd T v i.val.castSucc) →
    ∃ (j : Fin (N + 1) ≃ J) (e : Fin N ≃ E) (c d : E → ℝ) (a0 : ℝ),
      j 0 = jl ∧ j (Fin.last N) = jf ∧
      (∀ k, j k.castSucc = jn (e k) ∧ j k.succ = jo (e k)) ∧
      0 < a0 ∧ a0 < b ∧
      (∀ i, a0 < c i ∧ c i < Real.sqrt (T - H.time i.val.succ) ∧
        Real.sqrt (T - H.time i.val.succ) < d i ∧ d i < b ∧
        Icc (c i) (d i) ⊆ Ioo (c0 i) (d0 i)) ∧
      H.regularizedStageStart T 0 cut = 0 ∧ H.regularizedStageEnd T v first = v ∧
      ∀ a ∈ Ioo 0 a0,
        ∃ (lo hi : J → ℝ) (s : Fin (2 * N + 3) → ℝ),
          StrictMono s ∧ s 0 = a ∧ s (Fin.last (2 * N + 2)) = v ∧
          s ⟨2 * N + 1, by omega⟩ = b ∧
          (∀ k, s ⟨2 * k.val, by omega⟩ = lo (j k) ∧
            s ⟨2 * k.val + 1, by omega⟩ = hi (j k)) ∧
          (∀ k, s ⟨2 * k.val + 1, by omega⟩ = c (e k) ∧
            s ⟨2 * k.val + 2, by omega⟩ = d (e k)) ∧
          lo jl = a ∧ hi jf = b ∧
          (∀ i, hi (jn i) = c i ∧ lo (jo i) = d i) ∧
          (∀ x : J, H.regularizedStageStart T 0 x.val < lo x ∧ lo x < hi x ∧
            hi x < H.regularizedStageEnd T v x.val) := by
  classical
  intro J E jo jn jf jl N c0 d0 hcollar
  let EP := {i : Fin H.eventCount //
    first ≤ i.castSucc ∧ i.succ ≤ cut ∧ 0 < Real.sqrt (T - H.time i.succ)}
  have hw (i : E) : 0 < Real.sqrt (T - H.time i.val.succ) :=
    Real.sqrt_pos.mpr (sub_pos.mpr ((H.time_strictMono.monotone i.property.2).trans_lt hcut.1))
  let ep : E ≃ EP :=
    { toFun := fun i => ⟨i.val, i.property.1, i.property.2, hw i⟩
      invFun := fun i => ⟨i.val, i.property.1, i.property.2.1⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  obtain ⟨pos, hfp, hpc, hchar, _, hstart, hend, _, _, j, eP, cP, dP, a0,
      _, _, hj0, hjLast, hjEvent, ha0, ha0b, hcP, _, _, hpieces⟩ :=
    H.exists_ordered_positive_stage_pieces first cut hfc ⟨hcut.1.le, hcut.2⟩ hpast hbv hmb
      (fun i => c0 (ep.symm i)) (fun i => d0 (ep.symm i))
      (fun i => hcollar (ep.symm i))
  have hpos : pos = cut := hchar.mpr hcut.1
  subst pos
  let e : Fin N ≃ E := eP.trans ep.symm
  let c : E → ℝ := fun i => cP (ep i)
  let d : E → ℝ := fun i => dP (ep i)
  have hce (k : Fin N) : c (e k) = cP (eP k) := ep.apply_symm_apply (eP k) ▸ rfl
  have hde (k : Fin N) : d (e k) = dP (eP k) := ep.apply_symm_apply (eP k) ▸ rfl
  have hj0' : j 0 = jl := Subtype.ext hj0
  have hjLast' : j (Fin.last N) = jf := Subtype.ext hjLast
  have hjEvent' (k : Fin N) : j k.castSucc = jn (e k) ∧ j k.succ = jo (e k) :=
    ⟨Subtype.ext (hjEvent k).1.symm, Subtype.ext (hjEvent k).2.symm⟩
  refine ⟨j, e, c, d, a0, hj0', hjLast', hjEvent', ha0, ha0b, ?_, hstart, hend, ?_⟩
  · intro i
    have hi := hcP (ep i)
    simp only [ep.symm_apply_apply] at hi
    exact ⟨hi.1, hi.2.1, hi.2.2.1, hi.2.2.2.2.2.2, hi.2.2.2.1⟩
  · intro a ha
    obtain ⟨s, hs, hs0, hsv, hsb, hscd, hgap⟩ := hpieces a ha
    let lo : J → ℝ := fun x => s ⟨2 * (j.symm x).val, by have hh := (j.symm x).isLt; omega⟩
    let hi : J → ℝ := fun x => s ⟨2 * (j.symm x).val + 1, by have hh := (j.symm x).isLt; omega⟩
    have hleft (k : Fin (N + 1)) : s ⟨2 * k.val, by omega⟩ = lo (j k) := by
      simp only [lo, j.symm_apply_apply]
    have hright (k : Fin (N + 1)) : s ⟨2 * k.val + 1, by omega⟩ = hi (j k) := by
      simp only [hi, j.symm_apply_apply]
    have hcd (k : Fin N) : s ⟨2 * k.val + 1, by omega⟩ = c (e k) ∧
        s ⟨2 * k.val + 2, by omega⟩ = d (e k) :=
      ⟨(hscd k).1.trans (hce k).symm, (hscd k).2.trans (hde k).symm⟩
    refine ⟨lo, hi, s, hs, hs0, hsv, hsb, fun k => ⟨hleft k, hright k⟩,
      hcd, ?_, ?_, ?_, ?_⟩
    · rw [← hj0', ← hleft]
      exact hs0
    · rw [← hjLast', ← hright]
      exact hsb
    · intro i
      obtain ⟨k, rfl⟩ := e.surjective i
      constructor
      · rw [← (hjEvent' k).1, ← hright]
        exact (hcd k).1
      · rw [← (hjEvent' k).2, ← hleft]
        have hidx : (⟨2 * k.succ.val, by omega⟩ : Fin (2 * N + 3)) =
            ⟨2 * k.val + 2, by omega⟩ := Fin.ext (by simp only [Fin.val_succ]; omega)
        rw [hidx]
        exact (hcd k).2
    · intro x
      obtain ⟨k, rfl⟩ := j.surjective x
      rw [← hleft, ← hright]
      exact ⟨(hgap k).1, hs (by change 2 * k.val < 2 * k.val + 1; omega), (hgap k).2⟩

private theorem exists_global_smooth_stage_representative_of_regularizedExtendedAction_eq_regularizedCost
    (H : ObservedHistory.{uStageSmooth})
    (first last : Fin (H.eventCount + 1)) (hle : first ≤ last)
    {T B u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v)
    (hupper : T - u ^ 2 ∈ Icc (H.time last) (H.stageEndTime last))
    (hpast : T - v ^ 2 ∈ H.stageDomain first)
    (hscalar : ∀ j : H.StageInterval first last,
      ∀ t ∈ Ioo (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val),
      ∀ x : (H.stage j.val).Carrier, -B ≤ metricScalarAt (H.stageMetric j.val (T - t ^ 2)) x)
    (gamma : (j : H.StageInterval first last) → ℝ → (H.stage j.val).Carrier)
    (hgammaAC : ∀ j, Manifold.absolutelyContinuousOnInterval ThreeModel (gamma j)
      (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val))
    (hgammaInt : ∀ j, IntervalIntegrable (H.stageRegularizedLagrangian j.val T (gamma j)) volume
      (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val))
    (hgammaNodes : ∀ (i : Fin H.eventCount) (hf : first ≤ i.castSucc) (hl : i.succ ≤ last),
      ∃ z : (H.event i).old,
        z.val.val = gamma ⟨i.castSucc, hf, i.castSucc_lt_succ.le.trans hl⟩
          (Real.sqrt (T - H.time i.succ)) ∧
        (H.event i).oldOutput z = gamma ⟨i.succ, hf.trans i.castSucc_lt_succ.le, hl⟩
          (Real.sqrt (T - H.time i.succ)))
    (hmin : H.regularizedExtendedAction first last T B u v gamma =
      H.regularizedCost first last hle T B u v
        (gamma ⟨last, hle, le_rfl⟩ u) (gamma ⟨first, le_rfl, hle⟩ v))
    (j : H.StageInterval first last) {a b : ℝ} (hab : a ≤ b)
    (hleft : H.regularizedStageStart T u j.val < a)
    (hright : b < H.regularizedStageEnd T v j.val) :
    ∃ (D : RealTimeInterval)
      (S : SolutionOn (I := ThreeModel) (M := (H.stage j.val).Carrier) D),
      IsSolutionOn S ∧
      (∀ t, S.base.metric t = H.stageMetric j.val t) ∧
      (∀ (eta : ℝ → (H.stage j.val).Carrier) (r : ℝ),
        H.stageRegularizedLagrangian j.val T eta r = lRegularizedLagrangian S T eta r) ∧
      (∀ (eta : ℝ → (H.stage j.val).Carrier) (c d : ℝ),
        H.stageRegularizedAction j.val T eta c d = lRegularizedAction S T eta c d) ∧
      (∀ r ∈ Ioo (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val),
        T - r ^ 2 ∈ D.regular) ∧
      ∃ beta : ℝ → (H.stage j.val).Carrier, ContMDiff 𝓘(ℝ, ℝ) ThreeModel ∞ beta ∧
        (∀ r ∈ Icc a b, beta =ᶠ[𝓝 r] gamma j) ∧
        IsLRegularizedGeodesicOn S T beta (Icc a b) ∧
        lRegularizedAction S T beta a b = H.stageRegularizedAction j.val T (gamma j) a b := by
  have hsub : Icc a b ⊆ Ioo (H.regularizedStageStart T u j.val)
      (H.regularizedStageEnd T v j.val) :=
    fun _ hr => ⟨hleft.trans_le hr.1, hr.2.trans_lt hright⟩
  have hflow : ∃ (D : RealTimeInterval)
      (S : SolutionOn (I := ThreeModel) (M := (H.stage j.val).Carrier) D),
      IsSolutionOn S ∧
      (∀ t, S.base.metric t = H.stageMetric j.val t) ∧
      (∀ (eta : ℝ → (H.stage j.val).Carrier) (r : ℝ),
        H.stageRegularizedLagrangian j.val T eta r = lRegularizedLagrangian S T eta r) ∧
      IsLRegularizedGeodesicOn S T (gamma j)
        (Ioo (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val)) := by
    rcases j with ⟨k, hk⟩
    cases k using Fin.lastCases with
    | last =>
      have hp := H.mapsTo_regularizedStage_Ioo_Ioo T u v (Fin.last H.eventCount)
        (hsub ⟨le_rfl, hab⟩)
      have hfinal : H.time (Fin.last H.eventCount) < H.horizon := by
        simpa only [H.stageEndTime_last] using hp.1.trans hp.2
      have hlast : last = Fin.last H.eventCount :=
        le_antisymm (Fin.le_last last) hk.2
      subst last
      refine ⟨_, (H.finalSlab hfinal).flow, (H.finalSlab hfinal).equation, ?_,
        H.stageRegularizedLagrangian_last hfinal T, ?_⟩
      · intro t
        simp only [stageMetric, Fin.lastCases_last, dite_eq_left hfinal]
      · exact H.regularizedGeodesicOn_final_stage_of_regularizedExtendedAction_eq_regularizedCost
          first hfinal hu huv (by simpa only [H.stageEndTime_last] using hupper)
          hpast hscalar gamma hgammaAC hgammaInt (fun i hf => hgammaNodes i hf (Fin.le_last _)) hmin
    | cast i =>
      refine ⟨_, (H.event i).incoming.flow, (H.event i).incoming.equation, ?_,
        H.stageRegularizedLagrangian_castSucc i T, ?_⟩
      · intro t
        simp only [stageMetric, Fin.lastCases_castSucc]
      · exact H.regularizedGeodesicOn_incoming_stage_of_regularizedExtendedAction_eq_regularizedCost
          first last hle hu huv hupper hpast hscalar gamma hgammaAC hgammaInt hgammaNodes hmin
          i hk.1 hk.2
  obtain ⟨D, S, hS, hmetric, hlag, hgeo⟩ := hflow
  have haction (eta : ℝ → (H.stage j.val).Carrier) (c d : ℝ) :
      H.stageRegularizedAction j.val T eta c d = lRegularizedAction S T eta c d := by
    unfold stageRegularizedAction lRegularizedAction
    exact intervalIntegral.integral_congr (fun r _ => hlag eta r)
  have hclock (r : ℝ)
      (hr : r ∈ Ioo (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val)) :
      T - r ^ 2 ∈ D.regular := (hgeo r hr).1
  have hsmooth := hgeo.contMDiffOn hS isOpen_Ioo
  let U := (fun t : ℝ => a + t) ⁻¹'
    Ioo (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val)
  have hU : IsOpen U := isOpen_Ioo.preimage (continuous_const.add continuous_id)
  have hLU : ContMDiffOn 𝓘(ℝ, ℝ) ThreeModel ∞ (fun t => gamma j (a + t)) U :=
    hsmooth.comp (contMDiff_const.add contMDiff_id).contMDiffOn (fun _ ht => ht)
  have hseg : Icc (0 : ℝ) (b - a) ⊆ U := by
    intro t ht
    exact hsub ⟨by linarith [ht.1], by linarith [ht.2]⟩
  obtain ⟨eta, heta, hgerm⟩ :=
    DifferentialGeometry.Topology.Manifold.exists_global_smooth_curve_eq_near_interval
      (sub_nonneg.mpr hab) hU hseg hLU
  let beta : ℝ → (H.stage j.val).Carrier := fun t => eta (t - a)
  have hbeta : ContMDiff 𝓘(ℝ, ℝ) ThreeModel ∞ beta :=
    heta.comp (contMDiff_id.sub contMDiff_const)
  have hbetaEq (r : ℝ) (hr : r ∈ Icc a b) : beta =ᶠ[𝓝 r] gamma j := by
    have heq := (hgerm (r - a) ⟨by linarith [hr.1], by linarith [hr.2]⟩).comp_tendsto
      (continuous_id.sub continuous_const).continuousAt.tendsto
    filter_upwards [heq] with t ht
    have hsum : a + (t - a) = t := by ring
    simpa only [beta, Function.comp_apply, Pi.sub_apply, id_eq, hsum] using ht
  have hgeoAB : IsLRegularizedGeodesicOn S T (gamma j) (Icc a b) :=
    fun r hr => hgeo r (hsub hr)
  refine ⟨D, S, hS, hmetric, hlag, haction, hclock, beta, hbeta, hbetaEq,
    hgeoAB.congr_of_eventuallyEq hbetaEq, ?_⟩
  rw [haction]
  apply lRegularizedAction_congr
  intro r hr
  rw [uIoo_of_le hab] at hr
  exact (hbetaEq r ⟨hr.1.le, hr.2.le⟩).eq_of_nhds

private theorem survivor_lift_weighted_action_on_shrunk_collar
    (H : ObservedHistory.{u}) (first last : Fin (H.eventCount + 1))
    (gamma : (j : H.StageInterval first last) → ℝ → (H.stage j.val).Carrier)
    (i : Fin H.eventCount) (hf : first ≤ i.castSucc) (hl : i.succ ≤ last)
    {C D T c0 d0 c d : ℝ} (hCs : C < H.time i.succ) (hsD : H.time i.succ < D)
    (W : TopologicalSpace.Opens (H.event i).incoming.terminalRegularOpen)
    (F : PartialDiffeomorph ThreeModel ThreeModel
      (H.event i).incoming.terminalRegularOpen (H.stage i.succ).Carrier ∞)
    (S : SolutionOn (I := ThreeModel) (M := W) (RealTimeInterval.closed C D (hCs.trans hsD).le))
    (hlocalOld : IsLocalDiffeomorph ThreeModel ThreeModel ∞ (fun z : W => z.val.val))
    (hlocalNew : IsLocalDiffeomorph ThreeModel ThreeModel ∞ (fun z : W => F z.val))
    (hmetricOld : ∀ t ∈ Ico C (H.time i.succ), S.base.metric t =
      localPullMetric (H.stageMetric i.castSucc t) (fun z : W => z.val.val) hlocalOld)
    (hmetricNew : ∀ t ∈ Icc (H.time i.succ) D, S.base.metric t =
      localPullMetric (H.stageMetric i.succ t) (fun z : W => F z.val) hlocalNew)
    (eta : ℝ → W) (hAC : Manifold.absolutelyContinuousOnInterval ThreeModel eta c0 d0)
    (hint : IntervalIntegrable (lRegularizedLagrangian S T eta) volume c0 d0)
    (hnew : EqOn ((fun z : W => F z.val) ∘ eta)
      (gamma ⟨i.succ, hf.trans i.castSucc_lt_succ.le, hl⟩)
      (Icc c0 (Real.sqrt (T - H.time i.succ))))
    (hold : EqOn ((fun z : W => z.val.val) ∘ eta)
      (gamma ⟨i.castSucc, hf, i.castSucc_lt_succ.le.trans hl⟩)
      (Icc (Real.sqrt (T - H.time i.succ)) d0))
    (hc : 0 ≤ c) (hcw : c < Real.sqrt (T - H.time i.succ))
    (hwd : Real.sqrt (T - H.time i.succ) < d)
    (hsub : Icc c d ⊆ Ioo c0 d0)
    (hclock : ∀ r ∈ Icc c0 d0, T - r ^ 2 ∈ Ioo C D)
    (weight : ℝ → ℝ) (hweight : ContinuousOn weight (Icc c d)) :
    IntervalIntegrable (fun r => weight r * lRegularizedLagrangian S T eta r) volume c d ∧
      IntervalIntegrable (fun r => weight r * H.stageRegularizedLagrangian i.succ T
        (gamma ⟨i.succ, hf.trans i.castSucc_lt_succ.le, hl⟩) r) volume
        c (Real.sqrt (T - H.time i.succ)) ∧
      IntervalIntegrable (fun r => weight r * H.stageRegularizedLagrangian i.castSucc T
        (gamma ⟨i.castSucc, hf, i.castSucc_lt_succ.le.trans hl⟩) r) volume
        (Real.sqrt (T - H.time i.succ)) d ∧
      (∫ r in c..d, weight r * lRegularizedLagrangian S T eta r) =
        (∫ r in c..Real.sqrt (T - H.time i.succ), weight r *
          H.stageRegularizedLagrangian i.succ T
            (gamma ⟨i.succ, hf.trans i.castSucc_lt_succ.le, hl⟩) r) +
        ∫ r in Real.sqrt (T - H.time i.succ)..d, weight r *
          H.stageRegularizedLagrangian i.castSucc T
            (gamma ⟨i.castSucc, hf, i.castSucc_lt_succ.le.trans hl⟩) r := by
  let w := Real.sqrt (T - H.time i.succ)
  have hw : 0 < w := hc.trans_lt hcw
  have hwclock : T - w ^ 2 = H.time i.succ := by
    rw [Real.sq_sqrt (Real.sqrt_pos.mp hw).le]
    ring
  have hcd : c ≤ d := (hcw.trans hwd).le
  have hc0 : c0 < c := (hsub (left_mem_Icc.mpr hcd)).1
  have hd0 : d < d0 := (hsub (right_mem_Icc.mpr hcd)).2
  have h0 : c0 ≤ d0 := (hc0.trans_le (hcd.trans_lt hd0).le).le
  have hintSub {l r : ℝ} (hlr : l ≤ r) (hcl : c ≤ l) (hrd : r ≤ d) :
      IntervalIntegrable (lRegularizedLagrangian S T eta) volume l r :=
    hint.mono_set (by
      simpa only [uIcc_of_le hlr, uIcc_of_le h0] using
        Icc_subset_Icc (hc0.le.trans hcl) (hrd.trans hd0.le))
  have htransfer (j : Fin (H.eventCount + 1))
      (f : W → (H.stage j).Carrier) (hlocal : IsLocalDiffeomorph ThreeModel ThreeModel ∞ f)
      (alpha : ℝ → (H.stage j).Carrier) {l r : ℝ}
      (hlr : l ≤ r) (hcl : c ≤ l) (hrd : r ≤ d)
      (hproj : EqOn (f ∘ eta) alpha (Ioo l r))
      (hmet : ∀ q ∈ Ioo l r, S.base.metric (T - q ^ 2) =
        localPullMetric (H.stageMetric j (T - q ^ 2)) f hlocal) :
      lRegularizedLagrangian S T eta =ᵐ[volume.restrict (Ι l r)]
        H.stageRegularizedLagrangian j T alpha := by
    have hACSub := Manifold.absolutelyContinuousOnInterval_mono hAC (show uIcc l r ⊆ uIcc c0 d0 by
      simpa only [uIcc_of_le hlr, uIcc_of_le h0] using
        Icc_subset_Icc (hc0.le.trans hcl) (hrd.trans hd0.le))
    have hdiff := Manifold.absolutelyContinuousOnInterval_ae_mdifferentiableAt hACSub
    rw [uIcc_of_le hlr, ← restrict_Ioo_eq_restrict_Icc] at hdiff
    rw [uIoc_of_le hlr, ← restrict_Ioo_eq_restrict_Ioc]
    filter_upwards [hdiff, ae_restrict_mem measurableSet_Ioo] with q hqdiff hq
    have heq : f ∘ eta =ᶠ[𝓝 q] alpha := by
      filter_upwards [Ioo_mem_nhds hq.1 hq.2] with t ht
      exact hproj ht
    have hlag := H.stageRegularizedLagrangian_comp_eq_of_localPullMetric j S f hlocal T
      hqdiff (hmet q hq)
    rw [← hlag]
    have hv := heq.mfderiv_eq (I := 𝓘(ℝ, ℝ)) (I' := ThreeModel)
    unfold stageRegularizedLagrangian lVelocity
    rw [hv, heq.self_of_nhds]
    rfl
  have hleft := htransfer i.succ (fun z : W => F z.val) hlocalNew
    (gamma ⟨i.succ, hf.trans i.castSucc_lt_succ.le, hl⟩) hcw.le le_rfl hwd.le
    (fun q hq => hnew ⟨hc0.le.trans hq.1.le, hq.2.le⟩) (fun q hq => by
      apply hmetricNew
      have htime := hclock q (Ioo_subset_Icc_self (hsub
        ⟨hq.1.le, hq.2.le.trans hwd.le⟩))
      have hsq : q ^ 2 < w ^ 2 := (sq_lt_sq₀ (hc.trans hq.1.le) hw.le).mpr hq.2
      exact ⟨by linarith [hwclock], htime.2.le⟩)
  have hright := htransfer i.castSucc (fun z : W => z.val.val) hlocalOld
    (gamma ⟨i.castSucc, hf, i.castSucc_lt_succ.le.trans hl⟩) hwd.le hcw.le le_rfl
    (fun q hq => hold ⟨hq.1.le, hq.2.le.trans hd0.le⟩) (fun q hq => by
      apply hmetricOld
      have htime := hclock q (Ioo_subset_Icc_self (hsub
        ⟨hcw.le.trans hq.1.le, hq.2.le⟩))
      have hsq : w ^ 2 < q ^ 2 := (sq_lt_sq₀ hw.le (hw.le.trans hq.1.le)).mpr hq.1
      exact ⟨htime.1.le, by linarith [hwclock]⟩)
  have hintWeighted {l r : ℝ} (hlr : l ≤ r) (hcl : c ≤ l) (hrd : r ≤ d) :
      IntervalIntegrable (fun q => weight q * lRegularizedLagrangian S T eta q) volume l r :=
    (hintSub hlr hcl hrd).continuousOn_mul (by
      rw [uIcc_of_le hlr]
      exact hweight.mono (Icc_subset_Icc hcl hrd))
  have hleftWeighted := hleft.mono (fun r hr => congrArg (fun x : ℝ => weight r * x) hr)
  have hrightWeighted := hright.mono (fun r hr => congrArg (fun x : ℝ => weight r * x) hr)
  have hintLeft := hintWeighted hcw.le le_rfl hwd.le
  have hintRight := hintWeighted hwd.le hcw.le le_rfl
  refine ⟨hintWeighted hcd le_rfl le_rfl,
    (intervalIntegrable_congr_ae hleftWeighted).mp hintLeft,
    (intervalIntegrable_congr_ae hrightWeighted).mp hintRight, ?_⟩
  rw [← intervalIntegral.integral_add_adjacent_intervals hintLeft hintRight]
  exact congrArg₂ (fun x y : ℝ => x + y)
    (intervalIntegral.integral_congr_ae_restrict hleftWeighted)
    (intervalIntegral.integral_congr_ae_restrict hrightWeighted)

private theorem exists_smooth_survivor_piece
    (H : ObservedHistory.{u}) (first last : Fin (H.eventCount + 1))
    (gamma : (j : H.StageInterval first last) → ℝ → (H.stage j.val).Carrier)
    (i : Fin H.eventCount) (hf : first ≤ i.castSucc) (hl : i.succ ≤ last)
    {C D T c0 d0 c d : ℝ} (hCs : C < H.time i.succ) (hsD : H.time i.succ < D)
    (W : TopologicalSpace.Opens (H.event i).incoming.terminalRegularOpen)
    (F : PartialDiffeomorph ThreeModel ThreeModel
      (H.event i).incoming.terminalRegularOpen (H.stage i.succ).Carrier ∞)
    (S : SolutionOn (I := ThreeModel) (M := W) (RealTimeInterval.closed C D (hCs.trans hsD).le))
    (hS : IsSolutionOn S)
    (hlocalOld : IsLocalDiffeomorph ThreeModel ThreeModel ∞ (fun z : W => z.val.val))
    (hlocalNew : IsLocalDiffeomorph ThreeModel ThreeModel ∞ (fun z : W => F z.val))
    (hmetricOld : ∀ t ∈ Ico C (H.time i.succ), S.base.metric t =
      localPullMetric (H.stageMetric i.castSucc t) (fun z : W => z.val.val) hlocalOld)
    (hmetricNew : ∀ t ∈ Icc (H.time i.succ) D, S.base.metric t =
      localPullMetric (H.stageMetric i.succ t) (fun z : W => F z.val) hlocalNew)
    (eta : ℝ → W) (hAC : Manifold.absolutelyContinuousOnInterval ThreeModel eta c0 d0)
    (hint : IntervalIntegrable (lRegularizedLagrangian S T eta) volume c0 d0)
    (hgeo : IsLRegularizedGeodesicOn S T eta (Ioo c0 d0))
    (hnew : EqOn ((fun z : W => F z.val) ∘ eta)
      (gamma ⟨i.succ, hf.trans i.castSucc_lt_succ.le, hl⟩)
      (Icc c0 (Real.sqrt (T - H.time i.succ))))
    (hold : EqOn ((fun z : W => z.val.val) ∘ eta)
      (gamma ⟨i.castSucc, hf, i.castSucc_lt_succ.le.trans hl⟩)
      (Icc (Real.sqrt (T - H.time i.succ)) d0))
    (hc : 0 ≤ c) (hcw : c < Real.sqrt (T - H.time i.succ))
    (hwd : Real.sqrt (T - H.time i.succ) < d)
    (hsub : Icc c d ⊆ Ioo c0 d0)
    (hclock : ∀ r ∈ Icc c0 d0, T - r ^ 2 ∈ Ioo C D)
    : ∃ lo hi : ℝ, lo < c ∧ d < hi ∧
      (∀ r ∈ Ioo lo hi,
        T - r ^ 2 ∈ (RealTimeInterval.closed C D (hCs.trans hsD).le).regular) ∧
      ∃ beta : ℝ → W,
        ContMDiff 𝓘(ℝ, ℝ) ThreeModel ∞ beta ∧
        (∀ r ∈ Icc c d, beta =ᶠ[𝓝 r] eta) ∧
        IsLRegularizedGeodesicOn S T beta (Icc c d) ∧
        EqOn ((fun z : W => F z.val) ∘ beta)
          (gamma ⟨i.succ, hf.trans i.castSucc_lt_succ.le, hl⟩)
          (Icc c (Real.sqrt (T - H.time i.succ))) ∧
        EqOn ((fun z : W => z.val.val) ∘ beta)
          (gamma ⟨i.castSucc, hf, i.castSucc_lt_succ.le.trans hl⟩)
          (Icc (Real.sqrt (T - H.time i.succ)) d) ∧
        ((fun z : W => F z.val) ∘ beta) =ᶠ[𝓝 c]
          (gamma ⟨i.succ, hf.trans i.castSucc_lt_succ.le, hl⟩) ∧
        ((fun z : W => z.val.val) ∘ beta) =ᶠ[𝓝 d]
          (gamma ⟨i.castSucc, hf, i.castSucc_lt_succ.le.trans hl⟩) ∧
        EqOn (lRegularizedLagrangian S T beta) (lRegularizedLagrangian S T eta) (Icc c d) ∧
        IntervalIntegrable (lRegularizedLagrangian S T beta) volume c d ∧
        lRegularizedAction S T beta c d =
          H.stageRegularizedAction i.succ T
            (gamma ⟨i.succ, hf.trans i.castSucc_lt_succ.le, hl⟩)
            c (Real.sqrt (T - H.time i.succ)) +
          H.stageRegularizedAction i.castSucc T
            (gamma ⟨i.castSucc, hf, i.castSucc_lt_succ.le.trans hl⟩)
            (Real.sqrt (T - H.time i.succ)) d ∧
        ∀ (weight : ℝ → ℝ), ContinuousOn weight (Icc c d) →
          IntervalIntegrable (fun r => weight r * lRegularizedLagrangian S T beta r)
            volume c d ∧
          IntervalIntegrable (fun r => weight r * H.stageRegularizedLagrangian i.succ T
            (gamma ⟨i.succ, hf.trans i.castSucc_lt_succ.le, hl⟩) r) volume
            c (Real.sqrt (T - H.time i.succ)) ∧
          IntervalIntegrable (fun r => weight r * H.stageRegularizedLagrangian i.castSucc T
            (gamma ⟨i.castSucc, hf, i.castSucc_lt_succ.le.trans hl⟩) r) volume
            (Real.sqrt (T - H.time i.succ)) d ∧
          (∫ r in c..d, weight r * lRegularizedLagrangian S T beta r) =
            (∫ r in c..Real.sqrt (T - H.time i.succ), weight r *
              H.stageRegularizedLagrangian i.succ T
                (gamma ⟨i.succ, hf.trans i.castSucc_lt_succ.le, hl⟩) r) +
            ∫ r in Real.sqrt (T - H.time i.succ)..d, weight r *
              H.stageRegularizedLagrangian i.castSucc T
                (gamma ⟨i.castSucc, hf, i.castSucc_lt_succ.le.trans hl⟩) r := by
  have hcd : c < d := hcw.trans hwd
  have hc0 : c0 < c := (hsub (left_mem_Icc.mpr hcd.le)).1
  have hd0 : d < d0 := (hsub (right_mem_Icc.mpr hcd.le)).2
  have hsmooth := hgeo.contMDiffOn hS isOpen_Ioo
  obtain ⟨rho, lo, hi, hlo, hhi, hrho, hrhoId, _, hrange⟩ :=
    DifferentialGeometry.exists_smooth_time_clamp_range_subset isOpen_Ioo hcd hsub
  let beta : ℝ → W := eta ∘ rho
  have hbeta : ContMDiff 𝓘(ℝ, ℝ) ThreeModel ∞ beta :=
    hsmooth.comp_contMDiff hrho.contMDiff hrange
  have hgerm (r : ℝ) (hr : r ∈ Icc c d) : beta =ᶠ[𝓝 r] eta := by
    filter_upwards [Icc_mem_nhds (hlo.trans_le hr.1) (hr.2.trans_lt hhi)] with t ht
    change eta (rho t) = eta t
    rw [hrhoId ht]
    rfl
  have hclockMargin (r : ℝ) (hr : r ∈ Ioo lo hi) :
      T - r ^ 2 ∈ (RealTimeInterval.closed C D (hCs.trans hsD).le).regular := by
    have hrr := hrange r
    rw [hrhoId (Ioo_subset_Icc_self hr)] at hrr
    exact hclock r (Ioo_subset_Icc_self hrr)
  have hbetaGeo : IsLRegularizedGeodesicOn S T beta (Icc c d) :=
    (show IsLRegularizedGeodesicOn S T eta (Icc c d) from
      fun r hr => hgeo r (hsub hr)).congr_of_eventuallyEq hgerm
  have hnewBeta : EqOn ((fun z : W => F z.val) ∘ beta)
      (gamma ⟨i.succ, hf.trans i.castSucc_lt_succ.le, hl⟩)
      (Icc c (Real.sqrt (T - H.time i.succ))) := by
    intro r hr
    change F (beta r).val = _
    rw [(hgerm r ⟨hr.1, hr.2.trans hwd.le⟩).self_of_nhds]
    exact hnew ⟨hc0.le.trans hr.1, hr.2⟩
  have holdBeta : EqOn ((fun z : W => z.val.val) ∘ beta)
      (gamma ⟨i.castSucc, hf, i.castSucc_lt_succ.le.trans hl⟩)
      (Icc (Real.sqrt (T - H.time i.succ)) d) := by
    intro r hr
    change (beta r).val.val = _
    rw [(hgerm r ⟨hcw.le.trans hr.1, hr.2⟩).self_of_nhds]
    exact hold ⟨hr.1, hr.2.trans hd0.le⟩
  have hnewGerm : ((fun z : W => F z.val) ∘ beta) =ᶠ[𝓝 c]
      (gamma ⟨i.succ, hf.trans i.castSucc_lt_succ.le, hl⟩) := by
    filter_upwards [hgerm c (left_mem_Icc.mpr hcd.le), Ioo_mem_nhds hc0 hcw] with r heq hr
    change F (beta r).val = _
    rw [heq]
    exact hnew (Ioo_subset_Icc_self hr)
  have holdGerm : ((fun z : W => z.val.val) ∘ beta) =ᶠ[𝓝 d]
      (gamma ⟨i.castSucc, hf, i.castSucc_lt_succ.le.trans hl⟩) := by
    filter_upwards [hgerm d (right_mem_Icc.mpr hcd.le), Ioo_mem_nhds hwd hd0] with r heq hr
    change (beta r).val.val = _
    rw [heq]
    exact hold (Ioo_subset_Icc_self hr)
  have hdensity : EqOn (lRegularizedLagrangian S T beta)
      (lRegularizedLagrangian S T eta) (Icc c d) := by
    intro r hr
    have heq := hgerm r hr
    have hvel : lVelocity (I := ThreeModel) beta r = lVelocity (I := ThreeModel) eta r := by
      unfold lVelocity
      rw [heq.mfderiv_eq]
      rfl
    unfold lRegularizedLagrangian
    rw [hvel, heq.self_of_nhds]
  have hweighted (weight : ℝ → ℝ) (hweight : ContinuousOn weight (Icc c d)) :=
    H.survivor_lift_weighted_action_on_shrunk_collar first last gamma i hf hl hCs hsD W F S
      hlocalOld hlocalNew hmetricOld hmetricNew eta hAC hint hnew hold hc hcw hwd hsub hclock
      weight hweight
  have hweightedBeta (weight : ℝ → ℝ) (hweight : ContinuousOn weight (Icc c d)) :
      IntervalIntegrable (fun r => weight r * lRegularizedLagrangian S T beta r) volume c d ∧
      IntervalIntegrable (fun r => weight r * H.stageRegularizedLagrangian i.succ T
        (gamma ⟨i.succ, hf.trans i.castSucc_lt_succ.le, hl⟩) r) volume
        c (Real.sqrt (T - H.time i.succ)) ∧
      IntervalIntegrable (fun r => weight r * H.stageRegularizedLagrangian i.castSucc T
        (gamma ⟨i.castSucc, hf, i.castSucc_lt_succ.le.trans hl⟩) r) volume
        (Real.sqrt (T - H.time i.succ)) d ∧
      (∫ r in c..d, weight r * lRegularizedLagrangian S T beta r) =
        (∫ r in c..Real.sqrt (T - H.time i.succ), weight r *
          H.stageRegularizedLagrangian i.succ T
            (gamma ⟨i.succ, hf.trans i.castSucc_lt_succ.le, hl⟩) r) +
        ∫ r in Real.sqrt (T - H.time i.succ)..d, weight r *
          H.stageRegularizedLagrangian i.castSucc T
            (gamma ⟨i.castSucc, hf, i.castSucc_lt_succ.le.trans hl⟩) r := by
    obtain ⟨hInt, hNew, hOld, hEq⟩ := hweighted weight hweight
    have hEqWeighted : EqOn (fun r => weight r * lRegularizedLagrangian S T eta r)
        (fun r => weight r * lRegularizedLagrangian S T beta r) (Icc c d) :=
      fun r hr => congrArg (fun x : ℝ => weight r * x) (hdensity hr).symm
    refine ⟨hInt.congr (fun r hr => hEqWeighted (Ioc_subset_Icc_self
      (by simpa only [uIoc_of_le hcd.le] using hr))), hNew, hOld, ?_⟩
    rw [← hEq]
    exact intervalIntegral.integral_congr (by
      simpa only [uIcc_of_le hcd.le] using hEqWeighted.symm)
  have hunit := hweightedBeta (fun _ => 1) continuousOn_const
  have hbetaInt : IntervalIntegrable (lRegularizedLagrangian S T beta) volume c d := by
    simpa only [one_mul] using hunit.1
  have hbetaAction : lRegularizedAction S T beta c d =
      H.stageRegularizedAction i.succ T (gamma ⟨i.succ, hf.trans i.castSucc_lt_succ.le, hl⟩)
        c (Real.sqrt (T - H.time i.succ)) +
      H.stageRegularizedAction i.castSucc T (gamma ⟨i.castSucc, hf, i.castSucc_lt_succ.le.trans hl⟩)
        (Real.sqrt (T - H.time i.succ)) d := by
    simpa only [one_mul, lRegularizedAction, stageRegularizedAction] using hunit.2.2.2
  exact ⟨lo, hi, hlo, hhi, hclockMargin, beta, hbeta, hgerm, hbetaGeo,
    hnewBeta, holdBeta, hnewGerm, holdGerm, hdensity, hbetaInt, hbetaAction, hweightedBeta⟩

private theorem exists_smooth_prefix_stage_representatives
    (H : ObservedHistory.{u}) (first last : Fin (H.eventCount + 1)) (hle : first ≤ last)
    {T B v : ℝ} (hv : 0 < v)
    (hupper : T ∈ Icc (H.time last) (H.stageEndTime last))
    (hpast : T - v ^ 2 ∈ Ioo (H.time first) (H.stageEndTime first))
    (hscalar : ∀ j : H.StageInterval first last,
      ∀ r ∈ Ioo (H.regularizedStageStart T 0 j.val) (H.regularizedStageEnd T v j.val),
      ∀ x : (H.stage j.val).Carrier, -B ≤ metricScalarAt (H.stageMetric j.val (T - r ^ 2)) x)
    (gamma : (j : H.StageInterval first last) → ℝ → (H.stage j.val).Carrier)
    (hgammaAC : ∀ j, Manifold.absolutelyContinuousOnInterval ThreeModel (gamma j)
      (H.regularizedStageStart T 0 j.val) (H.regularizedStageEnd T v j.val))
    (hgammaInt : ∀ j, IntervalIntegrable (H.stageRegularizedLagrangian j.val T (gamma j)) volume
      (H.regularizedStageStart T 0 j.val) (H.regularizedStageEnd T v j.val))
    (hgammaNodes : ∀ (i : Fin H.eventCount) (hf : first ≤ i.castSucc) (hl : i.succ ≤ last),
      ∃ z : (H.event i).old,
        z.val.val = gamma ⟨i.castSucc, hf, i.castSucc_le_succ.trans hl⟩
          (Real.sqrt (T - H.time i.succ)) ∧
        (H.event i).oldOutput z = gamma ⟨i.succ, hf.trans i.castSucc_le_succ, hl⟩
          (Real.sqrt (T - H.time i.succ)))
    (hmin : H.regularizedExtendedAction first last T B 0 v gamma =
      H.regularizedCost first last hle T B 0 v
        (gamma ⟨last, hle, le_rfl⟩ 0) (gamma ⟨first, le_rfl, hle⟩ v))
    (cut : Fin (H.eventCount + 1)) (hcl : cut ≤ last) :
    let J := H.StageInterval first cut;
    let gammaCut : (x : J) → ℝ → (H.stage x.val).Carrier :=
      fun x => gamma ⟨x.val, x.property.1, x.property.2.trans hcl⟩;
    ∀ lo hi : J → ℝ,
      (∀ x, H.regularizedStageStart T 0 x.val < lo x ∧ lo x ≤ hi x ∧
        hi x < H.regularizedStageEnd T v x.val) →
    ∃ (DO : J → RealTimeInterval)
      (SO : (x : J) → SolutionOn (I := ThreeModel) (M := (H.stage x.val).Carrier) (DO x))
      (alpha : (x : J) → ℝ → (H.stage x.val).Carrier) (low high : J → ℝ),
      (∀ x, IsSolutionOn (SO x)) ∧
      (∀ x t, (SO x).base.metric t = H.stageMetric x.val t) ∧
      (∀ x, ContMDiff 𝓘(ℝ, ℝ) ThreeModel ∞ (alpha x)) ∧
      (∀ x, ∀ r ∈ Icc (lo x) (hi x), alpha x =ᶠ[𝓝 r] gammaCut x) ∧
      (∀ x, EqOn (alpha x) (gammaCut x) (Icc (lo x) (hi x))) ∧
      (∀ x, IsLRegularizedGeodesicOn (SO x) T (alpha x) (Icc (lo x) (hi x))) ∧
      (∀ x, low x < lo x ∧ hi x < high x) ∧
      (∀ x, ∀ r ∈ Ioo (low x) (high x), T - r ^ 2 ∈ (DO x).regular) ∧
      (∀ x, EqOn (lRegularizedLagrangian (SO x) T (alpha x))
        (H.stageRegularizedLagrangian x.val T (gammaCut x)) (Icc (lo x) (hi x))) ∧
      (∀ x, lRegularizedAction (SO x) T (alpha x) (lo x) (hi x) =
        H.stageRegularizedAction x.val T (gammaCut x) (lo x) (hi x)) ∧
      (∀ x (weight : ℝ → ℝ),
        (∫ r in (lo x)..(hi x), weight r * lRegularizedLagrangian (SO x) T (alpha x) r) =
          ∫ r in (lo x)..(hi x), weight r * H.stageRegularizedLagrangian x.val T (gammaCut x) r) := by
  classical
  intro J gammaCut lo hi hgap
  have hupper0 : T - (0 : ℝ) ^ 2 ∈ Icc (H.time last) (H.stageEndTime last) := by
    simpa only [zero_pow two_ne_zero, sub_zero] using hupper
  have hpastD := H.mem_stageDomain_of_mem_Ioo hpast
  have hproducer (x : J) :=
    H.exists_global_smooth_stage_representative_of_regularizedExtendedAction_eq_regularizedCost
      first last hle le_rfl hv.le hupper0 hpastD hscalar gamma hgammaAC hgammaInt hgammaNodes hmin
      ⟨x.val, x.property.1, x.property.2.trans hcl⟩ (hgap x).2.1 (hgap x).1 (hgap x).2.2
  choose DO SO hSO hmetric hlag haction hclock alpha hsmooth hgerm hgeo hact using hproducer
  let low (x : J) := (H.regularizedStageStart T 0 x.val + lo x) / 2
  let high (x : J) := (hi x + H.regularizedStageEnd T v x.val) / 2
  have hmargin (x : J) : low x < lo x ∧ hi x < high x := by
    dsimp only [low, high]
    constructor <;> linarith [(hgap x).1, (hgap x).2.2]
  have hreg (x : J) (r : ℝ) (hr : r ∈ Ioo (low x) (high x)) :
      T - r ^ 2 ∈ (DO x).regular := by
    apply hclock x r
    dsimp only [low, high] at hr
    constructor <;> linarith [(hgap x).1, (hgap x).2.2, hr.1, hr.2]
  have hdensity (x : J) : EqOn (lRegularizedLagrangian (SO x) T (alpha x))
      (H.stageRegularizedLagrangian x.val T (gammaCut x)) (Icc (lo x) (hi x)) := by
    intro r hr
    rw [hlag x]
    have heq := hgerm x r hr
    have hvel : lVelocity (I := ThreeModel) (alpha x) r = lVelocity (I := ThreeModel) (gammaCut x) r := by
      unfold lVelocity
      rw [heq.mfderiv_eq]
      rfl
    unfold lRegularizedLagrangian
    rw [hvel, heq.self_of_nhds]
  refine ⟨DO, SO, alpha, low, high, hSO, hmetric, hsmooth, hgerm,
    fun x r hr => (hgerm x r hr).self_of_nhds, hgeo, hmargin, hreg, hdensity, hact, ?_⟩
  intro x weight
  apply intervalIntegral.integral_congr
  intro r hr
  rw [uIcc_of_le (hgap x).2.1] at hr
  exact congrArg (fun z : ℝ => weight r * z) (hdensity x hr)

private theorem exists_smooth_prefix_survivor_representatives
    (H : ObservedHistory.{u}) (first last cut : Fin (H.eventCount + 1)) (hcl : cut ≤ last)
    (gamma : (x : H.StageInterval first last) → ℝ → (H.stage x.val).Carrier) (T : ℝ) :
    let E := {i : Fin H.eventCount // first ≤ i.castSucc ∧ i.succ ≤ cut};
    let jo (i : E) : H.StageInterval first last :=
      ⟨i.val.castSucc, i.property.1, i.val.castSucc_le_succ.trans (i.property.2.trans hcl)⟩;
    let jn (i : E) : H.StageInterval first last :=
      ⟨i.val.succ, i.property.1.trans i.val.castSucc_le_succ, i.property.2.trans hcl⟩;
    ∀ (C D : E → ℝ) (hCs : ∀ i, C i < H.time i.val.succ)
      (hsD : ∀ i, H.time i.val.succ < D i)
      (W : (i : E) → TopologicalSpace.Opens (H.event i.val).incoming.terminalRegularOpen)
      (F : (i : E) → PartialDiffeomorph ThreeModel ThreeModel
        (H.event i.val).incoming.terminalRegularOpen (H.stage i.val.succ).Carrier ∞)
      (S : (i : E) → SolutionOn (I := ThreeModel) (M := W i)
        (RealTimeInterval.closed (C i) (D i) ((hCs i).trans (hsD i)).le))
      (hlocalOld : ∀ i, IsLocalDiffeomorph ThreeModel ThreeModel ∞ (fun z : W i => z.val.val))
      (hlocalNew : ∀ i, IsLocalDiffeomorph ThreeModel ThreeModel ∞ (fun z : W i => F i z.val))
      (c0 d0 c d : E → ℝ) (eta : (i : E) → ℝ → W i),
      (∀ i, IsSolutionOn (S i)) →
      (∀ i, ∀ t ∈ Ico (C i) (H.time i.val.succ), (S i).base.metric t =
        localPullMetric (H.stageMetric i.val.castSucc t) (fun z : W i => z.val.val) (hlocalOld i)) →
      (∀ i, ∀ t ∈ Icc (H.time i.val.succ) (D i), (S i).base.metric t =
        localPullMetric (H.stageMetric i.val.succ t) (fun z : W i => F i z.val) (hlocalNew i)) →
      (∀ i, Manifold.absolutelyContinuousOnInterval ThreeModel (eta i) (c0 i) (d0 i)) →
      (∀ i, IntervalIntegrable (lRegularizedLagrangian (S i) T (eta i)) volume (c0 i) (d0 i)) →
      (∀ i, IsLRegularizedGeodesicOn (S i) T (eta i) (Ioo (c0 i) (d0 i))) →
      (∀ i, EqOn ((fun z : W i => F i z.val) ∘ eta i) (gamma (jn i))
        (Icc (c0 i) (Real.sqrt (T - H.time i.val.succ)))) →
      (∀ i, EqOn ((fun z : W i => z.val.val) ∘ eta i) (gamma (jo i))
        (Icc (Real.sqrt (T - H.time i.val.succ)) (d0 i))) →
      (∀ i, 0 ≤ c i ∧ c i < Real.sqrt (T - H.time i.val.succ) ∧
        Real.sqrt (T - H.time i.val.succ) < d i ∧ Icc (c i) (d i) ⊆ Ioo (c0 i) (d0 i)) →
      (∀ i, ∀ r ∈ Icc (c0 i) (d0 i), T - r ^ 2 ∈ Ioo (C i) (D i)) →
    ∃ (low high : E → ℝ) (alpha : (i : E) → ℝ → W i),
      (∀ i, low i < c i ∧ d i < high i) ∧
      (∀ i, ∀ r ∈ Ioo (low i) (high i),
        T - r ^ 2 ∈ (RealTimeInterval.closed (C i) (D i) ((hCs i).trans (hsD i)).le).regular) ∧
      (∀ i, ContMDiff 𝓘(ℝ, ℝ) ThreeModel ∞ (alpha i)) ∧
      (∀ i, ∀ r ∈ Icc (c i) (d i), alpha i =ᶠ[𝓝 r] eta i) ∧
      (∀ i, IsLRegularizedGeodesicOn (S i) T (alpha i) (Icc (c i) (d i))) ∧
      (∀ i, EqOn ((fun z : W i => F i z.val) ∘ alpha i) (gamma (jn i))
        (Icc (c i) (Real.sqrt (T - H.time i.val.succ)))) ∧
      (∀ i, EqOn ((fun z : W i => z.val.val) ∘ alpha i) (gamma (jo i))
        (Icc (Real.sqrt (T - H.time i.val.succ)) (d i))) ∧
      (∀ i, ((fun z : W i => F i z.val) ∘ alpha i) =ᶠ[𝓝 (c i)] gamma (jn i)) ∧
      (∀ i, ((fun z : W i => z.val.val) ∘ alpha i) =ᶠ[𝓝 (d i)] gamma (jo i)) ∧
      (∀ i, EqOn (lRegularizedLagrangian (S i) T (alpha i))
        (lRegularizedLagrangian (S i) T (eta i)) (Icc (c i) (d i))) ∧
      (∀ i, IntervalIntegrable (lRegularizedLagrangian (S i) T (alpha i)) volume (c i) (d i)) ∧
      (∀ i, lRegularizedAction (S i) T (alpha i) (c i) (d i) =
        H.stageRegularizedAction i.val.succ T (gamma (jn i)) (c i)
          (Real.sqrt (T - H.time i.val.succ)) +
        H.stageRegularizedAction i.val.castSucc T (gamma (jo i))
          (Real.sqrt (T - H.time i.val.succ)) (d i)) ∧
      (∀ i (weight : ℝ → ℝ), ContinuousOn weight (Icc (c i) (d i)) →
        IntervalIntegrable (fun r => weight r * lRegularizedLagrangian (S i) T (alpha i) r)
          volume (c i) (d i) ∧
        IntervalIntegrable (fun r => weight r * H.stageRegularizedLagrangian i.val.succ T
          (gamma (jn i)) r) volume (c i) (Real.sqrt (T - H.time i.val.succ)) ∧
        IntervalIntegrable (fun r => weight r * H.stageRegularizedLagrangian i.val.castSucc T
          (gamma (jo i)) r) volume (Real.sqrt (T - H.time i.val.succ)) (d i) ∧
        (∫ r in (c i)..(d i), weight r * lRegularizedLagrangian (S i) T (alpha i) r) =
          (∫ r in (c i)..Real.sqrt (T - H.time i.val.succ), weight r *
            H.stageRegularizedLagrangian i.val.succ T (gamma (jn i)) r) +
          ∫ r in Real.sqrt (T - H.time i.val.succ)..(d i), weight r *
            H.stageRegularizedLagrangian i.val.castSucc T (gamma (jo i)) r) := by
  classical
  intro E jo jn C D hCs hsD W F S hlocalOld hlocalNew c0 d0 c d eta
    hS hmetricOld hmetricNew hAC hint hgeo hnew hold hcollar hclock
  have hproducer (i : E) :=
    H.exists_smooth_survivor_piece first last gamma i.val i.property.1 (i.property.2.trans hcl)
      (hCs i) (hsD i) (W i) (F i) (S i) (hS i) (hlocalOld i) (hlocalNew i)
      (hmetricOld i) (hmetricNew i) (eta i) (hAC i) (hint i) (hgeo i) (hnew i) (hold i)
      (hcollar i).1 (hcollar i).2.1 (hcollar i).2.2.1 (hcollar i).2.2.2 (hclock i)
  choose low high hlo hhi hreg alpha hsmooth hgerm hclosed hnewBeta holdBeta hnewGerm holdGerm
    hdensity hInt haction hweighted using hproducer
  exact ⟨low, high, alpha, fun i => ⟨hlo i, hhi i⟩, hreg, hsmooth, hgerm, hclosed,
    hnewBeta, holdBeta, hnewGerm, holdGerm, hdensity, hInt, haction, hweighted⟩

private theorem sum_weighted_stage_action_eq_collar_action
    (H : ObservedHistory.{u}) (first last : Fin (H.eventCount + 1)) (hle : first ≤ last)
    {T a v : ℝ} (ha : 0 ≤ a) (hav : a ≤ v)
    (hupper : T - a ^ 2 ∈ Icc (H.time last) (H.stageEndTime last))
    (hpast : T - v ^ 2 ∈ H.stageDomain first) :
    let J := H.StageInterval first last;
    let E := {i : Fin H.eventCount // first ≤ i.castSucc ∧ i.succ ≤ last};
    let jo (i : E) : J := ⟨i.val.castSucc, i.property.1,
      i.val.castSucc_le_succ.trans i.property.2⟩;
    let jn (i : E) : J := ⟨i.val.succ,
      i.property.1.trans i.val.castSucc_le_succ, i.property.2⟩;
    ∀ (lo hi : J → ℝ) (gamma : (j : J) → ℝ → (H.stage j.val).Carrier),
      (∀ j, H.regularizedStageStart T a j.val ≤ lo j ∧ lo j ≤ hi j ∧
        hi j ≤ H.regularizedStageEnd T v j.val) →
      lo ⟨last, hle, le_rfl⟩ = a →
      (∀ j, IntervalIntegrable (H.stageRegularizedLagrangian j.val T (gamma j)) volume
        (H.regularizedStageStart T 0 j.val) (H.regularizedStageEnd T v j.val)) →
    ∀ (w : ℝ → ℝ), ContinuousOn w (Icc a v) →
    ∀ (W : (i : E) → TopologicalSpace.Opens (H.event i.val).incoming.terminalRegularOpen)
      (D : E → RealTimeInterval)
      (S : (i : E) → SolutionOn (I := ThreeModel) (M := W i) (D i))
      (eta : (i : E) → ℝ → W i),
      (∀ i,
        (∫ r in hi (jn i)..lo (jo i), w r * lRegularizedLagrangian (S i) T (eta i) r) =
          (∫ r in hi (jn i)..Real.sqrt (T - H.time i.val.succ),
            w r * H.stageRegularizedLagrangian i.val.succ T (gamma (jn i)) r) +
          (∫ r in Real.sqrt (T - H.time i.val.succ)..lo (jo i),
            w r * H.stageRegularizedLagrangian i.val.castSucc T (gamma (jo i)) r)) →
      (∑ j : J,
        ∫ r in H.regularizedStageStart T a j.val..H.regularizedStageEnd T v j.val,
          w r * H.stageRegularizedLagrangian j.val T (gamma j) r) =
        (∑ j : J, ∫ r in lo j..hi j,
          w r * H.stageRegularizedLagrangian j.val T (gamma j) r) +
        (∑ i : E, ∫ r in hi (jn i)..lo (jo i),
          w r * lRegularizedLagrangian (S i) T (eta i) r) +
        (∫ r in hi ⟨first, le_rfl, hle⟩..v,
          w r * H.stageRegularizedLagrangian first T (gamma ⟨first, le_rfl, hle⟩) r) := by
  classical
  intro J E jo jn lo hi gamma hbounds hlo hInt w hw W D S eta hseam
  have hstart : H.regularizedStageStart T a last = a :=
    H.regularizedStageStart_eq_of_mem_Icc ha hupper
  have hend : H.regularizedStageEnd T v first = v :=
    H.regularizedStageEnd_eq_of_mem_stageDomain (ha.trans hav) hpast
  have ho (i : E) : H.regularizedStageStart T a i.val.castSucc =
      Real.sqrt (T - H.time i.val.succ) :=
    H.regularizedStageStart_castSucc_eq_event_clock hupper i.val i.property.2
  have hn (i : E) : H.regularizedStageEnd T v i.val.succ =
      Real.sqrt (T - H.time i.val.succ) :=
    H.regularizedStageEnd_succ_eq_event_clock hpast i.val i.property.1
  let f (j : J) (r : ℝ) := w r * H.stageRegularizedLagrangian j.val T (gamma j) r
  have hfull (j : J) : IntervalIntegrable (f j) volume
      (H.regularizedStageStart T a j.val) (H.regularizedStageEnd T v j.val) := by
    have hj := H.regularizedStage_bounds ha hav hupper hpast j
    have hleft : H.regularizedStageStart T 0 j.val ≤ H.regularizedStageStart T a j.val := by
      rw [H.regularizedStageStart_eq_max_zero T ha]
      exact le_max_right _ _
    have hbase := (hInt j).mono_set (show
        uIcc (H.regularizedStageStart T a j.val) (H.regularizedStageEnd T v j.val) ⊆
        uIcc (H.regularizedStageStart T 0 j.val) (H.regularizedStageEnd T v j.val) by
      rw [uIcc_of_le hj.2.1, uIcc_of_le (hleft.trans hj.2.1)]
      exact Icc_subset_Icc hleft le_rfl)
    exact hbase.continuousOn_mul (by
      rw [uIcc_of_le hj.2.1]
      exact hw.mono (Icc_subset_Icc hj.1 hj.2.2))
  have hparts (j : J) :
      (∫ r in H.regularizedStageStart T a j.val..H.regularizedStageEnd T v j.val, f j r) =
        (∫ r in H.regularizedStageStart T a j.val..lo j, f j r) +
        (∫ r in lo j..hi j, f j r) +
        (∫ r in hi j..H.regularizedStageEnd T v j.val, f j r) := by
    have hs := hbounds j
    have hordered := hs.1.trans (hs.2.1.trans hs.2.2)
    have hleft := (hfull j).mono_set (show
        uIcc (H.regularizedStageStart T a j.val) (lo j) ⊆
        uIcc (H.regularizedStageStart T a j.val) (H.regularizedStageEnd T v j.val) by
      rw [uIcc_of_le hs.1, uIcc_of_le hordered]
      exact Icc_subset_Icc le_rfl (hs.2.1.trans hs.2.2))
    have hmid := (hfull j).mono_set (show uIcc (lo j) (hi j) ⊆
        uIcc (H.regularizedStageStart T a j.val) (H.regularizedStageEnd T v j.val) by
      rw [uIcc_of_le hs.2.1, uIcc_of_le hordered]
      exact Icc_subset_Icc hs.1 hs.2.2)
    have hright := (hfull j).mono_set (show
        uIcc (hi j) (H.regularizedStageEnd T v j.val) ⊆
        uIcc (H.regularizedStageStart T a j.val) (H.regularizedStageEnd T v j.val) by
      rw [uIcc_of_le hs.2.2, uIcc_of_le hordered]
      exact Icc_subset_Icc (hs.1.trans hs.2.1) le_rfl)
    rw [intervalIntegral.integral_add_adjacent_intervals hleft hmid,
      intervalIntegral.integral_add_adjacent_intervals (hleft.trans hmid) hright]
  calc
    _ = ∑ j : J,
        ((∫ r in H.regularizedStageStart T a j.val..lo j, f j r) +
          (∫ r in lo j..hi j, f j r) +
          (∫ r in hi j..H.regularizedStageEnd T v j.val, f j r)) :=
      Finset.sum_congr rfl (fun j _ => hparts j)
    _ = _ := by
      rw [H.sum_stage_parts_eq_endpoints_add_events first last hle]
      simp only [hstart, hend, hlo, intervalIntegral.integral_same, zero_add]
      congr 2
      apply Finset.sum_congr rfl
      intro i _
      change (∫ r in hi (jn i)..H.regularizedStageEnd T v i.val.succ, f (jn i) r) +
        (∫ r in H.regularizedStageStart T a i.val.castSucc..lo (jo i), f (jo i) r) = _
      rw [ho, hn]
      exact (hseam i).symm

private theorem weighted_integral_eq_stage_of_eqOn
    (H : ObservedHistory) (j : Fin (H.eventCount + 1))
    {D : RealTimeInterval}
    (S : SolutionOn (I := ThreeModel) (M := (H.stage j).Carrier) D)
    (T a b : ℝ) (beta gamma : ℝ → (H.stage j).Carrier) (w : ℝ → ℝ)
    (hmetric : ∀ r ∈ uIoo a b, S.base.metric (T - r ^ 2) = H.stageMetric j (T - r ^ 2))
    (heq : EqOn beta gamma (uIoo a b)) :
    (∫ r in a..b, w r * lRegularizedLagrangian S T beta r) =
      ∫ r in a..b, w r * H.stageRegularizedLagrangian j T gamma r := by
  apply intervalIntegral.integral_congr_uIoo
  intro r hr
  have hev : beta =ᶠ[𝓝 r] gamma := heq.eventuallyEq_of_mem (isOpen_Ioo.mem_nhds hr)
  have hvel : lVelocity (I := ThreeModel) beta r = lVelocity (I := ThreeModel) gamma r := by
    unfold lVelocity
    rw [hev.mfderiv_eq]
    rfl
  change w r * ((1 / 2 : ℝ) *
      (S.base.metric (T - r ^ 2)).inner (beta r)
        (lVelocity (I := ThreeModel) beta r) (lVelocity (I := ThreeModel) beta r) +
      2 * r ^ 2 * metricScalarAt (S.base.metric (T - r ^ 2)) (beta r)) =
    w r * ((1 / 2 : ℝ) * (H.stageMetric j (T - r ^ 2)).inner (gamma r)
        (lVelocity (I := ThreeModel) gamma r) (lVelocity (I := ThreeModel) gamma r) +
      2 * r ^ 2 * metricScalarAt (H.stageMetric j (T - r ^ 2)) (gamma r))
  rw [hmetric r hr, hvel, hev.self_of_nhds]

private theorem sum_weighted_stage_action_eq_smooth_collar_action
    (H : ObservedHistory.{u}) (first last : Fin (H.eventCount + 1)) (hle : first ≤ last)
    {T a v : ℝ} (ha : 0 ≤ a) (hav : a ≤ v)
    (hupper : T - a ^ 2 ∈ Icc (H.time last) (H.stageEndTime last))
    (hpast : T - v ^ 2 ∈ H.stageDomain first) :
    let J := H.StageInterval first last;
    let E := {i : Fin H.eventCount // first ≤ i.castSucc ∧ i.succ ≤ last};
    let jo (i : E) : J := ⟨i.val.castSucc, i.property.1,
      i.val.castSucc_le_succ.trans i.property.2⟩;
    let jn (i : E) : J := ⟨i.val.succ,
      i.property.1.trans i.val.castSucc_le_succ, i.property.2⟩;
    ∀ (lo hi : J → ℝ) (gamma : (j : J) → ℝ → (H.stage j.val).Carrier),
      (∀ j, H.regularizedStageStart T a j.val ≤ lo j ∧ lo j ≤ hi j ∧
        hi j ≤ H.regularizedStageEnd T v j.val) →
      lo ⟨last, hle, le_rfl⟩ = a →
      (∀ j, IntervalIntegrable (H.stageRegularizedLagrangian j.val T (gamma j)) volume
        (H.regularizedStageStart T 0 j.val) (H.regularizedStageEnd T v j.val)) →
    ∀ (w : ℝ → ℝ), ContinuousOn w (Icc a v) →
    ∀ (W : (i : E) → TopologicalSpace.Opens (H.event i.val).incoming.terminalRegularOpen)
      (DS : E → RealTimeInterval)
      (SS : (i : E) → SolutionOn (I := ThreeModel) (M := W i) (DS i))
      (eta : (i : E) → ℝ → W i),
      (∀ i,
        (∫ r in hi (jn i)..lo (jo i), w r * lRegularizedLagrangian (SS i) T (eta i) r) =
          (∫ r in hi (jn i)..Real.sqrt (T - H.time i.val.succ),
            w r * H.stageRegularizedLagrangian i.val.succ T (gamma (jn i)) r) +
          (∫ r in Real.sqrt (T - H.time i.val.succ)..lo (jo i),
            w r * H.stageRegularizedLagrangian i.val.castSucc T (gamma (jo i)) r)) →
    ∀ (DO : J → RealTimeInterval) (DT : RealTimeInterval)
      (SO : (j : J) → SolutionOn (I := ThreeModel) (M := (H.stage j.val).Carrier) (DO j))
      (ST : SolutionOn (I := ThreeModel) (M := (H.stage first).Carrier) DT)
      (beta : (j : J) → ℝ → (H.stage j.val).Carrier) (tail : ℝ → (H.stage first).Carrier),
      (∀ j, ∀ r ∈ uIoo (lo j) (hi j),
        (SO j).base.metric (T - r ^ 2) = H.stageMetric j.val (T - r ^ 2)) →
      (∀ r ∈ uIoo (hi ⟨first, le_rfl, hle⟩) v,
        ST.base.metric (T - r ^ 2) = H.stageMetric first (T - r ^ 2)) →
      (∀ j, EqOn (beta j) (gamma j) (uIoo (lo j) (hi j))) →
      EqOn tail (gamma ⟨first, le_rfl, hle⟩) (uIoo (hi ⟨first, le_rfl, hle⟩) v) →
      (∑ j : J,
        ∫ r in H.regularizedStageStart T a j.val..H.regularizedStageEnd T v j.val,
          w r * H.stageRegularizedLagrangian j.val T (gamma j) r) =
        (∑ j : J, ∫ r in lo j..hi j, w r * lRegularizedLagrangian (SO j) T (beta j) r) +
        (∑ i : E, ∫ r in hi (jn i)..lo (jo i), w r * lRegularizedLagrangian (SS i) T (eta i) r) +
        (∫ r in hi ⟨first, le_rfl, hle⟩..v, w r * lRegularizedLagrangian ST T tail r) := by
  intro J E jo jn lo hi gamma hbounds hlo hInt w hw W DS SS eta hseam
    DO DT SO ST beta tail hmetricO hmetricT hbeta htail
  rw [H.sum_weighted_stage_action_eq_collar_action first last hle ha hav hupper hpast
    lo hi gamma hbounds hlo hInt w hw W DS SS eta hseam]
  have hO : (∑ j : J, ∫ r in lo j..hi j,
      w r * H.stageRegularizedLagrangian j.val T (gamma j) r) =
      ∑ j : J, ∫ r in lo j..hi j, w r * lRegularizedLagrangian (SO j) T (beta j) r := by
    apply Finset.sum_congr rfl
    intro j _
    exact (H.weighted_integral_eq_stage_of_eqOn j.val (SO j) T (lo j) (hi j)
      (beta j) (gamma j) w (hmetricO j) (hbeta j)).symm
  rw [hO, H.weighted_integral_eq_stage_of_eqOn first ST T _ v tail _ w hmetricT htail]

theorem sum_action_scalar_bound_of_spatial_minimum
    (H : ObservedHistory.{u}) (first last : Fin (H.eventCount + 1)) (hle : first ≤ last)
    {T B v : ℝ} (hv : 0 < v)
    (hupper : T ∈ Icc (H.time last) (H.stageEndTime last))
    (hpast : T - v ^ 2 ∈ Ioo (H.time first) (H.stageEndTime first))
    (gamma : (j : H.StageInterval first last) → ℝ → (H.stage j.val).Carrier)
    (hAC : ∀ j, Manifold.absolutelyContinuousOnInterval ThreeModel (gamma j)
      (H.regularizedStageStart T 0 j.val) (H.regularizedStageEnd T v j.val))
    (hFirst : ContMDiff 𝓘(ℝ, ℝ) ThreeModel 1 (gamma ⟨first, le_rfl, hle⟩))
    (hInt : ∀ j, IntervalIntegrable (H.stageRegularizedLagrangian j.val T (gamma j)) volume
      (H.regularizedStageStart T 0 j.val) (H.regularizedStageEnd T v j.val))
    (hNodes : ∀ (i : Fin H.eventCount) (hf : first ≤ i.castSucc) (hl : i.succ ≤ last),
      ∃ z : (H.event i).old,
        z.val.val = gamma ⟨i.castSucc, hf, i.castSucc_le_succ.trans hl⟩
          (Real.sqrt (T - H.time i.succ)) ∧
        (H.event i).oldOutput z = gamma ⟨i.succ, hf.trans i.castSucc_le_succ, hl⟩
          (Real.sqrt (T - H.time i.succ)))
    (hscalar : ∀ j : H.StageInterval first last,
      ∀ r ∈ Ioo (H.regularizedStageStart T 0 j.val) (H.regularizedStageEnd T v j.val),
      ∀ x : (H.stage j.val).Carrier, -B ≤ metricScalarAt (H.stageMetric j.val (T - r ^ 2)) x)
    (hminimum : ∀ q : (H.stage first).Carrier,
      (((∑ j : H.StageInterval first last, H.stageRegularizedAction j.val T (gamma j)
        (H.regularizedStageStart T 0 j.val) (H.regularizedStageEnd T v j.val)) : ℝ) : WithTop ℝ) ≤
      H.regularizedCost first last hle T B 0 v (gamma ⟨last, hle, le_rfl⟩ 0) q)
    (hcross : ∀ (i : Fin H.eventCount) (hf : first ≤ i.castSucc) (hl : i.succ ≤ last),
      0 < Real.sqrt (T - H.time i.succ) →
      (H.event i).RegularCrossing
        (gamma ⟨i.castSucc, hf, i.castSucc_le_succ.trans hl⟩ (Real.sqrt (T - H.time i.succ)))
        (gamma ⟨i.succ, hf.trans i.castSucc_le_succ, hl⟩ (Real.sqrt (T - H.time i.succ)))) :
    (∑ j : H.StageInterval first last, H.stageRegularizedAction j.val T (gamma j)
      (H.regularizedStageStart T 0 j.val) (H.regularizedStageEnd T v j.val)) +
      2 * v ^ 3 * metricScalarAt (H.stageMetric first (T - v ^ 2))
        (gamma ⟨first, le_rfl, hle⟩ v) ≤ 6 * v := by
  classical
  have hupper0 : T - (0 : ℝ) ^ 2 ∈ Icc (H.time last) (H.stageEndTime last) := by
    simpa only [zero_pow two_ne_zero, sub_zero] using hupper
  have hpastD := H.mem_stageDomain_of_mem_Ioo hpast
  have hfull := H.regularizedExtendedAction_eq_sum_action first last le_rfl hv.le hupper0 hpastD
    gamma hInt (fun j => by
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
      exact hscalar j r hr (gamma j r))
  have hstation := H.past_velocity_eq_zero_of_spatial_minimum first last hle le_rfl hv
    hupper0 hpast hscalar gamma hAC hFirst hInt hNodes
    (fun q => hfull.trans_le (hminimum q))
  obtain ⟨hcost, cut, hfc, hcl, hstart, hend, hcut, hpos, hcollapsed, hminCut⟩ :=
    H.exists_positive_prefix_action_minimum_of_spatial_minimum first last hle hv hupper hpast
      gamma hAC hInt hNodes hscalar hminimum
  let J := H.StageInterval first cut
  let E := {i : Fin H.eventCount // first ≤ i.castSucc ∧ i.succ ≤ cut}
  let gammaCut : (j : J) → ℝ → (H.stage j.val).Carrier :=
    fun j => gamma ⟨j.val, j.property.1, j.property.2.trans hcl⟩
  obtain ⟨DT, ST, hST, hMT, hLT, hAT, hTregV, cTail, b, lowT, highT,
    hcTail, hmbTail, hbv, hb0, hlowT, hhighT, hregT, alphaT, hsmT, hgeoT,
    hcenterT, hgermT, hvalueT, hvelocityT, hactionT⟩ :=
    H.exists_smooth_terminal_stage_piece first last hle hv hupper hpast hscalar gamma
      hAC hInt hNodes hcost (hFirst v)
  have hmb : (H.regularizedStageStart T 0 first + H.regularizedStageEnd T v first) / 2 < b :=
    (le_max_right _ _).trans_lt hmbTail
  have hfinal : lVelocity (I := ThreeModel) alphaT v = 0 := hvelocityT.trans hstation
  have hcrossCut (i : Fin H.eventCount) (hf : first ≤ i.castSucc) (hl : i.succ ≤ cut) :=
    hcross i hf (hl.trans hcl) (Real.sqrt_pos.mpr (sub_pos.mpr
      ((H.time_strictMono.monotone hl).trans_lt hcut.1)))
  obtain ⟨C, D, hCs, hsD, W, FC, SS, hold, hnew, c0, d0, eta, hgeom, _⟩ :=
    H.exists_positive_prefix_survivor_collars first last hle hv hupper hpast hscalar gamma
      hAC hInt hNodes hcost cut hcl hcut b ⟨hb0, hbv⟩ hmb hcrossCut
  have hcollarInput (i : E) :
      H.regularizedStageStart T 0 i.val.succ < c0 i ∧
      c0 i < Real.sqrt (T - H.time i.val.succ) ∧
      Real.sqrt (T - H.time i.val.succ) < d0 i ∧
      d0 i < H.regularizedStageEnd T v i.val.castSucc := by
    rcases hgeom i with ⟨_, _, _, _, _, _, _, _, _, _, _, hc0w, hwd0, _, hclipN, hclipO, _⟩
    exact ⟨hclipN, hc0w, hwd0, hclipO⟩
  obtain ⟨j, e, c, d, a0, hj0, hjLast, hjEvent, ha0, ha0b, hcollars, _, _, hpieces⟩ :=
    H.exists_ordered_prefix_piece_intervals first cut hfc hcut hpast hbv hmb c0 d0 hcollarInput
  choose hwpos hwv hCold hDnew hFCsource hSS hcrossW hmetricOld hmetricNew hterminal
    hc0pos hc0w hwd0 hd0v hclipNew hclipOld hclock hEtaAC hEtaC1 hEtaGeo hEtaNew hEtaOld
    hEtaInt hEtaAction using hgeom
  obtain ⟨lowS, highS, alphaS, hmarginS, hregS, hsmS, hgermS, hgeoS, hnewS, holdS,
    hnewGermS, holdGermS, hdensityS, hIntS, hActionS, hweightedS⟩ :=
    H.exists_smooth_prefix_survivor_representatives first last cut hcl gamma T
      C D hCs hsD W FC SS hold hnew c0 d0 c d eta hSS hmetricOld hmetricNew hEtaAC
      hEtaInt hEtaGeo hEtaNew hEtaOld
      (fun i => ⟨(ha0.trans (hcollars i).1).le, (hcollars i).2.1,
        (hcollars i).2.2.1, (hcollars i).2.2.2.2⟩) hclock
  let R := metricScalarAt (H.stageMetric first (T - v ^ 2)) (gamma ⟨first, le_rfl, hle⟩ v)
  have hbound : ∀ᶠ a in 𝓝[>] (0 : ℝ),
      (∑ x : J, ∫ r in H.regularizedStageStart T a x.val..H.regularizedStageEnd T v x.val,
        (1 - a ^ 2 / r ^ 2) * H.stageRegularizedLagrangian x.val T (gammaCut x) r) +
      2 * v * R * (v - a) ^ 2 ≤ 2 * (3 : ℝ) * (v - a) := by
    filter_upwards [self_mem_nhdsWithin,
      (eventually_lt_nhds ha0).filter_mono nhdsWithin_le_nhds] with a ha haa0
    have ha0' : 0 < a := ha
    have hab : a < b := haa0.trans ha0b
    have hav : a < v := hab.trans hbv
    obtain ⟨lo, hi, s, hs, hs0, hEnd, hb, hOrd, hSeam, hlo, hhi, hJoinClocks, hGaps⟩ :=
      hpieces a ⟨ha0', haa0⟩
    have hupperA : T - a ^ 2 ∈ Icc (H.time cut) (H.stageEndTime cut) := by
      apply Ioo_subset_Icc_self
      apply H.mapsTo_regularizedStage_Ioo_Ioo T 0 v cut
      rw [← hlo]
      exact ⟨(hGaps ⟨cut, hfc, le_rfl⟩).1,
        ((hGaps ⟨cut, hfc, le_rfl⟩).2.1).trans ((hGaps ⟨cut, hfc, le_rfl⟩).2.2)⟩
    have hLo (x : J) : a ≤ lo x := by
      obtain ⟨k, rfl⟩ := j.surjective x
      rw [← (hOrd k).1, ← hs0]
      exact hs.monotone (Fin.zero_le _)
    have hBoundsA (x : J) : H.regularizedStageStart T a x.val ≤ lo x ∧
        lo x ≤ hi x ∧ hi x ≤ H.regularizedStageEnd T v x.val := by
      rw [H.regularizedStageStart_eq_max_zero T ha0'.le]
      exact ⟨max_le (hLo x) (hGaps x).1.le, (hGaps x).2.1.le, (hGaps x).2.2.le⟩
    have hheadSubset : uIcc 0 (lo ⟨cut, hfc, le_rfl⟩) ⊆
        uIcc (H.regularizedStageStart T 0 cut) (H.regularizedStageEnd T v cut) := by
      have h0end : 0 ≤ H.regularizedStageEnd T v cut := Real.sqrt_nonneg _
      rw [hstart, hlo, uIcc_of_le ha0'.le, uIcc_of_le h0end]
      exact Icc_subset_Icc le_rfl (by
        rw [← hlo]
        exact ((hGaps ⟨cut, hfc, le_rfl⟩).2.1).le.trans ((hGaps ⟨cut, hfc, le_rfl⟩).2.2).le)
    have hprefixAC : Manifold.absolutelyContinuousOnInterval ThreeModel
        (gammaCut ⟨cut, hfc, le_rfl⟩) 0 (lo ⟨cut, hfc, le_rfl⟩) :=
      Manifold.absolutelyContinuousOnInterval_mono (hAC ⟨cut, hfc, hcl⟩) hheadSubset
    have hprefixInt : IntervalIntegrable
        (H.stageRegularizedLagrangian cut T (gammaCut ⟨cut, hfc, le_rfl⟩)) volume
        0 (lo ⟨cut, hfc, le_rfl⟩) := (hInt ⟨cut, hfc, hcl⟩).mono_set hheadSubset
    obtain ⟨DO, SO, alphaO, lowO, highO, hSO, hmetricO, hsmO, hgermO, hcenterO,
      hgeoO, hmarginO, hregO, hdensityO, hActionO, hweightedO⟩ :=
      H.exists_smooth_prefix_stage_representatives first last hle hv hupper hpast hscalar
        gamma hAC hInt hNodes hcost cut hcl lo hi
        (fun x => ⟨(hGaps x).1, (hGaps x).2.1.le, (hGaps x).2.2⟩)
    let DS : E → RealTimeInterval := fun i =>
      RealTimeInterval.closed (C i) (D i) ((hCs i).trans (hsD i)).le
    let weight : ℝ → ℝ := fun r => 1 - a ^ 2 / r ^ 2
    have hw : ContinuousOn weight (Icc a v) :=
      continuousOn_const.sub (continuousOn_const.div (continuousOn_id.pow 2)
        (fun r hr => pow_ne_zero 2 (ne_of_gt (ha0'.trans_le hr.1))))
    have hweightedSeam (i : E) :
        (∫ r in hi ⟨i.val.succ, i.property.1.trans i.val.castSucc_le_succ, i.property.2⟩..
          lo ⟨i.val.castSucc, i.property.1, i.val.castSucc_le_succ.trans i.property.2⟩,
          weight r * lRegularizedLagrangian (SS i) T (alphaS i) r) =
        (∫ r in hi ⟨i.val.succ, i.property.1.trans i.val.castSucc_le_succ, i.property.2⟩..
          Real.sqrt (T - H.time i.val.succ),
          weight r * H.stageRegularizedLagrangian i.val.succ T
            (gammaCut ⟨i.val.succ, i.property.1.trans i.val.castSucc_le_succ, i.property.2⟩) r) +
        ∫ r in Real.sqrt (T - H.time i.val.succ)..
          lo ⟨i.val.castSucc, i.property.1, i.val.castSucc_le_succ.trans i.property.2⟩,
          weight r * H.stageRegularizedLagrangian i.val.castSucc T
            (gammaCut ⟨i.val.castSucc, i.property.1, i.val.castSucc_le_succ.trans i.property.2⟩) r := by
      rw [(hJoinClocks i).1, (hJoinClocks i).2]
      exact (hweightedS i weight (hw.mono (Icc_subset_Icc
        (haa0.trans (hcollars i).1).le ((hcollars i).2.2.2.1.trans hbv).le))).2.2.2
    have hpartition := H.sum_weighted_stage_action_eq_smooth_collar_action first cut hfc
      ha0'.le hav.le hupperA hpastD lo hi gammaCut hBoundsA hlo
      (fun x => hInt ⟨x.val, x.property.1, x.property.2.trans hcl⟩)
      weight hw W DS SS alphaS hweightedSeam DO DT SO ST alphaO alphaT
      (fun x r _ => hmetricO x _) (fun r _ => hMT _)
      (fun x r hr => hcenterO x (Ioo_subset_Icc_self (by
        simpa only [uIoo_of_le (hGaps x).2.1.le] using hr)))
      (by simpa only [hhi, uIoo_of_le hbv.le] using hcenterT.mono Ioo_subset_Icc_self)
    have hscalarT : ST.scalar (T - v ^ 2) (alphaT v) = R := by
      simp only [SolutionOn.scalar, SolutionFamily.scalar, hMT, hvalueT, R]
    rw [hpartition]
    have htrace := H.smooth_collar_weighted_trace_bound_of_action_minimum first cut hfc
      hv.le ⟨hcut.1.le, hcut.2⟩ hpastD gammaCut lo hi
      (fun x => ⟨(hGaps x).1.le, (hGaps x).2.1.le, (hGaps x).2.2.le⟩)
      hprefixAC hprefixInt hminCut j e hjLast hj0 (fun k => (hjEvent k).1)
      (fun k => (hjEvent k).2) W FC C D DO DS DT SO SS ST hold hnew alphaO alphaS alphaT s
      hSO hSS hST hmetricO hMT hcrossW hmetricOld hmetricNew
      (fun i => by
        rw [(hJoinClocks i).1, (hJoinClocks i).2]
        exact ⟨(hcollars i).2.1, (hcollars i).2.2.1⟩)
      (fun i r hr => by
        rw [(hJoinClocks i).1, (hJoinClocks i).2] at hr
        exact hclock i r (Ioo_subset_Icc_self ((hcollars i).2.2.2.2 hr)))
      hsmO hsmS hsmT hgeoO
      (fun i => by simpa only [(hJoinClocks i).1, (hJoinClocks i).2] using hgeoS i)
      (by simpa only [hhi] using hgeoT) hgermO
      (by simpa only [hhi] using hcenterT) (by simpa only [hhi] using hgermT)
      (fun i r hr => holdS i (by simpa only [(hJoinClocks i).2] using hr))
      (fun i r hr => hnewS i (by simpa only [(hJoinClocks i).1] using hr))
      (fun i => by simpa only [(hJoinClocks i).2] using holdGermS i)
      (fun i => by simpa only [(hJoinClocks i).1] using hnewGermS i)
      hfinal hs (by simpa only [hs0] using ha0')
      (fun k => (hOrd k).1) (fun k => (hOrd k).2)
      (fun k => (hSeam k).1.trans (hJoinClocks (e k)).1.symm)
      (fun k => (hSeam k).2.trans (hJoinClocks (e k)).2.symm)
      (hb.trans hhi.symm) hEnd lowO highO lowS highS lowT highT hmarginO
      (fun i => by simpa only [(hJoinClocks i).1, (hJoinClocks i).2] using hmarginS i)
      (by simpa only [hhi] using hlowT) hhighT hregO hregS hregT
    simpa only [weight, hs0, hscalarT, show (2 : ℝ) * 3 = 6 by norm_num] using htrace
  have hh := H.sum_action_scalar_bound_of_positive_prefix_weighted_bounds first last cut hcl
    T v R 3 gamma hpos hcollapsed hInt hbound
  simpa only [R, show (2 : ℝ) * 3 = 6 by norm_num] using hh

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory
