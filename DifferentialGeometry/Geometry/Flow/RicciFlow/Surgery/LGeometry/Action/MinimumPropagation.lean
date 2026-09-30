import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.LGeometry.Action.MinimumTime
import DifferentialGeometry.Analysis.Calculus.UpperSupport.Monotonicity
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TerminalClosedSolution
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Estimates.Constant
import DifferentialGeometry.Analysis.Calculus.UpperSupport.Propagation
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.LGeometry.Action.C1Attainment
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.LGeometry.Action.IndexEstimate
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.LGeometry.Action.SpatialMinimum
set_option autoImplicit false

noncomputable section

open Set Filter _root_.MeasureTheory
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Perelman
open scoped _root_.Manifold ContDiff _root_.Topology Interval BigOperators

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

universe u

private theorem mem_stageDomain_of_mem_Ico
    (H : ObservedHistory.{u}) {j : Fin (H.eventCount + 1)} {t : ℝ}
    (ht : t ∈ Ico (H.time j) (H.stageEndTime j)) : t ∈ H.stageDomain j := by
  cases j using Fin.lastCases with
  | last =>
    simpa only [stageDomain, Fin.lastCases_last, H.stageEndTime_last] using
      (show t ∈ Icc (H.time (Fin.last H.eventCount)) H.horizon from
        ⟨ht.1, by simpa only [H.stageEndTime_last] using ht.2.le⟩)
  | cast i =>
    simpa only [stageDomain, Fin.lastCases_castSucc, H.stageEndTime_castSucc] using ht

private theorem exists_constant_tail_extension_action_le
    (H : ObservedHistory.{u}) (first last : Fin (H.eventCount + 1)) (hle : first ≤ last)
    {T u v w : ℝ} (hu : 0 ≤ u) (huv : u ≤ v) (hvw : v ≤ w)
    (hupper : T - u ^ 2 ∈ Icc (H.time last) (H.stageEndTime last))
    (hvpast : T - v ^ 2 ∈ Ico (H.time first) (H.stageEndTime first))
    (hwpast : T - w ^ 2 ∈ Ico (H.time first) (H.stageEndTime first))
    (C : ℝ) (hceiling : ∀ r ∈ Icc v w, ∀ x : (H.stage first).Carrier,
      metricScalarAt (H.stageMetric first (T - r ^ 2)) x ≤ C)
    (gamma : (j : H.StageInterval first last) → ℝ → (H.stage j.val).Carrier)
    (hgamma : ∀ j, Manifold.absolutelyContinuousOnInterval ThreeModel (gamma j)
      (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val))
    (hint : ∀ j, IntervalIntegrable (H.stageRegularizedLagrangian j.val T (gamma j)) volume
      (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val))
    (hnodes : ∀ (i : Fin H.eventCount) (hf : first ≤ i.castSucc) (hl : i.succ ≤ last),
      ∃ z : (H.event i).old,
        z.val.val = gamma ⟨i.castSucc, hf, i.castSucc_lt_succ.le.trans hl⟩
          (Real.sqrt (T - H.time i.succ)) ∧
        (H.event i).oldOutput z = gamma ⟨i.succ, hf.trans i.castSucc_lt_succ.le, hl⟩
          (Real.sqrt (T - H.time i.succ))) :
    ∃ beta : (j : H.StageInterval first last) → ℝ → (H.stage j.val).Carrier,
      (∀ j, Manifold.absolutelyContinuousOnInterval ThreeModel (beta j)
        (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T w j.val)) ∧
      (∀ j, IntervalIntegrable (H.stageRegularizedLagrangian j.val T (beta j)) volume
        (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T w j.val)) ∧
      (∀ j r, r ≤ v → beta j r = gamma j r) ∧
      beta ⟨last, hle, le_rfl⟩ u = gamma ⟨last, hle, le_rfl⟩ u ∧
      (∀ r, v ≤ r → beta ⟨first, le_rfl, hle⟩ r = gamma ⟨first, le_rfl, hle⟩ v) ∧
      (∀ (i : Fin H.eventCount) (hf : first ≤ i.castSucc) (hl : i.succ ≤ last),
        ∃ z : (H.event i).old,
          z.val.val = beta ⟨i.castSucc, hf, i.castSucc_lt_succ.le.trans hl⟩
            (Real.sqrt (T - H.time i.succ)) ∧
          (H.event i).oldOutput z = beta ⟨i.succ, hf.trans i.castSucc_lt_succ.le, hl⟩
            (Real.sqrt (T - H.time i.succ))) ∧
      (∑ j : H.StageInterval first last, H.stageRegularizedAction j.val T (beta j)
        (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T w j.val)) ≤
      (∑ j : H.StageInterval first last, H.stageRegularizedAction j.val T (gamma j)
        (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val)) +
        (2 * C / 3) * (w ^ 3 - v ^ 3) := by
  classical
  let jf : H.StageInterval first last := ⟨first, le_rfl, hle⟩
  let a := H.regularizedStageStart T u first
  have hv : 0 ≤ v := hu.trans huv
  have hw : 0 ≤ w := hv.trans hvw
  have hvD := H.mem_stageDomain_of_mem_Ico hvpast
  have hwD := H.mem_stageDomain_of_mem_Ico hwpast
  have hendv := H.regularizedStageEnd_eq_of_mem_stageDomain hv hvD
  have hendw := H.regularizedStageEnd_eq_of_mem_stageDomain hw hwD
  have hav : a ≤ v := by
    simpa only [a, jf, hendv] using (H.regularizedStage_bounds hu huv hupper hvD jf).2.1
  have hclock (r : ℝ) (hr : r ∈ Icc v w) :
      T - r ^ 2 ∈ Ico (H.time first) (H.stageEndTime first) := by
    have hvr : v ^ 2 ≤ r ^ 2 := (sq_le_sq₀ hv (hv.trans hr.1)).mpr hr.1
    have hrw : r ^ 2 ≤ w ^ 2 := (sq_le_sq₀ (hv.trans hr.1) hw).mpr hr.2
    exact ⟨by linarith [hwpast.1], by linarith [hvpast.2]⟩
  have hendOther (j : H.StageInterval first last) (hj : j ≠ jf) :
      H.regularizedStageEnd T w j.val = H.regularizedStageEnd T v j.val := by
    have hjlt : first < j.val := lt_of_le_of_ne j.property.1 (by
      intro heq
      exact hj (Subtype.ext heq.symm))
    have htime : H.stageEndTime first ≤ H.time j.val := by
      cases first using Fin.lastCases with
      | last => exact False.elim ((not_lt_of_ge (Fin.le_last j.val)) hjlt)
      | cast i =>
        rw [H.stageEndTime_castSucc]
        apply H.time_strictMono.monotone
        exact hjlt
    simp only [regularizedStageEnd, max_eq_right (hwpast.2.le.trans htime),
      max_eq_right (hvpast.2.le.trans htime)]
  obtain ⟨D, S, hS, hlag, hcarrier⟩ :
      ∃ (D : RealTimeInterval) (S : SolutionOn (I := ThreeModel) (M := (H.stage first).Carrier) D),
        IsSolutionOn S ∧
        (∀ eta : ℝ → (H.stage first).Carrier,
          H.stageRegularizedLagrangian first T eta = lRegularizedLagrangian S T eta) ∧
        (∀ r ∈ Icc v w, T - r ^ 2 ∈ D.carrier) := by
    cases first using Fin.lastCases with
    | last =>
      have hfinal : H.time (Fin.last H.eventCount) < H.horizon := by
        simpa only [H.stageEndTime_last] using hvpast.1.trans_lt hvpast.2
      refine ⟨_, (H.finalSlab hfinal).flow, (H.finalSlab hfinal).equation,
        (fun eta => funext (H.stageRegularizedLagrangian_last hfinal T eta)), ?_⟩
      intro r hr
      simpa only [RealTimeInterval.closed, RealTimeInterval.carrier, H.stageEndTime_last]
        using Ico_subset_Icc_self (hclock r hr)
    | cast i =>
      refine ⟨_, (H.event i).incoming.flow, (H.event i).incoming.equation,
        (fun eta => funext (H.stageRegularizedLagrangian_castSucc i T eta)), ?_⟩
      intro r hr
      simpa only [RealTimeInterval.closedOpen, RealTimeInterval.carrier,
        H.stageEndTime_castSucc] using hclock r hr
  let tail : ℝ → (H.stage first).Carrier := fun _ => gamma jf v
  have htailCont : ContinuousOn (H.stageRegularizedLagrangian first T tail) (Icc v w) := by
    rw [hlag]
    exact (lRegularizedLagrangian_continuousOn_carrier S hS tail contMDiff_const).comp
      (f := fun r : ℝ => (T, r)) (continuousOn_const.prodMk continuousOn_id)
      (fun r hr => hcarrier r hr)
  have htailInt : IntervalIntegrable (H.stageRegularizedLagrangian first T tail) volume v w :=
    htailCont.intervalIntegrable_of_Icc hvw
  have htailLag (r : ℝ) : H.stageRegularizedLagrangian first T tail r =
      2 * r ^ 2 * metricScalarAt (H.stageMetric first (T - r ^ 2)) (gamma jf v) := by
    have hvel : lVelocity (I := ThreeModel) tail r = 0 := by
      simp only [tail, lVelocity, mfderiv_const]
      rfl
    simp only [stageRegularizedLagrangian, hvel, map_zero, mul_zero, zero_add, tail]
  have htailBound : H.stageRegularizedAction first T tail v w ≤
      (2 * C / 3) * (w ^ 3 - v ^ 3) := by
    have hpoly : IntervalIntegrable (fun r : ℝ => 2 * r ^ 2 * C) volume v w :=
      (by fun_prop : Continuous (fun r : ℝ => 2 * r ^ 2 * C)).intervalIntegrable _ _
    have hleInt := intervalIntegral.integral_mono_on hvw htailInt hpoly
      (fun r hr => by rw [htailLag]; exact mul_le_mul_of_nonneg_left (hceiling r hr _) (by positivity))
    have hpolyEq : (∫ r in v..w, 2 * r ^ 2 * C) = (2 * C / 3) * (w ^ 3 - v ^ 3) := by
      rw [intervalIntegral.integral_mul_const, intervalIntegral.integral_const_mul, integral_pow]
      norm_num
      ring
    exact hleInt.trans_eq hpolyEq
  let eta : ℝ → (H.stage first).Carrier := (Iic v).piecewise (gamma jf) tail
  have hetaLeft (r : ℝ) (hr : r ≤ v) : eta r = gamma jf r := ite_eq_left hr
  have hetaRight (r : ℝ) (hr : v ≤ r) : eta r = gamma jf v := by
    rcases hr.eq_or_lt with hr | hr
    · subst r
      exact hetaLeft v le_rfl
    · exact ite_eq_right (not_le.mpr hr)
  have hetaAC : Manifold.absolutelyContinuousOnInterval ThreeModel eta a w := by
    apply Manifold.absolutelyContinuousOnInterval_piecewise_Iic
      (by simpa only [jf, hendv, a] using hgamma jf)
      (Manifold.absolutelyContinuousOnInterval_of_contMDiffOn contMDiffOn_const) hav hvw
    rfl
  have hlagEq (alpha beta : ℝ → (H.stage first).Carrier) (l r : ℝ) (hlr : l ≤ r)
      (heq : EqOn alpha beta (Icc l r)) :
      EqOn (H.stageRegularizedLagrangian first T alpha)
        (H.stageRegularizedLagrangian first T beta) (uIoo l r) := by
    intro t ht
    rw [uIoo_of_le hlr] at ht
    have hev : alpha =ᶠ[𝓝 t] beta := by
      filter_upwards [Ioo_mem_nhds ht.1 ht.2] with z hz
      exact heq (Ioo_subset_Icc_self hz)
    have hval := hev.self_of_nhds
    have hder := hev.mfderiv_eq (I := 𝓘(ℝ, ℝ)) (I' := ThreeModel)
    unfold stageRegularizedLagrangian lVelocity
    rw [hder, hval]
    rfl
  have hheadLag := hlagEq eta (gamma jf) a v hav (fun _ hr => hetaLeft _ hr.2)
  have htailEq := hlagEq eta tail v w hvw (fun _ hr => hetaRight _ hr.1)
  have hheadInt : IntervalIntegrable (H.stageRegularizedLagrangian first T eta) volume a v :=
    (show IntervalIntegrable (H.stageRegularizedLagrangian first T (gamma jf)) volume a v from
      by simpa only [jf, a, hendv] using hint jf).congr_uIoo hheadLag.symm
  have hetaTailInt := htailInt.congr_uIoo htailEq.symm
  have hetaInt := hheadInt.trans hetaTailInt
  have hetaAction : H.stageRegularizedAction first T eta a w =
      H.stageRegularizedAction first T (gamma jf) a v + H.stageRegularizedAction first T tail v w := by
    unfold stageRegularizedAction
    rw [← intervalIntegral.integral_add_adjacent_intervals hheadInt hetaTailInt,
      intervalIntegral.integral_congr_uIoo hheadLag, intervalIntegral.integral_congr_uIoo htailEq]
  let beta := Function.update gamma jf eta
  have hbetaFirst : beta jf = eta := Function.update_self ..
  have hbetaOther (j : H.StageInterval first last) (hj : j ≠ jf) : beta j = gamma j :=
    Function.update_of_ne hj ..
  have hbetaLeft (j : H.StageInterval first last) (r : ℝ) (hr : r ≤ v) : beta j r = gamma j r := by
    by_cases hj : j = jf
    · subst j
      rw [hbetaFirst]
      exact hetaLeft r hr
    · rw [hbetaOther j hj]
  refine ⟨beta, ?_, ?_, hbetaLeft, hbetaLeft _ u huv, ?_, ?_, ?_⟩
  · intro j
    by_cases hj : j = jf
    · subst j
      simpa only [hbetaFirst, jf, hendw, a] using hetaAC
    · rw [hbetaOther j hj, hendOther j hj]
      exact hgamma j
  · intro j
    by_cases hj : j = jf
    · subst j
      simpa only [hbetaFirst, jf, hendw, a] using hetaInt
    · rw [hbetaOther j hj, hendOther j hj]
      exact hint j
  · intro r hr
    exact hbetaFirst ▸ hetaRight r hr
  · intro i hf hl
    obtain ⟨z, hzold, hznew⟩ := hnodes i hf hl
    have hiV : Real.sqrt (T - H.time i.succ) ≤ v := by
      have hb := H.regularizedStage_bounds hu huv hupper hvD
        ⟨i.castSucc, hf, i.castSucc_lt_succ.le.trans hl⟩
      rw [H.regularizedStageStart_castSucc_eq_event_clock hupper i hl] at hb
      exact hb.2.1.trans hb.2.2
    exact ⟨z, hzold.trans (hbetaLeft _ _ hiV).symm, hznew.trans (hbetaLeft _ _ hiV).symm⟩
  · have hsum : (∑ j : H.StageInterval first last, H.stageRegularizedAction j.val T (beta j)
        (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T w j.val)) =
        (∑ j : H.StageInterval first last, H.stageRegularizedAction j.val T (gamma j)
          (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val)) +
          H.stageRegularizedAction first T tail v w := by
      calc
        _ = ∑ j : H.StageInterval first last,
            (H.stageRegularizedAction j.val T (gamma j)
              (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val) +
              if j = jf then H.stageRegularizedAction first T tail v w else 0) := by
          apply Finset.sum_congr rfl
          intro j _
          by_cases hj : j = jf
          · subst j
            simpa only [hbetaFirst, jf, hendw, hendv, ite_eq_left rfl, ite_true, a] using hetaAction
          · simp only [hbetaOther j hj, hendOther j hj, ite_eq_right hj, add_zero]
        _ = _ := by simp only [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    exact hsum.trans_le (add_le_add le_rfl htailBound)

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

universe uMinExtend

private theorem exists_spatial_action_minimum_le_of_constant_tail
    (H : ObservedHistory.{uMinExtend})
    (first last : Fin (H.eventCount + 1)) (hle : first ≤ last)
    {T B u v w A : ℝ} (hvw : v ≤ w)
    (hupper : T - u ^ 2 ∈ H.stageDomain last)
    (hvpast : T - v ^ 2 ∈ Ico (H.time first) (H.stageEndTime first))
    (hwpast : T - w ^ 2 ∈ Ico (H.time first) (H.stageEndTime first))
    (hscalar : ∀ j : H.StageInterval first last,
      ∀ r ∈ Ioo (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T w j.val),
      ∀ x : (H.stage j.val).Carrier, -B ≤ metricScalarAt (H.stageMetric j.val (T - r ^ 2)) x)
    (C : ℝ) (hceiling : ∀ r ∈ Icc v w, ∀ x : (H.stage first).Carrier,
      metricScalarAt (H.stageMetric first (T - r ^ 2)) x ≤ C)
    (p : (H.stage last).Carrier) (q : (H.stage first).Carrier)
    (hA : A ∈ H.regularizedC1ActionValues first last hle T u v p q) :
    ∃ (m : ℝ) (y : (H.stage first).Carrier),
      m ∈ H.regularizedC1ActionValues first last hle T u w p y ∧
      (∀ (z : (H.stage first).Carrier) (L : ℝ),
        L ∈ H.regularizedC1ActionValues first last hle T u w p z → m ≤ L) ∧
      m ≤ A + (2 * C / 3) * (w ^ 3 - v ^ 3) := by
  classical
  obtain ⟨hu, huv, huppercc, _, gamma, hgamma, hint, hrecent, _, hnodes, hsum⟩ := hA
  have huw := huv.trans hvw
  have hwD := H.mem_stageDomain_of_mem_Ico hwpast
  obtain ⟨beta, hbeta, hbetaInt, _, hbetaRecent, _, hbetaNodes, hbetaSum⟩ :=
    exists_constant_tail_extension_action_le H first last hle hu huv hvw huppercc
      hvpast hwpast C hceiling gamma
      (fun j => Manifold.absolutelyContinuousOnInterval_of_contMDiffOn (hgamma j).contMDiffOn)
      hint hnodes
  let y₀ := beta ⟨first, le_rfl, hle⟩ w
  let L := ∑ j : H.StageInterval first last, H.stageRegularizedAction j.val T (beta j)
    (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T w j.val)
  have hbetaExt : H.regularizedExtendedAction first last T B u w beta = (L : WithTop ℝ) := by
    apply H.regularizedExtendedAction_eq_sum_action first last hu huw huppercc hwD beta hbetaInt
    intro j
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
    exact hscalar j r hr (beta j r)
  have hmember : (L : WithTop ℝ) ∈ H.regularizedActionValues first last hle T B u w p y₀ :=
    ⟨hu, huw, huppercc, hwD, beta, hbeta, hbetaRecent.trans hrecent, rfl, hbetaNodes, hbetaExt⟩
  have hcostLe := H.regularizedCost_le_of_competitor first last hle T B u w p y₀ hmember
  have hfinite : H.regularizedCost first last hle T B u w p y₀ ≠ ⊤ :=
    ne_top_of_le_ne_top WithTop.coe_ne_top hcostLe
  obtain ⟨y, eta, heta, hetaInt, hetaRecent, hetaPast, hetaNodes, hcost, hmin⟩ :=
    H.exists_spatial_regularizedCost_minimizer first last hle T B u w hupper hscalar p ⟨y₀, hfinite⟩
  let m := ∑ j : H.StageInterval first last, H.stageRegularizedAction j.val T (eta j)
    (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T w j.val)
  refine ⟨m, y, ⟨hu, huw, huppercc, hwD, eta, heta, hetaInt, hetaRecent, hetaPast, hetaNodes, rfl⟩,
    ?_, ?_⟩
  · intro z value hvalue
    have hvalueAC := H.coe_mem_regularizedActionValues_of_mem_regularizedC1ActionValues
      first last hle hscalar p z hvalue
    exact WithTop.coe_le_coe.mp ((hmin z).trans
      (H.regularizedCost_le_of_competitor first last hle T B u w p z hvalueAC))
  · have hmL : m ≤ L := WithTop.coe_le_coe.mp ((hmin y₀).trans hcostLe)
    apply hmL.trans
    simpa only [L, hsum] using hbetaSum

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

universe u

private theorem tail_truncation_action_ge
    (H : ObservedHistory.{u}) (first last : Fin (H.eventCount + 1)) (hle : first ≤ last)
    {T B u v w : ℝ} (hu : 0 ≤ u) (huv : u ≤ v) (hvw : v ≤ w)
    (hupper : T - u ^ 2 ∈ Icc (H.time last) (H.stageEndTime last))
    (hvpast : T - v ^ 2 ∈ H.stageDomain first)
    (hwpast : T - w ^ 2 ∈ H.stageDomain first)
    (gamma : (j : H.StageInterval first last) → ℝ → (H.stage j.val).Carrier)
    (hgamma : ∀ j, Manifold.absolutelyContinuousOnInterval ThreeModel (gamma j)
      (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T w j.val))
    (hint : ∀ j, IntervalIntegrable (H.stageRegularizedLagrangian j.val T (gamma j)) volume
      (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T w j.val))
    (hnodes : ∀ (i : Fin H.eventCount) (hf : first ≤ i.castSucc) (hl : i.succ ≤ last),
      ∃ z : (H.event i).old,
        z.val.val = gamma ⟨i.castSucc, hf, i.castSucc_lt_succ.le.trans hl⟩
          (Real.sqrt (T - H.time i.succ)) ∧
        (H.event i).oldOutput z = gamma ⟨i.succ, hf.trans i.castSucc_lt_succ.le, hl⟩
          (Real.sqrt (T - H.time i.succ)))
    (hscalar : ∀ r ∈ Ioo v w,
      -B ≤ metricScalarAt (H.stageMetric first (T - r ^ 2))
        (gamma ⟨first, le_rfl, hle⟩ r)) :
    (∀ j, Manifold.absolutelyContinuousOnInterval ThreeModel (gamma j)
      (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val)) ∧
    (∀ j, IntervalIntegrable (H.stageRegularizedLagrangian j.val T (gamma j)) volume
      (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val)) ∧
    H.regularizedExtendedAction first last T B u v gamma ∈
      H.regularizedActionValues first last hle T B u v
        (gamma ⟨last, hle, le_rfl⟩ u) (gamma ⟨first, le_rfl, hle⟩ v) ∧
    (∑ j : H.StageInterval first last, H.stageRegularizedAction j.val T (gamma j)
      (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val)) -
      (2 * B / 3) * (w ^ 3 - v ^ 3) ≤
    (∑ j : H.StageInterval first last, H.stageRegularizedAction j.val T (gamma j)
      (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T w j.val)) := by
  classical
  let jf : H.StageInterval first last := ⟨first, le_rfl, hle⟩
  let a := H.regularizedStageStart T u first
  have hv : 0 ≤ v := hu.trans huv
  have hw : 0 ≤ w := hv.trans hvw
  have hendv := H.regularizedStageEnd_eq_of_mem_stageDomain hv hvpast
  have hendw := H.regularizedStageEnd_eq_of_mem_stageDomain hw hwpast
  have hav : a ≤ v := by
    simpa only [a, jf, hendv] using (H.regularizedStage_bounds hu huv hupper hvpast jf).2.1
  have haw : a ≤ w := hav.trans hvw
  have hendOther (j : H.StageInterval first last) (hj : j ≠ jf) :
      H.regularizedStageEnd T w j.val = H.regularizedStageEnd T v j.val := by
    have hjlt : first < j.val := lt_of_le_of_ne j.property.1 (by
      intro heq
      exact hj (Subtype.ext heq.symm))
    have htime : H.stageEndTime first ≤ H.time j.val := by
      cases first using Fin.lastCases with
      | last => exact False.elim ((not_lt_of_ge (Fin.le_last j.val)) hjlt)
      | cast i =>
        rw [H.stageEndTime_castSucc]
        apply H.time_strictMono.monotone
        exact hjlt
    simp only [regularizedStageEnd,
      max_eq_right ((H.le_stageEndTime_of_mem_stageDomain hwpast).trans htime),
      max_eq_right ((H.le_stageEndTime_of_mem_stageDomain hvpast).trans htime)]
  have hwholeInt : IntervalIntegrable (H.stageRegularizedLagrangian first T (gamma jf)) volume a w := by
    simpa only [jf, a, hendw] using hint jf
  have hheadInt : IntervalIntegrable (H.stageRegularizedLagrangian first T (gamma jf)) volume a v :=
    hwholeInt.mono_set (by
      simpa only [uIcc_of_le hav, uIcc_of_le haw] using Icc_subset_Icc le_rfl hvw)
  have htailInt : IntervalIntegrable (H.stageRegularizedLagrangian first T (gamma jf)) volume v w :=
    hwholeInt.mono_set (by
      simpa only [uIcc_of_le hvw, uIcc_of_le haw] using Icc_subset_Icc hav le_rfl)
  have hgammaV (j : H.StageInterval first last) :
      Manifold.absolutelyContinuousOnInterval ThreeModel (gamma j)
        (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val) := by
    by_cases hj : j = jf
    · subst j
      have hwhole : Manifold.absolutelyContinuousOnInterval ThreeModel (gamma jf) a w := by
        simpa only [jf, a, hendw] using hgamma jf
      have hhead := Manifold.absolutelyContinuousOnInterval_mono hwhole (show uIcc a v ⊆ uIcc a w by
        simpa only [uIcc_of_le hav, uIcc_of_le haw] using Icc_subset_Icc le_rfl hvw)
      simpa only [jf, a, hendv] using hhead
    · rw [← hendOther j hj]
      exact hgamma j
  have hintV (j : H.StageInterval first last) :
      IntervalIntegrable (H.stageRegularizedLagrangian j.val T (gamma j)) volume
        (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val) := by
    by_cases hj : j = jf
    · subst j
      simpa only [jf, a, hendv] using hheadInt
    · rw [← hendOther j hj]
      exact hint j
  refine ⟨hgammaV, hintV, ⟨hu, huv, hupper, hvpast, gamma, hgammaV, rfl, rfl, hnodes, rfl⟩, ?_⟩
  have htailBound := H.stageRegularizedAction_ge_of_scalar_lower_bound first T (gamma jf)
    hvw hscalar htailInt
  have hadd : H.stageRegularizedAction first T (gamma jf) a w =
      H.stageRegularizedAction first T (gamma jf) a v + H.stageRegularizedAction first T (gamma jf) v w :=
    (intervalIntegral.integral_add_adjacent_intervals hheadInt htailInt).symm
  have hsum : (∑ j : H.StageInterval first last, H.stageRegularizedAction j.val T (gamma j)
      (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T w j.val)) =
      (∑ j : H.StageInterval first last, H.stageRegularizedAction j.val T (gamma j)
        (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val)) +
        H.stageRegularizedAction first T (gamma jf) v w := by
    calc
      _ = ∑ j : H.StageInterval first last,
          (H.stageRegularizedAction j.val T (gamma j)
            (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val) +
            if j = jf then H.stageRegularizedAction first T (gamma jf) v w else 0) := by
        apply Finset.sum_congr rfl
        intro j _
        by_cases hj : j = jf
        · subst j
          simpa only [jf, hendw, hendv, ite_eq_left rfl, ite_true, a] using hadd
        · simp only [hendOther j hj, ite_eq_right hj, add_zero]
      _ = _ := by simp only [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  rw [hsum]
  linarith

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

universe uMinBounds

private theorem spatial_action_minimum_clock_bounds
    (H : ObservedHistory.{uMinBounds})
    (first last : Fin (H.eventCount + 1)) (hle : first ≤ last)
    {T B u v w mv mw : ℝ} (hvw : v ≤ w)
    (hupper : T - u ^ 2 ∈ H.stageDomain last)
    (hvpast : T - v ^ 2 ∈ Ico (H.time first) (H.stageEndTime first))
    (hwpast : T - w ^ 2 ∈ Ico (H.time first) (H.stageEndTime first))
    (hscalar : ∀ j : H.StageInterval first last,
      ∀ r ∈ Ioo (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T w j.val),
      ∀ x : (H.stage j.val).Carrier, -B ≤ metricScalarAt (H.stageMetric j.val (T - r ^ 2)) x)
    (C : ℝ) (hceiling : ∀ r ∈ Icc v w, ∀ x : (H.stage first).Carrier,
      metricScalarAt (H.stageMetric first (T - r ^ 2)) x ≤ C)
    (p : (H.stage last).Carrier)
    (hvmin : ∃ q : (H.stage first).Carrier,
      mv ∈ H.regularizedC1ActionValues first last hle T u v p q ∧
      ∀ (z : (H.stage first).Carrier) (L : ℝ),
        L ∈ H.regularizedC1ActionValues first last hle T u v p z → mv ≤ L)
    (hwmin : ∃ q : (H.stage first).Carrier,
      mw ∈ H.regularizedC1ActionValues first last hle T u w p q ∧
      ∀ (z : (H.stage first).Carrier) (L : ℝ),
        L ∈ H.regularizedC1ActionValues first last hle T u w p z → mw ≤ L) :
    mv - (2 * B / 3) * (w ^ 3 - v ^ 3) ≤ mw ∧
      mw ≤ mv + (2 * C / 3) * (w ^ 3 - v ^ 3) := by
  classical
  obtain ⟨qv, hmv, hminv⟩ := hvmin
  obtain ⟨qw, hmw, hminw⟩ := hwmin
  have hu := hmv.1
  have huv := hmv.2.1
  obtain ⟨mnew, ynew, hmnew, _, hmnewBound⟩ :=
    exists_spatial_action_minimum_le_of_constant_tail H first last hle hvw hupper
      hvpast hwpast hscalar C hceiling p qv hmv
  refine ⟨?_, (hminw ynew mnew hmnew).trans hmnewBound⟩
  obtain ⟨_, _, huppercc, _, gamma, hgamma, hint, hrecent, _, hnodes, hsumw⟩ := hmw
  have hvD := H.mem_stageDomain_of_mem_Ico hvpast
  have hwD := H.mem_stageDomain_of_mem_Ico hwpast
  have hw : 0 ≤ w := (hu.trans huv).trans hvw
  have hendw := H.regularizedStageEnd_eq_of_mem_stageDomain hw hwD
  have hstart : H.regularizedStageStart T u first ≤ v := by
    have hb := (H.regularizedStage_bounds hu huv huppercc hvD
      (⟨first, le_rfl, hle⟩ : H.StageInterval first last)).2.1
    rwa [H.regularizedStageEnd_eq_of_mem_stageDomain (hu.trans huv) hvD] at hb
  obtain ⟨_, hintv, _, hbound⟩ := tail_truncation_action_ge H first last hle hu huv hvw
    huppercc hvD hwD gamma
    (fun j => Manifold.absolutelyContinuousOnInterval_of_contMDiffOn (hgamma j).contMDiffOn)
    hint hnodes (fun r hr => hscalar ⟨first, le_rfl, hle⟩ r
      ⟨hstart.trans_lt hr.1, by simpa only [hendw] using hr.2⟩ _)
  let A := ∑ j : H.StageInterval first last, H.stageRegularizedAction j.val T (gamma j)
    (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val)
  have hAv : A ∈ H.regularizedC1ActionValues first last hle T u v p
      (gamma ⟨first, le_rfl, hle⟩ v) :=
    ⟨hu, huv, huppercc, hvD, gamma, hgamma, hintv, hrecent, rfl, hnodes, rfl⟩
  have hmvA := hminv _ A hAv
  rw [hsumw] at hbound
  exact (sub_le_sub_right hmvA _).trans hbound

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

universe u

private theorem exists_scalar_ceiling_on_clock_interval
    (H : ObservedHistory.{u}) (j : Fin (H.eventCount + 1)) {T v w : ℝ}
    (hv : 0 ≤ v) (hvw : v ≤ w)
    (hpast : H.time j ≤ T - w ^ 2) (hrecent : T - v ^ 2 < H.stageEndTime j) :
    ∃ C : ℝ, ∀ r ∈ Icc v w, ∀ x : (H.stage j).Carrier,
      metricScalarAt (H.stageMetric j (T - r ^ 2)) x ≤ C := by
  have hsq : v ^ 2 ≤ w ^ 2 := (sq_le_sq₀ hv (hv.trans hvw)).mpr hvw
  obtain ⟨D, S, hS, hmetric, hcarrier⟩ :
      ∃ (D : RealTimeInterval) (S : SolutionOn (I := ThreeModel) (M := (H.stage j).Carrier) D),
        IsSolutionOn S ∧ (∀ t, S.base.metric t = H.stageMetric j t) ∧
        Icc (T - w ^ 2) (T - v ^ 2) ⊆ D.carrier := by
    cases j using Fin.lastCases with
    | last =>
      have hfinal : H.time (Fin.last H.eventCount) < H.horizon := by
        simpa only [H.stageEndTime_last] using
          (hpast.trans (sub_le_sub_left hsq T)).trans_lt hrecent
      refine ⟨_, (H.finalSlab hfinal).flow, (H.finalSlab hfinal).equation, ?_, ?_⟩
      · intro t
        simp only [stageMetric, Fin.lastCases_last, dite_eq_left hfinal]
      · intro t ht
        change H.time (Fin.last H.eventCount) ≤ t ∧ t ≤ H.horizon
        exact ⟨hpast.trans ht.1, ht.2.trans (by simpa only [H.stageEndTime_last] using hrecent.le)⟩
    | cast i =>
      refine ⟨_, (H.event i).incoming.flow, (H.event i).incoming.equation, ?_, ?_⟩
      · intro t
        simp only [stageMetric, Fin.lastCases_castSucc]
      · intro t ht
        change H.time i.castSucc ≤ t ∧ t < H.time i.succ
        exact ⟨hpast.trans ht.1, ht.2.trans_lt (by simpa only [H.stageEndTime_castSucc] using hrecent)⟩
  have hcompact : IsCompact (Icc (T - w ^ 2) (T - v ^ 2) ×ˢ (univ : Set (H.stage j).Carrier)) :=
    isCompact_Icc.prod isCompact_univ
  obtain ⟨C, hC⟩ := hcompact.bddAbove_image
    (hS.scalarCont.mono (prod_mono hcarrier (subset_refl univ)))
  refine ⟨C, ?_⟩
  intro r hr x
  have hrv : v ^ 2 ≤ r ^ 2 := (sq_le_sq₀ hv (hv.trans hr.1)).mpr hr.1
  have hrw : r ^ 2 ≤ w ^ 2 := (sq_le_sq₀ (hv.trans hr.1) (hv.trans hvw)).mpr hr.2
  have hbound := hC ⟨(T - r ^ 2, x),
    ⟨⟨sub_le_sub_left hrw T, sub_le_sub_left hrv T⟩, mem_univ x⟩, rfl⟩
  change metricScalarAt (S.base.metric (T - r ^ 2)) x ≤ C at hbound
  rwa [hmetric] at hbound

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

universe uMinCont

private theorem continuousOn_spatial_action_minimum
    (H : ObservedHistory.{uMinCont})
    (first last : Fin (H.eventCount + 1)) (hle : first ≤ last)
    {T B u a b : ℝ} (hu : 0 ≤ u) (hua : u ≤ a) (hab : a ≤ b)
    (hupper : T - u ^ 2 ∈ H.stageDomain last)
    (hapast : T - a ^ 2 ∈ Ico (H.time first) (H.stageEndTime first))
    (hbpast : T - b ^ 2 ∈ Ico (H.time first) (H.stageEndTime first))
    (hscalar : ∀ j : H.StageInterval first last,
      ∀ r ∈ Ioo (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T b j.val),
      ∀ x : (H.stage j.val).Carrier, -B ≤ metricScalarAt (H.stageMetric j.val (T - r ^ 2)) x)
    (p : (H.stage last).Carrier) (m : ℝ → ℝ)
    (hmin : ∀ v ∈ Icc a b, ∃ q : (H.stage first).Carrier,
      m v ∈ H.regularizedC1ActionValues first last hle T u v p q ∧
      ∀ (z : (H.stage first).Carrier) (L : ℝ),
        L ∈ H.regularizedC1ActionValues first last hle T u v p z → m v ≤ L) :
    ContinuousOn m (Icc a b) := by
  have ha := hu.trans hua
  have hb := ha.trans hab
  obtain ⟨C, hC⟩ := exists_scalar_ceiling_on_clock_interval H first ha hab hbpast.1 hapast.2
  have hreg (v : ℝ) (hv : v ∈ Icc a b) :
      T - v ^ 2 ∈ Ico (H.time first) (H.stageEndTime first) := by
    have hav : a ^ 2 ≤ v ^ 2 := (sq_le_sq₀ ha (ha.trans hv.1)).mpr hv.1
    have hvb : v ^ 2 ≤ b ^ 2 := (sq_le_sq₀ (ha.trans hv.1) hb).mpr hv.2
    exact ⟨by linarith [hbpast.1], by linarith [hapast.2]⟩
  have hfloor (v : ℝ) (hv : v ∈ Icc a b) (j : H.StageInterval first last)
      (r : ℝ) (hr : r ∈ Ioo (H.regularizedStageStart T u j.val)
        (H.regularizedStageEnd T v j.val)) (x : (H.stage j.val).Carrier) :
      -B ≤ metricScalarAt (H.stageMetric j.val (T - r ^ 2)) x := by
    have hvb : v ^ 2 ≤ b ^ 2 := (sq_le_sq₀ (ha.trans hv.1) hb).mpr hv.2
    have hend : H.regularizedStageEnd T v j.val ≤ H.regularizedStageEnd T b j.val := by
      unfold regularizedStageEnd
      apply Real.sqrt_le_sqrt
      exact sub_le_sub_left (max_le_max_right _ (sub_le_sub_left hvb T)) T
    exact hscalar j r ⟨hr.1, hr.2.trans_le hend⟩ x
  let K := |2 * B / 3| + |2 * C / 3|
  have hBK : 2 * B / 3 ≤ K := (le_abs_self _).trans (le_add_of_nonneg_right (abs_nonneg _))
  have hCK : 2 * C / 3 ≤ K := (le_abs_self _).trans (le_add_of_nonneg_left (abs_nonneg _))
  have hordered (v w : ℝ) (hv : v ∈ Icc a b) (hw : w ∈ Icc a b) (hvw : v ≤ w) :
      |m w - m v| ≤ K * |w ^ 3 - v ^ 3| := by
    have hbounds := spatial_action_minimum_clock_bounds H first last hle hvw hupper
      (hreg v hv) (hreg w hw) (hfloor w hw) C
      (fun r hr => hC r ⟨hv.1.trans hr.1, hr.2.trans hw.2⟩) p (hmin v hv) (hmin w hw)
    have hcube : 0 ≤ w ^ 3 - v ^ 3 := sub_nonneg.mpr (pow_le_pow_left₀ (ha.trans hv.1) hvw _)
    rw [abs_of_nonneg hcube]
    apply abs_le.mpr
    constructor
    · have hB := mul_le_mul_of_nonneg_right hBK hcube
      linarith [hbounds.1]
    · have hC' := mul_le_mul_of_nonneg_right hCK hcube
      linarith [hbounds.2]
  have hdist (v w : ℝ) (hv : v ∈ Icc a b) (hw : w ∈ Icc a b) :
      dist (m w) (m v) ≤ K * |w ^ 3 - v ^ 3| := by
    rw [Real.dist_eq]
    rcases le_total v w with hvw | hwv
    · exact hordered v w hv hw hvw
    · simpa only [abs_sub_comm] using hordered w v hw hv hwv
  intro v hv
  apply tendsto_iff_dist_tendsto_zero.mpr
  have hlimit : Tendsto (fun w : ℝ => K * |w ^ 3 - v ^ 3|) (𝓝[Icc a b] v) (𝓝 0) := by
    have hc : ContinuousAt (fun w : ℝ => K * |w ^ 3 - v ^ 3|) v := by fun_prop
    simpa only [sub_self, abs_zero, mul_zero] using hc.continuousWithinAt.tendsto
  exact tendsto_const_nhds.squeeze' hlimit
    (Eventually.of_forall (fun w => dist_nonneg))
    (by filter_upwards [self_mem_nhdsWithin] with w hw; exact hdist v w hv hw)

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

universe uMinCost

private theorem regularizedCost_eq_and_le_of_spatial_action_minimum
    (H : ObservedHistory.{uMinCost})
    (first last : Fin (H.eventCount + 1)) (hle : first ≤ last)
    (T B u v : ℝ)
    (hupper : T - u ^ 2 ∈ H.stageDomain last)
    (hscalar : ∀ j : H.StageInterval first last,
      ∀ r ∈ Ioo (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T v j.val),
      ∀ x : (H.stage j.val).Carrier, -B ≤ metricScalarAt (H.stageMetric j.val (T - r ^ 2)) x)
    (p : (H.stage last).Carrier) (q : (H.stage first).Carrier) (m : ℝ)
    (hmem : m ∈ H.regularizedC1ActionValues first last hle T u v p q)
    (hminimum : ∀ (z : (H.stage first).Carrier) (L : ℝ),
      L ∈ H.regularizedC1ActionValues first last hle T u v p z → m ≤ L) :
    H.regularizedCost first last hle T B u v p q = (m : WithTop ℝ) ∧
      ∀ z : (H.stage first).Carrier,
        (m : WithTop ℝ) ≤ H.regularizedCost first last hle T B u v p z := by
  have hcost (z : (H.stage first).Carrier) :=
    H.regularizedCost_eq_regularizedC1Cost first last hle T B u v hupper hscalar p z
  refine ⟨(hcost q).trans (H.regularizedC1Cost_eq_of_minimum first last hle T u v m
    p q hmem (hminimum q)), ?_⟩
  intro z
  rw [hcost z]
  by_cases hne : (H.regularizedC1ActionValues first last hle T u v p z).Nonempty
  · apply le_csInf (hne.image (fun r : ℝ => (r : WithTop ℝ)))
    rintro value ⟨L, hL, rfl⟩
    exact WithTop.coe_le_coe.mpr (hminimum z L hL)
  · rw [H.regularizedC1Cost_eq_top_of_no_competitor first last hle T u v p z
      (Set.not_nonempty_iff_eq_empty.mp hne)]
    exact le_top

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

universe uMinExists

theorem exists_continuous_spatial_regularizedCost_minimum
    (H : ObservedHistory.{uMinExists})
    (first last : Fin (H.eventCount + 1)) (hle : first ≤ last)
    {T B u a b : ℝ} (hu : 0 ≤ u) (hua : u ≤ a) (hab : a ≤ b)
    (hupper : T - u ^ 2 ∈ H.stageDomain last)
    (hapast : T - a ^ 2 ∈ Ico (H.time first) (H.stageEndTime first))
    (hbpast : T - b ^ 2 ∈ Ico (H.time first) (H.stageEndTime first))
    (hscalar : ∀ j : H.StageInterval first last,
      ∀ r ∈ Ioo (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T b j.val),
      ∀ x : (H.stage j.val).Carrier, -B ≤ metricScalarAt (H.stageMetric j.val (T - r ^ 2)) x)
    (p : (H.stage last).Carrier)
    (hfinite : ∃ q : (H.stage first).Carrier,
      H.regularizedCost first last hle T B u a p q ≠ ⊤) :
    ∃ m : ℝ → ℝ, ContinuousOn m (Icc a b) ∧
      ∀ v ∈ Icc a b, ∃ q : (H.stage first).Carrier,
        m v ∈ H.regularizedC1ActionValues first last hle T u v p q ∧
        H.regularizedCost first last hle T B u v p q = (m v : WithTop ℝ) ∧
        ∀ z : (H.stage first).Carrier,
          (m v : WithTop ℝ) ≤ H.regularizedCost first last hle T B u v p z := by
  classical
  have ha := hu.trans hua
  have hb := ha.trans hab
  have huppercc : T - u ^ 2 ∈ Icc (H.time last) (H.stageEndTime last) :=
    ⟨H.time_le_of_mem_stageDomain hupper, H.le_stageEndTime_of_mem_stageDomain hupper⟩
  have hreg (v : ℝ) (hv : v ∈ Icc a b) :
      T - v ^ 2 ∈ Ico (H.time first) (H.stageEndTime first) := by
    have hav : a ^ 2 ≤ v ^ 2 := (sq_le_sq₀ ha (ha.trans hv.1)).mpr hv.1
    have hvb : v ^ 2 ≤ b ^ 2 := (sq_le_sq₀ (ha.trans hv.1) hb).mpr hv.2
    exact ⟨by linarith [hbpast.1], by linarith [hapast.2]⟩
  have hfloor (v : ℝ) (hv : v ∈ Icc a b) (j : H.StageInterval first last)
      (r : ℝ) (hr : r ∈ Ioo (H.regularizedStageStart T u j.val)
        (H.regularizedStageEnd T v j.val)) (x : (H.stage j.val).Carrier) :
      -B ≤ metricScalarAt (H.stageMetric j.val (T - r ^ 2)) x := by
    have hvb : v ^ 2 ≤ b ^ 2 := (sq_le_sq₀ (ha.trans hv.1) hb).mpr hv.2
    have hend : H.regularizedStageEnd T v j.val ≤ H.regularizedStageEnd T b j.val := by
      unfold regularizedStageEnd
      apply Real.sqrt_le_sqrt
      exact sub_le_sub_left (max_le_max_right _ (sub_le_sub_left hvb T)) T
    exact hscalar j r ⟨hr.1, hr.2.trans_le hend⟩ x
  obtain ⟨q, gamma, hgamma, hint, hrecent, hpast, hnodes, _, _⟩ :=
    H.exists_spatial_regularizedCost_minimizer first last hle T B u a hupper
      (hfloor a ⟨le_rfl, hab⟩) p hfinite
  let A := ∑ j : H.StageInterval first last, H.stageRegularizedAction j.val T (gamma j)
    (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T a j.val)
  have hA : A ∈ H.regularizedC1ActionValues first last hle T u a p q :=
    ⟨hu, hua, huppercc, H.mem_stageDomain_of_mem_Ico hapast,
      gamma, hgamma, hint, hrecent, hpast, hnodes, rfl⟩
  obtain ⟨C, hC⟩ := exists_scalar_ceiling_on_clock_interval H first ha hab hbpast.1 hapast.2
  have hex (v : Icc a b) := exists_spatial_action_minimum_le_of_constant_tail H first last hle
    v.property.1 hupper hapast (hreg v v.property) (hfloor v v.property) C
    (fun r hr => hC r ⟨hr.1, hr.2.trans v.property.2⟩) p q hA
  choose m q hm hminimal hbound using hex
  let f : ℝ → ℝ := fun v => if hv : v ∈ Icc a b then m ⟨v, hv⟩ else 0
  have hf (v : ℝ) (hv : v ∈ Icc a b) : ∃ q : (H.stage first).Carrier,
      f v ∈ H.regularizedC1ActionValues first last hle T u v p q ∧
      ∀ (z : (H.stage first).Carrier) (L : ℝ),
        L ∈ H.regularizedC1ActionValues first last hle T u v p z → f v ≤ L := by
    refine ⟨q ⟨v, hv⟩, ?_, ?_⟩
    · simpa only [f, dite_eq_left hv] using hm ⟨v, hv⟩
    · simpa only [f, dite_eq_left hv] using hminimal ⟨v, hv⟩
  refine ⟨f, continuousOn_spatial_action_minimum H first last hle hu hua hab hupper
    hapast hbpast hscalar p f hf, ?_⟩
  intro v hv
  obtain ⟨q, hmem, hminimum⟩ := hf v hv
  exact ⟨q, hmem, regularizedCost_eq_and_le_of_spatial_action_minimum H first last hle
    T B u v hupper (hfloor v hv) p q (f v) hmem hminimum⟩

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab

universe u

variable {P : OrientedThreeStage.{u}} {a s : ℝ} {G : P.IncomingSlab a s}

private theorem TerminalLimitMetric.exists_constant_incoming_action_le
    (L : G.TerminalLimitMetric) (x : G.terminalRegularOpen)
    {T k : ℝ} (hk : 0 ≤ k) (hTk : T - k ^ 2 = s) :
    ∃ d > k, ∃ C : ℝ, ∀ w ∈ Icc k d,
      (∀ r ∈ Ioc k w, T - r ^ 2 ∈ Ioo a s) ∧
      IntervalIntegrable (lRegularizedLagrangian G.flow T (fun _ => x.val)) volume k w ∧
      lRegularizedAction G.flow T (fun _ => x.val) k w ≤
        (2 * C / 3) * (w ^ 3 - k ^ 3) := by
  obtain ⟨c, hac, hcs⟩ := exists_between G.lt
  let W : TopologicalSpace.Opens G.terminalRegularOpen := ⊤
  let y : W := ⟨x, mem_univ x⟩
  let S := L.closedSolution W hcs.le
  have hS : IsSolutionOn S := L.closedSolution_isSolutionOn W hac.le hcs
  let d := Real.sqrt (T - c)
  have hdc : d ^ 2 = T - c := Real.sq_sqrt (by nlinarith [sq_nonneg k])
  have hd0 : 0 ≤ d := Real.sqrt_nonneg _
  have hkd : k < d := by nlinarith
  have hclock (r : ℝ) (hr : r ∈ Icc k d) : T - r ^ 2 ∈ Icc c s := by
    have hr0 : 0 ≤ r := hk.trans hr.1
    have hlo := (sq_le_sq₀ hk hr0).mpr hr.1
    have hhi := (sq_le_sq₀ hr0 hd0).mpr hr.2
    constructor <;> nlinarith
  have hbefore (r : ℝ) (hr : r ∈ Ioc k d) : T - r ^ 2 ∈ Ioo a s := by
    have hh := hclock r ⟨hr.1.le, hr.2⟩
    have hsq := (sq_lt_sq₀ hk (hk.trans hr.1.le)).mpr hr.1
    exact ⟨hac.trans_le hh.1, by nlinarith⟩
  have hsc : ContinuousOn (fun t : ℝ => S.scalar t y) (Icc c s) := by
    have hc : ContinuousOn (fun z : ℝ × W => S.scalar z.1 z.2)
        ((RealTimeInterval.closed c s hcs.le).carrier ×ˢ univ) := hS.scalarCont
    have hmap : ContinuousOn (fun t : ℝ => (t, y)) (Icc c s) :=
      continuousOn_id.prodMk continuousOn_const
    exact hc.comp (f := fun t : ℝ => (t, y)) hmap (fun _ ht => ⟨ht, mem_univ _⟩)
  obtain ⟨C, hC⟩ := isCompact_Icc.bddAbove_image hsc
  have hscalar (r : ℝ) (hr : r ∈ Ioc k d) :
      S.scalar (T - r ^ 2) y = G.flow.scalar (T - r ^ 2) x.val := by
    let : IsManifold ThreeModel 1 G.terminalRegularOpen := IsManifold.of_le (n := ∞) (by decide)
    let : IsManifold ThreeModel 1 W := IsManifold.of_le (n := ∞) (by decide)
    calc
      S.scalar (T - r ^ 2) y = metricScalarAt (L.extendedMetric (T - r ^ 2)) x :=
        CheegerGromovCompactness.metricScalarAt_restrictOpen
          (L.extendedMetric (T - r ^ 2)) W y
      _ = metricScalarAt ((G.flow.base.metric (T - r ^ 2)).restrictOpen G.terminalRegularOpen) x := by
        rw [L.extendedMetric_before (hbefore r hr).2]
      _ = G.flow.scalar (T - r ^ 2) x.val :=
        CheegerGromovCompactness.metricScalarAt_restrictOpen
          (G.flow.base.metric (T - r ^ 2)) G.terminalRegularOpen x
  have hcont : ContinuousOn (fun r : ℝ => 2 * r ^ 2 * S.scalar (T - r ^ 2) y) (Icc k d) :=
    (continuousOn_const.mul (continuousOn_id.pow 2)).mul
      (hsc.comp (continuous_const.sub (continuous_id.pow 2)).continuousOn hclock)
  refine ⟨d, hkd, C, ?_⟩
  intro w hw
  have hpolyInt : IntervalIntegrable
      (fun r : ℝ => 2 * r ^ 2 * S.scalar (T - r ^ 2) y) volume k w :=
    (hcont.mono (Icc_subset_Icc le_rfl hw.2)).intervalIntegrable_of_Icc hw.1
  have hlag : lRegularizedLagrangian G.flow T (fun _ => x.val) =ᵐ[volume.restrict (Ι k w)]
      fun r : ℝ => 2 * r ^ 2 * S.scalar (T - r ^ 2) y := by
    rw [uIoc_of_le hw.1]
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
    have hv : lVelocity (I := ThreeModel) (fun _ : ℝ => x.val) r = 0 := by
      simp only [lVelocity, mfderiv_const]
      rfl
    simp only [lRegularizedLagrangian, hv, map_zero, mul_zero, zero_add]
    rw [hscalar r ⟨hr.1, hr.2.trans hw.2⟩]
  have hright : IntervalIntegrable (fun r : ℝ => 2 * r ^ 2 * C) volume k w :=
    (by fun_prop : Continuous (fun r : ℝ => 2 * r ^ 2 * C)).intervalIntegrable _ _
  have hle := intervalIntegral.integral_mono_on hw.1 hpolyInt hright (fun r hr =>
    mul_le_mul_of_nonneg_left (hC ⟨T - r ^ 2, hclock r ⟨hr.1, hr.2.trans hw.2⟩, rfl⟩)
      (by positivity))
  have hpolyEq : (∫ r in k..w, 2 * r ^ 2 * C) = (2 * C / 3) * (w ^ 3 - k ^ 3) := by
    rw [intervalIntegral.integral_mul_const, intervalIntegral.integral_const_mul, integral_pow]
    norm_num
    ring
  refine ⟨fun r hr => hbefore r ⟨hr.1, hr.2.trans hw.2⟩,
    (intervalIntegrable_congr_ae hlag).mpr hpolyInt, ?_⟩
  change (∫ r in k..w, lRegularizedLagrangian G.flow T (fun _ => x.val) r) ≤ _
  rw [intervalIntegral.integral_congr_ae_restrict hlag]
  exact hle.trans_eq hpolyEq

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

universe uEventUpper

private theorem exists_event_prefix_action_le
    (H : ObservedHistory.{uEventUpper}) (i : Fin H.eventCount)
    (last : Fin (H.eventCount + 1)) (hl : i.succ ≤ last)
    {T u m : ℝ} (p : (H.stage last).Carrier) (q : (H.stage i.succ).Carrier)
    (hm : m ∈ H.regularizedC1ActionValues i.succ last hl T u
      (Real.sqrt (T - H.time i.succ)) p q)
    (x : (H.event i).incoming.terminalRegularOpen)
    (hcross : (H.event i).RegularCrossing x.val q) :
    ∃ d > Real.sqrt (T - H.time i.succ), ∃ C : ℝ,
      ∀ w ∈ Ioc (Real.sqrt (T - H.time i.succ)) d, ∃ A : ℝ,
        A ∈ H.regularizedC1ActionValues i.castSucc last
          (i.castSucc_le_succ.trans hl) T u w p x.val ∧
        A ≤ m + (2 * C / 3) * (w ^ 3 - (Real.sqrt (T - H.time i.succ)) ^ 3) := by
  let k := Real.sqrt (T - H.time i.succ)
  have hk : 0 ≤ k := Real.sqrt_nonneg _
  have hsT : H.time i.succ ≤ T :=
    (H.time_le_of_mem_stageDomain hm.2.2.2.1).trans (sub_le_self _ (sq_nonneg _))
  have hTk : T - k ^ 2 = H.time i.succ := by
    rw [show k ^ 2 = T - H.time i.succ from Real.sq_sqrt (sub_nonneg.mpr hsT)]
    ring
  obtain ⟨d, hkd, C, htail⟩ :=
    (H.event i).terminal.exists_constant_incoming_action_le x hk hTk
  obtain ⟨z, _, hzx, hzq⟩ := hcross
  refine ⟨d, hkd, C, ?_⟩
  intro w hw
  obtain ⟨hclock, hint, hbound⟩ := htail w ⟨hw.1.le, hw.2⟩
  have hpast : T - w ^ 2 ∈ H.stageDomain i.castSucc := by
    apply H.mem_stageDomain_of_mem_Ioo
    simpa only [H.stageEndTime_castSucc] using hclock w ⟨hw.1, le_rfl⟩
  have hupperOld : T - k ^ 2 ∈ Icc (H.time i.castSucc) (H.stageEndTime i.castSucc) := by
    rw [hTk, H.stageEndTime_castSucc]
    exact ⟨(H.time_strictMono i.castSucc_lt_succ).le, le_rfl⟩
  let Aold := H.stageRegularizedAction i.castSucc T (fun _ => x.val) k w
  have hAold : Aold ∈ H.regularizedC1ActionValues i.castSucc i.castSucc le_rfl
      T k w z.val.val x.val := by
    apply (H.mem_regularizedC1ActionValues_self i.castSucc z.val.val x.val).mpr
    refine ⟨hk, hw.1.le, hupperOld, hpast, (fun _ => x.val), contMDiff_const, ?_, hzx.symm, rfl, rfl⟩
    rw [funext (H.stageRegularizedLagrangian_castSucc i T (fun _ => x.val))]
    exact hint
  refine ⟨Aold + m, ?_, ?_⟩
  · apply (H.mem_regularizedC1ActionValues_split_at_event (i.castSucc_le_succ.trans hl)
      i le_rfl hl hm.1 (hm.2.1.trans hw.1.le) hm.2.2.1 hpast p x.val).mpr
    refine ⟨z, Aold, m, hAold, ?_, rfl⟩
    simpa only [hzq] using hm
  · have hAoldBound : Aold ≤ (2 * C / 3) * (w ^ 3 - k ^ 3) := by
      simpa only [Aold, H.stageRegularizedAction_castSucc] using hbound
    linarith

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

universe u

private theorem action_ge_spatial_minimum_at_event
    (H : ObservedHistory.{u}) (i : Fin H.eventCount)
    (last : Fin (H.eventCount + 1)) (hl : i.succ ≤ last)
    {T B u v m A : ℝ}
    (p : (H.stage last).Carrier) (q : (H.stage i.castSucc).Carrier)
    (hA : A ∈ H.regularizedC1ActionValues i.castSucc last
      (i.castSucc_le_succ.trans hl) T u v p q)
    (hscalar : ∀ r ∈ Ioo (Real.sqrt (T - H.time i.succ)) v,
      ∀ x : (H.stage i.castSucc).Carrier,
        -B ≤ metricScalarAt (H.stageMetric i.castSucc (T - r ^ 2)) x)
    (hmin : ∀ (z : (H.stage i.succ).Carrier) (L : ℝ),
      L ∈ H.regularizedC1ActionValues i.succ last hl T u
        (Real.sqrt (T - H.time i.succ)) p z → m ≤ L) :
    m - (2 * B / 3) * (v ^ 3 - (Real.sqrt (T - H.time i.succ)) ^ 3) ≤ A := by
  obtain ⟨z, Aold, Anew, hold, hnew, hsum⟩ :=
    (H.mem_regularizedC1ActionValues_split_at_event (i.castSucc_le_succ.trans hl)
      i le_rfl hl hA.1 hA.2.1 hA.2.2.1 hA.2.2.2.1 p q).mp hA
  have hstart := H.regularizedStageStart_eq_of_mem_Icc hold.1 hold.2.2.1
  have hend := H.regularizedStageEnd_eq_of_mem_stageDomain (hold.1.trans hold.2.1)
    hold.2.2.2.1
  have hlower := H.regularizedC1ActionValues_ge_of_scalar_lower
    i.castSucc i.castSucc le_rfl T (Real.sqrt (T - H.time i.succ)) v B
    (fun j r hr x => by
      have hj : j = (⟨i.castSucc, le_rfl, le_rfl⟩ : H.StageInterval i.castSucc i.castSucc) :=
        Subtype.ext (le_antisymm j.property.2 j.property.1)
      subst j
      exact hscalar r (by simpa only [hstart, hend] using hr) x)
    z.val.val q hold
  have hnewLower := hmin _ Anew hnew
  linarith

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

universe uEventLimit

private theorem exists_spatial_minimum_tendsto_at_regular_event_from_old_side
    (H : ObservedHistory.{uEventLimit}) (i : Fin H.eventCount)
    (last : Fin (H.eventCount + 1)) (hl : i.succ ≤ last)
    {T B u m0 : ℝ}
    (hupper : T - u ^ 2 ∈ H.stageDomain last)
    (hscalar : ∀ j : H.StageInterval i.castSucc last,
      ∀ t ∈ H.stageDomain j.val, ∀ z : (H.stage j.val).Carrier,
        -B ≤ metricScalarAt (H.stageMetric j.val t) z)
    (p : (H.stage last).Carrier) (q : (H.stage i.succ).Carrier)
    (hm0 : m0 ∈ H.regularizedC1ActionValues i.succ last hl T u
      (Real.sqrt (T - H.time i.succ)) p q)
    (hmin0 : ∀ (z : (H.stage i.succ).Carrier) (A : ℝ),
      A ∈ H.regularizedC1ActionValues i.succ last hl T u
        (Real.sqrt (T - H.time i.succ)) p z → m0 ≤ A)
    (x : (H.event i).incoming.terminalRegularOpen)
    (hcross : (H.event i).RegularCrossing x.val q) :
    let k := Real.sqrt (T - H.time i.succ);
    ∃ d > k, ∃ C : ℝ, ∃ m : ℝ → ℝ,
      m k = m0 ∧ Tendsto m (𝓝[>] k) (𝓝 m0) ∧
      ∀ w ∈ Ioc k d, ∃ y : (H.stage i.castSucc).Carrier,
        m w ∈ H.regularizedC1ActionValues i.castSucc last
          (i.castSucc_le_succ.trans hl) T u w p y ∧
        H.regularizedCost i.castSucc last (i.castSucc_le_succ.trans hl) T B u w p y =
          (m w : WithTop ℝ) ∧
        (∀ z : (H.stage i.castSucc).Carrier,
          (m w : WithTop ℝ) ≤ H.regularizedCost i.castSucc last
            (i.castSucc_le_succ.trans hl) T B u w p z) ∧
        m0 - (2 * B / 3) * (w ^ 3 - k ^ 3) ≤ m w ∧
        m w ≤ m0 + (2 * C / 3) * (w ^ 3 - k ^ 3) := by
  classical
  let k := Real.sqrt (T - H.time i.succ)
  let hle := i.castSucc_le_succ.trans hl
  have huppercc : T - u ^ 2 ∈ Icc (H.time last) (H.stageEndTime last) :=
    ⟨H.time_le_of_mem_stageDomain hupper, H.le_stageEndTime_of_mem_stageDomain hupper⟩
  have hfloor (w : ℝ) (j : H.StageInterval i.castSucc last)
      (r : ℝ) (hr : r ∈ Ioo (H.regularizedStageStart T u j.val)
        (H.regularizedStageEnd T w j.val)) (z : (H.stage j.val).Carrier) :
      -B ≤ metricScalarAt (H.stageMetric j.val (T - r ^ 2)) z :=
    hscalar j (T - r ^ 2) (H.mapsTo_regularizedStage_Ioo T u w j.val hr) z
  obtain ⟨d, hkd, C, hcompetitor⟩ := exists_event_prefix_action_le H i last hl p q hm0 x hcross
  have hex (w : Ioc k d) : ∃ (m : ℝ) (y : (H.stage i.castSucc).Carrier),
      m ∈ H.regularizedC1ActionValues i.castSucc last hle T u w p y ∧
      H.regularizedCost i.castSucc last hle T B u w p y = (m : WithTop ℝ) ∧
      (∀ z : (H.stage i.castSucc).Carrier,
        (m : WithTop ℝ) ≤ H.regularizedCost i.castSucc last hle T B u w p z) ∧
      m0 - (2 * B / 3) * (w.val ^ 3 - k ^ 3) ≤ m ∧
      m ≤ m0 + (2 * C / 3) * (w.val ^ 3 - k ^ 3) := by
    obtain ⟨A, hA, hAbound⟩ := hcompetitor w w.property
    have hAAC := H.coe_mem_regularizedActionValues_of_mem_regularizedC1ActionValues
      i.castSucc last hle (hfloor w) p x.val hA
    have hcostLe := H.regularizedCost_le_of_competitor i.castSucc last hle T B u w p x.val hAAC
    have hfinite : H.regularizedCost i.castSucc last hle T B u w p x.val ≠ ⊤ :=
      ne_top_of_le_ne_top WithTop.coe_ne_top hcostLe
    obtain ⟨y, gamma, hgamma, hint, hrecent, hpast, hnodes, hcost, hminimal⟩ :=
      H.exists_spatial_regularizedCost_minimizer i.castSucc last hle T B u w
        hupper (hfloor w) p ⟨x.val, hfinite⟩
    let m := ∑ j : H.StageInterval i.castSucc last, H.stageRegularizedAction j.val T (gamma j)
      (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T w j.val)
    have hm : m ∈ H.regularizedC1ActionValues i.castSucc last hle T u w p y :=
      ⟨hA.1, hA.2.1, huppercc, hA.2.2.2.1,
        gamma, hgamma, hint, hrecent, hpast, hnodes, rfl⟩
    have hstart := H.regularizedStageStart_castSucc_eq_event_clock huppercc i hl
    have hend := H.regularizedStageEnd_eq_of_mem_stageDomain
      (hA.1.trans hA.2.1) hA.2.2.2.1
    have hlower := action_ge_spatial_minimum_at_event H i last hl p y hm
      (fun r hr z => hfloor w ⟨i.castSucc, le_rfl, hle⟩ r
        (by simpa only [hstart, hend] using hr) z) hmin0
    have hupperBound : m ≤ A := WithTop.coe_le_coe.mp ((hminimal x.val).trans hcostLe)
    exact ⟨m, y, hm, hcost, hminimal, hlower, hupperBound.trans hAbound⟩
  choose value point hvalue hcost hminimal hlower hupperBound using hex
  let m : ℝ → ℝ := fun w => if hw : w ∈ Ioc k d then value ⟨w, hw⟩ else m0
  have hm (w : ℝ) (hw : w ∈ Ioc k d) : ∃ y : (H.stage i.castSucc).Carrier,
      m w ∈ H.regularizedC1ActionValues i.castSucc last hle T u w p y ∧
      H.regularizedCost i.castSucc last hle T B u w p y = (m w : WithTop ℝ) ∧
      (∀ z : (H.stage i.castSucc).Carrier,
        (m w : WithTop ℝ) ≤ H.regularizedCost i.castSucc last hle T B u w p z) ∧
      m0 - (2 * B / 3) * (w ^ 3 - k ^ 3) ≤ m w ∧
      m w ≤ m0 + (2 * C / 3) * (w ^ 3 - k ^ 3) := by
    refine ⟨point ⟨w, hw⟩, ?_⟩
    simpa only [m, dite_eq_left hw] using
      And.intro (hvalue ⟨w, hw⟩) (And.intro (hcost ⟨w, hw⟩)
        (And.intro (hminimal ⟨w, hw⟩) (And.intro (hlower ⟨w, hw⟩) (hupperBound ⟨w, hw⟩))))
  have hnear : ∀ᶠ w in 𝓝[>] k, w ∈ Ioc k d := by
    filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (Iio_mem_nhds hkd)] with w hw hwd
    exact ⟨hw, hwd.le⟩
  have hleft : Tendsto (fun w : ℝ => m0 - (2 * B / 3) * (w ^ 3 - k ^ 3))
      (𝓝[>] k) (𝓝 m0) := by
    have hc : ContinuousAt (fun w : ℝ => m0 - (2 * B / 3) * (w ^ 3 - k ^ 3)) k := by fun_prop
    simpa only [sub_self, mul_zero, sub_zero] using hc.tendsto.mono_left nhdsWithin_le_nhds
  have hright : Tendsto (fun w : ℝ => m0 + (2 * C / 3) * (w ^ 3 - k ^ 3))
      (𝓝[>] k) (𝓝 m0) := by
    have hc : ContinuousAt (fun w : ℝ => m0 + (2 * C / 3) * (w ^ 3 - k ^ 3)) k := by fun_prop
    simpa only [sub_self, mul_zero, add_zero] using hc.tendsto.mono_left nhdsWithin_le_nhds
  have hlimit : Tendsto m (𝓝[>] k) (𝓝 m0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hleft hright
    · filter_upwards [hnear] with w hw
      exact (hm w hw).choose_spec.2.2.2.1
    · filter_upwards [hnear] with w hw
      exact (hm w hw).choose_spec.2.2.2.2
  refine ⟨d, hkd, C, m, ?_, hlimit, hm⟩
  exact dite_eq_right (by simp : k ∉ Ioc k d)

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

universe uEventContinuous

private theorem continuousOn_spatial_minimum_at_event_of_tendsto
    (H : ObservedHistory.{uEventContinuous}) (i : Fin H.eventCount)
    (last : Fin (H.eventCount + 1)) (hl : i.succ ≤ last)
    {T B u k d : ℝ}
    (hupper : T - u ^ 2 ∈ H.stageDomain last)
    (hscalar : ∀ j : H.StageInterval i.castSucc last,
      ∀ t ∈ H.stageDomain j.val, ∀ z : (H.stage j.val).Carrier,
        -B ≤ metricScalarAt (H.stageMetric j.val t) z)
    (p : (H.stage last).Carrier) (m : ℝ → ℝ)
    (hlimit : Tendsto m (𝓝[>] k) (𝓝 (m k)))
    (hminimum : ∀ w ∈ Ioc k d, ∃ y : (H.stage i.castSucc).Carrier,
      m w ∈ H.regularizedC1ActionValues i.castSucc last
        (i.castSucc_le_succ.trans hl) T u w p y ∧
      ∀ z : (H.stage i.castSucc).Carrier,
        (m w : WithTop ℝ) ≤ H.regularizedCost i.castSucc last
          (i.castSucc_le_succ.trans hl) T B u w p z) :
    ContinuousOn m (Icc k d) := by
  have hle := i.castSucc_le_succ.trans hl
  have hfloor (w : ℝ) (j : H.StageInterval i.castSucc last)
      (r : ℝ) (hr : r ∈ Ioo (H.regularizedStageStart T u j.val)
        (H.regularizedStageEnd T w j.val)) (z : (H.stage j.val).Carrier) :
      -B ≤ metricScalarAt (H.stageMetric j.val (T - r ^ 2)) z :=
    hscalar j (T - r ^ 2) (H.mapsTo_regularizedStage_Ioo T u w j.val hr) z
  intro w hw
  by_cases hwk : w = k
  · subst w
    have hc : ContinuousWithinAt m (Ioi k) k := hlimit
    apply hc.insert.mono
    intro r hr
    rcases eq_or_lt_of_le hr.1 with heq | hlt
    · exact mem_insert_iff.mpr (Or.inl heq.symm)
    · exact mem_insert_of_mem _ hlt
  · have hkw : k < w := lt_of_le_of_ne hw.1 (Ne.symm hwk)
    let a := (k + w) / 2
    have hka : k < a := by dsimp only [a]; linarith
    have haw : a < w := by dsimp only [a]; linarith
    have had : a ≤ d := haw.le.trans hw.2
    obtain ⟨qa, hma, _⟩ := hminimum a ⟨hka, had⟩
    obtain ⟨qd, hmd, _⟩ := hminimum d ⟨hkw.trans_le hw.2, le_rfl⟩
    have haD : T - a ^ 2 ∈ Ico (H.time i.castSucc) (H.stageEndTime i.castSucc) := by
      simpa only [stageDomain, Fin.lastCases_castSucc, H.stageEndTime_castSucc]
        using hma.2.2.2.1
    have hdD : T - d ^ 2 ∈ Ico (H.time i.castSucc) (H.stageEndTime i.castSucc) := by
      simpa only [stageDomain, Fin.lastCases_castSucc, H.stageEndTime_castSucc]
        using hmd.2.2.2.1
    have hmin (v : ℝ) (hv : v ∈ Icc a d) :
        ∃ q : (H.stage i.castSucc).Carrier,
          m v ∈ H.regularizedC1ActionValues i.castSucc last hle T u v p q ∧
          ∀ (z : (H.stage i.castSucc).Carrier) (A : ℝ),
            A ∈ H.regularizedC1ActionValues i.castSucc last hle T u v p z → m v ≤ A := by
      obtain ⟨q, hmem, hminimal⟩ := hminimum v ⟨hka.trans_le hv.1, hv.2⟩
      refine ⟨q, hmem, ?_⟩
      intro z A hA
      have hAC := H.coe_mem_regularizedActionValues_of_mem_regularizedC1ActionValues
        i.castSucc last hle (hfloor v) p z hA
      exact WithTop.coe_le_coe.mp ((hminimal z).trans
        (H.regularizedCost_le_of_competitor i.castSucc last hle T B u v p z hAC))
    have hc := continuousOn_spatial_action_minimum H i.castSucc last hle
      hma.1 hma.2.1 had hupper haD hdD (hfloor d) p m hmin
    apply (hc w ⟨haw.le, hw.2⟩).mono_of_mem_nhdsWithin
    filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (Ioi_mem_nhds haw)] with r hr har
    exact ⟨har.le, hr.2⟩

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

universe uEventCostLimit

theorem exists_continuous_spatial_regularizedCost_minimum_of_regularCrossing
    (H : ObservedHistory.{uEventCostLimit}) (i : Fin H.eventCount)
    (last : Fin (H.eventCount + 1)) (hl : i.succ ≤ last)
    {T B u : ℝ}
    (hupper : T - u ^ 2 ∈ H.stageDomain last)
    (hscalar : ∀ j : H.StageInterval i.castSucc last,
      ∀ t ∈ H.stageDomain j.val, ∀ z : (H.stage j.val).Carrier,
        -B ≤ metricScalarAt (H.stageMetric j.val t) z)
    (p : (H.stage last).Carrier) (q : (H.stage i.succ).Carrier)
    (hfinite : H.regularizedCost i.succ last hl T B u
      (Real.sqrt (T - H.time i.succ)) p q ≠ ⊤)
    (hminimum : ∀ z : (H.stage i.succ).Carrier,
      H.regularizedCost i.succ last hl T B u (Real.sqrt (T - H.time i.succ)) p q ≤
        H.regularizedCost i.succ last hl T B u (Real.sqrt (T - H.time i.succ)) p z)
    (x : (H.event i).incoming.terminalRegularOpen)
    (hcross : (H.event i).RegularCrossing x.val q) :
    let k := Real.sqrt (T - H.time i.succ);
    ∃ d > k, ∃ C : ℝ, ∃ m : ℝ → ℝ,
      H.regularizedCost i.succ last hl T B u k p q = (m k : WithTop ℝ) ∧
      ContinuousOn m (Icc k d) ∧
      ∀ w ∈ Ioc k d, ∃ y : (H.stage i.castSucc).Carrier,
        m w ∈ H.regularizedC1ActionValues i.castSucc last
          (i.castSucc_le_succ.trans hl) T u w p y ∧
        H.regularizedCost i.castSucc last (i.castSucc_le_succ.trans hl) T B u w p y =
          (m w : WithTop ℝ) ∧
        (∀ z : (H.stage i.castSucc).Carrier,
          (m w : WithTop ℝ) ≤ H.regularizedCost i.castSucc last
            (i.castSucc_le_succ.trans hl) T B u w p z) ∧
        m k - (2 * B / 3) * (w ^ 3 - k ^ 3) ≤ m w ∧
        m w ≤ m k + (2 * C / 3) * (w ^ 3 - k ^ 3) := by
  let k := Real.sqrt (T - H.time i.succ)
  have hfloor (j : H.StageInterval i.succ last)
      (r : ℝ) (hr : r ∈ Ioo (H.regularizedStageStart T u j.val)
        (H.regularizedStageEnd T k j.val)) (z : (H.stage j.val).Carrier) :
      -B ≤ metricScalarAt (H.stageMetric j.val (T - r ^ 2)) z :=
    hscalar ⟨j.val, i.castSucc_le_succ.trans j.property.1, j.property.2⟩ (T - r ^ 2)
      (H.mapsTo_regularizedStage_Ioo T u k j.val hr) z
  have hcostEq (z : (H.stage i.succ).Carrier) :=
    H.regularizedCost_eq_regularizedC1Cost i.succ last hl T B u k hupper hfloor p z
  have hfiniteC1 : H.regularizedC1Cost i.succ last hl T u k p q ≠ ⊤ := by
    rwa [hcostEq q] at hfinite
  have hne : (H.regularizedC1ActionValues i.succ last hl T u k p q).Nonempty := by
    by_contra hempty
    exact hfiniteC1 (H.regularizedC1Cost_eq_top_of_no_competitor i.succ last hl T u k p q
      (Set.not_nonempty_iff_eq_empty.mp hempty))
  obtain ⟨A, hA⟩ := hne
  obtain ⟨gamma, hgamma, hint, hrecent, hpast, hnodes, haction⟩ :=
    H.exists_regularizedC1Cost_minimizer_of_ne_top i.succ last hl T B u k
      hupper hfloor p q hfiniteC1
  let m0 := ∑ j : H.StageInterval i.succ last, H.stageRegularizedAction j.val T (gamma j)
    (H.regularizedStageStart T u j.val) (H.regularizedStageEnd T k j.val)
  have hm0 : m0 ∈ H.regularizedC1ActionValues i.succ last hl T u k p q :=
    ⟨hA.1, hA.2.1, hA.2.2.1, hA.2.2.2.1, gamma, hgamma, hint, hrecent, hpast, hnodes, rfl⟩
  have hcost0 : H.regularizedCost i.succ last hl T B u k p q = (m0 : WithTop ℝ) :=
    (hcostEq q).trans haction.symm
  have hmin0 (z : (H.stage i.succ).Carrier) (value : ℝ)
      (hvalue : value ∈ H.regularizedC1ActionValues i.succ last hl T u k p z) : m0 ≤ value := by
    have hvalueAC := H.coe_mem_regularizedActionValues_of_mem_regularizedC1ActionValues
      i.succ last hl hfloor p z hvalue
    have hh := (hminimum z).trans
      (H.regularizedCost_le_of_competitor i.succ last hl T B u k p z hvalueAC)
    rw [hcost0] at hh
    exact WithTop.coe_le_coe.mp hh
  obtain ⟨d, hkd, C, m, hmk, hlimit, hminima⟩ :=
    exists_spatial_minimum_tendsto_at_regular_event_from_old_side H i last hl hupper hscalar
      p q hm0 hmin0 x hcross
  refine ⟨d, hkd, C, m, ?_, ?_, ?_⟩
  · simpa only [hmk] using hcost0
  · apply continuousOn_spatial_minimum_at_event_of_tendsto H i last hl hupper hscalar p m
    · simpa only [hmk] using hlimit
    · intro w hw
      obtain ⟨y, hmem, _, hminimum, _, _⟩ := hminima w hw
      exact ⟨y, hmem, hminimum⟩
  · intro w hw
    simpa only [hmk] using hminima w hw

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

universe u uSupport uPropagation uEventPropagation uTargetSlice

private theorem stage_lagrangian_continuousOn_regular_clock
    (H : ObservedHistory.{u}) (j : Fin (H.eventCount + 1)) (T : ℝ)
    (γ : ℝ → (H.stage j).Carrier) (hγ : ContMDiff 𝓘(ℝ, ℝ) ThreeModel 1 γ) :
    ContinuousOn (H.stageRegularizedLagrangian j T γ)
      {w : ℝ | T - w ^ 2 ∈ Ioo (H.time j) (H.stageEndTime j)} := by
  cases j using Fin.lastCases with
  | last =>
    by_cases ht : H.time (Fin.last H.eventCount) < H.horizon
    · have hc := lRegularizedLagrangian_continuousOn_carrier
        (H.finalSlab ht).flow (H.finalSlab ht).equation γ hγ
      have hh := hc.comp (s := {w : ℝ | T - w ^ 2 ∈
          Ioo (H.time (Fin.last H.eventCount)) (H.stageEndTime (Fin.last H.eventCount))})
        (continuous_const.prodMk continuous_id).continuousOn (fun w hw =>
          show T - w ^ 2 ∈ Icc (H.time (Fin.last H.eventCount)) H.horizon from
            ⟨hw.1.le, by simpa only [H.stageEndTime_last] using hw.2.le⟩)
      simpa only [Function.comp_def, id_eq, ← H.stageRegularizedLagrangian_last ht] using hh
    · intro w hw
      exact False.elim (ht (hw.1.trans (by simpa only [H.stageEndTime_last] using hw.2)))
  | cast i =>
    have hc := lRegularizedLagrangian_continuousOn_carrier
      (H.event i).incoming.flow (H.event i).incoming.equation γ hγ
    have hh := hc.comp (s := {w : ℝ | T - w ^ 2 ∈
        Ioo (H.time i.castSucc) (H.stageEndTime i.castSucc)})
      (continuous_const.prodMk continuous_id).continuousOn (fun w hw =>
        show T - w ^ 2 ∈ Ico (H.time i.castSucc) (H.time i.succ) from
          ⟨hw.1.le, by simpa only [H.stageEndTime_castSucc] using hw.2⟩)
    simpa only [Function.comp_def, id_eq, ← H.stageRegularizedLagrangian_castSucc] using hh

private theorem eventually_stage_ends_eq_of_past_interior
    (H : ObservedHistory.{u}) {first last : Fin (H.eventCount + 1)} (hle : first ≤ last)
    {T v : ℝ} (hv : 0 < v)
    (hpast : T - v ^ 2 ∈ Ioo (H.time first) (H.stageEndTime first)) :
    ∀ᶠ w in 𝓝 v, 0 < w ∧ T - w ^ 2 ∈ H.stageDomain first ∧
      ∀ j : H.StageInterval first last,
        H.regularizedStageEnd T w j.val =
          if j = ⟨first, le_rfl, hle⟩ then w else H.regularizedStageEnd T v j.val := by
  classical
  have hclock : Continuous (fun w : ℝ => T - w ^ 2) :=
    continuous_const.sub (continuous_id.pow 2)
  filter_upwards [Ioi_mem_nhds hv, hclock.continuousAt.eventually
    (isOpen_Ioo.mem_nhds hpast)] with w hw hwp
  refine ⟨hw, H.mem_stageDomain_of_mem_Ioo hwp, ?_⟩
  intro j
  split_ifs with hj
  · subst j
    exact H.regularizedStageEnd_eq_of_mem_stageDomain hw.le (H.mem_stageDomain_of_mem_Ioo hwp)
  · have hlt : first < j.val := lt_of_le_of_ne j.property.1 (by
      intro he
      exact hj (Subtype.ext he.symm))
    have htj : H.stageEndTime first ≤ H.time j.val := by
      cases first using Fin.lastCases with
      | last => exact False.elim (not_lt_of_ge (Fin.le_last _) hlt)
      | cast i =>
        rw [H.stageEndTime_castSucc]
        apply H.time_strictMono.monotone
        change i.val + 1 ≤ j.val.val
        exact hlt
    simp only [regularizedStageEnd, max_eq_right (hwp.2.le.trans htj),
      max_eq_right (hpast.2.le.trans htj)]

private theorem hasDerivAt_sum_stage_action_past_cutoff
    (H : ObservedHistory.{u}) {first last : Fin (H.eventCount + 1)} (hle : first ≤ last)
    {T v : ℝ} (hv : 0 < v)
    (hpast : T - v ^ 2 ∈ Ioo (H.time first) (H.stageEndTime first))
    (γ : (j : H.StageInterval first last) → ℝ → (H.stage j.val).Carrier)
    (hγ : ContMDiff 𝓘(ℝ, ℝ) ThreeModel 1 (γ ⟨first, le_rfl, hle⟩))
    (hint : ∀ j, IntervalIntegrable (H.stageRegularizedLagrangian j.val T (γ j)) volume
      (H.regularizedStageStart T 0 j.val) (H.regularizedStageEnd T v j.val)) :
    HasDerivAt (fun w : ℝ => ∑ j : H.StageInterval first last,
      H.stageRegularizedAction j.val T (γ j)
        (H.regularizedStageStart T 0 j.val) (H.regularizedStageEnd T w j.val))
      (H.stageRegularizedLagrangian first T (γ ⟨first, le_rfl, hle⟩) v) v := by
  classical
  let jfirst : H.StageInterval first last := ⟨first, le_rfl, hle⟩
  let W : Set ℝ := {w : ℝ | T - w ^ 2 ∈ Ioo (H.time first) (H.stageEndTime first)}
  have hW : IsOpen W := isOpen_Ioo.preimage (continuous_const.sub (continuous_id.pow 2))
  have hcont := stage_lagrangian_continuousOn_regular_clock H first T (γ jfirst) hγ
  have hmeas : StronglyMeasurableAtFilter
      (H.stageRegularizedLagrangian first T (γ jfirst)) (𝓝 v) volume := by
    have hh := hcont.stronglyMeasurableAtFilter_nhdsWithin hW.measurableSet v (μ := volume)
    rwa [nhdsWithin_eq_nhds.mpr (hW.mem_nhds hpast)] at hh
  have hend : H.regularizedStageEnd T v first = v :=
    H.regularizedStageEnd_eq_of_mem_stageDomain hv.le (H.mem_stageDomain_of_mem_Ioo hpast)
  have hintfirst : IntervalIntegrable (H.stageRegularizedLagrangian first T (γ jfirst)) volume
      (H.regularizedStageStart T 0 first) v := by
    simpa only [jfirst, hend] using hint jfirst
  have hfirst := intervalIntegral.integral_hasDerivAt_right hintfirst hmeas
    (hcont.continuousAt (hW.mem_nhds hpast))
  have hends := eventually_stage_ends_eq_of_past_interior H hle hv hpast
  have hderiv (j : H.StageInterval first last) :
      HasDerivAt (fun w : ℝ => H.stageRegularizedAction j.val T (γ j)
        (H.regularizedStageStart T 0 j.val) (H.regularizedStageEnd T w j.val))
        (if j = jfirst then H.stageRegularizedLagrangian first T (γ jfirst) v else 0) v := by
    by_cases hj : j = jfirst
    · subst j
      rw [ite_eq_left rfl]
      apply hfirst.congr_of_eventuallyEq
      filter_upwards [hends] with w hw
      rw [hw.2.2 jfirst, ite_eq_left rfl]
      rfl
    · rw [ite_eq_right hj]
      apply (hasDerivAt_const v (H.stageRegularizedAction j.val T (γ j)
        (H.regularizedStageStart T 0 j.val) (H.regularizedStageEnd T v j.val))).congr_of_eventuallyEq
      filter_upwards [hends] with w hw
      rw [hw.2.2 j, ite_eq_right hj]
  have hh := HasDerivAt.fun_sum (u := Finset.univ) (fun j _ => hderiv j)
  simpa only [Finset.sum_ite_eq', Finset.mem_univ, ite_true] using hh

private theorem hasDerivAt_scalar_support_past_cutoff
    (H : ObservedHistory.{u}) {first last : Fin (H.eventCount + 1)} (hle : first ≤ last)
    {T v : ℝ} (hv : 0 < v)
    (hpast : T - v ^ 2 ∈ Ioo (H.time first) (H.stageEndTime first))
    (γ : (j : H.StageInterval first last) → ℝ → (H.stage j.val).Carrier)
    (hγ : ContMDiff 𝓘(ℝ, ℝ) ThreeModel 1 (γ ⟨first, le_rfl, hle⟩))
    (hint : ∀ j, IntervalIntegrable (H.stageRegularizedLagrangian j.val T (γ j)) volume
      (H.regularizedStageStart T 0 j.val) (H.regularizedStageEnd T v j.val)) :
    HasDerivAt (fun ρ : ℝ => 2 * Real.sqrt ρ *
      (∑ j : H.StageInterval first last, H.stageRegularizedAction j.val T (γ j)
        (H.regularizedStageStart T 0 j.val) (H.regularizedStageEnd T (Real.sqrt ρ) j.val)) - 6 * ρ)
      ((∑ j : H.StageInterval first last, H.stageRegularizedAction j.val T (γ j)
        (H.regularizedStageStart T 0 j.val) (H.regularizedStageEnd T v j.val)) / v +
        H.stageRegularizedLagrangian first T (γ ⟨first, le_rfl, hle⟩) v - 6) (v ^ 2) := by
  have hsqrt := Real.hasDerivAt_sqrt (ne_of_gt (sq_pos_of_pos hv))
  rw [Real.sqrt_sq hv.le] at hsqrt
  have hd := hasDerivAt_sum_stage_action_past_cutoff H hle hv hpast γ hγ hint
  have hcomp := hd.comp_of_eq (v ^ 2) hsqrt (Real.sqrt_sq hv.le).symm
  have hh := ((hsqrt.const_mul 2).mul hcomp).sub ((hasDerivAt_id (v ^ 2)).const_mul 6)
  apply hh.congr_deriv
  simp only [Function.comp_apply, Real.sqrt_sq hv.le]
  field_simp [ne_of_gt hv]

private theorem eventually_sum_stage_action_mem_past_cutoff
    (H : ObservedHistory.{u}) {first last : Fin (H.eventCount + 1)} (hle : first ≤ last)
    {T v : ℝ} (hv : 0 < v)
    (hupper : T ∈ Icc (H.time last) (H.stageEndTime last))
    (hpast : T - v ^ 2 ∈ Ioo (H.time first) (H.stageEndTime first))
    (γ : (j : H.StageInterval first last) → ℝ → (H.stage j.val).Carrier)
    (hγ : ∀ j, ContMDiff 𝓘(ℝ, ℝ) ThreeModel 1 (γ j))
    (hint : ∀ j, IntervalIntegrable (H.stageRegularizedLagrangian j.val T (γ j)) volume
      (H.regularizedStageStart T 0 j.val) (H.regularizedStageEnd T v j.val))
    (hnode : ∀ (i : Fin H.eventCount) (hf : first ≤ i.castSucc) (hl : i.succ ≤ last),
      ∃ z : (H.event i).old,
        z.val.val = γ ⟨i.castSucc, hf, i.castSucc_lt_succ.le.trans hl⟩
          (Real.sqrt (T - H.time i.succ)) ∧
        (H.event i).oldOutput z = γ ⟨i.succ, hf.trans i.castSucc_lt_succ.le, hl⟩
          (Real.sqrt (T - H.time i.succ))) :
    ∀ᶠ w in 𝓝 v,
      (∑ j : H.StageInterval first last, H.stageRegularizedAction j.val T (γ j)
        (H.regularizedStageStart T 0 j.val) (H.regularizedStageEnd T w j.val)) ∈
      H.regularizedC1ActionValues first last hle T 0 w
        (γ ⟨last, hle, le_rfl⟩ 0) (γ ⟨first, le_rfl, hle⟩ w) := by
  classical
  let jfirst : H.StageInterval first last := ⟨first, le_rfl, hle⟩
  let W : Set ℝ := {w : ℝ | T - w ^ 2 ∈ Ioo (H.time first) (H.stageEndTime first)}
  have hW : IsOpen W := isOpen_Ioo.preimage (continuous_const.sub (continuous_id.pow 2))
  have hcont := stage_lagrangian_continuousOn_regular_clock H first T (γ jfirst) (hγ jfirst)
  have hmeas : StronglyMeasurableAtFilter
      (H.stageRegularizedLagrangian first T (γ jfirst)) (𝓝 v) volume := by
    have hh := hcont.stronglyMeasurableAtFilter_nhdsWithin hW.measurableSet v (μ := volume)
    rwa [nhdsWithin_eq_nhds.mpr (hW.mem_nhds hpast)] at hh
  have hnew : ∀ᶠ w in 𝓝 v,
      IntervalIntegrable (H.stageRegularizedLagrangian first T (γ jfirst)) volume v w :=
    (hcont.continuousAt (hW.mem_nhds hpast)).tendsto.eventually_intervalIntegrable
      hmeas (volume.finiteAt_nhds v) tendsto_const_nhds tendsto_id
  have hend : H.regularizedStageEnd T v first = v :=
    H.regularizedStageEnd_eq_of_mem_stageDomain hv.le (H.mem_stageDomain_of_mem_Ioo hpast)
  have hintfirst : IntervalIntegrable (H.stageRegularizedLagrangian first T (γ jfirst)) volume
      (H.regularizedStageStart T 0 first) v := by
    simpa only [jfirst, hend] using hint jfirst
  filter_upwards [eventually_stage_ends_eq_of_past_interior H hle hv hpast, hnew] with w hw hiw
  refine ⟨le_rfl, hw.1.le, by simpa only [zero_pow (by decide : 2 ≠ 0), sub_zero] using hupper,
    hw.2.1, γ, hγ, ?_, rfl, rfl, hnode, rfl⟩
  intro j
  rw [hw.2.2 j]
  by_cases hj : j = jfirst
  · subst j
    rw [ite_eq_left rfl]
    exact hintfirst.trans hiw
  · rw [ite_eq_right hj]
    exact hint j

private theorem regular_spatial_minimum_has_time_support
    (H : ObservedHistory.{uSupport})
    (first last : Fin (H.eventCount + 1)) (hle : first ≤ last)
    {T B v : ℝ} (hv : 0 < v)
    (hupper : T ∈ H.stageDomain last)
    (hpast : T - v ^ 2 ∈ Ioo (H.time first) (H.stageEndTime first))
    (p : (H.stage last).Carrier)
    (gamma : (j : H.StageInterval first last) → ℝ → (H.stage j.val).Carrier)
    (hgamma : ∀ j, ContMDiff 𝓘(ℝ, ℝ) ThreeModel 1 (gamma j))
    (hint : ∀ j, IntervalIntegrable (H.stageRegularizedLagrangian j.val T (gamma j)) volume
      (H.regularizedStageStart T 0 j.val) (H.regularizedStageEnd T v j.val))
    (hrecent : gamma ⟨last, hle, le_rfl⟩ 0 = p)
    (hnodes : ∀ (i : Fin H.eventCount) (hf : first ≤ i.castSucc) (hl : i.succ ≤ last),
      ∃ z : (H.event i).old,
        z.val.val = gamma ⟨i.castSucc, hf, i.castSucc_le_succ.trans hl⟩
          (Real.sqrt (T - H.time i.succ)) ∧
        (H.event i).oldOutput z = gamma ⟨i.succ, hf.trans i.castSucc_le_succ, hl⟩
          (Real.sqrt (T - H.time i.succ)))
    (hscalar : ∀ j : H.StageInterval first last,
      ∀ r ∈ Ioo (H.regularizedStageStart T 0 j.val) (H.regularizedStageEnd T v j.val),
      ∀ x : (H.stage j.val).Carrier, -B ≤ metricScalarAt (H.stageMetric j.val (T - r ^ 2)) x)
    (hminimum : ∀ (q : (H.stage first).Carrier) (L : ℝ),
      L ∈ H.regularizedC1ActionValues first last hle T 0 v p q →
      (∑ j : H.StageInterval first last, H.stageRegularizedAction j.val T (gamma j)
        (H.regularizedStageStart T 0 j.val) (H.regularizedStageEnd T v j.val)) ≤ L)
    (hcross : ∀ (i : Fin H.eventCount) (hf : first ≤ i.castSucc) (hl : i.succ ≤ last),
      0 < Real.sqrt (T - H.time i.succ) →
      (H.event i).RegularCrossing
        (gamma ⟨i.castSucc, hf, i.castSucc_le_succ.trans hl⟩ (Real.sqrt (T - H.time i.succ)))
        (gamma ⟨i.succ, hf.trans i.castSucc_le_succ, hl⟩ (Real.sqrt (T - H.time i.succ))))
    (m : ℝ → ℝ)
    (hm : ∀ᶠ w in 𝓝 v, ∃ y : (H.stage first).Carrier,
      m w ∈ H.regularizedC1ActionValues first last hle T 0 w p y ∧
      ∀ (z : (H.stage first).Carrier) (L : ℝ),
        L ∈ H.regularizedC1ActionValues first last hle T 0 w p z → m w ≤ L) :
    let A := ∑ j : H.StageInterval first last, H.stageRegularizedAction j.val T (gamma j)
      (H.regularizedStageStart T 0 j.val) (H.regularizedStageEnd T v j.val);
    let R := metricScalarAt (H.stageMetric first (T - v ^ 2))
      (gamma ⟨first, le_rfl, hle⟩ v);
    let phi : ℝ → ℝ := fun rho => 2 * Real.sqrt rho *
      (∑ j : H.StageInterval first last, H.stageRegularizedAction j.val T (gamma j)
        (H.regularizedStageStart T 0 j.val) (H.regularizedStageEnd T (Real.sqrt rho) j.val)) - 6 * rho;
    m v = A ∧ phi (v ^ 2) = 2 * v * A - 6 * v ^ 2 ∧
      (∀ᶠ rho in 𝓝 (v ^ 2),
        2 * Real.sqrt rho * m (Real.sqrt rho) - 6 * rho ≤ phi rho) ∧
      HasDerivAt phi (A / v + 2 * v ^ 2 * R - 6) (v ^ 2) ∧
      A / v + 2 * v ^ 2 * R - 6 ≤ 0 := by
  classical
  intro A R phi
  have hupper0 : T - (0 : ℝ) ^ 2 ∈ H.stageDomain last := by simpa using hupper
  have huppercc : T ∈ Icc (H.time last) (H.stageEndTime last) :=
    ⟨H.time_le_of_mem_stageDomain hupper, H.le_stageEndTime_of_mem_stageDomain hupper⟩
  have huppercc0 : T - (0 : ℝ) ^ 2 ∈ Icc (H.time last) (H.stageEndTime last) := by
    simpa using huppercc
  have hAC j := Manifold.absolutelyContinuousOnInterval_of_contMDiffOn (hgamma j).contMDiffOn
    (a := H.regularizedStageStart T 0 j.val) (b := H.regularizedStageEnd T v j.val)
  have hmembers := eventually_sum_stage_action_mem_past_cutoff H hle hv huppercc hpast
    gamma hgamma hint hnodes
  simp only [hrecent] at hmembers
  have hcostLower : ∀ q : (H.stage first).Carrier,
      (A : WithTop ℝ) ≤ H.regularizedCost first last hle T B 0 v p q :=
    (H.regularizedCost_eq_and_le_of_spatial_action_minimum first last hle T B 0 v
      hupper0 hscalar p (gamma ⟨first, le_rfl, hle⟩ v) A hmembers.self_of_nhds hminimum).2
  have hminimumCost (q : (H.stage first).Carrier) :
      (A : WithTop ℝ) ≤ H.regularizedCost first last hle T B 0 v
        (gamma ⟨last, hle, le_rfl⟩ 0) q := by simpa only [hrecent] using hcostLower q
  have hfull := H.regularizedExtendedAction_eq_sum_action first last le_rfl hv.le
    huppercc0 (H.mem_stageDomain_of_mem_Ioo hpast) gamma hint (fun j => by
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
      exact hscalar j r hr (gamma j r))
  have hvel := H.past_velocity_eq_zero_of_spatial_minimum first last hle le_rfl hv
    huppercc0 hpast hscalar gamma hAC (hgamma ⟨first, le_rfl, hle⟩) hint hnodes
    (fun q => hfull.trans_le (hminimumCost q))
  have hindex := H.sum_action_scalar_bound_of_spatial_minimum first last hle hv
    huppercc hpast gamma hAC (hgamma ⟨first, le_rfl, hle⟩) hint hnodes hscalar hminimumCost hcross
  obtain ⟨y, hmy, hmlower⟩ := hm.self_of_nhds
  have hmA : m v = A := le_antisymm (hmlower _ _ hmembers.self_of_nhds) (hminimum y _ hmy)
  have hlag : H.stageRegularizedLagrangian first T (gamma ⟨first, le_rfl, hle⟩) v =
      2 * v ^ 2 * R := by
    simp only [stageRegularizedLagrangian, hvel, map_zero, mul_zero, zero_add, R]
  refine ⟨hmA, ?_, ?_, ?_, ?_⟩
  · simp only [phi, A, Real.sqrt_sq hv.le]
  · have hsqrt : Tendsto Real.sqrt (𝓝 (v ^ 2)) (𝓝 v) := by
      have hs := Real.continuous_sqrt.tendsto (v ^ 2)
      rw [Real.sqrt_sq hv.le] at hs
      exact hs
    filter_upwards [hsqrt.eventually (hm.and hmembers)] with rho hrho
    obtain ⟨y, _hy, hlower⟩ := hrho.1
    exact sub_le_sub_right (mul_le_mul_of_nonneg_left (hlower _ _ hrho.2) (by positivity)) _
  · simpa only [hlag, A, phi] using
      hasDerivAt_scalar_support_past_cutoff H hle hv hpast gamma (hgamma ⟨first, le_rfl, hle⟩) hint
  · have hnum : A + 2 * v ^ 3 * R - 6 * v ≤ 0 := sub_nonpos.mpr hindex
    have heq : A / v + 2 * v ^ 2 * R - 6 = (A + 2 * v ^ 3 * R - 6 * v) / v := by
      field_simp [hv.ne']
    rw [heq]
    exact div_nonpos_of_nonpos_of_nonneg hnum hv.le

private theorem exists_propagating_negative_spatial_minimum_on_stage
    (H : ObservedHistory.{uPropagation})
    (first last : Fin (H.eventCount + 1)) (hle : first ≤ last)
    {T B a b Abar : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hupper : T ∈ H.stageDomain last)
    (hapast : T - a ^ 2 ∈ Ioo (H.time first) (H.stageEndTime first))
    (hbpast : T - b ^ 2 ∈ Ico (H.time first) (H.stageEndTime first))
    (hscalar : ∀ j : H.StageInterval first last,
      ∀ r ∈ Ioo (H.regularizedStageStart T 0 j.val) (H.regularizedStageEnd T b j.val),
      ∀ x : (H.stage j.val).Carrier, -B ≤ metricScalarAt (H.stageMetric j.val (T - r ^ 2)) x)
    (p : (H.stage last).Carrier) (q₀ : (H.stage first).Carrier) (L₀ : ℝ)
    (hseed : L₀ ∈ H.regularizedC1ActionValues first last hle T 0 a p q₀)
    (hnegative : 2 * a * L₀ - 6 * a ^ 2 < 0)
    (hthreshold : 3 * b < Abar)
    (hregular : ∀ w ∈ Icc a b,
      ∀ gamma : (j : H.StageInterval first last) → ℝ → (H.stage j.val).Carrier,
        (∀ j, ContMDiff 𝓘(ℝ, ℝ) ThreeModel 1 (gamma j)) →
        (∀ j, IntervalIntegrable (H.stageRegularizedLagrangian j.val T (gamma j)) volume
          (H.regularizedStageStart T 0 j.val) (H.regularizedStageEnd T w j.val)) →
        gamma ⟨last, hle, le_rfl⟩ 0 = p →
        (∀ (i : Fin H.eventCount) (hf : first ≤ i.castSucc) (hl : i.succ ≤ last),
          ∃ z : (H.event i).old,
            z.val.val = gamma ⟨i.castSucc, hf, i.castSucc_le_succ.trans hl⟩
              (Real.sqrt (T - H.time i.succ)) ∧
            (H.event i).oldOutput z = gamma ⟨i.succ, hf.trans i.castSucc_le_succ, hl⟩
              (Real.sqrt (T - H.time i.succ))) →
        (∑ j : H.StageInterval first last, H.stageRegularizedAction j.val T (gamma j)
          (H.regularizedStageStart T 0 j.val) (H.regularizedStageEnd T w j.val)) < Abar →
        ∀ (i : Fin H.eventCount) (hf : first ≤ i.castSucc) (hl : i.succ ≤ last),
          0 < Real.sqrt (T - H.time i.succ) →
          (H.event i).RegularCrossing
            (gamma ⟨i.castSucc, hf, i.castSucc_le_succ.trans hl⟩ (Real.sqrt (T - H.time i.succ)))
            (gamma ⟨i.succ, hf.trans i.castSucc_le_succ, hl⟩ (Real.sqrt (T - H.time i.succ)))) :
    ∃ m : ℝ → ℝ, ContinuousOn m (Icc a b) ∧
      (∀ w ∈ Icc a b, ∃ q : (H.stage first).Carrier,
        m w ∈ H.regularizedC1ActionValues first last hle T 0 w p q ∧
        H.regularizedCost first last hle T B 0 w p q = (m w : WithTop ℝ) ∧
        ∀ z : (H.stage first).Carrier,
          (m w : WithTop ℝ) ≤ H.regularizedCost first last hle T B 0 w p z) ∧
      (∀ w ∈ Icc a b, 2 * w * m w - 6 * w ^ 2 ≤ 2 * a * m a - 6 * a ^ 2) ∧
      2 * a * m a - 6 * a ^ 2 < 0 := by
  classical
  have hupper0 : T - (0 : ℝ) ^ 2 ∈ H.stageDomain last := by simpa using hupper
  have hfloor (w : ℝ) (hw : w ∈ Icc a b) (j : H.StageInterval first last)
      (r : ℝ) (hr : r ∈ Ioo (H.regularizedStageStart T 0 j.val)
        (H.regularizedStageEnd T w j.val)) (x : (H.stage j.val).Carrier) :
      -B ≤ metricScalarAt (H.stageMetric j.val (T - r ^ 2)) x := by
    have hsq : w ^ 2 ≤ b ^ 2 := (sq_le_sq₀ (ha.le.trans hw.1) (ha.le.trans hab)).mpr hw.2
    have hend : H.regularizedStageEnd T w j.val ≤ H.regularizedStageEnd T b j.val := by
      unfold regularizedStageEnd
      apply Real.sqrt_le_sqrt
      exact sub_le_sub_left (max_le_max_right _ (sub_le_sub_left hsq T)) T
    exact hscalar j r ⟨hr.1, hr.2.trans_le hend⟩ x
  have hcostEq (w : ℝ) (hw : w ∈ Icc a b) (q : (H.stage first).Carrier) :=
    H.regularizedCost_eq_regularizedC1Cost first last hle T B 0 w hupper0 (hfloor w hw) p q
  have hfinite : ∃ q : (H.stage first).Carrier,
      H.regularizedCost first last hle T B 0 a p q ≠ ⊤ := by
    refine ⟨q₀, ne_top_of_le_ne_top (WithTop.coe_ne_top (a := L₀)) ?_⟩
    rw [hcostEq a ⟨le_rfl, hab⟩ q₀]
    exact H.regularizedC1Cost_le_of_competitor first last hle T 0 a B
      (hfloor a ⟨le_rfl, hab⟩) p q₀ hseed
  obtain ⟨m, hcont, hvalues⟩ := H.exists_continuous_spatial_regularizedCost_minimum
    first last hle le_rfl ha.le hab hupper0 ⟨hapast.1.le, hapast.2⟩ hbpast hscalar p hfinite
  have hminimum (w : ℝ) (hw : w ∈ Icc a b) (q : (H.stage first).Carrier) (L : ℝ)
      (hL : L ∈ H.regularizedC1ActionValues first last hle T 0 w p q) : m w ≤ L := by
    obtain ⟨_, _, _, hmin⟩ := hvalues w hw
    have hc := H.regularizedC1Cost_le_of_competitor first last hle T 0 w B (hfloor w hw) p q hL
    exact WithTop.coe_le_coe.mp ((hmin q).trans ((hcostEq w hw q).trans_le hc))
  let g : ℝ → ℝ := fun w => 2 * w * m w - 6 * w ^ 2
  have hgcont : ContinuousOn g (Icc a b) :=
    ((continuousOn_const.mul continuousOn_id).mul hcont).sub
      (continuousOn_const.mul (continuousOn_id.pow 2))
  have hgnegative : g a < 0 := by
    have hma := hminimum a ⟨le_rfl, hab⟩ q₀ L₀ hseed
    exact (sub_le_sub_right (mul_le_mul_of_nonneg_left hma (by positivity)) _).trans_lt hnegative
  have hsupport : ∀ w ∈ Ioo a b, g w < 0 →
      ∃ theta : ℝ → ℝ, ∃ d : ℝ,
        theta w = g w ∧ g ≤ᶠ[𝓝[>] w] theta ∧ HasDerivAt theta d w ∧ d ≤ 0 := by
    intro w hw hg
    have hw0 : 0 < w := ha.trans hw.1
    have hwcc : w ∈ Icc a b := ⟨hw.1.le, hw.2.le⟩
    have hpast : T - w ^ 2 ∈ Ioo (H.time first) (H.stageEndTime first) := by
      have hsqwb := (sq_lt_sq₀ hw0.le (ha.le.trans hab)).mpr hw.2
      have hsqaw := (sq_le_sq₀ ha.le hw0.le).mpr hw.1.le
      exact ⟨by linarith [hbpast.1], by linarith [hapast.2]⟩
    obtain ⟨q, hmem, _, _⟩ := hvalues w hwcc
    rcases hmem with ⟨_, _, _, _, gamma, hgamma, hint, hrecent, _hpastEq, hnodes, hsum⟩
    have hsmall : m w < Abar := by
      have hmw : m w < 3 * w := by dsimp only [g] at hg; nlinarith
      exact hmw.trans ((mul_le_mul_of_nonneg_left hw.2.le (by norm_num)).trans_lt hthreshold)
    have hcross := hregular w hwcc gamma hgamma hint hrecent hnodes (hsum.trans_lt hsmall)
    have hmnear : ∀ᶠ r in 𝓝 w, ∃ z : (H.stage first).Carrier,
        m r ∈ H.regularizedC1ActionValues first last hle T 0 r p z ∧
        ∀ (y : (H.stage first).Carrier) (A : ℝ),
          A ∈ H.regularizedC1ActionValues first last hle T 0 r p y → m r ≤ A := by
      filter_upwards [isOpen_Ioo.mem_nhds hw] with r hr
      obtain ⟨z, hmr, _, _⟩ := hvalues r ⟨hr.1.le, hr.2.le⟩
      exact ⟨z, hmr, hminimum r ⟨hr.1.le, hr.2.le⟩⟩
    obtain ⟨_, _htouch, hupperPhi, hderivPhi, hdPhi⟩ := H.regular_spatial_minimum_has_time_support
      first last hle hw0 hupper hpast p gamma hgamma hint hrecent hnodes (hfloor w hwcc)
      (fun z A hA => hsum.trans_le (hminimum w hwcc z A hA)) hcross m hmnear
    let A := ∑ j : H.StageInterval first last, H.stageRegularizedAction j.val T (gamma j)
      (H.regularizedStageStart T 0 j.val) (H.regularizedStageEnd T w j.val)
    let R := metricScalarAt (H.stageMetric first (T - w ^ 2))
      (gamma ⟨first, le_rfl, hle⟩ w)
    let phi : ℝ → ℝ := fun rho => 2 * Real.sqrt rho *
      (∑ j : H.StageInterval first last, H.stageRegularizedAction j.val T (gamma j)
        (H.regularizedStageStart T 0 j.val) (H.regularizedStageEnd T (Real.sqrt rho) j.val)) - 6 * rho
    let e := A / w + 2 * w ^ 2 * R - 6
    let theta : ℝ → ℝ := fun r => phi (r ^ 2)
    have hderiv : HasDerivAt phi e (w ^ 2) := hderivPhi
    have hupper' : ∀ᶠ rho in 𝓝 (w ^ 2),
        2 * Real.sqrt rho * m (Real.sqrt rho) - 6 * rho ≤ phi rho := hupperPhi
    have he : e ≤ 0 := hdPhi
    refine ⟨theta, e * (2 * w), ?_, ?_, ?_, mul_nonpos_of_nonpos_of_nonneg he (by positivity)⟩
    · simp only [theta, phi, Real.sqrt_sq hw0.le, hsum, g]
    · have hsquare : Tendsto (fun r : ℝ => r ^ 2) (𝓝 w) (𝓝 (w ^ 2)) :=
        (continuous_id.pow 2).continuousAt.tendsto
      filter_upwards [(hsquare.eventually hupper').filter_mono nhdsWithin_le_nhds,
        self_mem_nhdsWithin] with r hr hwr
      simpa only [Real.sqrt_sq (hw0.le.trans hwr.le), g, theta] using hr
    · have hsquareDeriv : HasDerivAt (fun r : ℝ => r ^ 2) (2 * w) w := by
        simpa only [Nat.reduceSub, pow_one, Nat.cast_ofNat]
          using hasDerivAt_pow 2 w
      exact hderiv.comp_of_eq w hsquareDeriv rfl
  refine ⟨m, hcont, hvalues, ?_, hgnegative⟩
  exact DifferentialGeometry.image_le_initial_of_deriv_upper_support_nonpos_below
    (C := 0) hgcont hgnegative hsupport

private theorem exists_propagating_negative_spatial_minimum_across_event
    (H : ObservedHistory.{uEventPropagation}) (i : Fin H.eventCount)
    (last : Fin (H.eventCount + 1)) (hl : i.succ ≤ last)
    {T B L Vmax Abar : ℝ}
    (hupper : T ∈ H.stageDomain last)
    (hscalar : ∀ j : H.StageInterval i.castSucc last,
      ∀ t ∈ H.stageDomain j.val, ∀ z : (H.stage j.val).Carrier,
        -B ≤ metricScalarAt (H.stageMetric j.val t) z)
    (p : (H.stage last).Carrier) (q : (H.stage i.succ).Carrier)
    (hbirth : H.regularizedCost i.succ last hl T B 0
      (Real.sqrt (T - H.time i.succ)) p q = (L : WithTop ℝ))
    (hbirthMin : ∀ z : (H.stage i.succ).Carrier,
      (L : WithTop ℝ) ≤ H.regularizedCost i.succ last hl T B 0
        (Real.sqrt (T - H.time i.succ)) p z)
    (x : (H.event i).incoming.terminalRegularOpen)
    (hcrossBirth : (H.event i).RegularCrossing x.val q)
    (hV : Real.sqrt (T - H.time i.succ) < Vmax)
    (hnegative : 2 * Real.sqrt (T - H.time i.succ) * L -
      6 * (Real.sqrt (T - H.time i.succ)) ^ 2 < 0)
    (hthreshold : 3 * Vmax < Abar)
    (hregular : ∀ w ∈ Ioc (Real.sqrt (T - H.time i.succ)) Vmax,
      T - w ^ 2 ∈ H.stageDomain i.castSucc →
      ∀ gamma : (j : H.StageInterval i.castSucc last) → ℝ → (H.stage j.val).Carrier,
        (∀ j, ContMDiff 𝓘(ℝ, ℝ) ThreeModel 1 (gamma j)) →
        (∀ j, IntervalIntegrable (H.stageRegularizedLagrangian j.val T (gamma j)) volume
          (H.regularizedStageStart T 0 j.val) (H.regularizedStageEnd T w j.val)) →
        gamma ⟨last, i.castSucc_le_succ.trans hl, le_rfl⟩ 0 = p →
        (∀ (e : Fin H.eventCount) (hf : i.castSucc ≤ e.castSucc) (he : e.succ ≤ last),
          ∃ z : (H.event e).old,
            z.val.val = gamma ⟨e.castSucc, hf, e.castSucc_le_succ.trans he⟩
              (Real.sqrt (T - H.time e.succ)) ∧
            (H.event e).oldOutput z = gamma ⟨e.succ, hf.trans e.castSucc_le_succ, he⟩
              (Real.sqrt (T - H.time e.succ))) →
        (∑ j : H.StageInterval i.castSucc last, H.stageRegularizedAction j.val T (gamma j)
          (H.regularizedStageStart T 0 j.val) (H.regularizedStageEnd T w j.val)) < Abar →
        ∀ (e : Fin H.eventCount) (hf : i.castSucc ≤ e.castSucc) (he : e.succ ≤ last),
          0 < Real.sqrt (T - H.time e.succ) →
          (H.event e).RegularCrossing
            (gamma ⟨e.castSucc, hf, e.castSucc_le_succ.trans he⟩ (Real.sqrt (T - H.time e.succ)))
            (gamma ⟨e.succ, hf.trans e.castSucc_le_succ, he⟩ (Real.sqrt (T - H.time e.succ)))) :
    let k := Real.sqrt (T - H.time i.succ);
    ∃ d ∈ Ioo k Vmax, ∃ m : ℝ → ℝ,
      H.regularizedCost i.succ last hl T B 0 k p q = (m k : WithTop ℝ) ∧
      m k = L ∧ ContinuousOn m (Icc k d) ∧
      (∀ w ∈ Ioc k d, ∃ y : (H.stage i.castSucc).Carrier,
        m w ∈ H.regularizedC1ActionValues i.castSucc last
          (i.castSucc_le_succ.trans hl) T 0 w p y ∧
        H.regularizedCost i.castSucc last (i.castSucc_le_succ.trans hl) T B 0 w p y =
          (m w : WithTop ℝ) ∧
        ∀ z : (H.stage i.castSucc).Carrier,
          (m w : WithTop ℝ) ≤ H.regularizedCost i.castSucc last
            (i.castSucc_le_succ.trans hl) T B 0 w p z) ∧
      ∀ w ∈ Icc k d, 2 * w * m w - 6 * w ^ 2 ≤ 2 * k * L - 6 * k ^ 2 := by
  classical
  intro k
  have hk : 0 < k := by
    by_contra h
    have hk0 : k = 0 := le_antisymm (not_lt.mp h) (Real.sqrt_nonneg _)
    have hneg : 2 * k * L - 6 * k ^ 2 < 0 := hnegative
    norm_num [hk0] at hneg
  have hupper0 : T - (0 : ℝ) ^ 2 ∈ H.stageDomain last := by simpa using hupper
  have hfinite : H.regularizedCost i.succ last hl T B 0 k p q ≠ ⊤ := by
    rw [hbirth]
    exact WithTop.coe_ne_top
  obtain ⟨d₀, hkd₀, _C, m, hmBirth, hcont₀, hvalues₀⟩ :=
    H.exists_continuous_spatial_regularizedCost_minimum_of_regularCrossing i last hl
      hupper0 hscalar p q hfinite (fun z => hbirth.trans_le (hbirthMin z)) x hcrossBirth
  let d := min d₀ ((k + Vmax) / 2)
  have hkd : k < d := lt_min hkd₀ (by dsimp only [k]; linarith)
  have hdV : d < Vmax := (min_le_right _ _).trans_lt (by linarith)
  have hdd₀ : d ≤ d₀ := min_le_left _ _
  have hmL : m k = L := WithTop.coe_injective (hmBirth.symm.trans hbirth)
  have hcont := hcont₀.mono (Icc_subset_Icc le_rfl hdd₀)
  have hvalues (w : ℝ) (hw : w ∈ Ioc k d) : ∃ y : (H.stage i.castSucc).Carrier,
      m w ∈ H.regularizedC1ActionValues i.castSucc last (i.castSucc_le_succ.trans hl) T 0 w p y ∧
      H.regularizedCost i.castSucc last (i.castSucc_le_succ.trans hl) T B 0 w p y =
        (m w : WithTop ℝ) ∧
      ∀ z : (H.stage i.castSucc).Carrier, (m w : WithTop ℝ) ≤
        H.regularizedCost i.castSucc last (i.castSucc_le_succ.trans hl) T B 0 w p z := by
    obtain ⟨y, hmem, hcost, hmin, _, _⟩ := hvalues₀ w ⟨hw.1, hw.2.trans hdd₀⟩
    exact ⟨y, hmem, hcost, hmin⟩
  have hfloor (w : ℝ) (j : H.StageInterval i.castSucc last) (r : ℝ)
      (hr : r ∈ Ioo (H.regularizedStageStart T 0 j.val) (H.regularizedStageEnd T w j.val))
      (z : (H.stage j.val).Carrier) : -B ≤ metricScalarAt (H.stageMetric j.val (T - r ^ 2)) z :=
    hscalar j _ (H.mapsTo_regularizedStage_Ioo T 0 w j.val hr) z
  have hminimum (w : ℝ) (hw : w ∈ Ioc k d) (z : (H.stage i.castSucc).Carrier) (A : ℝ)
      (hA : A ∈ H.regularizedC1ActionValues i.castSucc last
        (i.castSucc_le_succ.trans hl) T 0 w p z) : m w ≤ A := by
    obtain ⟨_, _, _, hmin⟩ := hvalues w hw
    have hAC := H.coe_mem_regularizedActionValues_of_mem_regularizedC1ActionValues
      i.castSucc last (i.castSucc_le_succ.trans hl) (hfloor w) p z hA
    exact WithTop.coe_le_coe.mp ((hmin z).trans
      (H.regularizedCost_le_of_competitor i.castSucc last (i.castSucc_le_succ.trans hl)
        T B 0 w p z hAC))
  obtain ⟨_yd, hmd, _, _⟩ := hvalues d ⟨hkd, le_rfl⟩
  have hdPhysical : T - d ^ 2 ∈ Ico (H.time i.castSucc) (H.stageEndTime i.castSucc) := by
    simpa only [stageDomain, Fin.lastCases_castSucc, H.stageEndTime_castSucc] using hmd.2.2.2.1
  let g : ℝ → ℝ := fun w => 2 * w * m w - 6 * w ^ 2
  have hgcont : ContinuousOn g (Icc k d) :=
    ((continuousOn_const.mul continuousOn_id).mul hcont).sub
      (continuousOn_const.mul (continuousOn_id.pow 2))
  have hgnegative : g k < 0 := by simpa only [g, hmL, k] using hnegative
  have hsupport : ∀ w ∈ Ioo k d, g w < 0 →
      ∃ theta : ℝ → ℝ, ∃ e : ℝ,
        theta w = g w ∧ g ≤ᶠ[𝓝[>] w] theta ∧ HasDerivAt theta e w ∧ e ≤ 0 := by
    intro w hw hg
    have hw0 : 0 < w := hk.trans hw.1
    have hwoc : w ∈ Ioc k d := ⟨hw.1, hw.2.le⟩
    obtain ⟨y, hmem, _, _⟩ := hvalues w hwoc
    have hwDomain := hmem.2.2.2.1
    have hwPhysical : T - w ^ 2 ∈ Ico (H.time i.castSucc) (H.stageEndTime i.castSucc) := by
      simpa only [stageDomain, Fin.lastCases_castSucc, H.stageEndTime_castSucc] using hmem.2.2.2.1
    have hpast : T - w ^ 2 ∈ Ioo (H.time i.castSucc) (H.stageEndTime i.castSucc) := by
      have hsq := (sq_lt_sq₀ hw0.le ((hk.trans hkd).le)).mpr hw.2
      exact ⟨by linarith [hdPhysical.1], hwPhysical.2⟩
    rcases hmem with ⟨_, _, _, _, gamma, hgamma, hint, hrecent, _hpastEq, hnodes, hsum⟩
    have hsmall : m w < Abar := by
      have hm : m w < 3 * w := by dsimp only [g] at hg; nlinarith
      exact hm.trans ((mul_le_mul_of_nonneg_left (hw.2.trans hdV).le (by norm_num)).trans_lt hthreshold)
    have hcross := hregular w ⟨hw.1, (hw.2.trans hdV).le⟩ hwDomain gamma hgamma hint hrecent hnodes
      (hsum.trans_lt hsmall)
    have hmnear : ∀ᶠ r in 𝓝 w, ∃ z : (H.stage i.castSucc).Carrier,
        m r ∈ H.regularizedC1ActionValues i.castSucc last (i.castSucc_le_succ.trans hl) T 0 r p z ∧
        ∀ (y : (H.stage i.castSucc).Carrier) (A : ℝ),
          A ∈ H.regularizedC1ActionValues i.castSucc last (i.castSucc_le_succ.trans hl)
            T 0 r p y → m r ≤ A := by
      filter_upwards [isOpen_Ioo.mem_nhds hw] with r hr
      obtain ⟨z, hmr, _, _⟩ := hvalues r ⟨hr.1, hr.2.le⟩
      exact ⟨z, hmr, hminimum r ⟨hr.1, hr.2.le⟩⟩
    obtain ⟨_, _htouch, hupperPhi, hderivPhi, hdPhi⟩ := H.regular_spatial_minimum_has_time_support
      i.castSucc last (i.castSucc_le_succ.trans hl) hw0 hupper hpast p gamma hgamma hint hrecent
      hnodes (hfloor w) (fun z A hA => hsum.trans_le (hminimum w hwoc z A hA)) hcross m hmnear
    let A := ∑ j : H.StageInterval i.castSucc last, H.stageRegularizedAction j.val T (gamma j)
      (H.regularizedStageStart T 0 j.val) (H.regularizedStageEnd T w j.val)
    let R := metricScalarAt (H.stageMetric i.castSucc (T - w ^ 2))
      (gamma ⟨i.castSucc, le_rfl, i.castSucc_le_succ.trans hl⟩ w)
    let phi : ℝ → ℝ := fun rho => 2 * Real.sqrt rho *
      (∑ j : H.StageInterval i.castSucc last, H.stageRegularizedAction j.val T (gamma j)
        (H.regularizedStageStart T 0 j.val) (H.regularizedStageEnd T (Real.sqrt rho) j.val)) - 6 * rho
    let e := A / w + 2 * w ^ 2 * R - 6
    let theta : ℝ → ℝ := fun r => phi (r ^ 2)
    have hderiv : HasDerivAt phi e (w ^ 2) := hderivPhi
    have hupper' : ∀ᶠ rho in 𝓝 (w ^ 2),
        2 * Real.sqrt rho * m (Real.sqrt rho) - 6 * rho ≤ phi rho := hupperPhi
    have he : e ≤ 0 := hdPhi
    refine ⟨theta, e * (2 * w), ?_, ?_, ?_, mul_nonpos_of_nonpos_of_nonneg he (by positivity)⟩
    · simp only [theta, phi, Real.sqrt_sq hw0.le, hsum, g]
    · have hsquare : Tendsto (fun r : ℝ => r ^ 2) (𝓝 w) (𝓝 (w ^ 2)) :=
        (continuous_id.pow 2).continuousAt.tendsto
      filter_upwards [(hsquare.eventually hupper').filter_mono nhdsWithin_le_nhds,
        self_mem_nhdsWithin] with r hr hwr
      simpa only [Real.sqrt_sq (hw0.le.trans hwr.le), g, theta] using hr
    · have hsquareDeriv : HasDerivAt (fun r : ℝ => r ^ 2) (2 * w) w := by
        simpa only [Nat.reduceSub, pow_one, Nat.cast_ofNat]
          using hasDerivAt_pow 2 w
      exact hderiv.comp_of_eq w hsquareDeriv rfl
  refine ⟨d, ⟨hkd, hdV⟩, m, hmBirth, hmL, hcont, hvalues, ?_⟩
  intro w hw
  have hh := DifferentialGeometry.image_le_initial_of_deriv_upper_support_nonpos_below
    (C := 0) hgcont hgnegative hsupport w hw
  simpa only [g, hmL] using hh

theorem exists_spatial_regularizedCost_minimum_lt_three_mul
    (H : ObservedHistory.{uTargetSlice}) (target last : Fin (H.eventCount + 1))
    {T B Abar w : ℝ} (hupper : T ∈ H.stageDomain last)
    (hscalar : ∀ j : Fin (H.eventCount + 1), ∀ t ∈ H.stageDomain j,
      ∀ z : (H.stage j).Carrier, -B ≤ metricScalarAt (H.stageMetric j t) z)
    (p : (H.stage last).Carrier) (hthreshold : 3 * w < Abar)
    (hregular : ∀ (first : Fin (H.eventCount + 1)) (hle : first ≤ last)
      (v : ℝ), 0 < v → v ≤ w → T - v ^ 2 ∈ H.stageDomain first →
      ∀ gamma : (j : H.StageInterval first last) → ℝ → (H.stage j.val).Carrier,
        (∀ j, ContMDiff 𝓘(ℝ, ℝ) ThreeModel 1 (gamma j)) →
        (∀ j, IntervalIntegrable (H.stageRegularizedLagrangian j.val T (gamma j)) volume
          (H.regularizedStageStart T 0 j.val) (H.regularizedStageEnd T v j.val)) →
        gamma ⟨last, hle, le_rfl⟩ 0 = p →
        (∀ (i : Fin H.eventCount) (hf : first ≤ i.castSucc) (hl : i.succ ≤ last),
          ∃ z : (H.event i).old,
            z.val.val = gamma ⟨i.castSucc, hf, i.castSucc_le_succ.trans hl⟩
              (Real.sqrt (T - H.time i.succ)) ∧
            (H.event i).oldOutput z = gamma ⟨i.succ, hf.trans i.castSucc_le_succ, hl⟩
              (Real.sqrt (T - H.time i.succ))) →
        (∑ j : H.StageInterval first last, H.stageRegularizedAction j.val T (gamma j)
          (H.regularizedStageStart T 0 j.val) (H.regularizedStageEnd T v j.val)) < Abar →
        ∀ (i : Fin H.eventCount) (hf : first ≤ i.castSucc) (hl : i.succ ≤ last),
          0 < Real.sqrt (T - H.time i.succ) →
          (H.event i).RegularCrossing
            (gamma ⟨i.castSucc, hf, i.castSucc_le_succ.trans hl⟩ (Real.sqrt (T - H.time i.succ)))
            (gamma ⟨i.succ, hf.trans i.castSucc_le_succ, hl⟩ (Real.sqrt (T - H.time i.succ))))
    (hbirthRegular : ∀ (i : Fin H.eventCount) (hl : i.succ ≤ last)
      (q : (H.stage i.succ).Carrier) (A : ℝ),
      0 < Real.sqrt (T - H.time i.succ) →
      Real.sqrt (T - H.time i.succ) < w →
      A ∈ H.regularizedC1ActionValues i.succ last hl T 0
        (Real.sqrt (T - H.time i.succ)) p q → A < Abar →
      ∃ x : (H.event i).incoming.terminalRegularOpen, (H.event i).RegularCrossing x.val q)
    (hwpast : T - w ^ 2 ∈ H.stageDomain target)
    (first : Fin (H.eventCount + 1)) (htarget : target ≤ first) (hle : first ≤ last)
    {a : ℝ} (ha : 0 < a) (haw : a ≤ w)
    (hpast : T - a ^ 2 ∈ Ioo (H.time first) (H.stageEndTime first))
    (q₀ : (H.stage first).Carrier) (L₀ : ℝ)
    (hseed : L₀ ∈ H.regularizedC1ActionValues first last hle T 0 a p q₀)
    (hnegative : 2 * a * L₀ - 6 * a ^ 2 < 0) :
    ∃ (q : (H.stage target).Carrier) (L : ℝ),
      L ∈ H.regularizedC1ActionValues target last (htarget.trans hle) T 0 w p q ∧
      H.regularizedCost target last (htarget.trans hle) T B 0 w p q = (L : WithTop ℝ) ∧
      (∀ z : (H.stage target).Carrier,
        (L : WithTop ℝ) ≤ H.regularizedCost target last (htarget.trans hle) T B 0 w p z) ∧
      L < 3 * w := by
  classical
  have hw : 0 < w := ha.trans_le haw
  have htargetPast : T - w ^ 2 ∈ Ico (H.time target) (H.stageEndTime target) := by
    induction target using Fin.lastCases with
    | last =>
      refine ⟨H.time_le_of_mem_stageDomain hwpast, ?_⟩
      rw [H.stageEndTime_last]
      nlinarith [(H.stageDomain_subset last hupper).2, sq_pos_of_pos hw]
    | cast i =>
      simpa only [stageDomain, Fin.lastCases_castSucc, H.stageEndTime_castSucc] using hwpast
  have hstage : ∀ (j : Fin (H.eventCount + 1)) (hjl : j ≤ last)
      (a b : ℝ), 0 < a → a ≤ b → b ≤ w → T - a ^ 2 ∈ Ioo (H.time j) (H.stageEndTime j) →
      T - b ^ 2 ∈ Ico (H.time j) (H.stageEndTime j) →
      ∀ (q : (H.stage j).Carrier) (L : ℝ),
        L ∈ H.regularizedC1ActionValues j last hjl T 0 a p q → 2 * a * L - 6 * a ^ 2 < 0 →
      ∃ (y : (H.stage j).Carrier) (A : ℝ),
        A ∈ H.regularizedC1ActionValues j last hjl T 0 b p y ∧
        H.regularizedCost j last hjl T B 0 b p y = (A : WithTop ℝ) ∧
        (∀ z : (H.stage j).Carrier,
          (A : WithTop ℝ) ≤ H.regularizedCost j last hjl T B 0 b p z) ∧
        2 * b * A - 6 * b ^ 2 < 0 := by
    intro j hjl a b ha hab hbw hpast hbPast q L hseed hneg
    have hb0 : 0 ≤ b := ha.le.trans hab
    have hfloor (x : H.StageInterval j last) (r : ℝ)
        (hr : r ∈ Ioo (H.regularizedStageStart T 0 x.val) (H.regularizedStageEnd T b x.val))
        (z : (H.stage x.val).Carrier) :=
      hscalar x.val _ (H.mapsTo_regularizedStage_Ioo T 0 b x.val hr) z
    obtain ⟨m, _, hvalues, hbound, hnegInit⟩ := H.exists_propagating_negative_spatial_minimum_on_stage
      j last hjl ha hab hupper hpast hbPast hfloor p q L hseed hneg
      ((mul_le_mul_of_nonneg_left hbw (by norm_num)).trans_lt hthreshold) (by
        intro r hr gamma hgamma hint hrecent hnodes hsmall
        have hr0 : 0 < r := ha.trans_le hr.1
        have hsqab := (sq_le_sq₀ ha.le hr0.le).mpr hr.1
        have hsqrb := (sq_le_sq₀ hr0.le hb0).mpr hr.2
        have hrDomain : T - r ^ 2 ∈ H.stageDomain j := H.mem_stageDomain_of_mem_Ico
          ⟨by linarith [hbPast.1], by linarith [hpast.2]⟩
        exact hregular j hjl r hr0 (hr.2.trans hbw) hrDomain
          gamma hgamma hint hrecent hnodes hsmall)
    obtain ⟨y, hmem, hcost, hmin⟩ := hvalues b ⟨hab, le_rfl⟩
    exact ⟨y, m b, hmem, hcost, hmin, (hbound b ⟨hab, le_rfl⟩).trans_lt hnegInit⟩
  have descent : ∀ (j : Fin (H.eventCount + 1)) (hjl : j ≤ last), target ≤ j →
      ∀ (a : ℝ), 0 < a → a ≤ w → T - a ^ 2 ∈ Ioo (H.time j) (H.stageEndTime j) →
      ∀ (q : (H.stage j).Carrier) (L : ℝ),
        L ∈ H.regularizedC1ActionValues j last hjl T 0 a p q → 2 * a * L - 6 * a ^ 2 < 0 →
      ∃ (y : (H.stage target).Carrier) (A : ℝ),
        A ∈ H.regularizedC1ActionValues target last (htarget.trans hle) T 0 w p y ∧
        H.regularizedCost target last (htarget.trans hle) T B 0 w p y = (A : WithTop ℝ) ∧
        (∀ z : (H.stage target).Carrier,
          (A : WithTop ℝ) ≤ H.regularizedCost target last (htarget.trans hle) T B 0 w p z) ∧
        2 * w * A - 6 * w ^ 2 < 0 := by
    intro j
    induction j using Fin.induction with
    | zero =>
      intro hjl htj a ha haw hpast q L hseed hneg
      have ht : target = 0 := le_antisymm htj (Fin.zero_le _)
      subst target
      exact hstage 0 hjl a w ha haw le_rfl hpast htargetPast q L hseed hneg
    | succ i ih =>
      intro hjl htj a ha haw hpast q L hseed hneg
      by_cases heq : i.succ = target
      · subst target
        exact hstage i.succ hjl a w ha haw le_rfl hpast htargetPast q L hseed hneg
      have htold : target ≤ i.castSucc :=
        Fin.le_castSucc_iff.mpr (lt_of_le_of_ne htj (Ne.symm heq))
      let k := Real.sqrt (T - H.time i.succ)
      have hkSq : k ^ 2 = T - H.time i.succ := Real.sq_sqrt (by linarith [hpast.1, sq_nonneg a])
      have hak : a < k := (sq_lt_sq₀ ha.le (Real.sqrt_nonneg _)).mp (by linarith [hpast.1])
      have hk : 0 < k := ha.trans hak
      have hkClock : T - k ^ 2 = H.time i.succ := by rw [hkSq]; ring
      have hkPast : T - k ^ 2 ∈ Ico (H.time i.succ) (H.stageEndTime i.succ) := by
        rw [hkClock]
        exact ⟨le_rfl, hpast.1.trans hpast.2⟩
      have hwBelow : T - w ^ 2 < H.time i.succ :=
        htargetPast.2.trans_le (by
          simpa only [H.stageEndTime_castSucc] using H.stageEndTime_mono htold)
      have hkw : k < w := (sq_lt_sq₀ hk.le hw.le).mp (by linarith)
      obtain ⟨y, A, hmem, hcost, hmin, hnegBirth⟩ :=
        hstage i.succ hjl a k ha hak.le hkw.le hpast hkPast q L hseed hneg
      have hsmall : A < Abar := by
        have hA : A < 3 * k := by nlinarith
        exact hA.trans ((mul_lt_mul_of_pos_left hkw (by norm_num)).trans hthreshold)
      obtain ⟨x, hcross⟩ := hbirthRegular i hjl y A hk hkw hmem hsmall
      obtain ⟨d, hkd, m, _hbirthCost, _hmA, _hcont, hvalues, hbound⟩ :=
        H.exists_propagating_negative_spatial_minimum_across_event i last hjl (Vmax := w) hupper
          (fun z t ht p => hscalar z.val t ht p) p y hcost hmin x hcross
          hkw hnegBirth hthreshold (by
            intro r hr hrDomain gamma hgamma hint hrecent hnodes hsmall
            exact hregular i.castSucc (i.castSucc_le_succ.trans hjl) r (hk.trans hr.1) hr.2
              hrDomain gamma hgamma hint hrecent hnodes hsmall)
      obtain ⟨c, hkc, hcd⟩ := exists_between hkd.1
      have hcw : c < w := hcd.trans hkd.2
      obtain ⟨z, hmc, _, _⟩ := hvalues c ⟨hkc, hcd.le⟩
      obtain ⟨_zd, hmd, _, _⟩ := hvalues d ⟨hkd.1, le_rfl⟩
      have hc0 : 0 < c := hk.trans hkc
      have hcPhysical : T - c ^ 2 ∈ Ico (H.time i.castSucc) (H.stageEndTime i.castSucc) := by
        simpa only [stageDomain, Fin.lastCases_castSucc, H.stageEndTime_castSucc] using hmc.2.2.2.1
      have hdPhysical : T - d ^ 2 ∈ Ico (H.time i.castSucc) (H.stageEndTime i.castSucc) := by
        simpa only [stageDomain, Fin.lastCases_castSucc, H.stageEndTime_castSucc] using hmd.2.2.2.1
      have hcPast : T - c ^ 2 ∈ Ioo (H.time i.castSucc) (H.stageEndTime i.castSucc) := by
        have hsq := (sq_lt_sq₀ hc0.le ((hk.trans hkd.1).le)).mpr hcd
        exact ⟨by linarith [hdPhysical.1], hcPhysical.2⟩
      have hnegc : 2 * c * m c - 6 * c ^ 2 < 0 :=
        (hbound c ⟨hkc.le, hcd.le⟩).trans_lt hnegBirth
      exact ih (i.castSucc_le_succ.trans hjl) htold c hc0 hcw.le hcPast z (m c) hmc hnegc
  obtain ⟨q, L, hmem, hcost, hmin, hneg⟩ :=
    descent first hle htarget a ha haw hpast q₀ L₀ hseed hnegative
  refine ⟨q, L, hmem, hcost, hmin, ?_⟩
  by_contra h
  have hmul := mul_nonneg hw.le (sub_nonneg.mpr (not_lt.mp h))
  nlinarith only [hneg, hmul]

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory
