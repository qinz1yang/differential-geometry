import DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.FiniteTime.CurvatureBlowupRateIntrinsic
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.SlabTensorContinuity

noncomputable section

open Set
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Analysis.Parabolic
open DifferentialGeometry.Tensor0SBundle

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab

universe u

variable {P : OrientedThreeStage.{u}} {a s : ℝ} (G : P.IncomingSlab a s)

private theorem intrinsic_curvature_heat_subsolution :
    IsHeatPotSubsolutionOn (RealTimeInterval.closedOpen a s G.lt) (flowG G.flow)
      (fun t x => rmTowerCost 3 0 * Real.sqrt (nablaKRm04NormSqIntrinsic G.flow 0 t x))
      (nablaKRm04NormSqIntrinsic G.flow 0) := by
  refine
    { jointSmooth := towerNorm_joint G.equation 0
      jointCont := ?_
      sliceSmooth := fun t _ => nablaKNorm_smooth G.flow t 0
      timeDiff := ?_
      equation_le := ?_ }
  · simpa only [nablaKRm04NormSqIntrinsic, nablaKRm04Field_zero, Nat.add_zero,
      SolutionOn.family_metric] using
      P.tensorFamily_normSq_continuousOn G.equation.smoothMetric.metricTensor_cont
        G.equation.rm04Cont
  · intro t ht x
    obtain ⟨t1, hat1, ht1t⟩ := exists_between ht.1
    have h := isHeatPotSubsolutionOn_nablaKRm04NormSqIntrinsic_of_solution
      (I := ThreeModel) G.equation hat1 (ht1t.trans ht.2)
    exact h.timeDiff t ⟨ht1t, ht.2⟩ x
  · intro t ht x
    obtain ⟨t1, hat1, ht1t⟩ := exists_between ht.1
    have h := isHeatPotSubsolutionOn_nablaKRm04NormSqIntrinsic_of_solution
      (I := ThreeModel) G.equation hat1 (ht1t.trans ht.2)
    simpa using h.equation_le t ⟨ht1t, ht.2⟩ x

private theorem intrinsic_curvature_unbounded (h : G.SingularEndpoint) :
    Rm04NormSqUnboundedOn G.flow := by
  intro K
  obtain ⟨t, ht, x, hx⟩ := h (Real.sqrt (max K 0) + 1)
    (by positivity) a ⟨le_rfl, G.lt⟩
  refine ⟨t, x, ⟨ht.1.le, ht.2⟩, ?_⟩
  have hsqrt := Real.sq_sqrt (show 0 ≤ max K 0 from le_max_right _ _)
  have hnorm : G.riemannNorm t x ^ 2 = nablaKRm04NormSqIntrinsic G.flow 0 t x := by
    simpa only [riemannNorm, nablaKRm04NormSqIntrinsic, nablaKRm04Field_zero,
      Nat.add_zero] using Real.sq_sqrt
      (normSq0S_nonneg (G.flow.base.metric t) x 4 (G.flow.base.rm04 t x))
  nlinarith [Real.sqrt_nonneg (max K 0), le_max_left K 0]

theorem one_div_le_endpoint_sub_of_initial_curvature_bound
    (hsing : G.SingularEndpoint) {Q : ℝ} (hQ : 0 < Q)
    (hinit : ∀ x : P.Carrier, G.riemannNorm a x ≤ Q) :
    1 / (2592 * Q) ≤ s - a := by
  have hbound : ∀ x : P.Carrier, nablaKRm04NormSqIntrinsic G.flow 0 a x ≤ Q ^ 2 := by
    intro x
    have hnorm : G.riemannNorm a x ^ 2 = nablaKRm04NormSqIntrinsic G.flow 0 a x := by
      simpa only [riemannNorm, nablaKRm04NormSqIntrinsic, nablaKRm04Field_zero,
        Nat.add_zero] using Real.sq_sqrt
        (normSq0S_nonneg (G.flow.base.metric a) x 4 (G.flow.base.rm04 a x))
    have hn : 0 ≤ G.riemannNorm a x := Real.sqrt_nonneg _
    nlinarith [hinit x]
  have hcost : rmTowerCost 3 0 = 2592 := by
    rw [rmTowerCost_zero]
    norm_num
  have hc : 0 < rmTowerCost 3 0 := by rw [hcost]; norm_num
  have h := curvatureDoublingSpan_le_of_rm04NormSqUnbounded G.flow hc hQ
    (intrinsic_curvature_heat_subsolution G) (intrinsic_curvature_unbounded G hsing)
    ⟨le_rfl, G.lt⟩ hbound
  simpa only [curvatureDoublingSpan, hcost] using h

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab
