import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.LGeometry.Action.AbsoluteContinuity

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

open Set
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff

universe u

variable (H : ObservedHistory.{u})

/-- The actual constant competitor on a zero-duration stage has extended action
zero. The scalar-floor parameter is arbitrary because the integration interval
is empty. -/
theorem zero_mem_regularizedActionValues_self
    (j : Fin (H.eventCount + 1)) (B : ℝ) (p : (H.stage j).Carrier) :
    (0 : WithTop ℝ) ∈ H.regularizedActionValues j j le_rfl (H.time j) B 0 0 p p := by
  have hupper : H.time j - (0 : ℝ) ^ 2 ∈ Icc (H.time j) (H.stageEndTime j) := by
    simpa only [zero_pow two_ne_zero, sub_zero] using
      (show H.time j ∈ Icc (H.time j) (H.stageEndTime j) from
        ⟨le_rfl, H.time_le_stageEndTime j⟩)
  have hpast : H.time j - (0 : ℝ) ^ 2 ∈ H.stageDomain j := by
    simpa only [zero_pow two_ne_zero, sub_zero] using H.time_mem_stageDomain j
  have hconstant : (0 : ℝ) ∈ H.regularizedC1ActionValues j j le_rfl
      (H.time j) 0 0 p p := by
    apply (H.mem_regularizedC1ActionValues_self j p p).2
    refine ⟨le_rfl, le_rfl, hupper, hpast, (fun _ => p), contMDiff_const,
      IntervalIntegrable.refl, rfl, rfl, ?_⟩
    simp only [stageRegularizedAction, intervalIntegral.integral_same]
  have hfloor : ∀ k : H.StageInterval j j,
      ∀ r ∈ Ioo (H.regularizedStageStart (H.time j) 0 k.val)
          (H.regularizedStageEnd (H.time j) 0 k.val),
      ∀ x : (H.stage k.val).Carrier,
        -B ≤ metricScalarAt (H.stageMetric k.val (H.time j - r ^ 2)) x := by
    intro k r hr x
    have hbounds := H.regularizedStage_bounds (first := j) (last := j)
      (T := H.time j) (u := 0) (v := 0) le_rfl le_rfl hupper hpast k
    exact (not_lt_of_ge (hbounds.2.2.trans hbounds.1) (hr.1.trans hr.2)).elim
  exact H.coe_mem_regularizedActionValues_of_mem_regularizedC1ActionValues
    j j le_rfl hfloor p p hconstant

/-- Extend every older extended-action value through the original old/output
node at clock zero. Infinite values are retained; no integrability or finiteness
assumption is imposed on the older competitor. -/
theorem regularizedActionValues_subset_of_zero_pole
    (first : Fin (H.eventCount + 1)) (i : Fin H.eventCount)
    (hf : first ≤ i.castSucc) (B w : ℝ)
    (z : (H.event i).old) (y : (H.stage first).Carrier) :
    H.regularizedActionValues first i.castSucc hf (H.time i.succ) B 0 w z.val.val y ⊆
      H.regularizedActionValues first i.succ (hf.trans i.castSucc_le_succ)
        (H.time i.succ) B 0 w ((H.event i).oldOutput z) y := by
  intro A hA
  have hw : 0 ≤ w := hA.2.1
  have hpast : H.time i.succ - w ^ 2 ∈ H.stageDomain first := hA.2.2.2.1
  have hupper : H.time i.succ - (0 : ℝ) ^ 2 ∈
      Icc (H.time i.succ) (H.stageEndTime i.succ) := by
    simpa only [zero_pow two_ne_zero, sub_zero] using
      (show H.time i.succ ∈ Icc (H.time i.succ) (H.stageEndTime i.succ) from
        ⟨le_rfl, H.time_le_stageEndTime i.succ⟩)
  apply (H.mem_regularizedActionValues_split_at_event (hf.trans i.castSucc_le_succ)
    i hf le_rfl le_rfl hw hupper hpast ((H.event i).oldOutput z) y).2
  refine ⟨z, A, 0, ?_, ?_, add_zero A⟩
  · simpa only [sub_self, Real.sqrt_zero] using hA
  · simpa only [sub_self, Real.sqrt_zero] using
      H.zero_mem_regularizedActionValues_self i.succ B ((H.event i).oldOutput z)

/-- At a surgery-time pole, passing from the actual older node to its actual
output can only lower cost. The infimum argument includes empty action sets and
infinite values and preserves the same history, floor parameter and endpoints. -/
theorem regularizedCost_le_of_zero_pole
    (first : Fin (H.eventCount + 1)) (i : Fin H.eventCount)
    (hf : first ≤ i.castSucc) (B w : ℝ)
    (z : (H.event i).old) (y : (H.stage first).Carrier) :
    H.regularizedCost first i.succ (hf.trans i.castSucc_le_succ)
      (H.time i.succ) B 0 w ((H.event i).oldOutput z) y ≤
    H.regularizedCost first i.castSucc hf
      (H.time i.succ) B 0 w z.val.val y := by
  change _ ≤ sInf (H.regularizedActionValues first i.castSucc hf
    (H.time i.succ) B 0 w z.val.val y)
  apply (WithTop.isGLB_sInf' (H.regularizedActionValues_bddBelow first i.castSucc hf
    (H.time i.succ) B 0 w z.val.val y)).2
  intro A hA
  exact H.regularizedCost_le_of_competitor first i.succ (hf.trans i.castSucc_le_succ)
    (H.time i.succ) B 0 w ((H.event i).oldOutput z) y
    (H.regularizedActionValues_subset_of_zero_pole first i hf B w z y hA)

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory
