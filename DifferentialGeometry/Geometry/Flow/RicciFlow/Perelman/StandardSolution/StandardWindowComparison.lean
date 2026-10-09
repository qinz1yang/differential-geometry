import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.StandardMetricReference
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.StaticMetricApproximation
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.ApproximateIsometry.MetricApproximation.OfMetricDerivNorm
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.StaticCap
import DifferentialGeometry.Topology.Manifold.PartialDiffeomorph

set_option autoImplicit false
noncomputable section
open Set Filter Manifold TopologicalSpace DifferentialGeometry
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
  (I3 MetricComparisonOn MetricComparisonOn.ofMapMetricApproximation)
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology (standardCapWindow)
open scoped Manifold ContDiff BigOperators Topology
namespace DifferentialGeometry.PDE.RicciFlow

private local instance (D : ℝ) : SigmaCompactSpace (standardCapWindow D) :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen I3 (standardCapWindow D).isOpen)

private theorem mfderiv_subtypeVal_symm_apply {D : ℝ} (hne : Nonempty (standardCapWindow D))
    {z : EuclideanSpace ℝ (Fin 3)} (hz : z ∈ (standardCapWindow D : Set (EuclideanSpace ℝ (Fin 3))))
    (u : TangentSpace I3 z) :
    mfderiv I3 I3
      (DifferentialGeometry.Topology.PartialDiffeomorph.subtypeVal (I := I3)
        (standardCapWindow D) hne).symm z u = u := by
  let i := DifferentialGeometry.Topology.PartialDiffeomorph.subtypeVal (I := I3)
    (standardCapWindow D) hne
  have hsrc : i.symm.source = (standardCapWindow D : Set (EuclideanSpace ℝ (Fin 3))) :=
    (standardCapWindow D).openPartialHomeomorphSubtypeCoe_target hne
  have hz' : z ∈ i.symm.source := hsrc ▸ hz
  have hloc : (fun q => ((i.symm q : standardCapWindow D) : EuclideanSpace ℝ (Fin 3))) =ᶠ[𝓝 z]
      id :=
    Filter.eventuallyEq_of_mem (i.open_target.mem_nhds hz') fun q hq => i.right_inv' hq
  have hcomp := mfderiv_comp z
    (hasMFDerivAt_subtype_val (I := I3) (standardCapWindow D) (i.symm z)).mdifferentiableAt
    (i.symm.mdifferentiableAt (by decide) hz')
  rw [mfderiv_subtype_val] at hcomp
  have h1 : mfderiv I3 I3 (fun q => ((i.symm q : standardCapWindow D) :
      EuclideanSpace ℝ (Fin 3))) z u = mfderiv I3 I3 i.symm z u :=
    DFunLike.congr_fun hcomp u
  rw [hloc.mfderiv_eq, mfderiv_id] at h1
  exact h1.symm

theorem StandardSolution.exists_window_metricComparisonOn {Θ : ℝ} (hΘ0 : 0 ≤ Θ) (hΘ : Θ < 1)
    (order : ℕ) {η : ℝ} (hη : 0 < η) (hη1 : η < 1) :
    ∃ e : ℝ, 0 < e ∧ ∀ (D : ℝ) (hne : Nonempty (standardCapWindow D)) (Q : StandardSolution)
      (T : ℝ), T ∈ Icc 0 Θ →
      ∀ g : SmoothRiemannianMetric I3 (standardCapWindow D),
        (∀ i ≤ order, ∀ v : standardCapWindow D,
          metricDerivNorm i g ((Q.val.metric T).restrictOpen (standardCapWindow D))
            (StandardCap.metric.restrictOpen (standardCapWindow D)) v < e) →
      ∀ U : Set (EuclideanSpace ℝ (Fin 3)),
        closure U ⊆ (standardCapWindow D : Set (EuclideanSpace ℝ (Fin 3))) →
        Nonempty (MetricComparisonOn (fun _ => Q.val.metric T) (fun _ => g)
          ((DifferentialGeometry.Topology.PartialDiffeomorph.subtypeVal (I := I3)
            (standardCapWindow D) hne).symm : EuclideanSpace ℝ (Fin 3) → standardCapWindow D)
          U {0} order η) := by
  obtain ⟨Dr, hDr, href⟩ := exists_uniform_standard_metric_deriv_norm_reference_bound Θ hΘ0 hΘ order
  have hpos : 0 < (Dr + 1) * ((order : ℝ) + 1) := by positivity
  refine ⟨η / ((Dr + 1) * ((order : ℝ) + 1)), div_pos hη hpos, ?_⟩
  intro D hne Q T hT g hclose U hU
  let W := standardCapWindow D
  let i := DifferentialGeometry.Topology.PartialDiffeomorph.subtypeVal (I := I3) W hne
  have hsrc : i.symm.source = (W : Set (EuclideanSpace ℝ (Fin 3))) :=
    W.openPartialHomeomorphSubtypeCoe_target hne
  have hUW : U ⊆ (W : Set (EuclideanSpace ℝ (Fin 3))) := subset_closure.trans hU
  have hsymm (z : EuclideanSpace ℝ (Fin 3)) (hz : z ∈ (W : Set (EuclideanSpace ℝ (Fin 3)))) :
      i.symm z = ⟨z, hz⟩ :=
    Subtype.ext (i.right_inv' (show z ∈ i.symm.source from hsrc ▸ hz))
  obtain ⟨G, V, hKV, hVW, hGV, -⟩ :=
    exists_smooth_metric_agrees_on_neighborhood_of_is_closed (Q.val.metric T) W g
      isClosed_closure hU
  refine ⟨MetricComparisonOn.ofMapMetricApproximation
    (MapMetricApproximationOn.ofMetricDerivNorm G (Q.val.metric T) g hη hη1 ?_ ?_ ?_) {0}⟩
  · exact i.symm.contMDiffOn.mono (hsrc ▸ hUW)
  · intro x hx v
    have hxV : x ∈ (V : Set (EuclideanSpace ℝ (Fin 3))) := hKV (subset_closure hx)
    rw [Tensor0SBundle.metricTensorField_apply, hGV x hxV, mfderiv_subtypeVal_symm_apply hne
      (hUW hx), mfderiv_subtypeVal_symm_apply hne (hUW hx), hsymm x (hUW hx)]
  · intro a ha x hx
    have hxV : x ∈ (V : Set (EuclideanSpace ℝ (Fin 3))) := hKV (subset_closure hx)
    let xw : W := ⟨x, hUW hx⟩
    have hGe : ∀ᶠ y in 𝓝 xw, ∀ v w : TangentSpace I3 y,
        (G.restrictOpen W).inner y v w = g.inner y v w := by
      filter_upwards [continuous_subtype_val.continuousAt.preimage_mem_nhds
        (V.isOpen.mem_nhds hxV)] with y hy v w
      rw [SmoothRiemannianMetric.restrictOpen_inner]
      exact hGV y.val hy v w
    have hloc : metricDerivNorm a G (Q.val.metric T) (Q.val.metric T) x =
        metricDerivNorm a g ((Q.val.metric T).restrictOpen W) ((Q.val.metric T).restrictOpen W)
          xw := by
      rw [← metricDerivNorm_restrictOpen G (Q.val.metric T) (Q.val.metric T) W a xw,
        metricDerivNorm_eq_of_metric_eventuallyEq a (G.restrictOpen W) g _ _ xw hGe]
    have hsum : ∑ k ∈ Finset.range (order + 1),
        metricDerivNorm k g ((Q.val.metric T).restrictOpen W)
          (StandardCap.metric.restrictOpen W) xw ≤
        ((order : ℝ) + 1) * (η / ((Dr + 1) * ((order : ℝ) + 1))) := by
      calc ∑ k ∈ Finset.range (order + 1),
            metricDerivNorm k g ((Q.val.metric T).restrictOpen W)
              (StandardCap.metric.restrictOpen W) xw
          ≤ ∑ _k ∈ Finset.range (order + 1), η / ((Dr + 1) * ((order : ℝ) + 1)) :=
            Finset.sum_le_sum fun k hk =>
              (hclose k (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)) xw).le
        _ = ((order : ℝ) + 1) * (η / ((Dr + 1) * ((order : ℝ) + 1))) := by
            rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
            push_cast
            ring
    rw [hloc]
    calc metricDerivNorm a g ((Q.val.metric T).restrictOpen W)
          ((Q.val.metric T).restrictOpen W) xw
        ≤ Dr * ∑ k ∈ Finset.range (order + 1),
            metricDerivNorm k g ((Q.val.metric T).restrictOpen W)
              (StandardCap.metric.restrictOpen W) xw :=
          href W Q T hT g ((Q.val.metric T).restrictOpen W) a ha xw
      _ ≤ Dr * (((order : ℝ) + 1) * (η / ((Dr + 1) * ((order : ℝ) + 1)))) :=
          mul_le_mul_of_nonneg_left hsum hDr
      _ = η * (Dr / (Dr + 1)) := by
          field_simp
      _ ≤ η * 1 := by
          apply mul_le_mul_of_nonneg_left _ hη.le
          rw [div_le_one (by linarith)]
          linarith
      _ = η := mul_one η

theorem StandardSolution.exists_window_metricComparisonOn_of_lt {Θ : ℝ} (hΘ0 : 0 ≤ Θ)
    (hΘ : Θ < 1) (order : ℕ) {η : ℝ} (hη : 0 < η) (hη1 : η < 1) :
    ∃ e : ℝ, 0 < e ∧ ∀ (D : ℝ) (hne : Nonempty (standardCapWindow D)) (Q : StandardSolution)
      (T : ℝ), T ∈ Icc 0 Θ →
      ∀ g : SmoothRiemannianMetric I3 (standardCapWindow D),
        (∀ i ≤ order, ∀ v : standardCapWindow D,
          metricDerivNorm i g ((Q.val.metric T).restrictOpen (standardCapWindow D))
            (StandardCap.metric.restrictOpen (standardCapWindow D)) v < e) →
      ∀ D' : ℝ, D' < D →
        Nonempty (MetricComparisonOn (fun _ => Q.val.metric T) (fun _ => g)
          ((DifferentialGeometry.Topology.PartialDiffeomorph.subtypeVal (I := I3)
            (standardCapWindow D) hne).symm : EuclideanSpace ℝ (Fin 3) → standardCapWindow D)
          (standardCapWindow D') {0} order η) := by
  obtain ⟨e, he, h⟩ := StandardSolution.exists_window_metricComparisonOn hΘ0 hΘ order hη hη1
  refine ⟨e, he, fun D hne Q T hT g hg D' hD' => h D hne Q T hT g hg _ ?_⟩
  have hcl : closure (standardCapWindow D' : Set (EuclideanSpace ℝ (Fin 3))) ⊆
      {x | ‖x‖ ≤ D' + 1} :=
    closure_minimal (fun x hx => (show ‖x‖ < D' + 1 from hx).le) (isClosed_le continuous_norm continuous_const)
  intro x hx
  have hx' : ‖x‖ ≤ D' + 1 := hcl hx
  change ‖x‖ < D + 1
  linarith

end DifferentialGeometry.PDE.RicciFlow
