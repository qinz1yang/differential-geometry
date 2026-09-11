import DifferentialGeometry.Geometry.Curvature.Bounds.RicciOperatorNorm
import DifferentialGeometry.Geometry.Metric.LocalChartDistance
import DifferentialGeometry.Topology.Manifold.ChartDifferential
import Mathlib.Analysis.Calculus.FDeriv.Equiv
import DifferentialGeometry.Geometry.Metric.TensorInner.Tensor0S.Coordinates.MetricComparison

set_option autoImplicit false
noncomputable section
open Bundle Manifold Set Filter DifferentialGeometry
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold Topology ContDiff BigOperators InnerProductSpace
namespace DifferentialGeometry.Geometry.Metric

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private def metricBasis (g : SmoothRiemannianMetric I M) (p : M) :
    Module.Basis (Fin (Module.finrank ℝ E)) ℝ (TangentSpace I p) := by
  exact (DifferentialGeometry.Tensor0SBundle.exists_orthonormal_basis g p).choose

private theorem metricBasis_inner (g : SmoothRiemannianMetric I M) (p : M)
    (i j : Fin (Module.finrank ℝ E)) :
    g.inner p (metricBasis g p i) (metricBasis g p j) = if i = j then 1 else 0 :=
  (DifferentialGeometry.Tensor0SBundle.exists_orthonormal_basis g p).choose_spec i j

def metricEuclideanFrame (g : SmoothRiemannianMetric I M) (p : M) :
    EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) ≃L[ℝ] TangentSpace I p :=
  ((WithLp.linearEquiv 2 ℝ (Fin (Module.finrank ℝ E) → ℝ)).trans
    (metricBasis g p).equivFun.symm).toContinuousLinearEquiv

private theorem metricEuclideanFrame_apply (g : SmoothRiemannianMetric I M) (p : M)
    (v : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) :
    metricEuclideanFrame g p v = ∑ i, v i • metricBasis g p i := by
  simp only [metricEuclideanFrame, LinearEquiv.coe_toContinuousLinearEquiv',
    LinearEquiv.trans_apply, Module.Basis.equivFun_symm_apply]
  rfl

theorem metricEuclideanFrame_inner (g : SmoothRiemannianMetric I M) (p : M)
    (v w : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) :
    g.inner p (metricEuclideanFrame g p v) (metricEuclideanFrame g p w) = ⟪v, w⟫_ℝ := by
  rw [metricEuclideanFrame_apply, metricEuclideanFrame_apply]
  simp only [map_sum, map_smul, _root_.sum_apply, _root_.smul_apply,
    smul_eq_mul, metricBasis_inner]
  simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial]

theorem metricEuclideanFrame_sqrt (g : SmoothRiemannianMetric I M) (p : M)
    (v : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) :
    Real.sqrt (g.inner p (metricEuclideanFrame g p v) (metricEuclideanFrame g p v)) = ‖v‖ := by
  rw [metricEuclideanFrame_inner, real_inner_self_eq_norm_sq, Real.sqrt_sq (norm_nonneg v)]

theorem metricEuclideanFrame_symm_norm (g : SmoothRiemannianMetric I M) (p : M)
    (v : TangentSpace I p) :
    ‖(metricEuclideanFrame g p).symm v‖ = Real.sqrt (g.inner p v v) := by
  simpa only [ContinuousLinearEquiv.apply_symm_apply] using
    (metricEuclideanFrame_sqrt g p ((metricEuclideanFrame g p).symm v)).symm

def metricChartEuclideanEquiv (g : SmoothRiemannianMetric I M) (p : M) :
    E ≃L[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) :=
  ((trivializationAt E (TangentSpace I) p).continuousLinearEquivAt ℝ p
    (FiberBundle.mem_baseSet_trivializationAt' p)).symm.trans (metricEuclideanFrame g p).symm

theorem metricChartEuclideanEquiv_norm (g : SmoothRiemannianMetric I M) (p : M) (w : E) :
    ‖metricChartEuclideanEquiv g p w‖ =
      Real.sqrt (g.inner p
        ((trivializationAt E (TangentSpace I) p).symmL ℝ p w)
        ((trivializationAt E (TangentSpace I) p).symmL ℝ p w)) := by
  rw [metricChartEuclideanEquiv, ContinuousLinearEquiv.trans_apply,
    metricEuclideanFrame_symm_norm]
  rw [congrFun ((trivializationAt E (TangentSpace I) p).symm_continuousLinearEquivAt_eq
    (R := ℝ) (FiberBundle.mem_baseSet_trivializationAt' p)) w]

theorem metricChartEuclideanEquiv_symm_apply (g : SmoothRiemannianMetric I M) (p : M)
    (v : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) :
    (metricChartEuclideanEquiv g p).symm v =
      (trivializationAt E (TangentSpace I) p).continuousLinearMapAt ℝ p
        (metricEuclideanFrame g p v) := by
  simp only [metricChartEuclideanEquiv, ContinuousLinearEquiv.symm_trans_apply,
    ContinuousLinearEquiv.symm_symm]
  exact congrFun ((trivializationAt E (TangentSpace I) p).coe_continuousLinearEquivAt_eq
    (R := ℝ) (FiberBundle.mem_baseSet_trivializationAt' p)) _

variable {F H' N : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F] [TopologicalSpace H'] {J : ModelWithCorners ℝ F H'}
  [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J ∞ N]

def euclideanChartExpression (g : SmoothRiemannianMetric I M)
    (h : SmoothRiemannianMetric J N) (f : M → N) (p : M) (q : N) :
    EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) →
      EuclideanSpace ℝ (Fin (Module.finrank ℝ F)) :=
  (metricChartEuclideanEquiv h q) ∘
    (((extChartAt J q) ∘ f ∘ (extChartAt I p).symm) ∘ (metricChartEuclideanEquiv g p).symm)

theorem fderiv_euclideanChartExpression_apply [I.Boundaryless] [J.Boundaryless]
    (g : SmoothRiemannianMetric I M) (h : SmoothRiemannianMetric J N)
    (f : M → N) (p : M) (q : N) (x : M)
    (hx : x ∈ (extChartAt I p).source) (hfx : f x ∈ (extChartAt J q).source)
    (hc : ContinuousAt f x) (v : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) :
    fderiv ℝ (euclideanChartExpression g h f p q)
        (metricChartEuclideanEquiv g p (extChartAt I p x)) v =
      metricChartEuclideanEquiv h q
        ((trivializationAt F (TangentSpace J) q).continuousLinearMapAt ℝ (f x)
          (mfderiv I J f x
            ((trivializationAt E (TangentSpace I) p).symmL ℝ x
              ((trivializationAt E (TangentSpace I) p).continuousLinearMapAt ℝ p
                (metricEuclideanFrame g p v))))) := by
  rw [euclideanChartExpression, ContinuousLinearEquiv.comp_fderiv,
    ContinuousLinearEquiv.comp_right_fderiv, ContinuousLinearEquiv.symm_apply_apply,
    DifferentialGeometry.Topology.Manifold.fderiv_fixed_chart_eq_trivialization_comp_mfderiv
      f p q x hx hfx hc]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    metricChartEuclideanEquiv_symm_apply]

theorem eventually_norm_fderiv_euclideanChartExpression_le
    [I.Boundaryless] [J.Boundaryless]
    (g : SmoothRiemannianMetric I M) (h : SmoothRiemannianMetric J N)
    (f : M → N) (hf : Continuous f) (p : M) {K : ℝ} (hK : 1 < K) :
    ∀ᶠ x in 𝓝 p, x ∈ (extChartAt I p).source ∧
      f x ∈ (extChartAt J (f p)).source ∧
      ((∀ v : TangentSpace I x,
        Real.sqrt (h.inner (f x) (mfderiv I J f x v) (mfderiv I J f x v)) ≤
          Real.sqrt (g.inner x v v)) →
        ‖fderiv ℝ (euclideanChartExpression g h f p (f p))
          (metricChartEuclideanEquiv g p (extChartAt I p x))‖ ≤ K ^ 2) := by
  have hK0 : 0 ≤ K := le_trans zero_le_one hK.le
  have htarget := (hf.continuousAt (x := p))
    (eventually_tangent_transport_le h (f p) hK)
  filter_upwards [eventually_tangent_transport_le g p hK, htarget] with x hgx hhx
  rcases hgx with ⟨hx, _, hgback⟩
  rcases hhx with ⟨hfx, hhforward, _⟩
  have hx' : x ∈ (extChartAt I p).source := by simpa only [extChartAt_source] using hx
  have hfx' : f x ∈ (extChartAt J (f p)).source := by simpa only [extChartAt_source] using hfx
  refine ⟨hx', hfx', fun hdf => ?_⟩
  refine ContinuousLinearMap.opNorm_le_bound _ (sq_nonneg K) fun v => ?_
  rw [fderiv_euclideanChartExpression_apply g h f p (f p) x hx' hfx' hf.continuousAt,
    metricChartEuclideanEquiv_norm]
  let u : TangentSpace I x := (trivializationAt E (TangentSpace I) p).symmL ℝ x
    ((trivializationAt E (TangentSpace I) p).continuousLinearMapAt ℝ p
      (metricEuclideanFrame g p v))
  have h1 := hhforward (mfderiv I J f x u)
  have h2 := mul_le_mul_of_nonneg_left (hdf u) hK0
  have h3 := mul_le_mul_of_nonneg_left (hgback (metricEuclideanFrame g p v)) hK0
  have hlast : K * (K * Real.sqrt (g.inner p
      (metricEuclideanFrame g p v) (metricEuclideanFrame g p v))) = K ^ 2 * ‖v‖ := by
    rw [metricEuclideanFrame_sqrt]
    ring
  exact h1.trans (h2.trans (h3.trans_eq hlast))

end DifferentialGeometry.Geometry.Metric
