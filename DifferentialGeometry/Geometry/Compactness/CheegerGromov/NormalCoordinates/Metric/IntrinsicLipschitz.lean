import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.LocalConjugateRadius
import DifferentialGeometry.Geometry.Metric.ConvexChartDistance

section

set_option autoImplicit false
noncomputable section

namespace DifferentialGeometry.Geometry.Riemannian.NormalCoordinates

open Bundle Set Manifold
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian.Exponential
open DifferentialGeometry.Geometry.Riemannian.VolumeComparison
open scoped Manifold ContDiff Topology ENNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable [PseudoEMetricSpace M]
  [RiemannianBundle (fun x : M => TangentSpace I x)]
  [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]

theorem intrinsicFrameMetric_sqrt_le_of_local_curvature
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) g)
    (p : M) {r R K : ℝ} (hr : 0 ≤ r) (hrR : r < R) (hK : 0 ≤ K)
    (hRm : ∀ y : M, riemannianEDist I p y < ENNReal.ofReal R →
      Real.sqrt (Tensor0SBundle.normSq0S (I := I) g y 4
        (metricRm04At (I := I) g y)) ≤ K)
    {z : E} (hz : ‖z‖ ≤ r) (v : E) :
    Real.sqrt (intrinsicFrameMetric (I := I) g hEnorm p z v v) ≤
      (1 + gronwallBound 0
        (max (Real.sqrt (Module.finrank ℝ E : ℝ) * K * r ^ 2) 1)
        (Real.sqrt (Module.finrank ℝ E : ℝ) * K * r ^ 2) 1) * ‖v‖ := by
  let u : TangentSpace I p := normalFrame (I := I) g p z
  let w : TangentSpace I p := normalFrame (I := I) g p v
  let A : ℝ := Real.sqrt (Module.finrank ℝ E : ℝ) * K * r ^ 2
  have hA : 0 ≤ A := mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) hK) (sq_nonneg _)
  have hODE := intrinsicJacobi_ode (I := I) g hEnorm p u w hK
    (intrinsicRm04Bound_of_ball (I := I) g hEnorm p hRm (hz.trans_lt hrR))
  have hcoef : Real.sqrt (Fintype.card (Fin (Module.finrank ℝ E)) : ℝ) *
      K * g.inner p u u ≤ A := by
    dsimp only [u, A]
    rw [normalFrame_normSq, Fintype.card_fin]
    exact mul_le_mul_of_nonneg_left ((sq_le_sq₀ (norm_nonneg _) hr).2 hz)
      (mul_nonneg (Real.sqrt_nonneg _) hK)
  have hcoef0 : 0 ≤ Real.sqrt (Fintype.card (Fin (Module.finrank ℝ E)) : ℝ) *
      K * g.inner p u u :=
    mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) hK) (metric_inner_self_nonneg g p u)
  have hcoefSq := (sq_le_sq₀ hcoef0 hA).2 hcoef
  have hODE' : ∀ t ∈ Ico (0 : ℝ) 1,
      g.inner (intrinsicGeodesic (I := I) g hEnorm p u t)
          (CovariantDerivativeAlong.covDerivAlong (I := I) g
            (intrinsicGeodesic (I := I) g hEnorm p u)
            (fun s => CovariantDerivativeAlong.covDerivAlong (I := I) g
              (intrinsicGeodesic (I := I) g hEnorm p u)
              (intrinsicJacobi (I := I) g hEnorm p u w) s) t)
          (CovariantDerivativeAlong.covDerivAlong (I := I) g
            (intrinsicGeodesic (I := I) g hEnorm p u)
            (fun s => CovariantDerivativeAlong.covDerivAlong (I := I) g
              (intrinsicGeodesic (I := I) g hEnorm p u)
              (intrinsicJacobi (I := I) g hEnorm p u w) s) t) ≤
        A ^ 2 * g.inner (intrinsicGeodesic (I := I) g hEnorm p u t)
          (intrinsicJacobi (I := I) g hEnorm p u w t)
          (intrinsicJacobi (I := I) g hEnorm p u w t) := by
    intro t ht
    exact (hODE t ht).trans (mul_le_mul_of_nonneg_right hcoefSq
      (metric_inner_self_nonneg g _ _))
  have hupper := (intrinsicJacobi_bounds (I := I) g hEnorm p u w
    hA zero_lt_one hODE').1 1 (by norm_num)
  have hwNorm : Real.sqrt (g.inner p w w) = ‖v‖ := by
    simpa only [w] using normalFrame_sqrt (I := I) g p v
  simp only [one_mul, hwNorm] at hupper
  have hscale : gronwallBound 0 (max A 1) (A * ‖v‖) 1 =
      ‖v‖ * gronwallBound 0 (max A 1) A 1 := by
    rw [mul_comm A ‖v‖, gronwallBound_zero_mul_eps]
  rw [hscale] at hupper
  have hmetric : intrinsicFrameMetric (I := I) g hEnorm p z v v =
      g.inner (intrinsicGeodesic (I := I) g hEnorm p u 1)
        (intrinsicJacobi (I := I) g hEnorm p u w 1)
        (intrinsicJacobi (I := I) g hEnorm p u w 1) := by
    rw [intrinsic_metric_jacobi (I := I) g hEnorm p z v v]
    dsimp only [u, w, intrinsicFramedExp, expMapIntrinsic]
    rw [intrinsicFrameCLM_apply]
    rfl
  rw [hmetric]
  change _ ≤ (1 + gronwallBound 0 (max A 1) A 1) * ‖v‖
  nlinarith

end DifferentialGeometry.Geometry.Riemannian.NormalCoordinates

end

end

section

set_option autoImplicit false
noncomputable section

namespace DifferentialGeometry.Geometry.Riemannian.NormalCoordinates

open Bundle Set Manifold
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian.Exponential
open DifferentialGeometry.Geometry.Riemannian.VolumeComparison
open scoped Manifold ContDiff Topology ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable [PseudoEMetricSpace M]
  [RiemannianBundle (fun x : M => TangentSpace I x)]
  [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]

theorem lipschitzOnWith_intrinsicFramedExp_of_metric_bound
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) g)
    (p : M) {r : ℝ} {C : ℝ≥0}
    (hmetric : ∀ z ∈ Metric.closedBall (0 : E) r, ∀ v : E,
      Real.sqrt (intrinsicFrameMetric (I := I) g hEnorm p z v v) ≤ C * ‖v‖) :
    LipschitzOnWith C (intrinsicFramedExp (I := I) g hEnorm p)
      (Metric.closedBall (0 : E) r) := by
  intro x hx y hy
  rw [IsRiemannianManifold.out (I := I)]
  have hsmooth : ContMDiffOn 𝓘(ℝ, E) I 1
      (intrinsicFramedExp (I := I) g hEnorm p) Set.univ :=
    ((intrinsicFrame_smooth (I := I) g hEnorm p).of_le (by decide)).contMDiffOn
  apply riemannianEDist_le_mul_edist_of_convex isOpen_univ hsmooth
    (subset_univ _) (convex_closedBall (0 : E) r) _ hx hy
  intro z hz v
  rw [hEnorm]
  have hbound := hmetric z hz v
  have hbound' : Real.sqrt (g.inner (intrinsicFramedExp (I := I) g hEnorm p z)
      (mfderiv (modelWithCornersSelf ℝ E) I (intrinsicFramedExp (I := I) g hEnorm p) z v)
      (mfderiv (modelWithCornersSelf ℝ E) I (intrinsicFramedExp (I := I) g hEnorm p) z v)) ≤ C * ‖v‖ := by
    exact hbound
  simpa only [ENNReal.ofReal_mul (NNReal.coe_nonneg C), ENNReal.ofReal_coe_nnreal,
    ofReal_norm] using ENNReal.ofReal_le_ofReal hbound'

theorem lipschitzOnWith_intrinsicFramedExp_of_local_curvature
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) g)
    (p : M) {r R K : ℝ} (hr : 0 ≤ r) (hrR : r < R) (hK : 0 ≤ K)
    (hRm : ∀ y : M, riemannianEDist I p y < ENNReal.ofReal R →
      Real.sqrt (Tensor0SBundle.normSq0S (I := I) g y 4
        (metricRm04At (I := I) g y)) ≤ K) :
    LipschitzOnWith ⟨max (1 + gronwallBound 0
      (max (Real.sqrt (Module.finrank ℝ E : ℝ) * K * r ^ 2) 1)
      (Real.sqrt (Module.finrank ℝ E : ℝ) * K * r ^ 2) 1) 1,
      le_trans zero_le_one (le_max_right _ _)⟩
      (intrinsicFramedExp (I := I) g hEnorm p) (Metric.closedBall (0 : E) r) := by
  let A : ℝ := Real.sqrt (Module.finrank ℝ E : ℝ) * K * r ^ 2
  let B : ℝ := 1 + gronwallBound 0 (max A 1) A 1
  apply lipschitzOnWith_intrinsicFramedExp_of_metric_bound g hEnorm p
  intro z hz v
  have hz' : ‖z‖ ≤ r := by simpa only [Metric.mem_closedBall, dist_zero_right] using hz
  exact (intrinsicFrameMetric_sqrt_le_of_local_curvature g hEnorm p hr hrR hK hRm hz' v).trans
    (mul_le_mul_of_nonneg_right (le_max_left B 1) (norm_nonneg v))

end DifferentialGeometry.Geometry.Riemannian.NormalCoordinates

end

end
