import DifferentialGeometry.Geometry.Compactness.CheegerGromov.ApproximateIsometry.MetricApproximation.DistanceControl
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.ApproximateIsometry.MetricApproximation.Monotonicity
import DifferentialGeometry.Topology.MetricBall
import DifferentialGeometry.Geometry.Metric.Comparison.BallImage
import DifferentialGeometry.Topology.Manifold.PartialDiffeomorph.Basic

set_option autoImplicit false

noncomputable section

universe u uE uH

namespace DifferentialGeometry
namespace CheegerGromovCompactness

open scoped Manifold ContDiff Topology BigOperators ENNReal
open Bundle Manifold

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable [NeZero (Module.finrank Real E)] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
theorem MapMetricApproximationOn.image_metric_ball_subset
    {M : Type u} [TopologicalSpace M] [ChartedSpace H M] [T2Space M]
    [IsManifold I ∞ M]
    [PseudoMetricSpace M] [RiemannianBundle (fun x : M => TangentSpace I x)]
    [IsRiemannianManifold I M]
    {N : Type u} [TopologicalSpace N] [ChartedSpace H N]
    [IsManifold I ∞ N]
    [PseudoMetricSpace N] [RiemannianBundle (fun y : N => TangentSpace I y)]
    [IsRiemannianManifold I N]
    (Φ : PartialDiffeomorph I I M N (∞ : WithTop ℕ∞)) {O : M} {r r₂ R ε : ℝ} {p : ℕ}
    {g : SmoothRiemannianMetric I M} {h : SmoothRiemannianMetric I N}
    (hgnorm : ∀ (x : M) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (hhnorm : ∀ (y : N) (w : TangentSpace I y),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (h.inner y w w)))
    (hr : 0 < r) (hrr₂ : r ≤ r₂) (hε0 : 0 ≤ ε)
    (hR : Real.sqrt (1 + ε) * r < R)
    (hdata : MapMetricApproximationOn (I := I)
      (Metric.closedEBall O (ENNReal.ofReal r₂)) ε p (Φ : M → N) g h)
    (hsub : Metric.closedEBall O (ENNReal.ofReal r₂) ⊆ Φ.source) :
    (Φ : M → N) '' Metric.ball O r ⊆ Metric.ball ((Φ : M → N) O) R := by
  intro y hy
  have hyE : y ∈ (Φ : M → N) '' Metric.eball O (ENNReal.ofReal r) :=
    Set.image_mono (ball_subset_eball_ofReal O hr) hy
  have hyClosed :
      y ∈ Metric.closedEBall ((Φ : M → N) O)
        (ENNReal.ofReal (Real.sqrt (1 + ε) * r)) :=
    hdata.image_eball_subset_closedEBall (I := I) Φ hgnorm hhnorm hrr₂ hε0 hsub hyE
  exact closedEBall_ofReal_subset_ball ((Φ : M → N) O)
    (mul_nonneg (Real.sqrt_nonneg _) hr.le) hR hyClosed

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
theorem MapMetricApproximationOn.image_metric_ball_subset_of_closedEBall_subset
    {M : Type u} [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [IsManifold I ∞ M]
    [PseudoMetricSpace M] [RiemannianBundle (fun x : M => TangentSpace I x)]
    [IsRiemannianManifold I M]
    {N : Type u} [TopologicalSpace N] [ChartedSpace H N]
    [IsManifold I ∞ N]
    [PseudoMetricSpace N] [RiemannianBundle (fun y : N => TangentSpace I y)]
    [IsRiemannianManifold I N]
    (Φ : PartialDiffeomorph I I M N (∞ : WithTop ℕ∞)) {O : M} {r r₂ R ε : ℝ} {p : ℕ}
    {K : Set M} {g : SmoothRiemannianMetric I M} {h : SmoothRiemannianMetric I N}
    (hgnorm : ∀ (x : M) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (hhnorm : ∀ (y : N) (w : TangentSpace I y),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (h.inner y w w)))
    (hr : 0 < r) (hrr₂ : r ≤ r₂) (hε0 : 0 ≤ ε)
    (hR : Real.sqrt (1 + ε) * r < R)
    (hK : Metric.closedEBall O (ENNReal.ofReal r₂) ⊆ K)
    (hdata : MapMetricApproximationOn (I := I) K ε p (Φ : M → N) g h)
    (hsub : Metric.closedEBall O (ENNReal.ofReal r₂) ⊆ Φ.source) :
    (Φ : M → N) '' Metric.ball O r ⊆ Metric.ball ((Φ : M → N) O) R := by
  exact (hdata.mono hK le_rfl hdata.eps_lt_one).image_metric_ball_subset
    (I := I) Φ hgnorm hhnorm hr hrr₂ hε0 hR hsub

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
theorem PartialDiffeomorphMetricApproximation.ball_subset_image_closedBall
    {M : Type u} [PseudoMetricSpace M] [ChartedSpace H M] [T2Space M] [IsManifold I ∞ M]
    [RiemannianBundle (fun x : M => TangentSpace I x)] [IsRiemannianManifold I M]
    {N : Type u} [PseudoMetricSpace N] [ChartedSpace H N] [T2Space N] [IsManifold I ∞ N]
    [RiemannianBundle (fun x : N => TangentSpace I x)] [IsRiemannianManifold I N]
    (Φ : PartialDiffeomorph I I M N ∞) {O x : M} {r R A ε : ℝ} {p : ℕ}
    {g : SmoothRiemannianMetric I M} {h : SmoothRiemannianMetric I N}
    (hgnorm : ∀ (z : M) (v : TangentSpace I z),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner z v v)))
    (hhnorm : ∀ (z : N) (v : TangentSpace I z),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (h.inner z v v)))
    (hcompact : IsCompact (Metric.closedBall O R))
    (hx : x ∈ Metric.ball O r) (hmargin : Real.sqrt (1 + ε) * A + r < R)
    (D : PartialDiffeomorphMetricApproximation (I := I) (Metric.closedBall O R) ε p Φ g h) :
    Metric.ball ((Φ : M → N) x) A ⊆ (Φ : M → N) '' Metric.closedBall O R := by
  refine PartialDiffeomorph.ball_subset_image_closedBall_of_enorm_mfderiv_symm_le
    (PartialDiffeomorph.ofLE Φ (by decide)) (C := ⟨Real.sqrt (1 + ε), Real.sqrt_nonneg _⟩)
    hcompact D.source_sub ?_ hx hmargin
  intro z hz w
  change ‖mfderiv I I (Φ.symm : N → M) z w‖ₑ ≤
    ENNReal.ofReal (Real.sqrt (1 + ε)) * ‖w‖ₑ
  have hquad : g.inner ((Φ.symm : N → M) z)
      (mfderiv I I (Φ.symm : N → M) z w) (mfderiv I I (Φ.symm : N → M) z w) ≤
        (1 + ε) * h.inner z w w := by
    rw [← D.reverse.pullback_apply z hz (fun _ => w)]
    exact (tensor_apply_bounds_of_metricTensorErrorNorm_le
      D.reverse.pullback h (D.reverse.c0_small z hz) w).2
  calc
    ‖mfderiv I I (Φ.symm : N → M) z w‖ₑ =
        ENNReal.ofReal (Real.sqrt (g.inner ((Φ.symm : N → M) z)
          (mfderiv I I (Φ.symm : N → M) z w)
          (mfderiv I I (Φ.symm : N → M) z w))) := hgnorm _ _
    _ ≤ ENNReal.ofReal (Real.sqrt ((1 + ε) * h.inner z w w)) :=
      ENNReal.ofReal_le_ofReal (Real.sqrt_le_sqrt hquad)
    _ = ENNReal.ofReal (Real.sqrt (1 + ε)) *
        ENNReal.ofReal (Real.sqrt (h.inner z w w)) := by
      rw [Real.sqrt_mul (by linarith [D.forward.eps_pos] : 0 ≤ 1 + ε),
        ENNReal.ofReal_mul (Real.sqrt_nonneg _)]
    _ = ENNReal.ofReal (Real.sqrt (1 + ε)) * ‖w‖ₑ := by rw [hhnorm z w]

end CheegerGromovCompactness
end DifferentialGeometry
