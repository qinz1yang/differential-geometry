import DifferentialGeometry.Geometry.Compactness.CheegerGromov.ApproximateIsometry.DistanceControl
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.ApproximateIsometry.MetricApproximationMonotonicity
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.ApproximateIsometry.PairwiseApproximateIsometry

set_option autoImplicit false

noncomputable section

universe u uE uH

namespace DifferentialGeometry
namespace HCGCompactness

open scoped Manifold ContDiff Topology BigOperators ENNReal
open Bundle Manifold

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable [NeZero (Module.finrank Real E)] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]

section MemberBridge

theorem ball_subset_eball_ofReal {α : Type*} [PseudoMetricSpace α]
    (x : α) {r : ℝ} (hr : 0 < r) :
    Metric.ball x r ⊆ Metric.eball x (ENNReal.ofReal r) := by
  intro y hy
  rw [Metric.mem_ball] at hy
  rw [Metric.mem_eball, edist_dist]
  exact (ENNReal.ofReal_lt_ofReal_iff hr).2 hy

theorem closedEBall_ofReal_subset_ball {α : Type*} [PseudoMetricSpace α]
    (x : α) {r R : ℝ} (hr : 0 ≤ r) (hR : r < R) :
    Metric.closedEBall x (ENNReal.ofReal r) ⊆ Metric.ball x R := by
  intro y hy
  rw [Metric.mem_closedEBall] at hy
  rw [edist_dist] at hy
  rw [Metric.mem_ball]
  have hdist_le : dist y x ≤ r := by
    exact (ENNReal.ofReal_le_ofReal_iff hr).1 hy
  exact lt_of_le_of_lt hdist_le hR

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
theorem data_image_metric_ball
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
    data_image_ball (I := I) Φ hgnorm hhnorm hrr₂ hε0 hdata hsub hyE
  exact closedEBall_ofReal_subset_ball ((Φ : M → N) O)
    (mul_nonneg (Real.sqrt_nonneg _) hr.le) hR hyClosed

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
theorem data_image_metric_ball_of_superset
    {M : Type u} [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [IsManifold I ∞ M]
    [hManifoldM : IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    [PseudoMetricSpace M] [RiemannianBundle (fun x : M => TangentSpace I x)]
    [IsRiemannianManifold I M]
    {N : Type u} [TopologicalSpace N] [ChartedSpace H N]
    [hT2N : T2Space N] [IsManifold I ∞ N]
    [hSigmaN : SigmaCompactSpace N]
    [hManifoldN : IsManifold I ((∞ : WithTop ℕ∞) + 1) N]
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
  let _ := hManifoldM
  let _ := hT2N
  let _ := hSigmaN
  let _ := hManifoldN
  exact data_image_metric_ball (I := I) Φ hgnorm hhnorm hr hrr₂ hε0 hR
    (hdata.mono hK le_rfl hdata.eps_lt_one) hsub

omit [NeZero (Module.finrank ℝ E)] [CompleteSpace E] [I.Boundaryless] in
theorem member_isRiemannian (Y : PointedRiemannianManifold.{u, uE, uH} (I := I))
    (P : ProperMetricOn (I := I) Y) :
    letI : TopologicalSpace Y.M := Y.topology
    letI : ChartedSpace H Y.M := Y.charted
    letI : IsManifold I ∞ Y.M := Y.smooth
    letI : Bundle.RiemannianBundle (fun x : Y.M => TangentSpace I x) := Y.riemBundle
    letI : MetricSpace Y.M := P.ms
    IsRiemannianManifold I Y.M := by
  let : TopologicalSpace Y.M := Y.topology
  let : ChartedSpace H Y.M := Y.charted
  let : IsManifold I ∞ Y.M := Y.smooth
  let : Bundle.RiemannianBundle (fun x : Y.M => TangentSpace I x) := Y.riemBundle
  let : MetricSpace Y.M := P.ms
  refine ⟨fun x y => ?_⟩
  have hreal := P.realizes x y
  rw [edist_dist, ← hreal]
  rfl

end MemberBridge

end HCGCompactness
end DifferentialGeometry
