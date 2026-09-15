import DifferentialGeometry.Geometry.Exponential.NormalBall.Chart
import DifferentialGeometry.Analysis.Calculus.MapConvergence.DerivativeBounds
import DifferentialGeometry.Analysis.Calculus.MapConvergence.Composition
import DifferentialGeometry.Geometry.Exponential.NormalBall.Recenter

set_option autoImplicit false

noncomputable section

open Set
open scoped ContDiff Manifold

namespace DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.NormalBallChart

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : ℕ → Type u} [∀ k, TopologicalSpace (M k)] [∀ k, ChartedSpace H (M k)]
  [∀ k, IsManifold I ∞ (M k)]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

theorem exists_metricBounds_of_convergence
    (g : ∀ k, SmoothRiemannianMetric I (M k)) {p : ∀ k, M k}
    (c : ∀ k, NormalBallChart (I := I) (p k))
    {r r₀ : ℝ} (hr₀ : 0 < r₀) (hr₀r : r₀ < r)
    (hrr : ∀ k, r ≤ (c k).radius)
    (hell : ∀ k, (c k).MetricEquivOn (g k) (Metric.ball (0 : E) r))
    {B : E → E →L[ℝ] E →L[ℝ] ℝ}
    (hB : ContDiffOn ℝ (⊤ : ℕ∞) B (Metric.ball (0 : E) r))
    (hconv : CheegerGromovCompactness.MapCInfConvergenceOnCompacts (Metric.ball (0 : E) r)
      (fun k => (c k).metric (g k)) B) :
    ∃ (C : ℕ → ℝ) (mb : ∀ k, (c k).MetricBounds (g k)),
      ∀ k, (mb k).radius = r₀ ∧ (mb k).C = C := by
  have hsmooth : ∀ k, ContDiffOn ℝ (⊤ : ℕ∞) ((c k).metric (g k)) (Metric.ball (0 : E) r) :=
    fun k => ((c k).metric_cont_diff_on (g k) Metric.isOpen_ball (c k).smooth_to).mono
      (Metric.ball_subset_ball (hrr k))
  obtain ⟨C, hC, hbound⟩ :=
    CheegerGromovCompactness.MapCInfConvergenceOnCompacts.exists_iteratedFDeriv_bound
      Metric.isOpen_ball hsmooth hB hconv (isCompact_closedBall (0 : E) r₀)
      (Metric.closedBall_subset_ball hr₀r)
  let mb : ∀ k, (c k).MetricBounds (g k) := fun k =>
    { C := C
      C_nonneg := hC
      radius := r₀
      radius_pos := hr₀
      equiv := fun z hz => hell k z (Metric.ball_subset_ball hr₀r.le hz)
      deriv := fun q z hz => hbound q k z (Metric.ball_subset_closedBall hz) }
  exact ⟨C, mb, fun _ => ⟨rfl, rfl⟩⟩

end DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.NormalBallChart

end

set_option autoImplicit false
noncomputable section
open Set Filter
open scoped Manifold ContDiff Topology
namespace DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.NormalBallChart
open DifferentialGeometry.CheegerGromovCompactness
attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace
variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : ℕ → Type*} [∀ k, TopologicalSpace (M k)] [∀ k, ChartedSpace H (M k)] [∀ k, IsManifold I ∞ (M k)]

theorem metric_limit_symmetric_and_bounds
    (g : ∀ k, SmoothRiemannianMetric I (M k)) {p : ∀ k, M k}
    (c : ∀ k, NormalBallChart (I := I) (p k)) {U : Set E}
    (hell : ∀ k, (c k).MetricEquivOn (g k) U)
    {B : E → E →L[ℝ] E →L[ℝ] ℝ}
    (hconv : MapCInfConvergenceOnCompacts U (fun k => (c k).metric (g k)) B) :
    (∀ z ∈ U, ∀ v w : E, B z v w = B z w v) ∧
    ∀ z ∈ U, ∀ v : E, (1 / 2 : ℝ) * ‖v‖ ^ 2 ≤ B z v v ∧ B z v v ≤ 2 * ‖v‖ ^ 2 := by
  have htend : ∀ z ∈ U, ∀ v w : E,
      Tendsto (fun k => (c k).metric (g k) z v w) atTop (𝓝 (B z v w)) := by
    intro z hz v w
    have hc : Continuous (fun A : E →L[ℝ] E →L[ℝ] ℝ => A v w) := by fun_prop
    exact (hc.tendsto _).comp (tendsto_of_cInf hconv hz)
  constructor
  · intro z hz v w
    apply tendsto_nhds_unique (htend z hz v w)
    convert htend z hz w v using 1
    funext k
    simp only [metric_apply]
    exact (g k).symm _ _ _
  · intro z hz v
    exact ⟨ge_of_tendsto (htend z hz v v) (Eventually.of_forall fun k => (hell k z hz v).1),
      le_of_tendsto (htend z hz v v) (Eventually.of_forall fun k => (hell k z hz v).2)⟩
end DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.NormalBallChart

end

set_option autoImplicit false
noncomputable section
open Set
open scoped ContDiff Manifold Topology
namespace DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.NormalBallChart
open DifferentialGeometry.CheegerGromovCompactness

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : ℕ → Type*} [∀ k, TopologicalSpace (M k)] [∀ k, ChartedSpace H (M k)]
  [∀ k, IsManifold I ∞ (M k)]
attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace

theorem metric_recenter_convergence
    (g : ∀ k, SmoothRiemannianMetric I (M k)) {p : ∀ k, M k}
    (c : ∀ k, NormalBallChart (I := I) (p k)) (a : E) {r R : ℝ}
    (hr : 0 < r) (hball : ∀ k, Metric.ball a r ⊆ Metric.ball (0 : E) (c k).radius)
    (hchart : ∀ k, R ≤ (c k).radius)
    (htranslate : Metric.ball a r ⊆ Metric.ball (0 : E) R)
    {B : E → E →L[ℝ] E →L[ℝ] ℝ}
    (hB : ContDiffOn ℝ ∞ B (Metric.ball (0 : E) R))
    (hconv : MapCInfConvergenceOnCompacts (Metric.ball (0 : E) R)
      (fun k => (c k).metric (g k)) B) :
    MapCInfConvergenceOnCompacts (Metric.ball (0 : E) r)
      (fun k => ((c k).recenter a hr (hball k)).metric (g k)) (fun z => B (a + z)) := by
  have hsmooth : ∀ k, ContDiffOn ℝ ∞ ((c k).metric (g k)) (Metric.ball (0 : E) R) := by
    intro k
    exact ((c k).metric_cont_diff_on (g k) Metric.isOpen_ball (c k).smooth_to).mono
      (Metric.ball_subset_ball (hchart k))
  have hmap : MapsTo (fun z : E => a + z) (Metric.ball (0 : E) r) (Metric.ball (0 : E) R) := by
    intro z hz
    apply htranslate
    simpa only [Metric.mem_ball, dist_zero_right, dist_add_left, dist_self_add_left] using hz
  have htransC : ContDiff ℝ ∞ (fun z : E => a + z) := contDiff_const.add contDiff_id
  have hcomp := (mapCInfConvergence_const (fun z : E => a + z)).comp_of_finiteDimensional
    Metric.isOpen_ball Metric.isOpen_ball hconv
    (fun _ => htransC.contDiffOn) htransC.contDiffOn hsmooth hB hmap (fun _ => hmap)
  exact hcomp.congr Metric.isOpen_ball
    (fun k z hz => metric_recenter (g k) (c k) a hr (hball k) hz)
    (fun _ _ => rfl)

omit [FiniteDimensional ℝ E] in
theorem metricEquivOn_recenter
    (g : ∀ k, SmoothRiemannianMetric I (M k)) {p : ∀ k, M k}
    (c : ∀ k, NormalBallChart (I := I) (p k)) (a : E) {r R : ℝ}
    (hr : 0 < r) (hball : ∀ k, Metric.ball a r ⊆ Metric.ball (0 : E) (c k).radius)
    (htranslate : Metric.ball a r ⊆ Metric.ball (0 : E) R)
    (hell : ∀ k, (c k).MetricEquivOn (g k) (Metric.ball (0 : E) R)) :
    ∀ k, ((c k).recenter a hr (hball k)).MetricEquivOn (g k) (Metric.ball (0 : E) r) := by
  intro k
  exact MetricEquivOn.recenter (g k) a hr (hball k)
    (fun z hz => hell k z (htranslate hz))

end DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.NormalBallChart

end
