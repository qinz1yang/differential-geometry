import Mathlib.Geometry.Manifold.Instances.Real
import DifferentialGeometry.Geometry.Metric.Convergence.Naturality.PullbackCross
import DifferentialGeometry.Geometry.Metric.Tensor.IsometryNorm
import DifferentialGeometry.Geometry.Curvature.LocalIsometry
import DifferentialGeometry.Geometry.Metric.OpenEmbeddingPullback

set_option autoImplicit false
noncomputable section
open Set Function TopologicalSpace Manifold DifferentialGeometry
open DifferentialGeometry.Tensor0SBundle DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Tensor DifferentialGeometry.Geometry.Metric DifferentialGeometry.Topology.Manifold
open scoped Manifold ContDiff Topology
namespace DifferentialGeometry.Geometry.Curvature
variable {E F H K M N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [TopologicalSpace H] [TopologicalSpace K]
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F K}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [TopologicalSpace N] [ChartedSpace K N] [IsManifold J ∞ N] [T2Space N]

private theorem actual_isometry_curvature_jets [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric I M) (h : SmoothRiemannianMetric J N)
    (D : M ≃ₘ⟮I, J⟯ N)
    (hmetric : ∀ (y : M) (v w : TangentSpace I y),
      g.inner y v w = h.inner (D y) (mfderiv I J D y v) (mfderiv I J D y w))
    (j : ℕ) (x : M) :
    Real.sqrt (normSq0S g x (4 + j) (iterCov g 4 (metricRm04 g) j x)) =
      Real.sqrt (normSq0S h (D x) (4 + j) (iterCov h 4 (metricRm04 h) j (D x))) := by
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  let _ : CompleteSpace F := FiniteDimensional.complete ℝ F
  have hg : g = Diffeomorph.pullbackMetricCross h D := by
    apply SmoothRiemannianMetric.ext_inner
    intro y v w
    exact hmetric y v w
  have hRm (y : M) (v : Fin 4 → TangentSpace I y) :
      metricRm04 g y v = metricRm04 h (D y) (fun i => mfderiv I J D y (v i)) := by
    rw [hg]
    exact metricRm04_cross h D y v
  have hjet := iter_cov_of_metric_isometry g h D hmetric (metricRm04 g) (metricRm04 h) hRm j x
  obtain ⟨basis, hON⟩ := Tensor0SBundle.exists_orthonormal_basis (Diffeomorph.pullbackMetricCross h D) x
  apply congrArg Real.sqrt
  rw [hg]
  exact normSq0S_pullbackCross_eval_of_orthonormal h D x (4 + j) basis hON _ _
    (by rw [← hg]; exact hjet)

private theorem actual_curvature_jet_restriction
    (g : SmoothRiemannianMetric J N) (U : Opens N) (j : ℕ) (x : U) :
    Real.sqrt (normSq0S (g.restrictOpen U) x (4 + j)
      (iterCov (g.restrictOpen U) 4 (metricRm04 (g.restrictOpen U)) j x)) =
    Real.sqrt (normSq0S g (x : N) (4 + j) (iterCov g 4 (metricRm04 g) j (x : N))) := by
  have hr : metricRm04 (g.restrictOpen U) = restrictOpen0S 4 (V := U) (metricRm04 g) := by
    apply DFunLike.ext
    intro q
    apply tensor0SSpace_ext (I := J) 4 q
    intro w
    have ht := metricRm04StandardAt_restrictOpen g U q (w 0) (w 1) (w 2) (w 3)
    simp only [mfderiv_subtype_val_apply] at ht
    have hw : vec4 (w 0) (w 1) (w 2) (w 3) = w := by
      funext i
      fin_cases i <;> rfl
    change metricRm04 (g.restrictOpen U) q (vec4 (w 0) (w 1) (w 2) (w 3)) =
      metricRm04 g (q : N) (vec4 (w 0) (w 1) (w 2) (w 3)) at ht
    rw [hw] at ht
    exact ht
  rw [hr, iter_cov_restrict_open, normSq0S_restrictOpen_apply]
  rfl

theorem curvature_jets_of_injective_local_isometry [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric I M) (h : SmoothRiemannianMetric J N)
    (f : M → N) (hf : IsLocalDiffeomorph I J ∞ f) (hinj : Injective f)
    (hmetric : ∀ (x : M) (v w : TangentSpace I x),
      g.inner x v w = h.inner (f x) (mfderiv I J f x v) (mfderiv I J f x w))
    (j : ℕ) (x : M) :
    Real.sqrt (normSq0S g x (4 + j) (iterCov g 4 (metricRm04 g) j x)) =
      Real.sqrt (normSq0S h (f x) (4 + j) (iterCov h 4 (metricRm04 h) j (f x))) := by
  let D := diffeomorphOntoImage f hf hinj
  have hg : g = pullbackMetricOfInjectiveLocalDiffeomorph h f hf hinj := by
    apply SmoothRiemannianMetric.ext_inner
    intro y v w
    rw [pullbackMetricOfInjectiveLocalDiffeomorph_inner]
    exact hmetric y v w
  have he : g = Diffeomorph.pullbackMetricCross (h.restrictOpen hf.image) D := by
    rw [hg]
    apply SmoothRiemannianMetric.ext_inner
    intro y v w
    rw [Diffeomorph.pullbackMetricCross_inner]
    exact Diffeomorph.pullbackMetricCross_inner (h.restrictOpen hf.image) D y v w
  have hm : ∀ (y : M) (v w : TangentSpace I y),
      g.inner y v w = (h.restrictOpen hf.image).inner (D y)
        (mfderiv I J D y v) (mfderiv I J D y w) := by
    intro y v w
    rw [he, Diffeomorph.pullbackMetricCross_inner]
  have hj := (actual_isometry_curvature_jets g (h.restrictOpen hf.image) D hm j x)
  have hr := actual_curvature_jet_restriction h hf.image j (D x)
  simpa only [D, diffeomorphOntoImage_apply] using hj.trans hr
end DifferentialGeometry.Geometry.Curvature
