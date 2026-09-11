import Mathlib.Geometry.Manifold.Instances.Real
import DifferentialGeometry.Tensor.Metric.IsometryNorm
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
private abbrev JetsE3 := EuclideanSpace ℝ (Fin 3)
private local instance : NeZero (Module.finrank ℝ JetsE3) := ⟨by simp⟩
variable {M N : Type*} [TopologicalSpace M] [ChartedSpace JetsE3 M] [IsManifold (𝓡 3) ∞ M] [T2Space M]
  [TopologicalSpace N] [ChartedSpace JetsE3 N] [IsManifold (𝓡 3) ∞ N] [T2Space N]
private theorem actual_isometry_curvature_jets
    (g : SmoothRiemannianMetric (𝓡 3) M) (h : SmoothRiemannianMetric (𝓡 3) N)
    (D : M ≃ₘ⟮𝓡 3, 𝓡 3⟯ N)
    (hmetric : ∀ (y : M) (v w : TangentSpace (𝓡 3) y),
      g.inner y v w = h.inner (D y) (mfderiv (𝓡 3) (𝓡 3) D y v) (mfderiv (𝓡 3) (𝓡 3) D y w))
    (j : ℕ) (x : M) :
    Real.sqrt (normSq0S g x (4 + j) (iterCov g 4 (metricRm04 g) j x)) =
      Real.sqrt (normSq0S h (D x) (4 + j) (iterCov h 4 (metricRm04 h) j (D x))) ∧
      metricScalarAt g x = metricScalarAt h (D x) := by
  have hg : g = Diffeomorph.pullbackMetric h D := by
    apply SmoothRiemannianMetric.ext_inner
    intro y v w
    rw [Diffeomorph.pullbackMetric_inner]
    exact hmetric y v w
  have hRm (y : M) (w : Fin 4 → TangentSpace (𝓡 3) y) :
      metricRm04 g y w = metricRm04 h (D y) (fun i => mfderiv (𝓡 3) (𝓡 3) D y (w i)) := by
    rw [hg]
    have hc := metricRm04Standard_pullback h D y (w 0) (w 1) (w 2) (w 3)
    have hw : vec4 (w 0) (w 1) (w 2) (w 3) = w := by
      funext i
      fin_cases i <;> rfl
    have hdw : vec4 (mfderiv (𝓡 3) (𝓡 3) D y (w 0)) (mfderiv (𝓡 3) (𝓡 3) D y (w 1))
        (mfderiv (𝓡 3) (𝓡 3) D y (w 2)) (mfderiv (𝓡 3) (𝓡 3) D y (w 3)) =
        (fun i => mfderiv (𝓡 3) (𝓡 3) D y (w i)) := by
      funext i
      fin_cases i <;> rfl
    change metricRm04 (Diffeomorph.pullbackMetric h D) y (vec4 (w 0) (w 1) (w 2) (w 3)) =
      metricRm04 h (D y) (vec4 (mfderiv (𝓡 3) (𝓡 3) D y (w 0)) (mfderiv (𝓡 3) (𝓡 3) D y (w 1))
        (mfderiv (𝓡 3) (𝓡 3) D y (w 2)) (mfderiv (𝓡 3) (𝓡 3) D y (w 3))) at hc
    rw [hw, hdw] at hc
    exact hc
  have hjet := iter_cov_of_metric_isometry g h D hmetric (metricRm04 g) (metricRm04 h) hRm j x
  have hn := normSq0S_of_metric_isometry g h D hmetric (4 + j) x _ _ hjet
  refine ⟨congrArg Real.sqrt hn, ?_⟩
  rw [hg]
  exact metricScalarAt_pullback h D x
private theorem actual_curvature_jet_restriction
    (g : SmoothRiemannianMetric (𝓡 3) N) (U : Opens N) [SigmaCompactSpace U] (j : ℕ) (x : U) :
    Real.sqrt (normSq0S (g.restrictOpen U) x (4 + j)
      (iterCov (g.restrictOpen U) 4 (metricRm04 (g.restrictOpen U)) j x)) =
    Real.sqrt (normSq0S g (x : N) (4 + j) (iterCov g 4 (metricRm04 g) j (x : N))) := by
  have hr : metricRm04 (g.restrictOpen U) = restrictOpen0S 4 (V := U) (metricRm04 g) := by
    apply DFunLike.ext
    intro q
    apply tensor0SSpace_ext (I := 𝓡 3) 4 q
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
    (g : SmoothRiemannianMetric (𝓡 3) M) (h : SmoothRiemannianMetric (𝓡 3) N)
    (f : M → N) (hf : IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ f) (hinj : Injective f)
    (hmetric : ∀ (x : M) (v w : TangentSpace (𝓡 3) x),
      g.inner x v w = h.inner (f x) (mfderiv (𝓡 3) (𝓡 3) f x v) (mfderiv (𝓡 3) (𝓡 3) f x w))
    (j : ℕ) (x : M) :
    Real.sqrt (normSq0S g x (4 + j) (iterCov g 4 (metricRm04 g) j x)) =
      Real.sqrt (normSq0S h (f x) (4 + j) (iterCov h 4 (metricRm04 h) j (f x))) := by
  let D := diffeomorphOntoImage f hf hinj
  have hrange : range D = univ := D.surjective.range_eq
  let : SigmaCompactSpace hf.image := isSigmaCompact_univ_iff.mp
    (hrange ▸ isSigmaCompact_range D.continuous)
  have hg : g = pullbackMetricOfInjectiveLocalDiffeomorph h f hf hinj := by
    apply SmoothRiemannianMetric.ext_inner
    intro y v w
    rw [pullbackMetricOfInjectiveLocalDiffeomorph_inner]
    exact hmetric y v w
  have he : g = Diffeomorph.pullbackMetric (h.restrictOpen hf.image) D := by
    rw [hg]
    apply SmoothRiemannianMetric.ext_inner
    intro y v w
    rw [Diffeomorph.pullbackMetric_inner]
    exact Diffeomorph.pullbackMetricCross_inner (h.restrictOpen hf.image) D y v w
  have hm : ∀ (y : M) (v w : TangentSpace (𝓡 3) y),
      g.inner y v w = (h.restrictOpen hf.image).inner (D y)
        (mfderiv (𝓡 3) (𝓡 3) D y v) (mfderiv (𝓡 3) (𝓡 3) D y w) := by
    intro y v w
    rw [he, Diffeomorph.pullbackMetric_inner]
  have hj := (actual_isometry_curvature_jets g (h.restrictOpen hf.image) D hm j x).1
  have hr := actual_curvature_jet_restriction h hf.image j (D x)
  simpa only [D, diffeomorphOntoImage_apply] using hj.trans hr
end DifferentialGeometry.Geometry.Curvature
