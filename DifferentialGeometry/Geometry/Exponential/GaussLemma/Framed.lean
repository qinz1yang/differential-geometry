import DifferentialGeometry.Geometry.Exponential.GaussLemma.Pullback
import DifferentialGeometry.Geometry.Exponential.Smoothness.Framed
import DifferentialGeometry.Geometry.Comparison.RadialLength
import DifferentialGeometry.Geometry.Metric.PointwiseInner.Bounds

open Set
open scoped Manifold ContDiff

namespace DifferentialGeometry.Geometry.Riemannian.NormalCoordinates

open Exponential

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space (TangentBundle I M)]

theorem gauss_lemma_framedExpMap
    (g : SmoothRiemannianMetric I M) (p : M) {z : E} (v : E)
    (hz : normalFrame g p z ∈ expDomain g p) :
    g.inner (framedExpMap g p z)
      (mfderiv 𝓘(ℝ, E) I (framedExpMap g p) z z)
      (mfderiv 𝓘(ℝ, E) I (framedExpMap g p) z v) = inner ℝ z v := by
  rw [mfderiv_framedExpMap g p hz]
  change g.inner (expMap g p (normalFrame g p z))
      (mfderiv 𝓘(ℝ, E) I (fun u : E => expMap g p (show TangentSpace I p from u))
        (normalFrame g p z) (normalFrame g p z))
      (mfderiv 𝓘(ℝ, E) I (fun u : E => expMap g p (show TangentSpace I p from u))
        (normalFrame g p z) (normalFrame g p v)) = inner ℝ z v
  exact (gauss_lemma g p hz).trans (normalFrame_inner g p z v)

theorem framedExpMap_radial_lower_bound
    (g : SmoothRiemannianMetric I M) (p : M) {z : E} (v : E)
    (hz : normalFrame g p z ∈ expDomain g p) :
    |inner ℝ z v| ≤ ‖z‖ * Real.sqrt (g.inner (framedExpMap g p z)
      (mfderiv 𝓘(ℝ, E) I (framedExpMap g p) z v)
      (mfderiv 𝓘(ℝ, E) I (framedExpMap g p) z v)) := by
  have h := DifferentialGeometry.Analysis.Laplacian.abs_metric_inner_le_sqrt_metric_quadratic
    g (framedExpMap g p z) (mfderiv 𝓘(ℝ, E) I (framedExpMap g p) z z)
      (mfderiv 𝓘(ℝ, E) I (framedExpMap g p) z v)
  rw [gauss_lemma_framedExpMap g p v hz, gauss_lemma_framedExpMap g p z hz,
    real_inner_self_eq_norm_sq, Real.sqrt_sq (norm_nonneg z)] at h
  exact h

theorem norm_sub_le_pathELength_framedExpMap
    [(x : M) → ENorm (TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (p : M) {η : ℝ → E} {a b : ℝ}
    (hab : a ≤ b) (hη : ContDiffOn ℝ 1 η (Icc a b))
    (hdom : ∀ x ∈ Icc a b, normalFrame g p (η x) ∈ expDomain g p) :
    ENNReal.ofReal (‖η b‖ - ‖η a‖) ≤ Manifold.pathELength I (framedExpMap g p ∘ η) a b := by
  exact Manifold.norm_sub_le_pathELength_comp_of_radial_bound
    g.toContinuousRiemannianMetric hEnorm (framedExpMap g p) hab hη
    (fun x hx => (contMDiffAt_framedExpMap g p (hdom x hx)).of_le (by simp))
    (fun x hx v => (le_abs_self _).trans
      (framedExpMap_radial_lower_bound g p v (hdom x (Ioo_subset_Icc_self hx))))

theorem norm_le_pathELength_framedExpMap
    [(x : M) → ENorm (TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (p : M) {η : ℝ → E} {a b : ℝ}
    (hab : a ≤ b) (hηa : η a = 0) (hη : ContDiffOn ℝ 1 η (Icc a b))
    (hdom : ∀ x ∈ Icc a b, normalFrame g p (η x) ∈ expDomain g p) :
    ENNReal.ofReal ‖η b‖ ≤ Manifold.pathELength I (framedExpMap g p ∘ η) a b := by
  simpa only [hηa, norm_zero, sub_zero] using
    norm_sub_le_pathELength_framedExpMap g hEnorm p hab hη hdom

end DifferentialGeometry.Geometry.Riemannian.NormalCoordinates
