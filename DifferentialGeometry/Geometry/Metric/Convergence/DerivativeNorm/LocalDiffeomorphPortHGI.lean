import DifferentialGeometry.Geometry.Metric.Convergence.DerivativeNorm.GeneralHGI
import DifferentialGeometry.Geometry.Metric.Convergence.DerivativeNorm.PartialDiffeomorph
import DifferentialGeometry.Geometry.Metric.Convergence.FiniteOrderNorm
import DifferentialGeometry.Geometry.Metric.Pullback.Local

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.CheegerGromovCompactness

open scoped Manifold ContDiff Topology ENNReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {G : Type*} [TopologicalSpace G] {J : ModelWithCorners ℝ F G}
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N] [IsManifold J ∞ N] [T2Space N]

theorem metricDerivNorm_localPullMetric
    (gk gInf gRef : SmoothRiemannianMetric J N) (f : M → N)
    (hf : IsLocalDiffeomorph I J ∞ f) (a : ℕ) (x : M) :
    metricDerivNorm a (localPullMetric gk f hf) (localPullMetric gInf f hf)
      (localPullMetric gRef f hf) x = metricDerivNorm a gk gInf gRef (f x) := by
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  obtain ⟨Φ, hx, hΦ⟩ := hf x
  let U : TopologicalSpace.Opens M := ⟨Φ.source, Φ.open_source⟩
  have hinner (g : SmoothRiemannianMetric J N) (y : U) (v w : TangentSpace I y) :
      ((localPullMetric g f hf).restrictOpen U).inner y v w =
        g.inner (Φ (y : M)) (mfderiv I J Φ (y : M) v) (mfderiv I J Φ (y : M) w) := by
    rw [SmoothRiemannianMetric.restrictOpen_inner]
    have hpull := localPullMetric_inner g f hf (y : M) v w
    refine hpull.trans ?_
    have heq : f =ᶠ[𝓝 (y : M)] (Φ : M → N) :=
      Filter.Eventually.mono (Φ.open_source.mem_nhds y.property) fun z hz => hΦ hz
    rw [heq.eq_of_nhds, heq.mfderiv_eq]
    rfl
  have hlocal := HGI.metricDerivNorm_eq_of_partialDiffeomorph_inner Φ (U := U) Set.Subset.rfl
    gk gInf gRef ((localPullMetric gk f hf).restrictOpen U)
    ((localPullMetric gInf f hf).restrictOpen U) ((localPullMetric gRef f hf).restrictOpen U)
    (hinner gk) (hinner gInf) (hinner gRef) a ⟨x, hx⟩
  have hrestrict := HGI.metricDerivNorm_restrictOpen (localPullMetric gk f hf)
    (localPullMetric gInf f hf) (localPullMetric gRef f hf) U a ⟨x, hx⟩
  exact hrestrict.symm.trans (hlocal.trans (congrArg (metricDerivNorm a gk gInf gRef) (hΦ hx).symm))

theorem metricCkENormOn_localPullMetric
    (K : Set M) (p : ℕ) (gk gInf gRef : SmoothRiemannianMetric J N) (f : M → N)
    (hf : IsLocalDiffeomorph I J ∞ f) :
    metricCkENormOn K p (localPullMetric gk f hf) (localPullMetric gInf f hf)
      (localPullMetric gRef f hf) = metricCkENormOn (f '' K) p gk gInf gRef := by
  simp only [metricCkENormOn, metricDerivNorm_localPullMetric, iSup_image]

theorem metricCkENormOn_localPullMetric_le_of_mapsTo
    {K : Set M} {L : Set N} (p : ℕ) (gk gInf gRef : SmoothRiemannianMetric J N)
    (f : M → N) (hf : IsLocalDiffeomorph I J ∞ f) (hKL : Set.MapsTo f K L) :
    metricCkENormOn K p (localPullMetric gk f hf) (localPullMetric gInf f hf)
      (localPullMetric gRef f hf) ≤ metricCkENormOn L p gk gInf gRef := by
  rw [metricCkENormOn_localPullMetric]
  exact metricCkENormOn_mono_set hKL.image_subset p gk gInf gRef

end DifferentialGeometry.CheegerGromovCompactness
