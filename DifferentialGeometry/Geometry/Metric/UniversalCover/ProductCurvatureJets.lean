import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Bounds.BoundedGeometry
import DifferentialGeometry.Geometry.Metric.Pullback.Cross
import DifferentialGeometry.Geometry.Metric.UniversalCover.Metric


set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open DifferentialGeometry.Geometry.Riemannian.Topology
open DifferentialGeometry.CheegerGromovCompactness
open scoped Manifold ContDiff

section CrossDiffeomorphism

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] {J : ModelWithCorners ℝ F G}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N] [IsManifold J ∞ N] [T2Space N]


theorem curvDerivNorm_pullbackMetricCross
    (g : SmoothRiemannianMetric J N) (Phi : M ≃ₘ⟮I, J⟯ N) (m : ℕ) (x : M) :
    curvDerivNorm (I := I) m (Diffeomorph.pullbackMetricCross g Phi) x =
      curvDerivNorm (I := J) m g (Phi x) := by
  sorry

end CrossDiffeomorphism

section RealProduct

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]


theorem curvDerivNorm_le_product_real_of_inner_eq
    (h : SmoothRiemannianMetric I M)
    (gP : SmoothRiemannianMetric (I.prod 𝓘(ℝ, ℝ)) (M × ℝ))
    (b : ℝ) (hb : 0 < b)
    (hproduct : ∀ (y : M) (s : ℝ) (v w : TangentSpace I y) (a c : ℝ),
      gP.inner (y, s) (v, a) (w, c) = h.inner y v w + b * (a * c))
    (m : ℕ) (y : M) (s : ℝ) :
    curvDerivNorm (I := I) m h y ≤
      curvDerivNorm (I := I.prod 𝓘(ℝ, ℝ)) m gP (y, s) := by
  sorry

end RealProduct

section UniversalCoverLift

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M] [ConnectedSpace M]
  [LocallyPathConnectedSpace M] [SemilocallySimplyConnectedSpace M] [Inhabited M]


theorem curvDerivNorm_liftedMetric
    (g : SmoothRiemannianMetric I M) (m : ℕ) (x' : UniversalCover M) :
    curvDerivNorm (I := I) m (UniversalCover.liftedMetric (I := I) g) x' =
      curvDerivNorm (I := I) m g (UniversalCover.proj x') := by
  sorry

end UniversalCoverLift

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
