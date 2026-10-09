import DifferentialGeometry.Geometry.Curvature.Naturality.Pullback.Cross
import DifferentialGeometry.Geometry.Comparison.RadialHessianLowerBound

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.Geometry.Riemannian

open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F] [CompleteSpace F]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {G : Type*} [TopologicalSpace G] {J : ModelWithCorners ℝ F G}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
variable {N : Type*} [TopologicalSpace N] [ChartedSpace G N] [IsManifold J ∞ N] [T2Space N]

theorem sectionalBoundedBelowAt_pullbackMetricCross
    (g : SmoothRiemannianMetric J N) (Φ : M ≃ₘ⟮I, J⟯ N) (x : M) {K : ℝ}
    (hg : SectionalBoundedBelowAt g (Φ x) K) :
    SectionalBoundedBelowAt (Diffeomorph.pullbackMetricCross g Φ) x K := by
  intro v w
  rw [metricRm04Standard_pullbackCross, Diffeomorph.pullbackMetricCross_inner,
    Diffeomorph.pullbackMetricCross_inner, Diffeomorph.pullbackMetricCross_inner]
  exact hg _ _

theorem sectionalBoundedBelow_pullbackMetricCross
    (g : SmoothRiemannianMetric J N) (Φ : M ≃ₘ⟮I, J⟯ N) {K : ℝ}
    (hg : SectionalBoundedBelow g K) :
    SectionalBoundedBelow (Diffeomorph.pullbackMetricCross g Φ) K :=
  fun x => sectionalBoundedBelowAt_pullbackMetricCross g Φ x (hg (Φ x))

theorem exists_sectionalBoundedBelow_of_diffeomorph
    (Φ : M ≃ₘ⟮I, J⟯ N) {K : ℝ} (g : SmoothRiemannianMetric J N)
    (hg : SectionalBoundedBelow g K) :
    ∃ h : SmoothRiemannianMetric I M, SectionalBoundedBelow h K :=
  ⟨Diffeomorph.pullbackMetricCross g Φ, sectionalBoundedBelow_pullbackMetricCross g Φ hg⟩

end DifferentialGeometry.Geometry.Riemannian

end
