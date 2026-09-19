import DifferentialGeometry.Geometry.Flow.RicciFlow.Uniqueness.Forward.BufferedReference
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Solutions.Pullback

set_option autoImplicit false
noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open Set
open DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M] [ConnectedSpace M]

theorem pullbackMetricCross_eq_of_initial_isometry_of_complete_bounded_curvature
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn S) {a₀ a b K : ℝ} (ha : a₀ < a) (hab : a < b)
    (hcarrier : Icc a₀ b ⊆ D.carrier) (hregular : Ioo a₀ b ⊆ D.regular)
    (hcomplete : RiemannianMetricComplete (S.base.metric a₀))
    (hK : 0 ≤ K)
    (hcurvature : ∀ t ∈ Icc a₀ b, ∀ x : M,
      normSq0S (S.base.metric t) x 4 (S.base.rm04 t x) ≤ K)
    (Phi : M ≃ₘ⟮I, I⟯ M)
    (hinitial : Diffeomorph.pullbackMetricCross (S.base.metric a) Phi = S.base.metric a) :
    ∀ t ∈ Icc a b,
      Diffeomorph.pullbackMetricCross (S.base.metric t) Phi = S.base.metric t := by
  let P := S.pullback Phi
  have hP : IsSolutionOn P := IsSolutionOn.pullback S hS Phi
  have hcurvatureP : ∀ t ∈ Icc a₀ b, ∀ x : M,
      normSq0S (P.base.metric t) x 4 (P.base.rm04 t x) ≤ K := by
    intro t ht x
    change normSq0S (Diffeomorph.pullbackMetricCross (S.base.metric t) Phi) x 4
      (metricRm04At (Diffeomorph.pullbackMetricCross (S.base.metric t) Phi) x) ≤ K
    rw [DifferentialGeometry.CheegerGromovCompactness.riemannNormSq_cross]
    exact hcurvature t ht (Phi x)
  exact forward_unique_on_closed_slab_of_complete_bounded_curvature_of_buffered_reference
    P S hP hS ha hab
    (fun t ht => hcarrier ⟨ha.le.trans ht.1, ht.2⟩) hcarrier
    (fun t ht => hregular ⟨ha.trans ht.1, ht.2⟩) hregular hcomplete hK hK
    (fun t ht => hcurvatureP t ⟨ha.le.trans ht.1, ht.2⟩) hcurvature hinitial

end DifferentialGeometry.PDE.RicciFlow
