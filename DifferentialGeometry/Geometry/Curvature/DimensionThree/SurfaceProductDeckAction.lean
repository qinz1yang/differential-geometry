import DifferentialGeometry.Geometry.Curvature.DimensionThree.SurfaceProductCompactness
import DifferentialGeometry.Geometry.Metric.UniversalCover.DeckProductAction

set_option autoImplicit false

noncomputable section

open scoped Manifold ContDiff

namespace DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover.GlobalSurfaceProductSplitting

variable {H : Type} [TopologicalSpace H]
  {I : ModelWithCorners ℝ (DifferentialGeometry.Topology.Morse.MorseModel 3) H}
  [I.Boundaryless]
  {M : Type} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M] [ConnectedSpace M]
  [LocallyPathConnectedSpace M]
  [DifferentialGeometry.Geometry.Riemannian.Topology.SemilocallySimplyConnectedSpace M]
  [Inhabited M]

theorem exists_affine_deck_action_of_base_scalar_ne_zero
    (g : SmoothRiemannianMetric I M)
    (P : GlobalSurfaceProductSplitting (I := I) (M := M) g)
    (hscalar : ∀ x, DifferentialGeometry.Geometry.Curvature.metricScalarAt g x ≠ 0)
    (a : FundamentalGroup M (default : M)) :
    let _ : TopologicalSpace P.N := P.topologyN
    let _ : ChartedSpace (DifferentialGeometry.Topology.Morse.MorseModel 2) P.N := P.chartedN
    let _ : IsManifold 𝓘(ℝ, DifferentialGeometry.Topology.Morse.MorseModel 2) ∞ P.N := P.manifoldN
    let _ : T2Space P.N := P.t2N
    ∃ (φ : P.N ≃ₘ⟮𝓘(ℝ, DifferentialGeometry.Topology.Morse.MorseModel 2),
        𝓘(ℝ, DifferentialGeometry.Topology.Morse.MorseModel 2)⟯ P.N) (ε c : ℝ),
      (ε = 1 ∨ ε = -1) ∧ Diffeomorph.pullbackMetric P.metricN φ = P.metricN ∧
        ∀ y r, a • P.F (y, r) = P.F (φ y, ε * r + c) := by
  let _ : TopologicalSpace P.N := P.topologyN
  let _ : ChartedSpace (DifferentialGeometry.Topology.Morse.MorseModel 2) P.N := P.chartedN
  let _ : IsManifold 𝓘(ℝ, DifferentialGeometry.Topology.Morse.MorseModel 2) ∞ P.N := P.manifoldN
  let _ : T2Space P.N := P.t2N
  let _ : SigmaCompactSpace P.N := P.sigmaN
  let _ : ConnectedSpace P.N := P.connectedN
  apply exists_affine_product_deck_action_of_scalar_ne_zero P.metricN
    (by simp [DifferentialGeometry.Topology.Morse.MorseModel])
    (fun y => ?_) g P.F (by simpa only [flatModelMetric] using P.pullbackMetric_eq_prod g) a
  rw [P.metricScalarAt_eq_base g y 0]
  exact hscalar _

end DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover.GlobalSurfaceProductSplitting
