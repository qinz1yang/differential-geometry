import DifferentialGeometry.Geometry.Comparison.Volume.BoundaryInteriorRicci
import DifferentialGeometry.Geometry.Comparison.Distance.Continuity

/-!
Actual original distance balls keep their Ricci bound under the genuine true interior atlas change.
The corners model remains on the restricted metric; only the genuine interior uses the self model.
-/

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set
open scoped Manifold ContDiff ENNReal
open DifferentialGeometry.Geometry.Curvature

namespace DifferentialGeometry.Geometry.Riemannian.VolumeComparison

variable {E : Type*} [ambientNorm : NormedAddCommGroup E]
  [ambientSpace : NormedSpace ℝ E] [ambientFinite : FiniteDimensional ℝ E]
  {H : Type*} [modelTopology : TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [manifoldTopology : TopologicalSpace M] [manifoldCharts : ChartedSpace H M]
  [manifoldSmooth : IsManifold I ∞ M] [manifoldT2 : T2Space M]

private theorem interiorRicciBall_infty_ne_zero : (∞ : WithTop ℕ∞) ≠ 0 := by simp

theorem boundaryInteriorAtlas_ricci_ball_lower (g : SmoothRiemannianMetric I M) (p : M) :
    let U := DifferentialGeometry.Manifold.intrinsicInterior I ∞
      interiorRicciBall_infty_ne_zero (M := M)
    let _interiorCharts := DifferentialGeometry.Manifold.interiorChartedSpace I ∞ (M := U)
    let _interiorSmooth := DifferentialGeometry.Manifold.interiorIsManifold I ∞ (M := U)
    ∀ κ L : ℝ,
      (∀ (x : U) (v : TangentSpace I x),
        DifferentialGeometry.riemannianEDistOf g p (x : M) < ENNReal.ofReal L →
        -2 * κ ^ 2 * (g.restrictOpen U).inner x v v ≤
          ricciTensor (g.restrictOpen U) x v v) →
      ∀ (x : U) (v : TangentSpace 𝓘(ℝ, E) x),
        DifferentialGeometry.riemannianEDistOf g p (x : M) < ENNReal.ofReal L →
        -2 * κ ^ 2 * (boundaryInteriorAtlasMetric g).inner x v v ≤
          ricciTensor (boundaryInteriorAtlasMetric g) x v v := by
  let U := DifferentialGeometry.Manifold.intrinsicInterior I ∞
    interiorRicciBall_infty_ne_zero (M := M)
  let Φ := DifferentialGeometry.Manifold.interiorAtlasDiffeomorph I ∞ (M := U)
  let _interiorCharts := DifferentialGeometry.Manifold.interiorChartedSpace I ∞ (M := U)
  let _interiorSmooth := DifferentialGeometry.Manifold.interiorIsManifold I ∞ (M := U)
  dsimp only
  intro κ L hRic x v hball
  have hcurve := boundaryInteriorAtlas_ricci g x v v
  have hinner := DifferentialGeometry.Diffeomorph.pullbackMetricCross_inner
    (g.restrictOpen U) Φ.symm x v v
  change (boundaryInteriorAtlasMetric g).inner x v v = _ at hinner
  rw [hcurve, hinner]
  exact hRic (Φ.symm x) (mfderiv 𝓘(ℝ, E) I Φ.symm x v) hball

end DifferentialGeometry.Geometry.Riemannian.VolumeComparison
