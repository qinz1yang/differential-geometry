import DifferentialGeometry.Geometry.Comparison.Volume.BoundaryInteriorAtlasMetric

/-!
The actual original interior geodesic equation also lifts into the genuine interior atlas.
Both directions use the original restricted metric and the native atlas identity.
-/

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set
open scoped Manifold ContDiff
open DifferentialGeometry.Geometry.Riemannian.Geodesic

namespace DifferentialGeometry.Geometry.Riemannian.VolumeComparison

variable {E : Type*} [ambientNorm : NormedAddCommGroup E]
  [ambientSpace : NormedSpace ℝ E] [ambientFinite : FiniteDimensional ℝ E]
  {H : Type*} [modelTopology : TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [manifoldTopology : TopologicalSpace M] [manifoldCharts : ChartedSpace H M]
  [manifoldSmooth : IsManifold I ∞ M] [manifoldT2 : T2Space M]

private theorem interiorEquation_infty_ne_zero : (∞ : WithTop ℕ∞) ≠ 0 := by simp

theorem boundaryInteriorAtlas_geodesicEquation_iff (g : SmoothRiemannianMetric I M) :
    let U := DifferentialGeometry.Manifold.intrinsicInterior I ∞
      interiorEquation_infty_ne_zero (M := M)
    let _interiorCharts := DifferentialGeometry.Manifold.interiorChartedSpace I ∞ (M := U)
    let _interiorSmooth := DifferentialGeometry.Manifold.interiorIsManifold I ∞ (M := U)
    ∀ (γ : ℝ → U) (t : ℝ), ContMDiffAt 𝓘(ℝ) 𝓘(ℝ, E) ∞ γ t →
      (HasGeodesicEquationAt (boundaryInteriorAtlasMetric g) γ t ↔
        HasGeodesicEquationAt g (fun s => (γ s : M)) t) := by
  let U := DifferentialGeometry.Manifold.intrinsicInterior I ∞
    interiorEquation_infty_ne_zero (M := M)
  let Φ := DifferentialGeometry.Manifold.interiorAtlasDiffeomorph I ∞ (M := U)
  let _interiorCharts := DifferentialGeometry.Manifold.interiorChartedSpace I ∞ (M := U)
  let _interiorSmooth := DifferentialGeometry.Manifold.interiorIsManifold I ∞ (M := U)
  dsimp only
  intro γ t hγ
  constructor
  · exact boundaryInteriorAtlas_geodesicEquation g γ t hγ
  · intro hgeo
    have hold := (boundaryOpen_geodesicEquation_iff (g := g) (U := U)
      (γ := γ) (t := t) (γ t).property).mpr hgeo
    have hmapped : HasGeodesicEquationAt (g.restrictOpen U)
        (fun s => Φ.symm (γ s)) t := hold
    exact geoEq_of_mapCrossAt (g.restrictOpen U) Φ.symm γ t hγ hmapped

end DifferentialGeometry.Geometry.Riemannian.VolumeComparison
