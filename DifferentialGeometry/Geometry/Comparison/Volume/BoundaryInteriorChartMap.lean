import DifferentialGeometry.Geometry.Comparison.Volume.BoundaryInteriorAtlasMetric
import DifferentialGeometry.Topology.Manifold.LocalDiffeomorph.Open

/-!
The original interior chart composed with genuine inclusion is a local diffeomorphism.
Its source is an actual open subset of the true interior with the new boundaryless atlas.
-/

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry.Riemannian.VolumeComparison

variable {E : Type*} [ambientNorm : NormedAddCommGroup E]
  [ambientSpace : NormedSpace ℝ E] [ambientFinite : FiniteDimensional ℝ E]
  {H : Type*} [modelTopology : TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [manifoldTopology : TopologicalSpace M] [manifoldCharts : ChartedSpace H M]
  [manifoldSmooth : IsManifold I ∞ M]

private theorem interiorChartMap_infty_ne_zero : (∞ : WithTop ℕ∞) ≠ 0 := by simp

omit ambientFinite in
theorem boundaryInteriorChart_localDiffeomorph (p : M) :
    let U := DifferentialGeometry.Manifold.intrinsicInterior I ∞
      interiorChartMap_infty_ne_zero (M := M)
    let _interiorCharts := DifferentialGeometry.Manifold.interiorChartedSpace I ∞ (M := U)
    let _interiorSmooth := DifferentialGeometry.Manifold.interiorIsManifold I ∞ (M := U)
    let F := fun x : U => extChartAt I p (x : M)
    let S := {x : U | (x : M) ∈ (DifferentialGeometry.Manifold.interiorChart I ∞ p).source}
    IsOpen S ∧ IsLocalDiffeomorphOn 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ F S := by
  let U := DifferentialGeometry.Manifold.intrinsicInterior I ∞
    interiorChartMap_infty_ne_zero (M := M)
  let Φ := DifferentialGeometry.Manifold.interiorAtlasDiffeomorph I ∞ (M := U)
  have hvalOld := DifferentialGeometry.isLocalDiffeomorph_subtype_val (I := I) U
  let _interiorCharts := DifferentialGeometry.Manifold.interiorChartedSpace I ∞ (M := U)
  let _interiorSmooth := DifferentialGeometry.Manifold.interiorIsManifold I ∞ (M := U)
  dsimp only
  refine ⟨(DifferentialGeometry.Manifold.interiorChart I ∞ p).open_source.preimage
    continuous_subtype_val, ?_⟩
  rintro ⟨x, hx⟩
  have hinc : IsLocalDiffeomorphAt 𝓘(ℝ, E) I ∞ (Subtype.val : U → M) x := by
    have hh := (Φ.symm.isLocalDiffeomorph x).comp I M (hvalOld (Φ.symm x))
    exact hh
  have hchart := (DifferentialGeometry.Manifold.interiorChart I ∞ p).isLocalDiffeomorphAt
    I 𝓘(ℝ, E) ∞ hx
  exact hinc.comp 𝓘(ℝ, E) E hchart

end DifferentialGeometry.Geometry.Riemannian.VolumeComparison
