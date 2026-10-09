import DifferentialGeometry.Topology.Morse.EuclideanModelReverse
import DifferentialGeometry.Geometry.Thurston.EquivariantRoundMetricA5Closure
import DifferentialGeometry.Geometry.Metric.Sphere.Quotient.SimplyConnectedSpaceForm
import DifferentialGeometry.Geometry.Comparison.Synge.Even
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.TerminalSurfaceProductEuclidean

/-!
# A closed orientable surface with positive curvature is the sphere (SF3, orientable case)

Row SF3 of package SURF (`design-finite-surface-foundations-20261004.md` §C2), orientable case,
consumed by LFR17's positive branch. Let `Z` be a compact connected surface modelled on `𝓡 2`
with an orientation and a smooth metric `h` of positive scalar (equivalently Gaussian) curvature.

1. Synge in even dimension (`Geometry.synge_simplyConnected_of_even_dim`) makes `Z` simply
   connected (`simplyConnectedSpace_of_scalar_pos`).
2. Moving to `MorseModel 2` charts (`Topology.Morse.euclideanModelMorseModelChartedSpace`), the
   surface Ricci flow theorem `GC.Geometry.exists_isometryInvariant_roundMetric_proved` gives a
   metric of constant curvature `1`.
3. The simply connected space form theorem
   `Geometry.exists_isometry_round_sphere_of_constant_positive_sectional_curvature` gives a
   diffeomorphism onto the round `S²` (`nonempty_diffeomorph_sphere_of_simplyConnected_of_scalar_pos`).

No Gauss–Bonnet and no classification of surfaces is used.
-/

set_option autoImplicit false

noncomputable section

open DifferentialGeometry DifferentialGeometry.Geometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Topology.Morse
open scoped Manifold ContDiff

namespace DifferentialGeometry.Geometry.ClosedSurface

local notation "E2" => EuclideanSpace ℝ (Fin 2)
local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "MM2" => DifferentialGeometry.Topology.Morse.MorseModel 2

variable {Z : Type*} [TopologicalSpace Z] [ChartedSpace E2 Z] [IsManifold (𝓡 2) ∞ Z]
  [T2Space Z] [CompactSpace Z] [ConnectedSpace Z]

/-- **Synge for surfaces.** A compact connected oriented surface with a smooth metric of positive
scalar curvature is simply connected. -/
theorem simplyConnectedSpace_of_scalar_pos (o : ManifoldOrientation (𝓡 2) Z 2)
    (h : SmoothRiemannianMetric (𝓡 2) Z) (hscal : ∀ x, 0 < metricScalarAt h x) :
    SimplyConnectedSpace Z :=
  synge_simplyConnected_of_even_dim (n := 2) (by simp) le_rfl even_two h
    (Riemannian.hasPositiveSectionalCurvature_of_forall_metricScalarAt_pos_of_finrank_eq_two h
      (by simp) hscal)
    ⟨o.orientation, DifferentialGeometry.Topology.Manifold.isCompatibleOrientation_of_manifoldOrientation o⟩

/-- **Simply connected case.** A compact connected simply connected surface with a smooth metric of
positive scalar curvature is diffeomorphic to the round `S²`. -/
theorem nonempty_diffeomorph_sphere_of_simplyConnected_of_scalar_pos [SimplyConnectedSpace Z]
    (h : SmoothRiemannianMetric (𝓡 2) Z) (hscal : ∀ x, 0 < metricScalarAt h x) :
    Nonempty (Z ≃ₘ⟮𝓡 2, 𝓡 2⟯ Metric.sphere (0 : E3) 1) := by
  let _ := euclideanModelMorseModelChartedSpace 2 Z
  have := isManifold_euclideanModelMorseModel (n := 2) (M := Z)
  let Ψ : Z ≃ₘ⟮𝓘(ℝ, MM2), 𝓡 2⟯ Z := euclideanModelMorseModelDiffeomorph
  let h' : SmoothRiemannianMetric 𝓘(ℝ, MM2) Z := Diffeomorph.pullbackMetricCross h Ψ
  have hscal' : ∀ x, 0 < metricScalarAt h' x := fun x => by
    rw [DifferentialGeometry.CheegerGromovCompactness.metricScalar_cross h Ψ x]
    exact hscal _
  obtain ⟨h₁, hsec₁, -⟩ := GC.Geometry.exists_isometryInvariant_roundMetric_proved h' hscal'
  obtain ⟨Φ, -⟩ := exists_isometry_round_sphere_of_constant_positive_sectional_curvature
    (I := 𝓘(ℝ, MM2)) (M := Z) (n := 2) (by norm_num) (by simp) h₁ 1 one_pos hsec₁
  exact ⟨Ψ.symm.trans Φ⟩

/-- **SF3, orientable case.** A compact connected oriented surface with a smooth metric of positive
scalar curvature is diffeomorphic to the round `S²`. -/
theorem nonempty_diffeomorph_sphere_of_scalar_pos (o : ManifoldOrientation (𝓡 2) Z 2)
    (h : SmoothRiemannianMetric (𝓡 2) Z) (hscal : ∀ x, 0 < metricScalarAt h x) :
    Nonempty (Z ≃ₘ⟮𝓡 2, 𝓡 2⟯ Metric.sphere (0 : E3) 1) := by
  have := simplyConnectedSpace_of_scalar_pos o h hscal
  exact nonempty_diffeomorph_sphere_of_simplyConnected_of_scalar_pos h hscal

end DifferentialGeometry.Geometry.ClosedSurface
