import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.NoncompactShrinkerCover

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Bundle
open DifferentialGeometry.Geometry
open DifferentialGeometry.Geometry.Riemannian.Topology
open scoped Manifold ContDiff

local notation "SphereTwo" => Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1
local notation "Cylinder" => SphereTwo × ℝ
local notation "CylinderI" => ModelWithCorners.prod (𝓡 2) 𝓘(ℝ, ℝ)

local instance cylinderClassificationModelSphereDimension :
    Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) := ⟨by simp⟩

local instance cylinderClassificationModelOne : IsManifold CylinderI 1 Cylinder :=
  IsManifold.of_le (n := ∞) (by decide)

local instance cylinderClassificationModelLocallyPathConnected :
    LocallyPathConnectedSpace Cylinder :=
  DifferentialGeometry.Topology.Manifold.locallyPathConnectedSpace_of_modelWithCorners CylinderI

local instance cylinderClassificationModelSemilocallySimplyConnected :
    SemilocallySimplyConnectedSpace Cylinder :=
  manifold_semilocallySimplyConnectedSpace (I := CylinderI) (M := Cylinder)

local instance cylinderClassificationModelInhabited : Inhabited Cylinder :=
  ⟨(sphereEquator 0, 0)⟩

private theorem scaleMetric_one_roundThreeCylinder :
    scaleMetric (1 : ℝ) (by norm_num) roundThreeCylinderShrinkerMetric =
      roundThreeCylinderShrinkerMetric := by
  apply SmoothRiemannianMetric.ext_inner
  intro x v w
  rw [scaleMetric_inner, one_mul]

theorem noncompactShrinkerCylinderClassification_roundThreeCylinder :
    NoncompactShrinkerCylinderClassification (I := CylinderI) (M := Cylinder)
      roundThreeCylinderShrinkerMetric roundThreeCylinderShrinkerPotential 1 := by
  obtain ⟨Psi, hproj, hmetric, -⟩ :=
    exists_universalCover_cylinder_isometry_of_solitonModelCovering
      (I := CylinderI) (M := Cylinder) (sigma := 1) (by norm_num)
      (g := roundThreeCylinderShrinkerMetric) (f := roundThreeCylinderShrinkerPotential)
      (cover := id)
      (by
        rw [scaleMetric_one_roundThreeCylinder]
        exact solitonModelCovering_refl normalizedGradientRicciSoliton_roundThreeCylinder)
  refine ⟨0, Psi, hmetric, ?_⟩
  intro x s
  rw [hproj x s]
  simp only [id_eq, Real.sqrt_one, one_mul, zero_div, add_zero,
    roundThreeCylinderShrinkerPotential_apply]

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
