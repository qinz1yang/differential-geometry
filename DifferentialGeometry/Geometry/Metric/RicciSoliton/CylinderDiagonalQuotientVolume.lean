import DifferentialGeometry.Analysis.Integration.Measure.Riemannian.Covering
import DifferentialGeometry.Geometry.Metric.RicciSoliton.CylinderQuotients

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set MeasureTheory
open scoped Manifold ContDiff ENNReal Topology
open DifferentialGeometry.Integral.Measure
  (riemannianVolumeMeasure_map_eq_natCast_smul_of_localPullMetric)

namespace DifferentialGeometry.Geometry

local notation "Cylinder" => Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 × ℝ
local notation "CylinderI" => ModelWithCorners.prod (𝓡 2) 𝓘(ℝ, ℝ)

section

private local instance cylinderMeasurableSpace : MeasurableSpace Cylinder := borel Cylinder
private local instance cylinderBorelSpace : BorelSpace Cylinder := ⟨rfl⟩
private local instance quotientMeasurableSpace : MeasurableSpace CylinderDiagonalQuotient :=
  borel CylinderDiagonalQuotient
private local instance quotientBorelSpace : BorelSpace CylinderDiagonalQuotient := ⟨rfl⟩

private theorem encard_cylinderDiagonalQuotientMap_fiber (y : CylinderDiagonalQuotient) :
    {x : Cylinder | cylinderDiagonalQuotientMap x = y}.encard = (2 : ℕ∞) := by
  classical
  revert y
  refine Quotient.ind (motive := fun y : CylinderDiagonalQuotient =>
    {x : Cylinder | cylinderDiagonalQuotientMap x = y}.encard = (2 : ℕ∞)) fun x₀ => ?_
  have hfix : x₀ ≠ cylinderDiagonalDiffeomorph x₀ := by
    intro h
    exact cylinderDiagonalDiffeomorph_fixed_point_free x₀ h.symm
  have hset : {x : Cylinder | cylinderDiagonalQuotientMap x =
      cylinderDiagonalQuotientMap x₀} = {x₀, cylinderDiagonalDiffeomorph x₀} := by
    ext x
    rw [Set.mem_ofPred_eq, cylinderDiagonalQuotientMap_eq_iff]
    exact ⟨fun h => h, fun h => h⟩
  change {x : Cylinder | cylinderDiagonalQuotientMap x =
    cylinderDiagonalQuotientMap x₀}.encard = (2 : ℕ∞)
  rw [hset, Set.encard_insert_of_notMem (by simpa using hfix),
    Set.encard_singleton]
  norm_num

theorem map_cylinderDiagonalQuotientMap_riemannianVolumeMeasure :
    Measure.map cylinderDiagonalQuotientMap
        (DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure
          (I := CylinderI) (M := Cylinder)
          roundThreeCylinderShrinkerMetric) =
      (2 : ENNReal) •
        DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure
          (I := CylinderI) (M := CylinderDiagonalQuotient) cylinderDiagonalQuotientMetric :=
  riemannianVolumeMeasure_map_eq_natCast_smul_of_localPullMetric
    (I := CylinderI) (M := Cylinder) (N := CylinderDiagonalQuotient)
    roundThreeCylinderShrinkerMetric cylinderDiagonalQuotientMetric
    cylinderDiagonalQuotientMap_isLocalDiffeomorph
    localPullMetric_cylinderDiagonalQuotientMetric 2 encard_cylinderDiagonalQuotientMap_fiber

end

end DifferentialGeometry.Geometry
