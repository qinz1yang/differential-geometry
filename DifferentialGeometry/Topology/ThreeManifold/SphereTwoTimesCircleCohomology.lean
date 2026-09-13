import DifferentialGeometry.Topology.Homology.UniversalCoefficientsOneLinearEquiv
import DifferentialGeometry.Topology.Homology.SphereRank
import DifferentialGeometry.Topology.Homology.SphereTopHomology
import DifferentialGeometry.Topology.ThreeManifold.StandardFactors

noncomputable section

open CategoryTheory ContinuousMap Metric Module Set

universe u

namespace DifferentialGeometry.Topology

private instance sphereOnePathConnectedSpace :
    PathConnectedSpace (sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) :=
  unitSphere_pathConnected_of_finrank (E := EuclideanSpace ℝ (Fin 2)) (by simp)

theorem not_subsingleton_integralSingularCohomology_one_sphereTwoTimesCircle :
    ¬ Subsingleton (integralSingularCohomology 1 SphereTwoTimesCircle) := by
  intro hsub
  have hhom : Subsingleton (integralSingularHomology 1 SphereTwoTimesCircle →ₗ[ℤ] ℤ) :=
    @Function.Injective.subsingleton _ _
      (integralSingularCohomologyOneLinearEquiv SphereTwoTimesCircle).symm.toLinearMap
      (integralSingularCohomologyOneLinearEquiv SphereTwoTimesCircle).symm.injective hsub
  let d := integralSphereTopHomologyEquiv 0 (EuclideanSpace ℝ (Fin 2)) (by simp)
  let i : C(sphere (0 : EuclideanSpace ℝ (Fin 2)) 1, SphereTwoTimesCircle) :=
    ContinuousMap.prodMk (ContinuousMap.const _ sphereTwoNorth) (ContinuousMap.id _)
  let p : C(SphereTwoTimesCircle, sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) := ContinuousMap.snd
  let φ : integralSingularHomology 1 SphereTwoTimesCircle →ₗ[ℤ] ℤ :=
    d.toLinearMap.comp (integralSingularHomologyMap 1 p)
  have hp : p.comp i = ContinuousMap.id _ := by
    ext x
    rfl
  have happ : ∀ y, φ (integralSingularHomologyMap 1 i y) = d y := by
    intro y
    change d (integralSingularHomologyMap 1 p (integralSingularHomologyMap 1 i y)) = d y
    rw [← LinearMap.comp_apply, ← integralSingularHomologyMap_comp, hp,
      integralSingularHomologyMap_id]
    rfl
  have hzero : φ (integralSingularHomologyMap 1 i (d.symm 1)) = 0 := by
    rw [Subsingleton.elim φ 0]
    rfl
  have hone : φ (integralSingularHomologyMap 1 i (d.symm 1)) = 1 := by
    rw [happ (d.symm 1), LinearEquiv.apply_symm_apply]
  exact one_ne_zero (hone.symm.trans hzero)

end DifferentialGeometry.Topology
