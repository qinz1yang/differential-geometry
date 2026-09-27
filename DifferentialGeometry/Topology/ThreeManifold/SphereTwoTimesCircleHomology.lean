import DifferentialGeometry.Topology.Homology.SphereGenerator
import DifferentialGeometry.Topology.ThreeManifold.StandardFactors

noncomputable section

open ContinuousMap Metric

namespace DifferentialGeometry.Topology

theorem not_subsingleton_integralSingularHomology_two_sphereTwoTimesCircle :
    ¬ Subsingleton (integralSingularHomology 2 SphereTwoTimesCircle) := by
  intro hsub
  let e := integralSphereTopHomologyEquiv 1 (EuclideanSpace ℝ (Fin 3)) (by simp)
  let c : integralSingularHomology 2 (sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) := e.symm 1
  have hc : c ≠ 0 := by
    intro hc0
    have h2 : e c = e 0 := congrArg e hc0
    rw [map_zero] at h2
    simp only [c, LinearEquiv.apply_symm_apply] at h2
    exact one_ne_zero h2
  let pt : sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 :=
    unitSpherePointOfFinrankPos (E := EuclideanSpace ℝ (Fin 2)) (by simp)
  let i : C(sphere (0 : EuclideanSpace ℝ (Fin 3)) 1, SphereTwoTimesCircle) :=
    (ContinuousMap.id _).prodMk (ContinuousMap.const _ pt)
  have hcomp : (ContinuousMap.fst : C(SphereTwoTimesCircle,
      sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)).comp i = ContinuousMap.id _ := by
    ext x
    rfl
  have hmap : integralSingularHomologyMap 2
      (ContinuousMap.fst : C(SphereTwoTimesCircle,
        sphere (0 : EuclideanSpace ℝ (Fin 3)) 1))
      (integralSingularHomologyMap 2 i c) = c := by
    rw [← LinearMap.comp_apply, ← integralSingularHomologyMap_comp, hcomp,
      integralSingularHomologyMap_id]
    rfl
  have hzero : integralSingularHomologyMap 2 i c = 0 := Subsingleton.elim _ _
  rw [hzero, map_zero] at hmap
  exact hc hmap.symm

end DifferentialGeometry.Topology
