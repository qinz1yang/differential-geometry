import DifferentialGeometry.Topology.Homology.SphereGeneratorCriterion
import DifferentialGeometry.Topology.Homology.SphereHomologyVanishing
import DifferentialGeometry.Topology.Homology.Homotopy

noncomputable section

open CategoryTheory CategoryTheory.Limits Metric Module

universe u

namespace DifferentialGeometry.Topology

theorem not_isSphereHomologyGenerator_zero (n : ℕ) :
    ¬ IsSphereHomologyGenerator n
      (0 : integralSingularHomology (n + 1) (liftedHomotopySphere.{u} n)) := by
  intro h
  obtain ⟨φ, hφ⟩ := (isSphereHomologyGenerator_iff_exists_functional n 0).mp h
  exact (zero_ne_one : (0 : ℤ) ≠ 1) (by rw [map_zero] at hφ; exact hφ)

theorem exists_functional_integralLiftedSphereGenerator_eq_one (n : ℕ) :
    ∃ φ : integralSingularHomology (n + 1) (liftedHomotopySphere.{u} n) →ₗ[ℤ] ℤ,
      φ (integralLiftedSphereGenerator.{u} n) = 1 :=
  ⟨(integralLiftedSphereTopEquiv n).toLinearMap, integralLiftedSphereGenerator_coordinate n⟩

theorem bijective_zsmul_integralLiftedSphereGenerator (n : ℕ) :
    Function.Bijective (fun z : ℤ => z • integralLiftedSphereGenerator.{u} n) :=
  (isSphereHomologyGenerator_iff_bijective_zsmul n _).mp
    (integralLiftedSphereGenerator_isGenerator n)

theorem not_bijective_zsmul_zero_sphereGenerator (n : ℕ) :
    ¬ Function.Bijective
      (fun z : ℤ => z •
        (0 : integralSingularHomology (n + 1) (liftedHomotopySphere.{u} n))) :=
  fun h => not_isSphereHomologyGenerator_zero n
    ((isSphereHomologyGenerator_iff_bijective_zsmul n 0).mpr h)

theorem subsingleton_integralSingularHomology_two_threeSphere :
    Subsingleton (integralSingularHomology 2
      (sphere (0 : EuclideanSpace ℝ (Fin 4)) 1)) :=
  integralSphereHomology_subsingleton 3 2 (EuclideanSpace ℝ (Fin 4))
    (by simp) (by norm_num) (by norm_num)

theorem subsingleton_integralSingularHomology_two_liftedHomotopySphere_two :
    Subsingleton (integralSingularHomology 2 (liftedHomotopySphere.{u} 2)) := by
  have h : Subsingleton (integralSingularHomology 2
      (sphere (0 : liftedSphereSpace.{u} 2) 1)) :=
    integralSphereHomology_subsingleton 3 2 (liftedSphereSpace.{u} 2)
      (liftedSphereSpace_finrank 2) (by norm_num) (by norm_num)
  exact ⟨fun a b => (integralSingularHomologyHomotopyEquiv 2
    (liftedSphereHomeomorph.{u} 2).toHomotopyEquiv).injective
      (h.allEq _ _)⟩

theorem not_subsingleton_integralSingularHomology_two_twoSphere :
    ¬ Subsingleton (integralSingularHomology 2
      (sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)) := by
  intro h
  let e := integralSphereTopHomologyEquiv 1 (EuclideanSpace ℝ (Fin 3)) (by simp)
  have : Subsingleton ℤ :=
    ⟨fun a b => e.symm.injective (h.allEq (e.symm a) (e.symm b))⟩
  exact (zero_ne_one : (0 : ℤ) ≠ 1) (this.allEq 0 1)

end DifferentialGeometry.Topology
