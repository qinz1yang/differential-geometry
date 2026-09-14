import DifferentialGeometry.Topology.Homology.LiftedSphereRelativeBridge
import DifferentialGeometry.Topology.Homology.IntegralReducedCoefficientBridge

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicTopology ContinuousMap Set Module
open scoped Topology

namespace DifferentialGeometry.Topology

noncomputable def integralRelativeHomologySingletonReducedEquiv (X : Type) [TopologicalSpace X]
    (b : X) (n : ℕ) (hn : 1 < n + 1) :
    integralRelativeHomology (n + 1) ({b} : Set X) ≃ₗ[ℤ]
      DifferentialGeometry.Homology.reducedSingularHomology (ModuleCat.of ℤ ℤ) (TopCat.of X)
        (n + 1) :=
  (LinearEquiv.ofBijective (integralAbsoluteToRelative (n + 1) ({b} : Set X))
    (integralAbsoluteToRelative_singleton_bijective b (n := n + 1) hn)).symm.trans
  (integralReducedSingularHomologyEquiv n X)

theorem integralRelativeHomologySingletonReducedEquiv_symm_apply
    (X : Type) [TopologicalSpace X] (b : X) (n : ℕ) (hn : 1 < n + 1)
    (c : DifferentialGeometry.Homology.reducedSingularHomology (ModuleCat.of ℤ ℤ) (TopCat.of X)
      (n + 1)) :
    (integralRelativeHomologySingletonReducedEquiv X b n hn).symm c =
      integralAbsoluteToRelative (n + 1) ({b} : Set X)
        ((integralReducedSingularHomologyEquiv n X).symm c) :=
  by simp [integralRelativeHomologySingletonReducedEquiv]

theorem integralRelativeHomologySingletonReducedEquiv_apply_absoluteToRelative
    (X : Type) [TopologicalSpace X] (b : X) (n : ℕ) (hn : 1 < n + 1)
    (c : integralSingularHomology (n + 1) X) :
    integralRelativeHomologySingletonReducedEquiv X b n hn
        (integralAbsoluteToRelative (n + 1) ({b} : Set X) c) =
      integralReducedSingularHomologyEquiv n X c :=
  by simp [integralRelativeHomologySingletonReducedEquiv]

theorem not_subsingleton_integralRelativeHomology_singleton_liftedSphere
    (b : liftedHomotopySphere.{0} 1) :
    ¬ Subsingleton (integralRelativeHomology 2 ({b} : Set (liftedHomotopySphere.{0} 1))) := by
  intro h
  obtain ⟨ψ, hψ⟩ := exists_relative_functional_integralLiftedSphereGenerator 1 (by norm_num) b
  rw [@Subsingleton.elim _ h
    (integralAbsoluteToRelative 2 ({b} : Set (liftedHomotopySphere.{0} 1))
      (integralLiftedSphereGenerator.{0} 1)) 0, map_zero] at hψ
  exact zero_ne_one hψ

theorem not_subsingleton_reducedSingularHomology_liftedSphere (b : liftedHomotopySphere.{0} 1) :
    ¬ Subsingleton
      (DifferentialGeometry.Homology.reducedSingularHomology (ModuleCat.of ℤ ℤ)
        (TopCat.of (liftedHomotopySphere.{0} 1)) 2) := by
  intro h
  refine not_subsingleton_integralRelativeHomology_singleton_liftedSphere b ?_
  refine ⟨fun x y => ?_⟩
  exact (integralRelativeHomologySingletonReducedEquiv (liftedHomotopySphere.{0} 1) b 1
      (by norm_num)).injective
    (@Subsingleton.elim _ h
      (integralRelativeHomologySingletonReducedEquiv (liftedHomotopySphere.{0} 1) b 1
        (by norm_num) x)
      (integralRelativeHomologySingletonReducedEquiv (liftedHomotopySphere.{0} 1) b 1
        (by norm_num) y))

end DifferentialGeometry.Topology
