import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CubeSphereGenerator
import DifferentialGeometry.Topology.Homology.HurewiczBijectionFrontier
import DifferentialGeometry.Topology.Homology.IntegralReducedCoefficientBridge

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicTopology ContinuousMap Set Module
open scoped Topology
open DifferentialGeometry.Homology
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

namespace DifferentialGeometry.Topology

def liftedSphereMap (n : ℕ) :
    C(liftedHomotopySphere.{u} n, Metric.sphere (0 : liftedSphereSpace.{u} n) 1) :=
  ⟨liftedSphereHomeomorph n, (liftedSphereHomeomorph n).continuous⟩

def euclideanToLiftedSphereMap :
    C(Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1,
      Metric.sphere (0 : liftedSphereSpace.{u} 2) 1) :=
  let e : Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1 ≃ₜ
      Metric.sphere (0 : liftedSphereSpace.{u} 2) 1 :=
    Homeomorph.ulift.symm.trans (liftedSphereHomeomorph 2)
  ⟨e, e.continuous⟩

theorem euclideanToLiftedSphereMap_apply
    (z : Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1) :
    euclideanToLiftedSphereMap.{u} z = liftedSphereHomeomorph 2 (ULift.up z) :=
  rfl

def cubeSphereUnliftedLoop :
    GenLoop (Fin 3) (Metric.sphere (0 : liftedSphereSpace.{u} 2) 1)
      (liftedSphereMap.{u} 2 (ULift.up (cubeSphereBasepoint 2))) :=
  DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.genLoopPostcompose (liftedSphereMap.{u} 2)
    (cubeSphereCollapse.{u} 2)

theorem cubeSphereUnliftedLoop_apply (t : Fin 3 → unitInterval) :
    cubeSphereUnliftedLoop.{u} t = euclideanToLiftedSphereMap.{u} (cubeSphereProjection 2 t) :=
  rfl

theorem hurewiczCubeClass_cubeSphereUnliftedLoop :
    hurewiczCubeClass cubeSphereUnliftedLoop.{u} =
      integralHomologyMap 3 (liftedSphereMap.{u} 2) cubeSphereFundamentalClass.{u} :=
  hurewiczCubeClass_natural (liftedSphereMap.{u} 2) (cubeSphereCollapse.{u} 2)

theorem integralLiftedSphereTopEquiv_cubeSphereFundamentalClass :
    integralLiftedSphereTopEquiv.{u} 2 cubeSphereFundamentalClass.{u} =
      integralSphereTopHomologyEquiv 2 (liftedSphereSpace.{u} 2)
        (liftedSphereSpace_finrank 2) (hurewiczCubeClass cubeSphereUnliftedLoop.{u}) := by
  rw [integralLiftedSphereTopEquiv, LinearEquiv.trans_apply]
  refine congrArg (integralSphereTopHomologyEquiv 2 (liftedSphereSpace.{u} 2)
    (liftedSphereSpace_finrank 2)) ?_
  exact (hurewiczCubeClass_cubeSphereUnliftedLoop.{u}).symm

theorem genLoopSphereHomeomorph_cubeSphereUnliftedLoop_val :
    (genLoopSphereHomeomorph 2 (liftedSphereMap.{u} 2 (ULift.up (cubeSphereBasepoint 2)))
      cubeSphereUnliftedLoop.{u}).val = euclideanToLiftedSphereMap.{u} := by
  refine ContinuousMap.ext fun z => ?_
  obtain ⟨t, rfl⟩ := cubeSphereProjection_surjective 2 z
  rw [genLoopSphereHomeomorph_projection]
  exact cubeSphereUnliftedLoop_apply.{u} t

theorem isSphereHomologyGenerator_cubeSphereFundamentalClass_iff_isUnit :
    IsSphereHomologyGenerator.{u} 2 cubeSphereFundamentalClass.{u} ↔
      IsUnit (integralLiftedSphereTopEquiv.{u} 2 cubeSphereFundamentalClass.{u}) := by
  rw [isSphereHomologyGenerator_cubeSphereFundamentalClass_iff_coordinate]
  constructor
  · rintro (h | h)
    · rw [h]
      exact isUnit_one
    · rw [h]
      exact Int.isUnit_iff.mpr (Or.inr rfl)
  · intro h
    rcases Int.isUnit_iff.mp h with h | h
    · exact Or.inl h
    · exact Or.inr h

def liftedSphereReducedHomologyEquivThree :
    reducedSingularHomology (ModuleCat.of ℤ ℤ)
        (TopCat.of (liftedHomotopySphere.{0} 2)) 3 ≃ₗ[ℤ] ℤ :=
  (reducedSingularHomologyIso (ModuleCat.of ℤ ℤ)
      (Homeomorph.ulift.toHomotopyEquiv) 3).toLinearEquiv.trans
    (AddEquiv.toIntLinearEquiv
      (DifferentialGeometry.LocalDegree.euclideanSphereTopReducedHomologyEquiv 3))

def cubeSphereReducedDegreeCoordinate :
    integralSingularHomology 3 (liftedHomotopySphere.{0} 2) ≃ₗ[ℤ] ℤ :=
  (integralReducedSingularHomologyEquiv 2 (liftedHomotopySphere.{0} 2)).trans
    liftedSphereReducedHomologyEquivThree

theorem isSphereHomologyGenerator_cubeSphereFundamentalClass_iff_reducedDegreeCoordinate_isUnit :
    IsSphereHomologyGenerator.{0} 2 cubeSphereFundamentalClass.{0} ↔
      IsUnit (cubeSphereReducedDegreeCoordinate cubeSphereFundamentalClass.{0}) := by
  rw [isSphereHomologyGenerator_cubeSphereFundamentalClass_iff_isUnit]
  exact (isUnit_apply_iff_isUnit_apply_of_linearEquiv cubeSphereReducedDegreeCoordinate
    (integralLiftedSphereTopEquiv.{0} 2) cubeSphereFundamentalClass.{0}).symm

theorem isSphereHomologyGenerator_cubeSphereFundamentalClass_iff_unliftedCoordinate_isUnit :
    IsSphereHomologyGenerator.{u} 2 cubeSphereFundamentalClass.{u} ↔
      IsUnit (integralSphereTopHomologyEquiv 2 (liftedSphereSpace.{u} 2)
        (liftedSphereSpace_finrank 2) (hurewiczCubeClass cubeSphereUnliftedLoop.{u})) := by
  rw [isSphereHomologyGenerator_cubeSphereFundamentalClass_iff_isUnit,
    integralLiftedSphereTopEquiv_cubeSphereFundamentalClass]

theorem cubeSphereFundamentalClass_ne_zero_of_reducedDegreeCoordinate_isUnit
    (h : IsUnit (cubeSphereReducedDegreeCoordinate cubeSphereFundamentalClass.{0})) :
    cubeSphereFundamentalClass.{0} ≠ 0 := by
  intro hzero
  rw [hzero, map_zero] at h
  exact not_isUnit_zero h

theorem not_exists_linearMap_eq_one_integralRelativeHomology_three_singleton_cube
    (b : Fin 3 → unitInterval)
    (z : integralRelativeHomology 3 ({b} : Set (Fin 3 → unitInterval))) :
    ¬ ∃ φ : integralRelativeHomology 3 ({b} : Set (Fin 3 → unitInterval)) →ₗ[ℤ] ℤ, φ z = 1 :=
  not_exists_linearMap_eq_one_of_subsingleton
    (subsingleton_integralRelativeHomology_three_singleton_cube b) z

theorem exists_relative_functional_liftedSphereGenerator_two :
    ∃ ψ : integralRelativeHomology 3
        ({ULift.up (cubeSphereBasepoint 2)} : Set (liftedHomotopySphere.{0} 2)) →ₗ[ℤ] ℤ,
      ψ (integralAbsoluteToRelative 3
        ({ULift.up (cubeSphereBasepoint 2)} : Set (liftedHomotopySphere.{0} 2))
        (integralLiftedSphereGenerator.{0} 2)) = 1 :=
  exists_relative_functional_integralLiftedSphereGenerator 2 (by norm_num)
    (ULift.up (cubeSphereBasepoint 2))

variable {X : Type u} [TopologicalSpace X]

theorem hurewiczThreeMultiplicative_of_cubeSphereFundamentalClass_isSphereHomologyGenerator
    (hg : IsSphereHomologyGenerator.{u} 2 cubeSphereFundamentalClass.{u}) :
    HurewiczThreeMultiplicative X :=
  fun x _ c hc a b =>
    sphereHurewicz_mul_of_cubeSphereFundamentalClass_isSphereHomologyGenerator hg x c hc a b

end DifferentialGeometry.Topology
