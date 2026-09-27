import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.EuclideanSimplexGeneratorCriterion
import DifferentialGeometry.Topology.Homology.SphereGeneratorCriterion

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicTopology ContinuousMap Set Module
open scoped Simplicial Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

theorem euclideanStandardSimplexClass_generator_iff_exists_boundary_functional_eq_one :
    Function.Bijective (fun z : ℤ => z • euclideanStandardSimplexClass.{u}) ↔
      ∃ ψ : DifferentialGeometry.Topology.integralSingularHomology 2
          ({(0 : DifferentialGeometry.Topology.liftedSphereSpace.{u} 1)}ᶜ :
            Set (DifferentialGeometry.Topology.liftedSphereSpace.{u} 1)) →ₗ[ℤ] ℤ,
        ψ euclideanStandardSimplexBoundaryClass.{u} = 1 := by
  constructor
  · intro h
    have hU : IsUnit
        ((DifferentialGeometry.Topology.integralPuncturedSpaceSphereHomologyEquiv
            (DifferentialGeometry.Topology.liftedSphereSpace.{u} 1) 2).trans
          (DifferentialGeometry.Topology.integralSphereTopHomologyEquiv 1
            (DifferentialGeometry.Topology.liftedSphereSpace.{u} 1)
            (DifferentialGeometry.Topology.liftedSphereSpace_finrank 1))
          euclideanStandardSimplexBoundaryClass.{u}) :=
      (euclideanStandardSimplexClass_generator_iff_isUnit_boundaryClass).mp h
    obtain ⟨φ, -, hφ⟩ :=
      (isUnit_apply_iff_exists_surjective_functional
        ((DifferentialGeometry.Topology.integralPuncturedSpaceSphereHomologyEquiv
            (DifferentialGeometry.Topology.liftedSphereSpace.{u} 1) 2).trans
          (DifferentialGeometry.Topology.integralSphereTopHomologyEquiv 1
            (DifferentialGeometry.Topology.liftedSphereSpace.{u} 1)
            (DifferentialGeometry.Topology.liftedSphereSpace_finrank 1)))
        euclideanStandardSimplexBoundaryClass.{u}).mp hU
    exact ⟨φ, hφ⟩
  · rintro ⟨ψ, hψ⟩
    exact euclideanStandardSimplexClass_generator_of_boundaryClass_functional_eq_one ψ hψ

theorem euclideanStandardSimplexClass_generator_iff_puncturedBoundaryClass_generator :
    Function.Bijective (fun z : ℤ => z • euclideanStandardSimplexClass.{u}) ↔
      Function.Bijective (fun z : ℤ => z •
        DifferentialGeometry.Topology.integralPuncturedSpaceSphereHomologyEquiv
          (DifferentialGeometry.Topology.liftedSphereSpace.{u} 1) 2
          euclideanStandardSimplexBoundaryClass.{u}) :=
  (euclideanStandardSimplexClass_generator_iff_isUnit_boundaryClass).trans
    (isUnit_apply_iff_bijective_zsmul
      (DifferentialGeometry.Topology.integralSphereTopHomologyEquiv 1
        (DifferentialGeometry.Topology.liftedSphereSpace.{u} 1)
        (DifferentialGeometry.Topology.liftedSphereSpace_finrank 1))
      (DifferentialGeometry.Topology.integralPuncturedSpaceSphereHomologyEquiv
        (DifferentialGeometry.Topology.liftedSphereSpace.{u} 1) 2
        euclideanStandardSimplexBoundaryClass.{u}))

def euclideanStandardSimplexBoundarySphereClass :
    DifferentialGeometry.Topology.integralSingularHomology 2
      (DifferentialGeometry.Topology.liftedHomotopySphere.{u} 1) :=
  (DifferentialGeometry.Topology.integralSingularHomologyHomotopyEquiv 2
      (DifferentialGeometry.Topology.liftedSphereHomeomorph.{u} 1).toHomotopyEquiv).symm
    (DifferentialGeometry.Topology.integralPuncturedSpaceSphereHomologyEquiv
      (DifferentialGeometry.Topology.liftedSphereSpace.{u} 1) 2
      euclideanStandardSimplexBoundaryClass.{u})

theorem euclideanStandardSimplexClass_generator_iff_isSphereHomologyGenerator :
    Function.Bijective (fun z : ℤ => z • euclideanStandardSimplexClass.{u}) ↔
      DifferentialGeometry.Topology.IsSphereHomologyGenerator.{u} 1
        euclideanStandardSimplexBoundarySphereClass.{u} := by
  rw [DifferentialGeometry.Topology.isSphereHomologyGenerator_iff_bijective_zsmul]
  have hdef : euclideanStandardSimplexBoundarySphereClass.{u} =
      (DifferentialGeometry.Topology.integralSingularHomologyHomotopyEquiv 2
        (DifferentialGeometry.Topology.liftedSphereHomeomorph.{u} 1).toHomotopyEquiv).symm
        (DifferentialGeometry.Topology.integralPuncturedSpaceSphereHomologyEquiv
          (DifferentialGeometry.Topology.liftedSphereSpace.{u} 1) 2
          euclideanStandardSimplexBoundaryClass.{u}) := rfl
  rw [hdef]
  exact (euclideanStandardSimplexClass_generator_iff_puncturedBoundaryClass_generator).trans
    (bijective_zsmul_iff_of_linearEquiv
      (DifferentialGeometry.Topology.integralSingularHomologyHomotopyEquiv 2
        (DifferentialGeometry.Topology.liftedSphereHomeomorph.{u} 1).toHomotopyEquiv).symm
      (DifferentialGeometry.Topology.integralPuncturedSpaceSphereHomologyEquiv
        (DifferentialGeometry.Topology.liftedSphereSpace.{u} 1) 2
        euclideanStandardSimplexBoundaryClass.{u})).symm

variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold ThreeModel ∞ M]

theorem exists_unique_fundamentalClass_iff_exists_and_injective_localization
    (o : TangentOrientationSection M) :
    (∃! z : IntegralHomology M 3, ∀ x : M,
        absoluteToRelative M ({x}ᶜ) 3 z = localOrientationClass o x) ↔
      (∃ z : IntegralHomology M 3, ∀ x : M,
        absoluteToRelative M ({x}ᶜ) 3 z = localOrientationClass o x) ∧
      Function.Injective (fun w : IntegralHomology M 3 =>
        fun x : M => absoluteToRelative M ({x}ᶜ) 3 w) := by
  constructor
  · rintro ⟨z, hz, huniq⟩
    refine ⟨⟨z, hz⟩, ?_⟩
    intro w w' hww
    have hdiff : ∀ x : M, absoluteToRelative M ({x}ᶜ) 3 (w - w') = 0 := by
      intro x
      have hx : absoluteToRelative M ({x}ᶜ) 3 w = absoluteToRelative M ({x}ᶜ) 3 w' :=
        congrFun hww x
      rw [map_sub, hx, sub_self]
    have hzw : ∀ x : M,
        absoluteToRelative M ({x}ᶜ) 3 (z + (w - w')) = localOrientationClass o x := by
      intro x
      rw [map_add, hdiff x, add_zero, hz x]
    have h1 : z + (w - w') = z := huniq _ hzw
    have h0 : w - w' = 0 := by
      have h2 := congrArg (fun t : IntegralHomology M 3 => t - z) h1
      simpa using h2
    exact sub_eq_zero.mp h0
  · rintro ⟨⟨z, hz⟩, hinj⟩
    exact ⟨z, hz, fun z' hz' => hinj (funext fun x => by
      change absoluteToRelative M ({x}ᶜ) 3 z' = absoluteToRelative M ({x}ᶜ) 3 z
      rw [hz' x, hz x])⟩

theorem bijective_zsmul_of_forall_absoluteToRelative_eq_and_injective
    (o : TangentOrientationSection M) (x : M) (z : IntegralHomology M 3)
    (hz : ∀ y : M, absoluteToRelative M ({y}ᶜ) 3 z = localOrientationClass o y)
    (hlocal : Function.Bijective (fun k : ℤ => k • localOrientationClass o x))
    (hinj : Function.Injective (absoluteToRelative M ({x}ᶜ) 3)) :
    Function.Bijective (fun k : ℤ => k • z) := by
  constructor
  · intro a b hab
    apply hlocal.1
    have h := congrArg (absoluteToRelative M ({x}ᶜ) 3) hab
    simpa only [map_zsmul, hz x] using h
  · intro w
    obtain ⟨k, hk⟩ := hlocal.2 (absoluteToRelative M ({x}ᶜ) 3 w)
    refine ⟨k, hinj ?_⟩
    rw [map_zsmul, hz x]
    exact hk

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
