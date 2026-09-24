import DifferentialGeometry.Topology.Homology.CochainCones
import DifferentialGeometry.Topology.Homology.HurewiczFrontier

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace DifferentialGeometry.Topology

variable {X : Type u} [TopologicalSpace X]

theorem subsingleton_integralSingularHomology_two_of_subsingleton_homotopyGroup_two
    [SimplyConnectedSpace X] (h : SphereHurewiczTwoCanonical X)
    (hpi : ∀ x : X, Subsingleton (HomotopyGroup (Fin 2) X x)) :
    Subsingleton (integralSingularHomology 2 X) := by
  refine ⟨fun a b => ?_⟩
  let x : X := Classical.choice (inferInstance : Nonempty X)
  have hb := (sphereHurewicz_two_isomorphism_of_canonical_generator h x
    (integralLiftedSphereGenerator 1) (integralLiftedSphereGenerator_isGenerator 1)).1
  obtain ⟨a', rfl⟩ := hb.2 a
  obtain ⟨b', rfl⟩ := hb.2 b
  exact congrArg (sphereHurewicz 1 x (integralLiftedSphereGenerator 1))
    (Subsingleton.elim a' b')

theorem subsingleton_integralSingularHomology_two_of_cohomology_one
    (e : integralSingularHomology 2 X ≅ integralSingularCohomology 1 X)
    [Subsingleton (integralSingularCohomology 1 X)] :
    Subsingleton (integralSingularHomology 2 X) := by
  refine ⟨fun a b => ?_⟩
  have hb : Function.Bijective
      (e.hom.hom : integralSingularHomology 2 X → integralSingularCohomology 1 X) :=
    (ConcreteCategory.isIso_iff_bijective e.hom).mp inferInstance
  exact hb.1 (Subsingleton.elim _ _)

theorem subsingleton_integralSingularHomology_two_of_poincareDual [SimplyConnectedSpace X]
    (e : integralSingularHomology 2 X ≅ integralSingularCohomology 1 X) :
    Subsingleton (integralSingularHomology 2 X) :=
  haveI : Subsingleton (integralSingularCohomology 1 X) :=
    integralSingularCohomology_one_subsingleton (X := X)
  subsingleton_integralSingularHomology_two_of_cohomology_one e

theorem subsingleton_integralSingularHomology_two_of_injective_cohomology_one
    [SimplyConnectedSpace X]
    (f : integralSingularHomology 2 X →ₗ[ℤ] integralSingularCohomology 1 X)
    (hf : Function.Injective f) :
    Subsingleton (integralSingularHomology 2 X) :=
  @Function.Injective.subsingleton _ _ f hf
    (integralSingularCohomology_one_subsingleton (X := X))

theorem subsingleton_integralSingularHomology_two_of_injective_intersection_pairing
    [SimplyConnectedSpace X]
    (β : integralSingularHomology 2 X →ₗ[ℤ] (integralSingularHomology 1 X →ₗ[ℤ] ℤ))
    (hβ : Function.Injective β) :
    Subsingleton (integralSingularHomology 2 X) :=
  haveI : Subsingleton (integralSingularHomology 1 X) :=
    integralSingularHomology_one_subsingleton (X := X)
  @Function.Injective.subsingleton _ _ β hβ inferInstance

end DifferentialGeometry.Topology
