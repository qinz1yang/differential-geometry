import Mathlib.Topology.Compactification.OnePoint.Basic
import DifferentialGeometry.Topology.Homology.CohomologyHomeomorphInvariance
import DifferentialGeometry.Topology.Homology.HomologyTwoFrontier
import DifferentialGeometry.Topology.Homology.SpherePuncture
import DifferentialGeometry.Topology.Homology.SphereHomologyVanishing
import DifferentialGeometry.Topology.Homology.SphereTopHomology
import DifferentialGeometry.Topology.FundamentalGroup.Sphere

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicTopology ContinuousMap Set
open scoped Topology

universe u

namespace DifferentialGeometry.Topology

abbrev integralCompactSupportCohomologyOne (X : Type u) [TopologicalSpace X] :
    ModuleCat.{u} ℤ :=
  integralSingularCohomology 1 (OnePoint X)

def noncompactPoincareDualityTwoOne (X : Type u) [TopologicalSpace X] : Prop :=
  Nonempty (integralSingularHomology 2 X ≅ integralCompactSupportCohomologyOne X)

variable {X : Type u} [TopologicalSpace X]

theorem noncompactPoincareDualityTwoOne_of_subsingleton
    [Subsingleton (integralSingularHomology 2 X)]
    [Subsingleton (integralCompactSupportCohomologyOne X)] :
    noncompactPoincareDualityTwoOne X := by
  refine ⟨?_⟩
  refine ⟨ModuleCat.ofHom 0, ModuleCat.ofHom 0, ?_, ?_⟩
  · apply ModuleCat.hom_ext
    ext x
    exact Subsingleton.elim _ _
  · apply ModuleCat.hom_ext
    ext x
    exact Subsingleton.elim _ _

theorem subsingleton_integralSingularHomology_two_of_noncompactPoincareDualityTwoOne
    (h : noncompactPoincareDualityTwoOne X)
    [Subsingleton (integralCompactSupportCohomologyOne X)] :
    Subsingleton (integralSingularHomology 2 X) := by
  refine ⟨fun a b => ?_⟩
  obtain ⟨e⟩ := h
  have hb : Function.Bijective
      (e.hom.hom : integralSingularHomology 2 X → integralCompactSupportCohomologyOne X) :=
    (ConcreteCategory.isIso_iff_bijective e.hom).mp inferInstance
  exact hb.1 (Subsingleton.elim _ _)

variable [T2Space X] [CompactSpace X]

noncomputable def compactSupportCohomologyComplSingletonHomeomorph (x : X) :
    OnePoint ({x}ᶜ : Set X) ≃ₜ X :=
  OnePoint.equivOfIsEmbeddingOfRangeEq x Subtype.val Topology.IsEmbedding.subtypeVal (by
    ext y
    simp only [Set.mem_range, Set.mem_compl_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨z, rfl⟩
      exact z.2
    · intro hy
      exact ⟨⟨y, hy⟩, rfl⟩)

theorem nonempty_linearEquiv_compactSupportCohomologyOne_compl_singleton (x : X) :
    Nonempty (integralCompactSupportCohomologyOne ({x}ᶜ : Set X) ≃ₗ[ℤ]
      integralSingularCohomology 1 X) :=
  ⟨integralSingularCohomologyEquivOfHomeomorph
    (compactSupportCohomologyComplSingletonHomeomorph x) 1⟩

theorem subsingleton_integralCompactSupportCohomologyOne_compl_singleton (x : X)
    [Subsingleton (integralSingularCohomology 1 X)] :
    Subsingleton (integralCompactSupportCohomologyOne ({x}ᶜ : Set X)) :=
  subsingleton_integralSingularCohomology_of_homeomorph
    (compactSupportCohomologyComplSingletonHomeomorph x).symm 1

theorem subsingleton_integralSingularHomology_two_compl_singleton_of_noncompactPoincareDuality
    (x : X) (h : noncompactPoincareDualityTwoOne ({x}ᶜ : Set X))
    [Subsingleton (integralSingularCohomology 1 X)] :
    Subsingleton (integralSingularHomology 2 ({x}ᶜ : Set X)) :=
  @subsingleton_integralSingularHomology_two_of_noncompactPoincareDualityTwoOne
    ({x}ᶜ : Set X) inferInstance h
    (subsingleton_integralCompactSupportCohomologyOne_compl_singleton x)

theorem subsingleton_integralSingularHomology_two_sphereThree_compl_singleton
    (v : SphereThree) :
    Subsingleton (integralSingularHomology 2 ({v}ᶜ : Set SphereThree)) := by
  exact @integralSingularHomology_subsingleton_of_contractible 2 (by norm_num)
    ({v}ᶜ : Set SphereThree) inferInstance (spherePuncture_contractible v)

theorem noncompactPoincareDualityTwoOne_sphereThree_compl_singleton (v : SphereThree) :
    noncompactPoincareDualityTwoOne ({v}ᶜ : Set SphereThree) :=
  @noncompactPoincareDualityTwoOne_of_subsingleton
    ({v}ᶜ : Set SphereThree) inferInstance
    (subsingleton_integralSingularHomology_two_sphereThree_compl_singleton v)
    (@subsingleton_integralCompactSupportCohomologyOne_compl_singleton SphereThree _ _ _ v
      (integralSingularCohomology_one_subsingleton (X := SphereThree)))

end DifferentialGeometry.Topology
