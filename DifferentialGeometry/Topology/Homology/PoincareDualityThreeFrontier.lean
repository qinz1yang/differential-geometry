import DifferentialGeometry.Topology.Homology.HomologyTwoFrontier
import DifferentialGeometry.Topology.Homology.RadialHomotopy
import DifferentialGeometry.Topology.Homology.SphereHomologyVanishing
import DifferentialGeometry.Topology.Homology.SphereTopHomology
import DifferentialGeometry.Topology.Homology.UniversalCoefficientsOneLinearEquiv
import DifferentialGeometry.Topology.FundamentalGroup.Sphere

noncomputable section

open CategoryTheory CategoryTheory.Limits Metric Module Set

universe u

namespace DifferentialGeometry.Topology

variable {X : Type u} [TopologicalSpace X]

def poincareDualityTwoOne (X : Type u) [TopologicalSpace X] : Prop :=
  Nonempty (integralSingularHomology 2 X ≅ integralSingularCohomology 1 X)

theorem poincareDualityTwoOne_of_subsingleton
    [Subsingleton (integralSingularHomology 2 X)]
    [Subsingleton (integralSingularCohomology 1 X)] :
    poincareDualityTwoOne X := by
  refine ⟨?_⟩
  refine ⟨ModuleCat.ofHom 0, ModuleCat.ofHom 0, ?_, ?_⟩
  · apply ModuleCat.hom_ext
    ext x
    exact Subsingleton.elim _ _
  · apply ModuleCat.hom_ext
    ext x
    exact Subsingleton.elim _ _

theorem subsingleton_integralSingularHomology_two_of_poincareDualityTwoOne
    (h : poincareDualityTwoOne X) [Subsingleton (integralSingularCohomology 1 X)] :
    Subsingleton (integralSingularHomology 2 X) :=
  h.elim fun e => subsingleton_integralSingularHomology_two_of_cohomology_one e

theorem subsingleton_integralSingularHomology_two_of_poincareDualityTwoOne_of_simplyConnected
    (h : poincareDualityTwoOne X) [SimplyConnectedSpace X] :
    Subsingleton (integralSingularHomology 2 X) :=
  haveI : Subsingleton (integralSingularCohomology 1 X) :=
    integralSingularCohomology_one_subsingleton (X := X)
  subsingleton_integralSingularHomology_two_of_poincareDualityTwoOne h

theorem subsingleton_integralSingularHomology_two_of_poincareDualityTwoOne_of_subsingleton_dual
    [PathConnectedSpace X] (h : poincareDualityTwoOne X)
    (hd : Subsingleton (integralSingularHomology 1 X →ₗ[ℤ] ℤ)) :
    Subsingleton (integralSingularHomology 2 X) :=
  haveI : Subsingleton (integralSingularCohomology 1 X) :=
    @Function.Injective.subsingleton _ _
      (integralSingularCohomologyOneLinearEquiv X).toLinearMap
      (integralSingularCohomologyOneLinearEquiv X).injective hd
  subsingleton_integralSingularHomology_two_of_poincareDualityTwoOne h

theorem nonempty_linearEquiv_homologyTwo_homologyOneDual_of_poincareDualityTwoOne
    [PathConnectedSpace X] (h : poincareDualityTwoOne X) :
    Nonempty (integralSingularHomology 2 X ≃ₗ[ℤ] (integralSingularHomology 1 X →ₗ[ℤ] ℤ)) :=
  h.elim fun e =>
    ⟨(LinearEquiv.ofBijective e.hom.hom
        ((ConcreteCategory.isIso_iff_bijective e.hom).mp inferInstance)).trans
      (integralSingularCohomologyOneLinearEquiv X)⟩

theorem subsingleton_integralSingularHomology_two_sphereThree :
    Subsingleton (integralSingularHomology 2 SphereThree) :=
  integralSphereHomology_subsingleton 3 2 (EuclideanSpace ℝ (Fin 4)) (by simp) (by norm_num)
    (by norm_num)

theorem poincareDualityTwoOne_sphereThree : poincareDualityTwoOne SphereThree :=
  haveI : Subsingleton (integralSingularHomology 2 SphereThree) :=
    subsingleton_integralSingularHomology_two_sphereThree
  haveI : Subsingleton (integralSingularCohomology 1 SphereThree) :=
    integralSingularCohomology_one_subsingleton (X := SphereThree)
  poincareDualityTwoOne_of_subsingleton

theorem not_poincareDualityTwoOne_sphereTwo : ¬ poincareDualityTwoOne SphereTwo := by
  rintro ⟨e⟩
  let d := integralSphereTopHomologyEquiv 1 (EuclideanSpace ℝ (Fin 3)) (by simp)
  have hZ : Subsingleton ℤ :=
    haveI : Subsingleton (integralSingularCohomology 1 SphereTwo) :=
      integralSingularCohomology_one_subsingleton (X := SphereTwo)
    haveI : Subsingleton (integralSingularHomology 2 SphereTwo) :=
      subsingleton_integralSingularHomology_two_of_cohomology_one e
    @Function.Injective.subsingleton _ _ d.symm.toLinearMap d.symm.injective inferInstance
  exact zero_ne_one (Subsingleton.elim (0 : ℤ) 1)

theorem subsingleton_integralSingularHomology_one_punctured_of_finrank_eq_three
    (E : Type u) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (h : Module.finrank ℝ E = 3) :
    Subsingleton (integralSingularHomology 1 ({0}ᶜ : Set E)) :=
  @Function.Injective.subsingleton _ _
    (integralPuncturedSpaceSphereHomologyEquiv (E := E) 1).toLinearMap
    (integralPuncturedSpaceSphereHomologyEquiv (E := E) 1).injective
    (integralSphereHomology_subsingleton 2 1 E (by rw [h]) (by norm_num) (by norm_num))

theorem not_subsingleton_integralSingularHomology_two_punctured_of_finrank_eq_three
    (E : Type u) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (h : Module.finrank ℝ E = 3) :
    ¬ Subsingleton (integralSingularHomology 2 ({0}ᶜ : Set E)) := by
  intro hsub
  let d := (integralPuncturedSpaceSphereHomologyEquiv (E := E) 2).trans
    (integralSphereTopHomologyEquiv 1 E (by rw [h]))
  have hZ : Subsingleton ℤ :=
    @Function.Injective.subsingleton _ _ d.symm.toLinearMap d.symm.injective hsub
  exact zero_ne_one (Subsingleton.elim (0 : ℤ) 1)

theorem not_poincareDualityTwoOne_punctured_of_finrank_eq_three
    (E : Type u) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (h : Module.finrank ℝ E = 3) :
    ¬ poincareDualityTwoOne ({0}ᶜ : Set E) :=
  haveI : Subsingleton (integralSingularHomology 1 ({0}ᶜ : Set E)) :=
    subsingleton_integralSingularHomology_one_punctured_of_finrank_eq_three E h
  haveI : PathConnectedSpace ({0}ᶜ : Set E) :=
    isPathConnected_iff_pathConnectedSpace.mp
      (isPathConnected_compl_singleton_of_one_lt_rank
        (by rw [← Module.finrank_eq_rank', h]; norm_num) 0)
  fun hpd =>
    not_subsingleton_integralSingularHomology_two_punctured_of_finrank_eq_three E h
      (subsingleton_integralSingularHomology_two_of_poincareDualityTwoOne_of_subsingleton_dual
        hpd inferInstance)

end DifferentialGeometry.Topology
