import DifferentialGeometry.Topology.Homology.NoncompactPoincareDualityFrontier
import DifferentialGeometry.Topology.Homology.PoincareDualityThreeFrontier

noncomputable section

open CategoryTheory CategoryTheory.Limits Module Set

universe u

namespace DifferentialGeometry.Topology

private theorem nonempty_iso_iff_nonempty_linearEquiv {A B : ModuleCat.{u} ℤ} :
    Nonempty (A ≅ B) ↔ Nonempty (↑A ≃ₗ[ℤ] ↑B) where
  mp h := h.elim fun e => ⟨LinearEquiv.ofBijective e.hom.hom
    ((ConcreteCategory.isIso_iff_bijective e.hom).mp inferInstance)⟩
  mpr h := h.elim fun e => ⟨e.toModuleIso⟩

theorem poincareDualityTwoOne_iff_nonempty_linearEquiv_homologyOneDual
    (X : Type u) [TopologicalSpace X] [PathConnectedSpace X] :
    poincareDualityTwoOne X ↔
      Nonempty (integralSingularHomology 2 X ≃ₗ[ℤ]
        (integralSingularHomology 1 X →ₗ[ℤ] ℤ)) := by
  unfold poincareDualityTwoOne
  rw [nonempty_iso_iff_nonempty_linearEquiv]
  exact ⟨fun ⟨e⟩ => ⟨e.trans (integralSingularCohomologyOneLinearEquiv X)⟩,
    fun ⟨e⟩ => ⟨e.trans (integralSingularCohomologyOneLinearEquiv X).symm⟩⟩

theorem noncompactPoincareDualityTwoOne_iff_nonempty_linearEquiv_cohomologyOne
    (X : Type u) [TopologicalSpace X] [T2Space X] [CompactSpace X] (x : X) :
    noncompactPoincareDualityTwoOne ({x}ᶜ : Set X) ↔
      Nonempty (integralSingularHomology 2 ({x}ᶜ : Set X) ≃ₗ[ℤ]
        integralSingularCohomology 1 X) := by
  unfold noncompactPoincareDualityTwoOne
  rw [nonempty_iso_iff_nonempty_linearEquiv]
  exact ⟨fun ⟨e⟩ => ⟨e.trans (integralSingularCohomologyEquivOfHomeomorph
      (compactSupportCohomologyComplSingletonHomeomorph x) 1)⟩,
    fun ⟨e⟩ => ⟨e.trans (integralSingularCohomologyEquivOfHomeomorph
      (compactSupportCohomologyComplSingletonHomeomorph x) 1).symm⟩⟩

theorem noncompactPoincareDualityTwoOne_iff_nonempty_linearEquiv_homologyOneDual
    (X : Type u) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [PathConnectedSpace X] (x : X) :
    noncompactPoincareDualityTwoOne ({x}ᶜ : Set X) ↔
      Nonempty (integralSingularHomology 2 ({x}ᶜ : Set X) ≃ₗ[ℤ]
        (integralSingularHomology 1 X →ₗ[ℤ] ℤ)) := by
  rw [noncompactPoincareDualityTwoOne_iff_nonempty_linearEquiv_cohomologyOne X x]
  exact ⟨fun ⟨e⟩ => ⟨e.trans (integralSingularCohomologyOneLinearEquiv X)⟩,
    fun ⟨e⟩ => ⟨e.trans (integralSingularCohomologyOneLinearEquiv X).symm⟩⟩

theorem subsingleton_integralSingularCohomology_one_iff_subsingleton_integralSingularHomology_two_compl_singleton
    (X : Type u) [TopologicalSpace X] [T2Space X] [CompactSpace X] (x : X)
    (h : noncompactPoincareDualityTwoOne ({x}ᶜ : Set X)) :
    Subsingleton (integralSingularCohomology 1 X) ↔
      Subsingleton (integralSingularHomology 2 ({x}ᶜ : Set X)) := by
  obtain ⟨e⟩ := h
  have hb : Function.Bijective
      (e.hom.hom : integralSingularHomology 2 ({x}ᶜ : Set X) →
        integralCompactSupportCohomologyOne ({x}ᶜ : Set X)) :=
    (ConcreteCategory.isIso_iff_bijective e.hom).mp inferInstance
  have hc : ↑(integralCompactSupportCohomologyOne ({x}ᶜ : Set X)) ≃ₗ[ℤ]
      ↑(integralSingularCohomology 1 X) :=
    integralSingularCohomologyEquivOfHomeomorph
      (compactSupportCohomologyComplSingletonHomeomorph x) 1
  exact ⟨fun h₁ => ⟨fun a b => hb.1 (hc.injective
      (h₁.allEq (hc (e.hom.hom a)) (hc (e.hom.hom b))))⟩,
    fun h₂ => ⟨fun a b => by
      have hc' : Subsingleton ↑(integralCompactSupportCohomologyOne ({x}ᶜ : Set X)) :=
        ⟨fun u v => by
          obtain ⟨p, rfl⟩ := hb.2 u
          obtain ⟨q, rfl⟩ := hb.2 v
          rw [h₂.allEq p q]⟩
      obtain ⟨u, rfl⟩ := hc.surjective a
      obtain ⟨v, rfl⟩ := hc.surjective b
      rw [hc'.allEq u v]⟩⟩

theorem nonempty_linearEquiv_homologyTwo_sphereThree_dual :
    Nonempty (integralSingularHomology 2 SphereThree ≃ₗ[ℤ]
      (integralSingularHomology 1 SphereThree →ₗ[ℤ] ℤ)) :=
  (poincareDualityTwoOne_iff_nonempty_linearEquiv_homologyOneDual SphereThree).mp
    poincareDualityTwoOne_sphereThree

theorem not_nonempty_linearEquiv_homologyTwo_sphereTwo_dual :
    ¬ Nonempty (integralSingularHomology 2 SphereTwo ≃ₗ[ℤ]
      (integralSingularHomology 1 SphereTwo →ₗ[ℤ] ℤ)) :=
  fun h => not_poincareDualityTwoOne_sphereTwo
    ((poincareDualityTwoOne_iff_nonempty_linearEquiv_homologyOneDual SphereTwo).mpr h)

theorem nonempty_linearEquiv_homologyTwo_compl_singleton_sphereThree (v : SphereThree) :
    Nonempty (integralSingularHomology 2 ({v}ᶜ : Set SphereThree) ≃ₗ[ℤ]
      integralSingularCohomology 1 SphereThree) :=
  (noncompactPoincareDualityTwoOne_iff_nonempty_linearEquiv_cohomologyOne
      SphereThree v).mp
    (noncompactPoincareDualityTwoOne_sphereThree_compl_singleton v)

theorem nonempty_linearEquiv_homologyTwo_compl_singleton_sphereThree_dual
    (v : SphereThree) :
    Nonempty (integralSingularHomology 2 ({v}ᶜ : Set SphereThree) ≃ₗ[ℤ]
      (integralSingularHomology 1 SphereThree →ₗ[ℤ] ℤ)) :=
  (noncompactPoincareDualityTwoOne_iff_nonempty_linearEquiv_homologyOneDual
      SphereThree v).mp
    (noncompactPoincareDualityTwoOne_sphereThree_compl_singleton v)

theorem subsingleton_integralSingularHomology_two_compl_singleton_sphereThree
    (v : SphereThree) :
    Subsingleton (integralSingularHomology 2 ({v}ᶜ : Set SphereThree)) :=
  (subsingleton_integralSingularCohomology_one_iff_subsingleton_integralSingularHomology_two_compl_singleton
      SphereThree v (noncompactPoincareDualityTwoOne_sphereThree_compl_singleton v)).mp
    (integralSingularCohomology_one_subsingleton (X := SphereThree))

end DifferentialGeometry.Topology
