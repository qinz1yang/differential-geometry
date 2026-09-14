import DifferentialGeometry.Topology.Homology.CohomologyHomeomorphInvariance
import DifferentialGeometry.Topology.Homology.NoncompactPoincareDualityFrontier

noncomputable section

open CategoryTheory CategoryTheory.Limits Metric Module Set

universe u

namespace DifferentialGeometry.Topology

abbrev integralCompactSupportCohomology (n : ℕ) (X : Type u) [TopologicalSpace X] :
    ModuleCat.{u} ℤ :=
  integralSingularCohomology n (OnePoint X)

theorem integralCompactSupportCohomology_one (X : Type u) [TopologicalSpace X] :
    integralCompactSupportCohomology 1 X = integralCompactSupportCohomologyOne X := rfl

theorem nonempty_linearEquiv_compactSupportCohomology_compl_singleton
    (X : Type u) [TopologicalSpace X] [T2Space X] [CompactSpace X] (x : X) (n : ℕ) :
    Nonempty (integralCompactSupportCohomology n ({x}ᶜ : Set X) ≃ₗ[ℤ]
      integralSingularCohomology n X) :=
  ⟨integralSingularCohomologyEquivOfHomeomorph
    (compactSupportCohomologyComplSingletonHomeomorph x) n⟩

theorem nonempty_linearEquiv_compactSupportCohomology_punctured_sphere
    (E : Type u) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (v : sphere (0 : E) 1) (n : ℕ) :
    Nonempty (integralCompactSupportCohomology n ({v}ᶜ : Set (sphere (0 : E) 1)) ≃ₗ[ℤ]
      integralSingularCohomology n (sphere (0 : E) 1)) :=
  nonempty_linearEquiv_compactSupportCohomology_compl_singleton (sphere (0 : E) 1) v n

theorem subsingleton_compactSupportCohomology_compl_singleton_iff
    (X : Type u) [TopologicalSpace X] [T2Space X] [CompactSpace X] (x : X) (n : ℕ) :
    Subsingleton (integralCompactSupportCohomology n ({x}ᶜ : Set X)) ↔
      Subsingleton (integralSingularCohomology n X) := by
  have hc := integralSingularCohomologyEquivOfHomeomorph
    (compactSupportCohomologyComplSingletonHomeomorph x) n
  exact ⟨fun h => ⟨fun a b => by
      obtain ⟨u, rfl⟩ := hc.surjective a
      obtain ⟨v, rfl⟩ := hc.surjective b
      rw [h.allEq u v]⟩,
    fun h => ⟨fun a b => hc.injective (h.allEq (hc a) (hc b))⟩⟩

theorem nonempty_linearEquiv_homologyOne_compactSupportCohomologyTwo_iff
    (X : Type u) [TopologicalSpace X] [T2Space X] [CompactSpace X] (x : X) :
    Nonempty (integralSingularHomology 1 ({x}ᶜ : Set X) ≃ₗ[ℤ]
        integralCompactSupportCohomology 2 ({x}ᶜ : Set X)) ↔
      Nonempty (integralSingularHomology 1 ({x}ᶜ : Set X) ≃ₗ[ℤ]
        integralSingularCohomology 2 X) :=
  ⟨fun ⟨e⟩ => ⟨e.trans (integralSingularCohomologyEquivOfHomeomorph
      (compactSupportCohomologyComplSingletonHomeomorph x) 2)⟩,
    fun ⟨e⟩ => ⟨e.trans (integralSingularCohomologyEquivOfHomeomorph
      (compactSupportCohomologyComplSingletonHomeomorph x) 2).symm⟩⟩

theorem integralSingularCohomologyEquivOfHomeomorph_refl
    (X : Type u) [TopologicalSpace X] (n : ℕ) :
    integralSingularCohomologyEquivOfHomeomorph (Homeomorph.refl X) n =
      LinearEquiv.refl ℤ (integralSingularCohomology n X) := by
  ext a
  change integralSingularCohomologyMap n ((Homeomorph.refl X).symm : C(X, X)) a = a
  rw [show ((Homeomorph.refl X).symm : C(X, X)) = ContinuousMap.id X from rfl,
    integralSingularCohomologyMap_id]
  rfl

theorem integralSingularCohomologyEquivOfHomeomorph_trans
    {X Y Z : Type u} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    (e : X ≃ₜ Y) (f : Y ≃ₜ Z) (n : ℕ) :
    integralSingularCohomologyEquivOfHomeomorph (e.trans f) n =
      (integralSingularCohomologyEquivOfHomeomorph e n).trans
        (integralSingularCohomologyEquivOfHomeomorph f n) := by
  ext a
  change integralSingularCohomologyMap n ((e.trans f).symm : C(Z, X)) a =
    integralSingularCohomologyMap n (f.symm : C(Z, Y))
      (integralSingularCohomologyMap n (e.symm : C(Y, X)) a)
  rw [← LinearMap.comp_apply, ← integralSingularCohomologyMap_comp]
  congr 1

theorem nonempty_linearEquiv_compactSupportCohomology_two_compl_singleton_sphereThree
    (v : SphereThree) :
    Nonempty (integralCompactSupportCohomology 2 ({v}ᶜ : Set SphereThree) ≃ₗ[ℤ]
      integralSingularCohomology 2 SphereThree) :=
  nonempty_linearEquiv_compactSupportCohomology_compl_singleton SphereThree v 2

theorem subsingleton_compactSupportCohomology_one_compl_singleton_sphereThree
    (v : SphereThree) :
    Subsingleton (integralCompactSupportCohomology 1 ({v}ᶜ : Set SphereThree)) :=
  (subsingleton_compactSupportCohomology_compl_singleton_iff SphereThree v 1).mpr
    (integralSingularCohomology_one_subsingleton (X := SphereThree))

theorem subsingleton_compactSupportCohomology_two_compl_singleton_punit :
    Subsingleton (integralCompactSupportCohomology 2 ({PUnit.unit}ᶜ : Set PUnit.{u + 1})) ↔
      Subsingleton (integralSingularCohomology 2 PUnit.{u + 1}) :=
  subsingleton_compactSupportCohomology_compl_singleton_iff PUnit.{u + 1} PUnit.unit 2

theorem nonempty_linearEquiv_homologyOne_compactSupportCohomologyTwo_iff_sphereThree
    (v : SphereThree) :
    Nonempty (integralSingularHomology 1 ({v}ᶜ : Set SphereThree) ≃ₗ[ℤ]
        integralCompactSupportCohomology 2 ({v}ᶜ : Set SphereThree)) ↔
      Nonempty (integralSingularHomology 1 ({v}ᶜ : Set SphereThree) ≃ₗ[ℤ]
        integralSingularCohomology 2 SphereThree) :=
  nonempty_linearEquiv_homologyOne_compactSupportCohomologyTwo_iff SphereThree v

end DifferentialGeometry.Topology
