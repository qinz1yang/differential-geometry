import DifferentialGeometry.Topology.Homology.LiftedSquareBoundaryDegree
import DifferentialGeometry.Topology.Homology.SphereGeneratorCriterion

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicTopology ContinuousMap Set Module
open scoped Topology

universe u

namespace DifferentialGeometry.Topology

variable {X : Type u} [TopologicalSpace X]

theorem integralAbsoluteToRelative_singleton_injective (b : X) (n : ℕ) (hn : n ≠ 0) :
    Function.Injective (integralAbsoluteToRelative n ({b} : Set X)) :=
  integralAbsoluteToRelative_injective_of_subsingleton n {b}
    (integralSingularHomology_subsingleton_of_contractible n hn ({b} : Set X))

theorem integralAbsoluteToRelative_singleton_surjective (b : X) {n : ℕ} (hn : 1 < n) :
    Function.Surjective (integralAbsoluteToRelative n ({b} : Set X)) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hspec : LinearMap.range (integralAbsoluteToRelative (m + 1) ({b} : Set X)) =
      LinearMap.ker (integralRelativeConnecting m ({b} : Set X)) :=
    (LinearMap.exact_iff.mp (integralRelative_exact_relative m ({b} : Set X))).symm
  have hzero : integralRelativeConnecting m ({b} : Set X) = 0 := by
    refine LinearMap.ext fun y => ?_
    let hsub : Subsingleton (integralSingularHomology m ({b} : Set X)) :=
      integralSingularHomology_subsingleton_of_contractible m (by omega) ({b} : Set X)
    exact @Subsingleton.elim _ hsub _ _
  exact LinearMap.range_eq_top.mp (by rw [hspec, hzero, LinearMap.ker_zero])

theorem integralAbsoluteToRelative_singleton_bijective (b : X) {n : ℕ} (hn : 1 < n) :
    Function.Bijective (integralAbsoluteToRelative n ({b} : Set X)) :=
  ⟨integralAbsoluteToRelative_singleton_injective b n (by omega),
    integralAbsoluteToRelative_singleton_surjective b hn⟩

theorem linearEquiv_symm_toLinearMap_apply {M N : Type u} [AddCommGroup M] [Module ℤ M]
    [AddCommGroup N] [Module ℤ N] (e : M ≃ₗ[ℤ] N) (y : M) :
    e.symm.toLinearMap (e y) = y :=
  LinearEquiv.symm_apply_apply e y

theorem linearEquiv_toLinearMap_apply {M N : Type u} [AddCommGroup M] [Module ℤ M]
    [AddCommGroup N] [Module ℤ N] (e : M ≃ₗ[ℤ] N) (y : M) :
    e.toLinearMap y = e y := rfl

theorem exists_linearMap_eq_one_iff_of_linearEquiv {M N : Type u} [AddCommGroup M] [Module ℤ M]
    [AddCommGroup N] [Module ℤ N] (e : M ≃ₗ[ℤ] N) (x : M) :
    (∃ φ : M →ₗ[ℤ] ℤ, φ x = 1) ↔ ∃ ψ : N →ₗ[ℤ] ℤ, ψ (e x) = 1 := by
  refine ⟨?_, ?_⟩
  · rintro ⟨φ, hφ⟩
    refine ⟨φ.comp e.symm.toLinearMap, ?_⟩
    rw [LinearMap.comp_apply, linearEquiv_symm_toLinearMap_apply, hφ]
  · rintro ⟨ψ, hψ⟩
    refine ⟨ψ.comp e.toLinearMap, ?_⟩
    rw [LinearMap.comp_apply, linearEquiv_toLinearMap_apply, hψ]

theorem isSphereHomologyGenerator_iff_exists_relative_functional (n : ℕ) (hn : 0 < n)
    (b : liftedHomotopySphere.{u} n)
    (c : integralSingularHomology (n + 1) (liftedHomotopySphere.{u} n)) :
    IsSphereHomologyGenerator n c ↔
      ∃ ψ : integralRelativeHomology (n + 1)
          ({b} : Set (liftedHomotopySphere.{u} n)) →ₗ[ℤ] ℤ,
        ψ (integralAbsoluteToRelative (n + 1)
          ({b} : Set (liftedHomotopySphere.{u} n)) c) = 1 := by
  rw [isSphereHomologyGenerator_iff_exists_functional n c]
  exact exists_linearMap_eq_one_iff_of_linearEquiv
    (LinearEquiv.ofBijective
      (integralAbsoluteToRelative (n + 1) ({b} : Set (liftedHomotopySphere.{u} n)))
      (integralAbsoluteToRelative_singleton_bijective b (X := liftedHomotopySphere.{u} n)
        (by omega))) c

theorem exists_relative_functional_integralLiftedSphereGenerator (n : ℕ) (hn : 0 < n)
    (b : liftedHomotopySphere.{u} n) :
    ∃ ψ : integralRelativeHomology (n + 1)
        ({b} : Set (liftedHomotopySphere.{u} n)) →ₗ[ℤ] ℤ,
      ψ (integralAbsoluteToRelative (n + 1)
        ({b} : Set (liftedHomotopySphere.{u} n))
        (integralLiftedSphereGenerator.{u} n)) = 1 :=
  (isSphereHomologyGenerator_iff_exists_relative_functional n hn b
    (integralLiftedSphereGenerator.{u} n)).mp (integralLiftedSphereGenerator_isGenerator n)

theorem squareSphereFundamentalClass_isSphereHomologyGenerator_iff_exists_relative_functional :
    IsSphereHomologyGenerator.{u} 1 squareSphereFundamentalClass.{u} ↔
      ∃ ψ : integralRelativeHomology 2 (liftedSphereBasepoint.{u}) →ₗ[ℤ] ℤ,
        ψ (integralAbsoluteToRelative 2 (liftedSphereBasepoint.{u})
          squareSphereFundamentalClass) = 1 :=
  isSphereHomologyGenerator_iff_exists_relative_functional 1 (by norm_num)
    (ULift.up (cubeSphereBasepoint 1)) squareSphereFundamentalClass

theorem squareSphereFundamentalClass_isSphereHomologyGenerator_iff_exists_collapse_functional :
    IsSphereHomologyGenerator.{u} 1 squareSphereFundamentalClass.{u} ↔
      ∃ ψ : integralRelativeHomology 2 (liftedSphereBasepoint.{u}) →ₗ[ℤ] ℤ,
        ψ (integralRelativeHomologyMap 2 liftedSquareCollapse.{u} liftedSquareCollapse_mapsTo
          liftedSquareRelativeFundamentalClass.{u}) = 1 := by
  rw [squareSphereFundamentalClass_isSphereHomologyGenerator_iff_exists_relative_functional,
    ← integralRelativeHomologyMap_liftedSquareCollapse_liftedSquareRelativeFundamentalClass]

theorem squareSphereFundamentalClass_isSphereHomologyGenerator_of_collapse_bijective
    (hT : Function.Bijective (integralRelativeHomologyMap 2 liftedSquareCollapse.{u}
      liftedSquareCollapse_mapsTo))
    (hrel : ∃ φ : integralRelativeHomology 2 (liftedSquareBoundary.{u}) →ₗ[ℤ] ℤ,
      φ liftedSquareRelativeFundamentalClass.{u} = 1) :
    IsSphereHomologyGenerator.{u} 1 squareSphereFundamentalClass.{u} := by
  obtain ⟨φ, hφ⟩ := hrel
  let e := LinearEquiv.ofBijective (integralRelativeHomologyMap 2 liftedSquareCollapse.{u}
    liftedSquareCollapse_mapsTo) hT
  refine (squareSphereFundamentalClass_isSphereHomologyGenerator_iff_exists_collapse_functional).mpr
    ⟨φ.comp e.symm.toLinearMap, ?_⟩
  have hx : e liftedSquareRelativeFundamentalClass.{u} =
      integralRelativeHomologyMap 2 liftedSquareCollapse.{u} liftedSquareCollapse_mapsTo
        liftedSquareRelativeFundamentalClass.{u} := rfl
  rw [← hx, LinearMap.comp_apply, linearEquiv_symm_toLinearMap_apply, hφ]

theorem hurewicz_two_mul_of_liftedSquareCollapse_bijective
    (hT : Function.Bijective (integralRelativeHomologyMap 2 liftedSquareCollapse.{u}
      liftedSquareCollapse_mapsTo))
    (hrel : ∃ φ : integralRelativeHomology 2 (liftedSquareBoundary.{u}) →ₗ[ℤ] ℤ,
      φ liftedSquareRelativeFundamentalClass.{u} = 1)
    (x : X) (c : integralSingularHomology 2 (liftedHomotopySphere.{u} 1))
    (hc : IsSphereHomologyGenerator 1 c) :
    ∀ a b : HomotopyGroup (Fin 2) X x,
      sphereHurewicz 1 x c (a * b) = sphereHurewicz 1 x c a + sphereHurewicz 1 x c b :=
  hurewicz_two_mul x
    (squareSphereFundamentalClass_isSphereHomologyGenerator_of_collapse_bijective hT hrel) c hc

theorem not_exists_linearMap_eq_one_of_subsingleton {M : Type u} [AddCommGroup M] [Module ℤ M]
    (hsub : Subsingleton M) (x : M) : ¬ ∃ φ : M →ₗ[ℤ] ℤ, φ x = 1 := by
  rintro ⟨φ, hφ⟩
  rw [@Subsingleton.elim _ hsub x 0, map_zero] at hφ
  exact zero_ne_one hφ

theorem subsingleton_integralRelativeHomology_singleton_of_subsingleton_homology (b : X)
    {n : ℕ} (hn : 1 < n) (h : Subsingleton (integralSingularHomology n X)) :
    Subsingleton (integralRelativeHomology n ({b} : Set X)) := by
  have hbij := integralAbsoluteToRelative_singleton_bijective b hn
  refine ⟨fun y₁ y₂ => ?_⟩
  obtain ⟨z₁, rfl⟩ := hbij.2 y₁
  obtain ⟨z₂, rfl⟩ := hbij.2 y₂
  rw [@Subsingleton.elim _ h z₁ z₂]

theorem pi_unitInterval_nullhomotopic (n : ℕ) :
    (ContinuousMap.id (Fin n → unitInterval)).Nullhomotopic := by
  refine ⟨fun _ => (0 : unitInterval), ⟨ContinuousMap.Homotopy.mk
    ⟨fun p => fun i => ⟨(1 - (p.1 : ℝ)) * (p.2 i : ℝ), ?_, ?_⟩, ?_⟩
    ?_ ?_⟩⟩
  · exact mul_nonneg (by linarith [(p.1).property.1, (p.1).property.2]) (p.2 i).property.1
  · nlinarith [(p.1).property.1, (p.1).property.2, (p.2 i).property.1, (p.2 i).property.2]
  · apply continuous_pi
    intro i
    apply Continuous.subtype_mk
    have h1 : Continuous fun p : unitInterval × (Fin n → unitInterval) =>
        (1 - (p.1 : ℝ)) :=
      continuous_const.sub (continuous_subtype_val.comp continuous_fst)
    have h2 : Continuous fun p : unitInterval × (Fin n → unitInterval) =>
        ((p.2 i : unitInterval) : ℝ) :=
      continuous_subtype_val.comp ((continuous_apply i).comp continuous_snd)
    exact h1.mul h2
  · intro v
    funext i
    apply Subtype.ext
    simp
  · intro v
    funext i
    apply Subtype.ext
    simp

theorem pi_unitInterval_contractible (n : ℕ) : ContractibleSpace (Fin n → unitInterval) :=
  (contractible_iff_id_nullhomotopic (Fin n → unitInterval)).mpr
    (pi_unitInterval_nullhomotopic n)

theorem integralRelativeConnecting_cubeBoundary_bijective :
    Function.Bijective (integralRelativeConnecting 2 (Cube.boundary (Fin 3))) := by
  have h3 : Subsingleton (integralSingularHomology 3 (Fin 3 → unitInterval)) :=
    @integralSingularHomology_subsingleton_of_contractible 3 (by omega) _
      _ (pi_unitInterval_contractible 3)
  have h2 : Subsingleton (integralSingularHomology 2 (Fin 3 → unitInterval)) :=
    @integralSingularHomology_subsingleton_of_contractible 2 (by omega) _
      _ (pi_unitInterval_contractible 3)
  exact ⟨integralRelativeConnecting_injective_of_subsingleton 2 (Cube.boundary (Fin 3)) h3,
    integralRelativeConnecting_surjective_of_subsingleton 2 (Cube.boundary (Fin 3)) h2⟩

noncomputable def cubeBoundaryConnectingEquiv :
    integralRelativeHomology 3 (Cube.boundary (Fin 3)) ≃ₗ[ℤ]
      integralSingularHomology 2 (Cube.boundary (Fin 3)) :=
  letI := pi_unitInterval_contractible 3
  integralRelativeConnectingEquivOfContractible 2 (by omega) (Cube.boundary (Fin 3))

theorem subsingleton_integralRelativeHomology_two_singleton_square (b : Square) :
    Subsingleton (integralRelativeHomology 2 ({b} : Set Square)) :=
  subsingleton_integralRelativeHomology_singleton_of_subsingleton_homology (X := Square) b
    (n := 2) (by norm_num)
    (@integralSingularHomology_subsingleton_of_contractible 2 (by omega) Square _
      square_contractible)

theorem subsingleton_integralRelativeHomology_three_singleton_cube (b : Fin 3 → unitInterval) :
    Subsingleton (integralRelativeHomology 3 ({b} : Set (Fin 3 → unitInterval))) :=
  subsingleton_integralRelativeHomology_singleton_of_subsingleton_homology b (n := 3)
    (by norm_num)
    (@integralSingularHomology_subsingleton_of_contractible 3 (by omega) _ _
      (pi_unitInterval_contractible 3))

theorem not_exists_linearMap_eq_one_integralRelativeHomology_two_singleton_square (b : Square)
    (z : integralRelativeHomology 2 ({b} : Set Square)) :
    ¬ ∃ φ : integralRelativeHomology 2 ({b} : Set Square) →ₗ[ℤ] ℤ, φ z = 1 :=
  not_exists_linearMap_eq_one_of_subsingleton
    (subsingleton_integralRelativeHomology_two_singleton_square b) z

end DifferentialGeometry.Topology
