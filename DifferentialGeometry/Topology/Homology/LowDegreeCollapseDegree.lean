import DifferentialGeometry.Topology.Homology.LiftedSquareBoundaryDegree
import DifferentialGeometry.Topology.Homology.LiftedSphereRelativeBridge
import DifferentialGeometry.Topology.Homology.SphereGenerator
import DifferentialGeometry.Topology.Homology.SphereGeneratorCriterion
import DifferentialGeometry.Topology.Homology.HurewiczBijectionFrontier
import DifferentialGeometry.Topology.Homology.CubeSphereDegreeUnit
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.LowDegreeHurewiczCubeBridge

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicTopology ContinuousMap Set Module
open scoped Topology

universe u

namespace DifferentialGeometry.Topology

variable {M : Type u} [AddCommGroup M] [Module ℤ M]

theorem exists_linearEquiv_eq_one_of_forall_exists_zsmul_of_linearMap_eq_one
    (φ : M →ₗ[ℤ] ℤ) (x : M) (hx : ∀ z : M, ∃ k : ℤ, z = k • x) (hφ : φ x = 1) :
    ∃ e : M ≃ₗ[ℤ] ℤ, e x = 1 := by
  have hinj : Function.Injective φ := by
    intro a b hab
    obtain ⟨ka, hka⟩ := hx a
    obtain ⟨kb, hkb⟩ := hx b
    have h1 : φ a = ka := by rw [hka, map_zsmul, hφ, smul_eq_mul, mul_one]
    have h2 : φ b = kb := by rw [hkb, map_zsmul, hφ, smul_eq_mul, mul_one]
    rw [h1, h2] at hab
    rw [hka, hkb, hab]
  have hsurj : Function.Surjective φ := fun k =>
    ⟨k • x, by rw [map_zsmul, hφ, smul_eq_mul, mul_one]⟩
  exact ⟨LinearEquiv.ofBijective φ ⟨hinj, hsurj⟩, hφ⟩

theorem forall_exists_zsmul_liftedSquareRelativeFundamentalClass_iff_boundaryLoop :
    (∀ z : integralRelativeHomology 2 (liftedSquareBoundary.{u} : Set (liftedSquare.{u})),
      ∃ k : ℤ, z = k • liftedSquareRelativeFundamentalClass.{u}) ↔
    (∀ w : integralSingularHomology 1 (liftedSquareBoundary.{u} : Set (liftedSquare.{u})),
      ∃ k : ℤ, w = k • liftedSquareBoundaryLoopClass.{u}) := by
  let e : integralRelativeHomology 2 (liftedSquareBoundary.{u} : Set (liftedSquare.{u})) ≃ₗ[ℤ]
      integralSingularHomology 1 (liftedSquareBoundary.{u} : Set (liftedSquare.{u})) :=
    LinearEquiv.ofBijective (integralRelativeConnecting 1 (liftedSquareBoundary.{u} :
      Set (liftedSquare.{u}))) integralRelativeConnecting_liftedSquare_bijective
  have he : e liftedSquareRelativeFundamentalClass.{u} =
      liftedSquareBoundaryLoopClass.{u} :=
    integralRelativeConnecting_liftedSquareRelativeFundamentalClass
  constructor
  · intro h w
    obtain ⟨k, hk⟩ := h (e.symm w)
    refine ⟨k, ?_⟩
    rw [← LinearEquiv.apply_symm_apply e w, hk, map_zsmul, he]
  · intro h z
    obtain ⟨k, hk⟩ := h (e z)
    refine ⟨k, ?_⟩
    have h3 : e.symm (e z) = k • e.symm (liftedSquareBoundaryLoopClass.{u}) := by
      rw [hk, map_zsmul]
    rw [← he, LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply] at h3
    exact h3

theorem isSphereHomologyGenerator_squareSphereFundamentalClass_iff_surjective
    (hx : ∀ z : integralRelativeHomology 2 (liftedSquareBoundary.{u} : Set (liftedSquare.{u})),
      ∃ k : ℤ, z = k • liftedSquareRelativeFundamentalClass.{u}) :
    IsSphereHomologyGenerator.{u} 1 squareSphereFundamentalClass.{u} ↔
      Function.Surjective (integralRelativeHomologyMap 2 liftedSquareCollapse.{u}
        liftedSquareCollapse_mapsTo.{u}) := by
  let habsE : integralSingularHomology 2 (liftedHomotopySphere.{u} 1) ≃ₗ[ℤ]
      integralRelativeHomology 2 (liftedSphereBasepoint.{u} :
        Set (liftedHomotopySphere.{u} 1)) :=
    LinearEquiv.ofBijective (integralAbsoluteToRelative 2
      (liftedSphereBasepoint.{u} : Set (liftedHomotopySphere.{u} 1)))
      (integralAbsoluteToRelative_singleton_bijective (ULift.up (cubeSphereBasepoint 1))
        (n := 2) (by norm_num))
  constructor
  · intro hgen n
    obtain ⟨k, hk⟩ := (isSphereHomologyGenerator_iff_forall_exists_zsmul 1
      squareSphereFundamentalClass.{u}).mp hgen (habsE.symm n)
    refine ⟨k • liftedSquareRelativeFundamentalClass.{u}, ?_⟩
    have h1 : n = k • habsE squareSphereFundamentalClass.{u} := by
      have h := congrArg habsE hk
      rwa [LinearEquiv.apply_symm_apply, map_zsmul] at h
    rw [map_zsmul, integralRelativeHomologyMap_liftedSquareCollapse_liftedSquareRelativeFundamentalClass]
    exact h1.symm
  · intro hsurj
    refine (isSphereHomologyGenerator_iff_forall_exists_zsmul 1
      squareSphereFundamentalClass.{u}).mpr ?_
    intro n
    obtain ⟨w, hw⟩ := hsurj (habsE n)
    obtain ⟨k, hk⟩ := hx w
    refine ⟨k, ?_⟩
    have h1 : habsE n = k • habsE squareSphereFundamentalClass.{u} := by
      rw [← hw, hk, map_zsmul,
        integralRelativeHomologyMap_liftedSquareCollapse_liftedSquareRelativeFundamentalClass]
      rfl
    exact habsE.injective (by rw [map_zsmul, h1])

theorem bijective_liftedSquareCollapse_of_surjective
    (hx : ∀ z : integralRelativeHomology 2 (liftedSquareBoundary.{u} : Set (liftedSquare.{u})),
      ∃ k : ℤ, z = k • liftedSquareRelativeFundamentalClass.{u})
    (hsurj : Function.Surjective (integralRelativeHomologyMap 2 liftedSquareCollapse.{u}
      liftedSquareCollapse_mapsTo.{u})) :
    Function.Bijective (integralRelativeHomologyMap 2 liftedSquareCollapse.{u}
      liftedSquareCollapse_mapsTo.{u}) := by
  have hgen := (isSphereHomologyGenerator_squareSphereFundamentalClass_iff_surjective hx).mpr hsurj
  obtain ⟨eP, heP⟩ := hgen
  let habsE : integralSingularHomology 2 (liftedHomotopySphere.{u} 1) ≃ₗ[ℤ]
      integralRelativeHomology 2 (liftedSphereBasepoint.{u} :
        Set (liftedHomotopySphere.{u} 1)) :=
    LinearEquiv.ofBijective (integralAbsoluteToRelative 2
      (liftedSphereBasepoint.{u} : Set (liftedHomotopySphere.{u} 1)))
      (integralAbsoluteToRelative_singleton_bijective (ULift.up (cubeSphereBasepoint 1))
        (n := 2) (by norm_num))
  let η : integralRelativeHomology 2 (liftedSphereBasepoint.{u} :
      Set (liftedHomotopySphere.{u} 1)) →ₗ[ℤ] ℤ := eP.toLinearMap.comp habsE.symm.toLinearMap
  have hη : η ((integralRelativeHomologyMap 2 liftedSquareCollapse.{u}
      liftedSquareCollapse_mapsTo.{u}) liftedSquareRelativeFundamentalClass.{u}) = 1 := by
    rw [integralRelativeHomologyMap_liftedSquareCollapse_liftedSquareRelativeFundamentalClass]
    change eP (habsE.symm (habsE squareSphereFundamentalClass.{u})) = 1
    rw [LinearEquiv.symm_apply_apply, heP]
  refine ⟨?_, hsurj⟩
  intro a b hab
  obtain ⟨ka, hka⟩ := hx a
  obtain ⟨kb, hkb⟩ := hx b
  have h : ka = kb := by
    have h' := congrArg η hab
    rw [hka, hkb, map_zsmul, map_zsmul, map_zsmul, map_zsmul, hη] at h'
    simpa using h'
  rw [hka, hkb, h]

theorem squareSphereFundamentalClass_ne_zero_of_surjective
    (hx : ∀ z : integralRelativeHomology 2 (liftedSquareBoundary.{u} : Set (liftedSquare.{u})),
      ∃ k : ℤ, z = k • liftedSquareRelativeFundamentalClass.{u})
    (hsurj : Function.Surjective (integralRelativeHomologyMap 2 liftedSquareCollapse.{u}
      liftedSquareCollapse_mapsTo.{u})) :
    squareSphereFundamentalClass.{u} ≠ 0 :=
  IsSphereHomologyGenerator.ne_zero 1
    ((isSphereHomologyGenerator_squareSphereFundamentalClass_iff_surjective hx).mpr hsurj)

theorem hurewiczTwoMultiplicative_of_surjective_liftedSquareCollapse {X : Type u}
    [TopologicalSpace X]
    (hx : ∀ z : integralRelativeHomology 2 (liftedSquareBoundary.{u} : Set (liftedSquare.{u})),
      ∃ k : ℤ, z = k • liftedSquareRelativeFundamentalClass.{u})
    (hrel : ∃ φ : integralRelativeHomology 2 (liftedSquareBoundary.{u} :
      Set (liftedSquare.{u})) →ₗ[ℤ] ℤ,
      φ liftedSquareRelativeFundamentalClass.{u} = 1)
    (hsurj : Function.Surjective (integralRelativeHomologyMap 2 liftedSquareCollapse.{u}
      liftedSquareCollapse_mapsTo.{u})) :
    HurewiczTwoMultiplicative X :=
  hurewiczTwoMultiplicative_of_liftedSquareCollapse_bijective
    (bijective_liftedSquareCollapse_of_surjective hx hsurj) hrel

theorem liftedSquareFundamentalChain_boundary_segments :
    (integralSingularChains (liftedSquare.{u})).d 2 1 liftedSquareFundamentalChain.{u} =
      singularChainImageGen 1 liftedSquareUp.{u}
        (squareSegmentChain squareEast squareNorthEast + squareSegmentChain squareOrigin squareEast -
          squareSegmentChain squareNorth squareNorthEast -
          squareSegmentChain squareOrigin squareNorth) := by
  rw [liftedSquareFundamentalChain, singularChainImageGen_d_eq 1 liftedSquareUp.{u}
    squareFundamentalChain, squareFundamentalChain_boundary]

theorem not_isUnit_apply_integralRelativeHomology_two_singleton_square (b : Square)
    (e : integralRelativeHomology 2 ({b} : Set Square) ≃ₗ[ℤ] ℤ)
    (x : integralRelativeHomology 2 ({b} : Set Square)) : ¬ IsUnit (e x) := by
  have hx : x = 0 :=
    @Subsingleton.elim _ (subsingleton_integralRelativeHomology_two_singleton_square b) x 0
  rw [hx, map_zero]
  exact not_isUnit_zero

theorem isSphereHomologyGenerator_cubeSphereFundamentalClass_iff_surjective
    (x : integralRelativeHomology 3 (Cube.boundary (Fin 3)))
    (hx : ∀ z : integralRelativeHomology 3 (Cube.boundary (Fin 3)), ∃ k : ℤ, z = k • x)
    (hclass : (integralRelativeHomologyMap 3 (cubeSphereCollapse.{0} 2).val
        (fun t ht => show (cubeSphereCollapse.{0} 2).val t ∈
          ({ULift.up (cubeSphereBasepoint 2)} : Set (liftedHomotopySphere.{0} 2)) from
          (cubeSphereCollapse.{0} 2).property t ht)) x =
      integralAbsoluteToRelative 3 ({ULift.up (cubeSphereBasepoint 2)} :
        Set (liftedHomotopySphere.{0} 2)) cubeSphereFundamentalClass.{0}) :
    IsSphereHomologyGenerator.{0} 2 cubeSphereFundamentalClass.{0} ↔
      Function.Surjective (integralRelativeHomologyMap 3 (cubeSphereCollapse.{0} 2).val
        (fun t ht => show (cubeSphereCollapse.{0} 2).val t ∈
          ({ULift.up (cubeSphereBasepoint 2)} : Set (liftedHomotopySphere.{0} 2)) from
          (cubeSphereCollapse.{0} 2).property t ht)) := by
  let habsE : integralSingularHomology 3 (liftedHomotopySphere.{0} 2) ≃ₗ[ℤ]
      integralRelativeHomology 3 ({ULift.up (cubeSphereBasepoint 2)} :
        Set (liftedHomotopySphere.{0} 2)) :=
    LinearEquiv.ofBijective (integralAbsoluteToRelative 3
      ({ULift.up (cubeSphereBasepoint 2)} : Set (liftedHomotopySphere.{0} 2)))
      (integralAbsoluteToRelative_singleton_bijective (ULift.up (cubeSphereBasepoint 2))
        (n := 3) (by norm_num))
  constructor
  · intro hgen n
    obtain ⟨k, hk⟩ := (isSphereHomologyGenerator_iff_forall_exists_zsmul 2
      cubeSphereFundamentalClass.{0}).mp hgen (habsE.symm n)
    refine ⟨k • x, ?_⟩
    have h1 : n = k • habsE cubeSphereFundamentalClass.{0} := by
      have h := congrArg habsE hk
      rwa [LinearEquiv.apply_symm_apply, map_zsmul] at h
    rw [map_zsmul, hclass]
    exact h1.symm
  · intro hsurj
    refine (isSphereHomologyGenerator_iff_forall_exists_zsmul 2
      cubeSphereFundamentalClass.{0}).mpr ?_
    intro n
    obtain ⟨w, hw⟩ := hsurj (habsE n)
    obtain ⟨k, hk⟩ := hx w
    refine ⟨k, ?_⟩
    have h1 : habsE n = k • habsE cubeSphereFundamentalClass.{0} := by
      rw [← hw, hk, map_zsmul, hclass]
      rfl
    exact habsE.injective (by rw [map_zsmul, h1])

theorem hurewiczThreeMultiplicative_of_surjective_cubeSphereCollapse {X : Type}
    [TopologicalSpace X]
    (x : integralRelativeHomology 3 (Cube.boundary (Fin 3)))
    (hx : ∀ z : integralRelativeHomology 3 (Cube.boundary (Fin 3)), ∃ k : ℤ, z = k • x)
    (hclass : (integralRelativeHomologyMap 3 (cubeSphereCollapse.{0} 2).val
        (fun t ht => show (cubeSphereCollapse.{0} 2).val t ∈
          ({ULift.up (cubeSphereBasepoint 2)} : Set (liftedHomotopySphere.{0} 2)) from
          (cubeSphereCollapse.{0} 2).property t ht)) x =
      integralAbsoluteToRelative 3 ({ULift.up (cubeSphereBasepoint 2)} :
        Set (liftedHomotopySphere.{0} 2)) cubeSphereFundamentalClass.{0})
    (hsurj : Function.Surjective (integralRelativeHomologyMap 3 (cubeSphereCollapse.{0} 2).val
      (fun t ht => show (cubeSphereCollapse.{0} 2).val t ∈
        ({ULift.up (cubeSphereBasepoint 2)} : Set (liftedHomotopySphere.{0} 2)) from
        (cubeSphereCollapse.{0} 2).property t ht))) :
    HurewiczThreeMultiplicative X :=
  hurewiczThreeMultiplicative_of_cubeSphereFundamentalClass_isSphereHomologyGenerator
    ((isSphereHomologyGenerator_cubeSphereFundamentalClass_iff_surjective x hx hclass).mpr hsurj)

end DifferentialGeometry.Topology
