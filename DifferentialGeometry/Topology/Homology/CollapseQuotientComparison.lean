import DifferentialGeometry.Topology.Homology.LiftedSphereRelativeBridge
import DifferentialGeometry.Topology.Homology.IntegralReducedCoefficientBridge
import DifferentialGeometry.Topology.Homology.HurewiczBijectionFrontier
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.LowDegreeHurewiczCubeBridge

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicTopology ContinuousMap Set Module
open scoped Topology

universe u

namespace DifferentialGeometry.Topology

variable {M N : Type u} [AddCommGroup M] [Module ℤ M] [AddCommGroup N] [Module ℤ N]

theorem forall_exists_zsmul_of_isUnit_apply (e : M ≃ₗ[ℤ] ℤ) {x : M}
    (h : IsUnit (e x)) : ∀ z : M, ∃ k : ℤ, z = k • x := by
  obtain ⟨u, hu⟩ := h
  have h1 : e.symm (1 : ℤ) = ((u⁻¹ : ℤˣ) : ℤ) • x := by
    apply e.injective
    rw [map_zsmul, LinearEquiv.apply_symm_apply, ← hu, smul_eq_mul]
    exact (Units.inv_mul u).symm
  intro z
  refine ⟨e z * ((u⁻¹ : ℤˣ) : ℤ), ?_⟩
  calc z = e.symm (e z) := (e.symm_apply_apply z).symm
    _ = e.symm ((e z) • (1 : ℤ)) := by rw [smul_eq_mul, mul_one]
    _ = (e z) • e.symm (1 : ℤ) := map_zsmul e.symm (e z) 1
    _ = (e z) • (((u⁻¹ : ℤˣ) : ℤ) • x) := by rw [h1]
    _ = (e z * ((u⁻¹ : ℤˣ) : ℤ)) • x := smul_smul _ _ _

theorem isUnit_apply_of_exists_linearMap_eq_one (e : M ≃ₗ[ℤ] ℤ) {x : M}
    (h : ∃ φ : M →ₗ[ℤ] ℤ, φ x = 1) : IsUnit (e x) := by
  obtain ⟨φ, hφ⟩ := h
  have h2 : (e x) • e.symm (1 : ℤ) = x := by
    rw [← map_zsmul, smul_eq_mul, mul_one, LinearEquiv.symm_apply_apply]
  have hb : φ ((e x) • e.symm (1 : ℤ)) = e x * φ (e.symm 1) := by
    rw [map_zsmul, smul_eq_mul]
  have hmul : e x * φ (e.symm 1) = 1 := by
    rw [← hb, h2, hφ]
  exact Int.isUnit_iff.mpr (Int.eq_one_or_neg_one_of_mul_eq_one hmul)

theorem bijective_of_forall_exists_zsmul_of_exists_linearEquiv_eq_one
    (f : M →ₗ[ℤ] N) (x : M) (hx : ∀ z : M, ∃ k : ℤ, z = k • x)
    (hy : ∃ e : N ≃ₗ[ℤ] ℤ, e (f x) = 1) : Function.Bijective f := by
  constructor
  · intro a b hab
    obtain ⟨ka, hka⟩ := hx a
    obtain ⟨kb, hkb⟩ := hx b
    obtain ⟨e, he⟩ := hy
    have h1 : e (f a) = ka := by
      rw [hka, map_zsmul, map_zsmul, he, smul_eq_mul, mul_one]
    have h2 : e (f b) = kb := by
      rw [hkb, map_zsmul, map_zsmul, he, smul_eq_mul, mul_one]
    have hk : ka = kb := by rw [← h1, ← h2, hab]
    rw [hka, hkb, hk]
  · intro y
    obtain ⟨e, he⟩ := hy
    refine ⟨(e y) • x, ?_⟩
    apply e.injective
    rw [map_zsmul, map_zsmul, he, smul_eq_mul, mul_one]

private theorem bijective_comp_iff_of_bijective {α β γ : Sort*} (g : β → γ) (f : α → β)
    (hg : Function.Bijective g) : Function.Bijective (g ∘ f) ↔ Function.Bijective f :=
  Equiv.comp_bijective f (Equiv.ofBijective g hg)

theorem bijective_integralRelativeHomologyMap_of_forall_exists_zsmul {X Y : Type u}
    [TopologicalSpace X] [TopologicalSpace Y] {n : ℕ} (f : C(X, Y))
    {A : Set X} {B : Set Y} (hf : MapsTo f A B) (x : integralRelativeHomology n A)
    (hx : ∀ z : integralRelativeHomology n A, ∃ k : ℤ, z = k • x)
    (hy : ∃ e : integralRelativeHomology n B ≃ₗ[ℤ] ℤ,
      e (integralRelativeHomologyMap n f hf x) = 1) :
    Function.Bijective (integralRelativeHomologyMap n f hf) :=
  bijective_of_forall_exists_zsmul_of_exists_linearEquiv_eq_one
    (integralRelativeHomologyMap n f hf) x hx hy

def liftedSquareRelativeCollapse :
    integralRelativeChains (liftedSquareBoundary.{u} : Set (liftedSquare.{u})) ⟶
      integralRelativeChains (liftedSphereBasepoint.{u} :
        Set (liftedHomotopySphere.{u} 1)) :=
  integralRelativeChainMap liftedSquareCollapse.{u} liftedSquareCollapse_mapsTo.{u}

theorem liftedSquareRelativeCollapse_homologyMap :
    (HomologicalComplex.homologyMap liftedSquareRelativeCollapse.{u} 2).hom =
      integralRelativeHomologyMap 2 liftedSquareCollapse.{u} liftedSquareCollapse_mapsTo.{u} :=
  rfl

theorem isUnit_liftedSquareRelativeFundamentalClass_iff_forall_exists_zsmul
    (e : integralRelativeHomology 2 (liftedSquareBoundary.{u} :
      Set (liftedSquare.{u})) ≃ₗ[ℤ] ℤ) :
    IsUnit (e liftedSquareRelativeFundamentalClass.{u}) ↔
      ∀ z : integralRelativeHomology 2 (liftedSquareBoundary.{u} : Set (liftedSquare.{u})),
        ∃ k : ℤ, z = k • liftedSquareRelativeFundamentalClass.{u} := by
  constructor
  · intro h
    exact forall_exists_zsmul_of_isUnit_apply e h
  · intro h
    obtain ⟨k, hk⟩ := h (e.symm 1)
    have h1 : e liftedSquareRelativeFundamentalClass.{u} * k = 1 := by
      have h2 := congrArg e hk
      rw [map_zsmul, LinearEquiv.apply_symm_apply, smul_eq_mul] at h2
      rw [mul_comm]
      exact h2.symm
    exact Int.isUnit_iff.mpr (Int.eq_one_or_neg_one_of_mul_eq_one h1)

theorem bijective_liftedSquareCollapse_of_forall_exists_zsmul
    (hx : ∀ z : integralRelativeHomology 2 (liftedSquareBoundary.{u} : Set (liftedSquare.{u})),
      ∃ k : ℤ, z = k • liftedSquareRelativeFundamentalClass.{u})
    (hgen : IsSphereHomologyGenerator.{u} 1 squareSphereFundamentalClass.{u}) :
    Function.Bijective (integralRelativeHomologyMap 2 liftedSquareCollapse.{u}
      liftedSquareCollapse_mapsTo.{u}) := by
  refine bijective_of_forall_exists_zsmul_of_exists_linearEquiv_eq_one
    (integralRelativeHomologyMap 2 liftedSquareCollapse liftedSquareCollapse_mapsTo)
    liftedSquareRelativeFundamentalClass hx ?_
  obtain ⟨e, he⟩ := hgen
  have habs := integralAbsoluteToRelative_singleton_bijective
    (ULift.up (cubeSphereBasepoint 1)) (n := 2) (by norm_num)
  let habsE : integralSingularHomology 2 (liftedHomotopySphere.{u} 1) ≃ₗ[ℤ]
      integralRelativeHomology 2 (liftedSphereBasepoint.{u} :
        Set (liftedHomotopySphere.{u} 1)) :=
    LinearEquiv.ofBijective (integralAbsoluteToRelative 2
      (liftedSphereBasepoint.{u} : Set (liftedHomotopySphere.{u} 1))) habs
  refine ⟨habsE.symm.trans e, ?_⟩
  have hcomp : habsE.symm (integralAbsoluteToRelative 2
      (liftedSphereBasepoint.{u} : Set (liftedHomotopySphere.{u} 1))
      squareSphereFundamentalClass.{u}) = squareSphereFundamentalClass.{u} := by
    change habsE.symm (habsE squareSphereFundamentalClass.{u}) = squareSphereFundamentalClass.{u}
    exact LinearEquiv.symm_apply_apply habsE squareSphereFundamentalClass.{u}
  rw [LinearEquiv.trans_apply,
    integralRelativeHomologyMap_liftedSquareCollapse_liftedSquareRelativeFundamentalClass,
    hcomp, he]

theorem bijective_liftedSquareCollapse_of_isUnit
    (e : integralRelativeHomology 2 (liftedSquareBoundary.{u} : Set (liftedSquare.{u})) ≃ₗ[ℤ] ℤ)
    (hunit : IsUnit (e liftedSquareRelativeFundamentalClass.{u}))
    (hgen : IsSphereHomologyGenerator.{u} 1 squareSphereFundamentalClass.{u}) :
    Function.Bijective (integralRelativeHomologyMap 2 liftedSquareCollapse.{u}
      liftedSquareCollapse_mapsTo.{u}) :=
  bijective_liftedSquareCollapse_of_forall_exists_zsmul
    ((isUnit_liftedSquareRelativeFundamentalClass_iff_forall_exists_zsmul e).mp hunit) hgen

theorem bijective_liftedSquareCollapse_of_linearEquiv_of_functional
    (e : integralRelativeHomology 2 (liftedSquareBoundary.{u} : Set (liftedSquare.{u})) ≃ₗ[ℤ] ℤ)
    (hrel : ∃ φ : integralRelativeHomology 2 (liftedSquareBoundary.{u} :
      Set (liftedSquare.{u})) →ₗ[ℤ] ℤ,
      φ liftedSquareRelativeFundamentalClass.{u} = 1)
    (hgen : IsSphereHomologyGenerator.{u} 1 squareSphereFundamentalClass.{u}) :
    Function.Bijective (integralRelativeHomologyMap 2 liftedSquareCollapse.{u}
      liftedSquareCollapse_mapsTo.{u}) :=
  bijective_liftedSquareCollapse_of_isUnit e
    (isUnit_apply_of_exists_linearMap_eq_one e hrel) hgen

def liftedSquareReducedCollapseComparison :
    integralRelativeHomology 2 (liftedSquareBoundary.{0} : Set (liftedSquare.{0})) →ₗ[ℤ]
      (DifferentialGeometry.Homology.reducedSingularHomology (ModuleCat.of ℤ ℤ)
        (TopCat.of (liftedHomotopySphere.{0} 1)) 2) :=
  (integralReducedSingularHomologyEquiv 1 (liftedHomotopySphere.{0} 1)).toLinearMap ∘ₗ
    ((LinearEquiv.ofBijective (integralAbsoluteToRelative 2
        (liftedSphereBasepoint.{0} : Set (liftedHomotopySphere.{0} 1)))
        (integralAbsoluteToRelative_singleton_bijective (ULift.up (cubeSphereBasepoint 1))
          (n := 2) (by norm_num))).symm.toLinearMap ∘ₗ
      integralRelativeHomologyMap 2 liftedSquareCollapse.{0} liftedSquareCollapse_mapsTo.{0})

theorem liftedSquareReducedCollapseComparison_bijective_iff :
    Function.Bijective liftedSquareReducedCollapseComparison ↔
      Function.Bijective (integralRelativeHomologyMap 2 liftedSquareCollapse.{0}
        liftedSquareCollapse_mapsTo.{0}) := by
  have hA : Function.Bijective fun z : integralSingularHomology 2 (liftedHomotopySphere.{0} 1) =>
      (integralReducedSingularHomologyEquiv 1 (liftedHomotopySphere.{0} 1)) z :=
    (integralReducedSingularHomologyEquiv 1 (liftedHomotopySphere.{0} 1)).bijective
  have hB : Function.Bijective fun z : integralRelativeHomology 2
      (liftedSphereBasepoint.{0} : Set (liftedHomotopySphere.{0} 1)) =>
      (LinearEquiv.ofBijective (integralAbsoluteToRelative 2
        (liftedSphereBasepoint.{0} : Set (liftedHomotopySphere.{0} 1)))
        (integralAbsoluteToRelative_singleton_bijective (ULift.up (cubeSphereBasepoint 1))
          (n := 2) (by norm_num))).symm z :=
    (LinearEquiv.ofBijective (integralAbsoluteToRelative 2
      (liftedSphereBasepoint.{0} : Set (liftedHomotopySphere.{0} 1)))
      (integralAbsoluteToRelative_singleton_bijective (ULift.up (cubeSphereBasepoint 1))
        (n := 2) (by norm_num))).symm.bijective
  change Function.Bijective ((fun z : integralSingularHomology 2 (liftedHomotopySphere.{0} 1) =>
      (integralReducedSingularHomologyEquiv 1 (liftedHomotopySphere.{0} 1)) z) ∘
      ((fun z : integralRelativeHomology 2 (liftedSphereBasepoint.{0} :
          Set (liftedHomotopySphere.{0} 1)) =>
        (LinearEquiv.ofBijective (integralAbsoluteToRelative 2
          (liftedSphereBasepoint.{0} : Set (liftedHomotopySphere.{0} 1)))
          (integralAbsoluteToRelative_singleton_bijective (ULift.up (cubeSphereBasepoint 1))
            (n := 2) (by norm_num))).symm z) ∘
        (integralRelativeHomologyMap 2 liftedSquareCollapse.{0}
          liftedSquareCollapse_mapsTo.{0}))) ↔ _
  exact (bijective_comp_iff_of_bijective _ _ hA).trans (bijective_comp_iff_of_bijective _ _ hB)

theorem bijective_liftedSquareReducedCollapseComparison_of_forall_exists_zsmul
    (hx : ∀ z : integralRelativeHomology 2 (liftedSquareBoundary.{0} : Set (liftedSquare.{0})),
      ∃ k : ℤ, z = k • liftedSquareRelativeFundamentalClass.{0})
    (hgen : IsSphereHomologyGenerator.{0} 1 squareSphereFundamentalClass.{0}) :
    Function.Bijective liftedSquareReducedCollapseComparison :=
  liftedSquareReducedCollapseComparison_bijective_iff.mpr
    (bijective_liftedSquareCollapse_of_forall_exists_zsmul hx hgen)

theorem not_bijective_zsmul_integralRelativeHomology_two_singleton_square (b : Square)
    (x : integralRelativeHomology 2 ({b} : Set Square)) :
    ¬ Function.Bijective fun z : ℤ => z • x := by
  intro h
  have h0 : x = 0 :=
    @Subsingleton.elim _ (subsingleton_integralRelativeHomology_two_singleton_square b) x 0
  have hz : (0 : ℤ) • x = (1 : ℤ) • x := by
    rw [h0]
    simp
  exact zero_ne_one (h.1 hz)

theorem cubeSphereCollapse_mapsTo :
    MapsTo (cubeSphereCollapse.{0} 2).val (Cube.boundary (Fin 3))
      ({ULift.up (cubeSphereBasepoint 2)} : Set (liftedHomotopySphere.{0} 2)) :=
  fun t ht => (cubeSphereCollapse.{0} 2).property t ht

def cubeSphereRelativeCollapse :
    integralRelativeChains (Cube.boundary (Fin 3)) ⟶
      integralRelativeChains ({ULift.up (cubeSphereBasepoint 2)} :
        Set (liftedHomotopySphere.{0} 2)) :=
  integralRelativeChainMap (cubeSphereCollapse.{0} 2).val cubeSphereCollapse_mapsTo

theorem cubeSphereRelativeCollapse_homologyMap :
    (HomologicalComplex.homologyMap cubeSphereRelativeCollapse 3).hom =
      integralRelativeHomologyMap 3 (cubeSphereCollapse.{0} 2).val cubeSphereCollapse_mapsTo :=
  rfl

def cubeSphereCollapseComparison :
    integralRelativeHomology 3 (Cube.boundary (Fin 3)) →ₗ[ℤ]
      integralRelativeHomology 3 ({ULift.up (cubeSphereBasepoint 2)} :
        Set (liftedHomotopySphere.{0} 2)) :=
  integralRelativeHomologyMap 3 (cubeSphereCollapse.{0} 2).val cubeSphereCollapse_mapsTo

theorem bijective_cubeSphereCollapse_of_forall_exists_zsmul
    (x : integralRelativeHomology 3 (Cube.boundary (Fin 3)))
    (hx : ∀ z : integralRelativeHomology 3 (Cube.boundary (Fin 3)), ∃ k : ℤ, z = k • x)
    (hclass : cubeSphereCollapseComparison x =
      integralAbsoluteToRelative 3 ({ULift.up (cubeSphereBasepoint 2)} :
        Set (liftedHomotopySphere.{0} 2)) cubeSphereFundamentalClass.{0})
    (hgen : IsSphereHomologyGenerator.{0} 2 cubeSphereFundamentalClass.{0}) :
    Function.Bijective cubeSphereCollapseComparison := by
  refine bijective_of_forall_exists_zsmul_of_exists_linearEquiv_eq_one
    cubeSphereCollapseComparison x hx ?_
  obtain ⟨e, he⟩ := hgen
  have habs := integralAbsoluteToRelative_singleton_bijective
    (ULift.up (cubeSphereBasepoint 2)) (n := 3) (by norm_num)
  let habsE : integralSingularHomology 3 (liftedHomotopySphere.{0} 2) ≃ₗ[ℤ]
      integralRelativeHomology 3 ({ULift.up (cubeSphereBasepoint 2)} :
        Set (liftedHomotopySphere.{0} 2)) :=
    LinearEquiv.ofBijective (integralAbsoluteToRelative 3
      ({ULift.up (cubeSphereBasepoint 2)} : Set (liftedHomotopySphere.{0} 2))) habs
  refine ⟨habsE.symm.trans e, ?_⟩
  have hcomp : habsE.symm (integralAbsoluteToRelative 3
      ({ULift.up (cubeSphereBasepoint 2)} : Set (liftedHomotopySphere.{0} 2))
      cubeSphereFundamentalClass.{0}) = cubeSphereFundamentalClass.{0} := by
    change habsE.symm (habsE cubeSphereFundamentalClass.{0}) = cubeSphereFundamentalClass.{0}
    exact LinearEquiv.symm_apply_apply habsE cubeSphereFundamentalClass.{0}
  rw [LinearEquiv.trans_apply, hclass, hcomp, he]

theorem isSphereHomologyGenerator_squareSphereFundamentalClass_iff_isUnit :
    IsSphereHomologyGenerator.{u} 1 squareSphereFundamentalClass.{u} ↔
      IsUnit (integralLiftedSphereTopEquiv.{u} 1 squareSphereFundamentalClass.{u}) := by
  rw [isSphereHomologyGenerator_squareSphereFundamentalClass_iff_coordinate]
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

theorem hurewiczTwoMultiplicative_of_forall_exists_zsmul {Y : Type u} [TopologicalSpace Y]
    (hx : ∀ z : integralRelativeHomology 2 (liftedSquareBoundary.{u} : Set (liftedSquare.{u})),
      ∃ k : ℤ, z = k • liftedSquareRelativeFundamentalClass.{u})
    (hgen : IsSphereHomologyGenerator.{u} 1 squareSphereFundamentalClass.{u})
    (hrel : ∃ φ : integralRelativeHomology 2 (liftedSquareBoundary.{u} :
      Set (liftedSquare.{u})) →ₗ[ℤ] ℤ,
      φ liftedSquareRelativeFundamentalClass.{u} = 1) :
    HurewiczTwoMultiplicative Y :=
  hurewiczTwoMultiplicative_of_liftedSquareCollapse_bijective
    (bijective_liftedSquareCollapse_of_forall_exists_zsmul hx hgen) hrel

end DifferentialGeometry.Topology
