import DifferentialGeometry.Topology.LocalDegree.SphereAntipodal
import DifferentialGeometry.Topology.LocalDegree.LinearSphere
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional

set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits
open Metric Submodule
noncomputable section
universe u
namespace DifferentialGeometry.LocalDegree
open DifferentialGeometry.Homology

variable {E : Type u} [NormedAddCommGroup E]

section Normed
variable [NormedSpace ℝ E]


theorem linearSphereMap_linearIsometryEquiv_apply (A : E ≃ₗᵢ[ℝ] E)
    (x : sphere (0 : E) 1) :
    (linearSphereMap A.toContinuousLinearEquiv x : E) = A x := by
  rw [linearSphereMap_apply]
  change ‖A x‖⁻¹ • A x = A x
  rw [A.norm_map, norm_eq_of_mem_sphere x]
  simp

end Normed

variable [InnerProductSpace ℝ E]

def unitSphereReflection (v : E) : C(sphere (0 : E) 1, sphere (0 : E) 1) :=
  linearSphereMap ((ℝ ∙ v)ᗮ.reflection.toContinuousLinearEquiv)


@[simp]
theorem unitSphereReflection_apply (v : E) (x : sphere (0 : E) 1) :
    (unitSphereReflection v x : E) = (ℝ ∙ v)ᗮ.reflection x :=
  linearSphereMap_linearIsometryEquiv_apply _ x


@[simp]
theorem unitSphereReflection_normal (v : sphere (0 : E) 1) :
    unitSphereReflection (v : E) v = -v := by
  apply Subtype.ext
  rw [unitSphereReflection_apply]
  exact reflection_orthogonalComplement_singleton_eq_neg (𝕜 := ℝ) (v : E)


theorem unitSphereReflection_injective (v : E) : Function.Injective (unitSphereReflection v) := by
  intro x y h
  apply Subtype.ext
  apply (ℝ ∙ v)ᗮ.reflection.injective
  simpa only [unitSphereReflection_apply] using congrArg Subtype.val h

private theorem reflection_maps_first (v : sphere (0 : E) 1) :
    Set.MapsTo (unitSphereReflection (v : E))
      (poleComplement v : Set (sphere (0 : E) 1))
      (poleComplement (-v) : Set (sphere (0 : E) 1)) := by
  intro x hx
  change unitSphereReflection (v : E) x ≠ -v
  intro h
  exact hx (unitSphereReflection_injective (v : E) (h.trans (unitSphereReflection_normal v).symm))

private theorem reflection_maps_second (v : sphere (0 : E) 1) :
    Set.MapsTo (unitSphereReflection (v : E))
      (poleComplement (-v) : Set (sphere (0 : E) 1))
      (poleComplement v : Set (sphere (0 : E) 1)) := by
  intro x hx
  have hv : unitSphereReflection (v : E) (-v) = v := by
    apply Subtype.ext
    rw [unitSphereReflection_apply]
    change (ℝ ∙ (v : E))ᗮ.reflection (-(v : E)) = (v : E)
    rw [map_neg, reflection_orthogonalComplement_singleton_eq_neg (𝕜 := ℝ), neg_neg]
  change unitSphereReflection (v : E) x ≠ v
  intro h
  exact hx (unitSphereReflection_injective (v : E) (h.trans hv.symm))


def poleOverlapReflection (v : sphere (0 : E) 1) :
    TopCat.of (poleIntersection v) ⟶ TopCat.of (poleIntersection v) :=
  relativeSubspaceMap (TopCat.ofHom (unitSphereReflection (v : E)))
    (fun _ hx => ⟨reflection_maps_second v hx.2, reflection_maps_first v hx.1⟩)


theorem poleIntersectionHomotopyEquiv_inv_reflection (v : sphere (0 : E) 1) :
    TopCat.ofHom (poleIntersectionHomotopyEquiv v).invFun ≫ poleOverlapReflection v =
      TopCat.ofHom (poleIntersectionHomotopyEquiv v).invFun := by
  ext x
  change (unitSphereReflection (v : E) ((poleIntersectionHomotopyEquiv v).symm x).val : E) =
    (((poleIntersectionHomotopyEquiv v).symm x).val : E)
  rw [unitSphereReflection_apply, poleIntersectionHomotopyEquiv_symm_apply]
  exact reflection_mem_subspace_eq_self x.val.property

variable {k : Type u} [Ring k] (R : ModuleCat.{u} k)

theorem poleOverlapReflection_reducedHomologyMap (v : sphere (0 : E) 1) (n : ℕ) :
    reducedSingularHomologyMap R (poleOverlapReflection v) n = 𝟙 _ := by
  let e : reducedSingularHomology R (TopCat.of (poleIntersection v)) n ≅
      reducedSingularHomology R (TopCat.of (EquatorialSphere v)) n :=
    reducedSingularHomologyIso R (poleIntersectionHomotopyEquiv v) n
  apply (cancel_epi e.inv).mp
  have h := congrArg (fun f => reducedSingularHomologyMap R f n)
    (poleIntersectionHomotopyEquiv_inv_reflection v)
  simp only [reducedSingularHomologyMap_comp] at h
  exact h.trans (Category.comp_id e.inv).symm

private theorem reflection_poleCover (v : sphere (0 : E) 1) :
    ∀ x : sphere (0 : E) 1,
      x ∈ (poleComplement v : Set (sphere (0 : E) 1)) ∨
      x ∈ (poleComplement (-v) : Set (sphere (0 : E) 1)) := by
  intro x
  have h : x ∈ (poleComplement v ⊔ poleComplement (-v)) := by
    rw [poleComplement_sup]
    trivial
  exact h


theorem sphereEquatorReducedHomologyIso_reflection (v : sphere (0 : E) 1) (n : ℕ) :
    reducedSingularHomologyMap R (TopCat.ofHom (unitSphereReflection (v : E))) (n + 1) ≫
        (sphereEquatorReducedHomologyIso R v n).hom =
      -(sphereEquatorReducedHomologyIso R v n).hom := by
  have hs := contractibleSpace_poleComplement v
  have ht := contractibleSpace_poleComplement (-v)
  have h := reducedConnectingMap_of_coverExchange R
    (TopCat.ofHom (unitSphereReflection (v : E)))
    (reflection_maps_first v) (reflection_maps_second v)
    (poleComplement v).isOpen (poleComplement (-v)).isOpen (reflection_poleCover v) n
  rw [reducedMayerVietorisConnectingMap_eq_iso] at h
  change _ ≫ (_ ≫ _) = -(_ ≫ _)
  rw [← Category.assoc, h, Preadditive.neg_comp, Category.assoc]
  let e : reducedSingularHomology R (TopCat.of (poleIntersection v)) n ≅
      reducedSingularHomology R (TopCat.of (EquatorialSphere v)) n :=
    reducedSingularHomologyIso R (poleIntersectionHomotopyEquiv v) n
  have hh := congrArg (fun f =>
    (reducedMayerVietorisConnectingIso R (TopCat.of (sphere (0 : E) 1))
      (poleComplement v : Set (sphere (0 : E) 1))
      (poleComplement (-v) : Set (sphere (0 : E) 1))
      (poleComplement v).isOpen (poleComplement (-v)).isOpen (reflection_poleCover v) n).hom ≫
      (f ≫ e.hom))
    (poleOverlapReflection_reducedHomologyMap R v n)
  simpa only [Category.id_comp] using! congrArg Neg.neg hh

theorem unitSphereReflection_reducedHomologyMap_succ (v : sphere (0 : E) 1) (n : ℕ) :
    reducedSingularHomologyMap R (TopCat.ofHom (unitSphereReflection (v : E))) (n + 1) =
      -𝟙 _ := by
  apply (cancel_mono (sphereEquatorReducedHomologyIso R v n).hom).mp
  rw [sphereEquatorReducedHomologyIso_reflection, Preadditive.neg_comp, Category.id_comp]


theorem euclideanSphereDegree_reflection_unit {d : ℕ} (v : EuclideanSphere d) :
    euclideanSphereDegree (unitSphereReflection (v : EuclideanSpace ℝ (Fin (d + 1)))) = -1 := by
  cases d with
  | zero =>
    have hspan : ℝ ∙ (v : EuclideanSpace ℝ (Fin 1)) = ⊤ :=
      Submodule.eq_top_of_finrank_eq (by
        rw [finrank_span_singleton (ne_zero_of_mem_unit_sphere v)]
        simp)
    have heq : unitSphereReflection (v : EuclideanSpace ℝ (Fin 1)) =
        unitSphereAntipodal (EuclideanSpace ℝ (Fin 1)) := by
      apply ContinuousMap.ext
      intro x
      apply Subtype.ext
      simp only [unitSphereReflection_apply, hspan, top_orthogonal_eq_bot, reflection_bot]
      rfl
    rw [heq, euclideanSphereDegree_antipodal_zero]
  | succ d =>
    unfold euclideanSphereDegree
    rw [unitSphereReflection_reducedHomologyMap_succ]
    change euclideanSphereTopReducedHomologyEquiv (d + 1)
      (-euclideanSphereTopGenerator (d + 1)) = -1
    rw [map_neg, euclideanSphereTopReducedHomologyEquiv_generator]


theorem euclideanSphereDegree_reflection {d : ℕ}
    (v : EuclideanSpace ℝ (Fin (d + 1))) (hv : v ≠ 0) :
    euclideanSphereDegree (unitSphereReflection v) = -1 := by
  let p : EuclideanSphere d := ⟨‖v‖⁻¹ • v, by
    rw [mem_sphere_zero_iff_norm, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg v)),
      inv_mul_cancel₀ (norm_ne_zero_iff.mpr hv)]⟩
  have hspan : ℝ ∙ (p : EuclideanSpace ℝ (Fin (d + 1))) = ℝ ∙ v :=
    span_singleton_smul_eq (isUnit_iff_ne_zero.mpr (inv_ne_zero (norm_ne_zero_iff.mpr hv))) v
  have h := euclideanSphereDegree_reflection_unit p
  simpa only [unitSphereReflection, hspan] using h

theorem euclideanSphereDegree_hyperplaneReflection {d : ℕ}
    (K : Submodule ℝ (EuclideanSpace ℝ (Fin (d + 1))))
    (hK : Module.finrank ℝ Kᗮ = 1) :
    euclideanSphereDegree (linearSphereMap K.reflection.toContinuousLinearEquiv) = -1 := by
  let b := Module.finBasisOfFinrankEq ℝ Kᗮ hK
  have hv : ((b 0 : Kᗮ) : EuclideanSpace ℝ (Fin (d + 1))) ≠ 0 := by
    intro hz
    exact b.ne_zero 0 (Subtype.ext hz)
  have hspan := eq_span_singleton_of_mem_of_finrank_eq_one hK (b 0).property hv
  have hplane : K = (ℝ ∙ ((b 0 : Kᗮ) : EuclideanSpace ℝ (Fin (d + 1))))ᗮ := by
    rw [← hspan, K.orthogonal_orthogonal]
  exact (congrArg (fun L : Submodule ℝ (EuclideanSpace ℝ (Fin (d + 1))) =>
    euclideanSphereDegree (linearSphereMap L.reflection.toContinuousLinearEquiv)) hplane).trans
      (euclideanSphereDegree_reflection _ hv)


@[simp]
theorem unitSphereReflection_zero :
    unitSphereReflection (0 : E) = ContinuousMap.id (sphere (0 : E) 1) := by
  ext x
  rw [unitSphereReflection_apply]
  apply reflection_mem_subspace_eq_self
  rw [mem_orthogonal_singleton_iff_inner_left]
  simp


theorem euclideanSphereDegree_reflection_zero (d : ℕ) :
    euclideanSphereDegree (unitSphereReflection (0 : EuclideanSpace ℝ (Fin (d + 1)))) = 1 := by
  rw [unitSphereReflection_zero, euclideanSphereDegree_id]

end DifferentialGeometry.LocalDegree
