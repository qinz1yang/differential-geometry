import Mathlib.Geometry.Manifold.Instances.Sphere
import Mathlib.Analysis.Normed.Module.Ball.RadialEquiv
import Mathlib.Analysis.Convex.Contractible

set_option autoImplicit false
open Metric Set Module ContinuousMap
open scoped Topology RealInnerProductSpace unitInterval
noncomputable section
namespace Poincare.LocalDegree

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]


def poleComplement (v : sphere (0 : E) 1) : TopologicalSpace.Opens (sphere (0 : E) 1) :=
  ⟨{v}ᶜ, isOpen_compl_singleton⟩

private theorem pole_ne_neg (v : sphere (0 : E) 1) : v ≠ -v := by
  intro heq
  have hh := congrArg (fun x : sphere (0 : E) 1 ↦ ⟪(v : E), (x : E)⟫) heq
  change ⟪(v : E), (v : E)⟫ = ⟪(v : E), -(v : E)⟫ at hh
  have hi : ⟪(v : E), (v : E)⟫ = 1 := by simp [norm_eq_of_mem_sphere v]
  rw [inner_neg_right, hi] at hh
  norm_num at hh


theorem poleComplement_sup (v : sphere (0 : E) 1) :
    poleComplement v ⊔ poleComplement (-v) = ⊤ := by
  ext x
  change (x ∈ ({v}ᶜ ∪ {-v}ᶜ : Set (sphere (0 : E) 1))) ↔ True
  simp only [mem_union, mem_compl_iff, mem_singleton_iff, iff_true]
  by_cases h : x = v
  · exact Or.inr (h ▸ pole_ne_neg v)
  · exact Or.inl h


def puncturedSphereHomeomorph (v : sphere (0 : E) 1) :
    poleComplement v ≃ₜ (ℝ ∙ (v : E))ᗮ :=
  (stereographic (norm_eq_of_mem_sphere v)).toHomeomorphSourceTarget.trans
    (Homeomorph.Set.univ _)


theorem puncturedSphereHomeomorph_apply (v : sphere (0 : E) 1) (x : poleComplement v) :
    puncturedSphereHomeomorph v x =
      (2 / (1 - ⟪(v : E), (x.val : E)⟫)) • (ℝ ∙ (v : E))ᗮ.orthogonalProjectionOnto x.val := rfl


theorem contractibleSpace_poleComplement (v : sphere (0 : E) 1) :
    ContractibleSpace (poleComplement v) :=
  (puncturedSphereHomeomorph v).contractibleSpace

private theorem stereographic_eq_zero_iff (v x : sphere (0 : E) 1)
    (hx : x ≠ v) : stereographic (norm_eq_of_mem_sphere v) x = 0 ↔ x = -v := by
  constructor
  · intro hz
    apply (stereographic (norm_eq_of_mem_sphere v)).injOn hx
      (Ne.symm (pole_ne_neg v))
    exact hz.trans (stereographic_apply_neg v).symm
  · intro h
    rw [h]
    exact stereographic_apply_neg v


def poleIntersection (v : sphere (0 : E) 1) : TopologicalSpace.Opens (sphere (0 : E) 1) :=
  poleComplement v ⊓ poleComplement (-v)


abbrev EquatorialSphere (v : sphere (0 : E) 1) :=
  sphere (0 : (ℝ ∙ (v : E))ᗮ) 1

private def intersectionAsSubtype (v : sphere (0 : E) 1) :
    poleIntersection v ≃ₜ {x : poleComplement v // x.val ≠ -v} where
  toFun x := ⟨⟨x.val, x.property.1⟩, x.property.2⟩
  invFun x := ⟨x.val.val, ⟨x.val.property, x.property⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

def poleIntersectionPuncturedHomeomorph (v : sphere (0 : E) 1) :
    poleIntersection v ≃ₜ ({0}ᶜ : Set (ℝ ∙ (v : E))ᗮ) :=
  (intersectionAsSubtype v).trans
    ((puncturedSphereHomeomorph v).subtype (fun x ↦
      (not_congr (stereographic_eq_zero_iff v x.val x.property)).symm))

def poleIntersectionHomeomorph (v : sphere (0 : E) 1) :
    poleIntersection v ≃ₜ (EquatorialSphere v × Ioi (0 : ℝ)) :=
  (poleIntersectionPuncturedHomeomorph v).trans (homeomorphUnitSphereProd _)


theorem poleIntersectionHomeomorph_direction (v : sphere (0 : E) 1)
    (x : poleIntersection v) :
    ((poleIntersectionHomeomorph v x).1 : (ℝ ∙ (v : E))ᗮ) =
      ‖stereographic (norm_eq_of_mem_sphere v) x.val‖⁻¹ •
        stereographic (norm_eq_of_mem_sphere v) x.val :=
  homeomorphUnitSphereProd_apply_fst_coe _ _


theorem poleIntersectionHomeomorph_radius (v : sphere (0 : E) 1)
    (x : poleIntersection v) :
    ((poleIntersectionHomeomorph v x).2 : ℝ) =
      ‖stereographic (norm_eq_of_mem_sphere v) x.val‖ :=
  homeomorphUnitSphereProd_apply_snd_coe _ _

theorem poleIntersectionHomeomorph_symm_apply (v : sphere (0 : E) 1)
    (e : EquatorialSphere v) (r : Ioi (0 : ℝ)) :
    (((poleIntersectionHomeomorph v).symm (e, r)).val : E) =
      ((r : ℝ) ^ 2 + 4)⁻¹ •
        ((4 * (r : ℝ)) • (e.val : E) + ((r : ℝ) ^ 2 - 4) • (v : E)) := by
  let w := (homeomorphUnitSphereProd (ℝ ∙ (v : E))ᗮ).symm (e, r)
  have hw : (w : (ℝ ∙ (v : E))ᗮ) = (r : ℝ) • (e : (ℝ ∙ (v : E))ᗮ) :=
    homeomorphUnitSphereProd_symm_apply_coe _ _
  have hnorm : ‖(w : (ℝ ∙ (v : E))ᗮ)‖ = (r : ℝ) := by
    rw [hw, norm_smul, Real.norm_of_nonneg r.property.le, norm_eq_of_mem_sphere e, mul_one]
  change (stereoInvFun (norm_eq_of_mem_sphere v) (w : (ℝ ∙ (v : E))ᗮ) : E) = _
  rw [stereoInvFun_apply, hnorm, hw]
  simp only [Submodule.coe_smul_of_tower, smul_smul]

private def productPositiveHomotopyEquiv (X : Type*) [TopologicalSpace X] :
    (X × Ioi (0 : ℝ)) ≃ₕ X where
  toFun := ⟨Prod.fst, continuous_fst⟩
  invFun := (ContinuousMap.id X).prodMk (ContinuousMap.const X ⟨2, by norm_num⟩)
  left_inv := ⟨{
    toFun := fun p ↦ (p.2.1, ⟨(1 - (p.1 : ℝ)) * 2 + (p.1 : ℝ) * (p.2.2 : ℝ),
      (convex_Ioi (0 : ℝ)) (show (2 : ℝ) ∈ Ioi (0 : ℝ) by norm_num) p.2.2.property
        (sub_nonneg.mpr p.1.property.2) p.1.property.1 (sub_add_cancel 1 (p.1 : ℝ))⟩)
    continuous_toFun := by fun_prop
    map_zero_left := by intro p; ext <;> simp
    map_one_left := by intro p; ext <;> simp }⟩
  right_inv := by
    apply ContinuousMap.Homotopic.refl

def poleIntersectionHomotopyEquiv (v : sphere (0 : E) 1) :
    poleIntersection v ≃ₕ EquatorialSphere v :=
  (poleIntersectionHomeomorph v).toHomotopyEquiv.trans (productPositiveHomotopyEquiv _)


theorem poleIntersectionHomotopyEquiv_apply (v : sphere (0 : E) 1)
    (x : poleIntersection v) :
    (poleIntersectionHomotopyEquiv v x : (ℝ ∙ (v : E))ᗮ) =
      ‖stereographic (norm_eq_of_mem_sphere v) x.val‖⁻¹ •
        stereographic (norm_eq_of_mem_sphere v) x.val :=
  poleIntersectionHomeomorph_direction v x

theorem poleIntersectionHomotopyEquiv_symm_apply (v : sphere (0 : E) 1)
    (e : EquatorialSphere v) :
    (((poleIntersectionHomotopyEquiv v).symm e).val : E) = (e.val : E) := by
  have hh := poleIntersectionHomeomorph_symm_apply v e ⟨2, by norm_num⟩
  change (((poleIntersectionHomeomorph v).symm (e, ⟨2, by norm_num⟩)).val : E) = _
  rw [hh]
  norm_num [smul_smul]

def poleIntersectionRetractionHomotopy (v : sphere (0 : E) 1) :
    (ContinuousMap.id (poleIntersection v)).Homotopy
      ((poleIntersectionHomotopyEquiv v).symm.toFun.comp (poleIntersectionHomotopyEquiv v).toFun) where
  toFun p := (poleIntersectionHomeomorph v).symm
    ((poleIntersectionHomeomorph v p.2).1,
      ⟨(1 - (p.1 : ℝ)) * ((poleIntersectionHomeomorph v p.2).2 : ℝ) + (p.1 : ℝ) * 2,
        (convex_Ioi (0 : ℝ)) (poleIntersectionHomeomorph v p.2).2.property
          (show (2 : ℝ) ∈ Ioi (0 : ℝ) by norm_num)
          (sub_nonneg.mpr p.1.property.2) p.1.property.1 (sub_add_cancel 1 (p.1 : ℝ))⟩)
  continuous_toFun := by fun_prop
  map_zero_left x := by
    change (poleIntersectionHomeomorph v).symm _ = x
    convert (poleIntersectionHomeomorph v).symm_apply_apply x using 1
    ext
    simp
  map_one_left x := by
    change (poleIntersectionHomeomorph v).symm _ =
      (poleIntersectionHomeomorph v).symm ((poleIntersectionHomeomorph v x).1, ⟨2, by norm_num⟩)
    congr 1
    ext <;> simp


theorem poleIntersectionRetractionHomotopy_coordinates (v : sphere (0 : E) 1)
    (t : I) (x : poleIntersection v) :
    poleIntersectionHomeomorph v (poleIntersectionRetractionHomotopy v (t, x)) =
      ((poleIntersectionHomeomorph v x).1,
        ⟨(1 - (t : ℝ)) * ((poleIntersectionHomeomorph v x).2 : ℝ) + (t : ℝ) * 2,
          (convex_Ioi (0 : ℝ)) (poleIntersectionHomeomorph v x).2.property
            (show (2 : ℝ) ∈ Ioi (0 : ℝ) by norm_num)
            (sub_nonneg.mpr t.property.2) t.property.1 (sub_add_cancel 1 (t : ℝ))⟩) :=
  (poleIntersectionHomeomorph v).apply_symm_apply _


theorem poleIntersectionRetractionHomotopy_fixed (v : sphere (0 : E) 1)
    (t : I) (e : EquatorialSphere v) :
    poleIntersectionRetractionHomotopy v (t, (poleIntersectionHomotopyEquiv v).symm e) =
      (poleIntersectionHomotopyEquiv v).symm e := by
  apply (poleIntersectionHomeomorph v).injective
  rw [poleIntersectionRetractionHomotopy_coordinates]
  have heq : poleIntersectionHomeomorph v ((poleIntersectionHomotopyEquiv v).symm e) =
      (e, ⟨2, by norm_num⟩) := (poleIntersectionHomeomorph v).apply_symm_apply _
  rw [heq]
  apply Prod.ext
  · rfl
  · apply Subtype.ext
    dsimp
    ring

def equatorialSphereHomeomorph (n : ℕ) [Fact (finrank ℝ E = n + 1)]
    (v : sphere (0 : E) 1) :
    EquatorialSphere v ≃ₜ sphere (0 : EuclideanSpace ℝ (Fin n)) 1 :=
  ((OrthonormalBasis.fromOrthogonalSpanSingleton n (ne_zero_of_mem_unit_sphere v)).repr.toHomeomorph).subtype
    (fun w ↦ by
      simp only [mem_sphere, dist_zero_right]
      change ‖w‖ = 1 ↔ ‖(OrthonormalBasis.fromOrthogonalSpanSingleton n
        (ne_zero_of_mem_unit_sphere v)).repr w‖ = 1
      rw [LinearIsometryEquiv.norm_map])

theorem isEmpty_poleIntersection_of_finrank_one [Fact (finrank ℝ E = 1)]
    (v : sphere (0 : E) 1) : IsEmpty (poleIntersection v) := by
  have : Fact (finrank ℝ E = 0 + 1) := ⟨Fact.out⟩
  exact ⟨fun x ↦ isEmptyElim (equatorialSphereHomeomorph 0 v ((poleIntersectionHomeomorph v x).1))⟩


def euclideanNorth (n : ℕ) : sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 :=
  ⟨EuclideanSpace.single 0 1, by simp⟩


theorem euclidean_poleCover (n : ℕ) :
    poleComplement (euclideanNorth n) ⊔ poleComplement (-(euclideanNorth n)) = ⊤ :=
  poleComplement_sup _

def euclideanPoleIntersectionHomotopyEquiv (n : ℕ) :
    poleIntersection (euclideanNorth n) ≃ₕ sphere (0 : EuclideanSpace ℝ (Fin n)) 1 := by
  letI : Fact (finrank ℝ (EuclideanSpace ℝ (Fin (n + 1))) = n + 1) := ⟨by simp⟩
  exact (poleIntersectionHomotopyEquiv _).trans
    (equatorialSphereHomeomorph n _).toHomotopyEquiv


theorem isEmpty_euclideanZeroSphereIntersection : IsEmpty (poleIntersection (euclideanNorth 0)) := by
  let : Fact (finrank ℝ (EuclideanSpace ℝ (Fin (0 + 1))) = 1) := ⟨by simp⟩
  exact isEmpty_poleIntersection_of_finrank_one _

end Poincare.LocalDegree
