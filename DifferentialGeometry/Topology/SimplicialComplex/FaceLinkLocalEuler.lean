import DifferentialGeometry.Topology.SimplicialComplex.FaceStarContractible
import DifferentialGeometry.Topology.SimplicialComplex.FaceShellEulerCharacteristic
import DifferentialGeometry.Topology.SimplicialComplex.GeometricEulerCharacteristic
import DifferentialGeometry.Topology.Homology.Local.Manifold
import DifferentialGeometry.Topology.Homotopy.ConvexProduct

set_option autoImplicit false
noncomputable section
open Set CategoryTheory ContinuousMap DifferentialGeometry.Homology
namespace DifferentialGeometry.Topology.SimplicialComplex
universe u
variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [LinearOrder E]
  (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces] (s : Finset E)


def faceStarNeighborhoodHomeomorphism :
    ((Subtype.val : K.space → E) ⁻¹' faceOpenStar K s) ≃ₜ faceOpenStar K s where
  toFun x := ⟨x.val.val, x.property⟩
  invFun x := ⟨⟨x.val, x.property.1⟩, x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := (continuous_subtype_val.subtype_mk _).subtype_mk _

variable (hs : s ∈ K.faces)
include hs


def puncturedFaceOpenStarHomeomorphism :
    ({(⟨s.centroid ℝ id, geometricFaceBarycenter_mem_faceOpenStar K s hs⟩ : faceOpenStar K s)}ᶜ : Set (faceOpenStar K s)) ≃ₜ
      puncturedFaceOpenStar K s where
  toFun x := ⟨x.val.val, x.val.property, fun h => x.property (Subtype.ext h)⟩
  invFun x := ⟨⟨x.val, x.property.1⟩, fun h => x.property.2 (congrArg Subtype.val h)⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := (continuous_subtype_val.subtype_mk _).subtype_mk _

private theorem neighborhood_puncture_iff
    (y : (Subtype.val : K.space → E) ⁻¹' faceOpenStar K s) :
    y ∈ ({(⟨geometricFaceBarycenter K s hs,
        geometricFaceBarycenter_mem_faceOpenStar K s hs⟩ :
          (Subtype.val : K.space → E) ⁻¹' faceOpenStar K s)}ᶜ : Set _) ↔
      faceStarNeighborhoodHomeomorphism K s y ∈
        ({(⟨s.centroid ℝ id, geometricFaceBarycenter_mem_faceOpenStar K s hs⟩ : faceOpenStar K s)}ᶜ : Set _) :=
  not_congr (faceStarNeighborhoodHomeomorphism K s).injective.eq_iff.symm


def puncturedFaceStarHomotopyEquiv :
    puncturedFaceOpenStar K s ≃ₕ (geometricFaceShell K s).space :=
  (puncturedFaceStarHomeomorphism K s hs).toHomotopyEquiv.trans
    (DifferentialGeometry.HomotopyEquiv.productConvex _ (convex_Ioo (0 : ℝ) 1)
      ⟨1 / 2, by constructor <;> norm_num⟩)


@[simp]
theorem puncturedFaceStarHomotopyEquiv_symm_apply (y : (geometricFaceShell K s).space) :
    ((puncturedFaceStarHomotopyEquiv K s hs).symm y).val =
      (1 / 2 : ℝ) • s.centroid ℝ id + (1 / 2 : ℝ) • y.val := by
  change (1 / 2 : ℝ) • s.centroid ℝ id + (1 - 1 / 2 : ℝ) • y.val = _
  norm_num


theorem finiteHomologyType_puncturedFaceStar (k : Type u) [Field k] :
    finiteHomologyType k (TopCat.of (puncturedFaceOpenStar K s)) :=
  (finiteHomologyType_iff_of_homotopyEquiv k
    (X := TopCat.of (puncturedFaceOpenStar K s))
    (Y := TopCat.of (geometricFaceShell K s).space)
    (puncturedFaceStarHomotopyEquiv K s hs)).mpr
      (finiteHomologyType_geometricSpace (geometricFaceShell K s) k)


theorem eulerChar_puncturedFaceStar (k : Type u) [Field k] :
    eulerChar k (TopCat.of (puncturedFaceOpenStar K s)) =
      eulerChar k (TopCat.of (geometricFaceShell K s).space) :=
  eulerChar_eq_of_homotopyEquiv k
    (X := TopCat.of (puncturedFaceOpenStar K s))
    (Y := TopCat.of (geometricFaceShell K s).space)
    (puncturedFaceStarHomotopyEquiv K s hs)


theorem finiteHomologyType_localGeometricFace (k : Type u) [Field k] :
    DifferentialGeometry.HomologicalComplex.finiteHomologyType
      (relativeChainComplex (TopCat.of K.space)
        ({(geometricFaceBarycenter K s hs : K.space)}ᶜ : Set K.space)
        (ModuleCat.of k k)) := by
  let U : Set K.space := (Subtype.val : K.space → E) ⁻¹' faceOpenStar K s
  let x : K.space := geometricFaceBarycenter K s hs
  have hx : x ∈ U := geometricFaceBarycenter_mem_faceOpenStar K s hs
  have hf := (finiteHomologyType_iff_of_homeomorph k
    (X := TopCat.of ({(⟨s.centroid ℝ id, geometricFaceBarycenter_mem_faceOpenStar K s hs⟩ : faceOpenStar K s)}ᶜ : Set _))
    (Y := TopCat.of (puncturedFaceOpenStar K s))
    (puncturedFaceOpenStarHomeomorphism K s hs)).mpr
      (finiteHomologyType_puncturedFaceStar K s hs k)
  have hrel := finiteHomologyType_relativeChainComplex (TopCat.of (faceOpenStar K s))
    ({(⟨s.centroid ℝ id, geometricFaceBarycenter_mem_faceOpenStar K s hs⟩ : faceOpenStar K s)}ᶜ : Set _) k hf
    (finiteHomologyType_faceOpenStar K s hs k)
  let e := relativeChainIso (X := TopCat.of U) (Y := TopCat.of (faceOpenStar K s))
    (ModuleCat.of k k) (faceStarNeighborhoodHomeomorphism K s)
    (neighborhood_puncture_iff K s hs)
  have hn := (DifferentialGeometry.HomologicalComplex.finiteHomologyType_iff_of_quasiIso e.hom).mpr hrel
  exact (finiteHomologyType_puncturedNeighborhood_iff (TopCat.of K.space) U x hx k
    (isOpen_faceOpenStar K s)).mp hn


theorem relativeEulerChar_face_eq_one_sub_shell (k : Type u) [Field k] :
    relativeEulerChar (TopCat.of K.space)
      ({(geometricFaceBarycenter K s hs : K.space)}ᶜ : Set K.space) k =
        1 - eulerChar k (TopCat.of (geometricFaceShell K s).space) := by
  let U : Set K.space := (Subtype.val : K.space → E) ⁻¹' faceOpenStar K s
  let x : K.space := geometricFaceBarycenter K s hs
  have hx : x ∈ U := geometricFaceBarycenter_mem_faceOpenStar K s hs
  have he : ∀ y : U,
      y ∈ ({(⟨x, hx⟩ : U)}ᶜ : Set U) ↔
        faceStarNeighborhoodHomeomorphism K s y ∈
          ({(⟨s.centroid ℝ id, geometricFaceBarycenter_mem_faceOpenStar K s hs⟩ : faceOpenStar K s)}ᶜ : Set (faceOpenStar K s)) :=
    neighborhood_puncture_iff K s hs
  have hf := (finiteHomologyType_iff_of_homeomorph k
    (X := TopCat.of ({(⟨s.centroid ℝ id, geometricFaceBarycenter_mem_faceOpenStar K s hs⟩ : faceOpenStar K s)}ᶜ : Set _))
    (Y := TopCat.of (puncturedFaceOpenStar K s))
    (puncturedFaceOpenStarHomeomorphism K s hs)).mpr
      (finiteHomologyType_puncturedFaceStar K s hs k)
  calc
    _ = relativeEulerChar (TopCat.of U) ({(⟨x, hx⟩ : U)}ᶜ : Set U) k :=
      (relativeEulerChar_puncturedNeighborhood (TopCat.of K.space) U x hx k
        (isOpen_faceOpenStar K s)).symm
    _ = relativeEulerChar (TopCat.of (faceOpenStar K s))
        ({(⟨s.centroid ℝ id, geometricFaceBarycenter_mem_faceOpenStar K s hs⟩ : faceOpenStar K s)}ᶜ : Set _) k :=
      relativeEulerChar_eq_of_homeomorph (X := TopCat.of U)
        (Y := TopCat.of (faceOpenStar K s)) k (faceStarNeighborhoodHomeomorphism K s) he
    _ = 1 - eulerChar k (TopCat.of (geometricFaceShell K s).space) := by
      rw [relativeEulerChar_eq_sub (TopCat.of (faceOpenStar K s))
        ({(⟨s.centroid ℝ id, geometricFaceBarycenter_mem_faceOpenStar K s hs⟩ : faceOpenStar K s)}ᶜ : Set _) k hf (finiteHomologyType_faceOpenStar K s hs k),
        eulerChar_faceOpenStar K s hs k,
        eulerChar_eq_of_homeomorph k
          (X := TopCat.of ({(⟨s.centroid ℝ id, geometricFaceBarycenter_mem_faceOpenStar K s hs⟩ : faceOpenStar K s)}ᶜ : Set _))
          (Y := TopCat.of (puncturedFaceOpenStar K s)) (puncturedFaceOpenStarHomeomorphism K s hs),
        eulerChar_puncturedFaceStar K s hs k]


theorem faceEulerChar_faceShell_eq_one_sub_local (k : Type u) [Field k] :
    faceEulerChar (faceShell K.toPreAbstractSimplicialComplex s) =
      1 - relativeEulerChar (TopCat.of K.space)
        ({(geometricFaceBarycenter K s hs : K.space)}ᶜ : Set K.space) k := by
  have h := relativeEulerChar_face_eq_one_sub_shell K s hs k
  rw [eulerChar_geometricSpace_eq_faceEulerChar] at h
  change _ = 1 - faceEulerChar (faceShell K.toPreAbstractSimplicialComplex s) at h
  omega


theorem faceEulerChar_link_eq_one_sub_signed_local (k : Type u) [Field k] :
    faceEulerChar (link K.toPreAbstractSimplicialComplex s) =
      1 - (-1 : ℤ) ^ (s.card - 1) * relativeEulerChar (TopCat.of K.space)
        ({geometricFaceBarycenter K s hs}ᶜ : Set K.space) k := by
  have h := relativeEulerChar_face_eq_one_sub_shell K s hs k
  rw [eulerChar_geometricSpace_eq_faceEulerChar] at h
  have hfactor := one_sub_faceEulerChar_faceShell K.toPreAbstractSimplicialComplex s hs
  change _ = 1 - faceEulerChar (faceShell K.toPreAbstractSimplicialComplex s) at h
  have hsq : ((-1 : ℤ) ^ (s.card - 1)) * ((-1 : ℤ) ^ (s.card - 1)) = 1 := by
    rw [← mul_pow]
    norm_num
  rw [h, hfactor, ← mul_assoc, hsq, one_mul]
  ring

end DifferentialGeometry.Topology.SimplicialComplex
