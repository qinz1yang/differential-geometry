import DifferentialGeometry.Topology.SimplicialComplex.FaceStar
import DifferentialGeometry.Topology.Simplex.OpenCell
import Mathlib.Topology.OpenPartialHomeomorph.Composition
import Mathlib.Analysis.InnerProductSpace.PiL2

set_option autoImplicit false
noncomputable section
open Set Metric

namespace Poincare.Topology.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [LinearOrder E]
  (K : Geometry.SimplicialComplex ℝ E) (s : Finset E) (hs : s ∈ K.faces)
  (hmax : IsMax (⟨s, hs⟩ : K.faces))

include hmax in
theorem mem_convexHull_of_mem_maximalFaceStar {x : E} (hx : x ∈ faceOpenStar K s) :
    x ∈ convexHull ℝ (s : Set E) := by
  obtain ⟨t, ht, hxt⟩ := Geometry.SimplicialComplex.mem_space_iff.mp hx.1
  have hst := subset_of_mem_faceOpenStar K s hx ht hxt
  have hts : t ⊆ s := hmax (show (⟨s, hs⟩ : K.faces) ≤ ⟨t, ht⟩ from hst)
  exact convexHull_mono (show (t : Set E) ⊆ s from hts) hxt

private theorem maximalFace_coordinate_mem_openCell
    (x : (Subtype.val : K.space → E) ⁻¹' faceOpenStar K s) :
    (geometricFaceHomeomorphism K hs).symm
      ⟨x.val.val, mem_convexHull_of_mem_maximalFaceStar K s hs hmax x.prop⟩ ∈
        Poincare.Simplex.openCell s := by
  rw [Poincare.Simplex.openCell_eq_compl_boundary]
  intro hb
  have hh := (vertexMap_mem_geometricFaceCostar_iff K hs _).mpr hb
  have he := congrArg (fun y : convexHull ℝ (s : Set E) ↦ y.val)
    ((geometricFaceHomeomorphism K hs).apply_symm_apply
      ⟨x.val.val, mem_convexHull_of_mem_maximalFaceStar K s hs hmax x.prop⟩)
  change Poincare.Simplex.vertexMap (fun i : s ↦ (i : E)) _ = x.val.val at he
  exact x.prop.2 (he ▸ hh)

omit [LinearOrder E] in
private theorem geometricFace_openCell_mem_star (a : Poincare.Simplex.openCell s) :
    (geometricFaceHomeomorphism K hs a.val).val ∈ faceOpenStar K s := by
  refine ⟨Geometry.SimplicialComplex.convexHull_subset_space hs
    (geometricFaceHomeomorphism K hs a.val).prop, ?_⟩
  intro hx
  have hb := (vertexMap_mem_geometricFaceCostar_iff K hs a.val).mp hx
  have ha : a.val ∉ Poincare.Simplex.boundary s := by
    simpa only [Poincare.Simplex.openCell_eq_compl_boundary, Set.mem_compl_iff] using a.prop
  exact ha hb

def maximalFaceStarHomeomorphism :
    ((Subtype.val : K.space → E) ⁻¹' faceOpenStar K s) ≃ₜ Poincare.Simplex.openCell s where
  toFun x := ⟨(geometricFaceHomeomorphism K hs).symm
    ⟨x.val.val, mem_convexHull_of_mem_maximalFaceStar K s hs hmax x.prop⟩,
    maximalFace_coordinate_mem_openCell K s hs hmax x⟩
  invFun a := ⟨⟨(geometricFaceHomeomorphism K hs a.val).val,
      Geometry.SimplicialComplex.convexHull_subset_space hs
        (geometricFaceHomeomorphism K hs a.val).prop⟩,
    geometricFace_openCell_mem_star K s hs a⟩
  left_inv x := by
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun y : convexHull ℝ (s : Set E) ↦ y.val)
      ((geometricFaceHomeomorphism K hs).apply_symm_apply
        ⟨x.val.val, mem_convexHull_of_mem_maximalFaceStar K s hs hmax x.prop⟩)
  right_inv a := by
    apply Subtype.ext
    exact (geometricFaceHomeomorphism K hs).symm_apply_apply a.val
  continuous_toFun := ((geometricFaceHomeomorphism K hs).symm.continuous.comp
    ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk _)).subtype_mk _
  continuous_invFun := (((continuous_subtype_val.comp
    ((geometricFaceHomeomorphism K hs).continuous.comp continuous_subtype_val)).subtype_mk _).subtype_mk _)


@[simp]
theorem maximalFaceStarHomeomorphism_symm_val (a : Poincare.Simplex.openCell s) :
    ((maximalFaceStarHomeomorphism K s hs hmax).symm a).val.val =
      (geometricFaceHomeomorphism K hs a.val).val := rfl

theorem maximalFaceStarHomeomorphism_apply_val
    (x : (Subtype.val : K.space → E) ⁻¹' faceOpenStar K s) :
    (geometricFaceHomeomorphism K hs
      (maximalFaceStarHomeomorphism K s hs hmax x).val).val = x.val.val :=
  congrArg (fun y : convexHull ℝ (s : Set E) ↦ y.val)
    ((geometricFaceHomeomorphism K hs).apply_symm_apply
      ⟨x.val.val, mem_convexHull_of_mem_maximalFaceStar K s hs hmax x.prop⟩)

def maximalFaceOpenBallHomeomorphism {n : ℕ} (hn : s.card = n + 1) :
    ((Subtype.val : K.space → E) ⁻¹' faceOpenStar K s) ≃ₜ ball (0 : Fin n → ℝ) 1 :=
  (maximalFaceStarHomeomorphism K s hs hmax).trans
    (((Poincare.Simplex.openCellReindexHomeomorph (s.orderIsoOfFin hn).toEquiv).symm).trans
      (Poincare.Simplex.stdSimplexOpenBallHomeomorph n))

theorem isOpenEmbedding_maximalFaceCoordinates {n : ℕ} (hn : s.card = n + 1) :
    Topology.IsOpenEmbedding (fun x ↦ (EuclideanSpace.equiv (Fin n) ℝ).symm
      (maximalFaceOpenBallHomeomorphism K s hs hmax hn x).val) :=
  (EuclideanSpace.equiv (Fin n) ℝ).symm.toHomeomorph.isOpenEmbedding.comp
    (isOpen_ball.isOpenEmbedding_subtypeVal.comp
      (maximalFaceOpenBallHomeomorphism K s hs hmax hn).isOpenEmbedding)

def maximalFaceEuclideanChart {n : ℕ} (hn : s.card = n + 1) :
    OpenPartialHomeomorph ((Subtype.val : K.space → E) ⁻¹' faceOpenStar K s)
      (EuclideanSpace ℝ (Fin n)) := by
  let : Nonempty ((Subtype.val : K.space → E) ⁻¹' faceOpenStar K s) :=
    ⟨⟨geometricFaceBarycenter K s hs, ⟨(geometricFaceBarycenter K s hs).prop, geometricFaceBarycenter_not_mem_costar K s hs⟩⟩⟩
  exact (isOpenEmbedding_maximalFaceCoordinates K s hs hmax hn).toOpenPartialHomeomorph _


@[simp]
theorem maximalFaceEuclideanChart_source {n : ℕ} (hn : s.card = n + 1) :
    (maximalFaceEuclideanChart K s hs hmax hn).source = Set.univ := rfl


@[simp]
theorem maximalFaceEuclideanChart_apply {n : ℕ} (hn : s.card = n + 1)
    (x : (Subtype.val : K.space → E) ⁻¹' faceOpenStar K s) :
    maximalFaceEuclideanChart K s hs hmax hn x =
      (EuclideanSpace.equiv (Fin n) ℝ).symm
        (maximalFaceOpenBallHomeomorphism K s hs hmax hn x).val := rfl

end Poincare.Topology.SimplicialComplex
