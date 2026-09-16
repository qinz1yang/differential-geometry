import DifferentialGeometry.Topology.PiecewiseLinear.EulerPolyhedra

namespace DifferentialGeometry.Topology.PiecewiseLinear

open DifferentialGeometry.Topology.SimplicialComplex

structure OpenCellProfile where
  vertices : ℕ
  edges : ℕ
  faces : ℕ

namespace OpenCellProfile

def eulerChar (C : OpenCellProfile) : ℤ := C.vertices - C.edges + C.faces

inductive Operation where
  | alpha
  | beta
  | gamma
  | delta

def apply (C : OpenCellProfile) : Operation → OpenCellProfile
  | .alpha => ⟨C.vertices + 1, C.edges + 1, C.faces⟩
  | .beta => ⟨C.vertices + 1, C.edges + 1, C.faces⟩
  | .gamma => ⟨C.vertices, C.edges + 1, C.faces + 1⟩
  | .delta => ⟨C.vertices, C.edges + 1, C.faces + 1⟩

theorem eulerChar_apply (C : OpenCellProfile) (o : Operation) :
    eulerChar (apply C o) = eulerChar C := by
  cases o <;> simp [apply, eulerChar] <;> omega

def applyOperations : OpenCellProfile → List Operation → OpenCellProfile
  | C, [] => C
  | C, o :: ops => applyOperations (apply C o) ops

theorem eulerChar_applyOperations (C : OpenCellProfile) (ops : List Operation) :
    eulerChar (applyOperations C ops) = eulerChar C := by
  induction ops generalizing C with
  | nil => rfl
  | cons o ops ih => rw [applyOperations, ih, eulerChar_apply]

def IsRefinement (C' C : OpenCellProfile) : Prop :=
  ∃ ops : List Operation, applyOperations C ops = C'

theorem eulerChar_eq_of_isRefinement {C' C : OpenCellProfile} (h : IsRefinement C' C) :
    eulerChar C' = eulerChar C := by
  obtain ⟨ops, rfl⟩ := h
  exact eulerChar_applyOperations C ops

end OpenCellProfile

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

noncomputable def simplicialOpenCellProfile
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces] : OpenCellProfile where
  vertices := (facesOfCard K.toPreAbstractSimplicialComplex 1).card
  edges := (facesOfCard K.toPreAbstractSimplicialComplex 2).card
  faces := (facesOfCard K.toPreAbstractSimplicialComplex 3).card

theorem simplicialOpenCellProfile_eulerChar
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hd : ∀ s ∈ K.faces, s.card ≤ 3) :
    (simplicialOpenCellProfile K).eulerChar = eulerChar K := by
  rw [eulerChar, faceEulerChar_eq_of_card_le_three K.toPreAbstractSimplicialComplex hd]
  rfl

open Classical in
theorem eulerChar_eq_of_faces_eq
    (K L : Geometry.SimplicialComplex ℝ E)
    [Finite K.faces] [Finite L.faces] (hfaces : K.faces = L.faces) :
    eulerChar K = eulerChar L := by
  apply faceEulerChar_congr
  ext s
  rw [hfaces]

open Classical in
theorem eulerChar_eq_add_sub_of_faces_union
    (M K L : Geometry.SimplicialComplex ℝ E)
    [Finite M.faces] [Finite K.faces] [Finite L.faces]
    (hfaces : M.faces = K.faces ∪ L.faces) :
    eulerChar M = eulerChar K + eulerChar L - eulerChar (intersectionComplex K L) := by
  have hM : M.toPreAbstractSimplicialComplex =
      K.toPreAbstractSimplicialComplex ⊔ L.toPreAbstractSimplicialComplex := by
    ext s
    change s ∈ M.faces ↔ s ∈ K.faces ∪ L.faces
    rw [hfaces]
  have hI : (intersectionComplex K L).toPreAbstractSimplicialComplex =
      K.toPreAbstractSimplicialComplex ⊓ L.toPreAbstractSimplicialComplex := by
    ext s
    rfl
  have hEuler := faceEulerChar_sup_add_faceEulerChar_inf
    K.toPreAbstractSimplicialComplex L.toPreAbstractSimplicialComplex
  have hMchar := faceEulerChar_congr hM
  have hIchar := faceEulerChar_congr hI
  unfold eulerChar
  rw [hMchar, hIchar]
  omega

open Classical in
theorem eulerChar_eq_zero_of_faces_eq_empty
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hfaces : K.faces = ∅) : eulerChar K = 0 := by
  have hK : K.toPreAbstractSimplicialComplex =
      (⊥ : PreAbstractSimplicialComplex E) := by
    ext s
    change s ∈ K.faces ↔ False
    rw [hfaces]
    simp
  unfold eulerChar
  exact (faceEulerChar_congr hK).trans faceEulerChar_bot

open Classical in
theorem eulerChar_eq_add_of_faces_disjoint_union
    (M K L : Geometry.SimplicialComplex ℝ E)
    [Finite M.faces] [Finite K.faces] [Finite L.faces]
    (hfaces : M.faces = K.faces ∪ L.faces) (hdisjoint : Disjoint K.faces L.faces) :
    eulerChar M = eulerChar K + eulerChar L := by
  have hI : (intersectionComplex K L).faces = ∅ :=
    Set.disjoint_iff_inter_eq_empty.mp hdisjoint
  rw [eulerChar_eq_add_sub_of_faces_union M K L hfaces,
    eulerChar_eq_zero_of_faces_eq_empty (intersectionComplex K L) hI, sub_zero]

open Classical in
theorem eulerChar_eq_add_of_faces_union_of_isPLSphere_one
    [FiniteDimensional ℝ E]
    (M K L : Geometry.SimplicialComplex ℝ E)
    [Finite M.faces] [Finite K.faces] [Finite L.faces]
    (hfaces : M.faces = K.faces ∪ L.faces)
    (hinter : IsPLSphere 1 (intersectionComplex K L).space) :
    eulerChar M = eulerChar K + eulerChar L := by
  rw [eulerChar_eq_add_sub_of_faces_union M K L hfaces,
    eulerChar_of_isPLSphere_one (intersectionComplex K L) hinter, sub_zero]

end DifferentialGeometry.Topology.PiecewiseLinear
