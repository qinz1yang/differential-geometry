import DifferentialGeometry.Topology.Simplex.Face
import DifferentialGeometry.Topology.Simplex.BoundaryRetraction
import Mathlib.Topology.OpenPartialHomeomorph.Constructions

noncomputable section

open Set

namespace DifferentialGeometry.Simplex

universe u

variable {n : ℕ}

def faceToBoundary (i : Fin (n + 2)) :
    C(stdSimplex ℝ (Fin (n + 1)), boundary (Fin (n + 2))) :=
  ⟨fun p => ⟨stdSimplex.map i.succAbove p, ⟨i, map_succAbove_apply_pivot i p⟩⟩,
    (stdSimplex.continuous_map i.succAbove).subtype_mk _⟩

@[simp]
theorem faceToBoundary_val (i : Fin (n + 2))
    (p : stdSimplex ℝ (Fin (n + 1))) :
    (faceToBoundary i p).val = stdSimplex.map i.succAbove p := rfl

theorem faceToBoundary_injective (i : Fin (n + 2)) :
    Function.Injective (faceToBoundary i) := by
  intro p q h
  apply Subtype.ext
  funext j
  have hj := congrArg (fun z : boundary (Fin (n + 2)) => z.val.val (i.succAbove j)) h
  exact (map_succAbove_apply_image i p j).symm.trans
    (hj.trans (map_succAbove_apply_image i q j))

private def faceInterior (i : Fin (n + 2)) : Set (boundary (Fin (n + 2))) :=
  {p | ∀ j : Fin (n + 1), 0 < p.val.val (i.succAbove j)}

private theorem faceInterior_pivot_eq_zero (i : Fin (n + 2))
    {p : boundary (Fin (n + 2))} (hp : p ∈ faceInterior i) : p.val.val i = 0 := by
  obtain ⟨j, hj⟩ := p.property
  by_cases hji : j = i
  · exact hji ▸ hj
  · obtain ⟨k, rfl⟩ := Fin.exists_succAbove_eq hji
    exact False.elim ((ne_of_gt (hp k)) hj)

private def faceFromBoundary (i : Fin (n + 2))
    (p : boundary (Fin (n + 2))) : stdSimplex ℝ (Fin (n + 1)) :=
  if hp : p.val.val i = 0 then faceDelete i ⟨p.val, hp⟩ else stdSimplex.barycenter

private theorem faceFromBoundary_apply (i : Fin (n + 2))
    {p : boundary (Fin (n + 2))} (hp : p.val.val i = 0) :
    faceFromBoundary i p = faceDelete i ⟨p.val, hp⟩ := by
  simp [faceFromBoundary, hp]

private theorem faceFromBoundary_faceToBoundary (i : Fin (n + 2))
    (p : stdSimplex ℝ (Fin (n + 1))) :
    faceFromBoundary i (faceToBoundary i p) = p := by
  rw [faceFromBoundary_apply i (map_succAbove_apply_pivot i p)]
  exact faceDelete_faceInsert i p

def faceOpenPartialHomeomorph (i : Fin (n + 2)) :
    OpenPartialHomeomorph (stdSimplex ℝ (Fin (n + 1))) (boundary (Fin (n + 2))) where
  toFun := faceToBoundary i
  invFun := faceFromBoundary i
  source := (boundary (Fin (n + 1)))ᶜ
  target := faceInterior i
  map_source' := by
    intro p hp j
    change 0 < (stdSimplex.map i.succAbove p).val (i.succAbove j)
    rw [map_succAbove_apply_image]
    exact lt_of_le_of_ne (p.property.1 j) (Ne.symm (fun hj => hp ⟨j, hj⟩))
  map_target' := by
    intro p hp
    rw [faceFromBoundary_apply i (faceInterior_pivot_eq_zero i hp)]
    rintro ⟨j, hj⟩
    exact (ne_of_gt (hp j)) hj
  left_inv' := fun p _ => faceFromBoundary_faceToBoundary i p
  right_inv' := by
    intro p hp
    rw [faceFromBoundary_apply i (faceInterior_pivot_eq_zero i hp)]
    apply Subtype.ext
    change stdSimplex.map i.succAbove (faceDelete i ⟨p.val, _⟩) = p.val
    exact congrArg Subtype.val (faceInsert_faceDelete i ⟨p.val, faceInterior_pivot_eq_zero i hp⟩)
  open_source := isClosed_boundary.isOpen_compl
  open_target := by
    change IsOpen {p : boundary (Fin (n + 2)) | ∀ j : Fin (n + 1), 0 < p.val.val (i.succAbove j)}
    simp only [ofPred_forall]
    apply isOpen_iInter_of_finite
    intro j
    exact isOpen_lt continuous_const ((continuous_apply (i.succAbove j)).comp
      (continuous_subtype_val.comp continuous_subtype_val))
  continuousOn_toFun := (faceToBoundary i).continuous.continuousOn
  continuousOn_invFun := by
    rw [continuousOn_iff_continuous_domRestrict]
    let f : C(faceInterior i, face i) :=
      ⟨fun p => ⟨p.val.val, faceInterior_pivot_eq_zero i p.property⟩,
        (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _⟩
    have he : (fun p : faceInterior i => faceFromBoundary i p.val) =
        fun p : faceInterior i => faceDelete i (f p) := by
      funext p
      exact faceFromBoundary_apply i (faceInterior_pivot_eq_zero i p.property)
    change Continuous (fun p : faceInterior i => faceFromBoundary i p.val)
    rw [he]
    exact (faceDelete i).continuous.comp f.continuous

@[simp]
theorem faceOpenPartialHomeomorph_apply (i : Fin (n + 2))
    (p : stdSimplex ℝ (Fin (n + 1))) :
    faceOpenPartialHomeomorph i p = faceToBoundary i p := rfl

@[simp]
theorem faceOpenPartialHomeomorph_source (i : Fin (n + 2)) :
    (faceOpenPartialHomeomorph i).source = (boundary (Fin (n + 1)))ᶜ := rfl

@[simp]
theorem faceOpenPartialHomeomorph_target (i : Fin (n + 2)) :
    (faceOpenPartialHomeomorph i).target =
      {p | ∀ j : Fin (n + 1), 0 < p.val.val (i.succAbove j)} := rfl


def liftedFaceToBoundary (i : Fin (n + 2)) :
    C(ULift.{u} (stdSimplex ℝ (Fin (n + 1))), ULift.{u} (boundary (Fin (n + 2)))) :=
  ⟨fun p => ULift.up (faceToBoundary i p.down),
    continuous_uliftUp.comp ((faceToBoundary i).continuous.comp continuous_uliftDown)⟩

theorem liftedFaceToBoundary_injective (i : Fin (n + 2)) :
    Function.Injective (liftedFaceToBoundary.{u} i) := by
  intro p q h
  apply ULift.ext
  exact faceToBoundary_injective i (congrArg ULift.down h)

def liftedFaceOpenPartialHomeomorph (i : Fin (n + 2)) :
    OpenPartialHomeomorph (ULift.{u} (stdSimplex ℝ (Fin (n + 1))))
      (ULift.{u} (boundary (Fin (n + 2)))) :=
  (Homeomorph.ulift.transOpenPartialHomeomorph
    (faceOpenPartialHomeomorph i)).transHomeomorph Homeomorph.ulift.symm

@[simp]
theorem liftedFaceOpenPartialHomeomorph_apply (i : Fin (n + 2))
    (p : ULift.{u} (stdSimplex ℝ (Fin (n + 1)))) :
    liftedFaceOpenPartialHomeomorph i p = liftedFaceToBoundary i p := rfl

@[simp]
theorem liftedFaceOpenPartialHomeomorph_source (i : Fin (n + 2)) :
    (liftedFaceOpenPartialHomeomorph.{u} i).source =
      {p | p.down ∈ (boundary (Fin (n + 1)))ᶜ} := rfl

theorem liftedFaceToBoundary_mapsTo (i : Fin (n + 2))
    (p : ULift.{u} (stdSimplex ℝ (Fin (n + 1)))) :
    MapsTo (liftedFaceToBoundary i) ({p}ᶜ : Set _)
      ({liftedFaceToBoundary i p}ᶜ : Set _) :=
  fun _ hq h => hq (liftedFaceToBoundary_injective i h)

end DifferentialGeometry.Simplex
