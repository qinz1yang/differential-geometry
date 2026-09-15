import DifferentialGeometry.Topology.Simplex.BoundaryGluing
import Mathlib.Topology.Homotopy.Basic

noncomputable section

namespace DifferentialGeometry.Simplex

open ContinuousMap

variable {n : ℕ} {X : Type*} [TopologicalSpace X]
  {f g : Fin (n + 3) → C(stdSimplex ℝ (Fin (n + 2)), X)}

private def boundaryHomotopyMap
    (H : ∀ i, (f i).Homotopy (g i))
    (h : ∀ (i : Fin (n + 3)) (j : Fin (n + 2))
      (t : unitInterval) (p : stdSimplex ℝ (Fin (n + 1))),
      H i (t, stdSimplex.map j.succAbove p) =
        H (i.succAbove j) (t, stdSimplex.map (j.predAbove i).succAbove p)) :
    C(unitInterval × boundary (Fin (n + 3)), X) :=
  let F i := ((H i).toContinuousMap.comp ContinuousMap.prodSwap).curry
  let hF : ∀ (i : Fin (n + 3)) (j : Fin (n + 2))
      (p : stdSimplex ℝ (Fin (n + 1))),
      F i (stdSimplex.map j.succAbove p) =
        F (i.succAbove j) (stdSimplex.map (j.predAbove i).succAbove p) := by
    intro i j p
    ext t
    exact h i j t p
  (boundaryDesc F hF).uncurry.comp ContinuousMap.prodSwap

private theorem boundaryHomotopyMap_face
    (H : ∀ i, (f i).Homotopy (g i))
    (h : ∀ (i : Fin (n + 3)) (j : Fin (n + 2))
      (t : unitInterval) (p : stdSimplex ℝ (Fin (n + 1))),
      H i (t, stdSimplex.map j.succAbove p) =
        H (i.succAbove j) (t, stdSimplex.map (j.predAbove i).succAbove p))
    (i : Fin (n + 3)) (t : unitInterval) (p : stdSimplex ℝ (Fin (n + 2))) :
    boundaryHomotopyMap H h
      (t, ⟨stdSimplex.map i.succAbove p, ⟨i, map_succAbove_apply_pivot i p⟩⟩) =
      H i (t, p) := by
  dsimp only [boundaryHomotopyMap]
  simp only [ContinuousMap.comp_apply, ContinuousMap.prodSwap_apply,
    ContinuousMap.uncurry_apply, Function.uncurry_apply_pair, boundaryDesc_face,
    ContinuousMap.curry_apply]
  rfl

def boundaryHomotopy
    (hf : ∀ (i : Fin (n + 3)) (j : Fin (n + 2))
      (p : stdSimplex ℝ (Fin (n + 1))),
      f i (stdSimplex.map j.succAbove p) =
        f (i.succAbove j) (stdSimplex.map (j.predAbove i).succAbove p))
    (hg : ∀ (i : Fin (n + 3)) (j : Fin (n + 2))
      (p : stdSimplex ℝ (Fin (n + 1))),
      g i (stdSimplex.map j.succAbove p) =
        g (i.succAbove j) (stdSimplex.map (j.predAbove i).succAbove p))
    (H : ∀ i, (f i).Homotopy (g i))
    (h : ∀ (i : Fin (n + 3)) (j : Fin (n + 2))
      (t : unitInterval) (p : stdSimplex ℝ (Fin (n + 1))),
      H i (t, stdSimplex.map j.succAbove p) =
        H (i.succAbove j) (t, stdSimplex.map (j.predAbove i).succAbove p)) :
    (boundaryDesc f hf).Homotopy (boundaryDesc g hg) where
  toContinuousMap := boundaryHomotopyMap H h
  map_zero_left p := by
    obtain ⟨i, hi⟩ := p.property
    let q := faceDelete i ⟨p.val, hi⟩
    have he : p = ⟨stdSimplex.map i.succAbove q,
        ⟨i, map_succAbove_apply_pivot i q⟩⟩ :=
      Subtype.ext (congrArg Subtype.val (faceInsert_faceDelete i ⟨p.val, hi⟩)).symm
    rw [he]
    change (boundaryHomotopyMap H h (0, ⟨stdSimplex.map i.succAbove q,
      ⟨i, map_succAbove_apply_pivot i q⟩⟩)) = _
    rw [boundaryHomotopyMap_face, boundaryDesc_face]
    exact (H i).apply_zero q
  map_one_left p := by
    obtain ⟨i, hi⟩ := p.property
    let q := faceDelete i ⟨p.val, hi⟩
    have he : p = ⟨stdSimplex.map i.succAbove q,
        ⟨i, map_succAbove_apply_pivot i q⟩⟩ :=
      Subtype.ext (congrArg Subtype.val (faceInsert_faceDelete i ⟨p.val, hi⟩)).symm
    rw [he]
    change (boundaryHomotopyMap H h (1, ⟨stdSimplex.map i.succAbove q,
      ⟨i, map_succAbove_apply_pivot i q⟩⟩)) = _
    rw [boundaryHomotopyMap_face, boundaryDesc_face]
    exact (H i).apply_one q

theorem boundaryHomotopy_face
    (hf : ∀ (i : Fin (n + 3)) (j : Fin (n + 2))
      (p : stdSimplex ℝ (Fin (n + 1))),
      f i (stdSimplex.map j.succAbove p) =
        f (i.succAbove j) (stdSimplex.map (j.predAbove i).succAbove p))
    (hg : ∀ (i : Fin (n + 3)) (j : Fin (n + 2))
      (p : stdSimplex ℝ (Fin (n + 1))),
      g i (stdSimplex.map j.succAbove p) =
        g (i.succAbove j) (stdSimplex.map (j.predAbove i).succAbove p))
    (H : ∀ i, (f i).Homotopy (g i))
    (h : ∀ (i : Fin (n + 3)) (j : Fin (n + 2))
      (t : unitInterval) (p : stdSimplex ℝ (Fin (n + 1))),
      H i (t, stdSimplex.map j.succAbove p) =
        H (i.succAbove j) (t, stdSimplex.map (j.predAbove i).succAbove p))
    (i : Fin (n + 3)) (t : unitInterval) (p : stdSimplex ℝ (Fin (n + 2))) :
    boundaryHomotopy hf hg H h
      (t, ⟨stdSimplex.map i.succAbove p, ⟨i, map_succAbove_apply_pivot i p⟩⟩) =
      H i (t, p) :=
  boundaryHomotopyMap_face H h i t p

end DifferentialGeometry.Simplex
