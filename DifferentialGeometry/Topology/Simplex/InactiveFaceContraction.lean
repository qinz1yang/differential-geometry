import DifferentialGeometry.Topology.Simplex.VertexContraction
import DifferentialGeometry.Topology.Simplex.HomotopyExtension

noncomputable section

open ContinuousMap

namespace DifferentialGeometry.Simplex

variable {n : ℕ}

private def inactiveDisk : Set (boundary (Fin (n + 3))) :=
  {p | ∃ j : Fin (n + 3), j ≠ 0 ∧ p.val.val j = 0}

private theorem vertexContraction_mem_inactiveDisk (t : unitInterval) (q : inactiveDisk (n := n)) :
    ∃ j : Fin (n + 3), j ≠ 0 ∧ (vertexContraction (0 : Fin (n + 3)) (t, q.1.1)).val j = 0 := by
  obtain ⟨j, hj, hz⟩ := q.2
  refine ⟨j, hj, ?_⟩
  rw [vertexContraction_apply]
  simp [hz, Ne.symm hj]

private def inactiveDiskContraction :
    C(unitInterval × inactiveDisk (n := n), inactiveDisk (n := n)) where
  toFun z :=
    ⟨⟨vertexContraction (0 : Fin (n + 3)) (z.1, z.2.1.1), by
      obtain ⟨j, hj, hz⟩ := vertexContraction_mem_inactiveDisk (n := n) z.1 z.2
      exact ⟨j, hz⟩⟩, vertexContraction_mem_inactiveDisk (n := n) z.1 z.2⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply Continuous.subtype_mk
    exact (vertexContraction (I := Fin (n + 3)) (0 : Fin (n + 3))).continuous.comp
      (continuous_fst.prodMk
        (continuous_subtype_val.comp (continuous_subtype_val.comp continuous_snd)))

private def oppositeFaceBoundaryToInactive :
    C(boundary (Fin (n + 2)), inactiveDisk (n := n)) where
  toFun q :=
    ⟨⟨stdSimplex.map (0 : Fin (n + 3)).succAbove q.1,
      ⟨0, map_succAbove_apply_pivot (0 : Fin (n + 3)) q.1⟩⟩, by
      obtain ⟨j, hz⟩ := q.2
      refine ⟨(0 : Fin (n + 3)).succAbove j, Fin.succAbove_ne _ _, ?_⟩
      rw [map_succAbove_apply_image]
      exact hz⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply Continuous.subtype_mk
    exact (stdSimplex.continuous_map (0 : Fin (n + 3)).succAbove).comp continuous_subtype_val

private def inactiveDiskBoundaryInclusion :
    C(inactiveDisk (n := n), boundary (Fin (n + 3))) :=
  ⟨Subtype.val, continuous_subtype_val⟩

private def oppositeFaceBoundaryContraction :
    C(unitInterval × boundary (Fin (n + 2)), boundary (Fin (n + 3))) :=
  (inactiveDiskBoundaryInclusion (n := n)).comp
    ((inactiveDiskContraction (n := n)).comp
      (ContinuousMap.prodMap (ContinuousMap.id unitInterval) (oppositeFaceBoundaryToInactive (n := n))))

private theorem oppositeFaceBoundaryContraction_zero (q : boundary (Fin (n + 2))) :
    oppositeFaceBoundaryContraction (n := n) (0, q) =
      ⟨stdSimplex.map (0 : Fin (n + 3)).succAbove q.1,
        ⟨0, map_succAbove_apply_pivot (0 : Fin (n + 3)) q.1⟩⟩ := by
  apply Subtype.ext
  exact vertexContraction_zero (0 : Fin (n + 3)) _

private def boundaryFaceInclusion (i : Fin (n + 3)) :
    C(stdSimplex ℝ (Fin (n + 2)), boundary (Fin (n + 3))) where
  toFun p := ⟨stdSimplex.map i.succAbove p, ⟨i, map_succAbove_apply_pivot i p⟩⟩
  continuous_toFun := (stdSimplex.continuous_map i.succAbove).subtype_mk _

private def inactiveFaceInclusion (i : Fin (n + 3)) (hi : i ≠ 0) :
    C(stdSimplex ℝ (Fin (n + 2)), inactiveDisk (n := n)) where
  toFun p := ⟨boundaryFaceInclusion (n := n) i p, ⟨i, hi, map_succAbove_apply_pivot i p⟩⟩
  continuous_toFun := (boundaryFaceInclusion (n := n) i).continuous.subtype_mk _

private def inactiveFaceContraction (i : Fin (n + 3)) (hi : i ≠ 0) :
    C(unitInterval × stdSimplex ℝ (Fin (n + 2)), boundary (Fin (n + 3))) :=
  (inactiveDiskBoundaryInclusion (n := n)).comp
    ((inactiveDiskContraction (n := n)).comp
      (ContinuousMap.prodMap (ContinuousMap.id unitInterval) (inactiveFaceInclusion (n := n) i hi)))

private theorem exists_boundaryHomotopy_contraction_inactiveDisk :
    ∃ K : C(unitInterval × boundary (Fin (n + 3)), boundary (Fin (n + 3))),
      (∀ p, K (0, p) = p) ∧
      (∀ (t : unitInterval) (p : boundary (Fin (n + 3))), p ∈ inactiveDisk (n := n) →
        (K (t, p)).val = vertexContraction (0 : Fin (n + 3)) (t, p.val)) := by
  classical
  obtain ⟨F, hF, hside⟩ := exists_continuous_homotopy_extension (n + 1)
    (boundaryFaceInclusion (n := n) 0) (oppositeFaceBoundaryContraction (n := n))
      (oppositeFaceBoundaryContraction_zero (n := n))
  let L (i : Fin (n + 3)) : C(unitInterval × stdSimplex ℝ (Fin (n + 2)), boundary (Fin (n + 3))) :=
    if hi : i = 0 then F else inactiveFaceContraction (n := n) i hi
  have hL (i : Fin (n + 3)) (j : Fin (n + 2)) (t : unitInterval)
      (p : stdSimplex ℝ (Fin (n + 1))) :
      (L i (t, stdSimplex.map j.succAbove p)).val =
        vertexContraction (0 : Fin (n + 3))
          (t, stdSimplex.map i.succAbove (stdSimplex.map j.succAbove p)) := by
    by_cases hi : i = 0
    · subst i
      simp only [L, dif_pos rfl]
      exact congrArg Subtype.val (hside t
        ⟨stdSimplex.map j.succAbove p, ⟨j, map_succAbove_apply_pivot j p⟩⟩)
    · simp only [L, dif_neg hi]
      rfl
  have hfaces (i : Fin (n + 3)) (j : Fin (n + 2)) (t : unitInterval)
      (p : stdSimplex ℝ (Fin (n + 1))) :
      L i (t, stdSimplex.map j.succAbove p) =
        L (i.succAbove j) (t, stdSimplex.map (j.predAbove i).succAbove p) := by
    apply Subtype.ext
    rw [hL, hL]
    congr 2
    rw [stdSimplex.map_comp_apply, stdSimplex.map_comp_apply]
    congr 1
    funext k
    exact (Fin.succAbove_succAbove_succAbove_predAbove i j k).symm
  let G (i : Fin (n + 3)) : C(stdSimplex ℝ (Fin (n + 2)), C(unitInterval, boundary (Fin (n + 3)))) :=
    ((L i).comp ContinuousMap.prodSwap).curry
  have hG (i : Fin (n + 3)) (j : Fin (n + 2)) (p : stdSimplex ℝ (Fin (n + 1))) :
      G i (stdSimplex.map j.succAbove p) =
        G (i.succAbove j) (stdSimplex.map (j.predAbove i).succAbove p) := by
    apply ContinuousMap.ext
    intro t
    exact hfaces i j t p
  let K : C(unitInterval × boundary (Fin (n + 3)), boundary (Fin (n + 3))) :=
    (boundaryDesc G hG).uncurry.comp ContinuousMap.prodSwap
  have hK (i : Fin (n + 3)) (t : unitInterval) (p : stdSimplex ℝ (Fin (n + 2))) :
      K (t, boundaryFaceInclusion (n := n) i p) = L i (t, p) := by
    change boundaryDesc G hG ⟨stdSimplex.map i.succAbove p,
      ⟨i, map_succAbove_apply_pivot i p⟩⟩ t = L i (t, p)
    rw [boundaryDesc_face]
    rfl
  refine ⟨K, ?_, ?_⟩
  · intro p
    obtain ⟨i, hi⟩ := p.property
    let q := faceDelete i ⟨p.val, hi⟩
    have hq : boundaryFaceInclusion (n := n) i q = p := by
      apply Subtype.ext
      change stdSimplex.map i.succAbove q = p.val
      exact congrArg (fun r : face i => r.val) (faceInsert_faceDelete i ⟨p.val, hi⟩)
    rw [← hq, hK]
    by_cases hi0 : i = 0
    · subst i
      exact hF q
    · simp only [L, dif_neg hi0]
      apply Subtype.ext
      exact vertexContraction_zero (0 : Fin (n + 3)) _
  · intro t p hp
    obtain ⟨i, hi0, hi⟩ := hp
    let q := faceDelete i ⟨p.val, hi⟩
    have hq : boundaryFaceInclusion (n := n) i q = p := by
      apply Subtype.ext
      change stdSimplex.map i.succAbove q = p.val
      exact congrArg (fun r : face i => r.val) (faceInsert_faceDelete i ⟨p.val, hi⟩)
    rw [← hq, hK]
    simp only [L, dif_neg hi0]
    rfl

theorem exists_boundary_homotopy_contracting_faces_through_zero (n : ℕ) :
    ∃ K : C(unitInterval × boundary (Fin (n + 3)), boundary (Fin (n + 3))),
      (∀ p, K (0, p) = p) ∧
      (∀ (t : unitInterval) (p : boundary (Fin (n + 3))),
        (∃ j : Fin (n + 3), j ≠ 0 ∧ p.val.val j = 0) →
        (K (t, p)).val = vertexContraction (0 : Fin (n + 3)) (t, p.val)) :=
  exists_boundaryHomotopy_contraction_inactiveDisk (n := n)

theorem exists_boundary_homotopy_collapsing_faces_through_zero (n : ℕ) :
    ∃ K : C(unitInterval × boundary (Fin (n + 3)), boundary (Fin (n + 3))),
      (∀ p, K (0, p) = p) ∧
      (∀ p, (∃ j : Fin (n + 3), j ≠ 0 ∧ p.val.val j = 0) →
        (K (1, p)).val = stdSimplex.vertex (S := ℝ) (0 : Fin (n + 3))) ∧
      ∀ (t : unitInterval) p,
        (∃ j : Fin (n + 3), j ≠ 0 ∧ p.val.val j = 0) →
          ∃ j : Fin (n + 3), j ≠ 0 ∧ (K (t, p)).val.val j = 0 := by
  obtain ⟨K, hK0, hKA⟩ := exists_boundary_homotopy_contracting_faces_through_zero n
  refine ⟨K, hK0, ?_, ?_⟩
  · intro p hp
    exact (hKA 1 p hp).trans (vertexContraction_one (0 : Fin (n + 3)) p.val)
  · intro t p hp
    obtain ⟨j, hj, hz⟩ := hp
    refine ⟨j, hj, ?_⟩
    rw [hKA t p ⟨j, hj, hz⟩, vertexContraction_apply]
    simp [hz, Ne.symm hj]

end DifferentialGeometry.Simplex
