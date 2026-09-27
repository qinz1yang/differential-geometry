import DifferentialGeometry.Topology.Homotopy.CubicalBoundary
import DifferentialGeometry.Topology.Simplex.TriangleGenLoop
import DifferentialGeometry.Topology.Simplex.CubicalBoundaryHomotopy
import DifferentialGeometry.Topology.Homotopy.CoordinateSwap
import DifferentialGeometry.Topology.Simplex.TetrahedronOneSkeleton

noncomputable section
open Set ContinuousMap
open scoped unitInterval
namespace DifferentialGeometry.Topology

variable {X : Type*} [TopologicalSpace X] {x : X}

private abbrev Other := {j : Fin 2 // j ≠ 0}

private theorem other_eq (j : Other) : j = ⟨1, by decide⟩ := by
  apply Subtype.ext
  have h := j.property
  rcases j with ⟨j, hj⟩
  fin_cases j <;> simp_all

private def cubeLoop (G : C(I × I × I, X))
    (hG : ∀ s t u, (s = 0 ∨ s = 1) ∨
      ((t = 0 ∨ t = 1) ∧ (u = 0 ∨ u = 1)) → G (s, t, u) = x)
    (t u : I) : GenLoop Other X x :=
  ⟨⟨fun v => G (v ⟨1, by decide⟩, t, u), by fun_prop⟩, by
    rintro v ⟨i, hi⟩
    rw [other_eq i] at hi
    exact hG _ _ _ (Or.inl hi)⟩

private def cubeFace0 (G : C(I × I × I, X))
    (hG : ∀ s t u, (s = 0 ∨ s = 1) ∨
      ((t = 0 ∨ t = 1) ∧ (u = 0 ∨ u = 1)) → G (s, t, u) = x) :
    GenLoop (Fin 2) X x :=
  ⟨⟨fun v => G (v 1, 0, v 0), by fun_prop⟩, by
    rintro v ⟨i, hi⟩
    fin_cases i
    · exact hG _ _ _ (Or.inr ⟨Or.inl rfl, hi⟩)
    · exact hG _ _ _ (Or.inl hi)⟩

private def cubeFace1 (G : C(I × I × I, X))
    (hG : ∀ s t u, (s = 0 ∨ s = 1) ∨
      ((t = 0 ∨ t = 1) ∧ (u = 0 ∨ u = 1)) → G (s, t, u) = x) :
    GenLoop (Fin 2) X x :=
  ⟨⟨fun v => G (v 1, 1, v 0), by fun_prop⟩, by
    rintro v ⟨i, hi⟩
    fin_cases i
    · exact hG _ _ _ (Or.inr ⟨Or.inr rfl, hi⟩)
    · exact hG _ _ _ (Or.inl hi)⟩

private def cubeFace2 (G : C(I × I × I, X))
    (hG : ∀ s t u, (s = 0 ∨ s = 1) ∨
      ((t = 0 ∨ t = 1) ∧ (u = 0 ∨ u = 1)) → G (s, t, u) = x) :
    GenLoop (Fin 2) X x :=
  ⟨⟨fun v => G (v 1, v 0, 0), by fun_prop⟩, by
    rintro v ⟨i, hi⟩
    fin_cases i
    · exact hG _ _ _ (Or.inr ⟨hi, Or.inl rfl⟩)
    · exact hG _ _ _ (Or.inl hi)⟩

private def cubeFace3 (G : C(I × I × I, X))
    (hG : ∀ s t u, (s = 0 ∨ s = 1) ∨
      ((t = 0 ∨ t = 1) ∧ (u = 0 ∨ u = 1)) → G (s, t, u) = x) :
    GenLoop (Fin 2) X x :=
  ⟨⟨fun v => G (v 1, v 0, 1), by fun_prop⟩, by
    rintro v ⟨i, hi⟩
    fin_cases i
    · exact hG _ _ _ (Or.inr ⟨hi, Or.inr rfl⟩)
    · exact hG _ _ _ (Or.inl hi)⟩

private theorem homotopyGroup_cube_faces_relation
    (G : C(I × I × I, X))
    (hG : ∀ s t u, (s = 0 ∨ s = 1) ∨
      ((t = 0 ∨ t = 1) ∧ (u = 0 ∨ u = 1)) → G (s, t, u) = x) :
    ((· * ·) : _ → _ → HomotopyGroup (Fin 2) X x)
        ⟦cubeFace3 G hG⟧ ⟦cubeFace0 G hG⟧ =
      ((· * ·) : _ → _ → HomotopyGroup (Fin 2) X x)
        ⟦cubeFace1 G hG⟧ ⟦cubeFace2 G hG⟧ := by
  let H : C(I × I, GenLoop Other X x) :=
    ⟨fun p => cubeLoop G hG p.1 p.2, by
      apply Continuous.subtype_mk
      apply continuous_of_continuous_uncurry
      change Continuous (fun p : (I × I) × (Other → I) =>
        G (p.2 ⟨1, by decide⟩, p.1.1, p.1.2))
      fun_prop⟩
  apply homotopyGroup_mul_eq_mul_of_square (i := 0)
    (a := cubeFace0 G hG) (b := cubeFace1 G hG)
    (c := cubeFace2 G hG) (d := cubeFace3 G hG) H
  · intro t
    ext v
    change G (v ⟨1, by decide⟩, 0, t) = G ((Cube.insertAt (0 : Fin 2) (t, v)) 1, 0, (Cube.insertAt (0 : Fin 2) (t, v)) 0)
    simp
  · intro t
    ext v
    change G (v ⟨1, by decide⟩, 1, t) = G ((Cube.insertAt (0 : Fin 2) (t, v)) 1, 1, (Cube.insertAt (0 : Fin 2) (t, v)) 0)
    simp
  · intro t
    ext v
    change G (v ⟨1, by decide⟩, t, 0) = G ((Cube.insertAt (0 : Fin 2) (t, v)) 1, (Cube.insertAt (0 : Fin 2) (t, v)) 0, 0)
    simp
  · intro t
    ext v
    change G (v ⟨1, by decide⟩, t, 1) = G ((Cube.insertAt (0 : Fin 2) (t, v)) 1, (Cube.insertAt (0 : Fin 2) (t, v)) 0, 1)
    simp

private def tetrahedronFace (F : C(stdSimplex ℝ (Fin 4), X)) (i : Fin 4) :
    C(stdSimplex ℝ (Fin 3), X) :=
  F.comp ⟨stdSimplex.map i.succAbove, stdSimplex.continuous_map i.succAbove⟩

private theorem tetrahedronFace_boundary (F : C(stdSimplex ℝ (Fin 4), X))
    (hF : ∀ p : Simplex.tetrahedronOneSkeleton, F p.val = x) (i : Fin 4) :
    ∀ p ∈ Simplex.boundary (Fin 3), tetrahedronFace F i p = x := by
  intro p hp
  exact hF (Simplex.faceBoundaryIntoTetrahedronOneSkeleton i ⟨p, hp⟩)

private theorem tetrahedronJoin_skeleton (F : C(stdSimplex ℝ (Fin 4), X))
    (hF : ∀ p : Simplex.tetrahedronOneSkeleton, F p.val = x) :
    ∀ s t u, (s = 0 ∨ s = 1) ∨
      ((t = 0 ∨ t = 1) ∧ (u = 0 ∨ u = 1)) →
        (F.comp Simplex.tetrahedronJoin) (s, t, u) = x := by
  intro s t u h
  apply hF ⟨Simplex.tetrahedronJoin (s,t,u), ?_⟩
  rcases h with (rfl | rfl) | ⟨(rfl | rfl), (rfl | rfl)⟩
  · exact ⟨2, 3, by decide, by simp [Simplex.tetrahedronJoin], by simp [Simplex.tetrahedronJoin]⟩
  · exact ⟨0, 1, by decide, by simp [Simplex.tetrahedronJoin], by simp [Simplex.tetrahedronJoin]⟩
  · exact ⟨1, 3, by decide, by simp [Simplex.tetrahedronJoin], by simp [Simplex.tetrahedronJoin]⟩
  · exact ⟨1, 2, by decide, by simp [Simplex.tetrahedronJoin], by simp [Simplex.tetrahedronJoin]⟩
  · exact ⟨0, 3, by decide, by simp [Simplex.tetrahedronJoin], by simp [Simplex.tetrahedronJoin]⟩
  · exact ⟨0, 2, by decide, by simp [Simplex.tetrahedronJoin], by simp [Simplex.tetrahedronJoin]⟩

private theorem cubeFace0_tetrahedron (F : C(stdSimplex ℝ (Fin 4), X))
    (hF : ∀ p : Simplex.tetrahedronOneSkeleton, F p.val = x) :
    cubeFace0 (F.comp Simplex.tetrahedronJoin) (tetrahedronJoin_skeleton F hF) =
      GenLoop.congr x (Equiv.swap (0 : Fin 2) 1)
        (Simplex.triangleGenLoop (tetrahedronFace F 1) x (tetrahedronFace_boundary F hF 1)) := by
  ext v
  change F (Simplex.tetrahedronJoin (v 1, 0, v 0)) =
    F (stdSimplex.map (1 : Fin 4).succAbove
      (Simplex.triangleJoin (v ((Equiv.swap (0 : Fin 2) 1) 0),
        v ((Equiv.swap (0 : Fin 2) 1) 1))))
  simp only [Simplex.tetrahedronJoin_middle_zero, Equiv.swap_apply_left, Equiv.swap_apply_right]

private theorem cubeFace1_tetrahedron (F : C(stdSimplex ℝ (Fin 4), X))
    (hF : ∀ p : Simplex.tetrahedronOneSkeleton, F p.val = x) :
    cubeFace1 (F.comp Simplex.tetrahedronJoin) (tetrahedronJoin_skeleton F hF) =
      GenLoop.congr x (Equiv.swap (0 : Fin 2) 1)
        (Simplex.triangleGenLoop (tetrahedronFace F 0) x (tetrahedronFace_boundary F hF 0)) := by
  ext v
  change F (Simplex.tetrahedronJoin (v 1, 1, v 0)) =
    F (stdSimplex.map (0 : Fin 4).succAbove
      (Simplex.triangleJoin (v ((Equiv.swap (0 : Fin 2) 1) 0),
        v ((Equiv.swap (0 : Fin 2) 1) 1))))
  simp only [Simplex.tetrahedronJoin_middle_one, Equiv.swap_apply_left, Equiv.swap_apply_right]

private def cubeFace2HomotopyRel (F : C(stdSimplex ℝ (Fin 4), X))
    (hF : ∀ p : Simplex.tetrahedronOneSkeleton, F p.val = x) :
    (cubeFace2 (F.comp Simplex.tetrahedronJoin) (tetrahedronJoin_skeleton F hF)).val.HomotopyRel
      (Simplex.triangleGenLoop (tetrahedronFace F 3) x (tetrahedronFace_boundary F hF 3)).val
      (Cube.boundary (Fin 2)) where
  toContinuousMap :=
    (Simplex.triangleJoinReverseHomotopyRel (tetrahedronFace F 3)
      (tetrahedronFace_boundary F hF 3)).toContinuousMap.comp
        ⟨fun p => (p.1, p.2 1, p.2 0), by fun_prop⟩
  map_zero_left v := by
    change (Simplex.triangleJoinReverseHomotopyRel (tetrahedronFace F 3)
      (tetrahedronFace_boundary F hF 3)) (0, v 1, v 0) = _
    rw [ContinuousMap.HomotopyWith.apply_zero]
    change F (stdSimplex.map (3 : Fin 4).succAbove
      (Simplex.triangleJoinReverse (v 1, v 0))) =
        F (Simplex.tetrahedronJoin (v 1, v 0, 0))
    rw [Simplex.tetrahedronJoin_last_zero]
  map_one_left v := by
    change (Simplex.triangleJoinReverseHomotopyRel (tetrahedronFace F 3)
      (tetrahedronFace_boundary F hF 3)) (1, v 1, v 0) = _
    rw [ContinuousMap.HomotopyWith.apply_one]
    rfl
  prop' t v hv := by
    change (Simplex.triangleJoinReverseHomotopyRel (tetrahedronFace F 3)
      (tetrahedronFace_boundary F hF 3)) (t, v 1, v 0) = _
    have hb : (v 1, v 0) ∈ {p : I × I | p.1 = 0 ∨ p.1 = 1 ∨ p.2 = 0 ∨ p.2 = 1} := by
      obtain ⟨j, hj⟩ := hv
      fin_cases j
      · exact Or.inr (Or.inr hj)
      · rcases hj with h | h
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
    rw [ContinuousMap.HomotopyRel.eq_fst _ t hb]
    change F (stdSimplex.map (3 : Fin 4).succAbove
      (Simplex.triangleJoinReverse (v 1, v 0))) =
        F (Simplex.tetrahedronJoin (v 1, v 0, 0))
    rw [Simplex.tetrahedronJoin_last_zero]

private def cubeFace3HomotopyRel (F : C(stdSimplex ℝ (Fin 4), X))
    (hF : ∀ p : Simplex.tetrahedronOneSkeleton, F p.val = x) :
    (cubeFace3 (F.comp Simplex.tetrahedronJoin) (tetrahedronJoin_skeleton F hF)).val.HomotopyRel
      (Simplex.triangleGenLoop (tetrahedronFace F 2) x (tetrahedronFace_boundary F hF 2)).val
      (Cube.boundary (Fin 2)) where
  toContinuousMap :=
    (Simplex.triangleJoinReverseHomotopyRel (tetrahedronFace F 2)
      (tetrahedronFace_boundary F hF 2)).toContinuousMap.comp
        ⟨fun p => (p.1, p.2 1, p.2 0), by fun_prop⟩
  map_zero_left v := by
    change (Simplex.triangleJoinReverseHomotopyRel (tetrahedronFace F 2)
      (tetrahedronFace_boundary F hF 2)) (0, v 1, v 0) = _
    rw [ContinuousMap.HomotopyWith.apply_zero]
    change F (stdSimplex.map (2 : Fin 4).succAbove
      (Simplex.triangleJoinReverse (v 1, v 0))) =
        F (Simplex.tetrahedronJoin (v 1, v 0, 1))
    rw [Simplex.tetrahedronJoin_last_one]
  map_one_left v := by
    change (Simplex.triangleJoinReverseHomotopyRel (tetrahedronFace F 2)
      (tetrahedronFace_boundary F hF 2)) (1, v 1, v 0) = _
    rw [ContinuousMap.HomotopyWith.apply_one]
    rfl
  prop' t v hv := by
    change (Simplex.triangleJoinReverseHomotopyRel (tetrahedronFace F 2)
      (tetrahedronFace_boundary F hF 2)) (t, v 1, v 0) = _
    have hb : (v 1, v 0) ∈ {p : I × I | p.1 = 0 ∨ p.1 = 1 ∨ p.2 = 0 ∨ p.2 = 1} := by
      obtain ⟨j, hj⟩ := hv
      fin_cases j
      · exact Or.inr (Or.inr hj)
      · rcases hj with h | h
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
    rw [ContinuousMap.HomotopyRel.eq_fst _ t hb]
    change F (stdSimplex.map (2 : Fin 4).succAbove
      (Simplex.triangleJoinReverse (v 1, v 0))) =
        F (Simplex.tetrahedronJoin (v 1, v 0, 1))
    rw [Simplex.tetrahedronJoin_last_one]

theorem triangleGenLoop_tetrahedron_face_relation
    (F : C(stdSimplex ℝ (Fin 4), X))
    (hF : ∀ p : Simplex.tetrahedronOneSkeleton, F p.val = x) :
    let q : Fin 4 → HomotopyGroup (Fin 2) X x := fun i =>
      (⟦Simplex.triangleGenLoop
        (F.comp ⟨stdSimplex.map i.succAbove, stdSimplex.continuous_map i.succAbove⟩) x
        (fun p hp => hF (Simplex.faceBoundaryIntoTetrahedronOneSkeleton i ⟨p, hp⟩))⟧ :
          HomotopyGroup (Fin 2) X x)
    q 0 * q 2 = q 1 * q 3 := by
  let q : Fin 4 → HomotopyGroup (Fin 2) X x := fun i =>
    (⟦Simplex.triangleGenLoop (tetrahedronFace F i) x (tetrahedronFace_boundary F hF i)⟧ :
      HomotopyGroup (Fin 2) X x)
  change q 0 * q 2 = q 1 * q 3
  have h := homotopyGroup_cube_faces_relation (F.comp Simplex.tetrahedronJoin)
    (tetrahedronJoin_skeleton F hF)
  have h2 : (⟦cubeFace2 (F.comp Simplex.tetrahedronJoin) (tetrahedronJoin_skeleton F hF)⟧ :
      HomotopyGroup (Fin 2) X x) = q 3 :=
    Quotient.sound ⟨cubeFace2HomotopyRel F hF⟩
  have h3 : (⟦cubeFace3 (F.comp Simplex.tetrahedronJoin) (tetrahedronJoin_skeleton F hF)⟧ :
      HomotopyGroup (Fin 2) X x) = q 2 :=
    Quotient.sound ⟨cubeFace3HomotopyRel F hF⟩
  rw [cubeFace0_tetrahedron F hF, cubeFace1_tetrahedron F hF,
    homotopyGroup_swap_eq_inv, homotopyGroup_swap_eq_inv, h2, h3] at h
  change q 2 * (q 1)⁻¹ = (q 0)⁻¹ * q 3 at h
  calc
    q 0 * q 2 = q 0 * (q 2 * (q 1)⁻¹) * q 1 := by simp [mul_assoc]
    _ = q 0 * ((q 0)⁻¹ * q 3) * q 1 := by rw [h]
    _ = q 1 * q 3 := by simp [mul_comm]

end DifferentialGeometry.Topology
