import DifferentialGeometry.Topology.Simplex.TetrahedronJoinQuotient
import DifferentialGeometry.Topology.Simplex.TriangleCubeSphere
import DifferentialGeometry.Topology.Homotopy.CubicalBoundaryFilling
import DifferentialGeometry.Topology.Simplex.TetrahedronHomotopyRelation

noncomputable section
open scoped unitInterval
namespace DifferentialGeometry.Topology
variable {X : Type*} [TopologicalSpace X] {x : X}

private abbrev Other := {j : Fin 2 // j ≠ 0}

private theorem other_eq (j : Other) : j = ⟨1, by decide⟩ := by
  apply Subtype.ext
  have h := j.property
  rcases j with ⟨j, hj⟩
  fin_cases j <;> simp_all

private def joinFaceLoop (g : C(stdSimplex ℝ (Fin 3), X))
    (hg : ∀ p ∈ Simplex.boundary (Fin 3), g p = x) : GenLoop (Fin 2) X x :=
  GenLoop.congr x (Equiv.swap (0 : Fin 2) 1) (Simplex.triangleGenLoop g x hg)

private def joinReverseFaceLoop (g : C(stdSimplex ℝ (Fin 3), X))
    (hg : ∀ p ∈ Simplex.boundary (Fin 3), g p = x) : GenLoop (Fin 2) X x :=
  ⟨⟨fun v => g (Simplex.triangleJoinReverse (v 1, v 0)), by fun_prop⟩, by
    rintro v ⟨i, hi⟩
    apply hg
    fin_cases i
    · change v 0 = 0 ∨ v 0 = 1 at hi
      rcases hi with h | h
      · refine ⟨1, ?_⟩
        change (1 - (v 1 : ℝ)) * (v 0 : ℝ) = 0
        simp [h]
      · refine ⟨0, ?_⟩
        change (1 - (v 1 : ℝ)) * (1 - (v 0 : ℝ)) = 0
        simp [h]
    · change v 1 = 0 ∨ v 1 = 1 at hi
      rcases hi with h | h
      · refine ⟨2, ?_⟩
        change (v 1 : ℝ) = 0
        simp [h]
      · refine ⟨0, ?_⟩
        change (1 - (v 1 : ℝ)) * (1 - (v 0 : ℝ)) = 0
        simp [h]⟩

private theorem joinReverseFaceLoop_homotopic (g : C(stdSimplex ℝ (Fin 3), X))
    (hg : ∀ p ∈ Simplex.boundary (Fin 3), g p = x) :
    GenLoop.Homotopic (joinReverseFaceLoop g hg) (Simplex.triangleGenLoop g x hg) := by
  refine ⟨{
    toContinuousMap := (Simplex.triangleJoinReverseHomotopyRel g hg).toContinuousMap.comp
      ⟨fun p => (p.1, p.2 1, p.2 0), by fun_prop⟩
    map_zero_left := ?_
    map_one_left := ?_
    prop' := ?_ }⟩
  · intro v
    exact (Simplex.triangleJoinReverseHomotopyRel g hg).apply_zero (v 1, v 0)
  · intro v
    exact (Simplex.triangleJoinReverseHomotopyRel g hg).apply_one (v 1, v 0)
  · intro t v hv
    have hb : (v 1, v 0) ∈ {p : unitInterval × unitInterval |
        p.1 = 0 ∨ p.1 = 1 ∨ p.2 = 0 ∨ p.2 = 1} := by
      obtain ⟨j, hj⟩ := hv
      fin_cases j
      · exact Or.inr (Or.inr hj)
      · rcases hj with h | h
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
    exact (Simplex.triangleJoinReverseHomotopyRel g hg).eq_fst t hb

private theorem joinFaceLoop_apply (g : C(stdSimplex ℝ (Fin 3), X))
    (hg : ∀ p ∈ Simplex.boundary (Fin 3), g p = x) (t u : unitInterval) :
    GenLoop.toLoop 0 (joinFaceLoop g hg) u (fun _ : Other => t) =
      g (Simplex.triangleJoin (t, u)) := by
  change g (Simplex.triangleJoin
    ((Cube.insertAt (0 : Fin 2) (u, fun _ : Other => t)) ((Equiv.swap (0 : Fin 2) 1) 0),
      (Cube.insertAt (0 : Fin 2) (u, fun _ : Other => t)) ((Equiv.swap (0 : Fin 2) 1) 1))) = _
  simp

private theorem joinReverseFaceLoop_apply (g : C(stdSimplex ℝ (Fin 3), X))
    (hg : ∀ p ∈ Simplex.boundary (Fin 3), g p = x) (t u : unitInterval) :
    GenLoop.toLoop 0 (joinReverseFaceLoop g hg) u (fun _ : Other => t) =
      g (Simplex.triangleJoinReverse (t, u)) := by
  change g (Simplex.triangleJoinReverse
    ((Cube.insertAt (0 : Fin 2) (u, fun _ : Other => t)) 1,
      (Cube.insertAt (0 : Fin 2) (u, fun _ : Other => t)) 0)) = _
  simp

private theorem triangleJoinReverse_surjective : Function.Surjective Simplex.triangleJoinReverse := by
  intro p
  have hsum : p.val 0 + p.val 1 + p.val 2 = 1 := by
    simpa [Fin.sum_univ_succ, add_assoc] using p.property.2
  let s : unitInterval := ⟨p.val 2, p.property.1 2, by linarith [p.property.1 0, p.property.1 1]⟩
  let t : unitInterval := ⟨p.val 1 / (p.val 0 + p.val 1),
    unitInterval.div_mem (p.property.1 1) (add_nonneg (p.property.1 0) (p.property.1 1))
      (by linarith [p.property.1 0])⟩
  have hst : (1 - (s : ℝ)) * (t : ℝ) = p.val 1 := by
    have hs : 1 - (s : ℝ) = p.val 0 + p.val 1 := by dsimp [s]; linarith
    rw [hs]
    by_cases h : p.val 0 + p.val 1 = 0
    · have hz : p.val 1 = 0 := by linarith [p.property.1 0, p.property.1 1]
      simp [t, hz]
    · exact mul_div_cancel₀ _ h
  refine ⟨(s,t), ?_⟩
  apply Subtype.ext
  funext i
  fin_cases i
  · change (1 - (s : ℝ)) * (1 - (t : ℝ)) = p.val 0
    rw [mul_sub, mul_one, hst]
    dsimp [s]
    linarith
  · exact hst
  · rfl


private def loopFamilyCube (F : C(unitInterval × unitInterval, GenLoop Other X x)) :
    C(unitInterval × unitInterval × unitInterval, X) :=
  ⟨fun p => F (p.2.1, p.2.2) (fun _ : Other => p.1), by fun_prop⟩

private theorem loopFamilyCube_zero (F : C(unitInterval × unitInterval, GenLoop Other X x))
    (t u : unitInterval) : loopFamilyCube F (0,t,u) = x :=
  GenLoop.boundary _ _ ⟨⟨1, by decide⟩, Or.inl rfl⟩

private theorem loopFamilyCube_one (F : C(unitInterval × unitInterval, GenLoop Other X x))
    (t u : unitInterval) : loopFamilyCube F (1,t,u) = x :=
  GenLoop.boundary _ _ ⟨⟨1, by decide⟩, Or.inr rfl⟩

theorem exists_tetrahedron_extension_of_triangleGenLoop_relation
    (g : Fin 4 → C(stdSimplex ℝ (Fin 3), X))
    (hg : ∀ i, ∀ p ∈ Simplex.boundary (Fin 3), g i p = x)
    (h : let q : Fin 4 → HomotopyGroup (Fin 2) X x := fun i =>
      ⟦Simplex.triangleGenLoop (g i) x (hg i)⟧
      q 0 * q 2 = q 1 * q 3) :
    ∃ F : C(stdSimplex ℝ (Fin 4), X),
      ∀ (i : Fin 4) (p : stdSimplex ℝ (Fin 3)),
        F (stdSimplex.map i.succAbove p) = g i p := by
  let q : Fin 4 → HomotopyGroup (Fin 2) X x := fun i =>
    ⟦Simplex.triangleGenLoop (g i) x (hg i)⟧
  change q 0 * q 2 = q 1 * q 3 at h
  have ha (i : Fin 4) : (⟦joinFaceLoop (g i) (hg i)⟧ : HomotopyGroup (Fin 2) X x) = (q i)⁻¹ :=
    homotopyGroup_swap_eq_inv _
  have hb (i : Fin 4) : (⟦joinReverseFaceLoop (g i) (hg i)⟧ : HomotopyGroup (Fin 2) X x) = q i :=
    Quotient.sound (joinReverseFaceLoop_homotopic (g i) (hg i))
  have he : ((· * ·) : _ → _ → HomotopyGroup (Fin 2) X x)
      ⟦joinReverseFaceLoop (g 2) (hg 2)⟧ ⟦joinFaceLoop (g 1) (hg 1)⟧ =
      ((· * ·) : _ → _ → HomotopyGroup (Fin 2) X x)
        ⟦joinFaceLoop (g 0) (hg 0)⟧ ⟦joinReverseFaceLoop (g 3) (hg 3)⟧ := by
    rw [ha, ha, hb, hb]
    have he := congrArg (fun z => (q 0)⁻¹ * z * (q 1)⁻¹) h
    simpa [mul_assoc, mul_comm, mul_left_comm] using he
  obtain ⟨F, hbottom, htop, hleft, hright⟩ :=
    exists_square_of_homotopyGroup_mul_eq_mul 0
      (joinFaceLoop (g 1) (hg 1)) (joinFaceLoop (g 0) (hg 0))
      (joinReverseFaceLoop (g 3) (hg 3)) (joinReverseFaceLoop (g 2) (hg 2)) he
  let G := loopFamilyCube F
  have hzero : ∀ t u v, G (0,t,u) = G (0,t,v) :=
    fun t u v => (loopFamilyCube_zero F t u).trans (loopFamilyCube_zero F t v).symm
  have hone : ∀ t u v, G (1,t,u) = G (1,v,u) :=
    fun t u v => (loopFamilyCube_one F t u).trans (loopFamilyCube_one F v u).symm
  let K := Simplex.tetrahedronJoinDesc G hzero hone
  have hk (p : unitInterval × unitInterval × unitInterval) :
      K (Simplex.tetrahedronJoin p) = G p := Simplex.tetrahedronJoinDesc_apply G hzero hone p
  have h0 (s u : unitInterval) : G (s,1,u) = g 0 (Simplex.triangleJoin (s,u)) := by
    change F (1,u) (fun _ : Other => s) = _
    rw [htop]
    exact joinFaceLoop_apply (g 0) (hg 0) s u
  have h1 (s u : unitInterval) : G (s,0,u) = g 1 (Simplex.triangleJoin (s,u)) := by
    change F (0,u) (fun _ : Other => s) = _
    rw [hbottom]
    exact joinFaceLoop_apply (g 1) (hg 1) s u
  have h2 (s t : unitInterval) : G (s,t,1) = g 2 (Simplex.triangleJoinReverse (s,t)) := by
    change F (t,1) (fun _ : Other => s) = _
    rw [hright]
    exact joinReverseFaceLoop_apply (g 2) (hg 2) s t
  have h3 (s t : unitInterval) : G (s,t,0) = g 3 (Simplex.triangleJoinReverse (s,t)) := by
    change F (t,0) (fun _ : Other => s) = _
    rw [hleft]
    exact joinReverseFaceLoop_apply (g 3) (hg 3) s t
  refine ⟨K, ?_⟩
  intro i p
  fin_cases i
  · obtain ⟨⟨s,u⟩, rfl⟩ := Simplex.triangleJoin_surjective p
    change K (stdSimplex.map (0 : Fin 4).succAbove (Simplex.triangleJoin (s,u))) = g 0 _
    rw [← Simplex.tetrahedronJoin_middle_one, hk, h0]
  · obtain ⟨⟨s,u⟩, rfl⟩ := Simplex.triangleJoin_surjective p
    change K (stdSimplex.map (1 : Fin 4).succAbove (Simplex.triangleJoin (s,u))) = g 1 _
    rw [← Simplex.tetrahedronJoin_middle_zero, hk, h1]
  · obtain ⟨⟨s,t⟩, rfl⟩ := triangleJoinReverse_surjective p
    change K (stdSimplex.map (2 : Fin 4).succAbove (Simplex.triangleJoinReverse (s,t))) = g 2 _
    rw [← Simplex.tetrahedronJoin_last_one, hk, h2]
  · obtain ⟨⟨s,t⟩, rfl⟩ := triangleJoinReverse_surjective p
    change K (stdSimplex.map (3 : Fin 4).succAbove (Simplex.triangleJoinReverse (s,t))) = g 3 _
    rw [← Simplex.tetrahedronJoin_last_zero, hk, h3]

end DifferentialGeometry.Topology
