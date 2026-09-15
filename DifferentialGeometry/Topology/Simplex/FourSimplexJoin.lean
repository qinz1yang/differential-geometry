import DifferentialGeometry.Topology.Simplex.CubeParametrization

noncomputable section

open scoped unitInterval

namespace DifferentialGeometry.Simplex

def tetrahedronCone : C(unitInterval × unitInterval × unitInterval, stdSimplex ℝ (Fin 4)) where
  toFun x := ⟨![1 - (x.1 : ℝ), (x.1 : ℝ) * (1 - (x.2.1 : ℝ)),
    (x.1 : ℝ) * (x.2.1 : ℝ) * (1 - (x.2.2 : ℝ)),
    (x.1 : ℝ) * (x.2.1 : ℝ) * (x.2.2 : ℝ)], by
    constructor
    · intro i
      have hs0 := x.1.2.1
      have hs1 := x.1.2.2
      have ht0 := x.2.1.2.1
      have ht1 := x.2.1.2.2
      have hu0 := x.2.2.2.1
      have hu1 := x.2.2.2.2
      fin_cases i <;> dsimp <;> positivity
    · simp [Fin.sum_univ_succ]
      ring⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply continuous_pi
    intro i
    fin_cases i <;> dsimp <;> fun_prop

def fourSimplexJoin : C(unitInterval × unitInterval × unitInterval × unitInterval, stdSimplex ℝ (Fin 5)) where
  toFun x := ⟨![(1 - (x.1 : ℝ)) * (1 - (x.2.1 : ℝ)),
    (1 - (x.1 : ℝ)) * (x.2.1 : ℝ),
    (x.1 : ℝ) * (1 - (x.2.2.1 : ℝ)),
    (x.1 : ℝ) * (x.2.2.1 : ℝ) * (1 - (x.2.2.2 : ℝ)),
    (x.1 : ℝ) * (x.2.2.1 : ℝ) * (x.2.2.2 : ℝ)], by
    constructor
    · intro i
      have hs0 := x.1.2.1
      have hs1 := x.1.2.2
      have ht0 := x.2.1.2.1
      have ht1 := x.2.1.2.2
      have hu0 := x.2.2.1.2.1
      have hu1 := x.2.2.1.2.2
      have hv0 := x.2.2.2.2.1
      have hv1 := x.2.2.2.2.2
      fin_cases i <;> dsimp <;> positivity
    · simp [Fin.sum_univ_succ]
      ring⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply continuous_pi
    intro i
    fin_cases i <;> dsimp <;> fun_prop

theorem fourSimplexJoin_val (s t u v : unitInterval) :
    (fourSimplexJoin (s, t, u, v)).val = ![(1 - (s : ℝ)) * (1 - (t : ℝ)),
      (1 - (s : ℝ)) * (t : ℝ),
      (s : ℝ) * (1 - (u : ℝ)),
      (s : ℝ) * (u : ℝ) * (1 - (v : ℝ)),
      (s : ℝ) * (u : ℝ) * (v : ℝ)] := rfl

@[simp] theorem fourSimplexJoin_first_zero (t u v : unitInterval) :
    (fourSimplexJoin (0, t, u, v)).val = ![(1 : ℝ) - (t : ℝ), (t : ℝ), 0, 0, 0] := by
  funext i
  fin_cases i <;> simp [fourSimplexJoin]

@[simp] theorem fourSimplexJoin_first_one (t u v : unitInterval) :
    (fourSimplexJoin (1, t, u, v)).val =
      ![0, 0, 1 - (u : ℝ), (u : ℝ) * (1 - (v : ℝ)), (u : ℝ) * (v : ℝ)] := by
  funext i
  fin_cases i <;> simp [fourSimplexJoin]

@[simp] theorem fourSimplexJoin_second_zero (s u v : unitInterval) :
    fourSimplexJoin (s, 0, u, v) = stdSimplex.map (1 : Fin 5).succAbove (tetrahedronCone (s, u, v)) := by
  apply Subtype.ext
  funext i
  by_cases hi : i = 1
  · subst i
    rw [map_succAbove_apply_pivot]
    simp [fourSimplexJoin]
  · obtain ⟨j, rfl⟩ := Fin.exists_succAbove_eq hi
    rw [map_succAbove_apply_image]
    fin_cases j <;> simp [fourSimplexJoin, tetrahedronCone, Fin.succAbove]

@[simp] theorem fourSimplexJoin_second_one (s u v : unitInterval) :
    fourSimplexJoin (s, 1, u, v) = stdSimplex.map (0 : Fin 5).succAbove (tetrahedronCone (s, u, v)) := by
  apply Subtype.ext
  funext i
  by_cases hi : i = 0
  · subst i
    rw [map_succAbove_apply_pivot]
    simp [fourSimplexJoin]
  · obtain ⟨j, rfl⟩ := Fin.exists_succAbove_eq hi
    rw [map_succAbove_apply_image]
    fin_cases j <;> simp [fourSimplexJoin, tetrahedronCone, Fin.succAbove]

@[simp] theorem fourSimplexJoin_third_zero (s t v : unitInterval) :
    (fourSimplexJoin (s, t, 0, v)).val = ![(1 - (s : ℝ)) * (1 - (t : ℝ)),
      (1 - (s : ℝ)) * (t : ℝ), (s : ℝ), 0, 0] := by
  funext i
  fin_cases i <;> simp [fourSimplexJoin]

@[simp] theorem fourSimplexJoin_third_one (s t v : unitInterval) :
    fourSimplexJoin (s, t, 1, v) = stdSimplex.map (2 : Fin 5).succAbove (tetrahedronJoin (s, t, v)) := by
  apply Subtype.ext
  funext i
  by_cases hi : i = 2
  · subst i
    rw [map_succAbove_apply_pivot]
    simp [fourSimplexJoin]
  · obtain ⟨j, rfl⟩ := Fin.exists_succAbove_eq hi
    rw [map_succAbove_apply_image]
    fin_cases j <;> simp [fourSimplexJoin, tetrahedronJoin, Fin.succAbove]

@[simp] theorem fourSimplexJoin_fourth_zero (s t u : unitInterval) :
    fourSimplexJoin (s, t, u, 0) = stdSimplex.map (4 : Fin 5).succAbove (tetrahedronJoin (s, t, u)) := by
  apply Subtype.ext
  funext i
  by_cases hi : i = 4
  · subst i
    rw [map_succAbove_apply_pivot]
    simp [fourSimplexJoin]
  · obtain ⟨j, rfl⟩ := Fin.exists_succAbove_eq hi
    rw [map_succAbove_apply_image]
    fin_cases j <;> simp [fourSimplexJoin, tetrahedronJoin, Fin.succAbove]

@[simp] theorem fourSimplexJoin_fourth_one (s t u : unitInterval) :
    fourSimplexJoin (s, t, u, 1) = stdSimplex.map (3 : Fin 5).succAbove (tetrahedronJoin (s, t, u)) := by
  apply Subtype.ext
  funext i
  by_cases hi : i = 3
  · subst i
    rw [map_succAbove_apply_pivot]
    simp [fourSimplexJoin]
  · obtain ⟨j, rfl⟩ := Fin.exists_succAbove_eq hi
    rw [map_succAbove_apply_image]
    fin_cases j <;> simp [fourSimplexJoin, tetrahedronJoin, Fin.succAbove]

end DifferentialGeometry.Simplex
