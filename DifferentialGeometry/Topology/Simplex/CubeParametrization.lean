import DifferentialGeometry.Topology.Simplex.Face

noncomputable section

open scoped unitInterval

namespace DifferentialGeometry.Simplex

def triangleJoin : C(unitInterval × unitInterval, stdSimplex ℝ (Fin 3)) where
  toFun x := ⟨![1 - (x.1 : ℝ), (x.1 : ℝ) * (1 - (x.2 : ℝ)), (x.1 : ℝ) * (x.2 : ℝ)], by
    constructor
    · intro i
      have ha0 := x.1.2.1
      have ha1 := x.1.2.2
      have hb0 := x.2.2.1
      have hb1 := x.2.2.2
      fin_cases i <;> dsimp <;> positivity
    · simp [Fin.sum_univ_succ]
      ring⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply continuous_pi
    intro i
    fin_cases i <;> dsimp <;> fun_prop

@[simp] theorem triangleJoin_zero (v : unitInterval) :
    triangleJoin (0, v) = stdSimplex.vertex (0 : Fin 3) := by
  apply Subtype.ext
  funext i
  fin_cases i <;> simp [triangleJoin]

@[simp] theorem triangleJoin_one (v : unitInterval) :
    triangleJoin (1, v) = stdSimplex.map (0 : Fin 3).succAbove
      (stdSimplexHomeomorphUnitInterval.symm v) := by
  apply Subtype.ext
  funext i
  by_cases hi : i = 0
  · subst i
    rw [map_succAbove_apply_pivot]
    simp [triangleJoin]
  · obtain ⟨j, rfl⟩ := Fin.exists_succAbove_eq hi
    rw [map_succAbove_apply_image]
    fin_cases j <;> simp [triangleJoin, stdSimplexHomeomorphUnitInterval, stdSimplexEquivIcc]

@[simp] theorem triangleJoin_second_zero (s : unitInterval) :
    triangleJoin (s, 0) = stdSimplex.map (2 : Fin 3).succAbove
      (stdSimplexHomeomorphUnitInterval.symm s) := by
  apply Subtype.ext
  funext i
  by_cases hi : i = 2
  · subst i
    rw [map_succAbove_apply_pivot]
    simp [triangleJoin]
  · obtain ⟨j, rfl⟩ := Fin.exists_succAbove_eq hi
    rw [map_succAbove_apply_image]
    fin_cases j <;> simp [triangleJoin, stdSimplexHomeomorphUnitInterval, stdSimplexEquivIcc,
      Fin.succAbove]

@[simp] theorem triangleJoin_second_one (s : unitInterval) :
    triangleJoin (s, 1) = stdSimplex.map (1 : Fin 3).succAbove
      (stdSimplexHomeomorphUnitInterval.symm s) := by
  apply Subtype.ext
  funext i
  by_cases hi : i = 1
  · subst i
    rw [map_succAbove_apply_pivot]
    simp [triangleJoin]
  · obtain ⟨j, rfl⟩ := Fin.exists_succAbove_eq hi
    rw [map_succAbove_apply_image]
    fin_cases j <;> simp [triangleJoin, stdSimplexHomeomorphUnitInterval, stdSimplexEquivIcc,
      Fin.succAbove]

def triangleJoinReverse : C(unitInterval × unitInterval, stdSimplex ℝ (Fin 3)) where
  toFun x := ⟨![(1 - (x.1 : ℝ)) * (1 - (x.2 : ℝ)),
      (1 - (x.1 : ℝ)) * (x.2 : ℝ), (x.1 : ℝ)], by
    constructor
    · intro i
      have ha0 := x.1.2.1
      have ha1 := x.1.2.2
      have hb0 := x.2.2.1
      have hb1 := x.2.2.2
      fin_cases i <;> dsimp <;> positivity
    · simp [Fin.sum_univ_succ]
      ring⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply continuous_pi
    intro i
    fin_cases i <;> dsimp <;> fun_prop

def tetrahedronJoin : C(unitInterval × unitInterval × unitInterval, stdSimplex ℝ (Fin 4)) where
  toFun x := ⟨![(1 - (x.1 : ℝ)) * (1 - (x.2.1 : ℝ)),
      (1 - (x.1 : ℝ)) * (x.2.1 : ℝ), (x.1 : ℝ) * (1 - (x.2.2 : ℝ)),
      (x.1 : ℝ) * (x.2.2 : ℝ)], by
    constructor
    · intro i
      have ha0 := x.1.2.1
      have ha1 := x.1.2.2
      have hb0 := x.2.1.2.1
      have hb1 := x.2.1.2.2
      have hc0 := x.2.2.2.1
      have hc1 := x.2.2.2.2
      fin_cases i <;> dsimp <;> positivity
    · simp [Fin.sum_univ_succ]
      ring⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply continuous_pi
    intro i
    fin_cases i <;> dsimp <;> fun_prop

@[simp] theorem tetrahedronJoin_zero (t u : unitInterval) :
    (tetrahedronJoin (0, t, u)).val = ![1 - (t : ℝ), (t : ℝ), 0, 0] := by
  funext i
  fin_cases i <;> simp [tetrahedronJoin]

@[simp] theorem tetrahedronJoin_one (t u : unitInterval) :
    (tetrahedronJoin (1, t, u)).val = ![0, 0, 1 - (u : ℝ), (u : ℝ)] := by
  funext i
  fin_cases i <;> simp [tetrahedronJoin]

@[simp] theorem tetrahedronJoin_middle_zero (s u : unitInterval) :
    tetrahedronJoin (s, 0, u) = stdSimplex.map (1 : Fin 4).succAbove (triangleJoin (s, u)) := by
  apply Subtype.ext
  funext i
  by_cases hi : i = 1
  · subst i
    rw [map_succAbove_apply_pivot]
    simp [tetrahedronJoin]
  · obtain ⟨j, rfl⟩ := Fin.exists_succAbove_eq hi
    rw [map_succAbove_apply_image]
    fin_cases j <;> simp [tetrahedronJoin, triangleJoin, Fin.succAbove]

@[simp] theorem tetrahedronJoin_middle_one (s u : unitInterval) :
    tetrahedronJoin (s, 1, u) = stdSimplex.map (0 : Fin 4).succAbove (triangleJoin (s, u)) := by
  apply Subtype.ext
  funext i
  by_cases hi : i = 0
  · subst i
    rw [map_succAbove_apply_pivot]
    simp [tetrahedronJoin]
  · obtain ⟨j, rfl⟩ := Fin.exists_succAbove_eq hi
    rw [map_succAbove_apply_image]
    fin_cases j <;> simp [tetrahedronJoin, triangleJoin, Fin.succAbove]

@[simp] theorem tetrahedronJoin_last_zero (s t : unitInterval) :
    tetrahedronJoin (s, t, 0) = stdSimplex.map (3 : Fin 4).succAbove
      (triangleJoinReverse (s, t)) := by
  apply Subtype.ext
  funext i
  by_cases hi : i = 3
  · subst i
    rw [map_succAbove_apply_pivot]
    simp [tetrahedronJoin]
  · obtain ⟨j, rfl⟩ := Fin.exists_succAbove_eq hi
    rw [map_succAbove_apply_image]
    fin_cases j <;> simp [tetrahedronJoin, triangleJoinReverse, Fin.succAbove]

@[simp] theorem tetrahedronJoin_last_one (s t : unitInterval) :
    tetrahedronJoin (s, t, 1) = stdSimplex.map (2 : Fin 4).succAbove
      (triangleJoinReverse (s, t)) := by
  apply Subtype.ext
  funext i
  by_cases hi : i = 2
  · subst i
    rw [map_succAbove_apply_pivot]
    simp [tetrahedronJoin]
  · obtain ⟨j, rfl⟩ := Fin.exists_succAbove_eq hi
    rw [map_succAbove_apply_image]
    fin_cases j <;> simp [tetrahedronJoin, triangleJoinReverse, Fin.succAbove]

end DifferentialGeometry.Simplex
