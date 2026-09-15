import DifferentialGeometry.Topology.Homotopy.Reindex

noncomputable section

open Set ContinuousMap
open scoped unitInterval

namespace DifferentialGeometry.Topology

private def squareSwapDenom (r : unitInterval) : ℝ :=
  (1 - (r : ℝ)) ^ 2 + (r : ℝ) ^ 2

private theorem squareSwapDenom_pos (r : unitInterval) : 0 < squareSwapDenom r := by
  dsimp [squareSwapDenom]
  nlinarith [sq_nonneg ((r : ℝ) - 1 / 2)]

private def squareSwapRaw (r : unitInterval) (v : Fin 2 → unitInterval) : Fin 2 → ℝ :=
  ![((1 - (r : ℝ)) * (2 * (v 1 : ℝ) - 1) - (r : ℝ) * (2 * (v 0 : ℝ) - 1)) /
      squareSwapDenom r,
    ((1 - (r : ℝ)) * (2 * (v 0 : ℝ) - 1) + (r : ℝ) * (2 * (v 1 : ℝ) - 1)) /
      squareSwapDenom r]

private theorem squareSwapRaw_inverse_zero (r : unitInterval) (v : Fin 2 → unitInterval) :
    (1 - (r : ℝ)) * squareSwapRaw r v 1 - (r : ℝ) * squareSwapRaw r v 0 =
      2 * (v 0 : ℝ) - 1 := by
  simp only [squareSwapRaw, Matrix.cons_val_zero, Matrix.cons_val_one]
  field_simp [ne_of_gt (squareSwapDenom_pos r)]
  dsimp [squareSwapDenom]
  ring

private theorem squareSwapRaw_inverse_one (r : unitInterval) (v : Fin 2 → unitInterval) :
    (1 - (r : ℝ)) * squareSwapRaw r v 0 + (r : ℝ) * squareSwapRaw r v 1 =
      2 * (v 1 : ℝ) - 1 := by
  simp only [squareSwapRaw, Matrix.cons_val_zero, Matrix.cons_val_one]
  field_simp [ne_of_gt (squareSwapDenom_pos r)]
  dsimp [squareSwapDenom]
  ring

private def squareSwapParam :
    C(unitInterval × (Fin 2 → unitInterval), Fin 2 → unitInterval) where
  toFun p i := projIcc 0 1 zero_le_one ((squareSwapRaw p.1 p.2 i + 1) / 2)
  continuous_toFun := by
    apply continuous_pi
    intro i
    apply continuous_projIcc.comp
    apply Continuous.div_const
    apply Continuous.add_const
    have hd : Continuous (fun p : unitInterval × (Fin 2 → unitInterval) => squareSwapDenom p.1) := by
      dsimp [squareSwapDenom]
      fun_prop
    fin_cases i <;> dsimp [squareSwapRaw] <;>
      exact Continuous.div (by fun_prop) hd (fun p => ne_of_gt (squareSwapDenom_pos p.1))

private theorem convex_combo_strict (r : unitInterval) (a b : ℝ)
    (ha : -1 < a ∧ a < 1) (hb : -1 < b ∧ b < 1) :
    -1 < (1 - (r : ℝ)) * a + (r : ℝ) * b ∧
      (1 - (r : ℝ)) * a + (r : ℝ) * b < 1 := by
  exact convex_Ioo (-1 : ℝ) 1 ha hb (sub_nonneg.mpr r.property.2) r.property.1 (by ring)

private theorem squareSwapParam_boundary (r : unitInterval) (v : Fin 2 → unitInterval)
    (hv : v ∈ Cube.boundary (Fin 2)) : squareSwapParam (r, v) ∈ Cube.boundary (Fin 2) := by
  by_contra h
  have hi (i : Fin 2) : -1 < squareSwapRaw r v i ∧ squareSwapRaw r v i < 1 := by
    have h0 : ¬ squareSwapParam (r, v) i = 0 := fun hi => h ⟨i, Or.inl hi⟩
    have h1 : ¬ squareSwapParam (r, v) i = 1 := fun hi => h ⟨i, Or.inr hi⟩
    have hlo : 0 < (squareSwapRaw r v i + 1) / 2 := by
      by_contra hh
      apply h0
      exact projIcc_of_le_left zero_le_one (le_of_not_gt hh)
    have hhi : (squareSwapRaw r v i + 1) / 2 < 1 := by
      by_contra hh
      apply h1
      exact projIcc_of_right_le zero_le_one (le_of_not_gt hh)
    constructor <;> linarith
  have hzero := convex_combo_strict r (squareSwapRaw r v 1) (-squareSwapRaw r v 0)
    (hi 1) (by constructor <;> linarith [(hi 0).1, (hi 0).2])
  have hone := convex_combo_strict r (squareSwapRaw r v 0) (squareSwapRaw r v 1) (hi 0) (hi 1)
  rw [mul_neg, ← sub_eq_add_neg, squareSwapRaw_inverse_zero] at hzero
  rw [squareSwapRaw_inverse_one] at hone
  rcases hv with ⟨i, hi⟩
  fin_cases i <;> rcases hi with hi | hi
  · change v 0 = 0 at hi
    rw [hi] at hzero
    norm_num at hzero
  · change v 0 = 1 at hi
    rw [hi] at hzero
    norm_num at hzero
  · change v 1 = 0 at hi
    rw [hi] at hone
    norm_num at hone
  · change v 1 = 1 at hi
    rw [hi] at hone
    norm_num at hone

private theorem squareSwapParam_zero (v : Fin 2 → unitInterval) :
    squareSwapParam (0, v) = fun i => v ((Equiv.swap (0 : Fin 2) 1) i) := by
  funext i
  fin_cases i
  · change projIcc 0 1 zero_le_one _ = v 1
    convert projIcc_of_mem zero_le_one (v 1).property using 1
    simp [squareSwapRaw, squareSwapDenom]
  · change projIcc 0 1 zero_le_one _ = v 0
    convert projIcc_of_mem zero_le_one (v 0).property using 1
    simp [squareSwapRaw, squareSwapDenom]

private theorem squareSwapParam_one (v : Fin 2 → unitInterval) :
    squareSwapParam (1, v) = fun i => if i = 0 then unitInterval.symm (v 0) else v i := by
  funext i
  fin_cases i
  · change projIcc 0 1 zero_le_one ((squareSwapRaw 1 v 0 + 1) / 2) = unitInterval.symm (v 0)
    have he : (squareSwapRaw 1 v 0 + 1) / 2 = (unitInterval.symm (v 0) : ℝ) := by
      norm_num [squareSwapRaw, squareSwapDenom, unitInterval.symm]
      ring
    rw [he]
    exact projIcc_of_mem zero_le_one (unitInterval.symm (v 0)).property
  · change projIcc 0 1 zero_le_one _ = v 1
    convert projIcc_of_mem zero_le_one (v 1).property using 1
    simp [squareSwapRaw, squareSwapDenom]


def genLoopSwapHomotopyRel {X : Type*} [TopologicalSpace X] {x : X}
    (p : GenLoop (Fin 2) X x) :
    (GenLoop.congr x (Equiv.swap (0 : Fin 2) 1) p).val.HomotopyRel
      (GenLoop.symmAt 0 p).val (Cube.boundary (Fin 2)) where
  toContinuousMap := p.val.comp squareSwapParam
  map_zero_left v := by
    change p (squareSwapParam (0, v)) = _
    rw [squareSwapParam_zero]
    rfl
  map_one_left v := by
    change p (squareSwapParam (1, v)) = _
    rw [squareSwapParam_one]
    rfl
  prop' r v hv := by
    change p (squareSwapParam (r, v)) = _
    rw [GenLoop.boundary p _ (squareSwapParam_boundary r v hv)]
    exact (GenLoop.boundary (GenLoop.congr x (Equiv.swap (0 : Fin 2) 1) p) v hv).symm

theorem homotopyGroup_swap_eq_inv {X : Type*} [TopologicalSpace X] {x : X}
    (p : GenLoop (Fin 2) X x) :
    (⟦GenLoop.congr x (Equiv.swap (0 : Fin 2) 1) p⟧ : HomotopyGroup (Fin 2) X x) =
      ((⟦p⟧)⁻¹ : HomotopyGroup (Fin 2) X x) := by
  rw [HomotopyGroup.inv_spec (i := (0 : Fin 2))]
  exact Quotient.sound ⟨genLoopSwapHomotopyRel p⟩

end DifferentialGeometry.Topology
