import DifferentialGeometry.Tensor.RSTensor.Evaluation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry

open Bundle DifferentialGeometry.Tensor0SBundle
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [IsManifold I 1 M]

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] in
private theorem eval02_slots_eq
    {x : M}
    (A : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x)
    (m : Fin 2 -> TangentSpace I x) (v w : TangentSpace I x)
    (h0 : m 0 = v) (h1 : m 1 = w) :
    A m = eval02 (I := I) (M := M) A v w := by
  congr 1
  funext i
  fin_cases i <;> simp [h0, h1]

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] in
private theorem quad02_add_smul_eq
    {x : M}
    (A : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x)
    {v w : TangentSpace I x} {a : Real}
    (hsym : eval02 (I := I) (M := M) A w v =
      eval02 (I := I) (M := M) A v w) :
    quad02 (I := I) (M := M) A (v + a • w) =
      quad02 (I := I) (M := M) A v +
        2 * a * eval02 (I := I) (M := M) A v w +
        a * a * quad02 (I := I) (M := M) A w := by
  let m : Fin 2 -> TangentSpace I x := fun _ => v + a • w
  have h0 := A.map_update_add m (0 : Fin 2) v (a • w)
  have h00 :
      Function.update m (0 : Fin 2) (v + a • w) = m := by
    funext i
    fin_cases i <;> simp [m]
  have h0v :
      A (Function.update m (0 : Fin 2) v) =
        eval02 (I := I) (M := M) A v (v + a • w) := by
    apply eval02_slots_eq
    · simp [m]
    · simp [m]
  have h0w :
      A (Function.update m (0 : Fin 2) (a • w)) =
        a * eval02 (I := I) (M := M) A w (v + a • w) := by
    have hsmul := A.map_update_smul m (0 : Fin 2) a w
    have hslot :
        A (Function.update m (0 : Fin 2) w) =
          eval02 (I := I) (M := M) A w (v + a • w) := by
      apply eval02_slots_eq
      · simp [m]
      · simp [m]
    calc
      A (Function.update m (0 : Fin 2) (a • w))
          = a • A (Function.update m (0 : Fin 2) w) := by
              exact hsmul
      _ = a * eval02 (I := I) (M := M) A w (v + a • w) := by
              simp [hslot, smul_eq_mul]
  have hfirst :
      quad02 (I := I) (M := M) A (v + a • w) =
        eval02 (I := I) (M := M) A v (v + a • w) +
          a * eval02 (I := I) (M := M) A w (v + a • w) := by
    calc
      quad02 (I := I) (M := M) A (v + a • w) = A m := by
        rfl
      _ = A (Function.update m (0 : Fin 2) (v + a • w)) := by rw [h00]
      _ = A (Function.update m (0 : Fin 2) v) +
            A (Function.update m (0 : Fin 2) (a • w)) := by
              exact h0
      _ = eval02 (I := I) (M := M) A v (v + a • w) +
            a * eval02 (I := I) (M := M) A w (v + a • w) := by
              rw [h0v, h0w]
  have hv_add :
      eval02 (I := I) (M := M) A v (v + a • w) =
        quad02 (I := I) (M := M) A v +
          a * eval02 (I := I) (M := M) A v w := by
    let mv : Fin 2 -> TangentSpace I x := fun i => if i = 0 then v else v + a • w
    have hslot :
        mv = Function.update mv (1 : Fin 2) (v + a • w) := by
      funext i
      fin_cases i <;> simp [mv]
    have hadd := A.map_update_add mv (1 : Fin 2) v (a • w)
    have hleft :
        A (Function.update mv (1 : Fin 2) (v + a • w)) =
          eval02 (I := I) (M := M) A v (v + a • w) := by
      apply eval02_slots_eq <;> simp [mv]
    have hvv :
        A (Function.update mv (1 : Fin 2) v) =
          quad02 (I := I) (M := M) A v := by
      calc
        A (Function.update mv (1 : Fin 2) v) =
            eval02 (I := I) (M := M) A v v := by
              apply eval02_slots_eq <;> simp [mv]
        _ = quad02 (I := I) (M := M) A v := by
              rw [eval02_self]
    have hvw_smul :
        A (Function.update mv (1 : Fin 2) (a • w)) =
          a * eval02 (I := I) (M := M) A v w := by
      have hsmul := A.map_update_smul mv (1 : Fin 2) a w
      have hvw :
          A (Function.update mv (1 : Fin 2) w) =
            eval02 (I := I) (M := M) A v w := by
        apply eval02_slots_eq <;> simp [mv]
      calc
        A (Function.update mv (1 : Fin 2) (a • w))
            = a • A (Function.update mv (1 : Fin 2) w) := by
                exact hsmul
        _ = a * eval02 (I := I) (M := M) A v w := by
                simp [hvw, smul_eq_mul]
    calc
      eval02 (I := I) (M := M) A v (v + a • w)
          = A (Function.update mv (1 : Fin 2) (v + a • w)) := by
              rw [hleft]
      _ = A (Function.update mv (1 : Fin 2) v) +
            A (Function.update mv (1 : Fin 2) (a • w)) := by
              exact hadd
      _ = quad02 (I := I) (M := M) A v +
            a * eval02 (I := I) (M := M) A v w := by
              rw [hvv, hvw_smul]
  have hw_add :
      eval02 (I := I) (M := M) A w (v + a • w) =
        eval02 (I := I) (M := M) A w v +
          a * quad02 (I := I) (M := M) A w := by
    let mw : Fin 2 -> TangentSpace I x := fun i => if i = 0 then w else v + a • w
    have hadd := A.map_update_add mw (1 : Fin 2) v (a • w)
    have hleft :
        A (Function.update mw (1 : Fin 2) (v + a • w)) =
          eval02 (I := I) (M := M) A w (v + a • w) := by
      apply eval02_slots_eq <;> simp [mw]
    have hwv :
        A (Function.update mw (1 : Fin 2) v) =
          eval02 (I := I) (M := M) A w v := by
      apply eval02_slots_eq <;> simp [mw]
    have hww_smul :
        A (Function.update mw (1 : Fin 2) (a • w)) =
          a * quad02 (I := I) (M := M) A w := by
      have hsmul := A.map_update_smul mw (1 : Fin 2) a w
      have hww :
          A (Function.update mw (1 : Fin 2) w) =
            quad02 (I := I) (M := M) A w := by
        calc
          A (Function.update mw (1 : Fin 2) w) =
              eval02 (I := I) (M := M) A w w := by
                apply eval02_slots_eq <;> simp [mw]
          _ = quad02 (I := I) (M := M) A w := by
                rw [eval02_self]
      calc
        A (Function.update mw (1 : Fin 2) (a • w))
            = a • A (Function.update mw (1 : Fin 2) w) := by
                exact hsmul
        _ = a * quad02 (I := I) (M := M) A w := by
                simp [hww, smul_eq_mul]
    calc
      eval02 (I := I) (M := M) A w (v + a • w)
          = A (Function.update mw (1 : Fin 2) (v + a • w)) := by
              rw [hleft]
      _ = A (Function.update mw (1 : Fin 2) v) +
            A (Function.update mw (1 : Fin 2) (a • w)) := by
              exact hadd
      _ = eval02 (I := I) (M := M) A w v +
            a * quad02 (I := I) (M := M) A w := by
              rw [hwv, hww_smul]
  calc
    quad02 (I := I) (M := M) A (v + a • w)
        = eval02 (I := I) (M := M) A v (v + a • w) +
            a * eval02 (I := I) (M := M) A w (v + a • w) := hfirst
    _ = quad02 (I := I) (M := M) A v +
          2 * a * eval02 (I := I) (M := M) A v w +
          a * a * quad02 (I := I) (M := M) A w := by
            rw [hv_add, hw_add, hsym]
            ring

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] in
theorem psd_null_left
    {x : M}
    (A : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x)
    {v : TangentSpace I x}
    (hsym : ∀ u w : TangentSpace I x,
      eval02 (I := I) (M := M) A u w = eval02 (I := I) (M := M) A w u)
    (hpsd : ∀ u : TangentSpace I x, 0 ≤ quad02 (I := I) (M := M) A u)
    (hnull : quad02 (I := I) (M := M) A v = 0) :
    ∀ w : TangentSpace I x, eval02 (I := I) (M := M) A v w = 0 := by
  intro w
  let c : Real := eval02 (I := I) (M := M) A v w
  let q : Real := quad02 (I := I) (M := M) A w
  have hq : 0 ≤ q := hpsd w
  by_contra hc
  let a : Real := -c / (q + 1)
  have hden_pos : 0 < q + 1 := by linarith
  have hden_ne : q + 1 ≠ 0 := ne_of_gt hden_pos
  have hpos := hpsd (v + a • w)
  have hquad :
      quad02 (I := I) (M := M) A (v + a • w) =
        2 * a * c + a * a * q := by
    have h := quad02_add_smul_eq (I := I) (M := M) A
      (v := v) (w := w) (a := a) (hsym w v)
    simpa [c, q, hnull, add_assoc, add_comm, add_left_comm] using h
  have hnonneg : 0 ≤ 2 * a * c + a * a * q := by
    simpa [hquad] using hpos
  have hcalc : 2 * a * c + a * a * q =
      - (c * c) * (q + 2) / ((q + 1) * (q + 1)) := by
    subst a
    field_simp [hden_ne]
    ring
  have hc_sq_pos : 0 < c * c := mul_self_pos.mpr hc
  have hq2_pos : 0 < q + 2 := by linarith
  have hden_sq_pos : 0 < (q + 1) * (q + 1) := mul_pos hden_pos hden_pos
  have hneg : - (c * c) * (q + 2) / ((q + 1) * (q + 1)) < 0 := by
    exact div_neg_of_neg_of_pos (mul_neg_of_neg_of_pos (neg_lt_zero.mpr hc_sq_pos) hq2_pos)
      hden_sq_pos
  exact not_le_of_gt (by simpa [hcalc] using hneg) hnonneg

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] in
theorem psd_null_right
    {x : M}
    (A : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x)
    {v : TangentSpace I x}
    (hsym : ∀ u w : TangentSpace I x,
      eval02 (I := I) (M := M) A u w = eval02 (I := I) (M := M) A w u)
    (hpsd : ∀ u : TangentSpace I x, 0 ≤ quad02 (I := I) (M := M) A u)
    (hnull : quad02 (I := I) (M := M) A v = 0) :
    ∀ w : TangentSpace I x, eval02 (I := I) (M := M) A w v = 0 := by
  intro w
  rw [← hsym v w]
  exact psd_null_left (I := I) (M := M) A hsym hpsd hnull w

end DifferentialGeometry
