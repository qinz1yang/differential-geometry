import Mathlib.LinearAlgebra.Orientation
import Mathlib.LinearAlgebra.Determinant
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Orientation signs under linear automorphisms (P1a, algebra)

* `alternatingMap_vec3_combo`: an alternating form in three arguments under the substitution
  `(h, x, y) ↦ (h, a x + b y, c x + d y)` is multiplied by `a d - b c`;
* `orientation_map_eq_basis_iff`: pushing an orientation forward by `D` keeps it equal to a basis
  orientation iff (it was equal ↔ `det D > 0`);
* `orientation_sign_iff_map`: the statement "`o` is the basis orientation iff `b.det Y > 0`" is
  invariant under pushing `o` and `Y` forward by a linear automorphism (for `b.det Y ≠ 0`).
-/

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.Topology.VectorBundle

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

omit [AddCommGroup E] [Module ℝ E] in
private theorem update_one_vec3 (h x y z : E) :
    Function.update ![h, x, y] 1 z = ![h, z, y] := by
  funext i
  fin_cases i <;> simp

omit [AddCommGroup E] [Module ℝ E] in
private theorem update_two_vec3 (h x y z : E) :
    Function.update ![h, x, y] 2 z = ![h, x, z] := by
  funext i
  fin_cases i <;> simp

/-- An alternating form in three arguments under a substitution of its last two arguments. -/
theorem alternatingMap_vec3_combo (φ : E [⋀^Fin 3]→ₗ[ℝ] ℝ) (h x y : E) (a b c d : ℝ) :
    φ ![h, a • x + b • y, c • x + d • y] = (a * d - b * c) * φ ![h, x, y] := by
  have add1 : ∀ x x' y : E, φ ![h, x + x', y] = φ ![h, x, y] + φ ![h, x', y] := by
    intro x x' y
    have := φ.map_update_add ![h, x, y] 1 x x'
    simpa only [update_one_vec3] using this
  have smul1 : ∀ (r : ℝ) (x y : E), φ ![h, r • x, y] = r * φ ![h, x, y] := by
    intro r x y
    have := φ.map_update_smul ![h, x, y] 1 r x
    simpa only [update_one_vec3, smul_eq_mul] using this
  have add2 : ∀ x y y' : E, φ ![h, x, y + y'] = φ ![h, x, y] + φ ![h, x, y'] := by
    intro x y y'
    have := φ.map_update_add ![h, x, y] 2 y y'
    simpa only [update_two_vec3] using this
  have smul2 : ∀ (r : ℝ) (x y : E), φ ![h, x, r • y] = r * φ ![h, x, y] := by
    intro r x y
    have := φ.map_update_smul ![h, x, y] 2 r y
    simpa only [update_two_vec3, smul_eq_mul] using this
  have diag : ∀ x : E, φ ![h, x, x] = 0 := fun x =>
    φ.map_eq_zero_of_eq ![h, x, x] (i := 1) (j := 2) rfl (by decide)
  have swap : φ ![h, y, x] = -φ ![h, x, y] := by
    have := φ.map_swap ![h, x, y] (i := 1) (j := 2) (by decide)
    have heq : ![h, x, y] ∘ Equiv.swap (1 : Fin 3) 2 = ![h, y, x] := by
      funext i
      fin_cases i <;> rfl
    rwa [heq] at this
  simp only [add1, add2, smul1, smul2, diag, swap]
  ring

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Pushing an orientation forward by a linear automorphism `D` keeps it equal to a basis
orientation exactly when it was equal and `det D > 0`, or it was not equal and `det D < 0`. -/
theorem orientation_map_eq_basis_iff
    {β₀ : Module.Basis ι ℝ E} {D : E ≃ₗ[ℝ] E} {o : Orientation ℝ E ι} :
    Orientation.map ι D o = β₀.orientation ↔
      (o = β₀.orientation ↔ 0 < LinearMap.det (D : E →ₗ[ℝ] E)) := by
  have hprod := LinearEquiv.det_mul_det_symm D
  have hbase : Orientation.map ι D β₀.orientation = β₀.orientation ↔
      0 < LinearMap.det (D : E →ₗ[ℝ] E) := by
    rw [← β₀.orientation_map, Module.Basis.orientation_eq_iff_det_pos, Module.Basis.det_map]
    have hcomp : ⇑D.symm ∘ ⇑β₀ = ⇑(D.symm : E →ₗ[ℝ] E) ∘ ⇑β₀ := rfl
    rw [hcomp, Module.Basis.det_comp, Module.Basis.det_self, mul_one]
    constructor
    · intro h
      by_contra hn
      have : LinearMap.det (D : E →ₗ[ℝ] E) * LinearMap.det (D.symm : E →ₗ[ℝ] E) ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg (not_lt.mp hn) h.le
      linarith
    · intro h
      by_contra hn
      have : LinearMap.det (D : E →ₗ[ℝ] E) * LinearMap.det (D.symm : E →ₗ[ℝ] E) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos h.le (not_lt.mp hn)
      linarith
  have hnn : ∀ x : Orientation ℝ E ι, - -x = x := fun x => neg_neg x
  rcases β₀.orientation_eq_or_eq_neg o with rfl | rfl
  · simp only [true_iff]
    exact hbase
  · rw [Orientation.map_neg]
    have hne : (-β₀.orientation = β₀.orientation) ↔ False :=
      ⟨fun h => Module.Ray.ne_neg_self β₀.orientation h.symm, False.elim⟩
    rw [hne, false_iff]
    constructor
    · intro h hpos
      have h' : Orientation.map ι D β₀.orientation = -β₀.orientation := by
        have := congrArg (fun z : Orientation ℝ E ι => -z) h
        exact (hnn _).symm.trans this
      exact (β₀.orientation_ne_iff_eq_neg _).mpr h' (hbase.mpr hpos)
    · intro h
      have h' : Orientation.map ι D β₀.orientation ≠ β₀.orientation := fun h'' => h (hbase.mp h'')
      rw [(β₀.orientation_ne_iff_eq_neg _).mp h']
      exact hnn _

/-- **Sign transfer under a linear automorphism.** If `b.det Y ≠ 0`, the statement "`o` is the
basis orientation iff `Y` is positive" is unchanged when `o` and `Y` are pushed forward by `D`. -/
theorem orientation_sign_iff_map
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    {β₀ : Module.Basis ι ℝ E} {b : Module.Basis κ ℝ E} (D : E ≃ₗ[ℝ] E)
    {o : Orientation ℝ E ι} {Y : κ → E} (hY : b.det Y ≠ 0) :
    ((o = β₀.orientation) ↔ 0 < b.det Y) ↔
      ((Orientation.map ι D o = β₀.orientation) ↔ 0 < b.det (⇑D ∘ Y)) := by
  have hcomp : b.det (⇑D ∘ Y) = LinearMap.det (D : E →ₗ[ℝ] E) * b.det Y :=
    Module.Basis.det_comp b (D : E →ₗ[ℝ] E) Y
  have hδ : LinearMap.det (D : E →ₗ[ℝ] E) ≠ 0 := (LinearEquiv.isUnit_det' D).ne_zero
  rw [orientation_map_eq_basis_iff, hcomp]
  rcases lt_or_gt_of_ne hδ with hneg | hpos
  · have h1 : (0 < LinearMap.det (D : E →ₗ[ℝ] E) * b.det Y) ↔ ¬ (0 < b.det Y) := by
      constructor
      · intro h hy
        have := mul_neg_of_neg_of_pos hneg hy
        linarith
      · intro h
        have hy : b.det Y < 0 := lt_of_le_of_ne (not_lt.mp h) hY
        exact mul_pos_of_neg_of_neg hneg hy
    rw [h1]
    have h2 : ¬ (0 < LinearMap.det (D : E →ₗ[ℝ] E)) := not_lt.mpr hneg.le
    tauto
  · have h1 : (0 < LinearMap.det (D : E →ₗ[ℝ] E) * b.det Y) ↔ 0 < b.det Y :=
      ⟨fun h => pos_of_mul_pos_right h hpos.le, fun h => mul_pos hpos h⟩
    rw [h1]
    tauto

end DifferentialGeometry.Topology.VectorBundle
