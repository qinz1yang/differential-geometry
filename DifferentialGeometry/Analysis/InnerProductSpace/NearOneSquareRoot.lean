import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Normed.Ring.Units

/-!
# Smooth square roots near the identity in a complete real normed algebra

Lane CMS-BUN (S-BUNDLE, kernel G1). In a real normed algebra, square roots within distance `1` of
the identity are unique, and they commute with everything that commutes with the radicand
(a Sylvester-type estimate: `Y D + D Z = 0` with `‖Y - 1‖, ‖Z - 1‖ < 1` forces `D = 0`).
In a complete real normed algebra the inverse function theorem for `R ↦ R * R` at `1`
(derivative `2 • id`) gives a square root `sqrtNearOne 𝔸`, defined on a ball around `1`, which is
`C^∞` at every point of that ball.

Used for the polar correction `B = T (T* T)^{-1/2}` of the norm-preserving bundle smoothing (LFR47).
-/

set_option autoImplicit false

noncomputable section

open Metric
open scoped ContDiff Topology

namespace DifferentialGeometry.Analysis.NearOneSqrt

section Algebra

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸]

/-- Sylvester-type uniqueness: `Y D + D Z = 0` with `Y`, `Z` within distance `1` of the
identity forces `D = 0`. -/
theorem eq_zero_of_mul_add_mul_eq_zero {Y Z D : 𝔸} (hY : ‖Y - 1‖ < 1) (hZ : ‖Z - 1‖ < 1)
    (h : Y * D + D * Z = 0) : D = 0 := by
  have hsplit : (Y - 1) * D + D * (Z - 1) = (Y * D + D * Z) - (2 : ℝ) • D := by
    rw [sub_mul, mul_sub, one_mul, mul_one, two_smul]
    abel
  have key : (2 : ℝ) • D = -((Y - 1) * D + D * (Z - 1)) := by
    rw [hsplit, h]
    simp
  have hn : 2 * ‖D‖ ≤ (‖Y - 1‖ + ‖Z - 1‖) * ‖D‖ := by
    calc 2 * ‖D‖ = ‖(2 : ℝ) • D‖ := by rw [norm_smul]; norm_num
      _ = ‖(Y - 1) * D + D * (Z - 1)‖ := by rw [key, norm_neg]
      _ ≤ ‖(Y - 1) * D‖ + ‖D * (Z - 1)‖ := norm_add_le _ _
      _ ≤ ‖Y - 1‖ * ‖D‖ + ‖D‖ * ‖Z - 1‖ := add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
      _ = (‖Y - 1‖ + ‖Z - 1‖) * ‖D‖ := by ring
  have h0 : ‖D‖ ≤ 0 := by nlinarith [norm_nonneg D]
  exact norm_le_zero_iff.mp h0

/-- Square roots within distance `1` of the identity are unique. -/
theorem eq_of_mul_self_eq {Y Z : 𝔸} (hY : ‖Y - 1‖ < 1) (hZ : ‖Z - 1‖ < 1) (h : Y * Y = Z * Z) :
    Y = Z := by
  have hD : Y * (Y - Z) + (Y - Z) * Z = 0 := by
    rw [mul_sub, sub_mul, h]
    abel
  exact sub_eq_zero.mp (eq_zero_of_mul_add_mul_eq_zero hY hZ hD)

/-- A square root within distance `1` of the identity commutes with everything that commutes with
its square. -/
theorem commute_of_mul_self_eq {C X Y : 𝔸} (hY : ‖Y - 1‖ < 1) (hYX : Y * Y = X)
    (hC : Commute C X) : Commute C Y := by
  have h : Y * (C * Y - Y * C) + (C * Y - Y * C) * Y = 0 := by
    have e1 : Y * (C * Y - Y * C) + (C * Y - Y * C) * Y = C * (Y * Y) - (Y * Y) * C := by
      simp only [mul_sub, sub_mul, mul_assoc]
      abel
    rw [e1, hYX, hC.eq, sub_self]
  exact sub_eq_zero.mp (eq_zero_of_mul_add_mul_eq_zero hY hY h)

/-- The derivative of squaring at `R`, `H ↦ R * H + H * R`, has the expected form. -/
theorem hasFDerivAt_mul_self (R : 𝔸) :
    HasFDerivAt (fun X : 𝔸 => X * X)
      (ContinuousLinearMap.mul ℝ 𝔸 R + (ContinuousLinearMap.mul ℝ 𝔸).flip R) R := by
  have h := (hasFDerivAt_id (𝕜 := ℝ) R).fun_mul' (hasFDerivAt_id (𝕜 := ℝ) R)
  have heq : ContinuousLinearMap.mul ℝ 𝔸 R + (ContinuousLinearMap.mul ℝ 𝔸).flip R =
      id R • ContinuousLinearMap.id ℝ 𝔸 + MulOpposite.op (id R) • ContinuousLinearMap.id ℝ 𝔸 := by
    ext H
    simp
  rw [heq]
  exact h

end Algebra

section Complete

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸]

/-- Existence and smoothness of square roots near the identity (inverse function theorem). -/
theorem exists_contDiffAt_sqrt :
    ∃ η > 0, ∃ R : 𝔸 → 𝔸, R 1 = 1 ∧ ∀ X ∈ ball (1 : 𝔸) η,
      ContDiffAt ℝ ∞ R X ∧ R X * R X = X ∧ ‖R X - 1‖ < 1 := by
  set D : 𝔸 → 𝔸 →L[ℝ] 𝔸 := fun R =>
    ContinuousLinearMap.mul ℝ 𝔸 R + (ContinuousLinearMap.mul ℝ 𝔸).flip R with hDdef
  have hDcont : Continuous D :=
    (ContinuousLinearMap.mul ℝ 𝔸).continuous.add (ContinuousLinearMap.mul ℝ 𝔸).flip.continuous
  have hD1 : D 1 = (2 : ℝ) • (1 : 𝔸 →L[ℝ] 𝔸) := by
    ext H
    simp [hDdef, two_smul]
  have hu1 : IsUnit (D 1) := by
    rw [hD1, ← Algebra.algebraMap_eq_smul_one]
    exact (two_ne_zero : (2 : ℝ) ≠ 0).isUnit.map _
  have hUopen : IsOpen (D ⁻¹' {L : 𝔸 →L[ℝ] 𝔸 | IsUnit L}) := Units.isOpen.preimage hDcont
  obtain ⟨ρ₁, hρ₁, hball₁⟩ := Metric.isOpen_iff.mp hUopen 1 hu1
  set f : 𝔸 → 𝔸 := fun X => X * X with hfdef
  have hf : ContDiffAt ℝ ∞ f 1 := (contDiff_id.mul contDiff_id).contDiffAt
  have hcoe : ∀ u : (𝔸 →L[ℝ] 𝔸)ˣ,
      ((ContinuousLinearEquiv.unitsEquiv ℝ 𝔸 u : 𝔸 ≃L[ℝ] 𝔸) : 𝔸 →L[ℝ] 𝔸) = u := by
    intro u
    ext H
    rfl
  have hf' : HasFDerivAt f
      ((ContinuousLinearEquiv.unitsEquiv ℝ 𝔸 hu1.unit : 𝔸 ≃L[ℝ] 𝔸) : 𝔸 →L[ℝ] 𝔸) 1 := by
    rw [hcoe, IsUnit.unit_spec]
    exact hasFDerivAt_mul_self 1
  have hn : (∞ : WithTop ℕ∞) ≠ 0 := by decide
  set e := hf.toOpenPartialHomeomorph f hf' hn with he
  have hecoe : (e : 𝔸 → 𝔸) = f := rfl
  have h1src : (1 : 𝔸) ∈ e.source := hf.mem_toOpenPartialHomeomorph_source hf' hn
  have hf1 : f 1 = 1 := by simp [hfdef]
  have h1tgt : (1 : 𝔸) ∈ e.target := by
    have := hf.image_mem_toOpenPartialHomeomorph_target hf' hn
    rwa [hf1] at this
  have hsymm1 : e.symm 1 = 1 := by
    have h := e.left_inv h1src
    rw [hecoe, hf1] at h
    exact h
  have hcont : ContinuousAt e.symm 1 := e.continuousAt_symm h1tgt
  obtain ⟨η₁, hη₁, hη₁ball⟩ := Metric.continuousAt_iff.mp hcont (min ρ₁ 1) (lt_min hρ₁ one_pos)
  obtain ⟨η₂, hη₂, hη₂ball⟩ := Metric.isOpen_iff.mp e.open_target 1 h1tgt
  refine ⟨min η₁ η₂, lt_min hη₁ hη₂, e.symm, hsymm1, ?_⟩
  intro X hX
  have hX₁ : dist X 1 < η₁ := lt_of_lt_of_le (mem_ball.mp hX) (min_le_left _ _)
  have hX₂ : X ∈ e.target := hη₂ball (mem_ball.mpr (lt_of_lt_of_le (mem_ball.mp hX) (min_le_right _ _)))
  have hclose : dist (e.symm X) 1 < min ρ₁ 1 := by
    have := hη₁ball hX₁
    rwa [hsymm1] at this
  have hsq : e.symm X * e.symm X = X := by
    have h := e.right_inv hX₂
    rw [hecoe] at h
    exact h
  refine ⟨?_, hsq, ?_⟩
  · have hunit : IsUnit (D (e.symm X)) :=
      hball₁ (mem_ball.mpr (lt_of_lt_of_le hclose (min_le_left _ _)))
    have hder : HasFDerivAt e
        ((ContinuousLinearEquiv.unitsEquiv ℝ 𝔸 hunit.unit : 𝔸 ≃L[ℝ] 𝔸) : 𝔸 →L[ℝ] 𝔸)
        (e.symm X) := by
      rw [hcoe, IsUnit.unit_spec, hecoe]
      exact hasFDerivAt_mul_self (e.symm X)
    have hfX : ContDiffAt ℝ ∞ e (e.symm X) := by
      rw [hecoe]
      exact (contDiff_id.mul contDiff_id).contDiffAt
    exact e.contDiffAt_symm hX₂ hder hfX
  · rw [← dist_eq_norm]
    exact lt_of_lt_of_le hclose (min_le_right _ _)

variable (𝔸) in
/-- The radius of the ball around `1` on which `sqrtNearOne 𝔸` is a smooth square root. -/
def sqrtRadius : ℝ := Classical.choose (exists_contDiffAt_sqrt (𝔸 := 𝔸))

variable (𝔸) in
/-- A square root near the identity, `C^∞` on `ball 1 (sqrtRadius 𝔸)`. -/
def sqrtNearOne : 𝔸 → 𝔸 :=
  Classical.choose (Classical.choose_spec (exists_contDiffAt_sqrt (𝔸 := 𝔸))).2

theorem sqrtRadius_pos : 0 < sqrtRadius 𝔸 :=
  (Classical.choose_spec (exists_contDiffAt_sqrt (𝔸 := 𝔸))).1

theorem sqrtNearOne_one : sqrtNearOne 𝔸 1 = 1 :=
  (Classical.choose_spec (Classical.choose_spec (exists_contDiffAt_sqrt (𝔸 := 𝔸))).2).1

theorem sqrtNearOne_spec {X : 𝔸} (hX : X ∈ ball (1 : 𝔸) (sqrtRadius 𝔸)) :
    ContDiffAt ℝ ∞ (sqrtNearOne 𝔸) X ∧ sqrtNearOne 𝔸 X * sqrtNearOne 𝔸 X = X ∧
      ‖sqrtNearOne 𝔸 X - 1‖ < 1 :=
  (Classical.choose_spec (Classical.choose_spec (exists_contDiffAt_sqrt (𝔸 := 𝔸))).2).2 X hX

theorem contDiffAt_sqrtNearOne {X : 𝔸} (hX : X ∈ ball (1 : 𝔸) (sqrtRadius 𝔸)) :
    ContDiffAt ℝ ∞ (sqrtNearOne 𝔸) X :=
  (sqrtNearOne_spec hX).1

theorem sqrtNearOne_mul_self {X : 𝔸} (hX : X ∈ ball (1 : 𝔸) (sqrtRadius 𝔸)) :
    sqrtNearOne 𝔸 X * sqrtNearOne 𝔸 X = X :=
  (sqrtNearOne_spec hX).2.1

theorem norm_sqrtNearOne_sub_one_lt {X : 𝔸} (hX : X ∈ ball (1 : 𝔸) (sqrtRadius 𝔸)) :
    ‖sqrtNearOne 𝔸 X - 1‖ < 1 :=
  (sqrtNearOne_spec hX).2.2

theorem isUnit_sqrtNearOne {X : 𝔸} (hX : X ∈ ball (1 : 𝔸) (sqrtRadius 𝔸)) :
    IsUnit (sqrtNearOne 𝔸 X) := by
  have h : ‖1 - sqrtNearOne 𝔸 X‖ < 1 := by
    rw [norm_sub_rev]
    exact norm_sqrtNearOne_sub_one_lt hX
  simpa using isUnit_one_sub_of_norm_lt_one h

/-- Every square root of `X` within distance `1` of the identity is `sqrtNearOne 𝔸 X`. -/
theorem eq_sqrtNearOne {X Y : 𝔸} (hX : X ∈ ball (1 : 𝔸) (sqrtRadius 𝔸)) (hY : ‖Y - 1‖ < 1)
    (hYX : Y * Y = X) : Y = sqrtNearOne 𝔸 X :=
  eq_of_mul_self_eq hY (norm_sqrtNearOne_sub_one_lt hX) (by rw [hYX, sqrtNearOne_mul_self hX])

/-- `sqrtNearOne 𝔸 X` commutes with everything that commutes with `X`. -/
theorem commute_sqrtNearOne {C X : 𝔸} (hX : X ∈ ball (1 : 𝔸) (sqrtRadius 𝔸))
    (hC : Commute C X) : Commute C (sqrtNearOne 𝔸 X) :=
  commute_of_mul_self_eq (norm_sqrtNearOne_sub_one_lt hX) (sqrtNearOne_mul_self hX) hC

end Complete

end DifferentialGeometry.Analysis.NearOneSqrt
