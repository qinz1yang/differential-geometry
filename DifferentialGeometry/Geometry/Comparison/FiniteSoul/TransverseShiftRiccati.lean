import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Normed.Ring.Units
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# S3-SHIFT kernel: the matrix Riccati bound on a uniform interval (lane CMS3-SHIFT, group G1)

Let `F` be a finite-dimensional real inner product space and `Y : ℝ → F →L[ℝ] F` solve the matrix
Jacobi equation `Y'' = −R Y`, `Y 0 = 1`, `Y' 0 = 0`, where `R t` is self-adjoint, positive semidefinite and
`‖R t‖ ≤ Λ`. On the uniform interval `[0, ρ]` with `Λ ρ² ≤ 1/4`:

* `norm_sub_one_le_of_jacobi_operator`: `‖Y t − 1‖ ≤ 1/3` (a priori bound by the mean value inequality,
  applied to the maximum of `‖Y‖`), hence `Y t` is invertible;
* `inner_deriv_apply_eq_of_jacobi_operator`: the Wronskian identity `⟪Y' a, Y b⟫ = ⟪Y a, Y' b⟫`;
* `inner_riccati_apply_self_nonpos`: `A = Y' Y⁻¹` is symmetric and `⟪A v, v⟫ ≤ 0`
  (`A' = −R − A²`, `A 0 = 0`);
* `norm_apply_le_of_jacobi_operator` (frozen name): `Y t` is a unit and `‖Y t a‖ ≤ ‖a‖`
  (`(‖Y a‖²)' = 2 ⟪A (Y a), Y a⟫ ≤ 0`).

Deviation from the frozen interface (a strengthening): the hypothesis `ContinuousOn R (Icc 0 ρ)` is not
used by the proof and is dropped; the verbatim frozen statement is an `example` in
`TransverseShiftRiccatiApplications.lean`.
-/

set_option autoImplicit false

noncomputable section

open Set
open scoped InnerProductSpace

namespace DifferentialGeometry.Geometry.FiniteSoul

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

/-- An operator within distance `< 1` of the identity is a unit. -/
theorem isUnit_of_norm_sub_one_lt_one {T : F →L[ℝ] F} (h : ‖T - 1‖ < 1) : IsUnit T :=
  not_not.mp fun hT => nonunits.subset_compl_ball hT (mem_ball_iff_norm.mpr h)

omit [FiniteDimensional ℝ F] in
/-- **A priori bound.** On the uniform interval, `‖Y t − 1‖ ≤ 1/3`. -/
theorem norm_sub_one_le_of_jacobi_operator {Y Y' R : ℝ → F →L[ℝ] F} {Λ ρ : ℝ} (hρ : 0 ≤ ρ)
    (hΛ : 0 ≤ Λ) (hΛρ : Λ * ρ ^ 2 ≤ 1 / 4)
    (hY : ∀ t ∈ Icc 0 ρ, HasDerivWithinAt Y (Y' t) (Icc 0 ρ) t)
    (hY' : ∀ t ∈ Icc 0 ρ, HasDerivWithinAt Y' (-((R t).comp (Y t))) (Icc 0 ρ) t)
    (hY0 : Y 0 = 1) (hY'0 : Y' 0 = 0) (hRbd : ∀ t ∈ Icc 0 ρ, ‖R t‖ ≤ Λ) :
    ∀ t ∈ Icc 0 ρ, ‖Y t - 1‖ ≤ 1 / 3 := by
  have hYc : ContinuousOn Y (Icc 0 ρ) := fun t ht => (hY t ht).continuousWithinAt
  obtain ⟨t₀, ht₀, hmax⟩ := isCompact_Icc.exists_isMaxOn (nonempty_Icc.2 hρ)
    (continuous_norm.comp_continuousOn hYc)
  have hM : ∀ t ∈ Icc 0 ρ, ‖Y t‖ ≤ ‖Y t₀‖ := fun t ht => isMaxOn_iff.mp hmax t ht
  have hM0 : 0 ≤ ‖Y t₀‖ := norm_nonneg _
  have h1 : ∀ t ∈ Icc 0 ρ, ‖Y' t - Y' 0‖ ≤ (Λ * ‖Y t₀‖) * (t - 0) := by
    refine norm_image_sub_le_of_norm_deriv_le_segment' hY' fun t ht => ?_
    have ht' : t ∈ Icc 0 ρ := Ico_subset_Icc_self ht
    rw [norm_neg]
    calc ‖(R t).comp (Y t)‖ ≤ ‖R t‖ * ‖Y t‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ Λ * ‖Y t₀‖ := mul_le_mul (hRbd t ht') (hM t ht') (norm_nonneg _) hΛ
  have h2 : ∀ t ∈ Icc 0 ρ, ‖Y' t‖ ≤ Λ * ‖Y t₀‖ * ρ := by
    intro t ht
    have h := h1 t ht
    rw [hY'0, sub_zero, sub_zero] at h
    exact h.trans (mul_le_mul_of_nonneg_left ht.2 (mul_nonneg hΛ hM0))
  have h3 : ∀ t ∈ Icc 0 ρ, ‖Y t - Y 0‖ ≤ (Λ * ‖Y t₀‖ * ρ) * (t - 0) :=
    norm_image_sub_le_of_norm_deriv_le_segment' hY fun t ht => h2 t (Ico_subset_Icc_self ht)
  have h4 : ∀ t ∈ Icc 0 ρ, ‖Y t - 1‖ ≤ ‖Y t₀‖ / 4 := by
    intro t ht
    have h := h3 t ht
    rw [hY0, sub_zero] at h
    calc ‖Y t - 1‖ ≤ Λ * ‖Y t₀‖ * ρ * t := h
      _ ≤ Λ * ‖Y t₀‖ * ρ * ρ :=
          mul_le_mul_of_nonneg_left ht.2 (mul_nonneg (mul_nonneg hΛ hM0) hρ)
      _ = ‖Y t₀‖ * (Λ * ρ ^ 2) := by ring
      _ ≤ ‖Y t₀‖ * (1 / 4) := mul_le_mul_of_nonneg_left hΛρ hM0
      _ = ‖Y t₀‖ / 4 := by ring
  have hone : ‖(1 : F →L[ℝ] F)‖ ≤ 1 := ContinuousLinearMap.norm_id_le
  have hle : ‖Y t₀‖ ≤ ‖Y t₀ - 1‖ + ‖(1 : F →L[ℝ] F)‖ := by
    calc ‖Y t₀‖ = ‖(Y t₀ - 1) + 1‖ := by rw [sub_add_cancel]
      _ ≤ ‖Y t₀ - 1‖ + ‖(1 : F →L[ℝ] F)‖ := norm_add_le _ _
  have hM43 : ‖Y t₀‖ ≤ 4 / 3 := by linarith [h4 t₀ ht₀]
  intro t ht
  linarith [h4 t ht]

omit [FiniteDimensional ℝ F] in
/-- The derivative of `t ↦ Y t a` from the derivative of `t ↦ Y t`. -/
theorem hasDerivWithinAt_clm_apply_const {Y : ℝ → F →L[ℝ] F} {Y₁ : F →L[ℝ] F} {s : Set ℝ} {t : ℝ}
    (hY : HasDerivWithinAt Y Y₁ s t) (a : F) :
    HasDerivWithinAt (fun τ => Y τ a) (Y₁ a) s t :=
  (ContinuousLinearMap.apply ℝ F a).hasFDerivAt.comp_hasDerivWithinAt t hY

/-- **Wronskian identity.** `⟪Y' t a, Y t b⟫ = ⟪Y t a, Y' t b⟫` on the interval. -/
theorem inner_deriv_apply_eq_of_jacobi_operator {Y Y' R : ℝ → F →L[ℝ] F} {ρ : ℝ}
    (hY : ∀ t ∈ Icc 0 ρ, HasDerivWithinAt Y (Y' t) (Icc 0 ρ) t)
    (hY' : ∀ t ∈ Icc 0 ρ, HasDerivWithinAt Y' (-((R t).comp (Y t))) (Icc 0 ρ) t)
    (hY'0 : Y' 0 = 0) (hRsa : ∀ t ∈ Icc 0 ρ, IsSelfAdjoint (R t)) (a b : F) :
    ∀ t ∈ Icc 0 ρ, ⟪Y' t a, Y t b⟫_ℝ = ⟪Y t a, Y' t b⟫_ℝ := by
  set w : ℝ → ℝ := fun t => ⟪Y' t a, Y t b⟫_ℝ - ⟪Y t a, Y' t b⟫_ℝ with hw
  have hder : ∀ t ∈ Icc 0 ρ, HasDerivWithinAt w 0 (Icc 0 ρ) t := by
    intro t ht
    have h1 := (hasDerivWithinAt_clm_apply_const (hY' t ht) a).inner ℝ
      (hasDerivWithinAt_clm_apply_const (hY t ht) b)
    have h2 := (hasDerivWithinAt_clm_apply_const (hY t ht) a).inner ℝ
      (hasDerivWithinAt_clm_apply_const (hY' t ht) b)
    have hsymm : ⟪R t (Y t a), Y t b⟫_ℝ = ⟪Y t a, R t (Y t b)⟫_ℝ :=
      (hRsa t ht).isSymmetric (Y t a) (Y t b)
    convert h1.sub h2 using 1
    simp only [neg_apply, ContinuousLinearMap.comp_apply, inner_neg_left, inner_neg_right]
    change 0 = _ + -⟪R t (Y t a), Y t b⟫_ℝ - (-⟪Y t a, R t (Y t b)⟫_ℝ + _)
    rw [hsymm]
    ring
  have hconst := norm_image_sub_le_of_norm_deriv_le_segment' hder
    (fun _ _ => (norm_zero : ‖(0 : ℝ)‖ = 0).le)
  intro t ht
  have h := hconst t ht
  rw [zero_mul, norm_le_zero_iff, sub_eq_zero] at h
  have hw0 : w 0 = 0 := by simp only [hw, hY'0, zero_apply, inner_zero_left,
    inner_zero_right, sub_zero]
  have : w t = 0 := h.trans hw0
  simp only [hw] at this
  linarith

/-- **The Riccati operator is negative semidefinite.** With `A t = Y' t * (Y t)⁻¹`, `A` is symmetric,
`A' = −R − A²` and `A 0 = 0`, hence `⟪A t v, v⟫ ≤ 0`. -/
theorem inner_riccati_apply_self_nonpos {Y Y' R : ℝ → F →L[ℝ] F} {ρ : ℝ}
    (hY : ∀ t ∈ Icc 0 ρ, HasDerivWithinAt Y (Y' t) (Icc 0 ρ) t)
    (hY' : ∀ t ∈ Icc 0 ρ, HasDerivWithinAt Y' (-((R t).comp (Y t))) (Icc 0 ρ) t)
    (hY'0 : Y' 0 = 0) (hRsa : ∀ t ∈ Icc 0 ρ, IsSelfAdjoint (R t))
    (hRpos : ∀ t ∈ Icc 0 ρ, ∀ a : F, 0 ≤ ⟪R t a, a⟫_ℝ) (hunit : ∀ t ∈ Icc 0 ρ, IsUnit (Y t)) :
    ∀ t ∈ Icc 0 ρ, ∀ v : F, ⟪(Y' t * Ring.inverse (Y t)) v, v⟫_ℝ ≤ 0 := by
  set U : ℝ → F →L[ℝ] F := fun t => Ring.inverse (Y t) with hUdef
  set A : ℝ → F →L[ℝ] F := fun t => Y' t * U t with hAdef
  have hYU : ∀ t ∈ Icc 0 ρ, Y t * U t = 1 := fun t ht => Ring.mul_inverse_cancel (Y t) (hunit t ht)
  have hUY : ∀ t ∈ Icc 0 ρ, U t * Y t = 1 := fun t ht => Ring.inverse_mul_cancel (Y t) (hunit t ht)
  have hW := inner_deriv_apply_eq_of_jacobi_operator hY hY' hY'0 hRsa
  -- `A` is symmetric
  have hAsymm : ∀ t ∈ Icc 0 ρ, ∀ x y : F, ⟪A t x, y⟫_ℝ = ⟪x, A t y⟫_ℝ := by
    intro t ht x y
    have hx : Y t (U t x) = x := by
      change (Y t * U t) x = x
      rw [hYU t ht, one_apply_eq_self]
    have hy : Y t (U t y) = y := by
      change (Y t * U t) y = y
      rw [hYU t ht, one_apply_eq_self]
    have h := hW (U t x) (U t y) t ht
    rw [hx, hy] at h
    exact h
  -- derivative of `U`
  have hU' : ∀ t ∈ Icc 0 ρ, HasDerivWithinAt U (-(U t * Y' t * U t)) (Icc 0 ρ) t := by
    intro t ht
    obtain ⟨u, hu⟩ := hunit t ht
    have hl : HasFDerivAt Ring.inverse
        (-ContinuousLinearMap.mulLeftRight ℝ (F →L[ℝ] F) (U t) (U t)) (Y t) := by
      have h := hasFDerivAt_ringInverse (𝕜 := ℝ) u
      rw [← Ring.inverse_unit u, hu] at h
      exact h
    exact (hl.comp_hasDerivWithinAt t (hY t ht)).congr_deriv
      (by rw [neg_apply, ContinuousLinearMap.mulLeftRight_apply])
  -- derivative of `A`
  have hA' : ∀ t ∈ Icc 0 ρ, HasDerivWithinAt A (-(R t) - A t * A t) (Icc 0 ρ) t := by
    intro t ht
    have h := (hY' t ht).clm_comp (hU' t ht)
    convert h using 1
    change -(R t) - Y' t * U t * (Y' t * U t) =
      -((R t) * Y t) * U t + Y' t * -(U t * Y' t * U t)
    have e1 : R t * Y t * U t = R t := by rw [mul_assoc, hYU t ht, mul_one]
    have e2 : Y' t * -(U t * Y' t * U t) = -(Y' t * U t * (Y' t * U t)) := by noncomm_ring
    rw [neg_mul, e1, e2, sub_eq_add_neg]
  -- `t ↦ ⟪A t v, v⟫` is antitone
  intro t ht v
  set q : ℝ → ℝ := fun τ => ⟪A τ v, v⟫_ℝ with hq
  have hq' : ∀ τ ∈ Icc 0 ρ, HasDerivWithinAt q (-⟪R τ v, v⟫_ℝ - ⟪A τ v, A τ v⟫_ℝ) (Icc 0 ρ) τ := by
    intro τ hτ
    have h := (hasDerivWithinAt_clm_apply_const (hA' τ hτ) v).inner ℝ
      (hasDerivWithinAt_const τ (Icc 0 ρ) v)
    convert h using 1
    rw [inner_zero_right, zero_add, sub_apply, neg_apply, inner_sub_left, inner_neg_left]
    change _ = -⟪R τ v, v⟫_ℝ - ⟪A τ (A τ v), v⟫_ℝ
    rw [hAsymm τ hτ (A τ v) v]
  have hanti : AntitoneOn q (Icc 0 ρ) := by
    refine antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc 0 ρ)
      (fun τ hτ => (hq' τ hτ).continuousWithinAt)
      (fun τ hτ => (hq' τ (interior_subset hτ)).mono interior_subset) fun τ hτ => ?_
    have h1 := hRpos τ (interior_subset hτ) v
    have h2 := real_inner_self_nonneg (x := A τ v)
    linarith
  have h0 : (0 : ℝ) ∈ Icc 0 ρ := ⟨le_rfl, ht.1.trans ht.2⟩
  have hq0 : q 0 = 0 := by
    simp only [hq, hAdef, hY'0, zero_mul, zero_apply, inner_zero_left]
  have h := hanti h0 ht ht.1
  rw [hq0] at h
  exact h

/-- **S3-SHIFT kernel (frozen name; `ContinuousOn R` dropped, unused).** `Y'' = −R Y`, `Y 0 = 1`,
`Y' 0 = 0`, `R` self-adjoint, positive semidefinite, `‖R‖ ≤ Λ`. On the uniform interval `[0, ρ]` with
`Λ ρ² ≤ 1/4`, `Y` is invertible and `‖Y t a‖ ≤ ‖a‖`. -/
theorem norm_apply_le_of_jacobi_operator {Y Y' R : ℝ → F →L[ℝ] F} {Λ ρ : ℝ} (hρ : 0 < ρ)
    (hΛ : 0 ≤ Λ) (hΛρ : Λ * ρ ^ 2 ≤ 1 / 4)
    (hY : ∀ t ∈ Icc 0 ρ, HasDerivWithinAt Y (Y' t) (Icc 0 ρ) t)
    (hY' : ∀ t ∈ Icc 0 ρ, HasDerivWithinAt Y' (-((R t).comp (Y t))) (Icc 0 ρ) t)
    (hY0 : Y 0 = 1) (hY'0 : Y' 0 = 0)
    (hRsa : ∀ t ∈ Icc 0 ρ, IsSelfAdjoint (R t)) (hRpos : ∀ t ∈ Icc 0 ρ, ∀ a : F, 0 ≤ ⟪R t a, a⟫_ℝ)
    (hRbd : ∀ t ∈ Icc 0 ρ, ‖R t‖ ≤ Λ) :
    ∀ t ∈ Icc 0 ρ, IsUnit (Y t) ∧ ∀ a : F, ‖Y t a‖ ≤ ‖a‖ := by
  have hsub := norm_sub_one_le_of_jacobi_operator hρ.le hΛ hΛρ hY hY' hY0 hY'0 hRbd
  have hunit : ∀ t ∈ Icc 0 ρ, IsUnit (Y t) := fun t ht =>
    isUnit_of_norm_sub_one_lt_one (lt_of_le_of_lt (hsub t ht) (by norm_num))
  have hA := inner_riccati_apply_self_nonpos hY hY' hY'0 hRsa hRpos hunit
  intro t ht
  refine ⟨hunit t ht, fun a => ?_⟩
  set f : ℝ → ℝ := fun τ => ⟪Y τ a, Y τ a⟫_ℝ with hf
  have hf' : ∀ τ ∈ Icc 0 ρ, HasDerivWithinAt f (2 * ⟪(Y' τ * Ring.inverse (Y τ)) (Y τ a), Y τ a⟫_ℝ)
      (Icc 0 ρ) τ := by
    intro τ hτ
    have h := (hasDerivWithinAt_clm_apply_const (hY τ hτ) a).inner ℝ
      (hasDerivWithinAt_clm_apply_const (hY τ hτ) a)
    convert h using 1
    have hinv : (Y' τ * Ring.inverse (Y τ)) (Y τ a) = Y' τ a := by
      change Y' τ ((Ring.inverse (Y τ) * Y τ) a) = Y' τ a
      rw [Ring.inverse_mul_cancel (Y τ) (hunit τ hτ), one_apply_eq_self]
    rw [hinv, real_inner_comm (Y τ a) (Y' τ a)]
    ring
  have hanti : AntitoneOn f (Icc 0 ρ) := by
    refine antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc 0 ρ)
      (fun τ hτ => (hf' τ hτ).continuousWithinAt)
      (fun τ hτ => (hf' τ (interior_subset hτ)).mono interior_subset) fun τ hτ => ?_
    have h := hA τ (interior_subset hτ) (Y τ a)
    linarith
  have h0 : (0 : ℝ) ∈ Icc 0 ρ := ⟨le_rfl, hρ.le⟩
  have h := hanti h0 ht ht.1
  simp only [hf, hY0, one_apply_eq_self, real_inner_self_eq_norm_sq] at h
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp h

end DifferentialGeometry.Geometry.FiniteSoul
