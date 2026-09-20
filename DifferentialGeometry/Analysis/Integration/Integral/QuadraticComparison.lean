import DifferentialGeometry.Analysis.Integration.Lp.QuadraticDomination

noncomputable section
open Set Filter MeasureTheory
open scoped ENNReal

namespace DifferentialGeometry.Analysis

variable {X F : Type*} [MeasurableSpace X] [NormedAddCommGroup F] [NormedSpace ℝ F]
  {μ : Measure X}

theorem integral_quadratic_difference_le_of_coefficient_comparison
    {J : Type*} [Fintype J]
    (A₀ : F →L[ℝ] F →L[ℝ] ℝ) (hsym : ∀ v w, A₀ v w = A₀ w v)
    {lam ε : ℝ} (hlam : 0 < lam) (hε : 0 ≤ ε)
    (hcoerce : ∀ v, lam * ‖v‖ ^ 2 ≤ A₀ v v)
    (A B : X → F →L[ℝ] F →L[ℝ] ℝ)
    (hA : ∀ v w, AEStronglyMeasurable (fun x => A x v w) μ)
    (hB : ∀ v w, AEStronglyMeasurable (fun x => B x v w) μ)
    (hAdiff : ∀ᵐ x ∂μ, ‖A x - A₀‖ ≤ ε)
    (hBdiff : ∀ᵐ x ∂μ, ‖B x - A₀‖ ≤ ε)
    (G H : J → X → F) (hG : ∀ j, MemLp (G j) 2 μ) (hH : ∀ j, MemLp (H j) 2 μ)
    (horth : (∫ x, ∑ j : J, A₀ (H j x) (G j x - H j x) ∂μ) = 0)
    (hmin : (∑ j : J, ∫ x, A x (G j x) (G j x) ∂μ) ≤
      ∑ j : J, ∫ x, B x (H j x) (H j x) ∂μ)
    (henergy : (∑ j : J, ∫ x, ‖H j x‖ ^ 2 ∂μ) ≤ ∑ j : J, ∫ x, ‖G j x‖ ^ 2 ∂μ) :
    (∑ j : J, ∫ x, ‖G j x - H j x‖ ^ 2 ∂μ) ≤
      (2 * ε / lam) * ∑ j : J, ∫ x, ‖G j x‖ ^ 2 ∂μ := by
  let N (P : J → X → F) := ∑ j : J, ∫ x, ‖P j x‖ ^ 2 ∂μ
  let Q (C : X → F →L[ℝ] F →L[ℝ] ℝ) (P : J → X → F) :=
    ∑ j : J, ∫ x, C x (P j x) (P j x) ∂μ
  have hA₀ (P R : X → F) (hP : MemLp P 2 μ) (hR : MemLp R 2 μ) :
      Integrable (fun x => A₀ (P x) (R x)) μ :=
    integrable_bilinear_of_apply_aestronglyMeasurable (fun _ => A₀)
      (fun _ _ => aestronglyMeasurable_const) (Eventually.of_forall fun _ => le_rfl) hP hR
  have hD (C : X → F →L[ℝ] F →L[ℝ] ℝ)
      (hCm : ∀ v w, AEStronglyMeasurable (fun x => C x v w) μ)
      (hCd : ∀ᵐ x ∂μ, ‖C x - A₀‖ ≤ ε)
      (P : J → X → F) (hP : ∀ j, MemLp (P j) 2 μ) :
      |Q C P - Q (fun _ => A₀) P| ≤ ε * N P := by
    have hCi (j : J) : Integrable (fun x => (C x - A₀) (P j x) (P j x)) μ :=
      integrable_bilinear_of_apply_aestronglyMeasurable (fun x => C x - A₀)
        (fun v w => by simpa only [sub_apply, Pi.sub_def] using
          (hCm v w).sub aestronglyMeasurable_const) hCd (hP j) (hP j)
    have hCbound : ∀ᵐ x ∂μ, ‖C x‖ ≤ ε + ‖A₀‖ := by
      filter_upwards [hCd] with x hx
      calc
        ‖C x‖ = ‖C x - A₀ + A₀‖ := by congr 1; abel
        _ ≤ ‖C x - A₀‖ + ‖A₀‖ := norm_add_le (C x - A₀) A₀
        _ ≤ ε + ‖A₀‖ := add_le_add_left hx _
    have hCPi (j : J) : Integrable (fun x => C x (P j x) (P j x)) μ :=
      integrable_bilinear_of_apply_aestronglyMeasurable C hCm hCbound (hP j) (hP j)
    have hEq : Q C P - Q (fun _ => A₀) P =
        ∑ j : J, ∫ x, (C x - A₀) (P j x) (P j x) ∂μ := by
      dsimp only [Q]
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro j hj
      rw [← integral_sub (hCPi j) (hA₀ (P j) (P j) (hP j) (hP j))]
      apply integral_congr_ae
      exact Eventually.of_forall fun x => by simp only [sub_apply]
    rw [hEq]
    calc
      |∑ j : J, ∫ x, (C x - A₀) (P j x) (P j x) ∂μ| ≤
          ∑ j : J, |∫ x, (C x - A₀) (P j x) (P j x) ∂μ| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ j : J, ε * ∫ x, ‖P j x‖ ^ 2 ∂μ := by
        apply Finset.sum_le_sum
        intro j hj
        simpa only [Real.norm_eq_abs] using norm_integral_quadratic_le_integral_norm_sq
          (fun x => C x - A₀)
          (fun v w => by simpa only [sub_apply, Pi.sub_def] using
            (hCm v w).sub aestronglyMeasurable_const) hCd (hP j)
      _ = ε * N P := (Finset.mul_sum ..).symm
  have hDG := hD A hA hAdiff G hG
  have hDH := hD B hB hBdiff H hH
  let D := fun j x => G j x - H j x
  have hDi (j : J) : MemLp (D j) 2 μ := (hG j).sub (hH j)
  have hpair (v w : F) : A₀ (v - w) (v - w) = A₀ v v - A₀ w w - 2 * A₀ w (v - w) := by
    simp only [map_sub, sub_apply]
    rw [hsym v w]
    ring
  have horthSum : (∑ j : J, ∫ x, A₀ (H j x) (D j x) ∂μ) = 0 := by
    rw [← integral_finsetSum _ (fun j _ => hA₀ (H j) (D j) (hH j) (hDi j))]
    exact horth
  have hgap : Q (fun _ => A₀) D = Q (fun _ => A₀) G - Q (fun _ => A₀) H := by
    have heq (j : J) : (∫ x, A₀ (D j x) (D j x) ∂μ) =
        (∫ x, A₀ (G j x) (G j x) ∂μ) - (∫ x, A₀ (H j x) (H j x) ∂μ) -
          2 * ∫ x, A₀ (H j x) (D j x) ∂μ := by
      have hp : (fun x => A₀ (D j x) (D j x)) =
          fun x => (A₀ (G j x) (G j x) - A₀ (H j x) (H j x)) -
            2 * A₀ (H j x) (D j x) := funext fun x => hpair (G j x) (H j x)
      rw [hp]
      have hiDiff : Integrable (fun x => A₀ (G j x) (G j x) - A₀ (H j x) (H j x)) μ :=
        (hA₀ (G j) (G j) (hG j) (hG j)).sub (hA₀ (H j) (H j) (hH j) (hH j))
      have hiCross : Integrable (fun x => 2 * A₀ (H j x) (D j x)) μ :=
        (hA₀ (H j) (D j) (hH j) (hDi j)).const_mul 2
      rw [integral_sub hiDiff hiCross,
        integral_sub (hA₀ (G j) (G j) (hG j) (hG j))
          (hA₀ (H j) (H j) (hH j) (hH j)), integral_const_mul]
    dsimp only [Q]
    simp_rw [heq]
    rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
      horthSum, mul_zero, sub_zero]
  have hcoerceI : lam * N D ≤ Q (fun _ => A₀) D := by
    dsimp only [N, Q]
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j hj
    rw [← integral_const_mul]
    exact integral_mono_ae ((hDi j).norm.integrable_sq.const_mul lam)
      (hA₀ (D j) (D j) (hDi j) (hDi j)) (Eventually.of_forall fun x => hcoerce (D j x))
  have hbound : lam * N D ≤ 2 * ε * N G := by
    rw [hgap] at hcoerceI
    have hleft := (abs_le.mp hDG).1
    have hright := (abs_le.mp hDH).2
    have hEn : ε * N H ≤ ε * N G := mul_le_mul_of_nonneg_left henergy hε
    change Q A G ≤ Q B H at hmin
    linarith
  have hres := (le_div_iff₀ hlam).mpr (show N D * lam ≤ 2 * ε * N G by nlinarith)
  simpa only [div_mul_eq_mul_div] using hres

end DifferentialGeometry.Analysis

end
