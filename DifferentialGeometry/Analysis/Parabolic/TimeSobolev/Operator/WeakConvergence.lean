import DifferentialGeometry.Analysis.Parabolic.TimeSobolev.Operator.Basic
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Analysis.Normed.Operator.BanachSteinhaus

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter
open scoped NNReal

namespace DifferentialGeometry.Analysis.Parabolic.TimeSobolev

variable {X Y : Type*}
variable [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
variable [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]
variable {T : ℝ}

omit [CompleteSpace X] [CompleteSpace Y] in
private theorem timeOp_sub
    (A B : ℝ → X →L[ℝ] Y)
    (hA : AEStronglyMeasurable A (timeMeasure T))
    (hB : AEStronglyMeasurable B (timeMeasure T))
    (CA CB C : NNReal)
    (hCA : ∀ᵐ t ∂timeMeasure T, ‖A t‖ ≤ (CA : ℝ))
    (hCB : ∀ᵐ t ∂timeMeasure T, ‖B t‖ ≤ (CB : ℝ))
    (hC : ∀ᵐ t ∂timeMeasure T, ‖A t - B t‖ ≤ (C : ℝ)) :
    timeOp A hA CA hCA - timeOp B hB CB hCB =
      timeOp (fun t ↦ A t - B t) (hA.sub hB) C hC := by
  ext f
  simp only [sub_apply]
  filter_upwards [Lp.coeFn_sub (timeOp A hA CA hCA f) (timeOp B hB CB hCB f),
    timeOp_apply_ae A hA CA hCA f, timeOp_apply_ae B hB CB hCB f,
    timeOp_apply_ae (fun t ↦ A t - B t) (hA.sub hB) C hC f]
    with t hsub hAf hBf hDf
  exact calc
    ((timeOp A hA CA hCA f - timeOp B hB CB hCB f : timeL2 Y T) : ℝ → Y) t
        = ((timeOp A hA CA hCA f : ℝ → Y) -
          (timeOp B hB CB hCB f : ℝ → Y)) t := hsub
    _ = A t (f t) - B t (f t) := by rw [Pi.sub_apply, hAf, hBf]
    _ = (A t - B t) (f t) :=
      (sub_apply (A t) (B t) (f t)).symm
    _ = (timeOp (fun t ↦ A t - B t) (hA.sub hB) C hC f : ℝ → Y) t := hDf.symm

theorem timeOp_weak_lim
    (A : ℕ → ℝ → X →L[ℝ] Y) (A_lim : ℝ → X →L[ℝ] Y)
    (hA : ∀ n, AEStronglyMeasurable (A n) (timeMeasure T))
    (hA_lim : AEStronglyMeasurable A_lim (timeMeasure T))
    (C : ℕ → NNReal) (C_lim : NNReal)
    (hC : ∀ n, ∀ᵐ t ∂timeMeasure T, ‖A n t‖ ≤ (C n : ℝ))
    (hC_lim : ∀ᵐ t ∂timeMeasure T, ‖A_lim t‖ ≤ (C_lim : ℝ))
    (ε : ℕ → NNReal) (hε : Tendsto ε atTop (nhds 0))
    (hconv : ∀ n, ∀ᵐ t ∂timeMeasure T, ‖A n t - A_lim t‖ ≤ (ε n : ℝ))
    (u : ℕ → timeL2 X T) (u_lim : timeL2 X T)
    (hu : ∀ z, Tendsto (fun n ↦ inner ℝ (u n) z) atTop
      (nhds (inner ℝ u_lim z))) :
    ∀ z, Tendsto
      (fun n ↦ inner ℝ (timeOp (A n) (hA n) (C n) (hC n) (u n)) z) atTop
      (nhds (inner ℝ (timeOp A_lim hA_lim C_lim hC_lim u_lim) z)) := by
  let L : timeL2 X T →L[ℝ] timeL2 Y T := timeOp A_lim hA_lim C_lim hC_lim
  let Ln : ℕ → timeL2 X T →L[ℝ] timeL2 Y T :=
    fun n ↦ timeOp (A n) (hA n) (C n) (hC n)
  obtain ⟨D, huD⟩ := banach_steinhaus (g := fun n ↦ innerSL ℝ (u n)) fun z ↦ by
    simpa only [innerSL_apply_apply, forall_mem_range] using
      (isBounded_iff_forall_norm_le.1
        (Metric.isBounded_range_of_tendsto
          (fun n ↦ inner ℝ (u n) z) (hu z)))
  have hu_norm (n : ℕ) : ‖u n‖ ≤ D := by
    simpa only [innerSL_apply_norm] using huD n
  have hop (n : ℕ) : ‖Ln n - L‖ ≤ (ε n : ℝ) := by
    rw [show Ln n - L = timeOp (fun t ↦ A n t - A_lim t)
      ((hA n).sub hA_lim) (ε n) (hconv n) by
        simpa only [Ln, L] using
          timeOp_sub (A n) A_lim (hA n) hA_lim (C n) C_lim (ε n)
            (hC n) hC_lim (hconv n)]
    exact timeOp_norm_le _ _ _ _
  have herr_norm : Tendsto (fun n ↦ ‖(Ln n - L) (u n)‖) atTop (nhds 0) := by
    apply squeeze_zero (fun n ↦ norm_nonneg _)
      (fun n ↦ (Ln n - L).le_opNorm (u n) |>.trans <|
        mul_le_mul (hop n) (hu_norm n) (norm_nonneg _) (NNReal.coe_nonneg (ε n)))
    simpa only [NNReal.coe_zero, zero_mul] using
      (NNReal.tendsto_coe.2 hε).mul_const D
  have herr : Tendsto (fun n ↦ (Ln n - L) (u n)) atTop (nhds 0) :=
    tendsto_zero_iff_norm_tendsto_zero.2 herr_norm
  intro z
  have herr_inner : Tendsto (fun n ↦ inner ℝ ((Ln n - L) (u n)) z) atTop
      (nhds 0) := by
    simpa only [inner_zero_left] using herr.inner tendsto_const_nhds
  have hfixed : Tendsto (fun n ↦ inner ℝ (L (u n)) z) atTop
      (nhds (inner ℝ (L u_lim) z)) := by
    simpa only [ContinuousLinearMap.adjoint_inner_right] using hu (L.adjoint z)
  simpa only [Ln, L, sub_apply, inner_sub_left,
    sub_add_cancel, zero_add] using
    herr_inner.add hfixed

theorem timeOp_weak_uniform
    (A : ℕ → ℝ → X →L[ℝ] Y) (A_lim : ℝ → X →L[ℝ] Y)
    (hA : ∀ n, AEStronglyMeasurable (A n) (timeMeasure T))
    (hA_lim : AEStronglyMeasurable A_lim (timeMeasure T))
    (C : ℕ → NNReal) (C_lim : NNReal)
    (hC : ∀ n, ∀ᵐ t ∂timeMeasure T, ‖A n t‖ ≤ (C n : ℝ))
    (hC_lim : ∀ᵐ t ∂timeMeasure T, ‖A_lim t‖ ≤ (C_lim : ℝ))
    (hconv : ∀ δ : ℝ, 0 < δ → ∀ᶠ n in atTop,
      ∀ᵐ t ∂timeMeasure T, ‖A n t - A_lim t‖ ≤ δ)
    (u : ℕ → timeL2 X T) (u_lim : timeL2 X T)
    (hu : ∀ z, Tendsto (fun n ↦ inner ℝ (u n) z) atTop
      (nhds (inner ℝ u_lim z))) :
    ∀ z, Tendsto
      (fun n ↦ inner ℝ (timeOp (A n) (hA n) (C n) (hC n) (u n)) z) atTop
      (nhds (inner ℝ (timeOp A_lim hA_lim C_lim hC_lim u_lim) z)) := by
  let L : timeL2 X T →L[ℝ] timeL2 Y T := timeOp A_lim hA_lim C_lim hC_lim
  let Ln : ℕ → timeL2 X T →L[ℝ] timeL2 Y T :=
    fun n ↦ timeOp (A n) (hA n) (C n) (hC n)
  obtain ⟨D, huD⟩ := banach_steinhaus (g := fun n ↦ innerSL ℝ (u n)) fun z ↦ by
    simpa only [innerSL_apply_apply, forall_mem_range] using
      (isBounded_iff_forall_norm_le.1
        (Metric.isBounded_range_of_tendsto
          (fun n ↦ inner ℝ (u n) z) (hu z)))
  have hu_norm (n : ℕ) : ‖u n‖ ≤ D := by
    simpa only [innerSL_apply_norm] using huD n
  have hD : 0 ≤ D := (norm_nonneg (u 0)).trans (hu_norm 0)
  have herr_norm : Tendsto (fun n ↦ ‖(Ln n - L) (u n)‖) atTop (nhds 0) := by
    rw [Metric.tendsto_nhds]
    intro e he
    let δ : ℝ := e / (D + 1)
    have hden : 0 < D + 1 := by linarith
    have hδ : 0 < δ := div_pos he hden
    let δnn : NNReal := ⟨δ, hδ.le⟩
    filter_upwards [hconv δ hδ] with n hn
    have hop : ‖Ln n - L‖ ≤ δ := by
      rw [show Ln n - L = timeOp (fun t ↦ A n t - A_lim t)
        ((hA n).sub hA_lim) δnn hn by
          simpa only [Ln, L] using
            timeOp_sub (A n) A_lim (hA n) hA_lim (C n) C_lim δnn
              (hC n) hC_lim hn]
      change ‖timeOp (fun t ↦ A n t - A_lim t) ((hA n).sub hA_lim) δnn hn‖ ≤
        (δnn : ℝ)
      exact timeOp_norm_le _ _ δnn hn
    have hmul : δ * D < e := by
      dsimp only [δ]
      rw [div_mul_eq_mul_div, div_lt_iff₀ hden]
      nlinarith
    have hnorm : ‖(Ln n - L) (u n)‖ < e :=
      ((Ln n - L).le_opNorm (u n)).trans_lt
        ((mul_le_mul hop (hu_norm n) (norm_nonneg _) hδ.le).trans_lt hmul)
    simpa only [Real.dist_eq, sub_zero, abs_of_nonneg (norm_nonneg _)] using hnorm
  have herr : Tendsto (fun n ↦ (Ln n - L) (u n)) atTop (nhds 0) :=
    tendsto_zero_iff_norm_tendsto_zero.2 herr_norm
  intro z
  have herr_inner : Tendsto (fun n ↦ inner ℝ ((Ln n - L) (u n)) z) atTop
      (nhds 0) := by
    simpa only [inner_zero_left] using herr.inner tendsto_const_nhds
  have hfixed : Tendsto (fun n ↦ inner ℝ (L (u n)) z) atTop
      (nhds (inner ℝ (L u_lim) z)) := by
    simpa only [ContinuousLinearMap.adjoint_inner_right] using hu (L.adjoint z)
  simpa only [Ln, L, sub_apply, inner_sub_left,
    sub_add_cancel, zero_add] using
    herr_inner.add hfixed

end DifferentialGeometry.Analysis.Parabolic.TimeSobolev

end
