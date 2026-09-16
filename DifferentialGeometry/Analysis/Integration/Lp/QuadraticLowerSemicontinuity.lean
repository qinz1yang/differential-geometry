import DifferentialGeometry.Analysis.Integration.Lp.Bilinear
import Mathlib.Analysis.Normed.Module.DoubleDual
import Mathlib.Analysis.Normed.Operator.BanachSteinhaus
import Mathlib.Topology.Algebra.Order.LiminfLimsup

noncomputable section

open Filter MeasureTheory Set
open scoped ENNReal Topology

namespace MeasureTheory

variable {P X : Type*} [MeasurableSpace P] {μ : Measure P}
  [NormedAddCommGroup X] [NormedSpace ℝ X]

private theorem norm_bounded_of_tendsto_dual {Y : Type*}
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] (u : ℕ → Y) (v : Y)
    (hu : ∀ F : Y →L[ℝ] ℝ, Tendsto (fun n => F (u n)) atTop (𝓝 (F v))) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ n, ‖u n‖ ≤ D := by
  obtain ⟨D, hD⟩ := banach_steinhaus
    (g := fun n => NormedSpace.inclusionInDoubleDual ℝ Y (u n)) fun F => by
      simpa only [NormedSpace.dual_def, forall_mem_range] using
        (isBounded_iff_forall_norm_le.1
          (Metric.isBounded_range_of_tendsto (fun n => F (u n)) (hu F)))
  have hb (n : ℕ) : ‖u n‖ ≤ D := by
    have hn := hD n
    change ‖NormedSpace.inclusionInDoubleDualLi ℝ (u n)‖ ≤ D at hn
    simpa only [LinearIsometry.norm_map] using hn
  exact ⟨D, (norm_nonneg (u 0)).trans (hb 0), hb⟩

def integralBilinearLpRight (B : P → X →L[ℝ] X →L[ℝ] ℝ)
    (hB : ∀ x y, AEStronglyMeasurable (fun t => B t x y) μ)
    {C : ℝ} (hC : ∀ᵐ t ∂μ, ‖B t‖ ≤ C) (u : Lp X 2 μ) :
    Lp X 2 μ →L[ℝ] ℝ where
  toFun v := ∫ t, B t (u t) (v t) ∂μ
  map_add' v w := by
    rw [← integral_add
      (integrable_bilinear_of_apply_aestronglyMeasurable B hB hC (Lp.memLp u) (Lp.memLp v))
      (integrable_bilinear_of_apply_aestronglyMeasurable B hB hC (Lp.memLp u) (Lp.memLp w))]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_add v w] with t ht
    rw [ht, Pi.add_apply, map_add]
  map_smul' r v := by
    rw [← integral_smul]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_smul r v] with t ht
    simp only [ht, Pi.smul_apply, map_smul, RingHom.id_apply]
  cont := continuous_integral_bilinear_lp_right B hB hC u

theorem tendsto_integral_bilinear_of_weak
    (B : ℕ → P → X →L[ℝ] X →L[ℝ] ℝ) (B₀ : P → X →L[ℝ] X →L[ℝ] ℝ)
    (hB : ∀ n x y, AEStronglyMeasurable (fun t => B n t x y) μ)
    (hB₀ : ∀ x y, AEStronglyMeasurable (fun t => B₀ t x y) μ)
    (C : ℕ → ℝ) (C₀ : ℝ)
    (hC : ∀ n, ∀ᵐ t ∂μ, ‖B n t‖ ≤ C n)
    (hC₀ : ∀ᵐ t ∂μ, ‖B₀ t‖ ≤ C₀)
    (hconv : ∀ δ : ℝ, 0 < δ → ∀ᶠ n in atTop, ∀ᵐ t ∂μ, ‖B n t - B₀ t‖ ≤ δ)
    (u : ℕ → Lp X 2 μ) (u₀ v : Lp X 2 μ)
    (hu : ∀ F : Lp X 2 μ →L[ℝ] ℝ,
      Tendsto (fun n => F (u n)) atTop (𝓝 (F u₀))) :
    Tendsto (fun n => ∫ t, B n t (v t) (u n t) ∂μ) atTop
      (𝓝 (∫ t, B₀ t (v t) (u₀ t) ∂μ)) := by
  obtain ⟨D, hD, huD⟩ := norm_bounded_of_tendsto_dual u u₀ hu
  have hfixed := hu (integralBilinearLpRight B₀ hB₀ hC₀ v)
  have herr : Tendsto
      (fun n => (∫ t, B n t (v t) (u n t) ∂μ) -
        ∫ t, B₀ t (v t) (u n t) ∂μ) atTop (𝓝 0) := by
    rw [Metric.tendsto_nhds]
    intro ε hε
    have hden : 0 < ‖v‖ * D + 1 := by positivity
    let δ : ℝ := ε / (‖v‖ * D + 1)
    have hδ : 0 < δ := div_pos hε hden
    filter_upwards [hconv δ hδ] with n hn
    have heq : (∫ t, B n t (v t) (u n t) ∂μ) -
        (∫ t, B₀ t (v t) (u n t) ∂μ) =
        ∫ t, (B n t - B₀ t) (v t) (u n t) ∂μ := by
      rw [← integral_sub
        (integrable_bilinear_of_apply_aestronglyMeasurable (B n) (hB n) (hC n)
          (Lp.memLp v) (Lp.memLp (u n)))
        (integrable_bilinear_of_apply_aestronglyMeasurable B₀ hB₀ hC₀
          (Lp.memLp v) (Lp.memLp (u n)))]
      rfl
    rw [dist_zero_right, heq]
    have hnorm := norm_integral_bilinear_le_lp_norm (fun t => B n t - B₀ t)
      (fun x y => (hB n x y).sub (hB₀ x y)) hδ.le hn v (u n)
    apply hnorm.trans_lt
    calc
      δ * (‖v‖ * ‖u n‖) ≤ δ * (‖v‖ * D) := by gcongr; exact huD n
      _ < ε := by
        dsimp only [δ]
        rw [div_mul_eq_mul_div, div_lt_iff₀ hden]
        nlinarith [mul_nonneg (norm_nonneg v) hD]
  simpa only [integralBilinearLpRight, ContinuousLinearMap.coe_mk',
    LinearMap.coe_mk, AddHom.coe_mk, sub_add_cancel, zero_add] using herr.add hfixed



theorem isBoundedUnder_integral_quadratic_of_weak
    (B : ℕ → P → X →L[ℝ] X →L[ℝ] ℝ)
    (hB : ∀ n x y, AEStronglyMeasurable (fun t => B n t x y) μ)
    {C : ℝ} (hC : ∀ᶠ n in atTop, ∀ᵐ t ∂μ, ‖B n t‖ ≤ C)
    (u : ℕ → Lp X 2 μ) (u₀ : Lp X 2 μ)
    (hu : ∀ F : Lp X 2 μ →L[ℝ] ℝ,
      Tendsto (fun n => F (u n)) atTop (𝓝 (F u₀))) :
    IsBoundedUnder (· ≤ ·) atTop
      (fun n => ‖∫ t, B n t (u n t) (u n t) ∂μ‖) := by
  obtain ⟨D, hD, huD⟩ := norm_bounded_of_tendsto_dual u u₀ hu
  refine ⟨max 0 C * (D * D), ?_⟩
  change ∀ᶠ n in atTop, ‖∫ t, B n t (u n t) (u n t) ∂μ‖ ≤ _
  filter_upwards [hC] with n hn
  have hb : ∀ᵐ t ∂μ, ‖B n t‖ ≤ max 0 C :=
    hn.mono fun t ht => ht.trans (le_max_right 0 C)
  have hnorm := norm_integral_bilinear_le_lp_norm (B n) (hB n)
    (le_max_left 0 C) hb (u n) (u n)
  apply hnorm.trans
  exact mul_le_mul_of_nonneg_left
    (mul_le_mul (huD n) (huD n) (norm_nonneg _) hD) (le_max_left 0 C)

theorem integral_quadratic_le_liminf_of_weak
    (B : ℕ → P → X →L[ℝ] X →L[ℝ] ℝ) (B₀ : P → X →L[ℝ] X →L[ℝ] ℝ)
    (hB : ∀ n x y, AEStronglyMeasurable (fun t => B n t x y) μ)
    (hB₀ : ∀ x y, AEStronglyMeasurable (fun t => B₀ t x y) μ)
    (C : ℕ → ℝ) (C₀ : ℝ)
    (hC : ∀ n, ∀ᵐ t ∂μ, ‖B n t‖ ≤ C n)
    (hC₀ : ∀ᵐ t ∂μ, ‖B₀ t‖ ≤ C₀)
    (hconv : ∀ δ : ℝ, 0 < δ → ∀ᶠ n in atTop, ∀ᵐ t ∂μ, ‖B n t - B₀ t‖ ≤ δ)
    (hpos : ∀ n, ∀ᵐ t ∂μ, ∀ x, 0 ≤ B n t x x)
    (u : ℕ → Lp X 2 μ) (u₀ : Lp X 2 μ)
    (hu : ∀ F : Lp X 2 μ →L[ℝ] ℝ,
      Tendsto (fun n => F (u n)) atTop (𝓝 (F u₀))) :
    (∫ t, B₀ t (u₀ t) (u₀ t) ∂μ) ≤
      liminf (fun n => ∫ t, B n t (u n t) (u n t) ∂μ) atTop := by
  let q : ℕ → ℝ := fun n => ∫ t, B n t (u n t) (u n t) ∂μ
  let q₀ : ℝ := ∫ t, B₀ t (u₀ t) (u₀ t) ∂μ
  have hleft := tendsto_integral_bilinear_of_weak B B₀ hB hB₀ C C₀ hC hC₀ hconv u u₀ u₀ hu
  have hright := tendsto_integral_bilinear_of_weak
    (fun n t => (B n t).flip) (fun t => (B₀ t).flip)
    (fun n x y => hB n y x) (fun x y => hB₀ y x) C C₀
    (fun n => (hC n).mono fun t ht => by simpa only [ContinuousLinearMap.opNorm_flip] using ht)
    (hC₀.mono fun t ht => by simpa only [ContinuousLinearMap.opNorm_flip] using ht)
    (fun δ hδ => (hconv δ hδ).mono fun n hn => hn.mono fun t ht => by
      have heq : (B n t).flip - (B₀ t).flip = (B n t - B₀ t).flip := rfl
      simpa only [heq, ContinuousLinearMap.opNorm_flip] using ht)
    u u₀ u₀ hu
  have hfixed := tendsto_integral_bilinear_of_weak B B₀ hB hB₀ C C₀ hC hC₀ hconv
    (fun _ => u₀) u₀ u₀ (fun _ => tendsto_const_nhds)
  let r : ℕ → ℝ := fun n =>
    (∫ t, B n t (u₀ t) (u n t) ∂μ) + (∫ t, B n t (u n t) (u₀ t) ∂μ) -
      ∫ t, B n t (u₀ t) (u₀ t) ∂μ
  have hr : Tendsto r atTop (𝓝 q₀) := by
    simpa only [ContinuousLinearMap.flip_apply, add_sub_cancel_left] using
      (hleft.add hright).sub hfixed
  have hi (n) (v w : Lp X 2 μ) :=
    integrable_bilinear_of_apply_aestronglyMeasurable (B n) (hB n) (hC n)
      (Lp.memLp v) (Lp.memLp w)
  have hrq (n) : r n ≤ q n := by
    have hn : 0 ≤ ∫ t, B n t ((u n - u₀) t) ((u n - u₀) t) ∂μ :=
      integral_nonneg_of_ae ((hpos n).mono fun t ht => ht _)
    have heq : (∫ t, B n t ((u n - u₀) t) ((u n - u₀) t) ∂μ) = q n - r n := by
      calc
        _ = ∫ t, B n t (u n t) (u n t) - B n t (u₀ t) (u n t) -
            B n t (u n t) (u₀ t) + B n t (u₀ t) (u₀ t) ∂μ := by
          apply integral_congr_ae
          filter_upwards [Lp.coeFn_sub (u n) u₀] with t ht
          simp only [ht, Pi.sub_apply, map_sub, sub_apply]
          ring
        _ = q n - r n := by
          have hab := integral_sub (hi n (u n) (u n)) (hi n u₀ (u n))
          have habc := integral_sub ((hi n (u n) (u n)).sub (hi n u₀ (u n)))
            (hi n (u n) u₀)
          have habcd := integral_add
            (((hi n (u n) (u n)).sub (hi n u₀ (u n))).sub (hi n (u n) u₀))
            (hi n u₀ u₀)
          simp only [Pi.sub_apply] at habc habcd
          rw [habcd, habc, hab]
          dsimp only [q, r]
          ring
    rw [heq] at hn
    linarith
  have hbound : ∀ᶠ n in atTop, ∀ᵐ t ∂μ, ‖B n t‖ ≤ 1 + C₀ := by
    filter_upwards [hconv 1 zero_lt_one] with n hn
    filter_upwards [hn, hC₀] with t ht ht₀
    exact (norm_le_norm_sub_add (B n t) (B₀ t)).trans (add_le_add ht ht₀)
  obtain ⟨D, hD⟩ := isBoundedUnder_integral_quadratic_of_weak B hB hbound u u₀ hu
  change ∀ᶠ n in atTop, ‖q n‖ ≤ D at hD
  have hqbound : ∀ᶠ n in atTop, q n ≤ D :=
    hD.mono fun n hn => (le_abs_self (q n)).trans hn
  have hcob : IsCoboundedUnder (· ≥ ·) atTop q :=
    isCoboundedUnder_ge_of_eventually_le atTop hqbound
  apply le_of_forall_lt
  intro a ha
  let b : ℝ := (a + q₀) / 2
  have hab : a < b := by dsimp only [b]; linarith
  have hbq : b < q₀ := by dsimp only [b]; linarith
  have hbv : ∀ᶠ n in atTop, b ≤ q n :=
    ((tendsto_order.1 hr).1 b hbq).mono fun n hn => hn.le.trans (hrq n)
  exact hab.trans_le (le_liminf_of_le hcob hbv)

end MeasureTheory
