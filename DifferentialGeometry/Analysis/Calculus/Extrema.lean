import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.LocalExtr.Basic

noncomputable section

open Filter
open scoped Topology

namespace DifferentialGeometry.Analysis.Calculus

theorem deriv_nonneg_of_isMaxOn_left {f : ℝ → ℝ} {a : ℝ}
    (hf : ∀ᶠ x in 𝓝[≤] a, f x ≤ f a)
    (hderiv : DifferentiableAt ℝ f a) :
    0 ≤ deriv f a := by
  have hder : HasDerivAt f (deriv f a) a := hderiv.hasDerivAt
  have ht : Tendsto (slope f a) (𝓝[≠] a) (𝓝 (deriv f a)) := hder.tendsto_slope
  have hsub_ne : Set.Iio a ⊆ {x : ℝ | x ≠ a} := by
    intro x hx
    exact ne_of_lt (Set.mem_Iio.mp hx)
  have hleft : Tendsto (slope f a) (𝓝[<] a) (𝓝 (deriv f a)) := by
    exact ht.mono_left (nhdsWithin_mono a hsub_ne)
  have hsub_le : Set.Iio a ⊆ Set.Iic a := by
    intro x hx
    exact le_of_lt (Set.mem_Iio.mp hx)
  have hf_left : ∀ᶠ x in 𝓝[<] a, f x ≤ f a := by
    exact (Filter.le_def.mp (nhdsWithin_mono a hsub_le)) {x : ℝ | f x ≤ f a} hf
  have hlt_filter : ∀ᶠ x in 𝓝[<] a, x < a := self_mem_nhdsWithin
  have hnonneg : ∀ᶠ x in 𝓝[<] a, 0 ≤ slope f a x := by
    filter_upwards [hf_left, hlt_filter] with x hx hlt
    unfold slope
    have hnum : f x - f a ≤ 0 := sub_nonpos.mpr hx
    have hden : x - a < 0 := sub_neg.mpr hlt
    have hinv : (x - a)⁻¹ ≤ 0 := inv_nonpos.mpr hden.le
    have hprod : 0 ≤ (f x - f a) * (x - a)⁻¹ := mul_nonneg_of_nonpos_of_nonpos hnum hinv
    simpa [smul_eq_mul, mul_comm] using hprod
  exact ge_of_tendsto hleft hnonneg

theorem deriv_nonpos_of_isMaxOn_right {f : ℝ → ℝ} {a : ℝ}
    (hf : ∀ᶠ x in 𝓝[≥] a, f x ≤ f a)
    (hderiv : DifferentiableAt ℝ f a) :
    deriv f a ≤ 0 := by
  have hder : HasDerivAt f (deriv f a) a := hderiv.hasDerivAt
  have ht : Tendsto (slope f a) (𝓝[≠] a) (𝓝 (deriv f a)) := hder.tendsto_slope
  have hsub_ne : Set.Ioi a ⊆ {x : ℝ | x ≠ a} := by
    intro x hx
    exact ne_of_gt (Set.mem_Ioi.mp hx)
  have hright : Tendsto (slope f a) (𝓝[>] a) (𝓝 (deriv f a)) := by
    exact ht.mono_left (nhdsWithin_mono a hsub_ne)
  have hsub_le : Set.Ioi a ⊆ Set.Ici a := by
    intro x hx
    exact le_of_lt (Set.mem_Ioi.mp hx)
  have hf_right : ∀ᶠ x in 𝓝[>] a, f x ≤ f a := by
    exact (Filter.le_def.mp (nhdsWithin_mono a hsub_le)) {x : ℝ | f x ≤ f a} hf
  have hgt_filter : ∀ᶠ x in 𝓝[>] a, a < x := self_mem_nhdsWithin
  have hnonpos : ∀ᶠ x in 𝓝[>] a, slope f a x ≤ 0 := by
    filter_upwards [hf_right, hgt_filter] with x hx hgt
    unfold slope
    have hnum : f x - f a ≤ 0 := sub_nonpos.mpr hx
    have hden : 0 < x - a := sub_pos.mpr hgt
    have hinv : 0 ≤ (x - a)⁻¹ := inv_nonneg.mpr hden.le
    have hprod : (f x - f a) * (x - a)⁻¹ ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hnum hinv
    simpa [smul_eq_mul, mul_comm] using hprod
  exact le_of_tendsto hright hnonpos

theorem deriv_nonneg_at_right_endpoint_of_isMaxOn_Icc
    {f : ℝ → ℝ} {a d : ℝ} (ha : 0 < a)
    (hmax : IsMaxOn f (Set.Icc 0 a) a)
    (hderiv : HasDerivAt f d a) :
    0 ≤ d := by
  have hdir : -(a / 2) ∈ posTangentConeAt (Set.Icc 0 a) a := by
    apply mem_posTangentConeAt_of_segment_subset
    rw [show a + -(a / 2) = a / 2 by ring, segment_symm,
      segment_eq_Icc (by linarith : a / 2 ≤ a)]
    intro s hs
    exact ⟨by linarith [hs.1], hs.2⟩
  have hnonpos := hmax.localize.hasFDerivWithinAt_nonpos
    hderiv.hasFDerivAt.hasFDerivWithinAt hdir
  have heval : (ContinuousLinearMap.toSpanSingleton ℝ d) (-(a / 2)) =
      -(a / 2) * d := by
    simp [ContinuousLinearMap.toSpanSingleton_apply, mul_comm]
  rw [heval] at hnonpos
  nlinarith

end DifferentialGeometry.Analysis.Calculus

end
