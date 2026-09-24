import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

noncomputable section

open Filter MeasureTheory Set
open scoped ENNReal NNReal Topology

namespace MeasureTheory

private theorem norm_top_le_of_ae_bound {X : Type*} [MeasurableSpace X] {μ : Measure X}
    (f : Lp ℝ ∞ μ) {C : ℝ} (hC : 0 ≤ C) (hf : ∀ᵐ x ∂μ, ‖f x‖ ≤ C) : ‖f‖ ≤ C := by
  rw [Lp.norm_def, eLpNorm_exponent_top]
  exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top
    (eLpNormEssSup_le_of_ae_bound hf)).trans_eq (ENNReal.toReal_ofReal hC)

private theorem abs_inv_sub_one_le {c x A : ℝ} (hc : 0 < c) (hx : c ≤ x)
    (hA : |x - 1| ≤ A) : |x⁻¹ - 1| ≤ A / c := by
  have hx0 : 0 < x := hc.trans_le hx
  have he : x⁻¹ - 1 = (1 - x) / x := by field_simp
  rw [he, abs_div, abs_of_pos hx0, abs_sub_comm]
  exact (div_le_div_of_nonneg_left (abs_nonneg _) hc hx).trans
    ((div_le_div_iff_of_pos_right hc).mpr hA)

private theorem abs_inv_sub_inv_le {c x y A : ℝ} (hc : 0 < c) (hx : c ≤ x) (hy : c ≤ y)
    (hA : |x - y| ≤ A) : |x⁻¹ - y⁻¹| ≤ A / c ^ 2 := by
  have hx0 : 0 < x := hc.trans_le hx
  have hy0 : 0 < y := hc.trans_le hy
  rw [inv_sub_inv hx0.ne' hy0.ne', abs_div, abs_mul, abs_of_pos hx0, abs_of_pos hy0,
    abs_sub_comm]
  have hcc : c ^ 2 ≤ x * y := by
    simpa only [pow_two] using mul_le_mul hx hy hc.le hx0.le
  exact (div_le_div_of_nonneg_left (abs_nonneg _) (sq_pos_of_pos hc) hcc).trans
    ((div_le_div_iff_of_pos_right (sq_pos_of_pos hc)).mpr hA)

theorem exists_lp_top_reciprocal_sub_one_of_ae_lipschitz
    {X : Type*} [MeasurableSpace X] {μ : Measure X} {T c : ℝ}
    (hT : 0 ≤ T) (hc : 0 < c) (B : ℝ≥0) (v : ℝ → X → ℝ)
    (hm : ∀ t ∈ Icc (0 : ℝ) T, AEStronglyMeasurable (v t) μ)
    (hv : ∀ t ∈ Icc (0 : ℝ) T, ∀ᵐ x ∂μ, c ≤ v t x)
    (h0 : ∀ᵐ x ∂μ, v 0 x = 1)
    (hLip : ∀ s ∈ Icc (0 : ℝ) T, ∀ t ∈ Icc (0 : ℝ) T,
      ∀ᵐ x ∂μ, |v s x - v t x| ≤ (B : ℝ) * |s - t|) :
    ∃ a : ℝ → Lp ℝ ∞ μ,
      ContinuousOn a (Icc (0 : ℝ) T) ∧
      (∀ t ∈ Icc (0 : ℝ) T, a t =ᵐ[μ] fun x => (v t x)⁻¹ - 1) ∧
      (∀ t ∈ Icc (0 : ℝ) T, ‖a t‖ ≤ (B : ℝ) * T / c) := by
  have hbound (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) :
      ∀ᵐ x ∂μ, |(v t x)⁻¹ - 1| ≤ (B : ℝ) * T / c := by
    filter_upwards [hv t ht, h0, hLip t ht 0 ⟨le_rfl, hT⟩] with x hx hx0 hxt
    rw [hx0, sub_zero, abs_of_nonneg ht.1] at hxt
    exact abs_inv_sub_one_le hc hx (hxt.trans (mul_le_mul_of_nonneg_left ht.2 B.coe_nonneg))
  have hmem (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) : MemLp (fun x => (v t x)⁻¹ - 1) ∞ μ := by
    apply memLp_top_of_bound ((hm t ht).aemeasurable.inv.sub_const 1).aestronglyMeasurable
      ((B : ℝ) * T / c)
    simpa only [Real.norm_eq_abs, Pi.inv_apply] using hbound t ht
  let a : ℝ → Lp ℝ ∞ μ := fun t =>
    if ht : t ∈ Icc (0 : ℝ) T then (hmem t ht).toLp (fun x => (v t x)⁻¹ - 1) else 0
  have ha (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) :
      a t =ᵐ[μ] fun x => (v t x)⁻¹ - 1 := by
    simpa only [a, dif_pos ht] using (hmem t ht).coeFn_toLp
  have hnorm (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) : ‖a t‖ ≤ (B : ℝ) * T / c := by
    apply norm_top_le_of_ae_bound _ (div_nonneg (mul_nonneg B.coe_nonneg hT) hc.le)
    filter_upwards [ha t ht, hbound t ht] with x hx hbx
    simpa only [hx, Real.norm_eq_abs] using hbx
  have hla : LipschitzOnWith ⟨(B : ℝ) / c ^ 2, div_nonneg B.coe_nonneg (sq_nonneg c)⟩
      a (Icc (0 : ℝ) T) := by
    apply LipschitzOnWith.of_dist_le_mul
    intro s hs t ht
    rw [dist_eq_norm]
    apply norm_top_le_of_ae_bound _ (mul_nonneg (div_nonneg B.coe_nonneg (sq_nonneg c))
      (dist_nonneg))
    filter_upwards [Lp.coeFn_sub (a s) (a t), ha s hs, ha t ht, hv s hs, hv t ht,
      hLip s hs t ht] with x hx hsx htx hvx hvy hxy
    simp only [hx, Pi.sub_apply, hsx, htx, Real.norm_eq_abs]
    rw [sub_sub_sub_cancel_right]
    simpa only [Real.dist_eq, mul_div_assoc, div_mul_eq_mul_div] using
      abs_inv_sub_inv_le hc hvx hvy hxy
  exact ⟨a, hla.continuousOn, ha, hnorm⟩

end MeasureTheory
