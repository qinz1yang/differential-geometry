import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Const

/-!
# EDP01 kernel: the adjusted scale varies slowly

Frozen blueprint master207B, lemma `lem:fibration-actual-adjusted-scale-derivative` (EDP01, lines
6666–6746). The actual adjusted scale is the blend `s = (1 - χ) ρ + χ z` of the slowly varying scale
`ρ` (LC02) with the scale component `z = (P₁F)_ρ` of the projected first-cloud map, cut off by
`χ = ψ₁ ∘ F`. The proof has three analytic steps, proved here for functions on a real normed space
(a chart at the point, normed by `g_p`, is an instance):

* (SW) a weighted mean `μ = ∑ w_y a_y` of values `a_y` within `δ` of one constant `R`, with weights
  summing to one near the point, has `‖Dμ‖ ≤ N c δ` (`weightedMean_hasFDerivAt_norm_le`), because
  `∑ Dw_y = 0`; its value is within `δ` of `R` when the weights are nonnegative
  (`abs_weightedMean_sub_le`);
* (SD) the product rule for the blend (`adjustedScale_hasFDerivAt`) and the pointwise bounds
  `|s - ρ| ≤ K₁Λρ`, `‖Ds‖ ≤ (1 + K₂ + K₁K₃)Λ` (`adjustedScale_bounds`);
* the global statement, with hypotheses on `z, χ` only on the closed support of `χ`, since `s = ρ`
  near every point outside it (`adjustedScale_slow`), and positivity (`adjustedScale_pos`).

`adjustedScale_constant_le` checks that the blueprint's constant
`C_ρ = 100 (L₀ + 1)(1 + b_cut + N_b c_w / Σ₁)` (here `S = Σ₁`) dominates `1 + K₂ + K₁K₃` and `K₁` for
`K₁ = 80/3`, `K₂ = 80 N_b c_w L₀ / (3 S)`, `K₃ = b_cut L₀`.

The binding to the actual `χ, z` (CFS12, CFS31, GAF01, GAF04) is not available in the tree.
-/

set_option autoImplicit false

noncomputable section

open Set Filter
open scoped Topology

namespace DifferentialGeometry.Geometry.Collapse.EdgeDisk

/-- (SW), linear algebra: if `∑ d_y = 0` then `∑ a_y d_y = ∑ (a_y - R) d_y`, so it is bounded by
`N δ c`. -/
theorem norm_sum_smul_le_of_sum_eq_zero {ι V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (s : Finset ι) (a : ι → ℝ) (d : ι → V) {R δ c : ℝ} (hsum : ∑ y ∈ s, d y = 0)
    (ha : ∀ y ∈ s, |a y - R| ≤ δ) (hd : ∀ y ∈ s, ‖d y‖ ≤ c) :
    ‖∑ y ∈ s, a y • d y‖ ≤ s.card * (δ * c) := by
  have hrw : ∑ y ∈ s, a y • d y = ∑ y ∈ s, (a y - R) • d y := by
    have : ∑ y ∈ s, (a y - R) • d y = ∑ y ∈ s, a y • d y - R • ∑ y ∈ s, d y := by
      rw [Finset.smul_sum, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun y _ => sub_smul _ _ _
    rw [this, hsum, smul_zero, sub_zero]
  rw [hrw]
  calc ‖∑ y ∈ s, (a y - R) • d y‖ ≤ ∑ y ∈ s, ‖(a y - R) • d y‖ := norm_sum_le _ _
    _ ≤ ∑ _y ∈ s, δ * c := by
        apply Finset.sum_le_sum
        intro y hy
        rw [norm_smul, Real.norm_eq_abs]
        exact mul_le_mul (ha y hy) (hd y hy) (norm_nonneg _) ((abs_nonneg _).trans (ha y hy))
    _ = s.card * (δ * c) := by rw [Finset.sum_const, nsmul_eq_mul]

/-- (SW): the weighted mean of values within `δ` of `R`, for weights summing to one near `x`, has
derivative `∑ a_y Dw_y` of norm at most `N δ c`, where `c` bounds every `‖Dw_y‖`. -/
theorem weightedMean_hasFDerivAt_norm_le {ι E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (s : Finset ι) (w : ι → E → ℝ) (w' : ι → E →L[ℝ] ℝ) (a : ι → ℝ) {x : E} {R δ c : ℝ}
    (hw : ∀ y ∈ s, HasFDerivAt (w y) (w' y) x)
    (hpart : ∀ᶠ z in 𝓝 x, ∑ y ∈ s, w y z = 1)
    (ha : ∀ y ∈ s, |a y - R| ≤ δ) (hw' : ∀ y ∈ s, ‖w' y‖ ≤ c) :
    HasFDerivAt (fun z => ∑ y ∈ s, w y z * a y) (∑ y ∈ s, a y • w' y) x ∧
      ‖∑ y ∈ s, a y • w' y‖ ≤ s.card * (δ * c) := by
  refine ⟨HasFDerivAt.fun_sum fun y hy => (hw y hy).mul_const (a y), ?_⟩
  have hsum : HasFDerivAt (fun z => ∑ y ∈ s, w y z) (∑ y ∈ s, w' y) x :=
    HasFDerivAt.fun_sum fun y hy => hw y hy
  have hconst : HasFDerivAt (fun z => ∑ y ∈ s, w y z) (0 : E →L[ℝ] ℝ) x :=
    (hasFDerivAt_const (1 : ℝ) x).congr_of_eventuallyEq hpart
  exact norm_sum_smul_le_of_sum_eq_zero s a w' (hsum.unique hconst) ha hw'

/-- (SC)/(SM): a convex combination of values within `δ` of `R` is within `δ` of `R`. -/
theorem abs_weightedMean_sub_le {ι : Type*} (s : Finset ι) (w a : ι → ℝ) {R δ : ℝ}
    (hw0 : ∀ y ∈ s, 0 ≤ w y) (hw1 : ∑ y ∈ s, w y = 1) (ha : ∀ y ∈ s, |a y - R| ≤ δ) :
    |∑ y ∈ s, w y * a y - R| ≤ δ := by
  have hrw : ∑ y ∈ s, w y * a y - R = ∑ y ∈ s, w y * (a y - R) := by
    have : ∑ y ∈ s, w y * (a y - R) = ∑ y ∈ s, w y * a y - (∑ y ∈ s, w y) * R := by
      rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun y _ => mul_sub _ _ _
    rw [this, hw1, one_mul]
  rw [hrw]
  calc |∑ y ∈ s, w y * (a y - R)| ≤ ∑ y ∈ s, |w y * (a y - R)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ y ∈ s, w y * δ := by
        apply Finset.sum_le_sum
        intro y hy
        rw [abs_mul, abs_of_nonneg (hw0 y hy)]
        exact mul_le_mul_of_nonneg_left (ha y hy) (hw0 y hy)
    _ = δ := by rw [← Finset.sum_mul, hw1, one_mul]

section Blend

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The product rule for the blend `s = (1 - χ) ρ + χ z`. -/
theorem adjustedScale_hasFDerivAt {ρ z χ : E → ℝ} {ρ' z' χ' : E →L[ℝ] ℝ} {x : E}
    (hρ : HasFDerivAt ρ ρ' x) (hz : HasFDerivAt z z' x) (hχ : HasFDerivAt χ χ' x) :
    HasFDerivAt (fun y => (1 - χ y) * ρ y + χ y * z y)
      ((1 - χ x) • ρ' + χ x • z' + (z x - ρ x) • χ') x := by
  have h1 : HasFDerivAt (fun y => 1 - χ y) (-χ') x := hχ.const_sub 1
  have h := (h1.mul hρ).add (hχ.mul hz)
  convert h using 1
  ext v
  simp
  ring

/-- (SD), pointwise: the value and derivative bounds of the blend at one point, for abstract
derivative vectors in a normed space `V`. -/
theorem adjustedScale_bounds {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {ρ z χ Λ K₁ K₂ K₃ : ℝ} {ρ' z' χ' : V} (hρ : 0 < ρ) (hχ0 : 0 ≤ χ) (hχ1 : χ ≤ 1)
    (hz : |z - ρ| ≤ K₁ * Λ * ρ) (hρ' : ‖ρ'‖ ≤ Λ) (hz' : ‖z'‖ ≤ K₂ * Λ) (hχ' : ‖χ'‖ ≤ K₃ / ρ) :
    |(1 - χ) * ρ + χ * z - ρ| ≤ K₁ * Λ * ρ ∧
      ‖(1 - χ) • ρ' + χ • z' + (z - ρ) • χ'‖ ≤ (1 + K₂ + K₁ * K₃) * Λ := by
  have hΛ : 0 ≤ Λ := (norm_nonneg _).trans hρ'
  have hK₂Λ : 0 ≤ K₂ * Λ := (norm_nonneg _).trans hz'
  have hK₃ρ : 0 ≤ K₃ / ρ := (norm_nonneg _).trans hχ'
  refine ⟨?_, ?_⟩
  · have : (1 - χ) * ρ + χ * z - ρ = χ * (z - ρ) := by ring
    rw [this, abs_mul, abs_of_nonneg hχ0]
    calc χ * |z - ρ| ≤ 1 * |z - ρ| := mul_le_mul_of_nonneg_right hχ1 (abs_nonneg _)
      _ ≤ K₁ * Λ * ρ := by rw [one_mul]; exact hz
  · have hterm3 : |z - ρ| * ‖χ'‖ ≤ K₁ * K₃ * Λ := by
      calc |z - ρ| * ‖χ'‖ ≤ (K₁ * Λ * ρ) * (K₃ / ρ) :=
            mul_le_mul hz hχ' (norm_nonneg _) ((abs_nonneg _).trans hz)
        _ = K₁ * K₃ * Λ := by field_simp
    calc ‖(1 - χ) • ρ' + χ • z' + (z - ρ) • χ'‖
        ≤ ‖(1 - χ) • ρ'‖ + ‖χ • z'‖ + ‖(z - ρ) • χ'‖ := norm_add₃_le
      _ = (1 - χ) * ‖ρ'‖ + χ * ‖z'‖ + |z - ρ| * ‖χ'‖ := by
          rw [norm_smul, norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
            Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hχ1), abs_of_nonneg hχ0]
      _ ≤ (1 - χ) * Λ + χ * (K₂ * Λ) + K₁ * K₃ * Λ := by
          gcongr
      _ ≤ Λ + K₂ * Λ + K₁ * K₃ * Λ := by nlinarith
      _ = (1 + K₂ + K₁ * K₃) * Λ := by ring

/-- **EDP01 kernel (SD), global form.** Let `ρ > 0` be differentiable with `‖Dρ‖ ≤ Λ` and let
`0 ≤ χ ≤ 1`. Suppose that at every point of the closed support of `χ` the functions `z, χ` are
differentiable with `|z - ρ| ≤ K₁Λρ`, `‖Dz‖ ≤ K₂Λ` and `‖Dχ‖ ≤ K₃/ρ`. Then the blend
`s = (1 - χ)ρ + χ z` is differentiable everywhere, `|s - ρ| ≤ K₁Λρ` and `‖Ds‖ ≤ (1 + K₂ + K₁K₃)Λ`.
Outside the closed support `s = ρ` near the point, as in the blueprint. -/
theorem adjustedScale_slow {ρ z χ : E → ℝ} {Λ K₁ K₂ K₃ : ℝ} (hK₁ : 0 ≤ K₁)
    (hK : 0 ≤ K₂ + K₁ * K₃) (hρ : ∀ x, DifferentiableAt ℝ ρ x) (hρpos : ∀ x, 0 < ρ x)
    (hρ' : ∀ x, ‖fderiv ℝ ρ x‖ ≤ Λ) (hχ01 : ∀ x, 0 ≤ χ x ∧ χ x ≤ 1)
    (hsupp : ∀ x ∈ tsupport χ, DifferentiableAt ℝ z x ∧ DifferentiableAt ℝ χ x ∧
      |z x - ρ x| ≤ K₁ * Λ * ρ x ∧ ‖fderiv ℝ z x‖ ≤ K₂ * Λ ∧ ‖fderiv ℝ χ x‖ ≤ K₃ / ρ x) :
    ∀ x, DifferentiableAt ℝ (fun y => (1 - χ y) * ρ y + χ y * z y) x ∧
      |(1 - χ x) * ρ x + χ x * z x - ρ x| ≤ K₁ * Λ * ρ x ∧
      ‖fderiv ℝ (fun y => (1 - χ y) * ρ y + χ y * z y) x‖ ≤ (1 + K₂ + K₁ * K₃) * Λ := by
  intro x
  by_cases hx : x ∈ tsupport χ
  · obtain ⟨hzd, hχd, hzv, hz', hχ'⟩ := hsupp x hx
    have hd := adjustedScale_hasFDerivAt (hρ x).hasFDerivAt hzd.hasFDerivAt hχd.hasFDerivAt
    obtain ⟨hv, hn⟩ := adjustedScale_bounds (hρpos x) (hχ01 x).1 (hχ01 x).2 hzv (hρ' x) hz' hχ'
    exact ⟨hd.differentiableAt, hv, by rw [hd.fderiv]; exact hn⟩
  · have hev : χ =ᶠ[𝓝 x] fun _ => 0 := notMem_tsupport_iff_eventuallyEq.mp hx
    have hχx : χ x = 0 := hev.eq_of_nhds
    have hseq : (fun y => (1 - χ y) * ρ y + χ y * z y) =ᶠ[𝓝 x] ρ := by
      filter_upwards [hev] with y hy
      rw [hy]
      ring
    have hΛ : 0 ≤ Λ := (norm_nonneg _).trans (hρ' x)
    refine ⟨(hρ x).congr_of_eventuallyEq hseq, ?_, ?_⟩
    · rw [hχx]
      simp only [sub_zero, one_mul, zero_mul, add_zero, sub_self, abs_zero]
      exact mul_nonneg (mul_nonneg hK₁ hΛ) (hρpos x).le
    · rw [hseq.fderiv_eq]
      calc ‖fderiv ℝ ρ x‖ ≤ Λ := hρ' x
        _ ≤ (1 + K₂ + K₁ * K₃) * Λ := by nlinarith

end Blend

/-- Positivity of the adjusted scale: `|σ - ρ| ≤ CΛρ` with `CΛ < 1` forces `σ > 0`. -/
theorem adjustedScale_pos {σ ρ C Λ : ℝ} (hρ : 0 < ρ) (h : |σ - ρ| ≤ C * Λ * ρ)
    (hCΛ : C * Λ < 1) : 0 < σ := by
  have h1 := (abs_le.mp h).1
  nlinarith

/-- The blueprint constant `C_ρ = 100 (L₀ + 1)(1 + b_cut + N_b c_w / Σ₁)` (here `S = Σ₁`) dominates both
`K₁ = 80/3` and `1 + K₂ + K₁K₃` for `K₂ = 80 N_b c_w L₀ / (3 Σ₁)`, `K₃ = b_cut L₀`. -/
theorem adjustedScale_constant_le {L b N c S : ℝ} (hL : 0 ≤ L) (hb : 0 ≤ b) (hN : 0 ≤ N)
    (hc : 0 ≤ c) (hS : 0 < S) :
    80 / 3 ≤ 100 * (L + 1) * (1 + b + N * c / S) ∧
      1 + 80 * N * c * L / (3 * S) + 80 / 3 * (b * L) ≤
        100 * (L + 1) * (1 + b + N * c / S) := by
  have hq : 0 ≤ N * c / S := div_nonneg (mul_nonneg hN hc) hS.le
  have hrw : 80 * N * c * L / (3 * S) = 80 / 3 * L * (N * c / S) := by
    field_simp
  rw [hrw]
  constructor
  · nlinarith [mul_nonneg hL hb, mul_nonneg hL hq]
  · nlinarith [mul_nonneg hL hb, mul_nonneg hL hq]

end DifferentialGeometry.Geometry.Collapse.EdgeDisk
