import DifferentialGeometry.Analysis.Calculus.ScalarDerivativeBounds
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Topology.Algebra.Support
import Mathlib.Tactic.FieldSimp

set_option autoImplicit false

namespace DifferentialGeometry.Analysis

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

noncomputable def edgeCutoff (Δ : ℝ) (f g : ℝ → ℝ) (u v : E →L[ℝ] ℝ) (x : E) : ℝ :=
  f (Δ⁻¹ * u x) * g (Δ⁻¹ * v x)

noncomputable def jointEdgeCutoff {ι : Type*} [Fintype ι]
    (Δ : ℝ) (f g h χ : ℝ → ℝ) (u : ι → E →L[ℝ] ℝ) (v : E →L[ℝ] ℝ) (x : E) : ℝ :=
  h (Δ⁻¹ * v x) * χ (∑ i, edgeCutoff Δ f g (u i) v x)

theorem contDiff_edgeCutoff {f g : ℝ → ℝ} {n : WithTop ℕ∞}
    (hf : ContDiff ℝ n f) (hg : ContDiff ℝ n g) (Δ : ℝ) (u v : E →L[ℝ] ℝ) :
    ContDiff ℝ n (edgeCutoff Δ f g u v) :=
  (hf.comp (contDiff_const.mul u.contDiff)).mul (hg.comp (contDiff_const.mul v.contDiff))

theorem contDiff_jointEdgeCutoff {ι : Type*} [Fintype ι] {f g h χ : ℝ → ℝ}
    {n : WithTop ℕ∞} (hf : ContDiff ℝ n f) (hg : ContDiff ℝ n g)
    (hh : ContDiff ℝ n h) (hχ : ContDiff ℝ n χ)
    (Δ : ℝ) (u : ι → E →L[ℝ] ℝ) (v : E →L[ℝ] ℝ) :
    ContDiff ℝ n (jointEdgeCutoff Δ f g h χ u v) :=
  (hh.comp (contDiff_const.mul v.contDiff)).mul
    (hχ.comp (ContDiff.sum fun i _ => contDiff_edgeCutoff hf hg Δ (u i) v))

theorem edgeCutoff_mem_Icc {f g : ℝ → ℝ} (hf : ∀ x, f x ∈ Set.Icc 0 1)
    (hg : ∀ x, g x ∈ Set.Icc 0 1) (Δ : ℝ) (u v : E →L[ℝ] ℝ) (x : E) :
    edgeCutoff Δ f g u v x ∈ Set.Icc 0 1 := by
  exact ⟨mul_nonneg (hf _).1 (hg _).1,
    (mul_le_mul (hf _).2 (hg _).2 (hg _).1 (by norm_num)).trans_eq (one_mul _)⟩

theorem jointEdgeCutoff_mem_Icc {ι : Type*} [Fintype ι] {h χ : ℝ → ℝ}
    (hh : ∀ x, h x ∈ Set.Icc 0 1) (hχ : ∀ x, χ x ∈ Set.Icc 0 1)
    (Δ : ℝ) (f g : ℝ → ℝ) (u : ι → E →L[ℝ] ℝ) (v : E →L[ℝ] ℝ) (x : E) :
    jointEdgeCutoff Δ f g h χ u v x ∈ Set.Icc 0 1 := by
  exact ⟨mul_nonneg (hh _).1 (hχ _).1,
    (mul_le_mul (hh _).2 (hχ _).2 (hχ _).1 (by norm_num)).trans_eq (one_mul _)⟩

private theorem scaled_coordinate_bounds (u : E →L[ℝ] ℝ) (hu : ‖u‖ ≤ 1)
    {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) {Δ P : ℝ} (hΔ : 0 < Δ) (hP : 0 ≤ P)
    (hD : ∀ x, ‖fderiv ℝ f x‖ ≤ P) (hDD : ∀ x, ‖fderiv ℝ (fderiv ℝ f) x‖ ≤ P) (x : E) :
    ‖fderiv ℝ (fun y => f (Δ⁻¹ * u y)) x‖ ≤ P * Δ⁻¹ ∧
      ‖fderiv ℝ (fderiv ℝ (fun y => f (Δ⁻¹ * u y))) x‖ ≤ P * Δ⁻¹ ^ 2 := by
  let U : E →L[ℝ] ℝ := Δ⁻¹ • u
  have hU : ‖U‖ ≤ Δ⁻¹ := by
    rw [show U = Δ⁻¹ • u from rfl, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hΔ)]
    exact (mul_le_mul_of_nonneg_left hu (inv_nonneg.mpr hΔ.le)).trans_eq (mul_one _)
  exact linear_precomp_derivative_bounds U hf (inv_nonneg.mpr hΔ.le) hP hP hU hD hDD x

theorem edgeCutoff_derivative_bounds {f g : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (hg : ContDiff ℝ 2 g) {Δ P : ℝ} (hΔ : 0 < Δ) (hP : 1 ≤ P)
    (hfv : ∀ x, f x ∈ Set.Icc 0 1) (hgv : ∀ x, g x ∈ Set.Icc 0 1)
    (hDf : ∀ x, ‖fderiv ℝ f x‖ ≤ P) (hDg : ∀ x, ‖fderiv ℝ g x‖ ≤ P)
    (hDDf : ∀ x, ‖fderiv ℝ (fderiv ℝ f) x‖ ≤ P)
    (hDDg : ∀ x, ‖fderiv ℝ (fderiv ℝ g) x‖ ≤ P)
    (u v : E →L[ℝ] ℝ) (hu : ‖u‖ ≤ 1) (hv : ‖v‖ ≤ 1) (x : E) :
    ‖fderiv ℝ (edgeCutoff Δ f g u v) x‖ ≤ 2 * P * Δ⁻¹ ∧
      ‖fderiv ℝ (fderiv ℝ (edgeCutoff Δ f g u v)) x‖ ≤ 4 * P ^ 2 * Δ⁻¹ ^ 2 := by
  have hP0 : 0 ≤ P := by linarith
  have hfb := scaled_coordinate_bounds u hu hf hΔ hP0 hDf hDDf x
  have hgb := scaled_coordinate_bounds v hv hg hΔ hP0 hDg hDDg x
  have hh := unit_scalar_product_derivative_bounds
    (hf.comp (contDiff_const.mul u.contDiff)) (hg.comp (contDiff_const.mul v.contDiff))
    (x := x) (by dsimp only [Function.comp_apply]; rw [abs_of_nonneg (hfv _).1]; exact (hfv _).2)
    (by dsimp only [Function.comp_apply]; rw [abs_of_nonneg (hgv _).1]; exact (hgv _).2) hfb.1 hgb.1 hfb.2 hgb.2
  constructor
  · exact hh.1.trans_eq (by ring)
  · apply hh.2.trans
    have hsq : P ≤ P ^ 2 := by nlinarith
    have hp := mul_le_mul_of_nonneg_right hsq (sq_nonneg Δ⁻¹)
    nlinarith

theorem edgeCutoff_weight_bound {f g : ℝ → ℝ} {Δ : ℝ} (hΔ : 0 < Δ)
    (hf : tsupport f ⊆ Set.Icc (-9) 9) (u v : E →L[ℝ] ℝ) {x : E}
    (hx : x ∈ tsupport (edgeCutoff Δ f g u v)) : |u x| ≤ 9 * Δ := by
  have hs := tsupport_mul_subset_left hx
  have ht := hf (tsupport_comp_subset_preimage f (continuous_const.mul u.continuous) hs)
  have hh : |Δ⁻¹ * u x| ≤ 9 := abs_le.mpr ht
  rw [abs_mul, abs_of_pos (inv_pos.mpr hΔ)] at hh
  have hm := mul_le_mul_of_nonneg_left hh hΔ.le
  rwa [← mul_assoc, mul_inv_cancel₀ hΔ.ne', one_mul, mul_comm Δ] at hm

theorem jointEdgeCutoff_weight_bound {ι : Type*} [Fintype ι] {f g h χ : ℝ → ℝ}
    {Δ : ℝ} (hΔ : 0 < Δ) (hh : tsupport h ⊆ Set.Icc (1 / 5) 9)
    (u : ι → E →L[ℝ] ℝ) (v : E →L[ℝ] ℝ) {x : E}
    (hx : x ∈ tsupport (jointEdgeCutoff Δ f g h χ u v)) : |v x| ≤ 9 * Δ := by
  have hs := tsupport_mul_subset_left hx
  have ht := hh (tsupport_comp_subset_preimage h (continuous_const.mul v.continuous) hs)
  change 1 / 5 ≤ Δ⁻¹ * v x ∧ Δ⁻¹ * v x ≤ 9 at ht
  have hb : |Δ⁻¹ * v x| ≤ 9 := abs_le.mpr ⟨by linarith [ht.1], ht.2⟩
  rw [abs_mul, abs_of_pos (inv_pos.mpr hΔ)] at hb
  have hm := mul_le_mul_of_nonneg_left hb hΔ.le
  rwa [← mul_assoc, mul_inv_cancel₀ hΔ.ne', one_mul, mul_comm Δ] at hm

theorem jointEdgeCutoff_derivative_bounds {ι : Type*} [Fintype ι]
    {f g h χ : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g)
    (hh : ContDiff ℝ 2 h) (hχ : ContDiff ℝ 2 χ) {Δ P : ℝ} (hΔ : 0 < Δ) (hP : 1 ≤ P)
    (hfv : ∀ x, f x ∈ Set.Icc 0 1) (hgv : ∀ x, g x ∈ Set.Icc 0 1)
    (hhv : ∀ x, h x ∈ Set.Icc 0 1) (hχv : ∀ x, χ x ∈ Set.Icc 0 1)
    (hDf : ∀ x, ‖fderiv ℝ f x‖ ≤ P) (hDg : ∀ x, ‖fderiv ℝ g x‖ ≤ P)
    (hDh : ∀ x, ‖fderiv ℝ h x‖ ≤ P) (hDχ : ∀ x, ‖fderiv ℝ χ x‖ ≤ P)
    (hDDf : ∀ x, ‖fderiv ℝ (fderiv ℝ f) x‖ ≤ P)
    (hDDg : ∀ x, ‖fderiv ℝ (fderiv ℝ g) x‖ ≤ P)
    (hDDh : ∀ x, ‖fderiv ℝ (fderiv ℝ h) x‖ ≤ P)
    (hDDχ : ∀ x, ‖fderiv ℝ (fderiv ℝ χ) x‖ ≤ P)
    (u : ι → E →L[ℝ] ℝ) (v : E →L[ℝ] ℝ)
    (hu : ∀ i, ‖u i‖ ≤ 1) (hv : ‖v‖ ≤ 1) (x : E) :
    let n : ℝ := Fintype.card ι
    ‖fderiv ℝ (jointEdgeCutoff Δ f g h χ u v) x‖ ≤ (1 + 2 * n) * P ^ 2 * Δ⁻¹ ∧
      ‖fderiv ℝ (fderiv ℝ (jointEdgeCutoff Δ f g h χ u v)) x‖ ≤
        (1 + 8 * n + 4 * n ^ 2) * P ^ 3 * Δ⁻¹ ^ 2 := by
  let n : ℝ := Fintype.card ι
  have hn : 0 ≤ n := Nat.cast_nonneg _
  have hP0 : 0 ≤ P := by linarith
  have ht : 0 ≤ Δ⁻¹ := inv_nonneg.mpr hΔ.le
  let z (i : ι) := edgeCutoff Δ f g (u i) v
  let Z : E → ℝ := fun y => ∑ i, z i y
  have hz (i : ι) : ContDiff ℝ 2 (z i) := contDiff_edgeCutoff hf hg Δ (u i) v
  have hZ : ContDiff ℝ 2 Z := ContDiff.sum fun i _ => hz i
  have hzb (i : ι) (y : E) := edgeCutoff_derivative_bounds hf hg hΔ hP hfv hgv
    hDf hDg hDDf hDDg (u i) v (hu i) hv y
  have hZb := finite_sum_derivative_bounds hz
    (fun i y => (hzb i y).1) (fun i y => (hzb i y).2) x
  have hZ1 : ‖fderiv ℝ Z x‖ ≤ n * (2 * P * Δ⁻¹) := hZb.1
  have hZ2 : ‖fderiv ℝ (fderiv ℝ Z) x‖ ≤ n * (4 * P ^ 2 * Δ⁻¹ ^ 2) := hZb.2
  have hχd := hχ.differentiable (by norm_num)
  have hZd := hZ.differentiable (by norm_num)
  have hDχd : Differentiable ℝ (fderiv ℝ χ) := hχ.fderiv_right (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2) |>.differentiable (by norm_num)
  have hDZd : Differentiable ℝ (fderiv ℝ Z) := hZ.fderiv_right (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2) |>.differentiable (by norm_num)
  have hχZ1 : ‖fderiv ℝ (χ ∘ Z) x‖ ≤ 2 * n * P ^ 2 * Δ⁻¹ := by
    rw [fderiv_comp x (hχd (Z x)) (hZd x)]
    apply (ContinuousLinearMap.opNorm_comp_le _ _).trans
    calc
      _ ≤ P * (n * (2 * P * Δ⁻¹)) := by gcongr; exact hDχ _
      _ = _ := by ring
  have hχZ2 : ‖fderiv ℝ (fderiv ℝ (χ ∘ Z)) x‖ ≤ 4 * (n ^ 2 + n) * P ^ 3 * Δ⁻¹ ^ 2 := by
    apply (norm_second_fderiv_comp_le hχd hZd (hDχd (Z x)) (hDZd x)).trans
    calc
      _ ≤ P * (n * (2 * P * Δ⁻¹)) ^ 2 + P * (n * (4 * P ^ 2 * Δ⁻¹ ^ 2)) := by
        gcongr
        · exact hDDχ _
        · exact hDχ _
      _ = _ := by ring
  have hhbound := scaled_coordinate_bounds v hv hh hΔ hP0 hDh hDDh x
  have hprod := unit_scalar_product_derivative_bounds
    (hh.comp (contDiff_const.mul v.contDiff)) (hχ.comp hZ)
    (x := x) (by dsimp only [Function.comp_apply]; rw [abs_of_nonneg (hhv _).1]; exact (hhv _).2)
    (by dsimp only [Function.comp_apply]; rw [abs_of_nonneg (hχv _).1]; exact (hχv _).2)
    hhbound.1 hχZ1 hhbound.2 hχZ2
  have hP2 : P ≤ P ^ 2 := by nlinarith
  have hP3 : P ≤ P ^ 3 := by
    have hp := mul_le_mul_of_nonneg_left hP2 hP0
    nlinarith
  dsimp only
  constructor
  · apply hprod.1.trans
    have hp := mul_le_mul_of_nonneg_right hP2 ht
    nlinarith
  · apply hprod.2.trans
    have hp := mul_le_mul_of_nonneg_right hP3 (sq_nonneg Δ⁻¹)
    nlinarith

theorem jointEdgeCutoff_eq_zero_of_all_edgeCutoff_zero {ι : Type*} [Fintype ι]
    {Δ : ℝ} {f g h χ : ℝ → ℝ} (hχ : χ 0 = 0)
    (u : ι → E →L[ℝ] ℝ) (v : E →L[ℝ] ℝ) {x : E}
    (hx : ∀ i, edgeCutoff Δ f g (u i) v x = 0) : jointEdgeCutoff Δ f g h χ u v x = 0 := by
  simp only [jointEdgeCutoff, hx, Finset.sum_const_zero, hχ, mul_zero]

theorem joint_cutoff_common_constant {n P : ℝ} (hn : 0 ≤ n) (hP : 1 ≤ P) :
    let K := 10 * (n + 1) ^ 2 * P ^ 3
    2 * P ≤ K ∧ 4 * P ^ 2 ≤ K ∧ (1 + 2 * n) * P ^ 2 ≤ K ∧
      (1 + 8 * n + 4 * n ^ 2) * P ^ 3 ≤ K := by
  have hP0 : 0 ≤ P := by linarith
  have hP2 : P ≤ P ^ 2 := by nlinarith
  have hP23 : P ^ 2 ≤ P ^ 3 := by nlinarith [mul_le_mul_of_nonneg_left hP2 hP0]
  have hP3 : P ≤ P ^ 3 := hP2.trans hP23
  have h1 : 2 ≤ 10 * (n + 1) ^ 2 := by nlinarith [sq_nonneg n]
  have h2 : 4 ≤ 10 * (n + 1) ^ 2 := by nlinarith [sq_nonneg n]
  have h3 : 1 + 2 * n ≤ 10 * (n + 1) ^ 2 := by nlinarith [sq_nonneg n]
  have h4 : 1 + 8 * n + 4 * n ^ 2 ≤ 10 * (n + 1) ^ 2 := by nlinarith [sq_nonneg n]
  exact ⟨(mul_le_mul_of_nonneg_left hP3 (by norm_num)).trans
      (mul_le_mul_of_nonneg_right h1 (pow_nonneg hP0 _)),
    (mul_le_mul_of_nonneg_left hP23 (by norm_num)).trans
      (mul_le_mul_of_nonneg_right h2 (pow_nonneg hP0 _)),
    (mul_le_mul_of_nonneg_left hP23 (by positivity)).trans
      (mul_le_mul_of_nonneg_right h3 (pow_nonneg hP0 _)),
    mul_le_mul_of_nonneg_right h4 (pow_nonneg hP0 _)⟩

end DifferentialGeometry.Analysis
