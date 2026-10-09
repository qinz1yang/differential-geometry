import DifferentialGeometry.Analysis.Calculus.CutoffAdjustment
import Mathlib.Analysis.Calculus.MeanValue
import DifferentialGeometry.Analysis.ParameterSelection.AdjustmentBudget
import DifferentialGeometry.Analysis.InnerProductSpace.NormalSpectralSection
import DifferentialGeometry.Analysis.NormedSpace.ScaleVanishing

/-! Actual adjustment budgets and coordinate locality, preserving the original cloud data. -/

set_option autoImplicit false
noncomputable section

open Set Metric
open scoped BigOperators

namespace DifferentialGeometry.Analysis

variable {E H F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup H] [NormedSpace ℝ H] [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem perturbed_nearest_displacement
    (P : F → F) (A : F →L[ℝ] F) (hA : ‖ContinuousLinearMap.id ℝ F - A‖ ≤ 1)
    (x y : F) {r ε : ℝ} (hr : 0 < r) (hy : y ∈ ball x r)
    (hP : ∀ z ∈ ball x r, DifferentiableAt ℝ P z)
    (hderiv : ∀ z ∈ ball x r, ‖fderiv ℝ P z - A‖ ≤ ε)
    (hcenter : ‖P x - x‖ ≤ ε * r) :
    ‖P y - y‖ ≤ ε * r + (1 + ε) * ‖y - x‖ := by
  let v : F → F := fun z => P z - z
  have hv (z : F) (hz : z ∈ ball x r) : DifferentiableAt ℝ v z :=
    (hP z hz).sub differentiableAt_id
  have hbound (z : F) (hz : z ∈ ball x r) : ‖fderiv ℝ v z‖ ≤ 1 + ε := by
    rw [show v = fun z => P z - id z from rfl,
      fderiv_fun_sub (hP z hz) differentiableAt_id, fderiv_id]
    have heq : fderiv ℝ P z - ContinuousLinearMap.id ℝ F =
        (fderiv ℝ P z - A) - (ContinuousLinearMap.id ℝ F - A) := by abel
    rw [heq]
    exact (norm_sub_le _ _).trans (by linarith [hderiv z hz])
  have hh := Convex.norm_image_sub_le_of_norm_fderiv_le hv hbound
    (convex_ball x r) (mem_ball_self hr) hy
  have ht := norm_sub_le (v y - v x) (-v x)
  simp only [sub_neg_eq_add, sub_add_cancel, norm_neg] at ht
  change ‖P y - y‖ ≤ _
  change ‖v y‖ ≤ _
  linarith

theorem projected_adjustment_lt_of_threshold
    {f f₀ : E → H} {ψ : H → ℝ} {P : F → F} {x : E}
    (Q : H →L[ℝ] F) (J : F →L[ℝ] H) (A : F →L[ℝ] F)
    (hQ : ‖Q‖ ≤ 1) (hJ : ‖J‖ ≤ 1) (hA : ‖ContinuousLinearMap.id ℝ F - A‖ ≤ 1)
    (hf : DifferentiableAt ℝ f x) (hψ : DifferentiableAt ℝ ψ (f x))
    (hP : DifferentiableAt ℝ P (Q (f x))) {c μ b L ε σ ρ E₀ H₀ ν : ℝ}
    (hc : 0 < c) (hc1 : c ≤ 1) (hμ : 0 < μ) (hb : 0 ≤ b) (hL : 0 ≤ L)
    (hε : 0 ≤ ε) (hE : 0 ≤ E₀) (hH : 0 ≤ H₀) (hρ : 0 < ρ)
    (hεsmall : ε ≤ 1 / 10) (hσ : σ ≤ 1 / 2) (hν : ν ≤ c / 16)
    (hεα : ε ≤ min (c / (16 * (1 + b) * (1 + L))) (μ / (8 * (1 + L))))
    (hEα : E₀ ≤ min (c / (16 * (1 + b) * (1 + L))) (μ / (8 * (1 + L))))
    (hHα : H₀ ≤ min (c / (16 * (1 + b) * (1 + L))) (μ / (8 * (1 + L))))
    (hcutoff : 0 ≤ ψ (f x) ∧ ψ (f x) ≤ 1)
    (hvalue : ‖P (Q (f x)) - Q (f x)‖ ≤
      ((5 / 3 : ℝ) * ε * σ + (1 + ε) * E₀) * ρ)
    (hcutoffDeriv : ‖fderiv ℝ ψ (f x)‖ ≤ b / ρ)
    (hfirst : ‖fderiv ℝ f₀ x‖ ≤ L)
    (hcomparison : ‖fderiv ℝ P (Q (f x)) - A‖ ≤ ε)
    (hnormal : ‖(ContinuousLinearMap.id ℝ F - A).comp (Q.comp (fderiv ℝ f₀ x))‖ ≤ ν)
    (hpriorValue : ‖f x - f₀ x‖ ≤ E₀ * ρ)
    (hpriorDeriv : ‖fderiv ℝ f x - fderiv ℝ f₀ x‖ ≤ H₀) :
    let g : E → H := fun y => f y + ψ (f y) • J (P (Q (f y)) - Q (f y))
    ‖g x - f₀ x‖ < c * ρ ∧ ‖fderiv ℝ g x - fderiv ℝ f₀ x‖ < c ∧
      ‖(fderiv ℝ P (Q (f x))).comp (Q.comp (fderiv ℝ f x)) -
        A.comp (Q.comp (fderiv ℝ f₀ x))‖ < μ := by
  have hbudget := adjustment_errors_lt_of_threshold hc hc1 hμ hb hL hε hE hH
    hεsmall hσ hν hεα hEα hHα
  have hactual := projected_cutoff_adjustment_cumulative_le Q J A hQ hJ hA hf hψ hP
    hb hL hε hH hρ hcutoff hvalue hcutoffDeriv hfirst hcomparison hnormal
    hpriorValue hpriorDeriv
  have hDf : ‖fderiv ℝ f x‖ ≤ L + H₀ := by
    have ht := norm_sub_le (fderiv ℝ f x - fderiv ℝ f₀ x) (-(fderiv ℝ f₀ x))
    simp only [sub_neg_eq_add, sub_add_cancel, norm_neg] at ht
    linarith
  have hsplit :
      (fderiv ℝ P (Q (f x))).comp (Q.comp (fderiv ℝ f x)) -
        A.comp (Q.comp (fderiv ℝ f₀ x)) =
      (fderiv ℝ P (Q (f x)) - A).comp (Q.comp (fderiv ℝ f x)) +
        A.comp (Q.comp (fderiv ℝ f x - fderiv ℝ f₀ x)) := by
    ext v
    simp only [ContinuousLinearMap.comp_apply, map_sub, sub_apply, add_apply]
    abel
  have hAnorm : ‖A‖ ≤ 2 := by
    have ht := norm_sub_le (ContinuousLinearMap.id ℝ F)
      (ContinuousLinearMap.id ℝ F - A)
    rw [sub_sub_cancel] at ht
    have hi : ‖ContinuousLinearMap.id ℝ F‖ ≤ 1 := ContinuousLinearMap.norm_id_le
    linarith
  dsimp only at hactual hbudget ⊢
  refine ⟨hactual.1.trans_lt (mul_lt_mul_of_pos_right hbudget.1 hρ),
    hactual.2.trans_lt hbudget.2.1, ?_⟩
  rw [hsplit]
  apply (norm_add_le _ _).trans_lt
  have hU : ‖Q.comp (fderiv ℝ f x)‖ ≤ L + H₀ :=
    (ContinuousLinearMap.opNorm_comp_le _ _).trans
      ((mul_le_mul hQ hDf (norm_nonneg _) (by norm_num)).trans_eq (one_mul _))
  have hV : ‖Q.comp (fderiv ℝ f x - fderiv ℝ f₀ x)‖ ≤ H₀ :=
    (ContinuousLinearMap.opNorm_comp_le _ _).trans
      ((mul_le_mul hQ hpriorDeriv (norm_nonneg _) (by norm_num)).trans_eq (one_mul _))
  have hfirstTerm : ‖(fderiv ℝ P (Q (f x)) - A).comp
      (Q.comp (fderiv ℝ f x))‖ ≤ ε * (L + H₀) :=
    (ContinuousLinearMap.opNorm_comp_le _ _).trans
      (mul_le_mul hcomparison hU (norm_nonneg _) hε)
  have hsecondTerm : ‖A.comp (Q.comp (fderiv ℝ f x - fderiv ℝ f₀ x))‖ ≤ 2 * H₀ :=
    (ContinuousLinearMap.opNorm_comp_le _ _).trans
      (mul_le_mul hAnorm hV (norm_nonneg _) (by norm_num))
  have hstrong := adjustment_threshold_pos_and_bounds hc hμ hb hL
  have hrank : ε * (L + H₀) + 2 * H₀ < μ := by
    let α := min (c / (16 * (1 + b) * (1 + L))) (μ / (8 * (1 + L)))
    have hH1 : H₀ ≤ 1 := by
      have ht := hstrong.2.1
      have hα : 0 ≤ α := hstrong.1.le
      have hαb := mul_nonneg hα hb
      have hαL := mul_nonneg hα hL
      have hαbL := mul_nonneg hαb hL
      change 16 * α * (1 + b) * (1 + L) ≤ c at ht
      change H₀ ≤ α at hHα
      nlinarith
    have hm := mul_le_mul_of_nonneg_right hεα (add_nonneg hL hH)
    have hαL := mul_nonneg hstrong.1.le hL
    have hαH := mul_le_mul_of_nonneg_left hH1 hstrong.1.le
    nlinarith [hstrong.2.2]
  exact (add_le_add hfirstTerm hsecondTerm).trans_lt hrank

theorem projected_adjustment_lt_of_original_cloud
    {f f₀ : E → H} {ψ : H → ℝ} {P : F → F} {x : E}
    (Q : H →L[ℝ] F) (J : F →L[ℝ] H) (A : F →L[ℝ] F)
    (hQ : ‖Q‖ ≤ 1) (hJ : ‖J‖ ≤ 1) (hA : ‖ContinuousLinearMap.id ℝ F - A‖ ≤ 1)
    (hf : DifferentiableAt ℝ f x) (hψ : DifferentiableAt ℝ ψ (f x))
    {c μ b L ε σ ρ E₀ H₀ ν r : ℝ}
    (hr : 0 < r) (hy : Q (f x) ∈ ball (Q (f₀ x)) r)
    (hP : ∀ z ∈ ball (Q (f₀ x)) r, DifferentiableAt ℝ P z)
    (hc : 0 < c) (hc1 : c ≤ 1) (hμ : 0 < μ) (hb : 0 ≤ b) (hL : 0 ≤ L)
    (hε : 0 ≤ ε) (hE : 0 ≤ E₀) (hH : 0 ≤ H₀) (hρ : 0 < ρ)
    (hεsmall : ε ≤ 1 / 10) (hσ : σ ≤ 1 / 2) (hν : ν ≤ c / 16)
    (hεα : ε ≤ min (c / (16 * (1 + b) * (1 + L))) (μ / (8 * (1 + L))))
    (hEα : E₀ ≤ min (c / (16 * (1 + b) * (1 + L))) (μ / (8 * (1 + L))))
    (hHα : H₀ ≤ min (c / (16 * (1 + b) * (1 + L))) (μ / (8 * (1 + L))))
    (hcutoff : 0 ≤ ψ (f x) ∧ ψ (f x) ≤ 1)
    (hradius : r ≤ (5 / 3 : ℝ) * σ * ρ)
    (hcenter : ‖P (Q (f₀ x)) - Q (f₀ x)‖ ≤ ε * r)
    (hcutoffDeriv : ‖fderiv ℝ ψ (f x)‖ ≤ b / ρ)
    (hfirst : ‖fderiv ℝ f₀ x‖ ≤ L)
    (hcomparison : ∀ z ∈ ball (Q (f₀ x)) r, ‖fderiv ℝ P z - A‖ ≤ ε)
    (hnormal : ‖(ContinuousLinearMap.id ℝ F - A).comp (Q.comp (fderiv ℝ f₀ x))‖ ≤ ν)
    (hpriorValue : ‖f x - f₀ x‖ ≤ E₀ * ρ)
    (hpriorDeriv : ‖fderiv ℝ f x - fderiv ℝ f₀ x‖ ≤ H₀) :
    let g : E → H := fun y => f y + ψ (f y) • J (P (Q (f y)) - Q (f y))
    ‖g x - f₀ x‖ < c * ρ ∧ ‖fderiv ℝ g x - fderiv ℝ f₀ x‖ < c ∧
      ‖(fderiv ℝ P (Q (f x))).comp (Q.comp (fderiv ℝ f x)) -
        A.comp (Q.comp (fderiv ℝ f₀ x))‖ < μ := by
  have hdisplacement := perturbed_nearest_displacement P A hA (Q (f₀ x)) (Q (f x))
    hr hy hP hcomparison hcenter
  have hQerror : ‖Q (f x) - Q (f₀ x)‖ ≤ E₀ * ρ := by
    rw [← map_sub]
    exact ((Q.le_opNorm _).trans
      ((mul_le_mul_of_nonneg_right hQ (norm_nonneg _)).trans_eq (one_mul _))).trans
        hpriorValue
  have hvalue : ‖P (Q (f x)) - Q (f x)‖ ≤
      ((5 / 3 : ℝ) * ε * σ + (1 + ε) * E₀) * ρ := by
    have h1 := mul_le_mul_of_nonneg_left hradius hε
    have h2 := mul_le_mul_of_nonneg_left hQerror (by linarith : 0 ≤ 1 + ε)
    nlinarith
  exact projected_adjustment_lt_of_threshold Q J A hQ hJ hA hf hψ (hP _ hy)
    hc hc1 hμ hb hL hε hE hH hρ hεsmall hσ hν hεα hEα hHα hcutoff
    hvalue hcutoffDeriv hfirst (hcomparison _ hy) hnormal hpriorValue hpriorDeriv

end DifferentialGeometry.Analysis

namespace GC.MetricGeometry

variable {H I : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [FiniteDimensional ℝ H]

theorem spectral_zero_coordinate_nearest
    (V : Submodule ℝ H) (S : Finset I) (L : I → Submodule ℝ H) (center : I → H)
    (w : I → H → ℝ) (x : H) {b r : ℝ} (hb : 1 ≤ b) (hr : 0 < r)
    (hw : ∀ z ∈ ball x (8 * b * r), ∑ i ∈ S, w i z = 1)
    (hL : ∀ z ∈ ball x (8 * b * r), ∀ i ∈ S, w i z ≠ 0 → L i ≤ Vᗮ)
    (hcenter : ∀ z ∈ ball x (8 * b * r), ∀ i ∈ S, w i z ≠ 0 → center i ∈ Vᗮ)
    (y : H) (hy : ‖y - x‖ < 3 * b * r)
    (hzero :
      ((⨆ a ∈ ball (1 : ℝ) (1 / 2), Module.End.eigenspace
        (∑ i ∈ S, w i y • (L i)ᗮ.starProjection).toLinearMap a).starProjection)
          (y - ∑ i ∈ S, w i y • center i) = 0) :
    V.starProjection y = 0 ∧
      ∀ z : H, V.starProjection z = 0 → ∀ ψ : ℝ,
        V.starProjection (z + ψ • (y - z)) = 0 := by
  have hyball : y ∈ ball x (8 * b * r) := by
    change dist y x < 8 * b * r
    rw [dist_eq_norm]
    nlinarith [mul_pos (by linarith : 0 < b) hr]
  have hsection := Submodule.starProjection_weighted_normal_section V S L center
    (fun i => w i y) (hw y hyball) (hL y hyball) (hcenter y hyball)
    (ball (1 : ℝ) (1 / 2)) (by simp) y
  let Q := ((⨆ a ∈ ball (1 : ℝ) (1 / 2), Module.End.eigenspace
    (∑ i ∈ S, w i y • (L i)ᗮ.starProjection).toLinearMap a).starProjection)
  have heq : (∑ i ∈ S, w i y • Q (y - center i)) =
      Q (y - ∑ i ∈ S, w i y • center i) := by
    simp only [map_sub, smul_sub, Finset.sum_sub_distrib, ← Finset.sum_smul,
      hw y hyball, one_smul, map_sum, map_smul]
  change V.starProjection (∑ i ∈ S, w i y • Q (y - center i)) = _ at hsection
  rw [heq, hzero, map_zero] at hsection
  have hv : V.starProjection y = 0 := hsection.symm
  refine ⟨hv, ?_⟩
  intro z hz ψ
  simp only [map_add, map_smul, map_sub, hv, hz, sub_zero, smul_zero, add_zero]

theorem small_marker_block_vanishes_of_support_scales
    {MP MI V : Type*} [Zero V] (ρ : MP → ℝ) (R : MI → ℝ)
    (marker : MI → MP → ℝ) (block : MI → MP → V)
    (hmarker : ∀ i p, 0 ≤ marker i p)
    (hsupport : ∀ i p, 0 < marker i p → ρ p ≤ 5 * R i / 4)
    (hzero : ∀ i p, marker i p = 0 → block i p = 0)
    (a i : MI) (p : MP) (ha : 0 < R a) (hcore : 3 * R a / 4 ≤ ρ p)
    (hprune : R i ≤ R a / 2) : block i p = 0 := by
  apply hzero i p
  apply le_antisymm ?_ (hmarker i p)
  by_contra hnot
  have hp := hsupport i p (lt_of_not_ge hnot)
  linarith

omit [FiniteDimensional ℝ H] in
omit [FiniteDimensional ℝ H] in
theorem small_marker_segment_bound
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (J : H →L[ℝ] V) (hJ : ‖J‖ ≤ 1) {x y : H} (hx : J x = 0)
    {ρ R E : ℝ} (hR : 0 ≤ R) (herror : ‖y - x‖ ≤ E * ρ)
    (hsmall : R < ρ / 16 → J y = 0) (hE : 0 ≤ E) (hEsmall : E ≤ 1 / 512) :
    ∀ z ∈ segment ℝ x y, ‖J z‖ ≤ R / 32 := by
  have hh := J.norm_on_segment_le_of_vanishing_at_small_scale hJ hx hR
    (by norm_num : (0 : ℝ) < 16) herror hsmall hE
  intro z hz
  exact (hh z hz).trans (by nlinarith [mul_le_mul_of_nonneg_right hEsmall hR])

end GC.MetricGeometry

namespace DifferentialGeometry.Analysis

theorem affine_adjustment_consumer {ε : ℝ} (hε : 0 ≤ ε) (hεsmall : ε ≤ 1 / 32) :
    let P : ℝ → ℝ := fun y => (1 + ε) * y
    let g : ℝ → ℝ := fun y => y + (1 / 2 : ℝ) * (P y - y)
    ‖fderiv ℝ g 0 - ContinuousLinearMap.id ℝ ℝ‖ < 1 ∧
      ‖fderiv ℝ P 0 - ContinuousLinearMap.id ℝ ℝ‖ < 1 := by
  let P : ℝ → ℝ := fun y => (1 + ε) * y
  have hder : fderiv ℝ P 0 = (1 + ε) • ContinuousLinearMap.id ℝ ℝ :=
    ((hasFDerivAt_id (0 : ℝ)).const_mul (1 + ε)).fderiv
  have hcompare : ‖fderiv ℝ P 0 - ContinuousLinearMap.id ℝ ℝ‖ ≤ ε := by
    rw [hder]
    have heq : (1 + ε) • ContinuousLinearMap.id ℝ ℝ - ContinuousLinearMap.id ℝ ℝ =
        ε • ContinuousLinearMap.id ℝ ℝ := by
      apply ContinuousLinearMap.ext
      intro v
      simp only [smul_apply, ContinuousLinearMap.id_apply, sub_apply]
      simp only [smul_eq_mul]
      ring
    rw [heq, norm_smul, Real.norm_eq_abs, abs_of_nonneg hε]
    simpa only [mul_one] using
      mul_le_mul_of_nonneg_left (ContinuousLinearMap.norm_id_le (𝕜 := ℝ) (E := ℝ)) hε
  have hh := projected_adjustment_lt_of_threshold (f := id) (f₀ := id)
    (ψ := fun y : ℝ => (1 / 2 : ℝ)) (P := P) (x := 0)
    (ContinuousLinearMap.id ℝ ℝ) (ContinuousLinearMap.id ℝ ℝ)
    (ContinuousLinearMap.id ℝ ℝ) ContinuousLinearMap.norm_id_le
    ContinuousLinearMap.norm_id_le (by simp) differentiableAt_id
    (differentiableAt_const (1 / 2 : ℝ))
    (by exact ((differentiableAt_const (1 + ε)).mul differentiableAt_id))
    (c := 1) (μ := 1) (b := 0) (L := 1) (ε := ε) (σ := 1 / 2)
    (ρ := 1) (E₀ := 0) (H₀ := 0) (ν := 0)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hε (by norm_num) (by norm_num) (by norm_num) (by linarith) (by norm_num)
    (by norm_num) (by norm_num; exact hεsmall) (by norm_num) (by norm_num)
    (by constructor <;> norm_num)
    (by
      simpa only [P, id_eq, ContinuousLinearMap.id_apply, sub_zero, Real.norm_eq_abs,
        one_div, mul_zero, add_zero, mul_one, abs_zero] using
        mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 5 / 3) hε)
          (by norm_num : (0 : ℝ) ≤ 2⁻¹)) (by simp)
    (by simp [fderiv_id, ContinuousLinearMap.norm_id])
    hcompare (by simp) (by simp) (by simp)
  dsimp only at hh ⊢
  refine ⟨?_, hcompare.trans_lt (by linarith)⟩
  simpa only [P, id_eq, ContinuousLinearMap.id_apply, smul_eq_mul, fderiv_id] using hh.2.1

end DifferentialGeometry.Analysis
