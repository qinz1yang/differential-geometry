import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

set_option autoImplicit false

noncomputable section

open Filter Metric Set
open scoped Topology NNReal

namespace DifferentialGeometry.Geometry.Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {D : E → ℝ} {L : ℝ≥0} {G H : E}

omit [InnerProductSpace ℝ E] in
private theorem lipschitz_value_le_norm_mul
    (hD : LipschitzWith L D) (hzero : D 0 = 0) (v : E) :
    D v ≤ (L : ℝ) * ‖v‖ := by
  have hbound : |D v| ≤ (L : ℝ) * ‖v‖ := by
    simpa only [hzero, Real.dist_eq, sub_zero, dist_zero_right, Real.norm_eq_abs]
      using hD.dist_le_mul v 0
  exact (le_abs_self _).trans hbound

private theorem exists_quadratic_penalty_maximizer [FiniteDimensional ℝ E]
    (hD : LipschitzWith L D) (hzero : D 0 = 0) :
    ∃ G : E, ∀ v : E, D v - ‖v‖ ^ 2 / 2 ≤ D G - ‖G‖ ^ 2 / 2 := by
  let f : E → ℝ := fun v => D v - ‖v‖ ^ 2 / 2
  let R : ℝ := 2 * (L : ℝ) + 1
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hzero_mem : (0 : E) ∈ closedBall 0 R := by
    simpa only [mem_closedBall, dist_self] using hR
  have hf : Continuous f :=
    hD.continuous.sub ((continuous_norm.pow 2).div_const 2)
  obtain ⟨G, _, hmax⟩ := (isCompact_closedBall (0 : E) R).exists_isMaxOn
    ⟨0, hzero_mem⟩ hf.continuousOn
  have hmax' : ∀ v ∈ closedBall (0 : E) R, f v ≤ f G := isMaxOn_iff.mp hmax
  have hnonneg : 0 ≤ f G := by
    simpa only [f, hzero, norm_zero, zero_pow (by decide : 2 ≠ 0),
      zero_div, sub_zero] using hmax' 0 hzero_mem
  refine ⟨G, fun v => ?_⟩
  by_cases hv : v ∈ closedBall (0 : E) R
  · exact hmax' v hv
  · have hvR : R < ‖v‖ := by
      simpa only [mem_closedBall, dist_zero_right, not_le] using hv
    have hvL : 0 ≤ ‖v‖ - 2 * (L : ℝ) := by dsimp [R] at hvR; linarith
    have hprod := mul_nonneg (norm_nonneg v) hvL
    have hDv := lipschitz_value_le_norm_mul hD hzero v
    have hvf : f v ≤ 0 := by dsimp [f]; nlinarith
    exact hvf.trans hnonneg

private theorem gradient_support_of_penalty_maximum
    (hsmul : ∀ (a : ℝ), 0 ≤ a → ∀ v : E, D (a • v) = a * D v)
    (hadd : ∀ v w : E, D v + D w ≤ D (v + w))
    (hmax : ∀ v : E, D v - ‖v‖ ^ 2 / 2 ≤ D G - ‖G‖ ^ 2 / 2) :
    ∀ v : E, D v ≤ inner ℝ G v := by
  intro v
  have hstep (t : ℝ) (ht : 0 < t) :
      D v ≤ inner ℝ G v + t * ‖v‖ ^ 2 / 2 := by
    have hsum := hadd G (t • v)
    rw [hsmul t ht.le v] at hsum
    have hnorm : ‖G + t • v‖ ^ 2 =
        ‖G‖ ^ 2 + 2 * t * inner ℝ G v + t ^ 2 * ‖v‖ ^ 2 := by
      rw [norm_add_sq_real, real_inner_smul_right, norm_smul,
        Real.norm_eq_abs, abs_of_pos ht]
      ring
    have hm := hmax (G + t • v)
    rw [hnorm] at hm
    have hmul : t * D v ≤ t * (inner ℝ G v + t * ‖v‖ ^ 2 / 2) := by
      nlinarith [hm, hsum]
    exact (mul_le_mul_iff_right₀ ht).mp hmul
  apply le_of_forall_pos_le_add
  intro ε hε
  let t : ℝ := ε / (‖v‖ ^ 2 + 1)
  have hden : 0 < ‖v‖ ^ 2 + 1 := by positivity
  have ht : 0 < t := div_pos hε hden
  have hteq : t * (‖v‖ ^ 2 + 1) = ε := by
    dsimp only [t]
    exact div_mul_cancel₀ _ hden.ne'
  have hsmall : t * ‖v‖ ^ 2 / 2 ≤ ε := by nlinarith
  exact (hstep t ht).trans (by linarith)

private theorem gradient_calibration_of_penalty_maximum
    (hsmul : ∀ (a : ℝ), 0 ≤ a → ∀ v : E, D (a • v) = a * D v)
    (hmax : ∀ v : E, D v - ‖v‖ ^ 2 / 2 ≤ D G - ‖G‖ ^ 2 / 2) :
    D G = ‖G‖ ^ 2 := by
  let q : ℝ → ℝ := fun t => t * D G - t ^ 2 * ‖G‖ ^ 2 / 2
  have hloc : IsLocalMax q 1 := by
    change ∀ᶠ t : ℝ in 𝓝 1, q t ≤ q 1
    filter_upwards [eventually_gt_nhds (by norm_num : (0 : ℝ) < 1)] with t ht
    have hm := hmax (t • G)
    rw [hsmul t ht.le G, norm_smul, Real.norm_eq_abs, abs_of_pos ht, mul_pow] at hm
    simpa only [q, one_mul, one_pow] using hm
  have hder : HasDerivAt q (D G - ‖G‖ ^ 2) 1 := by
    convert! ((hasDerivAt_id (1 : ℝ)).mul_const (D G)).sub
      ((((hasDerivAt_id (1 : ℝ)).pow 2).mul_const (‖G‖ ^ 2)).div_const 2) using 1
    norm_num [q]
  exact sub_eq_zero.mp (hloc.hasDerivAt_eq_zero hder)

theorem superadditive_gradient_unique
    (hGsupport : ∀ v : E, D v ≤ inner ℝ G v) (hGcal : D G = ‖G‖ ^ 2)
    (hHsupport : ∀ v : E, D v ≤ inner ℝ H v) (hHcal : D H = ‖H‖ ^ 2) :
    G = H := by
  have hGH := hGsupport H
  have hHG := hHsupport G
  rw [hHcal] at hGH
  rw [hGcal, real_inner_comm G H] at hHG
  have hsub : ‖G - H‖ ^ 2 ≤ 0 := by
    rw [norm_sub_sq_real]
    linarith
  have hnorm : ‖G - H‖ = 0 := by nlinarith [norm_nonneg (G - H)]
  exact sub_eq_zero.mp (norm_eq_zero.mp hnorm)

theorem existsUnique_superadditive_gradient [FiniteDimensional ℝ E]
    (hD : LipschitzWith L D) (hzero : D 0 = 0)
    (hsmul : ∀ (a : ℝ), 0 ≤ a → ∀ v : E, D (a • v) = a * D v)
    (hadd : ∀ v w : E, D v + D w ≤ D (v + w)) :
    ∃! G : E, (∀ v : E, D v ≤ inner ℝ G v) ∧ D G = ‖G‖ ^ 2 := by
  obtain ⟨G, hmax⟩ := exists_quadratic_penalty_maximizer hD hzero
  have hs := gradient_support_of_penalty_maximum hsmul hadd hmax
  have hc := gradient_calibration_of_penalty_maximum hsmul hmax
  refine ⟨G, ⟨hs, hc⟩, ?_⟩
  intro H hH
  exact superadditive_gradient_unique hH.1 hH.2 hs hc

theorem superadditive_gradient_eq_zero_iff
    (hsupport : ∀ v : E, D v ≤ inner ℝ G v) (hcal : D G = ‖G‖ ^ 2) :
    G = 0 ↔ ∀ v : E, D v ≤ 0 := by
  constructor
  · intro hG v
    simpa only [hG, inner_zero_left] using hsupport v
  · intro hnonpos
    have hsq : ‖G‖ ^ 2 ≤ 0 := hcal ▸ hnonpos G
    have hnorm : ‖G‖ = 0 := by nlinarith [norm_nonneg G]
    exact norm_eq_zero.mp hnorm

theorem superadditive_gradient_ne_zero_iff
    (hsupport : ∀ v : E, D v ≤ inner ℝ G v) (hcal : D G = ‖G‖ ^ 2) :
    G ≠ 0 ↔ ∃ v : E, 0 < D v := by
  constructor
  · intro hG
    refine ⟨G, ?_⟩
    rw [hcal]
    exact sq_pos_of_pos (norm_pos_iff.mpr hG)
  · rintro ⟨v, hv⟩ hG
    have hnonpos := (superadditive_gradient_eq_zero_iff hsupport hcal).mp hG v
    exact (not_lt_of_ge hnonpos) hv

omit [InnerProductSpace ℝ E] in
theorem superadditive_gradient_norm_le
    (hD : LipschitzWith L D) (hzero : D 0 = 0) (hcal : D G = ‖G‖ ^ 2) :
    ‖G‖ ≤ (L : ℝ) := by
  by_cases hG : G = 0
  · simpa only [hG, norm_zero] using L.coe_nonneg
  · have hpos : 0 < ‖G‖ := norm_pos_iff.mpr hG
    have hbound := lipschitz_value_le_norm_mul hD hzero G
    rw [hcal, pow_two] at hbound
    exact (mul_le_mul_iff_left₀ hpos).mp hbound

theorem superadditive_gradient_le_norm_mul
    (hsupport : ∀ v : E, D v ≤ inner ℝ G v) (v : E) :
    D v ≤ ‖G‖ * ‖v‖ :=
  (hsupport v).trans (real_inner_le_norm G v)

theorem superadditive_gradient_unit_maximizer
    (hsmul : ∀ (a : ℝ), 0 ≤ a → ∀ v : E, D (a • v) = a * D v)
    (hsupport : ∀ v : E, D v ≤ inner ℝ G v) (hcal : D G = ‖G‖ ^ 2)
    (hG : G ≠ 0) :
    ‖‖G‖⁻¹ • G‖ = 1 ∧ D (‖G‖⁻¹ • G) = ‖G‖ ∧
      (∀ v : E, ‖v‖ ≤ 1 → D v ≤ ‖G‖) ∧
      (∀ v : E, ‖v‖ ≤ 1 → D v = ‖G‖ → v = ‖G‖⁻¹ • G) := by
  have hpos : 0 < ‖G‖ := norm_pos_iff.mpr hG
  have hne : ‖G‖ ≠ 0 := hpos.ne'
  have hunit : ‖‖G‖⁻¹ • G‖ = 1 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hpos), inv_mul_cancel₀ hne]
  have hvalue : D (‖G‖⁻¹ • G) = ‖G‖ := by
    rw [hsmul _ (inv_nonneg.mpr (norm_nonneg G)) G, hcal,
      pow_two, ← mul_assoc, inv_mul_cancel₀ hne, one_mul]
  have hbound (v : E) (hv : ‖v‖ ≤ 1) : D v ≤ ‖G‖ := by
    calc
      D v ≤ ‖G‖ * ‖v‖ := superadditive_gradient_le_norm_mul hsupport v
      _ ≤ ‖G‖ := by simpa only [mul_one] using mul_le_mul_of_nonneg_left hv (norm_nonneg G)
  refine ⟨hunit, hvalue, hbound, ?_⟩
  intro v hv hDv
  have hlower : 1 ≤ ‖v‖ := by
    apply (mul_le_mul_iff_right₀ hpos).mp
    calc
      ‖G‖ * 1 = D v := by rw [mul_one, hDv]
      _ ≤ ‖G‖ * ‖v‖ := superadditive_gradient_le_norm_mul hsupport v
  have hvnorm : ‖v‖ = 1 := le_antisymm hv hlower
  have hinner : inner ℝ G v = ‖G‖ * ‖v‖ := by
    apply le_antisymm (real_inner_le_norm G v)
    simpa only [hvnorm, mul_one, hDv] using hsupport v
  have hv_eq := (inner_eq_norm_mul_iff_div (𝕜 := ℝ) hG).mp hinner
  simpa only [hvnorm, RCLike.ofReal_real_eq_id, id_eq, one_div] using hv_eq.symm

theorem existsUnique_superadditive_unit_ball_maximizer [FiniteDimensional ℝ E]
    (hD : LipschitzWith L D) (hzero : D 0 = 0)
    (hsmul : ∀ (a : ℝ), 0 ≤ a → ∀ v : E, D (a • v) = a * D v)
    (hadd : ∀ v w : E, D v + D w ≤ D (v + w))
    (hpositive : ∃ v : E, 0 < D v) :
    ∃! U : E, ‖U‖ ≤ 1 ∧ ∀ v : E, ‖v‖ ≤ 1 → D v ≤ D U := by
  obtain ⟨G, hG, _⟩ := existsUnique_superadditive_gradient hD hzero hsmul hadd
  have hne := (superadditive_gradient_ne_zero_iff hG.1 hG.2).mpr hpositive
  obtain ⟨hunit, hvalue, hbound, huniq⟩ :=
    superadditive_gradient_unit_maximizer hsmul hG.1 hG.2 hne
  refine ⟨‖G‖⁻¹ • G, ⟨hunit.le, ?_⟩, ?_⟩
  · intro v hv
    rw [hvalue]
    exact hbound v hv
  · intro U hU
    apply huniq U hU.1
    apply le_antisymm (hbound U hU.1)
    calc
      ‖G‖ = D (‖G‖⁻¹ • G) := hvalue.symm
      _ ≤ D U := hU.2 _ hunit.le

end DifferentialGeometry.Geometry.Topology
