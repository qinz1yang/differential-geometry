import DifferentialGeometry.Analysis.Calculus.BilinearBounds
import DifferentialGeometry.Analysis.Calculus.FDeriv.Punctured
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.ZPow
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Analysis.Calculus.FDeriv.RestrictScalars
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Ring

set_option autoImplicit false

noncomputable section

open Set Filter Metric
open scoped Topology ContDiff

namespace DifferentialGeometry.Analysis

/-- Conjugation of a real planar operator by the differential of a power map,
with the identity value at the center. Off the center the radial factors
cancel, so this is also conjugation by the corresponding unit rotation. -/
def complexPowerConjugate (m : ℕ) (A : ℂ → ℂ →L[ℝ] ℂ) (w : ℂ) : ℂ →L[ℝ] ℂ :=
  if w = 0 then ContinuousLinearMap.id ℝ ℂ else
    (ContinuousLinearMap.mul ℝ ℂ ((w ^ m)⁻¹)).comp
      ((A w).comp (ContinuousLinearMap.mul ℝ ℂ (w ^ m)))

private theorem inverse_power_hasFDerivAt
    (m : ℕ) {w : ℂ} (hw : w ≠ 0) :
    HasFDerivAt (fun z : ℂ => (z ^ m)⁻¹)
      ((ContinuousLinearMap.toSpanSingleton ℂ
        (-(m : ℂ) * (w ^ (m + 1))⁻¹)).restrictScalars ℝ) w := by
  have he : -(m : ℤ) - 1 = -((m + 1 : ℕ) : ℤ) := by omega
  have hd := ((hasDerivAt_zpow (-(m : ℤ)) w (Or.inl hw)).hasFDerivAt).restrictScalars ℝ
  simpa only [he, Int.cast_neg, Int.cast_natCast, zpow_neg, zpow_natCast] using hd

private theorem norm_fderiv_operator_comp_le
    {A B : ℂ → ℂ →L[ℝ] ℂ} {w : ℂ}
    (hA : DifferentiableAt ℝ A w) (hB : DifferentiableAt ℝ B w) :
    ‖fderiv ℝ (fun z => (A z).comp (B z)) w‖ ≤
      ‖A w‖ * ‖fderiv ℝ B w‖ + ‖fderiv ℝ A w‖ * ‖B w‖ := by
  have hb := ContinuousLinearMap.norm_fderiv_bilinear_le
    (ContinuousLinearMap.compL ℝ ℂ ℂ ℂ) hA hB
  exact hb.trans (mul_le_of_le_one_left (by positivity)
    (ContinuousLinearMap.norm_compL_le ℝ ℂ ℂ ℂ))

private theorem complexPowerConjugate_sub_id
    (m : ℕ) (A : ℂ → ℂ →L[ℝ] ℂ) {w : ℂ} (hw : w ≠ 0) :
    complexPowerConjugate m A w - ContinuousLinearMap.id ℝ ℂ =
      (ContinuousLinearMap.mul ℝ ℂ ((w ^ m)⁻¹)).comp
        ((A w - ContinuousLinearMap.id ℝ ℂ).comp
          (ContinuousLinearMap.mul ℝ ℂ (w ^ m))) := by
  rw [complexPowerConjugate, ite_eq_right hw]
  ext v
  change (w ^ m)⁻¹ * A w (w ^ m * v) - v =
    (w ^ m)⁻¹ * (A w (w ^ m * v) - w ^ m * v)
  rw [mul_sub, ← mul_assoc, inv_mul_cancel₀ (pow_ne_zero m hw), one_mul]

private theorem power_multiplication_derivative_bounds
    {m : ℕ} (hm : 1 ≤ m) {w : ℂ} (hw : w ≠ 0) :
    let P : ℂ → ℂ →L[ℝ] ℂ := fun z => ContinuousLinearMap.mul ℝ ℂ (z ^ m)
    let J : ℂ → ℂ →L[ℝ] ℂ := fun z => ContinuousLinearMap.mul ℝ ℂ ((z ^ m)⁻¹)
    ContDiffAt ℝ 1 P w ∧ ContDiffAt ℝ 1 J w ∧
      ‖fderiv ℝ P w‖ ≤ (m : ℝ) * ‖w‖ ^ m / ‖w‖ ∧
      ‖fderiv ℝ J w‖ ≤ (m : ℝ) * (‖w‖ ^ (m + 1))⁻¹ := by
  intro P J
  have hpC : ContDiffAt ℝ 1 (fun z : ℂ => z ^ m) w := contDiffAt_id.pow m
  have hjC : ContDiffAt ℝ 1 (fun z : ℂ => (z ^ m)⁻¹) w :=
    hpC.inv (pow_ne_zero m hw)
  have hP : ContDiffAt ℝ 1 P w :=
    (ContinuousLinearMap.mul ℝ ℂ).contDiff.contDiffAt.comp w hpC
  have hJ : ContDiffAt ℝ 1 J w :=
    (ContinuousLinearMap.mul ℝ ℂ).contDiff.contDiffAt.comp w hjC
  refine ⟨hP, hJ, ?_, ?_⟩
  · have hp := (hasDerivAt_pow m w).hasFDerivAt.restrictScalars ℝ
    change ‖fderiv ℝ ((ContinuousLinearMap.mul ℝ ℂ) ∘
      (fun z : ℂ => z ^ m)) w‖ ≤ (m : ℝ) * ‖w‖ ^ m / ‖w‖
    rw [((ContinuousLinearMap.mul ℝ ℂ).hasFDerivAt.comp w hp).fderiv]
    calc
      _ ≤ ‖ContinuousLinearMap.mul ℝ ℂ‖ *
          ‖(ContinuousLinearMap.toSpanSingleton ℂ
            ((m : ℂ) * w ^ (m - 1))).restrictScalars ℝ‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ 1 * ‖(ContinuousLinearMap.toSpanSingleton ℂ
          ((m : ℂ) * w ^ (m - 1))).restrictScalars ℝ‖ :=
        mul_le_mul_of_nonneg_right (ContinuousLinearMap.opNorm_mul_le ℝ ℂ) (norm_nonneg _)
      _ = (m : ℝ) * ‖w‖ ^ (m - 1) := by
        rw [one_mul, ContinuousLinearMap.norm_restrictScalars,
          ContinuousLinearMap.norm_toSpanSingleton]
        simp only [norm_mul, Complex.norm_natCast, norm_pow]
      _ = (m : ℝ) * ‖w‖ ^ m / ‖w‖ := by
        have he : ‖w‖ ^ m = ‖w‖ ^ (m - 1) * ‖w‖ := by
          rw [← pow_succ, Nat.sub_add_cancel hm]
        rw [he]
        field_simp [norm_ne_zero_iff.mpr hw]
  · have hi := inverse_power_hasFDerivAt m hw
    change ‖fderiv ℝ ((ContinuousLinearMap.mul ℝ ℂ) ∘
      (fun z : ℂ => (z ^ m)⁻¹)) w‖ ≤ (m : ℝ) * (‖w‖ ^ (m + 1))⁻¹
    rw [((ContinuousLinearMap.mul ℝ ℂ).hasFDerivAt.comp w hi).fderiv]
    calc
      _ ≤ ‖ContinuousLinearMap.mul ℝ ℂ‖ *
          ‖(ContinuousLinearMap.toSpanSingleton ℂ
            (-(m : ℂ) * (w ^ (m + 1))⁻¹)).restrictScalars ℝ‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ 1 * ‖(ContinuousLinearMap.toSpanSingleton ℂ
          (-(m : ℂ) * (w ^ (m + 1))⁻¹)).restrictScalars ℝ‖ :=
        mul_le_mul_of_nonneg_right (ContinuousLinearMap.opNorm_mul_le ℝ ℂ) (norm_nonneg _)
      _ = _ := by
        rw [one_mul, ContinuousLinearMap.norm_restrictScalars,
          ContinuousLinearMap.norm_toSpanSingleton]
        simp only [norm_mul, norm_neg, Complex.norm_natCast, norm_inv, norm_pow]

private theorem complexPowerConjugate_pointwise_bounds
    {m : ℕ} (hm : 1 ≤ m) {A : ℂ → ℂ →L[ℝ] ℂ} {C : ℝ} (hC : 0 ≤ C)
    {w : ℂ} (hw : w ≠ 0) (hA : ContDiffAt ℝ 1 A w)
    (hsize : ‖A w - ContinuousLinearMap.id ℝ ℂ‖ ≤ C * ‖w‖ ^ 2)
    (hder : ‖fderiv ℝ A w‖ ≤ C * ‖w‖) :
    ContDiffAt ℝ 1 (complexPowerConjugate m A) w ∧
      ‖complexPowerConjugate m A w - ContinuousLinearMap.id ℝ ℂ‖ ≤ C * ‖w‖ ^ 2 ∧
      ‖fderiv ℝ (complexPowerConjugate m A) w‖ ≤
        ((2 * (m : ℝ) + 1) * C) * ‖w‖ := by
  let P : ℂ → ℂ →L[ℝ] ℂ := fun z => ContinuousLinearMap.mul ℝ ℂ (z ^ m)
  let J : ℂ → ℂ →L[ℝ] ℂ := fun z => ContinuousLinearMap.mul ℝ ℂ ((z ^ m)⁻¹)
  let D : ℂ → ℂ →L[ℝ] ℂ := fun z => A z - ContinuousLinearMap.id ℝ ℂ
  let B : ℂ → ℂ →L[ℝ] ℂ := fun z => (D z).comp (P z)
  let T : ℂ → ℂ →L[ℝ] ℂ := fun z => (J z).comp (B z)
  obtain ⟨hP, hJ, hPD, hJD⟩ := power_multiplication_derivative_bounds hm hw
  have hD : ContDiffAt ℝ 1 D w := hA.sub contDiffAt_const
  have hB : ContDiffAt ℝ 1 B w := hD.clm_comp hP
  have hT : ContDiffAt ℝ 1 T w := hJ.clm_comp hB
  have hnear : complexPowerConjugate m A =ᶠ[𝓝 w]
      fun z => T z + ContinuousLinearMap.id ℝ ℂ := by
    filter_upwards [eventually_ne_nhds hw] with z hz
    exact (sub_eq_iff_eq_add.mp (complexPowerConjugate_sub_id m A hz))
  have hK : ContDiffAt ℝ 1 (complexPowerConjugate m A) w :=
    (hT.add contDiffAt_const).congr_of_eventuallyEq hnear
  have hPn : ‖P w‖ = ‖w‖ ^ m := by
    simp only [P, ContinuousLinearMap.opNorm_mul_apply, norm_pow]
  have hJn : ‖J w‖ = (‖w‖ ^ m)⁻¹ := by
    simp only [J, ContinuousLinearMap.opNorm_mul_apply, norm_inv, norm_pow]
  have hn : ‖w‖ ≠ 0 := norm_ne_zero_iff.mpr hw
  have hDn : ‖D w‖ ≤ C * ‖w‖ ^ 2 := hsize
  have hDD : ‖fderiv ℝ D w‖ ≤ C * ‖w‖ := by
    simpa only [D, (hA.differentiableAt_one.hasFDerivAt.sub_const
      (ContinuousLinearMap.id ℝ ℂ)).fderiv] using hder
  have hBn : ‖B w‖ ≤ (C * ‖w‖ ^ 2) * ‖w‖ ^ m := by
    exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
      (by rw [hPn]; exact mul_le_mul_of_nonneg_right hDn (by positivity))
  have hBD : ‖fderiv ℝ B w‖ ≤
      (C * ‖w‖ ^ 2) * ((m : ℝ) * ‖w‖ ^ m / ‖w‖) + (C * ‖w‖) * ‖w‖ ^ m := by
    apply (norm_fderiv_operator_comp_le hD.differentiableAt_one hP.differentiableAt_one).trans
    rw [hPn]
    exact add_le_add
      (mul_le_mul hDn hPD (norm_nonneg _) (by positivity))
      (mul_le_mul_of_nonneg_right hDD (by positivity))
  refine ⟨hK, ?_, ?_⟩
  · rw [complexPowerConjugate_sub_id m A hw]
    change ‖T w‖ ≤ C * ‖w‖ ^ 2
    calc
      _ ≤ ‖J w‖ * ‖B w‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ (‖w‖ ^ m)⁻¹ * ((C * ‖w‖ ^ 2) * ‖w‖ ^ m) := by
        rw [hJn]
        exact mul_le_mul_of_nonneg_left hBn (by positivity)
      _ = _ := by field_simp [hn]
  · have hKD : fderiv ℝ (complexPowerConjugate m A) w = fderiv ℝ T w :=
      hnear.fderiv_eq.trans
        (hT.differentiableAt_one.hasFDerivAt.add_const (ContinuousLinearMap.id ℝ ℂ)).fderiv
    rw [hKD]
    calc
      _ ≤ ‖J w‖ * ‖fderiv ℝ B w‖ + ‖fderiv ℝ J w‖ * ‖B w‖ :=
        norm_fderiv_operator_comp_le hJ.differentiableAt_one hB.differentiableAt_one
      _ ≤ (‖w‖ ^ m)⁻¹ *
          ((C * ‖w‖ ^ 2) * ((m : ℝ) * ‖w‖ ^ m / ‖w‖) +
            (C * ‖w‖) * ‖w‖ ^ m) +
          ((m : ℝ) * (‖w‖ ^ (m + 1))⁻¹) * ((C * ‖w‖ ^ 2) * ‖w‖ ^ m) := by
        rw [hJn]
        exact add_le_add
          (mul_le_mul_of_nonneg_left hBD (by positivity))
          (mul_le_mul hJD hBn (norm_nonneg _) (by positivity))
      _ = _ := by
        rw [pow_succ]
        field_simp [hn]
        ring

/-- Quadratic convergence to the identity and a linear bound on the actual
punctured derivative remove the singularity of power conjugation. The
extended operator is genuinely `C¹`, with zero derivative at the center.
All norms are real Euclidean operator norms. -/
theorem contDiffAt_complexPowerConjugate_of_quadratic_order
    {m : ℕ} (hm : 1 ≤ m) {A : ℂ → ℂ →L[ℝ] ℂ} {C : ℝ} (hC : 0 ≤ C)
    (hA : ∀ᶠ w in 𝓝[≠] (0 : ℂ), ContDiffAt ℝ 1 A w)
    (hbound : ∀ᶠ w in 𝓝[≠] (0 : ℂ),
      ‖A w - ContinuousLinearMap.id ℝ ℂ‖ ≤ C * ‖w‖ ^ 2 ∧
        ‖fderiv ℝ A w‖ ≤ C * ‖w‖) :
    let K := complexPowerConjugate m A
    ContDiffAt ℝ 1 K 0 ∧ HasFDerivAt K (0 : ℂ →L[ℝ] ℂ →L[ℝ] ℂ) 0 ∧
      ∀ᶠ w in 𝓝 (0 : ℂ),
        ‖K w - ContinuousLinearMap.id ℝ ℂ‖ ≤ C * ‖w‖ ^ 2 ∧
          ‖fderiv ℝ K w‖ ≤ ((2 * (m : ℝ) + 1) * C) * ‖w‖ := by
  intro K
  have hK0 : K 0 = ContinuousLinearMap.id ℝ ℂ := by
    simp [K, complexPowerConjugate]
  have hall : ∀ᶠ w in 𝓝[≠] (0 : ℂ), ContDiffAt ℝ 1 K w ∧
      ‖K w - ContinuousLinearMap.id ℝ ℂ‖ ≤ C * ‖w‖ ^ 2 ∧
        ‖fderiv ℝ K w‖ ≤ ((2 * (m : ℝ) + 1) * C) * ‖w‖ := by
    filter_upwards [hA, hbound, self_mem_nhdsWithin] with w hw hb hw0
    exact complexPowerConjugate_pointwise_bounds hm hC hw0 hw hb.1 hb.2
  have hval : Tendsto (fun w => K w - ContinuousLinearMap.id ℝ ℂ)
      (𝓝[≠] (0 : ℂ)) (𝓝 0) := by
    apply squeeze_zero_norm' (hall.mono fun _ hw => hw.2.1)
    have ht : Tendsto (fun w : ℂ => C * ‖w‖ ^ 2) (𝓝[≠] (0 : ℂ))
        (𝓝 (C * ‖(0 : ℂ)‖ ^ 2)) :=
      (((continuousAt_id : ContinuousAt (fun w : ℂ => w) 0).norm.pow 2).const_mul C).tendsto.mono_left
        nhdsWithin_le_nhds
    simpa only [norm_zero, zero_pow (by decide : 2 ≠ 0), mul_zero] using ht
  have hcont : ContinuousAt K 0 := by
    apply continuousAt_iff_punctured_nhds.mpr
    rw [hK0]
    simpa only [sub_add_cancel, zero_add] using
      hval.add_const (ContinuousLinearMap.id ℝ ℂ)
  have hlim : Tendsto (fderiv ℝ K) (𝓝[≠] (0 : ℂ)) (𝓝 0) := by
    apply squeeze_zero_norm' (hall.mono fun _ hw => hw.2.2)
    have ht : Tendsto (fun w : ℂ => ((2 * (m : ℝ) + 1) * C) * ‖w‖)
        (𝓝[≠] (0 : ℂ)) (𝓝 (((2 * (m : ℝ) + 1) * C) * ‖(0 : ℂ)‖)) :=
      ((continuousAt_id : ContinuousAt (fun w : ℂ => w) 0).norm.const_mul
        ((2 * (m : ℝ) + 1) * C)).tendsto.mono_left nhdsWithin_le_nhds
    simpa only [norm_zero, mul_zero] using ht
  have hcenter : HasFDerivAt K (0 : ℂ →L[ℝ] ℂ →L[ℝ] ℂ) 0 :=
    DifferentialGeometry.hasFDerivAt_zero_of_punctured_tendsto
      (hall.mono fun _ hw => hw.1.differentiableAt_one.hasFDerivAt) hcont hlim
  have hcontD : ContinuousAt (fderiv ℝ K) 0 := by
    apply continuousAt_iff_punctured_nhds.mpr
    rw [hcenter.fderiv]
    exact hlim
  obtain ⟨r, hr, hball⟩ : ∃ r > 0, ball (0 : ℂ) r ∩ {(0 : ℂ)}ᶜ ⊆
      {w | ContDiffAt ℝ 1 K w ∧
        ‖K w - ContinuousLinearMap.id ℝ ℂ‖ ≤ C * ‖w‖ ^ 2 ∧
          ‖fderiv ℝ K w‖ ≤ ((2 * (m : ℝ) + 1) * C) * ‖w‖} :=
    mem_nhdsWithin_iff.1 hall
  have hK1 : ContDiffAt ℝ 1 K 0 := by
    apply contDiffAt_one_iff.mpr
    refine ⟨fderiv ℝ K, ball (0 : ℂ) r, ball_mem_nhds 0 hr, ?_, ?_⟩
    · intro w hw
      by_cases hw0 : w = 0
      · subst w
        exact hcontD.continuousWithinAt
      · exact ((hball ⟨hw, hw0⟩).1.continuousAt_fderiv one_ne_zero).continuousWithinAt
    · intro w hw
      by_cases hw0 : w = 0
      · subst w
        simpa only [hcenter.fderiv] using hcenter
      · exact (hball ⟨hw, hw0⟩).1.differentiableAt_one.hasFDerivAt
  refine ⟨hK1, hcenter, ?_⟩
  filter_upwards [ball_mem_nhds (0 : ℂ) hr] with w hw
  by_cases hw0 : w = 0
  · subst w
    rw [hK0, sub_self, hcenter.fderiv, norm_zero]
    simp
  · exact (hball ⟨hw, hw0⟩).2

end DifferentialGeometry.Analysis
