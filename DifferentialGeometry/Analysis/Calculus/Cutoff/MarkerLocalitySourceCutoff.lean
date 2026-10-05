import DifferentialGeometry.Analysis.Calculus.Cutoff.UniformAxisCutoff

/-!
# CFS31: the source first cutoff `ψ₁`

Blueprint `master207B.tex`, CFS31 (`prop:fibration-marker-cutoff-sequence`, lines 3783–3855), first paragraph of
the proof. For blocks `u_i : H → E_i`, `v_i : H → ℝ` (continuous linear, norm `≤ 1`) and the increasing profile
`χ` of CFS22 (`cfsRamp`), the source summand is

  `a_i = χ_{1/2,1}(v_i / R_i) · [1 − χ_{6,13/2}(|u_i| / v_i)]`

(`markerLocalitySourceGate`; for `v_i ≤ R_i/2` the first factor vanishes, so no division by a zero marker is used)
and `ψ₁ = χ_{1/2,1}(Σ_i a_i)` (`markerLocalitySourceCutoff`).

* `markerLocalitySourceGate_contDiff`: each summand is smooth (including at `u_i = 0`, where the radial factor is
  locally constant); `norm_fderiv_markerLocalitySourceGate_le`: `‖D a_i‖ ≤ 32 P / R_i` everywhere.
* `markerLocalitySourceCutoff_row`: on the ORIGINAL map (`u_i F = R_i ζ_i η_i`, `v_i F = R_i ζ_i`), `ψ₁` is smooth with
  values in `[0, 1]`, has the exact plateau `ψ₁(F p) = 1` where some `|η_i(p)| < 6` on `U_i`, its CLOSED support
  localizes the original point: `F p ∈ tsupport ψ₁ ⇒ ∃ i, p ∈ U_i ∧ |η_i(p)| ≤ 13/2 < 7` (stage-one instance of
  CFS29's localization hypothesis — the "first-stage" condition of review 39's §4.2 list), and
  `‖Dψ₁(F p)‖ ≤ 80 N P² / ρ(p) ≤ 10⁴ (N+1)² P⁴ / ρ(p)` from at most `N` positive markers and (AS).
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology
open scoped ContDiff BigOperators

namespace GC.MetricGeometry

section Gate

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]

/-- The CFS31 source summand `a(z) = χ_{1/2,1}(v z / R) · (1 − χ_{6,13/2}(‖u z‖ / v z))`. -/
def markerLocalitySourceGate (χ : ℝ → ℝ) (R : ℝ) (u : H →L[ℝ] E) (v : H →L[ℝ] ℝ) (z : H) : ℝ :=
  cfsRamp χ (1 / 2) 1 (v z / R) * (1 - cfsRamp χ 6 (13 / 2) (‖u z‖ / v z))

variable {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ) (hχ0 : ∀ t ≤ 0, χ t = 0)
  (hχ1 : ∀ t, 1 ≤ t → χ t = 1) (hχI : ∀ t, χ t ∈ Icc (0 : ℝ) 1)
  {R : ℝ} (u : H →L[ℝ] E) (v : H →L[ℝ] ℝ)

include hχI in
theorem markerLocalitySourceGate_mem_Icc (z : H) :
    markerLocalitySourceGate χ R u v z ∈ Icc (0 : ℝ) 1 := by
  have h1 := hχI ((v z / R - 1 / 2) / (1 - 1 / 2))
  have h2 := hχI ((‖u z‖ / v z - 6) / (13 / 2 - 6))
  simp only [markerLocalitySourceGate, cfsRamp, mem_Icc] at h1 h2 ⊢
  constructor <;> nlinarith

include hχ0 in
theorem markerLocalitySourceGate_eventually_zero_of_lt {z : H} (h : v z / R < 1 / 2) :
    markerLocalitySourceGate χ R u v =ᶠ[𝓝 z] fun _ => 0 := by
  have hopen : IsOpen {w | v w / R < 1 / 2} :=
    isOpen_lt (v.continuous.div_const R) continuous_const
  filter_upwards [hopen.mem_nhds h] with w hw
  simp only [markerLocalitySourceGate,
    cfsRamp_eq_zero hχ0 (by norm_num : (1 / 2 : ℝ) < 1) (le_of_lt hw), zero_mul]

theorem continuousAt_markerLocalityRatio {z : H} (hv : v z ≠ 0) :
    ContinuousAt (fun w => ‖u w‖ / v w) z :=
  ((continuous_norm.comp u.continuous).continuousAt).div v.continuous.continuousAt hv

include hχ1 in
theorem markerLocalitySourceGate_eventually_zero_of_gt {z : H} (hv : v z ≠ 0)
    (hs : 13 / 2 < ‖u z‖ / v z) : markerLocalitySourceGate χ R u v =ᶠ[𝓝 z] fun _ => 0 := by
  filter_upwards [(continuousAt_markerLocalityRatio u v hv).eventually (lt_mem_nhds hs)] with w hw
  simp only [markerLocalitySourceGate,
    cfsRamp_eq_one hχ1 (by norm_num : (6 : ℝ) < 13 / 2) hw.le, sub_self, mul_zero]

include hχ0 in
theorem markerLocalitySourceGate_eventually_eq_of_lt {z : H} (hv : v z ≠ 0)
    (hs : ‖u z‖ / v z < 6) :
    markerLocalitySourceGate χ R u v =ᶠ[𝓝 z] fun w => cfsRamp χ (1 / 2) 1 (v w / R) := by
  filter_upwards [(continuousAt_markerLocalityRatio u v hv).eventually (gt_mem_nhds hs)] with w hw
  simp only [markerLocalitySourceGate,
    cfsRamp_eq_zero hχ0 (by norm_num : (6 : ℝ) < 13 / 2) hw.le, sub_zero, mul_one]

include hχ hχ0 hχ1 in
theorem markerLocalitySourceGate_contDiffAt (hR : 0 < R) (z : H) :
    ContDiffAt ℝ ∞ (markerLocalitySourceGate χ R u v) z := by
  by_cases h1 : v z / R < 1 / 2
  · exact contDiffAt_const.congr_of_eventuallyEq
      (markerLocalitySourceGate_eventually_zero_of_lt hχ0 u v h1)
  have hvpos : 0 < v z := by
    rw [not_lt, le_div_iff₀ hR] at h1
    linarith
  have hg1 : ContDiff ℝ ∞ (fun w => cfsRamp χ (1 / 2) 1 (v w / R)) :=
    (contDiff_cfsRamp hχ _ _).comp (v.contDiff.div_const R)
  by_cases h2 : ‖u z‖ / v z < 6
  · exact hg1.contDiffAt.congr_of_eventuallyEq
      (markerLocalitySourceGate_eventually_eq_of_lt hχ0 u v hvpos.ne' h2)
  by_cases h3 : 13 / 2 < ‖u z‖ / v z
  · exact contDiffAt_const.congr_of_eventuallyEq
      (markerLocalitySourceGate_eventually_zero_of_gt hχ1 u v hvpos.ne' h3)
  have hu0 : u z ≠ 0 := by
    intro h0
    rw [h0, norm_zero, zero_div] at h2
    norm_num at h2
  have hs : ContDiffAt ℝ ∞ (fun w => ‖u w‖ / v w) z :=
    ((contDiffAt_norm ℝ hu0).comp z u.contDiff.contDiffAt).div v.contDiff.contDiffAt hvpos.ne'
  exact hg1.contDiffAt.mul (contDiffAt_const.sub ((contDiff_cfsRamp hχ _ _).contDiffAt.comp z hs))

include hχ hχ0 hχ1 in
theorem markerLocalitySourceGate_contDiff (hR : 0 < R) :
    ContDiff ℝ ∞ (markerLocalitySourceGate χ R u v) :=
  contDiff_iff_contDiffAt.mpr (markerLocalitySourceGate_contDiffAt hχ hχ0 hχ1 u v hR)

include hχ hχ0 hχ1 hχI in
/-- `‖D a‖ ≤ 32 P / R` everywhere (CFS31: ratio differential `≤ 15/R`, two profile slopes `2P`). -/
theorem norm_fderiv_markerLocalitySourceGate_le {P : ℝ} (hP1 : 1 ≤ P) (hP : ∀ t, |deriv χ t| ≤ P)
    (hu : ‖u‖ ≤ 1) (hv : ‖v‖ ≤ 1) (hR : 0 < R) (z : H) :
    ‖fderiv ℝ (markerLocalitySourceGate χ R u v) z‖ ≤ 32 * P / R := by
  have hbound0 : (0 : ℝ) ≤ 32 * P / R := by positivity
  by_cases h1 : v z / R < 1 / 2
  · rw [(markerLocalitySourceGate_eventually_zero_of_lt hχ0 u v h1).fderiv_eq, fderiv_const_apply,
      norm_zero]
    exact hbound0
  have hvR : R / 2 ≤ v z := by
    rw [not_lt, le_div_iff₀ hR] at h1
    linarith
  have hvpos : 0 < v z := by linarith
  set vR : H →L[ℝ] ℝ := R⁻¹ • v with hvRdef
  have hvRapply : ∀ w, v w / R = vR w := fun w => by
    simp [vR, div_eq_inv_mul]
  have hvRnorm : ‖vR‖ ≤ 1 / R := by
    calc ‖vR‖ ≤ ‖R⁻¹‖ * ‖v‖ := ContinuousLinearMap.opNorm_smul_le _ _
      _ ≤ R⁻¹ * 1 := by
          rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hR)]
          exact mul_le_mul_of_nonneg_left hv (inv_pos.mpr hR).le
      _ = 1 / R := by ring
  have hdg1 : ∀ t, DifferentiableAt ℝ (cfsRamp χ (1 / 2) 1) t := fun t =>
    (hasDerivAt_cfsRamp hχ _ _ t).differentiableAt
  have hA : ‖fderiv ℝ (fun w => cfsRamp χ (1 / 2) 1 (vR w)) z‖ ≤ 2 * P / R := by
    have h := norm_fderiv_comp_real_le (hdg1 (vR z)) vR.differentiableAt
      (abs_deriv_cfsRamp_le hχ hP (by norm_num : (1 / 2 : ℝ) < 1) (vR z))
    rw [vR.fderiv] at h
    calc _ ≤ P / (1 - 1 / 2) * ‖vR‖ := h
      _ ≤ P / (1 - 1 / 2) * (1 / R) :=
          mul_le_mul_of_nonneg_left hvRnorm (by positivity)
      _ = 2 * P / R := by ring
  by_cases h2 : ‖u z‖ / v z < 6
  · have heq := markerLocalitySourceGate_eventually_eq_of_lt hχ0 (R := R) u v hvpos.ne' h2
    rw [heq.fderiv_eq]
    simp only [hvRapply]
    exact hA.trans (by
      apply div_le_div_of_nonneg_right _ hR.le
      linarith)
  by_cases h3 : 13 / 2 < ‖u z‖ / v z
  · rw [(markerLocalitySourceGate_eventually_zero_of_gt hχ1 u v hvpos.ne' h3).fderiv_eq,
      fderiv_const_apply, norm_zero]
    exact hbound0
  rw [not_lt] at h2 h3
  have hu0 : u z ≠ 0 := by
    intro h0
    rw [h0, norm_zero, zero_div] at h2
    norm_num at h2
  have hd : v z ≠ 0 := hvpos.ne'
  have hNdiff : DifferentiableAt ℝ (fun w => ‖u w‖) z :=
    ((contDiffAt_norm (n := ∞) ℝ hu0).differentiableAt (by simp)).comp z u.differentiableAt
  have hNlip : LipschitzWith 1 (fun w => ‖u w‖) := by
    refine LipschitzWith.of_dist_le_mul fun w w' => ?_
    rw [Real.dist_eq, NNReal.coe_one, one_mul]
    calc |‖u w‖ - ‖u w'‖| ≤ ‖u w - u w'‖ := abs_norm_sub_norm_le _ _
      _ = ‖u (w - w')‖ := by rw [map_sub]
      _ ≤ ‖u‖ * ‖w - w'‖ := u.le_opNorm _
      _ ≤ 1 * ‖w - w'‖ := mul_le_mul_of_nonneg_right hu (norm_nonneg _)
      _ = dist w w' := by rw [one_mul, dist_eq_norm]
  have hN' : ‖fderiv ℝ (fun w => ‖u w‖) z‖ ≤ 1 := by
    simpa using norm_fderiv_le_of_lipschitz ℝ (x₀ := z) hNlip
  have hIv : HasFDerivAt (fun w => (v w)⁻¹) ((-((v z) ^ 2)⁻¹) • v) z :=
    (hasDerivAt_inv hd).comp_hasFDerivAt z v.hasFDerivAt
  have hs : HasFDerivAt (fun w => ‖u w‖ * (v w)⁻¹)
      (‖u z‖ • ((-((v z) ^ 2)⁻¹) • v) + (v z)⁻¹ • fderiv ℝ (fun w => ‖u w‖) z) z :=
    hNdiff.hasFDerivAt.mul hIv
  have hsnorm : ‖‖u z‖ • ((-((v z) ^ 2)⁻¹) • v) + (v z)⁻¹ • fderiv ℝ (fun w => ‖u w‖) z‖ ≤
      15 / R := by
    have hsz : ‖u z‖ ≤ 13 / 2 * v z := (div_le_iff₀ hvpos).mp h3
    have e1 : ‖‖u z‖ • ((-((v z) ^ 2)⁻¹) • v)‖ ≤ ‖u z‖ * ((v z) ^ 2)⁻¹ := by
      rw [norm_smul, norm_smul, norm_neg, Real.norm_eq_abs, Real.norm_eq_abs, abs_norm,
        abs_of_pos (by positivity : (0 : ℝ) < ((v z) ^ 2)⁻¹)]
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      calc ((v z) ^ 2)⁻¹ * ‖v‖ ≤ ((v z) ^ 2)⁻¹ * 1 := by gcongr
        _ = _ := mul_one _
    have e2 : ‖(v z)⁻¹ • fderiv ℝ (fun w => ‖u w‖) z‖ ≤ (v z)⁻¹ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity)]
      calc (v z)⁻¹ * ‖fderiv ℝ (fun w => ‖u w‖) z‖ ≤ (v z)⁻¹ * 1 := by gcongr
        _ = _ := mul_one _
    have e3 : ‖u z‖ * ((v z) ^ 2)⁻¹ ≤ 13 / 2 / v z := by
      calc ‖u z‖ * ((v z) ^ 2)⁻¹ ≤ 13 / 2 * v z * ((v z) ^ 2)⁻¹ := by gcongr
        _ = 13 / 2 / v z := by field_simp
    have e5 : 13 / 2 / v z + (v z)⁻¹ ≤ 15 / R := by
      rw [← one_div, ← add_div, div_le_div_iff₀ hvpos hR]
      nlinarith
    calc _ ≤ ‖‖u z‖ • ((-((v z) ^ 2)⁻¹) • v)‖ +
          ‖(v z)⁻¹ • fderiv ℝ (fun w => ‖u w‖) z‖ := norm_add_le _ _
      _ ≤ 13 / 2 / v z + (v z)⁻¹ := add_le_add (e1.trans e3) e2
      _ ≤ 15 / R := e5
  have hdq : ∀ t, DifferentiableAt ℝ (cfsRamp χ 6 (13 / 2)) t := fun t =>
    (hasDerivAt_cfsRamp hχ _ _ t).differentiableAt
  have hsfun : (fun w => ‖u w‖ / v w) = fun w => ‖u w‖ * (v w)⁻¹ := by
    funext w
    rw [div_eq_mul_inv]
  have hQ : HasFDerivAt (fun w => 1 - cfsRamp χ 6 (13 / 2) (‖u w‖ / v w))
      (-(deriv (cfsRamp χ 6 (13 / 2)) (‖u z‖ / v z) •
        (‖u z‖ • ((-((v z) ^ 2)⁻¹) • v) + (v z)⁻¹ • fderiv ℝ (fun w => ‖u w‖) z))) z := by
    have hs' : HasFDerivAt (fun w => ‖u w‖ / v w)
        (‖u z‖ • ((-((v z) ^ 2)⁻¹) • v) + (v z)⁻¹ • fderiv ℝ (fun w => ‖u w‖) z) z := by
      rw [hsfun]
      exact hs
    have hcomp := (hdq (‖u z‖ / v z)).hasDerivAt.comp_hasFDerivAt z hs'
    exact hcomp.const_sub 1
  have hQnorm : ‖-(deriv (cfsRamp χ 6 (13 / 2)) (‖u z‖ / v z) •
      (‖u z‖ • ((-((v z) ^ 2)⁻¹) • v) + (v z)⁻¹ • fderiv ℝ (fun w => ‖u w‖) z))‖ ≤
        30 * P / R := by
    rw [norm_neg, norm_smul, Real.norm_eq_abs]
    have hq := abs_deriv_cfsRamp_le hχ hP (by norm_num : (6 : ℝ) < 13 / 2) (‖u z‖ / v z)
    calc _ ≤ P / (13 / 2 - 6) * (15 / R) :=
          mul_le_mul hq hsnorm (norm_nonneg _) (by positivity)
      _ = 30 * P / R := by ring
  have hAfun : HasFDerivAt (fun w => cfsRamp χ (1 / 2) 1 (v w / R))
      (fderiv ℝ (fun w => cfsRamp χ (1 / 2) 1 (vR w)) z) z := by
    simp only [hvRapply]
    exact ((hdg1 (vR z)).comp z vR.differentiableAt).hasFDerivAt
  have hgate := hAfun.fun_mul hQ
  have hgfun : markerLocalitySourceGate χ R u v = fun w => cfsRamp χ (1 / 2) 1 (v w / R) *
      (1 - cfsRamp χ 6 (13 / 2) (‖u w‖ / v w)) := rfl
  rw [hgfun, hgate.fderiv]
  have hc1 := hχI ((v z / R - 1 / 2) / (1 - 1 / 2))
  have hc2 := hχI ((‖u z‖ / v z - 6) / (13 / 2 - 6))
  have hb1 : |cfsRamp χ (1 / 2) 1 (v z / R)| ≤ 1 := by
    rw [abs_le]
    simp only [cfsRamp, mem_Icc] at hc1 ⊢
    constructor <;> linarith
  have hb2 : |1 - cfsRamp χ 6 (13 / 2) (‖u z‖ / v z)| ≤ 1 := by
    rw [abs_le]
    simp only [cfsRamp, mem_Icc] at hc2 ⊢
    constructor <;> linarith
  calc _ ≤ ‖cfsRamp χ (1 / 2) 1 (v z / R) • -(deriv (cfsRamp χ 6 (13 / 2))
          (‖u z‖ / v z) • (‖u z‖ • ((-((v z) ^ 2)⁻¹) • v) +
            (v z)⁻¹ • fderiv ℝ (fun w => ‖u w‖) z))‖ +
        ‖(1 - cfsRamp χ 6 (13 / 2) (‖u z‖ / v z)) •
          fderiv ℝ (fun w => cfsRamp χ (1 / 2) 1 (vR w)) z‖ := norm_add_le _ _
    _ ≤ 1 * (30 * P / R) + 1 * (2 * P / R) := by
        rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
        exact add_le_add (mul_le_mul hb1 hQnorm (norm_nonneg _) zero_le_one)
          (mul_le_mul hb2 hA (norm_nonneg _) zero_le_one)
    _ = 32 * P / R := by ring

end Gate

section Row

variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
  {I : Type*} [Fintype I] {E : I → Type*} [∀ i, NormedAddCommGroup (E i)]
  [∀ i, InnerProductSpace ℝ (E i)]

/-- The CFS31 source first cutoff `ψ₁ = χ_{1/2,1}(Σ_i a_i)`. -/
def markerLocalitySourceCutoff (χ : ℝ → ℝ) (R : I → ℝ) (u : ∀ i, H →L[ℝ] E i)
    (v : I → H →L[ℝ] ℝ) (z : H) : ℝ :=
  cfsRamp χ (1 / 2) 1 (∑ i, markerLocalitySourceGate χ (R i) (u i) (v i) z)

/-- CFS31, the source first cutoff on the original map: smooth, `[0,1]`-valued, exact plateau on the `6` core,
closed support localizing the ORIGINAL point to `|η_i| ≤ 13/2 < 7` on `U_i`, and `‖Dψ₁‖ ≤ 80 N P²/ρ ≤ C/ρ` along
`F`. -/
theorem markerLocalitySourceCutoff_row {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ)
    (hχ0 : ∀ t ≤ 0, χ t = 0) (hχ1 : ∀ t, 1 ≤ t → χ t = 1) (hχI : ∀ t, χ t ∈ Icc (0 : ℝ) 1)
    {P : ℝ} (hP1 : 1 ≤ P) (hP : ∀ t, |deriv χ t| ≤ P) (N : ℕ)
    (u : ∀ i, H →L[ℝ] E i) (v : I → H →L[ℝ] ℝ) (hu : ∀ i, ‖u i‖ ≤ 1) (hv : ∀ i, ‖v i‖ ≤ 1)
    {X : Type*} (R : I → ℝ) (hR : ∀ i, 0 < R i) (ρ : X → ℝ) (hρ : ∀ p, 0 < ρ p)
    (U : I → Set X) (η : ∀ i, X → E i) (ζ : I → X → ℝ) (F : X → H)
    (hζU : ∀ i p, p ∉ U i → ζ i p = 0)
    (hblock : ∀ i p, u i (F p) = (R i * ζ i p) • η i p ∧ v i (F p) = R i * ζ i p)
    (hcount : ∀ p, (Finset.univ.filter fun i => 0 < ζ i p).card ≤ N)
    (hcomp : ∀ i p, 0 < ζ i p → 3 / 4 * R i ≤ ρ p ∧ ρ p ≤ 5 / 4 * R i)
    (hplateau : ∀ i p, p ∈ U i → ‖η i p‖ < 6 → ζ i p = 1) :
    ContDiff ℝ ∞ (markerLocalitySourceCutoff χ R u v) ∧
      (∀ z, markerLocalitySourceCutoff χ R u v z ∈ Icc (0 : ℝ) 1) ∧
      (∀ p, (∃ i, p ∈ U i ∧ ‖η i p‖ < 6) → markerLocalitySourceCutoff χ R u v (F p) = 1) ∧
      (∀ p, F p ∈ tsupport (markerLocalitySourceCutoff χ R u v) →
        ∃ i, p ∈ U i ∧ ‖η i p‖ ≤ 13 / 2) ∧
      (∀ p, ‖fderiv ℝ (markerLocalitySourceCutoff χ R u v) (F p)‖ ≤ 80 * N * P ^ 2 / ρ p) ∧
      (∀ p, ‖fderiv ℝ (markerLocalitySourceCutoff χ R u v) (F p)‖ ≤
        10 ^ 4 * ((N : ℝ) + 1) ^ 2 * P ^ 4 / ρ p) := by
  let gate : I → H → ℝ := fun i => markerLocalitySourceGate χ (R i) (u i) (v i)
  have hgsmooth : ∀ i, ContDiff ℝ ∞ (gate i) := fun i =>
    markerLocalitySourceGate_contDiff hχ hχ0 hχ1 (u i) (v i) (hR i)
  have hgmem : ∀ i z, gate i z ∈ Icc (0 : ℝ) 1 := fun i z =>
    markerLocalitySourceGate_mem_Icc hχI (u i) (v i) z
  have hψfun : markerLocalitySourceCutoff χ R u v =
      fun z => cfsRamp χ (1 / 2) 1 (∑ i, gate i z) := rfl
  have hsum : ContDiff ℝ ∞ (fun z => ∑ i, gate i z) :=
    ContDiff.sum fun i _ => hgsmooth i
  -- the derivative bound along `F`
  have hderiv : ∀ p, ‖fderiv ℝ (markerLocalitySourceCutoff χ R u v) (F p)‖ ≤
      80 * N * P ^ 2 / ρ p := by
    intro p
    let S : Finset I := Finset.univ.filter fun i => 0 < ζ i p
    have hρp := hρ p
    have hD0 : ∀ i, i ∉ S → fderiv ℝ (gate i) (F p) = 0 := by
      intro i hi
      have hζ0 : ζ i p ≤ 0 := by
        by_contra hpos
        exact hi (Finset.mem_filter.mpr ⟨Finset.mem_univ i, lt_of_not_ge hpos⟩)
      have hlt : v i (F p) / R i < 1 / 2 := by
        rw [div_lt_iff₀ (hR i), (hblock i p).2]
        nlinarith [hR i]
      rw [(markerLocalitySourceGate_eventually_zero_of_lt hχ0 (u i) (v i) hlt).fderiv_eq,
        fderiv_const_apply]
    have hD1 : ∀ i ∈ S, ‖fderiv ℝ (gate i) (F p)‖ ≤ 40 * P / ρ p := by
      intro i hi
      have hζpos : 0 < ζ i p := (Finset.mem_filter.mp hi).2
      have hc := (hcomp i p hζpos).2
      have hb := norm_fderiv_markerLocalitySourceGate_le hχ hχ0 hχ1 hχI (u i) (v i) hP1 hP
        (hu i) (hv i) (hR i) (F p)
      refine hb.trans ?_
      rw [div_le_div_iff₀ (hR i) hρp]
      nlinarith
    have hgdiff : ∀ i ∈ (Finset.univ : Finset I), DifferentiableAt ℝ (gate i) (F p) := fun i _ =>
      (hgsmooth i).differentiable (by simp) (F p)
    have hfsum : fderiv ℝ (fun w => ∑ i, gate i w) (F p) = ∑ i, fderiv ℝ (gate i) (F p) :=
      fderiv_fun_sum hgdiff
    have hsumnorm : ‖fderiv ℝ (fun w => ∑ i, gate i w) (F p)‖ ≤ N * (40 * P / ρ p) := by
      rw [hfsum]
      calc ‖∑ i, fderiv ℝ (gate i) (F p)‖ ≤ ∑ i, ‖fderiv ℝ (gate i) (F p)‖ := norm_sum_le _ _
        _ = ∑ i ∈ S, ‖fderiv ℝ (gate i) (F p)‖ := by
            refine (Finset.sum_subset (Finset.subset_univ S) fun i _ hi => ?_).symm
            rw [hD0 i hi, norm_zero]
        _ ≤ ∑ _i ∈ S, (40 * P / ρ p) := Finset.sum_le_sum hD1
        _ = S.card * (40 * P / ρ p) := by rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ N * (40 * P / ρ p) := by
            apply mul_le_mul_of_nonneg_right _ (by positivity)
            exact_mod_cast hcount p
    have hdg : DifferentiableAt ℝ (cfsRamp χ (1 / 2) 1) (∑ i, gate i (F p)) :=
      (hasDerivAt_cfsRamp hχ _ _ _).differentiableAt
    have hcomp' := norm_fderiv_comp_real_le (L := fun w => ∑ i, gate i w) (z := F p) hdg
      (hsum.differentiable (by simp) (F p))
      (abs_deriv_cfsRamp_le hχ hP (by norm_num : (1 / 2 : ℝ) < 1) (∑ i, gate i (F p)))
    rw [hψfun]
    calc _ ≤ P / (1 - 1 / 2) * ‖fderiv ℝ (fun w => ∑ i, gate i w) (F p)‖ := hcomp'
      _ ≤ P / (1 - 1 / 2) * (N * (40 * P / ρ p)) :=
          mul_le_mul_of_nonneg_left hsumnorm (by positivity)
      _ = 80 * N * P ^ 2 / ρ p := by ring
  refine ⟨?_, ?_, ?_, ?_, hderiv, ?_⟩
  · rw [hψfun]
    exact (contDiff_cfsRamp hχ _ _).comp hsum
  · intro z
    exact hχI _
  · -- exact plateau on the `6` core
    rintro p ⟨i, hpU, hη⟩
    have hζ1 := hplateau i p hpU hη
    have hRi := hR i
    obtain ⟨hu1, hv1⟩ := hblock i p
    rw [hζ1, mul_one] at hu1 hv1
    have hgate1 : gate i (F p) = 1 := by
      have hA : cfsRamp χ (1 / 2) 1 (v i (F p) / R i) = 1 := by
        refine cfsRamp_eq_one hχ1 (by norm_num) ?_
        rw [hv1, div_self hRi.ne']
      have hB : cfsRamp χ 6 (13 / 2) (‖u i (F p)‖ / v i (F p)) = 0 := by
        refine cfsRamp_eq_zero hχ0 (by norm_num) ?_
        rw [hu1, hv1, norm_smul, Real.norm_eq_abs, abs_of_pos hRi, mul_div_cancel_left₀ _ hRi.ne']
        exact hη.le
      change markerLocalitySourceGate χ (R i) (u i) (v i) (F p) = 1
      simp only [markerLocalitySourceGate, hA, hB, sub_zero, mul_one]
    have hsum1 : 1 ≤ ∑ j, gate j (F p) := by
      calc (1 : ℝ) = gate i (F p) := hgate1.symm
        _ ≤ ∑ j, gate j (F p) :=
          Finset.single_le_sum (fun j _ => (hgmem j (F p)).1) (Finset.mem_univ i)
    rw [hψfun]
    exact cfsRamp_eq_one hχ1 (by norm_num) hsum1
  · -- closed support localizes the original point to `|η_i| ≤ 13/2`
    intro p hsupp
    by_contra hnot0
    have hnot : ∀ i, p ∈ U i → 13 / 2 < ‖η i p‖ := fun i hi =>
      not_le.mp fun h => hnot0 ⟨i, hi, h⟩
    have hzero : ∀ i, gate i =ᶠ[𝓝 (F p)] fun _ => 0 := by
      intro i
      have hRi := hR i
      obtain ⟨hu1, hv1⟩ := hblock i p
      by_cases hv2 : v i (F p) / R i < 1 / 2
      · exact markerLocalitySourceGate_eventually_zero_of_lt hχ0 (u i) (v i) hv2
      rw [not_lt, le_div_iff₀ hRi, hv1] at hv2
      have hζpos : 0 < ζ i p := by nlinarith
      have hpU : p ∈ U i := by
        by_contra hpU
        rw [hζU i p hpU] at hζpos
        exact lt_irrefl 0 hζpos
      have hη := hnot i hpU
      have hvpos : 0 < v i (F p) := by rw [hv1]; positivity
      refine markerLocalitySourceGate_eventually_zero_of_gt hχ1 (u i) (v i) hvpos.ne' ?_
      rw [hu1, hv1, norm_smul, Real.norm_eq_abs, abs_of_pos (mul_pos hRi hζpos),
        mul_div_cancel_left₀ _ (mul_pos hRi hζpos).ne']
      exact hη
    have hsum0 : (fun z => ∑ i, gate i z) =ᶠ[𝓝 (F p)] fun _ => 0 := by
      have hall : ∀ᶠ z in 𝓝 (F p), ∀ i, gate i z = 0 :=
        Filter.eventually_all.mpr fun i => hzero i
      filter_upwards [hall] with z hz
      simp [hz]
    have hψ0 : markerLocalitySourceCutoff χ R u v =ᶠ[𝓝 (F p)] fun _ => 0 := by
      rw [hψfun]
      filter_upwards [hsum0] with z hz
      rw [hz]
      exact cfsRamp_eq_zero hχ0 (by norm_num) (by norm_num)
    exact (notMem_tsupport_iff_eventuallyEq.mpr hψ0) hsupp
  · intro p
    refine (hderiv p).trans ?_
    apply div_le_div_of_nonneg_right _ (hρ p).le
    have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    have hP2 : (1 : ℝ) ≤ P ^ 2 := by nlinarith
    have hP4 : P ^ 2 ≤ P ^ 4 := by nlinarith
    have hN2 : 80 * (N : ℝ) ≤ 10 ^ 4 * ((N : ℝ) + 1) ^ 2 := by nlinarith
    calc 80 * (N : ℝ) * P ^ 2 ≤ 10 ^ 4 * ((N : ℝ) + 1) ^ 2 * P ^ 2 :=
          mul_le_mul_of_nonneg_right hN2 (by positivity)
      _ ≤ 10 ^ 4 * ((N : ℝ) + 1) ^ 2 * P ^ 4 :=
          mul_le_mul_of_nonneg_left hP4 (by positivity)

end Row

end GC.MetricGeometry
