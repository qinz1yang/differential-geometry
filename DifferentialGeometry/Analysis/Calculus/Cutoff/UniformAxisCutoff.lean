import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.Deriv.Support

/-!
# CFS22: a uniform one-axis cutoff with a zero-marker bound

Blueprint `master207B.tex`, CFS22 (`lem:fibration-uniform-axis-cutoff`, lines 3264–3352), in the
explicit finite-index form of external review 39, §5.2. The profile `χ` is any smooth function
with values in `[0, 1]`, `χ = 0` on `(−∞, 0]`, `χ = 1` on `[1, ∞)` and `|χ'| ≤ P`, `P ≥ 1`;
`χ_{a,b}(t) = χ((t − a)/(b − a))` (`cfsRamp`), `q = 1 − χ_{6.2, 6.8}`.

For blocks `u_i : H → E_i`, `v_i : H → ℝ` (continuous linear, norm `≤ 1`; an orthogonal sum of
`E_i ⊕ ℝ` blocks is a special case) the gate is `a_i = χ_{1/2,3/4}(v_i/R_i) q(|u_i|/(ℓ v_i))`
(`cfsAxisGate`; for `v_i ≤ 0` the first factor vanishes) and the cutoff is
`ψ_s = χ_{1/4,1/2}(Σ_i a_i)` (`cfsUniformAxisCutoff`).

* `cfsAxisGate_contDiff`, `norm_fderiv_cfsAxisGate_le`: each gate is smooth with
  `‖D a_i‖ ≤ 30 P / R_i` everywhere.
* `cfs22_row`: with `κ = 1/(1000 (N+1) P²)`, `C₀ = 10⁴ (N+1)² P⁴`, the original blocks
  `(u_i F, v_i F) = (R_i ζ_i η_i, R_i ζ_i)`, at most `N` positive markers at each point, scale
  comparability and `|η_i| ≤ 9ℓ` on positive markers, `ζ_i = 1` where `|η_i| < 6ℓ` on `U_i`,
  `ζ_i = 0` off `U_i`, the FULL perturbation bound `|f − F| ≤ (4κ/5) ρ` and the zero-marker bound
  `ζ_i(p) = 0 ⇒ |v_i(f p)| ≤ R_i/32` (both explicit hypotheses, review §5.2): `ψ_s` is smooth with
  values in `[0, 1]`, equals one at `f(p)` whenever some `|η_i(p)| < 6ℓ` on `U_i`, has
  `f(p) ∈ tsupport ψ_s ⇒ ∃ i, p ∈ U_i ∧ |η_i(p)| < 7ℓ`, and `‖Dψ_s‖ ≤ C₀/ρ(p)` on the whole segment
  from `F(p)` to `f(p)`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology
open scoped ContDiff BigOperators

namespace GC.MetricGeometry

section Ramp

/-- `χ_{a,b}(t) = χ((t − a)/(b − a))`. -/
def cfsRamp (χ : ℝ → ℝ) (a b t : ℝ) : ℝ := χ ((t - a) / (b - a))

variable {χ : ℝ → ℝ}

theorem contDiff_cfsRamp (hχ : ContDiff ℝ ∞ χ) (a b : ℝ) : ContDiff ℝ ∞ (cfsRamp χ a b) :=
  hχ.comp ((contDiff_id.sub contDiff_const).div_const _)

theorem cfsRamp_eq_zero (hχ0 : ∀ t ≤ 0, χ t = 0) {a b t : ℝ} (hab : a < b) (ht : t ≤ a) :
    cfsRamp χ a b t = 0 :=
  hχ0 _ (div_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith))

theorem cfsRamp_eq_one (hχ1 : ∀ t, 1 ≤ t → χ t = 1) {a b t : ℝ} (hab : a < b) (ht : b ≤ t) :
    cfsRamp χ a b t = 1 :=
  hχ1 _ ((one_le_div (by linarith)).mpr (by linarith))

theorem hasDerivAt_cfsRamp (hχ : ContDiff ℝ ∞ χ) (a b t : ℝ) :
    HasDerivAt (cfsRamp χ a b) (deriv χ ((t - a) / (b - a)) * (1 / (b - a))) t := by
  have h1 : HasDerivAt (fun s => (s - a) / (b - a)) (1 / (b - a)) t :=
    ((hasDerivAt_sub_const_iff a).mpr (hasDerivAt_id' t)).div_const (b - a)
  exact ((hχ.differentiable (by simp)).differentiableAt.hasDerivAt).comp t h1

theorem abs_deriv_cfsRamp_le (hχ : ContDiff ℝ ∞ χ) {P : ℝ} (hP : ∀ t, |deriv χ t| ≤ P)
    {a b : ℝ} (hab : a < b) (t : ℝ) : |deriv (cfsRamp χ a b) t| ≤ P / (b - a) := by
  have hpos : 0 < b - a := by linarith
  rw [(hasDerivAt_cfsRamp hχ a b t).deriv, abs_mul, abs_of_pos (one_div_pos.mpr hpos)]
  calc |deriv χ ((t - a) / (b - a))| * (1 / (b - a)) ≤ P * (1 / (b - a)) :=
        mul_le_mul_of_nonneg_right (hP _) (one_div_pos.mpr hpos).le
    _ = P / (b - a) := by ring

end Ramp

/-- Chain rule bound for a real profile after a real-valued map. -/
theorem norm_fderiv_comp_real_le {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {g : ℝ → ℝ} {L : H → ℝ} {z : H} {B : ℝ} (hg : DifferentiableAt ℝ g (L z))
    (hL : DifferentiableAt ℝ L z) (hB : |deriv g (L z)| ≤ B) :
    ‖fderiv ℝ (fun w => g (L w)) z‖ ≤ B * ‖fderiv ℝ L z‖ := by
  have h := (hg.hasDerivAt.comp_hasFDerivAt z hL.hasFDerivAt).fderiv
  rw [show (fun w => g (L w)) = g ∘ L from rfl, h, norm_smul, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_right hB (norm_nonneg _)

section Gate

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]

/-- The axis gate `a(z) = χ_{1/2,3/4}(v z / R) · q(‖u z‖ / (ℓ v z))`, `q = 1 − χ_{6.2,6.8}`. -/
def cfsAxisGate (χ : ℝ → ℝ) (ℓ R : ℝ) (u : H →L[ℝ] E) (v : H →L[ℝ] ℝ) (z : H) : ℝ :=
  cfsRamp χ (1 / 2) (3 / 4) (v z / R) * (1 - cfsRamp χ (31 / 5) (34 / 5) (‖u z‖ / (ℓ * v z)))

variable {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ) (hχ0 : ∀ t ≤ 0, χ t = 0)
  (hχ1 : ∀ t, 1 ≤ t → χ t = 1) (hχI : ∀ t, χ t ∈ Icc (0 : ℝ) 1)
  {ℓ R : ℝ} (u : H →L[ℝ] E) (v : H →L[ℝ] ℝ)

include hχI in
theorem cfsAxisGate_mem_Icc (z : H) : cfsAxisGate χ ℓ R u v z ∈ Icc (0 : ℝ) 1 := by
  have h1 := hχI ((v z / R - 1 / 2) / (3 / 4 - 1 / 2))
  have h2 := hχI ((‖u z‖ / (ℓ * v z) - 31 / 5) / (34 / 5 - 31 / 5))
  simp only [cfsAxisGate, cfsRamp, mem_Icc] at h1 h2 ⊢
  constructor <;> nlinarith

include hχ0 in
theorem cfsAxisGate_eventually_zero_of_lt {z : H} (h : v z / R < 1 / 2) :
    cfsAxisGate χ ℓ R u v =ᶠ[𝓝 z] fun _ => 0 := by
  have hopen : IsOpen {w | v w / R < 1 / 2} :=
    isOpen_lt (v.continuous.div_const R) continuous_const
  filter_upwards [hopen.mem_nhds h] with w hw
  simp only [cfsAxisGate, cfsRamp_eq_zero hχ0 (by norm_num : (1 / 2 : ℝ) < 3 / 4) (le_of_lt hw),
    zero_mul]

theorem continuousAt_axisRatio {z : H} (hv : v z ≠ 0) (hℓ : ℓ ≠ 0) :
    ContinuousAt (fun w => ‖u w‖ / (ℓ * v w)) z :=
  ((continuous_norm.comp u.continuous).continuousAt).div
    ((continuous_const.mul v.continuous).continuousAt) (mul_ne_zero hℓ hv)

include hχ1 in
theorem cfsAxisGate_eventually_zero_of_gt (hℓ : ℓ ≠ 0) {z : H} (hv : v z ≠ 0)
    (hs : 34 / 5 < ‖u z‖ / (ℓ * v z)) : cfsAxisGate χ ℓ R u v =ᶠ[𝓝 z] fun _ => 0 := by
  filter_upwards [(continuousAt_axisRatio u v hv hℓ).eventually (lt_mem_nhds hs)] with w hw
  simp only [cfsAxisGate, cfsRamp_eq_one hχ1 (by norm_num : (31 / 5 : ℝ) < 34 / 5) hw.le,
    sub_self, mul_zero]

include hχ0 in
theorem cfsAxisGate_eventually_eq_of_lt (hℓ : ℓ ≠ 0) {z : H} (hv : v z ≠ 0)
    (hs : ‖u z‖ / (ℓ * v z) < 31 / 5) :
    cfsAxisGate χ ℓ R u v =ᶠ[𝓝 z] fun w => cfsRamp χ (1 / 2) (3 / 4) (v w / R) := by
  filter_upwards [(continuousAt_axisRatio u v hv hℓ).eventually (gt_mem_nhds hs)] with w hw
  simp only [cfsAxisGate, cfsRamp_eq_zero hχ0 (by norm_num : (31 / 5 : ℝ) < 34 / 5) hw.le,
    sub_zero, mul_one]

include hχ hχ0 hχ1 in
theorem cfsAxisGate_contDiffAt (hR : 0 < R) (hℓ : 0 < ℓ) (z : H) :
    ContDiffAt ℝ ∞ (cfsAxisGate χ ℓ R u v) z := by
  by_cases h1 : v z / R < 1 / 2
  · exact contDiffAt_const.congr_of_eventuallyEq
      (cfsAxisGate_eventually_zero_of_lt hχ0 u v h1)
  have hvpos : 0 < v z := by
    rw [not_lt, le_div_iff₀ hR] at h1
    linarith
  have hg1 : ContDiff ℝ ∞ (fun w => cfsRamp χ (1 / 2) (3 / 4) (v w / R)) :=
    (contDiff_cfsRamp hχ _ _).comp (v.contDiff.div_const R)
  by_cases h2 : ‖u z‖ / (ℓ * v z) < 31 / 5
  · exact hg1.contDiffAt.congr_of_eventuallyEq
      (cfsAxisGate_eventually_eq_of_lt hχ0 u v hℓ.ne' hvpos.ne' h2)
  by_cases h3 : 34 / 5 < ‖u z‖ / (ℓ * v z)
  · exact contDiffAt_const.congr_of_eventuallyEq
      (cfsAxisGate_eventually_zero_of_gt hχ1 u v hℓ.ne' hvpos.ne' h3)
  have hu0 : u z ≠ 0 := by
    intro h0
    rw [h0, norm_zero, zero_div] at h2
    norm_num at h2
  have hs : ContDiffAt ℝ ∞ (fun w => ‖u w‖ / (ℓ * v w)) z :=
    ((contDiffAt_norm ℝ hu0).comp z u.contDiff.contDiffAt).div
      (contDiffAt_const.mul v.contDiff.contDiffAt) (by positivity)
  exact hg1.contDiffAt.mul (contDiffAt_const.sub ((contDiff_cfsRamp hχ _ _).contDiffAt.comp z hs))

include hχ hχ0 hχ1 in
theorem cfsAxisGate_contDiff (hR : 0 < R) (hℓ : 0 < ℓ) : ContDiff ℝ ∞ (cfsAxisGate χ ℓ R u v) :=
  contDiff_iff_contDiffAt.mpr (cfsAxisGate_contDiffAt hχ hχ0 hχ1 u v hR hℓ)

include hχ hχ0 hχ1 hχI in
/-- `‖D a‖ ≤ 30 P / R` everywhere. -/
theorem norm_fderiv_cfsAxisGate_le {P : ℝ} (hP1 : 1 ≤ P) (hP : ∀ t, |deriv χ t| ≤ P)
    (hu : ‖u‖ ≤ 1) (hv : ‖v‖ ≤ 1) (hR : 0 < R) (hℓ : 1 ≤ ℓ) (z : H) :
    ‖fderiv ℝ (cfsAxisGate χ ℓ R u v) z‖ ≤ 30 * P / R := by
  have hbound0 : (0 : ℝ) ≤ 30 * P / R := by positivity
  have hℓ0 : 0 < ℓ := by linarith
  by_cases h1 : v z / R < 1 / 2
  · rw [(cfsAxisGate_eventually_zero_of_lt hχ0 u v h1).fderiv_eq, fderiv_const_apply,
      norm_zero]
    exact hbound0
  have hvR : R / 2 ≤ v z := by
    rw [not_lt, le_div_iff₀ hR] at h1
    linarith
  have hvpos : 0 < v z := by linarith
  -- the first factor through the linear map `R⁻¹ • v`
  set vR : H →L[ℝ] ℝ := R⁻¹ • v with hvRdef
  have hvRapply : ∀ w, v w / R = vR w := fun w => by
    simp [vR, div_eq_inv_mul]
  have hvRnorm : ‖vR‖ ≤ 1 / R := by
    calc ‖vR‖ ≤ ‖R⁻¹‖ * ‖v‖ := ContinuousLinearMap.opNorm_smul_le _ _
      _ ≤ R⁻¹ * 1 := by
          rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hR)]
          exact mul_le_mul_of_nonneg_left hv (inv_pos.mpr hR).le
      _ = 1 / R := by ring
  have hdg1 : ∀ t, DifferentiableAt ℝ (cfsRamp χ (1 / 2) (3 / 4)) t := fun t =>
    (hasDerivAt_cfsRamp hχ _ _ t).differentiableAt
  have hA : ‖fderiv ℝ (fun w => cfsRamp χ (1 / 2) (3 / 4) (vR w)) z‖ ≤ 4 * P / R := by
    have h := norm_fderiv_comp_real_le (hdg1 (vR z)) vR.differentiableAt
      (abs_deriv_cfsRamp_le hχ hP (by norm_num : (1 / 2 : ℝ) < 3 / 4) (vR z))
    rw [vR.fderiv] at h
    calc _ ≤ P / (3 / 4 - 1 / 2) * ‖vR‖ := h
      _ ≤ P / (3 / 4 - 1 / 2) * (1 / R) :=
          mul_le_mul_of_nonneg_left hvRnorm (by positivity)
      _ = 4 * P / R := by ring
  by_cases h2 : ‖u z‖ / (ℓ * v z) < 31 / 5
  · have heq := cfsAxisGate_eventually_eq_of_lt hχ0 (R := R) u v hℓ0.ne' hvpos.ne' h2
    rw [heq.fderiv_eq]
    simp only [hvRapply]
    exact hA.trans (by
      apply div_le_div_of_nonneg_right _ hR.le
      linarith)
  by_cases h3 : 34 / 5 < ‖u z‖ / (ℓ * v z)
  · rw [(cfsAxisGate_eventually_zero_of_gt hχ1 u v hℓ0.ne' hvpos.ne' h3).fderiv_eq,
      fderiv_const_apply, norm_zero]
    exact hbound0
  rw [not_lt] at h2 h3
  have hu0 : u z ≠ 0 := by
    intro h0
    rw [h0, norm_zero, zero_div] at h2
    norm_num at h2
  -- the ratio `s = ‖u‖ · (ℓ v)⁻¹`
  have hd : ℓ * v z ≠ 0 := by positivity
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
  have hD : HasFDerivAt (fun w => ℓ * v w) (ℓ • v) z := v.hasFDerivAt.const_mul ℓ
  have hIv : HasFDerivAt (fun w => (ℓ * v w)⁻¹) ((-((ℓ * v z) ^ 2)⁻¹) • (ℓ • v)) z :=
    (hasDerivAt_inv hd).comp_hasFDerivAt z hD
  have hs : HasFDerivAt (fun w => ‖u w‖ * (ℓ * v w)⁻¹)
      (‖u z‖ • ((-((ℓ * v z) ^ 2)⁻¹) • (ℓ • v)) + (ℓ * v z)⁻¹ • fderiv ℝ (fun w => ‖u w‖) z)
      z := hNdiff.hasFDerivAt.mul hIv
  have hsnorm : ‖‖u z‖ • ((-((ℓ * v z) ^ 2)⁻¹) • (ℓ • v)) +
      (ℓ * v z)⁻¹ • fderiv ℝ (fun w => ‖u w‖) z‖ ≤ 78 / 5 / R := by
    have hsz : ‖u z‖ ≤ 34 / 5 * (ℓ * v z) := (div_le_iff₀ (by positivity)).mp h3
    have e1 : ‖‖u z‖ • ((-((ℓ * v z) ^ 2)⁻¹) • (ℓ • v))‖ ≤ ‖u z‖ * (((ℓ * v z) ^ 2)⁻¹ * ℓ) := by
      rw [norm_smul, norm_smul, norm_smul, norm_neg, Real.norm_eq_abs, Real.norm_eq_abs,
        Real.norm_eq_abs, abs_norm, abs_of_pos (by positivity : (0 : ℝ) < ((ℓ * v z) ^ 2)⁻¹),
        abs_of_pos hℓ0]
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      calc ((ℓ * v z) ^ 2)⁻¹ * (ℓ * ‖v‖) ≤ ((ℓ * v z) ^ 2)⁻¹ * (ℓ * 1) := by gcongr
        _ = _ := by ring
    have e2 : ‖(ℓ * v z)⁻¹ • fderiv ℝ (fun w => ‖u w‖) z‖ ≤ (ℓ * v z)⁻¹ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity)]
      calc (ℓ * v z)⁻¹ * ‖fderiv ℝ (fun w => ‖u w‖) z‖ ≤ (ℓ * v z)⁻¹ * 1 := by gcongr
        _ = _ := mul_one _
    have e3 : ‖u z‖ * (((ℓ * v z) ^ 2)⁻¹ * ℓ) ≤ 34 / 5 / v z := by
      calc ‖u z‖ * (((ℓ * v z) ^ 2)⁻¹ * ℓ) ≤ 34 / 5 * (ℓ * v z) * (((ℓ * v z) ^ 2)⁻¹ * ℓ) := by
            gcongr
        _ = 34 / 5 / v z := by field_simp
    have e4 : (ℓ * v z)⁻¹ ≤ 1 / v z := by
      rw [one_div]
      exact inv_anti₀ hvpos (by nlinarith)
    have e5 : 34 / 5 / v z + 1 / v z ≤ 78 / 5 / R := by
      rw [← add_div, div_le_div_iff₀ hvpos hR]
      nlinarith
    calc _ ≤ ‖‖u z‖ • ((-((ℓ * v z) ^ 2)⁻¹) • (ℓ • v))‖ +
          ‖(ℓ * v z)⁻¹ • fderiv ℝ (fun w => ‖u w‖) z‖ := norm_add_le _ _
      _ ≤ 34 / 5 / v z + 1 / v z := add_le_add (e1.trans e3) (e2.trans e4)
      _ ≤ 78 / 5 / R := e5
  -- the second factor `1 − χ_{6.2,6.8}(s)`
  have hdq : ∀ t, DifferentiableAt ℝ (cfsRamp χ (31 / 5) (34 / 5)) t := fun t =>
    (hasDerivAt_cfsRamp hχ _ _ t).differentiableAt
  have hsfun : (fun w => ‖u w‖ / (ℓ * v w)) = fun w => ‖u w‖ * (ℓ * v w)⁻¹ := by
    funext w
    rw [div_eq_mul_inv]
  have hQ : HasFDerivAt (fun w => 1 - cfsRamp χ (31 / 5) (34 / 5) (‖u w‖ / (ℓ * v w)))
      (-(deriv (cfsRamp χ (31 / 5) (34 / 5)) (‖u z‖ / (ℓ * v z)) •
        (‖u z‖ • ((-((ℓ * v z) ^ 2)⁻¹) • (ℓ • v)) +
          (ℓ * v z)⁻¹ • fderiv ℝ (fun w => ‖u w‖) z))) z := by
    have hs' : HasFDerivAt (fun w => ‖u w‖ / (ℓ * v w))
        (‖u z‖ • ((-((ℓ * v z) ^ 2)⁻¹) • (ℓ • v)) +
          (ℓ * v z)⁻¹ • fderiv ℝ (fun w => ‖u w‖) z) z := by
      rw [hsfun]
      exact hs
    have hcomp := (hdq (‖u z‖ / (ℓ * v z))).hasDerivAt.comp_hasFDerivAt z hs'
    exact hcomp.const_sub 1
  have hQnorm : ‖-(deriv (cfsRamp χ (31 / 5) (34 / 5)) (‖u z‖ / (ℓ * v z)) •
      (‖u z‖ • ((-((ℓ * v z) ^ 2)⁻¹) • (ℓ • v)) +
        (ℓ * v z)⁻¹ • fderiv ℝ (fun w => ‖u w‖) z))‖ ≤ 26 * P / R := by
    rw [norm_neg, norm_smul, Real.norm_eq_abs]
    have hq := abs_deriv_cfsRamp_le hχ hP (by norm_num : (31 / 5 : ℝ) < 34 / 5)
      (‖u z‖ / (ℓ * v z))
    calc _ ≤ P / (34 / 5 - 31 / 5) * (78 / 5 / R) :=
          mul_le_mul hq hsnorm (norm_nonneg _) (by positivity)
      _ = 26 * P / R := by ring
  have hAfun : HasFDerivAt (fun w => cfsRamp χ (1 / 2) (3 / 4) (v w / R))
      (fderiv ℝ (fun w => cfsRamp χ (1 / 2) (3 / 4) (vR w)) z) z := by
    simp only [hvRapply]
    exact ((hdg1 (vR z)).comp z vR.differentiableAt).hasFDerivAt
  have hgate := hAfun.fun_mul hQ
  have hgfun : cfsAxisGate χ ℓ R u v = fun w => cfsRamp χ (1 / 2) (3 / 4) (v w / R) *
      (1 - cfsRamp χ (31 / 5) (34 / 5) (‖u w‖ / (ℓ * v w))) := rfl
  rw [hgfun, hgate.fderiv]
  have hc1 := hχI ((v z / R - 1 / 2) / (3 / 4 - 1 / 2))
  have hc2 := hχI ((‖u z‖ / (ℓ * v z) - 31 / 5) / (34 / 5 - 31 / 5))
  have hb1 : |cfsRamp χ (1 / 2) (3 / 4) (v z / R)| ≤ 1 := by
    rw [abs_le]
    simp only [cfsRamp, mem_Icc] at hc1 ⊢
    constructor <;> linarith
  have hb2 : |1 - cfsRamp χ (31 / 5) (34 / 5) (‖u z‖ / (ℓ * v z))| ≤ 1 := by
    rw [abs_le]
    simp only [cfsRamp, mem_Icc] at hc2 ⊢
    constructor <;> linarith
  calc _ ≤ ‖cfsRamp χ (1 / 2) (3 / 4) (v z / R) • -(deriv (cfsRamp χ (31 / 5) (34 / 5))
          (‖u z‖ / (ℓ * v z)) • (‖u z‖ • ((-((ℓ * v z) ^ 2)⁻¹) • (ℓ • v)) +
            (ℓ * v z)⁻¹ • fderiv ℝ (fun w => ‖u w‖) z))‖ +
        ‖(1 - cfsRamp χ (31 / 5) (34 / 5) (‖u z‖ / (ℓ * v z))) •
          fderiv ℝ (fun w => cfsRamp χ (1 / 2) (3 / 4) (vR w)) z‖ := norm_add_le _ _
    _ ≤ 1 * (26 * P / R) + 1 * (4 * P / R) := by
        rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
        exact add_le_add (mul_le_mul hb1 hQnorm (norm_nonneg _) zero_le_one)
          (mul_le_mul hb2 hA (norm_nonneg _) zero_le_one)
    _ = 30 * P / R := by ring

end Gate

section Row

variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
  {I : Type*} [Fintype I] {E : I → Type*} [∀ i, NormedAddCommGroup (E i)]
  [∀ i, InnerProductSpace ℝ (E i)]

/-- The cutoff `ψ_s = χ_{1/4,1/2}(Σ_i a_i)` of CFS22. -/
def cfsUniformAxisCutoff (χ : ℝ → ℝ) (ℓ : ℝ) (R : I → ℝ) (u : ∀ i, H →L[ℝ] E i)
    (v : I → H →L[ℝ] ℝ) (z : H) : ℝ :=
  cfsRamp χ (1 / 4) (1 / 2) (∑ i, cfsAxisGate χ ℓ (R i) (u i) (v i) z)

/-- CFS22 (`lem:fibration-uniform-axis-cutoff`) in the explicit form of review 39, §5.2. -/
theorem cfs22_row {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ) (hχ0 : ∀ t ≤ 0, χ t = 0)
    (hχ1 : ∀ t, 1 ≤ t → χ t = 1) (hχI : ∀ t, χ t ∈ Icc (0 : ℝ) 1) {P : ℝ} (hP1 : 1 ≤ P)
    (hP : ∀ t, |deriv χ t| ≤ P) (N : ℕ)
    (u : ∀ i, H →L[ℝ] E i) (v : I → H →L[ℝ] ℝ) (hu : ∀ i, ‖u i‖ ≤ 1) (hv : ∀ i, ‖v i‖ ≤ 1)
    {X : Type*} {ℓ : ℝ} (hℓ : 1 ≤ ℓ) (R : I → ℝ) (hR : ∀ i, 0 < R i) (ρ : X → ℝ)
    (hρ : ∀ p, 0 < ρ p) (U : I → Set X) (η : ∀ i, X → E i) (ζ : I → X → ℝ)
    (hζI : ∀ i p, ζ i p ∈ Icc (0 : ℝ) 1) (F f : X → H)
    (hζU : ∀ i p, p ∉ U i → ζ i p = 0)
    (hblock : ∀ i p, u i (F p) = (R i * ζ i p) • η i p ∧ v i (F p) = R i * ζ i p)
    (hcount : ∀ p, (Finset.univ.filter fun i => 0 < ζ i p).card ≤ N)
    (hcomp : ∀ i p, 0 < ζ i p → 3 / 4 * R i ≤ ρ p ∧ ρ p ≤ 5 / 4 * R i ∧ ‖η i p‖ ≤ 9 * ℓ)
    (hplateau : ∀ i p, p ∈ U i → ‖η i p‖ < 6 * ℓ → ζ i p = 1)
    (hpert : ∀ p, ‖f p - F p‖ ≤ 4 * (1 / (1000 * ((N : ℝ) + 1) * P ^ 2)) / 5 * ρ p)
    (hZM : ∀ i p, ζ i p = 0 → |v i (f p)| ≤ R i / 32) :
    ContDiff ℝ ∞ (cfsUniformAxisCutoff χ ℓ R u v) ∧
      (∀ z, cfsUniformAxisCutoff χ ℓ R u v z ∈ Icc (0 : ℝ) 1) ∧
      (∀ p, (∃ i, p ∈ U i ∧ ‖η i p‖ < 6 * ℓ) → cfsUniformAxisCutoff χ ℓ R u v (f p) = 1) ∧
      (∀ p, f p ∈ tsupport (cfsUniformAxisCutoff χ ℓ R u v) →
        ∃ i, p ∈ U i ∧ ‖η i p‖ < 7 * ℓ) ∧
      (∀ p, ∀ t ∈ Icc (0 : ℝ) 1,
        ‖fderiv ℝ (cfsUniformAxisCutoff χ ℓ R u v) ((1 - t) • F p + t • f p)‖ ≤
          10 ^ 4 * ((N : ℝ) + 1) ^ 2 * P ^ 4 / ρ p) := by
  set κ : ℝ := 1 / (1000 * ((N : ℝ) + 1) * P ^ 2) with hκdef
  have hNP : 1 ≤ ((N : ℝ) + 1) * P ^ 2 := by
    have h1 : (1 : ℝ) ≤ (N : ℝ) + 1 := by linarith [(Nat.cast_nonneg N : (0 : ℝ) ≤ N)]
    have h2 : (1 : ℝ) ≤ P ^ 2 := by nlinarith
    nlinarith
  have hκpos : 0 < κ := by positivity
  have hκsmall : κ ≤ 1 / 1000 := by
    rw [hκdef, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  have hℓ0 : 0 < ℓ := by linarith
  let gate : I → H → ℝ := fun i => cfsAxisGate χ ℓ (R i) (u i) (v i)
  have hgsmooth : ∀ i, ContDiff ℝ ∞ (gate i) := fun i =>
    cfsAxisGate_contDiff hχ hχ0 hχ1 (u i) (v i) (hR i) hℓ0
  have hgmem : ∀ i z, gate i z ∈ Icc (0 : ℝ) 1 := fun i z => cfsAxisGate_mem_Icc hχI (u i) (v i) z
  have hψfun : cfsUniformAxisCutoff χ ℓ R u v =
      fun z => cfsRamp χ (1 / 4) (1 / 2) (∑ i, gate i z) := rfl
  have hsum : ContDiff ℝ ∞ (fun z => ∑ i, gate i z) :=
    ContDiff.sum fun i _ => hgsmooth i
  -- block estimates for the perturbed map at a positive marker
  have hpertR : ∀ i p, 0 < ζ i p → ‖f p - F p‖ ≤ κ * R i := by
    intro i p hζ
    have hc := (hcomp i p hζ).2.1
    calc ‖f p - F p‖ ≤ 4 * κ / 5 * ρ p := hpert p
      _ ≤ 4 * κ / 5 * (5 / 4 * R i) := by gcongr
      _ = κ * R i := by ring
  have hvblock : ∀ i p, |v i (f p) - v i (F p)| ≤ ‖f p - F p‖ := by
    intro i p
    rw [← map_sub]
    calc |v i (f p - F p)| = ‖v i (f p - F p)‖ := (Real.norm_eq_abs _).symm
      _ ≤ ‖v i‖ * ‖f p - F p‖ := (v i).le_opNorm _
      _ ≤ 1 * ‖f p - F p‖ := mul_le_mul_of_nonneg_right (hv i) (norm_nonneg _)
      _ = ‖f p - F p‖ := one_mul _
  have hublock : ∀ i p, ‖u i (f p) - u i (F p)‖ ≤ ‖f p - F p‖ := by
    intro i p
    rw [← map_sub]
    calc ‖u i (f p - F p)‖ ≤ ‖u i‖ * ‖f p - F p‖ := (u i).le_opNorm _
      _ ≤ 1 * ‖f p - F p‖ := mul_le_mul_of_nonneg_right (hu i) (norm_nonneg _)
      _ = ‖f p - F p‖ := one_mul _
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- smoothness
    rw [hψfun]
    exact (contDiff_cfsRamp hχ _ _).comp hsum
  · -- values
    intro z
    exact hχI _
  · -- plateau on the `6ℓ` core
    rintro p ⟨i, hpU, hη⟩
    have hζ1 := hplateau i p hpU hη
    have hζpos : 0 < ζ i p := by rw [hζ1]; norm_num
    have hRi := hR i
    obtain ⟨hu1, hv1⟩ := hblock i p
    rw [hζ1, mul_one] at hu1 hv1
    have hpe := hpertR i p hζpos
    have hvf : R i * (1 - κ) ≤ v i (f p) := by
      have := (abs_le.mp ((hvblock i p).trans hpe)).1
      rw [hv1] at this
      nlinarith
    have hvpos : 0 < v i (f p) := by
      have : 0 < R i * (1 - κ) := mul_pos hRi (by linarith)
      linarith
    have huf : ‖u i (f p)‖ ≤ R i * ‖η i p‖ + κ * R i := by
      have h1 := norm_le_insert' (u i (f p)) (u i (F p))
      have h2 := (hublock i p).trans hpe
      rw [hu1] at h1 h2
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hRi] at h1
      linarith
    have hgate1 : gate i (f p) = 1 := by
      have hA : cfsRamp χ (1 / 2) (3 / 4) (v i (f p) / R i) = 1 := by
        refine cfsRamp_eq_one hχ1 (by norm_num) ?_
        rw [le_div_iff₀ hRi]
        nlinarith
      have hB : cfsRamp χ (31 / 5) (34 / 5) (‖u i (f p)‖ / (ℓ * v i (f p))) = 0 := by
        refine cfsRamp_eq_zero hχ0 (by norm_num) ?_
        rw [div_le_iff₀ (by positivity)]
        have hη' : ‖η i p‖ ≤ 6 * ℓ := hη.le
        have h1 : R i * ‖η i p‖ ≤ R i * (6 * ℓ) := mul_le_mul_of_nonneg_left hη' hRi.le
        have h2 : ℓ * (R i * (1 - κ)) ≤ ℓ * v i (f p) := mul_le_mul_of_nonneg_left hvf hℓ0.le
        have hℓR : 0 < ℓ * R i := mul_pos hℓ0 hRi
        have k1 : ℓ * R i * κ ≤ ℓ * R i * (1 / 1000) :=
          mul_le_mul_of_nonneg_left hκsmall hℓR.le
        have k2 : 1 * (κ * R i) ≤ ℓ * (κ * R i) :=
          mul_le_mul_of_nonneg_right hℓ (mul_nonneg hκpos.le hRi.le)
        linarith
      change cfsAxisGate χ ℓ (R i) (u i) (v i) (f p) = 1
      simp only [cfsAxisGate, hA, hB, sub_zero, mul_one]
    have hsum1 : 1 ≤ ∑ j, gate j (f p) := by
      calc (1 : ℝ) = gate i (f p) := hgate1.symm
        _ ≤ ∑ j, gate j (f p) :=
          Finset.single_le_sum (fun j _ => (hgmem j (f p)).1) (Finset.mem_univ i)
    rw [hψfun]
    exact cfsRamp_eq_one hχ1 (by norm_num) (by linarith)
  · -- closed support inside the `7ℓ` set
    intro p hsupp
    by_contra hnot0
    have hnot : ∀ i, p ∈ U i → 7 * ℓ ≤ ‖η i p‖ := fun i hi =>
      not_lt.mp fun h => hnot0 ⟨i, hi, h⟩
    have hzero : ∀ i, gate i =ᶠ[𝓝 (f p)] fun _ => 0 := by
      intro i
      have hRi := hR i
      by_cases hζ0 : ζ i p = 0
      · refine cfsAxisGate_eventually_zero_of_lt hχ0 (u i) (v i) ?_
        have h := hZM i p hζ0
        rw [div_lt_iff₀ hRi]
        linarith [(abs_le.mp h).2]
      have hζpos : 0 < ζ i p := lt_of_le_of_ne (hζI i p).1 (Ne.symm hζ0)
      have hpU : p ∈ U i := by
        by_contra hpU
        exact hζ0 (hζU i p hpU)
      have hη7 : 7 * ℓ ≤ ‖η i p‖ := hnot i hpU
      obtain ⟨hu1, hv1⟩ := hblock i p
      have hpe := hpertR i p hζpos
      by_cases hv2 : v i (f p) / R i < 1 / 2
      · exact cfsAxisGate_eventually_zero_of_lt hχ0 (u i) (v i) hv2
      rw [not_lt, le_div_iff₀ hRi] at hv2
      have hvup : v i (f p) ≤ R i * ζ i p + κ * R i := by
        have := (abs_le.mp ((hvblock i p).trans hpe)).2
        rw [hv1] at this
        linarith
      have hvpos : 0 < v i (f p) := by linarith
      have hζlow : 1 / 2 - κ ≤ ζ i p := by
        have : R i * (1 / 2) ≤ R i * (ζ i p + κ) := by nlinarith
        have := le_of_mul_le_mul_left this hRi
        linarith
      have hulow : R i * ζ i p * ‖η i p‖ - κ * R i ≤ ‖u i (f p)‖ := by
        have h1 := norm_sub_norm_le (u i (F p)) (u i (F p) - u i (f p))
        have h2 := (hublock i p).trans hpe
        rw [sub_sub_cancel, norm_sub_rev] at h1
        rw [hu1] at h1 h2
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hRi.le hζpos.le)] at h1
        linarith
      refine cfsAxisGate_eventually_zero_of_gt hχ1 (u i) (v i) hℓ0.ne' hvpos.ne' ?_
      rw [lt_div_iff₀ (by positivity)]
      have h1 : R i * ζ i p * (7 * ℓ) ≤ R i * ζ i p * ‖η i p‖ :=
        mul_le_mul_of_nonneg_left hη7 (mul_nonneg hRi.le hζpos.le)
      have h2 : ℓ * v i (f p) ≤ ℓ * (R i * ζ i p + κ * R i) :=
        mul_le_mul_of_nonneg_left hvup hℓ0.le
      have hℓR : 0 < ℓ * R i := mul_pos hℓ0 hRi
      have f4 : ℓ * R i * (1 / 2 - κ) ≤ ℓ * R i * ζ i p := mul_le_mul_of_nonneg_left hζlow hℓR.le
      have f5 : 1 * (κ * R i) ≤ ℓ * (κ * R i) :=
        mul_le_mul_of_nonneg_right hℓ (mul_nonneg hκpos.le hRi.le)
      have f6 : ℓ * R i * κ ≤ ℓ * R i * (1 / 1000) := mul_le_mul_of_nonneg_left hκsmall hℓR.le
      linarith
    have hsum0 : (fun z => ∑ i, gate i z) =ᶠ[𝓝 (f p)] fun _ => 0 := by
      have hall : ∀ᶠ z in 𝓝 (f p), ∀ i, gate i z = 0 :=
        Filter.eventually_all.mpr fun i => hzero i
      filter_upwards [hall] with z hz
      simp [hz]
    have hψ0 : cfsUniformAxisCutoff χ ℓ R u v =ᶠ[𝓝 (f p)] fun _ => 0 := by
      rw [hψfun]
      filter_upwards [hsum0] with z hz
      rw [hz]
      exact cfsRamp_eq_zero hχ0 (by norm_num) (by norm_num)
    exact (notMem_tsupport_iff_eventuallyEq.mpr hψ0) hsupp
  · -- derivative bound along the segment
    intro p t ht
    set z := (1 - t) • F p + t • f p with hz
    let S : Finset I := Finset.univ.filter fun i => 0 < ζ i p
    have hρp := hρ p
    have hD0 : ∀ i, i ∉ S → fderiv ℝ (gate i) z = 0 := by
      intro i hi
      have hζ0 : ζ i p = 0 := by
        have hle := (hζI i p).1
        by_contra hne
        exact hi (Finset.mem_filter.mpr ⟨Finset.mem_univ i, lt_of_le_of_ne hle (Ne.symm hne)⟩)
      have hvz : v i z = t * v i (f p) := by
        rw [hz, map_add, map_smul, map_smul, (hblock i p).2, hζ0, mul_zero, smul_zero,
          zero_add, smul_eq_mul]
      have hlt : v i z / R i < 1 / 2 := by
        rw [div_lt_iff₀ (hR i), hvz]
        have h := hZM i p hζ0
        have h1 : t * v i (f p) ≤ t * |v i (f p)| := mul_le_mul_of_nonneg_left (le_abs_self _) ht.1
        have h2 : t * |v i (f p)| ≤ 1 * (R i / 32) := mul_le_mul ht.2 h (abs_nonneg _) zero_le_one
        nlinarith [hR i]
      rw [(cfsAxisGate_eventually_zero_of_lt hχ0 (u i) (v i) hlt).fderiv_eq, fderiv_const_apply]
    have hD1 : ∀ i ∈ S, ‖fderiv ℝ (gate i) z‖ ≤ 75 / 2 * P / ρ p := by
      intro i hi
      have hζpos : 0 < ζ i p := (Finset.mem_filter.mp hi).2
      have hc := (hcomp i p hζpos).2.1
      have hb := norm_fderiv_cfsAxisGate_le hχ hχ0 hχ1 hχI (u i) (v i) hP1 hP (hu i) (hv i) (hR i)
        hℓ z
      refine hb.trans ?_
      rw [div_le_div_iff₀ (hR i) hρp]
      nlinarith
    have hgdiff : ∀ i ∈ (Finset.univ : Finset I), DifferentiableAt ℝ (gate i) z := fun i _ =>
      (hgsmooth i).differentiable (by simp) z
    have hfsum : fderiv ℝ (fun w => ∑ i, gate i w) z = ∑ i, fderiv ℝ (gate i) z :=
      fderiv_fun_sum hgdiff
    have hsumnorm : ‖fderiv ℝ (fun w => ∑ i, gate i w) z‖ ≤ N * (75 / 2 * P / ρ p) := by
      rw [hfsum]
      calc ‖∑ i, fderiv ℝ (gate i) z‖ ≤ ∑ i, ‖fderiv ℝ (gate i) z‖ := norm_sum_le _ _
        _ = ∑ i ∈ S, ‖fderiv ℝ (gate i) z‖ := by
            refine (Finset.sum_subset (Finset.subset_univ S) fun i _ hi => ?_).symm
            rw [hD0 i hi, norm_zero]
        _ ≤ ∑ _i ∈ S, (75 / 2 * P / ρ p) := Finset.sum_le_sum hD1
        _ = S.card * (75 / 2 * P / ρ p) := by rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ N * (75 / 2 * P / ρ p) := by
            apply mul_le_mul_of_nonneg_right _ (by positivity)
            exact_mod_cast hcount p
    have hdg : DifferentiableAt ℝ (cfsRamp χ (1 / 4) (1 / 2)) (∑ i, gate i z) :=
      (hasDerivAt_cfsRamp hχ _ _ _).differentiableAt
    have hcomp' := norm_fderiv_comp_real_le (L := fun w => ∑ i, gate i w) (z := z) hdg
      (hsum.differentiable (by simp) z)
      (abs_deriv_cfsRamp_le hχ hP (by norm_num : (1 / 4 : ℝ) < 1 / 2) (∑ i, gate i z))
    rw [hψfun]
    calc _ ≤ P / (1 / 2 - 1 / 4) * ‖fderiv ℝ (fun w => ∑ i, gate i w) z‖ := hcomp'
      _ ≤ P / (1 / 2 - 1 / 4) * (N * (75 / 2 * P / ρ p)) :=
          mul_le_mul_of_nonneg_left hsumnorm (by positivity)
      _ = 150 * N * P ^ 2 / ρ p := by ring
      _ ≤ 10 ^ 4 * ((N : ℝ) + 1) ^ 2 * P ^ 4 / ρ p := by
          apply div_le_div_of_nonneg_right _ hρp.le
          have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
          have hP2 : (1 : ℝ) ≤ P ^ 2 := by nlinarith
          nlinarith [mul_le_mul hP2 hP2 zero_le_one (by positivity)]

end Row

end GC.MetricGeometry
