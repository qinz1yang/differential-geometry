import DifferentialGeometry.Analysis.Calculus.Cutoff.UniformAxisCutoff
import Mathlib.Analysis.Calculus.MeanValue

/-!
# CFS23: a uniform buffered edge cutoff

Blueprint `master207B.tex`, CFS23 (`prop:fibration-uniform-edge-cutoff`, lines 3353–3476), in the
explicit finite-index form of external review 39, §5.3. It reuses the CFS22 kernel
(`UniformAxisCutoff.lean`): the ramps `χ_{a,b} = cfsRamp χ a b` and the axis gates
`a_i = cfsAxisGate χ Δ R_i u_i v_i`.

New objects (all on an arbitrary real normed space `H`):
* `cfsTrunc`: the truncation `T(s) = s · χ_{1/16,1/8}(s)`;
* `cfsAxisRatioFactor`: the ratio factor `q(‖u‖/(ℓ v)) = 1 − χ_{6.2,6.8}(‖u‖/(ℓ v))`;
* `cfsEdgeGate`: `B_E = χ_{1/8,1/4}(x'' / x_ρ) · q(‖x'‖/(Δ x''))`;
* `cfsTruncAggregate`: `Z = χ_{1/2,1}(Σ_i T(v_i / R_i))`;
* `cfsEdgeDefect`: `d_i = (v_i / R_i) Z − x'' / x_ρ`;
* `cfsBufferedEdgeCutoff`: `ψ_e = χ_{1/4,1/2}(Σ_i a_i (B_E + χ_{1/8,1/4}(d_i)))`.

Main theorem `cfs23_row`: under the CFS22 data minus its one-axis plateau hypothesis, plus the
scale functional `x_ρ` with `x_ρ(F p) = ρ(p)`, the variable edge block `(x', x'')` with
`(‖x'(F p)‖, x''(F p)) = (ρ t z₀, ρ z₀)` on `D = ⋃ U_i`, `z₀ = h(t/Δ) χ_{1/2,1}(Σ ζ_i)`, and the
joint edge identity `ζ_i = 1 − χ_{8,9}(t/Δ)` where `|η_i| < 8Δ` on `U_i`, the cutoff `ψ_e` is
smooth on `O = {x_ρ > 0}` with values in `[0, 1]`, equals one at `f(p)` on the joint inner region
`{|η_i| < 6Δ, t < 6Δ}`, vanishes near `f(p)` off the joint outer region `{|η_i| < 7Δ, t < 7Δ}`
(closed support), and has `‖Dψ_e‖ ≤ C₀/ρ(p)` at every point of the segment from `F(p)` to `f(p)`,
which lies in `O`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology
open scoped ContDiff BigOperators

namespace GC.MetricGeometry

section RealProfiles

variable {χ : ℝ → ℝ}

/-- Mean value bound for a real function with a bounded derivative. -/
theorem cfs_abs_sub_le_of_abs_deriv_le {g : ℝ → ℝ} (hg : Differentiable ℝ g) {C : ℝ}
    (hC : ∀ s, |deriv g s| ≤ C) (a b : ℝ) : |g a - g b| ≤ C * |a - b| := by
  have h := Convex.norm_image_sub_le_of_norm_deriv_le (s := univ) (fun x _ => hg x)
    (fun x _ => by rw [Real.norm_eq_abs]; exact hC x) convex_univ (mem_univ b) (mem_univ a)
  simpa [Real.norm_eq_abs] using h

theorem cfsRamp_mem_Icc (hχI : ∀ t, χ t ∈ Icc (0 : ℝ) 1) (a b t : ℝ) :
    cfsRamp χ a b t ∈ Icc (0 : ℝ) 1 :=
  hχI _

theorem cfsRamp_monotone (hχmono : Monotone χ) {a b : ℝ} (hab : a < b) :
    Monotone (cfsRamp χ a b) := fun s t hst =>
  hχmono (div_le_div_of_nonneg_right (by linarith) (by linarith))

theorem abs_cfsRamp_sub_le (hχ : ContDiff ℝ ∞ χ) {P : ℝ} (hP : ∀ t, |deriv χ t| ≤ P) {a b : ℝ}
    (hab : a < b) (s t : ℝ) :
    |cfsRamp χ a b s - cfsRamp χ a b t| ≤ P / (b - a) * |s - t| :=
  cfs_abs_sub_le_of_abs_deriv_le (fun x => (hasDerivAt_cfsRamp hχ a b x).differentiableAt)
    (abs_deriv_cfsRamp_le hχ hP hab) s t

theorem cfsRamp_comp_eventually_zero {H : Type*} [TopologicalSpace H] (hχ0 : ∀ t ≤ 0, χ t = 0)
    {a b : ℝ} (hab : a < b) {g : H → ℝ} {z : H} (hg : ContinuousAt g z) (h : g z < a) :
    (fun w => cfsRamp χ a b (g w)) =ᶠ[𝓝 z] fun _ => 0 := by
  filter_upwards [hg.eventually (gt_mem_nhds h)] with w hw
  exact cfsRamp_eq_zero hχ0 hab hw.le

/-- The truncation `T(s) = s · χ_{1/16,1/8}(s)`. -/
def cfsTrunc (χ : ℝ → ℝ) (s : ℝ) : ℝ := s * cfsRamp χ (1 / 16) (1 / 8) s

theorem contDiff_cfsTrunc (hχ : ContDiff ℝ ∞ χ) : ContDiff ℝ ∞ (cfsTrunc χ) :=
  contDiff_id.mul (contDiff_cfsRamp hχ _ _)

theorem cfsTrunc_eq_zero (hχ0 : ∀ t ≤ 0, χ t = 0) {s : ℝ} (hs : s ≤ 1 / 16) :
    cfsTrunc χ s = 0 := by
  rw [cfsTrunc, cfsRamp_eq_zero hχ0 (by norm_num : (1 / 16 : ℝ) < 1 / 8) hs, mul_zero]

theorem cfsTrunc_eq_self (hχ1 : ∀ t, 1 ≤ t → χ t = 1) {s : ℝ} (hs : 1 / 8 ≤ s) :
    cfsTrunc χ s = s := by
  rw [cfsTrunc, cfsRamp_eq_one hχ1 (by norm_num : (1 / 16 : ℝ) < 1 / 8) hs, mul_one]

theorem cfsTrunc_nonneg (hχ0 : ∀ t ≤ 0, χ t = 0) (hχI : ∀ t, χ t ∈ Icc (0 : ℝ) 1) (s : ℝ) :
    0 ≤ cfsTrunc χ s := by
  by_cases hs : s ≤ 1 / 16
  · rw [cfsTrunc_eq_zero hχ0 hs]
  · exact mul_nonneg (by linarith [not_le.mp hs]) (hχI _).1

theorem cfsTrunc_le_self (hχI : ∀ t, χ t ∈ Icc (0 : ℝ) 1) {s : ℝ} (hs : 0 ≤ s) :
    cfsTrunc χ s ≤ s := by
  have h := (hχI ((s - 1 / 16) / (1 / 8 - 1 / 16))).2
  simp only [cfsTrunc, cfsRamp]
  nlinarith

theorem abs_deriv_cfsTrunc_le (hχ : ContDiff ℝ ∞ χ) (hχ0 : ∀ t ≤ 0, χ t = 0)
    (hχ1 : ∀ t, 1 ≤ t → χ t = 1) (hχI : ∀ t, χ t ∈ Icc (0 : ℝ) 1) {P : ℝ}
    (hP : ∀ t, |deriv χ t| ≤ P) (s : ℝ) : |deriv (cfsTrunc χ) s| ≤ 1 + 2 * P := by
  have hP0 : 0 ≤ P := (abs_nonneg _).trans (hP 0)
  by_cases h1 : s < 1 / 16
  · have heq : cfsTrunc χ =ᶠ[𝓝 s] fun _ => 0 := by
      filter_upwards [Iio_mem_nhds h1] with w hw
      exact cfsTrunc_eq_zero hχ0 (le_of_lt hw)
    rw [heq.deriv_eq, deriv_const, abs_zero]
    linarith
  by_cases h2 : 1 / 8 < s
  · have heq : cfsTrunc χ =ᶠ[𝓝 s] fun w => w := by
      filter_upwards [Ioi_mem_nhds h2] with w hw
      exact cfsTrunc_eq_self hχ1 (le_of_lt hw)
    rw [heq.deriv_eq, deriv_id'', abs_one]
    linarith
  rw [not_lt] at h1 h2
  have hd : HasDerivAt (cfsTrunc χ) (1 * cfsRamp χ (1 / 16) (1 / 8) s +
      s * (deriv χ ((s - 1 / 16) / (1 / 8 - 1 / 16)) * (1 / (1 / 8 - 1 / 16)))) s :=
    (hasDerivAt_id s).mul (hasDerivAt_cfsRamp hχ _ _ s)
  rw [hd.deriv]
  have hr := hχI ((s - 1 / 16) / (1 / 8 - 1 / 16))
  have hq := hP ((s - 1 / 16) / (1 / 8 - 1 / 16))
  have hs0 : 0 ≤ s := by linarith
  calc |1 * cfsRamp χ (1 / 16) (1 / 8) s +
        s * (deriv χ ((s - 1 / 16) / (1 / 8 - 1 / 16)) * (1 / (1 / 8 - 1 / 16)))|
      ≤ |1 * cfsRamp χ (1 / 16) (1 / 8) s| +
        |s * (deriv χ ((s - 1 / 16) / (1 / 8 - 1 / 16)) * (1 / (1 / 8 - 1 / 16)))| :=
        abs_add_le _ _
    _ ≤ 1 + 1 / 8 * (P * 16) := by
        apply add_le_add
        · rw [one_mul, abs_le]
          simp only [cfsRamp, mem_Icc] at hr ⊢
          constructor <;> linarith
        · rw [abs_mul, abs_mul, abs_of_nonneg hs0]
          have h16 : |(1 : ℝ) / (1 / 8 - 1 / 16)| = 16 := by norm_num
          rw [h16]
          exact mul_le_mul h2 (mul_le_mul_of_nonneg_right hq (by norm_num)) (by positivity)
            (by norm_num)
    _ = 1 + 2 * P := by ring

theorem abs_cfsTrunc_sub_le (hχ : ContDiff ℝ ∞ χ) (hχ0 : ∀ t ≤ 0, χ t = 0)
    (hχ1 : ∀ t, 1 ≤ t → χ t = 1) (hχI : ∀ t, χ t ∈ Icc (0 : ℝ) 1) {P : ℝ}
    (hP : ∀ t, |deriv χ t| ≤ P) (a b : ℝ) :
    |cfsTrunc χ a - cfsTrunc χ b| ≤ (1 + 2 * P) * |a - b| :=
  cfs_abs_sub_le_of_abs_deriv_le ((contDiff_cfsTrunc hχ).differentiable (by simp))
    (abs_deriv_cfsTrunc_le hχ hχ0 hχ1 hχI hP) a b

end RealProfiles

section Product

variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]

/-- Product rule bound for real functions. -/
theorem cfs_norm_fderiv_mul_le {c d : H → ℝ} {z : H} (hc : DifferentiableAt ℝ c z)
    (hd : DifferentiableAt ℝ d z) {A B A' B' : ℝ} (hcA : |c z| ≤ A) (hdB : |d z| ≤ B)
    (hc' : ‖fderiv ℝ c z‖ ≤ A') (hd' : ‖fderiv ℝ d z‖ ≤ B') :
    ‖fderiv ℝ (fun w => c w * d w) z‖ ≤ A * B' + B * A' := by
  rw [fderiv_fun_mul hc hd]
  calc ‖c z • fderiv ℝ d z + d z • fderiv ℝ c z‖
      ≤ ‖c z • fderiv ℝ d z‖ + ‖d z • fderiv ℝ c z‖ := norm_add_le _ _
    _ ≤ A * B' + B * A' := by
        rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
        exact add_le_add (mul_le_mul hcA hd' (norm_nonneg _) ((abs_nonneg _).trans hcA))
          (mul_le_mul hdB hc' (norm_nonneg _) ((abs_nonneg _).trans hdB))

/-- Chain rule bound for a ramp after a real function. -/
theorem cfs_norm_fderiv_ramp_comp_le {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ) {P : ℝ}
    (hP : ∀ t, |deriv χ t| ≤ P) {a b : ℝ} (hab : a < b) {g : H → ℝ} {z : H}
    (hg : DifferentiableAt ℝ g z) {B : ℝ} (hB : ‖fderiv ℝ g z‖ ≤ B) :
    ‖fderiv ℝ (fun w => cfsRamp χ a b (g w)) z‖ ≤ P / (b - a) * B := by
  have h := norm_fderiv_comp_real_le ((hasDerivAt_cfsRamp hχ a b (g z)).differentiableAt) hg
    (abs_deriv_cfsRamp_le hχ hP hab (g z))
  have hpos : 0 ≤ P / (b - a) := by
    have hP0 : 0 ≤ P := (abs_nonneg _).trans (hP 0)
    exact div_nonneg hP0 (by linarith)
  exact h.trans (mul_le_mul_of_nonneg_left hB hpos)

theorem cfs_differentiableAt_div {c d : H → ℝ} {z : H} (hc : DifferentiableAt ℝ c z)
    (hd : DifferentiableAt ℝ d z) (hx : d z ≠ 0) : DifferentiableAt ℝ (fun w => c w / d w) z := by
  have h := hc.fun_mul (hd.fun_inv hx)
  simpa only [div_eq_mul_inv] using h

/-- Quotient rule bound for a real function over a positive continuous linear functional. -/
theorem cfs_norm_fderiv_div_clm_le {c : H → ℝ} {z : H} (hc : DifferentiableAt ℝ c z)
    (L : H →L[ℝ] ℝ) (hLz : 0 < L z) {A A' K : ℝ} (hcA : |c z| ≤ A)
    (hc' : ‖fderiv ℝ c z‖ ≤ A') (hL : ‖L‖ ≤ K) :
    ‖fderiv ℝ (fun w => c w / L w) z‖ ≤ A * (K / L z ^ 2) + 1 / L z * A' := by
  have hinv : HasFDerivAt (fun w => (L w)⁻¹) ((-(L z ^ 2)⁻¹) • L) z :=
    (hasDerivAt_inv hLz.ne').comp_hasFDerivAt z L.hasFDerivAt
  have hfun : (fun w => c w / L w) = fun w => c w * (L w)⁻¹ := by
    funext w
    rw [div_eq_mul_inv]
  rw [hfun]
  refine cfs_norm_fderiv_mul_le hc hinv.differentiableAt hcA ?_ hc' ?_
  · rw [abs_inv, abs_of_pos hLz, one_div]
  · rw [hinv.fderiv, norm_smul, norm_neg, Real.norm_eq_abs, abs_inv,
      abs_of_pos (by positivity : (0 : ℝ) < L z ^ 2)]
    calc (L z ^ 2)⁻¹ * ‖L‖ ≤ (L z ^ 2)⁻¹ * K :=
          mul_le_mul_of_nonneg_left hL (by positivity)
      _ = K / L z ^ 2 := by rw [inv_mul_eq_div]

end Product

section RatioFactor

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]

/-- The ratio factor `q(‖u‖/(ℓ v)) = 1 − χ_{6.2,6.8}(‖u‖/(ℓ v))` of the CFS22/CFS23 gates. -/
def cfsAxisRatioFactor (χ : ℝ → ℝ) (ℓ : ℝ) (u : H →L[ℝ] E) (v : H →L[ℝ] ℝ) (z : H) : ℝ :=
  1 - cfsRamp χ (31 / 5) (34 / 5) (‖u z‖ / (ℓ * v z))

variable {χ : ℝ → ℝ} {ℓ : ℝ} (u : H →L[ℝ] E) (v : H →L[ℝ] ℝ)

theorem cfsAxisGate_eq_mul_ratioFactor (R : ℝ) (z : H) :
    cfsAxisGate χ ℓ R u v z =
      cfsRamp χ (1 / 2) (3 / 4) (v z / R) * cfsAxisRatioFactor χ ℓ u v z :=
  rfl

theorem cfsAxisRatioFactor_mem_Icc (hχI : ∀ t, χ t ∈ Icc (0 : ℝ) 1) (z : H) :
    cfsAxisRatioFactor χ ℓ u v z ∈ Icc (0 : ℝ) 1 := by
  have h := hχI ((‖u z‖ / (ℓ * v z) - 31 / 5) / (34 / 5 - 31 / 5))
  simp only [cfsAxisRatioFactor, cfsRamp, mem_Icc] at h ⊢
  constructor <;> linarith

theorem cfsAxisRatioFactor_eq_one (hχ0 : ∀ t ≤ 0, χ t = 0) {z : H}
    (hs : ‖u z‖ / (ℓ * v z) ≤ 31 / 5) : cfsAxisRatioFactor χ ℓ u v z = 1 := by
  rw [cfsAxisRatioFactor, cfsRamp_eq_zero hχ0 (by norm_num) hs, sub_zero]

theorem cfsAxisRatioFactor_eventually_one (hχ0 : ∀ t ≤ 0, χ t = 0) (hℓ : ℓ ≠ 0) {z : H}
    (hv : v z ≠ 0) (hs : ‖u z‖ / (ℓ * v z) < 31 / 5) :
    cfsAxisRatioFactor χ ℓ u v =ᶠ[𝓝 z] fun _ => 1 := by
  filter_upwards [(continuousAt_axisRatio u v hv hℓ).eventually (gt_mem_nhds hs)] with w hw
  exact cfsAxisRatioFactor_eq_one u v hχ0 hw.le

theorem cfsAxisRatioFactor_eventually_zero (hχ1 : ∀ t, 1 ≤ t → χ t = 1) (hℓ : ℓ ≠ 0)
    {z : H} (hv : v z ≠ 0) (hs : 34 / 5 < ‖u z‖ / (ℓ * v z)) :
    cfsAxisRatioFactor χ ℓ u v =ᶠ[𝓝 z] fun _ => 0 := by
  filter_upwards [(continuousAt_axisRatio u v hv hℓ).eventually (lt_mem_nhds hs)] with w hw
  rw [cfsAxisRatioFactor, cfsRamp_eq_one hχ1 (by norm_num) hw.le, sub_self]

theorem cfsAxisRatioFactor_contDiffAt (hχ : ContDiff ℝ ∞ χ) (hχ0 : ∀ t ≤ 0, χ t = 0)
    (hℓ : ℓ ≠ 0) {z : H} (hv : v z ≠ 0) :
    ContDiffAt ℝ ∞ (cfsAxisRatioFactor χ ℓ u v) z := by
  by_cases h : ‖u z‖ / (ℓ * v z) < 31 / 5
  · exact contDiffAt_const.congr_of_eventuallyEq
      (cfsAxisRatioFactor_eventually_one u v hχ0 hℓ hv h)
  have hu0 : u z ≠ 0 := by
    intro h0
    rw [h0, norm_zero, zero_div] at h
    norm_num at h
  have hs : ContDiffAt ℝ ∞ (fun w => ‖u w‖ / (ℓ * v w)) z :=
    ((contDiffAt_norm ℝ hu0).comp z u.contDiff.contDiffAt).div
      (contDiffAt_const.mul v.contDiff.contDiffAt) (mul_ne_zero hℓ hv)
  exact contDiffAt_const.sub ((contDiff_cfsRamp hχ _ _).contDiffAt.comp z hs)

/-- `‖D q‖ ≤ 13 P / v` at points with `v > 0`. -/
theorem norm_fderiv_cfsAxisRatioFactor_le (hχ : ContDiff ℝ ∞ χ) (hχ0 : ∀ t ≤ 0, χ t = 0)
    (hχ1 : ∀ t, 1 ≤ t → χ t = 1) {P : ℝ} (hP : ∀ t, |deriv χ t| ≤ P) (hu : ‖u‖ ≤ 1)
    (hv : ‖v‖ ≤ 1) (hℓ : 1 ≤ ℓ) {z : H} (hvz : 0 < v z) :
    ‖fderiv ℝ (cfsAxisRatioFactor χ ℓ u v) z‖ ≤ 13 * P / v z := by
  have hP0 : 0 ≤ P := (abs_nonneg _).trans (hP 0)
  have hbound0 : (0 : ℝ) ≤ 13 * P / v z := by positivity
  have hℓ0 : 0 < ℓ := by linarith
  by_cases h2 : ‖u z‖ / (ℓ * v z) < 31 / 5
  · rw [(cfsAxisRatioFactor_eventually_one u v hχ0 hℓ0.ne' hvz.ne' h2).fderiv_eq,
      fderiv_const_apply, norm_zero]
    exact hbound0
  by_cases h3 : 34 / 5 < ‖u z‖ / (ℓ * v z)
  · rw [(cfsAxisRatioFactor_eventually_zero u v hχ1 hℓ0.ne' hvz.ne' h3).fderiv_eq,
      fderiv_const_apply, norm_zero]
    exact hbound0
  rw [not_lt] at h2 h3
  have hu0 : u z ≠ 0 := by
    intro h0
    rw [h0, norm_zero, zero_div] at h2
    norm_num at h2
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
  set L : H →L[ℝ] ℝ := ℓ • v with hLdef
  have hLapply : ∀ w, L w = ℓ * v w := fun w => by simp [L]
  have hLz : 0 < L z := by rw [hLapply]; positivity
  have hLnorm : ‖L‖ ≤ ℓ := by
    calc ‖L‖ ≤ ‖ℓ‖ * ‖v‖ := ContinuousLinearMap.opNorm_smul_le _ _
      _ ≤ ℓ * 1 := by
          rw [Real.norm_eq_abs, abs_of_pos hℓ0]
          exact mul_le_mul_of_nonneg_left hv hℓ0.le
      _ = ℓ := mul_one ℓ
  have hsz : ‖u z‖ ≤ 34 / 5 * (ℓ * v z) := (div_le_iff₀ (by positivity)).mp h3
  have hratio : ‖fderiv ℝ (fun w => ‖u w‖ / L w) z‖ ≤
      34 / 5 * (ℓ * v z) * (ℓ / L z ^ 2) + 1 / L z * 1 :=
    cfs_norm_fderiv_div_clm_le hNdiff L hLz (by rw [abs_norm]; exact hsz) hN' hLnorm
  have hfun : (fun w => ‖u w‖ / L w) = fun w => ‖u w‖ / (ℓ * v w) := by
    funext w
    rw [hLapply]
  rw [hfun, hLapply] at hratio
  have hratio' : ‖fderiv ℝ (fun w => ‖u w‖ / (ℓ * v w)) z‖ ≤ 39 / 5 / v z := by
    have e1 : 34 / 5 * (ℓ * v z) * (ℓ / (ℓ * v z) ^ 2) + 1 / (ℓ * v z) * 1 =
        34 / 5 / v z + 1 / (ℓ * v z) := by
      field_simp
    have e2 : 1 / (ℓ * v z) ≤ 1 / v z := by
      rw [div_le_div_iff₀ (by positivity) hvz]
      nlinarith
    calc _ ≤ _ := hratio
      _ = 34 / 5 / v z + 1 / (ℓ * v z) := e1
      _ ≤ 34 / 5 / v z + 1 / v z := by linarith
      _ = 39 / 5 / v z := by ring
  have hratioDiff : DifferentiableAt ℝ (fun w => ‖u w‖ / (ℓ * v w)) z :=
    cfs_differentiableAt_div hNdiff ((v.differentiableAt).const_mul ℓ)
      (mul_ne_zero hℓ0.ne' hvz.ne')
  have hQfun : cfsAxisRatioFactor χ ℓ u v =
      fun w => 1 - cfsRamp χ (31 / 5) (34 / 5) (‖u w‖ / (ℓ * v w)) := rfl
  rw [hQfun, fderiv_const_sub]
  rw [norm_neg]
  calc _ ≤ P / (34 / 5 - 31 / 5) * (39 / 5 / v z) :=
        cfs_norm_fderiv_ramp_comp_le (a := 31 / 5) (b := 34 / 5) hχ hP (by norm_num) hratioDiff
          hratio'
    _ = 13 * P / v z := by ring

end RatioFactor

section EdgeGate

variable {E' : Type*} [NormedAddCommGroup E'] [InnerProductSpace ℝ E']
  {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]

/-- The edge gate `B_E = χ_{1/8,1/4}(x''/x_ρ) · q(‖x'‖/(Δ x''))`. -/
def cfsEdgeGate (χ : ℝ → ℝ) (Δ : ℝ) (xρ : H →L[ℝ] ℝ) (x1 : H →L[ℝ] E') (x2 : H →L[ℝ] ℝ)
    (z : H) : ℝ :=
  cfsRamp χ (1 / 8) (1 / 4) (x2 z / xρ z) * cfsAxisRatioFactor χ Δ x1 x2 z

variable {χ : ℝ → ℝ} {Δ : ℝ} (xρ : H →L[ℝ] ℝ) (x1 : H →L[ℝ] E') (x2 : H →L[ℝ] ℝ)

theorem cfsEdgeGate_mem_Icc (hχI : ∀ t, χ t ∈ Icc (0 : ℝ) 1) (z : H) :
    cfsEdgeGate χ Δ xρ x1 x2 z ∈ Icc (0 : ℝ) 1 := by
  have h1 := hχI ((x2 z / xρ z - 1 / 8) / (1 / 4 - 1 / 8))
  have h2 := cfsAxisRatioFactor_mem_Icc (ℓ := Δ) x1 x2 hχI z
  simp only [cfsEdgeGate, cfsRamp, mem_Icc] at h1 h2 ⊢
  constructor <;> nlinarith

theorem continuousAt_cfsEdgeRatio {z : H} (hz : xρ z ≠ 0) :
    ContinuousAt (fun w => x2 w / xρ w) z :=
  x2.continuous.continuousAt.div xρ.continuous.continuousAt hz

theorem cfsEdgeGate_eventually_zero_of_lt (hχ0 : ∀ t ≤ 0, χ t = 0) {z : H} (hz : xρ z ≠ 0)
    (h : x2 z / xρ z < 1 / 8) : cfsEdgeGate χ Δ xρ x1 x2 =ᶠ[𝓝 z] fun _ => 0 := by
  filter_upwards [(continuousAt_cfsEdgeRatio xρ x2 hz).eventually (gt_mem_nhds h)] with w hw
  rw [cfsEdgeGate, cfsRamp_eq_zero hχ0 (by norm_num) hw.le, zero_mul]

theorem cfsEdgeGate_eventually_zero_of_gt (hχ1 : ∀ t, 1 ≤ t → χ t = 1) (hΔ : Δ ≠ 0)
    {z : H} (hx2 : x2 z ≠ 0) (hs : 34 / 5 < ‖x1 z‖ / (Δ * x2 z)) :
    cfsEdgeGate χ Δ xρ x1 x2 =ᶠ[𝓝 z] fun _ => 0 := by
  filter_upwards [cfsAxisRatioFactor_eventually_zero x1 x2 hχ1 hΔ hx2 hs] with w hw
  rw [cfsEdgeGate, hw, mul_zero]

theorem cfsEdgeGate_eq_one (hχ0 : ∀ t ≤ 0, χ t = 0) (hχ1 : ∀ t, 1 ≤ t → χ t = 1) {z : H}
    (hv : 1 / 4 ≤ x2 z / xρ z) (hs : ‖x1 z‖ / (Δ * x2 z) ≤ 31 / 5) :
    cfsEdgeGate χ Δ xρ x1 x2 z = 1 := by
  rw [cfsEdgeGate, cfsRamp_eq_one hχ1 (by norm_num) hv, cfsAxisRatioFactor_eq_one x1 x2 hχ0 hs,
    one_mul]

theorem cfsEdgeGate_contDiffAt (hχ : ContDiff ℝ ∞ χ) (hχ0 : ∀ t ≤ 0, χ t = 0) (hΔ : Δ ≠ 0)
    {z : H} (hz : 0 < xρ z) : ContDiffAt ℝ ∞ (cfsEdgeGate χ Δ xρ x1 x2) z := by
  by_cases h : x2 z / xρ z < 1 / 8
  · exact contDiffAt_const.congr_of_eventuallyEq
      (cfsEdgeGate_eventually_zero_of_lt xρ x1 x2 hχ0 hz.ne' h)
  have hx2 : 0 < x2 z := by
    rw [not_lt, le_div_iff₀ hz] at h
    linarith
  exact ((contDiff_cfsRamp hχ _ _).contDiffAt.comp z
    (x2.contDiff.contDiffAt.div xρ.contDiff.contDiffAt hz.ne')).mul
    (cfsAxisRatioFactor_contDiffAt x1 x2 hχ hχ0 hΔ hx2.ne')

/-- `‖D (x''/x_ρ)‖ ≤ 10 / r` where `x_ρ ≥ r/2` and `|x''| ≤ 2r`. -/
theorem norm_fderiv_cfsEdgeRatio_le (hxρ : ‖xρ‖ ≤ 1) (hx2 : ‖x2‖ ≤ 1) {r : ℝ} (hr : 0 < r)
    {z : H} (hzr : r ≤ 2 * xρ z) (hx2z : |x2 z| ≤ 2 * r) :
    ‖fderiv ℝ (fun w => x2 w / xρ w) z‖ ≤ 10 / r := by
  have hX : 0 < xρ z := by linarith
  have h := cfs_norm_fderiv_div_clm_le (A' := 1) x2.differentiableAt xρ hX hx2z
    (by rw [x2.fderiv]; exact hx2) hxρ
  have hinv : 1 / xρ z ≤ 2 / r := by
    rw [div_le_div_iff₀ hX hr]
    linarith
  have hinv0 : 0 ≤ 1 / xρ z := by positivity
  have hsq : 1 / xρ z ^ 2 ≤ (2 / r) ^ 2 := by
    rw [show 1 / xρ z ^ 2 = (1 / xρ z) ^ 2 by ring]
    exact pow_le_pow_left₀ hinv0 hinv 2
  calc _ ≤ 2 * r * (1 / xρ z ^ 2) + 1 / xρ z * 1 := h
    _ ≤ 2 * r * (2 / r) ^ 2 + 2 / r * 1 := by
        apply add_le_add
        · exact mul_le_mul_of_nonneg_left hsq (by positivity)
        · exact mul_le_mul_of_nonneg_right hinv zero_le_one
    _ = 10 / r := by field_simp; ring

/-- `‖D B_E‖ ≤ 300 P / r` where `x_ρ ≥ r/2` and `|x''| ≤ 2r`. -/
theorem norm_fderiv_cfsEdgeGate_le (hχ : ContDiff ℝ ∞ χ) (hχ0 : ∀ t ≤ 0, χ t = 0)
    (hχ1 : ∀ t, 1 ≤ t → χ t = 1) (hχI : ∀ t, χ t ∈ Icc (0 : ℝ) 1) {P : ℝ}
    (hP : ∀ t, |deriv χ t| ≤ P) (hxρ : ‖xρ‖ ≤ 1) (hx1 : ‖x1‖ ≤ 1) (hx2 : ‖x2‖ ≤ 1)
    (hΔ : 1 ≤ Δ) {r : ℝ} (hr : 0 < r) {z : H} (hzr : r ≤ 2 * xρ z) (hx2z : |x2 z| ≤ 2 * r) :
    ‖fderiv ℝ (cfsEdgeGate χ Δ xρ x1 x2) z‖ ≤ 300 * P / r := by
  have hP0 : 0 ≤ P := (abs_nonneg _).trans (hP 0)
  have hX : 0 < xρ z := by linarith
  by_cases h : x2 z / xρ z < 1 / 8
  · rw [(cfsEdgeGate_eventually_zero_of_lt xρ x1 x2 hχ0 hX.ne' h).fderiv_eq,
      fderiv_const_apply, norm_zero]
    positivity
  have hx2pos : r / 16 ≤ x2 z := by
    rw [not_lt, le_div_iff₀ hX] at h
    linarith
  have hx2z0 : 0 < x2 z := by linarith
  have hA : ‖fderiv ℝ (fun w => cfsRamp χ (1 / 8) (1 / 4) (x2 w / xρ w)) z‖ ≤
      P / (1 / 4 - 1 / 8) * (10 / r) :=
    cfs_norm_fderiv_ramp_comp_le (a := 1 / 8) (b := 1 / 4) hχ hP (by norm_num)
      (cfs_differentiableAt_div x2.differentiableAt xρ.differentiableAt hX.ne')
      (norm_fderiv_cfsEdgeRatio_le xρ x2 hxρ hx2 hr hzr hx2z)
  have hQ := norm_fderiv_cfsAxisRatioFactor_le x1 x2 hχ hχ0 hχ1 hP hx1 hx2 hΔ hx2z0
  have hQ' : ‖fderiv ℝ (cfsAxisRatioFactor χ Δ x1 x2) z‖ ≤ 208 * P / r := by
    refine hQ.trans ?_
    rw [div_le_div_iff₀ hx2z0 hr]
    nlinarith
  have hAI := hχI ((x2 z / xρ z - 1 / 8) / (1 / 4 - 1 / 8))
  have hAabs : |cfsRamp χ (1 / 8) (1 / 4) (x2 z / xρ z)| ≤ 1 := by
    rw [abs_le]
    simp only [cfsRamp, mem_Icc] at hAI ⊢
    constructor <;> linarith
  have hQI := cfsAxisRatioFactor_mem_Icc (ℓ := Δ) x1 x2 hχI z
  have hQabs : |cfsAxisRatioFactor χ Δ x1 x2 z| ≤ 1 := by
    rw [abs_le]
    constructor <;> linarith [hQI.1, hQI.2]
  have hAd : DifferentiableAt ℝ (fun w => cfsRamp χ (1 / 8) (1 / 4) (x2 w / xρ w)) z :=
    (hasDerivAt_cfsRamp hχ _ _ _).differentiableAt.comp z
      (cfs_differentiableAt_div x2.differentiableAt xρ.differentiableAt hX.ne')
  have hQd : DifferentiableAt ℝ (cfsAxisRatioFactor χ Δ x1 x2) z :=
    (cfsAxisRatioFactor_contDiffAt x1 x2 hχ hχ0 (by linarith) hx2z0.ne').differentiableAt
      (by simp)
  have hprod := cfs_norm_fderiv_mul_le hAd hQd hAabs hQabs hA hQ'
  calc ‖fderiv ℝ (cfsEdgeGate χ Δ xρ x1 x2) z‖ ≤
      1 * (208 * P / r) + 1 * (P / (1 / 4 - 1 / 8) * (10 / r)) := hprod
    _ ≤ 300 * P / r := by
        rw [show 1 * (208 * P / r) + 1 * (P / (1 / 4 - 1 / 8) * (10 / r)) = 288 * P / r by
          field_simp; ring]
        apply div_le_div_of_nonneg_right _ hr.le
        linarith

end EdgeGate

section GateValues

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
  {χ : ℝ → ℝ} (u : H →L[ℝ] E) (v : H →L[ℝ] ℝ)

theorem cfs_abs_clm_sub_le (L : H →L[ℝ] ℝ) (hL : ‖L‖ ≤ 1) (w w' : H) :
    |L w - L w'| ≤ ‖w - w'‖ := by
  rw [← map_sub, ← Real.norm_eq_abs]
  calc ‖L (w - w')‖ ≤ ‖L‖ * ‖w - w'‖ := L.le_opNorm _
    _ ≤ 1 * ‖w - w'‖ := mul_le_mul_of_nonneg_right hL (norm_nonneg _)
    _ = ‖w - w'‖ := one_mul _

theorem cfs_norm_clm_sub_le (L : H →L[ℝ] E) (hL : ‖L‖ ≤ 1) (w w' : H) :
    ‖L w - L w'‖ ≤ ‖w - w'‖ := by
  rw [← map_sub]
  calc ‖L (w - w')‖ ≤ ‖L‖ * ‖w - w'‖ := L.le_opNorm _
    _ ≤ 1 * ‖w - w'‖ := mul_le_mul_of_nonneg_right hL (norm_nonneg _)
    _ = ‖w - w'‖ := one_mul _

theorem cfs_norm_segment_sub_le {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) (a b : H) :
    ‖((1 - s) • a + s • b) - a‖ ≤ ‖b - a‖ := by
  have h : ((1 - s) • a + s • b) - a = s • (b - a) := by
    rw [sub_smul, one_smul, smul_sub]
    abel
  rw [h, norm_smul, Real.norm_eq_abs, abs_of_nonneg hs.1]
  calc s * ‖b - a‖ ≤ 1 * ‖b - a‖ := mul_le_mul_of_nonneg_right hs.2 (norm_nonneg _)
    _ = ‖b - a‖ := one_mul _

/-- The axis gate equals one near a full marker inside the `6ℓ` core (CFS22 plateau step). -/
theorem cfsAxisGate_eq_one_of_near (hχ0 : ∀ t ≤ 0, χ t = 0) (hχ1 : ∀ t, 1 ≤ t → χ t = 1)
    {ℓ R κ a : ℝ} (hR : 0 < R) (hℓ : 1 ≤ ℓ) (hκ0 : 0 ≤ κ) (hκ : κ ≤ 1 / 1000) {w : H}
    (hvw : R * (1 - κ) ≤ v w) (huw : ‖u w‖ ≤ R * a + κ * R) (ha : a < 6 * ℓ) :
    cfsAxisGate χ ℓ R u v w = 1 := by
  have hℓ0 : 0 < ℓ := by linarith
  have hvpos : 0 < v w := by
    have : 0 < R * (1 - κ) := mul_pos hR (by linarith)
    linarith
  have hA : cfsRamp χ (1 / 2) (3 / 4) (v w / R) = 1 := by
    refine cfsRamp_eq_one hχ1 (by norm_num) ?_
    rw [le_div_iff₀ hR]
    nlinarith
  have hB : cfsRamp χ (31 / 5) (34 / 5) (‖u w‖ / (ℓ * v w)) = 0 := by
    refine cfsRamp_eq_zero hχ0 (by norm_num) ?_
    rw [div_le_iff₀ (by positivity)]
    have h1 : R * a ≤ R * (6 * ℓ) := mul_le_mul_of_nonneg_left ha.le hR.le
    have h2 : ℓ * (R * (1 - κ)) ≤ ℓ * v w := mul_le_mul_of_nonneg_left hvw hℓ0.le
    have hℓR : 0 < ℓ * R := mul_pos hℓ0 hR
    have k1 : ℓ * R * κ ≤ ℓ * R * (1 / 1000) := mul_le_mul_of_nonneg_left hκ hℓR.le
    have k2 : 1 * (κ * R) ≤ ℓ * (κ * R) := mul_le_mul_of_nonneg_right hℓ (mul_nonneg hκ0 hR.le)
    linarith
  rw [cfsAxisGate_eq_mul_ratioFactor, cfsAxisRatioFactor, hA, hB, sub_zero, mul_one]

/-- The axis gate vanishes near a point whose marker block is far out (CFS22 support step). -/
theorem cfsAxisGate_eventually_zero_of_far (hχ0 : ∀ t ≤ 0, χ t = 0)
    (hχ1 : ∀ t, 1 ≤ t → χ t = 1) {ℓ R κ ζ a : ℝ} (hR : 0 < R) (hℓ : 1 ≤ ℓ) (hκ0 : 0 ≤ κ)
    (hκ : κ ≤ 1 / 1000) (hζ : 0 ≤ ζ) {w : H} (hvw : |v w - R * ζ| ≤ κ * R)
    (huw : R * ζ * a - κ * R ≤ ‖u w‖) (ha : 7 * ℓ ≤ a) :
    cfsAxisGate χ ℓ R u v =ᶠ[𝓝 w] fun _ => 0 := by
  have hℓ0 : 0 < ℓ := by linarith
  by_cases hv2 : v w / R < 1 / 2
  · exact cfsAxisGate_eventually_zero_of_lt hχ0 u v hv2
  rw [not_lt, le_div_iff₀ hR] at hv2
  have hvup : v w ≤ R * ζ + κ * R := by linarith [(abs_le.mp hvw).2]
  have hvpos : 0 < v w := by linarith
  have hζlow : 1 / 2 - κ ≤ ζ := by
    have : R * (1 / 2) ≤ R * (ζ + κ) := by nlinarith
    have := le_of_mul_le_mul_left this hR
    linarith
  refine cfsAxisGate_eventually_zero_of_gt hχ1 u v hℓ0.ne' hvpos.ne' ?_
  rw [lt_div_iff₀ (by positivity)]
  have h1 : R * ζ * (7 * ℓ) ≤ R * ζ * a := mul_le_mul_of_nonneg_left ha (mul_nonneg hR.le hζ)
  have h2 : ℓ * v w ≤ ℓ * (R * ζ + κ * R) := mul_le_mul_of_nonneg_left hvup hℓ0.le
  have hℓR : 0 < ℓ * R := mul_pos hℓ0 hR
  have f4 : ℓ * R * (1 / 2 - κ) ≤ ℓ * R * ζ := mul_le_mul_of_nonneg_left hζlow hℓR.le
  have f5 : 1 * (κ * R) ≤ ℓ * (κ * R) := mul_le_mul_of_nonneg_right hℓ (mul_nonneg hκ0 hR.le)
  have f6 : ℓ * R * κ ≤ ℓ * R * (1 / 1000) := mul_le_mul_of_nonneg_left hκ hℓR.le
  linarith

end GateValues

section Aggregate

variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
  {I : Type*} [Fintype I]

/-- The truncated aggregate `Z = χ_{1/2,1}(Σ_i T(v_i / R_i))`. -/
def cfsTruncAggregate (χ : ℝ → ℝ) (R : I → ℝ) (v : I → H →L[ℝ] ℝ) (z : H) : ℝ :=
  cfsRamp χ (1 / 2) 1 (∑ i, cfsTrunc χ (v i z / R i))

/-- The edge defect `d_i = (v_i / R_i) Z − x''/x_ρ`. -/
def cfsEdgeDefect (χ : ℝ → ℝ) (R : I → ℝ) (v : I → H →L[ℝ] ℝ) (xρ x2 : H →L[ℝ] ℝ) (i : I)
    (z : H) : ℝ :=
  v i z / R i * cfsTruncAggregate χ R v z - x2 z / xρ z

variable {χ : ℝ → ℝ} (R : I → ℝ) (v : I → H →L[ℝ] ℝ)

theorem contDiff_cfsTruncAggregate (hχ : ContDiff ℝ ∞ χ) :
    ContDiff ℝ ∞ (cfsTruncAggregate χ R v) :=
  (contDiff_cfsRamp hχ _ _).comp
    (ContDiff.sum fun i _ => (contDiff_cfsTrunc hχ).comp ((v i).contDiff.div_const (R i)))

theorem cfsTruncAggregate_mem_Icc (hχI : ∀ t, χ t ∈ Icc (0 : ℝ) 1) (z : H) :
    cfsTruncAggregate χ R v z ∈ Icc (0 : ℝ) 1 :=
  hχI _

theorem cfs_div_const_clm_eq (L : H →L[ℝ] ℝ) (c : ℝ) :
    (fun w => L w / c) = ⇑(c⁻¹ • L) := by
  funext w
  simp [div_eq_inv_mul]

theorem cfs_differentiableAt_div_const_clm (L : H →L[ℝ] ℝ) (c : ℝ) (z : H) :
    DifferentiableAt ℝ (fun w => L w / c) z := by
  rw [cfs_div_const_clm_eq]
  exact (c⁻¹ • L).differentiableAt

theorem cfs_norm_inv_smul_clm_le (L : H →L[ℝ] ℝ) (hL : ‖L‖ ≤ 1) {c : ℝ} (hc : 0 < c) :
    ‖c⁻¹ • L‖ ≤ 1 / c := by
  calc ‖c⁻¹ • L‖ ≤ ‖c⁻¹‖ * ‖L‖ := ContinuousLinearMap.opNorm_smul_le _ _
    _ ≤ c⁻¹ * 1 := by
        rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hc)]
        exact mul_le_mul_of_nonneg_left hL (inv_pos.mpr hc).le
    _ = 1 / c := by ring

theorem norm_fderiv_div_const_clm_le (L : H →L[ℝ] ℝ) (hL : ‖L‖ ≤ 1) {c : ℝ} (hc : 0 < c)
    (z : H) : ‖fderiv ℝ (fun w => L w / c) z‖ ≤ 1 / c := by
  rw [cfs_div_const_clm_eq, ContinuousLinearMap.fderiv]
  exact cfs_norm_inv_smul_clm_le L hL hc

/-- `‖D T(v/R)‖ ≤ (1 + 2P)/R`. -/
theorem norm_fderiv_cfsTrunc_comp_le (hχ : ContDiff ℝ ∞ χ) (hχ0 : ∀ t ≤ 0, χ t = 0)
    (hχ1 : ∀ t, 1 ≤ t → χ t = 1) (hχI : ∀ t, χ t ∈ Icc (0 : ℝ) 1) {P : ℝ}
    (hP : ∀ t, |deriv χ t| ≤ P) (L : H →L[ℝ] ℝ) (hL : ‖L‖ ≤ 1) {c : ℝ} (hc : 0 < c) (z : H) :
    ‖fderiv ℝ (fun w => cfsTrunc χ (L w / c)) z‖ ≤ (1 + 2 * P) * (1 / c) := by
  have hP0 : 0 ≤ P := (abs_nonneg _).trans (hP 0)
  have hdiff : DifferentiableAt ℝ (fun w => L w / c) z := cfs_differentiableAt_div_const_clm L c z
  have h := norm_fderiv_comp_real_le (L := fun w => L w / c) (z := z)
    (((contDiff_cfsTrunc hχ).differentiable (by simp)) (L z / c)) hdiff
    (abs_deriv_cfsTrunc_le hχ hχ0 hχ1 hχI hP (L z / c))
  exact h.trans (mul_le_mul_of_nonneg_left (norm_fderiv_div_const_clm_le L hL hc z)
    (by positivity))

/-- `‖DZ‖ ≤ 8 N P² / r` when only the indices of `S` (`|S| ≤ N`, `R_i ≥ 4r/5`) have markers
`≥ 1/16` at `z`. -/
theorem norm_fderiv_cfsTruncAggregate_le (hχ : ContDiff ℝ ∞ χ) (hχ0 : ∀ t ≤ 0, χ t = 0)
    (hχ1 : ∀ t, 1 ≤ t → χ t = 1) (hχI : ∀ t, χ t ∈ Icc (0 : ℝ) 1) {P : ℝ} (hP1 : 1 ≤ P)
    (hP : ∀ t, |deriv χ t| ≤ P) (hv : ∀ i, ‖v i‖ ≤ 1) (hR : ∀ i, 0 < R i) {N : ℕ}
    (S : Finset I) (hS : S.card ≤ N) {r : ℝ} (hr : 0 < r) {z : H}
    (hout : ∀ i ∉ S, v i z / R i < 1 / 16) (hin : ∀ i ∈ S, 4 / 5 * r ≤ R i) :
    ‖fderiv ℝ (cfsTruncAggregate χ R v) z‖ ≤ 8 * N * P ^ 2 / r := by
  let g : I → H → ℝ := fun i w => cfsTrunc χ (v i w / R i)
  have hgdiff : ∀ i ∈ (Finset.univ : Finset I), DifferentiableAt ℝ (g i) z := fun i _ =>
    ((contDiff_cfsTrunc hχ).comp ((v i).contDiff.div_const (R i))).differentiable
      (by simp) z
  have hD0 : ∀ i ∉ S, fderiv ℝ (g i) z = 0 := by
    intro i hi
    have hev : g i =ᶠ[𝓝 z] fun _ => 0 := by
      have hc : ContinuousAt (fun w => v i w / R i) z :=
        ((v i).continuous.div_const (R i)).continuousAt
      filter_upwards [hc.eventually (gt_mem_nhds (hout i hi))] with w hw
      exact cfsTrunc_eq_zero hχ0 hw.le
    rw [hev.fderiv_eq, fderiv_const_apply]
  have hD1 : ∀ i ∈ S, ‖fderiv ℝ (g i) z‖ ≤ (1 + 2 * P) * (5 / (4 * r)) := by
    intro i hi
    refine (norm_fderiv_cfsTrunc_comp_le hχ hχ0 hχ1 hχI hP (v i) (hv i) (hR i) z).trans ?_
    apply mul_le_mul_of_nonneg_left _ (by linarith)
    rw [div_le_div_iff₀ (hR i) (by positivity)]
    linarith [hin i hi]
  have hsumdiff : DifferentiableAt ℝ (fun w => ∑ i, g i w) z :=
    DifferentiableAt.fun_sum hgdiff
  have hsumnorm : ‖fderiv ℝ (fun w => ∑ i, g i w) z‖ ≤ N * ((1 + 2 * P) * (5 / (4 * r))) := by
    rw [fderiv_fun_sum hgdiff]
    calc ‖∑ i, fderiv ℝ (g i) z‖ ≤ ∑ i, ‖fderiv ℝ (g i) z‖ := norm_sum_le _ _
      _ = ∑ i ∈ S, ‖fderiv ℝ (g i) z‖ := by
          refine (Finset.sum_subset (Finset.subset_univ S) fun i _ hi => ?_).symm
          rw [hD0 i hi, norm_zero]
      _ ≤ ∑ _i ∈ S, (1 + 2 * P) * (5 / (4 * r)) := Finset.sum_le_sum hD1
      _ = S.card * ((1 + 2 * P) * (5 / (4 * r))) := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ N * ((1 + 2 * P) * (5 / (4 * r))) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          exact_mod_cast hS
  have h := cfs_norm_fderiv_ramp_comp_le (a := 1 / 2) (b := 1) hχ hP (by norm_num) hsumdiff
    hsumnorm
  have hZfun : cfsTruncAggregate χ R v = fun w => cfsRamp χ (1 / 2) 1 (∑ i, g i w) := rfl
  rw [hZfun]
  refine h.trans ?_
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  rw [show P / (1 - 1 / 2) * (N * ((1 + 2 * P) * (5 / (4 * r)))) =
    5 / 2 * N * (P * (1 + 2 * P)) / r by field_simp; ring]
  apply div_le_div_of_nonneg_right _ hr.le
  have : P * (1 + 2 * P) ≤ 3 * P ^ 2 := by nlinarith
  nlinarith

/-- `|Z w − Z w'| ≤ 2P Σ_i |T(v_i w / R_i) − T(v_i w' / R_i)|`. -/
theorem abs_cfsTruncAggregate_sub_le (hχ : ContDiff ℝ ∞ χ) {P : ℝ}
    (hP : ∀ t, |deriv χ t| ≤ P) (w w' : H) :
    |cfsTruncAggregate χ R v w - cfsTruncAggregate χ R v w'| ≤
      2 * P * ∑ i, |cfsTrunc χ (v i w / R i) - cfsTrunc χ (v i w' / R i)| := by
  have h := abs_cfsRamp_sub_le hχ hP (by norm_num : (1 / 2 : ℝ) < 1)
    (∑ i, cfsTrunc χ (v i w / R i)) (∑ i, cfsTrunc χ (v i w' / R i))
  have hP0 : 0 ≤ P := (abs_nonneg _).trans (hP 0)
  calc _ ≤ P / (1 - 1 / 2) * |∑ i, cfsTrunc χ (v i w / R i) - ∑ i, cfsTrunc χ (v i w' / R i)| :=
        h
    _ ≤ P / (1 - 1 / 2) * ∑ i, |cfsTrunc χ (v i w / R i) - cfsTrunc χ (v i w' / R i)| := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        rw [← Finset.sum_sub_distrib]
        exact Finset.abs_sum_le_sum_abs _ _
    _ = 2 * P * ∑ i, |cfsTrunc χ (v i w / R i) - cfsTrunc χ (v i w' / R i)| := by ring

theorem cfsEdgeDefect_contDiffAt (hχ : ContDiff ℝ ∞ χ) (xρ x2 : H →L[ℝ] ℝ) (i : I) {z : H}
    (hz : xρ z ≠ 0) : ContDiffAt ℝ ∞ (cfsEdgeDefect χ R v xρ x2 i) z :=
  ((((v i).contDiff.div_const (R i)).mul (contDiff_cfsTruncAggregate R v hχ)).contDiffAt).sub
    (x2.contDiff.contDiffAt.div xρ.contDiff.contDiffAt hz)

/-- `‖D d_i‖ ≤ 2 B_Z + 1/R_i + 10/r`. -/
theorem norm_fderiv_cfsEdgeDefect_le (hχ : ContDiff ℝ ∞ χ) (hχI : ∀ t, χ t ∈ Icc (0 : ℝ) 1)
    (hv : ∀ i, ‖v i‖ ≤ 1) (hR : ∀ i, 0 < R i) (xρ x2 : H →L[ℝ] ℝ) (hxρ : ‖xρ‖ ≤ 1)
    (hx2 : ‖x2‖ ≤ 1) (i : I) {r BZ : ℝ} (hr : 0 < r) {z : H} (hzr : r ≤ 2 * xρ z)
    (hx2z : |x2 z| ≤ 2 * r) (hm : |v i z / R i| ≤ 2)
    (hZ : ‖fderiv ℝ (cfsTruncAggregate χ R v) z‖ ≤ BZ) :
    ‖fderiv ℝ (cfsEdgeDefect χ R v xρ x2 i) z‖ ≤ 2 * BZ + 1 / R i + 10 / r := by
  have hX : 0 < xρ z := by linarith
  have hmdiff : DifferentiableAt ℝ (fun w => v i w / R i) z :=
    cfs_differentiableAt_div_const_clm (v i) (R i) z
  have hZdiff : DifferentiableAt ℝ (cfsTruncAggregate χ R v) z :=
    (contDiff_cfsTruncAggregate R v hχ).differentiable (by simp) z
  have hvEdiff : DifferentiableAt ℝ (fun w => x2 w / xρ w) z :=
    cfs_differentiableAt_div x2.differentiableAt xρ.differentiableAt hX.ne'
  have hprod : DifferentiableAt ℝ (fun w => v i w / R i * cfsTruncAggregate χ R v w) z :=
    hmdiff.mul hZdiff
  have hdfun : cfsEdgeDefect χ R v xρ x2 i =
      fun w => v i w / R i * cfsTruncAggregate χ R v w - x2 w / xρ w := rfl
  have hZI := cfsTruncAggregate_mem_Icc R v hχI z
  have hZabs : |cfsTruncAggregate χ R v z| ≤ 1 := by
    rw [abs_le]
    constructor <;> linarith [hZI.1, hZI.2]
  have h1 := cfs_norm_fderiv_mul_le hmdiff hZdiff hm hZabs
    (norm_fderiv_div_const_clm_le (v i) (hv i) (hR i) z) hZ
  have h2 := norm_fderiv_cfsEdgeRatio_le xρ x2 hxρ hx2 hr hzr hx2z
  rw [hdfun, fderiv_fun_sub hprod hvEdiff]
  calc _ ≤ ‖fderiv ℝ (fun w => v i w / R i * cfsTruncAggregate χ R v w) z‖ +
        ‖fderiv ℝ (fun w => x2 w / xρ w) z‖ := norm_sub_le _ _
    _ ≤ 2 * BZ + 1 * (1 / R i) + 10 / r := add_le_add h1 h2
    _ = 2 * BZ + 1 / R i + 10 / r := by ring

end Aggregate

section Row

variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
  {I : Type*} [Fintype I] {E : I → Type*} [∀ i, NormedAddCommGroup (E i)]
  [∀ i, InnerProductSpace ℝ (E i)]
  {E' : Type*} [NormedAddCommGroup E'] [InnerProductSpace ℝ E']

/-- The summand `a_i (B_E + χ_{1/8,1/4}(d_i))` of CFS23. -/
def cfsEdgeSummand (χ : ℝ → ℝ) (Δ : ℝ) (R : I → ℝ) (u : ∀ i, H →L[ℝ] E i)
    (v : I → H →L[ℝ] ℝ) (xρ : H →L[ℝ] ℝ) (x1 : H →L[ℝ] E') (x2 : H →L[ℝ] ℝ) (i : I)
    (z : H) : ℝ :=
  cfsAxisGate χ Δ (R i) (u i) (v i) z *
    (cfsEdgeGate χ Δ xρ x1 x2 z + cfsRamp χ (1 / 8) (1 / 4) (cfsEdgeDefect χ R v xρ x2 i z))

/-- The buffered edge cutoff `ψ_e = χ_{1/4,1/2}(Σ_i a_i (B_E + χ_{1/8,1/4}(d_i)))` of CFS23. -/
def cfsBufferedEdgeCutoff (χ : ℝ → ℝ) (Δ : ℝ) (R : I → ℝ) (u : ∀ i, H →L[ℝ] E i)
    (v : I → H →L[ℝ] ℝ) (xρ : H →L[ℝ] ℝ) (x1 : H →L[ℝ] E') (x2 : H →L[ℝ] ℝ) (z : H) : ℝ :=
  cfsRamp χ (1 / 4) (1 / 2) (∑ i, cfsEdgeSummand χ Δ R u v xρ x1 x2 i z)

variable {χ : ℝ → ℝ} {Δ : ℝ} (R : I → ℝ) (u : ∀ i, H →L[ℝ] E i) (v : I → H →L[ℝ] ℝ)
  (xρ : H →L[ℝ] ℝ) (x1 : H →L[ℝ] E') (x2 : H →L[ℝ] ℝ)

theorem cfsEdgeSummand_mem_Icc (hχI : ∀ t, χ t ∈ Icc (0 : ℝ) 1) (i : I) (z : H) :
    cfsEdgeSummand χ Δ R u v xρ x1 x2 i z ∈ Icc (0 : ℝ) 2 := by
  have h1 := cfsAxisGate_mem_Icc (ℓ := Δ) (R := R i) hχI (u i) (v i) z
  have h2 := cfsEdgeGate_mem_Icc (Δ := Δ) xρ x1 x2 hχI z
  have h3 := cfsRamp_mem_Icc hχI (1 / 8) (1 / 4) (cfsEdgeDefect χ R v xρ x2 i z)
  simp only [cfsEdgeSummand, mem_Icc] at h1 h2 h3 ⊢
  constructor <;> nlinarith

theorem cfsBufferedEdgeCutoff_mem_Icc (hχI : ∀ t, χ t ∈ Icc (0 : ℝ) 1) (z : H) :
    cfsBufferedEdgeCutoff χ Δ R u v xρ x1 x2 z ∈ Icc (0 : ℝ) 1 :=
  cfsRamp_mem_Icc hχI _ _ _

theorem cfsEdgeSummand_contDiffAt (hχ : ContDiff ℝ ∞ χ) (hχ0 : ∀ t ≤ 0, χ t = 0)
    (hχ1 : ∀ t, 1 ≤ t → χ t = 1) (hR : ∀ i, 0 < R i) (hΔ : 0 < Δ) (i : I) {z : H}
    (hz : 0 < xρ z) : ContDiffAt ℝ ∞ (cfsEdgeSummand χ Δ R u v xρ x1 x2 i) z :=
  (cfsAxisGate_contDiff hχ hχ0 hχ1 (u i) (v i) (hR i) hΔ).contDiffAt.mul
    ((cfsEdgeGate_contDiffAt xρ x1 x2 hχ hχ0 hΔ.ne' hz).add
      ((contDiff_cfsRamp hχ _ _).contDiffAt.comp z
        (cfsEdgeDefect_contDiffAt R v hχ xρ x2 i hz.ne')))

theorem cfsBufferedEdgeCutoff_contDiffAt (hχ : ContDiff ℝ ∞ χ) (hχ0 : ∀ t ≤ 0, χ t = 0)
    (hχ1 : ∀ t, 1 ≤ t → χ t = 1) (hR : ∀ i, 0 < R i) (hΔ : 0 < Δ) {z : H} (hz : 0 < xρ z) :
    ContDiffAt ℝ ∞ (cfsBufferedEdgeCutoff χ Δ R u v xρ x1 x2) z :=
  (contDiff_cfsRamp hχ _ _).contDiffAt.comp z
    (ContDiffAt.sum fun i _ => cfsEdgeSummand_contDiffAt R u v xρ x1 x2 hχ hχ0 hχ1 hR hΔ i hz)

/-- CFS23 smoothness: `ψ_e` is smooth on `O = {x_ρ > 0}`. -/
theorem cfsBufferedEdgeCutoff_contDiffOn (hχ : ContDiff ℝ ∞ χ) (hχ0 : ∀ t ≤ 0, χ t = 0)
    (hχ1 : ∀ t, 1 ≤ t → χ t = 1) (hR : ∀ i, 0 < R i) (hΔ : 0 < Δ) :
    ContDiffOn ℝ ∞ (cfsBufferedEdgeCutoff χ Δ R u v xρ x1 x2) {z | 0 < xρ z} := fun _ hz =>
  (cfsBufferedEdgeCutoff_contDiffAt R u v xρ x1 x2 hχ hχ0 hχ1 hR hΔ hz).contDiffWithinAt

theorem cfs_kappa_facts {P : ℝ} (hP1 : 1 ≤ P) (N : ℕ) :
    0 < 1 / (1000 * ((N : ℝ) + 1) * P ^ 2) ∧ 1 / (1000 * ((N : ℝ) + 1) * P ^ 2) ≤ 1 / 1000 ∧
      ((N : ℝ) + 1) * P ^ 2 * (1 / (1000 * ((N : ℝ) + 1) * P ^ 2)) = 1 / 1000 := by
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hNP : 1 ≤ ((N : ℝ) + 1) * P ^ 2 := by
    have h1 : (1 : ℝ) ≤ (N : ℝ) + 1 := by linarith
    have h2 : (1 : ℝ) ≤ P ^ 2 := by nlinarith
    nlinarith
  refine ⟨by positivity, ?_, ?_⟩
  · rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  · field_simp

/-- CFS23 exact plateau: `ψ_e(f p) = 1` on the joint inner region `{|η_i| < 6Δ, t < 6Δ}`. -/
theorem cfs23_plateau (hχ : ContDiff ℝ ∞ χ) (hχ0 : ∀ t ≤ 0, χ t = 0)
    (hχ1 : ∀ t, 1 ≤ t → χ t = 1) (hχI : ∀ t, χ t ∈ Icc (0 : ℝ) 1) (hχmono : Monotone χ)
    {P : ℝ} (hP1 : 1 ≤ P) (hP : ∀ t, |deriv χ t| ≤ P) (N : ℕ) (hu : ∀ i, ‖u i‖ ≤ 1)
    (hv : ∀ i, ‖v i‖ ≤ 1) (hxρ : ‖xρ‖ ≤ 1) (hx1 : ‖x1‖ ≤ 1) (hx2 : ‖x2‖ ≤ 1)
    {X : Type*} (hΔ : 1 ≤ Δ) (hR : ∀ i, 0 < R i) (ρ : X → ℝ) (hρ : ∀ p, 0 < ρ p)
    (U : I → Set X) (η : ∀ i, X → E i) (ζ : I → X → ℝ) (F f : X → H)
    (hblock : ∀ i p, u i (F p) = (R i * ζ i p) • η i p ∧ v i (F p) = R i * ζ i p)
    (hcomp : ∀ i p, 0 < ζ i p → 3 / 4 * R i ≤ ρ p ∧ ρ p ≤ 5 / 4 * R i ∧ ‖η i p‖ ≤ 9 * Δ)
    (hpert : ∀ p, ‖f p - F p‖ ≤ 4 * (1 / (1000 * ((N : ℝ) + 1) * P ^ 2)) / 5 * ρ p)
    (t : X → ℝ) (h : ℝ → ℝ) (hhI : ∀ s, h s ∈ Icc (0 : ℝ) 1) (hxρF : ∀ p, xρ (F p) = ρ p)
    (hedgeblock : ∀ p, (∃ i, p ∈ U i) →
      ‖x1 (F p)‖ = ρ p * t p * (h (t p / Δ) * cfsRamp χ (1 / 2) 1 (∑ i, ζ i p)) ∧
      x2 (F p) = ρ p * (h (t p / Δ) * cfsRamp χ (1 / 2) 1 (∑ i, ζ i p)))
    (hedge : ∀ i p, p ∈ U i → ‖η i p‖ < 8 * Δ → ζ i p = 1 - cfsRamp χ 8 9 (t p / Δ))
    (p : X) (i : I) (hpU : p ∈ U i) (hη6 : ‖η i p‖ < 6 * Δ) (ht6 : t p < 6 * Δ) :
    cfsBufferedEdgeCutoff χ Δ R u v xρ x1 x2 (f p) = 1 := by
  obtain ⟨hκpos, hκsmall, hκNP⟩ := cfs_kappa_facts hP1 N
  set κ : ℝ := 1 / (1000 * ((N : ℝ) + 1) * P ^ 2) with hκdef
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hPκ : P * κ ≤ 1 / 1000 := by
    have hPP : 1 * P ≤ P * P := mul_le_mul_of_nonneg_right hP1 (by linarith)
    have h1 : P * κ ≤ ((N : ℝ) + 1) * P ^ 2 * κ := by
      apply mul_le_mul_of_nonneg_right _ hκpos.le
      have hNP2 : 0 ≤ (N : ℝ) * P ^ 2 := by positivity
      linarith
    linarith
  have hΔ0 : 0 < Δ := by linarith
  have hρp := hρ p
  have hRi := hR i
  -- the full marker of the witness
  have hζ1 : ζ i p = 1 := by
    rw [hedge i p hpU (by linarith), cfsRamp_eq_zero hχ0 (by norm_num) ?_, sub_zero]
    rw [div_le_iff₀ hΔ0]
    linarith
  obtain ⟨hu1, hv1⟩ := hblock i p
  rw [hζ1, mul_one] at hu1 hv1
  have hc := (hcomp i p (by rw [hζ1]; norm_num)).2.1
  set e := ‖f p - F p‖ with he_def
  have he0 : 0 ≤ e := norm_nonneg _
  have he : e ≤ 4 * κ / 5 * ρ p := hpert p
  have heR : e ≤ κ * R i := by
    calc e ≤ 4 * κ / 5 * ρ p := he
      _ ≤ 4 * κ / 5 * (5 / 4 * R i) := by gcongr
      _ = κ * R i := by ring
  have heρ : e ≤ ρ p / 1000 := by
    have : 4 * κ / 5 * ρ p ≤ 1 / 1000 * ρ p := by
      apply mul_le_mul_of_nonneg_right _ hρp.le
      linarith
    linarith
  -- the axis gate of the witness equals one
  have hvdiff := cfs_abs_clm_sub_le (v i) (hv i) (f p) (F p)
  rw [hv1] at hvdiff
  have hvf_lo : R i * (1 - κ) ≤ v i (f p) := by
    have := (abs_le.mp hvdiff).1
    linarith
  have hudiff := cfs_norm_clm_sub_le (u i) (hu i) (f p) (F p)
  have huf : ‖u i (f p)‖ ≤ R i * ‖η i p‖ + κ * R i := by
    have h1 := norm_le_insert' (u i (f p)) (u i (F p))
    rw [hu1, norm_smul, Real.norm_eq_abs, abs_of_pos hRi] at h1
    rw [hu1] at hudiff
    linarith
  have hgate : cfsAxisGate χ Δ (R i) (u i) (v i) (f p) = 1 :=
    cfsAxisGate_eq_one_of_near (u i) (v i) hχ0 hχ1 hRi hΔ hκpos.le hκsmall hvf_lo huf hη6
  -- the edge data
  obtain ⟨hx1F, hx2F⟩ := hedgeblock p ⟨i, hpU⟩
  have hz0I : 0 ≤ h (t p / Δ) * cfsRamp χ (1 / 2) 1 (∑ j, ζ j p) ∧
      h (t p / Δ) * cfsRamp χ (1 / 2) 1 (∑ j, ζ j p) ≤ 1 := by
    obtain ⟨h1a, h1b⟩ := hhI (t p / Δ)
    obtain ⟨h2a, h2b⟩ := cfsRamp_mem_Icc hχI (1 / 2) 1 (∑ j, ζ j p)
    constructor <;> nlinarith
  set z₀ := h (t p / Δ) * cfsRamp χ (1 / 2) 1 (∑ j, ζ j p) with hz₀def
  have hxρdiff := cfs_abs_clm_sub_le xρ hxρ (f p) (F p)
  rw [hxρF] at hxρdiff
  have hx2diff := cfs_abs_clm_sub_le x2 hx2 (f p) (F p)
  rw [hx2F] at hx2diff
  have hx1diff := cfs_norm_clm_sub_le x1 hx1 (f p) (F p)
  have hx1f : ‖x1 (f p)‖ ≤ ρ p * t p * z₀ + e := by
    have h1 := norm_le_insert' (x1 (f p)) (x1 (F p))
    rw [hx1F] at h1
    linarith
  have hxρlo : ρ p - e ≤ xρ (f p) := by linarith [(abs_le.mp hxρdiff).1]
  have hxρhi : xρ (f p) ≤ ρ p + e := by linarith [(abs_le.mp hxρdiff).2]
  have hx2lo : ρ p * z₀ - e ≤ x2 (f p) := by linarith [(abs_le.mp hx2diff).1]
  have hx2hi : x2 (f p) ≤ ρ p * z₀ + e := by linarith [(abs_le.mp hx2diff).2]
  have hxρpos : 0 < xρ (f p) := by linarith
  have hρz0 : 0 ≤ ρ p * z₀ := mul_nonneg hρp.le hz0I.1
  -- the witness summand is at least one
  have hBb : 1 ≤ cfsEdgeGate χ Δ xρ x1 x2 (f p) +
      cfsRamp χ (1 / 8) (1 / 4) (cfsEdgeDefect χ R v xρ x2 i (f p)) := by
    have hBI := cfsEdgeGate_mem_Icc (Δ := Δ) xρ x1 x2 hχI (f p)
    have hbI := cfsRamp_mem_Icc hχI (1 / 8) (1 / 4) (cfsEdgeDefect χ R v xρ x2 i (f p))
    by_cases hz : 3 / 8 ≤ z₀
    · -- the edge gate is saturated
      have hρz : 3 / 8 * ρ p ≤ ρ p * z₀ := by
        have := mul_le_mul_of_nonneg_left hz hρp.le
        linarith
      have hx2pos : 0 < x2 (f p) := by linarith
      have hB1 : cfsEdgeGate χ Δ xρ x1 x2 (f p) = 1 := by
        refine cfsEdgeGate_eq_one xρ x1 x2 hχ0 hχ1 ?_ ?_
        · rw [le_div_iff₀ hxρpos]
          linarith
        · rw [div_le_iff₀ (by positivity)]
          have k1 : t p * (ρ p * z₀) ≤ 6 * Δ * (ρ p * z₀) :=
            mul_le_mul_of_nonneg_right ht6.le hρz0
          have k2 : Δ * (ρ p * z₀ - e) ≤ Δ * x2 (f p) :=
            mul_le_mul_of_nonneg_left hx2lo hΔ0.le
          have k3 : Δ * e ≤ Δ * (ρ p / 1000) := mul_le_mul_of_nonneg_left heρ hΔ0.le
          have k4 : Δ * (3 / 8 * ρ p) ≤ Δ * (ρ p * z₀) := mul_le_mul_of_nonneg_left hρz hΔ0.le
          have k5 : 1 * e ≤ Δ * e := mul_le_mul_of_nonneg_right hΔ he0
          have k6 : ρ p * t p * z₀ = t p * (ρ p * z₀) := by ring
          linarith
      linarith [hbI.1]
    · -- the defect gate is saturated
      rw [not_le] at hz
      have hρz : ρ p * z₀ ≤ 3 / 8 * ρ p := by
        have := mul_le_mul_of_nonneg_left hz.le hρp.le
        linarith
      have hm : 1 - κ ≤ v i (f p) / R i := by
        rw [le_div_iff₀ hRi]
        linarith
      have hm8 : 1 / 8 ≤ v i (f p) / R i := by linarith
      have hsumT : 1 - κ ≤ ∑ j, cfsTrunc χ (v j (f p) / R j) := by
        calc 1 - κ ≤ v i (f p) / R i := hm
          _ = cfsTrunc χ (v i (f p) / R i) := (cfsTrunc_eq_self hχ1 hm8).symm
          _ ≤ ∑ j, cfsTrunc χ (v j (f p) / R j) :=
              Finset.single_le_sum (f := fun j => cfsTrunc χ (v j (f p) / R j))
                (fun j _ => cfsTrunc_nonneg hχ0 hχI _) (Finset.mem_univ i)
      have hZlo : 1 - 2 * P * κ ≤ cfsTruncAggregate χ R v (f p) := by
        have hmono := cfsRamp_monotone hχmono (by norm_num : (1 / 2 : ℝ) < 1) hsumT
        have hlip := abs_cfsRamp_sub_le hχ hP (by norm_num : (1 / 2 : ℝ) < 1) 1 (1 - κ)
        rw [cfsRamp_eq_one (a := 1 / 2) (b := 1) (t := 1) hχ1 (by norm_num) le_rfl,
          show (1 : ℝ) - (1 - κ) = κ by ring, abs_of_pos hκpos] at hlip
        have hlip' := (abs_le.mp hlip).2
        have hZdef : cfsTruncAggregate χ R v (f p) =
            cfsRamp χ (1 / 2) 1 (∑ j, cfsTrunc χ (v j (f p) / R j)) := rfl
        rw [hZdef]
        have h2P : P / (1 - 1 / 2) * κ = 2 * P * κ := by ring
        calc 1 - 2 * P * κ = 1 - P / (1 - 1 / 2) * κ := by rw [h2P]
          _ ≤ cfsRamp χ (1 / 2) 1 (1 - κ) := by linarith [hlip']
          _ ≤ _ := hmono
      have hvE : x2 (f p) / xρ (f p) ≤ 1 / 2 := by
        rw [div_le_iff₀ hxρpos]
        linarith
      have hd : 1 / 4 ≤ cfsEdgeDefect χ R v xρ x2 i (f p) := by
        have hZ0 : 0 ≤ 1 - 2 * P * κ := by linarith
        have hm0 : 0 ≤ 1 - κ := by linarith
        have hprod : (1 - κ) * (1 - 2 * P * κ) ≤
            v i (f p) / R i * cfsTruncAggregate χ R v (f p) :=
          mul_le_mul hm hZlo hZ0 (by linarith)
        have hexp : 1 - κ - 2 * P * κ ≤ (1 - κ) * (1 - 2 * P * κ) := by
          have : 0 ≤ 2 * P * κ * κ := by positivity
          linarith
        have hdef : cfsEdgeDefect χ R v xρ x2 i (f p) =
            v i (f p) / R i * cfsTruncAggregate χ R v (f p) - x2 (f p) / xρ (f p) := rfl
        rw [hdef]
        linarith
      have hb1 : cfsRamp χ (1 / 8) (1 / 4) (cfsEdgeDefect χ R v xρ x2 i (f p)) = 1 :=
        cfsRamp_eq_one hχ1 (by norm_num) hd
      linarith [hBI.1]
  have hsum : 1 ≤ ∑ j, cfsEdgeSummand χ Δ R u v xρ x1 x2 j (f p) := by
    calc (1 : ℝ) ≤ cfsEdgeSummand χ Δ R u v xρ x1 x2 i (f p) := by
          rw [cfsEdgeSummand, hgate, one_mul]
          exact hBb
      _ ≤ ∑ j, cfsEdgeSummand χ Δ R u v xρ x1 x2 j (f p) :=
          Finset.single_le_sum
            (fun j _ => (cfsEdgeSummand_mem_Icc R u v xρ x1 x2 hχI j (f p)).1)
            (Finset.mem_univ i)
  exact cfsRamp_eq_one hχ1 (by norm_num) (by linarith)

/-- CFS23 closed-support localization: `ψ_e` vanishes on a neighbourhood of `f(p)` unless `p`
lies in the joint outer region `{|η_i| < 7Δ, t < 7Δ}`. -/
theorem cfs23_support (hχ : ContDiff ℝ ∞ χ) (hχ0 : ∀ t ≤ 0, χ t = 0)
    (hχ1 : ∀ t, 1 ≤ t → χ t = 1) (hχI : ∀ t, χ t ∈ Icc (0 : ℝ) 1) (hχmono : Monotone χ)
    {P : ℝ} (hP1 : 1 ≤ P) (hP : ∀ t, |deriv χ t| ≤ P) (N : ℕ) (hu : ∀ i, ‖u i‖ ≤ 1)
    (hv : ∀ i, ‖v i‖ ≤ 1) (hxρ : ‖xρ‖ ≤ 1) (hx1 : ‖x1‖ ≤ 1) (hx2 : ‖x2‖ ≤ 1)
    {X : Type*} (hΔ : 1 ≤ Δ) (hR : ∀ i, 0 < R i) (ρ : X → ℝ) (hρ : ∀ p, 0 < ρ p)
    (U : I → Set X) (η : ∀ i, X → E i) (ζ : I → X → ℝ) (hζI : ∀ i p, ζ i p ∈ Icc (0 : ℝ) 1)
    (F f : X → H) (hζU : ∀ i p, p ∉ U i → ζ i p = 0)
    (hblock : ∀ i p, u i (F p) = (R i * ζ i p) • η i p ∧ v i (F p) = R i * ζ i p)
    (hcount : ∀ p, (Finset.univ.filter fun i => 0 < ζ i p).card ≤ N)
    (hcomp : ∀ i p, 0 < ζ i p → 3 / 4 * R i ≤ ρ p ∧ ρ p ≤ 5 / 4 * R i ∧ ‖η i p‖ ≤ 9 * Δ)
    (hpert : ∀ p, ‖f p - F p‖ ≤ 4 * (1 / (1000 * ((N : ℝ) + 1) * P ^ 2)) / 5 * ρ p)
    (hZM : ∀ i p, ζ i p = 0 → |v i (f p)| ≤ R i / 32)
    (t : X → ℝ) (h : ℝ → ℝ) (hhg : ∀ s, 3 / 10 ≤ s → h s = 1 - cfsRamp χ 8 9 s)
    (hxρF : ∀ p, xρ (F p) = ρ p)
    (hedgeblock : ∀ p, (∃ i, p ∈ U i) →
      ‖x1 (F p)‖ = ρ p * t p * (h (t p / Δ) * cfsRamp χ (1 / 2) 1 (∑ i, ζ i p)) ∧
      x2 (F p) = ρ p * (h (t p / Δ) * cfsRamp χ (1 / 2) 1 (∑ i, ζ i p)))
    (hedge : ∀ i p, p ∈ U i → ‖η i p‖ < 8 * Δ → ζ i p = 1 - cfsRamp χ 8 9 (t p / Δ))
    (p : X) (hp : ¬∃ i, p ∈ U i ∧ ‖η i p‖ < 7 * Δ ∧ t p < 7 * Δ) :
    cfsBufferedEdgeCutoff χ Δ R u v xρ x1 x2 =ᶠ[𝓝 (f p)] fun _ => 0 := by
  obtain ⟨hκpos, hκsmall, hκNP⟩ := cfs_kappa_facts hP1 N
  set κ : ℝ := 1 / (1000 * ((N : ℝ) + 1) * P ^ 2) with hκdef
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hP0 : 0 ≤ P := by linarith
  have hNκ : (N : ℝ) * P ^ 2 * κ ≤ 1 / 1000 := by
    have hP2κ : 0 ≤ P ^ 2 * κ := by positivity
    linarith
  have hΔ0 : 0 < Δ := by linarith
  have hρp := hρ p
  set e := ‖f p - F p‖ with he_def
  have he0 : 0 ≤ e := norm_nonneg _
  have he : e ≤ 4 * κ / 5 * ρ p := hpert p
  have heρ : e ≤ ρ p / 1000 := by
    have : 4 * κ / 5 * ρ p ≤ 1 / 1000 * ρ p := by
      apply mul_le_mul_of_nonneg_right _ hρp.le
      linarith
    linarith
  have heR : ∀ j, 0 < ζ j p → e ≤ κ * R j := by
    intro j hj
    have hc := (hcomp j p hj).2.1
    calc e ≤ 4 * κ / 5 * ρ p := he
      _ ≤ 4 * κ / 5 * (5 / 4 * R j) := by gcongr
      _ = κ * R j := by ring
  have hxρdiff := cfs_abs_clm_sub_le xρ hxρ (f p) (F p)
  rw [hxρF] at hxρdiff
  have hxρlo : ρ p - e ≤ xρ (f p) := by linarith [(abs_le.mp hxρdiff).1]
  have hxρhi : xρ (f p) ≤ ρ p + e := by linarith [(abs_le.mp hxρdiff).2]
  have hxρpos : 0 < xρ (f p) := by linarith
  -- the truncated aggregate at `F p` and its perturbation
  let S : Finset I := Finset.univ.filter fun j => 0 < ζ j p
  have hmF : ∀ j, v j (F p) / R j = ζ j p := fun j => by
    rw [(hblock j p).2, mul_div_cancel_left₀ _ (hR j).ne']
  have hZF : cfsTruncAggregate χ R v (F p) ≤ cfsRamp χ (1 / 2) 1 (∑ j, ζ j p) := by
    have hsum : ∑ j, cfsTrunc χ (v j (F p) / R j) ≤ ∑ j, ζ j p :=
      Finset.sum_le_sum fun j _ => by
        rw [hmF j]
        exact cfsTrunc_le_self hχI (hζI j p).1
    exact cfsRamp_monotone hχmono (by norm_num) hsum
  have hZdiff : |cfsTruncAggregate χ R v (f p) - cfsTruncAggregate χ R v (F p)| ≤
      6 * N * P ^ 2 * κ := by
    have h1 := abs_cfsTruncAggregate_sub_le R v hχ hP (f p) (F p)
    have hterm0 : ∀ j ∉ S,
        |cfsTrunc χ (v j (f p) / R j) - cfsTrunc χ (v j (F p) / R j)| = 0 := by
      intro j hj
      have hζ0 : ζ j p = 0 := by
        have hle := (hζI j p).1
        by_contra hne
        exact hj (Finset.mem_filter.mpr ⟨Finset.mem_univ j, lt_of_le_of_ne hle (Ne.symm hne)⟩)
      have hm1 : v j (f p) / R j ≤ 1 / 16 := by
        rw [div_le_iff₀ (hR j)]
        linarith [(abs_le.mp (hZM j p hζ0)).2, hR j]
      rw [hmF j, hζ0, cfsTrunc_eq_zero hχ0 hm1, cfsTrunc_eq_zero hχ0 (by norm_num), sub_zero,
        abs_zero]
    have hterm1 : ∀ j ∈ S,
        |cfsTrunc χ (v j (f p) / R j) - cfsTrunc χ (v j (F p) / R j)| ≤ (1 + 2 * P) * κ := by
      intro j hj
      have hζpos : 0 < ζ j p := (Finset.mem_filter.mp hj).2
      refine (abs_cfsTrunc_sub_le hχ hχ0 hχ1 hχI hP _ _).trans ?_
      apply mul_le_mul_of_nonneg_left _ (by linarith)
      rw [← sub_div, abs_div, abs_of_pos (hR j), div_le_iff₀ (hR j)]
      exact (cfs_abs_clm_sub_le (v j) (hv j) (f p) (F p)).trans (heR j hζpos)
    have hsum : ∑ j, |cfsTrunc χ (v j (f p) / R j) - cfsTrunc χ (v j (F p) / R j)| ≤
        N * ((1 + 2 * P) * κ) := by
      calc ∑ j, |cfsTrunc χ (v j (f p) / R j) - cfsTrunc χ (v j (F p) / R j)|
          = ∑ j ∈ S, |cfsTrunc χ (v j (f p) / R j) - cfsTrunc χ (v j (F p) / R j)| := by
            refine (Finset.sum_subset (Finset.subset_univ S) fun j _ hj => ?_).symm
            exact hterm0 j hj
        _ ≤ ∑ _j ∈ S, (1 + 2 * P) * κ := Finset.sum_le_sum hterm1
        _ = S.card * ((1 + 2 * P) * κ) := by rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ N * ((1 + 2 * P) * κ) := by
            apply mul_le_mul_of_nonneg_right _ (by positivity)
            exact_mod_cast hcount p
    calc _ ≤ 2 * P * ∑ j, |cfsTrunc χ (v j (f p) / R j) - cfsTrunc χ (v j (F p) / R j)| := h1
      _ ≤ 2 * P * (N * ((1 + 2 * P) * κ)) := mul_le_mul_of_nonneg_left hsum (by positivity)
      _ ≤ 6 * N * P ^ 2 * κ := by
          have hk : 0 ≤ (N : ℝ) * κ := by positivity
          have hPP : 1 * P ≤ P * P := mul_le_mul_of_nonneg_right hP1 hP0
          have h6 : 2 * P * (1 + 2 * P) ≤ 6 * P ^ 2 := by linarith
          calc 2 * P * (N * ((1 + 2 * P) * κ)) = (2 * P * (1 + 2 * P)) * (N * κ) := by ring
            _ ≤ (6 * P ^ 2) * (N * κ) := mul_le_mul_of_nonneg_right h6 hk
            _ = 6 * N * P ^ 2 * κ := by ring
  -- every summand vanishes near `f p`
  have hsummand : ∀ i,
      cfsEdgeSummand χ Δ R u v xρ x1 x2 i =ᶠ[𝓝 (f p)] fun _ => 0 := by
    intro i
    have hRi := hR i
    by_cases hζ0 : ζ i p = 0
    · have hlt : v i (f p) / R i < 1 / 2 := by
        rw [div_lt_iff₀ hRi]
        linarith [(abs_le.mp (hZM i p hζ0)).2]
      filter_upwards [cfsAxisGate_eventually_zero_of_lt (ℓ := Δ) hχ0 (u i) (v i) hlt] with z hz
      simp only [cfsEdgeSummand, hz, zero_mul]
    have hζpos : 0 < ζ i p := lt_of_le_of_ne (hζI i p).1 (Ne.symm hζ0)
    have hpU : p ∈ U i := by
      by_contra hpU
      exact hζ0 (hζU i p hpU)
    obtain ⟨hu1, hv1⟩ := hblock i p
    have hvdiff := cfs_abs_clm_sub_le (v i) (hv i) (f p) (F p)
    rw [hv1] at hvdiff
    have hvw : |v i (f p) - R i * ζ i p| ≤ κ * R i := hvdiff.trans (heR i hζpos)
    by_cases hη7 : 7 * Δ ≤ ‖η i p‖
    · have huw : R i * ζ i p * ‖η i p‖ - κ * R i ≤ ‖u i (f p)‖ := by
        have h1 := norm_sub_norm_le (u i (F p)) (u i (F p) - u i (f p))
        have h2 := (cfs_norm_clm_sub_le (u i) (hu i) (f p) (F p)).trans (heR i hζpos)
        rw [sub_sub_cancel, norm_sub_rev] at h1
        rw [hu1] at h1 h2
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hRi.le hζpos.le)] at h1
        linarith
      filter_upwards [cfsAxisGate_eventually_zero_of_far (u i) (v i) hχ0 hχ1 hRi hΔ hκpos.le
        hκsmall (hζI i p).1 hvw huw hη7] with z hz
      simp only [cfsEdgeSummand, hz, zero_mul]
    rw [not_le] at hη7
    have ht7 : 7 * Δ ≤ t p := by
      by_contra ht
      exact hp ⟨i, hpU, hη7, not_le.mp ht⟩
    have hζg : ζ i p = 1 - cfsRamp χ 8 9 (t p / Δ) := hedge i p hpU (by linarith)
    have ht310 : 3 / 10 ≤ t p / Δ := by
      rw [le_div_iff₀ hΔ0]
      linarith
    have hhζ : h (t p / Δ) = ζ i p := by rw [hhg _ ht310, ← hζg]
    obtain ⟨hx1F, hx2F⟩ := hedgeblock p ⟨i, hpU⟩
    rw [hhζ] at hx1F hx2F
    have hZ0I := cfsRamp_mem_Icc hχI (1 / 2) 1 (∑ j, ζ j p)
    set Z₀ := cfsRamp χ (1 / 2) 1 (∑ j, ζ j p) with hZ₀def
    have hζ1 := (hζI i p).2
    have hz0 : 0 ≤ ζ i p * Z₀ := mul_nonneg hζpos.le hZ0I.1
    have hz1 : ζ i p * Z₀ ≤ 1 := by
      calc ζ i p * Z₀ ≤ 1 * 1 := mul_le_mul hζ1 hZ0I.2 hZ0I.1 zero_le_one
        _ = 1 := one_mul 1
    have hx2diff := cfs_abs_clm_sub_le x2 hx2 (f p) (F p)
    rw [hx2F] at hx2diff
    have hx2lo : ρ p * (ζ i p * Z₀) - e ≤ x2 (f p) := by linarith [(abs_le.mp hx2diff).1]
    have hx2hi : x2 (f p) ≤ ρ p * (ζ i p * Z₀) + e := by linarith [(abs_le.mp hx2diff).2]
    -- the defect gate vanishes near `f p`
    have hb : (fun z => cfsRamp χ (1 / 8) (1 / 4) (cfsEdgeDefect χ R v xρ x2 i z)) =ᶠ[𝓝 (f p)]
        fun _ => 0 := by
      refine cfsRamp_comp_eventually_zero hχ0 (by norm_num)
        (cfsEdgeDefect_contDiffAt R v hχ xρ x2 i hxρpos.ne').continuousAt ?_
      set Zf := cfsTruncAggregate χ R v (f p) with hZfdef
      have hZfI := cfsTruncAggregate_mem_Icc R v hχI (f p)
      have hm : v i (f p) / R i ≤ ζ i p + κ := by
        rw [div_le_iff₀ hRi]
        linarith [(abs_le.mp hvw).2]
      have hZup : Zf ≤ Z₀ + 6 * N * P ^ 2 * κ := by
        linarith [(abs_le.mp hZdiff).2]
      have hvE : ζ i p * Z₀ - 2 * κ ≤ x2 (f p) / xρ (f p) := by
        rw [le_div_iff₀ hxρpos]
        have k1 : ζ i p * Z₀ * xρ (f p) ≤ ζ i p * Z₀ * (ρ p + e) :=
          mul_le_mul_of_nonneg_left hxρhi hz0
        have k2 : ζ i p * Z₀ * e ≤ 1 * e := mul_le_mul_of_nonneg_right hz1 he0
        have k3 : κ * (ρ p - e) ≤ κ * xρ (f p) := mul_le_mul_of_nonneg_left hxρlo hκpos.le
        have k4 : κ * e ≤ 1 / 1000 * e := mul_le_mul_of_nonneg_right hκsmall he0
        have k5 : ρ p * (ζ i p * Z₀) = ζ i p * Z₀ * ρ p := by ring
        linarith
      have k1 : v i (f p) / R i * Zf ≤ (ζ i p + κ) * Zf := mul_le_mul_of_nonneg_right hm hZfI.1
      have k2 : κ * Zf ≤ κ * 1 := mul_le_mul_of_nonneg_left hZfI.2 hκpos.le
      have k3 : ζ i p * Zf ≤ ζ i p * (Z₀ + 6 * N * P ^ 2 * κ) :=
        mul_le_mul_of_nonneg_left hZup hζpos.le
      have k4 : ζ i p * (6 * N * P ^ 2 * κ) ≤ 1 * (6 * N * P ^ 2 * κ) :=
        mul_le_mul_of_nonneg_right hζ1 (by positivity)
      have hdef : cfsEdgeDefect χ R v xρ x2 i (f p) =
          v i (f p) / R i * Zf - x2 (f p) / xρ (f p) := rfl
      rw [hdef]
      linarith
    -- the edge gate vanishes near `f p`
    have hB : cfsEdgeGate χ Δ xρ x1 x2 =ᶠ[𝓝 (f p)] fun _ => 0 := by
      by_cases hvE : x2 (f p) / xρ (f p) < 1 / 8
      · exact cfsEdgeGate_eventually_zero_of_lt xρ x1 x2 hχ0 hxρpos.ne' hvE
      rw [not_lt, le_div_iff₀ hxρpos] at hvE
      have hx2pos : 0 < x2 (f p) := by linarith
      refine cfsEdgeGate_eventually_zero_of_gt xρ x1 x2 hχ1 hΔ0.ne' hx2pos.ne' ?_
      rw [lt_div_iff₀ (by positivity)]
      have hx1f : ρ p * t p * (ζ i p * Z₀) - e ≤ ‖x1 (f p)‖ := by
        have h1 := norm_sub_norm_le (x1 (F p)) (x1 (F p) - x1 (f p))
        have h2 := cfs_norm_clm_sub_le x1 hx1 (f p) (F p)
        rw [sub_sub_cancel, norm_sub_rev] at h1
        rw [hx1F] at h1
        linarith
      have hρz0 : 0 ≤ ρ p * (ζ i p * Z₀) := mul_nonneg hρp.le hz0
      have k1 : 7 * Δ * (ρ p * (ζ i p * Z₀)) ≤ t p * (ρ p * (ζ i p * Z₀)) :=
        mul_le_mul_of_nonneg_right ht7 hρz0
      have k2 : Δ * x2 (f p) ≤ Δ * (ρ p * (ζ i p * Z₀) + e) :=
        mul_le_mul_of_nonneg_left hx2hi hΔ0.le
      have hρzlo : (ρ p - e) / 8 - e ≤ ρ p * (ζ i p * Z₀) := by linarith
      have k3 : Δ * ((ρ p - e) / 8 - e) ≤ Δ * (ρ p * (ζ i p * Z₀)) :=
        mul_le_mul_of_nonneg_left hρzlo hΔ0.le
      have k4 : Δ * e ≤ Δ * (ρ p / 1000) := mul_le_mul_of_nonneg_left heρ hΔ0.le
      have k5 : 1 * e ≤ Δ * e := mul_le_mul_of_nonneg_right hΔ he0
      have k6 : 0 < Δ * ρ p := mul_pos hΔ0 hρp
      have k7 : ρ p * t p * (ζ i p * Z₀) = t p * (ρ p * (ζ i p * Z₀)) := by ring
      linarith
    filter_upwards [hb, hB] with z hz1 hz2
    simp only [cfsEdgeSummand]
    rw [hz2, hz1, add_zero, mul_zero]
  have hall : ∀ᶠ z in 𝓝 (f p), ∀ i, cfsEdgeSummand χ Δ R u v xρ x1 x2 i z = 0 :=
    Filter.eventually_all.mpr hsummand
  filter_upwards [hall] with z hz
  simp only [cfsBufferedEdgeCutoff, hz, Finset.sum_const_zero]
  exact cfsRamp_eq_zero hχ0 (by norm_num) (by norm_num)

/-- CFS23 derivative bound: every point of the segment from `F p` to `f p` lies in
`O = {x_ρ > 0}` and `‖Dψ_e‖ ≤ C₀ / ρ(p)` there, `C₀ = 10⁴ (N+1)² P⁴`. -/
theorem cfs23_segment (hχ : ContDiff ℝ ∞ χ) (hχ0 : ∀ t ≤ 0, χ t = 0)
    (hχ1 : ∀ t, 1 ≤ t → χ t = 1) (hχI : ∀ t, χ t ∈ Icc (0 : ℝ) 1) {P : ℝ} (hP1 : 1 ≤ P)
    (hP : ∀ t, |deriv χ t| ≤ P) (N : ℕ) (hu : ∀ i, ‖u i‖ ≤ 1) (hv : ∀ i, ‖v i‖ ≤ 1)
    (hxρ : ‖xρ‖ ≤ 1) (hx1 : ‖x1‖ ≤ 1) (hx2 : ‖x2‖ ≤ 1) {X : Type*} (hΔ : 1 ≤ Δ)
    (hR : ∀ i, 0 < R i) (ρ : X → ℝ) (hρ : ∀ p, 0 < ρ p) (ζ : I → X → ℝ)
    (hζI : ∀ i p, ζ i p ∈ Icc (0 : ℝ) 1) (F f : X → H)
    (hvblock : ∀ i p, v i (F p) = R i * ζ i p)
    (hcount : ∀ p, (Finset.univ.filter fun i => 0 < ζ i p).card ≤ N)
    (hscale : ∀ i p, 0 < ζ i p → ρ p ≤ 5 / 4 * R i)
    (hpert : ∀ p, ‖f p - F p‖ ≤ 4 * (1 / (1000 * ((N : ℝ) + 1) * P ^ 2)) / 5 * ρ p)
    (hZM : ∀ i p, ζ i p = 0 → |v i (f p)| ≤ R i / 32) (hxρF : ∀ p, xρ (F p) = ρ p)
    (hx2F : ∀ i p, 0 < ζ i p → |x2 (F p)| ≤ ρ p) (p : X) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    0 < xρ ((1 - s) • F p + s • f p) ∧
      ‖fderiv ℝ (cfsBufferedEdgeCutoff χ Δ R u v xρ x1 x2) ((1 - s) • F p + s • f p)‖ ≤
        10 ^ 4 * ((N : ℝ) + 1) ^ 2 * P ^ 4 / ρ p := by
  obtain ⟨hκpos, hκsmall, hκNP⟩ := cfs_kappa_facts hP1 N
  set κ : ℝ := 1 / (1000 * ((N : ℝ) + 1) * P ^ 2) with hκdef
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hP0 : 0 ≤ P := by linarith
  have hΔ0 : 0 < Δ := by linarith
  have hρp := hρ p
  set z := (1 - s) • F p + s • f p with hzdef
  set e := ‖f p - F p‖ with he_def
  have he : e ≤ 4 * κ / 5 * ρ p := hpert p
  have heρ : e ≤ ρ p / 1000 := by
    have : 4 * κ / 5 * ρ p ≤ 1 / 1000 * ρ p := by
      apply mul_le_mul_of_nonneg_right _ hρp.le
      linarith
    linarith
  have hzF : ‖z - F p‖ ≤ e := cfs_norm_segment_sub_le hs (F p) (f p)
  have hxρz := cfs_abs_clm_sub_le xρ hxρ z (F p)
  rw [hxρF] at hxρz
  have hzr : ρ p ≤ 2 * xρ z := by linarith [(abs_le.mp hxρz).1]
  have hxpos : 0 < xρ z := by linarith
  refine ⟨hxpos, ?_⟩
  let S : Finset I := Finset.univ.filter fun i => 0 < ζ i p
  have hζ0 : ∀ i ∉ S, ζ i p = 0 := by
    intro i hi
    have hle := (hζI i p).1
    by_contra hne
    exact hi (Finset.mem_filter.mpr ⟨Finset.mem_univ i, lt_of_le_of_ne hle (Ne.symm hne)⟩)
  have hmout : ∀ i ∉ S, v i z / R i < 1 / 16 := by
    intro i hi
    have hvz : v i z = s * v i (f p) := by
      rw [hzdef, map_add, map_smul, map_smul, hvblock, hζ0 i hi, mul_zero, smul_zero, zero_add,
        smul_eq_mul]
    rw [div_lt_iff₀ (hR i), hvz]
    have h := hZM i p (hζ0 i hi)
    have h1 : s * v i (f p) ≤ s * |v i (f p)| := mul_le_mul_of_nonneg_left (le_abs_self _) hs.1
    have h2 : s * |v i (f p)| ≤ 1 * (R i / 32) := mul_le_mul hs.2 h (abs_nonneg _) zero_le_one
    linarith [hR i]
  have hin : ∀ i ∈ S, 4 / 5 * ρ p ≤ R i := by
    intro i hi
    have := hscale i p (Finset.mem_filter.mp hi).2
    linarith
  have hZd : ‖fderiv ℝ (cfsTruncAggregate χ R v) z‖ ≤ 8 * N * P ^ 2 / ρ p :=
    norm_fderiv_cfsTruncAggregate_le R v hχ hχ0 hχ1 hχI hP1 hP hv hR S (hcount p) hρp hmout hin
  have hD0 : ∀ i ∉ S, fderiv ℝ (cfsEdgeSummand χ Δ R u v xρ x1 x2 i) z = 0 := by
    intro i hi
    have hlt : v i z / R i < 1 / 2 := by linarith [hmout i hi]
    have hev : cfsEdgeSummand χ Δ R u v xρ x1 x2 i =ᶠ[𝓝 z] fun _ => 0 := by
      filter_upwards [cfsAxisGate_eventually_zero_of_lt (ℓ := Δ) hχ0 (u i) (v i) hlt] with w hw
      simp only [cfsEdgeSummand, hw, zero_mul]
    rw [hev.fderiv_eq, fderiv_const_apply]
  have hD1 : ∀ i ∈ S, ‖fderiv ℝ (cfsEdgeSummand χ Δ R u v xρ x1 x2 i) z‖ ≤
      700 * ((N : ℝ) + 1) * P ^ 3 / ρ p := by
    intro i hi
    have hζpos : 0 < ζ i p := (Finset.mem_filter.mp hi).2
    have hc := hscale i p hζpos
    have hRi := hR i
    have heR : e ≤ κ * R i := by
      calc e ≤ 4 * κ / 5 * ρ p := he
        _ ≤ 4 * κ / 5 * (5 / 4 * R i) := by gcongr
        _ = κ * R i := by ring
    have hx2z : |x2 z| ≤ 2 * ρ p := by
      have h1 := (cfs_abs_clm_sub_le x2 hx2 z (F p)).trans hzF
      have h2 := hx2F i p hζpos
      have h3 := abs_sub_abs_le_abs_sub (x2 z) (x2 (F p))
      linarith
    have hm : |v i z / R i| ≤ 2 := by
      have h1 := (cfs_abs_clm_sub_le (v i) (hv i) z (F p)).trans (hzF.trans heR)
      rw [hvblock] at h1
      have h2 := abs_sub_abs_le_abs_sub (v i z) (R i * ζ i p)
      rw [abs_of_nonneg (mul_nonneg hRi.le hζpos.le)] at h2
      have hζ1 := (hζI i p).2
      rw [abs_div, abs_of_pos hRi, div_le_iff₀ hRi]
      have : R i * ζ i p ≤ R i * 1 := mul_le_mul_of_nonneg_left hζ1 hRi.le
      have : κ * R i ≤ 1 / 1000 * R i := mul_le_mul_of_nonneg_right hκsmall hRi.le
      linarith
    -- the derivative of each factor
    have hgd : ‖fderiv ℝ (cfsAxisGate χ Δ (R i) (u i) (v i)) z‖ ≤ 75 / 2 * P / ρ p := by
      refine (norm_fderiv_cfsAxisGate_le hχ hχ0 hχ1 hχI (u i) (v i) hP1 hP (hu i) (hv i) hRi hΔ
        z).trans ?_
      rw [div_le_div_iff₀ hRi hρp]
      have := mul_le_mul_of_nonneg_left hc (by positivity : (0 : ℝ) ≤ 30 * P)
      linarith
    have hBd := norm_fderiv_cfsEdgeGate_le xρ x1 x2 hχ hχ0 hχ1 hχI hP hxρ hx1 hx2 hΔ hρp hzr hx2z
    have hdd := norm_fderiv_cfsEdgeDefect_le R v hχ hχI hv hR xρ x2 hxρ hx2 i hρp hzr hx2z hm hZd
    have hdd' : ‖fderiv ℝ (cfsEdgeDefect χ R v xρ x2 i) z‖ ≤ 30 * ((N : ℝ) + 1) * P ^ 2 / ρ p := by
      have h1R : 1 / R i ≤ 5 / 4 / ρ p := by
        rw [div_le_div_iff₀ hRi hρp]
        linarith
      have hP2 : 1 ≤ P ^ 2 := by
        have : 1 * 1 ≤ P * P := mul_le_mul hP1 hP1 zero_le_one hP0
        linarith
      have hNP2 : 0 ≤ (N : ℝ) * P ^ 2 := by positivity
      calc _ ≤ 2 * (8 * N * P ^ 2 / ρ p) + 1 / R i + 10 / ρ p := hdd
        _ ≤ 2 * (8 * N * P ^ 2 / ρ p) + 5 / 4 / ρ p + 10 / ρ p := by linarith
        _ = (16 * N * P ^ 2 + 45 / 4) / ρ p := by ring
        _ ≤ 30 * ((N : ℝ) + 1) * P ^ 2 / ρ p := by
            apply div_le_div_of_nonneg_right _ hρp.le
            linarith
    have hddiff : DifferentiableAt ℝ (cfsEdgeDefect χ R v xρ x2 i) z :=
      (cfsEdgeDefect_contDiffAt R v hχ xρ x2 i hxpos.ne').differentiableAt (by simp)
    have hbd : ‖fderiv ℝ (fun w => cfsRamp χ (1 / 8) (1 / 4) (cfsEdgeDefect χ R v xρ x2 i w)) z‖ ≤
        P / (1 / 4 - 1 / 8) * (30 * ((N : ℝ) + 1) * P ^ 2 / ρ p) :=
      cfs_norm_fderiv_ramp_comp_le (a := 1 / 8) (b := 1 / 4) hχ hP (by norm_num) hddiff hdd'
    have hBdiff : DifferentiableAt ℝ (cfsEdgeGate χ Δ xρ x1 x2) z :=
      (cfsEdgeGate_contDiffAt xρ x1 x2 hχ hχ0 hΔ0.ne' hxpos).differentiableAt (by simp)
    have hbdiff : DifferentiableAt ℝ
        (fun w => cfsRamp χ (1 / 8) (1 / 4) (cfsEdgeDefect χ R v xρ x2 i w)) z :=
      (hasDerivAt_cfsRamp hχ _ _ _).differentiableAt.comp z hddiff
    have hBbdiff : DifferentiableAt ℝ (fun w => cfsEdgeGate χ Δ xρ x1 x2 w +
        cfsRamp χ (1 / 8) (1 / 4) (cfsEdgeDefect χ R v xρ x2 i w)) z := hBdiff.add hbdiff
    have hBbnorm : ‖fderiv ℝ (fun w => cfsEdgeGate χ Δ xρ x1 x2 w +
        cfsRamp χ (1 / 8) (1 / 4) (cfsEdgeDefect χ R v xρ x2 i w)) z‖ ≤
        300 * P / ρ p + P / (1 / 4 - 1 / 8) * (30 * ((N : ℝ) + 1) * P ^ 2 / ρ p) := by
      rw [fderiv_fun_add hBdiff hbdiff]
      exact (norm_add_le _ _).trans (add_le_add hBd hbd)
    have hgdiff : DifferentiableAt ℝ (cfsAxisGate χ Δ (R i) (u i) (v i)) z :=
      (cfsAxisGate_contDiff hχ hχ0 hχ1 (u i) (v i) hRi hΔ0).differentiable (by simp) z
    have hgI := cfsAxisGate_mem_Icc (ℓ := Δ) (R := R i) hχI (u i) (v i) z
    have hgabs : |cfsAxisGate χ Δ (R i) (u i) (v i) z| ≤ 1 := by
      rw [abs_le]
      constructor <;> linarith [hgI.1, hgI.2]
    have hBI := cfsEdgeGate_mem_Icc (Δ := Δ) xρ x1 x2 hχI z
    have hbI := cfsRamp_mem_Icc hχI (1 / 8) (1 / 4) (cfsEdgeDefect χ R v xρ x2 i z)
    have hBbabs : |cfsEdgeGate χ Δ xρ x1 x2 z +
        cfsRamp χ (1 / 8) (1 / 4) (cfsEdgeDefect χ R v xρ x2 i z)| ≤ 2 := by
      rw [abs_le]
      constructor <;> linarith [hBI.1, hBI.2, hbI.1, hbI.2]
    have hprod := cfs_norm_fderiv_mul_le hgdiff hBbdiff hgabs hBbabs hgd hBbnorm
    have hsfun : cfsEdgeSummand χ Δ R u v xρ x1 x2 i = fun w =>
        cfsAxisGate χ Δ (R i) (u i) (v i) w * (cfsEdgeGate χ Δ xρ x1 x2 w +
          cfsRamp χ (1 / 8) (1 / 4) (cfsEdgeDefect χ R v xρ x2 i w)) := rfl
    rw [hsfun]
    refine hprod.trans ?_
    have hP3 : P ≤ P ^ 3 := by
      have h1 : 1 * 1 ≤ P * P := mul_le_mul hP1 hP1 zero_le_one hP0
      have h1' : (1 : ℝ) ≤ P * P := by linarith
      have h2 : P * 1 ≤ P * (P * P) := mul_le_mul_of_nonneg_left h1' hP0
      have h3 : P * (P * P) = P ^ 3 := by ring
      linarith
    have hNP3 : P ^ 3 ≤ ((N : ℝ) + 1) * P ^ 3 := by
      have : 0 ≤ (N : ℝ) * P ^ 3 := by positivity
      linarith
    calc 1 * (300 * P / ρ p + P / (1 / 4 - 1 / 8) * (30 * ((N : ℝ) + 1) * P ^ 2 / ρ p)) +
          2 * (75 / 2 * P / ρ p)
        = (375 * P + 240 * ((N : ℝ) + 1) * P ^ 3) / ρ p := by ring
      _ ≤ 700 * ((N : ℝ) + 1) * P ^ 3 / ρ p := by
          apply div_le_div_of_nonneg_right _ hρp.le
          linarith
  -- the sum and the outer ramp
  have hsdiff : ∀ i ∈ (Finset.univ : Finset I),
      DifferentiableAt ℝ (cfsEdgeSummand χ Δ R u v xρ x1 x2 i) z := fun i _ =>
    (cfsEdgeSummand_contDiffAt R u v xρ x1 x2 hχ hχ0 hχ1 hR hΔ0 i hxpos).differentiableAt
      (by simp)
  have hsumnorm : ‖fderiv ℝ (fun w => ∑ i, cfsEdgeSummand χ Δ R u v xρ x1 x2 i w) z‖ ≤
      N * (700 * ((N : ℝ) + 1) * P ^ 3 / ρ p) := by
    rw [fderiv_fun_sum hsdiff]
    calc ‖∑ i, fderiv ℝ (cfsEdgeSummand χ Δ R u v xρ x1 x2 i) z‖
        ≤ ∑ i, ‖fderiv ℝ (cfsEdgeSummand χ Δ R u v xρ x1 x2 i) z‖ := norm_sum_le _ _
      _ = ∑ i ∈ S, ‖fderiv ℝ (cfsEdgeSummand χ Δ R u v xρ x1 x2 i) z‖ := by
          refine (Finset.sum_subset (Finset.subset_univ S) fun i _ hi => ?_).symm
          rw [hD0 i hi, norm_zero]
      _ ≤ ∑ _i ∈ S, 700 * ((N : ℝ) + 1) * P ^ 3 / ρ p := Finset.sum_le_sum hD1
      _ = S.card * (700 * ((N : ℝ) + 1) * P ^ 3 / ρ p) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ N * (700 * ((N : ℝ) + 1) * P ^ 3 / ρ p) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          exact_mod_cast hcount p
  have hψfun : cfsBufferedEdgeCutoff χ Δ R u v xρ x1 x2 =
      fun w => cfsRamp χ (1 / 4) (1 / 2) (∑ i, cfsEdgeSummand χ Δ R u v xρ x1 x2 i w) := rfl
  rw [hψfun]
  refine (cfs_norm_fderiv_ramp_comp_le (a := 1 / 4) (b := 1 / 2) hχ hP (by norm_num)
    (DifferentiableAt.fun_sum hsdiff) hsumnorm).trans ?_
  calc P / (1 / 2 - 1 / 4) * (N * (700 * ((N : ℝ) + 1) * P ^ 3 / ρ p))
      = 2800 * N * ((N : ℝ) + 1) * P ^ 4 / ρ p := by ring
    _ ≤ 10 ^ 4 * ((N : ℝ) + 1) ^ 2 * P ^ 4 / ρ p := by
        apply div_le_div_of_nonneg_right _ hρp.le
        have hk : 0 ≤ ((N : ℝ) + 1) * P ^ 4 := by positivity
        have h1 : 2800 * (N : ℝ) ≤ 10 ^ 4 * ((N : ℝ) + 1) := by linarith
        calc 2800 * (N : ℝ) * ((N : ℝ) + 1) * P ^ 4 = (2800 * (N : ℝ)) * (((N : ℝ) + 1) * P ^ 4) := by
              ring
          _ ≤ (10 ^ 4 * ((N : ℝ) + 1)) * (((N : ℝ) + 1) * P ^ 4) :=
              mul_le_mul_of_nonneg_right h1 hk
          _ = 10 ^ 4 * ((N : ℝ) + 1) ^ 2 * P ^ 4 := by ring

/-- CFS23 (`prop:fibration-uniform-edge-cutoff`, B:3353) in the explicit finite-index form of
external review 39, §5.3: the CFS22 data without the one-axis plateau hypothesis, a monotone
profile, the scale functional `x_ρ` with `x_ρ(F p) = ρ(p)`, the variable edge block
`(‖x'(F p)‖, x''(F p)) = (ρ t z₀, ρ z₀)` on `D = ⋃ U_i` with `z₀ = h(t/Δ) χ_{1/2,1}(Σ ζ_i)`, and
the joint edge identity `ζ_i = 1 − χ_{8,9}(t/Δ)` where `|η_i| < 8Δ` on `U_i`. Conclusions: `ψ_e`
is smooth on `O = {x_ρ > 0}` with values in `[0, 1]`; `ψ_e(f p) = 1` on the joint inner region;
`f p ∈ tsupport ψ_e` only from the joint outer region (closed support, in fact in all of `H`);
every segment point lies in `O` with `‖Dψ_e‖ ≤ 10⁴ (N+1)² P⁴ / ρ(p)`. -/
theorem cfs23_row (hχ : ContDiff ℝ ∞ χ) (hχ0 : ∀ t ≤ 0, χ t = 0)
    (hχ1 : ∀ t, 1 ≤ t → χ t = 1) (hχI : ∀ t, χ t ∈ Icc (0 : ℝ) 1) (hχmono : Monotone χ)
    {P : ℝ} (hP1 : 1 ≤ P) (hP : ∀ t, |deriv χ t| ≤ P) (N : ℕ) (hu : ∀ i, ‖u i‖ ≤ 1)
    (hv : ∀ i, ‖v i‖ ≤ 1) (hxρ : ‖xρ‖ ≤ 1) (hx1 : ‖x1‖ ≤ 1) (hx2 : ‖x2‖ ≤ 1)
    {X : Type*} (hΔ : 1 ≤ Δ) (hR : ∀ i, 0 < R i) (ρ : X → ℝ) (hρ : ∀ p, 0 < ρ p)
    (U : I → Set X) (η : ∀ i, X → E i) (ζ : I → X → ℝ) (hζI : ∀ i p, ζ i p ∈ Icc (0 : ℝ) 1)
    (F f : X → H) (hζU : ∀ i p, p ∉ U i → ζ i p = 0)
    (hblock : ∀ i p, u i (F p) = (R i * ζ i p) • η i p ∧ v i (F p) = R i * ζ i p)
    (hcount : ∀ p, (Finset.univ.filter fun i => 0 < ζ i p).card ≤ N)
    (hcomp : ∀ i p, 0 < ζ i p → 3 / 4 * R i ≤ ρ p ∧ ρ p ≤ 5 / 4 * R i ∧ ‖η i p‖ ≤ 9 * Δ)
    (hpert : ∀ p, ‖f p - F p‖ ≤ 4 * (1 / (1000 * ((N : ℝ) + 1) * P ^ 2)) / 5 * ρ p)
    (hZM : ∀ i p, ζ i p = 0 → |v i (f p)| ≤ R i / 32)
    (t : X → ℝ) (h : ℝ → ℝ) (hhI : ∀ s, h s ∈ Icc (0 : ℝ) 1)
    (hhg : ∀ s, 3 / 10 ≤ s → h s = 1 - cfsRamp χ 8 9 s) (hxρF : ∀ p, xρ (F p) = ρ p)
    (hedgeblock : ∀ p, (∃ i, p ∈ U i) →
      ‖x1 (F p)‖ = ρ p * t p * (h (t p / Δ) * cfsRamp χ (1 / 2) 1 (∑ i, ζ i p)) ∧
      x2 (F p) = ρ p * (h (t p / Δ) * cfsRamp χ (1 / 2) 1 (∑ i, ζ i p)))
    (hedge : ∀ i p, p ∈ U i → ‖η i p‖ < 8 * Δ → ζ i p = 1 - cfsRamp χ 8 9 (t p / Δ)) :
    ContDiffOn ℝ ∞ (cfsBufferedEdgeCutoff χ Δ R u v xρ x1 x2) {z | 0 < xρ z} ∧
      (∀ z, cfsBufferedEdgeCutoff χ Δ R u v xρ x1 x2 z ∈ Icc (0 : ℝ) 1) ∧
      (∀ p, (∃ i, p ∈ U i ∧ ‖η i p‖ < 6 * Δ ∧ t p < 6 * Δ) →
        cfsBufferedEdgeCutoff χ Δ R u v xρ x1 x2 (f p) = 1) ∧
      (∀ p, f p ∈ tsupport (cfsBufferedEdgeCutoff χ Δ R u v xρ x1 x2) →
        ∃ i, p ∈ U i ∧ ‖η i p‖ < 7 * Δ ∧ t p < 7 * Δ) ∧
      (∀ p, ∀ s ∈ Icc (0 : ℝ) 1, 0 < xρ ((1 - s) • F p + s • f p) ∧
        ‖fderiv ℝ (cfsBufferedEdgeCutoff χ Δ R u v xρ x1 x2) ((1 - s) • F p + s • f p)‖ ≤
          10 ^ 4 * ((N : ℝ) + 1) ^ 2 * P ^ 4 / ρ p) := by
  have hΔ0 : 0 < Δ := by linarith
  refine ⟨cfsBufferedEdgeCutoff_contDiffOn R u v xρ x1 x2 hχ hχ0 hχ1 hR hΔ0,
    cfsBufferedEdgeCutoff_mem_Icc R u v xρ x1 x2 hχI, ?_, ?_, ?_⟩
  · rintro p ⟨i, hpU, hη6, ht6⟩
    exact cfs23_plateau R u v xρ x1 x2 hχ hχ0 hχ1 hχI hχmono hP1 hP N hu hv hxρ hx1 hx2 hΔ hR ρ
      hρ U η ζ F f hblock hcomp hpert t h hhI hxρF hedgeblock hedge p i hpU hη6 ht6
  · intro p hsupp
    by_contra hnot
    exact (notMem_tsupport_iff_eventuallyEq.mpr (cfs23_support R u v xρ x1 x2 hχ hχ0 hχ1 hχI
      hχmono hP1 hP N hu hv hxρ hx1 hx2 hΔ hR ρ hρ U η ζ hζI F f hζU hblock hcount hcomp hpert
      hZM t h hhg hxρF hedgeblock hedge p hnot)) hsupp
  · intro p s hs
    have hx2F : ∀ i p, 0 < ζ i p → |x2 (F p)| ≤ ρ p := by
      intro i p hζ
      have hpU : p ∈ U i := by
        by_contra hpU
        exact (ne_of_gt hζ) (hζU i p hpU)
      rw [(hedgeblock p ⟨i, hpU⟩).2]
      obtain ⟨h1a, h1b⟩ := hhI (t p / Δ)
      obtain ⟨h2a, h2b⟩ := cfsRamp_mem_Icc hχI (1 / 2) 1 (∑ j, ζ j p)
      have hz0 : 0 ≤ h (t p / Δ) * cfsRamp χ (1 / 2) 1 (∑ j, ζ j p) := mul_nonneg h1a h2a
      have hz1 : h (t p / Δ) * cfsRamp χ (1 / 2) 1 (∑ j, ζ j p) ≤ 1 := by
        calc h (t p / Δ) * cfsRamp χ (1 / 2) 1 (∑ j, ζ j p) ≤ 1 * 1 :=
              mul_le_mul h1b h2b h2a zero_le_one
          _ = 1 := one_mul 1
      rw [abs_of_nonneg (mul_nonneg (hρ p).le hz0)]
      calc ρ p * (h (t p / Δ) * cfsRamp χ (1 / 2) 1 (∑ j, ζ j p)) ≤ ρ p * 1 :=
            mul_le_mul_of_nonneg_left hz1 (hρ p).le
        _ = ρ p := mul_one _
    exact cfs23_segment R u v xρ x1 x2 hχ hχ0 hχ1 hχI hP1 hP N hu hv hxρ hx1 hx2 hΔ hR ρ hρ ζ hζI
      F f (fun i p => (hblock i p).2) hcount (fun i p hζ => (hcomp i p hζ).2.1) hpert hZM hxρF
      hx2F p hs

end Row

end GC.MetricGeometry
