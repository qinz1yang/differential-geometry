import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# EDP03 kernel: the full height quotient estimate (and EDP02's height arithmetic)

Frozen blueprint master207B, lemma `lem:fibration-edge-original-buffer-and-height` (EDP03, lines
6837–6947) and lemma `lem:fibration-actual-edge-height-localization` (EDP02, lines 6748–6835).

In `R_i` units put `q = ρ/R_i`, `p = P/R_i` (so the original height is `t = p/q`), `S = s/R_i` and
`B = A/R_i` (so the actual height is `T = B/S`). With `κ = C_ρΛ` and `ϑ = κΔ`:

* `edgeHeight_quotient_hasFDerivAt`: the FULL quotient rule
  `D(T - t) = (DB - Dp)/S + (1/S - 1/q) Dp - (T/S) DS + (t/q) Dq`;
* `edgeHeight_quotient_value_lt`: `|T - t| < 2c₃ + 10ϑ`;
* `edgeHeight_quotient_deriv_lt`: the norm of that derivative is `< 2c₃ + 20ϑ`;
* `edgeHeight_EH`: both are `< h_* = 50(c₃ + ϑ) < 1/1000` (EH);
* `edgeHeight_low_band_lt`: on `t < .3Δ`, `T < .31Δ`;
* EDP02's arithmetic: `edgeBeta_lt` (`β = (1 + 2P₀)·5c₃/4 < 1/1000`),
  `edgeHeight_high_branch_lt` (`t(1 - β) < 4Δ(1 + c₃) + c₃ ⇒ t < 4.01Δ`),
  `edgeHeight_low_branch_lt` (`(.35Δ + c₃)/(1 - c₃) < 4Δ`, also with `3.5Δ`);
* (EDist) arithmetic: `edgeDist_enclosure_lt` (`a ≤ 5 ⇒ < 8`, `a ≤ 4.2 ⇒ < 6`).

The hypotheses are the normalized forms of (SD) (EDP01), (AE) (GAF02) and the Lipschitz bound of the
physical smoothing, used as in the blueprint, except that `‖Dq‖ ≤ Λ` is weakened to `‖Dq‖ ≤ κ`
(`C_ρ ≥ 1`). The binding to the actual `P` (LFR27), `A` (GAF02) and the enclosure (LFR28) is not in
the tree.
-/

set_option autoImplicit false

noncomputable section

open Set Filter
open scoped Topology

namespace DifferentialGeometry.Geometry.Collapse.EdgeDisk

/-- The full quotient rule for `T - t = B/S - p/q`. -/
theorem edgeHeight_quotient_hasFDerivAt {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {p q S B : E → ℝ} {x : E} {dp dq dS dB : E →L[ℝ] ℝ} (hp : HasFDerivAt p dp x)
    (hq : HasFDerivAt q dq x) (hS : HasFDerivAt S dS x) (hB : HasFDerivAt B dB x)
    (hq0 : q x ≠ 0) (hS0 : S x ≠ 0) :
    HasFDerivAt (fun y => B y / S y - p y / q y)
      ((S x)⁻¹ • (dB - dp) + ((S x)⁻¹ - (q x)⁻¹) • dp - (B x / S x / S x) • dS +
        (p x / q x / q x) • dq) x := by
  have hSi : HasFDerivAt (fun y => (S y)⁻¹) ((-(S x ^ 2)⁻¹) • dS) x :=
    (hasDerivAt_inv hS0).comp_hasFDerivAt x hS
  have hqi : HasFDerivAt (fun y => (q y)⁻¹) ((-(q x ^ 2)⁻¹) • dq) x :=
    (hasDerivAt_inv hq0).comp_hasFDerivAt x hq
  have h := (hB.mul hSi).sub (hp.mul hqi)
  have hfun : (fun y => B y / S y - p y / q y) = (fun y => B y * (S y)⁻¹ - p y * (q y)⁻¹) := by
    funext y
    rw [div_eq_mul_inv, div_eq_mul_inv]
  rw [hfun]
  convert h using 1
  ext v
  simp
  field_simp
  ring

section Estimates

variable {p q S B c₃ κ Δ : ℝ}

/-- Common consequences of the normalized hypotheses. -/
theorem edgeHeight_aux (hq : 99 / 100 < q) (hS : |S - q| ≤ κ * q) (hΔ : 1 ≤ Δ) (hκ : 0 ≤ κ)
    (hϑ : κ * Δ < 1 / 1000000) :
    κ < 1 / 1000000 ∧ q * (1 - κ) ≤ S ∧ 98 / 100 < S := by
  have hκ1 : κ < 1 / 1000000 := by nlinarith
  have hSlow : q * (1 - κ) ≤ S := by
    have := (abs_le.mp hS).1
    nlinarith
  refine ⟨hκ1, hSlow, ?_⟩
  nlinarith

/-- (EH), value: `|T - t| < 2c₃ + 10ϑ`. -/
theorem edgeHeight_quotient_value_lt (hq : 99 / 100 < q) (hS : |S - q| ≤ κ * q)
    (hB : |B - p| < c₃ * q) (ht0 : 0 ≤ p / q) (ht : p / q < 5 * Δ) (hΔ : 1 ≤ Δ) (hκ : 0 ≤ κ)
    (hϑ : κ * Δ < 1 / 1000000) :
    |B / S - p / q| < 2 * c₃ + 10 * (κ * Δ) := by
  obtain ⟨hκ1, hSlow, hS98⟩ := edgeHeight_aux hq hS hΔ hκ hϑ
  have hq0 : 0 < q := by linarith
  have hS0 : 0 < S := by linarith
  have hc₃ : 0 < c₃ := by
    have := abs_nonneg (B - p)
    nlinarith
  set t := p / q with ht_def
  have hp : p = t * q := by rw [ht_def]; field_simp
  have key : B / S - t = (B - p + t * (q - S)) / S := by
    rw [hp]
    field_simp
    ring
  rw [key, abs_div, abs_of_pos hS0, div_lt_iff₀ hS0]
  have h1 : |B - p + t * (q - S)| ≤ |B - p| + t * |q - S| := by
    calc |B - p + t * (q - S)| ≤ |B - p| + |t * (q - S)| := abs_add_le _ _
      _ = |B - p| + t * |q - S| := by rw [abs_mul, abs_of_nonneg ht0]
  have h2 : t * |q - S| ≤ 5 * Δ * (κ * q) := by
    rw [abs_sub_comm]
    exact mul_le_mul ht.le hS (abs_nonneg _) (by linarith)
  have h3 : c₃ * q + 5 * Δ * (κ * q) ≤ (2 * c₃ + 10 * (κ * Δ)) * S := by
    have hpos : 0 ≤ 2 * c₃ + 10 * (κ * Δ) := by positivity
    have h4 := mul_le_mul_of_nonneg_left hSlow hpos
    have h5 : 0 ≤ (c₃ + 5 * (κ * Δ)) * q * (1 - 2 * κ) := by
      apply mul_nonneg (mul_nonneg (by positivity) hq0.le)
      linarith
    nlinarith
  linarith

/-- (EH), derivative: the norm of the derivative of `T - t` is `< 2c₃ + 20ϑ`. -/
theorem edgeHeight_quotient_deriv_lt {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {dp dq dS dB : V} (hq : 99 / 100 < q) (hS : |S - q| ≤ κ * q) (hB : |B - p| < c₃ * q)
    (ht0 : 0 ≤ p / q) (ht : p / q < 5 * Δ) (hΔ : 1 ≤ Δ) (hκ : 0 ≤ κ)
    (hϑ : κ * Δ < 1 / 1000000) (hc₃ : c₃ < 1 / 100000) (hdS : ‖dS‖ ≤ κ) (hdq : ‖dq‖ ≤ κ)
    (hdB : ‖dB - dp‖ < c₃) (hdp : ‖dp‖ < 2) :
    ‖S⁻¹ • (dB - dp) + (S⁻¹ - q⁻¹) • dp - (B / S / S) • dS + (p / q / q) • dq‖ <
      2 * c₃ + 20 * (κ * Δ) := by
  obtain ⟨hκ1, hSlow, hS98⟩ := edgeHeight_aux hq hS hΔ hκ hϑ
  have hq0 : 0 < q := by linarith
  have hS0 : 0 < S := by linarith
  have hval := edgeHeight_quotient_value_lt hq hS hB ht0 ht hΔ hκ hϑ
  have hc₃0 : 0 < c₃ := by
    have := abs_nonneg (B - p)
    nlinarith
  -- reciprocal bounds
  have hSi : S⁻¹ < 103 / 100 := by
    rw [inv_lt_comm₀ hS0 (by norm_num)]
    linarith
  have hqi : q⁻¹ < 102 / 100 := by
    rw [inv_lt_comm₀ hq0 (by norm_num)]
    linarith
  have hSi0 : 0 < S⁻¹ := inv_pos.mpr hS0
  have hqi0 : 0 < q⁻¹ := inv_pos.mpr hq0
  -- |T| < 6Δ
  have hT : |B / S| < 6 * Δ := by
    have := abs_sub_abs_le_abs_sub (B / S) (p / q)
    rw [abs_of_nonneg ht0] at this
    nlinarith
  -- the four terms
  have t1 : ‖S⁻¹ • (dB - dp)‖ ≤ c₃ * (103 / 100) := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hSi0, mul_comm]
    exact mul_le_mul hdB.le hSi.le hSi0.le hc₃0.le
  have t2 : ‖(S⁻¹ - q⁻¹) • dp‖ ≤ κ * (103 / 100) * 2 := by
    rw [norm_smul, Real.norm_eq_abs]
    have hdiff : |S⁻¹ - q⁻¹| ≤ κ * S⁻¹ := by
      have hrw : S⁻¹ - q⁻¹ = (q - S) * S⁻¹ * q⁻¹ := by field_simp
      rw [hrw, abs_mul, abs_mul, abs_of_pos hSi0, abs_of_pos hqi0, abs_sub_comm]
      calc |S - q| * S⁻¹ * q⁻¹ ≤ κ * q * S⁻¹ * q⁻¹ := by gcongr
        _ = κ * S⁻¹ := by field_simp
    calc |S⁻¹ - q⁻¹| * ‖dp‖ ≤ (κ * S⁻¹) * 2 := mul_le_mul hdiff hdp.le (norm_nonneg _)
          (mul_nonneg hκ hSi0.le)
      _ ≤ κ * (103 / 100) * 2 := by gcongr
  have t3 : ‖(B / S / S) • dS‖ ≤ 6 * Δ * (103 / 100) * κ := by
    rw [norm_smul, Real.norm_eq_abs, div_eq_mul_inv (B / S) S, abs_mul, abs_of_pos hSi0]
    have h6 : 0 ≤ 6 * Δ := by linarith
    apply mul_le_mul _ hdS (norm_nonneg _) (by positivity)
    exact mul_le_mul hT.le hSi.le hSi0.le h6
  have t4 : ‖(p / q / q) • dq‖ ≤ 5 * Δ * (102 / 100) * κ := by
    rw [norm_smul, Real.norm_eq_abs, div_eq_mul_inv (p / q) q, abs_mul, abs_of_pos hqi0,
      abs_of_nonneg ht0]
    have h5 : 0 ≤ 5 * Δ := by linarith
    apply mul_le_mul _ hdq (norm_nonneg _) (by positivity)
    exact mul_le_mul ht.le hqi.le hqi0.le h5
  have htri : ‖S⁻¹ • (dB - dp) + (S⁻¹ - q⁻¹) • dp - (B / S / S) • dS + (p / q / q) • dq‖ ≤
      ‖S⁻¹ • (dB - dp)‖ + ‖(S⁻¹ - q⁻¹) • dp‖ + ‖(B / S / S) • dS‖ + ‖(p / q / q) • dq‖ := by
    calc _ ≤ ‖S⁻¹ • (dB - dp) + (S⁻¹ - q⁻¹) • dp - (B / S / S) • dS‖ + ‖(p / q / q) • dq‖ :=
          norm_add_le _ _
      _ ≤ ‖S⁻¹ • (dB - dp) + (S⁻¹ - q⁻¹) • dp‖ + ‖(B / S / S) • dS‖ + ‖(p / q / q) • dq‖ := by
          gcongr
          exact norm_sub_le _ _
      _ ≤ _ := by
          gcongr
          exact norm_add_le _ _
  have hkd : κ ≤ κ * Δ := by nlinarith
  have hsum : c₃ * (103 / 100) + κ * (103 / 100) * 2 + 6 * Δ * (103 / 100) * κ +
      5 * Δ * (102 / 100) * κ < 2 * c₃ + 20 * (κ * Δ) := by nlinarith
  linarith

/-- **(EH) of EDP03.** On the band, both `|T - t|` and the norm of `D(T - t)` are less than
`h_* = 50(c₃ + ϑ)`, and `h_* < 1/1000`. -/
theorem edgeHeight_EH {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {dp dq dS dB : V} (hq : 99 / 100 < q) (hS : |S - q| ≤ κ * q) (hB : |B - p| < c₃ * q)
    (ht0 : 0 ≤ p / q) (ht : p / q < 5 * Δ) (hΔ : 1 ≤ Δ) (hκ : 0 ≤ κ)
    (hϑ : κ * Δ < 1 / 1000000) (hc₃ : c₃ < 1 / 100000) (hdS : ‖dS‖ ≤ κ) (hdq : ‖dq‖ ≤ κ)
    (hdB : ‖dB - dp‖ < c₃) (hdp : ‖dp‖ < 2) :
    |B / S - p / q| < 50 * (c₃ + κ * Δ) ∧
      ‖S⁻¹ • (dB - dp) + (S⁻¹ - q⁻¹) • dp - (B / S / S) • dS + (p / q / q) • dq‖ <
        50 * (c₃ + κ * Δ) ∧ 50 * (c₃ + κ * Δ) < 1 / 1000 := by
  have hv := edgeHeight_quotient_value_lt hq hS hB ht0 ht hΔ hκ hϑ
  have hd := edgeHeight_quotient_deriv_lt hq hS hB ht0 ht hΔ hκ hϑ hc₃ hdS hdq hdB hdp
  have hc₃0 : 0 < c₃ := by
    have := abs_nonneg (B - p)
    nlinarith
  have hϑ0 : 0 ≤ κ * Δ := mul_nonneg hκ (by linarith)
  refine ⟨by linarith, by linarith, by linarith⟩

/-- EDP03, low band: if `t < .3Δ` then `T < .31Δ`. Only the upper value bound `B < p + c₃q` is used
(the original auxiliary vector lies between zero and `ρt`). -/
theorem edgeHeight_low_band_lt (hq : 99 / 100 < q) (hS : |S - q| ≤ κ * q) (hB : B - p < c₃ * q)
    (ht : p / q < 3 / 10 * Δ) (hΔ : 1 ≤ Δ) (hκ : 0 ≤ κ) (hϑ : κ * Δ < 1 / 1000000)
    (hc₃ : c₃ < 1 / 100000) :
    B / S < 31 / 100 * Δ := by
  obtain ⟨hκ1, hSlow, hS98⟩ := edgeHeight_aux hq hS hΔ hκ hϑ
  have hq0 : 0 < q := by linarith
  have hS0 : 0 < S := by linarith
  rw [div_lt_iff₀ hS0]
  have hp : p < 3 / 10 * Δ * q := by rwa [div_lt_iff₀ hq0] at ht
  have h1 : (3 / 10 * Δ + c₃) * q ≤ 31 / 100 * Δ * (q * (1 - κ)) := by
    have h2 : 3 / 10 * Δ + c₃ ≤ 31 / 100 * Δ * (1 - κ) := by nlinarith
    nlinarith
  have h3 : 31 / 100 * Δ * (q * (1 - κ)) ≤ 31 / 100 * Δ * S := by
    apply mul_le_mul_of_nonneg_left hSlow
    linarith
  nlinarith

end Estimates

/-- EDP02, (EZ): `β = (1 + 2P₀)·(5c₃/4) < 1/1000` under (SE)'s `c₃ < [10⁵(P₀ + 1)]⁻¹`. -/
theorem edgeBeta_lt {P₀ c₃ : ℝ} (hc : 0 ≤ c₃)
    (hcP : c₃ * (100000 * (P₀ + 1)) < 1) :
    (1 + 2 * P₀) * (5 * c₃ / 4) < 1 / 1000 := by
  nlinarith

/-- EDP02, high branch: `t(1 - β) < 4Δ(1 + c₃) + c₃` forces `t < 4.01Δ`. -/
theorem edgeHeight_high_branch_lt {t β c₃ Δ : ℝ} (hβ : β < 1 / 1000)
    (hc : c₃ < 1 / 100000) (hΔ : 1 ≤ Δ)
    (h : t * (1 - β) < 4 * Δ * (1 + c₃) + c₃) :
    t < 401 / 100 * Δ := by
  by_contra hcon
  rw [not_lt] at hcon
  have h1 : 401 / 100 * Δ * (1 - β) ≤ t * (1 - β) :=
    mul_le_mul_of_nonneg_right hcon (by linarith)
  nlinarith

/-- EDP02, low branch and interior: `(.35Δ + c₃)/(1 - c₃) < 4Δ` and `(3.5Δ + c₃)/(1 - c₃) < 4Δ`. -/
theorem edgeHeight_low_branch_lt {c₃ Δ : ℝ} (hc : c₃ < 1 / 100000)
    (hΔ : 1 ≤ Δ) :
    (35 / 100 * Δ + c₃) / (1 - c₃) < 4 * Δ ∧ (7 / 2 * Δ + c₃) / (1 - c₃) < 4 * Δ := by
  have h1 : 0 < 1 - c₃ := by linarith
  constructor
  · rw [div_lt_iff₀ h1]
    nlinarith
  · rw [div_lt_iff₀ h1]
    nlinarith

/-- (EDist) arithmetic of EDP03: with all original errors at most `10⁻⁸`, the enclosure radius
`√((a + μ)² + (a(1 + λ) + μ + 2τ)²) + τ` is `< 8` for `a ≤ 5` and `< 6` for `a ≤ 4.2`. -/
theorem edgeDist_enclosure_lt {a lam μ τ : ℝ} (ha : 0 ≤ a) (hl0 : 0 ≤ lam)
    (hl : lam ≤ 1 / 100000000) (hμ0 : 0 ≤ μ) (hμ : μ ≤ 1 / 100000000) (hτ0 : 0 ≤ τ)
    (hτ : τ ≤ 1 / 100000000) :
    (a ≤ 5 → Real.sqrt ((a + μ) ^ 2 + (a * (1 + lam) + μ + 2 * τ) ^ 2) + τ < 8) ∧
      (a ≤ 21 / 5 → Real.sqrt ((a + μ) ^ 2 + (a * (1 + lam) + μ + 2 * τ) ^ 2) + τ < 6) := by
  have hal : 0 ≤ a * lam := mul_nonneg ha hl0
  constructor
  · intro h5
    have hsq : Real.sqrt ((a + μ) ^ 2 + (a * (1 + lam) + μ + 2 * τ) ^ 2) < 8 - τ := by
      rw [Real.sqrt_lt' (by linarith)]
      have hx : a * lam ≤ 5 / 100000000 := by nlinarith
      nlinarith
    linarith
  · intro h4
    have hsq : Real.sqrt ((a + μ) ^ 2 + (a * (1 + lam) + μ + 2 * τ) ^ 2) < 6 - τ := by
      rw [Real.sqrt_lt' (by linarith)]
      have hx : a * lam ≤ 5 / 100000000 := by nlinarith
      nlinarith
    linarith

end DifferentialGeometry.Geometry.Collapse.EdgeDisk
