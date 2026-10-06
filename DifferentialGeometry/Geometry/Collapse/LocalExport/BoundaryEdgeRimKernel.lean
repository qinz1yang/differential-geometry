import DifferentialGeometry.Geometry.Collapse.EdgeDisk.HeightQuotient
import DifferentialGeometry.Geometry.Collapse.LocalExport.EdgeCollarConorm

/-!
# G12 / G16 (part b): the numeric kernel of the rim surjectivity (S-BAUG-D)

Closed twin: `Gaf02Chain.edge_height_EH_EDPE`, `Gaf02Chain.edge_homotopy_conorm_EDPE` at `θ = 1`
and `Gaf02Chain.edge_vertical_rank_EDPE` (`Fibration/ActualStageChainEdpHeight.lean`). The kernel
is stated over an arbitrary real vector space `V` (the tangent space of `W°` at the point) and
linear functionals, so that no tangent-space type is ever instantiated in a kernel:

* `norm_toLp_le_abs_add_abs_BAUGD`, `inner_toLp_two_BAUGD`: the Euclidean plane arithmetic;
* `pair_surjective_of_conorm_BAUGD`: a co-norm `> 9/10` of the pair `(dη, dt)` on a set `Sp`, and
  `|dgq − dη| + |dT − dt| < 1/2` on `Sp`, give `(dgq, dT)` onto `ℝ × ℝ`;
* `rim_t_bounds_BAUGD`: the pure-real value analysis (`T = 4Δ` forces `3.9Δ < t < 4.1Δ`);
* `rim_pair_surjective_kernel_BAUGD`: with the normalized EDP03 inputs (`ρ_q/ρ_j`, `|s − ρ| ≤ κρ`,
  `|A − P| < c₃ρ`, the five derivative bounds on `Sp`) and `dt = d(P/ρ)`, `dT = d(A/s)` by the
  quotient rule, `(dgq, dT)` is onto, from the EDP03 kernels `EdgeDisk.edgeHeight_quotient_*`.
-/

set_option autoImplicit false

noncomputable section

open Set

namespace DifferentialGeometry.Geometry.Collapse

/-- A vector of the Euclidean plane is bounded by the sum of its two coordinates. -/
theorem norm_toLp_le_abs_add_abs_BAUGD (x y : ℝ) :
    ‖(WithLp.toLp 2 ![x, y] : EuclideanSpace ℝ (Fin 2))‖ ≤ |x| + |y| := by
  rw [EuclideanSpace.norm_eq, Fin.sum_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Real.norm_eq_abs, sq_abs]
  have h : x ^ 2 + y ^ 2 ≤ (|x| + |y|) ^ 2 := by
    nlinarith [abs_nonneg x, abs_nonneg y, sq_abs x, sq_abs y]
  calc Real.sqrt (x ^ 2 + y ^ 2) ≤ Real.sqrt ((|x| + |y|) ^ 2) := Real.sqrt_le_sqrt h
    _ = |x| + |y| := Real.sqrt_sq (by positivity)

/-- The inner product of a plane vector with a unit vector, in coordinates. -/
theorem inner_toLp_two_BAUGD (x y : ℝ) (ξ : EuclideanSpace ℝ (Fin 2)) :
    inner ℝ (WithLp.toLp 2 ![x, y] : EuclideanSpace ℝ (Fin 2)) ξ = x * ξ 0 + y * ξ 1 := by
  simp only [PiLp.inner_apply, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    RCLike.inner_apply, conj_trivial]
  ring

/-- The inner product of two plane vectors, in coordinates. -/
theorem inner_two_BAUGD (v ξ : EuclideanSpace ℝ (Fin 2)) :
    inner ℝ v ξ = v 0 * ξ 0 + v 1 * ξ 1 := by
  simp only [PiLp.inner_apply, Fin.sum_univ_two, RCLike.inner_apply, conj_trivial]
  ring

/-- **The perturbation step**: a co-norm `> 9/10` of `(dη, dt)` on `Sp` and a perturbation
`|dgq − dη| + |dT − dt| < 1/2` on `Sp` give `(dgq, dT)` onto `ℝ × ℝ`. -/
theorem pair_surjective_of_conorm_BAUGD {V : Type*} [AddCommGroup V] [Module ℝ V] (Sp : Set V)
    (dη dt dgq dT : V →ₗ[ℝ] ℝ)
    (hco : ∀ ξ : EuclideanSpace ℝ (Fin 2), ‖ξ‖ = 1 →
      ∃ W ∈ Sp, 9 / 10 < dη W * ξ 0 + dt W * ξ 1)
    (hpert : ∀ W ∈ Sp, |dgq W - dη W| + |dT W - dt W| < 1 / 2) :
    Function.Surjective (fun W => (dgq W, dT W)) := by
  let A : V →ₗ[ℝ] EuclideanSpace ℝ (Fin 2) :=
    { toFun := fun W => WithLp.toLp 2 ![dgq W, dT W]
      map_add' := fun u v => by
        ext i
        fin_cases i <;> simp
      map_smul' := fun r v => by
        ext i
        fin_cases i <;> simp }
  have hA : Function.Surjective A := by
    refine surjective_of_conorm_pos_EDP6 A fun ξ hξ => ?_
    obtain ⟨W, hW, h9⟩ := hco ξ hξ
    refine ⟨W, ?_⟩
    change 0 < inner ℝ (WithLp.toLp 2 ![dgq W, dT W] : EuclideanSpace ℝ (Fin 2)) ξ
    rw [inner_toLp_two_BAUGD]
    have hξ0 : |ξ 0| ≤ 1 := by
      have := PiLp.norm_apply_le ξ 0
      rw [hξ] at this
      simpa using this
    have hξ1 : |ξ 1| ≤ 1 := by
      have := PiLp.norm_apply_le ξ 1
      rw [hξ] at this
      simpa using this
    have h1 : dgq W * ξ 0 + dT W * ξ 1 =
        (dη W * ξ 0 + dt W * ξ 1) + ((dgq W - dη W) * ξ 0 + (dT W - dt W) * ξ 1) := by ring
    have h2 : |(dgq W - dη W) * ξ 0| ≤ |dgq W - dη W| := by
      rw [abs_mul]
      exact mul_le_of_le_one_right (abs_nonneg _) hξ0
    have h3 : |(dT W - dt W) * ξ 1| ≤ |dT W - dt W| := by
      rw [abs_mul]
      exact mul_le_of_le_one_right (abs_nonneg _) hξ1
    have h4 := hpert W hW
    have h5 := (abs_le.mp h2).1
    have h6 := (abs_le.mp h3).1
    have h7 := neg_abs_le (dgq W - dη W)
    have h8 := neg_abs_le (dT W - dt W)
    rw [h1]
    linarith
  intro y
  obtain ⟨W, hW⟩ := hA (WithLp.toLp 2 ![y.1, y.2])
  refine ⟨W, ?_⟩
  have h0 := congrArg (fun v : EuclideanSpace ℝ (Fin 2) => v 0) hW
  have h1 := congrArg (fun v : EuclideanSpace ℝ (Fin 2) => v 1) hW
  simp only [A, LinearMap.coe_mk, AddHom.coe_mk, Matrix.cons_val_zero,
    Matrix.cons_val_one] at h0 h1
  exact Prod.ext h0 h1

/-- **The rim kernel** (EDP03's (EH) with EDP04's final-time co-norm): in the normalization by the
chart scale `ρ_j`, with `|s − ρ| ≤ κρ`, `|A − P| < c₃ρ`, `0 ≤ t < 5Δ`, `κΔ < 10⁻⁶`, `c₃ < 10⁻⁵`,
the derivative bounds `|ds|, |dρ| ≤ κρ_j`, `|dA − dP| < c₃ρ_j`, `|dP| < 2ρ_j`, `|dgq − dη| < c₃`
on `Sp`, the quotient-rule differentials `dt = d(P/ρ)`, `dT = d(A/s)` and a co-norm `> 9/10` of
`(dη, dt)` on `Sp`: the pair `(dgq, dT)` is onto `ℝ × ℝ`. -/
theorem rim_pair_surjective_kernel_BAUGD {V : Type*} [AddCommGroup V] [Module ℝ V] (Sp : Set V)
    (dη dP dρ dA ds dgq dt dT : V →ₗ[ℝ] ℝ) {ρj ρq Pq Aq sq c₃ κ Δ : ℝ} (hρj : 0 < ρj)
    (hq : 99 / 100 < ρq / ρj) (hS : |sq / ρj - ρq / ρj| ≤ κ * (ρq / ρj))
    (hB : |Aq / ρj - Pq / ρj| < c₃ * (ρq / ρj)) (ht0 : 0 ≤ Pq / ρj / (ρq / ρj))
    (ht : Pq / ρj / (ρq / ρj) < 5 * Δ) (hΔ : 1 ≤ Δ) (hκ : 0 ≤ κ) (hϑ : κ * Δ < 1 / 1000000)
    (hc₃ : c₃ < 1 / 100000)
    (hdt : ∀ W, dt W = ρq⁻¹ * dP W - Pq * (ρq ^ 2)⁻¹ * dρ W)
    (hdT : ∀ W, dT W = sq⁻¹ * dA W - Aq * (sq ^ 2)⁻¹ * ds W)
    (hds : ∀ W ∈ Sp, |ds W| ≤ κ * ρj) (hdρ : ∀ W ∈ Sp, |dρ W| ≤ κ * ρj)
    (hdA : ∀ W ∈ Sp, |dA W - dP W| < c₃ * ρj) (hdP : ∀ W ∈ Sp, |dP W| < 2 * ρj)
    (hdg : ∀ W ∈ Sp, |dgq W - dη W| < c₃)
    (hco : ∀ ξ : EuclideanSpace ℝ (Fin 2), ‖ξ‖ = 1 →
      ∃ W ∈ Sp, 9 / 10 < dη W * ξ 0 + dt W * ξ 1) :
    Function.Surjective (fun W => (dgq W, dT W)) := by
  obtain ⟨hκ1, hSlow, hS98⟩ := EdgeDisk.edgeHeight_aux hq hS hΔ hκ hϑ
  have hq0 : 0 < ρq / ρj := by linarith
  have hρq : 0 < ρq := by
    have := mul_pos hq0 hρj
    rwa [div_mul_cancel₀ _ hρj.ne'] at this
  have hS0 : 0 < sq / ρj := by linarith
  have hsq : 0 < sq := by
    have := mul_pos hS0 hρj
    rwa [div_mul_cancel₀ _ hρj.ne'] at this
  have hc₃0 : 0 < c₃ := by
    have := abs_nonneg (Aq / ρj - Pq / ρj)
    nlinarith
  have hϑ0 : 0 ≤ κ * Δ := mul_nonneg hκ (by linarith)
  refine pair_surjective_of_conorm_BAUGD Sp dη dt dgq dT hco fun W hW => ?_
  have hk := EdgeDisk.edgeHeight_quotient_deriv_lt (V := ℝ) (p := Pq / ρj) (q := ρq / ρj)
    (S := sq / ρj) (B := Aq / ρj) (c₃ := c₃) (κ := κ) (Δ := Δ)
    (dp := dP W / ρj) (dq := dρ W / ρj) (dS := ds W / ρj) (dB := dA W / ρj) hq hS hB ht0 ht hΔ hκ
    hϑ hc₃ ?_ ?_ ?_ ?_
  · have heq : (sq / ρj)⁻¹ • (dA W / ρj - dP W / ρj) +
        ((sq / ρj)⁻¹ - (ρq / ρj)⁻¹) • (dP W / ρj) -
        (Aq / ρj / (sq / ρj) / (sq / ρj)) • (ds W / ρj) +
        (Pq / ρj / (ρq / ρj) / (ρq / ρj)) • (dρ W / ρj) = dT W - dt W := by
      rw [hdT, hdt]
      simp only [smul_eq_mul]
      field_simp
      ring
    rw [heq, Real.norm_eq_abs] at hk
    have := hdg W hW
    linarith
  · rw [Real.norm_eq_abs, abs_div, abs_of_pos hρj, div_le_iff₀ hρj]
    exact hds W hW
  · rw [Real.norm_eq_abs, abs_div, abs_of_pos hρj, div_le_iff₀ hρj]
    exact hdρ W hW
  · rw [Real.norm_eq_abs, ← sub_div, abs_div, abs_of_pos hρj, div_lt_iff₀ hρj]
    exact hdA W hW
  · rw [Real.norm_eq_abs, abs_div, abs_of_pos hρj, div_lt_iff₀ hρj]
    exact hdP W hW

/-- **The pure-real core of the rim analysis** (EDP03's (EH) value and low band with EDP04's
`T = 4Δ`): with `|s − ρ| ≤ κρ`, `|A − A_F| < c₃ρ`, `A_F ≤ P` (and `A_F = P` once `t ≥ .3Δ`),
`t < 4.01Δ`, `κΔ < 10⁻⁶`, `c₃ < 10⁻⁵`: `T = A/s = 4Δ` forces `3.9Δ < t < 4.1Δ` and
`|A − P| < c₃ρ`. -/
theorem rim_t_bounds_BAUGD {ρj ρq Pq Aq sq c₃ κ Δ AF : ℝ} (hρj : 0 < ρj)
    (hq99 : 99 / 100 < ρq / ρj) (hs : |sq - ρq| ≤ κ * ρq) (hAP : AF ≤ Pq)
    (hAerr : |Aq - AF| < c₃ * ρq) (hAFeq : 3 / 10 * Δ ≤ Pq / ρq → AF = Pq) (hPnn : 0 ≤ Pq)
    (ht : Pq / ρq < 401 / 100 * Δ) (hΔ : 1 ≤ Δ) (hκ : 0 ≤ κ) (hϑ : κ * Δ < 1 / 1000000)
    (hc₃ : c₃ < 1 / 100000) (hT : Aq / sq = 4 * Δ) :
    39 / 10 * Δ < Pq / ρq ∧ Pq / ρq < 41 / 10 * Δ ∧ |Aq - Pq| < c₃ * ρq := by
  have hρq : 0 < ρq := by
    have h := mul_pos (by linarith : 0 < ρq / ρj) hρj
    rwa [div_mul_cancel₀ _ hρj.ne'] at h
  have hq0 : 0 < ρq / ρj := by linarith
  have hS : |sq / ρj - ρq / ρj| ≤ κ * (ρq / ρj) := by
    rw [← sub_div, abs_div, abs_of_pos hρj, div_le_iff₀ hρj]
    calc |sq - ρq| ≤ κ * ρq := hs
      _ = κ * (ρq / ρj) * ρj := by field_simp
  have hnorm : Pq / ρj / (ρq / ρj) = Pq / ρq := by field_simp
  have hnormT : Aq / ρj / (sq / ρj) = Aq / sq := by
    have hsq : sq ≠ 0 := by
      intro h0
      rw [h0, div_zero] at hT
      linarith
    field_simp
  have ht0 : 0 ≤ Pq / ρq := div_nonneg hPnn hρq.le
  have hc₃0 : 0 < c₃ := by
    have h0 := abs_nonneg (Aq - AF)
    nlinarith
  have hAerr' : |Aq / ρj - AF / ρj| < c₃ * (ρq / ρj) := by
    rw [← sub_div, abs_div, abs_of_pos hρj, div_lt_iff₀ hρj]
    calc |Aq - AF| < c₃ * ρq := hAerr
      _ = c₃ * (ρq / ρj) * ρj := by field_simp
  -- the low band is excluded by `T = 4Δ`
  have h3 : 3 / 10 * Δ ≤ Pq / ρq := by
    by_contra hlow
    rw [not_le] at hlow
    have hB : Aq / ρj - Pq / ρj < c₃ * (ρq / ρj) := by
      have h1 : Aq / ρj - AF / ρj < c₃ * (ρq / ρj) := (le_abs_self _).trans_lt hAerr'
      have h2 : AF / ρj ≤ Pq / ρj := div_le_div_of_nonneg_right hAP hρj.le
      linarith
    have hl := EdgeDisk.edgeHeight_low_band_lt (p := Pq / ρj) (q := ρq / ρj) (S := sq / ρj)
      (B := Aq / ρj) (c₃ := c₃) (κ := κ) (Δ := Δ) hq99 hS hB (by rw [hnorm]; exact hlow) hΔ hκ
      hϑ hc₃
    rw [hnormT, hT] at hl
    linarith
  have hAF := hAFeq h3
  rw [hAF] at hAerr
  have hB : |Aq / ρj - Pq / ρj| < c₃ * (ρq / ρj) := by
    rw [hAF] at hAerr'
    exact hAerr'
  have hv := EdgeDisk.edgeHeight_quotient_value_lt (p := Pq / ρj) (q := ρq / ρj)
    (S := sq / ρj) (B := Aq / ρj) (c₃ := c₃) (κ := κ) (Δ := Δ) hq99 hS hB
    (by rw [hnorm]; exact ht0) (by rw [hnorm]; linarith) hΔ hκ hϑ
  rw [hnormT, hnorm, hT] at hv
  have hϑ0 : 0 ≤ κ * Δ := mul_nonneg hκ (by linarith)
  have hv' := abs_lt.mp hv
  refine ⟨?_, ?_, hAerr⟩
  · nlinarith [hv'.1, hv'.2]
  · nlinarith [hv'.1, hv'.2]

end DifferentialGeometry.Geometry.Collapse
