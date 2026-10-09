import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryReplacementPiecesBCF2K
import DifferentialGeometry.Geometry.Collapse.BoundaryEarlyThresholdsBSTD1

/-!
# BCF02's numerical premises: satisfiability, order, and what the boundary register gives

The compactness `BoundaryCompactSlimChoice.isCompact_edgePiece_BCF2K` (lane BCF2-K, G5) takes
register inequalities on the supply's parameters as explicit numerical premises (lead's decision,
13:3x). This file checks them:

* `bcf02_register_thresholds_BCF2K` (ORDER): `Δ` first; `σ(Δ) = bcf02Sigma_BCF2K Δ`,
  `η(Δ) = bcf02Eta_BCF2K Δ` follow; then thresholds `b₀, μ₀, Λ₀ > 0` depending on `Δ` only such
  that every `b < b₀`, `μ < μ₀`, `Λ < Λ₀` meets the requests on `b`, `μ`, `Λ`; the lower requests on
  `T`, `L_max` and the BCP04.a index `n` hold on a tail.
* `bcf02_register_example_BCF2K` (SATISFIABILITY): for every `Δ ≥ 2` there are values of all
  parameters meeting ALL premises at once (all positive).
* `bcf02_register_given_BCF2K` (REGISTER): the premises the early choice `BoundaryEarlyOver_BSTD1`
  already gives (with the fields used): `Δ ≥ 2` (`β₂_pos`, `β₂_lt`, `Δ_gt`), `0 ≤ Λ` (`Λ_pos`),
  `μ ≤ 10⁻⁸` (`μ_le8`), `τ ≤ 10⁻⁸` (`τ_pos`, `τ_sqrt`, `ε_le8`), `0 ≤ σs ≤ 1/100` (`σs_pos`,
  `σs_le`), `b < 10⁻⁶` and `b(2(20Δ + 1)) ≤ 1` (`b_pos`, `b_inv`, with `Δ ≥ 2`), `s < 10⁻⁶`
  (`s_lt_b'`, `b'_lt`), `10⁶ΔΛ < 10⁻⁵` (`Λ_pos`, `Λ_c5`, `s'_lt`). The remaining premises
  (`σc ≤ 1/1000`, `T ≥ 1000Δ`, `β₂ < 10⁻⁶`, `μΔ < 10⁻⁴`, `b ≤ η(Δ)`, `3b ≤ σ(Δ)`,
  `σ(Δ)⁻¹ ≤ L_max`, `1140Δ ≤ 35n`) are NOT given by the register (REGISTER GAP, reported).
-/

set_option autoImplicit false

noncomputable section

open Set Function Filter

namespace DifferentialGeometry.Geometry.Collapse

/-- **The order of BCF02's numerical requests** (`Δ` first, then `σ(Δ)`, `η(Δ)`, then the
thresholds): for `Δ ≥ 2` there are `b₀, μ₀, Λ₀ > 0` (functions of `Δ`) such that every `b < b₀`
has `b < 10⁻⁶`, `b ≤ η(Δ)`, `3b ≤ σ(Δ)`, `b(2(20Δ + 1)) ≤ 1`; every `μ < μ₀` has `μ ≤ 10⁻⁸`,
`μΔ < 10⁻⁴`; every `Λ < Λ₀` has `10⁶ΔΛ < 10⁻⁵`; and the BCP04.a index meets `1140Δ ≤ 35n` on a
tail `n ≥ n₀` (the lower requests `T ≥ 1000Δ`, `L_max ≥ σ(Δ)⁻¹` are free choices after `Δ`). -/
theorem bcf02_register_thresholds_BCF2K {Δ : ℝ} (hΔ : 2 ≤ Δ) :
    ∃ b₀ μ₀ Λ₀ : ℝ, 0 < b₀ ∧ 0 < μ₀ ∧ 0 < Λ₀ ∧
      (∀ b, b < b₀ → b < 1 / 1000000 ∧ b ≤ bcf02Eta_BCF2K Δ ∧ 3 * b ≤ bcf02Sigma_BCF2K Δ ∧
        b * (2 * (20 * Δ + 1)) ≤ 1) ∧
      (∀ μ, μ < μ₀ → μ ≤ 1 / 10 ^ 8 ∧ μ * Δ < 1 / 10000) ∧
      (∀ Λ, Λ < Λ₀ → 1000000 * Δ * Λ < 1 / 100000) ∧
      ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → 1140 * Δ ≤ 35 * (n : ℝ) := by
  obtain ⟨hσ, -, hη, -⟩ := bcf02_constants_spec_BCF2K hΔ
  have hΔ0 : 0 < Δ := by linarith
  have hH : 0 < 2 * (20 * Δ + 1) := by positivity
  set b₀ := min (min (1 / 10 ^ 7) (bcf02Eta_BCF2K Δ)) (min (bcf02Sigma_BCF2K Δ / 3)
    (1 / (2 * (20 * Δ + 1)))) with hb₀
  set μ₀ := min (1 / 10 ^ 8) (1 / (10000 * Δ)) with hμ₀
  set Λ₀ := 1 / (100000000000 * Δ) with hΛ₀
  have hb₀1 : b₀ ≤ 1 / 10 ^ 7 := (min_le_left _ _).trans (min_le_left _ _)
  have hb₀2 : b₀ ≤ bcf02Eta_BCF2K Δ := (min_le_left _ _).trans (min_le_right _ _)
  have hb₀3 : b₀ ≤ bcf02Sigma_BCF2K Δ / 3 := (min_le_right _ _).trans (min_le_left _ _)
  have hb₀4 : b₀ ≤ 1 / (2 * (20 * Δ + 1)) := (min_le_right _ _).trans (min_le_right _ _)
  have hb₀pos : 0 < b₀ :=
    lt_min (lt_min (by norm_num) hη) (lt_min (by linarith) (by positivity))
  have hμ₀1 : μ₀ ≤ 1 / 10 ^ 8 := min_le_left _ _
  have hμ₀2 : μ₀ ≤ 1 / (10000 * Δ) := min_le_right _ _
  have hμ₀pos : 0 < μ₀ := lt_min (by norm_num) (by positivity)
  refine ⟨b₀, μ₀, Λ₀, hb₀pos, hμ₀pos, by positivity, fun b hb => ⟨by linarith, by linarith,
    by linarith, ?_⟩, fun μ hμ => ⟨by linarith, ?_⟩, fun Λ hΛ => ?_, ?_⟩
  · have h := mul_lt_mul_of_pos_right (hb.trans_le hb₀4) hH
    rw [div_mul_cancel₀ _ hH.ne'] at h
    exact h.le
  · have h := mul_lt_mul_of_pos_right (hμ.trans_le hμ₀2) hΔ0
    have he : 1 / (10000 * Δ) * Δ = 1 / 10000 := by field_simp
    linarith
  · have h := mul_lt_mul_of_pos_left hΛ (by positivity : (0 : ℝ) < 1000000 * Δ)
    have he : 1000000 * Δ * (1 / (100000000000 * Δ)) = 1 / 100000 := by
      field_simp
      norm_num
    linarith
  · refine ⟨⌈1140 * Δ / 35⌉₊, fun n hn => ?_⟩
    have h1 : 1140 * Δ / 35 ≤ (n : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hn)
    linarith

/-- **BCF02's numerical premises are satisfiable at once** (for every `Δ ≥ 2`): positive values of
`Λ, μ, τ, σc, σs, b, s, β₂, T, L_max` and an index `n` meeting every numerical premise of
`BoundaryCompactSlimChoice.isCompact_edgePiece_BCF2K` simultaneously. -/
theorem bcf02_register_example_BCF2K {Δ : ℝ} (hΔ : 2 ≤ Δ) :
    ∃ Λ μ τ σc σs b s β₂ T Lmax : ℝ, ∃ n : ℕ,
      0 < Λ ∧ 0 < μ ∧ 0 < τ ∧ 0 < σc ∧ 0 < σs ∧ 0 < b ∧ 0 < s ∧ 0 < β₂ ∧ 0 < Lmax ∧
      0 ≤ Λ ∧ μ ≤ 1 / 10 ^ 8 ∧ τ ≤ 1 / 10 ^ 8 ∧ σc ≤ 1 / 1000 ∧ 1140 * Δ ≤ 35 * (n : ℝ) ∧
      1000 * Δ ≤ T ∧ 0 ≤ σs ∧ σs ≤ 1 / 100 ∧ b < 1 / 1000000 ∧ s < 1 / 1000000 ∧
      β₂ < 1 / 1000000 ∧ (bcf02Sigma_BCF2K Δ)⁻¹ ≤ Lmax ∧ b ≤ bcf02Eta_BCF2K Δ ∧
      3 * b ≤ bcf02Sigma_BCF2K Δ ∧ b * (2 * (20 * Δ + 1)) ≤ 1 ∧
      1000000 * Δ * Λ < 1 / 100000 ∧ μ * Δ < 1 / 10000 := by
  obtain ⟨hσ, -, -, -⟩ := bcf02_constants_spec_BCF2K hΔ
  obtain ⟨b₀, μ₀, Λ₀, hb₀, hμ₀, hΛ₀, hb, hμ, hΛ, n₀, hn⟩ :=
    bcf02_register_thresholds_BCF2K hΔ
  obtain ⟨hb1, hb2, hb3, hb4⟩ := hb (b₀ / 2) (by linarith)
  obtain ⟨hμ1, hμ2⟩ := hμ (μ₀ / 2) (by linarith)
  refine ⟨Λ₀ / 2, μ₀ / 2, 1 / 10 ^ 9, 1 / 2000, 1 / 200, b₀ / 2, 1 / 10 ^ 7, 1 / 10 ^ 7,
    1000 * Δ, (bcf02Sigma_BCF2K Δ)⁻¹, n₀, by positivity, by positivity, by norm_num, by norm_num,
    by norm_num, by positivity, by norm_num, by norm_num, inv_pos.mpr hσ, by positivity, hμ1,
    by norm_num, by norm_num, hn n₀ le_rfl, le_rfl, by norm_num, by norm_num, hb1, by norm_num,
    by norm_num, le_rfl, hb2, hb3, hb4, hΛ (Λ₀ / 2) (by linarith), hμ2⟩

/-- **What the boundary register already gives** (early choice `E : BoundaryEarlyOver_BSTD1 Θ`):
`2 ≤ Δ` (`β₂_pos`, `β₂_lt`, `Δ_gt`), `0 ≤ Λ` (`Λ_pos`), `μ ≤ 10⁻⁸` (`μ_le8`), `τ ≤ 10⁻⁸`
(`τ_pos`, `τ_sqrt`, `ε_le8`), `0 ≤ σs ≤ 1/100` (`σs_pos`, `σs_le`), `b < 10⁻⁶` and
`b(2(20Δ + 1)) ≤ 1` (`b_pos`, `b_inv`), `s < 10⁻⁶` (`s_pos`, `s_lt_b'`, `b'_lt`), `10⁶ΔΛ < 10⁻⁵`
(`Λ_pos`, `Λ_c5`, `s'_lt`). -/
theorem bcf02_register_given_BCF2K {Θ : BoundaryProducerThresholds_BSTD1}
    (E : BoundaryEarlyOver_BSTD1 Θ) :
    2 ≤ E.Δ ∧ 0 ≤ E.Λ ∧ E.μ ≤ 1 / 10 ^ 8 ∧ E.τ ≤ 1 / 10 ^ 8 ∧ 0 ≤ E.σs ∧ E.σs ≤ 1 / 100 ∧
      E.b < 1 / 1000000 ∧ E.b * (2 * (20 * E.Δ + 1)) ≤ 1 ∧ E.s < 1 / 1000000 ∧
      1000000 * E.Δ * E.Λ < 1 / 100000 := by
  have hΔ : 2 ≤ E.Δ := bcf02_register_delta_BCF2K E.β₂_pos E.β₂_lt E.Δ_gt
  have hΔ0 : 0 < E.Δ := by linarith
  have hΔ4 : 10000 < E.Δ := by
    have h : 10000 < 100 / E.β₂ := by
      rw [lt_div_iff₀ E.β₂_pos]
      linarith [E.β₂_lt]
    linarith [E.Δ_gt]
  -- `τ`: `140√τ < ε²/20 ≤ 10⁻¹⁶/20`
  have hτ : E.τ ≤ 1 / 10 ^ 8 := by
    have hε := E.ε_pos
    have hε2 : E.ε ^ 2 ≤ (1 / 10 ^ 8) ^ 2 := pow_le_pow_left₀ hε.le E.ε_le8 2
    have hsq : Real.sqrt E.τ < 1 / 10 ^ 4 := by
      have := E.τ_sqrt
      nlinarith [Real.sqrt_nonneg E.τ]
    have h0 := Real.sqrt_nonneg E.τ
    have hsq2 : Real.sqrt E.τ ^ 2 = E.τ := Real.sq_sqrt E.τ_pos.le
    nlinarith
  -- `b`: `100Δ < b⁻¹`
  have hbΔ : E.b * (100 * E.Δ) < 1 := by
    have h := E.b_inv
    have hb := E.b_pos
    rw [lt_inv_comm₀ (by positivity) hb] at h
    have h2 := mul_lt_mul_of_pos_right h (by positivity : (0 : ℝ) < 100 * E.Δ)
    rw [inv_mul_cancel₀ (by positivity)] at h2
    exact h2
  have hb1 : E.b < 1 / 1000000 := by
    have hb := E.b_pos
    nlinarith
  have hb2 : E.b * (2 * (20 * E.Δ + 1)) ≤ 1 := by
    have hb := E.b_pos
    nlinarith
  -- `s < b'/10⁵`, `b' < 1/(10⁶Δ)`
  have hs : E.s < 1 / 1000000 := by
    have h1 := E.s_lt_b'
    have h2 := E.b'_lt
    have h3 : 1 / (1000000 * E.Δ) ≤ 1 / 2000000 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      linarith
    linarith
  exact ⟨hΔ, E.Λ_pos.le, E.μ_le8, hτ, E.σs_pos.le, E.σs_le, hb1, hb2, hs,
    bcf02_register_lipschitz_BCF2K (by linarith) E.Λ_pos.le E.Λ_c5 E.s'_lt⟩

end DifferentialGeometry.Geometry.Collapse
