import DifferentialGeometry.Geometry.Collapse.BoundaryScale.CuspBallSandwich

/-!
# The collar comparison near the boundary (statement Q)

* `cusp_collar_constant_lt` (interface `Q_constant_lt`): `C_δ = e^{3 h₀} ((1+δ)/(1-δ))³ < 3/2` for
  `0 ≤ δ ≤ 1/1000`, `h₀ = 4/100`, by the exact rational bound `e^{3h₀} ≤ 25/22`,
  `(1+δ)/(1-δ) ≤ 1001/999`, `(25/22)(1001/999)³ < 3/2` (design D5).
* `NearlyCuspidalBoundary.collar_comparison` (interface `Q_collar_comparison`, cross-multiplied in
  `ℝ≥0∞`): for `d(q, ∂W) ≤ 1/100` and `0 < s ≤ b ≤ 1/100`, `V_q(b) s³ ≤ C_δ b³ V_q(s)`.
  Proof: the ball sandwich V.3 at `b` and at `s` (one collar coordinate for both), and the
  antitone ratio `F(ρ)/ρ³` of the flat half-ellipsoid volume (BDY-M,
  `torus_halfProduct_volume_div_cube_antitone`) at `s/λ₊ ≤ b/λ₋`; the constant is
  `(λ₊/λ₋)⁶ = C_δ`.

Q replaces BSA02 only for its current consumers; BSA02 itself stays open (design D5).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Function
open DifferentialGeometry DifferentialGeometry.Integral.Measure GC.Endpoint
open DifferentialGeometry.Geometry.Hyperbolic DifferentialGeometry.Topology.Manifold
open scoped Manifold ContDiff ENNReal Real

namespace DifferentialGeometry.Geometry.Collapse

universe u

variable {W : CompactCarrier.{u}} {g : SmoothRiemannianMetric W.model W.Carrier} {K : ℕ} {δ : ℝ}

/-- `e^{3 h₀} ≤ 25/22` for `h₀ = 4/100` (from `1 - 3h₀ ≤ e^{-3h₀}`). -/
theorem exp_three_mul_four_hundredths_le : Real.exp (3 * (4 / 100)) ≤ 25 / 22 := by
  have h := Real.add_one_le_exp (-(3 * (4 / 100)))
  have hpos := Real.exp_pos (3 * (4 / 100))
  have hmul : Real.exp (3 * (4 / 100)) * Real.exp (-(3 * (4 / 100))) = 1 := by
    rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  nlinarith

/-- **Q.0** (interface `Q_constant_lt`): `C_δ = e^{3 h₀} ((1+δ)/(1-δ))³ < 3/2` for
`0 ≤ δ ≤ 1/1000`, via the exact rational bound `(25/22)(1001/999)³ < 3/2`. -/
theorem cusp_collar_constant_lt (hδ0 : 0 ≤ δ) (hδ : δ ≤ 1 / 1000) :
    Real.exp (3 * (4 / 100)) * ((1 + δ) / (1 - δ)) ^ 3 < 3 / 2 := by
  have hq0 : 0 ≤ (1 + δ) / (1 - δ) := div_nonneg (by linarith) (by linarith)
  have hq : (1 + δ) / (1 - δ) ≤ 1001 / 999 := by
    rw [div_le_div_iff₀ (by linarith) (by norm_num)]
    linarith
  have hq3 : ((1 + δ) / (1 - δ)) ^ 3 ≤ (1001 / 999) ^ 3 := pow_le_pow_left₀ hq0 hq 3
  calc Real.exp (3 * (4 / 100)) * ((1 + δ) / (1 - δ)) ^ 3
      ≤ 25 / 22 * (1001 / 999) ^ 3 :=
        mul_le_mul exp_three_mul_four_hundredths_le hq3 (pow_nonneg hq0 3) (by norm_num)
    _ < 3 / 2 := by norm_num

/-- **Q: collar comparison** (interface `Q_collar_comparison`, replacing BSA02 for its current
consumers): for `d(q, ∂W) ≤ 1/100` and `0 < s ≤ b ≤ 1/100`,
`V_q(b) s³ ≤ C_δ b³ V_q(s)` with `C_δ = e^{3 h₀} ((1+δ)/(1-δ))³ = (λ₊/λ₋)⁶`. -/
theorem NearlyCuspidalBoundary.collar_comparison (B : NearlyCuspidalBoundary W g K δ)
    (hδ0 : 0 ≤ δ) (hδ : δ ≤ 1 / 1000) {q : W.Carrier}
    (hq : distanceToBoundary W g q ≤ ENNReal.ofReal (1 / 100)) {s b : ℝ} (hs : 0 < s)
    (hsb : s ≤ b) (hb : b ≤ 1 / 100) :
    ballVolume g q b * ENNReal.ofReal (s ^ 3) ≤
      ENNReal.ofReal (Real.exp (3 * (4 / 100)) * ((1 + δ) / (1 - δ)) ^ 3 * b ^ 3) *
        ballVolume g q s := by
  obtain ⟨i, x, z₁, hz₁0, -, -, hsand⟩ := B.ball_sandwich hδ0 hδ hq
  have hb0 : 0 < b := hs.trans_le hsb
  obtain ⟨-, hVb⟩ := hsand b hb0 hb
  obtain ⟨hVs, -⟩ := hsand s hs (hsb.trans hb)
  set gT := (B.collar i).cusp.torusMetric with hgT
  set F : ℝ → ℝ := fun r =>
    ((@Measure.prod Torus ℝ (borel Torus) _ (riemannianVolumeMeasure torusModel Torus gT) volume)
      {p : Torus × ℝ | 0 ≤ p.2 ∧ (p.2 - z₁) ^ 2 +
        (riemannianEDistOf gT x p.1).toReal ^ 2 < r ^ 2}).toReal with hF
  set lm : ℝ := Real.sqrt ((1 - δ) * Real.exp (-(4 / 100))) with hlm
  set lp : ℝ := Real.sqrt (1 + δ) with hlp
  change (ballVolume g q b).toReal ≤ lp ^ 3 * F (b / lm) at hVb
  change lm ^ 3 * F (s / lp) ≤ (ballVolume g q s).toReal at hVs
  -- constants
  have hδ1 : δ < 1 := by linarith
  have hlp2 : lp ^ 2 = 1 + δ := Real.sq_sqrt (by linarith)
  have hlppos : 0 < lp := Real.sqrt_pos.mpr (by linarith)
  have hlm2 : lm ^ 2 = (1 - δ) * Real.exp (-(4 / 100)) :=
    Real.sq_sqrt (mul_nonneg (by linarith) (Real.exp_pos _).le)
  have hlmpos : 0 < lm := Real.sqrt_pos.mpr (mul_pos (by linarith) (Real.exp_pos _))
  have hlmlp : lm ≤ lp := by
    apply Real.sqrt_le_sqrt
    have : Real.exp (-(4 / 100)) ≤ 1 := Real.exp_le_one_iff.mpr (by norm_num)
    nlinarith
  set C : ℝ := Real.exp (3 * (4 / 100)) * ((1 + δ) / (1 - δ)) ^ 3 with hC
  have hC6 : C * lm ^ 6 = lp ^ 6 := by
    have h6 : lm ^ 6 = (lm ^ 2) ^ 3 := by ring
    have h6' : lp ^ 6 = (lp ^ 2) ^ 3 := by ring
    have he : Real.exp (-(4 / 100)) ^ 3 * Real.exp (3 * (4 / 100)) = 1 := by
      rw [← Real.exp_nat_mul, ← Real.exp_add]
      norm_num
    have h1δ : (1 - δ) ≠ 0 := by linarith
    rw [h6, h6', hlm2, hlp2, hC, div_pow, mul_pow]
    generalize Real.exp (3 * (4 / 100)) = E1 at he ⊢
    generalize Real.exp (-(4 / 100)) = E2 at he ⊢
    have hc : (1 + δ) ^ 3 / (1 - δ) ^ 3 * (1 - δ) ^ 3 = (1 + δ) ^ 3 :=
      div_mul_cancel₀ _ (pow_ne_zero 3 h1δ)
    calc E1 * ((1 + δ) ^ 3 / (1 - δ) ^ 3) * ((1 - δ) ^ 3 * E2 ^ 3)
        = ((1 + δ) ^ 3 / (1 - δ) ^ 3 * (1 - δ) ^ 3) * (E2 ^ 3 * E1) := by ring
      _ = (1 + δ) ^ 3 := by rw [hc, he, mul_one]
  -- the antitone ratio at `s/λ₊ ≤ b/λ₋`
  have hsl : 0 < s / lp := div_pos hs hlppos
  have hsbl : s / lp ≤ b / lm :=
    (div_le_div_of_nonneg_left hs.le hlmpos hlmlp).trans (div_le_div_of_nonneg_right hsb hlmpos.le)
  have hanti : F (b / lm) / (b / lm) ^ 3 ≤ F (s / lp) / (s / lp) ^ 3 :=
    torus_halfProduct_volume_div_cube_antitone (B.collar i).cusp x hz₁0 hsl hsbl
  have hX0 : 0 ≤ F (s / lp) := ENNReal.toReal_nonneg
  have hVs0 : 0 ≤ (ballVolume g q s).toReal := ENNReal.toReal_nonneg
  -- the real inequality
  have hreal : (ballVolume g q b).toReal * s ^ 3 ≤ C * b ^ 3 * (ballVolume g q s).toReal := by
    have hY : F (b / lm) * s ^ 3 ≤ F (s / lp) * lp ^ 3 * b ^ 3 / lm ^ 3 := by
      have hbl : 0 < b / lm := div_pos hb0 hlmpos
      rw [div_le_div_iff₀ (pow_pos hbl 3) (pow_pos hsl 3)] at hanti
      rw [le_div_iff₀ (pow_pos hlmpos 3)]
      have e1 : F (b / lm) * (s / lp) ^ 3 * (lp ^ 3 * lm ^ 3) = F (b / lm) * s ^ 3 * lm ^ 3 := by
        field_simp
      have e2 : F (s / lp) * (b / lm) ^ 3 * (lp ^ 3 * lm ^ 3) = F (s / lp) * lp ^ 3 * b ^ 3 := by
        field_simp
      nlinarith [mul_le_mul_of_nonneg_right hanti (by positivity : (0 : ℝ) ≤ lp ^ 3 * lm ^ 3)]
    have hX : F (s / lp) ≤ (ballVolume g q s).toReal / lm ^ 3 := by
      rw [le_div_iff₀ (pow_pos hlmpos 3), mul_comm]
      exact hVs
    calc (ballVolume g q b).toReal * s ^ 3 ≤ lp ^ 3 * F (b / lm) * s ^ 3 :=
          mul_le_mul_of_nonneg_right hVb (by positivity)
      _ = lp ^ 3 * (F (b / lm) * s ^ 3) := by ring
      _ ≤ lp ^ 3 * (F (s / lp) * lp ^ 3 * b ^ 3 / lm ^ 3) :=
          mul_le_mul_of_nonneg_left hY (by positivity)
      _ ≤ lp ^ 3 * ((ballVolume g q s).toReal / lm ^ 3 * lp ^ 3 * b ^ 3 / lm ^ 3) := by
          gcongr
      _ = lp ^ 6 / lm ^ 6 * b ^ 3 * (ballVolume g q s).toReal := by
          field_simp
      _ = C * b ^ 3 * (ballVolume g q s).toReal := by
          rw [← hC6]
          field_simp
  -- back to `ℝ≥0∞`
  have hfin : IsFiniteMeasure (riemannianVolumeMeasure W.model W.Carrier g) :=
    riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace (I := W.model) (M := W.Carrier) g
  have htop : ∀ r, ballVolume g q r ≠ ⊤ := fun r => measure_ne_top _ _
  have hC0 : 0 ≤ C * b ^ 3 := by positivity
  rw [← ENNReal.ofReal_toReal (htop b), ← ENNReal.ofReal_toReal (htop s),
    ← ENNReal.ofReal_mul ENNReal.toReal_nonneg, ← ENNReal.ofReal_mul hC0]
  exact ENNReal.ofReal_le_ofReal hreal

end DifferentialGeometry.Geometry.Collapse
