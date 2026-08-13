import DifferentialGeometry.Analysis.Parabolic.Moser.BombieriGiustiCylinder
import DifferentialGeometry.Analysis.Parabolic.Moser.BombieriGiusti
import DifferentialGeometry.Analysis.Parabolic.Moser.ForwardIteration

set_option autoImplicit false

noncomputable section

open Bundle Manifold MeasureTheory Set
open scoped ContDiff Manifold Topology

namespace DifferentialGeometry.Analysis.Parabolic.Moser

open DifferentialGeometry.Analysis.Laplacian
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Analysis.Parabolic.Energy
open DifferentialGeometry.Integral.DivergenceTheorem

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Module.Finite ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

variable [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]

private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

def canonicalEarlyBombieriGiustiReverseCost
    (n : ℕ) (g : SmoothRiemannianMetric I M)
    (hdim : 2 < (Module.finrank ℝ E : ℝ))
    (p₀ A b τ B lower upper : ℝ) (k : ℕ) : ℝ :=
  canonicalForwardMoserReverseCost (I := I) (M := M) n g hdim p₀ A
    (bombieriGiustiIncreasingLevel b τ k)
    (bombieriGiustiIncreasingLevel b τ (k + 1)) B
    (bombieriGiustiDescendingLevel lower upper (2 * k + 2))
    (bombieriGiustiDescendingLevel lower upper (2 * k + 1))

def canonicalEarlyBombieriGiustiStepPolynomialCoefficient
    (p₀ A b τ B lower upper : ℝ) : ℝ :=
  max 1 (forwardMoserStepCoefficientEnvelope p₀ A τ
    (4 / (τ - b))
    (576 * CutoffProfile.derivBound ^ 2 * B / (upper - lower) ^ 2))

theorem canonicalEarlyBombieriGiustiStepEnvelope_le_polynomial
    {p₀ A b τ B lower upper : ℝ}
    (hp₀ : 0 < p₀) (hp₀_one : p₀ < 1)
    (hAb : A ≤ b) (hbτ : b < τ)
    (hB : 0 ≤ B) (hlowerUpper : lower < upper) (k : ℕ) :
    canonicalForwardMoserStepEnvelope p₀ A
        (bombieriGiustiIncreasingLevel b τ k)
        (bombieriGiustiIncreasingLevel b τ (k + 1)) B
        (bombieriGiustiDescendingLevel lower upper (2 * k + 2))
        (bombieriGiustiDescendingLevel lower upper (2 * k + 1)) ≤
      canonicalEarlyBombieriGiustiStepPolynomialCoefficient
          p₀ A b τ B lower upper * (k + 1 : ℝ) ^ 4 := by
  let m : ℝ := k + 1
  let T : ℝ := 4 / (τ - b)
  let K : ℝ :=
    576 * CutoffProfile.derivBound ^ 2 * B / (upper - lower) ^ 2
  let Q : ℝ := max 1 (p₀ / (2 * (1 - p₀)))
  let R : ℝ := 2 * p₀ / (1 - p₀)
  have hm : 1 ≤ m := by norm_num [m]
  have hm_nonneg : 0 ≤ m := zero_le_one.trans hm
  have hm_four : 1 ≤ m ^ 4 := one_le_pow₀ hm
  have hm_sq_four : m ^ 2 ≤ m ^ 4 := by
    have hm_le_sq : m ≤ m ^ 2 := by
      nlinarith [mul_nonneg hm_nonneg (sub_nonneg.mpr hm)]
    have hpow := pow_le_pow_left₀ hm_nonneg hm_le_sq 2
    nlinarith
  have hT : 0 ≤ T := by
    exact div_nonneg (by norm_num) (sub_pos.mpr hbτ).le
  have hK : 0 ≤ K := by
    exact div_nonneg
      (mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _)) hB)
      (sq_nonneg _)
  have hQ : 0 ≤ Q := zero_le_one.trans (le_max_left _ _)
  have hR : 0 ≤ R :=
    div_nonneg (mul_nonneg (by norm_num) hp₀.le) (sub_pos.mpr hp₀_one).le
  have htime :
      2 / (bombieriGiustiIncreasingLevel b τ (k + 1) -
          bombieriGiustiIncreasingLevel b τ k) ≤ T * m ^ 4 := by
    calc
      _ ≤ T * m ^ 2 := by
        simpa only [div_eq_mul_inv, T, m] using
          two_mul_bombieriGiustiIncreasingLevel_gap_inv_le hbτ k
      _ ≤ T * m ^ 4 := mul_le_mul_of_nonneg_left hm_sq_four hT
  have hgradient : canonicalForwardMoserGradientCost B
      (bombieriGiustiDescendingLevel lower upper (2 * k + 2))
      (bombieriGiustiDescendingLevel lower upper (2 * k + 1)) ≤
      K * m ^ 4 := by
    let gap := bombieriGiustiDescendingLevel lower upper (2 * k + 1) -
      bombieriGiustiDescendingLevel lower upper (2 * k + 2)
    have hgap : 0 < gap := bombieriGiustiReciprocalLocalizer_gap_pos hlowerUpper k
    have hinv := bombieriGiustiDescendingLevel_odd_gap_inv_sq_le
      hlowerUpper k
    unfold canonicalForwardMoserGradientCost
    rw [show bombieriGiustiDescendingLevel lower upper (2 * k + 1) -
        bombieriGiustiDescendingLevel lower upper (2 * k + 2) = gap by rfl,
      div_eq_mul_inv, ← inv_pow]
    calc
      CutoffProfile.derivBound ^ 2 * B * (16 * gap⁻¹ ^ 2) ≤
          CutoffProfile.derivBound ^ 2 * B *
            (16 * ((36 / (upper - lower) ^ 2) * m ^ 4)) := by
        apply mul_le_mul_of_nonneg_left _
          (mul_nonneg (sq_nonneg _) hB)
        exact mul_le_mul_of_nonneg_left (by simpa only [gap, m] using hinv)
          (by norm_num)
      _ = K * m ^ 4 := by
        dsimp only [K]
        ring
  have hendpoint : bombieriGiustiIncreasingLevel b τ (k + 1) ≤ τ :=
    (bombieriGiustiIncreasingLevel_lt hbτ (k + 1)).le
  have houter_nonneg : 0 ≤ τ - A + 1 := by linarith
  have htime_nonneg : 0 ≤
      2 / (bombieriGiustiIncreasingLevel b τ (k + 1) -
        bombieriGiustiIncreasingLevel b τ k) := by
    exact div_nonneg (by norm_num)
      (sub_pos.mpr
        (bombieriGiustiIncreasingLevel_strictMono hbτ (Nat.lt_succ_self k))).le
  have hgradient_nonneg : 0 ≤ canonicalForwardMoserGradientCost B
      (bombieriGiustiDescendingLevel lower upper (2 * k + 2))
      (bombieriGiustiDescendingLevel lower upper (2 * k + 1)) := by
    unfold canonicalForwardMoserGradientCost
    exact mul_nonneg (mul_nonneg (sq_nonneg _) hB)
      (div_nonneg (by norm_num) (sq_nonneg _))
  have hinside : timeCutoffDerivConstant *
        (2 / (bombieriGiustiIncreasingLevel b τ (k + 1) -
          bombieriGiustiIncreasingLevel b τ k)) +
        R * canonicalForwardMoserGradientCost B
          (bombieriGiustiDescendingLevel lower upper (2 * k + 2))
          (bombieriGiustiDescendingLevel lower upper (2 * k + 1)) ≤
      (timeCutoffDerivConstant * T + R * K) * m ^ 4 := by
    calc
      _ ≤ timeCutoffDerivConstant * (T * m ^ 4) + R * (K * m ^ 4) :=
        add_le_add
          (mul_le_mul_of_nonneg_left htime timeCutoffDerivConstant_nonneg)
          (mul_le_mul_of_nonneg_left hgradient hR)
      _ = (timeCutoffDerivConstant * T + R * K) * m ^ 4 := by ring
  unfold canonicalForwardMoserStepEnvelope
  apply max_le
  · calc
      1 ≤ m ^ 4 := hm_four
      _ = 1 * m ^ 4 := by ring
      _ ≤ max 1 (forwardMoserStepCoefficientEnvelope p₀ A τ T K) * m ^ 4 :=
        mul_le_mul_of_nonneg_right
          (le_max_left 1 (forwardMoserStepCoefficientEnvelope p₀ A τ T K))
          (pow_nonneg hm_nonneg 4)
      _ = canonicalEarlyBombieriGiustiStepPolynomialCoefficient
          p₀ A b τ B lower upper * (k + 1 : ℝ) ^ 4 := by
        rfl
  · unfold forwardMoserStepCoefficientEnvelope
    have hraw :
        (bombieriGiustiIncreasingLevel b τ (k + 1) - A + 1) * Q *
            (timeCutoffDerivConstant *
                (2 / (bombieriGiustiIncreasingLevel b τ (k + 1) -
                  bombieriGiustiIncreasingLevel b τ k)) +
              R * canonicalForwardMoserGradientCost B
                (bombieriGiustiDescendingLevel lower upper (2 * k + 2))
                (bombieriGiustiDescendingLevel lower upper (2 * k + 1))) +
            canonicalForwardMoserGradientCost B
              (bombieriGiustiDescendingLevel lower upper (2 * k + 2))
              (bombieriGiustiDescendingLevel lower upper (2 * k + 1)) ≤
          forwardMoserStepCoefficientEnvelope p₀ A τ T K * m ^ 4 := by
      calc
        _ ≤ ((τ - A + 1) * Q) *
              ((timeCutoffDerivConstant * T + R * K) * m ^ 4) + K * m ^ 4 := by
          exact add_le_add
            (mul_le_mul
              (mul_le_mul_of_nonneg_right (by linarith) hQ)
              hinside
              (add_nonneg
                (mul_nonneg timeCutoffDerivConstant_nonneg htime_nonneg)
                (mul_nonneg hR hgradient_nonneg))
              (mul_nonneg houter_nonneg hQ))
            hgradient
        _ = forwardMoserStepCoefficientEnvelope p₀ A τ T K * m ^ 4 := by
          unfold forwardMoserStepCoefficientEnvelope
          dsimp only [Q, R]
          ring
    have hC : forwardMoserStepCoefficientEnvelope p₀ A τ T K ≤
        canonicalEarlyBombieriGiustiStepPolynomialCoefficient
          p₀ A b τ B lower upper := by
      exact le_max_right _ _
    exact hraw.trans (mul_le_mul_of_nonneg_right hC (pow_nonneg hm_nonneg 4))

theorem one_le_canonicalEarlyBombieriGiustiReverseCost
    (n : ℕ) [NeZero n] (g : SmoothRiemannianMetric I M)
    (hdim : 2 < (Module.finrank ℝ E : ℝ))
    (p₀ A b τ B lower upper : ℝ) (k : ℕ) :
    1 ≤ canonicalEarlyBombieriGiustiReverseCost (I := I) (M := M)
      n g hdim p₀ A b τ B lower upper k := by
  exact one_le_canonicalForwardMoserReverseCost n g hdim p₀ A
    (bombieriGiustiIncreasingLevel b τ k)
    (bombieriGiustiIncreasingLevel b τ (k + 1)) B
    (bombieriGiustiDescendingLevel lower upper (2 * k + 2))
    (bombieriGiustiDescendingLevel lower upper (2 * k + 1))

theorem exists_polynomial_bound_canonicalEarlyBombieriGiustiReverseCost
    (n : ℕ) [NeZero n] (g : SmoothRiemannianMetric I M)
    (hdim : 2 < (Module.finrank ℝ E : ℝ))
    {p₀ A b τ B lower upper : ℝ}
    (hp₀ : 0 < p₀) (hp₀_one : p₀ < 1)
    (hAb : A ≤ b) (hbτ : b < τ)
    (hB : 0 ≤ B) (hlowerUpper : lower < upper) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ k : ℕ,
      canonicalEarlyBombieriGiustiReverseCost (I := I) (M := M)
          n g hdim p₀ A b τ B lower upper k ≤
        C * (k + 1 : ℝ) ^ (n + 2) ^ 2 := by
  let theta := parabolicMoserDecay n
  let S := max 1 (localizedSobolevConstant (I := I) (M := M) g hdim)
  let Abar := canonicalEarlyBombieriGiustiStepPolynomialCoefficient
    p₀ A b τ B lower upper
  let base := ((theta * Real.log S + Real.log Abar) / (1 - theta) +
    Real.log 16 * (theta / (1 - theta) ^ 2)) / (1 - theta)
  let C := Real.exp base
  have htheta : 0 ≤ theta := (parabolicMoserDecay_pos n).le
  have hdenom : 0 < 1 - theta := sub_pos.mpr (parabolicMoserDecay_lt_one n)
  have hS : 1 ≤ S := le_max_left _ _
  have hAbar : 1 ≤ Abar := by
    exact le_max_left _ _
  have hbase : 0 ≤ base := by
    dsimp only [base]
    exact div_nonneg
      (add_nonneg
        (div_nonneg
          (add_nonneg (mul_nonneg htheta (Real.log_nonneg hS))
            (Real.log_nonneg hAbar)) hdenom.le)
        (mul_nonneg (Real.log_nonneg (by norm_num))
          (div_nonneg htheta (sq_nonneg _))))
      hdenom.le
  refine ⟨C, ?_, ?_⟩
  · exact (Real.one_le_exp_iff).2 hbase
  · intro k
    let m : ℝ := k + 1
    let Ak := canonicalForwardMoserStepEnvelope p₀ A
      (bombieriGiustiIncreasingLevel b τ k)
      (bombieriGiustiIncreasingLevel b τ (k + 1)) B
      (bombieriGiustiDescendingLevel lower upper (2 * k + 2))
      (bombieriGiustiDescendingLevel lower upper (2 * k + 1))
    have hm : 0 < m := by positivity
    have hAk : 1 ≤ Ak := by
      exact le_max_left _ _
    have hAk_bound : Ak ≤ Abar * m ^ 4 := by
      simpa only [Ak, Abar, m] using
        canonicalEarlyBombieriGiustiStepEnvelope_le_polynomial
          hp₀ hp₀_one hAb hbτ hB hlowerUpper k
    have hproduct : 0 < Abar * m ^ 4 :=
      mul_pos (zero_lt_one.trans_le hAbar) (pow_pos hm 4)
    have hlog : Real.log Ak ≤ Real.log Abar + 4 * Real.log m := by
      have hmono := Real.log_le_log (zero_lt_one.trans_le hAk) hAk_bound
      rw [Real.log_mul (zero_lt_one.trans_le hAbar).ne'
          (pow_pos hm 4).ne', Real.log_pow] at hmono
      norm_num at hmono ⊢
      exact hmono
    have hdegree : (((n + 2) ^ 2 : ℕ) : ℝ) =
        4 * (1 - theta)⁻¹ ^ 2 := by
      calc
        (((n + 2) ^ 2 : ℕ) : ℝ) = ((n : ℝ) + 2) ^ 2 := by
          push_cast
          ring
        _ = 4 * (1 - parabolicMoserDecay n)⁻¹ ^ 2 :=
          (four_mul_inv_one_sub_parabolicMoserDecay_sq (n := n)).symm
        _ = 4 * (1 - theta)⁻¹ ^ 2 := by rfl
    have hscaled : Real.log Ak * (1 - theta)⁻¹ ^ 2 ≤
        (Real.log Abar + 4 * Real.log m) * (1 - theta)⁻¹ ^ 2 :=
      mul_le_mul_of_nonneg_right hlog (sq_nonneg _)
    have hexponent :
        canonicalForwardMoserLogCost (I := I) (M := M)
            n g hdim p₀ A
              (bombieriGiustiIncreasingLevel b τ k)
              (bombieriGiustiIncreasingLevel b τ (k + 1)) B
              (bombieriGiustiDescendingLevel lower upper (2 * k + 2))
              (bombieriGiustiDescendingLevel lower upper (2 * k + 1)) /
            (1 - theta) ≤
          base + (((n + 2) ^ 2 : ℕ) : ℝ) * Real.log m := by
      unfold canonicalForwardMoserLogCost
      dsimp only [Ak, S, base, theta]
      rw [div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv]
      calc
        ((theta * Real.log S + Real.log Ak) * (1 - theta)⁻¹ +
            Real.log 16 * (theta * ((1 - theta) ^ 2)⁻¹)) *
              (1 - theta)⁻¹ =
            (theta * Real.log S * (1 - theta)⁻¹ ^ 2 +
              Real.log 16 * theta * ((1 - theta) ^ 2)⁻¹ *
                (1 - theta)⁻¹) +
              Real.log Ak * (1 - theta)⁻¹ ^ 2 := by ring
        _ ≤ (theta * Real.log S * (1 - theta)⁻¹ ^ 2 +
              Real.log 16 * theta * ((1 - theta) ^ 2)⁻¹ *
                (1 - theta)⁻¹) +
              (Real.log Abar + 4 * Real.log m) *
                (1 - theta)⁻¹ ^ 2 := by gcongr
        _ = (((theta * Real.log S + Real.log Abar) * (1 - theta)⁻¹ +
              Real.log 16 * (theta * ((1 - theta) ^ 2)⁻¹)) *
                (1 - theta)⁻¹) +
              (4 * (1 - theta)⁻¹ ^ 2) * Real.log m := by ring
        _ = base + (((n + 2) ^ 2 : ℕ) : ℝ) * Real.log m := by
          rw [← hdegree]
          dsimp only [base]
          rw [div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv]
    unfold canonicalEarlyBombieriGiustiReverseCost
    unfold canonicalForwardMoserReverseCost
    calc
      Real.exp
          (canonicalForwardMoserLogCost (I := I) (M := M)
            n g hdim p₀ A
              (bombieriGiustiIncreasingLevel b τ k)
              (bombieriGiustiIncreasingLevel b τ (k + 1)) B
              (bombieriGiustiDescendingLevel lower upper (2 * k + 2))
              (bombieriGiustiDescendingLevel lower upper (2 * k + 1)) /
            (1 - parabolicMoserDecay n)) ≤
          Real.exp (base + (((n + 2) ^ 2 : ℕ) : ℝ) * Real.log m) := by
        exact Real.exp_le_exp.mpr (by simpa only [theta] using hexponent)
      _ = Real.exp base * Real.exp
          ((((n + 2) ^ 2 : ℕ) : ℝ) * Real.log m) := Real.exp_add _ _
      _ = C * m ^ (n + 2) ^ 2 := by
        rw [Real.exp_nat_mul (Real.log m) ((n + 2) ^ 2), Real.exp_log hm]
      _ = C * (k + 1 : ℝ) ^ (n + 2) ^ 2 := by rfl

theorem summable_canonicalEarlyBombieriGiustiThreshold
    (n : ℕ) [NeZero n] (g : SmoothRiemannianMetric I M)
    (hdim : 2 < (Module.finrank ℝ E : ℝ))
    {p₀ c₀ A b τ B lower upper : ℝ}
    (hp₀ : 0 < p₀) (hp₀_one : p₀ < 1) (hc₀ : 0 ≤ c₀)
    (hAb : A ≤ b) (hbτ : b < τ)
    (hB : 0 ≤ B) (hlowerUpper : lower < upper) :
    Summable (fun k : ℕ => (3 / 4 : ℝ) ^ k *
      (bombieriGiustiThreshold p₀ c₀
        (canonicalEarlyBombieriGiustiReverseCost (I := I) (M := M)
          n g hdim p₀ A b τ B lower upper k) / 4)) := by
  rcases exists_polynomial_bound_canonicalEarlyBombieriGiustiReverseCost
      n g hdim hp₀ hp₀_one hAb hbτ hB hlowerUpper with ⟨C, hC, hbound⟩
  exact summable_geometric_mul_bombieriGiustiThreshold_of_polynomial_le
    ((n + 2) ^ 2) hp₀ hc₀ hC
    (fun k => one_le_canonicalEarlyBombieriGiustiReverseCost
      n g hdim p₀ A b τ B lower upper k)
    hbound

theorem localizedSpacetimeRpowNorm_le_canonicalEarlyBombieriGiustiReverseCost_of_supersolution
    (g : SmoothRiemannianMetric I M)
    (hdim : 2 < (Module.finrank ℝ E : ℝ))
    (rho : SmoothScalar g)
    (u : ℝ → M → ℝ)
    (hu : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun z : ℝ × M => u z.1 z.2))
    (hpos : ∀ t x, 0 < u t x)
    {p₀ A b τ B lower upper : ℝ}
    (hp₀_one : p₀ < 1)
    (hAb : A ≤ b) (hbτ : b < τ)
    (hB : 0 ≤ B) (hlowerUpper : lower < upper)
    (hrho : ∀ x : M,
      g.inner x
          (gradFun (I := I) g rho.toFun x)
          (gradFun (I := I) g rho.toFun x) ≤ B)
    (hpde : ∀ t ∈ Icc A τ, ∀ x : M,
      Δ_g (I := I) g (smoothScalarSlice (I := I) g u hu t).toContMDiffMap x ≤
        deriv (fun s => u s x) t) :
    ∀ k {p : ℝ}, 0 < p → p < p₀ →
      localizedSpacetimeRpowNorm (I := I) (M := M)
          (bombieriGiustiSpatialCutoff rho lower upper k) u p₀ A
            (bombieriGiustiIncreasingLevel b τ k) ≤
        canonicalEarlyBombieriGiustiReverseCost (I := I) (M := M)
            (Module.finrank ℝ E) g hdim p₀ A b τ B lower upper k ^
              (1 / p - 1 / p₀) *
          localizedSpacetimeRpowNorm (I := I) (M := M)
            (bombieriGiustiSpatialCutoff rho lower upper (k + 1)) u p A
              (bombieriGiustiIncreasingLevel b τ (k + 1)) := by
  intro k p hp hpp₀
  let localLower := bombieriGiustiDescendingLevel lower upper (2 * k + 2)
  let localUpper := bombieriGiustiDescendingLevel lower upper (2 * k + 1)
  let pivot := bombieriGiustiIncreasingLevel b τ k
  let endpoint := bombieriGiustiIncreasingLevel b τ (k + 1)
  have htime := bombieriGiustiIncreasingLevel_strictMono hbτ
  have hpivotEndpoint : pivot < endpoint := htime (Nat.lt_succ_self k)
  have hApivot : A ≤ pivot := hAb.trans
    (bombieriGiustiIncreasingLevel_ge hbτ k)
  have hendpointτ : endpoint < τ :=
    bombieriGiustiIncreasingLevel_lt hbτ (k + 1)
  have hlocal : localLower < localUpper :=
    bombieriGiustiDescendingLevel_strictAnti hlowerUpper (by omega)
  apply localizedSpacetimeRpowNorm_le_canonicalForwardMoserReverseCost_of_supersolution_of_lt
    (I := I) (M := M) g hdim rho
      (bombieriGiustiSpatialCutoff rho lower upper k)
      (bombieriGiustiSpatialCutoff rho lower upper (k + 1))
      u hu hpos hp hpp₀ hp₀_one hApivot hpivotEndpoint hB hlocal hrho
  · intro t ht x
    exact hpde t ⟨ht.1, ht.2.trans hendpointτ.le⟩ x
  · exact le_rfl
  · intro m _
    exact (moserUpperTimeLevel_lt hpivotEndpoint m).le
  · intro m _ x
    exact bombieriGiustiSpatialCutoff_le_forward_inner
      rho hlowerUpper k m x
  · exact le_rfl
  · exact le_rfl
  · intro x
    exact forward_initial_spatialCutoffBetween_le_bombieriGiustiSpatialCutoff_succ
      rho hlowerUpper k x

theorem early_localizedSpacetimeRpowNorm_le_exp_tsum_canonicalBombieriGiustiThreshold_of_supersolution_of_summable
    (g : SmoothRiemannianMetric I M)
    (hdim : 2 < (Module.finrank ℝ E : ℝ))
    (rho outer averagingCutoff : SmoothScalar g)
    (C : ℝ) (hC : 0 < C)
    (hP : HasLocalizedPoincareAtAverage (I := I) (M := M) g
      outer averagingCutoff C)
    (u : ℝ → M → ℝ)
    (hu : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun z : ℝ × M => u z.1 z.2))
    (hpos : ∀ t x, 0 < u t x)
    {p₀ A b τ B lower upper : ℝ}
    (hp₀ : 0 < p₀) (hp₀_one : p₀ < 1)
    (hAb : A ≤ b) (hbτ : b < τ)
    (hB : 0 ≤ B) (hlowerUpper : lower < upper)
    (hrho : ∀ x : M,
      g.inner x
          (gradFun (I := I) g rho.toFun x)
          (gradFun (I := I) g rho.toFun x) ≤ B)
    (hmeasure : ∀ k,
      localizedSpacetimeMeasure (I := I) (M := M)
        (bombieriGiustiSpatialCutoff rho lower upper k) A
          (bombieriGiustiIncreasingLevel b τ k) ≠ 0)
    (hmeasure_le_one : ∀ k,
      (localizedSpacetimeMeasure (I := I) (M := M)
        (bombieriGiustiSpatialCutoff rho lower upper k) A
          (bombieriGiustiIncreasingLevel b τ k)).real Set.univ ≤ 1)
    (houter : ∀ k x,
      (bombieriGiustiSpatialCutoff rho lower upper k).toFun x ^ 2 ≤
        outer.toFun x ^ 2)
    (hmass : 0 < cutoffMass (I := I) (M := M) averagingCutoff)
    (hpde : ∀ t ∈ Icc A τ, ∀ x : M,
      Δ_g (I := I) g (smoothScalarSlice (I := I) g u hu t).toContMDiffMap x ≤
        deriv (fun q => u q x) t)
    (hsummable : Summable (fun k : ℕ =>
      (3 / 4 : ℝ) ^ k *
        (bombieriGiustiThreshold p₀
          (2 * C * cutoffMass (I := I) (M := M) averagingCutoff)
          (canonicalEarlyBombieriGiustiReverseCost (I := I) (M := M)
            (Module.finrank ℝ E) g hdim p₀ A b τ B lower upper k) / 4))) :
    let rate := logCenterDrift (I := I) (M := M) g averagingCutoff
    let center := shiftedLogCenter (I := I) (M := M) g averagingCutoff
      u hu hpos τ
    let v := exponentialTimeRescale rate center u
    localizedSpacetimeRpowNorm (I := I) (M := M)
        (bombieriGiustiSpatialCutoff rho lower upper 0) v p₀ A b ≤
      Real.exp (∑' k : ℕ, (3 / 4 : ℝ) ^ k *
        (bombieriGiustiThreshold p₀
          (2 * C * cutoffMass (I := I) (M := M) averagingCutoff)
          (canonicalEarlyBombieriGiustiReverseCost (I := I) (M := M)
            (Module.finrank ℝ E) g hdim p₀ A b τ B lower upper k) / 4)) := by
  let n := Module.finrank ℝ E
  letI : NeZero n := by
    refine ⟨Nat.ne_of_gt ?_⟩
    exact_mod_cast (by linarith : 0 < (n : ℝ))
  let rate := logCenterDrift (I := I) (M := M) g averagingCutoff
  let center := shiftedLogCenter (I := I) (M := M) g averagingCutoff
    u hu hpos τ
  let v := exponentialTimeRescale rate center u
  have hv := contMDiff_exponentialTimeRescale rate center u hu
  have hvpos := exponentialTimeRescale_pos rate center u hpos
  have hvpde : ∀ t ∈ Icc A τ, ∀ x : M,
      Δ_g (I := I) g (smoothScalarSlice (I := I) g v hv t).toContMDiffMap x ≤
        deriv (fun q => v q x) t := by
    intro t ht x
    exact centered_exponential_time_rescale_supersolution
      (I := I) (M := M) g averagingCutoff u hu hpos τ (hpde t ht x)
  dsimp only
  conv_lhs =>
    rw [show b = bombieriGiustiIncreasingLevel b τ 0 by
      exact (bombieriGiustiIncreasingLevel_zero b τ).symm]
  apply early_localizedSpacetimeRpowNorm_le_exp_tsum_bombieriGiustiThreshold_of_supersolution
    (I := I) (M := M) g
      (bombieriGiustiSpatialCutoff rho lower upper) outer averagingCutoff
      (canonicalEarlyBombieriGiustiReverseCost (I := I) (M := M)
        n g hdim p₀ A b τ B lower upper)
      (fun _ => A) (bombieriGiustiIncreasingLevel b τ)
      C hC hP u hu hpos (A := A) (τ := τ) hp₀
  · intro k
    exact one_le_canonicalEarlyBombieriGiustiReverseCost
      n g hdim p₀ A b τ B lower upper k
  · exact hmeasure
  · exact hmeasure_le_one
  · intro k
    exact le_rfl
  · intro k
    exact (bombieriGiustiIncreasingLevel_strictMono hbτ
      (Nat.lt_succ_self k)).le
  · exact bombieriGiustiSpatialCutoff_mono rho hlowerUpper
  · exact hAb.trans hbτ.le
  · intro k
    exact le_rfl
  · intro k
    exact (bombieriGiustiIncreasingLevel_lt hbτ k).le
  · exact houter
  · exact hmass
  · exact hpde
  · intro k p hp hpp₀
    simpa only [v, rate, center, n] using
      (localizedSpacetimeRpowNorm_le_canonicalEarlyBombieriGiustiReverseCost_of_supersolution
        (I := I) (M := M) g hdim rho v hv hvpos hp₀_one hAb hbτ hB
          hlowerUpper hrho hvpde k hp hpp₀)
  · simpa only [n] using hsummable

theorem early_localizedSpacetimeRpowNorm_le_exp_tsum_canonicalBombieriGiustiThreshold_of_supersolution
    (g : SmoothRiemannianMetric I M)
    (hdim : 2 < (Module.finrank ℝ E : ℝ))
    (rho outer averagingCutoff : SmoothScalar g)
    (C : ℝ) (hC : 0 < C)
    (hP : HasLocalizedPoincareAtAverage (I := I) (M := M) g
      outer averagingCutoff C)
    (u : ℝ → M → ℝ)
    (hu : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun z : ℝ × M => u z.1 z.2))
    (hpos : ∀ t x, 0 < u t x)
    {p₀ A b τ B lower upper : ℝ}
    (hp₀ : 0 < p₀) (hp₀_one : p₀ < 1)
    (hAb : A ≤ b) (hbτ : b < τ)
    (hB : 0 ≤ B) (hlowerUpper : lower < upper)
    (hrho : ∀ x : M,
      g.inner x
          (gradFun (I := I) g rho.toFun x)
          (gradFun (I := I) g rho.toFun x) ≤ B)
    (hmeasure : ∀ k,
      localizedSpacetimeMeasure (I := I) (M := M)
        (bombieriGiustiSpatialCutoff rho lower upper k) A
          (bombieriGiustiIncreasingLevel b τ k) ≠ 0)
    (hmeasure_le_one : ∀ k,
      (localizedSpacetimeMeasure (I := I) (M := M)
        (bombieriGiustiSpatialCutoff rho lower upper k) A
          (bombieriGiustiIncreasingLevel b τ k)).real Set.univ ≤ 1)
    (houter : ∀ k x,
      (bombieriGiustiSpatialCutoff rho lower upper k).toFun x ^ 2 ≤
        outer.toFun x ^ 2)
    (hmass : 0 < cutoffMass (I := I) (M := M) averagingCutoff)
    (hpde : ∀ t ∈ Icc A τ, ∀ x : M,
      Δ_g (I := I) g (smoothScalarSlice (I := I) g u hu t).toContMDiffMap x ≤
        deriv (fun q => u q x) t) :
    let rate := logCenterDrift (I := I) (M := M) g averagingCutoff
    let center := shiftedLogCenter (I := I) (M := M) g averagingCutoff
      u hu hpos τ
    let v := exponentialTimeRescale rate center u
    localizedSpacetimeRpowNorm (I := I) (M := M)
        (bombieriGiustiSpatialCutoff rho lower upper 0) v p₀ A b ≤
      Real.exp (∑' k : ℕ, (3 / 4 : ℝ) ^ k *
        (bombieriGiustiThreshold p₀
          (2 * C * cutoffMass (I := I) (M := M) averagingCutoff)
          (canonicalEarlyBombieriGiustiReverseCost (I := I) (M := M)
            (Module.finrank ℝ E) g hdim p₀ A b τ B lower upper k) / 4)) := by
  apply
    early_localizedSpacetimeRpowNorm_le_exp_tsum_canonicalBombieriGiustiThreshold_of_supersolution_of_summable
      g hdim rho outer averagingCutoff C hC hP u hu hpos hp₀ hp₀_one
        hAb hbτ hB hlowerUpper hrho hmeasure hmeasure_le_one houter hmass hpde
  let n := Module.finrank ℝ E
  letI : NeZero n := by
    refine ⟨Nat.ne_of_gt ?_⟩
    exact_mod_cast (by linarith : 0 < (n : ℝ))
  have hc₀ : 0 ≤
      2 * C * cutoffMass (I := I) (M := M) averagingCutoff :=
    mul_nonneg (mul_nonneg (by norm_num) hC.le) hmass.le
  simpa only [n] using
    summable_canonicalEarlyBombieriGiustiThreshold
      n g hdim hp₀ hp₀_one hc₀ hAb hbτ hB hlowerUpper

end DifferentialGeometry.Analysis.Parabolic.Moser

end
