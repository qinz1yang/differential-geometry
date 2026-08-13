import DifferentialGeometry.Analysis.Parabolic.Moser.BombieriGiustiForward
import DifferentialGeometry.Analysis.Parabolic.Moser.BombieriGiustiReciprocal
import DifferentialGeometry.Analysis.Parabolic.Moser.Crossover
import DifferentialGeometry.Analysis.Parabolic.Moser.EvolvingCrossover
import DifferentialGeometry.Analysis.Parabolic.Moser.EvolvingReciprocal

set_option autoImplicit false

noncomputable section

open Bundle Manifold MeasureTheory Set
open scoped ContDiff ENNReal Manifold Topology

namespace DifferentialGeometry.Analysis.Parabolic.Moser

open DifferentialGeometry.Analysis.Laplacian
open DifferentialGeometry.Analysis.Parabolic.Energy
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Integral.Measure

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Module.Finite ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

variable [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]

def canonicalEvolvingEarlyBombieriGiustiReverseCost
    (n : ℕ) (V : ℝ≥0∞) (C p₀ A b τ G B lower upper : ℝ) (k : ℕ) : ℝ :=
  canonicalEvolvingForwardMoserReverseCost n V C p₀ A
    (bombieriGiustiIncreasingLevel b τ k)
    (bombieriGiustiIncreasingLevel b τ (k + 1)) G B
    (bombieriGiustiDescendingLevel lower upper (2 * k + 2))
    (bombieriGiustiDescendingLevel lower upper (2 * k + 1))

theorem one_le_canonicalEvolvingEarlyBombieriGiustiReverseCost
    (n : ℕ) [NeZero n] (V : ℝ≥0∞)
    (C p₀ A b τ G B lower upper : ℝ) (k : ℕ) :
    1 ≤ canonicalEvolvingEarlyBombieriGiustiReverseCost
      n V C p₀ A b τ G B lower upper k := by
  exact one_le_canonicalEvolvingForwardMoserReverseCost n V C p₀ A
    (bombieriGiustiIncreasingLevel b τ k)
    (bombieriGiustiIncreasingLevel b τ (k + 1)) G B
    (bombieriGiustiDescendingLevel lower upper (2 * k + 2))
    (bombieriGiustiDescendingLevel lower upper (2 * k + 1))

def canonicalEvolvingEarlyBombieriGiustiStepPolynomialCoefficient
    (V : ℝ≥0∞) (p₀ A b τ G B lower upper : ℝ) : ℝ :=
  max 1 (V.toReal * evolvingForwardMoserStepCoefficientEnvelope p₀ A τ
    (4 / (τ - b))
    (576 * CutoffProfile.derivBound ^ 2 * G / (upper - lower) ^ 2) B)

theorem canonicalEvolvingEarlyBombieriGiustiStepEnvelope_le_polynomial
    (V : ℝ≥0∞) {p₀ A b τ G B lower upper : ℝ}
    (hp₀ : 0 < p₀) (hp₀_one : p₀ < 1)
    (hAb : A ≤ b) (hbτ : b < τ)
    (hG : 0 ≤ G) (hB : 0 ≤ B)
    (hlowerUpper : lower < upper) (k : ℕ) :
    canonicalEvolvingForwardMoserStepEnvelope V p₀ A
        (bombieriGiustiIncreasingLevel b τ k)
        (bombieriGiustiIncreasingLevel b τ (k + 1)) G B
        (bombieriGiustiDescendingLevel lower upper (2 * k + 2))
        (bombieriGiustiDescendingLevel lower upper (2 * k + 1)) ≤
      canonicalEvolvingEarlyBombieriGiustiStepPolynomialCoefficient
          V p₀ A b τ G B lower upper * (k + 1 : ℝ) ^ 4 := by
  let m : ℝ := k + 1
  let T : ℝ := 4 / (τ - b)
  let K : ℝ :=
    576 * CutoffProfile.derivBound ^ 2 * G / (upper - lower) ^ 2
  let Q : ℝ := max 1 (p₀ / (2 * (1 - p₀)))
  let R : ℝ := 2 * p₀ / (1 - p₀)
  let localTime := 2 / (bombieriGiustiIncreasingLevel b τ (k + 1) -
    bombieriGiustiIncreasingLevel b τ k)
  let localGradient := canonicalForwardMoserGradientCost G
    (bombieriGiustiDescendingLevel lower upper (2 * k + 2))
    (bombieriGiustiDescendingLevel lower upper (2 * k + 1))
  let localCoefficient := evolvingForwardMoserStepCoefficientEnvelope p₀ A
    (bombieriGiustiIncreasingLevel b τ (k + 1))
    localTime localGradient B
  let globalCoefficient :=
    evolvingForwardMoserStepCoefficientEnvelope p₀ A τ T K B
  have hm : 1 ≤ m := by norm_num [m]
  have hm_nonneg : 0 ≤ m := zero_le_one.trans hm
  have hm_four : 1 ≤ m ^ 4 := one_le_pow₀ hm
  have hm_sq_four : m ^ 2 ≤ m ^ 4 := by
    have hm_le_sq : m ≤ m ^ 2 := by
      nlinarith [mul_nonneg hm_nonneg (sub_nonneg.mpr hm)]
    have hpow := pow_le_pow_left₀ hm_nonneg hm_le_sq 2
    nlinarith
  have hT : 0 ≤ T :=
    div_nonneg (by norm_num) (sub_pos.mpr hbτ).le
  have hK : 0 ≤ K := div_nonneg
    (mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _)) hG)
    (sq_nonneg _)
  have hQ : 0 ≤ Q := zero_le_one.trans (le_max_left _ _)
  have hR : 0 ≤ R :=
    div_nonneg (mul_nonneg (by norm_num) hp₀.le) (sub_pos.mpr hp₀_one).le
  have htime : localTime ≤ T * m ^ 4 := by
    calc
      localTime ≤ T * m ^ 2 := by
        simpa only [localTime, T, m] using
          two_mul_bombieriGiustiIncreasingLevel_gap_inv_le hbτ k
      _ ≤ T * m ^ 4 := mul_le_mul_of_nonneg_left hm_sq_four hT
  have hgradient : localGradient ≤ K * m ^ 4 := by
    let gap := bombieriGiustiDescendingLevel lower upper (2 * k + 1) -
      bombieriGiustiDescendingLevel lower upper (2 * k + 2)
    have hgap := bombieriGiustiDescendingLevel_odd_gap_inv_sq_le
      hlowerUpper k
    unfold localGradient canonicalForwardMoserGradientCost
    rw [show bombieriGiustiDescendingLevel lower upper (2 * k + 1) -
        bombieriGiustiDescendingLevel lower upper (2 * k + 2) = gap by rfl,
      div_eq_mul_inv, ← inv_pow]
    calc
      CutoffProfile.derivBound ^ 2 * G * (16 * gap⁻¹ ^ 2) ≤
          CutoffProfile.derivBound ^ 2 * G *
            (16 * ((36 / (upper - lower) ^ 2) * m ^ 4)) := by
        apply mul_le_mul_of_nonneg_left _
          (mul_nonneg (sq_nonneg _) hG)
        exact mul_le_mul_of_nonneg_left
          (by simpa only [gap, m] using hgap) (by norm_num)
      _ = K * m ^ 4 := by
        dsimp only [K]
        ring
  have hendpoint : bombieriGiustiIncreasingLevel b τ (k + 1) ≤ τ :=
    (bombieriGiustiIncreasingLevel_lt hbτ (k + 1)).le
  have houter_nonneg : 0 ≤ τ - A + 1 := by linarith
  have htime_nonneg : 0 ≤ localTime := by
    exact div_nonneg (by norm_num)
      (sub_pos.mpr
        (bombieriGiustiIncreasingLevel_strictMono hbτ
          (Nat.lt_succ_self k))).le
  have hgradient_nonneg : 0 ≤ localGradient := by
    unfold localGradient canonicalForwardMoserGradientCost
    positivity
  have htrace_nonneg : 0 ≤ (1 / 2) * B := mul_nonneg (by norm_num) hB
  have hinside :
      timeCutoffDerivConstant * localTime + R * localGradient + (1 / 2) * B ≤
        (timeCutoffDerivConstant * T + R * K + (1 / 2) * B) * m ^ 4 := by
    calc
      _ ≤ timeCutoffDerivConstant * (T * m ^ 4) +
          R * (K * m ^ 4) + ((1 / 2) * B) * m ^ 4 :=
        add_le_add
          (add_le_add
            (mul_le_mul_of_nonneg_left htime timeCutoffDerivConstant_nonneg)
            (mul_le_mul_of_nonneg_left hgradient hR))
          (le_mul_of_one_le_right htrace_nonneg hm_four)
      _ = (timeCutoffDerivConstant * T + R * K + (1 / 2) * B) *
          m ^ 4 := by ring
  have hlocal : localCoefficient ≤ globalCoefficient * m ^ 4 := by
    unfold localCoefficient globalCoefficient
      evolvingForwardMoserStepCoefficientEnvelope
    have houter :
        (bombieriGiustiIncreasingLevel b τ (k + 1) - A + 1) * Q ≤
          (τ - A + 1) * Q :=
      mul_le_mul_of_nonneg_right (by linarith) hQ
    exact calc
      (bombieriGiustiIncreasingLevel b τ (k + 1) - A + 1) * Q *
            (timeCutoffDerivConstant * localTime + R * localGradient +
              (1 / 2) * B) + localGradient ≤
          ((τ - A + 1) * Q) *
              ((timeCutoffDerivConstant * T + R * K + (1 / 2) * B) *
                m ^ 4) + K * m ^ 4 := by
        exact add_le_add
          (mul_le_mul houter hinside
            (add_nonneg
              (add_nonneg
                (mul_nonneg timeCutoffDerivConstant_nonneg htime_nonneg)
                (mul_nonneg hR hgradient_nonneg)) htrace_nonneg)
            (mul_nonneg houter_nonneg hQ))
          hgradient
      _ = ((τ - A + 1) * Q *
            (timeCutoffDerivConstant * T + R * K + (1 / 2) * B) + K) *
          m ^ 4 := by ring
  unfold canonicalEvolvingForwardMoserStepEnvelope
  apply max_le
  · calc
      1 ≤ m ^ 4 := hm_four
      _ = 1 * m ^ 4 := by ring
      _ ≤ canonicalEvolvingEarlyBombieriGiustiStepPolynomialCoefficient
          V p₀ A b τ G B lower upper * m ^ 4 :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (pow_nonneg hm_nonneg 4)
  · calc
      V.toReal * localCoefficient ≤ V.toReal * (globalCoefficient * m ^ 4) :=
        mul_le_mul_of_nonneg_left hlocal ENNReal.toReal_nonneg
      _ = (V.toReal * globalCoefficient) * m ^ 4 := by ring
      _ ≤ canonicalEvolvingEarlyBombieriGiustiStepPolynomialCoefficient
          V p₀ A b τ G B lower upper * m ^ 4 :=
        mul_le_mul_of_nonneg_right (le_max_right _ _) (pow_nonneg hm_nonneg 4)

theorem exists_polynomial_bound_canonicalEvolvingEarlyBombieriGiustiReverseCost
    (n : ℕ) [NeZero n] (V : ℝ≥0∞)
    {C p₀ A b τ G B lower upper : ℝ}
    (hp₀ : 0 < p₀) (hp₀_one : p₀ < 1)
    (hAb : A ≤ b) (hbτ : b < τ)
    (hG : 0 ≤ G) (hB : 0 ≤ B)
    (hlowerUpper : lower < upper) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ k : ℕ,
      canonicalEvolvingEarlyBombieriGiustiReverseCost
          n V C p₀ A b τ G B lower upper k ≤
        K * (k + 1 : ℝ) ^ (n + 2) ^ 2 := by
  let theta := parabolicMoserDecay n
  let S := max 1 (V.toReal * C)
  let Abar := canonicalEvolvingEarlyBombieriGiustiStepPolynomialCoefficient
    V p₀ A b τ G B lower upper
  let base := ((theta * Real.log S + Real.log Abar) / (1 - theta) +
    Real.log 16 * (theta / (1 - theta) ^ 2)) / (1 - theta)
  let K := Real.exp base
  have htheta : 0 ≤ theta := (parabolicMoserDecay_pos n).le
  have hdenom : 0 < 1 - theta := sub_pos.mpr (parabolicMoserDecay_lt_one n)
  have hS : 1 ≤ S := le_max_left _ _
  have hAbar : 1 ≤ Abar := le_max_left _ _
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
  refine ⟨K, (Real.one_le_exp_iff).2 hbase, ?_⟩
  intro k
  let m : ℝ := k + 1
  let Ak := canonicalEvolvingForwardMoserStepEnvelope V p₀ A
    (bombieriGiustiIncreasingLevel b τ k)
    (bombieriGiustiIncreasingLevel b τ (k + 1)) G B
    (bombieriGiustiDescendingLevel lower upper (2 * k + 2))
    (bombieriGiustiDescendingLevel lower upper (2 * k + 1))
  have hm : 0 < m := by positivity
  have hAk : 1 ≤ Ak := le_max_left _ _
  have hAk_bound : Ak ≤ Abar * m ^ 4 := by
    simpa only [Ak, Abar, m] using
      canonicalEvolvingEarlyBombieriGiustiStepEnvelope_le_polynomial
        V hp₀ hp₀_one hAb hbτ hG hB hlowerUpper k
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
      canonicalEvolvingForwardMoserLogCost n V C p₀ A
            (bombieriGiustiIncreasingLevel b τ k)
            (bombieriGiustiIncreasingLevel b τ (k + 1)) G B
            (bombieriGiustiDescendingLevel lower upper (2 * k + 2))
            (bombieriGiustiDescendingLevel lower upper (2 * k + 1)) /
          (1 - theta) ≤
        base + (((n + 2) ^ 2 : ℕ) : ℝ) * Real.log m := by
    unfold canonicalEvolvingForwardMoserLogCost
    dsimp only [Ak, S, base, theta]
    rw [div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv]
    calc
      ((parabolicMoserDecay n * Real.log (max 1 (V.toReal * C)) +
              Real.log Ak) * (1 - parabolicMoserDecay n)⁻¹ +
            Real.log 16 *
              (parabolicMoserDecay n *
                ((1 - parabolicMoserDecay n) ^ 2)⁻¹)) *
          (1 - parabolicMoserDecay n)⁻¹ =
        (theta * Real.log S * (1 - theta)⁻¹ ^ 2 +
            Real.log 16 * theta * ((1 - theta) ^ 2)⁻¹ *
              (1 - theta)⁻¹) +
          Real.log Ak * (1 - theta)⁻¹ ^ 2 := by ring
      _ ≤ (theta * Real.log S * (1 - theta)⁻¹ ^ 2 +
            Real.log 16 * theta * ((1 - theta) ^ 2)⁻¹ *
              (1 - theta)⁻¹) +
          (Real.log Abar + 4 * Real.log m) *
            (1 - theta)⁻¹ ^ 2 := by gcongr
      _ = (((theta * Real.log S + Real.log Abar) *
              (1 - theta)⁻¹ +
            Real.log 16 * (theta * ((1 - theta) ^ 2)⁻¹)) *
              (1 - theta)⁻¹) +
          (4 * (1 - theta)⁻¹ ^ 2) * Real.log m := by ring
      _ = base + (((n + 2) ^ 2 : ℕ) : ℝ) * Real.log m := by
        rw [← hdegree]
        dsimp only [base]
        rw [div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv]
  unfold canonicalEvolvingEarlyBombieriGiustiReverseCost
    canonicalEvolvingForwardMoserReverseCost
  calc
    Real.exp
        (canonicalEvolvingForwardMoserLogCost n V C p₀ A
            (bombieriGiustiIncreasingLevel b τ k)
            (bombieriGiustiIncreasingLevel b τ (k + 1)) G B
            (bombieriGiustiDescendingLevel lower upper (2 * k + 2))
            (bombieriGiustiDescendingLevel lower upper (2 * k + 1)) /
          (1 - parabolicMoserDecay n)) ≤
      Real.exp (base + (((n + 2) ^ 2 : ℕ) : ℝ) * Real.log m) := by
        exact Real.exp_le_exp.mpr (by simpa only [theta] using hexponent)
    _ = Real.exp base *
        Real.exp ((((n + 2) ^ 2 : ℕ) : ℝ) * Real.log m) :=
      Real.exp_add _ _
    _ = K * m ^ (n + 2) ^ 2 := by
      rw [Real.exp_nat_mul (Real.log m) ((n + 2) ^ 2), Real.exp_log hm]
    _ = K * (k + 1 : ℝ) ^ (n + 2) ^ 2 := by rfl

theorem summable_canonicalEvolvingEarlyBombieriGiustiThreshold
    (n : ℕ) [NeZero n] (V : ℝ≥0∞)
    {C p₀ c₀ A b τ G B lower upper : ℝ}
    (hp₀ : 0 < p₀) (hp₀_one : p₀ < 1) (hc₀ : 0 ≤ c₀)
    (hAb : A ≤ b) (hbτ : b < τ)
    (hG : 0 ≤ G) (hB : 0 ≤ B)
    (hlowerUpper : lower < upper) :
    Summable (fun k : ℕ => (3 / 4 : ℝ) ^ k *
      (bombieriGiustiThreshold p₀ c₀
        (canonicalEvolvingEarlyBombieriGiustiReverseCost
          n V C p₀ A b τ G B lower upper k) / 4)) := by
  rcases exists_polynomial_bound_canonicalEvolvingEarlyBombieriGiustiReverseCost
      n V hp₀ hp₀_one hAb hbτ hG hB hlowerUpper with ⟨K, hK, hbound⟩
  exact summable_geometric_mul_bombieriGiustiThreshold_of_polynomial_le
    ((n + 2) ^ 2) hp₀ hc₀ hK
    (fun k => one_le_canonicalEvolvingEarlyBombieriGiustiReverseCost
      n V C p₀ A b τ G B lower upper k)
    hbound

theorem localizedSpacetimeRpowNorm_le_canonicalEvolvingEarlyBombieriGiustiReverseCost_of_supersolution
    (qMetric : SmoothRiemannianMetric I M)
    (g : ℝ → SmoothRiemannianMetric I M)
    (hdim : 2 < (Module.finrank ℝ E : ℝ))
    (rho : SmoothScalar qMetric)
    (u : ℝ → M → ℝ)
    (hu : ContMDiff ((modelWithCornersSelf ℝ ℝ).prod I)
      (modelWithCornersSelf ℝ ℝ) ∞
      (fun z : ℝ × M => u z.1 z.2))
    (hpos : ∀ t x, 0 < u t x)
    {p₀ A b τ C G B lower upper t₀ : ℝ}
    (V : ℝ≥0∞)
    (hp₀_one : p₀ < 1)
    (hAb : A ≤ b) (hbτ : b < τ)
    (hC : 0 ≤ C) (hG : 0 ≤ G) (hB : 0 ≤ B)
    (hlowerUpper : lower < upper)
    (hg : MetricFamilyRegularAt (I := I) g t₀)
    (hgram : ∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)),
      ContMDiffOn ((modelWithCornersSelf ℝ ℝ).prod I)
        (modelWithCornersSelf ℝ ℝ) ∞
        (fun z : ℝ × M =>
          chartGramMatrix (I := I) (g z.1) x₀ z.2 i j)
        (Set.univ ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet))
    (hSobolev : ∀ t ∈ Icc A τ,
      localizedSobolevConstant (I := I) (M := M) (g t) hdim ≤ C)
    (htrace : ∀ t ∈ Icc A τ, ∀ x : M,
      -traceTimeDerivMetric (I := I) g t x ≤ B)
    (hrho : ∀ t ∈ Icc A τ, ∀ x : M,
      (g t).inner x
          (gradFun (I := I) (g t) rho.toFun x)
          (gradFun (I := I) (g t) rho.toFun x) ≤ G)
    (hpde : ∀ t ∈ Icc A τ, ∀ x : M,
      Δ_g (I := I) (g t)
          (smoothScalarSlice (I := I) (g t) u hu t).toContMDiffMap x ≤
        deriv (fun s => u s x) t)
    (hVtop : V ≠ ⊤)
    (hvolume : ∀ t ∈ Icc A τ,
      riemannianMeasureFamily (I := I) (M := M) g t ≤
          V • riemannianVolumeMeasure (I := I) (M := M) qMetric ∧
        riemannianVolumeMeasure (I := I) (M := M) qMetric ≤
          V • riemannianMeasureFamily (I := I) (M := M) g t) :
    ∀ k {p : ℝ}, 0 < p → p < p₀ →
      localizedSpacetimeRpowNorm (I := I) (M := M)
          (bombieriGiustiSpatialCutoff rho lower upper k) u p₀ A
            (bombieriGiustiIncreasingLevel b τ k) ≤
        canonicalEvolvingEarlyBombieriGiustiReverseCost
            (Module.finrank ℝ E) V C p₀ A b τ G B lower upper k ^
              (1 / p - 1 / p₀) *
          localizedSpacetimeRpowNorm (I := I) (M := M)
            (bombieriGiustiSpatialCutoff rho lower upper (k + 1)) u p A
              (bombieriGiustiIncreasingLevel b τ (k + 1)) := by
  intro k p hp hpp₀
  let localLower := bombieriGiustiDescendingLevel lower upper (2 * k + 2)
  let localUpper := bombieriGiustiDescendingLevel lower upper (2 * k + 1)
  let pivot := bombieriGiustiIncreasingLevel b τ k
  let endpoint := bombieriGiustiIncreasingLevel b τ (k + 1)
  have hpivotEndpoint : pivot < endpoint :=
    bombieriGiustiIncreasingLevel_strictMono hbτ (Nat.lt_succ_self k)
  have hApivot : A ≤ pivot := hAb.trans
    (bombieriGiustiIncreasingLevel_ge hbτ k)
  have hendpointτ : endpoint < τ :=
    bombieriGiustiIncreasingLevel_lt hbτ (k + 1)
  have hlocal : localLower < localUpper :=
    bombieriGiustiDescendingLevel_strictAnti hlowerUpper (by omega)
  apply localizedSpacetimeRpowNorm_le_evolvingReverseCost_of_supersolution_of_lt
    (I := I) (M := M) qMetric g hdim rho
      (bombieriGiustiSpatialCutoff rho lower upper k)
      (bombieriGiustiSpatialCutoff rho lower upper (k + 1))
      u hu hpos V hp hpp₀ hp₀_one hApivot hpivotEndpoint
      hC hG hB hlocal hg hgram
  · intro t ht
    exact hSobolev t ⟨ht.1, ht.2.trans hendpointτ.le⟩
  · intro t ht x
    exact htrace t ⟨ht.1, ht.2.trans hendpointτ.le⟩ x
  · intro t ht x
    exact hrho t ⟨ht.1, ht.2.trans hendpointτ.le⟩ x
  · intro t ht x
    exact hpde t ⟨ht.1, ht.2.trans hendpointτ.le⟩ x
  · exact hVtop
  · intro t ht
    exact hvolume t ⟨ht.1, ht.2.trans hendpointτ.le⟩
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

def evolvingBombieriGiustiReciprocalGradientCost
    (G lower upper : ℝ) (k : ℕ) : ℝ :=
  16 * CutoffProfile.derivBound ^ 2 *
    (bombieriGiustiDescendingLevel lower upper (2 * k + 1) -
      bombieriGiustiDescendingLevel lower upper (2 * k + 2))⁻¹ ^ 2 * G

theorem evolvingBombieriGiustiReciprocalGradientCost_nonneg
    {G lower upper : ℝ} (hG : 0 ≤ G) (k : ℕ) :
    0 ≤ evolvingBombieriGiustiReciprocalGradientCost G lower upper k := by
  unfold evolvingBombieriGiustiReciprocalGradientCost
  positivity

omit [SigmaCompactSpace M] [CompactSpace M] in
theorem spatialMoserCutoff_bombieriGiustiReciprocalLocalizer_gradient_le
    (g : SmoothRiemannianMetric I M) {q : SmoothRiemannianMetric I M}
    (rho : SmoothScalar q) {G lower upper : ℝ}
    (hG : 0 ≤ G)
    (hrho : ∀ x : M,
      g.inner x
          (gradFun (I := I) g rho.toFun x)
          (gradFun (I := I) g rho.toFun x) ≤ G)
    (k j : ℕ) (x : M) :
    g.inner x
        (gradientFun (I := I) g
          (spatialMoserCutoff
            (bombieriGiustiReciprocalLocalizer rho lower upper k)
            (2 * j + 1)).toFun x)
        (gradientFun (I := I) g
          (spatialMoserCutoff
            (bombieriGiustiReciprocalLocalizer rho lower upper k)
            (2 * j + 1)).toFun x) ≤
      evolvingMoserSpatialGradientCost
          (evolvingBombieriGiustiReciprocalGradientCost G lower upper k) j *
        (spatialMoserCutoff
          (bombieriGiustiReciprocalLocalizer rho lower upper k)
          (2 * j)).toFun x ^ 2 := by
  let localizer := bombieriGiustiReciprocalLocalizer rho lower upper k
  let gap := bombieriGiustiDescendingLevel lower upper (2 * k + 1) -
    bombieriGiustiDescendingLevel lower upper (2 * k + 2)
  let K := gap⁻¹ ^ 2 * G
  have hK : 0 ≤ K := mul_nonneg (sq_nonneg _) hG
  have hlocalizer : ∀ y : M,
      g.inner y
          (gradFun (I := I) g localizer.toFun y)
          (gradFun (I := I) g localizer.toFun y) ≤ K := by
    intro y
    simpa only [localizer, gap, K] using
      (bombieriGiustiReciprocalLocalizer_inner_grad_self_le
        (I := I) g rho hrho k y)
  have hcutoff := spatialMoserCutoff_succ_gradient_le
    (I := I) g localizer hK hlocalizer (2 * j) x
  calc
    g.inner x
        (gradientFun (I := I) g
          (spatialMoserCutoff localizer (2 * j + 1)).toFun x)
        (gradientFun (I := I) g
          (spatialMoserCutoff localizer (2 * j + 1)).toFun x) ≤
      (CutoffProfile.derivBound ^ 2 * K /
          moserCutoffWidth (2 * j + 1) ^ 2) *
        (spatialMoserCutoff localizer (2 * j)).toFun x ^ 2 := hcutoff
    _ = evolvingMoserSpatialGradientCost
          (evolvingBombieriGiustiReciprocalGradientCost G lower upper k) j *
        (spatialMoserCutoff localizer (2 * j)).toFun x ^ 2 := by
      rw [div_eq_mul_inv, moserCutoffWidth_succ_inv_sq]
      unfold evolvingMoserSpatialGradientCost
        evolvingBombieriGiustiReciprocalGradientCost
      dsimp only [K, gap]
      ring

def canonicalEvolvingLateBombieriGiustiReverseCost
    (n : ℕ) (Vfixed Vmoving : ℝ≥0∞)
    (C G B τ c d D lower upper : ℝ) (k : ℕ) : ℝ :=
  max 1 (evolvingReciprocalReverseCost n Vfixed Vmoving C
    (evolvingBombieriGiustiReciprocalGradientCost G lower upper k) B
    (bombieriGiustiDescendingLevel τ c (k + 1))
    (bombieriGiustiLatePivot τ c k)
    (bombieriGiustiIncreasingLevel d D (k + 1)))

theorem one_le_canonicalEvolvingLateBombieriGiustiReverseCost
    (n : ℕ) (Vfixed Vmoving : ℝ≥0∞)
    (C G B τ c d D lower upper : ℝ) (k : ℕ) :
    1 ≤ canonicalEvolvingLateBombieriGiustiReverseCost
      n Vfixed Vmoving C G B τ c d D lower upper k := by
  exact le_max_left _ _

def canonicalEvolvingLateBombieriGiustiStepPolynomialCoefficient
    (G B τ c D lower upper : ℝ) : ℝ :=
  let K := 576 * CutoffProfile.derivBound ^ 2 * G / (upper - lower) ^ 2
  max 1 ((D - τ + 1) *
    (8 * timeCutoffDerivConstant / (c - τ) + 4 * K + (1 / 2) * B) + K)

theorem evolvingMoserStepConstant_bombieriGiustiLate_le_polynomial
    {G B τ c d D lower upper : ℝ}
    (hτc : τ < c) (hcd : c ≤ d) (hdD : d < D)
    (hG : 0 ≤ G) (hB : 0 ≤ B)
    (hlowerUpper : lower < upper) (k : ℕ) :
    evolvingMoserStepConstant
        (evolvingBombieriGiustiReciprocalGradientCost G lower upper k) B
        (bombieriGiustiDescendingLevel τ c (k + 1))
        (bombieriGiustiLatePivot τ c k)
        (bombieriGiustiIncreasingLevel d D (k + 1)) ≤
      canonicalEvolvingLateBombieriGiustiStepPolynomialCoefficient
          G B τ c D lower upper * (k + 1 : ℝ) ^ 4 := by
  let m : ℝ := k + 1
  let timeGap := bombieriGiustiDescendingLevel τ c k -
    bombieriGiustiDescendingLevel τ c (k + 1)
  let spaceGap := bombieriGiustiDescendingLevel lower upper (2 * k + 1) -
    bombieriGiustiDescendingLevel lower upper (2 * k + 2)
  let localGradient :=
    evolvingBombieriGiustiReciprocalGradientCost G lower upper k
  let K := 576 * CutoffProfile.derivBound ^ 2 * G / (upper - lower) ^ 2
  let T := 8 * timeCutoffDerivConstant / (c - τ)
  have hm : 1 ≤ m := by norm_num [m]
  have hm_nonneg : 0 ≤ m := zero_le_one.trans hm
  have hm_four : 1 ≤ m ^ 4 := one_le_pow₀ hm
  have hm_sq_four : m ^ 2 ≤ m ^ 4 := by
    have hm_le_sq : m ≤ m ^ 2 := by
      nlinarith [mul_nonneg hm_nonneg (sub_nonneg.mpr hm)]
    have hpow := pow_le_pow_left₀ hm_nonneg hm_le_sq 2
    nlinarith
  have hK : 0 ≤ K := div_nonneg
    (mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _)) hG)
    (sq_nonneg _)
  have hT : 0 ≤ T := div_nonneg
    (mul_nonneg (by norm_num) timeCutoffDerivConstant_nonneg)
    (sub_pos.mpr hτc).le
  have hlocalGradient : localGradient ≤ K * m ^ 4 := by
    have hgap := bombieriGiustiDescendingLevel_odd_gap_inv_sq_le
      hlowerUpper k
    unfold localGradient evolvingBombieriGiustiReciprocalGradientCost
    calc
      16 * CutoffProfile.derivBound ^ 2 * spaceGap⁻¹ ^ 2 * G ≤
          16 * CutoffProfile.derivBound ^ 2 *
            ((36 / (upper - lower) ^ 2) * m ^ 4) * G := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left
            (by simpa only [spaceGap, m] using hgap)
            (mul_nonneg (by norm_num) (sq_nonneg _))) hG
      _ = K * m ^ 4 := by
        dsimp only [K]
        ring
  have hpivot : bombieriGiustiLatePivot τ c k -
      bombieriGiustiDescendingLevel τ c (k + 1) = timeGap / 2 := by
    dsimp only [bombieriGiustiLatePivot, timeGap]
    ring
  have htimeGap : 0 < timeGap := by
    dsimp only [timeGap]
    exact sub_pos.mpr
      (bombieriGiustiDescendingLevel_strictAnti hτc
        (Nat.lt_succ_self k))
  have htime : 2 * timeCutoffDerivConstant /
      (bombieriGiustiLatePivot τ c k -
        bombieriGiustiDescendingLevel τ c (k + 1)) ≤ T * m ^ 4 := by
    have hgapInv := bombieriGiustiDescendingLevel_gap_inv_le hτc k
    calc
      2 * timeCutoffDerivConstant /
          (bombieriGiustiLatePivot τ c k -
            bombieriGiustiDescendingLevel τ c (k + 1)) =
          4 * timeCutoffDerivConstant * timeGap⁻¹ := by
        rw [hpivot]
        field_simp [htimeGap.ne']
        ring
      _ ≤ 4 * timeCutoffDerivConstant *
          ((2 / (c - τ)) * m ^ 2) :=
        mul_le_mul_of_nonneg_left
          (by simpa only [timeGap, m] using hgapInv)
          (mul_nonneg (by norm_num) timeCutoffDerivConstant_nonneg)
      _ = T * m ^ 2 := by
        dsimp only [T]
        ring
      _ ≤ T * m ^ 4 := mul_le_mul_of_nonneg_left hm_sq_four hT
  have houter :
      bombieriGiustiIncreasingLevel d D (k + 1) -
          bombieriGiustiDescendingLevel τ c (k + 1) + 1 ≤
        D - τ + 1 := by
    have hleft := bombieriGiustiDescendingLevel_gt hτc (k + 1)
    have hright := bombieriGiustiIncreasingLevel_lt hdD (k + 1)
    linarith
  have houter_nonneg : 0 ≤
      bombieriGiustiIncreasingLevel d D (k + 1) -
        bombieriGiustiDescendingLevel τ c (k + 1) + 1 := by
    have hleft := bombieriGiustiDescendingLevel_le hτc (k + 1)
    have hright := bombieriGiustiIncreasingLevel_ge hdD (k + 1)
    linarith
  have houter_bound_nonneg : 0 ≤ D - τ + 1 :=
    houter_nonneg.trans houter
  have hlocalGradient_nonneg : 0 ≤ localGradient :=
    evolvingBombieriGiustiReciprocalGradientCost_nonneg hG k
  have htrace_nonneg : 0 ≤ (1 / 2) * B := mul_nonneg (by norm_num) hB
  have hinside :
      2 * timeCutoffDerivConstant /
          (bombieriGiustiLatePivot τ c k -
            bombieriGiustiDescendingLevel τ c (k + 1)) +
        4 * localGradient + (1 / 2) * B ≤
      (T + 4 * K + (1 / 2) * B) * m ^ 4 := by
    calc
      _ ≤ T * m ^ 4 + 4 * (K * m ^ 4) + ((1 / 2) * B) * m ^ 4 :=
        add_le_add
          (add_le_add htime
            (mul_le_mul_of_nonneg_left hlocalGradient (by norm_num)))
          (le_mul_of_one_le_right htrace_nonneg hm_four)
      _ = (T + 4 * K + (1 / 2) * B) * m ^ 4 := by ring
  have hinside_nonneg : 0 ≤
      2 * timeCutoffDerivConstant /
          (bombieriGiustiLatePivot τ c k -
            bombieriGiustiDescendingLevel τ c (k + 1)) +
        4 * localGradient + (1 / 2) * B := by
    exact add_nonneg
      (add_nonneg
        (div_nonneg
          (mul_nonneg (by norm_num) timeCutoffDerivConstant_nonneg)
          (by rw [hpivot]; exact div_nonneg htimeGap.le (by norm_num)))
        (mul_nonneg (by norm_num) hlocalGradient_nonneg))
      htrace_nonneg
  unfold evolvingMoserStepConstant
  let raw := (D - τ + 1) * (T + 4 * K + (1 / 2) * B) + K
  have hraw :
      (bombieriGiustiIncreasingLevel d D (k + 1) -
          bombieriGiustiDescendingLevel τ c (k + 1) + 1) *
          (2 * timeCutoffDerivConstant /
              (bombieriGiustiLatePivot τ c k -
                bombieriGiustiDescendingLevel τ c (k + 1)) +
            4 * localGradient + (1 / 2) * B) + localGradient ≤
        raw * m ^ 4 := by
    calc
      _ ≤ (D - τ + 1) * ((T + 4 * K + (1 / 2) * B) * m ^ 4) +
          K * m ^ 4 :=
        add_le_add
          (mul_le_mul houter hinside hinside_nonneg houter_bound_nonneg)
          hlocalGradient
      _ = raw * m ^ 4 := by
        dsimp only [raw]
        ring
  have hcoefficient : raw ≤
      canonicalEvolvingLateBombieriGiustiStepPolynomialCoefficient
        G B τ c D lower upper := le_max_right _ _
  exact hraw.trans (mul_le_mul_of_nonneg_right hcoefficient
    (pow_nonneg hm_nonneg 4))

theorem exists_polynomial_bound_canonicalEvolvingLateBombieriGiustiReverseCost
    (n : ℕ) [NeZero n] (Vfixed Vmoving : ℝ≥0∞)
    {C G B τ c d D lower upper : ℝ}
    (hτc : τ < c) (hcd : c ≤ d) (hdD : d < D)
    (hG : 0 ≤ G) (hB : 0 ≤ B)
    (hlowerUpper : lower < upper) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ k : ℕ,
      canonicalEvolvingLateBombieriGiustiReverseCost
          n Vfixed Vmoving C G B τ c d D lower upper k ≤
        K * (k + 1 : ℝ) ^ (2 * (n + 2)) := by
  let theta := parabolicMoserDecay n
  let S := max 1 C
  let Abar := canonicalEvolvingLateBombieriGiustiStepPolynomialCoefficient
    G B τ c D lower upper
  let base := ((theta * Real.log S + Real.log Abar) / 2) /
      (1 - theta) +
    (Real.log 16 / 2) * (theta / (1 - theta) ^ 2)
  let volumeFactor := max 1
    ((max 1 Vfixed.toReal) ^ 2 * Vmoving.toReal)
  let K := volumeFactor * Real.exp (2 * base)
  have htheta : 0 ≤ theta := (parabolicMoserDecay_pos n).le
  have htheta_one : theta < 1 := parabolicMoserDecay_lt_one n
  have hdenom : 0 < 1 - theta := sub_pos.mpr htheta_one
  have hS : 1 ≤ S := le_max_left _ _
  have hAbar : 1 ≤ Abar := le_max_left _ _
  have hbase : 0 ≤ base := by
    dsimp only [base]
    exact add_nonneg
      (div_nonneg
        (div_nonneg
          (add_nonneg (mul_nonneg htheta (Real.log_nonneg hS))
            (Real.log_nonneg hAbar)) (by norm_num)) hdenom.le)
      (mul_nonneg
        (div_nonneg (Real.log_nonneg (by norm_num)) (by norm_num))
        (div_nonneg htheta (sq_nonneg _)))
  have hvolumeFactor : 1 ≤ volumeFactor := le_max_left _ _
  have hexpBase : 1 ≤ Real.exp (2 * base) :=
    (Real.one_le_exp_iff).2 (mul_nonneg (by norm_num) hbase)
  have hK : 1 ≤ K := by
    calc
      1 = 1 * 1 := by ring
      _ ≤ volumeFactor * Real.exp (2 * base) :=
        mul_le_mul hvolumeFactor hexpBase zero_le_one
          (zero_le_one.trans hvolumeFactor)
      _ = K := by rfl
  refine ⟨K, hK, ?_⟩
  intro k
  let m : ℝ := k + 1
  let localGradient :=
    evolvingBombieriGiustiReciprocalGradientCost G lower upper k
  let aOuter := bombieriGiustiDescendingLevel τ c (k + 1)
  let pivot := bombieriGiustiLatePivot τ c k
  let bOuter := bombieriGiustiIncreasingLevel d D (k + 1)
  let Ak := max 1 (evolvingMoserStepConstant
    localGradient B aOuter pivot bOuter)
  let factor := evolvingMoserLocalBoundFactor
    n C localGradient B 2 aOuter pivot bOuter
  have hm : 0 < m := by positivity
  have hm_one : 1 ≤ m := by norm_num [m]
  have hm_four : 1 ≤ m ^ 4 := one_le_pow₀ hm_one
  have hAk : 1 ≤ Ak := le_max_left _ _
  have hAk_bound : Ak ≤ Abar * m ^ 4 := by
    apply max_le
    · calc
        1 = 1 * 1 := by ring
        _ ≤ Abar * m ^ 4 :=
          mul_le_mul hAbar hm_four zero_le_one (zero_le_one.trans hAbar)
    · simpa only [Abar, m, localGradient, aOuter, pivot, bOuter] using
        evolvingMoserStepConstant_bombieriGiustiLate_le_polynomial
          hτc hcd hdD hG hB hlowerUpper k
  have hlog : Real.log Ak ≤ Real.log Abar + 4 * Real.log m := by
    have hmono := Real.log_le_log (zero_lt_one.trans_le hAk) hAk_bound
    rw [Real.log_mul (zero_lt_one.trans_le hAbar).ne'
        (pow_pos hm 4).ne', Real.log_pow] at hmono
    norm_num at hmono ⊢
    exact hmono
  have hdegree : (((2 * (n + 2) : ℕ) : ℝ)) =
      4 * (1 - theta)⁻¹ := by
    calc
      (((2 * (n + 2) : ℕ) : ℝ)) = 2 * ((n : ℝ) + 2) := by
        push_cast
        ring
      _ = 4 * (1 - parabolicMoserDecay n)⁻¹ := by
        rw [← two_mul_inv_one_sub_parabolicMoserDecay]
        ring
      _ = 4 * (1 - theta)⁻¹ := by rfl
  have hfactor : factor ≤
      Real.exp (base + 2 * (1 - theta)⁻¹ * Real.log m) := by
    unfold factor evolvingMoserLocalBoundFactor
    rw [tsum_moserIterationCost htheta htheta_one]
    apply Real.exp_le_exp.mpr
    dsimp only [Ak, S, base, theta]
    calc
      ((parabolicMoserDecay n * Real.log (max 1 C) +
              Real.log (max 1
                (evolvingMoserStepConstant localGradient B
                  aOuter pivot bOuter))) /
            2) /
          (1 - parabolicMoserDecay n) +
        (Real.log 16 / 2) *
          (parabolicMoserDecay n /
            (1 - parabolicMoserDecay n) ^ 2) ≤
        ((theta * Real.log S +
              (Real.log Abar + 4 * Real.log m)) / 2) /
            (1 - theta) +
          (Real.log 16 / 2) * (theta / (1 - theta) ^ 2) := by
        gcongr
      _ = ((theta * Real.log S + Real.log Abar) / 2) /
            (1 - theta) +
          (Real.log 16 / 2) * (theta / (1 - theta) ^ 2) +
            2 * (1 - theta)⁻¹ * Real.log m := by
        rw [div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv]
        ring
  have hfactor_nonneg : 0 ≤ factor := by
    unfold factor evolvingMoserLocalBoundFactor
    exact (Real.exp_pos _).le
  have hupper_nonneg : 0 ≤
      Real.exp (base + 2 * (1 - theta)⁻¹ * Real.log m) :=
    (Real.exp_pos _).le
  have hfactor_sq : factor ^ 2 ≤
      Real.exp (2 * base) * m ^ (2 * (n + 2)) := by
    calc
      factor ^ 2 ≤
          Real.exp (base + 2 * (1 - theta)⁻¹ * Real.log m) ^ 2 :=
        (sq_le_sq₀ hfactor_nonneg hupper_nonneg).2 hfactor
      _ = Real.exp
          ((base + 2 * (1 - theta)⁻¹ * Real.log m) +
            (base + 2 * (1 - theta)⁻¹ * Real.log m)) := by
        rw [pow_two, ← Real.exp_add]
      _ = Real.exp
          (2 * base + (((2 * (n + 2) : ℕ) : ℝ)) * Real.log m) := by
        congr 1
        rw [hdegree]
        ring
      _ = Real.exp (2 * base) *
          Real.exp ((((2 * (n + 2) : ℕ) : ℝ)) * Real.log m) :=
        Real.exp_add _ _
      _ = Real.exp (2 * base) * m ^ (2 * (n + 2)) := by
        rw [Real.exp_nat_mul (Real.log m) (2 * (n + 2)), Real.exp_log hm]
  have hpower : 1 ≤ m ^ (2 * (n + 2)) := one_le_pow₀ hm_one
  unfold canonicalEvolvingLateBombieriGiustiReverseCost
    evolvingReciprocalReverseCost
  apply max_le
  · calc
      1 ≤ K := hK
      _ ≤ K * m ^ (2 * (n + 2)) :=
        le_mul_of_one_le_right (zero_le_one.trans hK) hpower
  · rw [Real.rpow_two, mul_pow]
    calc
      (max 1 Vfixed.toReal) ^ 2 * factor ^ 2 * Vmoving.toReal ≤
          (max 1 Vfixed.toReal) ^ 2 *
              (Real.exp (2 * base) * m ^ (2 * (n + 2))) *
            Vmoving.toReal := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hfactor_sq (sq_nonneg _))
          ENNReal.toReal_nonneg
      _ = ((max 1 Vfixed.toReal) ^ 2 * Vmoving.toReal) *
          Real.exp (2 * base) * m ^ (2 * (n + 2)) := by ring
      _ ≤ volumeFactor * Real.exp (2 * base) * m ^ (2 * (n + 2)) := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (le_max_right _ _)
            (Real.exp_pos _).le)
          (pow_nonneg hm.le _)
      _ = K * m ^ (2 * (n + 2)) := by rfl

theorem summable_canonicalEvolvingLateBombieriGiustiThreshold
    (n : ℕ) [NeZero n] (Vfixed Vmoving : ℝ≥0∞)
    {C G B p₀ c₀ τ c d D lower upper : ℝ}
    (hp₀ : 0 < p₀) (hc₀ : 0 ≤ c₀)
    (hτc : τ < c) (hcd : c ≤ d) (hdD : d < D)
    (hG : 0 ≤ G) (hB : 0 ≤ B)
    (hlowerUpper : lower < upper) :
    Summable (fun k : ℕ => (3 / 4 : ℝ) ^ k *
      (bombieriGiustiThreshold p₀ c₀
        (canonicalEvolvingLateBombieriGiustiReverseCost
          n Vfixed Vmoving C G B τ c d D lower upper k) / 4)) := by
  rcases exists_polynomial_bound_canonicalEvolvingLateBombieriGiustiReverseCost
      n Vfixed Vmoving hτc hcd hdD hG hB hlowerUpper with
    ⟨K, hK, hbound⟩
  exact summable_geometric_mul_bombieriGiustiThreshold_of_polynomial_le
    (2 * (n + 2)) hp₀ hc₀ hK
    (fun k => one_le_canonicalEvolvingLateBombieriGiustiReverseCost
      n Vfixed Vmoving C G B τ c d D lower upper k)
    hbound

theorem localizedSpacetimeRpowNorm_inv_le_canonicalEvolvingLateBombieriGiustiReverseCost_of_gradient_bound_of_volume_le
    (qMetric : SmoothRiemannianMetric I M)
    (g : ℝ → SmoothRiemannianMetric I M)
    (hdim : 2 < (Module.finrank ℝ E : ℝ))
    (rho : SmoothScalar qMetric)
    (u : ℝ → M → ℝ)
    (hu : ContMDiff ((modelWithCornersSelf ℝ ℝ).prod I)
      (modelWithCornersSelf ℝ ℝ) ∞
      (fun z : ℝ × M => u z.1 z.2))
    (hpos : ∀ t x, 0 < u t x)
    {p₀ τ c d D C G B lower upper t₀ : ℝ}
    (Vfixed Vmoving : ℝ≥0∞)
    (hτc : τ < c) (hcd : c ≤ d) (hdD : d < D)
    (hC : 0 ≤ C) (hG : 0 ≤ G) (hB : 0 ≤ B)
    (hlowerUpper : lower < upper)
    (hg : MetricFamilyRegularAt (I := I) g t₀)
    (hgram : ∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)),
      ContMDiffOn ((modelWithCornersSelf ℝ ℝ).prod I)
        (modelWithCornersSelf ℝ ℝ) ∞
        (fun z : ℝ × M =>
          chartGramMatrix (I := I) (g z.1) x₀ z.2 i j)
        (Set.univ ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet))
    (hSobolev : ∀ t ∈ Icc τ D,
      localizedSobolevConstant (I := I) (M := M) (g t) hdim ≤ C)
    (hpde : ∀ t ∈ Icc τ D, ∀ x : M,
      Δ_g (I := I) (g t)
          (smoothScalarSlice (I := I) (g t) u hu t).toContMDiffMap x ≤
        deriv (fun s => u s x) t)
    (htrace : ∀ t ∈ Icc τ D, ∀ x : M,
      traceTimeDerivMetric (I := I) g t x ≤ B)
    (hgradient : ∀ k j t, t ∈ Icc τ D → ∀ x : M,
      (g t).inner x
          (gradientFun (I := I) (g t)
            (spatialMoserCutoff
              (bombieriGiustiReciprocalLocalizer rho lower upper k)
              (2 * j + 1)).toFun x)
          (gradientFun (I := I) (g t)
            (spatialMoserCutoff
              (bombieriGiustiReciprocalLocalizer rho lower upper k)
              (2 * j + 1)).toFun x) ≤
        evolvingMoserSpatialGradientCost
            (evolvingBombieriGiustiReciprocalGradientCost G lower upper k) j *
          (spatialMoserCutoff
            (bombieriGiustiReciprocalLocalizer rho lower upper k)
            (2 * j)).toFun x ^ 2)
    (hVfixedTop : Vfixed ≠ ⊤)
    (hVmovingZero : Vmoving ≠ 0) (hVmovingTop : Vmoving ≠ ⊤)
    (hfixedVolume : ∀ t ∈ Icc τ D,
      riemannianVolumeMeasure (I := I) (M := M) qMetric ≤
        Vfixed • riemannianMeasureFamily (I := I) (M := M) g t)
    (hmovingVolume : ∀ t ∈ Icc τ D,
      riemannianMeasureFamily (I := I) (M := M) g t ≤
        Vmoving • riemannianVolumeMeasure (I := I) (M := M) qMetric)
    (hmeasure : ∀ k,
      localizedSpacetimeMeasure (I := I) (M := M)
        (bombieriGiustiSpatialCutoff rho lower upper k)
          (bombieriGiustiDescendingLevel τ c k)
          (bombieriGiustiIncreasingLevel d D k) ≠ 0) :
    ∀ k {p : ℝ}, 0 < p → p < p₀ →
      localizedSpacetimeRpowNorm (I := I) (M := M)
          (bombieriGiustiSpatialCutoff rho lower upper k)
          (fun t x => (u t x)⁻¹) p₀
          (bombieriGiustiDescendingLevel τ c k)
          (bombieriGiustiIncreasingLevel d D k) ≤
        canonicalEvolvingLateBombieriGiustiReverseCost
            (Module.finrank ℝ E) Vfixed Vmoving C G B
              τ c d D lower upper k ^ (1 / p - 1 / p₀) *
          localizedSpacetimeRpowNorm (I := I) (M := M)
            (bombieriGiustiSpatialCutoff rho lower upper (k + 1))
            (fun t x => (u t x)⁻¹) p
            (bombieriGiustiDescendingLevel τ c (k + 1))
            (bombieriGiustiIncreasingLevel d D (k + 1)) := by
  intro k p hp hpp₀
  let aOuter := bombieriGiustiDescendingLevel τ c (k + 1)
  let aInner := bombieriGiustiDescendingLevel τ c k
  let bInner := bombieriGiustiIncreasingLevel d D k
  let bOuter := bombieriGiustiIncreasingLevel d D (k + 1)
  let pivot := bombieriGiustiLatePivot τ c k
  let localizer := bombieriGiustiReciprocalLocalizer rho lower upper k
  let gradientCost := evolvingBombieriGiustiReciprocalGradientCost G lower upper k
  let inv : ℝ → M → ℝ := fun t x => (u t x)⁻¹
  let reverseCost := evolvingReciprocalReverseCost
    (Module.finrank ℝ E) Vfixed Vmoving C gradientCost B aOuter pivot bOuter
  have haOuterInner : aOuter < aInner :=
    bombieriGiustiDescendingLevel_strictAnti hτc (Nat.lt_succ_self k)
  have hbInnerOuter : bInner < bOuter :=
    bombieriGiustiIncreasingLevel_strictMono hdD (Nat.lt_succ_self k)
  have hτaOuter : τ < aOuter :=
    bombieriGiustiDescendingLevel_gt hτc (k + 1)
  have hbOuterD : bOuter < D :=
    bombieriGiustiIncreasingLevel_lt hdD (k + 1)
  have haInnerc : aInner ≤ c :=
    bombieriGiustiDescendingLevel_le hτc k
  have hdbInner : d ≤ bInner :=
    bombieriGiustiIncreasingLevel_ge hdD k
  have haInnerbInner : aInner ≤ bInner :=
    haInnerc.trans (hcd.trans hdbInner)
  have haOuterPivot : aOuter < pivot := by
    dsimp only [pivot, bombieriGiustiLatePivot]
    linarith
  have hpivotInner : pivot < aInner := by
    dsimp only [pivot, bombieriGiustiLatePivot]
    linarith
  have hpivotbOuter : pivot ≤ bOuter :=
    hpivotInner.le.trans (haInnerbInner.trans hbInnerOuter.le)
  have hmeasureLocalizer : localizedSpacetimeMeasure (I := I) (M := M)
      (spatialMoserCutoff localizer 0) aOuter bOuter ≠ 0 := by
    have hdom := localizedSpacetimeMeasure_mono (I := I) (M := M)
      haOuterInner.le hbInnerOuter.le
      (bombieriGiustiSpatialCutoff_le_reciprocalLocalizer
        rho hlowerUpper k)
    apply Measure.measure_univ_pos.mp
    have htarget : 0 <
        localizedSpacetimeMeasure (I := I) (M := M)
          (bombieriGiustiSpatialCutoff rho lower upper k) aInner bInner
            Set.univ := by
      simpa only [aInner, bInner] using
        (Measure.measure_univ_pos.mpr (hmeasure k))
    exact htarget.trans_le (hdom Set.univ)
  have hreverse :
      localizedSpacetimeRpowNorm (I := I) (M := M)
          (bombieriGiustiSpatialCutoff rho lower upper k) inv p₀ aInner bInner ≤
        reverseCost ^ (1 / p - 1 / p₀) *
          localizedSpacetimeRpowNorm (I := I) (M := M)
            (spatialMoserCutoff localizer 0) inv p aOuter bOuter := by
    apply localizedSpacetimeRpowNorm_inv_le_evolvingReciprocalReverseCost_of_volume_le
      (I := I) (M := M) g hdim localizer
        (bombieriGiustiSpatialCutoff rho lower upper k) u hu hpos
        hp hpp₀.le haOuterPivot hpivotbOuter haOuterInner.le hpivotInner
        haInnerbInner hbInnerOuter hB hC
        (evolvingBombieriGiustiReciprocalGradientCost_nonneg hG k) hg hgram
    · intro t ht
      exact hSobolev t ⟨hτaOuter.le.trans ht.1, ht.2.trans hbOuterD.le⟩
    · intro t ht x
      exact hpde t ⟨hτaOuter.le.trans ht.1, ht.2.trans hbOuterD.le⟩ x
    · intro t ht x
      exact htrace t ⟨hτaOuter.le.trans ht.1, ht.2.trans hbOuterD.le⟩ x
    · intro j t ht x
      exact hgradient k j t
        ⟨hτaOuter.le.trans ht.1, ht.2.trans hbOuterD.le⟩ x
    · exact hVfixedTop
    · exact hVmovingZero
    · exact hVmovingTop
    · intro t ht
      exact hfixedVolume t
        ⟨hτaOuter.le.trans ht.1, ht.2.trans hbOuterD.le⟩
    · intro t ht
      exact hmovingVolume t
        ⟨hτaOuter.le.trans ht.1, ht.2.trans hbOuterD.le⟩
    · exact one_lt_bombieriGiustiReciprocalLocalizer_of_ne_zero
        rho hlowerUpper k
    · exact bombieriGiustiSpatialCutoff_le_reciprocalLocalizer
        rho hlowerUpper k
    · exact hmeasureLocalizer
  have hinv : Continuous (fun z : ℝ × M => inv z.1 z.2) :=
    hu.continuous.inv₀ fun z => (hpos z.1 z.2).ne'
  have hinvpos : ∀ t x, 0 < inv t x := fun t x => inv_pos.mpr (hpos t x)
  have hmono := localizedSpacetimeRpowNorm_mono_measure
    (I := I) (M := M) inv hinv hinvpos
      (a := aOuter) (b := bOuter) (c := aOuter) (d := bOuter)
      hp le_rfl le_rfl
      (reciprocalLocalizer_le_bombieriGiustiSpatialCutoff_succ
        rho hlowerUpper k)
  have hexponent : 0 ≤ 1 / p - 1 / p₀ := by
    exact sub_nonneg.mpr (one_div_le_one_div_of_le hp hpp₀.le)
  have hreverseCost : 0 ≤ reverseCost := by
    unfold reverseCost evolvingReciprocalReverseCost
    exact mul_nonneg (Real.rpow_nonneg (mul_nonneg
      (zero_le_one.trans (le_max_left _ _)) (Real.exp_pos _).le) _)
      ENNReal.toReal_nonneg
  have hcost : reverseCost ^ (1 / p - 1 / p₀) ≤
      canonicalEvolvingLateBombieriGiustiReverseCost
          (Module.finrank ℝ E) Vfixed Vmoving C G B
            τ c d D lower upper k ^ (1 / p - 1 / p₀) := by
    exact Real.rpow_le_rpow hreverseCost (le_max_right _ _) hexponent
  change localizedSpacetimeRpowNorm (I := I) (M := M)
      (bombieriGiustiSpatialCutoff rho lower upper k) inv p₀ aInner bInner ≤
    canonicalEvolvingLateBombieriGiustiReverseCost
        (Module.finrank ℝ E) Vfixed Vmoving C G B
          τ c d D lower upper k ^ (1 / p - 1 / p₀) *
      localizedSpacetimeRpowNorm (I := I) (M := M)
        (bombieriGiustiSpatialCutoff rho lower upper (k + 1))
        inv p aOuter bOuter
  calc
    localizedSpacetimeRpowNorm (I := I) (M := M)
        (bombieriGiustiSpatialCutoff rho lower upper k) inv p₀ aInner bInner ≤
      reverseCost ^ (1 / p - 1 / p₀) *
        localizedSpacetimeRpowNorm (I := I) (M := M)
          (spatialMoserCutoff localizer 0) inv p aOuter bOuter := hreverse
    _ ≤ canonicalEvolvingLateBombieriGiustiReverseCost
          (Module.finrank ℝ E) Vfixed Vmoving C G B
            τ c d D lower upper k ^ (1 / p - 1 / p₀) *
        localizedSpacetimeRpowNorm (I := I) (M := M)
          (spatialMoserCutoff localizer 0) inv p aOuter bOuter :=
      mul_le_mul_of_nonneg_right hcost
        (localizedSpacetimeRpowNorm_nonneg (I := I) (M := M)
          (spatialMoserCutoff localizer 0) inv
          (fun t x => (hinvpos t x).le) p aOuter bOuter)
    _ ≤ canonicalEvolvingLateBombieriGiustiReverseCost
          (Module.finrank ℝ E) Vfixed Vmoving C G B
            τ c d D lower upper k ^ (1 / p - 1 / p₀) *
        localizedSpacetimeRpowNorm (I := I) (M := M)
          (bombieriGiustiSpatialCutoff rho lower upper (k + 1))
          inv p aOuter bOuter :=
      mul_le_mul_of_nonneg_left hmono
        (Real.rpow_nonneg
          (zero_le_one.trans (one_le_canonicalEvolvingLateBombieriGiustiReverseCost
            (Module.finrank ℝ E) Vfixed Vmoving C G B
              τ c d D lower upper k)) _)

theorem localizedSpacetimeRpowNorm_inv_le_canonicalEvolvingLateBombieriGiustiReverseCost_of_volume_le
    (qMetric : SmoothRiemannianMetric I M)
    (g : ℝ → SmoothRiemannianMetric I M)
    (hdim : 2 < (Module.finrank ℝ E : ℝ))
    (rho : SmoothScalar qMetric)
    (u : ℝ → M → ℝ)
    (hu : ContMDiff ((modelWithCornersSelf ℝ ℝ).prod I)
      (modelWithCornersSelf ℝ ℝ) ∞
      (fun z : ℝ × M => u z.1 z.2))
    (hpos : ∀ t x, 0 < u t x)
    {p₀ τ c d D C G B lower upper t₀ : ℝ}
    (Vfixed Vmoving : ℝ≥0∞)
    (hτc : τ < c) (hcd : c ≤ d) (hdD : d < D)
    (hC : 0 ≤ C) (hG : 0 ≤ G) (hB : 0 ≤ B)
    (hlowerUpper : lower < upper)
    (hg : MetricFamilyRegularAt (I := I) g t₀)
    (hgram : ∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)),
      ContMDiffOn ((modelWithCornersSelf ℝ ℝ).prod I)
        (modelWithCornersSelf ℝ ℝ) ∞
        (fun z : ℝ × M =>
          chartGramMatrix (I := I) (g z.1) x₀ z.2 i j)
        (Set.univ ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet))
    (hSobolev : ∀ t ∈ Icc τ D,
      localizedSobolevConstant (I := I) (M := M) (g t) hdim ≤ C)
    (hpde : ∀ t ∈ Icc τ D, ∀ x : M,
      Δ_g (I := I) (g t)
          (smoothScalarSlice (I := I) (g t) u hu t).toContMDiffMap x ≤
        deriv (fun s => u s x) t)
    (htrace : ∀ t ∈ Icc τ D, ∀ x : M,
      traceTimeDerivMetric (I := I) g t x ≤ B)
    (hrho : ∀ t ∈ Icc τ D, ∀ x : M,
      (g t).inner x
          (gradFun (I := I) (g t) rho.toFun x)
          (gradFun (I := I) (g t) rho.toFun x) ≤ G)
    (hVfixedTop : Vfixed ≠ ⊤)
    (hVmovingZero : Vmoving ≠ 0) (hVmovingTop : Vmoving ≠ ⊤)
    (hfixedVolume : ∀ t ∈ Icc τ D,
      riemannianVolumeMeasure (I := I) (M := M) qMetric ≤
        Vfixed • riemannianMeasureFamily (I := I) (M := M) g t)
    (hmovingVolume : ∀ t ∈ Icc τ D,
      riemannianMeasureFamily (I := I) (M := M) g t ≤
        Vmoving • riemannianVolumeMeasure (I := I) (M := M) qMetric)
    (hmeasure : ∀ k,
      localizedSpacetimeMeasure (I := I) (M := M)
        (bombieriGiustiSpatialCutoff rho lower upper k)
          (bombieriGiustiDescendingLevel τ c k)
          (bombieriGiustiIncreasingLevel d D k) ≠ 0) :
    ∀ k {p : ℝ}, 0 < p → p < p₀ →
      localizedSpacetimeRpowNorm (I := I) (M := M)
          (bombieriGiustiSpatialCutoff rho lower upper k)
          (fun t x => (u t x)⁻¹) p₀
          (bombieriGiustiDescendingLevel τ c k)
          (bombieriGiustiIncreasingLevel d D k) ≤
        canonicalEvolvingLateBombieriGiustiReverseCost
            (Module.finrank ℝ E) Vfixed Vmoving C G B
              τ c d D lower upper k ^ (1 / p - 1 / p₀) *
          localizedSpacetimeRpowNorm (I := I) (M := M)
            (bombieriGiustiSpatialCutoff rho lower upper (k + 1))
            (fun t x => (u t x)⁻¹) p
            (bombieriGiustiDescendingLevel τ c (k + 1))
            (bombieriGiustiIncreasingLevel d D (k + 1)) := by
  exact
    localizedSpacetimeRpowNorm_inv_le_canonicalEvolvingLateBombieriGiustiReverseCost_of_gradient_bound_of_volume_le
      (I := I) (M := M) qMetric g hdim rho u hu hpos Vfixed Vmoving
        hτc hcd hdD hC hG hB hlowerUpper hg hgram hSobolev hpde htrace
        (fun k j t ht x =>
          spatialMoserCutoff_bombieriGiustiReciprocalLocalizer_gradient_le
            (I := I) (g t) rho hG (hrho t ht) k j x)
        hVfixedTop hVmovingZero hVmovingTop hfixedVolume hmovingVolume hmeasure

theorem early_localizedSpacetimeRpowNorm_le_exp_tsum_canonicalEvolvingBombieriGiustiThreshold_of_supersolution_of_log_tail
    (qMetric : SmoothRiemannianMetric I M)
    (g : ℝ → SmoothRiemannianMetric I M)
    (hdim : 2 < (Module.finrank ℝ E : ℝ))
    (rho outer : SmoothScalar qMetric)
    (u : ℝ → M → ℝ)
    (hu : ContMDiff ((modelWithCornersSelf ℝ ℝ).prod I)
      (modelWithCornersSelf ℝ ℝ) ∞
      (fun z : ℝ × M => u z.1 z.2))
    (hpos : ∀ t x, 0 < u t x)
    {p₀ c₀ A b τ C G B lower upper t₀ : ℝ}
    (V : ℝ≥0∞)
    (hp₀ : 0 < p₀) (hp₀_one : p₀ < 1) (hc₀ : 0 < c₀)
    (hAb : A ≤ b) (hbτ : b < τ)
    (hC : 0 ≤ C) (hG : 0 ≤ G) (hB : 0 ≤ B)
    (hlowerUpper : lower < upper)
    (hg : MetricFamilyRegularAt (I := I) g t₀)
    (hgram : ∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)),
      ContMDiffOn ((modelWithCornersSelf ℝ ℝ).prod I)
        (modelWithCornersSelf ℝ ℝ) ∞
        (fun z : ℝ × M =>
          chartGramMatrix (I := I) (g z.1) x₀ z.2 i j)
        (Set.univ ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet))
    (hSobolev : ∀ t ∈ Icc A τ,
      localizedSobolevConstant (I := I) (M := M) (g t) hdim ≤ C)
    (htrace : ∀ t ∈ Icc A τ, ∀ x : M,
      -traceTimeDerivMetric (I := I) g t x ≤ B)
    (hrho : ∀ t ∈ Icc A τ, ∀ x : M,
      (g t).inner x
          (gradFun (I := I) (g t) rho.toFun x)
          (gradFun (I := I) (g t) rho.toFun x) ≤ G)
    (hpde : ∀ t ∈ Icc A τ, ∀ x : M,
      Δ_g (I := I) (g t)
          (smoothScalarSlice (I := I) (g t) u hu t).toContMDiffMap x ≤
        deriv (fun s => u s x) t)
    (hVtop : V ≠ ⊤)
    (hvolume : ∀ t ∈ Icc A τ,
      riemannianMeasureFamily (I := I) (M := M) g t ≤
          V • riemannianVolumeMeasure (I := I) (M := M) qMetric ∧
        riemannianVolumeMeasure (I := I) (M := M) qMetric ≤
          V • riemannianMeasureFamily (I := I) (M := M) g t)
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
    (htail : ∀ r, 0 < r →
      (localizedSpacetimeMeasure (I := I) (M := M) outer A τ).real
        {z | r < Real.log (u z.1 z.2)} ≤ c₀ / r) :
    localizedSpacetimeRpowNorm (I := I) (M := M)
        (bombieriGiustiSpatialCutoff rho lower upper 0) u p₀ A b ≤
      Real.exp (∑' k : ℕ, (3 / 4 : ℝ) ^ k *
        (bombieriGiustiThreshold p₀ c₀
          (canonicalEvolvingEarlyBombieriGiustiReverseCost
            (Module.finrank ℝ E) V C p₀ A b τ G B lower upper k) / 4)) := by
  let n := Module.finrank ℝ E
  letI : NeZero n := by
    refine ⟨Nat.ne_of_gt ?_⟩
    exact_mod_cast (by linarith : 0 < (n : ℝ))
  conv_lhs =>
    rw [show b = bombieriGiustiIncreasingLevel b τ 0 by
      exact (bombieriGiustiIncreasingLevel_zero b τ).symm]
  apply localizedSpacetimeRpowNorm_le_exp_tsum_bombieriGiustiThreshold
    (I := I) (M := M)
      (bombieriGiustiSpatialCutoff rho lower upper) outer
      (fun z => u z.1 z.2)
      (canonicalEvolvingEarlyBombieriGiustiReverseCost
        n V C p₀ A b τ G B lower upper)
      (fun _ => A) (bombieriGiustiIncreasingLevel b τ)
      (p₀ := p₀) (c₀ := c₀) (c := A) (d := τ)
      hp₀ hc₀
  · intro k
    exact one_le_canonicalEvolvingEarlyBombieriGiustiReverseCost
      n V C p₀ A b τ G B lower upper k
  · exact hu.continuous
  · exact fun z => hpos z.1 z.2
  · exact hmeasure
  · exact hmeasure_le_one
  · intro k
    exact le_rfl
  · intro k
    exact (bombieriGiustiIncreasingLevel_strictMono hbτ
      (Nat.lt_succ_self k)).le
  · exact bombieriGiustiSpatialCutoff_mono rho hlowerUpper
  · intro k
    exact le_rfl
  · intro k
    exact (bombieriGiustiIncreasingLevel_lt hbτ k).le
  · exact houter
  · intro k r hr
    let S : Set (ℝ × M) := {z | r < Real.log (u z.1 z.2)}
    have hdom := localizedSpacetimeMeasure_mono (I := I) (M := M)
      (a := A) (b := bombieriGiustiIncreasingLevel b τ k)
      (c := A) (d := τ)
      le_rfl (bombieriGiustiIncreasingLevel_lt hbτ k).le (houter k)
    have hreal :
        (localizedSpacetimeMeasure (I := I) (M := M)
          (bombieriGiustiSpatialCutoff rho lower upper k) A
            (bombieriGiustiIncreasingLevel b τ k)).real S ≤
          (localizedSpacetimeMeasure (I := I) (M := M) outer A τ).real S :=
      ENNReal.toReal_mono (measure_ne_top _ _) (hdom S)
    exact hreal.trans (by simpa only [S] using htail r hr)
  · intro k p hp hpp₀
    simpa only [n] using
      (localizedSpacetimeRpowNorm_le_canonicalEvolvingEarlyBombieriGiustiReverseCost_of_supersolution
        (I := I) (M := M) qMetric g hdim rho u hu hpos V hp₀_one
          hAb hbτ hC hG hB hlowerUpper hg hgram hSobolev htrace hrho hpde
          hVtop hvolume k hp hpp₀)
  · simpa only [n] using
      summable_canonicalEvolvingEarlyBombieriGiustiThreshold
        n V hp₀ hp₀_one hc₀.le hAb hbτ hG hB hlowerUpper

theorem late_localizedSpacetimeRpowNorm_inv_le_exp_tsum_canonicalEvolvingBombieriGiustiThreshold_of_supersolution_of_log_tail_of_volume_le
    (qMetric : SmoothRiemannianMetric I M)
    (g : ℝ → SmoothRiemannianMetric I M)
    (hdim : 2 < (Module.finrank ℝ E : ℝ))
    (rho outer : SmoothScalar qMetric)
    (u : ℝ → M → ℝ)
    (hu : ContMDiff ((modelWithCornersSelf ℝ ℝ).prod I)
      (modelWithCornersSelf ℝ ℝ) ∞
      (fun z : ℝ × M => u z.1 z.2))
    (hpos : ∀ t x, 0 < u t x)
    {p₀ c₀ τ c d D C G B lower upper t₀ : ℝ}
    (Vfixed Vmoving : ℝ≥0∞)
    (hp₀ : 0 < p₀) (hc₀ : 0 < c₀)
    (hτc : τ < c) (hcd : c ≤ d) (hdD : d < D)
    (hC : 0 ≤ C) (hG : 0 ≤ G) (hB : 0 ≤ B)
    (hlowerUpper : lower < upper)
    (hg : MetricFamilyRegularAt (I := I) g t₀)
    (hgram : ∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)),
      ContMDiffOn ((modelWithCornersSelf ℝ ℝ).prod I)
        (modelWithCornersSelf ℝ ℝ) ∞
        (fun z : ℝ × M =>
          chartGramMatrix (I := I) (g z.1) x₀ z.2 i j)
        (Set.univ ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet))
    (hSobolev : ∀ t ∈ Icc τ D,
      localizedSobolevConstant (I := I) (M := M) (g t) hdim ≤ C)
    (hpde : ∀ t ∈ Icc τ D, ∀ x : M,
      Δ_g (I := I) (g t)
          (smoothScalarSlice (I := I) (g t) u hu t).toContMDiffMap x ≤
        deriv (fun s => u s x) t)
    (htrace : ∀ t ∈ Icc τ D, ∀ x : M,
      traceTimeDerivMetric (I := I) g t x ≤ B)
    (hrho : ∀ t ∈ Icc τ D, ∀ x : M,
      (g t).inner x
          (gradFun (I := I) (g t) rho.toFun x)
          (gradFun (I := I) (g t) rho.toFun x) ≤ G)
    (hVfixedTop : Vfixed ≠ ⊤)
    (hVmovingZero : Vmoving ≠ 0) (hVmovingTop : Vmoving ≠ ⊤)
    (hfixedVolume : ∀ t ∈ Icc τ D,
      riemannianVolumeMeasure (I := I) (M := M) qMetric ≤
        Vfixed • riemannianMeasureFamily (I := I) (M := M) g t)
    (hmovingVolume : ∀ t ∈ Icc τ D,
      riemannianMeasureFamily (I := I) (M := M) g t ≤
        Vmoving • riemannianVolumeMeasure (I := I) (M := M) qMetric)
    (hmeasure : ∀ k,
      localizedSpacetimeMeasure (I := I) (M := M)
        (bombieriGiustiSpatialCutoff rho lower upper k)
          (bombieriGiustiDescendingLevel τ c k)
          (bombieriGiustiIncreasingLevel d D k) ≠ 0)
    (hmeasure_le_one : ∀ k,
      (localizedSpacetimeMeasure (I := I) (M := M)
        (bombieriGiustiSpatialCutoff rho lower upper k)
          (bombieriGiustiDescendingLevel τ c k)
          (bombieriGiustiIncreasingLevel d D k)).real Set.univ ≤ 1)
    (houter : ∀ k x,
      (bombieriGiustiSpatialCutoff rho lower upper k).toFun x ^ 2 ≤
        outer.toFun x ^ 2)
    (htail : ∀ r, 0 < r →
      (localizedSpacetimeMeasure (I := I) (M := M) outer τ D).real
        {z | Real.log (u z.1 z.2) < -r} ≤ c₀ / r) :
    localizedSpacetimeRpowNorm (I := I) (M := M)
        (bombieriGiustiSpatialCutoff rho lower upper 0)
        (fun t x => (u t x)⁻¹) p₀ c d ≤
      Real.exp (∑' k : ℕ, (3 / 4 : ℝ) ^ k *
        (bombieriGiustiThreshold p₀ c₀
          (canonicalEvolvingLateBombieriGiustiReverseCost
            (Module.finrank ℝ E) Vfixed Vmoving C G B
              τ c d D lower upper k) / 4)) := by
  let n := Module.finrank ℝ E
  letI : NeZero n := by
    refine ⟨Nat.ne_of_gt ?_⟩
    exact_mod_cast (by linarith : 0 < (n : ℝ))
  let inv : ℝ → M → ℝ := fun t x => (u t x)⁻¹
  have hinv : Continuous (fun z : ℝ × M => inv z.1 z.2) :=
    hu.continuous.inv₀ fun z => (hpos z.1 z.2).ne'
  have hinvpos : ∀ t x, 0 < inv t x := fun t x => inv_pos.mpr (hpos t x)
  suffices hbound : localizedSpacetimeRpowNorm (I := I) (M := M)
        (bombieriGiustiSpatialCutoff rho lower upper 0)
        (fun t x => inv t x) p₀
        (bombieriGiustiDescendingLevel τ c 0)
        (bombieriGiustiIncreasingLevel d D 0) ≤
      Real.exp (∑' k : ℕ, (3 / 4 : ℝ) ^ k *
        (bombieriGiustiThreshold p₀ c₀
          (canonicalEvolvingLateBombieriGiustiReverseCost
            n Vfixed Vmoving C G B τ c d D lower upper k) / 4)) by
    simpa only [bombieriGiustiDescendingLevel_zero,
      bombieriGiustiIncreasingLevel_zero, inv, n] using hbound
  apply localizedSpacetimeRpowNorm_le_exp_tsum_bombieriGiustiThreshold
    (I := I) (M := M)
      (bombieriGiustiSpatialCutoff rho lower upper) outer
      (fun z => inv z.1 z.2)
      (canonicalEvolvingLateBombieriGiustiReverseCost
        n Vfixed Vmoving C G B τ c d D lower upper)
      (bombieriGiustiDescendingLevel τ c)
      (bombieriGiustiIncreasingLevel d D)
      (p₀ := p₀) (c₀ := c₀) (c := τ) (d := D)
      hp₀ hc₀
  · intro k
    exact one_le_canonicalEvolvingLateBombieriGiustiReverseCost
      n Vfixed Vmoving C G B τ c d D lower upper k
  · exact hinv
  · exact fun z => hinvpos z.1 z.2
  · exact hmeasure
  · exact hmeasure_le_one
  · intro k
    exact (bombieriGiustiDescendingLevel_strictAnti hτc
      (Nat.lt_succ_self k)).le
  · intro k
    exact (bombieriGiustiIncreasingLevel_strictMono hdD
      (Nat.lt_succ_self k)).le
  · exact bombieriGiustiSpatialCutoff_mono rho hlowerUpper
  · intro k
    exact (bombieriGiustiDescendingLevel_gt hτc k).le
  · intro k
    exact (bombieriGiustiIncreasingLevel_lt hdD k).le
  · exact houter
  · intro k r hr
    let S : Set (ℝ × M) := {z | r < Real.log (inv z.1 z.2)}
    have hdom := localizedSpacetimeMeasure_mono (I := I) (M := M)
      (bombieriGiustiDescendingLevel_gt hτc k).le
      (bombieriGiustiIncreasingLevel_lt hdD k).le (houter k)
    have hreal :
        (localizedSpacetimeMeasure (I := I) (M := M)
          (bombieriGiustiSpatialCutoff rho lower upper k)
            (bombieriGiustiDescendingLevel τ c k)
            (bombieriGiustiIncreasingLevel d D k)).real S ≤
          (localizedSpacetimeMeasure (I := I) (M := M) outer τ D).real S :=
      ENNReal.toReal_mono (measure_ne_top _ _) (hdom S)
    have hset : S = {z : ℝ × M | Real.log (u z.1 z.2) < -r} := by
      ext z
      simp only [S, inv, mem_setOf_eq, Real.log_inv]
      constructor <;> intro hz <;> linarith
    change (localizedSpacetimeMeasure (I := I) (M := M)
      (bombieriGiustiSpatialCutoff rho lower upper k)
        (bombieriGiustiDescendingLevel τ c k)
        (bombieriGiustiIncreasingLevel d D k)).real S ≤ c₀ / r
    rw [hset]
    rw [hset] at hreal
    exact hreal.trans (htail r hr)
  · intro k p hp hpp₀
    simpa only [n, inv] using
      (localizedSpacetimeRpowNorm_inv_le_canonicalEvolvingLateBombieriGiustiReverseCost_of_volume_le
        (I := I) (M := M) qMetric g hdim rho u hu hpos
          Vfixed Vmoving hτc hcd hdD hC hG hB hlowerUpper hg hgram
          hSobolev hpde htrace hrho hVfixedTop hVmovingZero hVmovingTop
          hfixedVolume hmovingVolume hmeasure k hp hpp₀)
  · simpa only [n] using
      summable_canonicalEvolvingLateBombieriGiustiThreshold
        n Vfixed Vmoving hp₀ hc₀.le hτc hcd hdD hG hB hlowerUpper

theorem late_localizedSpacetimeRpowNorm_inv_le_exp_tsum_canonicalEvolvingBombieriGiustiThreshold_nat_add_of_supersolution_of_log_tail_of_volume_le
    (qMetric : SmoothRiemannianMetric I M)
    (g : ℝ → SmoothRiemannianMetric I M)
    (hdim : 2 < (Module.finrank ℝ E : ℝ))
    (rho outer : SmoothScalar qMetric)
    (u : ℝ → M → ℝ)
    (hu : ContMDiff ((modelWithCornersSelf ℝ ℝ).prod I)
      (modelWithCornersSelf ℝ ℝ) ∞
      (fun z : ℝ × M => u z.1 z.2))
    (hpos : ∀ t x, 0 < u t x)
    {p₀ c₀ τ c d D C G B lower upper t₀ : ℝ}
    (Vfixed Vmoving : ℝ≥0∞)
    (hp₀ : 0 < p₀) (hc₀ : 0 < c₀)
    (hτc : τ < c) (hcd : c ≤ d) (hdD : d < D)
    (hC : 0 ≤ C) (hG : 0 ≤ G) (hB : 0 ≤ B)
    (hlowerUpper : lower < upper)
    (hg : MetricFamilyRegularAt (I := I) g t₀)
    (hgram : ∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)),
      ContMDiffOn ((modelWithCornersSelf ℝ ℝ).prod I)
        (modelWithCornersSelf ℝ ℝ) ∞
        (fun z : ℝ × M =>
          chartGramMatrix (I := I) (g z.1) x₀ z.2 i j)
        (Set.univ ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet))
    (hSobolev : ∀ t ∈ Icc τ D,
      localizedSobolevConstant (I := I) (M := M) (g t) hdim ≤ C)
    (hpde : ∀ t ∈ Icc τ D, ∀ x : M,
      Δ_g (I := I) (g t)
          (smoothScalarSlice (I := I) (g t) u hu t).toContMDiffMap x ≤
        deriv (fun s => u s x) t)
    (htrace : ∀ t ∈ Icc τ D, ∀ x : M,
      traceTimeDerivMetric (I := I) g t x ≤ B)
    (hrho : ∀ t ∈ Icc τ D, ∀ x : M,
      (g t).inner x
          (gradFun (I := I) (g t) rho.toFun x)
          (gradFun (I := I) (g t) rho.toFun x) ≤ G)
    (hVfixedTop : Vfixed ≠ ⊤)
    (hVmovingZero : Vmoving ≠ 0) (hVmovingTop : Vmoving ≠ ⊤)
    (hfixedVolume : ∀ t ∈ Icc τ D,
      riemannianVolumeMeasure (I := I) (M := M) qMetric ≤
        Vfixed • riemannianMeasureFamily (I := I) (M := M) g t)
    (hmovingVolume : ∀ t ∈ Icc τ D,
      riemannianMeasureFamily (I := I) (M := M) g t ≤
        Vmoving • riemannianVolumeMeasure (I := I) (M := M) qMetric)
    (hmeasure : ∀ k,
      localizedSpacetimeMeasure (I := I) (M := M)
        (bombieriGiustiSpatialCutoff rho lower upper k)
          (bombieriGiustiDescendingLevel τ c k)
          (bombieriGiustiIncreasingLevel d D k) ≠ 0)
    (hmeasure_le_one : ∀ k,
      (localizedSpacetimeMeasure (I := I) (M := M)
        (bombieriGiustiSpatialCutoff rho lower upper k)
          (bombieriGiustiDescendingLevel τ c k)
          (bombieriGiustiIncreasingLevel d D k)).real Set.univ ≤ 1)
    (houter : ∀ k x,
      (bombieriGiustiSpatialCutoff rho lower upper k).toFun x ^ 2 ≤
        outer.toFun x ^ 2)
    (htail : ∀ r, 0 < r →
      (localizedSpacetimeMeasure (I := I) (M := M) outer τ D).real
        {z | Real.log (u z.1 z.2) < -r} ≤ c₀ / r)
    (j : ℕ) :
    localizedSpacetimeRpowNorm (I := I) (M := M)
        (bombieriGiustiSpatialCutoff rho lower upper j)
        (fun t x => (u t x)⁻¹) p₀
        (bombieriGiustiDescendingLevel τ c j)
        (bombieriGiustiIncreasingLevel d D j) ≤
      Real.exp (∑' k : ℕ, (3 / 4 : ℝ) ^ k *
        (bombieriGiustiThreshold p₀ c₀
          (canonicalEvolvingLateBombieriGiustiReverseCost
            (Module.finrank ℝ E) Vfixed Vmoving C G B
              τ c d D lower upper (j + k)) / 4)) := by
  let n := Module.finrank ℝ E
  letI : NeZero n := by
    refine ⟨Nat.ne_of_gt ?_⟩
    exact_mod_cast (by linarith : 0 < (n : ℝ))
  let inv : ℝ → M → ℝ := fun t x => (u t x)⁻¹
  have hinv : Continuous (fun z : ℝ × M => inv z.1 z.2) :=
    hu.continuous.inv₀ fun z => (hpos z.1 z.2).ne'
  have hinvpos : ∀ t x, 0 < inv t x := fun t x => inv_pos.mpr (hpos t x)
  apply localizedSpacetimeRpowNorm_le_exp_tsum_bombieriGiustiThreshold
    (I := I) (M := M)
      (fun k => bombieriGiustiSpatialCutoff rho lower upper (j + k)) outer
      (fun z => inv z.1 z.2)
      (fun k => canonicalEvolvingLateBombieriGiustiReverseCost
        n Vfixed Vmoving C G B τ c d D lower upper (j + k))
      (fun k => bombieriGiustiDescendingLevel τ c (j + k))
      (fun k => bombieriGiustiIncreasingLevel d D (j + k))
      (p₀ := p₀) (c₀ := c₀) (c := τ) (d := D)
      hp₀ hc₀
  · intro k
    exact one_le_canonicalEvolvingLateBombieriGiustiReverseCost
      n Vfixed Vmoving C G B τ c d D lower upper (j + k)
  · exact hinv
  · exact fun z => hinvpos z.1 z.2
  · intro k
    exact hmeasure (j + k)
  · intro k
    exact hmeasure_le_one (j + k)
  · intro k
    exact (bombieriGiustiDescendingLevel_strictAnti hτc (by omega)).le
  · intro k
    exact (bombieriGiustiIncreasingLevel_strictMono hdD (by omega)).le
  · intro k x
    simpa only [Nat.add_assoc] using
      bombieriGiustiSpatialCutoff_mono rho hlowerUpper (j + k) x
  · intro k
    exact (bombieriGiustiDescendingLevel_gt hτc (j + k)).le
  · intro k
    exact (bombieriGiustiIncreasingLevel_lt hdD (j + k)).le
  · intro k x
    exact houter (j + k) x
  · intro k r hr
    let S : Set (ℝ × M) := {z | r < Real.log (inv z.1 z.2)}
    have hdom := localizedSpacetimeMeasure_mono (I := I) (M := M)
      (bombieriGiustiDescendingLevel_gt hτc (j + k)).le
      (bombieriGiustiIncreasingLevel_lt hdD (j + k)).le
      (houter (j + k))
    have hreal :
        (localizedSpacetimeMeasure (I := I) (M := M)
          (bombieriGiustiSpatialCutoff rho lower upper (j + k))
            (bombieriGiustiDescendingLevel τ c (j + k))
            (bombieriGiustiIncreasingLevel d D (j + k))).real S ≤
          (localizedSpacetimeMeasure (I := I) (M := M) outer τ D).real S :=
      ENNReal.toReal_mono (measure_ne_top _ _) (hdom S)
    have hset : S = {z : ℝ × M | Real.log (u z.1 z.2) < -r} := by
      ext z
      simp only [S, inv, mem_setOf_eq, Real.log_inv]
      constructor <;> intro hz <;> linarith
    change (localizedSpacetimeMeasure (I := I) (M := M)
      (bombieriGiustiSpatialCutoff rho lower upper (j + k))
        (bombieriGiustiDescendingLevel τ c (j + k))
        (bombieriGiustiIncreasingLevel d D (j + k))).real S ≤ c₀ / r
    rw [hset]
    rw [hset] at hreal
    exact hreal.trans (htail r hr)
  · intro k p hp hpp₀
    simpa only [n, inv, Nat.add_assoc] using
      (localizedSpacetimeRpowNorm_inv_le_canonicalEvolvingLateBombieriGiustiReverseCost_of_volume_le
        (I := I) (M := M) qMetric g hdim rho u hu hpos
          Vfixed Vmoving hτc hcd hdD hC hG hB hlowerUpper hg hgram
          hSobolev hpde htrace hrho hVfixedTop hVmovingZero hVmovingTop
          hfixedVolume hmovingVolume hmeasure (j + k) hp hpp₀)
  · let f : ℕ → ℝ := fun k => (3 / 4 : ℝ) ^ k *
      (bombieriGiustiThreshold p₀ c₀
        (canonicalEvolvingLateBombieriGiustiReverseCost
          n Vfixed Vmoving C G B τ c d D lower upper k) / 4)
    have hs : Summable f := by
      exact summable_canonicalEvolvingLateBombieriGiustiThreshold
        n Vfixed Vmoving hp₀ hc₀.le hτc hcd hdD hG hB hlowerUpper
    have hshift : Summable (fun k => f (k + j)) :=
      (summable_nat_add_iff j).2 hs
    have hscaled := hshift.mul_left ((3 / 4 : ℝ) ^ j)⁻¹
    refine hscaled.congr ?_
    intro k
    dsimp only [f]
    rw [pow_add]
    field_simp [(pow_pos (by norm_num : (0 : ℝ) < 3 / 4) j).ne']
    simp only [Nat.add_comm]

def evolvingBombieriGiustiLatePointwiseFactor
    (n : ℕ) (V : ℝ≥0∞) (C G B p τ c d D lower upper : ℝ) : ℝ :=
  (max 1 V.toReal * evolvingMoserLocalBoundFactor n C
      (evolvingBombieriGiustiReciprocalGradientCost G lower upper 0) B 2
      (bombieriGiustiDescendingLevel τ c 1)
      (bombieriGiustiLatePivot τ c 0)
      (bombieriGiustiIncreasingLevel d D 1)) ^ (2 / p) *
    V.toReal ^ (1 / p)

theorem inv_le_evolvingBombieriGiustiLatePointwiseFactor_mul_localizedSpacetimeRpowNorm_of_volume_le
    (qMetric : SmoothRiemannianMetric I M)
    (g : ℝ → SmoothRiemannianMetric I M)
    (hdim : 2 < (Module.finrank ℝ E : ℝ))
    (rho : SmoothScalar qMetric)
    (u : ℝ → M → ℝ)
    (hu : ContMDiff ((modelWithCornersSelf ℝ ℝ).prod I)
      (modelWithCornersSelf ℝ ℝ) ∞
      (fun z : ℝ × M => u z.1 z.2))
    (hpos : ∀ t x, 0 < u t x)
    {p τ c d D C G B lower upper t₀ : ℝ}
    (V : ℝ≥0∞)
    (hp : 0 < p)
    (hτc : τ < c) (hcd : c ≤ d) (hdD : d < D)
    (hC : 0 ≤ C) (hG : 0 ≤ G) (hB : 0 ≤ B)
    (hlowerUpper : lower < upper)
    (hg : MetricFamilyRegularAt (I := I) g t₀)
    (hgram : ∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)),
      ContMDiffOn ((modelWithCornersSelf ℝ ℝ).prod I)
        (modelWithCornersSelf ℝ ℝ) ∞
        (fun z : ℝ × M =>
          chartGramMatrix (I := I) (g z.1) x₀ z.2 i j)
        (Set.univ ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet))
    (hSobolev : ∀ t ∈ Icc τ D,
      localizedSobolevConstant (I := I) (M := M) (g t) hdim ≤ C)
    (hpde : ∀ t ∈ Icc τ D, ∀ x : M,
      Δ_g (I := I) (g t)
          (smoothScalarSlice (I := I) (g t) u hu t).toContMDiffMap x ≤
        deriv (fun s => u s x) t)
    (htrace : ∀ t ∈ Icc τ D, ∀ x : M,
      traceTimeDerivMetric (I := I) g t x ≤ B)
    (hrho : ∀ t ∈ Icc τ D, ∀ x : M,
      (g t).inner x
          (gradFun (I := I) (g t) rho.toFun x)
          (gradFun (I := I) (g t) rho.toFun x) ≤ G)
    (hVzero : V ≠ 0) (hVtop : V ≠ ⊤)
    (hvolume : ∀ t ∈ Icc τ D,
      riemannianMeasureFamily (I := I) (M := M) g t ≤
          V • riemannianVolumeMeasure (I := I) (M := M) qMetric ∧
        riemannianVolumeMeasure (I := I) (M := M) qMetric ≤
          V • riemannianMeasureFamily (I := I) (M := M) g t) :
    ∀ t ∈ Icc c d, ∀ x : M,
      (bombieriGiustiSpatialCutoff rho lower upper 0).toFun x ≠ 0 →
      (u t x)⁻¹ ≤
        evolvingBombieriGiustiLatePointwiseFactor
            (Module.finrank ℝ E) V C G B p τ c d D lower upper *
          localizedSpacetimeRpowNorm (I := I) (M := M)
            (bombieriGiustiSpatialCutoff rho lower upper 1)
            (fun s y => (u s y)⁻¹) p
            (bombieriGiustiDescendingLevel τ c 1)
            (bombieriGiustiIncreasingLevel d D 1) := by
  let n := Module.finrank ℝ E
  let aOuter := bombieriGiustiDescendingLevel τ c 1
  let pivot := bombieriGiustiLatePivot τ c 0
  let bOuter := bombieriGiustiIncreasingLevel d D 1
  let localizer := bombieriGiustiReciprocalLocalizer rho lower upper 0
  let gradientCost := evolvingBombieriGiustiReciprocalGradientCost G lower upper 0
  let f : ℝ → M → ℝ := fun s y => (u s y)⁻¹
  let v : ℝ → M → ℝ := fun s y => u s y ^ (-p / 2)
  let cutoff := spatialMoserCutoff localizer 0
  let Dmoving := evolvingMoserLocalizedMass
    (I := I) (M := M) n g localizer v 2 aOuter pivot bOuter 0
  let Pfixed := localizedSpacetimeRpowMoment
    (I := I) (M := M) cutoff f p aOuter bOuter
  let Nouter := localizedSpacetimeRpowNorm
    (I := I) (M := M) (bombieriGiustiSpatialCutoff rho lower upper 1)
      f p aOuter bOuter
  let F := max 1 V.toReal * evolvingMoserLocalBoundFactor
    n C gradientCost B 2 aOuter pivot bOuter
  have haOuterPivot : aOuter < pivot := by
    dsimp only [aOuter, pivot, bombieriGiustiLatePivot]
    have hdesc := bombieriGiustiDescendingLevel_strictAnti hτc (by omega : 0 < 1)
    linarith
  have hpivotc : pivot < c := by
    dsimp only [pivot, bombieriGiustiLatePivot]
    rw [bombieriGiustiDescendingLevel_zero]
    have hdesc := bombieriGiustiDescendingLevel_strictAnti hτc (by omega : 0 < 1)
    have hdesc' : bombieriGiustiDescendingLevel τ c 1 < c := by
      simpa only [bombieriGiustiDescendingLevel_zero] using hdesc
    linarith
  have hdbOuter : d < bOuter := by
    dsimp only [bOuter]
    simpa only [bombieriGiustiIncreasingLevel_zero] using
      bombieriGiustiIncreasingLevel_strictMono hdD (by omega : 0 < 1)
  have hτaOuter : τ < aOuter := bombieriGiustiDescendingLevel_gt hτc 1
  have hbOuterD : bOuter < D := bombieriGiustiIncreasingLevel_lt hdD 1
  have hpivotbOuter : pivot ≤ bOuter := by
    exact hpivotc.le.trans (hcd.trans (hdbOuter.le))
  have hf : ContMDiff ((modelWithCornersSelf ℝ ℝ).prod I)
      (modelWithCornersSelf ℝ ℝ) ∞
      (fun z : ℝ × M => f z.1 z.2) := by
    simpa only [f, Real.rpow_neg_one] using
      contMDiff_rpow_of_pos hu hpos (-1 : ℝ)
  have hfpos : ∀ s y, 0 < f s y := fun s y => inv_pos.mpr (hpos s y)
  have hintegrand : Continuous (fun z : ℝ × M =>
      cutoff.toFun z.2 ^ 2 * f z.1 z.2 ^ p) :=
    (cutoff.smooth.continuous.comp continuous_snd).pow 2 |>.mul
      (hf.continuous.rpow_const fun z => Or.inl (hfpos z.1 z.2).ne')
  have hcompare := intervalIntegral_moving_le_fixed_of_volume_le
    (I := I) (M := M) qMetric g
      (fun s y => cutoff.toFun y ^ 2 * f s y ^ p) hintegrand
      (fun s y => mul_nonneg (sq_nonneg _)
        (Real.rpow_nonneg (hfpos s y).le _))
      (haOuterPivot.le.trans hpivotbOuter) hg V hVtop
      (fun s hs => (hvolume s
        ⟨hτaOuter.le.trans hs.1, hs.2.trans hbOuterD.le⟩).1)
  have hD_eq : Dmoving =
      ∫ s in aOuter..bOuter, ∫ y, cutoff.toFun y ^ 2 * f s y ^ p
        ∂(riemannianMeasureFamily (I := I) (M := M) g s) := by
    rw [show Dmoving = evolvingMoserLocalizedMass
      (I := I) (M := M) n g localizer v 2 aOuter pivot bOuter 0 by rfl,
      evolvingMoserLocalizedMass, moserTimeLevel_zero]
    apply intervalIntegral.integral_congr
    intro s _
    apply integral_congr_ae
    filter_upwards with y
    simp only [parabolicMoserExponent_zero, cutoff, v, f]
    congr 1
    calc
      (u s y ^ (-p / 2)) ^ (2 : ℝ) = u s y ^ ((-p / 2) * 2) :=
        (Real.rpow_mul (hpos s y).le _ _).symm
      _ = u s y ^ (-p) := by congr 1; ring
      _ = (u s y)⁻¹ ^ p := Real.rpow_neg_eq_inv_rpow _ _
  have hfixed_eq :
      (∫ s in aOuter..bOuter, ∫ y, cutoff.toFun y ^ 2 * f s y ^ p
        ∂(riemannianVolumeMeasure (I := I) (M := M) qMetric)) = Pfixed := by
    dsimp only [Pfixed]
    rw [localizedSpacetimeRpowMoment_eq_intervalIntegral_of_continuous_pos
      (I := I) (M := M) cutoff f hf.continuous hfpos
        (haOuterPivot.le.trans hpivotbOuter)]
  have hDmoving : 0 ≤ Dmoving := evolvingMoserLocalizedMass_nonneg
    (I := I) (M := M) n g localizer v haOuterPivot hpivotbOuter
      (fun s y => (Real.rpow_pos_of_pos (hpos s y) _).le) 0
  have hPfixed : 0 ≤ Pfixed := localizedSpacetimeRpowMoment_nonneg
    (I := I) (M := M) cutoff f (fun s y => (hfpos s y).le) p aOuter bOuter
  have hDP : Dmoving ≤ V.toReal * Pfixed := by
    calc
      Dmoving = ∫ s in aOuter..bOuter, ∫ y, cutoff.toFun y ^ 2 * f s y ^ p
          ∂(riemannianMeasureFamily (I := I) (M := M) g s) := hD_eq
      _ ≤ V.toReal *
          (∫ s in aOuter..bOuter, ∫ y, cutoff.toFun y ^ 2 * f s y ^ p
            ∂(riemannianVolumeMeasure (I := I) (M := M) qMetric)) := hcompare
      _ = V.toReal * Pfixed := congrArg (fun z => V.toReal * z) hfixed_eq
  have hVreal : 0 < V.toReal := ENNReal.toReal_pos hVzero hVtop
  have hroot : Dmoving ^ (1 / p) ≤ V.toReal ^ (1 / p) * Pfixed ^ (1 / p) := by
    calc
      Dmoving ^ (1 / p) ≤ (V.toReal * Pfixed) ^ (1 / p) :=
        Real.rpow_le_rpow hDmoving hDP (div_nonneg zero_le_one hp.le)
      _ = V.toReal ^ (1 / p) * Pfixed ^ (1 / p) := by
        rw [Real.mul_rpow hVreal.le hPfixed]
  have hnormMono : Pfixed ^ (1 / p) ≤ Nouter := by
    change localizedSpacetimeRpowNorm (I := I) (M := M)
      cutoff f p aOuter bOuter ≤ Nouter
    simpa only [Nouter, cutoff, localizer] using
      (localizedSpacetimeRpowNorm_mono_measure
        (I := I) (M := M) f hf.continuous hfpos hp le_rfl le_rfl
          (reciprocalLocalizer_le_bombieriGiustiSpatialCutoff_succ
            rho hlowerUpper 0))
  have hrootOuter : Dmoving ^ (1 / p) ≤ V.toReal ^ (1 / p) * Nouter :=
    hroot.trans (mul_le_mul_of_nonneg_left hnormMono
      (Real.rpow_nonneg hVreal.le _))
  have hF : 0 ≤ F := mul_nonneg
    (zero_le_one.trans (le_max_left _ _)) (Real.exp_pos _).le
  intro t ht x hx
  have htLocal : t ∈ Ioo pivot bOuter :=
    ⟨hpivotc.trans_le ht.1, ht.2.trans_lt hdbOuter⟩
  have hxLocal : 1 < localizer.toFun x :=
    one_lt_bombieriGiustiReciprocalLocalizer_of_ne_zero
      rho hlowerUpper 0 x hx
  have hlocal :=
    evolving_reciprocal_local_boundedness_of_supersolution_rpow_of_volume_le
      (I := I) (M := M) g hdim localizer u hu hpos hp
        haOuterPivot hpivotbOuter hB hC
        (evolvingBombieriGiustiReciprocalGradientCost_nonneg hG 0) hg hgram
        (fun s hs => hSobolev s
          ⟨hτaOuter.le.trans hs.1, hs.2.trans hbOuterD.le⟩)
        (fun s hs y => hpde s
          ⟨hτaOuter.le.trans hs.1, hs.2.trans hbOuterD.le⟩ y)
        (fun s hs y => htrace s
          ⟨hτaOuter.le.trans hs.1, hs.2.trans hbOuterD.le⟩ y)
        (fun k s hs y =>
          spatialMoserCutoff_bombieriGiustiReciprocalLocalizer_gradient_le
            (I := I) (g s) rho hG
              (fun z => hrho s
                ⟨hτaOuter.le.trans hs.1, hs.2.trans hbOuterD.le⟩ z)
              0 k y)
        V hVtop
        (fun s hs => (hvolume s
          ⟨hτaOuter.le.trans hs.1, hs.2.trans hbOuterD.le⟩).2)
        t htLocal x hxLocal
  have hlocal' : (u t x)⁻¹ ≤ F ^ (2 / p) * Dmoving ^ (1 / p) := by
    simpa only [F, Dmoving, v, localizer, gradientCost, n,
      aOuter, pivot, bOuter] using hlocal
  calc
    (u t x)⁻¹ ≤ F ^ (2 / p) * Dmoving ^ (1 / p) := hlocal'
    _ ≤ F ^ (2 / p) * (V.toReal ^ (1 / p) * Nouter) :=
      mul_le_mul_of_nonneg_left hrootOuter (Real.rpow_nonneg hF _)
    _ = evolvingBombieriGiustiLatePointwiseFactor
          n V C G B p τ c d D lower upper * Nouter := by
      unfold evolvingBombieriGiustiLatePointwiseFactor
      dsimp only [F, gradientCost, aOuter, pivot, bOuter]
      ring

theorem early_localizedSpacetimeRpowNorm_le_exp_tsum_canonicalEvolvingBombieriGiustiThreshold_of_exponentialTimeRescale_of_evolving_supersolution
    (qMetric : SmoothRiemannianMetric I M)
    (g : ℝ → SmoothRiemannianMetric I M)
    (hdim : 2 < (Module.finrank ℝ E : ℝ))
    (rho outer : SmoothScalar qMetric)
    (averagingCutoff : M → ℝ)
    (u : ℝ → M → ℝ)
    (hu : ContMDiff ((modelWithCornersSelf ℝ ℝ).prod I)
      (modelWithCornersSelf ℝ ℝ) ∞
      (fun z : ℝ × M => u z.1 z.2))
    (hpos : ∀ t x, 0 < u t x)
    (Ccenter Ctail H W rate : ℝ)
    {p₀ A b τ C G B lower upper t₀ : ℝ}
    (V : ℝ≥0∞)
    (hp₀ : 0 < p₀) (hp₀_one : p₀ < 1)
    (hAb : A ≤ b) (hbτ : b < τ)
    (hC : 0 ≤ C) (hG : 0 ≤ G) (hB : 0 ≤ B)
    (hCtail : 0 ≤ Ctail) (hrate : 0 ≤ rate)
    (hlowerUpper : lower < upper)
    (hg : MetricFamilyRegularAt (I := I) g t₀)
    (hgram : ∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)),
      ContMDiffOn ((modelWithCornersSelf ℝ ℝ).prod I)
        (modelWithCornersSelf ℝ ℝ) ∞
        (fun z : ℝ × M =>
          chartGramMatrix (I := I) (g z.1) x₀ z.2 i j)
        (Set.univ ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet))
    (haveragingCutoff : ContMDiff I (modelWithCornersSelf ℝ ℝ) ∞
      averagingCutoff)
    (hne : ∃ x, averagingCutoff x ≠ 0)
    (hPcenter : HasEvolvingLocalizedPoincare
      (I := I) (M := M) g averagingCutoff averagingCutoff Ccenter (Icc A τ))
    (hPtail : HasEvolvingLocalizedPoincareAtAverage
      (I := I) (M := M) g outer.toFun averagingCutoff Ctail (Icc A τ))
    (htraceAbs : ∀ t ∈ Icc A τ, ∀ x : M,
      |(1 / 2) * traceTimeDerivMetric (I := I) g t x| ≤ H)
    (hmass_le : ∀ t ∈ Icc A τ,
      evolvingCutoffMass (I := I) (M := M) g averagingCutoff t ≤ W)
    (hdrift_le : ∀ t ∈ Icc A τ,
      evolvingLogCenterDrift
        (I := I) (M := M) g averagingCutoff Ccenter H t ≤ rate)
    (hSobolev : ∀ t ∈ Icc A τ,
      localizedSobolevConstant (I := I) (M := M) (g t) hdim ≤ C)
    (htrace : ∀ t ∈ Icc A τ, ∀ x : M,
      -traceTimeDerivMetric (I := I) g t x ≤ B)
    (hrho : ∀ t ∈ Icc A τ, ∀ x : M,
      (g t).inner x
          (gradFun (I := I) (g t) rho.toFun x)
          (gradFun (I := I) (g t) rho.toFun x) ≤ G)
    (hpde : ∀ t ∈ Icc A τ, ∀ x : M,
      Δ_g (I := I) (g t)
          (smoothScalarSlice (I := I) (g t) u hu t).toContMDiffMap x ≤
        deriv (fun s => u s x) t)
    (hVtop : V ≠ ⊤)
    (hvolume : ∀ t ∈ Icc A τ,
      riemannianMeasureFamily (I := I) (M := M) g t ≤
          V • riemannianVolumeMeasure (I := I) (M := M) qMetric ∧
        riemannianVolumeMeasure (I := I) (M := M) qMetric ≤
          V • riemannianMeasureFamily (I := I) (M := M) g t)
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
        outer.toFun x ^ 2) :
    let center := evolvingLocalizedAverage
      (I := I) (M := M) g averagingCutoff
        (fun s x => Real.log (u s x)) τ + rate * τ
    let v := exponentialTimeRescale rate center u
    let c₀ := max 1 (V.toReal * (4 * Ctail * W))
    localizedSpacetimeRpowNorm (I := I) (M := M)
        (bombieriGiustiSpatialCutoff rho lower upper 0) v p₀ A b ≤
      Real.exp (∑' k : ℕ, (3 / 4 : ℝ) ^ k *
        (bombieriGiustiThreshold p₀ c₀
          (canonicalEvolvingEarlyBombieriGiustiReverseCost
            (Module.finrank ℝ E) V C p₀ A b τ G B lower upper k) / 4)) := by
  let logu : ℝ → M → ℝ := fun s x => Real.log (u s x)
  let center := evolvingLocalizedAverage
    (I := I) (M := M) g averagingCutoff logu τ + rate * τ
  let v := exponentialTimeRescale rate center u
  let c₀ := max 1 (V.toReal * (4 * Ctail * W))
  have hc₀ : 0 < c₀ := zero_lt_one.trans_le (le_max_left _ _)
  have hv := contMDiff_exponentialTimeRescale rate center u hu
  have hvpos := exponentialTimeRescale_pos rate center u hpos
  have hvpde : ∀ t ∈ Icc A τ, ∀ x : M,
      Δ_g (I := I) (g t)
          (smoothScalarSlice (I := I) (g t) v hv t).toContMDiffMap x ≤
        deriv (fun s => v s x) t := by
    intro t ht x
    exact exponential_time_rescale_supersolution
      (I := I) (M := M) (g t) rate center hrate u hu hpos (hpde t ht x)
  have htail : ∀ r, 0 < r →
      (localizedSpacetimeMeasure (I := I) (M := M) outer A τ).real
        {z | r < Real.log (v z.1 z.2)} ≤ c₀ / r := by
    intro r hr
    have hraw :=
      early_localizedSpacetimeMeasure_log_superlevel_tail_of_exponentialTimeRescale_of_evolving_supersolution
        (I := I) (M := M) g outer averagingCutoff u hu hpos
          Ccenter Ctail H W rate (hAb.trans hbτ.le) hr hCtail hg V hVtop
          (fun t ht => (hvolume t ht).2) hgram haveragingCutoff hne
          hPcenter hPtail htraceAbs hmass_le hdrift_le hpde
    calc
      (localizedSpacetimeMeasure (I := I) (M := M) outer A τ).real
          {z | r < Real.log (v z.1 z.2)} ≤
        V.toReal * (4 * Ctail * W / r) := by
          simpa only [v, center, logu] using hraw
      _ = (V.toReal * (4 * Ctail * W)) / r := by ring
      _ ≤ c₀ / r := div_le_div_of_nonneg_right (le_max_right _ _) hr.le
  simpa only [center, v, c₀, logu] using
    (early_localizedSpacetimeRpowNorm_le_exp_tsum_canonicalEvolvingBombieriGiustiThreshold_of_supersolution_of_log_tail
      (I := I) (M := M) qMetric g hdim rho outer v hv hvpos
        V hp₀ hp₀_one hc₀ hAb hbτ hC hG hB hlowerUpper hg hgram
        hSobolev htrace hrho hvpde hVtop hvolume hmeasure hmeasure_le_one
        houter htail)

theorem late_localizedSpacetimeRpowNorm_inv_le_exp_tsum_canonicalEvolvingBombieriGiustiThreshold_of_exponentialTimeRescale_of_evolving_supersolution_of_volume_le
    (qMetric : SmoothRiemannianMetric I M)
    (g : ℝ → SmoothRiemannianMetric I M)
    (hdim : 2 < (Module.finrank ℝ E : ℝ))
    (rho outer : SmoothScalar qMetric)
    (averagingCutoff : M → ℝ)
    (u : ℝ → M → ℝ)
    (hu : ContMDiff ((modelWithCornersSelf ℝ ℝ).prod I)
      (modelWithCornersSelf ℝ ℝ) ∞
      (fun z : ℝ × M => u z.1 z.2))
    (hpos : ∀ t x, 0 < u t x)
    (Ccenter Ctail H W rate : ℝ)
    {p₀ τ c d D C G B lower upper t₀ : ℝ}
    (V : ℝ≥0∞)
    (hp₀ : 0 < p₀)
    (hτc : τ < c) (hcd : c ≤ d) (hdD : d < D)
    (hC : 0 ≤ C) (hG : 0 ≤ G) (hB : 0 ≤ B)
    (hCtail : 0 ≤ Ctail) (hrate : 0 ≤ rate)
    (hlowerUpper : lower < upper)
    (hg : MetricFamilyRegularAt (I := I) g t₀)
    (hgram : ∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)),
      ContMDiffOn ((modelWithCornersSelf ℝ ℝ).prod I)
        (modelWithCornersSelf ℝ ℝ) ∞
        (fun z : ℝ × M =>
          chartGramMatrix (I := I) (g z.1) x₀ z.2 i j)
        (Set.univ ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet))
    (haveragingCutoff : ContMDiff I (modelWithCornersSelf ℝ ℝ) ∞
      averagingCutoff)
    (hne : ∃ x, averagingCutoff x ≠ 0)
    (hPcenter : HasEvolvingLocalizedPoincare
      (I := I) (M := M) g averagingCutoff averagingCutoff Ccenter (Icc τ D))
    (hPtail : HasEvolvingLocalizedPoincareAtAverage
      (I := I) (M := M) g outer.toFun averagingCutoff Ctail (Icc τ D))
    (htraceAbs : ∀ t ∈ Icc τ D, ∀ x : M,
      |(1 / 2) * traceTimeDerivMetric (I := I) g t x| ≤ H)
    (hmass_le : ∀ t ∈ Icc τ D,
      evolvingCutoffMass (I := I) (M := M) g averagingCutoff t ≤ W)
    (hdrift_le : ∀ t ∈ Icc τ D,
      evolvingLogCenterDrift
        (I := I) (M := M) g averagingCutoff Ccenter H t ≤ rate)
    (hSobolev : ∀ t ∈ Icc τ D,
      localizedSobolevConstant (I := I) (M := M) (g t) hdim ≤ C)
    (htrace : ∀ t ∈ Icc τ D, ∀ x : M,
      traceTimeDerivMetric (I := I) g t x ≤ B)
    (hrho : ∀ t ∈ Icc τ D, ∀ x : M,
      (g t).inner x
          (gradFun (I := I) (g t) rho.toFun x)
          (gradFun (I := I) (g t) rho.toFun x) ≤ G)
    (hpde : ∀ t ∈ Icc τ D, ∀ x : M,
      Δ_g (I := I) (g t)
          (smoothScalarSlice (I := I) (g t) u hu t).toContMDiffMap x ≤
        deriv (fun s => u s x) t)
    (hVzero : V ≠ 0) (hVtop : V ≠ ⊤)
    (hvolume : ∀ t ∈ Icc τ D,
      riemannianMeasureFamily (I := I) (M := M) g t ≤
          V • riemannianVolumeMeasure (I := I) (M := M) qMetric ∧
        riemannianVolumeMeasure (I := I) (M := M) qMetric ≤
          V • riemannianMeasureFamily (I := I) (M := M) g t)
    (hmeasure : ∀ k,
      localizedSpacetimeMeasure (I := I) (M := M)
        (bombieriGiustiSpatialCutoff rho lower upper k)
          (bombieriGiustiDescendingLevel τ c k)
          (bombieriGiustiIncreasingLevel d D k) ≠ 0)
    (hmeasure_le_one : ∀ k,
      (localizedSpacetimeMeasure (I := I) (M := M)
        (bombieriGiustiSpatialCutoff rho lower upper k)
          (bombieriGiustiDescendingLevel τ c k)
          (bombieriGiustiIncreasingLevel d D k)).real Set.univ ≤ 1)
    (houter : ∀ k x,
      (bombieriGiustiSpatialCutoff rho lower upper k).toFun x ^ 2 ≤
        outer.toFun x ^ 2) :
    let center := evolvingLocalizedAverage
      (I := I) (M := M) g averagingCutoff
        (fun s x => Real.log (u s x)) τ + rate * τ
    let v := exponentialTimeRescale rate center u
    let c₀ := max 1 (V.toReal * (4 * Ctail * W))
    localizedSpacetimeRpowNorm (I := I) (M := M)
        (bombieriGiustiSpatialCutoff rho lower upper 0)
        (fun t x => (v t x)⁻¹) p₀ c d ≤
      Real.exp (∑' k : ℕ, (3 / 4 : ℝ) ^ k *
        (bombieriGiustiThreshold p₀ c₀
          (canonicalEvolvingLateBombieriGiustiReverseCost
            (Module.finrank ℝ E) V V C G B τ c d D lower upper k) / 4)) := by
  let logu : ℝ → M → ℝ := fun s x => Real.log (u s x)
  let center := evolvingLocalizedAverage
    (I := I) (M := M) g averagingCutoff logu τ + rate * τ
  let v := exponentialTimeRescale rate center u
  let c₀ := max 1 (V.toReal * (4 * Ctail * W))
  have hc₀ : 0 < c₀ := zero_lt_one.trans_le (le_max_left _ _)
  have hv := contMDiff_exponentialTimeRescale rate center u hu
  have hvpos := exponentialTimeRescale_pos rate center u hpos
  have hvpde : ∀ t ∈ Icc τ D, ∀ x : M,
      Δ_g (I := I) (g t)
          (smoothScalarSlice (I := I) (g t) v hv t).toContMDiffMap x ≤
        deriv (fun s => v s x) t := by
    intro t ht x
    exact exponential_time_rescale_supersolution
      (I := I) (M := M) (g t) rate center hrate u hu hpos (hpde t ht x)
  have htail : ∀ r, 0 < r →
      (localizedSpacetimeMeasure (I := I) (M := M) outer τ D).real
        {z | Real.log (v z.1 z.2) < -r} ≤ c₀ / r := by
    intro r hr
    have hraw :=
      late_localizedSpacetimeMeasure_log_sublevel_tail_of_exponentialTimeRescale_of_evolving_supersolution
        (I := I) (M := M) g outer averagingCutoff u hu hpos
          Ccenter Ctail H W rate (hτc.le.trans (hcd.trans hdD.le))
          hr hCtail hg V hVtop (fun t ht => (hvolume t ht).2) hgram
          haveragingCutoff hne hPcenter hPtail htraceAbs hmass_le
          hdrift_le hpde
    calc
      (localizedSpacetimeMeasure (I := I) (M := M) outer τ D).real
          {z | Real.log (v z.1 z.2) < -r} ≤
        V.toReal * (4 * Ctail * W / r) := by
          simpa only [v, center, logu] using hraw
      _ = (V.toReal * (4 * Ctail * W)) / r := by ring
      _ ≤ c₀ / r := div_le_div_of_nonneg_right (le_max_right _ _) hr.le
  simpa only [center, v, c₀, logu] using
    (late_localizedSpacetimeRpowNorm_inv_le_exp_tsum_canonicalEvolvingBombieriGiustiThreshold_of_supersolution_of_log_tail_of_volume_le
      (I := I) (M := M) qMetric g hdim rho outer v hv hvpos
        V V hp₀ hc₀ hτc hcd hdD hC hG hB hlowerUpper hg hgram
        hSobolev hvpde htrace hrho hVtop hVzero hVtop
        (fun t ht => (hvolume t ht).2) (fun t ht => (hvolume t ht).1)
        hmeasure hmeasure_le_one houter htail)

def canonicalEvolvingEarlyBombieriGiustiThresholdSum
    (n : ℕ) (V : ℝ≥0∞)
    (C p₀ c₀ A b τ G B lower upper : ℝ) : ℝ :=
  ∑' k : ℕ, (3 / 4 : ℝ) ^ k *
    (bombieriGiustiThreshold p₀ c₀
      (canonicalEvolvingEarlyBombieriGiustiReverseCost
        n V C p₀ A b τ G B lower upper k) / 4)

def canonicalEvolvingLateBombieriGiustiThresholdSum
    (n : ℕ) (Vfixed Vmoving : ℝ≥0∞)
    (C G B p₀ c₀ τ c d D lower upper : ℝ) : ℝ :=
  ∑' k : ℕ, (3 / 4 : ℝ) ^ k *
    (bombieriGiustiThreshold p₀ c₀
      (canonicalEvolvingLateBombieriGiustiReverseCost
        n Vfixed Vmoving C G B τ c d D lower upper k) / 4)

def canonicalEvolvingLateBombieriGiustiThresholdSumNatAdd
    (n : ℕ) (Vfixed Vmoving : ℝ≥0∞)
    (C G B p₀ c₀ τ c d D lower upper : ℝ) (j : ℕ) : ℝ :=
  ∑' k : ℕ, (3 / 4 : ℝ) ^ k *
    (bombieriGiustiThreshold p₀ c₀
      (canonicalEvolvingLateBombieriGiustiReverseCost
        n Vfixed Vmoving C G B τ c d D lower upper (j + k)) / 4)

theorem evolvingBombieriGiustiLatePointwiseFactor_nonneg
    (n : ℕ) (V : ℝ≥0∞) (C G B p τ c d D lower upper : ℝ) :
    0 ≤ evolvingBombieriGiustiLatePointwiseFactor
      n V C G B p τ c d D lower upper := by
  exact mul_nonneg
    (Real.rpow_nonneg
      (mul_nonneg (zero_le_one.trans (le_max_left 1 V.toReal))
        (Real.exp_pos _).le) _)
    (Real.rpow_nonneg ENNReal.toReal_nonneg _)

def canonicalEvolvingBombieriGiustiWeakHarnackBound
    (n : ℕ) (V : ℝ≥0∞)
    (C G Bearly Blate rate p₀ c₀ A b τ c d D lower upper : ℝ) : ℝ :=
  Real.exp (rate * (D - A)) *
    (Real.exp (canonicalEvolvingEarlyBombieriGiustiThresholdSum
      n V C p₀ c₀ A b τ G Bearly lower upper) *
    (evolvingBombieriGiustiLatePointwiseFactor
      n V C G Blate p₀ τ c d D lower upper *
    Real.exp (canonicalEvolvingLateBombieriGiustiThresholdSumNatAdd
      n V V C G Blate p₀ c₀ τ c d D lower upper 1)))

def canonicalEvolvingBombieriGiustiCrossoverBound
    (n : ℕ) (V : ℝ≥0∞)
    (C G Bearly Blate rate p₀ c₀ A b τ c d D lower upper : ℝ) : ℝ :=
  Real.exp (rate * (d - A)) *
    (Real.exp (canonicalEvolvingEarlyBombieriGiustiThresholdSum
      n V C p₀ c₀ A b τ G Bearly lower upper) *
    Real.exp (canonicalEvolvingLateBombieriGiustiThresholdSum
      n V V C G Blate p₀ c₀ τ c d D lower upper))

omit [I.Boundaryless] in
theorem localizedSpacetimeRpowNorm_mul_inv_le_canonicalEvolvingBombieriGiustiCrossoverBound_of_exponentialTimeRescale_bounds
    {qMetric : SmoothRiemannianMetric I M}
    (rho : SmoothScalar qMetric)
    (rate center : ℝ)
    (u : ℝ → M → ℝ)
    (hu : ContMDiff ((modelWithCornersSelf ℝ ℝ).prod I)
      (modelWithCornersSelf ℝ ℝ) ∞
      (fun z : ℝ × M => u z.1 z.2))
    (hpos : ∀ t x, 0 < u t x)
    {n : ℕ} {V : ℝ≥0∞}
    {C G Bearly Blate p₀ c₀ A b τ c d D lower upper : ℝ}
    (hp₀ : 0 < p₀) (hrate : 0 ≤ rate)
    (hearly : localizedSpacetimeRpowNorm (I := I) (M := M)
      (bombieriGiustiSpatialCutoff rho lower upper 0)
      (exponentialTimeRescale rate center u) p₀ A b ≤
        Real.exp (canonicalEvolvingEarlyBombieriGiustiThresholdSum
          n V C p₀ c₀ A b τ G Bearly lower upper))
    (hlate : localizedSpacetimeRpowNorm (I := I) (M := M)
      (bombieriGiustiSpatialCutoff rho lower upper 0)
      (fun t x => (exponentialTimeRescale rate center u t x)⁻¹) p₀ c d ≤
        Real.exp (canonicalEvolvingLateBombieriGiustiThresholdSum
          n V V C G Blate p₀ c₀ τ c d D lower upper)) :
    localizedSpacetimeRpowNorm (I := I) (M := M)
        (bombieriGiustiSpatialCutoff rho lower upper 0) u p₀ A b *
      localizedSpacetimeRpowNorm (I := I) (M := M)
        (bombieriGiustiSpatialCutoff rho lower upper 0)
          (fun t x => (u t x)⁻¹) p₀ c d ≤
      canonicalEvolvingBombieriGiustiCrossoverBound
        n V C G Bearly Blate rate p₀ c₀ A b τ c d D lower upper := by
  have hbound :=
    localizedSpacetimeRpowNorm_mul_inv_le_of_exponentialTimeRescale_bounds
      (I := I) (M := M)
      (bombieriGiustiSpatialCutoff rho lower upper 0)
      (bombieriGiustiSpatialCutoff rho lower upper 0)
      rate center u hu hpos hp₀ hrate (Real.exp_pos _).le hearly hlate
  simpa only [canonicalEvolvingBombieriGiustiCrossoverBound] using hbound

omit [I.Boundaryless] in
theorem localizedSpacetimeRpowNorm_le_canonicalEvolvingBombieriGiustiWeakHarnackBound_mul_of_exponentialTimeRescale_bounds
    {qMetric : SmoothRiemannianMetric I M}
    (rho : SmoothScalar qMetric)
    (rate center : ℝ)
    (u : ℝ → M → ℝ)
    (hu : ContMDiff ((modelWithCornersSelf ℝ ℝ).prod I)
      (modelWithCornersSelf ℝ ℝ) ∞
      (fun z : ℝ × M => u z.1 z.2))
    (hpos : ∀ t x, 0 < u t x)
    (x : M)
    {n : ℕ} {V : ℝ≥0∞}
    {C G Bearly Blate p₀ c₀ A b τ c d D lower upper t : ℝ}
    (hp₀ : 0 < p₀) (hrate : 0 ≤ rate) (htD : t ≤ D)
    (hearly : localizedSpacetimeRpowNorm (I := I) (M := M)
      (bombieriGiustiSpatialCutoff rho lower upper 0)
      (exponentialTimeRescale rate center u) p₀ A b ≤
        Real.exp (canonicalEvolvingEarlyBombieriGiustiThresholdSum
          n V C p₀ c₀ A b τ G Bearly lower upper))
    (hlate : (exponentialTimeRescale rate center u t x)⁻¹ ≤
      evolvingBombieriGiustiLatePointwiseFactor
          n V C G Blate p₀ τ c d D lower upper *
        Real.exp (canonicalEvolvingLateBombieriGiustiThresholdSumNatAdd
          n V V C G Blate p₀ c₀ τ c d D lower upper 1)) :
    localizedSpacetimeRpowNorm (I := I) (M := M)
        (bombieriGiustiSpatialCutoff rho lower upper 0) u p₀ A b ≤
      canonicalEvolvingBombieriGiustiWeakHarnackBound
        n V C G Bearly Blate rate p₀ c₀ A b τ c d D lower upper * u t x := by
  have hbound :=
    localizedSpacetimeRpowNorm_le_of_exponentialTimeRescale_bound_of_inv_bound
      (I := I) (M := M) (bombieriGiustiSpatialCutoff rho lower upper 0)
        rate center u hu hpos x hp₀ hrate htD (Real.exp_pos _).le
        (mul_nonneg
          (evolvingBombieriGiustiLatePointwiseFactor_nonneg
            n V C G Blate p₀ τ c d D lower upper)
          (Real.exp_pos _).le)
        hearly hlate
  simpa only [canonicalEvolvingBombieriGiustiWeakHarnackBound] using hbound

theorem localizedSpacetimeRpowNorm_mul_inv_le_canonicalEvolvingBombieriGiustiCrossoverBound_of_supersolution
    (qMetric : SmoothRiemannianMetric I M)
    (g : ℝ → SmoothRiemannianMetric I M)
    (hdim : 2 < (Module.finrank ℝ E : ℝ))
    (rho outer : SmoothScalar qMetric)
    (averagingCutoff : M → ℝ)
    (u : ℝ → M → ℝ)
    (hu : ContMDiff ((modelWithCornersSelf ℝ ℝ).prod I)
      (modelWithCornersSelf ℝ ℝ) ∞
      (fun z : ℝ × M => u z.1 z.2))
    (hpos : ∀ t x, 0 < u t x)
    (Ccenter Ctail H W rate : ℝ)
    {p₀ A b τ c d D C G Bearly Blate lower upper t₀ : ℝ}
    (V : ℝ≥0∞)
    (hp₀ : 0 < p₀) (hp₀_one : p₀ < 1)
    (hAb : A ≤ b) (hbτ : b < τ)
    (hτc : τ < c) (hcd : c ≤ d) (hdD : d < D)
    (hC : 0 ≤ C) (hG : 0 ≤ G)
    (hBearly : 0 ≤ Bearly) (hBlate : 0 ≤ Blate)
    (hCtail : 0 ≤ Ctail) (hrate : 0 ≤ rate)
    (hlowerUpper : lower < upper)
    (hg : MetricFamilyRegularAt (I := I) g t₀)
    (hgram : ∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)),
      ContMDiffOn ((modelWithCornersSelf ℝ ℝ).prod I)
        (modelWithCornersSelf ℝ ℝ) ∞
        (fun z : ℝ × M =>
          chartGramMatrix (I := I) (g z.1) x₀ z.2 i j)
        (Set.univ ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet))
    (haveragingCutoff : ContMDiff I (modelWithCornersSelf ℝ ℝ) ∞
      averagingCutoff)
    (hne : ∃ x, averagingCutoff x ≠ 0)
    (hPcenter : HasEvolvingLocalizedPoincare
      (I := I) (M := M) g averagingCutoff averagingCutoff Ccenter (Icc A D))
    (hPtail : HasEvolvingLocalizedPoincareAtAverage
      (I := I) (M := M) g outer.toFun averagingCutoff Ctail (Icc A D))
    (htraceAbs : ∀ t ∈ Icc A D, ∀ x : M,
      |(1 / 2) * traceTimeDerivMetric (I := I) g t x| ≤ H)
    (hmass_le : ∀ t ∈ Icc A D,
      evolvingCutoffMass (I := I) (M := M) g averagingCutoff t ≤ W)
    (hdrift_le : ∀ t ∈ Icc A D,
      evolvingLogCenterDrift
        (I := I) (M := M) g averagingCutoff Ccenter H t ≤ rate)
    (hSobolev : ∀ t ∈ Icc A D,
      localizedSobolevConstant (I := I) (M := M) (g t) hdim ≤ C)
    (htraceEarly : ∀ t ∈ Icc A D, ∀ x : M,
      -traceTimeDerivMetric (I := I) g t x ≤ Bearly)
    (htraceLate : ∀ t ∈ Icc A D, ∀ x : M,
      traceTimeDerivMetric (I := I) g t x ≤ Blate)
    (hrho : ∀ t ∈ Icc A D, ∀ x : M,
      (g t).inner x
          (gradFun (I := I) (g t) rho.toFun x)
          (gradFun (I := I) (g t) rho.toFun x) ≤ G)
    (hpde : ∀ t ∈ Icc A D, ∀ x : M,
      Δ_g (I := I) (g t)
          (smoothScalarSlice (I := I) (g t) u hu t).toContMDiffMap x ≤
        deriv (fun s => u s x) t)
    (hVzero : V ≠ 0) (hVtop : V ≠ ⊤)
    (hvolume : ∀ t ∈ Icc A D,
      riemannianMeasureFamily (I := I) (M := M) g t ≤
          V • riemannianVolumeMeasure (I := I) (M := M) qMetric ∧
        riemannianVolumeMeasure (I := I) (M := M) qMetric ≤
          V • riemannianMeasureFamily (I := I) (M := M) g t)
    (hearlyMeasure : ∀ k,
      localizedSpacetimeMeasure (I := I) (M := M)
        (bombieriGiustiSpatialCutoff rho lower upper k) A
          (bombieriGiustiIncreasingLevel b τ k) ≠ 0)
    (hearlyMeasure_le_one : ∀ k,
      (localizedSpacetimeMeasure (I := I) (M := M)
        (bombieriGiustiSpatialCutoff rho lower upper k) A
          (bombieriGiustiIncreasingLevel b τ k)).real Set.univ ≤ 1)
    (hlateMeasure : ∀ k,
      localizedSpacetimeMeasure (I := I) (M := M)
        (bombieriGiustiSpatialCutoff rho lower upper k)
          (bombieriGiustiDescendingLevel τ c k)
          (bombieriGiustiIncreasingLevel d D k) ≠ 0)
    (hlateMeasure_le_one : ∀ k,
      (localizedSpacetimeMeasure (I := I) (M := M)
        (bombieriGiustiSpatialCutoff rho lower upper k)
          (bombieriGiustiDescendingLevel τ c k)
          (bombieriGiustiIncreasingLevel d D k)).real Set.univ ≤ 1)
    (houter : ∀ k x,
      (bombieriGiustiSpatialCutoff rho lower upper k).toFun x ^ 2 ≤
        outer.toFun x ^ 2) :
    let c₀ := max 1 (V.toReal * (4 * Ctail * W))
    localizedSpacetimeRpowNorm (I := I) (M := M)
        (bombieriGiustiSpatialCutoff rho lower upper 0) u p₀ A b *
      localizedSpacetimeRpowNorm (I := I) (M := M)
        (bombieriGiustiSpatialCutoff rho lower upper 0)
          (fun t x => (u t x)⁻¹) p₀ c d ≤
      canonicalEvolvingBombieriGiustiCrossoverBound
        (Module.finrank ℝ E) V C G Bearly Blate rate p₀ c₀
          A b τ c d D lower upper := by
  let n := Module.finrank ℝ E
  let logu : ℝ → M → ℝ := fun s x => Real.log (u s x)
  let center := evolvingLocalizedAverage
    (I := I) (M := M) g averagingCutoff logu τ + rate * τ
  let v := exponentialTimeRescale rate center u
  let c₀ := max 1 (V.toReal * (4 * Ctail * W))
  have hAτ : A ≤ τ := hAb.trans hbτ.le
  have hτD : τ ≤ D := hτc.le.trans (hcd.trans hdD.le)
  have hearly : localizedSpacetimeRpowNorm (I := I) (M := M)
      (bombieriGiustiSpatialCutoff rho lower upper 0) v p₀ A b ≤
    Real.exp (canonicalEvolvingEarlyBombieriGiustiThresholdSum
      n V C p₀ c₀ A b τ G Bearly lower upper) := by
    simpa only [v, center, logu, c₀, n,
      canonicalEvolvingEarlyBombieriGiustiThresholdSum] using
      (early_localizedSpacetimeRpowNorm_le_exp_tsum_canonicalEvolvingBombieriGiustiThreshold_of_exponentialTimeRescale_of_evolving_supersolution
        (I := I) (M := M) qMetric g hdim rho outer averagingCutoff
          u hu hpos Ccenter Ctail H W rate V hp₀ hp₀_one hAb hbτ
          hC hG hBearly hCtail hrate hlowerUpper hg hgram
          haveragingCutoff hne
          (fun t ht => hPcenter t ⟨ht.1, ht.2.trans hτD⟩)
          (fun t ht => hPtail t ⟨ht.1, ht.2.trans hτD⟩)
          (fun t ht => htraceAbs t ⟨ht.1, ht.2.trans hτD⟩)
          (fun t ht => hmass_le t ⟨ht.1, ht.2.trans hτD⟩)
          (fun t ht => hdrift_le t ⟨ht.1, ht.2.trans hτD⟩)
          (fun t ht => hSobolev t ⟨ht.1, ht.2.trans hτD⟩)
          (fun t ht => htraceEarly t ⟨ht.1, ht.2.trans hτD⟩)
          (fun t ht => hrho t ⟨ht.1, ht.2.trans hτD⟩)
          (fun t ht => hpde t ⟨ht.1, ht.2.trans hτD⟩)
          hVtop (fun t ht => hvolume t ⟨ht.1, ht.2.trans hτD⟩)
          hearlyMeasure hearlyMeasure_le_one houter)
  have hlate : localizedSpacetimeRpowNorm (I := I) (M := M)
      (bombieriGiustiSpatialCutoff rho lower upper 0)
        (fun t x => (v t x)⁻¹) p₀ c d ≤
    Real.exp (canonicalEvolvingLateBombieriGiustiThresholdSum
      n V V C G Blate p₀ c₀ τ c d D lower upper) := by
    simpa only [v, center, logu, c₀, n,
      canonicalEvolvingLateBombieriGiustiThresholdSum] using
      (late_localizedSpacetimeRpowNorm_inv_le_exp_tsum_canonicalEvolvingBombieriGiustiThreshold_of_exponentialTimeRescale_of_evolving_supersolution_of_volume_le
        (I := I) (M := M) qMetric g hdim rho outer averagingCutoff
          u hu hpos Ccenter Ctail H W rate V hp₀ hτc hcd hdD
          hC hG hBlate hCtail hrate hlowerUpper hg hgram
          haveragingCutoff hne
          (fun t ht => hPcenter t ⟨hAτ.trans ht.1, ht.2⟩)
          (fun t ht => hPtail t ⟨hAτ.trans ht.1, ht.2⟩)
          (fun t ht => htraceAbs t ⟨hAτ.trans ht.1, ht.2⟩)
          (fun t ht => hmass_le t ⟨hAτ.trans ht.1, ht.2⟩)
          (fun t ht => hdrift_le t ⟨hAτ.trans ht.1, ht.2⟩)
          (fun t ht => hSobolev t ⟨hAτ.trans ht.1, ht.2⟩)
          (fun t ht => htraceLate t ⟨hAτ.trans ht.1, ht.2⟩)
          (fun t ht => hrho t ⟨hAτ.trans ht.1, ht.2⟩)
          (fun t ht => hpde t ⟨hAτ.trans ht.1, ht.2⟩)
          hVzero hVtop (fun t ht => hvolume t ⟨hAτ.trans ht.1, ht.2⟩)
          hlateMeasure hlateMeasure_le_one houter)
  simpa only [c₀, n] using
    (localizedSpacetimeRpowNorm_mul_inv_le_canonicalEvolvingBombieriGiustiCrossoverBound_of_exponentialTimeRescale_bounds
      (I := I) (M := M) rho rate center u hu hpos hp₀ hrate hearly hlate)

theorem localizedSpacetimeRpowNorm_le_canonicalEvolvingBombieriGiustiWeakHarnackBound_mul_of_supersolution
    (qMetric : SmoothRiemannianMetric I M)
    (g : ℝ → SmoothRiemannianMetric I M)
    (hdim : 2 < (Module.finrank ℝ E : ℝ))
    (rho outer : SmoothScalar qMetric)
    (averagingCutoff : M → ℝ)
    (u : ℝ → M → ℝ)
    (hu : ContMDiff ((modelWithCornersSelf ℝ ℝ).prod I)
      (modelWithCornersSelf ℝ ℝ) ∞
      (fun z : ℝ × M => u z.1 z.2))
    (hpos : ∀ t x, 0 < u t x)
    (Ccenter Ctail H W rate : ℝ)
    {p₀ A b τ c d D C G Bearly Blate lower upper t₀ : ℝ}
    (V : ℝ≥0∞)
    (hp₀ : 0 < p₀) (hp₀_one : p₀ < 1)
    (hAb : A ≤ b) (hbτ : b < τ)
    (hτc : τ < c) (hcd : c ≤ d) (hdD : d < D)
    (hC : 0 ≤ C) (hG : 0 ≤ G)
    (hBearly : 0 ≤ Bearly) (hBlate : 0 ≤ Blate)
    (hCtail : 0 ≤ Ctail) (hrate : 0 ≤ rate)
    (hlowerUpper : lower < upper)
    (hg : MetricFamilyRegularAt (I := I) g t₀)
    (hgram : ∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)),
      ContMDiffOn ((modelWithCornersSelf ℝ ℝ).prod I)
        (modelWithCornersSelf ℝ ℝ) ∞
        (fun z : ℝ × M =>
          chartGramMatrix (I := I) (g z.1) x₀ z.2 i j)
        (Set.univ ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet))
    (haveragingCutoff : ContMDiff I (modelWithCornersSelf ℝ ℝ) ∞
      averagingCutoff)
    (hne : ∃ x, averagingCutoff x ≠ 0)
    (hPcenter : HasEvolvingLocalizedPoincare
      (I := I) (M := M) g averagingCutoff averagingCutoff Ccenter (Icc A D))
    (hPtail : HasEvolvingLocalizedPoincareAtAverage
      (I := I) (M := M) g outer.toFun averagingCutoff Ctail (Icc A D))
    (htraceAbs : ∀ t ∈ Icc A D, ∀ x : M,
      |(1 / 2) * traceTimeDerivMetric (I := I) g t x| ≤ H)
    (hmass_le : ∀ t ∈ Icc A D,
      evolvingCutoffMass (I := I) (M := M) g averagingCutoff t ≤ W)
    (hdrift_le : ∀ t ∈ Icc A D,
      evolvingLogCenterDrift
        (I := I) (M := M) g averagingCutoff Ccenter H t ≤ rate)
    (hSobolev : ∀ t ∈ Icc A D,
      localizedSobolevConstant (I := I) (M := M) (g t) hdim ≤ C)
    (htraceEarly : ∀ t ∈ Icc A D, ∀ x : M,
      -traceTimeDerivMetric (I := I) g t x ≤ Bearly)
    (htraceLate : ∀ t ∈ Icc A D, ∀ x : M,
      traceTimeDerivMetric (I := I) g t x ≤ Blate)
    (hrho : ∀ t ∈ Icc A D, ∀ x : M,
      (g t).inner x
          (gradFun (I := I) (g t) rho.toFun x)
          (gradFun (I := I) (g t) rho.toFun x) ≤ G)
    (hpde : ∀ t ∈ Icc A D, ∀ x : M,
      Δ_g (I := I) (g t)
          (smoothScalarSlice (I := I) (g t) u hu t).toContMDiffMap x ≤
        deriv (fun s => u s x) t)
    (hVzero : V ≠ 0) (hVtop : V ≠ ⊤)
    (hvolume : ∀ t ∈ Icc A D,
      riemannianMeasureFamily (I := I) (M := M) g t ≤
          V • riemannianVolumeMeasure (I := I) (M := M) qMetric ∧
        riemannianVolumeMeasure (I := I) (M := M) qMetric ≤
          V • riemannianMeasureFamily (I := I) (M := M) g t)
    (hearlyMeasure : ∀ k,
      localizedSpacetimeMeasure (I := I) (M := M)
        (bombieriGiustiSpatialCutoff rho lower upper k) A
          (bombieriGiustiIncreasingLevel b τ k) ≠ 0)
    (hearlyMeasure_le_one : ∀ k,
      (localizedSpacetimeMeasure (I := I) (M := M)
        (bombieriGiustiSpatialCutoff rho lower upper k) A
          (bombieriGiustiIncreasingLevel b τ k)).real Set.univ ≤ 1)
    (hlateMeasure : ∀ k,
      localizedSpacetimeMeasure (I := I) (M := M)
        (bombieriGiustiSpatialCutoff rho lower upper k)
          (bombieriGiustiDescendingLevel τ c k)
          (bombieriGiustiIncreasingLevel d D k) ≠ 0)
    (hlateMeasure_le_one : ∀ k,
      (localizedSpacetimeMeasure (I := I) (M := M)
        (bombieriGiustiSpatialCutoff rho lower upper k)
          (bombieriGiustiDescendingLevel τ c k)
          (bombieriGiustiIncreasingLevel d D k)).real Set.univ ≤ 1)
    (houter : ∀ k x,
      (bombieriGiustiSpatialCutoff rho lower upper k).toFun x ^ 2 ≤
        outer.toFun x ^ 2) :
    let c₀ := max 1 (V.toReal * (4 * Ctail * W))
    ∀ t ∈ Icc c d, ∀ x : M,
      (bombieriGiustiSpatialCutoff rho lower upper 0).toFun x ≠ 0 →
      localizedSpacetimeRpowNorm (I := I) (M := M)
          (bombieriGiustiSpatialCutoff rho lower upper 0) u p₀ A b ≤
        canonicalEvolvingBombieriGiustiWeakHarnackBound
          (Module.finrank ℝ E) V C G Bearly Blate rate p₀ c₀
            A b τ c d D lower upper * u t x := by
  let n := Module.finrank ℝ E
  let logu : ℝ → M → ℝ := fun s x => Real.log (u s x)
  let center := evolvingLocalizedAverage
    (I := I) (M := M) g averagingCutoff logu τ + rate * τ
  let v := exponentialTimeRescale rate center u
  let c₀ := max 1 (V.toReal * (4 * Ctail * W))
  have hc₀ : 0 < c₀ := zero_lt_one.trans_le (le_max_left _ _)
  have hAτ : A ≤ τ := hAb.trans hbτ.le
  have hτD : τ ≤ D := hτc.le.trans (hcd.trans hdD.le)
  have hv := contMDiff_exponentialTimeRescale rate center u hu
  have hvpos := exponentialTimeRescale_pos rate center u hpos
  have hvpde : ∀ t ∈ Icc τ D, ∀ x : M,
      Δ_g (I := I) (g t)
          (smoothScalarSlice (I := I) (g t) v hv t).toContMDiffMap x ≤
        deriv (fun s => v s x) t := by
    intro t ht x
    exact exponential_time_rescale_supersolution
      (I := I) (M := M) (g t) rate center hrate u hu hpos
        (hpde t ⟨hAτ.trans ht.1, ht.2⟩ x)
  have htail : ∀ r, 0 < r →
      (localizedSpacetimeMeasure (I := I) (M := M) outer τ D).real
        {z | Real.log (v z.1 z.2) < -r} ≤ c₀ / r := by
    intro r hr
    have hraw :=
      late_localizedSpacetimeMeasure_log_sublevel_tail_of_exponentialTimeRescale_of_evolving_supersolution
        (I := I) (M := M) g outer averagingCutoff u hu hpos
          Ccenter Ctail H W rate hτD hr hCtail hg V hVtop
          (fun t ht => (hvolume t ⟨hAτ.trans ht.1, ht.2⟩).2) hgram
          haveragingCutoff hne
          (fun t ht => hPcenter t ⟨hAτ.trans ht.1, ht.2⟩)
          (fun t ht => hPtail t ⟨hAτ.trans ht.1, ht.2⟩)
          (fun t ht => htraceAbs t ⟨hAτ.trans ht.1, ht.2⟩)
          (fun t ht => hmass_le t ⟨hAτ.trans ht.1, ht.2⟩)
          (fun t ht => hdrift_le t ⟨hAτ.trans ht.1, ht.2⟩)
          (fun t ht => hpde t ⟨hAτ.trans ht.1, ht.2⟩)
    calc
      (localizedSpacetimeMeasure (I := I) (M := M) outer τ D).real
          {z | Real.log (v z.1 z.2) < -r} ≤
        V.toReal * (4 * Ctail * W / r) := by
          simpa only [v, center, logu] using hraw
      _ = (V.toReal * (4 * Ctail * W)) / r := by ring
      _ ≤ c₀ / r := div_le_div_of_nonneg_right (le_max_right _ _) hr.le
  have hearly : localizedSpacetimeRpowNorm (I := I) (M := M)
      (bombieriGiustiSpatialCutoff rho lower upper 0) v p₀ A b ≤
    Real.exp (canonicalEvolvingEarlyBombieriGiustiThresholdSum
      n V C p₀ c₀ A b τ G Bearly lower upper) := by
    simpa only [v, center, logu, c₀, n,
      canonicalEvolvingEarlyBombieriGiustiThresholdSum] using
      (early_localizedSpacetimeRpowNorm_le_exp_tsum_canonicalEvolvingBombieriGiustiThreshold_of_exponentialTimeRescale_of_evolving_supersolution
        (I := I) (M := M) qMetric g hdim rho outer averagingCutoff
          u hu hpos Ccenter Ctail H W rate V hp₀ hp₀_one hAb hbτ
          hC hG hBearly hCtail hrate hlowerUpper hg hgram
          haveragingCutoff hne
          (fun t ht => hPcenter t ⟨ht.1, ht.2.trans hτD⟩)
          (fun t ht => hPtail t ⟨ht.1, ht.2.trans hτD⟩)
          (fun t ht => htraceAbs t ⟨ht.1, ht.2.trans hτD⟩)
          (fun t ht => hmass_le t ⟨ht.1, ht.2.trans hτD⟩)
          (fun t ht => hdrift_le t ⟨ht.1, ht.2.trans hτD⟩)
          (fun t ht => hSobolev t ⟨ht.1, ht.2.trans hτD⟩)
          (fun t ht => htraceEarly t ⟨ht.1, ht.2.trans hτD⟩)
          (fun t ht => hrho t ⟨ht.1, ht.2.trans hτD⟩)
          (fun t ht => hpde t ⟨ht.1, ht.2.trans hτD⟩)
          hVtop (fun t ht => hvolume t ⟨ht.1, ht.2.trans hτD⟩)
          hearlyMeasure hearlyMeasure_le_one houter)
  have hlate : localizedSpacetimeRpowNorm (I := I) (M := M)
      (bombieriGiustiSpatialCutoff rho lower upper 1)
      (fun s x => (v s x)⁻¹) p₀
      (bombieriGiustiDescendingLevel τ c 1)
      (bombieriGiustiIncreasingLevel d D 1) ≤
    Real.exp (canonicalEvolvingLateBombieriGiustiThresholdSumNatAdd
      n V V C G Blate p₀ c₀ τ c d D lower upper 1) := by
    simpa only [n, canonicalEvolvingLateBombieriGiustiThresholdSumNatAdd] using
      (late_localizedSpacetimeRpowNorm_inv_le_exp_tsum_canonicalEvolvingBombieriGiustiThreshold_nat_add_of_supersolution_of_log_tail_of_volume_le
        (I := I) (M := M) qMetric g hdim rho outer v hv hvpos
          V V hp₀ hc₀ hτc hcd hdD hC hG hBlate hlowerUpper hg hgram
          (fun t ht => hSobolev t ⟨hAτ.trans ht.1, ht.2⟩)
          hvpde
          (fun t ht => htraceLate t ⟨hAτ.trans ht.1, ht.2⟩)
          (fun t ht => hrho t ⟨hAτ.trans ht.1, ht.2⟩)
          hVtop hVzero hVtop
          (fun t ht => (hvolume t ⟨hAτ.trans ht.1, ht.2⟩).2)
          (fun t ht => (hvolume t ⟨hAτ.trans ht.1, ht.2⟩).1)
          hlateMeasure hlateMeasure_le_one houter htail 1)
  dsimp only
  intro t ht x hx
  have hpoint :=
    inv_le_evolvingBombieriGiustiLatePointwiseFactor_mul_localizedSpacetimeRpowNorm_of_volume_le
      (I := I) (M := M) qMetric g hdim rho v hv hvpos V hp₀
        hτc hcd hdD hC hG hBlate hlowerUpper hg hgram
        (fun s hs => hSobolev s ⟨hAτ.trans hs.1, hs.2⟩)
        hvpde
        (fun s hs y => htraceLate s ⟨hAτ.trans hs.1, hs.2⟩ y)
        (fun s hs y => hrho s ⟨hAτ.trans hs.1, hs.2⟩ y)
        hVzero hVtop (fun s hs => hvolume s ⟨hAτ.trans hs.1, hs.2⟩)
        t ht x hx
  have hpoint' : (v t x)⁻¹ ≤
      evolvingBombieriGiustiLatePointwiseFactor
          n V C G Blate p₀ τ c d D lower upper *
        Real.exp (canonicalEvolvingLateBombieriGiustiThresholdSumNatAdd
          n V V C G Blate p₀ c₀ τ c d D lower upper 1) :=
    hpoint.trans (mul_le_mul_of_nonneg_left hlate
      (evolvingBombieriGiustiLatePointwiseFactor_nonneg
        n V C G Blate p₀ τ c d D lower upper))
  simpa only [c₀, n, v] using
    (localizedSpacetimeRpowNorm_le_canonicalEvolvingBombieriGiustiWeakHarnackBound_mul_of_exponentialTimeRescale_bounds
      (I := I) (M := M) rho rate center u hu hpos x hp₀ hrate
        (ht.2.trans hdD.le) hearly hpoint')

end DifferentialGeometry.Analysis.Parabolic.Moser

end
