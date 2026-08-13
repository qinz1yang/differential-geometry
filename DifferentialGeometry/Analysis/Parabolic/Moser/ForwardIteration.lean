import DifferentialGeometry.Analysis.Parabolic.Moser.Iteration
import DifferentialGeometry.Analysis.Parabolic.Moser.Cutoff
import DifferentialGeometry.Analysis.Parabolic.Moser.ReverseHolder
import DifferentialGeometry.Analysis.Parabolic.Moser.SpacetimeMeasure

set_option autoImplicit false

noncomputable section

open Bundle Manifold MeasureTheory Set
open scoped ContDiff Manifold Topology

namespace DifferentialGeometry.Analysis.Parabolic.Moser

open DifferentialGeometry.Analysis.Laplacian
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Analysis.Parabolic.Energy
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Integral.Measure

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Module.Finite ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

variable [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]

private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

def forwardMoserLocalizedMass
    (n : ℕ) {g : SmoothRiemannianMetric I M} (rho : SmoothScalar g)
    (u : ℝ → M → ℝ) (p₀ a τ b : ℝ) (k : ℕ) : ℝ :=
  ∫ t in a..moserUpperTimeLevel τ b k,
    ∫ x, (spatialMoserCutoff rho (2 * k)).toFun x ^ 2 *
      u t x ^ parabolicMoserExponent n p₀ k
      ∂(riemannianVolumeMeasure (I := I) (M := M) g)

def forwardMoserNormalizedMass
    (n : ℕ) {g : SmoothRiemannianMetric I M} (rho : SmoothScalar g)
    (u : ℝ → M → ℝ) (p₀ a τ b : ℝ) (k : ℕ) : ℝ :=
  forwardMoserLocalizedMass (I := I) (M := M) n rho u p₀ a τ b k ^
    (1 / parabolicMoserExponent n p₀ k)

def forwardMoserStepCoefficient (q a t₁ t₂ K : ℝ) : ℝ :=
  (t₁ - a + 1) * max 1 (q / (2 * (1 - q))) *
      (timeCutoffDerivConstant / (t₂ - t₁) + (2 * q / (1 - q)) * K) + K

def forwardMoserStepCoefficientEnvelope (q a b T K : ℝ) : ℝ :=
  (b - a + 1) * max 1 (q / (2 * (1 - q))) *
      (timeCutoffDerivConstant * T + (2 * q / (1 - q)) * K) + K

theorem div_one_sub_mono
    {p q : ℝ} (hpq : p ≤ q) (hq : q < 1) :
    p / (1 - p) ≤ q / (1 - q) := by
  rw [div_le_div_iff₀ (sub_pos.mpr (hpq.trans_lt hq)) (sub_pos.mpr hq)]
  nlinarith

theorem forwardMoserStepCoefficient_le_envelope_mul_pow
    {q qbar a t₁ t₂ b T K Kbar : ℝ} (k : ℕ)
    (hq : 0 ≤ q) (hqqbar : q ≤ qbar) (hqbar_one : qbar < 1)
    (hat₁ : a ≤ t₁) (ht₁b : t₁ ≤ b) (ht₁t₂ : t₁ < t₂)
    (hK : 0 ≤ K)
    (htime : (t₂ - t₁)⁻¹ ≤ T * 16 ^ k)
    (hgradient : K ≤ Kbar * 16 ^ k) :
    forwardMoserStepCoefficient q a t₁ t₂ K ≤
      forwardMoserStepCoefficientEnvelope qbar a b T Kbar * 16 ^ k := by
  have hqbar : 0 ≤ qbar := hq.trans hqqbar
  have hq_one : q < 1 := hqqbar.trans_lt hqbar_one
  have hratio : q / (1 - q) ≤ qbar / (1 - qbar) :=
    div_one_sub_mono hqqbar hqbar_one
  have hratio_nonneg : 0 ≤ q / (1 - q) :=
    div_nonneg hq (sub_pos.mpr hq_one).le
  have hratio_bar_nonneg : 0 ≤ qbar / (1 - qbar) :=
    div_nonneg hqbar (sub_pos.mpr hqbar_one).le
  have hsmallRatio : q / (2 * (1 - q)) ≤ qbar / (2 * (1 - qbar)) := by
    rw [div_le_div_iff₀
      (mul_pos (by norm_num) (sub_pos.mpr hq_one))
      (mul_pos (by norm_num) (sub_pos.mpr hqbar_one))]
    nlinarith
  have hmax : max 1 (q / (2 * (1 - q))) ≤
      max 1 (qbar / (2 * (1 - qbar))) := max_le_max_left 1 hsmallRatio
  have hpow_nonneg : 0 ≤ (16 : ℝ) ^ k := pow_nonneg (by norm_num) k
  have htime_nonneg : 0 ≤ timeCutoffDerivConstant / (t₂ - t₁) :=
    div_nonneg timeCutoffDerivConstant_nonneg (sub_pos.mpr ht₁t₂).le
  have htime_bound : timeCutoffDerivConstant / (t₂ - t₁) ≤
      (timeCutoffDerivConstant * T) * 16 ^ k := by
    calc
      timeCutoffDerivConstant / (t₂ - t₁) =
          timeCutoffDerivConstant * (t₂ - t₁)⁻¹ := div_eq_mul_inv _ _
      _ ≤ timeCutoffDerivConstant * (T * 16 ^ k) :=
        mul_le_mul_of_nonneg_left htime timeCutoffDerivConstant_nonneg
      _ = (timeCutoffDerivConstant * T) * 16 ^ k := by ring
  have hlargeRatio : 2 * q / (1 - q) ≤ 2 * qbar / (1 - qbar) := by
    calc
      2 * q / (1 - q) = 2 * (q / (1 - q)) := by ring
      _ ≤ 2 * (qbar / (1 - qbar)) := by gcongr
      _ = 2 * qbar / (1 - qbar) := by ring
  have hlargeRatio_nonneg : 0 ≤ 2 * q / (1 - q) := by
    simpa only [mul_div_assoc] using mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hratio_nonneg
  have hlargeRatio_bar_nonneg : 0 ≤ 2 * qbar / (1 - qbar) := by
    simpa only [mul_div_assoc] using
      mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hratio_bar_nonneg
  have hgradient_bound : (2 * q / (1 - q)) * K ≤
      ((2 * qbar / (1 - qbar)) * Kbar) * 16 ^ k := by
    calc
      (2 * q / (1 - q)) * K ≤ (2 * qbar / (1 - qbar)) * K :=
        mul_le_mul_of_nonneg_right hlargeRatio hK
      _ ≤ (2 * qbar / (1 - qbar)) * (Kbar * 16 ^ k) :=
        mul_le_mul_of_nonneg_left hgradient hlargeRatio_bar_nonneg
      _ = ((2 * qbar / (1 - qbar)) * Kbar) * 16 ^ k := by ring
  have hinside_nonneg : 0 ≤
      timeCutoffDerivConstant / (t₂ - t₁) + (2 * q / (1 - q)) * K :=
    add_nonneg htime_nonneg (mul_nonneg hlargeRatio_nonneg hK)
  have hinside :
      timeCutoffDerivConstant / (t₂ - t₁) + (2 * q / (1 - q)) * K ≤
        (timeCutoffDerivConstant * T +
          (2 * qbar / (1 - qbar)) * Kbar) * 16 ^ k := by
    calc
      _ ≤ (timeCutoffDerivConstant * T) * 16 ^ k +
          ((2 * qbar / (1 - qbar)) * Kbar) * 16 ^ k :=
        add_le_add htime_bound hgradient_bound
      _ = _ := by ring
  have houter :
      (t₁ - a + 1) * max 1 (q / (2 * (1 - q))) ≤
        (b - a + 1) * max 1 (qbar / (2 * (1 - qbar))) := by
    exact mul_le_mul (by linarith) hmax
      (zero_le_one.trans (le_max_left _ _)) (by linarith)
  have houter_bar_nonneg : 0 ≤
      (b - a + 1) * max 1 (qbar / (2 * (1 - qbar))) :=
    mul_nonneg (by linarith) (zero_le_one.trans (le_max_left _ _))
  unfold forwardMoserStepCoefficient forwardMoserStepCoefficientEnvelope
  calc
    (t₁ - a + 1) * max 1 (q / (2 * (1 - q))) *
          (timeCutoffDerivConstant / (t₂ - t₁) + (2 * q / (1 - q)) * K) + K ≤
        ((b - a + 1) * max 1 (qbar / (2 * (1 - qbar)))) *
          ((timeCutoffDerivConstant * T +
            (2 * qbar / (1 - qbar)) * Kbar) * 16 ^ k) +
          Kbar * 16 ^ k := by
      exact add_le_add
        (mul_le_mul houter hinside hinside_nonneg houter_bar_nonneg) hgradient
    _ = ((b - a + 1) * max 1 (qbar / (2 * (1 - qbar))) *
          (timeCutoffDerivConstant * T +
            (2 * qbar / (1 - qbar)) * Kbar) + Kbar) * 16 ^ k := by ring

def forwardMoserStepFactor
    (n : ℕ) (g : SmoothRiemannianMetric I M)
    (hdim : 2 < (Module.finrank ℝ E : ℝ))
    (rho : SmoothScalar g) (p₀ a τ b : ℝ) (k : ℕ) : ℝ :=
  localizedSobolevConstant (I := I) (M := M) g hdim ^
      (1 / parabolicMoserExponent n p₀ (k + 1)) *
    forwardMoserStepCoefficient
        (parabolicMoserExponent n p₀ k) a
        (moserUpperTimeLevel τ b (k + 1)) (moserUpperTimeLevel τ b k)
        (spatialMoserCutoffGradientConstant (I := I) g rho * 4 ^ (2 * k)) ^
      (1 / parabolicMoserExponent n p₀ k)

def nestedForwardMoserMoment
    (n : ℕ) {g : SmoothRiemannianMetric I M} (rho : SmoothScalar g)
    (u : ℝ → M → ℝ) (p₀ a : ℝ)
    (level upperTime : ℕ → ℝ) (k : ℕ) : ℝ :=
  localizedSpacetimeRpowMoment (I := I) (M := M)
    (spatialCutoffBetween rho (level (2 * k)) (level (2 * k + 1))) u
    (parabolicMoserExponent n p₀ k) a (upperTime k)

def nestedForwardMoserNorm
    (n : ℕ) {g : SmoothRiemannianMetric I M} (rho : SmoothScalar g)
    (u : ℝ → M → ℝ) (p₀ a : ℝ)
    (level upperTime : ℕ → ℝ) (k : ℕ) : ℝ :=
  nestedForwardMoserMoment (I := I) (M := M) n rho u p₀ a level upperTime k ^
    (1 / parabolicMoserExponent n p₀ k)

def nestedForwardMoserGradientCost
    (B : ℝ) (level : ℕ → ℝ) (k : ℕ) : ℝ :=
  CutoffProfile.derivBound ^ 2 * B /
    (level (2 * k + 2) - level (2 * k + 1)) ^ 2

def canonicalForwardMoserGradientCost
    (B lower upper : ℝ) : ℝ :=
  CutoffProfile.derivBound ^ 2 * B * (16 / (upper - lower) ^ 2)

def canonicalForwardMoserStepEnvelope
    (q a τ b B lower upper : ℝ) : ℝ :=
  max 1 (forwardMoserStepCoefficientEnvelope q a b (2 / (b - τ))
    (canonicalForwardMoserGradientCost B lower upper))

def canonicalForwardMoserIterationCost
    (n : ℕ) (g : SmoothRiemannianMetric I M)
    (hdim : 2 < (Module.finrank ℝ E : ℝ))
    (p₀ q a τ b B lower upper : ℝ) (k : ℕ) : ℝ :=
  moserIterationCost (parabolicMoserDecay n)
    ((parabolicMoserDecay n *
        Real.log (max 1 (localizedSobolevConstant (I := I) (M := M) g hdim)) +
      Real.log (canonicalForwardMoserStepEnvelope q a τ b B lower upper)) / p₀)
    (Real.log 16 / p₀) k

def canonicalForwardMoserLogCost
    (n : ℕ) (g : SmoothRiemannianMetric I M)
    (hdim : 2 < (Module.finrank ℝ E : ℝ))
    (q a τ b B lower upper : ℝ) : ℝ :=
  let theta := parabolicMoserDecay n
  let C := max 1 (localizedSobolevConstant (I := I) (M := M) g hdim)
  let A := canonicalForwardMoserStepEnvelope q a τ b B lower upper
  (theta * Real.log C + Real.log A) / (1 - theta) +
    Real.log 16 * (theta / (1 - theta) ^ 2)

def canonicalForwardMoserReverseCost
    (n : ℕ) (g : SmoothRiemannianMetric I M)
    (hdim : 2 < (Module.finrank ℝ E : ℝ))
    (q a τ b B lower upper : ℝ) : ℝ :=
  Real.exp (canonicalForwardMoserLogCost (I := I) (M := M)
    n g hdim q a τ b B lower upper / (1 - parabolicMoserDecay n))

theorem canonicalForwardMoserLogCost_nonneg
    (n : ℕ) [NeZero n] (g : SmoothRiemannianMetric I M)
    (hdim : 2 < (Module.finrank ℝ E : ℝ))
    (q a τ b B lower upper : ℝ) :
    0 ≤ canonicalForwardMoserLogCost (I := I) (M := M)
      n g hdim q a τ b B lower upper := by
  have htheta : 0 ≤ parabolicMoserDecay n := (parabolicMoserDecay_pos n).le
  have hdenom : 0 ≤ 1 - parabolicMoserDecay n :=
    sub_nonneg.mpr (parabolicMoserDecay_lt_one n).le
  have hC : 1 ≤ max 1 (localizedSobolevConstant (I := I) (M := M) g hdim) :=
    le_max_left _ _
  have hA : 1 ≤ canonicalForwardMoserStepEnvelope q a τ b B lower upper :=
    le_max_left _ _
  unfold canonicalForwardMoserLogCost
  dsimp only
  exact add_nonneg
    (div_nonneg
      (add_nonneg (mul_nonneg htheta (Real.log_nonneg hC)) (Real.log_nonneg hA))
      hdenom)
    (mul_nonneg (Real.log_nonneg (by norm_num))
      (div_nonneg htheta (sq_nonneg _)))

theorem canonicalForwardMoserIterationCost_nonneg
    (n : ℕ) [NeZero n] (g : SmoothRiemannianMetric I M)
    (hdim : 2 < (Module.finrank ℝ E : ℝ))
    {p₀ : ℝ} (hp₀ : 0 < p₀) (q a τ b B lower upper : ℝ) (k : ℕ) :
    0 ≤ canonicalForwardMoserIterationCost (I := I) (M := M)
      n g hdim p₀ q a τ b B lower upper k := by
  have hC : 1 ≤ max 1 (localizedSobolevConstant (I := I) (M := M) g hdim) :=
    le_max_left _ _
  have hA : 1 ≤ canonicalForwardMoserStepEnvelope q a τ b B lower upper :=
    le_max_left _ _
  unfold canonicalForwardMoserIterationCost
  exact moserIterationCost_nonneg (parabolicMoserDecay_pos n).le
    (div_nonneg
      (add_nonneg
        (mul_nonneg (parabolicMoserDecay_pos n).le (Real.log_nonneg hC))
        (Real.log_nonneg hA)) hp₀.le)
    (div_nonneg (Real.log_nonneg (by norm_num)) hp₀.le) k

theorem one_le_canonicalForwardMoserReverseCost
    (n : ℕ) [NeZero n] (g : SmoothRiemannianMetric I M)
    (hdim : 2 < (Module.finrank ℝ E : ℝ))
    (q a τ b B lower upper : ℝ) :
    1 ≤ canonicalForwardMoserReverseCost (I := I) (M := M)
      n g hdim q a τ b B lower upper := by
  unfold canonicalForwardMoserReverseCost
  calc
    1 = Real.exp 0 := Real.exp_zero.symm
    _ ≤ Real.exp (canonicalForwardMoserLogCost (I := I) (M := M)
        n g hdim q a τ b B lower upper / (1 - parabolicMoserDecay n)) :=
      Real.exp_le_exp.mpr (div_nonneg
        (canonicalForwardMoserLogCost_nonneg n g hdim q a τ b B lower upper)
        (sub_nonneg.mpr (parabolicMoserDecay_lt_one n).le))

theorem tsum_canonicalForwardMoserIterationCost
    (n : ℕ) [NeZero n] (g : SmoothRiemannianMetric I M)
    (hdim : 2 < (Module.finrank ℝ E : ℝ))
    {p₀ : ℝ} (hp₀ : 0 < p₀) (q a τ b B lower upper : ℝ) :
    ∑' k, canonicalForwardMoserIterationCost (I := I) (M := M)
        n g hdim p₀ q a τ b B lower upper k =
      canonicalForwardMoserLogCost (I := I) (M := M)
        n g hdim q a τ b B lower upper / p₀ := by
  unfold canonicalForwardMoserIterationCost canonicalForwardMoserLogCost
  dsimp only
  rw [tsum_moserIterationCost (parabolicMoserDecay_pos n).le
    (parabolicMoserDecay_lt_one n)]
  field_simp [hp₀.ne']

theorem nestedForwardMoserGradientCost_canonical
    {B lower upper : ℝ} (hlowerUpper : lower < upper) (k : ℕ) :
    nestedForwardMoserGradientCost B
        (moserCutoffLevelBetween lower upper) k =
      canonicalForwardMoserGradientCost B lower upper * 16 ^ k := by
  unfold nestedForwardMoserGradientCost canonicalForwardMoserGradientCost
  rw [div_eq_mul_inv,
    moserCutoffLevelBetween_even_succ_inv_sq hlowerUpper]
  ring

theorem forwardMoserStepCoefficient_canonical_le_mul_pow
    {q qbar a τ b B lower upper : ℝ} (k : ℕ)
    (hq : 0 ≤ q) (hqqbar : q ≤ qbar) (hqbar_one : qbar < 1)
    (haτ : a ≤ τ) (hτb : τ < b) (hB : 0 ≤ B)
    (hlowerUpper : lower < upper) :
    forwardMoserStepCoefficient q a
        (moserUpperTimeLevel τ b (k + 1)) (moserUpperTimeLevel τ b k)
        (nestedForwardMoserGradientCost B
          (moserCutoffLevelBetween lower upper) k) ≤
      canonicalForwardMoserStepEnvelope qbar a τ b B lower upper * 16 ^ k := by
  have hK : 0 ≤ nestedForwardMoserGradientCost B
      (moserCutoffLevelBetween lower upper) k := by
    exact div_nonneg (mul_nonneg (sq_nonneg _) hB) (sq_nonneg _)
  have henvelope := forwardMoserStepCoefficient_le_envelope_mul_pow k
    hq hqqbar hqbar_one
    (haτ.trans (moserUpperTimeLevel_lt hτb (k + 1)).le)
    (moserUpperTimeLevel_le hτb (k + 1))
    (moserUpperTimeLevel_succ_lt hτb k) hK
    (moserUpperTimeLevel_sub_succ_inv_le_mul_pow hτb k)
    (le_of_eq (nestedForwardMoserGradientCost_canonical hlowerUpper k))
  calc
    _ ≤ forwardMoserStepCoefficientEnvelope qbar a b (2 / (b - τ))
          (canonicalForwardMoserGradientCost B lower upper) * 16 ^ k := henvelope
    _ ≤ canonicalForwardMoserStepEnvelope qbar a τ b B lower upper * 16 ^ k := by
      exact mul_le_mul_of_nonneg_right (le_max_right _ _)
        (pow_nonneg (by norm_num) k)

def nestedForwardMoserStepFactor
    (n : ℕ) (g : SmoothRiemannianMetric I M)
    (hdim : 2 < (Module.finrank ℝ E : ℝ))
    (B p₀ a : ℝ) (level upperTime : ℕ → ℝ) (k : ℕ) : ℝ :=
  localizedSobolevConstant (I := I) (M := M) g hdim ^
      (1 / parabolicMoserExponent n p₀ (k + 1)) *
    forwardMoserStepCoefficient
        (parabolicMoserExponent n p₀ k) a
        (upperTime (k + 1)) (upperTime k)
        (nestedForwardMoserGradientCost B level k) ^
      (1 / parabolicMoserExponent n p₀ k)

omit [I.Boundaryless] in
theorem localizedSpacetimeRpowMoment_gain_le
    (n : ℕ) [NeZero n]
    {g : SmoothRiemannianMetric I M} (rho : SmoothScalar g)
    (u : ℝ → M → ℝ)
    (hu : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun z : ℝ × M => u z.1 z.2))
    (hpos : ∀ t x, 0 < u t x)
    {q a b level₁ level₂ level₃ : ℝ}
    (hab : a ≤ b) (hlevel₁₂ : level₁ < level₂)
    (hlevel₂₃ : level₂ < level₃) :
    localizedSpacetimeRpowMoment (I := I) (M := M)
        (spatialCutoffBetween rho level₂ level₃) u
        (parabolicMoserGain n * q) a b ≤
      ∫ t in a..b, ∫ x,
        |(spatialCutoffBetween rho level₁ level₂).toFun x *
            u t x ^ (q / 2)| ^ (2 + 4 / (n : ℝ))
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
  let μ := riemannianVolumeMeasure (I := I) (M := M) g
  let inner := spatialCutoffBetween rho level₂ level₃
  let middle := spatialCutoffBetween rho level₁ level₂
  let p := parabolicMoserGain n * q
  let critical := 2 + 4 / (n : ℝ)
  let left : ℝ → ℝ := fun t =>
    ∫ x, inner.toFun x ^ 2 * u t x ^ p ∂μ
  let right : ℝ → ℝ := fun t =>
    ∫ x, |middle.toFun x * u t x ^ (q / 2)| ^ critical ∂μ
  letI : IsFiniteMeasure μ := by
    dsimp only [μ]
    exact riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace
      (I := I) (M := M) g
  have hn : 0 < (n : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
  have hcritical : 0 ≤ critical := by
    dsimp only [critical]
    positivity
  have hleft_joint : Continuous (fun z : ℝ × M =>
      inner.toFun z.2 ^ 2 * u z.1 z.2 ^ p) :=
    (inner.smooth.continuous.comp continuous_snd).pow 2 |>.mul
      (hu.continuous.rpow_const fun z => Or.inl (hpos z.1 z.2).ne')
  have hright_base : Continuous (fun z : ℝ × M =>
      |middle.toFun z.2 * u z.1 z.2 ^ (q / 2)|) :=
    (((middle.smooth.continuous.comp continuous_snd).mul
      (hu.continuous.rpow_const fun z => Or.inl (hpos z.1 z.2).ne'))).abs
  have hright_joint : Continuous (fun z : ℝ × M =>
      |middle.toFun z.2 * u z.1 z.2 ^ (q / 2)| ^ critical) :=
    hright_base.rpow_const fun _ => Or.inr hcritical
  have hleft_cont : ContinuousOn left (Icc a b) := by
    have h := DifferentialGeometry.Integral.Measure.integral_contOn_cpt
      (K := Icc a b) μ
      (fun t x => inner.toFun x ^ 2 * u t x ^ p)
      isCompact_Icc hleft_joint.continuousOn
    simpa only [left] using h
  have hright_cont : ContinuousOn right (Icc a b) := by
    have h := DifferentialGeometry.Integral.Measure.integral_contOn_cpt
      (K := Icc a b) μ
      (fun t x => |middle.toFun x * u t x ^ (q / 2)| ^ critical)
      isCompact_Icc hright_joint.continuousOn
    simpa only [right] using h
  have hleft_int : IntervalIntegrable left volume a b := by
    apply ContinuousOn.intervalIntegrable
    simpa [uIcc_of_le hab] using hleft_cont
  have hright_int : IntervalIntegrable right volume a b := by
    apply ContinuousOn.intervalIntegrable
    simpa [uIcc_of_le hab] using hright_cont
  have hpoint : ∀ t ∈ Icc a b, left t ≤ right t := by
    intro t _
    have hu_slice : Continuous (u t) :=
      hu.continuous.comp (continuous_const.prodMk continuous_id)
    have hleft_slice : Continuous (fun x : M =>
        inner.toFun x ^ 2 * u t x ^ p) :=
      (inner.smooth.continuous.pow 2).mul
        (hu_slice.rpow_const fun x => Or.inl (hpos t x).ne')
    have hright_slice : Continuous (fun x : M =>
        |middle.toFun x * u t x ^ (q / 2)| ^ critical) :=
      (((middle.smooth.continuous.mul
        (hu_slice.rpow_const fun x => Or.inl (hpos t x).ne')).abs).rpow_const
          fun _ => Or.inr hcritical)
    apply integral_mono
      (hleft_slice.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
      (hright_slice.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
    intro x
    have hcutoff := spatialCutoffBetween_sq_le_rpow rho
      hlevel₁₂ hlevel₂₃ critical x
    have hu_pow : 0 ≤ u t x ^ p := Real.rpow_nonneg (hpos t x).le p
    have hidentity := abs_mul_rpow_half_parabolic_gain n
      (spatialCutoffBetween_mem_Icc rho level₁ level₂ x).1 (hpos t x)
      (q := q)
    change inner.toFun x ^ 2 * u t x ^ p ≤
      |middle.toFun x * u t x ^ (q / 2)| ^ critical
    calc
      _ ≤ middle.toFun x ^ critical * u t x ^ p :=
        mul_le_mul_of_nonneg_right (by
          simpa only [inner, middle] using hcutoff) hu_pow
      _ = _ := by
        simpa only [p, critical, middle] using hidentity.symm
  rw [localizedSpacetimeRpowMoment_eq_intervalIntegral_of_continuous_pos
    (I := I) (M := M) inner u hu.continuous hpos hab]
  exact intervalIntegral.integral_mono_on hab hleft_int hright_int hpoint

theorem localizedSpacetimeRpowMoment_gain_le_of_supersolution
    (g : SmoothRiemannianMetric I M)
    (hdim : 2 < (Module.finrank ℝ E : ℝ))
    (rho : SmoothScalar g)
    (u : ℝ → M → ℝ)
    (hu : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun z : ℝ × M => u z.1 z.2))
    (hpos : ∀ t x, 0 < u t x)
    {q a innerTime outerTime level₀ level₁ level₂ level₃ B : ℝ}
    (hq_pos : 0 < q) (hq_one : q < 1)
    (haInner : a ≤ innerTime) (hinnerOuter : innerTime < outerTime)
    (hlevel₀₁ : level₀ < level₁) (hlevel₁₂ : level₁ < level₂)
    (hlevel₂₃ : level₂ < level₃) (hB : 0 ≤ B)
    (hrho : ∀ x : M,
      g.inner x
          (gradFun (I := I) g rho.toFun x)
          (gradFun (I := I) g rho.toFun x) ≤ B)
    (hpde : ∀ t ∈ Icc a outerTime, ∀ x : M,
      Δ_g (I := I) g (smoothScalarSlice (I := I) g u hu t).toContMDiffMap x ≤
        deriv (fun s => u s x) t) :
    let n := Module.finrank ℝ E
    let K := CutoffProfile.derivBound ^ 2 * B / (level₂ - level₁) ^ 2
    localizedSpacetimeRpowMoment (I := I) (M := M)
        (spatialCutoffBetween rho level₂ level₃) u
        (parabolicMoserGain n * q) a innerTime ≤
      localizedSobolevConstant (I := I) (M := M) g hdim *
        (forwardMoserStepCoefficient q a innerTime outerTime K *
          localizedSpacetimeRpowMoment (I := I) (M := M)
            (spatialCutoffBetween rho level₀ level₁) u q a outerTime) ^
          parabolicMoserGain n := by
  let n := Module.finrank ℝ E
  letI : NeZero n := by
    refine ⟨Nat.ne_of_gt ?_⟩
    exact_mod_cast (by linarith : 0 < (n : ℝ))
  let outer := spatialCutoffBetween rho level₀ level₁
  let middle := spatialCutoffBetween rho level₁ level₂
  let inner := spatialCutoffBetween rho level₂ level₃
  let K := CutoffProfile.derivBound ^ 2 * B / (level₂ - level₁) ^ 2
  let L := localizedSpacetimeRpowMoment (I := I) (M := M)
    outer u q a outerTime
  have haOuter : a ≤ outerTime := haInner.trans hinnerOuter.le
  have hK : 0 ≤ K := by
    exact div_nonneg (mul_nonneg (sq_nonneg _) hB) (sq_nonneg _)
  have hL : 0 ≤ L := by
    exact localizedSpacetimeRpowMoment_nonneg (I := I) (M := M)
      outer u (fun t x => (hpos t x).le) q a outerTime
  have houterMass :
      (∫ t in a..outerTime,
        localizedL2Mass (I := I) (M := M) outer
          (smoothScalarSlice (I := I) g (fun s x => u s x ^ (q / 2))
            (contMDiff_rpow_of_pos hu hpos (q / 2)) t)) = L := by
    dsimp only [L]
    rw [localizedSpacetimeRpowMoment_eq_intervalIntegral_of_continuous_pos
      (I := I) (M := M) outer u hu.continuous hpos haOuter]
    apply intervalIntegral.integral_congr
    intro t _
    simpa only [outer] using localizedL2Mass_rpow_half
      (I := I) (M := M) g
        (spatialCutoffBetween rho level₀ level₁) u hu hpos q t
  have hreverse := positive_rpow_reverse_holder_step
    (I := I) (M := M) g hdim middle outer u hu hpos
      hq_pos hq_one haInner hinnerOuter hK hL hpde
      (fun x => by
        simpa only [middle, outer] using
          spatialCutoffBetween_sq_le rho hlevel₀₁ hlevel₁₂ x)
      (fun x => by
        simpa only [middle, outer, K] using
          spatialCutoffBetween_gradient_le (I := I) g rho
            hlevel₀₁ hlevel₁₂ hB hrho x)
      houterMass.le
  have hbridge := localizedSpacetimeRpowMoment_gain_le n rho u hu hpos
    haInner hlevel₁₂ hlevel₂₃ (q := q)
  change localizedSpacetimeRpowMoment (I := I) (M := M) inner u
      (parabolicMoserGain n * q) a innerTime ≤
    localizedSobolevConstant (I := I) (M := M) g hdim *
      (forwardMoserStepCoefficient q a innerTime outerTime K * L) ^
        parabolicMoserGain n
  calc
    localizedSpacetimeRpowMoment (I := I) (M := M) inner u
          (parabolicMoserGain n * q) a innerTime ≤
        ∫ t in a..innerTime, ∫ x,
          |middle.toFun x * u t x ^ (q / 2)| ^ (2 + 4 / (n : ℝ))
          ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
      simpa only [inner, middle] using hbridge
    _ ≤ localizedSobolevConstant (I := I) (M := M) g hdim *
        (((innerTime - a + 1) *
            positiveRpowCommonEnergyBound q innerTime outerTime K L + K * L) ^
          parabolicMoserGain n) := by
      simpa only [n, parabolicMoserGain] using hreverse
    _ = localizedSobolevConstant (I := I) (M := M) g hdim *
        (forwardMoserStepCoefficient q a innerTime outerTime K * L) ^
          parabolicMoserGain n := by
      congr 2
      unfold forwardMoserStepCoefficient positiveRpowCommonEnergyBound
        positiveRpowEnergyBound
      ring

theorem forwardMoserStepCoefficient_nonneg
    {q a t₁ t₂ K : ℝ}
    (hq_pos : 0 < q) (hq_one : q < 1)
    (hat₁ : a ≤ t₁) (ht₁t₂ : t₁ < t₂) (hK : 0 ≤ K) :
    0 ≤ forwardMoserStepCoefficient q a t₁ t₂ K := by
  have hdenom : 0 ≤ 1 - q := sub_nonneg.mpr hq_one.le
  have htime : 0 ≤ timeCutoffDerivConstant / (t₂ - t₁) :=
    div_nonneg timeCutoffDerivConstant_nonneg (sub_nonneg.mpr ht₁t₂.le)
  have hpower : 0 ≤ 2 * q / (1 - q) :=
    div_nonneg (mul_nonneg (by norm_num) hq_pos.le) hdenom
  have hmax : 0 ≤ max 1 (q / (2 * (1 - q))) :=
    zero_le_one.trans (le_max_left _ _)
  exact add_nonneg
    (mul_nonneg
      (mul_nonneg (by linarith : 0 ≤ t₁ - a + 1) hmax)
      (add_nonneg htime (mul_nonneg hpower hK))) hK

theorem nestedForwardMoserNorm_succ_le_of_supersolution
    (g : SmoothRiemannianMetric I M)
    (hdim : 2 < (Module.finrank ℝ E : ℝ))
    (rho : SmoothScalar g)
    (u : ℝ → M → ℝ)
    (hu : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun z : ℝ × M => u z.1 z.2))
    (hpos : ∀ t x, 0 < u t x)
    {p₀ a B : ℝ} (level upperTime : ℕ → ℝ) (k : ℕ)
    (hp₀ : 0 < p₀)
    (hexponent_one :
      parabolicMoserExponent (Module.finrank ℝ E) p₀ k < 1)
    (haTime : a ≤ upperTime (k + 1))
    (htime : upperTime (k + 1) < upperTime k)
    (hlevel₀₁ : level (2 * k) < level (2 * k + 1))
    (hlevel₁₂ : level (2 * k + 1) < level (2 * k + 2))
    (hlevel₂₃ : level (2 * k + 2) < level (2 * k + 3))
    (hB : 0 ≤ B)
    (hrho : ∀ x : M,
      g.inner x
          (gradFun (I := I) g rho.toFun x)
          (gradFun (I := I) g rho.toFun x) ≤ B)
    (hpde : ∀ t ∈ Icc a (upperTime k), ∀ x : M,
      Δ_g (I := I) g (smoothScalarSlice (I := I) g u hu t).toContMDiffMap x ≤
        deriv (fun s => u s x) t) :
    nestedForwardMoserNorm (I := I) (M := M) (Module.finrank ℝ E)
        rho u p₀ a level upperTime (k + 1) ≤
      nestedForwardMoserStepFactor (I := I) (M := M)
          (Module.finrank ℝ E) g hdim B p₀ a level upperTime k *
        nestedForwardMoserNorm (I := I) (M := M) (Module.finrank ℝ E)
          rho u p₀ a level upperTime k := by
  let n := Module.finrank ℝ E
  letI : NeZero n := by
    refine ⟨Nat.ne_of_gt ?_⟩
    exact_mod_cast (by linarith : 0 < (n : ℝ))
  let q := parabolicMoserExponent n p₀ k
  let K := nestedForwardMoserGradientCost B level k
  let coefficient := forwardMoserStepCoefficient q a
    (upperTime (k + 1)) (upperTime k) K
  let L := nestedForwardMoserMoment (I := I) (M := M)
    n rho u p₀ a level upperTime k
  let L' := nestedForwardMoserMoment (I := I) (M := M)
    n rho u p₀ a level upperTime (k + 1)
  have hq_pos : 0 < q := parabolicMoserExponent_pos n hp₀ k
  have hK : 0 ≤ K := by
    dsimp only [K, nestedForwardMoserGradientCost]
    exact div_nonneg (mul_nonneg (sq_nonneg _) hB) (sq_nonneg _)
  have hcoefficient : 0 ≤ coefficient :=
    forwardMoserStepCoefficient_nonneg hq_pos
      (by simpa only [q, n] using hexponent_one) haTime htime hK
  have hL : 0 ≤ L := by
    exact localizedSpacetimeRpowMoment_nonneg (I := I) (M := M)
      (spatialCutoffBetween rho (level (2 * k)) (level (2 * k + 1)))
      u (fun t x => (hpos t x).le) (parabolicMoserExponent n p₀ k)
      a (upperTime k)
  have hL' : 0 ≤ L' := by
    exact localizedSpacetimeRpowMoment_nonneg (I := I) (M := M)
      (spatialCutoffBetween rho (level (2 * (k + 1)))
        (level (2 * (k + 1) + 1)))
      u (fun t x => (hpos t x).le) (parabolicMoserExponent n p₀ (k + 1))
      a (upperTime (k + 1))
  have hstep₀ := localizedSpacetimeRpowMoment_gain_le_of_supersolution
    (I := I) (M := M) g hdim rho u hu hpos hq_pos
      (by simpa only [q, n] using hexponent_one) haTime htime
      hlevel₀₁ hlevel₁₂ hlevel₂₃ hB hrho hpde
  have hstep : L' ≤
      localizedSobolevConstant (I := I) (M := M) g hdim *
        (coefficient * L) ^ parabolicMoserGain n := by
    simpa only [L, L', coefficient, K, q, nestedForwardMoserMoment,
      parabolicMoserExponent_succ, Nat.mul_add, Nat.mul_one, Nat.add_assoc,
      n] using hstep₀
  have hnormalized := normalized_exponent_gain_step
    hL hL' (localizedSobolevConstant_nonneg (I := I) (M := M) g hdim)
      hcoefficient (parabolicMoserGain_pos n) hq_pos hstep
  simpa only [nestedForwardMoserNorm, nestedForwardMoserStepFactor,
    L, L', coefficient, K, q, parabolicMoserExponent_succ, n, mul_assoc] using
      hnormalized

theorem nestedForwardMoserNorm_succ_le_exp_of_supersolution
    (g : SmoothRiemannianMetric I M)
    (hdim : 2 < (Module.finrank ℝ E : ℝ))
    (rho : SmoothScalar g)
    (u : ℝ → M → ℝ)
    (hu : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun z : ℝ × M => u z.1 z.2))
    (hpos : ∀ t x, 0 < u t x)
    {p₀ qbar a τ b B lower upper : ℝ} (k : ℕ)
    (hp₀ : 0 < p₀)
    (hexponent_le :
      parabolicMoserExponent (Module.finrank ℝ E) p₀ k ≤ qbar)
    (hqbar_one : qbar < 1)
    (haτ : a ≤ τ) (hτb : τ < b)
    (hB : 0 ≤ B) (hlowerUpper : lower < upper)
    (hrho : ∀ x : M,
      g.inner x
          (gradFun (I := I) g rho.toFun x)
          (gradFun (I := I) g rho.toFun x) ≤ B)
    (hpde : ∀ t ∈ Icc a b, ∀ x : M,
      Δ_g (I := I) g (smoothScalarSlice (I := I) g u hu t).toContMDiffMap x ≤
        deriv (fun s => u s x) t) :
    nestedForwardMoserNorm (I := I) (M := M) (Module.finrank ℝ E)
        rho u p₀ a (moserCutoffLevelBetween lower upper)
          (moserUpperTimeLevel τ b) (k + 1) ≤
      Real.exp
          (canonicalForwardMoserIterationCost (I := I) (M := M)
            (Module.finrank ℝ E) g hdim p₀ qbar a τ b B lower upper k) *
        nestedForwardMoserNorm (I := I) (M := M) (Module.finrank ℝ E)
          rho u p₀ a (moserCutoffLevelBetween lower upper)
            (moserUpperTimeLevel τ b) k := by
  let n := Module.finrank ℝ E
  letI : NeZero n := by
    refine ⟨Nat.ne_of_gt ?_⟩
    exact_mod_cast (by linarith : 0 < (n : ℝ))
  let level := moserCutoffLevelBetween lower upper
  let upperTime := moserUpperTimeLevel τ b
  let q := parabolicMoserExponent n p₀ k
  let K := nestedForwardMoserGradientCost B level k
  let coefficient := forwardMoserStepCoefficient q a
    (upperTime (k + 1)) (upperTime k) K
  let L := nestedForwardMoserMoment (I := I) (M := M)
    n rho u p₀ a level upperTime k
  let L' := nestedForwardMoserMoment (I := I) (M := M)
    n rho u p₀ a level upperTime (k + 1)
  let C := max 1 (localizedSobolevConstant (I := I) (M := M) g hdim)
  let A := canonicalForwardMoserStepEnvelope qbar a τ b B lower upper
  have hq_pos : 0 < q := parabolicMoserExponent_pos n hp₀ k
  have hq_one : q < 1 := hexponent_le.trans_lt hqbar_one
  have hlevel := moserCutoffLevelBetween_strictMono hlowerUpper
  have haTime : a ≤ upperTime (k + 1) :=
    haτ.trans (moserUpperTimeLevel_lt hτb (k + 1)).le
  have htime : upperTime (k + 1) < upperTime k :=
    moserUpperTimeLevel_succ_lt hτb k
  have hK : 0 ≤ K := by
    dsimp only [K, nestedForwardMoserGradientCost]
    exact div_nonneg (mul_nonneg (sq_nonneg _) hB) (sq_nonneg _)
  have hcoefficient : 0 ≤ coefficient :=
    forwardMoserStepCoefficient_nonneg hq_pos hq_one haTime htime hK
  have hcoefficient_bound : coefficient ≤ A * 16 ^ k := by
    simpa only [coefficient, K, A, level, upperTime, q, n] using
      (forwardMoserStepCoefficient_canonical_le_mul_pow k hq_pos.le
        hexponent_le hqbar_one haτ hτb hB hlowerUpper)
  have hL : 0 ≤ L := by
    exact localizedSpacetimeRpowMoment_nonneg (I := I) (M := M)
      (spatialCutoffBetween rho (level (2 * k)) (level (2 * k + 1)))
      u (fun t x => (hpos t x).le) q a (upperTime k)
  have hL' : 0 ≤ L' := by
    exact localizedSpacetimeRpowMoment_nonneg (I := I) (M := M)
      (spatialCutoffBetween rho (level (2 * (k + 1)))
        (level (2 * (k + 1) + 1)))
      u (fun t x => (hpos t x).le) (parabolicMoserExponent n p₀ (k + 1))
      a (upperTime (k + 1))
  have hstep₀ := localizedSpacetimeRpowMoment_gain_le_of_supersolution
    (I := I) (M := M) g hdim rho u hu hpos hq_pos hq_one
      haTime htime
      (hlevel (Nat.lt_succ_self (2 * k)))
      (hlevel (Nat.lt_succ_self (2 * k + 1)))
      (hlevel (Nat.lt_succ_self (2 * k + 2)))
      hB hrho
      (fun t ht x => hpde t
        ⟨ht.1, ht.2.trans (moserUpperTimeLevel_le hτb k)⟩ x)
  have hstep : L' ≤
      localizedSobolevConstant (I := I) (M := M) g hdim *
        (coefficient * L) ^ parabolicMoserGain n := by
    simpa only [L, L', coefficient, K, q, level, upperTime,
      nestedForwardMoserMoment, parabolicMoserExponent_succ,
      Nat.mul_add, Nat.mul_one, Nat.add_assoc, n] using hstep₀
  have hstep_envelope : L' ≤ C * ((A * 16 ^ k) * L) ^ parabolicMoserGain n := by
    calc
      L' ≤ localizedSobolevConstant (I := I) (M := M) g hdim *
          (coefficient * L) ^ parabolicMoserGain n := hstep
      _ ≤ C * ((A * 16 ^ k) * L) ^ parabolicMoserGain n := by
        exact mul_le_mul (le_max_right _ _)
          (Real.rpow_le_rpow (mul_nonneg hcoefficient hL)
            (mul_le_mul_of_nonneg_right hcoefficient_bound hL)
            (parabolicMoserGain_pos n).le)
          (Real.rpow_nonneg (mul_nonneg hcoefficient hL) _)
          (zero_le_one.trans (le_max_left _ _))
  have hnormalized := normalized_moser_step n hp₀
    (show 1 ≤ C from le_max_left _ _)
    (show 1 ≤ A from le_max_left _ _)
    hL hL' k hstep_envelope
  simpa only [nestedForwardMoserNorm, L, L', C, A, level, upperTime,
    canonicalForwardMoserIterationCost, n] using hnormalized

theorem nestedForwardMoserNorm_le_exp_finset_of_supersolution
    (g : SmoothRiemannianMetric I M)
    (hdim : 2 < (Module.finrank ℝ E : ℝ))
    (rho : SmoothScalar g)
    (u : ℝ → M → ℝ)
    (hu : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun z : ℝ × M => u z.1 z.2))
    (hpos : ∀ t x, 0 < u t x)
    {p₀ qbar a τ b B lower upper : ℝ} (m : ℕ)
    (hp₀ : 0 < p₀) (hqbar_one : qbar < 1)
    (haτ : a ≤ τ) (hτb : τ < b)
    (hB : 0 ≤ B) (hlowerUpper : lower < upper)
    (hrho : ∀ x : M,
      g.inner x
          (gradFun (I := I) g rho.toFun x)
          (gradFun (I := I) g rho.toFun x) ≤ B)
    (hpde : ∀ t ∈ Icc a b, ∀ x : M,
      Δ_g (I := I) g (smoothScalarSlice (I := I) g u hu t).toContMDiffMap x ≤
        deriv (fun s => u s x) t)
    (hexponents : ∀ k < m,
      parabolicMoserExponent (Module.finrank ℝ E) p₀ k ≤ qbar) :
    nestedForwardMoserNorm (I := I) (M := M) (Module.finrank ℝ E)
        rho u p₀ a (moserCutoffLevelBetween lower upper)
          (moserUpperTimeLevel τ b) m ≤
      Real.exp
          (∑ k ∈ Finset.range m,
            canonicalForwardMoserIterationCost (I := I) (M := M)
              (Module.finrank ℝ E) g hdim p₀ qbar a τ b B lower upper k) *
        nestedForwardMoserNorm (I := I) (M := M) (Module.finrank ℝ E)
          rho u p₀ a (moserCutoffLevelBetween lower upper)
            (moserUpperTimeLevel τ b) 0 := by
  let n := Module.finrank ℝ E
  letI : NeZero n := by
    refine ⟨Nat.ne_of_gt ?_⟩
    exact_mod_cast (by linarith : 0 < (n : ℝ))
  let level := moserCutoffLevelBetween lower upper
  let upperTime := moserUpperTimeLevel τ b
  let X : ℕ → ℝ := fun k =>
    nestedForwardMoserNorm (I := I) (M := M)
      n rho u p₀ a level upperTime k
  let cost : ℕ → ℝ := fun k =>
    canonicalForwardMoserIterationCost (I := I) (M := M)
      n g hdim p₀ qbar a τ b B lower upper k
  have hstep : ∀ k < m, X (k + 1) ≤ Real.exp (cost k) * X k := by
    intro k hk
    simpa only [X, cost, level, upperTime, n] using
      (nestedForwardMoserNorm_succ_le_exp_of_supersolution
        (I := I) (M := M) g hdim rho u hu hpos k hp₀
          (by simpa only [n] using hexponents k hk) hqbar_one
          haτ hτb hB hlowerUpper hrho hpde)
  have hfinite := finite_multiplicative_iteration m
    (fun _ _ => (Real.exp_pos _).le) hstep
  calc
    X m ≤ (∏ k ∈ Finset.range m, Real.exp (cost k)) * X 0 := hfinite
    _ = Real.exp (∑ k ∈ Finset.range m, cost k) * X 0 := by
      rw [Real.exp_sum]
    _ = _ := by rfl

theorem nestedForwardMoserNorm_le_exp_of_supersolution
    (g : SmoothRiemannianMetric I M)
    (hdim : 2 < (Module.finrank ℝ E : ℝ))
    (rho : SmoothScalar g)
    (u : ℝ → M → ℝ)
    (hu : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun z : ℝ × M => u z.1 z.2))
    (hpos : ∀ t x, 0 < u t x)
    {p₀ qbar a τ b B lower upper : ℝ} (m : ℕ)
    (hp₀ : 0 < p₀) (hqbar_one : qbar < 1)
    (haτ : a ≤ τ) (hτb : τ < b)
    (hB : 0 ≤ B) (hlowerUpper : lower < upper)
    (hrho : ∀ x : M,
      g.inner x
          (gradFun (I := I) g rho.toFun x)
          (gradFun (I := I) g rho.toFun x) ≤ B)
    (hpde : ∀ t ∈ Icc a b, ∀ x : M,
      Δ_g (I := I) g (smoothScalarSlice (I := I) g u hu t).toContMDiffMap x ≤
        deriv (fun s => u s x) t)
    (hexponents : ∀ k < m,
      parabolicMoserExponent (Module.finrank ℝ E) p₀ k ≤ qbar) :
    nestedForwardMoserNorm (I := I) (M := M) (Module.finrank ℝ E)
        rho u p₀ a (moserCutoffLevelBetween lower upper)
          (moserUpperTimeLevel τ b) m ≤
      Real.exp
          (∑' k, canonicalForwardMoserIterationCost (I := I) (M := M)
            (Module.finrank ℝ E) g hdim p₀ qbar a τ b B lower upper k) *
        nestedForwardMoserNorm (I := I) (M := M) (Module.finrank ℝ E)
          rho u p₀ a (moserCutoffLevelBetween lower upper)
            (moserUpperTimeLevel τ b) 0 := by
  let n := Module.finrank ℝ E
  letI : NeZero n := by
    refine ⟨Nat.ne_of_gt ?_⟩
    exact_mod_cast (by linarith : 0 < (n : ℝ))
  let level := moserCutoffLevelBetween lower upper
  let upperTime := moserUpperTimeLevel τ b
  let X : ℕ → ℝ := fun k =>
    nestedForwardMoserNorm (I := I) (M := M)
      n rho u p₀ a level upperTime k
  let C := max 1 (localizedSobolevConstant (I := I) (M := M) g hdim)
  let A := canonicalForwardMoserStepEnvelope qbar a τ b B lower upper
  let theta := parabolicMoserDecay n
  let c₀ := (theta * Real.log C + Real.log A) / p₀
  let c₁ := Real.log 16 / p₀
  have hC : 1 ≤ C := le_max_left _ _
  have hA : 1 ≤ A := le_max_left _ _
  have hc₀ : 0 ≤ c₀ := by
    exact div_nonneg
      (add_nonneg
        (mul_nonneg (parabolicMoserDecay_pos n).le (Real.log_nonneg hC))
        (Real.log_nonneg hA)) hp₀.le
  have hc₁ : 0 ≤ c₁ :=
    div_nonneg (Real.log_nonneg (by norm_num)) hp₀.le
  have hX_zero : 0 ≤ X 0 := by
    unfold X nestedForwardMoserNorm
    exact Real.rpow_nonneg
      (localizedSpacetimeRpowMoment_nonneg (I := I) (M := M)
        (spatialCutoffBetween rho (level 0) (level 1)) u
        (fun t x => (hpos t x).le) (parabolicMoserExponent n p₀ 0)
        a (upperTime 0)) _
  have hstep : ∀ k < m,
      X (k + 1) ≤ Real.exp (moserIterationCost theta c₀ c₁ k) * X k := by
    intro k hk
    have h := nestedForwardMoserNorm_succ_le_exp_of_supersolution
      (I := I) (M := M) g hdim rho u hu hpos k hp₀
        (by simpa only [n] using hexponents k hk) hqbar_one
        haτ hτb hB hlowerUpper hrho hpde
    simpa only [X, level, upperTime, theta, c₀, c₁, C, A,
      canonicalForwardMoserIterationCost, n] using h
  have hbound := finite_moser_iteration_bound m hX_zero
    (parabolicMoserDecay_pos n).le (parabolicMoserDecay_lt_one n)
    hc₀ hc₁ hstep
  simpa only [X, level, upperTime, theta, c₀, c₁, C, A,
    canonicalForwardMoserIterationCost, n] using hbound

theorem nestedForwardMoserNorm_le_reverseCost_rpow_of_supersolution
    (g : SmoothRiemannianMetric I M)
    (hdim : 2 < (Module.finrank ℝ E : ℝ))
    (rho : SmoothScalar g)
    (u : ℝ → M → ℝ)
    (hu : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun z : ℝ × M => u z.1 z.2))
    (hpos : ∀ t x, 0 < u t x)
    {p₀ q a τ b B lower upper : ℝ} {m : ℕ}
    (hp₀ : 0 < p₀) (hq_one : q < 1)
    (haτ : a ≤ τ) (hτb : τ < b)
    (hB : 0 ≤ B) (hlowerUpper : lower < upper)
    (hrho : ∀ x : M,
      g.inner x
          (gradFun (I := I) g rho.toFun x)
          (gradFun (I := I) g rho.toFun x) ≤ B)
    (hpde : ∀ t ∈ Icc a b, ∀ x : M,
      Δ_g (I := I) g (smoothScalarSlice (I := I) g u hu t).toContMDiffMap x ≤
        deriv (fun s => u s x) t)
    (hexponents : ∀ k < m,
      parabolicMoserExponent (Module.finrank ℝ E) p₀ k ≤ q)
    (hm : 0 < m)
    (htarget : parabolicMoserExponent (Module.finrank ℝ E) p₀ m = q) :
    nestedForwardMoserNorm (I := I) (M := M) (Module.finrank ℝ E)
        rho u p₀ a (moserCutoffLevelBetween lower upper)
          (moserUpperTimeLevel τ b) m ≤
      canonicalForwardMoserReverseCost (I := I) (M := M)
          (Module.finrank ℝ E) g hdim q a τ b B lower upper ^
            (1 / p₀ - 1 / q) *
        nestedForwardMoserNorm (I := I) (M := M) (Module.finrank ℝ E)
          rho u p₀ a (moserCutoffLevelBetween lower upper)
            (moserUpperTimeLevel τ b) 0 := by
  let n := Module.finrank ℝ E
  letI : NeZero n := by
    refine ⟨Nat.ne_of_gt ?_⟩
    exact_mod_cast (by linarith : 0 < (n : ℝ))
  let D := canonicalForwardMoserLogCost (I := I) (M := M)
    n g hdim q a τ b B lower upper
  let X₀ := nestedForwardMoserNorm (I := I) (M := M) n
    rho u p₀ a (moserCutoffLevelBetween lower upper)
      (moserUpperTimeLevel τ b) 0
  have hbound := nestedForwardMoserNorm_le_exp_of_supersolution
    (I := I) (M := M) g hdim rho u hu hpos m hp₀ hq_one
      haτ hτb hB hlowerUpper hrho hpde hexponents
  rw [tsum_canonicalForwardMoserIterationCost n g hdim hp₀
    q a τ b B lower upper] at hbound
  have hprefactor := exp_div_le_rpow_exponent_gap n
    (canonicalForwardMoserLogCost_nonneg n g hdim q a τ b B lower upper)
    hp₀ hm (by simpa only [n] using htarget)
  have hX₀ : 0 ≤ X₀ := by
    unfold X₀ nestedForwardMoserNorm
    exact Real.rpow_nonneg
      (localizedSpacetimeRpowMoment_nonneg (I := I) (M := M)
        (spatialCutoffBetween rho
          (moserCutoffLevelBetween lower upper 0)
          (moserCutoffLevelBetween lower upper 1)) u
        (fun t x => (hpos t x).le)
        (parabolicMoserExponent n p₀ 0) a (moserUpperTimeLevel τ b 0)) _
  calc
    nestedForwardMoserNorm (I := I) (M := M) n
          rho u p₀ a (moserCutoffLevelBetween lower upper)
            (moserUpperTimeLevel τ b) m ≤ Real.exp (D / p₀) * X₀ := by
      simpa only [D, X₀, n] using hbound
    _ ≤ canonicalForwardMoserReverseCost (I := I) (M := M)
          n g hdim q a τ b B lower upper ^ (1 / p₀ - 1 / q) * X₀ := by
      exact mul_le_mul_of_nonneg_right (by
        simpa only [D, canonicalForwardMoserReverseCost] using hprefactor) hX₀
    _ = _ := by rfl

theorem localizedSpacetimeRpowNorm_le_canonicalForwardMoserReverseCost_of_supersolution
    (g : SmoothRiemannianMetric I M)
    (hdim : 2 < (Module.finrank ℝ E : ℝ))
    (rho inner outer : SmoothScalar g)
    (u : ℝ → M → ℝ)
    (hu : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun z : ℝ × M => u z.1 z.2))
    (hpos : ∀ t x, 0 < u t x)
    {p q a τ b B lower upper c d e f : ℝ} {m : ℕ}
    (hp : 0 < p) (hq_one : q < 1)
    (haτ : a ≤ τ) (hτb : τ < b)
    (hB : 0 ≤ B) (hlowerUpper : lower < upper)
    (hrho : ∀ x : M,
      g.inner x
          (gradFun (I := I) g rho.toFun x)
          (gradFun (I := I) g rho.toFun x) ≤ B)
    (hpde : ∀ t ∈ Icc a b, ∀ x : M,
      Δ_g (I := I) g (smoothScalarSlice (I := I) g u hu t).toContMDiffMap x ≤
        deriv (fun s => u s x) t)
    (hexponents : ∀ k < m,
      parabolicMoserExponent (Module.finrank ℝ E) p k ≤ q)
    (hm : 0 < m)
    (htarget : parabolicMoserExponent (Module.finrank ℝ E) p m = q)
    (hac : a ≤ c) (hdm : d ≤ moserUpperTimeLevel τ b m)
    (hinner : ∀ x,
      inner.toFun x ^ 2 ≤
        (spatialCutoffBetween rho
          (moserCutoffLevelBetween lower upper (2 * m))
          (moserCutoffLevelBetween lower upper (2 * m + 1))).toFun x ^ 2)
    (hea : e ≤ a) (hbf : b ≤ f)
    (houter : ∀ x,
      (spatialCutoffBetween rho
        (moserCutoffLevelBetween lower upper 0)
        (moserCutoffLevelBetween lower upper 1)).toFun x ^ 2 ≤
          outer.toFun x ^ 2) :
    localizedSpacetimeRpowNorm (I := I) (M := M) inner u q c d ≤
      canonicalForwardMoserReverseCost (I := I) (M := M)
          (Module.finrank ℝ E) g hdim q a τ b B lower upper ^
            (1 / p - 1 / q) *
        localizedSpacetimeRpowNorm (I := I) (M := M) outer u p e f := by
  let n := Module.finrank ℝ E
  letI : NeZero n := by
    refine ⟨Nat.ne_of_gt ?_⟩
    exact_mod_cast (by linarith : 0 < (n : ℝ))
  have hq : 0 < q := by
    rw [← htarget]
    exact parabolicMoserExponent_pos n hp m
  have hiteration := nestedForwardMoserNorm_le_reverseCost_rpow_of_supersolution
    (I := I) (M := M) g hdim rho u hu hpos hp hq_one
      haτ hτb hB hlowerUpper hrho hpde hexponents hm htarget
  have hinnerMono := localizedSpacetimeRpowNorm_mono_measure
    (I := I) (M := M) u hu.continuous hpos hq hac hdm hinner
  have houterMono := localizedSpacetimeRpowNorm_mono_measure
    (I := I) (M := M) u hu.continuous hpos hp hea hbf houter
  have hcost : 0 ≤
      canonicalForwardMoserReverseCost (I := I) (M := M)
          n g hdim q a τ b B lower upper ^ (1 / p - 1 / q) :=
    Real.rpow_nonneg (Real.exp_pos _).le _
  calc
    localizedSpacetimeRpowNorm (I := I) (M := M) inner u q c d ≤
        localizedSpacetimeRpowNorm (I := I) (M := M)
          (spatialCutoffBetween rho
            (moserCutoffLevelBetween lower upper (2 * m))
            (moserCutoffLevelBetween lower upper (2 * m + 1))) u q a
              (moserUpperTimeLevel τ b m) := hinnerMono
    _ = nestedForwardMoserNorm (I := I) (M := M) n rho u p a
          (moserCutoffLevelBetween lower upper)
          (moserUpperTimeLevel τ b) m := by
      simp only [nestedForwardMoserNorm, nestedForwardMoserMoment,
        localizedSpacetimeRpowNorm, htarget, n]
    _ ≤ canonicalForwardMoserReverseCost (I := I) (M := M)
          n g hdim q a τ b B lower upper ^ (1 / p - 1 / q) *
        nestedForwardMoserNorm (I := I) (M := M) n rho u p a
          (moserCutoffLevelBetween lower upper)
          (moserUpperTimeLevel τ b) 0 := by
      simpa only [n] using hiteration
    _ = canonicalForwardMoserReverseCost (I := I) (M := M)
          n g hdim q a τ b B lower upper ^ (1 / p - 1 / q) *
        localizedSpacetimeRpowNorm (I := I) (M := M)
          (spatialCutoffBetween rho
            (moserCutoffLevelBetween lower upper 0)
            (moserCutoffLevelBetween lower upper 1)) u p a b := by
      simp only [nestedForwardMoserNorm, nestedForwardMoserMoment,
        localizedSpacetimeRpowNorm, parabolicMoserExponent_zero,
        moserUpperTimeLevel_zero]
    _ ≤ canonicalForwardMoserReverseCost (I := I) (M := M)
          n g hdim q a τ b B lower upper ^ (1 / p - 1 / q) *
        localizedSpacetimeRpowNorm (I := I) (M := M) outer u p e f :=
      mul_le_mul_of_nonneg_left houterMono hcost

theorem nestedForwardMoserStepFactor_nonneg
    (n : ℕ) [NeZero n] (g : SmoothRiemannianMetric I M)
    (hdim : 2 < (Module.finrank ℝ E : ℝ))
    {B p₀ a : ℝ} (level upperTime : ℕ → ℝ) (k : ℕ)
    (hp₀ : 0 < p₀)
    (hexponent_one : parabolicMoserExponent n p₀ k < 1)
    (haTime : a ≤ upperTime (k + 1))
    (htime : upperTime (k + 1) < upperTime k)
    (hB : 0 ≤ B) :
    0 ≤ nestedForwardMoserStepFactor (I := I) (M := M)
      n g hdim B p₀ a level upperTime k := by
  have hK : 0 ≤ nestedForwardMoserGradientCost B level k := by
    exact div_nonneg (mul_nonneg (sq_nonneg _) hB) (sq_nonneg _)
  have hcoefficient := forwardMoserStepCoefficient_nonneg
    (parabolicMoserExponent_pos n hp₀ k) hexponent_one haTime htime hK
  exact mul_nonneg
    (Real.rpow_nonneg
      (localizedSobolevConstant_nonneg (I := I) (M := M) g hdim) _)
    (Real.rpow_nonneg hcoefficient _)

theorem nestedForwardMoserStepFactor_le_exp_canonicalForwardMoserIterationCost
    (n : ℕ) [NeZero n] (g : SmoothRiemannianMetric I M)
    (hdim : 2 < (Module.finrank ℝ E : ℝ))
    {p₀ qbar a τ b B lower upper : ℝ} (k : ℕ)
    (hp₀ : 0 < p₀)
    (hexponent_le : parabolicMoserExponent n p₀ k ≤ qbar)
    (hqbar_one : qbar < 1)
    (haτ : a ≤ τ) (hτb : τ < b)
    (hB : 0 ≤ B) (hlowerUpper : lower < upper) :
    nestedForwardMoserStepFactor (I := I) (M := M)
        n g hdim B p₀ a (moserCutoffLevelBetween lower upper)
          (moserUpperTimeLevel τ b) k ≤
      Real.exp
        (canonicalForwardMoserIterationCost (I := I) (M := M)
          n g hdim p₀ qbar a τ b B lower upper k) := by
  let level := moserCutoffLevelBetween lower upper
  let upperTime := moserUpperTimeLevel τ b
  let q := parabolicMoserExponent n p₀ k
  let K := nestedForwardMoserGradientCost B level k
  let coefficient := forwardMoserStepCoefficient q a
    (upperTime (k + 1)) (upperTime k) K
  let C := max 1 (localizedSobolevConstant (I := I) (M := M) g hdim)
  let A := canonicalForwardMoserStepEnvelope qbar a τ b B lower upper
  let L' := C * (A * 16 ^ k) ^ parabolicMoserGain n
  have hq : 0 < q := parabolicMoserExponent_pos n hp₀ k
  have hq_one : q < 1 := hexponent_le.trans_lt hqbar_one
  have hC : 1 ≤ C := le_max_left _ _
  have hA : 1 ≤ A := le_max_left _ _
  have haTime : a ≤ upperTime (k + 1) :=
    haτ.trans (moserUpperTimeLevel_lt hτb (k + 1)).le
  have htime : upperTime (k + 1) < upperTime k :=
    moserUpperTimeLevel_succ_lt hτb k
  have hK : 0 ≤ K := by
    dsimp only [K, nestedForwardMoserGradientCost]
    exact div_nonneg (mul_nonneg (sq_nonneg _) hB) (sq_nonneg _)
  have hcoefficient : 0 ≤ coefficient :=
    forwardMoserStepCoefficient_nonneg hq hq_one haTime htime hK
  have hcoefficient_bound : coefficient ≤ A * 16 ^ k := by
    simpa only [coefficient, K, A, level, upperTime, q] using
      (forwardMoserStepCoefficient_canonical_le_mul_pow k hq.le
        hexponent_le hqbar_one haτ hτb hB hlowerUpper)
  have hsobolev_bound :
      localizedSobolevConstant (I := I) (M := M) g hdim ≤ C :=
    le_max_right _ _
  have hfactor_bound :
      nestedForwardMoserStepFactor (I := I) (M := M)
          n g hdim B p₀ a level upperTime k ≤
        C ^ (1 / parabolicMoserExponent n p₀ (k + 1)) *
          (A * 16 ^ k) ^ (1 / q) := by
    unfold nestedForwardMoserStepFactor
    exact mul_le_mul
      (Real.rpow_le_rpow
        (localizedSobolevConstant_nonneg (I := I) (M := M) g hdim)
        hsobolev_bound
        (div_nonneg zero_le_one (parabolicMoserExponent_pos n hp₀ (k + 1)).le))
      (Real.rpow_le_rpow hcoefficient hcoefficient_bound
        (div_nonneg zero_le_one hq.le))
      (Real.rpow_nonneg hcoefficient _)
      (Real.rpow_nonneg (zero_le_one.trans hC) _)
  have hL' : 0 ≤ L' := by
    exact mul_nonneg (zero_le_one.trans hC)
      (Real.rpow_nonneg
        (mul_nonneg (zero_le_one.trans hA) (pow_nonneg (by norm_num) k)) _)
  have hnormalized := normalized_moser_step n hp₀ hC hA zero_le_one hL' k
    (by dsimp only [L']; rw [mul_one])
  have hrewrite :
      C ^ (1 / parabolicMoserExponent n p₀ (k + 1)) *
          (A * 16 ^ k) ^ (1 / q) =
        L' ^ (1 / parabolicMoserExponent n p₀ (k + 1)) := by
    have hAbase : 0 ≤ A * 16 ^ k :=
      mul_nonneg (zero_le_one.trans hA) (pow_nonneg (by norm_num) k)
    dsimp only [L']
    rw [Real.mul_rpow (zero_le_one.trans hC) (Real.rpow_nonneg hAbase _)]
    rw [← Real.rpow_mul hAbase]
    congr 1
    dsimp only [q]
    rw [parabolicMoserExponent_succ]
    field_simp [(parabolicMoserGain_pos n).ne', hq.ne']
  calc
    nestedForwardMoserStepFactor (I := I) (M := M)
          n g hdim B p₀ a level upperTime k ≤
        C ^ (1 / parabolicMoserExponent n p₀ (k + 1)) *
          (A * 16 ^ k) ^ (1 / q) := hfactor_bound
    _ = L' ^ (1 / parabolicMoserExponent n p₀ (k + 1)) := hrewrite
    _ ≤ Real.exp
        (canonicalForwardMoserIterationCost (I := I) (M := M)
          n g hdim p₀ qbar a τ b B lower upper k) := by
      simpa only [L', C, A, q, level, upperTime,
        canonicalForwardMoserIterationCost, mul_one, Real.one_rpow] using hnormalized

theorem nestedForwardMoserNorm_interpolation_step_of_supersolution
    (g : SmoothRiemannianMetric I M)
    (hdim : 2 < (Module.finrank ℝ E : ℝ))
    (rho : SmoothScalar g)
    (u : ℝ → M → ℝ)
    (hu : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun z : ℝ × M => u z.1 z.2))
    (hpos : ∀ t x, 0 < u t x)
    {p₀ q theta a B : ℝ} (level upperTime : ℕ → ℝ) (k : ℕ)
    (hp₀ : 0 < p₀) (hq : 0 < q)
    (htheta : 0 ≤ theta) (htheta_one : theta ≤ 1)
    (hq_eq : q =
      theta * parabolicMoserExponent (Module.finrank ℝ E) p₀ k +
        (1 - theta) *
          parabolicMoserExponent (Module.finrank ℝ E) p₀ (k + 1))
    (hexponent_one :
      parabolicMoserExponent (Module.finrank ℝ E) p₀ k < 1)
    (hlevel : StrictMono level) (htime : StrictAnti upperTime)
    (haTime : a ≤ upperTime (k + 1)) (hB : 0 ≤ B)
    (hrho : ∀ x : M,
      g.inner x
          (gradFun (I := I) g rho.toFun x)
          (gradFun (I := I) g rho.toFun x) ≤ B)
    (hpde : ∀ t ∈ Icc a (upperTime k), ∀ x : M,
      Δ_g (I := I) g (smoothScalarSlice (I := I) g u hu t).toContMDiffMap x ≤
        deriv (fun s => u s x) t) :
    localizedSpacetimeRpowNorm (I := I) (M := M)
        (spatialCutoffBetween rho (level (2 * (k + 1)))
          (level (2 * (k + 1) + 1))) u q a (upperTime (k + 1)) ≤
      nestedForwardMoserStepFactor (I := I) (M := M)
          (Module.finrank ℝ E) g hdim B p₀ a level upperTime k ^
            ((1 - theta) *
              parabolicMoserExponent (Module.finrank ℝ E) p₀ (k + 1) / q) *
        nestedForwardMoserNorm (I := I) (M := M) (Module.finrank ℝ E)
          rho u p₀ a level upperTime k := by
  let n := Module.finrank ℝ E
  letI : NeZero n := by
    refine ⟨Nat.ne_of_gt ?_⟩
    exact_mod_cast (by linarith : 0 < (n : ℝ))
  let p := parabolicMoserExponent n p₀ k
  let r := parabolicMoserExponent n p₀ (k + 1)
  let inner := spatialCutoffBetween rho (level (2 * (k + 1)))
    (level (2 * (k + 1) + 1))
  let outer := spatialCutoffBetween rho (level (2 * k)) (level (2 * k + 1))
  let factor := nestedForwardMoserStepFactor (I := I) (M := M)
    n g hdim B p₀ a level upperTime k
  let innerNorm : ℝ → ℝ := fun s =>
    localizedSpacetimeRpowNorm (I := I) (M := M)
      inner u s a (upperTime (k + 1))
  let outerNorm := localizedSpacetimeRpowNorm (I := I) (M := M)
    outer u p a (upperTime k)
  let alpha := theta * p / q
  let beta := (1 - theta) * r / q
  have hp : 0 < p := parabolicMoserExponent_pos n hp₀ k
  have hr : 0 < r := parabolicMoserExponent_pos n hp₀ (k + 1)
  have halpha : 0 ≤ alpha :=
    div_nonneg (mul_nonneg htheta hp.le) hq.le
  have hbeta : 0 ≤ beta :=
    div_nonneg (mul_nonneg (sub_nonneg.mpr htheta_one) hr.le) hq.le
  have halpha_beta : alpha + beta = 1 := by
    dsimp only [alpha, beta]
    rw [← add_div]
    rw [← hq_eq]
    exact div_self hq.ne'
  have hinnerOuterCutoff : ∀ x,
      inner.toFun x ^ 2 ≤ outer.toFun x ^ 2 := by
    intro x
    have hfirst := spatialCutoffBetween_sq_le rho
      (hlevel (Nat.lt_succ_self (2 * k + 1)))
      (hlevel (Nat.lt_succ_self (2 * k + 2))) x
    have hsecond := spatialCutoffBetween_sq_le rho
      (hlevel (Nat.lt_succ_self (2 * k)))
      (hlevel (Nat.lt_succ_self (2 * k + 1))) x
    simpa only [inner, outer, Nat.mul_add, Nat.mul_one, Nat.add_assoc] using
      hfirst.trans hsecond
  have hinnerOuter : innerNorm p ≤ outerNorm := by
    exact localizedSpacetimeRpowNorm_mono_measure
      (I := I) (M := M) u hu.continuous hpos hp le_rfl
        (htime.antitone (Nat.le_succ k)) hinnerOuterCutoff
  have hgain : innerNorm r ≤ factor * outerNorm := by
    simpa only [innerNorm, outerNorm, factor, inner, outer, p, r, n,
      nestedForwardMoserNorm, nestedForwardMoserMoment] using
      (nestedForwardMoserNorm_succ_le_of_supersolution
        (I := I) (M := M) g hdim rho u hu hpos level upperTime k hp₀
          (by simpa only [n] using hexponent_one) haTime
          (htime (Nat.lt_succ_self k))
          (hlevel (Nat.lt_succ_self (2 * k)))
          (hlevel (Nat.lt_succ_self (2 * k + 1)))
          (hlevel (Nat.lt_succ_self (2 * k + 2))) hB hrho hpde)
  have hinterpolation : innerNorm q ≤
      innerNorm p ^ alpha * innerNorm r ^ beta := by
    simpa only [innerNorm, alpha, beta, p, r, inner] using
      (localizedSpacetimeRpowNorm_le_interpolation
        (I := I) (M := M) inner u hu.continuous hpos hp hq hr
          htheta htheta_one (by simpa only [p, r, n] using hq_eq))
  have hfactor : 0 ≤ factor := by
    simpa only [factor, n] using
      (nestedForwardMoserStepFactor_nonneg
        (I := I) (M := M) n g hdim level upperTime k hp₀
          (by simpa only [n] using hexponent_one) haTime
          (htime (Nat.lt_succ_self k)) hB)
  have hinnerP : 0 ≤ innerNorm p :=
    localizedSpacetimeRpowNorm_nonneg (I := I) (M := M)
      inner u (fun t x => (hpos t x).le) p a (upperTime (k + 1))
  have hinnerR : 0 ≤ innerNorm r :=
    localizedSpacetimeRpowNorm_nonneg (I := I) (M := M)
      inner u (fun t x => (hpos t x).le) r a (upperTime (k + 1))
  have houter : 0 ≤ outerNorm :=
    localizedSpacetimeRpowNorm_nonneg (I := I) (M := M)
      outer u (fun t x => (hpos t x).le) p a (upperTime k)
  calc
    innerNorm q ≤ innerNorm p ^ alpha * innerNorm r ^ beta := hinterpolation
    _ ≤ outerNorm ^ alpha * (factor * outerNorm) ^ beta := by
      exact mul_le_mul
        (Real.rpow_le_rpow hinnerP hinnerOuter halpha)
        (Real.rpow_le_rpow hinnerR hgain hbeta)
        (Real.rpow_nonneg hinnerR beta)
        (Real.rpow_nonneg houter alpha)
    _ = factor ^ beta * outerNorm := by
      rw [Real.mul_rpow hfactor houter]
      calc
        outerNorm ^ alpha * (factor ^ beta * outerNorm ^ beta) =
            factor ^ beta * (outerNorm ^ alpha * outerNorm ^ beta) := by ring
        _ = factor ^ beta * outerNorm ^ (alpha + beta) := by
          rw [Real.rpow_add_of_nonneg houter halpha hbeta]
        _ = factor ^ beta * outerNorm := by rw [halpha_beta, Real.rpow_one]
    _ = _ := by rfl

theorem nestedForwardMoserNorm_interpolation_step_le_exp_of_supersolution
    (g : SmoothRiemannianMetric I M)
    (hdim : 2 < (Module.finrank ℝ E : ℝ))
    (rho : SmoothScalar g)
    (u : ℝ → M → ℝ)
    (hu : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun z : ℝ × M => u z.1 z.2))
    (hpos : ∀ t x, 0 < u t x)
    {p₀ q theta qbar a τ b B lower upper : ℝ} (k : ℕ)
    (hp₀ : 0 < p₀) (hq : 0 < q)
    (htheta : 0 ≤ theta) (htheta_one : theta ≤ 1)
    (hq_eq : q =
      theta * parabolicMoserExponent (Module.finrank ℝ E) p₀ k +
        (1 - theta) *
          parabolicMoserExponent (Module.finrank ℝ E) p₀ (k + 1))
    (hexponent_le :
      parabolicMoserExponent (Module.finrank ℝ E) p₀ k ≤ qbar)
    (hqbar_one : qbar < 1)
    (haτ : a ≤ τ) (hτb : τ < b)
    (hB : 0 ≤ B) (hlowerUpper : lower < upper)
    (hrho : ∀ x : M,
      g.inner x
          (gradFun (I := I) g rho.toFun x)
          (gradFun (I := I) g rho.toFun x) ≤ B)
    (hpde : ∀ t ∈ Icc a b, ∀ x : M,
      Δ_g (I := I) g (smoothScalarSlice (I := I) g u hu t).toContMDiffMap x ≤
        deriv (fun s => u s x) t) :
    localizedSpacetimeRpowNorm (I := I) (M := M)
        (spatialCutoffBetween rho
          (moserCutoffLevelBetween lower upper (2 * (k + 1)))
          (moserCutoffLevelBetween lower upper (2 * (k + 1) + 1)))
        u q a (moserUpperTimeLevel τ b (k + 1)) ≤
      Real.exp
          (((1 - theta) *
              parabolicMoserExponent (Module.finrank ℝ E) p₀ (k + 1) / q) *
            canonicalForwardMoserIterationCost (I := I) (M := M)
              (Module.finrank ℝ E) g hdim p₀ qbar a τ b B lower upper k) *
        nestedForwardMoserNorm (I := I) (M := M) (Module.finrank ℝ E)
          rho u p₀ a (moserCutoffLevelBetween lower upper)
            (moserUpperTimeLevel τ b) k := by
  let n := Module.finrank ℝ E
  letI : NeZero n := by
    refine ⟨Nat.ne_of_gt ?_⟩
    exact_mod_cast (by linarith : 0 < (n : ℝ))
  let level := moserCutoffLevelBetween lower upper
  let upperTime := moserUpperTimeLevel τ b
  let p := parabolicMoserExponent n p₀ k
  let r := parabolicMoserExponent n p₀ (k + 1)
  let beta := (1 - theta) * r / q
  let factor := nestedForwardMoserStepFactor (I := I) (M := M)
    n g hdim B p₀ a level upperTime k
  let cost := canonicalForwardMoserIterationCost (I := I) (M := M)
    n g hdim p₀ qbar a τ b B lower upper k
  let X := nestedForwardMoserNorm (I := I) (M := M) n
    rho u p₀ a level upperTime k
  have hp : 0 < p := parabolicMoserExponent_pos n hp₀ k
  have hr : 0 < r := parabolicMoserExponent_pos n hp₀ (k + 1)
  have hbeta : 0 ≤ beta :=
    div_nonneg (mul_nonneg (sub_nonneg.mpr htheta_one) hr.le) hq.le
  have hraw :
      localizedSpacetimeRpowNorm (I := I) (M := M)
          (spatialCutoffBetween rho (level (2 * (k + 1)))
            (level (2 * (k + 1) + 1))) u q a (upperTime (k + 1)) ≤
        factor ^ beta * X := by
    simpa only [level, upperTime, p, r, beta, factor, X, n] using
      (nestedForwardMoserNorm_interpolation_step_of_supersolution
        (I := I) (M := M) g hdim rho u hu hpos level upperTime k hp₀ hq
          htheta htheta_one (by simpa only [n] using hq_eq)
          (hexponent_le.trans_lt hqbar_one)
          (moserCutoffLevelBetween_strictMono hlowerUpper)
          (moserUpperTimeLevel_strictAnti hτb)
          (haτ.trans (moserUpperTimeLevel_lt hτb (k + 1)).le) hB hrho
          (fun t ht x => hpde t
            ⟨ht.1, ht.2.trans (moserUpperTimeLevel_le hτb k)⟩ x))
  have hfactor : 0 ≤ factor := by
    simpa only [factor, level, upperTime, n] using
      (nestedForwardMoserStepFactor_nonneg
        (I := I) (M := M) n g hdim level upperTime k hp₀
          (hexponent_le.trans_lt hqbar_one)
          (haτ.trans (moserUpperTimeLevel_lt hτb (k + 1)).le)
          (moserUpperTimeLevel_succ_lt hτb k) hB)
  have hfactorBound : factor ≤ Real.exp cost := by
    simpa only [factor, cost, level, upperTime, n] using
      (nestedForwardMoserStepFactor_le_exp_canonicalForwardMoserIterationCost
        (I := I) (M := M) n g hdim k hp₀ hexponent_le hqbar_one
          haτ hτb hB hlowerUpper)
  have hX : 0 ≤ X := by
    exact localizedSpacetimeRpowNorm_nonneg (I := I) (M := M)
      (spatialCutoffBetween rho (level (2 * k)) (level (2 * k + 1)))
      u (fun t x => (hpos t x).le) p a (upperTime k)
  have hpower : factor ^ beta ≤ Real.exp (beta * cost) := by
    calc
      factor ^ beta ≤ (Real.exp cost) ^ beta :=
        Real.rpow_le_rpow hfactor hfactorBound hbeta
      _ = Real.exp (beta * cost) := by
        rw [Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]
        congr 1
        ring
  calc
    localizedSpacetimeRpowNorm (I := I) (M := M)
          (spatialCutoffBetween rho (level (2 * (k + 1)))
            (level (2 * (k + 1) + 1))) u q a (upperTime (k + 1)) ≤
        factor ^ beta * X := hraw
    _ ≤ Real.exp (beta * cost) * X := mul_le_mul_of_nonneg_right hpower hX
    _ = _ := by rfl

theorem nestedForwardMoserNorm_interpolation_le_reverseCost_rpow_of_supersolution
    (g : SmoothRiemannianMetric I M)
    (hdim : 2 < (Module.finrank ℝ E : ℝ))
    (rho : SmoothScalar g)
    (u : ℝ → M → ℝ)
    (hu : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun z : ℝ × M => u z.1 z.2))
    (hpos : ∀ t x, 0 < u t x)
    {p₀ q theta a τ b B lower upper : ℝ} (k : ℕ)
    (hp₀ : 0 < p₀) (hq : 0 < q) (hq_one : q < 1)
    (htheta : 0 ≤ theta) (htheta_one : theta ≤ 1)
    (hq_eq : q =
      theta * parabolicMoserExponent (Module.finrank ℝ E) p₀ k +
        (1 - theta) *
          parabolicMoserExponent (Module.finrank ℝ E) p₀ (k + 1))
    (haτ : a ≤ τ) (hτb : τ < b)
    (hB : 0 ≤ B) (hlowerUpper : lower < upper)
    (hrho : ∀ x : M,
      g.inner x
          (gradFun (I := I) g rho.toFun x)
          (gradFun (I := I) g rho.toFun x) ≤ B)
    (hpde : ∀ t ∈ Icc a b, ∀ x : M,
      Δ_g (I := I) g (smoothScalarSlice (I := I) g u hu t).toContMDiffMap x ≤
        deriv (fun s => u s x) t) :
    localizedSpacetimeRpowNorm (I := I) (M := M)
        (spatialCutoffBetween rho
          (moserCutoffLevelBetween lower upper (2 * (k + 1)))
          (moserCutoffLevelBetween lower upper (2 * (k + 1) + 1)))
        u q a (moserUpperTimeLevel τ b (k + 1)) ≤
      canonicalForwardMoserReverseCost (I := I) (M := M)
          (Module.finrank ℝ E) g hdim q a τ b B lower upper ^
            (1 / p₀ - 1 / q) *
        nestedForwardMoserNorm (I := I) (M := M) (Module.finrank ℝ E)
          rho u p₀ a (moserCutoffLevelBetween lower upper)
            (moserUpperTimeLevel τ b) 0 := by
  let n := Module.finrank ℝ E
  letI : NeZero n := by
    refine ⟨Nat.ne_of_gt ?_⟩
    exact_mod_cast (by linarith : 0 < (n : ℝ))
  let level := moserCutoffLevelBetween lower upper
  let upperTime := moserUpperTimeLevel τ b
  let p := parabolicMoserExponent n p₀ k
  let r := parabolicMoserExponent n p₀ (k + 1)
  let alpha := theta * p / q
  let beta := (1 - theta) * r / q
  let cost : ℕ → ℝ := fun j =>
    canonicalForwardMoserIterationCost (I := I) (M := M)
      n g hdim p₀ q a τ b B lower upper j
  let D := canonicalForwardMoserLogCost (I := I) (M := M)
    n g hdim q a τ b B lower upper
  let R := canonicalForwardMoserReverseCost (I := I) (M := M)
    n g hdim q a τ b B lower upper
  let X : ℕ → ℝ := fun j =>
    nestedForwardMoserNorm (I := I) (M := M)
      n rho u p₀ a level upperTime j
  have hp : 0 < p := parabolicMoserExponent_pos n hp₀ k
  have hr : 0 < r := parabolicMoserExponent_pos n hp₀ (k + 1)
  have hpr : p < r := parabolicMoserExponent_strictMono n hp₀
    (Nat.lt_succ_self k)
  have halpha : 0 ≤ alpha :=
    div_nonneg (mul_nonneg htheta hp.le) hq.le
  have hbeta : 0 ≤ beta :=
    div_nonneg (mul_nonneg (sub_nonneg.mpr htheta_one) hr.le) hq.le
  have halpha_beta : alpha + beta = 1 := by
    dsimp only [alpha, beta]
    rw [← add_div, ← hq_eq]
    exact div_self hq.ne'
  have hbeta_one : beta ≤ 1 := by linarith
  have hpq : p ≤ q := by
    rw [hq_eq]
    nlinarith [mul_nonneg htheta hp.le,
      mul_nonneg (sub_nonneg.mpr htheta_one) hr.le]
  have hexponents : ∀ j < k, parabolicMoserExponent n p₀ j ≤ q := by
    intro j hj
    exact (parabolicMoserExponent_strictMono n hp₀ hj).le.trans hpq
  have hstep :=
    nestedForwardMoserNorm_interpolation_step_le_exp_of_supersolution
      (I := I) (M := M) g hdim rho u hu hpos k hp₀ hq htheta htheta_one
        (by simpa only [n] using hq_eq) hpq hq_one haτ hτb hB
        hlowerUpper hrho hpde
  have hprior := nestedForwardMoserNorm_le_exp_finset_of_supersolution
    (I := I) (M := M) g hdim rho u hu hpos k hp₀ hq_one
      haτ hτb hB hlowerUpper hrho hpde
      (by simpa only [n] using hexponents)
  have hcost_nonneg : ∀ j, 0 ≤ cost j := by
    intro j
    simpa only [cost] using
      (canonicalForwardMoserIterationCost_nonneg
        (I := I) (M := M) n g hdim hp₀ q a τ b B lower upper j)
  have hcost_summable : Summable cost := by
    unfold cost canonicalForwardMoserIterationCost
    exact summable_moserIterationCost (parabolicMoserDecay_pos n).le
      (parabolicMoserDecay_lt_one n)
  have hpartial :
      (∑ j ∈ Finset.range k, cost j) + beta * cost k ≤ ∑' j, cost j := by
    calc
      (∑ j ∈ Finset.range k, cost j) + beta * cost k ≤
          (∑ j ∈ Finset.range k, cost j) + cost k := by
        gcongr
        exact mul_le_of_le_one_left (hcost_nonneg k) hbeta_one
      _ = ∑ j ∈ Finset.range (k + 1), cost j := by
        rw [Finset.sum_range_succ]
      _ ≤ ∑' j, cost j :=
        hcost_summable.sum_le_tsum (Finset.range (k + 1))
          (fun j _ => hcost_nonneg j)
  have htsum : (∑' j, cost j) = D / p₀ := by
    simpa only [cost, D] using
      (tsum_canonicalForwardMoserIterationCost
        (I := I) (M := M) n g hdim hp₀ q a τ b B lower upper)
  have hpartialD :
      (∑ j ∈ Finset.range k, cost j) + beta * cost k ≤ D / p₀ := by
    rw [← htsum]
    exact hpartial
  have hlogbound :
      (∑ j ∈ Finset.range k, cost j) + beta * cost k ≤
        D / (1 - parabolicMoserDecay n) * (1 / p₀ - 1 / q) := by
    by_cases hk : k = 0
    · subst k
      have hinvr : 1 / r = parabolicMoserDecay n / p₀ := by
        simpa only [r, pow_one] using inv_parabolicMoserExponent n hp₀ 1
      have hq_eq_zero : q = theta * p₀ + (1 - theta) * r := by
        simpa only [n, r, parabolicMoserExponent_zero, zero_add] using hq_eq
      have hgap : 1 / p₀ - 1 / q = beta * (1 / p₀ - 1 / r) := by
        dsimp only [beta]
        field_simp [hp₀.ne', hq.ne', hr.ne']
        rw [hq_eq_zero]
        ring
      have hcost_zero : cost 0 ≤ D / p₀ := by
        have hsingle := hcost_summable.sum_le_tsum ({0} : Finset ℕ)
          (fun j _ => hcost_nonneg j)
        simpa only [Finset.sum_singleton, htsum] using hsingle
      simp only [Finset.range_zero, Finset.sum_empty, zero_add]
      calc
        beta * cost 0 ≤ beta * (D / p₀) :=
          mul_le_mul_of_nonneg_left hcost_zero hbeta
        _ = D / (1 - parabolicMoserDecay n) * (1 / p₀ - 1 / q) := by
          rw [hgap, hinvr]
          field_simp [hp₀.ne',
            (sub_pos.mpr (parabolicMoserDecay_lt_one n)).ne']
    · have hkpos : 0 < k := Nat.pos_of_ne_zero hk
      have hprefactor := exp_div_le_rpow_exponent_gap n
        (canonicalForwardMoserLogCost_nonneg n g hdim q a τ b B lower upper)
        hp₀ hkpos (by rfl : parabolicMoserExponent n p₀ k = p)
      have hprefactor_log :
          D / p₀ ≤ D / (1 - parabolicMoserDecay n) * (1 / p₀ - 1 / p) := by
        change Real.exp (D / p₀) ≤
          Real.exp (D / (1 - parabolicMoserDecay n)) ^
            (1 / p₀ - 1 / p) at hprefactor
        rw [Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp] at hprefactor
        exact Real.exp_le_exp.mp hprefactor
      have hinv : 1 / q ≤ 1 / p := one_div_le_one_div_of_le hp hpq
      have hDdiv : 0 ≤ D / (1 - parabolicMoserDecay n) :=
        div_nonneg
          (canonicalForwardMoserLogCost_nonneg n g hdim q a τ b B lower upper)
          (sub_nonneg.mpr (parabolicMoserDecay_lt_one n).le)
      calc
        (∑ j ∈ Finset.range k, cost j) + beta * cost k ≤ D / p₀ := hpartialD
        _ ≤ D / (1 - parabolicMoserDecay n) * (1 / p₀ - 1 / p) :=
          hprefactor_log
        _ ≤ D / (1 - parabolicMoserDecay n) * (1 / p₀ - 1 / q) := by
          exact mul_le_mul_of_nonneg_left (sub_le_sub_left hinv (1 / p₀)) hDdiv
  have hprefactor :
      Real.exp ((∑ j ∈ Finset.range k, cost j) + beta * cost k) ≤
        R ^ (1 / p₀ - 1 / q) := by
    unfold R canonicalForwardMoserReverseCost
    rw [Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]
    exact Real.exp_le_exp.mpr hlogbound
  have hXzero : 0 ≤ X 0 := by
    simpa only [X, nestedForwardMoserNorm, nestedForwardMoserMoment,
      parabolicMoserExponent_zero] using
      (localizedSpacetimeRpowNorm_nonneg (I := I) (M := M)
        (spatialCutoffBetween rho (level 0) (level 1)) u
        (fun t x => (hpos t x).le) p₀ a (upperTime 0))
  calc
    localizedSpacetimeRpowNorm (I := I) (M := M)
          (spatialCutoffBetween rho (level (2 * (k + 1)))
            (level (2 * (k + 1) + 1))) u q a (upperTime (k + 1)) ≤
        Real.exp (beta * cost k) * X k := by
      simpa only [level, upperTime, beta, cost, p, r, n] using hstep
    _ ≤ Real.exp (beta * cost k) *
        (Real.exp (∑ j ∈ Finset.range k, cost j) * X 0) := by
      exact mul_le_mul_of_nonneg_left
        (by simpa only [X, level, upperTime, cost, n] using hprior)
        (Real.exp_pos _).le
    _ = Real.exp ((∑ j ∈ Finset.range k, cost j) + beta * cost k) * X 0 := by
      rw [Real.exp_add]
      ring
    _ ≤ R ^ (1 / p₀ - 1 / q) * X 0 :=
      mul_le_mul_of_nonneg_right hprefactor hXzero
    _ = _ := by rfl

theorem exists_nested_forward_moser_reverse_holder_of_supersolution
    (g : SmoothRiemannianMetric I M)
    (hdim : 2 < (Module.finrank ℝ E : ℝ))
    (rho : SmoothScalar g)
    (u : ℝ → M → ℝ)
    (hu : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun z : ℝ × M => u z.1 z.2))
    (hpos : ∀ t x, 0 < u t x)
    {p q a τ b B lower upper : ℝ}
    (hp : 0 < p) (hpq : p < q) (hq_one : q < 1)
    (haτ : a ≤ τ) (hτb : τ < b)
    (hB : 0 ≤ B) (hlowerUpper : lower < upper)
    (hrho : ∀ x : M,
      g.inner x
          (gradFun (I := I) g rho.toFun x)
          (gradFun (I := I) g rho.toFun x) ≤ B)
    (hpde : ∀ t ∈ Icc a b, ∀ x : M,
      Δ_g (I := I) g (smoothScalarSlice (I := I) g u hu t).toContMDiffMap x ≤
        deriv (fun s => u s x) t) :
    ∃ m : ℕ, 0 < m ∧
      localizedSpacetimeRpowNorm (I := I) (M := M)
          (spatialCutoffBetween rho
            (moserCutoffLevelBetween lower upper (2 * m))
            (moserCutoffLevelBetween lower upper (2 * m + 1)))
          u q a (moserUpperTimeLevel τ b m) ≤
        canonicalForwardMoserReverseCost (I := I) (M := M)
            (Module.finrank ℝ E) g hdim q a τ b B lower upper ^
              (1 / p - 1 / q) *
          nestedForwardMoserNorm (I := I) (M := M) (Module.finrank ℝ E)
            rho u p a (moserCutoffLevelBetween lower upper)
              (moserUpperTimeLevel τ b) 0 := by
  let n := Module.finrank ℝ E
  letI : NeZero n := by
    refine ⟨Nat.ne_of_gt ?_⟩
    exact_mod_cast (by linarith : 0 < (n : ℝ))
  obtain ⟨m, hpstar_p, hp_gain⟩ :=
    exists_parabolic_moser_iteration_depth n hp hpq
  let pstar := q * parabolicMoserDecay n ^ m
  have hm : 0 < m := by
    by_contra hmzero
    have hmzero' : m = 0 := Nat.eq_zero_of_not_pos hmzero
    subst m
    have hqp : q < p := by simpa only [pstar, pow_zero, mul_one] using hpstar_p
    exact (lt_irrefl p) (hpq.trans hqp)
  let k := m - 1
  have hkm : k + 1 = m := Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hm.ne')
  let pk := parabolicMoserExponent n p k
  let rk := parabolicMoserExponent n p (k + 1)
  have hpstar_target : parabolicMoserExponent n pstar m = q := by
    simpa only [pstar] using parabolicMoserExponent_decay_mul_self n q m
  have hpkq : pk ≤ q := by
    calc
      pk ≤ parabolicMoserExponent n (parabolicMoserGain n * pstar) k := by
        unfold pk parabolicMoserExponent
        exact mul_le_mul_of_nonneg_right hp_gain
          (pow_nonneg (parabolicMoserGain_pos n).le k)
      _ = parabolicMoserExponent n pstar (k + 1) := by
        unfold parabolicMoserExponent
        rw [pow_succ]
        ring
      _ = parabolicMoserExponent n pstar m := by rw [hkm]
      _ = q := hpstar_target
  have hqrk : q < rk := by
    calc
      q = parabolicMoserExponent n pstar m := hpstar_target.symm
      _ < parabolicMoserExponent n p m := by
        unfold parabolicMoserExponent
        exact mul_lt_mul_of_pos_right hpstar_p
          (pow_pos (parabolicMoserGain_pos n) m)
      _ = rk := by rw [← hkm]
  have hpkrk : pk < rk := by
    exact parabolicMoserExponent_strictMono n hp (Nat.lt_succ_self k)
  let theta := (rk - q) / (rk - pk)
  have htheta : 0 ≤ theta :=
    div_nonneg (sub_nonneg.mpr hqrk.le) (sub_nonneg.mpr hpkrk.le)
  have htheta_one : theta ≤ 1 := by
    apply (div_le_one (sub_pos.mpr hpkrk)).2
    linarith
  have hq_eq : q = theta * pk + (1 - theta) * rk := by
    dsimp only [theta]
    field_simp [(sub_pos.mpr hpkrk).ne']
    ring
  have hbound :=
    nestedForwardMoserNorm_interpolation_le_reverseCost_rpow_of_supersolution
      (I := I) (M := M) g hdim rho u hu hpos k hp (hp.trans hpq)
        hq_one htheta htheta_one
        (by simpa only [pk, rk, n] using hq_eq)
        haτ hτb hB hlowerUpper hrho hpde
  refine ⟨m, hm, ?_⟩
  simpa only [k, hkm, n] using hbound

theorem localizedSpacetimeRpowNorm_le_canonicalForwardMoserReverseCost_of_supersolution_of_lt
    (g : SmoothRiemannianMetric I M)
    (hdim : 2 < (Module.finrank ℝ E : ℝ))
    (rho inner outer : SmoothScalar g)
    (u : ℝ → M → ℝ)
    (hu : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun z : ℝ × M => u z.1 z.2))
    (hpos : ∀ t x, 0 < u t x)
    {p q a τ b B lower upper c d e f : ℝ}
    (hp : 0 < p) (hpq : p < q) (hq_one : q < 1)
    (haτ : a ≤ τ) (hτb : τ < b)
    (hB : 0 ≤ B) (hlowerUpper : lower < upper)
    (hrho : ∀ x : M,
      g.inner x
          (gradFun (I := I) g rho.toFun x)
          (gradFun (I := I) g rho.toFun x) ≤ B)
    (hpde : ∀ t ∈ Icc a b, ∀ x : M,
      Δ_g (I := I) g (smoothScalarSlice (I := I) g u hu t).toContMDiffMap x ≤
        deriv (fun s => u s x) t)
    (hac : a ≤ c)
    (hdm : ∀ m, 0 < m → d ≤ moserUpperTimeLevel τ b m)
    (hinner : ∀ m, 0 < m → ∀ x,
      inner.toFun x ^ 2 ≤
        (spatialCutoffBetween rho
          (moserCutoffLevelBetween lower upper (2 * m))
          (moserCutoffLevelBetween lower upper (2 * m + 1))).toFun x ^ 2)
    (hea : e ≤ a) (hbf : b ≤ f)
    (houter : ∀ x,
      (spatialCutoffBetween rho
        (moserCutoffLevelBetween lower upper 0)
        (moserCutoffLevelBetween lower upper 1)).toFun x ^ 2 ≤
          outer.toFun x ^ 2) :
    localizedSpacetimeRpowNorm (I := I) (M := M) inner u q c d ≤
      canonicalForwardMoserReverseCost (I := I) (M := M)
          (Module.finrank ℝ E) g hdim q a τ b B lower upper ^
            (1 / p - 1 / q) *
        localizedSpacetimeRpowNorm (I := I) (M := M) outer u p e f := by
  let n := Module.finrank ℝ E
  letI : NeZero n := by
    refine ⟨Nat.ne_of_gt ?_⟩
    exact_mod_cast (by linarith : 0 < (n : ℝ))
  obtain ⟨m, hm, hiteration⟩ :=
    exists_nested_forward_moser_reverse_holder_of_supersolution
      (I := I) (M := M) g hdim rho u hu hpos hp hpq hq_one
        haτ hτb hB hlowerUpper hrho hpde
  have hinnerMono := localizedSpacetimeRpowNorm_mono_measure
    (I := I) (M := M) u hu.continuous hpos (hp.trans hpq) hac
      (hdm m hm) (hinner m hm)
  have houterMono := localizedSpacetimeRpowNorm_mono_measure
    (I := I) (M := M) u hu.continuous hpos hp hea hbf houter
  have hcost : 0 ≤
      canonicalForwardMoserReverseCost (I := I) (M := M)
          n g hdim q a τ b B lower upper ^ (1 / p - 1 / q) :=
    Real.rpow_nonneg (Real.exp_pos _).le _
  calc
    localizedSpacetimeRpowNorm (I := I) (M := M) inner u q c d ≤
        localizedSpacetimeRpowNorm (I := I) (M := M)
          (spatialCutoffBetween rho
            (moserCutoffLevelBetween lower upper (2 * m))
            (moserCutoffLevelBetween lower upper (2 * m + 1)))
          u q a (moserUpperTimeLevel τ b m) := hinnerMono
    _ ≤ canonicalForwardMoserReverseCost (I := I) (M := M)
          n g hdim q a τ b B lower upper ^ (1 / p - 1 / q) *
        nestedForwardMoserNorm (I := I) (M := M) n
          rho u p a (moserCutoffLevelBetween lower upper)
            (moserUpperTimeLevel τ b) 0 := by
      simpa only [n] using hiteration
    _ = canonicalForwardMoserReverseCost (I := I) (M := M)
          n g hdim q a τ b B lower upper ^ (1 / p - 1 / q) *
        localizedSpacetimeRpowNorm (I := I) (M := M)
          (spatialCutoffBetween rho
            (moserCutoffLevelBetween lower upper 0)
            (moserCutoffLevelBetween lower upper 1)) u p a b := by
      simp only [nestedForwardMoserNorm, nestedForwardMoserMoment,
        localizedSpacetimeRpowNorm, parabolicMoserExponent_zero,
        moserUpperTimeLevel_zero,
        Nat.mul_zero, Nat.zero_add]
    _ ≤ canonicalForwardMoserReverseCost (I := I) (M := M)
          n g hdim q a τ b B lower upper ^ (1 / p - 1 / q) *
        localizedSpacetimeRpowNorm (I := I) (M := M) outer u p e f :=
      mul_le_mul_of_nonneg_left houterMono hcost

theorem nestedForwardMoserNorm_le_of_supersolution
    (g : SmoothRiemannianMetric I M)
    (hdim : 2 < (Module.finrank ℝ E : ℝ))
    (rho : SmoothScalar g)
    (u : ℝ → M → ℝ)
    (hu : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun z : ℝ × M => u z.1 z.2))
    (hpos : ∀ t x, 0 < u t x)
    {p₀ a B : ℝ} (level upperTime : ℕ → ℝ) (m : ℕ)
    (hp₀ : 0 < p₀)
    (hlevel : StrictMono level) (htime : StrictAnti upperTime)
    (haTime : a ≤ upperTime m) (hB : 0 ≤ B)
    (hrho : ∀ x : M,
      g.inner x
          (gradFun (I := I) g rho.toFun x)
          (gradFun (I := I) g rho.toFun x) ≤ B)
    (hpde : ∀ t ∈ Icc a (upperTime 0), ∀ x : M,
      Δ_g (I := I) g (smoothScalarSlice (I := I) g u hu t).toContMDiffMap x ≤
        deriv (fun s => u s x) t)
    (hexponents : ∀ k < m,
      parabolicMoserExponent (Module.finrank ℝ E) p₀ k < 1) :
    nestedForwardMoserNorm (I := I) (M := M) (Module.finrank ℝ E)
        rho u p₀ a level upperTime m ≤
      (∏ k ∈ Finset.range m,
        nestedForwardMoserStepFactor (I := I) (M := M)
          (Module.finrank ℝ E) g hdim B p₀ a level upperTime k) *
        nestedForwardMoserNorm (I := I) (M := M) (Module.finrank ℝ E)
          rho u p₀ a level upperTime 0 := by
  let n := Module.finrank ℝ E
  letI : NeZero n := by
    refine ⟨Nat.ne_of_gt ?_⟩
    exact_mod_cast (by linarith : 0 < (n : ℝ))
  let X : ℕ → ℝ := fun k =>
    nestedForwardMoserNorm (I := I) (M := M)
      n rho u p₀ a level upperTime k
  let factor : ℕ → ℝ := fun k =>
    nestedForwardMoserStepFactor (I := I) (M := M)
      n g hdim B p₀ a level upperTime k
  have hfactor : ∀ k < m, 0 ≤ factor k := by
    intro k hk
    have hk1m : k + 1 ≤ m := Nat.succ_le_iff.mpr hk
    exact nestedForwardMoserStepFactor_nonneg (I := I) (M := M)
      n g hdim level upperTime k hp₀
        (by simpa only [n] using hexponents k hk)
        (haTime.trans (htime.antitone hk1m))
        (htime (Nat.lt_succ_self k)) hB
  have hstep : ∀ k < m, X (k + 1) ≤ factor k * X k := by
    intro k hk
    have hk1m : k + 1 ≤ m := Nat.succ_le_iff.mpr hk
    exact nestedForwardMoserNorm_succ_le_of_supersolution
      (I := I) (M := M) g hdim rho u hu hpos level upperTime k hp₀
        (by simpa only [n] using hexponents k hk)
        (haTime.trans (htime.antitone hk1m))
        (htime (Nat.lt_succ_self k))
        (hlevel (Nat.lt_succ_self (2 * k)))
        (hlevel (Nat.lt_succ_self (2 * k + 1)))
        (hlevel (Nat.lt_succ_self (2 * k + 2)))
        hB hrho
        (fun t ht x => hpde t
          ⟨ht.1, ht.2.trans (htime.antitone (Nat.zero_le k))⟩ x)
  simpa only [X, factor, n] using
    (finite_multiplicative_iteration m hfactor hstep)

theorem nestedForwardMoserNorm_le_rpowNorm_of_supersolution
    (g : SmoothRiemannianMetric I M)
    (hdim : 2 < (Module.finrank ℝ E : ℝ))
    (rho : SmoothScalar g)
    (u : ℝ → M → ℝ)
    (hu : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun z : ℝ × M => u z.1 z.2))
    (hpos : ∀ t x, 0 < u t x)
    {p₀ p a B : ℝ} (level upperTime : ℕ → ℝ) (m : ℕ)
    (hp₀ : 0 < p₀) (hp₀p : p₀ ≤ p)
    (hlevel : StrictMono level) (htime : StrictAnti upperTime)
    (haTime : a ≤ upperTime m) (hB : 0 ≤ B)
    (hrho : ∀ x : M,
      g.inner x
          (gradFun (I := I) g rho.toFun x)
          (gradFun (I := I) g rho.toFun x) ≤ B)
    (hpde : ∀ t ∈ Icc a (upperTime 0), ∀ x : M,
      Δ_g (I := I) g (smoothScalarSlice (I := I) g u hu t).toContMDiffMap x ≤
        deriv (fun s => u s x) t)
    (hexponents : ∀ k < m,
      parabolicMoserExponent (Module.finrank ℝ E) p₀ k < 1)
    (hmass :
      (localizedSpacetimeMeasure (I := I) (M := M)
        (spatialCutoffBetween rho (level 0) (level 1)) a (upperTime 0)).real
          Set.univ ≤ 1) :
    nestedForwardMoserNorm (I := I) (M := M) (Module.finrank ℝ E)
        rho u p₀ a level upperTime m ≤
      (∏ k ∈ Finset.range m,
        nestedForwardMoserStepFactor (I := I) (M := M)
          (Module.finrank ℝ E) g hdim B p₀ a level upperTime k) *
        localizedSpacetimeRpowNorm (I := I) (M := M)
          (spatialCutoffBetween rho (level 0) (level 1)) u
            p a (upperTime 0) := by
  let n := Module.finrank ℝ E
  letI : NeZero n := by
    refine ⟨Nat.ne_of_gt ?_⟩
    exact_mod_cast (by linarith : 0 < (n : ℝ))
  let factor : ℕ → ℝ := fun k =>
    nestedForwardMoserStepFactor (I := I) (M := M)
      n g hdim B p₀ a level upperTime k
  let P := ∏ k ∈ Finset.range m, factor k
  have hiteration := nestedForwardMoserNorm_le_of_supersolution
    (I := I) (M := M) g hdim rho u hu hpos level upperTime m hp₀
      hlevel htime haTime hB hrho hpde hexponents
  have hfactor : ∀ k < m, 0 ≤ factor k := by
    intro k hk
    have hk1m : k + 1 ≤ m := Nat.succ_le_iff.mpr hk
    exact nestedForwardMoserStepFactor_nonneg (I := I) (M := M)
      n g hdim level upperTime k hp₀
        (by simpa only [n] using hexponents k hk)
        (haTime.trans (htime.antitone hk1m))
        (htime (Nat.lt_succ_self k)) hB
  have hP : 0 ≤ P := by
    apply Finset.prod_nonneg
    intro k hk
    exact hfactor k (Finset.mem_range.mp hk)
  have hmono := localizedSpacetimeRpowNorm_mono
    (I := I) (M := M)
      (spatialCutoffBetween rho (level 0) (level 1)) u
      hu.continuous hpos hp₀ hp₀p hmass
      (a := a) (b := upperTime 0)
  have hzero :
      nestedForwardMoserNorm (I := I) (M := M) n
          rho u p₀ a level upperTime 0 ≤
        localizedSpacetimeRpowNorm (I := I) (M := M)
          (spatialCutoffBetween rho (level 0) (level 1)) u
            p a (upperTime 0) := by
    simpa only [nestedForwardMoserNorm, nestedForwardMoserMoment,
      parabolicMoserExponent_zero, zero_mul, zero_add] using hmono
  calc
    nestedForwardMoserNorm (I := I) (M := M) n
          rho u p₀ a level upperTime m ≤
        P * nestedForwardMoserNorm (I := I) (M := M) n
          rho u p₀ a level upperTime 0 := by
      simpa only [P, factor, n] using hiteration
    _ ≤ P * localizedSpacetimeRpowNorm (I := I) (M := M)
          (spatialCutoffBetween rho (level 0) (level 1)) u
            p a (upperTime 0) :=
      mul_le_mul_of_nonneg_left hzero hP
    _ = _ := by rfl

theorem exists_nested_forward_moser_iteration_of_supersolution
    (g : SmoothRiemannianMetric I M)
    (hdim : 2 < (Module.finrank ℝ E : ℝ))
    (rho : SmoothScalar g)
    (u : ℝ → M → ℝ)
    (hu : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun z : ℝ × M => u z.1 z.2))
    (hpos : ∀ t x, 0 < u t x)
    {p q a B : ℝ} (level upperTime : ℕ → ℝ)
    (hp : 0 < p) (hpq : p < q) (hq_one : q < 1)
    (hlevel : StrictMono level) (htime : StrictAnti upperTime)
    (haTime : ∀ k, a ≤ upperTime k) (hB : 0 ≤ B)
    (hrho : ∀ x : M,
      g.inner x
          (gradFun (I := I) g rho.toFun x)
          (gradFun (I := I) g rho.toFun x) ≤ B)
    (hpde : ∀ t ∈ Icc a (upperTime 0), ∀ x : M,
      Δ_g (I := I) g (smoothScalarSlice (I := I) g u hu t).toContMDiffMap x ≤
        deriv (fun s => u s x) t)
    (hmass :
      (localizedSpacetimeMeasure (I := I) (M := M)
        (spatialCutoffBetween rho (level 0) (level 1)) a (upperTime 0)).real
          Set.univ ≤ 1) :
    let n := Module.finrank ℝ E
    ∃ m : ℕ,
      let p₀ := q * parabolicMoserDecay n ^ m
      p₀ < p ∧ p ≤ parabolicMoserGain n * p₀ ∧
        parabolicMoserExponent n p₀ m = q ∧
        nestedForwardMoserNorm (I := I) (M := M) n
            rho u p₀ a level upperTime m ≤
          (∏ k ∈ Finset.range m,
            nestedForwardMoserStepFactor (I := I) (M := M)
              n g hdim B p₀ a level upperTime k) *
            localizedSpacetimeRpowNorm (I := I) (M := M)
              (spatialCutoffBetween rho (level 0) (level 1)) u
                p a (upperTime 0) := by
  let n := Module.finrank ℝ E
  letI : NeZero n := by
    refine ⟨Nat.ne_of_gt ?_⟩
    exact_mod_cast (by linarith : 0 < (n : ℝ))
  obtain ⟨m, hp₀p, hpp₀⟩ :=
    exists_parabolic_moser_iteration_depth n hp hpq
  let p₀ := q * parabolicMoserDecay n ^ m
  have hq_pos : 0 < q := hp.trans hpq
  have hp₀ : 0 < p₀ :=
    mul_pos hq_pos (pow_pos (parabolicMoserDecay_pos n) m)
  have htarget : parabolicMoserExponent n p₀ m = q := by
    simpa only [p₀] using parabolicMoserExponent_decay_mul_self n q m
  have hexponents : ∀ k < m, parabolicMoserExponent n p₀ k < 1 := by
    intro k hk
    calc
      parabolicMoserExponent n p₀ k < parabolicMoserExponent n p₀ m :=
        parabolicMoserExponent_strictMono n hp₀ hk
      _ = q := htarget
      _ < 1 := hq_one
  have hbound := nestedForwardMoserNorm_le_rpowNorm_of_supersolution
    (I := I) (M := M) g hdim rho u hu hpos level upperTime m hp₀
      hp₀p.le hlevel htime (haTime m) hB hrho hpde hexponents hmass
  refine ⟨m, ?_⟩
  simpa only [p₀, n] using ⟨hp₀p, hpp₀, htarget, hbound⟩

omit [I.Boundaryless] [CompactSpace M] in
theorem forwardMoserLocalizedMass_nonneg
    (n : ℕ) {g : SmoothRiemannianMetric I M} (rho : SmoothScalar g)
    (u : ℝ → M → ℝ) {p₀ a τ b : ℝ}
    (haτ : a ≤ τ) (hτb : τ < b) (hu : ∀ t x, 0 ≤ u t x) (k : ℕ) :
    0 ≤ forwardMoserLocalizedMass (I := I) (M := M) n rho u p₀ a τ b k := by
  apply intervalIntegral.integral_nonneg
  · exact haτ.trans (moserUpperTimeLevel_lt hτb k).le
  · intro t _
    exact integral_nonneg fun x => mul_nonneg (sq_nonneg _)
      (Real.rpow_nonneg (hu t x) _)

omit [I.Boundaryless] in
theorem forwardMoserLocalizedMass_succ_le
    (n : ℕ) [NeZero n]
    {g : SmoothRiemannianMetric I M} (rho : SmoothScalar g)
    (u : ℝ → M → ℝ)
    (hu : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun z : ℝ × M => u z.1 z.2))
    (hpos : ∀ t x, 0 < u t x)
    {p₀ a τ b : ℝ} (haτ : a ≤ τ) (hτb : τ < b) (k : ℕ) :
    forwardMoserLocalizedMass (I := I) (M := M) n rho u p₀ a τ b (k + 1) ≤
      ∫ t in a..moserUpperTimeLevel τ b (k + 1),
        ∫ x,
          |(spatialMoserCutoff rho (2 * k + 1)).toFun x *
              u t x ^ (parabolicMoserExponent n p₀ k / 2)| ^
            (2 + 4 / (n : ℝ))
          ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
  let μ := riemannianVolumeMeasure (I := I) (M := M) g
  let upper := moserUpperTimeLevel τ b (k + 1)
  let p := parabolicMoserExponent n p₀ (k + 1)
  let critical := 2 + 4 / (n : ℝ)
  let left : ℝ → ℝ := fun t =>
    ∫ x, (spatialMoserCutoff rho (2 * (k + 1))).toFun x ^ 2 * u t x ^ p ∂μ
  let right : ℝ → ℝ := fun t =>
    ∫ x, |(spatialMoserCutoff rho (2 * k + 1)).toFun x *
      u t x ^ (parabolicMoserExponent n p₀ k / 2)| ^ critical ∂μ
  letI : IsFiniteMeasure μ := by
    dsimp only [μ]
    exact riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace
      (I := I) (M := M) g
  have hn : 0 < (n : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
  have hcritical : 0 ≤ critical := by
    dsimp only [critical]
    positivity
  have hleft_joint : Continuous (fun z : ℝ × M =>
      (spatialMoserCutoff rho (2 * (k + 1))).toFun z.2 ^ 2 * u z.1 z.2 ^ p) :=
    ((spatialMoserCutoff rho (2 * (k + 1))).smooth.continuous.comp
      continuous_snd).pow 2 |>.mul
        (hu.continuous.rpow_const (fun z => Or.inl (hpos z.1 z.2).ne'))
  have hright_base : Continuous (fun z : ℝ × M =>
      |(spatialMoserCutoff rho (2 * k + 1)).toFun z.2 *
        u z.1 z.2 ^ (parabolicMoserExponent n p₀ k / 2)|) :=
    (((spatialMoserCutoff rho (2 * k + 1)).smooth.continuous.comp continuous_snd).mul
      (hu.continuous.rpow_const (fun z => Or.inl (hpos z.1 z.2).ne'))).abs
  have hright_joint : Continuous (fun z : ℝ × M =>
      |(spatialMoserCutoff rho (2 * k + 1)).toFun z.2 *
        u z.1 z.2 ^ (parabolicMoserExponent n p₀ k / 2)| ^ critical) :=
    hright_base.rpow_const (fun _ => Or.inr hcritical)
  have haupper : a ≤ upper :=
    haτ.trans (moserUpperTimeLevel_lt hτb (k + 1)).le
  have hleft_cont : ContinuousOn left (Icc a upper) := by
    have h := DifferentialGeometry.Integral.Measure.integral_contOn_cpt
      (K := Icc a upper) μ
      (fun t x => (spatialMoserCutoff rho (2 * (k + 1))).toFun x ^ 2 * u t x ^ p)
      isCompact_Icc hleft_joint.continuousOn
    simpa only [left] using h
  have hright_cont : ContinuousOn right (Icc a upper) := by
    have h := DifferentialGeometry.Integral.Measure.integral_contOn_cpt
      (K := Icc a upper) μ
      (fun t x => |(spatialMoserCutoff rho (2 * k + 1)).toFun x *
        u t x ^ (parabolicMoserExponent n p₀ k / 2)| ^ critical)
      isCompact_Icc hright_joint.continuousOn
    simpa only [right] using h
  have hleft_int : IntervalIntegrable left volume a upper := by
    apply ContinuousOn.intervalIntegrable
    simpa [uIcc_of_le haupper] using hleft_cont
  have hright_int : IntervalIntegrable right volume a upper := by
    apply ContinuousOn.intervalIntegrable
    simpa [uIcc_of_le haupper] using hright_cont
  have hpoint : ∀ t ∈ Icc a upper, left t ≤ right t := by
    intro t _
    have hu_slice : Continuous (u t) :=
      hu.continuous.comp (continuous_const.prodMk continuous_id)
    have hleft_slice : Continuous (fun x : M =>
        (spatialMoserCutoff rho (2 * (k + 1))).toFun x ^ 2 * u t x ^ p) :=
      ((spatialMoserCutoff rho (2 * (k + 1))).smooth.continuous.pow 2).mul
        (hu_slice.rpow_const (fun x => Or.inl (hpos t x).ne'))
    have hright_slice : Continuous (fun x : M =>
        |(spatialMoserCutoff rho (2 * k + 1)).toFun x *
          u t x ^ (parabolicMoserExponent n p₀ k / 2)| ^ critical) :=
      (((spatialMoserCutoff rho (2 * k + 1)).smooth.continuous.mul
        (hu_slice.rpow_const (fun x => Or.inl (hpos t x).ne'))).abs).rpow_const
          (fun _ => Or.inr hcritical)
    apply integral_mono
      (hleft_slice.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
      (hright_slice.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
    intro x
    have heta := spatialMoserCutoff_add_two_sq_le_rpow
      rho (2 * k) x critical
    have hu_pow : 0 ≤ u t x ^ p := Real.rpow_nonneg (hpos t x).le p
    have hidentity := abs_mul_rpow_half_critical n
      (spatialMoserCutoff_mem_Icc rho (2 * k + 1) x).1 (hpos t x) k
      (p₀ := p₀)
    change
      (spatialMoserCutoff rho (2 * (k + 1))).toFun x ^ 2 * u t x ^ p ≤
        |(spatialMoserCutoff rho (2 * k + 1)).toFun x *
          u t x ^ (parabolicMoserExponent n p₀ k / 2)| ^ critical
    rw [show 2 * (k + 1) = 2 * k + 2 by omega]
    calc
      _ ≤ (spatialMoserCutoff rho (2 * k + 1)).toFun x ^ critical *
          u t x ^ p := mul_le_mul_of_nonneg_right heta hu_pow
      _ = _ := by simpa only [p, critical] using hidentity.symm
  have htime := intervalIntegral.integral_mono_on haupper hleft_int hright_int hpoint
  simpa only [forwardMoserLocalizedMass, left, right, upper, p, critical] using htime

theorem forwardMoserLocalizedMass_succ_le_of_supersolution
    (g : SmoothRiemannianMetric I M)
    (hdim : 2 < (Module.finrank ℝ E : ℝ))
    (rho : SmoothScalar g)
    (u : ℝ → M → ℝ)
    (hu : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun z : ℝ × M => u z.1 z.2))
    (hpos : ∀ t x, 0 < u t x)
    {p₀ a τ b : ℝ} (hp₀ : 0 < p₀) (haτ : a ≤ τ) (hτb : τ < b)
    (hpde : ∀ t ∈ Icc a b, ∀ x : M,
      Δ_g (I := I) g (smoothScalarSlice (I := I) g u hu t).toContMDiffMap x ≤
        deriv (fun s => u s x) t)
    (k : ℕ)
    (hexponent_one :
      parabolicMoserExponent (Module.finrank ℝ E) p₀ k < 1) :
    forwardMoserLocalizedMass (I := I) (M := M) (Module.finrank ℝ E)
        rho u p₀ a τ b (k + 1) ≤
      localizedSobolevConstant (I := I) (M := M) g hdim *
        (((moserUpperTimeLevel τ b (k + 1) - a + 1) *
            positiveRpowCommonEnergyBound
              (parabolicMoserExponent (Module.finrank ℝ E) p₀ k)
              (moserUpperTimeLevel τ b (k + 1))
              (moserUpperTimeLevel τ b k)
              (spatialMoserCutoffGradientConstant (I := I) g rho * 4 ^ (2 * k))
              (forwardMoserLocalizedMass (I := I) (M := M) (Module.finrank ℝ E)
                rho u p₀ a τ b k) +
          (spatialMoserCutoffGradientConstant (I := I) g rho * 4 ^ (2 * k)) *
            forwardMoserLocalizedMass (I := I) (M := M) (Module.finrank ℝ E)
              rho u p₀ a τ b k) ^
          parabolicMoserGain (Module.finrank ℝ E)) := by
  let n := Module.finrank ℝ E
  letI : NeZero n := by
    refine ⟨Nat.ne_of_gt ?_⟩
    exact_mod_cast (by linarith : 0 < (n : ℝ))
  let q := parabolicMoserExponent n p₀ k
  let inner := spatialMoserCutoff rho (2 * k + 1)
  let outer := spatialMoserCutoff rho (2 * k)
  let t₁ := moserUpperTimeLevel τ b (k + 1)
  let t₂ := moserUpperTimeLevel τ b k
  let K := spatialMoserCutoffGradientConstant (I := I) g rho * 4 ^ (2 * k)
  let L := forwardMoserLocalizedMass (I := I) (M := M) n rho u p₀ a τ b k
  have hq_pos : 0 < q := parabolicMoserExponent_pos n hp₀ k
  have hat₁ : a ≤ t₁ := haτ.trans (moserUpperTimeLevel_lt hτb (k + 1)).le
  have ht₁t₂ : t₁ < t₂ := moserUpperTimeLevel_succ_lt hτb k
  have hK : 0 ≤ K := mul_nonneg
    (spatialMoserCutoffGradientConstant_nonneg (I := I) g rho)
    (pow_nonneg (by norm_num) _)
  have hL : 0 ≤ L :=
    forwardMoserLocalizedMass_nonneg n rho u haτ hτb
      (fun t x => (hpos t x).le) k
  have hbridge := forwardMoserLocalizedMass_succ_le n rho u hu hpos
    (p₀ := p₀) (a := a) (τ := τ) (b := b) haτ hτb k
  have hreverse := positive_rpow_reverse_holder_step
    (I := I) (M := M) g hdim inner outer u hu hpos
    hq_pos (by simpa only [q, n] using hexponent_one)
    hat₁ ht₁t₂ hK hL
    (fun t ht x => hpde t
      ⟨ht.1, ht.2.trans (moserUpperTimeLevel_le hτb k)⟩ x)
    (fun x => by
      simpa only [inner, outer] using spatialMoserCutoff_succ_sq_le rho (2 * k) x)
    (fun x => by
      simpa only [inner, outer, K] using
        spatialMoserCutoff_gradient_le (I := I) g rho (2 * k) x)
    (by
      have heq :
          (∫ t in a..t₂,
            localizedL2Mass (I := I) (M := M) outer
              (smoothScalarSlice (I := I) g (fun s x => u s x ^ (q / 2))
                (contMDiff_rpow_of_pos hu hpos (q / 2)) t)) = L := by
        dsimp only [L, t₂]
        rw [forwardMoserLocalizedMass]
        apply intervalIntegral.integral_congr
        intro t _
        simpa only [outer, q] using localizedL2Mass_rpow_half
          (I := I) (M := M) g (spatialMoserCutoff rho (2 * k))
            u hu hpos (parabolicMoserExponent n p₀ k) t
      exact heq.le)
  calc
    forwardMoserLocalizedMass (I := I) (M := M) (Module.finrank ℝ E)
          rho u p₀ a τ b (k + 1) ≤
        ∫ t in a..t₁,
          ∫ x, |inner.toFun x * u t x ^ (q / 2)| ^
            (2 + 4 / (n : ℝ))
            ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
      simpa only [n, q, inner, t₁] using hbridge
    _ ≤ localizedSobolevConstant (I := I) (M := M) g hdim *
        (((t₁ - a + 1) * positiveRpowCommonEnergyBound q t₁ t₂ K L +
          K * L) ^ parabolicMoserGain n) := by
      simpa only [n, parabolicMoserGain] using hreverse
    _ = _ := by
      rfl

theorem forwardMoserLocalizedMass_succ_le_homogeneous_of_supersolution
    (g : SmoothRiemannianMetric I M)
    (hdim : 2 < (Module.finrank ℝ E : ℝ))
    (rho : SmoothScalar g)
    (u : ℝ → M → ℝ)
    (hu : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun z : ℝ × M => u z.1 z.2))
    (hpos : ∀ t x, 0 < u t x)
    {p₀ a τ b : ℝ} (hp₀ : 0 < p₀) (haτ : a ≤ τ) (hτb : τ < b)
    (hpde : ∀ t ∈ Icc a b, ∀ x : M,
      Δ_g (I := I) g (smoothScalarSlice (I := I) g u hu t).toContMDiffMap x ≤
        deriv (fun s => u s x) t)
    (k : ℕ)
    (hexponent_one :
      parabolicMoserExponent (Module.finrank ℝ E) p₀ k < 1) :
    forwardMoserLocalizedMass (I := I) (M := M) (Module.finrank ℝ E)
        rho u p₀ a τ b (k + 1) ≤
      localizedSobolevConstant (I := I) (M := M) g hdim *
        (forwardMoserStepCoefficient
            (parabolicMoserExponent (Module.finrank ℝ E) p₀ k) a
            (moserUpperTimeLevel τ b (k + 1)) (moserUpperTimeLevel τ b k)
            (spatialMoserCutoffGradientConstant (I := I) g rho * 4 ^ (2 * k)) *
          forwardMoserLocalizedMass (I := I) (M := M) (Module.finrank ℝ E)
            rho u p₀ a τ b k) ^
          parabolicMoserGain (Module.finrank ℝ E) := by
  have h := forwardMoserLocalizedMass_succ_le_of_supersolution
    (I := I) (M := M) g hdim rho u hu hpos hp₀ haτ hτb hpde k hexponent_one
  convert h using 1
  unfold forwardMoserStepCoefficient positiveRpowCommonEnergyBound
    positiveRpowEnergyBound
  ring_nf

theorem forwardMoserNormalizedMass_succ_le_of_supersolution
    (g : SmoothRiemannianMetric I M)
    (hdim : 2 < (Module.finrank ℝ E : ℝ))
    (rho : SmoothScalar g)
    (u : ℝ → M → ℝ)
    (hu : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun z : ℝ × M => u z.1 z.2))
    (hpos : ∀ t x, 0 < u t x)
    {p₀ a τ b : ℝ} (hp₀ : 0 < p₀) (haτ : a ≤ τ) (hτb : τ < b)
    (hpde : ∀ t ∈ Icc a b, ∀ x : M,
      Δ_g (I := I) g (smoothScalarSlice (I := I) g u hu t).toContMDiffMap x ≤
        deriv (fun s => u s x) t)
    (k : ℕ)
    (hexponent_one :
      parabolicMoserExponent (Module.finrank ℝ E) p₀ k < 1) :
    forwardMoserNormalizedMass (I := I) (M := M) (Module.finrank ℝ E)
        rho u p₀ a τ b (k + 1) ≤
      forwardMoserStepFactor (I := I) (M := M) (Module.finrank ℝ E)
        g hdim rho p₀ a τ b k *
        forwardMoserNormalizedMass (I := I) (M := M) (Module.finrank ℝ E)
          rho u p₀ a τ b k := by
  let n := Module.finrank ℝ E
  letI : NeZero n := by
    refine ⟨Nat.ne_of_gt ?_⟩
    exact_mod_cast (by linarith : 0 < (n : ℝ))
  let q := parabolicMoserExponent n p₀ k
  let K := spatialMoserCutoffGradientConstant (I := I) g rho * 4 ^ (2 * k)
  let coefficient := forwardMoserStepCoefficient q a
    (moserUpperTimeLevel τ b (k + 1)) (moserUpperTimeLevel τ b k) K
  let L := forwardMoserLocalizedMass (I := I) (M := M) n rho u p₀ a τ b k
  let L' := forwardMoserLocalizedMass (I := I) (M := M) n rho u p₀ a τ b (k + 1)
  have hq_pos : 0 < q := parabolicMoserExponent_pos n hp₀ k
  have hK : 0 ≤ K := mul_nonneg
    (spatialMoserCutoffGradientConstant_nonneg (I := I) g rho)
    (pow_nonneg (by norm_num) _)
  have hcoefficient : 0 ≤ coefficient :=
    forwardMoserStepCoefficient_nonneg hq_pos
      (by simpa only [q, n] using hexponent_one)
      (haτ.trans (moserUpperTimeLevel_lt hτb (k + 1)).le)
      (moserUpperTimeLevel_succ_lt hτb k) hK
  have hL : 0 ≤ L := forwardMoserLocalizedMass_nonneg n rho u haτ hτb
    (fun t x => (hpos t x).le) k
  have hL' : 0 ≤ L' := forwardMoserLocalizedMass_nonneg n rho u haτ hτb
    (fun t x => (hpos t x).le) (k + 1)
  have hstep := forwardMoserLocalizedMass_succ_le_homogeneous_of_supersolution
    (I := I) (M := M) g hdim rho u hu hpos hp₀ haτ hτb hpde k hexponent_one
  have hnormalized := normalized_exponent_gain_step
    hL hL' (localizedSobolevConstant_nonneg (I := I) (M := M) g hdim)
    hcoefficient (parabolicMoserGain_pos n) hq_pos
    (by simpa only [L, L', coefficient, q, K, n] using hstep)
  have hexponent : parabolicMoserGain n * q =
      parabolicMoserExponent n p₀ (k + 1) := by
    simpa only [q] using (parabolicMoserExponent_succ n p₀ k).symm
  simpa only [forwardMoserNormalizedMass, forwardMoserStepFactor,
    n, q, K, coefficient, L, L', hexponent, mul_assoc] using hnormalized

theorem forwardMoserStepFactor_nonneg
    (n : ℕ) [NeZero n] (g : SmoothRiemannianMetric I M)
    (hdim : 2 < (Module.finrank ℝ E : ℝ))
    (rho : SmoothScalar g) {p₀ a τ b : ℝ}
    (hp₀ : 0 < p₀) (haτ : a ≤ τ) (hτb : τ < b) (k : ℕ)
    (hexponent_one : parabolicMoserExponent n p₀ k < 1) :
    0 ≤ forwardMoserStepFactor (I := I) (M := M) n g hdim rho p₀ a τ b k := by
  have hK : 0 ≤ spatialMoserCutoffGradientConstant (I := I) g rho * 4 ^ (2 * k) :=
    mul_nonneg (spatialMoserCutoffGradientConstant_nonneg (I := I) g rho)
      (pow_nonneg (by norm_num) _)
  have hcoefficient := forwardMoserStepCoefficient_nonneg
    (parabolicMoserExponent_pos n hp₀ k) hexponent_one
    (haτ.trans (moserUpperTimeLevel_lt hτb (k + 1)).le)
    (moserUpperTimeLevel_succ_lt hτb k) hK
  exact mul_nonneg (Real.rpow_nonneg
    (localizedSobolevConstant_nonneg (I := I) (M := M) g hdim) _)
    (Real.rpow_nonneg hcoefficient _)

theorem forwardMoserNormalizedMass_le_of_supersolution
    (g : SmoothRiemannianMetric I M)
    (hdim : 2 < (Module.finrank ℝ E : ℝ))
    (rho : SmoothScalar g)
    (u : ℝ → M → ℝ)
    (hu : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun z : ℝ × M => u z.1 z.2))
    (hpos : ∀ t x, 0 < u t x)
    {p₀ a τ b : ℝ} (hp₀ : 0 < p₀) (haτ : a ≤ τ) (hτb : τ < b)
    (hpde : ∀ t ∈ Icc a b, ∀ x : M,
      Δ_g (I := I) g (smoothScalarSlice (I := I) g u hu t).toContMDiffMap x ≤
        deriv (fun s => u s x) t)
    (m : ℕ)
    (hexponents : ∀ k < m,
      parabolicMoserExponent (Module.finrank ℝ E) p₀ k < 1) :
    forwardMoserNormalizedMass (I := I) (M := M) (Module.finrank ℝ E)
        rho u p₀ a τ b m ≤
      (∏ k ∈ Finset.range m,
        forwardMoserStepFactor (I := I) (M := M) (Module.finrank ℝ E)
          g hdim rho p₀ a τ b k) *
        forwardMoserNormalizedMass (I := I) (M := M) (Module.finrank ℝ E)
          rho u p₀ a τ b 0 := by
  let n := Module.finrank ℝ E
  letI : NeZero n := by
    refine ⟨Nat.ne_of_gt ?_⟩
    exact_mod_cast (by linarith : 0 < (n : ℝ))
  let X : ℕ → ℝ := fun k =>
    forwardMoserNormalizedMass (I := I) (M := M) n rho u p₀ a τ b k
  let factor : ℕ → ℝ := fun k =>
    forwardMoserStepFactor (I := I) (M := M) n g hdim rho p₀ a τ b k
  have hfactor : ∀ k < m, 0 ≤ factor k := by
    intro k hk
    exact forwardMoserStepFactor_nonneg (I := I) (M := M) n g hdim rho
      hp₀ haτ hτb k (by simpa only [n] using hexponents k hk)
  have hstep : ∀ k < m, X (k + 1) ≤ factor k * X k := by
    intro k hk
    exact forwardMoserNormalizedMass_succ_le_of_supersolution
      (I := I) (M := M) g hdim rho u hu hpos hp₀ haτ hτb hpde k
      (by simpa only [n] using hexponents k hk)
  simpa only [X, factor, n] using
    (finite_multiplicative_iteration m hfactor hstep)

theorem forward_moser_iteration_of_supersolution
    (g : SmoothRiemannianMetric I M)
    (hdim : 2 < (Module.finrank ℝ E : ℝ))
    (rho : SmoothScalar g)
    (u : ℝ → M → ℝ)
    (hu : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun z : ℝ × M => u z.1 z.2))
    (hpos : ∀ t x, 0 < u t x)
    {q a τ b : ℝ} (hq_pos : 0 < q) (hq_one : q < 1)
    (haτ : a ≤ τ) (hτb : τ < b)
    (hpde : ∀ t ∈ Icc a b, ∀ x : M,
      Δ_g (I := I) g (smoothScalarSlice (I := I) g u hu t).toContMDiffMap x ≤
        deriv (fun s => u s x) t)
    (m : ℕ) :
    let n := Module.finrank ℝ E
    let p₀ := q * parabolicMoserDecay n ^ m
    forwardMoserLocalizedMass (I := I) (M := M) n rho u p₀ a τ b m ^ (1 / q) ≤
      (∏ k ∈ Finset.range m,
        forwardMoserStepFactor (I := I) (M := M) n
          g hdim rho p₀ a τ b k) *
        forwardMoserLocalizedMass (I := I) (M := M) n
          rho u p₀ a τ b 0 ^ (1 / p₀) := by
  let n := Module.finrank ℝ E
  letI : NeZero n := by
    refine ⟨Nat.ne_of_gt ?_⟩
    exact_mod_cast (by linarith : 0 < (n : ℝ))
  let p₀ := q * parabolicMoserDecay n ^ m
  have hp₀ : 0 < p₀ := mul_pos hq_pos (pow_pos (parabolicMoserDecay_pos n) m)
  have hexponents : ∀ k < m, parabolicMoserExponent n p₀ k < 1 := by
    intro k hk
    calc
      parabolicMoserExponent n p₀ k < parabolicMoserExponent n p₀ m :=
        parabolicMoserExponent_strictMono n hp₀ hk
      _ = q := by
        simpa only [p₀] using parabolicMoserExponent_decay_mul_self n q m
      _ < 1 := hq_one
  have h := forwardMoserNormalizedMass_le_of_supersolution
    (I := I) (M := M) g hdim rho u hu hpos hp₀ haτ hτb hpde m hexponents
  simpa only [forwardMoserNormalizedMass, parabolicMoserExponent_zero,
    p₀, n, parabolicMoserExponent_decay_mul_self] using h

end DifferentialGeometry.Analysis.Parabolic.Moser

end
