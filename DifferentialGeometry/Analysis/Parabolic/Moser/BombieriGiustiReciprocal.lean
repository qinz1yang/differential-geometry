import DifferentialGeometry.Analysis.Parabolic.Moser.BombieriGiustiCylinder
import DifferentialGeometry.Analysis.Parabolic.Moser.BombieriGiusti
import DifferentialGeometry.Analysis.Parabolic.Moser.LocalBoundedness

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

def bombieriGiustiLatePivot (τ c : ℝ) (k : ℕ) : ℝ :=
  (bombieriGiustiDescendingLevel τ c (k + 1) +
    bombieriGiustiDescendingLevel τ c k) / 2

def canonicalLateBombieriGiustiReverseCost
    (g : SmoothRiemannianMetric I M)
    (hdim : 2 < (Module.finrank ℝ E : ℝ))
    (rho : SmoothScalar g)
    (τ c d D lower upper : ℝ) (k : ℕ) : ℝ :=
  moserLocalBoundFactor (I := I) (M := M) g hdim
      (bombieriGiustiReciprocalLocalizer rho lower upper k) 2
      (bombieriGiustiDescendingLevel τ c (k + 1))
      (bombieriGiustiLatePivot τ c k)
      (bombieriGiustiIncreasingLevel d D (k + 1)) ^ (2 : ℝ)

def canonicalLateBombieriGiustiStepPolynomialCoefficient
    {g : SmoothRiemannianMetric I M} (rho : SmoothScalar g)
    (τ c D lower upper : ℝ) : ℝ :=
  let K := (36 / (upper - lower) ^ 2) *
    spatialMoserCutoffGradientConstant (I := I) g rho
  max 1 ((D - τ + 1) *
    (8 * timeCutoffDerivConstant / (c - τ) + 4 * K) + K)

omit [SigmaCompactSpace M] in
theorem canonicalLateBombieriGiustiStepConstant_le_polynomial
    (g : SmoothRiemannianMetric I M) (rho : SmoothScalar g)
    {τ c d D lower upper : ℝ}
    (hτc : τ < c) (hcd : c ≤ d) (hdD : d < D)
    (hlowerUpper : lower < upper) (k : ℕ) :
    moserStepConstant (I := I)
        (bombieriGiustiReciprocalLocalizer rho lower upper k)
        (bombieriGiustiDescendingLevel τ c (k + 1))
        (bombieriGiustiLatePivot τ c k)
        (bombieriGiustiIncreasingLevel d D (k + 1)) ≤
      canonicalLateBombieriGiustiStepPolynomialCoefficient (I := I)
          rho τ c D lower upper * (k + 1 : ℝ) ^ 4 := by
  let m : ℝ := k + 1
  let gap := bombieriGiustiDescendingLevel τ c k -
    bombieriGiustiDescendingLevel τ c (k + 1)
  let Kbase := spatialMoserCutoffGradientConstant (I := I) g rho
  let K := (36 / (upper - lower) ^ 2) * Kbase
  let T := 8 * timeCutoffDerivConstant / (c - τ)
  have hm : 1 ≤ m := by norm_num [m]
  have hm_nonneg : 0 ≤ m := zero_le_one.trans hm
  have hm_four : 1 ≤ m ^ 4 := one_le_pow₀ hm
  have hm_sq_four : m ^ 2 ≤ m ^ 4 := by
    have hm_le_sq : m ≤ m ^ 2 := by
      nlinarith [mul_nonneg hm_nonneg (sub_nonneg.mpr hm)]
    have hpow := pow_le_pow_left₀ hm_nonneg hm_le_sq 2
    nlinarith
  have hgap : 0 < gap := by
    dsimp only [gap]
    exact sub_pos.mpr
      (bombieriGiustiDescendingLevel_strictAnti hτc (Nat.lt_succ_self k))
  have hKbase : 0 ≤ Kbase :=
    spatialMoserCutoffGradientConstant_nonneg (I := I) g rho
  have hK : 0 ≤ K := mul_nonneg
    (div_nonneg (by norm_num) (sq_nonneg _)) hKbase
  have hT : 0 ≤ T := div_nonneg
    (mul_nonneg (by norm_num) timeCutoffDerivConstant_nonneg)
    (sub_pos.mpr hτc).le
  have hlocalizer : spatialMoserCutoffGradientConstant (I := I) g
      (bombieriGiustiReciprocalLocalizer rho lower upper k) ≤
      K * m ^ 4 := by
    have hscale :=
      spatialMoserCutoffGradientConstant_reciprocalLocalizer_le
        g rho lower upper k
    have hgapSq := bombieriGiustiDescendingLevel_odd_gap_inv_sq_le
      hlowerUpper k
    calc
      _ ≤ (bombieriGiustiDescendingLevel lower upper (2 * k + 1) -
            bombieriGiustiDescendingLevel lower upper (2 * k + 2))⁻¹ ^ 2 *
          Kbase := by simpa only [Kbase] using hscale
      _ ≤ ((36 / (upper - lower) ^ 2) * m ^ 4) * Kbase :=
        mul_le_mul_of_nonneg_right (by simpa only [m] using hgapSq) hKbase
      _ = K * m ^ 4 := by
        dsimp only [K]
        ring
  have hpivot : bombieriGiustiLatePivot τ c k -
      bombieriGiustiDescendingLevel τ c (k + 1) = gap / 2 := by
    dsimp only [bombieriGiustiLatePivot, gap]
    ring
  have htime : 2 * timeCutoffDerivConstant /
      (bombieriGiustiLatePivot τ c k -
        bombieriGiustiDescendingLevel τ c (k + 1)) ≤ T * m ^ 4 := by
    have hgapInv := bombieriGiustiDescendingLevel_gap_inv_le hτc k
    calc
      2 * timeCutoffDerivConstant /
          (bombieriGiustiLatePivot τ c k -
            bombieriGiustiDescendingLevel τ c (k + 1)) =
          4 * timeCutoffDerivConstant * gap⁻¹ := by
        rw [hpivot]
        field_simp [hgap.ne']
        ring
      _ ≤ 4 * timeCutoffDerivConstant *
          ((2 / (c - τ)) * m ^ 2) :=
        mul_le_mul_of_nonneg_left (by simpa only [gap, m] using hgapInv)
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
  have hinside :
      2 * timeCutoffDerivConstant /
          (bombieriGiustiLatePivot τ c k -
            bombieriGiustiDescendingLevel τ c (k + 1)) +
        4 * spatialMoserCutoffGradientConstant (I := I) g
          (bombieriGiustiReciprocalLocalizer rho lower upper k) ≤
      (T + 4 * K) * m ^ 4 := by
    calc
      _ ≤ T * m ^ 4 + 4 * (K * m ^ 4) :=
        add_le_add htime (mul_le_mul_of_nonneg_left hlocalizer (by norm_num))
      _ = (T + 4 * K) * m ^ 4 := by ring
  have hinside_nonneg : 0 ≤
      2 * timeCutoffDerivConstant /
          (bombieriGiustiLatePivot τ c k -
            bombieriGiustiDescendingLevel τ c (k + 1)) +
        4 * spatialMoserCutoffGradientConstant (I := I) g
          (bombieriGiustiReciprocalLocalizer rho lower upper k) := by
    apply add_nonneg
    · exact div_nonneg
        (mul_nonneg (by norm_num) timeCutoffDerivConstant_nonneg)
        (by rw [hpivot]; positivity)
    · exact mul_nonneg (by norm_num)
        (spatialMoserCutoffGradientConstant_nonneg (I := I) g _)
  unfold moserStepConstant
  let raw := (D - τ + 1) * (T + 4 * K) + K
  have hraw :
      (bombieriGiustiIncreasingLevel d D (k + 1) -
          bombieriGiustiDescendingLevel τ c (k + 1) + 1) *
          (2 * timeCutoffDerivConstant /
              (bombieriGiustiLatePivot τ c k -
                bombieriGiustiDescendingLevel τ c (k + 1)) +
            4 * spatialMoserCutoffGradientConstant (I := I) g
              (bombieriGiustiReciprocalLocalizer rho lower upper k)) +
        spatialMoserCutoffGradientConstant (I := I) g
          (bombieriGiustiReciprocalLocalizer rho lower upper k) ≤
        raw * m ^ 4 := by
    calc
      _ ≤ (D - τ + 1) * ((T + 4 * K) * m ^ 4) + K * m ^ 4 := by
        exact add_le_add
          (mul_le_mul houter hinside
            hinside_nonneg houter_bound_nonneg)
          hlocalizer
      _ = raw * m ^ 4 := by
        dsimp only [raw]
        ring
  have hcoefficient : raw ≤
      canonicalLateBombieriGiustiStepPolynomialCoefficient (I := I)
        rho τ c D lower upper := by
    exact le_max_right _ _
  exact hraw.trans (mul_le_mul_of_nonneg_right hcoefficient
    (pow_nonneg hm_nonneg 4))

theorem one_le_canonicalLateBombieriGiustiReverseCost
    (g : SmoothRiemannianMetric I M)
    (hdim : 2 < (Module.finrank ℝ E : ℝ))
    (rho : SmoothScalar g)
    (τ c d D lower upper : ℝ) (k : ℕ) :
    1 ≤ canonicalLateBombieriGiustiReverseCost (I := I) (M := M)
      g hdim rho τ c d D lower upper k := by
  unfold canonicalLateBombieriGiustiReverseCost
  exact Real.one_le_rpow
    (one_le_moserLocalBoundFactor g hdim
      (bombieriGiustiReciprocalLocalizer rho lower upper k)
      (by norm_num) _ _ _)
    (by norm_num)

theorem exists_polynomial_bound_canonicalLateBombieriGiustiReverseCost
    (g : SmoothRiemannianMetric I M)
    (hdim : 2 < (Module.finrank ℝ E : ℝ))
    (rho : SmoothScalar g)
    {τ c d D lower upper : ℝ}
    (hτc : τ < c) (hcd : c ≤ d) (hdD : d < D)
    (hlowerUpper : lower < upper) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ k : ℕ,
      canonicalLateBombieriGiustiReverseCost (I := I) (M := M)
          g hdim rho τ c d D lower upper k ≤
        C * (k + 1 : ℝ) ^ (2 * (Module.finrank ℝ E + 2)) := by
  let n := Module.finrank ℝ E
  letI : NeZero n := by
    refine ⟨Nat.ne_of_gt ?_⟩
    exact_mod_cast (by linarith : 0 < (n : ℝ))
  let theta := parabolicMoserDecay n
  let S := max 1 (localizedSobolevConstant (I := I) (M := M) g hdim)
  let Abar := canonicalLateBombieriGiustiStepPolynomialCoefficient
    (I := I) rho τ c D lower upper
  let base := (theta * Real.log S + Real.log Abar) / (1 - theta) +
    Real.log 16 * (theta / (1 - theta) ^ 2)
  let C := Real.exp base
  have htheta : 0 ≤ theta := (parabolicMoserDecay_pos n).le
  have hdenom : 0 < 1 - theta := sub_pos.mpr (parabolicMoserDecay_lt_one n)
  have hS : 1 ≤ S := le_max_left _ _
  have hAbar : 1 ≤ Abar := by
    exact le_max_left _ _
  have hbase : 0 ≤ base := by
    dsimp only [base]
    exact add_nonneg
      (div_nonneg
        (add_nonneg (mul_nonneg htheta (Real.log_nonneg hS))
          (Real.log_nonneg hAbar)) hdenom.le)
      (mul_nonneg (Real.log_nonneg (by norm_num))
        (div_nonneg htheta (sq_nonneg _)))
  refine ⟨C, ?_, ?_⟩
  · exact (Real.one_le_exp_iff).2 hbase
  · intro k
    let m : ℝ := k + 1
    let Ak := max 1 (moserStepConstant (I := I)
      (bombieriGiustiReciprocalLocalizer rho lower upper k)
      (bombieriGiustiDescendingLevel τ c (k + 1))
      (bombieriGiustiLatePivot τ c k)
      (bombieriGiustiIncreasingLevel d D (k + 1)))
    have hm : 0 < m := by positivity
    have hAk : 1 ≤ Ak := le_max_left _ _
    have hAk_bound : Ak ≤ Abar * m ^ 4 := by
      apply max_le
      · calc
          1 ≤ m ^ 4 := one_le_pow₀ (by norm_num [m])
          _ ≤ Abar * m ^ 4 := by
            exact le_mul_of_one_le_left (pow_nonneg hm.le 4) hAbar
      · simpa only [Abar, m] using
          canonicalLateBombieriGiustiStepConstant_le_polynomial
            g rho hτc hcd hdD hlowerUpper k
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
    have hscaled : Real.log Ak * (1 - theta)⁻¹ ≤
        (Real.log Abar + 4 * Real.log m) * (1 - theta)⁻¹ :=
      mul_le_mul_of_nonneg_right hlog (inv_nonneg.mpr hdenom.le)
    have hexponent :
        (((theta * Real.log S + Real.log Ak) / 2) / (1 - theta) +
            (Real.log 16 / 2) *
              (theta / (1 - theta) ^ 2)) +
          (((theta * Real.log S + Real.log Ak) / 2) / (1 - theta) +
            (Real.log 16 / 2) *
              (theta / (1 - theta) ^ 2)) ≤
          base + (((2 * (n + 2) : ℕ) : ℝ) * Real.log m) := by
      rw [div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv]
      calc
        _ = theta * Real.log S * (1 - theta)⁻¹ +
              Real.log Ak * (1 - theta)⁻¹ +
              Real.log 16 * theta * ((1 - theta) ^ 2)⁻¹ := by ring
        _ ≤ theta * Real.log S * (1 - theta)⁻¹ +
              (Real.log Abar + 4 * Real.log m) * (1 - theta)⁻¹ +
              Real.log 16 * theta * ((1 - theta) ^ 2)⁻¹ := by
          gcongr
        _ = base + (4 * (1 - theta)⁻¹) * Real.log m := by
          dsimp only [base]
          rw [div_eq_mul_inv, div_eq_mul_inv]
          ring
        _ = base + (((2 * (n + 2) : ℕ) : ℝ) * Real.log m) := by
          rw [hdegree]
    unfold canonicalLateBombieriGiustiReverseCost
    rw [moserLocalBoundFactor_eq_exp, Real.rpow_two, pow_two,
      ← Real.exp_add]
    calc
      Real.exp
          ((((theta * Real.log S + Real.log Ak) / 2) / (1 - theta) +
              (Real.log 16 / 2) *
                (theta / (1 - theta) ^ 2)) +
            (((theta * Real.log S + Real.log Ak) / 2) / (1 - theta) +
              (Real.log 16 / 2) *
                (theta / (1 - theta) ^ 2))) ≤
          Real.exp
            (base + (((2 * (n + 2) : ℕ) : ℝ) * Real.log m)) := by
        exact Real.exp_le_exp.mpr hexponent
      _ = Real.exp base * Real.exp
          (((2 * (n + 2) : ℕ) : ℝ) * Real.log m) := Real.exp_add _ _
      _ = C * m ^ (2 * (n + 2)) := by
        rw [Real.exp_nat_mul (Real.log m) (2 * (n + 2)), Real.exp_log hm]
      _ = C * (k + 1 : ℝ) ^ (2 * (Module.finrank ℝ E + 2)) := by rfl

theorem summable_canonicalLateBombieriGiustiThreshold
    (g : SmoothRiemannianMetric I M)
    (hdim : 2 < (Module.finrank ℝ E : ℝ))
    (rho : SmoothScalar g)
    {p₀ c₀ τ c d D lower upper : ℝ}
    (hp₀ : 0 < p₀) (hc₀ : 0 ≤ c₀)
    (hτc : τ < c) (hcd : c ≤ d) (hdD : d < D)
    (hlowerUpper : lower < upper) :
    Summable (fun k : ℕ => (3 / 4 : ℝ) ^ k *
      (bombieriGiustiThreshold p₀ c₀
        (canonicalLateBombieriGiustiReverseCost (I := I) (M := M)
          g hdim rho τ c d D lower upper k) / 4)) := by
  rcases exists_polynomial_bound_canonicalLateBombieriGiustiReverseCost
      g hdim rho hτc hcd hdD hlowerUpper with ⟨C, hC, hbound⟩
  exact summable_geometric_mul_bombieriGiustiThreshold_of_polynomial_le
    (2 * (Module.finrank ℝ E + 2)) hp₀ hc₀ hC
    (fun k => one_le_canonicalLateBombieriGiustiReverseCost
      g hdim rho τ c d D lower upper k)
    hbound

theorem localizedSpacetimeRpowNorm_inv_le_canonicalLateBombieriGiustiReverseCost_of_supersolution
    (g : SmoothRiemannianMetric I M)
    (hdim : 2 < (Module.finrank ℝ E : ℝ))
    (rho : SmoothScalar g)
    (u : ℝ → M → ℝ)
    (hu : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun z : ℝ × M => u z.1 z.2))
    (hpos : ∀ t x, 0 < u t x)
    {p₀ τ c d D lower upper : ℝ}
    (hτc : τ < c) (hcd : c ≤ d) (hdD : d < D)
    (hlowerUpper : lower < upper)
    (hmeasure : ∀ k,
      localizedSpacetimeMeasure (I := I) (M := M)
        (bombieriGiustiSpatialCutoff rho lower upper k)
          (bombieriGiustiDescendingLevel τ c k)
          (bombieriGiustiIncreasingLevel d D k) ≠ 0)
    (hpde : ∀ t ∈ Icc τ D, ∀ x : M,
      Δ_g (I := I) g (smoothScalarSlice (I := I) g u hu t).toContMDiffMap x ≤
        deriv (fun s => u s x) t) :
    ∀ k {p : ℝ}, 0 < p → p < p₀ →
      localizedSpacetimeRpowNorm (I := I) (M := M)
          (bombieriGiustiSpatialCutoff rho lower upper k)
          (fun t x => (u t x)⁻¹) p₀
          (bombieriGiustiDescendingLevel τ c k)
          (bombieriGiustiIncreasingLevel d D k) ≤
        canonicalLateBombieriGiustiReverseCost (I := I) (M := M)
            g hdim rho τ c d D lower upper k ^ (1 / p - 1 / p₀) *
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
  let inv : ℝ → M → ℝ := fun t x => (u t x)⁻¹
  have ha := bombieriGiustiDescendingLevel_strictAnti hτc
  have hb := bombieriGiustiIncreasingLevel_strictMono hdD
  have haOuterInner : aOuter < aInner := ha (Nat.lt_succ_self k)
  have hbInnerOuter : bInner < bOuter := hb (Nat.lt_succ_self k)
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
  have hpdeOuter : ∀ t ∈ Icc aOuter bOuter, ∀ x : M,
      Δ_g (I := I) g (smoothScalarSlice (I := I) g u hu t).toContMDiffMap x ≤
        deriv (fun s => u s x) t := by
    intro t ht x
    exact hpde t ⟨hτaOuter.le.trans ht.1, ht.2.trans hbOuterD.le⟩ x
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
        canonicalLateBombieriGiustiReverseCost (I := I) (M := M)
            g hdim rho τ c d D lower upper k ^ (1 / p - 1 / p₀) *
          localizedSpacetimeRpowNorm (I := I) (M := M)
            (spatialMoserCutoff localizer 0) inv p aOuter bOuter := by
    simpa only [inv, localizer, aOuter, aInner, bInner, bOuter, pivot,
      canonicalLateBombieriGiustiReverseCost] using
      (localizedSpacetimeRpowNorm_inv_reverse_holder_of_supersolution
        (I := I) (M := M) g hdim localizer
          (bombieriGiustiSpatialCutoff rho lower upper k) u hu hpos
          hp hpp₀.le haOuterPivot hpivotbOuter haOuterInner.le hpivotInner
          haInnerbInner hbInnerOuter
          (one_lt_bombieriGiustiReciprocalLocalizer_of_ne_zero
            rho hlowerUpper k)
          (bombieriGiustiSpatialCutoff_le_reciprocalLocalizer
            rho hlowerUpper k)
          hmeasureLocalizer hpdeOuter)
  have hinv : Continuous (fun z : ℝ × M => inv z.1 z.2) :=
    hu.continuous.inv₀ fun z => (hpos z.1 z.2).ne'
  have hinvpos : ∀ t x, 0 < inv t x := fun t x => inv_pos.mpr (hpos t x)
  have hmono := localizedSpacetimeRpowNorm_mono_measure
    (I := I) (M := M) inv hinv hinvpos
      (a := aOuter) (b := bOuter) (c := aOuter) (d := bOuter)
      hp le_rfl le_rfl
      (reciprocalLocalizer_le_bombieriGiustiSpatialCutoff_succ
        rho hlowerUpper k)
  have hcost : 0 ≤ canonicalLateBombieriGiustiReverseCost (I := I) (M := M)
      g hdim rho τ c d D lower upper k :=
    zero_le_one.trans (one_le_canonicalLateBombieriGiustiReverseCost
      g hdim rho τ c d D lower upper k)
  change localizedSpacetimeRpowNorm (I := I) (M := M)
      (bombieriGiustiSpatialCutoff rho lower upper k) inv p₀ aInner bInner ≤
    canonicalLateBombieriGiustiReverseCost (I := I) (M := M)
        g hdim rho τ c d D lower upper k ^ (1 / p - 1 / p₀) *
      localizedSpacetimeRpowNorm (I := I) (M := M)
        (bombieriGiustiSpatialCutoff rho lower upper (k + 1))
        inv p aOuter bOuter
  calc
    localizedSpacetimeRpowNorm (I := I) (M := M)
        (bombieriGiustiSpatialCutoff rho lower upper k) inv p₀ aInner bInner ≤
      canonicalLateBombieriGiustiReverseCost (I := I) (M := M)
          g hdim rho τ c d D lower upper k ^ (1 / p - 1 / p₀) *
        localizedSpacetimeRpowNorm (I := I) (M := M)
          (spatialMoserCutoff localizer 0) inv p aOuter bOuter := hreverse
    _ ≤ canonicalLateBombieriGiustiReverseCost (I := I) (M := M)
          g hdim rho τ c d D lower upper k ^ (1 / p - 1 / p₀) *
        localizedSpacetimeRpowNorm (I := I) (M := M)
          (bombieriGiustiSpatialCutoff rho lower upper (k + 1))
          inv p aOuter bOuter :=
      mul_le_mul_of_nonneg_left hmono (Real.rpow_nonneg hcost _)

theorem late_localizedSpacetimeRpowNorm_inv_le_exp_tsum_canonicalBombieriGiustiThreshold_of_supersolution_of_summable
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
    {p₀ τ c d D lower upper : ℝ}
    (hp₀ : 0 < p₀)
    (hτc : τ < c) (hcd : c ≤ d) (hdD : d < D)
    (hlowerUpper : lower < upper)
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
    (hmass : 0 < cutoffMass (I := I) (M := M) averagingCutoff)
    (hpde : ∀ t ∈ Icc τ D, ∀ x : M,
      Δ_g (I := I) g (smoothScalarSlice (I := I) g u hu t).toContMDiffMap x ≤
        deriv (fun q => u q x) t)
    (hsummable : Summable (fun k : ℕ =>
      (3 / 4 : ℝ) ^ k *
        (bombieriGiustiThreshold p₀
          (2 * C * cutoffMass (I := I) (M := M) averagingCutoff)
          (canonicalLateBombieriGiustiReverseCost (I := I) (M := M)
            g hdim rho τ c d D lower upper k) / 4))) :
    let rate := logCenterDrift (I := I) (M := M) g averagingCutoff
    let center := shiftedLogCenter (I := I) (M := M) g averagingCutoff
      u hu hpos τ
    let v := exponentialTimeRescale rate center u
    localizedSpacetimeRpowNorm (I := I) (M := M)
        (bombieriGiustiSpatialCutoff rho lower upper 0)
        (fun t x => (v t x)⁻¹) p₀ c d ≤
      Real.exp (∑' k : ℕ, (3 / 4 : ℝ) ^ k *
        (bombieriGiustiThreshold p₀
          (2 * C * cutoffMass (I := I) (M := M) averagingCutoff)
          (canonicalLateBombieriGiustiReverseCost (I := I) (M := M)
            g hdim rho τ c d D lower upper k) / 4)) := by
  let rate := logCenterDrift (I := I) (M := M) g averagingCutoff
  let center := shiftedLogCenter (I := I) (M := M) g averagingCutoff
    u hu hpos τ
  let v := exponentialTimeRescale rate center u
  have hv := contMDiff_exponentialTimeRescale rate center u hu
  have hvpos := exponentialTimeRescale_pos rate center u hpos
  have hvpde : ∀ t ∈ Icc τ D, ∀ x : M,
      Δ_g (I := I) g (smoothScalarSlice (I := I) g v hv t).toContMDiffMap x ≤
        deriv (fun q => v q x) t := by
    intro t ht x
    exact centered_exponential_time_rescale_supersolution
      (I := I) (M := M) g averagingCutoff u hu hpos τ (hpde t ht x)
  have hbound :=
    late_localizedSpacetimeRpowNorm_inv_le_exp_tsum_bombieriGiustiThreshold_of_supersolution
      (I := I) (M := M) g
      (bombieriGiustiSpatialCutoff rho lower upper) outer averagingCutoff
      (canonicalLateBombieriGiustiReverseCost (I := I) (M := M)
        g hdim rho τ c d D lower upper)
      (bombieriGiustiDescendingLevel τ c)
      (bombieriGiustiIncreasingLevel d D)
      C hC hP u hu hpos (τ := τ) (D := D) hp₀
      (fun k => one_le_canonicalLateBombieriGiustiReverseCost
        g hdim rho τ c d D lower upper k)
      hmeasure hmeasure_le_one
      (fun k => (bombieriGiustiDescendingLevel_strictAnti hτc
        (Nat.lt_succ_self k)).le)
      (fun k => (bombieriGiustiIncreasingLevel_strictMono hdD
        (Nat.lt_succ_self k)).le)
      (bombieriGiustiSpatialCutoff_mono rho hlowerUpper)
      (hτc.le.trans (hcd.trans hdD.le))
      (fun k => (bombieriGiustiDescendingLevel_gt hτc k).le)
      (fun k => (bombieriGiustiIncreasingLevel_lt hdD k).le)
      houter hmass hpde
      (fun k p hp hpp₀ => by
        simpa only [v, rate, center] using
          (localizedSpacetimeRpowNorm_inv_le_canonicalLateBombieriGiustiReverseCost_of_supersolution
            (I := I) (M := M) g hdim rho v hv hvpos hτc hcd hdD
              hlowerUpper hmeasure hvpde k hp hpp₀))
      hsummable
  simpa only [bombieriGiustiDescendingLevel_zero,
    bombieriGiustiIncreasingLevel_zero, v, rate, center] using hbound

theorem late_localizedSpacetimeRpowNorm_inv_le_exp_tsum_canonicalBombieriGiustiThreshold_of_supersolution
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
    {p₀ τ c d D lower upper : ℝ}
    (hp₀ : 0 < p₀)
    (hτc : τ < c) (hcd : c ≤ d) (hdD : d < D)
    (hlowerUpper : lower < upper)
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
    (hmass : 0 < cutoffMass (I := I) (M := M) averagingCutoff)
    (hpde : ∀ t ∈ Icc τ D, ∀ x : M,
      Δ_g (I := I) g (smoothScalarSlice (I := I) g u hu t).toContMDiffMap x ≤
        deriv (fun q => u q x) t) :
    let rate := logCenterDrift (I := I) (M := M) g averagingCutoff
    let center := shiftedLogCenter (I := I) (M := M) g averagingCutoff
      u hu hpos τ
    let v := exponentialTimeRescale rate center u
    localizedSpacetimeRpowNorm (I := I) (M := M)
        (bombieriGiustiSpatialCutoff rho lower upper 0)
        (fun t x => (v t x)⁻¹) p₀ c d ≤
      Real.exp (∑' k : ℕ, (3 / 4 : ℝ) ^ k *
        (bombieriGiustiThreshold p₀
          (2 * C * cutoffMass (I := I) (M := M) averagingCutoff)
          (canonicalLateBombieriGiustiReverseCost (I := I) (M := M)
            g hdim rho τ c d D lower upper k) / 4)) := by
  apply
    late_localizedSpacetimeRpowNorm_inv_le_exp_tsum_canonicalBombieriGiustiThreshold_of_supersolution_of_summable
      g hdim rho outer averagingCutoff C hC hP u hu hpos hp₀ hτc hcd hdD
        hlowerUpper hmeasure hmeasure_le_one houter hmass hpde
  have hc₀ : 0 ≤
      2 * C * cutoffMass (I := I) (M := M) averagingCutoff :=
    mul_nonneg (mul_nonneg (by norm_num) hC.le) hmass.le
  exact summable_canonicalLateBombieriGiustiThreshold
    g hdim rho hp₀ hc₀ hτc hcd hdD hlowerUpper

end DifferentialGeometry.Analysis.Parabolic.Moser

end
