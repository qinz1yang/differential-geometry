import DifferentialGeometry.Analysis.HoleFilling
import DifferentialGeometry.Analysis.Parabolic.Moser.EvolvingBombieriGiusti
import DifferentialGeometry.Analysis.Parabolic.Moser.SpacetimeSup

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

variable [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]

private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

def evolvingMoserSmallExponentStepFactor
    (n : ℕ) (Vfixed Vmoving : ℝ≥0∞)
    (C G B τ c d D lower upper : ℝ) (k : ℕ) : ℝ :=
  canonicalEvolvingLateBombieriGiustiReverseCost
    n Vfixed Vmoving C G B τ c d D lower upper k ^ (1 / 2 : ℝ)

def evolvingMoserSmallExponentLocalBoundFactor
    (n : ℕ) (Vfixed Vmoving : ℝ≥0∞)
    (C G B p τ c d D lower upper : ℝ) : ℝ :=
  let alpha := p / 2
  let beta := 1 - alpha
  let theta : ℝ := 1 / 2
  ∑' k : ℕ, theta ^ k *
    (alpha *
      (evolvingMoserSmallExponentStepFactor
          n Vfixed Vmoving C G B τ c d D lower upper k *
        (beta / theta) ^ beta) ^ (1 / alpha))

theorem summable_evolvingMoserSmallExponentLocalBoundCost
    (n : ℕ) [NeZero n] (Vfixed Vmoving : ℝ≥0∞)
    {C G B p τ c d D lower upper : ℝ}
    (hp : 0 < p) (hp_two : p < 2)
    (hτc : τ < c) (hcd : c ≤ d) (hdD : d < D)
    (hG : 0 ≤ G) (hB : 0 ≤ B)
    (hlowerUpper : lower < upper) :
    let alpha := p / 2
    let beta := 1 - alpha
    let theta : ℝ := 1 / 2
    Summable (fun k : ℕ => theta ^ k *
      (alpha *
        (evolvingMoserSmallExponentStepFactor
            n Vfixed Vmoving C G B τ c d D lower upper k *
          (beta / theta) ^ beta) ^ (1 / alpha))) := by
  let alpha := p / 2
  let beta := 1 - alpha
  let theta : ℝ := 1 / 2
  let F : ℕ → ℝ := fun k =>
    evolvingMoserSmallExponentStepFactor
      n Vfixed Vmoving C G B τ c d D lower upper k
  let degree := 2 * (n + 2)
  have halpha : 0 < alpha := div_pos hp (by norm_num)
  have hbeta : 0 < beta := by dsimp only [beta, alpha]; linarith
  have htheta : 0 < theta := by norm_num [theta]
  rcases exists_polynomial_bound_canonicalEvolvingLateBombieriGiustiReverseCost
      n Vfixed Vmoving hτc hcd hdD hG hB hlowerUpper with
    ⟨L, hL, hcost⟩
  let R := (beta / theta) ^ beta
  let K := alpha * (L * R) ^ (1 / alpha)
  let s := (degree : ℝ) / alpha
  have hR : 0 < R := Real.rpow_pos_of_pos (div_pos hbeta htheta) _
  have hK : 0 ≤ K := mul_nonneg halpha.le
    (Real.rpow_nonneg (mul_nonneg (zero_le_one.trans hL) hR.le) _)
  have hF : ∀ k, F k ≤ L * (k + 1 : ℝ) ^ degree := by
    intro k
    calc
      F k ≤ canonicalEvolvingLateBombieriGiustiReverseCost
          n Vfixed Vmoving C G B τ c d D lower upper k := by
        exact Real.rpow_le_self_of_one_le
          (one_le_canonicalEvolvingLateBombieriGiustiReverseCost
            n Vfixed Vmoving C G B τ c d D lower upper k)
          (by norm_num)
      _ ≤ L * (k + 1 : ℝ) ^ degree := by
        simpa only [degree] using hcost k
  have hpoint : ∀ k, alpha * (F k * R) ^ (1 / alpha) ≤
      K * (k + 1 : ℝ) ^ s := by
    intro k
    let m : ℝ := k + 1
    have hm : 0 < m := by positivity
    have hFR : F k * R ≤ (L * m ^ degree) * R :=
      mul_le_mul_of_nonneg_right (by simpa only [m] using hF k) hR.le
    have hrpow := Real.rpow_le_rpow
      (mul_nonneg
        (Real.rpow_nonneg
          (zero_le_one.trans
            (one_le_canonicalEvolvingLateBombieriGiustiReverseCost
              n Vfixed Vmoving C G B τ c d D lower upper k)) _)
        hR.le)
      hFR (div_pos one_pos halpha).le
    calc
      alpha * (F k * R) ^ (1 / alpha) ≤
          alpha * ((L * m ^ degree) * R) ^ (1 / alpha) :=
        mul_le_mul_of_nonneg_left hrpow halpha.le
      _ = K * m ^ s := by
        have hpower : ((L * m ^ degree) * R) ^ (1 / alpha) =
            (L * R) ^ (1 / alpha) *
              m ^ ((degree : ℝ) * (1 / alpha)) := by
          rw [show (L * m ^ degree) * R = (L * R) * m ^ degree by ring,
            Real.mul_rpow (mul_nonneg (zero_le_one.trans hL) hR.le)
              (pow_nonneg hm.le degree),
            ← Real.rpow_natCast, ← Real.rpow_mul hm.le]
        have hexponent : (degree : ℝ) * (1 / alpha) =
            (degree : ℝ) / alpha := by
          field_simp [halpha.ne']
        rw [hpower, hexponent]
        dsimp only [K, s]
        ring
      _ = K * (k + 1 : ℝ) ^ s := by rfl
  have hmajor : Summable (fun k : ℕ =>
      theta ^ k * (K * (k + 1 : ℝ) ^ s)) := by
    have hs := summable_geometric_mul_nat_add_rpow
      (r := theta) (by norm_num [theta])
      (by norm_num [theta, Real.norm_eq_abs]) s
    refine (hs.mul_right K).congr ?_
    intro k
    ring
  apply Summable.of_nonneg_of_le
  · intro k
    exact mul_nonneg (pow_nonneg htheta.le k)
      (mul_nonneg halpha.le (Real.rpow_nonneg
        (mul_nonneg
          (Real.rpow_nonneg
            (zero_le_one.trans
              (one_le_canonicalEvolvingLateBombieriGiustiReverseCost
                n Vfixed Vmoving C G B τ c d D lower upper k)) _)
          hR.le) _))
  · intro k
    exact mul_le_mul_of_nonneg_left (hpoint k) (pow_nonneg htheta.le k)
  · simpa only [alpha, beta, theta, F, R] using hmajor

theorem evolvingMoserSmallExponentLocalBoundFactor_nonneg
    (n : ℕ) (Vfixed Vmoving : ℝ≥0∞)
    (C G B : ℝ) {p τ c d D lower upper : ℝ}
    (hp : 0 < p) (hp_two : p < 2) :
    0 ≤ evolvingMoserSmallExponentLocalBoundFactor
      n Vfixed Vmoving C G B p τ c d D lower upper := by
  let alpha := p / 2
  let beta := 1 - alpha
  let theta : ℝ := 1 / 2
  have halpha : 0 < alpha := div_pos hp (by norm_num)
  have hbeta : 0 < beta := by dsimp only [beta, alpha]; linarith
  unfold evolvingMoserSmallExponentLocalBoundFactor
  apply tsum_nonneg
  intro k
  exact mul_nonneg (pow_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) k)
    (mul_nonneg halpha.le (Real.rpow_nonneg
      (mul_nonneg
        (Real.rpow_nonneg
          (zero_le_one.trans
            (one_le_canonicalEvolvingLateBombieriGiustiReverseCost
              n Vfixed Vmoving C G B τ c d D lower upper k)) _)
        (Real.rpow_nonneg (div_nonneg hbeta.le (by norm_num)) _)) _))

theorem evolving_local_boundedness_of_subsolution_of_lt_two_of_volume_le
    (qMetric : SmoothRiemannianMetric I M)
    (g : ℝ → SmoothRiemannianMetric I M)
    (hdim : 2 < (Module.finrank ℝ E : ℝ))
    (rho : SmoothScalar qMetric)
    (u : ℝ → M → ℝ)
    (hu : ContMDiff ((modelWithCornersSelf ℝ ℝ).prod I)
      (modelWithCornersSelf ℝ ℝ) ∞
      (fun z : ℝ × M => u z.1 z.2))
    (hpos : ∀ t x, 0 < u t x)
    {p τ c d D C G B outerLower outerUpper lower upper t₀ : ℝ}
    (Vfixed Vmoving : ℝ≥0∞)
    (hp : 0 < p) (hp_two : p < 2)
    (hτc : τ < c) (hcd : c ≤ d) (hdD : d < D)
    (hC : 0 ≤ C) (hG : 0 ≤ G) (hB : 0 ≤ B)
    (houter : outerLower < outerUpper) (houterLower : outerUpper ≤ lower)
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
      deriv (fun s => u s x) t ≤
        Δ_g (I := I) (g t)
          (smoothScalarSlice (I := I) (g t) u hu t).toContMDiffMap x)
    (htrace : ∀ t ∈ Icc τ D, ∀ x : M,
      traceTimeDerivMetric (I := I) g t x ≤ B)
    (hrho : ∀ t ∈ Icc τ D, ∀ x : M,
      (g t).inner x
          (gradFun (I := I) (g t) rho.toFun x)
          (gradFun (I := I) (g t) rho.toFun x) ≤ G)
    (hVfixedTop : Vfixed ≠ ⊤) (hVmovingTop : Vmoving ≠ ⊤)
    (hfixedVolume : ∀ t ∈ Icc τ D,
      riemannianVolumeMeasure (I := I) (M := M) qMetric ≤
        Vfixed • riemannianMeasureFamily (I := I) (M := M) g t)
    (hmovingVolume : ∀ t ∈ Icc τ D,
      riemannianMeasureFamily (I := I) (M := M) g t ≤
        Vmoving • riemannianVolumeMeasure (I := I) (M := M) qMetric) :
    ∀ t ∈ Icc c d, ∀ x : M,
      (bombieriGiustiSpatialCutoff rho lower upper 0).toFun x ≠ 0 →
      u t x ≤
        evolvingMoserSmallExponentLocalBoundFactor
            (Module.finrank ℝ E) Vfixed Vmoving C G B p
              τ c d D lower upper *
          localizedSpacetimeRpowNorm (I := I) (M := M)
            (spatialCutoffBetween rho outerLower outerUpper) u p τ D := by
  let n := Module.finrank ℝ E
  letI : NeZero n := by
    refine ⟨Nat.ne_of_gt ?_⟩
    exact_mod_cast (by linarith : 0 < (n : ℝ))
  let alpha := p / 2
  let beta := 1 - alpha
  let theta : ℝ := 1 / 2
  let cutoff : ℕ → SmoothScalar qMetric := fun k =>
    bombieriGiustiSpatialCutoff rho lower upper k
  let localizer : ℕ → SmoothScalar qMetric := fun k =>
    bombieriGiustiReciprocalLocalizer rho lower upper k
  let a : ℕ → ℝ := bombieriGiustiDescendingLevel τ c
  let b : ℕ → ℝ := bombieriGiustiIncreasingLevel d D
  let pivot : ℕ → ℝ := bombieriGiustiLatePivot τ c
  let F : ℕ → ℝ := fun k =>
    evolvingMoserSmallExponentStepFactor
      n Vfixed Vmoving C G B τ c d D lower upper k
  let N := localizedSpacetimeRpowNorm (I := I) (M := M)
    (spatialCutoffBetween rho outerLower outerUpper) u p τ D
  let X : ℕ → ℝ := fun k =>
    localizedSpacetimeSup (I := I) (cutoff k) u (a k) (b k)
  have halpha : 0 < alpha := div_pos hp (by norm_num)
  have halpha_one : alpha < 1 := by dsimp only [alpha]; linarith
  have hbeta : 0 < beta := sub_pos.mpr halpha_one
  have halphaBeta : alpha + beta = 1 := by dsimp only [beta]; ring
  have htheta : 0 < theta := by norm_num [theta]
  have htheta_one : theta < 1 := by norm_num [theta]
  have ha : ∀ k, τ ≤ a k := fun k =>
    (bombieriGiustiDescendingLevel_gt hτc k).le
  have hb : ∀ k, b k ≤ D := fun k =>
    (bombieriGiustiIncreasingLevel_lt hdD k).le
  have hab : ∀ k, a k ≤ b k := fun k =>
    (bombieriGiustiDescendingLevel_le hτc k).trans
      (hcd.trans (bombieriGiustiIncreasingLevel_ge hdD k))
  have hN : 0 ≤ N := localizedSpacetimeRpowNorm_nonneg
    (I := I) (M := M) _ u (fun t x => (hpos t x).le) p τ D
  intro t ht x hx
  have hcutoff : ∀ k, (cutoff k).toFun x ≠ 0 := by
    intro k
    induction k with
    | zero => exact hx
    | succ k ih =>
        intro hzero
        have hmono := bombieriGiustiSpatialCutoff_mono
          rho hlowerUpper k x
        change (cutoff k).toFun x ^ 2 ≤ (cutoff (k + 1)).toFun x ^ 2 at hmono
        rw [hzero, zero_pow (by norm_num : 2 ≠ 0)] at hmono
        have hsquare : (cutoff k).toFun x ^ 2 = 0 :=
          le_antisymm hmono (sq_nonneg _)
        exact ih (sq_eq_zero_iff.mp hsquare)
  have hXpos : ∀ k, 0 < X k := by
    intro k
    exact localizedSpacetimeSup_pos (I := I) (M := M)
      (cutoff k) u hu.continuous hpos (hab k) ⟨x, hcutoff k⟩
  have hXbdd : BddAbove (Set.range X) := by
    apply bddAbove_range_localizedSpacetimeSup
      (I := I) (M := M) cutoff u hu.continuous ha hb hab
    intro k
    exact ⟨x, hcutoff k⟩
  have hFnonneg : ∀ k, 0 ≤ F k := fun k =>
    Real.rpow_nonneg
      (zero_le_one.trans
        (one_le_canonicalEvolvingLateBombieriGiustiReverseCost
          n Vfixed Vmoving C G B τ c d D lower upper k)) _
  have hcoefficient_nonneg : ∀ k, 0 ≤ F k * N ^ alpha := fun k =>
    mul_nonneg (hFnonneg k) (Real.rpow_nonneg hN _)
  have hstep : ∀ k, X k ≤
      (F k * N ^ alpha) * X (k + 1) ^ beta := by
    intro k
    let aOuter := a (k + 1)
    let bOuter := b (k + 1)
    let localPivot := pivot k
    let localGradient :=
      evolvingBombieriGiustiReciprocalGradientCost G lower upper k
    let Dmoving := evolvingMoserLocalizedMass
      (I := I) (M := M) n g (localizer k) u 2
        aOuter localPivot bOuter 0
    let Dfixed := moserLocalizedMass
      (I := I) (M := M) n (localizer k) u 2
        aOuter localPivot bOuter 0
    let Ntwo := localizedSpacetimeRpowNorm (I := I) (M := M)
      (spatialMoserCutoff (localizer k) 0) u 2 aOuter bOuter
    let A := max 1 Vfixed.toReal * evolvingMoserLocalBoundFactor
      n C localGradient B 2 aOuter localPivot bOuter
    have haOuterInner : aOuter < a k := by
      exact bombieriGiustiDescendingLevel_strictAnti hτc (Nat.lt_succ_self k)
    have hbInnerOuter : b k < bOuter := by
      exact bombieriGiustiIncreasingLevel_strictMono hdD (Nat.lt_succ_self k)
    have haOuterPivot : aOuter < localPivot := by
      dsimp only [aOuter, localPivot, a, pivot, bombieriGiustiLatePivot]
      linarith
    have hpivotInner : localPivot < a k := by
      dsimp only [localPivot, a, pivot, bombieriGiustiLatePivot]
      linarith
    have hpivotOuter : localPivot ≤ bOuter :=
      hpivotInner.le.trans ((hab k).trans hbInnerOuter.le)
    have haOuterτ : τ ≤ aOuter := ha (k + 1)
    have hbOuterD : bOuter ≤ D := hb (k + 1)
    have hpdeOuter : ∀ s ∈ Icc aOuter bOuter, ∀ y : M,
        deriv (fun q => u q y) s ≤
          Δ_g (I := I) (g s)
            (smoothScalarSlice (I := I) (g s) u hu s).toContMDiffMap y := by
      intro s hs y
      exact hpde s ⟨haOuterτ.trans hs.1, hs.2.trans hbOuterD⟩ y
    have hnormBound : ∀ s ∈ Icc aOuter bOuter, ∀ y,
        (spatialMoserCutoff (localizer k) 0).toFun y ≠ 0 →
          u s y ≤ X (k + 1) := by
      intro s hs y hy
      apply le_localizedSpacetimeSup (I := I) (M := M)
        (cutoff (k + 1)) u hu.continuous hs
      intro hzero
      have hmono := reciprocalLocalizer_le_bombieriGiustiSpatialCutoff_succ
        rho hlowerUpper k y
      change (spatialMoserCutoff (localizer k) 0).toFun y ^ 2 ≤
        (cutoff (k + 1)).toFun y ^ 2 at hmono
      rw [hzero, zero_pow (by norm_num : 2 ≠ 0)] at hmono
      exact hy (sq_eq_zero_iff.mp (le_antisymm hmono (sq_nonneg _)))
    have hinterpolation := localizedSpacetimeRpowNorm_le_of_bound_on_cutoff
      (I := I) (M := M) (spatialMoserCutoff (localizer k) 0) u
      hu.continuous hpos hp (by linarith : p ≤ 2) (hab (k + 1))
      (hXpos (k + 1)) hnormBound
    have hnormMono : localizedSpacetimeRpowNorm (I := I) (M := M)
        (spatialMoserCutoff (localizer k) 0) u p aOuter bOuter ≤ N := by
      apply localizedSpacetimeRpowNorm_mono_measure
        (I := I) (M := M) u hu.continuous hpos hp
          haOuterτ hbOuterD
      intro y
      exact (reciprocalLocalizer_le_bombieriGiustiSpatialCutoff_succ
        rho hlowerUpper k y).trans
        (bombieriGiustiSpatialCutoff_le_outer rho houter houterLower
          hlowerUpper (k + 1) y)
    have hnormPower : localizedSpacetimeRpowNorm (I := I) (M := M)
        (spatialMoserCutoff (localizer k) 0) u p aOuter bOuter ^ alpha ≤
        N ^ alpha := by
      exact Real.rpow_le_rpow
        (localizedSpacetimeRpowNorm_nonneg (I := I) (M := M) _ u
          (fun s y => (hpos s y).le) p aOuter bOuter)
        hnormMono halpha.le
    have hnormTwo : Ntwo ≤ N ^ alpha * X (k + 1) ^ beta := by
      calc
        Ntwo ≤ localizedSpacetimeRpowNorm (I := I) (M := M)
              (spatialMoserCutoff (localizer k) 0) u p aOuter bOuter ^ (p / 2) *
            X (k + 1) ^ (1 - p / 2) := hinterpolation
        _ ≤ N ^ alpha * X (k + 1) ^ beta := by
          exact mul_le_mul_of_nonneg_right
            (by simpa only [alpha] using hnormPower)
            (Real.rpow_nonneg (hXpos (k + 1)).le _)
    have hDmoving : 0 ≤ Dmoving := evolvingMoserLocalizedMass_nonneg
      (I := I) (M := M) n g (localizer k) u haOuterPivot hpivotOuter
        (fun s y => (hpos s y).le) 0
    have hDfixed : 0 ≤ Dfixed := moserLocalizedMass_nonneg
      (I := I) (M := M) n (localizer k) u haOuterPivot hpivotOuter
        (fun s y => (hpos s y).le) 0
    have hmass : Dmoving ≤ Vmoving.toReal * Dfixed := by
      simpa only [Dmoving, Dfixed, moserTimeLevel_zero] using
        (evolvingMoserLocalizedMass_le_toReal_mul_moserLocalizedMass
          (I := I) (M := M) n g (localizer k) u hu hpos
            haOuterPivot hpivotOuter hg Vmoving hVmovingTop 0
            (fun s hs => hmovingVolume s
              ⟨haOuterτ.trans (by simpa only [moserTimeLevel_zero] using hs.1),
                hs.2.trans hbOuterD⟩))
    have hroot : Dmoving ^ (1 / 2 : ℝ) ≤
        Vmoving.toReal ^ (1 / 2 : ℝ) * Dfixed ^ (1 / 2 : ℝ) := by
      calc
        Dmoving ^ (1 / 2 : ℝ) ≤
            (Vmoving.toReal * Dfixed) ^ (1 / 2 : ℝ) :=
          Real.rpow_le_rpow hDmoving hmass (by norm_num)
        _ = Vmoving.toReal ^ (1 / 2 : ℝ) *
            Dfixed ^ (1 / 2 : ℝ) := by
          rw [Real.mul_rpow ENNReal.toReal_nonneg hDfixed]
    have hfixedNorm : Dfixed ^ (1 / 2 : ℝ) = Ntwo := by
      simpa only [Dfixed, Ntwo, moserNormalizedMass,
        parabolicMoserExponent_zero] using
        (moserNormalizedMass_zero_eq_localizedSpacetimeRpowNorm
          (I := I) (M := M) n (localizer k) u hu hpos (hab (k + 1)))
    have hA : 0 ≤ A := mul_nonneg
      (zero_le_one.trans (le_max_left 1 Vfixed.toReal)) (Real.exp_pos _).le
    have hraw : 0 ≤ A ^ (2 : ℝ) * Vmoving.toReal :=
      mul_nonneg (Real.rpow_nonneg hA _) ENNReal.toReal_nonneg
    have hrootA : (A ^ (2 : ℝ)) ^ (1 / 2 : ℝ) = A := by
      rw [← Real.rpow_mul hA]
      norm_num
    have hactualRoot : A * Vmoving.toReal ^ (1 / 2 : ℝ) =
        (A ^ (2 : ℝ) * Vmoving.toReal) ^ (1 / 2 : ℝ) := by
      rw [Real.mul_rpow (Real.rpow_nonneg hA _) ENNReal.toReal_nonneg,
        hrootA]
    have hrawCanonical : A ^ (2 : ℝ) * Vmoving.toReal ≤
        canonicalEvolvingLateBombieriGiustiReverseCost
          n Vfixed Vmoving C G B τ c d D lower upper k := by
      unfold canonicalEvolvingLateBombieriGiustiReverseCost
        evolvingReciprocalReverseCost
      apply le_max_of_le_right
      rfl
    have hfactor : A * Vmoving.toReal ^ (1 / 2 : ℝ) ≤ F k := by
      rw [hactualRoot]
      exact Real.rpow_le_rpow hraw hrawCanonical (by norm_num)
    apply localizedSpacetimeSup_le (I := I) (M := M)
      (cutoff k) u (hab k) ⟨x, hcutoff k⟩
    intro s hs y hy
    have hsLocal : s ∈ Ioo localPivot bOuter :=
      ⟨hpivotInner.trans_le hs.1, hs.2.trans_lt hbInnerOuter⟩
    have hyLocal : 1 < (localizer k).toFun y :=
      one_lt_bombieriGiustiReciprocalLocalizer_of_ne_zero
        rho hlowerUpper k y hy
    have hlocal := evolving_local_boundedness_of_subsolution_of_volume_le
      (I := I) (M := M) g hdim (localizer k) u hu hpos
        (p₀ := 2) (by norm_num) haOuterPivot hpivotOuter hB hC
        (evolvingBombieriGiustiReciprocalGradientCost_nonneg hG k)
        hg hgram
        (fun q hq => hSobolev q
          ⟨haOuterτ.trans hq.1, hq.2.trans hbOuterD⟩)
        hpdeOuter
        (fun q hq z => htrace q
          ⟨haOuterτ.trans hq.1, hq.2.trans hbOuterD⟩ z)
        (fun j q hq z =>
          spatialMoserCutoff_bombieriGiustiReciprocalLocalizer_gradient_le
            (I := I) (g q) rho hG
              (fun w => hrho q
                ⟨haOuterτ.trans hq.1, hq.2.trans hbOuterD⟩ w)
              k j z)
        Vfixed hVfixedTop
        (fun q hq => hfixedVolume q
          ⟨haOuterτ.trans hq.1, hq.2.trans hbOuterD⟩)
        s hsLocal y hyLocal
    have hlocal' : u s y ≤ A * Dmoving ^ (1 / 2 : ℝ) := by
      simpa only [A, Dmoving, evolvingMoserLocalBound,
        evolvingMoserNormalizedMass, parabolicMoserExponent_zero,
        localGradient, aOuter, localPivot, bOuter, n, localizer,
        mul_assoc] using hlocal
    calc
      u s y ≤ A * Dmoving ^ (1 / 2 : ℝ) := hlocal'
      _ ≤ A *
          (Vmoving.toReal ^ (1 / 2 : ℝ) * Dfixed ^ (1 / 2 : ℝ)) :=
        mul_le_mul_of_nonneg_left hroot hA
      _ = (A * Vmoving.toReal ^ (1 / 2 : ℝ)) * Ntwo := by
        rw [hfixedNorm]
        ring
      _ ≤ F k * Ntwo :=
        mul_le_mul_of_nonneg_right hfactor
          (localizedSpacetimeRpowNorm_nonneg
            (I := I) (M := M) (spatialMoserCutoff (localizer k) 0) u
              (fun q z => (hpos q z).le) 2 aOuter bOuter)
      _ ≤ F k * (N ^ alpha * X (k + 1) ^ beta) :=
        mul_le_mul_of_nonneg_left hnormTwo (hFnonneg k)
      _ = (F k * N ^ alpha) * X (k + 1) ^ beta := by ring
  have hstructural := summable_evolvingMoserSmallExponentLocalBoundCost
    n Vfixed Vmoving (C := C) hp hp_two hτc hcd hdD hG hB hlowerUpper
  have hstructural' : Summable (fun k : ℕ => theta ^ k *
      (alpha * (F k * (beta / theta) ^ beta) ^ (1 / alpha))) := by
    simpa only [alpha, beta, theta, F] using hstructural
  have hterm : ∀ k, theta ^ k *
      (alpha * (((F k * N ^ alpha) *
        (beta / theta) ^ beta) ^ (1 / alpha))) =
    (theta ^ k *
      (alpha * (F k * (beta / theta) ^ beta) ^ (1 / alpha))) * N := by
    intro k
    have hFbeta : 0 ≤ F k * (beta / theta) ^ beta :=
      mul_nonneg (hFnonneg k)
        (Real.rpow_nonneg (div_nonneg hbeta.le htheta.le) _)
    have hNalpha : 0 ≤ N ^ alpha := Real.rpow_nonneg hN _
    rw [show (F k * N ^ alpha) * (beta / theta) ^ beta =
        (F k * (beta / theta) ^ beta) * N ^ alpha by ring,
      Real.mul_rpow hFbeta hNalpha, ← Real.rpow_mul hN]
    have hcancel : alpha * (1 / alpha) = 1 := by field_simp [halpha.ne']
    rw [hcancel, Real.rpow_one]
    ring
  have hsummable : Summable (fun k : ℕ => theta ^ k *
      (alpha * (((F k * N ^ alpha) *
        (beta / theta) ^ beta) ^ (1 / alpha)))) := by
    refine (hstructural'.mul_right N).congr ?_
    intro k
    exact (hterm k).symm
  have hhole := DifferentialGeometry.Analysis.weighted_summable_hole_filling
    hXbdd (fun k => (hXpos k).le) hcoefficient_nonneg halpha hbeta
      halphaBeta htheta htheta_one hsummable hstep
  have hfactor : (∑' k : ℕ, theta ^ k *
      (alpha * (((F k * N ^ alpha) *
        (beta / theta) ^ beta) ^ (1 / alpha)))) =
      evolvingMoserSmallExponentLocalBoundFactor
          n Vfixed Vmoving C G B p τ c d D lower upper * N := by
    rw [tsum_congr hterm, tsum_mul_right]
    rfl
  calc
    u t x ≤ X 0 := le_localizedSpacetimeSup
      (I := I) (M := M) (cutoff 0) u hu.continuous
        (by simpa only [a, b, bombieriGiustiDescendingLevel_zero,
          bombieriGiustiIncreasingLevel_zero] using ht) hx
    _ ≤ ∑' k : ℕ, theta ^ k *
        (alpha * (((F k * N ^ alpha) *
          (beta / theta) ^ beta) ^ (1 / alpha))) := hhole
    _ = evolvingMoserSmallExponentLocalBoundFactor
          n Vfixed Vmoving C G B p τ c d D lower upper * N := hfactor

private theorem evolving_local_boundedness_of_subsolution_of_two_le_of_volume_le
    (qMetric : SmoothRiemannianMetric I M)
    (g : ℝ → SmoothRiemannianMetric I M)
    (hdim : 2 < (Module.finrank ℝ E : ℝ))
    (rho : SmoothScalar qMetric)
    (u : ℝ → M → ℝ)
    (hu : ContMDiff ((modelWithCornersSelf ℝ ℝ).prod I)
      (modelWithCornersSelf ℝ ℝ) ∞
      (fun z : ℝ × M => u z.1 z.2))
    (hpos : ∀ t x, 0 < u t x)
    {p τ c d D C G B outerLower outerUpper lower upper t₀ : ℝ}
    (Vfixed Vmoving : ℝ≥0∞)
    (hp : 2 ≤ p)
    (hτc : τ < c) (hcd : c ≤ d) (hdD : d < D)
    (hC : 0 ≤ C) (hG : 0 ≤ G) (hB : 0 ≤ B)
    (houter : outerLower < outerUpper) (houterLower : outerUpper ≤ lower)
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
      deriv (fun s => u s x) t ≤
        Δ_g (I := I) (g t)
          (smoothScalarSlice (I := I) (g t) u hu t).toContMDiffMap x)
    (htrace : ∀ t ∈ Icc τ D, ∀ x : M,
      traceTimeDerivMetric (I := I) g t x ≤ B)
    (hrho : ∀ t ∈ Icc τ D, ∀ x : M,
      (g t).inner x
          (gradFun (I := I) (g t) rho.toFun x)
          (gradFun (I := I) (g t) rho.toFun x) ≤ G)
    (hVfixedTop : Vfixed ≠ ⊤) (hVmovingTop : Vmoving ≠ ⊤)
    (hfixedVolume : ∀ t ∈ Icc τ D,
      riemannianVolumeMeasure (I := I) (M := M) qMetric ≤
        Vfixed • riemannianMeasureFamily (I := I) (M := M) g t)
    (hmovingVolume : ∀ t ∈ Icc τ D,
      riemannianMeasureFamily (I := I) (M := M) g t ≤
        Vmoving • riemannianVolumeMeasure (I := I) (M := M) qMetric) :
    ∀ t ∈ Icc c d, ∀ x : M,
      (bombieriGiustiSpatialCutoff rho lower upper 0).toFun x ≠ 0 →
      u t x ≤
        (max 1 Vfixed.toReal *
            evolvingMoserLocalBoundFactor
              (Module.finrank ℝ E) C
                (evolvingBombieriGiustiReciprocalGradientCost
                  G lower upper 0)
                B p
                (bombieriGiustiDescendingLevel τ c 1)
                (bombieriGiustiLatePivot τ c 0)
                (bombieriGiustiIncreasingLevel d D 1) *
            Vmoving.toReal ^ (1 / p)) *
          localizedSpacetimeRpowNorm (I := I) (M := M)
            (spatialCutoffBetween rho outerLower outerUpper) u p τ D := by
  let n := Module.finrank ℝ E
  let aOuter := bombieriGiustiDescendingLevel τ c 1
  let pivot := bombieriGiustiLatePivot τ c 0
  let bOuter := bombieriGiustiIncreasingLevel d D 1
  let localizer := bombieriGiustiReciprocalLocalizer rho lower upper 0
  let localGradient :=
    evolvingBombieriGiustiReciprocalGradientCost G lower upper 0
  let Dmoving := evolvingMoserLocalizedMass
    (I := I) (M := M) n g localizer u p aOuter pivot bOuter 0
  let Dfixed := moserLocalizedMass
    (I := I) (M := M) n localizer u p aOuter pivot bOuter 0
  let Nlocal := localizedSpacetimeRpowNorm (I := I) (M := M)
    (spatialMoserCutoff localizer 0) u p aOuter bOuter
  let Nouter := localizedSpacetimeRpowNorm (I := I) (M := M)
    (spatialCutoffBetween rho outerLower outerUpper) u p τ D
  let A := max 1 Vfixed.toReal *
    evolvingMoserLocalBoundFactor n C localGradient B p aOuter pivot bOuter
  have hp_pos : 0 < p := lt_of_lt_of_le (by norm_num) hp
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
  have haOuterbOuter : aOuter ≤ bOuter :=
    (bombieriGiustiDescendingLevel_le hτc 1).trans
      (hcd.trans hdbOuter.le)
  have hpivotbOuter : pivot ≤ bOuter :=
    hpivotc.le.trans (hcd.trans hdbOuter.le)
  have hpdeOuter : ∀ s ∈ Icc aOuter bOuter, ∀ y : M,
      deriv (fun q => u q y) s ≤
        Δ_g (I := I) (g s)
          (smoothScalarSlice (I := I) (g s) u hu s).toContMDiffMap y := by
    intro s hs y
    exact hpde s ⟨hτaOuter.le.trans hs.1, hs.2.trans hbOuterD.le⟩ y
  have hDmoving : 0 ≤ Dmoving := evolvingMoserLocalizedMass_nonneg
    (I := I) (M := M) n g localizer u haOuterPivot hpivotbOuter
      (fun s y => (hpos s y).le) 0
  have hDfixed : 0 ≤ Dfixed := moserLocalizedMass_nonneg
    (I := I) (M := M) n localizer u haOuterPivot hpivotbOuter
      (fun s y => (hpos s y).le) 0
  have hA : 0 ≤ A := mul_nonneg
    (zero_le_one.trans (le_max_left 1 Vfixed.toReal)) (Real.exp_pos _).le
  have hmass : Dmoving ≤ Vmoving.toReal * Dfixed := by
    simpa only [Dmoving, Dfixed, moserTimeLevel_zero] using
      (evolvingMoserLocalizedMass_le_toReal_mul_moserLocalizedMass
        (I := I) (M := M) n g localizer u hu hpos
          haOuterPivot hpivotbOuter hg Vmoving hVmovingTop 0
          (fun s hs => hmovingVolume s
            ⟨hτaOuter.le.trans
                (by simpa only [moserTimeLevel_zero] using hs.1),
              hs.2.trans hbOuterD.le⟩))
  have hroot : Dmoving ^ (1 / p) ≤
      Vmoving.toReal ^ (1 / p) * Dfixed ^ (1 / p) := by
    calc
      Dmoving ^ (1 / p) ≤ (Vmoving.toReal * Dfixed) ^ (1 / p) :=
        Real.rpow_le_rpow hDmoving hmass (div_nonneg one_pos.le hp_pos.le)
      _ = Vmoving.toReal ^ (1 / p) * Dfixed ^ (1 / p) := by
        rw [Real.mul_rpow ENNReal.toReal_nonneg hDfixed]
  have hfixedNorm : Dfixed ^ (1 / p) = Nlocal := by
    simpa only [Dfixed, Nlocal, moserNormalizedMass,
      parabolicMoserExponent_zero] using
      (moserNormalizedMass_zero_eq_localizedSpacetimeRpowNorm
        (I := I) (M := M) n localizer u hu hpos haOuterbOuter)
  have hnormMono : Nlocal ≤ Nouter := by
    apply localizedSpacetimeRpowNorm_mono_measure
      (I := I) (M := M) u hu.continuous hpos hp_pos
        hτaOuter.le hbOuterD.le
    intro y
    exact (reciprocalLocalizer_le_bombieriGiustiSpatialCutoff_succ
      rho hlowerUpper 0 y).trans
      (bombieriGiustiSpatialCutoff_le_outer rho houter houterLower
        hlowerUpper 1 y)
  intro t ht x hx
  have htLocal : t ∈ Ioo pivot bOuter :=
    ⟨hpivotc.trans_le ht.1, ht.2.trans_lt hdbOuter⟩
  have hxLocal : 1 < localizer.toFun x :=
    one_lt_bombieriGiustiReciprocalLocalizer_of_ne_zero
      rho hlowerUpper 0 x hx
  have hlocal := evolving_local_boundedness_of_subsolution_of_volume_le
    (I := I) (M := M) g hdim localizer u hu hpos hp
      haOuterPivot hpivotbOuter hB hC
      (evolvingBombieriGiustiReciprocalGradientCost_nonneg hG 0)
      hg hgram
      (fun s hs => hSobolev s
        ⟨hτaOuter.le.trans hs.1, hs.2.trans hbOuterD.le⟩)
      hpdeOuter
      (fun s hs y => htrace s
        ⟨hτaOuter.le.trans hs.1, hs.2.trans hbOuterD.le⟩ y)
      (fun k s hs y =>
        spatialMoserCutoff_bombieriGiustiReciprocalLocalizer_gradient_le
          (I := I) (g s) rho hG
            (fun z => hrho s
              ⟨hτaOuter.le.trans hs.1, hs.2.trans hbOuterD.le⟩ z)
            0 k y)
      Vfixed hVfixedTop
      (fun s hs => hfixedVolume s
        ⟨hτaOuter.le.trans hs.1, hs.2.trans hbOuterD.le⟩)
      t htLocal x hxLocal
  have hlocal' : u t x ≤ A * Dmoving ^ (1 / p) := by
    simpa only [A, Dmoving, evolvingMoserLocalBound,
      evolvingMoserNormalizedMass, parabolicMoserExponent_zero,
      localGradient, aOuter, pivot, bOuter, n, localizer, mul_assoc] using hlocal
  calc
    u t x ≤ A * Dmoving ^ (1 / p) := hlocal'
    _ ≤ A * (Vmoving.toReal ^ (1 / p) * Dfixed ^ (1 / p)) :=
      mul_le_mul_of_nonneg_left hroot hA
    _ = (A * Vmoving.toReal ^ (1 / p)) * Nlocal := by
      rw [hfixedNorm]
      ring
    _ ≤ (A * Vmoving.toReal ^ (1 / p)) * Nouter :=
      mul_le_mul_of_nonneg_left hnormMono
        (mul_nonneg hA (Real.rpow_nonneg ENNReal.toReal_nonneg _))
    _ = (max 1 Vfixed.toReal *
            evolvingMoserLocalBoundFactor n C localGradient B p
              aOuter pivot bOuter *
            Vmoving.toReal ^ (1 / p)) * Nouter := by rfl

def evolvingMoserPositiveExponentLocalBoundFactor
    (n : ℕ) (Vfixed Vmoving : ℝ≥0∞)
    (C G B p τ c d D lower upper : ℝ) : ℝ :=
  if p < 2 then
    evolvingMoserSmallExponentLocalBoundFactor
      n Vfixed Vmoving C G B p τ c d D lower upper
  else
    max 1 Vfixed.toReal *
      evolvingMoserLocalBoundFactor n C
        (evolvingBombieriGiustiReciprocalGradientCost G lower upper 0)
        B p
        (bombieriGiustiDescendingLevel τ c 1)
        (bombieriGiustiLatePivot τ c 0)
        (bombieriGiustiIncreasingLevel d D 1) *
      Vmoving.toReal ^ (1 / p)

theorem evolvingMoserPositiveExponentLocalBoundFactor_nonneg
    (n : ℕ) (Vfixed Vmoving : ℝ≥0∞)
    (C G B : ℝ) {p τ c d D lower upper : ℝ} (hp : 0 < p) :
    0 ≤ evolvingMoserPositiveExponentLocalBoundFactor
      n Vfixed Vmoving C G B p τ c d D lower upper := by
  by_cases hp_two : p < 2
  · rw [evolvingMoserPositiveExponentLocalBoundFactor, if_pos hp_two]
    exact evolvingMoserSmallExponentLocalBoundFactor_nonneg
      n Vfixed Vmoving C G B hp hp_two
  · rw [evolvingMoserPositiveExponentLocalBoundFactor, if_neg hp_two]
    exact mul_nonneg
      (mul_nonneg
        (zero_le_one.trans (le_max_left 1 Vfixed.toReal))
        (Real.exp_pos _).le)
      (Real.rpow_nonneg ENNReal.toReal_nonneg _)

theorem evolving_local_boundedness_of_subsolution_rpow_of_volume_le
    (qMetric : SmoothRiemannianMetric I M)
    (g : ℝ → SmoothRiemannianMetric I M)
    (hdim : 2 < (Module.finrank ℝ E : ℝ))
    (rho : SmoothScalar qMetric)
    (u : ℝ → M → ℝ)
    (hu : ContMDiff ((modelWithCornersSelf ℝ ℝ).prod I)
      (modelWithCornersSelf ℝ ℝ) ∞
      (fun z : ℝ × M => u z.1 z.2))
    (hpos : ∀ t x, 0 < u t x)
    {p τ c d D C G B outerLower outerUpper lower upper t₀ : ℝ}
    (Vfixed Vmoving : ℝ≥0∞)
    (hp : 0 < p)
    (hτc : τ < c) (hcd : c ≤ d) (hdD : d < D)
    (hC : 0 ≤ C) (hG : 0 ≤ G) (hB : 0 ≤ B)
    (houter : outerLower < outerUpper) (houterLower : outerUpper ≤ lower)
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
      deriv (fun s => u s x) t ≤
        Δ_g (I := I) (g t)
          (smoothScalarSlice (I := I) (g t) u hu t).toContMDiffMap x)
    (htrace : ∀ t ∈ Icc τ D, ∀ x : M,
      traceTimeDerivMetric (I := I) g t x ≤ B)
    (hrho : ∀ t ∈ Icc τ D, ∀ x : M,
      (g t).inner x
          (gradFun (I := I) (g t) rho.toFun x)
          (gradFun (I := I) (g t) rho.toFun x) ≤ G)
    (hVfixedTop : Vfixed ≠ ⊤) (hVmovingTop : Vmoving ≠ ⊤)
    (hfixedVolume : ∀ t ∈ Icc τ D,
      riemannianVolumeMeasure (I := I) (M := M) qMetric ≤
        Vfixed • riemannianMeasureFamily (I := I) (M := M) g t)
    (hmovingVolume : ∀ t ∈ Icc τ D,
      riemannianMeasureFamily (I := I) (M := M) g t ≤
        Vmoving • riemannianVolumeMeasure (I := I) (M := M) qMetric) :
    ∀ t ∈ Icc c d, ∀ x : M,
      (bombieriGiustiSpatialCutoff rho lower upper 0).toFun x ≠ 0 →
      u t x ≤
        evolvingMoserPositiveExponentLocalBoundFactor
            (Module.finrank ℝ E) Vfixed Vmoving C G B p
              τ c d D lower upper *
          localizedSpacetimeRpowNorm (I := I) (M := M)
            (spatialCutoffBetween rho outerLower outerUpper) u p τ D := by
  by_cases hp_two : p < 2
  · simpa only [evolvingMoserPositiveExponentLocalBoundFactor,
      if_pos hp_two] using
      (evolving_local_boundedness_of_subsolution_of_lt_two_of_volume_le
        (I := I) (M := M) qMetric g hdim rho u hu hpos Vfixed Vmoving
          hp hp_two hτc hcd hdD hC hG hB houter houterLower hlowerUpper
          hg hgram hSobolev hpde htrace hrho hVfixedTop hVmovingTop
          hfixedVolume hmovingVolume)
  · have hpTwo : 2 ≤ p := le_of_not_gt hp_two
    simpa only [evolvingMoserPositiveExponentLocalBoundFactor,
      if_neg hp_two] using
      (evolving_local_boundedness_of_subsolution_of_two_le_of_volume_le
        (I := I) (M := M) qMetric g hdim rho u hu hpos Vfixed Vmoving
          hpTwo hτc hcd hdD hC hG hB houter houterLower hlowerUpper
          hg hgram hSobolev hpde htrace hrho hVfixedTop hVmovingTop
          hfixedVolume hmovingVolume)

end DifferentialGeometry.Analysis.Parabolic.Moser

end
