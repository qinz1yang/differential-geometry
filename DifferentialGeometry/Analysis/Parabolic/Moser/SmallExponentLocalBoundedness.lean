import DifferentialGeometry.Analysis.HoleFilling
import DifferentialGeometry.Analysis.Parabolic.Moser.BombieriGiustiReciprocal
import DifferentialGeometry.Analysis.Parabolic.Moser.SpacetimeSup

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

def moserSmallExponentLocalBoundFactor
    (g : SmoothRiemannianMetric I M)
    (hdim : 2 < (Module.finrank ℝ E : ℝ))
    (rho : SmoothScalar g) (p τ c d D lower upper : ℝ) : ℝ :=
  let alpha := p / 2
  let beta := 1 - alpha
  let theta : ℝ := 1 / 2
  ∑' k : ℕ, theta ^ k *
    (alpha *
      (moserLocalBoundFactor (I := I) (M := M) g hdim
          (bombieriGiustiReciprocalLocalizer rho lower upper k) 2
          (bombieriGiustiDescendingLevel τ c (k + 1))
          (bombieriGiustiLatePivot τ c k)
          (bombieriGiustiIncreasingLevel d D (k + 1)) *
        (beta / theta) ^ beta) ^ (1 / alpha))

theorem summable_moserSmallExponentLocalBoundCost
    (g : SmoothRiemannianMetric I M)
    (hdim : 2 < (Module.finrank ℝ E : ℝ))
    (rho : SmoothScalar g)
    {p τ c d D lower upper : ℝ}
    (hp : 0 < p) (hp_two : p < 2)
    (hτc : τ < c) (hcd : c ≤ d) (hdD : d < D)
    (hlowerUpper : lower < upper) :
    let alpha := p / 2
    let beta := 1 - alpha
    let theta : ℝ := 1 / 2
    Summable (fun k : ℕ ↦ theta ^ k *
      (alpha *
        (moserLocalBoundFactor (I := I) (M := M) g hdim
            (bombieriGiustiReciprocalLocalizer rho lower upper k) 2
            (bombieriGiustiDescendingLevel τ c (k + 1))
            (bombieriGiustiLatePivot τ c k)
            (bombieriGiustiIncreasingLevel d D (k + 1)) *
          (beta / theta) ^ beta) ^ (1 / alpha))) := by
  let n := Module.finrank ℝ E
  let alpha := p / 2
  let beta := 1 - alpha
  let theta : ℝ := 1 / 2
  let F : ℕ → ℝ := fun k ↦
    moserLocalBoundFactor (I := I) (M := M) g hdim
      (bombieriGiustiReciprocalLocalizer rho lower upper k) 2
      (bombieriGiustiDescendingLevel τ c (k + 1))
      (bombieriGiustiLatePivot τ c k)
      (bombieriGiustiIncreasingLevel d D (k + 1))
  let degree := 2 * (n + 2)
  have halpha : 0 < alpha := div_pos hp (by norm_num)
  have hbeta : 0 < beta := by dsimp only [beta, alpha]; linarith
  have htheta : 0 < theta := by norm_num [theta]
  rcases exists_polynomial_bound_canonicalLateBombieriGiustiReverseCost
      g hdim rho hτc hcd hdD hlowerUpper with ⟨C, hC, hcost⟩
  let R := (beta / theta) ^ beta
  let K := alpha * (C * R) ^ (1 / alpha)
  let s := (degree : ℝ) / alpha
  have hR : 0 < R := Real.rpow_pos_of_pos (div_pos hbeta htheta) _
  have hK : 0 ≤ K := mul_nonneg halpha.le
    (Real.rpow_nonneg (mul_nonneg (zero_le_one.trans hC) hR.le) _)
  have hF : ∀ k, F k ≤ C * (k + 1 : ℝ) ^ degree := by
    intro k
    have hFone : 1 ≤ F k := by
      exact one_le_moserLocalBoundFactor g hdim
        (bombieriGiustiReciprocalLocalizer rho lower upper k)
        (by norm_num) _ _ _
    have hFsquare : F k ≤ (F k) ^ 2 := by nlinarith
    calc
      F k ≤ (F k) ^ 2 := hFsquare
      _ = canonicalLateBombieriGiustiReverseCost (I := I) (M := M)
          g hdim rho τ c d D lower upper k := by
        rw [canonicalLateBombieriGiustiReverseCost, Real.rpow_two]
      _ ≤ C * (k + 1 : ℝ) ^ degree := by
        simpa only [degree, n] using hcost k
  have hpoint : ∀ k, alpha * (F k * R) ^ (1 / alpha) ≤
      K * (k + 1 : ℝ) ^ s := by
    intro k
    let m : ℝ := k + 1
    have hm : 0 < m := by positivity
    have hFR : F k * R ≤ (C * m ^ degree) * R :=
      mul_le_mul_of_nonneg_right (by simpa only [m] using hF k) hR.le
    have hrpow := Real.rpow_le_rpow
      (mul_nonneg (zero_le_one.trans
        (one_le_moserLocalBoundFactor g hdim
          (bombieriGiustiReciprocalLocalizer rho lower upper k)
          (by norm_num) _ _ _)) hR.le)
      hFR (div_pos one_pos halpha).le
    calc
      alpha * (F k * R) ^ (1 / alpha) ≤
          alpha * ((C * m ^ degree) * R) ^ (1 / alpha) :=
        mul_le_mul_of_nonneg_left hrpow halpha.le
      _ = K * m ^ s := by
        have hpower : ((C * m ^ degree) * R) ^ (1 / alpha) =
            (C * R) ^ (1 / alpha) * m ^ ((degree : ℝ) * (1 / alpha)) := by
          rw [show (C * m ^ degree) * R = (C * R) * m ^ degree by ring,
            Real.mul_rpow (mul_nonneg (zero_le_one.trans hC) hR.le)
              (pow_nonneg hm.le degree),
            ← Real.rpow_natCast, ← Real.rpow_mul hm.le]
        have hexponent : (degree : ℝ) * (1 / alpha) = (degree : ℝ) / alpha := by
          field_simp [halpha.ne']
        rw [hpower, hexponent]
        dsimp only [K, s]
        ring
      _ = K * (k + 1 : ℝ) ^ s := by rfl
  have hmajor : Summable (fun k : ℕ ↦
      theta ^ k * (K * (k + 1 : ℝ) ^ s)) := by
    have hs := summable_geometric_mul_nat_add_rpow
      (r := theta) (by norm_num [theta]) (by norm_num [theta, Real.norm_eq_abs]) s
    refine (hs.mul_right K).congr ?_
    intro k
    ring
  apply Summable.of_nonneg_of_le
  · intro k
    exact mul_nonneg (pow_nonneg htheta.le k)
      (mul_nonneg halpha.le (Real.rpow_nonneg
        (mul_nonneg (Real.exp_pos _).le hR.le) _))
  · intro k
    exact mul_le_mul_of_nonneg_left (hpoint k) (pow_nonneg htheta.le k)
  · simpa only [alpha, beta, theta, F, R] using hmajor

theorem moserSmallExponentLocalBoundFactor_nonneg
    (g : SmoothRiemannianMetric I M)
    (hdim : 2 < (Module.finrank ℝ E : ℝ))
    (rho : SmoothScalar g)
    {p τ c d D lower upper : ℝ} (hp : 0 < p) (hp_two : p < 2) :
    0 ≤ moserSmallExponentLocalBoundFactor (I := I) (M := M)
      g hdim rho p τ c d D lower upper := by
  let alpha := p / 2
  let beta := 1 - alpha
  let theta : ℝ := 1 / 2
  have halpha : 0 < alpha := div_pos hp (by norm_num)
  have hbeta : 0 < beta := by dsimp only [beta, alpha]; linarith
  unfold moserSmallExponentLocalBoundFactor
  apply tsum_nonneg
  intro k
  exact mul_nonneg (pow_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) k)
    (mul_nonneg halpha.le (Real.rpow_nonneg
      (mul_nonneg (Real.exp_pos _).le
        (Real.rpow_nonneg (div_nonneg hbeta.le (by norm_num)) _)) _))

private theorem local_boundedness_of_subsolution_of_lt_two
    (g : SmoothRiemannianMetric I M)
    (hdim : 2 < (Module.finrank ℝ E : ℝ))
    (rho : SmoothScalar g)
    (u : ℝ → M → ℝ)
    (hu : ContMDiff ((modelWithCornersSelf ℝ ℝ).prod I)
      (modelWithCornersSelf ℝ ℝ) ∞ (fun z : ℝ × M ↦ u z.1 z.2))
    (hpos : ∀ t x, 0 < u t x)
    {p τ c d D outerLower outerUpper lower upper : ℝ}
    (hp : 0 < p) (hp_two : p < 2)
    (hτc : τ < c) (hcd : c ≤ d) (hdD : d < D)
    (houter : outerLower < outerUpper) (houterLower : outerUpper ≤ lower)
    (hlowerUpper : lower < upper)
    (hpde : ∀ t ∈ Icc τ D, ∀ x : M,
      deriv (fun s ↦ u s x) t ≤
        Δ_g (I := I) g (smoothScalarSlice (I := I) g u hu t).toContMDiffMap x) :
    ∀ t ∈ Icc c d, ∀ x : M,
      (bombieriGiustiSpatialCutoff rho lower upper 0).toFun x ≠ 0 →
      u t x ≤
        moserSmallExponentLocalBoundFactor (I := I) (M := M)
            g hdim rho p τ c d D lower upper *
          localizedSpacetimeRpowNorm (I := I) (M := M)
            (spatialCutoffBetween rho outerLower outerUpper) u p τ D := by
  let alpha := p / 2
  let beta := 1 - alpha
  let theta : ℝ := 1 / 2
  let cutoff : ℕ → SmoothScalar g := fun k ↦
    bombieriGiustiSpatialCutoff rho lower upper k
  let localizer : ℕ → SmoothScalar g := fun k ↦
    bombieriGiustiReciprocalLocalizer rho lower upper k
  let a : ℕ → ℝ := bombieriGiustiDescendingLevel τ c
  let b : ℕ → ℝ := bombieriGiustiIncreasingLevel d D
  let pivot : ℕ → ℝ := bombieriGiustiLatePivot τ c
  let F : ℕ → ℝ := fun k ↦
    moserLocalBoundFactor (I := I) (M := M) g hdim (localizer k) 2
      (a (k + 1)) (pivot k) (b (k + 1))
  let N := localizedSpacetimeRpowNorm (I := I) (M := M)
    (spatialCutoffBetween rho outerLower outerUpper) u p τ D
  let X : ℕ → ℝ := fun k ↦
    localizedSpacetimeSup (I := I) (cutoff k) u (a k) (b k)
  have halpha : 0 < alpha := div_pos hp (by norm_num)
  have halpha_one : alpha < 1 := by dsimp only [alpha]; linarith
  have hbeta : 0 < beta := sub_pos.mpr halpha_one
  have halphaBeta : alpha + beta = 1 := by dsimp only [beta]; ring
  have htheta : 0 < theta := by norm_num [theta]
  have htheta_one : theta < 1 := by norm_num [theta]
  have ha : ∀ k, τ ≤ a k := fun k ↦
    (bombieriGiustiDescendingLevel_gt hτc k).le
  have hb : ∀ k, b k ≤ D := fun k ↦
    (bombieriGiustiIncreasingLevel_lt hdD k).le
  have hab : ∀ k, a k ≤ b k := fun k ↦
    (bombieriGiustiDescendingLevel_le hτc k).trans
      (hcd.trans (bombieriGiustiIncreasingLevel_ge hdD k))
  have hN : 0 ≤ N := localizedSpacetimeRpowNorm_nonneg
    (I := I) (M := M) _ u (fun t x ↦ (hpos t x).le) p τ D
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
  have hFnonneg : ∀ k, 0 ≤ F k := fun k ↦ (Real.exp_pos _).le
  have hcoefficient_nonneg : ∀ k, 0 ≤ F k * N ^ alpha := fun k ↦
    mul_nonneg (hFnonneg k) (Real.rpow_nonneg hN _)
  have hstep : ∀ k, X k ≤
      (F k * N ^ alpha) * X (k + 1) ^ beta := by
    intro k
    have haOuterInner : a (k + 1) < a k := by
      exact bombieriGiustiDescendingLevel_strictAnti hτc (Nat.lt_succ_self k)
    have hbInnerOuter : b k < b (k + 1) := by
      exact bombieriGiustiIncreasingLevel_strictMono hdD (Nat.lt_succ_self k)
    have haOuterPivot : a (k + 1) < pivot k := by
      dsimp only [a, pivot, bombieriGiustiLatePivot]
      linarith
    have hpivotInner : pivot k < a k := by
      dsimp only [a, pivot, bombieriGiustiLatePivot]
      linarith
    have hpivotOuter : pivot k ≤ b (k + 1) :=
      hpivotInner.le.trans ((hab k).trans hbInnerOuter.le)
    have hpdeOuter : ∀ s ∈ Icc (a (k + 1)) (b (k + 1)), ∀ y : M,
        deriv (fun q ↦ u q y) s ≤
          Δ_g (I := I) g (smoothScalarSlice (I := I) g u hu s).toContMDiffMap y := by
      intro s hs y
      exact hpde s ⟨(ha (k + 1)).trans hs.1, hs.2.trans (hb (k + 1))⟩ y
    have hnormBound : ∀ s ∈ Icc (a (k + 1)) (b (k + 1)), ∀ y,
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
        (spatialMoserCutoff (localizer k) 0) u p (a (k + 1)) (b (k + 1)) ≤ N := by
      apply localizedSpacetimeRpowNorm_mono_measure
        (I := I) (M := M) u hu.continuous hpos hp (ha (k + 1)) (hb (k + 1))
      intro y
      exact (reciprocalLocalizer_le_bombieriGiustiSpatialCutoff_succ
        rho hlowerUpper k y).trans
        (bombieriGiustiSpatialCutoff_le_outer rho houter houterLower
          hlowerUpper (k + 1) y)
    have hnormPower : localizedSpacetimeRpowNorm (I := I) (M := M)
        (spatialMoserCutoff (localizer k) 0) u p (a (k + 1)) (b (k + 1)) ^ alpha ≤
        N ^ alpha := by
      exact Real.rpow_le_rpow
        (localizedSpacetimeRpowNorm_nonneg (I := I) (M := M) _ u
          (fun s y ↦ (hpos s y).le) p (a (k + 1)) (b (k + 1)))
        hnormMono halpha.le
    have hnormTwo : localizedSpacetimeRpowNorm (I := I) (M := M)
        (spatialMoserCutoff (localizer k) 0) u 2 (a (k + 1)) (b (k + 1)) ≤
        N ^ alpha * X (k + 1) ^ beta := by
      calc
        _ ≤ localizedSpacetimeRpowNorm (I := I) (M := M)
              (spatialMoserCutoff (localizer k) 0) u p
                (a (k + 1)) (b (k + 1)) ^ (p / 2) *
            X (k + 1) ^ (1 - p / 2) := hinterpolation
        _ ≤ N ^ alpha * X (k + 1) ^ beta := by
          exact mul_le_mul_of_nonneg_right
            (by simpa only [alpha] using hnormPower)
            (Real.rpow_nonneg (hXpos (k + 1)).le _)
    apply localizedSpacetimeSup_le (I := I) (M := M)
      (cutoff k) u (hab k) ⟨x, hcutoff k⟩
    intro s hs y hy
    have hsLocal : s ∈ Ioo (pivot k) (b (k + 1)) :=
      ⟨hpivotInner.trans_le hs.1, hs.2.trans_lt hbInnerOuter⟩
    have hyLocal : 1 < (localizer k).toFun y := by
      exact one_lt_bombieriGiustiReciprocalLocalizer_of_ne_zero
        rho hlowerUpper k y hy
    have hlocal := local_boundedness_of_subsolution
      (I := I) (M := M) g hdim (localizer k) u hu hpos
        (p₀ := 2) (by norm_num) haOuterPivot hpivotOuter hpdeOuter
        s hsLocal y hyLocal
    have hlocal' : u s y ≤ F k *
        localizedSpacetimeRpowNorm (I := I) (M := M)
          (spatialMoserCutoff (localizer k) 0) u 2
            (a (k + 1)) (b (k + 1)) := by
      rw [moserLocalBound] at hlocal
      rwa [moserNormalizedMass_zero_eq_localizedSpacetimeRpowNorm
        (I := I) (M := M) (Module.finrank ℝ E) (localizer k) u hu hpos
          (hab (k + 1))] at hlocal
    calc
      u s y ≤ F k * localizedSpacetimeRpowNorm (I := I) (M := M)
          (spatialMoserCutoff (localizer k) 0) u 2
            (a (k + 1)) (b (k + 1)) := hlocal'
      _ ≤ F k * (N ^ alpha * X (k + 1) ^ beta) :=
        mul_le_mul_of_nonneg_left hnormTwo (hFnonneg k)
      _ = (F k * N ^ alpha) * X (k + 1) ^ beta := by ring
  have hstructural := summable_moserSmallExponentLocalBoundCost
    (I := I) (M := M) g hdim rho hp hp_two hτc hcd hdD hlowerUpper
  have hstructural' : Summable (fun k : ℕ ↦ theta ^ k *
      (alpha * (F k * (beta / theta) ^ beta) ^ (1 / alpha))) := by
    simpa only [alpha, beta, theta, F, localizer, a, b, pivot] using hstructural
  have hterm : ∀ k, theta ^ k *
      (alpha * (((F k * N ^ alpha) * (beta / theta) ^ beta) ^ (1 / alpha))) =
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
  have hsummable : Summable (fun k : ℕ ↦ theta ^ k *
      (alpha * (((F k * N ^ alpha) * (beta / theta) ^ beta) ^ (1 / alpha)))) := by
    refine (hstructural'.mul_right N).congr ?_
    intro k
    exact (hterm k).symm
  have hhole := DifferentialGeometry.Analysis.weighted_summable_hole_filling
    hXbdd (fun k ↦ (hXpos k).le) hcoefficient_nonneg halpha hbeta
      halphaBeta htheta htheta_one hsummable hstep
  have hfactor : (∑' k : ℕ, theta ^ k *
      (alpha * (((F k * N ^ alpha) * (beta / theta) ^ beta) ^ (1 / alpha)))) =
      moserSmallExponentLocalBoundFactor (I := I) (M := M)
          g hdim rho p τ c d D lower upper * N := by
    rw [tsum_congr hterm, tsum_mul_right]
    rfl
  calc
    u t x ≤ X 0 := le_localizedSpacetimeSup
      (I := I) (M := M) (cutoff 0) u hu.continuous
        (by simpa only [a, b, bombieriGiustiDescendingLevel_zero,
          bombieriGiustiIncreasingLevel_zero] using ht) hx
    _ ≤ ∑' k : ℕ, theta ^ k *
        (alpha * (((F k * N ^ alpha) * (beta / theta) ^ beta) ^ (1 / alpha))) := hhole
    _ = moserSmallExponentLocalBoundFactor (I := I) (M := M)
          g hdim rho p τ c d D lower upper * N := hfactor

private theorem local_boundedness_of_subsolution_of_two_le
    (g : SmoothRiemannianMetric I M)
    (hdim : 2 < (Module.finrank ℝ E : ℝ))
    (rho : SmoothScalar g)
    (u : ℝ → M → ℝ)
    (hu : ContMDiff ((modelWithCornersSelf ℝ ℝ).prod I)
      (modelWithCornersSelf ℝ ℝ) ∞ (fun z : ℝ × M ↦ u z.1 z.2))
    (hpos : ∀ t x, 0 < u t x)
    {p τ c d D outerLower outerUpper lower upper : ℝ}
    (hp : 2 ≤ p) (hτc : τ < c) (hcd : c ≤ d) (hdD : d < D)
    (houter : outerLower < outerUpper) (houterLower : outerUpper ≤ lower)
    (hlowerUpper : lower < upper)
    (hpde : ∀ t ∈ Icc τ D, ∀ x : M,
      deriv (fun s ↦ u s x) t ≤
        Δ_g (I := I) g (smoothScalarSlice (I := I) g u hu t).toContMDiffMap x) :
    ∀ t ∈ Icc c d, ∀ x : M,
      (bombieriGiustiSpatialCutoff rho lower upper 0).toFun x ≠ 0 →
      u t x ≤
        moserLocalBoundFactor (I := I) (M := M) g hdim
            (bombieriGiustiReciprocalLocalizer rho lower upper 0) p
            (bombieriGiustiDescendingLevel τ c 1)
            (bombieriGiustiLatePivot τ c 0)
            (bombieriGiustiIncreasingLevel d D 1) *
          localizedSpacetimeRpowNorm (I := I) (M := M)
            (spatialCutoffBetween rho outerLower outerUpper) u p τ D := by
  let aOuter := bombieriGiustiDescendingLevel τ c 1
  let pivot := bombieriGiustiLatePivot τ c 0
  let bOuter := bombieriGiustiIncreasingLevel d D 1
  let localizer := bombieriGiustiReciprocalLocalizer rho lower upper 0
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
  have hτaOuter : τ < aOuter := by
    exact bombieriGiustiDescendingLevel_gt hτc 1
  have hbOuterD : bOuter < D := by
    exact bombieriGiustiIncreasingLevel_lt hdD 1
  have haOuterbOuter : aOuter ≤ bOuter := by
    exact (bombieriGiustiDescendingLevel_le hτc 1).trans
      (hcd.trans hdbOuter.le)
  have hpivotbOuter : pivot ≤ bOuter :=
    hpivotc.le.trans (hcd.trans hdbOuter.le)
  have hpdeOuter : ∀ t ∈ Icc aOuter bOuter, ∀ x : M,
      deriv (fun s ↦ u s x) t ≤
        Δ_g (I := I) g (smoothScalarSlice (I := I) g u hu t).toContMDiffMap x := by
    intro t ht x
    exact hpde t ⟨hτaOuter.le.trans ht.1, ht.2.trans hbOuterD.le⟩ x
  intro t ht x hx
  have htLocal : t ∈ Ioo pivot bOuter :=
    ⟨hpivotc.trans_le ht.1, ht.2.trans_lt hdbOuter⟩
  have hxLocal : 1 < localizer.toFun x := by
    exact one_lt_bombieriGiustiReciprocalLocalizer_of_ne_zero
      rho hlowerUpper 0 x hx
  have hlocal := local_boundedness_of_subsolution
    (I := I) (M := M) g hdim localizer u hu hpos hp haOuterPivot
      hpivotbOuter hpdeOuter t htLocal x hxLocal
  have hlocal' : u t x ≤
      moserLocalBoundFactor (I := I) (M := M) g hdim
          localizer p aOuter pivot bOuter *
        localizedSpacetimeRpowNorm (I := I) (M := M)
          (spatialMoserCutoff localizer 0) u p aOuter bOuter := by
    rw [moserLocalBound] at hlocal
    rwa [moserNormalizedMass_zero_eq_localizedSpacetimeRpowNorm
      (I := I) (M := M) (Module.finrank ℝ E) localizer u hu hpos
        haOuterbOuter] at hlocal
  have hmono : localizedSpacetimeRpowNorm (I := I) (M := M)
      (spatialMoserCutoff localizer 0) u p aOuter bOuter ≤
    localizedSpacetimeRpowNorm (I := I) (M := M)
      (spatialCutoffBetween rho outerLower outerUpper) u p τ D := by
    apply localizedSpacetimeRpowNorm_mono_measure
      (I := I) (M := M) u hu.continuous hpos (lt_of_lt_of_le (by norm_num) hp)
      hτaOuter.le hbOuterD.le
    intro y
    exact (reciprocalLocalizer_le_bombieriGiustiSpatialCutoff_succ
      rho hlowerUpper 0 y).trans
      (bombieriGiustiSpatialCutoff_le_outer rho houter houterLower
        hlowerUpper 1 y)
  exact hlocal'.trans (mul_le_mul_of_nonneg_left hmono
    (Real.exp_pos _).le)

def moserPositiveExponentLocalBoundFactor
    (g : SmoothRiemannianMetric I M)
    (hdim : 2 < (Module.finrank ℝ E : ℝ))
    (rho : SmoothScalar g) (p τ c d D lower upper : ℝ) : ℝ :=
  if p < 2 then
    moserSmallExponentLocalBoundFactor (I := I) (M := M)
      g hdim rho p τ c d D lower upper
  else
    moserLocalBoundFactor (I := I) (M := M) g hdim
      (bombieriGiustiReciprocalLocalizer rho lower upper 0) p
      (bombieriGiustiDescendingLevel τ c 1)
      (bombieriGiustiLatePivot τ c 0)
      (bombieriGiustiIncreasingLevel d D 1)

theorem moserPositiveExponentLocalBoundFactor_nonneg
    (g : SmoothRiemannianMetric I M)
    (hdim : 2 < (Module.finrank ℝ E : ℝ))
    (rho : SmoothScalar g)
    {p τ c d D lower upper : ℝ} (hp : 0 < p) :
    0 ≤ moserPositiveExponentLocalBoundFactor (I := I) (M := M)
      g hdim rho p τ c d D lower upper := by
  by_cases hp_two : p < 2
  · rw [moserPositiveExponentLocalBoundFactor, if_pos hp_two]
    exact moserSmallExponentLocalBoundFactor_nonneg
      g hdim rho hp hp_two
  · rw [moserPositiveExponentLocalBoundFactor, if_neg hp_two]
    exact (Real.exp_pos _).le

theorem local_boundedness_of_subsolution_rpow
    (g : SmoothRiemannianMetric I M)
    (hdim : 2 < (Module.finrank ℝ E : ℝ))
    (rho : SmoothScalar g)
    (u : ℝ → M → ℝ)
    (hu : ContMDiff ((modelWithCornersSelf ℝ ℝ).prod I)
      (modelWithCornersSelf ℝ ℝ) ∞ (fun z : ℝ × M ↦ u z.1 z.2))
    (hpos : ∀ t x, 0 < u t x)
    {p τ c d D outerLower outerUpper lower upper : ℝ}
    (hp : 0 < p) (hτc : τ < c) (hcd : c ≤ d) (hdD : d < D)
    (houter : outerLower < outerUpper) (houterLower : outerUpper ≤ lower)
    (hlowerUpper : lower < upper)
    (hpde : ∀ t ∈ Icc τ D, ∀ x : M,
      deriv (fun s ↦ u s x) t ≤
        Δ_g (I := I) g (smoothScalarSlice (I := I) g u hu t).toContMDiffMap x) :
    ∀ t ∈ Icc c d, ∀ x : M,
      (bombieriGiustiSpatialCutoff rho lower upper 0).toFun x ≠ 0 →
      u t x ≤
        moserPositiveExponentLocalBoundFactor (I := I) (M := M)
            g hdim rho p τ c d D lower upper *
          localizedSpacetimeRpowNorm (I := I) (M := M)
            (spatialCutoffBetween rho outerLower outerUpper) u p τ D := by
  by_cases hp_two : p < 2
  · simpa only [moserPositiveExponentLocalBoundFactor, if_pos hp_two] using
      (local_boundedness_of_subsolution_of_lt_two
        (I := I) (M := M) g hdim rho u hu hpos hp hp_two hτc hcd hdD
          houter houterLower hlowerUpper hpde)
  · have hpTwo : 2 ≤ p := le_of_not_gt hp_two
    simpa only [moserPositiveExponentLocalBoundFactor, if_neg hp_two] using
      (local_boundedness_of_subsolution_of_two_le
        (I := I) (M := M) g hdim rho u hu hpos hpTwo hτc hcd hdD
          houter houterLower hlowerUpper hpde)

end DifferentialGeometry.Analysis.Parabolic.Moser

end
