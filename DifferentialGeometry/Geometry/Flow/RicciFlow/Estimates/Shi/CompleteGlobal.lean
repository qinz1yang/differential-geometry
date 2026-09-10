import DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.Shi.LaplacianInputRegularWindow
import DifferentialGeometry.Geometry.Comparison.HopfRinow.Proper
import DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.MetricComparison
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Ricci.Estimate.QuadraticForm

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Operator

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle Filter DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Analysis
open scoped Manifold ContDiff Topology Bundle BigOperators

section ScalarMonotonicity

private theorem div_le_div_right_of_nonneg {u v c : Real} (h : u ≤ v) (hc : 0 ≤ c) :
    u / c ≤ v / c := by
  rw [div_eq_mul_inv, div_eq_mul_inv]
  exact mul_le_mul_of_nonneg_right h (inv_nonneg.mpr hc)

private theorem max_div_right_of_pos {a b c : Real} (hc : 0 < c) :
    max a b / c = max (a / c) (b / c) := by
  rcases le_total a b with h | h
  · rw [max_eq_right h, max_eq_right (div_le_div_right_of_nonneg h hc.le)]
  · rw [max_eq_left h, max_eq_left (div_le_div_right_of_nonneg h hc.le)]

private theorem max_mul_right_of_nonneg {u v k : Real} (hk : 0 ≤ k) :
    max (u * k) (v * k) = max u v * k := by
  rcases le_total u v with h | h
  · rw [max_eq_right h, max_eq_right (mul_le_mul_of_nonneg_right h hk)]
  · rw [max_eq_left h, max_eq_left (mul_le_mul_of_nonneg_right h hk)]

private theorem max_one_sq_of_nonneg {u : Real} (hu : 0 ≤ u) :
    max 1 u ^ 2 = max 1 (u ^ 2) := by
  rcases le_total u 1 with h | h
  · rw [max_eq_left h, max_eq_left (by nlinarith : u ^ 2 ≤ (1 : Real)), one_pow]
  · rw [max_eq_right h, max_eq_right (by nlinarith : (1 : Real) ≤ u ^ 2)]

private theorem sqrt_max_one_le (x : Real) :
    Real.sqrt (max 1 x) ≤ max 1 (Real.sqrt x) := by
  rcases le_total x 1 with h | h
  · rw [max_eq_left h, Real.sqrt_one]
    exact le_max_left _ _
  · rw [max_eq_right h]
    exact le_max_right _ _

theorem polynomialAbsorptionBound_mono {a a' b b' c e e' : Real} (hc : 0 < c)
    (ha : a ≤ a') (hb : b ≤ b') (he : e ≤ e') :
    polynomialAbsorptionBound a b c e ≤ polynomialAbsorptionBound a' b' c e' := by
  have hmono : ∀ u v : Real, u ≤ v → 4 * u / c ≤ 4 * v / c := by
    intro u v huv
    exact div_le_div_right_of_nonneg (by linarith) hc.le
  have hinner : max 1 (max (4 * a / c) (max (4 * b / c) (4 * e / c))) ≤
      max 1 (max (4 * a' / c) (max (4 * b' / c) (4 * e' / c))) :=
    max_le_max le_rfl
      (max_le_max (hmono a a' ha) (max_le_max (hmono b b' hb) (hmono e e' he)))
  have h0 : (0 : Real) ≤ max 1 (max (4 * a / c) (max (4 * b / c) (4 * e / c))) :=
    le_trans zero_le_one (le_max_left _ _)
  unfold polynomialAbsorptionBound
  rw [pow_two, pow_two]
  exact mul_self_le_mul_self h0 hinner

theorem bernsteinSelfCoupledBound_mono {c C C' A A' B B' Dc Dc' kappa kappa' T T' : Real}
    (hc : 0 < c) (hCC : C ≤ C') (hT : 0 ≤ T) (hTT : T ≤ T')
    (hD : 0 ≤ Dc) (hDD : Dc ≤ Dc') (hk : 0 ≤ kappa) (hkk : kappa ≤ kappa')
    (hA : 0 ≤ A) (hAA : A ≤ A') (hB : 0 ≤ B) (hBB : B ≤ B') :
    bernsteinSelfCoupledBound c C A B Dc kappa T ≤
      bernsteinSelfCoupledBound c C' A' B' Dc' kappa' T' := by
  have hT' : (0 : Real) ≤ T' := le_trans hT hTT
  unfold bernsteinSelfCoupledBound
  refine polynomialAbsorptionBound_mono hc ?_ ?_ hCC
  · have h1 : T * Dc ≤ T' * Dc' := mul_le_mul hTT hDD hD hT'
    exact mul_le_mul h1 hkk hk (mul_nonneg hT' (le_trans hD hDD))
  · exact mul_le_mul hTT (by linarith) (by linarith) hT'

private theorem shiFirstTimeConst_mono (d : ℕ) (a : Real) {T T' : Real}
    (hT : 0 ≤ T) (hTT : T ≤ T') :
    shiFirstTimeConst d a T ≤ shiFirstTimeConst d a T' := by
  have hc := shiFirstBernsteinConst_nonneg d a
  have hsq : T ^ 2 ≤ T' ^ 2 := by nlinarith
  unfold shiFirstTimeConst
  nlinarith

private theorem exp_window_mono (d : ℕ) (K : Real) {T T' : Real} (hTT : T ≤ T') (k : Real)
    (hk : 0 ≤ k) :
    Real.exp (k * ((d : Real) ^ 2 * Real.sqrt K) * T) ≤
      Real.exp (k * ((d : Real) ^ 2 * Real.sqrt K) * T') := by
  refine Real.exp_le_exp.mpr ?_
  have h : (0 : Real) ≤ k * ((d : Real) ^ 2 * Real.sqrt K) :=
    mul_nonneg hk (mul_nonneg (sq_nonneg _) (Real.sqrt_nonneg _))
  nlinarith


private theorem shiInitialCutoffA_mono (d : ℕ) (K r₁ r₂ : Real) {T T' : Real} (hTT : T ≤ T') :
    shiInitialCutoffA d T K r₁ r₂ ≤ shiInitialCutoffA d T' K r₁ r₂ := by
  have hcoef : (0 : Real) ≤ shiCutoffDerivSqConst * (2 / (r₂ - r₁)) ^ 2 :=
    mul_nonneg shiCutoffDerivSqConst_nonneg (sq_nonneg _)
  unfold shiInitialCutoffA
  exact mul_le_mul_of_nonneg_left (exp_window_mono d K hTT 2 (by norm_num)) hcoef

private theorem shiInitialCutoffB_mono (d : ℕ) (K : Real) {r₁ r₂ : Real} (hr : r₁ ≤ r₂)
    {T T' Clap Clap' : Real} (hTT : T ≤ T') (hC : Clap ≤ Clap') :
    shiInitialCutoffB d T K r₁ r₂ Clap ≤ shiInitialCutoffB d T' K r₁ r₂ Clap' := by
  have hk : (0 : Real) ≤ 2 / (r₂ - r₁) := div_nonneg (by norm_num) (by linarith)
  have h1 : CutoffProfile.derivBound * (2 / (r₂ - r₁)) * Clap ≤
      CutoffProfile.derivBound * (2 / (r₂ - r₁)) * Clap' :=
    mul_le_mul_of_nonneg_left hC (mul_nonneg CutoffProfile.derivBound_nonneg hk)
  have h2 : CutoffProfile.derivBound * (2 / (r₂ - r₁)) ^ 2 *
        Real.exp (2 * ((d : Real) ^ 2 * Real.sqrt K) * T) ≤
      CutoffProfile.derivBound * (2 / (r₂ - r₁)) ^ 2 *
        Real.exp (2 * ((d : Real) ^ 2 * Real.sqrt K) * T') :=
    mul_le_mul_of_nonneg_left (exp_window_mono d K hTT 2 (by norm_num))
      (mul_nonneg CutoffProfile.derivBound_nonneg (sq_nonneg _))
  unfold shiInitialCutoffB
  linarith

private theorem shiInitialCutoffD_mono {r₁ r₂ : Real} (hr : r₁ ≤ r₂) {C C' : Real}
    (h : C ≤ C') : shiInitialCutoffD r₁ r₂ C ≤ shiInitialCutoffD r₁ r₂ C' := by
  unfold shiInitialCutoffD
  exact mul_le_mul_of_nonneg_left h
    (mul_nonneg (Real.sqrt_nonneg _) (div_nonneg (by norm_num) (by linarith)))

private theorem shiFirstDerivativeLocalBound_mono (d : ℕ) {a : Real} (ha : 32 ≤ a)
    {T T' A A' B B' Dc Dc' cn cn' : Real}
    (hT : 0 ≤ T) (hTT : T ≤ T') (hA : 0 ≤ A) (hAA : A ≤ A') (hB : 0 ≤ B) (hBB : B ≤ B')
    (hD : 0 ≤ Dc) (hDD : Dc ≤ Dc') (hcn : 0 ≤ cn) (hcncn : cn ≤ cn') :
    shiFirstDerivativeLocalBound d a T A B Dc cn ≤
      shiFirstDerivativeLocalBound d a T' A' B' Dc' cn' := by
  have hapos : (0 : Real) < a := by linarith
  have hcoup0 : (0 : Real) ≤ shiFirstDerivativeCoupling a cn :=
    div_nonneg hcn (Real.sqrt_nonneg _)
  have hcoup : shiFirstDerivativeCoupling a cn ≤ shiFirstDerivativeCoupling a cn' := by
    unfold shiFirstDerivativeCoupling
    exact div_le_div_right_of_nonneg hcncn (Real.sqrt_nonneg _)
  have hb := bernsteinSelfCoupledBound_mono (shiFirstTimeCoeff_pos ha)
    (shiFirstTimeConst_mono d a hT hTT) hT hTT hD hDD hcoup0 hcoup hA hAA hB hBB
  unfold shiFirstDerivativeLocalBound
  exact Real.sqrt_le_sqrt (div_le_div_right_of_nonneg hb hapos.le)

theorem shiLocalFirstDerivativeConst_mono (d : ℕ) {T T' R Clap Clap' Cconn Cconn' : Real}
    (hR : 0 < R) (hT : 0 ≤ T) (hTT : T ≤ T') (hClap : 0 ≤ Clap) (hClapClap : Clap ≤ Clap')
    (hCconn : 0 ≤ Cconn) (hCconnCconn : Cconn ≤ Cconn') :
    shiLocalFirstDerivativeConst d T R Clap Cconn ≤
      shiLocalFirstDerivativeConst d T' R Clap' Cconn' := by
  have hr : 3 * R / 4 ≤ R := by linarith
  unfold shiLocalFirstDerivativeConst shiFirstDerivativeLocalConst
  refine shiFirstDerivativeLocalBound_mono d (by norm_num) hT hTT
    (shiInitialCutoffA_nonneg _ _ _ _ _) (shiInitialCutoffA_mono d 1 _ _ hTT)
    (shiInitialCutoffB_nonneg d hr hClap) (shiInitialCutoffB_mono d 1 hr hTT hClapClap)
    (shiInitialCutoffD_nonneg hr hCconn) (shiInitialCutoffD_mono hr hCconnCconn)
    (by positivity) ?_
  exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hTT) (by norm_num)

theorem shiFixedCutoffError_mono (d : ℕ) {r₁ r₂ : Real} (hr : r₁ ≤ r₂)
    {T T' Clap Clap' Cconn Cconn' Hb Hb' : Real}
    (hTT : T ≤ T') (hClap : Clap ≤ Clap') (hCconn : 0 ≤ Cconn)
    (hCconnCconn : Cconn ≤ Cconn') (hHb : 0 ≤ Hb) (hHbHb : Hb ≤ Hb') :
    shiFixedCutoffError d T r₁ r₂ Clap Cconn Hb ≤
      shiFixedCutoffError d T' r₁ r₂ Clap' Cconn' Hb' := by
  have hsqrt : 2 * Real.sqrt T ≤ 2 * Real.sqrt T' :=
    mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hTT) (by norm_num)
  have hweight : 2 * Real.sqrt T * Hb ≤ 2 * Real.sqrt T' * Hb' :=
    mul_le_mul hsqrt hHbHb hHb (by positivity)
  have hprod : shiInitialCutoffD r₁ r₂ Cconn * (2 * Real.sqrt T * Hb) ≤
      shiInitialCutoffD r₁ r₂ Cconn' * (2 * Real.sqrt T' * Hb') :=
    mul_le_mul (shiInitialCutoffD_mono hr hCconnCconn) hweight
      (mul_nonneg (mul_nonneg (by norm_num) (Real.sqrt_nonneg _)) hHb)
      (shiInitialCutoffD_nonneg hr (le_trans hCconn hCconnCconn))
  have hB := shiInitialCutoffB_mono d 1 hr hTT hClap
  unfold shiFixedCutoffError
  exact max_le_max (shiInitialCutoffA_mono d 1 _ _ hTT) (by linarith)



private theorem sq_le_sq_of_nonneg {A A' : Real} (hA : 0 ≤ A) (hAA : A ≤ A') :
    A ^ 2 ≤ A' ^ 2 := by nlinarith


private theorem shiShiftRatio_mono {A A' : Real} (hA : 0 ≤ A) (hAA : A ≤ A') :
    (1 + 5 * A ^ 2) / (1 + 4 * A ^ 2) ≤ (1 + 5 * A' ^ 2) / (1 + 4 * A' ^ 2) := by
  have hs : (0 : Real) < 1 + 4 * A ^ 2 := by positivity
  have hs' : (0 : Real) < 1 + 4 * A' ^ 2 := by positivity
  have hsq := sq_le_sq_of_nonneg hA hAA
  rw [div_le_div_iff₀ hs hs']
  nlinarith

private theorem shiShiftQuartic_mono {A A' : Real} (hA : 0 ≤ A) (hAA : A ≤ A') :
    (1 + 5 * A ^ 2) ^ 4 / (1 + 4 * A ^ 2) ≤ (1 + 5 * A' ^ 2) ^ 4 / (1 + 4 * A' ^ 2) := by
  have hs : (0 : Real) < 1 + 4 * A ^ 2 := by positivity
  have hs' : (0 : Real) < 1 + 4 * A' ^ 2 := by positivity
  have hsq := sq_le_sq_of_nonneg hA hAA
  have hkey : (1 + 5 * A ^ 2) * (1 + 4 * A' ^ 2) ≤ (1 + 5 * A' ^ 2) * (1 + 4 * A ^ 2) := by
    nlinarith
  have hcube : (1 + 5 * A ^ 2) ^ 3 ≤ (1 + 5 * A' ^ 2) ^ 3 :=
    pow_le_pow_left₀ (by positivity) (by linarith) 3
  rw [div_le_div_iff₀ hs hs']
  calc (1 + 5 * A ^ 2) ^ 4 * (1 + 4 * A' ^ 2)
      = (1 + 5 * A ^ 2) ^ 3 * ((1 + 5 * A ^ 2) * (1 + 4 * A' ^ 2)) := by ring
    _ ≤ (1 + 5 * A' ^ 2) ^ 3 * ((1 + 5 * A' ^ 2) * (1 + 4 * A ^ 2)) :=
        mul_le_mul hcube hkey (by positivity) (by positivity)
    _ = (1 + 5 * A' ^ 2) ^ 4 * (1 + 4 * A ^ 2) := by ring

private theorem shiHigherLYCoeff_mono (d m : ℕ) {T T' A A' : Real}
    (hTT : T ≤ T') (hA : 0 ≤ A) (hAA : A ≤ A') :
    shiHigherLYCoeff d m T A ≤ shiHigherLYCoeff d m T' A' := by
  have hc := rmTowerCost_nonneg d (m + 1)
  have hm : (0 : Real) ≤ (m : Real) := Nat.cast_nonneg m
  have hsq := sq_le_sq_of_nonneg hA hAA
  have h : rmTowerCost d (m + 1) * ((m : Real) + 2) * (T + A ^ 2 / 2) ≤
      rmTowerCost d (m + 1) * ((m : Real) + 2) * (T' + A' ^ 2 / 2) :=
    mul_le_mul_of_nonneg_left (by linarith) (mul_nonneg hc (by linarith))
  unfold shiHigherLYCoeff
  linarith

private theorem shiHigherLXConst_mono (d m : ℕ) {A A' : Real} (hA : 0 ≤ A) (hAA : A ≤ A') :
    shiHigherLXConst d m A ≤ shiHigherLXConst d m A' := by
  have hc := rmTowerCost_nonneg d m
  have hm : (0 : Real) ≤ (m : Real) := Nat.cast_nonneg m
  have hA' : (0 : Real) ≤ A' := le_trans hA hAA
  have hcube : A ^ 3 ≤ A' ^ 3 := pow_le_pow_left₀ hA hAA 3
  unfold shiHigherLXConst
  exact mul_le_mul_of_nonneg_left hcube (mul_nonneg hc (by linarith))

private theorem shiHigherFConst_mono (d m : ℕ) {T T' A A' : Real}
    (hT : 0 ≤ T) (hTT : T ≤ T') (hA : 0 ≤ A) (hAA : A ≤ A') :
    shiHigherFConst d m T A ≤ shiHigherFConst d m T' A' := by
  have hLY := shiHigherLYCoeff_mono d m hTT hA hAA
  have hLY0 := shiHigherLYCoeff_nonneg hT d m A
  have hLX := shiHigherLXConst_mono d m hA hAA
  have hLX0 := shiHigherLXConst_nonneg hA d m
  have hsq := sq_le_sq_of_nonneg hA hAA
  have hm : (0 : Real) ≤ (m : Real) := Nat.cast_nonneg m
  have h1 : (1 + 5 * A ^ 2) * shiHigherLYCoeff d m T A ≤
      (1 + 5 * A' ^ 2) * shiHigherLYCoeff d m T' A' :=
    mul_le_mul (by linarith) hLY hLY0 (by nlinarith [sq_nonneg A'])
  have h2 : (m : Real) * A ^ 2 ≤ (m : Real) * A' ^ 2 := mul_le_mul_of_nonneg_left hsq hm
  have h3 : shiHigherLXConst d m A * T ≤ shiHigherLXConst d m A' * T' :=
    mul_le_mul hLX hTT hT (le_trans hLX0 hLX)
  unfold shiHigherFConst
  linarith

private theorem shiHigherBernsteinConst_mono (d m : ℕ) {T T' A A' : Real}
    (hT : 0 ≤ T) (hTT : T ≤ T') (hA : 0 ≤ A) (hAA : A ≤ A') :
    shiHigherBernsteinConst d m T A ≤ shiHigherBernsteinConst d m T' A' := by
  have hT' : (0 : Real) ≤ T' := le_trans hT hTT
  have hA' : (0 : Real) ≤ A' := le_trans hA hAA
  have hF := shiHigherFConst_nonneg hT hA d m
  have hFF := shiHigherFConst_mono d m hT hTT hA hAA
  have hF' := shiHigherFConst_nonneg hT' hA' d m
  have hrho := shiShiftRatio_mono hA hAA
  have hrho0 : (0 : Real) ≤ (1 + 5 * A ^ 2) / (1 + 4 * A ^ 2) := by positivity
  have heq : ∀ X Y : Real,
      5 * (1 + 5 * Y ^ 2) ^ 2 / 4 * (X / shiHigherShift Y) ^ 2 =
        5 / 4 * ((1 + 5 * Y ^ 2) / (1 + 4 * Y ^ 2) * X) ^ 2 := by
    intro X Y
    unfold shiHigherShift
    ring
  have hmul : (1 + 5 * A ^ 2) / (1 + 4 * A ^ 2) * shiHigherFConst d m T A ≤
      (1 + 5 * A' ^ 2) / (1 + 4 * A' ^ 2) * shiHigherFConst d m T' A' :=
    mul_le_mul hrho hFF hF (le_trans hrho0 hrho)
  have hmul0 : (0 : Real) ≤ (1 + 5 * A ^ 2) / (1 + 4 * A ^ 2) * shiHigherFConst d m T A :=
    mul_nonneg hrho0 hF
  have hsq : ((1 + 5 * A ^ 2) / (1 + 4 * A ^ 2) * shiHigherFConst d m T A) ^ 2 ≤
      ((1 + 5 * A' ^ 2) / (1 + 4 * A' ^ 2) * shiHigherFConst d m T' A') ^ 2 :=
    pow_le_pow_left₀ hmul0 hmul 2
  have hlast : shiHigherFConst d m T A * T ^ 2 ≤ shiHigherFConst d m T' A' * T' ^ 2 :=
    mul_le_mul hFF (by nlinarith) (by positivity) hF'
  unfold shiHigherBernsteinConst
  rw [heq (shiHigherFConst d m T A) A, heq (shiHigherFConst d m T' A') A']
  linarith

private theorem shiHigherStepBound_eq_max (d m : ℕ) {T A e : Real}
    (hT : 0 ≤ T) (hA : 0 ≤ A) (he : 0 ≤ e) :
    shiHigherStepBound d m T A e =
      max (1 / (1 + 4 * A ^ 2))
        (25 * ((1 + 5 * A ^ 2) ^ 4 / (1 + 4 * A ^ 2)) *
          max (12 * (e * T)) (4 * shiHigherBernsteinConst d m T A) ^ 2) := by
  have hs : (0 : Real) < 1 + 4 * A ^ 2 := by positivity
  have hz : (0 : Real) < 5 * (1 + 5 * A ^ 2) ^ 2 := by positivity
  have hC : 0 ≤ shiHigherBernsteinConst d m T A := shiHigherBernsteinConst_nonneg hT hA d m
  have heT : (0 : Real) ≤ 12 * (e * T) := by positivity
  have hW0 : (0 : Real) ≤ max (12 * (e * T)) (4 * shiHigherBernsteinConst d m T A) :=
    le_trans heT (le_max_left _ _)
  have hdiv : ∀ y : Real, y / shiHigherBernsteinCoeff A = y * (5 * (1 + 5 * A ^ 2) ^ 2) := by
    intro y
    have hne : (5 * (1 + 5 * A ^ 2) ^ 2 : Real) ≠ 0 := ne_of_gt hz
    unfold shiHigherBernsteinCoeff
    field_simp
  have hnum : (4 : Real) * (3 * e * T) = 12 * (e * T) := by ring
  have hzero : (4 : Real) * 0 = 0 := by ring
  unfold shiHigherStepBound bernsteinMaximumBound polynomialAbsorptionBound shiHigherShift
  rw [hzero, hnum]
  simp only [hdiv]
  rw [max_mul_right_of_nonneg hz.le, zero_mul,
    max_eq_right (mul_nonneg hW0 hz.le), max_one_sq_of_nonneg (mul_nonneg hW0 hz.le),
    max_div_right_of_pos hs]
  congr 1
  rw [mul_pow]
  field_simp
  ring

private theorem shiHigherStepBound_le_max_one (d m : ℕ) {T T' A A' e e' : Real}
    (hT : 0 ≤ T) (hTT : T ≤ T') (hA : 0 ≤ A) (hAA : A ≤ A') (he : 0 ≤ e) (hee : e ≤ e') :
    shiHigherStepBound d m T A e ≤ max 1 (shiHigherStepBound d m T' A' e') := by
  have hT' : (0 : Real) ≤ T' := le_trans hT hTT
  have hA' : (0 : Real) ≤ A' := le_trans hA hAA
  have he' : (0 : Real) ≤ e' := le_trans he hee
  have hq := shiShiftQuartic_mono hA hAA
  have hq0 : (0 : Real) ≤ (1 + 5 * A ^ 2) ^ 4 / (1 + 4 * A ^ 2) := by positivity
  have hCC : shiHigherBernsteinConst d m T A ≤ shiHigherBernsteinConst d m T' A' :=
    shiHigherBernsteinConst_mono d m hT hTT hA hAA
  have heTT : 12 * (e * T) ≤ 12 * (e' * T') := by
    have : e * T ≤ e' * T' := mul_le_mul hee hTT hT he'
    linarith
  have hWW : max (12 * (e * T)) (4 * shiHigherBernsteinConst d m T A) ≤
      max (12 * (e' * T')) (4 * shiHigherBernsteinConst d m T' A') :=
    max_le_max heTT (by linarith)
  have hW0 : (0 : Real) ≤ max (12 * (e * T)) (4 * shiHigherBernsteinConst d m T A) :=
    le_trans (by positivity) (le_max_left _ _)
  have hWsq : max (12 * (e * T)) (4 * shiHigherBernsteinConst d m T A) ^ 2 ≤
      max (12 * (e' * T')) (4 * shiHigherBernsteinConst d m T' A') ^ 2 :=
    pow_le_pow_left₀ hW0 hWW 2
  rw [shiHigherStepBound_eq_max d m hT hA he, shiHigherStepBound_eq_max d m hT' hA' he']
  refine max_le ?_ ?_
  · refine le_trans ?_ (le_max_left _ _)
    rw [div_le_one (by positivity)]
    nlinarith
  · refine le_trans ?_ (le_trans (le_max_right (1 / (1 + 4 * A' ^ 2)) _) (le_max_right 1 _))
    exact mul_le_mul (by linarith) hWsq (sq_nonneg _) (by positivity)

theorem shiAllOrdersBound_mono (d : ℕ) {T T' : Real} {eps eps' : ℕ → Real}
    (hT : 0 ≤ T) (hTT : T ≤ T') (heps : ∀ j, 0 ≤ eps j) (hepsle : ∀ j, eps j ≤ eps' j)
    (m : ℕ) :
    shiAllOrdersBound d T eps m ≤ shiAllOrdersBound d T' eps' m := by
  induction m with
  | zero => rw [shiAllOrdersBound_zero, shiAllOrdersBound_zero]
  | succ m ih =>
      have hprev0 : (0 : Real) ≤ shiAllOrdersBound d T eps m :=
        shiAllOrdersBound_nonneg d T eps m
      have hprev1 : (1 : Real) ≤ shiAllOrdersBound d T' eps' m :=
        one_le_shiAllOrdersBound d T' eps' m
      have hstep := shiHigherStepBound_le_max_one d m hT hTT hprev0 ih (heps m) (hepsle m)
      rw [shiAllOrdersBound_succ, shiAllOrdersBound_succ]
      refine max_le (le_trans ih (le_max_left _ _)) ?_
      refine le_trans (Real.sqrt_le_sqrt hstep) ?_
      refine le_trans (sqrt_max_one_le _) ?_
      exact max_le (le_trans hprev1 (le_max_left _ _)) (le_max_right _ _)


theorem shiLocalClap_mono (d : ℕ) {T T' R : Real} (hR : 0 < R) (hTT : T ≤ T') :
    shiLocalClap d T R ≤ shiLocalClap d T' R := by
  have h4 : (0 : Real) ≤ 4 / R + 1 := by
    have := div_nonneg (by norm_num : (0 : Real) ≤ 4) hR.le
    linarith
  have hexp : Real.exp (2 * (d : Real) ^ 2 * T) ≤ Real.exp (2 * (d : Real) ^ 2 * T') := by
    refine Real.exp_le_exp.mpr ?_
    nlinarith [sq_nonneg ((d : Real))]
  unfold shiLocalClap
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hexp (Nat.cast_nonneg d)) h4

theorem shiLocalCconn_mono (d : ℕ) {T T' : Real} (hTT : T ≤ T') :
    shiLocalCconn d T ≤ shiLocalCconn d T' := by
  have hexp2 : Real.exp (2 * (d : Real) ^ 2 * T) ≤ Real.exp (2 * (d : Real) ^ 2 * T') := by
    refine Real.exp_le_exp.mpr ?_
    nlinarith [sq_nonneg ((d : Real))]
  have hexp3 : Real.exp (3 * (d : Real) ^ 2 * T) ≤ Real.exp (3 * (d : Real) ^ 2 * T') := by
    refine Real.exp_le_exp.mpr ?_
    nlinarith [sq_nonneg ((d : Real))]
  have h1 : (d : Real) * Real.exp (2 * (d : Real) ^ 2 * T) ≤
      (d : Real) * Real.exp (2 * (d : Real) ^ 2 * T') :=
    mul_le_mul_of_nonneg_left hexp2 (Nat.cast_nonneg d)
  have h2 : 3 * Real.sqrt ((d : Real) ^ 5) * Real.exp (3 * (d : Real) ^ 2 * T) ≤
      3 * Real.sqrt ((d : Real) ^ 5) * Real.exp (3 * (d : Real) ^ 2 * T') :=
    mul_le_mul_of_nonneg_left hexp3 (by positivity)
  unfold shiLocalCconn
  exact mul_le_mul h1 h2 (by positivity) (by positivity)

private theorem shiLocalCutoffError_nonneg (d : ℕ) (T R Clap Cconn Hb : Real) (j : ℕ) :
    0 ≤ shiLocalCutoffError d T R Clap Cconn Hb j :=
  shiFixedCutoffError_nonneg _ _ _ _ _ _ _

theorem shiLocalCutoffError_mono (d : ℕ) {T T' R Clap Clap' Cconn Cconn' Hb Hb' : Real}
    (hR : 0 < R) (hTT : T ≤ T') (hClap : Clap ≤ Clap') (hCconn : 0 ≤ Cconn)
    (hCconnCconn : Cconn ≤ Cconn') (hHb : 0 ≤ Hb) (hHbHb : Hb ≤ Hb') (j : ℕ) :
    shiLocalCutoffError d T R Clap Cconn Hb j ≤
      shiLocalCutoffError d T' R Clap' Cconn' Hb' j := by
  unfold shiLocalCutoffError
  exact shiFixedCutoffError_mono d (shiLocalRadius_succ_lt hR j).le hTT hClap hCconn
    hCconnCconn hHb hHbHb

theorem shiLocalUniformBound_mono (d m : ℕ) {T T' R : Real} (hR : 0 < R) (hT : 0 ≤ T)
    (hTT : T ≤ T') :
    shiLocalUniformBound d m T R ≤ shiLocalUniformBound d m T' R := by
  have hClap := shiLocalClap_mono d hR hTT
  have hClap0 := shiLocalClap_nonneg d T hR
  have hCconn := shiLocalCconn_mono d hTT
  have hCconn0 := shiLocalCconn_nonneg d T
  have hHb := shiLocalFirstDerivativeConst_mono d hR hT hTT hClap0 hClap hCconn0 hCconn
  have hHb0 := shiLocalFirstDerivativeConst_nonneg d T R (shiLocalClap d T R)
    (shiLocalCconn d T)
  unfold shiLocalUniformBound shiLocalAllOrdersConst
  exact shiAllOrdersBound_mono d hT hTT
    (fun j => shiLocalCutoffError_nonneg d T R _ _ _ j)
    (fun j => shiLocalCutoffError_mono d hR hTT hClap hCconn0 hCconn hHb0 hHb j) m

private theorem sqrt_le_div_of_weighted (m : ℕ) {a N C : Real} (ha : 0 < a)
    (h : Real.sqrt (a ^ m * N) ≤ C) :
    Real.sqrt N ≤ C / Real.sqrt a ^ m := by
  have hpow : (0 : Real) < Real.sqrt a ^ m := pow_pos (Real.sqrt_pos.mpr ha) m
  rw [Real.sqrt_mul (pow_nonneg ha.le m), sqrt_pow_of_nonneg ha.le m] at h
  rw [le_div_iff₀ hpow, mul_comm]
  exact h

end ScalarMonotonicity

section Shift

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I ∞ M] [IsManifold I 1 M] [IsManifold I 2 M]
variable [SigmaCompactSpace M] [T2Space M]

omit [I.Boundaryless] [IsManifold I 2 M] [SigmaCompactSpace M] [T2Space M] in
private theorem timeShift_family_connection
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) (τ s : Real) :
    (S.timeShift τ).family.connection s = S.family.connection (s + τ) := rfl

omit [I.Boundaryless] [SigmaCompactSpace M] in
private theorem nablaKRm04Field_timeShift
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) (τ s : Real) (k : ℕ) :
    nablaKRm04Field (I := I) (S.timeShift τ) s k =
      nablaKRm04Field (I := I) S (s + τ) k := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [nablaKRm04Field_succ, ih, timeShift_family_connection]

omit [I.Boundaryless] [SigmaCompactSpace M] in
private theorem nablaKRm04NormSqIntrinsic_timeShift
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) (τ : Real) (k : ℕ)
    (s : Real) (x : M) :
    nablaKRm04NormSqIntrinsic (I := I) (S.timeShift τ) k s x =
      nablaKRm04NormSqIntrinsic (I := I) S k (s + τ) x := by
  unfold nablaKRm04NormSqIntrinsic
  rw [nablaKRm04Field_timeShift]
  rfl

def timeShiftSolution
    {alpha omega : Real} {halphaomega : alpha < omega}
    (S : SolutionOn (I := I) (M := M)
      (RealTimeInterval.closedOpen alpha omega halphaomega)) (τ : Real) :
    SolutionOn (I := I) (M := M)
      (RealTimeInterval.closedOpen (alpha - τ) (omega - τ)
        (sub_lt_sub_right halphaomega τ)) :=
  (S.timeShift τ).cast _

omit [FiniteDimensional Real E] [CompleteSpace E] [I.Boundaryless] [IsManifold I 1 M]
  [IsManifold I 2 M] [SigmaCompactSpace M] [T2Space M] in
theorem timeShiftSolution_metric
    {alpha omega : Real} {halphaomega : alpha < omega}
    (S : SolutionOn (I := I) (M := M)
      (RealTimeInterval.closedOpen alpha omega halphaomega)) (τ s : Real) :
    (timeShiftSolution (I := I) S τ).base.metric s = S.base.metric (s + τ) := rfl

omit [I.Boundaryless] [IsManifold I 2 M] [SigmaCompactSpace M] in
theorem isSolutionOn_timeShiftSolution
    {alpha omega : Real} {halphaomega : alpha < omega}
    {S : SolutionOn (I := I) (M := M)
      (RealTimeInterval.closedOpen alpha omega halphaomega)}
    (hS : IsSolutionOn (I := I) S) (τ : Real) :
    IsSolutionOn (I := I) (timeShiftSolution (I := I) S τ) := by
  refine isSolutionOn_cast (isSolutionOn_timeShift (I := I) hS τ) ?_ ?_
  · ext s
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨by linarith, by linarith⟩
    · rintro ⟨h1, h2⟩
      exact ⟨by linarith, by linarith⟩
  · ext s
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨by linarith, by linarith⟩
    · rintro ⟨h1, h2⟩
      exact ⟨by linarith, by linarith⟩

omit [I.Boundaryless] [SigmaCompactSpace M] in
theorem nablaKRm04NormSqIntrinsic_timeShiftSolution
    {alpha omega : Real} {halphaomega : alpha < omega}
    (S : SolutionOn (I := I) (M := M)
      (RealTimeInterval.closedOpen alpha omega halphaomega)) (τ : Real) (k : ℕ)
    (s : Real) (x : M) :
    nablaKRm04NormSqIntrinsic (I := I) (timeShiftSolution (I := I) S τ) k s x =
      nablaKRm04NormSqIntrinsic (I := I) S k (s + τ) x := by
  unfold timeShiftSolution
  rw [nablaKRm04NormSqIntrinsic_cast, nablaKRm04NormSqIntrinsic_timeShift]

end Shift



section Global

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [FiniteDimensional Real E] [NeZero (Module.finrank Real E)] [CompleteSpace E]
variable [I.Boundaryless]
variable [IsManifold I 1 M] [IsManifold I 2 M] [IsManifold I ∞ M]
variable [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]
variable [VectorBundle Real E (TangentSpace I : M → Type _)]

def shiCompleteGlobalBound (d m : ℕ) : Real := shiLocalUniformBound d m 1 1


theorem shiCompleteGlobalBound_nonneg (d m : ℕ) : 0 ≤ shiCompleteGlobalBound d m :=
  shiLocalUniformBound_nonneg _ _ _ _

private theorem shi_centre_bound_of_solution
    {alpha omega : Real} {halphaomega : alpha < omega}
    (S : SolutionOn (I := I) (M := M)
      (RealTimeInterval.closedOpen alpha omega halphaomega))
    (hS : IsSolutionOn (I := I) S) {T K : Real} (x : M)
    (halpha : alpha < 0) (hT : 0 < T) (hTomega : T < omega) (hK : 0 < K)
    (hKT : K * T ≤ 1)
    (hcomplete : RiemannianMetricComplete (I := I) (S.base.metric 0))
    (hcurv : ∀ s ∈ Set.Icc (0 : Real) T, ∀ y : M,
      nablaKRm04NormSqIntrinsic (I := I) S 0 s y ≤ K ^ 2) (m : ℕ) :
    Real.sqrt (T ^ m * nablaKRm04NormSqIntrinsic (I := I) S m T x) ≤
      shiCompleteGlobalBound (Module.finrank Real E) m * K := by
  have h0 : (0 : Real) ∈
      (RealTimeInterval.closedOpen alpha omega halphaomega).carrier :=
    ⟨halpha.le, lt_trans hT hTomega⟩
  have hball : IsCompact {y : M |
      riemannianEDistOf (I := I) (S.base.metric 0) x y ≤
        ENNReal.ofReal (1 / Real.sqrt K)} :=
    RiemannianMetricComplete.closedEBall_isCompact (I := I) hcomplete x (1 / Real.sqrt K)
  have hcentre : riemannianEDistOf (I := I) (S.base.metric 0) x x ≤
      ENNReal.ofReal (1 / (2 * Real.sqrt K)) := by
    rw [riemannianEDistOf_self]
    simp
  have hlocal := (shi_local_all_orders_curvature_scale_of_solution_uniform (I := I) S hS
    (R := 1) x halpha hK hT hTomega one_pos h0 hball
    (fun s hs y _ => hcurv s hs y) m T ⟨hT, le_rfl⟩ x hcentre).1
  have hmono : shiLocalUniformBound (Module.finrank Real E) m (K * T) 1 ≤
      shiCompleteGlobalBound (Module.finrank Real E) m :=
    shiLocalUniformBound_mono _ _ one_pos (mul_nonneg hK.le hT.le) hKT
  exact le_trans hlocal (mul_le_mul_of_nonneg_right hmono hK.le)

theorem shi_complete_global_of_solution
    {alpha omega : Real} {halphaomega : alpha < omega}
    (S : SolutionOn (I := I) (M := M)
      (RealTimeInterval.closedOpen alpha omega halphaomega))
    (hS : IsSolutionOn (I := I) S) {T K : Real}
    (halpha : alpha < 0) (hTomega : T < omega) (hK : 0 < K)
    (hcomplete : RiemannianMetricComplete (I := I) (S.base.metric 0))
    (hcurv : ∀ s ∈ Set.Icc (0 : Real) T, ∀ y : M,
      nablaKRm04NormSqIntrinsic (I := I) S 0 s y ≤ K ^ 2) :
    ∀ m : ℕ, ∀ t ∈ Set.Ioc (0 : Real) T, ∀ x : M,
      Real.sqrt (nablaKRm04NormSqIntrinsic (I := I) S m t x) ≤
        shiCompleteGlobalBound (Module.finrank Real E) m * K /
          Real.sqrt (min t K⁻¹) ^ m := by
  intro m t ht x
  have hKinv : (0 : Real) < K⁻¹ := inv_pos.mpr hK
  have htomega : t < omega := lt_of_le_of_lt ht.2 hTomega
  rcases le_total t K⁻¹ with hle | hle
  · rw [min_eq_left hle]
    refine sqrt_le_div_of_weighted m ht.1 ?_
    refine shi_centre_bound_of_solution (I := I) S hS x halpha ht.1 htomega hK ?_
      hcomplete ?_ m
    · calc K * t ≤ K * K⁻¹ := mul_le_mul_of_nonneg_left hle hK.le
        _ = 1 := mul_inv_cancel₀ (ne_of_gt hK)
    · exact fun s hs y => hcurv s ⟨hs.1, le_trans hs.2 ht.2⟩ y
  · rw [min_eq_right hle]
    have hτ0 : 0 ≤ t - K⁻¹ := by linarith
    have hτt : t - K⁻¹ ≤ t := by linarith
    have hslab : Set.Icc (0 : Real) (t - K⁻¹) ⊆
        (RealTimeInterval.closedOpen alpha omega halphaomega).carrier := by
      intro s hs
      exact ⟨by linarith [hs.1], by linarith [hs.2]⟩
    have hreg : Set.Ioc (0 : Real) (t - K⁻¹) ⊆
        (RealTimeInterval.closedOpen alpha omega halphaomega).regular := by
      intro s hs
      exact ⟨by linarith [hs.1], by linarith [hs.2]⟩
    have hric : ∀ s ∈ Set.Icc (0 : Real) (t - K⁻¹), ∀ y : M, ∀ v : TangentSpace I y,
        |ricciTensor (I := I) (S.base.metric s) y v v| ≤
          ((Module.finrank Real E : Real) ^ 2 * K) * (S.base.metric s).inner y v v := by
      intro s hs y v
      have hsT : s ∈ Set.Icc (0 : Real) T :=
        ⟨hs.1, by linarith [hs.2, ht.2]⟩
      have hcurv0 : normSq0S (I := I) (S.base.metric s) y 4 (S.base.rm04 s y) ≤ K ^ 2 := by
        simpa only [nablaKRm04NormSqIntrinsic, nablaKRm04Field_zero, Nat.add_zero] using
          hcurv s hsT y
      have hb := ricci_quadratic_form_bound_of_solution_curvature_bound (I := I) S y v hcurv0
      rwa [Real.sqrt_sq hK.le] at hb
    have hcompleteτ : RiemannianMetricComplete (I := I) (S.base.metric (t - K⁻¹)) :=
      complete_of_ricBound (I := I) S hS hslab hreg (by positivity) hric hcomplete
        ⟨hτ0, le_rfl⟩
    have hshiftcomplete : RiemannianMetricComplete (I := I)
        ((timeShiftSolution (I := I) S (t - K⁻¹)).base.metric 0) := by
      rw [timeShiftSolution_metric, zero_add]
      exact hcompleteτ
    have hcurvshift : ∀ s ∈ Set.Icc (0 : Real) K⁻¹, ∀ y : M,
        nablaKRm04NormSqIntrinsic (I := I)
          (timeShiftSolution (I := I) S (t - K⁻¹)) 0 s y ≤ K ^ 2 := by
      intro s hs y
      rw [nablaKRm04NormSqIntrinsic_timeShiftSolution]
      exact hcurv (s + (t - K⁻¹)) ⟨by linarith [hs.1], by linarith [hs.2, ht.2]⟩ y
    have hcore := shi_centre_bound_of_solution (I := I)
      (timeShiftSolution (I := I) S (t - K⁻¹))
      (isSolutionOn_timeShiftSolution (I := I) hS (t - K⁻¹)) x (by linarith) hKinv
      (by linarith) hK (le_of_eq (mul_inv_cancel₀ (ne_of_gt hK))) hshiftcomplete
      hcurvshift m
    rw [nablaKRm04NormSqIntrinsic_timeShiftSolution] at hcore
    have hsum : K⁻¹ + (t - K⁻¹) = t := by ring
    rw [hsum] at hcore
    exact sqrt_le_div_of_weighted m hKinv hcore

theorem shi_complete_global_sum_of_solution
    {alpha omega : Real} {halphaomega : alpha < omega}
    (S : SolutionOn (I := I) (M := M)
      (RealTimeInterval.closedOpen alpha omega halphaomega))
    (hS : IsSolutionOn (I := I) S) {T K : Real}
    (halpha : alpha < 0) (hTomega : T < omega) (hK : 0 < K)
    (hcomplete : RiemannianMetricComplete (I := I) (S.base.metric 0))
    (hcurv : ∀ s ∈ Set.Icc (0 : Real) T, ∀ y : M,
      nablaKRm04NormSqIntrinsic (I := I) S 0 s y ≤ K ^ 2) :
    ∀ m : ℕ, ∀ t ∈ Set.Ioc (0 : Real) T, ∀ x : M,
      Real.sqrt (nablaKRm04NormSqIntrinsic (I := I) S m t x) ≤
        shiCompleteGlobalBound (Module.finrank Real E) m * K *
          (1 / Real.sqrt t ^ m + Real.sqrt K ^ m) := by
  intro m t ht x
  have hKinv : (0 : Real) < K⁻¹ := inv_pos.mpr hK
  have hCK : (0 : Real) ≤ shiCompleteGlobalBound (Module.finrank Real E) m * K :=
    mul_nonneg (shiCompleteGlobalBound_nonneg _ _) hK.le
  have hmain := shi_complete_global_of_solution (I := I) S hS halpha hTomega hK
    hcomplete hcurv m t ht x
  have hsplit : 1 / Real.sqrt (min t K⁻¹) ^ m ≤
      1 / Real.sqrt t ^ m + Real.sqrt K ^ m := by
    have hpt : (0 : Real) ≤ 1 / Real.sqrt t ^ m := by positivity
    have hpK : (0 : Real) ≤ Real.sqrt K ^ m := by positivity
    rcases le_total t K⁻¹ with hle | hle
    · rw [min_eq_left hle]
      linarith
    · rw [min_eq_right hle, Real.sqrt_inv, inv_pow, one_div, inv_inv]
      linarith
  calc Real.sqrt (nablaKRm04NormSqIntrinsic (I := I) S m t x)
      ≤ shiCompleteGlobalBound (Module.finrank Real E) m * K /
          Real.sqrt (min t K⁻¹) ^ m := hmain
    _ = shiCompleteGlobalBound (Module.finrank Real E) m * K *
          (1 / Real.sqrt (min t K⁻¹) ^ m) := by
        rw [div_eq_mul_one_div]
    _ ≤ shiCompleteGlobalBound (Module.finrank Real E) m * K *
          (1 / Real.sqrt t ^ m + Real.sqrt K ^ m) :=
        mul_le_mul_of_nonneg_left hsplit hCK

theorem shi_positive_slab_of_solution
    {alpha omega : Real} {halphaomega : alpha < omega}
    (S : SolutionOn (I := I) (M := M)
      (RealTimeInterval.closedOpen alpha omega halphaomega))
    (hS : IsSolutionOn (I := I) S) {a₀ a b K : Real}
    (halpha : alpha < a₀) (ha₀ : a₀ < a) (hb : b < omega) (hK : 0 < K)
    (hcomplete : RiemannianMetricComplete (I := I) (S.base.metric a₀))
    (hcurv : ∀ s ∈ Set.Icc a₀ b, ∀ y : M,
      nablaKRm04NormSqIntrinsic (I := I) S 0 s y ≤ K ^ 2) :
    ∀ m : ℕ, ∀ t ∈ Set.Icc a b, ∀ x : M,
      Real.sqrt (nablaKRm04NormSqIntrinsic (I := I) S m t x) ≤
        shiCompleteGlobalBound (Module.finrank Real E) m * K *
          (1 / Real.sqrt (a - a₀) + Real.sqrt K) ^ m := by
  intro m t ht x
  have hKinv : (0 : Real) < K⁻¹ := inv_pos.mpr hK
  have haa : (0 : Real) < a - a₀ := by linarith
  have hCK : (0 : Real) ≤ shiCompleteGlobalBound (Module.finrank Real E) m * K :=
    mul_nonneg (shiCompleteGlobalBound_nonneg _ _) hK.le
  have hshiftcomplete : RiemannianMetricComplete (I := I)
      ((timeShiftSolution (I := I) S a₀).base.metric 0) := by
    rw [timeShiftSolution_metric, zero_add]
    exact hcomplete
  have hcurvshift : ∀ s ∈ Set.Icc (0 : Real) (b - a₀), ∀ y : M,
      nablaKRm04NormSqIntrinsic (I := I)
        (timeShiftSolution (I := I) S a₀) 0 s y ≤ K ^ 2 := by
    intro s hs y
    rw [nablaKRm04NormSqIntrinsic_timeShiftSolution]
    exact hcurv (s + a₀) ⟨by linarith [hs.1], by linarith [hs.2]⟩ y
  have hmain := shi_complete_global_of_solution (I := I) (timeShiftSolution (I := I) S a₀)
    (isSolutionOn_timeShiftSolution (I := I) hS a₀) (by linarith) (by linarith) hK
    hshiftcomplete hcurvshift m (t - a₀)
    ⟨by linarith [ht.1], by linarith [ht.2]⟩ x
  rw [nablaKRm04NormSqIntrinsic_timeShiftSolution, sub_add_cancel] at hmain
  have hstep : 1 / Real.sqrt (min (t - a₀) K⁻¹) ≤ 1 / Real.sqrt (a - a₀) + Real.sqrt K := by
    have hsqa : (0 : Real) < Real.sqrt (a - a₀) := Real.sqrt_pos.mpr haa
    have hsqK : (0 : Real) ≤ Real.sqrt K := Real.sqrt_nonneg K
    rcases le_total (a - a₀) K⁻¹ with hle | hle
    · have hmin : a - a₀ ≤ min (t - a₀) K⁻¹ := le_min (by linarith [ht.1]) hle
      have h1 : 1 / Real.sqrt (min (t - a₀) K⁻¹) ≤ 1 / Real.sqrt (a - a₀) :=
        one_div_le_one_div_of_le hsqa (Real.sqrt_le_sqrt hmin)
      linarith
    · have hmin : K⁻¹ ≤ min (t - a₀) K⁻¹ := le_min (by linarith [ht.1]) le_rfl
      have h1 : 1 / Real.sqrt (min (t - a₀) K⁻¹) ≤ 1 / Real.sqrt K⁻¹ :=
        one_div_le_one_div_of_le (Real.sqrt_pos.mpr hKinv) (Real.sqrt_le_sqrt hmin)
      have hinvK : 1 / Real.sqrt K⁻¹ = Real.sqrt K := by
        rw [Real.sqrt_inv, one_div, inv_inv]
      rw [hinvK] at h1
      have hpos : (0 : Real) ≤ 1 / Real.sqrt (a - a₀) := by positivity
      linarith
  have hpow : (1 / Real.sqrt (min (t - a₀) K⁻¹)) ^ m ≤
      (1 / Real.sqrt (a - a₀) + Real.sqrt K) ^ m :=
    pow_le_pow_left₀ (by positivity) hstep m
  calc Real.sqrt (nablaKRm04NormSqIntrinsic (I := I) S m t x)
      ≤ shiCompleteGlobalBound (Module.finrank Real E) m * K /
          Real.sqrt (min (t - a₀) K⁻¹) ^ m := hmain
    _ = shiCompleteGlobalBound (Module.finrank Real E) m * K *
          (1 / Real.sqrt (min (t - a₀) K⁻¹)) ^ m := by
        rw [div_pow, one_pow, div_eq_mul_one_div]
    _ ≤ shiCompleteGlobalBound (Module.finrank Real E) m * K *
          (1 / Real.sqrt (a - a₀) + Real.sqrt K) ^ m :=
        mul_le_mul_of_nonneg_left hpow hCK

private theorem eq_zero_of_le_mul_of_pos_le_one {v A : Real} (hv : 0 ≤ v) (hA : 0 ≤ A)
    (h : ∀ K : Real, 0 < K → K ≤ 1 → v ≤ A * K) : v = 0 := by
  refine le_antisymm (le_of_forall_pos_lt_add ?_) hv
  intro ε hε
  set K : Real := min 1 (ε / (2 * (A + 1))) with hKdef
  have hApos : (0 : Real) < A + 1 := by linarith
  have hKpos : 0 < K := lt_min one_pos (by positivity)
  have hK1 : K ≤ 1 := min_le_left _ _
  have hKle : K ≤ ε / (2 * (A + 1)) := min_le_right _ _
  calc v ≤ A * K := h K hKpos hK1
    _ ≤ A * (ε / (2 * (A + 1))) := by gcongr
    _ < 0 + ε := by
        rw [zero_add, mul_div_assoc', div_lt_iff₀ (by positivity)]
        nlinarith

theorem shi_complete_global_flat_of_solution
    {alpha omega : Real} {halphaomega : alpha < omega}
    (S : SolutionOn (I := I) (M := M)
      (RealTimeInterval.closedOpen alpha omega halphaomega))
    (hS : IsSolutionOn (I := I) S) {T : Real}
    (halpha : alpha < 0) (hTomega : T < omega)
    (hcomplete : RiemannianMetricComplete (I := I) (S.base.metric 0))
    (hflat : ∀ s ∈ Set.Icc (0 : Real) T, ∀ y : M,
      nablaKRm04NormSqIntrinsic (I := I) S 0 s y ≤ 0) :
    ∀ m : ℕ, ∀ t ∈ Set.Ioc (0 : Real) T, ∀ x : M,
      nablaKRm04NormSqIntrinsic (I := I) S m t x = 0 := by
  intro m t ht x
  have hv0 : 0 ≤ nablaKRm04NormSqIntrinsic (I := I) S m t x :=
    nablaKRm04NormSqIntrinsic_nonneg (I := I) S m t x
  have hC0 : 0 ≤ shiCompleteGlobalBound (Module.finrank Real E) m :=
    shiCompleteGlobalBound_nonneg _ _
  have hsqrt : Real.sqrt (nablaKRm04NormSqIntrinsic (I := I) S m t x) = 0 := by
    refine eq_zero_of_le_mul_of_pos_le_one (Real.sqrt_nonneg _)
      (A := shiCompleteGlobalBound (Module.finrank Real E) m * (1 / Real.sqrt t ^ m + 1))
      (by positivity) ?_
    intro K hK hK1
    have hcurv : ∀ s ∈ Set.Icc (0 : Real) T, ∀ y : M,
        nablaKRm04NormSqIntrinsic (I := I) S 0 s y ≤ K ^ 2 :=
      fun s hs y => (hflat s hs y).trans (by positivity)
    have h := shi_complete_global_sum_of_solution (I := I) S hS halpha hTomega hK hcomplete
      hcurv m t ht x
    have hsqK : Real.sqrt K ^ m ≤ 1 := by
      have h1 : Real.sqrt K ≤ 1 := by simpa using Real.sqrt_le_sqrt hK1
      exact pow_le_one₀ (Real.sqrt_nonneg K) h1
    calc Real.sqrt (nablaKRm04NormSqIntrinsic (I := I) S m t x)
        ≤ shiCompleteGlobalBound (Module.finrank Real E) m * K *
            (1 / Real.sqrt t ^ m + Real.sqrt K ^ m) := h
      _ ≤ shiCompleteGlobalBound (Module.finrank Real E) m * K *
            (1 / Real.sqrt t ^ m + 1) := by gcongr
      _ = shiCompleteGlobalBound (Module.finrank Real E) m *
            (1 / Real.sqrt t ^ m + 1) * K := by ring
  exact le_antisymm (Real.sqrt_eq_zero'.mp hsqrt) hv0

theorem shi_positive_slab_flat_of_solution
    {alpha omega : Real} {halphaomega : alpha < omega}
    (S : SolutionOn (I := I) (M := M)
      (RealTimeInterval.closedOpen alpha omega halphaomega))
    (hS : IsSolutionOn (I := I) S) {a₀ a b : Real}
    (halpha : alpha < a₀) (ha₀ : a₀ < a) (hb : b < omega)
    (hcomplete : RiemannianMetricComplete (I := I) (S.base.metric a₀))
    (hflat : ∀ s ∈ Set.Icc a₀ b, ∀ y : M,
      nablaKRm04NormSqIntrinsic (I := I) S 0 s y ≤ 0) :
    ∀ m : ℕ, ∀ t ∈ Set.Icc a b, ∀ x : M,
      nablaKRm04NormSqIntrinsic (I := I) S m t x = 0 := by
  intro m t ht x
  have hv0 : 0 ≤ nablaKRm04NormSqIntrinsic (I := I) S m t x :=
    nablaKRm04NormSqIntrinsic_nonneg (I := I) S m t x
  have hC0 : 0 ≤ shiCompleteGlobalBound (Module.finrank Real E) m :=
    shiCompleteGlobalBound_nonneg _ _
  have hsqrt : Real.sqrt (nablaKRm04NormSqIntrinsic (I := I) S m t x) = 0 := by
    refine eq_zero_of_le_mul_of_pos_le_one (Real.sqrt_nonneg _)
      (A := shiCompleteGlobalBound (Module.finrank Real E) m *
        (1 / Real.sqrt (a - a₀) + 1) ^ m)
      (by positivity) ?_
    intro K hK hK1
    have hcurv : ∀ s ∈ Set.Icc a₀ b, ∀ y : M,
        nablaKRm04NormSqIntrinsic (I := I) S 0 s y ≤ K ^ 2 :=
      fun s hs y => (hflat s hs y).trans (by positivity)
    have h := shi_positive_slab_of_solution (I := I) S hS halpha ha₀ hb hK hcomplete
      hcurv m t ht x
    have hsqK : Real.sqrt K ≤ 1 := by simpa using Real.sqrt_le_sqrt hK1
    have hpow : (1 / Real.sqrt (a - a₀) + Real.sqrt K) ^ m ≤
        (1 / Real.sqrt (a - a₀) + 1) ^ m := by
      gcongr
    calc Real.sqrt (nablaKRm04NormSqIntrinsic (I := I) S m t x)
        ≤ shiCompleteGlobalBound (Module.finrank Real E) m * K *
            (1 / Real.sqrt (a - a₀) + Real.sqrt K) ^ m := h
      _ ≤ shiCompleteGlobalBound (Module.finrank Real E) m * K *
            (1 / Real.sqrt (a - a₀) + 1) ^ m := by gcongr
      _ = shiCompleteGlobalBound (Module.finrank Real E) m *
            (1 / Real.sqrt (a - a₀) + 1) ^ m * K := by ring
  exact le_antisymm (Real.sqrt_eq_zero'.mp hsqrt) hv0

end Global

end DifferentialGeometry.PDE.RicciFlow

end
