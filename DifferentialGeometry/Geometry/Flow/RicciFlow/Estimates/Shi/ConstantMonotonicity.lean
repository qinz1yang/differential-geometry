import DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.Shi.LaplacianInputRegularWindow

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

theorem shiHigherBernsteinConst_mono (d m : ℕ) {T T' A A' : Real}
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


theorem shiHigherBernsteinConst_mono_time (d m : ℕ) (Astar : Real) (hA : 0 ≤ Astar) :
    MonotoneOn (fun T => shiHigherBernsteinConst d m T Astar) (Set.Ici 0) := by
  intro θ hθ T hT hθT
  exact shiHigherBernsteinConst_mono d m hθ hθT hA le_rfl

theorem bernsteinMaximumBound_mono {c C C' eps eps' T T' : Real}
    (hc : 0 < c) (hCC : C ≤ C') (hT : 0 ≤ T) (hTT : T ≤ T')
    (heps : 0 ≤ eps) (heps' : eps ≤ eps') :
    bernsteinMaximumBound c C eps T ≤ bernsteinMaximumBound c C' eps' T' := by
  unfold bernsteinMaximumBound
  apply polynomialAbsorptionBound_mono hc le_rfl _ hCC
  exact mul_le_mul (mul_le_mul_of_nonneg_left heps' (by norm_num)) hTT hT
    (mul_nonneg (by norm_num) (heps.trans heps'))

end ScalarMonotonicity

end DifferentialGeometry.PDE.RicciFlow
