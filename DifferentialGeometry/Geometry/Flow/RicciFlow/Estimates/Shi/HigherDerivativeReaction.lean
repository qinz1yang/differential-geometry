import DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.Shi.FirstDerivativeReaction
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Operator

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle
open DifferentialGeometry.Analysis.Parabolic
open scoped Manifold ContDiff BigOperators Bundle Topology

section ScalarAbsorption

theorem shi_higher_quadratic_absorption (P Q : Real) :
    -10 * P ^ 2 + 8 * P * Q - 2 * Q ^ 2 ≤ -(2 / 5) * Q ^ 2 := by
  nlinarith [sq_nonneg (5 * P - 2 * Q)]

theorem sqrt_le_half_div_add {Y t : Real} (hY : 0 ≤ Y) (ht : 0 < t) :
    Real.sqrt Y ≤ (Y / t + t) / 2 := by
  have hne : t ≠ 0 := ne_of_gt ht
  obtain ⟨s, hs0, rfl⟩ : ∃ s : Real, 0 ≤ s ∧ Y = s ^ 2 :=
    ⟨Real.sqrt Y, Real.sqrt_nonneg Y, (Real.sq_sqrt hY).symm⟩
  rw [Real.sqrt_sq hs0, le_div_iff₀ (by norm_num : (0 : Real) < 2), ← sub_nonneg]
  have hexp : s ^ 2 / t + t - s * 2 = (s - t) ^ 2 / t := by
    field_simp
    ring
  rw [hexp]
  positivity

theorem shi_higher_bernstein_absorption {a b C F Y t T L : Real}
    (ha : 0 < a) (hab : a ≤ b) (hY : 0 ≤ Y) (hC : 0 ≤ C)
    (ht : 0 < t) (htT : t ≤ T)
    (hlow : a * Y ≤ F) (hhigh : F ≤ b * Y)
    (hL : L ≤ -(2 / 5) * Y ^ 2 / t + C * (Y / t) + C * t) :
    L ≤ -(1 / (5 * b ^ 2) / t) * F ^ 2 +
      (5 * b ^ 2 / 4 * (C / a) ^ 2 + C * T ^ 2) / t := by
  have hb : 0 < b := lt_of_lt_of_le ha hab
  have hane : a ≠ 0 := ne_of_gt ha
  have hbne : b ≠ 0 := ne_of_gt hb
  have htne : t ≠ 0 := ne_of_gt ht
  have hbsq : (0 : Real) < b ^ 2 := by positivity
  have hF0 : 0 ≤ F := le_trans (mul_nonneg ha.le hY) hlow
  have hFsq : F ^ 2 ≤ b ^ 2 * Y ^ 2 := by
    nlinarith [mul_self_le_mul_self hF0 hhigh]
  have hmono : ∀ p q : Real, p ≤ q → p / t ≤ q / t := by
    intro p q hpq
    rw [div_eq_mul_inv, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right hpq (by positivity)
  have hnum : -(2 / 5) * Y ^ 2 + C * Y + C * t ^ 2 ≤
      -(1 / (5 * b ^ 2)) * F ^ 2 + (5 * b ^ 2 / 4 * (C / a) ^ 2 + C * T ^ 2) := by
    rw [← sub_nonneg]
    have hid : -(1 / (5 * b ^ 2)) * F ^ 2 + (5 * b ^ 2 / 4 * (C / a) ^ 2 + C * T ^ 2) -
        (-(2 / 5) * Y ^ 2 + C * Y + C * t ^ 2) =
        2 * (b ^ 2 * Y ^ 2 - F ^ 2) / (5 * b ^ 2) +
          (2 * F - 5 * b ^ 2 * (C / a)) ^ 2 / (20 * b ^ 2) +
          C / a * (F - a * Y) + C * (T ^ 2 - t ^ 2) := by
      field_simp
      ring
    rw [hid]
    have h1 : (0 : Real) ≤ 2 * (b ^ 2 * Y ^ 2 - F ^ 2) / (5 * b ^ 2) := by
      have hd : (0 : Real) ≤ b ^ 2 * Y ^ 2 - F ^ 2 := by linarith [hFsq]
      positivity
    have h2 : (0 : Real) ≤ (2 * F - 5 * b ^ 2 * (C / a)) ^ 2 / (20 * b ^ 2) := by positivity
    have h3 : (0 : Real) ≤ C / a * (F - a * Y) :=
      mul_nonneg (by positivity) (by linarith [hlow])
    have h4 : (0 : Real) ≤ C * (T ^ 2 - t ^ 2) :=
      mul_nonneg hC (by nlinarith [mul_self_le_mul_self ht.le htT])
    linarith
  have hsrc : -(2 / 5) * Y ^ 2 / t + C * (Y / t) + C * t =
      (-(2 / 5) * Y ^ 2 + C * Y + C * t ^ 2) / t := by
    field_simp
  have hgoal : -(1 / (5 * b ^ 2) / t) * F ^ 2 +
      (5 * b ^ 2 / 4 * (C / a) ^ 2 + C * T ^ 2) / t =
      (-(1 / (5 * b ^ 2)) * F ^ 2 + (5 * b ^ 2 / 4 * (C / a) ^ 2 + C * T ^ 2)) / t := by
    field_simp
  rw [hsrc] at hL
  rw [hgoal]
  exact hL.trans (hmono _ _ hnum)

theorem shi_higher_product_le
    {a b Xm X Y Zt sig P um1 p q t T CY CX LY LX cr LF mm : Real}
    (hY0 : 0 ≤ Y) (hZ0 : 0 ≤ Zt) (hsig0 : 0 ≤ sig)
    (hCY0 : 0 ≤ CY) (hCX0 : 0 ≤ CX) (hmm0 : 0 ≤ mm) (hXm0 : 0 ≤ Xm)
    (hq0 : 0 ≤ q) (ht0 : 0 < t) (htT : t ≤ T)
    (hXmax : X ≤ Xm) (ha5 : 5 * X ≤ a + X) (haX0 : 0 ≤ a + X) (haXle : a + X ≤ b)
    (hXp : X = t * p) (hYt : Y = t * q)
    (hXZ : X * Zt = sig * P ^ 2) (hYq : Y * q = sig * um1 ^ 2)
    (hLY : LY ≤ -2 * Zt + CY * q + CY * t)
    (hLX : LX ≤ -2 * q + mm * p + CX)
    (hcr : cr ≤ 8 * sig * P * um1)
    (hLF : LF ≤ (a + X) * LY + Y * LX + cr) :
    LF ≤ -(2 / 5) * (Y * q) + (b * CY + mm * Xm + CX * T) * q +
      (b * CY + mm * Xm + CX * T) * t := by
  have hT0 : (0 : Real) ≤ T := le_trans ht0.le htT
  have hstep1 : (a + X) * LY ≤ (a + X) * (-2 * Zt + CY * q + CY * t) :=
    mul_le_mul_of_nonneg_left hLY haX0
  have hstep2 : Y * LX ≤ Y * (-2 * q + mm * p + CX) :=
    mul_le_mul_of_nonneg_left hLX hY0
  have hsplit1 : (a + X) * (-2 * Zt + CY * q + CY * t) =
      (a + X) * (-2 * Zt) + (a + X) * (CY * q) + (a + X) * (CY * t) := by ring
  have hsplit2 : Y * (-2 * q + mm * p + CX) = Y * (-2 * q) + Y * (mm * p) + Y * CX := by ring
  have hi : (a + X) * (-2 * Zt) ≤ -10 * (X * Zt) := by
    nlinarith [mul_nonneg hZ0 (by linarith : (0 : Real) ≤ a + X - 5 * X)]
  have hvi : (a + X) * (CY * q) ≤ b * CY * q := by
    nlinarith [mul_nonneg (mul_nonneg (sub_nonneg.mpr haXle) hCY0) hq0]
  have hvii : (a + X) * (CY * t) ≤ b * CY * t := by
    nlinarith [mul_nonneg (mul_nonneg (sub_nonneg.mpr haXle) hCY0) ht0.le]
  have hviii : Y * (mm * p) ≤ mm * Xm * q := by
    have h1 : Y * (mm * p) = mm * (X * q) := by
      rw [hXp, hYt]
      ring
    have h2 : mm * (X * q) ≤ mm * (Xm * q) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hXmax hq0) hmm0
    linarith [h1, h2]
  have hix : Y * CX ≤ CX * T * q := by
    have h1 : Y * CX = t * q * CX := by rw [hYt]
    have h2 : t * q * CX ≤ T * q * CX :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right htT hq0) hCX0
    linarith [h1, h2]
  have hlead := mul_le_mul_of_nonneg_left
    (shi_higher_quadratic_absorption P um1) hsig0
  have hleadeq : sig * (-10 * P ^ 2 + 8 * P * um1 - 2 * um1 ^ 2) =
      -10 * (X * Zt) + 8 * sig * P * um1 - 2 * (Y * q) := by
    rw [hXZ, hYq]
    ring
  have hleadeq2 : sig * (-(2 / 5) * um1 ^ 2) = -(2 / 5) * (Y * q) := by
    rw [hYq]
    ring
  have hextra : (0 : Real) ≤ (mm * Xm + CX * T) * t :=
    mul_nonneg (add_nonneg (mul_nonneg hmm0 hXm0) (mul_nonneg hCX0 hT0)) ht0.le
  linarith [hLF, hstep1, hstep2, hsplit1.le, hsplit1.ge, hsplit2.le, hsplit2.ge,
    hi, hvi, hvii, hviii, hix, hcr, hlead, hleadeq.le, hleadeq.ge, hleadeq2.le,
    hleadeq2.ge, hextra]

theorem sqrt_mul_pow_triple {t : Real} (ht : 0 ≤ t) {i j k e : ℕ}
    (hsum : i + j + k = 2 * e) (p q r : Real) :
    Real.sqrt (t ^ i * p) * Real.sqrt (t ^ j * q) * Real.sqrt (t ^ k * r) =
      t ^ e * (Real.sqrt p * Real.sqrt q * Real.sqrt r) := by
  have h1 : Real.sqrt (t ^ i) * Real.sqrt (t ^ j) = Real.sqrt (t ^ (i + j)) := by
    rw [← Real.sqrt_mul (pow_nonneg ht i), ← pow_add]
  have h2 : Real.sqrt (t ^ (i + j)) * Real.sqrt (t ^ k) = Real.sqrt (t ^ (i + j + k)) := by
    rw [← Real.sqrt_mul (pow_nonneg ht (i + j)), ← pow_add]
  have h3 : Real.sqrt (t ^ (i + j + k)) = t ^ e := by
    rw [hsum, two_mul, pow_add, Real.sqrt_mul_self (pow_nonneg ht e)]
  have hpow : Real.sqrt (t ^ i) * Real.sqrt (t ^ j) * Real.sqrt (t ^ k) = t ^ e := by
    rw [h1, h2, h3]
  rw [Real.sqrt_mul (pow_nonneg ht i), Real.sqrt_mul (pow_nonneg ht j),
    Real.sqrt_mul (pow_nonneg ht k), ← hpow]
  ring

end ScalarAbsorption

section Constants

def shiHigherShift (Astar : Real) : Real := 1 + 4 * Astar ^ 2

def shiHigherLYCoeff (d m : ℕ) (T Astar : Real) : Real :=
  ((m : Real) + 1) + rmTowerCost d (m + 1) * ((m : Real) + 2) * (T + Astar ^ 2 / 2)

def shiHigherLXConst (d m : ℕ) (Astar : Real) : Real :=
  rmTowerCost d m * ((m : Real) + 1) * Astar ^ 3

def shiHigherFConst (d m : ℕ) (T Astar : Real) : Real :=
  (1 + 5 * Astar ^ 2) * shiHigherLYCoeff d m T Astar +
    (m : Real) * Astar ^ 2 + shiHigherLXConst d m Astar * T

def shiHigherBernsteinCoeff (Astar : Real) : Real := 1 / (5 * (1 + 5 * Astar ^ 2) ^ 2)

def shiHigherBernsteinConst (d m : ℕ) (T Astar : Real) : Real :=
  5 * (1 + 5 * Astar ^ 2) ^ 2 / 4 *
      (shiHigherFConst d m T Astar / shiHigherShift Astar) ^ 2 +
    shiHigherFConst d m T Astar * T ^ 2

def shiHigherStepBound (d m : ℕ) (T Astar eps : Real) : Real :=
  bernsteinMaximumBound (shiHigherBernsteinCoeff Astar)
      (shiHigherBernsteinConst d m T Astar) eps T / shiHigherShift Astar


theorem one_le_shiHigherShift (Astar : Real) : 1 ≤ shiHigherShift Astar := by
  unfold shiHigherShift
  nlinarith [sq_nonneg Astar]


theorem shiHigherShift_pos (Astar : Real) : 0 < shiHigherShift Astar :=
  lt_of_lt_of_le zero_lt_one (one_le_shiHigherShift Astar)


theorem shiHigherLYCoeff_nonneg {T : Real} (hT : 0 ≤ T) (d m : ℕ) (Astar : Real) :
    0 ≤ shiHigherLYCoeff d m T Astar := by
  have hc := rmTowerCost_nonneg d (m + 1)
  have hm : (0 : Real) ≤ (m : Real) := Nat.cast_nonneg m
  have hA : (0 : Real) ≤ Astar ^ 2 := sq_nonneg Astar
  unfold shiHigherLYCoeff
  have h1 : (0 : Real) ≤ rmTowerCost d (m + 1) * ((m : Real) + 2) * (T + Astar ^ 2 / 2) := by
    have h2 : (0 : Real) ≤ (m : Real) + 2 := by linarith
    have h3 : (0 : Real) ≤ T + Astar ^ 2 / 2 := by linarith
    exact mul_nonneg (mul_nonneg hc h2) h3
  linarith


theorem shiHigherLXConst_nonneg {Astar : Real} (hA : 0 ≤ Astar) (d m : ℕ) :
    0 ≤ shiHigherLXConst d m Astar := by
  have hc := rmTowerCost_nonneg d m
  have hm : (0 : Real) ≤ (m : Real) := Nat.cast_nonneg m
  unfold shiHigherLXConst
  have h2 : (0 : Real) ≤ (m : Real) + 1 := by linarith
  exact mul_nonneg (mul_nonneg hc h2) (by positivity)


theorem shiHigherFConst_nonneg {T Astar : Real} (hT : 0 ≤ T) (hA : 0 ≤ Astar) (d m : ℕ) :
    0 ≤ shiHigherFConst d m T Astar := by
  have h1 := shiHigherLYCoeff_nonneg hT d m Astar
  have h2 := shiHigherLXConst_nonneg hA d m
  have hm : (0 : Real) ≤ (m : Real) := Nat.cast_nonneg m
  have hA2 : (0 : Real) ≤ Astar ^ 2 := sq_nonneg Astar
  unfold shiHigherFConst
  have h3 : (0 : Real) ≤ (1 + 5 * Astar ^ 2) * shiHigherLYCoeff d m T Astar := by
    have : (0 : Real) ≤ 1 + 5 * Astar ^ 2 := by linarith
    exact mul_nonneg this h1
  have h4 : (0 : Real) ≤ (m : Real) * Astar ^ 2 := mul_nonneg hm hA2
  have h5 : (0 : Real) ≤ shiHigherLXConst d m Astar * T := mul_nonneg h2 hT
  linarith


theorem shiHigherBernsteinCoeff_pos (Astar : Real) : 0 < shiHigherBernsteinCoeff Astar := by
  have h : (0 : Real) < 5 * (1 + 5 * Astar ^ 2) ^ 2 := by positivity
  unfold shiHigherBernsteinCoeff
  positivity


theorem shiHigherBernsteinConst_nonneg {T Astar : Real} (hT : 0 ≤ T) (hA : 0 ≤ Astar)
    (d m : ℕ) : 0 ≤ shiHigherBernsteinConst d m T Astar := by
  have h1 := shiHigherFConst_nonneg hT hA d m
  unfold shiHigherBernsteinConst
  have h2 : (0 : Real) ≤ 5 * (1 + 5 * Astar ^ 2) ^ 2 / 4 *
      (shiHigherFConst d m T Astar / shiHigherShift Astar) ^ 2 := by positivity
  have h3 : (0 : Real) ≤ shiHigherFConst d m T Astar * T ^ 2 := by positivity
  linarith

end Constants

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [FiniteDimensional Real E] [NeZero (Module.finrank Real E)] [CompleteSpace E]
variable [I.Boundaryless]
variable [IsManifold I 1 M] [IsManifold I 2 M] [IsManifold I ∞ M]
variable [T2Space M] [BoundarylessManifold I M]
variable [VectorBundle Real E (TangentSpace I : M -> Type _)]

section ParabolicAlgebra

omit [NeZero (Module.finrank Real E)] [CompleteSpace E] [I.Boundaryless]
  [IsManifold I 2 M] [T2Space M] [BoundarylessManifold I M] in
theorem parabolicOperatorWithDrift_pow_mul
    (G : MetricConnectionFamily (I := I) (M := M) Real)
    (T : Real) (X : Real -> (x : M) -> TangentSpace I x)
    (F : Real -> M -> Real) (j : Nat) (t : Real) (x : M)
    (huniq : UniqueDiffWithinAt Real (Set.Icc 0 T) t)
    (hF_time : DifferentiableWithinAt Real (fun s : Real => F s x) (Set.Icc 0 T) t)
    (hF_space : forall y : M, MDifferentiableAt I 𝓘(Real, Real) (F t) y)
    (hF_grad : MDifferentiableAt I (I.prod 𝓘(Real, E)) (T% fun y : M =>
      gradientFun (I := I) (G.metric t) (F t) y) x) :
    parabolicOperatorWithDrift (I := I) G T X (fun s y => s ^ j * F s y) t x =
      (j : Real) * t ^ (j - 1) * F t x +
        t ^ j * parabolicOperatorWithDrift (I := I) G T X F t x := by
  have hpow_diff : DifferentiableWithinAt Real (fun s : Real => s ^ j) (Set.Icc 0 T) t :=
    (hasDerivAt_pow j t).differentiableAt.differentiableWithinAt
  have hpow_deriv : derivWithin (fun s : Real => s ^ j) (Set.Icc 0 T) t =
      (j : Real) * t ^ (j - 1) :=
    (hasDerivAt_pow j t).hasDerivWithinAt.derivWithin huniq
  have hderiv : derivWithin (fun s : Real => s ^ j * F s x) (Set.Icc 0 T) t =
      (j : Real) * t ^ (j - 1) * F t x +
        t ^ j * derivWithin (fun s : Real => F s x) (Set.Icc 0 T) t := by
    rw [derivWithin_fun_mul hpow_diff hF_time, hpow_deriv]
  have hsmul : (fun y : M => t ^ j * F t y) = (t ^ j) • F t := by
    funext y
    simp [smul_eq_mul]
  have hheat : heatOperatorWithDrift (I := I) G t (X t) (fun y : M => t ^ j * F t y) x =
      t ^ j * heatOperatorWithDrift (I := I) G t (X t) (F t) x := by
    rw [hsmul]
    exact heatOperatorWithDrift_const_smul (I := I) G t (X t) (t ^ j) hF_space hF_grad
  rw [parabolicOperatorWithDrift_eq, parabolicOperatorWithDrift_eq, hderiv]
  change _ - heatOperatorWithDrift (I := I) G t (X t) (fun y : M => t ^ j * F t y) x = _
  rw [hheat]
  ring

end ParabolicAlgebra

section WeightedQuantities

def shiWeightedNormSq
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) (j : Nat) :
    Real -> M -> Real :=
  fun t x => t ^ j * nablaKRm04NormSqIntrinsic (I := I) S j t x

def shiHigherBernsteinQuantity
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) (m : Nat) (a : Real) :
    Real -> M -> Real :=
  fun t x => (a + shiWeightedNormSq (I := I) S m t x) *
    shiWeightedNormSq (I := I) S (m + 1) t x

omit [NeZero (Module.finrank Real E)] [I.Boundaryless] [BoundarylessManifold I M]
  [VectorBundle Real E (TangentSpace I : M -> Type _)] in
theorem shiWeightedNormSq_nonneg
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) (j : Nat)
    {t : Real} (ht : 0 ≤ t) (x : M) :
    0 ≤ shiWeightedNormSq (I := I) S j t x :=
  mul_nonneg (pow_nonneg ht j) (nablaKRm04NormSqIntrinsic_nonneg (I := I) S j t x)

omit [NeZero (Module.finrank Real E)] [I.Boundaryless] [BoundarylessManifold I M]
  [VectorBundle Real E (TangentSpace I : M -> Type _)] in
theorem shiWeightedNormSq_zero_of_ne_zero
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) {j : Nat} (hj : j ≠ 0)
    (x : M) :
    shiWeightedNormSq (I := I) S j 0 x = 0 := by
  unfold shiWeightedNormSq
  rw [zero_pow hj, zero_mul]

omit [NeZero (Module.finrank Real E)] [I.Boundaryless] [BoundarylessManifold I M]
  [VectorBundle Real E (TangentSpace I : M -> Type _)] in
theorem contMDiff_shiWeightedNormSq
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) (j : Nat) (t : Real) :
    ContMDiff I 𝓘(Real, Real) ∞ (shiWeightedNormSq (I := I) S j t) :=
  contMDiff_const.mul (nablaKNorm_smooth (I := I) S t j)

omit [VectorBundle Real E (TangentSpace I : M -> Type _)] in
theorem differentiableAt_shiWeightedNormSq
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) (j : Nat)
    {t : Real} (htreg : t ∈ D.regular) (x : M) :
    DifferentiableAt Real (fun s : Real => shiWeightedNormSq (I := I) S j s x) t :=
  ((hasDerivAt_pow j t).differentiableAt).mul
    (differentiableAt_nablaKRm04NormSqIntrinsic (I := I) S hS j htreg x)

omit [NeZero (Module.finrank Real E)] [I.Boundaryless] [BoundarylessManifold I M]
  [VectorBundle Real E (TangentSpace I : M -> Type _)] in
theorem gradientAt_shiWeightedNormSq
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) (j : Nat) (t : Real)
    (x : M) :
    gradientAt (I := I) (flowG (I := I) S) t (shiWeightedNormSq (I := I) S j t) x =
      t ^ j • gradientAt (I := I) (flowG (I := I) S) t
        (nablaKRm04NormSqIntrinsic (I := I) S j t) x := by
  have hsmooth := nablaKNorm_smooth (I := I) S t j
  have hfun : shiWeightedNormSq (I := I) S j t =
      t ^ j • nablaKRm04NormSqIntrinsic (I := I) S j t := by
    funext y
    simp [shiWeightedNormSq, smul_eq_mul]
  unfold gradientAt
  rw [hfun]
  exact gradientFun_const_smul (I := I) ((flowG (I := I) S).metric t) (t ^ j)
    (hsmooth.contMDiffAt.mdifferentiableAt (by simp))

theorem parabolicOperatorWithDrift_shiWeightedNormSq_raw
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) {T : Real} (hT : 0 < T) (k : Nat)
    {t : Real} (ht : t ∈ Set.Icc 0 T) (htreg : t ∈ D.regular) (x : M) :
    parabolicOperatorWithDrift (I := I) (flowG (I := I) S) T
        (fun _ y => (0 : TangentSpace I y))
        (shiWeightedNormSq (I := I) S k) t x ≤
      (k : Real) * t ^ (k - 1) * nablaKRm04NormSqIntrinsic (I := I) S k t x +
        t ^ k * (-2 * nablaKRm04NormSqIntrinsic (I := I) S (k + 1) t x +
          towerReactionSum (M := M) (nablaKRm04NormSqIntrinsic (I := I) S)
            (rmTowerCost (Module.finrank Real E) k) k t x) := by
  have huniq : UniqueDiffWithinAt Real (Set.Icc 0 T) t :=
    (uniqueDiffOn_Icc hT).uniqueDiffWithinAt ht
  have hsmooth := nablaKNorm_smooth (I := I) S t k
  have heq := parabolicOperatorWithDrift_pow_mul (I := I) (flowG (I := I) S) T
    (fun _ y => (0 : TangentSpace I y)) (nablaKRm04NormSqIntrinsic (I := I) S k) k t x huniq
    ((differentiableAt_nablaKRm04NormSqIntrinsic (I := I) S hS k htreg x).differentiableWithinAt)
    (fun y => hsmooth.contMDiffAt.mdifferentiableAt (by simp))
    (gradientFun_mdiffAt (I := I) ((flowG (I := I) S).metric t) hsmooth x)
  have hbase :=
    parabolicOperatorWithDrift_nablaKRm04NormSqIntrinsic_le (I := I) S hS hT k ht htreg x
  have hunfold : shiWeightedNormSq (I := I) S k =
      fun s (y : M) => s ^ k * nablaKRm04NormSqIntrinsic (I := I) S k s y := rfl
  rw [hunfold, heq]
  have hscaled := mul_le_mul_of_nonneg_left hbase (pow_nonneg ht.1 k)
  linarith

end WeightedQuantities

section ReactionSums

omit [NeZero (Module.finrank Real E)] [I.Boundaryless] [BoundarylessManifold I M]
  [VectorBundle Real E (TangentSpace I : M -> Type _)] in
theorem tpow_mul_towerReactionSum_le
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D)
    {t Astar c : Real} (ht : 0 ≤ t) (hc : 0 ≤ c) (hAstar : 0 ≤ Astar) (m : Nat) (x : M)
    (hIH : ∀ j : Nat, j ≤ m →
      t ^ j * nablaKRm04NormSqIntrinsic (I := I) S j t x ≤ Astar ^ 2) :
    t ^ m * towerReactionSum (M := M) (nablaKRm04NormSqIntrinsic (I := I) S) c m t x ≤
      c * ((m : Real) + 1) * Astar ^ 3 := by
  have hsqrt : ∀ j : Nat, j ≤ m →
      Real.sqrt (t ^ j * nablaKRm04NormSqIntrinsic (I := I) S j t x) ≤ Astar := by
    intro j hj
    have h := Real.sqrt_le_sqrt (hIH j hj)
    rwa [Real.sqrt_sq hAstar] at h
  unfold towerReactionSum
  rw [Finset.mul_sum]
  have hterm : ∀ j ∈ Finset.range (m + 1),
      t ^ m * (c * Real.sqrt (nablaKRm04NormSqIntrinsic (I := I) S j t x) *
          Real.sqrt (nablaKRm04NormSqIntrinsic (I := I) S (m - j) t x) *
          Real.sqrt (nablaKRm04NormSqIntrinsic (I := I) S m t x)) ≤ c * Astar ^ 3 := by
    intro j hj
    have hjm : j ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    have hsum : j + (m - j) + m = 2 * m := by omega
    have hkey := sqrt_mul_pow_triple ht hsum
      (nablaKRm04NormSqIntrinsic (I := I) S j t x)
      (nablaKRm04NormSqIntrinsic (I := I) S (m - j) t x)
      (nablaKRm04NormSqIntrinsic (I := I) S m t x)
    have hA := hsqrt j hjm
    have hB := hsqrt (m - j) (by omega)
    have hC := hsqrt m le_rfl
    have hA0 : 0 ≤ Real.sqrt (t ^ j * nablaKRm04NormSqIntrinsic (I := I) S j t x) :=
      Real.sqrt_nonneg _
    have hB0 : 0 ≤ Real.sqrt (t ^ (m - j) *
        nablaKRm04NormSqIntrinsic (I := I) S (m - j) t x) := Real.sqrt_nonneg _
    have hC0 : 0 ≤ Real.sqrt (t ^ m * nablaKRm04NormSqIntrinsic (I := I) S m t x) :=
      Real.sqrt_nonneg _
    have hprod : Real.sqrt (t ^ j * nablaKRm04NormSqIntrinsic (I := I) S j t x) *
        Real.sqrt (t ^ (m - j) * nablaKRm04NormSqIntrinsic (I := I) S (m - j) t x) *
        Real.sqrt (t ^ m * nablaKRm04NormSqIntrinsic (I := I) S m t x) ≤ Astar ^ 3 := by
      have h1 := mul_le_mul hA hB hB0 hAstar
      have h2 := mul_le_mul h1 hC hC0 (mul_nonneg hAstar hAstar)
      have hcube : Astar * Astar * Astar = Astar ^ 3 := by ring
      exact h2.trans (le_of_eq hcube)
    have heq : t ^ m * (c * Real.sqrt (nablaKRm04NormSqIntrinsic (I := I) S j t x) *
        Real.sqrt (nablaKRm04NormSqIntrinsic (I := I) S (m - j) t x) *
        Real.sqrt (nablaKRm04NormSqIntrinsic (I := I) S m t x)) =
        c * (t ^ m * (Real.sqrt (nablaKRm04NormSqIntrinsic (I := I) S j t x) *
          Real.sqrt (nablaKRm04NormSqIntrinsic (I := I) S (m - j) t x) *
          Real.sqrt (nablaKRm04NormSqIntrinsic (I := I) S m t x))) := by ring
    rw [heq, ← hkey]
    exact mul_le_mul_of_nonneg_left hprod hc
  refine le_trans (Finset.sum_le_sum hterm) ?_
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  push_cast
  ring_nf
  exact le_rfl

omit [NeZero (Module.finrank Real E)] [I.Boundaryless] [BoundarylessManifold I M]
  [VectorBundle Real E (TangentSpace I : M -> Type _)] in
theorem tpow_succ_mul_towerReactionSum_le
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D)
    {t Astar c : Real} (ht : 0 ≤ t) (hc : 0 ≤ c) (hAstar : 0 ≤ Astar) (m : Nat) (x : M)
    (hu0 : nablaKRm04NormSqIntrinsic (I := I) S 0 t x ≤ 1)
    (hIH : ∀ j : Nat, 1 ≤ j → j ≤ m →
      t ^ j * nablaKRm04NormSqIntrinsic (I := I) S j t x ≤ Astar ^ 2) :
    t ^ (m + 1) *
        towerReactionSum (M := M) (nablaKRm04NormSqIntrinsic (I := I) S) c (m + 1) t x ≤
      c * ((m : Real) + 2) *
        (t ^ (m + 1) * nablaKRm04NormSqIntrinsic (I := I) S (m + 1) t x +
          Astar ^ 2 *
            Real.sqrt (t ^ (m + 1) * nablaKRm04NormSqIntrinsic (I := I) S (m + 1) t x)) := by
  have hY0 : 0 ≤ t ^ (m + 1) * nablaKRm04NormSqIntrinsic (I := I) S (m + 1) t x :=
    mul_nonneg (pow_nonneg ht (m + 1))
      (nablaKRm04NormSqIntrinsic_nonneg (I := I) S (m + 1) t x)
  have hR0 : 0 ≤ Real.sqrt (t ^ (m + 1) *
      nablaKRm04NormSqIntrinsic (I := I) S (m + 1) t x) := Real.sqrt_nonneg _
  have hRR : Real.sqrt (t ^ (m + 1) * nablaKRm04NormSqIntrinsic (I := I) S (m + 1) t x) *
      Real.sqrt (t ^ (m + 1) * nablaKRm04NormSqIntrinsic (I := I) S (m + 1) t x) =
      t ^ (m + 1) * nablaKRm04NormSqIntrinsic (I := I) S (m + 1) t x :=
    Real.mul_self_sqrt hY0
  have hP0 : Real.sqrt (t ^ 0 * nablaKRm04NormSqIntrinsic (I := I) S 0 t x) ≤ 1 := by
    have h : t ^ 0 * nablaKRm04NormSqIntrinsic (I := I) S 0 t x ≤ 1 := by
      rw [pow_zero, one_mul]
      exact hu0
    have hs := Real.sqrt_le_sqrt h
    rwa [Real.sqrt_one] at hs
  have hsqrt : ∀ j : Nat, 1 ≤ j → j ≤ m →
      Real.sqrt (t ^ j * nablaKRm04NormSqIntrinsic (I := I) S j t x) ≤ Astar := by
    intro j hj1 hj
    have h := Real.sqrt_le_sqrt (hIH j hj1 hj)
    rwa [Real.sqrt_sq hAstar] at h
  unfold towerReactionSum
  rw [Finset.mul_sum]
  have hterm : ∀ j ∈ Finset.range (m + 1 + 1),
      t ^ (m + 1) * (c * Real.sqrt (nablaKRm04NormSqIntrinsic (I := I) S j t x) *
          Real.sqrt (nablaKRm04NormSqIntrinsic (I := I) S (m + 1 - j) t x) *
          Real.sqrt (nablaKRm04NormSqIntrinsic (I := I) S (m + 1) t x)) ≤
        c * (t ^ (m + 1) * nablaKRm04NormSqIntrinsic (I := I) S (m + 1) t x +
          Astar ^ 2 *
            Real.sqrt (t ^ (m + 1) *
              nablaKRm04NormSqIntrinsic (I := I) S (m + 1) t x)) := by
    intro j hj
    have hjm : j ≤ m + 1 := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    have hsum : j + (m + 1 - j) + (m + 1) = 2 * (m + 1) := by omega
    have hkey := sqrt_mul_pow_triple ht hsum
      (nablaKRm04NormSqIntrinsic (I := I) S j t x)
      (nablaKRm04NormSqIntrinsic (I := I) S (m + 1 - j) t x)
      (nablaKRm04NormSqIntrinsic (I := I) S (m + 1) t x)
    have hA0 : 0 ≤ Real.sqrt (t ^ j * nablaKRm04NormSqIntrinsic (I := I) S j t x) :=
      Real.sqrt_nonneg _
    have hB0 : 0 ≤ Real.sqrt (t ^ (m + 1 - j) *
        nablaKRm04NormSqIntrinsic (I := I) S (m + 1 - j) t x) := Real.sqrt_nonneg _
    have hprod : Real.sqrt (t ^ j * nablaKRm04NormSqIntrinsic (I := I) S j t x) *
        Real.sqrt (t ^ (m + 1 - j) *
          nablaKRm04NormSqIntrinsic (I := I) S (m + 1 - j) t x) *
        Real.sqrt (t ^ (m + 1) * nablaKRm04NormSqIntrinsic (I := I) S (m + 1) t x) ≤
        t ^ (m + 1) * nablaKRm04NormSqIntrinsic (I := I) S (m + 1) t x +
          Astar ^ 2 * Real.sqrt (t ^ (m + 1) *
            nablaKRm04NormSqIntrinsic (I := I) S (m + 1) t x) := by
      have hA2R : (0 : Real) ≤ Astar ^ 2 *
          Real.sqrt (t ^ (m + 1) *
            nablaKRm04NormSqIntrinsic (I := I) S (m + 1) t x) :=
        mul_nonneg (sq_nonneg Astar) hR0
      rcases Nat.eq_zero_or_pos j with rfl | hjpos
      · simp only [Nat.sub_zero]
        have hstep : Real.sqrt (t ^ 0 * nablaKRm04NormSqIntrinsic (I := I) S 0 t x) *
            Real.sqrt (t ^ (m + 1) *
              nablaKRm04NormSqIntrinsic (I := I) S (m + 1) t x) *
            Real.sqrt (t ^ (m + 1) *
              nablaKRm04NormSqIntrinsic (I := I) S (m + 1) t x) =
            Real.sqrt (t ^ 0 * nablaKRm04NormSqIntrinsic (I := I) S 0 t x) *
              (Real.sqrt (t ^ (m + 1) *
                  nablaKRm04NormSqIntrinsic (I := I) S (m + 1) t x) *
                Real.sqrt (t ^ (m + 1) *
                  nablaKRm04NormSqIntrinsic (I := I) S (m + 1) t x)) := by ring
        rw [hstep, hRR]
        have hle := mul_le_mul_of_nonneg_right hP0 hY0
        linarith
      · rcases eq_or_lt_of_le hjm with rfl | hjlt
        · simp only [Nat.sub_self]
          have hstep : Real.sqrt (t ^ (m + 1) *
                nablaKRm04NormSqIntrinsic (I := I) S (m + 1) t x) *
              Real.sqrt (t ^ 0 * nablaKRm04NormSqIntrinsic (I := I) S 0 t x) *
              Real.sqrt (t ^ (m + 1) *
                nablaKRm04NormSqIntrinsic (I := I) S (m + 1) t x) =
              Real.sqrt (t ^ 0 * nablaKRm04NormSqIntrinsic (I := I) S 0 t x) *
                (Real.sqrt (t ^ (m + 1) *
                    nablaKRm04NormSqIntrinsic (I := I) S (m + 1) t x) *
                  Real.sqrt (t ^ (m + 1) *
                    nablaKRm04NormSqIntrinsic (I := I) S (m + 1) t x)) := by ring
          rw [hstep, hRR]
          have hle := mul_le_mul_of_nonneg_right hP0 hY0
          linarith
        · have hjle : j ≤ m := by omega
          have hA := hsqrt j hjpos hjle
          have hB := hsqrt (m + 1 - j) (by omega) (by omega)
          have h1 := mul_le_mul hA hB hB0 hAstar
          have h2 := mul_le_mul_of_nonneg_right h1 hR0
          have h3 : Astar * Astar *
              Real.sqrt (t ^ (m + 1) *
                nablaKRm04NormSqIntrinsic (I := I) S (m + 1) t x) =
              Astar ^ 2 *
                Real.sqrt (t ^ (m + 1) *
                  nablaKRm04NormSqIntrinsic (I := I) S (m + 1) t x) := by ring
          linarith [h2, h3.le, h3.ge, hY0]
    have heq : t ^ (m + 1) * (c * Real.sqrt (nablaKRm04NormSqIntrinsic (I := I) S j t x) *
        Real.sqrt (nablaKRm04NormSqIntrinsic (I := I) S (m + 1 - j) t x) *
        Real.sqrt (nablaKRm04NormSqIntrinsic (I := I) S (m + 1) t x)) =
        c * (t ^ (m + 1) * (Real.sqrt (nablaKRm04NormSqIntrinsic (I := I) S j t x) *
          Real.sqrt (nablaKRm04NormSqIntrinsic (I := I) S (m + 1 - j) t x) *
          Real.sqrt (nablaKRm04NormSqIntrinsic (I := I) S (m + 1) t x))) := by ring
    rw [heq, ← hkey]
    exact mul_le_mul_of_nonneg_left hprod hc
  refine le_trans (Finset.sum_le_sum hterm) ?_
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  push_cast
  ring_nf
  exact le_rfl

end ReactionSums

section WeightEvolution

omit [VectorBundle Real E (TangentSpace I : M -> Type _)] in
theorem parabolicOperatorWithDrift_shiWeightedNormSq_le
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) {T Astar : Real} (hT : 0 < T) (hAstar : 0 ≤ Astar)
    (m : Nat) {t : Real} (ht : t ∈ Set.Icc 0 T) (htpos : 0 < t) (htreg : t ∈ D.regular)
    (x : M)
    (hIH : ∀ j : Nat, j ≤ m →
      t ^ j * nablaKRm04NormSqIntrinsic (I := I) S j t x ≤ Astar ^ 2) :
    parabolicOperatorWithDrift (I := I) (flowG (I := I) S) T
        (fun _ y => (0 : TangentSpace I y))
        (shiWeightedNormSq (I := I) S m) t x ≤
      -2 * (shiWeightedNormSq (I := I) S (m + 1) t x / t) +
        (m : Real) * (shiWeightedNormSq (I := I) S m t x / t) +
        shiHigherLXConst (Module.finrank Real E) m Astar := by
  have htne : t ≠ 0 := ne_of_gt htpos
  have hraw := parabolicOperatorWithDrift_shiWeightedNormSq_raw (I := I) S hS hT m ht htreg x
  have hreact := tpow_mul_towerReactionSum_le (I := I) S ht.1
    (rmTowerCost_nonneg (Module.finrank Real E) m) hAstar m x hIH
  have hYt : shiWeightedNormSq (I := I) S (m + 1) t x / t =
      t ^ m * nablaKRm04NormSqIntrinsic (I := I) S (m + 1) t x := by
    unfold shiWeightedNormSq
    rw [div_eq_iff htne, pow_succ]
    ring
  have hXt : (m : Real) * t ^ (m - 1) * nablaKRm04NormSqIntrinsic (I := I) S m t x =
      (m : Real) * (shiWeightedNormSq (I := I) S m t x / t) := by
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp
    · obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
      have key : shiWeightedNormSq (I := I) S (k + 1) t x / t =
          t ^ k * nablaKRm04NormSqIntrinsic (I := I) S (k + 1) t x := by
        unfold shiWeightedNormSq
        rw [div_eq_iff htne, pow_succ]
        ring
      rw [Nat.add_sub_cancel, key]
      ring
  have hexpand : t ^ m * (-2 * nablaKRm04NormSqIntrinsic (I := I) S (m + 1) t x +
      towerReactionSum (M := M) (nablaKRm04NormSqIntrinsic (I := I) S)
        (rmTowerCost (Module.finrank Real E) m) m t x) =
      -2 * (t ^ m * nablaKRm04NormSqIntrinsic (I := I) S (m + 1) t x) +
        t ^ m * towerReactionSum (M := M) (nablaKRm04NormSqIntrinsic (I := I) S)
          (rmTowerCost (Module.finrank Real E) m) m t x := by ring
  rw [hexpand, hXt, ← hYt] at hraw
  unfold shiHigherLXConst
  linarith

omit [VectorBundle Real E (TangentSpace I : M -> Type _)] in
theorem parabolicOperatorWithDrift_shiWeightedNormSq_succ_le
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) {T Astar : Real} (hT : 0 < T) (hAstar : 0 ≤ Astar)
    (m : Nat) {t : Real} (ht : t ∈ Set.Icc 0 T) (htpos : 0 < t) (htreg : t ∈ D.regular)
    (x : M) (hu0 : nablaKRm04NormSqIntrinsic (I := I) S 0 t x ≤ 1)
    (hIH : ∀ j : Nat, 1 ≤ j → j ≤ m →
      t ^ j * nablaKRm04NormSqIntrinsic (I := I) S j t x ≤ Astar ^ 2) :
    parabolicOperatorWithDrift (I := I) (flowG (I := I) S) T
        (fun _ y => (0 : TangentSpace I y))
        (shiWeightedNormSq (I := I) S (m + 1)) t x ≤
      -2 * (t ^ (m + 1) * nablaKRm04NormSqIntrinsic (I := I) S (m + 1 + 1) t x) +
        shiHigherLYCoeff (Module.finrank Real E) m T Astar *
          (shiWeightedNormSq (I := I) S (m + 1) t x / t) +
        shiHigherLYCoeff (Module.finrank Real E) m T Astar * t := by
  have htne : t ≠ 0 := ne_of_gt htpos
  have hTnn : (0 : Real) ≤ T := le_trans ht.1 ht.2
  have hraw :=
    parabolicOperatorWithDrift_shiWeightedNormSq_raw (I := I) S hS hT (m + 1) ht htreg x
  have hreact := tpow_succ_mul_towerReactionSum_le (I := I) S ht.1
    (rmTowerCost_nonneg (Module.finrank Real E) (m + 1)) hAstar m x hu0 hIH
  have hunf : shiWeightedNormSq (I := I) S (m + 1) t x =
      t ^ (m + 1) * nablaKRm04NormSqIntrinsic (I := I) S (m + 1) t x := rfl
  rw [← hunf] at hreact
  have hY0 : 0 ≤ shiWeightedNormSq (I := I) S (m + 1) t x :=
    shiWeightedNormSq_nonneg (I := I) S (m + 1) ht.1 x
  have hq0 : 0 ≤ shiWeightedNormSq (I := I) S (m + 1) t x / t := div_nonneg hY0 htpos.le
  have hYq : shiWeightedNormSq (I := I) S (m + 1) t x =
      t * (shiWeightedNormSq (I := I) S (m + 1) t x / t) := by
    field_simp
  have hyoung := sqrt_le_half_div_add hY0 htpos
  have hwt : ((m + 1 : Nat) : Real) * t ^ (m + 1 - 1) *
      nablaKRm04NormSqIntrinsic (I := I) S (m + 1) t x =
      ((m : Real) + 1) * (shiWeightedNormSq (I := I) S (m + 1) t x / t) := by
    have key : shiWeightedNormSq (I := I) S (m + 1) t x / t =
        t ^ m * nablaKRm04NormSqIntrinsic (I := I) S (m + 1) t x := by
      unfold shiWeightedNormSq
      rw [div_eq_iff htne, pow_succ]
      ring
    rw [Nat.add_sub_cancel, key]
    push_cast
    ring
  have hexpand : t ^ (m + 1) * (-2 * nablaKRm04NormSqIntrinsic (I := I) S (m + 1 + 1) t x +
      towerReactionSum (M := M) (nablaKRm04NormSqIntrinsic (I := I) S)
        (rmTowerCost (Module.finrank Real E) (m + 1)) (m + 1) t x) =
      -2 * (t ^ (m + 1) * nablaKRm04NormSqIntrinsic (I := I) S (m + 1 + 1) t x) +
        t ^ (m + 1) * towerReactionSum (M := M) (nablaKRm04NormSqIntrinsic (I := I) S)
          (rmTowerCost (Module.finrank Real E) (m + 1)) (m + 1) t x := by ring
  rw [hexpand, hwt] at hraw
  have hccM : (0 : Real) ≤ rmTowerCost (Module.finrank Real E) (m + 1) * ((m : Real) + 2) := by
    have hm : (0 : Real) ≤ (m : Real) + 2 := by positivity
    exact mul_nonneg (rmTowerCost_nonneg (Module.finrank Real E) (m + 1)) hm
  have hinner : shiWeightedNormSq (I := I) S (m + 1) t x +
      Astar ^ 2 * Real.sqrt (shiWeightedNormSq (I := I) S (m + 1) t x) ≤
      (T + Astar ^ 2 / 2) * (shiWeightedNormSq (I := I) S (m + 1) t x / t) +
        Astar ^ 2 / 2 * t := by
    have hd : (0 : Real) ≤ (T - t) * (shiWeightedNormSq (I := I) S (m + 1) t x / t) :=
      mul_nonneg (by linarith [ht.2]) hq0
    have hYT : shiWeightedNormSq (I := I) S (m + 1) t x ≤
        T * (shiWeightedNormSq (I := I) S (m + 1) t x / t) := by
      nlinarith [hYq, hd]
    have hsq := mul_le_mul_of_nonneg_left hyoung (sq_nonneg Astar)
    nlinarith [hYT, hsq]
  have hmul := mul_le_mul_of_nonneg_left hinner hccM
  have hbase : (0 : Real) ≤ ((m : Real) + 1) +
      rmTowerCost (Module.finrank Real E) (m + 1) * ((m : Real) + 2) * T := by
    have h1 : (0 : Real) ≤ (m : Real) + 1 := by positivity
    have h2 : (0 : Real) ≤ rmTowerCost (Module.finrank Real E) (m + 1) * ((m : Real) + 2) * T :=
      mul_nonneg hccM hTnn
    linarith
  have htail : (0 : Real) ≤ (((m : Real) + 1) +
      rmTowerCost (Module.finrank Real E) (m + 1) * ((m : Real) + 2) * T) * t :=
    mul_nonneg hbase ht.1
  unfold shiHigherLYCoeff
  nlinarith [hraw, hreact, hmul, htail]

end WeightEvolution

section GradientCrossTerm

omit [NeZero (Module.finrank Real E)] [I.Boundaryless] [BoundarylessManifold I M]
  [VectorBundle Real E (TangentSpace I : M -> Type _)] in
theorem inner_gradient_nablaKRm04NormSqIntrinsic_self_le
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) (j : Nat) (t : Real)
    (x : M) :
    ((flowG (I := I) S).metric t).inner x
        (gradientAt (I := I) (flowG (I := I) S) t
          (nablaKRm04NormSqIntrinsic (I := I) S j t) x)
        (gradientAt (I := I) (flowG (I := I) S) t
          (nablaKRm04NormSqIntrinsic (I := I) S j t) x) ≤
      4 * nablaKRm04NormSqIntrinsic (I := I) S j t x *
        nablaKRm04NormSqIntrinsic (I := I) S (j + 1) t x := by
  simpa [flowG, gradientAt] using towerNorm_grad_le (I := I) (S := S) j t x

omit [NeZero (Module.finrank Real E)] [I.Boundaryless] [BoundarylessManifold I M]
  [VectorBundle Real E (TangentSpace I : M -> Type _)] in
theorem neg_two_inner_gradient_shiWeightedNormSq_le
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) (m : Nat)
    {t : Real} (ht : 0 ≤ t) (x : M) :
    -2 * ((flowG (I := I) S).metric t).inner x
        (gradientAt (I := I) (flowG (I := I) S) t (shiWeightedNormSq (I := I) S m t) x)
        (gradientAt (I := I) (flowG (I := I) S) t
          (shiWeightedNormSq (I := I) S (m + 1) t) x) ≤
      8 * (t ^ m * t ^ (m + 1)) *
        (Real.sqrt (nablaKRm04NormSqIntrinsic (I := I) S m t x) *
          Real.sqrt (nablaKRm04NormSqIntrinsic (I := I) S (m + 1 + 1) t x)) *
        nablaKRm04NormSqIntrinsic (I := I) S (m + 1) t x := by
  have h0 := nablaKRm04NormSqIntrinsic_nonneg (I := I) S m t x
  have h1 := nablaKRm04NormSqIntrinsic_nonneg (I := I) S (m + 1) t x
  have h2 := nablaKRm04NormSqIntrinsic_nonneg (I := I) S (m + 1 + 1) t x
  have hsm : Real.sqrt (nablaKRm04NormSqIntrinsic (I := I) S m t x) ^ 2 =
      nablaKRm04NormSqIntrinsic (I := I) S m t x := Real.sq_sqrt h0
  have hsm2 : Real.sqrt (nablaKRm04NormSqIntrinsic (I := I) S (m + 1 + 1) t x) ^ 2 =
      nablaKRm04NormSqIntrinsic (I := I) S (m + 1 + 1) t x := Real.sq_sqrt h2
  have hgm := gradientAt_shiWeightedNormSq (I := I) S m t x
  have hgm1 := gradientAt_shiWeightedNormSq (I := I) S (m + 1) t x
  have hA : ((flowG (I := I) S).metric t).inner x
      (gradientAt (I := I) (flowG (I := I) S) t (shiWeightedNormSq (I := I) S m t) x)
      (gradientAt (I := I) (flowG (I := I) S) t (shiWeightedNormSq (I := I) S m t) x) ≤
      (t ^ m) ^ 2 * (4 * nablaKRm04NormSqIntrinsic (I := I) S m t x *
        nablaKRm04NormSqIntrinsic (I := I) S (m + 1) t x) := by
    rw [hgm, DifferentialGeometry.Analysis.Laplacian.metric_inner_smul_self]
    exact mul_le_mul_of_nonneg_left
      (inner_gradient_nablaKRm04NormSqIntrinsic_self_le (I := I) S m t x) (sq_nonneg (t ^ m))
  have hB : ((flowG (I := I) S).metric t).inner x
      (gradientAt (I := I) (flowG (I := I) S) t (shiWeightedNormSq (I := I) S (m + 1) t) x)
      (gradientAt (I := I) (flowG (I := I) S) t
        (shiWeightedNormSq (I := I) S (m + 1) t) x) ≤
      (t ^ (m + 1)) ^ 2 * (4 * nablaKRm04NormSqIntrinsic (I := I) S (m + 1) t x *
        nablaKRm04NormSqIntrinsic (I := I) S (m + 1 + 1) t x) := by
    rw [hgm1, DifferentialGeometry.Analysis.Laplacian.metric_inner_smul_self]
    exact mul_le_mul_of_nonneg_left
      (inner_gradient_nablaKRm04NormSqIntrinsic_self_le (I := I) S (m + 1) t x)
      (sq_nonneg (t ^ (m + 1)))
  have hBB : 0 ≤ ((flowG (I := I) S).metric t).inner x
      (gradientAt (I := I) (flowG (I := I) S) t (shiWeightedNormSq (I := I) S (m + 1) t) x)
      (gradientAt (I := I) (flowG (I := I) S) t
        (shiWeightedNormSq (I := I) S (m + 1) t) x) :=
    DifferentialGeometry.metric_inner_self_nonneg
      (I := I) (M := M) ((flowG (I := I) S).metric t) x _
  have hAnn : (0 : Real) ≤ (t ^ m) ^ 2 * (4 * nablaKRm04NormSqIntrinsic (I := I) S m t x *
      nablaKRm04NormSqIntrinsic (I := I) S (m + 1) t x) := by positivity
  have hcs := DifferentialGeometry.Analysis.Laplacian.metric_inner_cauchy_schwarz_sq
    (I := I) (M := M) ((flowG (I := I) S).metric t) x
    (gradientAt (I := I) (flowG (I := I) S) t (shiWeightedNormSq (I := I) S m t) x)
    (gradientAt (I := I) (flowG (I := I) S) t (shiWeightedNormSq (I := I) S (m + 1) t) x)
  have hmul := mul_le_mul hA hB hBB hAnn
  have hexp : (4 * (t ^ m * t ^ (m + 1)) *
      (Real.sqrt (nablaKRm04NormSqIntrinsic (I := I) S m t x) *
        Real.sqrt (nablaKRm04NormSqIntrinsic (I := I) S (m + 1 + 1) t x)) *
      nablaKRm04NormSqIntrinsic (I := I) S (m + 1) t x) ^ 2 =
      ((t ^ m) ^ 2 * (4 * nablaKRm04NormSqIntrinsic (I := I) S m t x *
          nablaKRm04NormSqIntrinsic (I := I) S (m + 1) t x)) *
        ((t ^ (m + 1)) ^ 2 * (4 * nablaKRm04NormSqIntrinsic (I := I) S (m + 1) t x *
          nablaKRm04NormSqIntrinsic (I := I) S (m + 1 + 1) t x)) := by
    have hrw : (4 * (t ^ m * t ^ (m + 1)) *
        (Real.sqrt (nablaKRm04NormSqIntrinsic (I := I) S m t x) *
          Real.sqrt (nablaKRm04NormSqIntrinsic (I := I) S (m + 1 + 1) t x)) *
        nablaKRm04NormSqIntrinsic (I := I) S (m + 1) t x) ^ 2 =
        16 * (t ^ m) ^ 2 * (t ^ (m + 1)) ^ 2 *
          (Real.sqrt (nablaKRm04NormSqIntrinsic (I := I) S m t x) ^ 2) *
          (Real.sqrt (nablaKRm04NormSqIntrinsic (I := I) S (m + 1 + 1) t x) ^ 2) *
          nablaKRm04NormSqIntrinsic (I := I) S (m + 1) t x ^ 2 := by ring
    rw [hrw, hsm, hsm2]
    ring
  have hbnn : (0 : Real) ≤ 4 * (t ^ m * t ^ (m + 1)) *
      (Real.sqrt (nablaKRm04NormSqIntrinsic (I := I) S m t x) *
        Real.sqrt (nablaKRm04NormSqIntrinsic (I := I) S (m + 1 + 1) t x)) *
      nablaKRm04NormSqIntrinsic (I := I) S (m + 1) t x :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num)
      (mul_nonneg (pow_nonneg ht m) (pow_nonneg ht (m + 1))))
      (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))) h1
  have hsq : (((flowG (I := I) S).metric t).inner x
      (gradientAt (I := I) (flowG (I := I) S) t (shiWeightedNormSq (I := I) S m t) x)
      (gradientAt (I := I) (flowG (I := I) S) t
        (shiWeightedNormSq (I := I) S (m + 1) t) x)) ^ 2 ≤
      (4 * (t ^ m * t ^ (m + 1)) *
        (Real.sqrt (nablaKRm04NormSqIntrinsic (I := I) S m t x) *
          Real.sqrt (nablaKRm04NormSqIntrinsic (I := I) S (m + 1 + 1) t x)) *
        nablaKRm04NormSqIntrinsic (I := I) S (m + 1) t x) ^ 2 := by
    rw [hexp]
    exact hcs.trans hmul
  have habs := abs_le_of_sq_le_sq hsq hbnn
  have hneg := neg_le_abs (((flowG (I := I) S).metric t).inner x
    (gradientAt (I := I) (flowG (I := I) S) t (shiWeightedNormSq (I := I) S m t) x)
    (gradientAt (I := I) (flowG (I := I) S) t
      (shiWeightedNormSq (I := I) S (m + 1) t) x))
  linarith

end GradientCrossTerm

section BernsteinProduct

omit [VectorBundle Real E (TangentSpace I : M -> Type _)] in
theorem parabolicOperatorWithDrift_shiHigherBernsteinQuantity_eq
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) (T : Real) (m : Nat) (a : Real)
    {t : Real} (htreg : t ∈ D.regular) (x : M) :
    parabolicOperatorWithDrift (I := I) (flowG (I := I) S) T
        (fun _ y => (0 : TangentSpace I y))
        (shiHigherBernsteinQuantity (I := I) S m a) t x =
      (a + shiWeightedNormSq (I := I) S m t x) *
          parabolicOperatorWithDrift (I := I) (flowG (I := I) S) T
            (fun _ y => (0 : TangentSpace I y))
            (shiWeightedNormSq (I := I) S (m + 1)) t x +
        shiWeightedNormSq (I := I) S (m + 1) t x *
          parabolicOperatorWithDrift (I := I) (flowG (I := I) S) T
            (fun _ y => (0 : TangentSpace I y)) (shiWeightedNormSq (I := I) S m) t x -
        2 * ((flowG (I := I) S).metric t).inner x
          (gradientAt (I := I) (flowG (I := I) S) t (shiWeightedNormSq (I := I) S m t) x)
          (gradientAt (I := I) (flowG (I := I) S) t
            (shiWeightedNormSq (I := I) S (m + 1) t) x) := by
  have hunfold : shiHigherBernsteinQuantity (I := I) S m a =
      fun s (y : M) => (a + shiWeightedNormSq (I := I) S m s y) *
        shiWeightedNormSq (I := I) S (m + 1) s y := rfl
  rw [hunfold]
  exact parabolicOperatorWithDrift_const_add_mul (I := I) (flowG (I := I) S) T
    (fun _ y => (0 : TangentSpace I y)) (shiWeightedNormSq (I := I) S m)
    (shiWeightedNormSq (I := I) S (m + 1)) a t x
    ((differentiableAt_shiWeightedNormSq (I := I) S hS m htreg x).differentiableWithinAt)
    ((differentiableAt_shiWeightedNormSq (I := I) S hS (m + 1) htreg x).differentiableWithinAt)
    (contMDiff_shiWeightedNormSq (I := I) S m t)
    (contMDiff_shiWeightedNormSq (I := I) S (m + 1) t)

omit [VectorBundle Real E (TangentSpace I : M -> Type _)] in
theorem parabolicOperatorWithDrift_shiHigherBernsteinQuantity_le
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) {T Astar : Real} (hT : 0 < T) (hAstar : 1 ≤ Astar)
    (m : Nat) {t : Real} (ht : t ∈ Set.Icc 0 T) (htpos : 0 < t) (htreg : t ∈ D.regular)
    (x : M) (hu0 : nablaKRm04NormSqIntrinsic (I := I) S 0 t x ≤ 1)
    (hIH : ∀ j : Nat, 1 ≤ j → j ≤ m →
      t ^ j * nablaKRm04NormSqIntrinsic (I := I) S j t x ≤ Astar ^ 2) :
    parabolicOperatorWithDrift (I := I) (flowG (I := I) S) T
        (fun _ y => (0 : TangentSpace I y))
        (shiHigherBernsteinQuantity (I := I) S m (shiHigherShift Astar)) t x ≤
      -(2 / 5) * shiWeightedNormSq (I := I) S (m + 1) t x ^ 2 / t +
        shiHigherFConst (Module.finrank Real E) m T Astar *
          (shiWeightedNormSq (I := I) S (m + 1) t x / t) +
        shiHigherFConst (Module.finrank Real E) m T Astar * t := by
  have hAstar0 : (0 : Real) ≤ Astar := le_trans zero_le_one hAstar
  have hTnn : (0 : Real) ≤ T := le_trans ht.1 ht.2
  have htne : t ≠ 0 := ne_of_gt htpos
  have h0 := nablaKRm04NormSqIntrinsic_nonneg (I := I) S m t x
  have h2 := nablaKRm04NormSqIntrinsic_nonneg (I := I) S (m + 1 + 1) t x
  have hIHall : ∀ j : Nat, j ≤ m →
      t ^ j * nablaKRm04NormSqIntrinsic (I := I) S j t x ≤ Astar ^ 2 := by
    intro j hj
    rcases Nat.eq_zero_or_pos j with rfl | hj1
    · have h1 : (1 : Real) ≤ Astar ^ 2 := by nlinarith
      rw [pow_zero, one_mul]
      linarith
    · exact hIH j hj1 hj
  have hLY := parabolicOperatorWithDrift_shiWeightedNormSq_succ_le (I := I) S hS hT hAstar0 m
    ht htpos htreg x hu0 hIH
  have hLX := parabolicOperatorWithDrift_shiWeightedNormSq_le (I := I) S hS hT hAstar0 m
    ht htpos htreg x hIHall
  have hprod := parabolicOperatorWithDrift_shiHigherBernsteinQuantity_eq (I := I) S hS T m
    (shiHigherShift Astar) htreg x
  have hcross := neg_two_inner_gradient_shiWeightedNormSq_le (I := I) S m ht.1 x
  have hY0 : 0 ≤ shiWeightedNormSq (I := I) S (m + 1) t x :=
    shiWeightedNormSq_nonneg (I := I) S (m + 1) ht.1 x
  have hZ0 : (0 : Real) ≤ t ^ (m + 1) *
      nablaKRm04NormSqIntrinsic (I := I) S (m + 1 + 1) t x :=
    mul_nonneg (pow_nonneg ht.1 (m + 1)) h2
  have hsig0 : (0 : Real) ≤ t ^ m * t ^ (m + 1) :=
    mul_nonneg (pow_nonneg ht.1 m) (pow_nonneg ht.1 (m + 1))
  have hq0 : 0 ≤ shiWeightedNormSq (I := I) S (m + 1) t x / t := div_nonneg hY0 htpos.le
  have hXmax : shiWeightedNormSq (I := I) S m t x ≤ Astar ^ 2 := hIHall m le_rfl
  have ha5 : 5 * shiWeightedNormSq (I := I) S m t x ≤
      shiHigherShift Astar + shiWeightedNormSq (I := I) S m t x := by
    unfold shiHigherShift
    linarith [hXmax]
  have haX0 : (0 : Real) ≤ shiHigherShift Astar + shiWeightedNormSq (I := I) S m t x := by
    have := shiHigherShift_pos Astar
    have hX0 : 0 ≤ shiWeightedNormSq (I := I) S m t x :=
      shiWeightedNormSq_nonneg (I := I) S m ht.1 x
    linarith
  have haXle : shiHigherShift Astar + shiWeightedNormSq (I := I) S m t x ≤
      1 + 5 * Astar ^ 2 := by
    unfold shiHigherShift
    linarith [hXmax]
  have hXp : shiWeightedNormSq (I := I) S m t x =
      t * (shiWeightedNormSq (I := I) S m t x / t) := by
    field_simp
  have hYt : shiWeightedNormSq (I := I) S (m + 1) t x =
      t * (shiWeightedNormSq (I := I) S (m + 1) t x / t) := by
    field_simp
  have hXZ : shiWeightedNormSq (I := I) S m t x *
      (t ^ (m + 1) * nablaKRm04NormSqIntrinsic (I := I) S (m + 1 + 1) t x) =
      t ^ m * t ^ (m + 1) *
        (Real.sqrt (nablaKRm04NormSqIntrinsic (I := I) S m t x) *
          Real.sqrt (nablaKRm04NormSqIntrinsic (I := I) S (m + 1 + 1) t x)) ^ 2 := by
    have hsm : Real.sqrt (nablaKRm04NormSqIntrinsic (I := I) S m t x) ^ 2 =
        nablaKRm04NormSqIntrinsic (I := I) S m t x := Real.sq_sqrt h0
    have hsm2 : Real.sqrt (nablaKRm04NormSqIntrinsic (I := I) S (m + 1 + 1) t x) ^ 2 =
        nablaKRm04NormSqIntrinsic (I := I) S (m + 1 + 1) t x := Real.sq_sqrt h2
    have hexp : (Real.sqrt (nablaKRm04NormSqIntrinsic (I := I) S m t x) *
        Real.sqrt (nablaKRm04NormSqIntrinsic (I := I) S (m + 1 + 1) t x)) ^ 2 =
        Real.sqrt (nablaKRm04NormSqIntrinsic (I := I) S m t x) ^ 2 *
          Real.sqrt (nablaKRm04NormSqIntrinsic (I := I) S (m + 1 + 1) t x) ^ 2 := by ring
    rw [hexp, hsm, hsm2]
    unfold shiWeightedNormSq
    ring
  have hYq : shiWeightedNormSq (I := I) S (m + 1) t x *
      (shiWeightedNormSq (I := I) S (m + 1) t x / t) =
      t ^ m * t ^ (m + 1) * nablaKRm04NormSqIntrinsic (I := I) S (m + 1) t x ^ 2 := by
    have hstep : shiWeightedNormSq (I := I) S (m + 1) t x *
        (shiWeightedNormSq (I := I) S (m + 1) t x / t) =
        shiWeightedNormSq (I := I) S (m + 1) t x *
          shiWeightedNormSq (I := I) S (m + 1) t x / t := by ring
    rw [hstep, div_eq_iff htne]
    unfold shiWeightedNormSq
    rw [pow_succ]
    ring
  have hLF : parabolicOperatorWithDrift (I := I) (flowG (I := I) S) T
      (fun _ y => (0 : TangentSpace I y))
      (shiHigherBernsteinQuantity (I := I) S m (shiHigherShift Astar)) t x ≤
      (shiHigherShift Astar + shiWeightedNormSq (I := I) S m t x) *
          parabolicOperatorWithDrift (I := I) (flowG (I := I) S) T
            (fun _ y => (0 : TangentSpace I y))
            (shiWeightedNormSq (I := I) S (m + 1)) t x +
        shiWeightedNormSq (I := I) S (m + 1) t x *
          parabolicOperatorWithDrift (I := I) (flowG (I := I) S) T
            (fun _ y => (0 : TangentSpace I y)) (shiWeightedNormSq (I := I) S m) t x +
        -2 * ((flowG (I := I) S).metric t).inner x
          (gradientAt (I := I) (flowG (I := I) S) t (shiWeightedNormSq (I := I) S m t) x)
          (gradientAt (I := I) (flowG (I := I) S) t
            (shiWeightedNormSq (I := I) S (m + 1) t) x) := by
    rw [hprod]
    linarith
  have hkey := shi_higher_product_le
    (hY0 := hY0) (hZ0 := hZ0) (hsig0 := hsig0)
    (hCY0 := shiHigherLYCoeff_nonneg hTnn (Module.finrank Real E) m Astar)
    (hCX0 := shiHigherLXConst_nonneg hAstar0 (Module.finrank Real E) m)
    (hmm0 := Nat.cast_nonneg m) (hXm0 := sq_nonneg Astar) (hq0 := hq0)
    (ht0 := htpos) (htT := ht.2) (hXmax := hXmax) (ha5 := ha5) (haX0 := haX0)
    (haXle := haXle) (hXp := hXp) (hYt := hYt) (hXZ := hXZ) (hYq := hYq)
    (hLY := hLY) (hLX := hLX) (hcr := hcross) (hLF := hLF)
  have hconv : -(2 / 5) * (shiWeightedNormSq (I := I) S (m + 1) t x *
      (shiWeightedNormSq (I := I) S (m + 1) t x / t)) =
      -(2 / 5) * shiWeightedNormSq (I := I) S (m + 1) t x ^ 2 / t := by ring
  unfold shiHigherFConst
  linarith [hkey, hconv.le, hconv.ge]

omit [VectorBundle Real E (TangentSpace I : M -> Type _)] in
theorem parabolicOperatorWithDrift_shiHigherBernsteinQuantity_sq_le
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) {T Astar : Real} (hT : 0 < T) (hAstar : 1 ≤ Astar)
    (m : Nat) {t : Real} (ht : t ∈ Set.Icc 0 T) (htpos : 0 < t) (htreg : t ∈ D.regular)
    (x : M) (hu0 : nablaKRm04NormSqIntrinsic (I := I) S 0 t x ≤ 1)
    (hIH : ∀ j : Nat, 1 ≤ j → j ≤ m →
      t ^ j * nablaKRm04NormSqIntrinsic (I := I) S j t x ≤ Astar ^ 2) :
    parabolicOperatorWithDrift (I := I) (flowG (I := I) S) T
        (fun _ y => (0 : TangentSpace I y))
        (shiHigherBernsteinQuantity (I := I) S m (shiHigherShift Astar)) t x ≤
      -(shiHigherBernsteinCoeff Astar / t) *
          shiHigherBernsteinQuantity (I := I) S m (shiHigherShift Astar) t x ^ 2 +
        shiHigherBernsteinConst (Module.finrank Real E) m T Astar / t := by
  have hAstar0 : (0 : Real) ≤ Astar := le_trans zero_le_one hAstar
  have hTnn : (0 : Real) ≤ T := le_trans ht.1 ht.2
  have hY0 : 0 ≤ shiWeightedNormSq (I := I) S (m + 1) t x :=
    shiWeightedNormSq_nonneg (I := I) S (m + 1) ht.1 x
  have hX0 : 0 ≤ shiWeightedNormSq (I := I) S m t x :=
    shiWeightedNormSq_nonneg (I := I) S m ht.1 x
  have hIHall : ∀ j : Nat, j ≤ m →
      t ^ j * nablaKRm04NormSqIntrinsic (I := I) S j t x ≤ Astar ^ 2 := by
    intro j hj
    rcases Nat.eq_zero_or_pos j with rfl | hj1
    · have h1 : (1 : Real) ≤ Astar ^ 2 := by nlinarith
      rw [pow_zero, one_mul]
      linarith
    · exact hIH j hj1 hj
  have hXmax : shiWeightedNormSq (I := I) S m t x ≤ Astar ^ 2 := hIHall m le_rfl
  have hunfoldF : shiHigherBernsteinQuantity (I := I) S m (shiHigherShift Astar) t x =
      (shiHigherShift Astar + shiWeightedNormSq (I := I) S m t x) *
        shiWeightedNormSq (I := I) S (m + 1) t x := rfl
  have hlow : shiHigherShift Astar * shiWeightedNormSq (I := I) S (m + 1) t x ≤
      shiHigherBernsteinQuantity (I := I) S m (shiHigherShift Astar) t x := by
    rw [hunfoldF]
    nlinarith [mul_nonneg hX0 hY0]
  have hhigh : shiHigherBernsteinQuantity (I := I) S m (shiHigherShift Astar) t x ≤
      (1 + 5 * Astar ^ 2) * shiWeightedNormSq (I := I) S (m + 1) t x := by
    rw [hunfoldF]
    have hle : shiHigherShift Astar + shiWeightedNormSq (I := I) S m t x ≤
        1 + 5 * Astar ^ 2 := by
      unfold shiHigherShift
      linarith [hXmax]
    exact mul_le_mul_of_nonneg_right hle hY0
  have hab : shiHigherShift Astar ≤ 1 + 5 * Astar ^ 2 := by
    unfold shiHigherShift
    nlinarith [sq_nonneg Astar]
  have hmain := parabolicOperatorWithDrift_shiHigherBernsteinQuantity_le (I := I) S hS hT
    hAstar m ht htpos htreg x hu0 hIH
  have habs := shi_higher_bernstein_absorption (shiHigherShift_pos Astar) hab hY0
    (shiHigherFConst_nonneg hTnn hAstar0 (Module.finrank Real E) m) htpos ht.2 hlow hhigh
    hmain
  unfold shiHigherBernsteinCoeff shiHigherBernsteinConst
  exact habs

end BernsteinProduct

section Regularity

omit [NeZero (Module.finrank Real E)] [I.Boundaryless] [BoundarylessManifold I M]
  [VectorBundle Real E (TangentSpace I : M -> Type _)] in
theorem shiHigherBernsteinQuantity_nonneg
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) (m : Nat) {a t : Real}
    (ha : 0 ≤ a) (ht : 0 ≤ t) (x : M) :
    0 ≤ shiHigherBernsteinQuantity (I := I) S m a t x := by
  have hX := shiWeightedNormSq_nonneg (I := I) S m ht x
  have hY := shiWeightedNormSq_nonneg (I := I) S (m + 1) ht x
  unfold shiHigherBernsteinQuantity
  have : (0 : Real) ≤ a + shiWeightedNormSq (I := I) S m t x := by linarith
  exact mul_nonneg this hY

omit [NeZero (Module.finrank Real E)] [I.Boundaryless] [BoundarylessManifold I M]
  [VectorBundle Real E (TangentSpace I : M -> Type _)] in
theorem shiHigherBernsteinQuantity_zero
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) (m : Nat) (a : Real)
    (x : M) :
    shiHigherBernsteinQuantity (I := I) S m a 0 x = 0 := by
  unfold shiHigherBernsteinQuantity
  rw [shiWeightedNormSq_zero_of_ne_zero (I := I) S (Nat.succ_ne_zero m) x, mul_zero]

omit [NeZero (Module.finrank Real E)] [I.Boundaryless] [BoundarylessManifold I M]
  [VectorBundle Real E (TangentSpace I : M -> Type _)] in
theorem contMDiff_shiHigherBernsteinQuantity
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) (m : Nat) (a t : Real) :
    ContMDiff I 𝓘(Real, Real) ∞ (shiHigherBernsteinQuantity (I := I) S m a t) :=
  (contMDiff_const.add (contMDiff_shiWeightedNormSq (I := I) S m t)).mul
    (contMDiff_shiWeightedNormSq (I := I) S (m + 1) t)

omit [VectorBundle Real E (TangentSpace I : M -> Type _)] in
theorem differentiableAt_shiHigherBernsteinQuantity
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) (m : Nat) (a : Real)
    {t : Real} (htreg : t ∈ D.regular) (x : M) :
    DifferentiableAt Real
      (fun s : Real => shiHigherBernsteinQuantity (I := I) S m a s x) t :=
  ((differentiableAt_const a).add
      (differentiableAt_shiWeightedNormSq (I := I) S hS m htreg x)).mul
    (differentiableAt_shiWeightedNormSq (I := I) S hS (m + 1) htreg x)

omit [NeZero (Module.finrank Real E)]
  [VectorBundle Real E (TangentSpace I : M -> Type _)] in
theorem continuousOn_shiHigherBernsteinQuantity
    {alpha omega T a : Real} {halphaomega : alpha < omega}
    {S : SolutionOn (I := I) (M := M)
      (RealTimeInterval.closedOpen alpha omega halphaomega)}
    (hS : IsSolutionOn (I := I) S) (m : Nat) (halpha : alpha < 0) (hTomega : T < omega) :
    ContinuousOn
      (fun p : Real × M => shiHigherBernsteinQuantity (I := I) S m a p.1 p.2)
      (spacetimeSlab (M := M) T) := by
  have hsub : spacetimeSlab (M := M) T ⊆
      (RealTimeInterval.closedOpen alpha omega halphaomega).regular ×ˢ
        (Set.univ : Set M) := by
    rintro ⟨s, y⟩ hp
    exact ⟨⟨lt_of_lt_of_le halpha hp.1.1, lt_of_le_of_lt hp.1.2 hTomega⟩, trivial⟩
  have h0 := ((towerNorm_joint (I := I) hS m).continuousOn).mono hsub
  have h1 := ((towerNorm_joint (I := I) hS (m + 1)).continuousOn).mono hsub
  have hres : ContinuousOn
      (fun p : Real × M =>
        (a + p.1 ^ m * nablaKRm04NormSqIntrinsic (I := I) S m p.1 p.2) *
          (p.1 ^ (m + 1) * nablaKRm04NormSqIntrinsic (I := I) S (m + 1) p.1 p.2))
      (spacetimeSlab (M := M) T) :=
    (continuousOn_const.add ((continuous_fst.continuousOn.pow m).mul h0)).mul
      ((continuous_fst.continuousOn.pow (m + 1)).mul h1)
  exact hres

end Regularity

section CutoffConsequence

theorem shiHigherBernsteinQuantity_cutoff_le
    {alpha omega T Astar eps : Real} {halphaomega : alpha < omega}
    (S : SolutionOn (I := I) (M := M)
      (RealTimeInterval.closedOpen alpha omega halphaomega))
    (hS : IsSolutionOn (I := I) S) (m : Nat)
    (cut : ShiFixedCutoff (I := I) (flowG (I := I) S) T eps)
    (halpha : alpha < 0) (hT : 0 < T) (hTomega : T < omega) (hAstar : 1 ≤ Astar)
    (hu0 : ∀ s ∈ Set.Icc (0 : Real) T, 0 < s → ∀ y : M, 0 < cut.chi s y →
      nablaKRm04NormSqIntrinsic (I := I) S 0 s y ≤ 1)
    (hIH : ∀ j : Nat, 1 ≤ j → j ≤ m → ∀ s ∈ Set.Icc (0 : Real) T, 0 < s → ∀ y : M,
      0 < cut.chi s y → s ^ j * nablaKRm04NormSqIntrinsic (I := I) S j s y ≤ Astar ^ 2) :
    ∀ t ∈ Set.Icc (0 : Real) T, ∀ x : M,
      cut.chi t x * shiHigherBernsteinQuantity (I := I) S m (shiHigherShift Astar) t x ≤
        bernsteinMaximumBound (shiHigherBernsteinCoeff Astar)
          (shiHigherBernsteinConst (Module.finrank Real E) m T Astar) eps T := by
  have hAstar0 : (0 : Real) ≤ Astar := le_trans zero_le_one hAstar
  have hreg : Set.Icc 0 T ⊆
      (RealTimeInterval.closedOpen alpha omega halphaomega).regular := by
    intro s hs
    exact ⟨lt_of_lt_of_le halpha hs.1, lt_of_le_of_lt hs.2 hTomega⟩
  refine bernstein_maximum_of_fixed_cutoff (I := I) cut
    (shiHigherBernsteinQuantity (I := I) S m (shiHigherShift Astar)) hT
    (shiHigherBernsteinCoeff_pos Astar)
    (shiHigherBernsteinConst_nonneg hT.le hAstar0 (Module.finrank Real E) m)
    (fun s hs y => shiHigherBernsteinQuantity_nonneg (I := I) S m
      (shiHigherShift_pos Astar).le hs.1 y)
    (fun y => shiHigherBernsteinQuantity_zero (I := I) S m (shiHigherShift Astar) y)
    (continuousOn_shiHigherBernsteinQuantity (I := I) hS m halpha hTomega)
    (fun s hs _ y =>
      (differentiableAt_shiHigherBernsteinQuantity (I := I) S hS m (shiHigherShift Astar)
        (hreg hs) y).differentiableWithinAt)
    (fun s hs _ y =>
      (contMDiff_shiHigherBernsteinQuantity (I := I) S m (shiHigherShift Astar)
        s).contMDiffAt.mdifferentiableAt (by simp))
    (fun s hs _ y =>
      gradientFun_mdiffAt (I := I) ((flowG (I := I) S).metric s)
        (contMDiff_shiHigherBernsteinQuantity (I := I) S m (shiHigherShift Astar) s) y)
    (fun s hs hspos y hchi =>
      parabolicOperatorWithDrift_shiHigherBernsteinQuantity_sq_le (I := I) S hS hT hAstar m
        hs hspos (hreg hs) y (hu0 s hs hspos y hchi)
        (fun j hj1 hjm => hIH j hj1 hjm s hs hspos y hchi))

theorem tpow_succ_mul_nablaKRm04NormSqIntrinsic_le_of_fixedCutoff
    {alpha omega T Astar eps : Real} {halphaomega : alpha < omega}
    (S : SolutionOn (I := I) (M := M)
      (RealTimeInterval.closedOpen alpha omega halphaomega))
    (hS : IsSolutionOn (I := I) S) (m : Nat)
    (cut : ShiFixedCutoff (I := I) (flowG (I := I) S) T eps)
    {Omega Omega' : Set M}
    (halpha : alpha < 0) (hT : 0 < T) (hTomega : T < omega) (hAstar : 1 ≤ Astar)
    (hsupp : cut.support ⊆ Omega)
    (hone : ∀ s ∈ Set.Icc (0 : Real) T, ∀ y ∈ Omega', cut.chi s y = 1)
    (hu0 : ∀ s ∈ Set.Ioc (0 : Real) T, ∀ y ∈ Omega,
      nablaKRm04NormSqIntrinsic (I := I) S 0 s y ≤ 1)
    (hIH : ∀ j : Nat, 1 ≤ j → j ≤ m → ∀ s ∈ Set.Ioc (0 : Real) T, ∀ y ∈ Omega,
      s ^ j * nablaKRm04NormSqIntrinsic (I := I) S j s y ≤ Astar ^ 2) :
    ∀ t ∈ Set.Ioc (0 : Real) T, ∀ x ∈ Omega',
      t ^ (m + 1) * nablaKRm04NormSqIntrinsic (I := I) S (m + 1) t x ≤
        shiHigherStepBound (Module.finrank Real E) m T Astar eps := by
  have hmem : ∀ s ∈ Set.Icc (0 : Real) T, ∀ y : M, 0 < cut.chi s y → y ∈ Omega := by
    intro s hs y hchi
    by_contra hy
    have hzero := cut.support_zero s hs y (fun hmem => hy (hsupp hmem))
    rw [hzero] at hchi
    exact lt_irrefl 0 hchi
  have hcut := shiHigherBernsteinQuantity_cutoff_le (I := I) S hS m cut halpha hT hTomega
    hAstar
    (fun s hs hspos y hchi => hu0 s ⟨hspos, hs.2⟩ y (hmem s hs y hchi))
    (fun j hj1 hjm s hs hspos y hchi => hIH j hj1 hjm s ⟨hspos, hs.2⟩ y (hmem s hs y hchi))
  intro t ht x hx
  have htIcc : t ∈ Set.Icc (0 : Real) T := ⟨ht.1.le, ht.2⟩
  have hval := hcut t htIcc x
  rw [hone t htIcc x hx, one_mul] at hval
  have hX0 : 0 ≤ shiWeightedNormSq (I := I) S m t x :=
    shiWeightedNormSq_nonneg (I := I) S m ht.1.le x
  have hY0 : 0 ≤ shiWeightedNormSq (I := I) S (m + 1) t x :=
    shiWeightedNormSq_nonneg (I := I) S (m + 1) ht.1.le x
  have hunfoldF : shiHigherBernsteinQuantity (I := I) S m (shiHigherShift Astar) t x =
      (shiHigherShift Astar + shiWeightedNormSq (I := I) S m t x) *
        shiWeightedNormSq (I := I) S (m + 1) t x := rfl
  have hlow : shiHigherShift Astar * shiWeightedNormSq (I := I) S (m + 1) t x ≤
      shiHigherBernsteinQuantity (I := I) S m (shiHigherShift Astar) t x := by
    rw [hunfoldF]
    nlinarith [mul_nonneg hX0 hY0]
  have hstep : shiWeightedNormSq (I := I) S (m + 1) t x ≤
      shiHigherStepBound (Module.finrank Real E) m T Astar eps := by
    unfold shiHigherStepBound
    rw [le_div_iff₀ (shiHigherShift_pos Astar)]
    nlinarith [hlow, hval]
  exact hstep

end CutoffConsequence

end DifferentialGeometry.PDE.RicciFlow
