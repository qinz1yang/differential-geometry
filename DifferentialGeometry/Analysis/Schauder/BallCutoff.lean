import DifferentialGeometry.Analysis.Calculus.BallCutoff
import DifferentialGeometry.Analysis.Parabolic.Euclidean.FrozenDuhamel
import DifferentialGeometry.Analysis.Schauder.CutoffExistence
import DifferentialGeometry.Analysis.Schauder.Localization

set_option autoImplicit false

noncomputable section

open Real
open scoped ContDiff RealInnerProductSpace

namespace DifferentialGeometry.Analysis.Schauder

open DifferentialGeometry.Analysis.Parabolic.Euclidean

variable {V : Type*}
  [NormedAddCommGroup V] [InnerProductSpace Real V] [FiniteDimensional Real V]

def ballCutoffLaplacian (center : V) (r R : Real) (x : V) : Real :=
  deriv CutoffProfile.value (ballCutoffArgument center r R x) *
      (2 * Module.finrank Real V / (R ^ 2 - r ^ 2)) +
    deriv (deriv CutoffProfile.value) (ballCutoffArgument center r R x) *
      ((2 / (R ^ 2 - r ^ 2)) ^ 2 * ‖x - center‖ ^ 2)

def ballNormSqFDeriv (center x : V) : V →L[Real] Real :=
  (2 : Nat) • innerSL Real (x - center)

omit [FiniteDimensional Real V] in
@[simp]
theorem ballNormSqFDeriv_apply (center x v : V) :
    ballNormSqFDeriv center x v = 2 * inner Real (x - center) v := by
  simp only [ballNormSqFDeriv, two_nsmul, ContinuousLinearMap.add_apply,
    coe_innerSL_apply]
  ring

def ballCutoffLaplacianFDeriv
    (center : V) (r R : Real) (x : V) : V →L[Real] Real :=
  ((2 * Module.finrank Real V / (R ^ 2 - r ^ 2)) *
      deriv (deriv CutoffProfile.value) (ballCutoffArgument center r R x)) •
      ballCutoffArgumentFDeriv center r R x +
    (((2 / (R ^ 2 - r ^ 2)) ^ 2 * ‖x - center‖ ^ 2) *
      deriv (deriv (deriv CutoffProfile.value))
        (ballCutoffArgument center r R x)) •
      ballCutoffArgumentFDeriv center r R x +
    ((2 / (R ^ 2 - r ^ 2)) ^ 2 *
      deriv (deriv CutoffProfile.value) (ballCutoffArgument center r R x)) •
      ballNormSqFDeriv center x

def ballCutoffLaplacianBound (r R : Real) : Real :=
  CutoffProfile.derivBound *
    (2 * Module.finrank Real V / (R ^ 2 - r ^ 2) +
      (2 / (R ^ 2 - r ^ 2)) ^ 2 * R ^ 2)

def ballCutoffLaplacianFDerivBound (r R : Real) : Real :=
  CutoffProfile.derivBound *
      (2 * Module.finrank Real V / (R ^ 2 - r ^ 2)) *
      (2 * R / (R ^ 2 - r ^ 2)) +
    CutoffProfile.deriv3Bound *
      ((2 / (R ^ 2 - r ^ 2)) ^ 2 * R ^ 2) *
      (2 * R / (R ^ 2 - r ^ 2)) +
    CutoffProfile.derivBound * (2 / (R ^ 2 - r ^ 2)) ^ 2 * (2 * R)

def ballCutoffLaplacianHolderConst (r R : Real) : NNReal :=
  max (2 * Real.toNNReal (ballCutoffLaplacianBound (V := V) r R))
    (Real.toNNReal (ballCutoffLaplacianFDerivBound (V := V) r R))

def ballCutoffHolderConst (r R : Real) : NNReal :=
  max 2 (Real.toNNReal (ballCutoffFDerivBound r R))

def ballCutoffFDerivHolderConst (r R : Real) : NNReal :=
  max (2 * Real.toNNReal (ballCutoffFDerivBound r R))
    (Real.toNNReal (ballCutoffFDeriv2Bound r R))

omit [FiniteDimensional Real V] in
theorem hasFDerivAt_ballNormSq (center x : V) :
    HasFDerivAt (fun y : V ↦ ‖y - center‖ ^ 2)
      (ballNormSqFDeriv center x) x := by
  simpa [ballNormSqFDeriv] using
    ((hasFDerivAt_id x).sub_const center).norm_sq

omit [FiniteDimensional Real V] in
theorem norm_ballNormSqFDeriv_le
    {center x : V} {R : Real} (hx : dist x center ≤ R) :
    ‖ballNormSqFDeriv center x‖ ≤ 2 * R := by
  have hdist : ‖x - center‖ ≤ R := by
    simpa [dist_eq_norm] using hx
  rw [ballNormSqFDeriv, RCLike.norm_nsmul Real,
    innerSL_apply_norm, nsmul_eq_mul]
  exact mul_le_mul_of_nonneg_left hdist (by norm_num)

omit [FiniteDimensional Real V] in
theorem ballCutoffLaplacianBound_nonneg
    {r R : Real} (hr : 0 ≤ r) (hrR : r < R) :
    0 ≤ ballCutoffLaplacianBound (V := V) r R := by
  have hden : 0 < R ^ 2 - r ^ 2 := by nlinarith
  exact mul_nonneg CutoffProfile.derivBound_nonneg
    (add_nonneg
      (div_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg _)) hden.le)
      (mul_nonneg (sq_nonneg _) (sq_nonneg _)))

omit [FiniteDimensional Real V] in
theorem ballCutoffLaplacianFDerivBound_nonneg
    {r R : Real} (hr : 0 ≤ r) (hrR : r < R) :
    0 ≤ ballCutoffLaplacianFDerivBound (V := V) r R := by
  have hden : 0 < R ^ 2 - r ^ 2 := by nlinarith
  have hR : 0 ≤ R := hr.trans hrR.le
  have hA : 0 ≤ 2 * Module.finrank Real V / (R ^ 2 - r ^ 2) :=
    div_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg _)) hden.le
  have hB : 0 ≤ (2 / (R ^ 2 - r ^ 2)) ^ 2 := sq_nonneg _
  have hs : 0 ≤ 2 * R / (R ^ 2 - r ^ 2) :=
    div_nonneg (mul_nonneg (by norm_num) hR) hden.le
  unfold ballCutoffLaplacianFDerivBound
  exact add_nonneg
    (add_nonneg
      (mul_nonneg (mul_nonneg CutoffProfile.derivBound_nonneg hA) hs)
      (mul_nonneg
        (mul_nonneg CutoffProfile.deriv3Bound_nonneg
          (mul_nonneg hB (sq_nonneg R))) hs))
    (mul_nonneg
      (mul_nonneg CutoffProfile.derivBound_nonneg hB)
      (mul_nonneg (by norm_num) hR))

omit [FiniteDimensional Real V] in
theorem hasFDerivAt_ballCutoffLaplacian
    (center : V) (r R : Real) (x : V) :
    HasFDerivAt (ballCutoffLaplacian center r R)
      (ballCutoffLaplacianFDeriv center r R x) x := by
  let a := ballCutoffArgument center r R x
  let A := 2 * Module.finrank Real V / (R ^ 2 - r ^ 2)
  let B := (2 / (R ^ 2 - r ^ 2)) ^ 2
  have hle3 : (3 : WithTop ℕ∞) ≤ (∞ : WithTop ℕ∞) := by
    have h : ((3 : ℕ∞) : WithTop ℕ∞) ≤
        (∞ : WithTop ℕ∞) := by
      exact_mod_cast (le_top : (3 : ℕ∞) ≤ ⊤)
    exact h
  have hprofile1 : HasDerivAt (deriv CutoffProfile.value)
      (deriv (deriv CutoffProfile.value) a) a :=
    (CutoffProfile.contDiff.of_le hle3).deriv' (n := 2) |>.differentiable
      (by simp) a |>.hasDerivAt
  have hprofile2 : HasDerivAt (deriv (deriv CutoffProfile.value))
      (deriv (deriv (deriv CutoffProfile.value)) a) a :=
    ((CutoffProfile.contDiff.of_le hle3).deriv' (n := 2)).deriv' (n := 1)
      |>.differentiable (by simp) a |>.hasDerivAt
  have ha1 : HasFDerivAt
      (fun y : V ↦ deriv CutoffProfile.value
        (ballCutoffArgument center r R y))
      (deriv (deriv CutoffProfile.value) a •
        ballCutoffArgumentFDeriv center r R x) x := by
    simpa only [a, Function.comp_def] using
      hprofile1.comp_hasFDerivAt x
        (hasFDerivAt_ballCutoffArgument center r R x)
  have ha2 : HasFDerivAt
      (fun y : V ↦ deriv (deriv CutoffProfile.value)
        (ballCutoffArgument center r R y))
      (deriv (deriv (deriv CutoffProfile.value)) a •
        ballCutoffArgumentFDeriv center r R x) x := by
    simpa only [a, Function.comp_def] using
      hprofile2.comp_hasFDerivAt x
        (hasFDerivAt_ballCutoffArgument center r R x)
  have hfirst := ha1.mul_const A
  have hsecond := ha2.mul
    ((hasFDerivAt_ballNormSq center x).mul_const B)
  have hsum := hfirst.add hsecond
  convert hsum using 1
  · funext y
    simp only [ballCutoffLaplacian, A, B, Pi.add_apply, Pi.mul_apply]
    ring
  · ext v
    simp only [ballCutoffLaplacianFDeriv, ballNormSqFDeriv_apply,
      a, A, B, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.smul_apply, smul_eq_mul]
    ring

omit [FiniteDimensional Real V] in
theorem abs_ballCutoffLaplacian_le
    {center : V} {r R : Real} (hr : 0 ≤ r) (hrR : r < R) (x : V) :
    |ballCutoffLaplacian center r R x| ≤
      ballCutoffLaplacianBound (V := V) r R := by
  have hden : 0 < R ^ 2 - r ^ 2 := by nlinarith
  have hR : 0 ≤ R := hr.trans hrR.le
  let A : Real := 2 * Module.finrank Real V / (R ^ 2 - r ^ 2)
  let B : Real := (2 / (R ^ 2 - r ^ 2)) ^ 2
  have hA : 0 ≤ A :=
    div_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg _)) hden.le
  have hB : 0 ≤ B := sq_nonneg _
  by_cases hx : dist x center ≤ R
  · have hdist : ‖x - center‖ ≤ R := by
      simpa [dist_eq_norm] using hx
    have hsq : ‖x - center‖ ^ 2 ≤ R ^ 2 :=
      (sq_le_sq₀ (norm_nonneg _) hR).2 hdist
    change
      |deriv CutoffProfile.value (ballCutoffArgument center r R x) * A +
        deriv (deriv CutoffProfile.value)
          (ballCutoffArgument center r R x) *
            (B * ‖x - center‖ ^ 2)| ≤ _
    calc
      _ ≤
          |deriv CutoffProfile.value (ballCutoffArgument center r R x) * A| +
            |deriv (deriv CutoffProfile.value)
              (ballCutoffArgument center r R x) *
                (B * ‖x - center‖ ^ 2)| := abs_add_le _ _
      _ =
          |deriv CutoffProfile.value (ballCutoffArgument center r R x)| * A +
            |deriv (deriv CutoffProfile.value)
              (ballCutoffArgument center r R x)| *
                (B * ‖x - center‖ ^ 2) := by
          rw [abs_mul, abs_mul, abs_of_nonneg hA, abs_mul,
            abs_of_nonneg hB,
            abs_of_nonneg (sq_nonneg ‖x - center‖)]
      _ ≤ CutoffProfile.derivBound * A +
          CutoffProfile.derivBound * (B * R ^ 2) :=
        add_le_add
          (mul_le_mul_of_nonneg_right
            (CutoffProfile.abs_deriv_le_derivBound _) hA)
          (mul_le_mul
            (CutoffProfile.abs_deriv2_le_derivBound _)
            (mul_le_mul_of_nonneg_left hsq hB)
            (mul_nonneg hB (sq_nonneg _))
            CutoffProfile.derivBound_nonneg)
      _ = ballCutoffLaplacianBound (V := V) r R := by
        simp only [ballCutoffLaplacianBound, A, B]
        ring
  · have harg : 2 ≤ ballCutoffArgument center r R x :=
      two_le_ballCutoffArgument_of_not_le hr hrR hx
    simp only [ballCutoffLaplacian,
      CutoffProfile.deriv_zero_of_ge harg,
      CutoffProfile.deriv2_zero_of_ge harg, zero_mul, zero_add, abs_zero]
    exact ballCutoffLaplacianBound_nonneg hr hrR

omit [FiniteDimensional Real V] in
theorem norm_ballCutoffLaplacianFDeriv_le
    {center : V} {r R : Real} (hr : 0 ≤ r) (hrR : r < R) (x : V) :
    ‖ballCutoffLaplacianFDeriv center r R x‖ ≤
      ballCutoffLaplacianFDerivBound (V := V) r R := by
  have hden : 0 < R ^ 2 - r ^ 2 := by nlinarith
  have hR : 0 ≤ R := hr.trans hrR.le
  let a := ballCutoffArgument center r R x
  let A : Real := 2 * Module.finrank Real V / (R ^ 2 - r ^ 2)
  let B : Real := (2 / (R ^ 2 - r ^ 2)) ^ 2
  let s : Real := 2 * R / (R ^ 2 - r ^ 2)
  have hA : 0 ≤ A :=
    div_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg _)) hden.le
  have hB : 0 ≤ B := sq_nonneg _
  have hs : 0 ≤ s :=
    div_nonneg (mul_nonneg (by norm_num) hR) hden.le
  by_cases hx : dist x center ≤ R
  · have hdist : ‖x - center‖ ≤ R := by
      simpa [dist_eq_norm] using hx
    have hsq : ‖x - center‖ ^ 2 ≤ R ^ 2 :=
      (sq_le_sq₀ (norm_nonneg _) hR).2 hdist
    have hdarg : ‖ballCutoffArgumentFDeriv center r R x‖ ≤ s :=
      norm_ballCutoffArgumentFDeriv_le hr hrR hx
    have hdnorm : ‖ballNormSqFDeriv center x‖ ≤ 2 * R :=
      norm_ballNormSqFDeriv_le hx
    have hterm1 :
        ‖(A * deriv (deriv CutoffProfile.value) a) •
            ballCutoffArgumentFDeriv center r R x‖ ≤
          (A * CutoffProfile.derivBound) * s := by
      rw [norm_smul, Real.norm_eq_abs, abs_mul, abs_of_nonneg hA]
      exact mul_le_mul
        (mul_le_mul_of_nonneg_left
          (CutoffProfile.abs_deriv2_le_derivBound a) hA)
        hdarg (norm_nonneg _)
        (mul_nonneg hA CutoffProfile.derivBound_nonneg)
    have hterm2 :
        ‖((B * ‖x - center‖ ^ 2) *
              deriv (deriv (deriv CutoffProfile.value)) a) •
            ballCutoffArgumentFDeriv center r R x‖ ≤
          ((B * R ^ 2) * CutoffProfile.deriv3Bound) * s := by
      rw [norm_smul, Real.norm_eq_abs, abs_mul, abs_mul,
        abs_of_nonneg hB,
        abs_of_nonneg (sq_nonneg ‖x - center‖)]
      have hcoefficient :
          (B * ‖x - center‖ ^ 2) *
              |deriv (deriv (deriv CutoffProfile.value)) a| ≤
            (B * R ^ 2) * CutoffProfile.deriv3Bound :=
        mul_le_mul
          (mul_le_mul_of_nonneg_left hsq hB)
          (CutoffProfile.abs_deriv3_le_deriv3Bound a)
          (abs_nonneg _)
          (mul_nonneg hB (sq_nonneg R))
      exact mul_le_mul hcoefficient hdarg (norm_nonneg _)
        (mul_nonneg (mul_nonneg hB (sq_nonneg R))
          CutoffProfile.deriv3Bound_nonneg)
    have hterm3 :
        ‖(B * deriv (deriv CutoffProfile.value) a) •
            ballNormSqFDeriv center x‖ ≤
          (B * CutoffProfile.derivBound) * (2 * R) := by
      rw [norm_smul, Real.norm_eq_abs, abs_mul, abs_of_nonneg hB]
      exact mul_le_mul
        (mul_le_mul_of_nonneg_left
          (CutoffProfile.abs_deriv2_le_derivBound a) hB)
        hdnorm (norm_nonneg _)
        (mul_nonneg hB CutoffProfile.derivBound_nonneg)
    change ‖(A * deriv (deriv CutoffProfile.value) a) •
        ballCutoffArgumentFDeriv center r R x +
      ((B * ‖x - center‖ ^ 2) *
        deriv (deriv (deriv CutoffProfile.value)) a) •
          ballCutoffArgumentFDeriv center r R x +
      (B * deriv (deriv CutoffProfile.value) a) •
        ballNormSqFDeriv center x‖ ≤ _
    calc
      _ ≤
          (‖(A * deriv (deriv CutoffProfile.value) a) •
              ballCutoffArgumentFDeriv center r R x‖ +
            ‖((B * ‖x - center‖ ^ 2) *
                deriv (deriv (deriv CutoffProfile.value)) a) •
              ballCutoffArgumentFDeriv center r R x‖) +
            ‖(B * deriv (deriv CutoffProfile.value) a) •
              ballNormSqFDeriv center x‖ :=
        (norm_add_le _ _).trans
          (add_le_add (norm_add_le _ _) (le_refl _))
      _ ≤
          ((A * CutoffProfile.derivBound) * s +
            ((B * R ^ 2) * CutoffProfile.deriv3Bound) * s) +
          (B * CutoffProfile.derivBound) * (2 * R) :=
        add_le_add (add_le_add hterm1 hterm2) hterm3
      _ = ballCutoffLaplacianFDerivBound (V := V) r R := by
        simp only [ballCutoffLaplacianFDerivBound, A, B, s]
        ring
  · have harg : 2 ≤ ballCutoffArgument center r R x :=
      two_le_ballCutoffArgument_of_not_le hr hrR hx
    have hz : ballCutoffLaplacianFDeriv center r R x = 0 := by
      ext v
      simp [ballCutoffLaplacianFDeriv,
        CutoffProfile.deriv2_zero_of_ge harg,
        CutoffProfile.deriv3_zero_of_ge harg]
    rw [hz, norm_zero]
    exact ballCutoffLaplacianFDerivBound_nonneg hr hrR

omit [FiniteDimensional Real V] in
theorem ballCutoffLaplacian_holderWith
    {center : V} {r R : Real} (hr : 0 ≤ r) (hrR : r < R)
    {alpha : NNReal} (halpha0 : 0 ≤ alpha) (halpha1 : alpha ≤ 1) :
    HolderWith (ballCutoffLaplacianHolderConst (V := V) r R) alpha
      (ballCutoffLaplacian center r R) := by
  have hM := ballCutoffLaplacianBound_nonneg (V := V) hr hrR
  have hN := ballCutoffLaplacianFDerivBound_nonneg (V := V) hr hrR
  apply holderWith_of_hasFDerivAt_of_norm_le
    (M := Real.toNNReal (ballCutoffLaplacianBound (V := V) r R))
    (N := Real.toNNReal (ballCutoffLaplacianFDerivBound (V := V) r R))
    halpha0 halpha1
  · exact hasFDerivAt_ballCutoffLaplacian center r R
  · intro x
    rw [Real.norm_eq_abs, Real.coe_toNNReal _ hM]
    exact abs_ballCutoffLaplacian_le hr hrR x
  · intro x
    rw [Real.coe_toNNReal _ hN]
    exact norm_ballCutoffLaplacianFDeriv_le hr hrR x

omit [FiniteDimensional Real V] in
theorem ballCutoff_holderWith
    {center : V} {r R : Real} (hr : 0 ≤ r) (hrR : r < R)
    {alpha : NNReal} (halpha0 : 0 ≤ alpha) (halpha1 : alpha ≤ 1) :
    HolderWith (ballCutoffHolderConst r R) alpha
      (ballCutoff center r R) := by
  have hN := ballCutoffFDerivBound_nonneg hr hrR
  have h : HolderWith
      (max (2 * (1 : NNReal))
        (Real.toNNReal (ballCutoffFDerivBound r R))) alpha
      (ballCutoff center r R) := by
    apply holderWith_of_hasFDerivAt_of_norm_le
      (M := (1 : NNReal))
      (N := Real.toNNReal (ballCutoffFDerivBound r R))
      halpha0 halpha1
    · exact hasFDerivAt_ballCutoff center r R
    · intro x
      rw [Real.norm_eq_abs,
        abs_of_nonneg (ballCutoff_mem_Icc center r R x).1]
      exact (ballCutoff_mem_Icc center r R x).2
    · intro x
      rw [Real.coe_toNNReal _ hN]
      exact norm_ballCutoffFDeriv_le hr hrR x
  simpa only [ballCutoffHolderConst, mul_one] using h

omit [FiniteDimensional Real V] in
theorem ballCutoffFDeriv_holderWith
    {center : V} {r R : Real} (hr : 0 ≤ r) (hrR : r < R)
    {alpha : NNReal} (halpha0 : 0 ≤ alpha) (halpha1 : alpha ≤ 1) :
    HolderWith (ballCutoffFDerivHolderConst r R) alpha
      (ballCutoffFDeriv center r R) := by
  have hM := ballCutoffFDerivBound_nonneg hr hrR
  have hN := ballCutoffFDeriv2Bound_nonneg hr hrR
  apply holderWith_of_hasFDerivAt_of_norm_le
    (M := Real.toNNReal (ballCutoffFDerivBound r R))
    (N := Real.toNNReal (ballCutoffFDeriv2Bound r R))
    halpha0 halpha1
  · exact hasFDerivAt_ballCutoffFDeriv center r R
  · intro x
    rw [Real.coe_toNNReal _ hM]
    exact norm_ballCutoffFDeriv_le hr hrR x
  · intro x
    rw [Real.coe_toNNReal _ hN]
    exact norm_ballCutoffFDeriv2_le hr hrR x

def ballCutoffBcf
    (center : V) {r R : Real} (hr : 0 ≤ r) (hrR : r < R) :
    BoundedContinuousFunction V Real :=
  compactSupportBcf (ballCutoff center r R)
    (ballCutoff_contDiff center r R).continuous
    (ballCutoff_hasCompactSupport hr hrR)

def ballCutoffFDerivBcf
    (center : V) {r R : Real} (hr : 0 ≤ r) (hrR : r < R) :
    BoundedContinuousFunction V (V →L[Real] Real) :=
  compactSupportBcf (ballCutoffFDeriv center r R)
    (ballCutoffFDeriv_contDiff center r R).continuous
    (ballCutoffFDeriv_hasCompactSupport hr hrR)

def ballCutoffFDeriv2Bcf
    (center : V) {r R : Real} (hr : 0 ≤ r) (hrR : r < R) :
    BoundedContinuousFunction V (V →L[Real] V →L[Real] Real) :=
  compactSupportBcf (ballCutoffFDeriv2 center r R)
    (ballCutoffFDeriv2_contDiff center r R).continuous
    (ballCutoffFDeriv2_hasCompactSupport hr hrR)

@[simp]
theorem ballCutoffBcf_apply
    (center : V) {r R : Real} (hr : 0 ≤ r) (hrR : r < R) (x : V) :
    ballCutoffBcf center hr hrR x = ballCutoff center r R x := rfl

@[simp]
theorem ballCutoffFDerivBcf_apply
    (center : V) {r R : Real} (hr : 0 ≤ r) (hrR : r < R) (x : V) :
    ballCutoffFDerivBcf center hr hrR x =
      ballCutoffFDeriv center r R x := rfl

@[simp]
theorem ballCutoffFDeriv2Bcf_apply
    (center : V) {r R : Real} (hr : 0 ≤ r) (hrR : r < R) (x : V) :
    ballCutoffFDeriv2Bcf center hr hrR x =
      ballCutoffFDeriv2 center r R x := rfl

theorem lapEval_ballCutoffFDeriv2
    (center : V) (r R : Real) (x : V) :
    lapEval (ballCutoffFDeriv2 center r R x) =
      ballCutoffLaplacian center r R x := by
  classical
  rw [lapEval_apply]
  simp only [ballCutoffFDeriv2, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.smulRight_apply,
    ballCutoffArgumentFDeriv_apply, ballCutoffArgumentFDeriv2_apply,
    smul_eq_mul]
  rw [Finset.sum_add_distrib]
  simp_rw [real_inner_self_eq_norm_sq,
    (stdOrthonormalBasis Real V).orthonormal.norm_eq_one, one_pow]
  rw [Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
  have hterm : ∀ i : Fin (Module.finrank Real V),
      deriv (deriv CutoffProfile.value) (ballCutoffArgument center r R x) *
          ((R ^ 2 - r ^ 2)⁻¹ *
            (2 * inner Real (x - center) ((stdOrthonormalBasis Real V) i))) *
        ((R ^ 2 - r ^ 2)⁻¹ *
          (2 * inner Real (x - center) ((stdOrthonormalBasis Real V) i))) =
      (deriv (deriv CutoffProfile.value) (ballCutoffArgument center r R x) *
        (2 / (R ^ 2 - r ^ 2)) ^ 2) *
          inner Real (x - center) ((stdOrthonormalBasis Real V) i) ^ 2 := by
    intro i
    rw [div_eq_mul_inv]
    ring
  simp_rw [hterm]
  rw [← Finset.mul_sum]
  rw [(stdOrthonormalBasis Real V).sum_sq_inner_left]
  simp only [pow_two]
  unfold ballCutoffLaplacian
  ring

theorem coreLap_ballCutoffFDeriv2Bcf
    (center : V) {r R : Real} (hr : 0 ≤ r) (hrR : r < R) (x : V) :
    coreLap (ballCutoffFDeriv2Bcf center hr hrR) x =
      ballCutoffLaplacian center r R x := by
  change lapEval (ballCutoffFDeriv2 center r R x) = _
  exact lapEval_ballCutoffFDeriv2 center r R x

end DifferentialGeometry.Analysis.Schauder

end
