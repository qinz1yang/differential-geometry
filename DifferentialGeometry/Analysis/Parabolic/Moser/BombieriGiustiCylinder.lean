import DifferentialGeometry.Analysis.Parabolic.Moser.Cutoff

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set
open scoped ContDiff Manifold Topology

namespace DifferentialGeometry.Analysis.Parabolic.Moser

open DifferentialGeometry.Analysis.Laplacian
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Integral.DivergenceTheorem

def bombieriGiustiInvScale (k : ℕ) : ℝ :=
  1 / (k + 1 : ℝ)

@[simp]
theorem bombieriGiustiInvScale_zero :
    bombieriGiustiInvScale 0 = 1 := by
  norm_num [bombieriGiustiInvScale]

theorem bombieriGiustiInvScale_pos (k : ℕ) :
    0 < bombieriGiustiInvScale k := by
  exact div_pos one_pos (by positivity)

theorem bombieriGiustiInvScale_le_one (k : ℕ) :
    bombieriGiustiInvScale k ≤ 1 := by
  unfold bombieriGiustiInvScale
  apply (div_le_one (by positivity)).2
  norm_num

theorem bombieriGiustiInvScale_succ_lt (k : ℕ) :
    bombieriGiustiInvScale (k + 1) < bombieriGiustiInvScale k := by
  unfold bombieriGiustiInvScale
  apply one_div_lt_one_div_of_lt
  · positivity
  · norm_num

theorem bombieriGiustiInvScale_sub_succ (k : ℕ) :
    bombieriGiustiInvScale k - bombieriGiustiInvScale (k + 1) =
      1 / ((k + 1 : ℝ) * (k + 2 : ℝ)) := by
  unfold bombieriGiustiInvScale
  field_simp
  push_cast
  ring

theorem bombieriGiustiInvScale_strictAnti :
    StrictAnti bombieriGiustiInvScale := by
  exact strictAnti_nat_of_succ_lt bombieriGiustiInvScale_succ_lt

def bombieriGiustiDescendingLevel (lower upper : ℝ) (k : ℕ) : ℝ :=
  lower + (upper - lower) * bombieriGiustiInvScale k

def bombieriGiustiIncreasingLevel (lower upper : ℝ) (k : ℕ) : ℝ :=
  upper - (upper - lower) * bombieriGiustiInvScale k

@[simp]
theorem bombieriGiustiDescendingLevel_zero (lower upper : ℝ) :
    bombieriGiustiDescendingLevel lower upper 0 = upper := by
  simp [bombieriGiustiDescendingLevel]

@[simp]
theorem bombieriGiustiIncreasingLevel_zero (lower upper : ℝ) :
    bombieriGiustiIncreasingLevel lower upper 0 = lower := by
  simp [bombieriGiustiIncreasingLevel]

theorem bombieriGiustiDescendingLevel_strictAnti
    {lower upper : ℝ} (hlowerUpper : lower < upper) :
    StrictAnti (bombieriGiustiDescendingLevel lower upper) := by
  apply strictAnti_nat_of_succ_lt
  intro k
  unfold bombieriGiustiDescendingLevel
  simpa only [add_comm] using add_lt_add_left
    (mul_lt_mul_of_pos_left (bombieriGiustiInvScale_succ_lt k)
      (sub_pos.mpr hlowerUpper)) lower

theorem bombieriGiustiIncreasingLevel_strictMono
    {lower upper : ℝ} (hlowerUpper : lower < upper) :
    StrictMono (bombieriGiustiIncreasingLevel lower upper) := by
  apply strictMono_nat_of_lt_succ
  intro k
  unfold bombieriGiustiIncreasingLevel
  exact sub_lt_sub_left
    (mul_lt_mul_of_pos_left (bombieriGiustiInvScale_succ_lt k)
      (sub_pos.mpr hlowerUpper)) upper

theorem bombieriGiustiDescendingLevel_gt
    {lower upper : ℝ} (hlowerUpper : lower < upper) (k : ℕ) :
    lower < bombieriGiustiDescendingLevel lower upper k := by
  unfold bombieriGiustiDescendingLevel
  exact lt_add_of_pos_right lower
    (mul_pos (sub_pos.mpr hlowerUpper) (bombieriGiustiInvScale_pos k))

theorem bombieriGiustiDescendingLevel_le
    {lower upper : ℝ} (hlowerUpper : lower < upper) (k : ℕ) :
    bombieriGiustiDescendingLevel lower upper k ≤ upper := by
  have hmul := mul_le_mul_of_nonneg_left (bombieriGiustiInvScale_le_one k)
    (sub_pos.mpr hlowerUpper).le
  unfold bombieriGiustiDescendingLevel
  linarith

theorem bombieriGiustiIncreasingLevel_ge
    {lower upper : ℝ} (hlowerUpper : lower < upper) (k : ℕ) :
    lower ≤ bombieriGiustiIncreasingLevel lower upper k := by
  have hmul := mul_le_mul_of_nonneg_left (bombieriGiustiInvScale_le_one k)
    (sub_pos.mpr hlowerUpper).le
  unfold bombieriGiustiIncreasingLevel
  linarith

theorem bombieriGiustiIncreasingLevel_lt
    {lower upper : ℝ} (hlowerUpper : lower < upper) (k : ℕ) :
    bombieriGiustiIncreasingLevel lower upper k < upper := by
  unfold bombieriGiustiIncreasingLevel
  exact sub_lt_self upper
    (mul_pos (sub_pos.mpr hlowerUpper) (bombieriGiustiInvScale_pos k))

theorem bombieriGiustiDescendingLevel_sub_succ
    (lower upper : ℝ) (k : ℕ) :
    bombieriGiustiDescendingLevel lower upper k -
        bombieriGiustiDescendingLevel lower upper (k + 1) =
      (upper - lower) / ((k + 1 : ℝ) * (k + 2 : ℝ)) := by
  rw [show bombieriGiustiDescendingLevel lower upper k -
      bombieriGiustiDescendingLevel lower upper (k + 1) =
        (upper - lower) *
          (bombieriGiustiInvScale k - bombieriGiustiInvScale (k + 1)) by
    unfold bombieriGiustiDescendingLevel
    ring,
    bombieriGiustiInvScale_sub_succ]
  ring

theorem bombieriGiustiIncreasingLevel_succ_sub
    (lower upper : ℝ) (k : ℕ) :
    bombieriGiustiIncreasingLevel lower upper (k + 1) -
        bombieriGiustiIncreasingLevel lower upper k =
      (upper - lower) / ((k + 1 : ℝ) * (k + 2 : ℝ)) := by
  rw [show bombieriGiustiIncreasingLevel lower upper (k + 1) -
      bombieriGiustiIncreasingLevel lower upper k =
        (upper - lower) *
          (bombieriGiustiInvScale k - bombieriGiustiInvScale (k + 1)) by
    unfold bombieriGiustiIncreasingLevel
    ring,
    bombieriGiustiInvScale_sub_succ]
  ring

theorem bombieriGiustiDescendingLevel_sub_succ_inv
    (lower upper : ℝ) (k : ℕ) :
    (bombieriGiustiDescendingLevel lower upper k -
        bombieriGiustiDescendingLevel lower upper (k + 1))⁻¹ =
      ((k + 1 : ℝ) * (k + 2 : ℝ)) / (upper - lower) := by
  rw [bombieriGiustiDescendingLevel_sub_succ]
  field_simp

theorem bombieriGiustiIncreasingLevel_succ_sub_inv
    (lower upper : ℝ) (k : ℕ) :
    (bombieriGiustiIncreasingLevel lower upper (k + 1) -
        bombieriGiustiIncreasingLevel lower upper k)⁻¹ =
      ((k + 1 : ℝ) * (k + 2 : ℝ)) / (upper - lower) := by
  rw [bombieriGiustiIncreasingLevel_succ_sub]
  field_simp

theorem two_mul_bombieriGiustiIncreasingLevel_gap_inv_le
    {lower upper : ℝ} (hlowerUpper : lower < upper) (k : ℕ) :
    2 * (bombieriGiustiIncreasingLevel lower upper (k + 1) -
        bombieriGiustiIncreasingLevel lower upper k)⁻¹ ≤
      (4 / (upper - lower)) * (k + 1 : ℝ) ^ 2 := by
  rw [bombieriGiustiIncreasingLevel_succ_sub_inv]
  have hm : 1 ≤ (k + 1 : ℝ) := by norm_num
  have hwidth : 0 ≤ (upper - lower)⁻¹ :=
    inv_nonneg.mpr (sub_pos.mpr hlowerUpper).le
  calc
    2 * (((k + 1 : ℝ) * (k + 2 : ℝ)) / (upper - lower)) =
        (2 * (k + 1 : ℝ) * (k + 2 : ℝ)) * (upper - lower)⁻¹ := by
      ring
    _ ≤ (4 * (k + 1 : ℝ) ^ 2) * (upper - lower)⁻¹ := by
      apply mul_le_mul_of_nonneg_right _ hwidth
      norm_num at hm ⊢
      nlinarith
    _ = (4 / (upper - lower)) * (k + 1 : ℝ) ^ 2 := by
      ring

theorem bombieriGiustiDescendingLevel_gap_inv_le
    {lower upper : ℝ} (hlowerUpper : lower < upper) (k : ℕ) :
    (bombieriGiustiDescendingLevel lower upper k -
        bombieriGiustiDescendingLevel lower upper (k + 1))⁻¹ ≤
      (2 / (upper - lower)) * (k + 1 : ℝ) ^ 2 := by
  rw [bombieriGiustiDescendingLevel_sub_succ_inv]
  have hm : 1 ≤ (k + 1 : ℝ) := by norm_num
  have hwidth : 0 ≤ (upper - lower)⁻¹ :=
    inv_nonneg.mpr (sub_pos.mpr hlowerUpper).le
  calc
    (((k + 1 : ℝ) * (k + 2 : ℝ)) / (upper - lower)) =
        ((k + 1 : ℝ) * (k + 2 : ℝ)) * (upper - lower)⁻¹ := by
      ring
    _ ≤ (2 * (k + 1 : ℝ) ^ 2) * (upper - lower)⁻¹ := by
      apply mul_le_mul_of_nonneg_right _ hwidth
      norm_num at hm ⊢
      nlinarith
    _ = (2 / (upper - lower)) * (k + 1 : ℝ) ^ 2 := by ring

theorem bombieriGiustiDescendingLevel_odd_gap_inv_le
    {lower upper : ℝ} (hlowerUpper : lower < upper) (k : ℕ) :
    (bombieriGiustiDescendingLevel lower upper (2 * k + 1) -
        bombieriGiustiDescendingLevel lower upper (2 * k + 2))⁻¹ ≤
      (6 / (upper - lower)) * (k + 1 : ℝ) ^ 2 := by
  rw [show 2 * k + 2 = (2 * k + 1) + 1 by omega,
    bombieriGiustiDescendingLevel_sub_succ_inv]
  have hm : 1 ≤ (k + 1 : ℝ) := by norm_num
  have hwidth : 0 ≤ (upper - lower)⁻¹ :=
    inv_nonneg.mpr (sub_pos.mpr hlowerUpper).le
  rw [div_eq_mul_inv, div_eq_mul_inv]
  calc
    ( ((2 * k + 1 : ℕ) : ℝ) + 1) *
          (((2 * k + 1 : ℕ) : ℝ) + 2) * (upper - lower)⁻¹ ≤
        (6 * (k + 1 : ℝ) ^ 2) * (upper - lower)⁻¹ := by
      apply mul_le_mul_of_nonneg_right _ hwidth
      push_cast
      nlinarith
    _ = 6 * (upper - lower)⁻¹ * (k + 1 : ℝ) ^ 2 := by ring

theorem bombieriGiustiDescendingLevel_odd_gap_inv_sq_le
    {lower upper : ℝ} (hlowerUpper : lower < upper) (k : ℕ) :
    (bombieriGiustiDescendingLevel lower upper (2 * k + 1) -
        bombieriGiustiDescendingLevel lower upper (2 * k + 2))⁻¹ ^ 2 ≤
      (36 / (upper - lower) ^ 2) * (k + 1 : ℝ) ^ 4 := by
  have hgap : 0 <
      bombieriGiustiDescendingLevel lower upper (2 * k + 1) -
        bombieriGiustiDescendingLevel lower upper (2 * k + 2) :=
    sub_pos.mpr (bombieriGiustiDescendingLevel_strictAnti hlowerUpper (by omega))
  have hpow := pow_le_pow_left₀ (inv_nonneg.mpr hgap.le)
    (bombieriGiustiDescendingLevel_odd_gap_inv_le hlowerUpper k) 2
  calc
    _ ≤ ((6 / (upper - lower)) * (k + 1 : ℝ) ^ 2) ^ 2 := hpow
    _ = (36 / (upper - lower) ^ 2) * (k + 1 : ℝ) ^ 4 := by
      rw [mul_pow, div_pow]
      ring

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Module.Finite ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

def bombieriGiustiSpatialCutoff
    {g : SmoothRiemannianMetric I M} (rho : SmoothScalar g)
    (lower upper : ℝ) (k : ℕ) : SmoothScalar g :=
  spatialCutoffBetween rho
    (bombieriGiustiDescendingLevel lower upper (2 * k + 1))
    (bombieriGiustiDescendingLevel lower upper (2 * k))

def bombieriGiustiReciprocalLocalizer
    {g : SmoothRiemannianMetric I M} (rho : SmoothScalar g)
    (lower upper : ℝ) (k : ℕ) : SmoothScalar g where
  toFun := fun x => 1 +
    (rho.toFun x - bombieriGiustiDescendingLevel lower upper (2 * k + 1)) /
      (bombieriGiustiDescendingLevel lower upper (2 * k + 1) -
        bombieriGiustiDescendingLevel lower upper (2 * k + 2))
  smooth := contMDiff_const.add
    ((rho.smooth.sub contMDiff_const).div_const
      (bombieriGiustiDescendingLevel lower upper (2 * k + 1) -
        bombieriGiustiDescendingLevel lower upper (2 * k + 2)))

theorem bombieriGiustiReciprocalLocalizer_gap_pos
    {lower upper : ℝ} (hlowerUpper : lower < upper) (k : ℕ) :
    0 < bombieriGiustiDescendingLevel lower upper (2 * k + 1) -
      bombieriGiustiDescendingLevel lower upper (2 * k + 2) := by
  exact sub_pos.mpr
    (bombieriGiustiDescendingLevel_strictAnti hlowerUpper (by omega))

theorem gradFun_bombieriGiustiReciprocalLocalizer
    [I.Boundaryless] [T2Space M]
    (g : SmoothRiemannianMetric I M) {q : SmoothRiemannianMetric I M}
    (rho : SmoothScalar q)
    (lower upper : ℝ) (k : ℕ) (x : M) :
    gradFun (I := I) g
        (bombieriGiustiReciprocalLocalizer rho lower upper k).toFun x =
      (bombieriGiustiDescendingLevel lower upper (2 * k + 1) -
          bombieriGiustiDescendingLevel lower upper (2 * k + 2))⁻¹ •
        gradFun (I := I) g rho.toFun x := by
  let affine : ℝ → ℝ := fun s => 1 +
    (s - bombieriGiustiDescendingLevel lower upper (2 * k + 1)) /
      (bombieriGiustiDescendingLevel lower upper (2 * k + 1) -
        bombieriGiustiDescendingLevel lower upper (2 * k + 2))
  have haffine : HasDerivAt affine
      (bombieriGiustiDescendingLevel lower upper (2 * k + 1) -
        bombieriGiustiDescendingLevel lower upper (2 * k + 2))⁻¹
      (rho.toFun x) := by
    have h := (hasDerivAt_const (rho.toFun x) (1 : ℝ)).add
      (((hasDerivAt_id (rho.toFun x)).sub_const
        (bombieriGiustiDescendingLevel lower upper (2 * k + 1))).div_const
          (bombieriGiustiDescendingLevel lower upper (2 * k + 1) -
            bombieriGiustiDescendingLevel lower upper (2 * k + 2)))
    simpa only [affine, zero_add, one_div] using h
  have hgradient := gradientFun_comp (I := I) g haffine.differentiableAt
    (rho.smooth.mdifferentiable (by simp) x)
  simpa only [affine, bombieriGiustiReciprocalLocalizer, haffine.deriv,
    gradientFun] using hgradient

theorem bombieriGiustiReciprocalLocalizer_inner_grad_self_le
    [I.Boundaryless] [T2Space M]
    (g : SmoothRiemannianMetric I M) {q : SmoothRiemannianMetric I M}
    (rho : SmoothScalar q) {G lower upper : ℝ}
    (hrho : ∀ x : M,
      g.inner x
          (gradFun (I := I) g rho.toFun x)
          (gradFun (I := I) g rho.toFun x) ≤ G)
    (k : ℕ) (x : M) :
    g.inner x
        (gradFun (I := I) g
          (bombieriGiustiReciprocalLocalizer rho lower upper k).toFun x)
        (gradFun (I := I) g
          (bombieriGiustiReciprocalLocalizer rho lower upper k).toFun x) ≤
      (bombieriGiustiDescendingLevel lower upper (2 * k + 1) -
          bombieriGiustiDescendingLevel lower upper (2 * k + 2))⁻¹ ^ 2 * G := by
  rw [gradFun_bombieriGiustiReciprocalLocalizer,
    metric_inner_smul_self]
  exact mul_le_mul_of_nonneg_left (hrho x) (sq_nonneg _)

theorem bombieriGiustiReciprocalLocalizer_gradientSqSup_le
    [I.Boundaryless] [T2Space M] [CompactSpace M]
    (g : SmoothRiemannianMetric I M) (rho : SmoothScalar g)
    (lower upper : ℝ) (k : ℕ) :
    (bombieriGiustiReciprocalLocalizer rho lower upper k).gradientSqSup ≤
      (bombieriGiustiDescendingLevel lower upper (2 * k + 1) -
          bombieriGiustiDescendingLevel lower upper (2 * k + 2))⁻¹ ^ 2 *
        rho.gradientSqSup := by
  refine SmoothScalar.gradientSqSup_le _
    (mul_nonneg (sq_nonneg _) rho.gradientSqSup_nonneg) ?_
  intro x
  rw [gradFun_bombieriGiustiReciprocalLocalizer,
    metric_inner_smul_self]
  exact mul_le_mul_of_nonneg_left
    (rho.inner_grad_self_le_gradientSqSup x) (sq_nonneg _)

theorem spatialMoserCutoffGradientConstant_reciprocalLocalizer_le
    [I.Boundaryless] [T2Space M] [CompactSpace M]
    (g : SmoothRiemannianMetric I M) (rho : SmoothScalar g)
    (lower upper : ℝ) (k : ℕ) :
    spatialMoserCutoffGradientConstant (I := I) g
        (bombieriGiustiReciprocalLocalizer rho lower upper k) ≤
      (bombieriGiustiDescendingLevel lower upper (2 * k + 1) -
          bombieriGiustiDescendingLevel lower upper (2 * k + 2))⁻¹ ^ 2 *
        spatialMoserCutoffGradientConstant (I := I) g rho := by
  unfold spatialMoserCutoffGradientConstant
  calc
    16 * CutoffProfile.derivBound ^ 2 *
          (bombieriGiustiReciprocalLocalizer rho lower upper k).gradientSqSup ≤
        16 * CutoffProfile.derivBound ^ 2 *
          ((bombieriGiustiDescendingLevel lower upper (2 * k + 1) -
              bombieriGiustiDescendingLevel lower upper (2 * k + 2))⁻¹ ^ 2 *
            rho.gradientSqSup) :=
      mul_le_mul_of_nonneg_left
        (bombieriGiustiReciprocalLocalizer_gradientSqSup_le g rho lower upper k)
        (mul_nonneg (by norm_num) (sq_nonneg _))
    _ = (bombieriGiustiDescendingLevel lower upper (2 * k + 1) -
            bombieriGiustiDescendingLevel lower upper (2 * k + 2))⁻¹ ^ 2 *
          (16 * CutoffProfile.derivBound ^ 2 * rho.gradientSqSup) := by
      ring

omit [Module.Finite ℝ E] in
theorem one_lt_bombieriGiustiReciprocalLocalizer_of_ne_zero
    {g : SmoothRiemannianMetric I M} (rho : SmoothScalar g)
    {lower upper : ℝ} (hlowerUpper : lower < upper) (k : ℕ) (x : M)
    (hx : (bombieriGiustiSpatialCutoff rho lower upper k).toFun x ≠ 0) :
    1 < (bombieriGiustiReciprocalLocalizer rho lower upper k).toFun x := by
  have hlevel := bombieriGiustiDescendingLevel_strictAnti hlowerUpper
  have hrho :
      bombieriGiustiDescendingLevel lower upper (2 * k + 1) < rho.toFun x := by
    by_contra h
    apply hx
    apply spatialCutoffBetween_eq_zero_of_le_inner
      (hlevel (by omega)) (le_of_not_gt h)
  change 1 < 1 +
    (rho.toFun x - bombieriGiustiDescendingLevel lower upper (2 * k + 1)) /
      (bombieriGiustiDescendingLevel lower upper (2 * k + 1) -
        bombieriGiustiDescendingLevel lower upper (2 * k + 2))
  exact lt_add_of_pos_right 1 (div_pos (sub_pos.mpr hrho)
    (bombieriGiustiReciprocalLocalizer_gap_pos hlowerUpper k))

omit [Module.Finite ℝ E] in
theorem bombieriGiustiSpatialCutoff_le_reciprocalLocalizer
    {g : SmoothRiemannianMetric I M} (rho : SmoothScalar g)
    {lower upper : ℝ} (hlowerUpper : lower < upper) (k : ℕ) (x : M) :
    (bombieriGiustiSpatialCutoff rho lower upper k).toFun x ^ 2 ≤
      (spatialMoserCutoff
        (bombieriGiustiReciprocalLocalizer rho lower upper k) 0).toFun x ^ 2 := by
  by_cases hx : (bombieriGiustiSpatialCutoff rho lower upper k).toFun x = 0
  · simpa [hx] using sq_nonneg
      ((spatialMoserCutoff
        (bombieriGiustiReciprocalLocalizer rho lower upper k) 0).toFun x)
  · have hlocalizer := one_lt_bombieriGiustiReciprocalLocalizer_of_ne_zero
      rho hlowerUpper k x hx
    have hone : (spatialMoserCutoff
        (bombieriGiustiReciprocalLocalizer rho lower upper k) 0).toFun x = 1 := by
      apply spatialMoserCutoff_eq_one_of_level_le
      norm_num [moserCutoffLevel]
      linarith
    rw [hone, one_pow]
    have hmem := spatialCutoffBetween_mem_Icc rho
      (bombieriGiustiDescendingLevel lower upper (2 * k + 1))
      (bombieriGiustiDescendingLevel lower upper (2 * k)) x
    simpa only [bombieriGiustiSpatialCutoff, one_pow] using
      (sq_le_sq₀ hmem.1 (by norm_num : (0 : ℝ) ≤ 1)).2 hmem.2

omit [Module.Finite ℝ E] in
theorem reciprocalLocalizer_le_bombieriGiustiSpatialCutoff_succ
    {g : SmoothRiemannianMetric I M} (rho : SmoothScalar g)
    {lower upper : ℝ} (hlowerUpper : lower < upper) (k : ℕ) (x : M) :
    (spatialMoserCutoff
        (bombieriGiustiReciprocalLocalizer rho lower upper k) 0).toFun x ^ 2 ≤
      (bombieriGiustiSpatialCutoff rho lower upper (k + 1)).toFun x ^ 2 := by
  let localizer := bombieriGiustiReciprocalLocalizer rho lower upper k
  change (spatialMoserCutoff localizer 0).toFun x ^ 2 ≤
    (bombieriGiustiSpatialCutoff rho lower upper (k + 1)).toFun x ^ 2
  by_cases hx : localizer.toFun x ≤ 0
  · have hzero : (spatialMoserCutoff localizer 0).toFun x = 0 := by
      apply spatialMoserCutoff_eq_zero_of_le_level
      simpa [moserCutoffLevel] using hx
    calc
      (spatialMoserCutoff localizer 0).toFun x ^ 2 = 0 := by
        rw [hzero]
        norm_num
      _ ≤ (bombieriGiustiSpatialCutoff rho lower upper (k + 1)).toFun x ^ 2 :=
        sq_nonneg _
  · have hlocalizer : 0 < localizer.toFun x := lt_of_not_ge hx
    have hgap := bombieriGiustiReciprocalLocalizer_gap_pos hlowerUpper k
    have hquotient :
        (-1 : ℝ) <
          (rho.toFun x - bombieriGiustiDescendingLevel lower upper (2 * k + 1)) /
            (bombieriGiustiDescendingLevel lower upper (2 * k + 1) -
              bombieriGiustiDescendingLevel lower upper (2 * k + 2)) := by
      dsimp only [localizer, bombieriGiustiReciprocalLocalizer] at hlocalizer
      linarith
    have hmul := (lt_div_iff₀ hgap).mp hquotient
    have hrho :
        bombieriGiustiDescendingLevel lower upper (2 * k + 2) < rho.toFun x := by
      linarith
    have hone :
        (bombieriGiustiSpatialCutoff rho lower upper (k + 1)).toFun x = 1 := by
      apply spatialCutoffBetween_eq_one_of_outer_le
      · exact bombieriGiustiDescendingLevel_strictAnti hlowerUpper (by omega)
      · convert hrho.le using 1
    rw [hone, one_pow]
    have hmem := spatialMoserCutoff_mem_Icc localizer 0 x
    simpa only [localizer, one_pow] using
      (sq_le_sq₀ hmem.1 (by norm_num : (0 : ℝ) ≤ 1)).2 hmem.2

omit [Module.Finite ℝ E] in
theorem bombieriGiustiSpatialCutoff_mono
    {g : SmoothRiemannianMetric I M} (rho : SmoothScalar g)
    {lower upper : ℝ} (hlowerUpper : lower < upper) (k : ℕ) (x : M) :
    (bombieriGiustiSpatialCutoff rho lower upper k).toFun x ^ 2 ≤
      (bombieriGiustiSpatialCutoff rho lower upper (k + 1)).toFun x ^ 2 := by
  let level := bombieriGiustiDescendingLevel lower upper
  have hlevel : StrictAnti level :=
    bombieriGiustiDescendingLevel_strictAnti hlowerUpper
  apply spatialCutoffBetween_sq_le_of_nested_levels rho
  · exact hlevel (by omega)
  · exact (hlevel (by omega)).le
  · exact hlevel (by omega)

omit [Module.Finite ℝ E] in
theorem bombieriGiustiSpatialCutoff_le_outer
    {g : SmoothRiemannianMetric I M} (rho : SmoothScalar g)
    {outerLower outerUpper lower upper : ℝ}
    (houter : outerLower < outerUpper) (houterLower : outerUpper ≤ lower)
    (hlowerUpper : lower < upper) (k : ℕ) (x : M) :
    (bombieriGiustiSpatialCutoff rho lower upper k).toFun x ^ 2 ≤
      (spatialCutoffBetween rho outerLower outerUpper).toFun x ^ 2 := by
  apply spatialCutoffBetween_sq_le_of_nested_levels rho houter
  · exact houterLower.trans
      (bombieriGiustiDescendingLevel_gt hlowerUpper (2 * k + 1)).le
  · exact (bombieriGiustiDescendingLevel_strictAnti hlowerUpper (by omega))

omit [Module.Finite ℝ E] in
theorem bombieriGiustiSpatialCutoff_le_forward_inner
    {g : SmoothRiemannianMetric I M} (rho : SmoothScalar g)
    {lower upper : ℝ} (hlowerUpper : lower < upper) (k m : ℕ) (x : M) :
    (bombieriGiustiSpatialCutoff rho lower upper k).toFun x ^ 2 ≤
      (spatialCutoffBetween rho
        (moserCutoffLevelBetween
          (bombieriGiustiDescendingLevel lower upper (2 * k + 2))
          (bombieriGiustiDescendingLevel lower upper (2 * k + 1)) (2 * m))
        (moserCutoffLevelBetween
          (bombieriGiustiDescendingLevel lower upper (2 * k + 2))
          (bombieriGiustiDescendingLevel lower upper (2 * k + 1))
          (2 * m + 1))).toFun x ^ 2 := by
  let level := bombieriGiustiDescendingLevel lower upper
  have hlevel : StrictAnti level :=
    bombieriGiustiDescendingLevel_strictAnti hlowerUpper
  have hlocal : level (2 * k + 2) < level (2 * k + 1) := hlevel (by omega)
  apply spatialCutoffBetween_sq_le_of_nested_levels rho
  · exact moserCutoffLevelBetween_strictMono hlocal (by omega)
  · exact (moserCutoffLevelBetween_lt hlocal (2 * m + 1)).le
  · exact hlevel (by omega)

omit [Module.Finite ℝ E] in
theorem forward_initial_spatialCutoffBetween_le_bombieriGiustiSpatialCutoff_succ
    {g : SmoothRiemannianMetric I M} (rho : SmoothScalar g)
    {lower upper : ℝ} (hlowerUpper : lower < upper) (k : ℕ) (x : M) :
    (spatialCutoffBetween rho
      (moserCutoffLevelBetween
        (bombieriGiustiDescendingLevel lower upper (2 * k + 2))
        (bombieriGiustiDescendingLevel lower upper (2 * k + 1)) 0)
      (moserCutoffLevelBetween
        (bombieriGiustiDescendingLevel lower upper (2 * k + 2))
        (bombieriGiustiDescendingLevel lower upper (2 * k + 1)) 1)).toFun x ^ 2 ≤
      (bombieriGiustiSpatialCutoff rho lower upper (k + 1)).toFun x ^ 2 := by
  let level := bombieriGiustiDescendingLevel lower upper
  have hlevel : StrictAnti level :=
    bombieriGiustiDescendingLevel_strictAnti hlowerUpper
  have hlocal : level (2 * k + 2) < level (2 * k + 1) := hlevel (by omega)
  apply spatialCutoffBetween_sq_le_of_nested_levels rho
  · exact hlevel (by omega)
  · simpa only [moserCutoffLevelBetween_zero] using le_rfl
  · exact moserCutoffLevelBetween_strictMono hlocal (by norm_num)

end DifferentialGeometry.Analysis.Parabolic.Moser

end
