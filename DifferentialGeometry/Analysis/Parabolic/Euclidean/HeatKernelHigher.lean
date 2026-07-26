import DifferentialGeometry.Analysis.Parabolic.Euclidean.HeatKernelPDE

/-!
# Higher derivatives of the Euclidean heat kernel

This file supplies the two derivative estimates needed by the heat-specific
parabolic Hörmander argument.  It constructs the third spatial derivative of
the normalized Gaussian, realizes it as the actual Fréchet derivative of
`heatD2`, and proves its scale-sharp spatial `L¹` bound.  It also records the
direct positive-time derivative of `heatD2`; this is the narrower alternative
to building a complete fourth spatial derivative API.
-/

noncomputable section

open MeasureTheory Real
open scoped RealInnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace Euclidean

section ThirdDerivative

variable {V : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]
  [Nontrivial V]

/-- Third directional derivative of the normalized time-one heat kernel. -/
def baseD3 (u v w x : V) : ℝ :=
  (-(8 : ℝ)⁻¹ * ⟪x, u⟫ * ⟪x, v⟫ * ⟪x, w⟫ +
      (4 : ℝ)⁻¹ *
        (⟪u, v⟫ * ⟪x, w⟫ + ⟪u, w⟫ * ⟪x, v⟫ +
          ⟪v, w⟫ * ⟪x, u⟫)) *
    baseHeat x

/-- Fréchet derivative map of `baseD2 v w`. -/
def baseD3Map (v w x : V) : V →L[ℝ] ℝ :=
  (-(8 : ℝ)⁻¹ * ⟪x, v⟫ * ⟪x, w⟫ * baseHeat x) • innerSL ℝ x +
    ((4 : ℝ)⁻¹ * ⟪x, w⟫ * baseHeat x) • innerSL ℝ v +
      ((4 : ℝ)⁻¹ * ⟪x, v⟫ * baseHeat x) • innerSL ℝ w +
        ((4 : ℝ)⁻¹ * ⟪v, w⟫ * baseHeat x) • innerSL ℝ x

omit [MeasurableSpace V] [BorelSpace V] [Nontrivial V] in
@[simp] theorem baseD3Map_apply (v w x u : V) :
    baseD3Map v w x u = baseD3 u v w x := by
  simp only [baseD3Map, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply, innerSL_apply_apply, smul_eq_mul]
  unfold baseD3
  rw [real_inner_comm v u, real_inner_comm w u]
  ring

omit [MeasurableSpace V] [BorelSpace V] [Nontrivial V] in
/-- The explicit third Gaussian kernel is the Fréchet derivative of the
second one. -/
theorem baseD2_hasFDeriv (v w x : V) :
    HasFDerivAt (baseD2 v w) (baseD3Map v w x) x := by
  have hv : HasFDerivAt (fun y : V => ⟪y, v⟫) (innerSL ℝ v) x := by
    simpa [real_inner_comm] using (innerSL ℝ v).hasFDerivAt
  have hw : HasFDerivAt (fun y : V => ⟪y, w⟫) (innerSL ℝ w) x := by
    simpa [real_inner_comm] using (innerSL ℝ w).hasFDerivAt
  have hp := ((hv.mul hw).const_mul (4 : ℝ)⁻¹).sub_const
    ((2 : ℝ)⁻¹ * ⟪v, w⟫)
  have h := hp.mul (baseHeat_hasFDeriv x)
  convert h using 1
  · funext y
    simp only [baseD2, Pi.mul_apply]
    ring
  · ext u
    simp only [baseD1Map, baseD3Map, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.smul_apply,
      innerSL_apply_apply, smul_eq_mul, Pi.mul_apply]
    ring

/-- Radial `L¹` majorant for the third derivative kernel. -/
def baseD3Maj (x : V) : ℝ :=
  ((8 : ℝ)⁻¹ * ‖x‖ ^ 3 + (3 / 4 : ℝ) * ‖x‖) * baseHeat x

omit [MeasurableSpace V] [BorelSpace V] [Nontrivial V] in
theorem baseD3Maj_nonneg (x : V) : 0 ≤ baseD3Maj x := by
  unfold baseD3Maj
  exact mul_nonneg
    (add_nonneg
      (mul_nonneg (by positivity) (pow_nonneg (norm_nonneg x) _))
      (mul_nonneg (by positivity) (norm_nonneg x)))
    (baseHeat_nonneg x)

omit [MeasurableSpace V] [BorelSpace V] [Nontrivial V] in
/-- The third derivative is bounded by its radial Gaussian majorant. -/
theorem baseD3_bound (u v w x : V) :
    ‖baseD3 u v w x‖ ≤ ‖u‖ * ‖v‖ * ‖w‖ * baseD3Maj x := by
  let A : ℝ := -(8 : ℝ)⁻¹ * ⟪x, u⟫ * ⟪x, v⟫ * ⟪x, w⟫
  let B : ℝ := (4 : ℝ)⁻¹ *
    (⟪u, v⟫ * ⟪x, w⟫ + ⟪u, w⟫ * ⟪x, v⟫ +
      ⟪v, w⟫ * ⟪x, u⟫)
  have hA : |A| ≤
      (8 : ℝ)⁻¹ * (‖x‖ * ‖u‖) * (‖x‖ * ‖v‖) * (‖x‖ * ‖w‖) := by
    dsimp [A]
    rw [abs_mul, abs_mul, abs_mul, abs_neg,
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ (8 : ℝ)⁻¹)]
    gcongr
    · exact abs_real_inner_le_norm x u
    · exact abs_real_inner_le_norm x v
    · exact abs_real_inner_le_norm x w
  have huv : |⟪u, v⟫ * ⟪x, w⟫| ≤
      (‖u‖ * ‖v‖) * (‖x‖ * ‖w‖) := by
    rw [abs_mul]
    exact mul_le_mul (abs_real_inner_le_norm u v)
      (abs_real_inner_le_norm x w) (abs_nonneg _)
      (mul_nonneg (norm_nonneg u) (norm_nonneg v))
  have huw : |⟪u, w⟫ * ⟪x, v⟫| ≤
      (‖u‖ * ‖w‖) * (‖x‖ * ‖v‖) := by
    rw [abs_mul]
    exact mul_le_mul (abs_real_inner_le_norm u w)
      (abs_real_inner_le_norm x v) (abs_nonneg _)
      (mul_nonneg (norm_nonneg u) (norm_nonneg w))
  have hvw : |⟪v, w⟫ * ⟪x, u⟫| ≤
      (‖v‖ * ‖w‖) * (‖x‖ * ‖u‖) := by
    rw [abs_mul]
    exact mul_le_mul (abs_real_inner_le_norm v w)
      (abs_real_inner_le_norm x u) (abs_nonneg _)
      (mul_nonneg (norm_nonneg v) (norm_nonneg w))
  have hB : |B| ≤ (3 / 4 : ℝ) * ‖x‖ * (‖u‖ * ‖v‖ * ‖w‖) := by
    dsimp [B]
    rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (4 : ℝ)⁻¹)]
    calc
      (4 : ℝ)⁻¹ *
          |⟪u, v⟫ * ⟪x, w⟫ + ⟪u, w⟫ * ⟪x, v⟫ +
            ⟪v, w⟫ * ⟪x, u⟫| ≤
          (4 : ℝ)⁻¹ *
            (|⟪u, v⟫ * ⟪x, w⟫| + |⟪u, w⟫ * ⟪x, v⟫| +
              |⟪v, w⟫ * ⟪x, u⟫|) := by
        gcongr
        exact (abs_add_le _ _).trans
          (add_le_add (abs_add_le _ _) (le_refl _))
      _ ≤ (4 : ℝ)⁻¹ *
            ((‖u‖ * ‖v‖) * (‖x‖ * ‖w‖) +
              (‖u‖ * ‖w‖) * (‖x‖ * ‖v‖) +
                (‖v‖ * ‖w‖) * (‖x‖ * ‖u‖)) := by
        gcongr
      _ = (3 / 4 : ℝ) * ‖x‖ * (‖u‖ * ‖v‖ * ‖w‖) := by ring
  unfold baseD3 baseD3Maj
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (baseHeat_nonneg x)]
  calc
    |A + B| * baseHeat x ≤ (|A| + |B|) * baseHeat x := by
      exact mul_le_mul_of_nonneg_right (abs_add_le A B) (baseHeat_nonneg x)
    _ ≤ ((8 : ℝ)⁻¹ * (‖x‖ * ‖u‖) * (‖x‖ * ‖v‖) *
          (‖x‖ * ‖w‖) +
          (3 / 4 : ℝ) * ‖x‖ * (‖u‖ * ‖v‖ * ‖w‖)) *
          baseHeat x := by
      exact mul_le_mul_of_nonneg_right (add_le_add hA hB) (baseHeat_nonneg x)
    _ = ‖u‖ * ‖v‖ * ‖w‖ *
        (((8 : ℝ)⁻¹ * ‖x‖ ^ 3 + (3 / 4 : ℝ) * ‖x‖) *
          baseHeat x) := by ring

/-- The radial third-derivative majorant is integrable. -/
theorem baseD3Maj_int : Integrable (baseD3Maj : V → ℝ) := by
  have h3 := (gaussMoment_int (V := V) 3
    (by positivity : (0 : ℝ) < (4 : ℝ)⁻¹)).const_mul
      ((8 : ℝ)⁻¹ * (baseHeatMass V)⁻¹)
  have h1 := (gaussMoment_int (V := V) 1
    (by positivity : (0 : ℝ) < (4 : ℝ)⁻¹)).const_mul
      ((3 / 4 : ℝ) * (baseHeatMass V)⁻¹)
  have heq : baseD3Maj = fun x : V =>
      ((8 : ℝ)⁻¹ * (baseHeatMass V)⁻¹) *
          (‖x‖ ^ 3 * Real.exp (-(4 : ℝ)⁻¹ * ‖x‖ ^ 2)) +
        ((3 / 4 : ℝ) * (baseHeatMass V)⁻¹) *
          (‖x‖ ^ 1 * Real.exp (-(4 : ℝ)⁻¹ * ‖x‖ ^ 2)) := by
    funext x
    unfold baseD3Maj baseHeat
    ring
  rw [heq]
  exact h3.add h1

/-- Dimension-dependent third-derivative `L¹` constant. -/
def heatC3 (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] : ℝ :=
  ∫ x : V, baseD3Maj x

omit [Nontrivial V] in
theorem heatC3_nonneg : 0 ≤ heatC3 V :=
  integral_nonneg baseD3Maj_nonneg

/-- Third-derivative majorant at time `t`. -/
def heatD3Maj (t : ℝ) (x : V) : ℝ :=
  ((heatScale t) ^ Module.finrank ℝ V)⁻¹ * (heatScale t)⁻¹ *
      (heatScale t)⁻¹ * (heatScale t)⁻¹ *
    baseD3Maj ((heatScale t)⁻¹ • x)

/-- Third spatial derivative kernel of the heat kernel. -/
def heatD3 (t : ℝ) (u v w x : V) : ℝ :=
  ((heatScale t) ^ Module.finrank ℝ V)⁻¹ * (heatScale t)⁻¹ *
      (heatScale t)⁻¹ * (heatScale t)⁻¹ *
    baseD3 u v w ((heatScale t)⁻¹ • x)

/-- Fréchet derivative map of `heatD2 t v w`. -/
def heatD3Map (t : ℝ) (v w x : V) : V →L[ℝ] ℝ :=
  (((heatScale t) ^ Module.finrank ℝ V)⁻¹ * (heatScale t)⁻¹ *
      (heatScale t)⁻¹ * (heatScale t)⁻¹) •
    baseD3Map v w ((heatScale t)⁻¹ • x)

omit [MeasurableSpace V] [BorelSpace V] [Nontrivial V] in
@[simp] theorem heatD3Map_apply (t : ℝ) (v w x u : V) :
    heatD3Map t v w x u = heatD3 t u v w x := by
  simp [heatD3Map, heatD3]

omit [MeasurableSpace V] [BorelSpace V] [Nontrivial V] in
/-- At positive time, `heatD3` is the actual Fréchet derivative of
`heatD2`. -/
theorem heatD2_hasFDeriv {t : ℝ} (_ht : 0 < t) (v w x : V) :
    HasFDerivAt (heatD2 t v w) (heatD3Map t v w x) x := by
  let S : V →L[ℝ] V := (heatScale t)⁻¹ • ContinuousLinearMap.id ℝ V
  have hS : HasFDerivAt (fun y : V => (heatScale t)⁻¹ • y) S x := by
    simpa [S] using S.hasFDerivAt
  have h := ((baseD2_hasFDeriv v w ((heatScale t)⁻¹ • x)).comp x hS).const_mul
    (((heatScale t) ^ Module.finrank ℝ V)⁻¹ * (heatScale t)⁻¹ *
      (heatScale t)⁻¹)
  convert h using 1
  ext u
  simp [heatD3Map, S, baseD3Map]
  ring

omit [MeasurableSpace V] [BorelSpace V] [Nontrivial V] in
theorem heatD3Maj_nonneg {t : ℝ} (ht : 0 < t) (x : V) :
    0 ≤ heatD3Maj t x := by
  unfold heatD3Maj
  exact mul_nonneg
    (mul_nonneg
      (mul_nonneg
        (mul_nonneg
          (inv_nonneg.mpr (pow_nonneg (heatScale_pos ht).le _))
          (inv_nonneg.mpr (heatScale_pos ht).le))
        (inv_nonneg.mpr (heatScale_pos ht).le))
      (inv_nonneg.mpr (heatScale_pos ht).le))
    (baseD3Maj_nonneg _)

omit [MeasurableSpace V] [BorelSpace V] [Nontrivial V] in
/-- Pointwise third-derivative kernel bound. -/
theorem heatD3_bound {t : ℝ} (ht : 0 < t) (u v w x : V) :
    ‖heatD3 t u v w x‖ ≤ ‖u‖ * ‖v‖ * ‖w‖ * heatD3Maj t x := by
  unfold heatD3 heatD3Maj
  rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_mul, abs_mul]
  simp only [abs_inv, abs_pow, abs_of_nonneg (heatScale_pos ht).le]
  have hfront : 0 ≤
      ((heatScale t) ^ Module.finrank ℝ V)⁻¹ * (heatScale t)⁻¹ *
        (heatScale t)⁻¹ * (heatScale t)⁻¹ := by
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg
          (inv_nonneg.mpr (pow_nonneg (heatScale_pos ht).le _))
          (inv_nonneg.mpr (heatScale_pos ht).le))
        (inv_nonneg.mpr (heatScale_pos ht).le))
      (inv_nonneg.mpr (heatScale_pos ht).le)
  calc
    ((heatScale t) ^ Module.finrank ℝ V)⁻¹ * (heatScale t)⁻¹ *
          (heatScale t)⁻¹ * (heatScale t)⁻¹ *
        ‖baseD3 u v w ((heatScale t)⁻¹ • x)‖ ≤
      ((heatScale t) ^ Module.finrank ℝ V)⁻¹ * (heatScale t)⁻¹ *
          (heatScale t)⁻¹ * (heatScale t)⁻¹ *
        (‖u‖ * ‖v‖ * ‖w‖ * baseD3Maj ((heatScale t)⁻¹ • x)) := by
      exact mul_le_mul_of_nonneg_left (baseD3_bound u v w _) hfront
    _ = ‖u‖ * ‖v‖ * ‖w‖ *
        (((heatScale t) ^ Module.finrank ℝ V)⁻¹ * (heatScale t)⁻¹ *
          (heatScale t)⁻¹ * (heatScale t)⁻¹ *
            baseD3Maj ((heatScale t)⁻¹ • x)) := by ring

/-- Integrability of the scaled third-derivative majorant. -/
theorem heatD3Maj_int {t : ℝ} (ht : 0 < t) :
    Integrable (heatD3Maj t : V → ℝ) := by
  unfold heatD3Maj
  exact (baseD3Maj_int (V := V)).comp_smul
    (inv_ne_zero (heatScale_pos ht).ne') |>.const_mul _

omit [Nontrivial V] in
/-- Exact spatial integral scaling of the third-derivative majorant. -/
theorem integral_heatD3Maj {t : ℝ} (ht : 0 < t) :
    ∫ x : V, heatD3Maj t x =
      t⁻¹ * (heatScale t)⁻¹ * heatC3 V := by
  have hr : 0 < heatScale t := heatScale_pos ht
  have hsqrt : heatScale t ^ 2 = t := by
    simpa [heatScale] using Real.sq_sqrt ht.le
  have hscale : (heatScale t)⁻¹ * (heatScale t)⁻¹ = t⁻¹ := by
    field_simp [hr.ne', ht.ne']
    nlinarith [hsqrt]
  unfold heatD3Maj heatC3
  rw [integral_const_mul,
    Measure.integral_comp_inv_smul_of_nonneg (volume : Measure V) baseD3Maj hr.le]
  simp only [smul_eq_mul]
  calc
    (heatScale t ^ Module.finrank ℝ V)⁻¹ * (heatScale t)⁻¹ *
          (heatScale t)⁻¹ * (heatScale t)⁻¹ *
          (heatScale t ^ Module.finrank ℝ V * ∫ x : V, baseD3Maj x) =
        ((heatScale t)⁻¹ * (heatScale t)⁻¹) *
          (heatScale t)⁻¹ * ∫ x : V, baseD3Maj x := by
      field_simp [hr.ne']
    _ = t⁻¹ * (heatScale t)⁻¹ * ∫ x : V, baseD3Maj x := by rw [hscale]

/-- `L¹` norm of the third derivative kernel, with `t^(-3/2)` scaling. -/
theorem integral_norm_D3 {t : ℝ} (ht : 0 < t) (u v w : V) :
    (∫ x : V, ‖heatD3 t u v w x‖) ≤
      ‖u‖ * ‖v‖ * ‖w‖ * t⁻¹ * (heatScale t)⁻¹ * heatC3 V := by
  have hker : Integrable (fun x : V => ‖heatD3 t u v w x‖) := by
    refine ((heatD3Maj_int (V := V) ht).const_mul (‖u‖ * ‖v‖ * ‖w‖)).mono' ?_ ?_
    · apply Continuous.aestronglyMeasurable
      unfold heatD3 baseD3 baseHeat baseHeatMass heatScale
      fun_prop
    · filter_upwards with x
      simpa [mul_assoc] using heatD3_bound ht u v w x
  calc
    (∫ x : V, ‖heatD3 t u v w x‖) ≤
        ∫ x : V, (‖u‖ * ‖v‖ * ‖w‖) * heatD3Maj t x := by
      exact integral_mono hker
        ((heatD3Maj_int (V := V) ht).const_mul (‖u‖ * ‖v‖ * ‖w‖))
        (fun x => by simpa [mul_assoc] using heatD3_bound ht u v w x)
    _ = (‖u‖ * ‖v‖ * ‖w‖) *
        (t⁻¹ * (heatScale t)⁻¹ * heatC3 V) := by
      rw [integral_const_mul, integral_heatD3Maj ht]
    _ = ‖u‖ * ‖v‖ * ‖w‖ * t⁻¹ * (heatScale t)⁻¹ * heatC3 V := by ring

end ThirdDerivative

section SecondTimeDerivative

variable {V : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]
  [Nontrivial V]

/-- Time derivative profile of the time-one Hessian after parabolic
rescaling. -/
def baseD2Dt (v w x : V) : ℝ :=
  -(((Module.finrank ℝ V : ℝ) + 2) / 2) * baseD2 v w x -
    (2 : ℝ)⁻¹ * baseD3 x v w x

/-- Radial majorant for the time derivative profile of the Hessian. -/
def baseD2DtMaj (x : V) : ℝ :=
  (((Module.finrank ℝ V : ℝ) + 2) / 2) * baseD2Maj x +
    (2 : ℝ)⁻¹ * ‖x‖ * baseD3Maj x

omit [MeasurableSpace V] [BorelSpace V] [Nontrivial V] in
theorem baseD2DtMaj_nonneg (x : V) : 0 ≤ baseD2DtMaj x := by
  unfold baseD2DtMaj
  exact add_nonneg
    (mul_nonneg (by positivity) (baseD2Maj_nonneg x))
    (mul_nonneg
      (mul_nonneg (by positivity) (norm_nonneg x))
      (baseD3Maj_nonneg x))

omit [MeasurableSpace V] [BorelSpace V] [Nontrivial V] in
/-- The rescaled Hessian time profile is bounded by its radial majorant. -/
theorem baseD2Dt_bound (v w x : V) :
    ‖baseD2Dt v w x‖ ≤ ‖v‖ * ‖w‖ * baseD2DtMaj x := by
  let c : ℝ := ((Module.finrank ℝ V : ℝ) + 2) / 2
  have hc : 0 ≤ c := by dsimp [c]; positivity
  unfold baseD2Dt baseD2DtMaj
  rw [Real.norm_eq_abs]
  calc
    |-c * baseD2 v w x - (2 : ℝ)⁻¹ * baseD3 x v w x| ≤
        |-c * baseD2 v w x| + |(2 : ℝ)⁻¹ * baseD3 x v w x| :=
      abs_sub _ _
    _ = c * ‖baseD2 v w x‖ + (2 : ℝ)⁻¹ * ‖baseD3 x v w x‖ := by
      rw [abs_mul, abs_mul, abs_neg, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_nonneg hc, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (2 : ℝ)⁻¹)]
    _ ≤ c * (‖v‖ * ‖w‖ * baseD2Maj x) +
        (2 : ℝ)⁻¹ * (‖x‖ * ‖v‖ * ‖w‖ * baseD3Maj x) := by
      exact add_le_add
        (mul_le_mul_of_nonneg_left (baseD2_bound v w x) hc)
        (mul_le_mul_of_nonneg_left (baseD3_bound x v w x) (by positivity))
    _ = ‖v‖ * ‖w‖ *
        (c * baseD2Maj x + (2 : ℝ)⁻¹ * ‖x‖ * baseD3Maj x) := by ring

/-- Integrability of the extra radial moment in `baseD2DtMaj`. -/
private theorem baseD3First_int :
    Integrable (fun x : V => ‖x‖ * baseD3Maj x) := by
  have h4 := (gaussMoment_int (V := V) 4
    (by positivity : (0 : ℝ) < (4 : ℝ)⁻¹)).const_mul
      ((8 : ℝ)⁻¹ * (baseHeatMass V)⁻¹)
  have h2 := (gaussMoment_int (V := V) 2
    (by positivity : (0 : ℝ) < (4 : ℝ)⁻¹)).const_mul
      ((3 / 4 : ℝ) * (baseHeatMass V)⁻¹)
  have heq : (fun x : V => ‖x‖ * baseD3Maj x) = fun x : V =>
      ((8 : ℝ)⁻¹ * (baseHeatMass V)⁻¹) *
          (‖x‖ ^ 4 * Real.exp (-(4 : ℝ)⁻¹ * ‖x‖ ^ 2)) +
        ((3 / 4 : ℝ) * (baseHeatMass V)⁻¹) *
          (‖x‖ ^ 2 * Real.exp (-(4 : ℝ)⁻¹ * ‖x‖ ^ 2)) := by
    funext x
    unfold baseD3Maj baseHeat
    ring
  rw [heq]
  exact h4.add h2

/-- The radial time-derivative majorant is integrable. -/
theorem baseD2DtMaj_int : Integrable (baseD2DtMaj : V → ℝ) := by
  have h0 := (baseD2Maj_int (V := V)).const_mul
    (((Module.finrank ℝ V : ℝ) + 2) / 2)
  have h1 := (baseD3First_int (V := V)).const_mul (2 : ℝ)⁻¹
  have heq : baseD2DtMaj = fun x : V =>
      (((Module.finrank ℝ V : ℝ) + 2) / 2) * baseD2Maj x +
        (2 : ℝ)⁻¹ * (‖x‖ * baseD3Maj x) := by
    funext x
    unfold baseD2DtMaj
    ring
  rw [heq]
  exact h0.add h1

/-- Dimension-dependent `L¹` constant for the Hessian time derivative. -/
def heatC2Dt (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] : ℝ :=
  ∫ x : V, baseD2DtMaj x

omit [Nontrivial V] in
theorem heatC2Dt_nonneg : 0 ≤ heatC2Dt V :=
  integral_nonneg baseD2DtMaj_nonneg

/-- Positive-time derivative of the heat-kernel Hessian. -/
def heatD2Dt (t : ℝ) (v w x : V) : ℝ :=
  ((heatScale t) ^ Module.finrank ℝ V)⁻¹ * (t ^ 2)⁻¹ *
    baseD2Dt v w ((heatScale t)⁻¹ • x)

/-- Radial majorant for the positive-time derivative of the heat-kernel
Hessian. -/
def heatD2DtMaj (t : ℝ) (x : V) : ℝ :=
  ((heatScale t) ^ Module.finrank ℝ V)⁻¹ * (t ^ 2)⁻¹ *
    baseD2DtMaj ((heatScale t)⁻¹ • x)

omit [MeasurableSpace V] [BorelSpace V] in
/-- At positive time, `heatD2Dt` is the actual time derivative of the
heat-kernel Hessian. -/
theorem heatD2_time {t : ℝ} (ht : 0 < t) (v w x : V) :
    HasDerivAt (fun s : ℝ => heatD2 s v w x) (heatD2Dt t v w x) t := by
  let n := Module.finrank ℝ V
  let r := heatScale t
  let z := r⁻¹ • x
  have hr : 0 < r := by
    simpa only [r] using heatScale_pos ht
  have hrsq : r ^ 2 = t := by
    simpa only [r, heatScale] using Real.sq_sqrt ht.le
  have hn : 0 < n := by
    simpa only [n] using (Module.finrank_pos : 0 < Module.finrank ℝ V)
  have hscale : HasDerivAt heatScale (1 / (2 * r)) t := by
    simpa only [heatScale, r] using Real.hasDerivAt_sqrt ht.ne'
  have hpow0 := (hscale.fun_pow n).inv (pow_ne_zero n hr.ne')
  change HasDerivAt (fun s : ℝ => ((heatScale s) ^ n)⁻¹)
    (-((n : ℝ) * r ^ (n - 1) * (1 / (2 * r))) / (r ^ n) ^ 2) t at hpow0
  have hpow : HasDerivAt (fun s : ℝ => ((heatScale s) ^ n)⁻¹)
      (-((n : ℝ) / (2 * t)) * (r ^ n)⁻¹) t := by
    convert hpow0 using 1
    rw [← hrsq]
    obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
    rw [hm]
    simp only [Nat.cast_succ, Nat.succ_sub_one, pow_succ]
    field_simp [hr.ne']
  have hinv := hscale.inv hr.ne'
  change HasDerivAt (fun s : ℝ => (heatScale s)⁻¹)
    (-(1 / (2 * r)) / r ^ 2) t at hinv
  have hcoeff0 := (hpow.mul hinv).mul hinv
  simp only [Pi.mul_apply] at hcoeff0
  rw [show heatScale t = r from rfl] at hcoeff0
  have hcoeff :
      HasDerivAt
        (fun s : ℝ => ((heatScale s) ^ n)⁻¹ * (heatScale s)⁻¹ *
          (heatScale s)⁻¹)
        (-(((n : ℝ) + 2) / 2) * (r ^ n)⁻¹ * (t ^ 2)⁻¹) t := by
    convert hcoeff0 using 1
    rw [← hrsq]
    field_simp [hr.ne']
    ring
  have hz0 := hinv.smul_const x
  change HasDerivAt (fun s : ℝ => (heatScale s)⁻¹ • x)
    ((-(1 / (2 * r)) / r ^ 2) • x) t at hz0
  have hz : HasDerivAt (fun s : ℝ => (heatScale s)⁻¹ • x)
      ((-(2 * t)⁻¹) • z) t := by
    convert hz0 using 1
    simp only [z, smul_smul]
    congr 1
    rw [← hrsq]
    field_simp [hr.ne']
  have hbase0 :
      HasDerivAt (fun s : ℝ => baseD2 v w ((heatScale s)⁻¹ • x))
        (baseD3Map v w z ((-(2 * t)⁻¹) • z)) t := by
    exact (baseD2_hasFDeriv v w z).comp_hasDerivAt t hz
  have hbase :
      HasDerivAt (fun s : ℝ => baseD2 v w ((heatScale s)⁻¹ • x))
        (-(2 * t)⁻¹ * baseD3 z v w z) t := by
    convert hbase0 using 1
    simp only [baseD3Map_apply]
    unfold baseD3
    simp only [real_inner_smul_right, real_inner_smul_left]
    ring
  have hprod := hcoeff.mul hbase
  convert hprod using 1
  unfold heatD2Dt baseD2Dt
  simp only [n, z]
  rw [show heatScale t = r from rfl]
  rw [← hrsq]
  field_simp [hr.ne']
  ring

omit [MeasurableSpace V] [BorelSpace V] [Nontrivial V] in
theorem heatD2DtMaj_nonneg {t : ℝ} (ht : 0 < t) (x : V) :
    0 ≤ heatD2DtMaj t x := by
  unfold heatD2DtMaj
  exact mul_nonneg
    (mul_nonneg
      (inv_nonneg.mpr (pow_nonneg (heatScale_pos ht).le _))
      (inv_nonneg.mpr (sq_nonneg t)))
    (baseD2DtMaj_nonneg _)

omit [MeasurableSpace V] [BorelSpace V] [Nontrivial V] in
/-- Pointwise bound for the positive-time Hessian derivative. -/
theorem heatD2Dt_bound {t : ℝ} (ht : 0 < t) (v w x : V) :
    ‖heatD2Dt t v w x‖ ≤ ‖v‖ * ‖w‖ * heatD2DtMaj t x := by
  unfold heatD2Dt heatD2DtMaj
  rw [Real.norm_eq_abs, abs_mul, abs_mul,
    abs_of_nonneg
      (inv_nonneg.mpr (pow_nonneg (heatScale_pos ht).le _)),
    abs_of_nonneg (inv_nonneg.mpr (sq_nonneg t))]
  have hfront :
      0 ≤ ((heatScale t) ^ Module.finrank ℝ V)⁻¹ * (t ^ 2)⁻¹ := by
    exact mul_nonneg
      (inv_nonneg.mpr (pow_nonneg (heatScale_pos ht).le _))
      (inv_nonneg.mpr (sq_nonneg t))
  calc
    ((heatScale t) ^ Module.finrank ℝ V)⁻¹ * (t ^ 2)⁻¹ *
        ‖baseD2Dt v w ((heatScale t)⁻¹ • x)‖ ≤
      ((heatScale t) ^ Module.finrank ℝ V)⁻¹ * (t ^ 2)⁻¹ *
        (‖v‖ * ‖w‖ * baseD2DtMaj ((heatScale t)⁻¹ • x)) := by
      exact mul_le_mul_of_nonneg_left (baseD2Dt_bound v w _) hfront
    _ = ‖v‖ * ‖w‖ *
        (((heatScale t) ^ Module.finrank ℝ V)⁻¹ * (t ^ 2)⁻¹ *
          baseD2DtMaj ((heatScale t)⁻¹ • x)) := by ring

/-- Integrability of the scaled Hessian-time-derivative majorant. -/
theorem heatD2DtMaj_int {t : ℝ} (ht : 0 < t) :
    Integrable (heatD2DtMaj t : V → ℝ) := by
  unfold heatD2DtMaj
  exact (baseD2DtMaj_int (V := V)).comp_smul
    (inv_ne_zero (heatScale_pos ht).ne') |>.const_mul _

omit [Nontrivial V] in
/-- Exact `t⁻²` spatial integral scaling of the time-derivative
majorant. -/
theorem integral_heatD2DtMaj {t : ℝ} (ht : 0 < t) :
    ∫ x : V, heatD2DtMaj t x = (t ^ 2)⁻¹ * heatC2Dt V := by
  have hr : 0 < heatScale t := heatScale_pos ht
  unfold heatD2DtMaj heatC2Dt
  rw [integral_const_mul,
    Measure.integral_comp_inv_smul_of_nonneg (volume : Measure V) baseD2DtMaj hr.le]
  simp only [smul_eq_mul]
  field_simp [hr.ne']

/-- `L¹` norm bound for the Hessian time derivative, with exact `t⁻²`
scaling. -/
theorem integral_norm_D2Dt {t : ℝ} (ht : 0 < t) (v w : V) :
    (∫ x : V, ‖heatD2Dt t v w x‖) ≤
      ‖v‖ * ‖w‖ * (t ^ 2)⁻¹ * heatC2Dt V := by
  have hker : Integrable (fun x : V => ‖heatD2Dt t v w x‖) := by
    refine ((heatD2DtMaj_int (V := V) ht).const_mul (‖v‖ * ‖w‖)).mono' ?_ ?_
    · apply Continuous.aestronglyMeasurable
      unfold heatD2Dt baseD2Dt baseD2 baseD3 baseHeat baseHeatMass heatScale
      fun_prop
    · filter_upwards with x
      simpa [mul_assoc] using heatD2Dt_bound ht v w x
  calc
    (∫ x : V, ‖heatD2Dt t v w x‖) ≤
        ∫ x : V, (‖v‖ * ‖w‖) * heatD2DtMaj t x := by
      exact integral_mono hker
        ((heatD2DtMaj_int (V := V) ht).const_mul (‖v‖ * ‖w‖))
        (fun x => by simpa [mul_assoc] using heatD2Dt_bound ht v w x)
    _ = (‖v‖ * ‖w‖) * ((t ^ 2)⁻¹ * heatC2Dt V) := by
      rw [integral_const_mul, integral_heatD2DtMaj ht]
    _ = ‖v‖ * ‖w‖ * (t ^ 2)⁻¹ * heatC2Dt V := by ring

end SecondTimeDerivative

end Euclidean
end Parabolic
end Analysis
end DifferentialGeometry

end
