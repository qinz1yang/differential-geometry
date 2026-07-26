import DifferentialGeometry.Analysis.Parabolic.Euclidean.HeatKernelLpPower

/-!
# Split Gaussian majorant for Koch--Lamm far shells

To obtain summable far-shell decay, split the `p`-th heat-kernel power into
two `p/2` factors.  One factor supplies the off-diagonal exponential and the
other remains an exactly integrable Gaussian.  This preserves the same
parabolic time power as the full `p`-mass.
-/

noncomputable section

open MeasureTheory Real
open scoped RealInnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace Euclidean

variable {V : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] [Nontrivial V]

/-- The integrable Gaussian left after extracting one `p/2` far-field
factor. -/
def klTailGauss (p : ℝ) (x : V) : ℝ :=
  ((baseHeatMass V)⁻¹) ^ (p / 2) * (baseHeat x) ^ (p / 2)

/-- Exact mass of `klTailGauss`. -/
def klTailMass (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] (p : ℝ) : ℝ :=
  ((baseHeatMass V)⁻¹) ^ (p / 2) * basePowMass V (p / 2)

/-- The split Gaussian is integrable at every positive exponent. -/
theorem klTailGauss_mem {p : ℝ} (hp : 0 < p) :
    Integrable (klTailGauss (V := V) p) := by
  unfold klTailGauss
  exact (baseHeatPow_mem (V := V) (half_pos hp)).const_mul _

omit [Nontrivial V] in
/-- Exact integral of the split Gaussian. -/
theorem klTailGauss_int {p : ℝ} (hp : 0 < p) :
    ∫ x : V, klTailGauss p x = klTailMass V p := by
  unfold klTailGauss klTailMass
  rw [integral_const_mul, baseHeatPow_int (V := V) (half_pos hp)]

/-- Scaled split-Gaussian kernel majorant. -/
def klTailKernel (u p : ℝ) (x : V) : ℝ :=
  ((((heatScale u) ^ Module.finrank ℝ V)⁻¹) ^ p) *
    klTailGauss p ((heatScale u)⁻¹ • x)

omit [Nontrivial V] in
/-- The translated split-Gaussian majorant has the same time power as the
full heat-kernel `p`-mass. -/
theorem klTailKernel_int {u p : ℝ} (hu : 0 < u) (hp : 0 < p) (x : V) :
    ∫ y : V, klTailKernel u p (x - y) =
      u ^ ((Module.finrank ℝ V : ℝ) * (1 - p) / 2) *
        klTailMass V p := by
  rw [integral_sub_left_eq_self
    (klTailKernel (V := V) u p) (volume : Measure V) x]
  unfold klTailKernel
  rw [integral_const_mul,
    Measure.integral_comp_inv_smul_of_nonneg (volume : Measure V)
      (klTailGauss (V := V) p) (heatScale_pos hu).le,
    klTailGauss_int (V := V) hp]
  simp only [smul_eq_mul]
  calc
    ((((heatScale u) ^ Module.finrank ℝ V)⁻¹) ^ p) *
          ((heatScale u) ^ Module.finrank ℝ V * klTailMass V p) =
        ((((heatScale u) ^ Module.finrank ℝ V)⁻¹) ^ p) *
          (heatScale u) ^ Module.finrank ℝ V * klTailMass V p := by ring
    _ = u ^ ((Module.finrank ℝ V : ℝ) * (1 - p) / 2) *
        klTailMass V p := by
      rw [heatPow_scale (V := V) hu]

omit [MeasurableSpace V] [BorelSpace V] [Nontrivial V] in
/-- If the scaled radius is at least `sqrt 2 * k`, the `p`-th heat-kernel
power is bounded by a summable exponential times the split-Gaussian
majorant. -/
theorem klHeatPow_tail {u p k : ℝ} (hu : 0 < u) (hp : 0 < p)
    (hk : 0 ≤ k) {x : V}
    (hlo : Real.sqrt 2 * k ≤ ‖(heatScale u)⁻¹ • x‖) :
    (heatKernel u x) ^ p ≤
      Real.exp (-(p * k ^ 2) / 4) * klTailKernel u p x := by
  let z : V := (heatScale u)⁻¹ • x
  have hsqrt : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hsq0 : (Real.sqrt 2 * k) ^ 2 ≤ ‖z‖ ^ 2 :=
    (sq_le_sq₀ (mul_nonneg (Real.sqrt_nonneg _) hk) (norm_nonneg _)).2 hlo
  have hsq : 2 * k ^ 2 ≤ ‖z‖ ^ 2 := by
    dsimp [z] at hsq0 ⊢
    nlinarith
  have harg : -(4 : ℝ)⁻¹ * ‖z‖ ^ 2 ≤ -(k ^ 2) / 2 := by
    nlinarith
  have hbase : baseHeat z ≤
      (baseHeatMass V)⁻¹ * Real.exp (-(k ^ 2) / 2) := by
    unfold baseHeat
    exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr harg)
      (inv_nonneg.mpr (baseHeatMass_pos (V := V)).le)
  have hhalf :
      (baseHeat z) ^ (p / 2) ≤
        ((baseHeatMass V)⁻¹) ^ (p / 2) *
          Real.exp (-(p * k ^ 2) / 4) := by
    calc
      (baseHeat z) ^ (p / 2) ≤
          ((baseHeatMass V)⁻¹ * Real.exp (-(k ^ 2) / 2)) ^
            (p / 2) :=
        Real.rpow_le_rpow (baseHeat_nonneg _) hbase (by positivity)
      _ = ((baseHeatMass V)⁻¹) ^ (p / 2) *
          Real.exp (-(p * k ^ 2) / 4) := by
        rw [Real.mul_rpow
          (inv_nonneg.mpr (baseHeatMass_pos (V := V)).le)
          (Real.exp_pos _).le, ← Real.exp_mul]
        congr 2
        ring
  have hbasePos : 0 < baseHeat z := by
    unfold baseHeat
    exact mul_pos (inv_pos.mpr (baseHeatMass_pos (V := V))) (Real.exp_pos _)
  have hsplit :
      (baseHeat z) ^ p =
        (baseHeat z) ^ (p / 2) * (baseHeat z) ^ (p / 2) := by
    rw [← Real.rpow_add hbasePos]
    congr 1
    ring
  rw [heatKernel_pow (V := V) hu hp]
  change
    ((((heatScale u) ^ Module.finrank ℝ V)⁻¹) ^ p) *
        (baseHeat z) ^ p ≤ _
  rw [hsplit]
  calc
    ((((heatScale u) ^ Module.finrank ℝ V)⁻¹) ^ p) *
          ((baseHeat z) ^ (p / 2) * (baseHeat z) ^ (p / 2)) ≤
        ((((heatScale u) ^ Module.finrank ℝ V)⁻¹) ^ p) *
          ((((baseHeatMass V)⁻¹) ^ (p / 2) *
              Real.exp (-(p * k ^ 2) / 4)) *
            (baseHeat z) ^ (p / 2)) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hhalf
          (Real.rpow_nonneg (baseHeat_nonneg _) _))
        (Real.rpow_nonneg
          (inv_nonneg.mpr (pow_nonneg (heatScale_pos hu).le _)) _)
    _ = Real.exp (-(p * k ^ 2) / 4) * klTailKernel u p x := by
      unfold klTailKernel klTailGauss
      dsimp [z]
      ring

end Euclidean
end Parabolic
end Analysis
end DifferentialGeometry

end
