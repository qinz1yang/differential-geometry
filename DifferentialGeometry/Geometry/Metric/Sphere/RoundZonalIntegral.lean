import DifferentialGeometry.Geometry.Metric.Sphere.RoundProjConnLC
import DifferentialGeometry.Geometry.Metric.Sphere.RoundChartGram
import DifferentialGeometry.Analysis.Integration.Measure.NoAtoms
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals


noncomputable section

open Manifold Metric Module Set MeasureTheory Filter Topology
open scoped Manifold Topology RealInnerProductSpace
open DifferentialGeometry.Integral.Measure

namespace DifferentialGeometry
namespace Geometry

local instance : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) :=
  ⟨finrank_euclideanSpace_fin⟩

def northPole : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 :=
  ⟨EuclideanSpace.single (2 : Fin 3) (1 : ℝ), by
    rw [mem_sphere_zero_iff_norm]
    simp⟩

def stereoHeight (x : EuclideanSpace ℝ (Fin 2)) : ℝ := (4 - ‖x‖ ^ 2) / (4 + ‖x‖ ^ 2)

def stereoDensity (x : EuclideanSpace ℝ (Fin 2)) : ℝ := (4 / (‖x‖ ^ 2 + 4)) ^ 2

theorem innerCoordFun_northPole_symm (x : EuclideanSpace ℝ (Fin 2)) :
    innerCoordFun (E := EuclideanSpace ℝ (Fin 3)) (n := 2)
        (EuclideanSpace.single (2 : Fin 3) (1 : ℝ))
        ((extChartAt (𝓡 2) northPole).symm x)
      = stereoHeight x := by
  have hw : (EuclideanSpace.single (2 : Fin 3) (1 : ℝ) : EuclideanSpace ℝ (Fin 3))
      = (northPole : EuclideanSpace ℝ (Fin 3)) := rfl
  change ⟪(EuclideanSpace.single (2 : Fin 3) (1 : ℝ) : EuclideanSpace ℝ (Fin 3)),
      ((extChartAt (𝓡 2) northPole).symm x : EuclideanSpace ℝ (Fin 3))⟫ = stereoHeight x
  rw [show ((extChartAt (𝓡 2) northPole).symm x : EuclideanSpace ℝ (Fin 3))
      = ((stereographic' 2 (-northPole)).symm x : EuclideanSpace ℝ (Fin 3)) from rfl]
  rw [stereographic'_symm_apply]
  simp only [inner_add_right, real_inner_smul_right]
  set U := (OrthonormalBasis.fromOrthogonalSpanSingleton (𝕜 := ℝ) 2
    (ne_zero_of_mem_unit_sphere (-northPole))).repr with hU
  set y := U.symm x with hy
  have hu : (↑northPole : EuclideanSpace ℝ (Fin 3))
      ∈ ℝ ∙ (↑(-northPole) : EuclideanSpace ℝ (Fin 3)) := by
    rw [Submodule.mem_span_singleton]
    exact ⟨-1, by rw [coe_neg_sphere]; module⟩
  have hA : ⟪(EuclideanSpace.single (2 : Fin 3) (1 : ℝ) : EuclideanSpace ℝ (Fin 3)),
      (↑y : EuclideanSpace ℝ (Fin 3))⟫ = 0 :=
    Submodule.inner_right_of_mem_orthogonal hu (Submodule.coe_mem y)
  have hB : ⟪(EuclideanSpace.single (2 : Fin 3) (1 : ℝ) : EuclideanSpace ℝ (Fin 3)),
      (↑(-northPole) : EuclideanSpace ℝ (Fin 3))⟫ = -1 := by
    rw [coe_neg_sphere, inner_neg_right, hw, real_inner_self_eq_norm_sq,
      mem_sphere_zero_iff_norm.mp northPole.2]
    norm_num
  have hC : ‖(↑y : EuclideanSpace ℝ (Fin 3))‖ = ‖x‖ := by
    rw [hy]; exact U.symm.norm_map x
  rw [hA, hB, hC]
  simp only [stereoHeight]
  ring

theorem integral_roundMetric_stereographic_reduction
    {F : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 → ℝ} (hF : Continuous F) :
    (∫ p, F p
        ∂(riemannianVolumeMeasure (I := 𝓡 2)
          (M := sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)
          (roundMetric (E := EuclideanSpace ℝ (Fin 3)) (n := 2))))
      = ∫ x : EuclideanSpace ℝ (Fin 2),
          stereoDensity x *
            F ((extChartAt (𝓡 2) northPole).symm x) ∂volume := sorry

def zonalRadialIntegrand (y : ℝ) : ℝ :=
  (4 / (y ^ 2 + 4)) ^ 2 *
    (((3 * ((4 - y ^ 2) / (4 + y ^ 2)) ^ 2 - 1) / 2) *
      (1 - ((4 - y ^ 2) / (4 + y ^ 2)) ^ 2))

def zonalRadialAntideriv (y : ℝ) : ℝ :=
  128 * (-(y ^ 2 + 4) ^ (-2 : ℤ) / 2 + 28 * (y ^ 2 + 4) ^ (-3 : ℤ) / 3
    - 48 * (y ^ 2 + 4) ^ (-4 : ℤ) + 384 * (y ^ 2 + 4) ^ (-5 : ℤ) / 5)

private lemma hasDerivAt_zonalRadialAntideriv (y : ℝ) :
    HasDerivAt zonalRadialAntideriv (y * zonalRadialIntegrand y) y := by
  have hne : (y ^ 2 + 4 : ℝ) ≠ 0 := by positivity
  have hbase : HasDerivAt (fun y : ℝ => y ^ 2 + 4) (2 * y) y := by
    simpa using (hasDerivAt_pow 2 y).add_const 4
  have hpow : ∀ m : ℤ, HasDerivAt (fun y : ℝ => (y ^ 2 + 4) ^ m)
      ((m : ℝ) * (y ^ 2 + 4) ^ (m - 1) * (2 * y)) y := by
    intro m
    simpa [Function.comp] using
      (hasDerivAt_zpow m (y ^ 2 + 4) (Or.inl hne)).comp y hbase
  have hH := ((((((hpow (-2)).neg.div_const 2).add
      (((hpow (-3)).const_mul 28).div_const 3)).sub
      ((hpow (-4)).const_mul 48)).add
      (((hpow (-5)).const_mul 384).div_const 5)).const_mul 128)
  convert hH using 1
  rw [zonalRadialIntegrand]
  rw [show ((-2 : ℤ) - 1) = -3 by rfl, show ((-3 : ℤ) - 1) = -4 by rfl,
      show ((-4 : ℤ) - 1) = -5 by rfl, show ((-5 : ℤ) - 1) = -6 by rfl]
  rw [show (4 + y ^ 2 : ℝ) = (y ^ 2 + 4) by ring]
  simp only [zpow_neg]
  rw [show ((2 : ℤ)) = ((2 : ℕ) : ℤ) by rfl, show ((3 : ℤ)) = ((3 : ℕ) : ℤ) by rfl,
      show ((4 : ℤ)) = ((4 : ℕ) : ℤ) by rfl, show ((5 : ℤ)) = ((5 : ℕ) : ℤ) by rfl,
      show ((6 : ℤ)) = ((6 : ℕ) : ℤ) by rfl]
  simp only [zpow_natCast]
  field_simp
  ring

private lemma zonalRadialAntideriv_zero : zonalRadialAntideriv 0 = 4 / 15 := by
  rw [zonalRadialAntideriv]; norm_num

private lemma tendsto_zonalRadialAntideriv :
    Tendsto zonalRadialAntideriv atTop (nhds 0) := by
  have h : Tendsto (fun y : ℝ => (y ^ 2 + 4)) atTop atTop :=
    Filter.tendsto_atTop_add_const_right _ 4 (tendsto_pow_atTop (by norm_num))
  have t : ∀ k : ℤ, k < 0 → Tendsto (fun y : ℝ => (y ^ 2 + 4) ^ k) atTop (nhds 0) :=
    fun k hk => (tendsto_zpow_atTop_zero hk).comp h
  have hexpr := ((((t (-2) (by norm_num)).neg.div_const 2).add
      (((t (-3) (by norm_num)).const_mul 28).div_const 3)).sub
      ((t (-4) (by norm_num)).const_mul 48)).add
      (((t (-5) (by norm_num)).const_mul 384).div_const 5)
  have := hexpr.const_mul 128
  simpa [zonalRadialAntideriv] using this

private lemma zonalRadialIntegrand_val (y : ℝ) :
    y * zonalRadialIntegrand y
      = 256 * y ^ 3 * (y ^ 4 - 16 * y ^ 2 + 16) / (y ^ 2 + 4) ^ 6 := by
  rw [zonalRadialIntegrand]
  have h1 : (y ^ 2 + 4 : ℝ) ≠ 0 := by positivity
  have h2 : (4 + y ^ 2 : ℝ) ≠ 0 := by positivity
  field_simp
  ring

private lemma continuous_mul_zonalRadialIntegrand :
    Continuous (fun y : ℝ => y * zonalRadialIntegrand y) := by
  have : (fun y : ℝ => y * zonalRadialIntegrand y)
      = fun y => 256 * y ^ 3 * (y ^ 4 - 16 * y ^ 2 + 16) / (y ^ 2 + 4) ^ 6 := by
    funext y; exact zonalRadialIntegrand_val y
  rw [this]
  apply Continuous.div
  · fun_prop
  · fun_prop
  · intro y; positivity

private lemma integrableOn_mul_zonalRadialIntegrand :
    IntegrableOn (fun y : ℝ => y * zonalRadialIntegrand y) (Ioi 0) := by
  refine MeasureTheory.Integrable.mono' (g := fun y => 1600 * (1 + y ^ 2)⁻¹)
    ((integrable_inv_one_add_sq.const_mul 1600).integrableOn) ?_ ?_
  · exact continuous_mul_zonalRadialIntegrand.aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    have hy0 : 0 ≤ y := le_of_lt hy
    rw [Real.norm_eq_abs, zonalRadialIntegrand_val y]
    rw [show (1600 : ℝ) * (1 + y ^ 2)⁻¹ = 1600 / (1 + y ^ 2) by rw [div_eq_mul_inv]]
    rw [abs_div, abs_of_pos (by positivity : (0:ℝ) < (y ^ 2 + 4) ^ 6)]
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have habs : |256 * y ^ 3 * (y ^ 4 - 16 * y ^ 2 + 16)|
        ≤ 256 * y ^ 3 * (25 * (y ^ 2 + 4) ^ 2) := by
      rw [abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ 256 * y ^ 3)]
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      rw [abs_le]
      constructor
      · nlinarith [sq_nonneg y, sq_nonneg (y ^ 2), sq_nonneg (y ^ 2 - 4)]
      · nlinarith [sq_nonneg y, sq_nonneg (y ^ 2)]
    calc |256 * y ^ 3 * (y ^ 4 - 16 * y ^ 2 + 16)| * (1 + y ^ 2)
        ≤ (256 * y ^ 3 * (25 * (y ^ 2 + 4) ^ 2)) * (1 + y ^ 2) :=
          mul_le_mul_of_nonneg_right habs (by positivity)
      _ ≤ 1600 * (y ^ 2 + 4) ^ 6 := by
          nlinarith [pow_nonneg hy0 3, sq_nonneg y, sq_nonneg (y ^ 2),
            pow_nonneg (by positivity : (0:ℝ) ≤ y ^ 2 + 4) 4,
            mul_nonneg (pow_nonneg hy0 3) (sq_nonneg (y ^ 2 - 1))]

theorem integral_stereoDensity_legendreTwo :
    (∫ x : EuclideanSpace ℝ (Fin 2),
        stereoDensity x *
          (((3 * stereoHeight x ^ 2 - 1) / 2) * (1 - stereoHeight x ^ 2)) ∂volume)
      = -(8 * Real.pi / 15) := by
  have hGrw : (∫ x : EuclideanSpace ℝ (Fin 2),
      stereoDensity x * (((3 * stereoHeight x ^ 2 - 1) / 2) * (1 - stereoHeight x ^ 2)) ∂volume)
      = ∫ x : EuclideanSpace ℝ (Fin 2), zonalRadialIntegrand ‖x‖ ∂volume :=
    integral_congr_ae (Filter.Eventually.of_forall (fun x => rfl))
  rw [hGrw]
  rw [MeasureTheory.integral_fun_norm_addHaar volume zonalRadialIntegrand]
  rw [finrank_euclideanSpace_fin]
  have hballr : volume.real (Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1) = Real.pi := by
    rw [MeasureTheory.measureReal_def, EuclideanSpace.volume_ball_fin_two]
    simp [ENNReal.toReal_ofReal Real.pi_pos.le]
  have hI : (∫ y in Set.Ioi (0 : ℝ), y ^ (2 - 1) • zonalRadialIntegrand y) = -(4 / 15) := by
    have he : (fun y : ℝ => y ^ (2 - 1) • zonalRadialIntegrand y)
        = fun y => y * zonalRadialIntegrand y := by
      funext y; rw [show (2 - 1) = 1 from rfl, pow_one, smul_eq_mul]
    rw [he]
    rw [MeasureTheory.integral_Ioi_of_hasDerivAt_of_tendsto'
      (fun x _ => hasDerivAt_zonalRadialAntideriv x) integrableOn_mul_zonalRadialIntegrand
      tendsto_zonalRadialAntideriv]
    rw [zonalRadialAntideriv_zero]; norm_num
  rw [hI, hballr]
  rw [nsmul_eq_mul, smul_eq_mul]
  push_cast
  ring

theorem integral_legendreTwo_height_roundMetric :
    (∫ p : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1,
        ((3 * (innerCoordFun (E := EuclideanSpace ℝ (Fin 3)) (n := 2)
            (EuclideanSpace.single (2 : Fin 3) (1 : ℝ)) p) ^ 2 - 1) / 2)
          * (1 - (innerCoordFun (E := EuclideanSpace ℝ (Fin 3)) (n := 2)
            (EuclideanSpace.single (2 : Fin 3) (1 : ℝ)) p) ^ 2)
        ∂(DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure (I := 𝓡 2)
          (M := Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)
          (DifferentialGeometry.Geometry.roundMetric
            (E := EuclideanSpace ℝ (Fin 3)) (n := 2))))
      = -(8 * Real.pi / 15) := by
  have hc : Continuous
      (fun p : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 =>
        (innerCoordFun (E := EuclideanSpace ℝ (Fin 3)) (n := 2)
          (EuclideanSpace.single (2 : Fin 3) (1 : ℝ)) p)) :=
    (innerCoordFun (E := EuclideanSpace ℝ (Fin 3)) (n := 2)
      (EuclideanSpace.single (2 : Fin 3) (1 : ℝ))).contMDiff.continuous
  have hcont : Continuous
      (fun p : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 =>
        ((3 * (innerCoordFun (E := EuclideanSpace ℝ (Fin 3)) (n := 2)
            (EuclideanSpace.single (2 : Fin 3) (1 : ℝ)) p) ^ 2 - 1) / 2)
          * (1 - (innerCoordFun (E := EuclideanSpace ℝ (Fin 3)) (n := 2)
            (EuclideanSpace.single (2 : Fin 3) (1 : ℝ)) p) ^ 2)) :=
    (((continuous_const.mul (hc.pow 2)).sub continuous_const).div_const 2).mul
      (continuous_const.sub (hc.pow 2))
  calc
    (∫ p : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1,
        ((3 * (innerCoordFun (E := EuclideanSpace ℝ (Fin 3)) (n := 2)
            (EuclideanSpace.single (2 : Fin 3) (1 : ℝ)) p) ^ 2 - 1) / 2)
          * (1 - (innerCoordFun (E := EuclideanSpace ℝ (Fin 3)) (n := 2)
            (EuclideanSpace.single (2 : Fin 3) (1 : ℝ)) p) ^ 2)
        ∂(riemannianVolumeMeasure (I := 𝓡 2)
          (M := Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)
          (roundMetric (E := EuclideanSpace ℝ (Fin 3)) (n := 2))))
        = ∫ x : EuclideanSpace ℝ (Fin 2),
            stereoDensity x *
              (((3 * (innerCoordFun (E := EuclideanSpace ℝ (Fin 3)) (n := 2)
                  (EuclideanSpace.single (2 : Fin 3) (1 : ℝ))
                  ((extChartAt (𝓡 2) northPole).symm x)) ^ 2 - 1) / 2)
                * (1 - (innerCoordFun (E := EuclideanSpace ℝ (Fin 3)) (n := 2)
                  (EuclideanSpace.single (2 : Fin 3) (1 : ℝ))
                  ((extChartAt (𝓡 2) northPole).symm x)) ^ 2)) ∂volume :=
      integral_roundMetric_stereographic_reduction hcont
    _ = ∫ x : EuclideanSpace ℝ (Fin 2),
          stereoDensity x *
            (((3 * stereoHeight x ^ 2 - 1) / 2) * (1 - stereoHeight x ^ 2)) ∂volume := by
        refine integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
        dsimp only
        rw [innerCoordFun_northPole_symm]
    _ = -(8 * Real.pi / 15) := integral_stereoDensity_legendreTwo

end Geometry
end DifferentialGeometry
