import DifferentialGeometry.Analysis.Parabolic.Euclidean.HeatD1LpPower

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

def baseD1Half (x : V) : ℝ :=
  ((2 : ℝ)⁻¹ * ‖x‖) *
    ((baseHeatMass V)⁻¹ * Real.exp (-(8 : ℝ)⁻¹ * ‖x‖ ^ 2))

omit [MeasurableSpace V] [BorelSpace V] [Nontrivial V] in
theorem baseD1Half_nonneg (x : V) : 0 ≤ baseD1Half x := by
  unfold baseD1Half
  exact mul_nonneg (mul_nonneg (by positivity) (norm_nonneg x))
    (mul_nonneg (inv_nonneg.mpr (baseHeatMass_pos (V := V)).le)
      (Real.exp_pos _).le)

omit [MeasurableSpace V] [BorelSpace V] [Nontrivial V] in
theorem baseD1_split (x : V) :
    baseD1Maj x =
      baseD1Half x * Real.exp (-(8 : ℝ)⁻¹ * ‖x‖ ^ 2) := by
  have hexp : Real.exp (-(4 : ℝ)⁻¹ * ‖x‖ ^ 2) =
      Real.exp (-(8 : ℝ)⁻¹ * ‖x‖ ^ 2) *
        Real.exp (-(8 : ℝ)⁻¹ * ‖x‖ ^ 2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  unfold baseD1Maj baseD1Half baseHeat
  rw [hexp]
  ring

omit [MeasurableSpace V] [BorelSpace V] [Nontrivial V] in
theorem baseD1Half_scale (x : V) :
    baseD1Half x = Real.sqrt 2 *
      baseD1Maj ((Real.sqrt 2)⁻¹ • x) := by
  have hs : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hs2 : (Real.sqrt 2) ^ 2 = (2 : ℝ) :=
    Real.sq_sqrt (by norm_num)
  have hnorm : ‖(Real.sqrt 2)⁻¹ • x‖ =
      (Real.sqrt 2)⁻¹ * ‖x‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hs]
  have hinv2 : ((Real.sqrt 2)⁻¹ : ℝ) ^ 2 = (2 : ℝ)⁻¹ := by
    rw [inv_pow, hs2]
  have harg : -(4 : ℝ)⁻¹ * ((Real.sqrt 2)⁻¹ * ‖x‖) ^ 2 =
      -(8 : ℝ)⁻¹ * ‖x‖ ^ 2 := by
    rw [mul_pow, hinv2]
    ring
  have hcancel : Real.sqrt 2 * (Real.sqrt 2)⁻¹ = 1 :=
    mul_inv_cancel₀ hs.ne'
  unfold baseD1Half baseD1Maj baseHeat
  rw [hnorm, harg]
  symm
  calc
    Real.sqrt 2 *
          (((2 : ℝ)⁻¹ * ((Real.sqrt 2)⁻¹ * ‖x‖)) *
            ((baseHeatMass V)⁻¹ *
              Real.exp (-(8 : ℝ)⁻¹ * ‖x‖ ^ 2))) =
        (Real.sqrt 2 * (Real.sqrt 2)⁻¹) *
          (((2 : ℝ)⁻¹ * ‖x‖) *
            ((baseHeatMass V)⁻¹ *
              Real.exp (-(8 : ℝ)⁻¹ * ‖x‖ ^ 2))) := by ring
    _ = ((2 : ℝ)⁻¹ * ‖x‖) *
        ((baseHeatMass V)⁻¹ *
          Real.exp (-(8 : ℝ)⁻¹ * ‖x‖ ^ 2)) := by rw [hcancel, one_mul]

theorem baseD1Half_rpow {p : ℝ} (hp1 : 1 ≤ p) (hp2 : p ≤ 2) :
    Integrable (fun x : V ↦ (baseD1Half x) ^ p) := by
  have hs : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hbase := (baseD1Maj_rpow (V := V) hp1 hp2).comp_smul
    (inv_ne_zero hs.ne')
  have hscaled := hbase.const_mul ((Real.sqrt 2) ^ p)
  convert hscaled using 1
  funext x
  rw [baseD1Half_scale (V := V) x,
    Real.mul_rpow hs.le (baseD1Maj_nonneg _)]

omit [MeasurableSpace V] [BorelSpace V] [Nontrivial V] in
theorem baseD1Half_le (x : V) :
    baseD1Half x ≤ 2 * (baseHeatMass V)⁻¹ := by
  let r : ℝ := ‖x‖
  let a : ℝ := (8 : ℝ)⁻¹ * r ^ 2
  have hr0 : 0 ≤ r := norm_nonneg x
  have hpoly : r / 4 ≤ 1 + a := by
    dsimp [a]
    nlinarith [sq_nonneg (r - 1)]
  have hrexp : r / 4 ≤ Real.exp a :=
    hpoly.trans (by simpa only [add_comm] using Real.add_one_le_exp a)
  have hmul := mul_le_mul_of_nonneg_right hrexp (Real.exp_pos (-a)).le
  have hrad : (2 : ℝ)⁻¹ * r * Real.exp (-a) ≤ 2 := by
    calc
      (2 : ℝ)⁻¹ * r * Real.exp (-a) =
          2 * ((r / 4) * Real.exp (-a)) := by ring
      _ ≤ 2 * (Real.exp a * Real.exp (-a)) :=
        mul_le_mul_of_nonneg_left hmul (by norm_num)
      _ = 2 := by rw [← Real.exp_add]; norm_num
  dsimp only [r, a] at hrad
  have hrad' : (2 : ℝ)⁻¹ * ‖x‖ *
      Real.exp (-(8 : ℝ)⁻¹ * ‖x‖ ^ 2) ≤ 2 := by
    convert hrad using 1
    ring_nf
  unfold baseD1Half
  calc
    ((2 : ℝ)⁻¹ * ‖x‖) *
          ((baseHeatMass V)⁻¹ *
            Real.exp (-(8 : ℝ)⁻¹ * ‖x‖ ^ 2)) =
        (baseHeatMass V)⁻¹ *
          ((2 : ℝ)⁻¹ * ‖x‖ *
            Real.exp (-(8 : ℝ)⁻¹ * ‖x‖ ^ 2)) := by ring
    _ ≤ (baseHeatMass V)⁻¹ * 2 :=
      mul_le_mul_of_nonneg_left hrad'
        (inv_nonneg.mpr (baseHeatMass_pos (V := V)).le)
    _ = 2 * (baseHeatMass V)⁻¹ := by ring

omit [MeasurableSpace V] [BorelSpace V] [Nontrivial V] in
theorem baseD1Maj_gauss (x : V) :
    baseD1Maj x ≤
      2 * (baseHeatMass V)⁻¹ *
        Real.exp (-(8 : ℝ)⁻¹ * ‖x‖ ^ 2) := by
  rw [baseD1_split (V := V) x]
  exact mul_le_mul_of_nonneg_right (baseD1Half_le (V := V) x)
    (Real.exp_pos _).le

omit [MeasurableSpace V] [BorelSpace V] [Nontrivial V] in
theorem baseD1Tail_le {R : ℝ} (hR : 0 ≤ R) {x : V} (hx : R ≤ ‖x‖) :
    baseD1Maj x ≤
      Real.exp (-(8 : ℝ)⁻¹ * R ^ 2) * baseD1Half x := by
  have hsq : R ^ 2 ≤ ‖x‖ ^ 2 :=
    (sq_le_sq₀ hR (norm_nonneg x)).2 hx
  have hexp : Real.exp (-(8 : ℝ)⁻¹ * ‖x‖ ^ 2) ≤
      Real.exp (-(8 : ℝ)⁻¹ * R ^ 2) :=
    Real.exp_le_exp.mpr (by nlinarith)
  rw [baseD1_split (V := V) x]
  calc
    baseD1Half x * Real.exp (-(8 : ℝ)⁻¹ * ‖x‖ ^ 2) ≤
        baseD1Half x * Real.exp (-(8 : ℝ)⁻¹ * R ^ 2) :=
      mul_le_mul_of_nonneg_left hexp (baseD1Half_nonneg (V := V) x)
    _ = Real.exp (-(8 : ℝ)⁻¹ * R ^ 2) * baseD1Half x := mul_comm _ _

omit [MeasurableSpace V] [BorelSpace V] [Nontrivial V] in
theorem baseD1Tail_pow {R p : ℝ} (hR : 0 ≤ R) (hp : 0 ≤ p)
    {x : V} (hx : R ≤ ‖x‖) :
    (baseD1Maj x) ^ p ≤
      (Real.exp (-(8 : ℝ)⁻¹ * R ^ 2)) ^ p *
        (baseD1Half x) ^ p := by
  have hpow := Real.rpow_le_rpow (baseD1Maj_nonneg x)
    (baseD1Tail_le (V := V) hR hx) hp
  rw [Real.mul_rpow (Real.exp_pos _).le
    (baseD1Half_nonneg (V := V) x)] at hpow
  exact hpow

def baseD1HalfMass (V : Type*) [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    [MeasurableSpace V] [BorelSpace V] (p : ℝ) : ℝ :=
  ∫ x : V, (baseD1Half x) ^ p

omit [Nontrivial V] in
theorem baseD1HalfMass_nn (p : ℝ) : 0 ≤ baseD1HalfMass V p := by
  unfold baseD1HalfMass
  exact integral_nonneg fun x ↦
    Real.rpow_nonneg (baseD1Half_nonneg (V := V) x) p

end Euclidean
end Parabolic
end Analysis
end DifferentialGeometry

end
