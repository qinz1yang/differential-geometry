import DifferentialGeometry.Geometry.Comparison.Toponogov.ComparisonAngle
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

open Filter Set Topology

namespace DifferentialGeometry.Geometry.Comparison.Toponogov

noncomputable def comparisonAngleNegCurvature (κ a b c : ℝ) : ℝ :=
  if κ = 0 then comparisonAngle a b c else
    Real.arccos
      ((Real.cosh (Real.sqrt κ * a) * Real.cosh (Real.sqrt κ * b) -
        Real.cosh (Real.sqrt κ * c)) /
      (Real.sinh (Real.sqrt κ * a) * Real.sinh (Real.sqrt κ * b)))

@[simp] theorem comparisonAngleNegCurvature_zero (a b c : ℝ) :
    comparisonAngleNegCurvature 0 a b c = comparisonAngle a b c := by
  simp [comparisonAngleNegCurvature]

theorem comparisonAngleNegCurvature_mem_Icc (κ a b c : ℝ) :
    comparisonAngleNegCurvature κ a b c ∈ Icc 0 Real.pi := by
  unfold comparisonAngleNegCurvature
  split
  · exact comparisonAngle_mem_Icc a b c
  · exact ⟨Real.arccos_nonneg _, Real.arccos_le_pi _⟩

private theorem hyperbolic_cosine_mem_Icc {a b c : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hlower : |a - b| ≤ c) (hupper : c ≤ a + b) :
    (Real.cosh a * Real.cosh b - Real.cosh c) /
      (Real.sinh a * Real.sinh b) ∈ Icc (-1) 1 := by
  have hc : 0 ≤ c := (abs_nonneg _).trans hlower
  have hup : Real.cosh c ≤ Real.cosh (a + b) :=
    Real.cosh_le_cosh.2 (by rwa [abs_of_nonneg hc, abs_of_pos (add_pos ha hb)])
  have hlo : Real.cosh (a - b) ≤ Real.cosh c :=
    Real.cosh_le_cosh.2 (by rwa [abs_of_nonneg hc])
  have hden : 0 < Real.sinh a * Real.sinh b :=
    mul_pos (Real.sinh_pos_iff.2 ha) (Real.sinh_pos_iff.2 hb)
  rw [Real.cosh_add] at hup
  rw [Real.cosh_sub] at hlo
  constructor
  · rw [le_div_iff₀ hden]
    linarith
  · rw [div_le_iff₀ hden]
    linarith

theorem cos_comparisonAngleNegCurvature_of_pos {κ a b c : ℝ}
    (hκ : 0 < κ) (ha : 0 < a) (hb : 0 < b)
    (hlower : |a - b| ≤ c) (hupper : c ≤ a + b) :
    Real.cos (comparisonAngleNegCurvature κ a b c) =
      (Real.cosh (Real.sqrt κ * a) * Real.cosh (Real.sqrt κ * b) -
        Real.cosh (Real.sqrt κ * c)) /
      (Real.sinh (Real.sqrt κ * a) * Real.sinh (Real.sqrt κ * b)) := by
  have hs : 0 < Real.sqrt κ := Real.sqrt_pos.2 hκ
  have hscaleLower : |Real.sqrt κ * a - Real.sqrt κ * b| ≤ Real.sqrt κ * c := by
    rw [← mul_sub, abs_mul, abs_of_pos hs]
    exact mul_le_mul_of_nonneg_left hlower hs.le
  have hscaleUpper : Real.sqrt κ * c ≤ Real.sqrt κ * a + Real.sqrt κ * b := by
    simpa only [mul_add] using mul_le_mul_of_nonneg_left hupper hs.le
  have hr := hyperbolic_cosine_mem_Icc (mul_pos hs ha) (mul_pos hs hb)
    hscaleLower hscaleUpper
  rw [comparisonAngleNegCurvature, ite_eq_right hκ.ne']
  exact Real.cos_arccos hr.1 hr.2

theorem comparisonAngleNegCurvature_add {κ a b : ℝ}
    (hκ : 0 ≤ κ) (ha : 0 < a) (hb : 0 < b) :
    comparisonAngleNegCurvature κ a b (a + b) = Real.pi := by
  by_cases hk : κ = 0
  · rw [hk, comparisonAngleNegCurvature_zero]
    exact comparisonAngle_add ha hb
  · have hs : 0 < Real.sqrt κ := Real.sqrt_pos.2 (lt_of_le_of_ne hκ (Ne.symm hk))
    have hden : Real.sinh (Real.sqrt κ * a) * Real.sinh (Real.sqrt κ * b) ≠ 0 :=
      (mul_pos (Real.sinh_pos_iff.2 (mul_pos hs ha))
        (Real.sinh_pos_iff.2 (mul_pos hs hb))).ne'
    rw [comparisonAngleNegCurvature, ite_eq_right hk, mul_add, Real.cosh_add]
    have hquotient :
        (Real.cosh (Real.sqrt κ * a) * Real.cosh (Real.sqrt κ * b) -
          (Real.cosh (Real.sqrt κ * a) * Real.cosh (Real.sqrt κ * b) +
          Real.sinh (Real.sqrt κ * a) * Real.sinh (Real.sqrt κ * b))) /
          (Real.sinh (Real.sqrt κ * a) * Real.sinh (Real.sqrt κ * b)) = -1 := by
      apply (div_eq_iff hden).2
      ring
    rw [hquotient, Real.arccos_neg_one]

theorem comparisonAngleNegCurvature_abs_sub {κ a b : ℝ}
    (hκ : 0 ≤ κ) (ha : 0 < a) (hb : 0 < b) :
    comparisonAngleNegCurvature κ a b |a - b| = 0 := by
  by_cases hk : κ = 0
  · rw [hk, comparisonAngleNegCurvature_zero]
    exact comparisonAngle_abs_sub ha hb
  · have hs : 0 < Real.sqrt κ := Real.sqrt_pos.2 (lt_of_le_of_ne hκ (Ne.symm hk))
    have hden : Real.sinh (Real.sqrt κ * a) * Real.sinh (Real.sqrt κ * b) ≠ 0 :=
      (mul_pos (Real.sinh_pos_iff.2 (mul_pos hs ha))
        (Real.sinh_pos_iff.2 (mul_pos hs hb))).ne'
    have hscale : Real.sqrt κ * |a - b| = |Real.sqrt κ * a - Real.sqrt κ * b| := by
      rw [← mul_sub, abs_mul, abs_of_pos hs]
    rw [comparisonAngleNegCurvature, ite_eq_right hk, hscale, Real.cosh_abs,
      Real.cosh_sub, sub_sub_cancel, div_self hden, Real.arccos_one]

theorem comparisonAngleNegCurvature_self {κ a : ℝ} (hκ : 0 ≤ κ) (ha : 0 < a) :
    comparisonAngleNegCurvature κ a a 0 = 0 := by
  simpa only [sub_self, abs_zero] using comparisonAngleNegCurvature_abs_sub hκ ha ha

theorem comparisonAngleNegCurvature_comm (κ a b c : ℝ) :
    comparisonAngleNegCurvature κ a b c = comparisonAngleNegCurvature κ b a c := by
  unfold comparisonAngleNegCurvature
  split
  · exact comparisonAngle_comm a b c
  · congr 1
    congr 1 <;> ring

private noncomputable def sinhRatio : ℝ → ℝ :=
  Function.update (fun x => Real.sinh x / x) 0 1

private theorem sinhRatio_zero : sinhRatio 0 = 1 := by
  simp [sinhRatio]

private theorem continuousAt_sinhRatio_zero : ContinuousAt sinhRatio 0 := by
  simpa only [sinhRatio, Real.sinh_zero, Real.cosh_zero, sub_zero] using
    (Real.hasDerivAt_sinh 0).continuousAt_div

private theorem sinh_eq_mul_sinhRatio (x : ℝ) :
    Real.sinh x = x * sinhRatio x := by
  by_cases hx : x = 0
  · simp [hx]
  · simp [sinhRatio, mul_div_cancel₀, hx]

private noncomputable def coshRatio (x : ℝ) : ℝ :=
  sinhRatio (x / 2) ^ 2 / 2

private theorem coshRatio_zero : coshRatio 0 = 1 / 2 := by
  simp [coshRatio, sinhRatio_zero]

private theorem continuousAt_coshRatio_zero : ContinuousAt coshRatio 0 := by
  have h : ContinuousAt (fun x : ℝ => sinhRatio (x / 2)) 0 :=
    continuousAt_sinhRatio_zero.comp_of_eq (continuousAt_id.div_const 2) (by simp)
  exact (h.pow 2).div_const 2

private theorem cosh_eq_one_add_mul_coshRatio (x : ℝ) :
    Real.cosh x = 1 + x ^ 2 * coshRatio x := by
  have hc := Real.cosh_two_mul (x / 2)
  have hs := Real.cosh_sq (x / 2)
  have hr := sinh_eq_mul_sinhRatio (x / 2)
  have hx : 2 * (x / 2) = x := by ring
  rw [hx] at hc
  unfold coshRatio
  rw [hr] at hc hs
  nlinarith

private noncomputable def regularizedCosine (s a b c : ℝ) : ℝ :=
  (a ^ 2 * coshRatio (s * a) + b ^ 2 * coshRatio (s * b) -
    c ^ 2 * coshRatio (s * c) +
    s ^ 2 * a ^ 2 * b ^ 2 * coshRatio (s * a) * coshRatio (s * b)) /
  (a * b * sinhRatio (s * a) * sinhRatio (s * b))

private theorem comparisonAngleNegCurvature_eq_regularizedCosine {κ : ℝ}
    (hκ : 0 ≤ κ) (a b c : ℝ) :
    comparisonAngleNegCurvature κ a b c =
      Real.arccos (regularizedCosine (Real.sqrt κ) a b c) := by
  by_cases hk : κ = 0
  · simp only [hk, comparisonAngleNegCurvature_zero, Real.sqrt_zero,
      regularizedCosine, zero_mul, coshRatio_zero, sinhRatio_zero,
      zero_pow (by decide : 2 ≠ 0), add_zero, mul_one,
      comparisonAngle]
    congr 1
    ring
  · have hs : Real.sqrt κ ≠ 0 := (Real.sqrt_pos.2 (lt_of_le_of_ne hκ (Ne.symm hk))).ne'
    rw [comparisonAngleNegCurvature, ite_eq_right hk]
    congr 1
    rw [cosh_eq_one_add_mul_coshRatio (Real.sqrt κ * a),
      cosh_eq_one_add_mul_coshRatio (Real.sqrt κ * b),
      cosh_eq_one_add_mul_coshRatio (Real.sqrt κ * c),
      sinh_eq_mul_sinhRatio (Real.sqrt κ * a),
      sinh_eq_mul_sinhRatio (Real.sqrt κ * b)]
    have hnum :
        (1 + (Real.sqrt κ * a) ^ 2 * coshRatio (Real.sqrt κ * a)) *
          (1 + (Real.sqrt κ * b) ^ 2 * coshRatio (Real.sqrt κ * b)) -
          (1 + (Real.sqrt κ * c) ^ 2 * coshRatio (Real.sqrt κ * c)) =
        (Real.sqrt κ) ^ 2 *
          (a ^ 2 * coshRatio (Real.sqrt κ * a) +
           b ^ 2 * coshRatio (Real.sqrt κ * b) -
           c ^ 2 * coshRatio (Real.sqrt κ * c) +
           (Real.sqrt κ) ^ 2 * a ^ 2 * b ^ 2 *
             coshRatio (Real.sqrt κ * a) * coshRatio (Real.sqrt κ * b)) := by ring
    have hden :
        (Real.sqrt κ * a * sinhRatio (Real.sqrt κ * a)) *
          (Real.sqrt κ * b * sinhRatio (Real.sqrt κ * b)) =
        (Real.sqrt κ) ^ 2 *
          (a * b * sinhRatio (Real.sqrt κ * a) * sinhRatio (Real.sqrt κ * b)) := by ring
    rw [hnum, hden, mul_div_mul_left _ _ (pow_ne_zero 2 hs)]
    rfl

theorem tendsto_comparisonAngleNegCurvature_zero {I : Type*} {l : Filter I}
    {κ a b c : I → ℝ} {a₀ b₀ c₀ : ℝ}
    (hκ : Tendsto κ l (𝓝 0))
    (ha : Tendsto a l (𝓝 a₀)) (hb : Tendsto b l (𝓝 b₀))
    (hc : Tendsto c l (𝓝 c₀))
    (hκnonneg : ∀ᶠ i in l, 0 ≤ κ i) (ha₀ : 0 < a₀) (hb₀ : 0 < b₀) :
    Tendsto (fun i => comparisonAngleNegCurvature (κ i) (a i) (b i) (c i)) l
      (𝓝 (comparisonAngle a₀ b₀ c₀)) := by
  have hs : Tendsto (fun i => Real.sqrt (κ i)) l (𝓝 0) := by
    simpa only [Function.comp_def, Real.sqrt_zero] using
      Real.continuous_sqrt.continuousAt.tendsto.comp hκ
  have hsa : Tendsto (fun i => Real.sqrt (κ i) * a i) l (𝓝 0) := by
    simpa using hs.mul ha
  have hsb : Tendsto (fun i => Real.sqrt (κ i) * b i) l (𝓝 0) := by
    simpa using hs.mul hb
  have hsc : Tendsto (fun i => Real.sqrt (κ i) * c i) l (𝓝 0) := by
    simpa using hs.mul hc
  have hqa : Tendsto (fun i => coshRatio (Real.sqrt (κ i) * a i)) l (𝓝 (1 / 2)) := by
    simpa only [Function.comp_def, coshRatio_zero] using continuousAt_coshRatio_zero.tendsto.comp hsa
  have hqb : Tendsto (fun i => coshRatio (Real.sqrt (κ i) * b i)) l (𝓝 (1 / 2)) := by
    simpa only [Function.comp_def, coshRatio_zero] using continuousAt_coshRatio_zero.tendsto.comp hsb
  have hqc : Tendsto (fun i => coshRatio (Real.sqrt (κ i) * c i)) l (𝓝 (1 / 2)) := by
    simpa only [Function.comp_def, coshRatio_zero] using continuousAt_coshRatio_zero.tendsto.comp hsc
  have hSa : Tendsto (fun i => sinhRatio (Real.sqrt (κ i) * a i)) l (𝓝 1) := by
    simpa only [Function.comp_def, sinhRatio_zero] using continuousAt_sinhRatio_zero.tendsto.comp hsa
  have hSb : Tendsto (fun i => sinhRatio (Real.sqrt (κ i) * b i)) l (𝓝 1) := by
    simpa only [Function.comp_def, sinhRatio_zero] using continuousAt_sinhRatio_zero.tendsto.comp hsb
  have hnum : Tendsto (fun i =>
      a i ^ 2 * coshRatio (Real.sqrt (κ i) * a i) +
      b i ^ 2 * coshRatio (Real.sqrt (κ i) * b i) -
      c i ^ 2 * coshRatio (Real.sqrt (κ i) * c i) +
      Real.sqrt (κ i) ^ 2 * a i ^ 2 * b i ^ 2 *
        coshRatio (Real.sqrt (κ i) * a i) * coshRatio (Real.sqrt (κ i) * b i)) l
      (𝓝 (a₀ ^ 2 * (1 / 2) + b₀ ^ 2 * (1 / 2) - c₀ ^ 2 * (1 / 2))) := by
    simpa only [zero_pow (by decide : 2 ≠ 0), zero_mul, add_zero] using
      ((((ha.pow 2).mul hqa).add ((hb.pow 2).mul hqb)).sub
        ((hc.pow 2).mul hqc)).add
        (((((hs.pow 2).mul (ha.pow 2)).mul (hb.pow 2)).mul hqa).mul hqb)
  have hden : Tendsto (fun i =>
      a i * b i * sinhRatio (Real.sqrt (κ i) * a i) *
        sinhRatio (Real.sqrt (κ i) * b i)) l (𝓝 (a₀ * b₀)) := by
    simpa only [mul_one] using ((ha.mul hb).mul hSa).mul hSb
  have hreg : Tendsto (fun i => regularizedCosine (Real.sqrt (κ i)) (a i) (b i) (c i)) l
      (𝓝 ((a₀ ^ 2 + b₀ ^ 2 - c₀ ^ 2) / (2 * a₀ * b₀))) := by
    have hr := hnum.div hden (mul_ne_zero ha₀.ne' hb₀.ne')
    convert hr using 1 <;> try rfl
    congr 1
    ring
  have hang := Real.continuous_arccos.continuousAt.tendsto.comp hreg
  apply hang.congr'
  filter_upwards [hκnonneg] with i hi
  exact (comparisonAngleNegCurvature_eq_regularizedCosine hi (a i) (b i) (c i)).symm

end DifferentialGeometry.Geometry.Comparison.Toponogov
