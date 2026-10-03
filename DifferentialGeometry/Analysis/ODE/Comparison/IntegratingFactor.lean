import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.Deriv.Inv

noncomputable section

open Set MeasureTheory Filter
open scoped Topology

namespace DifferentialGeometry.Analysis

def integratingFactor (rho : ℝ → ℝ) (s t : ℝ) : ℝ :=
  Real.exp (∫ w in s..t, rho w)

def affineComparisonSolution (rho : ℝ → ℝ) (k s t z : ℝ) : ℝ :=
  (integratingFactor rho s t)⁻¹ * (z - k * ∫ v in s..t, integratingFactor rho s v)

private theorem intervalIntegrable_of_continuousOn_Icc {rho : ℝ → ℝ} {a b s t : ℝ}
    (hc : ContinuousOn rho (Icc a b)) (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) :
    IntervalIntegrable rho volume s t :=
  (hc.mono (uIcc_subset_Icc hs ht)).intervalIntegrable

private theorem hasDerivWithinAt_intervalIntegral_of_continuousOn_Icc
    {rho : ℝ → ℝ} {a b s t : ℝ}
    (hc : ContinuousOn rho (Icc a b)) (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) :
    HasDerivWithinAt (fun v => ∫ w in s..v, rho w) (rho t) (Icc a b) t := by
  let : Fact (t ∈ Icc a b) := ⟨ht⟩
  have hm : StronglyMeasurableAtFilter rho (𝓝[Icc a b] t) volume :=
    ⟨Icc a b, self_mem_nhdsWithin, hc.aestronglyMeasurable measurableSet_Icc⟩
  exact intervalIntegral.integral_hasDerivWithinAt_right
    (intervalIntegrable_of_continuousOn_Icc hc hs ht) hm (hc t ht)

theorem integratingFactor_continuousOn {rho : ℝ → ℝ} {a b s : ℝ}
    (hi : IntervalIntegrable rho volume a b) (hs : s ∈ uIcc a b) :
    ContinuousOn (integratingFactor rho s) (uIcc a b) := by
  exact Real.continuous_exp.comp_continuousOn
    (intervalIntegral.continuousOn_primitive_interval' hi hs)

theorem hasDerivWithinAt_integratingFactor {rho : ℝ → ℝ} {a b s t : ℝ}
    (hc : ContinuousOn rho (Icc a b)) (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) :
    HasDerivWithinAt (integratingFactor rho s)
      (rho t * integratingFactor rho s t) (Icc a b) t := by
  change HasDerivWithinAt (fun v => Real.exp (∫ w in s..v, rho w))
    (rho t * Real.exp (∫ w in s..t, rho w)) (Icc a b) t
  simpa only [mul_comm] using
    (hasDerivWithinAt_intervalIntegral_of_continuousOn_Icc hc hs ht).exp

theorem integratingFactor_pos (rho : ℝ → ℝ) (s t : ℝ) :
    0 < integratingFactor rho s t := Real.exp_pos _

theorem integratingFactor_cocycle {rho : ℝ → ℝ} {s u t : ℝ}
    (hsu : IntervalIntegrable rho volume s u)
    (hut : IntervalIntegrable rho volume u t) :
    integratingFactor rho s t = integratingFactor rho s u * integratingFactor rho u t := by
  unfold integratingFactor
  rw [← intervalIntegral.integral_add_adjacent_intervals hsu hut, Real.exp_add]

private theorem integratingFactor_intervalIntegrable {rho : ℝ → ℝ} {s t : ℝ}
    (hi : IntervalIntegrable rho volume s t) :
    IntervalIntegrable (integratingFactor rho s) volume s t :=
  (integratingFactor_continuousOn hi left_mem_uIcc).intervalIntegrable

private theorem integratingFactor_integral_cocycle {rho : ℝ → ℝ} {s u t : ℝ}
    (hsu : IntervalIntegrable rho volume s u)
    (hut : IntervalIntegrable rho volume u t) :
    (∫ v in s..t, integratingFactor rho s v) =
      (∫ v in s..u, integratingFactor rho s v) +
        integratingFactor rho s u * ∫ v in u..t, integratingFactor rho u v := by
  have hfactor : ∀ v ∈ uIcc u t,
      integratingFactor rho s v = integratingFactor rho s u * integratingFactor rho u v := by
    intro v hv
    exact integratingFactor_cocycle hsu (hut.mono_set (uIcc_subset_uIcc left_mem_uIcc hv))
  have hFsut : IntervalIntegrable (integratingFactor rho s) volume u t :=
    ((integratingFactor_intervalIntegrable hut).const_mul (integratingFactor rho s u)).congr
      (fun v hv => (hfactor v (uIoc_subset_uIcc hv)).symm)
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (integratingFactor_intervalIntegrable hsu) hFsut]
  congr 1
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro v hv
  exact hfactor v hv

theorem affineComparisonSolution_cocycle {rho : ℝ → ℝ} {s u t : ℝ}
    (hsu : IntervalIntegrable rho volume s u)
    (hut : IntervalIntegrable rho volume u t) (k z : ℝ) :
    affineComparisonSolution rho k u t (affineComparisonSolution rho k s u z) =
      affineComparisonSolution rho k s t z := by
  unfold affineComparisonSolution
  rw [integratingFactor_cocycle hsu hut, integratingFactor_integral_cocycle hsu hut]
  field_simp [(integratingFactor_pos rho s u).ne', (integratingFactor_pos rho u t).ne']
  ring

theorem hasDerivWithinAt_affineComparisonSolution {rho : ℝ → ℝ} {a b s t : ℝ}
    (hc : ContinuousOn rho (Icc a b)) (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) (k z : ℝ) :
    HasDerivWithinAt (fun v => affineComparisonSolution rho k s v z)
      (-k - rho t * affineComparisonSolution rho k s t z) (Icc a b) t := by
  have hab : a ≤ b := hs.1.trans hs.2
  have hFc : ContinuousOn (integratingFactor rho s) (Icc a b) := by
    simpa only [uIcc_of_le hab] using
      integratingFactor_continuousOn (hc.intervalIntegrable_of_Icc hab)
        (by simpa only [uIcc_of_le hab] using hs)
  have hF := ((hasDerivWithinAt_integratingFactor hc hs ht).inv
    (integratingFactor_pos rho s t).ne').mul
    ((hasDerivWithinAt_const t (Icc a b) z).sub
      ((hasDerivWithinAt_intervalIntegral_of_continuousOn_Icc hFc hs ht).const_mul k))
  convert! hF using 1
  simp only [affineComparisonSolution, Pi.inv_apply, Pi.sub_apply]
  field_simp [(integratingFactor_pos rho s t).ne']
  ring

private theorem integral_abs_bound {rho : ℝ → ℝ} {s t M : ℝ}
    (hst : s ≤ t) (hbound : ∀ v ∈ Icc s t, |rho v| ≤ M) :
    |∫ w in s..t, rho w| ≤ M * (t - s) := by
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := s) (b := t)
    (f := rho) (C := M) (fun v hv => by
      rw [Real.norm_eq_abs]
      apply hbound v
      simpa only [uIcc_of_le hst] using (uIoc_subset_uIcc hv))
  simpa only [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hst)] using h

theorem integratingFactor_bounds {rho : ℝ → ℝ} {s t M : ℝ}
    (hst : s ≤ t) (hbound : ∀ v ∈ Icc s t, |rho v| ≤ M) :
    Real.exp (-M * (t - s)) ≤ integratingFactor rho s t ∧
      integratingFactor rho s t ≤ Real.exp (M * (t - s)) := by
  obtain ⟨hlo, hhi⟩ := abs_le.mp (integral_abs_bound hst hbound)
  exact ⟨Real.exp_le_exp.mpr (by linarith), Real.exp_le_exp.mpr hhi⟩

theorem affineComparisonSolution_lipschitz {rho : ℝ → ℝ} {s t M : ℝ}
    (hst : s ≤ t) (hbound : ∀ v ∈ Icc s t, |rho v| ≤ M) (k z z' : ℝ) :
    |affineComparisonSolution rho k s t z' - affineComparisonSolution rho k s t z| ≤
      Real.exp (M * (t - s)) * |z' - z| := by
  have hsub : affineComparisonSolution rho k s t z' - affineComparisonSolution rho k s t z =
      (integratingFactor rho s t)⁻¹ * (z' - z) := by
    unfold affineComparisonSolution
    ring
  have hi : (integratingFactor rho s t)⁻¹ ≤ Real.exp (M * (t - s)) := by
    rw [integratingFactor, ← Real.exp_neg]
    apply Real.exp_le_exp.mpr
    have hlo := (abs_le.mp (integral_abs_bound hst hbound)).1
    linarith
  rw [hsub, abs_mul, abs_of_pos (inv_pos.mpr (integratingFactor_pos rho s t))]
  exact mul_le_mul_of_nonneg_right hi (abs_nonneg _)

end DifferentialGeometry.Analysis
