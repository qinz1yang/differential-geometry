import DifferentialGeometry.Analysis.Elliptic.ComplexPlane.Regularization.Defs
import Mathlib.MeasureTheory.Integral.DominatedConvergence







noncomputable section

open Filter MeasureTheory
open scoped Topology

namespace DifferentialGeometry.Analysis


theorem regularizedConformalWeight_zero (a f : ℂ → ℝ) (z : ℂ) :
    regularizedConformalWeight a f 0 z = if a z = 0 then 0 else 1 := by
  by_cases ha : a z = 0 <;>
    simp [regularizedConformalWeight, regularizedConformalCoefficient, ha]



theorem regularizedConformalWeight_mem_Icc_all {a f : ℂ → ℝ} {z : ℂ}
    (ha : 0 ≤ a z) (ε : ℝ) : regularizedConformalWeight a f ε z ∈ Set.Icc 0 1 := by
  by_cases hε : ε = 0
  · subst ε
    rw [regularizedConformalWeight_zero]
    split_ifs <;> constructor <;> norm_num
  · exact regularizedConformalWeight_mem_Icc ha hε



theorem tendsto_regularizedConformalWeight (a f : ℂ → ℝ) (z : ℂ) :
    Tendsto (fun ε : ℝ => regularizedConformalWeight a f ε z) (𝓝 0)
      (𝓝 (if a z = 0 then 0 else 1)) := by
  by_cases ha : a z = 0
  · simp [regularizedConformalWeight, regularizedConformalCoefficient, ha]
  · have h : ContinuousAt (fun ε : ℝ => regularizedConformalWeight a f ε z) 0 := by
      unfold regularizedConformalWeight regularizedConformalCoefficient
      exact continuousAt_const.div
        (continuousAt_const.add ((continuousAt_id.pow 2).mul continuousAt_const)) (by simpa)
    change Tendsto _ _ (𝓝 (regularizedConformalWeight a f 0 z)) at h
    simpa only [regularizedConformalWeight_zero] using h




theorem tendsto_integral_regularizedConformalWeight_comp
    {X : Type*} [MeasurableSpace X] {μ : Measure X} {c : X → ℂ} {a f : ℂ → ℝ} {b : X → ℝ}
    (hc : Measurable c) (ha : Measurable a) (hf : Measurable f) (han : ∀ᵐ z ∂μ, 0 ≤ a (c z))
    (hb : Integrable b μ) :
    Tendsto (fun ε : ℝ => ∫ z, regularizedConformalWeight a f ε (c z) * b z ∂μ) (𝓝 0)
      (𝓝 (∫ z, if a (c z) = 0 then 0 else b z ∂μ)) := by
  apply tendsto_integral_filter_of_dominated_convergence (fun z => ‖b z‖)
  · apply Eventually.of_forall
    intro ε
    have hw : Measurable (regularizedConformalWeight a f ε) :=
      ha.div (ha.add (measurable_const.mul ((measurable_const.mul hf).exp)))
    exact (hw.comp hc).aestronglyMeasurable.mul hb.aestronglyMeasurable
  · apply Eventually.of_forall
    intro ε
    filter_upwards [han] with z hz
    have hw := regularizedConformalWeight_mem_Icc_all (f := f) hz ε
    rw [norm_mul, Real.norm_of_nonneg hw.1]
    exact mul_le_of_le_one_left (norm_nonneg _) hw.2
  · exact hb.norm
  · apply Eventually.of_forall
    intro z
    convert (tendsto_regularizedConformalWeight a f (c z)).mul_const (b z) using 1
    split_ifs <;> simp



theorem tendsto_integral_regularizedConformalWeight
    {μ : Measure ℂ} {a f b : ℂ → ℝ}
    (ha : Measurable a) (hf : Measurable f) (han : ∀ᵐ z ∂μ, 0 ≤ a z)
    (hb : Integrable b μ) :
    Tendsto (fun ε : ℝ => ∫ z, regularizedConformalWeight a f ε z * b z ∂μ) (𝓝 0)
      (𝓝 (∫ z, if a z = 0 then 0 else b z ∂μ)) :=
  tendsto_integral_regularizedConformalWeight_comp (c := id) measurable_id ha hf han hb

end DifferentialGeometry.Analysis
