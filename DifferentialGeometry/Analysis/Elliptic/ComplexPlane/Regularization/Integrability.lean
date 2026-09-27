import DifferentialGeometry.Analysis.Elliptic.ComplexPlane.Regularization.Limit



noncomputable section

open MeasureTheory Filter

namespace DifferentialGeometry.Analysis



theorem integrable_regularizedConformalWeight_comp_mul
    {X : Type*} [MeasurableSpace X] {μ : Measure X} {c : X → ℂ} {a f : ℂ → ℝ} {b : X → ℝ}
    (hc : Measurable c) (ha : Measurable a) (hf : Measurable f)
    (han : ∀ᵐ z ∂μ, 0 ≤ a (c z)) (hb : Integrable b μ) (ε : ℝ) :
    Integrable (fun z => regularizedConformalWeight a f ε (c z) * b z) μ := by
  have hw : Measurable (regularizedConformalWeight a f ε) :=
    ha.div (ha.add (measurable_const.mul ((measurable_const.mul hf).exp)))
  apply hb.norm.mono' ((hw.comp hc).aestronglyMeasurable.mul hb.aestronglyMeasurable)
  filter_upwards [han] with z hz
  have hbound := regularizedConformalWeight_mem_Icc_all (f := f) hz ε
  change ‖regularizedConformalWeight a f ε (c z) * b z‖ ≤ ‖b z‖
  rw [norm_mul, Real.norm_of_nonneg hbound.1]
  exact mul_le_of_le_one_left (norm_nonneg _) hbound.2

end DifferentialGeometry.Analysis
