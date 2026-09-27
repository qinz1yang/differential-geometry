import DifferentialGeometry.Analysis.Elliptic.ComplexPlane.Regularization.Integrability



noncomputable section

open MeasureTheory Filter
open scoped Topology

namespace DifferentialGeometry.Analysis



theorem tendsto_integral_regularizedConformalWeight_comp_of_zero
    {X : Type*} [MeasurableSpace X] {μ : Measure X} {c : X → ℂ} {a f : ℂ → ℝ} {b : X → ℝ}
    (hc : Measurable c) (ha : Measurable a) (hf : Measurable f)
    (han : ∀ᵐ z ∂μ, 0 ≤ a (c z)) (hb : Integrable b μ)
    (hzero : ∀ᵐ z ∂μ, a (c z) = 0 → b z = 0) :
    Tendsto (fun ε : ℝ => ∫ z, regularizedConformalWeight a f ε (c z) * b z ∂μ) (𝓝 0)
      (𝓝 (∫ z, b z ∂μ)) := by
  have h := tendsto_integral_regularizedConformalWeight_comp hc ha hf han hb
  have heq : (fun z => if a (c z) = 0 then 0 else b z) =ᵐ[μ] b := by
    filter_upwards [hzero] with z hz
    split_ifs with hza
    · exact (hz hza).symm
    · rfl
  rwa [integral_congr_ae heq] at h




theorem tendsto_integral_one_sub_regularizedConformalWeight_comp
    {X : Type*} [MeasurableSpace X] {μ : Measure X} {c : X → ℂ} {a f : ℂ → ℝ} {b : X → ℝ}
    (hc : Measurable c) (ha : Measurable a) (hf : Measurable f)
    (han : ∀ᵐ z ∂μ, 0 ≤ a (c z)) (hb : Integrable b μ)
    (hzero : ∀ᵐ z ∂μ, a (c z) = 0 → b z = 0) :
    Tendsto (fun ε : ℝ => ∫ z, (1 - regularizedConformalWeight a f ε (c z)) * b z ∂μ) (𝓝 0)
      (𝓝 0) := by
  have h := tendsto_integral_regularizedConformalWeight_comp_of_zero hc ha hf han hb hzero
  have heq (ε : ℝ) : (∫ z, (1 - regularizedConformalWeight a f ε (c z)) * b z ∂μ) =
      (∫ z, b z ∂μ) - ∫ z, regularizedConformalWeight a f ε (c z) * b z ∂μ := by
    rw [← integral_sub hb (integrable_regularizedConformalWeight_comp_mul hc ha hf han hb ε)]
    apply integral_congr_ae
    filter_upwards [] with z
    ring
  simp_rw [heq]
  simpa only [sub_self] using
    (tendsto_const_nhds : Tendsto (fun _ : ℝ => ∫ z, b z ∂μ) (𝓝 0) (𝓝 (∫ z, b z ∂μ))).sub h

end DifferentialGeometry.Analysis
