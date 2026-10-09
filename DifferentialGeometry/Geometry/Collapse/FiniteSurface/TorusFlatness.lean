import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.OpenPos

/-!
# LFR17 kernel: the torus clause

Blueprint LFR17 (master207A:26204), last paragraph of the proof: "a continuous nonnegative function
with zero integral against a positive Riemannian density vanishes everywhere". Applied to the
Gaussian curvature of the `C²` metric on a torus (whose total curvature is `2πχ(T²) = 0` by
Gauss–Bonnet), it gives `κ ≡ 0`. A Riemannian area measure is positive on nonempty open sets, which
is the only property used.

The rest of LFR17 (smooth Gauss–Bonnet on closed surfaces and the smooth classification of closed
orientable surfaces) is not in the tree; see `build-logs/resume/sheet-W4-F7c.md`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory

namespace DifferentialGeometry.Geometry.Collapse

/-- **LFR17, torus clause (kernel).** A continuous nonnegative integrable function with zero
integral against a measure that is positive on nonempty open sets vanishes everywhere. -/
theorem eq_zero_of_integral_eq_zero_of_continuous_nonneg {X : Type*} [TopologicalSpace X]
    [MeasurableSpace X] (μ : Measure X) [μ.IsOpenPosMeasure]
    {f : X → ℝ} (hf : Continuous f) (hnn : ∀ x, 0 ≤ f x) (hint : Integrable f μ)
    (h0 : ∫ x, f x ∂μ = 0) : f = 0 :=
  (hf.ae_eq_iff_eq μ continuous_const).mp
    ((integral_eq_zero_iff_of_nonneg (fun x => hnn x) hint).mp h0)

end DifferentialGeometry.Geometry.Collapse
