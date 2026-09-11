import DifferentialGeometry.Analysis.Calculus.Inverse.SmoothLocalInverse



noncomputable section

open Set Filter Function
open scoped Topology ContDiff

namespace DifferentialGeometry.Analysis

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]




theorem contDiffAt_lift_of_immersion {f : E → F} {s : Set E} {ψ : G → E} {x : G}
    (hs : IsOpen s) (hf : ContDiffOn ℝ ∞ f s) (hx : ψ x ∈ s)
    (hi : Injective (fderiv ℝ f (ψ x))) (hψ : ContinuousAt ψ x)
    (hc : ContDiffAt ℝ ∞ (f ∘ ψ) x) : ContDiffAt ℝ ∞ ψ x := by
  obtain ⟨r, U, V, hU, hxU, hV, hxV, _, hr, hleft, _⟩ :=
    exists_smooth_local_leftInverse hs hf hx hi
  have hrx : ContDiffAt ℝ ∞ r (f (ψ x)) :=
    (hr _ hxU).contDiffAt (hU.mem_nhds hxU)
  apply (hrx.comp x hc).congr_of_eventuallyEq
  filter_upwards [hψ (hV.mem_nhds hxV)] with y hy
  exact (hleft (ψ y) hy).symm

end DifferentialGeometry.Analysis
