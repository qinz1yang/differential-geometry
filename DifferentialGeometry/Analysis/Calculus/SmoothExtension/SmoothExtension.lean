import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Topology.Separation.Basic

open Set Filter Topology
open scoped ContDiff

namespace DifferentialGeometry.Analysis

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem contDiff_update_of_eventuallyEq [DecidableEq E] {n : ℕ∞ω} (B C : E → F) (p : E)
    (hB : ∀ x, x ≠ p → ContDiffAt ℝ n B x)
    (hC : ContDiffAt ℝ n C p)
    (hmatch : B =ᶠ[𝓝[≠] p] C) :
    ContDiff ℝ n (Function.update B p (C p)) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x = p
  · subst x
    apply hC.congr_of_eventuallyEq
    exact eventuallyEq_nhds_of_eventuallyEq_nhdsNE
      ((Function.update_eventuallyEq_nhdsNE B p p (C p)).trans hmatch)
      (Function.update_self _ _ _)
  · apply (hB x hx).congr_of_eventuallyEq
    filter_upwards [isOpen_compl_singleton.mem_nhds hx] with y hy
    exact Function.update_of_ne hy _ _

end DifferentialGeometry.Analysis
