import DifferentialGeometry.Topology.Manifold.Path.Reparametrization
import Mathlib.Analysis.Convex.PathConnected
import Mathlib.Analysis.Calculus.AddTorsor.AffineMap

noncomputable section

open Set
open scoped ContDiff

namespace Path

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem contDiffOn_extend_segment (a b : E) {n : ℕ∞ω} :
    ContDiffOn ℝ n (Path.segment a b).extend (Icc 0 1) :=
  (AffineMap.contDiff_lineMap a b).contDiffOn.congr (Path.eqOn_extend_segment a b)

theorem extend_segment_withSittingInstants (a b : E) :
    (Path.segment a b).withSittingInstants.extend =
      fun t : ℝ => AffineMap.lineMap a b (Real.smoothTransition (3 * t - 1)) := by
  rw [extend_withSittingInstants]
  funext t
  exact Path.eqOn_extend_segment a b
    ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩

end Path
