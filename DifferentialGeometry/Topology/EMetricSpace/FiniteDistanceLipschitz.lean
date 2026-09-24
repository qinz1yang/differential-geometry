import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Data.ENNReal.Real
import Mathlib.Data.ENNReal.Operations
import Mathlib.Algebra.Order.Group.MinMax
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

section

set_option autoImplicit false

open scoped ENNReal NNReal

namespace EMetric

variable {X : Type*} [PseudoEMetricSpace X]

theorem abs_toReal_edist_sub_le_of_edist_ne_top
    {x y p : X} (hxp : edist x p ≠ ⊤) (hyp : edist y p ≠ ⊤) :
    |(edist x p).toReal - (edist y p).toReal| ≤ (edist x y).toReal := by
  have hxy : edist x y ≠ ⊤ :=
    ne_top_of_le_ne_top (ENNReal.add_ne_top.mpr
      ⟨hxp, by simpa only [edist_comm p y] using hyp⟩) (edist_triangle x p y)
  have hfirst := ENNReal.toReal_le_add (edist_triangle x y p) hxy hyp
  have hsecond := ENNReal.toReal_le_add (edist_triangle y x p)
    (by simpa only [edist_comm y x] using hxy) hxp
  rw [edist_comm y x] at hsecond
  exact abs_sub_le_iff.mpr ⟨by linarith, by linarith⟩

theorem ofReal_abs_toReal_edist_sub_le_of_edist_ne_top
    {x y p : X} (hxp : edist x p ≠ ⊤) (hyp : edist y p ≠ ⊤) :
    ENNReal.ofReal |(edist x p).toReal - (edist y p).toReal| ≤ edist x y :=
  (ENNReal.ofReal_le_ofReal
    (abs_toReal_edist_sub_le_of_edist_ne_top hxp hyp)).trans ENNReal.ofReal_toReal_le

theorem ofReal_abs_toReal_edist_excess_sub_le_of_edist_ne_top
    {x y p : X} (hxp : edist x p ≠ ⊤) (hyp : edist y p ≠ ⊤) (R : ℝ) :
    ENNReal.ofReal |max ((edist x p).toReal - R) 0 -
      max ((edist y p).toReal - R) 0| ≤ edist x y := by
  have hmax := abs_max_sub_max_le_abs ((edist x p).toReal - R)
    ((edist y p).toReal - R) 0
  have heq : ((edist x p).toReal - R) - ((edist y p).toReal - R) =
      (edist x p).toReal - (edist y p).toReal := by ring
  rw [heq] at hmax
  exact (ENNReal.ofReal_le_ofReal hmax).trans
    (ofReal_abs_toReal_edist_sub_le_of_edist_ne_top hxp hyp)

theorem lipschitzWith_toReal_edist_comp
    {Z : Type*} [PseudoEMetricSpace Z] {U : Z → X} {L : ℝ≥0}
    (hU : LipschitzWith L U) (p : X) (hfin : ∀ z, edist (U z) p ≠ ⊤) :
    LipschitzWith L (fun z => (edist (U z) p).toReal) := by
  intro z w
  rw [edist_dist, Real.dist_eq]
  exact (ofReal_abs_toReal_edist_sub_le_of_edist_ne_top (hfin z) (hfin w)).trans
    (hU z w)

theorem lipschitzWith_toReal_edist_excess_comp
    {Z : Type*} [PseudoEMetricSpace Z] {U : Z → X} {L : ℝ≥0}
    (hU : LipschitzWith L U) (p : X) (hfin : ∀ z, edist (U z) p ≠ ⊤) (R : ℝ) :
    LipschitzWith L (fun z => max ((edist (U z) p).toReal - R) 0) := by
  intro z w
  rw [edist_dist, Real.dist_eq]
  exact (ofReal_abs_toReal_edist_excess_sub_le_of_edist_ne_top
    (hfin z) (hfin w) R).trans (hU z w)

end EMetric


end
