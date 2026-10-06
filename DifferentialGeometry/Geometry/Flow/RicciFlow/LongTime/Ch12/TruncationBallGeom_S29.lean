import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.CuspThickDistanceMain_S26
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.TruncationLevelCollar
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Contract.NoncollapseLocalization

set_option autoImplicit false
noncomputable section
open Set Function Manifold DifferentialGeometry DifferentialGeometry.Geometry
  DifferentialGeometry.Geometry.Hyperbolic GC.Endpoint DifferentialGeometry.Topology.Manifold
open scoped Manifold ContDiff ENNReal
universe u
namespace GC.LongTime.Ch12

variable {H : FiniteVolumeHyperbolicModel.{u}} (T : HyperbolicTruncation H)

/-- The truncation level used at ball scale `n`. -/
def levelOf_S29 (A n : ℝ) : ℝ := n / 2 + A + 1

/-- The basepoint lies below some cusp height in every cusp. -/
theorem exists_basepoint_height_S29 (x : H.Carrier) :
    ∃ a : ℝ, 0 ≤ a ∧ ∀ i, x ∉ T.cuspMap i '' {q : CuspHalfSpace | a < q.2.val 0} := by
  by_cases hc : x ∈ range T.inclusion
  · refine ⟨0, le_rfl, fun i ⟨q, hq, hqx⟩ => ?_⟩
    have hx : x ∈ range T.inclusion ∩ range (T.cuspMap i) := ⟨hc, q, hqx⟩
    rw [T.intersection i] at hx
    obtain ⟨θ, hθ⟩ := hx
    have := injective_cuspMap_S26 T i (hθ.trans hqx.symm)
    have h0 : q.2.val 0 = 0 := by rw [← this]; simp [halfZero, halfPoint]
    exact absurd hq (by simp [h0])
  · have hx : x ∈ ⋃ i, range (T.cuspMap i) := by
      have := T.exhausts ▸ mem_univ x
      exact this.resolve_left hc
    obtain ⟨i0, q0, hq0⟩ := mem_iUnion.mp hx
    refine ⟨max 0 (q0.2.val 0), le_max_left _ _, fun i ⟨q, hq, hqx⟩ => ?_⟩
    by_cases hi : i = i0
    · subst hi
      have := injective_cuspMap_S26 T i (hqx.trans hq0.symm)
      subst this
      exact absurd (show max 0 (q.2.val 0) < q.2.val 0 from hq) (not_lt.mpr (le_max_right _ _))
    · have hd := T.cusp_disjoint hi
      exact (Set.disjoint_left.mp hd) ⟨q, hqx⟩ ⟨q0, hq0⟩ |>.elim

end GC.LongTime.Ch12
