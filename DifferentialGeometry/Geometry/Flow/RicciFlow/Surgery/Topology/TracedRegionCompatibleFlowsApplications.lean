import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TracedRegionCompatibleFlows
import DifferentialGeometry.Geometry.Flow.RicciFlow.Solution.Restriction

/-!
# Consumer of A12: the common-depth statement of the first design

The first design stated A12 with one depth `τ` and one bound `K` for all radii.  It is the
special case `τ k = τ`, `K k = K` of the errata form: all left ends `a k` equal `t - τ`, the flows
are re-read on the common window `[t - τ, t]` (`SolutionOn.timeRestrict` keeps the metric family),
and `max (a k) (a l) = t - τ`.
-/

set_option autoImplicit false

noncomputable section

open Set TopologicalSpace
open scoped Manifold ContDiff

namespace FILL910

universe u

open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.Tensor0SBundle

/-- The common-depth A12 of the first design (interface text), from the errata form. -/
theorem A12_compatible_common_flows_of_common_depth (H : ObservedHistory.{u})
    (t : Icc (0 : ℝ) H.horizon) (p : (H.stageAt t).Carrier) (ρ : ℕ → ℝ) {τ K : ℝ}
    (h : ∀ k, H.isTracedRegion t p (ρ k) τ K) :
    ∃ (a : Icc (0 : ℝ) H.horizon) (hat : a ≤ t), a.val = t.val - τ ∧
      ∃ (U : ℕ → TopologicalSpace.Opens (H.stageAt t).Carrier)
        (S : ∀ k, SolutionOn (I := ThreeModel) (M := U k)
          (RealTimeInterval.closed a.val t.val hat)),
        (∀ k, (U k : Set (H.stageAt t).Carrier) =
          riemannianBallOf (H.stageMetric (H.activeStage t) t) p (ρ k)) ∧
        (∀ k, IsSolutionOn (S k)) ∧
        (∀ k, ∀ v ∈ Icc a.val t.val, v ∈ H.stageDomain (H.activeStage t) →
          (S k).base.metric v = (H.stageMetric (H.activeStage t) v).restrictOpen (U k)) ∧
        (∀ k, ∀ v ∈ Icc a.val t.val, ∀ x : U k,
          normSq0S ((S k).base.metric v) x 4 ((S k).base.rm04 v x) ≤ K ^ 2) ∧
        ∀ k l, ∀ v ∈ Icc a.val t.val,
          ((S k).base.metric v).restrictOpenOfSubset (inf_le_left : U k ⊓ U l ≤ U k) =
            ((S l).base.metric v).restrictOpenOfSubset (inf_le_right : U k ⊓ U l ≤ U l) := by
  obtain ⟨a, hat, ha, U, S, hU, hS, hcurrent, hRm, hcompat⟩ :=
    A12_compatible_common_flows H t p ρ (fun _ => τ) (fun _ => K) h
  have hval : ∀ k, (a k).val = (a 0).val := fun k => by rw [ha k, ha 0]
  have hwin : ∀ k, Icc (a 0).val t.val = Icc (a k).val t.val := fun k => by rw [hval k]
  refine ⟨a 0, hat 0, ha 0, U,
    fun k => (S k).timeRestrict (RealTimeInterval.closed (a 0).val t.val (hat 0)),
    hU, fun k => ?_, fun k v hv => ?_, fun k v hv => ?_, fun k l v hv => ?_⟩
  · refine isSolutionOn_timeRestrict (hS k) ?_ ?_
    · change Icc (a 0).val t.val ⊆ Icc (a k).val t.val
      rw [hwin k]
    · change Ioo (a 0).val t.val ⊆ Ioo (a k).val t.val
      rw [hval k]
  · rw [hwin k] at hv
    exact hcurrent k v hv
  · rw [hwin k] at hv
    exact hRm k v hv
  · have hmax : max (a k).val (a l).val = (a 0).val := by rw [hval k, hval l, max_self]
    exact hcompat k l v (by rw [hmax]; exact hv)

end FILL910
