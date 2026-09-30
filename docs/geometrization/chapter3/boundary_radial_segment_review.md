# AC62 independent inspection and compiled boundary tests

Two public theorems in one leaf add two owned declarations. The301-module gate
checks1371 owned declarations in3136 jobs; every new transitive closure contains
only propext, Classical.choice and Quot.sound. Source-copy unusedArguments,
simpNF and synTaut lint is silent. The compiled review is silent apart from eight
requested standard axiom reports. Declaration kinds were inspected; defLemma is
unavailable. Earlier math leaves are unchanged. The inherited AreaUpperBarrier
warning remains outside these closures. Static audit passes. No full migrated
root, fresh PDF/Overleaf build or human approval is claimed.

One agent source-checked and implemented the endpoint-limit proof. A different
agent independently inspected its actual hypotheses and proof, then constructed
the concrete driver. Root reread the full proof and ran combined acceptance.
The review checks that all time parameters use ONE ultrafilter below atTop,
that strictly interior times use only their own smaller compact centered balls,
and that the endpoint is supplied by its vanishing remaining-distance bound.
The endpoint is not obtained by assuming a compact closed ball at the full radius.
No completeness is used by the auxiliary; the original theorem uses it explicitly
to obtain smaller compact balls from local compactness of the open ball.

The first compiled case uses complete real-line geometry and actual affine short
curves, obtaining the exact isometric segment from2 to5 on[0,3]. A separate
application covers the auxiliary's degenerate case p=a=0. The stronger test uses
X=(-1,infinity), p=0 and a=1. It explicitly identifies every smaller centered
closed ball with a continuous image of the real compact interval[-r,r], proves
an actual unit-speed short curve to a, and instantiates the auxiliary to produce
the exact endpoint segment. It independently proves X is incomplete and
nonproper. Crucially, it ALSO proves the closed radius-one ball is NOT compact:
its inclusion image is(-1,1], which is not closed in the real line. This rules
out silently strengthening the compactness assumption to the endpoint radius.
All concrete result and negative-control axiom closures are standard.

AC62 is complete. The source curve and target endpoint remain the specified
ones; no global properness or boundary local compactness is introduced. AC63's
numerical first shortening and ALG08's coarse-buffer cross-angle comparison
remain the next independent steps toward AC65. Their final construction must
retain these same radial segments for both angles and coordinate convergence.

```lean
import DifferentialGeometry.Topology.MetricSpace.BoundaryRadialSegment
import Mathlib.Tactic
import Mathlib.Analysis.Normed.Affine.AddTorsor
import DifferentialGeometry.Topology.MetricSpace.SegmentCurves
import DifferentialGeometry.Topology.MetricSpace.LocalHopfRinow
import DifferentialGeometry.Topology.MetricSpace.ShortCurvePrefix
import Mathlib.Analysis.SpecificLimits.Basic

open Set Filter
open scoped Topology

namespace GCAC62Review

open Metric

private theorem real_segments (x y : ℝ) :
    ∃ f : Icc (0 : ℝ) 1 → ℝ,
      Continuous f ∧ f ⟨0, by norm_num⟩ = x ∧ f ⟨1, by norm_num⟩ = y ∧
      ∀ s t, dist (f s) (f t) = dist x y * dist s t := by
  refine ⟨fun t => AffineMap.lineMap x y (t : ℝ), by fun_prop, ?_, ?_, ?_⟩
  · exact AffineMap.lineMap_apply_zero x y
  · exact AffineMap.lineMap_apply_one x y
  · intro s t
    rw [dist_lineMap_lineMap]
    exact mul_comm _ _

private theorem real_curves : ∀ x y : ℝ, ∀ ε : ℝ, 0 < ε →
    ∃ c : unitInterval → ℝ, Continuous c ∧ c 0 = x ∧ c 1 = y ∧
      eVariationOn c univ < ENNReal.ofReal (dist x y + ε) :=
  arbitrarily_short_curves_of_metric_segments real_segments

private theorem real_endpoint :
    ∃ γ : Icc (0 : ℝ) 3 → ℝ, Isometry γ ∧
      γ ⟨0, by norm_num⟩ = 2 ∧ γ ⟨3, by norm_num⟩ = 5 := by
  let : LocallyCompactSpace (ball (2 : ℝ) 3) := isOpen_ball.locallyCompactSpace
  exact exists_isometric_segment_to_boundary_of_locallyCompact_ball real_curves 2
    (by norm_num) (a := 5) (by norm_num [Real.dist_eq])

private theorem degenerate_endpoint :
    ∃ γ : Icc (0 : ℝ) 0 → ℝ, Isometry γ ∧ γ ⟨0, by norm_num⟩ = 0 := by
  have hh := exists_isometric_segment_of_compact_inner_balls
    (p := (0 : ℝ)) (a := 0)
    (fun r hr hr0 => False.elim (by simp only [dist_self] at hr0; linarith))
    (real_curves 0 0)
  obtain ⟨γ, hγ, hstart, hend⟩ := hh
  let incl : Icc (0 : ℝ) 0 → Icc (0 : ℝ) (dist (0 : ℝ) 0) :=
    fun t => ⟨t.val, ⟨t.property.1, by simpa only [dist_self] using t.property.2⟩⟩
  exact ⟨γ ∘ incl, hγ.comp (Isometry.of_dist_eq (fun _ _ => rfl)), hstart⟩

private abbrev HalfLine := Ioi (-1 : ℝ)
private def p : HalfLine := ⟨0, by norm_num⟩
private def a : HalfLine := ⟨1, by norm_num⟩

private theorem endpoint_distance : dist p a = 1 := by norm_num [p, a, Subtype.dist_eq, Real.dist_eq]

private theorem compact_inner_ball (r : ℝ) (_hr : 0 ≤ r) (hrL : r < dist p a) :
    IsCompact (closedBall p r) := by
  rw [endpoint_distance] at hrL
  let lift : Icc (-r) r → HalfLine := fun x => ⟨x.val, by
    change -1 < x.val
    linarith [x.property.1]⟩
  have hlift : Continuous lift := continuous_subtype_val.subtype_mk _
  have hcompact := isCompact_range hlift
  have heq : range lift = closedBall p r := by
    ext x
    constructor
    · rintro ⟨t, rfl⟩
      change |t.val - 0| ≤ r
      rw [sub_zero]
      exact abs_le.mpr t.property
    · intro hx
      change |x.val - 0| ≤ r at hx
      rw [sub_zero] at hx
      exact ⟨⟨x.val, abs_le.mp hx⟩, rfl⟩
  rwa [heq] at hcompact

private def straight : unitInterval → HalfLine := fun t => ⟨t.val, by
  change -1 < t.val
  linarith [t.property.1]⟩

private theorem straight_isometry : Isometry straight := Isometry.of_dist_eq (fun _ _ => rfl)

private theorem endpoint_curves (ε : ℝ) (hε : 0 < ε) :
    ∃ c : unitInterval → HalfLine, Continuous c ∧ c 0 = p ∧ c 1 = a ∧
      eVariationOn c univ < ENNReal.ofReal (dist p a + ε) := by
  refine ⟨straight, straight_isometry.continuous, rfl, rfl, ?_⟩
  have hh : eVariationOn straight univ ≤ (1 : ENNReal) :=
    straight_isometry.lipschitzWith.eVariationOn_unitInterval_le
  apply hh.trans_lt
  rw [endpoint_distance]
  have h := (ENNReal.ofReal_lt_ofReal_iff (by linarith : 0 < 1 + ε)).mpr (by linarith : 1 < 1 + ε)
  simpa only [ENNReal.ofReal_one] using h

private theorem halfLine_endpoint :
    ∃ γ : Icc (0 : ℝ) 1 → HalfLine, Isometry γ ∧
      γ ⟨0, by norm_num⟩ = p ∧ γ ⟨1, by norm_num⟩ = a := by
  have hh := exists_isometric_segment_of_compact_inner_balls compact_inner_ball endpoint_curves
  obtain ⟨γ, hγ, hstart, hend⟩ := hh
  let incl : Icc (0 : ℝ) 1 → Icc (0 : ℝ) (dist p a) :=
    fun t => ⟨t.val, ⟨t.property.1, by rw [endpoint_distance]; exact t.property.2⟩⟩
  refine ⟨γ ∘ incl, hγ.comp (Isometry.of_dist_eq (fun _ _ => rfl)), hstart, ?_⟩
  have hlast : incl ⟨1, by norm_num⟩ = ⟨dist p a, ⟨dist_nonneg, le_rfl⟩⟩ :=
    Subtype.ext endpoint_distance.symm
  change γ (incl ⟨1, by norm_num⟩) = a
  rw [hlast]
  exact hend

private theorem halfLine_not_complete : ¬CompleteSpace HalfLine := by
  intro h
  let : CompleteSpace HalfLine := h
  have hc : IsClosed (Ioi (-1 : ℝ)) := by
    simpa only [Subtype.range_coe] using
      (isometry_subtype_coe (s := Ioi (-1 : ℝ))).isClosedEmbedding.isClosed_range
  have hm : (-1 : ℝ) ∈ closure (Ioi (-1 : ℝ)) := by
    rw [closure_Ioi]
    exact (show (-1 : ℝ) ≤ -1 from le_rfl)
  exact (lt_irrefl (-1 : ℝ)) (hc.closure_subset hm)

private theorem halfLine_not_proper : ¬ProperSpace HalfLine := by
  intro h
  let : ProperSpace HalfLine := h
  exact halfLine_not_complete inferInstance

private theorem halfLine_boundary_ball_not_compact : ¬IsCompact (closedBall p 1) := by
  intro h
  have hc := (h.image (continuous_subtype_val : Continuous (Subtype.val : HalfLine → ℝ))).isClosed
  have heq : Subtype.val '' closedBall p 1 = Ioc (-1 : ℝ) 1 := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      refine ⟨y.property, ?_⟩
      change |y.val - 0| ≤ 1 at hy
      rw [sub_zero] at hy
      exact (abs_le.mp hy).2
    · intro hx
      refine ⟨⟨x, hx.1⟩, ?_, rfl⟩
      change |x - 0| ≤ 1
      rw [sub_zero]
      exact abs_le.mpr ⟨hx.1.le, hx.2⟩
  rw [heq] at hc
  have hm : (-1 : ℝ) ∈ closure (Ioc (-1 : ℝ) 1) := by
    rw [closure_Ioc (by norm_num : (-1 : ℝ) ≠ 1)]
    norm_num
  exact (lt_irrefl (-1 : ℝ)) (hc.closure_subset hm).1

#print axioms real_endpoint
#print axioms degenerate_endpoint
#print axioms halfLine_endpoint
#print axioms halfLine_not_complete
#print axioms halfLine_not_proper
#print axioms halfLine_boundary_ball_not_compact

end GCAC62Review

#print axioms Metric.exists_isometric_segment_of_compact_inner_balls
#print axioms Metric.exists_isometric_segment_to_boundary_of_locallyCompact_ball
```
