# Final review: local Hopf--Rinow and the ALG05 metric input

This is a second-pass self-review, not an independent-agent review. The
complete two-file implementation was reread against the exact statements
and proof passages recorded in `local_hopf_rinow.md`. No mathematical
contract mismatch was found. The review retains the following boundaries:

- AC01 requires local compactness only on the open buffer, not globally.
- Completeness is needed only for the surrounding closed buffer.
- All distance and variation statements use the ambient metric.
- Compactness is proved at strictly smaller radii, not at the buffer boundary.
- The closed-ball result needs `2*r<L`; the strict open-ball result uses
  endpoints strictly inside the smaller ball.
- Exact segment production never assumes a restricted ball is a length space.
- The radial selections on approximating curves are neither assumed
  continuous nor assumed to preserve order. The three-piece variation
  estimate handles both orders; one common ultrafilter preserves all
  pairwise estimates in the limit.
- No division by the endpoint distance or the inner radius occurs, so the
  coincident-endpoint and zero-radius cases remain valid.
- The output is an ambient minimizing segment, not a claim of uniqueness
  or extension of arbitrary locally minimizing geodesics.
- The ALG05 application supplies new joins at the shifted center with the
  exact `17/16`, `16`, and `20` radius arithmetic from the blueprint. The
  point and scale themselves are still inputs from the unproved selection
  and comparison part of ALG05.

The following block is also an executable review: feed it to
`lake env lean --stdin` in this isolated checkout. It checks the elaborated
signatures, a fixed compact singleton with coincident endpoints in an
arbitrary ambient metric space, the zero-radius local application, and the
actual shifted-center radius application in an ambient space that is not
assumed complete. Its successful output is retained in
`evidence/local_hopf_rinow_review.log`.

```lean
import DifferentialGeometry.Topology.MetricSpace.LocalHopfRinow

set_option autoImplicit false
open Set Metric

#check @Metric.isCompact_closedBall_of_complete_buffer
#check @Metric.isCompact_closedBall_of_locallyCompact_ball
#check @Metric.exists_metric_segment_of_compact_arbitrarily_short_curves
#check @Metric.exists_metric_segment_in_closedBall_of_complete_buffer
#check @Metric.exists_metric_segment_in_closedBall_of_locallyCompact_ball
#check @Metric.exists_metric_segment_in_ball_of_complete_buffer
#check @Metric.exists_metric_segment_in_ball_of_recentered_complete_buffer

example {X : Type*} [MetricSpace X] (a : X) :
    ∃ f : unitInterval → X, Continuous f ∧ f 0 = a ∧ f 1 = a ∧
      (∀ t, f t ∈ ({a} : Set X)) ∧
      ∀ s t, dist (f s) (f t) = dist a a * dist s t := by
  apply Metric.exists_metric_segment_of_compact_arbitrarily_short_curves isCompact_singleton
  intro ε hε
  refine ⟨fun _ => a, continuous_const, rfl, rfl, fun _ => rfl, ?_⟩
  have hzero : eVariationOn (fun _ : unitInterval => a) univ = 0 :=
    eVariationOn.constant_on (by simp)
  simpa [hzero] using (ENNReal.ofReal_pos.mpr hε)

example {X : Type*} [MetricSpace X]
    (hcurves : ∀ a b : X, ∀ ε : ℝ, 0 < ε →
      ∃ c : unitInterval → X, Continuous c ∧ c 0 = a ∧ c 1 = b ∧
        eVariationOn c univ < ENNReal.ofReal (dist a b + ε))
    (p : X) {L : ℝ} (hL : 0 < L) [LocallyCompactSpace (ball p L)]
    (hcomplete : IsComplete (closedBall p L)) :
    ∃ f : unitInterval → X, Continuous f ∧ f 0 = p ∧ f 1 = p ∧ ∀ t, f t = p := by
  obtain ⟨f, hf, hf0, hf1, hmem, _⟩ :=
    Metric.exists_metric_segment_in_closedBall_of_complete_buffer hcurves p hcomplete
      (r := 0) (a := p) (b := p) (by simpa using hL) (by simp) (by simp)
  refine ⟨f, hf, hf0, hf1, ?_⟩
  intro t
  simpa using hmem t

example {X : Type*} [MetricSpace X] [LocallyCompactSpace X]
    (hcurves : ∀ a b : X, ∀ ε : ℝ, 0 < ε →
      ∃ c : unitInterval → X, Continuous c ∧ c 0 = a ∧ c 1 = b ∧
        eVariationOn c univ < ENNReal.ofReal (dist a b + ε))
    {o p : X} {L r₀ r : ℝ} (hr : 0 < r) (hrr₀ : r ≤ r₀)
    (hr₀L : r₀ < L / 20) (hshift : dist o p ≤ 16 * r₀)
    (hcomplete : IsComplete (closedBall o L))
    {a b : X} (ha : a ∈ ball p (17 * r / 16)) (hb : b ∈ ball p (17 * r / 16)) :
    ∃ f : unitInterval → X, Continuous f ∧ f 0 = a ∧ f 1 = b ∧
      (∀ t, f t ∈ ball p (2 * (17 * r / 16))) ∧
      ∀ s t, dist (f s) (f t) = dist a b * dist s t := by
  apply Metric.exists_metric_segment_in_ball_of_recentered_complete_buffer hcurves
    (by positivity) hcomplete ?_ ha hb
  rw [dist_comm p o]
  linarith

#eval "LOCAL_HOPF_RINOW_REVIEW_PASS"
```

The combined build and all-declaration axiom audit passed before this review:
42 manifest modules, 2730 Lake jobs, and 443 owned kernel-checked declarations.
The two new modules account for 10 public theorems and 7 private lemmas.
Their axiom dependencies, including transitive project imports, contain
only `propext`, `Classical.choice`, and `Quot.sound`. Existing mathematical
files, including earlier development leaves on this branch, were preserved.

The full PC root and full ALG05 theorem were not checked or claimed proved.
The separate blueprint static audit still stops on the unchanged historical
archive path, as recorded in `evidence/blueprint_static_local_hopf_rinow.log`.
