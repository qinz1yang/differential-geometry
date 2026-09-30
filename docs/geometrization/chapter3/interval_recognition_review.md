# Interval recognition: self-review and compiled consumers

Assistant self-review, not human or independent-agent mathematical approval.
The two new leaves contain four theorems. All public hypotheses and outputs
were read; the concatenation preserves both entire input maps, the endpoint
equivalence quantifies over all isometric segments, and the chart theorem
preserves the actual space, ambient ball metric and basepoint. Its nontriviality
hypothesis excludes the singleton, which cannot have a positive interval chart.
No completeness or curvature premise is silently introduced. Segment-interior
openness is the explicit unresolved geometric input.

Both source-copy drivers pass `#lint- only unusedArguments simpNF synTaut` silently.
As in the preceding checkpoint, defLemma is unavailable in the pinned environment;
all four new declarations were checked to be theorems. Both leaves compile silently.
The full scoped manifest build covers 65 modules / 2843 jobs; its axiom gate checks
576 owned declarations, accepting only propext, Classical.choice and Quot.sound.
Its unchanged AreaUpperBarrier warning remains outside the new dependency closure.
The inherited full migrated root is not built. Earlier mathematical leaves remain
unchanged. These three consumer examples and all four printed axiom closures pass:

```lean
import DifferentialGeometry.Topology.MetricSpace.IntervalRecognition

open Set Metric

example (x : ℝ) : ∃ σ : Icc (0 : ℝ) (dist x x) → ℝ,
    Isometry σ ∧ σ ⟨0, le_rfl, dist_nonneg⟩ = x := by
  obtain ⟨σ, hσ, h0, _⟩ := exists_isometric_segment_of_dist_eq_mul
    (x := x) (y := x) (f := fun _ => x) rfl rfl (by intro s t; simp)
  exact ⟨σ, hσ, h0⟩

example : ∃ σ : Icc (0 : ℝ) (0 + 2) → ℝ, Isometry σ ∧
    (∀ s : Icc (0 : ℝ) 0, σ ⟨s, s.property.1, by linarith [s.property.2]⟩ = s) ∧
    (∀ t : Icc (0 : ℝ) 2, σ ⟨0 + t, by linarith [t.property.1],
      by linarith [t.property.2]⟩ = t) := by
  exact exists_isometric_segment_concat (X := ℝ) (A := 0) (B := 2)
    (by norm_num) (by norm_num) (α := ((↑) : Icc (0 : ℝ) 0 → ℝ))
    (β := ((↑) : Icc (0 : ℝ) 2 → ℝ)) isometry_subtype_coe isometry_subtype_coe
    rfl (by norm_num [Real.dist_eq])

example {X : Type*} [MetricSpace X]
    (hsegments : ∀ x y : X, ∃ f : Icc (0 : ℝ) 1 → X,
      Continuous f ∧ f ⟨0, by norm_num⟩ = x ∧ f ⟨1, by norm_num⟩ = y ∧
      ∀ s t, dist (f s) (f t) = dist x y * dist s t)
    (p : X) (hn : ∀ (a b : ℝ) (σ : Icc a b → X), Isometry σ →
      ∀ t : Icc a b, a < (t : ℝ) → (t : ℝ) < b → σ t ≠ p)
    (x y : X) (h : dist x p + dist p y = dist x y) : x = p ∨ y = p :=
  (metric_endpoint_iff_not_mem_segment_interior hsegments p).mpr hn x y h

#print axioms Metric.exists_isometric_segment_of_dist_eq_mul
#print axioms Metric.exists_isometric_segment_concat
#print axioms Metric.metric_endpoint_iff_not_mem_segment_interior
#print axioms Metric.exists_pointed_interval_or_half_interval_of_isOpen_segments
```
