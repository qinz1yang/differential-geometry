# Segment-neighborhood self-review

This is an assistant mathematical/code self-review, not human or independent-agent approval.
Six public theorems and one private helper were inspected. All are theorem declarations.
The source and signature checks retain restricted metrics, actual ball subtypes, the
basepoint equations, arbitrary source radius up to and including endpoint distance,
and nonpositive-radius and degenerate-segment cases in the set equalities.
The half-interval theorem explicitly requires metric endpoint betweenness; it does not
silently derive this from the dimension bound. Local injectivity/openness are supplied
inputs; this is not the full recognition theorem.

The source-copy driver compiled silently with `#lint- only unusedArguments simpNF synTaut`.
The installed Batteries/Mathlib no longer exposes `defLemma` (the attempted four-linter
command was rejected); all seven owned declarations were directly checked to be theorems.
No linter or diagnostic suppression was added. The standalone leaf compiled silently.
The combined 63-module gate passes with 572 standard-axiom-only declarations; its unchanged
AreaUpperBarrier dependency emits the inherited admission warning. That warning is outside
the accepted new leaf's dependency closure. No full migrated-root build is claimed.

The following three consumer examples compile. The real-line case uses a center with
unequal distances to the supplied endpoints and radius equal to the nearer endpoint
distance; the second checks zero radius; the third checks the exact endpoint radius
and the consumer-visible basepoint equation. The final commands print all six public
axiom closures; the combined gate also checks the private helper.

```lean
import DifferentialGeometry.Topology.MetricSpace.SegmentNeighborhood

open Set Metric

private theorem real_segments (x y : ℝ) :
    ∃ f : Icc (0 : ℝ) 1 → ℝ,
      Continuous f ∧ f ⟨0, by norm_num⟩ = x ∧ f ⟨1, by norm_num⟩ = y ∧
      ∀ s t, dist (f s) (f t) = dist x y * dist s t := by
  refine ⟨fun t => x + t * (y - x),
    continuous_const.add (continuous_subtype_val.mul continuous_const), ?_, ?_, ?_⟩
  · simp
  · simp
  · intro s t
    change |(x + (s : ℝ) * (y - x)) - (x + (t : ℝ) * (y - x))| =
      |x - y| * |(s : ℝ) - t|
    calc
      _ = |(x - y) * ((t : ℝ) - s)| := congrArg abs (by ring)
      _ = _ := by rw [abs_mul, abs_sub_comm (t : ℝ) s]

private theorem real_segment_open (a b : ℝ) :
    IsOpen (((↑) : Icc a b → ℝ) '' {t | a < (t : ℝ) ∧ (t : ℝ) < b}) := by
  have heq : ((↑) : Icc a b → ℝ) '' {t | a < (t : ℝ) ∧ (t : ℝ) < b} = Ioo a b := by
    ext x
    constructor
    · rintro ⟨t, ht, rfl⟩
      exact ht
    · intro hx
      exact ⟨⟨x, hx.1.le, hx.2.le⟩, hx, rfl⟩
  rw [heq]
  exact isOpen_Ioo

example : ∃ e : Ioo (-2 : ℝ) 2 ≃ᵢ ball (0 : ℝ) 2,
    (e ⟨0, by norm_num⟩ : ℝ) = 0 := by
  exact exists_pointed_interval_isometry_of_isOpen_segment real_segments
    (isometry_subtype_coe (s := Icc (-2 : ℝ) 3)) (real_segment_open (-2) 3)
    ⟨0, by norm_num⟩ (by norm_num) (by norm_num)

example : ball (0 : ℝ) 0 =
    ((↑) : Icc (-2 : ℝ) 3 → ℝ) '' {t | dist t (⟨0, by norm_num⟩ : Icc (-2 : ℝ) 3) < 0} := by
  exact ball_eq_segment_image_of_isOpen real_segments isometry_subtype_coe
    (real_segment_open (-2) 3) ⟨0, by norm_num⟩ (by norm_num)

example {X : Type*} [MetricSpace X]
    (hsegments : ∀ x y : X, ∃ f : Icc (0 : ℝ) 1 → X,
      Continuous f ∧ f ⟨0, by norm_num⟩ = x ∧ f ⟨1, by norm_num⟩ = y ∧
      ∀ s t, dist (f s) (f t) = dist x y * dist s t)
    {D : ℝ} (hD : 0 < D) (σ : Icc (0 : ℝ) D → X) (hσ : Isometry σ)
    (ho : IsOpen (σ '' {t | 0 < (t : ℝ) ∧ (t : ℝ) < D}))
    (hend : ∀ x y : X, dist x (σ ⟨0, le_rfl, hD.le⟩) +
      dist (σ ⟨0, le_rfl, hD.le⟩) y = dist x y →
      x = σ ⟨0, le_rfl, hD.le⟩ ∨ y = σ ⟨0, le_rfl, hD.le⟩) :
    ∃ e : Ico (0 : ℝ) D ≃ᵢ ball (σ ⟨0, le_rfl, hD.le⟩) D,
      (e ⟨0, le_rfl, hD⟩ : X) = σ ⟨0, le_rfl, hD.le⟩ :=
  exists_pointed_half_interval_isometry_of_isOpen_segment hsegments hD.le hσ ho hend hD le_rfl

#print axioms Metric.ball_eq_segment_image_of_injOn_dist
#print axioms Metric.isOpen_segment_image_of_locally_injOn_dist
#print axioms Metric.ball_eq_segment_image_of_isOpen
#print axioms Metric.ball_eq_segment_image_at_endpoint_of_isOpen
#print axioms Metric.exists_pointed_interval_isometry_of_isOpen_segment
#print axioms Metric.exists_pointed_half_interval_isometry_of_isOpen_segment
```
