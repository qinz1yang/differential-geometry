# Residual correction: self-review and compiled consumers

This is an assistant self-review, not independent human/agent approval.
The residual is the actual metric distance to the target. Correction is
required only on the initial residual sublevel, and only at positive residual.
The displacement budget proves containment before completeness is used.
The limiting point has the sharp bound e(q)/mu, including equality.
The openness hypothesis applies at every center and arbitrarily small radii.

The fresh leaf and source-copy declaration lint (unusedArguments, simpNF,
synTaut) pass silently. The pinned environment has no defLemma; all three
source declarations were manually checked to be theorems. The combined gate
passes for 68 modules / 2847 jobs / 584 owned constants, including the generated
recursion helper. All new transitive axiom closures are standard. The inherited
AreaUpperBarrier warning remains outside these new dependencies; no full
migrated root build is claimed. The blueprint static audit passes unchanged.

Four compiled consumers test a genuine midpoint iteration whose solution
is on the complete-ball boundary, zero residual and radius, open-map assembly,
and a local domain O with an ambient complete ball contained in O. The last
consumer explicitly transports completeness to the subtype before applying
the theorem. A globally defined map on the ambient space is not needed.

```lean
import DifferentialGeometry.Topology.MetricSpace.ResidualCorrection

open Set Metric

private theorem midpoint_residual (x y : ℝ) :
    dist ((x + y) / 2) y = dist x y / 2 ∧
      dist x ((x + y) / 2) = dist x y / 2 := by
  constructor
  · rw [Real.dist_eq, Real.dist_eq]
    have h : (x + y) / 2 - y = (x - y) / 2 := by ring
    rw [h, abs_div]
    norm_num
  · rw [Real.dist_eq, Real.dist_eq]
    have h : x - (x + y) / 2 = (x - y) / 2 := by ring
    rw [h, abs_div]
    norm_num

example : ∃ z ∈ closedBall (0 : ℝ) 1, z = 1 ∧ dist 0 z ≤ 1 := by
  have h := exists_preimage_of_local_residual_correction
    (f := fun x : ℝ => x) (q := 0) (y := 1) (r := 1) (μ := 1) (ρ := 1 / 2)
    (by norm_num) (by norm_num) (by norm_num) isClosed_closedBall.isComplete
    continuous_id.continuousOn (by norm_num [Real.dist_eq])
    (fun x _ _ _ => ⟨(x + 1) / 2, by rw [(midpoint_residual x 1).1]; linarith,
      by rw [(midpoint_residual x 1).1, (midpoint_residual x 1).2]; linarith⟩)
  obtain ⟨z, hz, hzy, hd⟩ := h
  exact ⟨z, hz, hzy, by simpa [Real.dist_eq] using hd⟩

example (q : ℝ) : ∃ z ∈ closedBall q 0, z = q ∧ dist q z ≤ 0 := by
  have h := exists_preimage_of_local_residual_correction
    (f := fun x : ℝ => x) (q := q) (y := q) (r := 0) (μ := 1) (ρ := 0)
    (by norm_num) (by norm_num) (by norm_num) isClosed_closedBall.isComplete
    continuous_id.continuousOn (by simp)
    (fun x _ hx hxq => False.elim (by simpa using hx.trans_le hxq))
  obtain ⟨z, hz, hzy, hd⟩ := h
  exact ⟨z, hz, hzy, by simpa only [dist_self, zero_div] using hd⟩

example : IsOpenMap (fun x : ℝ => x) := by
  apply isOpenMap_of_local_residual_correction continuous_id
  intro q ε hε
  refine ⟨ε, 1, 0, hε, le_rfl, by norm_num, by norm_num, by norm_num,
    isClosed_closedBall.isComplete, ?_⟩
  intro y _ x _ _ _
  exact ⟨y, by simp, by simp⟩

example {X Y : Type*} [MetricSpace X] [MetricSpace Y] {O : Set X}
    (q : O) {y : Y} {r μ ρ : ℝ} (f : O → Y)
    (hbuf : closedBall (q : X) r ⊆ O)
    (hμ : 0 < μ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1)
    (hcomplete : IsComplete (closedBall (q : X) r))
    (hf : ContinuousOn f (closedBall q r)) (he : dist (f q) y ≤ μ * r)
    (hs : ∀ x ∈ closedBall q r, 0 < dist (f x) y → dist (f x) y ≤ dist (f q) y →
      ∃ z : O, dist (f z) y ≤ ρ * dist (f x) y ∧
        μ * dist x z ≤ dist (f x) y - dist (f z) y) :
    ∃ z ∈ closedBall q r, f z = y ∧ dist q z ≤ dist (f q) y / μ := by
  have himage : ((↑) : O → X) '' closedBall q r = closedBall (q : X) r := by
    ext x
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact hz
    · intro hx
      exact ⟨⟨x, hbuf hx⟩, hx, rfl⟩
  have hC : IsComplete (closedBall q r) := by
    rw [Subtype.isComplete_iff, himage]
    exact hcomplete
  exact exists_preimage_of_local_residual_correction hμ hρ0 hρ1 hC hf he hs

#print axioms Metric.exists_preimage_of_local_residual_correction
#print axioms Metric.ball_subset_image_ball_of_local_residual_correction
#print axioms Metric.isOpenMap_of_local_residual_correction
```
