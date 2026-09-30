# Compiled self-review: complete-ball almost minimum

The new theorem passes the 150-module/834-owned-declaration gate. Its
transitive closure uses only propext, Classical.choice and Quot.sound.
Source-copy unusedArguments, simpNF and synTaut linters are silent;
defLemma is unavailable and the declaration kind was inspected manually.
Earlier mathematical leaves are unchanged. The inherited AreaUpperBarrier
warning is outside the new closure. Static audit passes. No migrated
full-root, PDF or Overleaf build is claimed.

The first compiled example uses r(0)=2 and r(x)=1 for x!=0, a discontinuous
positive function. At epsilon=1/2 the selected point is proved NONZERO:
the original point fails the strict relative lower bound. Thus the example
requires genuine point selection and does not insert an assumed witness.
The second constructs the complete closed radius-four ball inside the
incomplete open interval (-10,10) as a closed subset of an actual compact
interval image, then applies the theorem there. Ambient completeness is
not supplied. The general conclusion quantifies over every ambient q;
it retains the non-strict distance threshold and strict function inequality.
No continuity of r or compactness of the complete ball is used in the
general proof. The distance-plus-radius budget maintains the complete
buffer before any Cauchy-limit argument is invoked. This is self-review,
not human approval or completion of the globalization suite.

```lean
import DifferentialGeometry.Topology.MetricSpace.AlmostMinimum
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic

open Set Filter Topology Metric

noncomputable def spikedRadius (x : ℝ) : ℝ := if x = 0 then 2 else 1

private theorem spiked_lower (x : ℝ) : 1 ≤ spikedRadius x := by
  unfold spikedRadius
  split <;> norm_num

example : ∃ p ∈ closedBall (0 : ℝ) 8, p ≠ 0 ∧ spikedRadius p ≤ 2 ∧
    ∀ q : ℝ, dist p q ≤ 2 * spikedRadius p → spikedRadius p / 2 < spikedRadius q := by
  obtain ⟨p, hp, hr, hq⟩ := exists_relative_almost_minimum_of_complete_closedBall
    (o := (0 : ℝ)) (r := spikedRadius) (ε := (1 : ℝ) / 2)
    (by norm_num) (by norm_num) (fun x => lt_of_lt_of_le zero_lt_one (spiked_lower x))
    isClosed_closedBall.isComplete (fun _ _ => ⟨1, zero_lt_one, Eventually.of_forall spiked_lower⟩)
  have hpne : p ≠ 0 := by
    intro heq
    subst p
    have h := hq 1 (by norm_num [spikedRadius, Real.dist_eq])
    norm_num [spikedRadius] at h
  refine ⟨p, ?_, hpne, ?_, ?_⟩
  · norm_num [spikedRadius] at hp ⊢
    exact hp
  · simpa [spikedRadius] using hr
  · intro q hdist
    have h := hq q (by convert hdist using 1; ring)
    convert h using 1; ring

example : ∃ p : Ioo (-10 : ℝ) 10,
    p ∈ closedBall (⟨0, by norm_num⟩ : Ioo (-10 : ℝ) 10) 4 ∧
    ∀ q : Ioo (-10 : ℝ) 10, dist p q ≤ 2 → (1 : ℝ) / 2 < 1 := by
  let o : Ioo (-10 : ℝ) 10 := ⟨0, by norm_num⟩
  let f : Icc (-4 : ℝ) 4 → Ioo (-10 : ℝ) 10 := fun x =>
    ⟨x, by constructor <;> linarith [x.property.1, x.property.2]⟩
  have hf : Continuous f := by fun_prop
  have hc : IsCompact (closedBall o 4) :=
    (isCompact_range hf).of_isClosed_subset isClosed_closedBall (by
      intro x hx
      change |(x : ℝ) - 0| ≤ 4 at hx
      rw [sub_zero, abs_le] at hx
      exact ⟨⟨x, hx⟩, by apply Subtype.ext; rfl⟩)
  obtain ⟨p, hp, _, hq⟩ := exists_relative_almost_minimum_of_complete_closedBall
    (o := o) (r := fun _ => (1 : ℝ)) (ε := (1 : ℝ) / 2)
    (by norm_num) (by norm_num) (fun _ => zero_lt_one)
    (by convert hc.isComplete using 1; norm_num)
    (fun _ _ => ⟨1, zero_lt_one, Eventually.of_forall (fun _ => le_rfl)⟩)
  refine ⟨p, ?_, ?_⟩
  · norm_num at hp
    exact hp
  · intro q hdist
    have h := hq q (by norm_num; exact hdist)
    norm_num at h ⊢

#print axioms Metric.exists_relative_almost_minimum_of_complete_closedBall

```
