# Coordinate correction: self-review and compiled consumers

This is an assistant self-review, not independent human/agent approval.
The arithmetic uses the actual l1 target metric, both signs, and a
positive maximal residual. The single-coordinate case is included.
The move length is exactly the selected residual; summing the other
coordinate errors yields the same displacement budget used by the
complete-buffer theorem. Nonemptiness supplies a real finite maximum,
not a default index. The target is the same supplied point throughout.

Both fresh leaves and source-copy declaration linters (unusedArguments,
simpNF, synTaut) compile silently. The pinned environment has no defLemma;
all six source declarations were manually checked to be theorems. The
combined gate passes for 70 modules / 2849 jobs / 590 owned constants.
All new axiom closures use only propext, Classical.choice and Quot.sound.
The inherited AreaUpperBarrier warning is outside the new dependencies.
No full migrated root build is claimed. Earlier mathematical leaves and
blueprint207 are unchanged.

Five compiled consumers check m=1 and m=2 parameter bounds, both selected
coordinate directions, and actual preimage assembly for the identity on
an l1 plane using explicit one-coordinate moves. That last example includes
initial residual equal to the complete-ball radius. The helper constructs
the witness using Function.update and proves its actual l1 displacement.

```lean
import DifferentialGeometry.Topology.MetricSpace.CoordinateResidual
import Mathlib.Tactic

open Set Metric

example : (9 / 10 : ℝ) ≤ 1 - 3 * (1 / 100 : ℝ) ^ 2 - 6 * (1 - 1) * (1 / 100) := by
  simpa using (paired_correction_constants (m := 1) (by norm_num) (δ := 1 / 100)
    (by norm_num) (by norm_num)).1

example : (0 : ℝ) ≤ 1 - (1 - 3 * (1 / 200 : ℝ) ^ 2 - 6 * (2 - 1) * (1 / 200)) / 2 :=
  (paired_correction_constants (m := 2) (by norm_num) (δ := 1 / 200)
    (by norm_num) (by norm_num)).2.2.1

example : dist (-2 : ℝ) 0 ≤ (1 - (1 / 2 : ℝ)) * dist (-4 : ℝ) 0 := by
  apply Real.dist_le_mul_of_directed_step
  norm_num [Real.dist_eq]

example : dist (2 : ℝ) 0 ≤ (1 - (1 / 2 : ℝ)) * dist (4 : ℝ) 0 := by
  apply Real.dist_le_mul_of_directed_step
  norm_num [Real.dist_eq]

private theorem identity_coordinate_move {ι : Type*} [Fintype ι] [DecidableEq ι]
    (x w : PiLp 1 (fun _ : ι => ℝ)) (i : ι) {t : ℝ} (ht : 0 < t) :
    ∃ y : PiLp 1 (fun _ : ι => ℝ), dist x y = t ∧
      (if w i ≤ x i then 1 * t ≤ x i - y i ∧ x i - y i ≤ t
       else 1 * t ≤ y i - x i ∧ y i - x i ≤ t) ∧
      ∀ j ≠ i, dist (y j) (x j) ≤ 0 * t := by
  let a := if w i ≤ x i then x i - t else x i + t
  let y : PiLp 1 (fun _ : ι => ℝ) := WithLp.toLp 1 (Function.update x.ofLp i a)
  have yi : y i = a := by simp [y]
  have yj (j : ι) (hj : j ≠ i) : y j = x j := by simp [y, hj]
  refine ⟨y, ?_, ?_, ?_⟩
  · rw [PiLp.dist_eq_of_L1]
    calc
      _ = dist (x i) (y i) := Finset.sum_eq_single i (fun j _ hj => by simp [yj j hj])
        (by simp)
      _ = t := by
        rw [yi]
        dsimp [a]
        split_ifs <;> rw [Real.dist_eq] <;> ring_nf <;> simp only [abs_neg, abs_of_pos ht]
  · dsimp [a] at yi
    split_ifs at yi ⊢ with h <;> rw [yi] <;> constructor <;> linarith
  · intro j hj
    simp [yj j hj]

example (q w : PiLp 1 (fun _ : Fin 2 => ℝ)) (r : ℝ) (h : dist q w ≤ r) :
    ∃ z ∈ closedBall q r, z = w ∧ dist q z ≤ dist q w := by
  have hs := exists_preimage_of_coordinate_moves (f := id) (q := q) (w := w)
    (r := r) (t₀ := dist q w) (α := 1) (β := 0)
    (by norm_num) (by norm_num) (by norm_num)
    isClosed_closedBall.isComplete continuous_id.continuousOn (by simpa using h) le_rfl
    (fun x _ i t ht _ _ => identity_coordinate_move x w i ht)
  simpa using hs

#print axioms Real.dist_le_mul_of_directed_step
#print axioms PiLp.dist_le_sub_of_coordinate_correction
#print axioms PiLp.dist_le_mul_of_largest_coordinate_correction
#print axioms Metric.exists_residual_correction_of_coordinate_moves
#print axioms Metric.paired_correction_constants
#print axioms Metric.exists_preimage_of_coordinate_moves
```
