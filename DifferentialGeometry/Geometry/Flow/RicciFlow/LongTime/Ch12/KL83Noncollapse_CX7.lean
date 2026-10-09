import DifferentialGeometry.Topology.MetricSpace.PositiveHausdorffCover
import DifferentialGeometry.Geometry.Metric.Approximation.PointedConvergence
import Mathlib.Topology.MetricSpace.HausdorffDimension

/-!
# CH12-CX7: noncollapse prevents a low-dimensional pointed limit

A positive volume on the radius-two source balls and a uniform cubic upper bound
on small balls imply `2 < dimH` of a proper pointed GH limit. The proof uses only
finite covers, so it does not assume measure convergence.
-/

set_option autoImplicit false

noncomputable section

open Set Metric Filter MeasureTheory
open scoped ENNReal NNReal Topology
open GC.MetricGeometry

namespace GC.LongTime.Ch12

/-- A positive common error smaller than finitely many positive radii. -/
theorem finite_positive_error_CX7 (F : Finset ℕ) (r : ℕ → ℝ)
    (hr : ∀ j, 0 < r j) : ∃ ε : ℝ, 0 < ε ∧ ε < 1 / 4 ∧ ∀ j ∈ F, ε < r j := by
  classical
  induction F using Finset.induction_on with
  | empty => exact ⟨1 / 8, by norm_num, by norm_num, by simp⟩
  | @insert j F hj ih =>
    obtain ⟨ε, hε, hε1, hεF⟩ := ih
    have hrj := hr j
    refine ⟨min ε (r j / 2), by positivity, (min_le_left _ _).trans_lt hε1, ?_⟩
    intro k hk
    rcases Finset.mem_insert.mp hk with rfl | hk
    · exact (min_le_right _ _).trans_lt (by linarith [hr k])
    · exact (min_le_left _ _).trans_lt (hεF k hk)

/-- Noncollapse plus local cubic measure bounds rules out Hausdorff dimension at most two.
The constants are uniform over all source points within distance four of the basepoint. -/
theorem dimH_gt_two_of_noncollapsed_CX7
    {X : ℕ → Type*} [∀ i, MetricSpace (X i)] [∀ i, MeasurableSpace (X i)]
    {Y : Type*} [MetricSpace Y] [ProperSpace Y]
    {p : ∀ i, X i} {q : Y} (hconv : PointedGHConverges p q)
    (μ : ∀ i, Measure (X i)) {v C : ℝ} (hv : 0 < v) (hC : 0 < C)
    (hlower : ∀ᶠ i in atTop, ENNReal.ofReal v ≤ μ i (ball (p i) 2))
    (hupper : ∀ᶠ i in atTop, ∀ x ∈ ball (p i) 4, ∀ r : ℝ, 0 < r → r ≤ 1 →
      μ i (ball x r) ≤ ENNReal.ofReal (C * r ^ 3)) :
    2 < dimH (univ : Set Y) := by
  classical
  let : MeasurableSpace Y := borel Y
  have : BorelSpace Y := ⟨rfl⟩
  by_contra hdim
  have hdim3 : dimH (univ : Set Y) < (3 : ℝ≥0) :=
    lt_of_le_of_lt (le_of_not_gt hdim) (by norm_num)
  have hzero : Measure.hausdorffMeasure 3 (closedBall q 3) = 0 := by
    have hz : Measure.hausdorffMeasure 3 (univ : Set Y) = 0 :=
      hausdorffMeasure_of_dimH_lt (d := (3 : ℝ≥0)) hdim3
    exact le_antisymm ((measure_mono (subset_univ _)).trans_eq hz) zero_le
  obtain ⟨U, r, hcover, hr, hsum⟩ :=
    Measure.exists_cover_by_positive_radii_of_hausdorffMeasure_zero
      (by norm_num : (0 : ℝ) < 3) hzero (by norm_num : (0 : ℝ) < 1 / 16)
      (show 0 < v / (128 * C) by positivity)
  have hc : ∀ j, ∃ c ∈ closedBall q 3,
      ∀ y ∈ U j ∩ closedBall q 3, dist y c ≤ r j := by
    intro j
    by_cases hj : (U j ∩ closedBall q 3).Nonempty
    · obtain ⟨c, hcU, hcB⟩ := hj
      refine ⟨c, hcB, fun y hy => ?_⟩
      have hd := edist_le_ediam_of_mem hy.1 hcU
      have he : edist y c ≤ ENNReal.ofReal (r j) := hd.trans (hr j).2.2
      rw [edist_dist] at he
      exact (ENNReal.ofReal_le_ofReal_iff (hr j).1.le).mp he
    · exact ⟨q, mem_closedBall_self (by norm_num), fun y hy => (hj ⟨y, hy⟩).elim⟩
  choose c hcB hcU using hc
  have hopenCover : closedBall q 3 ⊆ ⋃ j, ball (c j) (2 * r j) := by
    intro y hy
    obtain ⟨j, hj⟩ := mem_iUnion.mp (hcover hy)
    exact mem_iUnion.mpr ⟨j, (hcU j y ⟨hj, hy⟩).trans_lt (by linarith [(hr j).1])⟩
  obtain ⟨F, hF⟩ := (isCompact_closedBall q 3).elim_finite_subcover
    (fun j => ball (c j) (2 * r j)) (fun _ => isOpen_ball) hopenCover
  obtain ⟨ε, hε, hε1, hεr⟩ := finite_positive_error_CX7 F r (fun j => (hr j).1)
  obtain ⟨i, ⟨f⟩, hilo, hiup⟩ :=
    ((hconv.eventually_approx hε (show ε < 5 by linarith)).and (hlower.and hupper)).exists
  have hlift : ∀ j, ∃ z : BallCarrier (p i) 5, dist (c j) (f.toFun z) < ε := by
    intro j
    exact f.coverage (c j) (by have := mem_closedBall.mp (hcB j); linarith)
  choose z hz using hlift
  have hz4 : ∀ j, (z j).val ∈ ball (p i) 4 := by
    intro j
    have hrad := f.radial_lower (z j)
    have htri := dist_triangle (f.toFun (z j)) (c j) q
    rw [dist_comm (f.toFun (z j)) (c j)] at htri
    have hcb := mem_closedBall.mp (hcB j)
    change dist (z j).val (p i) < 4
    linarith [hz j]
  have hsource : ball (p i) 2 ⊆ ⋃ j ∈ F, ball (z j).val (4 * r j) := by
    intro x hx
    let xx : BallCarrier (p i) 5 := ⟨x, (mem_ball.mp hx).le.trans (by norm_num)⟩
    have hfx : f.toFun xx ∈ closedBall q 3 := by
      have hrad := f.radial_upper xx
      change dist (f.toFun xx) q ≤ 3
      have hx' := mem_ball.mp hx
      dsimp only [xx] at hrad
      linarith
    obtain ⟨j, hj, hfj⟩ := mem_iUnion₂.mp (hF hfx)
    refine mem_iUnion₂.mpr ⟨j, hj, ?_⟩
    have hd := (abs_lt.mp (f.distortion xx (z j))).1
    have ht := dist_triangle (f.toFun xx) (c j) (f.toFun (z j))
    have hfj' := mem_ball.mp hfj
    have hεj := hεr j hj
    change dist x (z j).val < 4 * r j
    dsimp only [xx] at hd
    linarith [hz j]
  have hsmall : μ i (ball (p i) 2) ≤ ENNReal.ofReal (v / 2) := by
    calc μ i (ball (p i) 2)
        ≤ μ i (⋃ j ∈ F, ball (z j).val (4 * r j)) := measure_mono hsource
      _ ≤ ∑ j ∈ F, μ i (ball (z j).val (4 * r j)) := measure_biUnion_finset_le _ _
      _ ≤ ∑ j ∈ F, ENNReal.ofReal (C * (4 * r j) ^ 3) := by
        apply Finset.sum_le_sum
        intro j hj
        exact hiup (z j).val (hz4 j) _ (by positivity [(hr j).1]) (by linarith [(hr j).2.1])
      _ = ENNReal.ofReal (64 * C) * ∑ j ∈ F, (ENNReal.ofReal (r j)) ^ 3 := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j hj
        rw [← ENNReal.ofReal_pow (hr j).1.le, ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        ring
      _ ≤ ENNReal.ofReal (64 * C) * ∑' j, (ENNReal.ofReal (r j)) ^ 3 := by
        gcongr
        exact ENNReal.sum_le_tsum F
      _ ≤ ENNReal.ofReal (64 * C) * ENNReal.ofReal (v / (128 * C)) := by
        gcongr
        simpa only [ENNReal.rpow_ofNat] using hsum
      _ = ENNReal.ofReal (v / 2) := by
        rw [← ENNReal.ofReal_mul (by positivity)]
        congr 1
        field_simp
        norm_num
  have := (ENNReal.ofReal_le_ofReal_iff (show 0 ≤ v / 2 by positivity)).mp (hilo.trans hsmall)
  linarith

end GC.LongTime.Ch12
