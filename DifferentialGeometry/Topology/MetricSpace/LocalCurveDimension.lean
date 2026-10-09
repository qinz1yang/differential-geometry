import DifferentialGeometry.Topology.MetricSpace.AlmostRadialPoint
import Mathlib.Topology.MetricSpace.HausdorffDimension

set_option autoImplicit false

open Set Metric

namespace Metric

variable {X : Type*} [MetricSpace X]

theorem one_le_dimH_ball_of_continuous_curve {p : X} {L : ℝ} (hL : 0 < L)
    (c : unitInterval → X) (hc : Continuous c) (hc0 : c 0 = p) (hne : c 1 ≠ p) :
    1 ≤ dimH (ball p L) := by
  have hd : 0 < dist p (c 1) := dist_pos.mpr hne.symm
  let a := min (L / 2) (dist p (c 1))
  have ha : 0 < a := lt_min (half_pos hL) hd
  have haL : a < L := (min_le_left _ _).trans_lt (half_lt_self hL)
  have hI : Icc (0 : ℝ) a ⊆ (fun x : X => dist p x) '' ball p L := by
    intro t ht
    obtain ⟨s, hs, _⟩ := exists_first_dist_eq_of_continuous_curve c hc hc0 ht.1
      (ht.2.trans (min_le_right _ _))
    exact ⟨c s, by rw [mem_ball, dist_comm, hs]; exact ht.2.trans_lt haL, hs⟩
  have hdim : dimH (Icc (0 : ℝ) a) = 1 := by
    have hi : (interior (Icc (0 : ℝ) a)).Nonempty := by
      rw [interior_Icc]
      exact ⟨a / 2, half_pos ha, half_lt_self ha⟩
    simpa using Real.dimH_of_nonempty_interior hi
  rw [← hdim]
  exact (dimH_mono hI).trans ((LipschitzWith.dist_right p).dimH_image_le (ball p L))

theorem subsingleton_of_dimH_ball_lt_one
    (hcurves : ∀ x y : X, ∃ c : unitInterval → X, Continuous c ∧ c 0 = x ∧ c 1 = y)
    {p : X} {L : ℝ} (hL : 0 < L) (hdim : dimH (ball p L) < 1) : Subsingleton X := by
  have heq (x : X) : x = p := by
    by_contra hne
    obtain ⟨c, hc, hc0, hc1⟩ := hcurves p x
    exact (not_lt_of_ge (one_le_dimH_ball_of_continuous_curve hL c hc hc0 (by simpa only [hc1] using hne))) hdim
  exact ⟨fun x y => (heq x).trans (heq y).symm⟩

end Metric
