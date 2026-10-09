import DifferentialGeometry.Topology.MetricSpace.LocalHopfRinow

set_option autoImplicit false

open Set Metric

namespace Metric

theorem mem_two_ball_of_radial_between
    {X : Type*} [MetricSpace X] {o q x u : X} {R : ℝ}
    (hq : q ∈ ball o (R / 2)) (hx : x ∈ closedBall o R)
    (hparts : dist q x = dist q u + dist u x) : u ∈ ball o (2 * R) := by
  have hq' : dist q o < R / 2 := hq
  have hx' : dist x o ≤ R := hx
  have htri := dist_triangle q o x
  have hu := dist_triangle u q o
  rw [dist_comm o x] at htri
  rw [dist_comm u q] at hu
  have hn := dist_nonneg (x := u) (y := x)
  change dist u o < 2 * R
  linarith

theorem radial_germ_mem_two_ball
    {X : Type*} [MetricSpace X] {o q : X} {R A : ℝ} {γ : ℝ → X}
    (hq : q ∈ ball o (R / 2)) (hend : γ A ∈ closedBall o R)
    (hrad : ∀ s ∈ Ioc (0 : ℝ) A, dist q (γ s) = s)
    (hmin : ∀ s ∈ Ioc (0 : ℝ) A, ∀ t ∈ Ioc (0 : ℝ) A,
      dist (γ s) (γ t) = |s - t|) :
    ∀ s ∈ Ioc (0 : ℝ) A, γ s ∈ ball o (2 * R) := by
  intro s hs
  have hA : 0 < A := hs.1.trans_le hs.2
  apply mem_two_ball_of_radial_between hq hend
  rw [hrad A ⟨hA, le_rfl⟩, hrad s hs, hmin s hs A ⟨hA, le_rfl⟩,
    abs_of_nonpos (sub_nonpos.mpr hs.2)]
  ring

theorem exists_radial_metric_segment_in_two_ball
    {X : Type*} [MetricSpace X] [CompleteSpace X]
    (hcurves : ∀ a b : X, ∀ ε : ℝ, 0 < ε →
      ∃ c : unitInterval → X, Continuous c ∧ c 0 = a ∧ c 1 = b ∧
        eVariationOn c univ < ENNReal.ofReal (dist a b + ε))
    (o : X) {L R : ℝ} [LocallyCompactSpace (ball o L)] (hR : 0 < R)
    (hmargin : 2 * R < L) {q x : X}
    (hq : q ∈ ball o (R / 2)) (hx : x ∈ closedBall o R) :
    ∃ f : unitInterval → X, Continuous f ∧ f 0 = q ∧ f 1 = x ∧
      (∀ t, f t ∈ ball o (2 * R)) ∧
      ∀ s t, dist (f s) (f t) = dist q x * dist s t := by
  have hq' : dist q o < R / 2 := hq
  have hx' : dist x o ≤ R := hx
  obtain ⟨f, hf, hf0, hf1, _, hdist⟩ :=
    exists_metric_segment_in_closedBall_of_locallyCompact_ball hcurves o hmargin
      (show q ∈ closedBall o R by change dist q o ≤ R; linarith) hx
  refine ⟨f, hf, hf0, hf1, ?_, hdist⟩
  intro t
  have ht := dist_center_le_of_metric_segment (p := o) f hf0 hf1 hdist t
  have htri := dist_triangle q o x
  rw [dist_comm o x] at htri
  change dist (f t) o < 2 * R
  linarith

end Metric
