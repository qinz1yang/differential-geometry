import DifferentialGeometry.Geometry.Metric.SelectedZeroSupportRows

/-!
# Consumers of the FC09 / FC13 selected-zero-ball rows

* `fc13_radial_contMDiffOn_test_ball`: on a manifold with a distance, a radial function of a
  maximal doubling zero ball, smooth on the open shell and with FC13's value error on a support
  meeting `D = B(p, L ρ p)`, is smooth on `D` (FC13 conclusion + its "in particular" clause).
* `fc09_selected_points_unit_interval`: on the compact interval `[0, 1]` with constant scale, LC64's
  selection has at most one centre in every unit ball (FC09 with the point supports `{i}`).
-/

set_option autoImplicit false

open Set Metric
open scoped Manifold ContDiff

namespace GC.MetricGeometry

/-- FC13 with its smoothness clause, on a manifold with a distance. -/
theorem fc13_radial_contMDiffOn_test_ball {X : Type*} [MetricSpace X] {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {H : Type*} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} [ChartedSpace H X] {n : WithTop ℕ∞}
    (Z : Set X) (r ρ η : X → ℝ) {Λ : NNReal}
    (hρ : LipschitzWith Λ ρ) (hρpos : ∀ x, 0 < ρ x) {T : ℝ} (hlower : ∀ q, T * ρ q ≤ r q)
    {z : X} (hZ : (ball z (r z) ∩ Z).Nonempty)
    (hmax : ∀ q, (ball q (r q) ∩ Z).Nonempty → ball z (r z) ⊆ ball q (r q) → r q ≤ 2 * r z)
    {p : X} {L e : ℝ} (hL : 0 < L) (hΛ : L * Λ ≤ 1 / 4) (hT : 1600 * L ≤ T) (he : e < 1 / 40)
    {S : Set X} (herror : ∀ x ∈ S, |η x - dist z x / r z| < e)
    (hvalue : ∀ x ∈ S, η x ∈ Icc (1 / 5) (9 / 10)) (hmeet : (S ∩ ball p (L * ρ p)).Nonempty)
    (hsmooth : ContMDiffOn I 𝓘(ℝ, ℝ) n η
      {x | 1 / 10 < dist z x / r z ∧ dist z x / r z < 10}) :
    T / 20 ≤ r z / ρ p ∧ ContMDiffOn I 𝓘(ℝ, ℝ) n η (ball p (L * ρ p)) := by
  obtain ⟨hratio, hshell⟩ := fc13_of_maximal_doubling Z r ρ η hρ hρpos hlower hZ hmax hL hΛ hT
    he herror hvalue hmeet
  exact ⟨hratio, fc13_contMDiffOn_of_shell hshell hsmooth⟩

/-- FC09 on `[0, 1]`: LC64's selection with radius `2000` and scale `1` has at most one centre in
every unit ball. -/
theorem fc09_selected_points_unit_interval :
    ∃ J : Set (Icc (0 : ℝ) 1), J.Finite ∧
      ∀ p : Icc (0 : ℝ) 1,
        {i | i ∈ J ∧ ({i} ∩ ball p 1 : Set (Icc (0 : ℝ) 1)).Nonempty}.Subsingleton := by
  obtain ⟨J, hfin, -, -, -, hfc09, -⟩ := fc09_fc13_selected_zero_balls (X := Icc (0 : ℝ) 1)
    univ (fun _ => (2000 : ℝ)) (fun _ => (1 : ℝ)) (Λ := 0) (LipschitzWith.const _)
    (fun _ => one_pos) (T := 2000) (U := 2000) (by norm_num) le_rfl (fun _ => by norm_num)
    (fun _ => by norm_num)
  refine ⟨J, hfin, fun p => ?_⟩
  have h := hfc09 (fun i => {i}) p 1 (1 / 2) one_pos (by norm_num) (by simp) (by norm_num)
    (by norm_num) (fun i _ => by
      rw [singleton_subset_iff]
      exact mem_closedBall_self (by norm_num))
  simpa only [mul_one] using h

end GC.MetricGeometry
