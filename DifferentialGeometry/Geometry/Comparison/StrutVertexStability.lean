import DifferentialGeometry.Geometry.Comparison.PairedPacketLocalization

set_option autoImplicit false

namespace DifferentialGeometry.Geometry.Comparison.Toponogov

open Set Metric Filter
open scoped Topology

variable {X : Type*} {ι : Type*} [MetricSpace X] [Finite ι]

theorem exists_ball_strut_margin {q : X} {s θ cap : ℝ}
    (hs : 0 < s) (hθ : 0 < θ) (hcap : 0 < cap) (a : ι → X)
    (ha : ∀ i, dist q (a i) = s)
    (hangle : ∀ i j, i ≠ j → Real.pi / 2 + 5 * θ <
      comparisonAngleNegCurvature 1 (dist q (a i)) (dist q (a j)) (dist (a i) (a j))) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ < s / 8 ∧ ρ < cap ∧
      (∀ x ∈ ball q ρ, ∀ i, s / 2 < dist x (a i)) ∧
      ∀ x ∈ ball q ρ, ∀ i j, i ≠ j → Real.pi / 2 + 4 * θ <
        comparisonAngleNegCurvature 1 (dist x (a i)) (dist x (a j)) (dist (a i) (a j)) := by
  have hne (i : ι) : q ≠ a i := dist_pos.mp (by rw [ha]; exact hs)
  have hev : ∀ᶠ x in 𝓝 q, ∀ i j, i ≠ j → Real.pi / 2 + 4 * θ <
      comparisonAngleNegCurvature 1 (dist x (a i)) (dist x (a j)) (dist (a i) (a j)) := by
    apply eventually_all.mpr
    intro i
    apply eventually_all.mpr
    intro j
    by_cases hij : i = j
    · exact Eventually.of_forall (fun _ h => (h hij).elim)
    have ht := (tendsto_order.mp (continuousAt_comparisonAngleNegCurvature_one_dist
      (hne i) (hne j))).1 (Real.pi / 2 + 4 * θ) (by linarith [hangle i j hij])
    exact ht.mono (fun _ h _ => h)
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hev
  let ρ := min (r / 2) (min (s / 16) (cap / 2))
  have hρ : 0 < ρ := lt_min (by positivity) (lt_min (by positivity) (by positivity))
  have hρr : ρ < r := (min_le_left _ _).trans_lt (by linarith)
  have hρs : ρ ≤ s / 16 := (min_le_right _ _).trans (min_le_left _ _)
  have hρcap : ρ ≤ cap / 2 := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨ρ, hρ, by linarith, by linarith, ?_, ?_⟩
  · intro x hx i
    have hx' : dist x q < ρ := hx
    have ht := dist_triangle q x (a i)
    rw [ha, dist_comm q x] at ht
    linarith
  · intro x hx
    exact hball (by exact (show dist x q < ρ from hx).trans hρr)

end DifferentialGeometry.Geometry.Comparison.Toponogov
