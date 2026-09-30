import DifferentialGeometry.Geometry.Comparison.SimplexStrutShortening
import DifferentialGeometry.Geometry.Comparison.StrutVertexStability

set_option autoImplicit false

namespace DifferentialGeometry.Geometry.Comparison.Toponogov

open Set Metric Filter
open scoped Topology

theorem exists_common_shortening_strut_neighborhood
    {X : Type*} {D : Type*} [MetricSpace X] {m n : ℕ} (hm : 0 < m) (hmn : m ≤ n)
    (q : X) (ξ : D → {v : EuclideanSpace ℝ (Fin m) // ‖v‖ = 1})
    (γ : D → ℝ → X) (r : D → ℝ)
    (hr : ∀ d, 0 < r d)
    (hradial : ∀ d, ∀ s ∈ Ioc (0 : ℝ) (r d), dist q (γ d s) = s)
    (hdense : ∀ v : EuclideanSpace ℝ (Fin m), ‖v‖ = 1 → ∀ ε : ℝ, 0 < ε →
      ∃ d, InnerProductGeometry.angle v (ξ d).val < ε)
    (hangle : ∀ d e, Tendsto
      (fun s : ℝ => comparisonAngleNegCurvature 1 s s (dist (γ d s) (γ e s)))
      (𝓝[>] (0 : ℝ)) (𝓝 (InnerProductGeometry.angle (ξ d).val (ξ e).val)))
    {S : ℝ} (hS : 0 < S) :
    ∃ (d : Fin (m + 1) → D) (s : ℝ), 0 < s ∧ s < S ∧
      (∀ i, s ≤ r (d i)) ∧ (∀ i, dist q (γ (d i) s) = s) ∧
      (∀ i j, i ≠ j → Real.pi / 2 + 5 * (8 * (n : ℝ))⁻¹ <
        comparisonAngleNegCurvature 1 (dist q (γ (d i) s)) (dist q (γ (d j) s))
          (dist (γ (d i) s) (γ (d j) s))) ∧
      ∀ cap : ℝ, 0 < cap → ∃ ρ : ℝ, 0 < ρ ∧ ρ < s / 8 ∧ ρ < cap ∧
        (∀ x ∈ ball q ρ, ∀ i, s / 2 < dist x (γ (d i) s)) ∧
        ∀ x ∈ ball q ρ, ∀ i j, i ≠ j → Real.pi / 2 + 4 * (8 * (n : ℝ))⁻¹ <
          comparisonAngleNegCurvature 1 (dist x (γ (d i) s)) (dist x (γ (d j) s))
            (dist (γ (d i) s) (γ (d j) s)) := by
  obtain ⟨d, s, hs, hsS, hsr, hrad, _hdir, hcomp⟩ :=
    exists_common_shortening_strut_of_dense_directions hm hmn q ξ γ r hr hradial hdense hangle hS
  refine ⟨d, s, hs, hsS, hsr, hrad, hcomp, fun cap hcap => ?_⟩
  have hn : 0 < (n : ℝ) := by exact_mod_cast lt_of_lt_of_le hm hmn
  exact exists_ball_strut_margin hs (by positivity) hcap (fun i => γ (d i) s) hrad hcomp

end DifferentialGeometry.Geometry.Comparison.Toponogov
