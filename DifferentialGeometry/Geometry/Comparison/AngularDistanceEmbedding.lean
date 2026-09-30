import DifferentialGeometry.Geometry.Comparison.ShortHingeEstimate
import DifferentialGeometry.Geometry.Comparison.AngularObstruction
import DifferentialGeometry.Topology.MetricSpace.EndpointReversalCoordinates

set_option autoImplicit false

namespace DifferentialGeometry.Geometry.Comparison.Toponogov

open Set Metric
open scoped NNReal

universe u v
variable {X : Type u} [MetricSpace X] {m : ℕ} {q : X} {ρ a₀ θ : ℝ}

theorem exists_centered_distance_embedding_of_angular_obstruction
    (hρ : 0 < ρ) (ha₀ : 0 < a₀) (hθ : 0 < θ) (hθhalf : θ < Real.pi / 2)
    (a : Fin (m + 1) → X) (D : ball q ρ → Type v) [∀ x, MetricSpace (D x)]
    (ζ : ∀ x, Fin (m + 1) → D x)
    (ha : ∀ x : ball q ρ, ∀ j, a₀ ≤ dist x.val (a j))
    (hscale : 2 * ρ ≤ shortHingeScale a₀ θ)
    (hζ : ∀ x : ball q ρ, ∀ i j, i ≠ j →
      Real.pi / 2 + θ < dist (ζ x i) (ζ x j))
    (hangular : ∀ x : ball q ρ, AngularObstruction (D x) m θ)
    (hhinges : ∀ x y : ball q ρ, x ≠ y →
      ∃ ξ : D x, ∀ j, ∃ H : MinimizingHinge (a j) y.val,
        H.center = x.val ∧ H.germAngle 1 = dist ξ (ζ x j) ∧ dist (a j) y.val ≤ H.modelSide 1) :
    let F : ball q ρ → PiLp 2 (fun _ : Fin m => ℝ) := fun x =>
      distanceCoordinates 2 (fun j : Fin m => a j.succ) x -
        distanceCoordinates 2 (fun j : Fin m => a j.succ) q
    F ⟨q, mem_ball_self hρ⟩ = 0 ∧
      (∀ x y, (Real.sin θ / 2) * dist x y ≤ dist (F x) (F y)) ∧
      LipschitzWith (NNReal.sqrt m) F ∧
      ∃ e : ball q ρ ≃ₜ range F, ∀ x, (e x : PiLp 2 (fun _ : Fin m => ℝ)) = F x := by
  have hμ : 0 < Real.sin θ / 2 := by
    have hs := Real.sin_pos_of_pos_of_lt_pi hθ (by linarith [Real.pi_pos])
    positivity
  apply exists_centered_distance_embedding_of_endpoint_reversal a (mem_ball_self hρ) hμ
  intro x hx y hy hxy
  let xx : ball q ρ := ⟨x, hx⟩
  let yy : ball q ρ := ⟨y, hy⟩
  have hne : xx ≠ yy := fun hh => hxy (congrArg Subtype.val hh)
  obtain ⟨ξ, hH⟩ := hhinges xx yy hne
  obtain ⟨j, hj⟩ := (hangular xx).exists_acute_anchor (ζ xx) (hζ xx) ξ
  obtain ⟨H, hc, hangle, hcomparison⟩ := hH j
  have hlen : dist x y < 2 * ρ := by
    have ht := dist_triangle x q y
    rw [dist_comm q y] at ht
    have hx' : dist x q < ρ := hx
    have hy' : dist y q < ρ := hy
    linarith
  have hdrop := H.distance_drop_of_short_hinge ha₀
    (by rw [hc]; exact ha xx j)
    (by rw [hc]; exact dist_pos.mpr hxy) hθ hθhalf
    (by rw [hangle]; exact hj) hcomparison
    (by rw [hc]; exact hlen.le.trans hscale)
  rw [hc, dist_comm (a j) y] at hdrop
  exact ⟨j, hdrop⟩

end DifferentialGeometry.Geometry.Comparison.Toponogov
