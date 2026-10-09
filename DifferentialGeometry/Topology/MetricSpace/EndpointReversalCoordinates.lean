import DifferentialGeometry.Topology.MetricSpace.DistanceCoordinates
import DifferentialGeometry.Topology.MetricSpace.CompactChart

set_option autoImplicit false

namespace Metric

open Set
open scoped NNReal

variable {X : Type*} [MetricSpace X] {m : ℕ} {μ : ℝ}

theorem exists_nonauxiliary_distance_separation
    (a : Fin (m + 1) → X) (hμ : 0 < μ) {x y : X} (hxy : x ≠ y)
    (hx : ∃ j, μ * dist x y ≤ dist x (a j) - dist y (a j))
    (hy : ∃ j, μ * dist y x ≤ dist y (a j) - dist x (a j)) :
    ∃ j : Fin m, μ * dist x y ≤ |dist x (a j.succ) - dist y (a j.succ)| := by
  obtain ⟨i, hi⟩ := hx
  obtain ⟨j, hj⟩ := hy
  rw [dist_comm y x] at hj
  have hpos : 0 < μ * dist x y := mul_pos hμ (dist_pos.mpr hxy)
  rcases Fin.eq_zero_or_eq_succ i with hi0 | ⟨k, hk⟩
  · subst i
    rcases Fin.eq_zero_or_eq_succ j with hj0 | ⟨k, hk⟩
    · subst j
      linarith
    · subst j
      exact ⟨k, hj.trans (by rw [abs_sub_comm]; exact le_abs_self _)⟩
  · subst i
    exact ⟨k, hi.trans (le_abs_self _)⟩

theorem distanceCoordinates_lower_of_endpoint_reversal
    (a : Fin (m + 1) → X) {V : Set X} (hμ : 0 < μ)
    (hdrop : ∀ x ∈ V, ∀ y ∈ V, x ≠ y →
      ∃ j, μ * dist x y ≤ dist x (a j) - dist y (a j))
    {x y : X} (hx : x ∈ V) (hy : y ∈ V) :
    μ * dist x y ≤
      dist (distanceCoordinates 2 (fun j : Fin m => a j.succ) x)
        (distanceCoordinates 2 (fun j : Fin m => a j.succ) y) := by
  by_cases hxy : x = y
  · subst y
    simp
  obtain ⟨j, hj⟩ := exists_nonauxiliary_distance_separation a hμ hxy
    (hdrop x hx y hy hxy) (hdrop y hy x hx (Ne.symm hxy))
  have ht := PiLp.dist_apply_le
    (distanceCoordinates 2 (fun j : Fin m => a j.succ) x)
    (distanceCoordinates 2 (fun j : Fin m => a j.succ) y) j
  rw [distanceCoordinates_apply, distanceCoordinates_apply, Real.dist_eq] at ht
  exact hj.trans ht

theorem exists_centered_distance_embedding_of_endpoint_reversal
    (a : Fin (m + 1) → X) {V : Set X} {q : X} (hq : q ∈ V) (hμ : 0 < μ)
    (hdrop : ∀ x ∈ V, ∀ y ∈ V, x ≠ y →
      ∃ j, μ * dist x y ≤ dist x (a j) - dist y (a j)) :
    let F : V → PiLp 2 (fun _ : Fin m => ℝ) := fun x =>
      distanceCoordinates 2 (fun j : Fin m => a j.succ) x -
        distanceCoordinates 2 (fun j : Fin m => a j.succ) q
    F ⟨q, hq⟩ = 0 ∧
      (∀ x y, μ * dist x y ≤ dist (F x) (F y)) ∧
      LipschitzWith (NNReal.sqrt m) F ∧
      ∃ e : V ≃ₜ range F, ∀ x, (e x : PiLp 2 (fun _ : Fin m => ℝ)) = F x := by
  dsimp only
  let A : Fin m → X := fun j => a j.succ
  let F : V → PiLp 2 (fun _ : Fin m => ℝ) := fun x =>
    distanceCoordinates 2 A x - distanceCoordinates 2 A q
  have hlo (x y : V) : μ * dist x y ≤ dist (F x) (F y) := by
    change μ * dist x.val y.val ≤ dist (distanceCoordinates 2 A x.val - _)
      (distanceCoordinates 2 A y.val - _)
    rw [dist_sub_right]
    exact distanceCoordinates_lower_of_endpoint_reversal a hμ hdrop x.property y.property
  have hLip : LipschitzWith (NNReal.sqrt m) F := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    change dist (distanceCoordinates 2 A x.val - _) (distanceCoordinates 2 A y.val - _) ≤ _
    rw [dist_sub_right]
    simpa only [Fintype.card_fin, Subtype.dist_eq] using (lipschitzWith_distanceCoordinates_two A).dist_le_mul x.val y.val
  obtain ⟨e, he, _, _⟩ := exists_homeomorph_range_of_lipschitz_lower_bound
    (ε := ⟨μ, hμ.le⟩) hLip hμ hlo
  exact ⟨sub_self _, hlo, hLip, e, he⟩


theorem isCompact_closedBall_of_endpoint_reversal
    (a : Fin (m + 1) → X) {q : X} {ρ r : ℝ} (hρ : 0 < ρ) (hr : r < ρ)
    (hc : IsComplete (closedBall q r)) (hμ : 0 < μ)
    (hdrop : ∀ x ∈ ball q ρ, ∀ y ∈ ball q ρ, x ≠ y →
      ∃ j, μ * dist x y ≤ dist x (a j) - dist y (a j)) :
    IsCompact (closedBall q r) := by
  obtain ⟨_, hlo, hLip, _⟩ := exists_centered_distance_embedding_of_endpoint_reversal
    a (mem_ball_self hρ) hμ hdrop
  exact isCompact_closedBall_of_chart hr hc (ε := ⟨μ, hμ.le⟩) hμ hLip hlo

end Metric
