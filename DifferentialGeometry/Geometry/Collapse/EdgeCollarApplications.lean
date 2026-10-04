import DifferentialGeometry.Geometry.Collapse.LocalGradientLipschitz
import DifferentialGeometry.Geometry.Metric.Approximation.EdgeBandEnclosure

/-!
# Consumers of the LFR36/LFR37/LFR38 kernels

* `edgeBand_buffer_subset_of_band`: LFR36's two enclosure steps composed — every point within `303`
  of a point of the tested band (LFR36.1) lies in `B(p, 16Δ)` and in the LFR34 window
  `Δ/25 ≤ d_A ≤ 10.5Δ`.
* `identity_rank_two_and_opNorm`: rank two and the component operator-norm bound for the identity
  of the Euclidean plane (`A = B = id`, `γ = 1/200`).
* `translate_identity_adapted_clauses`: the clause transfer for `χ = id` on `B(0,100)` and
  `J = id + c` (a translate), with `γ = 1/200`.
-/

set_option autoImplicit false

open Set Metric ContinuousLinearMap

namespace GC.MetricGeometry

variable {X : Type*} [MetricSpace X]

/-- LFR36: band points and their `d/q`-buffers (`q ≤ 1.01`, radius `300`) are enclosed. -/
theorem edgeBand_buffer_subset_of_band {Q : X → WithLp 2 (ℝ × ℝ)} {p : X} {A : Set X}
    {Δ τ μ : ℝ} {Λ : NNReal} {ρ F f : X → ℝ} (hΔ : 1000000 ≤ Δ) (hτ : τ ≤ 1 / 10000)
    (hμ : μ ≤ 1 / 1000000) (hΛ : 100 * Δ * Λ ≤ 1 / 1000000)
    (hQp : Q p = 0)
    (hdist : ∀ x ∈ ball p (200 * Δ), ∀ y ∈ ball p (200 * Δ),
      |dist (Q x) (Q y) - dist x y| ≤ τ * Δ)
    (hheight : ∀ x ∈ ball p (200 * Δ), 0 ≤ (Q x).snd)
    (hpA : p ∈ A) (hborder : ∀ a ∈ A ∩ ball p (190 * Δ), (Q a).snd ≤ τ * Δ)
    (hρ : LipschitzWith Λ ρ) (hρp : ρ p = 1)
    (hF : ∀ x, |F x - infDist x A| ≤ μ * Δ)
    (hf : ∀ x ∈ ball p (100 * Δ), |f x - (Q x).fst| ≤ μ * Δ)
    {x : X} (hx : x ∈ ball p (100 * Δ)) (hfx : |f x| ≤ 10 * Δ)
    (hη : Δ / 10 ≤ F x / ρ x) (hη' : F x / ρ x ≤ 10 * Δ) {y : X} (hy : dist x y < 303) :
    y ∈ ball p (16 * Δ) ∧ Δ / 25 ≤ infDist y A ∧ infDist y A ≤ 21 / 2 * Δ := by
  obtain ⟨h15, hlo, hhi⟩ := edgeBand_mem_ball_and_infDist_window (by linarith) hτ hμ hΛ hQp hdist
    hheight hpA hborder hρ hρp hF hf hx hfx hη hη'
  exact edgeBand_buffer_subset hΔ h15 hlo hhi hy

end GC.MetricGeometry

namespace DifferentialGeometry.Geometry.Comparison

/-- Rank two and the component bound for the identity of the plane. -/
theorem identity_rank_two_and_opNorm :
    Function.Surjective (ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin 2))) ∧
      ‖ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin 2))‖ ≤ Real.sqrt 2 * 1 := by
  have hA : ‖ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin 2)) ∘L
      adjoint (ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin 2))) - 1‖ < (1 / 200) / 4 := by
    rw [adjoint_id, ContinuousLinearMap.id_comp, ← ContinuousLinearMap.one_def, sub_self,
      norm_zero]
    norm_num
  have hB : ‖ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin 2)) -
      ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin 2))‖ < (1 / 200) / 100 := by
    rw [sub_self, norm_zero]
    norm_num
  refine ⟨surjective_of_gram_perturbation (by norm_num) hA hB, opNorm_le_of_components zero_le_one
    (fun v => ?_) (fun v => ?_)⟩
  · rw [one_mul, ContinuousLinearMap.id_apply, ← Real.norm_eq_abs]
    exact PiLp.norm_apply_le v 0
  · rw [one_mul, ContinuousLinearMap.id_apply, ← Real.norm_eq_abs]
    exact PiLp.norm_apply_le v 1

/-- The Lipschitz and image clauses for a translate of the identity. -/
theorem translate_identity_adapted_clauses (c : EuclideanSpace ℝ (Fin 2)) :
    let J : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2) := fun y => y + c
    (∀ y ∈ ball (0 : EuclideanSpace ℝ (Fin 2)) 100, ∀ z ∈ ball (0 : EuclideanSpace ℝ (Fin 2)) 100,
        dist (J y) (J z) ≤ (1 + 1 / 200) * dist y z) ∧
      (∀ y ∈ ball (0 : EuclideanSpace ℝ (Fin 2)) 100,
        infDist (J y) (ball (J 0) 100) ≤ 100 * (1 / 200)) ∧
      ∀ w ∈ ball (J 0) 100, infDist w (J '' ball (0 : EuclideanSpace ℝ (Fin 2)) 100) ≤
        100 * (1 / 200) := by
  intro J
  refine vector_adapted_metric_clauses_of_perturbation (χ := fun y => y) rfl
    (fun y _ z _ => by nlinarith [dist_nonneg (x := y) (y := z)])
    (fun y hy => by rw [infDist_zero_of_mem hy]; norm_num)
    (fun w hw => by rw [image_id', infDist_zero_of_mem hw]; norm_num)
    (fun y _ z _ => by simp [J])

end DifferentialGeometry.Geometry.Comparison
