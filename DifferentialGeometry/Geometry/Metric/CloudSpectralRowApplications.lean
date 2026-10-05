import DifferentialGeometry.Geometry.Metric.CloudSpectralRow

/-!
# Consumers of CFS04's span clause

* `cfs04_single_centre_span_clause`: a one-centre selection `{x₀}` with positive radius: on
  `B(x₀, λ r₀)` the spectral cluster fixes `V⊥` and the displacement has the normal
  `V⊥`-component of `z − x₀`, where `V = span{0, L_{x₀}}`.
* `cfs04_span_clause_euclidean_plane`: the same in `EuclideanSpace ℝ (Fin 2)` with the plane `⊥`.
-/

set_option autoImplicit false

noncomputable section

open Set Metric Module DifferentialGeometry.Analysis
open scoped BigOperators

namespace GC.MetricGeometry

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]

/-- The span clause for a one-centre selection. -/
theorem cfs04_single_centre_span_clause (x₀ : H) (r : H → ℝ) (hr : 0 < r x₀)
    (P : H → Submodule ℝ H) {ℓ : ℝ} (hℓ : 0 < ℓ) :
    let V : Submodule ℝ H := ⨆ (i ∈ ({x₀} : Finset H)) (_ : (closedBall i (20 * ℓ * r i) ∩
      ball x₀ (ℓ * r x₀)).Nonempty), (ℝ ∙ (i - x₀)) ⊔ P i
    let w : H → H → ℝ := fun i y => ballCutoff i (10 * ℓ * r i) (2 * (10 * ℓ * r i)) y /
      ∑ a ∈ ({x₀} : Finset H), ballCutoff a (10 * ℓ * r a) (2 * (10 * ℓ * r a)) y
    let Q : H → Submodule ℝ H := fun y => ⨆ μ ∈ ball (1 : ℝ) (1 / 2),
      End.eigenspace (∑ i ∈ ({x₀} : Finset H), w i y • (P i)ᗮ.starProjection).toLinearMap μ
    ∀ z ∈ ball x₀ (ℓ * r x₀), (∀ y ∈ Vᗮ, (Q z).starProjection y = y) ∧
      Vᗮ.starProjection ((Q z).starProjection (z - ∑ i ∈ ({x₀} : Finset H), w i z • i)) =
        Vᗮ.starProjection (z - x₀) :=
  cfs04_orthogonal_span_clause {x₀} r (fun i hi => by rw [Finset.mem_singleton.mp hi]; exact hr)
    P hℓ (Finset.mem_singleton_self x₀) (mem_ball_self (by positivity))

/-- The one-centre clause in the Euclidean plane with the zero plane. -/
theorem cfs04_span_clause_euclidean_plane (z : EuclideanSpace ℝ (Fin 2))
    (hz : z ∈ ball (0 : EuclideanSpace ℝ (Fin 2)) (1 / 100)) :
    let V : Submodule ℝ (EuclideanSpace ℝ (Fin 2)) :=
      ⨆ (i ∈ ({0} : Finset (EuclideanSpace ℝ (Fin 2))))
        (_ : (closedBall i (20 * 1 * 1) ∩ ball 0 (1 * 1)).Nonempty), (ℝ ∙ (i - 0)) ⊔ ⊥
    ∀ y ∈ Vᗮ, (⨆ μ ∈ ball (1 : ℝ) (1 / 2), End.eigenspace
      (∑ i ∈ ({0} : Finset (EuclideanSpace ℝ (Fin 2))),
        (ballCutoff i (10 * 1 * 1) (2 * (10 * 1 * 1)) z /
          ∑ a ∈ ({0} : Finset (EuclideanSpace ℝ (Fin 2))),
            ballCutoff a (10 * 1 * 1) (2 * (10 * 1 * 1)) z) •
          (⊥ : Submodule ℝ (EuclideanSpace ℝ (Fin 2)))ᗮ.starProjection).toLinearMap
        μ).starProjection y = y := by
  intro V y hy
  exact (cfs04_single_centre_span_clause (0 : EuclideanSpace ℝ (Fin 2)) (fun _ => 1) one_pos
    (fun _ => ⊥) one_pos z (by
      rw [mem_ball] at hz ⊢
      linarith)).1 y hy

end GC.MetricGeometry
