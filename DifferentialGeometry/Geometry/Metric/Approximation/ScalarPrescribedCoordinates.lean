import DifferentialGeometry.Geometry.Metric.Approximation.PrescribedCoordinateConvergence
import Mathlib.Analysis.InnerProductSpace.PiL2

set_option autoImplicit false

open Set Filter Metric
open scoped Topology

namespace GC.MetricGeometry

universe u v w
variable {X : ℕ → Type u} [∀ i, MetricSpace (X i)]
variable {Y : Type v} [MetricSpace Y] {Z : Type w} [MetricSpace Z] {k : ℕ}
variable {p : ∀ i, X i} {q : Y} {R ε : ℕ → ℝ}

theorem eventually_prescribed_kleinerLott_approximation_of_component_convergence
    (e : Y ≃ᵢ WithLp 2 (EuclideanSpace ℝ (Fin k) × Z))
    (f : ∀ i, PointedBallApprox (p i) q (R i) (ε i))
    (hR : Tendsto R atTop atTop) (hε : Tendsto ε atTop (𝓝 0))
    (h : ∀ i, X i → EuclideanSpace ℝ (Fin k))
    (hp : ∀ i, h i (p i) = (e q).fst)
    (hclose : ∀ S : ℝ, 0 < S → ∀ η : ℝ, 0 < η → ∀ᶠ i in atTop,
      ∀ j, ∀ x : BallCarrier (p i) (R i), dist x.val (p i) ≤ S →
        |h i x.val j - (e ((f i).toFun x)).fst j| < η)
    {δ : ℝ} (hδ : 0 < δ) (hδone : δ < 1) :
    ∀ᶠ i in atTop, ∃ ψ : KleinerLottApprox (p i) (e q) δ,
      ∀ x : X i, (ψ.toFun x).fst = h i x := by
  apply eventually_prescribed_kleinerLott_approximation e f hR hε h hp _ hδ hδone
  intro S η hη
  let ρ : ℝ := η / ((k : ℝ) + 1)
  have hk : 0 ≤ (k : ℝ) := Nat.cast_nonneg k
  have hden : 0 < (k : ℝ) + 1 := by positivity
  have hρ : 0 < ρ := div_pos hη hden
  filter_upwards [hclose (max S 1) (lt_of_lt_of_le zero_lt_one (le_max_right _ _)) ρ hρ] with i hi
  intro x hx
  have hsq : dist (h i x.val) (e ((f i).toFun x)).fst ^ 2 ≤ (k : ℝ) * ρ ^ 2 := by
    rw [EuclideanSpace.dist_sq_eq]
    calc
      ∑ j, dist (h i x.val j) ((e ((f i).toFun x)).fst j) ^ 2 ≤ ∑ _ : Fin k, ρ ^ 2 := by
        apply Finset.sum_le_sum
        intro j _
        have hh : dist (h i x.val j) ((e ((f i).toFun x)).fst j) ≤ ρ := by
          simpa only [Real.dist_eq] using (hi j x (hx.trans (le_max_left _ _))).le
        exact pow_le_pow_left₀ dist_nonneg hh 2
      _ = (k : ℝ) * ρ ^ 2 := by simp
  have hcard : (k : ℝ) ≤ ((k : ℝ) + 1) ^ 2 := by nlinarith [sq_nonneg (k : ℝ)]
  have hmul : ((k : ℝ) + 1) * ρ = η := by
    dsimp [ρ]
    exact mul_div_cancel₀ η hden.ne'
  have hsqη : (k : ℝ) * ρ ^ 2 ≤ η ^ 2 := by
    calc
      (k : ℝ) * ρ ^ 2 ≤ ((k : ℝ) + 1) ^ 2 * ρ ^ 2 :=
        mul_le_mul_of_nonneg_right hcard (sq_nonneg ρ)
      _ = η ^ 2 := by rw [← mul_pow, hmul]
  nlinarith [dist_nonneg (x := h i x.val) (y := (e ((f i).toFun x)).fst)]

theorem eventually_distance_coordinates_kleinerLott_approximation
    (e : Y ≃ᵢ WithLp 2 (EuclideanSpace ℝ (Fin k) × Z)) (z : Z)
    (hq : e q = WithLp.toLp 2 (0, z))
    (f : ∀ i, PointedBallApprox (p i) q (R i) (ε i))
    (hR : Tendsto R atTop atTop) (hε : Tendsto ε atTop (𝓝 0))
    (a : ∀ i, Fin k → X i)
    (hclose : ∀ S : ℝ, 0 < S → ∀ η : ℝ, 0 < η → ∀ᶠ i in atTop,
      ∀ j, ∀ x : BallCarrier (p i) (R i), dist x.val (p i) ≤ S →
        |dist (p i) (a i j) - dist x.val (a i j) - (e ((f i).toFun x)).fst j| < η)
    {δ : ℝ} (hδ : 0 < δ) (hδone : δ < 1) :
    ∀ᶠ i in atTop, ∃ ψ : KleinerLottApprox (p i) (WithLp.toLp 2 (0, z)) δ,
      ∀ x : X i, (ψ.toFun x).fst =
        WithLp.toLp 2 (fun j => dist (p i) (a i j) - dist x (a i j)) := by
  let h (i : ℕ) (x : X i) : EuclideanSpace ℝ (Fin k) :=
    WithLp.toLp 2 (fun j => dist (p i) (a i j) - dist x (a i j))
  have hp (i : ℕ) : h i (p i) = (e q).fst := by
    rw [hq]
    ext j
    simp [h]
  have hh := eventually_prescribed_kleinerLott_approximation_of_component_convergence
    e f hR hε h hp hclose hδ hδone
  rw [← hq]
  exact hh

end GC.MetricGeometry
