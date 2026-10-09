import DifferentialGeometry.Geometry.Metric.Approximation.ApproximateProductLimit
import Mathlib.Topology.MetricSpace.Bounded

/-! Uniform entire-factor diameter bounds persist in pointed limits and yield compact factors. -/

set_option autoImplicit false

open Set Filter
open scoped Topology

namespace GC.MetricGeometry.PointedGHConverges

universe u v w z

variable {X : ℕ → Type u} [∀ i, MetricSpace (X i)]
variable {Y : Type v} [MetricSpace Y] {p : ∀ i, X i} {q : Y} {D : ℝ}

theorem dist_le_of_uniform_bound (h : PointedGHConverges p q)
    (hD : ∀ i, ∀ x y : X i, dist x y ≤ D) (x y : Y) : dist x y ≤ D := by
  apply le_of_forall_pos_le_add
  intro ε hε
  let R := dist x q + dist y q + ε + 1
  have he : 0 < ε / 4 := by positivity
  have heR : ε / 4 < R := by
    dsimp [R]
    linarith [dist_nonneg (x := x) (y := q), dist_nonneg (x := y) (y := q)]
  obtain ⟨i, hi⟩ := (h.eventually_approx he heR).exists
  obtain ⟨f⟩ := hi
  obtain ⟨a, ha⟩ := f.coverage x (by
    dsimp [R]
    linarith [dist_nonneg (x := y) (y := q)])
  obtain ⟨b, hb⟩ := f.coverage y (by
    dsimp [R]
    linarith [dist_nonneg (x := x) (y := q)])
  have hab := (abs_lt.mp (f.distortion a b)).2
  have htri := dist_triangle4 x (f.toFun a) (f.toFun b) y
  rw [dist_comm (f.toFun b) y] at htri
  linarith [hD i a.val b.val]

theorem compactSpace_of_uniform_bound [ProperSpace Y] (h : PointedGHConverges p q)
    (hD : ∀ i, ∀ x y : X i, dist x y ≤ D) : CompactSpace Y := by
  apply Metric.compactSpace_iff_isBounded_univ.mpr
  exact Metric.isBounded_iff.mpr ⟨D, fun x hx y hy => h.dist_le_of_uniform_bound hD x y⟩

variable {E : Type w} {Z : ℕ → Type z} [MetricSpace E] [∀ i, MetricSpace (Z i)]
variable [ProperSpace E] [ProperSpace Y]
variable {a : E} {b : ∀ i, Z i} {δ : ℕ → ℝ}

theorem exists_compact_factor_of_approximate_products
    (h : PointedGHConverges p q)
    (f : ∀ i, KleinerLottApprox (p i) (WithLp.toLp 2 (a, b i)) (δ i))
    (hδ : Tendsto δ atTop (𝓝 0)) (hD : ∀ i, ∀ x y : Z i, dist x y ≤ D) :
    ∃ (W : Type) (m : MetricSpace W), letI := m
      ∃ (w : W) (φ : ℕ → ℕ), StrictMono φ ∧ ProperSpace W ∧ CompleteSpace W ∧
        CompactSpace W ∧ (∀ x y : W, dist x y ≤ D) ∧
        PointedGHConverges (fun i => b (φ i)) w ∧
        PointedGHConverges (fun i => p (φ i)) q ∧
        ∃ e : Y ≃ᵢ WithLp 2 (E × W), e q = WithLp.toLp 2 (a, w) := by
  obtain ⟨W, m, w, φ, hφ, hp, hc, hz, hx, e, he⟩ :=
    h.exists_product_isometry_of_approximate_products f hδ
  let := m
  let := hp
  have hbound : ∀ i, ∀ x y : Z (φ i), dist x y ≤ D := fun i => hD (φ i)
  exact ⟨W, m, w, φ, hφ, hp, hc, hz.compactSpace_of_uniform_bound hbound,
    hz.dist_le_of_uniform_bound hbound, hz, hx, e, he⟩

end GC.MetricGeometry.PointedGHConverges
