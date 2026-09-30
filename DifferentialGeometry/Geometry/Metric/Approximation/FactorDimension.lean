import DifferentialGeometry.Geometry.Metric.Approximation.CoveringLimit
import DifferentialGeometry.Geometry.Comparison.EuclideanFactorDimension

set_option autoImplicit false

open Set Filter MeasureTheory

namespace GC.MetricGeometry

universe u v w
variable {X : ℕ → Type u} {Y : Type v} {Z : Type w}
variable [∀ i, MetricSpace (X i)] [MetricSpace Y] [MetricSpace Z]
variable {p : ∀ i, X i} {q : Y}

theorem PointedGHConverges.exists_polynomial_nets_at (h : PointedGHConverges p q) {d : ℝ}
    (hcover : ∀ R : ℝ, 0 < R → ∃ C : ℝ, 0 < C ∧
      ∀ η : ℝ, 0 < η → η ≤ 1 →
        ∀ᶠ i in atTop, ∃ F : Finset (X i), (F.card : ℝ) ≤ C * η ^ (-d) ∧
          (∀ x ∈ F, dist x (p i) ≤ R) ∧
          ∀ x : X i, dist x (p i) ≤ R → ∃ y ∈ F, dist x y ≤ η)
    (z : Y) : ∀ R : ℝ, 0 < R → ∃ C : ℝ, 0 < C ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∃ F : Finset Y,
        (F.card : ℝ) ≤ C * δ ^ (-d) ∧ (∀ y ∈ F, dist y z ≤ R) ∧
        ∀ y : Y, dist y z ≤ R → ∃ w ∈ F, dist y w ≤ δ := by
  intro R hR
  have hU : 0 < R + dist z q := by linarith [dist_nonneg (x := z) (y := q)]
  obtain ⟨C, hC, hc⟩ := hcover (R + dist z q + 1) (by linarith)
  refine ⟨C * 4 ^ d * 2 ^ d, by positivity, ?_⟩
  intro δ hδ hδone
  obtain ⟨F, hcard, _, hnet⟩ := h.exists_internal_finset_net_of_polynomial_covering
    hU (show 0 < δ / 2 by positivity) (show δ / 2 ≤ 1 by linarith) hc
  obtain ⟨T, hTcard, hTinside, hTcover⟩ :=
    Metric.exists_internal_finset_net_of_finite_centers (Metric.closedBall z R) F id
      (show 0 < δ / 2 by positivity) (fun y hy => hnet y (by
        have ht := dist_triangle y z q
        change dist y z ≤ R at hy
        linarith))
  refine ⟨T, ?_, hTinside, ?_⟩
  · have heq : (C * 4 ^ d) * (δ / 2) ^ (-d) = (C * 4 ^ d * 2 ^ d) * δ ^ (-d) := by
      rw [Real.div_rpow hδ.le (by norm_num), Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2),
        div_inv_eq_mul]
      ring
    exact (show (T.card : ℝ) ≤ F.card by exact_mod_cast hTcard).trans (heq ▸ hcard)
  · intro y hy
    obtain ⟨w, hw, hd⟩ := hTcover y hy
    exact ⟨w, hw, by linarith⟩

theorem PointedGHConverges.dimH_euclidean_factor_le (h : PointedGHConverges p q)
    {k n : ℕ} (hkn : k ≤ n)
    (hcover : ∀ R : ℝ, 0 < R → ∃ C : ℝ, 0 < C ∧
      ∀ η : ℝ, 0 < η → η ≤ 1 →
        ∀ᶠ i in atTop, ∃ F : Finset (X i), (F.card : ℝ) ≤ C * η ^ (-(n : ℝ)) ∧
          (∀ x ∈ F, dist x (p i) ≤ R) ∧
          ∀ x : X i, dist x (p i) ≤ R → ∃ y ∈ F, dist x y ≤ η)
    (e : Y ≃ᵢ WithLp 2 (EuclideanSpace ℝ (Fin k) × Z)) (z : Z) :
    dimH (univ : Set Z) ≤ ENNReal.ofReal ((n - k : ℕ) : ℝ) := by
  exact e.dimH_euclidean_factor_le hkn (e.symm (WithLp.toLp 2 (0, z))) z
    (by simp) (h.exists_polynomial_nets_at hcover _)

theorem PointedGHConverges.dimH_real_factor_le (h : PointedGHConverges p q)
    {n : ℕ} (hn : 1 ≤ n)
    (hcover : ∀ R : ℝ, 0 < R → ∃ C : ℝ, 0 < C ∧
      ∀ η : ℝ, 0 < η → η ≤ 1 →
        ∀ᶠ i in atTop, ∃ F : Finset (X i), (F.card : ℝ) ≤ C * η ^ (-(n : ℝ)) ∧
          (∀ x ∈ F, dist x (p i) ≤ R) ∧
          ∀ x : X i, dist x (p i) ≤ R → ∃ y ∈ F, dist x y ≤ η)
    (e : Y ≃ᵢ WithLp 2 (ℝ × Z)) (z : Z) :
    dimH (univ : Set Z) ≤ ENNReal.ofReal ((n - 1 : ℕ) : ℝ) := by
  exact e.dimH_real_factor_le hn (e.symm (WithLp.toLp 2 (0, z))) z
    (by simp) (h.exists_polynomial_nets_at hcover _)

end GC.MetricGeometry
