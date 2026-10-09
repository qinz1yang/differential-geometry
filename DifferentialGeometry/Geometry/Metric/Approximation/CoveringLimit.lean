import DifferentialGeometry.Geometry.Metric.Approximation.NetTransfer
import DifferentialGeometry.Geometry.Metric.Approximation.PointedConvergence
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.Floor.Ring

open Filter Set

namespace GC.MetricGeometry

universe u v
variable {X : ℕ → Type u} {Y : Type v}
variable [∀ i, MetricSpace (X i)] [MetricSpace Y]
variable {p : ∀ i, X i} {q : Y}

theorem PointedGHConverges.exists_internal_finset_net
    (h : PointedGHConverges p q) {R δ K : ℝ} (hR : 0 < R) (hδ : 0 < δ)
    (hnets : ∀ᶠ i in atTop, ∃ F : Finset (X i), (F.card : ℝ) ≤ K ∧
      (∀ x ∈ F, dist x (p i) ≤ R + 1) ∧
      ∀ x : X i, dist x (p i) ≤ R + 1 → ∃ y ∈ F, dist x y ≤ δ / 4) :
    ∃ T : Finset Y, (T.card : ℝ) ≤ K ∧ (∀ y ∈ T, dist y q ≤ R) ∧
      ∀ y : Y, dist y q ≤ R → ∃ z ∈ T, dist y z < δ := by
  let ε := min (1 / 8 : ℝ) (δ / 16)
  have hε : 0 < ε := lt_min (by norm_num) (by positivity)
  have hεquarter : ε < 1 / 4 := (min_le_left _ _).trans_lt (by norm_num)
  have hεδ : ε < δ / 8 := (min_le_right _ _).trans_lt (by linarith)
  have hεR : ε < R + 2 := by linarith
  obtain ⟨i, hi, hFi⟩ := ((h.eventually_approx hε hεR).and hnets).exists
  obtain ⟨f⟩ := hi
  obtain ⟨F, hFcard, hFin, hFnet⟩ := hFi
  obtain ⟨T, hTcard, hTin, hTnet⟩ :=
    f.exists_internal_finset_net hR hδ hεquarter hεδ F hFin hFnet
  refine ⟨T, ?_, hTin, hTnet⟩
  exact (show (T.card : ℝ) ≤ F.card by exact_mod_cast hTcard).trans hFcard

theorem PointedGHConverges.exists_internal_finset_net_of_polynomial_covering
    (h : PointedGHConverges p q) {R δ C d : ℝ}
    (hR : 0 < R) (hδ : 0 < δ) (hδone : δ ≤ 1)
    (hnets : ∀ η : ℝ, 0 < η → η ≤ 1 →
      ∀ᶠ i in atTop, ∃ F : Finset (X i), (F.card : ℝ) ≤ C * η ^ (-d) ∧
        (∀ x ∈ F, dist x (p i) ≤ R + 1) ∧
        ∀ x : X i, dist x (p i) ≤ R + 1 → ∃ y ∈ F, dist x y ≤ η) :
    ∃ T : Finset Y, (T.card : ℝ) ≤ (C * 4 ^ d) * δ ^ (-d) ∧
      (∀ y ∈ T, dist y q ≤ R) ∧
      ∀ y : Y, dist y q ≤ R → ∃ z ∈ T, dist y z < δ := by
  obtain ⟨T, hcard, hTin, hTnet⟩ := h.exists_internal_finset_net hR hδ
    (hnets (δ / 4) (by positivity) (by linarith))
  refine ⟨T, ?_, hTin, hTnet⟩
  have heq : C * (δ / 4) ^ (-d) = (C * 4 ^ d) * δ ^ (-d) := by
    rw [Real.div_rpow hδ.le (by norm_num), Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 4),
      div_inv_eq_mul]
    ring
  exact heq ▸ hcard

private theorem ceil_covering_bound {B δ : ℝ} (hB : 0 ≤ B) (hδ : 0 < δ)
    (hδone : δ ≤ 1) (n : ℕ) :
    (((1 + Nat.ceil (B / (δ / 4))) ^ n : ℕ) : ℝ) ≤
      (2 + 4 * B) ^ n * δ ^ (-(n : ℝ)) := by
  have hc := (Nat.ceil_lt_add_one (div_nonneg hB (by positivity : 0 ≤ δ / 4))).le
  have hratio : B / (δ / 4) = 4 * B / δ := by ring
  have hb : (1 : ℝ) + Nat.ceil (B / (δ / 4)) ≤ (2 + 4 * B) / δ := by
    rw [hratio] at hc ⊢
    have htwo : (2 : ℝ) ≤ 2 / δ := (le_div_iff₀ hδ).mpr (by linarith)
    rw [add_div]
    linarith
  have hp := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ 1 + Nat.ceil (B / (δ / 4))) hb n
  push_cast
  calc
    ((1 : ℝ) + Nat.ceil (B / (δ / 4))) ^ n ≤ ((2 + 4 * B) / δ) ^ n := hp
    _ = (2 + 4 * B) ^ n * δ ^ (-(n : ℝ)) := by
      rw [div_pow, Real.rpow_neg hδ.le, Real.rpow_natCast, div_eq_mul_inv]

theorem PointedGHConverges.exists_internal_finset_net_of_ceil_covering
    (h : PointedGHConverges p q) {R δ B : ℝ} (n : ℕ)
    (hR : 0 < R) (hδ : 0 < δ) (hδone : δ ≤ 1) (hB : 0 ≤ B)
    (hnets : ∀ᶠ i in atTop, ∃ F : Finset (X i),
      F.card ≤ (1 + Nat.ceil (B / (δ / 4))) ^ n ∧
      (∀ x ∈ F, dist x (p i) ≤ R + 1) ∧
      ∀ x : X i, dist x (p i) ≤ R + 1 → ∃ y ∈ F, dist x y ≤ δ / 4) :
    ∃ T : Finset Y, (T.card : ℝ) ≤ (2 + 4 * B) ^ n * δ ^ (-(n : ℝ)) ∧
      (∀ y ∈ T, dist y q ≤ R) ∧
      ∀ y : Y, dist y q ≤ R → ∃ z ∈ T, dist y z < δ := by
  apply h.exists_internal_finset_net hR hδ
  filter_upwards [hnets] with i hi
  obtain ⟨F, hcard, hFin, hFnet⟩ := hi
  refine ⟨F, ?_, hFin, hFnet⟩
  exact (show (F.card : ℝ) ≤ ((1 + Nat.ceil (B / (δ / 4))) ^ n : ℕ) by
    exact_mod_cast hcard).trans (ceil_covering_bound hB hδ hδone n)

end GC.MetricGeometry
