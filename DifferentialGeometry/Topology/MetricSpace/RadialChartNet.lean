import DifferentialGeometry.Topology.MetricSpace.EuclideanPacking
import DifferentialGeometry.Topology.MetricSpace.FiniteNets
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

set_option autoImplicit false

open Set Metric Real

namespace Metric

theorem exists_net_of_radial_contraction_and_chart
    {X : Type*} [MetricSpace X] {S : Set X} {q : X} {n : ℕ} (hn : 0 < n)
    {L R δ δ₀ ε : ℝ} (hL : 1 ≤ L) (hR : 0 < R) (hδ : 0 < δ)
    (hδ₀ : 0 < δ₀) (hδδ₀ : δ < δ₀) (hε : 0 < ε)
    (h : S → X) (hmem : ∀ x, h x ∈ ball q δ)
    (hlower : ∀ x y : S, (δ / sinh (2 * R)) * dist (x : X) (y : X) ≤ dist (h x) (h y))
    (φ : ball q δ₀ → PiLp 2 (fun _ : Fin n => ℝ))
    (hφ0 : φ ⟨q, by simpa only [mem_ball, dist_self] using hδ₀⟩ = 0)
    (hφlower : ∀ u v : ball q δ₀, L⁻¹ * dist u v ≤ dist (φ u) (φ v))
    (hφupper : ∀ u v : ball q δ₀, dist (φ u) (φ v) ≤ L * dist u v) :
    ∃ T : Finset X, T.card ≤ (1 + ⌈4 * L ^ 2 * sqrt n * sinh (2 * R) / ε⌉₊) ^ n ∧
      (T : Set X) ⊆ S ∧ ∀ x ∈ S, ∃ y ∈ T, dist x y < ε := by
  have hLp : 0 < L := by linarith
  have hsinh : 0 < sinh (2 * R) := sinh_pos_iff.mpr (by positivity)
  let H : S → ball q δ₀ := fun x => ⟨h x, (hmem x).trans hδδ₀⟩
  let F : S → PiLp 2 (fun _ : Fin n => ℝ) := fun x => φ (H x)
  let K := δ / (L * sinh (2 * R))
  have hK : 0 < K := div_pos hδ (mul_pos hLp hsinh)
  have hFnorm (x : S) : ‖F x‖ ≤ L * δ := by
    have hb := hφupper (H x) ⟨q, by simpa only [mem_ball, dist_self] using hδ₀⟩
    rw [hφ0, dist_zero_right] at hb
    exact hb.trans (mul_le_mul_of_nonneg_left (hmem x).le hLp.le)
  have hFlower (x y : S) : K * dist x y ≤ dist (F x) (F y) := by
    calc
      K * dist x y = L⁻¹ * ((δ / sinh (2 * R)) * dist (x : X) (y : X)) := by
        dsimp only [K]
        change δ / (L * sinh (2 * R)) * dist (x : X) (y : X) = _
        field_simp
      _ ≤ L⁻¹ * dist (h x) (h y) :=
        mul_le_mul_of_nonneg_left (hlower x y) (inv_nonneg.mpr hLp.le)
      _ ≤ dist (F x) (F y) := hφlower (H x) (H y)
  apply exists_finset_net_card_le_of_packing hε
  intro A hA hsep
  have hbound := card_le_of_bounded_lower_dist_map hn (mul_nonneg hLp.le hδ.le)
    hK hε hFnorm hFlower A hA hsep
  have heq : 4 * (L * δ) * sqrt n / (K * ε) =
      4 * L ^ 2 * sqrt n * sinh (2 * R) / ε := by
    dsimp only [K]
    field_simp
  rw [heq] at hbound
  have hceil := Nat.le_ceil (4 * L ^ 2 * sqrt n * sinh (2 * R) / ε)
  have hbase : 0 ≤ 1 + 4 * L ^ 2 * sqrt n * sinh (2 * R) / ε := by positivity
  have ht : (A.card : ℝ) ≤
      (1 + (⌈4 * L ^ 2 * sqrt n * sinh (2 * R) / ε⌉₊ : ℝ)) ^ n :=
    hbound.trans (pow_le_pow_left₀ hbase (by linarith) n)
  exact_mod_cast ht

end Metric
