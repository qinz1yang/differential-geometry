/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hongzhou Lin
-/
import DifferentialGeometry.Geometry.Hyperbolic.LorentzModel.CoarseGeometry.CocompactActions

noncomputable section

namespace DifferentialGeometry.UniformCoarseMaps

open Hyperbolic HyperbolicConvexity PseudoIsometry

variable {n : ℕ}

theorem exists_affine_upper_of_uniformContinuous {Φ : HUpper n → HUpper n}
    (hΦ : UniformContinuous Φ) :
    ∃ L : ℝ, 0 < L ∧ ∀ x y, dist (Φ x) (Φ y) ≤ L * dist x y + 1 := by
  obtain ⟨δ, hδ, hmod⟩ := Metric.uniformContinuous_iff_le.mp hΦ 1 (by norm_num)
  refine ⟨δ⁻¹, inv_pos.mpr hδ, fun x y => ?_⟩
  by_cases hxy : x = y
  · subst y
    simp only [dist_self, mul_zero, zero_add]
    norm_num
  let T := dist x y
  have hT : 0 < T := dist_pos.mpr hxy
  let m : ℕ := ⌈T / δ⌉₊
  have hmpos : 0 < m := Nat.ceil_pos.mpr (div_pos hT hδ)
  have hmR : (0 : ℝ) < m := by exact_mod_cast hmpos
  have hm : (m : ℝ) ≠ 0 := hmR.ne'
  have hmT : T ≤ (m : ℝ) * δ := (div_le_iff₀ hδ).mp (Nat.le_ceil (T / δ))
  have hmlt : (m : ℝ) < T / δ + 1 := Nat.ceil_lt_add_one (div_nonneg hT.le hδ.le)
  let p : ℕ → HUpper n := fun i => geodFromTo x y hxy ((i : ℝ) / m * T)
  have hp0 : p 0 = x := by
    simp only [p, Nat.cast_zero, zero_div, zero_mul, geodFromTo_zero]
  have hpm : p m = y := by
    simp only [p, div_self hm, one_mul]
    exact geodFromTo_dist hxy
  have hstep (i : ℕ) : dist (p i) (p (i + 1)) ≤ δ := by
    change dist (geodFromTo x y hxy _) (geodFromTo x y hxy _) ≤ δ
    rw [dist_geodFromTo]
    have he : (i : ℝ) / m * T - ((i + 1 : ℕ) : ℝ) / m * T = -(T / m) := by
      push_cast
      ring
    rw [he, abs_neg, abs_of_nonneg (div_nonneg hT.le hmR.le), div_le_iff₀ hmR]
    simpa only [mul_comm] using hmT
  have hchain : dist (Φ (p 0)) (Φ (p m)) ≤ m := by
    calc
      _ ≤ ∑ i ∈ Finset.range m, dist (Φ (p i)) (Φ (p (i + 1))) :=
        UniformPseudoIsometry.dist_le_sum_range (fun i => Φ (p i)) m
      _ ≤ ∑ _i ∈ Finset.range m, (1 : ℝ) :=
        Finset.sum_le_sum (fun i _ => hmod (hstep i))
      _ = m := by simp
  rw [hp0, hpm] at hchain
  calc
    dist (Φ x) (Φ y) ≤ m := hchain
    _ ≤ T / δ + 1 := hmlt.le
    _ = δ⁻¹ * dist x y + 1 := by dsimp only [T]; ring

theorem pseudoIsometry_of_upper_and_coarse_inverse {Φ Ψ : HUpper n → HUpper n}
    {K E : ℝ} (hK : 1 ≤ K) (hE : 0 ≤ E)
    (hΦ : ∀ x y, dist (Φ x) (Φ y) ≤ K * dist x y + 1)
    (hΨ : ∀ x y, dist (Ψ x) (Ψ y) ≤ K * dist x y + 1)
    (hcomp : ∀ x, dist (Ψ (Φ x)) x ≤ E) :
    IsPseudoIsometry K (1 + 2 * E) Φ := by
  have hC : 0 ≤ 1 + 2 * E := by positivity
  refine ⟨hK, hC, fun x y => (hΦ x y).trans (by linarith), fun x y => ?_⟩
  have hKpos : 0 < K := lt_of_lt_of_le zero_lt_one hK
  have htri := dist_triangle x (Ψ (Φ x)) y
  have htri' := dist_triangle (Ψ (Φ x)) (Ψ (Φ y)) y
  have hx := hcomp x
  rw [dist_comm (Ψ (Φ x)) x] at hx
  have hy := hcomp y
  have hm := hΨ (Φ x) (Φ y)
  have hbound : dist x y ≤ K * dist (Φ x) (Φ y) + (1 + 2 * E) := by linarith
  have hs := mul_le_mul_of_nonneg_left hbound (inv_nonneg.mpr hKpos.le)
  rw [mul_add, ← mul_assoc, inv_mul_cancel₀ hKpos.ne', one_mul] at hs
  have herror : K⁻¹ * (1 + 2 * E) ≤ 1 + 2 * E :=
    (mul_le_mul_of_nonneg_right (inv_le_one_of_one_le₀ hK) hC).trans_eq (one_mul _)
  linarith

theorem exists_twoSided_pseudoIsometry {Φ Ψ : HUpper n → HUpper n}
    (hΦ : UniformContinuous Φ) (hΨ : UniformContinuous Ψ)
    {E E' : ℝ} (hE : 0 ≤ E) (hE' : 0 ≤ E')
    (hleft : ∀ x, dist (Ψ (Φ x)) x ≤ E) (hright : ∀ y, dist (Φ (Ψ y)) y ≤ E') :
    ∃ K C C' : ℝ, IsPseudoIsometry K C Φ ∧ IsPseudoIsometry K C' Ψ := by
  obtain ⟨L, _, hL⟩ := exists_affine_upper_of_uniformContinuous hΦ
  obtain ⟨L', _, hL'⟩ := exists_affine_upper_of_uniformContinuous hΨ
  let K := max 1 (max L L')
  have hK : 1 ≤ K := le_max_left _ _
  have hLK : L ≤ K := (le_max_left _ _).trans (le_max_right _ _)
  have hL'K : L' ≤ K := (le_max_right _ _).trans (le_max_right _ _)
  have hu : ∀ x y, dist (Φ x) (Φ y) ≤ K * dist x y + 1 :=
    fun x y => (hL x y).trans
      (add_le_add (mul_le_mul_of_nonneg_right hLK dist_nonneg) le_rfl)
  have hv : ∀ x y, dist (Ψ x) (Ψ y) ≤ K * dist x y + 1 :=
    fun x y => (hL' x y).trans
      (add_le_add (mul_le_mul_of_nonneg_right hL'K dist_nonneg) le_rfl)
  exact ⟨K, 1 + 2 * E, 1 + 2 * E',
    pseudoIsometry_of_upper_and_coarse_inverse hK hE hu hv hleft,
    pseudoIsometry_of_upper_and_coarse_inverse hK hE' hv hu hright⟩

end DifferentialGeometry.UniformCoarseMaps
