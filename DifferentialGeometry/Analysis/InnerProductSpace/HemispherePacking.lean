import Mathlib.Geometry.Euclidean.Angle.Unoriented.Basic
import Mathlib.Analysis.InnerProductSpace.Continuous
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.Tactic.Linarith

set_option autoImplicit false

open Filter Topology
open scoped BigOperators Topology

namespace InnerProductGeometry

theorem linearIndependent_of_inner_pos_of_pairwise_inner_nonpos
    {ι E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (v : ι → E) (u : E) (hpos : ∀ i, 0 < inner ℝ u (v i))
    (hpair : ∀ i j, i ≠ j → inner ℝ (v i) (v j) ≤ 0) :
    LinearIndependent ℝ v := by
  classical
  apply linearIndependent_iff'.mpr
  intro s c hsum i hi
  let a : ι → ℝ := fun j => max (c j) 0
  let b : ι → ℝ := fun j => max (-c j) 0
  have ha (j) : 0 ≤ a j := le_max_right _ _
  have hb (j) : 0 ≤ b j := le_max_right _ _
  have hab (j) : a j - b j = c j := by
    dsimp [a, b]
    rcases le_total 0 (c j) with hj | hj
    · rw [max_eq_left hj, max_eq_right (neg_nonpos.mpr hj)]
      ring
    · rw [max_eq_right hj, max_eq_left (neg_nonneg.mpr hj)]
      ring
  have hprod (j) : a j * b j = 0 := by
    dsimp [a, b]
    rcases le_total 0 (c j) with hj | hj
    · rw [max_eq_right (neg_nonpos.mpr hj), mul_zero]
    · rw [max_eq_right hj, zero_mul]
  let A : E := ∑ j ∈ s, a j • v j
  let B : E := ∑ j ∈ s, b j • v j
  have heq : A = B := by
    apply sub_eq_zero.mp
    dsimp [A, B]
    rw [← Finset.sum_sub_distrib]
    simp_rw [← sub_smul, hab]
    exact hsum
  have hinner : inner ℝ A B ≤ 0 := by
    dsimp [A, B]
    rw [sum_inner]
    apply Finset.sum_nonpos
    intro j hj
    rw [inner_sum]
    apply Finset.sum_nonpos
    intro k hk
    rw [real_inner_smul_left, inner_smul_right]
    by_cases hjk : j = k
    · subst k
      rw [← mul_assoc, hprod, zero_mul]
    · exact mul_nonpos_of_nonneg_of_nonpos (ha j)
        (mul_nonpos_of_nonneg_of_nonpos (hb k) (hpair j k hjk))
  have hAzero : A = 0 := by
    apply (inner_self_eq_zero (𝕜 := ℝ)).mp
    apply le_antisymm
    · rwa [← heq] at hinner
    · exact real_inner_self_nonneg
  have hBzero : B = 0 := heq.symm.trans hAzero
  have hazero : a i = 0 := by
    have h := congrArg (fun x : E => inner ℝ u x) hAzero
    dsimp [A] at h
    rw [inner_sum, inner_zero_right] at h
    simp only [inner_smul_right] at h
    have hh := Finset.single_le_sum
      (fun j (_ : j ∈ s) => mul_nonneg (ha j) (hpos j).le) hi
    rw [h] at hh
    nlinarith [hpos i, ha i]
  have hbzero : b i = 0 := by
    have h := congrArg (fun x : E => inner ℝ u x) hBzero
    dsimp [B] at h
    rw [inner_sum, inner_zero_right] at h
    simp only [inner_smul_right] at h
    have hh := Finset.single_le_sum
      (fun j (_ : j ∈ s) => mul_nonneg (hb j) (hpos j).le) hi
    rw [h] at hh
    nlinarith [hpos i, hb i]
  rw [← hab i, hazero, hbzero, sub_zero]

theorem card_le_finrank_of_pairwise_inner_neg_of_inner_nonneg
    {ι E : Type*} [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [Module.Finite ℝ E] (v : ι → E) (u : E) (hu : u ≠ 0)
    (hside : ∀ i, 0 ≤ inner ℝ u (v i))
    (hpair : ∀ i j, i ≠ j → inner ℝ (v i) (v j) < 0) :
    Fintype.card ι ≤ Module.finrank ℝ E := by
  have hevent : ∀ᶠ t : ℝ in 𝓝 0, ∀ i j, i ≠ j →
      inner ℝ (v i + t • u) (v j + t • u) < 0 := by
    apply eventually_all.mpr
    intro i
    apply eventually_all.mpr
    intro j
    by_cases hij : i = j
    · exact Filter.Eventually.of_forall (fun _ h => (h hij).elim)
    have hc : Continuous (fun t : ℝ => inner ℝ (v i + t • u) (v j + t • u)) :=
      (continuous_const.add (continuous_id.smul continuous_const)).inner
        (continuous_const.add (continuous_id.smul continuous_const))
    have hh : inner ℝ (v i + (0 : ℝ) • u) (v j + (0 : ℝ) • u) < 0 := by
      simpa only [zero_smul, add_zero] using hpair i j hij
    filter_upwards [hc.continuousAt.eventually (gt_mem_nhds hh)] with t ht _ using ht
  have hevent' : ∀ᶠ t : ℝ in 𝓝[>] 0, ∀ i j, i ≠ j →
      inner ℝ (v i + t • u) (v j + t • u) < 0 :=
    hevent.filter_mono nhdsWithin_le_nhds
  have hpositive : ∀ᶠ t : ℝ in 𝓝[>] 0, 0 < t := self_mem_nhdsWithin
  obtain ⟨t, ht, hp⟩ := (hpositive.and hevent').exists
  have hpos (i) : 0 < inner ℝ u (v i + t • u) := by
    rw [inner_add_right, inner_smul_right]
    exact add_pos_of_nonneg_of_pos (hside i)
      (mul_pos ht (real_inner_self_pos.mpr hu))
  exact (linearIndependent_of_inner_pos_of_pairwise_inner_nonpos
    (fun i => v i + t • u) u hpos (fun i j hij => (hp i j hij).le)).fintype_card_le_finrank

theorem card_le_finrank_of_separated_inner_bounds
    {ι E : Type*} [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [Module.Finite ℝ E] (v : ι → E) (u : E) (hu : ‖u‖ = 1)
    (hv : ∀ i, ‖v i‖ ≤ 1) {s : ℝ} (hs : 0 ≤ s)
    (hside : ∀ i, inner ℝ u (v i) < s)
    (hpair : ∀ i j, i ≠ j → inner ℝ (v i) (v j) < -s) :
    Fintype.card ι ≤ Module.finrank ℝ E := by
  let a : ι → ℝ := fun i => inner ℝ u (v i)
  let w : ι → E := fun i => v i - max (a i) 0 • u
  have huu : inner ℝ u u = 1 := by rw [real_inner_self_eq_norm_sq, hu]; norm_num
  have hu' : -u ≠ 0 := by
    intro h
    have hz : u = 0 := neg_eq_zero.mp h
    rw [hz, norm_zero] at hu
    norm_num at hu
  have ha (i) : -1 ≤ a i := by
    have hh := abs_real_inner_le_norm u (v i)
    rw [hu, one_mul] at hh
    exact neg_le_of_abs_le (hh.trans (hv i))
  have hwside (i) : 0 ≤ inner ℝ (-u) (w i) := by
    dsimp [w]
    rw [inner_neg_left, inner_sub_right, inner_smul_right, huu, mul_one]
    change 0 ≤ -(a i - max (a i) 0)
    linarith [le_max_left (a i) 0]
  have hwpair (i j) (hij : i ≠ j) : inner ℝ (w i) (w j) < 0 := by
    have heq : inner ℝ (w i) (w j) = inner ℝ (v i) (v j) -
        max (a j) 0 * a i - max (a i) 0 * a j + max (a i) 0 * max (a j) 0 := by
      dsimp [w, a]
      rw [inner_sub_left, inner_sub_right, inner_smul_right,
        real_inner_smul_left, inner_sub_right, inner_smul_right, huu,
        real_inner_comm (v i) u]
      ring
    rw [heq]
    by_cases hi : 0 ≤ a i
    · rw [max_eq_left hi]
      by_cases hj : 0 ≤ a j
      · rw [max_eq_left hj]
        nlinarith [hpair i j hij]
      · rw [max_eq_right (le_of_not_ge hj)]
        have hab : a i * a j ≥ -a i := by nlinarith [ha j]
        have hh := hside i
        change a i < s at hh
        nlinarith [hpair i j hij]
    · rw [max_eq_right (le_of_not_ge hi)]
      by_cases hj : 0 ≤ a j
      · rw [max_eq_left hj]
        have hab : a j * a i ≥ -a j := by nlinarith [ha i]
        have hh := hside j
        change a j < s at hh
        nlinarith [hpair i j hij]
      · rw [max_eq_right (le_of_not_ge hj)]
        nlinarith [hpair i j hij]
  exact card_le_finrank_of_pairwise_inner_neg_of_inner_nonneg w (-u) hu' hwside hwpair

theorem card_le_finrank_of_angle_separation
    {ι E : Type*} [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [Module.Finite ℝ E] (v : ι → E) (u : E) (hu : ‖u‖ = 1)
    (hv : ∀ i, ‖v i‖ = 1) {θ : ℝ} (hθ : 0 ≤ θ) (hθpi : θ ≤ Real.pi / 2)
    (hside : ∀ i, Real.pi / 2 - θ < angle u (v i))
    (hpair : ∀ i j, i ≠ j → Real.pi / 2 + θ < angle (v i) (v j)) :
    Fintype.card ι ≤ Module.finrank ℝ E := by
  apply card_le_finrank_of_separated_inner_bounds v u hu (fun i => (hv i).le)
    (Real.sin_nonneg_of_nonneg_of_le_pi hθ (by linarith [Real.pi_pos]))
  · intro i
    have hh := Real.cos_lt_cos_of_nonneg_of_le_pi (by linarith : 0 ≤ Real.pi / 2 - θ)
      (angle_le_pi u (v i)) (hside i)
    simpa only [cos_angle, hu, hv, mul_one, div_one, Real.cos_pi_div_two_sub] using hh
  · intro i j hij
    have hh := Real.cos_lt_cos_of_nonneg_of_le_pi (by positivity : 0 ≤ Real.pi / 2 + θ)
      (angle_le_pi (v i) (v j)) (hpair i j hij)
    simpa only [cos_angle, hv, mul_one, div_one, Real.cos_add, Real.cos_pi_div_two, Real.sin_pi_div_two, zero_mul, one_mul, zero_sub] using hh

end InnerProductGeometry
