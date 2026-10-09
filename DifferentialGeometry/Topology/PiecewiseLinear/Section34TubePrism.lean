/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.PolytopeSection
import DifferentialGeometry.Topology.PiecewiseLinear.BallGluing
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional

open Set Topology Metric

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

theorem exists_orthonormal_pair_of_ne_zero {d : E3} (hd : d ≠ 0) :
    ∃ e₁ e₂ : E3, inner ℝ e₁ d = 0 ∧ inner ℝ e₂ d = 0 ∧ ‖e₁‖ = 1 ∧ ‖e₂‖ = 1 ∧
      inner ℝ e₁ e₂ = 0 ∧
      ∀ y : E3, inner ℝ d y = 0 → ‖y‖ ≤ |inner ℝ e₁ y| + |inner ℝ e₂ y| := by
  have : Fact (Module.finrank ℝ E3 = 2 + 1) := ⟨by simp⟩
  have hK : Module.finrank ℝ (ℝ ∙ d)ᗮ = 2 := Submodule.finrank_orthogonal_span_singleton hd
  let b := (stdOrthonormalBasis ℝ (ℝ ∙ d)ᗮ).reindex (finCongr hK)
  have hperp : ∀ i, inner ℝ (b i : E3) d = 0 := fun i =>
    Submodule.mem_orthogonal_singleton_iff_inner_left.mp (b i).2
  have hnorm : ∀ i, ‖(b i : E3)‖ = 1 := fun i => b.orthonormal.1 i
  have horth : inner ℝ (b 0 : E3) (b 1 : E3) = 0 :=
    b.orthonormal.2 (show (0 : Fin 2) ≠ 1 by decide)
  refine ⟨b 0, b 1, hperp 0, hperp 1, hnorm 0, hnorm 1, horth, fun y hy => ?_⟩
  have hyK : y ∈ (ℝ ∙ d)ᗮ := Submodule.mem_orthogonal_singleton_iff_inner_right.mpr hy
  have hsum := congrArg (fun z : (ℝ ∙ d)ᗮ => (z : E3)) (b.sum_repr' ⟨y, hyK⟩)
  simp only [Fin.sum_univ_two, Submodule.coe_add, Submodule.coe_smul, Submodule.coe_inner]
    at hsum
  calc ‖y‖ = ‖inner ℝ (b 0 : E3) y • (b 0 : E3) + inner ℝ (b 1 : E3) y • (b 1 : E3)‖ := by
        rw [hsum]
    _ ≤ ‖inner ℝ (b 0 : E3) y • (b 0 : E3)‖ + ‖inner ℝ (b 1 : E3) y • (b 1 : E3)‖ :=
        norm_add_le _ _
    _ = |inner ℝ (b 0 : E3) y| + |inner ℝ (b 1 : E3) y| := by
        rw [norm_smul, norm_smul, hnorm 0, hnorm 1, Real.norm_eq_abs, Real.norm_eq_abs, mul_one,
          mul_one]

theorem exists_prism_decomposition {a w n n' e₁ e₂ x : E3} {μ L : ℝ}
    (he₁ : inner ℝ e₁ (w - a) = 0) (he₂ : inner ℝ e₂ (w - a) = 0)
    (hbound : ∀ y : E3, inner ℝ (w - a) y = 0 → ‖y‖ ≤ |inner ℝ e₁ y| + |inner ℝ e₂ y|)
    (hn : 0 < inner ℝ n (w - a)) (hn' : 0 < inner ℝ n' (w - a))
    (h1 : μ ≤ inner ℝ n (x - a)) (h2 : inner ℝ n' (x - w) ≤ 0)
    (h3 : inner ℝ e₁ (x - a) ≤ L) (h4 : inner ℝ e₂ (x - a) ≤ L)
    (h5 : -(inner ℝ e₁ (x - a) + inner ℝ e₂ (x - a)) ≤ L) :
    ∃ t : ℝ, ∃ y : E3, x - a = y + t • (w - a) ∧ ‖y‖ ≤ 4 * L ∧
      (μ - 4 * L * ‖n‖) / inner ℝ n (w - a) ≤ t ∧
      t ≤ 1 + 4 * L * ‖n'‖ / inner ℝ n' (w - a) := by
  set d := w - a with hd
  have hd0 : d ≠ 0 := by
    intro h
    rw [h, inner_zero_right] at hn
    exact lt_irrefl _ hn
  have hdd : 0 < inner ℝ d d := real_inner_self_pos.mpr hd0
  set t := inner ℝ d (x - a) / inner ℝ d d with ht
  set y := x - a - t • d with hy
  have hxy : x - a = y + t • d := by rw [hy]; abel
  have hdy : inner ℝ d y = 0 := by
    rw [hy, inner_sub_right, real_inner_smul_right, ht, div_mul_cancel₀ _ hdd.ne', sub_self]
  have hey : ∀ e : E3, inner ℝ e d = 0 → inner ℝ e y = inner ℝ e (x - a) := by
    intro e he
    rw [hxy, inner_add_right, real_inner_smul_right, he, mul_zero, add_zero]
  have hc₁ := hey e₁ he₁
  have hc₂ := hey e₂ he₂
  have hya : ‖y‖ ≤ 4 * L := by
    have hb := hbound y hdy
    rw [hc₁, hc₂] at hb
    have ha₁ : |inner ℝ e₁ (x - a)| ≤ 2 * L := abs_le.mpr ⟨by linarith, by linarith⟩
    have ha₂ : |inner ℝ e₂ (x - a)| ≤ 2 * L := abs_le.mpr ⟨by linarith, by linarith⟩
    linarith
  have hny : inner ℝ n y ≤ 4 * L * ‖n‖ := by
    have := real_inner_le_norm n y
    nlinarith [norm_nonneg n]
  have hny' : -(4 * L * ‖n'‖) ≤ inner ℝ n' y := by
    have := abs_real_inner_le_norm n' y
    have h' := neg_abs_le (inner ℝ n' y)
    nlinarith [norm_nonneg n']
  refine ⟨t, y, hxy, hya, ?_, ?_⟩
  · rw [div_le_iff₀ hn]
    have hsplit : inner ℝ n (x - a) = inner ℝ n y + t * inner ℝ n d := by
      rw [hxy, inner_add_right, real_inner_smul_right]
    linarith
  · have hxw : x - w = y + (t - 1) • d := by
      have h' : x - w = (x - a) - d := by rw [hd]; abel
      rw [h', hxy, sub_smul, one_smul]
      abel
    have hsplit : inner ℝ n' (x - w) = inner ℝ n' y + (t - 1) * inner ℝ n' d := by
      rw [hxw, inner_add_right, real_inner_smul_right]
    have hle : (t - 1) * inner ℝ n' d ≤ 4 * L * ‖n'‖ := by linarith
    have : t - 1 ≤ 4 * L * ‖n'‖ / inner ℝ n' d := by rw [le_div_iff₀ hn']; linarith
    linarith

theorem notMem_interior_of_forall_add_smul {S : Set E3} {x v : E3} {ε₀ : ℝ} (hε₀ : 0 < ε₀)
    (h : ∀ ε : ℝ, 0 < ε → ε < ε₀ → x + ε • v ∉ S) : x ∉ interior S := by
  intro hx
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp isOpen_interior x hx
  set ε := min (ε₀ / 2) (r / (2 * (‖v‖ + 1))) with hε
  have hε0 : 0 < ε := lt_min (half_pos hε₀) (div_pos hr (by positivity))
  have hε1 : ε < ε₀ := lt_of_le_of_lt (min_le_left _ _) (half_lt_self hε₀)
  apply h ε hε0 hε1
  apply interior_subset
  apply hball
  rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos hε0]
  calc ε * ‖v‖ ≤ r / (2 * (‖v‖ + 1)) * ‖v‖ := by
        gcongr
        exact min_le_right _ _
    _ < r := by
      rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
      nlinarith [norm_nonneg v]

theorem exists_inner_eq_zero_inner_pos {u m d : E3} (hu : u ≠ 0) (hud : inner ℝ u d = 0)
    (hmd : inner ℝ m d ≠ 0) : ∃ v : E3, inner ℝ m v = 0 ∧ 0 < inner ℝ u v := by
  have hm : m ≠ 0 := by
    rintro rfl
    exact hmd (inner_zero_left _)
  have hmm : 0 < inner ℝ m m := real_inner_self_pos.mpr hm
  set c := inner ℝ m u / inner ℝ m m with hc
  obtain ⟨v, hv⟩ : ∃ v : E3, v = u - c • m := ⟨_, rfl⟩
  have hmv : inner ℝ m v = 0 := by
    rw [hv, inner_sub_right, real_inner_smul_right, hc, div_mul_cancel₀ _ hmm.ne', sub_self]
  have hvv : inner ℝ v v = inner ℝ u v := by
    nth_rewrite 1 [hv]
    rw [inner_sub_left, real_inner_smul_left, hmv, mul_zero, sub_zero]
  have hv0 : v ≠ 0 := by
    intro h0
    have hum : u = c • m := by
      rw [h0] at hv
      exact (sub_eq_zero.mp hv.symm)
    rw [hum, real_inner_smul_left] at hud
    rcases mul_eq_zero.mp hud with hc0 | hc0
    · rw [hc0, zero_smul] at hum
      exact hu hum
    · exact hmd hc0
  exact ⟨v, hmv, hvv ▸ real_inner_self_pos.mpr hv0⟩

theorem inner_lt_of_mem_nhdsWithin {C : Set E3} {q u m : E3} {r c : ℝ}
    (hv : ∃ v : E3, inner ℝ m v = 0 ∧ 0 < inner ℝ u v) (hC : ∀ x ∈ C, inner ℝ u x ≤ c)
    (hqr : inner ℝ m q = r) (hq : inner ℝ u q ≤ c)
    (hnhds : C ∩ {x | inner ℝ m x = r} ∈ 𝓝[{x | inner ℝ m x = r}] q) : inner ℝ u q < c := by
  rcases hq.lt_or_eq with h | h
  · exact h
  exfalso
  obtain ⟨v, hmv, huv⟩ := hv
  obtain ⟨U, hU, hUsub⟩ := mem_nhdsWithin_iff_exists_mem_nhds_inter.mp hnhds
  obtain ⟨ε, hε, hεU⟩ := Metric.mem_nhds_iff.mp hU
  set t := ε / (2 * (‖v‖ + 1)) with ht
  have ht0 : 0 < t := div_pos hε (by positivity)
  have hxU : q + t • v ∈ U := by
    apply hεU
    rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos ht0,
      ht, div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
    nlinarith [norm_nonneg v]
  have hxm : q + t • v ∈ {x | inner ℝ m x = r} := by
    change inner ℝ m (q + t • v) = r
    rw [inner_add_right, real_inner_smul_right, hmv, mul_zero, add_zero, hqr]
  have hxC := (hUsub ⟨hxU, hxm⟩).1
  have hle := hC _ hxC
  rw [inner_add_right, real_inner_smul_right, h] at hle
  nlinarith

def thinPrism (a w n n' e₁ e₂ : E3) (μ L : ℝ) : Set E3 :=
  {x | μ ≤ inner ℝ n (x - a) ∧ inner ℝ n' (x - w) ≤ 0 ∧ inner ℝ e₁ (x - a) ≤ L ∧
    inner ℝ e₂ (x - a) ≤ L ∧ -(inner ℝ e₁ (x - a) + inner ℝ e₂ (x - a)) ≤ L}

theorem isHPolytope_thinPrism {a w n n' e₁ e₂ : E3} {μ L : ℝ}
    (he₁ : inner ℝ e₁ (w - a) = 0) (he₂ : inner ℝ e₂ (w - a) = 0)
    (hbound : ∀ y : E3, inner ℝ (w - a) y = 0 → ‖y‖ ≤ |inner ℝ e₁ y| + |inner ℝ e₂ y|)
    (hn : 0 < inner ℝ n (w - a)) (hn' : 0 < inner ℝ n' (w - a)) :
    IsHPolytope (thinPrism a w n n' e₁ e₂ μ L) := by
  let l : Fin 5 → E3 →ₗ[ℝ] ℝ := ![-(innerₗ E3 n), innerₗ E3 n', innerₗ E3 e₁, innerₗ E3 e₂,
    -(innerₗ E3 (e₁ + e₂))]
  let c : Fin 5 → ℝ := ![-μ - inner ℝ n a, inner ℝ n' w, L + inner ℝ e₁ a, L + inner ℝ e₂ a,
    L - inner ℝ (e₁ + e₂) a]
  have heq : thinPrism a w n n' e₁ e₂ μ L = {x | ∀ i, l i x ≤ c i} := by
    ext x
    simp only [thinPrism, mem_ofPred_eq, Fin.forall_fin_succ, IsEmpty.forall_iff, and_true, l, c,
      Matrix.cons_val_zero, Matrix.cons_val_succ, LinearMap.neg_apply, innerₗ_apply_apply,
      inner_sub_right, inner_add_left]
    constructor
    · rintro ⟨h1, h2, h3, h4, h5⟩
      exact ⟨by linarith, by linarith, by linarith, by linarith, by linarith⟩
    · rintro ⟨h1, h2, h3, h4, h5⟩
      exact ⟨by linarith, by linarith, by linarith, by linarith, by linarith⟩
  have hclosed : IsClosed (thinPrism a w n n' e₁ e₂ μ L) := by
    rw [heq, ofPred_forall]
    exact isClosed_iInter fun i =>
      isClosed_le (l i).continuous_of_finiteDimensional continuous_const
  set T := |(μ - 4 * L * ‖n‖) / inner ℝ n (w - a)| + |1 + 4 * L * ‖n'‖ / inner ℝ n' (w - a)|
    with hT
  have hbdd : Bornology.IsBounded (thinPrism a w n n' e₁ e₂ μ L) := by
    refine (isBounded_closedBall (x := a) (r := 4 * L + T * ‖w - a‖)).subset ?_
    rintro x ⟨h1, h2, h3, h4, h5⟩
    obtain ⟨t, y, hxy, hy, htl, htu⟩ :=
      exists_prism_decomposition he₁ he₂ hbound hn hn' h1 h2 h3 h4 h5
    rw [mem_closedBall, dist_eq_norm, hxy]
    have ht : |t| ≤ T := by
      rw [hT]
      rcases abs_cases t with ⟨h, -⟩ | ⟨h, -⟩
      · rw [h]
        exact le_add_of_nonneg_of_le (abs_nonneg _) (htu.trans (le_abs_self _))
      · rw [h]
        have := neg_abs_le ((μ - 4 * L * ‖n‖) / inner ℝ n (w - a))
        exact le_add_of_le_of_nonneg (by linarith) (abs_nonneg _)
    calc ‖y + t • (w - a)‖ ≤ ‖y‖ + |t| * ‖w - a‖ := by
          rw [← Real.norm_eq_abs, ← norm_smul]
          exact norm_add_le _ _
      _ ≤ 4 * L + T * ‖w - a‖ := by gcongr
  exact ⟨Metric.isCompact_of_isClosed_isBounded hclosed hbdd, Fin 5, inferInstance, l, c, heq⟩

theorem subset_interior_thinPrism (a w n n' e₁ e₂ : E3) (μ L : ℝ) :
    {x : E3 | μ < inner ℝ n (x - a) ∧ inner ℝ n' (x - w) < 0 ∧ inner ℝ e₁ (x - a) < L ∧
      inner ℝ e₂ (x - a) < L ∧ -(inner ℝ e₁ (x - a) + inner ℝ e₂ (x - a)) < L} ⊆
      interior (thinPrism a w n n' e₁ e₂ μ L) := by
  have hcont : ∀ (v b : E3), Continuous fun x : E3 => inner ℝ v (x - b) := fun v b =>
    continuous_const.inner (continuous_id.sub continuous_const)
  apply interior_maximal
  · rintro x ⟨h1, h2, h3, h4, h5⟩
    exact ⟨h1.le, h2.le, h3.le, h4.le, h5.le⟩
  · exact (isOpen_lt continuous_const (hcont n a)).inter
      ((isOpen_lt (hcont n' w) continuous_const).inter
      ((isOpen_lt (hcont e₁ a) continuous_const).inter ((isOpen_lt (hcont e₂ a)
        continuous_const).inter (isOpen_lt ((hcont e₁ a).add (hcont e₂ a)).neg continuous_const))))

theorem exists_dist_segment_le_of_mem_thinPrism {a w n n' e₁ e₂ x : E3} {L : ℝ}
    (he₁ : inner ℝ e₁ (w - a) = 0) (he₂ : inner ℝ e₂ (w - a) = 0)
    (hbound : ∀ y : E3, inner ℝ (w - a) y = 0 → ‖y‖ ≤ |inner ℝ e₁ y| + |inner ℝ e₂ y|)
    (hn : 0 < inner ℝ n (w - a)) (hn' : 0 < inner ℝ n' (w - a)) (hL : 0 ≤ L)
    (hx : x ∈ thinPrism a w n n' e₁ e₂ 0 L) :
    ∃ s ∈ segment ℝ a w, dist x s ≤
      (5 + (4 * ‖n‖ / inner ℝ n (w - a) + 4 * ‖n'‖ / inner ℝ n' (w - a)) * ‖w - a‖) * L := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := hx
  obtain ⟨t, y, hxy, hy, htl, htu⟩ :=
    exists_prism_decomposition he₁ he₂ hbound hn hn' h1 h2 h3 h4 h5
  set t' := max 0 (min t 1) with ht'
  have ht'I : t' ∈ Icc (0 : ℝ) 1 := ⟨le_max_left _ _, max_le zero_le_one (min_le_right _ _)⟩
  refine ⟨a + t' • (w - a), by rw [segment_eq_image']; exact ⟨t', ht'I, rfl⟩, ?_⟩
  have hA : 0 ≤ 4 * L * ‖n‖ / inner ℝ n (w - a) := div_nonneg (by positivity) hn.le
  have hB : 0 ≤ 4 * L * ‖n'‖ / inner ℝ n' (w - a) := div_nonneg (by positivity) hn'.le
  have hlow : -(4 * L * ‖n‖ / inner ℝ n (w - a)) ≤ t := by
    rw [zero_sub, neg_div] at htl
    exact htl
  have htt : |t - t'| ≤ 4 * L * ‖n‖ / inner ℝ n (w - a) + 4 * L * ‖n'‖ / inner ℝ n' (w - a) := by
    rcases le_or_gt t 0 with h0 | h0
    · have : t' = 0 := by rw [ht', min_eq_left (h0.trans zero_le_one), max_eq_left h0]
      rw [this, sub_zero, abs_of_nonpos h0]
      linarith
    · rcases le_or_gt t 1 with h1 | h1
      · have : t' = t := by rw [ht', min_eq_left h1, max_eq_right h0.le]
        rw [this, sub_self, abs_zero]
        linarith
      · have : t' = 1 := by rw [ht', min_eq_right h1.le, max_eq_right zero_le_one]
        rw [this, abs_of_pos (by linarith)]
        linarith
  have hxs : x - (a + t' • (w - a)) = y + (t - t') • (w - a) := by
    rw [sub_smul]
    calc x - (a + t' • (w - a)) = (x - a) - t' • (w - a) := by abel
      _ = y + (t • (w - a) - t' • (w - a)) := by rw [hxy]; abel
  rw [dist_eq_norm, hxs]
  have hnw := norm_nonneg (w - a)
  have hq : 0 ≤ (4 * ‖n‖ / inner ℝ n (w - a) + 4 * ‖n'‖ / inner ℝ n' (w - a)) := by
    have h1 : 0 ≤ 4 * ‖n‖ / inner ℝ n (w - a) := div_nonneg (by positivity) hn.le
    have h2 : 0 ≤ 4 * ‖n'‖ / inner ℝ n' (w - a) := div_nonneg (by positivity) hn'.le
    linarith
  calc ‖y + (t - t') • (w - a)‖ ≤ ‖y‖ + |t - t'| * ‖w - a‖ := by
        rw [← Real.norm_eq_abs, ← norm_smul]
        exact norm_add_le _ _
    _ ≤ 4 * L + (4 * L * ‖n‖ / inner ℝ n (w - a) + 4 * L * ‖n'‖ / inner ℝ n' (w - a)) *
        ‖w - a‖ := by gcongr
    _ = 4 * L + (4 * ‖n‖ / inner ℝ n (w - a) + 4 * ‖n'‖ / inner ℝ n' (w - a)) * ‖w - a‖ * L := by
        ring
    _ ≤ _ := by nlinarith

theorem norm_sub_le_of_mem_thinPrism {a w n n' e₁ e₂ x : E3} {μ L : ℝ}
    (he₁ : inner ℝ e₁ (w - a) = 0) (he₂ : inner ℝ e₂ (w - a) = 0)
    (hbound : ∀ y : E3, inner ℝ (w - a) y = 0 → ‖y‖ ≤ |inner ℝ e₁ y| + |inner ℝ e₂ y|)
    (hn : 0 < inner ℝ n (w - a)) (hn' : 0 < inner ℝ n' (w - a)) (hL : 0 ≤ L)
    (hx : x ∈ thinPrism a w n n' e₁ e₂ μ L) (h0 : inner ℝ n (x - a) = 0) :
    ‖x - a‖ ≤
      (5 + (4 * ‖n‖ / inner ℝ n (w - a) + 4 * ‖n'‖ / inner ℝ n' (w - a)) * ‖w - a‖) * L := by
  obtain ⟨-, h2, h3, h4, h5⟩ := hx
  obtain ⟨t, y, hxy, hy, -, -⟩ :=
    exists_prism_decomposition (μ := 0) he₁ he₂ hbound hn hn' h0.ge h2 h3 h4 h5
  have hsplit : inner ℝ n (x - a) = inner ℝ n y + t * inner ℝ n (w - a) := by
    rw [hxy, inner_add_right, real_inner_smul_right]
  have hny := abs_real_inner_le_norm n y
  have htn : |t| * inner ℝ n (w - a) ≤ ‖n‖ * (4 * L) := by
    have : |t * inner ℝ n (w - a)| = |inner ℝ n y| := by
      rw [abs_eq_abs]
      right
      linarith
    rw [abs_mul, abs_of_pos hn] at this
    rw [this]
    exact hny.trans (by gcongr)
  have ht : |t| ≤ 4 * L * ‖n‖ / inner ℝ n (w - a) := by
    rw [le_div_iff₀ hn]
    linarith
  have hB : 0 ≤ 4 * ‖n'‖ / inner ℝ n' (w - a) * ‖w - a‖ * L :=
    mul_nonneg (mul_nonneg (div_nonneg (by positivity) hn'.le) (norm_nonneg _)) hL
  rw [hxy]
  calc ‖y + t • (w - a)‖ ≤ ‖y‖ + |t| * ‖w - a‖ := by
        rw [← Real.norm_eq_abs, ← norm_smul]
        exact norm_add_le _ _
    _ ≤ 4 * L + 4 * L * ‖n‖ / inner ℝ n (w - a) * ‖w - a‖ := by gcongr
    _ = 4 * L + 4 * ‖n‖ / inner ℝ n (w - a) * ‖w - a‖ * L := by ring
    _ ≤ _ := by nlinarith

theorem exists_ball_subset_thinPrism {a w n n' e₁ e₂ : E3} {L : ℝ}
    (he₁ : inner ℝ e₁ (w - a) = 0) (he₂ : inner ℝ e₂ (w - a) = 0) (hn₁ : ‖e₁‖ = 1)
    (hn₂ : ‖e₂‖ = 1) (hn : 0 < inner ℝ n (w - a)) (hL : 0 < L) :
    ∃ ρ' > 0, ∀ x ∈ ball w ρ', inner ℝ n' (x - w) ≤ 0 → x ∈ thinPrism a w n n' e₁ e₂ 0 L := by
  set ρ' := min (L / 2) (inner ℝ n (w - a) / (2 * ‖n‖ + 1)) with hρ'
  have hρ'0 : 0 < ρ' := lt_min (half_pos hL) (div_pos hn (by positivity))
  refine ⟨ρ', hρ'0, fun x hxb hxt => ?_⟩
  have hxw : ‖x - w‖ < ρ' := by rw [← dist_eq_norm]; exact hxb
  have hxw2 : ‖x - w‖ < L / 2 := hxw.trans_le (min_le_left _ _)
  have hxw3 : ‖x - w‖ < inner ℝ n (w - a) / (2 * ‖n‖ + 1) := hxw.trans_le (min_le_right _ _)
  have hsplit : ∀ v : E3, inner ℝ v (x - a) = inner ℝ v (x - w) + inner ℝ v (w - a) := by
    intro v
    rw [← inner_add_right]
    congr 1
    abel
  have hb1 := abs_real_inner_le_norm e₁ (x - w)
  have hb2 := abs_real_inner_le_norm e₂ (x - w)
  have hbn := abs_real_inner_le_norm n (x - w)
  rw [hn₁, one_mul] at hb1
  rw [hn₂, one_mul] at hb2
  refine ⟨?_, hxt, ?_, ?_, ?_⟩
  · rw [hsplit]
    have h1 : ‖n‖ * ‖x - w‖ ≤ ‖n‖ * (inner ℝ n (w - a) / (2 * ‖n‖ + 1)) := by gcongr
    have h2 : ‖n‖ * (inner ℝ n (w - a) / (2 * ‖n‖ + 1)) ≤ inner ℝ n (w - a) := by
      rw [mul_div_assoc', div_le_iff₀ (by positivity)]
      nlinarith [norm_nonneg n]
    have := neg_abs_le (inner ℝ n (x - w))
    linarith
  · rw [hsplit, he₁, add_zero]
    have := le_abs_self (inner ℝ e₁ (x - w))
    linarith
  · rw [hsplit, he₂, add_zero]
    have := le_abs_self (inner ℝ e₂ (x - w))
    linarith
  · rw [hsplit, hsplit, he₁, he₂, add_zero, add_zero]
    have := neg_abs_le (inner ℝ e₁ (x - w))
    have := neg_abs_le (inner ℝ e₂ (x - w))
    linarith

theorem notMem_interior_thinPrism {a w n n' e₁ e₂ x : E3} {μ L : ℝ} (hn0 : n ≠ 0)
    (hx : inner ℝ n (x - a) = μ) : x ∉ interior (thinPrism a w n n' e₁ e₂ μ L) := by
  have hnn : 0 < inner ℝ n n := real_inner_self_pos.mpr hn0
  refine notMem_interior_of_forall_add_smul (v := -n) one_pos fun ε hε _ hmem => ?_
  obtain ⟨h1, -⟩ := hmem
  have : x + ε • -n - a = (x - a) - ε • n := by rw [smul_neg]; abel
  rw [this, inner_sub_right, hx, real_inner_smul_right] at h1
  nlinarith

theorem notMem_interior_thinPrism_of_inner_eq {a w n n' e₁ e₂ x : E3} {μ L : ℝ}
    (hn' : n' ≠ 0) (hx : inner ℝ n' (x - w) = 0) :
    x ∉ interior (thinPrism a w n n' e₁ e₂ μ L) := by
  have hnn : 0 < inner ℝ n' n' := real_inner_self_pos.mpr hn'
  refine notMem_interior_of_forall_add_smul (v := n') one_pos fun ε hε _ hmem => ?_
  obtain ⟨-, h2, -⟩ := hmem
  have : x + ε • n' - w = (x - w) + ε • n' := by abel
  rw [this, inner_add_right, hx, real_inner_smul_right] at h2
  nlinarith

theorem mem_interior_thinPrism_of_mem_nhdsWithin {a w n n' e₁ e₂ m q : E3} {μ L r : ℝ}
    (he₁ : inner ℝ e₁ (w - a) = 0) (he₂ : inner ℝ e₂ (w - a) = 0) (hn₁ : ‖e₁‖ = 1)
    (hn₂ : ‖e₂‖ = 1) (he₁₂ : inner ℝ e₁ e₂ = 0) (hmd : inner ℝ m (w - a) ≠ 0)
    (hq : q ∈ thinPrism a w n n' e₁ e₂ μ L) (hqr : inner ℝ m q = r)
    (hbot : μ < inner ℝ n (q - a)) (htop : inner ℝ n' (q - w) < 0)
    (hnhds : thinPrism a w n n' e₁ e₂ μ L ∩ {x | inner ℝ m x = r} ∈
      𝓝[{x | inner ℝ m x = r}] q) :
    q ∈ interior (thinPrism a w n n' e₁ e₂ μ L) := by
  have hlat : ∀ u : E3, u ≠ 0 → inner ℝ u (w - a) = 0 → ∀ c : ℝ,
      (∀ x ∈ thinPrism a w n n' e₁ e₂ μ L, inner ℝ u x ≤ c) → inner ℝ u q ≤ c →
      inner ℝ u q < c :=
    fun u hu hud c hCu hq' =>
      inner_lt_of_mem_nhdsWithin (exists_inner_eq_zero_inner_pos hu hud hmd) hCu hqr hq' hnhds
  have hne : ∀ e : E3, ‖e‖ = 1 → e ≠ 0 := fun e he h0 => by
    rw [h0, norm_zero] at he
    exact zero_ne_one he
  have he₃ : -(e₁ + e₂) ≠ 0 := by
    intro h0
    have h00 : inner ℝ (e₁ + e₂) (e₁ + e₂) = 0 := by
      rw [neg_eq_zero.mp h0, inner_zero_left]
    rw [inner_add_left, inner_add_right, inner_add_right, real_inner_self_eq_norm_sq,
      real_inner_self_eq_norm_sq, hn₁, hn₂, he₁₂, real_inner_comm, he₁₂] at h00
    norm_num at h00
  obtain ⟨-, -, hq3, hq4, hq5⟩ := hq
  have hq3' : inner ℝ e₁ q < L + inner ℝ e₁ a := by
    refine hlat e₁ (hne e₁ hn₁) he₁ _ (fun x hx => ?_) ?_
    · obtain ⟨-, -, h3, -⟩ := hx
      rw [inner_sub_right] at h3
      linarith
    · rw [inner_sub_right] at hq3
      linarith
  have hq4' : inner ℝ e₂ q < L + inner ℝ e₂ a := by
    refine hlat e₂ (hne e₂ hn₂) he₂ _ (fun x hx => ?_) ?_
    · obtain ⟨-, -, -, h4, -⟩ := hx
      rw [inner_sub_right] at h4
      linarith
    · rw [inner_sub_right] at hq4
      linarith
  have he₃d : inner ℝ (-(e₁ + e₂)) (w - a) = 0 := by
    rw [inner_neg_left, inner_add_left, he₁, he₂, add_zero, neg_zero]
  have hlin : ∀ x : E3, inner ℝ (-(e₁ + e₂)) x = -(inner ℝ e₁ x + inner ℝ e₂ x) := fun x => by
    rw [inner_neg_left, inner_add_left]
  have hq5' : inner ℝ (-(e₁ + e₂)) q < L - (inner ℝ e₁ a + inner ℝ e₂ a) := by
    refine hlat _ he₃ he₃d _ (fun x hx => ?_) ?_
    · obtain ⟨-, -, -, -, h5⟩ := hx
      rw [inner_sub_right, inner_sub_right] at h5
      rw [hlin]
      linarith
    · rw [inner_sub_right, inner_sub_right] at hq5
      rw [hlin]
      linarith
  rw [hlin] at hq5'
  apply subset_interior_thinPrism
  refine ⟨hbot, htop, ?_, ?_, ?_⟩
  · rw [inner_sub_right]
    linarith
  · rw [inner_sub_right]
    linarith
  · rw [inner_sub_right, inner_sub_right]
    linarith

theorem exists_isPLBall_union_prism {X V : Set E3} {a w n n' : E3} {ρ : ℝ} (hX : IsPLBall 3 X)
    (hρ : 0 < ρ) (hflat : X ∩ ball a ρ = {x | inner ℝ n (x - a) ≤ 0} ∩ ball a ρ)
    (hn : 0 < inner ℝ n (w - a)) (hn' : 0 < inner ℝ n' (w - a))
    (hseg : ∀ x ∈ segment ℝ a w, x ≠ a → x ∉ X) (hV : IsOpen V) (hsegV : segment ℝ a w ⊆ V) :
    ∃ C : Set E3, IsHPolytope C ∧ C ⊆ V ∧ C ⊆ {x | inner ℝ n' (x - w) ≤ 0} ∧
      openSegment ℝ a w ⊆ interior C ∧ IsPLBall 3 (X ∪ C) ∧
      (∃ ρ' > 0, (X ∪ C) ∩ ball w ρ' = {x | inner ℝ n' (x - w) ≤ 0} ∩ ball w ρ') ∧
      ∀ (m : E3) (r : ℝ), inner ℝ m (w - a) ≠ 0 → ∀ q ∈ C, inner ℝ m q = r →
        0 < inner ℝ n (q - a) → inner ℝ n' (q - w) < 0 →
        C ∩ {x | inner ℝ m x = r} ∈ 𝓝[{x | inner ℝ m x = r}] q → q ∈ interior C := by
  have hw : w ≠ a := by
    intro h
    rw [h, sub_self, inner_zero_right] at hn
    exact lt_irrefl _ hn
  have hn0 : n ≠ 0 := by
    rintro rfl
    rw [inner_zero_left] at hn
    exact lt_irrefl _ hn
  have hd0 : w - a ≠ 0 := sub_ne_zero.mpr hw
  obtain ⟨e₁, e₂, he₁, he₂, hn₁, hn₂, he₁₂, hbound⟩ := exists_orthonormal_pair_of_ne_zero hd0
  have he₁' : inner ℝ e₁ (w - a) = 0 := he₁
  have hXc : IsClosed X := hX.isPolyhedron.isClosed
  have hsegc : IsCompact (segment ℝ a w) := by
    rw [segment_eq_image']
    exact isCompact_Icc.image (by fun_prop)
  obtain ⟨δV, hδV, hδVsub⟩ := hsegc.exists_cthickening_subset_open hV hsegV
  have hK0 : IsCompact (segment ℝ a w \ ball a (ρ / 2)) := hsegc.diff isOpen_ball
  have hK0X : segment ℝ a w \ ball a (ρ / 2) ⊆ Xᶜ := by
    rintro x ⟨hx, hxb⟩
    refine hseg x hx fun h => hxb ?_
    rw [h]
    exact mem_ball_self (half_pos hρ)
  obtain ⟨δ0, hδ0, hδ0sub⟩ := hK0.exists_cthickening_subset_open hXc.isOpen_compl hK0X
  have hwX : w ∉ X := hseg w (right_mem_segment ℝ a w) hw
  obtain ⟨ρw, hρw, hρwX⟩ := Metric.isOpen_iff.mp hXc.isOpen_compl w hwX
  set K₁ := 5 + (4 * ‖n‖ / inner ℝ n (w - a) + 4 * ‖n'‖ / inner ℝ n' (w - a)) * ‖w - a‖
    with hK₁def
  have hK₁ : 0 < K₁ := by
    have h1 : 0 ≤ 4 * ‖n‖ / inner ℝ n (w - a) := div_nonneg (by positivity) hn.le
    have h2 : 0 ≤ 4 * ‖n'‖ / inner ℝ n' (w - a) := div_nonneg (by positivity) hn'.le
    have h3 := norm_nonneg (w - a)
    positivity
  set M := min (min δV δ0) ρ with hM
  have hM0 : 0 < M := lt_min (lt_min hδV hδ0) hρ
  set L := M / (4 * K₁) with hL
  have hL0 : 0 < L := div_pos hM0 (by positivity)
  have hKL : K₁ * L = M / 4 := by
    rw [hL]
    field_simp
  have hMδV : M ≤ δV := (min_le_left _ _).trans (min_le_left _ _)
  have hMδ0 : M ≤ δ0 := (min_le_left _ _).trans (min_le_right _ _)
  have hMρ : M ≤ ρ := min_le_right _ _
  set C := thinPrism a w n n' e₁ e₂ 0 L with hCdef
  have hC : IsHPolytope C := isHPolytope_thinPrism he₁ he₂ hbound hn hn'
  have hdist : ∀ x ∈ C, ∃ s ∈ segment ℝ a w, dist x s ≤ K₁ * L := fun x hx =>
    exists_dist_segment_le_of_mem_thinPrism he₁ he₂ hbound hn hn' hL0.le hx
  have hCV : C ⊆ V := by
    intro x hx
    obtain ⟨s, hs, hds⟩ := hdist x hx
    exact hδVsub (mem_cthickening_of_dist_le x s δV _ hs (by linarith))
  have hint : openSegment ℝ a w ⊆ interior C := by
    intro x hx
    rw [openSegment_eq_image'] at hx
    obtain ⟨t, ⟨ht0, ht1⟩, rfl⟩ := hx
    apply subset_interior_thinPrism
    have hxa : a + t • (w - a) - a = t • (w - a) := by abel
    have hxw : a + t • (w - a) - w = (t - 1) • (w - a) := by rw [sub_smul, one_smul]; abel
    simp only [mem_ofPred_eq, hxa, hxw, real_inner_smul_right, he₁, he₂, mul_zero, add_zero,
      neg_zero]
    exact ⟨mul_pos ht0 hn, mul_neg_of_neg_of_pos (by linarith) hn', hL0, hL0, hL0⟩
  have hCball : IsPLBall 3 C := by
    have hmid : a + (1 / 2 : ℝ) • (w - a) ∈ openSegment ℝ a w := by
      rw [openSegment_eq_image']
      exact ⟨1 / 2, ⟨by norm_num, by norm_num⟩, rfl⟩
    have := hC.isPLBall ⟨_, hint hmid⟩
    rwa [finrank_euclideanSpace_fin] at this
  have hXC : ∀ x ∈ X ∩ C, x ∈ ball a ρ ∧ inner ℝ n (x - a) = 0 := by
    rintro x ⟨hxX, hxC⟩
    by_cases hxb : x ∈ ball a ρ
    · have h := (hflat.subset ⟨hxX, hxb⟩).1
      obtain ⟨h1, -⟩ := hxC
      exact ⟨hxb, le_antisymm h h1⟩
    · exfalso
      obtain ⟨s, hs, hds⟩ := hdist x hxC
      have hsa : s ∉ ball a (ρ / 2) := by
        intro hsb
        rw [mem_ball] at hsb
        apply hxb
        rw [mem_ball]
        have := dist_triangle x s a
        linarith
      exact hδ0sub (mem_cthickening_of_dist_le x s δ0 _ ⟨hs, hsa⟩ (by linarith)) hxX
  have hC₁ : IsHPolytope (thinPrism a w n n' e₁ e₂ (-1) L) :=
    isHPolytope_thinPrism he₁ he₂ hbound hn hn'
  have hℓ : innerₗ E3 n ≠ 0 := by
    intro h
    have h' := congrArg (fun f : E3 →ₗ[ℝ] ℝ => f (w - a)) h
    simp only [innerₗ_apply_apply, LinearMap.zero_apply] at h'
    linarith
  have haint : a ∈ interior (thinPrism a w n n' e₁ e₂ (-1) L) ∩
      {x | innerₗ E3 n x = inner ℝ n a} := by
    refine ⟨subset_interior_thinPrism a w n n' e₁ e₂ (-1) L ?_, by simp⟩
    have haw : a - w = -(w - a) := by abel
    simp only [mem_ofPred_eq, sub_self, inner_zero_right, haw, inner_neg_right, neg_zero,
      add_zero]
    exact ⟨by norm_num, by linarith, hL0, hL0, hL0⟩
  have hB2 := hC₁.isPLBall_inter_fiber (n := 2) (by simp) (innerₗ E3 n) hℓ ⟨a, haint⟩
  have hXCeq : X ∩ C = thinPrism a w n n' e₁ e₂ (-1) L ∩ {x | innerₗ E3 n x = inner ℝ n a} := by
    ext x
    constructor
    · intro hx
      obtain ⟨-, h0⟩ := hXC x hx
      obtain ⟨-, ⟨-, h2, h3, h4, h5⟩⟩ := hx
      refine ⟨⟨by linarith, h2, h3, h4, h5⟩, ?_⟩
      change inner ℝ n x = inner ℝ n a
      rw [inner_sub_right] at h0
      linarith
    · rintro ⟨hx₁, hfib⟩
      change inner ℝ n x = inner ℝ n a at hfib
      have h0 : inner ℝ n (x - a) = 0 := by rw [inner_sub_right, hfib, sub_self]
      have hxa := norm_sub_le_of_mem_thinPrism he₁ he₂ hbound hn hn' hL0.le hx₁ h0
      have hxb : x ∈ ball a ρ := by
        rw [mem_ball, dist_eq_norm]
        linarith
      obtain ⟨-, h2, h3, h4, h5⟩ := hx₁
      exact ⟨(hflat.symm.subset ⟨h0.le, hxb⟩).1, h0.ge, h2, h3, h4, h5⟩
  have hBfX : X ∩ C ⊆ frontier X := by
    intro x hx
    obtain ⟨hxb, h0⟩ := hXC x hx
    refine ⟨subset_closure hx.1, ?_⟩
    have hnn : 0 < inner ℝ n n := real_inner_self_pos.mpr hn0
    have hdx : 0 < ρ - dist x a := sub_pos.mpr (mem_ball.mp hxb)
    refine notMem_interior_of_forall_add_smul (v := n) (ε₀ := (ρ - dist x a) / (‖n‖ + 1))
      (div_pos hdx (by positivity)) fun ε hε hεlt hmem => ?_
    have hmemb : x + ε • n ∈ ball a ρ := by
      rw [mem_ball]
      calc dist (x + ε • n) a ≤ dist (x + ε • n) x + dist x a := dist_triangle _ _ _
        _ = ε * ‖n‖ + dist x a := by
          rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos hε]
        _ < ρ := by
          rw [lt_div_iff₀ (by positivity)] at hεlt
          nlinarith [norm_nonneg n]
    have hle := (hflat.subset ⟨hmem, hmemb⟩).1
    change inner ℝ n (x + ε • n - a) ≤ 0 at hle
    have : x + ε • n - a = (x - a) + ε • n := by abel
    rw [this, inner_add_right, h0, real_inner_smul_right] at hle
    nlinarith
  have hBfC : X ∩ C ⊆ frontier C := fun x hx =>
    ⟨subset_closure hx.2, notMem_interior_thinPrism hn0 (hXC x hx).2⟩
  have hunion := isPLBall_union_of_inter_isPLBall_two hX hCball (hXCeq ▸ hB2) hBfX hBfC
  refine ⟨C, hC, hCV, fun x hx => hx.2.1, hint, hunion, ?_, ?_⟩
  · obtain ⟨ρ₁, hρ₁, hρ₁C⟩ := exists_ball_subset_thinPrism (n' := n') he₁ he₂ hn₁ hn₂ hn hL0
    refine ⟨min ρw ρ₁, lt_min hρw hρ₁, ?_⟩
    ext x
    constructor
    · rintro ⟨hx | hx, hxb⟩
      · exact absurd hx (hρwX (ball_subset_ball (min_le_left _ _) hxb))
      · exact ⟨hx.2.1, hxb⟩
    · rintro ⟨hxt, hxb⟩
      exact ⟨Or.inr (hρ₁C x (ball_subset_ball (min_le_right _ _) hxb) hxt), hxb⟩
  · intro m r hmd q hq hqr hbot htop hnhds
    exact mem_interior_thinPrism_of_mem_nhdsWithin he₁ he₂ hn₁ hn₂ he₁₂ hmd hq hqr hbot htop
      hnhds

end DifferentialGeometry.Topology.PiecewiseLinear
