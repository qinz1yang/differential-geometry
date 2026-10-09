import DifferentialGeometry.Analysis.Calculus.IteratedDerivative.ResolventBounds

set_option autoImplicit false

noncomputable section

open scoped BigOperators NNReal Topology

namespace DifferentialGeometry.Analysis

theorem sum_norm_iteratedFDeriv_normalized_weights_le
    {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (S : Finset ι) {U : Set E} (hU : IsOpen U)
    {φ : ι → E → ℝ} {m : ℕ}
    (hφ : ∀ i ∈ S, ContDiffOn ℝ m (φ i) U)
    (hden : ∀ y ∈ U, 1 ≤ ∑ i ∈ S, φ i y)
    {x : E} (hx : x ∈ U) (B : ℝ≥0) {σ : ℝ} (hσ : 0 ≤ σ)
    (hjet : ∀ j, j ≤ m → (∑ i ∈ S, ‖iteratedFDeriv ℝ j (φ i) x‖) ≤ B * σ ^ j) :
    ∀ n, n ≤ m →
      (∑ i ∈ S, ‖iteratedFDeriv ℝ n
        (fun y => φ i y / (∑ k ∈ S, φ k y)) x‖) ≤
          (2 : ℝ) ^ n * B * resolventDerivativeBound 1 B n * σ ^ n := by
  classical
  let d : E → ℝ := fun y => ∑ i ∈ S, φ i y
  let f : E → ℝ := fun y => -d y
  let v : E → ℝ := fun y => (d y)⁻¹
  have hd : ContDiffOn ℝ m d U := ContDiffOn.sum (fun i hi => hφ i hi)
  have hf : ContDiffOn ℝ m f U := hd.neg
  have hdpos (y : E) (hy : y ∈ U) : 0 < d y := lt_of_lt_of_le zero_lt_one (hden y hy)
  have hv : ContDiffOn ℝ m v U := hd.inv (fun y hy => (hdpos y hy).ne')
  have hres (y : E) : resolvent (f y) (0 : ℝ) = v y := by
    simp only [resolvent, f, v, map_zero, zero_sub, neg_neg, Ring.inverse_eq_inv]
  have hμ (y : E) (hy : y ∈ U) : (0 : ℝ) ∈ resolventSet ℝ (f y) := by
    rw [spectrum.mem_resolventSet_iff]
    simpa only [f, map_zero, zero_sub, neg_neg] using
      (isUnit_iff_ne_zero.mpr (hdpos y hy).ne' : IsUnit (d y))
  have hvzero : ‖v x‖ ≤ 1 := by
    change ‖(d x)⁻¹‖ ≤ 1
    rw [norm_inv, Real.norm_eq_abs, abs_of_pos (hdpos x hx)]
    exact inv_le_one_of_one_le₀ (hden x hx)
  have hfjet (j : ℕ) (_hj : 1 ≤ j) (hjm : j ≤ m) :
      ‖iteratedFDeriv ℝ j f x‖ ≤ (1 : ℝ) * B * σ ^ j := by
    change ‖iteratedFDeriv ℝ j (-d) x‖ ≤ _
    rw [iteratedFDeriv_neg_apply, norm_neg]
    change ‖iteratedFDeriv ℝ j (fun y => ∑ i ∈ S, φ i y) x‖ ≤ _
    rw [iteratedFDeriv_fun_sum_apply
      (fun i hi => ((hφ i hi).contDiffAt (hU.mem_nhds hx)).of_le (by exact_mod_cast hjm))]
    simpa only [one_mul] using (norm_sum_le _ _).trans (hjet j hjm)
  have hvjet (j : ℕ) (hjm : j ≤ m) :
      ‖iteratedFDeriv ℝ j v x‖ ≤ (resolventDerivativeBound 1 B j : ℝ) * σ ^ j := by
    by_cases hj : j = 0
    · subst j
      simpa only [norm_iteratedFDeriv_zero, resolventDerivativeBound, NNReal.coe_one,
        pow_zero, mul_one] using hvzero
    · have h := norm_iteratedFDeriv_resolvent_le_of_small_derivatives
        (𝕜 := ℝ) (R := ℝ) hU hf hμ hx
        (by norm_num : (0 : ℝ) ≤ 1) (by norm_num : (1 : ℝ) ≤ 1) hσ 1 B
        (by simpa only [hres, NNReal.coe_one] using hvzero) hfjet j (by omega) hjm
      simpa only [hres, one_mul] using h
  intro n hnm
  let C : ℝ := resolventDerivativeBound 1 B n
  have hC : 0 ≤ C := NNReal.coe_nonneg _
  have hvlow (j : ℕ) (hjn : j ≤ n) : ‖iteratedFDeriv ℝ j v x‖ ≤ C * σ ^ j := by
    apply (hvjet j (hjn.trans hnm)).trans
    exact mul_le_mul_of_nonneg_right
      (by exact_mod_cast resolventDerivativeBound_mono 1 B hjn) (pow_nonneg hσ j)
  have hprod (i : ι) (hi : i ∈ S) :
      ‖iteratedFDeriv ℝ n (fun y => φ i y / (∑ k ∈ S, φ k y)) x‖ ≤
        ∑ j ∈ Finset.range (n + 1), (n.choose j : ℝ) *
          ‖iteratedFDeriv ℝ j (φ i) x‖ * ‖iteratedFDeriv ℝ (n - j) v x‖ := by
    have h := norm_iteratedFDerivWithin_mul_le (hφ i hi) hv hU.uniqueDiffOn hx
      (n := n) (by exact_mod_cast hnm)
    simpa only [iteratedFDerivWithin_of_isOpen _ hU hx, div_eq_mul_inv, v, d] using h
  calc
    _ ≤ ∑ i ∈ S, ∑ j ∈ Finset.range (n + 1), (n.choose j : ℝ) *
        ‖iteratedFDeriv ℝ j (φ i) x‖ * ‖iteratedFDeriv ℝ (n - j) v x‖ :=
      Finset.sum_le_sum hprod
    _ = ∑ j ∈ Finset.range (n + 1), (n.choose j : ℝ) *
        (∑ i ∈ S, ‖iteratedFDeriv ℝ j (φ i) x‖) *
          ‖iteratedFDeriv ℝ (n - j) v x‖ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j _hj
      rw [← Finset.sum_mul, ← Finset.mul_sum]
    _ ≤ ∑ j ∈ Finset.range (n + 1), (n.choose j : ℝ) * (B * C * σ ^ n) := by
      apply Finset.sum_le_sum
      intro j hj
      have hjn : j ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
      calc
        _ ≤ (n.choose j : ℝ) * (B * σ ^ j) * (C * σ ^ (n - j)) := by
          gcongr
          · exact hjet j (hjn.trans hnm)
          · exact hvlow (n - j) (Nat.sub_le n j)
        _ = ((n.choose j : ℝ) * B * C) * (σ ^ j * σ ^ (n - j)) := by ring
        _ = (n.choose j : ℝ) * (B * C * σ ^ n) := by
          rw [← pow_add, Nat.add_sub_of_le hjn]
          ring
    _ = (2 : ℝ) ^ n * B * resolventDerivativeBound 1 B n * σ ^ n := by
      have hchoose : (∑ j ∈ Finset.range (n + 1), (n.choose j : ℝ)) = 2 ^ n := by
        exact_mod_cast Nat.sum_range_choose n
      rw [← Finset.sum_mul, hchoose]
      dsimp only [C]
      ring

end DifferentialGeometry.Analysis
