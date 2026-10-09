import DifferentialGeometry.Analysis.Calculus.Resolvent
import Mathlib.Analysis.Calculus.ContDiff.Bounds

set_option autoImplicit false

noncomputable section

open scoped BigOperators NNReal

variable {𝕜 R E A : Type*} [NontriviallyNormedField 𝕜] [CommSemiring R]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedRing A] [NormedAlgebra 𝕜 A] [Algebra R A] [CompleteSpace A]

theorem norm_iteratedFDeriv_succ_resolvent_le
    {U : Set E} (hU : IsOpen U) {f : E → A} (n : ℕ)
    (hf : ContDiffOn 𝕜 (n + 1) f U) {μ : R}
    (hμ : ∀ y ∈ U, μ ∈ resolventSet R (f y)) {x : E} (hx : x ∈ U) :
    ‖iteratedFDeriv 𝕜 (n + 1) (fun y => resolvent (f y) μ) x‖ ≤
      ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) *
        (∑ j ∈ Finset.range (i + 1), (i.choose j : ℝ) *
          ‖iteratedFDeriv 𝕜 j (fun y => resolvent (f y) μ) x‖ *
          ‖iteratedFDeriv 𝕜 (i - j) (fun y => resolvent (f y) μ) x‖) *
        ‖iteratedFDeriv 𝕜 (n - i + 1) f x‖ := by
  let g := fun y => resolvent (f y) μ
  let B := ContinuousLinearMap.mulLeftRight 𝕜 A
  let M := fun y => B (g y) (g y)
  have hfn : ContDiffOn 𝕜 n f U := hf.of_le (by exact_mod_cast Nat.le_succ n)
  have hg : ContDiffOn 𝕜 n g U := hfn.resolvent hμ
  have hdf : ContDiffOn 𝕜 n (fderiv 𝕜 f) U := hf.fderiv_of_isOpen hU (by simp)
  have hM : ContDiffOn 𝕜 n M U := (B.contDiff.comp_contDiffOn hg).clm_apply hg
  have heq : Set.EqOn (fderiv 𝕜 g) (fun y => (M y).comp (fderiv 𝕜 f y)) U := by
    intro y hy
    have hfy : DifferentiableAt 𝕜 f y :=
      (hf.differentiableOn (by simp) y hy).differentiableAt (hU.mem_nhds hy)
    exact (hfy.hasFDerivAt.resolvent (hμ y hy)).fderiv
  have hprod := (ContinuousLinearMap.compL 𝕜 E A A).norm_iteratedFDerivWithin_le_of_bilinear_of_le_one
    hM hdf hU.uniqueDiffOn hx (n := n) le_rfl (ContinuousLinearMap.norm_compL_le 𝕜 E A A)
  rw [← norm_iteratedFDeriv_fderiv, ← iteratedFDerivWithin_of_isOpen n hU hx,
    iteratedFDerivWithin_congr heq hx n]
  apply hprod.trans
  apply Finset.sum_le_sum
  intro i hi
  have hin : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  have hm := B.norm_iteratedFDerivWithin_le_of_bilinear_of_le_one hg hg hU.uniqueDiffOn hx
    (n := i) (by exact_mod_cast hin) (ContinuousLinearMap.opNorm_mulLeftRight_le 𝕜 A)
  have hnorm : ‖iteratedFDerivWithin 𝕜 (n - i) (fderiv 𝕜 f) U x‖ =
      ‖iteratedFDeriv 𝕜 (n - i + 1) f x‖ := by
    rw [iteratedFDerivWithin_of_isOpen (n - i) hU hx, norm_iteratedFDeriv_fderiv]
  rw [hnorm]
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  simpa only [iteratedFDerivWithin_of_isOpen _ hU hx] using hm

def resolventDerivativeBound (K B : ℝ≥0) : ℕ → ℝ≥0
  | 0 => K
  | n + 1 => max (resolventDerivativeBound K B n)
      (3 ^ n * B * (resolventDerivativeBound K B n) ^ 2)

theorem resolventDerivativeBound_mono (K B : ℝ≥0) : Monotone (resolventDerivativeBound K B) :=
  monotone_nat_of_le_succ (fun _ => le_max_left _ _)

theorem norm_iteratedFDeriv_resolvent_le_of_small_derivatives
    {U : Set E} (hU : IsOpen U) {f : E → A} {m : ℕ}
    (hf : ContDiffOn 𝕜 m f U) {μ : R}
    (hμ : ∀ y ∈ U, μ ∈ resolventSet R (f y)) {x : E} (hx : x ∈ U)
    {δ σ : ℝ} (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) (hσ : 0 ≤ σ) (K B : ℝ≥0)
    (hR : ‖resolvent (f x) μ‖ ≤ K)
    (hD : ∀ j, 1 ≤ j → j ≤ m → ‖iteratedFDeriv 𝕜 j f x‖ ≤ δ * B * σ ^ j) :
    ∀ n, 1 ≤ n → n ≤ m →
      ‖iteratedFDeriv 𝕜 n (fun y => resolvent (f y) μ) x‖ ≤
        δ * resolventDerivativeBound K B n * σ ^ n := by
  have hb : ∀ n, n ≤ m →
      ‖iteratedFDeriv 𝕜 n (fun y => resolvent (f y) μ) x‖ ≤
        resolventDerivativeBound K B n * σ ^ n ∧
      (1 ≤ n → ‖iteratedFDeriv 𝕜 n (fun y => resolvent (f y) μ) x‖ ≤
        δ * resolventDerivativeBound K B n * σ ^ n) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro hnm
      cases n with
      | zero =>
        refine ⟨?_, by omega⟩
        simpa only [norm_iteratedFDeriv_zero, resolventDerivativeBound, pow_zero, mul_one] using hR
      | succ n =>
        let C : ℝ := resolventDerivativeBound K B n
        have hC : 0 ≤ C := NNReal.coe_nonneg _
        have hlow (j : ℕ) (hj : j ≤ n) :
            ‖iteratedFDeriv 𝕜 j (fun y => resolvent (f y) μ) x‖ ≤ C * σ ^ j := by
          apply ((ih j (by omega) (by omega)).1).trans
          exact mul_le_mul_of_nonneg_right (by exact_mod_cast resolventDerivativeBound_mono K B hj)
            (pow_nonneg hσ j)
        have hchoose (i : ℕ) : (∑ j ∈ Finset.range (i + 1), (i.choose j : ℝ)) = 2 ^ i := by
          exact_mod_cast Nat.sum_range_choose i
        have hpair (i : ℕ) (hi : i ≤ n) :
            (∑ j ∈ Finset.range (i + 1), (i.choose j : ℝ) *
              ‖iteratedFDeriv 𝕜 j (fun y => resolvent (f y) μ) x‖ *
              ‖iteratedFDeriv 𝕜 (i - j) (fun y => resolvent (f y) μ) x‖) ≤
                2 ^ i * C ^ 2 * σ ^ i := by
          calc
            _ ≤ ∑ j ∈ Finset.range (i + 1), (i.choose j : ℝ) * (C ^ 2 * σ ^ i) := by
              apply Finset.sum_le_sum
              intro j hj
              have hji : j ≤ i := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
              calc
                _ ≤ (i.choose j : ℝ) * (C * σ ^ j) * (C * σ ^ (i - j)) := by
                  gcongr
                  · exact hlow j (hji.trans hi)
                  · exact hlow (i - j) ((Nat.sub_le i j).trans hi)
                _ = ((i.choose j : ℝ) * C ^ 2) * (σ ^ j * σ ^ (i - j)) := by ring
                _ = (i.choose j : ℝ) * (C ^ 2 * σ ^ i) := by
                  rw [← pow_add, Nat.add_sub_of_le hji]
                  ring
            _ = 2 ^ i * C ^ 2 * σ ^ i := by rw [← Finset.sum_mul, hchoose]; ring
        have hsum : (∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * 2 ^ i) = (3 : ℝ) ^ n := by
          have hh := add_pow (2 : ℝ) 1 n
          norm_num only [one_pow, mul_one, show (2 : ℝ) + 1 = 3 by norm_num] at hh
          simpa only [mul_comm] using hh.symm
        have hbound : ‖iteratedFDeriv 𝕜 (n + 1) (fun y => resolvent (f y) μ) x‖ ≤
            δ * (3 ^ n * B * C ^ 2) * σ ^ (n + 1) := by
          apply (norm_iteratedFDeriv_succ_resolvent_le hU n
            (hf.of_le (by exact_mod_cast hnm)) hμ hx).trans
          calc
            _ ≤ ∑ i ∈ Finset.range (n + 1), ((n.choose i : ℝ) * 2 ^ i) *
                (δ * B * C ^ 2 * σ ^ (n + 1)) := by
              apply Finset.sum_le_sum
              intro i hi
              have hin : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
              calc
                _ ≤ (n.choose i : ℝ) * (2 ^ i * C ^ 2 * σ ^ i) *
                    (δ * B * σ ^ (n - i + 1)) := by
                  gcongr
                  · exact hpair i hin
                  · exact hD (n - i + 1) (by omega) (by omega)
                _ = ((n.choose i : ℝ) * 2 ^ i) * (δ * B * C ^ 2) *
                    (σ ^ i * σ ^ (n - i + 1)) := by ring
                _ = ((n.choose i : ℝ) * 2 ^ i) * (δ * B * C ^ 2 * σ ^ (n + 1)) := by
                  rw [← pow_add, show i + (n - i + 1) = n + 1 by omega]
                  ring
            _ = δ * (3 ^ n * B * C ^ 2) * σ ^ (n + 1) := by
              rw [← Finset.sum_mul, hsum]
              ring
        have hstep : (3 : ℝ) ^ n * B * C ^ 2 ≤ resolventDerivativeBound K B (n + 1) := by
          dsimp only [C, resolventDerivativeBound]
          exact_mod_cast (le_max_right (resolventDerivativeBound K B n)
            ((3 : ℝ≥0) ^ n * B * (resolventDerivativeBound K B n) ^ (2 : ℕ)))
        have hsmall := hbound.trans (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hstep hδ) (pow_nonneg hσ (n + 1)))
        refine ⟨hsmall.trans ?_, fun _ => hsmall⟩
        apply mul_le_mul_of_nonneg_right _ (pow_nonneg hσ (n + 1))
        simpa only [one_mul] using (mul_le_mul_of_nonneg_right hδ1
          (NNReal.coe_nonneg (resolventDerivativeBound K B (n + 1))))
  intro n hn hnm
  exact (hb n hnm).2 hn
