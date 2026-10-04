import DifferentialGeometry.Analysis.InnerProductSpace.NormalGraphAffineRemainderJets

/-! Bounds for arbitrary higher graph coefficients in the affine normal equation. -/

set_option autoImplicit false
noncomputable section
open Set
open scoped BigOperators ContDiff

namespace DifferentialGeometry.Analysis

variable {E F Z : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z]

theorem norm_iteratedFDeriv_affine_normal_graph_remainder_le_unrestricted
    (g : E → F) (a : E) (A : Z →L[ℝ] E) (b : F) (B : Z →L[ℝ] F)
    (V : Set E) (hV : IsOpen V) (j : ℕ)
    (hg : ContDiffOn ℝ (j + 1 : ℕ) g V) (z : Z) (hz : a + A z ∈ V)
    (R ε K : ℝ) (hR : 0 < R) (hε0 : 0 ≤ ε)
    (hK : 1 ≤ K) (hA : ‖A‖ ≤ K) (hB : ‖B‖ ≤ 1)
    (hv : ‖b + B z‖ ≤ 2 * R)
    (hjet : ∀ i ≤ j + 1,
      ‖iteratedFDeriv ℝ i g (a + A z)‖ ≤ ε * R * (R⁻¹) ^ i) :
    ‖iteratedFDeriv ℝ j (fun y =>
      (ContinuousLinearMap.adjoint (fderiv ℝ g (a + A y)))
        (g (a + A y) - (b + B y))) z‖ ≤
      ((ε + 2) * (2 * K) ^ j) * ε * R * (R⁻¹) ^ j := by
  let U : Set Z := (fun y => a + A y) ⁻¹' V
  have hU : IsOpen U := hV.preimage (continuous_const.add A.continuous)
  have hzU : z ∈ U := hz
  have hK0 : 0 ≤ K := zero_le_one.trans hK
  have hσ : 0 ≤ R⁻¹ := inv_nonneg.mpr hR.le
  have hq : ContDiffOn ℝ (j + 1 : ℕ) (fun y => a + A y) U :=
    contDiffOn_const.add A.contDiff.contDiffOn
  have hcomp : ContDiffOn ℝ (j + 1 : ℕ) (fun y => g (a + A y)) U :=
    hg.comp hq (fun y hy => hy)
  have hvdiff : ContDiff ℝ (j : ℕ) (fun y => b + B y) :=
    contDiff_const.add B.contDiff
  have hvderiv : fderiv ℝ (fun y => b + B y) = fun y => B :=
    funext (fun y => ((B.hasFDerivAt (x := y)).const_add b).fderiv)
  have hgcomp (i : ℕ) (hi : i ≤ j + 1) :
      ‖iteratedFDeriv ℝ i (fun y => g (a + A y)) z‖ ≤
        ε * K ^ i * R * (R⁻¹) ^ i := by
    rw [iteratedFDeriv_comp_affine hV (hg.of_le (by exact_mod_cast hi)) a A hz]
    calc
      _ ≤ ‖iteratedFDeriv ℝ i g (a + A z)‖ * ∏ aidx : Fin i, ‖A‖ :=
        ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _
      _ = ‖iteratedFDeriv ℝ i g (a + A z)‖ * ‖A‖ ^ i := by simp
      _ ≤ (ε * R * (R⁻¹) ^ i) * K ^ i := by
        gcongr
        exact hjet i hi
      _ = _ := by ring
  have hvjet (i : ℕ) :
      ‖iteratedFDeriv ℝ i (fun y => b + B y) z‖ ≤
        2 * K ^ i * R * (R⁻¹) ^ i := by
    cases i with
    | zero => simpa only [norm_iteratedFDeriv_zero, pow_zero, mul_one] using hv
    | succ i =>
      cases i with
      | zero =>
        rw [norm_iteratedFDeriv_one, hvderiv]
        simpa only [Nat.zero_add, pow_one, mul_assoc, mul_inv_cancel₀ hR.ne', mul_one]
          using (hB.trans (by linarith : 1 ≤ 2 * K))
      | succ i =>
        rw [← norm_iteratedFDeriv_fderiv, hvderiv,
          iteratedFDeriv_const_of_ne (by omega), Pi.zero_apply, norm_zero]
        positivity
  have hres (i : ℕ) (hi : i ≤ j) :
      ‖iteratedFDeriv ℝ i (fun y => g (a + A y) - (b + B y)) z‖ ≤
        (ε + 2) * K ^ i * R * (R⁻¹) ^ i := by
    rw [fun_iteratedFDeriv_sub_apply
      ((hcomp.contDiffAt (hU.mem_nhds hzU)).of_le (by exact_mod_cast (by omega : i ≤ j + 1)))
      (hvdiff.contDiffAt.of_le (by exact_mod_cast hi))]
    have hh := (norm_sub_le _ _).trans
      (add_le_add (hgcomp i (by omega)) (hvjet i))
    convert hh using 1; ring
  have h := norm_iteratedFDeriv_affine_normal_graph_remainder_le g
    (fun y => b + B y) a A U V hU hV (fun y hy => hy) j hg hvdiff.contDiffOn z hzU
  apply h.trans
  calc
    _ ≤ ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) *
        ((ε + 2) * K ^ j * ε * R * (R⁻¹) ^ j) := by
      apply Finset.sum_le_sum
      intro i hi
      have hij : i ≤ j := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
      have hlead : ‖iteratedFDeriv ℝ (i + 1) g (a + A z)‖ * ‖A‖ ^ i ≤
          ε * K ^ i * (R⁻¹) ^ i := by
        calc
          _ ≤ (ε * R * (R⁻¹) ^ (i + 1)) * K ^ i := by
            gcongr
            exact hjet (i + 1) (by omega)
          _ = ε * K ^ i * (R * R⁻¹) * (R⁻¹) ^ i := by rw [pow_succ]; ring
          _ = _ := by rw [mul_inv_cancel₀ hR.ne']; ring
      calc
        _ ≤ (j.choose i : ℝ) * (ε * K ^ i * (R⁻¹) ^ i) *
            ((ε + 2) * K ^ (j - i) * R * (R⁻¹) ^ (j - i)) := by
          gcongr
          exact hres (j - i) (Nat.sub_le j i)
        _ = ((j.choose i : ℝ) * (ε + 2) * ε * R) *
            (K ^ i * K ^ (j - i)) * ((R⁻¹) ^ i * (R⁻¹) ^ (j - i)) := by ring
        _ = _ := by rw [← pow_add, ← pow_add, Nat.add_sub_of_le hij]; ring
    _ = _ := by
      have hchoose : (∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ)) = 2 ^ j := by
        exact_mod_cast Nat.sum_range_choose j
      rw [← Finset.sum_mul, hchoose, mul_pow]
      ring

end DifferentialGeometry.Analysis
