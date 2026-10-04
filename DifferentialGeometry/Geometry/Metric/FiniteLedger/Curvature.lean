import DifferentialGeometry.Geometry.Curvature.Coordinates.MetricJet.CoefficientField

set_option autoImplicit false

noncomputable section

open scoped ContDiff
open DifferentialGeometry.Tensor.Coordinates (chartModelBasis)

namespace DifferentialGeometry.Analysis

private theorem det_coefficientGram_ne_zero_of_isCoercive {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] {b : E → E →L[ℝ] E →L[ℝ] ℝ} {w : E}
    (hco : IsCoercive (b w)) : (Matrix.of (coefficientGram b w)).det ≠ 0 := by
  obtain ⟨C, hC, hCu⟩ := hco
  have hpos : ∀ u : E, u ≠ 0 → 0 < b w u u := fun u hu =>
    lt_of_lt_of_le (mul_pos (mul_pos hC (norm_pos_iff.mpr hu)) (norm_pos_iff.mpr hu)) (hCu u)
  intro hdet0
  obtain ⟨c, hc0, hcv⟩ :=
    (Matrix.exists_mulVec_eq_zero_iff (M := Matrix.of (coefficientGram b w))).2 hdet0
  set v : E := ∑ i, c i • chartModelBasis E i with hv
  have hrow0 : ∀ i, (b w (chartModelBasis E i)) v = 0 := by
    intro i
    have h1 : (b w (chartModelBasis E i)) v =
        ∑ j, Matrix.of (coefficientGram b w) i j * c j := by
      rw [hv, map_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_smul, smul_eq_mul, mul_comm]
      simp only [coefficientGram_apply, Matrix.of_apply]
    have h2 : (∑ j, Matrix.of (coefficientGram b w) i j * c j) = 0 := by
      simpa [Matrix.mulVec, dotProduct] using congrFun hcv i
    rw [h1, h2]
  have hinner : b w v v = 0 := by
    have hout : (b w) v = ∑ i, c i • ((b w) (chartModelBasis E i)) := by
      rw [hv, map_sum]
      exact Finset.sum_congr rfl fun i _ => by rw [map_smul]
    calc b w v v = (∑ i, c i • ((b w) (chartModelBasis E i))) v := by rw [hout]
      _ = ∑ i, c i • ((b w (chartModelBasis E i)) v) := by
          rw [_root_.sum_apply]
          exact Finset.sum_congr rfl fun i _ => by rw [_root_.smul_apply]
      _ = 0 := by
          refine Finset.sum_eq_zero fun i _ => ?_
          rw [hrow0 i, smul_zero]
  have hvne : v ≠ 0 := by
    intro hv0
    apply hc0
    have hz : ∑ i, c i • chartModelBasis E i = 0 := hv.symm.trans hv0
    have hall := Fintype.linearIndependent_iff.1 (chartModelBasis E).linearIndependent c hz
    funext i
    exact hall i
  exact absurd hinner (ne_of_gt (hpos v hvne))

private theorem contDiffAt_jetRm04_of_det_ne_zero {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] {p₀ : MatJet E (Module.finrank ℝ E)}
    (hp₀ : (Matrix.of p₀.1).det ≠ 0) (X Y Z W : E) :
    ContDiffAt ℝ ∞ (fun p : MatJet E (Module.finrank ℝ E) => jetRm04 p X Y Z W) p₀ := by
  unfold jetRm04
  refine ContDiffAt.sum (fun i _ => ?_)
  refine ContDiffAt.sum (fun j _ => ?_)
  refine ContDiffAt.sum (fun k _ => ?_)
  refine ContDiffAt.sum (fun l _ => ?_)
  refine contDiffAt_const.mul (ContDiffAt.sum (fun l' _ => ?_))
  exact (contDiff_jetVal l l').contDiffAt.mul (contDiffAt_jetRiemann _ hp₀ k i j l')

theorem coefficientRm04_contDiffOn {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {U : Set E} (hU : IsOpen U) {b : E → E →L[ℝ] E →L[ℝ] ℝ}
    {K' : ℕ} (hb : ContDiffOn ℝ K' b U) (hco : ∀ x ∈ U, IsCoercive (b x)) (hK : 2 ≤ K')
    (X Y Z W : E) :
    ContDiffOn ℝ ((K' - 2 : ℕ) : ℕ∞ω) (fun w => coefficientRm04 b w X Y Z W) U := by
  obtain ⟨m, rfl⟩ : ∃ m, K' = m + 1 + 1 := ⟨K' - 2, by omega⟩
  have hm : m + 1 + 1 - 2 = m := by omega
  rw [hm]
  rw [Nat.cast_add_one, Nat.cast_add_one] at hb
  have hG : ContDiffOn ℝ ((m : ℕ∞ω) + 1 + 1) (coefficientGram b) U :=
    contDiffOn_coefficientGram hb
  have hG1 : ContDiffOn ℝ ((m : ℕ∞ω) + 1) (fderiv ℝ (coefficientGram b)) U :=
    hG.fderiv_of_isOpen hU le_rfl
  have hG2 : ContDiffOn ℝ m (fderiv ℝ (fderiv ℝ (coefficientGram b))) U :=
    hG1.fderiv_of_isOpen hU le_rfl
  have h1 : (m : ℕ∞ω) ≤ m + 1 := le_add_of_nonneg_right zero_le_one
  have h0 : (m : ℕ∞ω) ≤ m + 1 + 1 := h1.trans (le_add_of_nonneg_right zero_le_one)
  have hjet : ContDiffOn ℝ m (fun w => jet2 (coefficientGram b) w) U :=
    (hG.of_le h0).prodMk ((hG1.of_le h1).prodMk hG2)
  exact fun w hw => (contDiffAt_infty.mp (contDiffAt_jetRm04_of_det_ne_zero
    (p₀ := jet2 (coefficientGram b) w) (det_coefficientGram_ne_zero_of_isCoercive (hco w hw))
    X Y Z W) m).comp_contDiffWithinAt w (hjet w hw)

end DifferentialGeometry.Analysis
