import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.CovariantJet.Basic
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.CovariantJet.Naturality
import DifferentialGeometry.Analysis.Spectral.Tensor.Estimates.OperatorField.H1H2Composition

noncomputable section

open Manifold
open scoped BigOperators Manifold ContDiff

namespace DifferentialGeometry.Analysis.Sobolev

open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Integral.L2

variable
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
      [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

theorem exists_covariantJetNormSq_two_operatorFieldComposition_le
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) (p r c : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (Φ : SmoothCcTensor g r c) (W : SmoothCcTensor g p r),
        covariantJetNormSq (I := I) (M := M) g 2
            (ccOperatorFieldComp (I := I) (M := M) g p r c Φ W) ≤
          C * covariantJetNormSq (I := I) (M := M) g 2 Φ *
            covariantJetNormSq (I := I) (M := M) g 2 W := by
  obtain ⟨C₀, hC₀, happ⟩ :=
    operator_field_composition_h2_h2_to_h2_bound (I := I) (M := M) hDim g p r c
  refine ⟨C₀ ^ 2, sq_nonneg _, ?_⟩
  intro Φ W
  have hΦ0 : 0 ≤ covariantJetNormSq (I := I) (M := M) g 2 Φ :=
    covariantJetNormSq_nonneg (I := I) (M := M) g Φ
  have hW0 : 0 ≤ covariantJetNormSq (I := I) (M := M) g 2 W :=
    covariantJetNormSq_nonneg (I := I) (M := M) g W
  have hsΦ :
      Real.sqrt (covariantJetNormSq (I := I) (M := M) g 2 Φ) ^ 2 =
        covariantJetNormSq (I := I) (M := M) g 2 Φ :=
    Real.sq_sqrt hΦ0
  have hsW :
      Real.sqrt (covariantJetNormSq (I := I) (M := M) g 2 W) ^ 2 =
        covariantJetNormSq (I := I) (M := M) g 2 W :=
    Real.sq_sqrt hW0
  have h := happ Φ W
    (Real.sqrt (covariantJetNormSq (I := I) (M := M) g 2 Φ))
    (Real.sqrt (covariantJetNormSq (I := I) (M := M) g 2 W))
    (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    (by
      unfold covariantJetNormSq
      exact le_of_eq hsΦ.symm)
    (by
      unfold covariantJetNormSq
      exact le_of_eq hsW.symm)
  calc
    covariantJetNormSq (I := I) (M := M) g 2
        (ccOperatorFieldComp (I := I) (M := M) g p r c Φ W) ≤
      (C₀ *
        Real.sqrt (covariantJetNormSq (I := I) (M := M) g 2 Φ) *
        Real.sqrt (covariantJetNormSq (I := I) (M := M) g 2 W)) ^ 2 := by
      change (∑ j ∈ Finset.range 3,
        ‖iteratedCovGrad (I := I) g p c j
          (ccOperatorFieldComp (I := I) (M := M) g p r c Φ W)‖ ^ 2) ≤ _
      exact h
    _ = C₀ ^ 2 * covariantJetNormSq (I := I) (M := M) g 2 Φ *
        covariantJetNormSq (I := I) (M := M) g 2 W := by
      rw [mul_pow, mul_pow, hsΦ, hsW]

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
private theorem iteratedCovGrad_covGrad_norm_sq
    (g : SmoothRiemannianMetric I M) (r s i : ℕ)
    (S : SmoothCcTensor g r s) :
    ‖iteratedCovGrad (I := I) g r (s + 1) i
        (covGrad (I := I) (M := M) g r s S)‖ ^ 2 =
      ‖iteratedCovGrad (I := I) g r s (i + 1) S‖ ^ 2 := by
  rw [SmoothCcTensor.norm_def,
    tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs,
    SmoothCcTensor.norm_def,
    tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs]
  refine MeasureTheory.integral_congr_ae
    (Filter.Eventually.of_forall fun x => ?_)
  exact riemannianFiberNormSq_iteratedCovGrad_covGrad_comm_rs
    (I := I) (M := M) g r s i S x

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
theorem covariantJetNormSq_two_covGrad_le_three
    (g : SmoothRiemannianMetric I M) {r s : ℕ}
    (S : SmoothCcTensor g r s) :
    covariantJetNormSq (I := I) (M := M) g 2
        (covGrad (I := I) (M := M) g r s S) ≤
      covariantJetNormSq (I := I) (M := M) g 3 S := by
  have h0 := iteratedCovGrad_covGrad_norm_sq (I := I) (M := M) g r s 0 S
  have h1 := iteratedCovGrad_covGrad_norm_sq (I := I) (M := M) g r s 1 S
  have h2 := iteratedCovGrad_covGrad_norm_sq (I := I) (M := M) g r s 2 S
  unfold covariantJetNormSq
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
    Nat.reduceAdd] at h0 h1 h2 ⊢
  rw [h0, h1, h2]
  nlinarith only [sq_nonneg ‖S‖]

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
theorem covariantJetNormSq_three_le_two_add_covGrad
    (g : SmoothRiemannianMetric I M) {r s : ℕ}
    (S : SmoothCcTensor g r s) :
    covariantJetNormSq (I := I) (M := M) g 3 S ≤
      covariantJetNormSq (I := I) (M := M) g 2 S +
        covariantJetNormSq (I := I) (M := M) g 2
          (covGrad (I := I) (M := M) g r s S) := by
  have h0 := iteratedCovGrad_covGrad_norm_sq (I := I) (M := M) g r s 0 S
  have h1 := iteratedCovGrad_covGrad_norm_sq (I := I) (M := M) g r s 1 S
  have h2 := iteratedCovGrad_covGrad_norm_sq (I := I) (M := M) g r s 2 S
  unfold covariantJetNormSq
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
    Nat.reduceAdd] at h0 h1 h2 ⊢
  rw [h0, h1, h2]
  nlinarith only [sq_nonneg
    ‖iteratedCovGrad (I := I) g r s 1 S‖,
    sq_nonneg ‖iteratedCovGrad (I := I) g r s 2 S‖]

omit [BoundarylessManifold I M] in
private theorem operatorFieldComposition_tame_coefficient_bound
    {c0 c1 c2 fr X Y : ℝ}
    (hc0 : 0 ≤ c0) (hc1 : 0 ≤ c1) (hc2 : 0 ≤ c2)
    (hfr : 0 ≤ fr) (hX : 0 ≤ X) (hY : 0 ≤ Y) :
    c0 * X + 2 * (c1 * X + c2 * fr * Y) ≤
      (c0 + 2 * (c1 + c2 * fr)) * (X + Y) := by
  have h0Y : 0 ≤ c0 * Y := mul_nonneg hc0 hY
  have h1Y : 0 ≤ 2 * c1 * Y :=
    mul_nonneg (mul_nonneg (by norm_num) hc1) hY
  have h2X : 0 ≤ 2 * c2 * fr * X :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hc2) hfr) hX
  nlinarith only [h0Y, h1Y, h2X]

theorem exists_covariantJetNormSq_three_operatorFieldComposition_tame_bound
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) (p r c : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (Φ : SmoothCcTensor g r c) (W : SmoothCcTensor g p r),
        covariantJetNormSq (I := I) (M := M) g 3
            (ccOperatorFieldComp (I := I) (M := M) g p r c Φ W) ≤
          C * (covariantJetNormSq (I := I) (M := M) g 3 Φ *
              covariantJetNormSq (I := I) (M := M) g 2 W +
            covariantJetNormSq (I := I) (M := M) g 2 Φ *
              covariantJetNormSq (I := I) (M := M) g 3 W) := by
  obtain ⟨C0, hC0, h0⟩ :=
    exists_covariantJetNormSq_two_operatorFieldComposition_le (I := I) (M := M) hDim g p r c
  obtain ⟨C1, hC1, h1⟩ :=
    exists_covariantJetNormSq_two_operatorFieldComposition_le (I := I) (M := M) hDim g p r (c + 1)
  obtain ⟨C2, hC2, h2⟩ :=
    exists_covariantJetNormSq_two_operatorFieldComposition_le (I := I) (M := M) hDim g p (r + 1) (c + 1)
  let fr : ℝ := Module.finrank ℝ E
  let C : ℝ := C0 + 2 * (C1 + C2 * fr)
  have hfr : 0 ≤ fr := Nat.cast_nonneg _
  have hC : 0 ≤ C := by
    dsimp only [C]
    exact add_nonneg hC0
      (mul_nonneg (by norm_num) (add_nonneg hC1 (mul_nonneg hC2 hfr)))
  refine ⟨C, hC, ?_⟩
  intro Φ W
  let Y : SmoothCcTensor g p c := ccOperatorFieldComp (I := I) (M := M) g p r c Φ W
  let P : SmoothCcTensor g p (c + 1) :=
    ccOperatorFieldComp (I := I) (M := M) g p r (c + 1)
      (covGrad (I := I) (M := M) g r c Φ) W
  let Q : SmoothCcTensor g p (c + 1) :=
    ccOperatorFieldComp (I := I) (M := M) g p (r + 1) (c + 1)
      (slotExtend (I := I) (M := M) g r c Φ)
      (covGrad (I := I) (M := M) g p r W)
  let X : ℝ := covariantJetNormSq (I := I) (M := M) g 3 Φ *
    covariantJetNormSq (I := I) (M := M) g 2 W
  let Z : ℝ := covariantJetNormSq (I := I) (M := M) g 2 Φ *
    covariantJetNormSq (I := I) (M := M) g 3 W
  have hΦ23 := covariantJetNormSq_mono (I := I) (M := M) g (by omega : 2 ≤ 3) Φ
  have hΦ2 := covariantJetNormSq_nonneg (I := I) (M := M) (m := 2) g Φ
  have hW2 := covariantJetNormSq_nonneg (I := I) (M := M) (m := 2) g W
  have hΦ3 := covariantJetNormSq_nonneg (I := I) (M := M) (m := 3) g Φ
  have hW3 := covariantJetNormSq_nonneg (I := I) (M := M) (m := 3) g W
  have hX : 0 ≤ X := mul_nonneg hΦ3 hW2
  have hZ : 0 ≤ Z := mul_nonneg hΦ2 hW3
  have hY2 : covariantJetNormSq (I := I) (M := M) g 2 Y ≤ C0 * X := by
    calc
      covariantJetNormSq (I := I) (M := M) g 2 Y ≤
          C0 * covariantJetNormSq (I := I) (M := M) g 2 Φ *
            covariantJetNormSq (I := I) (M := M) g 2 W := by
        simpa only [Y] using h0 Φ W
      _ ≤ C0 * covariantJetNormSq (I := I) (M := M) g 3 Φ *
            covariantJetNormSq (I := I) (M := M) g 2 W := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hΦ23 hC0) hW2
      _ = C0 * X := by simp only [X]; ring
  have hP2 : covariantJetNormSq (I := I) (M := M) g 2 P ≤ C1 * X := by
    calc
      covariantJetNormSq (I := I) (M := M) g 2 P ≤
          C1 * covariantJetNormSq (I := I) (M := M) g 2
              (covGrad (I := I) (M := M) g r c Φ) *
            covariantJetNormSq (I := I) (M := M) g 2 W := by
        simpa only [P] using h1 (covGrad (I := I) (M := M) g r c Φ) W
      _ ≤ C1 * covariantJetNormSq (I := I) (M := M) g 3 Φ *
            covariantJetNormSq (I := I) (M := M) g 2 W := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left
            (covariantJetNormSq_two_covGrad_le_three (I := I) (M := M) g Φ) hC1) hW2
      _ = C1 * X := by simp only [X]; ring
  have hQ2 : covariantJetNormSq (I := I) (M := M) g 2 Q ≤ C2 * fr * Z := by
    calc
      covariantJetNormSq (I := I) (M := M) g 2 Q ≤
          C2 * covariantJetNormSq (I := I) (M := M) g 2
              (slotExtend (I := I) (M := M) g r c Φ) *
            covariantJetNormSq (I := I) (M := M) g 2
              (covGrad (I := I) (M := M) g p r W) := by
        simpa only [Q] using
          h2 (slotExtend (I := I) (M := M) g r c Φ)
            (covGrad (I := I) (M := M) g p r W)
      _ ≤ C2 * (fr * covariantJetNormSq (I := I) (M := M) g 2 Φ) *
            covariantJetNormSq (I := I) (M := M) g 2
              (covGrad (I := I) (M := M) g p r W) := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left
            (by simpa only [fr] using
              covariantJetNormSq_slotExtend_le (I := I) (M := M) g r c Φ) hC2)
          (covariantJetNormSq_nonneg (I := I) (M := M) g
            (covGrad (I := I) (M := M) g p r W))
      _ ≤ C2 * (fr * covariantJetNormSq (I := I) (M := M) g 2 Φ) *
            covariantJetNormSq (I := I) (M := M) g 3 W := by
        exact mul_le_mul_of_nonneg_left
          (covariantJetNormSq_two_covGrad_le_three (I := I) (M := M) g W)
          (mul_nonneg hC2 (mul_nonneg hfr hΦ2))
      _ = C2 * fr * Z := by simp only [Z]; ring
  have hgrad : covariantJetNormSq (I := I) (M := M) g 2
      (covGrad (I := I) (M := M) g p c Y) ≤
        2 * (C1 * X + C2 * fr * Z) := by
    rw [show covGrad (I := I) (M := M) g p c Y = P + Q by
      simpa only [Y, P, Q] using covGrad_operatorFieldComposition_eq (I := I) (M := M) g p r c Φ W]
    exact (covariantJetNormSq_add_le (I := I) (M := M) g 2 P Q).trans
      (mul_le_mul_of_nonneg_left (add_le_add hP2 hQ2) (by norm_num))
  calc
    covariantJetNormSq (I := I) (M := M) g 3
        (ccOperatorFieldComp (I := I) (M := M) g p r c Φ W) =
      covariantJetNormSq (I := I) (M := M) g 3 Y := rfl
    _ ≤ covariantJetNormSq (I := I) (M := M) g 2 Y +
        covariantJetNormSq (I := I) (M := M) g 2
          (covGrad (I := I) (M := M) g p c Y) :=
      covariantJetNormSq_three_le_two_add_covGrad (I := I) (M := M) g Y
    _ ≤ C0 * X + 2 * (C1 * X + C2 * fr * Z) := add_le_add hY2 hgrad
    _ ≤ C * (X + Z) := by
      simpa only [C] using operatorFieldComposition_tame_coefficient_bound hC0 hC1 hC2 hfr hX hZ
    _ = C * (covariantJetNormSq (I := I) (M := M) g 3 Φ *
            covariantJetNormSq (I := I) (M := M) g 2 W +
          covariantJetNormSq (I := I) (M := M) g 2 Φ *
            covariantJetNormSq (I := I) (M := M) g 3 W) := by
      simp only [X, Z]

end DifferentialGeometry.Analysis.Sobolev
