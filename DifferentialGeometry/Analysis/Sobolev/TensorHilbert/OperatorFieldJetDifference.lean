import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.CovariantJet
import DifferentialGeometry.Analysis.Spectral.Tensor.Estimates.OperatorFieldCompositionJetMul

noncomputable section

open Manifold
open scoped Manifold ContDiff

namespace DifferentialGeometry.Analysis.Sobolev

open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Integral.L2

variable
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
      [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] in
theorem operatorFieldComposition_sub
    (g : SmoothRiemannianMetric I M) (a b c : ℕ)
    (Φ₁ Φ₂ : SmoothCcTensor g b c) (W₁ W₂ : SmoothCcTensor g a b) :
    ccOperatorFieldComp (I := I) (M := M) g a b c Φ₁ W₁ -
        ccOperatorFieldComp (I := I) (M := M) g a b c Φ₂ W₂ =
      ccOperatorFieldComp (I := I) (M := M) g a b c (Φ₁ - Φ₂) W₁ +
        ccOperatorFieldComp (I := I) (M := M) g a b c Φ₂ (W₁ - W₂) := by
  rw [operatorFieldComposition_sub_left, operatorFieldComposition_sub_right]
  abel

omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
theorem covariantJetNormSq_operatorFieldComposition_sub_le
    (g : SmoothRiemannianMetric I M) (m a b c : ℕ)
    (C Xd YT XU Yd : ℝ) (hC : 0 ≤ C)
    (ΦT ΦU : SmoothCcTensor g b c) (WT WU : SmoothCcTensor g a b)
    (happ : ∀ (Φ : SmoothCcTensor g b c) (W : SmoothCcTensor g a b),
      covariantJetNormSq (I := I) (M := M) g m
          (ccOperatorFieldComp (I := I) (M := M) g a b c Φ W) ≤
        C * covariantJetNormSq (I := I) (M := M) g m Φ *
          covariantJetNormSq (I := I) (M := M) g m W)
    (hΦd : covariantJetNormSq (I := I) (M := M) g m (ΦT - ΦU) ≤ Xd)
    (hWT : covariantJetNormSq (I := I) (M := M) g m WT ≤ YT)
    (hΦU : covariantJetNormSq (I := I) (M := M) g m ΦU ≤ XU)
    (hWd : covariantJetNormSq (I := I) (M := M) g m (WT - WU) ≤ Yd) :
    covariantJetNormSq (I := I) (M := M) g m
        (ccOperatorFieldComp (I := I) (M := M) g a b c ΦT WT -
          ccOperatorFieldComp (I := I) (M := M) g a b c ΦU WU) ≤
      2 * (C * Xd * YT + C * XU * Yd) := by
  rw [operatorFieldComposition_sub]
  refine (covariantJetNormSq_add_le (I := I) (M := M) g m _ _).trans ?_
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply add_le_add
  · refine (happ _ _).trans ?_
    exact mul_le_mul
      (mul_le_mul_of_nonneg_left hΦd hC) hWT
      (covariantJetNormSq_nonneg (I := I) (M := M) (m := m) g _)
      (mul_nonneg hC
        ((covariantJetNormSq_nonneg (I := I) (M := M) (m := m) g _).trans hΦd))
  · refine (happ _ _).trans ?_
    exact mul_le_mul
      (mul_le_mul_of_nonneg_left hΦU hC) hWd
      (covariantJetNormSq_nonneg (I := I) (M := M) (m := m) g _)
      (mul_nonneg hC
        ((covariantJetNormSq_nonneg (I := I) (M := M) (m := m) g _).trans hΦU))

end DifferentialGeometry.Analysis.Sobolev
