import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.Scalar.Multiplication

noncomputable section

open scoped Manifold ContDiff

namespace DifferentialGeometry.Analysis.Spectral

open DifferentialGeometry.Integral.L2

variable
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
      [BoundarylessManifold I M] [T2Space M]

theorem scalar_product_sub_hs_bound (g : SmoothRiemannianMetric I M) (n : ℕ)
    (hn : Module.finrank ℝ E / 2 + 1 ≤ n) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ A B D T : SmoothCcTensor g 0 0,
      ‖ccTensorToHs g 0 (n : ℝ)
        (ccOperatorFieldComp g 0 0 0 A B - ccOperatorFieldComp g 0 0 0 D T)‖ ≤
        C * (‖ccTensorToHs g 0 (n : ℝ) A‖ * ‖ccTensorToHs g 0 (n : ℝ) (B - T)‖ +
          ‖ccTensorToHs g 0 (n : ℝ) (A - D)‖ * ‖ccTensorToHs g 0 (n : ℝ) T‖) := by
  obtain ⟨C, hC, hbound⟩ := scalar_product_hs_bound g n hn
  refine ⟨C, hC, ?_⟩
  intro A B D T
  have heq : ccOperatorFieldComp g 0 0 0 A B - ccOperatorFieldComp g 0 0 0 D T =
      ccOperatorFieldComp g 0 0 0 A (B - T) +
        ccOperatorFieldComp g 0 0 0 (A - D) T := by
    rw [ccOperatorFieldComp_sub_right, operatorFieldComposition_sub_left]
    abel
  rw [heq, ccTensorToHs_add]
  calc
    _ ≤ ‖ccTensorToHs g 0 (n : ℝ) (ccOperatorFieldComp g 0 0 0 A (B - T))‖ +
        ‖ccTensorToHs g 0 (n : ℝ) (ccOperatorFieldComp g 0 0 0 (A - D) T)‖ :=
      norm_add_le _ _
    _ ≤ C * ‖ccTensorToHs g 0 (n : ℝ) A‖ * ‖ccTensorToHs g 0 (n : ℝ) (B - T)‖ +
        C * ‖ccTensorToHs g 0 (n : ℝ) (A - D)‖ * ‖ccTensorToHs g 0 (n : ℝ) T‖ :=
      add_le_add (hbound A (B - T)) (hbound (A - D) T)
    _ = _ := by ring

end DifferentialGeometry.Analysis.Spectral
