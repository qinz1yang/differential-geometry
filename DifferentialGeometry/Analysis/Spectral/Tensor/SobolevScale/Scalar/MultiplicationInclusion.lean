import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.Scalar.Multiplication
import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.Embedding.SmoothInclusion

noncomputable section

open scoped ContDiff Manifold

namespace DifferentialGeometry.Analysis.Spectral

open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
  [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

theorem tensorHsInclusion_scalarHsMul
    (g : SmoothRiemannianMetric I M) {n m : ℕ}
    (hn : Module.finrank ℝ E / 2 + 1 ≤ n) (h : n ≤ m)
    (u v : TensorHs g 0 0 (m : ℝ)) :
    tensorHsInclusion (show (n : ℝ) ≤ (m : ℝ) by exact_mod_cast h)
        (scalarHsMul g m (hn.trans h) u v) =
      scalarHsMul g n hn
        (tensorHsInclusion (show (n : ℝ) ≤ (m : ℝ) by exact_mod_cast h) u)
        (tensorHsInclusion (show (n : ℝ) ≤ (m : ℝ) by exact_mod_cast h) v) := by
  let J := tensorHsInclusion (g := g) (r := 0) (s := 0)
    (show (n : ℝ) ≤ (m : ℝ) by exact_mod_cast h)
  change J (scalarHsMul g m (hn.trans h) u v) = scalarHsMul g n hn (J u) (J v)
  refine (ccToHsLin_dense g 0 (by positivity : (0 : ℝ) ≤ (m : ℝ))).induction_on u ?_ ?_
  · exact isClosed_eq
      (J.continuous.comp ((scalarHsMul g m (hn.trans h)).continuous.clm_apply continuous_const))
      (((scalarHsMul g n hn).continuous.comp J.continuous).clm_apply continuous_const)
  intro S
  refine (ccToHsLin_dense g 0 (by positivity : (0 : ℝ) ≤ (m : ℝ))).induction_on v ?_ ?_
  · exact isClosed_eq
      (J.continuous.comp (scalarHsMul g m (hn.trans h) (ccToHsLin g 0 (m : ℝ) S)).continuous)
      ((scalarHsMul g n hn (J (ccToHsLin g 0 (m : ℝ) S))).continuous.comp J.continuous)
  intro T
  simp only [ccToHsLin_apply, scalarHsMul_apply_ccTensorToHs, J,
    tensorHsInclusion_ccTensorToHs]

end DifferentialGeometry.Analysis.Spectral
