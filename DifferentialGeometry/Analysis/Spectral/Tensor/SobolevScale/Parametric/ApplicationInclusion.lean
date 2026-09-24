import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.Parametric.Application
import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.Embedding.SmoothInclusion

noncomputable section
open scoped Manifold ContDiff

namespace DifferentialGeometry.Analysis.Spectral

open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

theorem tensorHsInclusion_appHs
    (g : SmoothRiemannianMetric I M) (b c : ℕ) {n m : ℕ} (h : n ≤ m)
    (Φ : SmoothCcTensor g b c) (u : TensorHs g 0 b (m : ℝ)) :
    tensorHsInclusion (by exact_mod_cast h : (n : ℝ) ≤ (m : ℝ))
      (appHs g b c m Φ u) =
    appHs g b c n Φ
      (tensorHsInclusion (by exact_mod_cast h : (n : ℝ) ≤ (m : ℝ)) u) := by
  let Jb := tensorHsInclusion (g := g) (r := 0) (s := b)
    (by exact_mod_cast h : (n : ℝ) ≤ (m : ℝ))
  let Jc := tensorHsInclusion (g := g) (r := 0) (s := c)
    (by exact_mod_cast h : (n : ℝ) ≤ (m : ℝ))
  refine (ccToHsLin_dense g b (by positivity : (0 : ℝ) ≤ (m : ℝ))).induction_on u ?_ ?_
  · exact isClosed_eq (Jc.continuous.comp (appHs g b c m Φ).continuous)
      ((appHs g b c n Φ).continuous.comp Jb.continuous)
  intro S
  simp only [ccToHsLin_apply, appHs_apply_ccTensorToHs,
    tensorHsInclusion_ccTensorToHs]

end DifferentialGeometry.Analysis.Spectral
