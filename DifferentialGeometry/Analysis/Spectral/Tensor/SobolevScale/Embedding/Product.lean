import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.Embedding.SmoothCompactSupportDense
import Mathlib.Analysis.Normed.Lp.PiLp

open scoped Manifold ContDiff ENNReal

namespace DifferentialGeometry.Analysis.Spectral

open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation

variable {ι : Type*} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
  [T2Space M] [SigmaCompactSpace M]

theorem denseRange_ccTensorToHs_piLp
    (g : SmoothRiemannianMetric I M) (s : ℕ) {σ : ℝ} (hσ : 0 ≤ σ) (p : ℝ≥0∞) :
    DenseRange (fun S : ι → SmoothCcTensor g 0 s =>
      WithLp.toLp p (fun i => ccTensorToHs (I := I) (M := M) g s σ (S i))) := by
  have h : DenseRange (fun S : ι → SmoothCcTensor g 0 s =>
      fun i => ccTensorToHs (I := I) (M := M) g s σ (S i)) :=
    DenseRange.piMap (fun _ : ι => ccToHsLin_dense (I := I) (M := M) g s hσ)
  exact ((PiLp.homeomorph p (fun _ : ι => TensorHs g 0 s σ)).symm.surjective.denseRange).comp
    h (PiLp.continuous_toLp p _)

end DifferentialGeometry.Analysis.Spectral
