import DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.Smoothing.Sobolev

noncomputable section
open scoped Manifold ContDiff

namespace DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation


variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]
  {g : SmoothRiemannianMetric I M} {r s : ℕ} {a b d t : ℝ}

theorem tensorHsInclusion_tensorHeatSemigroupHs (hbd : d ≤ b) (ht : 0 < t)
    (U : TensorHs g r s a) :
    tensorHsInclusion hbd
        (tensorHeatSemigroupHs (g := g) (r := r) (s := s) ht (a := a) (b := b) U) =
      tensorHeatSemigroupHs (g := g) (r := r) (s := s) ht (a := a) (b := d) U := by
  apply TensorHs.ext
  funext i
  rw [tensorHsInclusion_coeff_apply, tensorHeatSemigroupHs_coeff, tensorHeatSemigroupHs_coeff]

end DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
