import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.Defs
import DifferentialGeometry.Analysis.Spectral.Intrinsic.CompactResolvent

open scoped Manifold ContDiff

namespace DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorHs

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

instance instSeparableSpace (g : SmoothRiemannianMetric I M) (r s : ℕ) (σ : ℝ) :
    TopologicalSpace.SeparableSpace (TensorHs g r s σ) := by
  let : Countable (TensorSpectral.TensorNonzeroResolventEigenvalue g r s) :=
    TensorSpectral.TensorNonzeroResolventEigenvalue.countable_ofCompact g r s
      (DifferentialGeometry.Analysis.Spectral.tensorResolventL2_isCompactOperator g r s)
  let : Countable (TensorEigenIdx g r s) := inferInstance
  let b : HilbertBasis (TensorEigenIdx g r s) ℝ (TensorHs g r s σ) :=
    HilbertBasis.ofRepr (rescaleEquivL2 (g := g) (r := r) (s := s) (σ := σ))
  have hd : Dense (Submodule.span ℝ (Set.range b) : Set (TensorHs g r s σ)) := by
    rw [dense_iff_closure_eq, ← Submodule.topologicalClosure_coe, b.dense_span]
    rfl
  exact hd.isSeparable_iff.mp (Set.countable_range b).isSeparable.span

end DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorHs
