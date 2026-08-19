import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.RiemannianFiberNormSq.RiemannianFiberNormSqSmoothCcUniformBound
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.IteratedCovGradLinear

noncomputable section

open Bundle Manifold DifferentialGeometry.Tensor0SBundle
open scoped Manifold ContDiff

namespace DifferentialGeometry.Analysis.Spectral

open DifferentialGeometry.Analysis.Elliptic
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Sobolev

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
  [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem exists_riemannianFiberNormSq_iteratedCovGrad_bound
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (F : SmoothCcTensor g r s) :
    ∃ c : ℕ → ℝ, (∀ i, 0 ≤ c i) ∧ ∀ (i : ℕ) (x : M),
      riemannianFiberNormSq (I := I) (M := M) g r (s + i) x
        ((iteratedCovGrad (I := I) g r s i F).toSection x) ≤ c i := by
  refine ⟨fun i => (exists_bound_riemannianFiberNormSq_smoothCcTensor
      (I := I) (M := M) g r (s + i)
      (iteratedCovGrad (I := I) g r s i F)).choose,
    fun i => (exists_bound_riemannianFiberNormSq_smoothCcTensor
      (I := I) (M := M) g r (s + i)
      (iteratedCovGrad (I := I) g r s i F)).choose_spec.1,
    fun i x => (exists_bound_riemannianFiberNormSq_smoothCcTensor
      (I := I) (M := M) g r (s + i)
      (iteratedCovGrad (I := I) g r s i F)).choose_spec.2 x⟩

end DifferentialGeometry.Analysis.Spectral

end
