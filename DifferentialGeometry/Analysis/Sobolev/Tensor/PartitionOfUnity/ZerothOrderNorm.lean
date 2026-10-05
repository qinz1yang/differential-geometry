import DifferentialGeometry.Analysis.Sobolev.Tensor.PartitionOfUnity.WeightedNorm
import DifferentialGeometry.Analysis.Sobolev.Tensor.PartitionOfUnity.WeightedSobolevNorm


namespace DifferentialGeometry.Analysis.Sobolev.Tensor

open Bundle
open scoped Manifold ContDiff
open DifferentialGeometry.Integral.L2

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] in
theorem tensorPouSobolevHsNorm_zero_eq_tensorPouSobolevNorm
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (T : SmoothCcTensor g r s) :
    tensorPouSobolevHsNorm (I := I) (M := M) g 0 T =
      tensorPouSobolevNorm (I := I) (M := M) g 0 T := by
  rw [tensorPouSobolevHsNorm_eq, tensorPouSobolevNorm_eq]
  congr 1
  refine tsum_congr (fun α => ?_)
  refine Finset.sum_congr rfl (fun IJ _ => ?_)
  refine Finset.sum_congr rfl (fun j hj => ?_)
  simp only [Finset.mem_range, Nat.mul_zero, Nat.zero_add] at hj
  interval_cases j
  rw [Finset.univ_unique, Finset.sum_singleton]
  refine MeasureTheory.lintegral_congr (fun y => ?_)
  congr 2
  rw [iteratedFDeriv_zero_apply, norm_iteratedFDeriv_zero, Real.norm_eq_abs]
  rfl

end DifferentialGeometry.Analysis.Sobolev.Tensor
