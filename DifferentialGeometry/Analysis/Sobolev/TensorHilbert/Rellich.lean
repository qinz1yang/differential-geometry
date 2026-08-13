import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.HilbertSpace
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.Inclusion
import Mathlib.Analysis.Normed.Operator.Compact

noncomputable section


open Bundle Manifold MeasureTheory Set Filter DifferentialGeometry.Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators Matrix
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Sobolev
namespace IntrinsicSobolev

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Sobolev.Tensor
open DifferentialGeometry.Analysis.Sobolev.Chart
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

omit [NeZero (Module.finrank ℝ E)] in
lemma denseRange_smoothToHsCompl
    (g : SmoothRiemannianMetric I M) (r s k : ℕ) :
    DenseRange (fun S : SmoothCcTensorHs g r s (k + 1) =>
      (S : TensorPouSobolevHilbert g r s (k + 1))) := by
  simpa using (UniformSpace.Completion.denseRange_coe :
    DenseRange (fun S : SmoothCcTensorHs g r s (k + 1) =>
      (S : TensorPouSobolevHilbert g r s (k + 1))))

omit [NeZero (Module.finrank ℝ E)] in
lemma exists_smooth_close_to_TensorHs
    (g : SmoothRiemannianMetric I M) (r s k : ℕ)
    (x : TensorPouSobolevHilbert g r s (k + 1)) {δ : ℝ} (hδ : 0 < δ) :
    ∃ S : SmoothCcTensorHs g r s (k + 1),
      ‖x - (S : TensorPouSobolevHilbert g r s (k + 1))‖ < δ ∧
      ‖S‖ ≤ ‖x‖ + δ := by
  classical
  have h_dense : DenseRange (fun S : SmoothCcTensorHs g r s (k + 1) =>
      (S : TensorPouSobolevHilbert g r s (k + 1))) :=
    denseRange_smoothToHsCompl (I := I) (M := M) g r s k
  rw [denseRange_iff_closure_range, Set.eq_univ_iff_forall] at h_dense
  have hx : x ∈ closure (Set.range (fun S : SmoothCcTensorHs g r s (k + 1) =>
      (S : TensorPouSobolevHilbert g r s (k + 1)))) := h_dense x
  rw [Metric.mem_closure_iff] at hx
  obtain ⟨q, ⟨S, hS_eq⟩, hS_close⟩ := hx δ hδ
  refine ⟨S, ?_, ?_⟩
  · rw [show x - (S : TensorPouSobolevHilbert g r s (k + 1)) = x - q from
      congrArg (fun y : TensorPouSobolevHilbert g r s (k + 1) => x - y) hS_eq]
    simpa [dist_eq_norm] using hS_close
  · have hS_norm : ‖(S : TensorPouSobolevHilbert g r s (k + 1))‖ = ‖S‖ :=
      UniformSpace.Completion.norm_coe S
    rw [← hS_norm]
    calc
      ‖(S : TensorPouSobolevHilbert g r s (k + 1))‖
          = dist (S : TensorPouSobolevHilbert g r s (k + 1)) 0 := by simp [dist_eq_norm]
      _ ≤ dist (S : TensorPouSobolevHilbert g r s (k + 1)) x + dist x 0 :=
            dist_triangle (S : TensorPouSobolevHilbert g r s (k + 1)) x 0
      _ = ‖x - (S : TensorPouSobolevHilbert g r s (k + 1))‖ + ‖x‖ := by
            simp [dist_eq_norm, norm_sub_rev, add_comm]
      _ ≤ ‖x‖ + δ := by
            have hb : ‖x - (S : TensorPouSobolevHilbert g r s (k + 1))‖ ≤ δ :=
              le_of_lt (by simpa [dist_eq_norm, hS_eq] using hS_close)
            linarith

theorem tensorPouSobolevHilbert_inclusion_isCompactOperator
    (g : SmoothRiemannianMetric I M) (r s k : ℕ) :
    IsCompactOperator (inclusionHk_succ (I := I) (M := M) g r s k) := by
  sorry

theorem TensorPouSobolevHilbert_inclusion_H2_L2_isCompact
    (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    IsCompactOperator (inclusionHk_succ (I := I) (M := M) g r s 0) :=
  tensorPouSobolevHilbert_inclusion_isCompactOperator
    (I := I) (M := M) g r s 0

end IntrinsicSobolev
end Sobolev
end Analysis
end DifferentialGeometry

end
