import DifferentialGeometry.Geometry.Metric.TensorInner.FiberNorm.SlotPairing
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.MetricPerturbation.CometricSlotPairing
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.OperatorField.Calculus.SlotInsertion
import DifferentialGeometry.Analysis.Integration.L2.Pairing.Defs

open DifferentialGeometry.TensorMetric
  (fiberNormSqComponent tensorInnerPointwise tensorInnerPointwise_eq_sum_componentS_mul)
open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Analysis.Elliptic
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Operator

noncomputable section


open Bundle Manifold MeasureTheory Set Filter DifferentialGeometry.Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators

namespace DifferentialGeometry.Analysis.Sobolev.TensorHilbert

open DifferentialGeometry.Analysis.Laplacian

open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Analysis.Spectral.MetricRealization

variable
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [CompactSpace M] [BoundarylessManifold I M]
      [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

omit [BoundarylessManifold I M] [I.Boundaryless] in
theorem tensorL2Inner_operatorFieldApplication_slotInsertEndoCc_self_adjoint
    (g₀ : SmoothRiemannianMetric I M) (s : ℕ)
    (Λ : ContMDiffSection I (E →L[ℝ] E) ∞
      (fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x))
    (hadj : ∀ (x : M) (a b : TangentSpace I x),
      g₀.inner x (Λ x a) b = g₀.inner x a (Λ x b))
    (A B : SmoothCcTensor g₀ 0 (s + 1)) :
    tensorL2Inner (I := I) (M := M) g₀ 0 (s + 1)
        (operatorFieldApply (I := I) (M := M) g₀ (s + 1) (s + 1)
          (endoSlotZeroCcTensor (I := I) (M := M) g₀ s Λ) A).toFun
        B.toFun =
      tensorL2Inner (I := I) (M := M) g₀ 0 (s + 1)
        A.toFun
        (operatorFieldApply (I := I) (M := M) g₀ (s + 1) (s + 1)
          (endoSlotZeroCcTensor (I := I) (M := M) g₀ s Λ) B).toFun := by
  classical
  refine integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
  simp only []
  obtain ⟨e, bse, hbse, horth⟩ :=
    exists_orthoFrame_basis_E (I := I) (M := M) g₀ x
  have hslotA :
      (operatorFieldApply (I := I) (M := M) g₀ (s + 1) (s + 1)
          (endoSlotZeroCcTensor (I := I) (M := M) g₀ s Λ) A).toFun x =
        TensorRSSpace.toModel
          (show TensorRSSpace 0 (s + 1) I x from
            TensorRSSpace.ofCLM ((slotInsertEndoFib (s + 1) 0 x (Λ x)).comp
              (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from
                A.toSection x))) := rfl
  have hslotB :
      (operatorFieldApply (I := I) (M := M) g₀ (s + 1) (s + 1)
          (endoSlotZeroCcTensor (I := I) (M := M) g₀ s Λ) B).toFun x =
        TensorRSSpace.toModel
          (show TensorRSSpace 0 (s + 1) I x from
            TensorRSSpace.ofCLM ((slotInsertEndoFib (s + 1) 0 x (Λ x)).comp
              (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from
                B.toSection x))) := rfl
  rw [hslotA, hslotB, SmoothCcTensor.toFun_apply, SmoothCcTensor.toFun_apply]
  exact tensorInnerPointwise_slotΛ_self_adjoint (I := I) (M := M) g₀ s x (Λ x)
    (hadj x) (A.toSection x) (B.toSection x) e bse hbse horth

end DifferentialGeometry.Analysis.Sobolev.TensorHilbert

end
