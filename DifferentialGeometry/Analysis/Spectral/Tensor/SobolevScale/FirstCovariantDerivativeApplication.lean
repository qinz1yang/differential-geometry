import DifferentialGeometry.Analysis.Spectral.Tensor.Estimates.H2H3FirstOrder
import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.SmoothCcDense

noncomputable section

open Bundle Manifold MeasureTheory Set Filter DifferentialGeometry.Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators

namespace DifferentialGeometry
namespace Integral
namespace Connection

open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
  [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

private noncomputable def firstCovariantDerivativeApplicationLinearMap
    (g : SmoothRiemannianMetric I M) (s c : ℕ)
    (Φ : SmoothCcTensor g (s + 1) c) :
    SmoothCcTensor g 0 s →ₗ[ℝ] SmoothCcTensor g 0 c where
  toFun := fun U =>
    operatorFieldApply (I := I) (M := M) g (s + 1) c Φ
      (iteratedCovGrad (I := I) g 0 s 1 U)
  map_add' := fun U V => by
    rw [iteratedCovGrad_add]
    change operatorFieldApply (I := I) (M := M) g (s + 1) c Φ
        (iteratedCovGrad (I := I) g 0 s 1 U + iteratedCovGrad (I := I) g 0 s 1 V) = _
    exact operatorFieldApplication_add_right (I := I) (M := M) g (s + 1) c Φ _ _
  map_smul' := fun a U => by
    simp only [RingHom.id_apply, iteratedCovGrad_smul, operatorFieldApplication_smul_right]

noncomputable def firstCovariantDerivativeApplication
    (g : SmoothRiemannianMetric I M) (s c : ℕ)
    (Φ : SmoothCcTensor g (s + 1) c) :
    TensorHs (I := I) (M := M) g 0 s (3 : ℝ) →L[ℝ]
      TensorHs (I := I) (M := M) g 0 c (2 : ℝ) :=
  ((ccToHsLin (I := I) (M := M) g c (2 : ℝ)).comp
      (firstCovariantDerivativeApplicationLinearMap (I := I) (M := M) g s c Φ)).extendOfNorm
    (ccToHsLin (I := I) (M := M) g s (3 : ℝ))

theorem firstCovariantDerivativeApplication_norm
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) (s c : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (Φ : SmoothCcTensor g (s + 1) c) (A : ℝ), 0 ≤ A →
        (∑ j ∈ Finset.range 3,
          ‖iteratedCovGrad (I := I) g (s + 1) c j Φ‖ ^ 2) ≤ A ^ 2 →
        ‖firstCovariantDerivativeApplication (I := I) (M := M) g s c Φ‖ ≤ C * A := by
  obtain ⟨C, hC, happ⟩ :=
    operatorFieldApplication_h2_h3_h2 (I := I) (M := M) hDim g s c
  refine ⟨C, hC, ?_⟩
  intro Φ A hA hΦ
  have hdense : DenseRange
      (ccToHsLin (I := I) (M := M) g s (3 : ℝ)) :=
    ccToHsLin_dense (I := I) (M := M) g s (by positivity)
  unfold firstCovariantDerivativeApplication
  apply LinearMap.opNorm_extendOfNorm_le hdense (mul_nonneg hC hA)
  intro U
  change
    ‖ccTensorToHs (I := I) (M := M) g c (2 : ℝ)
        (operatorFieldApply (I := I) (M := M) g (s + 1) c Φ
          (iteratedCovGrad (I := I) g 0 s 1 U))‖ ≤
      (C * A) *
        ‖ccTensorToHs (I := I) (M := M) g s (3 : ℝ) U‖
  simpa only [mul_assoc] using happ Φ U A hA hΦ

theorem firstCovariantDerivativeApplication_ccTensorToHs
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) (s c : ℕ)
    (Φ : SmoothCcTensor g (s + 1) c) (U : SmoothCcTensor g 0 s) :
    firstCovariantDerivativeApplication (I := I) (M := M) g s c Φ
        (ccTensorToHs (I := I) (M := M) g s (3 : ℝ) U) =
      ccTensorToHs (I := I) (M := M) g c (2 : ℝ)
        (operatorFieldApply (I := I) (M := M) g (s + 1) c Φ
          (iteratedCovGrad (I := I) g 0 s 1 U)) := by
  let A : ℝ := Real.sqrt
    (∑ j ∈ Finset.range 3,
      ‖iteratedCovGrad (I := I) g (s + 1) c j Φ‖ ^ 2)
  have hsum : 0 ≤
      ∑ j ∈ Finset.range 3,
        ‖iteratedCovGrad (I := I) g (s + 1) c j Φ‖ ^ 2 :=
    Finset.sum_nonneg fun j _ => sq_nonneg _
  have hA : 0 ≤ A := Real.sqrt_nonneg _
  have hΦ :
      (∑ j ∈ Finset.range 3,
        ‖iteratedCovGrad (I := I) g (s + 1) c j Φ‖ ^ 2) ≤ A ^ 2 := by
    rw [show A ^ 2 =
      ∑ j ∈ Finset.range 3,
        ‖iteratedCovGrad (I := I) g (s + 1) c j Φ‖ ^ 2 by
      simp only [A, Real.sq_sqrt hsum]]
  obtain ⟨C, _, happ⟩ :=
    operatorFieldApplication_h2_h3_h2 (I := I) (M := M) hDim g s c
  have hdense : DenseRange
      (ccToHsLin (I := I) (M := M) g s (3 : ℝ)) :=
    ccToHsLin_dense (I := I) (M := M) g s (by positivity)
  change
    (((ccToHsLin (I := I) (M := M) g c (2 : ℝ)).comp
        (firstCovariantDerivativeApplicationLinearMap (I := I) (M := M) g s c Φ)).extendOfNorm
      (ccToHsLin (I := I) (M := M) g s (3 : ℝ)))
        ((ccToHsLin (I := I) (M := M) g s (3 : ℝ)) U) =
      ((ccToHsLin (I := I) (M := M) g c (2 : ℝ)).comp
        (firstCovariantDerivativeApplicationLinearMap (I := I) (M := M) g s c Φ)) U
  apply LinearMap.extendOfNorm_eq hdense
  refine ⟨C * A, ?_⟩
  intro V
  change
    ‖ccTensorToHs (I := I) (M := M) g c (2 : ℝ)
        (operatorFieldApply (I := I) (M := M) g (s + 1) c Φ
          (iteratedCovGrad (I := I) g 0 s 1 V))‖ ≤
      (C * A) *
        ‖ccTensorToHs (I := I) (M := M) g s (3 : ℝ) V‖
  simpa only [mul_assoc] using happ Φ V A hA hΦ

end Connection
end Integral
end DifferentialGeometry

end
