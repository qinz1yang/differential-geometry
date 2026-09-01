import DifferentialGeometry.Geometry.Connection.TensorNabla.OperatorFieldSecondGradientDecomposition
import DifferentialGeometry.Geometry.Metric.DeTurck.ConnectionDifference
import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.RicciThreeArmCorrectionFieldBound
import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.RicciLinearizationArmFields
import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.RicciPathPalatiniLinearization
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.RicciDeTurckSectionDifference
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.JetProductIntegral
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.DeTurckRemainderDefs
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.DeTurckLieHigherOrderCoeffField
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.DeTurckLie.Kernel.L2JetBound
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.DeTurckLie.Coefficient.L2JetBound
import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.CurvatureDecompositionMonomialFibreNormBound
import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.RicciArmResidualCoefficientFields
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.RicciDeTurck.Remainder.ResidualField.GridWindow.Basic
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection


noncomputable section


open Bundle Manifold Set Filter DifferentialGeometry.Tensor0SBundle MeasureTheory
open scoped Manifold Topology ContDiff BigOperators

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2

open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.Analysis.Spectral.MetricRealization
open DifferentialGeometry.Analysis.Spectral.DeTurck
open DifferentialGeometry.PDE.DeTurck.RicciLinearization

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

def deTurckLieCovariantDerivativeDecompositionC2Family (g₀ : SmoothRiemannianMetric I M)
    (T : SmoothCcTensor g₀ 0 2) {δ : ℝ}
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    (hδZ : metricCauchySchwarzBound (I := I) (M := M) g₀
      (ccTensorBilinSymm (I := I) g₀ (0 : SmoothCcTensor g₀ 0 2)) δ)
    (q : Fin 3 → Equiv.Perm (Fin 4)) (ε : Fin 3 → ℝ) (s : ℝ) : SmoothCcTensor g₀ 4 2 :=
  s • ∑ i : Fin 3, ε i • ((1 / 2 : ℝ) •
    (curvatureActionMonomialCoeffField (I := I) (M := M) g₀
        (metricPerturbationPath (I := I) g₀ T 0 hδ hδZ s)
        (ccTensorUnitValueSection (I := I) (M := M) g₀ T)
        (ccTensorUnitValueSection_contMDiff (I := I) (M := M) g₀ T) (q i)
      + curvatureActionMonomialCoeffField (I := I) (M := M) g₀
        (metricPerturbationPath (I := I) g₀ T 0 hδ hδZ s)
        (ccTensorUnitValueSection (I := I) (M := M) g₀ T)
        (ccTensorUnitValueSection_contMDiff (I := I) (M := M) g₀ T)
        ((q i).trans (Equiv.swap (0 : Fin 4) 1))))


omit [BoundarylessManifold I M] in
omit [I.Boundaryless] in
omit [SigmaCompactSpace M] in
@[simp] lemma deTurckLieCovariantDerivativeDecompositionC2Family_zero (g₀ : SmoothRiemannianMetric I M)
    (T : SmoothCcTensor g₀ 0 2) {δ : ℝ}
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    (hδZ : metricCauchySchwarzBound (I := I) (M := M) g₀
      (ccTensorBilinSymm (I := I) g₀ (0 : SmoothCcTensor g₀ 0 2)) δ)
    (q : Fin 3 → Equiv.Perm (Fin 4)) (ε : Fin 3 → ℝ) :
    deTurckLieCovariantDerivativeDecompositionC2Family (I := I) (M := M) g₀ T hδ hδZ q ε 0 = 0 := by
  rw [deTurckLieCovariantDerivativeDecompositionC2Family, zero_smul]


omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
omit [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
lemma toModel_ccTensorUnitValueSection_domDomCongrSection_swap
    (g₀ : SmoothRiemannianMetric I M) (T : SmoothCcTensor g₀ 0 2) (x : M)
    (p q' : E) :
    Tensor0SSpace.toModel (ccTensorUnitValueSection (I := I) (M := M) g₀
        (domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 2) 1) T) x)
        ![p, q'] =
      Tensor0SSpace.toModel (ccTensorUnitValueSection (I := I) (M := M) g₀ T x)
        ![q', p] := by
  have hbridge : ∀ (S : SmoothCcTensor g₀ 0 2),
      Tensor0SSpace.toModel (ccTensorUnitValueSection (I := I) (M := M) g₀ S x) =
        unitModel (I := I) (M := M) g₀ 2 S x := fun S => rfl
  rw [hbridge, hbridge, domDomCongrSection_unitModel,
    ContinuousMultilinearMap.domDomCongr_apply]
  congr 1
  funext i
  fin_cases i <;> rfl


omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M]
    [T2Space M] [SigmaCompactSpace M] in
lemma eval_ccTensorUnitValueSection_domDomCongrSection_swap
    (g₀ : SmoothRiemannianMetric I M) (T : SmoothCcTensor g₀ 0 2) (x : M)
    (p q' : TangentSpace I x) :
    Tensor0SSpace.eval (ccTensorUnitValueSection (I := I) (M := M) g₀
        (domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 2) 1) T) x)
        ![p, q'] =
      Tensor0SSpace.eval (ccTensorUnitValueSection (I := I) (M := M) g₀ T x)
        ![q', p] := by
  rw [← Tensor0SSpace.toModel_apply_tangent, ← Tensor0SSpace.toModel_apply_tangent]
  exact toModel_ccTensorUnitValueSection_domDomCongrSection_swap (I := I) (M := M) g₀ T x
    (tangentSpaceModelContinuousLinearEquiv (I := I) x p)
    (tangentSpaceModelContinuousLinearEquiv (I := I) x q')


omit [I.Boundaryless] [BoundarylessManifold I M] [SigmaCompactSpace M] in
theorem curvatureDecompositionMonomialCoeffField_unitValue_trans_swap
    (g₀ g₁ : SmoothRiemannianMetric I M) (T : SmoothCcTensor g₀ 0 2)
    (σ : Equiv.Perm (Fin 4)) :
    curvatureActionMonomialCoeffField (I := I) (M := M) g₀ g₁
        (ccTensorUnitValueSection (I := I) (M := M) g₀ T)
        (ccTensorUnitValueSection_contMDiff (I := I) (M := M) g₀ T)
        (σ.trans (Equiv.swap (0 : Fin 4) 1)) =
      curvatureActionMonomialCoeffField (I := I) (M := M) g₀ g₁
        (ccTensorUnitValueSection (I := I) (M := M) g₀
          (domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 2) 1) T))
        (ccTensorUnitValueSection_contMDiff (I := I) (M := M) g₀
          (domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 2) 1) T)) σ := by
  classical
  refine SmoothCcTensor.ext ?_
  refine ContMDiffSection.ext (fun x => ?_)
  rw [curvatureDecompositionMonomialCoeffField_toSection, curvatureDecompositionMonomialCoeffField_toSection]
  refine congrArg TensorRSSpace.ofCLM ?_
  refine ContinuousLinearMap.ext (fun G => ?_)
  refine Tensor0SSpace.toModel_injective ?_
  refine ContinuousMultilinearMap.ext (fun v => ?_)
  rw [curvatureActionMonomialTrace, curvatureActionMonomialTrace,
    curvatureDecompositionMonomialFibFixedFrame_toModel, curvatureDecompositionMonomialFibFixedFrame_toModel]
  have hcons : ∀ (p q' : E) (j : Fin 4),
      (Fin.cons p (Fin.cons q' v) : Fin 4 → E) ((Equiv.swap (0 : Fin 4) 1) j) =
        (Fin.cons q' (Fin.cons p v) : Fin 4 → E) j := by
    intro p q' j
    fin_cases j <;> rfl
  have hstep : ∀ a b : Fin (Module.finrank ℝ E),
      Tensor0SSpace.eval (ccTensorUnitValueSection (I := I) (M := M) g₀ T x)
          ![smoothOrthoFrame (I := I) g₁ x a x, smoothOrthoFrame (I := I) g₁ x b x] *
        Tensor0SSpace.toModel (𝕜 := ℝ) G
          (fun i => (Fin.cons
            (tangentSpaceModelContinuousLinearEquiv (I := I) x (smoothOrthoFrame (I := I) g₁ x a x))
            (Fin.cons
              (tangentSpaceModelContinuousLinearEquiv (I := I) x (smoothOrthoFrame (I := I) g₁ x b x)) v) : Fin 4 → E)
            ((σ.trans (Equiv.swap (0 : Fin 4) 1)) i)) =
      Tensor0SSpace.eval (ccTensorUnitValueSection (I := I) (M := M) g₀ T x)
          ![smoothOrthoFrame (I := I) g₁ x a x, smoothOrthoFrame (I := I) g₁ x b x] *
        Tensor0SSpace.toModel (𝕜 := ℝ) G
          (fun i => (Fin.cons
            (tangentSpaceModelContinuousLinearEquiv (I := I) x (smoothOrthoFrame (I := I) g₁ x b x))
            (Fin.cons
              (tangentSpaceModelContinuousLinearEquiv (I := I) x (smoothOrthoFrame (I := I) g₁ x a x)) v) : Fin 4 → E) (σ i)) := by
    intro a b
    congr 1
    refine congrArg _ ?_
    funext i
    exact hcons _ _ (σ i)
  rw [Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => hstep a b))]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => ?_))
  rw [eval_ccTensorUnitValueSection_domDomCongrSection_swap]


omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
omit [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
lemma ccTensorUnitValueSection_add (g₀ : SmoothRiemannianMetric I M)
    (S S' : SmoothCcTensor g₀ 0 2) (y : M) :
    ccTensorUnitValueSection (I := I) (M := M) g₀ (S + S') y =
      ccTensorUnitValueSection (I := I) (M := M) g₀ S y +
        ccTensorUnitValueSection (I := I) (M := M) g₀ S' y := by
  have h : ((S + S').toSection y : TensorRSSpace 0 2 I y) =
      (S.toSection y : TensorRSSpace 0 2 I y) + (S'.toSection y : TensorRSSpace 0 2 I y) := by
    rw [SmoothCcTensor.toSection_add, ContMDiffSection.coe_add, Pi.add_apply]
  rw [ccTensorUnitValueSection, ccTensorUnitValueSection, ccTensorUnitValueSection, h]
  rfl


omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
omit [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
lemma ccTensorUnitValueSection_smul (g₀ : SmoothRiemannianMetric I M) (c : ℝ)
    (S : SmoothCcTensor g₀ 0 2) (y : M) :
    ccTensorUnitValueSection (I := I) (M := M) g₀ (c • S) y =
      c • ccTensorUnitValueSection (I := I) (M := M) g₀ S y := by
  have h : ((c • S).toSection y : TensorRSSpace 0 2 I y) =
      c • (S.toSection y : TensorRSSpace 0 2 I y) := by
    rw [SmoothCcTensor.toSection_smul, ContMDiffSection.coe_smul, Pi.smul_apply]
  rw [ccTensorUnitValueSection, ccTensorUnitValueSection, h]
  rfl


omit [I.Boundaryless] [BoundarylessManifold I M] [SigmaCompactSpace M] in
theorem curvatureDecompositionMonomialCoeffField_unitValue_add
    (g₀ g₁ : SmoothRiemannianMetric I M) (S S' : SmoothCcTensor g₀ 0 2)
    (σ : Equiv.Perm (Fin 4)) :
    curvatureActionMonomialCoeffField (I := I) (M := M) g₀ g₁
        (ccTensorUnitValueSection (I := I) (M := M) g₀ (S + S'))
        (ccTensorUnitValueSection_contMDiff (I := I) (M := M) g₀ (S + S')) σ =
      curvatureActionMonomialCoeffField (I := I) (M := M) g₀ g₁
          (ccTensorUnitValueSection (I := I) (M := M) g₀ S)
          (ccTensorUnitValueSection_contMDiff (I := I) (M := M) g₀ S) σ
        + curvatureActionMonomialCoeffField (I := I) (M := M) g₀ g₁
          (ccTensorUnitValueSection (I := I) (M := M) g₀ S')
          (ccTensorUnitValueSection_contMDiff (I := I) (M := M) g₀ S') σ := by
  classical
  refine SmoothCcTensor.ext ?_
  refine ContMDiffSection.ext (fun x => ?_)
  rw [SmoothCcTensor.toSection_add, ContMDiffSection.coe_add, Pi.add_apply,
    curvatureDecompositionMonomialCoeffField_toSection, curvatureDecompositionMonomialCoeffField_toSection,
    curvatureDecompositionMonomialCoeffField_toSection]
  refine tensorRSSpace_ext 4 2 x (fun G => ?_)
  refine Tensor0SSpace.toModel_injective ?_
  refine ContinuousMultilinearMap.ext (fun v => ?_)
  have hadd : (show Tensor0SSpace 4 I x →L[ℝ] Tensor0SSpace 2 I x from
      (TensorRSSpace.ofCLM (curvatureActionMonomialTrace (I := I) (M := M) g₁
          (ccTensorUnitValueSection (I := I) (M := M) g₀ S) σ x)
        + TensorRSSpace.ofCLM (curvatureActionMonomialTrace (I := I) (M := M) g₁
          (ccTensorUnitValueSection (I := I) (M := M) g₀ S') σ x))) G =
      curvatureActionMonomialTrace (I := I) (M := M) g₁
          (ccTensorUnitValueSection (I := I) (M := M) g₀ S) σ x G
        + curvatureActionMonomialTrace (I := I) (M := M) g₁
          (ccTensorUnitValueSection (I := I) (M := M) g₀ S') σ x G := rfl
  rw [hadd]
  simp only [Tensor0SSpace.toModel_add, add_apply,
    TensorRSSpace.ofCLM]
  rw [curvatureActionMonomialTrace, curvatureActionMonomialTrace,
    curvatureActionMonomialTrace, curvatureDecompositionMonomialFibFixedFrame_toModel,
    curvatureDecompositionMonomialFibFixedFrame_toModel, curvatureDecompositionMonomialFibFixedFrame_toModel]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  rw [ccTensorUnitValueSection_add]
  simp only [Tensor0SSpace.eval_add]
  rw [add_mul]


omit [I.Boundaryless] [BoundarylessManifold I M] [SigmaCompactSpace M] in
theorem curvatureDecompositionMonomialCoeffField_unitValue_smul
    (g₀ g₁ : SmoothRiemannianMetric I M) (c : ℝ) (S : SmoothCcTensor g₀ 0 2)
    (σ : Equiv.Perm (Fin 4)) :
    curvatureActionMonomialCoeffField (I := I) (M := M) g₀ g₁
        (ccTensorUnitValueSection (I := I) (M := M) g₀ (c • S))
        (ccTensorUnitValueSection_contMDiff (I := I) (M := M) g₀ (c • S)) σ =
      c • curvatureActionMonomialCoeffField (I := I) (M := M) g₀ g₁
          (ccTensorUnitValueSection (I := I) (M := M) g₀ S)
          (ccTensorUnitValueSection_contMDiff (I := I) (M := M) g₀ S) σ := by
  classical
  refine SmoothCcTensor.ext ?_
  refine ContMDiffSection.ext (fun x => ?_)
  rw [SmoothCcTensor.toSection_smul, ContMDiffSection.coe_smul, Pi.smul_apply,
    curvatureDecompositionMonomialCoeffField_toSection, curvatureDecompositionMonomialCoeffField_toSection]
  refine tensorRSSpace_ext 4 2 x (fun G => ?_)
  refine Tensor0SSpace.toModel_injective ?_
  refine ContinuousMultilinearMap.ext (fun v => ?_)
  have hsmul : (show Tensor0SSpace 4 I x →L[ℝ] Tensor0SSpace 2 I x from
      (c • TensorRSSpace.ofCLM (curvatureActionMonomialTrace (I := I) (M := M) g₁
        (ccTensorUnitValueSection (I := I) (M := M) g₀ S) σ x))) G =
      c • curvatureActionMonomialTrace (I := I) (M := M) g₁
        (ccTensorUnitValueSection (I := I) (M := M) g₀ S) σ x G := rfl
  rw [hsmul]
  simp only [Tensor0SSpace.toModel_smul, smul_apply, smul_eq_mul,
    TensorRSSpace.ofCLM]
  rw [curvatureActionMonomialTrace, curvatureActionMonomialTrace,
    curvatureDecompositionMonomialFibFixedFrame_toModel, curvatureDecompositionMonomialFibFixedFrame_toModel]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  rw [ccTensorUnitValueSection_smul]
  simp only [Tensor0SSpace.eval_smul, smul_eq_mul]
  ring


omit [I.Boundaryless] [BoundarylessManifold I M] [SigmaCompactSpace M] in
theorem curvatureDecompositionMonomialCoeffField_unitValue_pair_eq_symmS
    (g₀ g₁ : SmoothRiemannianMetric I M) (T : SmoothCcTensor g₀ 0 2)
    (σ : Equiv.Perm (Fin 4)) :
    (1 / 2 : ℝ) •
      (curvatureActionMonomialCoeffField (I := I) (M := M) g₀ g₁
          (ccTensorUnitValueSection (I := I) (M := M) g₀ T)
          (ccTensorUnitValueSection_contMDiff (I := I) (M := M) g₀ T) σ
        + curvatureActionMonomialCoeffField (I := I) (M := M) g₀ g₁
          (ccTensorUnitValueSection (I := I) (M := M) g₀ T)
          (ccTensorUnitValueSection_contMDiff (I := I) (M := M) g₀ T)
          (σ.trans (Equiv.swap (0 : Fin 4) 1))) =
      curvatureActionMonomialCoeffField (I := I) (M := M) g₀ g₁
        (ccTensorUnitValueSection (I := I) (M := M) g₀ (ccTensor02Symm (I := I) (M := M) g₀ T))
        (ccTensorUnitValueSection_contMDiff (I := I) (M := M) g₀
          (ccTensor02Symm (I := I) (M := M) g₀ T)) σ := by
  rw [show curvatureActionMonomialCoeffField (I := I) (M := M) g₀ g₁
        (ccTensorUnitValueSection (I := I) (M := M) g₀ (ccTensor02Symm (I := I) (M := M) g₀ T))
        (ccTensorUnitValueSection_contMDiff (I := I) (M := M) g₀
          (ccTensor02Symm (I := I) (M := M) g₀ T)) σ =
      curvatureActionMonomialCoeffField (I := I) (M := M) g₀ g₁
        (ccTensorUnitValueSection (I := I) (M := M) g₀ ((1 / 2 : ℝ) •
          (T + domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 2) 1) T)))
        (ccTensorUnitValueSection_contMDiff (I := I) (M := M) g₀ ((1 / 2 : ℝ) •
          (T + domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 2) 1) T))) σ from by
    congr 1]
  rw [curvatureDecompositionMonomialCoeffField_unitValue_smul,
    curvatureDecompositionMonomialCoeffField_unitValue_add,
    curvatureDecompositionMonomialCoeffField_unitValue_trans_swap]


omit [BoundarylessManifold I M] in
omit [I.Boundaryless] in
omit [SigmaCompactSpace M] in
theorem deTurckLieCovariantDerivativeDecompositionC2Family_eq_symmS_weight (g₀ : SmoothRiemannianMetric I M)
    (T : SmoothCcTensor g₀ 0 2) {δ : ℝ}
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    (hδZ : metricCauchySchwarzBound (I := I) (M := M) g₀
      (ccTensorBilinSymm (I := I) g₀ (0 : SmoothCcTensor g₀ 0 2)) δ)
    (q : Fin 3 → Equiv.Perm (Fin 4)) (ε : Fin 3 → ℝ) (s : ℝ) :
    deTurckLieCovariantDerivativeDecompositionC2Family (I := I) (M := M) g₀ T hδ hδZ q ε s =
      s • ∑ i : Fin 3, ε i •
        curvatureActionMonomialCoeffField (I := I) (M := M) g₀
          (metricPerturbationPath (I := I) g₀ T 0 hδ hδZ s)
          (ccTensorUnitValueSection (I := I) (M := M) g₀ (ccTensor02Symm (I := I) (M := M) g₀ T))
          (ccTensorUnitValueSection_contMDiff (I := I) (M := M) g₀
            (ccTensor02Symm (I := I) (M := M) g₀ T)) (q i) := by
  rw [deTurckLieCovariantDerivativeDecompositionC2Family]
  congr 1
  refine Finset.sum_congr rfl (fun i _ => ?_)
  congr 1
  exact curvatureDecompositionMonomialCoeffField_unitValue_pair_eq_symmS (I := I) (M := M) g₀
    (metricPerturbationPath (I := I) g₀ T 0 hδ hδZ s) T (q i)

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
