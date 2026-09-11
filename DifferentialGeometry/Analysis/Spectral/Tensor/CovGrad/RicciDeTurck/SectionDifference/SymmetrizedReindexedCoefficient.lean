import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.ConnectionDifference.KoszulCovariantDerivative
import DifferentialGeometry.Geometry.Curvature.RoughLaplacian.ConnectionDifference.CovariantDerivative
import DifferentialGeometry.Geometry.Metric.TensorInner.Cotangent.InverseMetricField
import DifferentialGeometry.Geometry.Connection.MetricCompatibility.Tensor.InverseMetric
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.Metric.CometricDoubleTrace
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.Permutation.Naturality
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.ConnectionDifference.RicciPalatini
import DifferentialGeometry.Geometry.Curvature.RoughLaplacian.RicciTrace.Basic
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.TensorAction.Field
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.RicciDeTurck.SectionDifference.KoszulSecondCovariantDerivative
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.RicciDeTurck.SectionDifference.PrincipalEndomorphismTrace
open DifferentialGeometry.Geometry.Connection.Realization DifferentialGeometry.Tensor.Multilinear
open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection

noncomputable section


open Bundle Manifold Set Filter DifferentialGeometry.Tensor0SBundle
open scoped Manifold Topology ContDiff BigOperators Matrix

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2

open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.PDE.RicciFlow DifferentialGeometry.Analysis.Sobolev
    DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Analysis.Spectral.MetricRealization
open DifferentialGeometry.Analysis.Spectral.DeTurck

section NormedSpaceModel

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

noncomputable def ccTensor02Symm (g₀ : SmoothRiemannianMetric I M) (T : SmoothCcTensor g₀ 0 2) :
    SmoothCcTensor g₀ 0 2 :=
  (1 / 2 : ℝ) • (T + domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 2) 1) T)

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
omit [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma unitModel_eq_ccTensorBilin (g₀ : SmoothRiemannianMetric I M)
    (S : SmoothCcTensor g₀ 0 2) (b : M) (u w : TangentSpace I b) :
    unitModel (I := I) (M := M) g₀ 2 S b ![u, w] = smoothCcTensorBilinForm (I := I) g₀ S b u w := by
  rw [ccTensorBilin_apply (I := I) g₀ S b u w, ccTensorModel]
  rw [show ccTensorMultilinear (I := I) g₀ S b =
      (show Tensor0SSpace 0 I b →L[ℝ] Tensor0SSpace 2 I b from S.toSection b)
        (unitZeroSec (I := I) (M := M) b) from rfl]
  rw [unitModel]
  refine congrArg _ ?_
  funext k
  fin_cases k <;> rfl

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
omit [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma ccTensorBilin_domDomCongrSection_swap (g₀ : SmoothRiemannianMetric I M)
    (T : SmoothCcTensor g₀ 0 2) (b : M) (u w : TangentSpace I b) :
    smoothCcTensorBilinForm (I := I) g₀
        (domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 2) 1) T) b u w =
      smoothCcTensorBilinForm (I := I) g₀ T b w u := by
  rw [← unitModel_eq_ccTensorBilin (I := I) (M := M) g₀ _ b u w,
      ← unitModel_eq_ccTensorBilin (I := I) (M := M) g₀ T b w u]
  rw [domDomCongrSection_unitModel (I := I) g₀ (Equiv.swap (0 : Fin 2) 1) T b,
      ContinuousMultilinearMap.domDomCongr_apply]
  congr 1
  funext k
  fin_cases k <;> rfl

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
omit [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
lemma ccTensorBilin_add (g₀ : SmoothRiemannianMetric I M)
    (S T : SmoothCcTensor g₀ 0 2) (b : M) (u w : TangentSpace I b) :
    smoothCcTensorBilinForm (I := I) g₀ (S + T) b u w =
      smoothCcTensorBilinForm (I := I) g₀ S b u w + smoothCcTensorBilinForm (I := I) g₀ T b u
        w := by
  rw [← unitModel_eq_ccTensorBilin (I := I) (M := M) g₀ (S + T) b u w,
      ← unitModel_eq_ccTensorBilin (I := I) (M := M) g₀ S b u w,
      ← unitModel_eq_ccTensorBilin (I := I) (M := M) g₀ T b u w]
  rw [DifferentialGeometry.Analysis.Parabolic.TensorSpectral.unitModel_add
    (I := I) (M := M) g₀ 2 S T b, add_apply]

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M]
    [SigmaCompactSpace M] in
lemma ccTensorBilin_smul (g₀ : SmoothRiemannianMetric I M)
    (c : ℝ) (S : SmoothCcTensor g₀ 0 2) (b : M) (u w : TangentSpace I b) :
    smoothCcTensorBilinForm (I := I) g₀ (c • S) b u w =
      c * smoothCcTensorBilinForm (I := I) g₀ S b u w := by
  rw [ccTensorBilin_apply, ccTensorBilin_apply, ccTensorModel_smul,
    smul_apply, smul_eq_mul]

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
omit [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
theorem smoothCcTensorBilinForm_ccTensor02Symm (g₀ : SmoothRiemannianMetric I M) (T : SmoothCcTensor g₀ 0 2)
    (b : M) (u w : TangentSpace I b) :
    smoothCcTensorBilinForm (I := I) g₀ (ccTensor02Symm (I := I) (M := M) g₀ T) b u w =
      ccTensorBilinSymm (I := I) g₀ T b u w := by
  rw [ccTensor02Symm, ccTensorBilin_smul, ccTensorBilin_add,
    ccTensorBilin_domDomCongrSection_swap (I := I) (M := M) g₀ T b u w,
    ccTensorBilinSymm_apply]

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
omit [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
theorem ccTensor02Symm_eq_self (g₀ : SmoothRiemannianMetric I M)
    (S : SmoothCcTensor g₀ 0 2)
    (hsymm : ∀ (x : M) (u w : TangentSpace I x),
      smoothCcTensorBilinForm (I := I) g₀ S x u w = smoothCcTensorBilinForm (I := I) g₀ S x w u) :
    ccTensor02Symm (I := I) (M := M) g₀ S = S := by
  have hswap : domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 2) 1) S = S := by
    refine smoothCcTensor_ext_of_unitModel (I := I) (M := M) g₀ (fun x => ?_)
    rw [domDomCongrSection_unitModel]
    refine ContinuousMultilinearMap.ext (fun v => ?_)
    rw [ContinuousMultilinearMap.domDomCongr_apply]
    have hv : ∀ u w : TangentSpace I x,
        unitModel (I := I) (M := M) g₀ 2 S x ![u, w] =
          unitModel (I := I) (M := M) g₀ 2 S x ![w, u] := by
      intro u w
      rw [unitModel_eq_ccTensorBilin (I := I) (M := M) g₀ S x u w,
        unitModel_eq_ccTensorBilin (I := I) (M := M) g₀ S x w u]
      exact hsymm x u w
    have hveta : (fun i => v ((Equiv.swap (0 : Fin 2) 1) i)) = ![v 1, v 0] := by
      funext i
      fin_cases i <;> rfl
    have hveta' : v = ![v 0, v 1] := by
      funext i
      fin_cases i <;> rfl
    rw [hveta]
    conv_rhs => rw [hveta']
    exact hv (v 1) (v 0)
  have htwo : S + S = (2 : ℝ) • S := (two_smul ℝ S).symm
  rw [ccTensor02Symm, hswap, htwo, smul_smul,
    show (1 / 2 : ℝ) * 2 = 1 by norm_num, one_smul]

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
omit [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
theorem smoothCcTensorBilinForm_ccTensor02Symm_eq_metric_sub (g₀ g₁ : SmoothRiemannianMetric I M) (T : SmoothCcTensor g₀ 0 2)
    (hg₁ : ∀ (b : M) (u w : TangentSpace I b),
      g₁.inner b u w = g₀.inner b u w + ccTensorBilinSymm (I := I) g₀ T b u w)
    (b : M) (u w : TangentSpace I b) :
    smoothCcTensorBilinForm (I := I) g₀ (ccTensor02Symm (I := I) (M := M) g₀ T) b u w =
      g₁.inner b u w - g₀.inner b u w := by
  rw [smoothCcTensorBilinForm_ccTensor02Symm (I := I) (M := M) g₀ T b u w, hg₁ b u w]
  ring

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
omit [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma unitModel_domDomCongrSection_swap_add (g₀ : SmoothRiemannianMetric I M)
    (T T' : SmoothCcTensor g₀ 0 2) (x : M) :
    unitModel (I := I) (M := M) g₀ 2
        (domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 2) 1) (T + T')) x =
      unitModel (I := I) (M := M) g₀ 2
          (domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 2) 1) T) x +
        unitModel (I := I) (M := M) g₀ 2
          (domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 2) 1) T') x := by
  rw [domDomCongrSection_unitModel, domDomCongrSection_unitModel, domDomCongrSection_unitModel,
    DifferentialGeometry.Analysis.Parabolic.TensorSpectral.unitModel_add]
  apply ContinuousMultilinearMap.ext
  intro m
  rw [ContinuousMultilinearMap.domDomCongr_apply, add_apply,
    add_apply, ContinuousMultilinearMap.domDomCongr_apply,
    ContinuousMultilinearMap.domDomCongr_apply]

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
omit [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma unitModel_domDomCongrSection_swap_smul (g₀ : SmoothRiemannianMetric I M)
    (c : ℝ) (T : SmoothCcTensor g₀ 0 2) (x : M) :
    unitModel (I := I) (M := M) g₀ 2
        (domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 2) 1) (c • T)) x =
      c • unitModel (I := I) (M := M) g₀ 2
        (domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 2) 1) T) x := by
  rw [domDomCongrSection_unitModel, domDomCongrSection_unitModel]
  have hsmul : unitModel (I := I) (M := M) g₀ 2 (c • T) x =
      c • unitModel (I := I) (M := M) g₀ 2 T x := by
    simp only [unitModel]
    rw [SmoothCcTensor.toSection_smul, ContMDiffSection.coe_smul, Pi.smul_apply,
      smul_apply, Tensor0SSpace.toModel_smul]
  rw [hsmul]
  apply ContinuousMultilinearMap.ext
  intro m
  rw [ContinuousMultilinearMap.domDomCongr_apply, smul_apply,
    smul_apply, ContinuousMultilinearMap.domDomCongr_apply]

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
omit [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
theorem ccTensor02Symm_add (g₀ : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2) :
    ccTensor02Symm (I := I) (M := M) g₀ (T + T') =
      ccTensor02Symm (I := I) (M := M) g₀ T + ccTensor02Symm (I := I) (M := M) g₀ T' := by
  apply smoothCcTensor_ext_of_unitModel
  intro x
  simp only [ccTensor02Symm, DifferentialGeometry.Analysis.Parabolic.TensorSpectral.unitModel_smul, DifferentialGeometry.Analysis.Parabolic.TensorSpectral.unitModel_add, unitModel_domDomCongrSection_swap_add]
  module

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
omit [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
theorem ccTensor02Symm_smul (g₀ : SmoothRiemannianMetric I M) (c : ℝ) (T : SmoothCcTensor g₀ 0 2) :
    ccTensor02Symm (I := I) (M := M) g₀ (c • T) = c • ccTensor02Symm (I := I) (M := M) g₀ T := by
  apply smoothCcTensor_ext_of_unitModel
  intro x
  simp only [ccTensor02Symm, DifferentialGeometry.Analysis.Parabolic.TensorSpectral.unitModel_smul, DifferentialGeometry.Analysis.Parabolic.TensorSpectral.unitModel_add, unitModel_domDomCongrSection_swap_smul]
  module

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
omit [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
theorem ccTensor02Symm_neg (g₀ : SmoothRiemannianMetric I M) (T : SmoothCcTensor g₀ 0 2) :
    ccTensor02Symm (I := I) (M := M) g₀ (-T) = -ccTensor02Symm (I := I) (M := M) g₀ T := by
  have h := ccTensor02Symm_smul (I := I) (M := M) g₀ (-1 : ℝ) T
  rw [neg_one_smul, neg_one_smul] at h
  exact h

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
omit [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
theorem ccTensor02Symm_sub (g₀ : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2) :
    ccTensor02Symm (I := I) (M := M) g₀ (T - T') =
      ccTensor02Symm (I := I) (M := M) g₀ T - ccTensor02Symm (I := I) (M := M) g₀ T' := by
  rw [sub_eq_add_neg, ccTensor02Symm_add, ccTensor02Symm_neg, sub_eq_add_neg]

end NormedSpaceModel

section InnerProductSpaceModel

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

private def alignedPrincipalEndoCrossMetric (g₀ gop gcov : SmoothRiemannianMetric I M)
    (Z Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) : E →ₗ[ℝ] E where
  toFun := fun v => tangentSpaceModelContinuousLinearEquiv (I := I) x
    (inverseMetricSharpFib (I := I) gop x
      (dualToCotangent (I := I)
        (((cotangentCov (LeviCivita (I := I) g₀)).toFun
          (fun b => cotangentToCLM (I := I)
            (koszulCovGradCovec (I := I) (M := M) g₀ gcov Z Y b)) x
              ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm v) :
          TangentSpace I x →L[ℝ] ℝ) : Module.Dual ℝ (TangentSpace I x))))
  map_add' := fun v v' => by
    let e := tangentSpaceModelContinuousLinearEquiv (I := I) x
    let A := (cotangentCov (LeviCivita (I := I) g₀)).toFun
      (fun b => cotangentToCLM (I := I)
        (koszulCovGradCovec (I := I) (M := M) g₀ gcov Z Y b)) x
    change e (inverseMetricSharpFib (I := I) gop x
        (dualToCotangent (I := I)
          ((A (e.symm (v + v')) : TangentSpace I x →L[ℝ] ℝ) :
            Module.Dual ℝ (TangentSpace I x)))) =
      e (inverseMetricSharpFib (I := I) gop x
          (dualToCotangent (I := I)
            ((A (e.symm v) : TangentSpace I x →L[ℝ] ℝ) :
              Module.Dual ℝ (TangentSpace I x)))) +
        e (inverseMetricSharpFib (I := I) gop x
          (dualToCotangent (I := I)
            ((A (e.symm v') : TangentSpace I x →L[ℝ] ℝ) :
              Module.Dual ℝ (TangentSpace I x))))
    rw [map_add, map_add]
    change e (inverseMetricSharpFib (I := I) gop x
        (dualToCotangent (I := I)
          (((A (e.symm v) : TangentSpace I x →L[ℝ] ℝ) :
              Module.Dual ℝ (TangentSpace I x)) +
            ((A (e.symm v') : TangentSpace I x →L[ℝ] ℝ) :
              Module.Dual ℝ (TangentSpace I x))))) = _
    rw [dualToCotangent_addC, map_add, map_add]
  map_smul' := fun c v => by
    let e := tangentSpaceModelContinuousLinearEquiv (I := I) x
    let A := (cotangentCov (LeviCivita (I := I) g₀)).toFun
      (fun b => cotangentToCLM (I := I)
        (koszulCovGradCovec (I := I) (M := M) g₀ gcov Z Y b)) x
    change e (inverseMetricSharpFib (I := I) gop x
        (dualToCotangent (I := I)
          ((A (e.symm (c • v)) : TangentSpace I x →L[ℝ] ℝ) :
            Module.Dual ℝ (TangentSpace I x)))) =
      c • e (inverseMetricSharpFib (I := I) gop x
        (dualToCotangent (I := I)
          ((A (e.symm v) : TangentSpace I x →L[ℝ] ℝ) :
            Module.Dual ℝ (TangentSpace I x))))
    rw [map_smul, map_smul]
    change e (inverseMetricSharpFib (I := I) gop x
        (dualToCotangent (I := I)
          (c • ((A (e.symm v) : TangentSpace I x →L[ℝ] ℝ) :
            Module.Dual ℝ (TangentSpace I x))))) = _
    rw [dualToCotangent_smulC, map_smul, map_smul]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] in
omit [T2Space M] [SigmaCompactSpace M] in
@[simp] private lemma alignedPrincipalEndoCcross_apply (g₀ gop gcov : SmoothRiemannianMetric I M)
    (Z Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) (v : TangentSpace I x) :
    alignedPrincipalEndoCrossMetric (I := I) (M := M) g₀ gop gcov Z Y x
        (tangentSpaceModelContinuousLinearEquiv (I := I) x v) =
      tangentSpaceModelContinuousLinearEquiv (I := I) x
        (inverseMetricSharpFib (I := I) gop x
          (dualToCotangent (I := I)
            (((cotangentCov (LeviCivita (I := I) g₀)).toFun
              (fun b => cotangentToCLM (I := I)
                (koszulCovGradCovec (I := I) (M := M) g₀ gcov Z Y b)) x v :
              TangentSpace I x →L[ℝ] ℝ) : Module.Dual ℝ (TangentSpace I x)))) := by
  simp [alignedPrincipalEndoCrossMetric]

private def g1PrincipalVecCcross (g₀ gop gcov : SmoothRiemannianMetric I M)
    (Z Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) (v : TangentSpace I x) :
    TangentSpace I x :=
  inverseMetricSharpFib (I := I) gop x
    (dualToCotangent (I := I)
      (((cotangentCov (LeviCivita (I := I) gop)).toFun
        (fun b => cotangentToCLM (I := I)
          (koszulCovGradCovec (I := I) (M := M) g₀ gcov Z Y b)) x v :
        TangentSpace I x →L[ℝ] ℝ) : Module.Dual ℝ (TangentSpace I x)))

private def alignCorrectionVecCrossMetric (g₀ gop gcov : SmoothRiemannianMetric I M)
    (Z Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) (v : TangentSpace I x) :
    TangentSpace I x :=
  inverseMetricSharpFib (I := I) gop x
    (dualToCotangent (I := I)
      (-(LinearMap.toContinuousLinearMap
        { toFun := fun w => cotangentToCLM (I := I)
            (koszulCovGradCovec (I := I) (M := M) g₀ gcov Z Y x)
            (PDE.DeTurck.connectionDifference (I := I) gop g₀ x w v)
          map_add' := by
            intro w w'
            rw [show PDE.DeTurck.connectionDifference (I := I) gop g₀ x (w + w') v =
              PDE.DeTurck.connectionDifference (I := I) gop g₀ x w v +
                PDE.DeTurck.connectionDifference (I := I) gop g₀ x w' v from by rw [map_add]; rfl]
            rw [map_add]
          map_smul' := by
            intro c w
            rw [show PDE.DeTurck.connectionDifference (I := I) gop g₀ x (c • w) v =
              c • PDE.DeTurck.connectionDifference (I := I) gop g₀ x w v from by rw [map_smul]; rfl]
            rw [map_smul]; rfl } : TangentSpace I x →L[ℝ] ℝ)))

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
private lemma g1Principal_splitCcross
    (g₀ gop gcov : SmoothRiemannianMetric I M)
    (Z Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) (v : TangentSpace I x) :
    g1PrincipalVecCcross (I := I) (M := M) g₀ gop gcov Z Y x v =
      inverseMetricSharpFib (I := I) gop x
        (dualToCotangent (I := I)
          (((cotangentCov (LeviCivita (I := I) g₀)).toFun
            (fun b => cotangentToCLM (I := I)
              (koszulCovGradCovec (I := I) (M := M) g₀ gcov Z Y b)) x v :
            TangentSpace I x →L[ℝ] ℝ) : Module.Dual ℝ (TangentSpace I x)))
        + alignCorrectionVecCrossMetric (I := I) (M := M) g₀ gop gcov Z Y x v := by
  classical
  rw [g1PrincipalVecCcross, alignCorrectionVecCrossMetric]
  rw [← map_add]
  congr 1
  rw [← dualToCotangent_addC]
  congr 1
  ext w
  rw [LinearMap.add_apply]
  have hθ := koszulCovGradCovecCLM_mdiffAtCotangent (I := I) (M := M) g₀ gcov Z Y x
  have halign := cotangentCov_leviCivita_diff (I := I) (M := M) g₀ gop hθ v w
  rw [ContinuousLinearMap.coe_coe, ContinuousLinearMap.coe_coe]
  rw [show ((cotangentCov (LeviCivita (I := I) gop)).toFun
        (fun b => cotangentToCLM (I := I)
          (koszulCovGradCovec (I := I) (M := M) g₀ gcov Z Y b)) x v) w =
      ((cotangentCov (LeviCivita (I := I) g₀)).toFun
          (fun b => cotangentToCLM (I := I)
            (koszulCovGradCovec (I := I) (M := M) g₀ gcov Z Y b)) x v) w
        - cotangentToCLM (I := I)
            (koszulCovGradCovec (I := I) (M := M) g₀ gcov Z Y x)
            (PDE.DeTurck.connectionDifference (I := I) gop g₀ x w v) from by linarith [halign]]
  rw [show ((-(LinearMap.toContinuousLinearMap
        { toFun := fun w => cotangentToCLM (I := I)
            (koszulCovGradCovec (I := I) (M := M) g₀ gcov Z Y x)
            (PDE.DeTurck.connectionDifference (I := I) gop g₀ x w v)
          map_add' := by
            intro w w'
            rw [show PDE.DeTurck.connectionDifference (I := I) gop g₀ x (w + w') v =
              PDE.DeTurck.connectionDifference (I := I) gop g₀ x w v +
                PDE.DeTurck.connectionDifference (I := I) gop g₀ x w' v from by rw [map_add]; rfl]
            rw [map_add]
          map_smul' := by
            intro c w
            rw [show PDE.DeTurck.connectionDifference (I := I) gop g₀ x (c • w) v =
              c • PDE.DeTurck.connectionDifference (I := I) gop g₀ x w v from by rw [map_smul]; rfl]
            rw [map_smul]; rfl } : TangentSpace I x →L[ℝ] ℝ) : Module.Dual ℝ (TangentSpace I x)) w)
              =
      -(cotangentToCLM (I := I)
        (koszulCovGradCovec (I := I) (M := M) g₀ gcov Z Y x)
        (PDE.DeTurck.connectionDifference (I := I) gop g₀ x w v)) from rfl]
  ring

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [SigmaCompactSpace M] in
private lemma alignedPrincipalEndoCcross_inner_secondKoszul
    (g₀ gop gcov : SmoothRiemannianMetric I M) (S' : SmoothCcTensor g₀ 0 2)
    (hbil : ∀ (b : M) (u w : TangentSpace I b),
      smoothCcTensorBilinForm (I := I) g₀ S' b u w = gcov.inner b u w - g₀.inner b u w)
    (Z Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) (v ζ : TangentSpace I x) :
    gop.inner x
        ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm
          (alignedPrincipalEndoCrossMetric (I := I) (M := M) g₀ gop gcov Z Y x
            (tangentSpaceModelContinuousLinearEquiv (I := I) x v))) ζ =
      (1 / 2 : ℝ) *
          (Tensor0SSpace.eval (unitEvalSection (I := I) (M := M) g₀ 4
              (iteratedCovGrad (I := I) g₀ 0 2 2 S') x)
              ![v, Z x, Y x, ζ]
            + Tensor0SSpace.eval (unitEvalSection (I := I) (M := M) g₀ 4
                (iteratedCovGrad (I := I) g₀ 0 2 2 S') x)
                ![v, Y x, Z x, ζ]
            - Tensor0SSpace.eval (unitEvalSection (I := I) (M := M) g₀ 4
                (iteratedCovGrad (I := I) g₀ 0 2 2 S') x)
                ![v, ζ, Z x, Y x])
        + (1 / 2 : ℝ) *
          (Tensor0SSpace.eval (unitEvalSection (I := I) (M := M) g₀ 3
              (covGrad (I := I) (M := M) g₀ 0 2 S') x)
              ![(LeviCivita (I := I) g₀).toFun (fun b => Z b) x v, Y x, ζ]
            + Tensor0SSpace.eval (unitEvalSection (I := I) (M := M) g₀ 3
                (covGrad (I := I) (M := M) g₀ 0 2 S') x)
                ![Z x, (LeviCivita (I := I) g₀).toFun (fun b => Y b) x v, ζ]
            + Tensor0SSpace.eval (unitEvalSection (I := I) (M := M) g₀ 3
                (covGrad (I := I) (M := M) g₀ 0 2 S') x)
                ![(LeviCivita (I := I) g₀).toFun (fun b => Y b) x v, Z x, ζ]
            + Tensor0SSpace.eval (unitEvalSection (I := I) (M := M) g₀ 3
                (covGrad (I := I) (M := M) g₀ 0 2 S') x)
                ![Y x, (LeviCivita (I := I) g₀).toFun (fun b => Z b) x v, ζ]
            - Tensor0SSpace.eval (unitEvalSection (I := I) (M := M) g₀ 3
                (covGrad (I := I) (M := M) g₀ 0 2 S') x)
                ![ζ, (LeviCivita (I := I) g₀).toFun (fun b => Z b) x v, Y x]
            - Tensor0SSpace.eval (unitEvalSection (I := I) (M := M) g₀ 3
                (covGrad (I := I) (M := M) g₀ 0 2 S') x)
                ![ζ, Z x, (LeviCivita (I := I) g₀).toFun (fun b => Y b) x v]) := by
  classical
  let Xf : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
    ⟨smoothExtensionTangent (I := I) x v, smoothExtensionTangent_contMDiff (I := I) x v⟩
  have hXfx : Xf x = v := smoothExtensionTangent_eq (I := I) x v
  rw [alignedPrincipalEndoCcross_apply]
  rw [ContinuousLinearEquiv.symm_apply_apply]
  rw [inverseMetricSharpFib_inner (I := I) gop x _ ζ, cotangentToDualLinear_apply]
  rw [← hXfx]
  have hbridge := koszulCovGradCovec_covDeriv_eq_secondCovGrad (I := I) (M := M) g₀ gcov S' hbil Xf
    Y Z x ζ
  rw [hXfx]
  rw [hXfx] at hbridge
  exact hbridge

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
private lemma alignedPrincipalEndoCcross_trace_eq
    (g₀ gop gcov : SmoothRiemannianMetric I M) (S' : SmoothCcTensor g₀ 0 2)
    (hbil : ∀ (b : M) (u w : TangentSpace I b),
      smoothCcTensorBilinForm (I := I) g₀ S' b u w = gcov.inner b u w - g₀.inner b u w)
    (Z Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) :
    LinearMap.trace ℝ E (alignedPrincipalEndoCrossMetric (I := I) (M := M) g₀ gop gcov Z Y x) =
      unitModel (I := I) (M := M) g₀ 2
          (operatorFieldApply (I := I) (M := M) g₀ 4 2
            (ricciDeTurckPrincipalCoefficient (I := I) (M := M) g₀ gop)
            (iteratedCovGrad (I := I) g₀ 0 2 2 S')) x
              (fun i => tangentSpaceModelContinuousLinearEquiv (I := I) x (![Z x, Y x] i))
        + secondKoszulFrameRemainder (I := I) (M := M) g₀ gop S' Z Y x := by
  classical
  let e := tangentSpaceModelContinuousLinearEquiv (I := I) x
  rw [← trace_eq_cometricLmodel_pairing_sum (I := I) (M := M) gop x
    (alignedPrincipalEndoCrossMetric (I := I) (M := M) g₀ gop gcov Z Y x)]
  have hcoord : (fun i => tangentSpaceModelContinuousLinearEquiv (I := I) x (![Z x, Y x] i)) =
      ![e (Z x), e (Y x)] := by
    funext i
    fin_cases i <;> rfl
  rw [hcoord]
  rw [covDerivConnectionDifference_tracedPrincipal_eq_operatorFieldApply (I := I) (M := M)
    g₀ gop S' x ![e (Z x), e (Y x)]]
  rw [secondKoszulFrameRemainder]
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  let d := cometricLmodel (I := I) gop x
    (Tensor0SBundle.modelCovectorOfCLM (𝕜 := ℝ) (E := E)
      ((Module.finBasis ℝ E).cDualBasis k))
  let b := (Module.finBasis ℝ E) k
  have h := alignedPrincipalEndoCcross_inner_secondKoszul (I := I) (M := M)
    g₀ gop gcov S' hbil Z Y x (e.symm d) (e.symm b)
  convert h using 1
  all_goals with_unfolding_all rfl

def alignmentTraceRemainderCross (g₀ gop gcov : SmoothRiemannianMetric I M)
    (Z Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) : ℝ :=
  ∑ i : Fin (Module.finrank ℝ E),
    (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr
      (tangentSpaceModelContinuousLinearEquiv (I := I) x
        (alignCorrectionVecCrossMetric (I := I) (M := M) g₀ gop gcov Z Y x
          ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm
            ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) i)))) i

def palatiniTracedPrincipalRemainderCrossMetric (g₀ gop gcov : SmoothRiemannianMetric I M)
    (S' : SmoothCcTensor g₀ 0 2) (Z Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) : ℝ :=
  secondKoszulFrameRemainder (I := I) (M := M) g₀ gop S' Z Y x
    + alignmentTraceRemainderCross (I := I) (M := M) g₀ gop gcov Z Y x

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
theorem palatini_tracedPrincipal_cross_eq_combinedTrace
    (g₀ gop gcov : SmoothRiemannianMetric I M) (S' : SmoothCcTensor g₀ 0 2)
    (hbil : ∀ (b : M) (u w : TangentSpace I b),
      smoothCcTensorBilinForm (I := I) g₀ S' b u w = gcov.inner b u w - g₀.inner b u w)
    (Z Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) :
    (∑ i : Fin (Module.finrank ℝ E),
      (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr
        (tangentSpaceModelContinuousLinearEquiv (I := I) x
          (inverseMetricSharpFib (I := I) gop x
            (dualToCotangent (I := I)
              (((cotangentCov (LeviCivita (I := I) gop)).toFun
                (fun b => cotangentToCLM (I := I)
                  (koszulCovGradCovec (I := I) (M := M) g₀ gcov Z Y b)) x
                    ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm
                      ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) i)) :
                TangentSpace I x →L[ℝ] ℝ) : Module.Dual ℝ (TangentSpace I x))))) i) =
      unitModel (I := I) (M := M) g₀ 2
          (operatorFieldApply (I := I) (M := M) g₀ 4 2
            (ricciDeTurckPrincipalCoefficient (I := I) (M := M) g₀ gop)
            (iteratedCovGrad (I := I) g₀ 0 2 2 S')) x
              (fun i => tangentSpaceModelContinuousLinearEquiv (I := I) x (![Z x, Y x] i))
        + palatiniTracedPrincipalRemainderCrossMetric (I := I) (M := M)
            g₀ gop gcov S' Z Y x := by
  classical
  have hsumeq : (∑ i : Fin (Module.finrank ℝ E),
      (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr
        (tangentSpaceModelContinuousLinearEquiv (I := I) x
          (inverseMetricSharpFib (I := I) gop x
            (dualToCotangent (I := I)
              (((cotangentCov (LeviCivita (I := I) gop)).toFun
                (fun b => cotangentToCLM (I := I)
                  (koszulCovGradCovec (I := I) (M := M) g₀ gcov Z Y b)) x
                    ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm
                      ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) i)) :
                TangentSpace I x →L[ℝ] ℝ) : Module.Dual ℝ (TangentSpace I x))))) i) =
      ∑ i : Fin (Module.finrank ℝ E),
        ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr
            (alignedPrincipalEndoCrossMetric (I := I) (M := M) g₀ gop gcov Z Y x
              ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) i)) i
          + (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr
              (tangentSpaceModelContinuousLinearEquiv (I := I) x
                (alignCorrectionVecCrossMetric (I := I) (M := M) g₀ gop gcov Z Y x
                  ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm
                    ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) i)))) i) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    let e := tangentSpaceModelContinuousLinearEquiv (I := I) x
    have hsplit := g1Principal_splitCcross (I := I) (M := M) g₀ gop gcov Z Y x
      (e.symm ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) i))
    unfold g1PrincipalVecCcross at hsplit
    have hsplitE := congrArg e hsplit
    rw [hsplitE]
    rw [map_add, map_add, Finsupp.add_apply]
    rw [← alignedPrincipalEndoCcross_apply]
    simp only [e, ContinuousLinearEquiv.apply_symm_apply]
  rw [hsumeq, Finset.sum_add_distrib]
  rw [trace_eq_basis_repr_sum
    (alignedPrincipalEndoCrossMetric (I := I) (M := M) g₀ gop gcov Z Y x)]
  rw [alignedPrincipalEndoCcross_trace_eq (I := I) (M := M) g₀ gop gcov S' hbil Z Y x]
  rw [palatiniTracedPrincipalRemainderCrossMetric, alignmentTraceRemainderCross]
  ring

def palatiniTracedPrincipalDiffRemainder (g₀ g₁ g₁' : SmoothRiemannianMetric I M)
    (S S' : SmoothCcTensor g₀ 0 2) (Z Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) : ℝ :=
  palatiniTracedPrincipalRemainder (I := I) (M := M) g₀ g₁ S Z Y x
    - palatiniTracedPrincipalRemainderCrossMetric (I := I) (M := M) g₀ g₁ g₁' S' Z Y x

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
theorem palatini_tracedPrincipalDiff_covector_eq_combinedTrace
    (g₀ g₁ g₁' : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
    (hg₁ : ∀ (b : M) (u w : TangentSpace I b),
      g₁.inner b u w = g₀.inner b u w + ccTensorBilinSymm (I := I) g₀ T b u w)
    (hg₁' : ∀ (b : M) (u w : TangentSpace I b),
      g₁'.inner b u w = g₀.inner b u w + ccTensorBilinSymm (I := I) g₀ T' b u w)
    (Z Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) :
    (∑ i : Fin (Module.finrank ℝ E),
        (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr
          (tangentSpaceModelContinuousLinearEquiv (I := I) x
            (inverseMetricSharpFib (I := I) g₁ x
              (dualToCotangent (I := I)
                (((cotangentCov (LeviCivita (I := I) g₁)).toFun
                  (fun b => cotangentToCLM (I := I)
                    (koszulCovGradCovec (I := I) (M := M) g₀ g₁ Z Y b)) x
                      ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm
                        ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) i)) :
                  TangentSpace I x →L[ℝ] ℝ) : Module.Dual ℝ (TangentSpace I x))))) i)
      - (∑ i : Fin (Module.finrank ℝ E),
        (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr
          (tangentSpaceModelContinuousLinearEquiv (I := I) x
            (inverseMetricSharpFib (I := I) g₁ x
              (dualToCotangent (I := I)
                (((cotangentCov (LeviCivita (I := I) g₁)).toFun
                  (fun b => cotangentToCLM (I := I)
                    (koszulCovGradCovec (I := I) (M := M) g₀ g₁' Z Y b)) x
                      ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm
                        ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) i)) :
                  TangentSpace I x →L[ℝ] ℝ) : Module.Dual ℝ (TangentSpace I x))))) i) =
      unitModel (I := I) (M := M) g₀ 2
          (operatorFieldApply (I := I) (M := M) g₀ 4 2
            (ricciDeTurckPrincipalCoefficient (I := I) (M := M) g₀ g₁)
            (iteratedCovGrad (I := I) g₀ 0 2 2 (ccTensor02Symm (I := I) (M := M) g₀ (T - T')))) x
              (fun i => tangentSpaceModelContinuousLinearEquiv (I := I) x (![Z x, Y x] i))
        + palatiniTracedPrincipalDiffRemainder (I := I) (M := M) g₀ g₁ g₁'
            (ccTensor02Symm (I := I) (M := M) g₀ T) (ccTensor02Symm (I := I) (M := M) g₀ T') Z Y
              x := by
  classical
  have hbil : ∀ (b : M) (u w : TangentSpace I b),
      smoothCcTensorBilinForm (I := I) g₀ (ccTensor02Symm (I := I) (M := M) g₀ T) b u w =
        g₁.inner b u w - g₀.inner b u w :=
    smoothCcTensorBilinForm_ccTensor02Symm_eq_metric_sub (I := I) (M := M) g₀ g₁ T hg₁
  have hbil' : ∀ (b : M) (u w : TangentSpace I b),
      smoothCcTensorBilinForm (I := I) g₀ (ccTensor02Symm (I := I) (M := M) g₀ T') b u w =
        g₁'.inner b u w - g₀.inner b u w :=
    smoothCcTensorBilinForm_ccTensor02Symm_eq_metric_sub (I := I) (M := M) g₀ g₁' T' hg₁'
  rw [palatini_tracedPrincipal_eq_combinedTrace (I := I) (M := M) g₀ g₁
        (ccTensor02Symm (I := I) (M := M) g₀ T) hbil Z Y x]
  rw [palatini_tracedPrincipal_cross_eq_combinedTrace (I := I) (M := M) g₀ g₁ g₁'
        (ccTensor02Symm (I := I) (M := M) g₀ T') hbil' Z Y x]
  rw [palatiniTracedPrincipalDiffRemainder]
  rw [ccTensor02Symm_sub (I := I) (M := M) g₀ T T']
  rw [iteratedCovGrad_sub (I := I) g₀ 0 2 2
        (ccTensor02Symm (I := I) (M := M) g₀ T) (ccTensor02Symm (I := I) (M := M) g₀ T')]
  have hoperatorFieldApplication_sub : operatorFieldApply (I := I) (M := M) g₀ 4 2
    (ricciDeTurckPrincipalCoefficient (I := I) (M := M) g₀ g₁)
        (iteratedCovGrad (I := I) g₀ 0 2 2 (ccTensor02Symm (I := I) (M := M) g₀ T)
          - iteratedCovGrad (I := I) g₀ 0 2 2 (ccTensor02Symm (I := I) (M := M) g₀ T')) =
      operatorFieldApply (I := I) (M := M) g₀ 4 2 (ricciDeTurckPrincipalCoefficient (I := I) (M := M) g₀ g₁)
          (iteratedCovGrad (I := I) g₀ 0 2 2 (ccTensor02Symm (I := I) (M := M) g₀ T))
        - operatorFieldApply (I := I) (M := M) g₀ 4 2
          (ricciDeTurckPrincipalCoefficient (I := I) (M := M) g₀ g₁)
            (iteratedCovGrad (I := I) g₀ 0 2 2 (ccTensor02Symm (I := I) (M := M) g₀ T')) := by
    rw [show (iteratedCovGrad (I := I) g₀ 0 2 2 (ccTensor02Symm (I := I) (M := M) g₀ T)
          - iteratedCovGrad (I := I) g₀ 0 2 2 (ccTensor02Symm (I := I) (M := M) g₀ T')) =
        iteratedCovGrad (I := I) g₀ 0 2 2 (ccTensor02Symm (I := I) (M := M) g₀ T)
          + (-1 : ℝ) • iteratedCovGrad (I := I) g₀ 0 2 2 (ccTensor02Symm (I := I) (M := M) g₀ T')
            from by
      rw [neg_one_smul]; abel]
    rw [operatorFieldApplication_add_right, operatorFieldApplication_smul_right, neg_one_smul]
    abel
  rw [hoperatorFieldApplication_sub]
  have hsub : ∀ (a b : SmoothCcTensor g₀ 0 2),
      unitModel (I := I) (M := M) g₀ 2 (a - b) x
          (fun i => tangentSpaceModelContinuousLinearEquiv (I := I) x (![Z x, Y x] i)) =
        unitModel (I := I) (M := M) g₀ 2 a x
            (fun i => tangentSpaceModelContinuousLinearEquiv (I := I) x (![Z x, Y x] i))
          - unitModel (I := I) (M := M) g₀ 2 b x
            (fun i => tangentSpaceModelContinuousLinearEquiv (I := I) x (![Z x, Y x] i)) := by
    intro a b
    rw [show a - b = a + (-1 : ℝ) • b from by rw [neg_one_smul]; abel,
        DifferentialGeometry.Analysis.Parabolic.TensorSpectral.unitModel_add, DifferentialGeometry.Analysis.Parabolic.TensorSpectral.unitModel_smul]
    rw [add_apply, smul_apply]
    simp only [smul_eq_mul]
    ring
  rw [hsub]
  ring

def palatiniTracedPrincipalZRemainderCross (g₀ gop gcov : SmoothRiemannianMetric I M)
    (S' : SmoothCcTensor g₀ 0 2) (V W : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) : ℝ :=
  (∑ i : Fin (Module.finrank ℝ E),
    (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr
      (alignedPrincipalEndoCrossMetric (I := I) (M := M) g₀ gop gcov
          (⟨smoothExtensionTangent (I := I) x
              ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) i)),
            smoothExtensionTangent_contMDiff (I := I) x
              ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm
                ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) i))⟩)
          W x (tangentSpaceModelContinuousLinearEquiv (I := I) x (V x))
        - alignedPrincipalEndoZSlot (I := I) (M := M) g₀ gop S' V W x ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) i)) i)
  + (∑ i : Fin (Module.finrank ℝ E),
    (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr
      (tangentSpaceModelContinuousLinearEquiv (I := I) x
        (alignCorrectionVecCrossMetric (I := I) (M := M) g₀ gop gcov
          (⟨smoothExtensionTangent (I := I) x
              ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) i)),
            smoothExtensionTangent_contMDiff (I := I) x
              ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm
                ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) i))⟩)
          W x (V x))) i)

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
theorem palatini_tracedPrincipal_Zslot_cross_eq_combinedTrace
    (g₀ gop gcov : SmoothRiemannianMetric I M) (S' : SmoothCcTensor g₀ 0 2)
    (V W : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) :
    (∑ i : Fin (Module.finrank ℝ E),
      (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr
        (tangentSpaceModelContinuousLinearEquiv (I := I) x
          (inverseMetricSharpFib (I := I) gop x
            (dualToCotangent (I := I)
              (((cotangentCov (LeviCivita (I := I) gop)).toFun
                (fun b => cotangentToCLM (I := I)
                  (koszulCovGradCovec (I := I) (M := M) g₀ gcov
                    (⟨smoothExtensionTangent (I := I) x
                        ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm
                          ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) i)),
                      smoothExtensionTangent_contMDiff (I := I) x
                        ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm
                          ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) i))⟩) W b)) x (V x) :
                TangentSpace I x →L[ℝ] ℝ) : Module.Dual ℝ (TangentSpace I x))))) i) =
      unitModel (I := I) (M := M) g₀ 2
          (operatorFieldApply (I := I) (M := M) g₀ 4 2
            (ricciDeTurckPrincipalCoefficientZSlot (I := I) (M := M) g₀ gop)
            (iteratedCovGrad (I := I) g₀ 0 2 2 S')) x
              (fun i => tangentSpaceModelContinuousLinearEquiv (I := I) x (![V x, W x] i))
        + palatiniTracedPrincipalZRemainderCross (I := I) (M := M) g₀ gop gcov S' V W x := by
  classical
  rw [← alignedPrincipalEndoCZ_trace_eq (I := I) (M := M) g₀ gop S' V W x]
  rw [← trace_eq_basis_repr_sum (alignedPrincipalEndoZSlot (I := I) (M := M) g₀ gop S' V W x)]
  rw [palatiniTracedPrincipalZRemainderCross]
  have hsumeq : ∀ i : Fin (Module.finrank ℝ E),
      (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr
        (tangentSpaceModelContinuousLinearEquiv (I := I) x
          (inverseMetricSharpFib (I := I) gop x
            (dualToCotangent (I := I)
              (((cotangentCov (LeviCivita (I := I) gop)).toFun
                (fun b => cotangentToCLM (I := I)
                  (koszulCovGradCovec (I := I) (M := M) g₀ gcov
                    (⟨smoothExtensionTangent (I := I) x
                        ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm
                          ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) i)),
                      smoothExtensionTangent_contMDiff (I := I) x
                        ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm
                          ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) i))⟩) W b)) x (V x) :
                TangentSpace I x →L[ℝ] ℝ) : Module.Dual ℝ (TangentSpace I x))))) i =
        (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr
            (alignedPrincipalEndoZSlot (I := I) (M := M) g₀ gop S' V W x ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) i)) i
          + ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr
              (alignedPrincipalEndoCrossMetric (I := I) (M := M) g₀ gop gcov
                  (⟨smoothExtensionTangent (I := I) x
                      ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm
                        ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) i)),
                    smoothExtensionTangent_contMDiff (I := I) x
                      ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm
                        ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) i))⟩) W x
                    (tangentSpaceModelContinuousLinearEquiv (I := I) x (V x))
                - alignedPrincipalEndoZSlot (I := I) (M := M) g₀ gop S' V W x
                  ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) i)) i
            + (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr
                (tangentSpaceModelContinuousLinearEquiv (I := I) x
                  (alignCorrectionVecCrossMetric (I := I) (M := M) g₀ gop gcov
                    (⟨smoothExtensionTangent (I := I) x
                        ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm
                          ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) i)),
                      smoothExtensionTangent_contMDiff (I := I) x
                        ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm
                          ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) i))⟩) W x (V x))) i) := by
    intro i
    let e := tangentSpaceModelContinuousLinearEquiv (I := I) x
    set ei : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
      ⟨smoothExtensionTangent (I := I) x (e.symm ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) i)),
        smoothExtensionTangent_contMDiff (I := I) x (e.symm ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) i))⟩ with hei
    have hsplit := g1Principal_splitCcross (I := I) (M := M) g₀ gop gcov ei W x (V x)
    unfold g1PrincipalVecCcross at hsplit
    have hsplitE := congrArg e hsplit
    rw [hsplitE]
    rw [map_add, map_add, Finsupp.add_apply, ← alignedPrincipalEndoCcross_apply]
    rw [show (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr
          (alignedPrincipalEndoCrossMetric (I := I) (M := M) g₀ gop gcov ei W x (e (V x))) i =
        (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr
            (alignedPrincipalEndoZSlot (I := I) (M := M) g₀ gop S' V W x ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) i)) i
          + (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr
              (alignedPrincipalEndoCrossMetric (I := I) (M := M) g₀ gop gcov ei W x (e (V x))
                - alignedPrincipalEndoZSlot (I := I) (M := M) g₀ gop S' V W x
                  ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) i)) i from by
      rw [map_sub, Finsupp.sub_apply]
      ring]
    rw [add_assoc]
  rw [Finset.sum_congr rfl fun i _ => hsumeq i]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]

def palatiniTracedPrincipalZDiffRemainder (g₀ g₁ g₁' : SmoothRiemannianMetric I M)
    (S S' : SmoothCcTensor g₀ 0 2) (V W : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) : ℝ :=
  palatiniTracedPrincipalZRemainder (I := I) (M := M) g₀ g₁ S V W x
    - palatiniTracedPrincipalZRemainderCross (I := I) (M := M) g₀ g₁ g₁' S' V W x

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
theorem palatini_tracedPrincipalDiff_Zslot_eq_combinedTrace
    (g₀ g₁ g₁' : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
    (V W : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) :
    (∑ i : Fin (Module.finrank ℝ E),
        (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr
          (tangentSpaceModelContinuousLinearEquiv (I := I) x
            (inverseMetricSharpFib (I := I) g₁ x
              (dualToCotangent (I := I)
                (((cotangentCov (LeviCivita (I := I) g₁)).toFun
                  (fun b => cotangentToCLM (I := I)
                    (koszulCovGradCovec (I := I) (M := M) g₀ g₁
                      (⟨smoothExtensionTangent (I := I) x
                          ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm
                            ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) i)),
                        smoothExtensionTangent_contMDiff (I := I) x
                          ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm
                            ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) i))⟩) W b)) x (V x) :
                  TangentSpace I x →L[ℝ] ℝ) : Module.Dual ℝ (TangentSpace I x))))) i)
      - (∑ i : Fin (Module.finrank ℝ E),
        (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr
          (tangentSpaceModelContinuousLinearEquiv (I := I) x
            (inverseMetricSharpFib (I := I) g₁ x
              (dualToCotangent (I := I)
                (((cotangentCov (LeviCivita (I := I) g₁)).toFun
                  (fun b => cotangentToCLM (I := I)
                    (koszulCovGradCovec (I := I) (M := M) g₀ g₁'
                      (⟨smoothExtensionTangent (I := I) x
                          ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm
                            ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) i)),
                        smoothExtensionTangent_contMDiff (I := I) x
                          ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm
                            ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) i))⟩) W b)) x (V x) :
                  TangentSpace I x →L[ℝ] ℝ) : Module.Dual ℝ (TangentSpace I x))))) i) =
      unitModel (I := I) (M := M) g₀ 2
          (operatorFieldApply (I := I) (M := M) g₀ 4 2
            (ricciDeTurckPrincipalCoefficientZSlot (I := I) (M := M) g₀ g₁)
            (iteratedCovGrad (I := I) g₀ 0 2 2
              (ccTensor02Symm (I := I) (M := M) g₀ (T - T')))) x
              (fun i => tangentSpaceModelContinuousLinearEquiv (I := I) x (![V x, W x] i))
        + palatiniTracedPrincipalZDiffRemainder (I := I) (M := M) g₀ g₁ g₁'
            (ccTensor02Symm (I := I) (M := M) g₀ T) (ccTensor02Symm (I := I) (M := M) g₀ T')
              V W x := by
  classical
  rw [palatini_tracedPrincipal_Zslot_eq_combinedTrace (I := I) (M := M) g₀ g₁
        (ccTensor02Symm (I := I) (M := M) g₀ T) V W x]
  rw [palatini_tracedPrincipal_Zslot_cross_eq_combinedTrace (I := I) (M := M) g₀ g₁ g₁'
        (ccTensor02Symm (I := I) (M := M) g₀ T') V W x]
  rw [palatiniTracedPrincipalZDiffRemainder]
  rw [ccTensor02Symm_sub (I := I) (M := M) g₀ T T']
  rw [iteratedCovGrad_sub (I := I) g₀ 0 2 2
        (ccTensor02Symm (I := I) (M := M) g₀ T) (ccTensor02Symm (I := I) (M := M) g₀ T')]
  have hoperatorFieldApplication_sub : operatorFieldApply (I := I) (M := M) g₀ 4 2
    (ricciDeTurckPrincipalCoefficientZSlot (I := I) (M := M) g₀ g₁)
        (iteratedCovGrad (I := I) g₀ 0 2 2 (ccTensor02Symm (I := I) (M := M) g₀ T)
          - iteratedCovGrad (I := I) g₀ 0 2 2 (ccTensor02Symm (I := I) (M := M) g₀ T')) =
      operatorFieldApply (I := I) (M := M) g₀ 4 2
        (ricciDeTurckPrincipalCoefficientZSlot (I := I) (M := M) g₀ g₁)
          (iteratedCovGrad (I := I) g₀ 0 2 2 (ccTensor02Symm (I := I) (M := M) g₀ T))
        - operatorFieldApply (I := I) (M := M) g₀ 4 2
          (ricciDeTurckPrincipalCoefficientZSlot (I := I) (M := M) g₀ g₁)
            (iteratedCovGrad (I := I) g₀ 0 2 2 (ccTensor02Symm (I := I) (M := M) g₀ T')) := by
    rw [show (iteratedCovGrad (I := I) g₀ 0 2 2 (ccTensor02Symm (I := I) (M := M) g₀ T)
          - iteratedCovGrad (I := I) g₀ 0 2 2 (ccTensor02Symm (I := I) (M := M) g₀ T')) =
        iteratedCovGrad (I := I) g₀ 0 2 2 (ccTensor02Symm (I := I) (M := M) g₀ T)
          + (-1 : ℝ) • iteratedCovGrad (I := I) g₀ 0 2 2 (ccTensor02Symm (I := I) (M := M) g₀ T')
            from by
      rw [neg_one_smul]; abel]
    rw [operatorFieldApplication_add_right, operatorFieldApplication_smul_right, neg_one_smul]
    abel
  rw [hoperatorFieldApplication_sub]
  have hsub : ∀ (a b : SmoothCcTensor g₀ 0 2),
      unitModel (I := I) (M := M) g₀ 2 (a - b) x
          (fun i => tangentSpaceModelContinuousLinearEquiv (I := I) x (![V x, W x] i)) =
        unitModel (I := I) (M := M) g₀ 2 a x
            (fun i => tangentSpaceModelContinuousLinearEquiv (I := I) x (![V x, W x] i))
          - unitModel (I := I) (M := M) g₀ 2 b x
            (fun i => tangentSpaceModelContinuousLinearEquiv (I := I) x (![V x, W x] i)) := by
    intro a b
    rw [show a - b = a + (-1 : ℝ) • b from by rw [neg_one_smul]; abel,
        DifferentialGeometry.Analysis.Parabolic.TensorSpectral.unitModel_add, DifferentialGeometry.Analysis.Parabolic.TensorSpectral.unitModel_smul]
    rw [add_apply, smul_apply]
    simp only [smul_eq_mul]
    ring
  rw [hsub]
  ring

end InnerProductSpaceModel

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

namespace DifferentialGeometry.Analysis.Spectral

export DifferentialGeometry.Analysis.Parabolic.TensorSpectral (ccTensor02Symm_eq_self)

end DifferentialGeometry.Analysis.Spectral

end
