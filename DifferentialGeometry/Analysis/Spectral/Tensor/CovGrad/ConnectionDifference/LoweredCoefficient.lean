import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.ConnectionDifference.RecoveryEndomorphismJetBounds
import DifferentialGeometry.Geometry.Connection.LeviCivita.LoweredDifference

open DifferentialGeometry.TensorMetric (riemannianFiberNormSq
  riemannianFiberNormSq_eq_tensorInnerPointwise tensorInnerPointwise_smul_left
  tensorInnerPointwise_smul_right)
open DifferentialGeometry.Tensor.Multilinear
open DifferentialGeometry.Geometry.Connection
  (metricLoweredConnectionDifferenceCovector metricLoweredConnectionDifferenceField)
open DifferentialGeometry.Analysis.Elliptic
open DifferentialGeometry.Geometry.Curvature

noncomputable section


open Bundle Manifold Set Filter DifferentialGeometry.Tensor0SBundle
open scoped Manifold Topology ContDiff BigOperators Matrix

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

open DifferentialGeometry.Integral.L2

open DifferentialGeometry.PDE.RicciFlow DifferentialGeometry.Analysis.Sobolev
    DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Analysis.Spectral.DeTurck
open DifferentialGeometry.Analysis.Sobolev.TensorHilbert

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

section NormedConnectionDifferenceLowering

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

def metricLoweredConnectionDifferenceCoefficient (g₀ g₁ : SmoothRiemannianMetric I M) : SmoothCcTensor g₀ 0 3 where
  toSection :=
    MixedSection.fromMultilinearSection (𝕜 := ℝ) (F := E) (IB := I)
      (E := (TangentSpace I : M → Type _)) ∞ (DifferentialGeometry.Geometry.Connection.metricLoweredConnectionDifferenceField (I := I) g₀ g₁)
  hasCompactSupport := HasCompactSupport.of_compactSpace _

omit [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
private lemma connectionDifferenceLoweredCc_unitModel (g₀ g₁ : SmoothRiemannianMetric I M) (x : M) :
    unitModel (I := I) (M := M) g₀ 3 (metricLoweredConnectionDifferenceCoefficient (I := I) g₀ g₁) x =
      Tensor0SSpace.toModel (DifferentialGeometry.Geometry.Connection.metricLoweredConnectionDifferenceCovector (I := I) g₀ g₁ x) := by
  rw [unitModel]
  rw [show (metricLoweredConnectionDifferenceCoefficient (I := I) g₀ g₁).toSection x (unitTensor (I := I) (M := M) x) =
      (MixedSection.eval₀ (F := E) (E := (TangentSpace I : M → Type _)) x).smulRight
          (DifferentialGeometry.Geometry.Connection.metricLoweredConnectionDifferenceField (I := I) g₀ g₁ x)
          (ContinuousMultilinearMap.constOfIsEmpty ℝ (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ))
      from rfl]
  rw [ContinuousLinearMap.smulRight_apply, MixedSection.eval₀_apply,
    ContinuousMultilinearMap.constOfIsEmpty_apply, one_smul]
  rfl

omit [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
private lemma connectionDifferenceLoweredCc_unitModel_apply (g₀ g₁ : SmoothRiemannianMetric I M) (x : M)
    (m : Fin 3 → E) :
    unitModel (I := I) (M := M) g₀ 3 (metricLoweredConnectionDifferenceCoefficient (I := I) g₀ g₁) x m =
      g₀.inner x (PDE.DeTurck.connectionDifference (I := I) g₁ g₀ x
        ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm (m 0))
        ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm (m 1)))
        ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm (m 2)) := by
  rw [connectionDifferenceLoweredCc_unitModel]
  rw [Tensor0SSpace.toModel_apply_model_vector]
  rfl

end NormedConnectionDifferenceLowering

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
    [T2Space M] [SigmaCompactSpace M] in
private lemma interior_product_toModel_eval (s : ℕ) (x : M) (v : TangentSpace I x)
    (D : Tensor0SSpace (s + 1) I x) (w : Fin s → E) :
    Tensor0SSpace.toModel
        (Tensor0SBundle.interiorProduct (𝕜 := ℝ) (I := I) s x v D) w =
      Tensor0SSpace.toModel D
        (Fin.cons (tangentSpaceModelContinuousLinearEquiv (I := I) x v) w) := by
  have h1 : Tensor0SSpace.toModel
      (Tensor0SBundle.interiorProduct (𝕜 := ℝ) (I := I) s x v D) =
      Tensor0SBundle.modelInteriorProduct (𝕜 := ℝ) (E := E) s
        (tangentSpaceModelContinuousLinearEquiv (I := I) x v)
        (Tensor0SSpace.toModel D) := rfl
  rw [h1]
  rfl

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
    [T2Space M] [SigmaCompactSpace M] in
private theorem riemannianFiberNormSq_neg_value
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (x : M) (v : TensorRSSpace r s I x) :
    riemannianFiberNormSq (I := I) (M := M) g r s x (-v) =
      riemannianFiberNormSq (I := I) (M := M) g r s x v := by
  rw [riemannianFiberNormSq_eq_tensorInnerPointwise (I := I) (M := M) g r s x (-v),
    riemannianFiberNormSq_eq_tensorInnerPointwise (I := I) (M := M) g r s x v]
  rw [TensorRSSpace.toModel_neg]
  rw [← neg_one_smul ℝ (TensorRSSpace.toModel (𝕜 := ℝ) (E := E) (I := I) (M := M)
        (r := r) (s := s) (x := x) v),
    tensorInnerPointwise_smul_left, tensorInnerPointwise_smul_right]
  ring

omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
omit [I.Boundaryless] in
private lemma connectionDifferenceSection_eq_cometricRaiseSlot0Field (g₀ g₁ : SmoothRiemannianMetric I M) :
    connectionDifferenceSection (I := I) g₁ g₀ =
      cometricRaiseSlot0Field (I := I) (M := M) g₀ 1
        (domDomCongrSection (I := I) g₀ (finRotate 3) (metricLoweredConnectionDifferenceCoefficient (I := I) g₀ g₁)) := by
  apply Integral.L2.SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rw [connectionDifferenceSection_toSection, cometricRaiseSlot0Field_toSection]
  apply tensorRSSpace_ext 1 2 x
  intro om
  apply ContinuousMultilinearMap.ext
  intro YZ
  set u : TangentSpace I x := inverseMetricSharpFib (I := I) g₀ x om with hu
  set D : Tensor0SSpace 3 I x :=
    (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 3 I x from
      (domDomCongrSection (I := I) g₀ (finRotate 3)
        (metricLoweredConnectionDifferenceCoefficient (I := I) g₀ g₁)).toSection x)
      (unitTensor (I := I) (M := M) x) with hDdef
  have hLHS : Tensor0SSpace.eval
      ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 2 I x from
        connectionDifferenceFib (I := I) g₁ g₀ x) om) YZ =
      g₀.inner x u (PDE.DeTurck.connectionDifference (I := I) g₁ g₀ x (YZ 0) (YZ 1)) := by
    rw [Tensor0SSpace.eval_eq, connectionDifferenceFib_apply_eval]
    rw [show om (fun _ : Fin 1 => PDE.DeTurck.connectionDifference (I := I) g₁ g₀ x (YZ 0) (YZ 1)) =
        cotangentToDual (I := I) (x := x) om
          (PDE.DeTurck.connectionDifference (I := I) g₁ g₀ x (YZ 0) (YZ 1)) from
      (cotangentToDual_apply (I := I) om _).symm]
    rw [show cotangentToDual (I := I) (x := x) om
          (PDE.DeTurck.connectionDifference (I := I) g₁ g₀ x (YZ 0) (YZ 1)) =
        cotangentToDualLinear (I := I) (x := x) om
          (PDE.DeTurck.connectionDifference (I := I) g₁ g₀ x (YZ 0) (YZ 1)) from rfl]
    rw [← inverseMetricSharpFib_inner (I := I) g₀ x om
      (PDE.DeTurck.connectionDifference (I := I) g₁ g₀ x (YZ 0) (YZ 1)), ← hu]
  have hRHS : Tensor0SSpace.eval
      ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 2 I x from
        cometricRaiseSlot0Fib (I := I) g₀ 1 x D) om) YZ =
      Tensor0SSpace.toModel D
        (Fin.cons (tangentSpaceModelContinuousLinearEquiv (I := I) x u)
          (fun k => tangentSpaceModelContinuousLinearEquiv (I := I) x (YZ k))) := by
    rw [cometricRaiseSlot0Fib_clm_apply (I := I) g₀ 1 x D om]
    rw [← Tensor0SSpace.toModel_apply_tangent]
    rw [interior_product_toModel_eval (I := I) (M := M) (1 + 1) x
      (inverseMetricSharpFib (I := I) g₀ x om) D
      (fun k => tangentSpaceModelContinuousLinearEquiv (I := I) x (YZ k)), ← hu]
  change Tensor0SSpace.eval
      ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 2 I x from
        connectionDifferenceFib (I := I) g₁ g₀ x) om) YZ =
    Tensor0SSpace.eval
      ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 2 I x from
        cometricRaiseSlot0Fib (I := I) g₀ 1 x D) om) YZ
  rw [hLHS, hRHS]
  have hum : unitModel (I := I) (M := M) g₀ 3
      (domDomCongrSection (I := I) g₀ (finRotate 3) (metricLoweredConnectionDifferenceCoefficient (I := I) g₀ g₁)) x =
      Tensor0SSpace.toModel D := rfl
  rw [show Tensor0SSpace.toModel D
        (Fin.cons (tangentSpaceModelContinuousLinearEquiv (I := I) x u)
          (fun k => tangentSpaceModelContinuousLinearEquiv (I := I) x (YZ k))) =
        unitModel (I := I) (M := M) g₀ 3
          (domDomCongrSection (I := I) g₀ (finRotate 3) (metricLoweredConnectionDifferenceCoefficient (I := I) g₀ g₁)) x
          ![tangentSpaceModelContinuousLinearEquiv (I := I) x u,
            tangentSpaceModelContinuousLinearEquiv (I := I) x (YZ 0),
            tangentSpaceModelContinuousLinearEquiv (I := I) x (YZ 1)] from by
    rw [hum]; congr 1; funext k; fin_cases k <;> rfl]
  rw [domDomCongrSection_unitModel, ContinuousMultilinearMap.domDomCongr_apply]
  rw [show (fun i => (![tangentSpaceModelContinuousLinearEquiv (I := I) x u,
        tangentSpaceModelContinuousLinearEquiv (I := I) x (YZ 0),
        tangentSpaceModelContinuousLinearEquiv (I := I) x (YZ 1)] : Fin 3 → E)
          ((finRotate 3) i)) =
        ![tangentSpaceModelContinuousLinearEquiv (I := I) x (YZ 0),
          tangentSpaceModelContinuousLinearEquiv (I := I) x (YZ 1),
          tangentSpaceModelContinuousLinearEquiv (I := I) x u] from by
    funext i; fin_cases i <;> simp [finRotate_apply]]
  rw [connectionDifferenceLoweredCc_unitModel_apply]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, ContinuousLinearEquiv.symm_apply_apply]
  rw [g₀.symm x u (PDE.DeTurck.connectionDifference (I := I) g₁ g₀ x (YZ 0) (YZ 1))]

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
theorem metricLoweredConnectionDifferenceCoefficient_fiber_norm_sq_eq
    (g₀ g₁ : SmoothRiemannianMetric I M) (n : ℕ) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + n) x
        ((iteratedCovGrad (I := I) g₀ 0 3 n
          (metricLoweredConnectionDifferenceCoefficient (I := I) g₀ g₁)).toSection x) =
      riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + n) x
        ((iteratedCovGrad (I := I) g₀ 1 2 n
          (connectionDifferenceSection (I := I) g₁ g₀)).toSection x) := by
  calc
    riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + n) x
        ((iteratedCovGrad (I := I) g₀ 0 3 n
          (metricLoweredConnectionDifferenceCoefficient (I := I) g₀ g₁)).toSection x)
        = riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + n) x
            ((iteratedCovGrad (I := I) g₀ 0 3 n
              (domDomCongrSection (I := I) g₀ (finRotate 3)
                (metricLoweredConnectionDifferenceCoefficient (I := I) g₀ g₁))).toSection x) :=
          (riemannianFiberNormSq_iteratedCovGrad_domDomCongrSection
            (I := I) (M := M) g₀ (finRotate 3)
            (metricLoweredConnectionDifferenceCoefficient (I := I) g₀ g₁) n x).symm
    _ = riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + n) x
          ((iteratedCovGrad (I := I) g₀ 1 2 n
            (cometricRaiseSlot0Field (I := I) (M := M) g₀ 1
              (domDomCongrSection (I := I) g₀ (finRotate 3)
                (metricLoweredConnectionDifferenceCoefficient (I := I) g₀ g₁)))).toSection x) :=
        (riemannianFiberNormSq_iteratedCovGrad_cometricRaiseSlot0Field_eq
          (I := I) (M := M) g₀ 1
          (domDomCongrSection (I := I) g₀ (finRotate 3)
            (metricLoweredConnectionDifferenceCoefficient (I := I) g₀ g₁)) n x).symm
    _ = riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + n) x
          ((iteratedCovGrad (I := I) g₀ 1 2 n
            (connectionDifferenceSection (I := I) g₁ g₀)).toSection x) := by
        rw [connectionDifferenceSection_eq_cometricRaiseSlot0Field]

omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
omit [I.Boundaryless] in
private lemma flatTermCoeffCc_true_eq_cometricRaiseSlot0Field
    (g₀ g₁ : SmoothRiemannianMetric I M) :
    flatTermCoeffCc (I := I) g₀ g₁ true =
      cometricRaiseSlot0Field (I := I) (M := M) g₀ 1 (-metricLoweredConnectionDifferenceCoefficient (I := I) g₀ g₁) := by
  apply Integral.L2.SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rw [flatTermCoeffCc_toSection, cometricRaiseSlot0Field_toSection]
  apply tensorRSSpace_ext 1 2 x
  intro om
  apply ContinuousMultilinearMap.ext
  intro YZ
  set u : TangentSpace I x := inverseMetricSharpFib (I := I) g₀ x om with hu
  set D : Tensor0SSpace 3 I x :=
    (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 3 I x from
      (-metricLoweredConnectionDifferenceCoefficient (I := I) g₀ g₁).toSection x) (unitTensor (I := I) (M := M) x) with hDdef
  have hLHS : Tensor0SSpace.eval
      ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 2 I x from
        ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 2 I x from
            (flatTermCc (I := I) g₀ g₁ true).toSection x).comp
          (show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 1 I x from
            (omRecoverEndoCc (I := I) g₀ g₁).toSection x))) om) YZ =
      - g₀.inner x (PDE.DeTurck.connectionDifference (I := I) g₁ g₀ x u (YZ 0)) (YZ 1) := by
    rw [ContinuousLinearMap.comp_apply]
    rw [show (show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 1 I x from
          (omRecoverEndoCc (I := I) g₀ g₁).toSection x) om =
        g0FlatCLM (I := I) g₁ x (inverseMetricSharpFib (I := I) g₀ x om) from by
      rw [omRecoverEndoCc_toSection]; rfl]
    rw [Tensor0SSpace.eval_eq, flatTermCc_toSection, flatTermFib_apply, flatTermPairing_apply]
    rw [show flatTermVec (I := I) g₀ g₁ true x
          (g0FlatCLM (I := I) g₁ x (inverseMetricSharpFib (I := I) g₀ x om)) (YZ 0) =
        - PDE.DeTurck.connectionDifference (I := I) g₁ g₀ x
            (inverseMetricSharpFib (I := I) g₀ x om) (YZ 0) from by
      simp only [flatTermVec, ite_true]
      rw [inverseMetricSharpFib_g0FlatCLM]]
    rw [map_neg, neg_apply, ← hu]
  have hRHS : Tensor0SSpace.eval
      ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 2 I x from
        cometricRaiseSlot0Fib (I := I) g₀ 1 x D) om) YZ =
      Tensor0SSpace.toModel D
        (Fin.cons (tangentSpaceModelContinuousLinearEquiv (I := I) x u)
          (fun k => tangentSpaceModelContinuousLinearEquiv (I := I) x (YZ k))) := by
    rw [cometricRaiseSlot0Fib_clm_apply (I := I) g₀ 1 x D om]
    rw [← Tensor0SSpace.toModel_apply_tangent]
    rw [interior_product_toModel_eval (I := I) (M := M) (1 + 1) x
      (inverseMetricSharpFib (I := I) g₀ x om) D
      (fun k => tangentSpaceModelContinuousLinearEquiv (I := I) x (YZ k)), ← hu]
  change Tensor0SSpace.eval
      ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 2 I x from
        ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 2 I x from
          (flatTermCc (I := I) g₀ g₁ true).toSection x).comp
        (show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 1 I x from
          (omRecoverEndoCc (I := I) g₀ g₁).toSection x))) om) YZ =
    Tensor0SSpace.eval
      ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 2 I x from
        cometricRaiseSlot0Fib (I := I) g₀ 1 x D) om) YZ
  rw [hLHS, hRHS]
  have hum : unitModel (I := I) (M := M) g₀ 3 (-metricLoweredConnectionDifferenceCoefficient (I := I) g₀ g₁) x =
      Tensor0SSpace.toModel D := rfl
  rw [show Tensor0SSpace.toModel D
        (Fin.cons (tangentSpaceModelContinuousLinearEquiv (I := I) x u)
          (fun k => tangentSpaceModelContinuousLinearEquiv (I := I) x (YZ k))) =
        unitModel (I := I) (M := M) g₀ 3
          (-metricLoweredConnectionDifferenceCoefficient (I := I) g₀ g₁) x
          ![tangentSpaceModelContinuousLinearEquiv (I := I) x u,
            tangentSpaceModelContinuousLinearEquiv (I := I) x (YZ 0),
            tangentSpaceModelContinuousLinearEquiv (I := I) x (YZ 1)]
        from by rw [hum]; congr 1; funext k; fin_cases k <;> rfl]
  rw [show unitModel (I := I) (M := M) g₀ 3 (-metricLoweredConnectionDifferenceCoefficient (I := I) g₀ g₁) x =
        - unitModel (I := I) (M := M) g₀ 3 (metricLoweredConnectionDifferenceCoefficient (I := I) g₀ g₁) x from by
      simp only [unitModel]
      rw [SmoothCcTensor.toSection_neg, ContMDiffSection.coe_neg, Pi.neg_apply,
        neg_apply, Tensor0SSpace.toModel_neg]]
  change -g₀.inner x
      (PDE.DeTurck.connectionDifference (I := I) g₁ g₀ x u (YZ 0)) (YZ 1) =
    -unitModel (I := I) (M := M) g₀ 3
      (metricLoweredConnectionDifferenceCoefficient (I := I) g₀ g₁) x
      ![tangentSpaceModelContinuousLinearEquiv (I := I) x u,
        tangentSpaceModelContinuousLinearEquiv (I := I) x (YZ 0),
        tangentSpaceModelContinuousLinearEquiv (I := I) x (YZ 1)]
  rw [connectionDifferenceLoweredCc_unitModel_apply]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, ContinuousLinearEquiv.symm_apply_apply]

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
theorem riemannianFiberNormSq_iteratedCovGrad_flatTermCoefficient_eq_connectionDifference
    (g₀ g₁ : SmoothRiemannianMetric I M) (i : ℕ) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + i) x
        ((iteratedCovGrad (I := I) g₀ 1 2 i
          (flatTermCoeffCc (I := I) g₀ g₁ true)).toSection x) =
      riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + i) x
        ((iteratedCovGrad (I := I) g₀ 1 2 i (connectionDifferenceSection (I := I) g₁ g₀)).toSection x) := by
  calc riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + i) x
          ((iteratedCovGrad (I := I) g₀ 1 2 i (flatTermCoeffCc (I := I) g₀ g₁ true)).toSection x)
      = riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + i) x
          ((iteratedCovGrad (I := I) g₀ 1 2 i
            (cometricRaiseSlot0Field (I := I) (M := M) g₀ 1
              (-metricLoweredConnectionDifferenceCoefficient (I := I) g₀ g₁))).toSection x) := by
        rw [flatTermCoeffCc_true_eq_cometricRaiseSlot0Field]
    _ = riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + i) x
          ((iteratedCovGrad (I := I) g₀ 0 3 i
            (-metricLoweredConnectionDifferenceCoefficient (I := I) g₀ g₁)).toSection x) :=
        riemannianFiberNormSq_iteratedCovGrad_cometricRaiseSlot0Field_eq (I := I) (M := M) g₀ 1
          (-metricLoweredConnectionDifferenceCoefficient (I := I) g₀ g₁) i x
    _ = riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + i) x
          ((iteratedCovGrad (I := I) g₀ 0 3 i (metricLoweredConnectionDifferenceCoefficient (I := I) g₀ g₁)).toSection x) := by
        rw [iteratedCovGrad_neg]
        rw [show ((-(iteratedCovGrad (I := I) g₀ 0 3 i
              (metricLoweredConnectionDifferenceCoefficient (I := I) g₀ g₁))).toSection x) =
            -((iteratedCovGrad (I := I) g₀ 0 3 i
              (metricLoweredConnectionDifferenceCoefficient (I := I) g₀ g₁)).toSection x) from by
          rw [SmoothCcTensor.toSection_neg]; rfl]
        rw [riemannianFiberNormSq_neg_value]
    _ = riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + i) x
          ((iteratedCovGrad (I := I) g₀ 0 3 i
            (domDomCongrSection (I := I) g₀ (finRotate 3)
              (metricLoweredConnectionDifferenceCoefficient (I := I) g₀ g₁))).toSection x) :=
        (riemannianFiberNormSq_iteratedCovGrad_domDomCongrSection (I := I) (M := M) g₀
          (finRotate 3) (metricLoweredConnectionDifferenceCoefficient (I := I) g₀ g₁) i x).symm
    _ = riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + i) x
          ((iteratedCovGrad (I := I) g₀ 1 2 i
            (cometricRaiseSlot0Field (I := I) (M := M) g₀ 1
              (domDomCongrSection (I := I) g₀ (finRotate 3)
                (metricLoweredConnectionDifferenceCoefficient (I := I) g₀ g₁)))).toSection x) :=
        (riemannianFiberNormSq_iteratedCovGrad_cometricRaiseSlot0Field_eq (I := I) (M := M) g₀ 1
          (domDomCongrSection (I := I) g₀ (finRotate 3)
            (metricLoweredConnectionDifferenceCoefficient (I := I) g₀ g₁)) i x).symm
    _ = riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + i) x
          ((iteratedCovGrad (I := I) g₀ 1 2 i (connectionDifferenceSection (I := I) g₁ g₀)).toSection x) := by
        rw [connectionDifferenceSection_eq_cometricRaiseSlot0Field]

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
