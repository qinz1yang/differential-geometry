import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.RicciDeTurck.Remainder.Coefficient.L2JetMoser
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.ConnectionDifference.LoweredCoefficient
import DifferentialGeometry.Geometry.Metric.DeTurck.ConnectionDifference.Identities
import DifferentialGeometry.Geometry.Curvature.Bochner.WeitzenbockIdentity
import DifferentialGeometry.Geometry.Connection.LeviCivita.Koszul
import DifferentialGeometry.Geometry.Connection.TensorNabla.SlotInsertCovariantNaturality
import DifferentialGeometry.Analysis.Parabolic.DeTurckRicci.DeTurckVectorFieldL2JetBoundEndomorphismCometricRaise
import Mathlib.Analysis.MeanInequalities

noncomputable section


open DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Analysis.Elliptic
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection
open MeasureTheory Set Filter Topology Bundle Manifold DifferentialGeometry.Tensor0SBundle ContinuousLinearMap
open scoped ENNReal NNReal BigOperators Manifold ContDiff

namespace DifferentialGeometry.Integral.Connection

open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.Analysis.Spectral.MetricRealization
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Spectral.DeTurck
open DifferentialGeometry.Analysis.Sobolev.TensorHilbert
open DifferentialGeometry.PDE.DeTurck.RicciLinearization (metricPerturbationPath)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

private def tangentModel {n : ℕ} (x : M) (v : Fin n → TangentSpace I x) : Fin n → E :=
  fun i => tangentSpaceModelContinuousLinearEquiv (I := I) x (v i)

def deTurckVectorFieldSection (g₁ g_bg : SmoothRiemannianMetric I M) :
    Π b : M, TangentSpace I b :=
  fun b => (PDE.DeTurck.deTurckVF (I := I) g₁ g_bg :
    Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) b

def metricLoweredConnectionDifference (g₀ g₁ g_bg : SmoothRiemannianMetric I M) : SmoothCcTensor g₀ 0 3 :=
  metricLoweredConnectionDifferenceCoefficient (I := I) g₀ g₁ - metricLoweredConnectionDifferenceCoefficient (I := I) g₀ g_bg

def deTurckVectorFieldCovector (g₀ g₁ g_bg : SmoothRiemannianMetric I M) : SmoothCcTensor g₀ 0 1 :=
  operatorFieldApply (I := I) (M := M) g₀ 3 1 (cometricCastG0 (I := I) g₀ g₁)
    (metricLoweredConnectionDifference (I := I) (M := M) g₀ g₁ g_bg)

def deTurckVectorFieldCovariantDerivativeLoweredBase (g₀ g₁ g_bg : SmoothRiemannianMetric I M) : SmoothCcTensor g₀ 0 2 :=
  domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 2) 1)
    (covGrad (I := I) (M := M) g₀ 0 1 (deTurckVectorFieldCovector (I := I) (M := M) g₀ g₁ g_bg))

def connectionDifferenceRaisedEndomorphism (g₀ g₁ : SmoothRiemannianMetric I M) : SmoothCcTensor g₀ 1 2 :=
  cometricRaiseSlot0Field (I := I) (M := M) g₀ 1
    (domDomCongrSection (I := I) g₀ (Equiv.swap (1 : Fin 3) 2)
      (metricLoweredConnectionDifferenceCoefficient (I := I) g₀ g₁))

def deTurckVectorFieldCovariantDerivativeLoweredConnectionDifference (g₀ g₁ g_bg : SmoothRiemannianMetric I M) : SmoothCcTensor g₀ 0 2 :=
  operatorFieldApply (I := I) (M := M) g₀ 1 2 (connectionDifferenceRaisedEndomorphism (I := I) (M := M) g₀ g₁)
    (deTurckVectorFieldCovector (I := I) (M := M) g₀ g₁ g_bg)

def deTurckVectorFieldCovariantDerivativeLowered (g₀ g₁ g_bg : SmoothRiemannianMetric I M) : SmoothCcTensor g₀ 0 2 :=
  deTurckVectorFieldCovariantDerivativeLoweredBase (I := I) (M := M) g₀ g₁ g_bg + deTurckVectorFieldCovariantDerivativeLoweredConnectionDifference (I := I) (M := M) g₀ g₁ g_bg

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] [SigmaCompactSpace M] in
private theorem operatorFieldApplication_sub_right (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (Φ : SmoothCcTensor g r s) (W₁ W₂ : SmoothCcTensor g 0 r) :
    operatorFieldApply (I := I) (M := M) g r s Φ (W₁ - W₂) =
      operatorFieldApply (I := I) (M := M) g r s Φ W₁ - operatorFieldApply (I := I) (M := M) g r s Φ W₂ := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rw [show ((operatorFieldApply (I := I) (M := M) g r s Φ W₁ - operatorFieldApply (I := I) (M := M) g r s Φ W₂).toSection x) =
      (operatorFieldApply (I := I) (M := M) g r s Φ W₁).toSection x -
        (operatorFieldApply (I := I) (M := M) g r s Φ W₂).toSection x from rfl]
  rw [operatorFieldApplication_toSection, operatorFieldApplication_toSection, operatorFieldApplication_toSection]
  rw [show ((W₁ - W₂).toSection x : TensorRSSpace 0 r I x) = W₁.toSection x - W₂.toSection x from by
    rw [SmoothCcTensor.toSection_sub]; rfl]
  rw [ContinuousLinearMap.comp_sub]

omit [NeZero (Module.finrank ℝ E)] in
omit [I.Boundaryless] in
omit [SigmaCompactSpace M] in
theorem deTurckVectorFieldCovector_base_sub (g₀ g₁ g_bg : SmoothRiemannianMetric I M) :
    deTurckVectorFieldCovector (I := I) (M := M) g₀ g₁ g₀ - deTurckVectorFieldCovector (I := I) (M := M) g₀ g₁ g_bg =
      operatorFieldApply (I := I) (M := M) g₀ 3 1 (cometricCastG0 (I := I) g₀ g₁)
        (metricLoweredConnectionDifference (I := I) (M := M) g₀ g_bg g₀) := by
  unfold deTurckVectorFieldCovector
  rw [← operatorFieldApplication_sub_right]
  congr 1
  unfold metricLoweredConnectionDifference
  abel

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [SigmaCompactSpace M] in
private lemma connectionDifferenceLoweredCc_unitModel' (g₀ g₁ : SmoothRiemannianMetric I M) (x : M) :
    unitModel (I := I) (M := M) g₀ 3 (metricLoweredConnectionDifferenceCoefficient (I := I) g₀ g₁) x =
      Tensor0SSpace.toModel (metricLoweredConnectionDifferenceCovector (I := I) g₀ g₁ x) := by
  rw [unitModel]
  rw [show (metricLoweredConnectionDifferenceCoefficient (I := I) g₀ g₁).toSection x (unitTensor (I := I) (M := M) x) =
      (MixedSection.eval₀ (F := E) (E := (TangentSpace I : M → Type _)) x).smulRight
          (metricLoweredConnectionDifferenceField (I := I) g₀ g₁ x)
          (ContinuousMultilinearMap.constOfIsEmpty ℝ (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ))
      from rfl]
  rw [ContinuousLinearMap.smulRight_apply, MixedSection.eval₀_apply,
    ContinuousMultilinearMap.constOfIsEmpty_apply, one_smul]
  rfl

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
omit [I.Boundaryless] in
lemma metricLoweredConnectionDifference_unitModel_apply (g₀ g₁ g_bg : SmoothRiemannianMetric I M) (x : M)
    (m : Fin 3 → TangentSpace I x) :
    unitModel (I := I) (M := M) g₀ 3
        (metricLoweredConnectionDifference (I := I) (M := M) g₀ g₁ g_bg) x
        (fun i => tangentSpaceModelContinuousLinearEquiv (I := I) x (m i)) =
      g₀.inner x (PDE.DeTurck.connectionDifference (I := I) g₁ g_bg x (m 0) (m 1)) (m 2) := by
  rw [metricLoweredConnectionDifference, DifferentialGeometry.Analysis.Parabolic.TensorSpectral.unitModel_sub, sub_apply,
    connectionDifferenceLoweredCc_unitModel_apply', connectionDifferenceLoweredCc_unitModel_apply']
  rw [show g₀.inner x (PDE.DeTurck.connectionDifference (I := I) g₁ g₀ x (m 0) (m 1)) (m 2) -
        g₀.inner x (PDE.DeTurck.connectionDifference (I := I) g_bg g₀ x (m 0) (m 1)) (m 2) =
      g₀.inner x (PDE.DeTurck.connectionDifference (I := I) g₁ g₀ x (m 0) (m 1) -
        PDE.DeTurck.connectionDifference (I := I) g_bg g₀ x (m 0) (m 1)) (m 2) from by
    rw [map_sub, sub_apply]]
  rw [connectionDifference_endpoint_cocycle (I := I) g₀ g₁ g_bg x (m 0) (m 1)]

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
omit [I.Boundaryless] in
private lemma wOmega_toSection_unit (g₀ g₁ g_bg : SmoothRiemannianMetric I M) (x : M) :
    (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 1 I x from
        (deTurckVectorFieldCovector (I := I) (M := M) g₀ g₁ g_bg).toSection x)
      (unitTensor (I := I) (M := M) x) =
      cometricDoubleTraceFib (I := I) g₁ 1 x
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 3 I x from
          (metricLoweredConnectionDifference (I := I) (M := M) g₀ g₁ g_bg).toSection x)
          (unitTensor (I := I) (M := M) x)) := by
  rw [deTurckVectorFieldCovector, operatorFieldApplication_toSection]
  rfl

omit [SigmaCompactSpace M] in
omit [I.Boundaryless] in
lemma deTurckVectorFieldCovector_unitModel_apply (g₀ g₁ g_bg : SmoothRiemannianMetric I M) (x : M)
    (z : TangentSpace I x) :
    unitModel (I := I) (M := M) g₀ 1 (deTurckVectorFieldCovector (I := I) (M := M) g₀ g₁ g_bg) x
        (fun _ : Fin 1 => tangentSpaceModelContinuousLinearEquiv (I := I) x z) =
      g₀.inner x (deTurckVectorFieldSection (I := I) (M := M) g₁ g_bg x) z := by
  classical
  rw [unitModel, wOmega_toSection_unit]
  set D : Tensor0SSpace 3 I x :=
    (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 3 I x from
      (metricLoweredConnectionDifference (I := I) (M := M) g₀ g₁ g_bg).toSection x)
      (unitTensor (I := I) (M := M) x) with hD
  have hdiag := cometricDoubleTraceFib_eq_orthoFrame_diag (I := I) g₁ 1 x
    (mem_smoothOrthoFrameNbhd_self (I := I) (M := M) x) D
  rw [hdiag]
  rw [show Tensor0SSpace.toModel
        (∑ i : Fin (Module.finrank ℝ E),
          tensor0SCurry (I := I) (M := M) (𝕜 := ℝ) 1 x
            (tensor0SCurry (I := I) (M := M) (𝕜 := ℝ) 2 x D
              (smoothOrthoFrame (I := I) g₁ x i x))
            (smoothOrthoFrame (I := I) g₁ x i x)) =
      ∑ i : Fin (Module.finrank ℝ E),
        Tensor0SSpace.toModel
          (tensor0SCurry (I := I) (M := M) (𝕜 := ℝ) 1 x
            (tensor0SCurry (I := I) (M := M) (𝕜 := ℝ) 2 x D
              (smoothOrthoFrame (I := I) g₁ x i x))
            (smoothOrthoFrame (I := I) g₁ x i x)) from
    map_sum (tensor0SSpaceContinuousLinearEquiv (𝕜 := ℝ) (I := I) 1 x) _ _]
  rw [sum_apply]
  have hterm : ∀ i : Fin (Module.finrank ℝ E),
      Tensor0SSpace.toModel
          (tensor0SCurry (I := I) (M := M) (𝕜 := ℝ) 1 x
            (tensor0SCurry (I := I) (M := M) (𝕜 := ℝ) 2 x D
              (smoothOrthoFrame (I := I) g₁ x i x))
            (smoothOrthoFrame (I := I) g₁ x i x))
          (fun _ : Fin 1 => tangentSpaceModelContinuousLinearEquiv (I := I) x z) =
        g₀.inner x (PDE.DeTurck.connectionDifference (I := I) g₁ g_bg x
          (smoothOrthoFrame (I := I) g₁ x i x)
          (smoothOrthoFrame (I := I) g₁ x i x)) z := by
    intro i
    rw [TensorMultilinear.tensor0S_curry_toModel_apply_tangent (I := I) (M := M)
      (T := tensor0SCurry (I := I) (M := M) (𝕜 := ℝ) 2 x D
        (smoothOrthoFrame (I := I) g₁ x i x))
      (v0 := smoothOrthoFrame (I := I) g₁ x i x)
      (vs := fun _ : Fin 1 => tangentSpaceModelContinuousLinearEquiv (I := I) x z)]
    rw [TensorMultilinear.tensor0S_curry_toModel_apply_tangent (I := I) (M := M)
      (T := D) (v0 := smoothOrthoFrame (I := I) g₁ x i x)
      (vs := Fin.cons
        (tangentSpaceModelContinuousLinearEquiv (I := I) x
          (smoothOrthoFrame (I := I) g₁ x i x))
        (fun _ : Fin 1 => tangentSpaceModelContinuousLinearEquiv (I := I) x z))]
    have hm : Tensor0SSpace.toModel D
        (tangentModel x
          ![smoothOrthoFrame (I := I) g₁ x i x,
            smoothOrthoFrame (I := I) g₁ x i x, z]) =
        unitModel (I := I) (M := M) g₀ 3 (metricLoweredConnectionDifference (I := I) (M := M) g₀ g₁ g_bg) x
          (tangentModel x
            ![smoothOrthoFrame (I := I) g₁ x i x,
              smoothOrthoFrame (I := I) g₁ x i x, z]) := by
      rw [unitModel, ← hD]
    rw [show Fin.cons
          (tangentSpaceModelContinuousLinearEquiv (I := I) x
            (smoothOrthoFrame (I := I) g₁ x i x))
          (Fin.cons
            (tangentSpaceModelContinuousLinearEquiv (I := I) x
              (smoothOrthoFrame (I := I) g₁ x i x))
            (fun _ : Fin 1 => tangentSpaceModelContinuousLinearEquiv (I := I) x z)) =
        tangentModel x
          ![smoothOrthoFrame (I := I) g₁ x i x,
            smoothOrthoFrame (I := I) g₁ x i x, z] from by
      funext k
      fin_cases k <;> rfl]
    unfold tangentModel at hm
    unfold tangentModel
    rw [hm, metricLoweredConnectionDifference_unitModel_apply]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons]
  rw [Finset.sum_congr rfl (fun i _ => hterm i)]
  rw [show (∑ i : Fin (Module.finrank ℝ E),
        g₀.inner x (PDE.DeTurck.connectionDifference (I := I) g₁ g_bg x
          (smoothOrthoFrame (I := I) g₁ x i x)
          (smoothOrthoFrame (I := I) g₁ x i x)) z) =
      g₀.inner x (∑ i : Fin (Module.finrank ℝ E),
        PDE.DeTurck.connectionDifference (I := I) g₁ g_bg x
          (smoothOrthoFrame (I := I) g₁ x i x)
          (smoothOrthoFrame (I := I) g₁ x i x)) z from by
    rw [map_sum, sum_apply]]
  rw [deTurckVectorFieldSection, ← PDE.DeTurck.deTurckVF_eq_orthoFrame_trace (I := I) g₁ g_bg x]

omit [SigmaCompactSpace M] in
omit [I.Boundaryless] in
private lemma wOmega_toSection_unit_eq_flat (g₀ g₁ g_bg : SmoothRiemannianMetric I M) (x : M) :
    (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 1 I x from
        (deTurckVectorFieldCovector (I := I) (M := M) g₀ g₁ g_bg).toSection x)
      (unitTensor (I := I) (M := M) x) =
      g0FlatCLM (I := I) g₀ x (deTurckVectorFieldSection (I := I) (M := M) g₁ g_bg x) := by
  apply Tensor0SSpace.toModel_injective
  apply ContinuousMultilinearMap.ext
  intro m
  have hm : m = fun _ : Fin 1 => m 0 := by
    funext k; fin_cases k; rfl
  rw [hm]
  have hL : Tensor0SSpace.toModel
      ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 1 I x from
        (deTurckVectorFieldCovector (I := I) (M := M) g₀ g₁ g_bg).toSection x)
        (unitTensor (I := I) (M := M) x)) (fun _ : Fin 1 => m 0) =
      g₀.inner x (deTurckVectorFieldSection (I := I) (M := M) g₁ g_bg x)
        ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm (m 0)) := by
    change unitModel (I := I) (M := M) g₀ 1
        (deTurckVectorFieldCovector (I := I) (M := M) g₀ g₁ g_bg) x
        (fun _ : Fin 1 => m 0) = _
    simpa only [ContinuousLinearEquiv.apply_symm_apply] using
      deTurckVectorFieldCovector_unitModel_apply (I := I) (M := M) g₀ g₁ g_bg x
        ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm (m 0))
  rw [hL]
  have hR : Tensor0SSpace.toModel (g0FlatCLM (I := I) g₀ x (deTurckVectorFieldSection (I := I) (M := M) g₁ g_bg x))
      (fun _ : Fin 1 => m 0) =
      cotangentToDual (I := I)
        (g0FlatCLM (I := I) g₀ x (deTurckVectorFieldSection (I := I) (M := M) g₁ g_bg x))
        ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm (m 0)) := by
    rw [cotangentToDual_apply]
    congr 1
  rw [hR, cotangentToDual_g0FlatCLM]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [SigmaCompactSpace M] in
private lemma tensor0SCovariantDerivative01_consEval_leibnizDefect
    (g₀ : SmoothRiemannianMetric I M) (V : Π b : M, Tensor0SSpace 1 I b) {x : M}
    (hV : TensorSectionMDiffAt (I := I) 1 V x)
    (Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (v : TangentSpace I x) :
    Tensor0SSpace.toModel
        (Tensor0SNabla.tensor0SCovariantDerivative I M 1 (LeviCivita (I := I) g₀) V x v)
        (Fin.cons (tangentSpaceModelContinuousLinearEquiv (I := I) x (Y x))
          (fun i => Fin.elim0 i)) =
      directionalDerivAt (I := I)
          (fun b : M =>
            Tensor0SSpace.toModel (V b)
              (Fin.cons (tangentSpaceModelContinuousLinearEquiv (I := I) b (Y b))
                (fun i => Fin.elim0 i))) x v
        - Tensor0SSpace.toModel (V x)
            (Fin.cons (tangentSpaceModelContinuousLinearEquiv (I := I) x
                ((LeviCivita (I := I) g₀).toFun (fun b => Y b) x v))
              (fun i => Fin.elim0 i)) := by
  classical
  have hpeel := tensor0SCovariantDerivative_succ_consEval_peel
    (I := I) (M := M) g₀ 0 V hV Y v (fun i => Fin.elim0 i)
  have hbase : Tensor0SSpace.toModel
      (Tensor0SNabla.tensor0SCovariantDerivative I M 0 (LeviCivita (I := I) g₀)
        (fun y : M => Tensor0SNabla.curriedSection I M V y (Y y)) x v)
      (fun i => Fin.elim0 i) =
      directionalDerivAt (I := I)
        (fun b : M =>
          Tensor0SSpace.toModel (V b)
            (Fin.cons (tangentSpaceModelContinuousLinearEquiv (I := I) b (Y b))
              (fun i => Fin.elim0 i))) x v := by
    rw [tensor0SCovariantDerivative_zero_toModel_apply (I := I) (M := M) g₀
      (fun b : M => Tensor0SNabla.curriedSection I M V b (Y b)) x v]
    have hfun : Tensor0SNabla.scalarFn I M
        (fun b : M => Tensor0SNabla.curriedSection I M V b (Y b)) =
        (fun b : M =>
          Tensor0SSpace.toModel (V b)
            (Fin.cons (tangentSpaceModelContinuousLinearEquiv (I := I) b (Y b))
              (fun i => Fin.elim0 i))) := by
      funext b
      rw [scalarFn_eq_toModel_elim0 (I := I) (M := M)]
      rw [Tensor0SNabla.curriedSection_apply (s := 0) (T := V)]
      rw [TensorMultilinear.tensor0S_curry_toModel_apply_tangent (I := I) (M := M)
        (T := V b) (v0 := Y b) (vs := (fun i => Fin.elim0 i))]
    rw [hfun]
  rw [hpeel, hbase]

omit [SigmaCompactSpace M] in
omit [I.Boundaryless] in
private lemma wOmega_toSection_unitZero (g₀ g₁ g_bg : SmoothRiemannianMetric I M) (b : M) :
    (show Tensor0SSpace 0 I b →L[ℝ] Tensor0SSpace 1 I b from
        (deTurckVectorFieldCovector (I := I) (M := M) g₀ g₁ g_bg).toSection b)
      (unitZeroSec (I := I) (M := M) b) =
      g0FlatCLM (I := I) g₀ b (deTurckVectorFieldSection (I := I) (M := M) g₁ g_bg b) :=
  wOmega_toSection_unit_eq_flat (I := I) (M := M) g₀ g₁ g_bg b

omit [SigmaCompactSpace M] in
omit [I.Boundaryless] in
private lemma unitEvalSection_wOmega_toModel (g₀ g₁ g_bg : SmoothRiemannianMetric I M)
    (b : M) (z : TangentSpace I b) :
    Tensor0SSpace.toModel (unitEvalSection (I := I) (M := M) g₀ 1
        (deTurckVectorFieldCovector (I := I) (M := M) g₀ g₁ g_bg) b)
      (Fin.cons (tangentSpaceModelContinuousLinearEquiv (I := I) b z)
        (fun i => Fin.elim0 i)) =
      g₀.inner b (deTurckVectorFieldSection (I := I) (M := M) g₁ g_bg b) z := by
  rw [unitEvalSection_apply, wOmega_toSection_unitZero]
  have h : Tensor0SSpace.toModel
      (g0FlatCLM (I := I) g₀ b (deTurckVectorFieldSection (I := I) (M := M) g₁ g_bg b))
      (Fin.cons (tangentSpaceModelContinuousLinearEquiv (I := I) b z)
        (fun i => Fin.elim0 i)) =
      cotangentToDual (I := I)
        (g0FlatCLM (I := I) g₀ b (deTurckVectorFieldSection (I := I) (M := M) g₁ g_bg b)) z := by
    rw [cotangentToDual_apply]
    change Tensor0SSpace.toModel
        (g0FlatCLM (I := I) g₀ b (deTurckVectorFieldSection (I := I) (M := M) g₁ g_bg b))
        (Fin.cons (tangentSpaceModelContinuousLinearEquiv (I := I) b z)
          (fun i => Fin.elim0 i)) =
      Tensor0SSpace.toModel
        (g0FlatCLM (I := I) g₀ b (deTurckVectorFieldSection (I := I) (M := M) g₁ g_bg b))
        (fun _ : Fin 1 => tangentSpaceModelContinuousLinearEquiv (I := I) b z)
    congr 1
    funext k
    refine Fin.cases rfl (fun j => j.elim0) k
  rw [h, cotangentToDual_g0FlatCLM]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [SigmaCompactSpace M] in
private lemma wVF_contMDiff (g₁ g_bg : SmoothRiemannianMetric I M) :
    ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun b : M => TotalSpace.mk' E (E := fun z : M => TangentSpace I z) b
        (deTurckVectorFieldSection (I := I) (M := M) g₁ g_bg b)) :=
  (PDE.DeTurck.deTurckVF (I := I) g₁ g_bg).contMDiff

omit [SigmaCompactSpace M] in
lemma deTurckVectorFieldCovariantDerivativeLoweredBase_unitModel_apply (g₀ g₁ g_bg : SmoothRiemannianMetric I M) (x : M)
    (u w : TangentSpace I x) :
    unitModel (I := I) (M := M) g₀ 2
        (deTurckVectorFieldCovariantDerivativeLoweredBase (I := I) (M := M) g₀ g₁ g_bg) x
        (fun i => tangentSpaceModelContinuousLinearEquiv (I := I) x ((![u, w] : Fin 2 → TangentSpace I x) i)) =
      g₀.inner x
        ((LeviCivita (I := I) g₀).toFun (deTurckVectorFieldSection (I := I) (M := M) g₁ g_bg) x w) u := by
  classical
  obtain ⟨Y, hYx⟩ := ContMDiffSection.exists_eq_at (I := I) (n := (⊤ : ℕ∞))
    (F := E) (V := (TangentSpace I : M → Type _)) x u
  rw [deTurckVectorFieldCovariantDerivativeLoweredBase, domDomCongrSection_unitModel, ContinuousMultilinearMap.domDomCongr_apply]
  rw [show (fun i => tangentSpaceModelContinuousLinearEquiv (I := I) x
        ((![u, w] : Fin 2 → TangentSpace I x) ((Equiv.swap (0 : Fin 2) 1) i))) =
      (fun i => tangentSpaceModelContinuousLinearEquiv (I := I) x
        ((![w, u] : Fin 2 → TangentSpace I x) i)) from by
    funext i
    fin_cases i <;> rfl]
  rw [unitModel]
  rw [covGrad_toSection_apply_eval (I := I) (M := M) g₀ 0 1
    (deTurckVectorFieldCovector (I := I) (M := M) g₀ g₁ g_bg) x (unitTensor (I := I) (M := M) x)
    (fun i => tangentSpaceModelContinuousLinearEquiv (I := I) x
      ((![w, u] : Fin 2 → TangentSpace I x) i))]
  change Tensor0SSpace.toModel
      ((tensorCovDerivAt (I := I) (M := M) g₀ 0 1
        (deTurckVectorFieldCovector (I := I) (M := M) g₀ g₁ g_bg) x
        (tangentSpaceModelContinuousLinearEquiv (I := I) x w))
        (unitTensor (I := I) (M := M) x))
      (fun i => tangentSpaceModelContinuousLinearEquiv (I := I) x
        ((![u] : Fin 1 → TangentSpace I x) i)) = _
  rw [tensorCovDerivAt_def (I := I) (M := M) g₀ 0 1
    (deTurckVectorFieldCovector (I := I) (M := M) g₀ g₁ g_bg) x
    (tangentSpaceModelContinuousLinearEquiv (I := I) x w),
    ContinuousLinearEquiv.symm_apply_apply]
  rw [show unitTensor (I := I) (M := M) x = unitZeroSec (I := I) (M := M) x from rfl]
  rw [covDeriv_unit_eval_eq_genVal (I := I) (M := M) g₀ 1
    (deTurckVectorFieldCovector (I := I) (M := M) g₀ g₁ g_bg).toSection x w]
  have hV : TensorSectionMDiffAt (I := I) 1
      (unitEvalSection (I := I) (M := M) g₀ 1 (deTurckVectorFieldCovector (I := I) (M := M) g₀ g₁ g_bg)) x :=
    ((contMDiff_unitEvalSection (I := I) (M := M) g₀ 1
      (deTurckVectorFieldCovector (I := I) (M := M) g₀ g₁ g_bg)) x).mdifferentiableAt (by simp)
  have hgen : (fun y : M =>
      (show Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace 1 I y from
        (deTurckVectorFieldCovector (I := I) (M := M) g₀ g₁ g_bg).toSection y)
        (unitZeroSec (I := I) (M := M) y)) =
      unitEvalSection (I := I) (M := M) g₀ 1 (deTurckVectorFieldCovector (I := I) (M := M) g₀ g₁ g_bg) := rfl
  rw [hgen]
  rw [show (fun i => tangentSpaceModelContinuousLinearEquiv (I := I) x
        ((![u] : Fin 1 → TangentSpace I x) i)) =
      Fin.cons (tangentSpaceModelContinuousLinearEquiv (I := I) x (Y x))
        (fun i => Fin.elim0 i) from by
    funext k
    refine Fin.cases ?_ (fun j => j.elim0) k
    rw [hYx]; rfl]
  rw [tensor0SCovariantDerivative01_consEval_leibnizDefect (I := I) (M := M) g₀
    (unitEvalSection (I := I) (M := M) g₀ 1 (deTurckVectorFieldCovector (I := I) (M := M) g₀ g₁ g_bg)) hV Y w]
  have hscal : (fun b : M =>
      Tensor0SSpace.toModel
        (unitEvalSection (I := I) (M := M) g₀ 1 (deTurckVectorFieldCovector (I := I) (M := M) g₀ g₁ g_bg) b)
        (Fin.cons (tangentSpaceModelContinuousLinearEquiv (I := I) b (Y b))
          (fun i => Fin.elim0 i))) =
      (fun b : M => g₀.inner b (deTurckVectorFieldSection (I := I) (M := M) g₁ g_bg b) (Y b)) := by
    funext b
    exact unitEvalSection_wOmega_toModel (I := I) (M := M) g₀ g₁ g_bg b (Y b)
  rw [hscal, directionalDerivAt_eq]
  have hlei := leibniz_inner (I := I) (M := M) g₀
    (V := deTurckVectorFieldSection (I := I) (M := M) g₁ g_bg) (W := fun b => Y b)
    (wVF_contMDiff (I := I) (M := M) g₁ g_bg) Y.contMDiff (x := x) w
  rw [hlei]
  rw [show Tensor0SSpace.toModel
      (unitEvalSection (I := I) (M := M) g₀ 1 (deTurckVectorFieldCovector (I := I) (M := M) g₀ g₁ g_bg) x)
      (Fin.cons (tangentSpaceModelContinuousLinearEquiv (I := I) x
          ((LeviCivita (I := I) g₀).toFun (fun b => Y b) x w))
        (fun i => Fin.elim0 i)) =
      g₀.inner x (deTurckVectorFieldSection (I := I) (M := M) g₁ g_bg x)
        ((LeviCivita (I := I) g₀).toFun (fun b => Y b) x w) from
    unitEvalSection_wOmega_toModel (I := I) (M := M) g₀ g₁ g_bg x _]
  rw [hYx]
  ring

omit [SigmaCompactSpace M] in
omit [I.Boundaryless] in
lemma deTurckVectorFieldCovariantDerivativeLoweredConnectionDifference_unitModel_apply (g₀ g₁ g_bg : SmoothRiemannianMetric I M) (x : M)
    (u w : TangentSpace I x) :
    unitModel (I := I) (M := M) g₀ 2
        (deTurckVectorFieldCovariantDerivativeLoweredConnectionDifference (I := I) (M := M) g₀ g₁ g_bg) x
        (fun i => tangentSpaceModelContinuousLinearEquiv (I := I) x
          ((![u, w] : Fin 2 → TangentSpace I x) i)) =
      g₀.inner x
        (PDE.DeTurck.connectionDifference (I := I) g₁ g₀ x (deTurckVectorFieldSection (I := I) (M := M) g₁ g_bg x) w) u := by
  classical
  rw [unitModel, deTurckVectorFieldCovariantDerivativeLoweredConnectionDifference, operatorFieldApplication_toSection]
  rw [ContinuousLinearMap.comp_apply]
  rw [wOmega_toSection_unit_eq_flat (I := I) (M := M) g₀ g₁ g_bg x]
  rw [connectionDifferenceRaisedEndomorphism, cometricRaiseSlot0Field_toSection]
  set D : Tensor0SSpace 3 I x :=
    (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 3 I x from
      (domDomCongrSection (I := I) g₀ (Equiv.swap (1 : Fin 3) 2)
        (metricLoweredConnectionDifferenceCoefficient (I := I) g₀ g₁)).toSection x)
      (unitTensor (I := I) (M := M) x) with hD
  rw [cometricRaiseSlot0Fib_clm_apply (I := I) g₀ 1 x D
    (g0FlatCLM (I := I) g₀ x (deTurckVectorFieldSection (I := I) (M := M) g₁ g_bg x))]
  rw [inverseMetricSharpFib_g0FlatCLM (I := I) g₀ x (deTurckVectorFieldSection (I := I) (M := M) g₁ g_bg x)]
  rw [interior_product_toModel_eval' (I := I) (M := M) (1 + 1) x
    (deTurckVectorFieldSection (I := I) (M := M) g₁ g_bg x) D ![u, w]]
  have hDm : Tensor0SSpace.toModel D
      (tangentModel x
        ![deTurckVectorFieldSection (I := I) (M := M) g₁ g_bg x, u, w]) =
      unitModel (I := I) (M := M) g₀ 3
        (domDomCongrSection (I := I) g₀ (Equiv.swap (1 : Fin 3) 2)
          (metricLoweredConnectionDifferenceCoefficient (I := I) g₀ g₁)) x
        (tangentModel x
          ![deTurckVectorFieldSection (I := I) (M := M) g₁ g_bg x, u, w]) := by
    rw [unitModel, ← hD]
  rw [show Fin.cons
        (tangentSpaceModelContinuousLinearEquiv (I := I) x
          (deTurckVectorFieldSection (I := I) (M := M) g₁ g_bg x))
        (fun i => tangentSpaceModelContinuousLinearEquiv (I := I) x
          ((![u, w] : Fin 2 → TangentSpace I x) i)) =
      tangentModel x
        ![deTurckVectorFieldSection (I := I) (M := M) g₁ g_bg x, u, w] from by
    funext k
    fin_cases k <;> rfl]
  rw [hDm, domDomCongrSection_unitModel, ContinuousMultilinearMap.domDomCongr_apply]
  rw [show (fun i => tangentModel x
        (![deTurckVectorFieldSection (I := I) (M := M) g₁ g_bg x, u, w] :
          Fin 3 → TangentSpace I x) ((Equiv.swap (1 : Fin 3) 2) i)) =
      tangentModel x
        ![deTurckVectorFieldSection (I := I) (M := M) g₁ g_bg x, w, u] from by
    funext i
    fin_cases i <;> rfl]
  unfold tangentModel
  rw [connectionDifferenceLoweredCc_unitModel_apply']
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [SigmaCompactSpace M] in
private lemma wEndo_eq_covDeriv_add_connectionDifference (g₀ g₁ g_bg : SmoothRiemannianMetric I M)
    (x : M) (w : TangentSpace I x) :
    deTurckVectorFieldCovariantDerivativeEndomorphism (I := I) g₁ g_bg x w =
      (LeviCivita (I := I) g₀).toFun (deTurckVectorFieldSection (I := I) (M := M) g₁ g_bg) x w +
        PDE.DeTurck.connectionDifference (I := I) g₁ g₀ x (deTurckVectorFieldSection (I := I) (M := M) g₁ g_bg x) w := by
  have hW : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (fun b : M => TotalSpace.mk' E (E := fun z : M => TangentSpace I z) b
        (deTurckVectorFieldSection (I := I) (M := M) g₁ g_bg b)) x :=
    ((wVF_contMDiff (I := I) (M := M) g₁ g_bg) x).mdifferentiableAt (by simp)
  have hcd := PDE.DeTurck.connectionDifference_apply (I := I) g₁ g₀
    (σ := deTurckVectorFieldSection (I := I) (M := M) g₁ g_bg) (x := x) hW w
  have hEndo : deTurckVectorFieldCovariantDerivativeEndomorphism (I := I) g₁ g_bg x w =
      (LeviCivita (I := I) g₁).toFun (deTurckVectorFieldSection (I := I) (M := M) g₁ g_bg) x w := rfl
  rw [hEndo, hcd]
  abel

omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] [SigmaCompactSpace M] in
omit [I.Boundaryless] in
lemma cotangentToDual_cometricRaiseSlot0_gen
    (g₀ : SmoothRiemannianMetric I M) (A : SmoothCcTensor g₀ 0 2) (x : M)
    (om : Tensor0SSpace 1 I x) (w : TangentSpace I x) :
    cotangentToDual (I := I)
        ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 1 I x from
          (cometricRaiseSlot0Field (I := I) (M := M) g₀ 0 A).toSection x) om) w =
      unitModel (I := I) (M := M) g₀ 2 A x
        (fun i => tangentSpaceModelContinuousLinearEquiv (I := I) x
          ((![inverseMetricSharpFib (I := I) g₀ x om, w] :
            Fin 2 → TangentSpace I x) i)) := by
  rw [cotangentToDual_apply]
  rw [cometricRaiseSlot0Field_toSection]
  rw [cometricRaiseSlot0Fib_clm_apply (I := I) g₀ 0 x _ om]
  rw [show (Tensor0SBundle.interiorProduct (𝕜 := ℝ) (I := I) (0 + 1) x
          (inverseMetricSharpFib (I := I) g₀ x om)
          ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (0 + 2) I x from
              A.toSection x)
            (unitTensor (I := I) (M := M) x)) (fun _ : Fin 1 => w) : ℝ) =
      Tensor0SSpace.toModel
        (Tensor0SBundle.interiorProduct (𝕜 := ℝ) (I := I) (0 + 1) x
          (inverseMetricSharpFib (I := I) g₀ x om)
          ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (0 + 2) I x from
              A.toSection x)
            (unitTensor (I := I) (M := M) x)))
        (fun _ : Fin 1 => tangentSpaceModelContinuousLinearEquiv (I := I) x w) from by
    rw [Tensor0SSpace.toModel_apply_model_vector]
    congr 1]
  rw [interior_product_toModel_eval' (I := I) (M := M) (0 + 1) x
    (inverseMetricSharpFib (I := I) g₀ x om)
    ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (0 + 2) I x from
        A.toSection x)
      (unitTensor (I := I) (M := M) x)) (fun _ : Fin 1 => w)]
  rw [unitModel]
  congr 1
  funext k
  refine Fin.cases ?_ (fun j => ?_) k
  · rfl
  · refine Fin.cases ?_ (fun j' => j'.elim0) j
    rfl

omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
private lemma cotangentToDual_cometricRaise_wAlpha
    (g₀ g₁ g_bg : SmoothRiemannianMetric I M) (x : M) (om : Tensor0SSpace 1 I x)
    (w : TangentSpace I x) :
    cotangentToDual (I := I)
        ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 1 I x from
          (cometricRaiseSlot0Field (I := I) (M := M) g₀ 0
            (deTurckVectorFieldCovariantDerivativeLowered (I := I) (M := M) g₀ g₁ g_bg)).toSection x) om) w =
      unitModel (I := I) (M := M) g₀ 2 (deTurckVectorFieldCovariantDerivativeLowered (I := I) (M := M) g₀ g₁ g_bg) x
        (fun i => tangentSpaceModelContinuousLinearEquiv (I := I) x
          ((![inverseMetricSharpFib (I := I) g₀ x om, w] :
            Fin 2 → TangentSpace I x) i)) :=
  cotangentToDual_cometricRaiseSlot0_gen (I := I) (M := M) g₀
    (deTurckVectorFieldCovariantDerivativeLowered (I := I) (M := M) g₀ g₁ g_bg) x om w

omit [SigmaCompactSpace M] in
theorem deTurckVectorFieldCovariantDerivativeEndomorphismInsert_eq_cometricRaise_deTurckVectorFieldCovariantDerivativeLowered
    (g₀ g₁ g_bg : SmoothRiemannianMetric I M) :
    deTurckVectorFieldCovariantDerivativeEndomorphismInsert (I := I) (M := M) g₀ g₁ g_bg =
      cometricRaiseSlot0Field (I := I) (M := M) g₀ 0
        (deTurckVectorFieldCovariantDerivativeLowered (I := I) (M := M) g₀ g₁ g_bg) := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  apply tensorRSSpace_ext 1 1 x
  intro om
  apply cotangentToDualLinear_injective (I := I) (x := x)
  apply LinearMap.ext
  intro w
  rw [cotangentToDualLinear_apply, cotangentToDualLinear_apply]
  rw [cotangentToDual_cometricRaise_wAlpha (I := I) (M := M) g₀ g₁ g_bg x om w]
  rw [show (show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 1 I x from
        (deTurckVectorFieldCovariantDerivativeEndomorphismInsert (I := I) (M := M) g₀ g₁ g_bg).toSection x) om =
      slotInsertEndoFib (I := I) (M := M) 1 0 x
        (deTurckVectorFieldCovariantDerivativeEndomorphism (I := I) g₁ g_bg x) om from rfl]
  rw [cotangentToDual_slotInsertEndoFib' (I := I) (M := M) x
    (deTurckVectorFieldCovariantDerivativeEndomorphism (I := I) g₁ g_bg x) om w]
  rw [wEndo_eq_covDeriv_add_connectionDifference (I := I) (M := M) g₀ g₁ g_bg x w]
  rw [deTurckVectorFieldCovariantDerivativeLowered, DifferentialGeometry.Analysis.Parabolic.TensorSpectral.unitModel_add, add_apply,
    deTurckVectorFieldCovariantDerivativeLoweredBase_unitModel_apply (I := I) (M := M) g₀ g₁ g_bg x
      (inverseMetricSharpFib (I := I) g₀ x om) w,
    deTurckVectorFieldCovariantDerivativeLoweredConnectionDifference_unitModel_apply (I := I) (M := M) g₀ g₁ g_bg x
      (inverseMetricSharpFib (I := I) g₀ x om) w]
  rw [show cotangentToDual (I := I) om
        ((LeviCivita (I := I) g₀).toFun (deTurckVectorFieldSection (I := I) (M := M) g₁ g_bg) x w +
          PDE.DeTurck.connectionDifference (I := I) g₁ g₀ x (deTurckVectorFieldSection (I := I) (M := M) g₁ g_bg x) w) =
      cotangentToDual (I := I) om
          ((LeviCivita (I := I) g₀).toFun (deTurckVectorFieldSection (I := I) (M := M) g₁ g_bg) x w) +
        cotangentToDual (I := I) om
          (PDE.DeTurck.connectionDifference (I := I) g₁ g₀ x (deTurckVectorFieldSection (I := I) (M := M) g₁ g_bg x) w) from by
    rw [← cotangentToDualLinear_apply, map_add]]
  rw [show cotangentToDual (I := I) om
        ((LeviCivita (I := I) g₀).toFun (deTurckVectorFieldSection (I := I) (M := M) g₁ g_bg) x w) =
      g₀.inner x (inverseMetricSharpFib (I := I) g₀ x om)
        ((LeviCivita (I := I) g₀).toFun (deTurckVectorFieldSection (I := I) (M := M) g₁ g_bg) x w) from by
    rw [← cotangentToDualLinear_apply]
    exact (inverseMetricSharpFib_inner (I := I) g₀ x om
      ((LeviCivita (I := I) g₀).toFun (deTurckVectorFieldSection (I := I) (M := M) g₁ g_bg) x w)).symm]
  rw [show cotangentToDual (I := I) om
        (PDE.DeTurck.connectionDifference (I := I) g₁ g₀ x (deTurckVectorFieldSection (I := I) (M := M) g₁ g_bg x) w) =
      g₀.inner x (inverseMetricSharpFib (I := I) g₀ x om)
        (PDE.DeTurck.connectionDifference (I := I) g₁ g₀ x (deTurckVectorFieldSection (I := I) (M := M) g₁ g_bg x) w) from by
    rw [← cotangentToDualLinear_apply]
    exact (inverseMetricSharpFib_inner (I := I) g₀ x om
      (PDE.DeTurck.connectionDifference (I := I) g₁ g₀ x (deTurckVectorFieldSection (I := I) (M := M) g₁ g_bg x) w)).symm]
  rw [g₀.symm x (inverseMetricSharpFib (I := I) g₀ x om)
    ((LeviCivita (I := I) g₀).toFun (deTurckVectorFieldSection (I := I) (M := M) g₁ g_bg) x w),
    g₀.symm x (inverseMetricSharpFib (I := I) g₀ x om)
      (PDE.DeTurck.connectionDifference (I := I) g₁ g₀ x (deTurckVectorFieldSection (I := I) (M := M) g₁ g_bg x) w)]
end DifferentialGeometry.Integral.Connection

end
