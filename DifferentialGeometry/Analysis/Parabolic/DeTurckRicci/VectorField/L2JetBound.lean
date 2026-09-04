import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.RicciDeTurck.Remainder.Coefficient.L2JetMoser
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.ConnectionDifference.LoweredCoefficient
import DifferentialGeometry.Geometry.Metric.DeTurck.ConnectionDifference.Identities
import DifferentialGeometry.Geometry.Curvature.Bochner.WeitzenbockIdentity
import Mathlib.Analysis.MeanInequalities
open DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection


noncomputable section


open MeasureTheory Set Filter Topology Bundle Manifold DifferentialGeometry.Tensor0SBundle
    ContinuousLinearMap
open scoped ENNReal NNReal BigOperators Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow

open DifferentialGeometry.Analysis.Spectral.MetricRealization
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Spectral.DeTurck
open DifferentialGeometry.Analysis.Sobolev.TensorHilbert
open DifferentialGeometry.PDE.DeTurck.RicciLinearization (metricPerturbationPath)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

private def tangentModel {n : ℕ} (x : M) (v : Fin n → TangentSpace I x) : Fin n → E :=
  fun i => tangentSpaceModelContinuousLinearEquiv (I := I) x (v i)

def deTurckVectorFieldCovariantDerivativeEndomorphismSection (g₁ g_bg : SmoothRiemannianMetric I M) :
    ContMDiffSection I (E →L[ℝ] E) ∞
      (fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x) where
  toFun := fun x : M => deTurckVectorFieldCovariantDerivativeEndomorphism (I := I) g₁ g_bg x
  contMDiff_toFun := deTurckVectorFieldCovariantDerivativeEndomorphism_homSection_contMDiff (I := I) g₁ g_bg

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
@[simp] lemma deTurckVectorFieldCovariantDerivativeEndomorphismSection_apply (g₁ g_bg : SmoothRiemannianMetric I M) (x : M) :
    deTurckVectorFieldCovariantDerivativeEndomorphismSection (I := I) (M := M) g₁ g_bg x =
      deTurckVectorFieldCovariantDerivativeEndomorphism (I := I) g₁ g_bg x := rfl

def deTurckVectorFieldCovariantDerivativeEndomorphismInsert (g₀ g₁ g_bg : SmoothRiemannianMetric I M) :
    SmoothCcTensor g₀ 1 1 :=
  endoSlotZeroCcTensor (I := I) (M := M) g₀ 0
    (deTurckVectorFieldCovariantDerivativeEndomorphismSection (I := I) (M := M) g₁ g_bg)

private def deTurckVFRaw (g₁ g_bg : SmoothRiemannianMetric I M) :
    Π b : M, TangentSpace I b :=
  fun b => (PDE.DeTurck.deTurckVF (I := I) g₁ g_bg :
    Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) b

def connectionDifferenceLoweredCcDiff (g₀ g₁ g_bg : SmoothRiemannianMetric I M) : SmoothCcTensor g₀ 0 3 :=
  metricLoweredConnectionDifferenceCoefficient (I := I) g₀ g₁ - metricLoweredConnectionDifferenceCoefficient (I := I) g₀ g_bg

def deTurckVFFlat (g₀ g₁ g_bg : SmoothRiemannianMetric I M) : SmoothCcTensor g₀ 0 1 :=
  operatorFieldApply (I := I) (M := M) g₀ 3 1 (cometricDoubleTraceCastG0 (I := I) g₀ g₁)
    (connectionDifferenceLoweredCcDiff (I := I) (M := M) g₀ g₁ g_bg)

def deTurckVectorFieldCovariantDerivativeEndomorphismBilinCovGradTerm (g₀ g₁ g_bg : SmoothRiemannianMetric I M) : SmoothCcTensor g₀ 0
    2 :=
  domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 2) 1)
    (covGrad (I := I) (M := M) g₀ 0 1 (deTurckVFFlat (I := I) (M := M) g₀ g₁ g_bg))

def connectionDifferenceRaisedSwapSlot0 (g₀ g₁ : SmoothRiemannianMetric I M) : SmoothCcTensor g₀ 1 2 :=
  cometricRaiseSlot0Field (I := I) (M := M) g₀ 1
    (domDomCongrSection (I := I) g₀ (Equiv.swap (1 : Fin 3) 2)
      (metricLoweredConnectionDifferenceCoefficient (I := I) g₀ g₁))

def deTurckVectorFieldCovariantDerivativeEndomorphismBilinConnectionDifferenceTerm (g₀ g₁ g_bg : SmoothRiemannianMetric I M) : SmoothCcTensor g₀ 0
    2 :=
  operatorFieldApply (I := I) (M := M) g₀ 1 2 (connectionDifferenceRaisedSwapSlot0 (I := I) (M := M) g₀ g₁)
    (deTurckVFFlat (I := I) (M := M) g₀ g₁ g_bg)

def deTurckVectorFieldCovariantDerivativeEndomorphismBilin (g₀ g₁ g_bg : SmoothRiemannianMetric I M) : SmoothCcTensor g₀ 0 2 :=
  deTurckVectorFieldCovariantDerivativeEndomorphismBilinCovGradTerm (I := I) (M := M) g₀ g₁ g_bg + deTurckVectorFieldCovariantDerivativeEndomorphismBilinConnectionDifferenceTerm
    (I := I) (M := M) g₀ g₁ g_bg

omit [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
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

omit [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
lemma connectionDifferenceLoweredCc_unitModel_apply' (g₀ g₁ : SmoothRiemannianMetric I M) (x : M)
    (m : Fin 3 → TangentSpace I x) :
    unitModel (I := I) (M := M) g₀ 3
        (metricLoweredConnectionDifferenceCoefficient (I := I) g₀ g₁) x
        (fun i => tangentSpaceModelContinuousLinearEquiv (I := I) x (m i)) =
      g₀.inner x (PDE.DeTurck.connectionDifference (I := I) g₁ g₀ x (m 0) (m 1)) (m 2) := by
  rw [connectionDifferenceLoweredCc_unitModel']
  rw [Tensor0SSpace.toModel_apply_model_vector]
  simp only [ContinuousLinearEquiv.symm_apply_apply,
    connectionDifferenceLoweredCovec_apply]

omit [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
private lemma metricLoweredConnectionDifference_unitModel_apply (g₀ g₁ g_bg : SmoothRiemannianMetric I M) (x : M)
    (m : Fin 3 → TangentSpace I x) :
    unitModel (I := I) (M := M) g₀ 3
        (connectionDifferenceLoweredCcDiff (I := I) (M := M) g₀ g₁ g_bg) x
        (tangentModel x m) =
      g₀.inner x (PDE.DeTurck.connectionDifference (I := I) g₁ g_bg x (m 0) (m 1)) (m 2) := by
  unfold tangentModel
  rw [connectionDifferenceLoweredCcDiff, DifferentialGeometry.Analysis.Parabolic.TensorSpectral.unitModel_sub, sub_apply,
    connectionDifferenceLoweredCc_unitModel_apply', connectionDifferenceLoweredCc_unitModel_apply']
  rw [show g₀.inner x (PDE.DeTurck.connectionDifference (I := I) g₁ g₀ x (m 0) (m 1)) (m 2) -
        g₀.inner x (PDE.DeTurck.connectionDifference (I := I) g_bg g₀ x (m 0) (m 1)) (m 2) =
      g₀.inner x (PDE.DeTurck.connectionDifference (I := I) g₁ g₀ x (m 0) (m 1) -
        PDE.DeTurck.connectionDifference (I := I) g_bg g₀ x (m 0) (m 1)) (m 2) from by
    rw [map_sub, sub_apply]]
  rw [connectionDifference_endpoint_cocycle (I := I) g₀ g₁ g_bg x (m 0) (m 1)]

omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
omit [I.Boundaryless] in
private lemma wOmega_toSection_unit (g₀ g₁ g_bg : SmoothRiemannianMetric I M) (x : M) :
    (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 1 I x from
        (deTurckVFFlat (I := I) (M := M) g₀ g₁ g_bg).toSection x)
      (unitTensor (I := I) (M := M) x) =
      cometricDoubleTraceFib (I := I) g₁ 1 x
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 3 I x from
          (connectionDifferenceLoweredCcDiff (I := I) (M := M) g₀ g₁ g_bg).toSection x)
          (unitTensor (I := I) (M := M) x)) := by
  rw [deTurckVFFlat, operatorFieldApplication_toSection]
  rfl

omit [SigmaCompactSpace M] in
omit [I.Boundaryless] in
private lemma deTurckVectorFieldCovector_unitModel_apply (g₀ g₁ g_bg : SmoothRiemannianMetric I M) (x : M)
    (z : TangentSpace I x) :
    unitModel (I := I) (M := M) g₀ 1 (deTurckVFFlat (I := I) (M := M) g₀ g₁ g_bg) x
        (tangentModel x (fun _ : Fin 1 => z)) =
      g₀.inner x (deTurckVFRaw (I := I) (M := M) g₁ g_bg x) z := by
  classical
  rw [unitModel, wOmega_toSection_unit]
  set D : Tensor0SSpace 3 I x :=
    (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 3 I x from
      (connectionDifferenceLoweredCcDiff (I := I) (M := M) g₀ g₁ g_bg).toSection x)
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
          (tangentModel x (fun _ : Fin 1 => z)) =
        g₀.inner x (PDE.DeTurck.connectionDifference (I := I) g₁ g_bg x
          (smoothOrthoFrame (I := I) g₁ x i x)
          (smoothOrthoFrame (I := I) g₁ x i x)) z := by
    intro i
    rw [TensorMultilinear.tensor0S_curry_toModel_apply_tangent (I := I) (M := M)
      (T := tensor0SCurry (I := I) (M := M) (𝕜 := ℝ) 2 x D
        (smoothOrthoFrame (I := I) g₁ x i x))
      (v0 := smoothOrthoFrame (I := I) g₁ x i x)
      (vs := tangentModel x (fun _ : Fin 1 => z))]
    rw [TensorMultilinear.tensor0S_curry_toModel_apply_tangent (I := I) (M := M)
      (T := D) (v0 := smoothOrthoFrame (I := I) g₁ x i x)
      (vs := Fin.cons
        (tangentSpaceModelContinuousLinearEquiv (I := I) x
          (smoothOrthoFrame (I := I) g₁ x i x))
        (tangentModel x (fun _ : Fin 1 => z)))]
    have hm : Tensor0SSpace.toModel D
        (tangentModel x
          ![smoothOrthoFrame (I := I) g₁ x i x,
            smoothOrthoFrame (I := I) g₁ x i x, z]) =
        unitModel (I := I) (M := M) g₀ 3 (connectionDifferenceLoweredCcDiff (I := I) (M := M) g₀ g₁ g_bg) x
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
            (tangentModel x (fun _ : Fin 1 => z))) =
        tangentModel x
          ![smoothOrthoFrame (I := I) g₁ x i x,
            smoothOrthoFrame (I := I) g₁ x i x, z] from by
      funext k
      fin_cases k <;> rfl]
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
  rw [deTurckVFRaw, ← PDE.DeTurck.deTurckVF_eq_orthoFrame_trace (I := I) g₁ g_bg x]

omit [SigmaCompactSpace M] in
omit [I.Boundaryless] in
private lemma wOmega_toSection_unit_eq_flat (g₀ g₁ g_bg : SmoothRiemannianMetric I M) (x : M) :
    (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 1 I x from
        (deTurckVFFlat (I := I) (M := M) g₀ g₁ g_bg).toSection x)
      (unitTensor (I := I) (M := M) x) =
      g0FlatCLM (I := I) g₀ x (deTurckVFRaw (I := I) (M := M) g₁ g_bg x) := by
  apply Tensor0SSpace.toModel_injective
  apply ContinuousMultilinearMap.ext
  intro m
  have hm : m = fun _ : Fin 1 => m 0 := by
    funext k; fin_cases k; rfl
  rw [hm]
  have hL : Tensor0SSpace.toModel
      ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 1 I x from
        (deTurckVFFlat (I := I) (M := M) g₀ g₁ g_bg).toSection x)
        (unitTensor (I := I) (M := M) x)) (fun _ : Fin 1 => m 0) =
      g₀.inner x (deTurckVFRaw (I := I) (M := M) g₁ g_bg x)
        ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm (m 0)) := by
    change unitModel (I := I) (M := M) g₀ 1
        (deTurckVFFlat (I := I) (M := M) g₀ g₁ g_bg) x (fun _ : Fin 1 => m 0) = _
    have h := deTurckVectorFieldCovector_unitModel_apply (I := I) (M := M) g₀ g₁ g_bg x
      ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm (m 0))
    rw [show tangentModel x
          (fun _ : Fin 1 => (tangentSpaceModelContinuousLinearEquiv (I := I) x).symm (m 0)) =
        (fun _ : Fin 1 => m 0) from by
      funext k
      fin_cases k
      exact ContinuousLinearEquiv.apply_symm_apply _ _] at h
    exact h
  rw [hL]
  have hR : Tensor0SSpace.toModel
    (g0FlatCLM (I := I) g₀ x (deTurckVFRaw (I := I) (M := M) g₁ g_bg x))
      (fun _ : Fin 1 => m 0) =
      cotangentToDual (I := I)
        (g0FlatCLM (I := I) g₀ x (deTurckVFRaw (I := I) (M := M) g₁ g_bg x))
        ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm (m 0)) := by
    rw [cotangentToDual_apply]
    congr 1
  rw [hR, cotangentToDual_g0FlatCLM]

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
private lemma tensor0SCovariantDerivative01_consEval_leibnizDefect
    (g₀ : SmoothRiemannianMetric I M) (V : Π b : M, Tensor0SSpace 1 I b) {x : M}
    (hV : TensorSectionMDiffAt (I := I) 1 V x)
    (Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (v : TangentSpace I x) :
    Tensor0SSpace.toModel
        (Tensor0SNabla.tensor0SCovariantDerivative I M 1 (LeviCivita (I := I) g₀) V x v)
        (Fin.cons (tangentSpaceModelContinuousLinearEquiv (I := I) x (Y x))
          (fun i => Fin.elim0 i)) =
      directionalDeriv (I := I)
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
      directionalDeriv (I := I)
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
        (deTurckVFFlat (I := I) (M := M) g₀ g₁ g_bg).toSection b)
      (unitZeroSec (I := I) (M := M) b) =
      g0FlatCLM (I := I) g₀ b (deTurckVFRaw (I := I) (M := M) g₁ g_bg b) :=
  wOmega_toSection_unit_eq_flat (I := I) (M := M) g₀ g₁ g_bg b

omit [SigmaCompactSpace M] in
omit [I.Boundaryless] in
private lemma unitEvalSection_wOmega_toModel (g₀ g₁ g_bg : SmoothRiemannianMetric I M)
    (b : M) (z : TangentSpace I b) :
    Tensor0SSpace.toModel (unitEvalSection (I := I) (M := M) g₀ 1
        (deTurckVFFlat (I := I) (M := M) g₀ g₁ g_bg) b)
      (Fin.cons (tangentSpaceModelContinuousLinearEquiv (I := I) b z)
        (fun i => Fin.elim0 i)) =
      g₀.inner b (deTurckVFRaw (I := I) (M := M) g₁ g_bg b) z := by
  rw [unitEvalSection_apply, wOmega_toSection_unitZero]
  have h : Tensor0SSpace.toModel
      (g0FlatCLM (I := I) g₀ b (deTurckVFRaw (I := I) (M := M) g₁ g_bg b))
      (Fin.cons (tangentSpaceModelContinuousLinearEquiv (I := I) b z)
        (fun i => Fin.elim0 i)) =
      cotangentToDual (I := I)
        (g0FlatCLM (I := I) g₀ b (deTurckVFRaw (I := I) (M := M) g₁ g_bg b)) z := by
    rw [cotangentToDual_apply]
    change Tensor0SSpace.toModel
        (g0FlatCLM (I := I) g₀ b (deTurckVFRaw (I := I) (M := M) g₁ g_bg b))
        (Fin.cons (tangentSpaceModelContinuousLinearEquiv (I := I) b z)
          (fun i => Fin.elim0 i)) =
      Tensor0SSpace.toModel
        (g0FlatCLM (I := I) g₀ b (deTurckVFRaw (I := I) (M := M) g₁ g_bg b))
        (fun _ : Fin 1 => tangentSpaceModelContinuousLinearEquiv (I := I) b z)
    congr 1
    funext k
    refine Fin.cases rfl (fun j => j.elim0) k
  rw [h, cotangentToDual_g0FlatCLM]

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
private lemma wVF_contMDiff (g₁ g_bg : SmoothRiemannianMetric I M) :
    ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun b : M => TotalSpace.mk' E (E := fun z : M => TangentSpace I z) b
        (deTurckVFRaw (I := I) (M := M) g₁ g_bg b)) :=
  (PDE.DeTurck.deTurckVF (I := I) g₁ g_bg).contMDiff

omit [SigmaCompactSpace M] in
private lemma wAlphaA_unitModel_apply (g₀ g₁ g_bg : SmoothRiemannianMetric I M) (x : M)
    (u w : TangentSpace I x) :
    unitModel (I := I) (M := M) g₀ 2 (deTurckVectorFieldCovariantDerivativeEndomorphismBilinCovGradTerm (I := I) (M := M) g₀ g₁ g_bg)
      x (tangentModel x ![u, w]) =
      g₀.inner x
        ((LeviCivita (I := I) g₀).toFun (deTurckVFRaw (I := I) (M := M) g₁ g_bg) x w) u := by
  classical
  obtain ⟨Y, hYx⟩ := ContMDiffSection.exists_eq_at (I := I) (n := (⊤ : ℕ∞))
    (F := E) (V := (TangentSpace I : M → Type _)) x u
  rw [deTurckVectorFieldCovariantDerivativeEndomorphismBilinCovGradTerm, domDomCongrSection_unitModel,
    ContinuousMultilinearMap.domDomCongr_apply]
  rw [show (fun i => tangentModel x (![u, w] : Fin 2 → TangentSpace I x)
        ((Equiv.swap (0 : Fin 2) 1) i)) = tangentModel x ![w, u] from by
    funext i
    fin_cases i <;> rfl]
  rw [unitModel]
  rw [covGrad_toSection_apply_eval (I := I) (M := M) g₀ 0 1
    (deTurckVFFlat (I := I) (M := M) g₀ g₁ g_bg) x (unitTensor (I := I) (M := M) x)
    (tangentModel x ![w, u])]
  rw [show tangentModel x (![w, u] : Fin 2 → TangentSpace I x) 0 =
      tangentSpaceModelContinuousLinearEquiv (I := I) x w from rfl]
  rw [show Matrix.vecTail (tangentModel x (![w, u] : Fin 2 → TangentSpace I x)) =
      tangentModel x ![u] from by
    funext k
    refine Fin.cases rfl (fun j => j.elim0) k]
  rw [tensorCovDerivAt_def (I := I) (M := M) g₀ 0 1
    (deTurckVFFlat (I := I) (M := M) g₀ g₁ g_bg) x
    (tangentSpaceModelContinuousLinearEquiv (I := I) x w),
    ContinuousLinearEquiv.symm_apply_apply]
  rw [show unitTensor (I := I) (M := M) x = unitZeroSec (I := I) (M := M) x from rfl]
  rw [covDeriv_unit_eval_eq (I := I) (M := M) g₀ 1
    (deTurckVFFlat (I := I) (M := M) g₀ g₁ g_bg).toSection x w]
  have hV : TensorSectionMDiffAt (I := I) 1
      (unitEvalSection (I := I) (M := M) g₀ 1 (deTurckVFFlat (I := I) (M := M) g₀ g₁ g_bg)) x :=
    ((contMDiff_unitEvalSection (I := I) (M := M) g₀ 1
      (deTurckVFFlat (I := I) (M := M) g₀ g₁ g_bg)) x).mdifferentiableAt (by simp)
  have hgen : (fun y : M =>
      (show Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace 1 I y from
        (deTurckVFFlat (I := I) (M := M) g₀ g₁ g_bg).toSection y)
        (unitZeroSec (I := I) (M := M) y)) =
      unitEvalSection (I := I) (M := M) g₀ 1 (deTurckVFFlat (I := I) (M := M) g₀ g₁ g_bg) := rfl
  rw [hgen]
  rw [show tangentModel x (![u] : Fin 1 → TangentSpace I x) =
      Fin.cons (tangentSpaceModelContinuousLinearEquiv (I := I) x (Y x))
        (fun i => Fin.elim0 i) from by
    funext k
    refine Fin.cases ?_ (fun j => j.elim0) k
    rw [hYx]; rfl]
  rw [tensor0SCovariantDerivative01_consEval_leibnizDefect (I := I) (M := M) g₀
    (unitEvalSection (I := I) (M := M) g₀ 1 (deTurckVFFlat (I := I) (M := M) g₀ g₁ g_bg)) hV Y w]
  have hscal : (fun b : M =>
      Tensor0SSpace.toModel
        (unitEvalSection (I := I) (M := M) g₀ 1 (deTurckVFFlat (I := I) (M := M) g₀ g₁ g_bg) b)
        (Fin.cons (tangentSpaceModelContinuousLinearEquiv (I := I) b (Y b))
          (fun i => Fin.elim0 i))) =
      (fun b : M => g₀.inner b (deTurckVFRaw (I := I) (M := M) g₁ g_bg b) (Y b)) := by
    funext b
    exact unitEvalSection_wOmega_toModel (I := I) (M := M) g₀ g₁ g_bg b (Y b)
  rw [hscal, directionalDeriv_eq]
  have hlei := leibniz_inner (I := I) (M := M) g₀
    (V := deTurckVFRaw (I := I) (M := M) g₁ g_bg) (W := fun b => Y b)
    (wVF_contMDiff (I := I) (M := M) g₁ g_bg) Y.contMDiff (x := x) w
  rw [hlei]
  rw [show Tensor0SSpace.toModel
      (unitEvalSection (I := I) (M := M) g₀ 1 (deTurckVFFlat (I := I) (M := M) g₀ g₁ g_bg) x)
      (Fin.cons (tangentSpaceModelContinuousLinearEquiv (I := I) x
          ((LeviCivita (I := I) g₀).toFun (fun b => Y b) x w))
        (fun i => Fin.elim0 i)) =
      g₀.inner x (deTurckVFRaw (I := I) (M := M) g₁ g_bg x)
        ((LeviCivita (I := I) g₀).toFun (fun b => Y b) x w) from
    unitEvalSection_wOmega_toModel (I := I) (M := M) g₀ g₁ g_bg x _]
  rw [hYx]
  ring

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
    [T2Space M] [SigmaCompactSpace M] in
lemma interior_product_toModel_eval' (s : ℕ) (x : M) (v : TangentSpace I x)
    (D : Tensor0SSpace (s + 1) I x) (w : Fin s → TangentSpace I x) :
    Tensor0SSpace.toModel
        (Tensor0SBundle.interiorProduct (𝕜 := ℝ) (I := I) s x v D)
        (fun i => tangentSpaceModelContinuousLinearEquiv (I := I) x (w i)) =
      Tensor0SSpace.toModel D
        (Fin.cons (tangentSpaceModelContinuousLinearEquiv (I := I) x v)
          (fun i => tangentSpaceModelContinuousLinearEquiv (I := I) x (w i))) := by
  have h1 : Tensor0SSpace.toModel
      (Tensor0SBundle.interiorProduct (𝕜 := ℝ) (I := I) s x v D) =
      Tensor0SBundle.modelInteriorProduct (𝕜 := ℝ) (E := E) s
        (tangentSpaceModelContinuousLinearEquiv (I := I) x v)
        (Tensor0SSpace.toModel D) := rfl
  rw [h1]
  rfl

omit [SigmaCompactSpace M] in
omit [I.Boundaryless] in
private lemma deTurckVectorFieldCovariantDerivativeLoweredConnectionDifference_unitModel_apply (g₀ g₁ g_bg : SmoothRiemannianMetric I M) (x : M)
    (u w : TangentSpace I x) :
    unitModel (I := I) (M := M) g₀ 2 (deTurckVectorFieldCovariantDerivativeEndomorphismBilinConnectionDifferenceTerm (I := I) (M := M) g₀ g₁ g_bg)
      x (tangentModel x ![u, w]) =
      g₀.inner x
        (PDE.DeTurck.connectionDifference (I := I) g₁ g₀ x (deTurckVFRaw (I := I) (M := M) g₁ g_bg x) w) u := by
  classical
  rw [unitModel, deTurckVectorFieldCovariantDerivativeEndomorphismBilinConnectionDifferenceTerm, operatorFieldApplication_toSection]
  rw [ContinuousLinearMap.comp_apply]
  rw [wOmega_toSection_unit_eq_flat (I := I) (M := M) g₀ g₁ g_bg x]
  rw [connectionDifferenceRaisedSwapSlot0, cometricRaiseSlot0Field_toSection]
  set D : Tensor0SSpace 3 I x :=
    (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 3 I x from
      (domDomCongrSection (I := I) g₀ (Equiv.swap (1 : Fin 3) 2)
        (metricLoweredConnectionDifferenceCoefficient (I := I) g₀ g₁)).toSection x)
      (unitTensor (I := I) (M := M) x) with hD
  rw [cometricRaiseSlot0Fib_clm_apply (I := I) g₀ 1 x D
    (g0FlatCLM (I := I) g₀ x (deTurckVFRaw (I := I) (M := M) g₁ g_bg x))]
  rw [inverseMetricSharpFib_g0FlatCLM (I := I) g₀ x (deTurckVFRaw (I := I) (M := M) g₁ g_bg x)]
  unfold tangentModel
  rw [interior_product_toModel_eval' (I := I) (M := M) (1 + 1) x
    (deTurckVFRaw (I := I) (M := M) g₁ g_bg x) D ![u, w]]
  have hDm : Tensor0SSpace.toModel D
      (tangentModel x ![deTurckVFRaw (I := I) (M := M) g₁ g_bg x, u, w]) =
      unitModel (I := I) (M := M) g₀ 3
        (domDomCongrSection (I := I) g₀ (Equiv.swap (1 : Fin 3) 2)
          (metricLoweredConnectionDifferenceCoefficient (I := I) g₀ g₁)) x
        (tangentModel x ![deTurckVFRaw (I := I) (M := M) g₁ g_bg x, u, w]) := by
    rw [unitModel, ← hD]
  rw [show Fin.cons
      (tangentSpaceModelContinuousLinearEquiv (I := I) x
          (deTurckVFRaw (I := I) (M := M) g₁ g_bg x))
        (fun i => tangentSpaceModelContinuousLinearEquiv (I := I) x
          ((![u, w] : Fin 2 → TangentSpace I x) i)) =
      tangentModel x ![deTurckVFRaw (I := I) (M := M) g₁ g_bg x, u, w] from by
    funext k
    fin_cases k <;> rfl]
  rw [hDm, domDomCongrSection_unitModel, ContinuousMultilinearMap.domDomCongr_apply]
  rw [show (fun i => tangentModel x
        (![deTurckVFRaw (I := I) (M := M) g₁ g_bg x, u, w] : Fin 3 → TangentSpace I x)
          ((Equiv.swap (1 : Fin 3) 2) i)) =
      tangentModel x ![deTurckVFRaw (I := I) (M := M) g₁ g_bg x, w, u] from by
    funext i
    fin_cases i <;> rfl]
  unfold tangentModel
  rw [connectionDifferenceLoweredCc_unitModel_apply']
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons]

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
private lemma wEndo_eq_covDeriv_add_connectionDifference (g₀ g₁ g_bg : SmoothRiemannianMetric I M)
    (x : M) (w : TangentSpace I x) :
    deTurckVectorFieldCovariantDerivativeEndomorphism (I := I) g₁ g_bg x w =
      (LeviCivita (I := I) g₀).toFun (deTurckVFRaw (I := I) (M := M) g₁ g_bg) x w +
        PDE.DeTurck.connectionDifference (I := I) g₁ g₀ x (deTurckVFRaw (I := I) (M := M) g₁ g_bg x) w := by
  have hW : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (fun b : M => TotalSpace.mk' E (E := fun z : M => TangentSpace I z) b
        (deTurckVFRaw (I := I) (M := M) g₁ g_bg b)) x :=
    ((wVF_contMDiff (I := I) (M := M) g₁ g_bg) x).mdifferentiableAt (by simp)
  have hcd := PDE.DeTurck.connectionDifference_apply (I := I) g₁ g₀
    (σ := deTurckVFRaw (I := I) (M := M) g₁ g_bg) (x := x) hW w
  have hEndo : deTurckVectorFieldCovariantDerivativeEndomorphism (I := I) g₁ g_bg x w =
      (LeviCivita (I := I) g₁).toFun (deTurckVFRaw (I := I) (M := M) g₁ g_bg) x w := rfl
  rw [hEndo, hcd]
  abel

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
    [T2Space M] [SigmaCompactSpace M] in
lemma cotangentToDual_slotInsertEndoFib' (x : M)
    (Λ : TangentSpace I x →L[ℝ] TangentSpace I x) (om : Tensor0SSpace 1 I x)
    (w : TangentSpace I x) :
    cotangentToDual (I := I)
        (slotInsertEndoFib (I := I) (M := M) 1 0 x Λ om) w =
      cotangentToDual (I := I) om (Λ w) := by
  rw [cotangentToDual_apply, cotangentToDual_apply]
  rw [show (slotInsertEndoFib (I := I) (M := M) 1 0 x Λ om) (fun _ : Fin 1 => w) =
      Tensor0SSpace.toModel (slotInsertEndoFib (I := I) (M := M) 1 0 x Λ om)
        (fun _ : Fin 1 => tangentSpaceModelContinuousLinearEquiv (I := I) x w) from by
    rw [Tensor0SSpace.toModel_apply_model_vector]
    congr 1]
  rw [slotInsertEndoFib_apply_eval]
  rw [show Tensor0SSpace.toModel om
        (Function.update
          (fun _ : Fin 1 => tangentSpaceModelContinuousLinearEquiv (I := I) x w) 0
          (tangentLinearMapToModel Λ
            ((fun _ : Fin 1 => tangentSpaceModelContinuousLinearEquiv (I := I) x w) 0))) =
      Tensor0SSpace.toModel om
        (fun _ : Fin 1 => tangentSpaceModelContinuousLinearEquiv (I := I) x (Λ w)) from by
    congr 1
    funext k
    fin_cases k
    change tangentLinearMapToModel Λ
        (tangentSpaceModelContinuousLinearEquiv (I := I) x w) =
      tangentSpaceModelContinuousLinearEquiv (I := I) x (Λ w)
    rw [tangentLinearMapToModel_apply, ContinuousLinearEquiv.symm_apply_apply]]
  rw [Tensor0SSpace.toModel_apply_model_vector]
  congr 1

omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
private lemma cotangentToDual_cometricRaise_wAlpha
    (g₀ g₁ g_bg : SmoothRiemannianMetric I M) (x : M) (om : Tensor0SSpace 1 I x)
    (w : TangentSpace I x) :
    cotangentToDual (I := I)
        ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 1 I x from
          (cometricRaiseSlot0Field (I := I) (M := M) g₀ 0
            (deTurckVectorFieldCovariantDerivativeEndomorphismBilin (I := I) (M := M) g₀ g₁ g_bg)).toSection x) om) w =
      unitModel (I := I) (M := M) g₀ 2 (deTurckVectorFieldCovariantDerivativeEndomorphismBilin (I := I) (M := M) g₀ g₁ g_bg) x
        (tangentModel x ![inverseMetricSharpFib (I := I) g₀ x om, w]) := by
  rw [cotangentToDual_apply]
  rw [cometricRaiseSlot0Field_toSection]
  rw [cometricRaiseSlot0Fib_clm_apply (I := I) g₀ 0 x _ om]
  rw [show (Tensor0SBundle.interiorProduct (𝕜 := ℝ) (I := I) (0 + 1) x
          (inverseMetricSharpFib (I := I) g₀ x om)
          ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (0 + 2) I x from
            (deTurckVectorFieldCovariantDerivativeEndomorphismBilin (I := I) (M := M) g₀ g₁ g_bg).toSection x)
            (unitTensor (I := I) (M := M) x))
          (fun _ : Fin 1 => w) : ℝ) =
      Tensor0SSpace.toModel
        (Tensor0SBundle.interiorProduct (𝕜 := ℝ) (I := I) (0 + 1) x
          (inverseMetricSharpFib (I := I) g₀ x om)
          ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (0 + 2) I x from
              (deTurckVectorFieldCovariantDerivativeEndomorphismBilin (I := I) (M := M) g₀ g₁ g_bg).toSection x)
            (unitTensor (I := I) (M := M) x)))
        (tangentModel x (fun _ : Fin 1 => w)) from by
    rw [Tensor0SSpace.toModel_apply_model_vector]
    congr 1]
  unfold tangentModel
  rw [interior_product_toModel_eval' (I := I) (M := M) (0 + 1) x
    (inverseMetricSharpFib (I := I) g₀ x om)
    ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (0 + 2) I x from
        (deTurckVectorFieldCovariantDerivativeEndomorphismBilin (I := I) (M := M) g₀ g₁ g_bg).toSection x)
      (unitTensor (I := I) (M := M) x)) (fun _ : Fin 1 => w)]
  rw [unitModel]
  congr 1
  funext k
  refine Fin.cases ?_ (fun j => ?_) k
  · rfl
  · refine Fin.cases ?_ (fun j' => j'.elim0) j
    rfl

omit [SigmaCompactSpace M] in
theorem deTurckVectorFieldCovariantDerivativeEndomorphismInsert_eq_cometricRaise
    (g₀ g₁ g_bg : SmoothRiemannianMetric I M) :
    deTurckVectorFieldCovariantDerivativeEndomorphismInsert (I := I) (M := M) g₀ g₁ g_bg =
      cometricRaiseSlot0Field (I := I) (M := M) g₀ 0
        (deTurckVectorFieldCovariantDerivativeEndomorphismBilin (I := I) (M := M) g₀ g₁ g_bg) := by
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
  rw [deTurckVectorFieldCovariantDerivativeEndomorphismBilin, DifferentialGeometry.Analysis.Parabolic.TensorSpectral.unitModel_add, add_apply,
    wAlphaA_unitModel_apply (I := I) (M := M) g₀ g₁ g_bg x
      (inverseMetricSharpFib (I := I) g₀ x om) w,
    deTurckVectorFieldCovariantDerivativeLoweredConnectionDifference_unitModel_apply (I := I) (M := M) g₀ g₁ g_bg x
      (inverseMetricSharpFib (I := I) g₀ x om) w]
  rw [show cotangentToDual (I := I) om
        ((LeviCivita (I := I) g₀).toFun (deTurckVFRaw (I := I) (M := M) g₁ g_bg) x w +
          PDE.DeTurck.connectionDifference (I := I) g₁ g₀ x (deTurckVFRaw (I := I) (M := M) g₁ g_bg x) w) =
      cotangentToDual (I := I) om
          ((LeviCivita (I := I) g₀).toFun (deTurckVFRaw (I := I) (M := M) g₁ g_bg) x w) +
        cotangentToDual (I := I) om
          (PDE.DeTurck.connectionDifference (I := I) g₁ g₀ x (deTurckVFRaw (I := I) (M := M) g₁ g_bg x) w)
            from by
    rw [← cotangentToDualLinear_apply, map_add]]
  rw [show cotangentToDual (I := I) om
        ((LeviCivita (I := I) g₀).toFun (deTurckVFRaw (I := I) (M := M) g₁ g_bg) x w) =
      g₀.inner x (inverseMetricSharpFib (I := I) g₀ x om)
        ((LeviCivita (I := I) g₀).toFun (deTurckVFRaw (I := I) (M := M) g₁ g_bg) x w) from by
    rw [← cotangentToDualLinear_apply]
    exact (inverseMetricSharpFib_inner (I := I) g₀ x om
      ((LeviCivita (I := I) g₀).toFun (deTurckVFRaw (I := I) (M := M) g₁ g_bg) x w)).symm]
  rw [show cotangentToDual (I := I) om
        (PDE.DeTurck.connectionDifference (I := I) g₁ g₀ x (deTurckVFRaw (I := I) (M := M) g₁ g_bg x) w) =
      g₀.inner x (inverseMetricSharpFib (I := I) g₀ x om)
        (PDE.DeTurck.connectionDifference (I := I) g₁ g₀ x (deTurckVFRaw (I := I) (M := M) g₁ g_bg x) w) from by
    rw [← cotangentToDualLinear_apply]
    exact (inverseMetricSharpFib_inner (I := I) g₀ x om
      (PDE.DeTurck.connectionDifference (I := I) g₁ g₀ x (deTurckVFRaw (I := I) (M := M) g₁ g_bg x) w)).symm]
  rw [g₀.symm x (inverseMetricSharpFib (I := I) g₀ x om)
    ((LeviCivita (I := I) g₀).toFun (deTurckVFRaw (I := I) (M := M) g₁ g_bg) x w),
    g₀.symm x (inverseMetricSharpFib (I := I) g₀ x om)
      (PDE.DeTurck.connectionDifference (I := I) g₁ g₀ x (deTurckVFRaw (I := I) (M := M) g₁ g_bg x) w)]

end DifferentialGeometry.PDE.RicciFlow

end
