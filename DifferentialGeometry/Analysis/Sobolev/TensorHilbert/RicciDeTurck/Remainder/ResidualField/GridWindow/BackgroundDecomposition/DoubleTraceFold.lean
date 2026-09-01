import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.RicciArmResidualCoefficientFields
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.OperatorFieldInputSlotSymmetrization
import DifferentialGeometry.Analysis.Sobolev.BoundedFactorProductGrid
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.MetricPerturbation.ArmCoefficient.ReindexingNorm
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.MetricLoweredConnectionDifferenceCoefficient
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.RicciDeTurck.Remainder.ResidualField.GridWindow.InverseMetricQuadraticResidual
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.RicciDeTurck.Remainder.ResidualField.GridWindow.BackgroundDecomposition.MultilinearIdentities
open DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Analysis.Elliptic
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

open DifferentialGeometry.PDE.RicciFlow DifferentialGeometry.Analysis.Sobolev
    DifferentialGeometry.Analysis.Spectral
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

section bgrConversion

open DifferentialGeometry.Analysis.Sobolev.TensorHilbert

variable (g₀ g₁ : SmoothRiemannianMetric I M)

omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] [SigmaCompactSpace M] in
omit [I.Boundaryless] in
lemma movingMetricDoubleTraceField_self_eq (s : ℕ) :
    secondMetricCometricDoubleTraceField (I := I) (M := M) g₀ g₀ s = cometricDoubleTraceField
      (I := I) g₀ s := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rw [cometricDoubleTraceField_toSection]
  rfl

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] [SigmaCompactSpace M] in
private lemma slotInsertEndoCc_add_local (s : ℕ)
    (A B : ContMDiffSection I (E →L[ℝ] E) ∞
      (fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x)) :
    endoSlotZeroCcTensor (I := I) (M := M) g₀ s (A + B) =
      endoSlotZeroCcTensor (I := I) (M := M) g₀ s A +
        endoSlotZeroCcTensor (I := I) (M := M) g₀ s B := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  apply ContinuousLinearMap.ext
  intro D
  rw [show ((endoSlotZeroCcTensor (I := I) (M := M) g₀ s A +
        endoSlotZeroCcTensor (I := I) (M := M) g₀ s B).toSection x) =
      (endoSlotZeroCcTensor (I := I) (M := M) g₀ s A).toSection x +
        (endoSlotZeroCcTensor (I := I) (M := M) g₀ s B).toSection x from by
    rw [SmoothCcTensor.toSection_add]; rfl]
  rw [add_apply]
  simp only [slotInsertEndoCc_toSection]
  rw [show ((A + B) x) = A x + B x from by rw [ContMDiffSection.coe_add]; rfl]
  rw [slotInsertEndoFib_add_left, add_apply]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [BoundarylessManifold I M] [SigmaCompactSpace M] in
omit [I.Boundaryless] in
private lemma metricComparisonEndomorphismField_diff_split_local :
    metricComparisonEndomorphismField (I := I) (M := M) g₀ g₁ =
      metricComparisonDifferenceEndomorphismField (I := I) g₀ g₁ +
        metricComparisonEndomorphismField (I := I) (M := M) g₀ g₀ := by
  apply ContMDiffSection.ext
  intro x
  rw [show ((metricComparisonDifferenceEndomorphismField (I := I) g₀ g₁ +
        metricComparisonEndomorphismField (I := I) (M := M) g₀ g₀) x) =
      metricComparisonDifferenceEndomorphismField (I := I) g₀ g₁ x +
        metricComparisonEndomorphismField (I := I) (M := M) g₀ g₀ x from by
    rw [ContMDiffSection.coe_add]; rfl]
  apply ContinuousLinearMap.ext
  intro v
  rw [metricComparisonEndomorphismField_apply, add_apply]
  rw [show (metricComparisonDifferenceEndomorphismField (I := I) g₀ g₁ x) = metricComparisonDifferenceEndomorphism (I := I) g₀ g₁ x
    from rfl]
  rw [metricComparisonEndomorphismField_apply]
  rw [metricComparisonEndomorphism_eq_diff_add_id (I := I) g₀ g₁ x v]
  rw [show metricComparisonEndomorphism (I := I) g₀ g₀ x v = v from by
    rw [metricComparisonEndomorphism_apply, inverseMetricSharpFib_g0FlatCLM]]

omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] [SigmaCompactSpace M] in
omit [I.Boundaryless] in
private lemma operatorFieldComposition_slotInsert_id_eq (s c : ℕ) (Φ : SmoothCcTensor g₀ (s + 1) c) :
    ccOperatorFieldComp (I := I) (M := M) g₀ (s + 1) (s + 1) c Φ
      (endoSlotZeroCcTensor (I := I) (M := M) g₀ s
        (metricComparisonEndomorphismField (I := I) (M := M) g₀ g₀)) = Φ := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  apply ContinuousLinearMap.ext
  intro D
  rw [show ((ccOperatorFieldComp (I := I) (M := M) g₀ (s + 1) (s + 1) c Φ
      (endoSlotZeroCcTensor (I := I) (M := M) g₀ s
        (metricComparisonEndomorphismField (I := I) (M := M) g₀ g₀))).toSection x) D =
      ((show Tensor0SSpace (s + 1) I x →L[ℝ] Tensor0SSpace c I x from Φ.toSection x)
        (slotInsertEndoFib (I := I) (M := M) (s + 1) 0 x
          (metricComparisonEndomorphismField (I := I) (M := M) g₀ g₀ x) D)) from by
    rw [operatorFieldComposition_toSection]
    rfl]
  refine congrArg _ ?_
  apply Tensor0SSpace.toModel_injective
  refine ContinuousMultilinearMap.ext (fun m => ?_)
  rw [slotInsertEndoFib_apply_eval]
  rw [show tangentLinearMapToModel
      (metricComparisonEndomorphismField (I := I) (M := M) g₀ g₀ x) (m 0) = m 0 from by
    rw [tangentLinearMapToModel_apply, metricComparisonEndomorphismField_apply,
      metricComparisonEndomorphism_apply, inverseMetricSharpFib_g0FlatCLM,
      ContinuousLinearEquiv.apply_symm_apply]]
  rw [Function.update_eq_self]

omit [BoundarylessManifold I M] [SigmaCompactSpace M] in
omit [I.Boundaryless] in
private lemma movingMetricDoubleTraceField_eq_trace_fullRaised (s : ℕ) :
    secondMetricCometricDoubleTraceField (I := I) (M := M) g₀ g₁ s =
      ccOperatorFieldComp (I := I) (M := M) g₀ (s + 2) (s + 2) s
        (cometricDoubleTraceField (I := I) g₀ s)
        (endoSlotZeroCcTensor (I := I) (M := M) g₀ (s + 1)
          (metricComparisonEndomorphismField (I := I) (M := M) g₀ g₁)) := by
  classical
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  apply ContinuousLinearMap.ext
  intro Z
  apply Tensor0SSpace.toModel_injective
  apply ContinuousMultilinearMap.ext
  intro mm
  have hLHS : Tensor0SSpace.toModel
      ((show Tensor0SSpace (s + 2) I x →L[ℝ] Tensor0SSpace s I x from
        (secondMetricCometricDoubleTraceField (I := I) (M := M) g₀ g₁ s).toSection x) Z) mm =
      ∑ c : Fin (Module.finrank ℝ E),
        Tensor0SSpace.toModel Z
          (Fin.cons ((smoothOrthoFrame (I := I) g₁ x c x : TangentSpace I x) : E)
            (Fin.cons ((smoothOrthoFrame (I := I) g₁ x c x : TangentSpace I x) : E) mm)) := by
    rw [show ((show Tensor0SSpace (s + 2) I x →L[ℝ] Tensor0SSpace s I x from
        (secondMetricCometricDoubleTraceField (I := I) (M := M) g₀ g₁ s).toSection x) Z) =
        cometricDoubleTraceFib (I := I) g₁ s x Z from rfl]
    rw [cometricDoubleTraceFib_toModel (I := I) g₁ s x Z]
    rw [modelDoubleTrace_apply (E := E) s (cometricLmodel (I := I) g₁ x)]
    rw [cometric_dualTrace_eq_orthoFrame_diag (I := I) g₁ x
      (mem_smoothOrthoFrameNbhd_self (I := I) (M := M) x) (Tensor0SSpace.toModel Z) mm]
    with_unfolding_all rfl
  rw [hLHS]
  have hRHS : Tensor0SSpace.toModel
      ((show Tensor0SSpace (s + 2) I x →L[ℝ] Tensor0SSpace s I x from
        (ccOperatorFieldComp (I := I) (M := M) g₀ (s + 2) (s + 2) s
          (cometricDoubleTraceField (I := I) g₀ s)
          (endoSlotZeroCcTensor (I := I) (M := M) g₀ (s + 1)
            (metricComparisonEndomorphismField (I := I) (M := M) g₀ g₁))).toSection x) Z) mm =
      ∑ a : Fin (Module.finrank ℝ E),
        Tensor0SSpace.toModel Z
          (Fin.cons (show E from metricComparisonEndomorphism (I := I) g₀ g₁ x
              (smoothOrthoFrame (I := I) g₀ x a x))
            (Fin.cons ((smoothOrthoFrame (I := I) g₀ x a x : TangentSpace I x) : E) mm)) := by
    rw [show ((show Tensor0SSpace (s + 2) I x →L[ℝ] Tensor0SSpace s I x from
        (ccOperatorFieldComp (I := I) (M := M) g₀ (s + 2) (s + 2) s
          (cometricDoubleTraceField (I := I) g₀ s)
          (endoSlotZeroCcTensor (I := I) (M := M) g₀ (s + 1)
            (metricComparisonEndomorphismField (I := I) (M := M) g₀ g₁))).toSection x) Z) =
        cometricDoubleTraceFib (I := I) g₀ s x
          (slotInsertEndoFib (I := I) (M := M) (s + 2) 0 x
            (metricComparisonEndomorphismField (I := I) (M := M) g₀ g₁ x) Z) from by
      rw [operatorFieldComposition_toSection]
      rfl]
    rw [cometricDoubleTraceFib_toModel (I := I) g₀ s x]
    rw [modelDoubleTrace_apply (E := E) s (cometricLmodel (I := I) g₀ x)]
    rw [cometric_dualTrace_eq_orthoFrame_diag (I := I) g₀ x
      (mem_smoothOrthoFrameNbhd_self (I := I) (M := M) x)
      (Tensor0SSpace.toModel
        (slotInsertEndoFib (I := I) (M := M) (s + 2) 0 x
          (metricComparisonEndomorphismField (I := I) (M := M) g₀ g₁ x) Z)) mm]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [slotInsertEndoFib_apply_eval]
    rw [Fin.update_cons_zero]
    rfl
  rw [hRHS]
  have hGrep : ∀ a : Fin (Module.finrank ℝ E),
      (show E from metricComparisonEndomorphism (I := I) g₀ g₁ x (smoothOrthoFrame (I := I) g₀ x a x)) =
        ∑ c : Fin (Module.finrank ℝ E),
          (g₀.inner x (smoothOrthoFrame (I := I) g₀ x a x) (smoothOrthoFrame (I := I) g₁ x c x)) •
            (smoothOrthoFrame (I := I) g₁ x c x : E) := by
    intro a
    have h1 := tangent_eq_sum_inner_smoothOrthoFrame (I := I) (M := M) g₁ x
      (metricComparisonEndomorphism (I := I) g₀ g₁ x (smoothOrthoFrame (I := I) g₀ x a x))
    rw [show (show E from metricComparisonEndomorphism (I := I) g₀ g₁ x
        (smoothOrthoFrame (I := I) g₀ x a x)) =
        metricComparisonEndomorphism (I := I) g₀ g₁ x (smoothOrthoFrame (I := I) g₀ x a x) from rfl]
    conv_lhs => rw [h1]
    refine Finset.sum_congr rfl fun c _ => ?_
    congr 1
    rw [g₁.symm x (smoothOrthoFrame (I := I) g₁ x c x)
      (metricComparisonEndomorphism (I := I) g₀ g₁ x (smoothOrthoFrame (I := I) g₀ x a x))]
    rw [show g₁.inner x (metricComparisonEndomorphism (I := I) g₀ g₁ x (smoothOrthoFrame (I := I) g₀ x a x))
        (smoothOrthoFrame (I := I) g₁ x c x) =
        g₀.inner x (smoothOrthoFrame (I := I) g₀ x a x)
          (smoothOrthoFrame (I := I) g₁ x c x) from by
      rw [metricComparisonEndomorphism_apply]
      rw [inverseMetricSharpFib_inner (I := I) g₁ x
        (g0FlatCLM (I := I) g₀ x (smoothOrthoFrame (I := I) g₀ x a x))
        (smoothOrthoFrame (I := I) g₁ x c x)]
      rw [show cotangentToDualLinear (I := I) (x := x)
          (g0FlatCLM (I := I) g₀ x (smoothOrthoFrame (I := I) g₀ x a x))
          (smoothOrthoFrame (I := I) g₁ x c x) =
          cotangentToDual (I := I) (x := x)
            (g0FlatCLM (I := I) g₀ x (smoothOrthoFrame (I := I) g₀ x a x))
            (smoothOrthoFrame (I := I) g₁ x c x) from rfl]
      rw [cotangentToDual_g0FlatCLM]]
  symm
  calc (∑ a : Fin (Module.finrank ℝ E),
        Tensor0SSpace.toModel Z
          (Fin.cons (show E from metricComparisonEndomorphism (I := I) g₀ g₁ x
              (smoothOrthoFrame (I := I) g₀ x a x))
            (Fin.cons ((smoothOrthoFrame (I := I) g₀ x a x : TangentSpace I x) : E) mm)))
      = ∑ a : Fin (Module.finrank ℝ E), ∑ c : Fin (Module.finrank ℝ E),
          (g₀.inner x (smoothOrthoFrame (I := I) g₀ x a x)
            (smoothOrthoFrame (I := I) g₁ x c x)) *
          Tensor0SSpace.toModel Z
            (Fin.cons ((smoothOrthoFrame (I := I) g₁ x c x : TangentSpace I x) : E)
              (Fin.cons ((smoothOrthoFrame (I := I) g₀ x a x : TangentSpace I x) : E) mm)) := by
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [hGrep a]
        exact toModel_cons_sum_smul (E := E) (Tensor0SSpace.toModel Z)
          (Module.finrank ℝ E)
          (fun c => g₀.inner x (smoothOrthoFrame (I := I) g₀ x a x)
            (smoothOrthoFrame (I := I) g₁ x c x))
          (fun c => (smoothOrthoFrame (I := I) g₁ x c x : E))
          (Fin.cons ((smoothOrthoFrame (I := I) g₀ x a x : TangentSpace I x) : E) mm)
    _ = ∑ c : Fin (Module.finrank ℝ E), ∑ a : Fin (Module.finrank ℝ E),
          (g₀.inner x (smoothOrthoFrame (I := I) g₀ x a x)
            (smoothOrthoFrame (I := I) g₁ x c x)) *
          Tensor0SSpace.toModel Z
            (Fin.cons ((smoothOrthoFrame (I := I) g₁ x c x : TangentSpace I x) : E)
              (Fin.cons ((smoothOrthoFrame (I := I) g₀ x a x : TangentSpace I x) : E) mm)) :=
        Finset.sum_comm
    _ = ∑ c : Fin (Module.finrank ℝ E),
          Tensor0SSpace.toModel Z
            (Fin.cons ((smoothOrthoFrame (I := I) g₁ x c x : TangentSpace I x) : E)
              (Fin.cons ((smoothOrthoFrame (I := I) g₁ x c x : TangentSpace I x) : E) mm)) := by
        refine Finset.sum_congr rfl fun c _ => ?_
        have hsum := toModel_cons_cons_sum_smul (E := E) (Tensor0SSpace.toModel Z)
          ((smoothOrthoFrame (I := I) g₁ x c x : TangentSpace I x) : E)
          (Module.finrank ℝ E)
          (fun a => g₀.inner x (smoothOrthoFrame (I := I) g₀ x a x)
            (smoothOrthoFrame (I := I) g₁ x c x))
          (fun a => (smoothOrthoFrame (I := I) g₀ x a x : E)) mm
        rw [← hsum]
        have hrep0 := tangent_eq_sum_inner_smoothOrthoFrame (I := I) (M := M) g₀ x
          (smoothOrthoFrame (I := I) g₁ x c x)
        with_unfolding_all exact
          (congrArg (fun u : TangentSpace I x =>
            Tensor0SSpace.toModel Z
              (Fin.cons (smoothOrthoFrame (I := I) g₁ x c x) (Fin.cons u mm))) hrep0.symm)

omit [BoundarylessManifold I M] [SigmaCompactSpace M] in
omit [I.Boundaryless] in
private lemma movingMetricDoubleTraceField_cross_split (s : ℕ) :
    secondMetricCometricDoubleTraceField (I := I) (M := M) g₀ g₁ s =
      ccOperatorFieldComp (I := I) (M := M) g₀ (s + 2) (s + 2) s
        (cometricDoubleTraceField (I := I) g₀ s)
        (endoSlotZeroCcTensor (I := I) (M := M) g₀ (s + 1)
          (metricComparisonDifferenceEndomorphismField (I := I) g₀ g₁)) +
      cometricDoubleTraceField (I := I) g₀ s := by
  rw [movingMetricDoubleTraceField_eq_trace_fullRaised (I := I) (M := M) g₀ g₁ s]
  rw [metricComparisonEndomorphismField_diff_split_local (I := I) (M := M) g₀ g₁]
  rw [slotInsertEndoCc_add_local (I := I) (M := M) g₀ (s + 1)]
  rw [operatorFieldComposition_add_right (I := I) (M := M) g₀ (s + 2) (s + 2) s
    (cometricDoubleTraceField (I := I) g₀ s)]
  rw [operatorFieldComposition_slotInsert_id_eq (I := I) (M := M) g₀ (s + 1) s
    (cometricDoubleTraceField (I := I) g₀ s)]

def secondMetricPairTraceOperator : SmoothCcTensor g₀ 6 2 :=
  ccOperatorFieldComp (I := I) (M := M) g₀ 6 4 2
    (secondMetricCometricDoubleTraceField (I := I) (M := M) g₀ g₁ 2)
    (secondMetricCometricDoubleTraceField (I := I) (M := M) g₀ g₁ 4)

omit [BoundarylessManifold I M] [SigmaCompactSpace M] in
omit [I.Boundaryless] in
lemma secondMetricPairTraceOperator_apply_toModel (X : SmoothCcTensor g₀ 0 4) (x : M)
    (D : Tensor0SSpace 2 I x) (v : Fin 2 → E) :
    Tensor0SSpace.toModel
        ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
          (ccOperatorFieldComp (I := I) (M := M) g₀ 2 6 2
            (secondMetricPairTraceOperator (I := I) (M := M) g₀ g₁)
            (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 ricciFoldRemainderSlotPerm
              (slotExtendIter (I := I) (M := M) g₀ 0 4 2 X))).toSection x) D) v =
      ∑ b : Fin (Module.finrank ℝ E), ∑ a : Fin (Module.finrank ℝ E),
        Tensor0SSpace.toModel D
            ![tangentSpaceModelContinuousLinearEquiv (I := I) x
                (smoothOrthoFrame (I := I) g₁ x a x),
              tangentSpaceModelContinuousLinearEquiv (I := I) x
                (smoothOrthoFrame (I := I) g₁ x b x)] *
          unitModel (I := I) (M := M) g₀ 4 X x
            ![v 0, v 1, tangentSpaceModelContinuousLinearEquiv (I := I) x
                (smoothOrthoFrame (I := I) g₁ x a x),
              tangentSpaceModelContinuousLinearEquiv (I := I) x
                (smoothOrthoFrame (I := I) g₁ x b x)] := by
  classical
  set Y : Tensor0SSpace 6 I x :=
    (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 6 I x from
      (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 ricciFoldRemainderSlotPerm
        (slotExtendIter (I := I) (M := M) g₀ 0 4 2 X)).toSection x) D with hY_def
  have hYval : ∀ w : Fin 6 → E,
      Tensor0SSpace.toModel Y w =
        Tensor0SSpace.toModel D ![w 1, w 3] *
          unitModel (I := I) (M := M) g₀ 4 X x ![w 4, w 5, w 0, w 2] := by
    intro w
    rw [hY_def]
    rw [show ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 6 I x from
        (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 ricciFoldRemainderSlotPerm
          (slotExtendIter (I := I) (M := M) g₀ 0 4 2 X)).toSection x) D) =
        ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 6 I x from
          tensorRSDomDomCongr ricciFoldRemainderSlotPerm
            ((slotExtendIter (I := I) (M := M) g₀ 0 4 2 X).toSection x)) D) from by
      rw [rsDomDomCongrSection_toSection]]
    rw [toModel_rsDomDomCongr_apply (I := I) (M := M) ricciFoldRemainderSlotPerm
      ((slotExtendIter (I := I) (M := M) g₀ 0 4 2 X).toSection x) D]
    rw [ContinuousMultilinearMap.domDomCongr_apply]
    rw [slotExtendIter_two_toModel (I := I) (M := M) g₀ X x D
      (fun i => w (ricciFoldRemainderSlotPerm i))]
    refine congrArg₂ (· * ·) ?_ ?_
    · refine congrArg _ ?_
      funext k
      fin_cases k <;> rfl
    · refine congrArg _ ?_
      funext k
      fin_cases k <;> rfl
  rw [show ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
      (ccOperatorFieldComp (I := I) (M := M) g₀ 2 6 2
        (secondMetricPairTraceOperator (I := I) (M := M) g₀ g₁)
        (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 ricciFoldRemainderSlotPerm
          (slotExtendIter (I := I) (M := M) g₀ 0 4 2 X))).toSection x) D) =
      cometricDoubleTraceFib (I := I) g₁ 2 x
        (cometricDoubleTraceFib (I := I) g₁ 4 x Y) from by
    rw [hY_def]
    rw [operatorFieldComposition_toSection]
    rfl]
  rw [cometricDoubleTraceFib_toModel (I := I) g₁ 2 x]
  rw [modelDoubleTrace_apply (E := E) 2 (cometricLmodel (I := I) g₁ x)]
  rw [cometric_dualTrace_eq_orthoFrame_diag (I := I) g₁ x
    (mem_smoothOrthoFrameNbhd_self (I := I) (M := M) x)
    (Tensor0SSpace.toModel (cometricDoubleTraceFib (I := I) g₁ 4 x Y))
    (fun j => (v j : E))]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [cometricDoubleTraceFib_toModel (I := I) g₁ 4 x Y]
  rw [modelDoubleTrace_apply (E := E) 4 (cometricLmodel (I := I) g₁ x)]
  with_unfolding_all
    rw [cometric_dualTrace_eq_orthoFrame_diag (I := I) g₁ x
      (mem_smoothOrthoFrameNbhd_self (I := I) (M := M) x)
      (Tensor0SSpace.toModel Y)
      (Fin.cons (tangentSpaceModelContinuousLinearEquiv (I := I) x
          (smoothOrthoFrame (I := I) g₁ x b x))
        (Fin.cons (tangentSpaceModelContinuousLinearEquiv (I := I) x
            (smoothOrthoFrame (I := I) g₁ x b x))
          (fun j => (v j : E))))]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [hYval]
  rfl

def riemannCometricDoubleTraceFold : SmoothCcTensor g₀ 2 4 :=
  ccOperatorFieldComp (I := I) (M := M) g₀ 2 6 4 (cometricDoubleTraceField (I := I) g₀ 4)
    (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 (Equiv.swap (1 : Fin 6) 3)
      (slotExtendIter (I := I) (M := M) g₀ 0 4 2
        (riemannLoweredCc (I := I) (M := M) g₀ g₀ g₀)))

omit [SigmaCompactSpace M] in
omit [I.Boundaryless] in
lemma bgRArmWeight_toModel (x : M) (D : Tensor0SSpace 2 I x)
    (m : Fin 4 → E) :
    Tensor0SSpace.toModel
        ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 4 I x from
          (riemannCometricDoubleTraceFold (I := I) (M := M) g₀).toSection x) D) m =
      ∑ e : Fin (Module.finrank ℝ E),
        Tensor0SSpace.toModel D
            ![(smoothOrthoFrame (I := I) g₀ x e x : E), (m 1 : E)] *
          g₀.inner x (riemannOp (LeviCivita (I := I) g₀) x (m 0) (m 2) (m 3))
            (smoothOrthoFrame (I := I) g₀ x e x) := by
  classical
  set Y : Tensor0SSpace 6 I x :=
    (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 6 I x from
      (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 (Equiv.swap (1 : Fin 6) 3)
        (slotExtendIter (I := I) (M := M) g₀ 0 4 2
          (riemannLoweredCc (I := I) (M := M) g₀ g₀ g₀))).toSection x) D with hY_def
  have hYval : ∀ w : Fin 6 → E,
      Tensor0SSpace.toModel Y w =
        Tensor0SSpace.toModel D ![w 0, w 3] *
          unitModel (I := I) (M := M) g₀ 4
            (riemannLoweredCc (I := I) (M := M) g₀ g₀ g₀) x ![w 2, w 1, w 4, w 5] := by
    intro w
    rw [hY_def]
    rw [show ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 6 I x from
        (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 (Equiv.swap (1 : Fin 6) 3)
          (slotExtendIter (I := I) (M := M) g₀ 0 4 2
            (riemannLoweredCc (I := I) (M := M) g₀ g₀ g₀))).toSection x) D) =
        ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 6 I x from
          tensorRSDomDomCongr (Equiv.swap (1 : Fin 6) 3)
            ((slotExtendIter (I := I) (M := M) g₀ 0 4 2
              (riemannLoweredCc (I := I) (M := M) g₀ g₀ g₀)).toSection x)) D) from by
      rw [rsDomDomCongrSection_toSection]]
    rw [toModel_rsDomDomCongr_apply (I := I) (M := M) (Equiv.swap (1 : Fin 6) 3)
      ((slotExtendIter (I := I) (M := M) g₀ 0 4 2
        (riemannLoweredCc (I := I) (M := M) g₀ g₀ g₀)).toSection x) D]
    rw [ContinuousMultilinearMap.domDomCongr_apply]
    rw [slotExtendIter_two_toModel (I := I) (M := M) g₀
      (riemannLoweredCc (I := I) (M := M) g₀ g₀ g₀) x D
      (fun i => w ((Equiv.swap (1 : Fin 6) 3) i))]
    refine congrArg₂ (· * ·) ?_ ?_
    · refine congrArg _ ?_
      funext k
      fin_cases k <;> simp [Equiv.swap_apply_def]
    · refine congrArg _ ?_
      funext k
      fin_cases k <;> simp [Equiv.swap_apply_def]
  rw [show ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 4 I x from
      (riemannCometricDoubleTraceFold (I := I) (M := M) g₀).toSection x) D) =
      cometricDoubleTraceFib (I := I) g₀ 4 x Y from by
    rw [hY_def, riemannCometricDoubleTraceFold]
    rw [operatorFieldComposition_toSection]
    rfl]
  rw [cometricDoubleTraceFib_toModel (I := I) g₀ 4 x Y]
  rw [modelDoubleTrace_apply (E := E) 4 (cometricLmodel (I := I) g₀ x)]
  rw [cometric_dualTrace_eq_orthoFrame_diag (I := I) g₀ x
    (mem_smoothOrthoFrameNbhd_self (I := I) (M := M) x)
    (Tensor0SSpace.toModel Y) (fun j => (m j : E))]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [hYval]
  change Tensor0SSpace.toModel D
      ![((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E), (m 1 : E)] *
      unitModel (I := I) (M := M) g₀ 4
        (riemannLoweredCc (I := I) (M := M) g₀ g₀ g₀) x
        ![(m 0 : E), ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E),
          (m 2 : E), (m 3 : E)] = _
  rw [riemannLoweredCc_unitModel_apply (I := I) (M := M) g₀ g₀ g₀ x
    ![(m 0 : E), ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E),
      (m 2 : E), (m 3 : E)]]
  rfl

lemma exists_riemannianFiberNormSq_iteratedCovGrad_movingMetricDoubleTraceField_window (s : ℕ) {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ C : ℕ → ℝ, (∀ u, 0 ≤ C u) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        (_htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀) (_hδ0 : 0 ≤ δ)
        (_hbound : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P)
          δ)
        (u K : ℕ) (_huK : u ≤ K) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g₀ (s + 2) (s + u) x
            ((iteratedCovGrad (I := I) g₀ (s + 2) s u
              (secondMetricCometricDoubleTraceField (I := I) (M := M) g₀ g₁ s)).toSection x) ≤
          C u * Combinatorics.boundedFactorGridWindow
            (fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
              ((iteratedCovGrad (I := I) g₀ 0 2 l P).toSection x)) K (u + 1) := by
  classical
  obtain ⟨CΛ, hCΛ_nn, hCΛ⟩ :=
    riemannianFiberNormSq_iteratedCovGrad_slotInsertEndoCc_zero_metricComparisonDifferenceEndomorphism_diagGrid_le
      (I := I) (M := M) g₀ hδ₀
  set KD : ℕ → ℝ := fun u =>
    (exists_bound_riemannianFiberNormSq_smoothCcTensor (I := I) (M := M) g₀ (s + 2) (s + u)
      (iteratedCovGrad (I := I) g₀ (s + 2) s u (cometricDoubleTraceField (I := I) g₀ s))).choose
    with hKD_def
  have hKD_nn : ∀ u, 0 ≤ KD u := fun u =>
    (exists_bound_riemannianFiberNormSq_smoothCcTensor (I := I) (M := M) g₀ (s + 2) (s + u)
      (iteratedCovGrad (I := I) g₀ (s + 2) s u
        (cometricDoubleTraceField (I := I) g₀ s))).choose_spec.1
  have hKD : ∀ u (y : M),
      riemannianFiberNormSq (I := I) (M := M) g₀ (s + 2) (s + u) y
          ((iteratedCovGrad (I := I) g₀ (s + 2) s u
            (cometricDoubleTraceField (I := I) g₀ s)).toSection y) ≤ KD u := fun u =>
    (exists_bound_riemannianFiberNormSq_smoothCcTensor (I := I) (M := M) g₀ (s + 2) (s + u)
      (iteratedCovGrad (I := I) g₀ (s + 2) s u
        (cometricDoubleTraceField (I := I) g₀ s))).choose_spec.2
  refine ⟨fun u => 2 * (diagonalGridGrowthFactor (E := E) u *
      ∑ u₁ ∈ Finset.range (u + 1), KD u₁ *
        ∑ u₂ ∈ Finset.range (u + 1 - u₁), (Module.finrank ℝ E : ℝ) ^ (s + 1) * CΛ u₂) +
      2 * KD u, fun u => by
    have h1 : 0 ≤ diagonalGridGrowthFactor (E := E) u *
        ∑ u₁ ∈ Finset.range (u + 1), KD u₁ *
          ∑ u₂ ∈ Finset.range (u + 1 - u₁), (Module.finrank ℝ E : ℝ) ^ (s + 1) * CΛ u₂ :=
      mul_nonneg (operatorFieldApplicationGdiag_nonneg (E := E) u)
        (Finset.sum_nonneg fun u₁ _ => mul_nonneg (hKD_nn u₁)
          (Finset.sum_nonneg fun u₂ _ => mul_nonneg (by positivity) (hCΛ_nn u₂)))
    have h2 := hKD_nn u
    linarith, ?_⟩
  intro g₁ P htie δ hδ_le hδ0 hbound u K huK x
  set b : ℕ → ℝ := fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
    ((iteratedCovGrad (I := I) g₀ 0 2 l P).toSection x) with hb_def
  have hb_nn : ∀ l, 0 ≤ b l :=
    fun l => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + l) x _
  set W : ℝ := Combinatorics.boundedFactorGridWindow b K (u + 1) with hW_def
  have hW_nn : 0 ≤ W := Combinatorics.boundedFactorGridWindow_nonneg b hb_nn _ _
  have hW_one : 1 ≤ W := Combinatorics.one_le_boundedFactorGridWindow b hb_nn (by omega)
  have hsec : (iteratedCovGrad (I := I) g₀ (s + 2) s u
      (secondMetricCometricDoubleTraceField (I := I) (M := M) g₀ g₁ s)).toSection x =
      (iteratedCovGrad (I := I) g₀ (s + 2) s u
        (ccOperatorFieldComp (I := I) (M := M) g₀ (s + 2) (s + 2) s
          (cometricDoubleTraceField (I := I) g₀ s)
          (endoSlotZeroCcTensor (I := I) (M := M) g₀ (s + 1)
            (metricComparisonDifferenceEndomorphismField (I := I) g₀ g₁)))).toSection x +
      (iteratedCovGrad (I := I) g₀ (s + 2) s u
        (cometricDoubleTraceField (I := I) g₀ s)).toSection x := by
    rw [show secondMetricCometricDoubleTraceField (I := I) (M := M) g₀ g₁ s =
        ccOperatorFieldComp (I := I) (M := M) g₀ (s + 2) (s + 2) s
          (cometricDoubleTraceField (I := I) g₀ s)
          (endoSlotZeroCcTensor (I := I) (M := M) g₀ (s + 1)
            (metricComparisonDifferenceEndomorphismField (I := I) g₀ g₁)) +
        cometricDoubleTraceField (I := I) g₀ s from
      movingMetricDoubleTraceField_cross_split (I := I) (M := M) g₀ g₁ s]
    rw [iteratedCovGrad_add (I := I) g₀ (s + 2) s u _ _, SmoothCcTensor.toSection_add]
    rfl
  rw [hsec]
  refine le_trans (riemannianFiberNormSq_add_le (I := I) (M := M) g₀ (s + 2) (s + u) x _ _) ?_
  have hSI : ∀ u₂ : ℕ, u₂ ≤ u →
      riemannianFiberNormSq (I := I) (M := M) g₀ (s + 2) ((s + 2) + u₂) x
          ((iteratedCovGrad (I := I) g₀ (s + 2) (s + 2) u₂
            (endoSlotZeroCcTensor (I := I) (M := M) g₀ (s + 1)
              (metricComparisonDifferenceEndomorphismField (I := I) g₀ g₁))).toSection x) ≤
        ((Module.finrank ℝ E : ℝ) ^ (s + 1) * CΛ u₂) * W := by
    intro u₂ hu₂
    refine le_trans (riemannianFiberNormSq_iteratedCovGrad_slotInsertEndoCc_le_endo (I := I) (M := M) g₀
      (s + 1) (metricComparisonDifferenceEndomorphismField (I := I) g₀ g₁) u₂ x) ?_
    have hgrid := hCΛ g₁ P htie hδ_le hδ0 hbound u₂ x
    have hgw : (∑ n ∈ Finset.range (u₂ + 1),
        ∑ e ∈ Finset.Nat.antidiagonalTuple n u₂,
          ∏ m : Fin n, b (e m)) ≤ W := by
      rw [show (∑ n ∈ Finset.range (u₂ + 1),
          ∑ e ∈ Finset.Nat.antidiagonalTuple n u₂,
            ∏ m : Fin n, b (e m)) =
          Combinatorics.antidiagonalTupleGrid b u₂ from rfl]
      exact Combinatorics.antidiagonalTupleGrid_le_boundedFactorGridWindow b hb_nn
        (by omega) (by omega)
    calc (Module.finrank ℝ E : ℝ) ^ (s + 1) *
          riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + u₂) x
            ((iteratedCovGrad (I := I) g₀ 1 1 u₂
              (endoSlotZeroCcTensor (I := I) (M := M) g₀ 0
                (metricComparisonDifferenceEndomorphismField (I := I) g₀ g₁))).toSection x)
        ≤ (Module.finrank ℝ E : ℝ) ^ (s + 1) * (CΛ u₂ *
            ∑ n ∈ Finset.range (u₂ + 1),
              ∑ e ∈ Finset.Nat.antidiagonalTuple n u₂,
                ∏ m : Fin n, b (e m)) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          exact hgrid
      _ ≤ (Module.finrank ℝ E : ℝ) ^ (s + 1) * (CΛ u₂ * W) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hgw (hCΛ_nn u₂)) (by positivity)
      _ = ((Module.finrank ℝ E : ℝ) ^ (s + 1) * CΛ u₂) * W := by ring
  have hQ : riemannianFiberNormSq (I := I) (M := M) g₀ (s + 2) (s + u) x
      ((iteratedCovGrad (I := I) g₀ (s + 2) s u
        (ccOperatorFieldComp (I := I) (M := M) g₀ (s + 2) (s + 2) s
          (cometricDoubleTraceField (I := I) g₀ s)
          (endoSlotZeroCcTensor (I := I) (M := M) g₀ (s + 1)
            (metricComparisonDifferenceEndomorphismField (I := I) g₀ g₁)))).toSection x) ≤
      (diagonalGridGrowthFactor (E := E) u *
        ∑ u₁ ∈ Finset.range (u + 1), KD u₁ *
          ∑ u₂ ∈ Finset.range (u + 1 - u₁),
            (Module.finrank ℝ E : ℝ) ^ (s + 1) * CΛ u₂) * W := by
    refine le_trans
      (riemannianFiberNormSq_iteratedCovGrad_ccTensorCompose_diagonalProductGrid_leftFactor_le
      (I := I)
      (M := M) g₀ u (s + 2) (s + 2) s (cometricDoubleTraceField (I := I) g₀ s)
      (endoSlotZeroCcTensor (I := I) (M := M) g₀ (s + 1)
        (metricComparisonDifferenceEndomorphismField (I := I) g₀ g₁)) x) ?_
    calc diagonalGridGrowthFactor (E := E) u *
          ∑ u₁ ∈ Finset.range (u + 1),
            riemannianFiberNormSq (I := I) (M := M) g₀ (s + 2) (s + u₁) x
                ((iteratedCovGrad (I := I) g₀ (s + 2) s u₁
                  (cometricDoubleTraceField (I := I) g₀ s)).toSection x) *
              ∑ u₂ ∈ Finset.range (u + 1 - u₁),
                riemannianFiberNormSq (I := I) (M := M) g₀ (s + 2) ((s + 2) + u₂) x
                  ((iteratedCovGrad (I := I) g₀ (s + 2) (s + 2) u₂
                    (endoSlotZeroCcTensor (I := I) (M := M) g₀ (s + 1)
                      (metricComparisonDifferenceEndomorphismField (I := I) g₀ g₁))).toSection x)
        ≤ diagonalGridGrowthFactor (E := E) u *
            ∑ u₁ ∈ Finset.range (u + 1), KD u₁ *
              ∑ u₂ ∈ Finset.range (u + 1 - u₁),
                (((Module.finrank ℝ E : ℝ) ^ (s + 1) * CΛ u₂) * W) := by
          refine mul_le_mul_of_nonneg_left
            (Finset.sum_le_sum fun u₁ hu₁ => ?_) (operatorFieldApplicationGdiag_nonneg (E := E) u)
          refine mul_le_mul (hKD u₁ x) (Finset.sum_le_sum fun u₂ hu₂ => ?_)
            (Finset.sum_nonneg fun u₂ _ =>
              riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ (s + 2) ((s + 2) + u₂) x _)
            (hKD_nn u₁)
          rw [Finset.mem_range] at hu₁ hu₂
          exact hSI u₂ (by omega)
      _ = (diagonalGridGrowthFactor (E := E) u *
            ∑ u₁ ∈ Finset.range (u + 1), KD u₁ *
              ∑ u₂ ∈ Finset.range (u + 1 - u₁),
                (Module.finrank ℝ E : ℝ) ^ (s + 1) * CΛ u₂) * W := by
          have hstep : ∀ u₁ : ℕ, (KD u₁ *
              ∑ u₂ ∈ Finset.range (u + 1 - u₁),
                (((Module.finrank ℝ E : ℝ) ^ (s + 1) * CΛ u₂) * W)) =
              (KD u₁ * ∑ u₂ ∈ Finset.range (u + 1 - u₁),
                (Module.finrank ℝ E : ℝ) ^ (s + 1) * CΛ u₂) * W := by
            intro u₁
            rw [← Finset.sum_mul]
            ring
          rw [Finset.sum_congr rfl fun u₁ _ => hstep u₁, ← Finset.sum_mul]
          ring
  have hCDT : riemannianFiberNormSq (I := I) (M := M) g₀ (s + 2) (s + u) x
      ((iteratedCovGrad (I := I) g₀ (s + 2) s u
        (cometricDoubleTraceField (I := I) g₀ s)).toSection x) ≤ KD u * W := by
    calc riemannianFiberNormSq (I := I) (M := M) g₀ (s + 2) (s + u) x
          ((iteratedCovGrad (I := I) g₀ (s + 2) s u
            (cometricDoubleTraceField (I := I) g₀ s)).toSection x)
        ≤ KD u := hKD u x
      _ = KD u * 1 := by ring
      _ ≤ KD u * W := mul_le_mul_of_nonneg_left hW_one (hKD_nn u)
  calc 2 * riemannianFiberNormSq (I := I) (M := M) g₀ (s + 2) (s + u) x
        ((iteratedCovGrad (I := I) g₀ (s + 2) s u
          (ccOperatorFieldComp (I := I) (M := M) g₀ (s + 2) (s + 2) s
            (cometricDoubleTraceField (I := I) g₀ s)
            (endoSlotZeroCcTensor (I := I) (M := M) g₀ (s + 1)
              (metricComparisonDifferenceEndomorphismField (I := I) g₀ g₁)))).toSection x) +
      2 * riemannianFiberNormSq (I := I) (M := M) g₀ (s + 2) (s + u) x
        ((iteratedCovGrad (I := I) g₀ (s + 2) s u
          (cometricDoubleTraceField (I := I) g₀ s)).toSection x)
      ≤ 2 * ((diagonalGridGrowthFactor (E := E) u *
            ∑ u₁ ∈ Finset.range (u + 1), KD u₁ *
              ∑ u₂ ∈ Finset.range (u + 1 - u₁),
                (Module.finrank ℝ E : ℝ) ^ (s + 1) * CΛ u₂) * W) + 2 * (KD u * W) := by
        have hnn := riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ (s + 2) (s + u) x
          ((iteratedCovGrad (I := I) g₀ (s + 2) s u
            (cometricDoubleTraceField (I := I) g₀ s)).toSection x)
        linarith [hQ, hCDT]
    _ = (2 * (diagonalGridGrowthFactor (E := E) u *
          ∑ u₁ ∈ Finset.range (u + 1), KD u₁ *
            ∑ u₂ ∈ Finset.range (u + 1 - u₁),
              (Module.finrank ℝ E : ℝ) ^ (s + 1) * CΛ u₂) + 2 * KD u) * W := by ring


lemma exists_riemannianFiberNormSq_iteratedCovGrad_movingMetricPairTraceOperator_window {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ C : ℕ → ℝ, (∀ u, 0 ≤ C u) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        (_htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀) (_hδ0 : 0 ≤ δ)
        (_hbound : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P)
          δ)
        (u K : ℕ) (_huK : u ≤ K) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g₀ 6 (2 + u) x
            ((iteratedCovGrad (I := I) g₀ 6 2 u
              (secondMetricPairTraceOperator (I := I) (M := M) g₀ g₁)).toSection x) ≤
          C u * Combinatorics.boundedFactorGridWindow
            (fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
              ((iteratedCovGrad (I := I) g₀ 0 2 l P).toSection x)) K (u + 1) := by
  classical
  obtain ⟨C2, hC2_nn, hC2⟩ :=
    exists_riemannianFiberNormSq_iteratedCovGrad_movingMetricDoubleTraceField_window (I := I) (M := M) g₀ 2 hδ₀
  obtain ⟨C4, hC4_nn, hC4⟩ :=
    exists_riemannianFiberNormSq_iteratedCovGrad_movingMetricDoubleTraceField_window (I := I) (M := M) g₀ 4 hδ₀
  refine ⟨fun u => diagonalGridGrowthFactor (E := E) u *
      ∑ u₁ ∈ Finset.range (u + 1), C2 u₁ *
        ∑ u₂ ∈ Finset.range (u + 1 - u₁),
          C4 u₂ * Combinatorics.windowPairCellCount (u₁ + 1) (u₂ + 1),
    fun u => mul_nonneg (operatorFieldApplicationGdiag_nonneg (E := E) u)
      (Finset.sum_nonneg fun u₁ _ => mul_nonneg (hC2_nn u₁)
        (Finset.sum_nonneg fun u₂ _ => mul_nonneg (hC4_nn u₂)
          (Combinatorics.windowPairCellCount_nonneg _ _))), ?_⟩
  intro g₁ P htie δ hδ_le hδ0 hbound u K huK x
  set b : ℕ → ℝ := fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
    ((iteratedCovGrad (I := I) g₀ 0 2 l P).toSection x) with hb_def
  have hb_nn : ∀ l, 0 ≤ b l :=
    fun l => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + l) x _
  refine le_trans
    (riemannianFiberNormSq_iteratedCovGrad_ccTensorCompose_diagonalProductGrid_leftFactor_le
    (I := I)
    (M := M) g₀ u 6 4 2 (secondMetricCometricDoubleTraceField (I := I) (M := M) g₀ g₁ 2)
    (secondMetricCometricDoubleTraceField (I := I) (M := M) g₀ g₁ 4) x) ?_
  calc diagonalGridGrowthFactor (E := E) u *
        ∑ u₁ ∈ Finset.range (u + 1),
          riemannianFiberNormSq (I := I) (M := M) g₀ 4 (2 + u₁) x
              ((iteratedCovGrad (I := I) g₀ 4 2 u₁
                (secondMetricCometricDoubleTraceField (I := I) (M := M) g₀ g₁ 2)).toSection x) *
            ∑ u₂ ∈ Finset.range (u + 1 - u₁),
              riemannianFiberNormSq (I := I) (M := M) g₀ 6 (4 + u₂) x
                ((iteratedCovGrad (I := I) g₀ 6 4 u₂
                  (secondMetricCometricDoubleTraceField (I := I) (M := M) g₀ g₁ 4)).toSection x)
      ≤ diagonalGridGrowthFactor (E := E) u *
          ∑ u₁ ∈ Finset.range (u + 1),
            (C2 u₁ * Combinatorics.boundedFactorGridWindow b K (u₁ + 1)) *
            ∑ u₂ ∈ Finset.range (u + 1 - u₁),
              (C4 u₂ * Combinatorics.boundedFactorGridWindow b K (u₂ + 1)) := by
        refine mul_le_mul_of_nonneg_left
          (Finset.sum_le_sum fun u₁ hu₁ => ?_) (operatorFieldApplicationGdiag_nonneg (E := E) u)
        rw [Finset.mem_range] at hu₁
        refine mul_le_mul (hC2 g₁ P htie hδ_le hδ0 hbound u₁ K (by omega) x)
          (Finset.sum_le_sum fun u₂ hu₂ => ?_)
          (Finset.sum_nonneg fun u₂ _ =>
            riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 6 (4 + u₂) x _)
          (mul_nonneg (hC2_nn u₁)
            (Combinatorics.boundedFactorGridWindow_nonneg b hb_nn _ _))
        rw [Finset.mem_range] at hu₂
        exact hC4 g₁ P htie hδ_le hδ0 hbound u₂ K (by omega) x
    _ ≤ (diagonalGridGrowthFactor (E := E) u *
          ∑ u₁ ∈ Finset.range (u + 1), C2 u₁ *
            ∑ u₂ ∈ Finset.range (u + 1 - u₁),
              C4 u₂ * Combinatorics.windowPairCellCount (u₁ + 1) (u₂ + 1)) *
          Combinatorics.boundedFactorGridWindow b K (u + 1) := by
        rw [mul_assoc]
        refine mul_le_mul_of_nonneg_left ?_ (operatorFieldApplicationGdiag_nonneg (E := E) u)
        rw [Finset.sum_mul]
        refine Finset.sum_le_sum fun u₁ hu₁ => ?_
        rw [Finset.mul_sum, Finset.mul_sum, Finset.sum_mul]
        refine Finset.sum_le_sum fun u₂ hu₂ => ?_
        rw [Finset.mem_range] at hu₁ hu₂
        calc C2 u₁ * Combinatorics.boundedFactorGridWindow b K (u₁ + 1) *
              (C4 u₂ * Combinatorics.boundedFactorGridWindow b K (u₂ + 1))
            = (C2 u₁ * C4 u₂) *
                (Combinatorics.boundedFactorGridWindow b K (u₁ + 1) *
                  Combinatorics.boundedFactorGridWindow b K (u₂ + 1)) := by ring
          _ ≤ (C2 u₁ * C4 u₂) *
                (Combinatorics.windowPairCellCount (u₁ + 1) (u₂ + 1) *
                  Combinatorics.boundedFactorGridWindow b K ((u₁ + 1) + (u₂ + 1) - 1)) := by
              refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg (hC2_nn u₁) (hC4_nn u₂))
              exact Combinatorics.boundedFactorGridWindow_mul_le b hb_nn K (u₁ + 1) (u₂ + 1)
                (by omega) (by omega)
          _ ≤ (C2 u₁ * C4 u₂) *
                (Combinatorics.windowPairCellCount (u₁ + 1) (u₂ + 1) *
                  Combinatorics.boundedFactorGridWindow b K (u + 1)) := by
              refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg (hC2_nn u₁) (hC4_nn u₂))
              refine mul_le_mul_of_nonneg_left ?_
                (Combinatorics.windowPairCellCount_nonneg _ _)
              exact Combinatorics.boundedFactorGridWindow_mono b hb_nn (le_refl _) (by omega)
          _ = C2 u₁ * (C4 u₂ * Combinatorics.windowPairCellCount (u₁ + 1) (u₂ + 1)) *
                Combinatorics.boundedFactorGridWindow b K (u + 1) := by ring

end bgrConversion

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
