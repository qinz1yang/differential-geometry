import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.CurvatureCoefficientDifferenceJetTower.Lowered

open DifferentialGeometry.Tensor.Multilinear
open DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Analysis.Elliptic
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Connection.Realization
open DifferentialGeometry.Geometry.Operator

noncomputable section


open Bundle Manifold MeasureTheory Set Filter DifferentialGeometry.Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators

namespace DifferentialGeometry
namespace Analysis
namespace Spectral

open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.Analysis.Spectral.MetricRealization
  (gFibreOpBound ccTensorBilinSymm ccTensorBilin ccTensorBilin_apply ccTensorModel
    ccTensorMultilinear ccTensorBilinSymm_contMDiff ccTensorBilinSymm_apply ccTensorBilinSymm_symm)
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Analysis.Sobolev.TensorHilbert
open DifferentialGeometry.Analysis.Spectral.DeTurck

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

namespace CurvatureCoefficientDifferenceJetTower
end CurvatureCoefficientDifferenceJetTower

open CurvatureCoefficientDifferenceJetTower

section RiemannLoweredDifference



namespace CurvatureCoefficientDifferenceJetTower

def quadraticConnectionDifferenceCc (g₀ g₁ : SmoothRiemannianMetric I M) :
    SmoothCcTensor g₀ 1 3 :=
  ccOperatorFieldComp (I := I) (M := M) g₀ 1 2 3
    (termSlotEndoPassZeroCc (I := I) (M := M) g₀ (connectionDifferenceTermFieldPt (I := I) (M := M) g₀ g₁))
    (connectionDifferenceSection (I := I) g₁ g₀)

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [SigmaCompactSpace M] in
lemma quadraticConnectionDifferenceCc_toModel (g₀ g₁ : SmoothRiemannianMetric I M) (x : M)
    (om : Tensor0SSpace 1 I x) (w : Fin 3 → E) :
    Tensor0SSpace.toModel
        ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 3 I x from
          (quadraticConnectionDifferenceCc (I := I) (M := M) g₀ g₁).toSection x) om) w =
      cotangentToDual (I := I) (x := x) om
        (PDE.DeTurck.connectionDifference (I := I) g₁ g₀ x
          (PDE.DeTurck.connectionDifference (I := I) g₁ g₀ x
            ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm (w 1))
            ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm (w 2)))
          ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm (w 0))) := by
  rw [show ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 3 I x from
        (quadraticConnectionDifferenceCc (I := I) (M := M) g₀ g₁).toSection x) om) =
      ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 3 I x from
        (ccOperatorFieldComp (I := I) (M := M) g₀ 1 2 3
          (termSlotEndoPassZeroCc (I := I) (M := M) g₀
            (connectionDifferenceTermFieldPt (I := I) (M := M) g₀ g₁))
          (connectionDifferenceSection (I := I) g₁ g₀)).toSection x) om) from rfl]
  rw [toModel_operatorFieldComposition_termSlotEndoPassZeroCc_eval (I := I) (M := M) g₀
    (connectionDifferenceTermFieldPt (I := I) (M := M) g₀ g₁) (connectionDifferenceSection (I := I) g₁ g₀) x om w]
  rw [show ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 2 I x from
        (connectionDifferenceSection (I := I) g₁ g₀).toSection x) om) =
      connectionDifferencePairing (I := I) g₁ g₀ x om from rfl]
  rw [Tensor0SSpace.toModel_apply_model_vector]
  rw [show (fun j : Fin 2 =>
        (tangentSpaceModelContinuousLinearEquiv (I := I) x).symm
          (if j = 0 then
            tangentSpaceModelContinuousLinearEquiv (I := I) x
              (connectionDifferenceTermFieldPt (I := I) (M := M) g₀ g₁ x
                ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm (w 1))
                ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm (w 2)))
          else w 0)) =
      (Fin.cons (PDE.DeTurck.connectionDifference (I := I) g₁ g₀ x
          ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm (w 1))
          ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm (w 2)))
        (fun _ : Fin 1 =>
          (tangentSpaceModelContinuousLinearEquiv (I := I) x).symm (w 0)) :
        Fin 2 → TangentSpace I x) from by
    funext j
    refine Fin.cases ?_ ?_ j
    · rw [if_pos rfl, ContinuousLinearEquiv.symm_apply_apply]
      rfl
    · intro i
      rw [if_neg (Fin.succ_ne_zero i)]
      rfl]
  rw [connectionDifferencePairing_apply]
  rw [cotangentToDual_apply]
  rfl

def covectorExtensionSection (g₀ : SmoothRiemannianMetric I M) (x : M)
    (om : Tensor0SSpace 1 I x) :
    Cₛ^∞⟮I; Tensor0SModel 1 ℝ E, (fun y : M => Tensor0SSpace 1 I y)⟯ :=
  letI := Tensor0SBundle.tensor0SBundleTopology (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) 1
  ⟨fun b : M => g0FlatCLM (I := I) g₀ b
      (smoothExtensionTangent (I := I) x (inverseMetricSharpFib (I := I) g₀ x om) b),
   by
     have hU : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
         (fun b : M => TotalSpace.mk' E (E := fun z : M => TangentSpace I z) b
           (smoothExtensionTangent (I := I) x (inverseMetricSharpFib (I := I) g₀ x om) b)) :=
       smoothExtensionTangent_contMDiff (I := I) x (inverseMetricSharpFib (I := I) g₀ x om)
     exact ContMDiff.clm_bundle_apply (b := id) (g0FlatField_contMDiff (I := I) g₀) hU⟩

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [SigmaCompactSpace M] in
lemma covectorExtensionSection_self (g₀ : SmoothRiemannianMetric I M) (x : M)
    (om : Tensor0SSpace 1 I x) :
    covectorExtensionSection (I := I) (M := M) g₀ x om x = om := by
  change g0FlatCLM (I := I) g₀ x
      (smoothExtensionTangent (I := I) x (inverseMetricSharpFib (I := I) g₀ x om) x) = om
  rw [smoothExtensionTangent_eq (I := I) x (inverseMetricSharpFib (I := I) g₀ x om)]
  exact g0FlatCLM_inverseMetricSharpFib (I := I) g₀ x om

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
theorem riemannLoweredBackgroundDifference_palatini_repr
    (g₀ g₁ : SmoothRiemannianMetric I M) :
    cometricRaiseSlot0Field (I := I) (M := M) g₀ 2
        (domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 4) 1)
          (riemannLoweredBackgroundDifference (I := I) (M := M) g₀ g₁)) =
      rsDomDomCongrSection (I := I) (M := M) g₀ 1 3 (Equiv.swap (1 : Fin 3) 2)
          (covGrad (I := I) (M := M) g₀ 1 2 (connectionDifferenceSection (I := I) g₁ g₀) +
            quadraticConnectionDifferenceCc (I := I) (M := M) g₀ g₁) -
        rsDomDomCongrSection (I := I) (M := M) g₀ 1 3 (finRotate 3)
          (covGrad (I := I) (M := M) g₀ 1 2 (connectionDifferenceSection (I := I) g₁ g₀) +
            quadraticConnectionDifferenceCc (I := I) (M := M) g₀ g₁) := by
  classical
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  apply ContinuousLinearMap.ext
  intro om
  apply Tensor0SSpace.toModel_injective
  apply ContinuousMultilinearMap.ext
  intro v
  let vt : Fin 3 → TangentSpace I x :=
    fun i => (tangentSpaceModelContinuousLinearEquiv (I := I) x).symm (v i)
  set X0 : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
    smoothExtensionTangentSection (I := I) (M := M) x (vt 0) with hX0_def
  set X1 : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
    smoothExtensionTangentSection (I := I) (M := M) x (vt 1) with hX1_def
  set X2 : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
    smoothExtensionTangentSection (I := I) (M := M) x (vt 2) with hX2_def
  have hX0x : X0 x = vt 0 := smoothExtensionTangent_eq (I := I) x (vt 0)
  have hX1x : X1 x = vt 1 := smoothExtensionTangent_eq (I := I) x (vt 1)
  have hX2x : X2 x = vt 2 := smoothExtensionTangent_eq (I := I) x (vt 2)
  set omSec : Cₛ^∞⟮I; Tensor0SModel 1 ℝ E, (fun y : M => Tensor0SSpace 1 I y)⟯ :=
    covectorExtensionSection (I := I) (M := M) g₀ x om with homSec_def
  have homx : omSec x = om := covectorExtensionSection_self (I := I) (M := M) g₀ x om
  set u : TangentSpace I x := inverseMetricSharpFib (I := I) g₀ x om with hu_def
  have hpair : ∀ ww : TangentSpace I x,
      g₀.inner x ww u = cotangentToDual (I := I) (x := x) om ww := by
    intro ww
    rw [hu_def]
    rw [g₀.symm x ww (inverseMetricSharpFib (I := I) g₀ x om)]
    rw [g0_inner_inverseMetricSharp_mixed (I := I) (M := M) g₀ g₀ x om ww]
    rw [show metricComparisonEndomorphism (I := I) g₀ g₀ x ww = ww from by
      rw [metricComparisonEndomorphism_apply, inverseMetricSharpFib_g0FlatCLM]]
  have hDQ : ∀ (X Y Z : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯),
      Tensor0SSpace.toModel
        ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 3 I x from
          ((covGrad (I := I) (M := M) g₀ 1 2 (connectionDifferenceSection (I := I) g₁ g₀) +
            quadraticConnectionDifferenceCc (I := I) (M := M) g₀ g₁)).toSection x) om)
        (Fin.cons (tangentSpaceModelContinuousLinearEquiv (I := I) x (X x))
          (Fin.cons (tangentSpaceModelContinuousLinearEquiv (I := I) x (Y x))
            ![tangentSpaceModelContinuousLinearEquiv (I := I) x (Z x)])) =
      cotangentToDual (I := I) (x := x) om
          (covDerivConnectionDifference (I := I) g₀ g₁ (fun b => X b) (fun b => Z b) (fun b => Y b) x) +
        cotangentToDual (I := I) (x := x) om
          (PDE.DeTurck.connectionDifference (I := I) g₁ g₀ x
            (PDE.DeTurck.connectionDifference (I := I) g₁ g₀ x (Y x) (Z x)) (X x)) := by
    intro X Y Z
    have hsplit : ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 3 I x from
        ((covGrad (I := I) (M := M) g₀ 1 2 (connectionDifferenceSection (I := I) g₁ g₀) +
          quadraticConnectionDifferenceCc (I := I) (M := M) g₀ g₁)).toSection x) om) =
        ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 3 I x from
          (covGrad (I := I) (M := M) g₀ 1 2 (connectionDifferenceSection (I := I) g₁ g₀)).toSection x) om) +
        ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 3 I x from
          (quadraticConnectionDifferenceCc (I := I) (M := M) g₀ g₁).toSection x) om) := by
      rw [SmoothCcTensor.toSection_add]
      rfl
    rw [hsplit, Tensor0SSpace.toModel_add, add_apply]
    have hbridge : Tensor0SSpace.toModel
        ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 3 I x from
          (covGrad (I := I) (M := M) g₀ 1 2 (connectionDifferenceSection (I := I) g₁ g₀)).toSection x) om)
        (Fin.cons (tangentSpaceModelContinuousLinearEquiv (I := I) x (X x))
          (Fin.cons (tangentSpaceModelContinuousLinearEquiv (I := I) x (Y x))
            ![tangentSpaceModelContinuousLinearEquiv (I := I) x (Z x)])) =
        cotangentToDual (I := I) (x := x) om
          (covDerivConnectionDifference (I := I) g₀ g₁ (fun b => X b) (fun b => Z b) (fun b => Y b) x) := by
      rw [← homx]
      rw [connectionDifferenceSection_covGrad_eq_covDerivConnectionDifference (I := I) (M := M) g₁ g₀ omSec X Y Z x]
      rw [cotangentToDual_apply]
    rw [hbridge]
    rw [quadraticConnectionDifferenceCc_toModel (I := I) (M := M) g₀ g₁ x om
      (Fin.cons (tangentSpaceModelContinuousLinearEquiv (I := I) x (X x))
        (Fin.cons (tangentSpaceModelContinuousLinearEquiv (I := I) x (Y x))
          ![tangentSpaceModelContinuousLinearEquiv (I := I) x (Z x)]))]
    rfl
  have htor : (LeviCivita (I := I) g₀).torsion = 0 := LeviCivita_torsion_eq_zero (I := I) g₀
  have hpal := riemannSec_difference (LeviCivita (I := I) g₀) (LeviCivita (I := I) g₁)
    (X := fun b => X0 b) (Y := fun b => X1 b) (Z := fun b => X2 b)
    X0.contMDiff X1.contMDiff X2.contMDiff htor x
  have hop1 : riemannOp (LeviCivita (I := I) g₁) x (vt 0) (vt 1) (vt 2) =
      riemannSec (LeviCivita (I := I) g₁) (fun b => X0 b) (fun b => X1 b) (fun b => X2 b) x := by
    rw [← hX0x, ← hX1x, ← hX2x]
    exact riemannOp_apply_smooth (cov := LeviCivita (I := I) g₁)
      X0.contMDiff X1.contMDiff X2.contMDiff
  have hop0 : riemannOp (LeviCivita (I := I) g₀) x (vt 0) (vt 1) (vt 2) =
      riemannSec (LeviCivita (I := I) g₀) (fun b => X0 b) (fun b => X1 b) (fun b => X2 b) x := by
    rw [← hX0x, ← hX1x, ← hX2x]
    exact riemannOp_apply_smooth (cov := LeviCivita (I := I) g₀)
      X0.contMDiff X1.contMDiff X2.contMDiff
  have hLHS : Tensor0SSpace.toModel
      ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 3 I x from
        (cometricRaiseSlot0Field (I := I) (M := M) g₀ 2
          (domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 4) 1)
            (riemannLoweredBackgroundDifference (I := I) (M := M) g₀ g₁))).toSection x) om) v =
      g₀.inner x (riemannOp (LeviCivita (I := I) g₁) x (vt 0) (vt 1) (vt 2)) u -
        g₀.inner x (riemannOp (LeviCivita (I := I) g₀) x (vt 0) (vt 1) (vt 2)) u := by
    rw [show ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 3 I x from
          (cometricRaiseSlot0Field (I := I) (M := M) g₀ 2
            (domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 4) 1)
              (riemannLoweredBackgroundDifference (I := I) (M := M) g₀ g₁))).toSection x) om) =
        ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 3 I x from
          cometricRaiseSlot0Fib g₀ 2 x
            ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 4 I x from
              (domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 4) 1)
                (riemannLoweredBackgroundDifference (I := I) (M := M) g₀ g₁)).toSection x)
              (unitTensor (I := I) (M := M) x))) om) from rfl]
    rw [cometricRaiseSlot0Fib_clm_apply (I := I) g₀ 2 x
      ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 4 I x from
        (domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 4) 1)
          (riemannLoweredBackgroundDifference (I := I) (M := M) g₀ g₁)).toSection x)
        (unitTensor (I := I) (M := M) x)) om]
    rw [interiorProduct_toModel_eval_pal (I := I) (M := M) 3 x
      (inverseMetricSharpFib (I := I) g₀ x om) _ v]
    rw [show Tensor0SSpace.toModel
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 4 I x from
          (domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 4) 1)
            (riemannLoweredBackgroundDifference (I := I) (M := M) g₀ g₁)).toSection x)
          (unitTensor (I := I) (M := M) x)) =
        unitModel (I := I) (M := M) g₀ 4
          (domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 4) 1)
            (riemannLoweredBackgroundDifference (I := I) (M := M) g₀ g₁)) x from rfl]
    rw [domDomCongrSection_unitModel (I := I) g₀ (Equiv.swap (0 : Fin 4) 1)
      (riemannLoweredBackgroundDifference (I := I) (M := M) g₀ g₁) x]
    rw [ContinuousMultilinearMap.domDomCongr_apply]
    rw [show (fun i : Fin 4 =>
        (Fin.cons (tangentSpaceModelContinuousLinearEquiv (I := I) x
          (inverseMetricSharpFib (I := I) g₀ x om)) v : Fin 4 → E)
          ((Equiv.swap (0 : Fin 4) 1) i)) =
      (![v 0, tangentSpaceModelContinuousLinearEquiv (I := I) x u, v 1, v 2] : Fin 4 → E) from by
      funext i
      fin_cases i <;> rfl]
    rw [riemannLoweredBackgroundDifference_unitModel_apply (I := I) (M := M) g₀ g₁ x
      (![v 0, tangentSpaceModelContinuousLinearEquiv (I := I) x u, v 1, v 2] : Fin 4 → E)]
    rfl
  rw [hLHS]
  have hRHSsub : Tensor0SSpace.toModel
      ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 3 I x from
        (rsDomDomCongrSection (I := I) (M := M) g₀ 1 3 (Equiv.swap (1 : Fin 3) 2)
            (covGrad (I := I) (M := M) g₀ 1 2 (connectionDifferenceSection (I := I) g₁ g₀) +
              quadraticConnectionDifferenceCc (I := I) (M := M) g₀ g₁) -
          rsDomDomCongrSection (I := I) (M := M) g₀ 1 3 (finRotate 3)
            (covGrad (I := I) (M := M) g₀ 1 2 (connectionDifferenceSection (I := I) g₁ g₀) +
              quadraticConnectionDifferenceCc (I := I) (M := M) g₀ g₁)).toSection x) om) v =
      Tensor0SSpace.toModel
        ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 3 I x from
          (rsDomDomCongrSection (I := I) (M := M) g₀ 1 3 (Equiv.swap (1 : Fin 3) 2)
            (covGrad (I := I) (M := M) g₀ 1 2 (connectionDifferenceSection (I := I) g₁ g₀) +
              quadraticConnectionDifferenceCc (I := I) (M := M) g₀ g₁)).toSection x) om) v -
      Tensor0SSpace.toModel
        ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 3 I x from
          (rsDomDomCongrSection (I := I) (M := M) g₀ 1 3 (finRotate 3)
            (covGrad (I := I) (M := M) g₀ 1 2 (connectionDifferenceSection (I := I) g₁ g₀) +
              quadraticConnectionDifferenceCc (I := I) (M := M) g₀ g₁)).toSection x) om) v := by
    rw [show ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 3 I x from
        (rsDomDomCongrSection (I := I) (M := M) g₀ 1 3 (Equiv.swap (1 : Fin 3) 2)
            (covGrad (I := I) (M := M) g₀ 1 2 (connectionDifferenceSection (I := I) g₁ g₀) +
              quadraticConnectionDifferenceCc (I := I) (M := M) g₀ g₁) -
          rsDomDomCongrSection (I := I) (M := M) g₀ 1 3 (finRotate 3)
            (covGrad (I := I) (M := M) g₀ 1 2 (connectionDifferenceSection (I := I) g₁ g₀) +
              quadraticConnectionDifferenceCc (I := I) (M := M) g₀ g₁)).toSection x) om) =
        ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 3 I x from
          (rsDomDomCongrSection (I := I) (M := M) g₀ 1 3 (Equiv.swap (1 : Fin 3) 2)
            (covGrad (I := I) (M := M) g₀ 1 2 (connectionDifferenceSection (I := I) g₁ g₀) +
              quadraticConnectionDifferenceCc (I := I) (M := M) g₀ g₁)).toSection x) om) -
        ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 3 I x from
          (rsDomDomCongrSection (I := I) (M := M) g₀ 1 3 (finRotate 3)
            (covGrad (I := I) (M := M) g₀ 1 2 (connectionDifferenceSection (I := I) g₁ g₀) +
              quadraticConnectionDifferenceCc (I := I) (M := M) g₀ g₁)).toSection x) om) from by
      rw [SmoothCcTensor.toSection_sub]
      rfl]
    rw [Tensor0SSpace.toModel_sub, sub_apply]
  rw [hRHSsub]
  have hterm : ∀ (σ : Equiv.Perm (Fin 3)) (X Y Z : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯),
      ((fun i => v (σ i)) : Fin 3 → E) =
        Fin.cons (tangentSpaceModelContinuousLinearEquiv (I := I) x (X x))
          (Fin.cons (tangentSpaceModelContinuousLinearEquiv (I := I) x (Y x))
            ![tangentSpaceModelContinuousLinearEquiv (I := I) x (Z x)]) →
      Tensor0SSpace.toModel
        ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 3 I x from
          (rsDomDomCongrSection (I := I) (M := M) g₀ 1 3 σ
            (covGrad (I := I) (M := M) g₀ 1 2 (connectionDifferenceSection (I := I) g₁ g₀) +
              quadraticConnectionDifferenceCc (I := I) (M := M) g₀ g₁)).toSection x) om) v =
      cotangentToDual (I := I) (x := x) om
          (covDerivConnectionDifference (I := I) g₀ g₁ (fun b => X b) (fun b => Z b) (fun b => Y b) x) +
        cotangentToDual (I := I) (x := x) om
          (PDE.DeTurck.connectionDifference (I := I) g₁ g₀ x
            (PDE.DeTurck.connectionDifference (I := I) g₁ g₀ x (Y x) (Z x)) (X x)) := by
    intro σ X Y Z htup
    rw [show ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 3 I x from
        (rsDomDomCongrSection (I := I) (M := M) g₀ 1 3 σ
          (covGrad (I := I) (M := M) g₀ 1 2 (connectionDifferenceSection (I := I) g₁ g₀) +
            quadraticConnectionDifferenceCc (I := I) (M := M) g₀ g₁)).toSection x) om) =
        ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 3 I x from
          rsDomDomCongr σ
            ((covGrad (I := I) (M := M) g₀ 1 2 (connectionDifferenceSection (I := I) g₁ g₀) +
              quadraticConnectionDifferenceCc (I := I) (M := M) g₀ g₁).toSection x)) om) from by
      rw [rsDomDomCongrSection_toSection]]
    rw [toModel_rsDomDomCongr_apply (I := I) (M := M) σ
      ((covGrad (I := I) (M := M) g₀ 1 2 (connectionDifferenceSection (I := I) g₁ g₀) +
        quadraticConnectionDifferenceCc (I := I) (M := M) g₀ g₁).toSection x) om]
    rw [ContinuousMultilinearMap.domDomCongr_apply]
    rw [htup]
    exact hDQ X Y Z
  have htup1 : ((fun i => v ((Equiv.swap (1 : Fin 3) 2) i)) : Fin 3 → E) =
      Fin.cons (tangentSpaceModelContinuousLinearEquiv (I := I) x (X0 x))
        (Fin.cons (tangentSpaceModelContinuousLinearEquiv (I := I) x (X2 x))
          ![tangentSpaceModelContinuousLinearEquiv (I := I) x (X1 x)]) := by
    funext k
    fin_cases k
    · simp only [Fin.isValue, Fin.zero_eta, Nat.reduceAdd, Matrix.Fin.cons_vecCons,
        Nat.succ_eq_add_one, Fin.cons_zero, hX0x, vt,
        ContinuousLinearEquiv.apply_symm_apply]
      apply congrArg v
      decide
    · simp only [Fin.isValue, Fin.mk_one, Nat.reduceAdd, Matrix.Fin.cons_vecCons,
        Nat.succ_eq_add_one, Fin.cons_one, Matrix.cons_val_zero, hX2x, vt,
        ContinuousLinearEquiv.apply_symm_apply]
      apply congrArg v
      decide
    · simp only [Fin.isValue, Fin.reduceFinMk, Nat.reduceAdd, Matrix.Fin.cons_vecCons,
        Nat.succ_eq_add_one, Matrix.cons_val, hX1x, vt,
        ContinuousLinearEquiv.apply_symm_apply]
      apply congrArg v
      decide
  have htup2 : ((fun i => v ((finRotate 3) i)) : Fin 3 → E) =
      Fin.cons (tangentSpaceModelContinuousLinearEquiv (I := I) x (X1 x))
        (Fin.cons (tangentSpaceModelContinuousLinearEquiv (I := I) x (X2 x))
          ![tangentSpaceModelContinuousLinearEquiv (I := I) x (X0 x)]) := by
    funext k
    fin_cases k
    · simp only [Fin.zero_eta, Fin.isValue, Nat.reduceAdd, Matrix.Fin.cons_vecCons,
        Nat.succ_eq_add_one, Fin.cons_zero, hX1x, vt,
        ContinuousLinearEquiv.apply_symm_apply]
      apply congrArg v
      decide
    · simp only [Fin.mk_one, Fin.isValue, Nat.reduceAdd, Matrix.Fin.cons_vecCons,
        Nat.succ_eq_add_one, Fin.cons_one, Matrix.cons_val_zero, hX2x, vt,
        ContinuousLinearEquiv.apply_symm_apply]
      apply congrArg v
      decide
    · simp only [Fin.reduceFinMk, Fin.isValue, Nat.reduceAdd, Matrix.Fin.cons_vecCons,
        Nat.succ_eq_add_one, Matrix.cons_val, hX0x, vt,
        ContinuousLinearEquiv.apply_symm_apply]
      apply congrArg v
      decide
  rw [hterm (Equiv.swap (1 : Fin 3) 2) X0 X2 X1 htup1]
  rw [hterm (finRotate 3) X1 X2 X0 htup2]
  rw [hop1, hop0]
  rw [hpal]
  rw [map_add (g₀.inner x), add_apply]
  rw [map_add (g₀.inner x), add_apply]
  rw [map_sub (g₀.inner x), sub_apply]
  rw [map_sub (g₀.inner x), sub_apply]
  simp only [hpair]
  have hc1 : covDerivConnectionDifference (I := I) g₀ g₁
      (fun b => X0 b) (fun b => X1 b) (fun b => X2 b) x =
      covDerivDiff (LeviCivita (I := I) g₀) (LeviCivita (I := I) g₁)
        (fun b => X0 b) (fun b => X1 b) (fun b => X2 b) x := rfl
  have hc2 : covDerivConnectionDifference (I := I) g₀ g₁
      (fun b => X1 b) (fun b => X0 b) (fun b => X2 b) x =
      covDerivDiff (LeviCivita (I := I) g₀) (LeviCivita (I := I) g₁)
        (fun b => X1 b) (fun b => X0 b) (fun b => X2 b) x := rfl
  have hq1 : PDE.DeTurck.connectionDifference (I := I) g₁ g₀ x
      (PDE.DeTurck.connectionDifference (I := I) g₁ g₀ x (X2 x) (X1 x)) (X0 x) =
      CovariantDerivative.difference (LeviCivita (I := I) g₁) (LeviCivita (I := I) g₀) x
        (diffSec (LeviCivita (I := I) g₀) (LeviCivita (I := I) g₁)
          (fun b => X1 b) (fun b => X2 b) x) ((fun b => X0 b) x) := rfl
  have hq2 : PDE.DeTurck.connectionDifference (I := I) g₁ g₀ x
      (PDE.DeTurck.connectionDifference (I := I) g₁ g₀ x (X2 x) (X0 x)) (X1 x) =
      CovariantDerivative.difference (LeviCivita (I := I) g₁) (LeviCivita (I := I) g₀) x
        (diffSec (LeviCivita (I := I) g₀) (LeviCivita (I := I) g₁)
          (fun b => X0 b) (fun b => X2 b) x) ((fun b => X1 b) x) := rfl
  rw [← hc1, ← hc2, ← hq1, ← hq2]
  ring

def gridSumPairCount (m1 m2 : ℕ) : ℝ :=
  ∑ k1 ∈ Finset.range m1, ∑ k2 ∈ Finset.range m2, tGridCount k1 * tGridCount k2

lemma gridSumPairCount_nonneg (m1 m2 : ℕ) : 0 ≤ gridSumPairCount m1 m2 :=
  Finset.sum_nonneg fun k1 _ => Finset.sum_nonneg fun k2 _ =>
    mul_nonneg (tGridCount_nonneg k1) (tGridCount_nonneg k2)

lemma gridSum_mul_gridSum_le (b : ℕ → ℝ) (hb : ∀ j, 0 ≤ b j) (m1 m2 m3 : ℕ)
    (h3 : m1 + m2 ≤ m3 + 1) :
    (∑ k ∈ Finset.range m1, Combinatorics.antidiagonalTupleGrid b k) *
      (∑ k ∈ Finset.range m2, Combinatorics.antidiagonalTupleGrid b k) ≤
    gridSumPairCount m1 m2 * ∑ k ∈ Finset.range m3, Combinatorics.antidiagonalTupleGrid b k := by
  classical
  have hG_nn : ∀ k, 0 ≤ Combinatorics.antidiagonalTupleGrid b k :=
    fun k => Combinatorics.antidiagonalTupleGrid_nonneg b hb k
  have hS3_nn : 0 ≤ ∑ k ∈ Finset.range m3, Combinatorics.antidiagonalTupleGrid b k :=
    Finset.sum_nonneg fun k _ => hG_nn k
  rw [Finset.sum_mul]
  rw [gridSumPairCount, Finset.sum_mul]
  refine Finset.sum_le_sum fun k1 hk1 => ?_
  calc Combinatorics.antidiagonalTupleGrid b k1 *
        ∑ k ∈ Finset.range m2, Combinatorics.antidiagonalTupleGrid b k
      = ∑ k2 ∈ Finset.range m2, Combinatorics.antidiagonalTupleGrid b k1 *
          Combinatorics.antidiagonalTupleGrid b k2 := by rw [Finset.mul_sum]
    _ ≤ ∑ k2 ∈ Finset.range m2, (tGridCount k1 * tGridCount k2) *
          (∑ k ∈ Finset.range m3, Combinatorics.antidiagonalTupleGrid b k) := by
        refine Finset.sum_le_sum fun k2 hk2 => ?_
        refine le_trans (antidiagonalTupleGrid_mul_le b hb k1 k2) ?_
        refine mul_le_mul_of_nonneg_left ?_
          (mul_nonneg (tGridCount_nonneg k1) (tGridCount_nonneg k2))
        refine Finset.single_le_sum (f := fun k => Combinatorics.antidiagonalTupleGrid b k)
          (fun k _ => hG_nn k) ?_
        rw [Finset.mem_range] at hk1 hk2 ⊢
        omega
    _ = (∑ k2 ∈ Finset.range m2, tGridCount k1 * tGridCount k2) *
          (∑ k ∈ Finset.range m3, Combinatorics.antidiagonalTupleGrid b k) := by
        rw [Finset.sum_mul]

def perturbationSharpEndoFib (g₀ : SmoothRiemannianMetric I M)
    (T : SmoothCcTensor g₀ 0 2) (x : M) :
    TangentSpace I x →L[ℝ] TangentSpace I x :=
  LinearMap.toContinuousLinearMap
    { toFun := fun v => metricSharp (I := I) g₀ x
        (ccTensorBilinSymm (I := I) g₀ T x v).toLinearMap
      map_add' := fun v v' => by
        have h : ((ccTensorBilinSymm (I := I) g₀ T x (v + v')).toLinearMap) =
            (ccTensorBilinSymm (I := I) g₀ T x v).toLinearMap +
              (ccTensorBilinSymm (I := I) g₀ T x v').toLinearMap := by
          ext w
          simp [map_add]
        rw [show metricSharp (I := I) g₀ x
            (ccTensorBilinSymm (I := I) g₀ T x (v + v')).toLinearMap =
            (metricFlatMap (I := I) g₀ x).symm
              (ccTensorBilinSymm (I := I) g₀ T x (v + v')).toLinearMap from rfl,
          h, map_add]
        rfl
      map_smul' := fun c v => by
        have h : ((ccTensorBilinSymm (I := I) g₀ T x (c • v)).toLinearMap) =
            c • (ccTensorBilinSymm (I := I) g₀ T x v).toLinearMap := by
          ext w
          simp [map_smul]
        rw [show metricSharp (I := I) g₀ x
            (ccTensorBilinSymm (I := I) g₀ T x (c • v)).toLinearMap =
            (metricFlatMap (I := I) g₀ x).symm
              (ccTensorBilinSymm (I := I) g₀ T x (c • v)).toLinearMap from rfl,
          h, map_smul]
        rfl }

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
lemma perturbationSharpEndoFib_apply (g₀ : SmoothRiemannianMetric I M)
    (T : SmoothCcTensor g₀ 0 2) (x : M) (v : TangentSpace I x) :
    perturbationSharpEndoFib (I := I) (M := M) g₀ T x v =
      metricSharp (I := I) g₀ x (ccTensorBilinSymm (I := I) g₀ T x v).toLinearMap := by
  rw [perturbationSharpEndoFib, LinearMap.coe_toContinuousLinearMap']
  rfl

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
lemma inner_perturbationSharpEndoFib (g₀ : SmoothRiemannianMetric I M)
    (T : SmoothCcTensor g₀ 0 2) (x : M) (v w : TangentSpace I x) :
    g₀.inner x (perturbationSharpEndoFib (I := I) (M := M) g₀ T x v) w =
      ccTensorBilinSymm (I := I) g₀ T x v w := by
  rw [perturbationSharpEndoFib_apply]
  exact inner_metricSharp (I := I) g₀ x
    (ccTensorBilinSymm (I := I) g₀ T x v).toLinearMap w

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [BoundarylessManifold I M] in
omit [I.Boundaryless] [SigmaCompactSpace M] in
theorem perturbationSharpEndoFib_contMDiff (g₀ : SmoothRiemannianMetric I M)
    (T : SmoothCcTensor g₀ 0 2) :
    ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E)) ∞
      (fun x : M => TotalSpace.mk' (E →L[ℝ] E)
        (E := fun y : M => TangentSpace I y →L[ℝ] TangentSpace I y) x
        (perturbationSharpEndoFib (I := I) (M := M) g₀ T x)) := by
  apply contMDiff_continuousLinearMap_section_of_apply (I := I) (M := M)
    (F₂ := E) (V₂ := fun y : M => TangentSpace I y)
    (φ := fun x : M => perturbationSharpEndoFib (I := I) (M := M) g₀ T x)
  intro Y
  have hcv : ∀ (α : M) (j : Fin (Module.finrank ℝ E)),
      ContMDiffOn I 𝓘(ℝ) ∞
        (fun b : M => (ccTensorBilinSymm (I := I) g₀ T b (Y b)).toLinearMap
          (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α j b))
        (chartAt H α).source := by
    intro α j
    have hB : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
        (fun b : M => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
          (E := fun y => TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ) b
          (ccTensorBilinSymm (I := I) g₀ T b)) :=
      ccTensorBilinSymm_contMDiff (I := I) g₀ T
    have hBasis : ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞
        (DifferentialGeometry.Tensor.Coordinates.chartBasisVec (I := I) α j)
        (trivializationAt E (TangentSpace I) α).baseSet :=
      DifferentialGeometry.Tensor.Coordinates.chartBasisVec_contMDiffOn (I := I) α j
    have happ : ContMDiffOn I (I.prod 𝓘(ℝ, ℝ)) ∞
        (fun b : M => (⟨b,
            ccTensorBilinSymm (I := I) g₀ T b (Y b) (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α j b)⟩ :
            TotalSpace ℝ (Bundle.Trivial M ℝ)))
        (trivializationAt E (TangentSpace I) α).baseSet :=
      ContMDiffOn.clm_bundle_apply₂ (F₁ := E) (F₂ := E) (F₃ := ℝ)
        (b := id) hB.contMDiffOn Y.contMDiff.contMDiffOn hBasis
    have hbase_eq :
        (trivializationAt E (TangentSpace I) α).baseSet = (chartAt H α).source :=
      trivializationAt_baseSet_eq_chartAt_source (I := I) α
    rw [hbase_eq] at happ
    intro b hb
    have hpb := happ b hb
    rw [Bundle.contMDiffWithinAt_totalSpace] at hpb
    exact hpb.2
  have hsmooth := metricSharp_contMDiff_total (I := I) g₀
    (cv := fun b : M => (ccTensorBilinSymm (I := I) g₀ T b (Y b)).toLinearMap) hcv
  refine hsmooth.congr ?_
  intro x
  change TotalSpace.mk' E x
      (metricSharp (I := I) g₀ x (ccTensorBilinSymm (I := I) g₀ T x (Y x)).toLinearMap) =
    TotalSpace.mk' E x (perturbationSharpEndoFib (I := I) (M := M) g₀ T x (Y x))
  rw [perturbationSharpEndoFib_apply]

def perturbationSharpEndoField (g₀ : SmoothRiemannianMetric I M)
    (T : SmoothCcTensor g₀ 0 2) :
    ContMDiffSection I (E →L[ℝ] E) ∞
      (fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x) where
  toFun := fun x : M => perturbationSharpEndoFib (I := I) (M := M) g₀ T x
  contMDiff_toFun := perturbationSharpEndoFib_contMDiff (I := I) (M := M) g₀ T

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
lemma unitModel_eq_ccTensorBilin_pt (g₀ : SmoothRiemannianMetric I M)
    (S : SmoothCcTensor g₀ 0 2) (b : M) (u w : TangentSpace I b) :
    unitModel (I := I) (M := M) g₀ 2 S b ![u, w] = ccTensorBilin (I := I) g₀ S b u w := by
  rw [ccTensorBilin_apply (I := I) g₀ S b u w, ccTensorModel]
  rw [show ccTensorMultilinear (I := I) g₀ S b =
      (show Tensor0SSpace 0 I b →L[ℝ] Tensor0SSpace 2 I b from S.toSection b)
        (unitZeroSec (I := I) (M := M) b) from rfl]
  rw [unitModel]
  refine congrArg _ ?_
  funext k
  fin_cases k <;> rfl

omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
omit [I.Boundaryless] [SigmaCompactSpace M] in
lemma slotInsert_perturbationSharp_eq_raise_symmS (g₀ : SmoothRiemannianMetric I M)
    (T : SmoothCcTensor g₀ 0 2) :
    endoSlotZeroCcTensor (I := I) (M := M) g₀ 0
        (perturbationSharpEndoField (I := I) (M := M) g₀ T) =
      cometricRaiseSlot0Field (I := I) (M := M) g₀ 0
        (domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 2) 1)
          (symmS (I := I) (M := M) g₀ T)) := by
  classical
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  apply ContinuousLinearMap.ext
  intro om
  apply Tensor0SSpace.toModel_injective
  apply ContinuousMultilinearMap.ext
  intro w
  have hLHS : Tensor0SSpace.toModel
      ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 1 I x from
        (slotInsertEndoCc (I := I) (M := M) g₀ 0
          (perturbationSharpEndoField (I := I) (M := M) g₀ T)).toSection x) om) w =
      ccTensorBilinSymm (I := I) g₀ T x
        ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm (w 0))
        (inverseMetricSharpFib (I := I) g₀ x om) := by
    rw [show ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 1 I x from
          (slotInsertEndoCc (I := I) (M := M) g₀ 0
            (perturbationSharpEndoField (I := I) (M := M) g₀ T)).toSection x) om) =
        slotInsertEndoFib (I := I) (M := M) 1 0 x
          (perturbationSharpEndoField (I := I) (M := M) g₀ T x) om from rfl]
    rw [slotInsertEndoFib_apply_eval]
    rw [toModel_om_single_eq_cotangentToDual (I := I) (M := M) x om
      (Function.update w 0
        (tangentLinearMapToModel
          (perturbationSharpEndoField (I := I) (M := M) g₀ T x) (w 0)))]
    rw [Function.update_self, tangentLinearMapToModel_apply,
      ContinuousLinearEquiv.symm_apply_apply]
    rw [show (perturbationSharpEndoField (I := I) (M := M) g₀ T x) =
        perturbationSharpEndoFib (I := I) (M := M) g₀ T x from rfl]
    rw [cotangentToDual_eq_inner_sharp (I := I) (M := M) g₀ x om
      (perturbationSharpEndoFib (I := I) (M := M) g₀ T x
        ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm (w 0)))]
    rw [inner_perturbationSharpEndoFib]
  rw [hLHS]
  rw [show ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 1 I x from
        (cometricRaiseSlot0Field (I := I) (M := M) g₀ 0
          (domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 2) 1)
            (symmS (I := I) (M := M) g₀ T))).toSection x) om) =
      ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 1 I x from
        cometricRaiseSlot0Fib g₀ 0 x
          ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from
            (domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 2) 1)
              (symmS (I := I) (M := M) g₀ T)).toSection x)
            (unitTensor (I := I) (M := M) x))) om) from rfl]
  rw [cometricRaiseSlot0Fib_clm_apply (I := I) g₀ 0 x _ om]
  rw [interiorProduct_toModel_eval_pal (I := I) (M := M) 1 x
    (inverseMetricSharpFib (I := I) g₀ x om) _ w]
  rw [show Tensor0SSpace.toModel
      ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from
        (domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 2) 1)
          (symmS (I := I) (M := M) g₀ T)).toSection x)
        (unitTensor (I := I) (M := M) x)) =
      unitModel (I := I) (M := M) g₀ 2
        (domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 2) 1)
          (symmS (I := I) (M := M) g₀ T)) x from rfl]
  rw [domDomCongrSection_unitModel (I := I) g₀ (Equiv.swap (0 : Fin 2) 1)
    (symmS (I := I) (M := M) g₀ T) x]
  rw [ContinuousMultilinearMap.domDomCongr_apply]
  rw [show (fun i : Fin 2 =>
      (Fin.cons (tangentSpaceModelContinuousLinearEquiv (I := I) x
          (inverseMetricSharpFib (I := I) g₀ x om)) w : Fin 2 → E)
        ((Equiv.swap (0 : Fin 2) 1) i)) =
      (![w 0, tangentSpaceModelContinuousLinearEquiv (I := I) x
          (inverseMetricSharpFib (I := I) g₀ x om)] : Fin 2 → E) from by
    funext i
    fin_cases i <;> rfl]
  have hunit : unitModel (I := I) (M := M) g₀ 2
      (symmS (I := I) (M := M) g₀ T) x
      (![w 0, tangentSpaceModelContinuousLinearEquiv (I := I) x
        (inverseMetricSharpFib (I := I) g₀ x om)] : Fin 2 → E) =
      ccTensorBilin (I := I) g₀ (symmS (I := I) (M := M) g₀ T) x
        ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm (w 0))
        (inverseMetricSharpFib (I := I) g₀ x om) := by
    rw [ccTensorBilin_apply, ccTensorModel]
    rw [show ccTensorMultilinear (I := I) g₀ (symmS (I := I) (M := M) g₀ T) x =
        (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from
          (symmS (I := I) (M := M) g₀ T).toSection x)
          (unitZeroSec (I := I) (M := M) x) from rfl]
    rw [unitModel]
    rfl
  rw [hunit]
  rw [ccTensorBilin_symmS (I := I) (M := M) g₀ T x]

omit [NeZero (Module.finrank ℝ E)] in
omit [I.Boundaryless] [SigmaCompactSpace M] in
lemma riemannG1LoweringDifference_slotInsert_repr (g₀ g₁ : SmoothRiemannianMetric I M)
    (T : SmoothCcTensor g₀ 0 2)
    (htie : ∀ (y : M) (v w : TangentSpace I y),
      g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ T y v w) :
    riemannLoweredCc (I := I) (M := M) g₀ g₁ g₁ - riemannLoweredCc (I := I) (M := M) g₀ g₀ g₁ =
      domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 4) 1)
        (ccOperatorFieldComp (I := I) (M := M) g₀ 0 4 4
          (slotInsertEndoCc (I := I) (M := M) g₀ 3
            (perturbationSharpEndoField (I := I) (M := M) g₀ T))
          (domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 4) 1)
            (riemannLoweredCc (I := I) (M := M) g₀ g₀ g₁))) := by
  classical
  apply smoothCcTensor_ext_of_unitModel (I := I) (M := M) g₀
  intro x
  apply ContinuousMultilinearMap.ext
  intro m
  let mt : Fin 4 → TangentSpace I x :=
    fun i => (tangentSpaceModelContinuousLinearEquiv (I := I) x).symm (m i)
  have hLHS : unitModel (I := I) (M := M) g₀ 4
      (riemannLoweredCc (I := I) (M := M) g₀ g₁ g₁ -
        riemannLoweredCc (I := I) (M := M) g₀ g₀ g₁) x m =
      ccTensorBilinSymm (I := I) g₀ T x
        (riemannOp (LeviCivita (I := I) g₁) x (mt 0) (mt 2) (mt 3)) (mt 1) := by
    have hsub : unitModel (I := I) (M := M) g₀ 4
        (riemannLoweredCc (I := I) (M := M) g₀ g₁ g₁ -
          riemannLoweredCc (I := I) (M := M) g₀ g₀ g₁) x m =
        unitModel (I := I) (M := M) g₀ 4
            (riemannLoweredCc (I := I) (M := M) g₀ g₁ g₁) x m -
          unitModel (I := I) (M := M) g₀ 4
            (riemannLoweredCc (I := I) (M := M) g₀ g₀ g₁) x m := by
      rw [unitModel, unitModel, unitModel]
      rw [show ((riemannLoweredCc (I := I) (M := M) g₀ g₁ g₁ -
            riemannLoweredCc (I := I) (M := M) g₀ g₀ g₁).toSection x) =
          (riemannLoweredCc (I := I) (M := M) g₀ g₁ g₁).toSection x -
            (riemannLoweredCc (I := I) (M := M) g₀ g₀ g₁).toSection x from by
        rw [SmoothCcTensor.toSection_sub]; rfl]
      rw [sub_apply, Tensor0SSpace.toModel_sub,
        sub_apply]
    rw [hsub]
    rw [riemannLoweredCc_unitModel_apply (I := I) (M := M) g₀ g₁ g₁ x m]
    rw [riemannLoweredCc_unitModel_apply (I := I) (M := M) g₀ g₀ g₁ x m]
    rw [htie x (riemannOp (LeviCivita (I := I) g₁) x (mt 0) (mt 2) (mt 3)) (mt 1)]
    ring
  rw [hLHS]
  rw [domDomCongrSection_unitModel (I := I) g₀ (Equiv.swap (0 : Fin 4) 1)
    (ccOperatorFieldComp (I := I) (M := M) g₀ 0 4 4
      (slotInsertEndoCc (I := I) (M := M) g₀ 3
        (perturbationSharpEndoField (I := I) (M := M) g₀ T))
      (domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 4) 1)
        (riemannLoweredCc (I := I) (M := M) g₀ g₀ g₁))) x]
  rw [ContinuousMultilinearMap.domDomCongr_apply]
  have happ : unitModel (I := I) (M := M) g₀ 4
      (ccOperatorFieldComp (I := I) (M := M) g₀ 0 4 4
        (slotInsertEndoCc (I := I) (M := M) g₀ 3
          (perturbationSharpEndoField (I := I) (M := M) g₀ T))
        (domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 4) 1)
          (riemannLoweredCc (I := I) (M := M) g₀ g₀ g₁))) x
      (fun i => m ((Equiv.swap (0 : Fin 4) 1) i)) =
      unitModel (I := I) (M := M) g₀ 4
        (domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 4) 1)
          (riemannLoweredCc (I := I) (M := M) g₀ g₀ g₁)) x
        (Function.update (fun i => m ((Equiv.swap (0 : Fin 4) 1) i)) 0
          (tangentLinearMapToModel
            (perturbationSharpEndoField (I := I) (M := M) g₀ T x)
            ((fun i => m ((Equiv.swap (0 : Fin 4) 1) i)) 0))) := by
    rw [unitModel, unitModel]
    rw [show ((ccOperatorFieldComp (I := I) (M := M) g₀ 0 4 4
        (slotInsertEndoCc (I := I) (M := M) g₀ 3
          (perturbationSharpEndoField (I := I) (M := M) g₀ T))
        (domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 4) 1)
          (riemannLoweredCc (I := I) (M := M) g₀ g₀ g₁))).toSection x)
        (unitTensor (I := I) (M := M) x) =
      slotInsertEndoFib (I := I) (M := M) 4 0 x
        (perturbationSharpEndoField (I := I) (M := M) g₀ T x)
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 4 I x from
          (domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 4) 1)
            (riemannLoweredCc (I := I) (M := M) g₀ g₀ g₁)).toSection x)
          (unitTensor (I := I) (M := M) x)) from by
      rw [operatorFieldComposition_toSection]
      rfl]
    rw [slotInsertEndoFib_apply_eval]
  rw [happ]
  rw [domDomCongrSection_unitModel (I := I) g₀ (Equiv.swap (0 : Fin 4) 1)
    (riemannLoweredCc (I := I) (M := M) g₀ g₀ g₁) x]
  rw [ContinuousMultilinearMap.domDomCongr_apply]
  rw [show (fun i : Fin 4 =>
      (Function.update (fun i' => m ((Equiv.swap (0 : Fin 4) 1) i')) 0
        (tangentLinearMapToModel
          (perturbationSharpEndoField (I := I) (M := M) g₀ T x)
          ((fun i' => m ((Equiv.swap (0 : Fin 4) 1) i')) 0)))
        ((Equiv.swap (0 : Fin 4) 1) i)) =
      (![m 0, tangentLinearMapToModel
          (perturbationSharpEndoFib (I := I) (M := M) g₀ T x) (m 1),
        m 2, m 3] : Fin 4 → E) from by
    funext i
    fin_cases i
    · change (Function.update (fun i' => m ((Equiv.swap (0 : Fin 4) 1) i')) 0
          (tangentLinearMapToModel
            (perturbationSharpEndoField (I := I) (M := M) g₀ T x)
            (m ((Equiv.swap (0 : Fin 4) 1) 0)))) ((Equiv.swap (0 : Fin 4) 1) 0) = m 0
      rw [show ((Equiv.swap (0 : Fin 4) 1) 0) = (1 : Fin 4) from by decide]
      rw [Function.update_of_ne (by decide : (1 : Fin 4) ≠ 0)]
      rw [show ((Equiv.swap (0 : Fin 4) 1) 1) = (0 : Fin 4) from by decide]
    · change (Function.update (fun i' => m ((Equiv.swap (0 : Fin 4) 1) i')) 0
          (tangentLinearMapToModel
            (perturbationSharpEndoField (I := I) (M := M) g₀ T x)
            (m ((Equiv.swap (0 : Fin 4) 1) 0)))) ((Equiv.swap (0 : Fin 4) 1) 1) =
        tangentLinearMapToModel
          (perturbationSharpEndoFib (I := I) (M := M) g₀ T x) (m 1)
      rw [show ((Equiv.swap (0 : Fin 4) 1) 1) = (0 : Fin 4) from by decide]
      rw [Function.update_self]
      rw [show ((Equiv.swap (0 : Fin 4) 1) 0) = (1 : Fin 4) from by decide]
      rfl
    · change (Function.update (fun i' => m ((Equiv.swap (0 : Fin 4) 1) i')) 0
          (tangentLinearMapToModel
            (perturbationSharpEndoField (I := I) (M := M) g₀ T x)
            (m ((Equiv.swap (0 : Fin 4) 1) 0)))) ((Equiv.swap (0 : Fin 4) 1) 2) = m 2
      rw [show ((Equiv.swap (0 : Fin 4) 1) 2) = (2 : Fin 4) from by decide]
      rw [Function.update_of_ne (by decide : (2 : Fin 4) ≠ 0)]
      rw [show ((Equiv.swap (0 : Fin 4) 1) 2) = (2 : Fin 4) from by decide]
    · change (Function.update (fun i' => m ((Equiv.swap (0 : Fin 4) 1) i')) 0
          (tangentLinearMapToModel
            (perturbationSharpEndoField (I := I) (M := M) g₀ T x)
            (m ((Equiv.swap (0 : Fin 4) 1) 0)))) ((Equiv.swap (0 : Fin 4) 1) 3) = m 3
      rw [show ((Equiv.swap (0 : Fin 4) 1) 3) = (3 : Fin 4) from by decide]
      rw [Function.update_of_ne (by decide : (3 : Fin 4) ≠ 0)]
      rw [show ((Equiv.swap (0 : Fin 4) 1) 3) = (3 : Fin 4) from by decide]]
  rw [riemannLoweredCc_unitModel_apply (I := I) (M := M) g₀ g₀ g₁ x]
  rw [show (![m 0, tangentLinearMapToModel
      (perturbationSharpEndoFib (I := I) (M := M) g₀ T x) (m 1),
    m 2, m 3] : Fin 4 → E) 0 = m 0 from rfl]
  rw [show (![m 0, tangentLinearMapToModel
      (perturbationSharpEndoFib (I := I) (M := M) g₀ T x) (m 1),
    m 2, m 3] : Fin 4 → E) 1 = tangentLinearMapToModel
      (perturbationSharpEndoFib (I := I) (M := M) g₀ T x) (m 1) from rfl]
  rw [show (![m 0, tangentLinearMapToModel
      (perturbationSharpEndoFib (I := I) (M := M) g₀ T x) (m 1),
    m 2, m 3] : Fin 4 → E) 2 = m 2 from rfl]
  rw [show (![m 0, tangentLinearMapToModel
      (perturbationSharpEndoFib (I := I) (M := M) g₀ T x) (m 1),
    m 2, m 3] : Fin 4 → E) 3 = m 3 from rfl]
  simp only [tangentLinearMapToModel_apply, ContinuousLinearEquiv.symm_apply_apply]
  rw [g₀.symm x (riemannOp (LeviCivita (I := I) g₁) x (mt 0) (mt 2) (mt 3))
    (perturbationSharpEndoFib (I := I) (M := M) g₀ T x (mt 1))]
  rw [inner_perturbationSharpEndoFib (I := I) (M := M) g₀ T x (mt 1)
    (riemannOp (LeviCivita (I := I) g₁) x (mt 0) (mt 2) (mt 3))]
  rw [ccTensorBilinSymm_symm (I := I) g₀ T x (mt 1)
    (riemannOp (LeviCivita (I := I) g₁) x (mt 0) (mt 2) (mt 3))]

omit [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
lemma riemannianFiberNormSq_eq_sum_componentSq_of_horth_pt
    (g₀ : SmoothRiemannianMetric I M) (r s : ℕ) (x : M) (S : TensorRSSpace r s I x)
    {n : ℕ} (e : Fin n → TangentSpace I x) (hn : n = Module.finrank ℝ E)
    (horth : ∀ a b : Fin n, g₀.inner x (e a) (e b) = if a = b then (1 : ℝ) else 0) :
    riemannianFiberNormSq (I := I) (M := M) g₀ r s x S =
      ∑ K : Fin r → Fin n, ∑ J : Fin s → Fin n,
        (fiberNormSqComponent (I := I) (M := M) g₀ x r s S n e K J) ^ 2 := by
  classical
  have : Nonempty (Fin n) := by
    rw [hn]
    exact ⟨⟨0, Nat.pos_of_ne_zero (NeZero.ne (Module.finrank ℝ E))⟩⟩
  have he_li : LinearIndependent ℝ e := by
    rw [linearIndependent_iff']
    intro fs c hsum k hk_mem
    have h_zero : g₀.inner x (e k) (∑ j ∈ fs, c j • e j) = 0 := by rw [hsum]; simp
    rw [map_sum] at h_zero
    have h_pull : ∀ j ∈ fs, g₀.inner x (e k) (c j • e j) =
        c j * (if k = j then (1 : ℝ) else 0) := by
      intro j _
      rw [map_smul, horth k j, smul_eq_mul]
    rw [Finset.sum_congr rfl h_pull] at h_zero
    rw [Finset.sum_eq_single k (fun j _ hj => by rw [if_neg (Ne.symm hj), mul_zero])
      (fun hk => absurd hk_mem hk)] at h_zero
    rwa [if_pos rfl, mul_one] at h_zero
  have hrank : Module.finrank ℝ (TangentSpace I x) = Module.finrank ℝ E := rfl
  have hcard : Fintype.card (Fin n) = Module.finrank ℝ (TangentSpace I x) := by
    rw [Fintype.card_fin, hrank]; exact hn
  set bse := basisOfLinearIndependentOfCardEqFinrank he_li hcard with hbse_def
  have hbse : ∀ i : Fin n, bse i = e i := by
    intro i; rw [hbse_def, coe_basisOfLinearIndependentOfCardEqFinrank]
  exact riemannianFiberNormSq_eq_sum_componentSq_of_basis
    (I := I) (M := M) g₀ r s x S e bse hn hbse horth

omit [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
lemma fiberNormSqComponent_zero_toModel_pt
    (g₀ : SmoothRiemannianMetric I M) (s : ℕ) (x : M) (S : SmoothCcTensor g₀ 0 s)
    {n : ℕ} (e : Fin n → TangentSpace I x) (K : Fin 0 → Fin n) (L : Fin s → Fin n) :
    fiberNormSqComponent (I := I) (M := M) g₀ x 0 s (S.toSection x) n e K L =
      Tensor0SSpace.toModel
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from S.toSection x)
          (unitTensor (I := I) (M := M) x))
        (fun k => (show E from e (L k))) := by
  rw [show fiberNormSqComponent (I := I) (M := M) g₀ x 0 s (S.toSection x) n e K L =
      (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from S.toSection x)
        (coframeS (I := I) (M := M) g₀ x 0 e K) (fun k => e (L k)) from rfl]
  rw [coframeS_zero_eq_unitZeroSec (I := I) (M := M) g₀ x e K]
  rfl

omit [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
lemma riemannianFiberNormSq_symmS_zero_le_of_ball (g₀ : SmoothRiemannianMetric I M)
    (T : SmoothCcTensor g₀ 0 2) {δ : ℝ} (hδ0 : 0 ≤ δ)
    (hbound : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x
        ((symmS (I := I) (M := M) g₀ T).toSection x) ≤
      (Module.finrank ℝ E : ℝ) ^ 2 * δ ^ 2 := by
  classical
  obtain ⟨n, e, bse, hn, hbse, horth, _hpars, _hrepr, _hsum⟩ :=
    tangent_orthonormalBasis_witness (I := I) (M := M) g₀ x
  have hnE : n = Module.finrank ℝ E := by rw [hn]; rfl
  rw [riemannianFiberNormSq_eq_sum_componentSq_of_horth_pt (I := I) (M := M) g₀ 0 2 x
    ((symmS (I := I) (M := M) g₀ T).toSection x) e hnE horth]
  have hcomp : ∀ (K : Fin 0 → Fin n) (J : Fin 2 → Fin n),
      (fiberNormSqComponent (I := I) (M := M) g₀ x 0 2
        ((symmS (I := I) (M := M) g₀ T).toSection x) n e K J) ^ 2 ≤ δ ^ 2 := by
    intro K J
    have hval : fiberNormSqComponent (I := I) (M := M) g₀ x 0 2
        ((symmS (I := I) (M := M) g₀ T).toSection x) n e K J =
        ccTensorBilinSymm (I := I) g₀ T x (e (J 0)) (e (J 1)) := by
      rw [fiberNormSqComponent_zero_toModel_pt (I := I) (M := M) g₀ 2 x
        (symmS (I := I) (M := M) g₀ T) e K J]
      rw [show Tensor0SSpace.toModel
          ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from
            (symmS (I := I) (M := M) g₀ T).toSection x)
            (unitTensor (I := I) (M := M) x))
          (fun k => (show E from e (J k))) =
          unitModel (I := I) (M := M) g₀ 2 (symmS (I := I) (M := M) g₀ T) x
            ![e (J 0), e (J 1)] from by
        rw [unitModel]
        refine congrArg _ ?_
        funext k
        fin_cases k <;> rfl]
      rw [unitModel_eq_ccTensorBilin_pt (I := I) (M := M) g₀
        (symmS (I := I) (M := M) g₀ T) x (e (J 0)) (e (J 1))]
      rw [ccTensorBilin_symmS (I := I) (M := M) g₀ T x (e (J 0)) (e (J 1))]
    rw [hval]
    have habs := hbound x (e (J 0)) (e (J 1))
    have h00 : g₀.inner x (e (J 0)) (e (J 0)) = 1 := by
      rw [horth (J 0) (J 0), if_pos rfl]
    have h11 : g₀.inner x (e (J 1)) (e (J 1)) = 1 := by
      rw [horth (J 1) (J 1), if_pos rfl]
    rw [h00, h11, Real.sqrt_one, mul_one, mul_one] at habs
    have := abs_nonneg (ccTensorBilinSymm (I := I) g₀ T x (e (J 0)) (e (J 1)))
    nlinarith [habs, sq_abs (ccTensorBilinSymm (I := I) g₀ T x (e (J 0)) (e (J 1)))]
  calc (∑ K : Fin 0 → Fin n, ∑ J : Fin 2 → Fin n,
        (fiberNormSqComponent (I := I) (M := M) g₀ x 0 2
          ((symmS (I := I) (M := M) g₀ T).toSection x) n e K J) ^ 2)
      ≤ ∑ K : Fin 0 → Fin n, ∑ J : Fin 2 → Fin n, δ ^ 2 :=
        Finset.sum_le_sum fun K _ => Finset.sum_le_sum fun J _ => hcomp K J
    _ = (Fintype.card (Fin 0 → Fin n) : ℝ) * ((Fintype.card (Fin 2 → Fin n) : ℝ) * δ ^ 2) := by
        rw [Finset.sum_const, Finset.sum_const]
        simp only [Finset.card_univ, nsmul_eq_mul]
    _ ≤ (Module.finrank ℝ E : ℝ) ^ 2 * δ ^ 2 := by
        have hc0 : (Fintype.card (Fin 0 → Fin n) : ℝ) = 1 := by
          simp
        have hc2 : (Fintype.card (Fin 2 → Fin n) : ℝ) = (n : ℝ) ^ 2 := by
          simp only [Fintype.card_fun, Fintype.card_fin]
          push_cast
          ring
        rw [hc0, hc2, one_mul, hnE]

omit [SigmaCompactSpace M] in
lemma riemannianFiberNormSq_iteratedCovGrad_slotInsert3_perturbationSharp_le
    (g₀ : SmoothRiemannianMetric I M) (T : SmoothCcTensor g₀ 0 2) (j : ℕ) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g₀ 4 (4 + j) x
        ((iteratedCovGrad (I := I) g₀ 4 4 j
          (slotInsertEndoCc (I := I) (M := M) g₀ 3
            (perturbationSharpEndoField (I := I) (M := M) g₀ T))).toSection x) ≤
      (Module.finrank ℝ E : ℝ) ^ 3 *
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x
          ((iteratedCovGrad (I := I) g₀ 0 2 j (symmS (I := I) (M := M) g₀ T)).toSection x) := by
  refine le_trans (riemannianFiberNormSq_iteratedCovGrad_slotInsertEndoCc_le_endo (I := I) (M := M) g₀ 3
    (perturbationSharpEndoField (I := I) (M := M) g₀ T) j x) ?_
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  rw [slotInsert_perturbationSharp_eq_raise_symmS (I := I) (M := M) g₀ T]
  rw [riemannianFiberNormSq_iteratedCovGrad_cometricRaiseSlot0Field_eq (I := I) (M := M) g₀ 0
    (domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 2) 1)
      (symmS (I := I) (M := M) g₀ T)) j x]
  rw [riemannianFiberNormSq_iteratedCovGrad_domDomCongrSection (I := I) (M := M) g₀
    (Equiv.swap (0 : Fin 2) 1) (symmS (I := I) (M := M) g₀ T) j x]

end CurvatureCoefficientDifferenceJetTower

omit [SigmaCompactSpace M] in
theorem riemannianFiberNormSq_iteratedCovGrad_riemannLoweredBackgroundDifference_diagonalProductGrid_le
    (g₀ : SmoothRiemannianMetric I M) {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ C : ℕ → ℝ, (∀ i, 0 ≤ C i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (T : SmoothCcTensor g₀ 0 2)
        (_htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ T y v w)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀) (_hδ0 : 0 ≤ δ)
        (_hbound : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        (i : ℕ) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + i) x
            ((iteratedCovGrad (I := I) g₀ 0 4 i
              (riemannLoweredBackgroundDifference (I := I) (M := M) g₀ g₁)).toSection x) ≤
          C i * ∑ k ∈ Finset.range (i + 3),
            ∑ n ∈ Finset.range (k + 1),
              ∑ e ∈ Finset.Nat.antidiagonalTuple n k,
                ∏ m : Fin n,
                  riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
                    ((iteratedCovGrad (I := I) g₀ 0 2 (e m) T).toSection x) := by
  classical
  obtain ⟨CA, hCA_nn, hCA⟩ := exists_riemannianFiberNormSq_iteratedCovGrad_connectionDifferenceSection_tgrid
    (I := I) (M := M) g₀ hδ₀
  set AA : ℕ → ℕ → ℝ := fun i i' => ∑ l ∈ Finset.range (i + 1 - i'),
    CA i' * CA l * gridSumPairCount (i' + 2) (l + 2) with hAA_def
  have hAA_nn : ∀ i i', 0 ≤ AA i i' := by
    intro i i'
    rw [hAA_def]
    exact Finset.sum_nonneg fun l _ =>
      mul_nonneg (mul_nonneg (hCA_nn i') (hCA_nn l)) (gridSumPairCount_nonneg _ _)
  clear_value AA
  refine ⟨fun i => 8 * CA (i + 1) + 8 * (operatorFieldApplicationGdiag (E := E) i *
      ∑ i' ∈ Finset.range (i + 1), (Module.finrank ℝ E : ℝ) * AA i i'),
    fun i => by
      have h1 : 0 ≤ ∑ i' ∈ Finset.range (i + 1), (Module.finrank ℝ E : ℝ) * AA i i' :=
        Finset.sum_nonneg fun i' _ => mul_nonneg (Nat.cast_nonneg _) (hAA_nn i i')
      have h2 := operatorFieldApplicationGdiag_nonneg (E := E) i
      have h4 := hCA_nn (i + 1)
      positivity, ?_⟩
  intro g₁ T htie δ hδ_le hδ0 hbound i x
  set b : ℕ → ℝ := fun j => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x
    ((iteratedCovGrad (I := I) g₀ 0 2 j T).toSection x) with hb_def
  have hb : ∀ j, 0 ≤ b j :=
    fun j => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + j) x _
  have hgoal_eq : (∑ k ∈ Finset.range (i + 3),
      ∑ n ∈ Finset.range (k + 1),
        ∑ e ∈ Finset.Nat.antidiagonalTuple n k,
          ∏ m : Fin n, b (e m)) =
      ∑ k ∈ Finset.range (i + 3), Combinatorics.antidiagonalTupleGrid b k := rfl
  rw [hgoal_eq]
  set WW : ℝ := ∑ k ∈ Finset.range (i + 3), Combinatorics.antidiagonalTupleGrid b k
    with hWW_def
  have hWW_nn : 0 ≤ WW := by
    rw [hWW_def]
    exact Finset.sum_nonneg fun k _ => Combinatorics.antidiagonalTupleGrid_nonneg b hb k
  have hgsum_le_WW : ∀ m : ℕ, m ≤ i + 3 →
      (∑ k ∈ Finset.range m, Combinatorics.antidiagonalTupleGrid b k) ≤ WW := by
    intro m hm
    rw [hWW_def]
    refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.mpr hm) ?_
    intro k _ _
    exact Combinatorics.antidiagonalTupleGrid_nonneg b hb k
  clear_value WW
  have hstep1 : riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + i) x
      ((iteratedCovGrad (I := I) g₀ 0 4 i
        (riemannLoweredBackgroundDifference (I := I) (M := M) g₀ g₁)).toSection x) =
      riemannianFiberNormSq (I := I) (M := M) g₀ 1 (3 + i) x
        ((iteratedCovGrad (I := I) g₀ 1 3 i
          (cometricRaiseSlot0Field (I := I) (M := M) g₀ 2
            (domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 4) 1)
              (riemannLoweredBackgroundDifference (I := I) (M := M) g₀ g₁)))).toSection x) := by
    rw [riemannianFiberNormSq_iteratedCovGrad_cometricRaiseSlot0Field_eq (I := I) (M := M) g₀ 2
      (domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 4) 1)
        (riemannLoweredBackgroundDifference (I := I) (M := M) g₀ g₁)) i x]
    rw [riemannianFiberNormSq_iteratedCovGrad_domDomCongrSection (I := I) (M := M) g₀
      (Equiv.swap (0 : Fin 4) 1)
      (riemannLoweredBackgroundDifference (I := I) (M := M) g₀ g₁) i x]
  rw [hstep1]
  rw [riemannLoweredBackgroundDifference_palatini_repr (I := I) (M := M) g₀ g₁]
  set DQ : SmoothCcTensor g₀ 1 3 :=
    covGrad (I := I) (M := M) g₀ 1 2 (connectionDifferenceSection (I := I) g₁ g₀) +
      quadraticConnectionDifferenceCc (I := I) (M := M) g₀ g₁ with hDQ_def
  have hrs_eq : ∀ σ : Equiv.Perm (Fin 3),
      riemannianFiberNormSq (I := I) (M := M) g₀ 1 (3 + i) x
        ((iteratedCovGrad (I := I) g₀ 1 3 i
          (rsDomDomCongrSection (I := I) (M := M) g₀ 1 3 σ DQ)).toSection x) =
      riemannianFiberNormSq (I := I) (M := M) g₀ 1 (3 + i) x
        ((iteratedCovGrad (I := I) g₀ 1 3 i DQ).toSection x) := by
    intro σ
    exact riemannianFiberNormSq_iteratedCovGrad_rs_eq_of_section_domDomCongr (I := I) (M := M) g₀ 1 3 σ DQ
      (rsDomDomCongrSection (I := I) (M := M) g₀ 1 3 σ DQ)
      (fun y d => by
        rw [rsDomDomCongrSection_toSection, toModel_rsDomDomCongr_apply]) i x
  have hsubsec : (iteratedCovGrad (I := I) g₀ 1 3 i
      (rsDomDomCongrSection (I := I) (M := M) g₀ 1 3 (Equiv.swap (1 : Fin 3) 2) DQ -
        rsDomDomCongrSection (I := I) (M := M) g₀ 1 3 (finRotate 3) DQ)).toSection x =
      (iteratedCovGrad (I := I) g₀ 1 3 i
        (rsDomDomCongrSection (I := I) (M := M) g₀ 1 3 (Equiv.swap (1 : Fin 3) 2) DQ)).toSection x +
      (- (iteratedCovGrad (I := I) g₀ 1 3 i
        (rsDomDomCongrSection (I := I) (M := M) g₀ 1 3 (finRotate 3) DQ)).toSection x) := by
    rw [sub_eq_add_neg, iteratedCovGrad_add, iteratedCovGrad_neg,
      SmoothCcTensor.toSection_add]
    rw [show ((iteratedCovGrad (I := I) g₀ 1 3 i
        (rsDomDomCongrSection (I := I) (M := M) g₀ 1 3 (Equiv.swap (1 : Fin 3) 2) DQ)).toSection +
        (- iteratedCovGrad (I := I) g₀ 1 3 i
          (rsDomDomCongrSection (I := I) (M := M) g₀ 1 3 (finRotate 3) DQ)).toSection) x =
      (iteratedCovGrad (I := I) g₀ 1 3 i
        (rsDomDomCongrSection (I := I) (M := M) g₀ 1 3 (Equiv.swap (1 : Fin 3) 2) DQ)).toSection x +
      (- iteratedCovGrad (I := I) g₀ 1 3 i
        (rsDomDomCongrSection (I := I) (M := M) g₀ 1 3 (finRotate 3) DQ)).toSection x from rfl]
    rw [SmoothCcTensor.toSection_neg]
    rfl
  rw [hsubsec]
  refine le_trans (riemannianFiberNormSq_add_le (I := I) (M := M) g₀ 1 (3 + i) x _ _) ?_
  rw [riemannianFiberNormSq_neg_pt (I := I) (M := M) g₀ 1 (3 + i) x]
  rw [hrs_eq (Equiv.swap (1 : Fin 3) 2), hrs_eq (finRotate 3)]
  have hDQsec : (iteratedCovGrad (I := I) g₀ 1 3 i DQ).toSection x =
      (iteratedCovGrad (I := I) g₀ 1 3 i
        (covGrad (I := I) (M := M) g₀ 1 2 (connectionDifferenceSection (I := I) g₁ g₀))).toSection x +
      (iteratedCovGrad (I := I) g₀ 1 3 i
        (quadraticConnectionDifferenceCc (I := I) (M := M) g₀ g₁)).toSection x := by
    rw [hDQ_def, iteratedCovGrad_add, SmoothCcTensor.toSection_add]
    rfl
  have hD_le : riemannianFiberNormSq (I := I) (M := M) g₀ 1 (3 + i) x
      ((iteratedCovGrad (I := I) g₀ 1 3 i
        (covGrad (I := I) (M := M) g₀ 1 2 (connectionDifferenceSection (I := I) g₁ g₀))).toSection x) ≤
      CA (i + 1) * WW := by
    rw [riemannianFiberNormSq_iteratedCovGrad_covGrad_comm_rs (I := I) (M := M) g₀ 1 2 i
      (connectionDifferenceSection (I := I) g₁ g₀) x]
    refine le_trans (hCA g₁ T htie hδ_le hδ0 hbound (i + 1) x) ?_
    exact mul_le_mul_of_nonneg_left (hgsum_le_WW (i + 3) (le_refl _)) (hCA_nn (i + 1))
  have hcell : ∀ i' ∈ Finset.range (i + 1),
      riemannianFiberNormSq (I := I) (M := M) g₀ 2 (3 + i') x
          ((iteratedCovGrad (I := I) g₀ 2 3 i'
            (termSlotEndoPassZeroCc (I := I) (M := M) g₀
              (connectionDifferenceTermFieldPt (I := I) (M := M) g₀ g₁))).toSection x) *
        ∑ l ∈ Finset.range (i + 1 - i'),
          riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + l) x
            ((iteratedCovGrad (I := I) g₀ 1 2 l
              (connectionDifferenceSection (I := I) g₁ g₀)).toSection x) ≤
      ((Module.finrank ℝ E : ℝ) * AA i i') * WW := by
    intro i' hi'
    have hi'le : i' ≤ i := by
      rw [Finset.mem_range] at hi'; omega
    have hA1 : riemannianFiberNormSq (I := I) (M := M) g₀ 2 (3 + i') x
        ((iteratedCovGrad (I := I) g₀ 2 3 i'
          (termSlotEndoPassZeroCc (I := I) (M := M) g₀
            (connectionDifferenceTermFieldPt (I := I) (M := M) g₀ g₁))).toSection x) ≤
        (Module.finrank ℝ E : ℝ) *
          (CA i' * ∑ k ∈ Finset.range (i' + 2), Combinatorics.antidiagonalTupleGrid b k) := by
      refine le_trans (riemannianFiberNormSq_iteratedCovGrad_termSlotPass_connectionDifferenceTerm_le
        (I := I) (M := M) g₀ g₁ i' x) ?_
      refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
      exact hCA g₁ T htie hδ_le hδ0 hbound i' x
    have hA2 : (∑ l ∈ Finset.range (i + 1 - i'),
        riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + l) x
          ((iteratedCovGrad (I := I) g₀ 1 2 l
            (connectionDifferenceSection (I := I) g₁ g₀)).toSection x)) ≤
        ∑ l ∈ Finset.range (i + 1 - i'),
          CA l * ∑ k ∈ Finset.range (l + 2), Combinatorics.antidiagonalTupleGrid b k :=
      Finset.sum_le_sum fun l _ => hCA g₁ T htie hδ_le hδ0 hbound l x
    have hprod_nn1 : 0 ≤ ∑ l ∈ Finset.range (i + 1 - i'),
        riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + l) x
          ((iteratedCovGrad (I := I) g₀ 1 2 l
            (connectionDifferenceSection (I := I) g₁ g₀)).toSection x) :=
      Finset.sum_nonneg fun l _ =>
        riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 1 (2 + l) x _
    have hfr_nn : (0 : ℝ) ≤ (Module.finrank ℝ E : ℝ) := Nat.cast_nonneg _
    have hgsA_nn : 0 ≤ CA i' * ∑ k ∈ Finset.range (i' + 2),
        Combinatorics.antidiagonalTupleGrid b k :=
      mul_nonneg (hCA_nn i') (Finset.sum_nonneg fun k _ =>
        Combinatorics.antidiagonalTupleGrid_nonneg b hb k)
    have hpairsum : ∀ l ∈ Finset.range (i + 1 - i'),
        (CA i' * ∑ k ∈ Finset.range (i' + 2), Combinatorics.antidiagonalTupleGrid b k) *
          (CA l * ∑ k ∈ Finset.range (l + 2), Combinatorics.antidiagonalTupleGrid b k) ≤
        (CA i' * CA l * gridSumPairCount (i' + 2) (l + 2)) * WW := by
      intro l hl
      have hl_le : l ≤ i - i' := by
        rw [Finset.mem_range] at hl; omega
      have hgs := gridSum_mul_gridSum_le b hb (i' + 2) (l + 2) (i + 3) (by omega)
      calc (CA i' * ∑ k ∈ Finset.range (i' + 2), Combinatorics.antidiagonalTupleGrid b k) *
            (CA l * ∑ k ∈ Finset.range (l + 2), Combinatorics.antidiagonalTupleGrid b k)
          = (CA i' * CA l) *
              ((∑ k ∈ Finset.range (i' + 2), Combinatorics.antidiagonalTupleGrid b k) *
                (∑ k ∈ Finset.range (l + 2), Combinatorics.antidiagonalTupleGrid b k)) := by
            ring
        _ ≤ (CA i' * CA l) * (gridSumPairCount (i' + 2) (l + 2) *
              (∑ k ∈ Finset.range (i + 3), Combinatorics.antidiagonalTupleGrid b k)) := by
            refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg (hCA_nn i') (hCA_nn l))
            exact hgs
        _ ≤ (CA i' * CA l) * (gridSumPairCount (i' + 2) (l + 2) * WW) := by
            refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg (hCA_nn i') (hCA_nn l))
            refine mul_le_mul_of_nonneg_left ?_ (gridSumPairCount_nonneg _ _)
            exact hgsum_le_WW (i + 3) (le_refl _)
        _ = (CA i' * CA l * gridSumPairCount (i' + 2) (l + 2)) * WW := by ring
    calc riemannianFiberNormSq (I := I) (M := M) g₀ 2 (3 + i') x
          ((iteratedCovGrad (I := I) g₀ 2 3 i'
            (termSlotEndoPassZeroCc (I := I) (M := M) g₀
              (connectionDifferenceTermFieldPt (I := I) (M := M) g₀ g₁))).toSection x) *
        ∑ l ∈ Finset.range (i + 1 - i'),
          riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + l) x
            ((iteratedCovGrad (I := I) g₀ 1 2 l
              (connectionDifferenceSection (I := I) g₁ g₀)).toSection x)
        ≤ ((Module.finrank ℝ E : ℝ) *
            (CA i' * ∑ k ∈ Finset.range (i' + 2), Combinatorics.antidiagonalTupleGrid b k)) *
          ∑ l ∈ Finset.range (i + 1 - i'),
            CA l * ∑ k ∈ Finset.range (l + 2), Combinatorics.antidiagonalTupleGrid b k :=
          mul_le_mul hA1 hA2 hprod_nn1 (mul_nonneg hfr_nn hgsA_nn)
      _ = (Module.finrank ℝ E : ℝ) *
          ∑ l ∈ Finset.range (i + 1 - i'),
            (CA i' * ∑ k ∈ Finset.range (i' + 2), Combinatorics.antidiagonalTupleGrid b k) *
              (CA l * ∑ k ∈ Finset.range (l + 2), Combinatorics.antidiagonalTupleGrid b k) := by
          rw [mul_assoc, Finset.mul_sum]
      _ ≤ (Module.finrank ℝ E : ℝ) *
          ∑ l ∈ Finset.range (i + 1 - i'),
            (CA i' * CA l * gridSumPairCount (i' + 2) (l + 2)) * WW := by
          exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum hpairsum) hfr_nn
      _ = ((Module.finrank ℝ E : ℝ) * AA i i') * WW := by
          have hAAval : AA i i' = ∑ l ∈ Finset.range (i + 1 - i'),
              CA i' * CA l * gridSumPairCount (i' + 2) (l + 2) := by rw [hAA_def]
          rw [hAAval, ← Finset.sum_mul]
          ring
  have hQ_le : riemannianFiberNormSq (I := I) (M := M) g₀ 1 (3 + i) x
      ((iteratedCovGrad (I := I) g₀ 1 3 i
        (quadraticConnectionDifferenceCc (I := I) (M := M) g₀ g₁)).toSection x) ≤
      (operatorFieldApplicationGdiag (E := E) i *
        ∑ i' ∈ Finset.range (i + 1), (Module.finrank ℝ E : ℝ) * AA i i') * WW := by
    rw [show quadraticConnectionDifferenceCc (I := I) (M := M) g₀ g₁ =
        ccOperatorFieldComp (I := I) (M := M) g₀ 1 2 3
          (termSlotEndoPassZeroCc (I := I) (M := M) g₀
            (connectionDifferenceTermFieldPt (I := I) (M := M) g₀ g₁))
          (connectionDifferenceSection (I := I) g₁ g₀) from rfl]
    refine le_trans (riemannianFiberNormSq_iteratedCovGrad_operatorFieldComposition_diagonalProductGrid_rankLeft_le
      (I := I) (M := M) g₀ i 1 2 3
      (termSlotEndoPassZeroCc (I := I) (M := M) g₀
        (connectionDifferenceTermFieldPt (I := I) (M := M) g₀ g₁))
      (connectionDifferenceSection (I := I) g₁ g₀) x) ?_
    calc operatorFieldApplicationGdiag (E := E) i *
          ∑ i' ∈ Finset.range (i + 1),
            riemannianFiberNormSq (I := I) (M := M) g₀ 2 (3 + i') x
                ((iteratedCovGrad (I := I) g₀ 2 3 i'
                  (termSlotEndoPassZeroCc (I := I) (M := M) g₀
                    (connectionDifferenceTermFieldPt (I := I) (M := M) g₀ g₁))).toSection x) *
              ∑ l ∈ Finset.range (i + 1 - i'),
                riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + l) x
                  ((iteratedCovGrad (I := I) g₀ 1 2 l
                    (connectionDifferenceSection (I := I) g₁ g₀)).toSection x)
        ≤ operatorFieldApplicationGdiag (E := E) i *
            ∑ i' ∈ Finset.range (i + 1), ((Module.finrank ℝ E : ℝ) * AA i i') * WW :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum hcell) (operatorFieldApplicationGdiag_nonneg (E := E) i)
      _ = (operatorFieldApplicationGdiag (E := E) i *
            ∑ i' ∈ Finset.range (i + 1), (Module.finrank ℝ E : ℝ) * AA i i') * WW := by
          rw [← Finset.sum_mul]
          ring
  rw [hDQsec]
  have hsum_le := riemannianFiberNormSq_add_le (I := I) (M := M) g₀ 1 (3 + i) x
    ((iteratedCovGrad (I := I) g₀ 1 3 i
      (covGrad (I := I) (M := M) g₀ 1 2 (connectionDifferenceSection (I := I) g₁ g₀))).toSection x)
    ((iteratedCovGrad (I := I) g₀ 1 3 i
      (quadraticConnectionDifferenceCc (I := I) (M := M) g₀ g₁)).toSection x)
  have hDQfull : riemannianFiberNormSq (I := I) (M := M) g₀ 1 (3 + i) x
      ((iteratedCovGrad (I := I) g₀ 1 3 i
        (covGrad (I := I) (M := M) g₀ 1 2 (connectionDifferenceSection (I := I) g₁ g₀))).toSection x +
      (iteratedCovGrad (I := I) g₀ 1 3 i
        (quadraticConnectionDifferenceCc (I := I) (M := M) g₀ g₁)).toSection x) ≤
      2 * (CA (i + 1) * WW) +
        2 * ((operatorFieldApplicationGdiag (E := E) i *
          ∑ i' ∈ Finset.range (i + 1), (Module.finrank ℝ E : ℝ) * AA i i') * WW) := by
    refine le_trans hsum_le ?_
    linarith [hD_le, hQ_le]
  calc 2 * riemannianFiberNormSq (I := I) (M := M) g₀ 1 (3 + i) x
        ((iteratedCovGrad (I := I) g₀ 1 3 i
          (covGrad (I := I) (M := M) g₀ 1 2 (connectionDifferenceSection (I := I) g₁ g₀))).toSection x +
        (iteratedCovGrad (I := I) g₀ 1 3 i
          (quadraticConnectionDifferenceCc (I := I) (M := M) g₀ g₁)).toSection x) +
      2 * riemannianFiberNormSq (I := I) (M := M) g₀ 1 (3 + i) x
        ((iteratedCovGrad (I := I) g₀ 1 3 i
          (covGrad (I := I) (M := M) g₀ 1 2 (connectionDifferenceSection (I := I) g₁ g₀))).toSection x +
        (iteratedCovGrad (I := I) g₀ 1 3 i
          (quadraticConnectionDifferenceCc (I := I) (M := M) g₀ g₁)).toSection x)
      ≤ 2 * (2 * (CA (i + 1) * WW) +
          2 * ((operatorFieldApplicationGdiag (E := E) i *
            ∑ i' ∈ Finset.range (i + 1), (Module.finrank ℝ E : ℝ) * AA i i') * WW)) +
        2 * (2 * (CA (i + 1) * WW) +
          2 * ((operatorFieldApplicationGdiag (E := E) i *
            ∑ i' ∈ Finset.range (i + 1), (Module.finrank ℝ E : ℝ) * AA i i') * WW)) := by
        linarith [hDQfull]
    _ = (8 * CA (i + 1) + 8 * (operatorFieldApplicationGdiag (E := E) i *
          ∑ i' ∈ Finset.range (i + 1), (Module.finrank ℝ E : ℝ) * AA i i')) * WW := by
        ring

namespace CurvatureCoefficientDifferenceJetTower

omit [CompactSpace M] [I.Boundaryless] in
omit [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
lemma linearMap_trace_eq_orthoFrame_inner_sum (g₀ : SmoothRiemannianMetric I M)
    (x : M) (G : TangentSpace I x →ₗ[ℝ] TangentSpace I x) :
    LinearMap.trace ℝ (TangentSpace I x) G =
      ∑ i : Fin (Module.finrank ℝ E),
        g₀.inner x (G (smoothOrthoFrame (I := I) g₀ x i x))
          (smoothOrthoFrame (I := I) g₀ x i x) := by
  classical
  have : FiniteDimensional ℝ (TangentSpace I x) := inferInstanceAs (FiniteDimensional ℝ E)
  have : Nonempty (Fin (Module.finrank ℝ E)) :=
    ⟨⟨0, Nat.pos_of_ne_zero (NeZero.ne (Module.finrank ℝ E))⟩⟩
  set B : Fin (Module.finrank ℝ E) → TangentSpace I x :=
    fun i => smoothOrthoFrame (I := I) g₀ x i x with hB_def
  have horth : ∀ i j, g₀.inner x (B i) (B j) = if i = j then (1 : ℝ) else 0 :=
    fun i j => smoothOrthoFrame_orthonormal_at_center (I := I) g₀ x i j
  have hlin : LinearIndependent ℝ B := by
    rw [Fintype.linearIndependent_iff]
    intro c hc j
    have hpair : g₀.inner x (∑ i, c i • B i) (B j) = 0 := by
      rw [hc]
      simp
    rw [map_sum, sum_apply] at hpair
    have hsimp : ∀ i, g₀.inner x (c i • B i) (B j) = c i * (if i = j then (1 : ℝ) else 0) := by
      intro i
      rw [map_smul, smul_apply, smul_eq_mul, horth i j]
    rw [Finset.sum_congr rfl (fun i _ => hsimp i)] at hpair
    have hcol : (∑ i, c i * (if i = j then (1 : ℝ) else 0)) = c j := by simp
    rw [hcol] at hpair
    exact hpair
  have hcard : Fintype.card (Fin (Module.finrank ℝ E)) =
      Module.finrank ℝ (TangentSpace I x) := by
    rw [Fintype.card_fin]
    rfl
  set bB : Module.Basis (Fin (Module.finrank ℝ E)) ℝ (TangentSpace I x) :=
    basisOfLinearIndependentOfCardEqFinrank hlin hcard with hbB_def
  have hbB_coe : ∀ i, bB i = B i := by
    intro i
    rw [hbB_def]
    change (basisOfLinearIndependentOfCardEqFinrank hlin hcard :
        Fin (Module.finrank ℝ E) → TangentSpace I x) i = B i
    rw [coe_basisOfLinearIndependentOfCardEqFinrank]
  have hrepr : ∀ (v : TangentSpace I x) (j : Fin (Module.finrank ℝ E)),
      bB.repr v j = g₀.inner x v (B j) := by
    intro v j
    conv_rhs => rw [← bB.sum_repr v]
    rw [map_sum, sum_apply]
    have hsimp : ∀ i, g₀.inner x (bB.repr v i • bB i) (B j) =
        bB.repr v i * (if i = j then (1 : ℝ) else 0) := by
      intro i
      rw [map_smul, smul_apply, smul_eq_mul, hbB_coe i, horth i j]
    rw [Finset.sum_congr rfl (fun i _ => hsimp i)]
    simp
  rw [LinearMap.trace_eq_matrix_trace ℝ bB G]
  unfold Matrix.trace
  refine Finset.sum_congr rfl (fun i _ => ?_)
  simp only [Matrix.diag_apply]
  rw [LinearMap.toMatrix_apply, hrepr (G (bB i)) i, hbB_coe i]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless]
    [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
lemma interiorProduct_toModel_eval_lc (s : ℕ) (x : M) (v : TangentSpace I x)
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

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
lemma toModel_om_eval_lc (x : M) (om : Tensor0SSpace 1 I x) (V : E) :
    Tensor0SSpace.toModel om (fun _ : Fin 1 => V) =
      cotangentToDual (I := I) om
        ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm V) := by
  rw [cotangentToDual_apply]
  rfl

end CurvatureCoefficientDifferenceJetTower

omit [I.Boundaryless] [SigmaCompactSpace M] in
theorem slotInsert_ricMixedSharp_sub_ricEndoRaised_eq_raise_doubleTrace
    (g₀ g₁ : SmoothRiemannianMetric I M) :
    slotInsertEndoCc (I := I) (M := M) g₀ 0 (ricMixedSharpEndoField (I := I) (M := M) g₀ g₁) -
        slotInsertEndoCc (I := I) (M := M) g₀ 0 (ricEndoRaisedField (I := I) (M := M) g₀) =
      cometricRaiseSlot0Field (I := I) (M := M) g₀ 0
        (domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 2) 1)
          (ccOperatorFieldComp (I := I) (M := M) g₀ 0 4 2
            (cometricDoubleTraceField (I := I) g₀ 2)
            (riemannLoweredBackgroundDifference (I := I) (M := M) g₀ g₁))) := by
  classical
  set W2 : SmoothCcTensor g₀ 0 2 :=
    ccOperatorFieldComp (I := I) (M := M) g₀ 0 4 2
      (cometricDoubleTraceField (I := I) g₀ 2)
      (riemannLoweredBackgroundDifference (I := I) (M := M) g₀ g₁) with hW2_def
  have hW2unitModel : ∀ (x : M) (mm : Fin 2 → E),
      unitModel (I := I) (M := M) g₀ 2 W2 x mm =
        ricciTensor (I := I) g₁ x
            ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm (mm 0))
            ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm (mm 1)) -
          ricciTensor (I := I) g₀ x
            ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm (mm 0))
            ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm (mm 1)) := by
    intro x mm
    let mmt : Fin 2 → TangentSpace I x :=
      fun i => (tangentSpaceModelContinuousLinearEquiv (I := I) x).symm (mm i)
    have hsec : (W2.toSection x) =
        (show Tensor0SSpace 4 I x →L[ℝ] Tensor0SSpace 2 I x from
            cometricDoubleTraceFib (I := I) g₀ 2 x).comp
          (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 4 I x from
            (riemannLoweredBackgroundDifference (I := I) (M := M) g₀ g₁).toSection x) := by
      rw [hW2_def, operatorFieldComposition_toSection, cometricDoubleTraceField_toSection]
    rw [unitModel]
    rw [show (W2.toSection x) (unitTensor (I := I) (M := M) x) =
        cometricDoubleTraceFib (I := I) g₀ 2 x
          ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 4 I x from
            (riemannLoweredBackgroundDifference (I := I) (M := M) g₀ g₁).toSection x)
            (unitTensor (I := I) (M := M) x)) from by rw [hsec]; rfl]
    rw [cometricDoubleTraceFib_toModel]
    rw [modelDoubleTrace_apply]
    have hT : Tensor0SSpace.toModel
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 4 I x from
          (riemannLoweredBackgroundDifference (I := I) (M := M) g₀ g₁).toSection x)
          (unitTensor (I := I) (M := M) x)) =
        unitModel (I := I) (M := M) g₀ 4
          (riemannLoweredBackgroundDifference (I := I) (M := M) g₀ g₁) x := rfl
    rw [hT]
    rw [cometric_dualTrace_eq_orthoFrame_diag (I := I) g₀ x
      (mem_smoothOrthoFrameNbhd_self (I := I) (M := M) x)
      (unitModel (I := I) (M := M) g₀ 4
        (riemannLoweredBackgroundDifference (I := I) (M := M) g₀ g₁) x)
      mm]
    have hker : ∀ i : Fin (Module.finrank ℝ E),
        unitModel (I := I) (M := M) g₀ 4
          (riemannLoweredBackgroundDifference (I := I) (M := M) g₀ g₁) x
          (Fin.cons (tangentSpaceModelContinuousLinearEquiv (I := I) x
              (smoothOrthoFrame (I := I) g₀ x i x))
            (Fin.cons (tangentSpaceModelContinuousLinearEquiv (I := I) x
                (smoothOrthoFrame (I := I) g₀ x i x)) mm)) =
        g₀.inner x (riemannOp (LeviCivita (I := I) g₁) x
            (smoothOrthoFrame (I := I) g₀ x i x) (mmt 0) (mmt 1))
            (smoothOrthoFrame (I := I) g₀ x i x) -
          g₀.inner x (riemannOp (LeviCivita (I := I) g₀) x
              (smoothOrthoFrame (I := I) g₀ x i x) (mmt 0) (mmt 1))
              (smoothOrthoFrame (I := I) g₀ x i x) := by
      intro i
      rw [riemannLoweredBackgroundDifference_unitModel_apply]
      rw [show (Fin.cons
          (tangentSpaceModelContinuousLinearEquiv (I := I) x
            (smoothOrthoFrame (I := I) g₀ x i x))
          (Fin.cons
            (tangentSpaceModelContinuousLinearEquiv (I := I) x
              (smoothOrthoFrame (I := I) g₀ x i x)) mm) : Fin 4 → E) 2 = mm 0 from rfl,
        show (Fin.cons
          (tangentSpaceModelContinuousLinearEquiv (I := I) x
            (smoothOrthoFrame (I := I) g₀ x i x))
          (Fin.cons
            (tangentSpaceModelContinuousLinearEquiv (I := I) x
              (smoothOrthoFrame (I := I) g₀ x i x)) mm) : Fin 4 → E) 3 = mm 1 from rfl]
      simp [mmt]
    rw [Finset.sum_congr rfl (fun i _ => hker i), Finset.sum_sub_distrib]
    have htr1 : (∑ i : Fin (Module.finrank ℝ E),
        g₀.inner x (riemannOp (LeviCivita (I := I) g₁) x
            (smoothOrthoFrame (I := I) g₀ x i x) (mmt 0) (mmt 1))
            (smoothOrthoFrame (I := I) g₀ x i x)) =
        ricciTensor (I := I) g₁ x (mmt 0) (mmt 1) := by
      rw [ricciTensor_apply (I := I) g₁ x (mmt 0) (mmt 1),
        linearMap_trace_eq_orthoFrame_inner_sum (I := I) (M := M) g₀ x
          (ricciEndo (I := I) g₁ x (mmt 0) (mmt 1))]
      rfl
    have htr0 : (∑ i : Fin (Module.finrank ℝ E),
        g₀.inner x (riemannOp (LeviCivita (I := I) g₀) x
            (smoothOrthoFrame (I := I) g₀ x i x) (mmt 0) (mmt 1))
            (smoothOrthoFrame (I := I) g₀ x i x)) =
        ricciTensor (I := I) g₀ x (mmt 0) (mmt 1) := by
      rw [ricciTensor_apply (I := I) g₀ x (mmt 0) (mmt 1),
        linearMap_trace_eq_orthoFrame_inner_sum (I := I) (M := M) g₀ x
          (ricciEndo (I := I) g₀ x (mmt 0) (mmt 1))]
      rfl
    rw [htr1, htr0]
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rw [show ((slotInsertEndoCc (I := I) (M := M) g₀ 0
          (ricMixedSharpEndoField (I := I) (M := M) g₀ g₁) -
        slotInsertEndoCc (I := I) (M := M) g₀ 0
          (ricEndoRaisedField (I := I) (M := M) g₀)).toSection x) =
      (slotInsertEndoCc (I := I) (M := M) g₀ 0
          (ricMixedSharpEndoField (I := I) (M := M) g₀ g₁)).toSection x -
        (slotInsertEndoCc (I := I) (M := M) g₀ 0
          (ricEndoRaisedField (I := I) (M := M) g₀)).toSection x from by
    rw [SmoothCcTensor.toSection_sub]; rfl]
  apply ContinuousLinearMap.ext
  intro om
  rw [sub_apply]
  apply Tensor0SSpace.toModel_injective
  apply ContinuousMultilinearMap.ext
  intro m
  beta_reduce
  rw [Tensor0SSpace.toModel_sub, sub_apply]
  rw [show ((slotInsertEndoCc (I := I) (M := M) g₀ 0
        (ricMixedSharpEndoField (I := I) (M := M) g₀ g₁)).toSection x) om =
      slotInsertEndoFib (I := I) (M := M) 1 0 x
        (ricMixedSharpEndoFib (I := I) (M := M) g₀ g₁ x) om from rfl]
  rw [show ((slotInsertEndoCc (I := I) (M := M) g₀ 0
        (ricEndoRaisedField (I := I) (M := M) g₀)).toSection x) om =
      slotInsertEndoFib (I := I) (M := M) 1 0 x (ricEndoRaisedFib (I := I) g₀ x) om from rfl]
  rw [slotInsertEndoFib_apply_eval, slotInsertEndoFib_apply_eval]
  set u : TangentSpace I x := inverseMetricSharpFib (I := I) g₀ x om with hu_def
  have hupd : ∀ V : TangentSpace I x,
      Function.update m 0 (tangentSpaceModelContinuousLinearEquiv (I := I) x V) =
        fun _ : Fin 1 => tangentSpaceModelContinuousLinearEquiv (I := I) x V := by
    intro V
    funext j
    fin_cases j
    rfl
  have hsharp_pair : ∀ α : TangentSpace I x →ₗ[ℝ] ℝ,
      cotangentToDual (I := I) om (metricSharp (I := I) g₀ x α) = α u := by
    intro α
    rw [show cotangentToDual (I := I) om (metricSharp (I := I) g₀ x α) =
        cotangentToDualLinear (I := I) (x := x) om (metricSharp (I := I) g₀ x α) from rfl]
    rw [← inverseMetricSharpFib_inner (I := I) g₀ x om (metricSharp (I := I) g₀ x α), ← hu_def]
    exact inner_metricSharp_right (I := I) g₀ x α u
  have hLmix : Tensor0SSpace.toModel om
      (Function.update m 0
        (tangentLinearMapToModel (ricMixedSharpEndoFib (I := I) (M := M) g₀ g₁ x) (m 0))) =
      (ricciTensor (I := I) g₁ x
        ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm (m 0))).toLinearMap u := by
    rw [tangentLinearMapToModel_apply]
    rw [ricMixedSharpEndoFib_apply (I := I) (M := M) g₀ g₁ x
      ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm (m 0))]
    rw [hupd, toModel_om_eval_lc, ContinuousLinearEquiv.symm_apply_apply, hsharp_pair]
  have hLraised : Tensor0SSpace.toModel om
      (Function.update m 0
        (tangentLinearMapToModel (ricEndoRaisedFib (I := I) g₀ x) (m 0))) =
      (ricciTensor (I := I) g₀ x
        ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm (m 0))).toLinearMap u := by
    rw [tangentLinearMapToModel_apply]
    rw [ricEndoRaisedFib_apply (I := I) g₀ x
      ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm (m 0))]
    rw [hupd, toModel_om_eval_lc, ContinuousLinearEquiv.symm_apply_apply, hsharp_pair]
  rw [hLmix, hLraised]
  rw [cometricRaiseSlot0Field_toSection]
  rw [show ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 1 I x from
        cometricRaiseSlot0Fib g₀ 0 x
          ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from
            (domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 2) 1) W2).toSection x)
            (unitTensor (I := I) (M := M) x))) om) =
      Tensor0SBundle.interiorProduct (𝕜 := ℝ) (I := I) (0 + 1) x
        (inverseMetricSharpFib (I := I) g₀ x om)
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from
          (domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 2) 1) W2).toSection x)
          (unitTensor (I := I) (M := M) x)) from
    cometricRaiseSlot0Fib_clm_apply (I := I) g₀ 0 x _ om]
  rw [interiorProduct_toModel_eval_lc (I := I) (M := M) (0 + 1) x
    (inverseMetricSharpFib (I := I) g₀ x om) _ m]
  rw [show Tensor0SSpace.toModel
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from
          (domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 2) 1) W2).toSection x)
          (unitTensor (I := I) (M := M) x)) =
      unitModel (I := I) (M := M) g₀ 2
        (domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 2) 1) W2) x from rfl]
  rw [domDomCongrSection_unitModel, ContinuousMultilinearMap.domDomCongr_apply]
  rw [show (fun i : Fin 2 =>
        (Fin.cons (tangentSpaceModelContinuousLinearEquiv (I := I) x
            (inverseMetricSharpFib (I := I) g₀ x om)) m : Fin 2 → E)
          ((Equiv.swap (0 : Fin 2) 1) i)) =
      (![m 0, tangentSpaceModelContinuousLinearEquiv (I := I) x u] : Fin 2 → E) from by
    funext i
    fin_cases i <;>
      simp [hu_def]]
  rw [hW2unitModel x]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  rfl

end RiemannLoweredDifference

open DifferentialGeometry.Analysis.Spectral.DeTurck in
theorem riemannianFiberNormSq_iteratedCovGrad_ricciMixedSharpBackgroundDifference_diagonalProductGrid_le
    (g₀ : SmoothRiemannianMetric I M) {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ C : ℕ → ℝ, (∀ i, 0 ≤ C i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (T : SmoothCcTensor g₀ 0 2)
        (_htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ T y v w)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀) (_hδ0 : 0 ≤ δ)
        (_hbound : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        (i : ℕ) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + i) x
            ((iteratedCovGrad (I := I) g₀ 1 1 i
              (slotInsertEndoCc (I := I) (M := M) g₀ 0
                  (ricMixedSharpEndoField (I := I) (M := M) g₀ g₁) -
                slotInsertEndoCc (I := I) (M := M) g₀ 0
                  (ricEndoRaisedField (I := I) (M := M) g₀))).toSection x) ≤
          C i * ∑ k ∈ Finset.range (i + 3),
            ∑ n ∈ Finset.range (k + 1),
              ∑ e ∈ Finset.Nat.antidiagonalTuple n k,
                ∏ m : Fin n,
                  riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
                    ((iteratedCovGrad (I := I) g₀ 0 2 (e m) T).toSection x) := by
  classical
  obtain ⟨CA, hCA_nn, hCA⟩ :=
    riemannianFiberNormSq_iteratedCovGrad_riemannLoweredBackgroundDifference_diagonalProductGrid_le
      (I := I) (M := M) g₀ hδ₀
  obtain ⟨cPhi, hcPhi_nn, hcPhi⟩ := exists_bound_riemannianFiberNormSq_smoothCcTensor
    (I := I) (M := M) g₀ 4 2 (cometricDoubleTraceField (I := I) g₀ 2)
  refine ⟨fun i => operatorFieldApplicationGdiag (E := E) i * cPhi * (∑ l ∈ Finset.range (i + 1), CA l),
    fun i => mul_nonneg (mul_nonneg (operatorFieldApplicationGdiag_nonneg (E := E) i) hcPhi_nn)
      (Finset.sum_nonneg fun l _ => hCA_nn l), ?_⟩
  intro g₁ T htie δ hδ_le hδ0 hbound i x
  have hb : ∀ j : ℕ, 0 ≤ riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x
      ((iteratedCovGrad (I := I) g₀ 0 2 j T).toSection x) :=
    fun j => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + j) x _
  rw [slotInsert_ricMixedSharp_sub_ricEndoRaised_eq_raise_doubleTrace (I := I) (M := M) g₀ g₁]
  rw [riemannianFiberNormSq_iteratedCovGrad_cometricRaiseSlot0Field_eq (I := I) (M := M) g₀ 0
    (domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 2) 1)
      (ccOperatorFieldComp (I := I) (M := M) g₀ 0 4 2
        (cometricDoubleTraceField (I := I) g₀ 2)
        (riemannLoweredBackgroundDifference (I := I) (M := M) g₀ g₁))) i x]
  rw [riemannianFiberNormSq_iteratedCovGrad_domDomCongrSection (I := I) (M := M) g₀
    (Equiv.swap (0 : Fin 2) 1)
    (ccOperatorFieldComp (I := I) (M := M) g₀ 0 4 2
      (cometricDoubleTraceField (I := I) g₀ 2)
      (riemannLoweredBackgroundDifference (I := I) (M := M) g₀ g₁)) i x]
  refine le_trans (riemannianFiberNormSq_iteratedCovGrad_operatorFieldComposition_diagonalProductGrid_rankLeft_le
    (I := I) (M := M) g₀ i 0 4 2 (cometricDoubleTraceField (I := I) g₀ 2)
    (riemannLoweredBackgroundDifference (I := I) (M := M) g₀ g₁) x) ?_
  have hAzero : ∀ m : ℕ,
      riemannianFiberNormSq (I := I) (M := M) g₀ 4 (2 + (m + 1)) x
        ((iteratedCovGrad (I := I) g₀ 4 2 (m + 1)
          (cometricDoubleTraceField (I := I) g₀ 2)).toSection x) = 0 := by
    intro m
    rw [← riemannianFiberNormSq_iteratedCovGrad_covGrad_comm_rs (I := I) (M := M) g₀ 4 2 m
      (cometricDoubleTraceField (I := I) g₀ 2) x]
    rw [show covGrad (I := I) (M := M) g₀ 4 2 (cometricDoubleTraceField (I := I) g₀ 2) =
        (0 : SmoothCcTensor g₀ 4 3) from
      cometricDoubleTraceField_covGrad_eq_zero (I := I) g₀ 2]
    rw [show iteratedCovGrad (I := I) g₀ 4 3 m (0 : SmoothCcTensor g₀ 4 3) =
        (0 : SmoothCcTensor g₀ 4 (3 + m)) from by
      induction m with
      | zero => rw [iteratedCovGrad_zero]
      | succ m' ih => rw [iteratedCovGrad_succ, ih, covGrad_zero]]
    rw [show ((0 : SmoothCcTensor g₀ 4 (3 + m)).toSection x) =
        (0 : TensorRSSpace 4 (3 + m) I x) from by
      rw [SmoothCcTensor.toSection_zero]; rfl]
    exact riemannianFiberNormSq_zero (I := I) (M := M) g₀ 4 (3 + m) x
  have hBmono : ∀ i' : ℕ,
      (∑ l ∈ Finset.range (i + 1 - i'),
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + l) x
          ((iteratedCovGrad (I := I) g₀ 0 4 l
            (riemannLoweredBackgroundDifference (I := I) (M := M) g₀ g₁)).toSection x)) ≤
      ∑ l ∈ Finset.range (i + 1),
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + l) x
          ((iteratedCovGrad (I := I) g₀ 0 4 l
            (riemannLoweredBackgroundDifference (I := I) (M := M) g₀ g₁)).toSection x) := by
    intro i'
    refine Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.range_subset_range.mpr (by omega)) ?_
    intro l _ _
    exact riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (4 + l) x _
  have hterm : ∀ i' ∈ Finset.range (i + 1),
      riemannianFiberNormSq (I := I) (M := M) g₀ 4 (2 + i') x
          ((iteratedCovGrad (I := I) g₀ 4 2 i'
            (cometricDoubleTraceField (I := I) g₀ 2)).toSection x) *
        (∑ l ∈ Finset.range (i + 1 - i'),
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + l) x
            ((iteratedCovGrad (I := I) g₀ 0 4 l
              (riemannLoweredBackgroundDifference (I := I) (M := M) g₀ g₁)).toSection x)) ≤
      (if i' = 0 then
        cPhi * ∑ l ∈ Finset.range (i + 1),
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + l) x
            ((iteratedCovGrad (I := I) g₀ 0 4 l
              (riemannLoweredBackgroundDifference (I := I) (M := M) g₀ g₁)).toSection x)
      else 0) := by
    intro i' _
    match i' with
    | 0 =>
        rw [if_pos rfl]
        have hA0 : riemannianFiberNormSq (I := I) (M := M) g₀ 4 (2 + 0) x
            ((iteratedCovGrad (I := I) g₀ 4 2 0
              (cometricDoubleTraceField (I := I) g₀ 2)).toSection x) ≤ cPhi := by
          rw [iteratedCovGrad_zero]
          exact hcPhi x
        refine mul_le_mul hA0 (hBmono 0) (Finset.sum_nonneg fun l _ =>
          riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (4 + l) x _) hcPhi_nn
    | (m + 1) =>
        rw [if_neg (by omega)]
        rw [hAzero m, zero_mul]
  refine le_trans (mul_le_mul_of_nonneg_left (Finset.sum_le_sum hterm)
    (operatorFieldApplicationGdiag_nonneg (E := E) i)) ?_
  rw [Finset.sum_ite_eq' (Finset.range (i + 1)) 0]
  rw [if_pos (Finset.mem_range.mpr (by omega))]
  have hBackgroundrid : (∑ l ∈ Finset.range (i + 1),
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + l) x
        ((iteratedCovGrad (I := I) g₀ 0 4 l
          (riemannLoweredBackgroundDifference (I := I) (M := M) g₀ g₁)).toSection x)) ≤
      (∑ l ∈ Finset.range (i + 1), CA l) *
        tWindow (fun j => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x
          ((iteratedCovGrad (I := I) g₀ 0 2 j T).toSection x)) i := by
    calc (∑ l ∈ Finset.range (i + 1),
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + l) x
          ((iteratedCovGrad (I := I) g₀ 0 4 l
            (riemannLoweredBackgroundDifference (I := I) (M := M) g₀ g₁)).toSection x))
        ≤ ∑ l ∈ Finset.range (i + 1), CA l *
            tWindow (fun j => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x
              ((iteratedCovGrad (I := I) g₀ 0 2 j T).toSection x)) l := by
          refine Finset.sum_le_sum (fun l _ => ?_)
          have h := hCA g₁ T htie hδ_le hδ0 hbound l x
          rw [← tWindow_eq_tripleSum (I := I) (M := M) g₀ T x l] at h
          exact h
      _ ≤ ∑ l ∈ Finset.range (i + 1), CA l *
            tWindow (fun j => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x
              ((iteratedCovGrad (I := I) g₀ 0 2 j T).toSection x)) i := by
          refine Finset.sum_le_sum (fun l hl => ?_)
          refine mul_le_mul_of_nonneg_left ?_ (hCA_nn l)
          exact tWindow_mono _ hb (by
            have := Finset.mem_range.mp hl
            omega)
      _ = (∑ l ∈ Finset.range (i + 1), CA l) *
            tWindow (fun j => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x
              ((iteratedCovGrad (I := I) g₀ 0 2 j T).toSection x)) i := by
          rw [Finset.sum_mul]
  rw [← tWindow_eq_tripleSum (I := I) (M := M) g₀ T x i]
  calc operatorFieldApplicationGdiag (E := E) i *
        (cPhi * ∑ l ∈ Finset.range (i + 1),
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + l) x
            ((iteratedCovGrad (I := I) g₀ 0 4 l
              (riemannLoweredBackgroundDifference (I := I) (M := M) g₀ g₁)).toSection x))
      ≤ operatorFieldApplicationGdiag (E := E) i * (cPhi * ((∑ l ∈ Finset.range (i + 1), CA l) *
          tWindow (fun j => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x
            ((iteratedCovGrad (I := I) g₀ 0 2 j T).toSection x)) i)) := by
        refine mul_le_mul_of_nonneg_left ?_ (operatorFieldApplicationGdiag_nonneg (E := E) i)
        exact mul_le_mul_of_nonneg_left hBackgroundrid hcPhi_nn
    _ = operatorFieldApplicationGdiag (E := E) i * cPhi * (∑ l ∈ Finset.range (i + 1), CA l) *
          tWindow (fun j => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x
            ((iteratedCovGrad (I := I) g₀ 0 2 j T).toSection x)) i := by
        ring

namespace CurvatureCoefficientDifferenceJetTower

lemma diagonalGrid_arith (b : ℕ → ℝ) (hb : ∀ j, 0 ≤ b j)
    (i : ℕ) (G : ℝ) (hG : 0 ≤ G)
    (CL CD cbg : ℕ → ℝ) (hCL_nn : ∀ k, 0 ≤ CL k) (hCD_nn : ∀ k, 0 ≤ CD k)
    (hcbg_nn : ∀ k, 0 ≤ cbg k)
    (t u ap : ℝ) (wj vl : ℕ → ℝ)
    (ht : t ≤ 2 * u + 2 * ap)
    (hu : u ≤ CL i * tWindow b i)
    (hap : ap ≤ G * ∑ j ∈ Finset.range (i + 1), wj j * ∑ l ∈ Finset.range (i + 1 - j), vl l)
    (hwj : ∀ j, j ≤ i → wj j ≤ (2 * CL j + 2 * cbg j) * tWindow b j)
    (hvl_nn : ∀ l, 0 ≤ vl l)
    (hvl : ∀ l, l ≤ i → vl l ≤ CD l * Combinatorics.antidiagonalTupleGrid b l) :
    t ≤ (2 * CL i + 2 * (G * ∑ j ∈ Finset.range (i + 1), (2 * CL j + 2 * cbg j) *
        ∑ l ∈ Finset.range (i + 1 - j), CD l * tWindowMulConst j l)) * tWindow b i := by
  have hstep : ∀ j ∈ Finset.range (i + 1),
      wj j * ∑ l ∈ Finset.range (i + 1 - j), vl l ≤
        ((2 * CL j + 2 * cbg j) * ∑ l ∈ Finset.range (i + 1 - j),
          CD l * tWindowMulConst j l) * tWindow b i := by
    intro j hj
    rw [Finset.mem_range] at hj
    have hj_le : j ≤ i := by omega
    have hcj_nn : 0 ≤ 2 * CL j + 2 * cbg j := by
      have := hCL_nn j
      have := hcbg_nn j
      linarith
    have h1 : wj j * ∑ l ∈ Finset.range (i + 1 - j), vl l ≤
        ((2 * CL j + 2 * cbg j) * tWindow b j) * ∑ l ∈ Finset.range (i + 1 - j), vl l :=
      mul_le_mul_of_nonneg_right (hwj j hj_le) (Finset.sum_nonneg (fun l _ => hvl_nn l))
    refine le_trans h1 ?_
    have h2 : ∀ l ∈ Finset.range (i + 1 - j), tWindow b j * vl l ≤
        CD l * tWindowMulConst j l * tWindow b i := by
      intro l hl
      rw [Finset.mem_range] at hl
      have hl_le : l ≤ i := by omega
      have hjl : j + l ≤ i := by omega
      have h3 : tWindow b j * vl l ≤
          tWindow b j * (CD l * Combinatorics.antidiagonalTupleGrid b l) :=
        mul_le_mul_of_nonneg_left (hvl l hl_le) (tWindow_nonneg b hb j)
      refine le_trans h3 ?_
      rw [show tWindow b j * (CD l * Combinatorics.antidiagonalTupleGrid b l) =
          CD l * (tWindow b j * Combinatorics.antidiagonalTupleGrid b l) from by ring]
      calc CD l * (tWindow b j * Combinatorics.antidiagonalTupleGrid b l)
          ≤ CD l * (tWindowMulConst j l * tWindow b (j + l)) :=
            mul_le_mul_of_nonneg_left
              (tWindow_mul_antidiagonalTupleGrid_le b hb j l) (hCD_nn l)
        _ ≤ CD l * (tWindowMulConst j l * tWindow b i) :=
            mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left (tWindow_mono b hb hjl)
                (tWindowMulConst_nonneg j l)) (hCD_nn l)
        _ = CD l * tWindowMulConst j l * tWindow b i := by ring
    calc ((2 * CL j + 2 * cbg j) * tWindow b j) * ∑ l ∈ Finset.range (i + 1 - j), vl l
        = (2 * CL j + 2 * cbg j) * ∑ l ∈ Finset.range (i + 1 - j), tWindow b j * vl l := by
          rw [mul_assoc, Finset.mul_sum]
      _ ≤ (2 * CL j + 2 * cbg j) * ∑ l ∈ Finset.range (i + 1 - j),
            CD l * tWindowMulConst j l * tWindow b i :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum h2) hcj_nn
      _ = ((2 * CL j + 2 * cbg j) * ∑ l ∈ Finset.range (i + 1 - j),
            CD l * tWindowMulConst j l) * tWindow b i := by
          rw [← Finset.sum_mul]
          ring
  have hW_nn : 0 ≤ tWindow b i := tWindow_nonneg b hb i
  have hap2 : ap ≤ G * ((∑ j ∈ Finset.range (i + 1), (2 * CL j + 2 * cbg j) *
      ∑ l ∈ Finset.range (i + 1 - j), CD l * tWindowMulConst j l) * tWindow b i) := by
    refine le_trans hap ?_
    refine mul_le_mul_of_nonneg_left ?_ hG
    refine le_trans (Finset.sum_le_sum hstep) (le_of_eq ?_)
    rw [← Finset.sum_mul]
  have hu2 : u ≤ CL i * tWindow b i := hu
  calc t ≤ 2 * u + 2 * ap := ht
    _ ≤ 2 * (CL i * tWindow b i) + 2 * (G * ((∑ j ∈ Finset.range (i + 1),
          (2 * CL j + 2 * cbg j) * ∑ l ∈ Finset.range (i + 1 - j),
            CD l * tWindowMulConst j l) * tWindow b i)) := by linarith
    _ = (2 * CL i + 2 * (G * ∑ j ∈ Finset.range (i + 1), (2 * CL j + 2 * cbg j) *
          ∑ l ∈ Finset.range (i + 1 - j), CD l * tWindowMulConst j l)) * tWindow b i := by
        ring

end CurvatureCoefficientDifferenceJetTower

theorem riemannianFiberNormSq_iteratedCovGrad_slotInsertEndoCc_zero_ricEndoBackgroundDifferenceField_diagonalProductGrid_le
    (g₀ : SmoothRiemannianMetric I M) {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ C : ℕ → ℝ, (∀ i, 0 ≤ C i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (T : SmoothCcTensor g₀ 0 2)
        (_htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ T y v w)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀) (_hδ0 : 0 ≤ δ)
        (_hbound : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        (i : ℕ) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + i) x
            ((iteratedCovGrad (I := I) g₀ 1 1 i
              (slotInsertEndoCc (I := I) (M := M) g₀ 0
                (ricEndoBackgroundDifferenceField (I := I) (M := M) g₀ g₁))).toSection x) ≤
          C i * ∑ k ∈ Finset.range (i + 3),
            ∑ n ∈ Finset.range (k + 1),
              ∑ e ∈ Finset.Nat.antidiagonalTuple n k,
                ∏ m : Fin n,
                  riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
                    ((iteratedCovGrad (I := I) g₀ 0 2 (e m) T).toSection x) := by
  classical
  obtain ⟨CL, hCL_nn, hCL⟩ :=
    riemannianFiberNormSq_iteratedCovGrad_ricciMixedSharpBackgroundDifference_diagonalProductGrid_le
      (I := I) (M := M) g₀ hδ₀
  obtain ⟨CD, hCD_nn, hCD⟩ :=
    riemannianFiberNormSq_iteratedCovGrad_slotInsertEndoCc_zero_metricComparisonDifferenceEndomorphismField_diagonalProductGrid_le
      (I := I) (M := M) g₀ hδ₀
  obtain ⟨cbg, hcbg_nn, hcbg⟩ := exists_backgroundJet_riemannianFiberNormSq_bound (I := I) (M := M) g₀ 1 1
    (slotInsertEndoCc (I := I) (M := M) g₀ 0 (ricEndoRaisedField (I := I) (M := M) g₀))
  refine ⟨fun i => 2 * CL i + 2 * (operatorFieldApplicationGdiag (E := E) i *
      ∑ j ∈ Finset.range (i + 1), (2 * CL j + 2 * cbg j) *
        ∑ l ∈ Finset.range (i + 1 - j), CD l * tWindowMulConst j l),
    fun i => ?_, ?_⟩
  · have h1 : 0 ≤ operatorFieldApplicationGdiag (E := E) i := operatorFieldApplicationGdiag_nonneg (E := E) i
    have h2 : 0 ≤ ∑ j ∈ Finset.range (i + 1), (2 * CL j + 2 * cbg j) *
        ∑ l ∈ Finset.range (i + 1 - j), CD l * tWindowMulConst j l :=
      Finset.sum_nonneg (fun j _ => mul_nonneg
        (by have := hCL_nn j; have := hcbg_nn j; linarith)
        (Finset.sum_nonneg (fun l _ => mul_nonneg (hCD_nn l) (tWindowMulConst_nonneg j l))))
    have h3 := mul_nonneg h1 h2
    have h4 := hCL_nn i
    linarith
  · intro g₁ T htie δ hδ_le hδ0 hbound i x
    have hb : ∀ j : ℕ, 0 ≤ riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x
        ((iteratedCovGrad (I := I) g₀ 0 2 j T).toSection x) :=
      fun j => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + j) x _
    rw [← tWindow_eq_tripleSum (I := I) (M := M) g₀ T x i]
    have hsec : (iteratedCovGrad (I := I) g₀ 1 1 i
        (slotInsertEndoCc (I := I) (M := M) g₀ 0
          (ricEndoBackgroundDifferenceField (I := I) (M := M) g₀ g₁))).toSection x =
        (iteratedCovGrad (I := I) g₀ 1 1 i
          (slotInsertEndoCc (I := I) (M := M) g₀ 0
              (ricMixedSharpEndoField (I := I) (M := M) g₀ g₁) -
            slotInsertEndoCc (I := I) (M := M) g₀ 0
              (ricEndoRaisedField (I := I) (M := M) g₀))).toSection x +
          (iteratedCovGrad (I := I) g₀ 1 1 i
            (ccOperatorFieldComp (I := I) (M := M) g₀ 1 1 1
              (slotInsertEndoCc (I := I) (M := M) g₀ 0
                (ricMixedSharpEndoField (I := I) (M := M) g₀ g₁))
              (slotInsertEndoCc (I := I) (M := M) g₀ 0
                (metricComparisonDifferenceEndomorphismField (I := I) g₀ g₁)))).toSection x := by
      rw [slotInsertEndoCc_zero_ricEndoBackgroundDifference_telescope (I := I) (M := M) g₀ g₁,
        iteratedCovGrad_add (I := I) g₀ 1 1 i _ _, SmoothCcTensor.toSection_add]
      rfl
    have hLHS : riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + i) x
        ((iteratedCovGrad (I := I) g₀ 1 1 i
          (slotInsertEndoCc (I := I) (M := M) g₀ 0
            (ricEndoBackgroundDifferenceField (I := I) (M := M) g₀ g₁))).toSection x) ≤
        2 * riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + i) x
            ((iteratedCovGrad (I := I) g₀ 1 1 i
              (slotInsertEndoCc (I := I) (M := M) g₀ 0
                  (ricMixedSharpEndoField (I := I) (M := M) g₀ g₁) -
                slotInsertEndoCc (I := I) (M := M) g₀ 0
                  (ricEndoRaisedField (I := I) (M := M) g₀))).toSection x) +
          2 * riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + i) x
            ((iteratedCovGrad (I := I) g₀ 1 1 i
              (ccOperatorFieldComp (I := I) (M := M) g₀ 1 1 1
                (slotInsertEndoCc (I := I) (M := M) g₀ 0
                  (ricMixedSharpEndoField (I := I) (M := M) g₀ g₁))
                (slotInsertEndoCc (I := I) (M := M) g₀ 0
                  (metricComparisonDifferenceEndomorphismField (I := I) g₀ g₁)))).toSection x) := by
      rw [hsec]
      exact riemannianFiberNormSq_add_le (I := I) (M := M) g₀ 1 (1 + i) x _ _
    have hu : riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + i) x
        ((iteratedCovGrad (I := I) g₀ 1 1 i
          (slotInsertEndoCc (I := I) (M := M) g₀ 0
              (ricMixedSharpEndoField (I := I) (M := M) g₀ g₁) -
            slotInsertEndoCc (I := I) (M := M) g₀ 0
              (ricEndoRaisedField (I := I) (M := M) g₀))).toSection x) ≤
        CL i * tWindow (fun j => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x
          ((iteratedCovGrad (I := I) g₀ 0 2 j T).toSection x)) i := by
      rw [tWindow_eq_tripleSum (I := I) (M := M) g₀ T x i]
      exact hCL g₁ T htie hδ_le hδ0 hbound i x
    have hap := riemannianFiberNormSq_iteratedCovGrad_operatorFieldComposition_diagonalProductGrid_rankLeft_le
      (I := I) (M := M) g₀ i 1 1 1
      (slotInsertEndoCc (I := I) (M := M) g₀ 0 (ricMixedSharpEndoField (I := I) (M := M) g₀ g₁))
      (slotInsertEndoCc (I := I) (M := M) g₀ 0 (metricComparisonDifferenceEndomorphismField (I := I) g₀ g₁)) x
    have hwj : ∀ j, j ≤ i → riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + j) x
        ((iteratedCovGrad (I := I) g₀ 1 1 j
          (slotInsertEndoCc (I := I) (M := M) g₀ 0
            (ricMixedSharpEndoField (I := I) (M := M) g₀ g₁))).toSection x) ≤
        (2 * CL j + 2 * cbg j) *
          tWindow (fun j' => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j') x
            ((iteratedCovGrad (I := I) g₀ 0 2 j' T).toSection x)) j := by
      intro j hj
      have hsplit : slotInsertEndoCc (I := I) (M := M) g₀ 0
          (ricMixedSharpEndoField (I := I) (M := M) g₀ g₁) =
          (slotInsertEndoCc (I := I) (M := M) g₀ 0
              (ricMixedSharpEndoField (I := I) (M := M) g₀ g₁) -
            slotInsertEndoCc (I := I) (M := M) g₀ 0
              (ricEndoRaisedField (I := I) (M := M) g₀)) +
          slotInsertEndoCc (I := I) (M := M) g₀ 0
            (ricEndoRaisedField (I := I) (M := M) g₀) := by
        rw [sub_add_cancel]
      have hsec2 : (iteratedCovGrad (I := I) g₀ 1 1 j
          (slotInsertEndoCc (I := I) (M := M) g₀ 0
            (ricMixedSharpEndoField (I := I) (M := M) g₀ g₁))).toSection x =
          (iteratedCovGrad (I := I) g₀ 1 1 j
            (slotInsertEndoCc (I := I) (M := M) g₀ 0
                (ricMixedSharpEndoField (I := I) (M := M) g₀ g₁) -
              slotInsertEndoCc (I := I) (M := M) g₀ 0
                (ricEndoRaisedField (I := I) (M := M) g₀))).toSection x +
            (iteratedCovGrad (I := I) g₀ 1 1 j
              (slotInsertEndoCc (I := I) (M := M) g₀ 0
                (ricEndoRaisedField (I := I) (M := M) g₀))).toSection x := by
        conv_lhs => rw [hsplit]
        rw [iteratedCovGrad_add (I := I) g₀ 1 1 j _ _, SmoothCcTensor.toSection_add]
        rfl
      rw [hsec2]
      refine le_trans (riemannianFiberNormSq_add_le (I := I) (M := M) g₀ 1 (1 + j) x _ _) ?_
      have hone : 1 ≤ tWindow (fun j' => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j') x
          ((iteratedCovGrad (I := I) g₀ 0 2 j' T).toSection x)) j :=
        one_le_tWindow _ hb j
      have hb1 : riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + j) x
          ((iteratedCovGrad (I := I) g₀ 1 1 j
            (slotInsertEndoCc (I := I) (M := M) g₀ 0
                (ricMixedSharpEndoField (I := I) (M := M) g₀ g₁) -
              slotInsertEndoCc (I := I) (M := M) g₀ 0
                (ricEndoRaisedField (I := I) (M := M) g₀))).toSection x) ≤
          CL j * tWindow (fun j' => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j') x
            ((iteratedCovGrad (I := I) g₀ 0 2 j' T).toSection x)) j := by
        rw [tWindow_eq_tripleSum (I := I) (M := M) g₀ T x j]
        exact hCL g₁ T htie hδ_le hδ0 hbound j x
      have hb2 : riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + j) x
          ((iteratedCovGrad (I := I) g₀ 1 1 j
            (slotInsertEndoCc (I := I) (M := M) g₀ 0
              (ricEndoRaisedField (I := I) (M := M) g₀))).toSection x) ≤
          cbg j * tWindow (fun j' => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j') x
            ((iteratedCovGrad (I := I) g₀ 0 2 j' T).toSection x)) j :=
        le_trans (hcbg j x) (le_mul_of_one_le_right (hcbg_nn j) hone)
      linarith
    have hvl : ∀ l, l ≤ i → riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + l) x
        ((iteratedCovGrad (I := I) g₀ 1 1 l
          (slotInsertEndoCc (I := I) (M := M) g₀ 0
            (metricComparisonDifferenceEndomorphismField (I := I) g₀ g₁))).toSection x) ≤
        CD l * Combinatorics.antidiagonalTupleGrid
          (fun j' => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j') x
            ((iteratedCovGrad (I := I) g₀ 0 2 j' T).toSection x)) l := by
      intro l _
      rw [antidiagonalTupleGrid_eq_doubleSum (I := I) (M := M) g₀ T x l]
      exact hCD g₁ T htie hδ_le hδ0 hbound l x
    exact diagonalGrid_arith
      (fun j => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x
        ((iteratedCovGrad (I := I) g₀ 0 2 j T).toSection x)) hb i
      (operatorFieldApplicationGdiag (E := E) i) (operatorFieldApplicationGdiag_nonneg (E := E) i)
      CL CD cbg hCL_nn hCD_nn hcbg_nn
      (riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + i) x
        ((iteratedCovGrad (I := I) g₀ 1 1 i
          (slotInsertEndoCc (I := I) (M := M) g₀ 0
            (ricEndoBackgroundDifferenceField (I := I) (M := M) g₀ g₁))).toSection x))
      (riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + i) x
        ((iteratedCovGrad (I := I) g₀ 1 1 i
          (slotInsertEndoCc (I := I) (M := M) g₀ 0
              (ricMixedSharpEndoField (I := I) (M := M) g₀ g₁) -
            slotInsertEndoCc (I := I) (M := M) g₀ 0
              (ricEndoRaisedField (I := I) (M := M) g₀))).toSection x))
      (riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + i) x
        ((iteratedCovGrad (I := I) g₀ 1 1 i
          (ccOperatorFieldComp (I := I) (M := M) g₀ 1 1 1
            (slotInsertEndoCc (I := I) (M := M) g₀ 0
              (ricMixedSharpEndoField (I := I) (M := M) g₀ g₁))
            (slotInsertEndoCc (I := I) (M := M) g₀ 0
              (metricComparisonDifferenceEndomorphismField (I := I) g₀ g₁)))).toSection x))
      (fun j => riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + j) x
        ((iteratedCovGrad (I := I) g₀ 1 1 j
          (slotInsertEndoCc (I := I) (M := M) g₀ 0
            (ricMixedSharpEndoField (I := I) (M := M) g₀ g₁))).toSection x))
      (fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + l) x
        ((iteratedCovGrad (I := I) g₀ 1 1 l
          (slotInsertEndoCc (I := I) (M := M) g₀ 0
            (metricComparisonDifferenceEndomorphismField (I := I) g₀ g₁))).toSection x))
      hLHS hu hap hwj
      (fun l => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 1 (1 + l) x _)
      hvl

section RiemannMixedBiContr



def riemannMixedKernelBilin (g₀ g₁ : SmoothRiemannianMetric I M) (x : M)
    (p q : TangentSpace I x) :
    TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ :=
  haveI : FiniteDimensional ℝ (TangentSpace I x) := inferInstanceAs (FiniteDimensional ℝ E)
  LinearMap.toContinuousLinearMap
    { toFun := fun v0 => (g₀.inner x (riemannOp (LeviCivita (I := I) g₁) x v0 p q))
      map_add' := fun v0 v0' => by
        rw [(riemannOp (LeviCivita (I := I) g₁) x).map_add v0 v0',
          add_apply, add_apply, map_add]
      map_smul' := fun c v0 => by
        rw [(riemannOp (LeviCivita (I := I) g₁) x).map_smul c v0,
          smul_apply, smul_apply, map_smul,
          RingHom.id_apply] }

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [SigmaCompactSpace M] in
@[simp] theorem riemannMixedKernelBilin_apply (g₀ g₁ : SmoothRiemannianMetric I M) (x : M)
    (p q v0 v1 : TangentSpace I x) :
    riemannMixedKernelBilin (I := I) g₀ g₁ x p q v0 v1 =
      g₀.inner x (riemannOp (LeviCivita (I := I) g₁) x v0 p q) v1 := by
  rw [riemannMixedKernelBilin, LinearMap.coe_toContinuousLinearMap', LinearMap.coe_mk,
    AddHom.coe_mk]

def riemannMixedSummandFib (g₀ g₁ : SmoothRiemannianMetric I M) (x : M)
    (p q : TangentSpace I x) :
    Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x :=
  haveI : FiniteDimensional ℝ (Tensor0SSpace 2 I x) := inferInstance
  LinearMap.toContinuousLinearMap
    { toFun := fun D =>
        (Tensor0SSpace.toModel D
          ![tangentSpaceModelContinuousLinearEquiv (I := I) x p,
            tangentSpaceModelContinuousLinearEquiv (I := I) x q]) •
          Tensor0SSpace.ofModel (I := I) (x := x)
            (biForm₂ToModel E
              (tangentBilinearFormToModel (I := I) x
                (riemannMixedKernelBilin (I := I) g₀ g₁ x p q)))
      map_add' := fun D D' => by
        rw [Tensor0SSpace.toModel_add, add_apply, add_smul]
      map_smul' := fun c D => by
        rw [Tensor0SSpace.toModel_smul, smul_apply, smul_eq_mul,
          RingHom.id_apply, mul_smul] }

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [SigmaCompactSpace M] in
@[simp] theorem riemannMixedSummandFib_toModel (g₀ g₁ : SmoothRiemannianMetric I M) (x : M)
    (p q : TangentSpace I x) (D : Tensor0SSpace 2 I x) (v : Fin 2 → E) :
    Tensor0SSpace.toModel (riemannMixedSummandFib (I := I) g₀ g₁ x p q D) v =
      (Tensor0SSpace.toModel D
        ![tangentSpaceModelContinuousLinearEquiv (I := I) x p,
          tangentSpaceModelContinuousLinearEquiv (I := I) x q]) *
        g₀.inner x (riemannOp (LeviCivita (I := I) g₁) x
          ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm (v 0)) p q)
          ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm (v 1)) := by
  rw [riemannMixedSummandFib, LinearMap.coe_toContinuousLinearMap', LinearMap.coe_mk,
    AddHom.coe_mk, Tensor0SSpace.toModel_smul, smul_apply,
    Tensor0SSpace.toModel_ofModel, biForm₂ToModel_apply,
    tangentBilinearFormToModel_apply, smul_eq_mul, riemannMixedKernelBilin_apply]

def riemannMixedBiContrFibFixedFrame (g₀ g₁ : SmoothRiemannianMetric I M)
    (B : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b) (x : M) :
    Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x :=
  (2 : ℝ) • ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
    riemannMixedSummandFib (I := I) g₀ g₁ x (B a x) (B b x)

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [SigmaCompactSpace M] in
theorem riemannMixedBiContrFibFixedFrame_toModel (g₀ g₁ : SmoothRiemannianMetric I M)
    (B : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b) (x : M)
    (D : Tensor0SSpace 2 I x) (v : Fin 2 → E) :
    Tensor0SSpace.toModel (riemannMixedBiContrFibFixedFrame (I := I) g₀ g₁ B x D) v =
      2 * ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
        g₀.inner x (riemannOp (LeviCivita (I := I) g₁) x
          ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm (v 0))
          (B a x) (B b x))
          ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm (v 1)) *
          Tensor0SSpace.toModel D
            ![tangentSpaceModelContinuousLinearEquiv (I := I) x (B a x),
              tangentSpaceModelContinuousLinearEquiv (I := I) x (B b x)] := by
  classical
  rw [riemannMixedBiContrFibFixedFrame, smul_apply,
    Tensor0SSpace.toModel_smul, smul_apply, smul_eq_mul]
  congr 1
  rw [sum_apply, ← Tensor0SSpace.toModelL_apply, map_sum,
    sum_apply]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [sum_apply, Tensor0SSpace.toModelL_apply, ← Tensor0SSpace.toModelL_apply,
    map_sum, sum_apply]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  rw [Tensor0SSpace.toModelL_apply, riemannMixedSummandFib_toModel]
  ring

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [SigmaCompactSpace M] in
theorem mixedKernelScalar_global (g₀ g₁ : SmoothRiemannianMetric I M)
    {Y W p q : Π b : M, TangentSpace I b}
    (hY : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Y))
    (hW : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% W))
    (hp : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% p))
    (hq : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% q)) :
    ContMDiff I 𝓘(ℝ, ℝ) ∞
      (fun x : M => g₀.inner x
        (riemannOp (LeviCivita (I := I) g₁) x (Y x) (p x) (q x)) (W x)) := by
  classical
  have hRsec : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (T% (fun b : M => riemannSec (LeviCivita (I := I) g₁) Y p q b)) :=
    riemannSec_contMDiff (cov := LeviCivita (I := I) g₁) hY hp hq
  have hcongr : (fun x : M => g₀.inner x
        (riemannOp (LeviCivita (I := I) g₁) x (Y x) (p x) (q x)) (W x)) =
      (fun x : M => g₀.inner x (riemannSec (LeviCivita (I := I) g₁) Y p q x) (W x)) := by
    funext x
    rw [riemannOp_apply_smooth (cov := LeviCivita (I := I) g₁) hY hp hq]
  rw [hcongr]
  exact contMDiff_g_inner_of_smooth_sections (I := I) g₀
    ⟨fun b => riemannSec (LeviCivita (I := I) g₁) Y p q b, hRsec⟩ ⟨fun b => W b, hW⟩

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
omit [SigmaCompactSpace M] in
theorem riemannMixedKernelBilin_homSection_contMDiff (g₀ g₁ : SmoothRiemannianMetric I M)
    {p q : Π b : M, TangentSpace I b}
    (hp : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% p))
    (hq : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% q)) :
    ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun x : M => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun b : M => TangentSpace I b →L[ℝ] TangentSpace I b →L[ℝ] ℝ)
        x (riemannMixedKernelBilin (I := I) g₀ g₁ x (p x) (q x))) := by
  classical
  apply contMDiff_continuousLinearMap_section_of_apply
    (V₂ := fun x : M => TangentSpace I x →L[ℝ] ℝ)
    (φ := fun x : M => riemannMixedKernelBilin (I := I) g₀ g₁ x (p x) (q x))
  intro Y
  apply contMDiff_continuousLinearMap_section_of_apply
    (V₂ := fun _ : M => ℝ)
    (φ := fun x : M => riemannMixedKernelBilin (I := I) g₀ g₁ x (p x) (q x) (Y x))
  intro W
  have h_scalar := mixedKernelScalar_global (I := I) g₀ g₁ Y.contMDiff W.contMDiff hp hq
  intro x
  rw [contMDiffAt_section]
  refine (h_scalar.contMDiffAt).congr_of_eventuallyEq ?_
  filter_upwards with y
  change riemannMixedKernelBilin (I := I) g₀ g₁ y (p y) (q y) (Y y) (W y) =
    (trivializationAt ℝ (Bundle.Trivial M ℝ) x ⟨y, _⟩).2
  rw [riemannMixedKernelBilin_apply]
  rfl

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
omit [SigmaCompactSpace M] in
theorem riemannMixedBiContrFibFixedFrame_apply_section_contMDiff
    (g₀ g₁ : SmoothRiemannianMetric I M)
    (B : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b)
    (hB : ∀ i, ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% (B i)))
    (Y : Cₛ^∞⟮I; Tensor0SModel 2 ℝ E, fun x : M => Tensor0SSpace 2 I x⟯) :
    ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel 2 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SModel 2 ℝ E)
        (E := fun z : M => Tensor0SSpace 2 I z) x
        (riemannMixedBiContrFibFixedFrame (I := I) g₀ g₁ B x (Y x))) := by
  classical
  have hsummand : ∀ a b : Fin (Module.finrank ℝ E),
      ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel 2 ℝ E)) ∞
        (fun x : M => TotalSpace.mk' (Tensor0SModel 2 ℝ E)
          (E := fun z : M => Tensor0SSpace 2 I z) x
          (riemannMixedSummandFib (I := I) g₀ g₁ x (B a x) (B b x) (Y x))) := by
    intro a b
    have hscalar : ContMDiff I 𝓘(ℝ, ℝ) ∞
        (fun x : M => Tensor0SSpace.toModel (Y x) ![(B a x : E), (B b x : E)]) := by
      have h := TensorMultilinear.contMDiff_section_apply (n := 2)
        (fun b => Y b) Y.contMDiff
        (![fun z => B a z, fun z => B b z])
        (by
          intro i
          fin_cases i
          · exact hB a
          · exact hB b)
      refine h.congr ?_
      intro x
      congr 1
      funext i
      fin_cases i <;> rfl
    have hbilin := contMDiff_bilinSection_of_homSection (I := I)
      (fun x => riemannMixedKernelBilin (I := I) g₀ g₁ x (B a x) (B b x))
      (riemannMixedKernelBilin_homSection_contMDiff (I := I) g₀ g₁ (hB a) (hB b))
    have hsmul := ContMDiff.smul_section (f := fun x => Tensor0SSpace.toModel (Y x)
        ![(B a x : E), (B b x : E)])
      (s := fun x => Tensor0SSpace.ofModel (I := I) (x := x)
        (biForm₂ToModel (TangentSpace I x)
          (riemannMixedKernelBilin (I := I) g₀ g₁ x (B a x) (B b x))))
      hscalar hbilin
    refine hsmul.congr ?_
    intro x
    rfl
  set S : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) →
      Cₛ^∞⟮I; Tensor0SModel 2 ℝ E, fun z : M => Tensor0SSpace 2 I z⟯ :=
    fun a b =>
      { toFun := fun x : M => riemannMixedSummandFib (I := I) g₀ g₁ x (B a x) (B b x) (Y x)
        contMDiff_toFun := hsummand a b } with hS_def
  set Stot : Cₛ^∞⟮I; Tensor0SModel 2 ℝ E, fun z : M => Tensor0SSpace 2 I z⟯ :=
    (2 : ℝ) • ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E), S a b
    with hStot_def
  have hStot := Stot.contMDiff
  refine hStot.congr ?_
  intro x
  refine congrArg (TotalSpace.mk' (Tensor0SModel 2 ℝ E)
    (E := fun z : M => Tensor0SSpace 2 I z) x) ?_
  rw [riemannMixedBiContrFibFixedFrame, hStot_def, ContMDiffSection.coe_smul, Pi.smul_apply]
  have hcoeOuter : ((∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E), S a b :
      Cₛ^∞⟮I; Tensor0SModel 2 ℝ E, fun z : M => Tensor0SSpace 2 I z⟯) :
        Π z : M, Tensor0SSpace 2 I z) =
      ∑ a : Fin (Module.finrank ℝ E),
        ((∑ b : Fin (Module.finrank ℝ E), S a b :
          Cₛ^∞⟮I; Tensor0SModel 2 ℝ E, fun z : M => Tensor0SSpace 2 I z⟯) :
          Π z : M, Tensor0SSpace 2 I z) :=
    map_sum (ContMDiffSection.coeAddHom I (Tensor0SModel 2 ℝ E) ∞
      (fun z : M => Tensor0SSpace 2 I z))
      (fun a => ∑ b : Fin (Module.finrank ℝ E), S a b) Finset.univ
  have hcoeInner : ∀ a : Fin (Module.finrank ℝ E),
      ((∑ b : Fin (Module.finrank ℝ E), S a b :
        Cₛ^∞⟮I; Tensor0SModel 2 ℝ E, fun z : M => Tensor0SSpace 2 I z⟯) :
        Π z : M, Tensor0SSpace 2 I z) =
      ∑ b : Fin (Module.finrank ℝ E), ((S a b : Π z : M, Tensor0SSpace 2 I z)) := fun a =>
    map_sum (ContMDiffSection.coeAddHom I (Tensor0SModel 2 ℝ E) ∞
      (fun z : M => Tensor0SSpace 2 I z)) (fun b => S a b) Finset.univ
  have hsum : ((∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E), S a b :
      Cₛ^∞⟮I; Tensor0SModel 2 ℝ E, fun z : M => Tensor0SSpace 2 I z⟯) :
        Π z : M, Tensor0SSpace 2 I z) x =
      ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
        (S a b : Π z : M, Tensor0SSpace 2 I z) x := by
    rw [hcoeOuter, Finset.sum_apply]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [hcoeInner a, Finset.sum_apply]
  rw [hsum, smul_apply, sum_apply]
  congr 1
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [sum_apply]
  rfl

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
omit [SigmaCompactSpace M] in
theorem riemannMixedBiContrFibFixedFrame_contMDiff (g₀ g₁ : SmoothRiemannianMetric I M)
    (B : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b)
    (hB : ∀ i, ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% (B i))) :
    ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel 2 2 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel 2 2 ℝ E)
        (E := fun z : M => TensorRSSpace 2 2 I z) x
        (TensorRSSpace.ofCLM (riemannMixedBiContrFibFixedFrame (I := I) g₀ g₁ B x))) := by
  classical
  apply contMDiff_clm_section_of_pointwise (I := I) (M := M)
    (F₁ := Tensor0SModel 2 ℝ E) (V₁ := fun z : M => Tensor0SSpace 2 I z)
    (F₂ := Tensor0SModel 2 ℝ E) (V₂ := fun z : M => Tensor0SSpace 2 I z)
    (φ := fun x : M => riemannMixedBiContrFibFixedFrame (I := I) g₀ g₁ B x)
  intro Y
  exact riemannMixedBiContrFibFixedFrame_apply_section_contMDiff (I := I) g₀ g₁ B hB Y

def frameRiemannMixedKernel (g₀ g₁ : SmoothRiemannianMetric I M) (x : M)
    (v0 v1 : TangentSpace I x) :
    TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ :=
  haveI : FiniteDimensional ℝ (TangentSpace I x) := inferInstanceAs (FiniteDimensional ℝ E)
  LinearMap.toContinuousLinearMap
    { toFun := fun p => (g₀.inner x).flip v1 |>.comp
        ((riemannOp (LeviCivita (I := I) g₁) x v0 p))
      map_add' := fun p p' => by
        ext q
        simp only [ContinuousLinearMap.comp_apply, add_apply,
          (riemannOp (LeviCivita (I := I) g₁) x v0).map_add p p', map_add]
      map_smul' := fun c p => by
        ext q
        simp only [ContinuousLinearMap.comp_apply, smul_apply,
          RingHom.id_apply, (riemannOp (LeviCivita (I := I) g₁) x v0).map_smul c p, map_smul] }

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [SigmaCompactSpace M] in
theorem frameRiemannMixedKernel_apply (g₀ g₁ : SmoothRiemannianMetric I M) (x : M)
    (v0 v1 p q : TangentSpace I x) :
    frameRiemannMixedKernel (I := I) g₀ g₁ x v0 v1 p q =
      g₀.inner x (riemannOp (LeviCivita (I := I) g₁) x v0 p q) v1 := by
  rw [frameRiemannMixedKernel, LinearMap.coe_toContinuousLinearMap', LinearMap.coe_mk,
    AddHom.coe_mk, ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply]

def riemannMixedBiContrFib (g₀ g₁ : SmoothRiemannianMetric I M) (x : M) :
    Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x :=
  riemannMixedBiContrFibFixedFrame (I := I) g₀ g₁ (smoothOrthoFrame (I := I) g₀ x) x

omit [CompactSpace M] [I.Boundaryless] [SigmaCompactSpace M] in
theorem riemannMixedBiContrFib_eq_fixedFrame_on_nbhd (g₀ g₁ : SmoothRiemannianMetric I M)
    (x₀ : M) {y : M} (hy : y ∈ smoothOrthoFrameNbhd (I := I) (M := M) x₀) :
    riemannMixedBiContrFib (I := I) (M := M) g₀ g₁ y =
      riemannMixedBiContrFibFixedFrame (I := I) g₀ g₁ (smoothOrthoFrame (I := I) g₀ x₀) y := by
  classical
  apply ContinuousLinearMap.ext
  intro D
  apply Tensor0SSpace.toModel_injective
  apply ContinuousMultilinearMap.ext
  intro v
  rw [riemannMixedBiContrFib, riemannMixedBiContrFibFixedFrame_toModel,
    riemannMixedBiContrFibFixedFrame_toModel]
  apply congrArg (fun z : ℝ => 2 * z)
  let : IsManifold I 1 M :=
    IsManifold.of_le (I := I) (M := M) (n := (∞ : WithTop ℕ∞))
      (by decide : (1 : WithTop ℕ∞) ≤ (∞ : WithTop ℕ∞))
  let vt : Fin 2 → TangentSpace I y :=
    fun i => (tangentSpaceModelContinuousLinearEquiv (I := I) y).symm (v i)
  let Dd : TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ :=
    (biForm₂ToModel (TangentSpace I y)).symm
      (tensor0SSpaceFiberContinuousLinearEquiv (I := I) 2 y D)
  have hrewrite : ∀ (Bf : Fin (Module.finrank ℝ E) → TangentSpace I y),
      ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
        g₀.inner y (riemannOp (LeviCivita (I := I) g₁) y (vt 0) (Bf a) (Bf b)) (vt 1) *
          Tensor0SSpace.toModel D
            ![tangentSpaceModelContinuousLinearEquiv (I := I) y (Bf a),
              tangentSpaceModelContinuousLinearEquiv (I := I) y (Bf b)] =
      ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
        frameRiemannMixedKernel (I := I) g₀ g₁ y (vt 0) (vt 1) (Bf a) (Bf b) *
          Dd (Bf a) (Bf b) := by
    intro Bf
    refine Finset.sum_congr rfl (fun a _ => ?_)
    refine Finset.sum_congr rfl (fun b _ => ?_)
    rw [frameRiemannMixedKernel_apply (I := I) g₀ g₁ y (vt 0) (vt 1) (Bf a) (Bf b)]
    dsimp only [Dd]
    rw [biForm₂ToModel_symm_apply]
    rfl
  rw [hrewrite (fun a => smoothOrthoFrame (I := I) g₀ y a y),
    hrewrite (fun a => smoothOrthoFrame (I := I) g₀ x₀ a y)]
  exact double_frame_bilin_trace_indep (I := I) g₀ y
    (frameRiemannMixedKernel (I := I) g₀ g₁ y (vt 0) (vt 1))
    Dd
    (fun a => smoothOrthoFrame (I := I) g₀ y a y)
    (fun a => smoothOrthoFrame (I := I) g₀ x₀ a y)
    (fun i j => smoothOrthoFrame_orthonormal_at_center (I := I) g₀ y i j)
    (fun i j => smoothOrthoFrame_orthonormal (I := I) g₀ x₀ hy i j)

omit [CompactSpace M] [I.Boundaryless] in
omit [SigmaCompactSpace M] in
theorem riemannMixedBiContrFib_contMDiff (g₀ g₁ : SmoothRiemannianMetric I M) :
    ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel 2 2 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel 2 2 ℝ E)
        (E := fun z : M => TensorRSSpace 2 2 I z) x
        (TensorRSSpace.ofCLM (riemannMixedBiContrFib (I := I) (M := M) g₀ g₁ x))) := by
  classical
  intro x₀
  have h_fixed : ContMDiffAt I (I.prod 𝓘(ℝ, TensorRSModel 2 2 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel 2 2 ℝ E)
        (E := fun z : M => TensorRSSpace 2 2 I z) x
        (TensorRSSpace.ofCLM (riemannMixedBiContrFibFixedFrame (I := I) g₀ g₁
          (smoothOrthoFrame (I := I) g₀ x₀) x))) x₀ :=
    riemannMixedBiContrFibFixedFrame_contMDiff (I := I) g₀ g₁ (smoothOrthoFrame (I := I) g₀ x₀)
      (fun i => smoothOrthoFrame_smooth (I := I) g₀ x₀ i) x₀
  refine h_fixed.congr_of_eventuallyEq ?_
  filter_upwards [smoothOrthoFrameNbhd_mem_nhds (I := I) (M := M) x₀] with y hy
  exact congrArg (TotalSpace.mk' (TensorRSModel 2 2 ℝ E)
    (E := fun z : M => TensorRSSpace 2 2 I z) y)
    (congrArg TensorRSSpace.ofCLM
      (riemannMixedBiContrFib_eq_fixedFrame_on_nbhd (I := I) g₀ g₁ x₀ hy))

def ricciOrderZeroRiemannMixedCoeff (g₀ g₁ : SmoothRiemannianMetric I M) :
    SmoothCcTensor g₀ 2 2 where
  toSection :=
    { toFun := fun x : M =>
        (show TensorRSSpace 2 2 I x from
          TensorRSSpace.ofCLM (riemannMixedBiContrFib (I := I) (M := M) g₀ g₁ x))
      contMDiff_toFun := riemannMixedBiContrFib_contMDiff (I := I) (M := M) g₀ g₁ }
  hasCompactSupport := HasCompactSupport.of_compactSpace _

omit [I.Boundaryless] in
omit [SigmaCompactSpace M] in
theorem ricciOrderZeroRiemannMixedCoeff_toSection (g₀ g₁ : SmoothRiemannianMetric I M) (x : M) :
    (ricciOrderZeroRiemannMixedCoeff (I := I) (M := M) g₀ g₁).toSection x =
      (show TensorRSSpace 2 2 I x from
        TensorRSSpace.ofCLM (riemannMixedBiContrFib (I := I) (M := M) g₀ g₁ x)) := rfl

omit [I.Boundaryless] in
omit [SigmaCompactSpace M] in
theorem ricciOrderZeroRiemannMixedCoeff_self (g₀ : SmoothRiemannianMetric I M) :
    ricciOrderZeroRiemannMixedCoeff (I := I) (M := M) g₀ g₀ =
      ricciOrderZeroRiemannCoeff (I := I) (M := M) g₀ g₀ := by
  classical
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  apply ContinuousLinearMap.ext
  intro D
  apply Tensor0SSpace.toModel_injective
  apply ContinuousMultilinearMap.ext
  intro v
  rw [show ((ricciOrderZeroRiemannMixedCoeff (I := I) (M := M) g₀ g₀).toSection x) D =
      riemannMixedBiContrFib (I := I) (M := M) g₀ g₀ x D from rfl]
  rw [show ((ricciOrderZeroRiemannCoeff (I := I) (M := M) g₀ g₀).toSection x) D =
      riemannBiContrFib (I := I) g₀ x D from rfl]
  rw [riemannMixedBiContrFib, riemannBiContrFib, riemannMixedBiContrFibFixedFrame_toModel,
    riemannBiContrFibFixedFrame_toModel]

end RiemannMixedBiContr

end Spectral
end Analysis
end DifferentialGeometry

end
