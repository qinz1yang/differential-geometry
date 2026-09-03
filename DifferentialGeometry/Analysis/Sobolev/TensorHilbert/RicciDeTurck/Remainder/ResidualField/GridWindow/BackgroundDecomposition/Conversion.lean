import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.ResidualCoefficient.Decomposition
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.OperatorFieldInputSlotSymmetrization
import DifferentialGeometry.Analysis.Sobolev.BoundedFactorProductGrid
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.MetricPerturbation.ArmCoefficient.ReindexingNorm
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.MetricLoweredConnectionDifferenceCoefficient
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.RicciDeTurck.Remainder.ResidualField.GridWindow.InverseMetricQuadraticResidual
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.RicciDeTurck.Remainder.ResidualField.GridWindow.BackgroundDecomposition.MultilinearIdentities
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.RicciDeTurck.Remainder.ResidualField.GridWindow.BackgroundDecomposition.FibreNormBounds
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.RicciDeTurck.Remainder.ResidualField.GridWindow.BackgroundDecomposition.DoubleTraceFold
open DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Analysis.Elliptic
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Operator

noncomputable section


open Bundle Manifold Set Filter DifferentialGeometry.Tensor0SBundle MeasureTheory
open scoped Manifold Topology ContDiff BigOperators

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2

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

section bgrConversion

open DifferentialGeometry.Analysis.Sobolev.TensorHilbert

variable (g₀ g₁ : SmoothRiemannianMetric I M)

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] [SigmaCompactSpace M] in
lemma metricDifferenceCcTensor_eq_symmS (P : SmoothCcTensor g₀ 0 2)
    (htie : ∀ (y : M) (v w : TangentSpace I y),
      g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w) :
    metricDifferenceCcTensor (I := I) (M := M) g₀ g₁ = ccTensor02Symm (I := I) g₀ P := by
  apply smoothCcTensor_ext_of_unitModel (I := I) (M := M) g₀
  intro x
  apply ContinuousMultilinearMap.ext
  intro m
  rw [show metricDifferenceCcTensor (I := I) (M := M) g₀ g₁ =
      metricCcTensor (I := I) (M := M) g₀ g₁ - metricCcTensor (I := I) (M := M) g₀ g₀ from rfl]
  rw [DifferentialGeometry.Analysis.Parabolic.TensorSpectral.unitModel_sub (I := I) (M := M) g₀ 2
    (metricCcTensor (I := I) (M := M) g₀ g₁) (metricCcTensor (I := I) (M := M) g₀ g₀) x]
  rw [sub_apply]
  rw [metricCcTensor_unitModel_apply (I := I) (M := M) g₀ g₁ x m,
    metricCcTensor_unitModel_apply (I := I) (M := M) g₀ g₀ x m]
  rw [show unitModel (I := I) (M := M) g₀ 2 (ccTensor02Symm (I := I) g₀ P) x m =
      unitModel (I := I) (M := M) g₀ 2 (ccTensor02Symm (I := I) g₀ P) x ![m 0, m 1] from by
    refine congrArg _ ?_
    funext k
    fin_cases k <;> rfl]
  rw [unitModel_eq_ccTensorBilin_pt (I := I) (M := M) g₀ (ccTensor02Symm (I := I) g₀ P) x (m 0)
    (m 1)]
  rw [ccTensorBilin_symmS (I := I) (M := M) g₀ P x (m 0) (m 1)]
  rw [htie x (m 0) (m 1)]
  ring

def ricciFoldWeightA (S : SmoothCcTensor g₀ 0 2) : SmoothCcTensor g₀ 0 4 :=
  ccOperatorFieldComp (I := I) (M := M) g₀ 0 6 4 (cometricDoubleTraceField (I := I) g₀ 4)
    (rsDomDomCongrSection (I := I) (M := M) g₀ 0 6 (Equiv.swap (1 : Fin 6) 3)
      (ccOperatorFieldComp (I := I) (M := M) g₀ 0 2 6
        (slotExtendIter (I := I) (M := M) g₀ 0 4 2
          (riemannLoweredCc (I := I) (M := M) g₀ g₀ g₀)) S))

def ricciFoldWeightB (S : SmoothCcTensor g₀ 0 2) : SmoothCcTensor g₀ 0 4 :=
  ccOperatorFieldComp (I := I) (M := M) g₀ 0 6 4 (cometricDoubleTraceField (I := I) g₀ 4)
    (rsDomDomCongrSection (I := I) (M := M) g₀ 0 6 ricciFoldWeightBPerm
      (ccOperatorFieldComp (I := I) (M := M) g₀ 0 2 6
        (slotExtendIter (I := I) (M := M) g₀ 0 4 2
          (riemannLoweredCc (I := I) (M := M) g₀ g₀ g₀)) S))

omit [SigmaCompactSpace M] in
omit [I.Boundaryless] in
private lemma ricciFoldWeight_unitModel_gen (σ : Equiv.Perm (Fin 6))
    (S : SmoothCcTensor g₀ 0 2) (x : M) (m : Fin 4 → E) :
    unitModel (I := I) (M := M) g₀ 4
        (ccOperatorFieldComp (I := I) (M := M) g₀ 0 6 4 (cometricDoubleTraceField (I := I) g₀ 4)
          (rsDomDomCongrSection (I := I) (M := M) g₀ 0 6 σ
            (ccOperatorFieldComp (I := I) (M := M) g₀ 0 2 6
              (slotExtendIter (I := I) (M := M) g₀ 0 4 2
                (riemannLoweredCc (I := I) (M := M) g₀ g₀ g₀)) S))) x m =
      ∑ e : Fin (Module.finrank ℝ E),
        unitModel (I := I) (M := M) g₀ 2 S x
            ![((Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
                (Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E) m) :
                  Fin 6 → E) (σ 0)),
              ((Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
                (Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E) m) :
                  Fin 6 → E) (σ 1))] *
          unitModel (I := I) (M := M) g₀ 4
            (riemannLoweredCc (I := I) (M := M) g₀ g₀ g₀) x
            ![((Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
                (Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E) m) :
                  Fin 6 → E) (σ 2)),
              ((Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
                (Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E) m) :
                  Fin 6 → E) (σ 3)),
              ((Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
                (Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E) m) :
                  Fin 6 → E) (σ 4)),
              ((Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
                (Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E) m) :
                  Fin 6 → E) (σ 5))] := by
  classical
  set R4 : SmoothCcTensor g₀ 0 4 := riemannLoweredCc (I := I) (M := M) g₀ g₀ g₀ with hR4_def
  set Sval : Tensor0SSpace 2 I x :=
    (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from S.toSection x)
      (unitTensor (I := I) (M := M) x) with hSval_def
  set Y : Tensor0SSpace 6 I x :=
    (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 6 I x from
      (rsDomDomCongrSection (I := I) (M := M) g₀ 0 6 σ
        (ccOperatorFieldComp (I := I) (M := M) g₀ 0 2 6
          (slotExtendIter (I := I) (M := M) g₀ 0 4 2 R4) S)).toSection x)
      (unitTensor (I := I) (M := M) x) with hY_def
  have hYval : ∀ w : Fin 6 → E,
      Tensor0SSpace.toModel Y w =
        Tensor0SSpace.toModel Sval ![(w (σ 0) : E), (w (σ 1) : E)] *
          unitModel (I := I) (M := M) g₀ 4 R4 x
            ![(w (σ 2) : E), (w (σ 3) : E), (w (σ 4) : E), (w (σ 5) : E)] := by
    intro w
    rw [hY_def]
    rw [show ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 6 I x from
        (rsDomDomCongrSection (I := I) (M := M) g₀ 0 6 σ
          (ccOperatorFieldComp (I := I) (M := M) g₀ 0 2 6
            (slotExtendIter (I := I) (M := M) g₀ 0 4 2 R4) S)).toSection x)
        (unitTensor (I := I) (M := M) x)) =
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 6 I x from
          tensorRSDomDomCongr σ
            ((ccOperatorFieldComp (I := I) (M := M) g₀ 0 2 6
              (slotExtendIter (I := I) (M := M) g₀ 0 4 2 R4) S).toSection x))
          (unitTensor (I := I) (M := M) x)) from by
      rw [rsDomDomCongrSection_toSection]]
    rw [toModel_rsDomDomCongr_apply (I := I) (M := M) σ
      ((ccOperatorFieldComp (I := I) (M := M) g₀ 0 2 6
        (slotExtendIter (I := I) (M := M) g₀ 0 4 2 R4) S).toSection x)
      (unitTensor (I := I) (M := M) x)]
    rw [ContinuousMultilinearMap.domDomCongr_apply]
    rw [show ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 6 I x from
        (ccOperatorFieldComp (I := I) (M := M) g₀ 0 2 6
          (slotExtendIter (I := I) (M := M) g₀ 0 4 2 R4) S).toSection x)
        (unitTensor (I := I) (M := M) x)) =
        ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 6 I x from
          (slotExtendIter (I := I) (M := M) g₀ 0 4 2 R4).toSection x) Sval) from by
      rw [operatorFieldComposition_toSection]
      rfl]
    rw [slotExtendIter_two_toModel (I := I) (M := M) g₀ R4 x Sval (fun i => w (σ i))]
    refine congrArg₂ (· * ·) ?_ ?_
    · refine congrArg _ ?_
      funext k
      fin_cases k <;> rfl
    · rw [show unitModel (I := I) (M := M) g₀ 4 R4 x
          (fun k : Fin 4 => ((fun i => w (σ i)) (Fin.natAdd 2 k) : E)) =
          unitModel (I := I) (M := M) g₀ 4 R4 x
            ![(w (σ 2) : E), (w (σ 3) : E), (w (σ 4) : E), (w (σ 5) : E)] from by
        refine congrArg _ ?_
        funext k
        fin_cases k <;> rfl]
  rw [show unitModel (I := I) (M := M) g₀ 4
      (ccOperatorFieldComp (I := I) (M := M) g₀ 0 6 4 (cometricDoubleTraceField (I := I) g₀ 4)
        (rsDomDomCongrSection (I := I) (M := M) g₀ 0 6 σ
          (ccOperatorFieldComp (I := I) (M := M) g₀ 0 2 6
            (slotExtendIter (I := I) (M := M) g₀ 0 4 2 R4) S))) x =
      Tensor0SSpace.toModel (cometricDoubleTraceFib (I := I) g₀ 4 x Y) from by
    rw [unitModel, hY_def]
    rw [operatorFieldComposition_toSection]
    rfl]
  rw [cometricDoubleTraceFib_toModel (I := I) g₀ 4 x Y]
  rw [modelDoubleTrace_apply (E := E) 4 (cometricLmodel (I := I) g₀ x)]
  rw [cometric_dualTrace_eq_orthoFrame_diag (I := I) g₀ x
    (mem_smoothOrthoFrameNbhd_self (I := I) (M := M) x)
    (Tensor0SSpace.toModel Y) m]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [hYval]
  rfl

omit [SigmaCompactSpace M] in
omit [I.Boundaryless] in
private lemma ricciFoldWeights_unitModel_eq_kernel (S : SmoothCcTensor g₀ 0 2) (x : M)
    (p q v0 v1 : TangentSpace I x) :
    unitModel (I := I) (M := M) g₀ 4
        (ricciFoldWeightA (I := I) (M := M) g₀ S +
          ricciFoldWeightB (I := I) (M := M) g₀ S) x
        ![(v0 : E), (v1 : E), (p : E), (q : E)] =
      smoothCcTensorBilinForm (I := I) g₀ S x (riemannOp (LeviCivita (I := I) g₀) x v0 p q) v1 +
        smoothCcTensorBilinForm (I := I) g₀ S x q
          (riemannOp (LeviCivita (I := I) g₀) x v0 p v1) := by
  classical
  rw [DifferentialGeometry.Analysis.Parabolic.TensorSpectral.unitModel_add (I := I) (M := M) g₀ 4
    (ricciFoldWeightA (I := I) (M := M) g₀ S) (ricciFoldWeightB (I := I) (M := M) g₀ S) x,
    add_apply]
  have hA : unitModel (I := I) (M := M) g₀ 4 (ricciFoldWeightA (I := I) (M := M) g₀ S) x
      ![(v0 : E), (v1 : E), (p : E), (q : E)] =
      smoothCcTensorBilinForm (I := I) g₀ S x (riemannOp (LeviCivita (I := I) g₀) x v0 p q) v1 := by
    rw [show ricciFoldWeightA (I := I) (M := M) g₀ S =
        ccOperatorFieldComp (I := I) (M := M) g₀ 0 6 4 (cometricDoubleTraceField (I := I) g₀ 4)
          (rsDomDomCongrSection (I := I) (M := M) g₀ 0 6 (Equiv.swap (1 : Fin 6) 3)
            (ccOperatorFieldComp (I := I) (M := M) g₀ 0 2 6
              (slotExtendIter (I := I) (M := M) g₀ 0 4 2
                (riemannLoweredCc (I := I) (M := M) g₀ g₀ g₀)) S)) from rfl]
    rw [ricciFoldWeight_unitModel_gen (I := I) (M := M) g₀ (Equiv.swap (1 : Fin 6) 3) S x
      ![(v0 : E), (v1 : E), (p : E), (q : E)]]
    rw [tensorBilinearPairing_expand_left (I := I) (M := M) g₀ S x
      (riemannOp (LeviCivita (I := I) g₀) x v0 p q) v1]
    refine Finset.sum_congr rfl fun e _ => ?_
    have h1 : unitModel (I := I) (M := M) g₀ 2 S x
        ![((Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
            (Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
              ![(v0 : E), (v1 : E), (p : E), (q : E)]) : Fin 6 → E)
            ((Equiv.swap (1 : Fin 6) 3) 0)),
          ((Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
            (Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
              ![(v0 : E), (v1 : E), (p : E), (q : E)]) : Fin 6 → E)
            ((Equiv.swap (1 : Fin 6) 3) 1))] =
        unitModel (I := I) (M := M) g₀ 2 S x
          ![((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E), (v1 : E)] := by
      refine congrArg _ ?_
      funext k
      fin_cases k <;> rfl
    have h2 : unitModel (I := I) (M := M) g₀ 4
        (riemannLoweredCc (I := I) (M := M) g₀ g₀ g₀) x
        ![((Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
            (Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
              ![(v0 : E), (v1 : E), (p : E), (q : E)]) : Fin 6 → E)
            ((Equiv.swap (1 : Fin 6) 3) 2)),
          ((Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
            (Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
              ![(v0 : E), (v1 : E), (p : E), (q : E)]) : Fin 6 → E)
            ((Equiv.swap (1 : Fin 6) 3) 3)),
          ((Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
            (Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
              ![(v0 : E), (v1 : E), (p : E), (q : E)]) : Fin 6 → E)
            ((Equiv.swap (1 : Fin 6) 3) 4)),
          ((Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
            (Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
              ![(v0 : E), (v1 : E), (p : E), (q : E)]) : Fin 6 → E)
            ((Equiv.swap (1 : Fin 6) 3) 5))] =
        g₀.inner x (riemannOp (LeviCivita (I := I) g₀) x v0 p q)
          (smoothOrthoFrame (I := I) g₀ x e x) := by
      rw [show (![((Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
            (Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
              ![(v0 : E), (v1 : E), (p : E), (q : E)]) : Fin 6 → E)
            ((Equiv.swap (1 : Fin 6) 3) 2)),
          ((Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
            (Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
              ![(v0 : E), (v1 : E), (p : E), (q : E)]) : Fin 6 → E)
            ((Equiv.swap (1 : Fin 6) 3) 3)),
          ((Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
            (Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
              ![(v0 : E), (v1 : E), (p : E), (q : E)]) : Fin 6 → E)
            ((Equiv.swap (1 : Fin 6) 3) 4)),
          ((Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
            (Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
              ![(v0 : E), (v1 : E), (p : E), (q : E)]) : Fin 6 → E)
            ((Equiv.swap (1 : Fin 6) 3) 5))] : Fin 4 → E) =
          ![(v0 : E), ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E),
            (p : E), (q : E)] from by
        funext k
        fin_cases k <;> rfl]
      have hr := riemannLoweredCc_unitModel_apply (I := I) (M := M) g₀ g₀ g₀ x
        ![(tangentSpaceModelContinuousLinearEquiv (I := I) x) v0,
          (tangentSpaceModelContinuousLinearEquiv (I := I) x)
            (smoothOrthoFrame (I := I) g₀ x e x),
          (tangentSpaceModelContinuousLinearEquiv (I := I) x) p,
          (tangentSpaceModelContinuousLinearEquiv (I := I) x) q]
      with_unfolding_all
        exact hr
    rw [h1, h2]
    rw [unitModel_eq_ccTensorBilin_pt (I := I) (M := M) g₀ S x
      (smoothOrthoFrame (I := I) g₀ x e x) v1]
    ring
  have hB : unitModel (I := I) (M := M) g₀ 4 (ricciFoldWeightB (I := I) (M := M) g₀ S) x
      ![(v0 : E), (v1 : E), (p : E), (q : E)] =
      smoothCcTensorBilinForm (I := I) g₀ S x q (riemannOp (LeviCivita (I := I) g₀) x v0 p v1) := by
    rw [show ricciFoldWeightB (I := I) (M := M) g₀ S =
        ccOperatorFieldComp (I := I) (M := M) g₀ 0 6 4 (cometricDoubleTraceField (I := I) g₀ 4)
          (rsDomDomCongrSection (I := I) (M := M) g₀ 0 6 ricciFoldWeightBPerm
            (ccOperatorFieldComp (I := I) (M := M) g₀ 0 2 6
              (slotExtendIter (I := I) (M := M) g₀ 0 4 2
                (riemannLoweredCc (I := I) (M := M) g₀ g₀ g₀)) S)) from rfl]
    rw [ricciFoldWeight_unitModel_gen (I := I) (M := M) g₀ ricciFoldWeightBPerm S x
      ![(v0 : E), (v1 : E), (p : E), (q : E)]]
    rw [tensorBilinearPairing_expand_right (I := I) (M := M) g₀ S x q
      (riemannOp (LeviCivita (I := I) g₀) x v0 p v1)]
    refine Finset.sum_congr rfl fun e _ => ?_
    have h1 : unitModel (I := I) (M := M) g₀ 2 S x
        ![((Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
            (Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
              ![(v0 : E), (v1 : E), (p : E), (q : E)]) : Fin 6 → E)
            (ricciFoldWeightBPerm 0)),
          ((Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
            (Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
              ![(v0 : E), (v1 : E), (p : E), (q : E)]) : Fin 6 → E)
            (ricciFoldWeightBPerm 1))] =
        unitModel (I := I) (M := M) g₀ 2 S x
          ![(q : E), ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)] := by
      refine congrArg _ ?_
      funext k
      fin_cases k <;> rfl
    have h2 : unitModel (I := I) (M := M) g₀ 4
        (riemannLoweredCc (I := I) (M := M) g₀ g₀ g₀) x
        ![((Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
            (Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
              ![(v0 : E), (v1 : E), (p : E), (q : E)]) : Fin 6 → E)
            (ricciFoldWeightBPerm 2)),
          ((Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
            (Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
              ![(v0 : E), (v1 : E), (p : E), (q : E)]) : Fin 6 → E)
            (ricciFoldWeightBPerm 3)),
          ((Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
            (Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
              ![(v0 : E), (v1 : E), (p : E), (q : E)]) : Fin 6 → E)
            (ricciFoldWeightBPerm 4)),
          ((Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
            (Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
              ![(v0 : E), (v1 : E), (p : E), (q : E)]) : Fin 6 → E)
            (ricciFoldWeightBPerm 5))] =
        g₀.inner x (riemannOp (LeviCivita (I := I) g₀) x v0 p v1)
          (smoothOrthoFrame (I := I) g₀ x e x) := by
      rw [show (![((Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
            (Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
              ![(v0 : E), (v1 : E), (p : E), (q : E)]) : Fin 6 → E)
            (ricciFoldWeightBPerm 2)),
          ((Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
            (Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
              ![(v0 : E), (v1 : E), (p : E), (q : E)]) : Fin 6 → E)
            (ricciFoldWeightBPerm 3)),
          ((Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
            (Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
              ![(v0 : E), (v1 : E), (p : E), (q : E)]) : Fin 6 → E)
            (ricciFoldWeightBPerm 4)),
          ((Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
            (Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
              ![(v0 : E), (v1 : E), (p : E), (q : E)]) : Fin 6 → E)
            (ricciFoldWeightBPerm 5))] : Fin 4 → E) =
          ![(v0 : E), ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E),
            (p : E), (v1 : E)] from by
        funext k
        fin_cases k <;> rfl]
      have hr := riemannLoweredCc_unitModel_apply (I := I) (M := M) g₀ g₀ g₀ x
        ![(tangentSpaceModelContinuousLinearEquiv (I := I) x) v0,
          (tangentSpaceModelContinuousLinearEquiv (I := I) x)
            (smoothOrthoFrame (I := I) g₀ x e x),
          (tangentSpaceModelContinuousLinearEquiv (I := I) x) p,
          (tangentSpaceModelContinuousLinearEquiv (I := I) x) v1]
      with_unfolding_all
        exact hr
    rw [h1, h2]
    rw [show unitModel (I := I) (M := M) g₀ 2 S x
        ![(q : E), ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)] =
        smoothCcTensorBilinForm (I := I) g₀ S x q (smoothOrthoFrame (I := I) g₀ x e x) from
      unitModel_eq_ccTensorBilin_pt (I := I) (M := M) g₀ S x q
        (smoothOrthoFrame (I := I) g₀ x e x)]
    ring
  rw [hA, hB]

omit [SigmaCompactSpace M] in
omit [I.Boundaryless] in
lemma ricciFoldRemainderField_eq_decomposition (S : SmoothCcTensor g₀ 0 2) :
    ricciArmRicciFoldRemainderField (I := I) (M := M) g₀ g₁ S =
      (-(1 / 2) : ℝ) •
        ccOperatorFieldComp (I := I) (M := M) g₀ 2 6 2
          (secondMetricPairTraceOperator (I := I) (M := M) g₀ g₁)
          (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 ricciFoldRemainderSlotPerm
            (slotExtendIter (I := I) (M := M) g₀ 0 4 2
              (ricciFoldWeightA (I := I) (M := M) g₀ S +
                ricciFoldWeightB (I := I) (M := M) g₀ S))) := by
  classical
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  apply tensorRSSpace_ext 2 2 x
  intro D
  apply Tensor0SSpace.toModel_injective
  apply ContinuousMultilinearMap.ext
  intro v
  beta_reduce
  have hRHSsmul : ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
      (((-(1 / 2) : ℝ) •
        ccOperatorFieldComp (I := I) (M := M) g₀ 2 6 2
          (secondMetricPairTraceOperator (I := I) (M := M) g₀ g₁)
          (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 ricciFoldRemainderSlotPerm
            (slotExtendIter (I := I) (M := M) g₀ 0 4 2
              (ricciFoldWeightA (I := I) (M := M) g₀ S +
                ricciFoldWeightB (I := I) (M := M) g₀ S)))).toSection x)) D) =
      (-(1 / 2) : ℝ) • ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
        (ccOperatorFieldComp (I := I) (M := M) g₀ 2 6 2
          (secondMetricPairTraceOperator (I := I) (M := M) g₀ g₁)
          (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 ricciFoldRemainderSlotPerm
            (slotExtendIter (I := I) (M := M) g₀ 0 4 2
              (ricciFoldWeightA (I := I) (M := M) g₀ S +
                ricciFoldWeightB (I := I) (M := M) g₀ S)))).toSection x) D) := by
    rw [show ((((-(1 / 2) : ℝ) •
        ccOperatorFieldComp (I := I) (M := M) g₀ 2 6 2
          (secondMetricPairTraceOperator (I := I) (M := M) g₀ g₁)
          (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 ricciFoldRemainderSlotPerm
            (slotExtendIter (I := I) (M := M) g₀ 0 4 2
              (ricciFoldWeightA (I := I) (M := M) g₀ S +
                ricciFoldWeightB (I := I) (M := M) g₀ S)))).toSection x)) =
        (-(1 / 2) : ℝ) •
          ((ccOperatorFieldComp (I := I) (M := M) g₀ 2 6 2
            (secondMetricPairTraceOperator (I := I) (M := M) g₀ g₁)
            (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 ricciFoldRemainderSlotPerm
              (slotExtendIter (I := I) (M := M) g₀ 0 4 2
                (ricciFoldWeightA (I := I) (M := M) g₀ S +
                  ricciFoldWeightB (I := I) (M := M) g₀ S)))).toSection x) from by
      rw [SmoothCcTensor.toSection_smul]; rfl]
    rfl
  rw [hRHSsmul, Tensor0SSpace.toModel_smul, smul_apply, smul_eq_mul]
  rw [secondMetricPairTraceOperator_apply_toModel (I := I) (M := M) g₀ g₁
    (ricciFoldWeightA (I := I) (M := M) g₀ S + ricciFoldWeightB (I := I) (M := M) g₀ S) x D v]
  rw [show ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
      (ricciArmRicciFoldRemainderField (I := I) (M := M) g₀ g₁ S).toSection x) D) =
      ricciFoldBiContrFib (I := I) g₀ g₁ S x D from rfl]
  rw [show ricciFoldBiContrFib (I := I) g₀ g₁ S x =
      ricciFoldBiContrFibFixedFrame (I := I) g₀ S (smoothOrthoFrame (I := I) g₁ x) x from rfl]
  rw [ricciFoldBiContrFibFixedFrame_toModel (I := I) g₀ S (smoothOrthoFrame (I := I) g₁ x) x D v]
  rw [Finset.sum_comm]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  let v0 : TangentSpace I x :=
    (tangentSpaceModelContinuousLinearEquiv (I := I) x).symm (v 0)
  let v1 : TangentSpace I x :=
    (tangentSpaceModelContinuousLinearEquiv (I := I) x).symm (v 1)
  have hkernel := ricciFoldKernelBilin_apply (I := I) g₀ S x
    (smoothOrthoFrame (I := I) g₁ x a x) (smoothOrthoFrame (I := I) g₁ x b x) v0 v1
  with_unfolding_all
    change
      D.toModel
          ![(tangentSpaceModelContinuousLinearEquiv (I := I) x)
              (smoothOrthoFrame (I := I) g₁ x a x),
            (tangentSpaceModelContinuousLinearEquiv (I := I) x)
              (smoothOrthoFrame (I := I) g₁ x b x)] *
          ricciFoldKernelBilin (I := I) g₀ S x
            (smoothOrthoFrame (I := I) g₁ x a x)
            (smoothOrthoFrame (I := I) g₁ x b x) v0 v1 =
        (-(1 / 2) : ℝ) *
          (D.toModel
              ![(tangentSpaceModelContinuousLinearEquiv (I := I) x)
                  (smoothOrthoFrame (I := I) g₁ x a x),
                (tangentSpaceModelContinuousLinearEquiv (I := I) x)
                  (smoothOrthoFrame (I := I) g₁ x b x)] *
            unitModel (I := I) (M := M) g₀ 4
              (ricciFoldWeightA (I := I) (M := M) g₀ S +
                ricciFoldWeightB (I := I) (M := M) g₀ S) x
              ![v 0, v 1,
                (tangentSpaceModelContinuousLinearEquiv (I := I) x)
                  (smoothOrthoFrame (I := I) g₁ x a x),
                (tangentSpaceModelContinuousLinearEquiv (I := I) x)
                  (smoothOrthoFrame (I := I) g₁ x b x)])
  rw [hkernel]
  have hfold : unitModel (I := I) (M := M) g₀ 4
      (ricciFoldWeightA (I := I) (M := M) g₀ S + ricciFoldWeightB (I := I) (M := M) g₀ S) x
      ![v 0, v 1,
        (tangentSpaceModelContinuousLinearEquiv (I := I) x)
          (smoothOrthoFrame (I := I) g₁ x a x),
        (tangentSpaceModelContinuousLinearEquiv (I := I) x)
          (smoothOrthoFrame (I := I) g₁ x b x)] =
      smoothCcTensorBilinForm (I := I) g₀ S x
          (riemannOp (LeviCivita (I := I) g₀) x v0 (smoothOrthoFrame (I := I) g₁ x a x)
            (smoothOrthoFrame (I := I) g₁ x b x)) v1 +
        smoothCcTensorBilinForm (I := I) g₀ S x (smoothOrthoFrame (I := I) g₁ x b x)
          (riemannOp (LeviCivita (I := I) g₀) x v0 (smoothOrthoFrame (I := I) g₁ x a x)
            v1) := by
    have h := ricciFoldWeights_unitModel_eq_kernel g₀ S x
      (smoothOrthoFrame (I := I) g₁ x a x) (smoothOrthoFrame (I := I) g₁ x b x)
      v0 v1
    with_unfolding_all
      exact h
  rw [hfold]
  ring

lemma exists_riemannianFiberNormSq_iteratedCovGrad_ricciFoldWeightGeneral_boundedFactorGridWindow_le
    (σ : Equiv.Perm (Fin 6))
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ C : ℕ → ℝ, (∀ w, 0 ≤ C w) ∧
      ∀ (P : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀) (_hδ0 : 0 ≤ δ)
        (_hbound : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P)
          δ)
        (w K : ℕ) (_hwK : w ≤ K) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + w) x
            ((iteratedCovGrad (I := I) g₀ 0 4 w
              (ccOperatorFieldComp (I := I) (M := M) g₀ 0 6 4
                (cometricDoubleTraceField (I := I) g₀ 4)
                (rsDomDomCongrSection (I := I) (M := M) g₀ 0 6 σ
                  (ccOperatorFieldComp (I := I) (M := M) g₀ 0 2 6
                    (slotExtendIter (I := I) (M := M) g₀ 0 4 2
                      (riemannLoweredCc (I := I) (M := M) g₀ g₀ g₀))
                    (ccTensor02Symm (I := I) g₀ P))))).toSection x) ≤
          C w * Combinatorics.boundedFactorGridWindow
            (fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
              ((iteratedCovGrad (I := I) g₀ 0 2 l P).toSection x)) K (w + 1) := by
  classical
  set fr : ℝ := (Module.finrank ℝ E : ℝ) with hfr_def
  set KD : ℕ → ℝ := fun u =>
    (exists_bound_riemannianFiberNormSq_smoothCcTensor (I := I) (M := M) g₀ 6 (4 + u)
      (iteratedCovGrad (I := I) g₀ 6 4 u (cometricDoubleTraceField (I := I) g₀ 4))).choose
    with hKD_def
  have hKD_nn : ∀ u, 0 ≤ KD u := fun u =>
    (exists_bound_riemannianFiberNormSq_smoothCcTensor (I := I) (M := M) g₀ 6 (4 + u)
      (iteratedCovGrad (I := I) g₀ 6 4 u
        (cometricDoubleTraceField (I := I) g₀ 4))).choose_spec.1
  have hKD : ∀ u (y : M),
      riemannianFiberNormSq (I := I) (M := M) g₀ 6 (4 + u) y
          ((iteratedCovGrad (I := I) g₀ 6 4 u
            (cometricDoubleTraceField (I := I) g₀ 4)).toSection y) ≤ KD u := fun u =>
    (exists_bound_riemannianFiberNormSq_smoothCcTensor (I := I) (M := M) g₀ 6 (4 + u)
      (iteratedCovGrad (I := I) g₀ 6 4 u
        (cometricDoubleTraceField (I := I) g₀ 4))).choose_spec.2
  set KS : ℕ → ℝ := fun u =>
    (exists_bound_riemannianFiberNormSq_smoothCcTensor (I := I) (M := M) g₀ 2 (6 + u)
      (iteratedCovGrad (I := I) g₀ 2 6 u
        (slotExtendIter (I := I) (M := M) g₀ 0 4 2
          (riemannLoweredCc (I := I) (M := M) g₀ g₀ g₀)))).choose with hKS_def
  have hKS_nn : ∀ u, 0 ≤ KS u := fun u =>
    (exists_bound_riemannianFiberNormSq_smoothCcTensor (I := I) (M := M) g₀ 2 (6 + u)
      (iteratedCovGrad (I := I) g₀ 2 6 u
        (slotExtendIter (I := I) (M := M) g₀ 0 4 2
          (riemannLoweredCc (I := I) (M := M) g₀ g₀ g₀)))).choose_spec.1
  have hKS : ∀ u (y : M),
      riemannianFiberNormSq (I := I) (M := M) g₀ 2 (6 + u) y
          ((iteratedCovGrad (I := I) g₀ 2 6 u
            (slotExtendIter (I := I) (M := M) g₀ 0 4 2
              (riemannLoweredCc (I := I) (M := M) g₀ g₀ g₀))).toSection y) ≤ KS u := fun u =>
    (exists_bound_riemannianFiberNormSq_smoothCcTensor (I := I) (M := M) g₀ 2 (6 + u)
      (iteratedCovGrad (I := I) g₀ 2 6 u
        (slotExtendIter (I := I) (M := M) g₀ 0 4 2
          (riemannLoweredCc (I := I) (M := M) g₀ g₀ g₀)))).choose_spec.2
  refine ⟨fun w => diagonalGridGrowthFactor (E := E) w *
      ∑ w₁ ∈ Finset.range (w + 1), KD w₁ *
        ∑ w₂ ∈ Finset.range (w + 1 - w₁),
          diagonalGridGrowthFactor (E := E) w₂ *
            ∑ w₃ ∈ Finset.range (w₂ + 1), KS w₃ *
              ∑ w₄ ∈ Finset.range (w₂ + 1 - w₃), (fr ^ 2 + 1),
    fun w => by
      refine mul_nonneg (operatorFieldApplicationGdiag_nonneg (E := E) w)
        (Finset.sum_nonneg fun w₁ _ => mul_nonneg (hKD_nn w₁)
          (Finset.sum_nonneg fun w₂ _ => mul_nonneg (operatorFieldApplicationGdiag_nonneg (E := E) w₂)
            (Finset.sum_nonneg fun w₃ _ => mul_nonneg (hKS_nn w₃)
              (Finset.sum_nonneg fun w₄ _ => by positivity)))), ?_⟩
  intro P δ hδ_le hδ0 hbound w K hwK x
  set b : ℕ → ℝ := fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
    ((iteratedCovGrad (I := I) g₀ 0 2 l P).toSection x) with hb_def
  have hb_nn : ∀ l, 0 ≤ b l :=
    fun l => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + l) x _
  set W : ℝ := Combinatorics.boundedFactorGridWindow b K (w + 1) with hW_def
  have hW_nn : 0 ≤ W := Combinatorics.boundedFactorGridWindow_nonneg b hb_nn _ _
  have hW_one : 1 ≤ W := Combinatorics.one_le_boundedFactorGridWindow b hb_nn (by omega)
  have hS : ∀ w₄ : ℕ, w₄ ≤ w →
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + w₄) x
          ((iteratedCovGrad (I := I) g₀ 0 2 w₄
            (ccTensor02Symm (I := I) g₀ P)).toSection x) ≤ (fr ^ 2 + 1) * W := by
    intro w₄ hw₄
    match w₄, hw₄ with
    | 0, _ =>
        rw [iteratedCovGrad_zero]
        have hδ1 : δ ^ 2 ≤ 1 := by nlinarith
        have h0 := riemannianFiberNormSq_symmS_zero_le_of_ball (I := I) (M := M) g₀ P hδ0 hbound x
        calc riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x
              ((ccTensor02Symm (I := I) (M := M) g₀ P).toSection x)
            ≤ fr ^ 2 * δ ^ 2 := h0
          _ ≤ fr ^ 2 * 1 := by
              refine mul_le_mul_of_nonneg_left hδ1 ?_
              positivity
          _ ≤ (fr ^ 2 + 1) * 1 := by nlinarith
          _ ≤ (fr ^ 2 + 1) * W := by
              refine mul_le_mul_of_nonneg_left hW_one ?_
              positivity
    | (k + 1), hw₄ =>
        refine le_trans (riemannianFiberNormSq_iteratedCovGrad_symmS_pointwise (I := I) (M := M) g₀ P
          (k + 1) x) ?_
        calc b (k + 1)
            ≤ Combinatorics.antidiagonalTupleGrid b (k + 1) :=
              single_b_le_grid b hb_nn (k + 1) (by omega)
          _ ≤ Combinatorics.boundedFactorGridWindow b K (w + 1) :=
              Combinatorics.antidiagonalTupleGrid_le_boundedFactorGridWindow b hb_nn
                (by omega) (by omega)
          _ ≤ (fr ^ 2 + 1) * W := by
              rw [← hW_def]
              nlinarith [hW_nn]
  have hBase : ∀ w₂ : ℕ, w₂ ≤ w →
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (6 + w₂) x
          ((iteratedCovGrad (I := I) g₀ 0 6 w₂
            (rsDomDomCongrSection (I := I) (M := M) g₀ 0 6 σ
              (ccOperatorFieldComp (I := I) (M := M) g₀ 0 2 6
                (slotExtendIter (I := I) (M := M) g₀ 0 4 2
                  (riemannLoweredCc (I := I) (M := M) g₀ g₀ g₀))
                (ccTensor02Symm (I := I) g₀ P)))).toSection x) ≤
        (diagonalGridGrowthFactor (E := E) w₂ *
          ∑ w₃ ∈ Finset.range (w₂ + 1), KS w₃ *
            ∑ w₄ ∈ Finset.range (w₂ + 1 - w₃), (fr ^ 2 + 1)) * W := by
    intro w₂ hw₂
    rw [riemannianFiberNormSq_iteratedCovGrad_rsDomDomCongrSection_eq (I := I) (M := M) g₀ 0 6 σ _
      w₂ x]
    refine le_trans
      (riemannianFiberNormSq_iteratedCovGrad_ccTensorCompose_diagonalProductGrid_leftFactor_le
      (I := I)
      (M := M) g₀ w₂ 0 2 6
      (slotExtendIter (I := I) (M := M) g₀ 0 4 2
        (riemannLoweredCc (I := I) (M := M) g₀ g₀ g₀))
      (ccTensor02Symm (I := I) g₀ P) x) ?_
    calc diagonalGridGrowthFactor (E := E) w₂ *
          ∑ w₃ ∈ Finset.range (w₂ + 1),
            riemannianFiberNormSq (I := I) (M := M) g₀ 2 (6 + w₃) x
                ((iteratedCovGrad (I := I) g₀ 2 6 w₃
                  (slotExtendIter (I := I) (M := M) g₀ 0 4 2
                    (riemannLoweredCc (I := I) (M := M) g₀ g₀ g₀))).toSection x) *
              ∑ w₄ ∈ Finset.range (w₂ + 1 - w₃),
                riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + w₄) x
                  ((iteratedCovGrad (I := I) g₀ 0 2 w₄
                    (ccTensor02Symm (I := I) g₀ P)).toSection x)
        ≤ diagonalGridGrowthFactor (E := E) w₂ *
            ∑ w₃ ∈ Finset.range (w₂ + 1), KS w₃ *
              ∑ w₄ ∈ Finset.range (w₂ + 1 - w₃), ((fr ^ 2 + 1) * W) := by
          refine mul_le_mul_of_nonneg_left
            (Finset.sum_le_sum fun w₃ hw₃ => ?_) (operatorFieldApplicationGdiag_nonneg (E := E) w₂)
          rw [Finset.mem_range] at hw₃
          refine mul_le_mul (hKS w₃ x) (Finset.sum_le_sum fun w₄ hw₄ => ?_)
            (Finset.sum_nonneg fun w₄ _ =>
              riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + w₄) x _)
            (hKS_nn w₃)
          rw [Finset.mem_range] at hw₄
          exact hS w₄ (by omega)
      _ = (diagonalGridGrowthFactor (E := E) w₂ *
            ∑ w₃ ∈ Finset.range (w₂ + 1), KS w₃ *
              ∑ w₄ ∈ Finset.range (w₂ + 1 - w₃), (fr ^ 2 + 1)) * W := by
          have hstep : ∀ w₃ : ℕ, (KS w₃ *
              ∑ w₄ ∈ Finset.range (w₂ + 1 - w₃), ((fr ^ 2 + 1) * W)) =
              (KS w₃ * ∑ w₄ ∈ Finset.range (w₂ + 1 - w₃), (fr ^ 2 + 1)) * W := by
            intro w₃
            rw [← Finset.sum_mul]
            ring
          rw [Finset.sum_congr rfl fun w₃ _ => hstep w₃, ← Finset.sum_mul]
          ring
  refine le_trans
    (riemannianFiberNormSq_iteratedCovGrad_ccTensorCompose_diagonalProductGrid_leftFactor_le
    (I := I)
    (M := M) g₀ w 0 6 4 (cometricDoubleTraceField (I := I) g₀ 4)
    (rsDomDomCongrSection (I := I) (M := M) g₀ 0 6 σ
      (ccOperatorFieldComp (I := I) (M := M) g₀ 0 2 6
        (slotExtendIter (I := I) (M := M) g₀ 0 4 2
          (riemannLoweredCc (I := I) (M := M) g₀ g₀ g₀))
        (ccTensor02Symm (I := I) g₀ P))) x) ?_
  calc diagonalGridGrowthFactor (E := E) w *
        ∑ w₁ ∈ Finset.range (w + 1),
          riemannianFiberNormSq (I := I) (M := M) g₀ 6 (4 + w₁) x
              ((iteratedCovGrad (I := I) g₀ 6 4 w₁
                (cometricDoubleTraceField (I := I) g₀ 4)).toSection x) *
            ∑ w₂ ∈ Finset.range (w + 1 - w₁),
              riemannianFiberNormSq (I := I) (M := M) g₀ 0 (6 + w₂) x
                ((iteratedCovGrad (I := I) g₀ 0 6 w₂
                  (rsDomDomCongrSection (I := I) (M := M) g₀ 0 6 σ
                    (ccOperatorFieldComp (I := I) (M := M) g₀ 0 2 6
                      (slotExtendIter (I := I) (M := M) g₀ 0 4 2
                        (riemannLoweredCc (I := I) (M := M) g₀ g₀ g₀))
                      (ccTensor02Symm (I := I) g₀ P)))).toSection x)
      ≤ diagonalGridGrowthFactor (E := E) w *
          ∑ w₁ ∈ Finset.range (w + 1), KD w₁ *
            ∑ w₂ ∈ Finset.range (w + 1 - w₁),
              ((diagonalGridGrowthFactor (E := E) w₂ *
                ∑ w₃ ∈ Finset.range (w₂ + 1), KS w₃ *
                  ∑ w₄ ∈ Finset.range (w₂ + 1 - w₃), (fr ^ 2 + 1)) * W) := by
        refine mul_le_mul_of_nonneg_left
          (Finset.sum_le_sum fun w₁ hw₁ => ?_) (operatorFieldApplicationGdiag_nonneg (E := E) w)
        rw [Finset.mem_range] at hw₁
        refine mul_le_mul (hKD w₁ x) (Finset.sum_le_sum fun w₂ hw₂ => ?_)
          (Finset.sum_nonneg fun w₂ _ =>
            riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (6 + w₂) x _)
          (hKD_nn w₁)
        rw [Finset.mem_range] at hw₂
        exact hBase w₂ (by omega)
    _ = (diagonalGridGrowthFactor (E := E) w *
          ∑ w₁ ∈ Finset.range (w + 1), KD w₁ *
            ∑ w₂ ∈ Finset.range (w + 1 - w₁),
              diagonalGridGrowthFactor (E := E) w₂ *
                ∑ w₃ ∈ Finset.range (w₂ + 1), KS w₃ *
                  ∑ w₄ ∈ Finset.range (w₂ + 1 - w₃), (fr ^ 2 + 1)) * W := by
        have hstep : ∀ w₁ : ℕ, (KD w₁ *
            ∑ w₂ ∈ Finset.range (w + 1 - w₁),
              ((diagonalGridGrowthFactor (E := E) w₂ *
                ∑ w₃ ∈ Finset.range (w₂ + 1), KS w₃ *
                  ∑ w₄ ∈ Finset.range (w₂ + 1 - w₃), (fr ^ 2 + 1)) * W)) =
            (KD w₁ * ∑ w₂ ∈ Finset.range (w + 1 - w₁),
              diagonalGridGrowthFactor (E := E) w₂ *
                ∑ w₃ ∈ Finset.range (w₂ + 1), KS w₃ *
                  ∑ w₄ ∈ Finset.range (w₂ + 1 - w₃), (fr ^ 2 + 1)) * W := by
          intro w₁
          rw [← Finset.sum_mul]
          ring
        rw [Finset.sum_congr rfl fun w₁ _ => hstep w₁, ← Finset.sum_mul]
        ring

omit [I.Boundaryless] [SigmaCompactSpace M] in
lemma bgRCommCoeffField_eq_decomposition (g : SmoothRiemannianMetric I M) :
    ricciArmOrder0BackgroundCurvatureCoeffField (I := I) (M := M) g₀ g =
      ccOperatorFieldComp (I := I) (M := M) g₀ 2 4 2
        (secondMetricCometricDoubleTraceField (I := I) (M := M) g₀ g 2)
        (riemannCometricDoubleTraceFold (I := I) (M := M) g₀) := by
  classical
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  apply tensorRSSpace_ext 2 2 x
  intro D
  apply Tensor0SSpace.toModel_injective
  apply ContinuousMultilinearMap.ext
  intro v
  beta_reduce
  let v0 : TangentSpace I x :=
    (tangentSpaceModelContinuousLinearEquiv (I := I) x).symm (v 0)
  let v1 : TangentSpace I x :=
    (tangentSpaceModelContinuousLinearEquiv (I := I) x).symm (v 1)
  rw [show ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
      (ricciArmOrder0BackgroundCurvatureCoeffField (I := I) (M := M) g₀ g).toSection x) D) =
      backgroundRiemannBiContrFib (I := I) g₀ g x D from rfl]
  rw [show backgroundRiemannBiContrFib (I := I) g₀ g x =
      backgroundRiemannBiContrFibFixedFrame (I := I) g₀ (smoothOrthoFrame (I := I) g x) x from rfl]
  rw [backgroundRiemannBiContrFibFixedFrame_toModel (I := I) g₀ (smoothOrthoFrame (I := I) g x) x D
    (fun j => (v j : E))]
  rw [show ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
      (ccOperatorFieldComp (I := I) (M := M) g₀ 2 4 2
        (secondMetricCometricDoubleTraceField (I := I) (M := M) g₀ g 2)
        (riemannCometricDoubleTraceFold (I := I) (M := M) g₀)).toSection x) D) =
      cometricDoubleTraceFib (I := I) g 2 x
        ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 4 I x from
          (riemannCometricDoubleTraceFold (I := I) (M := M) g₀).toSection x) D) from by
    rw [operatorFieldComposition_toSection]
    rfl]
  rw [cometricDoubleTraceFib_toModel (I := I) g 2 x]
  rw [modelDoubleTrace_apply (E := E) 2 (cometricLmodel (I := I) g x)]
  rw [cometric_dualTrace_eq_orthoFrame_diag (I := I) g x
    (mem_smoothOrthoFrameNbhd_self (I := I) (M := M) x)
    (Tensor0SSpace.toModel
      ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 4 I x from
        (riemannCometricDoubleTraceFold (I := I) (M := M) g₀).toSection x) D))
    (fun j => (v j : E))]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [bgRArmWeight_toModel (I := I) (M := M) g₀ x D]
  change Tensor0SSpace.toModel D
      (Fin.cons ((tangentSpaceModelContinuousLinearEquiv (I := I) x)
          (riemannOp (LeviCivita (I := I) g₀) x
            (smoothOrthoFrame (I := I) g x c x) v0 v1))
        (Fin.cons ((tangentSpaceModelContinuousLinearEquiv (I := I) x)
            (smoothOrthoFrame (I := I) g x c x))
          (fun i : Fin 0 => i.elim0))) =
    ∑ e : Fin (Module.finrank ℝ E),
      Tensor0SSpace.toModel D
          (Fin.cons ((tangentSpaceModelContinuousLinearEquiv (I := I) x)
              (smoothOrthoFrame (I := I) g₀ x e x))
            (Fin.cons ((tangentSpaceModelContinuousLinearEquiv (I := I) x)
                (smoothOrthoFrame (I := I) g x c x))
              (fun i : Fin 0 => i.elim0))) *
        g₀.inner x (riemannOp (LeviCivita (I := I) g₀) x
            (smoothOrthoFrame (I := I) g x c x) v0 v1)
          (smoothOrthoFrame (I := I) g₀ x e x)
  have hu_exp : (tangentSpaceModelContinuousLinearEquiv (I := I) x)
      (riemannOp (LeviCivita (I := I) g₀) x
        (smoothOrthoFrame (I := I) g x c x) v0 v1) =
      ∑ e : Fin (Module.finrank ℝ E),
        g₀.inner x (riemannOp (LeviCivita (I := I) g₀) x
            (smoothOrthoFrame (I := I) g x c x) v0 v1)
          (smoothOrthoFrame (I := I) g₀ x e x) •
        (tangentSpaceModelContinuousLinearEquiv (I := I) x)
          (smoothOrthoFrame (I := I) g₀ x e x) := by
    simpa only [map_sum, map_smul] using congrArg
      (tangentSpaceModelContinuousLinearEquiv (I := I) x)
      (orthoFrame_expansion_at_center (I := I) (M := M) g₀ x
        (riemannOp (LeviCivita (I := I) g₀) x
          (smoothOrthoFrame (I := I) g x c x) v0 v1))
  rw [hu_exp]
  rw [toModel_cons_sum_smul (E := E) (Tensor0SSpace.toModel D)
    (Module.finrank ℝ E)
    (fun e => g₀.inner x (riemannOp (LeviCivita (I := I) g₀) x
        (smoothOrthoFrame (I := I) g x c x) v0 v1)
      (smoothOrthoFrame (I := I) g₀ x e x))
    (fun e => (tangentSpaceModelContinuousLinearEquiv (I := I) x)
      (smoothOrthoFrame (I := I) g₀ x e x))
    (Fin.cons ((tangentSpaceModelContinuousLinearEquiv (I := I) x)
        (smoothOrthoFrame (I := I) g x c x))
      (fun i : Fin 0 => i.elim0))]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [mul_comm]


open DifferentialGeometry.Integral.DivergenceTheorem in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
private lemma sharpRaisedKoszulVec_symmS_eq_connectionDifference (P : SmoothCcTensor g₀ 0 2)
    (htie : ∀ (y : M) (v w : TangentSpace I y),
      g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
    (x : M) (u ζ : TangentSpace I x) :
    sharpRaisedKoszulVec (I := I) g₀ g₁ (ccTensor02Symm (I := I) g₀ P) x u ζ =
      PDE.DeTurck.connectionDifference (I := I) g₁ g₀ x u ζ := by
  rw [sharpRaisedKoszulVec, metricSharp_def, LinearEquiv.symm_apply_eq]
  apply LinearMap.ext
  intro z
  rw [show (metricFlatMap (I := I) g₁ x
      (PDE.DeTurck.connectionDifference (I := I) g₁ g₀ x u ζ)) z =
      g₁.inner x (PDE.DeTurck.connectionDifference (I := I) g₁ g₀ x u ζ) z from rfl]
  rw [linearizedKoszulCovec_apply (I := I) g₀ (ccTensor02Symm (I := I) g₀ P) x u ζ z]
  rw [connectionDifferenceInner_g1_eq_half_covGradSymmS (I := I) g₀ g₁ P htie x u ζ z]
  with_unfolding_all
    rfl

section NormedKoszulCovectorConnectionDifferenceIdentity

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

variable (g₀ g₁ : SmoothRiemannianMetric I M)

omit [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
lemma koszulCovecCc_unitModel_eq_connectionDifference_g1_inner (P : SmoothCcTensor g₀ 0 2)
    (htie : ∀ (y : M) (v w : TangentSpace I y),
      g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
    (x : M) (a b c : TangentSpace I x) :
    unitModel (I := I) (M := M) g₀ 3 (koszulCovecCc (I := I) g₀ P) x
        ![(tangentSpaceModelContinuousLinearEquiv (I := I) x) c,
          (tangentSpaceModelContinuousLinearEquiv (I := I) x) a,
          (tangentSpaceModelContinuousLinearEquiv (I := I) x) b] =
      g₁.inner x (PDE.DeTurck.connectionDifference (I := I) g₁ g₀ x a b) c := by
  rw [koszulCovecCc_unitModel (I := I) (M := M) g₀ P x a b c]
  rw [connectionDifferenceInner_g1_eq_half_covGradSymmS (I := I) g₀ g₁ P htie x a b c]
  rfl

end NormedKoszulCovectorConnectionDifferenceIdentity

section NormedKoszulConnectionDifferenceFoldWeight

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

variable (g₀ g₁ : SmoothRiemannianMetric I M)

def koszulConnectionDifferenceFoldWeight (σ : Equiv.Perm (Fin 6)) (P : SmoothCcTensor g₀ 0 2) :
    SmoothCcTensor g₀ 0 4 :=
  ccOperatorFieldComp (I := I) (M := M) g₀ 0 6 4 (cometricDoubleTraceField (I := I) g₀ 4)
    (rsDomDomCongrSection (I := I) (M := M) g₀ 0 6 σ
      (ccOperatorFieldComp (I := I) (M := M) g₀ 0 3 6
        (slotExtendIter (I := I) (M := M) g₀ 0 3 3 (koszulCovecCc (I := I) g₀ P))
        (metricLoweredConnectionDifferenceCoefficient (I := I) g₀ g₁)))

end NormedKoszulConnectionDifferenceFoldWeight

section NormedKoszulConnectionDifferenceFoldIdentity

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

variable (g₀ g₁ : SmoothRiemannianMetric I M)

omit [SigmaCompactSpace M] in
lemma koszulConnectionDifferenceFoldWeight_unitModel_general (σ : Equiv.Perm (Fin 6))
    (P : SmoothCcTensor g₀ 0 2) (x : M) (m : Fin 4 → E) :
    unitModel (I := I) (M := M) g₀ 4
        (ccOperatorFieldComp (I := I) (M := M) g₀ 0 6 4 (cometricDoubleTraceField (I := I) g₀ 4)
          (rsDomDomCongrSection (I := I) (M := M) g₀ 0 6 σ
            (ccOperatorFieldComp (I := I) (M := M) g₀ 0 3 6
              (slotExtendIter (I := I) (M := M) g₀ 0 3 3 (koszulCovecCc (I := I) g₀ P))
              (metricLoweredConnectionDifferenceCoefficient (I := I) g₀ g₁)))) x m =
      ∑ e : Fin (Module.finrank ℝ E),
        unitModel (I := I) (M := M) g₀ 3 (metricLoweredConnectionDifferenceCoefficient (I := I) g₀ g₁) x
            ![((Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
                (Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E) m) :
                  Fin 6 → E) (σ 0)),
              ((Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
                (Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E) m) :
                  Fin 6 → E) (σ 1)),
              ((Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
                (Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E) m) :
                  Fin 6 → E) (σ 2))] *
          unitModel (I := I) (M := M) g₀ 3 (koszulCovecCc (I := I) g₀ P) x
            ![((Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
                (Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E) m) :
                  Fin 6 → E) (σ 3)),
              ((Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
                (Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E) m) :
                  Fin 6 → E) (σ 4)),
              ((Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
                (Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E) m) :
                  Fin 6 → E) (σ 5))] := by
  classical
  set κ3 : SmoothCcTensor g₀ 0 3 := koszulCovecCc (I := I) g₀ P with hκ3_def
  set Cval : Tensor0SSpace 3 I x :=
    (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 3 I x from
      (metricLoweredConnectionDifferenceCoefficient (I := I) g₀ g₁).toSection x)
      (unitTensor (I := I) (M := M) x) with hCval_def
  set Y : Tensor0SSpace 6 I x :=
    (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 6 I x from
      (rsDomDomCongrSection (I := I) (M := M) g₀ 0 6 σ
        (ccOperatorFieldComp (I := I) (M := M) g₀ 0 3 6
          (slotExtendIter (I := I) (M := M) g₀ 0 3 3 κ3)
          (metricLoweredConnectionDifferenceCoefficient (I := I) g₀ g₁))).toSection x)
      (unitTensor (I := I) (M := M) x) with hY_def
  have hYval : ∀ w : Fin 6 → E,
      Tensor0SSpace.toModel Y w =
        Tensor0SSpace.toModel Cval ![(w (σ 0) : E), (w (σ 1) : E), (w (σ 2) : E)] *
          unitModel (I := I) (M := M) g₀ 3 κ3 x
            ![(w (σ 3) : E), (w (σ 4) : E), (w (σ 5) : E)] := by
    intro w
    rw [hY_def]
    rw [show ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 6 I x from
        (rsDomDomCongrSection (I := I) (M := M) g₀ 0 6 σ
          (ccOperatorFieldComp (I := I) (M := M) g₀ 0 3 6
            (slotExtendIter (I := I) (M := M) g₀ 0 3 3 κ3)
            (metricLoweredConnectionDifferenceCoefficient (I := I) g₀ g₁))).toSection x)
        (unitTensor (I := I) (M := M) x)) =
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 6 I x from
          tensorRSDomDomCongr σ
            ((ccOperatorFieldComp (I := I) (M := M) g₀ 0 3 6
              (slotExtendIter (I := I) (M := M) g₀ 0 3 3 κ3)
              (metricLoweredConnectionDifferenceCoefficient (I := I) g₀ g₁)).toSection x))
          (unitTensor (I := I) (M := M) x)) from by
      rw [rsDomDomCongrSection_toSection]]
    rw [toModel_rsDomDomCongr_apply (I := I) (M := M) σ
      ((ccOperatorFieldComp (I := I) (M := M) g₀ 0 3 6
        (slotExtendIter (I := I) (M := M) g₀ 0 3 3 κ3)
        (metricLoweredConnectionDifferenceCoefficient (I := I) g₀ g₁)).toSection x)
      (unitTensor (I := I) (M := M) x)]
    rw [ContinuousMultilinearMap.domDomCongr_apply]
    rw [show ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 6 I x from
        (ccOperatorFieldComp (I := I) (M := M) g₀ 0 3 6
          (slotExtendIter (I := I) (M := M) g₀ 0 3 3 κ3)
          (metricLoweredConnectionDifferenceCoefficient (I := I) g₀ g₁)).toSection x)
        (unitTensor (I := I) (M := M) x)) =
        ((show Tensor0SSpace 3 I x →L[ℝ] Tensor0SSpace 6 I x from
          (slotExtendIter (I := I) (M := M) g₀ 0 3 3 κ3).toSection x) Cval) from by
      rw [operatorFieldComposition_toSection]
      rfl]
    rw [slotExtendIter_three_toModel (I := I) (M := M) g₀ κ3 x Cval (fun i => w (σ i))]
    refine congrArg₂ (· * ·) ?_ ?_
    · refine congrArg _ ?_
      funext k
      fin_cases k <;> rfl
    · rw [show unitModel (I := I) (M := M) g₀ 3 κ3 x
          (fun k : Fin 3 => ((fun i => w (σ i)) (Fin.natAdd 3 k) : E)) =
          unitModel (I := I) (M := M) g₀ 3 κ3 x
            ![(w (σ 3) : E), (w (σ 4) : E), (w (σ 5) : E)] from by
        refine congrArg _ ?_
        funext k
        fin_cases k <;> rfl]
  rw [show unitModel (I := I) (M := M) g₀ 4
      (ccOperatorFieldComp (I := I) (M := M) g₀ 0 6 4 (cometricDoubleTraceField (I := I) g₀ 4)
        (rsDomDomCongrSection (I := I) (M := M) g₀ 0 6 σ
          (ccOperatorFieldComp (I := I) (M := M) g₀ 0 3 6
            (slotExtendIter (I := I) (M := M) g₀ 0 3 3 κ3)
            (metricLoweredConnectionDifferenceCoefficient (I := I) g₀ g₁)))) x =
      Tensor0SSpace.toModel (cometricDoubleTraceFib (I := I) g₀ 4 x Y) from by
    rw [unitModel, hY_def]
    rw [operatorFieldComposition_toSection]
    rfl]
  rw [cometricDoubleTraceFib_toModel (I := I) g₀ 4 x Y]
  rw [modelDoubleTrace_apply (E := E) 4 (cometricLmodel (I := I) g₀ x)]
  rw [cometric_dualTrace_eq_orthoFrame_diag (I := I) g₀ x
    (mem_smoothOrthoFrameNbhd_self (I := I) (M := M) x)
    (Tensor0SSpace.toModel Y) m]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [hYval]
  rfl

end NormedKoszulConnectionDifferenceFoldIdentity

omit [SigmaCompactSpace M] in
private lemma sharpGradKoszulKernel_foldWeights_unitModel (P : SmoothCcTensor g₀ 0 2)
    (htie : ∀ (y : M) (v w : TangentSpace I y),
      g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
    (x : M) (p q v0 v1 : TangentSpace I x) :
    unitModel (I := I) (M := M) g₀ 4
        ((koszulConnectionDifferenceFoldWeight (I := I) (M := M) g₀ g₁ sharpGradKoszulKernelPositivePermutation P +
            koszulConnectionDifferenceFoldWeight (I := I) (M := M) g₀ g₁ sharpGradKoszulKernelPositiveKoszulSwapPermutation P) -
          (koszulConnectionDifferenceFoldWeight (I := I) (M := M) g₀ g₁ sharpGradKoszulKernelNegativePermutation P +
            koszulConnectionDifferenceFoldWeight (I := I) (M := M) g₀ g₁ sharpGradKoszulKernelNegativeKoszulSwapPermutation P)) x
        ![(v0 : E), (v1 : E), (p : E), (q : E)] =
      sharpGradKoszulKernelBilin (I := I) g₀ g₁ (ccTensor02Symm (I := I) g₀ P) x p q v0 v1 := by
  classical
  have hM1 : unitModel (I := I) (M := M) g₀ 4
      (koszulConnectionDifferenceFoldWeight (I := I) (M := M) g₀ g₁ sharpGradKoszulKernelPositivePermutation P) x
      ![(v0 : E), (v1 : E), (p : E), (q : E)] =
      ∑ e : Fin (Module.finrank ℝ E),
        g₀.inner x (PDE.DeTurck.connectionDifference (I := I) g₁ g₀ x q v0)
            (smoothOrthoFrame (I := I) g₀ x e x) *
          unitModel (I := I) (M := M) g₀ 3 (koszulCovecCc (I := I) g₀ P) x
            ![(v1 : E), (p : E),
              ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)] := by
    rw [show koszulConnectionDifferenceFoldWeight (I := I) (M := M) g₀ g₁ sharpGradKoszulKernelPositivePermutation P =
        ccOperatorFieldComp (I := I) (M := M) g₀ 0 6 4 (cometricDoubleTraceField (I := I) g₀ 4)
          (rsDomDomCongrSection (I := I) (M := M) g₀ 0 6 sharpGradKoszulKernelPositivePermutation
            (ccOperatorFieldComp (I := I) (M := M) g₀ 0 3 6
              (slotExtendIter (I := I) (M := M) g₀ 0 3 3 (koszulCovecCc (I := I) g₀ P))
              (metricLoweredConnectionDifferenceCoefficient (I := I) g₀ g₁))) from rfl]
    rw [koszulConnectionDifferenceFoldWeight_unitModel_general (I := I) (M := M) g₀ g₁ sharpGradKoszulKernelPositivePermutation P x
      ![(v0 : E), (v1 : E), (p : E), (q : E)]]
    refine Finset.sum_congr rfl fun e _ => ?_
    have h1 : unitModel (I := I) (M := M) g₀ 3 (metricLoweredConnectionDifferenceCoefficient (I := I) g₀ g₁) x
        ![((Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
            (Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
              ![(v0 : E), (v1 : E), (p : E), (q : E)]) : Fin 6 → E) (sharpGradKoszulKernelPositivePermutation 0)),
          ((Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
            (Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
              ![(v0 : E), (v1 : E), (p : E), (q : E)]) : Fin 6 → E) (sharpGradKoszulKernelPositivePermutation 1)),
          ((Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
            (Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
              ![(v0 : E), (v1 : E), (p : E), (q : E)]) : Fin 6 → E) (sharpGradKoszulKernelPositivePermutation 2))] =
        unitModel (I := I) (M := M) g₀ 3 (metricLoweredConnectionDifferenceCoefficient (I := I) g₀ g₁) x
          ![(q : E), (v0 : E),
            ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)] := by
      refine congrArg _ ?_
      funext k
      fin_cases k <;> rfl
    have h2 : unitModel (I := I) (M := M) g₀ 3 (koszulCovecCc (I := I) g₀ P) x
        ![((Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
            (Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
              ![(v0 : E), (v1 : E), (p : E), (q : E)]) : Fin 6 → E) (sharpGradKoszulKernelPositivePermutation 3)),
          ((Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
            (Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
              ![(v0 : E), (v1 : E), (p : E), (q : E)]) : Fin 6 → E) (sharpGradKoszulKernelPositivePermutation 4)),
          ((Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
            (Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
              ![(v0 : E), (v1 : E), (p : E), (q : E)]) : Fin 6 → E) (sharpGradKoszulKernelPositivePermutation 5))] =
        unitModel (I := I) (M := M) g₀ 3 (koszulCovecCc (I := I) g₀ P) x
          ![(v1 : E), (p : E),
            ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)] := by
      refine congrArg _ ?_
      funext k
      fin_cases k <;> rfl
    rw [h1, h2]
    congr 1
    have h12 := connectionDifferenceLowered_unitModel_value (I := I) (M := M) g₀ g₁ x
      ![q, v0, smoothOrthoFrame (I := I) g₀ x e x]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons] at h12
    exact h12
  have hM2 : unitModel (I := I) (M := M) g₀ 4
      (koszulConnectionDifferenceFoldWeight (I := I) (M := M) g₀ g₁ sharpGradKoszulKernelPositiveKoszulSwapPermutation P) x
      ![(v0 : E), (v1 : E), (p : E), (q : E)] =
      ∑ e : Fin (Module.finrank ℝ E),
        g₀.inner x (PDE.DeTurck.connectionDifference (I := I) g₁ g₀ x q v0)
            (smoothOrthoFrame (I := I) g₀ x e x) *
          unitModel (I := I) (M := M) g₀ 3 (koszulCovecCc (I := I) g₀ P) x
            ![((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E),
              (p : E), (v1 : E)] := by
    rw [show koszulConnectionDifferenceFoldWeight (I := I) (M := M) g₀ g₁ sharpGradKoszulKernelPositiveKoszulSwapPermutation P =
        ccOperatorFieldComp (I := I) (M := M) g₀ 0 6 4 (cometricDoubleTraceField (I := I) g₀ 4)
          (rsDomDomCongrSection (I := I) (M := M) g₀ 0 6 sharpGradKoszulKernelPositiveKoszulSwapPermutation
            (ccOperatorFieldComp (I := I) (M := M) g₀ 0 3 6
              (slotExtendIter (I := I) (M := M) g₀ 0 3 3 (koszulCovecCc (I := I) g₀ P))
              (metricLoweredConnectionDifferenceCoefficient (I := I) g₀ g₁))) from rfl]
    rw [koszulConnectionDifferenceFoldWeight_unitModel_general (I := I) (M := M) g₀ g₁ sharpGradKoszulKernelPositiveKoszulSwapPermutation P x
      ![(v0 : E), (v1 : E), (p : E), (q : E)]]
    refine Finset.sum_congr rfl fun e _ => ?_
    have h1 : unitModel (I := I) (M := M) g₀ 3 (metricLoweredConnectionDifferenceCoefficient (I := I) g₀ g₁) x
        ![((Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
            (Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
              ![(v0 : E), (v1 : E), (p : E), (q : E)]) : Fin 6 → E) (sharpGradKoszulKernelPositiveKoszulSwapPermutation 0)),
          ((Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
            (Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
              ![(v0 : E), (v1 : E), (p : E), (q : E)]) : Fin 6 → E) (sharpGradKoszulKernelPositiveKoszulSwapPermutation 1)),
          ((Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
            (Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
              ![(v0 : E), (v1 : E), (p : E), (q : E)]) : Fin 6 → E) (sharpGradKoszulKernelPositiveKoszulSwapPermutation 2))] =
        unitModel (I := I) (M := M) g₀ 3 (metricLoweredConnectionDifferenceCoefficient (I := I) g₀ g₁) x
          ![(q : E), (v0 : E),
            ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)] := by
      refine congrArg _ ?_
      funext k
      fin_cases k <;> rfl
    have h2 : unitModel (I := I) (M := M) g₀ 3 (koszulCovecCc (I := I) g₀ P) x
        ![((Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
            (Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
              ![(v0 : E), (v1 : E), (p : E), (q : E)]) : Fin 6 → E) (sharpGradKoszulKernelPositiveKoszulSwapPermutation 3)),
          ((Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
            (Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
              ![(v0 : E), (v1 : E), (p : E), (q : E)]) : Fin 6 → E) (sharpGradKoszulKernelPositiveKoszulSwapPermutation 4)),
          ((Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
            (Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
              ![(v0 : E), (v1 : E), (p : E), (q : E)]) : Fin 6 → E) (sharpGradKoszulKernelPositiveKoszulSwapPermutation 5))] =
        unitModel (I := I) (M := M) g₀ 3 (koszulCovecCc (I := I) g₀ P) x
          ![((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E),
            (p : E), (v1 : E)] := by
      refine congrArg _ ?_
      funext k
      fin_cases k <;> rfl
    rw [h1, h2]
    congr 1
    have h12 := connectionDifferenceLowered_unitModel_value (I := I) (M := M) g₀ g₁ x
      ![q, v0, smoothOrthoFrame (I := I) g₀ x e x]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons] at h12
    exact h12
  have hM3 : unitModel (I := I) (M := M) g₀ 4
      (koszulConnectionDifferenceFoldWeight (I := I) (M := M) g₀ g₁ sharpGradKoszulKernelNegativePermutation P) x
      ![(v0 : E), (v1 : E), (p : E), (q : E)] =
      ∑ e : Fin (Module.finrank ℝ E),
        g₀.inner x (PDE.DeTurck.connectionDifference (I := I) g₁ g₀ x q p)
            (smoothOrthoFrame (I := I) g₀ x e x) *
          unitModel (I := I) (M := M) g₀ 3 (koszulCovecCc (I := I) g₀ P) x
            ![(v1 : E), (v0 : E),
              ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)] := by
    rw [show koszulConnectionDifferenceFoldWeight (I := I) (M := M) g₀ g₁ sharpGradKoszulKernelNegativePermutation P =
        ccOperatorFieldComp (I := I) (M := M) g₀ 0 6 4 (cometricDoubleTraceField (I := I) g₀ 4)
          (rsDomDomCongrSection (I := I) (M := M) g₀ 0 6 sharpGradKoszulKernelNegativePermutation
            (ccOperatorFieldComp (I := I) (M := M) g₀ 0 3 6
              (slotExtendIter (I := I) (M := M) g₀ 0 3 3 (koszulCovecCc (I := I) g₀ P))
              (metricLoweredConnectionDifferenceCoefficient (I := I) g₀ g₁))) from rfl]
    rw [koszulConnectionDifferenceFoldWeight_unitModel_general (I := I) (M := M) g₀ g₁ sharpGradKoszulKernelNegativePermutation P x
      ![(v0 : E), (v1 : E), (p : E), (q : E)]]
    refine Finset.sum_congr rfl fun e _ => ?_
    have h1 : unitModel (I := I) (M := M) g₀ 3 (metricLoweredConnectionDifferenceCoefficient (I := I) g₀ g₁) x
        ![((Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
            (Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
              ![(v0 : E), (v1 : E), (p : E), (q : E)]) : Fin 6 → E) (sharpGradKoszulKernelNegativePermutation 0)),
          ((Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
            (Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
              ![(v0 : E), (v1 : E), (p : E), (q : E)]) : Fin 6 → E) (sharpGradKoszulKernelNegativePermutation 1)),
          ((Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
            (Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
              ![(v0 : E), (v1 : E), (p : E), (q : E)]) : Fin 6 → E) (sharpGradKoszulKernelNegativePermutation 2))] =
        unitModel (I := I) (M := M) g₀ 3 (metricLoweredConnectionDifferenceCoefficient (I := I) g₀ g₁) x
          ![(q : E), (p : E),
            ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)] := by
      refine congrArg _ ?_
      funext k
      fin_cases k <;> rfl
    have h2 : unitModel (I := I) (M := M) g₀ 3 (koszulCovecCc (I := I) g₀ P) x
        ![((Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
            (Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
              ![(v0 : E), (v1 : E), (p : E), (q : E)]) : Fin 6 → E) (sharpGradKoszulKernelNegativePermutation 3)),
          ((Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
            (Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
              ![(v0 : E), (v1 : E), (p : E), (q : E)]) : Fin 6 → E) (sharpGradKoszulKernelNegativePermutation 4)),
          ((Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
            (Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
              ![(v0 : E), (v1 : E), (p : E), (q : E)]) : Fin 6 → E) (sharpGradKoszulKernelNegativePermutation 5))] =
        unitModel (I := I) (M := M) g₀ 3 (koszulCovecCc (I := I) g₀ P) x
          ![(v1 : E), (v0 : E),
            ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)] := by
      refine congrArg _ ?_
      funext k
      fin_cases k <;> rfl
    rw [h1, h2]
    congr 1
    have h12 := connectionDifferenceLowered_unitModel_value (I := I) (M := M) g₀ g₁ x
      ![q, p, smoothOrthoFrame (I := I) g₀ x e x]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons] at h12
    exact h12
  have hM4 : unitModel (I := I) (M := M) g₀ 4
      (koszulConnectionDifferenceFoldWeight (I := I) (M := M) g₀ g₁ sharpGradKoszulKernelNegativeKoszulSwapPermutation P) x
      ![(v0 : E), (v1 : E), (p : E), (q : E)] =
      ∑ e : Fin (Module.finrank ℝ E),
        g₀.inner x (PDE.DeTurck.connectionDifference (I := I) g₁ g₀ x q p)
            (smoothOrthoFrame (I := I) g₀ x e x) *
          unitModel (I := I) (M := M) g₀ 3 (koszulCovecCc (I := I) g₀ P) x
            ![((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E),
              (v0 : E), (v1 : E)] := by
    rw [show koszulConnectionDifferenceFoldWeight (I := I) (M := M) g₀ g₁ sharpGradKoszulKernelNegativeKoszulSwapPermutation P =
        ccOperatorFieldComp (I := I) (M := M) g₀ 0 6 4 (cometricDoubleTraceField (I := I) g₀ 4)
          (rsDomDomCongrSection (I := I) (M := M) g₀ 0 6 sharpGradKoszulKernelNegativeKoszulSwapPermutation
            (ccOperatorFieldComp (I := I) (M := M) g₀ 0 3 6
              (slotExtendIter (I := I) (M := M) g₀ 0 3 3 (koszulCovecCc (I := I) g₀ P))
              (metricLoweredConnectionDifferenceCoefficient (I := I) g₀ g₁))) from rfl]
    rw [koszulConnectionDifferenceFoldWeight_unitModel_general (I := I) (M := M) g₀ g₁ sharpGradKoszulKernelNegativeKoszulSwapPermutation P x
      ![(v0 : E), (v1 : E), (p : E), (q : E)]]
    refine Finset.sum_congr rfl fun e _ => ?_
    have h1 : unitModel (I := I) (M := M) g₀ 3 (metricLoweredConnectionDifferenceCoefficient (I := I) g₀ g₁) x
        ![((Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
            (Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
              ![(v0 : E), (v1 : E), (p : E), (q : E)]) : Fin 6 → E) (sharpGradKoszulKernelNegativeKoszulSwapPermutation 0)),
          ((Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
            (Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
              ![(v0 : E), (v1 : E), (p : E), (q : E)]) : Fin 6 → E) (sharpGradKoszulKernelNegativeKoszulSwapPermutation 1)),
          ((Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
            (Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
              ![(v0 : E), (v1 : E), (p : E), (q : E)]) : Fin 6 → E) (sharpGradKoszulKernelNegativeKoszulSwapPermutation 2))] =
        unitModel (I := I) (M := M) g₀ 3 (metricLoweredConnectionDifferenceCoefficient (I := I) g₀ g₁) x
          ![(q : E), (p : E),
            ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)] := by
      refine congrArg _ ?_
      funext k
      fin_cases k <;> rfl
    have h2 : unitModel (I := I) (M := M) g₀ 3 (koszulCovecCc (I := I) g₀ P) x
        ![((Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
            (Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
              ![(v0 : E), (v1 : E), (p : E), (q : E)]) : Fin 6 → E) (sharpGradKoszulKernelNegativeKoszulSwapPermutation 3)),
          ((Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
            (Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
              ![(v0 : E), (v1 : E), (p : E), (q : E)]) : Fin 6 → E) (sharpGradKoszulKernelNegativeKoszulSwapPermutation 4)),
          ((Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
            (Fin.cons ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)
              ![(v0 : E), (v1 : E), (p : E), (q : E)]) : Fin 6 → E) (sharpGradKoszulKernelNegativeKoszulSwapPermutation 5))] =
        unitModel (I := I) (M := M) g₀ 3 (koszulCovecCc (I := I) g₀ P) x
          ![((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E),
            (v0 : E), (v1 : E)] := by
      refine congrArg _ ?_
      funext k
      fin_cases k <;> rfl
    rw [h1, h2]
    congr 1
    have h12 := connectionDifferenceLowered_unitModel_value (I := I) (M := M) g₀ g₁ x
      ![q, p, smoothOrthoFrame (I := I) g₀ x e x]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons] at h12
    exact h12
  have hexp : ∀ r s : TangentSpace I x,
      ((PDE.DeTurck.connectionDifference (I := I) g₁ g₀ x r s : TangentSpace I x) : E) =
        ∑ e : Fin (Module.finrank ℝ E),
          g₀.inner x (PDE.DeTurck.connectionDifference (I := I) g₁ g₀ x r s)
            (smoothOrthoFrame (I := I) g₀ x e x) •
          ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E) := by
    intro r s
    rw [show (∑ e : Fin (Module.finrank ℝ E),
        g₀.inner x (PDE.DeTurck.connectionDifference (I := I) g₁ g₀ x r s)
          (smoothOrthoFrame (I := I) g₀ x e x) •
        ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)) =
        ((∑ e : Fin (Module.finrank ℝ E),
          g₀.inner x (PDE.DeTurck.connectionDifference (I := I) g₁ g₀ x r s)
            (smoothOrthoFrame (I := I) g₀ x e x) •
          smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E) from rfl]
    conv_lhs => rw [orthoFrame_expansion_at_center (I := I) (M := M) g₀ x
      (PDE.DeTurck.connectionDifference (I := I) g₁ g₀ x r s)]
  have hT1 : g₁.inner x (PDE.DeTurck.connectionDifference (I := I) g₁ g₀ x p
        (PDE.DeTurck.connectionDifference (I := I) g₁ g₀ x q v0)) v1 =
      ∑ e : Fin (Module.finrank ℝ E),
        g₀.inner x (PDE.DeTurck.connectionDifference (I := I) g₁ g₀ x q v0)
            (smoothOrthoFrame (I := I) g₀ x e x) *
          unitModel (I := I) (M := M) g₀ 3 (koszulCovecCc (I := I) g₀ P) x
            ![(v1 : E), (p : E),
              ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)] := by
    rw [← koszulCovecCc_unitModel_eq_connectionDifference_g1_inner (I := I) (M := M) g₀ g₁ P htie x p
      (PDE.DeTurck.connectionDifference (I := I) g₁ g₀ x q v0) v1]
    conv_lhs => rw [hexp q v0]
    exact toModel_vec3_slot2_sum_smul (E := E)
      (unitModel (I := I) (M := M) g₀ 3 (koszulCovecCc (I := I) g₀ P) x)
      (Module.finrank ℝ E)
      (fun e => g₀.inner x (PDE.DeTurck.connectionDifference (I := I) g₁ g₀ x q v0)
        (smoothOrthoFrame (I := I) g₀ x e x))
      (fun e => ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E))
      ((v1 : TangentSpace I x) : E) ((p : TangentSpace I x) : E)
  have hT2 : g₁.inner x (PDE.DeTurck.connectionDifference (I := I) g₁ g₀ x q v0)
        (PDE.DeTurck.connectionDifference (I := I) g₁ g₀ x p v1) =
      ∑ e : Fin (Module.finrank ℝ E),
        g₀.inner x (PDE.DeTurck.connectionDifference (I := I) g₁ g₀ x q v0)
            (smoothOrthoFrame (I := I) g₀ x e x) *
          unitModel (I := I) (M := M) g₀ 3 (koszulCovecCc (I := I) g₀ P) x
            ![((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E),
              (p : E), (v1 : E)] := by
    rw [g₁.symm x (PDE.DeTurck.connectionDifference (I := I) g₁ g₀ x q v0)
      (PDE.DeTurck.connectionDifference (I := I) g₁ g₀ x p v1)]
    rw [← koszulCovecCc_unitModel_eq_connectionDifference_g1_inner (I := I) (M := M) g₀ g₁ P htie x p v1
      (PDE.DeTurck.connectionDifference (I := I) g₁ g₀ x q v0)]
    conv_lhs => rw [hexp q v0]
    exact toModel_vec3_slot0_sum_smul (E := E)
      (unitModel (I := I) (M := M) g₀ 3 (koszulCovecCc (I := I) g₀ P) x)
      (Module.finrank ℝ E)
      (fun e => g₀.inner x (PDE.DeTurck.connectionDifference (I := I) g₁ g₀ x q v0)
        (smoothOrthoFrame (I := I) g₀ x e x))
      (fun e => ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E))
      ((p : TangentSpace I x) : E) ((v1 : TangentSpace I x) : E)
  have hT3 : g₁.inner x (PDE.DeTurck.connectionDifference (I := I) g₁ g₀ x v0
        (PDE.DeTurck.connectionDifference (I := I) g₁ g₀ x q p)) v1 =
      ∑ e : Fin (Module.finrank ℝ E),
        g₀.inner x (PDE.DeTurck.connectionDifference (I := I) g₁ g₀ x q p)
            (smoothOrthoFrame (I := I) g₀ x e x) *
          unitModel (I := I) (M := M) g₀ 3 (koszulCovecCc (I := I) g₀ P) x
            ![(v1 : E), (v0 : E),
              ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E)] := by
    rw [← koszulCovecCc_unitModel_eq_connectionDifference_g1_inner (I := I) (M := M) g₀ g₁ P htie x v0
      (PDE.DeTurck.connectionDifference (I := I) g₁ g₀ x q p) v1]
    conv_lhs => rw [hexp q p]
    exact toModel_vec3_slot2_sum_smul (E := E)
      (unitModel (I := I) (M := M) g₀ 3 (koszulCovecCc (I := I) g₀ P) x)
      (Module.finrank ℝ E)
      (fun e => g₀.inner x (PDE.DeTurck.connectionDifference (I := I) g₁ g₀ x q p)
        (smoothOrthoFrame (I := I) g₀ x e x))
      (fun e => ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E))
      ((v1 : TangentSpace I x) : E) ((v0 : TangentSpace I x) : E)
  have hT4 : g₁.inner x (PDE.DeTurck.connectionDifference (I := I) g₁ g₀ x q p)
        (PDE.DeTurck.connectionDifference (I := I) g₁ g₀ x v0 v1) =
      ∑ e : Fin (Module.finrank ℝ E),
        g₀.inner x (PDE.DeTurck.connectionDifference (I := I) g₁ g₀ x q p)
            (smoothOrthoFrame (I := I) g₀ x e x) *
          unitModel (I := I) (M := M) g₀ 3 (koszulCovecCc (I := I) g₀ P) x
            ![((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E),
              (v0 : E), (v1 : E)] := by
    rw [g₁.symm x (PDE.DeTurck.connectionDifference (I := I) g₁ g₀ x q p)
      (PDE.DeTurck.connectionDifference (I := I) g₁ g₀ x v0 v1)]
    rw [← koszulCovecCc_unitModel_eq_connectionDifference_g1_inner (I := I) (M := M) g₀ g₁ P htie x v0 v1
      (PDE.DeTurck.connectionDifference (I := I) g₁ g₀ x q p)]
    conv_lhs => rw [hexp q p]
    exact toModel_vec3_slot0_sum_smul (E := E)
      (unitModel (I := I) (M := M) g₀ 3 (koszulCovecCc (I := I) g₀ P) x)
      (Module.finrank ℝ E)
      (fun e => g₀.inner x (PDE.DeTurck.connectionDifference (I := I) g₁ g₀ x q p)
        (smoothOrthoFrame (I := I) g₀ x e x))
      (fun e => ((smoothOrthoFrame (I := I) g₀ x e x : TangentSpace I x) : E))
      ((v0 : TangentSpace I x) : E) ((v1 : TangentSpace I x) : E)
  rw [DifferentialGeometry.Analysis.Parabolic.TensorSpectral.unitModel_sub (I := I) (M := M) g₀ 4
    (koszulConnectionDifferenceFoldWeight (I := I) (M := M) g₀ g₁ sharpGradKoszulKernelPositivePermutation P +
      koszulConnectionDifferenceFoldWeight (I := I) (M := M) g₀ g₁ sharpGradKoszulKernelPositiveKoszulSwapPermutation P)
    (koszulConnectionDifferenceFoldWeight (I := I) (M := M) g₀ g₁ sharpGradKoszulKernelNegativePermutation P +
      koszulConnectionDifferenceFoldWeight (I := I) (M := M) g₀ g₁ sharpGradKoszulKernelNegativeKoszulSwapPermutation P) x]
  rw [DifferentialGeometry.Analysis.Parabolic.TensorSpectral.unitModel_add (I := I) (M := M) g₀ 4
    (koszulConnectionDifferenceFoldWeight (I := I) (M := M) g₀ g₁ sharpGradKoszulKernelPositivePermutation P)
    (koszulConnectionDifferenceFoldWeight (I := I) (M := M) g₀ g₁ sharpGradKoszulKernelPositiveKoszulSwapPermutation P) x]
  rw [DifferentialGeometry.Analysis.Parabolic.TensorSpectral.unitModel_add (I := I) (M := M) g₀ 4
    (koszulConnectionDifferenceFoldWeight (I := I) (M := M) g₀ g₁ sharpGradKoszulKernelNegativePermutation P)
    (koszulConnectionDifferenceFoldWeight (I := I) (M := M) g₀ g₁ sharpGradKoszulKernelNegativeKoszulSwapPermutation P) x]
  rw [sub_apply, add_apply,
    add_apply]
  rw [hM1, hM2, hM3, hM4]
  rw [sharpGradKoszulKernelBilin_apply (I := I) g₀ g₁ (ccTensor02Symm (I := I) g₀ P) x p q v0 v1]
  rw [sharpRaisedKoszulVec_symmS_eq_connectionDifference (I := I) (M := M) g₀ g₁ P htie x q v0,
    sharpRaisedKoszulVec_symmS_eq_connectionDifference (I := I) (M := M) g₀ g₁ P htie x q p]
  rw [hT1, hT2, hT3, hT4]

omit [SigmaCompactSpace M] in
lemma sharpGradKoszulResidualField_eq_decomposition (P : SmoothCcTensor g₀ 0 2)
    (htie : ∀ (y : M) (v w : TangentSpace I y),
      g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w) :
    ricciArmSharpGradKoszulResidualField (I := I) (M := M) g₀ g₁ (ccTensor02Symm (I := I) g₀ P) =
      (2 : ℝ) •
        ccOperatorFieldComp (I := I) (M := M) g₀ 2 6 2
          (secondMetricPairTraceOperator (I := I) (M := M) g₀ g₁)
          (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 ricciFoldRemainderSlotPerm
            (slotExtendIter (I := I) (M := M) g₀ 0 4 2
              ((koszulConnectionDifferenceFoldWeight (I := I) (M := M) g₀ g₁ sharpGradKoszulKernelPositivePermutation P +
                  koszulConnectionDifferenceFoldWeight (I := I) (M := M) g₀ g₁ sharpGradKoszulKernelPositiveKoszulSwapPermutation P) -
                (koszulConnectionDifferenceFoldWeight (I := I) (M := M) g₀ g₁ sharpGradKoszulKernelNegativePermutation P +
                  koszulConnectionDifferenceFoldWeight (I := I) (M := M) g₀ g₁ sharpGradKoszulKernelNegativeKoszulSwapPermutation P)))) := by
  classical
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  apply tensorRSSpace_ext 2 2 x
  intro D
  apply Tensor0SSpace.toModel_injective
  apply ContinuousMultilinearMap.ext
  intro v
  beta_reduce
  have hRHSsmul : ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
      (((2 : ℝ) •
        ccOperatorFieldComp (I := I) (M := M) g₀ 2 6 2
          (secondMetricPairTraceOperator (I := I) (M := M) g₀ g₁)
          (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 ricciFoldRemainderSlotPerm
            (slotExtendIter (I := I) (M := M) g₀ 0 4 2
              ((koszulConnectionDifferenceFoldWeight (I := I) (M := M) g₀ g₁ sharpGradKoszulKernelPositivePermutation P +
                  koszulConnectionDifferenceFoldWeight (I := I) (M := M) g₀ g₁ sharpGradKoszulKernelPositiveKoszulSwapPermutation P) -
                (koszulConnectionDifferenceFoldWeight (I := I) (M := M) g₀ g₁ sharpGradKoszulKernelNegativePermutation P +
                  koszulConnectionDifferenceFoldWeight (I := I) (M := M) g₀ g₁ sharpGradKoszulKernelNegativeKoszulSwapPermutation P))))).toSection x)) D) =
      (2 : ℝ) • ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
        (ccOperatorFieldComp (I := I) (M := M) g₀ 2 6 2
          (secondMetricPairTraceOperator (I := I) (M := M) g₀ g₁)
          (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 ricciFoldRemainderSlotPerm
            (slotExtendIter (I := I) (M := M) g₀ 0 4 2
              ((koszulConnectionDifferenceFoldWeight (I := I) (M := M) g₀ g₁ sharpGradKoszulKernelPositivePermutation P +
                  koszulConnectionDifferenceFoldWeight (I := I) (M := M) g₀ g₁ sharpGradKoszulKernelPositiveKoszulSwapPermutation P) -
                (koszulConnectionDifferenceFoldWeight (I := I) (M := M) g₀ g₁ sharpGradKoszulKernelNegativePermutation P +
                  koszulConnectionDifferenceFoldWeight (I := I) (M := M) g₀ g₁ sharpGradKoszulKernelNegativeKoszulSwapPermutation P))))).toSection x)
                    D) := by
    rw [show ((((2 : ℝ) •
        ccOperatorFieldComp (I := I) (M := M) g₀ 2 6 2
          (secondMetricPairTraceOperator (I := I) (M := M) g₀ g₁)
          (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 ricciFoldRemainderSlotPerm
            (slotExtendIter (I := I) (M := M) g₀ 0 4 2
              ((koszulConnectionDifferenceFoldWeight (I := I) (M := M) g₀ g₁ sharpGradKoszulKernelPositivePermutation P +
                  koszulConnectionDifferenceFoldWeight (I := I) (M := M) g₀ g₁ sharpGradKoszulKernelPositiveKoszulSwapPermutation P) -
                (koszulConnectionDifferenceFoldWeight (I := I) (M := M) g₀ g₁ sharpGradKoszulKernelNegativePermutation P +
                  koszulConnectionDifferenceFoldWeight (I := I) (M := M) g₀ g₁ sharpGradKoszulKernelNegativeKoszulSwapPermutation P))))).toSection x)) =
        (2 : ℝ) •
          ((ccOperatorFieldComp (I := I) (M := M) g₀ 2 6 2
            (secondMetricPairTraceOperator (I := I) (M := M) g₀ g₁)
            (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 ricciFoldRemainderSlotPerm
              (slotExtendIter (I := I) (M := M) g₀ 0 4 2
                ((koszulConnectionDifferenceFoldWeight (I := I) (M := M) g₀ g₁ sharpGradKoszulKernelPositivePermutation P +
                    koszulConnectionDifferenceFoldWeight (I := I) (M := M) g₀ g₁ sharpGradKoszulKernelPositiveKoszulSwapPermutation P) -
                  (koszulConnectionDifferenceFoldWeight (I := I) (M := M) g₀ g₁ sharpGradKoszulKernelNegativePermutation P +
                    koszulConnectionDifferenceFoldWeight (I := I) (M := M) g₀ g₁ sharpGradKoszulKernelNegativeKoszulSwapPermutation P))))).toSection x)
                      from by
      rw [SmoothCcTensor.toSection_smul]; rfl]
    rfl
  rw [hRHSsmul, Tensor0SSpace.toModel_smul, smul_apply, smul_eq_mul]
  rw [secondMetricPairTraceOperator_apply_toModel (I := I) (M := M) g₀ g₁
    ((koszulConnectionDifferenceFoldWeight (I := I) (M := M) g₀ g₁ sharpGradKoszulKernelPositivePermutation P +
        koszulConnectionDifferenceFoldWeight (I := I) (M := M) g₀ g₁ sharpGradKoszulKernelPositiveKoszulSwapPermutation P) -
      (koszulConnectionDifferenceFoldWeight (I := I) (M := M) g₀ g₁ sharpGradKoszulKernelNegativePermutation P +
        koszulConnectionDifferenceFoldWeight (I := I) (M := M) g₀ g₁ sharpGradKoszulKernelNegativeKoszulSwapPermutation P)) x D v]
  rw [show ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
      (ricciArmSharpGradKoszulResidualField (I := I) (M := M) g₀ g₁
        (ccTensor02Symm (I := I) g₀ P)).toSection x) D) =
      sharpGradKoszulBiContrFib (I := I) g₀ g₁ (ccTensor02Symm (I := I) g₀ P) x D from rfl]
  rw [show sharpGradKoszulBiContrFib (I := I) g₀ g₁ (ccTensor02Symm (I := I) g₀ P) x =
      sharpGradKoszulBiContrFibFixedFrame (I := I) g₀ g₁ (ccTensor02Symm (I := I) g₀ P)
        (smoothOrthoFrame (I := I) g₁ x) x from rfl]
  rw [sharpGradKoszulBiContrFibFixedFrame_toModel (I := I) g₀ g₁ (ccTensor02Symm (I := I) g₀ P)
    (smoothOrthoFrame (I := I) g₁ x) x D v]
  congr 1
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  refine Finset.sum_congr rfl fun a _ => ?_
  let v0 : TangentSpace I x :=
    (tangentSpaceModelContinuousLinearEquiv (I := I) x).symm (v 0)
  let v1 : TangentSpace I x :=
    (tangentSpaceModelContinuousLinearEquiv (I := I) x).symm (v 1)
  have hv0Model : (v0 : E) = v 0 := by
    with_unfolding_all
      exact (tangentSpaceModelContinuousLinearEquiv (I := I) x).apply_symm_apply (v 0)
  have hv1Model : (v1 : E) = v 1 := by
    with_unfolding_all
      exact (tangentSpaceModelContinuousLinearEquiv (I := I) x).apply_symm_apply (v 1)
  have haModel :
      ((smoothOrthoFrame (I := I) g₁ x a x : TangentSpace I x) : E) =
        (tangentSpaceModelContinuousLinearEquiv (I := I) x)
          (smoothOrthoFrame (I := I) g₁ x a x) := by
    with_unfolding_all
      rfl
  have hbModel :
      ((smoothOrthoFrame (I := I) g₁ x b x : TangentSpace I x) : E) =
        (tangentSpaceModelContinuousLinearEquiv (I := I) x)
          (smoothOrthoFrame (I := I) g₁ x b x) := by
    with_unfolding_all
      rfl
  have hfold : unitModel (I := I) (M := M) g₀ 4
      ((koszulConnectionDifferenceFoldWeight (I := I) (M := M) g₀ g₁ sharpGradKoszulKernelPositivePermutation P +
          koszulConnectionDifferenceFoldWeight (I := I) (M := M) g₀ g₁ sharpGradKoszulKernelPositiveKoszulSwapPermutation P) -
        (koszulConnectionDifferenceFoldWeight (I := I) (M := M) g₀ g₁ sharpGradKoszulKernelNegativePermutation P +
          koszulConnectionDifferenceFoldWeight (I := I) (M := M) g₀ g₁ sharpGradKoszulKernelNegativeKoszulSwapPermutation P)) x
      ![v 0, v 1,
        (tangentSpaceModelContinuousLinearEquiv (I := I) x)
          (smoothOrthoFrame (I := I) g₁ x a x),
        (tangentSpaceModelContinuousLinearEquiv (I := I) x)
          (smoothOrthoFrame (I := I) g₁ x b x)] =
      sharpGradKoszulKernelBilin (I := I) g₀ g₁ (ccTensor02Symm (I := I) g₀ P) x
        (smoothOrthoFrame (I := I) g₁ x a x) (smoothOrthoFrame (I := I) g₁ x b x)
        v0 v1 := by
    have h := sharpGradKoszulKernel_foldWeights_unitModel (I := I) (M := M) g₀ g₁ P htie x
      (smoothOrthoFrame (I := I) g₁ x a x) (smoothOrthoFrame (I := I) g₁ x b x)
      v0 v1
    rw [hv0Model, hv1Model, haModel, hbModel] at h
    exact h
  have hD : Tensor0SSpace.toModel D
        ![(smoothOrthoFrame (I := I) g₁ x a x : TangentSpace I x),
          (smoothOrthoFrame (I := I) g₁ x b x : TangentSpace I x)] =
      Tensor0SSpace.toModel D
        ![(tangentSpaceModelContinuousLinearEquiv (I := I) x)
            (smoothOrthoFrame (I := I) g₁ x a x),
          (tangentSpaceModelContinuousLinearEquiv (I := I) x)
            (smoothOrthoFrame (I := I) g₁ x b x)] := by
    apply congrArg (Tensor0SSpace.toModel D)
    funext i
    fin_cases i
    · exact haModel
    · exact hbModel
  rw [hD]
  rw [hfold]
  with_unfolding_all
    rw [hv0Model, hv1Model]

section NormedKoszulConnectionDifferenceFoldGrid

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

variable (g₀ : SmoothRiemannianMetric I M)

lemma exists_riemannianFiberNormSq_iteratedCovGrad_koszulConnectionDifferenceFoldWeight_gridWindow_le
    (σ : Equiv.Perm (Fin 6))
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ C : ℕ → ℝ, (∀ w, 0 ≤ C w) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        (_htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀) (_hδ0 : 0 ≤ δ)
        (_hbound : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P)
          δ)
        (w K : ℕ) (_hwK : w + 1 ≤ K) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + w) x
            ((iteratedCovGrad (I := I) g₀ 0 4 w
              (ccOperatorFieldComp (I := I) (M := M) g₀ 0 6 4
                (cometricDoubleTraceField (I := I) g₀ 4)
                (rsDomDomCongrSection (I := I) (M := M) g₀ 0 6 σ
                  (ccOperatorFieldComp (I := I) (M := M) g₀ 0 3 6
                    (slotExtendIter (I := I) (M := M) g₀ 0 3 3
                      (koszulCovecCc (I := I) g₀ P))
                    (metricLoweredConnectionDifferenceCoefficient (I := I) g₀ g₁))))).toSection x) ≤
          C w * Combinatorics.boundedFactorGridWindow
            (fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
              ((iteratedCovGrad (I := I) g₀ 0 2 l P).toSection x)) K (w + 3) := by
  classical
  set fr : ℝ := (Module.finrank ℝ E : ℝ) with hfr_def
  have hfr_nn : 0 ≤ fr := Nat.cast_nonneg _
  obtain ⟨CA, hCA_nn, hCA⟩ :=
    exists_riemannianFiberNormSq_iteratedCovGrad_connectionDifferenceSection_tgrid (I := I) (M := M) g₀ hδ₀
  set KD : ℕ → ℝ := fun u =>
    (exists_bound_riemannianFiberNormSq_smoothCcTensor (I := I) (M := M) g₀ 6 (4 + u)
      (iteratedCovGrad (I := I) g₀ 6 4 u (cometricDoubleTraceField (I := I) g₀ 4))).choose
    with hKD_def
  have hKD_nn : ∀ u, 0 ≤ KD u := fun u =>
    (exists_bound_riemannianFiberNormSq_smoothCcTensor (I := I) (M := M) g₀ 6 (4 + u)
      (iteratedCovGrad (I := I) g₀ 6 4 u
        (cometricDoubleTraceField (I := I) g₀ 4))).choose_spec.1
  have hKD : ∀ u (y : M),
      riemannianFiberNormSq (I := I) (M := M) g₀ 6 (4 + u) y
          ((iteratedCovGrad (I := I) g₀ 6 4 u
            (cometricDoubleTraceField (I := I) g₀ 4)).toSection y) ≤ KD u := fun u =>
    (exists_bound_riemannianFiberNormSq_smoothCcTensor (I := I) (M := M) g₀ 6 (4 + u)
      (iteratedCovGrad (I := I) g₀ 6 4 u
        (cometricDoubleTraceField (I := I) g₀ 4))).choose_spec.2
  refine ⟨fun w => diagonalGridGrowthFactor (E := E) w *
      ∑ w₁ ∈ Finset.range (w + 1), KD w₁ *
        ∑ w₂ ∈ Finset.range (w + 1 - w₁),
          diagonalGridGrowthFactor (E := E) w₂ *
            ∑ w₃ ∈ Finset.range (w₂ + 1), (10 * fr ^ 3) *
              ∑ w₄ ∈ Finset.range (w₂ + 1 - w₃),
                CA w₄ * Combinatorics.windowPairCellCount (w₃ + 2) (w₄ + 2),
    fun w => mul_nonneg (operatorFieldApplicationGdiag_nonneg (E := E) w)
      (Finset.sum_nonneg fun w₁ _ => mul_nonneg (hKD_nn w₁)
        (Finset.sum_nonneg fun w₂ _ => mul_nonneg (operatorFieldApplicationGdiag_nonneg (E := E) w₂)
          (Finset.sum_nonneg fun w₃ _ =>
            mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hfr_nn 3))
              (Finset.sum_nonneg fun w₄ _ => mul_nonneg (hCA_nn w₄)
                (Combinatorics.windowPairCellCount_nonneg _ _))))), ?_⟩
  intro g₁ P htie δ hδ_le hδ0 hbound w K hwK x
  set b : ℕ → ℝ := fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
    ((iteratedCovGrad (I := I) g₀ 0 2 l P).toSection x) with hb_def
  have hb_nn : ∀ l, 0 ≤ b l :=
    fun l => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + l) x _
  have hκ : ∀ w₃ : ℕ, w₃ ≤ w →
      riemannianFiberNormSq (I := I) (M := M) g₀ 3 (6 + w₃) x
          ((iteratedCovGrad (I := I) g₀ 3 6 w₃
            (slotExtendIter (I := I) (M := M) g₀ 0 3 3
              (koszulCovecCc (I := I) g₀ P))).toSection x) ≤
        (10 * fr ^ 3) * Combinatorics.boundedFactorGridWindow b K (w₃ + 2) := by
    intro w₃ hw₃
    rw [show slotExtendIter (I := I) (M := M) g₀ 0 3 3 (koszulCovecCc (I := I) g₀ P) =
        slotExtend (I := I) (M := M) g₀ 2 5 (slotExtend (I := I) (M := M) g₀ 1 4
          (slotExtend (I := I) (M := M) g₀ 0 3 (koszulCovecCc (I := I) g₀ P))) from rfl]
    refine le_trans (riemannianFiberNormSq_iteratedCovGrad_slotExtend_le (I := I) (M := M) g₀ 2 5
      (slotExtend (I := I) (M := M) g₀ 1 4
        (slotExtend (I := I) (M := M) g₀ 0 3 (koszulCovecCc (I := I) g₀ P))) w₃ x) ?_
    refine le_trans (mul_le_mul_of_nonneg_left
      (riemannianFiberNormSq_iteratedCovGrad_slotExtend_le (I := I) (M := M) g₀ 1 4
        (slotExtend (I := I) (M := M) g₀ 0 3 (koszulCovecCc (I := I) g₀ P)) w₃ x)
      hfr_nn) ?_
    refine le_trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
      (riemannianFiberNormSq_iteratedCovGrad_slotExtend_le (I := I) (M := M) g₀ 0 3
        (koszulCovecCc (I := I) g₀ P) w₃ x) hfr_nn) hfr_nn) ?_
    refine le_trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left
        (riemannianFiberNormSq_iteratedCovGrad_koszulCovecCc_pointwise (I := I) (M := M) g₀ P w₃ x)
        hfr_nn) hfr_nn) hfr_nn) ?_
    have hb1 : b (w₃ + 1) ≤ Combinatorics.boundedFactorGridWindow b K (w₃ + 2) := by
      refine le_trans (single_b_le_grid b hb_nn (w₃ + 1) (by omega)) ?_
      exact Combinatorics.antidiagonalTupleGrid_le_boundedFactorGridWindow b hb_nn
        (by omega) (by omega)
    calc fr * (fr * (fr * (10 * b (w₃ + 1))))
        = (10 * fr ^ 3) * b (w₃ + 1) := by ring
      _ ≤ (10 * fr ^ 3) * Combinatorics.boundedFactorGridWindow b K (w₃ + 2) := by
          refine mul_le_mul_of_nonneg_left hb1 ?_
          exact mul_nonneg (by norm_num) (pow_nonneg hfr_nn 3)
  have hcdl : ∀ w₄ : ℕ, w₄ ≤ w →
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + w₄) x
          ((iteratedCovGrad (I := I) g₀ 0 3 w₄
            (metricLoweredConnectionDifferenceCoefficient (I := I) g₀ g₁)).toSection x) ≤
        CA w₄ * Combinatorics.boundedFactorGridWindow b K (w₄ + 2) := by
    intro w₄ hw₄
    rw [riemannianFiberNormSq_iteratedCovGrad_connectionDifferenceLowered_eq_connectionDifferenceSection (I := I) (M := M) g₀ g₁ w₄ x]
    refine le_trans (hCA g₁ P htie hδ_le hδ0 hbound w₄ x) ?_
    refine mul_le_mul_of_nonneg_left ?_ (hCA_nn w₄)
    have heq : (∑ k ∈ Finset.range (w₄ + 2), Combinatorics.antidiagonalTupleGrid b k) =
        Combinatorics.boundedFactorGridWindow b (w₄ + 1) (w₄ + 2) := by
      rw [Combinatorics.boundedFactorGridWindow]
      refine Finset.sum_congr rfl fun k hk => ?_
      rw [Finset.mem_range] at hk
      exact Combinatorics.antidiagonalTupleGrid_eq_boundedFactorGrid b (by omega)
    calc (∑ k ∈ Finset.range (w₄ + 2), Combinatorics.antidiagonalTupleGrid b k)
        = Combinatorics.boundedFactorGridWindow b (w₄ + 1) (w₄ + 2) := heq
      _ ≤ Combinatorics.boundedFactorGridWindow b K (w₄ + 2) :=
          Combinatorics.boundedFactorGridWindow_mono b hb_nn (by omega) (le_refl _)
  have hbase : ∀ w₂ : ℕ, w₂ ≤ w →
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (6 + w₂) x
          ((iteratedCovGrad (I := I) g₀ 0 6 w₂
            (rsDomDomCongrSection (I := I) (M := M) g₀ 0 6 σ
              (ccOperatorFieldComp (I := I) (M := M) g₀ 0 3 6
                (slotExtendIter (I := I) (M := M) g₀ 0 3 3
                  (koszulCovecCc (I := I) g₀ P))
                (metricLoweredConnectionDifferenceCoefficient (I := I) g₀ g₁)))).toSection x) ≤
        (diagonalGridGrowthFactor (E := E) w₂ *
          ∑ w₃ ∈ Finset.range (w₂ + 1), (10 * fr ^ 3) *
            ∑ w₄ ∈ Finset.range (w₂ + 1 - w₃),
              CA w₄ * Combinatorics.windowPairCellCount (w₃ + 2) (w₄ + 2)) *
          Combinatorics.boundedFactorGridWindow b K (w₂ + 3) := by
    intro w₂ hw₂
    rw [riemannianFiberNormSq_iteratedCovGrad_rsDomDomCongrSection_eq (I := I) (M := M) g₀ 0 6 σ _
      w₂ x]
    refine le_trans
      (riemannianFiberNormSq_iteratedCovGrad_ccTensorCompose_diagonalProductGrid_leftFactor_le
      (I := I)
      (M := M) g₀ w₂ 0 3 6
      (slotExtendIter (I := I) (M := M) g₀ 0 3 3 (koszulCovecCc (I := I) g₀ P))
      (metricLoweredConnectionDifferenceCoefficient (I := I) g₀ g₁) x) ?_
    calc diagonalGridGrowthFactor (E := E) w₂ *
          ∑ w₃ ∈ Finset.range (w₂ + 1),
            riemannianFiberNormSq (I := I) (M := M) g₀ 3 (6 + w₃) x
                ((iteratedCovGrad (I := I) g₀ 3 6 w₃
                  (slotExtendIter (I := I) (M := M) g₀ 0 3 3
                    (koszulCovecCc (I := I) g₀ P))).toSection x) *
              ∑ w₄ ∈ Finset.range (w₂ + 1 - w₃),
                riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + w₄) x
                  ((iteratedCovGrad (I := I) g₀ 0 3 w₄
                    (metricLoweredConnectionDifferenceCoefficient (I := I) g₀ g₁)).toSection x)
        ≤ diagonalGridGrowthFactor (E := E) w₂ *
            ∑ w₃ ∈ Finset.range (w₂ + 1),
              ((10 * fr ^ 3) * Combinatorics.boundedFactorGridWindow b K (w₃ + 2)) *
              ∑ w₄ ∈ Finset.range (w₂ + 1 - w₃),
                (CA w₄ * Combinatorics.boundedFactorGridWindow b K (w₄ + 2)) := by
          refine mul_le_mul_of_nonneg_left
            (Finset.sum_le_sum fun w₃ hw₃ => ?_) (operatorFieldApplicationGdiag_nonneg (E := E) w₂)
          rw [Finset.mem_range] at hw₃
          refine mul_le_mul (hκ w₃ (by omega)) (Finset.sum_le_sum fun w₄ hw₄ => ?_)
            (Finset.sum_nonneg fun w₄ _ =>
              riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (3 + w₄) x _)
            (mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hfr_nn 3))
              (Combinatorics.boundedFactorGridWindow_nonneg b hb_nn _ _))
          rw [Finset.mem_range] at hw₄
          exact hcdl w₄ (by omega)
      _ ≤ (diagonalGridGrowthFactor (E := E) w₂ *
            ∑ w₃ ∈ Finset.range (w₂ + 1), (10 * fr ^ 3) *
              ∑ w₄ ∈ Finset.range (w₂ + 1 - w₃),
                CA w₄ * Combinatorics.windowPairCellCount (w₃ + 2) (w₄ + 2)) *
            Combinatorics.boundedFactorGridWindow b K (w₂ + 3) := by
          rw [mul_assoc]
          refine mul_le_mul_of_nonneg_left ?_ (operatorFieldApplicationGdiag_nonneg (E := E) w₂)
          rw [Finset.sum_mul]
          refine Finset.sum_le_sum fun w₃ hw₃ => ?_
          rw [Finset.mul_sum, Finset.mul_sum, Finset.sum_mul]
          refine Finset.sum_le_sum fun w₄ hw₄ => ?_
          rw [Finset.mem_range] at hw₃ hw₄
          calc (10 * fr ^ 3) * Combinatorics.boundedFactorGridWindow b K (w₃ + 2) *
                (CA w₄ * Combinatorics.boundedFactorGridWindow b K (w₄ + 2))
              = ((10 * fr ^ 3) * CA w₄) *
                  (Combinatorics.boundedFactorGridWindow b K (w₃ + 2) *
                    Combinatorics.boundedFactorGridWindow b K (w₄ + 2)) := by ring
            _ ≤ ((10 * fr ^ 3) * CA w₄) *
                  (Combinatorics.windowPairCellCount (w₃ + 2) (w₄ + 2) *
                    Combinatorics.boundedFactorGridWindow b K
                      ((w₃ + 2) + (w₄ + 2) - 1)) := by
                refine mul_le_mul_of_nonneg_left ?_
                  (mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hfr_nn 3))
                    (hCA_nn w₄))
                exact Combinatorics.boundedFactorGridWindow_mul_le b hb_nn K (w₃ + 2)
                  (w₄ + 2) (by omega) (by omega)
            _ ≤ ((10 * fr ^ 3) * CA w₄) *
                  (Combinatorics.windowPairCellCount (w₃ + 2) (w₄ + 2) *
                    Combinatorics.boundedFactorGridWindow b K (w₂ + 3)) := by
                refine mul_le_mul_of_nonneg_left ?_
                  (mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hfr_nn 3))
                    (hCA_nn w₄))
                refine mul_le_mul_of_nonneg_left ?_
                  (Combinatorics.windowPairCellCount_nonneg _ _)
                exact Combinatorics.boundedFactorGridWindow_mono b hb_nn (le_refl _)
                  (by omega)
            _ = (10 * fr ^ 3) *
                  (CA w₄ * Combinatorics.windowPairCellCount (w₃ + 2) (w₄ + 2)) *
                  Combinatorics.boundedFactorGridWindow b K (w₂ + 3) := by ring
  refine le_trans
    (riemannianFiberNormSq_iteratedCovGrad_ccTensorCompose_diagonalProductGrid_leftFactor_le
    (I := I)
    (M := M) g₀ w 0 6 4 (cometricDoubleTraceField (I := I) g₀ 4)
    (rsDomDomCongrSection (I := I) (M := M) g₀ 0 6 σ
      (ccOperatorFieldComp (I := I) (M := M) g₀ 0 3 6
        (slotExtendIter (I := I) (M := M) g₀ 0 3 3 (koszulCovecCc (I := I) g₀ P))
        (metricLoweredConnectionDifferenceCoefficient (I := I) g₀ g₁))) x) ?_
  calc diagonalGridGrowthFactor (E := E) w *
        ∑ w₁ ∈ Finset.range (w + 1),
          riemannianFiberNormSq (I := I) (M := M) g₀ 6 (4 + w₁) x
              ((iteratedCovGrad (I := I) g₀ 6 4 w₁
                (cometricDoubleTraceField (I := I) g₀ 4)).toSection x) *
            ∑ w₂ ∈ Finset.range (w + 1 - w₁),
              riemannianFiberNormSq (I := I) (M := M) g₀ 0 (6 + w₂) x
                ((iteratedCovGrad (I := I) g₀ 0 6 w₂
                  (rsDomDomCongrSection (I := I) (M := M) g₀ 0 6 σ
                    (ccOperatorFieldComp (I := I) (M := M) g₀ 0 3 6
                      (slotExtendIter (I := I) (M := M) g₀ 0 3 3
                        (koszulCovecCc (I := I) g₀ P))
                      (metricLoweredConnectionDifferenceCoefficient (I := I) g₀ g₁)))).toSection x)
      ≤ diagonalGridGrowthFactor (E := E) w *
          ∑ w₁ ∈ Finset.range (w + 1), KD w₁ *
            ∑ w₂ ∈ Finset.range (w + 1 - w₁),
              ((diagonalGridGrowthFactor (E := E) w₂ *
                ∑ w₃ ∈ Finset.range (w₂ + 1), (10 * fr ^ 3) *
                  ∑ w₄ ∈ Finset.range (w₂ + 1 - w₃),
                    CA w₄ * Combinatorics.windowPairCellCount (w₃ + 2) (w₄ + 2)) *
                Combinatorics.boundedFactorGridWindow b K (w + 3)) := by
        refine mul_le_mul_of_nonneg_left
          (Finset.sum_le_sum fun w₁ hw₁ => ?_) (operatorFieldApplicationGdiag_nonneg (E := E) w)
        rw [Finset.mem_range] at hw₁
        refine mul_le_mul (hKD w₁ x) (Finset.sum_le_sum fun w₂ hw₂ => ?_)
          (Finset.sum_nonneg fun w₂ _ =>
            riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (6 + w₂) x _)
          (hKD_nn w₁)
        rw [Finset.mem_range] at hw₂
        refine le_trans (hbase w₂ (by omega)) ?_
        refine mul_le_mul_of_nonneg_left
          (Combinatorics.boundedFactorGridWindow_mono b hb_nn (le_refl _) (by omega))
          (mul_nonneg (operatorFieldApplicationGdiag_nonneg (E := E) w₂)
            (Finset.sum_nonneg fun w₃ _ =>
              mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hfr_nn 3))
                (Finset.sum_nonneg fun w₄ _ => mul_nonneg (hCA_nn w₄)
                  (Combinatorics.windowPairCellCount_nonneg _ _))))
    _ = (diagonalGridGrowthFactor (E := E) w *
          ∑ w₁ ∈ Finset.range (w + 1), KD w₁ *
            ∑ w₂ ∈ Finset.range (w + 1 - w₁),
              diagonalGridGrowthFactor (E := E) w₂ *
                ∑ w₃ ∈ Finset.range (w₂ + 1), (10 * fr ^ 3) *
                  ∑ w₄ ∈ Finset.range (w₂ + 1 - w₃),
                    CA w₄ * Combinatorics.windowPairCellCount (w₃ + 2) (w₄ + 2)) *
          Combinatorics.boundedFactorGridWindow b K (w + 3) := by
        have hstep : ∀ w₁ : ℕ, (KD w₁ *
            ∑ w₂ ∈ Finset.range (w + 1 - w₁),
              ((diagonalGridGrowthFactor (E := E) w₂ *
                ∑ w₃ ∈ Finset.range (w₂ + 1), (10 * fr ^ 3) *
                  ∑ w₄ ∈ Finset.range (w₂ + 1 - w₃),
                    CA w₄ * Combinatorics.windowPairCellCount (w₃ + 2) (w₄ + 2)) *
                Combinatorics.boundedFactorGridWindow b K (w + 3))) =
            (KD w₁ * ∑ w₂ ∈ Finset.range (w + 1 - w₁),
              diagonalGridGrowthFactor (E := E) w₂ *
                ∑ w₃ ∈ Finset.range (w₂ + 1), (10 * fr ^ 3) *
                  ∑ w₄ ∈ Finset.range (w₂ + 1 - w₃),
                    CA w₄ * Combinatorics.windowPairCellCount (w₃ + 2) (w₄ + 2)) *
              Combinatorics.boundedFactorGridWindow b K (w + 3) := by
          intro w₁
          rw [← Finset.sum_mul]
          ring
        rw [Finset.sum_congr rfl fun w₁ _ => hstep w₁, ← Finset.sum_mul]
        ring

end NormedKoszulConnectionDifferenceFoldGrid

end bgrConversion

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
