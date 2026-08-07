import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.CurvatureCoefficientDifferenceJetTowerCurvDiffGridWindow
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.MetricArmCoeffJetTower
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.RicciDeTurckSectionDifference
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.IteratedCovGradLinear
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.InverseMetricRaisedEndomorphismJetBound
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.CometricDoubleTraceField
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.RecoveryEndomorphismJetBound
import DifferentialGeometry.Tensor.Multilinear.Basis
import DifferentialGeometry.Tensor.Mixed.Field
import DifferentialGeometry.Analysis.Sobolev.RiemannianFiberNormSq.RiemannianFiberNormSqSmoothCcUniformBound
import DifferentialGeometry.Analysis.Sobolev.RiemannianFiberNormSq.FiberNormSubadditivity
import DifferentialGeometry.Analysis.Sobolev.GagliardoNirenbergLpFiberNorm
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.DeTurckRemainderHigherOrderTame
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.ConnectionDifferenceJetTower
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.RaisedKoszulCovariantJetTower
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.RaisedKoszulParallelRaiseJetBound
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.ConnectionDifferenceArmRfnsBound
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.RicciConnDiffPalatini
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.AppCcDropIteratedGrid
import DifferentialGeometry.Analysis.Sobolev.BoundedFactorProductGrid
import Mathlib.Analysis.MeanInequalities
import Mathlib.Data.Fin.Tuple.NatAntidiagonal
open DifferentialGeometry.Tensor.Multilinear
open DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Analysis.Elliptic
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection
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
open DifferentialGeometry.PDE.RicciFlow DifferentialGeometry.Analysis.Sobolev DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Analysis.Spectral.MetricRealization
  (metricCauchySchwarzBound ccTensorBilinSymm smoothCcTensorBilinForm ccTensorBilin_apply
  ccTensorModel ccTensorMultilinear ccTensorBilinSymm_contMDiff ccTensorBilinSymm_apply
  ccTensorBilinSymm_symm)
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Analysis.Sobolev.TensorHilbert
open DifferentialGeometry.Analysis.Spectral.DeTurck

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

section MixedSharpRicci

open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Analysis.Sobolev.TensorHilbert

set_option backward.isDefEq.respectTransparency false in
def ricMixedSharpEndoFib (g₀ g₁ : SmoothRiemannianMetric I M) (x : M) :
    TangentSpace I x →L[ℝ] TangentSpace I x :=
  LinearMap.toContinuousLinearMap
    { toFun := fun v => metricSharp (I := I) g₀ x (ricciTensor (I := I) g₁ x v).toLinearMap
      map_add' := fun v v' => by
        have h : (ricciTensor (I := I) g₁ x (v + v')).toLinearMap =
            (ricciTensor (I := I) g₁ x v).toLinearMap +
              (ricciTensor (I := I) g₁ x v').toLinearMap := by
          ext w
          simp [map_add]
        rw [show metricSharp (I := I) g₀ x (ricciTensor (I := I) g₁ x (v + v')).toLinearMap =
            (metricFlatMap (I := I) g₀ x).symm
              (ricciTensor (I := I) g₁ x (v + v')).toLinearMap from rfl,
          h, map_add]
        rfl
      map_smul' := fun c v => by
        have h : (ricciTensor (I := I) g₁ x (c • v)).toLinearMap =
            c • (ricciTensor (I := I) g₁ x v).toLinearMap := by
          ext w
          simp [map_smul]
        rw [show metricSharp (I := I) g₀ x (ricciTensor (I := I) g₁ x (c • v)).toLinearMap =
            (metricFlatMap (I := I) g₀ x).symm
              (ricciTensor (I := I) g₁ x (c • v)).toLinearMap from rfl,
          h, map_smul]
        rfl }

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
@[simp] lemma ricMixedSharpEndoFib_apply (g₀ g₁ : SmoothRiemannianMetric I M) (x : M)
    (v : TangentSpace I x) :
    ricMixedSharpEndoFib (I := I) (M := M) g₀ g₁ x v =
      metricSharp (I := I) g₀ x (ricciTensor (I := I) g₁ x v).toLinearMap := by
  rw [ricMixedSharpEndoFib, LinearMap.coe_toContinuousLinearMap']
  rfl

set_option backward.isDefEq.respectTransparency false in
omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem ricMixedSharpEndoFib_contMDiff [SigmaCompactSpace M] (g₀ g₁ : SmoothRiemannianMetric I M) :
    ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E)) ∞
      (fun x : M => TotalSpace.mk' (E →L[ℝ] E)
        (E := fun y : M => TangentSpace I y →L[ℝ] TangentSpace I y) x
        (ricMixedSharpEndoFib (I := I) (M := M) g₀ g₁ x)) := by
  apply cotangentCov_clmSection_smooth_aux (I := I) (M := M)
    (F₂ := E) (V₂ := fun y : M => TangentSpace I y)
    (φ := fun x : M => ricMixedSharpEndoFib (I := I) (M := M) g₀ g₁ x)
  intro Y
  have hcv : ∀ (α : M) (j : Fin (Module.finrank ℝ E)),
      ContMDiffOn I 𝓘(ℝ) ∞
        (fun b : M => (ricciTensor (I := I) g₁ b (Y b)).toLinearMap
          (chartBasisVecFiber (I := I) α j b))
        (chartAt H α).source := by
    intro α j
    have hRic : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
        (fun b : M => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
          (E := fun y => TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ) b
          (ricciTensor (I := I) g₁ b)) :=
      ricciTensor_contMDiff (I := I) g₁
    have hBasis : ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞
        (chartBasisVec (I := I) α j)
        (trivializationAt E (TangentSpace I) α).baseSet :=
      chartBasisVec_contMDiffOn (I := I) α j
    have happ : ContMDiffOn I (I.prod 𝓘(ℝ, ℝ)) ∞
        (fun b : M => (⟨b,
            ricciTensor (I := I) g₁ b (Y b) (chartBasisVecFiber (I := I) α j b)⟩ :
            TotalSpace ℝ (Bundle.Trivial M ℝ)))
        (trivializationAt E (TangentSpace I) α).baseSet :=
      ContMDiffOn.clm_bundle_apply₂ (F₁ := E) (F₂ := E) (F₃ := ℝ)
        (b := id) hRic.contMDiffOn Y.contMDiff.contMDiffOn hBasis
    have hbase_eq :
        (trivializationAt E (TangentSpace I) α).baseSet = (chartAt H α).source :=
      trivializationAt_baseSet_eq_chartAt_source (I := I) α
    rw [hbase_eq] at happ
    intro b hb
    have hpb := happ b hb
    rw [Bundle.contMDiffWithinAt_totalSpace] at hpb
    exact hpb.2
  have hsmooth := metricSharp_contMDiff_total (I := I) g₀
    (cv := fun b : M => (ricciTensor (I := I) g₁ b (Y b)).toLinearMap) hcv
  refine hsmooth.congr ?_
  intro x
  change TotalSpace.mk' E x
      (metricSharp (I := I) g₀ x (ricciTensor (I := I) g₁ x (Y x)).toLinearMap) =
    TotalSpace.mk' E x (ricMixedSharpEndoFib (I := I) (M := M) g₀ g₁ x (Y x))
  rw [ricMixedSharpEndoFib_apply]

set_option backward.isDefEq.respectTransparency false in
def ricMixedSharpEndoField [SigmaCompactSpace M] (g₀ g₁ : SmoothRiemannianMetric I M) :
    ContMDiffSection I (E →L[ℝ] E) ∞
      (fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x) where
  toFun := fun x : M => ricMixedSharpEndoFib (I := I) (M := M) g₀ g₁ x
  contMDiff_toFun := ricMixedSharpEndoFib_contMDiff (I := I) (M := M) g₀ g₁

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
lemma ricMixedSharpEndoField_apply [SigmaCompactSpace M] (g₀ g₁ : SmoothRiemannianMetric I M) (x : M) :
    ricMixedSharpEndoField (I := I) (M := M) g₀ g₁ x =
      ricMixedSharpEndoFib (I := I) (M := M) g₀ g₁ x := rfl

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma ricEndoRaisedFib_eq_mixed_add_gInvDiffRaised
    (g₀ g₁ : SmoothRiemannianMetric I M) (x : M) (v : TangentSpace I x) :
    ricEndoRaisedFib (I := I) g₁ x v =
      ricMixedSharpEndoFib (I := I) (M := M) g₀ g₁ x v +
        metricComparisonDiffEndo (I := I) g₀ g₁ x
          (ricMixedSharpEndoFib (I := I) (M := M) g₀ g₁ x v) := by
  rw [gInvDiffRaisedEndo_apply]
  have hcollapse : ricMixedSharpEndoFib (I := I) (M := M) g₀ g₁ x v +
      (inverseMetricSharpFib (I := I) g₁ x
          (g0FlatCLM (I := I) g₀ x (ricMixedSharpEndoFib (I := I) (M := M) g₀ g₁ x v)) -
        ricMixedSharpEndoFib (I := I) (M := M) g₀ g₁ x v) =
      inverseMetricSharpFib (I := I) g₁ x
        (g0FlatCLM (I := I) g₀ x (ricMixedSharpEndoFib (I := I) (M := M) g₀ g₁ x v)) := by
    abel
  rw [hcollapse]
  rw [inverseMetricSharpFib_g0FlatCLM_eq_metricSharp (I := I) g₀ g₁ x
    (ricMixedSharpEndoFib (I := I) (M := M) g₀ g₁ x v)]
  have hβ : (g₀.inner x (ricMixedSharpEndoFib (I := I) (M := M) g₀ g₁ x v)).toLinearMap =
      (ricciTensor (I := I) g₁ x v).toLinearMap := by
    ext w
    rw [show ((g₀.inner x (ricMixedSharpEndoFib (I := I) (M := M) g₀ g₁ x v)).toLinearMap) w =
        g₀.inner x (ricMixedSharpEndoFib (I := I) (M := M) g₀ g₁ x v) w from rfl]
    rw [ricMixedSharpEndoFib_apply]
    exact inner_metricSharp (I := I) g₀ x (ricciTensor (I := I) g₁ x v).toLinearMap w
  rw [hβ, ricEndoRaisedFib_apply]

set_option backward.isDefEq.respectTransparency false in
omit [NeZero (Module.finrank ℝ E)] in
theorem slotInsertEndoCc_zero_ricEndoBackgroundDifference_telescope
    (g₀ g₁ : SmoothRiemannianMetric I M) :
    endoSlotZeroCcTensor (I := I) (M := M) g₀ 0
        (ricEndoBackgroundDifferenceField (I := I) (M := M) g₀ g₁) =
      (endoSlotZeroCcTensor (I := I) (M := M) g₀ 0
          (ricMixedSharpEndoField (I := I) (M := M) g₀ g₁) -
        endoSlotZeroCcTensor (I := I) (M := M) g₀ 0
          (ricciEndomorphismField (I := I) (M := M) g₀)) +
      ccOperatorFieldComp (I := I) (M := M) g₀ 1 1 1
        (endoSlotZeroCcTensor (I := I) (M := M) g₀ 0
          (ricMixedSharpEndoField (I := I) (M := M) g₀ g₁))
        (endoSlotZeroCcTensor (I := I) (M := M) g₀ 0
          (gInvDiffRaisedEndoField (I := I) g₀ g₁)) := by
  classical
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rw [show ((((endoSlotZeroCcTensor (I := I) (M := M) g₀ 0
          (ricMixedSharpEndoField (I := I) (M := M) g₀ g₁) -
        endoSlotZeroCcTensor (I := I) (M := M) g₀ 0
          (ricciEndomorphismField (I := I) (M := M) g₀)) +
      ccOperatorFieldComp (I := I) (M := M) g₀ 1 1 1
        (endoSlotZeroCcTensor (I := I) (M := M) g₀ 0
          (ricMixedSharpEndoField (I := I) (M := M) g₀ g₁))
        (endoSlotZeroCcTensor (I := I) (M := M) g₀ 0
          (gInvDiffRaisedEndoField (I := I) g₀ g₁))).toSection) x) =
      ((endoSlotZeroCcTensor (I := I) (M := M) g₀ 0
          (ricMixedSharpEndoField (I := I) (M := M) g₀ g₁)).toSection x -
        (endoSlotZeroCcTensor (I := I) (M := M) g₀ 0
          (ricciEndomorphismField (I := I) (M := M) g₀)).toSection x) +
      (ccOperatorFieldComp (I := I) (M := M) g₀ 1 1 1
        (endoSlotZeroCcTensor (I := I) (M := M) g₀ 0
          (ricMixedSharpEndoField (I := I) (M := M) g₀ g₁))
        (endoSlotZeroCcTensor (I := I) (M := M) g₀ 0
          (gInvDiffRaisedEndoField (I := I) g₀ g₁))).toSection x from by
    rw [SmoothCcTensor.toSection_add, SmoothCcTensor.toSection_sub]
    rfl]
  apply ContinuousLinearMap.ext
  intro A
  rw [ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply]
  apply Tensor0SSpace.toModel_injective
  apply ContinuousMultilinearMap.ext
  intro m
  simp only [Tensor0SSpace.toModel_add, Tensor0SSpace.toModel_sub,
    ContinuousMultilinearMap.add_apply, ContinuousMultilinearMap.sub_apply]
  rw [show ((endoSlotZeroCcTensor (I := I) (M := M) g₀ 0
        (ricEndoBackgroundDifferenceField (I := I) (M := M) g₀ g₁)).toSection x) A =
      slotInsertEndoFib (I := I) (M := M) 1 0 x
        (ricEndoBackgroundDifferenceField (I := I) (M := M) g₀ g₁ x) A from rfl]
  rw [show ((endoSlotZeroCcTensor (I := I) (M := M) g₀ 0
        (ricMixedSharpEndoField (I := I) (M := M) g₀ g₁)).toSection x) A =
      slotInsertEndoFib (I := I) (M := M) 1 0 x
        (ricMixedSharpEndoFib (I := I) (M := M) g₀ g₁ x) A from rfl]
  rw [show ((endoSlotZeroCcTensor (I := I) (M := M) g₀ 0
        (ricciEndomorphismField (I := I) (M := M) g₀)).toSection x) A =
      slotInsertEndoFib (I := I) (M := M) 1 0 x
        (ricEndoRaisedFib (I := I) g₀ x) A from rfl]
  rw [show ((ccOperatorFieldComp (I := I) (M := M) g₀ 1 1 1
        (endoSlotZeroCcTensor (I := I) (M := M) g₀ 0
          (ricMixedSharpEndoField (I := I) (M := M) g₀ g₁))
        (endoSlotZeroCcTensor (I := I) (M := M) g₀ 0
          (gInvDiffRaisedEndoField (I := I) g₀ g₁))).toSection x) A =
      slotInsertEndoFib (I := I) (M := M) 1 0 x
        (ricMixedSharpEndoFib (I := I) (M := M) g₀ g₁ x)
        (slotInsertEndoFib (I := I) (M := M) 1 0 x
          (metricComparisonDiffEndo (I := I) g₀ g₁ x) A) from rfl]
  rw [slotInsertEndoFib_apply_eval, slotInsertEndoFib_apply_eval,
    slotInsertEndoFib_apply_eval, slotInsertEndoFib_apply_eval,
    slotInsertEndoFib_apply_eval]
  rw [Function.update_self, Function.update_idem]
  rw [ricEndoBackgroundDifferenceField_apply (I := I) (M := M) g₀ g₁ x]
  rw [ContinuousLinearMap.sub_apply, ContinuousMultilinearMap.map_update_sub]
  rw [ricEndoRaisedFib_eq_mixed_add_gInvDiffRaised (I := I) (M := M) g₀ g₁ x (m 0)]
  rw [ContinuousMultilinearMap.map_update_add]
  ring

end MixedSharpRicci

section RiemannLoweredDifference

section NormedRiemannLowering

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Analysis.Spectral.DeTurck

set_option backward.isDefEq.respectTransparency false

def riemannLoweredCovec (gm gc : SmoothRiemannianMetric I M) (x : M) :
    Tensor0SSpace 4 I x :=
  (show ContinuousMultilinearMap ℝ (fun _ : Fin 4 => TangentSpace I x) ℝ from
    { toFun := fun m =>
        gm.inner x (riemannOp (LeviCivita (I := I) gc) x (m 0) (m 2) (m 3)) (m 1)
      map_update_add' := by
        have h01 : (0 : Fin 4) ≠ 1 := by decide
        have h02 : (0 : Fin 4) ≠ 2 := by decide
        have h03 : (0 : Fin 4) ≠ 3 := by decide
        have h10 : (1 : Fin 4) ≠ 0 := by decide
        have h12 : (1 : Fin 4) ≠ 2 := by decide
        have h13 : (1 : Fin 4) ≠ 3 := by decide
        have h20 : (2 : Fin 4) ≠ 0 := by decide
        have h21 : (2 : Fin 4) ≠ 1 := by decide
        have h23 : (2 : Fin 4) ≠ 3 := by decide
        have h30 : (3 : Fin 4) ≠ 0 := by decide
        have h31 : (3 : Fin 4) ≠ 1 := by decide
        have h32 : (3 : Fin 4) ≠ 2 := by decide
        intro _ m i a a'
        fin_cases i <;>
          simp only [Fin.reduceFinMk, Fin.isValue, Function.update_self, ne_eq,
            Function.update_of_ne, h01, h02, h03, h10, h12, h13, h20, h21, h23, h30, h31, h32,
            not_false_eq_true]
        · rw [(riemannOp (LeviCivita (I := I) gc) x).map_add]
          simp only [ContinuousLinearMap.add_apply, (gm.inner x).map_add]
        · exact ((gm.inner x) _).map_add _ _
        · rw [((riemannOp (LeviCivita (I := I) gc) x) _).map_add]
          simp only [ContinuousLinearMap.add_apply, (gm.inner x).map_add]
        · rw [((riemannOp (LeviCivita (I := I) gc) x) _ _).map_add]
          simp only [(gm.inner x).map_add, ContinuousLinearMap.add_apply]
      map_update_smul' := by
        have h01 : (0 : Fin 4) ≠ 1 := by decide
        have h02 : (0 : Fin 4) ≠ 2 := by decide
        have h03 : (0 : Fin 4) ≠ 3 := by decide
        have h10 : (1 : Fin 4) ≠ 0 := by decide
        have h12 : (1 : Fin 4) ≠ 2 := by decide
        have h13 : (1 : Fin 4) ≠ 3 := by decide
        have h20 : (2 : Fin 4) ≠ 0 := by decide
        have h21 : (2 : Fin 4) ≠ 1 := by decide
        have h23 : (2 : Fin 4) ≠ 3 := by decide
        have h30 : (3 : Fin 4) ≠ 0 := by decide
        have h31 : (3 : Fin 4) ≠ 1 := by decide
        have h32 : (3 : Fin 4) ≠ 2 := by decide
        intro _ m i c a
        fin_cases i <;>
          simp only [Fin.reduceFinMk, Fin.isValue, Function.update_self, ne_eq,
            Function.update_of_ne, h01, h02, h03, h10, h12, h13, h20, h21, h23, h30, h31, h32,
            not_false_eq_true]
        · rw [(riemannOp (LeviCivita (I := I) gc) x).map_smul]
          simp only [ContinuousLinearMap.smul_apply, (gm.inner x).map_smul]
        · exact ((gm.inner x) _).map_smul c a
        · rw [((riemannOp (LeviCivita (I := I) gc) x) _).map_smul]
          simp only [ContinuousLinearMap.smul_apply, (gm.inner x).map_smul]
        · rw [((riemannOp (LeviCivita (I := I) gc) x) _ _).map_smul]
          simp only [(gm.inner x).map_smul, ContinuousLinearMap.smul_apply]
      cont := by
        have hR : Continuous (fun m : Fin 4 → TangentSpace I x =>
            riemannOp (LeviCivita (I := I) gc) x (m 0) (m 2) (m 3)) :=
          (((riemannOp (LeviCivita (I := I) gc) x).continuous.comp
            (continuous_apply 0)).clm_apply (continuous_apply 2)).clm_apply (continuous_apply 3)
        exact ((gm.inner x).continuous.comp hR).clm_apply (continuous_apply 1) }
    : Tensor0SSpace 4 I x)

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
@[simp] lemma riemannLoweredCovec_apply (gm gc : SmoothRiemannianMetric I M) (x : M)
    (m : Fin 4 → TangentSpace I x) :
    riemannLoweredCovec (I := I) gm gc x m =
      gm.inner x (riemannOp (LeviCivita (I := I) gc) x (m 0) (m 2) (m 3)) (m 1) := rfl

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma riemannLoweredScalar_global (gm gc : SmoothRiemannianMetric I M)
    {Y W p q : Π b : M, TangentSpace I b}
    (hY : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Y))
    (hW : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% W))
    (hp : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% p))
    (hq : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% q)) :
    ContMDiff I 𝓘(ℝ, ℝ) ∞
      (fun x : M => gm.inner x
        (riemannOp (LeviCivita (I := I) gc) x (Y x) (p x) (q x)) (W x)) := by
  classical
  have hRsec : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (T% (fun b : M => riemannSec (LeviCivita (I := I) gc) Y p q b)) :=
    riemannSec_contMDiff (cov := LeviCivita (I := I) gc) hY hp hq
  have hcongr : (fun x : M => gm.inner x
        (riemannOp (LeviCivita (I := I) gc) x (Y x) (p x) (q x)) (W x)) =
      (fun x : M => gm.inner x (riemannSec (LeviCivita (I := I) gc) Y p q x) (W x)) := by
    funext x
    rw [riemannOp_apply_smooth (cov := LeviCivita (I := I) gc) hY hp hq]
  rw [hcongr]
  exact contMDiff_g_inner_of_smooth_sections (I := I) gm
    ⟨fun b => riemannSec (LeviCivita (I := I) gc) Y p q b, hRsec⟩ ⟨fun b => W b, hW⟩

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma riemannLoweredScalar_contMDiffAt (gm gc : SmoothRiemannianMetric I M)
    (V0 V1 V2 V3 : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x₀ : M) :
    ContMDiffAt I 𝓘(ℝ, ℝ) ∞
      (fun x : M =>
        gm.inner x (riemannOp (LeviCivita (I := I) gc) x (V0 x) (V2 x) (V3 x)) (V1 x)) x₀ := by
  have hglob := riemannLoweredScalar_global (I := I) (M := M) gm gc
    (Y := fun b => V0 b) (W := fun b => V1 b) (p := fun b => V2 b) (q := fun b => V3 b)
    V0.contMDiff V1.contMDiff V2.contMDiff V3.contMDiff
  exact hglob.contMDiffAt

set_option backward.isDefEq.respectTransparency false in
omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
theorem riemannLoweredCovec_section_contMDiff (gm gc : SmoothRiemannianMetric I M) :
    ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel 4 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SModel 4 ℝ E)
        (E := fun z : M => Tensor0SSpace 4 I z) x (riemannLoweredCovec (I := I) gm gc x)) := by
  classical
  letI := Tensor0SBundle.tensor0SBundle_topology (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) 4
  refine (contMDiff_multilinearSection_iff_coord (𝕜 := ℝ) (F := E)
      (E := (TangentSpace I : M → Type _)) (IB := I) (n := (∞ : WithTop ℕ∞)) (Module.finBasis ℝ E)
      (fun x : M => (riemannLoweredCovec (I := I) gm gc x :
        Bundle.continuousMultilinearMap ℝ 4 E (TangentSpace I) x))).mpr ?_
  intro σ x₀
  set b := Module.finBasis ℝ E with hb
  set e₁ := trivializationAt E (TangentSpace I : M → Type _) x₀ with he₁def
  have he₁ : x₀ ∈ e₁.baseSet := mem_baseSet_trivializationAt E (TangentSpace I) x₀
  have hframe := e₁.isLocalFrameOn_localFrame_baseSet I (⊤ : ℕ∞) b
  obtain ⟨Y, hY⟩ := hframe.exists_contMDiffSection_eqOn_nhd e₁.open_baseSet he₁
  have hscalar : ContMDiffAt I 𝓘(ℝ, ℝ) ∞
      (fun x : M => gm.inner x
        (riemannOp (LeviCivita (I := I) gc) x (Y (σ 0) x) (Y (σ 2) x) (Y (σ 3) x))
        (Y (σ 1) x)) x₀ :=
    riemannLoweredScalar_contMDiffAt (I := I) gm gc (Y (σ 0)) (Y (σ 1)) (Y (σ 2)) (Y (σ 3)) x₀
  refine hscalar.congr_of_eventuallyEq ?_
  have h_base₁ : ∀ᶠ x in 𝓝 x₀, x ∈ e₁.baseSet := e₁.open_baseSet.mem_nhds he₁
  filter_upwards [h_base₁, hY] with x hx₁ hYx
  rw [continuousMultilinearMap_basis_repr]
  have hframeEq : ∀ k : Fin 4, e₁.symmL ℝ x (b (σ k)) = (Y (σ k)) x := by
    intro k
    rw [hYx (σ k), Trivialization.localFrame_apply_of_mem_baseSet (hx := hx₁)]
    simp [Trivialization.basisAt]
  change gm.inner x (riemannOp (LeviCivita (I := I) gc) x
      (e₁.symmL ℝ x (b (σ 0))) (e₁.symmL ℝ x (b (σ 2))) (e₁.symmL ℝ x (b (σ 3))))
      (e₁.symmL ℝ x (b (σ 1))) = _
  rw [hframeEq 0, hframeEq 1, hframeEq 2, hframeEq 3]

def riemannLoweredField (gm gc : SmoothRiemannianMetric I M) :
    Tensor0SBundle.Tensor0SField (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) ∞ 4 :=
  letI := Tensor0SBundle.tensor0SBundle_topology (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) 4
  ⟨fun x => riemannLoweredCovec (I := I) gm gc x,
    riemannLoweredCovec_section_contMDiff (I := I) gm gc⟩

def riemannLoweredCc (g₀ gm gc : SmoothRiemannianMetric I M) : SmoothCcTensor g₀ 0 4 where
  toSection :=
    MixedSection.fromMultilinearSection (𝕜 := ℝ) (F := E) (IB := I)
      (E := (TangentSpace I : M → Type _)) ∞ (riemannLoweredField (I := I) gm gc)
  hasCompactSupport := HasCompactSupport.of_compactSpace _

set_option backward.isDefEq.respectTransparency false in
omit [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
lemma riemannLoweredCc_unitModel (g₀ gm gc : SmoothRiemannianMetric I M) (x : M) :
    unitModel (I := I) (M := M) g₀ 4 (riemannLoweredCc (I := I) (M := M) g₀ gm gc) x =
      Tensor0SSpace.toModel (riemannLoweredCovec (I := I) gm gc x) := by
  rw [unitModel]
  rw [show (riemannLoweredCc (I := I) (M := M) g₀ gm gc).toSection x
        (unitTensor (I := I) (M := M) x) =
      (MixedSection.eval₀ (F := E) (E := (TangentSpace I : M → Type _)) x).smulRight
          (riemannLoweredField (I := I) gm gc x)
          (ContinuousMultilinearMap.constOfIsEmpty ℝ (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ))
      from rfl]
  rw [ContinuousLinearMap.smulRight_apply, MixedSection.eval₀_apply,
    ContinuousMultilinearMap.constOfIsEmpty_apply, one_smul]
  rfl

omit [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
lemma riemannLoweredCc_unitModel_apply (g₀ gm gc : SmoothRiemannianMetric I M) (x : M)
    (m : Fin 4 → TangentSpace I x) :
    unitModel (I := I) (M := M) g₀ 4 (riemannLoweredCc (I := I) (M := M) g₀ gm gc) x m =
      gm.inner x (riemannOp (LeviCivita (I := I) gc) x (m 0) (m 2) (m 3)) (m 1) := by
  rw [riemannLoweredCc_unitModel]
  rfl

def riemannLoweredBackgroundDifference (g₀ g₁ : SmoothRiemannianMetric I M) :
    SmoothCcTensor g₀ 0 4 :=
  riemannLoweredCc (I := I) (M := M) g₀ g₀ g₁ - riemannLoweredCc (I := I) (M := M) g₀ g₀ g₀

set_option backward.isDefEq.respectTransparency false in
omit [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
lemma riemannLoweredBackgroundDifference_unitModel_apply
    (g₀ g₁ : SmoothRiemannianMetric I M) (x : M) (m : Fin 4 → TangentSpace I x) :
    unitModel (I := I) (M := M) g₀ 4
        (riemannLoweredBackgroundDifference (I := I) (M := M) g₀ g₁) x m =
      g₀.inner x (riemannOp (LeviCivita (I := I) g₁) x (m 0) (m 2) (m 3)) (m 1) -
        g₀.inner x (riemannOp (LeviCivita (I := I) g₀) x (m 0) (m 2) (m 3)) (m 1) := by
  have hsub : unitModel (I := I) (M := M) g₀ 4
      (riemannLoweredBackgroundDifference (I := I) (M := M) g₀ g₁) x m =
      unitModel (I := I) (M := M) g₀ 4
          (riemannLoweredCc (I := I) (M := M) g₀ g₀ g₁) x m -
        unitModel (I := I) (M := M) g₀ 4
          (riemannLoweredCc (I := I) (M := M) g₀ g₀ g₀) x m := by
    simp only [riemannLoweredBackgroundDifference, unitModel]
    rw [show ((riemannLoweredCc (I := I) (M := M) g₀ g₀ g₁ -
          riemannLoweredCc (I := I) (M := M) g₀ g₀ g₀).toSection x) =
        (riemannLoweredCc (I := I) (M := M) g₀ g₀ g₁).toSection x -
          (riemannLoweredCc (I := I) (M := M) g₀ g₀ g₀).toSection x from by
      rw [SmoothCcTensor.toSection_sub]; rfl]
    rw [ContinuousLinearMap.sub_apply, Tensor0SSpace.toModel_sub,
      ContinuousMultilinearMap.sub_apply]
  rw [hsub, riemannLoweredCc_unitModel_apply, riemannLoweredCc_unitModel_apply]

end NormedRiemannLowering

section NormedSharpFlatSplitting

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

private local instance tensor0SModelNormedSpaceCC {s : ℕ} :
    NormedSpace ℝ (Tensor0SModel s ℝ E) :=
  Tensor0SBundle.tensor0SModel_normedSpace s

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
    [T2Space M] in
lemma interiorProduct_toModel_eval_pal (s : ℕ) (x : M) (vv : TangentSpace I x)
    (D : Tensor0SSpace (s + 1) I x) (w : Fin s → TangentSpace I x) :
    Tensor0SSpace.toModel
        (Tensor0SBundle.interior_product (𝕜 := ℝ) (I := I) s x vv D) w =
      Tensor0SSpace.toModel D (Fin.cons (show E from vv) (fun k => (show E from w k))) := by
  have h1 : Tensor0SSpace.toModel
      (Tensor0SBundle.interior_product (𝕜 := ℝ) (I := I) s x vv D) =
      Tensor0SBundle.model_interior_product (𝕜 := ℝ) (E := E) s (show E from vv)
        (Tensor0SSpace.toModel D) := rfl
  rw [h1]
  rfl

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless]
    [BoundarylessManifold I M] [T2Space M] in
lemma toModel_om_single_eq_cotangentToDual (x : M) (om : Tensor0SSpace 1 I x)
    (m : Fin 1 → TangentSpace I x) :
    Tensor0SSpace.toModel om (fun k => (m k : E)) =
      cotangentToDual (I := I) (x := x) om (m 0) := by
  rw [show (fun k : Fin 1 => (m k : E)) = (fun _ : Fin 1 => (m 0 : E)) from by
    funext k; fin_cases k; rfl]
  rw [cotangentToDual_apply]
  rfl

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
    [T2Space M] in
private lemma g1_inner_gInvRaisedEndo_left (g₀ g₁ : SmoothRiemannianMetric I M) (x : M)
    (v w : TangentSpace I x) :
    g₁.inner x (metricComparisonEndo (I := I) g₀ g₁ x v) w = g₀.inner x v w := by
  rw [gInvRaisedEndo_apply]
  rw [inverseMetricSharpFib_inner (I := I) g₁ x (g0FlatCLM (I := I) g₀ x v) w]
  rw [show cotangentToDualLinear (I := I) (x := x) (g0FlatCLM (I := I) g₀ x v) w =
      cotangentToDual (I := I) (x := x) (g0FlatCLM (I := I) g₀ x v) w from rfl]
  rw [cotangentToDual_g0FlatCLM]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
    [T2Space M] in
lemma g0_inner_inverseMetricSharp_mixed (g₀ g₁ : SmoothRiemannianMetric I M) (x : M)
    (om : Tensor0SSpace 1 I x) (v : TangentSpace I x) :
    g₀.inner x (inverseMetricSharpFib (I := I) g₁ x om) v =
      cotangentToDual (I := I) (x := x) om (metricComparisonEndo (I := I) g₀ g₁ x v) := by
  rw [show cotangentToDual (I := I) (x := x) om (metricComparisonEndo (I := I) g₀ g₁ x v) =
      cotangentToDualLinear (I := I) (x := x) om (metricComparisonEndo (I := I) g₀ g₁ x v) from rfl]
  rw [← inverseMetricSharpFib_inner (I := I) g₁ x om (metricComparisonEndo (I := I) g₀ g₁ x v)]
  rw [g₁.symm x (inverseMetricSharpFib (I := I) g₁ x om) (metricComparisonEndo (I := I) g₀ g₁ x v)]
  rw [g1_inner_gInvRaisedEndo_left (I := I) (M := M) g₀ g₁ x v
    (inverseMetricSharpFib (I := I) g₁ x om)]
  rw [g₀.symm x v (inverseMetricSharpFib (I := I) g₁ x om)]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
    [T2Space M] in
lemma cotangentToDual_eq_inner_sharp (g₀ : SmoothRiemannianMetric I M) (x : M)
    (om : Tensor0SSpace 1 I x) (ww : TangentSpace I x) :
    cotangentToDual (I := I) (x := x) om ww =
      g₀.inner x ww (inverseMetricSharpFib (I := I) g₀ x om) := by
  rw [g₀.symm x ww (inverseMetricSharpFib (I := I) g₀ x om)]
  rw [g0_inner_inverseMetricSharp_mixed (I := I) (M := M) g₀ g₀ x om ww]
  rw [show metricComparisonEndo (I := I) g₀ g₀ x ww = ww from by
    rw [gInvRaisedEndo_apply, inverseMetricSharpFib_g0FlatCLM]]

set_option backward.isDefEq.respectTransparency false in
omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
lemma sharpFlatEndoCc_eq_slotInsert_fullRaised (g₀ g₁ : SmoothRiemannianMetric I M) :
    sharpFlatEndoCc (I := I) g₀ g₁ =
      endoSlotZeroCcTensor (I := I) (M := M) g₀ 0
        (fullRaisedEndoField (I := I) (M := M) g₀ g₁) := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  apply ContinuousLinearMap.ext
  intro om
  apply Tensor0SSpace.toModel_injective
  apply ContinuousMultilinearMap.ext
  intro m
  rw [show ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 1 I x from
        (sharpFlatEndoCc (I := I) g₀ g₁).toSection x) om) =
      (g0FlatCLM (I := I) g₀ x) (inverseMetricSharpFib (I := I) g₁ x om) from rfl]
  rw [show ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 1 I x from
        (endoSlotZeroCcTensor (I := I) (M := M) g₀ 0
          (fullRaisedEndoField (I := I) (M := M) g₀ g₁)).toSection x) om) =
      slotInsertEndoFib (I := I) (M := M) 1 0 x
        (fullRaisedEndoField (I := I) (M := M) g₀ g₁ x) om from rfl]
  rw [slotInsertEndoFib_apply_eval]
  rw [toModel_om_single_eq_cotangentToDual (I := I) (M := M) x om
    (Function.update m 0 (fullRaisedEndoField (I := I) (M := M) g₀ g₁ x (m 0)))]
  rw [Function.update_self]
  rw [toModel_om_single_eq_cotangentToDual (I := I) (M := M) x
    ((g0FlatCLM (I := I) g₀ x) (inverseMetricSharpFib (I := I) g₁ x om)) m]
  rw [cotangentToDual_g0FlatCLM]
  rw [g0_inner_inverseMetricSharp_mixed (I := I) (M := M) g₀ g₁ x om (m 0)]
  rw [fullRaisedEndoField_apply]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [BoundarylessManifold I M]
    in
lemma fullRaisedEndoField_diff_split (g₀ g₁ : SmoothRiemannianMetric I M) :
    fullRaisedEndoField (I := I) (M := M) g₀ g₁ =
      gInvDiffRaisedEndoField (I := I) g₀ g₁ +
        fullRaisedEndoField (I := I) (M := M) g₀ g₀ := by
  apply ContMDiffSection.ext
  intro x
  rw [show ((gInvDiffRaisedEndoField (I := I) g₀ g₁ +
        fullRaisedEndoField (I := I) (M := M) g₀ g₀) x) =
      gInvDiffRaisedEndoField (I := I) g₀ g₁ x +
        fullRaisedEndoField (I := I) (M := M) g₀ g₀ x from by
    rw [ContMDiffSection.coe_add]; rfl]
  apply ContinuousLinearMap.ext
  intro v
  rw [fullRaisedEndoField_apply, ContinuousLinearMap.add_apply]
  rw [show (gInvDiffRaisedEndoField (I := I) g₀ g₁ x) = metricComparisonDiffEndo (I := I) g₀ g₁ x
    from rfl]
  rw [fullRaisedEndoField_apply]
  rw [gInvRaisedEndo_eq_diff_add_id (I := I) g₀ g₁ x v]
  rw [show metricComparisonEndo (I := I) g₀ g₀ x v = v from by
    rw [gInvRaisedEndo_apply, inverseMetricSharpFib_g0FlatCLM]]

set_option backward.isDefEq.respectTransparency false in
omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M]
    in
lemma slotInsertEndoCc_add_endo (g₀ : SmoothRiemannianMetric I M) (s : ℕ)
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
  rw [ContinuousLinearMap.add_apply]
  simp only [slotInsertEndoCc_toSection]
  rw [show ((A + B) x) = A x + B x from by rw [ContMDiffSection.coe_add]; rfl]
  rw [slotInsertEndoFib_add_left, ContinuousLinearMap.add_apply]

set_option backward.isDefEq.respectTransparency false in
omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [BoundarylessManifold I M]
    in
private lemma endoCovariantDerivative_fullRaised_id_eq_zero (g₀ : SmoothRiemannianMetric I M)
    (Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) (v : TangentSpace I x) :
    ((endoCovariantDerivative (I := I) (M := M) g₀)
        (fullRaisedEndoField (I := I) (M := M) g₀ g₀) x v) (Y x) = 0 := by
  have hLeib := endoCovariantDerivative_apply (I := I) (M := M) g₀
    (fullRaisedEndoField (I := I) (M := M) g₀ g₀) Y x v
  have hΛapp : (fun y : M => (fullRaisedEndoField (I := I) (M := M) g₀ g₀ y) (Y y)) =
      (fun y : M => Y y) := by
    funext y
    rw [fullRaisedEndoField_apply]
    rw [show metricComparisonEndo (I := I) g₀ g₀ y (Y y) = Y y from by
      rw [gInvRaisedEndo_apply, inverseMetricSharpFib_g0FlatCLM]]
  rw [hLeib, hΛapp]
  rw [fullRaisedEndoField_apply]
  rw [show metricComparisonEndo (I := I) g₀ g₀ x
      ((LeviCivita (I := I) g₀).toFun (fun y : M => Y y) x v) =
      (LeviCivita (I := I) g₀).toFun (fun y : M => Y y) x v from by
    rw [gInvRaisedEndo_apply, inverseMetricSharpFib_g0FlatCLM]]
  rw [sub_self]

set_option backward.isDefEq.respectTransparency false in
omit [NeZero (Module.finrank ℝ E)] in
private lemma covGrad_slotInsert_fullRaised_id_eq_zero (g₀ : SmoothRiemannianMetric I M) :
    covGrad (I := I) (M := M) g₀ 1 1
        (endoSlotZeroCcTensor (I := I) (M := M) g₀ 0
          (fullRaisedEndoField (I := I) (M := M) g₀ g₀)) = 0 := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  apply ContinuousLinearMap.ext
  intro D
  apply Tensor0SSpace.toModel_injective
  refine ContinuousMultilinearMap.ext (fun m => ?_)
  rw [covGrad_toSection_apply_eval (I := I) (M := M) g₀ 1 1
    (endoSlotZeroCcTensor (I := I) (M := M) g₀ 0
      (fullRaisedEndoField (I := I) (M := M) g₀ g₀)) x D m]
  rw [tensorCovDerivAt_slotInsertEndoCc_eq (I := I) (M := M) g₀ 0
    (fullRaisedEndoField (I := I) (M := M) g₀ g₀) x (m 0)]
  rw [show ((endoCovariantDerivative (I := I) (M := M) g₀)
        (fullRaisedEndoField (I := I) (M := M) g₀ g₀) x (m 0)) =
      (0 : TangentSpace I x →L[ℝ] TangentSpace I x) from by
    apply ContinuousLinearMap.ext
    intro w
    rw [ContinuousLinearMap.zero_apply]
    obtain ⟨Y, hY⟩ := ContMDiffSection.exists_eq_at (I := I)
      (F := E) (V := fun y : M => TangentSpace I y) (n := (⊤ : ℕ∞)) x w
    rw [← hY]
    exact endoCovariantDerivative_fullRaised_id_eq_zero (I := I) (M := M) g₀ Y x (m 0)]
  rw [show slotInsertEndoFib (I := I) (M := M) (0 + 1) 0 x
        (0 : TangentSpace I x →L[ℝ] TangentSpace I x) = 0 from by
    rw [show (0 : TangentSpace I x →L[ℝ] TangentSpace I x) =
        (0 : ℝ) • (0 : TangentSpace I x →L[ℝ] TangentSpace I x) from (zero_smul ℝ _).symm,
      slotInsertEndoFib_smul_left, zero_smul]]
  simp [SmoothCcTensor.toSection_zero]

omit [NeZero (Module.finrank ℝ E)] in
lemma iteratedCovGrad_slotInsert_fullRaised_id_succ_eq_zero
    (g₀ : SmoothRiemannianMetric I M) (m : ℕ) :
    iteratedCovGrad (I := I) g₀ 1 1 (m + 1)
        (endoSlotZeroCcTensor (I := I) (M := M) g₀ 0
          (fullRaisedEndoField (I := I) (M := M) g₀ g₀)) = 0 := by
  induction m with
  | zero =>
      rw [iteratedCovGrad_succ, iteratedCovGrad_zero]
      exact covGrad_slotInsert_fullRaised_id_eq_zero (I := I) (M := M) g₀
  | succ m' ih =>
      rw [iteratedCovGrad_succ, ih, covGrad_zero]

end NormedSharpFlatSplitting

section NormedRaisedKoszulPointwise

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
lemma iteratedCovGrad_smul_pt (g : SmoothRiemannianMetric I M) (r s j : ℕ)
    (c : ℝ) (w : SmoothCcTensor g r s) :
    iteratedCovGrad (I := I) g r s j (c • w) = c • iteratedCovGrad (I := I) g r s j w := by
  induction j with
  | zero => simp only [iteratedCovGrad_zero]
  | succ j ih =>
    rw [iteratedCovGrad_succ, iteratedCovGrad_succ, ih, covGrad_smul]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
    [T2Space M] in
lemma rfns_smul_pt (g : SmoothRiemannianMetric I M) (r s : ℕ) (x : M)
    (c : ℝ) (v : TensorRSSpace r s I x) :
    riemannianFiberNormSq (I := I) (M := M) g r s x (c • v) =
      c ^ 2 * riemannianFiberNormSq (I := I) (M := M) g r s x v := by
  rw [riemannianFiberNormSq_eq_tensorInnerPointwise (I := I) (M := M) g r s x (c • v),
    riemannianFiberNormSq_eq_tensorInnerPointwise (I := I) (M := M) g r s x v]
  rw [TensorRSSpace.toModel_smul, tensorInnerPointwise_smul_left,
    tensorInnerPointwise_smul_right]
  ring

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
    [T2Space M] in
lemma rfns_neg_pt (g : SmoothRiemannianMetric I M) (r s : ℕ) (x : M)
    (v : TensorRSSpace r s I x) :
    riemannianFiberNormSq (I := I) (M := M) g r s x (-v) =
      riemannianFiberNormSq (I := I) (M := M) g r s x v := by
  have h := rfns_smul_pt (I := I) (M := M) g r s x (-1 : ℝ) v
  rw [neg_one_smul] at h
  rw [h]; norm_num

omit [NeZero (Module.finrank ℝ E)] in
lemma rfns_iteratedCovGrad_symmS_pointwise (g₀ : SmoothRiemannianMetric I M)
    (T : SmoothCcTensor g₀ 0 2) (k : ℕ) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + k) x
        ((iteratedCovGrad (I := I) g₀ 0 2 k (ccTensor02Symm (I := I) (M := M) g₀ T)).toSection x) ≤
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + k) x
        ((iteratedCovGrad (I := I) g₀ 0 2 k T).toSection x) := by
  have hswap : riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + k) x
      ((iteratedCovGrad (I := I) g₀ 0 2 k
        (domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 2) 1) T)).toSection x) =
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + k) x
        ((iteratedCovGrad (I := I) g₀ 0 2 k T).toSection x) :=
    riemannianFiberNormSq_iteratedCovGrad_domDomCongrSection (I := I) (M := M) g₀
      (Equiv.swap (0 : Fin 2) 1) T k x
  set A := iteratedCovGrad (I := I) g₀ 0 2 k T with hA
  set B := iteratedCovGrad (I := I) g₀ 0 2 k
    (domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 2) 1) T) with hB
  have htoSec : ((iteratedCovGrad (I := I) g₀ 0 2 k
        (ccTensor02Symm (I := I) (M := M) g₀ T)).toSection x : TensorRSSpace 0 (2 + k) I x) =
      (1 / 2 : ℝ) • (A.toSection x) + (1 / 2 : ℝ) • (B.toSection x) := by
    rw [iteratedCovGrad_symmS_eq (I := I) (M := M) g₀ T k]
    rw [show (((1 / 2 : ℝ) • A + (1 / 2 : ℝ) • B).toSection x) =
        ((1 / 2 : ℝ) • A).toSection x + ((1 / 2 : ℝ) • B).toSection x from by
      rw [SmoothCcTensor.toSection_add]; rfl]
    rw [show (((1 / 2 : ℝ) • A).toSection x) = (1 / 2 : ℝ) • (A.toSection x) from by
        rw [SmoothCcTensor.toSection_smul]; rfl,
      show (((1 / 2 : ℝ) • B).toSection x) = (1 / 2 : ℝ) • (B.toSection x) from by
        rw [SmoothCcTensor.toSection_smul]; rfl]
  rw [htoSec]
  have hRB : riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + k) x (B.toSection x) =
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + k) x (A.toSection x) := hswap
  calc riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + k) x
          ((1 / 2 : ℝ) • (A.toSection x) + (1 / 2 : ℝ) • (B.toSection x))
      ≤ 2 * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + k) x
            ((1 / 2 : ℝ) • (A.toSection x)) +
          2 * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + k) x
            ((1 / 2 : ℝ) • (B.toSection x)) :=
        riemannianFiberNormSq_add_le (I := I) (M := M) g₀ 0 (2 + k) x _ _
    _ = (1 / 2 : ℝ) * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + k) x (A.toSection x) +
          (1 / 2 : ℝ) * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + k) x (B.toSection x) := by
        rw [rfns_smul_pt, rfns_smul_pt]; ring
    _ = riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + k) x (A.toSection x) := by
        rw [hRB]; ring

omit [NeZero (Module.finrank ℝ E)] in
private lemma rfns_iteratedCovGrad_koszulCovecCc_pointwise (g₀ : SmoothRiemannianMetric I M)
    (T : SmoothCcTensor g₀ 0 2) (i : ℕ) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + i) x
        ((iteratedCovGrad (I := I) g₀ 0 3 i (koszulCovecCc (I := I) g₀ T)).toSection x) ≤
      10 * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 1)) x
        ((iteratedCovGrad (I := I) g₀ 0 2 (i + 1) T).toSection x) := by
  classical
  set W : SmoothCcTensor g₀ 0 3 := symmSCovGrad3 (I := I) g₀ T with hW
  set DA : SmoothCcTensor g₀ 0 3 :=
    domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 3) 2) W with hDA
  set DB : SmoothCcTensor g₀ 0 3 := domDomCongrSection (I := I) g₀ (finRotate 3) W with hDB
  set DC : SmoothCcTensor g₀ 0 3 :=
    domDomCongrSection (I := I) g₀ (Equiv.swap (1 : Fin 3) 2) W with hDC
  have hpermW : ∀ σ : Equiv.Perm (Fin 3),
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + i) x
        ((iteratedCovGrad (I := I) g₀ 0 3 i
          (domDomCongrSection (I := I) g₀ σ W)).toSection x) ≤
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 1)) x
        ((iteratedCovGrad (I := I) g₀ 0 2 (i + 1) T).toSection x) := by
    intro σ
    rw [riemannianFiberNormSq_iteratedCovGrad_domDomCongrSection (I := I) (M := M) g₀ σ W i x]
    rw [hW]
    rw [show symmSCovGrad3 (I := I) g₀ T =
        covGrad (I := I) (M := M) g₀ 0 2 (ccTensor02Symm (I := I) g₀ T) from rfl]
    have hcomm := rfns_iteratedCovGrad_covGrad_comm_rs (I := I) (M := M) g₀ 0 2 i
      (ccTensor02Symm (I := I) g₀ T) x
    rw [hcomm]
    exact rfns_iteratedCovGrad_symmS_pointwise (I := I) (M := M) g₀ T (i + 1) x
  have hkos : koszulCovecCc (I := I) g₀ T = (1 / 2 : ℝ) • (DA + DB - DC) := by
    rw [koszulCovecCc, hDA, hDB, hDC, hW]
  have hsub : iteratedCovGrad (I := I) g₀ 0 3 i (DA + DB - DC) =
      iteratedCovGrad (I := I) g₀ 0 3 i DA + iteratedCovGrad (I := I) g₀ 0 3 i DB -
        iteratedCovGrad (I := I) g₀ 0 3 i DC := by
    rw [sub_eq_add_neg, sub_eq_add_neg, iteratedCovGrad_add, iteratedCovGrad_add,
      iteratedCovGrad_neg]
  have htoSec : ((iteratedCovGrad (I := I) g₀ 0 3 i (koszulCovecCc (I := I) g₀ T)).toSection x :
        TensorRSSpace 0 (3 + i) I x) =
      (1 / 2 : ℝ) • ((iteratedCovGrad (I := I) g₀ 0 3 i DA).toSection x +
        (iteratedCovGrad (I := I) g₀ 0 3 i DB).toSection x -
        (iteratedCovGrad (I := I) g₀ 0 3 i DC).toSection x) := by
    rw [hkos, iteratedCovGrad_smul_pt, hsub]
    rw [show (((1 / 2 : ℝ) • (iteratedCovGrad (I := I) g₀ 0 3 i DA +
          iteratedCovGrad (I := I) g₀ 0 3 i DB -
          iteratedCovGrad (I := I) g₀ 0 3 i DC)).toSection x) =
        (1 / 2 : ℝ) • ((iteratedCovGrad (I := I) g₀ 0 3 i DA +
          iteratedCovGrad (I := I) g₀ 0 3 i DB -
          iteratedCovGrad (I := I) g₀ 0 3 i DC).toSection x) from by
      rw [SmoothCcTensor.toSection_smul]; rfl]
    rw [show ((iteratedCovGrad (I := I) g₀ 0 3 i DA +
          iteratedCovGrad (I := I) g₀ 0 3 i DB -
          iteratedCovGrad (I := I) g₀ 0 3 i DC).toSection x) =
        (iteratedCovGrad (I := I) g₀ 0 3 i DA).toSection x +
          (iteratedCovGrad (I := I) g₀ 0 3 i DB).toSection x -
          (iteratedCovGrad (I := I) g₀ 0 3 i DC).toSection x from by
      rw [SmoothCcTensor.toSection_sub, SmoothCcTensor.toSection_add]; rfl]
  set PA := (iteratedCovGrad (I := I) g₀ 0 3 i DA).toSection x with hPA
  set PB := (iteratedCovGrad (I := I) g₀ 0 3 i DB).toSection x with hPB
  set PC := (iteratedCovGrad (I := I) g₀ 0 3 i DC).toSection x with hPC
  set R2 : ℝ := riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 1)) x
    ((iteratedCovGrad (I := I) g₀ 0 2 (i + 1) T).toSection x) with hR2
  have hbA : riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + i) x PA ≤ R2 :=
    hpermW (Equiv.swap (0 : Fin 3) 2)
  have hbB : riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + i) x PB ≤ R2 :=
    hpermW (finRotate 3)
  have hbC : riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + i) x PC ≤ R2 :=
    hpermW (Equiv.swap (1 : Fin 3) 2)
  rw [htoSec, rfns_smul_pt]
  have hnegC : riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + i) x (-PC) =
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + i) x PC :=
    rfns_neg_pt (I := I) (M := M) g₀ 0 (3 + i) x PC
  have hR2_nn : 0 ≤ R2 := riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + (i + 1)) x _
  have hsum : riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + i) x (PA + PB - PC) ≤
      10 * R2 := by
    have h1 := riemannianFiberNormSq_add_le (I := I) (M := M) g₀ 0 (3 + i) x (PA + PB) (-PC)
    have h2 := riemannianFiberNormSq_add_le (I := I) (M := M) g₀ 0 (3 + i) x PA PB
    rw [hnegC] at h1
    rw [show PA + PB - PC = (PA + PB) + (-PC) from sub_eq_add_neg _ _]
    linarith [h1, h2, hbA, hbB, hbC,
      riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (3 + i) x PA,
      riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (3 + i) x PB,
      riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (3 + i) x PC]
  linarith [hsum, hR2_nn,
    riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (3 + i) x (PA + PB - PC)]

omit [NeZero (Module.finrank ℝ E)] in
lemma rfns_iteratedCovGrad_raisedKoszul_pointwise (g₀ g₁ : SmoothRiemannianMetric I M)
    (T : SmoothCcTensor g₀ 0 2)
    (htie : ∀ (y : M) (v w : TangentSpace I y),
      g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ T y v w)
    (i : ℕ) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + i) x
        ((iteratedCovGrad (I := I) g₀ 1 2 i (raisedKoszul (I := I) g₀ g₁)).toSection x) ≤
      10 * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 1)) x
        ((iteratedCovGrad (I := I) g₀ 0 2 (i + 1) T).toSection x) := by
  rw [raisedKoszul_eq_cometricRaiseSlot0Field_koszulCovecCc (I := I) (M := M) g₀ g₁ T htie]
  rw [riemannianFiberNormSq_iteratedCovGrad_cometricRaiseSlot0Field_koszul_eq (I := I) (M := M) g₀ T
    i x]
  exact rfns_iteratedCovGrad_koszulCovecCc_pointwise (I := I) (M := M) g₀ T i x

omit [NeZero (Module.finrank ℝ E)] in
/-- The lowered Koszul covector costs exactly one metric derivative in `L2`. -/
theorem koszul_l2_succ
    (g₀ : SmoothRiemannianMetric I M) (T : SmoothCcTensor g₀ 0 2)
    (n : ℕ) :
    ‖iteratedCovGrad (I := I) g₀ 0 3 n (koszulCovecCc (I := I) g₀ T)‖ ^ 2 ≤
      10 * ‖iteratedCovGrad (I := I) g₀ 0 2 (n + 1) T‖ ^ 2 := by
  have hpt : ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + n) x
          ((iteratedCovGrad (I := I) g₀ 0 3 n
            (koszulCovecCc (I := I) g₀ T)).toSection x) ≤
        10 * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (n + 1)) x
          ((iteratedCovGrad (I := I) g₀ 0 2 (n + 1) T).toSection x) := by
    intro x
    exact rfns_iteratedCovGrad_koszulCovecCc_pointwise
      (I := I) (M := M) g₀ T n x
  have hF_int : MeasureTheory.Integrable
      (fun x => 10 * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (n + 1)) x
        ((iteratedCovGrad (I := I) g₀ 0 2 (n + 1) T).toSection x))
      (riemannianVolumeMeasure (I := I) (M := M) g₀) :=
    (integrable_riemannianFiberNormSq_toSection
      (I := I) (M := M) g₀ 0 (2 + (n + 1))
      (iteratedCovGrad (I := I) g₀ 0 2 (n + 1) T)).const_mul _
  have key := normSq_le_integral_of_pointwise_fiberNormSq_le_rs
    (I := I) (M := M) g₀ 0 (3 + n)
    (iteratedCovGrad (I := I) g₀ 0 3 n (koszulCovecCc (I := I) g₀ T))
    (fun x => 10 * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (n + 1)) x
      ((iteratedCovGrad (I := I) g₀ 0 2 (n + 1) T).toSection x))
    hF_int hpt
  refine key.trans ?_
  rw [MeasureTheory.integral_const_mul]
  rw [← tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs
    (I := I) (M := M) g₀ 0 (2 + (n + 1))
    (iteratedCovGrad (I := I) g₀ 0 2 (n + 1) T)]
  rw [← SmoothCcTensor.norm_def]

end NormedRaisedKoszulPointwise

section NormedConnectionDifferenceGrid

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

theorem exists_rfns_iteratedCovGrad_sharpFlatEndoCc_tgrid
    (g₀ : SmoothRiemannianMetric I M) {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ S : ℕ → ℝ, (∀ l, 0 ≤ S l) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (T : SmoothCcTensor g₀ 0 2)
        (_htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ T y v w)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀) (_hδ0 : 0 ≤ δ)
        (_hbound : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T)
          δ)
        (l : ℕ) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + l) x
            ((iteratedCovGrad (I := I) g₀ 1 1 l (sharpFlatEndoCc (I := I) g₀ g₁)).toSection x) ≤
          S l * Combinatorics.antidiagonalTupleGrid
            (fun j => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x
              ((iteratedCovGrad (I := I) g₀ 0 2 j T).toSection x)) l := by
  classical
  obtain ⟨CD, hCD_nn, hCD⟩ :=
    riemannianFiberNormSq_iteratedCovGrad_slotInsertEndoCc_zero_gInvDiffRaisedEndo_diagGrid_le
      (I := I) (M := M) g₀ hδ₀
  obtain ⟨cid, hcid_nn, hcid⟩ := exists_bound_riemannianFiberNormSq_smoothCcTensor
    (I := I) (M := M) g₀ 1 1
    (endoSlotZeroCcTensor (I := I) (M := M) g₀ 0 (fullRaisedEndoField (I := I) (M := M) g₀ g₀))
  refine ⟨fun l => 2 * CD l + 2 * cid,
    fun l => by have := hCD_nn l; linarith, ?_⟩
  intro g₁ T htie δ hδ_le hδ0 hbound l x
  set b : ℕ → ℝ := fun j => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x
    ((iteratedCovGrad (I := I) g₀ 0 2 j T).toSection x) with hb_def
  have hb : ∀ j, 0 ≤ b j :=
    fun j => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + j) x _
  have hgrid_nn : 0 ≤ Combinatorics.antidiagonalTupleGrid b l :=
    Combinatorics.antidiagonalTupleGrid_nonneg b hb l
  have hsplit : sharpFlatEndoCc (I := I) g₀ g₁ =
      endoSlotZeroCcTensor (I := I) (M := M) g₀ 0 (gInvDiffRaisedEndoField (I := I) g₀ g₁) +
        endoSlotZeroCcTensor (I := I) (M := M) g₀ 0
          (fullRaisedEndoField (I := I) (M := M) g₀ g₀) := by
    rw [sharpFlatEndoCc_eq_slotInsert_fullRaised (I := I) (M := M) g₀ g₁,
      fullRaisedEndoField_diff_split (I := I) (M := M) g₀ g₁,
      slotInsertEndoCc_add_endo (I := I) (M := M) g₀ 0]
  have hsec : (iteratedCovGrad (I := I) g₀ 1 1 l (sharpFlatEndoCc (I := I) g₀ g₁)).toSection x =
      (iteratedCovGrad (I := I) g₀ 1 1 l
        (endoSlotZeroCcTensor (I := I) (M := M) g₀ 0
          (gInvDiffRaisedEndoField (I := I) g₀ g₁))).toSection x +
      (iteratedCovGrad (I := I) g₀ 1 1 l
        (endoSlotZeroCcTensor (I := I) (M := M) g₀ 0
          (fullRaisedEndoField (I := I) (M := M) g₀ g₀))).toSection x := by
    rw [hsplit, iteratedCovGrad_add, SmoothCcTensor.toSection_add]
    rfl
  rw [hsec]
  refine le_trans (riemannianFiberNormSq_add_le (I := I) (M := M) g₀ 1 (1 + l) x _ _) ?_
  have hA : riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + l) x
      ((iteratedCovGrad (I := I) g₀ 1 1 l
        (endoSlotZeroCcTensor (I := I) (M := M) g₀ 0
          (gInvDiffRaisedEndoField (I := I) g₀ g₁))).toSection x) ≤
      CD l * Combinatorics.antidiagonalTupleGrid b l :=
    hCD g₁ T htie hδ_le hδ0 hbound l x
  have hB : riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + l) x
      ((iteratedCovGrad (I := I) g₀ 1 1 l
        (endoSlotZeroCcTensor (I := I) (M := M) g₀ 0
          (fullRaisedEndoField (I := I) (M := M) g₀ g₀))).toSection x) ≤
      cid * Combinatorics.antidiagonalTupleGrid b l := by
    match l with
    | 0 =>
        rw [iteratedCovGrad_zero]
        rw [Combinatorics.antidiagonalTupleGrid_zero, mul_one]
        exact hcid x
    | (m + 1) =>
        rw [iteratedCovGrad_slotInsert_fullRaised_id_succ_eq_zero (I := I) (M := M) g₀ m]
        rw [show ((0 : SmoothCcTensor g₀ 1 (1 + (m + 1))).toSection x) =
            (0 : TensorRSSpace 1 (1 + (m + 1)) I x) from by
          rw [SmoothCcTensor.toSection_zero]; rfl]
        rw [riemannianFiberNormSq_zero (I := I) (M := M) g₀ 1 (1 + (m + 1)) x]
        exact mul_nonneg hcid_nn
          (Combinatorics.antidiagonalTupleGrid_nonneg b hb (m + 1))
  calc 2 * riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + l) x
          ((iteratedCovGrad (I := I) g₀ 1 1 l
            (endoSlotZeroCcTensor (I := I) (M := M) g₀ 0
              (gInvDiffRaisedEndoField (I := I) g₀ g₁))).toSection x) +
        2 * riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + l) x
          ((iteratedCovGrad (I := I) g₀ 1 1 l
            (endoSlotZeroCcTensor (I := I) (M := M) g₀ 0
              (fullRaisedEndoField (I := I) (M := M) g₀ g₀))).toSection x)
      ≤ 2 * (CD l * Combinatorics.antidiagonalTupleGrid b l) +
          2 * (cid * Combinatorics.antidiagonalTupleGrid b l) := by
        have h1 := riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 1 (1 + l) x
          ((iteratedCovGrad (I := I) g₀ 1 1 l
            (endoSlotZeroCcTensor (I := I) (M := M) g₀ 0
              (gInvDiffRaisedEndoField (I := I) g₀ g₁))).toSection x)
        linarith
    _ = (2 * CD l + 2 * cid) * Combinatorics.antidiagonalTupleGrid b l := by ring

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma rfns_iteratedCovGrad_order_congr_ts (g : SmoothRiemannianMetric I M)
    (r s : ℕ) {n n' : ℕ} (h : n = n') (S : SmoothCcTensor g r s) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g r (s + n) x
        ((iteratedCovGrad (I := I) g r s n S).toSection x) =
      riemannianFiberNormSq (I := I) (M := M) g r (s + n') x
        ((iteratedCovGrad (I := I) g r s n' S).toSection x) := by
  subst h; rfl

theorem rfns_iteratedCovGrad_connDiffSection_topSeparated_le
    (g₀ : SmoothRiemannianMetric I M) {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ Ktop : ℝ, 0 ≤ Ktop ∧ ∃ Kc : ℕ → ℝ, (∀ j, 0 ≤ Kc j) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (T : SmoothCcTensor g₀ 0 2)
        (_htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ T y v w)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀) (_hδ0 : 0 ≤ δ)
        (_hbound : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T)
          δ)
        (j : ℕ) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + j) x
            ((ccOperatorFieldComp (I := I) (M := M) g₀ 1 1 (2 + j)
              (iteratedCovGrad (I := I) g₀ 1 2 j (raisedKoszul (I := I) g₀ g₁))
              (sharpFlatEndoCc (I := I) g₀ g₁)).toSection x) ≤
          Ktop * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (j + 1)) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (j + 1) T).toSection x) ∧
        riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + j) x
            ((iteratedCovGrad (I := I) g₀ 1 2 j (connDiffSection (I := I) g₁ g₀) -
              ccOperatorFieldComp (I := I) (M := M) g₀ 1 1 (2 + j)
                (iteratedCovGrad (I := I) g₀ 1 2 j (raisedKoszul (I := I) g₀ g₁))
                (sharpFlatEndoCc (I := I) g₀ g₁)).toSection x) ≤
          Kc j * ∑ k ∈ Finset.range j,
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (j - k)) x
                ((iteratedCovGrad (I := I) g₀ 0 2 (j - k) T).toSection x) *
              Combinatorics.antidiagonalTupleGrid
                (fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
                  ((iteratedCovGrad (I := I) g₀ 0 2 l T).toSection x)) (k + 1) := by
  classical
  obtain ⟨S, hS_nn, hS⟩ :=
    exists_rfns_iteratedCovGrad_sharpFlatEndoCc_tgrid (I := I) (M := M) g₀ hδ₀
  refine ⟨10 * S 0, mul_nonneg (by norm_num) (hS_nn 0), ?_⟩
  refine ⟨fun j => (j : ℝ) * diagonalGridGrowthFactor (E := E) j *
    (10 * ∑ l ∈ Finset.range (j + 1), S l),
    fun j => mul_nonneg (mul_nonneg (Nat.cast_nonneg j) (appCcGdiag_nonneg (E := E) j))
      (mul_nonneg (by norm_num) (Finset.sum_nonneg (fun l _ => hS_nn l))), ?_⟩
  intro g₁ T htie δ hδ_le hδ0 hbound j x
  set b : ℕ → ℝ := fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
    ((iteratedCovGrad (I := I) g₀ 0 2 l T).toSection x) with hb_def
  have hb : ∀ l, 0 ≤ b l :=
    fun l => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + l) x _
  constructor
  · rw [appCcRS_toSection (I := I) (M := M) g₀ 1 1 (2 + j)
      (iteratedCovGrad (I := I) g₀ 1 2 j (raisedKoszul (I := I) g₀ g₁))
      (sharpFlatEndoCc (I := I) g₀ g₁) x]
    refine le_trans (riemannianFiberNormSq_compRS_le_mul (I := I) (M := M) g₀ 1 1 (2 + j) x
      ((iteratedCovGrad (I := I) g₀ 1 2 j (raisedKoszul (I := I) g₀ g₁)).toSection x)
      ((sharpFlatEndoCc (I := I) g₀ g₁).toSection x)) ?_
    have hK := rfns_iteratedCovGrad_raisedKoszul_pointwise (I := I) (M := M) g₀ g₁ T htie j x
    have hF : riemannianFiberNormSq (I := I) (M := M) g₀ 1 1 x
        ((sharpFlatEndoCc (I := I) g₀ g₁).toSection x) ≤ S 0 := by
      have h0 := hS g₁ T htie hδ_le hδ0 hbound 0 x
      rw [Combinatorics.antidiagonalTupleGrid_zero, mul_one] at h0
      exact h0
    calc riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + j) x
            ((iteratedCovGrad (I := I) g₀ 1 2 j (raisedKoszul (I := I) g₀ g₁)).toSection x) *
          riemannianFiberNormSq (I := I) (M := M) g₀ 1 1 x
            ((sharpFlatEndoCc (I := I) g₀ g₁).toSection x)
        ≤ (10 * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (j + 1)) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (j + 1) T).toSection x)) * S 0 :=
          mul_le_mul hK hF
            (riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 1 1 x _)
            (mul_nonneg (by norm_num)
              (riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + (j + 1)) x _))
      _ = (10 * S 0) * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (j + 1)) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (j + 1) T).toSection x) := by ring
  · have hid : iteratedCovGrad (I := I) g₀ 1 2 j (connDiffSection (I := I) g₁ g₀) =
        ccOperatorFieldComp (I := I) (M := M) g₀ 1 1 (2 + j)
            (iteratedCovGrad (I := I) g₀ 1 2 j (raisedKoszul (I := I) g₀ g₁))
            (sharpFlatEndoCc (I := I) g₀ g₁) +
          ∑ k ∈ Finset.range j,
            ccOperatorFieldComp (I := I) (M := M) g₀ 1 (1 + (k + 1)) (2 + j)
              (appCcLeibnizPsi (I := I) (M := M) g₀ 1 2 (raisedKoszul (I := I) g₀ g₁) j (k + 1))
              (iteratedCovGrad (I := I) g₀ 1 1 (k + 1) (sharpFlatEndoCc (I := I) g₀ g₁)) := by
      rw [connDiffSection_eq_appCcRS_raisedKoszul_sharpFlatEndoCc (I := I) (M := M) g₀ g₁]
      rw [iteratedCovGrad_appCcRS_eq (I := I) (M := M) g₀ 1 1 2
        (raisedKoszul (I := I) g₀ g₁) (sharpFlatEndoCc (I := I) g₀ g₁) j]
      rw [Finset.sum_range_succ' (fun k =>
        ccOperatorFieldComp (I := I) (M := M) g₀ 1 (1 + k) (2 + j)
          (appCcLeibnizPsi (I := I) (M := M) g₀ 1 2 (raisedKoszul (I := I) g₀ g₁) j k)
          (iteratedCovGrad (I := I) g₀ 1 1 k (sharpFlatEndoCc (I := I) g₀ g₁))) j]
      have hf0 : ccOperatorFieldComp (I := I) (M := M) g₀ 1 (1 + 0) (2 + j)
          (appCcLeibnizPsi (I := I) (M := M) g₀ 1 2 (raisedKoszul (I := I) g₀ g₁) j 0)
          (iteratedCovGrad (I := I) g₀ 1 1 0 (sharpFlatEndoCc (I := I) g₀ g₁)) =
          ccOperatorFieldComp (I := I) (M := M) g₀ 1 1 (2 + j)
            (iteratedCovGrad (I := I) g₀ 1 2 j (raisedKoszul (I := I) g₀ g₁))
            (sharpFlatEndoCc (I := I) g₀ g₁) :=
        congrArg (fun Z : SmoothCcTensor g₀ 1 (2 + j) =>
          ccOperatorFieldComp (I := I) (M := M) g₀ 1 1 (2 + j) Z (sharpFlatEndoCc (I := I) g₀ g₁))
          (appCcLeibnizPsi_zero_right_eq (I := I) (M := M) g₀ 1 2
            (raisedKoszul (I := I) g₀ g₁) j)
      rw [hf0]
      exact add_comm _ _
    have hsub : iteratedCovGrad (I := I) g₀ 1 2 j (connDiffSection (I := I) g₁ g₀) -
        ccOperatorFieldComp (I := I) (M := M) g₀ 1 1 (2 + j)
          (iteratedCovGrad (I := I) g₀ 1 2 j (raisedKoszul (I := I) g₀ g₁))
          (sharpFlatEndoCc (I := I) g₀ g₁) =
        ∑ k ∈ Finset.range j,
          ccOperatorFieldComp (I := I) (M := M) g₀ 1 (1 + (k + 1)) (2 + j)
            (appCcLeibnizPsi (I := I) (M := M) g₀ 1 2 (raisedKoszul (I := I) g₀ g₁) j (k + 1))
            (iteratedCovGrad (I := I) g₀ 1 1 (k + 1) (sharpFlatEndoCc (I := I) g₀ g₁)) := by
      rw [hid]
      exact add_sub_cancel_left _ _
    rw [hsub]
    rw [SmoothCcTensor.toSection_sum_apply]
    refine le_trans (riemannianFiberNormSq_sum_le_card_mul (I := I) (M := M) g₀ 1 (2 + j) x
      (Finset.range j) (fun k =>
        (ccOperatorFieldComp (I := I) (M := M) g₀ 1 (1 + (k + 1)) (2 + j)
          (appCcLeibnizPsi (I := I) (M := M) g₀ 1 2 (raisedKoszul (I := I) g₀ g₁) j (k + 1))
          (iteratedCovGrad (I := I) g₀ 1 1 (k + 1)
            (sharpFlatEndoCc (I := I) g₀ g₁))).toSection x)) ?_
    rw [Finset.card_range]
    have hstep : (∑ k ∈ Finset.range j,
        riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + j) x
          ((ccOperatorFieldComp (I := I) (M := M) g₀ 1 (1 + (k + 1)) (2 + j)
            (appCcLeibnizPsi (I := I) (M := M) g₀ 1 2 (raisedKoszul (I := I) g₀ g₁) j (k + 1))
            (iteratedCovGrad (I := I) g₀ 1 1 (k + 1)
              (sharpFlatEndoCc (I := I) g₀ g₁))).toSection x)) ≤
        ∑ k ∈ Finset.range j,
          diagonalGridGrowthFactor (E := E) j * (10 * ∑ l ∈ Finset.range (j + 1), S l) *
            (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (j - k)) x
                ((iteratedCovGrad (I := I) g₀ 0 2 (j - k) T).toSection x) *
              Combinatorics.antidiagonalTupleGrid b (k + 1)) := by
      refine Finset.sum_le_sum (fun k hk => ?_)
      have hk_lt : k < j := Finset.mem_range.mp hk
      rw [appCcRS_toSection (I := I) (M := M) g₀ 1 (1 + (k + 1)) (2 + j)
        (appCcLeibnizPsi (I := I) (M := M) g₀ 1 2 (raisedKoszul (I := I) g₀ g₁) j (k + 1))
        (iteratedCovGrad (I := I) g₀ 1 1 (k + 1) (sharpFlatEndoCc (I := I) g₀ g₁)) x]
      refine le_trans (riemannianFiberNormSq_compRS_le_mul (I := I) (M := M) g₀ 1 (1 + (k + 1))
        (2 + j) x
        ((appCcLeibnizPsi (I := I) (M := M) g₀ 1 2 (raisedKoszul (I := I) g₀ g₁) j
          (k + 1)).toSection x)
        ((iteratedCovGrad (I := I) g₀ 1 1 (k + 1)
          (sharpFlatEndoCc (I := I) g₀ g₁)).toSection x)) ?_
      have hPsi : riemannianFiberNormSq (I := I) (M := M) g₀ (1 + (k + 1)) (2 + j) x
          ((appCcLeibnizPsi (I := I) (M := M) g₀ 1 2 (raisedKoszul (I := I) g₀ g₁) j
            (k + 1)).toSection x) ≤
          diagonalGridGrowthFactor (E := E) j * (10 * b (j - k)) := by
        have hE3 := rfns_iteratedCovGrad_appCcLeibnizPsi_window_le (I := I) (M := M) g₀ 1 2
          (raisedKoszul (I := I) g₀ g₁) j (k + 1) 0 (by omega : k + 1 ≤ j) x
        rw [rfns_iteratedCovGrad_order_congr_ts (I := I) (M := M) g₀ 1 2
          (show (j - (k + 1)) + 0 = j - (k + 1) from by omega)
          (raisedKoszul (I := I) g₀ g₁) x] at hE3
        refine le_trans hE3 (mul_le_mul_of_nonneg_left ?_ (appCcGdiag_nonneg (E := E) j))
        have hK := rfns_iteratedCovGrad_raisedKoszul_pointwise (I := I) (M := M) g₀ g₁ T htie
          (j - (k + 1)) x
        rw [rfns_iteratedCovGrad_order_congr_ts (I := I) (M := M) g₀ 0 2
          (show (j - (k + 1)) + 1 = j - k from by omega) T x] at hK
        exact hK
      have hF : riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + (k + 1)) x
          ((iteratedCovGrad (I := I) g₀ 1 1 (k + 1)
            (sharpFlatEndoCc (I := I) g₀ g₁)).toSection x) ≤
          S (k + 1) * Combinatorics.antidiagonalTupleGrid b (k + 1) :=
        hS g₁ T htie hδ_le hδ0 hbound (k + 1) x
      have hgrid_nn : 0 ≤ Combinatorics.antidiagonalTupleGrid b (k + 1) :=
        Combinatorics.antidiagonalTupleGrid_nonneg b hb (k + 1)
      have hSk_le : S (k + 1) ≤ ∑ l ∈ Finset.range (j + 1), S l :=
        Finset.single_le_sum (f := S) (fun l _ => hS_nn l)
          (Finset.mem_range.mpr (by omega : k + 1 < j + 1))
      calc riemannianFiberNormSq (I := I) (M := M) g₀ (1 + (k + 1)) (2 + j) x
              ((appCcLeibnizPsi (I := I) (M := M) g₀ 1 2 (raisedKoszul (I := I) g₀ g₁) j
                (k + 1)).toSection x) *
            riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + (k + 1)) x
              ((iteratedCovGrad (I := I) g₀ 1 1 (k + 1)
                (sharpFlatEndoCc (I := I) g₀ g₁)).toSection x)
          ≤ (diagonalGridGrowthFactor (E := E) j * (10 * b (j - k))) *
              (S (k + 1) * Combinatorics.antidiagonalTupleGrid b (k + 1)) := by
            refine mul_le_mul hPsi hF
              (riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 1 (1 + (k + 1)) x _) ?_
            have h10 : (0 : ℝ) ≤ 10 * b (j - k) := by
              have := hb (j - k); linarith
            exact mul_nonneg (appCcGdiag_nonneg (E := E) j) h10
        _ ≤ (diagonalGridGrowthFactor (E := E) j * (10 * b (j - k))) *
              ((∑ l ∈ Finset.range (j + 1), S l) *
                Combinatorics.antidiagonalTupleGrid b (k + 1)) := by
            refine mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_right hSk_le hgrid_nn) ?_
            have h10 : (0 : ℝ) ≤ 10 * b (j - k) := by
              have := hb (j - k); linarith
            exact mul_nonneg (appCcGdiag_nonneg (E := E) j) h10
        _ = diagonalGridGrowthFactor (E := E) j * (10 * ∑ l ∈ Finset.range (j + 1), S l) *
              (b (j - k) * Combinatorics.antidiagonalTupleGrid b (k + 1)) := by ring
    refine le_trans (mul_le_mul_of_nonneg_left hstep (Nat.cast_nonneg j)) (le_of_eq ?_)
    rw [← Finset.mul_sum]
    ring

def connDiffArmFieldPt (g₀ g₁ : SmoothRiemannianMetric I M) :
    ContMDiffSection I (E →L[ℝ] (E →L[ℝ] E)) ∞
      (fun x : M => TangentSpace I x →L[ℝ] (TangentSpace I x →L[ℝ] TangentSpace I x)) :=
  ⟨fun x : M => PDE.DeTurck.connDiff (I := I) g₁ g₀ x,
    bilinEndoField_contMDiff (I := I) (M := M)
      (fun x : M => PDE.DeTurck.connDiff (I := I) g₁ g₀ x)
      (fun V0 W => PDE.DeTurck.connDiff_contMDiff (I := I) g₁ g₀ V0.contMDiff W.contMDiff)⟩

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma connDiffArmFieldPt_apply (g₀ g₁ : SmoothRiemannianMetric I M) (x : M) :
    connDiffArmFieldPt (I := I) (M := M) g₀ g₁ x = PDE.DeTurck.connDiff (I := I) g₁ g₀ x := rfl

set_option backward.isDefEq.respectTransparency false in
omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
private lemma connDiffSection_eq_armSlotEndoCc_zero (g₀ g₁ : SmoothRiemannianMetric I M) :
    connDiffSection (I := I) g₁ g₀ =
      armSlotEndoCc (I := I) (M := M) g₀ 0 (connDiffArmFieldPt (I := I) (M := M) g₀ g₁) := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  apply ContinuousLinearMap.ext
  intro om
  apply Tensor0SSpace.toModel_injective
  apply ContinuousMultilinearMap.ext
  intro v
  rw [show ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 2 I x from
        (armSlotEndoCc (I := I) (M := M) g₀ 0
          (connDiffArmFieldPt (I := I) (M := M) g₀ g₁)).toSection x) om) =
      bilinearSlotInsertCLM (I := I) (M := M) 0 x (connDiffArmFieldPt (I := I) (M := M) g₀ g₁ x) om
      from rfl]
  rw [armSlotFib_apply_eval (I := I) (M := M) 0 x
    (connDiffArmFieldPt (I := I) (M := M) g₀ g₁ x) om v]
  rw [slotInsertEndoFib_apply_eval]
  rw [show (Function.update (Matrix.vecTail (fun k : Fin 2 => (v k : E))) 0
        (connDiffArmFieldPt (I := I) (M := M) g₀ g₁ x (v 0)
          (Matrix.vecTail (fun k : Fin 2 => (v k : E)) 0))) =
      (fun _ : Fin 1 => (show E from
        PDE.DeTurck.connDiff (I := I) g₁ g₀ x (v 0) (v 1))) from by
    funext k
    rw [show k = (0 : Fin 1) from Subsingleton.elim k 0]
    rw [Function.update_self]
    rfl]
  rw [show ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 2 I x from
        (connDiffSection (I := I) g₁ g₀).toSection x) om) =
      connDiffPairing (I := I) g₁ g₀ x om from rfl]
  change connDiffPairing (I := I) g₁ g₀ x om v = _
  rw [connDiffPairing_apply]
  rfl

set_option backward.isDefEq.respectTransparency false in
omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M]
    in
private lemma armSlotEndoCc_one_eq_reindex_slotExtend (g₀ : SmoothRiemannianMetric I M)
    (Arm : ContMDiffSection I (E →L[ℝ] (E →L[ℝ] E)) ∞
      (fun x : M => TangentSpace I x →L[ℝ] (TangentSpace I x →L[ℝ] TangentSpace I x))) :
    armSlotEndoCc (I := I) (M := M) g₀ 1 Arm =
      reindexCoeffGen (I := I) (M := M) g₀ 2 3
        (rsDomDomCongrSection (I := I) (M := M) g₀ 2 3 (finRotate 3).symm
          (slotExtend (I := I) (M := M) g₀ 1 2 (armSlotEndoCc (I := I) (M := M) g₀ 0 Arm)))
        (Equiv.swap (0 : Fin 2) 1) := by
  classical
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  apply ContinuousLinearMap.ext
  intro D
  apply Tensor0SSpace.toModel_injective
  apply ContinuousMultilinearMap.ext
  intro w
  have hτ0 : (finRotate 3).symm (0 : Fin 3) = (2 : Fin 3) := by decide
  have hτ1 : (finRotate 3).symm (1 : Fin 3) = (0 : Fin 3) := by decide
  have hτ2 : (finRotate 3).symm (2 : Fin 3) = (1 : Fin 3) := by decide
  set D' : Tensor0SSpace 2 I x := Tensor0SSpace.ofModel
    (ContinuousMultilinearMap.domDomCongr (Equiv.swap (0 : Fin 2) 1)
      (Tensor0SSpace.toModel D)) with hD'_def
  have hLHS : Tensor0SSpace.toModel
      ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 3 I x from
        (armSlotEndoCc (I := I) (M := M) g₀ 1 Arm).toSection x) D) w =
      Tensor0SSpace.toModel D
        (Function.update (Matrix.vecTail w) 0 (Arm x (w 0) (Matrix.vecTail w 0))) := by
    rw [show ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 3 I x from
          (armSlotEndoCc (I := I) (M := M) g₀ 1 Arm).toSection x) D) =
        bilinearSlotInsertCLM (I := I) (M := M) 1 x (Arm x) D from rfl]
    rw [armSlotFib_apply_eval (I := I) (M := M) 1 x (Arm x) D w]
    rw [slotInsertEndoFib_apply_eval]
  have e1 : Tensor0SSpace.toModel
      ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 3 I x from
        (reindexCoeffGen (I := I) (M := M) g₀ 2 3
          (rsDomDomCongrSection (I := I) (M := M) g₀ 2 3 (finRotate 3).symm
            (slotExtend (I := I) (M := M) g₀ 1 2 (armSlotEndoCc (I := I) (M := M) g₀ 0 Arm)))
          (Equiv.swap (0 : Fin 2) 1)).toSection x) D) w =
      Tensor0SSpace.toModel
        ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 3 I x from
          tensorRS_domDomCongr (finRotate 3).symm
            ((slotExtend (I := I) (M := M) g₀ 1 2
              (armSlotEndoCc (I := I) (M := M) g₀ 0 Arm)).toSection x)) D') w := by
    have h1 : ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 3 I x from
        (reindexCoeffGen (I := I) (M := M) g₀ 2 3
          (rsDomDomCongrSection (I := I) (M := M) g₀ 2 3 (finRotate 3).symm
            (slotExtend (I := I) (M := M) g₀ 1 2 (armSlotEndoCc (I := I) (M := M) g₀ 0 Arm)))
          (Equiv.swap (0 : Fin 2) 1)).toSection x) D) =
        ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 3 I x from
          tensorRS_domDomCongr (finRotate 3).symm
            ((slotExtend (I := I) (M := M) g₀ 1 2
              (armSlotEndoCc (I := I) (M := M) g₀ 0 Arm)).toSection x)) D') := by
      rw [reindexCoeffGen_toSection]
      rw [reindexCoeffFibGen_apply (I := I) 2 3 (Equiv.swap (0 : Fin 2) 1) x
        (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 3 I x from
          (rsDomDomCongrSection (I := I) (M := M) g₀ 2 3 (finRotate 3).symm
            (slotExtend (I := I) (M := M) g₀ 1 2
              (armSlotEndoCc (I := I) (M := M) g₀ 0 Arm))).toSection x) D]
      rw [← hD'_def]
      rw [rsDomDomCongrSection_toSection]
    exact congrArg (fun t : Tensor0SSpace 3 I x => Tensor0SSpace.toModel t w) h1
  have e2 : Tensor0SSpace.toModel
      ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 3 I x from
        tensorRS_domDomCongr (finRotate 3).symm
          ((slotExtend (I := I) (M := M) g₀ 1 2
            (armSlotEndoCc (I := I) (M := M) g₀ 0 Arm)).toSection x)) D') w =
      Tensor0SSpace.toModel
        ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 3 I x from
          (slotExtend (I := I) (M := M) g₀ 1 2
            (armSlotEndoCc (I := I) (M := M) g₀ 0 Arm)).toSection x) D')
        (fun i => w ((finRotate 3).symm i)) := by
    rw [toModel_rsDomDomCongr_apply (I := I) (M := M) (finRotate 3).symm
      ((slotExtend (I := I) (M := M) g₀ 1 2
        (armSlotEndoCc (I := I) (M := M) g₀ 0 Arm)).toSection x) D']
    rw [ContinuousMultilinearMap.domDomCongr_apply]
  have e3 : Tensor0SSpace.toModel
      ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 3 I x from
        (slotExtend (I := I) (M := M) g₀ 1 2
          (armSlotEndoCc (I := I) (M := M) g₀ 0 Arm)).toSection x) D')
      (fun i => w ((finRotate 3).symm i)) =
      Tensor0SSpace.toModel
        (bilinearSlotInsertCLM (I := I) (M := M) 0 x (Arm x)
          (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 1 x D' (w ((finRotate 3).symm 0))))
        (Matrix.vecTail (fun i => w ((finRotate 3).symm i))) := by
    rw [show ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 3 I x from
          (slotExtend (I := I) (M := M) g₀ 1 2
            (armSlotEndoCc (I := I) (M := M) g₀ 0 Arm)).toSection x) D') =
        (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 2 x).symm
          ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 2 I x from
              (armSlotEndoCc (I := I) (M := M) g₀ 0 Arm).toSection x).comp
            (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 1 x D')) from rfl]
    rw [show (fun i => w ((finRotate 3).symm i)) =
        Fin.cons (w ((finRotate 3).symm 0))
          (Matrix.vecTail (fun i => w ((finRotate 3).symm i))) from by
      funext k
      refine Fin.cases rfl (fun j => rfl) k]
    have hkey := TensorMultilinear.tensor0S_curry_apply_eval (I := I) (M := M) (n := 2)
      (T := (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 2 x).symm
        ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 2 I x from
            (armSlotEndoCc (I := I) (M := M) g₀ 0 Arm).toSection x).comp
          (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 1 x D')))
      (v0 := w ((finRotate 3).symm 0))
      (vs := Matrix.vecTail (fun i => w ((finRotate 3).symm i)))
    rw [ContinuousLinearEquiv.apply_symm_apply] at hkey
    rw [← hkey]
    rfl
  have e4 : Tensor0SSpace.toModel
      (bilinearSlotInsertCLM (I := I) (M := M) 0 x (Arm x)
        (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 1 x D' (w ((finRotate 3).symm 0))))
      (Matrix.vecTail (fun i => w ((finRotate 3).symm i))) =
      Tensor0SSpace.toModel
        (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 1 x D' (w ((finRotate 3).symm 0)))
        (fun _ : Fin 1 => (show E from
          Arm x (w ((finRotate 3).symm 1)) (w ((finRotate 3).symm 2)))) := by
    rw [armSlotFib_apply_eval (I := I) (M := M) 0 x (Arm x)
      (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 1 x D' (w ((finRotate 3).symm 0)))
      (Matrix.vecTail (fun i => w ((finRotate 3).symm i)))]
    rw [slotInsertEndoFib_apply_eval]
    congr 1
    funext k
    refine Fin.cases ?_ (fun j => j.elim0) k
    rw [Function.update_self]
    rfl
  have e5 : Tensor0SSpace.toModel
      (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 1 x D' (w ((finRotate 3).symm 0)))
      (fun _ : Fin 1 => (show E from
        Arm x (w ((finRotate 3).symm 1)) (w ((finRotate 3).symm 2)))) =
      Tensor0SSpace.toModel D'
        (Fin.cons (w ((finRotate 3).symm 0))
          (fun _ : Fin 1 => (show E from
            Arm x (w ((finRotate 3).symm 1)) (w ((finRotate 3).symm 2))))) :=
    TensorMultilinear.tensor0S_curry_apply_eval (I := I) (M := M) (n := 1)
      (T := D') (v0 := w ((finRotate 3).symm 0))
      (vs := fun _ : Fin 1 => (show E from
        Arm x (w ((finRotate 3).symm 1)) (w ((finRotate 3).symm 2))))
  have e6 : Tensor0SSpace.toModel D'
      (Fin.cons (w ((finRotate 3).symm 0))
        (fun _ : Fin 1 => (show E from
          Arm x (w ((finRotate 3).symm 1)) (w ((finRotate 3).symm 2))))) =
      Tensor0SSpace.toModel D
        (Function.update (Matrix.vecTail w) 0 (Arm x (w 0) (Matrix.vecTail w 0))) := by
    rw [hD'_def, Tensor0SSpace.toModel_ofModel, ContinuousMultilinearMap.domDomCongr_apply]
    rw [hτ0, hτ1, hτ2]
    congr 1
    funext k
    refine Fin.cases ?_ ?_ k
    · rw [show (Function.update (Matrix.vecTail w) 0
            (Arm x (w 0) (Matrix.vecTail w 0)) (0 : Fin 2)) =
          Arm x (w 0) (Matrix.vecTail w 0) from Function.update_self _ _ _]
      rfl
    · intro j
      refine Fin.cases ?_ (fun j2 => j2.elim0) j
      rw [show (Fin.succ (0 : Fin 1)) = (1 : Fin 2) from rfl]
      rw [Function.update_of_ne (by decide : (1 : Fin 2) ≠ 0)]
      rfl
  rw [hLHS, e1, e2, e3, e4, e5, e6]

lemma rfns_iteratedCovGrad_armSlotPass_connDiffArm_le
    (g₀ g₁ : SmoothRiemannianMetric I M) (j : ℕ) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g₀ 2 (3 + j) x
        ((iteratedCovGrad (I := I) g₀ 2 3 j
          (armSlotEndoPassZeroCc (I := I) (M := M) g₀
            (connDiffArmFieldPt (I := I) (M := M) g₀ g₁))).toSection x) ≤
      (Module.finrank ℝ E : ℝ) *
        riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + j) x
          ((iteratedCovGrad (I := I) g₀ 1 2 j (connDiffSection (I := I) g₁ g₀)).toSection x) := by
  rw [riemannianFiberNormSq_iteratedCovGrad_armSlotEndoPassZeroCc_eq (I := I) (M := M) g₀
    (connDiffArmFieldPt (I := I) (M := M) g₀ g₁) j x]
  rw [armSlotEndoCc_one_eq_reindex_slotExtend (I := I) (M := M) g₀
    (connDiffArmFieldPt (I := I) (M := M) g₀ g₁)]
  rw [rfns_iteratedCovGrad_rsDomDomCongr_both_eq (I := I) (M := M) g₀ 2 3
    (Equiv.swap (0 : Fin 2) 1) (finRotate 3).symm
    (slotExtend (I := I) (M := M) g₀ 1 2
      (armSlotEndoCc (I := I) (M := M) g₀ 0 (connDiffArmFieldPt (I := I) (M := M) g₀ g₁))) j x]
  refine le_trans (rfns_iteratedCovGrad_slotExtend_le (I := I) (M := M) g₀ 1 2
    (armSlotEndoCc (I := I) (M := M) g₀ 0 (connDiffArmFieldPt (I := I) (M := M) g₀ g₁)) j x) ?_
  rw [← connDiffSection_eq_armSlotEndoCc_zero (I := I) (M := M) g₀ g₁]

theorem exists_rfns_iteratedCovGrad_connDiffSection_tgrid
    (g₀ : SmoothRiemannianMetric I M) {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ CA : ℕ → ℝ, (∀ j, 0 ≤ CA j) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (T : SmoothCcTensor g₀ 0 2)
        (_htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ T y v w)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀) (_hδ0 : 0 ≤ δ)
        (_hbound : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T)
          δ)
        (j : ℕ) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + j) x
            ((iteratedCovGrad (I := I) g₀ 1 2 j
              (connDiffSection (I := I) g₁ g₀)).toSection x) ≤
          CA j * ∑ k ∈ Finset.range (j + 2),
            Combinatorics.antidiagonalTupleGrid
              (fun j' => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j') x
                ((iteratedCovGrad (I := I) g₀ 0 2 j' T).toSection x)) k := by
  classical
  obtain ⟨S, hS_nn, hS⟩ := exists_rfns_iteratedCovGrad_sharpFlatEndoCc_tgrid
    (I := I) (M := M) g₀ hδ₀
  refine ⟨fun j => diagonalGridGrowthFactor (E := E) j *
      ∑ i ∈ Finset.range (j + 1), 10 * ∑ l ∈ Finset.range (j + 1 - i), S l,
    fun j => mul_nonneg (appCcGdiag_nonneg (E := E) j)
      (Finset.sum_nonneg fun i _ => mul_nonneg (by norm_num)
        (Finset.sum_nonneg fun l _ => hS_nn l)), ?_⟩
  intro g₁ T htie δ hδ_le hδ0 hbound j x
  set b : ℕ → ℝ := fun j' => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j') x
    ((iteratedCovGrad (I := I) g₀ 0 2 j' T).toSection x) with hb_def
  have hb : ∀ j', 0 ≤ b j' :=
    fun j' => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + j') x _
  set G : ℝ := ∑ k ∈ Finset.range (j + 2), Combinatorics.antidiagonalTupleGrid b k with hG_def
  clear_value G
  have hG_nn : 0 ≤ G := by
    rw [hG_def]
    exact Finset.sum_nonneg fun k _ => Combinatorics.antidiagonalTupleGrid_nonneg b hb k
  have hcell : ∀ i ∈ Finset.range (j + 1), ∀ l ∈ Finset.range (j + 1 - i),
      riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + i) x
          ((iteratedCovGrad (I := I) g₀ 1 2 i (raisedKoszul (I := I) g₀ g₁)).toSection x) *
        riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + l) x
          ((iteratedCovGrad (I := I) g₀ 1 1 l (sharpFlatEndoCc (I := I) g₀ g₁)).toSection x) ≤
      (10 * S l) * G := by
    intro i hi l hl
    have h1 := rfns_iteratedCovGrad_raisedKoszul_pointwise (I := I) (M := M) g₀ g₁ T htie i x
    have h2 := hS g₁ T htie hδ_le hδ0 hbound l x
    have h1_nn := riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 1 (2 + i) x
      ((iteratedCovGrad (I := I) g₀ 1 2 i (raisedKoszul (I := I) g₀ g₁)).toSection x)
    have h2_nn := riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 1 (1 + l) x
      ((iteratedCovGrad (I := I) g₀ 1 1 l (sharpFlatEndoCc (I := I) g₀ g₁)).toSection x)
    have hb_le_grid : b (i + 1) * Combinatorics.antidiagonalTupleGrid b l ≤
        Combinatorics.antidiagonalTupleGrid b (l + (i + 1)) :=
      Combinatorics.single_factor_mul_antidiagonalTupleGrid_le b hb l (i + 1) (by omega)
    have hgrid_le_G : Combinatorics.antidiagonalTupleGrid b (l + (i + 1)) ≤ G := by
      rw [hG_def]
      refine Finset.single_le_sum
        (f := fun k => Combinatorics.antidiagonalTupleGrid b k)
        (fun k _ => Combinatorics.antidiagonalTupleGrid_nonneg b hb k) ?_
      rw [Finset.mem_range] at hi hl ⊢
      omega
    calc riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + i) x
            ((iteratedCovGrad (I := I) g₀ 1 2 i (raisedKoszul (I := I) g₀ g₁)).toSection x) *
          riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + l) x
            ((iteratedCovGrad (I := I) g₀ 1 1 l (sharpFlatEndoCc (I := I) g₀ g₁)).toSection x)
        ≤ (10 * b (i + 1)) * (S l * Combinatorics.antidiagonalTupleGrid b l) := by
          refine mul_le_mul ?_ h2 h2_nn (by
            have := hb (i + 1); linarith)
          exact h1
      _ = (10 * S l) * (b (i + 1) * Combinatorics.antidiagonalTupleGrid b l) := by ring
      _ ≤ (10 * S l) * Combinatorics.antidiagonalTupleGrid b (l + (i + 1)) := by
          refine mul_le_mul_of_nonneg_left hb_le_grid ?_
          have := hS_nn l; linarith
      _ ≤ (10 * S l) * G := by
          refine mul_le_mul_of_nonneg_left hgrid_le_G ?_
          have := hS_nn l; linarith
  refine le_trans (riemannianFiberNormSq_iteratedCovGrad_connDiffSection_diagonalProductGrid_le
    (I := I) (M := M) g₀ g₁ j x) ?_
  have hsum : (∑ i ∈ Finset.range (j + 1),
        riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + i) x
            ((iteratedCovGrad (I := I) g₀ 1 2 i (raisedKoszul (I := I) g₀ g₁)).toSection x) *
          ∑ l ∈ Finset.range (j + 1 - i),
            riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + l) x
              ((iteratedCovGrad (I := I) g₀ 1 1 l
                (sharpFlatEndoCc (I := I) g₀ g₁)).toSection x)) ≤
      (∑ i ∈ Finset.range (j + 1), 10 * ∑ l ∈ Finset.range (j + 1 - i), S l) * G := by
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun i hi => ?_
    rw [Finset.mul_sum]
    calc (∑ l ∈ Finset.range (j + 1 - i),
          riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + i) x
              ((iteratedCovGrad (I := I) g₀ 1 2 i (raisedKoszul (I := I) g₀ g₁)).toSection x) *
            riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + l) x
              ((iteratedCovGrad (I := I) g₀ 1 1 l
                (sharpFlatEndoCc (I := I) g₀ g₁)).toSection x))
        ≤ ∑ l ∈ Finset.range (j + 1 - i), (10 * S l) * G :=
          Finset.sum_le_sum fun l hl => hcell i hi l hl
      _ = (10 * ∑ l ∈ Finset.range (j + 1 - i), S l) * G := by
          rw [Finset.mul_sum, Finset.sum_mul]
  calc diagonalGridGrowthFactor (E := E) j *
        ∑ i ∈ Finset.range (j + 1),
          riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + i) x
              ((iteratedCovGrad (I := I) g₀ 1 2 i (raisedKoszul (I := I) g₀ g₁)).toSection x) *
            ∑ l ∈ Finset.range (j + 1 - i),
              riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + l) x
                ((iteratedCovGrad (I := I) g₀ 1 1 l
                  (sharpFlatEndoCc (I := I) g₀ g₁)).toSection x)
      ≤ diagonalGridGrowthFactor (E := E) j *
          ((∑ i ∈ Finset.range (j + 1), 10 * ∑ l ∈ Finset.range (j + 1 - i), S l) * G) :=
        mul_le_mul_of_nonneg_left hsum (appCcGdiag_nonneg (E := E) j)
    _ = (diagonalGridGrowthFactor (E := E) j *
          ∑ i ∈ Finset.range (j + 1), 10 * ∑ l ∈ Finset.range (j + 1 - i), S l) * G := by
        ring

end NormedConnectionDifferenceGrid

end RiemannLoweredDifference

end Spectral
end Analysis
end DifferentialGeometry
