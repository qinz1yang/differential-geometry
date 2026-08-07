import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.RicciDeTurckSectionDifference
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.CovDerivConnDiffQuadraticBound
import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.ConvexPerturbationPointwiseC2
import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.RicciDifferenceMeanValue
import DifferentialGeometry.Analysis.Sobolev.RiemannianFiberNormSq.RiemannianFiberNormSqSmoothCcUniformBound
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.OperatorFieldFibreNormJet
import DifferentialGeometry.Analysis.Sobolev.RiemannianFiberNormSq.RiemannianFiberNormSqRiemannOpDualFrameParseval
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.SingleSlotOperatorFiberNormBound
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.MetricArmCoeffJetTower
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.CurvatureCoefficientDifferenceJetTowerIntegral
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.IteratedCovGradFibreNormPermutationInvariance
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.RicciDeTurckLinearization
import DifferentialGeometry.Geometry.Flow.DeTurckVFConnDiffVariation
import DifferentialGeometry.Analysis.Integration.DivergenceTheorem.BracketDivergenceForm
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.DeTurckLieKernelL2JetBoundCoeffFieldOrderZeroBound
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.DeTurckLieKernelL2JetBoundLoweredKernelTensors
import DifferentialGeometry.Tensor.Auxiliary.DeTurckLieKernelL2JetBoundGridWindow
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.DeTurckLieKernelL2JetBoundCometricTraceFrame
open DifferentialGeometry.Tensor.Auxiliary
open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Analysis.Elliptic
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Operator


noncomputable section

set_option backward.isDefEq.respectTransparency false

open MeasureTheory Set Filter Topology Bundle Manifold DifferentialGeometry.Tensor0SBundle ContinuousLinearMap
open scoped ENNReal NNReal BigOperators Manifold ContDiff

namespace DifferentialGeometry.Analysis.Sobolev

open DifferentialGeometry
open DifferentialGeometry.PDE.RicciFlow DifferentialGeometry.Analysis.Sobolev DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
  (connDiffCovDerivBiContrFib dLaBiContrFib_contMDiff deTurckLieDLbFib deTurckLieDLbFib_contMDiff
    deTurckLieFib deTurckLieCoeffField deTurckLieCoeffField_toSection
    deTurckConnDiffCovDeriv connDiff_pairing_mdiffAt connDiffCovDerivOp dLaCovKernel_apply_extend)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

open DifferentialGeometry.Analysis.Spectral.MetricRealization
open DifferentialGeometry.PDE.DeTurck.RicciLinearization
  (realizedFam convexPerturbation realizedFam_inner_of_mem convexPerturbation_gFibreOpBound_abs
    abs_convex_smallConstant_lt_one realizedSmallSet)
open DifferentialGeometry.Analysis.Laplacian
  (metric_inner_self_nonneg metric_inner_cauchy_schwarz_sq)
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
  (covGrad connDiff_gFibreNorm_le_iteratedCovGrad_of_lt_one dLaBiContrFibFixedFrame_toModel)
open DifferentialGeometry.Geometry.Curvature
  (exists_covDerivConnDiff_gQuadratic_le_of_jetEnvelope
    abs_tensor_one_three_flat_eval_le_fibreNorm_mul_sqrt)
open DifferentialGeometry.Analysis.Sobolev.TensorHilbert
  (g0FlatCLM cotangentToDual_g0FlatCLM g0FlatCLM_apply)

open DifferentialGeometry.Analysis.Parabolic.TensorSpectral

section DLaGridBrick

open DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis.Spectral.DeTurck
open DifferentialGeometry.Analysis.Sobolev.TensorHilbert

set_option backward.isDefEq.respectTransparency false in
omit [NeZero (Module.finrank ℝ E)] in
theorem dLaLoweredCc_raise_repr (g₀ g₁ g_bg : SmoothRiemannianMetric I M) :
    cometricRaiseSlot0Field (I := I) (M := M) g₀ 2
        (dLaLoweredCc (I := I) (M := M) g₀ g₁ g_bg) =
      dLaKernelRaisedCc (I := I) (M := M) g₀ g₁ g_bg := by
  classical
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  apply ContinuousLinearMap.ext
  intro om
  apply Tensor0SSpace.toModel_injective
  apply ContinuousMultilinearMap.ext
  intro w
  have hexp_sub : ∀ (F G : SmoothCcTensor g₀ 1 3),
      Tensor0SSpace.toModel
        ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 3 I x from ((F - G).toSection x)) om) w =
      Tensor0SSpace.toModel
          ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 3 I x from (F.toSection x)) om) w -
        Tensor0SSpace.toModel
          ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 3 I x from (G.toSection x)) om) w := by
    intro F G
    rw [show ((F - G).toSection x) = F.toSection x - G.toSection x from by
      rw [SmoothCcTensor.toSection_sub]; rfl]
    rw [show ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 3 I x from
        (F.toSection x - G.toSection x)) om) =
        (show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 3 I x from F.toSection x) om -
          (show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 3 I x from G.toSection x) om from rfl]
    rw [Tensor0SSpace.toModel_sub, ContinuousMultilinearMap.sub_apply]
  have hexp_add : ∀ (F G : SmoothCcTensor g₀ 1 3),
      Tensor0SSpace.toModel
        ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 3 I x from ((F + G).toSection x)) om) w =
      Tensor0SSpace.toModel
          ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 3 I x from (F.toSection x)) om) w +
        Tensor0SSpace.toModel
          ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 3 I x from (G.toSection x)) om) w := by
    intro F G
    rw [show ((F + G).toSection x) = F.toSection x + G.toSection x from by
      rw [SmoothCcTensor.toSection_add]; rfl]
    rw [show ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 3 I x from
        (F.toSection x + G.toSection x)) om) =
        (show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 3 I x from F.toSection x) om +
          (show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 3 I x from G.toSection x) om from rfl]
    rw [Tensor0SSpace.toModel_add, ContinuousMultilinearMap.add_apply]
  have hA : ∀ (gc : SmoothRiemannianMetric I M),
      Tensor0SSpace.toModel
        ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 3 I x from
          (covGrad (I := I) (M := M) g₀ 1 2 (connDiffSection (I := I) gc g₀)).toSection x) om)
        w =
      cotangentToDual (I := I) (x := x) om
        (covDerivConnDiff (I := I) g₀ gc
          (smoothExtensionTangent (I := I) x (w 0))
          (smoothExtensionTangent (I := I) x (w 2))
          (smoothExtensionTangent (I := I) x (w 1)) x) := by
    intro gc
    have hb := connDiffSection_covGrad_eq_covDerivConnDiff (I := I) gc g₀
      (dLaCovectorExtensionSection (I := I) (M := M) g₀ x om)
      (smoothExtensionTangentSection (I := I) (M := M) x (w 0))
      (smoothExtensionTangentSection (I := I) (M := M) x (w 1))
      (smoothExtensionTangentSection (I := I) (M := M) x (w 2)) x
    rw [dLaCovectorExtensionSection_self (I := I) (M := M) g₀ x om] at hb
    rw [show smoothExtensionTangentSection (I := I) (M := M) x (w 0) x = w 0 from
      smoothExtensionTangent_eq (I := I) x (w 0)] at hb
    rw [show smoothExtensionTangentSection (I := I) (M := M) x (w 1) x = w 1 from
      smoothExtensionTangent_eq (I := I) x (w 1)] at hb
    rw [show smoothExtensionTangentSection (I := I) (M := M) x (w 2) x = w 2 from
      smoothExtensionTangent_eq (I := I) x (w 2)] at hb
    rw [show (Fin.cons (w 0) (Fin.cons (w 1) ![w 2]) : Fin 3 → TangentSpace I x) = w from by
      funext k
      refine Fin.cases rfl (fun j => ?_) k
      refine Fin.cases rfl (fun j' => ?_) j
      refine Fin.cases rfl (fun j'' => j''.elim0) j'] at hb
    rw [hb]
    rw [show covDerivConnDiff (I := I) g₀ gc
        (fun b => smoothExtensionTangentSection (I := I) (M := M) x (w 0) b)
        (fun b => smoothExtensionTangentSection (I := I) (M := M) x (w 2) b)
        (fun b => smoothExtensionTangentSection (I := I) (M := M) x (w 1) b) x =
      covDerivConnDiff (I := I) g₀ gc
        (smoothExtensionTangent (I := I) x (w 0))
        (smoothExtensionTangent (I := I) x (w 2))
        (smoothExtensionTangent (I := I) x (w 1)) x from rfl]
    exact (cotangentToDual_apply (I := I) (x := x) om _).symm
  have hswap0 : (Equiv.swap (0 : Fin 3) 2) 0 = 2 := Equiv.swap_apply_left 0 2
  have hswap1 : (Equiv.swap (0 : Fin 3) 2) 1 = 1 := by decide
  have hswap2 : (Equiv.swap (0 : Fin 3) 2) 2 = 0 := Equiv.swap_apply_right 0 2
  have hrot0 : (finRotate 3) (0 : Fin 3) = 1 := by decide
  have hrot1 : (finRotate 3) (1 : Fin 3) = 2 := by decide
  have hrot2 : (finRotate 3) (2 : Fin 3) = 0 := by decide
  have hQperm : ∀ (σ : Equiv.Perm (Fin 3)) (ga gb : SmoothRiemannianMetric I M),
      Tensor0SSpace.toModel
        ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 3 I x from
          (rsDomDomCongrSection (I := I) (M := M) g₀ 1 3 σ
            (dLaQuadCc (I := I) (M := M) g₀ ga gb)).toSection x) om) w =
      cotangentToDual (I := I) (x := x) om
        (PDE.DeTurck.connDiff (I := I) gb g₀ x
          (PDE.DeTurck.connDiff (I := I) ga g₀ x (w (σ 1)) (w (σ 2))) (w (σ 0))) := by
    intro σ ga gb
    rw [show ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 3 I x from
        (rsDomDomCongrSection (I := I) (M := M) g₀ 1 3 σ
          (dLaQuadCc (I := I) (M := M) g₀ ga gb)).toSection x) om) =
        ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 3 I x from
          tensorRS_domDomCongr σ ((dLaQuadCc (I := I) (M := M) g₀ ga gb).toSection x)) om) from by
      rw [rsDomDomCongrSection_toSection]]
    rw [toModel_rsDomDomCongr_apply (I := I) (M := M) σ
      ((dLaQuadCc (I := I) (M := M) g₀ ga gb).toSection x) om]
    rw [ContinuousMultilinearMap.domDomCongr_apply]
    exact dLaQuadCc_toModel (I := I) (M := M) g₀ ga gb x om (fun i => w (σ i))
  have hL : Tensor0SSpace.toModel
      ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 3 I x from
        (cometricRaiseSlot0Field (I := I) (M := M) g₀ 2
          (dLaLoweredCc (I := I) (M := M) g₀ g₁ g_bg)).toSection x) om) w =
      cotangentToDual (I := I) (x := x) om
        (connDiffCovDerivOp (I := I) g₁ g_bg x (w 0) (w 1) (w 2)) := by
    rw [show ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 3 I x from
        (cometricRaiseSlot0Field (I := I) (M := M) g₀ 2
          (dLaLoweredCc (I := I) (M := M) g₀ g₁ g_bg)).toSection x) om) =
        ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 3 I x from
          cometricRaiseSlot0Fib g₀ 2 x
            ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 4 I x from
              (dLaLoweredCc (I := I) (M := M) g₀ g₁ g_bg).toSection x)
              (unitTensor (I := I) (M := M) x))) om) from by
      rw [cometricRaiseSlot0Field_toSection]]
    rw [cometricRaiseSlot0Fib_clm_apply (I := I) g₀ 2 x _ om]
    rw [interiorProduct_toModel_eval_dla (I := I) (M := M) 3 x
      (inverseMetricSharpFib (I := I) g₀ x om) _ w]
    rw [show Tensor0SSpace.toModel
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 4 I x from
          (dLaLoweredCc (I := I) (M := M) g₀ g₁ g_bg).toSection x)
          (unitTensor (I := I) (M := M) x)) =
        unitModel (I := I) (M := M) g₀ 4 (dLaLoweredCc (I := I) (M := M) g₀ g₁ g_bg) x
        from rfl]
    rw [dLaLoweredCc_unitModel_apply (I := I) (M := M) g₀ g₁ g_bg x]
    rw [show (Fin.cons (show E from inverseMetricSharpFib (I := I) g₀ x om)
        (fun k => (show E from w k)) : Fin 4 → TangentSpace I x) 0 =
        inverseMetricSharpFib (I := I) g₀ x om from rfl]
    rw [show (Fin.cons (show E from inverseMetricSharpFib (I := I) g₀ x om)
        (fun k => (show E from w k)) : Fin 4 → TangentSpace I x) 1 = w 0 from rfl]
    rw [show (Fin.cons (show E from inverseMetricSharpFib (I := I) g₀ x om)
        (fun k => (show E from w k)) : Fin 4 → TangentSpace I x) 2 = w 1 from rfl]
    rw [show (Fin.cons (show E from inverseMetricSharpFib (I := I) g₀ x om)
        (fun k => (show E from w k)) : Fin 4 → TangentSpace I x) 3 = w 2 from rfl]
    rw [cotangentToDual_eq_inner_sharp_dla (I := I) (M := M) g₀ x om
      (connDiffCovDerivOp (I := I) g₁ g_bg x (w 0) (w 1) (w 2))]
  rw [hL]
  rw [dLaKernelRaisedCc]
  rw [hexp_add, hexp_sub, hexp_add, hexp_sub, hexp_sub, hexp_add, hexp_sub]
  rw [hA g₁, hA g_bg]
  rw [show Tensor0SSpace.toModel
      ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 3 I x from
        (dLaQuadCc (I := I) (M := M) g₀ g₁ g₁).toSection x) om) w =
      cotangentToDual (I := I) (x := x) om
        (PDE.DeTurck.connDiff (I := I) g₁ g₀ x
          (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (w 1) (w 2)) (w 0)) from
    dLaQuadCc_toModel (I := I) (M := M) g₀ g₁ g₁ x om w]
  rw [show Tensor0SSpace.toModel
      ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 3 I x from
        (dLaQuadCc (I := I) (M := M) g₀ g_bg g₁).toSection x) om) w =
      cotangentToDual (I := I) (x := x) om
        (PDE.DeTurck.connDiff (I := I) g₁ g₀ x
          (PDE.DeTurck.connDiff (I := I) g_bg g₀ x (w 1) (w 2)) (w 0)) from
    dLaQuadCc_toModel (I := I) (M := M) g₀ g_bg g₁ x om w]
  rw [hQperm (Equiv.swap (0 : Fin 3) 2) g₁ g₁, hQperm (Equiv.swap (0 : Fin 3) 2) g₁ g_bg,
    hQperm (finRotate 3) g₁ g₁, hQperm (finRotate 3) g₁ g_bg]
  rw [hswap0, hswap1, hswap2, hrot0, hrot1, hrot2]
  rw [dLaCovKernel_backgroundSplit (I := I) g₀ g₁ g_bg x (w 0) (w 1) (w 2)]
  have hcocy : ∀ u v : TangentSpace I x,
      PDE.DeTurck.connDiff (I := I) g₁ g_bg x u v =
        PDE.DeTurck.connDiff (I := I) g₁ g₀ x u v -
          PDE.DeTurck.connDiff (I := I) g_bg g₀ x u v :=
    fun u v => eq_sub_of_add_eq (connDiff_cocycle (I := I) g₁ g_bg g₀ x u v)
  rw [hcocy (w 1) (w 2)]
  rw [show PDE.DeTurck.connDiff (I := I) g₁ g₀ x
      (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (w 1) (w 2) -
        PDE.DeTurck.connDiff (I := I) g_bg g₀ x (w 1) (w 2)) (w 0) =
      PDE.DeTurck.connDiff (I := I) g₁ g₀ x
          (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (w 1) (w 2)) (w 0) -
        PDE.DeTurck.connDiff (I := I) g₁ g₀ x
          (PDE.DeTurck.connDiff (I := I) g_bg g₀ x (w 1) (w 2)) (w 0) from by
    rw [map_sub]
    rfl]
  rw [hcocy (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (w 1) (w 0)) (w 2)]
  rw [show PDE.DeTurck.connDiff (I := I) g₁ g_bg x (w 1)
      (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (w 2) (w 0)) =
      PDE.DeTurck.connDiff (I := I) g₁ g_bg x
        (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (w 2) (w 0)) (w 1) from
    PDE.DeTurck.connDiff_symm (I := I) g₁ g_bg x (w 1)
      (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (w 2) (w 0))]
  rw [hcocy (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (w 2) (w 0)) (w 1)]
  rw [cotangentToDual_map_sub_dla, cotangentToDual_map_sub_dla, cotangentToDual_map_add_dla,
    cotangentToDual_map_sub_dla, cotangentToDual_map_sub_dla, cotangentToDual_map_sub_dla,
    cotangentToDual_map_sub_dla]
  ring

set_option backward.isDefEq.respectTransparency false in
private noncomputable def dLaPerturbSharpEndoFib (g₀ : SmoothRiemannianMetric I M)
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

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
    [T2Space M] in
private lemma dLaPerturbSharpEndoFib_apply (g₀ : SmoothRiemannianMetric I M)
    (T : SmoothCcTensor g₀ 0 2) (x : M) (v : TangentSpace I x) :
    dLaPerturbSharpEndoFib (I := I) (M := M) g₀ T x v =
      metricSharp (I := I) g₀ x (ccTensorBilinSymm (I := I) g₀ T x v).toLinearMap := by
  rw [dLaPerturbSharpEndoFib, LinearMap.coe_toContinuousLinearMap']
  rfl

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
    [T2Space M] in
private lemma inner_dLaPerturbSharpEndoFib (g₀ : SmoothRiemannianMetric I M)
    (T : SmoothCcTensor g₀ 0 2) (x : M) (v w : TangentSpace I x) :
    g₀.inner x (dLaPerturbSharpEndoFib (I := I) (M := M) g₀ T x v) w =
      ccTensorBilinSymm (I := I) g₀ T x v w := by
  rw [dLaPerturbSharpEndoFib_apply]
  exact inner_metricSharp (I := I) g₀ x
    (ccTensorBilinSymm (I := I) g₀ T x v).toLinearMap w

set_option backward.isDefEq.respectTransparency false in
omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
private theorem dLaPerturbSharpEndoFib_contMDiff [SigmaCompactSpace M] (g₀ : SmoothRiemannianMetric I M)
    (T : SmoothCcTensor g₀ 0 2) :
    ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E)) ∞
      (fun x : M => TotalSpace.mk' (E →L[ℝ] E)
        (E := fun y : M => TangentSpace I y →L[ℝ] TangentSpace I y) x
        (dLaPerturbSharpEndoFib (I := I) (M := M) g₀ T x)) := by
  apply cotangentCov_clmSection_smooth_aux (I := I) (M := M)
    (F₂ := E) (V₂ := fun y : M => TangentSpace I y)
    (φ := fun x : M => dLaPerturbSharpEndoFib (I := I) (M := M) g₀ T x)
  intro Y
  have hcv : ∀ (α : M) (j : Fin (Module.finrank ℝ E)),
      ContMDiffOn I 𝓘(ℝ) ∞
        (fun b : M => (ccTensorBilinSymm (I := I) g₀ T b (Y b)).toLinearMap
          (chartBasisVecFiber (I := I) α j b))
        (chartAt H α).source := by
    intro α j
    have hB : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
        (fun b : M => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
          (E := fun y => TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ) b
          (ccTensorBilinSymm (I := I) g₀ T b)) :=
      ccTensorBilinSymm_contMDiff (I := I) g₀ T
    have hBasis : ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞
        (chartBasisVec (I := I) α j)
        (trivializationAt E (TangentSpace I) α).baseSet :=
      chartBasisVec_contMDiffOn (I := I) α j
    have happ : ContMDiffOn I (I.prod 𝓘(ℝ, ℝ)) ∞
        (fun b : M => (⟨b,
            ccTensorBilinSymm (I := I) g₀ T b (Y b) (chartBasisVecFiber (I := I) α j b)⟩ :
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
    TotalSpace.mk' E x (dLaPerturbSharpEndoFib (I := I) (M := M) g₀ T x (Y x))
  rw [dLaPerturbSharpEndoFib_apply]

noncomputable def dLaPerturbSharpEndoField (g₀ : SmoothRiemannianMetric I M)
    (T : SmoothCcTensor g₀ 0 2) :
    ContMDiffSection I (E →L[ℝ] E) ∞
      (fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x) where
  toFun := fun x : M => dLaPerturbSharpEndoFib (I := I) (M := M) g₀ T x
  contMDiff_toFun := dLaPerturbSharpEndoFib_contMDiff (I := I) (M := M) g₀ T

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
    [T2Space M] in
lemma unitModel_eq_ccTensorBilin_dla (g₀ : SmoothRiemannianMetric I M)
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

set_option backward.isDefEq.respectTransparency false in
omit [NeZero (Module.finrank ℝ E)] in
omit [BoundarylessManifold I M] in
lemma dLaSlotInsert_perturbSharp_eq_raise_symmS (g₀ : SmoothRiemannianMetric I M)
    (T : SmoothCcTensor g₀ 0 2) :
    endoSlotZeroCcTensor (I := I) (M := M) g₀ 0 (dLaPerturbSharpEndoField (I := I) (M := M) g₀ T) =
      cometricRaiseSlot0Field (I := I) (M := M) g₀ 0
        (domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 2) 1)
          (ccTensor02Symm (I := I) (M := M) g₀ T)) := by
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
        (endoSlotZeroCcTensor (I := I) (M := M) g₀ 0
          (dLaPerturbSharpEndoField (I := I) (M := M) g₀ T)).toSection x) om) w =
      ccTensorBilinSymm (I := I) g₀ T x (w 0)
        (inverseMetricSharpFib (I := I) g₀ x om) := by
    rw [show ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 1 I x from
          (endoSlotZeroCcTensor (I := I) (M := M) g₀ 0
            (dLaPerturbSharpEndoField (I := I) (M := M) g₀ T)).toSection x) om) =
        slotInsertEndoFib (I := I) (M := M) 1 0 x
          (dLaPerturbSharpEndoField (I := I) (M := M) g₀ T x) om from rfl]
    rw [slotInsertEndoFib_apply_eval]
    rw [toModel_om_single_eq_cotangentToDual_dla (I := I) (M := M) x om
      (Function.update w 0 (dLaPerturbSharpEndoField (I := I) (M := M) g₀ T x (w 0)))]
    rw [Function.update_self]
    rw [show (dLaPerturbSharpEndoField (I := I) (M := M) g₀ T x) =
        dLaPerturbSharpEndoFib (I := I) (M := M) g₀ T x from rfl]
    rw [cotangentToDual_eq_inner_sharp_dla (I := I) (M := M) g₀ x om
      (dLaPerturbSharpEndoFib (I := I) (M := M) g₀ T x (w 0))]
    rw [inner_dLaPerturbSharpEndoFib]
  rw [hLHS]
  rw [show ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 1 I x from
        (cometricRaiseSlot0Field (I := I) (M := M) g₀ 0
          (domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 2) 1)
            (ccTensor02Symm (I := I) (M := M) g₀ T))).toSection x) om) =
      ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 1 I x from
        cometricRaiseSlot0Fib g₀ 0 x
          ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from
            (domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 2) 1)
              (ccTensor02Symm (I := I) (M := M) g₀ T)).toSection x)
            (unitTensor (I := I) (M := M) x))) om) from rfl]
  rw [cometricRaiseSlot0Fib_clm_apply (I := I) g₀ 0 x _ om]
  rw [interiorProduct_toModel_eval_dla (I := I) (M := M) 1 x
    (inverseMetricSharpFib (I := I) g₀ x om) _ w]
  rw [show Tensor0SSpace.toModel
      ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from
        (domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 2) 1)
          (ccTensor02Symm (I := I) (M := M) g₀ T)).toSection x)
        (unitTensor (I := I) (M := M) x)) =
      unitModel (I := I) (M := M) g₀ 2
        (domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 2) 1)
          (ccTensor02Symm (I := I) (M := M) g₀ T)) x from rfl]
  rw [domDomCongrSection_unitModel (I := I) g₀ (Equiv.swap (0 : Fin 2) 1)
    (ccTensor02Symm (I := I) (M := M) g₀ T) x]
  rw [ContinuousMultilinearMap.domDomCongr_apply]
  rw [show (fun i : Fin 2 =>
      (Fin.cons (show E from inverseMetricSharpFib (I := I) g₀ x om)
        (fun k => (show E from w k)) : Fin 2 → E) ((Equiv.swap (0 : Fin 2) 1) i)) =
      (![(w 0 : E), (show E from inverseMetricSharpFib (I := I) g₀ x om)] : Fin 2 → E) from by
    funext i
    fin_cases i <;> rfl]
  rw [unitModel_eq_ccTensorBilin_dla (I := I) (M := M) g₀ (ccTensor02Symm (I := I) (M := M) g₀ T) x
    (w 0) (inverseMetricSharpFib (I := I) g₀ x om)]
  rw [ccTensorBilin_symmS (I := I) (M := M) g₀ T x]

noncomputable def dLaLoweredPerturbCc (g₀ : SmoothRiemannianMetric I M)
    (T : SmoothCcTensor g₀ 0 2) (g₁ g_bg : SmoothRiemannianMetric I M) :
    SmoothCcTensor g₀ 0 4 :=
  ccOperatorFieldComp (I := I) (M := M) g₀ 0 4 4
    (endoSlotZeroCcTensor (I := I) (M := M) g₀ 3 (dLaPerturbSharpEndoField (I := I) (M := M) g₀ T))
    (dLaLoweredCc (I := I) (M := M) g₀ g₁ g_bg)

noncomputable def dLaLoweredG1Cc (g₀ : SmoothRiemannianMetric I M)
    (T : SmoothCcTensor g₀ 0 2) (g₁ g_bg : SmoothRiemannianMetric I M) :
    SmoothCcTensor g₀ 0 4 :=
  dLaLoweredCc (I := I) (M := M) g₀ g₁ g_bg +
    dLaLoweredPerturbCc (I := I) (M := M) g₀ T g₁ g_bg

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
    [T2Space M] in
lemma unitModel_add_dla (g₀ : SmoothRiemannianMetric I M) (s : ℕ)
    (A B : SmoothCcTensor g₀ 0 s) (x : M) (m : Fin s → TangentSpace I x) :
    unitModel (I := I) (M := M) g₀ s (A + B) x m =
      unitModel (I := I) (M := M) g₀ s A x m + unitModel (I := I) (M := M) g₀ s B x m := by
  rw [unitModel, unitModel, unitModel]
  rw [show ((A + B).toSection x) = A.toSection x + B.toSection x from by
    rw [SmoothCcTensor.toSection_add]; rfl]
  rw [show ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from
      (A.toSection x + B.toSection x)) (unitTensor (I := I) (M := M) x)) =
      (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from A.toSection x)
          (unitTensor (I := I) (M := M) x) +
        (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from B.toSection x)
          (unitTensor (I := I) (M := M) x) from rfl]
  rw [Tensor0SSpace.toModel_add, ContinuousMultilinearMap.add_apply]

set_option backward.isDefEq.respectTransparency false in
omit [NeZero (Module.finrank ℝ E)] in
lemma dLaLoweredPerturbCc_unitModel_apply (g₀ : SmoothRiemannianMetric I M)
    (T : SmoothCcTensor g₀ 0 2) (g₁ g_bg : SmoothRiemannianMetric I M) (x : M)
    (m : Fin 4 → TangentSpace I x) :
    unitModel (I := I) (M := M) g₀ 4
        (dLaLoweredPerturbCc (I := I) (M := M) g₀ T g₁ g_bg) x m =
      ccTensorBilinSymm (I := I) g₀ T x
        (connDiffCovDerivOp (I := I) g₁ g_bg x (m 1) (m 2) (m 3)) (m 0) := by
  have hsec : unitModel (I := I) (M := M) g₀ 4
      (dLaLoweredPerturbCc (I := I) (M := M) g₀ T g₁ g_bg) x m =
      Tensor0SSpace.toModel
        (slotInsertEndoFib (I := I) (M := M) 4 0 x
          (dLaPerturbSharpEndoField (I := I) (M := M) g₀ T x)
          ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 4 I x from
            (dLaLoweredCc (I := I) (M := M) g₀ g₁ g_bg).toSection x)
            (unitTensor (I := I) (M := M) x))) m := by
    rw [unitModel]
    rw [show ((dLaLoweredPerturbCc (I := I) (M := M) g₀ T g₁ g_bg).toSection x)
        (unitTensor (I := I) (M := M) x) =
        slotInsertEndoFib (I := I) (M := M) 4 0 x
          (dLaPerturbSharpEndoField (I := I) (M := M) g₀ T x)
          ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 4 I x from
            (dLaLoweredCc (I := I) (M := M) g₀ g₁ g_bg).toSection x)
            (unitTensor (I := I) (M := M) x)) from by
      rw [dLaLoweredPerturbCc, appCcRS_toSection]
      rfl]
  rw [hsec]
  rw [slotInsertEndoFib_apply_eval]
  rw [show Tensor0SSpace.toModel
      ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 4 I x from
        (dLaLoweredCc (I := I) (M := M) g₀ g₁ g_bg).toSection x)
        (unitTensor (I := I) (M := M) x)) =
      unitModel (I := I) (M := M) g₀ 4 (dLaLoweredCc (I := I) (M := M) g₀ g₁ g_bg) x from rfl]
  rw [dLaLoweredCc_unitModel_apply (I := I) (M := M) g₀ g₁ g_bg x]
  rw [show (Function.update m 0
      (dLaPerturbSharpEndoField (I := I) (M := M) g₀ T x (m 0))) 0 =
      dLaPerturbSharpEndoField (I := I) (M := M) g₀ T x (m 0) from Function.update_self _ _ _]
  rw [show (Function.update m 0
      (dLaPerturbSharpEndoField (I := I) (M := M) g₀ T x (m 0))) 1 = m 1 from
    Function.update_of_ne (by decide) _ _]
  rw [show (Function.update m 0
      (dLaPerturbSharpEndoField (I := I) (M := M) g₀ T x (m 0))) 2 = m 2 from
    Function.update_of_ne (by decide) _ _]
  rw [show (Function.update m 0
      (dLaPerturbSharpEndoField (I := I) (M := M) g₀ T x (m 0))) 3 = m 3 from
    Function.update_of_ne (by decide) _ _]
  rw [g₀.symm x (connDiffCovDerivOp (I := I) g₁ g_bg x (m 1) (m 2) (m 3))
    (dLaPerturbSharpEndoField (I := I) (M := M) g₀ T x (m 0))]
  rw [show (dLaPerturbSharpEndoField (I := I) (M := M) g₀ T x) =
      dLaPerturbSharpEndoFib (I := I) (M := M) g₀ T x from rfl]
  rw [inner_dLaPerturbSharpEndoFib (I := I) (M := M) g₀ T x (m 0)
    (connDiffCovDerivOp (I := I) g₁ g_bg x (m 1) (m 2) (m 3))]
  exact ccTensorBilinSymm_symm (I := I) g₀ T x (m 0)
    (connDiffCovDerivOp (I := I) g₁ g_bg x (m 1) (m 2) (m 3))

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
    [T2Space M] in
private lemma rfns_neg_dla (g : SmoothRiemannianMetric I M) (r s : ℕ) (x : M)
    (v : TensorRSSpace r s I x) :
    riemannianFiberNormSq (I := I) (M := M) g r s x (-v) =
      riemannianFiberNormSq (I := I) (M := M) g r s x v := by
  rw [riemannianFiberNormSq_eq_tensorInnerPointwise (I := I) (M := M) g r s x (-v),
    riemannianFiberNormSq_eq_tensorInnerPointwise (I := I) (M := M) g r s x v]
  rw [TensorRSSpace.toModel_neg]
  rw [← neg_one_smul ℝ (TensorRSSpace.toModel (𝕜 := ℝ) (E := E) (I := I) (M := M)
        (r := r) (s := s) (x := x) v),
    tensorInnerPointwise_smul_left, tensorInnerPointwise_smul_right]
  ring

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
    [T2Space M] in
lemma rfns_smul_dla (g : SmoothRiemannianMetric I M) (r s : ℕ) (x : M)
    (c : ℝ) (v : TensorRSSpace r s I x) :
    riemannianFiberNormSq (I := I) (M := M) g r s x (c • v) =
      c ^ 2 * riemannianFiberNormSq (I := I) (M := M) g r s x v := by
  rw [riemannianFiberNormSq_eq_tensorInnerPointwise (I := I) (M := M) g r s x (c • v),
    riemannianFiberNormSq_eq_tensorInnerPointwise (I := I) (M := M) g r s x v]
  rw [TensorRSSpace.toModel_smul, tensorInnerPointwise_smul_left, tensorInnerPointwise_smul_right]
  ring

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
lemma rfns_iCG_sub_le_dla (g : SmoothRiemannianMetric I M) (r s : ℕ) (j : ℕ)
    (A B : SmoothCcTensor g r s) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g r (s + j) x
        ((iteratedCovGrad (I := I) g r s j (A - B)).toSection x) ≤
      2 * riemannianFiberNormSq (I := I) (M := M) g r (s + j) x
          ((iteratedCovGrad (I := I) g r s j A).toSection x) +
        2 * riemannianFiberNormSq (I := I) (M := M) g r (s + j) x
          ((iteratedCovGrad (I := I) g r s j B).toSection x) := by
  have hsec : (iteratedCovGrad (I := I) g r s j (A - B)).toSection x =
      (iteratedCovGrad (I := I) g r s j A).toSection x +
        (-(iteratedCovGrad (I := I) g r s j B).toSection x) := by
    rw [sub_eq_add_neg, iteratedCovGrad_add, iteratedCovGrad_neg, SmoothCcTensor.toSection_add]
    rw [show ((iteratedCovGrad (I := I) g r s j A).toSection +
        (-iteratedCovGrad (I := I) g r s j B).toSection) x =
        (iteratedCovGrad (I := I) g r s j A).toSection x +
          (-iteratedCovGrad (I := I) g r s j B).toSection x from rfl]
    rw [SmoothCcTensor.toSection_neg]
    rfl
  rw [hsec]
  refine le_trans (riemannianFiberNormSq_add_le (I := I) (M := M) g r (s + j) x _ _) ?_
  rw [rfns_neg_dla (I := I) (M := M) g r (s + j) x]

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
lemma rfns_iCG_add_le_dla (g : SmoothRiemannianMetric I M) (r s : ℕ) (j : ℕ)
    (A B : SmoothCcTensor g r s) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g r (s + j) x
        ((iteratedCovGrad (I := I) g r s j (A + B)).toSection x) ≤
      2 * riemannianFiberNormSq (I := I) (M := M) g r (s + j) x
          ((iteratedCovGrad (I := I) g r s j A).toSection x) +
        2 * riemannianFiberNormSq (I := I) (M := M) g r (s + j) x
          ((iteratedCovGrad (I := I) g r s j B).toSection x) := by
  have hsec : (iteratedCovGrad (I := I) g r s j (A + B)).toSection x =
      (iteratedCovGrad (I := I) g r s j A).toSection x +
        (iteratedCovGrad (I := I) g r s j B).toSection x := by
    rw [iteratedCovGrad_add, SmoothCcTensor.toSection_add]
    rfl
  rw [hsec]
  exact riemannianFiberNormSq_add_le (I := I) (M := M) g r (s + j) x _ _

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem exists_fixedField_rfns_jet_dla (g₀ : SmoothRiemannianMetric I M)
    (r s : ℕ) (F : SmoothCcTensor g₀ r s) :
    ∃ c : ℕ → ℝ, (∀ j, 0 ≤ c j) ∧ ∀ (j : ℕ) (x : M),
      riemannianFiberNormSq (I := I) (M := M) g₀ r (s + j) x
        ((iteratedCovGrad (I := I) g₀ r s j F).toSection x) ≤ c j := by
  have hex : ∀ j : ℕ, ∃ c : ℝ, 0 ≤ c ∧ ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g₀ r (s + j) x
        ((iteratedCovGrad (I := I) g₀ r s j F).toSection x) ≤ c :=
    fun j => exists_bound_riemannianFiberNormSq_smoothCcTensor (I := I) (M := M) g₀ r (s + j)
      (iteratedCovGrad (I := I) g₀ r s j F)
  choose c hc_nn hc using hex
  exact ⟨c, hc_nn, fun j x => hc j x⟩

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
    [T2Space M] in
lemma g1_inner_gInvRaisedEndo_left_dla (g₀ g₁ : SmoothRiemannianMetric I M) (x : M)
    (v w : TangentSpace I x) :
    g₁.inner x (metricComparisonEndo (I := I) g₀ g₁ x v) w = g₀.inner x v w := by
  rw [gInvRaisedEndo_apply]
  rw [inverseMetricSharpFib_inner (I := I) g₁ x (g0FlatCLM (I := I) g₀ x v) w]
  rw [show cotangentToDualLinear (I := I) (x := x) (g0FlatCLM (I := I) g₀ x v) w =
      cotangentToDual (I := I) (x := x) (g0FlatCLM (I := I) g₀ x v) w from rfl]
  rw [cotangentToDual_g0FlatCLM]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
    [T2Space M] in
private lemma g0_inner_inverseMetricSharp_mixed_dla (g₀ g₁ : SmoothRiemannianMetric I M) (x : M)
    (om : Tensor0SSpace 1 I x) (v : TangentSpace I x) :
    g₀.inner x (inverseMetricSharpFib (I := I) g₁ x om) v =
      cotangentToDual (I := I) (x := x) om (metricComparisonEndo (I := I) g₀ g₁ x v) := by
  rw [show cotangentToDual (I := I) (x := x) om (metricComparisonEndo (I := I) g₀ g₁ x v) =
      cotangentToDualLinear (I := I) (x := x) om (metricComparisonEndo (I := I) g₀ g₁ x v) from rfl]
  rw [← inverseMetricSharpFib_inner (I := I) g₁ x om (metricComparisonEndo (I := I) g₀ g₁ x v)]
  rw [g₁.symm x (inverseMetricSharpFib (I := I) g₁ x om) (metricComparisonEndo (I := I) g₀ g₁ x v)]
  rw [g1_inner_gInvRaisedEndo_left_dla (I := I) (M := M) g₀ g₁ x v
    (inverseMetricSharpFib (I := I) g₁ x om)]
  rw [g₀.symm x v (inverseMetricSharpFib (I := I) g₁ x om)]

set_option backward.isDefEq.respectTransparency false in
omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
lemma sharpFlatEndoCc_eq_slotInsert_fullRaised_dla (g₀ g₁ : SmoothRiemannianMetric I M) :
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
  rw [toModel_om_single_eq_cotangentToDual_dla (I := I) (M := M) x om
    (Function.update m 0 (fullRaisedEndoField (I := I) (M := M) g₀ g₁ x (m 0)))]
  rw [Function.update_self]
  rw [toModel_om_single_eq_cotangentToDual_dla (I := I) (M := M) x
    ((g0FlatCLM (I := I) g₀ x) (inverseMetricSharpFib (I := I) g₁ x om)) m]
  rw [cotangentToDual_g0FlatCLM]
  rw [g0_inner_inverseMetricSharp_mixed_dla (I := I) (M := M) g₀ g₁ x om (m 0)]
  rw [fullRaisedEndoField_apply]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [BoundarylessManifold I M]
    in
private lemma fullRaisedEndoField_diff_split_dla (g₀ g₁ : SmoothRiemannianMetric I M) :
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
private lemma slotInsertEndoCc_add_endo_dla (g₀ : SmoothRiemannianMetric I M) (s : ℕ)
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
private lemma endoCovariantDerivative_fullRaised_id_eq_zero_dla (g₀ : SmoothRiemannianMetric I M)
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
private lemma covGrad_slotInsert_fullRaised_id_eq_zero_dla (g₀ : SmoothRiemannianMetric I M) :
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
    exact endoCovariantDerivative_fullRaised_id_eq_zero_dla (I := I) (M := M) g₀ Y x (m 0)]
  rw [show slotInsertEndoFib (I := I) (M := M) (0 + 1) 0 x
        (0 : TangentSpace I x →L[ℝ] TangentSpace I x) = 0 from by
    rw [show (0 : TangentSpace I x →L[ℝ] TangentSpace I x) =
        (0 : ℝ) • (0 : TangentSpace I x →L[ℝ] TangentSpace I x) from (zero_smul ℝ _).symm,
      slotInsertEndoFib_smul_left, zero_smul]]
  simp [SmoothCcTensor.toSection_zero]

omit [NeZero (Module.finrank ℝ E)] in
private lemma iteratedCovGrad_slotInsert_fullRaised_id_succ_eq_zero_dla
    (g₀ : SmoothRiemannianMetric I M) (m : ℕ) :
    iteratedCovGrad (I := I) g₀ 1 1 (m + 1)
        (endoSlotZeroCcTensor (I := I) (M := M) g₀ 0
          (fullRaisedEndoField (I := I) (M := M) g₀ g₀)) = 0 := by
  induction m with
  | zero =>
      rw [iteratedCovGrad_succ, iteratedCovGrad_zero]
      exact covGrad_slotInsert_fullRaised_id_eq_zero_dla (I := I) (M := M) g₀
  | succ m' ih =>
      rw [iteratedCovGrad_succ, ih, covGrad_zero]

theorem exists_rfns_iteratedCovGrad_sharpFlatEndoCc_tgrid_dla
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
    rw [sharpFlatEndoCc_eq_slotInsert_fullRaised_dla (I := I) (M := M) g₀ g₁,
      fullRaisedEndoField_diff_split_dla (I := I) (M := M) g₀ g₁,
      slotInsertEndoCc_add_endo_dla (I := I) (M := M) g₀ 0]
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
        rw [iteratedCovGrad_slotInsert_fullRaised_id_succ_eq_zero_dla (I := I) (M := M) g₀ m]
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

theorem exists_rfns_iteratedCovGrad_connDiffSection_tgrid_dla
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
          CA j * antidiagonalTupleGridPartialSum
            (fun j' => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j') x
              ((iteratedCovGrad (I := I) g₀ 0 2 j' T).toSection x)) (j + 2) := by
  classical
  obtain ⟨S, hS_nn, hS⟩ := exists_rfns_iteratedCovGrad_sharpFlatEndoCc_tgrid_dla
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
  set G : ℝ := antidiagonalTupleGridPartialSum b (j + 2) with hG_def
  have hG_nn : 0 ≤ G := dLaGridWin_nonneg b hb (j + 2)
  have hcell : ∀ i ∈ Finset.range (j + 1), ∀ l ∈ Finset.range (j + 1 - i),
      riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + i) x
          ((iteratedCovGrad (I := I) g₀ 1 2 i (raisedKoszul (I := I) g₀ g₁)).toSection x) *
        riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + l) x
          ((iteratedCovGrad (I := I) g₀ 1 1 l (sharpFlatEndoCc (I := I) g₀ g₁)).toSection x) ≤
      (10 * S l) * G := by
    intro i hi l hl
    have h1 := rfns_iteratedCovGrad_raisedKoszul_pointwise_le (I := I) (M := M) g₀ g₁ T htie i x
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
      refine grid_le_dLaGridWin b hb ?_
      rw [Finset.mem_range] at hi hl
      omega
    calc riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + i) x
            ((iteratedCovGrad (I := I) g₀ 1 2 i (raisedKoszul (I := I) g₀ g₁)).toSection x) *
          riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + l) x
            ((iteratedCovGrad (I := I) g₀ 1 1 l (sharpFlatEndoCc (I := I) g₀ g₁)).toSection x)
        ≤ (10 * b (i + 1)) * (S l * Combinatorics.antidiagonalTupleGrid b l) :=
          mul_le_mul h1 h2 h2_nn (by
            have := hb (i + 1)
            positivity)
      _ = (10 * S l) * (b (i + 1) * Combinatorics.antidiagonalTupleGrid b l) := by ring
      _ ≤ (10 * S l) * Combinatorics.antidiagonalTupleGrid b (l + (i + 1)) := by
          refine mul_le_mul_of_nonneg_left hb_le_grid ?_
          have := hS_nn l
          positivity
      _ ≤ (10 * S l) * G := by
          refine mul_le_mul_of_nonneg_left hgrid_le_G ?_
          have := hS_nn l
          positivity
  refine le_trans (riemannianFiberNormSq_iteratedCovGrad_connDiffSection_diagonalProductGrid_le
    (I := I) (M := M) g₀ g₁ j x) ?_
  have hsum : ∑ i ∈ Finset.range (j + 1),
      riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + i) x
          ((iteratedCovGrad (I := I) g₀ 1 2 i (raisedKoszul (I := I) g₀ g₁)).toSection x) *
        ∑ l ∈ Finset.range (j + 1 - i),
          riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + l) x
            ((iteratedCovGrad (I := I) g₀ 1 1 l
              (sharpFlatEndoCc (I := I) g₀ g₁)).toSection x) ≤
      ∑ i ∈ Finset.range (j + 1), (10 * ∑ l ∈ Finset.range (j + 1 - i), S l) * G := by
    refine Finset.sum_le_sum fun i hi => ?_
    rw [Finset.mul_sum]
    have hrw : (10 * ∑ l ∈ Finset.range (j + 1 - i), S l) * G =
        ∑ l ∈ Finset.range (j + 1 - i), (10 * S l) * G := by
      rw [Finset.mul_sum, Finset.sum_mul]
    rw [hrw]
    exact Finset.sum_le_sum fun l hl => hcell i hi l hl
  refine le_trans (mul_le_mul_of_nonneg_left hsum (appCcGdiag_nonneg (E := E) j)) ?_
  rw [← Finset.sum_mul, ← mul_assoc]

end DLaGridBrick

end DifferentialGeometry.Analysis.Sobolev

end
