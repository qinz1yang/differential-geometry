import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.RicciDeTurckMetricArmCoeffField
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.ConnectionDifferenceFibreBound
import DifferentialGeometry.Analysis.Sobolev.Embedding.SobolevEmbeddingReverseHebeyToHs
import DifferentialGeometry.Analysis.Sobolev.Embedding.SobolevEmbeddingCmOrderDropping
import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.PointwiseToL2Packaging
import DifferentialGeometry.Geometry.Connection.TensorNabla.SlotInsertCovariantNaturality
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.SecondBianchi
import DifferentialGeometry.Analysis.Sobolev.GagliardoNirenbergLpFiberNorm
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.RiemannianFiberNormSq.RiemannianFiberNormSqNormBridge
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.IteratedCovGradFibreNormPermutationInvariance
import DifferentialGeometry.Analysis.Sobolev.AntidiagonalTupleProductGrid

noncomputable section

set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators

namespace DifferentialGeometry
namespace Integral
namespace Connection

open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Analysis.Laplacian
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.Analysis.Sobolev.TensorHilbert
open TensorRSNabla
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization (gFibreOpBound ccTensorBilinSymm)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

set_option linter.unusedSectionVars false in
theorem tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (S : SmoothCcTensor g r s) :
    tensorL2Norm (I := I) (M := M) g r s S.toFun ^ 2 =
      ∫ x, riemannianFiberNormSq (I := I) (M := M) g r s x (S.toSection x)
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
  have hfun : S.toFun = fun x => TensorRSSpace.toModel (𝕜 := ℝ) (E := E) (I := I) (M := M)
      (r := r) (s := s) (x := x) (S.toSection x) := rfl
  rw [hfun]
  exact tensorL2Norm_sq_eq_integral_riemannianFiberNormSq (I := I) (M := M) g r s _

set_option linter.unusedSectionVars false in
theorem norm_le_of_pointwise_fiberNormSq_bound_rs
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (C : SmoothCcTensor g r s) (B : ℝ)
    (hpt : ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g r s x (C.toSection x) ≤ B) :
    ‖C‖ ^ 2 ≤ B * (riemannianVolumeMeasure (I := I) (M := M) g Set.univ).toReal := by
  classical
  haveI : IsFiniteMeasure (riemannianVolumeMeasure (I := I) (M := M) g) :=
    riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace (I := I) (M := M) g
  rw [SmoothCcTensor.norm_def (I := I) (M := M) C,
    tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs (I := I) (M := M) g r s C]
  have hint : MeasureTheory.Integrable
      (fun x => riemannianFiberNormSq (I := I) (M := M) g r s x (C.toSection x))
      (riemannianVolumeMeasure (I := I) (M := M) g) :=
    integrable_riemannianFiberNormSq_toSection (I := I) (M := M) g r s C
  calc ∫ x, riemannianFiberNormSq (I := I) (M := M) g r s x (C.toSection x)
          ∂(riemannianVolumeMeasure (I := I) (M := M) g)
      ≤ ∫ _x, B ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
        refine MeasureTheory.integral_mono hint (MeasureTheory.integrable_const B)
          (fun x => hpt x)
    _ = B * (riemannianVolumeMeasure (I := I) (M := M) g Set.univ).toReal := by
        rw [MeasureTheory.integral_const, smul_eq_mul,
          MeasureTheory.measureReal_def, mul_comm]

set_option linter.unusedSectionVars false in
theorem normSq_le_integral_of_pointwise_fiberNormSq_le_rs
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (C : SmoothCcTensor g r s) (F : M → ℝ)
    (hF_int : MeasureTheory.Integrable F (riemannianVolumeMeasure (I := I) (M := M) g))
    (hpt : ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g r s x (C.toSection x) ≤ F x) :
    ‖C‖ ^ 2 ≤ ∫ x, F x ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
  classical
  haveI : IsFiniteMeasure (riemannianVolumeMeasure (I := I) (M := M) g) :=
    riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace (I := I) (M := M) g
  rw [SmoothCcTensor.norm_def (I := I) (M := M) C,
    tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs (I := I) (M := M) g r s C]
  have hint : MeasureTheory.Integrable
      (fun x => riemannianFiberNormSq (I := I) (M := M) g r s x (C.toSection x))
      (riemannianVolumeMeasure (I := I) (M := M) g) :=
    integrable_riemannianFiberNormSq_toSection (I := I) (M := M) g r s C
  exact MeasureTheory.integral_mono hint hF_int (fun x => hpt x)

set_option linter.unusedSectionVars false in
theorem riemannianFiberNormSq_gInvDiffSlotCoeff_le
    (g₀ g₁ : SmoothRiemannianMetric I M) (T : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ : δ < 1 / 2) (hδ0 : 0 ≤ δ)
    (h : ∀ y v w, g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm g₀ T y v w)
    (hbound : gFibreOpBound (I := I) g₀ (ccTensorBilinSymm g₀ T) δ) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x
        ((gInvDiffSlotCoeff (I := I) g₀ g₁).toSection x) ≤
      ((Module.finrank ℝ E : ℝ)) ^ 2 := by
  have hδ1 : δ < 1 := by linarith
  have hbase := riemannianFiberNormSq_gInvDiffSlotEndo_le (I := I) (M := M) g₀ g₁
    (ccTensorBilinSymm g₀ T) (fun y v w => h y v w) hδ1 hδ0 hbound x
  have hcoeff : (0 : ℝ) < 1 - δ := by linarith
  have hratio : δ / (1 - δ) ≤ 1 := by
    rw [div_le_one hcoeff]; linarith
  have hratio0 : 0 ≤ δ / (1 - δ) := div_nonneg hδ0 (by linarith)
  have hfr0 : (0 : ℝ) ≤ (Module.finrank ℝ E : ℝ) := Nat.cast_nonneg _
  have hmono : ((Module.finrank ℝ E : ℝ) * (δ / (1 - δ))) ^ 2 ≤
      ((Module.finrank ℝ E : ℝ)) ^ 2 := by
    have : (Module.finrank ℝ E : ℝ) * (δ / (1 - δ)) ≤ (Module.finrank ℝ E : ℝ) := by
      calc (Module.finrank ℝ E : ℝ) * (δ / (1 - δ))
          ≤ (Module.finrank ℝ E : ℝ) * 1 := by
            exact mul_le_mul_of_nonneg_left hratio hfr0
        _ = (Module.finrank ℝ E : ℝ) := by rw [mul_one]
    nlinarith [mul_nonneg hfr0 hratio0]
  calc riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x
          ((gInvDiffSlotCoeff (I := I) g₀ g₁).toSection x)
      = riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x
          (show TensorRSSpace 2 2 I x from
            TensorRSSpace.ofCLM (gInvDiffSlotEndo (I := I) g₀ g₁ x)) := by rfl
    _ ≤ ((Module.finrank ℝ E : ℝ) * (δ / (1 - δ))) ^ 2 := hbase
    _ ≤ ((Module.finrank ℝ E : ℝ)) ^ 2 := hmono

set_option backward.isDefEq.respectTransparency false in
def gInvDiffRaisedEndoField (g₀ g₁ : SmoothRiemannianMetric I M) :
    ContMDiffSection I (E →L[ℝ] E) ∞
      (fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x) where
  toFun := fun x : M => gInvDiffRaisedEndo (I := I) g₀ g₁ x
  contMDiff_toFun := gInvDiffRaisedEndo_contMDiff (I := I) g₀ g₁

set_option backward.isDefEq.respectTransparency false in
set_option linter.unusedSectionVars false in
theorem gInvDiffSlotCoeff_eq_slotInsertEndoCc (g₀ g₁ : SmoothRiemannianMetric I M) :
    gInvDiffSlotCoeff (I := I) g₀ g₁ =
      slotInsertEndoCc (I := I) (M := M) g₀ 1 (gInvDiffRaisedEndoField (I := I) g₀ g₁) := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option linter.unusedSectionVars false in
private theorem inverseMetricSharpFib_g0FlatY_contMDiff
    (g₀ g₁ : SmoothRiemannianMetric I M)
    (Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun b : M => TotalSpace.mk' E (E := fun z : M => TangentSpace I z) b
        (inverseMetricSharpFib (I := I) g₁ b (g0FlatCLM (I := I) g₀ b (Y b)))) := by
  have hsharpY : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun b : M => TotalSpace.mk' E (E := fun z : M => TangentSpace I z) b
        (metricSharp (I := I) g₁ b ((g₀.inner b (Y b)).toLinearMap))) := by
    apply metricSharp_contMDiff_total (I := I) g₁
    intro γ j
    exact metricFlat_chartComponent_contMDiffOn (I := I) g₀ Y γ j
  refine hsharpY.congr (fun x => ?_)
  rw [inverseMetricSharpFib_g0FlatCLM_eq_metricSharp (I := I) g₀ g₁ x (Y x)]

set_option linter.unusedSectionVars false in
private theorem cotangent_g0FlatY_mdiffAtCotangent
    (g₀ : SmoothRiemannianMetric I M)
    (Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) :
    MDiffAtCotangent (I := I)
      (fun b : M => cotangentToCLM (I := I) (g0FlatCLM (I := I) g₀ b (Y b))) x := by
  have heq : (fun b : M => cotangentToCLM (I := I) (g0FlatCLM (I := I) g₀ b (Y b))) =
      metricFlat (I := I) g₀ (fun b : M => Y b) := by
    funext b
    apply ContinuousLinearMap.ext
    intro w
    rw [metricFlat_apply]
    change cotangentToDual (I := I) (g0FlatCLM (I := I) g₀ b (Y b)) w = _
    exact cotangentToDual_g0FlatCLM (I := I) g₀ b (Y b) w
  rw [heq]
  exact metricFlat_mdiff (I := I) g₀ (Y.contMDiff.mdifferentiableAt (by norm_num))

set_option backward.isDefEq.respectTransparency false in
set_option linter.unusedSectionVars false in
private theorem endoCov_gInvDiffRaisedField_apply
    (g₀ g₁ : SmoothRiemannianMetric I M)
    (Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) (v : TangentSpace I x) :
    ((endoCovariantDerivative (I := I) (M := M) g₀)
        (gInvDiffRaisedEndoField (I := I) g₀ g₁) x v) (Y x) =
      - PDE.DeTurck.connDiff (I := I) g₁ g₀ x (gInvRaisedEndo (I := I) g₀ g₁ x (Y x)) v
      + inverseMetricSharpFib (I := I) g₁ x
          (dualToCotangent (I := I)
            (-(cotangentToCLM (I := I) (g0FlatCLM (I := I) g₀ x (Y x))).comp
                ((PDE.DeTurck.connDiff (I := I) g₁ g₀ x).flip v)).toLinearMap) := by
  classical
  set β : Π b : M, Tensor0SSpace 1 I b := fun b : M => g0FlatCLM (I := I) g₀ b (Y b) with hβdef
  set gradY : TangentSpace I x := (LeviCivita (I := I) g₀).toFun (fun y : M => Y y) x v with hgradY
  have hYmd := Y.mdifferentiableAt (x := x)
  have hβ : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (fun y : M => TotalSpace.mk' E (E := fun z : M => TangentSpace I z) y
        ((inverseMetricSharpFib (I := I) g₁ y) (β y))) x :=
    ((inverseMetricSharpFib_g0FlatY_contMDiff (I := I) g₀ g₁ Y) x).mdifferentiableAt
      (by norm_num)
  have hβ₀ : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (fun y : M => TotalSpace.mk' E (E := fun z : M => TangentSpace I z) y
        ((inverseMetricSharpFib (I := I) g₀ y) (β y))) x := by
    have hcong : (fun y : M => TotalSpace.mk' E (E := fun z : M => TangentSpace I z) y
        ((inverseMetricSharpFib (I := I) g₀ y) (β y))) =
        (fun y : M => TotalSpace.mk' E (E := fun z : M => TangentSpace I z) y (Y y)) := by
      funext y
      rw [hβdef]
      rw [inverseMetricSharpFib_g0FlatCLM (I := I) g₀ y (Y y)]
    rw [hcong]
    exact Y.mdifferentiableAt (x := x)
  have hβcot : MDiffAtCotangent (I := I) (fun b : M => cotangentToCLM (I := I) (β b)) x :=
    cotangent_g0FlatY_mdiffAtCotangent (I := I) g₀ Y x
  have hsharpY_mdiff :=
    ((inverseMetricSharpFib_g0FlatY_contMDiff (I := I) g₀ g₁ Y) x).mdifferentiableAt
      (by norm_num)
  have hΛapply : (gInvDiffRaisedEndoField (I := I) g₀ g₁ : Π y : M, _) =
      fun y : M => gInvDiffRaisedEndo (I := I) g₀ g₁ y := rfl
  have hLeibniz := endoCovariantDerivative_apply (I := I) (M := M) g₀
    (gInvDiffRaisedEndoField (I := I) g₀ g₁) Y x v
  rw [hLeibniz]
  have hΛval : ∀ y : M, (gInvDiffRaisedEndoField (I := I) g₀ g₁ y) (Y y) =
      (inverseMetricSharpFib (I := I) g₁ y) (β y) - Y y := by
    intro y
    rw [hβdef]
    change gInvDiffRaisedEndo (I := I) g₀ g₁ y (Y y) = _
    rw [gInvDiffRaisedEndo_apply]
  have hΛx : (gInvDiffRaisedEndoField (I := I) g₀ g₁ x) gradY =
      (inverseMetricSharpFib (I := I) g₁ x) (g0FlatCLM (I := I) g₀ x gradY) - gradY := by
    change gInvDiffRaisedEndo (I := I) g₀ g₁ x gradY = _
    rw [gInvDiffRaisedEndo_apply]
  have hsplit : (LeviCivita (I := I) g₀) (fun y : M => (gInvDiffRaisedEndoField (I := I) g₀ g₁ y) (Y y)) x v =
      (LeviCivita (I := I) g₀).toFun (fun y : M => (inverseMetricSharpFib (I := I) g₁ y) (β y)) x v
        - (LeviCivita (I := I) g₀).toFun (fun y : M => Y y) x v := by
    have hfun : (fun y : M => (gInvDiffRaisedEndoField (I := I) g₀ g₁ y) (Y y)) =
        (fun y : M => (inverseMetricSharpFib (I := I) g₁ y) (β y)) - (fun y : M => Y y) := by
      funext y
      rw [Pi.sub_apply, hΛval y]
    have hop : (LeviCivita (I := I) g₀).toFun
          (fun y : M => (gInvDiffRaisedEndoField (I := I) g₀ g₁ y) (Y y)) x =
        (LeviCivita (I := I) g₀).toFun
            (fun y : M => (inverseMetricSharpFib (I := I) g₁ y) (β y)) x
          - (LeviCivita (I := I) g₀).toFun (fun y : M => Y y) x := by
      rw [hfun]
      exact cov_toFun_sub (LeviCivita (I := I) g₀) hsharpY_mdiff hYmd
    have hopv := congrArg (fun L : TangentSpace I x →L[ℝ] TangentSpace I x => L v) hop
    simpa using hopv
  rw [hsplit]
  have hcross := covGrad_inverseMetricSharpFib_cross (I := I) g₀ g₁ β hβ hβcot v
  rw [hcross]
  have hT1 : inverseMetricSharpFib (I := I) g₁ x
        (dualToCotangent (I := I)
          ((cotangentCov (LeviCivita (I := I) g₀)).toFun
            (fun b : M => cotangentToCLM (I := I) (β b)) x v)) =
      inverseMetricSharpFib (I := I) g₁ x (g0FlatCLM (I := I) g₀ x gradY) := by
    have hB := inverseMetricSharpField_covGrad_eq_zero (I := I) g₀ β hβ₀ v
    have hseceq : (fun b : M => (inverseMetricSharpFib (I := I) g₀ b) (β b)) =
        (fun y : M => Y y) := by
      funext y
      rw [hβdef, inverseMetricSharpFib_g0FlatCLM (I := I) g₀ y (Y y)]
    rw [hseceq] at hB
    have hflat : g0FlatCLM (I := I) g₀ x gradY =
        dualToCotangent (I := I)
          ((cotangentCov (LeviCivita (I := I) g₀)).toFun
            (fun b : M => cotangentToCLM (I := I) (β b)) x v) := by
      rw [hgradY, hB,
        Analysis.Parabolic.TensorSpectral.g0FlatCLM_inverseMetricSharpFib (I := I) g₀ x _]
    rw [hflat]
  rw [hT1, hΛx]
  rw [show (inverseMetricSharpFib (I := I) g₁ x) (β x) =
      gInvRaisedEndo (I := I) g₀ g₁ x (Y x) from by
    rw [hβdef, gInvRaisedEndo_apply]]
  abel

set_option backward.isDefEq.respectTransparency false in
set_option linter.unusedSectionVars false in
private theorem endoCompSection_contMDiff
    (A B : ContMDiffSection I (E →L[ℝ] E) ∞
      (fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x)) :
    ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E)) ∞
      (fun x : M => TotalSpace.mk' (E →L[ℝ] E)
        (E := fun z : M => TangentSpace I z →L[ℝ] TangentSpace I z) x
        ((A x).comp (B x))) := by
  apply contMDiff_clm_section_of_pointwise (I := I) (M := M)
    (F₁ := E) (V₁ := fun z : M => TangentSpace I z)
    (F₂ := E) (V₂ := fun z : M => TangentSpace I z)
    (φ := fun x => (A x).comp (B x))
  intro Y
  have hBY : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun y : M => TotalSpace.mk' E (E := fun z : M => TangentSpace I z) y ((B y) (Y y))) :=
    endoApplySection_contMDiff (I := I) (M := M) B Y
  let BY : Cₛ^∞⟮I; E, (fun y : M => TangentSpace I y)⟯ := ⟨fun y : M => (B y) (Y y), hBY⟩
  have hABY : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun y : M => TotalSpace.mk' E (E := fun z : M => TangentSpace I z) y ((A y) (BY y))) :=
    endoApplySection_contMDiff (I := I) (M := M) A BY
  refine hABY.congr (fun x => ?_)
  rfl

set_option backward.isDefEq.respectTransparency false in
def endoCompField (A B : ContMDiffSection I (E →L[ℝ] E) ∞
      (fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x)) :
    ContMDiffSection I (E →L[ℝ] E) ∞
      (fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x) where
  toFun := fun x : M => (A x).comp (B x)
  contMDiff_toFun := endoCompSection_contMDiff (I := I) (M := M) A B

set_option linter.unusedSectionVars false in
@[simp] lemma endoCompField_apply
    (A B : ContMDiffSection I (E →L[ℝ] E) ∞
      (fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x)) (x : M) :
    (endoCompField (I := I) (M := M) A B x) = (A x).comp (B x) := rfl

set_option backward.isDefEq.respectTransparency false in
set_option linter.unusedSectionVars false in
theorem endoCovariantDerivative_comp
    (g₀ : SmoothRiemannianMetric I M)
    (A B : ContMDiffSection I (E →L[ℝ] E) ∞
      (fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x))
    (x : M) (v : TangentSpace I x) :
    ((endoCovariantDerivative (I := I) (M := M) g₀)
        (endoCompField (I := I) (M := M) A B) x v) =
      ((endoCovariantDerivative (I := I) (M := M) g₀) A x v).comp (B x) +
        (A x).comp ((endoCovariantDerivative (I := I) (M := M) g₀) B x v) := by
  classical
  apply ContinuousLinearMap.ext
  intro a
  obtain ⟨Y, hYx⟩ := ContMDiffSection.exists_eq_at (I := I) (n := (⊤ : ℕ∞))
    (F := E) (V := (TangentSpace I : M → Type _)) x a
  have hBY : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun y : M => TotalSpace.mk' E (E := fun z : M => TangentSpace I z) y ((B y) (Y y))) :=
    endoApplySection_contMDiff (I := I) (M := M) B Y
  let BY : Cₛ^∞⟮I; E, (fun y : M => TangentSpace I y)⟯ := ⟨fun y : M => (B y) (Y y), hBY⟩
  have hYmd := Y.mdifferentiableAt (x := x)
  have hABcomp := endoCovariantDerivative_apply (I := I) (M := M) g₀
    (endoCompField (I := I) (M := M) A B) Y x v
  have hAonBY := endoCovariantDerivative_apply (I := I) (M := M) g₀ A BY x v
  have hBonY := endoCovariantDerivative_apply (I := I) (M := M) g₀ B Y x v
  have hfun_eq : (fun y : M => (endoCompField (I := I) (M := M) A B y) (Y y)) =
      (fun y : M => (A y) ((B y) (Y y))) := by
    funext y
    rw [endoCompField_apply, ContinuousLinearMap.comp_apply]
  have hcompval : ((endoCovariantDerivative (I := I) (M := M) g₀)
        (endoCompField (I := I) (M := M) A B) x v) (Y x) =
      (LeviCivita (I := I) g₀) (fun y : M => (A y) ((B y) (Y y))) x v -
        (endoCompField (I := I) (M := M) A B x) ((LeviCivita (I := I) g₀) (fun y => Y y) x v) := by
    rw [hABcomp, hfun_eq]
  have hgradY : (LeviCivita (I := I) g₀) (fun y => Y y) x v =
      (LeviCivita (I := I) g₀).toFun (fun y : M => Y y) x v := rfl
  have hBgrad : (LeviCivita (I := I) g₀) (fun y : M => (B y) (Y y)) x v =
      ((endoCovariantDerivative (I := I) (M := M) g₀) B x v) (Y x) +
        (B x) ((LeviCivita (I := I) g₀) (fun y => Y y) x v) := by
    rw [eq_sub_iff_add_eq] at hBonY
    rw [← hBonY]
  have hAonBY' : ((endoCovariantDerivative (I := I) (M := M) g₀) A x v) ((B x) (Y x)) =
      (LeviCivita (I := I) g₀) (fun y : M => (A y) ((B y) (Y y))) x v -
        (A x) ((LeviCivita (I := I) g₀) (fun y : M => (B y) (Y y)) x v) := hAonBY
  rw [← hYx]
  rw [hcompval]
  rw [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.comp_apply, endoCompField_apply, ContinuousLinearMap.comp_apply]
  rw [hAonBY', hBgrad, map_add]
  abel

set_option linter.unusedSectionVars false in
private lemma sqrt_g0_inner_add_le'
    (g₀ : SmoothRiemannianMetric I M) (x : M) (a b : TangentSpace I x) :
    Real.sqrt (g₀.inner x (a + b) (a + b)) ≤
      Real.sqrt (g₀.inner x a a) + Real.sqrt (g₀.inner x b b) := by
  set na := Real.sqrt (g₀.inner x a a) with hna
  set nb := Real.sqrt (g₀.inner x b b) with hnb
  have haa_nn : 0 ≤ g₀.inner x a a := metric_inner_self_nonneg (I := I) (M := M) g₀ x a
  have hbb_nn : 0 ≤ g₀.inner x b b := metric_inner_self_nonneg (I := I) (M := M) g₀ x b
  have hsum_nn : 0 ≤ g₀.inner x (a + b) (a + b) :=
    metric_inner_self_nonneg (I := I) (M := M) g₀ x (a + b)
  have hna_nn : 0 ≤ na := Real.sqrt_nonneg _
  have hnb_nn : 0 ≤ nb := Real.sqrt_nonneg _
  have hna_sq : na ^ 2 = g₀.inner x a a := by rw [hna, Real.sq_sqrt haa_nn]
  have hnb_sq : nb ^ 2 = g₀.inner x b b := by rw [hnb, Real.sq_sqrt hbb_nn]
  have hcross : g₀.inner x a b ≤ na * nb := by
    have habs := abs_metric_inner_le_sqrt_metric_quadratic (I := I) (M := M) g₀ x a b
    rw [← hna, ← hnb] at habs
    exact le_trans (le_abs_self _) habs
  have hexpand : g₀.inner x (a + b) (a + b) =
      g₀.inner x a a + 2 * g₀.inner x a b + g₀.inner x b b := by
    have h1 : g₀.inner x (a + b) (a + b)
        = g₀.inner x a (a + b) + g₀.inner x b (a + b) := by
      rw [map_add (g₀.inner x), ContinuousLinearMap.add_apply]
    have h2 : g₀.inner x a (a + b) = g₀.inner x a a + g₀.inner x a b :=
      map_add (g₀.inner x a) a b
    have h3 : g₀.inner x b (a + b) = g₀.inner x b a + g₀.inner x b b :=
      map_add (g₀.inner x b) a b
    have h4 : g₀.inner x b a = g₀.inner x a b := g₀.symm x b a
    rw [h1, h2, h3, h4]; ring
  have hle_sq : g₀.inner x (a + b) (a + b) ≤ (na + nb) ^ 2 := by
    rw [hexpand]
    have hsq : (na + nb) ^ 2 = na ^ 2 + 2 * (na * nb) + nb ^ 2 := by ring
    rw [hsq, hna_sq, hnb_sq]
    nlinarith [hcross]
  have hsum_pos_nn : 0 ≤ na + nb := add_nonneg hna_nn hnb_nn
  calc Real.sqrt (g₀.inner x (a + b) (a + b))
      ≤ Real.sqrt ((na + nb) ^ 2) := Real.sqrt_le_sqrt hle_sq
    _ = na + nb := by rw [Real.sqrt_sq hsum_pos_nn]

set_option backward.isDefEq.respectTransparency false in
set_option linter.unusedSectionVars false in
set_option linter.unusedVariables false in
attribute [-instance] Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace in
theorem sqrt_inner_endoCov_gInvDiffRaisedField_le
    (g₀ : SmoothRiemannianMetric I M) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (g₁ : SmoothRiemannianMetric I M)
      (T : SmoothCcTensor g₀ 0 2)
      (h : ∀ y v w, g₁.inner y v w =
        g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ T y v w)
      {δ : ℝ} (hδ : δ < 1 / 2) (hδ0 : 0 ≤ δ)
      (hbound : gFibreOpBound (I := I) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
      (Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) (v : TangentSpace I x),
      letI : Bundle.RiemannianBundle
          (fun y : M => Tensor0SBundle.TensorRSSpace 0 3 I y) :=
        Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 0 3
      Real.sqrt (g₀.inner x
          (((endoCovariantDerivative (I := I) (M := M) g₀)
            (gInvDiffRaisedEndoField (I := I) g₀ g₁) x v) (Y x))
          (((endoCovariantDerivative (I := I) (M := M) g₀)
            (gInvDiffRaisedEndoField (I := I) g₀ g₁) x v) (Y x))) ≤
        C * ‖((iteratedCovGrad (I := I) g₀ 0 2 1 T).toSection x :
            Tensor0SBundle.TensorRSSpace 0 3 I x)‖ *
          Real.sqrt (g₀.inner x v v) * Real.sqrt (g₀.inner x (Y x) (Y x)) := by
  classical
  letI instTens : Bundle.RiemannianBundle
      (fun y : M => Tensor0SBundle.TensorRSSpace 0 3 I y) :=
    Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 0 3
  obtain ⟨C₀, hC₀0, hpw⟩ := connDiff_gFibreNorm_le_iteratedCovGrad (I := I) (M := M) g₀
  refine ⟨4 * C₀, by positivity, ?_⟩
  intro g₁ T h δ hδ hδ0 hbound Y x v
  have hcoeff : 0 < 1 - δ := by linarith
  set w : TangentSpace I x := Y x with hw_def
  set G : ℝ := ‖((iteratedCovGrad (I := I) g₀ 0 2 1 T).toSection x :
      Tensor0SBundle.TensorRSSpace 0 3 I x)‖ with hG_def
  have hG_nn : 0 ≤ G := norm_nonneg _
  set Nv : ℝ := Real.sqrt (g₀.inner x v v) with hNv_def
  set Nw : ℝ := Real.sqrt (g₀.inner x w w) with hNw_def
  have hNv_nn : 0 ≤ Nv := Real.sqrt_nonneg _
  have hNw_nn : 0 ≤ Nw := Real.sqrt_nonneg _
  have hinv_le : 1 / (1 - δ) ≤ 2 := by rw [div_le_iff₀ hcoeff]; linarith
  set EC : TangentSpace I x :=
    ((endoCovariantDerivative (I := I) (M := M) g₀)
      (gInvDiffRaisedEndoField (I := I) g₀ g₁) x v) (Y x) with hEC_def
  set T2 : TangentSpace I x :=
    - PDE.DeTurck.connDiff (I := I) g₁ g₀ x (gInvRaisedEndo (I := I) g₀ g₁ x w) v
    with hT2_def
  set T3 : TangentSpace I x :=
    inverseMetricSharpFib (I := I) g₁ x
      (dualToCotangent (I := I)
        (-(cotangentToCLM (I := I) (g0FlatCLM (I := I) g₀ x w)).comp
            ((PDE.DeTurck.connDiff (I := I) g₁ g₀ x).flip v)).toLinearMap)
    with hT3_def
  have hEC_eq : EC = T2 + T3 := by
    rw [hEC_def, hT2_def, hT3_def, hw_def]
    exact endoCov_gInvDiffRaisedField_apply (I := I) (M := M) g₀ g₁ Y x v
  have hgir := sqrt_inner_gInvRaisedEndo_le (I := I) g₀ g₁
    (ccTensorBilinSymm (I := I) g₀ T) (fun y a b => h y a b)
    (by linarith : δ < 1) hδ0 hbound x w
  rw [← hNw_def] at hgir
  have hT2_bound : Real.sqrt (g₀.inner x T2 T2) ≤ 2 * C₀ * G * Nv * Nw := by
    have hraw := hpw g₁ T h hδ hδ0 hbound x (gInvRaisedEndo (I := I) g₀ g₁ x w) v
    rw [← hNv_def] at hraw
    have hT2_sq : g₀.inner x T2 T2 =
        g₀.inner x (PDE.DeTurck.connDiff (I := I) g₁ g₀ x
            (gInvRaisedEndo (I := I) g₀ g₁ x w) v)
          (PDE.DeTurck.connDiff (I := I) g₁ g₀ x
            (gInvRaisedEndo (I := I) g₀ g₁ x w) v) := by
      simp only [hT2_def, map_neg, ContinuousLinearMap.neg_apply, neg_neg]
    rw [hT2_sq]
    refine hraw.trans ?_
    have hgir' : Real.sqrt (g₀.inner x (gInvRaisedEndo (I := I) g₀ g₁ x w)
        (gInvRaisedEndo (I := I) g₀ g₁ x w)) ≤ 2 * Nw := by
      refine hgir.trans ?_
      exact mul_le_mul_of_nonneg_right hinv_le hNw_nn
    calc C₀ * ‖((iteratedCovGrad (I := I) g₀ 0 2 1 T).toSection x :
              Tensor0SBundle.TensorRSSpace 0 3 I x)‖ *
            Real.sqrt (g₀.inner x (gInvRaisedEndo (I := I) g₀ g₁ x w)
              (gInvRaisedEndo (I := I) g₀ g₁ x w)) * Nv
        ≤ C₀ * G * (2 * Nw) * Nv := by
          rw [← hG_def]
          gcongr
      _ = 2 * C₀ * G * Nv * Nw := by ring
  have hT3_bound : Real.sqrt (g₀.inner x T3 T3) ≤ 2 * C₀ * G * Nv * Nw := by
    set Dfun : TangentSpace I x →L[ℝ] ℝ :=
      (-(cotangentToCLM (I := I) (g0FlatCLM (I := I) g₀ x w)).comp
          ((PDE.DeTurck.connDiff (I := I) g₁ g₀ x).flip v)) with hDfun_def
    set p : TangentSpace I x :=
      inverseMetricSharpFib (I := I) g₀ x (dualToCotangent (I := I) Dfun.toLinearMap)
      with hp_def
    have hT3eq : T3 = inverseMetricSharpFib (I := I) g₁ x (g0FlatCLM (I := I) g₀ x p) := by
      rw [hT3_def]
      congr 1
      exact (g0FlatCLM_inverseMetricSharpFib (I := I) g₀ x
        (dualToCotangent (I := I) Dfun.toLinearMap)).symm
    set Np : ℝ := Real.sqrt (g₀.inner x p p) with hNpdef
    have hNp_nn : 0 ≤ Np := Real.sqrt_nonneg _
    have hpp_nn : 0 ≤ g₀.inner x p p := metric_inner_self_nonneg (I := I) (M := M) g₀ x p
    have hNp_sq : Np ^ 2 = g₀.inner x p p := Real.sq_sqrt hpp_nn
    have hDval : ∀ z : TangentSpace I x, Dfun z =
        - g₀.inner x w (PDE.DeTurck.connDiff (I := I) g₁ g₀ x z v) := by
      intro z
      rw [hDfun_def, ContinuousLinearMap.neg_apply, ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.flip_apply]
      change - cotangentToDual (I := I) (g0FlatCLM (I := I) g₀ x w)
          (PDE.DeTurck.connDiff (I := I) g₁ g₀ x z v) = _
      rw [cotangentToDual_g0FlatCLM]
    have hpz : ∀ z : TangentSpace I x, g₀.inner x p z = Dfun z := by
      intro z
      rw [hp_def, inverseMetricSharpFib_inner (I := I) g₀ x
        (dualToCotangent (I := I) Dfun.toLinearMap) z]
      rw [cotangentToDualLinear_apply, cotangentToDual_dualToCotangent]
      rfl
    have hpp_val : g₀.inner x p p =
        - g₀.inner x w (PDE.DeTurck.connDiff (I := I) g₁ g₀ x p v) := by
      rw [hpz p, hDval p]
    have hconn_p := hpw g₁ T h hδ hδ0 hbound x p v
    rw [← hNv_def, ← hNpdef] at hconn_p
    have hconnG : Real.sqrt (g₀.inner x (PDE.DeTurck.connDiff (I := I) g₁ g₀ x p v)
          (PDE.DeTurck.connDiff (I := I) g₁ g₀ x p v)) ≤ C₀ * G * Np * Nv := hconn_p
    have hcs := abs_metric_inner_le_sqrt_metric_quadratic (I := I) (M := M) g₀ x w
      (PDE.DeTurck.connDiff (I := I) g₁ g₀ x p v)
    rw [← hNw_def] at hcs
    have hNp_le : Np ≤ C₀ * G * Nv * Nw := by
      have hpp_le : g₀.inner x p p ≤
          Nw * Real.sqrt (g₀.inner x (PDE.DeTurck.connDiff (I := I) g₁ g₀ x p v)
            (PDE.DeTurck.connDiff (I := I) g₁ g₀ x p v)) := by
        rw [hpp_val]
        calc - g₀.inner x w (PDE.DeTurck.connDiff (I := I) g₁ g₀ x p v)
            ≤ |g₀.inner x w (PDE.DeTurck.connDiff (I := I) g₁ g₀ x p v)| := neg_le_abs _
          _ ≤ Nw * Real.sqrt (g₀.inner x (PDE.DeTurck.connDiff (I := I) g₁ g₀ x p v)
              (PDE.DeTurck.connDiff (I := I) g₁ g₀ x p v)) := hcs
      have hKnn : 0 ≤ C₀ * G * Nv * Nw :=
        mul_nonneg (mul_nonneg (mul_nonneg hC₀0 hG_nn) hNv_nn) hNw_nn
      have hchain : Nw * Real.sqrt (g₀.inner x (PDE.DeTurck.connDiff (I := I) g₁ g₀ x p v)
            (PDE.DeTurck.connDiff (I := I) g₁ g₀ x p v)) ≤
          Nw * (C₀ * G * Np * Nv) :=
        mul_le_mul_of_nonneg_left hconnG hNw_nn
      have hpp_le2 : g₀.inner x p p ≤ (C₀ * G * Nv * Nw) * Np := by
        refine hpp_le.trans (hchain.trans ?_)
        nlinarith [hNw_nn, hNp_nn, mul_nonneg (mul_nonneg hC₀0 hG_nn) hNv_nn]
      nlinarith [hNp_sq, hNp_nn, hpp_le2, hKnn]
    have hsharp := sqrt_inner_inverseMetricSharpFib_g0FlatCLM_le (I := I) g₀ g₁
      (ccTensorBilinSymm (I := I) g₀ T) (fun y a b => h y a b)
      (by linarith : δ < 1) hδ0 hbound x p
    rw [← hNpdef] at hsharp
    rw [hT3eq]
    refine hsharp.trans ?_
    have hstep : (1 / (1 - δ)) * Np ≤ 2 * Np :=
      mul_le_mul_of_nonneg_right hinv_le hNp_nn
    refine hstep.trans ?_
    nlinarith [hNp_le, hNp_nn, mul_nonneg (mul_nonneg hC₀0 hG_nn) (mul_nonneg hNv_nn hNw_nn)]
  have htri : Real.sqrt (g₀.inner x EC EC) ≤
      Real.sqrt (g₀.inner x T2 T2) + Real.sqrt (g₀.inner x T3 T3) := by
    rw [hEC_eq]
    exact sqrt_g0_inner_add_le' (I := I) g₀ x T2 T3
  refine htri.trans ?_
  have hsum : Real.sqrt (g₀.inner x T2 T2) + Real.sqrt (g₀.inner x T3 T3) ≤
      (2 * C₀ * G * Nv * Nw) + (2 * C₀ * G * Nv * Nw) := add_le_add hT2_bound hT3_bound
  refine hsum.trans ?_
  nlinarith [mul_nonneg (mul_nonneg (mul_nonneg hC₀0 hG_nn) hNv_nn) hNw_nn]

set_option linter.unusedSectionVars false in
private lemma fiberComponent_slotInsertEndoFib_eq
    (g₀ : SmoothRiemannianMetric I M) (x : M)
    (Λ : TangentSpace I x →L[ℝ] TangentSpace I x)
    {n : ℕ} (e : Fin n → TangentSpace I x)
    (horth : ∀ i j : Fin n, g₀.inner x (e i) (e j) = if i = j then (1 : ℝ) else 0)
    (K J : Fin 2 → Fin n) :
    fiberNormSqComponent (I := I) (M := M) g₀ x 2 2
        (show TensorRSSpace 2 2 I x from
          TensorRSSpace.ofCLM (slotInsertEndoFib (I := I) (M := M) 2 0 x Λ)) n e K J =
      g₀.inner x (Λ (e (J 0))) (e (K 0)) * (if K 1 = J 1 then (1 : ℝ) else 0) := by
  have hcomp : fiberNormSqComponent (I := I) (M := M) g₀ x 2 2
      (show TensorRSSpace 2 2 I x from
        TensorRSSpace.ofCLM (slotInsertEndoFib (I := I) (M := M) 2 0 x Λ)) n e K J =
      Tensor0SSpace.toModel
        ((slotInsertEndoFib (I := I) (M := M) 2 0 x Λ) (coframeS (I := I) (M := M) g₀ x 2 e K))
        (fun k => e (J k)) := by
    unfold fiberNormSqComponent coframeS; rfl
  rw [hcomp, slotInsertEndoFib_apply_eval]
  rw [show (coframeS (I := I) (M := M) g₀ x 2 e K).toModel
        (Function.update (fun k => e (J k)) 0 (Λ (e (J 0))))
      = coframeS (I := I) (M := M) g₀ x 2 e K
        (Function.update (fun k => e (J k)) 0 (Λ (e (J 0)))) from rfl]
  rw [coframeS_apply, Fin.prod_univ_two, Function.update_self,
    Function.update_of_ne (by decide : (1 : Fin 2) ≠ 0)]
  rw [g₀.symm x (e (K 0)) (Λ (e (J 0))), horth (K 1) (J 1)]

set_option backward.isDefEq.respectTransparency false in
set_option linter.unusedSectionVars false in
set_option linter.unusedVariables false in
private lemma riemannianFiberNormSq_slotInsertEndoFib_le_card_mul
    (g₀ : SmoothRiemannianMetric I M) (x : M)
    (Λ : TangentSpace I x →L[ℝ] TangentSpace I x) (B : ℝ)
    (hΛ : ∀ a : TangentSpace I x, g₀.inner x a a = 1 → g₀.inner x (Λ a) (Λ a) ≤ B)
    (hB : 0 ≤ B) :
    riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x
        (show TensorRSSpace 2 2 I x from
          TensorRSSpace.ofCLM (slotInsertEndoFib (I := I) (M := M) 2 0 x Λ)) ≤
      ((Module.finrank ℝ E : ℝ)) ^ 2 * B := by
  classical
  obtain ⟨n, e, bse, hn, hbse, horth, hpars, hrepr_v, hsum⟩ :=
    tangent_orthonormalBasis_witness (I := I) (M := M) g₀ x
  have hnE : n = Module.finrank ℝ E := by rw [hn]; rfl
  rw [rfns_rs_eq_sum_componentSq_of_basis (I := I) (M := M) g₀ 2 2 x
    (show TensorRSSpace 2 2 I x from
      TensorRSSpace.ofCLM (slotInsertEndoFib (I := I) (M := M) 2 0 x Λ)) e bse hnE hbse horth]
  have hcompsq : ∀ (K J : Fin 2 → Fin n),
      (fiberNormSqComponent (I := I) (M := M) g₀ x 2 2
        (show TensorRSSpace 2 2 I x from
          TensorRSSpace.ofCLM (slotInsertEndoFib (I := I) (M := M) 2 0 x Λ)) n e K J) ^ 2 =
        (g₀.inner x (e (K 0)) (Λ (e (J 0)))) ^ 2 * (if K 1 = J 1 then (1 : ℝ) else 0) := by
    intro K J
    rw [fiberComponent_slotInsertEndoFib_eq (I := I) g₀ x Λ e horth K J]
    rw [g₀.symm x (Λ (e (J 0))) (e (K 0))]
    by_cases hkj : K 1 = J 1
    · simp only [hkj, if_true, mul_one]
    · simp only [hkj, if_false, mul_zero]; ring
  have hsumeq : (∑ K : Fin 2 → Fin n, ∑ J : Fin 2 → Fin n,
        (fiberNormSqComponent (I := I) (M := M) g₀ x 2 2
          (show TensorRSSpace 2 2 I x from
            TensorRSSpace.ofCLM (slotInsertEndoFib (I := I) (M := M) 2 0 x Λ)) n e K J) ^ 2) =
      ∑ J : Fin 2 → Fin n, g₀.inner x (Λ (e (J 0))) (Λ (e (J 0))) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun J _ => ?_)
    rw [Finset.sum_congr rfl (fun K _ => hcompsq K J)]
    rw [← (finTwoArrowEquiv (Fin n)).symm.sum_comp
      (fun K : Fin 2 → Fin n => (g₀.inner x (e (K 0)) (Λ (e (J 0)))) ^ 2 *
        (if K 1 = J 1 then (1 : ℝ) else 0))]
    rw [Fintype.sum_prod_type]
    have hKsum : ∀ k0 : Fin n,
        (∑ k1 : Fin n, (g₀.inner x (e (((finTwoArrowEquiv (Fin n)).symm (k0, k1)) 0))
            (Λ (e (J 0)))) ^ 2 *
          (if ((finTwoArrowEquiv (Fin n)).symm (k0, k1)) 1 = J 1 then (1 : ℝ) else 0)) =
        (g₀.inner x (e k0) (Λ (e (J 0)))) ^ 2 := by
      intro k0
      rw [show (∑ k1 : Fin n, (g₀.inner x (e (((finTwoArrowEquiv (Fin n)).symm (k0, k1)) 0))
            (Λ (e (J 0)))) ^ 2 *
          (if ((finTwoArrowEquiv (Fin n)).symm (k0, k1)) 1 = J 1 then (1 : ℝ) else 0)) =
          ∑ k1 : Fin n, (g₀.inner x (e k0) (Λ (e (J 0)))) ^ 2 *
            (if k1 = J 1 then (1 : ℝ) else 0) from by
        refine Finset.sum_congr rfl (fun k1 _ => ?_)
        rfl]
      rw [← Finset.mul_sum, Finset.sum_ite_eq' Finset.univ (J 1) (fun _ => (1 : ℝ))]
      simp
    rw [Finset.sum_congr rfl (fun k0 _ => hKsum k0)]
    exact hpars (Λ (e (J 0)))
  rw [hsumeq]
  have hJbound : ∀ J : Fin 2 → Fin n,
      g₀.inner x (Λ (e (J 0))) (Λ (e (J 0))) ≤ B := by
    intro J
    refine hΛ (e (J 0)) ?_
    rw [horth (J 0) (J 0)]; simp
  calc (∑ J : Fin 2 → Fin n, g₀.inner x (Λ (e (J 0))) (Λ (e (J 0))))
      ≤ ∑ _J : Fin 2 → Fin n, B := Finset.sum_le_sum (fun J _ => hJbound J)
    _ = ((Module.finrank ℝ E : ℝ)) ^ 2 * B := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
          Fintype.card_fin, nsmul_eq_mul, ← hnE]
        push_cast; ring

set_option linter.unusedSectionVars false in
private lemma fiberComponent_slotInsertEndoFib_eq_general
    (g₀ : SmoothRiemannianMetric I M) (x : M) (s : ℕ) (k : Fin s)
    (Λ : TangentSpace I x →L[ℝ] TangentSpace I x)
    {n : ℕ} (e : Fin n → TangentSpace I x)
    (horth : ∀ i j : Fin n, g₀.inner x (e i) (e j) = if i = j then (1 : ℝ) else 0)
    (K J : Fin s → Fin n) :
    fiberNormSqComponent (I := I) (M := M) g₀ x s s
        (show TensorRSSpace s s I x from
          TensorRSSpace.ofCLM (slotInsertEndoFib (I := I) (M := M) s k x Λ)) n e K J =
      g₀.inner x (e (K k)) (Λ (e (J k))) *
        ∏ l ∈ Finset.univ.erase k, (if K l = J l then (1 : ℝ) else 0) := by
  have hcomp : fiberNormSqComponent (I := I) (M := M) g₀ x s s
      (show TensorRSSpace s s I x from
        TensorRSSpace.ofCLM (slotInsertEndoFib (I := I) (M := M) s k x Λ)) n e K J =
      Tensor0SSpace.toModel
        ((slotInsertEndoFib (I := I) (M := M) s k x Λ) (coframeS (I := I) (M := M) g₀ x s e K))
        (fun l => e (J l)) := by
    unfold fiberNormSqComponent coframeS; rfl
  rw [hcomp, slotInsertEndoFib_apply_eval]
  rw [show (coframeS (I := I) (M := M) g₀ x s e K).toModel
        (Function.update (fun l => e (J l)) k (Λ (e (J k))))
      = coframeS (I := I) (M := M) g₀ x s e K
        (Function.update (fun l => e (J l)) k (Λ (e (J k)))) from rfl]
  rw [coframeS_apply]
  rw [← Finset.prod_erase_mul Finset.univ
    (fun l => g₀.inner x (e (K l))
      (Function.update (fun l => e (J l)) k (Λ (e (J k))) l)) (Finset.mem_univ k)]
  rw [Function.update_self]
  rw [g₀.symm x (e (K k)) (Λ (e (J k)))]
  rw [mul_comm]
  congr 1
  refine Finset.prod_congr rfl (fun l hl => ?_)
  have hlk : l ≠ k := Finset.ne_of_mem_erase hl
  rw [Function.update_of_ne hlk, horth (K l) (J l)]

set_option linter.unusedSectionVars false in
set_option linter.unusedVariables false in
private lemma sum_compSq_slotInsertEndoFib_eq_normSq
    (g₀ : SmoothRiemannianMetric I M) (x : M) (s : ℕ) (k : Fin s)
    (Λ : TangentSpace I x →L[ℝ] TangentSpace I x)
    {n : ℕ} (e : Fin n → TangentSpace I x)
    (horth : ∀ i j : Fin n, g₀.inner x (e i) (e j) = if i = j then (1 : ℝ) else 0)
    (hpars : ∀ v : TangentSpace I x, ∑ i : Fin n, g₀.inner x (e i) v ^ 2 = g₀.inner x v v)
    (J : Fin s → Fin n) :
    (∑ K : Fin s → Fin n,
        (fiberNormSqComponent (I := I) (M := M) g₀ x s s
          (show TensorRSSpace s s I x from
            TensorRSSpace.ofCLM (slotInsertEndoFib (I := I) (M := M) s k x Λ)) n e K J) ^ 2) =
      g₀.inner x (Λ (e (J k))) (Λ (e (J k))) := by
  classical
  have hcompsq : ∀ K : Fin s → Fin n,
      (fiberNormSqComponent (I := I) (M := M) g₀ x s s
        (show TensorRSSpace s s I x from
          TensorRSSpace.ofCLM (slotInsertEndoFib (I := I) (M := M) s k x Λ)) n e K J) ^ 2 =
        (g₀.inner x (e (K k)) (Λ (e (J k)))) ^ 2 *
          ∏ l ∈ Finset.univ.erase k, (if K l = J l then (1 : ℝ) else 0) := by
    intro K
    rw [fiberComponent_slotInsertEndoFib_eq_general (I := I) g₀ x s k Λ e horth K J]
    rw [mul_pow]
    congr 1
    rw [← Finset.prod_pow]
    refine Finset.prod_congr rfl (fun l _ => ?_)
    by_cases hkj : K l = J l
    · simp [hkj]
    · simp [hkj]
  rw [Finset.sum_congr rfl (fun K _ => hcompsq K)]
  set ee := Equiv.funSplitAt k (Fin n) with hee
  rw [← (Equiv.sum_comp ee.symm
    (fun K : Fin s → Fin n => (g₀.inner x (e (K k)) (Λ (e (J k)))) ^ 2 *
      ∏ l ∈ Finset.univ.erase k, (if K l = J l then (1 : ℝ) else 0)))]
  rw [Fintype.sum_prod_type]
  have hkval : ∀ (m : Fin n) (ρ : {i : Fin s // i ≠ k} → Fin n), (ee.symm (m, ρ)) k = m := by
    intro m ρ; rw [hee]; simp [Equiv.funSplitAt, Equiv.piSplitAt]
  have hinner : ∀ m : Fin n,
      (∑ ρ : {i : Fin s // i ≠ k} → Fin n,
        (g₀.inner x (e ((ee.symm (m, ρ)) k)) (Λ (e (J k)))) ^ 2 *
          ∏ l ∈ Finset.univ.erase k,
            (if (ee.symm (m, ρ)) l = J l then (1 : ℝ) else 0)) =
        (g₀.inner x (e m) (Λ (e (J k)))) ^ 2 := by
    intro m
    have hcoe : ∀ (ρ : {i : Fin s // i ≠ k} → Fin n) (l : Fin s) (hl : l ≠ k),
        (ee.symm (m, ρ)) l = ρ ⟨l, hl⟩ := by
      intro ρ l hl
      rw [hee]; simp [Equiv.funSplitAt, Equiv.piSplitAt, hl]
    have hindic : ∀ ρ : {i : Fin s // i ≠ k} → Fin n,
        (∏ l ∈ Finset.univ.erase k,
          (if (ee.symm (m, ρ)) l = J l then (1 : ℝ) else 0)) =
          (if ρ = (fun j : {i : Fin s // i ≠ k} => J j) then (1 : ℝ) else 0) := by
      intro ρ
      by_cases hρ : ρ = (fun j : {i : Fin s // i ≠ k} => J j)
      · rw [if_pos hρ]
        refine Finset.prod_eq_one (fun l hl => ?_)
        have hlk : l ≠ k := Finset.ne_of_mem_erase hl
        rw [hcoe ρ l hlk, hρ, if_pos rfl]
      · rw [if_neg hρ]
        obtain ⟨j, hj⟩ : ∃ j : {i : Fin s // i ≠ k}, ρ j ≠ J j := by
          by_contra hcon
          exact hρ (funext (fun j => not_not.mp (fun h => hcon ⟨j, h⟩)))
        refine Finset.prod_eq_zero (i := (j : Fin s))
          (Finset.mem_erase.mpr ⟨j.2, Finset.mem_univ _⟩) ?_
        rw [hcoe ρ (j : Fin s) j.2, if_neg hj]
    rw [Finset.sum_congr rfl (fun ρ _ => by rw [hkval m ρ, hindic ρ] :
      ∀ ρ ∈ Finset.univ,
        (g₀.inner x (e ((ee.symm (m, ρ)) k)) (Λ (e (J k)))) ^ 2 *
          ∏ l ∈ Finset.univ.erase k,
            (if (ee.symm (m, ρ)) l = J l then (1 : ℝ) else 0) =
        (g₀.inner x (e m) (Λ (e (J k)))) ^ 2 *
          (if ρ = (fun j : {i : Fin s // i ≠ k} => J j) then (1 : ℝ) else 0))]
    rw [← Finset.mul_sum,
      Finset.sum_ite_eq' Finset.univ (fun j : {i : Fin s // i ≠ k} => J j) (fun _ => (1 : ℝ))]
    simp
  rw [Finset.sum_congr rfl (fun m _ => hinner m)]
  exact hpars (Λ (e (J k)))

set_option backward.isDefEq.respectTransparency false in
set_option linter.unusedSectionVars false in
set_option linter.unusedVariables false in
private lemma riemannianFiberNormSq_slotInsertEndoFib_le_card_mul_general
    (g₀ : SmoothRiemannianMetric I M) (x : M) (s : ℕ) (k : Fin s)
    (Λ : TangentSpace I x →L[ℝ] TangentSpace I x) (B : ℝ)
    (hΛ : ∀ a : TangentSpace I x, g₀.inner x a a = 1 → g₀.inner x (Λ a) (Λ a) ≤ B)
    (hB : 0 ≤ B) :
    riemannianFiberNormSq (I := I) (M := M) g₀ s s x
        (show TensorRSSpace s s I x from
          TensorRSSpace.ofCLM (slotInsertEndoFib (I := I) (M := M) s k x Λ)) ≤
      ((Module.finrank ℝ E : ℝ)) ^ s * B := by
  classical
  obtain ⟨n, e, bse, hn, hbse, horth, hpars, hrepr_v, hsum⟩ :=
    tangent_orthonormalBasis_witness (I := I) (M := M) g₀ x
  have hnE : n = Module.finrank ℝ E := by rw [hn]; rfl
  rw [rfns_rs_eq_sum_componentSq_of_basis (I := I) (M := M) g₀ s s x
    (show TensorRSSpace s s I x from
      TensorRSSpace.ofCLM (slotInsertEndoFib (I := I) (M := M) s k x Λ)) e bse hnE hbse horth]
  rw [Finset.sum_comm]
  have hsumeq : (∑ J : Fin s → Fin n, ∑ K : Fin s → Fin n,
        (fiberNormSqComponent (I := I) (M := M) g₀ x s s
          (show TensorRSSpace s s I x from
            TensorRSSpace.ofCLM (slotInsertEndoFib (I := I) (M := M) s k x Λ)) n e K J) ^ 2) =
      ∑ J : Fin s → Fin n, g₀.inner x (Λ (e (J k))) (Λ (e (J k))) := by
    refine Finset.sum_congr rfl (fun J _ => ?_)
    exact sum_compSq_slotInsertEndoFib_eq_normSq (I := I) g₀ x s k Λ e horth hpars J
  rw [hsumeq]
  have hJbound : ∀ J : Fin s → Fin n,
      g₀.inner x (Λ (e (J k))) (Λ (e (J k))) ≤ B := by
    intro J
    refine hΛ (e (J k)) ?_
    rw [horth (J k) (J k)]; simp
  calc (∑ J : Fin s → Fin n, g₀.inner x (Λ (e (J k))) (Λ (e (J k))))
      ≤ ∑ _J : Fin s → Fin n, B := Finset.sum_le_sum (fun J _ => hJbound J)
    _ = ((Module.finrank ℝ E : ℝ)) ^ s * B := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
          Fintype.card_fin, nsmul_eq_mul, ← hnE]
        push_cast; ring

set_option backward.isDefEq.respectTransparency false in
set_option linter.unusedSectionVars false in
set_option linter.unusedVariables false in
attribute [-instance] Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace in
theorem riemannianFiberNormSq_covGrad_gInvDiffSlotCoeff_le
    (g₀ : SmoothRiemannianMetric I M) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (g₁ : SmoothRiemannianMetric I M)
      (T : SmoothCcTensor g₀ 0 2)
      {δ : ℝ} (hδ : δ < 1 / 2) (hδ0 : 0 ≤ δ)
      (h : ∀ y v w, g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ T y v w)
      (hbound : gFibreOpBound (I := I) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
      (x : M),
      letI : Bundle.RiemannianBundle
          (fun y : M => Tensor0SBundle.TensorRSSpace 0 3 I y) :=
        Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 0 3
      riemannianFiberNormSq (I := I) (M := M) g₀ 2 3 x
          ((covGrad (I := I) (M := M) g₀ 2 2 (gInvDiffSlotCoeff (I := I) g₀ g₁)).toSection x) ≤
        C ^ 2 * ‖((iteratedCovGrad (I := I) g₀ 0 2 1 T).toSection x :
            Tensor0SBundle.TensorRSSpace 0 3 I x)‖ ^ 2 := by
  classical
  letI instTens : Bundle.RiemannianBundle
      (fun y : M => Tensor0SBundle.TensorRSSpace 0 3 I y) :=
    Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 0 3
  obtain ⟨C₀, hC₀0, hpw⟩ := sqrt_inner_endoCov_gInvDiffRaisedField_le (I := I) (M := M) g₀
  refine ⟨Real.sqrt ((Module.finrank ℝ E : ℝ) ^ 3) * (4 * C₀), by positivity, ?_⟩
  intro g₁ T δ hδ hδ0 h hbound x
  set Λ : ContMDiffSection I (E →L[ℝ] E) ∞
      (fun y : M => TangentSpace I y →L[ℝ] TangentSpace I y) :=
    gInvDiffRaisedEndoField (I := I) g₀ g₁ with hΛ_def
  set G : ℝ := ‖((iteratedCovGrad (I := I) g₀ 0 2 1 T).toSection x :
      Tensor0SBundle.TensorRSSpace 0 3 I x)‖ with hG_def
  have hG_nn : 0 ≤ G := norm_nonneg _
  rw [gInvDiffSlotCoeff_eq_slotInsertEndoCc (I := I) g₀ g₁, ← hΛ_def]
  rw [covGrad_toSection_apply (I := I) (M := M) g₀ 2 2
    (slotInsertEndoCc (I := I) (M := M) g₀ 1 Λ) x]
  refine le_trans (DifferentialGeometry.Analysis.Sobolev.Tensor.riemannianFiberNormSq_covGradBundleEquiv_le_card_mul_rs (I := I) (M := M)
    g₀ 2 2 x _ ((Module.finrank ℝ E : ℝ) ^ 2 * (4 * C₀ * G) ^ 2) ?_) ?_
  · intro v hv
    have hΦ : tensorRSCovariantDerivative I M 2 2 (LeviCivita (I := I) g₀)
          (fun y : M => (slotInsertEndoCc (I := I) (M := M) g₀ 1 Λ).toSection y) x v =
        (show TensorRSSpace 2 2 I x from
          TensorRSSpace.ofCLM (slotInsertEndoFib (I := I) (M := M) 2 0 x
            ((endoCovariantDerivative (I := I) (M := M) g₀) Λ x v))) := by
      rw [← tensorCovDerivAt_def (I := I) (M := M) g₀ 2 2
        (slotInsertEndoCc (I := I) (M := M) g₀ 1 Λ) x v]
      exact tensorCovDerivAt_slotInsertEndoCc_eq (I := I) (M := M) g₀ 1 Λ x v
    rw [hΦ]
    refine riemannianFiberNormSq_slotInsertEndoFib_le_card_mul (I := I) g₀ x
      ((endoCovariantDerivative (I := I) (M := M) g₀) Λ x v) ((4 * C₀ * G) ^ 2) ?_ (by positivity)
    intro a ha
    obtain ⟨Y, hYx⟩ := ContMDiffSection.exists_eq_at (I := I) (n := (⊤ : ℕ∞))
      (F := E) (V := (TangentSpace I : M → Type _)) x a
    have hbd := hpw g₁ T h hδ hδ0 hbound Y x v
    rw [hYx] at hbd
    have hvroot : Real.sqrt (g₀.inner x v v) = 1 := by rw [hv, Real.sqrt_one]
    have haroot : Real.sqrt (g₀.inner x a a) = 1 := by rw [ha, Real.sqrt_one]
    rw [hvroot, haroot, mul_one, mul_one, ← hG_def] at hbd
    have haa_nn : 0 ≤ g₀.inner x
        (((endoCovariantDerivative (I := I) (M := M) g₀) Λ x v) a)
        (((endoCovariantDerivative (I := I) (M := M) g₀) Λ x v) a) :=
      metric_inner_self_nonneg (I := I) (M := M) g₀ x _
    have hsq := Real.sq_sqrt haa_nn
    nlinarith [hbd, Real.sqrt_nonneg (g₀.inner x
      (((endoCovariantDerivative (I := I) (M := M) g₀) Λ x v) a)
      (((endoCovariantDerivative (I := I) (M := M) g₀) Λ x v) a)), hsq,
      mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 4) hC₀0) hG_nn]
  · have hsq3 : Real.sqrt ((Module.finrank ℝ E : ℝ) ^ 3) ^ 2 = (Module.finrank ℝ E : ℝ) ^ 3 :=
      Real.sq_sqrt (by positivity)
    have hrhs : (Real.sqrt ((Module.finrank ℝ E : ℝ) ^ 3) * (4 * C₀)) ^ 2 * G ^ 2 =
        (Module.finrank ℝ E : ℝ) ^ 3 * (4 * C₀ * G) ^ 2 := by
      rw [mul_pow, hsq3]; ring
    have hlhs : (Module.finrank ℝ E : ℝ) * ((Module.finrank ℝ E : ℝ) ^ 2 * (4 * C₀ * G) ^ 2) =
        (Module.finrank ℝ E : ℝ) ^ 3 * (4 * C₀ * G) ^ 2 := by ring
    rw [hlhs, hrhs]

set_option linter.unusedSectionVars false in
attribute [-instance] Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace in
theorem norm_toSection_eq_sqrt_riemannianFiberNormSq
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (x : M) (W : SmoothCcTensor g r s) :
    letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace r s I b) :=
      Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g r s
    ‖(W.toSection x : TensorRSSpace r s I x)‖ =
      Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g r s x (W.toSection x)) := by
  letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace r s I b) :=
    Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g r s
  rw [norm_eq_sqrt_tensorInnerPointwise (I := I) (M := M) g r s x (W.toSection x),
    riemannianFiberNormSq_eq_tensorInnerPointwise (I := I) (M := M) g r s x (W.toSection x)]

set_option linter.unusedSectionVars false in
attribute [-instance] Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace in
theorem norm_iteratedCovGrad_gInvDiffSlotCoeff_le_envelope_zero
    (g₀ g₁ : SmoothRiemannianMetric I M) (T : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ : δ < 1 / 2) (hδ0 : 0 ≤ δ)
    (h : ∀ y v w, g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ T y v w)
    (hbound : gFibreOpBound (I := I) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ) (x : M) (R : ℝ) :
    letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace 2 2 I b) :=
      Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 2 2
    ‖((iteratedCovGrad (I := I) g₀ 2 2 0 (gInvDiffSlotCoeff (I := I) g₀ g₁)).toSection x :
        TensorRSSpace 2 2 I x)‖ ≤
      (Module.finrank ℝ E : ℝ) * (1 + R) ^ 0 := by
  letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace 2 2 I b) :=
    Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 2 2
  rw [iteratedCovGrad_zero, pow_zero, mul_one,
    norm_toSection_eq_sqrt_riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x
      (gInvDiffSlotCoeff (I := I) g₀ g₁)]
  have hb := riemannianFiberNormSq_gInvDiffSlotCoeff_le (I := I) (M := M) g₀ g₁ T hδ hδ0 h hbound x
  have hfr0 : (0 : ℝ) ≤ (Module.finrank ℝ E : ℝ) := Nat.cast_nonneg _
  calc Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x
          ((gInvDiffSlotCoeff (I := I) g₀ g₁).toSection x))
      ≤ Real.sqrt ((Module.finrank ℝ E : ℝ) ^ 2) := Real.sqrt_le_sqrt hb
    _ = (Module.finrank ℝ E : ℝ) := Real.sqrt_sq hfr0

set_option linter.unusedSectionVars false in
set_option linter.unusedVariables false in
attribute [-instance] Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace in
theorem norm_iteratedCovGrad_gInvDiffSlotCoeff_le_envelope_one
    (g₀ : SmoothRiemannianMetric I M) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (g₁ : SmoothRiemannianMetric I M) (T : SmoothCcTensor g₀ 0 2)
      {δ : ℝ} (hδ : δ < 1 / 2) (hδ0 : 0 ≤ δ)
      (h : ∀ y v w, g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ T y v w)
      (hbound : gFibreOpBound (I := I) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ) (x : M) {R : ℝ}
      (hR0 : 0 ≤ R)
      (hjet : letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace 0 3 I b) :=
          Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 0 3
        ‖((iteratedCovGrad (I := I) g₀ 0 2 1 T).toSection x : TensorRSSpace 0 3 I x)‖ ≤ R),
      letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace 2 3 I b) :=
        Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 2 3
      ‖((iteratedCovGrad (I := I) g₀ 2 2 1 (gInvDiffSlotCoeff (I := I) g₀ g₁)).toSection x :
          TensorRSSpace 2 3 I x)‖ ≤ C * (1 + R) ^ 1 := by
  obtain ⟨C, hC0, hbnd⟩ := riemannianFiberNormSq_covGrad_gInvDiffSlotCoeff_le (I := I) (M := M) g₀
  refine ⟨C, hC0, ?_⟩
  intro g₁ T δ hδ hδ0 h hbound x R hR0 hjet
  letI inst3 : Bundle.RiemannianBundle (fun b : M => TensorRSSpace 0 3 I b) :=
    Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 0 3
  letI inst23 : Bundle.RiemannianBundle (fun b : M => TensorRSSpace 2 3 I b) :=
    Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 2 3
  have hb := hbnd g₁ T hδ hδ0 h hbound x
  have hiter1 : iteratedCovGrad (I := I) g₀ 2 2 1 (gInvDiffSlotCoeff (I := I) g₀ g₁) =
      covGrad (I := I) (M := M) g₀ 2 2 (gInvDiffSlotCoeff (I := I) g₀ g₁) := by
    rw [iteratedCovGrad_succ, iteratedCovGrad_zero]
  rw [pow_one,
    norm_toSection_eq_sqrt_riemannianFiberNormSq (I := I) (M := M) g₀ 2 3 x
      (iteratedCovGrad (I := I) g₀ 2 2 1 (gInvDiffSlotCoeff (I := I) g₀ g₁)), hiter1]
  set G : ℝ := ‖((iteratedCovGrad (I := I) g₀ 0 2 1 T).toSection x : TensorRSSpace 0 3 I x)‖ with hG
  have hG0 : 0 ≤ G := norm_nonneg _
  have hsqrt_le : Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g₀ 2 3 x
      ((covGrad (I := I) (M := M) g₀ 2 2 (gInvDiffSlotCoeff (I := I) g₀ g₁)).toSection x)) ≤
      Real.sqrt (C ^ 2 * G ^ 2) := Real.sqrt_le_sqrt hb
  refine hsqrt_le.trans ?_
  rw [show C ^ 2 * G ^ 2 = (C * G) ^ 2 from by ring, Real.sqrt_sq (mul_nonneg hC0 hG0)]
  have hGR : G ≤ R := hjet
  calc C * G ≤ C * R := mul_le_mul_of_nonneg_left hGR hC0
    _ ≤ C * (1 + R) := by
        refine mul_le_mul_of_nonneg_left ?_ hC0; linarith

set_option backward.isDefEq.respectTransparency false in
set_option linter.unusedSectionVars false in
theorem covGrad_gInvDiffSlotCoeff_eq_covGrad_slotInsertEndoCc
    (g₀ g₁ : SmoothRiemannianMetric I M) :
    covGrad (I := I) (M := M) g₀ 2 2 (gInvDiffSlotCoeff (I := I) g₀ g₁) =
      covGrad (I := I) (M := M) g₀ 2 2
        (slotInsertEndoCc (I := I) (M := M) g₀ 1 (gInvDiffRaisedEndoField (I := I) g₀ g₁)) := by
  rw [gInvDiffSlotCoeff_eq_slotInsertEndoCc (I := I) g₀ g₁]

set_option backward.isDefEq.respectTransparency false in
set_option linter.unusedSectionVars false in
theorem covGrad_gInvDiffSlotCoeff_toSection_eval
    (g₀ g₁ : SmoothRiemannianMetric I M) (x : M)
    (D : Tensor0SSpace 2 I x) (v : Fin 3 → TangentSpace I x) :
    Tensor0SSpace.toModel
        ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 3 I x from
          (covGrad (I := I) (M := M) g₀ 2 2 (gInvDiffSlotCoeff (I := I) g₀ g₁)).toSection x) D) v =
      Tensor0SSpace.toModel
        ((slotInsertEndoFib (I := I) (M := M) 2 0 x
            ((endoCovariantDerivative (I := I) (M := M) g₀)
              (gInvDiffRaisedEndoField (I := I) g₀ g₁) x (v 0))) D)
        (Matrix.vecTail v) := by
  rw [covGrad_gInvDiffSlotCoeff_eq_covGrad_slotInsertEndoCc (I := I) g₀ g₁]
  exact covGrad_slotInsertEndoCc_toSection_eq (I := I) (M := M) g₀ 1
    (gInvDiffRaisedEndoField (I := I) g₀ g₁) x D v

set_option backward.isDefEq.respectTransparency false in
set_option linter.unusedSectionVars false in
theorem covGrad_gInvDiffSlotCoeff_endoCov_apply
    (g₀ g₁ : SmoothRiemannianMetric I M)
    (Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) (v : TangentSpace I x) :
    ((endoCovariantDerivative (I := I) (M := M) g₀)
        (gInvDiffRaisedEndoField (I := I) g₀ g₁) x v) (Y x) =
      - PDE.DeTurck.connDiff (I := I) g₁ g₀ x (gInvRaisedEndo (I := I) g₀ g₁ x (Y x)) v
      + inverseMetricSharpFib (I := I) g₁ x
          (dualToCotangent (I := I)
            (-(cotangentToCLM (I := I) (g0FlatCLM (I := I) g₀ x (Y x))).comp
                ((PDE.DeTurck.connDiff (I := I) g₁ g₀ x).flip v)).toLinearMap) :=
  endoCov_gInvDiffRaisedField_apply (I := I) (M := M) g₀ g₁ Y x v

set_option linter.unusedSectionVars false in
private lemma tensor0SOne_apply_add_comp (x : M) (om : Tensor0SSpace 1 I x)
    (a b : TangentSpace I x) :
    om (fun _ : Fin 1 => a + b) = om (fun _ : Fin 1 => a) + om (fun _ : Fin 1 => b) := by
  let φ := continuousMultilinearCurryFin1 ℝ (TangentSpace I x) ℝ
    (om : ContinuousMultilinearMap ℝ (fun _ : Fin 1 => TangentSpace I x) ℝ)
  have ha : (om : ContinuousMultilinearMap ℝ (fun _ : Fin 1 => TangentSpace I x) ℝ)
      (fun _ : Fin 1 => a) = φ a := by rw [continuousMultilinearCurryFin1_apply]; rfl
  have hb : (om : ContinuousMultilinearMap ℝ (fun _ : Fin 1 => TangentSpace I x) ℝ)
      (fun _ : Fin 1 => b) = φ b := by rw [continuousMultilinearCurryFin1_apply]; rfl
  have hab : (om : ContinuousMultilinearMap ℝ (fun _ : Fin 1 => TangentSpace I x) ℝ)
      (fun _ : Fin 1 => a + b) = φ (a + b) := by rw [continuousMultilinearCurryFin1_apply]; rfl
  change (om : ContinuousMultilinearMap ℝ (fun _ : Fin 1 => TangentSpace I x) ℝ)
      (fun _ => a + b) = _
  rw [hab, ha, hb, map_add]

set_option linter.unusedSectionVars false in
private lemma tensor0SOne_apply_smul_comp (x : M) (om : Tensor0SSpace 1 I x)
    (c : ℝ) (a : TangentSpace I x) :
    om (fun _ : Fin 1 => c • a) = c • om (fun _ : Fin 1 => a) := by
  let φ := continuousMultilinearCurryFin1 ℝ (TangentSpace I x) ℝ
    (om : ContinuousMultilinearMap ℝ (fun _ : Fin 1 => TangentSpace I x) ℝ)
  have ha : (om : ContinuousMultilinearMap ℝ (fun _ : Fin 1 => TangentSpace I x) ℝ)
      (fun _ : Fin 1 => a) = φ a := by rw [continuousMultilinearCurryFin1_apply]; rfl
  have hca : (om : ContinuousMultilinearMap ℝ (fun _ : Fin 1 => TangentSpace I x) ℝ)
      (fun _ : Fin 1 => c • a) = φ (c • a) := by rw [continuousMultilinearCurryFin1_apply]; rfl
  change (om : ContinuousMultilinearMap ℝ (fun _ : Fin 1 => TangentSpace I x) ℝ)
      (fun _ => c • a) = _
  rw [hca, ha, map_smul]

set_option linter.unusedSectionVars false in
private lemma tensor0SOne_apply_neg_comp (x : M) (om : Tensor0SSpace 1 I x)
    (a : TangentSpace I x) :
    om (fun _ : Fin 1 => -a) = -om (fun _ : Fin 1 => a) := by
  have h := tensor0SOne_apply_smul_comp (I := I) x om (-1) a
  simp only [neg_smul, one_smul] at h
  exact h

set_option backward.isDefEq.respectTransparency true in
def gInvCompPairing (g₀ g₁ : SmoothRiemannianMetric I M) (x : M)
    (om : Tensor0SSpace 1 I x) : Tensor0SSpace 2 I x :=
  (show ContinuousMultilinearMap ℝ (fun _ : Fin 2 => TangentSpace I x) ℝ from
    { toFun := fun YZ => om (fun _ : Fin 1 =>
        PDE.DeTurck.connDiff (I := I) g₁ g₀ x
          (gInvRaisedEndo (I := I) g₀ g₁ x (YZ 0)) (YZ 1))
      map_update_add' := by
        have hne10 : (1 : Fin 2) ≠ 0 := by decide
        have hne01 : (0 : Fin 2) ≠ 1 := by decide
        intro _ YZ i Y Y'
        fin_cases i <;>
          · simp only [Fin.isValue, Fin.mk_zero, Fin.mk_one, Function.update_self,
              Function.update_of_ne, ne_eq, hne10, hne01, not_false_eq_true,
              ContinuousLinearMap.add_apply, map_add]
            rw [tensor0SOne_apply_add_comp (I := I) x om]
      map_update_smul' := by
        have hne10 : (1 : Fin 2) ≠ 0 := by decide
        have hne01 : (0 : Fin 2) ≠ 1 := by decide
        intro _ YZ i c Y
        fin_cases i <;>
          · simp only [Fin.isValue, Fin.mk_zero, Fin.mk_one, Function.update_self,
              Function.update_of_ne, ne_eq, hne10, hne01, not_false_eq_true,
              ContinuousLinearMap.smul_apply, map_smul]
            rw [tensor0SOne_apply_smul_comp (I := I) x om]
      cont := by
        have hpair : Continuous (fun YZ : Fin 2 → TangentSpace I x => (YZ 0, YZ 1)) :=
          (continuous_apply 0).prodMk (continuous_apply 1)
        have hRaised : Continuous (gInvRaisedEndo (I := I) g₀ g₁ x) :=
          (gInvRaisedEndo (I := I) g₀ g₁ x).continuous
        have hbil : Continuous (fun YZ : Fin 2 → TangentSpace I x =>
            PDE.DeTurck.connDiff (I := I) g₁ g₀ x
              (gInvRaisedEndo (I := I) g₀ g₁ x (YZ 0)) (YZ 1)) := by
          have hc : Continuous (fun p : TangentSpace I x × TangentSpace I x =>
              PDE.DeTurck.connDiff (I := I) g₁ g₀ x p.1 p.2) :=
            (PDE.DeTurck.connDiff (I := I) g₁ g₀ x).continuous₂
          have hcomp : Continuous (fun YZ : Fin 2 → TangentSpace I x =>
              (gInvRaisedEndo (I := I) g₀ g₁ x (YZ 0), YZ 1)) :=
            (hRaised.comp (continuous_apply 0)).prodMk (continuous_apply 1)
          exact hc.comp hcomp
        exact ((ContinuousMultilinearMap.coe_continuous
          (om : ContinuousMultilinearMap ℝ (fun _ : Fin 1 => TangentSpace I x) ℝ)).comp
          (continuous_pi (fun _ => hbil))) } : Tensor0SSpace 2 I x)

set_option linter.unusedSectionVars false in
@[simp] lemma gInvCompPairing_apply (g₀ g₁ : SmoothRiemannianMetric I M) (x : M)
    (om : Tensor0SSpace 1 I x) (YZ : Fin 2 → TangentSpace I x) :
    (gInvCompPairing (I := I) g₀ g₁ x om) YZ =
      om (fun _ : Fin 1 =>
        PDE.DeTurck.connDiff (I := I) g₁ g₀ x
          (gInvRaisedEndo (I := I) g₀ g₁ x (YZ 0)) (YZ 1)) := rfl

set_option linter.unusedSectionVars false in
lemma gInvCompPairing_add (g₀ g₁ : SmoothRiemannianMetric I M) (x : M)
    (om om' : Tensor0SSpace 1 I x) :
    gInvCompPairing (I := I) g₀ g₁ x (om + om') =
      gInvCompPairing (I := I) g₀ g₁ x om + gInvCompPairing (I := I) g₀ g₁ x om' := by
  apply ContinuousMultilinearMap.ext
  intro YZ
  exact ContinuousMultilinearMap.add_apply om om' _

set_option linter.unusedSectionVars false in
lemma gInvCompPairing_smul (g₀ g₁ : SmoothRiemannianMetric I M) (x : M)
    (c : ℝ) (om : Tensor0SSpace 1 I x) :
    gInvCompPairing (I := I) g₀ g₁ x (c • om) =
      c • gInvCompPairing (I := I) g₀ g₁ x om := by
  apply ContinuousMultilinearMap.ext
  intro YZ
  exact ContinuousMultilinearMap.smul_apply om c _

def connDiffGInvCompositeFib (g₀ g₁ : SmoothRiemannianMetric I M) (x : M) :
    TensorRSSpace 1 2 I x :=
  TensorRSSpace.ofCLM
    (LinearMap.toContinuousLinearMap
      { toFun := fun om => gInvCompPairing (I := I) g₀ g₁ x om
        map_add' := gInvCompPairing_add (I := I) g₀ g₁ x
        map_smul' := gInvCompPairing_smul (I := I) g₀ g₁ x })

set_option linter.unusedSectionVars false in
@[simp] lemma connDiffGInvCompositeFib_apply (g₀ g₁ : SmoothRiemannianMetric I M) (x : M)
    (om : Tensor0SSpace 1 I x) :
    (show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 2 I x from
        connDiffGInvCompositeFib (I := I) g₀ g₁ x) om =
      gInvCompPairing (I := I) g₀ g₁ x om := rfl

set_option backward.isDefEq.respectTransparency false in
private theorem gInvRaisedEndo_section_contMDiff (g₀ g₁ : SmoothRiemannianMetric I M)
    (Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun b : M => TotalSpace.mk' E (E := fun z : M => TangentSpace I z) b
        (gInvRaisedEndo (I := I) g₀ g₁ b (Y b))) := by
  refine (inverseMetricSharpFib_g0FlatY_contMDiff (I := I) g₀ g₁ Y).congr (fun b => ?_)
  rw [gInvRaisedEndo_apply]

set_option backward.isDefEq.respectTransparency false in
theorem connDiffGInvCompositeFib_contMDiff (g₀ g₁ : SmoothRiemannianMetric I M) :
    ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel 1 2 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel 1 2 ℝ E)
        (E := fun z : M => TensorRSSpace 1 2 I z) x
        (connDiffGInvCompositeFib (I := I) g₀ g₁ x)) := by
  classical
  apply contMDiff_clm_section_of_pointwise (I := I) (M := M)
    (F₁ := Tensor0SModel 1 ℝ E) (V₁ := fun x : M => Tensor0SSpace 1 I x)
    (F₂ := Tensor0SModel 2 ℝ E) (V₂ := fun x : M => Tensor0SSpace 2 I x)
    (φ := fun x : M => (show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 2 I x from
      connDiffGInvCompositeFib (I := I) g₀ g₁ x))
  intro om
  letI := Tensor0SBundle.tensor0SBundle_topology (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) 2
  have hsec : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel 2 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SModel 2 ℝ E)
        (E := fun z : M => Tensor0SSpace 2 I z) x
        (gInvCompPairing (I := I) g₀ g₁ x (om x))) := by
    refine (contMDiff_multilinearSection_iff_coord (𝕜 := ℝ) (F := E)
      (E := (TangentSpace I : M → Type _)) (IB := I) (n := (∞ : WithTop ℕ∞)) (Module.finBasis ℝ E)
      (fun x : M => (gInvCompPairing (I := I) g₀ g₁ x (om x) :
        Bundle.continuousMultilinearMap ℝ 2 E (TangentSpace I) x))).mpr ?_
    intro σ x₀
    set b := Module.finBasis ℝ E with hb
    set e₁ := trivializationAt E (TangentSpace I : M → Type _) x₀ with he₁def
    have he₁ : x₀ ∈ e₁.baseSet := mem_baseSet_trivializationAt E (TangentSpace I) x₀
    have hframe := e₁.isLocalFrameOn_localFrame_baseSet I (⊤ : ℕ∞) b
    obtain ⟨Y, hY⟩ := hframe.exists_contMDiffSection_eqOn_nhd e₁.open_baseSet he₁
    have hconn : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
        (fun x : M => TotalSpace.mk' E (E := fun z : M => TangentSpace I z) x
          (((PDE.DeTurck.connDiff (I := I) g₁ g₀ x)
            (gInvRaisedEndo (I := I) g₀ g₁ x (Y (σ 0) x))) (Y (σ 1) x))) :=
      PDE.DeTurck.connDiff_contMDiff (I := I) g₁ g₀
        (gInvRaisedEndo_section_contMDiff (I := I) g₀ g₁ (Y (σ 0))) (Y (σ 1)).contMDiff
    have hscalar : ContMDiffAt I 𝓘(ℝ, ℝ) ∞
        (fun x : M => Tensor0SSpace.toModel (om x)
          (fun _ : Fin 1 => ((PDE.DeTurck.connDiff (I := I) g₁ g₀ x)
            (gInvRaisedEndo (I := I) g₀ g₁ x (Y (σ 0) x))) (Y (σ 1) x))) x₀ :=
      TensorMultilinear.contMDiffAt_section_apply (n := 1) (x₀ := x₀)
        (fun x : M => om x) (om.contMDiff x₀)
        (fun _ : Fin 1 => fun x : M => ((PDE.DeTurck.connDiff (I := I) g₁ g₀ x)
          (gInvRaisedEndo (I := I) g₀ g₁ x (Y (σ 0) x))) (Y (σ 1) x))
        (fun _ => (hconn x₀))
    refine hscalar.congr_of_eventuallyEq ?_
    have h_base₁ : ∀ᶠ x in 𝓝 x₀, x ∈ e₁.baseSet := e₁.open_baseSet.mem_nhds he₁
    filter_upwards [h_base₁, hY] with x hx₁ hYx
    rw [continuousMultilinearMap_basis_repr]
    have hframe0 : e₁.symmL ℝ x (b (σ 0)) = (Y (σ 0)) x := by
      rw [hYx (σ 0), Trivialization.localFrame_apply_of_mem_baseSet (hx := hx₁)]
      simp [Trivialization.basisAt]
    have hframe1 : e₁.symmL ℝ x (b (σ 1)) = (Y (σ 1)) x := by
      rw [hYx (σ 1), Trivialization.localFrame_apply_of_mem_baseSet (hx := hx₁)]
      simp [Trivialization.basisAt]
    change (gInvCompPairing (I := I) g₀ g₁ x (om x))
        (fun j : Fin 2 => e₁.symmL ℝ x (b (σ j))) = _
    rw [gInvCompPairing_apply]
    rw [Tensor0SSpace.toModel, tensor0SSpace_continuousLinearEquiv_apply]
    rw [hframe0, hframe1]
    rfl
  refine hsec.congr ?_
  intro x
  rfl

set_option backward.isDefEq.respectTransparency false in
def connDiffGInvComposite (g₀ g₁ : SmoothRiemannianMetric I M) : SmoothCcTensor g₀ 1 2 where
  toSection :=
    { toFun := fun x : M => connDiffGInvCompositeFib (I := I) g₀ g₁ x
      contMDiff_toFun := connDiffGInvCompositeFib_contMDiff (I := I) g₀ g₁ }
  hasCompactSupport := HasCompactSupport.of_compactSpace _

set_option backward.isDefEq.respectTransparency false in
set_option linter.unusedSectionVars false in
@[simp] lemma connDiffGInvComposite_toSection (g₀ g₁ : SmoothRiemannianMetric I M) (x : M) :
    (connDiffGInvComposite (I := I) g₀ g₁).toSection x =
      connDiffGInvCompositeFib (I := I) g₀ g₁ x := rfl

set_option backward.isDefEq.respectTransparency false in
set_option linter.unusedSectionVars false in
lemma connDiffGInvComposite_pairing_apply (g₀ g₁ : SmoothRiemannianMetric I M) (x : M)
    (om : Tensor0SSpace 1 I x) (YZ : Fin 2 → TangentSpace I x) :
    ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 2 I x from
        (connDiffGInvComposite (I := I) g₀ g₁).toSection x) om) YZ =
      om (fun _ : Fin 1 =>
        PDE.DeTurck.connDiff (I := I) g₁ g₀ x
          (gInvRaisedEndo (I := I) g₀ g₁ x (YZ 0)) (YZ 1)) := by
  rw [connDiffGInvComposite_toSection, connDiffGInvCompositeFib_apply, gInvCompPairing_apply]

set_option backward.isDefEq.respectTransparency false in
set_option linter.unusedSectionVars false in
theorem covGrad_gInvDiffSlotCoeff_eq_appCcRS_composite
    (g₀ g₁ : SmoothRiemannianMetric I M)
    (Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) (v : TangentSpace I x)
    (om : Tensor0SSpace 1 I x) :
    om (fun _ : Fin 1 =>
        ((endoCovariantDerivative (I := I) (M := M) g₀)
          (gInvDiffRaisedEndoField (I := I) g₀ g₁) x v) (Y x)) =
      - ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 2 I x from
            (connDiffGInvComposite (I := I) g₀ g₁).toSection x) om)
            (fun j : Fin 2 => if j = 0 then Y x else v)
      + om (fun _ : Fin 1 =>
          inverseMetricSharpFib (I := I) g₁ x
            (dualToCotangent (I := I)
              (-(cotangentToCLM (I := I) (g0FlatCLM (I := I) g₀ x (Y x))).comp
                  ((PDE.DeTurck.connDiff (I := I) g₁ g₀ x).flip v)).toLinearMap)) := by
  rw [covGrad_gInvDiffSlotCoeff_endoCov_apply (I := I) g₀ g₁ Y x v]
  rw [tensor0SOne_apply_add_comp (I := I) x om,
    tensor0SOne_apply_neg_comp (I := I) x om]
  rw [connDiffGInvComposite_pairing_apply (I := I) g₀ g₁ x om
    (fun j : Fin 2 => if j = 0 then Y x else v)]
  simp only [Fin.isValue, if_true, if_neg (by decide : (1 : Fin 2) ≠ 0)]

open TensorMultilinear
set_option linter.unusedSectionVars false in
private lemma curry_symm_smul_aux (s : ℕ) (x : M) (c : ℝ)
    (a : TangentSpace I x →L[ℝ] Tensor0SSpace (s+1) I x) :
    (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) (s + 1) x).symm (c • a) =
      c • (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) (s + 1) x).symm a := by
  apply Tensor0SSpace.toModel_injective (I := I) (M := M)
  ext vv
  rw [show vv = Fin.cons (vv 0) (Matrix.vecTail vv) from (Fin.cons_self_tail vv).symm]
  rw [← tensor0S_curry_apply_eval (T := (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) (s + 1) x).symm (c • a))]
  simp only [ContinuousLinearEquiv.apply_symm_apply, ContinuousLinearMap.smul_apply,
    Tensor0SSpace.toModel_smul, ContinuousMultilinearMap.smul_apply]
  rw [← tensor0S_curry_apply_eval (T := (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) (s + 1) x).symm a)]
  simp only [ContinuousLinearEquiv.apply_symm_apply]

set_option linter.unusedSectionVars false in
private lemma curry_symm_add_aux (s : ℕ) (x : M)
    (a b : TangentSpace I x →L[ℝ] Tensor0SSpace (s+1) I x) :
    (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) (s + 1) x).symm (a + b) =
      (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) (s + 1) x).symm a +
        (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) (s + 1) x).symm b := by
  apply Tensor0SSpace.toModel_injective (I := I) (M := M)
  ext vv
  rw [show vv = Fin.cons (vv 0) (Matrix.vecTail vv) from (Fin.cons_self_tail vv).symm]
  rw [← tensor0S_curry_apply_eval (T := (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) (s + 1) x).symm (a + b))]
  simp only [ContinuousLinearEquiv.apply_symm_apply, ContinuousLinearMap.add_apply,
    Tensor0SSpace.toModel_add, ContinuousMultilinearMap.add_apply]
  rw [← tensor0S_curry_apply_eval (T := (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) (s + 1) x).symm a),
    ← tensor0S_curry_apply_eval (T := (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) (s + 1) x).symm b)]
  simp only [ContinuousLinearEquiv.apply_symm_apply]

def armCurryCLM (s : ℕ) (x : M)
    (Arm : TangentSpace I x →L[ℝ] (TangentSpace I x →L[ℝ] TangentSpace I x))
    (D : Tensor0SSpace (s + 1) I x) : TangentSpace I x →L[ℝ] Tensor0SSpace (s + 1) I x :=
  haveI : FiniteDimensional ℝ (Tensor0SSpace (s + 1) I x) := inferInstance
  LinearMap.toContinuousLinearMap
    { toFun := fun v0 => slotInsertEndoFib (I := I) (M := M) (s + 1) 0 x (Arm v0) D
      map_add' := fun a b => by
        rw [map_add (Arm), slotInsertEndoFib_add_left (I := I) (M := M) (s+1) 0 x (Arm a) (Arm b),
          ContinuousLinearMap.add_apply]
      map_smul' := fun c a => by
        rw [map_smul (Arm)]
        rw [slotInsertEndoFib_smul_left (I := I) (M := M) (s+1) 0 x c (Arm a)]
        rfl }

set_option linter.unusedSectionVars false in
@[simp] lemma armCurryCLM_apply (s : ℕ) (x : M)
    (Arm : TangentSpace I x →L[ℝ] (TangentSpace I x →L[ℝ] TangentSpace I x))
    (D : Tensor0SSpace (s + 1) I x) (v0 : TangentSpace I x) :
    armCurryCLM (I := I) (M := M) s x Arm D v0 =
      slotInsertEndoFib (I := I) (M := M) (s + 1) 0 x (Arm v0) D := rfl

set_option linter.unusedSectionVars false in
lemma armCurryCLM_add (s : ℕ) (x : M)
    (Arm : TangentSpace I x →L[ℝ] (TangentSpace I x →L[ℝ] TangentSpace I x))
    (D D' : Tensor0SSpace (s + 1) I x) :
    armCurryCLM (I := I) (M := M) s x Arm (D + D') =
      armCurryCLM (I := I) (M := M) s x Arm D + armCurryCLM (I := I) (M := M) s x Arm D' := by
  apply ContinuousLinearMap.ext; intro v0
  simp only [ContinuousLinearMap.add_apply, armCurryCLM_apply, map_add]

set_option linter.unusedSectionVars false in
lemma armCurryCLM_smul (s : ℕ) (x : M) (c : ℝ)
    (Arm : TangentSpace I x →L[ℝ] (TangentSpace I x →L[ℝ] TangentSpace I x))
    (D : Tensor0SSpace (s + 1) I x) :
    armCurryCLM (I := I) (M := M) s x Arm (c • D) =
      c • armCurryCLM (I := I) (M := M) s x Arm D := by
  apply ContinuousLinearMap.ext; intro v0
  simp only [ContinuousLinearMap.smul_apply, armCurryCLM_apply, map_smul]

def armSlotFib (s : ℕ) (x : M)
    (Arm : TangentSpace I x →L[ℝ] (TangentSpace I x →L[ℝ] TangentSpace I x)) :
    Tensor0SSpace (s + 1) I x →L[ℝ] Tensor0SSpace (s + 1 + 1) I x :=
  haveI : FiniteDimensional ℝ (Tensor0SSpace (s + 1) I x) := inferInstance
  LinearMap.toContinuousLinearMap
    { toFun := fun D => (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) (s + 1) x).symm
        (armCurryCLM (I := I) (M := M) s x Arm D)
      map_add' := fun D D' => by
        rw [armCurryCLM_add, curry_symm_add_aux]
      map_smul' := fun c D => by
        rw [armCurryCLM_smul, curry_symm_smul_aux]; rfl }

set_option linter.unusedSectionVars false in
@[simp] lemma armSlotFib_apply (s : ℕ) (x : M)
    (Arm : TangentSpace I x →L[ℝ] (TangentSpace I x →L[ℝ] TangentSpace I x))
    (D : Tensor0SSpace (s + 1) I x) :
    armSlotFib (I := I) (M := M) s x Arm D =
      (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) (s + 1) x).symm
        (armCurryCLM (I := I) (M := M) s x Arm D) := rfl

set_option linter.unusedSectionVars false in
lemma armSlotFib_apply_eval (s : ℕ) (x : M)
    (Arm : TangentSpace I x →L[ℝ] (TangentSpace I x →L[ℝ] TangentSpace I x))
    (D : Tensor0SSpace (s + 1) I x) (v : Fin (s + 1 + 1) → TangentSpace I x) :
    Tensor0SSpace.toModel (armSlotFib (I := I) (M := M) s x Arm D) v =
      Tensor0SSpace.toModel
        (slotInsertEndoFib (I := I) (M := M) (s + 1) 0 x (Arm (v 0)) D) (Matrix.vecTail v) := by
  rw [armSlotFib_apply]
  have hkey := tensor0S_curry_apply_eval (I := I) (M := M) (n := s + 1)
    (T := (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) (s + 1) x).symm
      (armCurryCLM (I := I) (M := M) s x Arm D)) (v0 := v 0) (vs := Matrix.vecTail v)
  rw [ContinuousLinearEquiv.apply_symm_apply, armCurryCLM_apply] at hkey
  conv_lhs => rw [show v = Fin.cons (v 0) (Matrix.vecTail v) from (Fin.cons_self_tail v).symm]
  exact hkey.symm

set_option linter.unusedSectionVars false in
private lemma fiberComponent_armSlotFib_eq
    (g₀ : SmoothRiemannianMetric I M) (x : M) (s : ℕ)
    (Arm : TangentSpace I x →L[ℝ] (TangentSpace I x →L[ℝ] TangentSpace I x))
    {n : ℕ} (e : Fin n → TangentSpace I x)
    (horth : ∀ i j : Fin n, g₀.inner x (e i) (e j) = if i = j then (1 : ℝ) else 0)
    (K : Fin (s + 1) → Fin n) (J : Fin (s + 1 + 1) → Fin n) :
    fiberNormSqComponent (I := I) (M := M) g₀ x (s + 1) (s + 1 + 1)
        (show TensorRSSpace (s + 1) (s + 1 + 1) I x from
          TensorRSSpace.ofCLM (armSlotFib (I := I) (M := M) s x Arm)) n e K J =
      g₀.inner x (e (K 0)) (Arm (e (J 0)) (e (J (Fin.succ 0)))) *
        ∏ l ∈ Finset.univ.erase (0 : Fin (s + 1)),
          (if K l = J (Fin.succ l) then (1 : ℝ) else 0) := by
  have hcomp : fiberNormSqComponent (I := I) (M := M) g₀ x (s + 1) (s + 1 + 1)
      (show TensorRSSpace (s + 1) (s + 1 + 1) I x from
        TensorRSSpace.ofCLM (armSlotFib (I := I) (M := M) s x Arm)) n e K J =
      Tensor0SSpace.toModel
        (armSlotFib (I := I) (M := M) s x Arm (coframeS (I := I) (M := M) g₀ x (s + 1) e K))
        (fun l => e (J l)) := by
    unfold fiberNormSqComponent coframeS; rfl
  rw [hcomp, armSlotFib_apply_eval, slotInsertEndoFib_apply_eval]
  change coframeS (I := I) (M := M) g₀ x (s + 1) e K
        (Function.update (Matrix.vecTail (fun l => e (J l))) 0
          (Arm (e (J 0)) (Matrix.vecTail (fun l => e (J l)) 0))) = _
  rw [coframeS_apply]
  rw [← Finset.prod_erase_mul Finset.univ
    (fun k => g₀.inner x (e (K k))
      (Function.update (Matrix.vecTail (fun l => e (J l))) 0
        (Arm (e (J 0)) (Matrix.vecTail (fun l => e (J l)) 0)) k))
    (Finset.mem_univ (0 : Fin (s + 1)))]
  rw [Function.update_self]
  have hvt0 : Matrix.vecTail (fun l => e (J l)) (0 : Fin (s + 1)) = e (J (Fin.succ 0)) := rfl
  rw [hvt0, mul_comm]
  congr 1
  refine Finset.prod_congr rfl (fun l hl => ?_)
  have hlk : l ≠ (0 : Fin (s + 1)) := Finset.ne_of_mem_erase hl
  rw [Function.update_of_ne hlk]
  change g₀.inner x (e (K l)) (Matrix.vecTail (fun l => e (J l)) l) = _
  rw [show Matrix.vecTail (fun l => e (J l)) l = e (J (Fin.succ l)) from rfl,
    horth (K l) (J (Fin.succ l))]

set_option linter.unusedSectionVars false in
set_option linter.unusedVariables false in
private lemma sum_compSq_armSlotFib_eq_normSq
    (g₀ : SmoothRiemannianMetric I M) (x : M) (s : ℕ)
    (Arm : TangentSpace I x →L[ℝ] (TangentSpace I x →L[ℝ] TangentSpace I x))
    {n : ℕ} (e : Fin n → TangentSpace I x)
    (horth : ∀ i j : Fin n, g₀.inner x (e i) (e j) = if i = j then (1 : ℝ) else 0)
    (hpars : ∀ v : TangentSpace I x, ∑ i : Fin n, g₀.inner x (e i) v ^ 2 = g₀.inner x v v)
    (J : Fin (s + 1 + 1) → Fin n) :
    (∑ K : Fin (s + 1) → Fin n,
        (fiberNormSqComponent (I := I) (M := M) g₀ x (s + 1) (s + 1 + 1)
          (show TensorRSSpace (s + 1) (s + 1 + 1) I x from
            TensorRSSpace.ofCLM (armSlotFib (I := I) (M := M) s x Arm)) n e K J) ^ 2) =
      g₀.inner x (Arm (e (J 0)) (e (J (Fin.succ 0)))) (Arm (e (J 0)) (e (J (Fin.succ 0)))) := by
  classical
  set w : TangentSpace I x := Arm (e (J 0)) (e (J (Fin.succ 0))) with hw_def
  have hcompsq : ∀ K : Fin (s + 1) → Fin n,
      (fiberNormSqComponent (I := I) (M := M) g₀ x (s + 1) (s + 1 + 1)
        (show TensorRSSpace (s + 1) (s + 1 + 1) I x from
          TensorRSSpace.ofCLM (armSlotFib (I := I) (M := M) s x Arm)) n e K J) ^ 2 =
        (g₀.inner x (e (K 0)) w) ^ 2 *
          ∏ l ∈ Finset.univ.erase (0 : Fin (s + 1)),
            (if K l = J (Fin.succ l) then (1 : ℝ) else 0) := by
    intro K
    rw [fiberComponent_armSlotFib_eq (I := I) g₀ x s Arm e horth K J, ← hw_def]
    rw [mul_pow]
    congr 1
    rw [← Finset.prod_pow]
    refine Finset.prod_congr rfl (fun l _ => ?_)
    by_cases hkj : K l = J (Fin.succ l)
    · simp [hkj]
    · simp [hkj]
  rw [Finset.sum_congr rfl (fun K _ => hcompsq K)]
  set ee := Equiv.funSplitAt (0 : Fin (s + 1)) (Fin n) with hee
  rw [← (Equiv.sum_comp ee.symm
    (fun K : Fin (s + 1) → Fin n => (g₀.inner x (e (K 0)) w) ^ 2 *
      ∏ l ∈ Finset.univ.erase (0 : Fin (s + 1)),
        (if K l = J (Fin.succ l) then (1 : ℝ) else 0)))]
  rw [Fintype.sum_prod_type]
  have hkval : ∀ (m : Fin n) (ρ : {i : Fin (s + 1) // i ≠ 0} → Fin n),
      (ee.symm (m, ρ)) 0 = m := by
    intro m ρ; rw [hee]; simp [Equiv.funSplitAt, Equiv.piSplitAt]
  have hinner : ∀ m : Fin n,
      (∑ ρ : {i : Fin (s + 1) // i ≠ 0} → Fin n,
        (g₀.inner x (e ((ee.symm (m, ρ)) 0)) w) ^ 2 *
          ∏ l ∈ Finset.univ.erase (0 : Fin (s + 1)),
            (if (ee.symm (m, ρ)) l = J (Fin.succ l) then (1 : ℝ) else 0)) =
        (g₀.inner x (e m) w) ^ 2 := by
    intro m
    have hcoe : ∀ (ρ : {i : Fin (s + 1) // i ≠ 0} → Fin n) (l : Fin (s + 1)) (hl : l ≠ 0),
        (ee.symm (m, ρ)) l = ρ ⟨l, hl⟩ := by
      intro ρ l hl
      rw [hee]; simp [Equiv.funSplitAt, Equiv.piSplitAt, hl]
    have hindic : ∀ ρ : {i : Fin (s + 1) // i ≠ 0} → Fin n,
        (∏ l ∈ Finset.univ.erase (0 : Fin (s + 1)),
          (if (ee.symm (m, ρ)) l = J (Fin.succ l) then (1 : ℝ) else 0)) =
          (if ρ = (fun j : {i : Fin (s + 1) // i ≠ 0} => J (Fin.succ (j : Fin (s + 1))))
            then (1 : ℝ) else 0) := by
      intro ρ
      by_cases hρ : ρ = (fun j : {i : Fin (s + 1) // i ≠ 0} => J (Fin.succ (j : Fin (s + 1))))
      · rw [if_pos hρ]
        refine Finset.prod_eq_one (fun l hl => ?_)
        have hlk : l ≠ (0 : Fin (s + 1)) := Finset.ne_of_mem_erase hl
        rw [hcoe ρ l hlk, hρ, if_pos rfl]
      · rw [if_neg hρ]
        obtain ⟨j, hj⟩ : ∃ j : {i : Fin (s + 1) // i ≠ 0},
            ρ j ≠ J (Fin.succ (j : Fin (s + 1))) := by
          by_contra hcon
          exact hρ (funext (fun j => not_not.mp (fun h => hcon ⟨j, h⟩)))
        refine Finset.prod_eq_zero (i := (j : Fin (s + 1)))
          (Finset.mem_erase.mpr ⟨j.2, Finset.mem_univ _⟩) ?_
        rw [hcoe ρ (j : Fin (s + 1)) j.2, if_neg hj]
    rw [Finset.sum_congr rfl (fun ρ _ => by rw [hkval m ρ, hindic ρ] :
      ∀ ρ ∈ Finset.univ,
        (g₀.inner x (e ((ee.symm (m, ρ)) 0)) w) ^ 2 *
          ∏ l ∈ Finset.univ.erase (0 : Fin (s + 1)),
            (if (ee.symm (m, ρ)) l = J (Fin.succ l) then (1 : ℝ) else 0) =
        (g₀.inner x (e m) w) ^ 2 *
          (if ρ = (fun j : {i : Fin (s + 1) // i ≠ 0} => J (Fin.succ (j : Fin (s + 1))))
            then (1 : ℝ) else 0))]
    rw [← Finset.mul_sum,
      Finset.sum_ite_eq' Finset.univ
        (fun j : {i : Fin (s + 1) // i ≠ 0} => J (Fin.succ (j : Fin (s + 1)))) (fun _ => (1 : ℝ))]
    simp
  rw [Finset.sum_congr rfl (fun m _ => hinner m)]
  exact hpars w

set_option backward.isDefEq.respectTransparency false in
set_option linter.unusedSectionVars false in
set_option linter.unusedVariables false in
theorem riemannianFiberNormSq_armSlotFib_le
    (g₀ : SmoothRiemannianMetric I M) (x : M) (s : ℕ)
    (Arm : TangentSpace I x →L[ℝ] (TangentSpace I x →L[ℝ] TangentSpace I x)) (B : ℝ)
    (hArm : ∀ a b : TangentSpace I x, g₀.inner x a a = 1 → g₀.inner x b b = 1 →
      g₀.inner x (Arm a b) (Arm a b) ≤ B)
    (hB : 0 ≤ B) :
    riemannianFiberNormSq (I := I) (M := M) g₀ (s + 1) (s + 1 + 1) x
        (show TensorRSSpace (s + 1) (s + 1 + 1) I x from
          TensorRSSpace.ofCLM (armSlotFib (I := I) (M := M) s x Arm)) ≤
      ((Module.finrank ℝ E : ℝ)) ^ (s + 1 + 1) * B := by
  classical
  obtain ⟨n, e, bse, hn, hbse, horth, hpars, hrepr_v, hsum⟩ :=
    tangent_orthonormalBasis_witness (I := I) (M := M) g₀ x
  have hnE : n = Module.finrank ℝ E := by rw [hn]; rfl
  rw [rfns_rs_eq_sum_componentSq_of_basis (I := I) (M := M) g₀ (s + 1) (s + 1 + 1) x
    (show TensorRSSpace (s + 1) (s + 1 + 1) I x from
      TensorRSSpace.ofCLM (armSlotFib (I := I) (M := M) s x Arm)) e bse hnE hbse horth]
  rw [Finset.sum_comm]
  have hsumeq : (∑ J : Fin (s + 1 + 1) → Fin n, ∑ K : Fin (s + 1) → Fin n,
        (fiberNormSqComponent (I := I) (M := M) g₀ x (s + 1) (s + 1 + 1)
          (show TensorRSSpace (s + 1) (s + 1 + 1) I x from
            TensorRSSpace.ofCLM (armSlotFib (I := I) (M := M) s x Arm)) n e K J) ^ 2) =
      ∑ J : Fin (s + 1 + 1) → Fin n,
        g₀.inner x (Arm (e (J 0)) (e (J (Fin.succ 0)))) (Arm (e (J 0)) (e (J (Fin.succ 0)))) := by
    refine Finset.sum_congr rfl (fun J _ => ?_)
    exact sum_compSq_armSlotFib_eq_normSq (I := I) g₀ x s Arm e horth hpars J
  rw [hsumeq]
  have hJbound : ∀ J : Fin (s + 1 + 1) → Fin n,
      g₀.inner x (Arm (e (J 0)) (e (J (Fin.succ 0)))) (Arm (e (J 0)) (e (J (Fin.succ 0)))) ≤ B := by
    intro J
    refine hArm (e (J 0)) (e (J (Fin.succ 0))) ?_ ?_
    · rw [horth (J 0) (J 0)]; simp
    · rw [horth (J (Fin.succ 0)) (J (Fin.succ 0))]; simp
  calc (∑ J : Fin (s + 1 + 1) → Fin n,
          g₀.inner x (Arm (e (J 0)) (e (J (Fin.succ 0)))) (Arm (e (J 0)) (e (J (Fin.succ 0)))))
      ≤ ∑ _J : Fin (s + 1 + 1) → Fin n, B := Finset.sum_le_sum (fun J _ => hJbound J)
    _ = ((Module.finrank ℝ E : ℝ)) ^ (s + 1 + 1) * B := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
          Fintype.card_fin, nsmul_eq_mul, ← hnE]
        push_cast; ring

set_option backward.isDefEq.respectTransparency false in
set_option linter.unusedSectionVars false in
private lemma rfns_armSlotFib_eq_sum_normSq_frame
    (g₀ : SmoothRiemannianMetric I M) (x : M) (s : ℕ)
    (Arm : TangentSpace I x →L[ℝ] (TangentSpace I x →L[ℝ] TangentSpace I x))
    {n : ℕ} (e : Fin n → TangentSpace I x)
    (bse : Module.Basis (Fin n) ℝ (TangentSpace I x))
    (hn : n = Module.finrank ℝ E) (hbse : ∀ i : Fin n, bse i = e i)
    (horth : ∀ i j : Fin n, g₀.inner x (e i) (e j) = if i = j then (1 : ℝ) else 0)
    (hpars : ∀ v : TangentSpace I x, ∑ i : Fin n, g₀.inner x (e i) v ^ 2 = g₀.inner x v v) :
    riemannianFiberNormSq (I := I) (M := M) g₀ (s + 1) (s + 1 + 1) x
        (show TensorRSSpace (s + 1) (s + 1 + 1) I x from
          TensorRSSpace.ofCLM (armSlotFib (I := I) (M := M) s x Arm)) =
      (n : ℝ) ^ s * ∑ p : Fin n × Fin n,
        g₀.inner x (Arm (e p.1) (e p.2)) (Arm (e p.1) (e p.2)) := by
  classical
  rw [rfns_rs_eq_sum_componentSq_of_basis (I := I) (M := M) g₀ (s + 1) (s + 1 + 1) x
    (show TensorRSSpace (s + 1) (s + 1 + 1) I x from
      TensorRSSpace.ofCLM (armSlotFib (I := I) (M := M) s x Arm)) e bse hn hbse horth]
  rw [Finset.sum_comm]
  have hsumeq : (∑ J : Fin (s + 1 + 1) → Fin n, ∑ K : Fin (s + 1) → Fin n,
        (fiberNormSqComponent (I := I) (M := M) g₀ x (s + 1) (s + 1 + 1)
          (show TensorRSSpace (s + 1) (s + 1 + 1) I x from
            TensorRSSpace.ofCLM (armSlotFib (I := I) (M := M) s x Arm)) n e K J) ^ 2) =
      ∑ J : Fin (s + 1 + 1) → Fin n,
        g₀.inner x (Arm (e (J 0)) (e (J (Fin.succ 0)))) (Arm (e (J 0)) (e (J (Fin.succ 0)))) :=
    Finset.sum_congr rfl (fun J _ => sum_compSq_armSlotFib_eq_normSq (I := I) g₀ x s Arm e horth hpars J)
  rw [hsumeq]
  set F : Fin n → Fin n → ℝ := fun a b => g₀.inner x (Arm (e a) (e b)) (Arm (e a) (e b)) with hF
  have hJF : ∀ J : Fin (s + 1 + 1) → Fin n,
      g₀.inner x (Arm (e (J 0)) (e (J (Fin.succ 0)))) (Arm (e (J 0)) (e (J (Fin.succ 0)))) =
        F (J 0) (J (Fin.succ 0)) := fun J => rfl
  rw [Finset.sum_congr rfl (fun J _ => hJF J)]
  rw [← Fintype.sum_equiv (Fin.consEquiv (fun _ : Fin (s + 1 + 1) => Fin n))
        (fun pr : Fin n × (Fin (s + 1) → Fin n) => F pr.1 (pr.2 0))
        (fun J : Fin (s + 1 + 1) → Fin n => F (J 0) (J (Fin.succ 0)))
        (fun pr => by
          simp only [Fin.consEquiv_apply]
          rw [Fin.cons_zero, show (Fin.succ 0 : Fin (s + 1 + 1)) = (0 : Fin (s + 1)).succ from rfl,
            Fin.cons_succ])]
  rw [Fintype.sum_prod_type]
  have hinner : ∀ a : Fin n,
      (∑ r : Fin (s + 1) → Fin n, F a (r 0)) = (n : ℝ) ^ s * ∑ b : Fin n, F a b := by
    intro a
    rw [← Fintype.sum_equiv (Fin.consEquiv (fun _ : Fin (s + 1) => Fin n))
          (fun pr : Fin n × (Fin s → Fin n) => F a pr.1)
          (fun r : Fin (s + 1) → Fin n => F a (r 0))
          (fun pr => by simp [Fin.consEquiv])]
    rw [Fintype.sum_prod_type]
    rw [Finset.sum_congr rfl (fun b _ => by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin,
        nsmul_eq_mul, Nat.cast_pow] :
      ∀ b ∈ Finset.univ, (∑ _t : Fin s → Fin n, F a b) = (n : ℝ) ^ s * F a b)]
    rw [← Finset.mul_sum]
  rw [Finset.sum_congr rfl (fun a _ => hinner a)]
  rw [← Finset.mul_sum]
  congr 1
  rw [Fintype.sum_prod_type]

set_option backward.isDefEq.respectTransparency false in
set_option linter.unusedSectionVars false in
theorem riemannianFiberNormSq_armSlotFib_spectator_eq
    (g₀ : SmoothRiemannianMetric I M) (x : M) (s : ℕ)
    (Arm : TangentSpace I x →L[ℝ] (TangentSpace I x →L[ℝ] TangentSpace I x)) :
    riemannianFiberNormSq (I := I) (M := M) g₀ (s + 1) (s + 1 + 1) x
        (show TensorRSSpace (s + 1) (s + 1 + 1) I x from
          TensorRSSpace.ofCLM (armSlotFib (I := I) (M := M) s x Arm)) =
      (Module.finrank ℝ E : ℝ) ^ s *
        riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + 1) x
          (show TensorRSSpace 1 (1 + 1) I x from
            TensorRSSpace.ofCLM (armSlotFib (I := I) (M := M) 0 x Arm)) := by
  classical
  obtain ⟨n, e, bse, hn, hbse, horth, hpars, hrepr_v, hsum⟩ :=
    tangent_orthonormalBasis_witness (I := I) (M := M) g₀ x
  have hnE : n = Module.finrank ℝ E := by rw [hn]; rfl
  rw [rfns_armSlotFib_eq_sum_normSq_frame (I := I) g₀ x s Arm e bse hnE hbse horth hpars]
  rw [rfns_armSlotFib_eq_sum_normSq_frame (I := I) g₀ x 0 Arm e bse hnE hbse horth hpars]
  rw [pow_zero, one_mul]
  rw [show ((Module.finrank ℝ E : ℝ)) ^ s = (n : ℝ) ^ s from by rw [hnE]]

set_option backward.isDefEq.respectTransparency false in
theorem armSlotFib_contMDiff (s : ℕ)
    (Arm : Π x : M, TangentSpace I x →L[ℝ] (TangentSpace I x →L[ℝ] TangentSpace I x))
    (harm : ∀ (V0 W : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯),
      ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
        (fun x : M => TotalSpace.mk' E (E := fun z : M => TangentSpace I z) x
          (Arm x (V0 x) (W x)))) :
    ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel (s + 1) (s + 1 + 1) ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel (s + 1) (s + 1 + 1) ℝ E)
        (E := fun z : M => TensorRSSpace (s + 1) (s + 1 + 1) I z) x
        (TensorRSSpace.ofCLM (armSlotFib (I := I) (M := M) s x (Arm x)))) := by
  classical
  apply contMDiff_clm_section_of_pointwise (I := I) (M := M)
    (F₁ := Tensor0SModel (s + 1) ℝ E) (V₁ := fun x : M => Tensor0SSpace (s + 1) I x)
    (F₂ := Tensor0SModel (s + 1 + 1) ℝ E) (V₂ := fun x : M => Tensor0SSpace (s + 1 + 1) I x)
    (φ := fun x : M => (show Tensor0SSpace (s + 1) I x →L[ℝ] Tensor0SSpace (s + 1 + 1) I x from
      armSlotFib (I := I) (M := M) s x (Arm x)))
  intro D
  letI := Tensor0SBundle.tensor0SBundle_topology (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) (s + 1 + 1)
  have hsec : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel (s + 1 + 1) ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SModel (s + 1 + 1) ℝ E)
        (E := fun z : M => Tensor0SSpace (s + 1 + 1) I z) x
        (armSlotFib (I := I) (M := M) s x (Arm x) (D x))) := by
    refine (contMDiff_multilinearSection_iff_coord (𝕜 := ℝ) (F := E)
      (E := (TangentSpace I : M → Type _)) (IB := I) (n := (∞ : WithTop ℕ∞)) (Module.finBasis ℝ E)
      (fun x : M => (armSlotFib (I := I) (M := M) s x (Arm x) (D x) :
        Bundle.continuousMultilinearMap ℝ (s + 1 + 1) E (TangentSpace I) x))).mpr ?_
    intro σ x₀
    set b := Module.finBasis ℝ E with hb
    set e₁ := trivializationAt E (TangentSpace I : M → Type _) x₀ with he₁def
    have he₁ : x₀ ∈ e₁.baseSet := mem_baseSet_trivializationAt E (TangentSpace I) x₀
    have hframe := e₁.isLocalFrameOn_localFrame_baseSet I (⊤ : ℕ∞) b
    obtain ⟨Y, hY⟩ := hframe.exists_contMDiffSection_eqOn_nhd e₁.open_baseSet he₁
    have harmField : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
        (fun x : M => TotalSpace.mk' E (E := fun z : M => TangentSpace I z) x
          (Arm x (Y (σ 0) x) (Y (σ 1) x))) := harm (Y (σ 0)) (Y (σ 1))
    have hscalar : ContMDiffAt I 𝓘(ℝ, ℝ) ∞
        (fun x : M => Tensor0SSpace.toModel (D x)
          (Function.update (fun i : Fin (s + 1) => Y (σ (Fin.succ i)) x) 0
            (Arm x (Y (σ 0) x) (Y (σ 1) x)))) x₀ := by
      refine TensorMultilinear.contMDiffAt_section_apply (n := s + 1) (x₀ := x₀)
        (fun x : M => D x) (D.contMDiff x₀)
        (fun i : Fin (s + 1) => fun x : M =>
          Function.update (fun j : Fin (s + 1) => Y (σ (Fin.succ j)) x) 0
            (Arm x (Y (σ 0) x) (Y (σ 1) x)) i) ?_
      intro i
      by_cases hi : i = 0
      · subst hi
        refine (harmField x₀).congr_of_eventuallyEq (Filter.Eventually.of_forall (fun x => ?_))
        simp only [Function.update_self]
      · refine ((Y (σ (Fin.succ i))).contMDiff x₀).congr_of_eventuallyEq
          (Filter.Eventually.of_forall (fun x => ?_))
        simp only [Function.update_of_ne hi]
    refine hscalar.congr_of_eventuallyEq ?_
    have h_base₁ : ∀ᶠ x in 𝓝 x₀, x ∈ e₁.baseSet := e₁.open_baseSet.mem_nhds he₁
    filter_upwards [h_base₁, hY] with x hx₁ hYx
    rw [continuousMultilinearMap_basis_repr]
    have hframeS : ∀ k : Fin (s + 1 + 1), e₁.symmL ℝ x (b (σ k)) = (Y (σ k)) x := by
      intro k
      rw [hYx (σ k), Trivialization.localFrame_apply_of_mem_baseSet (hx := hx₁)]
      simp [Trivialization.basisAt]
    change Tensor0SSpace.toModel (armSlotFib (I := I) (M := M) s x (Arm x) (D x))
        (fun j : Fin (s + 1 + 1) => e₁.symmL ℝ x (b (σ j))) = _
    rw [armSlotFib_apply_eval]
    rw [slotInsertEndoFib_apply_eval]
    rw [Tensor0SSpace.toModel]
    have htail0 : Matrix.vecTail (fun j : Fin (s + 1 + 1) => e₁.symmL ℝ x (b (σ j))) 0 =
        (Y (σ 1)) x := by
      show e₁.symmL ℝ x (b (σ (Fin.succ 0))) = _
      rw [hframeS (Fin.succ 0)]; rfl
    have hupd : Function.update (Matrix.vecTail
          (fun j : Fin (s + 1 + 1) => e₁.symmL ℝ x (b (σ j)))) 0
          (Arm x (e₁.symmL ℝ x (b (σ 0)))
            (Matrix.vecTail (fun j : Fin (s + 1 + 1) => e₁.symmL ℝ x (b (σ j))) 0)) =
        Function.update (fun i : Fin (s + 1) => (Y (σ (Fin.succ i))) x) 0
          (Arm x ((Y (σ 0)) x) ((Y (σ 1)) x)) := by
      funext j
      by_cases hj : j = 0
      · subst hj
        simp only [Function.update_self, hframeS 0, htail0]
      · rw [Function.update_of_ne hj, Function.update_of_ne hj]
        show e₁.symmL ℝ x (b (σ (Fin.succ j))) = (Y (σ (Fin.succ j))) x
        rw [hframeS (Fin.succ j)]
    rw [hupd]
  refine hsec.congr ?_
  intro x
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option linter.unusedSectionVars false in
theorem endoCov_gInvDiffRaisedField_fibrewise
    (g₀ g₁ : SmoothRiemannianMetric I M) (x : M)
    (v0 w : TangentSpace I x) :
    ((endoCovariantDerivative (I := I) (M := M) g₀)
        (gInvDiffRaisedEndoField (I := I) g₀ g₁) x v0) w =
      - PDE.DeTurck.connDiff (I := I) g₁ g₀ x (gInvRaisedEndo (I := I) g₀ g₁ x w) v0
      + inverseMetricSharpFib (I := I) g₁ x
          (dualToCotangent (I := I)
            (-(cotangentToCLM (I := I) (g0FlatCLM (I := I) g₀ x w)).comp
                ((PDE.DeTurck.connDiff (I := I) g₁ g₀ x).flip v0)).toLinearMap) := by
  classical
  obtain ⟨Y, hYx⟩ := ContMDiffSection.exists_eq_at (I := I) (n := (⊤ : ℕ∞))
    (F := E) (V := (TangentSpace I : M → Type _)) x w
  have hk := covGrad_gInvDiffSlotCoeff_endoCov_apply (I := I) (M := M) g₀ g₁ Y x v0
  rw [hYx] at hk
  exact hk

def connArmEndo (g₀ g₁ : SmoothRiemannianMetric I M) (x : M) :
    TangentSpace I x →L[ℝ] (TangentSpace I x →L[ℝ] TangentSpace I x) :=
  -(((ContinuousLinearMap.compL ℝ (TangentSpace I x) (TangentSpace I x) (TangentSpace I x)).flip
      (gInvRaisedEndo (I := I) g₀ g₁ x)).comp
      (PDE.DeTurck.connDiff (I := I) g₁ g₀ x).flip)

set_option linter.unusedSectionVars false in
@[simp] lemma connArmEndo_apply (g₀ g₁ : SmoothRiemannianMetric I M) (x : M)
    (v0 w : TangentSpace I x) :
    connArmEndo (I := I) g₀ g₁ x v0 w =
      - PDE.DeTurck.connDiff (I := I) g₁ g₀ x (gInvRaisedEndo (I := I) g₀ g₁ x w) v0 := by
  rw [connArmEndo, ContinuousLinearMap.neg_apply, ContinuousLinearMap.neg_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply,
    ContinuousLinearMap.compL_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply]

def sharpArmEndo (g₀ g₁ : SmoothRiemannianMetric I M) (x : M) :
    TangentSpace I x →L[ℝ] (TangentSpace I x →L[ℝ] TangentSpace I x) :=
  (endoCovariantDerivative (I := I) (M := M) g₀)
      (gInvDiffRaisedEndoField (I := I) g₀ g₁) x
    - connArmEndo (I := I) g₀ g₁ x

set_option linter.unusedSectionVars false in
lemma sharpArmEndo_apply (g₀ g₁ : SmoothRiemannianMetric I M) (x : M)
    (v0 w : TangentSpace I x) :
    sharpArmEndo (I := I) g₀ g₁ x v0 w =
      inverseMetricSharpFib (I := I) g₁ x
        (dualToCotangent (I := I)
          (-(cotangentToCLM (I := I) (g0FlatCLM (I := I) g₀ x w)).comp
              ((PDE.DeTurck.connDiff (I := I) g₁ g₀ x).flip v0)).toLinearMap) := by
  rw [sharpArmEndo, ContinuousLinearMap.sub_apply, ContinuousLinearMap.sub_apply,
    connArmEndo_apply, endoCov_gInvDiffRaisedField_fibrewise (I := I) g₀ g₁ x v0 w]
  abel

set_option linter.unusedSectionVars false in
lemma endoCov_eq_connArm_add_sharpArm (g₀ g₁ : SmoothRiemannianMetric I M) (x : M)
    (v0 : TangentSpace I x) :
    (endoCovariantDerivative (I := I) (M := M) g₀)
        (gInvDiffRaisedEndoField (I := I) g₀ g₁) x v0 =
      connArmEndo (I := I) g₀ g₁ x v0 + sharpArmEndo (I := I) g₀ g₁ x v0 := by
  apply ContinuousLinearMap.ext; intro w
  rw [ContinuousLinearMap.add_apply, connArmEndo_apply, sharpArmEndo_apply,
    endoCov_gInvDiffRaisedField_fibrewise (I := I) g₀ g₁ x v0 w]

set_option backward.isDefEq.respectTransparency false in
set_option linter.unusedSectionVars false in
private theorem leviCivitaSection_contMDiff_aux (g : SmoothRiemannianMetric I M)
    {σ : Π x : M, TangentSpace I x}
    (hσ : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% σ)) :
    ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E)) ∞
      (fun x : M =>
        (⟨x, (LeviCivita (I := I) g).toFun σ x⟩ :
          TotalSpace (E →L[ℝ] E) (fun x : M =>
            TangentSpace I x →L[ℝ] TangentSpace I x))) := by
  have hσ' : ContMDiffOn I (I.prod 𝓘(ℝ, E)) ((∞ : WithTop ℕ∞) + 1) (T% σ) Set.univ := by
    have h_le : ((∞ : WithTop ℕ∞) + 1) ≤ (∞ : WithTop ℕ∞) := by rw [ENat.coe_top_add_one]
    exact (hσ.of_le h_le).contMDiffOn
  rw [← contMDiffOn_univ]
  exact LeviCivita_section_contMDiffOn_univ (I := I) g hσ'

set_option backward.isDefEq.respectTransparency false in
theorem connArmEndo_inner_contMDiff (g₀ g₁ : SmoothRiemannianMetric I M)
    (V0 W : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun x : M => TotalSpace.mk' E (E := fun z : M => TangentSpace I z) x
        (connArmEndo (I := I) g₀ g₁ x (V0 x) (W x))) := by
  have hconn : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun x : M => TotalSpace.mk' E (E := fun z : M => TangentSpace I z) x
        (PDE.DeTurck.connDiff (I := I) g₁ g₀ x
          (gInvRaisedEndo (I := I) g₀ g₁ x (W x)) (V0 x))) :=
    PDE.DeTurck.connDiff_contMDiff (I := I) g₁ g₀
      (gInvRaisedEndo_section_contMDiff (I := I) g₀ g₁ W) V0.contMDiff
  refine (hconn.neg_section).congr (fun x => ?_)
  rw [connArmEndo_apply]
  rfl

set_option backward.isDefEq.respectTransparency false in
theorem sharpArmEndo_inner_contMDiff (g₀ g₁ : SmoothRiemannianMetric I M)
    (V0 W : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun x : M => TotalSpace.mk' E (E := fun z : M => TangentSpace I z) x
        (sharpArmEndo (I := I) g₀ g₁ x (V0 x) (W x))) := by
  have hendo : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun x : M => TotalSpace.mk' E (E := fun z : M => TangentSpace I z) x
        ((endoCovariantDerivative (I := I) (M := M) g₀)
          (gInvDiffRaisedEndoField (I := I) g₀ g₁) x (V0 x) (W x))) := by
    have hΛcovW : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
        (fun x : M => TotalSpace.mk' E (E := fun z : M => TangentSpace I z) x
          ((LeviCivita (I := I) g₀).toFun
            (fun y : M => (gInvDiffRaisedEndoField (I := I) g₀ g₁ y) (W y)) x (V0 x))) :=
      ContMDiff.clm_bundle_apply (b := id)
        (leviCivitaSection_contMDiff_aux (I := I) g₀
          (endoApplySection_contMDiff (I := I) (M := M) (gInvDiffRaisedEndoField (I := I) g₀ g₁) W))
        V0.contMDiff
    have hcovWsec : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
        (fun x : M => TotalSpace.mk' E (E := fun z : M => TangentSpace I z) x
          ((LeviCivita (I := I) g₀).toFun (fun y : M => W y) x (V0 x))) :=
      ContMDiff.clm_bundle_apply (b := id)
        (leviCivitaSection_contMDiff_aux (I := I) g₀ W.contMDiff) V0.contMDiff
    have hcovW : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
        (fun x : M => TotalSpace.mk' E (E := fun z : M => TangentSpace I z) x
          ((gInvDiffRaisedEndoField (I := I) g₀ g₁ x)
            ((LeviCivita (I := I) g₀).toFun (fun y : M => W y) x (V0 x)))) :=
      endoApplySection_contMDiff (I := I) (M := M) (gInvDiffRaisedEndoField (I := I) g₀ g₁)
        ⟨_, hcovWsec⟩
    refine (hΛcovW.sub_section hcovW).congr (fun x => ?_)
    rw [endoCovariantDerivative_apply (I := I) (M := M) g₀
      (gInvDiffRaisedEndoField (I := I) g₀ g₁) W x (V0 x)]
    rfl
  refine (hendo.sub_section (connArmEndo_inner_contMDiff (I := I) g₀ g₁ V0 W)).congr (fun x => ?_)
  rw [show sharpArmEndo (I := I) g₀ g₁ x (V0 x) (W x) =
      (endoCovariantDerivative (I := I) (M := M) g₀)
        (gInvDiffRaisedEndoField (I := I) g₀ g₁) x (V0 x) (W x)
      - connArmEndo (I := I) g₀ g₁ x (V0 x) (W x) from by
    rw [sharpArmEndo, ContinuousLinearMap.sub_apply, ContinuousLinearMap.sub_apply]]
  rfl

set_option backward.isDefEq.respectTransparency false in
def connArmCc (g₀ g₁ : SmoothRiemannianMetric I M) : SmoothCcTensor g₀ 2 3 where
  toSection :=
    { toFun := fun x : M =>
        TensorRSSpace.ofCLM (armSlotFib (I := I) (M := M) 1 x (connArmEndo (I := I) g₀ g₁ x))
      contMDiff_toFun :=
        armSlotFib_contMDiff (I := I) (M := M) 1 (fun x : M => connArmEndo (I := I) g₀ g₁ x)
          (connArmEndo_inner_contMDiff (I := I) g₀ g₁) }
  hasCompactSupport := HasCompactSupport.of_compactSpace _

set_option backward.isDefEq.respectTransparency false in
def sharpArmCc (g₀ g₁ : SmoothRiemannianMetric I M) : SmoothCcTensor g₀ 2 3 where
  toSection :=
    { toFun := fun x : M =>
        TensorRSSpace.ofCLM (armSlotFib (I := I) (M := M) 1 x (sharpArmEndo (I := I) g₀ g₁ x))
      contMDiff_toFun :=
        armSlotFib_contMDiff (I := I) (M := M) 1 (fun x : M => sharpArmEndo (I := I) g₀ g₁ x)
          (sharpArmEndo_inner_contMDiff (I := I) g₀ g₁) }
  hasCompactSupport := HasCompactSupport.of_compactSpace _

set_option backward.isDefEq.respectTransparency false in
set_option linter.unusedSectionVars false in
@[simp] lemma connArmCc_toSection (g₀ g₁ : SmoothRiemannianMetric I M) (x : M) :
    (connArmCc (I := I) g₀ g₁).toSection x =
      TensorRSSpace.ofCLM (armSlotFib (I := I) (M := M) 1 x (connArmEndo (I := I) g₀ g₁ x)) := rfl

set_option backward.isDefEq.respectTransparency false in
set_option linter.unusedSectionVars false in
@[simp] lemma sharpArmCc_toSection (g₀ g₁ : SmoothRiemannianMetric I M) (x : M) :
    (sharpArmCc (I := I) g₀ g₁).toSection x =
      TensorRSSpace.ofCLM (armSlotFib (I := I) (M := M) 1 x (sharpArmEndo (I := I) g₀ g₁ x)) := rfl

set_option backward.isDefEq.respectTransparency false in
def connArmEndoCc (g₀ g₁ : SmoothRiemannianMetric I M) : SmoothCcTensor g₀ 1 2 where
  toSection :=
    { toFun := fun x : M =>
        TensorRSSpace.ofCLM (armSlotFib (I := I) (M := M) 0 x (connArmEndo (I := I) g₀ g₁ x))
      contMDiff_toFun :=
        armSlotFib_contMDiff (I := I) (M := M) 0 (fun x : M => connArmEndo (I := I) g₀ g₁ x)
          (connArmEndo_inner_contMDiff (I := I) g₀ g₁) }
  hasCompactSupport := HasCompactSupport.of_compactSpace _

set_option backward.isDefEq.respectTransparency false in
def sharpArmEndoCc (g₀ g₁ : SmoothRiemannianMetric I M) : SmoothCcTensor g₀ 1 2 where
  toSection :=
    { toFun := fun x : M =>
        TensorRSSpace.ofCLM (armSlotFib (I := I) (M := M) 0 x (sharpArmEndo (I := I) g₀ g₁ x))
      contMDiff_toFun :=
        armSlotFib_contMDiff (I := I) (M := M) 0 (fun x : M => sharpArmEndo (I := I) g₀ g₁ x)
          (sharpArmEndo_inner_contMDiff (I := I) g₀ g₁) }
  hasCompactSupport := HasCompactSupport.of_compactSpace _

set_option backward.isDefEq.respectTransparency false in
set_option linter.unusedSectionVars false in
@[simp] lemma connArmEndoCc_toSection (g₀ g₁ : SmoothRiemannianMetric I M) (x : M) :
    (connArmEndoCc (I := I) g₀ g₁).toSection x =
      TensorRSSpace.ofCLM (armSlotFib (I := I) (M := M) 0 x (connArmEndo (I := I) g₀ g₁ x)) := rfl

set_option backward.isDefEq.respectTransparency false in
set_option linter.unusedSectionVars false in
@[simp] lemma sharpArmEndoCc_toSection (g₀ g₁ : SmoothRiemannianMetric I M) (x : M) :
    (sharpArmEndoCc (I := I) g₀ g₁).toSection x =
      TensorRSSpace.ofCLM (armSlotFib (I := I) (M := M) 0 x (sharpArmEndo (I := I) g₀ g₁ x)) := rfl

set_option linter.unusedSectionVars false in
def bilinEndoCovariantDerivative (g : SmoothRiemannianMetric I M) :
    CovariantDerivative I (E →L[ℝ] (E →L[ℝ] E))
      (fun x : M => TangentSpace I x →L[ℝ] (TangentSpace I x →L[ℝ] TangentSpace I x)) :=
  HomConnectionGen.homBundleCovariantDerivativeGen I M
    E (fun x : M => TangentSpace I x)
    (E →L[ℝ] E) (fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x)
    (LeviCivita (I := I) g) (endoCovariantDerivative (I := I) (M := M) g)

set_option linter.unusedSectionVars false in
instance bilinEndoCovariantDerivative_contMDiff (g : SmoothRiemannianMetric I M) :
    (bilinEndoCovariantDerivative (I := I) (M := M) g).ContMDiffCovariantDerivative ∞ :=
  HomConnectionGen.homBundleCovariantDerivativeGen_contMDiff I M
    E (fun x : M => TangentSpace I x)
    (E →L[ℝ] E) (fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x)
    (LeviCivita (I := I) g) (endoCovariantDerivative (I := I) (M := M) g)

set_option linter.unusedSectionVars false in
theorem bilinEndoCovariantDerivative_apply (g : SmoothRiemannianMetric I M)
    (Arm : ContMDiffSection I (E →L[ℝ] (E →L[ℝ] E)) ∞
      (fun x : M => TangentSpace I x →L[ℝ] (TangentSpace I x →L[ℝ] TangentSpace I x)))
    (Y : ContMDiffSection I E ∞ (TangentSpace I)) (x : M) (v : E) :
    ((bilinEndoCovariantDerivative (I := I) (M := M) g) Arm x v) (Y x) =
      (endoCovariantDerivative (I := I) (M := M) g) (fun y => (Arm y) (Y y)) x v -
        (Arm x) ((LeviCivita (I := I) g) (fun y => Y y) x v) :=
  HomConnectionGen.homBundleCovariantDerivativeGen_apply I M
    E (fun x : M => TangentSpace I x)
    (E →L[ℝ] E) (fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x)
    (LeviCivita (I := I) g) (endoCovariantDerivative (I := I) (M := M) g) Arm Y x v

set_option linter.unusedSectionVars false in
theorem armField_inner_contMDiff
    (Arm : ContMDiffSection I (E →L[ℝ] (E →L[ℝ] E)) ∞
      (fun x : M => TangentSpace I x →L[ℝ] (TangentSpace I x →L[ℝ] TangentSpace I x)))
    (V0 W : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun x : M => TotalSpace.mk' E (E := fun z : M => TangentSpace I z) x
        (Arm x (V0 x) (W x))) := by
  have h1 : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E)) ∞
      (fun x : M => TotalSpace.mk' (E →L[ℝ] E)
        (E := fun z : M => TangentSpace I z →L[ℝ] TangentSpace I z) x
        (Arm x (V0 x))) :=
    ContMDiff.clm_bundle_apply (b := id) Arm.contMDiff V0.contMDiff
  exact ContMDiff.clm_bundle_apply (b := id) h1 W.contMDiff

set_option backward.isDefEq.respectTransparency false in
def armSlotEndoCc (g : SmoothRiemannianMetric I M) (s : ℕ)
    (Arm : ContMDiffSection I (E →L[ℝ] (E →L[ℝ] E)) ∞
      (fun x : M => TangentSpace I x →L[ℝ] (TangentSpace I x →L[ℝ] TangentSpace I x))) :
    SmoothCcTensor g (s + 1) (s + 1 + 1) where
  toSection :=
    { toFun := fun x : M =>
        TensorRSSpace.ofCLM (armSlotFib (I := I) (M := M) s x (Arm x))
      contMDiff_toFun :=
        armSlotFib_contMDiff (I := I) (M := M) s (fun x : M => Arm x)
          (fun V0 W => armField_inner_contMDiff (I := I) (M := M) Arm V0 W) }
  hasCompactSupport := HasCompactSupport.of_compactSpace _

set_option linter.unusedSectionVars false in
@[simp] lemma armSlotEndoCc_toSection (g : SmoothRiemannianMetric I M) (s : ℕ)
    (Arm : ContMDiffSection I (E →L[ℝ] (E →L[ℝ] E)) ∞
      (fun x : M => TangentSpace I x →L[ℝ] (TangentSpace I x →L[ℝ] TangentSpace I x)))
    (x : M) :
    (armSlotEndoCc (I := I) (M := M) g s Arm).toSection x =
      TensorRSSpace.ofCLM (armSlotFib (I := I) (M := M) s x (Arm x)) := rfl

set_option backward.isDefEq.respectTransparency false in
theorem bilinEndoField_contMDiff
    (Arm : Π x : M, TangentSpace I x →L[ℝ] (TangentSpace I x →L[ℝ] TangentSpace I x))
    (harm : ∀ (V0 W : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯),
      ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
        (fun x : M => TotalSpace.mk' E (E := fun z : M => TangentSpace I z) x
          (Arm x (V0 x) (W x)))) :
    ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] (E →L[ℝ] E))) ∞
      (fun x : M => TotalSpace.mk' (E →L[ℝ] (E →L[ℝ] E))
        (E := fun z : M => TangentSpace I z →L[ℝ] (TangentSpace I z →L[ℝ] TangentSpace I z)) x
        (Arm x)) := by
  apply contMDiff_clm_section_of_pointwise (I := I) (M := M)
    (F₁ := E) (V₁ := fun x : M => TangentSpace I x)
    (F₂ := E →L[ℝ] E) (V₂ := fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x)
    (φ := fun x : M => (show TangentSpace I x →L[ℝ] (TangentSpace I x →L[ℝ] TangentSpace I x) from
      Arm x))
  intro V0
  apply contMDiff_clm_section_of_pointwise (I := I) (M := M)
    (F₁ := E) (V₁ := fun x : M => TangentSpace I x)
    (F₂ := E) (V₂ := fun x : M => TangentSpace I x)
    (φ := fun x : M => (show TangentSpace I x →L[ℝ] TangentSpace I x from Arm x (V0 x)))
  intro W
  exact harm V0 W

def connArmEndoField (g₀ g₁ : SmoothRiemannianMetric I M) :
    ContMDiffSection I (E →L[ℝ] (E →L[ℝ] E)) ∞
      (fun x : M => TangentSpace I x →L[ℝ] (TangentSpace I x →L[ℝ] TangentSpace I x)) :=
  ⟨fun x : M => connArmEndo (I := I) g₀ g₁ x,
    bilinEndoField_contMDiff (I := I) (M := M) (fun x : M => connArmEndo (I := I) g₀ g₁ x)
      (connArmEndo_inner_contMDiff (I := I) g₀ g₁)⟩

def sharpArmEndoField (g₀ g₁ : SmoothRiemannianMetric I M) :
    ContMDiffSection I (E →L[ℝ] (E →L[ℝ] E)) ∞
      (fun x : M => TangentSpace I x →L[ℝ] (TangentSpace I x →L[ℝ] TangentSpace I x)) :=
  ⟨fun x : M => sharpArmEndo (I := I) g₀ g₁ x,
    bilinEndoField_contMDiff (I := I) (M := M) (fun x : M => sharpArmEndo (I := I) g₀ g₁ x)
      (sharpArmEndo_inner_contMDiff (I := I) g₀ g₁)⟩

set_option linter.unusedSectionVars false in
@[simp] lemma connArmEndoField_apply (g₀ g₁ : SmoothRiemannianMetric I M) (x : M) :
    connArmEndoField (I := I) g₀ g₁ x = connArmEndo (I := I) g₀ g₁ x := rfl

set_option linter.unusedSectionVars false in
@[simp] lemma sharpArmEndoField_apply (g₀ g₁ : SmoothRiemannianMetric I M) (x : M) :
    sharpArmEndoField (I := I) g₀ g₁ x = sharpArmEndo (I := I) g₀ g₁ x := rfl

set_option backward.isDefEq.respectTransparency false in
lemma connArmCc_eq_armSlotEndoCc (g₀ g₁ : SmoothRiemannianMetric I M) :
    connArmCc (I := I) g₀ g₁ = armSlotEndoCc (I := I) (M := M) g₀ 1 (connArmEndoField (I := I) g₀ g₁) := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rw [connArmCc_toSection, armSlotEndoCc_toSection, connArmEndoField_apply]

set_option backward.isDefEq.respectTransparency false in
lemma sharpArmCc_eq_armSlotEndoCc (g₀ g₁ : SmoothRiemannianMetric I M) :
    sharpArmCc (I := I) g₀ g₁ = armSlotEndoCc (I := I) (M := M) g₀ 1 (sharpArmEndoField (I := I) g₀ g₁) := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rw [sharpArmCc_toSection, armSlotEndoCc_toSection, sharpArmEndoField_apply]

set_option backward.isDefEq.respectTransparency false in
lemma connArmEndoCc_eq_armSlotEndoCc (g₀ g₁ : SmoothRiemannianMetric I M) :
    connArmEndoCc (I := I) g₀ g₁ = armSlotEndoCc (I := I) (M := M) g₀ 0 (connArmEndoField (I := I) g₀ g₁) := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rw [connArmEndoCc_toSection, armSlotEndoCc_toSection, connArmEndoField_apply]

set_option backward.isDefEq.respectTransparency false in
lemma sharpArmEndoCc_eq_armSlotEndoCc (g₀ g₁ : SmoothRiemannianMetric I M) :
    sharpArmEndoCc (I := I) g₀ g₁ = armSlotEndoCc (I := I) (M := M) g₀ 0 (sharpArmEndoField (I := I) g₀ g₁) := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rw [sharpArmEndoCc_toSection, armSlotEndoCc_toSection, sharpArmEndoField_apply]

set_option linter.unusedSectionVars false in
lemma curry_armSlotFib_eq_slotInsert (s : ℕ) (x : M)
    (Arm : TangentSpace I x →L[ℝ] (TangentSpace I x →L[ℝ] TangentSpace I x))
    (A : Tensor0SSpace (s + 1) I x) (v0 : TangentSpace I x) :
    (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) (s + 1) x
        (armSlotFib (I := I) (M := M) s x Arm A)) v0 =
      slotInsertEndoFib (I := I) (M := M) (s + 1) 0 x (Arm v0) A := by
  apply Tensor0SSpace.toModel_injective
  refine ContinuousMultilinearMap.ext (fun vt => ?_)
  rw [tensor0S_curry_apply_eval, armSlotFib_apply_eval]
  simp only [Fin.cons_zero]
  rfl

set_option linter.unusedSectionVars false in
lemma slotInsertEndoFib_sub_left (s : ℕ) (k : Fin s) (x : M)
    (Λ₁ Λ₂ : TangentSpace I x →L[ℝ] TangentSpace I x) :
    slotInsertEndoFib (I := I) (M := M) s k x (Λ₁ - Λ₂) =
      slotInsertEndoFib (I := I) (M := M) s k x Λ₁ -
        slotInsertEndoFib (I := I) (M := M) s k x Λ₂ := by
  rw [sub_eq_add_neg, sub_eq_add_neg]
  rw [show (-Λ₂ : TangentSpace I x →L[ℝ] TangentSpace I x) = ((-1 : ℝ)) • Λ₂ from by
    rw [neg_one_smul]]
  rw [slotInsertEndoFib_add_left (I := I) (M := M) s k x Λ₁ ((-1 : ℝ) • Λ₂)]
  rw [slotInsertEndoFib_smul_left (I := I) (M := M) s k x (-1 : ℝ) Λ₂]
  rw [neg_one_smul]

set_option backward.isDefEq.respectTransparency false in
set_option synthInstance.maxHeartbeats 4000000 in
set_option linter.unusedSectionVars false in
private theorem core_armSlot_curry_reading (g : SmoothRiemannianMetric I M) (s : ℕ)
    (Arm : ContMDiffSection I (E →L[ℝ] (E →L[ℝ] E)) ∞
      (fun x : M => TangentSpace I x →L[ℝ] (TangentSpace I x →L[ℝ] TangentSpace I x)))
    (x : M) (v : E) (D : Tensor0SSpace (s + 1) I x) (v0 : E) :
    (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) (s + 1) x
        ((show Tensor0SSpace (s + 1) I x →L[ℝ] Tensor0SSpace (s + 1 + 1) I x from
          tensorCovDerivAt (I := I) (M := M) g (s + 1) (s + 1 + 1)
            (armSlotEndoCc (I := I) (M := M) g s Arm) x v) D)) v0 =
      slotInsertEndoFib (I := I) (M := M) (s + 1) 0 x
        (((bilinEndoCovariantDerivative (I := I) (M := M) g) Arm x v) v0) D := by
  classical
  obtain ⟨w, hw⟩ := ContMDiffSection.exists_eq_at (I := I)
    (F := Tensor0SModel (s + 1) ℝ E) (V := fun y : M => Tensor0SSpace (s + 1) I y)
    (n := (⊤ : ℕ∞)) x D
  obtain ⟨Y, hY⟩ := ContMDiffSection.exists_eq_at (I := I)
    (F := E) (V := fun y : M => TangentSpace I y) (n := (⊤ : ℕ∞)) x v0
  set ASA := armSlotEndoCc (I := I) (M := M) g s Arm with hASA
  have hlamY : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E)) ∞
      (fun y : M => TotalSpace.mk' (E →L[ℝ] E)
        (E := fun z : M => TangentSpace I z →L[ℝ] TangentSpace I z) y ((Arm y) (Y y))) :=
    ContMDiff.clm_bundle_apply (b := id) Arm.contMDiff Y.contMDiff
  let lamY : ContMDiffSection I (E →L[ℝ] E) ∞
      (fun y : M => TangentSpace I y →L[ℝ] TangentSpace I y) :=
    ⟨fun y : M => (Arm y) (Y y), hlamY⟩
  set SIΛ := slotInsertEndoCc (I := I) (M := M) g s lamY with hSIΛ
  have hbridge_app : ∀ y : M, ∀ A : Tensor0SSpace (s + 1) I y,
      (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) (s + 1) y
          ((show Tensor0SSpace (s + 1) I y →L[ℝ] Tensor0SSpace (s + 1 + 1) I y from
            ASA.toSection y) A)) (Y y) =
        (show Tensor0SSpace (s + 1) I y →L[ℝ] Tensor0SSpace (s + 1) I y from SIΛ.toSection y) A := by
    intro y A
    rw [hASA, armSlotEndoCc_toSection]
    rw [show (show Tensor0SSpace (s + 1) I y →L[ℝ] Tensor0SSpace (s + 1 + 1) I y from
        TensorRSSpace.ofCLM (armSlotFib (I := I) (M := M) s y (Arm y))) A =
          armSlotFib (I := I) (M := M) s y (Arm y) A from rfl]
    rw [curry_armSlotFib_eq_slotInsert (I := I) (M := M) s y (Arm y) A (Y y)]
    rw [hSIΛ, slotInsertEndoCc_toSection]
    rfl
  have hw_at_full : TensorSectionMDiffAt (I := I) (s + 1 + 1)
      (fun y : M => (show Tensor0SSpace (s + 1) I y →L[ℝ] Tensor0SSpace (s + 1 + 1) I y from
        ASA.toSection y) (w y)) x := by
    have hsm : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel (s + 1 + 1) ℝ E)) ∞
        (fun y : M => TotalSpace.mk' (Tensor0SModel (s + 1 + 1) ℝ E)
          (E := fun z : M => Tensor0SSpace (s + 1 + 1) I z) y
          ((show Tensor0SSpace (s + 1) I y →L[ℝ] Tensor0SSpace (s + 1 + 1) I y from
            ASA.toSection y) (w y))) :=
      ContMDiff.clm_bundle_apply (b := id) ASA.toSection.contMDiff w.contMDiff
    exact (hsm x).mdifferentiableAt (by norm_num)
  have hSIw_at : TensorSectionMDiffAt (I := I) (s + 1)
      (fun y : M => (show Tensor0SSpace (s + 1) I y →L[ℝ] Tensor0SSpace (s + 1) I y from
        SIΛ.toSection y) (w y)) x := by
    have hsm : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel (s + 1) ℝ E)) ∞
        (fun y : M => TotalSpace.mk' (Tensor0SModel (s + 1) ℝ E)
          (E := fun z : M => Tensor0SSpace (s + 1) I z) y
          ((show Tensor0SSpace (s + 1) I y →L[ℝ] Tensor0SSpace (s + 1) I y from SIΛ.toSection y) (w y))) :=
      ContMDiff.clm_bundle_apply (b := id) SIΛ.toSection.contMDiff w.contMDiff
    exact (hsm x).mdifferentiableAt (by norm_num)
  have hCL_U := tensor0SCovariantDerivative_curriedSection_hom_leibniz (I := I) (M := M) g (s + 1)
    (fun y : M => (show Tensor0SSpace (s + 1) I y →L[ℝ] Tensor0SSpace (s + 1 + 1) I y from
      ASA.toSection y) (w y)) (x := x) hw_at_full Y v
  have hbridge_fun : (fun y : M => Tensor0SNabla.curriedSection I M
        (fun z : M => (show Tensor0SSpace (s + 1) I z →L[ℝ] Tensor0SSpace (s + 1 + 1) I z from
          ASA.toSection z) (w z)) y (Y y)) =
      (fun y : M => (show Tensor0SSpace (s + 1) I y →L[ℝ] Tensor0SSpace (s + 1) I y from
        SIΛ.toSection y) (w y)) := by
    funext y
    rw [Tensor0SNabla.curriedSection_apply]
    exact hbridge_app y (w y)
  have hHL_ASA := tensorRSCovariantDerivative_apply (I := I) (M := M) (s + 1) (s + 1 + 1)
    (LeviCivita (I := I) g) ASA.toSection w x v
  have hHL_SI := tensorRSCovariantDerivative_apply (I := I) (M := M) (s + 1) (s + 1)
    (LeviCivita (I := I) g) SIΛ.toSection w x v
  have hbilin := bilinEndoCovariantDerivative_apply (I := I) (M := M) g Arm Y x v
  have hEndoSI := tensorCovDerivAt_slotInsertEndoCc_eq (I := I) (M := M) g s lamY x v
  set Lw : Tensor0SSpace (s + 1) I x :=
    Tensor0SNabla.tensor0SCovariantDerivative I M (s + 1) (LeviCivita (I := I) g) (fun y : M => w y) x v with hLw
  set Lw' : Tensor0SSpace (s + 1) I x :=
    Tensor0SNabla.tensor0SCovariantDerivative I M (s + 1) (LeviCivita (I := I) g) w x v with hLw'
  have hLwLw' : Lw = Lw' := rfl
  set NY : TangentSpace I x := (LeviCivita (I := I) g).toFun (fun y => Y y) x v with hNY
  have hCURVE : (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) (s + 1) x
        ((show Tensor0SSpace (s + 1) I x →L[ℝ] Tensor0SSpace (s + 1 + 1) I x from
          tensorCovDerivAt (I := I) (M := M) g (s + 1) (s + 1 + 1) ASA x v) (w x))) (Y x) =
      slotInsertEndoFib (I := I) (M := M) (s + 1) 0 x
          ((endoCovariantDerivative (I := I) (M := M) g) lamY x v) (w x)
        - slotInsertEndoFib (I := I) (M := M) (s + 1) 0 x ((Arm x) NY) (w x) := by
    have hcurryDeriv : tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) (s + 1) x
          ((show Tensor0SSpace (s + 1) I x →L[ℝ] Tensor0SSpace (s + 1 + 1) I x from
            tensorCovDerivAt (I := I) (M := M) g (s + 1) (s + 1 + 1) ASA x v) (w x)) =
        tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) (s + 1) x
            (Tensor0SNabla.tensor0SCovariantDerivative I M (s + 1 + 1) (LeviCivita (I := I) g)
              (fun y : M => (show Tensor0SSpace (s + 1) I y →L[ℝ] Tensor0SSpace (s + 1 + 1) I y from
                ASA.toSection y) (w y)) x v)
          - tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) (s + 1) x
              ((show Tensor0SSpace (s + 1) I x →L[ℝ] Tensor0SSpace (s + 1 + 1) I x from
                ASA.toSection x) Lw') := by
      rw [tensorCovDerivAt_def (I := I) (M := M) g (s + 1) (s + 1 + 1) ASA x v]
      rw [show (⇑w : ∀ z : M, Tensor0SSpace (s + 1) I z) = (fun z : M => w z) from rfl] at hHL_ASA
      rw [hHL_ASA, map_sub]
    rw [hcurryDeriv]
    rw [ContinuousLinearMap.sub_apply]
    rw [eq_sub_of_add_eq hCL_U.symm]
    rw [show (⇑w : ∀ z : M, Tensor0SSpace (s + 1) I z) = (fun z : M => w z) from rfl]
    rw [hbridge_fun]
    have hcurrASA_NY : (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) (s + 1) x
          ((show Tensor0SSpace (s + 1) I x →L[ℝ] Tensor0SSpace (s + 1 + 1) I x from
            ASA.toSection x) (w x))) NY =
        slotInsertEndoFib (I := I) (M := M) (s + 1) 0 x ((Arm x) NY) (w x) := by
      rw [hASA, armSlotEndoCc_toSection]
      rw [show (show Tensor0SSpace (s + 1) I x →L[ℝ] Tensor0SSpace (s + 1 + 1) I x from
          TensorRSSpace.ofCLM (armSlotFib (I := I) (M := M) s x (Arm x))) (w x) =
            armSlotFib (I := I) (M := M) s x (Arm x) (w x) from rfl]
      rw [curry_armSlotFib_eq_slotInsert (I := I) (M := M) s x (Arm x) (w x) NY]
    have hSIderiv : Tensor0SNabla.tensor0SCovariantDerivative I M (s + 1) (LeviCivita (I := I) g)
          (fun y : M => (show Tensor0SSpace (s + 1) I y →L[ℝ] Tensor0SSpace (s + 1) I y from
            SIΛ.toSection y) (w y)) x v =
        (show Tensor0SSpace (s + 1) I x →L[ℝ] Tensor0SSpace (s + 1) I x from
            tensorCovDerivAt (I := I) (M := M) g (s + 1) (s + 1) SIΛ x v) (w x) +
          (show Tensor0SSpace (s + 1) I x →L[ℝ] Tensor0SSpace (s + 1) I x from SIΛ.toSection x) Lw' := by
      rw [tensorCovDerivAt_def (I := I) (M := M) g (s + 1) (s + 1) SIΛ x v]
      rw [show (⇑w : ∀ z : M, Tensor0SSpace (s + 1) I z) = (fun z : M => w z) from rfl] at hHL_SI
      rw [eq_sub_iff_add_eq] at hHL_SI
      rw [← hHL_SI]
    rw [hSIderiv, hEndoSI]
    have hSIw : (show Tensor0SSpace (s + 1) I x →L[ℝ] Tensor0SSpace (s + 1) I x from SIΛ.toSection x) Lw' =
        slotInsertEndoFib (I := I) (M := M) (s + 1) 0 x ((Arm x) (Y x)) Lw' := by
      rw [hSIΛ, slotInsertEndoCc_toSection]
      rfl
    have hcurrW_NY : Tensor0SNabla.curriedSection I M
          (fun z : M => (show Tensor0SSpace (s + 1) I z →L[ℝ] Tensor0SSpace (s + 1 + 1) I z from
            ASA.toSection z) (w z)) x NY =
        slotInsertEndoFib (I := I) (M := M) (s + 1) 0 x ((Arm x) NY) (w x) := by
      rw [Tensor0SNabla.curriedSection_apply]
      exact hcurrASA_NY
    have hcurrASA_Lw : (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) (s + 1) x
          ((show Tensor0SSpace (s + 1) I x →L[ℝ] Tensor0SSpace (s + 1 + 1) I x from
            ASA.toSection x) Lw')) (Y x) =
        slotInsertEndoFib (I := I) (M := M) (s + 1) 0 x ((Arm x) (Y x)) Lw' := by
      rw [hASA, armSlotEndoCc_toSection]
      rw [show (show Tensor0SSpace (s + 1) I x →L[ℝ] Tensor0SSpace (s + 1 + 1) I x from
          TensorRSSpace.ofCLM (armSlotFib (I := I) (M := M) s x (Arm x))) Lw' =
            armSlotFib (I := I) (M := M) s x (Arm x) Lw' from rfl]
      rw [curry_armSlotFib_eq_slotInsert (I := I) (M := M) s x (Arm x) Lw' (Y x)]
    rw [hSIw, hcurrW_NY, hcurrASA_Lw]
    abel
  rw [← hw, ← hY]
  rw [hCURVE]
  rw [← ContinuousLinearMap.sub_apply
    (slotInsertEndoFib (I := I) (M := M) (s + 1) 0 x
      ((endoCovariantDerivative (I := I) (M := M) g) lamY x v))
    (slotInsertEndoFib (I := I) (M := M) (s + 1) 0 x ((Arm x) NY)) (w x)]
  rw [← slotInsertEndoFib_sub_left (I := I) (M := M) (s + 1) 0 x
    ((endoCovariantDerivative (I := I) (M := M) g) lamY x v) ((Arm x) NY)]
  congr 1
  rw [hbilin]
  rfl

set_option linter.unusedSectionVars false in
theorem tensorCovDerivAt_armSlotEndoCc_eq (g : SmoothRiemannianMetric I M) (s : ℕ)
    (Arm : ContMDiffSection I (E →L[ℝ] (E →L[ℝ] E)) ∞
      (fun x : M => TangentSpace I x →L[ℝ] (TangentSpace I x →L[ℝ] TangentSpace I x)))
    (x : M) (v : E) :
    (show Tensor0SSpace (s + 1) I x →L[ℝ] Tensor0SSpace (s + 1 + 1) I x from
        tensorCovDerivAt (I := I) (M := M) g (s + 1) (s + 1 + 1)
          (armSlotEndoCc (I := I) (M := M) g s Arm) x v) =
      armSlotFib (I := I) (M := M) s x
        ((bilinEndoCovariantDerivative (I := I) (M := M) g) Arm x v) := by
  apply ContinuousLinearMap.ext
  intro D
  apply Tensor0SSpace.toModel_injective
  refine ContinuousMultilinearMap.ext (fun m => ?_)
  rw [show m = Fin.cons (m 0) (Matrix.vecTail m) from (Fin.cons_self_tail m).symm]
  rw [armSlotFib_apply_eval]
  rw [← tensor0S_curry_apply_eval (I := I) (M := M) (n := s + 1)
    (T := (show Tensor0SSpace (s + 1) I x →L[ℝ] Tensor0SSpace (s + 1 + 1) I x from
      tensorCovDerivAt (I := I) (M := M) g (s + 1) (s + 1 + 1)
        (armSlotEndoCc (I := I) (M := M) g s Arm) x v) D) (v0 := m 0) (vs := Matrix.vecTail m)]
  rw [core_armSlot_curry_reading (I := I) (M := M) g s Arm x v D (m 0)]
  simp only [Fin.cons_zero]
  rw [show Matrix.vecTail (Fin.cons (m 0) (Matrix.vecTail m)) = Matrix.vecTail m from by
    funext k; rfl]

set_option linter.unusedSectionVars false in
theorem covGrad_armSlotEndoCc_toSection_eq (g : SmoothRiemannianMetric I M) (s : ℕ)
    (Arm : ContMDiffSection I (E →L[ℝ] (E →L[ℝ] E)) ∞
      (fun x : M => TangentSpace I x →L[ℝ] (TangentSpace I x →L[ℝ] TangentSpace I x)))
    (x : M) (D : Tensor0SSpace (s + 1) I x) (v : Fin (s + 1 + 1 + 1) → TangentSpace I x) :
    Tensor0SSpace.toModel
        ((show Tensor0SSpace (s + 1) I x →L[ℝ] Tensor0SSpace (s + 1 + 1 + 1) I x from
          (covGrad (I := I) (M := M) g (s + 1) (s + 1 + 1)
            (armSlotEndoCc (I := I) (M := M) g s Arm)).toSection x) D) v =
      Tensor0SSpace.toModel
        ((armSlotFib (I := I) (M := M) s x
            ((bilinEndoCovariantDerivative (I := I) (M := M) g) Arm x (v 0))) D)
        (Matrix.vecTail v) := by
  rw [covGrad_toSection_apply_eval (I := I) (M := M) g (s + 1) (s + 1 + 1)
    (armSlotEndoCc (I := I) (M := M) g s Arm) x D v]
  rw [tensorCovDerivAt_armSlotEndoCc_eq (I := I) (M := M) g s Arm x (v 0)]

set_option backward.isDefEq.respectTransparency false in
set_option linter.unusedSectionVars false in
theorem covGrad_gInvDiffSlotCoeff_eq_slotInsert_section
    (g₀ g₁ : SmoothRiemannianMetric I M) :
    covGrad (I := I) (M := M) g₀ 2 2 (gInvDiffSlotCoeff (I := I) g₀ g₁) =
      connArmCc (I := I) g₀ g₁ + sharpArmCc (I := I) g₀ g₁ := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  apply tensorRSSpace_ext
  intro D
  apply Tensor0SSpace.toModel_injective (I := I) (M := M)
  apply ContinuousMultilinearMap.ext
  intro v
  rw [show ((connArmCc (I := I) g₀ g₁ + sharpArmCc (I := I) g₀ g₁).toSection x) =
      (connArmCc (I := I) g₀ g₁).toSection x + (sharpArmCc (I := I) g₀ g₁).toSection x from by
    rw [SmoothCcTensor.toSection_add]; rfl]
  rw [show ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 3 I x from
      ((connArmCc (I := I) g₀ g₁).toSection x + (sharpArmCc (I := I) g₀ g₁).toSection x)) D) =
      (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 3 I x from
        (connArmCc (I := I) g₀ g₁).toSection x) D +
      (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 3 I x from
        (sharpArmCc (I := I) g₀ g₁).toSection x) D from rfl]
  show Tensor0SSpace.toModel _ v = Tensor0SSpace.toModel (_ + _) v
  rw [Tensor0SSpace.toModel_add, ContinuousMultilinearMap.add_apply]
  rw [covGrad_gInvDiffSlotCoeff_toSection_eval (I := I) (M := M) g₀ g₁ x D v]
  rw [connArmCc_toSection, sharpArmCc_toSection]
  show _ = Tensor0SSpace.toModel
      (armSlotFib (I := I) (M := M) 1 x (connArmEndo (I := I) g₀ g₁ x) D) v +
    Tensor0SSpace.toModel
      (armSlotFib (I := I) (M := M) 1 x (sharpArmEndo (I := I) g₀ g₁ x) D) v
  rw [armSlotFib_apply_eval, armSlotFib_apply_eval]
  rw [endoCov_eq_connArm_add_sharpArm (I := I) g₀ g₁ x (v 0)]
  rw [slotInsertEndoFib_add_left, ContinuousLinearMap.add_apply,
    Tensor0SSpace.toModel_add, ContinuousMultilinearMap.add_apply]

private lemma diagonalGrid_step_rankLeft_le (n : ℝ) (hn : 0 ≤ n) (j : ℕ) (cΦ cW : ℕ → ℝ)
    (hcΦ : ∀ i, 0 ≤ cΦ i) (hcW : ∀ l, 0 ≤ cW l) :
    (∑ i ∈ Finset.range (j + 1), cΦ (i + 1) * ∑ l ∈ Finset.range (j + 1 - i), cW l) +
        n * ∑ i ∈ Finset.range (j + 1), cΦ i * ∑ l ∈ Finset.range (j + 1 - i), cW (l + 1) ≤
      (n + 1) * ∑ i ∈ Finset.range (j + 1 + 1),
        cΦ i * ∑ l ∈ Finset.range (j + 1 + 1 - i), cW l := by
  classical
  set D : ℝ := ∑ i ∈ Finset.range (j + 1 + 1), cΦ i * ∑ l ∈ Finset.range (j + 1 + 1 - i), cW l
    with hD_def
  have hcell_nn : ∀ i, 0 ≤ cΦ i * ∑ l ∈ Finset.range (j + 1 + 1 - i), cW l := by
    intro i; exact mul_nonneg (hcΦ i) (Finset.sum_nonneg (fun l _ => hcW l))
  have hWshift : ∀ m : ℕ, (∑ l ∈ Finset.range m, cW (l + 1)) ≤ ∑ l ∈ Finset.range (m + 1), cW l := by
    intro m
    rw [Finset.sum_range_succ' (fun l => cW l) m]
    exact le_add_of_nonneg_right (hcW 0)
  have hA : (∑ i ∈ Finset.range (j + 1), cΦ (i + 1) * ∑ l ∈ Finset.range (j + 1 - i), cW l) ≤ D := by
    rw [hD_def]
    rw [Finset.sum_range_succ' (fun i => cΦ i * ∑ l ∈ Finset.range (j + 1 + 1 - i), cW l) (j + 1)]
    refine le_trans ?_ (le_add_of_nonneg_right (hcell_nn 0))
    refine Finset.sum_le_sum (fun i hi => ?_)
    have hile : i ≤ j := by simp only [Finset.mem_range] at hi; omega
    refine mul_le_mul_of_nonneg_left (le_of_eq ?_) (hcΦ (i + 1))
    rw [show j + 1 + 1 - (i + 1) = j + 1 - i from by omega]
  have hB : (∑ i ∈ Finset.range (j + 1), cΦ i * ∑ l ∈ Finset.range (j + 1 - i), cW (l + 1)) ≤ D := by
    rw [hD_def]
    rw [Finset.sum_range_succ (fun i => cΦ i * ∑ l ∈ Finset.range (j + 1 + 1 - i), cW l) (j + 1)]
    refine le_trans ?_ (le_add_of_nonneg_right (hcell_nn (j + 1)))
    refine Finset.sum_le_sum (fun i hi => ?_)
    have hile : i ≤ j := by simp only [Finset.mem_range] at hi; omega
    refine mul_le_mul_of_nonneg_left ?_ (hcΦ i)
    refine le_trans (hWshift (j + 1 - i)) (le_of_eq ?_)
    rw [show j + 1 - i + 1 = j + 1 + 1 - i from by omega]
  calc (∑ i ∈ Finset.range (j + 1), cΦ (i + 1) * ∑ l ∈ Finset.range (j + 1 - i), cW l) +
          n * ∑ i ∈ Finset.range (j + 1), cΦ i * ∑ l ∈ Finset.range (j + 1 - i), cW (l + 1)
      ≤ D + n * D := by
        refine add_le_add hA ?_
        exact mul_le_mul_of_nonneg_left hB hn
    _ = (n + 1) * D := by ring

set_option maxHeartbeats 6400000 in
theorem rfns_iteratedCovGrad_appCcRS_diagonalProductGrid_rankLeft_le
    (g : SmoothRiemannianMetric I M) :
    ∀ (j p a b : ℕ) (Φ : SmoothCcTensor g a b) (W : SmoothCcTensor g p a) (x : M),
      riemannianFiberNormSq (I := I) (M := M) g p (b + j) x
          ((iteratedCovGrad (I := I) g p b j
            (appCcRS (I := I) (M := M) g p a b Φ W)).toSection x) ≤
        appCcGdiag (E := E) j *
          ∑ i ∈ Finset.range (j + 1),
            riemannianFiberNormSq (I := I) (M := M) g a (b + i) x
                ((iteratedCovGrad (I := I) g a b i Φ).toSection x) *
              ∑ l ∈ Finset.range (j + 1 - i),
                riemannianFiberNormSq (I := I) (M := M) g p (a + l) x
                  ((iteratedCovGrad (I := I) g p a l W).toSection x) := by
  intro j
  induction j with
  | zero =>
      intro p a b Φ W x
      rw [iteratedCovGrad_zero, appCcGdiag, pow_zero, one_mul]
      rw [Finset.sum_range_one, Finset.sum_range_one, iteratedCovGrad_zero, iteratedCovGrad_zero]
      rw [appCcRS_toSection (I := I) (M := M) g p a b Φ W x]
      have h := riemannianFiberNormSq_compRS_le_mul (I := I) (M := M) g p a b x
        (show TensorRSSpace a b I x from Φ.toSection x)
        (show TensorRSSpace p a I x from W.toSection x)
      simpa using h
  | succ j ih =>
      intro p a b Φ W x
      classical
      rw [← rfns_iteratedCovGrad_covGrad_comm_rs (I := I) (M := M) g p b j
        (appCcRS (I := I) (M := M) g p a b Φ W) x]
      rw [covGrad_appCcRS_eq (I := I) (M := M) g p a b Φ W]
      rw [iteratedCovGrad_add]
      refine le_trans (riemannianFiberNormSq_add_le (I := I) (M := M) g p ((b + 1) + j) x
        ((iteratedCovGrad (I := I) g p (b + 1) j
          (appCcRS (I := I) (M := M) g p a (b + 1)
            (covGrad (I := I) (M := M) g a b Φ) W)).toSection x)
        ((iteratedCovGrad (I := I) g p (b + 1) j
          (appCcRS (I := I) (M := M) g p (a + 1) (b + 1)
            (slotExtend (I := I) (M := M) g a b Φ)
            (covGrad (I := I) (M := M) g p a W))).toSection x)) ?_
      set cΦ : ℕ → ℝ := fun i => riemannianFiberNormSq (I := I) (M := M) g a (b + i) x
        ((iteratedCovGrad (I := I) g a b i Φ).toSection x) with hcΦ_def
      set cW : ℕ → ℝ := fun l => riemannianFiberNormSq (I := I) (M := M) g p (a + l) x
        ((iteratedCovGrad (I := I) g p a l W).toSection x) with hcW_def
      have hcΦ_nn : ∀ i, 0 ≤ cΦ i := fun i =>
        riemannianFiberNormSq_nonneg (I := I) (M := M) g a (b + i) x _
      have hcW_nn : ∀ l, 0 ≤ cW l := fun l =>
        riemannianFiberNormSq_nonneg (I := I) (M := M) g p (a + l) x _
      have hGj_nn : (0 : ℝ) ≤ appCcGdiag (E := E) j := appCcGdiag_nonneg (E := E) j
      have hn_nn : (0 : ℝ) ≤ (Module.finrank ℝ E : ℝ) := Nat.cast_nonneg _
      have hArmA : riemannianFiberNormSq (I := I) (M := M) g p ((b + 1) + j) x
            ((iteratedCovGrad (I := I) g p (b + 1) j
              (appCcRS (I := I) (M := M) g p a (b + 1)
                (covGrad (I := I) (M := M) g a b Φ) W)).toSection x) ≤
          appCcGdiag (E := E) j *
            ∑ i ∈ Finset.range (j + 1), cΦ (i + 1) * ∑ l ∈ Finset.range (j + 1 - i), cW l := by
        refine le_trans (ih p a (b + 1) (covGrad (I := I) (M := M) g a b Φ) W x) ?_
        refine mul_le_mul_of_nonneg_left (le_of_eq (Finset.sum_congr rfl (fun i _ => ?_))) hGj_nn
        rw [hcΦ_def]
        dsimp only
        rw [rfns_iteratedCovGrad_covGrad_comm_rs (I := I) (M := M) g a b i Φ x]
      have hArmB : riemannianFiberNormSq (I := I) (M := M) g p ((b + 1) + j) x
            ((iteratedCovGrad (I := I) g p (b + 1) j
              (appCcRS (I := I) (M := M) g p (a + 1) (b + 1)
                (slotExtend (I := I) (M := M) g a b Φ)
                (covGrad (I := I) (M := M) g p a W))).toSection x) ≤
          appCcGdiag (E := E) j *
            ((Module.finrank ℝ E : ℝ) *
              ∑ i ∈ Finset.range (j + 1), cΦ i * ∑ l ∈ Finset.range (j + 1 - i), cW (l + 1)) := by
        refine le_trans (ih p (a + 1) (b + 1) (slotExtend (I := I) (M := M) g a b Φ)
          (covGrad (I := I) (M := M) g p a W) x) ?_
        refine mul_le_mul_of_nonneg_left ?_ hGj_nn
        rw [Finset.mul_sum]
        refine Finset.sum_le_sum (fun i _ => ?_)
        have hWinner : (∑ l ∈ Finset.range (j + 1 - i),
              riemannianFiberNormSq (I := I) (M := M) g p ((a + 1) + l) x
                ((iteratedCovGrad (I := I) g p (a + 1) l
                  (covGrad (I := I) (M := M) g p a W)).toSection x)) =
            ∑ l ∈ Finset.range (j + 1 - i), cW (l + 1) := by
          refine Finset.sum_congr rfl (fun l _ => ?_)
          rw [hcW_def]
          dsimp only
          rw [rfns_iteratedCovGrad_covGrad_comm_rs (I := I) (M := M) g p a l W x]
        rw [hWinner]
        have hΦle : riemannianFiberNormSq (I := I) (M := M) g (a + 1) ((b + 1) + i) x
              ((iteratedCovGrad (I := I) g (a + 1) (b + 1) i
                (slotExtend (I := I) (M := M) g a b Φ)).toSection x) ≤
            (Module.finrank ℝ E : ℝ) * cΦ i := by
          rw [hcΦ_def]
          dsimp only
          exact rfns_iteratedCovGrad_slotExtend_le (I := I) (M := M) g a b Φ i x
        calc riemannianFiberNormSq (I := I) (M := M) g (a + 1) ((b + 1) + i) x
                ((iteratedCovGrad (I := I) g (a + 1) (b + 1) i
                  (slotExtend (I := I) (M := M) g a b Φ)).toSection x) *
              ∑ l ∈ Finset.range (j + 1 - i), cW (l + 1)
            ≤ ((Module.finrank ℝ E : ℝ) * cΦ i) * ∑ l ∈ Finset.range (j + 1 - i), cW (l + 1) :=
                mul_le_mul_of_nonneg_right hΦle
                  (Finset.sum_nonneg (fun l _ => hcW_nn (l + 1)))
          _ = (Module.finrank ℝ E : ℝ) * (cΦ i * ∑ l ∈ Finset.range (j + 1 - i), cW (l + 1)) := by
                ring
      refine le_trans (add_le_add
        (mul_le_mul_of_nonneg_left hArmA (by norm_num : (0:ℝ) ≤ 2))
        (mul_le_mul_of_nonneg_left hArmB (by norm_num : (0:ℝ) ≤ 2))) ?_
      set Gj : ℝ := appCcGdiag (E := E) j with hGj_def
      set SA : ℝ := ∑ i ∈ Finset.range (j + 1), cΦ (i + 1) * ∑ l ∈ Finset.range (j + 1 - i), cW l
        with hSA_def
      set SB : ℝ := ∑ i ∈ Finset.range (j + 1), cΦ i * ∑ l ∈ Finset.range (j + 1 - i), cW (l + 1)
        with hSB_def
      set DG : ℝ := ∑ i ∈ Finset.range (j + 1 + 1),
        cΦ i * ∑ l ∈ Finset.range (j + 1 + 1 - i), cW l with hDG_def
      have hstep : SA + (Module.finrank ℝ E : ℝ) * SB ≤ ((Module.finrank ℝ E : ℝ) + 1) * DG := by
        rw [hSA_def, hSB_def, hDG_def]
        exact diagonalGrid_step_rankLeft_le (Module.finrank ℝ E : ℝ) hn_nn j cΦ cW hcΦ_nn hcW_nn
      have hGdiag_succ : appCcGdiag (E := E) (j + 1) = (2 * ((Module.finrank ℝ E : ℝ) + 1)) * Gj := by
        rw [hGj_def, appCcGdiag, appCcGdiag, pow_succ]; ring
      rw [hGdiag_succ]
      have hGj_nn' : (0 : ℝ) ≤ Gj := hGj_nn
      nlinarith [mul_le_mul_of_nonneg_left hstep (by positivity : (0:ℝ) ≤ 2 * Gj), hGj_nn',
        hstep]

set_option linter.unusedSectionVars false in
theorem rfns_iteratedCovGrad_gInvDiffSlotCoeff_succ_le_arms
    (g₀ g₁ : SmoothRiemannianMetric I M) (m : ℕ) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + (m + 1)) x
        ((iteratedCovGrad (I := I) g₀ 2 2 (m + 1) (gInvDiffSlotCoeff (I := I) g₀ g₁)).toSection x) ≤
      2 * riemannianFiberNormSq (I := I) (M := M) g₀ 2 ((2 + 1) + m) x
            ((iteratedCovGrad (I := I) g₀ 2 3 m (connArmCc (I := I) g₀ g₁)).toSection x) +
        2 * riemannianFiberNormSq (I := I) (M := M) g₀ 2 ((2 + 1) + m) x
            ((iteratedCovGrad (I := I) g₀ 2 3 m (sharpArmCc (I := I) g₀ g₁)).toSection x) := by
  rw [← rfns_iteratedCovGrad_covGrad_comm_rs (I := I) (M := M) g₀ 2 2 m
    (gInvDiffSlotCoeff (I := I) g₀ g₁) x]
  rw [covGrad_gInvDiffSlotCoeff_eq_slotInsert_section (I := I) g₀ g₁]
  rw [iteratedCovGrad_add]
  exact riemannianFiberNormSq_add_le (I := I) (M := M) g₀ 2 ((2 + 1) + m) x _ _

set_option backward.isDefEq.respectTransparency false in
set_option linter.unusedSectionVars false in
theorem rsDomDomCongrFib_contMDiff (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (σ : Equiv.Perm (Fin s)) (R : SmoothCcTensor g r s) :
    ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun z : M => TensorRSSpace r s I z) x
        (rsDomDomCongr σ (R.toSection x))) := by
  classical
  apply contMDiff_clm_section_of_pointwise (I := I) (M := M)
    (F₁ := Tensor0SModel r ℝ E) (V₁ := fun x : M => Tensor0SSpace r I x)
    (F₂ := Tensor0SModel s ℝ E) (V₂ := fun x : M => Tensor0SSpace s I x)
    (φ := fun x : M => rsDomDomCongr σ (R.toSection x))
  intro Y
  have hZ := ContMDiff.clm_bundle_apply (b := id) R.toSection.contMDiff Y.contMDiff
  have hperm : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel s ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SModel s ℝ E)
        (E := fun z : M => Tensor0SSpace s I z) x
        (Tensor0SSpace.ofModel (ContinuousMultilinearMap.domDomCongr σ
          (Tensor0SSpace.toModel
            ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from R.toSection x) (Y x)))))) := by
    refine (contMDiff_multilinearSection_iff_coord (𝕜 := ℝ) (F := E)
      (E := (TangentSpace I : M → Type _)) (IB := I) (n := (∞ : WithTop ℕ∞)) (Module.finBasis ℝ E)
      (fun x => (Tensor0SSpace.ofModel (𝕜 := ℝ) (I := I) (x := x)
          (ContinuousMultilinearMap.domDomCongr σ
            (Tensor0SSpace.toModel
              ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from R.toSection x) (Y x)))) :
            Tensor0SSpace s I x))).mpr ?_
    have hZcoord := (contMDiff_multilinearSection_iff_coord (𝕜 := ℝ) (F := E)
      (E := (TangentSpace I : M → Type _)) (IB := I) (n := (∞ : WithTop ℕ∞)) (Module.finBasis ℝ E)
      (fun x => (show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from R.toSection x) (Y x))).mp hZ
    intro τ x₀
    refine (hZcoord (τ ∘ σ) x₀).congr_of_eventuallyEq ?_
    filter_upwards [Filter.univ_mem] with x _
    rw [continuousMultilinearMap_basis_repr, continuousMultilinearMap_basis_repr]
    change (ContinuousMultilinearMap.domDomCongr σ
        (Tensor0SSpace.toModel
          ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from R.toSection x) (Y x))))
        (fun j => (Bundle.Trivialization.symmL ℝ (trivializationAt E (TangentSpace I) x₀) x)
          ((Module.finBasis ℝ E) (τ j))) = _
    rw [ContinuousMultilinearMap.domDomCongr_apply]
    rfl
  refine hperm.congr (fun x => ?_)
  refine congrArg (fun t => TotalSpace.mk' (Tensor0SModel s ℝ E)
    (E := fun z : M => Tensor0SSpace s I z) x t) ?_
  apply Tensor0SSpace.toModel_injective
  change Tensor0SSpace.toModel
      ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from
        rsDomDomCongr σ (R.toSection x)) (Y x))
    = Tensor0SSpace.toModel
        (Tensor0SSpace.ofModel (ContinuousMultilinearMap.domDomCongr σ
          (Tensor0SSpace.toModel
            ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from R.toSection x) (Y x)))))
  rw [toModel_rsDomDomCongr_apply, Tensor0SSpace.toModel_ofModel]

set_option backward.isDefEq.respectTransparency false in
def rsDomDomCongrSection (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (σ : Equiv.Perm (Fin s)) (R : SmoothCcTensor g r s) : SmoothCcTensor g r s where
  toSection :=
    { toFun := fun x : M => rsDomDomCongr σ (R.toSection x)
      contMDiff_toFun := rsDomDomCongrFib_contMDiff (I := I) (M := M) g r s σ R }
  hasCompactSupport := HasCompactSupport.of_compactSpace _

set_option linter.unusedSectionVars false in
@[simp] lemma rsDomDomCongrSection_toSection (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (σ : Equiv.Perm (Fin s)) (R : SmoothCcTensor g r s) (x : M) :
    (rsDomDomCongrSection (I := I) (M := M) g r s σ R).toSection x =
      rsDomDomCongr σ (R.toSection x) := rfl

def armSlotEndoPassZeroCc (g : SmoothRiemannianMetric I M)
    (Arm : ContMDiffSection I (E →L[ℝ] (E →L[ℝ] E)) ∞
      (fun x : M => TangentSpace I x →L[ℝ] (TangentSpace I x →L[ℝ] TangentSpace I x))) :
    SmoothCcTensor g 2 3 :=
  rsDomDomCongrSection (I := I) (M := M) g 2 3 (finRotate 3)
    (armSlotEndoCc (I := I) (M := M) g 1 Arm)

set_option linter.unusedSectionVars false in
@[simp] lemma armSlotEndoPassZeroCc_toSection (g : SmoothRiemannianMetric I M)
    (Arm : ContMDiffSection I (E →L[ℝ] (E →L[ℝ] E)) ∞
      (fun x : M => TangentSpace I x →L[ℝ] (TangentSpace I x →L[ℝ] TangentSpace I x)))
    (x : M) :
    (armSlotEndoPassZeroCc (I := I) (M := M) g Arm).toSection x =
      rsDomDomCongr (finRotate 3)
        ((armSlotEndoCc (I := I) (M := M) g 1 Arm).toSection x) := rfl

set_option linter.unusedSectionVars false in
theorem toModel_appCcRS_armSlotEndoPassZeroCc_eval (g : SmoothRiemannianMetric I M)
    (Arm : ContMDiffSection I (E →L[ℝ] (E →L[ℝ] E)) ∞
      (fun x : M => TangentSpace I x →L[ℝ] (TangentSpace I x →L[ℝ] TangentSpace I x)))
    (W : SmoothCcTensor g 1 2) (x : M) (om : Tensor0SSpace 1 I x)
    (v : Fin 3 → TangentSpace I x) :
    Tensor0SSpace.toModel
        ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 3 I x from
          (appCcRS (I := I) (M := M) g 1 2 3
            (armSlotEndoPassZeroCc (I := I) (M := M) g Arm) W).toSection x) om) v =
      Tensor0SSpace.toModel
        ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 2 I x from W.toSection x) om)
        (fun j : Fin 2 => if j = 0 then Arm x (v 1) (v 2) else v 0) := by
  classical
  have hcomp : (show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 3 I x from
        (appCcRS (I := I) (M := M) g 1 2 3
          (armSlotEndoPassZeroCc (I := I) (M := M) g Arm) W).toSection x) om =
      (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 3 I x from
        (armSlotEndoPassZeroCc (I := I) (M := M) g Arm).toSection x)
        ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 2 I x from W.toSection x) om) := by
    rw [appCcRS_toSection]
    rfl
  rw [hcomp, armSlotEndoPassZeroCc_toSection]
  rw [toModel_rsDomDomCongr_apply, ContinuousMultilinearMap.domDomCongr_apply]
  rw [armSlotEndoCc_toSection]
  rw [show (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 3 I x from
        TensorRSSpace.ofCLM (armSlotFib (I := I) (M := M) 1 x (Arm x)))
        ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 2 I x from W.toSection x) om) =
      armSlotFib (I := I) (M := M) 1 x (Arm x)
        ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 2 I x from W.toSection x) om) from rfl]
  rw [armSlotFib_apply_eval, slotInsertEndoFib_apply_eval]
  have hr0 : finRotate 3 (0 : Fin 3) = 1 := by decide
  have hr1 : finRotate 3 (1 : Fin 3) = 2 := by decide
  have hr2 : finRotate 3 (2 : Fin 3) = 0 := by decide
  congr 1
  funext j
  refine Fin.cases ?_ ?_ j
  · rw [Function.update_self, if_pos rfl]
    change Arm x (v (finRotate 3 0)) (v (finRotate 3 1)) = Arm x (v 1) (v 2)
    rw [hr0, hr1]
  · intro i
    have hi : i = 0 := Subsingleton.elim i 0
    subst hi
    rw [Function.update_of_ne (Fin.succ_ne_zero 0), if_neg (Fin.succ_ne_zero 0)]
    change v (finRotate 3 2) = v 0
    rw [hr2]

private lemma exists_iteratedCovGrad_armSlotEndoPassZeroCc_toSection_eq
    (g : SmoothRiemannianMetric I M)
    (Arm : ContMDiffSection I (E →L[ℝ] (E →L[ℝ] E)) ∞
      (fun x : M => TangentSpace I x →L[ℝ] (TangentSpace I x →L[ℝ] TangentSpace I x)))
    (j : ℕ) :
    ∃ τ : Equiv.Perm (Fin (3 + j)), ∀ (x : M) (d : Tensor0SSpace 2 I x),
      Tensor0SSpace.toModel
          ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace (3 + j) I x from
            (iteratedCovGrad (I := I) g 2 3 j
              (armSlotEndoPassZeroCc (I := I) (M := M) g Arm)).toSection x) d) =
        ContinuousMultilinearMap.domDomCongr τ
          (Tensor0SSpace.toModel
            ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace (3 + j) I x from
              (iteratedCovGrad (I := I) g 2 3 j
                (armSlotEndoCc (I := I) (M := M) g 1 Arm)).toSection x) d)) := by
  induction j with
  | zero =>
    refine ⟨finRotate 3, fun x d => ?_⟩
    rw [iteratedCovGrad_zero, iteratedCovGrad_zero, armSlotEndoPassZeroCc_toSection,
      toModel_rsDomDomCongr_apply]
  | succ j ih =>
    obtain ⟨τ, hτ⟩ := ih
    refine ⟨Equiv.Perm.decomposeFin.symm (0, τ), fun x d => ?_⟩
    rw [iteratedCovGrad_succ, iteratedCovGrad_succ]
    apply ContinuousMultilinearMap.ext
    intro v
    exact covGrad_rs_toModel_domDomCongr (I := I) (M := M) g 2 (3 + j) τ
      (iteratedCovGrad (I := I) g 2 3 j (armSlotEndoCc (I := I) (M := M) g 1 Arm))
      (iteratedCovGrad (I := I) g 2 3 j (armSlotEndoPassZeroCc (I := I) (M := M) g Arm))
      hτ x d v

set_option linter.unusedSectionVars false in
theorem riemannianFiberNormSq_iteratedCovGrad_armSlotEndoPassZeroCc_eq
    (g : SmoothRiemannianMetric I M)
    (Arm : ContMDiffSection I (E →L[ℝ] (E →L[ℝ] E)) ∞
      (fun x : M => TangentSpace I x →L[ℝ] (TangentSpace I x →L[ℝ] TangentSpace I x)))
    (j : ℕ) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g 2 (3 + j) x
        ((iteratedCovGrad (I := I) g 2 3 j
          (armSlotEndoPassZeroCc (I := I) (M := M) g Arm)).toSection x) =
      riemannianFiberNormSq (I := I) (M := M) g 2 (3 + j) x
        ((iteratedCovGrad (I := I) g 2 3 j
          (armSlotEndoCc (I := I) (M := M) g 1 Arm)).toSection x) := by
  classical
  obtain ⟨τ, hτ⟩ := exists_iteratedCovGrad_armSlotEndoPassZeroCc_toSection_eq
    (I := I) (M := M) g Arm j
  have hsec : (iteratedCovGrad (I := I) g 2 3 j
        (armSlotEndoPassZeroCc (I := I) (M := M) g Arm)).toSection x =
      rsDomDomCongr τ
        ((iteratedCovGrad (I := I) g 2 3 j
          (armSlotEndoCc (I := I) (M := M) g 1 Arm)).toSection x) := by
    apply ContinuousLinearMap.ext
    intro d
    apply Tensor0SSpace.toModel_injective
    change Tensor0SSpace.toModel
        ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace (3 + j) I x from
          (iteratedCovGrad (I := I) g 2 3 j
            (armSlotEndoPassZeroCc (I := I) (M := M) g Arm)).toSection x) d) =
      Tensor0SSpace.toModel
        ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace (3 + j) I x from
          rsDomDomCongr τ
            ((iteratedCovGrad (I := I) g 2 3 j
              (armSlotEndoCc (I := I) (M := M) g 1 Arm)).toSection x)) d)
    rw [toModel_rsDomDomCongr_apply]
    exact hτ x d
  rw [hsec]
  exact riemannianFiberNormSq_domDomCongr_covariant (I := I) (M := M) g 2 (3 + j) x τ _

set_option linter.unusedSectionVars false in
private lemma metricCovDeriv_symm_right
    (g : SmoothRiemannianMetric I M)
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (X Y Z : Π b : M, TangentSpace I b) (x : M) :
    metricCovDeriv (I := I) g cov X Y Z x = metricCovDeriv (I := I) g cov X Z Y x := by
  unfold metricCovDeriv
  rw [show (fun b : M => g.inner b (Z b) (Y b)) = (fun b : M => g.inner b (Y b) (Z b)) from by
    funext b; rw [g.symm b (Z b) (Y b)]]
  rw [g.symm x (cov.toFun Y x (X x)) (Z x), g.symm x (Y x) (cov.toFun Z x (X x))]
  ring

set_option linter.unusedSectionVars false in
private lemma metricDiffCovDeriv_symm_right
    (g₁ g₀ : SmoothRiemannianMetric I M)
    (X Y Z : Π b : M, TangentSpace I b) (x : M) :
    metricDiffCovDeriv (I := I) g₁ g₀ X Y Z x =
      metricDiffCovDeriv (I := I) g₁ g₀ X Z Y x := by
  unfold metricDiffCovDeriv
  rw [metricCovDeriv_symm_right (I := I) g₁ (LeviCivita (I := I) g₀) X Y Z x,
    metricCovDeriv_symm_right (I := I) g₀ (LeviCivita (I := I) g₀) X Y Z x]

set_option linter.unusedSectionVars false in
theorem endoCovariantDerivative_gInvDiffRaisedEndoField_resolvent
    (g₀ g₁ : SmoothRiemannianMetric I M)
    (V W Z : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) :
    g₁.inner x
        (((endoCovariantDerivative (I := I) (M := M) g₀)
          (gInvDiffRaisedEndoField (I := I) g₀ g₁) x (V x)) (W x)) (Z x) =
      - metricDiffCovDeriv (I := I) g₁ g₀
          (fun y : M => V y)
          (fun y : M => gInvRaisedEndo (I := I) g₀ g₁ y (W y))
          (fun y : M => Z y) x := by
  classical
  have hg1gir : ∀ u : TangentSpace I x,
      g₁.inner x (gInvRaisedEndo (I := I) g₀ g₁ x (W x)) u = g₀.inner x (W x) u := by
    intro u
    rw [gInvRaisedEndo_apply, inverseMetricSharpFib_inner, cotangentToDualLinear_apply,
      cotangentToDual_g0FlatCLM]
  have hpair : g₁.inner x
        (((endoCovariantDerivative (I := I) (M := M) g₀)
          (gInvDiffRaisedEndoField (I := I) g₀ g₁) x (V x)) (W x)) (Z x) =
      - g₁.inner x (PDE.DeTurck.connDiff (I := I) g₁ g₀ x
          (gInvRaisedEndo (I := I) g₀ g₁ x (W x)) (V x)) (Z x)
        - g₀.inner x (W x) (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (Z x) (V x)) := by
    rw [endoCov_gInvDiffRaisedField_fibrewise (I := I) g₀ g₁ x (V x) (W x)]
    rw [map_add, ContinuousLinearMap.add_apply, map_neg, ContinuousLinearMap.neg_apply,
      inverseMetricSharpFib_inner, cotangentToDualLinear_apply, cotangentToDual_dualToCotangent]
    simp only [ContinuousLinearMap.coe_coe, ContinuousLinearMap.neg_apply,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply]
    rw [show (cotangentToCLM (I := I) (g0FlatCLM (I := I) g₀ x (W x)))
            (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (Z x) (V x)) =
          g₀.inner x (W x) (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (Z x) (V x)) from
      cotangentToDual_g0FlatCLM (I := I) g₀ x (W x)
        (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (Z x) (V x))]
    ring
  have hk1 := connDiff_koszul_metricDiff (I := I) g₁ g₀
    (X := fun y : M => V y) (Y := fun y : M => gInvRaisedEndo (I := I) g₀ g₁ y (W y))
    (Z := fun y : M => Z y) V.mdifferentiableAt
    ((gInvRaisedEndo_section_contMDiff (I := I) g₀ g₁ W x).mdifferentiableAt (by norm_num))
    Z.mdifferentiableAt
  have hk2 := connDiff_koszul_metricDiff (I := I) g₁ g₀
    (X := fun y : M => V y) (Y := fun y : M => Z y)
    (Z := fun y : M => gInvRaisedEndo (I := I) g₀ g₁ y (W y)) V.mdifferentiableAt
    Z.mdifferentiableAt
    ((gInvRaisedEndo_section_contMDiff (I := I) g₀ g₁ W x).mdifferentiableAt (by norm_num))
  have hsym := metricDiffCovDeriv_symm_right (I := I) g₁ g₀
    (fun y : M => V y) (fun y : M => Z y)
    (fun y : M => gInvRaisedEndo (I := I) g₀ g₁ y (W y)) x
  have hconv : g₀.inner x (W x) (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (Z x) (V x)) =
      g₁.inner x (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (Z x) (V x))
        (gInvRaisedEndo (I := I) g₀ g₁ x (W x)) := by
    rw [← hg1gir (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (Z x) (V x)),
      g₁.symm x (gInvRaisedEndo (I := I) g₀ g₁ x (W x))
        (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (Z x) (V x))]
  rw [hpair, hconv]
  simp only [] at hk1 hk2
  linarith [hk1, hk2, hsym]

set_option linter.unusedSectionVars false in
theorem rfns_iteratedCovGrad_rsDomDomCongr_both_eq
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (σ' : Equiv.Perm (Fin r)) (σ : Equiv.Perm (Fin s))
    (R : SmoothCcTensor g r s) (i : ℕ) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g r (s + i) x
        ((iteratedCovGrad (I := I) g r s i
          (reindexCoeffGen (I := I) (M := M) g r s
            (rsDomDomCongrSection (I := I) (M := M) g r s σ R) σ')).toSection x) =
      riemannianFiberNormSq (I := I) (M := M) g r (s + i) x
        ((iteratedCovGrad (I := I) g r s i R).toSection x) := by
  rw [rfns_iteratedCovGrad_reindexCoeffGen_eq (I := I) (M := M) g r s
    (rsDomDomCongrSection (I := I) (M := M) g r s σ R) σ' i x]
  exact rfns_iteratedCovGrad_rs_eq_of_section_domDomCongr (I := I) (M := M) g r s σ R
    (rsDomDomCongrSection (I := I) (M := M) g r s σ R)
    (fun y d => by
      rw [rsDomDomCongrSection_toSection, toModel_rsDomDomCongr_apply]) i x

set_option backward.isDefEq.respectTransparency false in
set_option linter.unusedSectionVars false in
private lemma slotInsertEndoCc_succ_eq_reindex_slotExtend
    (g₀ : SmoothRiemannianMetric I M) (s : ℕ)
    (Λ : ContMDiffSection I (E →L[ℝ] E) ∞
      (fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x)) :
    slotInsertEndoCc (I := I) (M := M) g₀ (s + 1) Λ =
      reindexCoeffGen (I := I) (M := M) g₀ (s + 1 + 1) (s + 1 + 1)
        (rsDomDomCongrSection (I := I) (M := M) g₀ (s + 1 + 1) (s + 1 + 1)
          (Equiv.swap (0 : Fin (s + 1 + 1)) 1)
          (slotExtend (I := I) (M := M) g₀ (s + 1) (s + 1)
            (slotInsertEndoCc (I := I) (M := M) g₀ s Λ)))
        (Equiv.swap (0 : Fin (s + 1 + 1)) 1) := by
  classical
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  apply ContinuousLinearMap.ext
  intro D
  apply Tensor0SSpace.toModel_injective
  apply ContinuousMultilinearMap.ext
  intro m
  change Tensor0SSpace.toModel
      ((show Tensor0SSpace (s + 1 + 1) I x →L[ℝ] Tensor0SSpace (s + 1 + 1) I x from
        (slotInsertEndoCc (I := I) (M := M) g₀ (s + 1) Λ).toSection x) D) m =
    Tensor0SSpace.toModel
      ((show Tensor0SSpace (s + 1 + 1) I x →L[ℝ] Tensor0SSpace (s + 1 + 1) I x from
        (reindexCoeffGen (I := I) (M := M) g₀ (s + 1 + 1) (s + 1 + 1)
          (rsDomDomCongrSection (I := I) (M := M) g₀ (s + 1 + 1) (s + 1 + 1)
            (Equiv.swap (0 : Fin (s + 1 + 1)) 1)
            (slotExtend (I := I) (M := M) g₀ (s + 1) (s + 1)
              (slotInsertEndoCc (I := I) (M := M) g₀ s Λ)))
          (Equiv.swap (0 : Fin (s + 1 + 1)) 1)).toSection x) D) m
  rw [slotInsertEndoCc_toSection, slotInsertEndoFib_apply_eval]
  rw [reindexCoeffGen_toSection, reindexCoeffFibGen_apply, rsDomDomCongrSection_toSection,
    toModel_rsDomDomCongr_apply, ContinuousMultilinearMap.domDomCongr_apply, slotExtend_toSection]
  rw [show (fun k : Fin (s + 1 + 1) => m ((Equiv.swap (0 : Fin (s + 1 + 1)) 1) k)) =
      Fin.cons (m 1) (fun j : Fin (s + 1) =>
        m ((Equiv.swap (0 : Fin (s + 1 + 1)) 1) (Fin.succ j))) from by
    funext k
    refine Fin.cases ?_ (fun j => ?_) k
    · simp only [Fin.cons_zero, Equiv.swap_apply_left]
    · simp only [Fin.cons_succ]]
  rw [slotExtendFib_apply_eval]
  rw [slotInsertEndoCc_toSection, slotInsertEndoFib_apply_eval, tensor0S_curry_apply_eval,
    Tensor0SSpace.toModel_ofModel, ContinuousMultilinearMap.domDomCongr_apply]
  have hswap_succ0 : (Equiv.swap (0 : Fin (s + 1 + 1)) 1) (Fin.succ (0 : Fin (s + 1))) = 0 := by
    rw [show (Fin.succ (0 : Fin (s + 1)) : Fin (s + 1 + 1)) = 1 from rfl, Equiv.swap_apply_right]
  rw [hswap_succ0]
  congr 1
  funext k
  refine Fin.cases ?_ (fun k₁ => ?_) k
  · rw [Equiv.swap_apply_left,
      show (1 : Fin (s + 1 + 1)) = Fin.succ (0 : Fin (s + 1)) from rfl, Fin.cons_succ,
      Function.update_self, Function.update_self]
  · refine Fin.cases ?_ (fun k₂ => ?_) k₁
    · have h10 : (1 : Fin (s + 1 + 1)) ≠ 0 := by
        rw [show (1 : Fin (s + 1 + 1)) = Fin.succ (0 : Fin (s + 1)) from rfl]
        exact Fin.succ_ne_zero _
      rw [show (Fin.succ (0 : Fin (s + 1)) : Fin (s + 1 + 1)) = 1 from rfl,
        Function.update_of_ne h10, Equiv.swap_apply_right, Fin.cons_zero]
    · have hne0 : (Fin.succ (Fin.succ k₂) : Fin (s + 1 + 1)) ≠ 0 := Fin.succ_ne_zero _
      have hne1 : (Fin.succ (Fin.succ k₂) : Fin (s + 1 + 1)) ≠ 1 := by
        rw [show (1 : Fin (s + 1 + 1)) = Fin.succ (0 : Fin (s + 1)) from rfl]
        exact fun h => Fin.succ_ne_zero _ (Fin.succ_injective _ h)
      rw [Function.update_of_ne hne0, Equiv.swap_apply_of_ne_of_ne hne0 hne1, Fin.cons_succ,
        Function.update_of_ne (Fin.succ_ne_zero k₂)]
      change m (Fin.succ (Fin.succ k₂)) =
        m ((Equiv.swap (0 : Fin (s + 1 + 1)) 1) (Fin.succ (Fin.succ k₂)))
      rw [Equiv.swap_apply_of_ne_of_ne hne0 hne1]

set_option linter.unusedSectionVars false in
theorem rfns_iteratedCovGrad_slotInsertEndoCc_le_endo
    (g₀ : SmoothRiemannianMetric I M) (s : ℕ)
    (Λ : ContMDiffSection I (E →L[ℝ] E) ∞
      (fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x))
    (i : ℕ) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g₀ (s + 1) ((s + 1) + i) x
        ((iteratedCovGrad (I := I) g₀ (s + 1) (s + 1) i
          (slotInsertEndoCc (I := I) (M := M) g₀ s Λ)).toSection x) ≤
      (Module.finrank ℝ E : ℝ) ^ s *
        riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + i) x
          ((iteratedCovGrad (I := I) g₀ 1 1 i
            (slotInsertEndoCc (I := I) (M := M) g₀ 0 Λ)).toSection x) := by
  induction s with
  | zero =>
    rw [pow_zero, one_mul]
  | succ s ih =>
    have hfr : (0 : ℝ) ≤ (Module.finrank ℝ E : ℝ) := Nat.cast_nonneg _
    have hA : riemannianFiberNormSq (I := I) (M := M) g₀ (s + 1 + 1) ((s + 1 + 1) + i) x
          ((iteratedCovGrad (I := I) g₀ (s + 1 + 1) (s + 1 + 1) i
            (slotInsertEndoCc (I := I) (M := M) g₀ (s + 1) Λ)).toSection x) =
        riemannianFiberNormSq (I := I) (M := M) g₀ (s + 1 + 1) ((s + 1 + 1) + i) x
          ((iteratedCovGrad (I := I) g₀ (s + 1 + 1) (s + 1 + 1) i
            (slotExtend (I := I) (M := M) g₀ (s + 1) (s + 1)
              (slotInsertEndoCc (I := I) (M := M) g₀ s Λ))).toSection x) := by
      rw [slotInsertEndoCc_succ_eq_reindex_slotExtend (I := I) (M := M) g₀ s Λ]
      exact rfns_iteratedCovGrad_rsDomDomCongr_both_eq (I := I) (M := M) g₀ (s + 1 + 1) (s + 1 + 1)
        (Equiv.swap (0 : Fin (s + 1 + 1)) 1) (Equiv.swap (0 : Fin (s + 1 + 1)) 1)
        (slotExtend (I := I) (M := M) g₀ (s + 1) (s + 1)
          (slotInsertEndoCc (I := I) (M := M) g₀ s Λ)) i x
    rw [hA]
    refine le_trans (rfns_iteratedCovGrad_slotExtend_le (I := I) (M := M) g₀ (s + 1) (s + 1)
      (slotInsertEndoCc (I := I) (M := M) g₀ s Λ) i x) ?_
    calc (Module.finrank ℝ E : ℝ) *
            riemannianFiberNormSq (I := I) (M := M) g₀ (s + 1) ((s + 1) + i) x
              ((iteratedCovGrad (I := I) g₀ (s + 1) (s + 1) i
                (slotInsertEndoCc (I := I) (M := M) g₀ s Λ)).toSection x)
        ≤ (Module.finrank ℝ E : ℝ) *
            ((Module.finrank ℝ E : ℝ) ^ s *
              riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + i) x
                ((iteratedCovGrad (I := I) g₀ 1 1 i
                  (slotInsertEndoCc (I := I) (M := M) g₀ 0 Λ)).toSection x)) :=
          mul_le_mul_of_nonneg_left ih hfr
      _ = (Module.finrank ℝ E : ℝ) ^ (s + 1) *
            riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + i) x
              ((iteratedCovGrad (I := I) g₀ 1 1 i
                (slotInsertEndoCc (I := I) (M := M) g₀ 0 Λ)).toSection x) := by
          rw [pow_succ]; ring

end Connection
end Integral
end DifferentialGeometry

end
