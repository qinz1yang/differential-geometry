import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.RicciDeTurckMetricArmCoeffField
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.ConnectionDifferenceFibreBound
import DifferentialGeometry.Analysis.Sobolev.Embedding.SobolevEmbeddingReverseHebeyToHs
import DifferentialGeometry.Analysis.Sobolev.Embedding.SobolevEmbeddingCmOrderDropping
import DifferentialGeometry.Analysis.Sobolev.RiemannianFiberNormSq.PointwiseToL2Packaging
import DifferentialGeometry.Geometry.Connection.TensorNabla.SlotInsertCovariantNaturality
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.SecondBianchi
import DifferentialGeometry.Analysis.Sobolev.GagliardoNirenbergLpFiberNorm
import DifferentialGeometry.Analysis.Sobolev.RiemannianFiberNormSq.RiemannianFiberNormSqNormBridge
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.IteratedCovGradFibreNormPermutationInvariance
import DifferentialGeometry.Analysis.Sobolev.AntidiagonalTupleProductGrid
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.MetricArmCoeffJetTowerRaisedEndoCovariantDerivativeBound
import DifferentialGeometry.Analysis.Sobolev.RiemannianFiberNormSq.MetricArmCoeffJetTowerSlotInsertEndoFibNormBound
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.MetricArmCoeffJetTowerArmSlotFibNormBound
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.MetricArmCoeffJetTowerAppCcRSProductGridRankLeftBound
open DifferentialGeometry.Geometry.Connection.Realization DifferentialGeometry.Tensor.Multilinear
open DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Analysis.Elliptic
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection


noncomputable section

open Bundle Manifold MeasureTheory Set Filter DifferentialGeometry.Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators

namespace DifferentialGeometry
namespace Analysis
namespace Sobolev

open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Analysis.Laplacian
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.PDE.RicciFlow DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Analysis.Sobolev.TensorHilbert
open DifferentialGeometry.TensorRSNabla
open DifferentialGeometry.Analysis.Spectral.MetricRealization
  (metricCauchySchwarzBound ccTensorBilinSymm)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M]

section NormedL2Identity

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

private local instance tensorRSRiemannianNormedAddCommGroup
    (r s : ℕ)
    [h : Bundle.RiemannianBundle (fun b : M => TensorRSSpace r s I b)] (b : M) :
    NormedAddCommGroup (TensorRSSpace r s I b) :=
  (h.g.toCore b).toNormedAddCommGroupOfTopology
    (h.g.continuousAt b) (h.g.isVonNBounded b)

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] in
theorem tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (S : SmoothCcTensor g r s) :
    tensorL2Norm (I := I) (M := M) g r s S.toFun ^ 2 =
      ∫ x, riemannianFiberNormSq (I := I) (M := M) g r s x (S.toSection x)
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
  have hfun : S.toFun = fun x => TensorRSSpace.toModel (𝕜 := ℝ) (E := E) (I := I) (M := M)
      (r := r) (s := s) (x := x) (S.toSection x) := rfl
  rw [hfun]
  exact tensorL2Norm_sq_eq_integral_riemannianFiberNormSq (I := I) (M := M) g r s _

end NormedL2Identity

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] in
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

section NormedIntegralBound

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] in
theorem normSq_le_integral_of_pointwise_fiberNormSq_le_rs
    [CompactSpace M]
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

end NormedIntegralBound

omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
theorem riemannianFiberNormSq_gInvDiffSlotCoeff_le
    (g₀ g₁ : SmoothRiemannianMetric I M) (T : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ : δ < 1 / 2) (hδ0 : 0 ≤ δ)
    (h : ∀ y v w, g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm g₀ T y v w)
    (hbound : metricCauchySchwarzBound (I := I) g₀ (ccTensorBilinSymm g₀ T) δ) (x : M) :
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
            TensorRSSpace.ofCLM (metricComparisonDiffSlotEndo (I := I) g₀ g₁ x)) := by rfl
    _ ≤ ((Module.finrank ℝ E : ℝ) * (δ / (1 - δ))) ^ 2 := hbase
    _ ≤ ((Module.finrank ℝ E : ℝ)) ^ 2 := hmono

section NormedSlotCoefficientIdentity

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

set_option backward.isDefEq.respectTransparency false in
omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
theorem gInvDiffSlotCoeff_eq_slotInsertEndoCc (g₀ g₁ : SmoothRiemannianMetric I M) :
    gInvDiffSlotCoeff (I := I) g₀ g₁ =
      endoSlotZeroCcTensor (I := I) (M := M) g₀ 1 (gInvDiffRaisedEndoField (I := I) g₀ g₁) := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rfl

end NormedSlotCoefficientIdentity

set_option backward.isDefEq.respectTransparency false in
omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
    in
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

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
    in
@[simp] lemma endoCompField_apply
    (A B : ContMDiffSection I (E →L[ℝ] E) ∞
      (fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x)) (x : M) :
    (endoCompField (I := I) (M := M) A B x) = (A x).comp (B x) := rfl

set_option backward.isDefEq.respectTransparency false in
omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
    in
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

section HilbertFirstDerivativeBound

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

set_option backward.isDefEq.respectTransparency false in
attribute [-instance] Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace in
theorem riemannianFiberNormSq_covGrad_gInvDiffSlotCoeff_le
    (g₀ : SmoothRiemannianMetric I M) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (g₁ : SmoothRiemannianMetric I M)
      (T : SmoothCcTensor g₀ 0 2)
      {δ : ℝ} (_hδ : δ < 1 / 2) (_hδ0 : 0 ≤ δ)
      (_h : ∀ y v w, g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ T y v w)
      (_hbound : metricCauchySchwarzBound (I := I) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
      (x : M),
      letI instTens : Bundle.RiemannianBundle
          (fun y : M => Tensor0SBundle.TensorRSSpace 0 3 I y) :=
        Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 0 3
      letI : ∀ b : M, NormedAddCommGroup (TensorRSSpace 0 3 I b) :=
        fun b => tensorRSRiemannianNormedAddCommGroup (I := I) 0 3 (h := instTens) b
      riemannianFiberNormSq (I := I) (M := M) g₀ 2 3 x
          ((covGrad (I := I) (M := M) g₀ 2 2 (gInvDiffSlotCoeff (I := I) g₀ g₁)).toSection x) ≤
        C ^ 2 * ‖((iteratedCovGrad (I := I) g₀ 0 2 1 T).toSection x :
            Tensor0SBundle.TensorRSSpace 0 3 I x)‖ ^ 2 := by
  classical
  letI instTens : Bundle.RiemannianBundle
      (fun y : M => Tensor0SBundle.TensorRSSpace 0 3 I y) :=
    Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 0 3
  letI : ∀ b : M, NormedAddCommGroup (TensorRSSpace 0 3 I b) :=
    fun b => tensorRSRiemannianNormedAddCommGroup (I := I) 0 3 (h := instTens) b
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
    (endoSlotZeroCcTensor (I := I) (M := M) g₀ 1 Λ) x]
  refine le_trans
    (Analysis.Sobolev.Tensor.riemannianFiberNormSq_covGradBundleEquiv_le_card_mul_rs
    (I := I) (M := M)
    g₀ 2 2 x _ ((Module.finrank ℝ E : ℝ) ^ 2 * (4 * C₀ * G) ^ 2) ?_) ?_
  · intro v hv
    have hΦ : tensorRSCovariantDerivative I M 2 2 (LeviCivita (I := I) g₀)
          (fun y : M => (endoSlotZeroCcTensor (I := I) (M := M) g₀ 1 Λ).toSection y) x v =
        (show TensorRSSpace 2 2 I x from
          TensorRSSpace.ofCLM (slotInsertEndoFib (I := I) (M := M) 2 0 x
            ((endoCovariantDerivative (I := I) (M := M) g₀) Λ x v))) := by
      rw [← tensorCovDerivAt_def (I := I) (M := M) g₀ 2 2
        (endoSlotZeroCcTensor (I := I) (M := M) g₀ 1 Λ) x v]
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

end HilbertFirstDerivativeBound

attribute [-instance] Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace in
omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
    [T2Space M] in
theorem norm_toSection_eq_sqrt_riemannianFiberNormSq
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (x : M) (W : SmoothCcTensor g r s) :
    letI instTens : Bundle.RiemannianBundle (fun b : M => TensorRSSpace r s I b) :=
      Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g r s
    letI : ∀ b : M, NormedAddCommGroup (TensorRSSpace r s I b) :=
      fun b => tensorRSRiemannianNormedAddCommGroup (I := I) r s (h := instTens) b
    ‖(W.toSection x : TensorRSSpace r s I x)‖ =
      Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g r s x (W.toSection x)) := by
  letI instTens : Bundle.RiemannianBundle (fun b : M => TensorRSSpace r s I b) :=
    Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g r s
  letI : ∀ b : M, NormedAddCommGroup (TensorRSSpace r s I b) :=
    fun b => tensorRSRiemannianNormedAddCommGroup (I := I) r s (h := instTens) b
  rw [norm_eq_sqrt_tensorInnerPointwise (I := I) (M := M) g r s x (W.toSection x),
    riemannianFiberNormSq_eq_tensorInnerPointwise (I := I) (M := M) g r s x (W.toSection x)]

attribute [-instance] Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace in
omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem norm_iteratedCovGrad_gInvDiffSlotCoeff_le_envelope_zero
    (g₀ g₁ : SmoothRiemannianMetric I M) (T : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ : δ < 1 / 2) (hδ0 : 0 ≤ δ)
    (h : ∀ y v w, g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ T y v w)
    (hbound : metricCauchySchwarzBound (I := I) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ) (x : M)
      (R : ℝ) :
    letI instTens : Bundle.RiemannianBundle (fun b : M => TensorRSSpace 2 2 I b) :=
      Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 2 2
    letI : ∀ b : M, NormedAddCommGroup (TensorRSSpace 2 2 I b) :=
      fun b => tensorRSRiemannianNormedAddCommGroup (I := I) 2 2 (h := instTens) b
    ‖((iteratedCovGrad (I := I) g₀ 2 2 0 (gInvDiffSlotCoeff (I := I) g₀ g₁)).toSection x :
        TensorRSSpace 2 2 I x)‖ ≤
      (Module.finrank ℝ E : ℝ) * (1 + R) ^ 0 := by
  letI instTens : Bundle.RiemannianBundle (fun b : M => TensorRSSpace 2 2 I b) :=
    Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 2 2
  letI : ∀ b : M, NormedAddCommGroup (TensorRSSpace 2 2 I b) :=
    fun b => tensorRSRiemannianNormedAddCommGroup (I := I) 2 2 (h := instTens) b
  rw [iteratedCovGrad_zero, pow_zero, mul_one,
    norm_toSection_eq_sqrt_riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x
      (gInvDiffSlotCoeff (I := I) g₀ g₁)]
  have hb := riemannianFiberNormSq_gInvDiffSlotCoeff_le (I := I) (M := M) g₀ g₁ T hδ hδ0 h hbound x
  have hfr0 : (0 : ℝ) ≤ (Module.finrank ℝ E : ℝ) := Nat.cast_nonneg _
  calc Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x
          ((gInvDiffSlotCoeff (I := I) g₀ g₁).toSection x))
      ≤ Real.sqrt ((Module.finrank ℝ E : ℝ) ^ 2) := Real.sqrt_le_sqrt hb
    _ = (Module.finrank ℝ E : ℝ) := Real.sqrt_sq hfr0

section HilbertFirstDerivativeEnvelope

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

attribute [-instance] Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace in
theorem norm_iteratedCovGrad_gInvDiffSlotCoeff_le_envelope_one
    (g₀ : SmoothRiemannianMetric I M) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (g₁ : SmoothRiemannianMetric I M) (T : SmoothCcTensor g₀ 0 2)
      {δ : ℝ} (_hδ : δ < 1 / 2) (_hδ0 : 0 ≤ δ)
      (_h : ∀ y v w, g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ T y v w)
      (_hbound : metricCauchySchwarzBound (I := I) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ) (x : M)
        {R : ℝ}
      (_hR0 : 0 ≤ R)
      (_hjet : letI inst3 : Bundle.RiemannianBundle (fun b : M => TensorRSSpace 0 3 I b) :=
          Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 0 3
        letI : ∀ b : M, NormedAddCommGroup (TensorRSSpace 0 3 I b) :=
          fun b => tensorRSRiemannianNormedAddCommGroup (I := I) 0 3 (h := inst3) b
        ‖((iteratedCovGrad (I := I) g₀ 0 2 1 T).toSection x : TensorRSSpace 0 3 I x)‖ ≤ R),
      letI inst23 : Bundle.RiemannianBundle (fun b : M => TensorRSSpace 2 3 I b) :=
        Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 2 3
      letI : ∀ b : M, NormedAddCommGroup (TensorRSSpace 2 3 I b) :=
        fun b => tensorRSRiemannianNormedAddCommGroup (I := I) 2 3 (h := inst23) b
      ‖((iteratedCovGrad (I := I) g₀ 2 2 1 (gInvDiffSlotCoeff (I := I) g₀ g₁)).toSection x :
          TensorRSSpace 2 3 I x)‖ ≤ C * (1 + R) ^ 1 := by
  obtain ⟨C, hC0, hbnd⟩ := riemannianFiberNormSq_covGrad_gInvDiffSlotCoeff_le (I := I) (M := M) g₀
  refine ⟨C, hC0, ?_⟩
  intro g₁ T δ hδ hδ0 h hbound x R hR0 hjet
  letI inst3 : Bundle.RiemannianBundle (fun b : M => TensorRSSpace 0 3 I b) :=
    Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 0 3
  letI : ∀ b : M, NormedAddCommGroup (TensorRSSpace 0 3 I b) :=
    fun b => tensorRSRiemannianNormedAddCommGroup (I := I) 0 3 (h := inst3) b
  letI inst23 : Bundle.RiemannianBundle (fun b : M => TensorRSSpace 2 3 I b) :=
    Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 2 3
  letI : ∀ b : M, NormedAddCommGroup (TensorRSSpace 2 3 I b) :=
    fun b => tensorRSRiemannianNormedAddCommGroup (I := I) 2 3 (h := inst23) b
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

end HilbertFirstDerivativeEnvelope

set_option backward.isDefEq.respectTransparency false in
omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
theorem covGrad_gInvDiffSlotCoeff_eq_covGrad_slotInsertEndoCc
    (g₀ g₁ : SmoothRiemannianMetric I M) :
    covGrad (I := I) (M := M) g₀ 2 2 (gInvDiffSlotCoeff (I := I) g₀ g₁) =
      covGrad (I := I) (M := M) g₀ 2 2
        (endoSlotZeroCcTensor (I := I) (M := M) g₀ 1 (gInvDiffRaisedEndoField (I := I) g₀ g₁)) := by
  rw [gInvDiffSlotCoeff_eq_slotInsertEndoCc (I := I) g₀ g₁]

set_option backward.isDefEq.respectTransparency false in
omit [NeZero (Module.finrank ℝ E)] in
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
omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem covGrad_gInvDiffSlotCoeff_endoCov_apply
    (g₀ g₁ : SmoothRiemannianMetric I M)
    (Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) (v : TangentSpace I x) :
    ((endoCovariantDerivative (I := I) (M := M) g₀)
        (gInvDiffRaisedEndoField (I := I) g₀ g₁) x v) (Y x) =
      - PDE.DeTurck.connDiff (I := I) g₁ g₀ x (metricComparisonEndo (I := I) g₀ g₁ x (Y x)) v
      + inverseMetricSharpFib (I := I) g₁ x
          (dualToCotangent (I := I)
            (-(cotangentToCLM (I := I) (g0FlatCLM (I := I) g₀ x (Y x))).comp
                ((PDE.DeTurck.connDiff (I := I) g₁ g₀ x).flip v)).toLinearMap) :=
  endoCov_gInvDiffRaisedField_apply (I := I) (M := M) g₀ g₁ Y x v

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless]
    [BoundarylessManifold I M] [T2Space M] in
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

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless]
    [BoundarylessManifold I M] [T2Space M] in
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

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless]
    [BoundarylessManifold I M] [T2Space M] in
private lemma tensor0SOne_apply_neg_comp (x : M) (om : Tensor0SSpace 1 I x)
    (a : TangentSpace I x) :
    om (fun _ : Fin 1 => -a) = -om (fun _ : Fin 1 => a) := by
  have h := tensor0SOne_apply_smul_comp (I := I) x om (-1) a
  simp only [neg_smul, one_smul] at h
  exact h

set_option backward.isDefEq.respectTransparency true in
def connDiffGInvCompositePairing [SigmaCompactSpace M] (g₀ g₁ : SmoothRiemannianMetric I M) (x : M)
    (om : Tensor0SSpace 1 I x) : Tensor0SSpace 2 I x :=
  (show ContinuousMultilinearMap ℝ (fun _ : Fin 2 => TangentSpace I x) ℝ from
    { toFun := fun YZ => om (fun _ : Fin 1 =>
        PDE.DeTurck.connDiff (I := I) g₁ g₀ x
          (metricComparisonEndo (I := I) g₀ g₁ x (YZ 0)) (YZ 1))
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
        have hRaised : Continuous (metricComparisonEndo (I := I) g₀ g₁ x) :=
          (metricComparisonEndo (I := I) g₀ g₁ x).continuous
        have hbil : Continuous (fun YZ : Fin 2 → TangentSpace I x =>
            PDE.DeTurck.connDiff (I := I) g₁ g₀ x
              (metricComparisonEndo (I := I) g₀ g₁ x (YZ 0)) (YZ 1)) := by
          have hc : Continuous (fun p : TangentSpace I x × TangentSpace I x =>
              PDE.DeTurck.connDiff (I := I) g₁ g₀ x p.1 p.2) :=
            (PDE.DeTurck.connDiff (I := I) g₁ g₀ x).continuous₂
          have hcomp : Continuous (fun YZ : Fin 2 → TangentSpace I x =>
              (metricComparisonEndo (I := I) g₀ g₁ x (YZ 0), YZ 1)) :=
            (hRaised.comp (continuous_apply 0)).prodMk (continuous_apply 1)
          exact hc.comp hcomp
        exact ((ContinuousMultilinearMap.coe_continuous
          (om : ContinuousMultilinearMap ℝ (fun _ : Fin 1 => TangentSpace I x) ℝ)).comp
          (continuous_pi (fun _ => hbil))) } : Tensor0SSpace 2 I x)

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M]
    [T2Space M] in
@[simp] lemma gInvCompPairing_apply (g₀ g₁ : SmoothRiemannianMetric I M) (x : M)
    (om : Tensor0SSpace 1 I x) (YZ : Fin 2 → TangentSpace I x) :
    (connDiffGInvCompositePairing (I := I) g₀ g₁ x om) YZ =
      om (fun _ : Fin 1 =>
        PDE.DeTurck.connDiff (I := I) g₁ g₀ x
          (metricComparisonEndo (I := I) g₀ g₁ x (YZ 0)) (YZ 1)) := rfl

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M]
    [T2Space M] in
lemma gInvCompPairing_add (g₀ g₁ : SmoothRiemannianMetric I M) (x : M)
    (om om' : Tensor0SSpace 1 I x) :
    connDiffGInvCompositePairing (I := I) g₀ g₁ x (om + om') =
      connDiffGInvCompositePairing (I := I) g₀ g₁ x om + connDiffGInvCompositePairing (I := I) g₀ g₁
        x om' := by
  apply ContinuousMultilinearMap.ext
  intro YZ
  exact ContinuousMultilinearMap.add_apply om om' _

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M]
    [T2Space M] in
lemma gInvCompPairing_smul (g₀ g₁ : SmoothRiemannianMetric I M) (x : M)
    (c : ℝ) (om : Tensor0SSpace 1 I x) :
    connDiffGInvCompositePairing (I := I) g₀ g₁ x (c • om) =
      c • connDiffGInvCompositePairing (I := I) g₀ g₁ x om := by
  apply ContinuousMultilinearMap.ext
  intro YZ
  exact ContinuousMultilinearMap.smul_apply om c _

def connDiffGInvCompositeFib [SigmaCompactSpace M] (g₀ g₁ : SmoothRiemannianMetric I M) (x : M) :
    TensorRSSpace 1 2 I x :=
  TensorRSSpace.ofCLM
    (LinearMap.toContinuousLinearMap
      { toFun := fun om => connDiffGInvCompositePairing (I := I) g₀ g₁ x om
        map_add' := gInvCompPairing_add (I := I) g₀ g₁ x
        map_smul' := gInvCompPairing_smul (I := I) g₀ g₁ x })

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M]
    [T2Space M] in
@[simp] lemma connDiffGInvCompositeFib_apply (g₀ g₁ : SmoothRiemannianMetric I M) (x : M)
    (om : Tensor0SSpace 1 I x) :
    (show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 2 I x from
        connDiffGInvCompositeFib (I := I) g₀ g₁ x) om =
      connDiffGInvCompositePairing (I := I) g₀ g₁ x om := rfl

set_option backward.isDefEq.respectTransparency false in
omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [BoundarylessManifold I M] [T2Space M]
    in
theorem gInvRaisedEndo_section_contMDiff (g₀ g₁ : SmoothRiemannianMetric I M)
    (Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun b : M => TotalSpace.mk' E (E := fun z : M => TangentSpace I z) b
        (metricComparisonEndo (I := I) g₀ g₁ b (Y b))) := by
  refine (inverseMetricSharpFib_g0FlatY_contMDiff (I := I) g₀ g₁ Y).congr (fun b => ?_)
  rw [gInvRaisedEndo_apply]

set_option backward.isDefEq.respectTransparency false in
omit [NeZero (Module.finrank ℝ E)] in
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
        (connDiffGInvCompositePairing (I := I) g₀ g₁ x (om x))) := by
    refine (contMDiff_multilinearSection_iff_coord (𝕜 := ℝ) (F := E)
      (E := (TangentSpace I : M → Type _)) (IB := I) (n := (∞ : WithTop ℕ∞)) (Module.finBasis ℝ E)
      (fun x : M => (connDiffGInvCompositePairing (I := I) g₀ g₁ x (om x) :
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
            (metricComparisonEndo (I := I) g₀ g₁ x (Y (σ 0) x))) (Y (σ 1) x))) :=
      PDE.DeTurck.connDiff_contMDiff (I := I) g₁ g₀
        (gInvRaisedEndo_section_contMDiff (I := I) g₀ g₁ (Y (σ 0))) (Y (σ 1)).contMDiff
    have hscalar : ContMDiffAt I 𝓘(ℝ, ℝ) ∞
        (fun x : M => Tensor0SSpace.toModel (om x)
          (fun _ : Fin 1 => ((PDE.DeTurck.connDiff (I := I) g₁ g₀ x)
            (metricComparisonEndo (I := I) g₀ g₁ x (Y (σ 0) x))) (Y (σ 1) x))) x₀ :=
      TensorMultilinear.contMDiffAt_section_apply (n := 1) (x₀ := x₀)
        (fun x : M => om x) (om.contMDiff x₀)
        (fun _ : Fin 1 => fun x : M => ((PDE.DeTurck.connDiff (I := I) g₁ g₀ x)
          (metricComparisonEndo (I := I) g₀ g₁ x (Y (σ 0) x))) (Y (σ 1) x))
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
    change (connDiffGInvCompositePairing (I := I) g₀ g₁ x (om x))
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
omit [NeZero (Module.finrank ℝ E)] in
@[simp] lemma connDiffGInvComposite_toSection (g₀ g₁ : SmoothRiemannianMetric I M) (x : M) :
    (connDiffGInvComposite (I := I) g₀ g₁).toSection x =
      connDiffGInvCompositeFib (I := I) g₀ g₁ x := rfl

set_option backward.isDefEq.respectTransparency false in
omit [NeZero (Module.finrank ℝ E)] in
lemma connDiffGInvComposite_pairing_apply (g₀ g₁ : SmoothRiemannianMetric I M) (x : M)
    (om : Tensor0SSpace 1 I x) (YZ : Fin 2 → TangentSpace I x) :
    ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 2 I x from
        (connDiffGInvComposite (I := I) g₀ g₁).toSection x) om) YZ =
      om (fun _ : Fin 1 =>
        PDE.DeTurck.connDiff (I := I) g₁ g₀ x
          (metricComparisonEndo (I := I) g₀ g₁ x (YZ 0)) (YZ 1)) := by
  rw [connDiffGInvComposite_toSection, connDiffGInvCompositeFib_apply, gInvCompPairing_apply]

set_option backward.isDefEq.respectTransparency false in
omit [NeZero (Module.finrank ℝ E)] in
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

open DifferentialGeometry.TensorMultilinear

set_option backward.isDefEq.respectTransparency false in
omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem endoCov_gInvDiffRaisedField_fibrewise
    (g₀ g₁ : SmoothRiemannianMetric I M) (x : M)
    (v0 w : TangentSpace I x) :
    ((endoCovariantDerivative (I := I) (M := M) g₀)
        (gInvDiffRaisedEndoField (I := I) g₀ g₁) x v0) w =
      - PDE.DeTurck.connDiff (I := I) g₁ g₀ x (metricComparisonEndo (I := I) g₀ g₁ x w) v0
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


end Sobolev
end Analysis
end DifferentialGeometry
