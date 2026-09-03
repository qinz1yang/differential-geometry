import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.PrincipalOperator.H2
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.PrincipalOperator.PrincipalCometricH2
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.MetricComparisonEndomorphismJetBound


noncomputable section

open Bundle Manifold MeasureTheory Set Filter DifferentialGeometry.Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Analysis.Sobolev.TensorHilbert
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Spectral.DeTurck
open DifferentialGeometry.Analysis.Spectral.MetricRealization
open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Operator

variable
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
      [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

private abbrev rank4H2 (g : SmoothRiemannianMetric I M) :=
  TensorHs (I := I) (M := M) g 0 4 (2 : ℝ)

private abbrev rank4End (g : SmoothRiemannianMetric I M) :=
  rank4H2 (I := I) (M := M) g →L[ℝ]
    rank4H2 (I := I) (M := M) g

private local instance rank4EndNorm
    (g : SmoothRiemannianMetric I M) :
    NormedAddCommGroup (rank4End (I := I) (M := M) g) :=
  ContinuousLinearMap.toNormedAddCommGroup

private local instance rank4EndSpace
    (g : SmoothRiemannianMetric I M) :
    NormedSpace ℝ (rank4End (I := I) (M := M) g) :=
  ContinuousLinearMap.toNormedSpace

private noncomputable def diffCoeff4
    (g a b : SmoothRiemannianMetric I M) :
    SmoothCcTensor g 4 4 :=
  slotInsertEndoCc (I := I) (M := M) g 3
    (metricComparisonDifferenceEndomorphismField (I := I) a b)

private noncomputable def fullCoeff4
    (g a b : SmoothRiemannianMetric I M) :
    SmoothCcTensor g 4 4 :=
  slotInsertEndoCc (I := I) (M := M) g 3
    (metricComparisonEndomorphismField (I := I) (M := M) a b)

private noncomputable def diffH2
    (g a b : SmoothRiemannianMetric I M) :
    rank4End (I := I) (M := M) g :=
  appHs (I := I) (M := M) g 4 4 2
    (diffCoeff4 (I := I) (M := M) g a b)

private noncomputable def fullH2
    (g a b : SmoothRiemannianMetric I M) :
    rank4End (I := I) (M := M) g :=
  appHs (I := I) (M := M) g 4 4 2
    (fullCoeff4 (I := I) (M := M) g a b)

omit [BoundarylessManifold I M] [NeZero (Module.finrank ℝ E)] [CompactSpace M] in
omit [I.Boundaryless] in
omit [SigmaCompactSpace M] in
private lemma raise_eq_diff
    (g₀ g₁ : SmoothRiemannianMetric I M) (T : SmoothCcTensor g₀ 0 2)
    (htie : ∀ (y : M) (v w : TangentSpace I y),
      g₁.inner y v w =
        g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ T y v w) :
    symmRaiseEndo (I := I) (M := M) g₀ T =
      metricComparisonDifferenceEndomorphismField (I := I) g₁ g₀ := by
  apply ContMDiffSection.ext
  intro x
  apply ContinuousLinearMap.ext
  intro v
  apply (metricFlatMap (I := I) g₀ x).injective
  ext w
  rw [metricFlatMap_apply, metricFlatMap_apply]
  rw [symmRaiseEndo_apply, inner_symmRaiseEndo]
  rw [show metricComparisonDifferenceEndomorphismField (I := I) g₁ g₀ x =
      metricComparisonDifferenceEndomorphism (I := I) g₁ g₀ x from rfl]
  rw [inner_g1_metricComparisonDifferenceEndomorphism (I := I) g₁ g₀ x v w]
  rw [htie x v w]
  ring

omit [BoundarylessManifold I M] [NeZero (Module.finrank ℝ E)] in
omit [I.Boundaryless] in
omit [SigmaCompactSpace M] in
private lemma perturbCoeff_eq_diff
    (g₀ g₁ : SmoothRiemannianMetric I M) (T : SmoothCcTensor g₀ 0 2)
    (htie : ∀ (y : M) (v w : TangentSpace I y),
      g₁.inner y v w =
        g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ T y v w) :
    metricPerturbationCoefficientH2 (I := I) (M := M) g₀ T =
      diffCoeff4 (I := I) (M := M) g₀ g₁ g₀ := by
  rw [metricPerturbationCoefficientH2, diffCoeff4,
    raise_eq_diff (I := I) (M := M) g₀ g₁ T htie]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [BoundarylessManifold I M] [SigmaCompactSpace M] in
omit [I.Boundaryless] in
private lemma fullField_decomp
    (g a b : SmoothRiemannianMetric I M) :
    metricComparisonEndomorphismField (I := I) (M := M) a b =
      metricComparisonDifferenceEndomorphismField (I := I) a b +
        metricComparisonEndomorphismField (I := I) (M := M) g g := by
  apply ContMDiffSection.ext
  intro x
  apply ContinuousLinearMap.ext
  intro v
  rw [metricComparisonEndomorphismField_apply]
  rw [show ((metricComparisonDifferenceEndomorphismField (I := I) a b +
      metricComparisonEndomorphismField (I := I) (M := M) g g) x) =
      metricComparisonDifferenceEndomorphismField (I := I) a b x +
        metricComparisonEndomorphismField (I := I) (M := M) g g x from by
    rw [ContMDiffSection.coe_add]
    rfl]
  rw [add_apply]
  rw [show metricComparisonDifferenceEndomorphismField (I := I) a b x =
      metricComparisonDifferenceEndomorphism (I := I) a b x from rfl]
  rw [metricComparisonEndomorphismField_apply]
  rw [metricComparisonEndomorphism_eq_diff_add_id]
  rw [metricComparisonEndomorphism_apply, inverseMetricSharpFib_g0FlatCLM]

omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] [SigmaCompactSpace M] in
omit [I.Boundaryless] in
private lemma fullCoeff_decomp
    (g a b : SmoothRiemannianMetric I M) :
    fullCoeff4 (I := I) (M := M) g a b =
      diffCoeff4 (I := I) (M := M) g a b +
        fullCoeff4 (I := I) (M := M) g g g := by
  rw [fullCoeff4, diffCoeff4, fullCoeff4,
    fullField_decomp (I := I) (M := M) g a b,
    slotInsertEndoCc_add]

private lemma fullH2_decomp
    (g a b : SmoothRiemannianMetric I M) :
    fullH2 (I := I) (M := M) g a b =
      diffH2 (I := I) (M := M) g a b +
        fullH2 (I := I) (M := M) g g g := by
  apply ContinuousLinearMap.ext
  intro U
  simp only [fullH2, diffH2, add_apply]
  rw [fullCoeff_decomp (I := I) (M := M) g a b]
  exact appHs_add (I := I) (M := M) g 4 4 2
    (diffCoeff4 (I := I) (M := M) g a b)
    (fullCoeff4 (I := I) (M := M) g g g) U

omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] [SigmaCompactSpace M] in
omit [I.Boundaryless] in
private lemma fullCoeff_self
    (g : SmoothRiemannianMetric I M) (W : SmoothCcTensor g 0 4) :
    operatorFieldApply (I := I) (M := M) g 4 4
        (fullCoeff4 (I := I) (M := M) g g g) W = W := by
  apply smoothCcTensor_ext_of_unitModel (I := I) (M := M) g
  intro x
  simp only [unitModel]
  rw [operatorFieldApplication_toSection]
  simp only [fullCoeff4, slotInsertEndoCc_toSection,
    metricComparisonEndomorphismField_apply]
  have hid : metricComparisonEndomorphism (I := I) g g x =
      ContinuousLinearMap.id ℝ (TangentSpace I x) := by
    apply ContinuousLinearMap.ext
    intro v
    rw [metricComparisonEndomorphism_apply, inverseMetricSharpFib_g0FlatCLM,
      ContinuousLinearMap.id_apply]
  change metricComparisonEndomorphism (I := I) g g x =
    ContinuousLinearMap.id ℝ (TangentSpace I x) at hid
  rw [hid, slotInsertFib_id, ContinuousLinearMap.id_comp]

private lemma fullH2_self
    (g : SmoothRiemannianMetric I M) :
    fullH2 (I := I) (M := M) g g g = 1 := by
  rw [ContinuousLinearMap.one_def]
  apply ContinuousLinearMap.ext
  intro U
  let ι := ccToHsLin (I := I) (M := M) g 4 (2 : ℝ)
  have hdense : DenseRange ι :=
    ccToHsLin_dense (I := I) (M := M) g 4 (by positivity)
  have hfun := hdense.equalizer
    (fullH2 (I := I) (M := M) g g g).continuous
    (ContinuousLinearMap.id ℝ
      (rank4H2 (I := I) (M := M) g)).continuous (by
      funext W
      simp only [Function.comp_apply, ι, ccToHsLin_apply,
        ContinuousLinearMap.id_apply]
      calc
        fullH2 (I := I) (M := M) g g g
            (ccTensorToHs (I := I) (M := M) g 4 (2 : ℝ) W) =
            ccTensorToHs (I := I) (M := M) g 4 (2 : ℝ)
              (operatorFieldApply (I := I) (M := M) g 4 4
                (fullCoeff4 (I := I) (M := M) g g g) W) := by
                  exact appHs_core (I := I) (M := M) g 4 4 2
                    (fullCoeff4 (I := I) (M := M) g g g) W
        _ = ccTensorToHs (I := I) (M := M) g 4 (2 : ℝ) W := by
          rw [fullCoeff_self (I := I) (M := M) g W])
  exact congrFun hfun U

private lemma fullH2_sub_one
    (g a b : SmoothRiemannianMetric I M) :
    fullH2 (I := I) (M := M) g a b - 1 =
      diffH2 (I := I) (M := M) g a b := by
  rw [fullH2_decomp (I := I) (M := M) g a b,
    fullH2_self (I := I) (M := M) g]
  abel

omit [NeZero (Module.finrank ℝ E)] in
omit [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma raised_cancel
    (g₀ g₁ : SmoothRiemannianMetric I M) (x : M) :
    (metricComparisonEndomorphism (I := I) g₁ g₀ x).comp
        (metricComparisonEndomorphism (I := I) g₀ g₁ x) =
      ContinuousLinearMap.id ℝ (TangentSpace I x) := by
  apply ContinuousLinearMap.ext
  intro v
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply,
    metricComparisonEndomorphism_apply, metricComparisonEndomorphism_apply]
  rw [g0FlatCLM_inverseMetricSharpFib (I := I) g₁ x
    (g0FlatCLM (I := I) g₀ x v)]
  rw [inverseMetricSharpFib_g0FlatCLM (I := I) g₀ x v]

omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] [SigmaCompactSpace M] in
omit [I.Boundaryless] in
private lemma fullCoeff_cancel
    (g₀ g₁ : SmoothRiemannianMetric I M)
    (W : SmoothCcTensor g₀ 0 4) :
    operatorFieldApply (I := I) (M := M) g₀ 4 4
        (fullCoeff4 (I := I) (M := M) g₀ g₀ g₁)
        (operatorFieldApply (I := I) (M := M) g₀ 4 4
          (fullCoeff4 (I := I) (M := M) g₀ g₁ g₀) W) = W := by
  apply smoothCcTensor_ext_of_unitModel (I := I) (M := M) g₀
  intro x
  simp only [unitModel]
  rw [operatorFieldApplication_toSection, operatorFieldApplication_toSection]
  rw [← ContinuousLinearMap.comp_assoc]
  simp only [fullCoeff4, slotInsertEndoCc_toSection,
    metricComparisonEndomorphismField_apply]
  rw [slotInsertFib_comp, raised_cancel, slotInsertFib_id,
    ContinuousLinearMap.id_comp]

private lemma fullH2_mul
    (g₀ g₁ : SmoothRiemannianMetric I M) :
    fullH2 (I := I) (M := M) g₀ g₀ g₁ *
        fullH2 (I := I) (M := M) g₀ g₁ g₀ = 1 := by
  rw [ContinuousLinearMap.mul_def, ContinuousLinearMap.one_def]
  apply ContinuousLinearMap.ext
  intro U
  let ι := ccToHsLin (I := I) (M := M) g₀ 4 (2 : ℝ)
  let L := (fullH2 (I := I) (M := M) g₀ g₀ g₁).comp
    (fullH2 (I := I) (M := M) g₀ g₁ g₀)
  let R := ContinuousLinearMap.id ℝ
    (rank4H2 (I := I) (M := M) g₀)
  have hdense : DenseRange ι :=
    ccToHsLin_dense (I := I) (M := M) g₀ 4 (by positivity)
  have hfun := hdense.equalizer L.continuous R.continuous (by
    funext W
    simp only [Function.comp_apply, L, R, ι, ccToHsLin_apply,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply]
    calc
      fullH2 (I := I) (M := M) g₀ g₀ g₁
          (fullH2 (I := I) (M := M) g₀ g₁ g₀
            (ccTensorToHs (I := I) (M := M) g₀ 4 (2 : ℝ) W)) =
          fullH2 (I := I) (M := M) g₀ g₀ g₁
            (ccTensorToHs (I := I) (M := M) g₀ 4 (2 : ℝ)
              (operatorFieldApply (I := I) (M := M) g₀ 4 4
                (fullCoeff4 (I := I) (M := M) g₀ g₁ g₀) W)) := by
            congr 1
            exact appHs_core (I := I) (M := M) g₀ 4 4 2
              (fullCoeff4 (I := I) (M := M) g₀ g₁ g₀) W
      _ = ccTensorToHs (I := I) (M := M) g₀ 4 (2 : ℝ)
            (operatorFieldApply (I := I) (M := M) g₀ 4 4
              (fullCoeff4 (I := I) (M := M) g₀ g₀ g₁)
              (operatorFieldApply (I := I) (M := M) g₀ 4 4
                (fullCoeff4 (I := I) (M := M) g₀ g₁ g₀) W)) := by
            exact appHs_core (I := I) (M := M) g₀ 4 4 2
              (fullCoeff4 (I := I) (M := M) g₀ g₀ g₁)
              (operatorFieldApply (I := I) (M := M) g₀ 4 4
                (fullCoeff4 (I := I) (M := M) g₀ g₁ g₀) W)
      _ = ccTensorToHs (I := I) (M := M) g₀ 4 (2 : ℝ) W := by
        rw [fullCoeff_cancel (I := I) (M := M) g₀ g₁ W])
  exact congrFun hfun U

private lemma perturbH2_eq_diff
    (hDim : Module.finrank ℝ E = 3)
    (g₀ g₁ : SmoothRiemannianMetric I M) (T : SmoothCcTensor g₀ 0 2)
    (htie : ∀ (y : M) (v w : TangentSpace I y),
      g₁.inner y v w =
        g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ T y v w) :
    metricPerturbationOperatorH2 (I := I) (M := M) g₀
        (ccTensorToHs (I := I) (M := M) g₀ 2 (2 : ℝ) T) =
      diffH2 (I := I) (M := M) g₀ g₁ g₀ := by
  rw [metricPerturbationOperatorH2_apply_smoothCore (I := I) (M := M) hDim g₀ T,
    diffH2, perturbCoeff_eq_diff (I := I) (M := M) g₀ g₁ T htie]

private lemma totalH2_eq
    (hDim : Module.finrank ℝ E = 3)
    (g₀ g₁ : SmoothRiemannianMetric I M) (T : SmoothCcTensor g₀ 0 2)
    (htie : ∀ (y : M) (v w : TangentSpace I y),
      g₁.inner y v w =
        g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ T y v w) :
    1 + metricPerturbationOperatorH2 (I := I) (M := M) g₀
        (ccTensorToHs (I := I) (M := M) g₀ 2 (2 : ℝ) T) =
      fullH2 (I := I) (M := M) g₀ g₁ g₀ := by
  rw [fullH2_decomp (I := I) (M := M) g₀ g₁ g₀,
    fullH2_self (I := I) (M := M) g₀,
    perturbH2_eq_diff (I := I) (M := M) hDim g₀ g₁ T htie]
  abel

private lemma fullH2_inverse
    (hDim : Module.finrank ℝ E = 3)
    (g₀ g₁ : SmoothRiemannianMetric I M) (T : SmoothCcTensor g₀ 0 2)
    (htie : ∀ (y : M) (v w : TangentSpace I y),
      g₁.inner y v w =
        g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ T y v w)
    (hsmall : ‖metricPerturbationOperatorH2 (I := I) (M := M) g₀
      (ccTensorToHs (I := I) (M := M) g₀ 2 (2 : ℝ) T)‖ < 1) :
    Ring.inverse (1 + metricPerturbationOperatorH2 (I := I) (M := M) g₀
        (ccTensorToHs (I := I) (M := M) g₀ 2 (2 : ℝ) T)) =
      fullH2 (I := I) (M := M) g₀ g₀ g₁ := by
  let B := metricPerturbationOperatorH2 (I := I) (M := M) g₀
    (ccTensorToHs (I := I) (M := M) g₀ 2 (2 : ℝ) T)
  have hneg : ‖-B‖ < 1 := by
    simpa only [norm_neg, B] using hsmall
  have hu : IsUnit (1 + B) := by
    have h := isUnit_one_sub_of_norm_lt_one (x := -B) hneg
    simpa only [sub_neg_eq_add] using h
  have hleft :
      fullH2 (I := I) (M := M) g₀ g₀ g₁ * (1 + B) = 1 := by
    rw [show 1 + B = fullH2 (I := I) (M := M) g₀ g₁ g₀ from by
      simpa only [B] using
        totalH2_eq (I := I) (M := M) hDim g₀ g₁ T htie]
    exact fullH2_mul (I := I) (M := M) g₀ g₁
  have hgeom :
      fullH2 (I := I) (M := M) g₀ g₀ g₁ =
        Ring.inverse (1 + B) := by
    calc
      fullH2 (I := I) (M := M) g₀ g₀ g₁ =
          fullH2 (I := I) (M := M) g₀ g₀ g₁ * 1 :=
        (mul_one _).symm
      _ = fullH2 (I := I) (M := M) g₀ g₀ g₁ *
          ((1 + B) * Ring.inverse (1 + B)) := by
            rw [Ring.mul_inverse_cancel (1 + B) hu]
      _ = (fullH2 (I := I) (M := M) g₀ g₀ g₁ * (1 + B)) *
          Ring.inverse (1 + B) := by
            rw [mul_assoc]
      _ = Ring.inverse (1 + B) := by
        rw [hleft, one_mul]
  simpa only [B] using hgeom.symm

theorem inverseMetricPerturbationCorrectionH2_apply_smoothCore
    (hDim : Module.finrank ℝ E = 3)
    (g₀ g₁ : SmoothRiemannianMetric I M) (T : SmoothCcTensor g₀ 0 2)
    (htie : ∀ (y : M) (v w : TangentSpace I y),
      g₁.inner y v w =
        g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ T y v w)
    (hsmall : ‖metricPerturbationOperatorH2 (I := I) (M := M) g₀
      (ccTensorToHs (I := I) (M := M) g₀ 2 (2 : ℝ) T)‖ < 1) :
    inverseMetricPerturbationCorrectionH2 (I := I) (M := M) g₀
        (ccTensorToHs (I := I) (M := M) g₀ 2 (2 : ℝ) T) =
      appHs (I := I) (M := M) g₀ 4 4 2
        (slotInsertEndoCc (I := I) (M := M) g₀ 3
          (metricComparisonDifferenceEndomorphismField (I := I) g₀ g₁)) := by
  change inverseMetricPerturbationCorrectionH2 (I := I) (M := M) g₀
      (ccTensorToHs (I := I) (M := M) g₀ 2 (2 : ℝ) T) =
    diffH2 (I := I) (M := M) g₀ g₀ g₁
  rw [inverseMetricPerturbationCorrectionH2,
    fullH2_inverse (I := I) (M := M) hDim g₀ g₁ T htie hsmall,
    fullH2_sub_one (I := I) (M := M) g₀ g₀ g₁]

theorem lowRegularityPrincipalOperatorH2_apply_smoothCore
    (hDim : Module.finrank ℝ E = 3)
    (g₀ g₁ : SmoothRiemannianMetric I M) (T : SmoothCcTensor g₀ 0 2)
    (htie : ∀ (y : M) (v w : TangentSpace I y),
      g₁.inner y v w =
        g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ T y v w)
    (hsmall : ‖metricPerturbationOperatorH2 (I := I) (M := M) g₀
      (ccTensorToHs (I := I) (M := M) g₀ 2 (2 : ℝ) T)‖ < 1) :
    lowRegularityPrincipalOperatorH2 (I := I) (M := M) g₀
        (ccTensorToHs (I := I) (M := M) g₀ 2 (2 : ℝ) T) =
      principalCometricOperatorH2 (I := I) (M := M) g₀ g₁ := by
  apply ContinuousLinearMap.ext
  intro U
  let ι := ccToHsLin (I := I) (M := M) g₀ 2 (4 : ℝ)
  have hdense : DenseRange ι :=
    ccToHsLin_dense (I := I) (M := M) g₀ 2 (by positivity)
  have hfun := hdense.equalizer
    (lowRegularityPrincipalOperatorH2 (I := I) (M := M) g₀
      (ccTensorToHs (I := I) (M := M) g₀ 2 (2 : ℝ) T)).continuous
    (principalCometricOperatorH2 (I := I) (M := M) g₀ g₁).continuous (by
      funext W
      simp only [Function.comp_apply, ι, ccToHsLin_apply]
      calc
        lowRegularityPrincipalOperatorH2 (I := I) (M := M) g₀
            (ccTensorToHs (I := I) (M := M) g₀ 2 (2 : ℝ) T)
            (ccTensorToHs (I := I) (M := M) g₀ 2 (4 : ℝ) W) =
            cometricDoubleTraceH2 (I := I) (M := M) g₀
              (inverseMetricPerturbationCorrectionH2 (I := I) (M := M) g₀
                (ccTensorToHs (I := I) (M := M) g₀ 2 (2 : ℝ) T)
                (secondCovariantDerivativeH4ToH2 (I := I) (M := M) g₀
                  (ccTensorToHs (I := I) (M := M) g₀ 2 (4 : ℝ) W))) := by
                    rfl
        _ = cometricDoubleTraceH2 (I := I) (M := M) g₀
              (appHs (I := I) (M := M) g₀ 4 4 2
                (slotInsertEndoCc (I := I) (M := M) g₀ 3
                  (metricComparisonDifferenceEndomorphismField (I := I) g₀ g₁))
                (ccTensorToHs (I := I) (M := M) g₀ 4 (2 : ℝ)
                  (iteratedCovGrad (I := I) g₀ 0 2 2 W))) := by
                    rw [hessianH2_core (I := I) (M := M) g₀ W,
                      inverseMetricPerturbationCorrectionH2_apply_smoothCore (I := I) (M := M)
                        hDim g₀ g₁ T htie hsmall]
        _ = cometricDoubleTraceH2 (I := I) (M := M) g₀
              (ccTensorToHs (I := I) (M := M) g₀ 4 (2 : ℝ)
                (operatorFieldApply (I := I) (M := M) g₀ 4 4
                  (slotInsertEndoCc (I := I) (M := M) g₀ 3
                    (metricComparisonDifferenceEndomorphismField (I := I) g₀ g₁))
                  (iteratedCovGrad (I := I) g₀ 0 2 2 W))) := by
                    congr 1
                    exact appHs_core (I := I) (M := M) g₀ 4 4 2
                      (slotInsertEndoCc (I := I) (M := M) g₀ 3
                        (metricComparisonDifferenceEndomorphismField (I := I) g₀ g₁))
                      (iteratedCovGrad (I := I) g₀ 0 2 2 W)
        _ = ccTensorToHs (I := I) (M := M) g₀ 2 (2 : ℝ)
              (operatorFieldApply (I := I) (M := M) g₀ 4 2
                (cometricDoubleTraceField (I := I) g₀ 2)
                (operatorFieldApply (I := I) (M := M) g₀ 4 4
                  (slotInsertEndoCc (I := I) (M := M) g₀ 3
                    (metricComparisonDifferenceEndomorphismField (I := I) g₀ g₁))
                  (iteratedCovGrad (I := I) g₀ 0 2 2 W))) := by
                    exact traceH2_core (I := I) (M := M) g₀ _
        _ = ccTensorToHs (I := I) (M := M) g₀ 2 (2 : ℝ)
              (deTurckPrincipalCometricArm (I := I) (M := M) g₀ g₁ W) := by
                    congr 1
                    rw [deTurckPrincipalCometricArm,
                      deTurckPrincipalCometricCoeff_eq_operatorFieldComposition_doubleTrace_slotInsertEndo]
                    change operatorFieldApply (I := I) (M := M) g₀ 4 2
                        (cometricDoubleTraceField (I := I) g₀ 2)
                        (operatorFieldApply (I := I) (M := M) g₀ 4 4
                          (endoSlotZeroCcTensor (I := I) (M := M) g₀ 3
                            (metricComparisonDifferenceEndomorphismField (I := I) g₀ g₁))
                          (iteratedCovGrad (I := I) g₀ 0 2 2 W)) = _
                    exact operatorFieldApplication_assoc (I := I) (M := M) g₀ 4 4 2 _ _ _
        _ = principalCometricOperatorH2 (I := I) (M := M) g₀ g₁
              (ccTensorToHs (I := I) (M := M) g₀ 2 (4 : ℝ) W) := by
                    exact
                      (principalCometricOperatorH2_apply_smoothCore (I := I) (M := M)
                        hDim g₀ g₁ W).symm)
  exact congrFun hfun U

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

end
