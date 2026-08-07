import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.DeTurckRemainderTameLipschitzLieCorrectionNormBounds
open DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Analysis.Elliptic
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Curvature


noncomputable section

open MeasureTheory Set Filter Topology Bundle Manifold DifferentialGeometry.Tensor0SBundle ContinuousLinearMap
open scoped ENNReal NNReal BigOperators Manifold ContDiff

namespace DifferentialGeometry.Analysis.Spectral

open LieCorr0Core
open DifferentialGeometry
open DifferentialGeometry.PDE.RicciFlow DifferentialGeometry.Analysis.Sobolev DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Analysis.Spectral.MetricRealization
open DifferentialGeometry.Integral.L2

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
  (chartRiemannTensor extChartAt_target_subset_interior_of_boundaryless)
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
  (covGrad unitModel smoothCcTensor_ext_of_unitModel unitTensor pathIntegralCoeffField
  pathIntegralCoeffField_appCc_eq pathIntegralCoeffField_toSection linearizedRicciThreeArmHjoint
  linearizedRicciThreeArmHcont linearizedRicciThreeArmHjoint_zero
  exists_linearizedRicci_threeArm_coeffFields ricciTensor_realize_sub_eq_threeArm_appCc
  linearizedRicciArm0Field linearizedRicciArm1Field linearizedRicciArm2FieldLichnerowicz
  linearizedRicciArm0BaseCoeff linearizedRicciArm0CorrField linearizedRicciArm1BaseCoeff
  linearizedRicciArm1CorrField ricciArmPrincipalCoeff traceHessianCoeff
  linearizedRicci_arm0Field_jointSmooth linearizedRicci_arm1Field_jointSmooth
  linearizedRicci_arm2FieldLichnerowicz_jointSmooth ricciArmOrder1KoszulCoeff
  exists_arm1Koszul_realizedFam_rfns_ballUniform continuousBilinearMap_basis_expand
  unitModel_basis_expand_two unitModel_eq_ccTensorBilin_local appCc_zero_left_local ccTensor02Symm
  symmS_sub ccTensorBilin_symmS iteratedCovGrad_symmS_eq domDomCongrSection
  riemannianFiberNormSq_iteratedCovGrad_domDomCongrSection)
open DifferentialGeometry.PDE.DeTurck (deTurckVF)
open DifferentialGeometry.PDE.DeTurck.RicciLinearization
  (realizedSmallSet realizedSmallSet_isOpen Icc_subset_realizedSmallSet linearizedRicciAt
  ricciTensor_realized_sub_eq_integral_linearizedRicci linearizedRicciAt_eq_deriv_chartSum_on_Ioo
  realizedRicciChartSum jointContMDiff_toModel_continuous_slice
  hasDerivAt_realizedRicciChartSum_general realizedFam)
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
  (symmAbsorbedCoeff symmAbsorbedCoeff_appCc_eq exists_iteratedCovGrad_unitModel_domDomCongrSection
  symmAbsorbedCoeff_riemannianFiberNormSq_le symmAbsorbedCoeff_jet_le)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M]

private local instance instCompleteSpaceE_tame : CompleteSpace E :=
  FiniteDimensional.complete ℝ E

section LieCorr0BoundsAll

set_option backward.isDefEq.respectTransparency false

open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
  (deTurckLieWEndo deTurckLieWEndo_apply deTurckLieWEndo_homSection_contMDiff deTurckVFCovDeriv
  connDiffOp_homSection_contMDiff metricConnDiffLoweredFib metricConnDiffLoweredFib_toModel
  metricConnDiffLoweredFib_contMDiff domDomCongrFibRank domDomCongrFibRank_apply
  tensor0SProdKappaFib tensor0SProdKappaFib_apply)
open DifferentialGeometry.Analysis.Spectral.DeTurck
  (cometricDoubleTraceFib cometricDoubleTraceFib_toModel cometricDoubleTraceFib_contMDiff)

section LieCorr0BoundsB

open DifferentialGeometry.Analysis.Spectral.DeTurck (cometricRaiseSlot0Fib)

open DifferentialGeometry.Analysis.Parabolic.TensorSpectral

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
    [T2Space M] in
lemma lc0b_interior_product_toModel_eval (s : ℕ) (x : M) (v : TangentSpace I x)
    (D : Tensor0SSpace (s + 1) I x) (w : Fin s → TangentSpace I x) :
    Tensor0SSpace.toModel
        (Tensor0SBundle.interior_product (𝕜 := ℝ) (I := I) s x v D) w =
      Tensor0SSpace.toModel D (Fin.cons (show E from v) (fun k => (show E from w k))) := by
  have h1 : Tensor0SSpace.toModel
      (Tensor0SBundle.interior_product (𝕜 := ℝ) (I := I) s x v D) =
      Tensor0SBundle.model_interior_product (𝕜 := ℝ) (E := E) s (show E from v)
        (Tensor0SSpace.toModel D) := rfl
  rw [h1]
  rfl

def lc0KappaField (g₁ gB : SmoothRiemannianMetric I M) :
    Tensor0SBundle.Tensor0SField (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) ∞ 3 :=
  letI := Tensor0SBundle.tensor0SBundle_topology (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) 3
  ⟨fun x => metricConnDiffLoweredFib (I := I) g₁ g₁ gB x,
    metricConnDiffLoweredFib_contMDiff (I := I) g₁ g₁ gB⟩

def lc0Kappa (g₀ g₁ gB : SmoothRiemannianMetric I M) : SmoothCcTensor g₀ 0 3 where
  toSection :=
    MixedSection.fromMultilinearSection (𝕜 := ℝ) (F := E) (IB := I)
      (E := (TangentSpace I : M → Type _)) ∞ (lc0KappaField (I := I) (M := M) g₁ gB)
  hasCompactSupport := HasCompactSupport.of_compactSpace _

omit [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
lemma lc0Kappa_unitModel_apply (g₀ g₁ gB : SmoothRiemannianMetric I M) (x : M)
    (m : Fin 3 → TangentSpace I x) :
    unitModel (I := I) (M := M) g₀ 3 (lc0Kappa (I := I) (M := M) g₀ g₁ gB) x m =
      g₁.inner x (PDE.DeTurck.connDiff (I := I) g₁ gB x (m 0) (m 1)) (m 2) := by
  rw [unitModel]
  rw [show (lc0Kappa (I := I) (M := M) g₀ g₁ gB).toSection x
      (unitTensor (I := I) (M := M) x) =
      (MixedSection.eval₀ (F := E) (E := (TangentSpace I : M → Type _)) x).smulRight
          (lc0KappaField (I := I) (M := M) g₁ gB x)
          (ContinuousMultilinearMap.constOfIsEmpty ℝ (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ))
      from rfl]
  rw [ContinuousLinearMap.smulRight_apply, MixedSection.eval₀_apply,
    ContinuousMultilinearMap.constOfIsEmpty_apply, one_smul]
  exact metricConnDiffLoweredFib_toModel (I := I) g₁ g₁ gB x m

private def lc0LowFixField (g₀ gB : SmoothRiemannianMetric I M) :
    Tensor0SBundle.Tensor0SField (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) ∞ 3 :=
  letI := Tensor0SBundle.tensor0SBundle_topology (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) 3
  ⟨fun x => metricConnDiffLoweredFib (I := I) g₀ g₀ gB x,
    metricConnDiffLoweredFib_contMDiff (I := I) g₀ g₀ gB⟩

def lc0LowFix (g₀ gB : SmoothRiemannianMetric I M) : SmoothCcTensor g₀ 0 3 where
  toSection :=
    MixedSection.fromMultilinearSection (𝕜 := ℝ) (F := E) (IB := I)
      (E := (TangentSpace I : M → Type _)) ∞ (lc0LowFixField (I := I) (M := M) g₀ gB)
  hasCompactSupport := HasCompactSupport.of_compactSpace _

omit [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
private lemma lc0LowFix_unitModel_apply (g₀ gB : SmoothRiemannianMetric I M) (x : M)
    (m : Fin 3 → TangentSpace I x) :
    unitModel (I := I) (M := M) g₀ 3 (lc0LowFix (I := I) (M := M) g₀ gB) x m =
      g₀.inner x (PDE.DeTurck.connDiff (I := I) g₀ gB x (m 0) (m 1)) (m 2) := by
  rw [unitModel]
  rw [show (lc0LowFix (I := I) (M := M) g₀ gB).toSection x
      (unitTensor (I := I) (M := M) x) =
      (MixedSection.eval₀ (F := E) (E := (TangentSpace I : M → Type _)) x).smulRight
          (lc0LowFixField (I := I) (M := M) g₀ gB x)
          (ContinuousMultilinearMap.constOfIsEmpty ℝ (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ))
      from rfl]
  rw [ContinuousLinearMap.smulRight_apply, MixedSection.eval₀_apply,
    ContinuousMultilinearMap.constOfIsEmpty_apply, one_smul]
  exact metricConnDiffLoweredFib_toModel (I := I) g₀ g₀ gB x m

private def lc0PbLowField (g₀ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
    (gA gB : SmoothRiemannianMetric I M) :
    Tensor0SBundle.Tensor0SField (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) ∞ 3 :=
  letI := Tensor0SBundle.tensor0SBundle_topology (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) 3
  ⟨fun x => ccBilinConnDiffLoweredFib (I := I) g₀ P gA gB x,
    ccBilinConnDiffLoweredFib_contMDiff (I := I) g₀ P gA gB⟩

def lc0PbLow (g₀ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
    (gA gB : SmoothRiemannianMetric I M) : SmoothCcTensor g₀ 0 3 where
  toSection :=
    MixedSection.fromMultilinearSection (𝕜 := ℝ) (F := E) (IB := I)
      (E := (TangentSpace I : M → Type _)) ∞ (lc0PbLowField (I := I) (M := M) g₀ P gA gB)
  hasCompactSupport := HasCompactSupport.of_compactSpace _

omit [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma lc0PbLow_unitModel_apply (g₀ : SmoothRiemannianMetric I M)
    (P : SmoothCcTensor g₀ 0 2) (gA gB : SmoothRiemannianMetric I M) (x : M)
    (m : Fin 3 → TangentSpace I x) :
    unitModel (I := I) (M := M) g₀ 3 (lc0PbLow (I := I) (M := M) g₀ P gA gB) x m =
      ccTensorBilinSymm (I := I) g₀ P x
        (PDE.DeTurck.connDiff (I := I) gA gB x (m 0) (m 1)) (m 2) := by
  rw [unitModel]
  rw [show (lc0PbLow (I := I) (M := M) g₀ P gA gB).toSection x
      (unitTensor (I := I) (M := M) x) =
      (MixedSection.eval₀ (F := E) (E := (TangentSpace I : M → Type _)) x).smulRight
          (lc0PbLowField (I := I) (M := M) g₀ P gA gB x)
          (ContinuousMultilinearMap.constOfIsEmpty ℝ (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ))
      from rfl]
  rw [ContinuousLinearMap.smulRight_apply, MixedSection.eval₀_apply,
    ContinuousMultilinearMap.constOfIsEmpty_apply, one_smul]
  exact ccBilinConnDiffLoweredFib_toModel (I := I) g₀ P gA gB x m

omit [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma lc0b_connDiffLowered_unitModel_apply (g₀ g₁ : SmoothRiemannianMetric I M)
    (x : M) (m : Fin 3 → TangentSpace I x) :
    unitModel (I := I) (M := M) g₀ 3 (connDiffLoweredCc (I := I) g₀ g₁) x m =
      g₀.inner x (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (m 0) (m 1)) (m 2) := by
  rw [unitModel]
  rw [show (connDiffLoweredCc (I := I) g₀ g₁).toSection x (unitTensor (I := I) (M := M) x) =
      (MixedSection.eval₀ (F := E) (E := (TangentSpace I : M → Type _)) x).smulRight
          (connDiffLoweredField (I := I) g₀ g₁ x)
          (ContinuousMultilinearMap.constOfIsEmpty ℝ (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ))
      from rfl]
  rw [ContinuousLinearMap.smulRight_apply, MixedSection.eval₀_apply,
    ContinuousMultilinearMap.constOfIsEmpty_apply, one_smul]
  rfl

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
    [T2Space M] in
private lemma lc0b_unitModel_add (g₀ : SmoothRiemannianMetric I M) (s : ℕ)
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

omit [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
theorem lc0b_kappa_decomp (g₀ g₁ gB : SmoothRiemannianMetric I M)
    (P : SmoothCcTensor g₀ 0 2)
    (htie : ∀ (y : M) (v w : TangentSpace I y),
      g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w) :
    lc0Kappa (I := I) (M := M) g₀ g₁ gB =
      connDiffLoweredCc (I := I) g₀ g₁ + lc0LowFix (I := I) (M := M) g₀ gB
        + lc0PbLow (I := I) (M := M) g₀ P g₁ g₀
        + lc0PbLow (I := I) (M := M) g₀ P g₀ gB := by
  apply smoothCcTensor_ext_of_unitModel (I := I) (M := M) g₀
  intro x
  apply ContinuousMultilinearMap.ext
  intro m
  rw [lc0b_unitModel_add (I := I) (M := M) g₀ 3 _ _ x m,
    lc0b_unitModel_add (I := I) (M := M) g₀ 3 _ _ x m,
    lc0b_unitModel_add (I := I) (M := M) g₀ 3 _ _ x m]
  rw [lc0Kappa_unitModel_apply (I := I) (M := M) g₀ g₁ gB x m,
    lc0b_connDiffLowered_unitModel_apply (I := I) (M := M) g₀ g₁ x m,
    lc0LowFix_unitModel_apply (I := I) (M := M) g₀ gB x m,
    lc0PbLow_unitModel_apply (I := I) (M := M) g₀ P g₁ g₀ x m,
    lc0PbLow_unitModel_apply (I := I) (M := M) g₀ P g₀ gB x m]
  rw [htie x (PDE.DeTurck.connDiff (I := I) g₁ gB x (m 0) (m 1)) (m 2)]
  rw [PDE.DeTurck.connDiff_cocycle (I := I) g₀ g₁ gB x (m 0) (m 1)]
  rw [map_add (g₀.inner x), map_add (ccTensorBilinSymm (I := I) g₀ P x)]
  rw [ContinuousLinearMap.add_apply, ContinuousLinearMap.add_apply]
  ring

omit [NeZero (Module.finrank ℝ E)] in
private lemma lc0b_koszulCovecCc_unitModel_eq_connDiff_g1_inner
    (g₀ g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
    (htie : ∀ (y : M) (v w : TangentSpace I y),
      g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
    (x : M) (a b c : TangentSpace I x) :
    unitModel (I := I) (M := M) g₀ 3 (koszulCovecCc (I := I) g₀ P) x ![c, a, b] =
      g₁.inner x (PDE.DeTurck.connDiff (I := I) g₁ g₀ x a b) c := by
  rw [koszulCovecCc_unitModel (I := I) (M := M) g₀ P x a b c]
  rw [connDiffInner_g1_eq_half_covGradSymmS (I := I) g₀ g₁ P htie x a b c]
  rfl

omit [NeZero (Module.finrank ℝ E)] in
/-- On the self-background arm, lowering the connection difference by the moving
metric cancels the inverse metric exactly and leaves the linear Koszul covector,
up to a cyclic permutation of its covariant slots. -/
theorem lc0Kappa_self_eq_koszulCovecCc (g₀ g₁ : SmoothRiemannianMetric I M)
    (P : SmoothCcTensor g₀ 0 2)
    (htie : ∀ (y : M) (v w : TangentSpace I y),
      g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w) :
    lc0Kappa (I := I) (M := M) g₀ g₁ g₀ =
      domDomCongrSection (I := I) g₀ (finRotate 3).symm
        (koszulCovecCc (I := I) g₀ P) := by
  apply smoothCcTensor_ext_of_unitModel (I := I) (M := M) g₀
  intro x
  apply ContinuousMultilinearMap.ext
  intro m
  rw [lc0Kappa_unitModel_apply (I := I) (M := M) g₀ g₁ g₀ x m]
  rw [domDomCongrSection_unitModel (I := I) g₀ (finRotate 3).symm
    (koszulCovecCc (I := I) g₀ P) x]
  rw [ContinuousMultilinearMap.domDomCongr_apply]
  have hargs :
      (fun i => m ((finRotate 3).symm i)) = ![m 2, m 0, m 1] := by
    funext i
    fin_cases i
    · change m ((finRotate 3).symm 0) = m 2
      rw [show (finRotate 3).symm (0 : Fin 3) = 2 by decide]
    · change m ((finRotate 3).symm 1) = m 0
      rw [show (finRotate 3).symm (1 : Fin 3) = 0 by decide]
    · change m ((finRotate 3).symm 2) = m 1
      rw [show (finRotate 3).symm (2 : Fin 3) = 1 by decide]
  rw [hargs]
  exact (lc0b_koszulCovecCc_unitModel_eq_connDiff_g1_inner
    (I := I) (M := M) g₀ g₁ P htie x (m 0) (m 1) (m 2)).symm

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless]
    [BoundarylessManifold I M] [T2Space M] in
private lemma lc0b_unitModel_sub (g₀ : SmoothRiemannianMetric I M) (s : ℕ)
    (A B : SmoothCcTensor g₀ 0 s) (x : M) (m : Fin s → TangentSpace I x) :
    unitModel (I := I) (M := M) g₀ s (A - B) x m =
      unitModel (I := I) (M := M) g₀ s A x m -
        unitModel (I := I) (M := M) g₀ s B x m := by
  rw [unitModel, unitModel, unitModel]
  rw [show (A - B).toSection x = A.toSection x - B.toSection x from by
    rw [SmoothCcTensor.toSection_sub]; rfl]
  rw [show ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from
      A.toSection x - B.toSection x) (unitTensor (I := I) (M := M) x)) =
      (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from A.toSection x)
          (unitTensor (I := I) (M := M) x) -
        (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from B.toSection x)
          (unitTensor (I := I) (M := M) x) from rfl]
  rw [Tensor0SSpace.toModel_sub, ContinuousMultilinearMap.sub_apply]

-- The pointwise metric/connection normalization is expensive to elaborate.
omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
/-- The affine-background form of `lc0Kappa`: the self-background Koszul term
is separated from one fixed lowered connection difference and one perturbative
pairing with that fixed difference. -/
theorem lc0Kappa_eq_self_sub_connDiffLowered_add_pbLow
    (g₀ g₁ gB : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
    (htie : ∀ (y : M) (v w : TangentSpace I y),
      g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w) :
    lc0Kappa (I := I) (M := M) g₀ g₁ gB =
      lc0Kappa (I := I) (M := M) g₀ g₁ g₀ -
        connDiffLoweredCc (I := I) g₀ gB +
        lc0PbLow (I := I) (M := M) g₀ P g₀ gB := by
  apply smoothCcTensor_ext_of_unitModel (I := I) (M := M) g₀
  intro x
  apply ContinuousMultilinearMap.ext
  intro m
  rw [lc0b_unitModel_add (I := I) (M := M) g₀ 3 _ _ x m,
    lc0b_unitModel_sub (I := I) (M := M) g₀ 3 _ _ x m]
  rw [lc0Kappa_unitModel_apply (I := I) (M := M) g₀ g₁ gB x m,
    lc0Kappa_unitModel_apply (I := I) (M := M) g₀ g₁ g₀ x m,
    lc0PbLow_unitModel_apply (I := I) (M := M) g₀ P g₀ gB x m]
  rw [lc0b_connDiffLowered_unitModel_apply (I := I) (M := M) g₀ gB x m]
  have hanti : PDE.DeTurck.connDiff (I := I) gB g₀ x (m 0) (m 1) =
      -PDE.DeTurck.connDiff (I := I) g₀ gB x (m 0) (m 1) := by
    have h := PDE.DeTurck.connDiff_cocycle
      (I := I) gB g₀ g₀ x (m 0) (m 1)
    rw [PDE.DeTurck.connDiff_self] at h
    exact eq_neg_of_add_eq_zero_left (by simpa only [add_comm] using h.symm)
  rw [hanti, map_neg, ContinuousLinearMap.neg_apply, sub_neg_eq_add]
  rw [PDE.DeTurck.connDiff_cocycle (I := I) g₀ g₁ gB x (m 0) (m 1)]
  rw [map_add (g₁.inner x), ContinuousLinearMap.add_apply]
  rw [htie x (PDE.DeTurck.connDiff (I := I) g₀ gB x (m 0) (m 1)) (m 2)]
  ring

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
/-- Difference form of the affine-background `lc0Kappa` identity. -/
theorem lc0Kappa_self_sub_eq_connDiffLowered_sub_pbLow
    (g₀ g₁ gB : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
    (htie : ∀ (y : M) (v w : TangentSpace I y),
      g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w) :
    lc0Kappa (I := I) (M := M) g₀ g₁ g₀ -
        lc0Kappa (I := I) (M := M) g₀ g₁ gB =
      connDiffLoweredCc (I := I) g₀ gB -
        lc0PbLow (I := I) (M := M) g₀ P g₀ gB := by
  rw [lc0Kappa_eq_self_sub_connDiffLowered_add_pbLow
    (I := I) (M := M) g₀ g₁ gB P htie]
  abel

def lc0FixCd (g₀ gB : SmoothRiemannianMetric I M) : SmoothCcTensor g₀ 1 2 where
  toSection := (connDiffSection (I := I) g₀ gB).toSection
  hasCompactSupport := (connDiffSection (I := I) g₀ gB).hasCompactSupport

omit [NeZero (Module.finrank ℝ E)] in
private lemma lc0b_connDiffSection_eq_raise_lowered (g₀ g₁ : SmoothRiemannianMetric I M) :
    connDiffSection (I := I) g₁ g₀ =
      cometricRaiseSlot0Field (I := I) (M := M) g₀ 1
        (domDomCongrSection (I := I) g₀ (finRotate 3) (connDiffLoweredCc (I := I) g₀ g₁)) := by
  apply Integral.L2.SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rw [connDiffSection_toSection, cometricRaiseSlot0Field_toSection]
  apply tensorRSSpace_ext 1 2 x
  intro om
  apply ContinuousMultilinearMap.ext
  intro YZ
  set u : TangentSpace I x := inverseMetricSharpFib (I := I) g₀ x om with hu
  set D : Tensor0SSpace 3 I x :=
    (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 3 I x from
      (domDomCongrSection (I := I) g₀ (finRotate 3)
        (connDiffLoweredCc (I := I) g₀ g₁)).toSection x)
      (unitTensor (I := I) (M := M) x) with hDdef
  have hLHS : (show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 2 I x from
        connDiffFib (I := I) g₁ g₀ x) om YZ =
      g₀.inner x u (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (YZ 0) (YZ 1)) := by
    rw [connDiffFib_apply_eval]
    rw [show om (fun _ : Fin 1 => PDE.DeTurck.connDiff (I := I) g₁ g₀ x (YZ 0) (YZ 1)) =
        cotangentToDual (I := I) (x := x) om
          (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (YZ 0) (YZ 1)) from
      (cotangentToDual_apply (I := I) om _).symm]
    rw [show cotangentToDual (I := I) (x := x) om
          (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (YZ 0) (YZ 1)) =
        cotangentToDualLinear (I := I) (x := x) om
          (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (YZ 0) (YZ 1)) from rfl]
    rw [← inverseMetricSharpFib_inner (I := I) g₀ x om
      (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (YZ 0) (YZ 1)), ← hu]
  have hRHS : (show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 2 I x from
        cometricRaiseSlot0Fib (I := I) g₀ 1 x D) om YZ =
      Tensor0SSpace.toModel D (Fin.cons (show E from u) (fun k => (show E from YZ k))) := by
    rw [cometricRaiseSlot0Fib_clm_apply (I := I) g₀ 1 x D om]
    rw [show (Tensor0SBundle.interior_product (𝕜 := ℝ) (I := I) (1 + 1) x
            (inverseMetricSharpFib (I := I) g₀ x om) D YZ : ℝ) =
        Tensor0SSpace.toModel
          (Tensor0SBundle.interior_product (𝕜 := ℝ) (I := I) (1 + 1) x
            (inverseMetricSharpFib (I := I) g₀ x om) D) YZ from rfl]
    rw [lc0b_interior_product_toModel_eval (I := I) (M := M) (1 + 1) x
      (inverseMetricSharpFib (I := I) g₀ x om) D YZ, ← hu]
  rw [hLHS, hRHS]
  have hum : unitModel (I := I) (M := M) g₀ 3
      (domDomCongrSection (I := I) g₀ (finRotate 3) (connDiffLoweredCc (I := I) g₀ g₁)) x =
      Tensor0SSpace.toModel D := rfl
  rw [show Tensor0SSpace.toModel D (Fin.cons (show E from u) (fun k => (show E from YZ k))) =
        unitModel (I := I) (M := M) g₀ 3
          (domDomCongrSection (I := I) g₀ (finRotate 3) (connDiffLoweredCc (I := I) g₀ g₁)) x
          ![u, YZ 0, YZ 1] from by
    rw [hum]; congr 1; funext k; fin_cases k <;> rfl]
  rw [domDomCongrSection_unitModel, ContinuousMultilinearMap.domDomCongr_apply]
  rw [show (fun i => (![u, YZ 0, YZ 1] : Fin 3 → TangentSpace I x) ((finRotate 3) i)) =
        ![YZ 0, YZ 1, u] from by
    funext i; fin_cases i <;> simp [finRotate_succ_apply]]
  rw [lc0b_connDiffLowered_unitModel_apply (I := I) (M := M) g₀ g₁ x ![YZ 0, YZ 1, u]]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons]
  rw [g₀.symm x u (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (YZ 0) (YZ 1))]

omit [NeZero (Module.finrank ℝ E)] in
lemma lc0b_rfns_icg_lowered_eq_connDiff (g₀ g₁ : SmoothRiemannianMetric I M)
    (n : ℕ) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + n) x
        ((iteratedCovGrad (I := I) g₀ 0 3 n (connDiffLoweredCc (I := I) g₀ g₁)).toSection x) =
      riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + n) x
        ((iteratedCovGrad (I := I) g₀ 1 2 n (connDiffSection (I := I) g₁ g₀)).toSection x) := by
  calc riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + n) x
        ((iteratedCovGrad (I := I) g₀ 0 3 n (connDiffLoweredCc (I := I) g₀ g₁)).toSection x)
      = riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + n) x
          ((iteratedCovGrad (I := I) g₀ 0 3 n
            (domDomCongrSection (I := I) g₀ (finRotate 3)
              (connDiffLoweredCc (I := I) g₀ g₁))).toSection x) :=
        (riemannianFiberNormSq_iteratedCovGrad_domDomCongrSection (I := I) (M := M) g₀
          (finRotate 3) (connDiffLoweredCc (I := I) g₀ g₁) n x).symm
    _ = riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + n) x
          ((iteratedCovGrad (I := I) g₀ 1 2 n
            (cometricRaiseSlot0Field (I := I) (M := M) g₀ 1
              (domDomCongrSection (I := I) g₀ (finRotate 3)
                (connDiffLoweredCc (I := I) g₀ g₁)))).toSection x) :=
        (riemannianFiberNormSq_iteratedCovGrad_cometricRaiseSlot0Field_eq (I := I) (M := M) g₀ 1
          (domDomCongrSection (I := I) g₀ (finRotate 3)
            (connDiffLoweredCc (I := I) g₀ g₁)) n x).symm
    _ = riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + n) x
          ((iteratedCovGrad (I := I) g₀ 1 2 n (connDiffSection (I := I) g₁ g₀)).toSection x) := by
        rw [lc0b_connDiffSection_eq_raise_lowered (I := I) (M := M) g₀ g₁]

omit [NeZero (Module.finrank ℝ E)] in
lemma lc0b_normSq_icg_lowered_eq (g₀ g₁ : SmoothRiemannianMetric I M) (n : ℕ) :
    ‖iteratedCovGrad (I := I) g₀ 0 3 n (connDiffLoweredCc (I := I) g₀ g₁)‖ ^ 2 =
      ‖iteratedCovGrad (I := I) g₀ 1 2 n (connDiffSection (I := I) g₁ g₀)‖ ^ 2 := by
  rw [lc0b_normSq_eq_integral, lc0b_normSq_eq_integral]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  exact lc0b_rfns_icg_lowered_eq_connDiff (I := I) (M := M) g₀ g₁ n x

omit [NeZero (Module.finrank ℝ E)] in
private lemma lc0b_pbLow_raise_eq (g₀ : SmoothRiemannianMetric I M)
    (P : SmoothCcTensor g₀ 0 2) (gA gB : SmoothRiemannianMetric I M)
    (Ψc : SmoothCcTensor g₀ 1 2)
    (hΨc : ∀ x : M, Ψc.toSection x = connDiffFib (I := I) gA gB x) :
    cometricRaiseSlot0Field (I := I) (M := M) g₀ 1
        (domDomCongrSection (I := I) g₀ (finRotate 3)
          (lc0PbLow (I := I) (M := M) g₀ P gA gB)) =
      ccOperatorFieldComp (I := I) (M := M) g₀ 1 1 2 Ψc
        (cometricRaiseSlot0Field (I := I) (M := M) g₀ 0
          (ccTensor02Symm (I := I) (M := M) g₀ P)) := by
  apply Integral.L2.SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rw [cometricRaiseSlot0Field_toSection, appCcRS_toSection]
  apply tensorRSSpace_ext 1 2 x
  intro om
  apply ContinuousMultilinearMap.ext
  intro YZ
  set u : TangentSpace I x := inverseMetricSharpFib (I := I) g₀ x om with hu
  set D : Tensor0SSpace 3 I x :=
    (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 3 I x from
      (domDomCongrSection (I := I) g₀ (finRotate 3)
        (lc0PbLow (I := I) (M := M) g₀ P gA gB)).toSection x)
      (unitTensor (I := I) (M := M) x) with hDdef
  have hLHS : (show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 2 I x from
        cometricRaiseSlot0Fib (I := I) g₀ 1 x D) om YZ =
      Tensor0SSpace.toModel D (Fin.cons (show E from u) (fun k => (show E from YZ k))) := by
    rw [cometricRaiseSlot0Fib_clm_apply (I := I) g₀ 1 x D om]
    rw [show (Tensor0SBundle.interior_product (𝕜 := ℝ) (I := I) (1 + 1) x
            (inverseMetricSharpFib (I := I) g₀ x om) D YZ : ℝ) =
        Tensor0SSpace.toModel
          (Tensor0SBundle.interior_product (𝕜 := ℝ) (I := I) (1 + 1) x
            (inverseMetricSharpFib (I := I) g₀ x om) D) YZ from rfl]
    rw [lc0b_interior_product_toModel_eval (I := I) (M := M) (1 + 1) x
      (inverseMetricSharpFib (I := I) g₀ x om) D YZ, ← hu]
  have hLHSval : Tensor0SSpace.toModel D
      (Fin.cons (show E from u) (fun k => (show E from YZ k))) =
      ccTensorBilinSymm (I := I) g₀ P x
        (PDE.DeTurck.connDiff (I := I) gA gB x (YZ 0) (YZ 1)) u := by
    have hum : unitModel (I := I) (M := M) g₀ 3
        (domDomCongrSection (I := I) g₀ (finRotate 3)
          (lc0PbLow (I := I) (M := M) g₀ P gA gB)) x =
        Tensor0SSpace.toModel D := rfl
    rw [show Tensor0SSpace.toModel D
          (Fin.cons (show E from u) (fun k => (show E from YZ k))) =
        unitModel (I := I) (M := M) g₀ 3
          (domDomCongrSection (I := I) g₀ (finRotate 3)
            (lc0PbLow (I := I) (M := M) g₀ P gA gB)) x ![u, YZ 0, YZ 1] from by
      rw [hum]; congr 1; funext k; fin_cases k <;> rfl]
    rw [domDomCongrSection_unitModel, ContinuousMultilinearMap.domDomCongr_apply]
    rw [show (fun i => (![u, YZ 0, YZ 1] : Fin 3 → TangentSpace I x) ((finRotate 3) i)) =
          ![YZ 0, YZ 1, u] from by
      funext i; fin_cases i <;> simp [finRotate_succ_apply]]
    rw [lc0PbLow_unitModel_apply (I := I) (M := M) g₀ P gA gB x ![YZ 0, YZ 1, u]]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons]
  have hRHS : ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 2 I x from
        Ψc.toSection x).comp
        (show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 1 I x from
          (cometricRaiseSlot0Field (I := I) (M := M) g₀ 0
            (ccTensor02Symm (I := I) (M := M) g₀ P)).toSection x)) om YZ =
      ccTensorBilinSymm (I := I) g₀ P x
        (PDE.DeTurck.connDiff (I := I) gA gB x (YZ 0) (YZ 1)) u := by
    rw [ContinuousLinearMap.comp_apply]
    set om' : Tensor0SSpace 1 I x :=
      (show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 1 I x from
        (cometricRaiseSlot0Field (I := I) (M := M) g₀ 0
          (ccTensor02Symm (I := I) (M := M) g₀ P)).toSection x) om with hom'
    rw [hΨc x]
    rw [connDiffFib_apply_eval (I := I) gA gB x om' YZ]
    rw [show om' (fun _ : Fin 1 =>
        PDE.DeTurck.connDiff (I := I) gA gB x (YZ 0) (YZ 1)) =
        Tensor0SSpace.toModel om' (fun _ : Fin 1 => (show E from
          PDE.DeTurck.connDiff (I := I) gA gB x (YZ 0) (YZ 1))) from rfl]
    rw [hom']
    rw [show ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 1 I x from
        (cometricRaiseSlot0Field (I := I) (M := M) g₀ 0
          (ccTensor02Symm (I := I) (M := M) g₀ P)).toSection x) om) =
        cometricRaiseSlot0Fib (I := I) g₀ 0 x
          ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from
            (ccTensor02Symm (I := I) (M := M) g₀ P).toSection x)
            (unitTensor (I := I) (M := M) x)) om from by
      rw [cometricRaiseSlot0Field_toSection]]
    rw [cometricRaiseSlot0Fib_clm_apply (I := I) g₀ 0 x _ om]
    rw [show Tensor0SSpace.toModel
        (Tensor0SBundle.interior_product (𝕜 := ℝ) (I := I) (0 + 1) x
          (inverseMetricSharpFib (I := I) g₀ x om)
          ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from
            (ccTensor02Symm (I := I) (M := M) g₀ P).toSection x)
            (unitTensor (I := I) (M := M) x)))
        (fun _ : Fin 1 => (show E from
          PDE.DeTurck.connDiff (I := I) gA gB x (YZ 0) (YZ 1))) =
        Tensor0SSpace.toModel
          ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from
            (ccTensor02Symm (I := I) (M := M) g₀ P).toSection x)
            (unitTensor (I := I) (M := M) x))
          (Fin.cons (show E from u)
            (fun _ : Fin 1 => (show E from
              PDE.DeTurck.connDiff (I := I) gA gB x (YZ 0) (YZ 1)))) from by
      rw [lc0b_interior_product_toModel_eval (I := I) (M := M) (0 + 1) x
        (inverseMetricSharpFib (I := I) g₀ x om) _ _, ← hu]]
    rw [show Tensor0SSpace.toModel
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from
          (ccTensor02Symm (I := I) (M := M) g₀ P).toSection x)
          (unitTensor (I := I) (M := M) x))
        (Fin.cons (show E from u)
          (fun _ : Fin 1 => (show E from
            PDE.DeTurck.connDiff (I := I) gA gB x (YZ 0) (YZ 1)))) =
        unitModel (I := I) (M := M) g₀ 2 (ccTensor02Symm (I := I) (M := M) g₀ P) x
          ![u, PDE.DeTurck.connDiff (I := I) gA gB x (YZ 0) (YZ 1)] from by
      rw [unitModel]
      congr 1
      funext k
      fin_cases k <;> rfl]
    rw [unitModel_eq_ccTensorBilin_local (I := I) (M := M) g₀
      (ccTensor02Symm (I := I) (M := M) g₀ P) x u
      (PDE.DeTurck.connDiff (I := I) gA gB x (YZ 0) (YZ 1))]
    rw [ccTensorBilin_symmS (I := I) (M := M) g₀ P x u
      (PDE.DeTurck.connDiff (I := I) gA gB x (YZ 0) (YZ 1))]
    exact ccTensorBilinSymm_symm (I := I) g₀ P x u
      (PDE.DeTurck.connDiff (I := I) gA gB x (YZ 0) (YZ 1))
  rw [hLHS, hLHSval]
  exact hRHS.symm

omit [NeZero (Module.finrank ℝ E)] in
lemma lc0b_rfns_icg_pbLow_eq (g₀ : SmoothRiemannianMetric I M)
    (P : SmoothCcTensor g₀ 0 2) (gA gB : SmoothRiemannianMetric I M)
    (Ψc : SmoothCcTensor g₀ 1 2)
    (hΨc : ∀ x : M, Ψc.toSection x = connDiffFib (I := I) gA gB x) (n : ℕ) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + n) x
        ((iteratedCovGrad (I := I) g₀ 0 3 n
          (lc0PbLow (I := I) (M := M) g₀ P gA gB)).toSection x) =
      riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + n) x
        ((iteratedCovGrad (I := I) g₀ 1 2 n
          (ccOperatorFieldComp (I := I) (M := M) g₀ 1 1 2 Ψc
            (cometricRaiseSlot0Field (I := I) (M := M) g₀ 0
              (ccTensor02Symm (I := I) (M := M) g₀ P)))).toSection x) := by
  calc riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + n) x
        ((iteratedCovGrad (I := I) g₀ 0 3 n
          (lc0PbLow (I := I) (M := M) g₀ P gA gB)).toSection x)
      = riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + n) x
          ((iteratedCovGrad (I := I) g₀ 0 3 n
            (domDomCongrSection (I := I) g₀ (finRotate 3)
              (lc0PbLow (I := I) (M := M) g₀ P gA gB))).toSection x) :=
        (riemannianFiberNormSq_iteratedCovGrad_domDomCongrSection (I := I) (M := M) g₀
          (finRotate 3) (lc0PbLow (I := I) (M := M) g₀ P gA gB) n x).symm
    _ = riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + n) x
          ((iteratedCovGrad (I := I) g₀ 1 2 n
            (cometricRaiseSlot0Field (I := I) (M := M) g₀ 1
              (domDomCongrSection (I := I) g₀ (finRotate 3)
                (lc0PbLow (I := I) (M := M) g₀ P gA gB)))).toSection x) :=
        (riemannianFiberNormSq_iteratedCovGrad_cometricRaiseSlot0Field_eq (I := I) (M := M) g₀ 1
          (domDomCongrSection (I := I) g₀ (finRotate 3)
            (lc0PbLow (I := I) (M := M) g₀ P gA gB)) n x).symm
    _ = riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + n) x
          ((iteratedCovGrad (I := I) g₀ 1 2 n
            (ccOperatorFieldComp (I := I) (M := M) g₀ 1 1 2 Ψc
              (cometricRaiseSlot0Field (I := I) (M := M) g₀ 0
                (ccTensor02Symm (I := I) (M := M) g₀ P)))).toSection x) := by
        rw [lc0b_pbLow_raise_eq (I := I) (M := M) g₀ P gA gB Ψc hΨc]

omit [NeZero (Module.finrank ℝ E)] in
lemma lc0b_normSq_icg_pbLow_eq (g₀ : SmoothRiemannianMetric I M)
    (P : SmoothCcTensor g₀ 0 2) (gA gB : SmoothRiemannianMetric I M)
    (Ψc : SmoothCcTensor g₀ 1 2)
    (hΨc : ∀ x : M, Ψc.toSection x = connDiffFib (I := I) gA gB x) (n : ℕ) :
    ‖iteratedCovGrad (I := I) g₀ 0 3 n (lc0PbLow (I := I) (M := M) g₀ P gA gB)‖ ^ 2 =
      ‖iteratedCovGrad (I := I) g₀ 1 2 n
        (ccOperatorFieldComp (I := I) (M := M) g₀ 1 1 2 Ψc
          (cometricRaiseSlot0Field (I := I) (M := M) g₀ 0
            (ccTensor02Symm (I := I) (M := M) g₀ P)))‖ ^ 2 := by
  rw [lc0b_normSq_eq_integral, lc0b_normSq_eq_integral]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  exact lc0b_rfns_icg_pbLow_eq (I := I) (M := M) g₀ P gA gB Ψc hΨc n x

end LieCorr0BoundsB

end LieCorr0BoundsAll

end DifferentialGeometry.Analysis.Spectral

end
