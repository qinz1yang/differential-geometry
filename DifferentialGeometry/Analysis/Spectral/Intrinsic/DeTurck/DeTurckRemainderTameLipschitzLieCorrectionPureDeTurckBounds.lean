import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.DeTurckRemainderTameLipschitzLieCorrectionMetricFeedBounds
open DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Analysis.Elliptic
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection


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

section LieCorr0BoundsD

open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Sobolev.TensorHilbert (metricComparisonEndo gInvRaisedEndo_apply
  g0FlatCLM cotangentToDual_g0FlatCLM)
open DifferentialGeometry.Analysis.Spectral.DeTurck (cometricDoubleTraceField
  cometricDoubleTraceField_covGrad_eq_zero modelDoubleTrace_apply cometricLmodel
  cometric_dualTrace_eq_orthoFrame_diag)

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem lc0b_fixedField_rfns_jet (g₀ : SmoothRiemannianMetric I M)
    (r s : ℕ) (F : SmoothCcTensor g₀ r s) :
    ∃ c : ℕ → ℝ, (∀ j, 0 ≤ c j) ∧ ∀ (j : ℕ) (x : M),
      riemannianFiberNormSq (I := I) (M := M) g₀ r (s + j) x
        ((iteratedCovGrad (I := I) g₀ r s j F).toSection x) ≤ c j := by
  have h : ∀ j : ℕ, ∃ c : ℝ, 0 ≤ c ∧ ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g₀ r (s + j) x
        ((iteratedCovGrad (I := I) g₀ r s j F).toSection x) ≤ c := fun j =>
    exists_bound_riemannianFiberNormSq_smoothCcTensor (I := I) (M := M) g₀ r (s + j)
      (iteratedCovGrad (I := I) g₀ r s j F)
  choose c hc0 hc using h
  exact ⟨c, hc0, fun j x => hc j x⟩

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] in
theorem lc0b_normSq_le_scaled_of_pointwise [SigmaCompactSpace M] (g₀ : SmoothRiemannianMetric I M)
    (r₁ s₁ r₂ s₂ : ℕ) (X : SmoothCcTensor g₀ r₁ s₁) (Y : SmoothCcTensor g₀ r₂ s₂)
    (c : ℝ) (_hc : 0 ≤ c)
    (hpt : ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ r₁ s₁ x (X.toSection x) ≤
      c * riemannianFiberNormSq (I := I) (M := M) g₀ r₂ s₂ x (Y.toSection x)) :
    ‖X‖ ^ 2 ≤ c * ‖Y‖ ^ 2 := by
  rw [lc0b_normSq_eq_integral, lc0b_normSq_eq_integral]
  rw [← MeasureTheory.integral_const_mul]
  refine MeasureTheory.integral_mono ?_ ?_ hpt
  · exact integrable_riemannianFiberNormSq_toSection (I := I) (M := M) g₀ r₁ s₁ X
  · exact (integrable_riemannianFiberNormSq_toSection (I := I) (M := M) g₀ r₂ s₂ Y).const_mul c

private lemma lc0b_icg_succ_cometricDT_zero (g₀ : SmoothRiemannianMetric I M) (s m : ℕ) :
    iteratedCovGrad (I := I) g₀ (s + 2) s (m + 1)
      (cometricDoubleTraceField (I := I) g₀ s) = 0 := by
  induction m with
  | zero =>
      rw [iteratedCovGrad_succ, iteratedCovGrad_zero]
      exact cometricDoubleTraceField_covGrad_eq_zero (I := I) g₀ s
  | succ m' ih =>
      rw [iteratedCovGrad_succ, ih, lc0b_covGrad_zero]

omit [NeZero (Module.finrank ℝ E)] [TopologicalSpace M] [CompactSpace M] [T2Space M]
    in
lemma lc0b_toModel_cons_sum_smul (_x : M) {n : ℕ}
    (Zm : Tensor0SModel (n + 1) ℝ E) (d : ℕ) (t : Fin d → ℝ)
    (u : Fin d → E) (rest : Fin n → E) :
    Zm (Fin.cons (∑ c, t c • u c) rest) =
      ∑ c, t c * Zm (Fin.cons (u c) rest) := by
  classical
  have h1 : ∀ v : E, (Fin.cons v rest : Fin (n + 1) → E) =
      Function.update (Fin.cons (0 : E) rest) 0 v := by
    intro v
    rw [Fin.update_cons_zero]
  have hgen : ∀ ss : Finset (Fin d),
      Zm (Function.update (Fin.cons (0 : E) rest) 0 (∑ c ∈ ss, t c • u c)) =
        ∑ c ∈ ss, t c * Zm (Function.update (Fin.cons (0 : E) rest) 0 (u c)) := by
    intro ss
    induction ss using Finset.induction_on with
    | empty =>
        rw [Finset.sum_empty, Finset.sum_empty]
        rw [show (0 : E) = ((0 : ℝ) • (0 : E)) from (zero_smul ℝ (0 : E)).symm]
        rw [ContinuousMultilinearMap.map_update_smul]
        rw [zero_smul]
    | @insert a ss ha ih =>
        rw [Finset.sum_insert ha, Finset.sum_insert ha]
        rw [ContinuousMultilinearMap.map_update_add]
        rw [ih]
        congr 1
        rw [ContinuousMultilinearMap.map_update_smul]
        rw [smul_eq_mul]
  have h2 := hgen Finset.univ
  rw [h1, h2]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [← h1 (u c)]

omit [NeZero (Module.finrank ℝ E)] [TopologicalSpace M] [CompactSpace M] [T2Space M]
    in
private lemma lc0b_toModel_cons_cons_sum_smul (_x : M) {n : ℕ}
    (Zm : Tensor0SModel (n + 2) ℝ E) (aa : E) (d : ℕ) (t : Fin d → ℝ)
    (u : Fin d → E) (rest : Fin n → E) :
    Zm (Fin.cons aa (Fin.cons (∑ c, t c • u c) rest)) =
      ∑ c, t c * Zm (Fin.cons aa (Fin.cons (u c) rest)) := by
  classical
  have h1 : ∀ v : E, (Fin.cons aa (Fin.cons v rest) : Fin (n + 2) → E) =
      Function.update (Fin.cons aa (Fin.cons (0 : E) rest)) 1 v := by
    intro v
    rw [show (1 : Fin (n + 2)) = Fin.succ 0 from rfl]
    rw [← Fin.cons_update]
    rw [Fin.update_cons_zero]
  have hgen : ∀ ss : Finset (Fin d),
      Zm (Function.update (Fin.cons aa (Fin.cons (0 : E) rest)) 1 (∑ c ∈ ss, t c • u c)) =
        ∑ c ∈ ss, t c * Zm (Function.update (Fin.cons aa (Fin.cons (0 : E) rest)) 1 (u c)) := by
    intro ss
    induction ss using Finset.induction_on with
    | empty =>
        rw [Finset.sum_empty, Finset.sum_empty]
        rw [show (0 : E) = ((0 : ℝ) • (0 : E)) from (zero_smul ℝ (0 : E)).symm]
        rw [ContinuousMultilinearMap.map_update_smul]
        rw [zero_smul]
    | @insert a ss ha ih =>
        rw [Finset.sum_insert ha, Finset.sum_insert ha]
        rw [ContinuousMultilinearMap.map_update_add]
        rw [ih]
        congr 1
        rw [ContinuousMultilinearMap.map_update_smul]
        rw [smul_eq_mul]
  have h2 := hgen Finset.univ
  rw [h1, h2]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [← h1 (u c)]

omit [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M]
    in
lemma lc0b_orthoFrame_center_repr (g : SmoothRiemannianMetric I M) (x : M)
    (v : TangentSpace I x) :
    v = ∑ i : Fin (Module.finrank ℝ E),
      g.inner x (smoothOrthoFrame (I := I) g x i x) v • smoothOrthoFrame (I := I) g x i x := by
  classical
  haveI : FiniteDimensional ℝ (TangentSpace I x) := inferInstanceAs (FiniteDimensional ℝ E)
  haveI : Nonempty (Fin (Module.finrank ℝ E)) :=
    ⟨⟨0, Nat.pos_of_ne_zero (NeZero.ne (Module.finrank ℝ E))⟩⟩
  set B : Fin (Module.finrank ℝ E) → TangentSpace I x :=
    fun i => smoothOrthoFrame (I := I) g x i x with hB_def
  have horth : ∀ i j, g.inner x (B i) (B j) = if i = j then (1 : ℝ) else 0 :=
    fun i j => smoothOrthoFrame_orthonormal_at_center (I := I) g x i j
  have hlin : LinearIndependent ℝ B := by
    rw [Fintype.linearIndependent_iff]
    intro c hc j
    have hpair : g.inner x (∑ i, c i • B i) (B j) = 0 := by
      rw [hc]
      simp
    rw [map_sum, ContinuousLinearMap.sum_apply] at hpair
    have hsimp : ∀ i, g.inner x (c i • B i) (B j) = c i * (if i = j then (1 : ℝ) else 0) := by
      intro i
      rw [map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul, horth i j]
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
  have hrepr : ∀ (w : TangentSpace I x) (j : Fin (Module.finrank ℝ E)),
      bB.repr w j = g.inner x (B j) w := by
    intro w j
    conv_rhs => rw [← bB.sum_repr w]
    rw [map_sum]
    have hsimp : ∀ i, g.inner x (B j) (bB.repr w i • bB i) =
        bB.repr w i * (if j = i then (1 : ℝ) else 0) := by
      intro i
      rw [map_smul, smul_eq_mul, hbB_coe i, horth j i]
    rw [Finset.sum_congr rfl (fun i _ => hsimp i)]
    simp
  conv_lhs => rw [← bB.sum_repr v]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hrepr v i, hbB_coe i]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
    [T2Space M] in
private lemma lc0b_g1_inner_gInvRaisedEndo_left (g₀ g₁ : SmoothRiemannianMetric I M)
    (x : M) (v w : TangentSpace I x) :
    g₁.inner x (metricComparisonEndo (I := I) g₀ g₁ x v) w = g₀.inner x v w := by
  rw [gInvRaisedEndo_apply]
  rw [inverseMetricSharpFib_inner (I := I) g₁ x (g0FlatCLM (I := I) g₀ x v) w]
  rw [cotangentToDualLinear_apply]
  exact cotangentToDual_g0FlatCLM (I := I) g₀ x v w

def lc0PureDT [SigmaCompactSpace M] (g₀ g₁ : SmoothRiemannianMetric I M) (s : ℕ) :
    SmoothCcTensor g₀ (s + 2) s where
  toSection :=
    { toFun := fun x : M =>
        (show TensorRSSpace (s + 2) s I x from cometricDoubleTraceFib (I := I) g₁ s x)
      contMDiff_toFun := cometricDoubleTraceFib_contMDiff (I := I) g₁ s }
  hasCompactSupport := HasCompactSupport.of_compactSpace _

omit [BoundarylessManifold I M] in
lemma lc0PureDT_eq_trace_fullRaised (g₀ g₁ : SmoothRiemannianMetric I M)
    (s : ℕ) :
    lc0PureDT (I := I) (M := M) g₀ g₁ s =
      ccOperatorFieldComp (I := I) (M := M) g₀ (s + 2) (s + 2) s
        (cometricDoubleTraceField (I := I) g₀ s)
        (endoSlotZeroCcTensor (I := I) (M := M) g₀ (s + 1)
          (fullRaisedEndoField (I := I) (M := M) g₀ g₁)) := by
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
        (lc0PureDT (I := I) (M := M) g₀ g₁ s).toSection x) Z) mm =
      ∑ c : Fin (Module.finrank ℝ E),
        Tensor0SSpace.toModel Z
          (Fin.cons ((smoothOrthoFrame (I := I) g₁ x c x : TangentSpace I x) : E)
            (Fin.cons ((smoothOrthoFrame (I := I) g₁ x c x : TangentSpace I x) : E) mm)) := by
    rw [show ((show Tensor0SSpace (s + 2) I x →L[ℝ] Tensor0SSpace s I x from
        (lc0PureDT (I := I) (M := M) g₀ g₁ s).toSection x) Z) =
        cometricDoubleTraceFib (I := I) g₁ s x Z from rfl]
    rw [cometricDoubleTraceFib_toModel (I := I) g₁ s x Z]
    rw [modelDoubleTrace_apply (E := E) s (cometricLmodel (I := I) g₁ x)]
    rw [cometric_dualTrace_eq_orthoFrame_diag (I := I) g₁ x
      (mem_smoothOrthoFrameNbhd_self (I := I) (M := M) x) (Tensor0SSpace.toModel Z) mm]
  rw [hLHS]
  have hRHS : Tensor0SSpace.toModel
      ((show Tensor0SSpace (s + 2) I x →L[ℝ] Tensor0SSpace s I x from
        (ccOperatorFieldComp (I := I) (M := M) g₀ (s + 2) (s + 2) s
          (cometricDoubleTraceField (I := I) g₀ s)
          (endoSlotZeroCcTensor (I := I) (M := M) g₀ (s + 1)
            (fullRaisedEndoField (I := I) (M := M) g₀ g₁))).toSection x) Z) mm =
      ∑ a : Fin (Module.finrank ℝ E),
        Tensor0SSpace.toModel Z
          (Fin.cons (show E from metricComparisonEndo (I := I) g₀ g₁ x
              (smoothOrthoFrame (I := I) g₀ x a x))
            (Fin.cons ((smoothOrthoFrame (I := I) g₀ x a x : TangentSpace I x) : E) mm)) := by
    rw [show ((show Tensor0SSpace (s + 2) I x →L[ℝ] Tensor0SSpace s I x from
        (ccOperatorFieldComp (I := I) (M := M) g₀ (s + 2) (s + 2) s
          (cometricDoubleTraceField (I := I) g₀ s)
          (endoSlotZeroCcTensor (I := I) (M := M) g₀ (s + 1)
            (fullRaisedEndoField (I := I) (M := M) g₀ g₁))).toSection x) Z) =
        cometricDoubleTraceFib (I := I) g₀ s x
          (slotInsertEndoFib (I := I) (M := M) (s + 2) 0 x
            (fullRaisedEndoField (I := I) (M := M) g₀ g₁ x) Z) from by
      rw [appCcRS_toSection]
      rfl]
    rw [cometricDoubleTraceFib_toModel (I := I) g₀ s x]
    rw [modelDoubleTrace_apply (E := E) s (cometricLmodel (I := I) g₀ x)]
    rw [cometric_dualTrace_eq_orthoFrame_diag (I := I) g₀ x
      (mem_smoothOrthoFrameNbhd_self (I := I) (M := M) x)
      (Tensor0SSpace.toModel
        (slotInsertEndoFib (I := I) (M := M) (s + 2) 0 x
          (fullRaisedEndoField (I := I) (M := M) g₀ g₁ x) Z)) mm]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [slotInsertEndoFib_apply_eval]
    rw [Fin.update_cons_zero]
    rfl
  rw [hRHS]
  have hGrep : ∀ a : Fin (Module.finrank ℝ E),
      (show E from metricComparisonEndo (I := I) g₀ g₁ x (smoothOrthoFrame (I := I) g₀ x a x)) =
        ∑ c : Fin (Module.finrank ℝ E),
          (g₀.inner x (smoothOrthoFrame (I := I) g₀ x a x) (smoothOrthoFrame (I := I) g₁ x c x)) •
            (smoothOrthoFrame (I := I) g₁ x c x : E) := by
    intro a
    have h1 := lc0b_orthoFrame_center_repr (I := I) (M := M) g₁ x
      (metricComparisonEndo (I := I) g₀ g₁ x (smoothOrthoFrame (I := I) g₀ x a x))
    rw [show (show E from metricComparisonEndo (I := I) g₀ g₁ x
        (smoothOrthoFrame (I := I) g₀ x a x)) =
        metricComparisonEndo (I := I) g₀ g₁ x (smoothOrthoFrame (I := I) g₀ x a x) from rfl]
    conv_lhs => rw [h1]
    refine Finset.sum_congr rfl fun c _ => ?_
    congr 1
    rw [g₁.symm x (smoothOrthoFrame (I := I) g₁ x c x)
      (metricComparisonEndo (I := I) g₀ g₁ x (smoothOrthoFrame (I := I) g₀ x a x))]
    rw [lc0b_g1_inner_gInvRaisedEndo_left (I := I) (M := M) g₀ g₁ x
      (smoothOrthoFrame (I := I) g₀ x a x) (smoothOrthoFrame (I := I) g₁ x c x)]
  symm
  calc (∑ a : Fin (Module.finrank ℝ E),
        Tensor0SSpace.toModel Z
          (Fin.cons (show E from metricComparisonEndo (I := I) g₀ g₁ x
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
        exact lc0b_toModel_cons_sum_smul (E := E) x (Tensor0SSpace.toModel Z)
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
        have hsum := lc0b_toModel_cons_cons_sum_smul (E := E) x (Tensor0SSpace.toModel Z)
          ((smoothOrthoFrame (I := I) g₁ x c x : TangentSpace I x) : E)
          (Module.finrank ℝ E)
          (fun a => g₀.inner x (smoothOrthoFrame (I := I) g₀ x a x)
            (smoothOrthoFrame (I := I) g₁ x c x))
          (fun a => (smoothOrthoFrame (I := I) g₀ x a x : E)) mm
        rw [← hsum]
        congr 2
        have hrep0 := lc0b_orthoFrame_center_repr (I := I) (M := M) g₀ x
          (smoothOrthoFrame (I := I) g₁ x c x)
        rw [show (∑ a : Fin (Module.finrank ℝ E),
            g₀.inner x (smoothOrthoFrame (I := I) g₀ x a x)
              (smoothOrthoFrame (I := I) g₁ x c x) •
              (smoothOrthoFrame (I := I) g₀ x a x : E)) =
            ((∑ a : Fin (Module.finrank ℝ E),
              g₀.inner x (smoothOrthoFrame (I := I) g₀ x a x)
                (smoothOrthoFrame (I := I) g₁ x c x) •
                smoothOrthoFrame (I := I) g₀ x a x : TangentSpace I x) : E) from rfl]
        rw [← hrep0]

theorem lc0b_pureDT_feed (g₀ : SmoothRiemannianMetric I M) (s : ℕ) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ (Λ : ℝ) (F : ℕ → ℝ), 0 ≤ Λ ∧ (∀ i, 0 ≤ F i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        (_htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀) (_hδ0 : 0 ≤ δ)
        (_hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ≤ R) →
        (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ (s + 2) s x
            ((lc0PureDT (I := I) (M := M) g₀ g₁ s).toSection x) ≤ Λ) ∧
        (∀ i : ℕ, i ≤ a →
          ∑ q ∈ Finset.range (i + 1),
            ‖iteratedCovGrad (I := I) g₀ (s + 2) s q
              (lc0PureDT (I := I) (M := M) g₀ g₁ s)‖ ^ 2 ≤ F i) := by
  classical
  obtain ⟨Λsf, Fsf, hΛsf_nn, hFsf_nn, hsf⟩ :=
    lc0b_sharpFlat_feed (I := I) (M := M) g₀ a ha_super hR hδ₀
  obtain ⟨c0, hc0_nn, hc0⟩ := lc0b_fixedField_rfns_jet (I := I) (M := M) g₀ (s + 2) s
    (cometricDoubleTraceField (I := I) g₀ s)
  set fr : ℝ := (Module.finrank ℝ E : ℝ) with hfr_def
  have hfr_nn : 0 ≤ fr := Nat.cast_nonneg _
  have hfrpow_nn : 0 ≤ fr ^ (s + 1) := by positivity
  refine ⟨c0 0 * (fr ^ (s + 1) * Λsf),
    fun i => ∑ q ∈ Finset.range (i + 1),
      diagonalGridGrowthFactor (E := E) q * (c0 0 * (((q : ℝ) + 1) * (fr ^ (s + 1) * Fsf i))),
    mul_nonneg (hc0_nn 0) (mul_nonneg hfrpow_nn hΛsf_nn),
    fun i => Finset.sum_nonneg fun q _ => mul_nonneg (appCcGdiag_nonneg (E := E) q)
      (mul_nonneg (hc0_nn 0) (mul_nonneg (by positivity)
        (mul_nonneg hfrpow_nn (hFsf_nn i)))), ?_⟩
  intro g₁ P htie δ hδ_le hδ0 hδ hPball
  obtain ⟨hsfsup, hsfsum⟩ := hsf g₁ P htie hδ_le hδ0 hδ hPball
  have hid := lc0PureDT_eq_trace_fullRaised (I := I) (M := M) g₀ g₁ s
  set W : SmoothCcTensor g₀ (s + 2) (s + 2) :=
    endoSlotZeroCcTensor (I := I) (M := M) g₀ (s + 1)
      (fullRaisedEndoField (I := I) (M := M) g₀ g₁) with hW_def
  have hWpt : ∀ (l : ℕ) (x : M),
      riemannianFiberNormSq (I := I) (M := M) g₀ (s + 2) ((s + 2) + l) x
        ((iteratedCovGrad (I := I) g₀ (s + 2) (s + 2) l W).toSection x) ≤
      fr ^ (s + 1) * riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + l) x
        ((iteratedCovGrad (I := I) g₀ 1 1 l (sharpFlatEndoCc (I := I) g₀ g₁)).toSection x) := by
    intro l x
    have h := rfns_iteratedCovGrad_slotInsertEndoCc_le_endo (I := I) (M := M) g₀ (s + 1)
      (fullRaisedEndoField (I := I) (M := M) g₀ g₁) l x
    rw [← hfr_def] at h
    refine le_trans h ?_
    rw [← lc0b_sharpFlat_eq_slotInsert_fullRaised (I := I) (M := M) g₀ g₁]
  have hWsup : ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g₀ (s + 2) (s + 2) x (W.toSection x) ≤
      fr ^ (s + 1) * Λsf := by
    intro x
    have h := hWpt 0 x
    simp only [iteratedCovGrad_zero] at h
    refine le_trans h ?_
    exact mul_le_mul_of_nonneg_left (hsfsup x) hfrpow_nn
  have hWsum : ∀ i : ℕ, i ≤ a → ∀ l : ℕ, l ≤ i →
      ‖iteratedCovGrad (I := I) g₀ (s + 2) (s + 2) l W‖ ^ 2 ≤ fr ^ (s + 1) * Fsf i := by
    intro i hi l hl
    have h1 : ‖iteratedCovGrad (I := I) g₀ (s + 2) (s + 2) l W‖ ^ 2 ≤
        fr ^ (s + 1) * ‖iteratedCovGrad (I := I) g₀ 1 1 l (sharpFlatEndoCc (I := I) g₀ g₁)‖ ^ 2 :=
      lc0b_normSq_le_scaled_of_pointwise (I := I) (M := M) g₀ (s + 2) ((s + 2) + l) 1 (1 + l)
        (iteratedCovGrad (I := I) g₀ (s + 2) (s + 2) l W)
        (iteratedCovGrad (I := I) g₀ 1 1 l (sharpFlatEndoCc (I := I) g₀ g₁))
        (fr ^ (s + 1)) hfrpow_nn (fun x => hWpt l x)
    refine le_trans h1 (mul_le_mul_of_nonneg_left ?_ hfrpow_nn)
    have hsingle : ‖iteratedCovGrad (I := I) g₀ 1 1 l (sharpFlatEndoCc (I := I) g₀ g₁)‖ ^ 2 ≤
        ∑ q ∈ Finset.range (i + 1),
          ‖iteratedCovGrad (I := I) g₀ 1 1 q (sharpFlatEndoCc (I := I) g₀ g₁)‖ ^ 2 :=
      Finset.single_le_sum (f := fun q =>
        ‖iteratedCovGrad (I := I) g₀ 1 1 q (sharpFlatEndoCc (I := I) g₀ g₁)‖ ^ 2)
        (fun q _ => sq_nonneg _) (Finset.mem_range.mpr (by omega))
    exact le_trans hsingle (hsfsum i hi)
  have hpt : ∀ (q : ℕ) (x : M),
      riemannianFiberNormSq (I := I) (M := M) g₀ (s + 2) (s + q) x
        ((iteratedCovGrad (I := I) g₀ (s + 2) s q
          (lc0PureDT (I := I) (M := M) g₀ g₁ s)).toSection x) ≤
      diagonalGridGrowthFactor (E := E) q * (c0 0 *
        ∑ l ∈ Finset.range (q + 1),
          riemannianFiberNormSq (I := I) (M := M) g₀ (s + 2) ((s + 2) + l) x
            ((iteratedCovGrad (I := I) g₀ (s + 2) (s + 2) l W).toSection x)) := by
    intro q x
    rw [hid]
    refine le_trans
      (riemannianFiberNormSq_iteratedCovGrad_ccTensorCompose_diagonalProductGrid_leftFactor_le
      (I := I) (M := M) g₀ q (s + 2) (s + 2) s
      (cometricDoubleTraceField (I := I) g₀ s) W x) ?_
    refine mul_le_mul_of_nonneg_left ?_ (appCcGdiag_nonneg (E := E) q)
    have hzero : ∀ i' ∈ Finset.range (q + 1), i' ≠ 0 →
        riemannianFiberNormSq (I := I) (M := M) g₀ (s + 2) (s + i') x
            ((iteratedCovGrad (I := I) g₀ (s + 2) s i'
              (cometricDoubleTraceField (I := I) g₀ s)).toSection x) *
          ∑ l ∈ Finset.range (q + 1 - i'),
            riemannianFiberNormSq (I := I) (M := M) g₀ (s + 2) ((s + 2) + l) x
              ((iteratedCovGrad (I := I) g₀ (s + 2) (s + 2) l W).toSection x) = 0 := by
      intro i' _ hi'0
      obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hi'0
      rw [lc0b_icg_succ_cometricDT_zero (I := I) (M := M) g₀ s m]
      rw [show ((0 : SmoothCcTensor g₀ (s + 2) (s + (m + 1))).toSection x) =
          (0 : TensorRSSpace (s + 2) (s + (m + 1)) I x) from by
        rw [SmoothCcTensor.toSection_zero]; rfl]
      rw [riemannianFiberNormSq_zero (I := I) (M := M) g₀ (s + 2) (s + (m + 1)) x]
      rw [zero_mul]
    have hsum_eq : (∑ i' ∈ Finset.range (q + 1),
        riemannianFiberNormSq (I := I) (M := M) g₀ (s + 2) (s + i') x
            ((iteratedCovGrad (I := I) g₀ (s + 2) s i'
              (cometricDoubleTraceField (I := I) g₀ s)).toSection x) *
          ∑ l ∈ Finset.range (q + 1 - i'),
            riemannianFiberNormSq (I := I) (M := M) g₀ (s + 2) ((s + 2) + l) x
              ((iteratedCovGrad (I := I) g₀ (s + 2) (s + 2) l W).toSection x)) =
        riemannianFiberNormSq (I := I) (M := M) g₀ (s + 2) (s + 0) x
            ((iteratedCovGrad (I := I) g₀ (s + 2) s 0
              (cometricDoubleTraceField (I := I) g₀ s)).toSection x) *
          ∑ l ∈ Finset.range (q + 1 - 0),
            riemannianFiberNormSq (I := I) (M := M) g₀ (s + 2) ((s + 2) + l) x
              ((iteratedCovGrad (I := I) g₀ (s + 2) (s + 2) l W).toSection x) := by
      refine Finset.sum_eq_single_of_mem 0 (Finset.mem_range.mpr (by omega)) ?_
      intro i' hi' hi'0
      exact hzero i' hi' hi'0
    rw [hsum_eq]
    have hsum_nn : 0 ≤ ∑ l ∈ Finset.range (q + 1 - 0),
        riemannianFiberNormSq (I := I) (M := M) g₀ (s + 2) ((s + 2) + l) x
          ((iteratedCovGrad (I := I) g₀ (s + 2) (s + 2) l W).toSection x) :=
      Finset.sum_nonneg fun l _ =>
        riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ (s + 2) ((s + 2) + l) x _
    exact mul_le_mul_of_nonneg_right (hc0 0 x) hsum_nn
  refine ⟨?_, ?_⟩
  · intro x
    have h := hpt 0 x
    simp only [iteratedCovGrad_zero] at h
    have h2 : (∑ l ∈ Finset.range (0 + 1),
        riemannianFiberNormSq (I := I) (M := M) g₀ (s + 2) ((s + 2) + l) x
          ((iteratedCovGrad (I := I) g₀ (s + 2) (s + 2) l W).toSection x)) =
        riemannianFiberNormSq (I := I) (M := M) g₀ (s + 2) ((s + 2) + 0) x
          ((iteratedCovGrad (I := I) g₀ (s + 2) (s + 2) 0 W).toSection x) := by
      rw [Finset.sum_range_one]
    rw [h2] at h
    simp only [iteratedCovGrad_zero] at h
    have h3 : riemannianFiberNormSq (I := I) (M := M) g₀ (s + 2) (s + 2) x (W.toSection x) ≤
        fr ^ (s + 1) * Λsf := hWsup x
    have happ : diagonalGridGrowthFactor (E := E) 0 = 1 := by
      rw [diagonalGridGrowthFactor, pow_zero]
    calc riemannianFiberNormSq (I := I) (M := M) g₀ (s + 2) s x
          ((lc0PureDT (I := I) (M := M) g₀ g₁ s).toSection x)
        ≤ diagonalGridGrowthFactor (E := E) 0 * (c0 0 *
            riemannianFiberNormSq (I := I) (M := M) g₀ (s + 2) (s + 2) x (W.toSection x)) := h
      _ = c0 0 * riemannianFiberNormSq (I := I) (M := M) g₀ (s + 2) (s + 2) x
            (W.toSection x) := by rw [happ, one_mul]
      _ ≤ c0 0 * (fr ^ (s + 1) * Λsf) := mul_le_mul_of_nonneg_left h3 (hc0_nn 0)
  · intro i hi
    refine Finset.sum_le_sum fun q hq => ?_
    have hq_le : q ≤ i := by have := Finset.mem_range.mp hq; omega
    have hint : MeasureTheory.Integrable
        (fun x => diagonalGridGrowthFactor (E := E) q * (c0 0 *
          ∑ l ∈ Finset.range (q + 1),
            riemannianFiberNormSq (I := I) (M := M) g₀ (s + 2) ((s + 2) + l) x
              ((iteratedCovGrad (I := I) g₀ (s + 2) (s + 2) l W).toSection x)))
        (riemannianVolumeMeasure (I := I) (M := M) g₀) := by
      refine MeasureTheory.Integrable.const_mul ?_ _
      refine MeasureTheory.Integrable.const_mul ?_ _
      exact MeasureTheory.integrable_finset_sum (Finset.range (q + 1)) fun l _ =>
        integrable_riemannianFiberNormSq_toSection (I := I) (M := M) g₀ (s + 2) ((s + 2) + l)
          (iteratedCovGrad (I := I) g₀ (s + 2) (s + 2) l W)
    have hkey := normSq_le_integral_of_pointwise_fiberNormSq_le_rs (I := I) (M := M) g₀
      (s + 2) (s + q)
      (iteratedCovGrad (I := I) g₀ (s + 2) s q (lc0PureDT (I := I) (M := M) g₀ g₁ s))
      (fun x => diagonalGridGrowthFactor (E := E) q * (c0 0 *
        ∑ l ∈ Finset.range (q + 1),
          riemannianFiberNormSq (I := I) (M := M) g₀ (s + 2) ((s + 2) + l) x
            ((iteratedCovGrad (I := I) g₀ (s + 2) (s + 2) l W).toSection x)))
      hint (fun x => hpt q x)
    refine le_trans hkey ?_
    rw [MeasureTheory.integral_const_mul]
    refine mul_le_mul_of_nonneg_left ?_ (appCcGdiag_nonneg (E := E) q)
    rw [MeasureTheory.integral_const_mul]
    refine mul_le_mul_of_nonneg_left ?_ (hc0_nn 0)
    rw [MeasureTheory.integral_finset_sum (Finset.range (q + 1)) (fun l _ =>
      integrable_riemannianFiberNormSq_toSection (I := I) (M := M) g₀ (s + 2) ((s + 2) + l)
        (iteratedCovGrad (I := I) g₀ (s + 2) (s + 2) l W))]
    have hterm : ∀ l ∈ Finset.range (q + 1),
        (∫ x, riemannianFiberNormSq (I := I) (M := M) g₀ (s + 2) ((s + 2) + l) x
          ((iteratedCovGrad (I := I) g₀ (s + 2) (s + 2) l W).toSection x)
          ∂(riemannianVolumeMeasure (I := I) (M := M) g₀)) ≤ fr ^ (s + 1) * Fsf i := by
      intro l hl
      have hleq : (∫ x, riemannianFiberNormSq (I := I) (M := M) g₀ (s + 2) ((s + 2) + l) x
          ((iteratedCovGrad (I := I) g₀ (s + 2) (s + 2) l W).toSection x)
          ∂(riemannianVolumeMeasure (I := I) (M := M) g₀)) =
          ‖iteratedCovGrad (I := I) g₀ (s + 2) (s + 2) l W‖ ^ 2 :=
        (lc0b_normSq_eq_integral (I := I) (M := M) g₀ (s + 2) ((s + 2) + l)
          (iteratedCovGrad (I := I) g₀ (s + 2) (s + 2) l W)).symm
      rw [hleq]
      exact hWsum i hi l (le_trans (by have := Finset.mem_range.mp hl; omega) hq_le)
    calc (∑ l ∈ Finset.range (q + 1),
          ∫ x, riemannianFiberNormSq (I := I) (M := M) g₀ (s + 2) ((s + 2) + l) x
            ((iteratedCovGrad (I := I) g₀ (s + 2) (s + 2) l W).toSection x)
            ∂(riemannianVolumeMeasure (I := I) (M := M) g₀))
        ≤ ∑ l ∈ Finset.range (q + 1), fr ^ (s + 1) * Fsf i := Finset.sum_le_sum hterm
      _ = ((q : ℝ) + 1) * (fr ^ (s + 1) * Fsf i) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          push_cast
          ring

end LieCorr0BoundsD

end LieCorr0BoundsAll

end DifferentialGeometry.Analysis.Spectral

end

