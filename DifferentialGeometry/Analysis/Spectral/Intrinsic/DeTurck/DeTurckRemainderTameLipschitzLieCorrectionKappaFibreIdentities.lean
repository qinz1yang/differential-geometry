import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.DeTurckRemainderTameLipschitzLieCorrectionPureDeTurckBounds
open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Curvature


noncomputable section

open MeasureTheory Set Filter Topology Bundle Manifold DifferentialGeometry.Tensor0SBundle ContinuousLinearMap
open scoped ENNReal NNReal BigOperators Manifold ContDiff

namespace DifferentialGeometry.Analysis.Spectral

open LieCorr0Core
open DifferentialGeometry
open DifferentialGeometry.PDE.RicciFlow DifferentialGeometry.Analysis.Spectral
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

section LieCorr0BoundsE1

open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Spectral.DeTurck (modelDoubleTrace_apply
  cometricLmodel)

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless]
    [BoundarylessManifold I M] [T2Space M] in
private lemma lc0b_unitTensor_toModel (x : M) (m : Fin 0 → E) :
    Tensor0SSpace.toModel (unitTensor (I := I) (M := M) x) m = 1 := by
  rw [unitTensor, Tensor0SSpace.toModel_ofModel]
  rfl

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless]
    [BoundarylessManifold I M] [T2Space M] in
private lemma lc0b_curry_zero (x : M) (D : Tensor0SSpace 1 I x) (v0 : E) :
    tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 0 x D v0 =
      (Tensor0SSpace.toModel D (fun _ : Fin 1 => v0)) • unitTensor (I := I) (M := M) x := by
  apply Tensor0SSpace.toModel_injective
  apply ContinuousMultilinearMap.ext
  intro m
  beta_reduce
  have h1 : Tensor0SSpace.toModel
      (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 0 x D v0) m =
      Tensor0SSpace.toModel D (Fin.cons v0 m) :=
    TensorMultilinear.tensor0S_curry_apply_eval (I := I) (M := M) (n := 0)
      (T := D) (v0 := v0) (vs := m)
  rw [h1]
  rw [Tensor0SSpace.toModel_smul, ContinuousMultilinearMap.smul_apply,
    lc0b_unitTensor_toModel (I := I) (M := M) x m, smul_eq_mul, mul_one]
  congr 1
  funext k
  refine Fin.cases ?_ (fun j => j.elim0) k
  rfl

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless]
    [BoundarylessManifold I M] [T2Space M] in
private lemma lc0b_clm_unit_smul (x : M) (s : ℕ)
    (A : Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x) (c : ℝ) :
    A (c • unitTensor (I := I) (M := M) x) = c • A (unitTensor (I := I) (M := M) x) :=
  A.map_smul c _

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M]
    in
lemma lc0b_KLift_fiber_13 (g₀ : SmoothRiemannianMetric I M)
    (K : SmoothCcTensor g₀ 0 3) (x : M) (D : Tensor0SSpace 1 I x) :
    (show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 4 I x from
      (slotExtendIter (I := I) (M := M) g₀ 0 3 1 K).toSection x) D =
    tensor0SProdKappaFib (I := I) (p := 1) (q := 3) x
      ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 3 I x from K.toSection x)
        (unitTensor (I := I) (M := M) x)) D := by
  apply Tensor0SSpace.toModel_injective
  apply ContinuousMultilinearMap.ext
  intro m
  beta_reduce
  set κ : Tensor0SSpace 3 I x :=
    (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 3 I x from K.toSection x)
      (unitTensor (I := I) (M := M) x) with hκ
  have hLHS : Tensor0SSpace.toModel
      ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 4 I x from
        (slotExtendIter (I := I) (M := M) g₀ 0 3 1 K).toSection x) D) m =
      Tensor0SSpace.toModel D (fun _ : Fin 1 => m 0) *
        Tensor0SSpace.toModel κ (Fin.tail m) := by
    rw [show ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 4 I x from
        (slotExtendIter (I := I) (M := M) g₀ 0 3 1 K).toSection x) D) =
        slotExtendPointwise (I := I) (M := M) g₀ 0 3 x
          (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 3 I x from K.toSection x) D from rfl]
    rw [show m = Fin.cons (m 0) (Fin.tail m) from (Fin.cons_self_tail m).symm]
    rw [slotExtendFib_apply_eval (I := I) (M := M) g₀ 0 3 x _ D (m 0) (Fin.tail m)]
    rw [lc0b_curry_zero (I := I) (M := M) x D (m 0)]
    rw [lc0b_clm_unit_smul (I := I) (M := M) x 3 _ _]
    rw [← hκ, Tensor0SSpace.toModel_smul, ContinuousMultilinearMap.smul_apply, smul_eq_mul]
    rfl
  rw [hLHS]
  rw [tensor0SProdKappaFib_apply (I := I) x κ D, Tensor0SSpace.toModel_ofModel]
  rw [Bundle.continuousMultilinearMap.modelProduct_apply]
  congr 1
  all_goals
    first
      | rfl
      | (congr 1
         funext k
         fin_cases k <;> rfl)

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M]
    in
lemma lc0b_KLift_fiber_21 (g₀ : SmoothRiemannianMetric I M)
    (K : SmoothCcTensor g₀ 0 1) (x : M) (D : Tensor0SSpace 2 I x) :
    (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 3 I x from
      (slotExtendIter (I := I) (M := M) g₀ 0 1 2 K).toSection x) D =
    tensor0SProdKappaFib (I := I) (p := 2) (q := 1) x
      ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 1 I x from K.toSection x)
        (unitTensor (I := I) (M := M) x)) D := by
  apply Tensor0SSpace.toModel_injective
  apply ContinuousMultilinearMap.ext
  intro m
  beta_reduce
  set κ : Tensor0SSpace 1 I x :=
    (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 1 I x from K.toSection x)
      (unitTensor (I := I) (M := M) x) with hκ
  have hstep1 : ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 3 I x from
      (slotExtendIter (I := I) (M := M) g₀ 0 1 2 K).toSection x) D) =
      slotExtendPointwise (I := I) (M := M) g₀ 1 2 x
        (show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 2 I x from
          (slotExtendIter (I := I) (M := M) g₀ 0 1 1 K).toSection x) D := rfl
  have hLHS : Tensor0SSpace.toModel
      ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 3 I x from
        (slotExtendIter (I := I) (M := M) g₀ 0 1 2 K).toSection x) D) m =
      Tensor0SSpace.toModel D ![m 0, m 1] * Tensor0SSpace.toModel κ (fun _ : Fin 1 => m 2) := by
    rw [hstep1]
    rw [show m = Fin.cons (m 0) (Fin.tail m) from (Fin.cons_self_tail m).symm]
    rw [slotExtendFib_apply_eval (I := I) (M := M) g₀ 1 2 x _ D (m 0) (Fin.tail m)]
    set D1 : Tensor0SSpace 1 I x :=
      tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 1 x D (m 0) with hD1
    have hinner : ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 2 I x from
        (slotExtendIter (I := I) (M := M) g₀ 0 1 1 K).toSection x) D1) =
        slotExtendPointwise (I := I) (M := M) g₀ 0 1 x
          (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 1 I x from K.toSection x) D1 := rfl
    rw [hinner]
    rw [show (Fin.tail m : Fin 2 → E) = Fin.cons (m 1) (fun _ : Fin 1 => m 2) from by
      funext k
      fin_cases k <;> rfl]
    rw [slotExtendFib_apply_eval (I := I) (M := M) g₀ 0 1 x _ D1 (m 1) (fun _ : Fin 1 => m 2)]
    rw [lc0b_curry_zero (I := I) (M := M) x D1 (m 1)]
    rw [lc0b_clm_unit_smul (I := I) (M := M) x 1 _ _]
    rw [← hκ, Tensor0SSpace.toModel_smul, ContinuousMultilinearMap.smul_apply, smul_eq_mul]
    have hD1val : Tensor0SSpace.toModel D1 (fun _ : Fin 1 => m 1) =
        Tensor0SSpace.toModel D ![m 0, m 1] := by
      rw [hD1]
      rw [TensorMultilinear.tensor0S_curry_apply_eval (I := I) (M := M) (n := 1)
        (T := D) (v0 := m 0) (vs := fun _ : Fin 1 => m 1)]
      congr 1
      funext k
      fin_cases k <;> rfl
    rw [hD1val]
    rfl
  rw [hLHS]
  rw [tensor0SProdKappaFib_apply (I := I) x κ D, Tensor0SSpace.toModel_ofModel]
  rw [Bundle.continuousMultilinearMap.modelProduct_apply]
  congr 1
  all_goals
    first
      | rfl
      | (congr 1
         funext k
         fin_cases k <;> rfl)

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M]
    in
lemma lc0b_KLift_fiber_23 (g₀ : SmoothRiemannianMetric I M)
    (K : SmoothCcTensor g₀ 0 3) (x : M) (D : Tensor0SSpace 2 I x) :
    (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 5 I x from
      (slotExtendIter (I := I) (M := M) g₀ 0 3 2 K).toSection x) D =
    tensor0SProdKappaFib (I := I) (p := 2) (q := 3) x
      ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 3 I x from K.toSection x)
        (unitTensor (I := I) (M := M) x)) D := by
  apply Tensor0SSpace.toModel_injective
  apply ContinuousMultilinearMap.ext
  intro m
  beta_reduce
  set κ : Tensor0SSpace 3 I x :=
    (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 3 I x from K.toSection x)
      (unitTensor (I := I) (M := M) x) with hκ
  have hLHS : Tensor0SSpace.toModel
      ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 5 I x from
        (slotExtendIter (I := I) (M := M) g₀ 0 3 2 K).toSection x) D) m =
      Tensor0SSpace.toModel D ![m 0, m 1] *
        Tensor0SSpace.toModel κ (fun j : Fin 3 => m (Fin.natAdd 2 j)) := by
    rw [show ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 5 I x from
        (slotExtendIter (I := I) (M := M) g₀ 0 3 2 K).toSection x) D) =
        slotExtendPointwise (I := I) (M := M) g₀ 1 4 x
          (show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 4 I x from
            (slotExtendIter (I := I) (M := M) g₀ 0 3 1 K).toSection x) D from rfl]
    rw [show m = Fin.cons (m 0) (Fin.tail m) from (Fin.cons_self_tail m).symm]
    rw [slotExtendFib_apply_eval (I := I) (M := M) g₀ 1 4 x _ D (m 0) (Fin.tail m)]
    set D1 : Tensor0SSpace 1 I x :=
      tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 1 x D (m 0) with hD1
    rw [show ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 4 I x from
        (slotExtendIter (I := I) (M := M) g₀ 0 3 1 K).toSection x) D1) =
        slotExtendPointwise (I := I) (M := M) g₀ 0 3 x
          (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 3 I x from K.toSection x) D1 from rfl]
    rw [show (Fin.tail m : Fin 4 → E) =
        Fin.cons (m 1) (fun j : Fin 3 => m (Fin.natAdd 2 j)) from by
      funext k
      fin_cases k <;> rfl]
    rw [slotExtendFib_apply_eval (I := I) (M := M) g₀ 0 3 x _ D1 (m 1)
      (fun j : Fin 3 => m (Fin.natAdd 2 j))]
    rw [lc0b_curry_zero (I := I) (M := M) x D1 (m 1)]
    rw [lc0b_clm_unit_smul (I := I) (M := M) x 3 _ _]
    rw [← hκ, Tensor0SSpace.toModel_smul, ContinuousMultilinearMap.smul_apply, smul_eq_mul]
    have hD1val : Tensor0SSpace.toModel D1 (fun _ : Fin 1 => m 1) =
        Tensor0SSpace.toModel D ![m 0, m 1] := by
      rw [hD1]
      rw [TensorMultilinear.tensor0S_curry_apply_eval (I := I) (M := M) (n := 1)
        (T := D) (v0 := m 0) (vs := fun _ : Fin 1 => m 1)]
      congr 1
      funext k
      fin_cases k <;> rfl
    rw [hD1val]
    first
      | rfl
      | (congr 1 ;
          first
            | rfl
            | (congr 1
               funext k
               fin_cases k <;> rfl))
  rw [hLHS]
  rw [tensor0SProdKappaFib_apply (I := I) x κ D, Tensor0SSpace.toModel_ofModel]
  rw [Bundle.continuousMultilinearMap.modelProduct_apply]
  congr 1
  all_goals
    first
      | rfl
      | (congr 1
         funext k
         fin_cases k <;> rfl)

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M]
    in
lemma lc0b_KLift_fiber_33 (g₀ : SmoothRiemannianMetric I M)
    (K : SmoothCcTensor g₀ 0 3) (x : M) (D : Tensor0SSpace 3 I x) :
    (show Tensor0SSpace 3 I x →L[ℝ] Tensor0SSpace 6 I x from
      (slotExtendIter (I := I) (M := M) g₀ 0 3 3 K).toSection x) D =
    tensor0SProdKappaFib (I := I) (p := 3) (q := 3) x
      ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 3 I x from K.toSection x)
        (unitTensor (I := I) (M := M) x)) D := by
  apply Tensor0SSpace.toModel_injective
  apply ContinuousMultilinearMap.ext
  intro m
  beta_reduce
  set κ : Tensor0SSpace 3 I x :=
    (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 3 I x from K.toSection x)
      (unitTensor (I := I) (M := M) x) with hκ
  have hLHS : Tensor0SSpace.toModel
      ((show Tensor0SSpace 3 I x →L[ℝ] Tensor0SSpace 6 I x from
        (slotExtendIter (I := I) (M := M) g₀ 0 3 3 K).toSection x) D) m =
      Tensor0SSpace.toModel D ![m 0, m 1, m 2] *
        Tensor0SSpace.toModel κ (fun j : Fin 3 => m (Fin.natAdd 3 j)) := by
    rw [show ((show Tensor0SSpace 3 I x →L[ℝ] Tensor0SSpace 6 I x from
        (slotExtendIter (I := I) (M := M) g₀ 0 3 3 K).toSection x) D) =
        slotExtendPointwise (I := I) (M := M) g₀ 2 5 x
          (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 5 I x from
            (slotExtendIter (I := I) (M := M) g₀ 0 3 2 K).toSection x) D from rfl]
    rw [show m = Fin.cons (m 0) (Fin.tail m) from (Fin.cons_self_tail m).symm]
    rw [slotExtendFib_apply_eval (I := I) (M := M) g₀ 2 5 x _ D (m 0) (Fin.tail m)]
    set D2 : Tensor0SSpace 2 I x :=
      tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 2 x D (m 0) with hD2
    rw [lc0b_KLift_fiber_23 (I := I) (M := M) g₀ K x D2]
    rw [← hκ]
    rw [tensor0SProdKappaFib_apply (I := I) x κ D2, Tensor0SSpace.toModel_ofModel]
    rw [Bundle.continuousMultilinearMap.modelProduct_apply]
    have hD2val : Tensor0SSpace.toModel D2
        ((Fin.tail m : Fin 5 → E) ∘ Fin.castAdd 3) =
        Tensor0SSpace.toModel D ![m 0, m 1, m 2] := by
      rw [hD2]
      rw [TensorMultilinear.tensor0S_curry_apply_eval (I := I) (M := M) (n := 2)
        (T := D) (v0 := m 0) (vs := (Fin.tail m : Fin 5 → E) ∘ Fin.castAdd 3)]
      congr 1
      funext k
      fin_cases k <;> rfl
    rw [hD2val]
    first
      | rfl
      | (congr 2
         funext j
         fin_cases j <;> rfl)
  rw [hLHS]
  rw [tensor0SProdKappaFib_apply (I := I) x κ D, Tensor0SSpace.toModel_ofModel]
  rw [Bundle.continuousMultilinearMap.modelProduct_apply]
  congr 1
  all_goals
    first
      | rfl
      | (congr 1
         funext k
         fin_cases k <;> rfl)

omit [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
lemma lc0b_kappa_fiber (g₀ g₁ gB : SmoothRiemannianMetric I M) (x : M) :
    (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 3 I x from
      (lc0Kappa (I := I) (M := M) g₀ g₁ gB).toSection x)
      (unitTensor (I := I) (M := M) x) =
      metricConnDiffLoweredFib (I := I) g₁ g₁ gB x := by
  rw [show (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 3 I x from
      (lc0Kappa (I := I) (M := M) g₀ g₁ gB).toSection x)
      (unitTensor (I := I) (M := M) x) =
      (MixedSection.eval₀ (F := E) (E := (TangentSpace I : M → Type _)) x).smulRight
          (lc0KappaField (I := I) (M := M) g₁ gB x)
          (ContinuousMultilinearMap.constOfIsEmpty ℝ (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ))
      from rfl]
  rw [ContinuousLinearMap.smulRight_apply, MixedSection.eval₀_apply,
    ContinuousMultilinearMap.constOfIsEmpty_apply, one_smul]
  rfl

omit [NeZero (Module.finrank ℝ E)] in
omit [BoundarylessManifold I M] in
lemma lc0b_traceStep_fiber (g₀ g₁ : SmoothRiemannianMetric I M) (p : ℕ)
    (σ : Equiv.Perm (Fin (p + 2))) (x : M) :
    (show Tensor0SSpace (p + 2) I x →L[ℝ] Tensor0SSpace p I x from
      (reindexCoeffGen (I := I) (M := M) g₀ (p + 2) p
        (lc0PureDT (I := I) (M := M) g₀ g₁ p) σ).toSection x) =
    lieCorr0TraceStep (I := I) g₁ p σ x := by
  apply ContinuousLinearMap.ext
  intro D
  rw [show ((show Tensor0SSpace (p + 2) I x →L[ℝ] Tensor0SSpace p I x from
      (reindexCoeffGen (I := I) (M := M) g₀ (p + 2) p
        (lc0PureDT (I := I) (M := M) g₀ g₁ p) σ).toSection x) D) =
      reindexCoeffFibGen (I := I) (p + 2) p σ x
        (show Tensor0SSpace (p + 2) I x →L[ℝ] Tensor0SSpace p I x from
          (lc0PureDT (I := I) (M := M) g₀ g₁ p).toSection x) D from rfl]
  rw [reindexCoeffFibGen_apply (I := I) (p + 2) p σ x _ D]
  rw [show ((show Tensor0SSpace (p + 2) I x →L[ℝ] Tensor0SSpace p I x from
      (lc0PureDT (I := I) (M := M) g₀ g₁ p).toSection x)
      (Tensor0SSpace.ofModel (ContinuousMultilinearMap.domDomCongr σ
        (Tensor0SSpace.toModel D)))) =
      cometricDoubleTraceFib (I := I) g₁ p x
        (Tensor0SSpace.ofModel (ContinuousMultilinearMap.domDomCongr σ
          (Tensor0SSpace.toModel D))) from rfl]
  rw [lieCorr0TraceStep, ContinuousLinearMap.comp_apply]
  congr 1

end LieCorr0BoundsE1

end LieCorr0BoundsAll

end DifferentialGeometry.Analysis.Spectral

end

