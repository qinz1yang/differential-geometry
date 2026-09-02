import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegularity.RemainderAction
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegularity.SecondOrderCoefficientLipschitzBounds
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.PrincipalOperatorCoreIdentification
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.LieCorrection.ZeroOrder.Coefficient.RadiusFreeDifference
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.DeTurckVectorField.EndomorphismInsertion.TopOrderSeparation

noncomputable section


open Bundle Manifold MeasureTheory Set Filter DifferentialGeometry.Tensor0SBundle
open scoped BigOperators Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

open DifferentialGeometry.Analysis.Elliptic
open DifferentialGeometry.Analysis.Parabolic
open DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Tensor.RSTensor
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Sobolev.TensorHilbert
open DifferentialGeometry.Analysis.Spectral.DeTurck
open DifferentialGeometry.Analysis.Spectral.MetricRealization

variable
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
      [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E :=
  FiniteDimensional.complete ℝ E

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless]
    [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private theorem unit_sub
    (g : SmoothRiemannianMetric I M) (s : ℕ)
    (S V : SmoothCcTensor g 0 s) (x : M) :
    unitModel (I := I) (M := M) g s (S - V) x =
      unitModel (I := I) (M := M) g s S x -
        unitModel (I := I) (M := M) g s V x := by
  rw [unitModel, unitModel, unitModel]
  have hsec : (S - V).toSection x = S.toSection x - V.toSection x := by
    rw [SmoothCcTensor.toSection_sub]
    rfl
  rw [show ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from
          (S - V).toSection x) (unitTensor (I := I) (M := M) x)) =
        (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from
          S.toSection x) (unitTensor (I := I) (M := M) x) -
        (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from
          V.toSection x) (unitTensor (I := I) (M := M) x) from by
    rw [hsec]
    rfl]
  rw [Tensor0SSpace.toModel_sub]

private noncomputable def fullSlot3
    (g gm : SmoothRiemannianMetric I M) : SmoothCcTensor g 3 3 :=
  endoSlotZeroCcTensor (I := I) (M := M) g 2
    (metricComparisonEndomorphismField (I := I) (M := M) g gm)

private def connectionDifferenceLowOrderPermutation : Equiv.Perm (Fin 3) :=
  ⟨![2, 0, 1], ![1, 2, 0], by decide, by decide⟩

private noncomputable def raiseLast
    (g gm : SmoothRiemannianMetric I M)
    (S : SmoothCcTensor g 0 3) : SmoothCcTensor g 0 3 :=
  domDomCongrSection (I := I) g connectionDifferenceLowOrderPermutation
    (operatorFieldApply (I := I) (M := M) g 3 3
      (fullSlot3 (I := I) (M := M) g gm)
      (domDomCongrSection (I := I) g (finRotate 3) S))

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [BoundarylessManifold I M] [SigmaCompactSpace M] in
omit [I.Boundaryless] in
private theorem raised_inner
    (g gm : SmoothRiemannianMetric I M) (x : M)
    (v w : TangentSpace I x) :
    gm.inner x (metricComparisonEndomorphismField (I := I) (M := M) g gm x v) w =
      g.inner x v w := by
  rw [metricComparisonEndomorphismField_apply, metricComparisonEndomorphism_apply]
  rw [inverseMetricSharpFib_inner (I := I) gm x
    (g0FlatCLM (I := I) g x v) w]
  rw [show cotangentToDualLinear (I := I) (x := x)
      (g0FlatCLM (I := I) g x v) w =
        cotangentToDual (I := I) (x := x)
          (g0FlatCLM (I := I) g x v) w from rfl]
  rw [cotangentToDual_g0FlatCLM]

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
omit [SigmaCompactSpace M] in
private theorem kappa_split
    (g gm : SmoothRiemannianMetric I M)
    (P : SmoothCcTensor g 0 2)
    (htie : ∀ (x : M) (v w : TangentSpace I x),
      gm.inner x v w =
        g.inner x v w + ccTensorBilinSymm (I := I) g P x v w) :
    lieCorrectionZeroKappa (I := I) (M := M) g gm g =
      metricLoweredConnectionDifferenceCoefficient (I := I) g gm +
        lieCorrectionZeroPbLow (I := I) (M := M) g P gm g := by
  refine smoothCcTensor_ext_of_unitModel (I := I) (M := M) g fun x => ?_
  refine ContinuousMultilinearMap.ext fun v => ?_
  rw [kappa_unit (I := I) (M := M)]
  rw [DifferentialGeometry.Analysis.Parabolic.TensorSpectral.unitModel_add (I := I) (M := M), add_apply]
  have hlower := connectionDifferenceLoweredCc_unitModel_apply'
    (I := I) (M := M) g gm x
    (fun i => (tangentSpaceModelContinuousLinearEquiv (I := I) x).symm (v i))
  simp only [ContinuousLinearEquiv.apply_symm_apply] at hlower
  rw [hlower, pbLow_unit (I := I) (M := M)]
  exact htie x
    (PDE.DeTurck.connectionDifference (I := I) gm g x
      ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm (v 0))
      ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm (v 1)))
    ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm (v 2))

omit [SigmaCompactSpace M] in
omit [I.Boundaryless] in
private theorem pb_eq_corr
    (g gm : SmoothRiemannianMetric I M)
    (P : SmoothCcTensor g 0 2)
    (htie : ∀ (x : M) (v w : TangentSpace I x),
      gm.inner x v w =
        g.inner x v w + ccTensorBilinSymm (I := I) g P x v w) :
    lieCorrectionZeroPbLow (I := I) (M := M) g P gm g =
      metricLoweredConnectionDifferenceCorrection (I := I) (M := M) g gm g P := by
  have hk := kappa_split (I := I) (M := M) g gm P htie
  have hm := metricConnectionDifferenceLoweredCoefficient_eq_lowered_add_correction (I := I) (M := M) g gm g P htie
  rw [metricLoweredConnectionDifference_eq_connectionDifferenceLoweredCc (I := I) (M := M) g gm] at hm
  exact add_left_cancel (hk.symm.trans hm)

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] [SigmaCompactSpace M] in
private theorem permCoeff_app
    (g : SmoothRiemannianMetric I M) {d : ℕ}
    (ρ : Equiv.Perm (Fin d)) (S : SmoothCcTensor g 0 d) :
    ccOperatorFieldComp (I := I) (M := M) g 0 d d
        (permCoeff (I := I) (M := M) g ρ) S =
      domDomCongrSection (I := I) g ρ S := by
  refine smoothCcTensor_ext_of_unitModel (I := I) (M := M) g fun x => ?_
  rw [domDomCongrSection_unitModel]
  rw [unitModel, operatorFieldComposition_toSection, ContinuousLinearMap.comp_apply]
  change Tensor0SSpace.toModel
      (slotPermCLM (I := I) ρ x
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace d I x from
          S.toSection x) (unitTensor (I := I) (M := M) x))) = _
  rw [slotPermCLM_apply, Tensor0SSpace.toModel_ofModel]
  rfl

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] [SigmaCompactSpace M] in
private theorem app_smul_left
    (g : SmoothRiemannianMetric I M) (a b c : ℕ) (k : ℝ)
    (Φ : SmoothCcTensor g b c) (W : SmoothCcTensor g a b) :
    ccOperatorFieldComp (I := I) (M := M) g a b c (k • Φ) W =
      k • ccOperatorFieldComp (I := I) (M := M) g a b c Φ W := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rw [operatorFieldComposition_toSection]
  rw [show (k • ccOperatorFieldComp (I := I) (M := M) g a b c Φ W).toSection x =
      k • (ccOperatorFieldComp (I := I) (M := M) g a b c Φ W).toSection x from rfl]
  rw [operatorFieldComposition_toSection, SmoothCcTensor.toSection_smul,
    ContMDiffSection.coe_smul, Pi.smul_apply]
  exact ContinuousLinearMap.smul_comp k
    (show Tensor0SSpace b I x →L[ℝ] Tensor0SSpace c I x from Φ.toSection x)
    (show Tensor0SSpace a I x →L[ℝ] Tensor0SSpace b I x from W.toSection x)

private noncomputable def koszulOp
    (g : SmoothRiemannianMetric I M) : SmoothCcTensor g 3 3 :=
  (1 / 2 : ℝ) •
    (permCoeff (I := I) (M := M) g (Equiv.swap (0 : Fin 3) 2) +
      permCoeff (I := I) (M := M) g (finRotate 3) -
      permCoeff (I := I) (M := M) g (Equiv.swap (1 : Fin 3) 2))

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] in
omit [T2Space M] [SigmaCompactSpace M] in
private theorem symm_eq_self
    (g : SmoothRiemannianMetric I M) (S : SmoothCcTensor g 0 2)
    (hS : ∀ (x : M) (u v : TangentSpace I x),
      ccTensorBilin (I := I) g S x u v =
        ccTensorBilin (I := I) g S x v u) :
    ccTensor02Symm (I := I) (M := M) g S = S := by
  have hswap :
      domDomCongrSection (I := I) g (Equiv.swap (0 : Fin 2) 1) S = S := by
    refine smoothCcTensor_ext_of_unitModel (I := I) (M := M) g fun x => ?_
    rw [domDomCongrSection_unitModel]
    refine ContinuousMultilinearMap.ext fun v => ?_
    rw [ContinuousMultilinearMap.domDomCongr_apply]
    have hv : ∀ u w : TangentSpace I x,
        unitModel (I := I) (M := M) g 2 S x ![u, w] =
          unitModel (I := I) (M := M) g 2 S x ![w, u] := by
      intro u w
      rw [unitModel_eq_ccTensorBilin_local (I := I) (M := M) g S x u w,
        unitModel_eq_ccTensorBilin_local (I := I) (M := M) g S x w u]
      exact hS x u w
    have hveta :
        (fun i => v ((Equiv.swap (0 : Fin 2) 1) i)) = ![v 1, v 0] := by
      funext i
      fin_cases i <;> rfl
    have hveta' : v = ![v 0, v 1] := by
      funext i
      fin_cases i <;> rfl
    rw [hveta]
    conv_rhs => rw [hveta']
    exact hv (v 1) (v 0)
  have htwo : S + S = (2 : ℝ) • S := (two_smul ℝ S).symm
  rw [ccTensor02Symm, hswap, htwo, smul_smul,
    show (1 / 2 : ℝ) * 2 = 1 by norm_num, one_smul]

omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] [SigmaCompactSpace M] in
private theorem koszulOp_app
    (g : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2)
    (hT : ∀ (x : M) (u v : TangentSpace I x),
      ccTensorBilin (I := I) g T x u v =
        ccTensorBilin (I := I) g T x v u) :
    ccOperatorFieldComp (I := I) (M := M) g 0 3 3
        (koszulOp (I := I) (M := M) g)
        (covGrad (I := I) (M := M) g 0 2 T) =
      koszulCovecCc (I := I) g T := by
  have hs := symm_eq_self (I := I) (M := M) g T hT
  rw [koszulOp, app_smul_left, operatorFieldComposition_sub_left,
    operatorFieldComposition_add_left, permCoeff_app, permCoeff_app, permCoeff_app]
  rw [koszulCovecCc, symmSCovGrad3, hs]

private noncomputable def kappaOp
    (g : SmoothRiemannianMetric I M) : SmoothCcTensor g 3 3 :=
  ccOperatorFieldComp (I := I) (M := M) g 3 3 3
    (permCoeff (I := I) (M := M) g (finRotate 3).symm)
    (koszulOp (I := I) (M := M) g)

omit [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
private theorem kappaOp_app
    (g gm : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2)
    (hT : ∀ (x : M) (u v : TangentSpace I x),
      ccTensorBilin (I := I) g T x u v =
        ccTensorBilin (I := I) g T x v u)
    (htie : ∀ (x : M) (u v : TangentSpace I x),
      gm.inner x u v =
        g.inner x u v + ccTensorBilinSymm (I := I) g T x u v) :
    ccOperatorFieldComp (I := I) (M := M) g 0 3 3
        (kappaOp (I := I) (M := M) g)
        (covGrad (I := I) (M := M) g 0 2 T) =
      lieCorrectionZeroKappa (I := I) (M := M) g gm g := by
  rw [operatorFieldComposition_zero_eq_operatorFieldApply, kappaOp, ← operatorFieldApplication_assoc]
  rw [show operatorFieldApply (I := I) (M := M) g 3 3
      (koszulOp (I := I) (M := M) g)
      (covGrad (I := I) (M := M) g 0 2 T) =
        koszulCovecCc (I := I) g T by
      rw [← operatorFieldComposition_zero_eq_operatorFieldApply]
      exact koszulOp_app (I := I) (M := M) g T hT]
  rw [← operatorFieldComposition_zero_eq_operatorFieldApply, permCoeff_app]
  exact (kappa_self (I := I) (M := M) g gm T htie).symm

omit [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
private theorem kappa_pair
    (g gT gU : SmoothRiemannianMetric I M)
    (T U : SmoothCcTensor g 0 2)
    (hT : ∀ (x : M) (u v : TangentSpace I x),
      ccTensorBilin (I := I) g T x u v =
        ccTensorBilin (I := I) g T x v u)
    (hU : ∀ (x : M) (u v : TangentSpace I x),
      ccTensorBilin (I := I) g U x u v =
        ccTensorBilin (I := I) g U x v u)
    (hTtie : ∀ (x : M) (u v : TangentSpace I x),
      gT.inner x u v =
        g.inner x u v + ccTensorBilinSymm (I := I) g T x u v)
    (hUtie : ∀ (x : M) (u v : TangentSpace I x),
      gU.inner x u v =
        g.inner x u v + ccTensorBilinSymm (I := I) g U x u v) :
    lieCorrectionZeroKappa (I := I) (M := M) g gT g -
        lieCorrectionZeroKappa (I := I) (M := M) g gU g =
      ccOperatorFieldComp (I := I) (M := M) g 0 3 3
        (kappaOp (I := I) (M := M) g)
        (covGrad (I := I) (M := M) g 0 2 (T - U)) := by
  rw [← kappaOp_app (I := I) (M := M) g gT T hT hTtie,
    ← kappaOp_app (I := I) (M := M) g gU U hU hUtie]
  rw [← operatorFieldComposition_sub_right, ← covGrad_sub]

omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
omit [I.Boundaryless] in
private theorem moving_pair
    (g gT gU : SmoothRiemannianMetric I M)
    (T U : SmoothCcTensor g 0 2)
    (hTtie : ∀ (x : M) (v w : TangentSpace I x),
      gT.inner x v w =
        g.inner x v w + ccTensorBilinSymm (I := I) g T x v w)
    (hUtie : ∀ (x : M) (v w : TangentSpace I x),
      gU.inner x v w =
        g.inner x v w + ccTensorBilinSymm (I := I) g U x v w) :
    raiseLast (I := I) (M := M) g gU
        (lieCorrectionZeroKappa (I := I) (M := M) g gT g -
          lieCorrectionZeroKappa (I := I) (M := M) g gU g -
          lieCorrectionZeroPbLow (I := I) (M := M) g (T - U) gT g) =
      metricLoweredConnectionDifferenceCoefficient (I := I) g gT -
        metricLoweredConnectionDifferenceCoefficient (I := I) g gU := by
  refine smoothCcTensor_ext_of_unitModel (I := I) (M := M) g fun x => ?_
  refine ContinuousMultilinearMap.ext fun v => ?_
  rw [raiseLast, domDomCongrSection_unitModel,
    ContinuousMultilinearMap.domDomCongr_apply]
  have hv₀ : (fun i => v (connectionDifferenceLowOrderPermutation i)) = ![v 2, v 0, v 1] := by
    funext i
    fin_cases i <;> rfl
  rw [hv₀]
  rw [unitModel, operatorFieldApplication_toSection, ContinuousLinearMap.comp_apply]
  simp only [fullSlot3, slotInsertEndoCc_toSection]
  rw [slotInsertEndoFib_apply_eval]
  have hv :
      Function.update (![v 2, v 0, v 1] : Fin 3 → E) 0
          (tangentLinearMapToModel
            (metricComparisonEndomorphismField (I := I) (M := M) g gU x) (v 2)) =
        ![tangentLinearMapToModel
            (metricComparisonEndomorphismField (I := I) (M := M) g gU x) (v 2),
          v 0, v 1] := by
    funext i
    fin_cases i <;> simp
  simp only [Matrix.cons_val_zero]
  rw [hv]
  rw [show Tensor0SSpace.toModel
      ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 3 I x from
        (domDomCongrSection (I := I) g (finRotate 3)
          (lieCorrectionZeroKappa (I := I) (M := M) g gT g -
            lieCorrectionZeroKappa (I := I) (M := M) g gU g -
            lieCorrectionZeroPbLow (I := I) (M := M) g (T - U) gT g)).toSection x)
        (unitTensor (I := I) (M := M) x))
      ![tangentLinearMapToModel
          (metricComparisonEndomorphismField (I := I) (M := M) g gU x) (v 2),
        v 0, v 1] =
      unitModel (I := I) (M := M) g 3
        (domDomCongrSection (I := I) g (finRotate 3)
          (lieCorrectionZeroKappa (I := I) (M := M) g gT g -
            lieCorrectionZeroKappa (I := I) (M := M) g gU g -
            lieCorrectionZeroPbLow (I := I) (M := M) g (T - U) gT g)) x
        ![tangentLinearMapToModel
            (metricComparisonEndomorphismField (I := I) (M := M) g gU x) (v 2),
          v 0, v 1] from rfl]
  rw [domDomCongrSection_unitModel,
    ContinuousMultilinearMap.domDomCongr_apply]
  have hv₁ :
      (fun i =>
        (![tangentLinearMapToModel
            (metricComparisonEndomorphismField (I := I) (M := M) g gU x) (v 2),
          v 0, v 1] : Fin 3 → E) ((finRotate 3) i)) =
        ![v 0, v 1,
          tangentLinearMapToModel
            (metricComparisonEndomorphismField (I := I) (M := M) g gU x) (v 2)] := by
    funext i
    fin_cases i <;> simp
  rw [hv₁]
  rw [unit_sub (I := I) (M := M), unit_sub (I := I) (M := M)]
  simp only [sub_apply]
  rw [kappa_unit (I := I) (M := M), kappa_unit (I := I) (M := M),
    pbLow_unit (I := I) (M := M)]
  simp only [tangentLinearMapToModel_apply]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]
  rw [show (tangentSpaceModelContinuousLinearEquiv (I := I) x).symm
      (tangentSpaceModelContinuousLinearEquiv (I := I) x
        (metricComparisonEndomorphismField (I := I) (M := M) g gU x
          ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm (v 2)))) =
      metricComparisonEndomorphismField (I := I) (M := M) g gU x
        ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm (v 2)) from
    (tangentSpaceModelContinuousLinearEquiv (I := I) x).symm_apply_apply _]
  let a := (tangentSpaceModelContinuousLinearEquiv (I := I) x).symm (v 0)
  let b := (tangentSpaceModelContinuousLinearEquiv (I := I) x).symm (v 1)
  let c := (tangentSpaceModelContinuousLinearEquiv (I := I) x).symm (v 2)
  let z := metricComparisonEndomorphismField (I := I) (M := M) g gU x c
  change gT.inner x (PDE.DeTurck.connectionDifference (I := I) gT g x a b) z -
      gU.inner x (PDE.DeTurck.connectionDifference (I := I) gU g x a b) z -
      ccTensorBilinSymm (I := I) g (T - U) x
        (PDE.DeTurck.connectionDifference (I := I) gT g x a b) z = _
  have hTU :
      ccTensorBilinSymm (I := I) g (T - U) x
          (PDE.DeTurck.connectionDifference (I := I) gT g x a b) z =
        gT.inner x (PDE.DeTurck.connectionDifference (I := I) gT g x a b) z -
          gU.inner x (PDE.DeTurck.connectionDifference (I := I) gT g x a b) z := by
    rw [ccTensorBilinSymm_sub, hTtie, hUtie]
    ring
  rw [hTU]
  rw [show
      gT.inner x (PDE.DeTurck.connectionDifference (I := I) gT g x a b) z -
          gU.inner x (PDE.DeTurck.connectionDifference (I := I) gU g x a b) z -
        (gT.inner x (PDE.DeTurck.connectionDifference (I := I) gT g x a b) z -
          gU.inner x (PDE.DeTurck.connectionDifference (I := I) gT g x a b) z) =
        gU.inner x
          (PDE.DeTurck.connectionDifference (I := I) gT g x a b -
            PDE.DeTurck.connectionDifference (I := I) gU g x a b) z by
    rw [map_sub, sub_apply]
    ring]
  dsimp only [z]
  rw [gU.symm x
    (PDE.DeTurck.connectionDifference (I := I) gT g x a b -
      PDE.DeTurck.connectionDifference (I := I) gU g x a b)
    (metricComparisonEndomorphismField (I := I) (M := M) g gU x c)]
  rw [map_sub, raised_inner (I := I) (M := M),
    raised_inner (I := I) (M := M)]
  rw [g.symm x c (PDE.DeTurck.connectionDifference (I := I) gT g x a b),
    g.symm x c (PDE.DeTurck.connectionDifference (I := I) gU g x a b)]
  have hlowT := connectionDifferenceLoweredCc_unitModel_apply'
    (I := I) (M := M) g gT x
    (fun i => (tangentSpaceModelContinuousLinearEquiv (I := I) x).symm (v i))
  have hlowU := connectionDifferenceLoweredCc_unitModel_apply'
    (I := I) (M := M) g gU x
    (fun i => (tangentSpaceModelContinuousLinearEquiv (I := I) x).symm (v i))
  simp only [ContinuousLinearEquiv.apply_symm_apply] at hlowT hlowU
  rw [unit_sub (I := I) (M := M), sub_apply, hlowT, hlowU]

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M]
    [SigmaCompactSpace M] in
private theorem app_sub_right
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (Φ : SmoothCcTensor g r s) (W V : SmoothCcTensor g 0 r) :
    operatorFieldApply (I := I) (M := M) g r s Φ (W - V) =
      operatorFieldApply (I := I) (M := M) g r s Φ W -
        operatorFieldApply (I := I) (M := M) g r s Φ V := by
  rw [sub_eq_add_neg, operatorFieldApplication_add_right]
  have hneg := operatorFieldApplication_smul_right (I := I) (M := M) g r s
    (-1 : ℝ) Φ V
  simp only [neg_one_smul] at hneg
  rw [hneg]
  rfl

private def corrPermA : Equiv.Perm (Fin 5) :=
  ⟨![2, 3, 0, 1, 4], ![2, 3, 0, 1, 4], by decide, by decide⟩

private def corrPermB : Equiv.Perm (Fin 5) :=
  ⟨![2, 3, 0, 4, 1], ![2, 4, 0, 1, 3], by decide, by decide⟩

private noncomputable def corrPk3
    (g : SmoothRiemannianMetric I M) (P : SmoothCcTensor g 0 2) :
    SmoothCcTensor g 3 5 :=
  slotExtend (I := I) (M := M) g 2 4
    (slotExtend (I := I) (M := M) g 1 3
      (slotExtend (I := I) (M := M) g 0 2 P))

private noncomputable def corrPhi
    (g : SmoothRiemannianMetric I M) (P : SmoothCcTensor g 0 2)
    (σ : Equiv.Perm (Fin 5)) : SmoothCcTensor g 3 3 :=
  ccOperatorFieldComp (I := I) (M := M) g 3 5 3
    (reindexCoeffGen (I := I) (M := M) g 5 3
      (cometricDoubleTraceField (I := I) g 3) σ)
    (corrPk3 (I := I) (M := M) g P)

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
omit [I.Boundaryless] in
private theorem corr_formula
    (g gm g_bg : SmoothRiemannianMetric I M)
    (P : SmoothCcTensor g 0 2) :
    metricLoweredConnectionDifferenceCorrection (I := I) (M := M) g gm g_bg P =
      (1 / 2 : ℝ) • operatorFieldApply (I := I) (M := M) g 3 3
          (corrPhi (I := I) (M := M) g P corrPermA)
          (metricLoweredConnectionDifference (I := I) (M := M) g gm g_bg) +
        (1 / 2 : ℝ) • operatorFieldApply (I := I) (M := M) g 3 3
          (corrPhi (I := I) (M := M) g P corrPermB)
          (metricLoweredConnectionDifference (I := I) (M := M) g gm g_bg) := by
  rfl

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [SigmaCompactSpace M] in
private theorem corr_cross
    (g gT gU : SmoothRiemannianMetric I M)
    (U : SmoothCcTensor g 0 2) :
    metricLoweredConnectionDifferenceCorrection (I := I) (M := M) g gT g U -
        metricLoweredConnectionDifferenceCorrection (I := I) (M := M) g gU g U =
      -metricLoweredConnectionDifferenceCorrection (I := I) (M := M) g gU gT U := by
  let WT : SmoothCcTensor g 0 3 :=
    metricLoweredConnectionDifference (I := I) (M := M) g gT g
  let WU : SmoothCcTensor g 0 3 :=
    metricLoweredConnectionDifference (I := I) (M := M) g gU g
  let WC : SmoothCcTensor g 0 3 :=
    metricLoweredConnectionDifference (I := I) (M := M) g gU gT
  have hW : WT - WU = -WC := by
    simp only [WT, WU, WC, metricLoweredConnectionDifference]
    module
  have hA := app_sub_right (I := I) (M := M) g 3 3
    (corrPhi (I := I) (M := M) g U corrPermA) WT WU
  have hB := app_sub_right (I := I) (M := M) g 3 3
    (corrPhi (I := I) (M := M) g U corrPermB) WT WU
  have hAn := operatorFieldApplication_smul_right (I := I) (M := M) g 3 3
    (-1 : ℝ) (corrPhi (I := I) (M := M) g U corrPermA) WC
  have hBn := operatorFieldApplication_smul_right (I := I) (M := M) g 3 3
    (-1 : ℝ) (corrPhi (I := I) (M := M) g U corrPermB) WC
  simp only [neg_one_smul] at hAn hBn
  have hA' :
      operatorFieldApply (I := I) (M := M) g 3 3
          (corrPhi (I := I) (M := M) g U corrPermA) WT -
        operatorFieldApply (I := I) (M := M) g 3 3
          (corrPhi (I := I) (M := M) g U corrPermA) WU =
      -operatorFieldApply (I := I) (M := M) g 3 3
        (corrPhi (I := I) (M := M) g U corrPermA) WC := by
    rw [← hA, hW, hAn]
  have hB' :
      operatorFieldApply (I := I) (M := M) g 3 3
          (corrPhi (I := I) (M := M) g U corrPermB) WT -
        operatorFieldApply (I := I) (M := M) g 3 3
          (corrPhi (I := I) (M := M) g U corrPermB) WU =
      -operatorFieldApply (I := I) (M := M) g 3 3
        (corrPhi (I := I) (M := M) g U corrPermB) WC := by
    rw [← hB, hW, hBn]
  rw [corr_formula (I := I) (M := M) g gT g U,
    corr_formula (I := I) (M := M) g gU g U,
    corr_formula (I := I) (M := M) g gU gT U]
  change
    ((1 / 2 : ℝ) • operatorFieldApply (I := I) (M := M) g 3 3
          (corrPhi (I := I) (M := M) g U corrPermA) WT +
        (1 / 2 : ℝ) • operatorFieldApply (I := I) (M := M) g 3 3
          (corrPhi (I := I) (M := M) g U corrPermB) WT) -
      ((1 / 2 : ℝ) • operatorFieldApply (I := I) (M := M) g 3 3
          (corrPhi (I := I) (M := M) g U corrPermA) WU +
        (1 / 2 : ℝ) • operatorFieldApply (I := I) (M := M) g 3 3
          (corrPhi (I := I) (M := M) g U corrPermB) WU) =
    -((1 / 2 : ℝ) • operatorFieldApply (I := I) (M := M) g 3 3
          (corrPhi (I := I) (M := M) g U corrPermA) WC +
        (1 / 2 : ℝ) • operatorFieldApply (I := I) (M := M) g 3 3
          (corrPhi (I := I) (M := M) g U corrPermB) WC)
  calc
    _ = (1 / 2 : ℝ) •
          (operatorFieldApply (I := I) (M := M) g 3 3
              (corrPhi (I := I) (M := M) g U corrPermA) WT -
            operatorFieldApply (I := I) (M := M) g 3 3
              (corrPhi (I := I) (M := M) g U corrPermA) WU) +
        (1 / 2 : ℝ) •
          (operatorFieldApply (I := I) (M := M) g 3 3
              (corrPhi (I := I) (M := M) g U corrPermB) WT -
            operatorFieldApply (I := I) (M := M) g 3 3
              (corrPhi (I := I) (M := M) g U corrPermB) WU) := by
      module
    _ = _ := by rw [hA', hB']; module

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
omit [I.Boundaryless] in
private theorem raise_cross
    (g gT gU : SmoothRiemannianMetric I M) :
    raiseLast (I := I) (M := M) g gU
        (-lieCorrectionZeroKappa (I := I) (M := M) g gU gT) =
      metricLoweredConnectionDifferenceCoefficient (I := I) g gT -
        metricLoweredConnectionDifferenceCoefficient (I := I) g gU := by
  refine smoothCcTensor_ext_of_unitModel (I := I) (M := M) g fun x => ?_
  refine ContinuousMultilinearMap.ext fun v => ?_
  rw [raiseLast, domDomCongrSection_unitModel,
    ContinuousMultilinearMap.domDomCongr_apply]
  have hv₀ : (fun i => v (connectionDifferenceLowOrderPermutation i)) = ![v 2, v 0, v 1] := by
    funext i
    fin_cases i <;> rfl
  rw [hv₀]
  rw [unitModel, operatorFieldApplication_toSection, ContinuousLinearMap.comp_apply]
  simp only [fullSlot3, slotInsertEndoCc_toSection]
  rw [slotInsertEndoFib_apply_eval]
  simp only [Matrix.cons_val_zero]
  have hv :
      Function.update (![v 2, v 0, v 1] : Fin 3 → E) 0
          (tangentLinearMapToModel
            (metricComparisonEndomorphismField (I := I) (M := M) g gU x) (v 2)) =
        ![tangentLinearMapToModel
            (metricComparisonEndomorphismField (I := I) (M := M) g gU x) (v 2),
          v 0, v 1] := by
    funext i
    fin_cases i <;> simp
  rw [hv]
  rw [show Tensor0SSpace.toModel
      ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 3 I x from
        (domDomCongrSection (I := I) g (finRotate 3)
          (-lieCorrectionZeroKappa (I := I) (M := M) g gU gT)).toSection x)
        (unitTensor (I := I) (M := M) x))
      ![tangentLinearMapToModel
          (metricComparisonEndomorphismField (I := I) (M := M) g gU x) (v 2),
        v 0, v 1] =
      unitModel (I := I) (M := M) g 3
        (domDomCongrSection (I := I) g (finRotate 3)
          (-lieCorrectionZeroKappa (I := I) (M := M) g gU gT)) x
        ![tangentLinearMapToModel
            (metricComparisonEndomorphismField (I := I) (M := M) g gU x) (v 2),
          v 0, v 1] from rfl]
  rw [domDomCongrSection_unitModel,
    ContinuousMultilinearMap.domDomCongr_apply]
  have hv₁ :
      (fun i =>
        (![tangentLinearMapToModel
            (metricComparisonEndomorphismField (I := I) (M := M) g gU x) (v 2),
          v 0, v 1] : Fin 3 → E) ((finRotate 3) i)) =
        ![v 0, v 1,
          tangentLinearMapToModel
            (metricComparisonEndomorphismField (I := I) (M := M) g gU x) (v 2)] := by
    funext i
    fin_cases i <;> simp
  rw [hv₁]
  rw [show unitModel (I := I) (M := M) g 3
      (-lieCorrectionZeroKappa (I := I) (M := M) g gU gT) x =
      -unitModel (I := I) (M := M) g 3
        (lieCorrectionZeroKappa (I := I) (M := M) g gU gT) x by
    simp only [unitModel]
    rw [SmoothCcTensor.toSection_neg, ContMDiffSection.coe_neg,
      Pi.neg_apply, neg_apply,
      Tensor0SSpace.toModel_neg]]
  rw [neg_apply,
    kappa_unit (I := I) (M := M)]
  simp only [tangentLinearMapToModel_apply]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]
  rw [show (tangentSpaceModelContinuousLinearEquiv (I := I) x).symm
      (tangentSpaceModelContinuousLinearEquiv (I := I) x
        (metricComparisonEndomorphismField (I := I) (M := M) g gU x
          ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm (v 2)))) =
      metricComparisonEndomorphismField (I := I) (M := M) g gU x
        ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm (v 2)) from
    (tangentSpaceModelContinuousLinearEquiv (I := I) x).symm_apply_apply _]
  let a := (tangentSpaceModelContinuousLinearEquiv (I := I) x).symm (v 0)
  let b := (tangentSpaceModelContinuousLinearEquiv (I := I) x).symm (v 1)
  let c := (tangentSpaceModelContinuousLinearEquiv (I := I) x).symm (v 2)
  change -gU.inner x
      (PDE.DeTurck.connectionDifference (I := I) gU gT x a b)
      (metricComparisonEndomorphismField (I := I) (M := M) g gU x c) = _
  rw [gU.symm x
    (PDE.DeTurck.connectionDifference (I := I) gU gT x a b)
    (metricComparisonEndomorphismField (I := I) (M := M) g gU x c)]
  rw [raised_inner (I := I) (M := M)]
  rw [g.symm x c (PDE.DeTurck.connectionDifference (I := I) gU gT x a b)]
  have hc := PDE.DeTurck.connectionDifference_cocycle
    (I := I) gT gU g x a b
  have hlowT := connectionDifferenceLoweredCc_unitModel_apply'
    (I := I) (M := M) g gT x
    (fun i => (tangentSpaceModelContinuousLinearEquiv (I := I) x).symm (v i))
  have hlowU := connectionDifferenceLoweredCc_unitModel_apply'
    (I := I) (M := M) g gU x
    (fun i => (tangentSpaceModelContinuousLinearEquiv (I := I) x).symm (v i))
  simp only [ContinuousLinearEquiv.apply_symm_apply] at hlowT hlowU
  rw [unit_sub (I := I) (M := M), sub_apply, hlowT, hlowU]
  rw [hc, map_add, add_apply]
  ring

omit [SigmaCompactSpace M] in
omit [I.Boundaryless] in
private theorem moving_corr
    (g gT gU : SmoothRiemannianMetric I M)
    (T U : SmoothCcTensor g 0 2)
    (hTtie : ∀ (x : M) (v w : TangentSpace I x),
      gT.inner x v w =
        g.inner x v w + ccTensorBilinSymm (I := I) g T x v w)
    (hUtie : ∀ (x : M) (v w : TangentSpace I x),
      gU.inner x v w =
        g.inner x v w + ccTensorBilinSymm (I := I) g U x v w) :
    raiseLast (I := I) (M := M) g gU
        (lieCorrectionZeroKappa (I := I) (M := M) g gT g -
          lieCorrectionZeroKappa (I := I) (M := M) g gU g -
          metricLoweredConnectionDifferenceCorrection (I := I) (M := M) g gT g (T - U)) =
      metricLoweredConnectionDifferenceCoefficient (I := I) g gT -
        metricLoweredConnectionDifferenceCoefficient (I := I) g gU := by
  have hmT := metricConnectionDifferenceLoweredCoefficient_eq_lowered_add_correction (I := I) (M := M) g gT g T hTtie
  have hmU := metricConnectionDifferenceLoweredCoefficient_eq_lowered_add_correction (I := I) (M := M) g gU g U hUtie
  rw [metricLoweredConnectionDifference_eq_connectionDifferenceLoweredCc (I := I) (M := M) g gT] at hmT
  rw [metricLoweredConnectionDifference_eq_connectionDifferenceLoweredCc (I := I) (M := M) g gU] at hmU
  have hsub := metricLoweredConnectionDifferenceCorrection_sub (I := I) (M := M) g gT g T U
  have hcross := corr_cross (I := I) (M := M) g gT gU U
  have hmC := metricConnectionDifferenceLoweredCoefficient_eq_lowered_add_correction (I := I) (M := M) g gU gT U hUtie
  have hwC :
      metricLoweredConnectionDifference (I := I) (M := M) g gU gT =
        metricLoweredConnectionDifferenceCoefficient (I := I) g gU -
          metricLoweredConnectionDifferenceCoefficient (I := I) g gT := by
    simp only [metricLoweredConnectionDifference]
  rw [hwC] at hmC
  have hcore :
      lieCorrectionZeroKappa (I := I) (M := M) g gT g -
          lieCorrectionZeroKappa (I := I) (M := M) g gU g -
          metricLoweredConnectionDifferenceCorrection (I := I) (M := M) g gT g (T - U) =
        -lieCorrectionZeroKappa (I := I) (M := M) g gU gT := by
    change
      metricConnectionDifferenceLoweredCoefficient (I := I) (M := M) g gT g -
          metricConnectionDifferenceLoweredCoefficient (I := I) (M := M) g gU g -
          metricLoweredConnectionDifferenceCorrection (I := I) (M := M) g gT g (T - U) =
        -metricConnectionDifferenceLoweredCoefficient (I := I) (M := M) g gU gT
    rw [hmT, hmU, hsub]
    calc
      _ = (metricLoweredConnectionDifferenceCoefficient (I := I) g gT -
            metricLoweredConnectionDifferenceCoefficient (I := I) g gU) +
          (metricLoweredConnectionDifferenceCorrection (I := I) (M := M) g gT g U -
            metricLoweredConnectionDifferenceCorrection (I := I) (M := M) g gU g U) := by
        module
      _ = (metricLoweredConnectionDifferenceCoefficient (I := I) g gT -
            metricLoweredConnectionDifferenceCoefficient (I := I) g gU) -
          metricLoweredConnectionDifferenceCorrection (I := I) (M := M) g gU gT U := by
        rw [hcross]
        module
      _ = -(metricLoweredConnectionDifferenceCoefficient (I := I) g gU -
            metricLoweredConnectionDifferenceCoefficient (I := I) g gT +
          metricLoweredConnectionDifferenceCorrection (I := I) (M := M) g gU gT U) := by
        module
      _ = -metricConnectionDifferenceLoweredCoefficient (I := I) (M := M) g gU gT := by
        rw [← hmC]
  rw [hcore]
  exact raise_cross (I := I) (M := M) g gT gU

omit [BoundarylessManifold I M] [NeZero (Module.finrank ℝ E)] [CompactSpace M] in
private theorem jet_nonneg
    (g : SmoothRiemannianMetric I M) {r s m : ℕ}
    (S : SmoothCcTensor g r s) :
    0 ≤ covariantJetNormSq (I := I) (M := M) g m S :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

omit [BoundarylessManifold I M] [NeZero (Module.finrank ℝ E)] [CompactSpace M] in
private theorem jet_mono
    (g : SmoothRiemannianMetric I M) {r s m n : ℕ}
    (hmn : m ≤ n) (S : SmoothCcTensor g r s) :
    covariantJetNormSq (I := I) (M := M) g m S ≤
      covariantJetNormSq (I := I) (M := M) g n S := by
  unfold covariantJetNormSq
  exact Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.range_subset_range.mpr (Nat.add_le_add_right hmn 1))
    (fun _ _ _ => sq_nonneg _)

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
private theorem jet_sub
    (g : SmoothRiemannianMetric I M) {r s : ℕ} (m : ℕ)
    (S V : SmoothCcTensor g r s) :
    covariantJetNormSq (I := I) (M := M) g m (S - V) ≤
      2 * (covariantJetNormSq (I := I) (M := M) g m S +
        covariantJetNormSq (I := I) (M := M) g m V) := by
  unfold covariantJetNormSq
  calc
    ∑ q ∈ Finset.range (m + 1),
        ‖iteratedCovGrad (I := I) g r s q (S - V)‖ ^ 2 ≤
      ∑ q ∈ Finset.range (m + 1),
        2 * (‖iteratedCovGrad (I := I) g r s q S‖ ^ 2 +
          ‖iteratedCovGrad (I := I) g r s q V‖ ^ 2) := by
      refine Finset.sum_le_sum fun q _ => ?_
      rw [iteratedCovGrad_sub]
      have htri := norm_sub_le
        (iteratedCovGrad (I := I) g r s q S)
        (iteratedCovGrad (I := I) g r s q V)
      calc
        ‖iteratedCovGrad (I := I) g r s q S -
            iteratedCovGrad (I := I) g r s q V‖ ^ 2 ≤
          (‖iteratedCovGrad (I := I) g r s q S‖ +
            ‖iteratedCovGrad (I := I) g r s q V‖) ^ 2 :=
              pow_le_pow_left₀ (norm_nonneg _) htri 2
        _ ≤ 2 * (‖iteratedCovGrad (I := I) g r s q S‖ ^ 2 +
            ‖iteratedCovGrad (I := I) g r s q V‖ ^ 2) := by
          nlinarith [sq_nonneg
            (‖iteratedCovGrad (I := I) g r s q S‖ -
              ‖iteratedCovGrad (I := I) g r s q V‖)]
    _ = 2 * ((∑ q ∈ Finset.range (m + 1),
          ‖iteratedCovGrad (I := I) g r s q S‖ ^ 2) +
        ∑ q ∈ Finset.range (m + 1),
          ‖iteratedCovGrad (I := I) g r s q V‖ ^ 2) := by
      simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum]

private theorem app_h2_mul
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) (p r c : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (Φ : SmoothCcTensor g r c) (W : SmoothCcTensor g p r),
        covariantJetNormSq (I := I) (M := M) g 2
            (ccOperatorFieldComp (I := I) (M := M) g p r c Φ W) ≤
          C * covariantJetNormSq (I := I) (M := M) g 2 Φ *
            covariantJetNormSq (I := I) (M := M) g 2 W := by
  obtain ⟨C₀, hC₀, happ⟩ :=
    operator_field_composition_h2_h2_to_h2_bound (I := I) (M := M) hDim g p r c
  refine ⟨C₀ ^ 2, sq_nonneg _, ?_⟩
  intro Φ W
  have hΦ0 : 0 ≤ covariantJetNormSq (I := I) (M := M) g 2 Φ :=
    jet_nonneg (I := I) (M := M) g Φ
  have hW0 : 0 ≤ covariantJetNormSq (I := I) (M := M) g 2 W :=
    jet_nonneg (I := I) (M := M) g W
  have hsΦ :
      Real.sqrt (covariantJetNormSq (I := I) (M := M) g 2 Φ) ^ 2 =
        covariantJetNormSq (I := I) (M := M) g 2 Φ :=
    Real.sq_sqrt hΦ0
  have hsW :
      Real.sqrt (covariantJetNormSq (I := I) (M := M) g 2 W) ^ 2 =
        covariantJetNormSq (I := I) (M := M) g 2 W :=
    Real.sq_sqrt hW0
  have h := happ Φ W
    (Real.sqrt (covariantJetNormSq (I := I) (M := M) g 2 Φ))
    (Real.sqrt (covariantJetNormSq (I := I) (M := M) g 2 W))
    (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    (by
      unfold covariantJetNormSq
      exact le_of_eq hsΦ.symm)
    (by
      unfold covariantJetNormSq
      exact le_of_eq hsW.symm)
  calc
    covariantJetNormSq (I := I) (M := M) g 2
        (ccOperatorFieldComp (I := I) (M := M) g p r c Φ W) ≤
      (C₀ *
        Real.sqrt (covariantJetNormSq (I := I) (M := M) g 2 Φ) *
        Real.sqrt (covariantJetNormSq (I := I) (M := M) g 2 W)) ^ 2 := by
      simpa only [covariantJetNormSq, Nat.reduceAdd] using h
    _ = C₀ ^ 2 * covariantJetNormSq (I := I) (M := M) g 2 Φ *
        covariantJetNormSq (I := I) (M := M) g 2 W := by
      rw [mul_pow, mul_pow, hsΦ, hsW]

private theorem app_h21_mul
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) (p r c : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (Φ : SmoothCcTensor g r c) (W : SmoothCcTensor g p r),
        covariantJetNormSq (I := I) (M := M) g 1
            (ccOperatorFieldComp (I := I) (M := M) g p r c Φ W) ≤
          C * covariantJetNormSq (I := I) (M := M) g 2 Φ *
            covariantJetNormSq (I := I) (M := M) g 1 W := by
  obtain ⟨C₀, hC₀, happ⟩ :=
    operator_field_composition_h2_h1_to_h1_bound (I := I) (M := M) hDim g p r c
  refine ⟨C₀ ^ 2, sq_nonneg _, ?_⟩
  intro Φ W
  let A : ℝ := Real.sqrt (covariantJetNormSq (I := I) (M := M) g 2 Φ)
  let B : ℝ := Real.sqrt (covariantJetNormSq (I := I) (M := M) g 1 W)
  have hΦ0 : 0 ≤ covariantJetNormSq (I := I) (M := M) g 2 Φ :=
    jet_nonneg (I := I) (M := M) g Φ
  have hW0 : 0 ≤ covariantJetNormSq (I := I) (M := M) g 1 W :=
    jet_nonneg (I := I) (M := M) g W
  have hA : 0 ≤ A := Real.sqrt_nonneg _
  have hB : 0 ≤ B := Real.sqrt_nonneg _
  have hAsq : A ^ 2 = covariantJetNormSq (I := I) (M := M) g 2 Φ := by
    simpa only [A] using Real.sq_sqrt hΦ0
  have hBsq : B ^ 2 = covariantJetNormSq (I := I) (M := M) g 1 W := by
    simpa only [B] using Real.sq_sqrt hW0
  have hnorm := happ Φ W A B hA hB
    (by
      simpa only [covariantJetNormSq, Nat.reduceAdd] using
        (le_of_eq hAsq.symm))
    (by
      simpa only [covariantJetNormSq, Nat.reduceAdd] using
        (le_of_eq hBsq.symm))
  have hsq := pow_le_pow_left₀
    (norm_nonneg
      (⟨ccOperatorFieldComp (I := I) (M := M) g p r c Φ W⟩ :
        SmoothCcTensorH1 g p c))
    hnorm 2
  have hjet :
      covariantJetNormSq (I := I) (M := M) g 1
          (ccOperatorFieldComp (I := I) (M := M) g p r c Φ W) ≤
        (C₀ * A * B) ^ 2 := by
    rw [smooth_cc_tensor_h1_norm_sq_eq_covariant_jet (I := I) (M := M) g p c
      (ccOperatorFieldComp (I := I) (M := M) g p r c Φ W)] at hsq
    simpa only [covariantJetNormSq, Finset.sum_range_succ,
      Finset.sum_range_zero, zero_add, Nat.reduceAdd,
      Nat.add_zero, iteratedCovGrad_zero, iteratedCovGrad_succ] using hsq
  calc
    covariantJetNormSq (I := I) (M := M) g 1
        (ccOperatorFieldComp (I := I) (M := M) g p r c Φ W) ≤
      (C₀ * A * B) ^ 2 := hjet
    _ = C₀ ^ 2 * covariantJetNormSq (I := I) (M := M) g 2 Φ *
        covariantJetNormSq (I := I) (M := M) g 1 W := by
      rw [mul_pow, mul_pow, hAsq, hBsq]

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
private theorem grad_l2_sq
    (g : SmoothRiemannianMetric I M) (r s i : ℕ)
    (S : SmoothCcTensor g r s) :
    ‖iteratedCovGrad (I := I) g r (s + 1) i
        (covGrad (I := I) (M := M) g r s S)‖ ^ 2 =
      ‖iteratedCovGrad (I := I) g r s (i + 1) S‖ ^ 2 := by
  rw [SmoothCcTensor.norm_def,
    tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs,
    SmoothCcTensor.norm_def,
    tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs]
  refine MeasureTheory.integral_congr_ae
    (Filter.Eventually.of_forall fun x => ?_)
  exact riemannianFiberNormSq_iteratedCovGrad_covGrad_comm_rs
    (I := I) (M := M) g r s i S x

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
private theorem grad_h2_le_h3
    (g : SmoothRiemannianMetric I M) {r s : ℕ}
    (S : SmoothCcTensor g r s) :
    covariantJetNormSq (I := I) (M := M) g 2
        (covGrad (I := I) (M := M) g r s S) ≤
      covariantJetNormSq (I := I) (M := M) g 3 S := by
  have h0 := grad_l2_sq (I := I) (M := M) g r s 0 S
  have h1 := grad_l2_sq (I := I) (M := M) g r s 1 S
  have h2 := grad_l2_sq (I := I) (M := M) g r s 2 S
  unfold covariantJetNormSq
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
    Nat.reduceAdd] at h0 h1 h2 ⊢
  rw [h0, h1, h2]
  nlinarith [sq_nonneg ‖S‖]

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
private theorem grad_h1_le_h2
    (g : SmoothRiemannianMetric I M) {r s : ℕ}
    (S : SmoothCcTensor g r s) :
    covariantJetNormSq (I := I) (M := M) g 1
        (covGrad (I := I) (M := M) g r s S) ≤
      covariantJetNormSq (I := I) (M := M) g 2 S := by
  have h0 := grad_l2_sq (I := I) (M := M) g r s 0 S
  have h1 := grad_l2_sq (I := I) (M := M) g r s 1 S
  unfold covariantJetNormSq
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
    Nat.reduceAdd] at h0 h1 ⊢
  rw [h0, h1]
  nlinarith [sq_nonneg ‖S‖]

omit [NeZero (Module.finrank ℝ E)] in
private theorem dom_h2
    (g : SmoothRiemannianMetric I M) {s : ℕ}
    (σ : Equiv.Perm (Fin s)) (S : SmoothCcTensor g 0 s) :
    covariantJetNormSq (I := I) (M := M) g 2
        (domDomCongrSection (I := I) g σ S) =
      covariantJetNormSq (I := I) (M := M) g 2 S := by
  unfold covariantJetNormSq
  apply Finset.sum_congr rfl
  intro q _
  rw [SmoothCcTensor.norm_def,
    tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs,
    SmoothCcTensor.norm_def,
    tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs]
  apply MeasureTheory.integral_congr_ae
  exact Filter.Eventually.of_forall fun x =>
    riemannianFiberNormSq_iteratedCovGrad_domDomCongrSection
      (I := I) (M := M) g σ S q x

omit [NeZero (Module.finrank ℝ E)] in
private theorem dom_h1
    (g : SmoothRiemannianMetric I M) {s : ℕ}
    (σ : Equiv.Perm (Fin s)) (S : SmoothCcTensor g 0 s) :
    covariantJetNormSq (I := I) (M := M) g 1
        (domDomCongrSection (I := I) g σ S) =
      covariantJetNormSq (I := I) (M := M) g 1 S := by
  unfold covariantJetNormSq
  apply Finset.sum_congr rfl
  intro q _
  rw [SmoothCcTensor.norm_def,
    tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs,
    SmoothCcTensor.norm_def,
    tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs]
  apply MeasureTheory.integral_congr_ae
  exact Filter.Eventually.of_forall fun x =>
    riemannianFiberNormSq_iteratedCovGrad_domDomCongrSection
      (I := I) (M := M) g σ S q x

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
omit [I.Boundaryless] in
private theorem connSec_eq_raise
    (g gm : SmoothRiemannianMetric I M) :
    connectionDifferenceSection (I := I) gm g =
      cometricRaiseSlot0Field (I := I) (M := M) g 1
        (domDomCongrSection (I := I) g (finRotate 3)
          (metricLoweredConnectionDifferenceCoefficient (I := I) g gm)) := by
  apply Integral.L2.SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rw [connectionDifferenceSection_toSection, cometricRaiseSlot0Field_toSection]
  apply tensorRSSpace_ext 1 2 x
  intro om
  apply ContinuousMultilinearMap.ext
  intro YZ
  let u : TangentSpace I x := inverseMetricSharpFib (I := I) g x om
  let D : Tensor0SSpace 3 I x :=
    (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 3 I x from
      (domDomCongrSection (I := I) g (finRotate 3)
        (metricLoweredConnectionDifferenceCoefficient (I := I) g gm)).toSection x)
      (unitTensor (I := I) (M := M) x)
  have hL :
      (show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 2 I x from
        connectionDifferenceFib (I := I) gm g x) om YZ =
        g.inner x u (PDE.DeTurck.connectionDifference (I := I) gm g x
          (YZ 0) (YZ 1)) := by
    rw [connectionDifferenceFib_apply_eval]
    rw [show om (fun _ : Fin 1 =>
          PDE.DeTurck.connectionDifference (I := I) gm g x (YZ 0) (YZ 1)) =
        cotangentToDual (I := I) (x := x) om
          (PDE.DeTurck.connectionDifference (I := I) gm g x (YZ 0) (YZ 1)) from
      (cotangentToDual_apply (I := I) om _).symm]
    rw [show cotangentToDual (I := I) (x := x) om
          (PDE.DeTurck.connectionDifference (I := I) gm g x (YZ 0) (YZ 1)) =
        cotangentToDualLinear (I := I) (x := x) om
          (PDE.DeTurck.connectionDifference (I := I) gm g x (YZ 0) (YZ 1)) from rfl]
    rw [← inverseMetricSharpFib_inner (I := I) g x om
      (PDE.DeTurck.connectionDifference (I := I) gm g x (YZ 0) (YZ 1))]
  have hR :
      (show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 2 I x from
        cometricRaiseSlot0Fib (I := I) g 1 x D) om YZ =
        Tensor0SSpace.eval D (Fin.cons u YZ) := by
    rw [cometricRaiseSlot0Fib_clm_apply (I := I) g 1 x D om]
    rw [Tensor0SBundle.interior_product_apply]
    exact (Tensor0SSpace.eval_eq _ _).symm
  have hmid :
      g.inner x u (PDE.DeTurck.connectionDifference (I := I) gm g x
          (YZ 0) (YZ 1)) = Tensor0SSpace.eval D (Fin.cons u YZ) := by
    rw [show Tensor0SSpace.eval D (Fin.cons u YZ) =
      unitModel (I := I) (M := M) g 3
        (domDomCongrSection (I := I) g (finRotate 3)
          (metricLoweredConnectionDifferenceCoefficient (I := I) g gm)) x
        ![tangentSpaceModelContinuousLinearEquiv (I := I) x u,
          tangentSpaceModelContinuousLinearEquiv (I := I) x (YZ 0),
          tangentSpaceModelContinuousLinearEquiv (I := I) x (YZ 1)] from by
      rfl]
    rw [domDomCongrSection_unitModel,
      ContinuousMultilinearMap.domDomCongr_apply]
    rw [show (fun i =>
      (![tangentSpaceModelContinuousLinearEquiv (I := I) x u,
        tangentSpaceModelContinuousLinearEquiv (I := I) x (YZ 0),
        tangentSpaceModelContinuousLinearEquiv (I := I) x (YZ 1)] : Fin 3 → E)
        ((finRotate 3) i)) =
          ![tangentSpaceModelContinuousLinearEquiv (I := I) x (YZ 0),
            tangentSpaceModelContinuousLinearEquiv (I := I) x (YZ 1),
            tangentSpaceModelContinuousLinearEquiv (I := I) x u] from by
      funext i
      fin_cases i <;> simp]
    rw [show
      (![tangentSpaceModelContinuousLinearEquiv (I := I) x (YZ 0),
        tangentSpaceModelContinuousLinearEquiv (I := I) x (YZ 1),
        tangentSpaceModelContinuousLinearEquiv (I := I) x u] : Fin 3 → E) =
        (fun i => tangentSpaceModelContinuousLinearEquiv (I := I) x
          ((![YZ 0, YZ 1, u] : Fin 3 → TangentSpace I x) i)) by
      funext i
      fin_cases i <;> rfl]
    rw [connectionDifferenceLoweredCc_unitModel_apply']
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons]
    exact g.symm x u
      (PDE.DeTurck.connectionDifference (I := I) gm g x (YZ 0) (YZ 1))
  exact hL.trans (hmid.trans hR.symm)

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private theorem dom_sub
    (g : SmoothRiemannianMetric I M) {s : ℕ}
    (σ : Equiv.Perm (Fin s)) (A B : SmoothCcTensor g 0 s) :
    domDomCongrSection (I := I) g σ (A - B) =
      domDomCongrSection (I := I) g σ A -
        domDomCongrSection (I := I) g σ B := by
  apply smoothCcTensor_ext_of_unitModel (I := I) (M := M) g
  intro x
  have hsub : ∀ (P Q : SmoothCcTensor g 0 s),
      unitModel (I := I) (M := M) g s (P - Q) x =
        unitModel (I := I) (M := M) g s P x -
          unitModel (I := I) (M := M) g s Q x := by
    intro P Q
    simp only [unitModel]
    rw [SmoothCcTensor.toSection_sub]
    rfl
  rw [domDomCongrSection_unitModel, hsub A B]
  rw [hsub
    (domDomCongrSection (I := I) g σ A)
    (domDomCongrSection (I := I) g σ B)]
  rw [domDomCongrSection_unitModel, domDomCongrSection_unitModel]
  apply ContinuousMultilinearMap.ext
  intro v
  simp only [sub_apply,
    ContinuousMultilinearMap.domDomCongr_apply]

omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] [SigmaCompactSpace M] in
omit [I.Boundaryless] in
private theorem raise_sub
    (g : SmoothRiemannianMetric I M) (s : ℕ)
    (A B : SmoothCcTensor g 0 (s + 2)) :
    cometricRaiseSlot0Field (I := I) (M := M) g s (A - B) =
      cometricRaiseSlot0Field (I := I) (M := M) g s A -
        cometricRaiseSlot0Field (I := I) (M := M) g s B := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rw [show
      (cometricRaiseSlot0Field (I := I) (M := M) g s A -
        cometricRaiseSlot0Field (I := I) (M := M) g s B).toSection x =
      (cometricRaiseSlot0Field (I := I) (M := M) g s A).toSection x -
        (cometricRaiseSlot0Field (I := I) (M := M) g s B).toSection x from by
    rw [SmoothCcTensor.toSection_sub]
    rfl]
  rw [cometricRaiseSlot0Field_toSection,
    cometricRaiseSlot0Field_toSection,
    cometricRaiseSlot0Field_toSection]
  rw [show
      (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 2) I x from
        (A - B).toSection x) (unitTensor (I := I) (M := M) x) =
      (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 2) I x from
        A.toSection x) (unitTensor (I := I) (M := M) x) -
      (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 2) I x from
        B.toSection x) (unitTensor (I := I) (M := M) x) from by
    rw [SmoothCcTensor.toSection_sub]
    rfl]
  exact ContinuousLinearMap.map_sub _ _ _

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
omit [I.Boundaryless] in
private theorem connSec_sub_eq
    (g gT gU : SmoothRiemannianMetric I M) :
    connectionDifferenceSection (I := I) gT g -
        connectionDifferenceSection (I := I) gU g =
      cometricRaiseSlot0Field (I := I) (M := M) g 1
        (domDomCongrSection (I := I) g (finRotate 3)
          (metricLoweredConnectionDifferenceCoefficient (I := I) g gT -
            metricLoweredConnectionDifferenceCoefficient (I := I) g gU)) := by
  rw [connSec_eq_raise (I := I) (M := M) g gT,
    connSec_eq_raise (I := I) (M := M) g gU,
    ← raise_sub (I := I) (M := M) g,
    ← dom_sub (I := I) (M := M) g]

omit [NeZero (Module.finrank ℝ E)] in
private theorem raisePerm_h2
    (g : SmoothRiemannianMetric I M)
    (S : SmoothCcTensor g 0 3) :
    covariantJetNormSq (I := I) (M := M) g 2
        (cometricRaiseSlot0Field (I := I) (M := M) g 1
          (domDomCongrSection (I := I) g (finRotate 3) S)) =
      covariantJetNormSq (I := I) (M := M) g 2 S := by
  calc
    covariantJetNormSq (I := I) (M := M) g 2
        (cometricRaiseSlot0Field (I := I) (M := M) g 1
          (domDomCongrSection (I := I) g (finRotate 3) S)) =
      covariantJetNormSq (I := I) (M := M) g 2
        (domDomCongrSection (I := I) g (finRotate 3) S) := by
          unfold covariantJetNormSq
          apply Finset.sum_congr rfl
          intro q _
          rw [norm_iteratedCovGrad_cometricRaiseSlot0Field_eq
            (I := I) (M := M) g 1
            (domDomCongrSection (I := I) g (finRotate 3) S) q]
    _ = covariantJetNormSq (I := I) (M := M) g 2 S :=
      dom_h2 (I := I) (M := M) g (finRotate 3) S

omit [NeZero (Module.finrank ℝ E)] in
private theorem connSec_h2_eq
    (g gT gU : SmoothRiemannianMetric I M) :
    covariantJetNormSq (I := I) (M := M) g 2
        (connectionDifferenceSection (I := I) gT g -
          connectionDifferenceSection (I := I) gU g) =
      covariantJetNormSq (I := I) (M := M) g 2
        (metricLoweredConnectionDifferenceCoefficient (I := I) g gT -
          metricLoweredConnectionDifferenceCoefficient (I := I) g gU) := by
  rw [connSec_sub_eq (I := I) (M := M) g gT gU]
  exact raisePerm_h2 (I := I) (M := M) g _

omit [NeZero (Module.finrank ℝ E)] in
private theorem raisePerm_h1
    (g : SmoothRiemannianMetric I M)
    (S : SmoothCcTensor g 0 3) :
    covariantJetNormSq (I := I) (M := M) g 1
        (cometricRaiseSlot0Field (I := I) (M := M) g 1
          (domDomCongrSection (I := I) g (finRotate 3) S)) =
      covariantJetNormSq (I := I) (M := M) g 1 S := by
  calc
    covariantJetNormSq (I := I) (M := M) g 1
        (cometricRaiseSlot0Field (I := I) (M := M) g 1
          (domDomCongrSection (I := I) g (finRotate 3) S)) =
      covariantJetNormSq (I := I) (M := M) g 1
        (domDomCongrSection (I := I) g (finRotate 3) S) := by
          unfold covariantJetNormSq
          apply Finset.sum_congr rfl
          intro q _
          rw [norm_iteratedCovGrad_cometricRaiseSlot0Field_eq
            (I := I) (M := M) g 1
            (domDomCongrSection (I := I) g (finRotate 3) S) q]
    _ = covariantJetNormSq (I := I) (M := M) g 1 S :=
      dom_h1 (I := I) (M := M) g (finRotate 3) S

omit [NeZero (Module.finrank ℝ E)] in
private theorem connSec_h1_eq
    (g gT gU : SmoothRiemannianMetric I M) :
    covariantJetNormSq (I := I) (M := M) g 1
        (connectionDifferenceSection (I := I) gT g -
          connectionDifferenceSection (I := I) gU g) =
      covariantJetNormSq (I := I) (M := M) g 1
        (metricLoweredConnectionDifferenceCoefficient (I := I) g gT -
          metricLoweredConnectionDifferenceCoefficient (I := I) g gU) := by
  rw [connSec_sub_eq (I := I) (M := M) g gT gU]
  exact raisePerm_h1 (I := I) (M := M) g _

private theorem slotExt_norm_le
    (g : SmoothRiemannianMetric I M) (r s i : ℕ)
    (Φ : SmoothCcTensor g r s) :
    ‖iteratedCovGrad (I := I) g (r + 1) (s + 1) i
        (slotExtend (I := I) (M := M) g r s Φ)‖ ≤
      Real.sqrt (Module.finrank ℝ E) *
        ‖iteratedCovGrad (I := I) g r s i Φ‖ := by
  classical
  let F : M → ℝ := fun x => (Module.finrank ℝ E : ℝ) *
    riemannianFiberNormSq (I := I) (M := M) g r (s + i) x
      ((iteratedCovGrad (I := I) g r s i Φ).toSection x)
  have hFint : Integrable F
      (riemannianVolumeMeasure (I := I) (M := M) g) := by
    dsimp only [F]
    exact (integrable_riemannianFiberNormSq_toSection
      (I := I) (M := M) g r (s + i)
      (iteratedCovGrad (I := I) g r s i Φ)).const_mul _
  have hsq := normSq_le_integral_of_pointwise_fiberNormSq_le_rs
    (I := I) (M := M) g (r + 1) ((s + 1) + i)
    (iteratedCovGrad (I := I) g (r + 1) (s + 1) i
      (slotExtend (I := I) (M := M) g r s Φ))
    F hFint (fun x => riemannianFiberNormSq_iteratedCovGrad_slotExtend_le
      (I := I) (M := M) g r s Φ i x)
  have hint :
      (∫ x,
        riemannianFiberNormSq (I := I) (M := M) g r (s + i) x
          ((iteratedCovGrad (I := I) g r s i Φ).toSection x)
        ∂(riemannianVolumeMeasure (I := I) (M := M) g)) =
        ‖iteratedCovGrad (I := I) g r s i Φ‖ ^ 2 := by
    rw [SmoothCcTensor.norm_def,
      tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs
        (I := I) (M := M) g r (s + i)]
  dsimp only [F] at hsq
  rw [MeasureTheory.integral_const_mul, hint] at hsq
  refine le_of_sq_le_sq ?_
    (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))
  rw [mul_pow, Real.sq_sqrt (by positivity :
    (0 : ℝ) ≤ (Module.finrank ℝ E : ℝ))]
  exact hsq

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] [SigmaCompactSpace M] in
private theorem reindex_sub_c1
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (A B : SmoothCcTensor g r s) (ρ : Equiv.Perm (Fin r)) :
    reindexCoeffGen (I := I) (M := M) g r s (A - B) ρ =
      reindexCoeffGen (I := I) (M := M) g r s A ρ -
        reindexCoeffGen (I := I) (M := M) g r s B ρ := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rw [SmoothCcTensor.toSection_sub, ContMDiffSection.coe_sub, Pi.sub_apply,
    reindexCoeffGen_toSection, reindexCoeffGen_toSection,
    reindexCoeffGen_toSection, SmoothCcTensor.toSection_sub,
    ContMDiffSection.coe_sub, Pi.sub_apply]
  apply ContinuousLinearMap.ext
  intro D
  rw [sub_apply, reindexCoeffFibGen_apply,
    reindexCoeffFibGen_apply, reindexCoeffFibGen_apply,
    sub_apply]

private theorem insert_h2
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M)
    (S : SmoothCcTensor g 1 2) :
    covariantJetNormSq (I := I) (M := M) g 2
        (reindexCoeffGen (I := I) (M := M) g 3 4
          (slotExtend (I := I) (M := M) g 2 3
            (slotExtend (I := I) (M := M) g 1 2 S))
          coreInPerm201) ≤
      9 * covariantJetNormSq (I := I) (M := M) g 2 S := by
  classical
  have hper : ∀ i : ℕ,
      ‖iteratedCovGrad (I := I) g 3 4 i
          (reindexCoeffGen (I := I) (M := M) g 3 4
            (slotExtend (I := I) (M := M) g 2 3
              (slotExtend (I := I) (M := M) g 1 2 S))
            coreInPerm201)‖ ≤
        3 * ‖iteratedCovGrad (I := I) g 1 2 i S‖ := by
    intro i
    rw [iteratedCovGrad_reindexCoeffGen (I := I) (M := M),
      norm_reindexCoeffGen_eq (I := I) (M := M)]
    calc
      _ ≤ Real.sqrt (Module.finrank ℝ E) *
          ‖iteratedCovGrad (I := I) g 2 3 i
            (slotExtend (I := I) (M := M) g 1 2 S)‖ :=
        slotExt_norm_le (I := I) (M := M) g 2 3 i _
      _ ≤ Real.sqrt (Module.finrank ℝ E) *
          (Real.sqrt (Module.finrank ℝ E) *
            ‖iteratedCovGrad (I := I) g 1 2 i S‖) :=
        mul_le_mul_of_nonneg_left
          (slotExt_norm_le (I := I) (M := M) g 1 2 i S)
          (Real.sqrt_nonneg _)
      _ = 3 * ‖iteratedCovGrad (I := I) g 1 2 i S‖ := by
        rw [hDim]
        have hs : Real.sqrt (3 : ℝ) ^ 2 = 3 :=
          Real.sq_sqrt (by norm_num)
        calc
          Real.sqrt (3 : ℝ) *
              (Real.sqrt (3 : ℝ) *
                ‖iteratedCovGrad (I := I) g 1 2 i S‖) =
              Real.sqrt (3 : ℝ) ^ 2 *
                ‖iteratedCovGrad (I := I) g 1 2 i S‖ := by ring
          _ = 3 * ‖iteratedCovGrad (I := I) g 1 2 i S‖ := by rw [hs]
  have hsq : ∀ i : ℕ,
      ‖iteratedCovGrad (I := I) g 3 4 i
          (reindexCoeffGen (I := I) (M := M) g 3 4
            (slotExtend (I := I) (M := M) g 2 3
              (slotExtend (I := I) (M := M) g 1 2 S))
            coreInPerm201)‖ ^ 2 ≤
        9 * ‖iteratedCovGrad (I := I) g 1 2 i S‖ ^ 2 := by
    intro i
    have h := pow_le_pow_left₀ (norm_nonneg _) (hper i) 2
    nlinarith
  unfold covariantJetNormSq
  calc
    (∑ i ∈ Finset.range (2 + 1),
        ‖iteratedCovGrad (I := I) g 3 4 i
          (reindexCoeffGen (I := I) (M := M) g 3 4
            (slotExtend (I := I) (M := M) g 2 3
              (slotExtend (I := I) (M := M) g 1 2 S))
            coreInPerm201)‖ ^ 2) ≤
      ∑ i ∈ Finset.range (2 + 1),
        9 * ‖iteratedCovGrad (I := I) g 1 2 i S‖ ^ 2 :=
      Finset.sum_le_sum fun i _ => hsq i
    _ = 9 * (∑ i ∈ Finset.range (2 + 1),
        ‖iteratedCovGrad (I := I) g 1 2 i S‖ ^ 2) := by
      rw [Finset.mul_sum]

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [SigmaCompactSpace M] in
private theorem connIns_sub_eq
    (g gT gU : SmoothRiemannianMetric I M) :
    connectionDifferenceContravariantInsertionField (I := I) g gT -
        connectionDifferenceContravariantInsertionField (I := I) g gU =
      reindexCoeffGen (I := I) (M := M) g 3 4
        (slotExtend (I := I) (M := M) g 2 3
          (slotExtend (I := I) (M := M) g 1 2
            (connectionDifferenceSection (I := I) gT g -
              connectionDifferenceSection (I := I) gU g)))
        coreInPerm201 := by
  rw [connectionDifferenceContravariantInsertionField_eq_reindex_slotExtend_two
      (I := I) (M := M) g gT,
    connectionDifferenceContravariantInsertionField_eq_reindex_slotExtend_two
      (I := I) (M := M) g gU,
    ← reindex_sub_c1 (I := I) (M := M) g,
    ← slotExtend_sub, ← slotExtend_sub]
  rw [show connectionDifferenceContrInsertionReindexPerm = coreInPerm201 from rfl]

private def kO0312 : Equiv.Perm (Fin 4) :=
  ⟨![0, 3, 1, 2], ![0, 2, 3, 1], by decide, by decide⟩

private def kO0213 : Equiv.Perm (Fin 4) :=
  ⟨![0, 2, 1, 3], ![0, 2, 1, 3], by decide, by decide⟩

private def kO2301 : Equiv.Perm (Fin 4) :=
  ⟨![2, 3, 0, 1], ![2, 3, 0, 1], by decide, by decide⟩

private def kO1302 : Equiv.Perm (Fin 4) :=
  ⟨![1, 3, 0, 2], ![2, 0, 3, 1], by decide, by decide⟩

private def kO1203 : Equiv.Perm (Fin 4) :=
  ⟨![1, 2, 0, 3], ![2, 0, 1, 3], by decide, by decide⟩

private def kI102 : Equiv.Perm (Fin 3) :=
  ⟨![1, 0, 2], ![1, 0, 2], by decide, by decide⟩

private def kI120 : Equiv.Perm (Fin 3) :=
  ⟨![1, 2, 0], ![2, 0, 1], by decide, by decide⟩

private noncomputable def kerOfIns
    (g : SmoothRiemannianMetric I M)
    (Q : SmoothCcTensor g 3 4) : SmoothCcTensor g 3 4 :=
  -(reindexCoeffGen (I := I) (M := M) g 3 4
        (ccOperatorFieldComp (I := I) (M := M) g 3 4 4
          (permCoeff (I := I) (M := M) g kO0312) Q) kI102
    + reindexCoeffGen (I := I) (M := M) g 3 4
        (ccOperatorFieldComp (I := I) (M := M) g 3 4 4
          (permCoeff (I := I) (M := M) g kO0213) Q) kI120
    + ccOperatorFieldComp (I := I) (M := M) g 3 4 4
        (permCoeff (I := I) (M := M) g kO2301) Q
    + reindexCoeffGen (I := I) (M := M) g 3 4
        (ccOperatorFieldComp (I := I) (M := M) g 3 4 4
          (permCoeff (I := I) (M := M) g kO1302) Q) kI102
    + reindexCoeffGen (I := I) (M := M) g 3 4
        (ccOperatorFieldComp (I := I) (M := M) g 3 4 4
          (permCoeff (I := I) (M := M) g kO1203) Q) kI120)

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [SigmaCompactSpace M] in
private theorem ricciKer_eq
    (g gm : SmoothRiemannianMetric I M) :
    linearizedRicciConnectionDifferenceOrder1KernelField (I := I) g gm =
      kerOfIns (I := I) (M := M) g
        (connectionDifferenceContravariantInsertionField (I := I) g gm) := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rfl

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M]
  [SigmaCompactSpace M] in
private theorem kerOfIns_sub
    (g : SmoothRiemannianMetric I M)
    (A B : SmoothCcTensor g 3 4) :
    kerOfIns (I := I) (M := M) g (A - B) =
      kerOfIns (I := I) (M := M) g A -
        kerOfIns (I := I) (M := M) g B := by
  simp only [kerOfIns, operatorFieldComposition_sub_right,
    reindex_sub_c1 (I := I) (M := M)]
  module

omit [SigmaCompactSpace M] in
private theorem outPerm_riemannianFiberNormSq
    (g : SmoothRiemannianMetric I M)
    (σ : Equiv.Perm (Fin 4)) (Q : SmoothCcTensor g 3 4)
    (q : ℕ) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g 3 (4 + q) x
        ((iteratedCovGrad (I := I) g 3 4 q
          (ccOperatorFieldComp (I := I) (M := M) g 3 4 4
            (permCoeff (I := I) (M := M) g σ) Q)).toSection x) =
      riemannianFiberNormSq (I := I) (M := M) g 3 (4 + q) x
        ((iteratedCovGrad (I := I) g 3 4 q Q).toSection x) := by
  refine DifferentialGeometry.Analysis.Spectral.riemannianFiberNormSq_iteratedCovGrad_rs_eq_of_section_domDomCongr
    (I := I) (M := M) g 3 4 σ Q
    (ccOperatorFieldComp (I := I) (M := M) g 3 4 4
      (permCoeff (I := I) (M := M) g σ) Q)
    (fun y d => ?_) q x
  have hy :
      (show Tensor0SSpace 3 I y →L[ℝ] Tensor0SSpace 4 I y from
        (ccOperatorFieldComp (I := I) (M := M) g 3 4 4
          (permCoeff (I := I) (M := M) g σ) Q).toSection y) d =
        slotPermCLM (I := I) σ y
          ((show Tensor0SSpace 3 I y →L[ℝ] Tensor0SSpace 4 I y from
            Q.toSection y) d) := rfl
  rw [hy, slotPermCLM_apply, Tensor0SSpace.toModel_ofModel]

private theorem outPerm_norm
    (g : SmoothRiemannianMetric I M)
    (σ : Equiv.Perm (Fin 4)) (Q : SmoothCcTensor g 3 4)
    (q : ℕ) :
    ‖iteratedCovGrad (I := I) g 3 4 q
        (ccOperatorFieldComp (I := I) (M := M) g 3 4 4
          (permCoeff (I := I) (M := M) g σ) Q)‖ =
      ‖iteratedCovGrad (I := I) g 3 4 q Q‖ := by
  refine raisedKoszul_norm_eq_of_sq_eq (norm_nonneg _) (norm_nonneg _) ?_
  rw [SmoothCcTensor.norm_def, SmoothCcTensor.norm_def,
    tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs,
    tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs]
  exact MeasureTheory.integral_congr_ae
    (Filter.Eventually.of_forall fun x =>
      outPerm_riemannianFiberNormSq (I := I) (M := M) g σ Q q x)

private theorem fullPerm_norm
    (g : SmoothRiemannianMetric I M)
    (σ : Equiv.Perm (Fin 4)) (ρ : Equiv.Perm (Fin 3))
    (Q : SmoothCcTensor g 3 4) (q : ℕ) :
    ‖iteratedCovGrad (I := I) g 3 4 q
        (reindexCoeffGen (I := I) (M := M) g 3 4
          (ccOperatorFieldComp (I := I) (M := M) g 3 4 4
            (permCoeff (I := I) (M := M) g σ) Q) ρ)‖ =
      ‖iteratedCovGrad (I := I) g 3 4 q Q‖ := by
  calc
    _ = ‖iteratedCovGrad (I := I) g 3 4 q
        (ccOperatorFieldComp (I := I) (M := M) g 3 4 4
          (permCoeff (I := I) (M := M) g σ) Q)‖ := by
      rw [iteratedCovGrad_reindexCoeffGen (I := I) (M := M),
        norm_reindexCoeffGen_eq (I := I) (M := M)]
    _ = _ := outPerm_norm (I := I) (M := M) g σ Q q

private theorem norm_five_le
    {V : Type*} [SeminormedAddCommGroup V]
    {a b c d e : V} {n : ℝ}
    (ha : ‖a‖ = n) (hb : ‖b‖ = n) (hc : ‖c‖ = n)
    (hd : ‖d‖ = n) (he : ‖e‖ = n) :
    ‖a + b + c + d + e‖ ≤ 5 * n := by
  have h1 := norm_add_le (a + b + c + d) e
  have h2 := norm_add_le (a + b + c) d
  have h3 := norm_add_le (a + b) c
  have h4 := norm_add_le a b
  linarith

private theorem kerOfIns_h2
    (g : SmoothRiemannianMetric I M)
    (Q : SmoothCcTensor g 3 4) :
    covariantJetNormSq (I := I) (M := M) g 2
        (kerOfIns (I := I) (M := M) g Q) ≤
      25 * covariantJetNormSq (I := I) (M := M) g 2 Q := by
  classical
  have hper : ∀ i : ℕ,
      ‖iteratedCovGrad (I := I) g 3 4 i
          (kerOfIns (I := I) (M := M) g Q)‖ ≤
        5 * ‖iteratedCovGrad (I := I) g 3 4 i Q‖ := by
    intro i
    simp only [kerOfIns, iteratedCovGrad_neg, norm_neg,
      iteratedCovGrad_add]
    exact norm_five_le
      (fullPerm_norm (I := I) (M := M) g kO0312 kI102 Q i)
      (fullPerm_norm (I := I) (M := M) g kO0213 kI120 Q i)
      (outPerm_norm (I := I) (M := M) g kO2301 Q i)
      (fullPerm_norm (I := I) (M := M) g kO1302 kI102 Q i)
      (fullPerm_norm (I := I) (M := M) g kO1203 kI120 Q i)
  have hsq : ∀ i : ℕ,
      ‖iteratedCovGrad (I := I) g 3 4 i
          (kerOfIns (I := I) (M := M) g Q)‖ ^ 2 ≤
        25 * ‖iteratedCovGrad (I := I) g 3 4 i Q‖ ^ 2 := by
    intro i
    have h := pow_le_pow_left₀ (norm_nonneg _) (hper i) 2
    nlinarith
  unfold covariantJetNormSq
  calc
    (∑ i ∈ Finset.range (2 + 1),
        ‖iteratedCovGrad (I := I) g 3 4 i
          (kerOfIns (I := I) (M := M) g Q)‖ ^ 2) ≤
      ∑ i ∈ Finset.range (2 + 1),
        25 * ‖iteratedCovGrad (I := I) g 3 4 i Q‖ ^ 2 :=
      Finset.sum_le_sum fun i _ => hsq i
    _ = 25 * (∑ i ∈ Finset.range (2 + 1),
        ‖iteratedCovGrad (I := I) g 3 4 i Q‖ ^ 2) := by
      rw [Finset.mul_sum]

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [SigmaCompactSpace M] in
private theorem ricciKer_sub_eq
    (g gT gU : SmoothRiemannianMetric I M) :
    linearizedRicciConnectionDifferenceOrder1KernelField (I := I) g gT -
        linearizedRicciConnectionDifferenceOrder1KernelField (I := I) g gU =
      kerOfIns (I := I) (M := M) g
        (connectionDifferenceContravariantInsertionField (I := I) g gT -
          connectionDifferenceContravariantInsertionField (I := I) g gU) := by
  rw [ricciKer_eq (I := I) (M := M) g gT,
    ricciKer_eq (I := I) (M := M) g gU,
    ← kerOfIns_sub (I := I) (M := M) g]

omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] [SigmaCompactSpace M] in
omit [I.Boundaryless] in
private theorem sharp_eq_slot0
    (g gm : SmoothRiemannianMetric I M) :
    sharpFlatEndoCc (I := I) g gm =
      endoSlotZeroCcTensor (I := I) (M := M) g 0
        (metricComparisonEndomorphismField (I := I) (M := M) g gm) := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  apply tensorRSSpace_ext 1 1 x
  intro om
  apply cotangentToDualLinear_injective (I := I) (x := x)
  apply LinearMap.ext
  intro w
  rw [cotangentToDualLinear_apply, cotangentToDualLinear_apply]
  rw [show (show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 1 I x from
        (endoSlotZeroCcTensor (I := I) (M := M) g 0
          (metricComparisonEndomorphismField (I := I) (M := M) g gm)).toSection x) om =
      slotInsertEndoFib (I := I) (M := M) 1 0 x
        (metricComparisonEndomorphism (I := I) g gm x) om from rfl]
  rw [cotangentToDual_slotInsertEndoFib' (I := I) (M := M) x
    (metricComparisonEndomorphism (I := I) g gm x) om w]
  rw [show (show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 1 I x from
        (sharpFlatEndoCc (I := I) g gm).toSection x) om =
      g0FlatCLM (I := I) g x
        (inverseMetricSharpFib (I := I) gm x om) from rfl]
  rw [cotangentToDual_g0FlatCLM]
  rw [show cotangentToDual (I := I) om
      (metricComparisonEndomorphism (I := I) g gm x w) =
      gm.inner x (inverseMetricSharpFib (I := I) gm x om)
        (metricComparisonEndomorphism (I := I) g gm x w) from by
    rw [← cotangentToDualLinear_apply]
    exact (inverseMetricSharpFib_inner (I := I) gm x om
      (metricComparisonEndomorphism (I := I) g gm x w)).symm]
  rw [show metricComparisonEndomorphism (I := I) g gm x w =
      inverseMetricSharpFib (I := I) gm x
        (g0FlatCLM (I := I) g x w) by
    rw [metricComparisonEndomorphism_apply]]
  rw [gm.symm x (inverseMetricSharpFib (I := I) gm x om)
    (inverseMetricSharpFib (I := I) gm x
      (g0FlatCLM (I := I) g x w))]
  rw [inverseMetricSharpFib_inner (I := I) gm x
    (g0FlatCLM (I := I) g x w)
    (inverseMetricSharpFib (I := I) gm x om)]
  rw [cotangentToDualLinear_apply, cotangentToDual_g0FlatCLM]
  rw [g.symm x w (inverseMetricSharpFib (I := I) gm x om)]

theorem sharp_h2_low
    (g : SmoothRiemannianMetric I M)
    {δ₀ : ℝ} (hδ₀0 : 0 ≤ δ₀) (hδ₀ : δ₀ < 1) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ (gm : SmoothRiemannianMetric I M)
        (P : SmoothCcTensor g 0 2)
        (_hP : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g P x u v =
            ccTensorBilin (I := I) g P x v u)
        (_htie : ∀ (x : M) (u v : TangentSpace I x),
          gm.inner x u v =
            g.inner x u v + ccTensorBilinSymm (I := I) g P x u v)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀) (_hδ0 : 0 ≤ δ)
        (_hδ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g P) δ),
      covariantJetNormSq (I := I) (M := M) g 2
          (sharpFlatEndoCc (I := I) g gm) ≤
        K * (1 + covariantJetNormSq (I := I) (M := M) g 2 P) := by
  classical
  let Λ₀ : ℝ := (Module.finrank ℝ E : ℝ) * δ₀
  have hΛ₀0 : 0 ≤ Λ₀ :=
    mul_nonneg (Nat.cast_nonneg _) hδ₀0
  obtain ⟨Λ, Flow, hΛ, hFlow0, hFlow⟩ :=
    sharpFlatEndoCc_lowOrder_jetL2_radiusFree
      (I := I) (M := M) g
        (2 * Module.finrank ℝ E + 10) hδ₀ hΛ₀0
  refine ⟨Flow 2, hFlow0 2, ?_⟩
  intro gm P hP htie δ hδ_le hδ0 hδ
  have hsymm : ccTensor02Symm (I := I) (M := M) g P = P :=
    symm_eq_self (I := I) (M := M) g P hP
  have hsup : ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g 0 2 x
          (P.toSection x) ≤ Λ₀ ^ 2 := by
    intro x
    rw [← hsymm]
    exact riemannianFiberNormSq_symmS_zero_le_fibreSmall
      (I := I) (M := M) g hδ₀0 P hδ_le hδ0 hδ x
  simpa only [covariantJetNormSq, Nat.reduceAdd] using
    (hFlow gm P htie hδ_le hδ0 hδ hsup).2 2 (by omega)

private theorem endo_slot_l2
    (g : SmoothRiemannianMetric I M) (s i : ℕ)
    (Λ : ContMDiffSection I (E →L[ℝ] E) ∞
      (fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x)) :
    ‖iteratedCovGrad (I := I) g (s + 1) (s + 1) i
        (endoSlotZeroCcTensor (I := I) (M := M) g s Λ)‖ ^ 2 ≤
      (Module.finrank ℝ E : ℝ) ^ s *
        ‖iteratedCovGrad (I := I) g 1 1 i
          (endoSlotZeroCcTensor (I := I) (M := M) g 0 Λ)‖ ^ 2 := by
  let F : M → ℝ := fun x => (Module.finrank ℝ E : ℝ) ^ s *
    riemannianFiberNormSq (I := I) (M := M) g 1 (1 + i) x
      ((iteratedCovGrad (I := I) g 1 1 i
        (endoSlotZeroCcTensor (I := I) (M := M) g 0 Λ)).toSection x)
  have hF : MeasureTheory.Integrable F
      (riemannianVolumeMeasure (I := I) (M := M) g) := by
    dsimp only [F]
    exact (integrable_riemannianFiberNormSq_toSection
      (I := I) (M := M) g 1 (1 + i)
      (iteratedCovGrad (I := I) g 1 1 i
        (endoSlotZeroCcTensor (I := I) (M := M) g 0 Λ))).const_mul _
  have hsq := normSq_le_integral_of_pointwise_fiberNormSq_le_rs
    (I := I) (M := M) g (s + 1) ((s + 1) + i)
    (iteratedCovGrad (I := I) g (s + 1) (s + 1) i
      (endoSlotZeroCcTensor (I := I) (M := M) g s Λ))
    F hF (fun x =>
      riemannianFiberNormSq_iteratedCovGrad_slotInsertEndoCc_le_endo
        (I := I) (M := M) g s Λ i x)
  have hint :
      (∫ x, riemannianFiberNormSq (I := I) (M := M) g 1 (1 + i) x
          ((iteratedCovGrad (I := I) g 1 1 i
            (endoSlotZeroCcTensor (I := I) (M := M) g 0 Λ)).toSection x)
        ∂(riemannianVolumeMeasure (I := I) (M := M) g)) =
        ‖iteratedCovGrad (I := I) g 1 1 i
          (endoSlotZeroCcTensor (I := I) (M := M) g 0 Λ)‖ ^ 2 := by
    rw [SmoothCcTensor.norm_def,
      tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs]
  dsimp only [F] at hsq
  rw [MeasureTheory.integral_const_mul, hint] at hsq
  exact hsq

private theorem endo_slot_h2
    (g : SmoothRiemannianMetric I M) (s : ℕ)
    (Λ : ContMDiffSection I (E →L[ℝ] E) ∞
      (fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x)) :
    covariantJetNormSq (I := I) (M := M) g 2
        (endoSlotZeroCcTensor (I := I) (M := M) g s Λ) ≤
      (Module.finrank ℝ E : ℝ) ^ s *
        covariantJetNormSq (I := I) (M := M) g 2
          (endoSlotZeroCcTensor (I := I) (M := M) g 0 Λ) := by
  unfold covariantJetNormSq
  calc
    ∑ i ∈ Finset.range 3,
        ‖iteratedCovGrad (I := I) g (s + 1) (s + 1) i
          (endoSlotZeroCcTensor (I := I) (M := M) g s Λ)‖ ^ 2 ≤
      ∑ i ∈ Finset.range 3, (Module.finrank ℝ E : ℝ) ^ s *
        ‖iteratedCovGrad (I := I) g 1 1 i
          (endoSlotZeroCcTensor (I := I) (M := M) g 0 Λ)‖ ^ 2 :=
      Finset.sum_le_sum fun i _ =>
        endo_slot_l2 (I := I) (M := M) g s i Λ
    _ = (Module.finrank ℝ E : ℝ) ^ s *
        ∑ i ∈ Finset.range 3,
          ‖iteratedCovGrad (I := I) g 1 1 i
            (endoSlotZeroCcTensor (I := I) (M := M) g 0 Λ)‖ ^ 2 := by
      rw [Finset.mul_sum]

private theorem full_slot_h2
    (g : SmoothRiemannianMetric I M)
    {δ₀ : ℝ} (hδ₀0 : 0 ≤ δ₀) (hδ₀ : δ₀ < 1) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ (gm : SmoothRiemannianMetric I M)
        (P : SmoothCcTensor g 0 2)
        (_hP : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g P x u v =
            ccTensorBilin (I := I) g P x v u)
        (_htie : ∀ (x : M) (u v : TangentSpace I x),
          gm.inner x u v =
            g.inner x u v + ccTensorBilinSymm (I := I) g P x u v)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀) (_hδ0 : 0 ≤ δ)
        (_hδ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g P) δ),
      covariantJetNormSq (I := I) (M := M) g 2
          (fullSlot3 (I := I) (M := M) g gm) ≤
        K * (1 + covariantJetNormSq (I := I) (M := M) g 2 P) := by
  obtain ⟨K₀, hK₀, hsharp⟩ :=
    sharp_h2_low (I := I) (M := M) g hδ₀0 hδ₀
  let fr : ℝ := Module.finrank ℝ E
  let K : ℝ := fr ^ 2 * K₀
  have hfr : 0 ≤ fr := Nat.cast_nonneg _
  have hK : 0 ≤ K := mul_nonneg (pow_nonneg hfr 2) hK₀
  refine ⟨K, hK, ?_⟩
  intro gm P hP htie δ hδ_le hδ0 hδ
  calc
    covariantJetNormSq (I := I) (M := M) g 2
        (fullSlot3 (I := I) (M := M) g gm) ≤
      fr ^ 2 * covariantJetNormSq (I := I) (M := M) g 2
        (endoSlotZeroCcTensor (I := I) (M := M) g 0
          (metricComparisonEndomorphismField (I := I) (M := M) g gm)) := by
      simpa only [fullSlot3, fr] using
        endo_slot_h2 (I := I) (M := M) g 2
          (metricComparisonEndomorphismField (I := I) (M := M) g gm)
    _ = fr ^ 2 * covariantJetNormSq (I := I) (M := M) g 2
        (sharpFlatEndoCc (I := I) g gm) := by
      rw [sharp_eq_slot0 (I := I) (M := M) g gm]
    _ ≤ fr ^ 2 * (K₀ *
        (1 + covariantJetNormSq (I := I) (M := M) g 2 P)) :=
      mul_le_mul_of_nonneg_left
        (hsharp gm P hP htie hδ_le hδ0 hδ) (pow_nonneg hfr 2)
    _ = K * (1 + covariantJetNormSq (I := I) (M := M) g 2 P) := by
      simp only [K]
      ring

private theorem raiseLast_h2
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (gm : SmoothRiemannianMetric I M)
        (S : SmoothCcTensor g 0 3),
      covariantJetNormSq (I := I) (M := M) g 2
          (raiseLast (I := I) (M := M) g gm S) ≤
        C * covariantJetNormSq (I := I) (M := M) g 2
            (fullSlot3 (I := I) (M := M) g gm) *
          covariantJetNormSq (I := I) (M := M) g 2 S := by
  obtain ⟨C, hC, happ⟩ :=
    app_h2_mul (I := I) (M := M) hDim g 0 3 3
  refine ⟨C, hC, ?_⟩
  intro gm S
  calc
    covariantJetNormSq (I := I) (M := M) g 2
        (raiseLast (I := I) (M := M) g gm S) =
      covariantJetNormSq (I := I) (M := M) g 2
        (operatorFieldApply (I := I) (M := M) g 3 3
          (fullSlot3 (I := I) (M := M) g gm)
          (domDomCongrSection (I := I) g (finRotate 3) S)) := by
      exact dom_h2 (I := I) (M := M) g connectionDifferenceLowOrderPermutation
        (operatorFieldApply (I := I) (M := M) g 3 3
          (fullSlot3 (I := I) (M := M) g gm)
          (domDomCongrSection (I := I) g (finRotate 3) S))
    _ ≤ C * covariantJetNormSq (I := I) (M := M) g 2
          (fullSlot3 (I := I) (M := M) g gm) *
        covariantJetNormSq (I := I) (M := M) g 2
          (domDomCongrSection (I := I) g (finRotate 3) S) := by
      simpa only [operatorFieldComposition_zero_eq_operatorFieldApply] using happ
        (fullSlot3 (I := I) (M := M) g gm)
        (domDomCongrSection (I := I) g (finRotate 3) S)
    _ = C * covariantJetNormSq (I := I) (M := M) g 2
          (fullSlot3 (I := I) (M := M) g gm) *
        covariantJetNormSq (I := I) (M := M) g 2 S := by
      rw [dom_h2 (I := I) (M := M)]

private theorem raiseLast_h1
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (gm : SmoothRiemannianMetric I M)
        (S : SmoothCcTensor g 0 3),
      covariantJetNormSq (I := I) (M := M) g 1
          (raiseLast (I := I) (M := M) g gm S) ≤
        C * covariantJetNormSq (I := I) (M := M) g 2
            (fullSlot3 (I := I) (M := M) g gm) *
          covariantJetNormSq (I := I) (M := M) g 1 S := by
  obtain ⟨C, hC, happ⟩ :=
    app_h21_mul (I := I) (M := M) hDim g 0 3 3
  refine ⟨C, hC, ?_⟩
  intro gm S
  calc
    covariantJetNormSq (I := I) (M := M) g 1
        (raiseLast (I := I) (M := M) g gm S) =
      covariantJetNormSq (I := I) (M := M) g 1
        (operatorFieldApply (I := I) (M := M) g 3 3
          (fullSlot3 (I := I) (M := M) g gm)
          (domDomCongrSection (I := I) g (finRotate 3) S)) := by
      exact dom_h1 (I := I) (M := M) g connectionDifferenceLowOrderPermutation
        (operatorFieldApply (I := I) (M := M) g 3 3
          (fullSlot3 (I := I) (M := M) g gm)
          (domDomCongrSection (I := I) g (finRotate 3) S))
    _ ≤ C * covariantJetNormSq (I := I) (M := M) g 2
          (fullSlot3 (I := I) (M := M) g gm) *
        covariantJetNormSq (I := I) (M := M) g 1
          (domDomCongrSection (I := I) g (finRotate 3) S) := by
      simpa only [operatorFieldComposition_zero_eq_operatorFieldApply] using happ
        (fullSlot3 (I := I) (M := M) g gm)
        (domDomCongrSection (I := I) g (finRotate 3) S)
    _ = C * covariantJetNormSq (I := I) (M := M) g 2
          (fullSlot3 (I := I) (M := M) g gm) *
        covariantJetNormSq (I := I) (M := M) g 1 S := by
      rw [dom_h1 (I := I) (M := M)]

private theorem kappa_pair_h2
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ (gT gU : SmoothRiemannianMetric I M)
        (T U : SmoothCcTensor g 0 2)
        (_hT : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g T x u v =
            ccTensorBilin (I := I) g T x v u)
        (_hU : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g U x u v =
            ccTensorBilin (I := I) g U x v u)
        (_hTtie : ∀ (x : M) (u v : TangentSpace I x),
          gT.inner x u v =
            g.inner x u v + ccTensorBilinSymm (I := I) g T x u v)
        (_hUtie : ∀ (x : M) (u v : TangentSpace I x),
          gU.inner x u v =
            g.inner x u v + ccTensorBilinSymm (I := I) g U x u v),
      covariantJetNormSq (I := I) (M := M) g 2
          (lieCorrectionZeroKappa (I := I) (M := M) g gT g -
            lieCorrectionZeroKappa (I := I) (M := M) g gU g) ≤
        K * covariantJetNormSq (I := I) (M := M) g 3 (T - U) := by
  obtain ⟨C, hC, happ⟩ :=
    app_h2_mul (I := I) (M := M) hDim g 0 3 3
  let Jop : ℝ :=
    covariantJetNormSq (I := I) (M := M) g 2
      (kappaOp (I := I) (M := M) g)
  let K : ℝ := C * Jop
  have hJop : 0 ≤ Jop :=
    jet_nonneg (I := I) (M := M) g _
  have hK : 0 ≤ K := mul_nonneg hC hJop
  refine ⟨K, hK, ?_⟩
  intro gT gU T U hT hU hTtie hUtie
  rw [kappa_pair (I := I) (M := M) g gT gU T U
    hT hU hTtie hUtie]
  calc
    covariantJetNormSq (I := I) (M := M) g 2
        (ccOperatorFieldComp (I := I) (M := M) g 0 3 3
          (kappaOp (I := I) (M := M) g)
          (covGrad (I := I) (M := M) g 0 2 (T - U))) ≤
      C * Jop *
        covariantJetNormSq (I := I) (M := M) g 2
          (covGrad (I := I) (M := M) g 0 2 (T - U)) := by
      simpa only [Jop] using happ
        (kappaOp (I := I) (M := M) g)
        (covGrad (I := I) (M := M) g 0 2 (T - U))
    _ ≤ C * Jop *
        covariantJetNormSq (I := I) (M := M) g 3 (T - U) :=
      mul_le_mul_of_nonneg_left
        (grad_h2_le_h3 (I := I) (M := M) g (T - U)) hK
    _ = K * covariantJetNormSq (I := I) (M := M) g 3 (T - U) := by
      rfl

private theorem kappa_pair_h1
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ (gT gU : SmoothRiemannianMetric I M)
        (T U : SmoothCcTensor g 0 2)
        (_hT : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g T x u v =
            ccTensorBilin (I := I) g T x v u)
        (_hU : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g U x u v =
            ccTensorBilin (I := I) g U x v u)
        (_hTtie : ∀ (x : M) (u v : TangentSpace I x),
          gT.inner x u v =
            g.inner x u v + ccTensorBilinSymm (I := I) g T x u v)
        (_hUtie : ∀ (x : M) (u v : TangentSpace I x),
          gU.inner x u v =
            g.inner x u v + ccTensorBilinSymm (I := I) g U x u v),
      covariantJetNormSq (I := I) (M := M) g 1
          (lieCorrectionZeroKappa (I := I) (M := M) g gT g -
            lieCorrectionZeroKappa (I := I) (M := M) g gU g) ≤
        K * covariantJetNormSq (I := I) (M := M) g 2 (T - U) := by
  obtain ⟨C, hC, happ⟩ :=
    app_h21_mul (I := I) (M := M) hDim g 0 3 3
  let Jop : ℝ :=
    covariantJetNormSq (I := I) (M := M) g 2
      (kappaOp (I := I) (M := M) g)
  let K : ℝ := C * Jop
  have hJop : 0 ≤ Jop :=
    jet_nonneg (I := I) (M := M) g _
  have hK : 0 ≤ K := mul_nonneg hC hJop
  refine ⟨K, hK, ?_⟩
  intro gT gU T U hT hU hTtie hUtie
  rw [kappa_pair (I := I) (M := M) g gT gU T U
    hT hU hTtie hUtie]
  calc
    covariantJetNormSq (I := I) (M := M) g 1
        (ccOperatorFieldComp (I := I) (M := M) g 0 3 3
          (kappaOp (I := I) (M := M) g)
          (covGrad (I := I) (M := M) g 0 2 (T - U))) ≤
      C * Jop *
        covariantJetNormSq (I := I) (M := M) g 1
          (covGrad (I := I) (M := M) g 0 2 (T - U)) := by
      simpa only [Jop] using happ
        (kappaOp (I := I) (M := M) g)
        (covGrad (I := I) (M := M) g 0 2 (T - U))
    _ ≤ C * Jop *
        covariantJetNormSq (I := I) (M := M) g 2 (T - U) :=
      mul_le_mul_of_nonneg_left
        (grad_h1_le_h2 (I := I) (M := M) g (T - U)) hK
    _ = K * covariantJetNormSq (I := I) (M := M) g 2 (T - U) := by
      rfl

private theorem wXi_h2_low
    (g : SmoothRiemannianMetric I M)
    {δ₀ : ℝ} (hδ₀0 : 0 ≤ δ₀) (hδ₀ : δ₀ < 1) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ (gm : SmoothRiemannianMetric I M)
        (P : SmoothCcTensor g 0 2)
        (_hP : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g P x u v =
            ccTensorBilin (I := I) g P x v u)
        (_htie : ∀ (x : M) (u v : TangentSpace I x),
          gm.inner x u v =
            g.inner x u v + ccTensorBilinSymm (I := I) g P x u v)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀) (_hδ0 : 0 ≤ δ)
        (_hδ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g P) δ),
      covariantJetNormSq (I := I) (M := M) g 2
          (metricLoweredConnectionDifference (I := I) (M := M) g gm g) ≤
        K * (1 + covariantJetNormSq (I := I) (M := M) g 3 P) := by
  classical
  let Λ₀ : ℝ := (Module.finrank ℝ E : ℝ) * δ₀
  have hΛ₀0 : 0 ≤ Λ₀ :=
    mul_nonneg (Nat.cast_nonneg _) hδ₀0
  obtain ⟨Flow, hFlow0, hFlow⟩ :=
    metricLoweredConnectionDifference_lowOrder_iteratedCovGrad_norm_sq_le
      (I := I) (M := M) g g
      (2 * Module.finrank ℝ E + 10) hδ₀ hΛ₀0
  refine ⟨Flow 2, hFlow0 2, ?_⟩
  intro gm P hP htie δ hδ_le hδ0 hδ
  have hsymm : ccTensor02Symm (I := I) (M := M) g P = P :=
    symm_eq_self (I := I) (M := M) g P hP
  have hsup : ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g 0 2 x
          (P.toSection x) ≤ Λ₀ ^ 2 := by
    intro x
    rw [← hsymm]
    exact riemannianFiberNormSq_symmS_zero_le_fibreSmall
      (I := I) (M := M) g hδ₀0 P hδ_le hδ0 hδ x
  simpa only [covariantJetNormSq, Nat.reduceAdd] using
    hFlow gm P htie hδ_le hδ0 hδ hsup 2 (by omega)

private theorem corr_diff_h2
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M)
    {δ₀ : ℝ} (hδ₀0 : 0 ≤ δ₀) (hδ₀ : δ₀ < 1) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ (gT : SmoothRiemannianMetric I M)
        (T U : SmoothCcTensor g 0 2)
        (_hT : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g T x u v =
            ccTensorBilin (I := I) g T x v u)
        (_hTtie : ∀ (x : M) (u v : TangentSpace I x),
          gT.inner x u v =
            g.inner x u v + ccTensorBilinSymm (I := I) g T x u v)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀) (_hδ0 : 0 ≤ δ)
        (_hδ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) δ),
      covariantJetNormSq (I := I) (M := M) g 2
          (metricLoweredConnectionDifferenceCorrection (I := I) (M := M) g gT g (T - U)) ≤
        K * (1 + covariantJetNormSq (I := I) (M := M) g 3 T) *
          covariantJetNormSq (I := I) (M := M) g 3 (T - U) := by
  obtain ⟨C, hC, hmul⟩ :=
    metricLoweredConnectionDifferenceCorrection_sobolev_two_mul_bound (I := I) (M := M) hDim g
  obtain ⟨Kw, hKw, hw⟩ :=
    wXi_h2_low (I := I) (M := M) g hδ₀0 hδ₀
  let K : ℝ := C * Kw
  have hK : 0 ≤ K := mul_nonneg hC hKw
  refine ⟨K, hK, ?_⟩
  intro gT T U hT hTtie δ hδ_le hδ0 hδ
  have hraw :
      covariantJetNormSq (I := I) (M := M) g 2
          (metricLoweredConnectionDifferenceCorrection (I := I) (M := M) g gT g (T - U)) ≤
        C * covariantJetNormSq (I := I) (M := M) g 2 (T - U) *
          covariantJetNormSq (I := I) (M := M) g 2
            (metricLoweredConnectionDifference (I := I) (M := M) g gT g) := by
    simpa only [covariantJetNormSq, Nat.reduceAdd] using
      hmul gT g (T - U)
  have hd := jet_mono (I := I) (M := M) g
    (by omega : 2 ≤ 3) (T - U)
  have hw' := hw gT T hT hTtie hδ_le hδ0 hδ
  have hD0 : 0 ≤ covariantJetNormSq (I := I) (M := M) g 3 (T - U) :=
    jet_nonneg (I := I) (M := M) g _
  have hW0 : 0 ≤ covariantJetNormSq (I := I) (M := M) g 2
      (metricLoweredConnectionDifference (I := I) (M := M) g gT g) :=
    jet_nonneg (I := I) (M := M) g _
  calc
    covariantJetNormSq (I := I) (M := M) g 2
        (metricLoweredConnectionDifferenceCorrection (I := I) (M := M) g gT g (T - U)) ≤
      C * covariantJetNormSq (I := I) (M := M) g 2 (T - U) *
        covariantJetNormSq (I := I) (M := M) g 2
          (metricLoweredConnectionDifference (I := I) (M := M) g gT g) := hraw
    _ ≤ C * covariantJetNormSq (I := I) (M := M) g 3 (T - U) *
        covariantJetNormSq (I := I) (M := M) g 2
          (metricLoweredConnectionDifference (I := I) (M := M) g gT g) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hd hC) hW0
    _ ≤ C * covariantJetNormSq (I := I) (M := M) g 3 (T - U) *
        (Kw * (1 + covariantJetNormSq (I := I) (M := M) g 3 T)) :=
      mul_le_mul_of_nonneg_left hw'
        (mul_nonneg hC hD0)
    _ = K * (1 + covariantJetNormSq (I := I) (M := M) g 3 T) *
        covariantJetNormSq (I := I) (M := M) g 3 (T - U) := by
      simp only [K]
      ring

private theorem corr_diff_h2_low
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M)
    {δ₀ : ℝ} (hδ₀0 : 0 ≤ δ₀) (hδ₀ : δ₀ < 1) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ (gT : SmoothRiemannianMetric I M)
        (T U : SmoothCcTensor g 0 2)
        (_hT : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g T x u v =
            ccTensorBilin (I := I) g T x v u)
        (_hTtie : ∀ (x : M) (u v : TangentSpace I x),
          gT.inner x u v =
            g.inner x u v + ccTensorBilinSymm (I := I) g T x u v)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀) (_hδ0 : 0 ≤ δ)
        (_hδ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) δ),
      covariantJetNormSq (I := I) (M := M) g 2
          (metricLoweredConnectionDifferenceCorrection (I := I) (M := M) g gT g (T - U)) ≤
        K * (1 + covariantJetNormSq (I := I) (M := M) g 3 T) *
          covariantJetNormSq (I := I) (M := M) g 2 (T - U) := by
  obtain ⟨C, hC, hmul⟩ :=
    metricLoweredConnectionDifferenceCorrection_sobolev_two_mul_bound (I := I) (M := M) hDim g
  obtain ⟨Kw, hKw, hw⟩ :=
    wXi_h2_low (I := I) (M := M) g hδ₀0 hδ₀
  let K : ℝ := C * Kw
  have hK : 0 ≤ K := mul_nonneg hC hKw
  refine ⟨K, hK, ?_⟩
  intro gT T U hT hTtie δ hδ_le hδ0 hδ
  have hraw :
      covariantJetNormSq (I := I) (M := M) g 2
          (metricLoweredConnectionDifferenceCorrection (I := I) (M := M) g gT g (T - U)) ≤
        C * covariantJetNormSq (I := I) (M := M) g 2 (T - U) *
          covariantJetNormSq (I := I) (M := M) g 2
            (metricLoweredConnectionDifference (I := I) (M := M) g gT g) := by
    simpa only [covariantJetNormSq, Nat.reduceAdd] using
      hmul gT g (T - U)
  have hw' := hw gT T hT hTtie hδ_le hδ0 hδ
  have hD0 : 0 ≤ covariantJetNormSq (I := I) (M := M) g 2 (T - U) :=
    jet_nonneg (I := I) (M := M) g _
  calc
    covariantJetNormSq (I := I) (M := M) g 2
        (metricLoweredConnectionDifferenceCorrection (I := I) (M := M) g gT g (T - U)) ≤
      C * covariantJetNormSq (I := I) (M := M) g 2 (T - U) *
        covariantJetNormSq (I := I) (M := M) g 2
          (metricLoweredConnectionDifference (I := I) (M := M) g gT g) := hraw
    _ ≤ C * covariantJetNormSq (I := I) (M := M) g 2 (T - U) *
        (Kw * (1 + covariantJetNormSq (I := I) (M := M) g 3 T)) :=
      mul_le_mul_of_nonneg_left hw'
        (mul_nonneg hC hD0)
    _ = K * (1 + covariantJetNormSq (I := I) (M := M) g 3 T) *
        covariantJetNormSq (I := I) (M := M) g 2 (T - U) := by
      simp only [K]
      ring

theorem exists_metricLoweredConnectionDifference_covariantJetNormSq_two_sub_bound
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M)
    {δ₀ : ℝ} (hδ₀0 : 0 ≤ δ₀) (hδ₀ : δ₀ < 1) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ (gT gU g_bg : SmoothRiemannianMetric I M)
        (T U : SmoothCcTensor g 0 2)
        (_hT : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g T x u v =
            ccTensorBilin (I := I) g T x v u)
        (_hU : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g U x u v =
            ccTensorBilin (I := I) g U x v u)
        (_hTtie : ∀ (x : M) (u v : TangentSpace I x),
          gT.inner x u v =
            g.inner x u v + ccTensorBilinSymm (I := I) g T x u v)
        (_hUtie : ∀ (x : M) (u v : TangentSpace I x),
          gU.inner x u v =
            g.inner x u v + ccTensorBilinSymm (I := I) g U x u v)
        {δT δU : ℝ}
        (_hδT_le : δT ≤ δ₀) (_hδT0 : 0 ≤ δT)
        (_hδT : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) δT)
        (_hδU_le : δU ≤ δ₀) (_hδU0 : 0 ≤ δU)
        (_hδU : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g U) δU),
      covariantJetNormSq (I := I) (M := M) g 2
          (metricLoweredConnectionDifference (I := I) (M := M) g gT g_bg -
            metricLoweredConnectionDifference (I := I) (M := M) g gU g_bg) ≤
        K * (1 + covariantJetNormSq (I := I) (M := M) g 3 T) *
          (1 + covariantJetNormSq (I := I) (M := M) g 3 U) *
          covariantJetNormSq (I := I) (M := M) g 3 (T - U) := by
  obtain ⟨Cr, hCr, hraise⟩ :=
    raiseLast_h2 (I := I) (M := M) hDim g
  obtain ⟨Ks, hKs, hslot⟩ :=
    full_slot_h2 (I := I) (M := M) g hδ₀0 hδ₀
  obtain ⟨Kk, hKk, hkappa⟩ :=
    kappa_pair_h2 (I := I) (M := M) hDim g
  obtain ⟨Kc, hKc, hcorr⟩ :=
    corr_diff_h2 (I := I) (M := M) hDim g hδ₀0 hδ₀
  let K : ℝ := 2 * Cr * Ks * (Kk + Kc)
  have hK : 0 ≤ K :=
    mul_nonneg
      (mul_nonneg (mul_nonneg (by norm_num) hCr) hKs)
      (add_nonneg hKk hKc)
  refine ⟨K, hK, ?_⟩
  intro gT gU g_bg T U hT hU hTtie hUtie
    δT δU hδT_le hδT0 hδT hδU_le hδU0 hδU
  let JT : ℝ := covariantJetNormSq (I := I) (M := M) g 3 T
  let JU : ℝ := covariantJetNormSq (I := I) (M := M) g 3 U
  let JD : ℝ := covariantJetNormSq (I := I) (M := M) g 3 (T - U)
  let X : SmoothCcTensor g 0 3 :=
    lieCorrectionZeroKappa (I := I) (M := M) g gT g -
      lieCorrectionZeroKappa (I := I) (M := M) g gU g
  let Y : SmoothCcTensor g 0 3 :=
    metricLoweredConnectionDifferenceCorrection (I := I) (M := M) g gT g (T - U)
  have hbg :
      metricLoweredConnectionDifference (I := I) (M := M) g gT g_bg -
          metricLoweredConnectionDifference (I := I) (M := M) g gU g_bg =
        metricLoweredConnectionDifferenceCoefficient (I := I) g gT -
          metricLoweredConnectionDifferenceCoefficient (I := I) g gU := by
    simp only [metricLoweredConnectionDifference]
    module
  have hexact :
      metricLoweredConnectionDifference (I := I) (M := M) g gT g_bg -
          metricLoweredConnectionDifference (I := I) (M := M) g gU g_bg =
        raiseLast (I := I) (M := M) g gU (X - Y) := by
    rw [hbg]
    exact (moving_corr (I := I) (M := M) g gT gU T U
      hTtie hUtie).symm
  have hJT : 0 ≤ JT := jet_nonneg (I := I) (M := M) g _
  have hJU : 0 ≤ JU := jet_nonneg (I := I) (M := M) g _
  have hJD : 0 ≤ JD := jet_nonneg (I := I) (M := M) g _
  have hX : covariantJetNormSq (I := I) (M := M) g 2 X ≤ Kk * JD := by
    simpa only [X, JD] using
      hkappa gT gU T U hT hU hTtie hUtie
  have hY :
      covariantJetNormSq (I := I) (M := M) g 2 Y ≤
        Kc * (1 + JT) * JD := by
    simpa only [Y, JT, JD] using
      hcorr gT T U hT hTtie hδT_le hδT0 hδT
  have hX0 : 0 ≤ covariantJetNormSq (I := I) (M := M) g 2 X :=
    jet_nonneg (I := I) (M := M) g _
  have hY0 : 0 ≤ covariantJetNormSq (I := I) (M := M) g 2 Y :=
    jet_nonneg (I := I) (M := M) g _
  have hk_up : Kk * JD ≤ Kk * (1 + JT) * JD := by
    calc
      Kk * JD = Kk * 1 * JD := by ring
      _ ≤ Kk * (1 + JT) * JD :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (le_add_of_nonneg_right hJT) hKk) hJD
  have hsum :
      covariantJetNormSq (I := I) (M := M) g 2 X +
          covariantJetNormSq (I := I) (M := M) g 2 Y ≤
        (Kk + Kc) * (1 + JT) * JD := by
    calc
      covariantJetNormSq (I := I) (M := M) g 2 X +
          covariantJetNormSq (I := I) (M := M) g 2 Y ≤
        Kk * JD + Kc * (1 + JT) * JD := add_le_add hX hY
      _ ≤ Kk * (1 + JT) * JD + Kc * (1 + JT) * JD :=
        add_le_add hk_up (le_refl _)
      _ = (Kk + Kc) * (1 + JT) * JD := by ring
  have hinner :
      covariantJetNormSq (I := I) (M := M) g 2 (X - Y) ≤
        2 * (Kk + Kc) * (1 + JT) * JD := by
    calc
      covariantJetNormSq (I := I) (M := M) g 2 (X - Y) ≤
        2 * (covariantJetNormSq (I := I) (M := M) g 2 X +
          covariantJetNormSq (I := I) (M := M) g 2 Y) :=
            jet_sub (I := I) (M := M) g 2 X Y
      _ ≤ 2 * ((Kk + Kc) * (1 + JT) * JD) :=
        mul_le_mul_of_nonneg_left hsum (by norm_num)
      _ = 2 * (Kk + Kc) * (1 + JT) * JD := by ring
  have hinner0 :
      0 ≤ covariantJetNormSq (I := I) (M := M) g 2 (X - Y) :=
    jet_nonneg (I := I) (M := M) g _
  have hJU23 := jet_mono (I := I) (M := M) g
    (by omega : 2 ≤ 3) U
  have hslot2 :
      covariantJetNormSq (I := I) (M := M) g 2
          (fullSlot3 (I := I) (M := M) g gU) ≤
        Ks * (1 + JU) := by
    calc
      covariantJetNormSq (I := I) (M := M) g 2
          (fullSlot3 (I := I) (M := M) g gU) ≤
        Ks * (1 + covariantJetNormSq (I := I) (M := M) g 2 U) :=
          hslot gU U hU hUtie hδU_le hδU0 hδU
      _ ≤ Ks * (1 + JU) :=
        mul_le_mul_of_nonneg_left (by
          dsimp only [JU]
          exact add_le_add (le_refl 1) hJU23) hKs
  have hslot0 :
      0 ≤ covariantJetNormSq (I := I) (M := M) g 2
          (fullSlot3 (I := I) (M := M) g gU) :=
    jet_nonneg (I := I) (M := M) g _
  rw [hexact]
  calc
    covariantJetNormSq (I := I) (M := M) g 2
        (raiseLast (I := I) (M := M) g gU (X - Y)) ≤
      Cr * covariantJetNormSq (I := I) (M := M) g 2
          (fullSlot3 (I := I) (M := M) g gU) *
        covariantJetNormSq (I := I) (M := M) g 2 (X - Y) :=
      hraise gU (X - Y)
    _ ≤ Cr * (Ks * (1 + JU)) *
        covariantJetNormSq (I := I) (M := M) g 2 (X - Y) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hslot2 hCr) hinner0
    _ ≤ Cr * (Ks * (1 + JU)) *
        (2 * (Kk + Kc) * (1 + JT) * JD) :=
      mul_le_mul_of_nonneg_left hinner
        (mul_nonneg hCr
          (mul_nonneg hKs (by linarith)))
    _ = K * (1 + JT) * (1 + JU) * JD := by
      simp only [K]
      ring

private theorem sq_add_sq_le_add_sq
    {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    x ^ 2 + y ^ 2 ≤ (x + y) ^ 2 := by
  calc
    x ^ 2 + y ^ 2 ≤ x ^ 2 + y ^ 2 + 2 * x * y :=
      le_add_of_nonneg_right (mul_nonneg (mul_nonneg (by norm_num) hx) hy)
    _ = (x + y) ^ 2 := by ring

private theorem add_sq_le_two_sq_add_sq (x y : ℝ) :
    (x + y) ^ 2 ≤ 2 * x ^ 2 + 2 * y ^ 2 := by
  calc
    (x + y) ^ 2 ≤ (x + y) ^ 2 + (x - y) ^ 2 :=
      le_add_of_nonneg_right (sq_nonneg (x - y))
    _ = 2 * x ^ 2 + 2 * y ^ 2 := by ring

private theorem one_add_sq_le_sq_one_add {x : ℝ} (hx : 0 ≤ x) :
    1 + x ^ 2 ≤ (1 + x) ^ 2 := by
  calc
    1 + x ^ 2 ≤ 1 + x ^ 2 + 2 * x :=
      le_add_of_nonneg_right (mul_nonneg (by norm_num) hx)
    _ = (1 + x) ^ 2 := by ring

theorem exists_metricLoweredConnectionDifference_covariantJetNormSq_one_sub_bound
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M)
    {δ₀ : ℝ} (hδ₀0 : 0 ≤ δ₀) (hδ₀ : δ₀ < 1) :
    ∃ B0 B1 : ℝ → ℝ,
      (∀ R : ℝ, 0 ≤ R → 0 ≤ B0 R) ∧
      (∀ R : ℝ, 0 ≤ R → 0 ≤ B1 R) ∧
      ∀ (gT gU g_bg : SmoothRiemannianMetric I M)
        (T U : SmoothCcTensor g 0 2)
        (_hT : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g T x u v =
            ccTensorBilin (I := I) g T x v u)
        (_hU : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g U x u v =
            ccTensorBilin (I := I) g U x v u)
        (_hTtie : ∀ (x : M) (u v : TangentSpace I x),
          gT.inner x u v =
            g.inner x u v + ccTensorBilinSymm (I := I) g T x u v)
        (_hUtie : ∀ (x : M) (u v : TangentSpace I x),
          gU.inner x u v =
            g.inner x u v + ccTensorBilinSymm (I := I) g U x u v)
        {δT δU : ℝ}
        (_hδT_le : δT ≤ δ₀) (_hδT0 : 0 ≤ δT)
        (_hδT : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) δT)
        (_hδU_le : δU ≤ δ₀) (_hδU0 : 0 ≤ δU)
        (_hδU : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g U) δU)
        (R A D2 : ℝ),
        0 ≤ R → 0 ≤ A → 0 ≤ D2 →
        covariantJetNormSq (I := I) (M := M) g 2 U ≤ R ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 3 T ≤ A ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 2 (T - U) ≤ D2 ^ 2 →
      covariantJetNormSq (I := I) (M := M) g 1
          (metricLoweredConnectionDifference (I := I) (M := M) g gT g_bg -
            metricLoweredConnectionDifference (I := I) (M := M) g gU g_bg) ≤
        (B0 R * D2 + B1 R * A * D2) ^ 2 := by
  obtain ⟨Cr, hCr, hraise⟩ :=
    raiseLast_h1 (I := I) (M := M) hDim g
  obtain ⟨Ks, hKs, hslot⟩ :=
    full_slot_h2 (I := I) (M := M) g hδ₀0 hδ₀
  obtain ⟨Kk, hKk, hkappa⟩ :=
    kappa_pair_h1 (I := I) (M := M) hDim g
  obtain ⟨Kc, hKc, hcorr⟩ :=
    corr_diff_h2_low (I := I) (M := M) hDim g hδ₀0 hδ₀
  let Q0 : ℝ → ℝ := fun R =>
    2 * Cr * Ks * (1 + R ^ 2) * (Kk + Kc)
  let Q1 : ℝ → ℝ := fun R =>
    2 * Cr * Ks * (1 + R ^ 2) * Kc
  let B0 : ℝ → ℝ := fun R => Real.sqrt (Q0 R)
  let B1 : ℝ → ℝ := fun R => Real.sqrt (Q1 R)
  have hQ0 : ∀ R : ℝ, 0 ≤ R → 0 ≤ Q0 R := by
    intro R hR
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg (mul_nonneg (by norm_num) hCr) hKs)
        (by positivity))
      (add_nonneg hKk hKc)
  have hQ1 : ∀ R : ℝ, 0 ≤ R → 0 ≤ Q1 R := by
    intro R hR
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg (mul_nonneg (by norm_num) hCr) hKs)
        (by positivity))
      hKc
  refine ⟨B0, B1, fun R hR => Real.sqrt_nonneg _,
    fun R hR => Real.sqrt_nonneg _, ?_⟩
  intro gT gU g_bg T U hT hU hTtie hUtie
    δT δU hδT_le hδT0 hδT hδU_le hδU0 hδU
    R A D2 hR hA hD2 hU2 hT3 hTU2
  let JT : ℝ := covariantJetNormSq (I := I) (M := M) g 3 T
  let JD : ℝ := covariantJetNormSq (I := I) (M := M) g 2 (T - U)
  let X : SmoothCcTensor g 0 3 :=
    lieCorrectionZeroKappa (I := I) (M := M) g gT g -
      lieCorrectionZeroKappa (I := I) (M := M) g gU g
  let Y : SmoothCcTensor g 0 3 :=
    metricLoweredConnectionDifferenceCorrection (I := I) (M := M) g gT g (T - U)
  have hbg :
      metricLoweredConnectionDifference (I := I) (M := M) g gT g_bg -
          metricLoweredConnectionDifference (I := I) (M := M) g gU g_bg =
        metricLoweredConnectionDifferenceCoefficient (I := I) g gT -
          metricLoweredConnectionDifferenceCoefficient (I := I) g gU := by
    simp only [metricLoweredConnectionDifference]
    module
  have hexact :
      metricLoweredConnectionDifference (I := I) (M := M) g gT g_bg -
          metricLoweredConnectionDifference (I := I) (M := M) g gU g_bg =
        raiseLast (I := I) (M := M) g gU (X - Y) := by
    rw [hbg]
    exact (moving_corr (I := I) (M := M) g gT gU T U
      hTtie hUtie).symm
  have hJT0 : 0 ≤ JT := jet_nonneg (I := I) (M := M) g _
  have hJD0 : 0 ≤ JD := jet_nonneg (I := I) (M := M) g _
  have hX :
      covariantJetNormSq (I := I) (M := M) g 1 X ≤ Kk * JD := by
    simpa only [X, JD] using
      hkappa gT gU T U hT hU hTtie hUtie
  have hY2 :
      covariantJetNormSq (I := I) (M := M) g 2 Y ≤
        Kc * (1 + JT) * JD := by
    simpa only [Y, JT, JD] using
      hcorr gT T U hT hTtie hδT_le hδT0 hδT
  have hY1 :
      covariantJetNormSq (I := I) (M := M) g 1 Y ≤
        Kc * (1 + JT) * JD := by
    exact (jet_mono (I := I) (M := M) g
      (by omega : 1 ≤ 2) Y).trans hY2
  have hsum :
      covariantJetNormSq (I := I) (M := M) g 1 X +
          covariantJetNormSq (I := I) (M := M) g 1 Y ≤
        (Kk + Kc * (1 + JT)) * JD := by
    calc
      _ ≤ Kk * JD + (Kc * (1 + JT) * JD) :=
        add_le_add hX hY1
      _ = (Kk + Kc * (1 + JT)) * JD := by ring
  have hinner :
      covariantJetNormSq (I := I) (M := M) g 1 (X - Y) ≤
        2 * (Kk + Kc * (1 + JT)) * JD := by
    calc
      covariantJetNormSq (I := I) (M := M) g 1 (X - Y) ≤
          2 * (covariantJetNormSq (I := I) (M := M) g 1 X +
            covariantJetNormSq (I := I) (M := M) g 1 Y) :=
        jet_sub (I := I) (M := M) g 1 X Y
      _ ≤ 2 * ((Kk + Kc * (1 + JT)) * JD) :=
        mul_le_mul_of_nonneg_left hsum (by norm_num)
      _ = 2 * (Kk + Kc * (1 + JT)) * JD := by ring
  have hinner0 :
      0 ≤ covariantJetNormSq (I := I) (M := M) g 1 (X - Y) :=
    jet_nonneg (I := I) (M := M) g _
  have hslot2 :
      covariantJetNormSq (I := I) (M := M) g 2
          (fullSlot3 (I := I) (M := M) g gU) ≤
        Ks * (1 + R ^ 2) := by
    calc
      covariantJetNormSq (I := I) (M := M) g 2
          (fullSlot3 (I := I) (M := M) g gU) ≤
        Ks * (1 + covariantJetNormSq (I := I) (M := M) g 2 U) :=
          hslot gU U hU hUtie hδU_le hδU0 hδU
      _ ≤ Ks * (1 + R ^ 2) :=
        mul_le_mul_of_nonneg_left
          (by simpa only [add_comm] using add_le_add_left hU2 1) hKs
  have hJT3 : JT ≤ A ^ 2 := by
    simpa only [JT] using hT3
  have hJD2 : JD ≤ D2 ^ 2 := by
    simpa only [JD] using hTU2
  have hpart :
      Kk + Kc * (1 + JT) ≤
        Kk + Kc * (1 + A ^ 2) := by
    calc
      Kk + Kc * (1 + JT) = Kc * (JT + 1) + Kk := by ring
      _ ≤ Kc * (A ^ 2 + 1) + Kk :=
        add_le_add_left
          (mul_le_mul_of_nonneg_left (add_le_add_left hJT3 1) hKc) Kk
      _ = Kk + Kc * (1 + A ^ 2) := by ring
  have hpart0 : 0 ≤ Kk + Kc * (1 + A ^ 2) := by
    exact add_nonneg hKk
      (mul_nonneg hKc (by positivity))
  have hinnerA :
      2 * (Kk + Kc * (1 + JT)) * JD ≤
        2 * (Kk + Kc * (1 + A ^ 2)) * D2 ^ 2 := by
    calc
      2 * (Kk + Kc * (1 + JT)) * JD ≤
          2 * (Kk + Kc * (1 + A ^ 2)) * JD :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hpart (by norm_num)) hJD0
      _ ≤ 2 * (Kk + Kc * (1 + A ^ 2)) * D2 ^ 2 :=
        mul_le_mul_of_nonneg_left hJD2
          (mul_nonneg (by norm_num) hpart0)
  have hfactor :
      0 ≤ Cr * (Ks * (1 + R ^ 2)) :=
    mul_nonneg hCr
      (mul_nonneg hKs (by positivity))
  have hout :
      covariantJetNormSq (I := I) (M := M) g 1
          (metricLoweredConnectionDifference (I := I) (M := M) g gT g_bg -
            metricLoweredConnectionDifference (I := I) (M := M) g gU g_bg) ≤
        (Q0 R + Q1 R * A ^ 2) * D2 ^ 2 := by
    rw [hexact]
    calc
      covariantJetNormSq (I := I) (M := M) g 1
          (raiseLast (I := I) (M := M) g gU (X - Y)) ≤
        Cr * covariantJetNormSq (I := I) (M := M) g 2
            (fullSlot3 (I := I) (M := M) g gU) *
          covariantJetNormSq (I := I) (M := M) g 1 (X - Y) :=
        hraise gU (X - Y)
      _ ≤ Cr * (Ks * (1 + R ^ 2)) *
          covariantJetNormSq (I := I) (M := M) g 1 (X - Y) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hslot2 hCr) hinner0
      _ ≤ Cr * (Ks * (1 + R ^ 2)) *
          (2 * (Kk + Kc * (1 + JT)) * JD) :=
        mul_le_mul_of_nonneg_left hinner hfactor
      _ ≤ Cr * (Ks * (1 + R ^ 2)) *
          (2 * (Kk + Kc * (1 + A ^ 2)) * D2 ^ 2) :=
        mul_le_mul_of_nonneg_left hinnerA hfactor
      _ = (Q0 R + Q1 R * A ^ 2) * D2 ^ 2 := by
        simp only [Q0, Q1]
        ring
  have hB0sq : (B0 R) ^ 2 = Q0 R := by
    simpa only [B0] using Real.sq_sqrt (hQ0 R hR)
  have hB1sq : (B1 R) ^ 2 = Q1 R := by
    simpa only [B1] using Real.sq_sqrt (hQ1 R hR)
  have ha0 : 0 ≤ B0 R * D2 :=
    mul_nonneg (Real.sqrt_nonneg _) hD2
  have hb0 : 0 ≤ B1 R * A * D2 :=
    mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) hA) hD2
  calc
    covariantJetNormSq (I := I) (M := M) g 1
        (metricLoweredConnectionDifference (I := I) (M := M) g gT g_bg -
          metricLoweredConnectionDifference (I := I) (M := M) g gU g_bg) ≤
      (Q0 R + Q1 R * A ^ 2) * D2 ^ 2 := hout
    _ = (B0 R * D2) ^ 2 + (B1 R * A * D2) ^ 2 := by
      rw [add_mul, mul_pow, mul_pow, mul_pow, hB0sq, hB1sq]
    _ ≤ (B0 R * D2 + B1 R * A * D2) ^ 2 :=
      sq_add_sq_le_add_sq ha0 hb0

theorem exists_metricLoweredConnectionDifference_covariantJetNormSq_two_sub_tame_bound
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M)
    {δ₀ : ℝ} (hδ₀0 : 0 ≤ δ₀) (hδ₀ : δ₀ < 1) :
    ∃ B0 B1 : ℝ → ℝ,
      (∀ R : ℝ, 0 ≤ R → 0 ≤ B0 R) ∧
      (∀ R : ℝ, 0 ≤ R → 0 ≤ B1 R) ∧
      ∀ (gT gU g_bg : SmoothRiemannianMetric I M)
        (T U : SmoothCcTensor g 0 2)
        (_hT : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g T x u v =
            ccTensorBilin (I := I) g T x v u)
        (_hU : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g U x u v =
            ccTensorBilin (I := I) g U x v u)
        (_hTtie : ∀ (x : M) (u v : TangentSpace I x),
          gT.inner x u v =
            g.inner x u v + ccTensorBilinSymm (I := I) g T x u v)
        (_hUtie : ∀ (x : M) (u v : TangentSpace I x),
          gU.inner x u v =
            g.inner x u v + ccTensorBilinSymm (I := I) g U x u v)
        {δT δU : ℝ}
        (_hδT_le : δT ≤ δ₀) (_hδT0 : 0 ≤ δT)
        (_hδT : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) δT)
        (_hδU_le : δU ≤ δ₀) (_hδU0 : 0 ≤ δU)
        (_hδU : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g U) δU)
        (R A D2 D3 : ℝ),
        0 ≤ R → 0 ≤ A → 0 ≤ D2 → 0 ≤ D3 →
        covariantJetNormSq (I := I) (M := M) g 2 U ≤ R ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 3 T ≤ A ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 2 (T - U) ≤ D2 ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 3 (T - U) ≤ D3 ^ 2 →
      covariantJetNormSq (I := I) (M := M) g 2
          (metricLoweredConnectionDifference (I := I) (M := M) g gT g_bg -
            metricLoweredConnectionDifference (I := I) (M := M) g gU g_bg) ≤
        (B0 R * D3 + B1 R * D2 + B1 R * A * D2) ^ 2 := by
  obtain ⟨Cr, hCr, hraise⟩ :=
    raiseLast_h2 (I := I) (M := M) hDim g
  obtain ⟨Ks, hKs, hslot⟩ :=
    full_slot_h2 (I := I) (M := M) g hδ₀0 hδ₀
  obtain ⟨Kk, hKk, hkappa⟩ :=
    kappa_pair_h2 (I := I) (M := M) hDim g
  obtain ⟨Cc, hCc, hcorr⟩ :=
    metricLoweredConnectionDifferenceCorrection_sobolev_two_mul_bound (I := I) (M := M) hDim g
  obtain ⟨Kw, hKw, hwXi⟩ :=
    wXi_h2_low (I := I) (M := M) g hδ₀0 hδ₀
  let Q0 : ℝ → ℝ := fun R =>
    2 * Cr * Ks * (1 + R ^ 2) * Kk
  let Q1 : ℝ → ℝ := fun R =>
    2 * Cr * Ks * (1 + R ^ 2) * (Cc * Kw)
  let B0 : ℝ → ℝ := fun R => Real.sqrt (Q0 R)
  let B1 : ℝ → ℝ := fun R => Real.sqrt (Q1 R)
  have hQ0 : ∀ R : ℝ, 0 ≤ R → 0 ≤ Q0 R := by
    intro R hR
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg (mul_nonneg (by norm_num) hCr) hKs)
          (by positivity))
      hKk
  have hQ1 : ∀ R : ℝ, 0 ≤ R → 0 ≤ Q1 R := by
    intro R hR
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg (mul_nonneg (by norm_num) hCr) hKs)
          (by positivity))
      (mul_nonneg hCc hKw)
  refine ⟨B0, B1, fun R _ => Real.sqrt_nonneg _,
    fun R _ => Real.sqrt_nonneg _, ?_⟩
  intro gT gU g_bg T U hT hU hTtie hUtie
    δT δU hδT_le hδT0 hδT hδU_le hδU0 hδU
    R A D2 D3 hR hA hD2 hD3 hU2 hT3 hTU2 hTU3
  let X : SmoothCcTensor g 0 3 :=
    lieCorrectionZeroKappa (I := I) (M := M) g gT g -
      lieCorrectionZeroKappa (I := I) (M := M) g gU g
  let Y : SmoothCcTensor g 0 3 :=
    metricLoweredConnectionDifferenceCorrection (I := I) (M := M) g gT g (T - U)
  have hbg :
      metricLoweredConnectionDifference (I := I) (M := M) g gT g_bg -
          metricLoweredConnectionDifference (I := I) (M := M) g gU g_bg =
        metricLoweredConnectionDifferenceCoefficient (I := I) g gT -
          metricLoweredConnectionDifferenceCoefficient (I := I) g gU := by
    simp only [metricLoweredConnectionDifference]
    module
  have hexact :
      metricLoweredConnectionDifference (I := I) (M := M) g gT g_bg -
          metricLoweredConnectionDifference (I := I) (M := M) g gU g_bg =
        raiseLast (I := I) (M := M) g gU (X - Y) := by
    rw [hbg]
    exact (moving_corr (I := I) (M := M) g gT gU T U
      hTtie hUtie).symm
  have hX :
      covariantJetNormSq (I := I) (M := M) g 2 X ≤ Kk * D3 ^ 2 := by
    calc
      covariantJetNormSq (I := I) (M := M) g 2 X ≤
          Kk * covariantJetNormSq (I := I) (M := M) g 3 (T - U) := by
        simpa only [X] using
          hkappa gT gU T U hT hU hTtie hUtie
      _ ≤ Kk * D3 ^ 2 :=
        mul_le_mul_of_nonneg_left hTU3 hKk
  have hW :
      covariantJetNormSq (I := I) (M := M) g 2
          (metricLoweredConnectionDifference (I := I) (M := M) g gT g) ≤
        Kw * (1 + A ^ 2) := by
    calc
      covariantJetNormSq (I := I) (M := M) g 2
          (metricLoweredConnectionDifference (I := I) (M := M) g gT g) ≤
        Kw * (1 + covariantJetNormSq (I := I) (M := M) g 3 T) :=
          hwXi gT T hT hTtie hδT_le hδT0 hδT
      _ ≤ Kw * (1 + A ^ 2) :=
        mul_le_mul_of_nonneg_left
          (by linarith) hKw
  have hY :
      covariantJetNormSq (I := I) (M := M) g 2 Y ≤
        Cc * Kw * (D2 ^ 2 + A ^ 2 * D2 ^ 2) := by
    have hraw :
        covariantJetNormSq (I := I) (M := M) g 2 Y ≤
          Cc * covariantJetNormSq (I := I) (M := M) g 2 (T - U) *
            covariantJetNormSq (I := I) (M := M) g 2
              (metricLoweredConnectionDifference (I := I) (M := M) g gT g) := by
      simpa only [Y, covariantJetNormSq, Nat.reduceAdd] using
        hcorr gT g (T - U)
    have hleft :
        Cc * covariantJetNormSq (I := I) (M := M) g 2 (T - U) ≤
          Cc * D2 ^ 2 :=
      mul_le_mul_of_nonneg_left hTU2 hCc
    have hW0 :
        0 ≤ covariantJetNormSq (I := I) (M := M) g 2
          (metricLoweredConnectionDifference (I := I) (M := M) g gT g) :=
      jet_nonneg (I := I) (M := M) g _
    calc
      covariantJetNormSq (I := I) (M := M) g 2 Y ≤
          Cc * covariantJetNormSq (I := I) (M := M) g 2 (T - U) *
            covariantJetNormSq (I := I) (M := M) g 2
              (metricLoweredConnectionDifference (I := I) (M := M) g gT g) := hraw
      _ ≤ Cc * D2 ^ 2 * (Kw * (1 + A ^ 2)) :=
        mul_le_mul hleft hW hW0
          (mul_nonneg hCc (sq_nonneg D2))
      _ = Cc * Kw * (D2 ^ 2 + A ^ 2 * D2 ^ 2) := by
        ring
  have hinner :
      covariantJetNormSq (I := I) (M := M) g 2 (X - Y) ≤
        2 * (Kk * D3 ^ 2 +
          Cc * Kw * (D2 ^ 2 + A ^ 2 * D2 ^ 2)) := by
    exact (jet_sub (I := I) (M := M) g 2 X Y).trans
      (mul_le_mul_of_nonneg_left (add_le_add hX hY) (by norm_num))
  have hinner0 :
      0 ≤ covariantJetNormSq (I := I) (M := M) g 2 (X - Y) :=
    jet_nonneg (I := I) (M := M) g _
  have hslotR :
      covariantJetNormSq (I := I) (M := M) g 2
          (fullSlot3 (I := I) (M := M) g gU) ≤
        Ks * (1 + R ^ 2) := by
    calc
      covariantJetNormSq (I := I) (M := M) g 2
          (fullSlot3 (I := I) (M := M) g gU) ≤
        Ks * (1 + covariantJetNormSq (I := I) (M := M) g 2 U) :=
          hslot gU U hU hUtie hδU_le hδU0 hδU
      _ ≤ Ks * (1 + R ^ 2) :=
        mul_le_mul_of_nonneg_left
          (by linarith) hKs
  have hfactor :
      0 ≤ Cr * (Ks * (1 + R ^ 2)) :=
    mul_nonneg hCr (mul_nonneg hKs (by positivity))
  have hout :
      covariantJetNormSq (I := I) (M := M) g 2
          (metricLoweredConnectionDifference (I := I) (M := M) g gT g_bg -
            metricLoweredConnectionDifference (I := I) (M := M) g gU g_bg) ≤
        Q0 R * D3 ^ 2 + Q1 R * D2 ^ 2 +
          Q1 R * A ^ 2 * D2 ^ 2 := by
    rw [hexact]
    calc
      covariantJetNormSq (I := I) (M := M) g 2
          (raiseLast (I := I) (M := M) g gU (X - Y)) ≤
        Cr * covariantJetNormSq (I := I) (M := M) g 2
            (fullSlot3 (I := I) (M := M) g gU) *
          covariantJetNormSq (I := I) (M := M) g 2 (X - Y) :=
        hraise gU (X - Y)
      _ ≤ Cr * (Ks * (1 + R ^ 2)) *
          covariantJetNormSq (I := I) (M := M) g 2 (X - Y) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hslotR hCr) hinner0
      _ ≤ Cr * (Ks * (1 + R ^ 2)) *
          (2 * (Kk * D3 ^ 2 +
            Cc * Kw * (D2 ^ 2 + A ^ 2 * D2 ^ 2))) :=
        mul_le_mul_of_nonneg_left hinner hfactor
      _ = Q0 R * D3 ^ 2 + Q1 R * D2 ^ 2 +
          Q1 R * A ^ 2 * D2 ^ 2 := by
        simp only [Q0, Q1]
        ring
  have hB0sq : (B0 R) ^ 2 = Q0 R := by
    simpa only [B0] using Real.sq_sqrt (hQ0 R hR)
  have hB1sq : (B1 R) ^ 2 = Q1 R := by
    simpa only [B1] using Real.sq_sqrt (hQ1 R hR)
  have ha0 : 0 ≤ B0 R * D3 :=
    mul_nonneg (Real.sqrt_nonneg _) hD3
  have hb0 : 0 ≤ B1 R * D2 :=
    mul_nonneg (Real.sqrt_nonneg _) hD2
  have hc0 : 0 ≤ B1 R * A * D2 :=
    mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) hA) hD2
  calc
    covariantJetNormSq (I := I) (M := M) g 2
        (metricLoweredConnectionDifference (I := I) (M := M) g gT g_bg -
          metricLoweredConnectionDifference (I := I) (M := M) g gU g_bg) ≤
      Q0 R * D3 ^ 2 + Q1 R * D2 ^ 2 +
        Q1 R * A ^ 2 * D2 ^ 2 := hout
    _ = (B0 R * D3) ^ 2 + (B1 R * D2) ^ 2 +
        (B1 R * A * D2) ^ 2 := by
      rw [mul_pow, mul_pow, mul_pow, mul_pow, hB0sq, hB1sq]
    _ ≤ (B0 R * D3 + B1 R * D2 + B1 R * A * D2) ^ 2 := by
      calc
        (B0 R * D3) ^ 2 + (B1 R * D2) ^ 2 +
            (B1 R * A * D2) ^ 2 ≤
          (B0 R * D3 + B1 R * D2) ^ 2 +
            (B1 R * A * D2) ^ 2 :=
          add_le_add (sq_add_sq_le_add_sq ha0 hb0) (le_refl _)
        _ ≤ (B0 R * D3 + B1 R * D2 + B1 R * A * D2) ^ 2 :=
          sq_add_sq_le_add_sq (add_nonneg ha0 hb0) hc0

theorem connSec_pair_h1
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M)
    {δ₀ : ℝ} (hδ₀0 : 0 ≤ δ₀) (hδ₀ : δ₀ < 1) :
    ∃ B0 B1 : ℝ → ℝ,
      (∀ R : ℝ, 0 ≤ R → 0 ≤ B0 R) ∧
      (∀ R : ℝ, 0 ≤ R → 0 ≤ B1 R) ∧
      ∀ (gT gU : SmoothRiemannianMetric I M)
        (T U : SmoothCcTensor g 0 2)
        (_hT : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g T x u v =
            ccTensorBilin (I := I) g T x v u)
        (_hU : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g U x u v =
            ccTensorBilin (I := I) g U x v u)
        (_hTtie : ∀ (x : M) (u v : TangentSpace I x),
          gT.inner x u v =
            g.inner x u v + ccTensorBilinSymm (I := I) g T x u v)
        (_hUtie : ∀ (x : M) (u v : TangentSpace I x),
          gU.inner x u v =
            g.inner x u v + ccTensorBilinSymm (I := I) g U x u v)
        {δT δU : ℝ}
        (_hδT_le : δT ≤ δ₀) (_hδT0 : 0 ≤ δT)
        (_hδT : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) δT)
        (_hδU_le : δU ≤ δ₀) (_hδU0 : 0 ≤ δU)
        (_hδU : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g U) δU)
        (R A D2 : ℝ),
        0 ≤ R → 0 ≤ A → 0 ≤ D2 →
        covariantJetNormSq (I := I) (M := M) g 2 U ≤ R ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 3 T ≤ A ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 2 (T - U) ≤ D2 ^ 2 →
      covariantJetNormSq (I := I) (M := M) g 1
          (connectionDifferenceSection (I := I) gT g -
            connectionDifferenceSection (I := I) gU g) ≤
        (B0 R * D2 + B1 R * A * D2) ^ 2 := by
  obtain ⟨B0, B1, hB0, hB1, hpair⟩ :=
    exists_metricLoweredConnectionDifference_covariantJetNormSq_one_sub_bound (I := I) (M := M) hDim g hδ₀0 hδ₀
  refine ⟨B0, B1, hB0, hB1, ?_⟩
  intro gT gU T U hT hU hTtie hUtie
    δT δU hδT_le hδT0 hδT hδU_le hδU0 hδU
    R A D2 hR hA hD2 hU2 hT3 hTU2
  calc
    covariantJetNormSq (I := I) (M := M) g 1
        (connectionDifferenceSection (I := I) gT g -
          connectionDifferenceSection (I := I) gU g) =
      covariantJetNormSq (I := I) (M := M) g 1
        (metricLoweredConnectionDifferenceCoefficient (I := I) g gT -
          metricLoweredConnectionDifferenceCoefficient (I := I) g gU) :=
      connSec_h1_eq (I := I) (M := M) g gT gU
    _ = covariantJetNormSq (I := I) (M := M) g 1
        (metricLoweredConnectionDifference (I := I) (M := M) g gT g -
          metricLoweredConnectionDifference (I := I) (M := M) g gU g) := by
      congr 1
      simp only [metricLoweredConnectionDifference]
      module
    _ ≤ (B0 R * D2 + B1 R * A * D2) ^ 2 :=
      hpair gT gU g T U hT hU hTtie hUtie
        hδT_le hδT0 hδT hδU_le hδU0 hδU
        R A D2 hR hA hD2 hU2 hT3 hTU2

theorem connSec_sub_tame
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M)
    {δ₀ : ℝ} (hδ₀0 : 0 ≤ δ₀) (hδ₀ : δ₀ < 1) :
    ∃ B0 B1 : ℝ → ℝ,
      (∀ R : ℝ, 0 ≤ R → 0 ≤ B0 R) ∧
      (∀ R : ℝ, 0 ≤ R → 0 ≤ B1 R) ∧
      ∀ (gT gU : SmoothRiemannianMetric I M)
        (T U : SmoothCcTensor g 0 2)
        (_hT : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g T x u v =
            ccTensorBilin (I := I) g T x v u)
        (_hU : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g U x u v =
            ccTensorBilin (I := I) g U x v u)
        (_hTtie : ∀ (x : M) (u v : TangentSpace I x),
          gT.inner x u v =
            g.inner x u v + ccTensorBilinSymm (I := I) g T x u v)
        (_hUtie : ∀ (x : M) (u v : TangentSpace I x),
          gU.inner x u v =
            g.inner x u v + ccTensorBilinSymm (I := I) g U x u v)
        {δT δU : ℝ}
        (_hδT_le : δT ≤ δ₀) (_hδT0 : 0 ≤ δT)
        (_hδT : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) δT)
        (_hδU_le : δU ≤ δ₀) (_hδU0 : 0 ≤ δU)
        (_hδU : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g U) δU)
        (R A D2 D3 : ℝ),
        0 ≤ R → 0 ≤ A → 0 ≤ D2 → 0 ≤ D3 →
        covariantJetNormSq (I := I) (M := M) g 2 U ≤ R ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 3 T ≤ A ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 2 (T - U) ≤ D2 ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 3 (T - U) ≤ D3 ^ 2 →
      covariantJetNormSq (I := I) (M := M) g 2
          (connectionDifferenceSection (I := I) gT g -
            connectionDifferenceSection (I := I) gU g) ≤
        (B0 R * D3 + B1 R * D2 + B1 R * A * D2) ^ 2 := by
  obtain ⟨B0, B1, hB0, hB1, hpair⟩ :=
    exists_metricLoweredConnectionDifference_covariantJetNormSq_two_sub_tame_bound (I := I) (M := M) hDim g hδ₀0 hδ₀
  refine ⟨B0, B1, hB0, hB1, ?_⟩
  intro gT gU T U hT hU hTtie hUtie
    δT δU hδT_le hδT0 hδT hδU_le hδU0 hδU
    R A D2 D3 hR hA hD2 hD3 hU2 hT3 hTU2 hTU3
  calc
    covariantJetNormSq (I := I) (M := M) g 2
        (connectionDifferenceSection (I := I) gT g -
          connectionDifferenceSection (I := I) gU g) =
      covariantJetNormSq (I := I) (M := M) g 2
        (metricLoweredConnectionDifferenceCoefficient (I := I) g gT -
          metricLoweredConnectionDifferenceCoefficient (I := I) g gU) :=
      connSec_h2_eq (I := I) (M := M) g gT gU
    _ = covariantJetNormSq (I := I) (M := M) g 2
        (metricLoweredConnectionDifference (I := I) (M := M) g gT g -
          metricLoweredConnectionDifference (I := I) (M := M) g gU g) := by
      congr 1
      simp only [metricLoweredConnectionDifference]
      module
    _ ≤ (B0 R * D3 + B1 R * D2 + B1 R * A * D2) ^ 2 :=
      hpair gT gU g T U hT hU hTtie hUtie
        hδT_le hδT0 hδT hδU_le hδU0 hδU
        R A D2 D3 hR hA hD2 hD3 hU2 hT3 hTU2 hTU3

theorem connIns_sub_tame
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M)
    {δ₀ : ℝ} (hδ₀0 : 0 ≤ δ₀) (hδ₀ : δ₀ < 1) :
    ∃ B0 B1 : ℝ → ℝ,
      (∀ R : ℝ, 0 ≤ R → 0 ≤ B0 R) ∧
      (∀ R : ℝ, 0 ≤ R → 0 ≤ B1 R) ∧
      ∀ (gT gU : SmoothRiemannianMetric I M)
        (T U : SmoothCcTensor g 0 2)
        (_hT : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g T x u v =
            ccTensorBilin (I := I) g T x v u)
        (_hU : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g U x u v =
            ccTensorBilin (I := I) g U x v u)
        (_hTtie : ∀ (x : M) (u v : TangentSpace I x),
          gT.inner x u v =
            g.inner x u v + ccTensorBilinSymm (I := I) g T x u v)
        (_hUtie : ∀ (x : M) (u v : TangentSpace I x),
          gU.inner x u v =
            g.inner x u v + ccTensorBilinSymm (I := I) g U x u v)
        {δT δU : ℝ}
        (_hδT_le : δT ≤ δ₀) (_hδT0 : 0 ≤ δT)
        (_hδT : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) δT)
        (_hδU_le : δU ≤ δ₀) (_hδU0 : 0 ≤ δU)
        (_hδU : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g U) δU)
        (R A D2 D3 : ℝ),
        0 ≤ R → 0 ≤ A → 0 ≤ D2 → 0 ≤ D3 →
        covariantJetNormSq (I := I) (M := M) g 2 U ≤ R ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 3 T ≤ A ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 2 (T - U) ≤ D2 ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 3 (T - U) ≤ D3 ^ 2 →
      covariantJetNormSq (I := I) (M := M) g 2
          (connectionDifferenceContravariantInsertionField (I := I) g gT -
            connectionDifferenceContravariantInsertionField (I := I) g gU) ≤
        (B0 R * D3 + B1 R * D2 + B1 R * A * D2) ^ 2 := by
  obtain ⟨C0, C1, hC0, hC1, hpair⟩ :=
    connSec_sub_tame (I := I) (M := M) hDim g hδ₀0 hδ₀
  let B0 : ℝ → ℝ := fun R => 3 * C0 R
  let B1 : ℝ → ℝ := fun R => 3 * C1 R
  refine ⟨B0, B1, fun R hR => mul_nonneg (by norm_num) (hC0 R hR),
    fun R hR => mul_nonneg (by norm_num) (hC1 R hR), ?_⟩
  intro gT gU T U hT hU hTtie hUtie
    δT δU hδT_le hδT0 hδT hδU_le hδU0 hδU
    R A D2 D3 hR hA hD2 hD3 hU2 hT3 hTU2 hTU3
  let X : ℝ := C0 R * D3 + C1 R * D2 + C1 R * A * D2
  have hX :
      covariantJetNormSq (I := I) (M := M) g 2
          (connectionDifferenceSection (I := I) gT g -
            connectionDifferenceSection (I := I) gU g) ≤ X ^ 2 := by
    simpa only [X] using
      hpair gT gU T U hT hU hTtie hUtie
        hδT_le hδT0 hδT hδU_le hδU0 hδU
        R A D2 D3 hR hA hD2 hD3 hU2 hT3 hTU2 hTU3
  have h9 : 0 ≤ (9 : ℝ) := by norm_num
  calc
    covariantJetNormSq (I := I) (M := M) g 2
        (connectionDifferenceContravariantInsertionField (I := I) g gT -
          connectionDifferenceContravariantInsertionField (I := I) g gU) =
      covariantJetNormSq (I := I) (M := M) g 2
        (reindexCoeffGen (I := I) (M := M) g 3 4
          (slotExtend (I := I) (M := M) g 2 3
            (slotExtend (I := I) (M := M) g 1 2
              (connectionDifferenceSection (I := I) gT g -
                connectionDifferenceSection (I := I) gU g)))
          coreInPerm201) := by
            rw [connIns_sub_eq (I := I) (M := M) g gT gU]
    _ ≤ 9 * covariantJetNormSq (I := I) (M := M) g 2
        (connectionDifferenceSection (I := I) gT g -
          connectionDifferenceSection (I := I) gU g) :=
      insert_h2 (I := I) (M := M) hDim g _
    _ ≤ 9 * X ^ 2 := mul_le_mul_of_nonneg_left hX h9
    _ = (B0 R * D3 + B1 R * D2 + B1 R * A * D2) ^ 2 := by
      simp only [B0, B1, X]
      ring

theorem ricciKer_sub_tame
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M)
    {δ₀ : ℝ} (hδ₀0 : 0 ≤ δ₀) (hδ₀ : δ₀ < 1) :
    ∃ B0 B1 : ℝ → ℝ,
      (∀ R : ℝ, 0 ≤ R → 0 ≤ B0 R) ∧
      (∀ R : ℝ, 0 ≤ R → 0 ≤ B1 R) ∧
      ∀ (gT gU : SmoothRiemannianMetric I M)
        (T U : SmoothCcTensor g 0 2)
        (_hT : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g T x u v =
            ccTensorBilin (I := I) g T x v u)
        (_hU : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g U x u v =
            ccTensorBilin (I := I) g U x v u)
        (_hTtie : ∀ (x : M) (u v : TangentSpace I x),
          gT.inner x u v =
            g.inner x u v + ccTensorBilinSymm (I := I) g T x u v)
        (_hUtie : ∀ (x : M) (u v : TangentSpace I x),
          gU.inner x u v =
            g.inner x u v + ccTensorBilinSymm (I := I) g U x u v)
        {δT δU : ℝ}
        (_hδT_le : δT ≤ δ₀) (_hδT0 : 0 ≤ δT)
        (_hδT : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) δT)
        (_hδU_le : δU ≤ δ₀) (_hδU0 : 0 ≤ δU)
        (_hδU : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g U) δU)
        (R A D2 D3 : ℝ),
        0 ≤ R → 0 ≤ A → 0 ≤ D2 → 0 ≤ D3 →
        covariantJetNormSq (I := I) (M := M) g 2 U ≤ R ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 3 T ≤ A ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 2 (T - U) ≤ D2 ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 3 (T - U) ≤ D3 ^ 2 →
      covariantJetNormSq (I := I) (M := M) g 2
          (linearizedRicciConnectionDifferenceOrder1KernelField (I := I) g gT -
            linearizedRicciConnectionDifferenceOrder1KernelField (I := I) g gU) ≤
        (B0 R * D3 + B1 R * D2 + B1 R * A * D2) ^ 2 := by
  obtain ⟨C0, C1, hC0, hC1, hpair⟩ :=
    connIns_sub_tame (I := I) (M := M) hDim g hδ₀0 hδ₀
  let B0 : ℝ → ℝ := fun R => 5 * C0 R
  let B1 : ℝ → ℝ := fun R => 5 * C1 R
  refine ⟨B0, B1, fun R hR => mul_nonneg (by norm_num) (hC0 R hR),
    fun R hR => mul_nonneg (by norm_num) (hC1 R hR), ?_⟩
  intro gT gU T U hT hU hTtie hUtie
    δT δU hδT_le hδT0 hδT hδU_le hδU0 hδU
    R A D2 D3 hR hA hD2 hD3 hU2 hT3 hTU2 hTU3
  let X : ℝ := C0 R * D3 + C1 R * D2 + C1 R * A * D2
  have hX :
      covariantJetNormSq (I := I) (M := M) g 2
          (connectionDifferenceContravariantInsertionField (I := I) g gT -
            connectionDifferenceContravariantInsertionField (I := I) g gU) ≤ X ^ 2 := by
    simpa only [X] using
      hpair gT gU T U hT hU hTtie hUtie
        hδT_le hδT0 hδT hδU_le hδU0 hδU
        R A D2 D3 hR hA hD2 hD3 hU2 hT3 hTU2 hTU3
  have h25 : 0 ≤ (25 : ℝ) := by norm_num
  calc
    covariantJetNormSq (I := I) (M := M) g 2
        (linearizedRicciConnectionDifferenceOrder1KernelField (I := I) g gT -
          linearizedRicciConnectionDifferenceOrder1KernelField (I := I) g gU) =
      covariantJetNormSq (I := I) (M := M) g 2
        (kerOfIns (I := I) (M := M) g
          (connectionDifferenceContravariantInsertionField (I := I) g gT -
            connectionDifferenceContravariantInsertionField (I := I) g gU)) := by
              rw [ricciKer_sub_eq (I := I) (M := M) g gT gU]
    _ ≤ 25 * covariantJetNormSq (I := I) (M := M) g 2
        (connectionDifferenceContravariantInsertionField (I := I) g gT -
          connectionDifferenceContravariantInsertionField (I := I) g gU) :=
      kerOfIns_h2 (I := I) (M := M) g _
    _ ≤ 25 * X ^ 2 := mul_le_mul_of_nonneg_left hX h25
    _ = (B0 R * D3 + B1 R * D2 + B1 R * A * D2) ^ 2 := by
      simp only [B0, B1, X]
      ring

omit [BoundarylessManifold I M] [NeZero (Module.finrank ℝ E)] [CompactSpace M] in
omit [I.Boundaryless] [SigmaCompactSpace M] in
private theorem raise_rev
    (g gm : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2)
    (htie : ∀ (y : M) (v w : TangentSpace I y),
      gm.inner y v w =
        g.inner y v w + ccTensorBilinSymm (I := I) g T y v w) :
    symmRaiseEndo (I := I) (M := M) g T =
      metricComparisonDifferenceEndomorphismField (I := I) gm g := by
  apply ContMDiffSection.ext
  intro x
  apply ContinuousLinearMap.ext
  intro v
  apply (metricFlatMap (I := I) g x).injective
  ext w
  rw [metricFlatMap_apply, metricFlatMap_apply]
  rw [symmRaiseEndo_apply, inner_symmRaiseEndo]
  rw [show metricComparisonDifferenceEndomorphismField (I := I) gm g x =
      metricComparisonDifferenceEndomorphism (I := I) gm g x from rfl]
  rw [inner_g1_metricComparisonDifferenceEndomorphism (I := I) gm g x v w]
  rw [htie x v w]
  ring

omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
omit [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
private theorem raise_cancel
    (a b : SmoothRiemannianMetric I M) (x : M) :
    (metricComparisonEndomorphism (I := I) a b x).comp
        (metricComparisonEndomorphism (I := I) b a x) =
      ContinuousLinearMap.id ℝ (TangentSpace I x) := by
  apply ContinuousLinearMap.ext
  intro v
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply,
    metricComparisonEndomorphism_apply, metricComparisonEndomorphism_apply]
  rw [g0FlatCLM_inverseMetricSharpFib (I := I) a x
    (g0FlatCLM (I := I) b x v)]
  rw [inverseMetricSharpFib_g0FlatCLM (I := I) b x v]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [BoundarylessManifold I M]
    [I.Boundaryless] [SigmaCompactSpace M] in
private theorem raise_pair
    (g gT gU : SmoothRiemannianMetric I M)
    (T U : SmoothCcTensor g 0 2)
    (hTtie : ∀ (y : M) (v w : TangentSpace I y),
      gT.inner y v w =
        g.inner y v w + ccTensorBilinSymm (I := I) g T y v w)
    (hUtie : ∀ (y : M) (v w : TangentSpace I y),
      gU.inner y v w =
        g.inner y v w + ccTensorBilinSymm (I := I) g U y v w)
    (x : M) :
    metricComparisonEndomorphism (I := I) g gT x -
        metricComparisonEndomorphism (I := I) g gU x =
      -((metricComparisonEndomorphism (I := I) g gT x).comp
        ((symmRaiseEndo (I := I) (M := M) g (T - U) x).comp
          (metricComparisonEndomorphism (I := I) g gU x))) := by
  let FT := metricComparisonEndomorphism (I := I) g gT x
  let FU := metricComparisonEndomorphism (I := I) g gU x
  let RT := metricComparisonEndomorphism (I := I) gT g x
  let RU := metricComparisonEndomorphism (I := I) gU g x
  let PT := symmRaiseEndo (I := I) (M := M) g T x
  let PU := symmRaiseEndo (I := I) (M := M) g U x
  let P := symmRaiseEndo (I := I) (M := M) g (T - U) x
  have hRT : RT = PT + 1 := by
    apply ContinuousLinearMap.ext
    intro v
    have hr := congrArg (fun F => F x)
      (raise_rev (I := I) (M := M) g gT T hTtie)
    have hv := congrArg (fun L => L v) hr
    change metricComparisonEndomorphism (I := I) gT g x v = PT v + v
    rw [metricComparisonEndomorphism_eq_diff_add_id]
    exact congrArg (fun z => z + v) hv.symm
  have hRU : RU = PU + 1 := by
    apply ContinuousLinearMap.ext
    intro v
    have hr := congrArg (fun F => F x)
      (raise_rev (I := I) (M := M) g gU U hUtie)
    have hv := congrArg (fun L => L v) hr
    change metricComparisonEndomorphism (I := I) gU g x v = PU v + v
    rw [metricComparisonEndomorphism_eq_diff_add_id]
    exact congrArg (fun z => z + v) hv.symm
  have hP : P = PT - PU := by
    have hs :
        symmRaiseEndo (I := I) (M := M) g (T - U) =
          symmRaiseEndo (I := I) (M := M) g T -
            symmRaiseEndo (I := I) (M := M) g U := by
      calc
        symmRaiseEndo (I := I) (M := M) g (T - U) =
            symmRaiseEndo (I := I) (M := M) g (T + (-1 : ℝ) • U) := by
              rw [neg_one_smul, sub_eq_add_neg]
        _ = symmRaiseEndo (I := I) (M := M) g T +
              symmRaiseEndo (I := I) (M := M) g ((-1 : ℝ) • U) := by
                rw [symmRaiseEndo_add]
        _ = symmRaiseEndo (I := I) (M := M) g T +
              (-1 : ℝ) • symmRaiseEndo (I := I) (M := M) g U := by
                rw [symmRaiseEndo_smul]
        _ = symmRaiseEndo (I := I) (M := M) g T -
              symmRaiseEndo (I := I) (M := M) g U := by
                simpa only [sub_eq_add_neg] using
                  congrArg
                    (fun z => symmRaiseEndo (I := I) (M := M) g T + z)
                    (neg_one_smul ℝ
                      (symmRaiseEndo (I := I) (M := M) g U))
    exact congrArg (fun F => F x) hs
  have hFTC : FT * RT = 1 := by
    simpa only [FT, RT, ContinuousLinearMap.mul_def, ContinuousLinearMap.one_def] using
      raise_cancel (I := I) (M := M) g gT x
  have hUCF : RU * FU = 1 := by
    simpa only [RU, FU, ContinuousLinearMap.mul_def, ContinuousLinearMap.one_def] using
      raise_cancel (I := I) (M := M) gU g x
  change FT - FU = -(FT.comp (P.comp FU))
  rw [show FT.comp (P.comp FU) = FT * P * FU by
    simp only [ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_assoc]]
  calc
    FT - FU = FT * (RU * FU) - (FT * RT) * FU := by
      rw [hUCF, hFTC, mul_one, one_mul]
    _ = FT * (RU - RT) * FU := by noncomm_ring
    _ = -(FT * P * FU) := by
      rw [hRT, hRU, hP]
      noncomm_ring

private noncomputable def perturb0
    (g : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2) :
    SmoothCcTensor g 1 1 :=
  endoSlotZeroCcTensor (I := I) (M := M) g 0
    (symmRaiseEndo (I := I) (M := M) g T)

omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M]
    [I.Boundaryless] [SigmaCompactSpace M] in
private theorem sharp_pair
    (g gT gU : SmoothRiemannianMetric I M)
    (T U : SmoothCcTensor g 0 2)
    (hTtie : ∀ (y : M) (v w : TangentSpace I y),
      gT.inner y v w =
        g.inner y v w + ccTensorBilinSymm (I := I) g T y v w)
    (hUtie : ∀ (y : M) (v w : TangentSpace I y),
      gU.inner y v w =
        g.inner y v w + ccTensorBilinSymm (I := I) g U y v w) :
    sharpFlatEndoCc (I := I) g gT -
        sharpFlatEndoCc (I := I) g gU =
      -ccOperatorFieldComp (I := I) (M := M) g 1 1 1
        (sharpFlatEndoCc (I := I) g gU)
        (ccOperatorFieldComp (I := I) (M := M) g 1 1 1
          (perturb0 (I := I) (M := M) g (T - U))
          (sharpFlatEndoCc (I := I) g gT)) := by
  rw [sharp_eq_slot0 (I := I) (M := M) g gT,
    sharp_eq_slot0 (I := I) (M := M) g gU,
    ← slotInsertEndoCc_sub]
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rw [SmoothCcTensor.toSection_neg]
  simp only [ContMDiffSection.coe_neg, Pi.neg_apply]
  rw [operatorFieldComposition_toSection, operatorFieldComposition_toSection]
  simp only [perturb0, slotInsertEndoCc_toSection,
    metricComparisonEndomorphismField_apply]
  rw [slotInsertFib_comp, slotInsertFib_comp]
  rw [ContMDiffSection.coe_sub, Pi.sub_apply]
  have hinv :
      metricComparisonDifferenceEndomorphismField (I := I) g gT x -
          metricComparisonDifferenceEndomorphismField (I := I) g gU x =
        metricComparisonEndomorphism (I := I) g gT x -
          metricComparisonEndomorphism (I := I) g gU x := by
    apply ContinuousLinearMap.ext
    intro v
    simp only [sub_apply,
      metricComparisonEndomorphism_eq_diff_add_id]
    abel
  rw [show metricComparisonEndomorphismField (I := I) (M := M) g gT x -
        metricComparisonEndomorphismField (I := I) (M := M) g gU x =
      metricComparisonDifferenceEndomorphismField (I := I) g gT x -
        metricComparisonDifferenceEndomorphismField (I := I) g gU x by
    apply ContinuousLinearMap.ext
    intro v
    rw [metricComparisonEndomorphismField_apply, metricComparisonEndomorphismField_apply]
    simp only [metricComparisonEndomorphism_eq_diff_add_id,
      sub_apply]
    abel]
  rw [hinv]
  rw [raise_pair (I := I) (M := M) g gT gU T U hTtie hUtie x]
  rw [show -((metricComparisonEndomorphism (I := I) g gT x).comp
        ((symmRaiseEndo (I := I) (M := M) g (T - U) x).comp
          (metricComparisonEndomorphism (I := I) g gU x))) =
      (-1 : ℝ) • ((metricComparisonEndomorphism (I := I) g gT x).comp
        ((symmRaiseEndo (I := I) (M := M) g (T - U) x).comp
          (metricComparisonEndomorphism (I := I) g gU x))) by rw [neg_one_smul],
    slotInsertEndoFib_smul_left, neg_one_smul]
  rw [ContinuousLinearMap.comp_assoc]

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
private theorem jet_add1
    (g : SmoothRiemannianMetric I M) {r s : ℕ} (m : ℕ)
    (S V : SmoothCcTensor g r s) :
    covariantJetNormSq (I := I) (M := M) g m (S + V) ≤
      2 * (covariantJetNormSq (I := I) (M := M) g m S +
        covariantJetNormSq (I := I) (M := M) g m V) := by
  unfold covariantJetNormSq
  calc
    ∑ q ∈ Finset.range (m + 1),
        ‖iteratedCovGrad (I := I) g r s q (S + V)‖ ^ 2 ≤
      ∑ q ∈ Finset.range (m + 1),
        2 * (‖iteratedCovGrad (I := I) g r s q S‖ ^ 2 +
          ‖iteratedCovGrad (I := I) g r s q V‖ ^ 2) := by
      refine Finset.sum_le_sum fun q _ => ?_
      rw [iteratedCovGrad_add]
      have htri := norm_add_le
        (iteratedCovGrad (I := I) g r s q S)
        (iteratedCovGrad (I := I) g r s q V)
      calc
        ‖iteratedCovGrad (I := I) g r s q S +
            iteratedCovGrad (I := I) g r s q V‖ ^ 2 ≤
          (‖iteratedCovGrad (I := I) g r s q S‖ +
            ‖iteratedCovGrad (I := I) g r s q V‖) ^ 2 :=
              pow_le_pow_left₀ (norm_nonneg _) htri 2
        _ ≤ 2 * (‖iteratedCovGrad (I := I) g r s q S‖ ^ 2 +
            ‖iteratedCovGrad (I := I) g r s q V‖ ^ 2) := by
          nlinarith [sq_nonneg
            (‖iteratedCovGrad (I := I) g r s q S‖ -
              ‖iteratedCovGrad (I := I) g r s q V‖)]
    _ = 2 * ((∑ q ∈ Finset.range (m + 1),
          ‖iteratedCovGrad (I := I) g r s q S‖ ^ 2) +
        ∑ q ∈ Finset.range (m + 1),
          ‖iteratedCovGrad (I := I) g r s q V‖ ^ 2) := by
      simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum]

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
private theorem jet_smul1
    (g : SmoothRiemannianMetric I M) {r s : ℕ} (m : ℕ)
    (c : ℝ) (S : SmoothCcTensor g r s) :
    covariantJetNormSq (I := I) (M := M) g m (c • S) =
      c ^ 2 * covariantJetNormSq (I := I) (M := M) g m S := by
  unfold covariantJetNormSq
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro q _
  rw [iteratedCovGrad_smul, norm_smul, Real.norm_eq_abs,
    mul_pow, sq_abs]

omit [NeZero (Module.finrank ℝ E)] in
private theorem reindex_h2_eq
    (g : SmoothRiemannianMetric I M) {r s : ℕ}
    (S : SmoothCcTensor g r s) (ρ : Equiv.Perm (Fin r)) :
    covariantJetNormSq (I := I) (M := M) g 2
        (reindexCoeffGen (I := I) (M := M) g r s S ρ) =
      covariantJetNormSq (I := I) (M := M) g 2 S := by
  unfold covariantJetNormSq
  apply Finset.sum_congr rfl
  intro q _
  rw [iteratedCovGrad_reindexCoeffGen (I := I) (M := M),
    norm_reindexCoeffGen_eq (I := I) (M := M)]

private theorem corrPk3_h2
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M)
    (P : SmoothCcTensor g 0 2) :
    covariantJetNormSq (I := I) (M := M) g 2
        (corrPk3 (I := I) (M := M) g P) ≤
      27 * covariantJetNormSq (I := I) (M := M) g 2 P := by
  let fr : ℝ := Module.finrank ℝ E
  have hper : ∀ q : ℕ,
      ‖iteratedCovGrad (I := I) g 3 5 q
          (corrPk3 (I := I) (M := M) g P)‖ ≤
        Real.sqrt fr *
          (Real.sqrt fr *
            (Real.sqrt fr *
              ‖iteratedCovGrad (I := I) g 0 2 q P‖)) := by
    intro q
    calc
      ‖iteratedCovGrad (I := I) g 3 5 q
          (corrPk3 (I := I) (M := M) g P)‖ ≤
        Real.sqrt (Module.finrank ℝ E) *
          ‖iteratedCovGrad (I := I) g 2 4 q
            (slotExtend (I := I) (M := M) g 1 3
              (slotExtend (I := I) (M := M) g 0 2 P))‖ := by
            simpa only [corrPk3, fr] using
              slotExt_norm_le (I := I) (M := M) g 2 4 q
                (slotExtend (I := I) (M := M) g 1 3
                  (slotExtend (I := I) (M := M) g 0 2 P))
      _ ≤ Real.sqrt fr *
          (Real.sqrt fr *
            ‖iteratedCovGrad (I := I) g 1 3 q
              (slotExtend (I := I) (M := M) g 0 2 P)‖) := by
            exact mul_le_mul_of_nonneg_left
              (slotExt_norm_le (I := I) (M := M) g 1 3 q
                (slotExtend (I := I) (M := M) g 0 2 P))
              (Real.sqrt_nonneg _)
      _ ≤ Real.sqrt fr *
          (Real.sqrt fr *
            (Real.sqrt fr *
              ‖iteratedCovGrad (I := I) g 0 2 q P‖)) := by
            exact mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left
                (slotExt_norm_le (I := I) (M := M) g 0 2 q P)
                (Real.sqrt_nonneg _))
              (Real.sqrt_nonneg _)
  have hsq : ∀ q : ℕ,
      ‖iteratedCovGrad (I := I) g 3 5 q
          (corrPk3 (I := I) (M := M) g P)‖ ^ 2 ≤
        27 * ‖iteratedCovGrad (I := I) g 0 2 q P‖ ^ 2 := by
    intro q
    have h := pow_le_pow_left₀
      (norm_nonneg
        (iteratedCovGrad (I := I) g 3 5 q
          (corrPk3 (I := I) (M := M) g P)))
      (hper q) 2
    have hs : Real.sqrt ((3 : ℕ) : ℝ) ^ 2 = 3 :=
      Real.sq_sqrt (by norm_num)
    calc
      ‖iteratedCovGrad (I := I) g 3 5 q
          (corrPk3 (I := I) (M := M) g P)‖ ^ 2 ≤
        (Real.sqrt fr *
          (Real.sqrt fr *
            (Real.sqrt fr *
              ‖iteratedCovGrad (I := I) g 0 2 q P‖))) ^ 2 := h
      _ = 27 * ‖iteratedCovGrad (I := I) g 0 2 q P‖ ^ 2 := by
        simp only [fr, hDim]
        rw [show
          (Real.sqrt ((3 : ℕ) : ℝ) *
            (Real.sqrt ((3 : ℕ) : ℝ) *
              (Real.sqrt ((3 : ℕ) : ℝ) *
                ‖iteratedCovGrad (I := I) g 0 2 q P‖))) ^ 2 =
            (Real.sqrt ((3 : ℕ) : ℝ) ^ 2) ^ 3 *
              ‖iteratedCovGrad (I := I) g 0 2 q P‖ ^ 2 by ring,
          hs]
        norm_num
  unfold covariantJetNormSq
  calc
    ∑ q ∈ Finset.range 3,
        ‖iteratedCovGrad (I := I) g 3 5 q
          (corrPk3 (I := I) (M := M) g P)‖ ^ 2 ≤
      ∑ q ∈ Finset.range 3,
        27 * ‖iteratedCovGrad (I := I) g 0 2 q P‖ ^ 2 :=
      Finset.sum_le_sum fun q _ => hsq q
    _ = 27 * ∑ q ∈ Finset.range 3,
        ‖iteratedCovGrad (I := I) g 0 2 q P‖ ^ 2 := by
      rw [Finset.mul_sum]

private theorem corrPhi_h2
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (P : SmoothCcTensor g 0 2) (σ : Equiv.Perm (Fin 5)),
        covariantJetNormSq (I := I) (M := M) g 2
            (corrPhi (I := I) (M := M) g P σ) ≤
          C * covariantJetNormSq (I := I) (M := M) g 2 P := by
  obtain ⟨Ca, hCa, happ⟩ :=
    app_h2_mul (I := I) (M := M) hDim g 3 5 3
  let J : ℝ := covariantJetNormSq (I := I) (M := M) g 2
    (cometricDoubleTraceField (I := I) g 3)
  let C : ℝ := 27 * Ca * J
  have hJ : 0 ≤ J :=
    jet_nonneg (I := I) (M := M) g
      (cometricDoubleTraceField (I := I) g 3)
  have hC : 0 ≤ C :=
    mul_nonneg (mul_nonneg (by norm_num) hCa) hJ
  refine ⟨C, hC, ?_⟩
  intro P σ
  have hpk := corrPk3_h2 (I := I) (M := M) hDim g P
  have hraw := happ
    (reindexCoeffGen (I := I) (M := M) g 5 3
      (cometricDoubleTraceField (I := I) g 3) σ)
    (corrPk3 (I := I) (M := M) g P)
  rw [reindex_h2_eq (I := I) (M := M) g
    (cometricDoubleTraceField (I := I) g 3) σ] at hraw
  calc
    covariantJetNormSq (I := I) (M := M) g 2
        (corrPhi (I := I) (M := M) g P σ) ≤
      Ca * J *
        covariantJetNormSq (I := I) (M := M) g 2
          (corrPk3 (I := I) (M := M) g P) := by
            simpa only [corrPhi, J] using hraw
    _ ≤ Ca * J *
        (27 * covariantJetNormSq (I := I) (M := M) g 2 P) :=
      mul_le_mul_of_nonneg_left hpk (mul_nonneg hCa hJ)
    _ = C * covariantJetNormSq (I := I) (M := M) g 2 P := by
      simp only [C]
      ring

private noncomputable def fourOf
    (g : SmoothRiemannianMetric I M) (P : SmoothCcTensor g 4 2) :
    SmoothCcTensor g 4 2 :=
  ((1 : ℝ) / 2) •
    (reindexCoeffGen (I := I) (M := M) g 4 2 P
        fourTraceArgPerm0231 +
      reindexCoeffGen (I := I) (M := M) g 4 2 P
        fourTraceArgPerm0321 -
      P -
      reindexCoeffGen (I := I) (M := M) g 4 2 P
        fourTraceArgPerm2301)

omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] [SigmaCompactSpace M] in
omit [I.Boundaryless] in
private theorem pure_eq_trace1
    (g gm : SmoothRiemannianMetric I M) :
    cometricDoubleTraceCoefficient (I := I) (M := M) g gm =
      pureTrace (I := I) (M := M) g gm 2 := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rw [cometricDoubleTraceCoefficient_toSection, pureTrace_toSection]

omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] [SigmaCompactSpace M] in
omit [I.Boundaryless] in
private theorem four_eq
    (g gm : SmoothRiemannianMetric I M) :
    ricciCometricFourTraceCastG0 (I := I) g gm =
      fourOf (I := I) (M := M) g
        (pureTrace (I := I) (M := M) g gm 2) := by
  rw [← pure_eq_trace1 (I := I) (M := M) g gm]
  exact ricciCometricFourTraceCastG0_eq_reindex_combination
    (I := I) g gm

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M]
    [SigmaCompactSpace M] in
private theorem four_sub
    (g : SmoothRiemannianMetric I M) (P Q : SmoothCcTensor g 4 2) :
    fourOf (I := I) (M := M) g (P - Q) =
      fourOf (I := I) (M := M) g P -
        fourOf (I := I) (M := M) g Q := by
  simp only [fourOf, reindex_sub_c1 (I := I) (M := M) g 4 2,
    smul_sub]
  module

omit [NeZero (Module.finrank ℝ E)] in
private theorem four_h2
    (g : SmoothRiemannianMetric I M) (P : SmoothCcTensor g 4 2) :
    covariantJetNormSq (I := I) (M := M) g 2
        (fourOf (I := I) (M := M) g P) ≤
      22 * covariantJetNormSq (I := I) (M := M) g 2 P := by
  let R₁ : SmoothCcTensor g 4 2 :=
    reindexCoeffGen (I := I) (M := M) g 4 2 P
      fourTraceArgPerm0231
  let R₂ : SmoothCcTensor g 4 2 :=
    reindexCoeffGen (I := I) (M := M) g 4 2 P
      fourTraceArgPerm0321
  let R₃ : SmoothCcTensor g 4 2 :=
    reindexCoeffGen (I := I) (M := M) g 4 2 P
      fourTraceArgPerm2301
  have hR₁ :
      covariantJetNormSq (I := I) (M := M) g 2 R₁ =
        covariantJetNormSq (I := I) (M := M) g 2 P :=
    reindex_h2_eq (I := I) (M := M) g P fourTraceArgPerm0231
  have hR₂ :
      covariantJetNormSq (I := I) (M := M) g 2 R₂ =
        covariantJetNormSq (I := I) (M := M) g 2 P :=
    reindex_h2_eq (I := I) (M := M) g P fourTraceArgPerm0321
  have hR₃ :
      covariantJetNormSq (I := I) (M := M) g 2 R₃ =
        covariantJetNormSq (I := I) (M := M) g 2 P :=
    reindex_h2_eq (I := I) (M := M) g P fourTraceArgPerm2301
  have h12 :
      covariantJetNormSq (I := I) (M := M) g 2 (R₁ + R₂) ≤
        4 * covariantJetNormSq (I := I) (M := M) g 2 P := by
    have h := jet_add1 (I := I) (M := M) g 2 R₁ R₂
    rw [hR₁, hR₂] at h
    linarith
  have h123 :
      covariantJetNormSq (I := I) (M := M) g 2 (R₁ + R₂ - P) ≤
        10 * covariantJetNormSq (I := I) (M := M) g 2 P := by
    have h := jet_sub (I := I) (M := M) g 2 (R₁ + R₂) P
    nlinarith [jet_nonneg (I := I) (M := M) (m := 2) g P]
  have h1234 :
      covariantJetNormSq (I := I) (M := M) g 2 (R₁ + R₂ - P - R₃) ≤
        22 * covariantJetNormSq (I := I) (M := M) g 2 P := by
    have h := jet_sub (I := I) (M := M) g 2 (R₁ + R₂ - P) R₃
    rw [hR₃] at h
    nlinarith [jet_nonneg (I := I) (M := M) (m := 2) g P]
  change covariantJetNormSq (I := I) (M := M) g 2
      (((1 : ℝ) / 2) • (R₁ + R₂ - P - R₃)) ≤ _
  rw [jet_smul1]
  calc
    ((1 : ℝ) / 2) ^ 2 *
        covariantJetNormSq (I := I) (M := M) g 2 (R₁ + R₂ - P - R₃) ≤
      covariantJetNormSq (I := I) (M := M) g 2 (R₁ + R₂ - P - R₃) := by
        nlinarith [jet_nonneg (I := I) (M := M) (m := 2) g
          (R₁ + R₂ - P - R₃)]
    _ ≤ 22 * covariantJetNormSq (I := I) (M := M) g 2 P := h1234

omit [NeZero (Module.finrank ℝ E)] in
omit [I.Boundaryless] [SigmaCompactSpace M] in
private theorem linearizedRicciConnectionDifferenceOrderOneCoefficient_sub
    (g gT gU : SmoothRiemannianMetric I M) :
    linearizedRicciConnectionDifferenceOrder1CoeffField (I := I) (M := M) g gT -
        linearizedRicciConnectionDifferenceOrder1CoeffField (I := I) (M := M) g gU =
      ccOperatorFieldComp (I := I) (M := M) g 3 4 2
          (ricciCometricFourTraceCastG0 (I := I) g gU)
          (linearizedRicciConnectionDifferenceOrder1KernelField (I := I) g gT -
            linearizedRicciConnectionDifferenceOrder1KernelField (I := I) g gU) +
        ccOperatorFieldComp (I := I) (M := M) g 3 4 2
          (ricciCometricFourTraceCastG0 (I := I) g gT -
            ricciCometricFourTraceCastG0 (I := I) g gU)
          (linearizedRicciConnectionDifferenceOrder1KernelField (I := I) g gT) := by
  rw [linearizedRicciConnectionDifferenceOrder1CoeffField_eq_ccOperatorFieldComp
      (I := I) (M := M) g gT,
    linearizedRicciConnectionDifferenceOrder1CoeffField_eq_ccOperatorFieldComp
      (I := I) (M := M) g gU,
    operatorFieldComposition_sub_right, operatorFieldComposition_sub_left]
  module

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [SigmaCompactSpace M] in
private theorem connIns_zero
    (g : SmoothRiemannianMetric I M) :
    connectionDifferenceContravariantInsertionField (I := I) g g = 0 := by
  have h := connIns_sub_eq (I := I) (M := M) g g g
  rw [connectionDifferenceContravariantInsertionField_eq_reindex_slotExtend_two
    (I := I) (M := M) g g,
    connectionDifferenceSection_self (I := I) (M := M) g]
  rw [show connectionDifferenceContrInsertionReindexPerm = coreInPerm201 from rfl]
  simpa only [sub_self] using h.symm

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [SigmaCompactSpace M] in
private theorem ricciKer_zero
    (g : SmoothRiemannianMetric I M) :
    linearizedRicciConnectionDifferenceOrder1KernelField (I := I) g g = 0 := by
  have hzero :
      kerOfIns (I := I) (M := M) g
          (0 : SmoothCcTensor g 3 4) = 0 := by
    have h := kerOfIns_sub (I := I) (M := M) g
      (0 : SmoothCcTensor g 3 4) 0
    simpa only [sub_self] using h
  rw [ricciKer_eq (I := I) (M := M) g g,
    connIns_zero (I := I) (M := M) g, hzero]

private theorem twenty_two_sq_le_five_sq (x : ℝ) :
    22 * x ^ 2 ≤ (5 * x) ^ 2 := by
  nlinarith [sq_nonneg x]

private theorem twice_sq_sum_le_double_sum_sq
    {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    2 * (x ^ 2 + y ^ 2) ≤ (2 * (x + y)) ^ 2 := by
  nlinarith [mul_nonneg hx hy]

theorem exists_linearizedRicciConnectionDifferenceOrderOneCoefficient_pairing_secondOrder_bound
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ ρ B0 B1 : ℝ,
      0 < ρ ∧ 0 ≤ B0 ∧ 0 ≤ B1 ∧
      ∀ (gT gU : SmoothRiemannianMetric I M)
        (T U : SmoothCcTensor g 0 2)
        (_hT : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g T x u v =
            ccTensorBilin (I := I) g T x v u)
        (_hU : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g U x u v =
            ccTensorBilin (I := I) g U x v u)
        (_hTtie : ∀ (x : M) (u v : TangentSpace I x),
          gT.inner x u v =
            g.inner x u v + ccTensorBilinSymm (I := I) g T x u v)
        (_hUtie : ∀ (x : M) (u v : TangentSpace I x),
          gU.inner x u v =
            g.inner x u v + ccTensorBilinSymm (I := I) g U x u v)
        {δ : ℝ} (_hδ_le : δ ≤ (1 : ℝ) / 3) (_hδ0 : 0 ≤ δ)
        (_hδT : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) δ)
        (_hδU : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g U) δ)
        (_hδZ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g
            (0 : SmoothCcTensor g 0 2)) δ),
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ ≤ ρ →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) U‖ ≤ ρ →
        ∀ (A D3 : ℝ), 0 ≤ A → 0 ≤ D3 →
        covariantJetNormSq (I := I) (M := M) g 3 T ≤ A ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 3 (T - U) ≤ D3 ^ 2 →
      let D2 :=
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) (T - U)‖
      covariantJetNormSq (I := I) (M := M) g 2
          (linearizedRicciConnectionDifferenceOrder1CoeffField
              (I := I) (M := M) g gT -
            linearizedRicciConnectionDifferenceOrder1CoeffField
              (I := I) (M := M) g gU) ≤
        (B0 * D3 + B1 * D2 + B1 * A * D2) ^ 2 := by
  obtain ⟨ρp, Cp, hρp, hCp, hpurePair⟩ :=
    RicciDeTurckLowOrder.trace2_pair_h2 (I := I) (M := M) hDim g
  obtain ⟨ρb, Cb, hρb, hCb, hpureBdd⟩ :=
    RicciDeTurckLowOrder.trace_two_sobolev_two_bound (I := I) (M := M) hDim g
  obtain ⟨Ch, hCh, hhs⟩ :=
    hs2_low2 (I := I) (M := M) g 2
  obtain ⟨K0, K1, hK0, hK1, hker⟩ :=
    ricciKer_sub_tame (I := I) (M := M) hDim g
      (δ₀ := (1 : ℝ) / 3) (by norm_num) (by norm_num)
  obtain ⟨Ca, hCa, happ⟩ :=
    app_h2_mul (I := I) (M := M) hDim g 3 4 2
  let ρ : ℝ := min ρp ρb
  let R0 : ℝ := Ch * ρ
  let X0 : ℝ := K0 R0
  let X1 : ℝ := K1 R0 * Ch
  let Y0 : ℝ := K0 0 + K1 0 + K1 0 * R0
  let H0 : ℝ := Real.sqrt Ca
  let H : ℝ := 2 * H0
  let B0 : ℝ := H * (5 * Cb * X0)
  let B1 : ℝ := H * (5 * Cb * X1 + 5 * Cp * Y0)
  have hρ : 0 < ρ := lt_min hρp hρb
  have hR0 : 0 ≤ R0 := mul_nonneg hCh hρ.le
  have hX0 : 0 ≤ X0 := hK0 R0 hR0
  have hX1 : 0 ≤ X1 := mul_nonneg (hK1 R0 hR0) hCh
  have hY0 : 0 ≤ Y0 := by
    exact add_nonneg
      (add_nonneg (hK0 0 (by norm_num)) (hK1 0 (by norm_num)))
      (mul_nonneg (hK1 0 (by norm_num)) hR0)
  have hH0 : 0 ≤ H0 := Real.sqrt_nonneg _
  have hH0sq : H0 ^ 2 = Ca := by
    simpa only [H0] using Real.sq_sqrt hCa
  have hH : 0 ≤ H := mul_nonneg (by norm_num) hH0
  have hB0 : 0 ≤ B0 :=
    mul_nonneg hH (mul_nonneg (mul_nonneg (by norm_num) hCb) hX0)
  have hB1 : 0 ≤ B1 :=
    mul_nonneg hH
      (add_nonneg
        (mul_nonneg (mul_nonneg (by norm_num) hCb) hX1)
        (mul_nonneg (mul_nonneg (by norm_num) hCp) hY0))
  refine ⟨ρ, B0, B1, hρ, hB0, hB1, ?_⟩
  intro gT gU T U hT hU hTtie hUtie δ hδ_le hδ0
    hδT hδU hδZ hTHs hUHs A D3 hA hD3 hT3 hTU3
  dsimp only
  let N : ℝ :=
    ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) (T - U)‖
  let TrT : SmoothCcTensor g 4 2 :=
    ricciCometricFourTraceCastG0 (I := I) g gT
  let TrU : SmoothCcTensor g 4 2 :=
    ricciCometricFourTraceCastG0 (I := I) g gU
  let KT : SmoothCcTensor g 3 4 :=
    linearizedRicciConnectionDifferenceOrder1KernelField (I := I) g gT
  let KU : SmoothCcTensor g 3 4 :=
    linearizedRicciConnectionDifferenceOrder1KernelField (I := I) g gU
  let XD : ℝ := X0 * D3 + X1 * N + X1 * A * N
  let YT : ℝ := Y0 * A
  have hN : 0 ≤ N := norm_nonneg _
  have hTHsp : ‖ccTensorToHs (I := I) (M := M) g 2
      (2 : ℝ) T‖ ≤ ρp := hTHs.trans (min_le_left _ _)
  have hUHsp : ‖ccTensorToHs (I := I) (M := M) g 2
      (2 : ℝ) U‖ ≤ ρp := hUHs.trans (min_le_left _ _)
  have hTHsb : ‖ccTensorToHs (I := I) (M := M) g 2
      (2 : ℝ) T‖ ≤ ρb := hTHs.trans (min_le_right _ _)
  have hUHsb : ‖ccTensorToHs (I := I) (M := M) g 2
      (2 : ℝ) U‖ ≤ ρb := hUHs.trans (min_le_right _ _)
  have hpD := hpurePair T U gT gU hTtie hUtie hTHsp hUHsp
  have hpU := hpureBdd U gU hUtie hUHsb
  have hTrD :
      covariantJetNormSq (I := I) (M := M) g 2 (TrT - TrU) ≤
        (5 * Cp * N) ^ 2 := by
    have heq : TrT - TrU =
        fourOf (I := I) (M := M) g
          (pureTrace (I := I) (M := M) g gT 2 -
            pureTrace (I := I) (M := M) g gU 2) := by
      rw [show TrT =
          fourOf (I := I) (M := M) g
            (pureTrace (I := I) (M := M) g gT 2) by
            exact four_eq (I := I) (M := M) g gT,
        show TrU =
          fourOf (I := I) (M := M) g
            (pureTrace (I := I) (M := M) g gU 2) by
            exact four_eq (I := I) (M := M) g gU,
        ← four_sub]
    rw [heq]
    calc
      covariantJetNormSq (I := I) (M := M) g 2
          (fourOf (I := I) (M := M) g
            (pureTrace (I := I) (M := M) g gT 2 -
              pureTrace (I := I) (M := M) g gU 2)) ≤
        22 * covariantJetNormSq (I := I) (M := M) g 2
          (pureTrace (I := I) (M := M) g gT 2 -
            pureTrace (I := I) (M := M) g gU 2) :=
        four_h2 (I := I) (M := M) g _
      _ ≤ 22 * (Cp * N) ^ 2 := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        simpa only [N] using hpD
      _ ≤ (5 * Cp * N) ^ 2 := by
        simpa only [mul_assoc] using
          twenty_two_sq_le_five_sq (Cp * N)
  have hTrU :
      covariantJetNormSq (I := I) (M := M) g 2 TrU ≤
        (5 * Cb) ^ 2 := by
    rw [show TrU =
        fourOf (I := I) (M := M) g
          (pureTrace (I := I) (M := M) g gU 2) by
      exact four_eq (I := I) (M := M) g gU]
    calc
      covariantJetNormSq (I := I) (M := M) g 2
          (fourOf (I := I) (M := M) g
            (pureTrace (I := I) (M := M) g gU 2)) ≤
        22 * covariantJetNormSq (I := I) (M := M) g 2
          (pureTrace (I := I) (M := M) g gU 2) :=
        four_h2 (I := I) (M := M) g _
      _ ≤ 22 * Cb ^ 2 :=
        mul_le_mul_of_nonneg_left hpU (by norm_num)
      _ ≤ (5 * Cb) ^ 2 := twenty_two_sq_le_five_sq Cb
  have hU2 :
      covariantJetNormSq (I := I) (M := M) g 2 U ≤ R0 ^ 2 := by
    calc
      covariantJetNormSq (I := I) (M := M) g 2 U ≤
          (Ch * ‖ccTensorToHs (I := I) (M := M) g 2
            (2 : ℝ) U‖) ^ 2 := by
        simpa only [covariantJetNormSq, Nat.reduceAdd] using hhs U
      _ ≤ (Ch * ρ) ^ 2 :=
        pow_le_pow_left₀
          (mul_nonneg hCh (norm_nonneg _))
          (mul_le_mul_of_nonneg_left hUHs hCh) 2
      _ = R0 ^ 2 := rfl
  have hTU2 :
      covariantJetNormSq (I := I) (M := M) g 2 (T - U) ≤
        (Ch * N) ^ 2 := by
    simpa only [covariantJetNormSq, Nat.reduceAdd, N] using hhs (T - U)
  have hKD :
      covariantJetNormSq (I := I) (M := M) g 2 (KT - KU) ≤ XD ^ 2 := by
    have hraw := hker gT gU T U hT hU hTtie hUtie
      hδ_le hδ0 hδT hδ_le hδ0 hδU
      R0 A (Ch * N) D3 hR0 hA (mul_nonneg hCh hN) hD3
      hU2 hT3 hTU2 hTU3
    convert hraw using 1
    simp only [XD, X0, X1]
    ring
  let JT2 : ℝ := covariantJetNormSq (I := I) (M := M) g 2 T
  let DT : ℝ := Real.sqrt JT2
  have hJT2 : 0 ≤ JT2 := by
    exact jet_nonneg (I := I) (M := M) (m := 2) g T
  have hDT : 0 ≤ DT := Real.sqrt_nonneg _
  have hDTsq : DT ^ 2 = JT2 := by
    simpa only [DT] using Real.sq_sqrt hJT2
  have hJT23 : JT2 ≤ covariantJetNormSq (I := I) (M := M) g 3 T := by
    simpa only [JT2] using
      jet_mono (I := I) (M := M) g (by omega : 2 ≤ 3) T
  have hDTA : DT ≤ A := by
    apply le_of_sq_le_sq
    · rw [hDTsq]
      exact hJT23.trans hT3
    · exact hA
  have hT2R :
      JT2 ≤ R0 ^ 2 := by
    calc
      JT2 ≤ (Ch * ‖ccTensorToHs (I := I) (M := M) g 2
          (2 : ℝ) T‖) ^ 2 := by
        simpa only [JT2, covariantJetNormSq, Nat.reduceAdd] using hhs T
      _ ≤ (Ch * ρ) ^ 2 :=
        pow_le_pow_left₀
          (mul_nonneg hCh (norm_nonneg _))
          (mul_le_mul_of_nonneg_left hTHs hCh) 2
      _ = R0 ^ 2 := rfl
  have hDTR : DT ≤ R0 := by
    apply le_of_sq_le_sq
    · rw [hDTsq]
      exact hT2R
    · exact hR0
  have hZsymm : ∀ (x : M) (u v : TangentSpace I x),
      ccTensorBilin (I := I) g
          (0 : SmoothCcTensor g 0 2) x u v =
        ccTensorBilin (I := I) g
          (0 : SmoothCcTensor g 0 2) x v u := by
    intro x u v
    rw [ccTensorBilin_zero, ccTensorBilin_zero]
  have hZtie : ∀ (x : M) (u v : TangentSpace I x),
      g.inner x u v =
        g.inner x u v +
          ccTensorBilinSymm (I := I) g
            (0 : SmoothCcTensor g 0 2) x u v := by
    intro x u v
    rw [ccTensorBilinSymm_apply, ccTensorBilin_zero,
      ccTensorBilin_zero]
    ring
  have hzero2 :
      covariantJetNormSq (I := I) (M := M) g 2
          (0 : SmoothCcTensor g 0 2) = 0 := by
    have h := jet_smul1 (I := I) (M := M) g 2 0
      (0 : SmoothCcTensor g 0 2)
    simpa using h
  have hKTraw := hker gT g T (0 : SmoothCcTensor g 0 2)
    hT hZsymm hTtie hZtie
    hδ_le hδ0 hδT hδ_le hδ0 hδZ
    0 A DT A (by norm_num) hA hDT hA
    (by rw [hzero2]; norm_num)
    hT3
    (by simpa only [sub_zero, JT2] using le_of_eq hDTsq.symm)
    (by simpa only [sub_zero] using hT3)
  have hKTraw' :
      covariantJetNormSq (I := I) (M := M) g 2 KT ≤
        (K0 0 * A + K1 0 * DT + K1 0 * A * DT) ^ 2 := by
    simpa only [KT, ricciKer_zero (I := I) (M := M) g, sub_zero]
      using hKTraw
  have hmid : K1 0 * DT ≤ K1 0 * A :=
    mul_le_mul_of_nonneg_left hDTA (hK1 0 (by norm_num))
  have hlast : K1 0 * A * DT ≤ K1 0 * A * R0 :=
    mul_le_mul_of_nonneg_left hDTR
      (mul_nonneg (hK1 0 (by norm_num)) hA)
  have hamp :
      K0 0 * A + K1 0 * DT + K1 0 * A * DT ≤ YT := by
    calc
      K0 0 * A + K1 0 * DT + K1 0 * A * DT ≤
          K0 0 * A + K1 0 * A + K1 0 * A * R0 :=
        add_le_add (add_le_add le_rfl hmid) hlast
      _ = YT := by
        simp only [YT, Y0]
        ring
  have hamp0 :
      0 ≤ K0 0 * A + K1 0 * DT + K1 0 * A * DT :=
    add_nonneg
      (add_nonneg (mul_nonneg (hK0 0 (by norm_num)) hA)
        (mul_nonneg (hK1 0 (by norm_num)) hDT))
      (mul_nonneg (mul_nonneg (hK1 0 (by norm_num)) hA) hDT)
  have hKT :
      covariantJetNormSq (I := I) (M := M) g 2 KT ≤ YT ^ 2 :=
    hKTraw'.trans (pow_le_pow_left₀ hamp0 hamp 2)
  let Z1 : ℝ := H0 * (5 * Cb) * XD
  let Z2 : ℝ := H0 * (5 * Cp) * YT * N
  have hXD : 0 ≤ XD :=
    add_nonneg
      (add_nonneg (mul_nonneg hX0 hD3)
        (mul_nonneg hX1 hN))
      (mul_nonneg (mul_nonneg hX1 hA) hN)
  have hYT : 0 ≤ YT := mul_nonneg hY0 hA
  have hZ1 : 0 ≤ Z1 :=
    mul_nonneg
      (mul_nonneg hH0 (mul_nonneg (by norm_num) hCb)) hXD
  have hZ2 : 0 ≤ Z2 :=
    mul_nonneg
      (mul_nonneg
        (mul_nonneg hH0 (mul_nonneg (by norm_num) hCp)) hYT) hN
  let V1 : SmoothCcTensor g 3 2 :=
    ccOperatorFieldComp (I := I) (M := M) g 3 4 2 TrU (KT - KU)
  let V2 : SmoothCcTensor g 3 2 :=
    ccOperatorFieldComp (I := I) (M := M) g 3 4 2 (TrT - TrU) KT
  have hV1 :
      covariantJetNormSq (I := I) (M := M) g 2 V1 ≤ Z1 ^ 2 := by
    calc
      covariantJetNormSq (I := I) (M := M) g 2 V1 ≤
          Ca * covariantJetNormSq (I := I) (M := M) g 2 TrU *
            covariantJetNormSq (I := I) (M := M) g 2 (KT - KU) := by
        simpa only [V1] using happ TrU (KT - KU)
      _ ≤ Ca * (5 * Cb) ^ 2 * XD ^ 2 := by
        exact mul_le_mul
          (mul_le_mul_of_nonneg_left hTrU hCa) hKD
          (jet_nonneg (I := I) (M := M) (m := 2) g (KT - KU))
          (mul_nonneg hCa (sq_nonneg (5 * Cb)))
      _ = Z1 ^ 2 := by
        simp only [Z1]
        rw [← hH0sq]
        ring
  have hV2 :
      covariantJetNormSq (I := I) (M := M) g 2 V2 ≤ Z2 ^ 2 := by
    calc
      covariantJetNormSq (I := I) (M := M) g 2 V2 ≤
          Ca * covariantJetNormSq (I := I) (M := M) g 2 (TrT - TrU) *
            covariantJetNormSq (I := I) (M := M) g 2 KT := by
        simpa only [V2] using happ (TrT - TrU) KT
      _ ≤ Ca * (5 * Cp * N) ^ 2 * YT ^ 2 := by
        exact mul_le_mul
          (mul_le_mul_of_nonneg_left hTrD hCa) hKT
          (jet_nonneg (I := I) (M := M) (m := 2) g KT)
          (mul_nonneg hCa (sq_nonneg (5 * Cp * N)))
      _ = Z2 ^ 2 := by
        simp only [Z2]
        rw [← hH0sq]
        ring
  have hlin :
      2 * (Z1 + Z2) ≤
        B0 * D3 + B1 * N + B1 * A * N := by
    have hextra : 0 ≤ H0 * (5 * Cp * Y0 * N) :=
      by positivity
    calc
      2 * (Z1 + Z2) ≤
          2 * (Z1 + Z2) + 2 * (H0 * (5 * Cp * Y0 * N)) :=
        le_add_of_nonneg_right (mul_nonneg (by norm_num) hextra)
      _ = B0 * D3 + B1 * N + B1 * A * N := by
        simp only [Z1, Z2, B0, B1, H, XD, YT, X0, X1, Y0]
        ring
  have hlin0 : 0 ≤ 2 * (Z1 + Z2) :=
    mul_nonneg (by norm_num) (add_nonneg hZ1 hZ2)
  rw [linearizedRicciConnectionDifferenceOrderOneCoefficient_sub (I := I) (M := M) g gT gU]
  change covariantJetNormSq (I := I) (M := M) g 2 (V1 + V2) ≤ _
  calc
    covariantJetNormSq (I := I) (M := M) g 2 (V1 + V2) ≤
        2 * (covariantJetNormSq (I := I) (M := M) g 2 V1 +
          covariantJetNormSq (I := I) (M := M) g 2 V2) :=
      jet_add1 (I := I) (M := M) g 2 V1 V2
    _ ≤ 2 * (Z1 ^ 2 + Z2 ^ 2) :=
      mul_le_mul_of_nonneg_left (add_le_add hV1 hV2) (by norm_num)
    _ ≤ (2 * (Z1 + Z2)) ^ 2 :=
      twice_sq_sum_le_double_sum_sq hZ1 hZ2
    _ ≤ (B0 * D3 + B1 * N + B1 * A * N) ^ 2 :=
      pow_le_pow_left₀ hlin0 hlin 2

omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] [SigmaCompactSpace M] in
omit [I.Boundaryless] in
private theorem lieTrace_eq
    (g gm : SmoothRiemannianMetric I M)
    (σ : Equiv.Perm (Fin 4)) :
    deTurckLieTraceCoeff (I := I) (M := M) g gm σ =
      reindexCoeffGen (I := I) (M := M) g 4 2
        (pureTrace (I := I) (M := M) g gm 2) σ := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rw [deTurckLieTraceCoeff_toSection, reindexCoeffGen_toSection,
    pureTrace_toSection]
  apply ContinuousLinearMap.ext
  intro D
  rw [reindexCoeffFibGen_apply, deTurckLieTraceFib,
    ContinuousLinearMap.comp_apply, domDomCongrFibPerm_apply]

private theorem slots_h2
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) (Ψ : SmoothCcTensor g 1 2) :
    covariantJetNormSq (I := I) (M := M) g 2
        (slotExtend (I := I) (M := M) g 2 3
          (slotExtend (I := I) (M := M) g 1 2 Ψ)) ≤
      9 * covariantJetNormSq (I := I) (M := M) g 2 Ψ := by
  have h := insert_h2 (I := I) (M := M) hDim g Ψ
  rw [reindex_h2_eq (I := I) (M := M)] at h
  exact h

omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
omit [I.Boundaryless] [SigmaCompactSpace M] in
private theorem liePiece_sub
    (g gT gU : SmoothRiemannianMetric I M)
    (σ : Equiv.Perm (Fin 4)) (ρ : Equiv.Perm (Fin 3))
    (ΨT ΨU : SmoothCcTensor g 1 2) :
    lieArm1Piece (I := I) (M := M) g gT σ ρ ΨT -
        lieArm1Piece (I := I) (M := M) g gU σ ρ ΨU =
      reindexCoeffGen (I := I) (M := M) g 3 2
        (ccOperatorFieldComp (I := I) (M := M) g 3 4 2
            (deTurckLieTraceCoeff (I := I) (M := M) g gU σ)
            (slotExtend (I := I) (M := M) g 2 3
              (slotExtend (I := I) (M := M) g 1 2 (ΨT - ΨU))) +
          ccOperatorFieldComp (I := I) (M := M) g 3 4 2
            (deTurckLieTraceCoeff (I := I) (M := M) g gT σ -
              deTurckLieTraceCoeff (I := I) (M := M) g gU σ)
            (slotExtend (I := I) (M := M) g 2 3
              (slotExtend (I := I) (M := M) g 1 2 ΨT))) ρ := by
  simp only [lieArm1Piece]
  unfold deTurckLieTraceCoeffPiece
  rw [← reindex_sub_c1 (I := I) (M := M) g,
    slotExtend_sub, slotExtend_sub,
    operatorFieldComposition_sub_right, operatorFieldComposition_sub_left]
  congr 1
  module

theorem liePiece_pair
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (gT gU : SmoothRiemannianMetric I M)
        (σ : Equiv.Perm (Fin 4)) (ρ : Equiv.Perm (Fin 3))
        (ΨT ΨU : SmoothCcTensor g 1 2)
        (Tb Td Qt Qd : ℝ),
        0 ≤ Tb → 0 ≤ Td → 0 ≤ Qt → 0 ≤ Qd →
        covariantJetNormSq (I := I) (M := M) g 2
            (deTurckLieTraceCoeff (I := I) (M := M) g gU σ) ≤
          Tb ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 2
            (deTurckLieTraceCoeff (I := I) (M := M) g gT σ -
              deTurckLieTraceCoeff (I := I) (M := M) g gU σ) ≤
          Td ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 2 ΨT ≤ Qt ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 2 (ΨT - ΨU) ≤ Qd ^ 2 →
      covariantJetNormSq (I := I) (M := M) g 2
          (lieArm1Piece (I := I) (M := M) g gT σ ρ ΨT -
            lieArm1Piece (I := I) (M := M) g gU σ ρ ΨU) ≤
        (C * (Tb * Qd + Td * Qt)) ^ 2 := by
  obtain ⟨Ca, hCa, happ⟩ :=
    app_h2_mul (I := I) (M := M) hDim g 3 4 2
  let H : ℝ := Real.sqrt Ca
  let C : ℝ := 6 * H
  have hH : 0 ≤ H := Real.sqrt_nonneg _
  have hHsq : H ^ 2 = Ca := by
    simpa only [H] using Real.sq_sqrt hCa
  have hC : 0 ≤ C := mul_nonneg (by norm_num) hH
  refine ⟨C, hC, ?_⟩
  intro gT gU σ ρ ΨT ΨU Tb Td Qt Qd
    hTb hTd hQt hQd hTb2 hTd2 hQt2 hQd2
  let ST : SmoothCcTensor g 3 4 :=
    slotExtend (I := I) (M := M) g 2 3
      (slotExtend (I := I) (M := M) g 1 2 ΨT)
  let SD : SmoothCcTensor g 3 4 :=
    slotExtend (I := I) (M := M) g 2 3
      (slotExtend (I := I) (M := M) g 1 2 (ΨT - ΨU))
  let V1 : SmoothCcTensor g 3 2 :=
    ccOperatorFieldComp (I := I) (M := M) g 3 4 2
      (deTurckLieTraceCoeff (I := I) (M := M) g gU σ) SD
  let V2 : SmoothCcTensor g 3 2 :=
    ccOperatorFieldComp (I := I) (M := M) g 3 4 2
      (deTurckLieTraceCoeff (I := I) (M := M) g gT σ -
        deTurckLieTraceCoeff (I := I) (M := M) g gU σ) ST
  let Z1 : ℝ := H * Tb * (3 * Qd)
  let Z2 : ℝ := H * Td * (3 * Qt)
  have hSD :
      covariantJetNormSq (I := I) (M := M) g 2 SD ≤ (3 * Qd) ^ 2 := by
    calc
      covariantJetNormSq (I := I) (M := M) g 2 SD ≤
          9 * covariantJetNormSq (I := I) (M := M) g 2 (ΨT - ΨU) :=
        slots_h2 (I := I) (M := M) hDim g _
      _ ≤ 9 * Qd ^ 2 :=
        mul_le_mul_of_nonneg_left hQd2 (by norm_num)
      _ = (3 * Qd) ^ 2 := by ring
  have hST :
      covariantJetNormSq (I := I) (M := M) g 2 ST ≤ (3 * Qt) ^ 2 := by
    calc
      covariantJetNormSq (I := I) (M := M) g 2 ST ≤
          9 * covariantJetNormSq (I := I) (M := M) g 2 ΨT :=
        slots_h2 (I := I) (M := M) hDim g _
      _ ≤ 9 * Qt ^ 2 :=
        mul_le_mul_of_nonneg_left hQt2 (by norm_num)
      _ = (3 * Qt) ^ 2 := by ring
  have hZ1 : 0 ≤ Z1 :=
    mul_nonneg (mul_nonneg hH hTb)
      (mul_nonneg (by norm_num) hQd)
  have hZ2 : 0 ≤ Z2 :=
    mul_nonneg (mul_nonneg hH hTd)
      (mul_nonneg (by norm_num) hQt)
  have hV1 :
      covariantJetNormSq (I := I) (M := M) g 2 V1 ≤ Z1 ^ 2 := by
    calc
      covariantJetNormSq (I := I) (M := M) g 2 V1 ≤
          Ca * covariantJetNormSq (I := I) (M := M) g 2
              (deTurckLieTraceCoeff (I := I) (M := M) g gU σ) *
            covariantJetNormSq (I := I) (M := M) g 2 SD := by
        simpa only [V1] using happ
          (deTurckLieTraceCoeff (I := I) (M := M) g gU σ) SD
      _ ≤ Ca * Tb ^ 2 * (3 * Qd) ^ 2 := by
        exact mul_le_mul
          (mul_le_mul_of_nonneg_left hTb2 hCa) hSD
          (jet_nonneg (I := I) (M := M) (m := 2) g SD)
          (mul_nonneg hCa (sq_nonneg Tb))
      _ = Z1 ^ 2 := by
        simp only [Z1]
        rw [← hHsq]
        ring
  have hV2 :
      covariantJetNormSq (I := I) (M := M) g 2 V2 ≤ Z2 ^ 2 := by
    calc
      covariantJetNormSq (I := I) (M := M) g 2 V2 ≤
          Ca * covariantJetNormSq (I := I) (M := M) g 2
              (deTurckLieTraceCoeff (I := I) (M := M) g gT σ -
                deTurckLieTraceCoeff (I := I) (M := M) g gU σ) *
            covariantJetNormSq (I := I) (M := M) g 2 ST := by
        simpa only [V2] using happ
          (deTurckLieTraceCoeff (I := I) (M := M) g gT σ -
            deTurckLieTraceCoeff (I := I) (M := M) g gU σ) ST
      _ ≤ Ca * Td ^ 2 * (3 * Qt) ^ 2 := by
        exact mul_le_mul
          (mul_le_mul_of_nonneg_left hTd2 hCa) hST
          (jet_nonneg (I := I) (M := M) (m := 2) g ST)
          (mul_nonneg hCa (sq_nonneg Td))
      _ = Z2 ^ 2 := by
        simp only [Z2]
        rw [← hHsq]
        ring
  rw [liePiece_sub (I := I) (M := M) g gT gU σ ρ ΨT ΨU,
    reindex_h2_eq (I := I) (M := M)]
  change covariantJetNormSq (I := I) (M := M) g 2 (V1 + V2) ≤ _
  calc
    covariantJetNormSq (I := I) (M := M) g 2 (V1 + V2) ≤
        2 * (covariantJetNormSq (I := I) (M := M) g 2 V1 +
          covariantJetNormSq (I := I) (M := M) g 2 V2) :=
      jet_add1 (I := I) (M := M) g 2 V1 V2
    _ ≤ 2 * (Z1 ^ 2 + Z2 ^ 2) :=
      mul_le_mul_of_nonneg_left (add_le_add hV1 hV2) (by norm_num)
    _ ≤ (2 * (Z1 + Z2)) ^ 2 := by
      nlinarith [mul_nonneg hZ1 hZ2]
    _ = (C * (Tb * Qd + Td * Qt)) ^ 2 := by
      simp only [C, Z1, Z2]
      ring

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [SigmaCompactSpace M] in
private theorem connBackground_eq
    (g gm : SmoothRiemannianMetric I M) :
    deTurckLieArmOneBackgroundConnectionDifference (I := I) (M := M) g gm g =
      connectionDifferenceSection (I := I) gm g := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rfl

private noncomputable def psiLeft
    (g gm : SmoothRiemannianMetric I M) : SmoothCcTensor g 1 2 :=
  cometricRaiseSlot0Field (I := I) (M := M) g 1
    (domDomCongrSection (I := I) g lieArm1RhoSlot0
      (deTurckLieArmOneBackgroundLoweredConnectionDifference (I := I) (M := M) g gm g))

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
omit [I.Boundaryless] in
private theorem psi_eq
    (g gm : SmoothRiemannianMetric I M) :
    deTurckLieArmOneBackgroundCoefficient (I := I) (M := M) g gm g =
      ccOperatorFieldComp (I := I) (M := M) g 1 1 2
        (psiLeft (I := I) (M := M) g gm)
        (sharpFlatEndoCc (I := I) g gm) := by
  rfl

omit [NeZero (Module.finrank ℝ E)] in
omit [I.Boundaryless] [SigmaCompactSpace M] in
private theorem psi_sub_eq
    (g gT gU : SmoothRiemannianMetric I M) :
    deTurckLieArmOneBackgroundCoefficient (I := I) (M := M) g gT g -
        deTurckLieArmOneBackgroundCoefficient (I := I) (M := M) g gU g =
      ccOperatorFieldComp (I := I) (M := M) g 1 1 2
          (psiLeft (I := I) (M := M) g gT)
          (sharpFlatEndoCc (I := I) g gT -
            sharpFlatEndoCc (I := I) g gU) +
        ccOperatorFieldComp (I := I) (M := M) g 1 1 2
          (psiLeft (I := I) (M := M) g gT -
            psiLeft (I := I) (M := M) g gU)
          (sharpFlatEndoCc (I := I) g gU) := by
  rw [psi_eq (I := I) (M := M) g gT,
    psi_eq (I := I) (M := M) g gU,
    operatorFieldComposition_sub_right, operatorFieldComposition_sub_left]
  module

omit [NeZero (Module.finrank ℝ E)] in
private theorem perturb_h2_eq
    (g : SmoothRiemannianMetric I M) (D : SmoothCcTensor g 0 2)
    (hD : ccTensor02Symm (I := I) (M := M) g D = D) :
    covariantJetNormSq (I := I) (M := M) g 2
        (perturb0 (I := I) (M := M) g D) =
      covariantJetNormSq (I := I) (M := M) g 2 D := by
  rw [show perturb0 (I := I) (M := M) g D =
      cometricRaiseSlot0Field (I := I) (M := M) g 0
        (domDomCongrSection (I := I) g
          (Equiv.swap (0 : Fin 2) 1)
          (ccTensor02Symm (I := I) (M := M) g D)) by
    simpa only [perturb0] using
      insert_symmRaise_eq (I := I) (M := M) g D]
  calc
    covariantJetNormSq (I := I) (M := M) g 2
        (cometricRaiseSlot0Field (I := I) (M := M) g 0
          (domDomCongrSection (I := I) g
            (Equiv.swap (0 : Fin 2) 1)
            (ccTensor02Symm (I := I) (M := M) g D))) =
      covariantJetNormSq (I := I) (M := M) g 2
        (domDomCongrSection (I := I) g
          (Equiv.swap (0 : Fin 2) 1)
          (ccTensor02Symm (I := I) (M := M) g D)) := by
        unfold covariantJetNormSq
        apply Finset.sum_congr rfl
        intro q _
        rw [norm_iteratedCovGrad_cometricRaiseSlot0Field_eq
          (I := I) (M := M) g 0
          (domDomCongrSection (I := I) g
            (Equiv.swap (0 : Fin 2) 1)
            (ccTensor02Symm (I := I) (M := M) g D)) q]
    _ = covariantJetNormSq (I := I) (M := M) g 2
          (ccTensor02Symm (I := I) (M := M) g D) :=
      dom_h2 (I := I) (M := M) g
        (Equiv.swap (0 : Fin 2) 1)
        (ccTensor02Symm (I := I) (M := M) g D)
    _ = covariantJetNormSq (I := I) (M := M) g 2 D := by rw [hD]

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
private theorem jet_neg1
    (g : SmoothRiemannianMetric I M) {r s : ℕ} (m : ℕ)
    (S : SmoothCcTensor g r s) :
    covariantJetNormSq (I := I) (M := M) g m (-S) =
      covariantJetNormSq (I := I) (M := M) g m S := by
  simpa only [neg_one_smul, neg_one_sq, one_mul] using
    jet_smul1 (I := I) (M := M) g m (-1 : ℝ) S

theorem sharp_pair_h2
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M)
    {δ₀ : ℝ} (hδ₀0 : 0 ≤ δ₀) (hδ₀ : δ₀ < 1) :
    ∃ ρ C : ℝ, 0 < ρ ∧ 0 ≤ C ∧
      ∀ (gT gU : SmoothRiemannianMetric I M)
        (T U : SmoothCcTensor g 0 2)
        (_hT : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g T x u v =
            ccTensorBilin (I := I) g T x v u)
        (_hU : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g U x u v =
            ccTensorBilin (I := I) g U x v u)
        (_hTtie : ∀ (x : M) (u v : TangentSpace I x),
          gT.inner x u v =
            g.inner x u v + ccTensorBilinSymm (I := I) g T x u v)
        (_hUtie : ∀ (x : M) (u v : TangentSpace I x),
          gU.inner x u v =
            g.inner x u v + ccTensorBilinSymm (I := I) g U x u v)
        {δT δU : ℝ}
        (_hδT_le : δT ≤ δ₀) (_hδT0 : 0 ≤ δT)
        (_hδT : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) δT)
        (_hδU_le : δU ≤ δ₀) (_hδU0 : 0 ≤ δU)
        (_hδU : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g U) δU),
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ ≤ ρ →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) U‖ ≤ ρ →
      covariantJetNormSq (I := I) (M := M) g 2
          (sharpFlatEndoCc (I := I) g gT -
            sharpFlatEndoCc (I := I) g gU) ≤
        (C * ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ)
          (T - U)‖) ^ 2 := by
  obtain ⟨Ks, hKs, hsharp⟩ :=
    sharp_h2_low (I := I) (M := M) g hδ₀0 hδ₀
  obtain ⟨Ca, hCa, happ⟩ :=
    app_h2_mul (I := I) (M := M) hDim g 1 1 1
  obtain ⟨Ch, hCh, hhs⟩ :=
    hs2_low2 (I := I) (M := M) g 2
  let ρ : ℝ := 1
  let S0 : ℝ := Ks * (1 + Ch ^ 2)
  let C : ℝ := Ca * S0 * Ch
  have hρ : 0 < ρ := by norm_num [ρ]
  have hS0 : 0 ≤ S0 :=
    mul_nonneg hKs (add_nonneg (by norm_num) (sq_nonneg Ch))
  have hC : 0 ≤ C := mul_nonneg (mul_nonneg hCa hS0) hCh
  refine ⟨ρ, C, hρ, hC, ?_⟩
  intro gT gU T U hT hU hTtie hUtie
    δT δU hδT_le hδT0 hδT hδU_le hδU0 hδU hTHs hUHs
  let N : ℝ :=
    ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) (T - U)‖
  let X : SmoothCcTensor g 1 1 :=
    ccOperatorFieldComp (I := I) (M := M) g 1 1 1
      (perturb0 (I := I) (M := M) g (T - U))
      (sharpFlatEndoCc (I := I) g gT)
  let Y : SmoothCcTensor g 1 1 :=
    ccOperatorFieldComp (I := I) (M := M) g 1 1 1
      (sharpFlatEndoCc (I := I) g gU) X
  have hN : 0 ≤ N := norm_nonneg _
  have hT2 :
      covariantJetNormSq (I := I) (M := M) g 2 T ≤ Ch ^ 2 := by
    calc
      covariantJetNormSq (I := I) (M := M) g 2 T ≤
          (Ch * ‖ccTensorToHs (I := I) (M := M) g 2
            (2 : ℝ) T‖) ^ 2 := by
        simpa only [covariantJetNormSq, Nat.reduceAdd] using hhs T
      _ ≤ (Ch * ρ) ^ 2 :=
        pow_le_pow_left₀
          (mul_nonneg hCh (norm_nonneg _))
          (mul_le_mul_of_nonneg_left hTHs hCh) 2
      _ = Ch ^ 2 := by simp only [ρ, mul_one]
  have hU2 :
      covariantJetNormSq (I := I) (M := M) g 2 U ≤ Ch ^ 2 := by
    calc
      covariantJetNormSq (I := I) (M := M) g 2 U ≤
          (Ch * ‖ccTensorToHs (I := I) (M := M) g 2
            (2 : ℝ) U‖) ^ 2 := by
        simpa only [covariantJetNormSq, Nat.reduceAdd] using hhs U
      _ ≤ (Ch * ρ) ^ 2 :=
        pow_le_pow_left₀
          (mul_nonneg hCh (norm_nonneg _))
          (mul_le_mul_of_nonneg_left hUHs hCh) 2
      _ = Ch ^ 2 := by simp only [ρ, mul_one]
  have hST :
      covariantJetNormSq (I := I) (M := M) g 2
          (sharpFlatEndoCc (I := I) g gT) ≤ S0 := by
    calc
      covariantJetNormSq (I := I) (M := M) g 2
          (sharpFlatEndoCc (I := I) g gT) ≤
        Ks * (1 + covariantJetNormSq (I := I) (M := M) g 2 T) :=
          hsharp gT T hT hTtie hδT_le hδT0 hδT
      _ ≤ S0 := by
        dsimp only [S0]
        exact mul_le_mul_of_nonneg_left (add_le_add le_rfl hT2) hKs
  have hSU :
      covariantJetNormSq (I := I) (M := M) g 2
          (sharpFlatEndoCc (I := I) g gU) ≤ S0 := by
    calc
      covariantJetNormSq (I := I) (M := M) g 2
          (sharpFlatEndoCc (I := I) g gU) ≤
        Ks * (1 + covariantJetNormSq (I := I) (M := M) g 2 U) :=
          hsharp gU U hU hUtie hδU_le hδU0 hδU
      _ ≤ S0 := by
        dsimp only [S0]
        exact mul_le_mul_of_nonneg_left (add_le_add le_rfl hU2) hKs
  have hDsymm :
      ccTensor02Symm (I := I) (M := M) g (T - U) = T - U := by
    rw [symmS_sub, symm_eq_self (I := I) (M := M) g T hT,
      symm_eq_self (I := I) (M := M) g U hU]
  have hD2 :
      covariantJetNormSq (I := I) (M := M) g 2 (T - U) ≤
        (Ch * N) ^ 2 := by
    simpa only [covariantJetNormSq, Nat.reduceAdd, N] using hhs (T - U)
  have hP :
      covariantJetNormSq (I := I) (M := M) g 2
          (perturb0 (I := I) (M := M) g (T - U)) ≤
        (Ch * N) ^ 2 := by
    rw [perturb_h2_eq (I := I) (M := M) g (T - U) hDsymm]
    exact hD2
  have hX :
      covariantJetNormSq (I := I) (M := M) g 2 X ≤
        Ca * (Ch * N) ^ 2 * S0 := by
    calc
      covariantJetNormSq (I := I) (M := M) g 2 X ≤
          Ca * covariantJetNormSq (I := I) (M := M) g 2
              (perturb0 (I := I) (M := M) g (T - U)) *
            covariantJetNormSq (I := I) (M := M) g 2
              (sharpFlatEndoCc (I := I) g gT) := by
        simpa only [X] using happ
          (perturb0 (I := I) (M := M) g (T - U))
          (sharpFlatEndoCc (I := I) g gT)
      _ ≤ Ca * (Ch * N) ^ 2 * S0 := by
        exact mul_le_mul
          (mul_le_mul_of_nonneg_left hP hCa) hST
          (jet_nonneg (I := I) (M := M) (m := 2) g
            (sharpFlatEndoCc (I := I) g gT))
          (mul_nonneg hCa (sq_nonneg (Ch * N)))
  have hY :
      covariantJetNormSq (I := I) (M := M) g 2 Y ≤ (C * N) ^ 2 := by
    calc
      covariantJetNormSq (I := I) (M := M) g 2 Y ≤
          Ca * covariantJetNormSq (I := I) (M := M) g 2
              (sharpFlatEndoCc (I := I) g gU) *
            covariantJetNormSq (I := I) (M := M) g 2 X := by
        simpa only [Y] using happ
          (sharpFlatEndoCc (I := I) g gU) X
      _ ≤ Ca * S0 * (Ca * (Ch * N) ^ 2 * S0) := by
        exact mul_le_mul
          (mul_le_mul_of_nonneg_left hSU hCa) hX
          (jet_nonneg (I := I) (M := M) (m := 2) g X)
          (mul_nonneg hCa hS0)
      _ = (C * N) ^ 2 := by
        simp only [C]
        ring
  rw [sharp_pair (I := I) (M := M) g gT gU T U hTtie hUtie,
    jet_neg1 (I := I) (M := M) g 2]
  exact hY

omit [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
omit [I.Boundaryless] in
private theorem corr_tel
    (g gT gU : SmoothRiemannianMetric I M)
    (T U : SmoothCcTensor g 0 2) :
    metricLoweredConnectionDifferenceCorrection (I := I) (M := M) g gT g T -
        metricLoweredConnectionDifferenceCorrection (I := I) (M := M) g gU g U =
      metricLoweredConnectionDifferenceCorrection (I := I) (M := M) g gT g (T - U) +
        (metricLoweredConnectionDifferenceCorrection (I := I) (M := M) g gT g U -
          metricLoweredConnectionDifferenceCorrection (I := I) (M := M) g gU g U) := by
  rw [metricLoweredConnectionDifferenceCorrection_sub (I := I) (M := M) g gT g T U]
  abel

private theorem corr_pair_h2
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (gT gU : SmoothRiemannianMetric I M)
        (T U : SmoothCcTensor g 0 2),
      covariantJetNormSq (I := I) (M := M) g 2
          (metricLoweredConnectionDifferenceCorrection (I := I) (M := M) g gT g T -
            metricLoweredConnectionDifferenceCorrection (I := I) (M := M) g gU g U) ≤
        C *
          (covariantJetNormSq (I := I) (M := M) g 2 (T - U) *
              covariantJetNormSq (I := I) (M := M) g 2
                (metricLoweredConnectionDifference (I := I) (M := M) g gT g) +
            covariantJetNormSq (I := I) (M := M) g 2 U *
              covariantJetNormSq (I := I) (M := M) g 2
                (metricLoweredConnectionDifference (I := I) (M := M) g gT g -
                  metricLoweredConnectionDifference (I := I) (M := M) g gU g)) := by
  obtain ⟨C0, hC0, hmul⟩ :=
    metricLoweredConnectionDifferenceCorrection_sobolev_two_mul_bound (I := I) (M := M) hDim g
  obtain ⟨C1, hC1, hmove⟩ :=
    metricLoweredConnectionDifferenceCorrection_metric_difference_sobolev_two_bound (I := I) (M := M) hDim g
  let C : ℝ := 2 * max C0 C1
  have hCmax : 0 ≤ max C0 C1 := hC0.trans (le_max_left C0 C1)
  have hC : 0 ≤ C := mul_nonneg (by norm_num) hCmax
  refine ⟨C, hC, ?_⟩
  intro gT gU T U
  let X : SmoothCcTensor g 0 3 :=
    metricLoweredConnectionDifferenceCorrection (I := I) (M := M) g gT g (T - U)
  let Y : SmoothCcTensor g 0 3 :=
    metricLoweredConnectionDifferenceCorrection (I := I) (M := M) g gT g U -
      metricLoweredConnectionDifferenceCorrection (I := I) (M := M) g gU g U
  let A : ℝ :=
    covariantJetNormSq (I := I) (M := M) g 2 (T - U) *
      covariantJetNormSq (I := I) (M := M) g 2
        (metricLoweredConnectionDifference (I := I) (M := M) g gT g)
  let B : ℝ :=
    covariantJetNormSq (I := I) (M := M) g 2 U *
      covariantJetNormSq (I := I) (M := M) g 2
        (metricLoweredConnectionDifference (I := I) (M := M) g gT g -
          metricLoweredConnectionDifference (I := I) (M := M) g gU g)
  have hA : 0 ≤ A := mul_nonneg
    (jet_nonneg (I := I) (M := M) g (T - U))
    (jet_nonneg (I := I) (M := M) g
      (metricLoweredConnectionDifference (I := I) (M := M) g gT g))
  have hB : 0 ≤ B := mul_nonneg
    (jet_nonneg (I := I) (M := M) g U)
    (jet_nonneg (I := I) (M := M) g
      (metricLoweredConnectionDifference (I := I) (M := M) g gT g -
        metricLoweredConnectionDifference (I := I) (M := M) g gU g))
  have hX :
      covariantJetNormSq (I := I) (M := M) g 2 X ≤ C0 * A := by
    simpa only [covariantJetNormSq, Nat.reduceAdd, X, A, mul_assoc] using
      hmul gT g (T - U)
  have hY :
      covariantJetNormSq (I := I) (M := M) g 2 Y ≤ C1 * B := by
    simpa only [covariantJetNormSq, Nat.reduceAdd, Y, B, mul_assoc] using
      hmove gT gU g U
  rw [corr_tel (I := I) (M := M) g gT gU T U]
  calc
    covariantJetNormSq (I := I) (M := M) g 2 (X + Y) ≤
        2 * (covariantJetNormSq (I := I) (M := M) g 2 X +
          covariantJetNormSq (I := I) (M := M) g 2 Y) :=
      jet_add1 (I := I) (M := M) g 2 X Y
    _ ≤ 2 * (C0 * A + C1 * B) :=
      mul_le_mul_of_nonneg_left (add_le_add hX hY) (by norm_num)
    _ ≤ 2 * (max C0 C1 * A + max C0 C1 * B) := by
      exact mul_le_mul_of_nonneg_left
        (add_le_add
          (mul_le_mul_of_nonneg_right (le_max_left C0 C1) hA)
          (mul_le_mul_of_nonneg_right (le_max_right C0 C1) hB))
        (by norm_num)
    _ = (2 * max C0 C1) * (A + B) := by ring
    _ = C * (A + B) := rfl

private theorem corr_h1_mul
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (gm g_bg : SmoothRiemannianMetric I M)
        (P : SmoothCcTensor g 0 2),
        covariantJetNormSq (I := I) (M := M) g 1
            (metricLoweredConnectionDifferenceCorrection (I := I) (M := M) g gm g_bg P) ≤
          C * covariantJetNormSq (I := I) (M := M) g 2 P *
            covariantJetNormSq (I := I) (M := M) g 1
              (metricLoweredConnectionDifference (I := I) (M := M) g gm g_bg) := by
  obtain ⟨Cφ, hCφ, hφ⟩ :=
    corrPhi_h2 (I := I) (M := M) hDim g
  obtain ⟨Ca, hCa, happ⟩ :=
    app_h21_mul (I := I) (M := M) hDim g 0 3 3
  let C : ℝ := Ca * Cφ
  have hC : 0 ≤ C := mul_nonneg hCa hCφ
  refine ⟨C, hC, ?_⟩
  intro gm g_bg P
  let W : SmoothCcTensor g 0 3 :=
    metricLoweredConnectionDifference (I := I) (M := M) g gm g_bg
  let ΦA : SmoothCcTensor g 3 3 :=
    corrPhi (I := I) (M := M) g P corrPermA
  let ΦB : SmoothCcTensor g 3 3 :=
    corrPhi (I := I) (M := M) g P corrPermB
  let UA : SmoothCcTensor g 0 3 :=
    operatorFieldApply (I := I) (M := M) g 3 3 ΦA W
  let UB : SmoothCcTensor g 0 3 :=
    operatorFieldApply (I := I) (M := M) g 3 3 ΦB W
  let JP : ℝ := covariantJetNormSq (I := I) (M := M) g 2 P
  let JW : ℝ := covariantJetNormSq (I := I) (M := M) g 1 W
  have hJP : 0 ≤ JP := jet_nonneg (I := I) (M := M) g P
  have hJW : 0 ≤ JW := jet_nonneg (I := I) (M := M) g W
  have hA :
      covariantJetNormSq (I := I) (M := M) g 1 UA ≤ C * JP * JW := by
    calc
      covariantJetNormSq (I := I) (M := M) g 1 UA ≤
          Ca * covariantJetNormSq (I := I) (M := M) g 2 ΦA * JW := by
        simpa only [UA, ΦA, W, JW, operatorFieldComposition_zero_eq_operatorFieldApply] using
          happ ΦA W
      _ ≤ Ca * (Cφ * JP) * JW := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left
            (by simpa only [ΦA, JP] using hφ P corrPermA) hCa)
          hJW
      _ = C * JP * JW := by
        simp only [C]
        ring
  have hB :
      covariantJetNormSq (I := I) (M := M) g 1 UB ≤ C * JP * JW := by
    calc
      covariantJetNormSq (I := I) (M := M) g 1 UB ≤
          Ca * covariantJetNormSq (I := I) (M := M) g 2 ΦB * JW := by
        simpa only [UB, ΦB, W, JW, operatorFieldComposition_zero_eq_operatorFieldApply] using
          happ ΦB W
      _ ≤ Ca * (Cφ * JP) * JW := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left
            (by simpa only [ΦB, JP] using hφ P corrPermB) hCa)
          hJW
      _ = C * JP * JW := by
        simp only [C]
        ring
  have hadd := jet_add1 (I := I) (M := M) g 1
    ((1 / 2 : ℝ) • UA) ((1 / 2 : ℝ) • UB)
  rw [jet_smul1, jet_smul1] at hadd
  rw [corr_formula (I := I) (M := M) g gm g_bg P]
  change covariantJetNormSq (I := I) (M := M) g 1
      ((1 / 2 : ℝ) • UA + (1 / 2 : ℝ) • UB) ≤ C * JP * JW
  calc
    covariantJetNormSq (I := I) (M := M) g 1
        ((1 / 2 : ℝ) • UA + (1 / 2 : ℝ) • UB) ≤
      2 * (((1 / 2 : ℝ) ^ 2 *
          covariantJetNormSq (I := I) (M := M) g 1 UA) +
        (1 / 2 : ℝ) ^ 2 *
          covariantJetNormSq (I := I) (M := M) g 1 UB) := hadd
    _ ≤ C * JP * JW := by
      nlinarith

theorem metricCorr_pair_h1
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (gT gU : SmoothRiemannianMetric I M)
        (T U : SmoothCcTensor g 0 2),
      covariantJetNormSq (I := I) (M := M) g 1
          (metricLoweredConnectionDifferenceCorrection (I := I) (M := M) g gT g T -
            metricLoweredConnectionDifferenceCorrection (I := I) (M := M) g gU g U) ≤
        C *
          (covariantJetNormSq (I := I) (M := M) g 2 (T - U) *
              covariantJetNormSq (I := I) (M := M) g 1
                (metricLoweredConnectionDifference (I := I) (M := M) g gT g) +
            covariantJetNormSq (I := I) (M := M) g 2 U *
              covariantJetNormSq (I := I) (M := M) g 1
                (metricLoweredConnectionDifference (I := I) (M := M) g gT g -
                  metricLoweredConnectionDifference (I := I) (M := M) g gU g)) := by
  obtain ⟨C0, hC0, hmul⟩ :=
    corr_h1_mul (I := I) (M := M) hDim g
  let C : ℝ := 2 * C0
  have hC : 0 ≤ C := mul_nonneg (by norm_num) hC0
  refine ⟨C, hC, ?_⟩
  intro gT gU T U
  let WT : SmoothCcTensor g 0 3 :=
    metricLoweredConnectionDifference (I := I) (M := M) g gT g
  let WU : SmoothCcTensor g 0 3 :=
    metricLoweredConnectionDifference (I := I) (M := M) g gU g
  let X : SmoothCcTensor g 0 3 :=
    metricLoweredConnectionDifferenceCorrection (I := I) (M := M) g gT g (T - U)
  let Y : SmoothCcTensor g 0 3 :=
    metricLoweredConnectionDifferenceCorrection (I := I) (M := M) g gT g U -
      metricLoweredConnectionDifferenceCorrection (I := I) (M := M) g gU g U
  let A : ℝ :=
    covariantJetNormSq (I := I) (M := M) g 2 (T - U) *
      covariantJetNormSq (I := I) (M := M) g 1 WT
  let B : ℝ :=
    covariantJetNormSq (I := I) (M := M) g 2 U *
      covariantJetNormSq (I := I) (M := M) g 1 (WT - WU)
  have hA : 0 ≤ A := mul_nonneg
    (jet_nonneg (I := I) (M := M) g (T - U))
    (jet_nonneg (I := I) (M := M) g WT)
  have hB : 0 ≤ B := mul_nonneg
    (jet_nonneg (I := I) (M := M) g U)
    (jet_nonneg (I := I) (M := M) g (WT - WU))
  have hX :
      covariantJetNormSq (I := I) (M := M) g 1 X ≤ C0 * A := by
    simpa only [X, A, WT, mul_assoc] using hmul gT g (T - U)
  have hWcross :
      metricLoweredConnectionDifference (I := I) (M := M) g gU gT = -(WT - WU) := by
    simp only [WT, WU, metricLoweredConnectionDifference]
    module
  have hY :
      covariantJetNormSq (I := I) (M := M) g 1 Y ≤ C0 * B := by
    change covariantJetNormSq (I := I) (M := M) g 1
      (metricLoweredConnectionDifferenceCorrection (I := I) (M := M) g gT g U -
        metricLoweredConnectionDifferenceCorrection (I := I) (M := M) g gU g U) ≤ C0 * B
    rw [corr_cross (I := I) (M := M) g gT gU U,
      jet_neg1 (I := I) (M := M) g 1]
    have hraw := hmul gU gT U
    rw [hWcross, jet_neg1 (I := I) (M := M) g 1] at hraw
    simpa only [B, WT, WU, mul_assoc] using hraw
  rw [corr_tel (I := I) (M := M) g gT gU T U]
  change covariantJetNormSq (I := I) (M := M) g 1 (X + Y) ≤ C * (A + B)
  calc
    covariantJetNormSq (I := I) (M := M) g 1 (X + Y) ≤
        2 * (covariantJetNormSq (I := I) (M := M) g 1 X +
          covariantJetNormSq (I := I) (M := M) g 1 Y) :=
      jet_add1 (I := I) (M := M) g 1 X Y
    _ ≤ 2 * (C0 * A + C0 * B) :=
      mul_le_mul_of_nonneg_left (add_le_add hX hY) (by norm_num)
    _ = C * (A + B) := by
      simp only [C]
      ring

omit [SigmaCompactSpace M] in
omit [I.Boundaryless] in
private theorem mcd_sub_eq
    (g gT gU : SmoothRiemannianMetric I M)
    (T U : SmoothCcTensor g 0 2)
    (hTtie : ∀ (x : M) (u v : TangentSpace I x),
      gT.inner x u v =
        g.inner x u v + ccTensorBilinSymm (I := I) g T x u v)
    (hUtie : ∀ (x : M) (u v : TangentSpace I x),
      gU.inner x u v =
        g.inner x u v + ccTensorBilinSymm (I := I) g U x u v) :
    metricConnectionDifferenceLoweredCoefficient (I := I) (M := M) g gT g -
        metricConnectionDifferenceLoweredCoefficient (I := I) (M := M) g gU g =
      (metricLoweredConnectionDifference (I := I) (M := M) g gT g -
        metricLoweredConnectionDifference (I := I) (M := M) g gU g) +
      (metricLoweredConnectionDifferenceCorrection (I := I) (M := M) g gT g T -
        metricLoweredConnectionDifferenceCorrection (I := I) (M := M) g gU g U) := by
  rw [metricConnectionDifferenceLoweredCoefficient_eq_lowered_add_correction (I := I) (M := M) g gT g T hTtie,
    metricConnectionDifferenceLoweredCoefficient_eq_lowered_add_correction (I := I) (M := M) g gU g U hUtie]
  module

namespace RicciDeTurckLowOrder

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [BoundarylessManifold I M]
    [I.Boundaryless] [SigmaCompactSpace M] in
theorem fullRev_sub
    (g gT gU : SmoothRiemannianMetric I M)
    (T U : SmoothCcTensor g 0 2)
    (hTtie : ∀ (x : M) (u v : TangentSpace I x),
      gT.inner x u v =
        g.inner x u v + ccTensorBilinSymm (I := I) g T x u v)
    (hUtie : ∀ (x : M) (u v : TangentSpace I x),
      gU.inner x u v =
        g.inner x u v + ccTensorBilinSymm (I := I) g U x u v) :
    metricComparisonEndomorphismField (I := I) (M := M) gT g -
        metricComparisonEndomorphismField (I := I) (M := M) gU g =
      symmRaiseEndo (I := I) (M := M) g (T - U) := by
  have hsub :
      symmRaiseEndo (I := I) (M := M) g (T - U) =
        symmRaiseEndo (I := I) (M := M) g T -
          symmRaiseEndo (I := I) (M := M) g U := by
    calc
      symmRaiseEndo (I := I) (M := M) g (T - U) =
          symmRaiseEndo (I := I) (M := M) g
            (T + (-1 : ℝ) • U) := by
              rw [neg_one_smul, sub_eq_add_neg]
      _ = symmRaiseEndo (I := I) (M := M) g T +
            symmRaiseEndo (I := I) (M := M) g
              ((-1 : ℝ) • U) := by
                rw [symmRaiseEndo_add]
      _ = symmRaiseEndo (I := I) (M := M) g T +
            (-1 : ℝ) •
              symmRaiseEndo (I := I) (M := M) g U := by
                rw [symmRaiseEndo_smul]
      _ = symmRaiseEndo (I := I) (M := M) g T -
            symmRaiseEndo (I := I) (M := M) g U := by
              module
  have hdec (gm : SmoothRiemannianMetric I M) :
      metricComparisonEndomorphismField (I := I) (M := M) gm g =
        metricComparisonDifferenceEndomorphismField (I := I) gm g +
          metricComparisonEndomorphismField (I := I) (M := M) g g := by
    apply ContMDiffSection.ext
    intro x
    rw [show ((metricComparisonDifferenceEndomorphismField (I := I) gm g +
          metricComparisonEndomorphismField (I := I) (M := M) g g) x) =
        metricComparisonDifferenceEndomorphismField (I := I) gm g x +
          metricComparisonEndomorphismField (I := I) (M := M) g g x from by
      rw [ContMDiffSection.coe_add]
      rfl]
    apply ContinuousLinearMap.ext
    intro v
    rw [metricComparisonEndomorphismField_apply, add_apply]
    rw [show metricComparisonDifferenceEndomorphismField (I := I) gm g x =
        metricComparisonDifferenceEndomorphism (I := I) gm g x from rfl]
    have hself :
        metricComparisonEndomorphism (I := I) g g x =
          ContinuousLinearMap.id ℝ (TangentSpace I x) := by
      apply ContinuousLinearMap.ext
      intro w
      rw [metricComparisonEndomorphism_apply, inverseMetricSharpFib_g0FlatCLM,
        ContinuousLinearMap.id_apply]
    rw [metricComparisonEndomorphismField_apply]
    change metricComparisonEndomorphism (I := I) gm g x v =
      metricComparisonDifferenceEndomorphism (I := I) gm g x v +
        metricComparisonEndomorphism (I := I) g g x v
    rw [hself, ContinuousLinearMap.id_apply]
    exact metricComparisonEndomorphism_eq_diff_add_id (I := I) gm g x v
  rw [hdec gT, hdec gU,
    ← raise_rev (I := I) (M := M) g gT T hTtie,
    ← raise_rev (I := I) (M := M) g gU U hUtie, hsub]
  module

theorem revSlot_pair_h2
    (g gT gU : SmoothRiemannianMetric I M)
    (T U : SmoothCcTensor g 0 2)
    (hT : ∀ (x : M) (u v : TangentSpace I x),
      ccTensorBilin (I := I) g T x u v =
        ccTensorBilin (I := I) g T x v u)
    (hU : ∀ (x : M) (u v : TangentSpace I x),
      ccTensorBilin (I := I) g U x u v =
        ccTensorBilin (I := I) g U x v u)
    (hTtie : ∀ (x : M) (u v : TangentSpace I x),
      gT.inner x u v =
        g.inner x u v + ccTensorBilinSymm (I := I) g T x u v)
    (hUtie : ∀ (x : M) (u v : TangentSpace I x),
      gU.inner x u v =
        g.inner x u v + ccTensorBilinSymm (I := I) g U x u v) :
    covariantJetNormSq (I := I) (M := M) g 2
        (endoSlotZeroCcTensor (I := I) (M := M) g 2
            (metricComparisonEndomorphismField (I := I) (M := M) gT g) -
          endoSlotZeroCcTensor (I := I) (M := M) g 2
            (metricComparisonEndomorphismField (I := I) (M := M) gU g)) ≤
      (Module.finrank ℝ E : ℝ) ^ 2 *
        covariantJetNormSq (I := I) (M := M) g 2 (T - U) := by
  have hsymm :
      ccTensor02Symm (I := I) (M := M) g (T - U) = T - U := by
    rw [symmS_sub, symm_eq_self (I := I) (M := M) g T hT,
      symm_eq_self (I := I) (M := M) g U hU]
  rw [← slotInsertEndoCc_sub,
    fullRev_sub (I := I) (M := M) g gT gU T U hTtie hUtie]
  calc
    covariantJetNormSq (I := I) (M := M) g 2
        (endoSlotZeroCcTensor (I := I) (M := M) g 2
          (symmRaiseEndo (I := I) (M := M) g (T - U))) ≤
      (Module.finrank ℝ E : ℝ) ^ 2 *
        covariantJetNormSq (I := I) (M := M) g 2
          (endoSlotZeroCcTensor (I := I) (M := M) g 0
            (symmRaiseEndo (I := I) (M := M) g (T - U))) :=
      endo_slot_h2 (I := I) (M := M) g 2
        (symmRaiseEndo (I := I) (M := M) g (T - U))
    _ = (Module.finrank ℝ E : ℝ) ^ 2 *
        covariantJetNormSq (I := I) (M := M) g 2 (T - U) := by
      rw [show
        endoSlotZeroCcTensor (I := I) (M := M) g 0
            (symmRaiseEndo (I := I) (M := M) g (T - U)) =
          perturb0 (I := I) (M := M) g (T - U) from rfl,
        perturb_h2_eq (I := I) (M := M) g (T - U) hsymm]

theorem reverse_slot_sobolev_two_bound
    (g : SmoothRiemannianMetric I M) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (gm : SmoothRiemannianMetric I M)
        (P : SmoothCcTensor g 0 2)
        (_hP : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g P x u v =
            ccTensorBilin (I := I) g P x v u)
        (_htie : ∀ (x : M) (u v : TangentSpace I x),
          gm.inner x u v =
            g.inner x u v + ccTensorBilinSymm (I := I) g P x u v)
        (R : ℝ), 0 ≤ R →
        covariantJetNormSq (I := I) (M := M) g 2 P ≤ R ^ 2 →
      covariantJetNormSq (I := I) (M := M) g 2
          (endoSlotZeroCcTensor (I := I) (M := M) g 2
            (metricComparisonEndomorphismField (I := I) (M := M) gm g)) ≤
        (C * (1 + R)) ^ 2 := by
  let A0 : SmoothCcTensor g 3 3 :=
    endoSlotZeroCcTensor (I := I) (M := M) g 2
      (metricComparisonEndomorphismField (I := I) (M := M) g g)
  let J0 : ℝ := covariantJetNormSq (I := I) (M := M) g 2 A0
  let fr : ℝ := Module.finrank ℝ E
  let Z : ℝ := 2 * (fr ^ 2 + J0)
  let C : ℝ := Real.sqrt Z
  have hJ0 : 0 ≤ J0 :=
    jet_nonneg (I := I) (M := M) g A0
  have hZ : 0 ≤ Z :=
    mul_nonneg (by norm_num)
      (add_nonneg (sq_nonneg fr) hJ0)
  refine ⟨C, Real.sqrt_nonneg _, ?_⟩
  intro gm P hP htie R hR hP2
  have hzero :
      ∀ (x : M) (u v : TangentSpace I x),
        ccTensorBilin (I := I) g
            (0 : SmoothCcTensor g 0 2) x u v =
          ccTensorBilin (I := I) g
            (0 : SmoothCcTensor g 0 2) x v u := by
    intro x u v
    rw [ccTensorBilin_zero, ccTensorBilin_zero]
  have hzeroTie :
      ∀ (x : M) (u v : TangentSpace I x),
        g.inner x u v =
          g.inner x u v +
            ccTensorBilinSymm (I := I) g
              (0 : SmoothCcTensor g 0 2) x u v := by
    intro x u v
    rw [ccTensorBilinSymm_apply, ccTensorBilin_zero,
      ccTensorBilin_zero]
    ring
  let A : SmoothCcTensor g 3 3 :=
    endoSlotZeroCcTensor (I := I) (M := M) g 2
      (metricComparisonEndomorphismField (I := I) (M := M) gm g)
  have hpair :
      covariantJetNormSq (I := I) (M := M) g 2 (A - A0) ≤
        fr ^ 2 * covariantJetNormSq (I := I) (M := M) g 2 P := by
    simpa only [A, A0, fr, sub_zero] using
      revSlot_pair_h2 (I := I) (M := M)
        g gm g P (0 : SmoothCcTensor g 0 2)
        hP hzero htie hzeroTie
  have hpairR :
      covariantJetNormSq (I := I) (M := M) g 2 (A - A0) ≤
        fr ^ 2 * R ^ 2 :=
    hpair.trans (mul_le_mul_of_nonneg_left hP2 (sq_nonneg fr))
  have hRdom : R ^ 2 ≤ (1 + R) ^ 2 := by
    nlinarith
  have hone : (1 : ℝ) ≤ (1 + R) ^ 2 := by
    nlinarith [sq_nonneg R]
  have hdom :
      2 * (fr ^ 2 * R ^ 2 + J0) ≤ Z * (1 + R) ^ 2 := by
    calc
      2 * (fr ^ 2 * R ^ 2 + J0) ≤
          2 * (fr ^ 2 * (1 + R) ^ 2 +
            J0 * (1 + R) ^ 2) :=
        mul_le_mul_of_nonneg_left
          (add_le_add
            (mul_le_mul_of_nonneg_left hRdom (sq_nonneg fr))
            (by simpa only [mul_one] using
              mul_le_mul_of_nonneg_left hone hJ0))
          (by norm_num)
      _ = Z * (1 + R) ^ 2 := by
        simp only [Z]
        ring
  have hCsq : C ^ 2 = Z := by
    simpa only [C] using Real.sq_sqrt hZ
  have hAeq : A = (A - A0) + A0 := by module
  change covariantJetNormSq (I := I) (M := M) g 2 A ≤
    (C * (1 + R)) ^ 2
  rw [hAeq]
  calc
    covariantJetNormSq (I := I) (M := M) g 2 ((A - A0) + A0) ≤
        2 * (covariantJetNormSq (I := I) (M := M) g 2 (A - A0) +
          covariantJetNormSq (I := I) (M := M) g 2 A0) :=
      jet_add1 (I := I) (M := M) g 2 (A - A0) A0
    _ ≤ 2 * (fr ^ 2 * R ^ 2 + J0) :=
      mul_le_mul_of_nonneg_left
        (add_le_add hpairR le_rfl) (by norm_num)
    _ ≤ Z * (1 + R) ^ 2 := hdom
    _ = (C * (1 + R)) ^ 2 := by
      rw [mul_pow, hCsq]

private theorem one_add_sq_mul_sq_le_add_mul_sq
    {A D : ℝ} (hA : 0 ≤ A) :
    (1 + A ^ 2) * D ^ 2 ≤ (D + A * D) ^ 2 := by
  calc
    (1 + A ^ 2) * D ^ 2 ≤ (1 + A) ^ 2 * D ^ 2 :=
      mul_le_mul_of_nonneg_right (one_add_sq_le_sq_one_add hA) (sq_nonneg D)
    _ = (D + A * D) ^ 2 := by ring

theorem mcd_pair_h2
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M)
    {δ₀ : ℝ} (hδ₀0 : 0 ≤ δ₀) (hδ₀ : δ₀ < 1) :
    ∃ B0 B1 : ℝ → ℝ,
      (∀ R : ℝ, 0 ≤ R → 0 ≤ B0 R) ∧
      (∀ R : ℝ, 0 ≤ R → 0 ≤ B1 R) ∧
      ∀ (gT gU : SmoothRiemannianMetric I M)
        (T U : SmoothCcTensor g 0 2)
        (_hT : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g T x u v =
            ccTensorBilin (I := I) g T x v u)
        (_hU : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g U x u v =
            ccTensorBilin (I := I) g U x v u)
        (_hTtie : ∀ (x : M) (u v : TangentSpace I x),
          gT.inner x u v =
            g.inner x u v + ccTensorBilinSymm (I := I) g T x u v)
        (_hUtie : ∀ (x : M) (u v : TangentSpace I x),
          gU.inner x u v =
            g.inner x u v + ccTensorBilinSymm (I := I) g U x u v)
        {δT δU : ℝ}
        (_hδT_le : δT ≤ δ₀) (_hδT0 : 0 ≤ δT)
        (_hδT : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) δT)
        (_hδU_le : δU ≤ δ₀) (_hδU0 : 0 ≤ δU)
        (_hδU : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g U) δU)
        (R A D2 D3 : ℝ),
        0 ≤ R → 0 ≤ A → 0 ≤ D2 → 0 ≤ D3 →
        covariantJetNormSq (I := I) (M := M) g 2 U ≤ R ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 3 T ≤ A ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 2 (T - U) ≤ D2 ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 3 (T - U) ≤ D3 ^ 2 →
      covariantJetNormSq (I := I) (M := M) g 2
          (metricConnectionDifferenceLoweredCoefficient (I := I) (M := M) g gT g -
            metricConnectionDifferenceLoweredCoefficient (I := I) (M := M) g gU g) ≤
        (B0 R * D3 + B1 R * D2 + B1 R * A * D2) ^ 2 := by
  obtain ⟨W0, W1, hW0, hW1, hw⟩ :=
    exists_metricLoweredConnectionDifference_covariantJetNormSq_two_sub_tame_bound (I := I) (M := M) hDim g hδ₀0 hδ₀
  obtain ⟨Kw, hKw, hwT⟩ :=
    wXi_h2_low (I := I) (M := M) g hδ₀0 hδ₀
  obtain ⟨Cc, hCc, hcorr⟩ :=
    corr_pair_h2 (I := I) (M := M) hDim g
  let H : ℝ := Real.sqrt Cc
  let Hw : ℝ := Real.sqrt Kw
  let B0 : ℝ → ℝ := fun R =>
    2 * (W0 R + H * R * W0 R)
  let B1 : ℝ → ℝ := fun R =>
    2 * (W1 R + H * (Hw + R * W1 R))
  have hH : 0 ≤ H := Real.sqrt_nonneg _
  have hHw : 0 ≤ Hw := Real.sqrt_nonneg _
  have hHsq : H ^ 2 = Cc := by
    simpa only [H] using Real.sq_sqrt hCc
  have hHwsq : Hw ^ 2 = Kw := by
    simpa only [Hw] using Real.sq_sqrt hKw
  refine ⟨B0, B1, ?_, ?_, ?_⟩
  · intro R hR
    exact mul_nonneg (by norm_num)
      (add_nonneg (hW0 R hR)
        (mul_nonneg (mul_nonneg hH hR) (hW0 R hR)))
  · intro R hR
    exact mul_nonneg (by norm_num)
      (add_nonneg (hW1 R hR)
        (mul_nonneg hH
          (add_nonneg hHw (mul_nonneg hR (hW1 R hR)))))
  intro gT gU T U hT hU hTtie hUtie
    δT δU hδT_le hδT0 hδT hδU_le hδU0 hδU
    R A D2 D3 hR hA hD2 hD3 hU2 hT3 hTU2 hTU3
  let WD : SmoothCcTensor g 0 3 :=
    metricLoweredConnectionDifference (I := I) (M := M) g gT g -
      metricLoweredConnectionDifference (I := I) (M := M) g gU g
  let CD : SmoothCcTensor g 0 3 :=
    metricLoweredConnectionDifferenceCorrection (I := I) (M := M) g gT g T -
      metricLoweredConnectionDifferenceCorrection (I := I) (M := M) g gU g U
  let X : ℝ := W0 R * D3 + W1 R * D2 + W1 R * A * D2
  let S : ℝ := Hw * (D2 + A * D2)
  let Y : ℝ := R * X
  let Z : ℝ := H * S + H * Y
  have hX : 0 ≤ X :=
    add_nonneg
      (add_nonneg (mul_nonneg (hW0 R hR) hD3)
        (mul_nonneg (hW1 R hR) hD2))
      (mul_nonneg (mul_nonneg (hW1 R hR) hA) hD2)
  have hS : 0 ≤ S :=
    mul_nonneg hHw
      (add_nonneg hD2 (mul_nonneg hA hD2))
  have hY : 0 ≤ Y := mul_nonneg hR hX
  have hZ : 0 ≤ Z :=
    add_nonneg (mul_nonneg hH hS) (mul_nonneg hH hY)
  have hWD :
      covariantJetNormSq (I := I) (M := M) g 2 WD ≤ X ^ 2 := by
    simpa only [WD, X] using
      hw gT gU g T U hT hU hTtie hUtie
        hδT_le hδT0 hδT hδU_le hδU0 hδU
        R A D2 D3 hR hA hD2 hD3 hU2 hT3 hTU2 hTU3
  have hWT :
      covariantJetNormSq (I := I) (M := M) g 2
          (metricLoweredConnectionDifference (I := I) (M := M) g gT g) ≤
        Kw * (1 + A ^ 2) := by
    exact (hwT gT T hT hTtie hδT_le hδT0 hδT).trans
      (mul_le_mul_of_nonneg_left (add_le_add le_rfl hT3) hKw)
  have hfirst :
      covariantJetNormSq (I := I) (M := M) g 2 (T - U) *
          covariantJetNormSq (I := I) (M := M) g 2
            (metricLoweredConnectionDifference (I := I) (M := M) g gT g) ≤
        S ^ 2 := by
    have hscalar :
        (1 + A ^ 2) * D2 ^ 2 ≤ (D2 + A * D2) ^ 2 := by
      exact one_add_sq_mul_sq_le_add_mul_sq hA
    calc
      covariantJetNormSq (I := I) (M := M) g 2 (T - U) *
          covariantJetNormSq (I := I) (M := M) g 2
            (metricLoweredConnectionDifference (I := I) (M := M) g gT g) ≤
        D2 ^ 2 * (Kw * (1 + A ^ 2)) :=
          mul_le_mul hTU2 hWT
            (jet_nonneg (I := I) (M := M) g
              (metricLoweredConnectionDifference (I := I) (M := M) g gT g))
            (sq_nonneg D2)
      _ = Hw ^ 2 * ((1 + A ^ 2) * D2 ^ 2) := by
        rw [hHwsq]
        ring
      _ ≤ Hw ^ 2 * (D2 + A * D2) ^ 2 :=
        mul_le_mul_of_nonneg_left hscalar (sq_nonneg Hw)
      _ = S ^ 2 := by
        simp only [S]
        ring
  have hsecond :
      covariantJetNormSq (I := I) (M := M) g 2 U *
          covariantJetNormSq (I := I) (M := M) g 2 WD ≤ Y ^ 2 := by
    calc
      covariantJetNormSq (I := I) (M := M) g 2 U *
          covariantJetNormSq (I := I) (M := M) g 2 WD ≤
        R ^ 2 * X ^ 2 :=
          mul_le_mul hU2 hWD
            (jet_nonneg (I := I) (M := M) g WD)
            (sq_nonneg R)
      _ = Y ^ 2 := by
        simp only [Y]
        ring
  have hCD :
      covariantJetNormSq (I := I) (M := M) g 2 CD ≤ Z ^ 2 := by
    have hraw := hcorr gT gU T U
    change covariantJetNormSq (I := I) (M := M) g 2 CD ≤
      Cc * (covariantJetNormSq (I := I) (M := M) g 2 (T - U) *
          covariantJetNormSq (I := I) (M := M) g 2
            (metricLoweredConnectionDifference (I := I) (M := M) g gT g) +
        covariantJetNormSq (I := I) (M := M) g 2 U *
          covariantJetNormSq (I := I) (M := M) g 2 WD) at hraw
    calc
      covariantJetNormSq (I := I) (M := M) g 2 CD ≤
          Cc * (covariantJetNormSq (I := I) (M := M) g 2 (T - U) *
              covariantJetNormSq (I := I) (M := M) g 2
                (metricLoweredConnectionDifference (I := I) (M := M) g gT g) +
            covariantJetNormSq (I := I) (M := M) g 2 U *
              covariantJetNormSq (I := I) (M := M) g 2 WD) := hraw
      _ ≤ Cc * (S ^ 2 + Y ^ 2) :=
        mul_le_mul_of_nonneg_left (add_le_add hfirst hsecond) hCc
      _ = (H * S) ^ 2 + (H * Y) ^ 2 := by
        rw [← hHsq]
        ring
      _ ≤ Z ^ 2 := by
        dsimp only [Z]
        exact sq_add_sq_le_add_sq
          (mul_nonneg hH hS) (mul_nonneg hH hY)
  rw [mcd_sub_eq (I := I) (M := M) g gT gU T U hTtie hUtie]
  change covariantJetNormSq (I := I) (M := M) g 2 (WD + CD) ≤ _
  calc
    covariantJetNormSq (I := I) (M := M) g 2 (WD + CD) ≤
        2 * (covariantJetNormSq (I := I) (M := M) g 2 WD +
          covariantJetNormSq (I := I) (M := M) g 2 CD) :=
      jet_add1 (I := I) (M := M) g 2 WD CD
    _ ≤ 2 * (X ^ 2 + Z ^ 2) :=
      mul_le_mul_of_nonneg_left (add_le_add hWD hCD) (by norm_num)
    _ ≤ (2 * (X + Z)) ^ 2 :=
      twice_sq_sum_le_double_sum_sq hX hZ
    _ = (B0 R * D3 + B1 R * D2 + B1 R * A * D2) ^ 2 := by
      simp only [B0, B1, Z, S, Y, X]
      ring

theorem metric_connection_difference_coefficient_sobolev_two_bound
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M)
    {δ₀ : ℝ} (hδ₀0 : 0 ≤ δ₀) (hδ₀ : δ₀ < 1) :
    ∃ B : ℝ → ℝ,
      (∀ R : ℝ, 0 ≤ R → 0 ≤ B R) ∧
      ∀ (gm : SmoothRiemannianMetric I M)
        (P : SmoothCcTensor g 0 2)
        (_hP : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g P x u v =
            ccTensorBilin (I := I) g P x v u)
        (_htie : ∀ (x : M) (u v : TangentSpace I x),
          gm.inner x u v =
            g.inner x u v + ccTensorBilinSymm (I := I) g P x u v)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀) (_hδ0 : 0 ≤ δ)
        (_hδ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g P) δ)
        (R A : ℝ), 0 ≤ R → 0 ≤ A →
        covariantJetNormSq (I := I) (M := M) g 2 P ≤ R ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 3 P ≤ A ^ 2 →
      covariantJetNormSq (I := I) (M := M) g 2
          (metricConnectionDifferenceLoweredCoefficient (I := I) (M := M) g gm g) ≤
        (B R * (1 + A)) ^ 2 := by
  obtain ⟨Kw, hKw, hw⟩ :=
    wXi_h2_low (I := I) (M := M) g hδ₀0 hδ₀
  obtain ⟨Cc, hCc, hmul⟩ :=
    metricLoweredConnectionDifferenceCorrection_sobolev_two_mul_bound (I := I) (M := M) hDim g
  let Q : ℝ → ℝ := fun R => 2 * Kw * (1 + Cc * R ^ 2)
  let B : ℝ → ℝ := fun R => Real.sqrt (Q R)
  have hQ : ∀ R : ℝ, 0 ≤ R → 0 ≤ Q R := by
    intro R hR
    exact mul_nonneg (mul_nonneg (by norm_num) hKw)
      (add_nonneg (by norm_num) (mul_nonneg hCc (sq_nonneg R)))
  refine ⟨B, fun R hR => Real.sqrt_nonneg _, ?_⟩
  intro gm P hP htie δ hδ_le hδ0 hδ R A hR hA hP2 hP3
  let X : SmoothCcTensor g 0 3 :=
    metricLoweredConnectionDifference (I := I) (M := M) g gm g
  let Y : SmoothCcTensor g 0 3 :=
    metricLoweredConnectionDifferenceCorrection (I := I) (M := M) g gm g P
  have hX :
      covariantJetNormSq (I := I) (M := M) g 2 X ≤
        Kw * (1 + A ^ 2) := by
    exact (hw gm P hP htie hδ_le hδ0 hδ).trans
      (mul_le_mul_of_nonneg_left (add_le_add le_rfl hP3) hKw)
  have hY :
      covariantJetNormSq (I := I) (M := M) g 2 Y ≤
        Cc * R ^ 2 * (Kw * (1 + A ^ 2)) := by
    have hraw := hmul gm g P
    change covariantJetNormSq (I := I) (M := M) g 2 Y ≤
      Cc * covariantJetNormSq (I := I) (M := M) g 2 P *
        covariantJetNormSq (I := I) (M := M) g 2 X at hraw
    exact hraw.trans
      (mul_le_mul
        (mul_le_mul_of_nonneg_left hP2 hCc) hX
        (jet_nonneg (I := I) (M := M) g X)
        (mul_nonneg hCc (sq_nonneg R)))
  rw [metricConnectionDifferenceLoweredCoefficient_eq_lowered_add_correction (I := I) (M := M) g gm g P htie]
  change covariantJetNormSq (I := I) (M := M) g 2 (X + Y) ≤ _
  have hBsq : (B R) ^ 2 = Q R := by
    simpa only [B] using Real.sq_sqrt (hQ R hR)
  have hscalar : 1 + A ^ 2 ≤ (1 + A) ^ 2 :=
    one_add_sq_le_sq_one_add hA
  calc
    covariantJetNormSq (I := I) (M := M) g 2 (X + Y) ≤
        2 * (covariantJetNormSq (I := I) (M := M) g 2 X +
          covariantJetNormSq (I := I) (M := M) g 2 Y) :=
      jet_add1 (I := I) (M := M) g 2 X Y
    _ ≤ 2 * (Kw * (1 + A ^ 2) +
        Cc * R ^ 2 * (Kw * (1 + A ^ 2))) :=
      mul_le_mul_of_nonneg_left (add_le_add hX hY) (by norm_num)
    _ = Q R * (1 + A ^ 2) := by
      simp only [Q]
      ring
    _ ≤ Q R * (1 + A) ^ 2 :=
      mul_le_mul_of_nonneg_left hscalar (hQ R hR)
    _ = (B R * (1 + A)) ^ 2 := by
      rw [mul_pow, hBsq]

theorem mcd_pair_h1
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M)
    {δ₀ : ℝ} (hδ₀0 : 0 ≤ δ₀) (hδ₀ : δ₀ < 1) :
    ∃ B0 B1 : ℝ → ℝ,
      (∀ R : ℝ, 0 ≤ R → 0 ≤ B0 R) ∧
      (∀ R : ℝ, 0 ≤ R → 0 ≤ B1 R) ∧
      ∀ (gT gU : SmoothRiemannianMetric I M)
        (T U : SmoothCcTensor g 0 2)
        (_hT : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g T x u v =
            ccTensorBilin (I := I) g T x v u)
        (_hU : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g U x u v =
            ccTensorBilin (I := I) g U x v u)
        (_hTtie : ∀ (x : M) (u v : TangentSpace I x),
          gT.inner x u v =
            g.inner x u v + ccTensorBilinSymm (I := I) g T x u v)
        (_hUtie : ∀ (x : M) (u v : TangentSpace I x),
          gU.inner x u v =
            g.inner x u v + ccTensorBilinSymm (I := I) g U x u v)
        {δT δU : ℝ}
        (_hδT_le : δT ≤ δ₀) (_hδT0 : 0 ≤ δT)
        (_hδT : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) δT)
        (_hδU_le : δU ≤ δ₀) (_hδU0 : 0 ≤ δU)
        (_hδU : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g U) δU)
        (R A D2 : ℝ),
        0 ≤ R → 0 ≤ A → 0 ≤ D2 →
        covariantJetNormSq (I := I) (M := M) g 2 U ≤ R ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 3 T ≤ A ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 2 (T - U) ≤ D2 ^ 2 →
      covariantJetNormSq (I := I) (M := M) g 1
          (metricConnectionDifferenceLoweredCoefficient (I := I) (M := M) g gT g -
            metricConnectionDifferenceLoweredCoefficient (I := I) (M := M) g gU g) ≤
        (B0 R * D2 + B1 R * A * D2) ^ 2 := by
  obtain ⟨W0, W1, hW0, hW1, hwp⟩ :=
    exists_metricLoweredConnectionDifference_covariantJetNormSq_one_sub_bound (I := I) (M := M) hDim g hδ₀0 hδ₀
  obtain ⟨Kw, hKw, hwlow⟩ :=
    wXi_h2_low (I := I) (M := M) g hδ₀0 hδ₀
  obtain ⟨Cc, hCc, hcp⟩ :=
    metricCorr_pair_h1 (I := I) (M := M) hDim g
  let Q0 : ℝ → ℝ := fun R =>
    2 * (2 * (W0 R) ^ 2 + Cc * (Kw + R ^ 2 * (2 * (W0 R) ^ 2)))
  let Q1 : ℝ → ℝ := fun R =>
    2 * (2 * (W1 R) ^ 2 + Cc * (Kw + R ^ 2 * (2 * (W1 R) ^ 2)))
  have hQ0 : ∀ R : ℝ, 0 ≤ R → 0 ≤ Q0 R := by
    intro R hR
    have : 0 ≤ Cc * (Kw + R ^ 2 * (2 * (W0 R) ^ 2)) :=
      mul_nonneg hCc (by positivity)
    positivity
  have hQ1 : ∀ R : ℝ, 0 ≤ R → 0 ≤ Q1 R := by
    intro R hR
    have : 0 ≤ Cc * (Kw + R ^ 2 * (2 * (W1 R) ^ 2)) :=
      mul_nonneg hCc (by positivity)
    positivity
  refine ⟨fun R => Real.sqrt (Q0 R), fun R => Real.sqrt (Q1 R),
    fun R hR => Real.sqrt_nonneg _, fun R hR => Real.sqrt_nonneg _, ?_⟩
  intro gT gU T U hT hU hTtie hUtie
    δT δU hδT_le hδT0 hδT hδU_le hδU0 hδU
    R A D2 hR hA hD2 hU2 hT3 hTU2
  have hwd : covariantJetNormSq (I := I) (M := M) g 1
      (metricLoweredConnectionDifference (I := I) (M := M) g gT g -
        metricLoweredConnectionDifference (I := I) (M := M) g gU g) ≤
      (W0 R * D2 + W1 R * A * D2) ^ 2 :=
    hwp gT gU g T U hT hU hTtie hUtie
      hδT_le hδT0 hδT hδU_le hδU0 hδU R A D2 hR hA hD2 hU2 hT3 hTU2
  have hws : covariantJetNormSq (I := I) (M := M) g 1
      (metricLoweredConnectionDifference (I := I) (M := M) g gT g) ≤ Kw * (1 + A ^ 2) := by
    have h2 := hwlow gT T hT hTtie hδT_le hδT0 hδT
    have hmono : covariantJetNormSq (I := I) (M := M) g 1
        (metricLoweredConnectionDifference (I := I) (M := M) g gT g) ≤
        covariantJetNormSq (I := I) (M := M) g 2
          (metricLoweredConnectionDifference (I := I) (M := M) g gT g) :=
      jet_mono (I := I) (M := M) g (by norm_num) _
    refine hmono.trans (h2.trans ?_)
    have : 1 + covariantJetNormSq (I := I) (M := M) g 3 T ≤ 1 + A ^ 2 := by
      linarith [hT3]
    exact mul_le_mul_of_nonneg_left this hKw
  have hcd : covariantJetNormSq (I := I) (M := M) g 1
      (metricLoweredConnectionDifferenceCorrection (I := I) (M := M) g gT g T -
        metricLoweredConnectionDifferenceCorrection (I := I) (M := M) g gU g U) ≤
      Cc * (D2 ^ 2 * (Kw * (1 + A ^ 2)) +
        R ^ 2 * (W0 R * D2 + W1 R * A * D2) ^ 2) := by
    refine (hcp gT gU T U).trans
      (mul_le_mul_of_nonneg_left ?_ hCc)
    have hx : covariantJetNormSq (I := I) (M := M) g 2 (T - U) *
        covariantJetNormSq (I := I) (M := M) g 1
          (metricLoweredConnectionDifference (I := I) (M := M) g gT g) ≤
        D2 ^ 2 * (Kw * (1 + A ^ 2)) :=
      mul_le_mul hTU2 hws
        (jet_nonneg (I := I) (M := M) g _) (sq_nonneg _)
    have hy : covariantJetNormSq (I := I) (M := M) g 2 U *
        covariantJetNormSq (I := I) (M := M) g 1
          (metricLoweredConnectionDifference (I := I) (M := M) g gT g -
            metricLoweredConnectionDifference (I := I) (M := M) g gU g) ≤
        R ^ 2 * (W0 R * D2 + W1 R * A * D2) ^ 2 :=
      mul_le_mul hU2 hwd
        (jet_nonneg (I := I) (M := M) g _) (sq_nonneg _)
    linarith
  have hsub := mcd_sub_eq (I := I) (M := M) g gT gU T U hTtie hUtie
  rw [hsub]
  have hadd := jet_add1 (I := I) (M := M) g 1
    (metricLoweredConnectionDifference (I := I) (M := M) g gT g -
      metricLoweredConnectionDifference (I := I) (M := M) g gU g)
    (metricLoweredConnectionDifferenceCorrection (I := I) (M := M) g gT g T -
      metricLoweredConnectionDifferenceCorrection (I := I) (M := M) g gU g U)
  have hcross : (W0 R * D2 + W1 R * A * D2) ^ 2 ≤
      2 * (W0 R) ^ 2 * D2 ^ 2 + 2 * (W1 R) ^ 2 * (A ^ 2 * D2 ^ 2) := by
    calc
      (W0 R * D2 + W1 R * A * D2) ^ 2 ≤
          2 * (W0 R * D2) ^ 2 + 2 * (W1 R * A * D2) ^ 2 :=
        add_sq_le_two_sq_add_sq _ _
      _ = 2 * (W0 R) ^ 2 * D2 ^ 2 +
          2 * (W1 R) ^ 2 * (A ^ 2 * D2 ^ 2) := by ring
  have hs0 : Real.sqrt (Q0 R) ^ 2 = Q0 R :=
    Real.sq_sqrt (hQ0 R hR)
  have hs1 : Real.sqrt (Q1 R) ^ 2 = Q1 R :=
    Real.sq_sqrt (hQ1 R hR)
  have hrhs : (Real.sqrt (Q0 R) * D2 + Real.sqrt (Q1 R) * (A * D2)) ^ 2 =
      Q0 R * D2 ^ 2 + Q1 R * (A ^ 2 * D2 ^ 2) +
        2 * (Real.sqrt (Q0 R) * Real.sqrt (Q1 R)) * (A * D2 ^ 2) := by
    have : (Real.sqrt (Q0 R) * D2 + Real.sqrt (Q1 R) * (A * D2)) ^ 2 =
        Real.sqrt (Q0 R) ^ 2 * D2 ^ 2 +
          Real.sqrt (Q1 R) ^ 2 * (A ^ 2 * D2 ^ 2) +
          2 * (Real.sqrt (Q0 R) * Real.sqrt (Q1 R)) * (A * D2 ^ 2) := by
      ring
    rw [this, hs0, hs1]
  have hcross0 : 0 ≤
      2 * (Real.sqrt (Q0 R) * Real.sqrt (Q1 R)) * (A * D2 ^ 2) := by
    have h1 : 0 ≤ Real.sqrt (Q0 R) * Real.sqrt (Q1 R) :=
      mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    have h2 : 0 ≤ A * D2 ^ 2 := mul_nonneg hA (sq_nonneg _)
    positivity
  calc
    covariantJetNormSq (I := I) (M := M) g 1
        ((metricLoweredConnectionDifference (I := I) (M := M) g gT g -
            metricLoweredConnectionDifference (I := I) (M := M) g gU g) +
          (metricLoweredConnectionDifferenceCorrection (I := I) (M := M) g gT g T -
            metricLoweredConnectionDifferenceCorrection (I := I) (M := M) g gU g U)) ≤
      2 * (covariantJetNormSq (I := I) (M := M) g 1
          (metricLoweredConnectionDifference (I := I) (M := M) g gT g -
            metricLoweredConnectionDifference (I := I) (M := M) g gU g) +
        covariantJetNormSq (I := I) (M := M) g 1
          (metricLoweredConnectionDifferenceCorrection (I := I) (M := M) g gT g T -
            metricLoweredConnectionDifferenceCorrection (I := I) (M := M) g gU g U)) := hadd
    _ ≤ 2 * ((W0 R * D2 + W1 R * A * D2) ^ 2 +
        Cc * (D2 ^ 2 * (Kw * (1 + A ^ 2)) +
          R ^ 2 * (W0 R * D2 + W1 R * A * D2) ^ 2)) := by
      linarith [hwd, hcd]
    _ ≤ Q0 R * D2 ^ 2 + Q1 R * (A ^ 2 * D2 ^ 2) := by
      have hexp : Cc * (D2 ^ 2 * (Kw * (1 + A ^ 2)) +
          R ^ 2 * (W0 R * D2 + W1 R * A * D2) ^ 2) ≤
          Cc * (D2 ^ 2 * (Kw * (1 + A ^ 2)) +
            R ^ 2 * (2 * (W0 R) ^ 2 * D2 ^ 2 +
              2 * (W1 R) ^ 2 * (A ^ 2 * D2 ^ 2))) := by
        refine mul_le_mul_of_nonneg_left ?_ hCc
        exact add_le_add (le_refl _)
          (mul_le_mul_of_nonneg_left hcross (sq_nonneg R))
      calc
        2 * ((W0 R * D2 + W1 R * A * D2) ^ 2 +
            Cc * (D2 ^ 2 * (Kw * (1 + A ^ 2)) +
              R ^ 2 * (W0 R * D2 + W1 R * A * D2) ^ 2)) ≤
          2 * ((2 * (W0 R) ^ 2 * D2 ^ 2 +
              2 * (W1 R) ^ 2 * (A ^ 2 * D2 ^ 2)) +
            Cc * (D2 ^ 2 * (Kw * (1 + A ^ 2)) +
              R ^ 2 * (2 * (W0 R) ^ 2 * D2 ^ 2 +
                2 * (W1 R) ^ 2 * (A ^ 2 * D2 ^ 2)))) :=
          mul_le_mul_of_nonneg_left (add_le_add hcross hexp) (by norm_num)
        _ = Q0 R * D2 ^ 2 + Q1 R * (A ^ 2 * D2 ^ 2) := by
          simp only [Q0, Q1]
          ring
    _ ≤ (Real.sqrt (Q0 R) * D2 + Real.sqrt (Q1 R) * (A * D2)) ^ 2 := by
      rw [hrhs]
      linarith [hcross0]
    _ = (Real.sqrt (Q0 R) * D2 + Real.sqrt (Q1 R) * A * D2) ^ 2 := by
      ring

private theorem fullSlot1_h2
    (g : SmoothRiemannianMetric I M)
    {δ₀ : ℝ} (hδ₀0 : 0 ≤ δ₀) (hδ₀ : δ₀ < 1) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ (gm : SmoothRiemannianMetric I M)
        (P : SmoothCcTensor g 0 2)
        (_hP : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g P x u v =
            ccTensorBilin (I := I) g P x v u)
        (_htie : ∀ (x : M) (u v : TangentSpace I x),
          gm.inner x u v =
            g.inner x u v + ccTensorBilinSymm (I := I) g P x u v)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀) (_hδ0 : 0 ≤ δ)
        (_hδ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g P) δ),
      covariantJetNormSq (I := I) (M := M) g 2
          (endoSlotZeroCcTensor (I := I) (M := M) g 1
            (metricComparisonEndomorphismField (I := I) (M := M) g gm)) ≤
        K * (1 + covariantJetNormSq (I := I) (M := M) g 2 P) := by
  obtain ⟨K₀, hK₀, hsharp⟩ :=
    sharp_h2_low (I := I) (M := M) g hδ₀0 hδ₀
  let fr : ℝ := Module.finrank ℝ E
  let K : ℝ := fr ^ 1 * K₀
  have hfr : 0 ≤ fr := Nat.cast_nonneg _
  have hK : 0 ≤ K := mul_nonneg (pow_nonneg hfr 1) hK₀
  refine ⟨K, hK, ?_⟩
  intro gm P hP htie δ hδ_le hδ0 hδ
  calc
    covariantJetNormSq (I := I) (M := M) g 2
        (endoSlotZeroCcTensor (I := I) (M := M) g 1
          (metricComparisonEndomorphismField (I := I) (M := M) g gm)) ≤
      fr ^ 1 * covariantJetNormSq (I := I) (M := M) g 2
        (endoSlotZeroCcTensor (I := I) (M := M) g 0
          (metricComparisonEndomorphismField (I := I) (M := M) g gm)) := by
      simpa only [fr] using
        endo_slot_h2 (I := I) (M := M) g 1
          (metricComparisonEndomorphismField (I := I) (M := M) g gm)
    _ = fr ^ 1 * covariantJetNormSq (I := I) (M := M) g 2
        (sharpFlatEndoCc (I := I) g gm) := by
      rw [sharp_eq_slot0 (I := I) (M := M) g gm]
    _ ≤ fr ^ 1 * (K₀ *
        (1 + covariantJetNormSq (I := I) (M := M) g 2 P)) :=
      mul_le_mul_of_nonneg_left
        (hsharp gm P hP htie hδ_le hδ0 hδ) (pow_nonneg hfr 1)
    _ = K * (1 + covariantJetNormSq (I := I) (M := M) g 2 P) := by
      simp only [K]
      ring

theorem full_slot_sobolev_two_bound
    (g : SmoothRiemannianMetric I M)
    {δ₀ : ℝ} (hδ₀0 : 0 ≤ δ₀) (hδ₀ : δ₀ < 1) :
    ∃ B : ℝ → ℝ,
      (∀ R : ℝ, 0 ≤ R → 0 ≤ B R) ∧
      ∀ (gm : SmoothRiemannianMetric I M)
        (P : SmoothCcTensor g 0 2)
        (_hP : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g P x u v =
            ccTensorBilin (I := I) g P x v u)
        (_htie : ∀ (x : M) (u v : TangentSpace I x),
          gm.inner x u v =
            g.inner x u v + ccTensorBilinSymm (I := I) g P x u v)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀) (_hδ0 : 0 ≤ δ)
        (_hδ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g P) δ)
        (R : ℝ), 0 ≤ R →
        covariantJetNormSq (I := I) (M := M) g 2 P ≤ R ^ 2 →
      covariantJetNormSq (I := I) (M := M) g 2
          (endoSlotZeroCcTensor (I := I) (M := M) g 1
            (metricComparisonEndomorphismField (I := I) (M := M) g gm)) ≤
        (B R) ^ 2 := by
  obtain ⟨K, hK, hfull⟩ :=
    fullSlot1_h2 (I := I) (M := M) g hδ₀0 hδ₀
  let Q : ℝ → ℝ := fun R => K * (1 + R ^ 2)
  let B : ℝ → ℝ := fun R => Real.sqrt (Q R)
  have hQ : ∀ R : ℝ, 0 ≤ R → 0 ≤ Q R := by
    intro R hR
    exact mul_nonneg hK (by positivity)
  refine ⟨B, fun R hR => Real.sqrt_nonneg _, ?_⟩
  intro gm P hP htie δ hδ_le hδ0 hδ R hR hP2
  have hBsq : (B R) ^ 2 = Q R := by
    simpa only [B] using Real.sq_sqrt (hQ R hR)
  calc
    covariantJetNormSq (I := I) (M := M) g 2
        (endoSlotZeroCcTensor (I := I) (M := M) g 1
          (metricComparisonEndomorphismField (I := I) (M := M) g gm)) ≤
      K * (1 + covariantJetNormSq (I := I) (M := M) g 2 P) :=
        hfull gm P hP htie hδ_le hδ0 hδ
    _ ≤ Q R := by
      simp only [Q]
      exact mul_le_mul_of_nonneg_left (by linarith) hK
    _ = (B R) ^ 2 := hBsq.symm

theorem fullSlot_pair_h1
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M)
    {δ₀ : ℝ} (hδ₀0 : 0 ≤ δ₀) (hδ₀ : δ₀ < 1) :
    ∃ B0 B1 : ℝ → ℝ,
      (∀ R : ℝ, 0 ≤ R → 0 ≤ B0 R) ∧
      (∀ R : ℝ, 0 ≤ R → 0 ≤ B1 R) ∧
      ∀ (gT gU : SmoothRiemannianMetric I M)
        (T U : SmoothCcTensor g 0 2)
        (_hT : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g T x u v =
            ccTensorBilin (I := I) g T x v u)
        (_hU : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g U x u v =
            ccTensorBilin (I := I) g U x v u)
        (_hTtie : ∀ (x : M) (u v : TangentSpace I x),
          gT.inner x u v =
            g.inner x u v + ccTensorBilinSymm (I := I) g T x u v)
        (_hUtie : ∀ (x : M) (u v : TangentSpace I x),
          gU.inner x u v =
            g.inner x u v + ccTensorBilinSymm (I := I) g U x u v)
        {δT δU : ℝ}
        (_hδT_le : δT ≤ δ₀) (_hδT0 : 0 ≤ δT)
        (_hδT : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) δT)
        (_hδU_le : δU ≤ δ₀) (_hδU0 : 0 ≤ δU)
        (_hδU : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g U) δU)
        (R A D2 : ℝ),
        0 ≤ R → 0 ≤ A → 0 ≤ D2 →
        covariantJetNormSq (I := I) (M := M) g 2 U ≤ R ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 3 T ≤ A ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 2 (T - U) ≤ D2 ^ 2 →
      covariantJetNormSq (I := I) (M := M) g 1
          (endoSlotZeroCcTensor (I := I) (M := M) g 1
              (metricComparisonEndomorphismField (I := I) (M := M) g gT) -
            endoSlotZeroCcTensor (I := I) (M := M) g 1
              (metricComparisonEndomorphismField (I := I) (M := M) g gU)) ≤
        (B0 R * D2 + B1 R * A * D2) ^ 2 := by
  obtain ⟨K, hK, hfull⟩ :=
    fullSlot1_h2 (I := I) (M := M) g hδ₀0 hδ₀
  obtain ⟨Cm, hCm, happ⟩ :=
    app_h21_mul (I := I) (M := M) hDim g 2 2 2
  let fr : ℝ := Module.finrank ℝ E
  have hfr : (0 : ℝ) ≤ fr := Nat.cast_nonneg _
  let Z : ℝ := Cm ^ 2 * K ^ 2 * fr
  have hZ : 0 ≤ Z :=
    mul_nonneg (mul_nonneg (sq_nonneg Cm) (sq_nonneg K)) hfr
  let Q : ℝ → ℝ := fun R => 2 * Z * (1 + R ^ 2)
  let B : ℝ → ℝ := fun R => Real.sqrt (Q R)
  have hQ : ∀ R : ℝ, 0 ≤ R → 0 ≤ Q R := by
    intro R hR
    exact mul_nonneg (mul_nonneg (by norm_num) hZ) (by positivity)
  refine ⟨B, B, fun R hR => Real.sqrt_nonneg _,
    fun R hR => Real.sqrt_nonneg _, ?_⟩
  intro gT gU T U hT hU hTtie hUtie
    δT δU hδT_le hδT0 hδT hδU_le hδU0 hδU
    R A D2 hR hA hD2 hU2 hT3 hTU2
  have hsymm : ccTensor02Symm (I := I) (M := M) g (T - U) = T - U := by
    rw [symmS_sub, symm_eq_self (I := I) (M := M) g T hT,
      symm_eq_self (I := I) (M := M) g U hU]
  have hdiff :
      metricComparisonEndomorphismField (I := I) (M := M) g gT -
          metricComparisonEndomorphismField (I := I) (M := M) g gU =
        metricComparisonDifferenceEndomorphismField (I := I) g gT -
          metricComparisonDifferenceEndomorphismField (I := I) g gU := by
    apply ContMDiffSection.ext
    intro x
    rw [ContMDiffSection.coe_sub, Pi.sub_apply,
      ContMDiffSection.coe_sub, Pi.sub_apply]
    apply ContinuousLinearMap.ext
    intro v
    rw [sub_apply, sub_apply,
      metricComparisonEndomorphismField_apply, metricComparisonEndomorphismField_apply,
      show metricComparisonDifferenceEndomorphismField (I := I) g gT x =
        metricComparisonDifferenceEndomorphism (I := I) g gT x from rfl,
      show metricComparisonDifferenceEndomorphismField (I := I) g gU x =
        metricComparisonDifferenceEndomorphism (I := I) g gU x from rfl,
      metricComparisonEndomorphism_eq_diff_add_id (I := I) g gT x v,
      metricComparisonEndomorphism_eq_diff_add_id (I := I) g gU x v]
    abel
  have hslot :
      endoSlotZeroCcTensor (I := I) (M := M) g 1
            (metricComparisonEndomorphismField (I := I) (M := M) g gT) -
          endoSlotZeroCcTensor (I := I) (M := M) g 1
            (metricComparisonEndomorphismField (I := I) (M := M) g gU) =
        inverseMetricDifferenceSlotCoefficient (I := I) g gT -
          inverseMetricDifferenceSlotCoefficient (I := I) g gU := by
    rw [inverseMetricDifferenceSlotCoefficient_eq_slotInsertEndoCc (I := I) g gT,
      inverseMetricDifferenceSlotCoefficient_eq_slotInsertEndoCc (I := I) g gU,
      ← slotInsertEndoCc_sub, ← slotInsertEndoCc_sub, hdiff]
  have hT2 : covariantJetNormSq (I := I) (M := M) g 2 T ≤ A ^ 2 :=
    (jet_mono (I := I) (M := M) (m := 2) (n := 3) g
      (by norm_num) T).trans hT3
  have hbdU : covariantJetNormSq (I := I) (M := M) g 2
      (endoSlotZeroCcTensor (I := I) (M := M) g 1
        (metricComparisonEndomorphismField (I := I) (M := M) g gU)) ≤
      K * (1 + R ^ 2) :=
    (hfull gU U hU hUtie hδU_le hδU0 hδU).trans
      (mul_le_mul_of_nonneg_left (by linarith) hK)
  have hbdT2 : covariantJetNormSq (I := I) (M := M) g 2
      (endoSlotZeroCcTensor (I := I) (M := M) g 1
        (metricComparisonEndomorphismField (I := I) (M := M) g gT)) ≤
      K * (1 + A ^ 2) :=
    (hfull gT T hT hTtie hδT_le hδT0 hδT).trans
      (mul_le_mul_of_nonneg_left (by linarith) hK)
  have hbdT1 : covariantJetNormSq (I := I) (M := M) g 1
      (endoSlotZeroCcTensor (I := I) (M := M) g 1
        (metricComparisonEndomorphismField (I := I) (M := M) g gT)) ≤
      K * (1 + A ^ 2) :=
    (jet_mono (I := I) (M := M) (m := 1) (n := 2) g
      (by norm_num) _).trans hbdT2
  have hbdP : covariantJetNormSq (I := I) (M := M) g 2
      (endoSlotZeroCcTensor (I := I) (M := M) g 1
        (symmRaiseEndo (I := I) (M := M) g (T - U))) ≤
      fr * D2 ^ 2 := by
    have h1 := endo_slot_h2 (I := I) (M := M) g 1
      (symmRaiseEndo (I := I) (M := M) g (T - U))
    have h2 : covariantJetNormSq (I := I) (M := M) g 2
        (endoSlotZeroCcTensor (I := I) (M := M) g 0
          (symmRaiseEndo (I := I) (M := M) g (T - U))) =
        covariantJetNormSq (I := I) (M := M) g 2 (T - U) := by
      rw [show endoSlotZeroCcTensor (I := I) (M := M) g 0
          (symmRaiseEndo (I := I) (M := M) g (T - U)) =
          perturb0 (I := I) (M := M) g (T - U) from rfl]
      exact perturb_h2_eq (I := I) (M := M) g (T - U) hsymm
    rw [h2] at h1
    refine h1.trans ?_
    simp only [fr, pow_one]
    exact mul_le_mul_of_nonneg_left hTU2 (Nat.cast_nonneg _)
  have harith : ∀ a b c y w : ℝ,
      w ≤ Cm * a * y → y ≤ Cm * b * c →
      a ≤ K * (1 + R ^ 2) → b ≤ fr * D2 ^ 2 →
      c ≤ K * (1 + A ^ 2) →
      0 ≤ a → 0 ≤ b → 0 ≤ c → 0 ≤ y →
      w ≤ Z * ((1 + R ^ 2) * ((1 + A ^ 2) * D2 ^ 2)) := by
    intro a b c y w hw hyb haR hbD hcA ha hb hc hy
    have hA1 : Cm * a ≤ Cm * (K * (1 + R ^ 2)) :=
      mul_le_mul_of_nonneg_left haR hCm
    have hB1 : Cm * b * c ≤
        Cm * (fr * D2 ^ 2) * (K * (1 + A ^ 2)) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hbD hCm) hcA hc
        (mul_nonneg hCm (mul_nonneg hfr (sq_nonneg D2)))
    have hy' : y ≤ Cm * (fr * D2 ^ 2) * (K * (1 + A ^ 2)) :=
      hyb.trans hB1
    have hprod : Cm * a * y ≤
        Cm * (K * (1 + R ^ 2)) *
          (Cm * (fr * D2 ^ 2) * (K * (1 + A ^ 2))) :=
      mul_le_mul hA1 hy' hy
        (mul_nonneg hCm (mul_nonneg hK (by positivity)))
    refine hw.trans (hprod.trans (le_of_eq ?_))
    simp only [Z]
    ring
  have hinner := happ
    (endoSlotZeroCcTensor (I := I) (M := M) g 1
      (symmRaiseEndo (I := I) (M := M) g (T - U)))
    (endoSlotZeroCcTensor (I := I) (M := M) g 1
      (metricComparisonEndomorphismField (I := I) (M := M) g gT))
  have houter := happ
    (endoSlotZeroCcTensor (I := I) (M := M) g 1
      (metricComparisonEndomorphismField (I := I) (M := M) g gU))
    (ccOperatorFieldComp (I := I) (M := M) g 2 2 2
      (endoSlotZeroCcTensor (I := I) (M := M) g 1
        (symmRaiseEndo (I := I) (M := M) g (T - U)))
      (endoSlotZeroCcTensor (I := I) (M := M) g 1
        (metricComparisonEndomorphismField (I := I) (M := M) g gT)))
  rw [hslot,
    invSlot_sub_factor (I := I) (M := M) g gT gU T U hTtie hUtie,
    jet_neg1]
  refine (harith _ _ _ _ _ houter hinner hbdU hbdP hbdT1
    (jet_nonneg (I := I) (M := M) (m := 2) g _)
    (jet_nonneg (I := I) (M := M) (m := 2) g _)
    (jet_nonneg (I := I) (M := M) (m := 1) g _)
    (jet_nonneg (I := I) (M := M) (m := 1) g _)).trans ?_
  have hBsq : (B R) ^ 2 = Q R := by
    simpa only [B] using Real.sq_sqrt (hQ R hR)
  have hexp : (B R * D2 + B R * A * D2) ^ 2 =
      Q R * (D2 ^ 2 * (1 + A) ^ 2) := by
    have h : (B R * D2 + B R * A * D2) ^ 2 =
        (B R) ^ 2 * (D2 ^ 2 * (1 + A) ^ 2) := by ring
    rw [h, hBsq]
  rw [hexp]
  have hA2 : 1 + A ^ 2 ≤ (1 + A) ^ 2 :=
    one_add_sq_le_sq_one_add hA
  have hstep : Z * ((1 + R ^ 2) * ((1 + A ^ 2) * D2 ^ 2)) ≤
      Z * ((1 + R ^ 2) * ((1 + A) ^ 2 * D2 ^ 2)) := by
    refine mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hA2 (sq_nonneg D2))
        (by positivity)) hZ
  have hnn : 0 ≤ Z * ((1 + R ^ 2) * ((1 + A) ^ 2 * D2 ^ 2)) :=
    mul_nonneg hZ (mul_nonneg (by positivity)
      (mul_nonneg (sq_nonneg _) (sq_nonneg _)))
  refine hstep.trans ?_
  simp only [Q]
  calc
    Z * ((1 + R ^ 2) * ((1 + A) ^ 2 * D2 ^ 2)) ≤
        Z * ((1 + R ^ 2) * ((1 + A) ^ 2 * D2 ^ 2)) +
          Z * ((1 + R ^ 2) * ((1 + A) ^ 2 * D2 ^ 2)) := by
      exact le_add_of_nonneg_right hnn
    _ = 2 * Z * (1 + R ^ 2) * (D2 ^ 2 * (1 + A) ^ 2) := by ring

end RicciDeTurckLowOrder

omit [NeZero (Module.finrank ℝ E)] in
private theorem raiseDom_h2
    (g : SmoothRiemannianMetric I M)
    (ρ : Equiv.Perm (Fin 3)) (S : SmoothCcTensor g 0 3) :
    covariantJetNormSq (I := I) (M := M) g 2
        (cometricRaiseSlot0Field (I := I) (M := M) g 1
          (domDomCongrSection (I := I) g ρ S)) =
      covariantJetNormSq (I := I) (M := M) g 2 S := by
  calc
    covariantJetNormSq (I := I) (M := M) g 2
        (cometricRaiseSlot0Field (I := I) (M := M) g 1
          (domDomCongrSection (I := I) g ρ S)) =
      covariantJetNormSq (I := I) (M := M) g 2
        (domDomCongrSection (I := I) g ρ S) := by
          unfold covariantJetNormSq
          apply Finset.sum_congr rfl
          intro q _
          rw [norm_iteratedCovGrad_cometricRaiseSlot0Field_eq
            (I := I) (M := M) g 1
            (domDomCongrSection (I := I) g ρ S) q]
    _ = covariantJetNormSq (I := I) (M := M) g 2 S :=
      dom_h2 (I := I) (M := M) g ρ S

omit [NeZero (Module.finrank ℝ E)] in
private theorem psiLeft_h2
    (g gm : SmoothRiemannianMetric I M) :
    covariantJetNormSq (I := I) (M := M) g 2
        (psiLeft (I := I) (M := M) g gm) =
      covariantJetNormSq (I := I) (M := M) g 2
        (deTurckLieArmOneBackgroundLoweredConnectionDifference (I := I) (M := M) g gm g) := by
  exact raiseDom_h2 (I := I) (M := M) g lieArm1RhoSlot0 _

omit [NeZero (Module.finrank ℝ E)] in
private theorem psiLeft_sub_h2
    (g gT gU : SmoothRiemannianMetric I M) :
    covariantJetNormSq (I := I) (M := M) g 2
        (psiLeft (I := I) (M := M) g gT -
          psiLeft (I := I) (M := M) g gU) =
      covariantJetNormSq (I := I) (M := M) g 2
        (deTurckLieArmOneBackgroundLoweredConnectionDifference (I := I) (M := M) g gT g -
          deTurckLieArmOneBackgroundLoweredConnectionDifference (I := I) (M := M) g gU g) := by
  rw [show psiLeft (I := I) (M := M) g gT -
      psiLeft (I := I) (M := M) g gU =
    cometricRaiseSlot0Field (I := I) (M := M) g 1
      (domDomCongrSection (I := I) g lieArm1RhoSlot0
        (deTurckLieArmOneBackgroundLoweredConnectionDifference (I := I) (M := M) g gT g -
          deTurckLieArmOneBackgroundLoweredConnectionDifference (I := I) (M := M) g gU g)) by
    simp only [psiLeft]
    rw [dom_sub, raise_sub]]
  exact raiseDom_h2 (I := I) (M := M) g lieArm1RhoSlot0 _

private theorem psi_pair_h2
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M)
    {δ₀ : ℝ} (hδ₀0 : 0 ≤ δ₀) (hδ₀ : δ₀ < 1) :
    ∃ ρ P B0 B1 : ℝ,
      0 < ρ ∧ 0 ≤ P ∧ 0 ≤ B0 ∧ 0 ≤ B1 ∧
      ∀ (gT gU : SmoothRiemannianMetric I M)
        (T U : SmoothCcTensor g 0 2)
        (_hT : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g T x u v =
            ccTensorBilin (I := I) g T x v u)
        (_hU : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g U x u v =
            ccTensorBilin (I := I) g U x v u)
        (_hTtie : ∀ (x : M) (u v : TangentSpace I x),
          gT.inner x u v =
            g.inner x u v + ccTensorBilinSymm (I := I) g T x u v)
        (_hUtie : ∀ (x : M) (u v : TangentSpace I x),
          gU.inner x u v =
            g.inner x u v + ccTensorBilinSymm (I := I) g U x u v)
        {δT δU : ℝ}
        (_hδT_le : δT ≤ δ₀) (_hδT0 : 0 ≤ δT)
        (_hδT : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) δT)
        (_hδU_le : δU ≤ δ₀) (_hδU0 : 0 ≤ δU)
        (_hδU : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g U) δU),
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ ≤ ρ →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) U‖ ≤ ρ →
        ∀ (A D3 : ℝ), 0 ≤ A → 0 ≤ D3 →
        covariantJetNormSq (I := I) (M := M) g 3 T ≤ A ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 3 (T - U) ≤ D3 ^ 2 →
      let N :=
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) (T - U)‖
      covariantJetNormSq (I := I) (M := M) g 2
          (deTurckLieArmOneBackgroundCoefficient (I := I) (M := M) g gT g) ≤
          (P * (1 + A)) ^ 2 ∧
        covariantJetNormSq (I := I) (M := M) g 2
          (deTurckLieArmOneBackgroundCoefficient (I := I) (M := M) g gT g -
            deTurckLieArmOneBackgroundCoefficient (I := I) (M := M) g gU g) ≤
          (B0 * D3 + B1 * N + B1 * A * N) ^ 2 := by
  obtain ⟨ρs, Cs, hρs, hCs, hsharpPair⟩ :=
    sharp_pair_h2 (I := I) (M := M) hDim g hδ₀0 hδ₀
  obtain ⟨M0, M1, hM0, hM1, hmcdPair⟩ :=
    RicciDeTurckLowOrder.mcd_pair_h2 (I := I) (M := M) hDim g hδ₀0 hδ₀
  obtain ⟨Mb, hMb, hmcdBdd⟩ :=
    RicciDeTurckLowOrder.metric_connection_difference_coefficient_sobolev_two_bound (I := I) (M := M) hDim g hδ₀0 hδ₀
  obtain ⟨Ks, hKs, hsharpBdd⟩ :=
    sharp_h2_low (I := I) (M := M) g hδ₀0 hδ₀
  obtain ⟨Ch, hCh, hhs⟩ :=
    hs2_low2 (I := I) (M := M) g 2
  obtain ⟨Ca, hCa, happ⟩ :=
    app_h2_mul (I := I) (M := M) hDim g 1 1 2
  let ρ : ℝ := ρs
  let R0 : ℝ := Ch * ρ
  let S0 : ℝ := Ks * (1 + R0 ^ 2)
  let Bs : ℝ := Real.sqrt S0
  let H : ℝ := Real.sqrt Ca
  let P : ℝ := H * Mb R0 * Bs
  let B0 : ℝ := 2 * H * (Bs * M0 R0)
  let B1 : ℝ := 2 * H * (Mb R0 * Cs + Bs * M1 R0 * Ch)
  have hρ : 0 < ρ := hρs
  have hR0 : 0 ≤ R0 := mul_nonneg hCh hρ.le
  have hS0 : 0 ≤ S0 :=
    mul_nonneg hKs (add_nonneg (by norm_num) (sq_nonneg R0))
  have hBs : 0 ≤ Bs := Real.sqrt_nonneg _
  have hBssq : Bs ^ 2 = S0 := by
    simpa only [Bs] using Real.sq_sqrt hS0
  have hH : 0 ≤ H := Real.sqrt_nonneg _
  have hHsq : H ^ 2 = Ca := by
    simpa only [H] using Real.sq_sqrt hCa
  have hP : 0 ≤ P :=
    mul_nonneg (mul_nonneg hH (hMb R0 hR0)) hBs
  have hB0 : 0 ≤ B0 :=
    mul_nonneg (mul_nonneg (by norm_num) hH)
      (mul_nonneg hBs (hM0 R0 hR0))
  have hB1 : 0 ≤ B1 :=
    mul_nonneg (mul_nonneg (by norm_num) hH)
      (add_nonneg
        (mul_nonneg (hMb R0 hR0) hCs)
        (mul_nonneg (mul_nonneg hBs (hM1 R0 hR0)) hCh))
  refine ⟨ρ, P, B0, B1, hρ, hP, hB0, hB1, ?_⟩
  intro gT gU T U hT hU hTtie hUtie
    δT δU hδT_le hδT0 hδT hδU_le hδU0 hδU
    hTHs hUHs A D3 hA hD3 hT3 hTU3
  dsimp only
  let N : ℝ :=
    ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) (T - U)‖
  let KT : SmoothCcTensor g 0 3 :=
    deTurckLieArmOneBackgroundLoweredConnectionDifference (I := I) (M := M) g gT g
  let KU : SmoothCcTensor g 0 3 :=
    deTurckLieArmOneBackgroundLoweredConnectionDifference (I := I) (M := M) g gU g
  let LT : SmoothCcTensor g 1 2 :=
    psiLeft (I := I) (M := M) g gT
  let LU : SmoothCcTensor g 1 2 :=
    psiLeft (I := I) (M := M) g gU
  let ST : SmoothCcTensor g 1 1 :=
    sharpFlatEndoCc (I := I) g gT
  let SU : SmoothCcTensor g 1 1 :=
    sharpFlatEndoCc (I := I) g gU
  let XD : ℝ := M0 R0 * D3 +
    M1 R0 * (Ch * N) + M1 R0 * A * (Ch * N)
  let Z1 : ℝ := H * (Mb R0 * (1 + A)) * (Cs * N)
  let Z2 : ℝ := H * XD * Bs
  have hN : 0 ≤ N := norm_nonneg _
  have hT2 :
      covariantJetNormSq (I := I) (M := M) g 2 T ≤ R0 ^ 2 := by
    calc
      covariantJetNormSq (I := I) (M := M) g 2 T ≤
          (Ch * ‖ccTensorToHs (I := I) (M := M) g 2
            (2 : ℝ) T‖) ^ 2 := by
        simpa only [covariantJetNormSq, Nat.reduceAdd] using hhs T
      _ ≤ (Ch * ρ) ^ 2 :=
        pow_le_pow_left₀
          (mul_nonneg hCh (norm_nonneg _))
          (mul_le_mul_of_nonneg_left hTHs hCh) 2
      _ = R0 ^ 2 := rfl
  have hU2 :
      covariantJetNormSq (I := I) (M := M) g 2 U ≤ R0 ^ 2 := by
    calc
      covariantJetNormSq (I := I) (M := M) g 2 U ≤
          (Ch * ‖ccTensorToHs (I := I) (M := M) g 2
            (2 : ℝ) U‖) ^ 2 := by
        simpa only [covariantJetNormSq, Nat.reduceAdd] using hhs U
      _ ≤ (Ch * ρ) ^ 2 :=
        pow_le_pow_left₀
          (mul_nonneg hCh (norm_nonneg _))
          (mul_le_mul_of_nonneg_left hUHs hCh) 2
      _ = R0 ^ 2 := rfl
  have hTU2 :
      covariantJetNormSq (I := I) (M := M) g 2 (T - U) ≤
        (Ch * N) ^ 2 := by
    simpa only [covariantJetNormSq, Nat.reduceAdd, N] using hhs (T - U)
  have hST :
      covariantJetNormSq (I := I) (M := M) g 2 ST ≤ S0 := by
    calc
      covariantJetNormSq (I := I) (M := M) g 2 ST ≤
        Ks * (1 + covariantJetNormSq (I := I) (M := M) g 2 T) := by
          simpa only [ST] using
            hsharpBdd gT T hT hTtie hδT_le hδT0 hδT
      _ ≤ S0 := by
        dsimp only [S0]
        exact mul_le_mul_of_nonneg_left (add_le_add le_rfl hT2) hKs
  have hSU :
      covariantJetNormSq (I := I) (M := M) g 2 SU ≤ S0 := by
    calc
      covariantJetNormSq (I := I) (M := M) g 2 SU ≤
        Ks * (1 + covariantJetNormSq (I := I) (M := M) g 2 U) := by
          simpa only [SU] using
            hsharpBdd gU U hU hUtie hδU_le hδU0 hδU
      _ ≤ S0 := by
        dsimp only [S0]
        exact mul_le_mul_of_nonneg_left (add_le_add le_rfl hU2) hKs
  have hSD :
      covariantJetNormSq (I := I) (M := M) g 2 (ST - SU) ≤
        (Cs * N) ^ 2 := by
    simpa only [ST, SU, N, ρ] using
      hsharpPair gT gU T U hT hU hTtie hUtie
        hδT_le hδT0 hδT hδU_le hδU0 hδU hTHs hUHs
  have hKT :
      covariantJetNormSq (I := I) (M := M) g 2 KT ≤
        (Mb R0 * (1 + A)) ^ 2 := by
    have hraw := hmcdBdd gT T hT hTtie
      hδT_le hδT0 hδT R0 A hR0 hA hT2 hT3
    rw [metricConnectionDifferenceLoweredCoefficient_eq_neg_kappa
      (I := I) (M := M) g gT g,
      jet_neg1 (I := I) (M := M) g 2] at hraw
    simpa only [KT] using hraw
  have hLT :
      covariantJetNormSq (I := I) (M := M) g 2 LT ≤
        (Mb R0 * (1 + A)) ^ 2 := by
    rw [show covariantJetNormSq (I := I) (M := M) g 2 LT =
        covariantJetNormSq (I := I) (M := M) g 2 KT by
      simpa only [LT, KT] using
        psiLeft_h2 (I := I) (M := M) g gT]
    exact hKT
  have hKD :
      covariantJetNormSq (I := I) (M := M) g 2 (KT - KU) ≤ XD ^ 2 := by
    have hraw := hmcdPair gT gU T U hT hU hTtie hUtie
      hδT_le hδT0 hδT hδU_le hδU0 hδU
      R0 A (Ch * N) D3 hR0 hA (mul_nonneg hCh hN) hD3
      hU2 hT3 hTU2 hTU3
    rw [metricConnectionDifferenceLoweredCoefficient_eq_neg_kappa
      (I := I) (M := M) g gT g,
      metricConnectionDifferenceLoweredCoefficient_eq_neg_kappa
      (I := I) (M := M) g gU g] at hraw
    have hsign : -KT - -KU = -(KT - KU) := by
      simp only [KT, KU]
      module
    rw [hsign, jet_neg1 (I := I) (M := M) g 2] at hraw
    simpa only [XD] using hraw
  have hLD :
      covariantJetNormSq (I := I) (M := M) g 2 (LT - LU) ≤ XD ^ 2 := by
    rw [show covariantJetNormSq (I := I) (M := M) g 2 (LT - LU) =
        covariantJetNormSq (I := I) (M := M) g 2 (KT - KU) by
      simpa only [LT, LU, KT, KU] using
        psiLeft_sub_h2 (I := I) (M := M) g gT gU]
    exact hKD
  have hPsiT :
      covariantJetNormSq (I := I) (M := M) g 2
          (deTurckLieArmOneBackgroundCoefficient (I := I) (M := M) g gT g) ≤
        (P * (1 + A)) ^ 2 := by
    rw [psi_eq (I := I) (M := M) g gT]
    calc
      covariantJetNormSq (I := I) (M := M) g 2
          (ccOperatorFieldComp (I := I) (M := M) g 1 1 2 LT ST) ≤
        Ca * covariantJetNormSq (I := I) (M := M) g 2 LT *
          covariantJetNormSq (I := I) (M := M) g 2 ST := by
            simpa only [LT, ST] using happ LT ST
      _ ≤ Ca * (Mb R0 * (1 + A)) ^ 2 * S0 := by
        exact mul_le_mul
          (mul_le_mul_of_nonneg_left hLT hCa) hST
          (jet_nonneg (I := I) (M := M) g ST)
          (mul_nonneg hCa (sq_nonneg (Mb R0 * (1 + A))))
      _ = (P * (1 + A)) ^ 2 := by
        rw [← hHsq, ← hBssq]
        simp only [P]
        ring
  have hZ1 : 0 ≤ Z1 :=
    mul_nonneg
      (mul_nonneg hH
        (mul_nonneg (hMb R0 hR0) (add_nonneg (by norm_num) hA)))
      (mul_nonneg hCs hN)
  have hXD : 0 ≤ XD :=
    add_nonneg
      (add_nonneg (mul_nonneg (hM0 R0 hR0) hD3)
        (mul_nonneg (hM1 R0 hR0) (mul_nonneg hCh hN)))
      (mul_nonneg
        (mul_nonneg (hM1 R0 hR0) hA)
        (mul_nonneg hCh hN))
  have hZ2 : 0 ≤ Z2 :=
    mul_nonneg (mul_nonneg hH hXD) hBs
  let V1 : SmoothCcTensor g 1 2 :=
    ccOperatorFieldComp (I := I) (M := M) g 1 1 2 LT (ST - SU)
  let V2 : SmoothCcTensor g 1 2 :=
    ccOperatorFieldComp (I := I) (M := M) g 1 1 2 (LT - LU) SU
  have hV1 :
      covariantJetNormSq (I := I) (M := M) g 2 V1 ≤ Z1 ^ 2 := by
    calc
      covariantJetNormSq (I := I) (M := M) g 2 V1 ≤
        Ca * covariantJetNormSq (I := I) (M := M) g 2 LT *
          covariantJetNormSq (I := I) (M := M) g 2 (ST - SU) := by
            simpa only [V1] using happ LT (ST - SU)
      _ ≤ Ca * (Mb R0 * (1 + A)) ^ 2 * (Cs * N) ^ 2 := by
        exact mul_le_mul
          (mul_le_mul_of_nonneg_left hLT hCa) hSD
          (jet_nonneg (I := I) (M := M) g (ST - SU))
          (mul_nonneg hCa (sq_nonneg (Mb R0 * (1 + A))))
      _ = Z1 ^ 2 := by
        rw [← hHsq]
        simp only [Z1]
        ring
  have hV2 :
      covariantJetNormSq (I := I) (M := M) g 2 V2 ≤ Z2 ^ 2 := by
    calc
      covariantJetNormSq (I := I) (M := M) g 2 V2 ≤
        Ca * covariantJetNormSq (I := I) (M := M) g 2 (LT - LU) *
          covariantJetNormSq (I := I) (M := M) g 2 SU := by
            simpa only [V2] using happ (LT - LU) SU
      _ ≤ Ca * XD ^ 2 * S0 := by
        exact mul_le_mul
          (mul_le_mul_of_nonneg_left hLD hCa) hSU
          (jet_nonneg (I := I) (M := M) g SU)
          (mul_nonneg hCa (sq_nonneg XD))
      _ = Z2 ^ 2 := by
        rw [← hHsq, ← hBssq]
        simp only [Z2]
        ring
  refine ⟨hPsiT, ?_⟩
  rw [psi_sub_eq (I := I) (M := M) g gT gU]
  change covariantJetNormSq (I := I) (M := M) g 2 (V1 + V2) ≤ _
  calc
    covariantJetNormSq (I := I) (M := M) g 2 (V1 + V2) ≤
        2 * (covariantJetNormSq (I := I) (M := M) g 2 V1 +
          covariantJetNormSq (I := I) (M := M) g 2 V2) :=
      jet_add1 (I := I) (M := M) g 2 V1 V2
    _ ≤ 2 * (Z1 ^ 2 + Z2 ^ 2) :=
      mul_le_mul_of_nonneg_left (add_le_add hV1 hV2) (by norm_num)
    _ ≤ (2 * (Z1 + Z2)) ^ 2 :=
      twice_sq_sum_le_double_sum_sq hZ1 hZ2
    _ = (B0 * D3 + B1 * N + B1 * A * N) ^ 2 := by
      simp only [B0, B1, Z1, Z2, XD]
      ring

private theorem twice_scaled_sq_add_scaled_sq_le
    (a b c Q : ℝ) (h : 2 * (a ^ 2 + b ^ 2) ≤ c ^ 2) :
    2 * ((a * Q) ^ 2 + (b * Q) ^ 2) ≤ (c * Q) ^ 2 := by
  nlinarith [sq_nonneg Q]

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
private theorem jet14
    (g : SmoothRiemannianMetric I M) {r s : ℕ}
    (Q : ℝ)
    (Z0 Z1 Z2 Z3 Z4 Z5 Z6 Z7 Z8 Z9 Z10 Z11 Z12 Z13 :
      SmoothCcTensor g r s)
    (h0 : covariantJetNormSq (I := I) (M := M) g 2 Z0 ≤ Q ^ 2)
    (h1 : covariantJetNormSq (I := I) (M := M) g 2 Z1 ≤ Q ^ 2)
    (h2 : covariantJetNormSq (I := I) (M := M) g 2 Z2 ≤ Q ^ 2)
    (h3 : covariantJetNormSq (I := I) (M := M) g 2 Z3 ≤ Q ^ 2)
    (h4 : covariantJetNormSq (I := I) (M := M) g 2 Z4 ≤ Q ^ 2)
    (h5 : covariantJetNormSq (I := I) (M := M) g 2 Z5 ≤ Q ^ 2)
    (h6 : covariantJetNormSq (I := I) (M := M) g 2 Z6 ≤ Q ^ 2)
    (h7 : covariantJetNormSq (I := I) (M := M) g 2 Z7 ≤ Q ^ 2)
    (h8 : covariantJetNormSq (I := I) (M := M) g 2 Z8 ≤ Q ^ 2)
    (h9 : covariantJetNormSq (I := I) (M := M) g 2 Z9 ≤ Q ^ 2)
    (h10 : covariantJetNormSq (I := I) (M := M) g 2 Z10 ≤ Q ^ 2)
    (h11 : covariantJetNormSq (I := I) (M := M) g 2 Z11 ≤ Q ^ 2)
    (h12 : covariantJetNormSq (I := I) (M := M) g 2 Z12 ≤ Q ^ 2)
    (h13 : covariantJetNormSq (I := I) (M := M) g 2 Z13 ≤ Q ^ 2) :
    covariantJetNormSq (I := I) (M := M) g 2
        (Z0 + (Z1 + Z2 - Z3 - Z4 - Z5 - Z6) +
          (Z7 + Z8 - Z9 - Z10 - Z11 - Z12) + Z13) ≤
      (47 * Q) ^ 2 := by
  let A12 : SmoothCcTensor g r s := Z1 + Z2
  let A123 : SmoothCcTensor g r s := A12 - Z3
  let A1234 : SmoothCcTensor g r s := A123 - Z4
  let A12345 : SmoothCcTensor g r s := A1234 - Z5
  let A1 : SmoothCcTensor g r s := A12345 - Z6
  let A78 : SmoothCcTensor g r s := Z7 + Z8
  let A789 : SmoothCcTensor g r s := A78 - Z9
  let A78910 : SmoothCcTensor g r s := A789 - Z10
  let A7891011 : SmoothCcTensor g r s := A78910 - Z11
  let A2 : SmoothCcTensor g r s := A7891011 - Z12
  let O1 : SmoothCcTensor g r s := Z0 + A1
  let O2 : SmoothCcTensor g r s := O1 + A2
  have hA12 :
      covariantJetNormSq (I := I) (M := M) g 2 A12 ≤ (2 * Q) ^ 2 := by
    calc
      covariantJetNormSq (I := I) (M := M) g 2 A12 ≤
          2 * (covariantJetNormSq (I := I) (M := M) g 2 Z1 +
            covariantJetNormSq (I := I) (M := M) g 2 Z2) := by
              simpa only [A12] using
                jet_add1 (I := I) (M := M) g 2 Z1 Z2
      _ ≤ 2 * (Q ^ 2 + Q ^ 2) :=
        mul_le_mul_of_nonneg_left (add_le_add h1 h2) (by norm_num)
      _ = (2 * Q) ^ 2 := by ring
  have hA123 :
      covariantJetNormSq (I := I) (M := M) g 2 A123 ≤ (4 * Q) ^ 2 := by
    calc
      covariantJetNormSq (I := I) (M := M) g 2 A123 ≤
          2 * (covariantJetNormSq (I := I) (M := M) g 2 A12 +
            covariantJetNormSq (I := I) (M := M) g 2 Z3) := by
              simpa only [A123] using
                jet_sub (I := I) (M := M) g 2 A12 Z3
      _ ≤ 2 * ((2 * Q) ^ 2 + Q ^ 2) :=
        mul_le_mul_of_nonneg_left (add_le_add hA12 h3) (by norm_num)
      _ ≤ (4 * Q) ^ 2 := by
        simpa using twice_scaled_sq_add_scaled_sq_le
          2 1 4 Q (by norm_num)
  have hA1234 :
      covariantJetNormSq (I := I) (M := M) g 2 A1234 ≤ (6 * Q) ^ 2 := by
    calc
      covariantJetNormSq (I := I) (M := M) g 2 A1234 ≤
          2 * (covariantJetNormSq (I := I) (M := M) g 2 A123 +
            covariantJetNormSq (I := I) (M := M) g 2 Z4) := by
              simpa only [A1234] using
                jet_sub (I := I) (M := M) g 2 A123 Z4
      _ ≤ 2 * ((4 * Q) ^ 2 + Q ^ 2) :=
        mul_le_mul_of_nonneg_left (add_le_add hA123 h4) (by norm_num)
      _ ≤ (6 * Q) ^ 2 := by
        simpa using twice_scaled_sq_add_scaled_sq_le
          4 1 6 Q (by norm_num)
  have hA12345 :
      covariantJetNormSq (I := I) (M := M) g 2 A12345 ≤ (9 * Q) ^ 2 := by
    calc
      covariantJetNormSq (I := I) (M := M) g 2 A12345 ≤
          2 * (covariantJetNormSq (I := I) (M := M) g 2 A1234 +
            covariantJetNormSq (I := I) (M := M) g 2 Z5) := by
              simpa only [A12345] using
                jet_sub (I := I) (M := M) g 2 A1234 Z5
      _ ≤ 2 * ((6 * Q) ^ 2 + Q ^ 2) :=
        mul_le_mul_of_nonneg_left (add_le_add hA1234 h5) (by norm_num)
      _ ≤ (9 * Q) ^ 2 := by
        simpa using twice_scaled_sq_add_scaled_sq_le
          6 1 9 Q (by norm_num)
  have hA1 :
      covariantJetNormSq (I := I) (M := M) g 2 A1 ≤ (13 * Q) ^ 2 := by
    calc
      covariantJetNormSq (I := I) (M := M) g 2 A1 ≤
          2 * (covariantJetNormSq (I := I) (M := M) g 2 A12345 +
            covariantJetNormSq (I := I) (M := M) g 2 Z6) := by
              simpa only [A1] using
                jet_sub (I := I) (M := M) g 2 A12345 Z6
      _ ≤ 2 * ((9 * Q) ^ 2 + Q ^ 2) :=
        mul_le_mul_of_nonneg_left (add_le_add hA12345 h6) (by norm_num)
      _ ≤ (13 * Q) ^ 2 := by
        simpa using twice_scaled_sq_add_scaled_sq_le
          9 1 13 Q (by norm_num)
  have hA78 :
      covariantJetNormSq (I := I) (M := M) g 2 A78 ≤ (2 * Q) ^ 2 := by
    calc
      covariantJetNormSq (I := I) (M := M) g 2 A78 ≤
          2 * (covariantJetNormSq (I := I) (M := M) g 2 Z7 +
            covariantJetNormSq (I := I) (M := M) g 2 Z8) := by
              simpa only [A78] using
                jet_add1 (I := I) (M := M) g 2 Z7 Z8
      _ ≤ 2 * (Q ^ 2 + Q ^ 2) :=
        mul_le_mul_of_nonneg_left (add_le_add h7 h8) (by norm_num)
      _ = (2 * Q) ^ 2 := by ring
  have hA789 :
      covariantJetNormSq (I := I) (M := M) g 2 A789 ≤ (4 * Q) ^ 2 := by
    calc
      covariantJetNormSq (I := I) (M := M) g 2 A789 ≤
          2 * (covariantJetNormSq (I := I) (M := M) g 2 A78 +
            covariantJetNormSq (I := I) (M := M) g 2 Z9) := by
              simpa only [A789] using
                jet_sub (I := I) (M := M) g 2 A78 Z9
      _ ≤ 2 * ((2 * Q) ^ 2 + Q ^ 2) :=
        mul_le_mul_of_nonneg_left (add_le_add hA78 h9) (by norm_num)
      _ ≤ (4 * Q) ^ 2 := by
        simpa using twice_scaled_sq_add_scaled_sq_le
          2 1 4 Q (by norm_num)
  have hA78910 :
      covariantJetNormSq (I := I) (M := M) g 2 A78910 ≤ (6 * Q) ^ 2 := by
    calc
      covariantJetNormSq (I := I) (M := M) g 2 A78910 ≤
          2 * (covariantJetNormSq (I := I) (M := M) g 2 A789 +
            covariantJetNormSq (I := I) (M := M) g 2 Z10) := by
              simpa only [A78910] using
                jet_sub (I := I) (M := M) g 2 A789 Z10
      _ ≤ 2 * ((4 * Q) ^ 2 + Q ^ 2) :=
        mul_le_mul_of_nonneg_left (add_le_add hA789 h10) (by norm_num)
      _ ≤ (6 * Q) ^ 2 := by
        simpa using twice_scaled_sq_add_scaled_sq_le
          4 1 6 Q (by norm_num)
  have hA7891011 :
      covariantJetNormSq (I := I) (M := M) g 2 A7891011 ≤
        (9 * Q) ^ 2 := by
    calc
      covariantJetNormSq (I := I) (M := M) g 2 A7891011 ≤
          2 * (covariantJetNormSq (I := I) (M := M) g 2 A78910 +
            covariantJetNormSq (I := I) (M := M) g 2 Z11) := by
              simpa only [A7891011] using
                jet_sub (I := I) (M := M) g 2 A78910 Z11
      _ ≤ 2 * ((6 * Q) ^ 2 + Q ^ 2) :=
        mul_le_mul_of_nonneg_left (add_le_add hA78910 h11) (by norm_num)
      _ ≤ (9 * Q) ^ 2 := by
        simpa using twice_scaled_sq_add_scaled_sq_le
          6 1 9 Q (by norm_num)
  have hA2 :
      covariantJetNormSq (I := I) (M := M) g 2 A2 ≤ (13 * Q) ^ 2 := by
    calc
      covariantJetNormSq (I := I) (M := M) g 2 A2 ≤
          2 * (covariantJetNormSq (I := I) (M := M) g 2 A7891011 +
            covariantJetNormSq (I := I) (M := M) g 2 Z12) := by
              simpa only [A2] using
                jet_sub (I := I) (M := M) g 2 A7891011 Z12
      _ ≤ 2 * ((9 * Q) ^ 2 + Q ^ 2) :=
        mul_le_mul_of_nonneg_left (add_le_add hA7891011 h12) (by norm_num)
      _ ≤ (13 * Q) ^ 2 := by
        simpa using twice_scaled_sq_add_scaled_sq_le
          9 1 13 Q (by norm_num)
  have hO1 :
      covariantJetNormSq (I := I) (M := M) g 2 O1 ≤ (19 * Q) ^ 2 := by
    calc
      covariantJetNormSq (I := I) (M := M) g 2 O1 ≤
          2 * (covariantJetNormSq (I := I) (M := M) g 2 Z0 +
            covariantJetNormSq (I := I) (M := M) g 2 A1) := by
              simpa only [O1] using
                jet_add1 (I := I) (M := M) g 2 Z0 A1
      _ ≤ 2 * (Q ^ 2 + (13 * Q) ^ 2) :=
        mul_le_mul_of_nonneg_left (add_le_add h0 hA1) (by norm_num)
      _ ≤ (19 * Q) ^ 2 := by
        simpa using twice_scaled_sq_add_scaled_sq_le
          1 13 19 Q (by norm_num)
  have hO2 :
      covariantJetNormSq (I := I) (M := M) g 2 O2 ≤ (33 * Q) ^ 2 := by
    calc
      covariantJetNormSq (I := I) (M := M) g 2 O2 ≤
          2 * (covariantJetNormSq (I := I) (M := M) g 2 O1 +
            covariantJetNormSq (I := I) (M := M) g 2 A2) := by
              simpa only [O2] using
                jet_add1 (I := I) (M := M) g 2 O1 A2
      _ ≤ 2 * ((19 * Q) ^ 2 + (13 * Q) ^ 2) :=
        mul_le_mul_of_nonneg_left (add_le_add hO1 hA2) (by norm_num)
      _ ≤ (33 * Q) ^ 2 :=
        twice_scaled_sq_add_scaled_sq_le 19 13 33 Q (by norm_num)
  change covariantJetNormSq (I := I) (M := M) g 2 (O2 + Z13) ≤ _
  calc
    covariantJetNormSq (I := I) (M := M) g 2 (O2 + Z13) ≤
        2 * (covariantJetNormSq (I := I) (M := M) g 2 O2 +
          covariantJetNormSq (I := I) (M := M) g 2 Z13) :=
      jet_add1 (I := I) (M := M) g 2 O2 Z13
    _ ≤ 2 * ((33 * Q) ^ 2 + Q ^ 2) :=
      mul_le_mul_of_nonneg_left (add_le_add hO2 h13) (by norm_num)
    _ ≤ (47 * Q) ^ 2 := by
      simpa using twice_scaled_sq_add_scaled_sq_le
        33 1 47 Q (by norm_num)

omit [NeZero (Module.finrank ℝ E)] in
theorem connSec_self_h2
    (g gm : SmoothRiemannianMetric I M) :
    covariantJetNormSq (I := I) (M := M) g 2
        (connectionDifferenceSection (I := I) gm g) =
      covariantJetNormSq (I := I) (M := M) g 2
        (metricLoweredConnectionDifference (I := I) (M := M) g gm g) := by
  calc
    covariantJetNormSq (I := I) (M := M) g 2
        (connectionDifferenceSection (I := I) gm g) =
      covariantJetNormSq (I := I) (M := M) g 2
        (connectionDifferenceSection (I := I) gm g -
          connectionDifferenceSection (I := I) g g) := by
            rw [connectionDifferenceSection_self (I := I) (M := M) g, sub_zero]
    _ = covariantJetNormSq (I := I) (M := M) g 2
        (metricLoweredConnectionDifferenceCoefficient (I := I) g gm -
          metricLoweredConnectionDifferenceCoefficient (I := I) g g) :=
      connSec_h2_eq (I := I) (M := M) g gm g
    _ = covariantJetNormSq (I := I) (M := M) g 2
        (metricLoweredConnectionDifference (I := I) (M := M) g gm g) := rfl

theorem deTurckLieFirstOrder_pairing_h2_bound
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ ρ B0 B1 : ℝ,
      0 < ρ ∧ 0 ≤ B0 ∧ 0 ≤ B1 ∧
      ∀ (gT gU : SmoothRiemannianMetric I M)
        (T U : SmoothCcTensor g 0 2)
        (_hT : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g T x u v =
            ccTensorBilin (I := I) g T x v u)
        (_hU : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g U x u v =
            ccTensorBilin (I := I) g U x v u)
        (_hTtie : ∀ (x : M) (u v : TangentSpace I x),
          gT.inner x u v =
            g.inner x u v + ccTensorBilinSymm (I := I) g T x u v)
        (_hUtie : ∀ (x : M) (u v : TangentSpace I x),
          gU.inner x u v =
            g.inner x u v + ccTensorBilinSymm (I := I) g U x u v)
        {δ : ℝ} (_hδ_le : δ ≤ (1 : ℝ) / 3) (_hδ0 : 0 ≤ δ)
        (_hδT : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) δ)
        (_hδU : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g U) δ),
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ ≤ ρ →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) U‖ ≤ ρ →
        ∀ (A D3 : ℝ), 0 ≤ A → 0 ≤ D3 →
        covariantJetNormSq (I := I) (M := M) g 3 T ≤ A ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 3 (T - U) ≤ D3 ^ 2 →
      let D2 :=
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) (T - U)‖
      covariantJetNormSq (I := I) (M := M) g 2
          (deTurckLieArm1Coeff (I := I) (M := M) g gT g -
            deTurckLieArm1Coeff (I := I) (M := M) g gU g) ≤
        (B0 * D3 + B1 * D2 + B1 * A * D2) ^ 2 := by
  obtain ⟨ρt, Ct, hρt, hCt, htracePair⟩ :=
    RicciDeTurckLowOrder.trace2_pair_h2 (I := I) (M := M) hDim g
  obtain ⟨ρb, Tb, hρb, hTb, htraceBdd⟩ :=
    RicciDeTurckLowOrder.trace_two_sobolev_two_bound (I := I) (M := M) hDim g
  obtain ⟨ρp, Pp, P0, P1, hρp, hPp, hP0, hP1, hpsi⟩ :=
    psi_pair_h2 (I := I) (M := M) hDim g
      (δ₀ := (1 : ℝ) / 3) (by norm_num) (by norm_num)
  obtain ⟨C0, C1, hC0, hC1, hconn⟩ :=
    connSec_sub_tame (I := I) (M := M) hDim g
      (δ₀ := (1 : ℝ) / 3) (by norm_num) (by norm_num)
  obtain ⟨Kw, hKw, hconnBdd⟩ :=
    wXi_h2_low (I := I) (M := M) g
      (δ₀ := (1 : ℝ) / 3) (by norm_num) (by norm_num)
  obtain ⟨Cp, hCp, hpiece⟩ :=
    liePiece_pair (I := I) (M := M) hDim g
  obtain ⟨Ch, hCh, hhs⟩ :=
    hs2_low2 (I := I) (M := M) g 2
  let ρ : ℝ := min ρt (min ρb ρp)
  let R0 : ℝ := Ch * ρ
  let Hw : ℝ := Real.sqrt Kw
  let LC0 : ℝ := Cp * Tb * C0 R0
  let LC1 : ℝ := Cp * (Tb * C1 R0 * Ch + Ct * Hw)
  let LP0 : ℝ := Cp * Tb * P0
  let LP1 : ℝ := Cp * (Tb * P1 + Ct * Pp)
  let B0 : ℝ := 47 * (LC0 + LP0)
  let B1 : ℝ := 47 * (LC1 + LP1)
  have hρ : 0 < ρ := lt_min hρt (lt_min hρb hρp)
  have hR0 : 0 ≤ R0 := mul_nonneg hCh hρ.le
  have hHw : 0 ≤ Hw := Real.sqrt_nonneg _
  have hHwsq : Hw ^ 2 = Kw := by
    simpa only [Hw] using Real.sq_sqrt hKw
  have hLC0 : 0 ≤ LC0 :=
    mul_nonneg (mul_nonneg hCp hTb) (hC0 R0 hR0)
  have hLC1 : 0 ≤ LC1 :=
    mul_nonneg hCp
      (add_nonneg
        (mul_nonneg (mul_nonneg hTb (hC1 R0 hR0)) hCh)
        (mul_nonneg hCt hHw))
  have hLP0 : 0 ≤ LP0 := mul_nonneg (mul_nonneg hCp hTb) hP0
  have hLP1 : 0 ≤ LP1 :=
    mul_nonneg hCp
      (add_nonneg (mul_nonneg hTb hP1) (mul_nonneg hCt hPp))
  have hB0 : 0 ≤ B0 :=
    mul_nonneg (by norm_num) (add_nonneg hLC0 hLP0)
  have hB1 : 0 ≤ B1 :=
    mul_nonneg (by norm_num) (add_nonneg hLC1 hLP1)
  refine ⟨ρ, B0, B1, hρ, hB0, hB1, ?_⟩
  intro gT gU T U hT hU hTtie hUtie
    δ hδ_le hδ0 hδT hδU hTHs hUHs
    A D3 hA hD3 hT3 hTU3
  dsimp only
  let N : ℝ :=
    ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) (T - U)‖
  let CT : SmoothCcTensor g 1 2 := connectionDifferenceSection (I := I) gT g
  let CU : SmoothCcTensor g 1 2 := connectionDifferenceSection (I := I) gU g
  let PT : SmoothCcTensor g 1 2 :=
    deTurckLieArmOneBackgroundCoefficient (I := I) (M := M) g gT g
  let PU : SmoothCcTensor g 1 2 :=
    deTurckLieArmOneBackgroundCoefficient (I := I) (M := M) g gU g
  let XC : ℝ := C0 R0 * D3 +
    C1 R0 * (Ch * N) + C1 R0 * A * (Ch * N)
  let XP : ℝ := P0 * D3 + P1 * N + P1 * A * N
  let YC : ℝ := Cp *
    (Tb * XC + (Ct * N) * (Hw * (1 + A)))
  let YP : ℝ := Cp *
    (Tb * XP + (Ct * N) * (Pp * (1 + A)))
  have hN : 0 ≤ N := norm_nonneg _
  have hTHst : ‖ccTensorToHs (I := I) (M := M) g 2
      (2 : ℝ) T‖ ≤ ρt := hTHs.trans (min_le_left _ _)
  have hUHst : ‖ccTensorToHs (I := I) (M := M) g 2
      (2 : ℝ) U‖ ≤ ρt := hUHs.trans (min_le_left _ _)
  have hTHsb : ‖ccTensorToHs (I := I) (M := M) g 2
      (2 : ℝ) T‖ ≤ ρb :=
    hTHs.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hUHsb : ‖ccTensorToHs (I := I) (M := M) g 2
      (2 : ℝ) U‖ ≤ ρb :=
    hUHs.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hTHsp : ‖ccTensorToHs (I := I) (M := M) g 2
      (2 : ℝ) T‖ ≤ ρp :=
    hTHs.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hUHsp : ‖ccTensorToHs (I := I) (M := M) g 2
      (2 : ℝ) U‖ ≤ ρp :=
    hUHs.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hT2 :
      covariantJetNormSq (I := I) (M := M) g 2 T ≤ R0 ^ 2 := by
    calc
      covariantJetNormSq (I := I) (M := M) g 2 T ≤
          (Ch * ‖ccTensorToHs (I := I) (M := M) g 2
            (2 : ℝ) T‖) ^ 2 := by
        simpa only [covariantJetNormSq, Nat.reduceAdd] using hhs T
      _ ≤ (Ch * ρ) ^ 2 :=
        pow_le_pow_left₀
          (mul_nonneg hCh (norm_nonneg _))
          (mul_le_mul_of_nonneg_left hTHs hCh) 2
      _ = R0 ^ 2 := rfl
  have hU2 :
      covariantJetNormSq (I := I) (M := M) g 2 U ≤ R0 ^ 2 := by
    calc
      covariantJetNormSq (I := I) (M := M) g 2 U ≤
          (Ch * ‖ccTensorToHs (I := I) (M := M) g 2
            (2 : ℝ) U‖) ^ 2 := by
        simpa only [covariantJetNormSq, Nat.reduceAdd] using hhs U
      _ ≤ (Ch * ρ) ^ 2 :=
        pow_le_pow_left₀
          (mul_nonneg hCh (norm_nonneg _))
          (mul_le_mul_of_nonneg_left hUHs hCh) 2
      _ = R0 ^ 2 := rfl
  have hTU2 :
      covariantJetNormSq (I := I) (M := M) g 2 (T - U) ≤
        (Ch * N) ^ 2 := by
    simpa only [covariantJetNormSq, Nat.reduceAdd, N] using hhs (T - U)
  have hTrU : ∀ σ : Equiv.Perm (Fin 4),
      covariantJetNormSq (I := I) (M := M) g 2
          (deTurckLieTraceCoeff (I := I) (M := M) g gU σ) ≤
        Tb ^ 2 := by
    intro σ
    rw [lieTrace_eq (I := I) (M := M) g gU σ,
      reindex_h2_eq (I := I) (M := M)]
    exact htraceBdd U gU hUtie hUHsb
  have hTrD : ∀ σ : Equiv.Perm (Fin 4),
      covariantJetNormSq (I := I) (M := M) g 2
          (deTurckLieTraceCoeff (I := I) (M := M) g gT σ -
            deTurckLieTraceCoeff (I := I) (M := M) g gU σ) ≤
        (Ct * N) ^ 2 := by
    intro σ
    have heq :
        deTurckLieTraceCoeff (I := I) (M := M) g gT σ -
            deTurckLieTraceCoeff (I := I) (M := M) g gU σ =
          reindexCoeffGen (I := I) (M := M) g 4 2
            (pureTrace (I := I) (M := M) g gT 2 -
              pureTrace (I := I) (M := M) g gU 2) σ := by
      rw [lieTrace_eq (I := I) (M := M) g gT σ,
        lieTrace_eq (I := I) (M := M) g gU σ,
        reindex_sub_c1 (I := I) (M := M) g 4 2]
    rw [heq, reindex_h2_eq (I := I) (M := M)]
    simpa only [N] using
      htracePair T U gT gU hTtie hUtie hTHst hUHst
  have hCT :
      covariantJetNormSq (I := I) (M := M) g 2 CT ≤
        (Hw * (1 + A)) ^ 2 := by
    rw [show covariantJetNormSq (I := I) (M := M) g 2 CT =
        covariantJetNormSq (I := I) (M := M) g 2
          (metricLoweredConnectionDifference (I := I) (M := M) g gT g) by
      simpa only [CT] using
        connSec_self_h2 (I := I) (M := M) g gT]
    calc
      covariantJetNormSq (I := I) (M := M) g 2
          (metricLoweredConnectionDifference (I := I) (M := M) g gT g) ≤
        Kw * (1 + covariantJetNormSq (I := I) (M := M) g 3 T) :=
          hconnBdd gT T hT hTtie hδ_le hδ0 hδT
      _ ≤ Kw * (1 + A ^ 2) :=
        mul_le_mul_of_nonneg_left (add_le_add le_rfl hT3) hKw
      _ = Hw ^ 2 * (1 + A ^ 2) := by rw [hHwsq]
      _ ≤ Hw ^ 2 * (1 + A) ^ 2 := by
        exact mul_le_mul_of_nonneg_left
          (one_add_sq_le_sq_one_add hA) (sq_nonneg Hw)
      _ = (Hw * (1 + A)) ^ 2 := by ring
  have hCD :
      covariantJetNormSq (I := I) (M := M) g 2 (CT - CU) ≤ XC ^ 2 := by
    simpa only [CT, CU, XC] using
      hconn gT gU T U hT hU hTtie hUtie
        hδ_le hδ0 hδT hδ_le hδ0 hδU
        R0 A (Ch * N) D3 hR0 hA (mul_nonneg hCh hN) hD3
        hU2 hT3 hTU2 hTU3
  have hPsiRaw := hpsi gT gU T U hT hU hTtie hUtie
    hδ_le hδ0 hδT hδ_le hδ0 hδU
    hTHsp hUHsp A D3 hA hD3 hT3 hTU3
  have hPT :
      covariantJetNormSq (I := I) (M := M) g 2 PT ≤
        (Pp * (1 + A)) ^ 2 := by
    simpa only [PT] using hPsiRaw.1
  have hPD :
      covariantJetNormSq (I := I) (M := M) g 2 (PT - PU) ≤ XP ^ 2 := by
    simpa only [PT, PU, XP, N] using hPsiRaw.2
  have hXC : 0 ≤ XC :=
    add_nonneg
      (add_nonneg (mul_nonneg (hC0 R0 hR0) hD3)
        (mul_nonneg (hC1 R0 hR0) (mul_nonneg hCh hN)))
      (mul_nonneg
        (mul_nonneg (hC1 R0 hR0) hA)
        (mul_nonneg hCh hN))
  have hXP : 0 ≤ XP :=
    add_nonneg
      (add_nonneg (mul_nonneg hP0 hD3) (mul_nonneg hP1 hN))
      (mul_nonneg (mul_nonneg hP1 hA) hN)
  have hYC : 0 ≤ YC :=
    mul_nonneg hCp
      (add_nonneg (mul_nonneg hTb hXC)
        (mul_nonneg (mul_nonneg hCt hN)
          (mul_nonneg hHw (by linarith))))
  have hYP : 0 ≤ YP :=
    mul_nonneg hCp
      (add_nonneg (mul_nonneg hTb hXP)
        (mul_nonneg (mul_nonneg hCt hN)
          (mul_nonneg hPp (by linarith))))
  have hConnPiece : ∀ (σ : Equiv.Perm (Fin 4))
      (r : Equiv.Perm (Fin 3)),
      covariantJetNormSq (I := I) (M := M) g 2
          (lieArm1Piece (I := I) (M := M) g gT σ r CT -
            lieArm1Piece (I := I) (M := M) g gU σ r CU) ≤
        YC ^ 2 := by
    intro σ r
    simpa only [YC] using
      hpiece gT gU σ r CT CU
        Tb (Ct * N) (Hw * (1 + A)) XC
        hTb (mul_nonneg hCt hN)
        (mul_nonneg hHw (by linarith)) hXC
        (hTrU σ) (hTrD σ) hCT hCD
  have hPsiPiece : ∀ (σ : Equiv.Perm (Fin 4))
      (r : Equiv.Perm (Fin 3)),
      covariantJetNormSq (I := I) (M := M) g 2
          (lieArm1Piece (I := I) (M := M) g gT σ r PT -
            lieArm1Piece (I := I) (M := M) g gU σ r PU) ≤
        YP ^ 2 := by
    intro σ r
    simpa only [YP] using
      hpiece gT gU σ r PT PU
        Tb (Ct * N) (Pp * (1 + A)) XP
        hTb (mul_nonneg hCt hN)
        (mul_nonneg hPp (by linarith)) hXP
        (hTrU σ) (hTrD σ) hPT hPD
  have hBackgroundPiece : ∀ (σ : Equiv.Perm (Fin 4))
      (r : Equiv.Perm (Fin 3)),
      covariantJetNormSq (I := I) (M := M) g 2
          (lieArm1Piece (I := I) (M := M) g gT σ r
              (deTurckLieArmOneBackgroundConnectionDifference (I := I) (M := M) g gT g) -
            lieArm1Piece (I := I) (M := M) g gU σ r
              (deTurckLieArmOneBackgroundConnectionDifference (I := I) (M := M) g gU g)) ≤
        YC ^ 2 := by
    intro σ r
    simpa only [CT, CU, connBackground_eq (I := I) (M := M)] using
      hConnPiece σ r
  let Z0 : SmoothCcTensor g 3 2 :=
    lieArm1Piece (I := I) (M := M) g gT lieArm1SigmaC
        lieArm1RhoSlot0
        (deTurckLieArmOneBackgroundConnectionDifference (I := I) (M := M) g gT g) -
      lieArm1Piece (I := I) (M := M) g gU lieArm1SigmaC
        lieArm1RhoSlot0
        (deTurckLieArmOneBackgroundConnectionDifference (I := I) (M := M) g gU g)
  let Z1 : SmoothCcTensor g 3 2 :=
    lieArm1Piece (I := I) (M := M) g gT lieArm1SigmaA
        (Equiv.refl (Fin 3)) CT -
      lieArm1Piece (I := I) (M := M) g gU lieArm1SigmaA
        (Equiv.refl (Fin 3)) CU
  let Z2 : SmoothCcTensor g 3 2 :=
    lieArm1Piece (I := I) (M := M) g gT lieArm1SigmaA
        (Equiv.refl (Fin 3)) PT -
      lieArm1Piece (I := I) (M := M) g gU lieArm1SigmaA
        (Equiv.refl (Fin 3)) PU
  let Z3 : SmoothCcTensor g 3 2 :=
    lieArm1Piece (I := I) (M := M) g gT lieArm1SigmaC
        (Equiv.refl (Fin 3)) CT -
      lieArm1Piece (I := I) (M := M) g gU lieArm1SigmaC
        (Equiv.refl (Fin 3)) CU
  let Z4 : SmoothCcTensor g 3 2 :=
    lieArm1Piece (I := I) (M := M) g gT lieArm1SigmaD
        lieArm1RhoSlot0 CT -
      lieArm1Piece (I := I) (M := M) g gU lieArm1SigmaD
        lieArm1RhoSlot0 CU
  let Z5 : SmoothCcTensor g 3 2 :=
    lieArm1Piece (I := I) (M := M) g gT (Equiv.refl (Fin 4))
        lieArm1RhoSlot1 CT -
      lieArm1Piece (I := I) (M := M) g gU (Equiv.refl (Fin 4))
        lieArm1RhoSlot1 CU
  let Z6 : SmoothCcTensor g 3 2 :=
    lieArm1Piece (I := I) (M := M) g gT lieArm1SigmaF
        (Equiv.refl (Fin 3)) CT -
      lieArm1Piece (I := I) (M := M) g gU lieArm1SigmaF
        (Equiv.refl (Fin 3)) CU
  let Z7 : SmoothCcTensor g 3 2 :=
    lieArm1Piece (I := I) (M := M) g gT lieArm1SigmaASwap
        (Equiv.refl (Fin 3)) CT -
      lieArm1Piece (I := I) (M := M) g gU lieArm1SigmaASwap
        (Equiv.refl (Fin 3)) CU
  let Z8 : SmoothCcTensor g 3 2 :=
    lieArm1Piece (I := I) (M := M) g gT lieArm1SigmaASwap
        (Equiv.refl (Fin 3)) PT -
      lieArm1Piece (I := I) (M := M) g gU lieArm1SigmaASwap
        (Equiv.refl (Fin 3)) PU
  let Z9 : SmoothCcTensor g 3 2 :=
    lieArm1Piece (I := I) (M := M) g gT lieArm1SigmaCSwap
        (Equiv.refl (Fin 3)) CT -
      lieArm1Piece (I := I) (M := M) g gU lieArm1SigmaCSwap
        (Equiv.refl (Fin 3)) CU
  let Z10 : SmoothCcTensor g 3 2 :=
    lieArm1Piece (I := I) (M := M) g gT lieArm1SigmaDSwap
        lieArm1RhoSlot0 CT -
      lieArm1Piece (I := I) (M := M) g gU lieArm1SigmaDSwap
        lieArm1RhoSlot0 CU
  let Z11 : SmoothCcTensor g 3 2 :=
    lieArm1Piece (I := I) (M := M) g gT lieArm1SigmaESwap
        lieArm1RhoSlot1 CT -
      lieArm1Piece (I := I) (M := M) g gU lieArm1SigmaESwap
        lieArm1RhoSlot1 CU
  let Z12 : SmoothCcTensor g 3 2 :=
    lieArm1Piece (I := I) (M := M) g gT lieArm1SigmaFSwap
        (Equiv.refl (Fin 3)) CT -
      lieArm1Piece (I := I) (M := M) g gU lieArm1SigmaFSwap
        (Equiv.refl (Fin 3)) CU
  let Z13 : SmoothCcTensor g 3 2 :=
    lieArm1Piece (I := I) (M := M) g gT (Equiv.refl (Fin 4))
        lieArm1RhoSlot0 CT -
      lieArm1Piece (I := I) (M := M) g gU (Equiv.refl (Fin 4))
        lieArm1RhoSlot0 CU
  let Q : ℝ := YC + YP
  have hQ : 0 ≤ Q := add_nonneg hYC hYP
  have hCQ : YC ^ 2 ≤ Q ^ 2 :=
    pow_le_pow_left₀ hYC (by dsimp only [Q]; linarith) 2
  have hPQ : YP ^ 2 ≤ Q ^ 2 :=
    pow_le_pow_left₀ hYP (by dsimp only [Q]; linarith) 2
  have hZ0 :
      covariantJetNormSq (I := I) (M := M) g 2 Z0 ≤ Q ^ 2 :=
    (hBackgroundPiece lieArm1SigmaC lieArm1RhoSlot0).trans hCQ
  have hZ1 :
      covariantJetNormSq (I := I) (M := M) g 2 Z1 ≤ Q ^ 2 :=
    (hConnPiece lieArm1SigmaA (Equiv.refl (Fin 3))).trans hCQ
  have hZ2 :
      covariantJetNormSq (I := I) (M := M) g 2 Z2 ≤ Q ^ 2 :=
    (hPsiPiece lieArm1SigmaA (Equiv.refl (Fin 3))).trans hPQ
  have hZ3 :
      covariantJetNormSq (I := I) (M := M) g 2 Z3 ≤ Q ^ 2 :=
    (hConnPiece lieArm1SigmaC (Equiv.refl (Fin 3))).trans hCQ
  have hZ4 :
      covariantJetNormSq (I := I) (M := M) g 2 Z4 ≤ Q ^ 2 :=
    (hConnPiece lieArm1SigmaD lieArm1RhoSlot0).trans hCQ
  have hZ5 :
      covariantJetNormSq (I := I) (M := M) g 2 Z5 ≤ Q ^ 2 :=
    (hConnPiece (Equiv.refl (Fin 4)) lieArm1RhoSlot1).trans hCQ
  have hZ6 :
      covariantJetNormSq (I := I) (M := M) g 2 Z6 ≤ Q ^ 2 :=
    (hConnPiece lieArm1SigmaF (Equiv.refl (Fin 3))).trans hCQ
  have hZ7 :
      covariantJetNormSq (I := I) (M := M) g 2 Z7 ≤ Q ^ 2 :=
    (hConnPiece lieArm1SigmaASwap (Equiv.refl (Fin 3))).trans hCQ
  have hZ8 :
      covariantJetNormSq (I := I) (M := M) g 2 Z8 ≤ Q ^ 2 :=
    (hPsiPiece lieArm1SigmaASwap (Equiv.refl (Fin 3))).trans hPQ
  have hZ9 :
      covariantJetNormSq (I := I) (M := M) g 2 Z9 ≤ Q ^ 2 :=
    (hConnPiece lieArm1SigmaCSwap (Equiv.refl (Fin 3))).trans hCQ
  have hZ10 :
      covariantJetNormSq (I := I) (M := M) g 2 Z10 ≤ Q ^ 2 :=
    (hConnPiece lieArm1SigmaDSwap lieArm1RhoSlot0).trans hCQ
  have hZ11 :
      covariantJetNormSq (I := I) (M := M) g 2 Z11 ≤ Q ^ 2 :=
    (hConnPiece lieArm1SigmaESwap lieArm1RhoSlot1).trans hCQ
  have hZ12 :
      covariantJetNormSq (I := I) (M := M) g 2 Z12 ≤ Q ^ 2 :=
    (hConnPiece lieArm1SigmaFSwap (Equiv.refl (Fin 3))).trans hCQ
  have hZ13 :
      covariantJetNormSq (I := I) (M := M) g 2 Z13 ≤ Q ^ 2 :=
    (hConnPiece (Equiv.refl (Fin 4)) lieArm1RhoSlot0).trans hCQ
  have hdecomp :
      deTurckLieArm1Coeff (I := I) (M := M) g gT g -
          deTurckLieArm1Coeff (I := I) (M := M) g gU g =
        Z0 + (Z1 + Z2 - Z3 - Z4 - Z5 - Z6) +
          (Z7 + Z8 - Z9 - Z10 - Z11 - Z12) + Z13 := by
    rw [deTurckLieArm1Coeff_eq_lieArm1Piece_sum
        (I := I) (M := M) g gT g,
      deTurckLieArm1Coeff_eq_lieArm1Piece_sum
        (I := I) (M := M) g gU g]
    dsimp only [Z0, Z1, Z2, Z3, Z4, Z5, Z6, Z7, Z8, Z9,
      Z10, Z11, Z12, Z13, CT, CU, PT, PU]
    module
  have hYCeq :
      YC = LC0 * D3 + LC1 * N + LC1 * A * N := by
    simp only [YC, XC, LC0, LC1]
    ring
  have hYPeq :
      YP = LP0 * D3 + LP1 * N + LP1 * A * N := by
    simp only [YP, XP, LP0, LP1]
    ring
  rw [hdecomp]
  calc
    covariantJetNormSq (I := I) (M := M) g 2
        (Z0 + (Z1 + Z2 - Z3 - Z4 - Z5 - Z6) +
          (Z7 + Z8 - Z9 - Z10 - Z11 - Z12) + Z13) ≤
      (47 * Q) ^ 2 :=
        jet14 (I := I) (M := M) g Q
          Z0 Z1 Z2 Z3 Z4 Z5 Z6 Z7 Z8 Z9 Z10 Z11 Z12 Z13
          hZ0 hZ1 hZ2 hZ3 hZ4 hZ5 hZ6 hZ7 hZ8 hZ9 hZ10 hZ11 hZ12 hZ13
    _ = (47 * ((LC0 + LP0) * D3 +
          (LC1 + LP1) * N + (LC1 + LP1) * A * N)) ^ 2 := by
      rw [show Q = (LC0 + LP0) * D3 +
          (LC1 + LP1) * N + (LC1 + LP1) * A * N by
        dsimp only [Q]
        rw [hYCeq, hYPeq]
        ring]
    _ = (B0 * D3 + B1 * N + B1 * A * N) ^ 2 := by
      rw [show B0 = 47 * (LC0 + LP0) by rfl,
        show B1 = 47 * (LC1 + LP1) by rfl]
      ring

theorem ricciDeTurckRemainderFirstOrderCoefficient_pairing_h2_bound
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ ρ B0 B1 : ℝ,
      0 < ρ ∧ 0 ≤ B0 ∧ 0 ≤ B1 ∧
      ∀ (gT gU : SmoothRiemannianMetric I M)
        (T U : SmoothCcTensor g 0 2)
        (_hT : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g T x u v =
            ccTensorBilin (I := I) g T x v u)
        (_hU : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g U x u v =
            ccTensorBilin (I := I) g U x v u)
        (_hTtie : ∀ (x : M) (u v : TangentSpace I x),
          gT.inner x u v =
            g.inner x u v + ccTensorBilinSymm (I := I) g T x u v)
        (_hUtie : ∀ (x : M) (u v : TangentSpace I x),
          gU.inner x u v =
            g.inner x u v + ccTensorBilinSymm (I := I) g U x u v)
        {δ : ℝ} (_hδ_le : δ ≤ (1 : ℝ) / 3) (_hδ0 : 0 ≤ δ)
        (_hδT : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) δ)
        (_hδU : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g U) δ)
        (_hδZ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g
            (0 : SmoothCcTensor g 0 2)) δ),
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ ≤ ρ →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) U‖ ≤ ρ →
        ∀ (A D3 : ℝ), 0 ≤ A → 0 ≤ D3 →
        covariantJetNormSq (I := I) (M := M) g 3 T ≤ A ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 3 (T - U) ≤ D3 ^ 2 →
      let D2 :=
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) (T - U)‖
      covariantJetNormSq (I := I) (M := M) g 2
          ((-2 : ℝ) •
              (linearizedRicciConnectionDifferenceOrder1CoeffField
                  (I := I) (M := M) g gT -
                linearizedRicciConnectionDifferenceOrder1CoeffField
                  (I := I) (M := M) g gU) +
            (deTurckLieArm1Coeff (I := I) (M := M) g gT g -
              deTurckLieArm1Coeff (I := I) (M := M) g gU g)) ≤
        (B0 * D3 + B1 * D2 + B1 * A * D2) ^ 2 := by
  obtain ⟨ρr, R0, R1, hρr, hR0, hR1, hricci⟩ :=
    exists_linearizedRicciConnectionDifferenceOrderOneCoefficient_pairing_secondOrder_bound (I := I) (M := M) hDim g
  obtain ⟨ρl, L0, L1, hρl, hL0, hL1, hlie⟩ :=
    deTurckLieFirstOrder_pairing_h2_bound (I := I) (M := M) hDim g
  let ρ : ℝ := min ρr ρl
  let B0 : ℝ := 4 * R0 + 2 * L0
  let B1 : ℝ := 4 * R1 + 2 * L1
  have hρ : 0 < ρ := lt_min hρr hρl
  have hB0 : 0 ≤ B0 :=
    add_nonneg (mul_nonneg (by norm_num) hR0)
      (mul_nonneg (by norm_num) hL0)
  have hB1 : 0 ≤ B1 :=
    add_nonneg (mul_nonneg (by norm_num) hR1)
      (mul_nonneg (by norm_num) hL1)
  refine ⟨ρ, B0, B1, hρ, hB0, hB1, ?_⟩
  intro gT gU T U hT hU hTtie hUtie
    δ hδ_le hδ0 hδT hδU hδZ hTHs hUHs
    A D3 hA hD3 hT3 hTU3
  dsimp only
  let N : ℝ :=
    ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) (T - U)‖
  let XR : ℝ := R0 * D3 + R1 * N + R1 * A * N
  let XL : ℝ := L0 * D3 + L1 * N + L1 * A * N
  let VR : SmoothCcTensor g 3 2 :=
    linearizedRicciConnectionDifferenceOrder1CoeffField
        (I := I) (M := M) g gT -
      linearizedRicciConnectionDifferenceOrder1CoeffField
        (I := I) (M := M) g gU
  let VL : SmoothCcTensor g 3 2 :=
    deTurckLieArm1Coeff (I := I) (M := M) g gT g -
      deTurckLieArm1Coeff (I := I) (M := M) g gU g
  have hN : 0 ≤ N := norm_nonneg _
  have hXR : 0 ≤ XR :=
    add_nonneg
      (add_nonneg (mul_nonneg hR0 hD3) (mul_nonneg hR1 hN))
      (mul_nonneg (mul_nonneg hR1 hA) hN)
  have hXL : 0 ≤ XL :=
    add_nonneg
      (add_nonneg (mul_nonneg hL0 hD3) (mul_nonneg hL1 hN))
      (mul_nonneg (mul_nonneg hL1 hA) hN)
  have hVR :
      covariantJetNormSq (I := I) (M := M) g 2 VR ≤ XR ^ 2 := by
    simpa only [VR, XR, N] using
      hricci gT gU T U hT hU hTtie hUtie
        hδ_le hδ0 hδT hδU hδZ
        (hTHs.trans (min_le_left _ _))
        (hUHs.trans (min_le_left _ _))
        A D3 hA hD3 hT3 hTU3
  have hVL :
      covariantJetNormSq (I := I) (M := M) g 2 VL ≤ XL ^ 2 := by
    simpa only [VL, XL, N] using
      hlie gT gU T U hT hU hTtie hUtie
        hδ_le hδ0 hδT hδU
        (hTHs.trans (min_le_right _ _))
        (hUHs.trans (min_le_right _ _))
        A D3 hA hD3 hT3 hTU3
  have hRicS :
      covariantJetNormSq (I := I) (M := M) g 2 ((-2 : ℝ) • VR) ≤
        (2 * XR) ^ 2 := by
    rw [jet_smul1 (I := I) (M := M) g 2]
    calc
      (-2 : ℝ) ^ 2 * covariantJetNormSq (I := I) (M := M) g 2 VR ≤
          (-2 : ℝ) ^ 2 * XR ^ 2 :=
        mul_le_mul_of_nonneg_left hVR (sq_nonneg _)
      _ = (2 * XR) ^ 2 := by ring
  change covariantJetNormSq (I := I) (M := M) g 2
      ((-2 : ℝ) • VR + VL) ≤ _
  calc
    covariantJetNormSq (I := I) (M := M) g 2
        ((-2 : ℝ) • VR + VL) ≤
      2 * (covariantJetNormSq (I := I) (M := M) g 2 ((-2 : ℝ) • VR) +
        covariantJetNormSq (I := I) (M := M) g 2 VL) :=
      jet_add1 (I := I) (M := M) g 2 ((-2 : ℝ) • VR) VL
    _ ≤ 2 * ((2 * XR) ^ 2 + XL ^ 2) :=
      mul_le_mul_of_nonneg_left (add_le_add hRicS hVL) (by norm_num)
    _ ≤ (2 * (2 * XR + XL)) ^ 2 := by
      calc
        2 * ((2 * XR) ^ 2 + XL ^ 2) ≤
            2 * (2 * XR + XL) ^ 2 :=
          mul_le_mul_of_nonneg_left
            (sq_add_sq_le_add_sq (mul_nonneg (by norm_num) hXR) hXL) (by norm_num)
        _ ≤ 4 * (2 * XR + XL) ^ 2 :=
          mul_le_mul_of_nonneg_right (by norm_num) (sq_nonneg _)
        _ = (2 * (2 * XR + XL)) ^ 2 := by ring
    _ = (B0 * D3 + B1 * N + B1 * A * N) ^ 2 := by
      simp only [B0, B1, XR, XL]
      ring

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

end
