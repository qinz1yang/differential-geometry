import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.LieCorrection.ZeroOrder.MixedConnectionExpansion
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.IteratedCovGradFibreNormPermutationInvariance
import DifferentialGeometry.Analysis.Spectral.Intrinsic.MetricRealization.TensorHsRealize
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.LieCorrection.TameBounds

noncomputable section


open Bundle Manifold DifferentialGeometry.Tensor0SBundle
open scoped Manifold Topology ContDiff BigOperators

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Spectral.MetricRealization
open DifferentialGeometry.Analysis.Spectral.DeTurck
open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Analysis.Spectral.LieCorrectionZeroCore
open DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Analysis.Elliptic
open DifferentialGeometry.Geometry.Curvature

variable
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
      [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [SigmaCompactSpace M] in
theorem kappa_unit (g₀ g₁ gB : SmoothRiemannianMetric I M) (x : M)
    (m : Fin 3 → E) :
    unitModel (I := I) (M := M) g₀ 3
        (lieCorrectionZeroKappa (I := I) (M := M) g₀ g₁ gB) x m =
      g₁.inner x (PDE.DeTurck.connectionDifference (I := I) g₁ gB x
        ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm (m 0))
        ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm (m 1)))
        ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm (m 2)) :=
  lieCorrectionZeroKappa_unitModel_apply (I := I) (M := M) g₀ g₁ gB x m

open DifferentialGeometry.Integral.DivergenceTheorem in
omit [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
private theorem koszul_g1 (g₀ g₁ : SmoothRiemannianMetric I M)
    (P : SmoothCcTensor g₀ 0 2)
    (htie : ∀ (y : M) (v w : TangentSpace I y),
      g₁.inner y v w = g₀.inner y v w +
        ccTensorBilinSymm (I := I) g₀ P y v w)
    (x : M) (a b c : TangentSpace I x) :
    unitModel (I := I) (M := M) g₀ 3
        (koszulCovecCc (I := I) g₀ P) x
          ![tangentSpaceModelContinuousLinearEquiv (I := I) x c,
            tangentSpaceModelContinuousLinearEquiv (I := I) x a,
            tangentSpaceModelContinuousLinearEquiv (I := I) x b] =
      g₁.inner x (PDE.DeTurck.connectionDifference (I := I) g₁ g₀ x a b) c := by
  rw [koszulCovecCc_unitModel (I := I) (M := M) g₀ P x a b c]
  rw [connectionDifferenceInner_g1_eq_half_covGrad_ccTensor02Symm
    (I := I) (M := M) g₀ g₁ P htie x a b c]
  rfl

omit [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem kappa_self (g₀ g₁ : SmoothRiemannianMetric I M)
    (P : SmoothCcTensor g₀ 0 2)
    (htie : ∀ (y : M) (v w : TangentSpace I y),
      g₁.inner y v w = g₀.inner y v w +
        ccTensorBilinSymm (I := I) g₀ P y v w) :
    lieCorrectionZeroKappa (I := I) (M := M) g₀ g₁ g₀ =
      domDomCongrSection (I := I) g₀ (finRotate 3).symm
        (koszulCovecCc (I := I) g₀ P) :=
  lieCorrectionZeroKappa_self_eq_koszulCovecCc (I := I) (M := M) g₀ g₁ P htie

private def pbLowCompatField (g₀ : SmoothRiemannianMetric I M)
    (P : SmoothCcTensor g₀ 0 2) (gA gB : SmoothRiemannianMetric I M) :
    Tensor0SBundle.Tensor0SField (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) ∞ 3 :=
  letI := Tensor0SBundle.tensor0SBundleTopology
    (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) 3
  ⟨fun x => ccBilinConnectionDifferenceLoweredFib (I := I) g₀ P gA gB x,
    ccBilinConnectionDifferenceLoweredFib_contMDiff (I := I) g₀ P gA gB⟩

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
omit [SigmaCompactSpace M] in
theorem pbLow_unit (g₀ : SmoothRiemannianMetric I M)
    (P : SmoothCcTensor g₀ 0 2) (gA gB : SmoothRiemannianMetric I M)
    (x : M) (m : Fin 3 → E) :
    unitModel (I := I) (M := M) g₀ 3
        (lieCorrectionZeroPbLow (I := I) (M := M) g₀ P gA gB) x m =
      ccTensorBilinSymm (I := I) g₀ P x
        (PDE.DeTurck.connectionDifference (I := I) gA gB x
          ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm (m 0))
          ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm (m 1)))
        ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm (m 2)) := by
  rw [unitModel]
  rw [show (lieCorrectionZeroPbLow (I := I) (M := M) g₀ P gA gB).toSection x
      (unitTensor (I := I) (M := M) x) =
      (MixedSection.eval₀ (F := E) (E := (TangentSpace I : M → Type _)) x).smulRight
        (pbLowCompatField (I := I) (M := M) g₀ P gA gB x)
        (ContinuousMultilinearMap.constOfIsEmpty ℝ
          (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ)) from rfl]
  rw [ContinuousLinearMap.smulRight_apply, MixedSection.eval₀_apply,
    ContinuousMultilinearMap.constOfIsEmpty_apply, one_smul]
  exact ccBilinConnectionDifferenceLoweredFib_toModel (I := I) g₀ P gA gB x m

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
omit [SigmaCompactSpace M] in
theorem pbLow_sub (g₀ : SmoothRiemannianMetric I M)
    (P Q : SmoothCcTensor g₀ 0 2) (gA gB : SmoothRiemannianMetric I M) :
    lieCorrectionZeroPbLow (I := I) (M := M) g₀ (P - Q) gA gB =
      lieCorrectionZeroPbLow (I := I) (M := M) g₀ P gA gB -
        lieCorrectionZeroPbLow (I := I) (M := M) g₀ Q gA gB := by
  apply smoothCcTensor_ext_of_unitModel (I := I) (M := M) g₀
  intro x
  apply ContinuousMultilinearMap.ext
  intro m
  rw [show unitModel (I := I) (M := M) g₀ 3
      (lieCorrectionZeroPbLow (I := I) (M := M) g₀ P gA gB -
        lieCorrectionZeroPbLow (I := I) (M := M) g₀ Q gA gB) x m =
      unitModel (I := I) (M := M) g₀ 3
          (lieCorrectionZeroPbLow (I := I) (M := M) g₀ P gA gB) x m -
        unitModel (I := I) (M := M) g₀ 3
          (lieCorrectionZeroPbLow (I := I) (M := M) g₀ Q gA gB) x m by
    simp only [unitModel]
    rw [SmoothCcTensor.toSection_sub, ContMDiffSection.coe_sub, Pi.sub_apply,
      sub_apply, Tensor0SSpace.toModel_sub, sub_apply]]
  rw [pbLow_unit (I := I) (M := M) g₀ (P - Q) gA gB x m,
    pbLow_unit (I := I) (M := M) g₀ P gA gB x m,
    pbLow_unit (I := I) (M := M) g₀ Q gA gB x m,
    ccTensorBilinSymm_sub]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private theorem unit_add0 (g₀ : SmoothRiemannianMetric I M) (s : ℕ)
    (A B : SmoothCcTensor g₀ 0 s) (x : M) (m : Fin s → E) :
    unitModel (I := I) (M := M) g₀ s (A + B) x m =
      unitModel (I := I) (M := M) g₀ s A x m +
        unitModel (I := I) (M := M) g₀ s B x m := by
  rw [unitModel, unitModel, unitModel]
  rw [show (A + B).toSection x = A.toSection x + B.toSection x from by
    rw [SmoothCcTensor.toSection_add]; rfl]
  rw [show ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from
      A.toSection x + B.toSection x) (unitTensor (I := I) (M := M) x)) =
      (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from A.toSection x)
          (unitTensor (I := I) (M := M) x) +
        (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from B.toSection x)
          (unitTensor (I := I) (M := M) x) from rfl]
  rw [Tensor0SSpace.toModel_add, add_apply]

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
omit [SigmaCompactSpace M] in
theorem kappa_bg (g₀ g₁ gB : SmoothRiemannianMetric I M)
    (P : SmoothCcTensor g₀ 0 2)
    (htie : ∀ (y : M) (v w : TangentSpace I y),
      g₁.inner y v w = g₀.inner y v w +
        ccTensorBilinSymm (I := I) g₀ P y v w) :
    lieCorrectionZeroKappa (I := I) (M := M) g₀ g₁ gB =
      lieCorrectionZeroKappa (I := I) (M := M) g₀ g₁ g₀ +
        lieCorrectionZeroKappa (I := I) (M := M) g₀ g₀ gB +
        lieCorrectionZeroPbLow (I := I) (M := M) g₀ P g₀ gB := by
  apply smoothCcTensor_ext_of_unitModel (I := I) (M := M) g₀
  intro x
  apply ContinuousMultilinearMap.ext
  intro m
  let v : Fin 3 → TangentSpace I x := fun i =>
    (tangentSpaceModelContinuousLinearEquiv (I := I) x).symm (m i)
  rw [unit_add0 (I := I) (M := M) g₀ 3 _ _ x m,
    unit_add0 (I := I) (M := M) g₀ 3 _ _ x m]
  rw [kappa_unit (I := I) (M := M) g₀ g₁ gB x m,
    kappa_unit (I := I) (M := M) g₀ g₁ g₀ x m,
    kappa_unit (I := I) (M := M) g₀ g₀ gB x m,
    pbLow_unit (I := I) (M := M) g₀ P g₀ gB x m]
  rw [htie x (PDE.DeTurck.connectionDifference (I := I) g₁ gB x (v 0) (v 1)) (v 2)]
  rw [PDE.DeTurck.connectionDifference_cocycle (I := I) g₀ g₁ gB x (v 0) (v 1)]
  rw [htie x (PDE.DeTurck.connectionDifference (I := I) g₁ g₀ x (v 0) (v 1)) (v 2)]
  rw [map_add (g₀.inner x), map_add (ccTensorBilinSymm (I := I) g₀ P x)]
  rw [add_apply, add_apply]
  ring

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [SigmaCompactSpace M] in
theorem kappa_base_neg (g₀ gB : SmoothRiemannianMetric I M) :
    lieCorrectionZeroKappa (I := I) (M := M) g₀ g₀ gB =
      -metricLoweredConnectionDifferenceCoefficient (I := I) g₀ gB := by
  apply smoothCcTensor_ext_of_unitModel (I := I) (M := M) g₀
  intro x
  apply ContinuousMultilinearMap.ext
  intro m
  let v : Fin 3 → TangentSpace I x := fun i =>
    (tangentSpaceModelContinuousLinearEquiv (I := I) x).symm (m i)
  rw [kappa_unit (I := I) (M := M) g₀ g₀ gB x m]
  rw [show unitModel (I := I) (M := M) g₀ 3
      (-metricLoweredConnectionDifferenceCoefficient (I := I) g₀ gB) x =
      -unitModel (I := I) (M := M) g₀ 3
        (metricLoweredConnectionDifferenceCoefficient (I := I) g₀ gB) x by
    simp only [unitModel]
    rw [SmoothCcTensor.toSection_neg, ContMDiffSection.coe_neg, Pi.neg_apply,
      neg_apply, Tensor0SSpace.toModel_neg]]
  have hm : (fun i => tangentSpaceModelContinuousLinearEquiv (I := I) x (v i)) = m := by
    funext i
    exact ContinuousLinearEquiv.apply_symm_apply _ _
  rw [← hm]
  change g₀.inner x (PDE.DeTurck.connectionDifference (I := I) g₀ gB x
      (v 0) (v 1)) (v 2) =
    -(unitModel (I := I) (M := M) g₀ 3
      (metricLoweredConnectionDifferenceCoefficient (I := I) g₀ gB) x
      (fun i => tangentSpaceModelContinuousLinearEquiv (I := I) x (v i)))
  rw [connectionDifferenceLoweredCc_unitModel_apply']
  have hcycle := PDE.DeTurck.connectionDifference_cocycle
    (I := I) gB g₀ g₀ x (v 0) (v 1)
  rw [PDE.DeTurck.connectionDifference_self] at hcycle
  have hneg :
      PDE.DeTurck.connectionDifference (I := I) g₀ gB x (v 0) (v 1) =
        -PDE.DeTurck.connectionDifference (I := I) gB g₀ x (v 0) (v 1) :=
    eq_neg_of_add_eq_zero_left hcycle.symm
  rw [hneg, map_neg, neg_apply]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private theorem ip_toModel (s : ℕ) (x : M) (v : TangentSpace I x)
    (D : Tensor0SSpace (s + 1) I x) (w : Fin s → E) :
    Tensor0SSpace.toModel
        (Tensor0SBundle.interiorProduct (𝕜 := ℝ) (I := I) s x v D) w =
      Tensor0SSpace.toModel D
        (Fin.cons (tangentSpaceModelContinuousLinearEquiv (I := I) x v) w) := by
  have h1 : Tensor0SSpace.toModel
      (Tensor0SBundle.interiorProduct (𝕜 := ℝ) (I := I) s x v D) =
      Tensor0SBundle.modelInteriorProduct (𝕜 := ℝ) (E := E) s
        (tangentSpaceModelContinuousLinearEquiv (I := I) x v)
        (Tensor0SSpace.toModel D) := rfl
  rw [h1]
  rfl

omit [NeZero (Module.finrank ℝ E)] in
omit [I.Boundaryless] in
omit [SigmaCompactSpace M] in
theorem pbLow_raise (g₀ gB : SmoothRiemannianMetric I M)
    (P : SmoothCcTensor g₀ 0 2) :
    cometricRaiseSlot0Field (I := I) (M := M) g₀ 1
        (domDomCongrSection (I := I) g₀ (finRotate 3)
          (lieCorrectionZeroPbLow (I := I) (M := M) g₀ P g₀ gB)) =
      ccOperatorFieldComp (I := I) (M := M) g₀ 1 1 2
        (lieFirstOrderFixCd (I := I) (M := M) g₀ gB)
        (cometricRaiseSlot0Field (I := I) (M := M) g₀ 0
          (ccTensor02Symm (I := I) (M := M) g₀ P)) := by
  apply Integral.L2.SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rw [cometricRaiseSlot0Field_toSection, operatorFieldComposition_toSection]
  apply tensorRSSpace_ext 1 2 x
  intro om
  apply ContinuousMultilinearMap.ext
  intro YZ
  set u : TangentSpace I x := inverseMetricSharpFib (I := I) g₀ x om with hu
  set D : Tensor0SSpace 3 I x :=
    (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 3 I x from
      (domDomCongrSection (I := I) g₀ (finRotate 3)
        (lieCorrectionZeroPbLow (I := I) (M := M) g₀ P g₀ gB)).toSection x)
      (unitTensor (I := I) (M := M) x) with hDdef
  have hLHS : (show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 2 I x from
        cometricRaiseSlot0Fib (I := I) g₀ 1 x D) om YZ =
      Tensor0SSpace.toModel D
        (Fin.cons (tangentSpaceModelContinuousLinearEquiv (I := I) x u)
          (fun k => tangentSpaceModelContinuousLinearEquiv (I := I) x (YZ k))) := by
    rw [cometricRaiseSlot0Fib_clm_apply (I := I) g₀ 1 x D om]
    rw [show (Tensor0SBundle.interiorProduct (𝕜 := ℝ) (I := I) (1 + 1) x
          (inverseMetricSharpFib (I := I) g₀ x om) D YZ : ℝ) =
        Tensor0SSpace.toModel
          (Tensor0SBundle.interiorProduct (𝕜 := ℝ) (I := I) (1 + 1) x
            (inverseMetricSharpFib (I := I) g₀ x om) D)
          (fun k => tangentSpaceModelContinuousLinearEquiv (I := I) x (YZ k)) from rfl]
    rw [ip_toModel (I := I) (M := M) (1 + 1) x
      (inverseMetricSharpFib (I := I) g₀ x om) D
      (fun k => tangentSpaceModelContinuousLinearEquiv (I := I) x (YZ k)), ← hu]
  have hLHSval : Tensor0SSpace.toModel D
      (Fin.cons (tangentSpaceModelContinuousLinearEquiv (I := I) x u)
        (fun k => tangentSpaceModelContinuousLinearEquiv (I := I) x (YZ k))) =
      ccTensorBilinSymm (I := I) g₀ P x
        (PDE.DeTurck.connectionDifference (I := I) g₀ gB x (YZ 0) (YZ 1)) u := by
    have hum : unitModel (I := I) (M := M) g₀ 3
        (domDomCongrSection (I := I) g₀ (finRotate 3)
          (lieCorrectionZeroPbLow (I := I) (M := M) g₀ P g₀ gB)) x =
        Tensor0SSpace.toModel D := rfl
    rw [show Tensor0SSpace.toModel D
          (Fin.cons (tangentSpaceModelContinuousLinearEquiv (I := I) x u)
            (fun k => tangentSpaceModelContinuousLinearEquiv (I := I) x (YZ k))) =
        unitModel (I := I) (M := M) g₀ 3
          (domDomCongrSection (I := I) g₀ (finRotate 3)
            (lieCorrectionZeroPbLow (I := I) (M := M) g₀ P g₀ gB)) x
          ![tangentSpaceModelContinuousLinearEquiv (I := I) x u,
            tangentSpaceModelContinuousLinearEquiv (I := I) x (YZ 0),
            tangentSpaceModelContinuousLinearEquiv (I := I) x (YZ 1)] from by
      rw [hum]
      congr 1
      funext k
      fin_cases k <;> rfl]
    rw [domDomCongrSection_unitModel, ContinuousMultilinearMap.domDomCongr_apply]
    rw [show (fun i =>
          ![tangentSpaceModelContinuousLinearEquiv (I := I) x u,
            tangentSpaceModelContinuousLinearEquiv (I := I) x (YZ 0),
            tangentSpaceModelContinuousLinearEquiv (I := I) x (YZ 1)]
              ((finRotate 3) i)) =
        ![tangentSpaceModelContinuousLinearEquiv (I := I) x (YZ 0),
          tangentSpaceModelContinuousLinearEquiv (I := I) x (YZ 1),
          tangentSpaceModelContinuousLinearEquiv (I := I) x u] from by
      funext i
      fin_cases i <;> simp [finRotate_apply]]
    rw [pbLow_unit (I := I) (M := M) g₀ P g₀ gB x]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons, ContinuousLinearEquiv.symm_apply_apply]
  have hRHS : ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 2 I x from
        (lieFirstOrderFixCd (I := I) (M := M) g₀ gB).toSection x).comp
        (show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 1 I x from
          (cometricRaiseSlot0Field (I := I) (M := M) g₀ 0
            (ccTensor02Symm (I := I) (M := M) g₀ P)).toSection x)) om YZ =
      ccTensorBilinSymm (I := I) g₀ P x
        (PDE.DeTurck.connectionDifference (I := I) g₀ gB x (YZ 0) (YZ 1)) u := by
    rw [ContinuousLinearMap.comp_apply]
    set om' : Tensor0SSpace 1 I x :=
      (show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 1 I x from
        (cometricRaiseSlot0Field (I := I) (M := M) g₀ 0
          (ccTensor02Symm (I := I) (M := M) g₀ P)).toSection x) om with hom'
    rw [show (lieFirstOrderFixCd (I := I) (M := M) g₀ gB).toSection x =
      connectionDifferenceFib (I := I) g₀ gB x from rfl]
    rw [connectionDifferenceFib_apply_eval (I := I) g₀ gB x om' YZ]
    rw [show om' (fun _ : Fin 1 =>
        PDE.DeTurck.connectionDifference (I := I) g₀ gB x (YZ 0) (YZ 1)) =
        Tensor0SSpace.toModel om' (fun _ : Fin 1 =>
          tangentSpaceModelContinuousLinearEquiv (I := I) x
            (PDE.DeTurck.connectionDifference (I := I) g₀ gB x (YZ 0) (YZ 1))) from rfl]
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
        (Tensor0SBundle.interiorProduct (𝕜 := ℝ) (I := I) (0 + 1) x
          (inverseMetricSharpFib (I := I) g₀ x om)
          ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from
            (ccTensor02Symm (I := I) (M := M) g₀ P).toSection x)
            (unitTensor (I := I) (M := M) x)))
        (fun _ : Fin 1 => tangentSpaceModelContinuousLinearEquiv (I := I) x
          (PDE.DeTurck.connectionDifference (I := I) g₀ gB x (YZ 0) (YZ 1))) =
        Tensor0SSpace.toModel
          ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from
            (ccTensor02Symm (I := I) (M := M) g₀ P).toSection x)
            (unitTensor (I := I) (M := M) x))
          (Fin.cons (tangentSpaceModelContinuousLinearEquiv (I := I) x u)
            (fun _ : Fin 1 => tangentSpaceModelContinuousLinearEquiv (I := I) x
              (PDE.DeTurck.connectionDifference (I := I) g₀ gB x (YZ 0) (YZ 1)))) from by
      rw [ip_toModel (I := I) (M := M) (0 + 1) x
        (inverseMetricSharpFib (I := I) g₀ x om) _
        (fun _ : Fin 1 => tangentSpaceModelContinuousLinearEquiv (I := I) x
          (PDE.DeTurck.connectionDifference (I := I) g₀ gB x (YZ 0) (YZ 1))), ← hu]]
    rw [show Tensor0SSpace.toModel
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from
          (ccTensor02Symm (I := I) (M := M) g₀ P).toSection x)
          (unitTensor (I := I) (M := M) x))
        (Fin.cons (tangentSpaceModelContinuousLinearEquiv (I := I) x u)
          (fun _ : Fin 1 => tangentSpaceModelContinuousLinearEquiv (I := I) x
            (PDE.DeTurck.connectionDifference (I := I) g₀ gB x (YZ 0) (YZ 1)))) =
        unitModel (I := I) (M := M) g₀ 2
          (ccTensor02Symm (I := I) (M := M) g₀ P) x
          ![tangentSpaceModelContinuousLinearEquiv (I := I) x u,
            tangentSpaceModelContinuousLinearEquiv (I := I) x
              (PDE.DeTurck.connectionDifference (I := I) g₀ gB x (YZ 0) (YZ 1))] from by
      rw [unitModel]
      congr 1
      funext k
      fin_cases k <;> rfl]
    have hunit := unitModel_eq_ccTensorBilin_local (I := I) (M := M) g₀
      (ccTensor02Symm (I := I) (M := M) g₀ P) x u
      (PDE.DeTurck.connectionDifference (I := I) g₀ gB x (YZ 0) (YZ 1))
    change unitModel (I := I) (M := M) g₀ 2
        (ccTensor02Symm (I := I) (M := M) g₀ P) x
        ![tangentSpaceModelContinuousLinearEquiv (I := I) x u,
          tangentSpaceModelContinuousLinearEquiv (I := I) x
            (PDE.DeTurck.connectionDifference (I := I) g₀ gB x (YZ 0) (YZ 1))] =
      smoothCcTensorBilinForm (I := I) g₀
        (ccTensor02Symm (I := I) (M := M) g₀ P) x u
        (PDE.DeTurck.connectionDifference (I := I) g₀ gB x (YZ 0) (YZ 1)) at hunit
    rw [hunit]
    rw [smoothCcTensorBilinForm_ccTensor02Symm (I := I) (M := M) g₀ P x u
      (PDE.DeTurck.connectionDifference (I := I) g₀ gB x (YZ 0) (YZ 1))]
    exact ccTensorBilinSymm_symm (I := I) g₀ P x u
      (PDE.DeTurck.connectionDifference (I := I) g₀ gB x (YZ 0) (YZ 1))
  exact hLHS.trans (hLHSval.trans hRHS.symm)

omit [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem pbLow_riemannianFiberNormSq (g₀ gB : SmoothRiemannianMetric I M)
    (P : SmoothCcTensor g₀ 0 2) (n : ℕ) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + n) x
        ((iteratedCovGrad (I := I) g₀ 0 3 n
          (lieCorrectionZeroPbLow (I := I) (M := M) g₀ P g₀ gB)).toSection x) =
      riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + n) x
        ((iteratedCovGrad (I := I) g₀ 1 2 n
          (ccOperatorFieldComp (I := I) (M := M) g₀ 1 1 2
            (lieFirstOrderFixCd (I := I) (M := M) g₀ gB)
            (cometricRaiseSlot0Field (I := I) (M := M) g₀ 0
              (ccTensor02Symm (I := I) (M := M) g₀ P)))).toSection x) := by
  calc
    riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + n) x
        ((iteratedCovGrad (I := I) g₀ 0 3 n
          (lieCorrectionZeroPbLow (I := I) (M := M) g₀ P g₀ gB)).toSection x)
        = riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + n) x
            ((iteratedCovGrad (I := I) g₀ 0 3 n
              (domDomCongrSection (I := I) g₀ (finRotate 3)
                (lieCorrectionZeroPbLow (I := I) (M := M) g₀ P g₀ gB))).toSection x) :=
          (riemannianFiberNormSq_iteratedCovGrad_domDomCongrSection
            (I := I) (M := M) g₀ (finRotate 3)
            (lieCorrectionZeroPbLow (I := I) (M := M) g₀ P g₀ gB) n x).symm
    _ = riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + n) x
          ((iteratedCovGrad (I := I) g₀ 1 2 n
            (cometricRaiseSlot0Field (I := I) (M := M) g₀ 1
              (domDomCongrSection (I := I) g₀ (finRotate 3)
                (lieCorrectionZeroPbLow (I := I) (M := M) g₀ P g₀ gB)))).toSection x) :=
        (riemannianFiberNormSq_iteratedCovGrad_cometricRaiseSlot0Field_eq
          (I := I) (M := M) g₀ 1
          (domDomCongrSection (I := I) g₀ (finRotate 3)
            (lieCorrectionZeroPbLow (I := I) (M := M) g₀ P g₀ gB)) n x).symm
    _ = riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + n) x
          ((iteratedCovGrad (I := I) g₀ 1 2 n
            (ccOperatorFieldComp (I := I) (M := M) g₀ 1 1 2
              (lieFirstOrderFixCd (I := I) (M := M) g₀ gB)
              (cometricRaiseSlot0Field (I := I) (M := M) g₀ 0
                (ccTensor02Symm (I := I) (M := M) g₀ P)))).toSection x) := by
        rw [pbLow_raise (I := I) (M := M) g₀ gB P]

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral
