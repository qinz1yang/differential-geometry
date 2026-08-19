import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegularity.SecondOrderCoefficientLipschitzBounds

noncomputable section

set_option backward.isDefEq.respectTransparency false

open Bundle Manifold MeasureTheory Set Filter DifferentialGeometry.Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Analysis.Sobolev
  (iteratedCovGrad iteratedCovGrad_succ iteratedCovGrad_zero metricConnectionDifferenceLoweredCoefficient
   rsDomDomCongrSection rsDomDomCongrSection_toSection)
open DifferentialGeometry.Analysis.Sobolev.TensorHilbert
open DifferentialGeometry.Analysis.Spectral
  (operatorFieldApply operatorFieldApplication_add_left operatorFieldApplication_add_right operatorFieldApplication_assoc operatorFieldApplication_smul_left operatorFieldApplication_smul_right operatorFieldApplication_sub_left operatorFieldApplication_toSection ccOperatorFieldComp
   operatorFieldComposition_toSection operatorFieldComposition_zero_eq_operatorFieldApply ccInputSlotSymm ccInputSlotSymm ccOperatorFieldComp
   ccSlotSwapField ccSlotSwapField_toSection deTurckLieTopOrderPairingFamily lieCorrectionZeroMixedConnection lieCorrectionZeroKappa lieCorrectionZeroRiemann lieCorrectionZeroVectorBundle
   lieCorrectionZeroField operatorFieldApply permCoeff ricciConnectionDifferenceQuadraticArm ricciConnectionDifferenceQuadraticKernel rsDomDomCongr slotExtend slotSwapFib slotSwapFib_apply
   slotExtendFib_apply slotExtend_toSection slotExtendIter symmS_eq_self_of_ccTensorBilin_symm
   tail_base_split toModel_rsDomDomCongr_apply)
open DifferentialGeometry.Geometry.Connection (slotInsertEndoCc slotInsertEndoCc_toSection)
open DifferentialGeometry.Geometry.Curvature (slotInsertEndoFib_apply_eval)
open DifferentialGeometry.PDE.DeTurck.RicciLinearization
open DifferentialGeometry.Analysis.Spectral.DeTurck
open DifferentialGeometry.Analysis.Spectral.MetricRealization

namespace LieCorrectionZeroCore

private abbrev lieCorrectionZeroMixedConnectionPermutationCycleZeroTwoOne :=
  DifferentialGeometry.Analysis.Spectral.LieCorrectionZeroCore.lieCorrectionZeroMixedConnectionPermutationCycleZeroTwoOne

private abbrev lieCorrectionZeroMixedConnectionPermutationCycleZeroTwoThreeOne :=
  DifferentialGeometry.Analysis.Spectral.LieCorrectionZeroCore.lieCorrectionZeroMixedConnectionPermutationCycleZeroTwoThreeOne

private abbrev lieCorrectionZeroMixedConnectionPermutationCycleZeroOneFour :=
  DifferentialGeometry.Analysis.Spectral.LieCorrectionZeroCore.lieCorrectionZeroMixedConnectionPermutationCycleZeroOneFour

end LieCorrectionZeroCore

variable
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
      [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

namespace RicciDeTurckPairing

omit [BoundarylessManifold I M] in
theorem ricciCovariantDerivativeConnectionDifference_self
    (g gm : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2) :
    operatorFieldApply (I := I) (M := M) g 2 2
        (RicciDeTurckLowOrder.ricciCovariantDerivativeConnectionDifferenceLowOrder (I := I) (M := M) g gm T) T =
      operatorFieldApply (I := I) (M := M) g 3 2
        (RicciDeTurckLowOrder.ricciConnectionDerivativeTransposedCoefficient (I := I) (M := M) g gm T)
        (iteratedCovGrad (I := I) g 0 2 1 T) := by
  rw [iteratedCovGrad_succ, iteratedCovGrad_zero]
  exact RicciDeTurckLowOrder.ricciCovariantDerivativeConnectionDifferenceLowOrder_apply (I := I) (M := M) g gm T T

omit [BoundarylessManifold I M] [SigmaCompactSpace M] in
theorem operatorFieldApplication_ipLowCc_eq_cometricRaiseSlot0Field
    (g : SmoothRiemannianMetric I M) (om : SmoothCcTensor g 0 1)
    (W : SmoothCcTensor g 0 2) :
    operatorFieldApply (I := I) (M := M) g 2 1
        (ipLowCc (I := I) (M := M) g om) W =
      operatorFieldApply (I := I) (M := M) g 1 1
        (cometricRaiseSlot0Field (I := I) (M := M) g 0 W) om := by
  apply smoothCcTensor_ext_of_unitModel (I := I) (M := M) g
  intro x
  let alpha : Tensor0SSpace 1 I x :=
    (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 1 I x from om.toSection x)
      (unitTensor (I := I) (M := M) x)
  have hflat : ∀ z : TangentSpace I x,
      unitModel (I := I) (M := M) g 1 om x (fun _ : Fin 1 => z) =
        g.inner x (inverseMetricSharpFib (I := I) g x alpha) z := by
    intro z
    rw [inverseMetricSharpFib_inner]
    change Tensor0SSpace.toModel alpha (fun _ : Fin 1 => (z : E)) =
      cotangentToDualLinear (I := I) (x := x) alpha z
    rw [show cotangentToDualLinear (I := I) (x := x) alpha z =
      cotangentToDual (I := I) (x := x) alpha z from rfl]
    rw [cotangentToDual_apply]
    rfl
  apply ContinuousMultilinearMap.ext
  intro m
  rw [unitModel, unitModel, operatorFieldApplication_toSection, operatorFieldApplication_toSection,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply]
  rw [ipLowCc_toSec_ip (I := I) (M := M) g om x
    (inverseMetricSharpFib (I := I) g x alpha) hflat]
  rw [cometricRaiseSlot0Field_toSection,
    cometricRaiseSlot0Fib_clm_apply]

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma unitTensor_toModel_apply (x : M) (m : Fin 0 → E) :
    Tensor0SSpace.toModel (unitTensor (I := I) (M := M) x) m = 1 := by
  rw [unitTensor, Tensor0SSpace.toModel_ofModel]
  rfl

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless]
    [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
theorem unitModel_add
    (g : SmoothRiemannianMetric I M)
    (A B : SmoothCcTensor g 0 2) (x : M) (v : Fin 2 → E) :
    unitModel (I := I) (M := M) g 2 (A + B) x v =
      unitModel (I := I) (M := M) g 2 A x v +
        unitModel (I := I) (M := M) g 2 B x v := by
  simp only [unitModel]
  rw [SmoothCcTensor.toSection_add, ContMDiffSection.coe_add,
    Pi.add_apply, ContinuousLinearMap.add_apply,
    Tensor0SSpace.toModel_add, ContinuousMultilinearMap.add_apply]

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma tensor0S_curry_zero_eq_smul_unitTensor
    (x : M) (D : Tensor0SSpace 1 I x) (v₀ : E) :
    tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 0 x D v₀ =
      Tensor0SSpace.toModel D (fun _ : Fin 1 => v₀) •
        unitTensor (I := I) (M := M) x := by
  apply Tensor0SSpace.toModel_injective
  apply ContinuousMultilinearMap.ext
  intro m
  beta_reduce
  have h₁ : Tensor0SSpace.toModel
      (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 0 x D v₀) m =
      Tensor0SSpace.toModel D (Fin.cons v₀ m) :=
    TensorMultilinear.tensor0S_curry_apply_eval (I := I) (M := M) (n := 0)
      (T := D) (v0 := v₀) (vs := m)
  rw [h₁, Tensor0SSpace.toModel_smul,
    ContinuousMultilinearMap.smul_apply, unitTensor_toModel_apply (I := I) (M := M) x m,
    smul_eq_mul, mul_one]
  congr 1
  funext k
  refine Fin.cases ?_ (fun j => j.elim0) k
  rfl

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma continuousLinearMap_apply_smul_unitTensor (x : M) (s : ℕ)
    (A : Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x) (c : ℝ) :
    A (c • unitTensor (I := I) (M := M) x) =
      c • A (unitTensor (I := I) (M := M) x) := A.map_smul c _

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] [SigmaCompactSpace M] in
private lemma slotExtendIter_two_zero_three_apply (g : SmoothRiemannianMetric I M)
    (K : SmoothCcTensor g 0 3) (x : M) (D : Tensor0SSpace 2 I x) :
    (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 5 I x from
      (slotExtendIter (I := I) (M := M) g 0 3 2 K).toSection x) D =
    tensor0SProdKappaFib (I := I) (p := 2) (q := 3) x
      ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 3 I x from K.toSection x)
        (unitTensor (I := I) (M := M) x)) D := by
  apply Tensor0SSpace.toModel_injective
  apply ContinuousMultilinearMap.ext
  intro m
  beta_reduce
  set kappa : Tensor0SSpace 3 I x :=
    (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 3 I x from K.toSection x)
      (unitTensor (I := I) (M := M) x) with hkappa
  have hLHS : Tensor0SSpace.toModel
      ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 5 I x from
        (slotExtendIter (I := I) (M := M) g 0 3 2 K).toSection x) D) m =
      Tensor0SSpace.toModel D ![m 0, m 1] *
        Tensor0SSpace.toModel kappa (fun j : Fin 3 => m (Fin.natAdd 2 j)) := by
    rw [show
        ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 5 I x from
          (slotExtendIter (I := I) (M := M) g 0 3 2 K).toSection x) D) =
          slotExtendFib (I := I) (M := M) 1 4 x
            (show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 4 I x from
              (slotExtendIter (I := I) (M := M) g 0 3 1 K).toSection x) D
          from rfl]
    rw [show m = Fin.cons (m 0) (Fin.tail m) from (Fin.cons_self_tail m).symm]
    rw [slotExtendFib_apply_eval (I := I) (M := M) 1 4 x _ D
      (m 0) (Fin.tail m)]
    set D₁ : Tensor0SSpace 1 I x :=
      tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 1 x D (m 0) with hD₁
    rw [show
        ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 4 I x from
          (slotExtendIter (I := I) (M := M) g 0 3 1 K).toSection x) D₁) =
          slotExtendFib (I := I) (M := M) 0 3 x
            (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 3 I x from
              K.toSection x) D₁ from rfl]
    rw [show (Fin.tail m : Fin 4 → E) =
        Fin.cons (m 1) (fun j : Fin 3 => m (Fin.natAdd 2 j)) from by
      funext k
      fin_cases k <;> rfl]
    rw [slotExtendFib_apply_eval (I := I) (M := M) 0 3 x _ D₁
      (m 1) (fun j : Fin 3 => m (Fin.natAdd 2 j))]
    rw [tensor0S_curry_zero_eq_smul_unitTensor (I := I) (M := M) x D₁ (m 1)]
    rw [continuousLinearMap_apply_smul_unitTensor (I := I) (M := M) x 3 _ _]
    rw [← hkappa, Tensor0SSpace.toModel_smul,
      ContinuousMultilinearMap.smul_apply, smul_eq_mul]
    have hD₁val : Tensor0SSpace.toModel D₁ (fun _ : Fin 1 => m 1) =
        Tensor0SSpace.toModel D ![m 0, m 1] := by
      rw [hD₁, TensorMultilinear.tensor0S_curry_apply_eval
        (I := I) (M := M) (n := 1) (T := D) (v0 := m 0)
        (vs := fun _ : Fin 1 => m 1)]
      congr 1
      funext k
      fin_cases k <;> rfl
    rw [hD₁val]
    first
      | rfl
      | (congr 1; first | rfl | (congr 1; funext k; fin_cases k <;> rfl))
  rw [hLHS, tensor0SProdKappaFib_apply (I := I) x kappa D,
    Tensor0SSpace.toModel_ofModel,
    Bundle.continuousMultilinearMap.modelProduct_apply]
  congr 1
  all_goals
    first
      | rfl
      | (congr 1; funext k; fin_cases k <;> rfl)

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] [SigmaCompactSpace M] in
lemma slotExtendIter_two_zero_four_apply (g : SmoothRiemannianMetric I M)
    (K : SmoothCcTensor g 0 4) (x : M) (D : Tensor0SSpace 2 I x) :
    (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 6 I x from
      (slotExtendIter (I := I) (M := M) g 0 4 2 K).toSection x) D =
    tensor0SProdKappaFib (I := I) (p := 2) (q := 4) x
      ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 4 I x from K.toSection x)
        (unitTensor (I := I) (M := M) x)) D := by
  apply Tensor0SSpace.toModel_injective
  apply ContinuousMultilinearMap.ext
  intro m
  beta_reduce
  set kappa : Tensor0SSpace 4 I x :=
    (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 4 I x from K.toSection x)
      (unitTensor (I := I) (M := M) x) with hkappa
  have hLHS : Tensor0SSpace.toModel
      ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 6 I x from
        (slotExtendIter (I := I) (M := M) g 0 4 2 K).toSection x) D) m =
      Tensor0SSpace.toModel D ![m 0, m 1] *
        Tensor0SSpace.toModel kappa (fun j : Fin 4 => m (Fin.natAdd 2 j)) := by
    rw [show
        ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 6 I x from
          (slotExtendIter (I := I) (M := M) g 0 4 2 K).toSection x) D) =
          slotExtendFib (I := I) (M := M) 1 5 x
            (show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 5 I x from
              (slotExtendIter (I := I) (M := M) g 0 4 1 K).toSection x) D
          from rfl]
    rw [show m = Fin.cons (m 0) (Fin.tail m) from (Fin.cons_self_tail m).symm]
    rw [slotExtendFib_apply_eval (I := I) (M := M) 1 5 x _ D
      (m 0) (Fin.tail m)]
    set D₁ : Tensor0SSpace 1 I x :=
      tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 1 x D (m 0) with hD₁
    rw [show
        ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 5 I x from
          (slotExtendIter (I := I) (M := M) g 0 4 1 K).toSection x) D₁) =
          slotExtendFib (I := I) (M := M) 0 4 x
            (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 4 I x from
              K.toSection x) D₁ from rfl]
    rw [show (Fin.tail m : Fin 5 → E) =
        Fin.cons (m 1) (fun j : Fin 4 => m (Fin.natAdd 2 j)) from by
      funext k
      fin_cases k <;> rfl]
    rw [slotExtendFib_apply_eval (I := I) (M := M) 0 4 x _ D₁
      (m 1) (fun j : Fin 4 => m (Fin.natAdd 2 j))]
    rw [tensor0S_curry_zero_eq_smul_unitTensor (I := I) (M := M) x D₁ (m 1)]
    rw [continuousLinearMap_apply_smul_unitTensor (I := I) (M := M) x 4 _ _]
    rw [← hkappa, Tensor0SSpace.toModel_smul,
      ContinuousMultilinearMap.smul_apply, smul_eq_mul]
    have hD₁val : Tensor0SSpace.toModel D₁ (fun _ : Fin 1 => m 1) =
        Tensor0SSpace.toModel D ![m 0, m 1] := by
      rw [hD₁, TensorMultilinear.tensor0S_curry_apply_eval
        (I := I) (M := M) (n := 1) (T := D) (v0 := m 0)
        (vs := fun _ : Fin 1 => m 1)]
      congr 1
      funext k
      fin_cases k <;> rfl
    rw [hD₁val]
    first
      | rfl
      | (congr 1; first | rfl | (congr 1; funext k; fin_cases k <;> rfl))
  rw [hLHS, tensor0SProdKappaFib_apply (I := I) x kappa D,
    Tensor0SSpace.toModel_ofModel,
    Bundle.continuousMultilinearMap.modelProduct_apply]
  congr 1
  all_goals
    first
      | rfl
      | (congr 1; funext k; fin_cases k <;> rfl)

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] [SigmaCompactSpace M] in
private lemma slotExtendIter_two_zero_two_apply (g : SmoothRiemannianMetric I M)
    (K : SmoothCcTensor g 0 2) (x : M) (D : Tensor0SSpace 2 I x) :
    (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 4 I x from
      (slotExtendIter (I := I) (M := M) g 0 2 2 K).toSection x) D =
    tensor0SProdKappaFib (I := I) (p := 2) (q := 2) x
      ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from K.toSection x)
        (unitTensor (I := I) (M := M) x)) D := by
  apply Tensor0SSpace.toModel_injective
  apply ContinuousMultilinearMap.ext
  intro m
  beta_reduce
  set kappa : Tensor0SSpace 2 I x :=
    (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from K.toSection x)
      (unitTensor (I := I) (M := M) x) with hkappa
  have hLHS : Tensor0SSpace.toModel
      ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 4 I x from
        (slotExtendIter (I := I) (M := M) g 0 2 2 K).toSection x) D) m =
      Tensor0SSpace.toModel D ![m 0, m 1] *
        Tensor0SSpace.toModel kappa (fun j : Fin 2 => m (Fin.natAdd 2 j)) := by
    rw [show
        ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 4 I x from
          (slotExtendIter (I := I) (M := M) g 0 2 2 K).toSection x) D) =
          slotExtendFib (I := I) (M := M) 1 3 x
            (show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 3 I x from
              (slotExtendIter (I := I) (M := M) g 0 2 1 K).toSection x) D
          from rfl]
    rw [show m = Fin.cons (m 0) (Fin.tail m) from (Fin.cons_self_tail m).symm]
    rw [slotExtendFib_apply_eval (I := I) (M := M) 1 3 x _ D
      (m 0) (Fin.tail m)]
    set D₁ : Tensor0SSpace 1 I x :=
      tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 1 x D (m 0) with hD₁
    rw [show
        ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 3 I x from
          (slotExtendIter (I := I) (M := M) g 0 2 1 K).toSection x) D₁) =
          slotExtendFib (I := I) (M := M) 0 2 x
            (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from
              K.toSection x) D₁ from rfl]
    rw [show (Fin.tail m : Fin 3 → E) =
        Fin.cons (m 1) (fun j : Fin 2 => m (Fin.natAdd 2 j)) from by
      funext k
      fin_cases k <;> rfl]
    rw [slotExtendFib_apply_eval (I := I) (M := M) 0 2 x _ D₁
      (m 1) (fun j : Fin 2 => m (Fin.natAdd 2 j))]
    rw [tensor0S_curry_zero_eq_smul_unitTensor (I := I) (M := M) x D₁ (m 1)]
    rw [continuousLinearMap_apply_smul_unitTensor (I := I) (M := M) x 2 _ _]
    rw [← hkappa, Tensor0SSpace.toModel_smul,
      ContinuousMultilinearMap.smul_apply, smul_eq_mul]
    have hD₁val : Tensor0SSpace.toModel D₁ (fun _ : Fin 1 => m 1) =
        Tensor0SSpace.toModel D ![m 0, m 1] := by
      rw [hD₁, TensorMultilinear.tensor0S_curry_apply_eval
        (I := I) (M := M) (n := 1) (T := D) (v0 := m 0)
        (vs := fun _ : Fin 1 => m 1)]
      congr 1
      funext k
      fin_cases k <;> rfl
    rw [hD₁val]
    first
      | rfl
      | (congr 1; first | rfl | (congr 1; funext k; fin_cases k <;> rfl))
  rw [hLHS, tensor0SProdKappaFib_apply (I := I) x kappa D,
    Tensor0SSpace.toModel_ofModel,
    Bundle.continuousMultilinearMap.modelProduct_apply]
  congr 1
  all_goals
    first
      | rfl
      | (congr 1; funext k; fin_cases k <;> rfl)

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] [SigmaCompactSpace M] in
private lemma slotExtendIter_three_zero_two_apply (g : SmoothRiemannianMetric I M)
    (K : SmoothCcTensor g 0 2) (x : M) (D : Tensor0SSpace 3 I x) :
    (show Tensor0SSpace 3 I x →L[ℝ] Tensor0SSpace 5 I x from
      (slotExtendIter (I := I) (M := M) g 0 2 3 K).toSection x) D =
    tensor0SProdKappaFib (I := I) (p := 3) (q := 2) x
      ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from K.toSection x)
        (unitTensor (I := I) (M := M) x)) D := by
  apply Tensor0SSpace.toModel_injective
  apply ContinuousMultilinearMap.ext
  intro m
  beta_reduce
  set kappa : Tensor0SSpace 2 I x :=
    (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from K.toSection x)
      (unitTensor (I := I) (M := M) x) with hkappa
  have hLHS : Tensor0SSpace.toModel
      ((show Tensor0SSpace 3 I x →L[ℝ] Tensor0SSpace 5 I x from
        (slotExtendIter (I := I) (M := M) g 0 2 3 K).toSection x) D) m =
      Tensor0SSpace.toModel D ![m 0, m 1, m 2] *
        Tensor0SSpace.toModel kappa (fun j : Fin 2 => m (Fin.natAdd 3 j)) := by
    rw [show
        ((show Tensor0SSpace 3 I x →L[ℝ] Tensor0SSpace 5 I x from
          (slotExtendIter (I := I) (M := M) g 0 2 3 K).toSection x) D) =
          slotExtendFib (I := I) (M := M) 2 4 x
            (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 4 I x from
              (slotExtendIter (I := I) (M := M) g 0 2 2 K).toSection x) D
          from rfl]
    rw [show m = Fin.cons (m 0) (Fin.tail m) from (Fin.cons_self_tail m).symm]
    rw [slotExtendFib_apply_eval (I := I) (M := M) 2 4 x _ D
      (m 0) (Fin.tail m)]
    set D₂ : Tensor0SSpace 2 I x :=
      tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 2 x D (m 0) with hD₂
    rw [slotExtendIter_two_zero_two_apply (I := I) (M := M) g K x D₂, ← hkappa,
      tensor0SProdKappaFib_apply (I := I) x kappa D₂,
      Tensor0SSpace.toModel_ofModel,
      Bundle.continuousMultilinearMap.modelProduct_apply]
    have hD₂val : Tensor0SSpace.toModel D₂
        ((Fin.tail m : Fin 4 → E) ∘ Fin.castAdd 2) =
        Tensor0SSpace.toModel D ![m 0, m 1, m 2] := by
      rw [hD₂, TensorMultilinear.tensor0S_curry_apply_eval
        (I := I) (M := M) (n := 2) (T := D) (v0 := m 0)
        (vs := (Fin.tail m : Fin 4 → E) ∘ Fin.castAdd 2)]
      congr 1
      funext k
      fin_cases k <;> rfl
    rw [hD₂val]
    first
      | rfl
      | (congr 2; funext j; fin_cases j <;> rfl)
  rw [hLHS, tensor0SProdKappaFib_apply (I := I) x kappa D,
    Tensor0SSpace.toModel_ofModel,
    Bundle.continuousMultilinearMap.modelProduct_apply]
  congr 1
  all_goals
    first
      | rfl
      | (congr 1; funext k; fin_cases k <;> rfl)

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] [SigmaCompactSpace M] in
lemma slotExtendIter_three_zero_three_apply (g : SmoothRiemannianMetric I M)
    (K : SmoothCcTensor g 0 3) (x : M) (D : Tensor0SSpace 3 I x) :
    (show Tensor0SSpace 3 I x →L[ℝ] Tensor0SSpace 6 I x from
      (slotExtendIter (I := I) (M := M) g 0 3 3 K).toSection x) D =
    tensor0SProdKappaFib (I := I) (p := 3) (q := 3) x
      ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 3 I x from K.toSection x)
        (unitTensor (I := I) (M := M) x)) D := by
  apply Tensor0SSpace.toModel_injective
  apply ContinuousMultilinearMap.ext
  intro m
  beta_reduce
  set kappa : Tensor0SSpace 3 I x :=
    (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 3 I x from K.toSection x)
      (unitTensor (I := I) (M := M) x) with hkappa
  have hLHS : Tensor0SSpace.toModel
      ((show Tensor0SSpace 3 I x →L[ℝ] Tensor0SSpace 6 I x from
        (slotExtendIter (I := I) (M := M) g 0 3 3 K).toSection x) D) m =
      Tensor0SSpace.toModel D ![m 0, m 1, m 2] *
        Tensor0SSpace.toModel kappa (fun j : Fin 3 => m (Fin.natAdd 3 j)) := by
    rw [show
        ((show Tensor0SSpace 3 I x →L[ℝ] Tensor0SSpace 6 I x from
          (slotExtendIter (I := I) (M := M) g 0 3 3 K).toSection x) D) =
          slotExtendFib (I := I) (M := M) 2 5 x
            (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 5 I x from
              (slotExtendIter (I := I) (M := M) g 0 3 2 K).toSection x) D
          from rfl]
    rw [show m = Fin.cons (m 0) (Fin.tail m) from (Fin.cons_self_tail m).symm]
    rw [slotExtendFib_apply_eval (I := I) (M := M) 2 5 x _ D
      (m 0) (Fin.tail m)]
    set D₂ : Tensor0SSpace 2 I x :=
      tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 2 x D (m 0) with hD₂
    rw [slotExtendIter_two_zero_three_apply (I := I) (M := M) g K x D₂, ← hkappa,
      tensor0SProdKappaFib_apply (I := I) x kappa D₂,
      Tensor0SSpace.toModel_ofModel,
      Bundle.continuousMultilinearMap.modelProduct_apply]
    have hD₂val : Tensor0SSpace.toModel D₂
        ((Fin.tail m : Fin 5 → E) ∘ Fin.castAdd 3) =
        Tensor0SSpace.toModel D ![m 0, m 1, m 2] := by
      rw [hD₂, TensorMultilinear.tensor0S_curry_apply_eval
        (I := I) (M := M) (n := 2) (T := D) (v0 := m 0)
        (vs := (Fin.tail m : Fin 5 → E) ∘ Fin.castAdd 3)]
      congr 1
      funext k
      fin_cases k <;> rfl
    rw [hD₂val]
    first
      | rfl
      | (congr 2; funext j; fin_cases j <;> rfl)
  rw [hLHS, tensor0SProdKappaFib_apply (I := I) x kappa D,
    Tensor0SSpace.toModel_ofModel,
    Bundle.continuousMultilinearMap.modelProduct_apply]
  congr 1
  all_goals
    first
      | rfl
      | (congr 1; funext k; fin_cases k <;> rfl)

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] [SigmaCompactSpace M] in
theorem operatorFieldComposition_permutationCoefficient_apply
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
theorem operatorFieldComposition_permutationCoefficient_apply_eq_rsDomDomCongrSection
    (g : SmoothRiemannianMetric I M) {a d : ℕ}
    (ρ : Equiv.Perm (Fin d)) (S : SmoothCcTensor g a d) :
    ccOperatorFieldComp (I := I) (M := M) g a d d
        (permCoeff (I := I) (M := M) g ρ) S =
      rsDomDomCongrSection (I := I) (M := M) g a d ρ S := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rw [operatorFieldComposition_toSection, rsDomDomCongrSection_toSection]
  apply ContinuousLinearMap.ext
  intro D
  rw [ContinuousLinearMap.comp_apply]
  apply Tensor0SSpace.toModel_injective
  change Tensor0SSpace.toModel
      (slotPermCLM (I := I) ρ x
        ((show Tensor0SSpace a I x →L[ℝ] Tensor0SSpace d I x from
          S.toSection x) D)) =
    Tensor0SSpace.toModel
      ((show Tensor0SSpace a I x →L[ℝ] Tensor0SSpace d I x from
        rsDomDomCongr ρ (S.toSection x)) D)
  rw [toModel_rsDomDomCongr_apply, slotPermCLM_apply,
    Tensor0SSpace.toModel_ofModel]

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] [SigmaCompactSpace M] in
theorem operatorFieldComposition_slotExtend_apply
    (g : SmoothRiemannianMetric I M) (a b c : ℕ)
    (A : SmoothCcTensor g b c) (B : SmoothCcTensor g a b) :
    ccOperatorFieldComp (I := I) (M := M) g (a + 1) (b + 1) (c + 1)
        (slotExtend (I := I) (M := M) g b c A)
        (slotExtend (I := I) (M := M) g a b B) =
      slotExtend (I := I) (M := M) g a c
        (ccOperatorFieldComp (I := I) (M := M) g a b c A B) := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rw [operatorFieldComposition_toSection, slotExtend_toSection, slotExtend_toSection,
    slotExtend_toSection, operatorFieldComposition_toSection]
  apply ContinuousLinearMap.ext
  intro D
  rw [ContinuousLinearMap.comp_apply]
  rw [DifferentialGeometry.Analysis.Spectral.slotExtendFib_apply,
    DifferentialGeometry.Analysis.Spectral.slotExtendFib_apply,
    DifferentialGeometry.Analysis.Spectral.slotExtendFib_apply]
  rw [ContinuousLinearEquiv.apply_symm_apply]
  rw [ContinuousLinearMap.comp_assoc]

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] [SigmaCompactSpace M] in
theorem operatorFieldComposition_slotExtendIter_two_apply
    (g : SmoothRiemannianMetric I M) (a b c : ℕ)
    (A : SmoothCcTensor g b c) (B : SmoothCcTensor g a b) :
    ccOperatorFieldComp (I := I) (M := M) g (a + 2) (b + 2) (c + 2)
        (slotExtendIter (I := I) (M := M) g b c 2 A)
        (slotExtendIter (I := I) (M := M) g a b 2 B) =
      slotExtendIter (I := I) (M := M) g a c 2
        (ccOperatorFieldComp (I := I) (M := M) g a b c A B) := by
  change ccOperatorFieldComp (I := I) (M := M) g ((a + 1) + 1) ((b + 1) + 1) ((c + 1) + 1)
      (slotExtend (I := I) (M := M) g (b + 1) (c + 1)
        (slotExtend (I := I) (M := M) g b c A))
      (slotExtend (I := I) (M := M) g (a + 1) (b + 1)
        (slotExtend (I := I) (M := M) g a b B)) =
    slotExtend (I := I) (M := M) g (a + 1) (c + 1)
      (slotExtend (I := I) (M := M) g a c
        (ccOperatorFieldComp (I := I) (M := M) g a b c A B))
  rw [operatorFieldComposition_slotExtend_apply (I := I) (M := M) g (a + 1) (b + 1) (c + 1)]
  rw [operatorFieldComposition_slotExtend_apply (I := I) (M := M) g a b c]

noncomputable def koszulCovectorCoefficient
    (g : SmoothRiemannianMetric I M) : SmoothCcTensor g 3 3 :=
  (1 / 2 : ℝ) •
    (permCoeff (I := I) (M := M) g (Equiv.swap (0 : Fin 3) 2) +
      permCoeff (I := I) (M := M) g (finRotate 3) -
      permCoeff (I := I) (M := M) g (Equiv.swap (1 : Fin 3) 2))

omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
theorem koszulCovectorCoefficient_apply
    (g : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2)
    (hT : ∀ (x : M) (u v : TangentSpace I x),
      ccTensorBilin (I := I) g T x u v =
        ccTensorBilin (I := I) g T x v u) :
    ccOperatorFieldComp (I := I) (M := M) g 0 3 3
        (koszulCovectorCoefficient (I := I) (M := M) g)
        (covGrad (I := I) (M := M) g 0 2 T) =
      koszulCovecCc (I := I) g T := by
  have hs := symmS_eq_self_of_ccTensorBilin_symm
    (I := I) (M := M) g T hT
  have hp (ρ : Equiv.Perm (Fin 3)) :
      operatorFieldApply (I := I) (M := M) g 3 3
          (permCoeff (I := I) (M := M) g ρ)
          (covGrad (I := I) (M := M) g 0 2 T) =
        domDomCongrSection (I := I) g ρ
          (covGrad (I := I) (M := M) g 0 2 T) := by
    simpa only [operatorFieldComposition_zero_eq_operatorFieldApply] using
      operatorFieldComposition_permutationCoefficient_apply (I := I) (M := M) g ρ
        (covGrad (I := I) (M := M) g 0 2 T)
  rw [operatorFieldComposition_zero_eq_operatorFieldApply, koszulCovectorCoefficient, operatorFieldApplication_smul_left,
    operatorFieldApplication_sub_left, operatorFieldApplication_add_left, hp, hp, hp]
  rw [koszulCovecCc, symmSCovGrad3, hs]

noncomputable def metricConnectionDifferenceLoweringCoefficient
    (g : SmoothRiemannianMetric I M) : SmoothCcTensor g 3 3 :=
  ccOperatorFieldComp (I := I) (M := M) g 3 3 3
    (permCoeff (I := I) (M := M) g (finRotate 3).symm)
    (koszulCovectorCoefficient (I := I) (M := M) g)

omit [NeZero (Module.finrank ℝ E)] in
theorem metricConnectionDifferenceLoweringCoefficient_apply
    (g gm : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2)
    (hT : ∀ (x : M) (u v : TangentSpace I x),
      ccTensorBilin (I := I) g T x u v =
        ccTensorBilin (I := I) g T x v u)
    (htie : ∀ (x : M) (u v : TangentSpace I x),
      gm.inner x u v =
        g.inner x u v + ccTensorBilinSymm (I := I) g T x u v) :
    ccOperatorFieldComp (I := I) (M := M) g 0 3 3
        (metricConnectionDifferenceLoweringCoefficient (I := I) (M := M) g)
        (covGrad (I := I) (M := M) g 0 2 T) =
      lieCorrectionZeroKappa (I := I) (M := M) g gm g := by
  rw [operatorFieldComposition_zero_eq_operatorFieldApply, metricConnectionDifferenceLoweringCoefficient, ← operatorFieldApplication_assoc]
  rw [show operatorFieldApply (I := I) (M := M) g 3 3
      (koszulCovectorCoefficient (I := I) (M := M) g)
      (covGrad (I := I) (M := M) g 0 2 T) =
        koszulCovecCc (I := I) g T by
      simpa only [operatorFieldComposition_zero_eq_operatorFieldApply] using
        koszulCovectorCoefficient_apply (I := I) (M := M) g T hT]
  have hp : operatorFieldApply (I := I) (M := M) g 3 3
      (permCoeff (I := I) (M := M) g (finRotate 3).symm)
      (koszulCovecCc (I := I) g T) =
        domDomCongrSection (I := I) g (finRotate 3).symm
          (koszulCovecCc (I := I) g T) := by
    simpa only [operatorFieldComposition_zero_eq_operatorFieldApply] using
      operatorFieldComposition_permutationCoefficient_apply (I := I) (M := M) g (finRotate 3).symm
        (koszulCovecCc (I := I) g T)
  rw [hp]
  exact (kappa_self (I := I) (M := M) g gm T htie).symm

def tensorThreeTwoBlockPermutation : Equiv.Perm (Fin 5) :=
  ⟨![2, 3, 4, 0, 1], ![3, 4, 0, 1, 2], by decide, by decide⟩

noncomputable def tensorThreeTwoProductCoefficient
    (g : SmoothRiemannianMetric I M) (W : SmoothCcTensor g 0 2) :
    SmoothCcTensor g 3 5 :=
  ccOperatorFieldComp (I := I) (M := M) g 3 5 5
    (permCoeff (I := I) (M := M) g tensorThreeTwoBlockPermutation)
    (slotExtendIter (I := I) (M := M) g 0 2 3 W)

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] [SigmaCompactSpace M] in
theorem tensorThreeTwoProductCoefficient_apply
    (g : SmoothRiemannianMetric I M) (K : SmoothCcTensor g 0 3)
    (W : SmoothCcTensor g 0 2) :
    ccOperatorFieldComp (I := I) (M := M) g 0 3 5
        (tensorThreeTwoProductCoefficient (I := I) (M := M) g W) K =
      ccOperatorFieldComp (I := I) (M := M) g 0 2 5
        (slotExtendIter (I := I) (M := M) g 0 3 2 K) W := by
  have hp (ρ : Equiv.Perm (Fin 5)) (S : SmoothCcTensor g 0 5) :
      ccOperatorFieldComp (I := I) (M := M) g 0 5 5
          (permCoeff (I := I) (M := M) g ρ) S =
        domDomCongrSection (I := I) g ρ S := by
    simpa only [ccOperatorFieldComp] using operatorFieldComposition_permutationCoefficient_apply (I := I) (M := M) g ρ S
  rw [operatorFieldComposition_zero_eq_operatorFieldApply, operatorFieldComposition_zero_eq_operatorFieldApply, tensorThreeTwoProductCoefficient,
    ← operatorFieldApplication_assoc, ← operatorFieldComposition_zero_eq_operatorFieldApply, hp]
  apply smoothCcTensor_ext_of_unitModel (I := I) (M := M) g
  intro x
  rw [domDomCongrSection_unitModel]
  apply ContinuousMultilinearMap.ext
  intro m
  rw [ContinuousMultilinearMap.domDomCongr_apply]
  rw [unitModel, unitModel, operatorFieldApplication_toSection, operatorFieldApplication_toSection,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply]
  rw [slotExtendIter_three_zero_two_apply (I := I) (M := M) g W x
      ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 3 I x from
        K.toSection x) (unitTensor (I := I) (M := M) x)),
    slotExtendIter_two_zero_three_apply (I := I) (M := M) g K x
      ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from
        W.toSection x) (unitTensor (I := I) (M := M) x))]
  rw [tensor0SProdKappaFib_apply, tensor0SProdKappaFib_apply,
    Tensor0SSpace.toModel_ofModel, Tensor0SSpace.toModel_ofModel,
    Bundle.continuousMultilinearMap.modelProduct_apply,
    Bundle.continuousMultilinearMap.modelProduct_apply]
  have hK :
      ((fun i => m (tensorThreeTwoBlockPermutation i)) ∘ Fin.castAdd 2) =
        (fun j : Fin 3 => m (Fin.natAdd 2 j)) := by
    funext j
    fin_cases j <;> rfl
  have hW :
      ((fun i => m (tensorThreeTwoBlockPermutation i)) ∘ Fin.natAdd 3) =
        (![m 0, m 1] : Fin 2 → E) := by
    funext j
    fin_cases j <;> rfl
  have hK₀ :
      (m ∘ Fin.natAdd 2) =
        (fun j : Fin 3 => m (Fin.natAdd 2 j)) := rfl
  have hW₀ :
      (m ∘ Fin.castAdd 3) = (![m 0, m 1] : Fin 2 → E) := by
    funext j
    fin_cases j <;> rfl
  rw [hK, hW, hK₀, hW₀]
  exact mul_comm _ _

noncomputable def lieCorrectionZeroMixedConnectionHalfDerivativeCoefficient
    (g gm gB : SmoothRiemannianMetric I M) (W : SmoothCcTensor g 0 2)
    (σlast : Equiv.Perm (Fin 4)) : SmoothCcTensor g 3 2 :=
  ccOperatorFieldComp (I := I) (M := M) g 3 4 2
    (reindexedPureTrace (I := I) (M := M) g gm 2 σlast)
    (ccOperatorFieldComp (I := I) (M := M) g 3 6 4
      (reindexedPureTrace (I := I) (M := M) g gm 4
        LieCorrectionZeroCore.lieCorrectionZeroMixedConnectionPermutationCycleZeroTwoThreeOne)
      (ccOperatorFieldComp (I := I) (M := M) g 3 3 6
        (slotExtendIter (I := I) (M := M) g 0 3 3
          (metricConnectionDifferenceLoweredCoefficient (I := I) (M := M) g gm gB))
        (ccOperatorFieldComp (I := I) (M := M) g 3 5 3
          (reindexedPureTrace (I := I) (M := M) g gm 3
            LieCorrectionZeroCore.lieCorrectionZeroMixedConnectionPermutationCycleZeroOneFour)
          (ccOperatorFieldComp (I := I) (M := M) g 3 3 5
            (tensorThreeTwoProductCoefficient (I := I) (M := M) g W)
            (metricConnectionDifferenceLoweringCoefficient (I := I) (M := M) g)))))

omit [NeZero (Module.finrank ℝ E)] in
theorem lieCorrectionZeroMixedConnectionHalfDerivativeCoefficient_apply
    (g gm gB : SmoothRiemannianMetric I M) (P W : SmoothCcTensor g 0 2)
    (σlast : Equiv.Perm (Fin 4))
    (hP : ∀ (x : M) (u v : TangentSpace I x),
      ccTensorBilin (I := I) g P x u v =
        ccTensorBilin (I := I) g P x v u)
    (htie : ∀ (x : M) (u v : TangentSpace I x),
      gm.inner x u v =
        g.inner x u v + ccTensorBilinSymm (I := I) g P x u v) :
    operatorFieldApply (I := I) (M := M) g 2 2
        (lieCorrectionZeroMixedConnectionHalfExpansion (I := I) (M := M) g gm gB σlast) W =
      operatorFieldApply (I := I) (M := M) g 3 2
        (lieCorrectionZeroMixedConnectionHalfDerivativeCoefficient (I := I) (M := M) g gm gB W σlast)
        (covGrad (I := I) (M := M) g 0 2 P) := by
  have hprod :
      operatorFieldApply (I := I) (M := M) g 2 5
          (slotExtendIter (I := I) (M := M) g 0 3 2
            (metricConnectionDifferenceLoweredCoefficient (I := I) (M := M) g gm g)) W =
        operatorFieldApply (I := I) (M := M) g 3 5
          (tensorThreeTwoProductCoefficient (I := I) (M := M) g W)
          (metricConnectionDifferenceLoweredCoefficient (I := I) (M := M) g gm g) := by
    simpa only [operatorFieldComposition_zero_eq_operatorFieldApply] using
      (tensorThreeTwoProductCoefficient_apply (I := I) (M := M) g
        (metricConnectionDifferenceLoweredCoefficient (I := I) (M := M) g gm g) W).symm
  have hconn :
      operatorFieldApply (I := I) (M := M) g 3 3
          (metricConnectionDifferenceLoweringCoefficient (I := I) (M := M) g)
          (covGrad (I := I) (M := M) g 0 2 P) =
        metricConnectionDifferenceLoweredCoefficient (I := I) (M := M) g gm g := by
    change operatorFieldApply (I := I) (M := M) g 3 3
        (metricConnectionDifferenceLoweringCoefficient (I := I) (M := M) g)
        (covGrad (I := I) (M := M) g 0 2 P) =
      lieCorrectionZeroKappa (I := I) (M := M) g gm g
    simpa only [operatorFieldComposition_zero_eq_operatorFieldApply] using
      metricConnectionDifferenceLoweringCoefficient_apply (I := I) (M := M) g gm P hP htie
  rw [lieCorrectionZeroMixedConnectionHalfExpansion]
  conv_lhs =>
    rw [← operatorFieldApplication_assoc, ← operatorFieldApplication_assoc, ← operatorFieldApplication_assoc, ← operatorFieldApplication_assoc]
  rw [hprod, ← hconn]
  rw [lieCorrectionZeroMixedConnectionHalfDerivativeCoefficient]
  conv_rhs =>
    rw [← operatorFieldApplication_assoc, ← operatorFieldApplication_assoc, ← operatorFieldApplication_assoc, ← operatorFieldApplication_assoc,
      ← operatorFieldApplication_assoc]

noncomputable def lieCorrectionZeroMixedConnectionDerivativeCoefficient
    (g gm gB : SmoothRiemannianMetric I M) (W : SmoothCcTensor g 0 2) :
    SmoothCcTensor g 3 2 :=
  (2 : ℝ) •
    (lieCorrectionZeroMixedConnectionHalfDerivativeCoefficient (I := I) (M := M) g gm gB W
        LieCorrectionZeroCore.lieCorrectionZeroMixedConnectionPermutationCycleZeroTwoOne +
      lieCorrectionZeroMixedConnectionHalfDerivativeCoefficient (I := I) (M := M) g gm gB W
        (lieCorrectionZeroMixedConnectionTraceOutputSwapPermutation * LieCorrectionZeroCore.lieCorrectionZeroMixedConnectionPermutationCycleZeroTwoOne))

omit [NeZero (Module.finrank ℝ E)] in
theorem lieCorrectionZeroMixedConnectionDerivativeCoefficient_apply
    (g gm gB : SmoothRiemannianMetric I M) (P W : SmoothCcTensor g 0 2)
    (hP : ∀ (x : M) (u v : TangentSpace I x),
      ccTensorBilin (I := I) g P x u v =
        ccTensorBilin (I := I) g P x v u)
    (htie : ∀ (x : M) (u v : TangentSpace I x),
      gm.inner x u v =
        g.inner x u v + ccTensorBilinSymm (I := I) g P x u v) :
    operatorFieldApply (I := I) (M := M) g 2 2
        (lieCorrectionZeroMixedConnectionExpansion (I := I) (M := M) g gm gB) W =
      operatorFieldApply (I := I) (M := M) g 3 2
        (lieCorrectionZeroMixedConnectionDerivativeCoefficient (I := I) (M := M) g gm gB W)
        (covGrad (I := I) (M := M) g 0 2 P) := by
  rw [lieCorrectionZeroMixedConnectionExpansion, operatorFieldApplication_smul_left, operatorFieldApplication_add_left]
  have hhalf := lieCorrectionZeroMixedConnectionHalfDerivativeCoefficient_apply (I := I) (M := M) g gm gB P W
    LieCorrectionZeroCore.lieCorrectionZeroMixedConnectionPermutationCycleZeroTwoOne hP htie
  have hhalf' := lieCorrectionZeroMixedConnectionHalfDerivativeCoefficient_apply (I := I) (M := M) g gm gB P W
    (lieCorrectionZeroMixedConnectionTraceOutputSwapPermutation * LieCorrectionZeroCore.lieCorrectionZeroMixedConnectionPermutationCycleZeroTwoOne) hP htie
  rw [hhalf, hhalf']
  rw [lieCorrectionZeroMixedConnectionDerivativeCoefficient, operatorFieldApplication_smul_left, operatorFieldApplication_add_left]

noncomputable def lieCorrectionZeroVectorBundleUnscaledDerivativeCoefficient
    (g gm : SmoothRiemannianMetric I M) (W : SmoothCcTensor g 0 2) :
    SmoothCcTensor g 3 2 :=
  ccOperatorFieldComp (I := I) (M := M) g 3 4 2
    (reindexedCometricDoubleTrace (I := I) (M := M) g gm)
    (ccOperatorFieldComp (I := I) (M := M) g 3 1 4
      (lieCorrectionZeroVectorBundleMetricConnectionDifferenceTerm (I := I) (M := M) g gm)
      (ccOperatorFieldComp (I := I) (M := M) g 3 1 1
        (cometricRaiseSlot0Field (I := I) (M := M) g 0 W)
        (ccOperatorFieldComp (I := I) (M := M) g 3 3 1
          (reindexedPureTrace (I := I) (M := M) g gm 1 (Equiv.refl _))
          (RicciDeTurckLowOrder.connectionDifferenceLowOrderOperator (I := I) (M := M) g gm))))

noncomputable def lieCorrectionZeroVectorBundleDerivativeCoefficient
    (g gm : SmoothRiemannianMetric I M) (W : SmoothCcTensor g 0 2) :
    SmoothCcTensor g 3 2 :=
  (2 : ℝ) • lieCorrectionZeroVectorBundleUnscaledDerivativeCoefficient (I := I) (M := M) g gm W

theorem lieCorrectionZeroVectorBundleDerivativeCoefficient_apply
    (g gm : SmoothRiemannianMetric I M) (P W : SmoothCcTensor g 0 2)
    (hP : ∀ (x : M) (u v : TangentSpace I x),
      ccTensorBilin (I := I) g P x u v =
        ccTensorBilin (I := I) g P x v u)
    (htie : ∀ (x : M) (u v : TangentSpace I x),
      gm.inner x u v =
        g.inner x u v + ccTensorBilinSymm (I := I) g P x u v) :
    operatorFieldApply (I := I) (M := M) g 2 2
        (lieCorrectionZeroVectorBundleExpansion (I := I) (M := M) g gm) W =
      operatorFieldApply (I := I) (M := M) g 3 2
        (lieCorrectionZeroVectorBundleDerivativeCoefficient (I := I) (M := M) g gm W)
        (covGrad (I := I) (M := M) g 0 2 P) := by
  have hip := operatorFieldApplication_ipLowCc_eq_cometricRaiseSlot0Field (I := I) (M := M) g (deTurckVectorFieldCovector (I := I) (M := M) g gm g) W
  have hw := deTurckVectorFieldCovector_eq_reindexedPureTrace_ccOperatorFieldComp (I := I) (M := M) g gm
  have hconn := RicciDeTurckLowOrder.connectionDifferenceLowOrderOperator_apply (I := I) (M := M) g gm P hP htie
  rw [lieCorrectionZeroVectorBundleExpansion, operatorFieldApplication_smul_left]
  rw [← operatorFieldApplication_assoc, ← operatorFieldApplication_assoc]
  rw [hip]
  rw [hw, operatorFieldComposition_zero_eq_operatorFieldApply]
  rw [← hconn]
  rw [operatorFieldComposition_zero_eq_operatorFieldApply]
  rw [lieCorrectionZeroVectorBundleDerivativeCoefficient, lieCorrectionZeroVectorBundleUnscaledDerivativeCoefficient, operatorFieldApplication_smul_left]
  conv_rhs =>
    rw [← operatorFieldApplication_assoc, ← operatorFieldApplication_assoc, ← operatorFieldApplication_assoc, ← operatorFieldApplication_assoc]

noncomputable def connectionDifferenceInsertionInnerDerivativeCoefficient
    (g : SmoothRiemannianMetric I M) (W : SmoothCcTensor g 0 2) :
    SmoothCcTensor g 3 3 :=
  ccOperatorFieldComp (I := I) (M := M) g 3 3 3
    (slotInsertEndoCc (I := I) (M := M) g 2
      (symmRaiseEndo (I := I) (M := M) g W))
    (permCoeff (I := I) (M := M) g (finRotate 3))

omit [NeZero (Module.finrank ℝ E)] in
theorem connectionDifferenceInsertionInnerDerivativeCoefficient_apply
    (g gm : SmoothRiemannianMetric I M) (W : SmoothCcTensor g 0 2) :
    operatorFieldApply (I := I) (M := M) g 2 3
        (connectionDifferenceContrInsertionInnerField (I := I) g gm)
        (symmS (I := I) (M := M) g W) =
      operatorFieldApply (I := I) (M := M) g 3 3
        (connectionDifferenceInsertionInnerDerivativeCoefficient (I := I) (M := M) g W)
        (metricLoweredConnectionDifferenceCoefficient (I := I) g gm) := by
  rw [connectionDifferenceInsertionInnerDerivativeCoefficient, ← operatorFieldApplication_assoc]
  rw [show operatorFieldApply (I := I) (M := M) g 3 3
      (permCoeff (I := I) (M := M) g (finRotate 3))
      (metricLoweredConnectionDifferenceCoefficient (I := I) g gm) =
        domDomCongrSection (I := I) g (finRotate 3)
          (metricLoweredConnectionDifferenceCoefficient (I := I) g gm) by
    simpa only [operatorFieldComposition_zero_eq_operatorFieldApply] using
      operatorFieldComposition_permutationCoefficient_apply (I := I) (M := M) g (finRotate 3)
        (metricLoweredConnectionDifferenceCoefficient (I := I) g gm)]
  apply smoothCcTensor_ext_of_unitModel (I := I) (M := M) g
  intro x
  apply ContinuousMultilinearMap.ext
  intro m
  have hm : m = ![m 0, m 1, m 2] := by
    funext j
    fin_cases j <;> rfl
  rw [unitModel, unitModel, operatorFieldApplication_toSection, operatorFieldApplication_toSection,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply]
  rw [connectionDifferenceContrInsertionInnerField_toSection]
  conv_lhs => rw [hm]
  rw [connContr11_insert']
  rw [show Tensor0SSpace.toModel
      ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from
        (symmS (I := I) (M := M) g W).toSection x)
        (unitTensor (I := I) (M := M) x))
      ![PDE.DeTurck.connectionDifference (I := I) gm g x (m 1) (m 2), m 0] =
        ccTensorBilin (I := I) g (symmS (I := I) (M := M) g W) x
          (PDE.DeTurck.connectionDifference (I := I) gm g x (m 1) (m 2)) (m 0) by
    rw [← unitModel_eq_ccTensorBilin_local (I := I) (M := M) g]
    rfl]
  rw [ccTensorBilin_symmS]
  rw [slotInsertEndoCc_toSection, slotInsertEndoFib_apply_eval]
  rw [show Tensor0SSpace.toModel
      ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 3 I x from
        (domDomCongrSection (I := I) g (finRotate 3)
          (metricLoweredConnectionDifferenceCoefficient (I := I) g gm)).toSection x)
        (unitTensor (I := I) (M := M) x))
      (Function.update m 0
        (symmRaiseEndo (I := I) (M := M) g W x (m 0))) =
        unitModel (I := I) (M := M) g 3
          (domDomCongrSection (I := I) g (finRotate 3)
            (metricLoweredConnectionDifferenceCoefficient (I := I) g gm)) x
          (Function.update m 0
            (symmRaiseEndo (I := I) (M := M) g W x (m 0))) from rfl]
  rw [domDomCongrSection_unitModel, ContinuousMultilinearMap.domDomCongr_apply]
  rw [show (fun i =>
      Function.update m 0
        (symmRaiseEndo (I := I) (M := M) g W x (m 0)) ((finRotate 3) i)) =
        ![m 1, m 2, symmRaiseEndo (I := I) (M := M) g W x (m 0)] by
    funext j
    fin_cases j <;> rfl]
  rw [connectionDifferenceLoweredCc_unitModel_apply']
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]
  rw [g.symm, symmRaiseEndo_apply, inner_symmRaiseEndo]
  exact ccTensorBilinSymm_symm (I := I) g W x _ _

noncomputable def connectionDifferenceInsertionInnerActionCoefficient
    (g gm : SmoothRiemannianMetric I M) (W : SmoothCcTensor g 0 2) :
    SmoothCcTensor g 3 3 :=
  ccOperatorFieldComp (I := I) (M := M) g 3 3 3
    (connectionDifferenceInsertionInnerDerivativeCoefficient (I := I) (M := M) g W)
    (RicciDeTurckLowOrder.connectionDifferenceLowOrderOperator (I := I) (M := M) g gm)

omit [NeZero (Module.finrank ℝ E)] in
theorem connectionDifferenceInsertionInnerActionCoefficient_apply
    (g gm : SmoothRiemannianMetric I M) (P W : SmoothCcTensor g 0 2)
    (hP : ∀ (x : M) (u v : TangentSpace I x),
      ccTensorBilin (I := I) g P x u v =
        ccTensorBilin (I := I) g P x v u)
    (htie : ∀ (x : M) (u v : TangentSpace I x),
      gm.inner x u v =
        g.inner x u v + ccTensorBilinSymm (I := I) g P x u v) :
    operatorFieldApply (I := I) (M := M) g 2 3
        (connectionDifferenceContrInsertionInnerField (I := I) g gm)
        (symmS (I := I) (M := M) g W) =
      operatorFieldApply (I := I) (M := M) g 3 3
        (connectionDifferenceInsertionInnerActionCoefficient (I := I) (M := M) g gm W)
        (covGrad (I := I) (M := M) g 0 2 P) := by
  rw [connectionDifferenceInsertionInnerDerivativeCoefficient_apply (I := I) (M := M) g gm W]
  rw [← RicciDeTurckLowOrder.connectionDifferenceLowOrderOperator_apply (I := I) (M := M) g gm P hP htie]
  rw [connectionDifferenceInsertionInnerActionCoefficient, ← operatorFieldApplication_assoc]
  rw [operatorFieldComposition_zero_eq_operatorFieldApply]

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] [SigmaCompactSpace M] in
private theorem operatorFieldApplication_reindexCoeffGen_symmetrized_input
    (g : SmoothRiemannianMetric I M) {s : ℕ}
    (R : SmoothCcTensor g 2 s) (W : SmoothCcTensor g 0 2) :
    operatorFieldApply (I := I) (M := M) g 2 s
        (reindexCoeffGen (I := I) (M := M) g 2 s R innerCoreInPerm10)
        (symmS (I := I) (M := M) g W) =
      operatorFieldApply (I := I) (M := M) g 2 s R
        (symmS (I := I) (M := M) g W) := by
  have hperm : innerCoreInPerm10 = Equiv.swap (0 : Fin 2) 1 := by
    ext j
    fin_cases j <;> rfl
  rw [hperm]
  apply smoothCcTensor_ext_of_unitModel (I := I) (M := M) g
  intro x
  rw [unitModel, unitModel, operatorFieldApplication_toSection, operatorFieldApplication_toSection,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply]
  rw [reindexCoeffGen_toSection, reindexCoeffFibGen_apply]
  have hu : Tensor0SSpace.ofModel
      (ContinuousMultilinearMap.domDomCongr (Equiv.swap (0 : Fin 2) 1)
        (Tensor0SSpace.toModel
          ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from
            (symmS (I := I) (M := M) g W).toSection x)
            (unitTensor (I := I) (M := M) x)))) =
      (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from
        (symmS (I := I) (M := M) g W).toSection x)
        (unitTensor (I := I) (M := M) x) := by
    apply Tensor0SSpace.toModel_injective
    change ContinuousMultilinearMap.domDomCongr (Equiv.swap (0 : Fin 2) 1)
        (Tensor0SSpace.toModel
          ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from
            (symmS (I := I) (M := M) g W).toSection x)
            (unitTensor (I := I) (M := M) x))) =
      Tensor0SSpace.toModel
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from
          (symmS (I := I) (M := M) g W).toSection x)
          (unitTensor (I := I) (M := M) x))
    apply ContinuousMultilinearMap.ext
    intro v
    rw [ContinuousMultilinearMap.domDomCongr_apply]
    have hv : (fun i => v ((Equiv.swap (0 : Fin 2) 1) i)) = ![v 1, v 0] := by
      funext j
      fin_cases j <;> rfl
    have hv' : v = ![v 0, v 1] := by
      funext j
      fin_cases j <;> rfl
    rw [hv]
    conv_rhs => rw [hv']
    change unitModel (I := I) (M := M) g 2
        (symmS (I := I) (M := M) g W) x ![v 1, v 0] =
      unitModel (I := I) (M := M) g 2
        (symmS (I := I) (M := M) g W) x ![v 0, v 1]
    rw [unitModel_eq_ccTensorBilin_local,
      unitModel_eq_ccTensorBilin_local, ccTensorBilin_symmS,
      ccTensorBilin_symmS]
    exact ccTensorBilinSymm_symm (I := I) g W x (v 1) (v 0)
  rw [hu]

def ricciQuadraticPermutation_cycleZeroThreeOneTwo : Equiv.Perm (Fin 4) :=
  ⟨![3, 2, 0, 1], ![2, 3, 1, 0], by decide, by decide⟩

def ricciQuadraticPermutation_swapBlocks : Equiv.Perm (Fin 4) :=
  ⟨![2, 3, 0, 1], ![2, 3, 0, 1], by decide, by decide⟩

def ricciQuadraticPermutation_cycleZeroThreeTwo : Equiv.Perm (Fin 4) :=
  ⟨![3, 1, 0, 2], ![2, 1, 3, 0], by decide, by decide⟩

def ricciQuadraticPermutation_cycleZeroOneThreeTwo : Equiv.Perm (Fin 4) :=
  ⟨![1, 3, 0, 2], ![2, 0, 3, 1], by decide, by decide⟩

def ricciQuadraticPermutation_cycleZeroOneTwo : Equiv.Perm (Fin 4) :=
  ⟨![1, 2, 0, 3], ![2, 0, 1, 3], by decide, by decide⟩

def ricciQuadraticPermutation_swapZeroTwo : Equiv.Perm (Fin 4) :=
  ⟨![2, 1, 0, 3], ![2, 1, 0, 3], by decide, by decide⟩

def ricciQuadraticPermutation_swapZeroOne : Equiv.Perm (Fin 3) :=
  ⟨![1, 0, 2], ![1, 0, 2], by decide, by decide⟩

def ricciQuadraticPermutation_rotateInputs : Equiv.Perm (Fin 3) :=
  ⟨![1, 2, 0], ![2, 0, 1], by decide, by decide⟩

private noncomputable def nestedConnectionDifferenceKernelTerm_swapZeroOne_cycleZeroThreeOneTwo
    (g gm : SmoothRiemannianMetric I M) : SmoothCcTensor g 2 4 :=
  ccOperatorFieldComp (I := I) (M := M) g 2 4 4
      (permCoeff (I := I) (M := M) g ricciQuadraticPermutation_cycleZeroThreeOneTwo)
    (ccOperatorFieldComp (I := I) (M := M) g 2 3 4
      (connectionDifferenceContravariantInsertionField (I := I) g gm)
      (ccOperatorFieldComp (I := I) (M := M) g 2 3 3
        (permCoeff (I := I) (M := M) g ricciQuadraticPermutation_swapZeroOne)
        (connectionDifferenceContrInsertionInnerField (I := I) g gm)))

noncomputable def ricciQuadraticKernelDerivativeNestedTerm
    (g gm : SmoothRiemannianMetric I M) (W : SmoothCcTensor g 0 2)
    (mid : Equiv.Perm (Fin 3)) (out : Equiv.Perm (Fin 4)) :
    SmoothCcTensor g 3 4 :=
  ccOperatorFieldComp (I := I) (M := M) g 3 4 4
      (permCoeff (I := I) (M := M) g out)
    (ccOperatorFieldComp (I := I) (M := M) g 3 3 4
      (connectionDifferenceContravariantInsertionField (I := I) g gm)
      (ccOperatorFieldComp (I := I) (M := M) g 3 3 3
        (permCoeff (I := I) (M := M) g mid)
        (connectionDifferenceInsertionInnerActionCoefficient (I := I) (M := M) g gm W)))

omit [NeZero (Module.finrank ℝ E)] in
theorem ricciQuadraticKernelDerivativeNestedTerm_apply
    (g gm : SmoothRiemannianMetric I M) (P W : SmoothCcTensor g 0 2)
    (mid : Equiv.Perm (Fin 3)) (out : Equiv.Perm (Fin 4))
    (hP : ∀ (x : M) (u v : TangentSpace I x),
      ccTensorBilin (I := I) g P x u v =
        ccTensorBilin (I := I) g P x v u)
    (htie : ∀ (x : M) (u v : TangentSpace I x),
      gm.inner x u v =
        g.inner x u v + ccTensorBilinSymm (I := I) g P x u v) :
    operatorFieldApply (I := I) (M := M) g 2 4
        (ccOperatorFieldComp (I := I) (M := M) g 2 4 4
          (permCoeff (I := I) (M := M) g out)
          (ccOperatorFieldComp (I := I) (M := M) g 2 3 4
            (connectionDifferenceContravariantInsertionField (I := I) g gm)
            (ccOperatorFieldComp (I := I) (M := M) g 2 3 3
              (permCoeff (I := I) (M := M) g mid)
              (connectionDifferenceContrInsertionInnerField (I := I) g gm))))
        (symmS (I := I) (M := M) g W) =
      operatorFieldApply (I := I) (M := M) g 3 4
        (ricciQuadraticKernelDerivativeNestedTerm (I := I) (M := M) g gm W mid out)
        (covGrad (I := I) (M := M) g 0 2 P) := by
  have hinner := connectionDifferenceInsertionInnerActionCoefficient_apply (I := I) (M := M) g gm P W hP htie
  conv_lhs =>
    rw [← operatorFieldApplication_assoc, ← operatorFieldApplication_assoc, ← operatorFieldApplication_assoc]
  rw [hinner]
  rw [ricciQuadraticKernelDerivativeNestedTerm]
  conv_rhs =>
    rw [← operatorFieldApplication_assoc, ← operatorFieldApplication_assoc, ← operatorFieldApplication_assoc]

omit [NeZero (Module.finrank ℝ E)] in
private theorem nestedConnectionDifferenceKernelTerm_swapZeroOne_cycleZeroThreeOneTwo_apply
    (g gm : SmoothRiemannianMetric I M) (P W : SmoothCcTensor g 0 2)
    (hP : ∀ (x : M) (u v : TangentSpace I x),
      ccTensorBilin (I := I) g P x u v =
        ccTensorBilin (I := I) g P x v u)
    (htie : ∀ (x : M) (u v : TangentSpace I x),
      gm.inner x u v =
        g.inner x u v + ccTensorBilinSymm (I := I) g P x u v) :
    operatorFieldApply (I := I) (M := M) g 2 4 (nestedConnectionDifferenceKernelTerm_swapZeroOne_cycleZeroThreeOneTwo (I := I) (M := M) g gm)
        (symmS (I := I) (M := M) g W) =
      operatorFieldApply (I := I) (M := M) g 3 4
        (ricciQuadraticKernelDerivativeNestedTerm (I := I) (M := M) g gm W ricciQuadraticPermutation_swapZeroOne ricciQuadraticPermutation_cycleZeroThreeOneTwo)
        (covGrad (I := I) (M := M) g 0 2 P) := by
  rw [nestedConnectionDifferenceKernelTerm_swapZeroOne_cycleZeroThreeOneTwo]
  exact ricciQuadraticKernelDerivativeNestedTerm_apply (I := I) (M := M) g gm P W
    ricciQuadraticPermutation_swapZeroOne ricciQuadraticPermutation_cycleZeroThreeOneTwo hP htie

private noncomputable def reindexedNestedConnectionDifferenceKernelTerm_swapZeroOne_swapBlocks
    (g gm : SmoothRiemannianMetric I M) : SmoothCcTensor g 2 4 :=
  reindexCoeffGen (I := I) (M := M) g 2 4
    (ccOperatorFieldComp (I := I) (M := M) g 2 4 4
      (permCoeff (I := I) (M := M) g ricciQuadraticPermutation_swapBlocks)
      (ccOperatorFieldComp (I := I) (M := M) g 2 3 4
        (connectionDifferenceContravariantInsertionField (I := I) g gm)
        (ccOperatorFieldComp (I := I) (M := M) g 2 3 3
          (permCoeff (I := I) (M := M) g ricciQuadraticPermutation_swapZeroOne)
          (connectionDifferenceContrInsertionInnerField (I := I) g gm))))
    innerCoreInPerm10

private noncomputable def nestedConnectionDifferenceKernelTerm_rotateInputs_cycleZeroThreeTwo
    (g gm : SmoothRiemannianMetric I M) : SmoothCcTensor g 2 4 :=
  ccOperatorFieldComp (I := I) (M := M) g 2 4 4
      (permCoeff (I := I) (M := M) g ricciQuadraticPermutation_cycleZeroThreeTwo)
    (ccOperatorFieldComp (I := I) (M := M) g 2 3 4
      (connectionDifferenceContravariantInsertionField (I := I) g gm)
      (ccOperatorFieldComp (I := I) (M := M) g 2 3 3
        (permCoeff (I := I) (M := M) g ricciQuadraticPermutation_rotateInputs)
        (connectionDifferenceContrInsertionInnerField (I := I) g gm)))

private noncomputable def reindexedBareConnectionDifferenceKernelTerm_cycleZeroOneThreeTwo
    (g gm : SmoothRiemannianMetric I M) : SmoothCcTensor g 2 4 :=
  reindexCoeffGen (I := I) (M := M) g 2 4
    (ccOperatorFieldComp (I := I) (M := M) g 2 4 4
      (permCoeff (I := I) (M := M) g ricciQuadraticPermutation_cycleZeroOneThreeTwo)
      (ccOperatorFieldComp (I := I) (M := M) g 2 3 4
        (connectionDifferenceContravariantInsertionField (I := I) g gm)
        (connectionDifferenceContrInsertionInnerField (I := I) g gm)))
    innerCoreInPerm10

private noncomputable def bareConnectionDifferenceKernelTerm_cycleZeroOneTwo
    (g gm : SmoothRiemannianMetric I M) : SmoothCcTensor g 2 4 :=
  ccOperatorFieldComp (I := I) (M := M) g 2 4 4
      (permCoeff (I := I) (M := M) g ricciQuadraticPermutation_cycleZeroOneTwo)
    (ccOperatorFieldComp (I := I) (M := M) g 2 3 4
      (connectionDifferenceContravariantInsertionField (I := I) g gm)
      (connectionDifferenceContrInsertionInnerField (I := I) g gm))

private noncomputable def reindexedNestedConnectionDifferenceKernelTerm_rotateInputs_swapZeroTwo
    (g gm : SmoothRiemannianMetric I M) : SmoothCcTensor g 2 4 :=
  reindexCoeffGen (I := I) (M := M) g 2 4
    (ccOperatorFieldComp (I := I) (M := M) g 2 4 4
      (permCoeff (I := I) (M := M) g ricciQuadraticPermutation_swapZeroTwo)
      (ccOperatorFieldComp (I := I) (M := M) g 2 3 4
        (connectionDifferenceContravariantInsertionField (I := I) g gm)
        (ccOperatorFieldComp (I := I) (M := M) g 2 3 3
          (permCoeff (I := I) (M := M) g ricciQuadraticPermutation_rotateInputs)
          (connectionDifferenceContrInsertionInnerField (I := I) g gm))))
    innerCoreInPerm10

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [SigmaCompactSpace M] in
private theorem ricciConnectionDifferenceQuadraticKernel_eq_sum
    (g gm : SmoothRiemannianMetric I M) :
    ricciConnectionDifferenceQuadraticKernel (I := I) (M := M) g gm =
      nestedConnectionDifferenceKernelTerm_swapZeroOne_cycleZeroThreeOneTwo (I := I) (M := M) g gm +
      reindexedNestedConnectionDifferenceKernelTerm_swapZeroOne_swapBlocks (I := I) (M := M) g gm +
      nestedConnectionDifferenceKernelTerm_rotateInputs_cycleZeroThreeTwo (I := I) (M := M) g gm +
      reindexedBareConnectionDifferenceKernelTerm_cycleZeroOneThreeTwo (I := I) (M := M) g gm +
      bareConnectionDifferenceKernelTerm_cycleZeroOneTwo (I := I) (M := M) g gm +
      reindexedNestedConnectionDifferenceKernelTerm_rotateInputs_swapZeroTwo (I := I) (M := M) g gm := by
  rfl

noncomputable def ricciQuadraticKernelDerivativeBareTerm
    (g gm : SmoothRiemannianMetric I M) (W : SmoothCcTensor g 0 2)
    (out : Equiv.Perm (Fin 4)) : SmoothCcTensor g 3 4 :=
  ccOperatorFieldComp (I := I) (M := M) g 3 4 4
      (permCoeff (I := I) (M := M) g out)
    (ccOperatorFieldComp (I := I) (M := M) g 3 3 4
      (connectionDifferenceContravariantInsertionField (I := I) g gm)
      (connectionDifferenceInsertionInnerActionCoefficient (I := I) (M := M) g gm W))

omit [NeZero (Module.finrank ℝ E)] in
theorem ricciQuadraticKernelDerivativeBareTerm_apply
    (g gm : SmoothRiemannianMetric I M) (P W : SmoothCcTensor g 0 2)
    (out : Equiv.Perm (Fin 4))
    (hP : ∀ (x : M) (u v : TangentSpace I x),
      ccTensorBilin (I := I) g P x u v =
        ccTensorBilin (I := I) g P x v u)
    (htie : ∀ (x : M) (u v : TangentSpace I x),
      gm.inner x u v =
        g.inner x u v + ccTensorBilinSymm (I := I) g P x u v) :
    operatorFieldApply (I := I) (M := M) g 2 4
        (ccOperatorFieldComp (I := I) (M := M) g 2 4 4
          (permCoeff (I := I) (M := M) g out)
          (ccOperatorFieldComp (I := I) (M := M) g 2 3 4
            (connectionDifferenceContravariantInsertionField (I := I) g gm)
            (connectionDifferenceContrInsertionInnerField (I := I) g gm)))
        (symmS (I := I) (M := M) g W) =
      operatorFieldApply (I := I) (M := M) g 3 4
        (ricciQuadraticKernelDerivativeBareTerm (I := I) (M := M) g gm W out)
        (covGrad (I := I) (M := M) g 0 2 P) := by
  have hinner := connectionDifferenceInsertionInnerActionCoefficient_apply (I := I) (M := M) g gm P W hP htie
  conv_lhs =>
    rw [← operatorFieldApplication_assoc, ← operatorFieldApplication_assoc]
  rw [hinner]
  rw [ricciQuadraticKernelDerivativeBareTerm]
  conv_rhs =>
    rw [← operatorFieldApplication_assoc, ← operatorFieldApplication_assoc]

omit [NeZero (Module.finrank ℝ E)] in
private theorem reindexedNestedConnectionDifferenceKernelTerm_swapZeroOne_swapBlocks_apply
    (g gm : SmoothRiemannianMetric I M) (P W : SmoothCcTensor g 0 2)
    (hP : ∀ (x : M) (u v : TangentSpace I x),
      ccTensorBilin (I := I) g P x u v =
        ccTensorBilin (I := I) g P x v u)
    (htie : ∀ (x : M) (u v : TangentSpace I x),
      gm.inner x u v =
        g.inner x u v + ccTensorBilinSymm (I := I) g P x u v) :
    operatorFieldApply (I := I) (M := M) g 2 4 (reindexedNestedConnectionDifferenceKernelTerm_swapZeroOne_swapBlocks (I := I) (M := M) g gm)
        (symmS (I := I) (M := M) g W) =
      operatorFieldApply (I := I) (M := M) g 3 4
        (ricciQuadraticKernelDerivativeNestedTerm (I := I) (M := M) g gm W ricciQuadraticPermutation_swapZeroOne ricciQuadraticPermutation_swapBlocks)
        (covGrad (I := I) (M := M) g 0 2 P) := by
  rw [reindexedNestedConnectionDifferenceKernelTerm_swapZeroOne_swapBlocks, operatorFieldApplication_reindexCoeffGen_symmetrized_input]
  exact ricciQuadraticKernelDerivativeNestedTerm_apply (I := I) (M := M) g gm P W
    ricciQuadraticPermutation_swapZeroOne ricciQuadraticPermutation_swapBlocks hP htie

omit [NeZero (Module.finrank ℝ E)] in
private theorem nestedConnectionDifferenceKernelTerm_rotateInputs_cycleZeroThreeTwo_apply
    (g gm : SmoothRiemannianMetric I M) (P W : SmoothCcTensor g 0 2)
    (hP : ∀ (x : M) (u v : TangentSpace I x),
      ccTensorBilin (I := I) g P x u v =
        ccTensorBilin (I := I) g P x v u)
    (htie : ∀ (x : M) (u v : TangentSpace I x),
      gm.inner x u v =
        g.inner x u v + ccTensorBilinSymm (I := I) g P x u v) :
    operatorFieldApply (I := I) (M := M) g 2 4 (nestedConnectionDifferenceKernelTerm_rotateInputs_cycleZeroThreeTwo (I := I) (M := M) g gm)
        (symmS (I := I) (M := M) g W) =
      operatorFieldApply (I := I) (M := M) g 3 4
        (ricciQuadraticKernelDerivativeNestedTerm (I := I) (M := M) g gm W ricciQuadraticPermutation_rotateInputs ricciQuadraticPermutation_cycleZeroThreeTwo)
        (covGrad (I := I) (M := M) g 0 2 P) := by
  rw [nestedConnectionDifferenceKernelTerm_rotateInputs_cycleZeroThreeTwo]
  exact ricciQuadraticKernelDerivativeNestedTerm_apply (I := I) (M := M) g gm P W
    ricciQuadraticPermutation_rotateInputs ricciQuadraticPermutation_cycleZeroThreeTwo hP htie

omit [NeZero (Module.finrank ℝ E)] in
private theorem reindexedBareConnectionDifferenceKernelTerm_cycleZeroOneThreeTwo_apply
    (g gm : SmoothRiemannianMetric I M) (P W : SmoothCcTensor g 0 2)
    (hP : ∀ (x : M) (u v : TangentSpace I x),
      ccTensorBilin (I := I) g P x u v =
        ccTensorBilin (I := I) g P x v u)
    (htie : ∀ (x : M) (u v : TangentSpace I x),
      gm.inner x u v =
        g.inner x u v + ccTensorBilinSymm (I := I) g P x u v) :
    operatorFieldApply (I := I) (M := M) g 2 4 (reindexedBareConnectionDifferenceKernelTerm_cycleZeroOneThreeTwo (I := I) (M := M) g gm)
        (symmS (I := I) (M := M) g W) =
      operatorFieldApply (I := I) (M := M) g 3 4
        (ricciQuadraticKernelDerivativeBareTerm (I := I) (M := M) g gm W ricciQuadraticPermutation_cycleZeroOneThreeTwo)
        (covGrad (I := I) (M := M) g 0 2 P) := by
  rw [reindexedBareConnectionDifferenceKernelTerm_cycleZeroOneThreeTwo, operatorFieldApplication_reindexCoeffGen_symmetrized_input]
  exact ricciQuadraticKernelDerivativeBareTerm_apply (I := I) (M := M) g gm P W ricciQuadraticPermutation_cycleZeroOneThreeTwo hP htie

omit [NeZero (Module.finrank ℝ E)] in
private theorem bareConnectionDifferenceKernelTerm_cycleZeroOneTwo_apply
    (g gm : SmoothRiemannianMetric I M) (P W : SmoothCcTensor g 0 2)
    (hP : ∀ (x : M) (u v : TangentSpace I x),
      ccTensorBilin (I := I) g P x u v =
        ccTensorBilin (I := I) g P x v u)
    (htie : ∀ (x : M) (u v : TangentSpace I x),
      gm.inner x u v =
        g.inner x u v + ccTensorBilinSymm (I := I) g P x u v) :
    operatorFieldApply (I := I) (M := M) g 2 4 (bareConnectionDifferenceKernelTerm_cycleZeroOneTwo (I := I) (M := M) g gm)
        (symmS (I := I) (M := M) g W) =
      operatorFieldApply (I := I) (M := M) g 3 4
        (ricciQuadraticKernelDerivativeBareTerm (I := I) (M := M) g gm W ricciQuadraticPermutation_cycleZeroOneTwo)
        (covGrad (I := I) (M := M) g 0 2 P) := by
  rw [bareConnectionDifferenceKernelTerm_cycleZeroOneTwo]
  exact ricciQuadraticKernelDerivativeBareTerm_apply (I := I) (M := M) g gm P W ricciQuadraticPermutation_cycleZeroOneTwo hP htie

omit [NeZero (Module.finrank ℝ E)] in
private theorem reindexedNestedConnectionDifferenceKernelTerm_rotateInputs_swapZeroTwo_apply
    (g gm : SmoothRiemannianMetric I M) (P W : SmoothCcTensor g 0 2)
    (hP : ∀ (x : M) (u v : TangentSpace I x),
      ccTensorBilin (I := I) g P x u v =
        ccTensorBilin (I := I) g P x v u)
    (htie : ∀ (x : M) (u v : TangentSpace I x),
      gm.inner x u v =
        g.inner x u v + ccTensorBilinSymm (I := I) g P x u v) :
    operatorFieldApply (I := I) (M := M) g 2 4 (reindexedNestedConnectionDifferenceKernelTerm_rotateInputs_swapZeroTwo (I := I) (M := M) g gm)
        (symmS (I := I) (M := M) g W) =
      operatorFieldApply (I := I) (M := M) g 3 4
        (ricciQuadraticKernelDerivativeNestedTerm (I := I) (M := M) g gm W ricciQuadraticPermutation_rotateInputs ricciQuadraticPermutation_swapZeroTwo)
        (covGrad (I := I) (M := M) g 0 2 P) := by
  rw [reindexedNestedConnectionDifferenceKernelTerm_rotateInputs_swapZeroTwo, operatorFieldApplication_reindexCoeffGen_symmetrized_input]
  exact ricciQuadraticKernelDerivativeNestedTerm_apply (I := I) (M := M) g gm P W
    ricciQuadraticPermutation_rotateInputs ricciQuadraticPermutation_swapZeroTwo hP htie

noncomputable def ricciQuadraticKernelDerivativeCoefficient
    (g gm : SmoothRiemannianMetric I M) (W : SmoothCcTensor g 0 2) :
    SmoothCcTensor g 3 4 :=
  ricciQuadraticKernelDerivativeNestedTerm (I := I) (M := M) g gm W ricciQuadraticPermutation_swapZeroOne ricciQuadraticPermutation_cycleZeroThreeOneTwo +
    ricciQuadraticKernelDerivativeNestedTerm (I := I) (M := M) g gm W ricciQuadraticPermutation_swapZeroOne ricciQuadraticPermutation_swapBlocks +
    ricciQuadraticKernelDerivativeNestedTerm (I := I) (M := M) g gm W ricciQuadraticPermutation_rotateInputs ricciQuadraticPermutation_cycleZeroThreeTwo +
    ricciQuadraticKernelDerivativeBareTerm (I := I) (M := M) g gm W ricciQuadraticPermutation_cycleZeroOneThreeTwo +
    ricciQuadraticKernelDerivativeBareTerm (I := I) (M := M) g gm W ricciQuadraticPermutation_cycleZeroOneTwo +
    ricciQuadraticKernelDerivativeNestedTerm (I := I) (M := M) g gm W ricciQuadraticPermutation_rotateInputs ricciQuadraticPermutation_swapZeroTwo

noncomputable def ricciConnectionDifferenceQuadraticDerivativeCoefficient
    (g gm : SmoothRiemannianMetric I M) (W : SmoothCcTensor g 0 2) :
    SmoothCcTensor g 3 2 :=
  ccOperatorFieldComp (I := I) (M := M) g 3 4 2
    (ricciCometricFourTraceCastG0 (I := I) g gm)
    (ricciQuadraticKernelDerivativeCoefficient (I := I) (M := M) g gm W)

omit [NeZero (Module.finrank ℝ E)] in
theorem ricciConnectionDifferenceQuadraticDerivativeCoefficient_apply
    (g gm : SmoothRiemannianMetric I M) (P W : SmoothCcTensor g 0 2)
    (hP : ∀ (x : M) (u v : TangentSpace I x),
      ccTensorBilin (I := I) g P x u v =
        ccTensorBilin (I := I) g P x v u)
    (htie : ∀ (x : M) (u v : TangentSpace I x),
      gm.inner x u v =
        g.inner x u v + ccTensorBilinSymm (I := I) g P x u v) :
    operatorFieldApply (I := I) (M := M) g 2 2
        (ricciConnectionDifferenceQuadraticArm (I := I) (M := M) g gm)
        (symmS (I := I) (M := M) g W) =
      operatorFieldApply (I := I) (M := M) g 3 2
        (ricciConnectionDifferenceQuadraticDerivativeCoefficient (I := I) (M := M) g gm W)
        (covGrad (I := I) (M := M) g 0 2 P) := by
  rw [ricciConnectionDifferenceQuadraticArm, ← operatorFieldApplication_assoc, ricciConnectionDifferenceQuadraticKernel_eq_sum]
  simp only [operatorFieldApplication_add_left]
  have h0 := nestedConnectionDifferenceKernelTerm_swapZeroOne_cycleZeroThreeOneTwo_apply (I := I) (M := M) g gm P W hP htie
  have h1 := reindexedNestedConnectionDifferenceKernelTerm_swapZeroOne_swapBlocks_apply (I := I) (M := M) g gm P W hP htie
  have h2 := nestedConnectionDifferenceKernelTerm_rotateInputs_cycleZeroThreeTwo_apply (I := I) (M := M) g gm P W hP htie
  have h3 := reindexedBareConnectionDifferenceKernelTerm_cycleZeroOneThreeTwo_apply (I := I) (M := M) g gm P W hP htie
  have h4 := bareConnectionDifferenceKernelTerm_cycleZeroOneTwo_apply (I := I) (M := M) g gm P W hP htie
  have h5 := reindexedNestedConnectionDifferenceKernelTerm_rotateInputs_swapZeroTwo_apply (I := I) (M := M) g gm P W hP htie
  rw [h0, h1, h2, h3, h4, h5]
  rw [ricciConnectionDifferenceQuadraticDerivativeCoefficient, ← operatorFieldApplication_assoc, ricciQuadraticKernelDerivativeCoefficient]
  simp only [operatorFieldApplication_add_left]

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] [SigmaCompactSpace M] in
private theorem operatorFieldApplication_ccSlotSwapField_apply
    (g : SmoothRiemannianMetric I M) (W : SmoothCcTensor g 0 2) :
    operatorFieldApply (I := I) (M := M) g 2 2
        (ccSlotSwapField (I := I) (M := M) g) W =
      domDomCongrSection (I := I) g (Equiv.swap (0 : Fin 2) 1) W := by
  apply smoothCcTensor_ext_of_unitModel (I := I) (M := M) g
  intro x
  rw [domDomCongrSection_unitModel]
  apply ContinuousMultilinearMap.ext
  intro v
  rw [unitModel, operatorFieldApplication_toSection, ContinuousLinearMap.comp_apply,
    ccSlotSwapField_toSection]
  change Tensor0SSpace.toModel
      (slotSwapFib (I := I) (M := M) x
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from
          W.toSection x) (unitTensor (I := I) (M := M) x))) v =
    (ContinuousMultilinearMap.domDomCongr
      (Equiv.swap (0 : Fin 2) 1)
      (unitModel (I := I) (M := M) g 2 W x)) v
  rw [slotSwapFib_apply, Tensor0SSpace.toModel_ofModel,
    ContinuousMultilinearMap.domDomCongr_apply]
  rfl

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] [SigmaCompactSpace M] in
private theorem operatorFieldApplication_ccInputSlotSymm_apply
    (g : SmoothRiemannianMetric I M) (C : SmoothCcTensor g 2 2)
    (W : SmoothCcTensor g 0 2) :
    operatorFieldApply (I := I) (M := M) g 2 2
        (ccInputSlotSymm (I := I) (M := M) g C) W =
      operatorFieldApply (I := I) (M := M) g 2 2 C
        (symmS (I := I) (M := M) g W) := by
  simp only [ccInputSlotSymm, ccInputSlotSymm]
  have hswap := operatorFieldApplication_ccSlotSwapField_apply (I := I) (M := M) g W
  rw [operatorFieldApplication_smul_left, operatorFieldApplication_add_left, ← operatorFieldApplication_assoc,
    hswap]
  simp only [symmS, ccTensor02Symm]
  rw [operatorFieldApplication_smul_right, operatorFieldApplication_add_right]

noncomputable def ricciConnectionDifferenceDerivativeCoefficient
    (g gm : SmoothRiemannianMetric I M) (W : SmoothCcTensor g 0 2) :
    SmoothCcTensor g 3 2 :=
  ricciConnectionDifferenceQuadraticDerivativeCoefficient (I := I) (M := M) g gm W +
    RicciDeTurckLowOrder.ricciConnectionDerivativeTransposedCoefficient (I := I) (M := M) g gm
      (symmS (I := I) (M := M) g W)

theorem ricciConnectionDifferenceDerivativeCoefficient_apply
    (g gm : SmoothRiemannianMetric I M) (P W : SmoothCcTensor g 0 2)
    (hP : ∀ (x : M) (u v : TangentSpace I x),
      ccTensorBilin (I := I) g P x u v =
        ccTensorBilin (I := I) g P x v u)
    (htie : ∀ (x : M) (u v : TangentSpace I x),
      gm.inner x u v =
        g.inner x u v + ccTensorBilinSymm (I := I) g P x u v) :
    operatorFieldApply (I := I) (M := M) g 2 2
        (RicciDeTurckLowOrder.symmetrizedRicciConnectionDifferenceLowOrderCoefficient (I := I) (M := M) g gm P) W =
      operatorFieldApply (I := I) (M := M) g 3 2
        (ricciConnectionDifferenceDerivativeCoefficient (I := I) (M := M) g gm W)
        (covGrad (I := I) (M := M) g 0 2 P) := by
  have hsymmInput := operatorFieldApplication_ccInputSlotSymm_apply (I := I) (M := M) g
    (RicciDeTurckLowOrder.ricciConnectionDifferenceLowOrderCoefficient (I := I) (M := M) g gm P) W
  have haa := ricciConnectionDifferenceQuadraticDerivativeCoefficient_apply (I := I) (M := M) g gm P W hP htie
  have hda := RicciDeTurckLowOrder.ricciCovariantDerivativeConnectionDifferenceLowOrder_apply (I := I) (M := M) g gm P
    (symmS (I := I) (M := M) g W)
  rw [RicciDeTurckLowOrder.symmetrizedRicciConnectionDifferenceLowOrderCoefficient, hsymmInput,
    RicciDeTurckLowOrder.ricciConnectionDifferenceLowOrderCoefficient, operatorFieldApplication_add_left]
  rw [haa, hda]
  rw [ricciConnectionDifferenceDerivativeCoefficient, operatorFieldApplication_add_left]

theorem lowerScalePathIntegrand_decomposition
    (g : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2)
    (hT : ∀ (x : M) (u v : TangentSpace I x),
      ccTensorBilin (I := I) g T x u v =
        ccTensorBilin (I := I) g T x v u)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) δ)
    (hδZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g
        (0 : SmoothCcTensor g 0 2)) δ)
    {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) 1) :
    RicciDeTurckLowOrder.pathIntegrand (I := I) (M := M) g g T hδ hδZ s =
      let gm := metricPerturbationPath (I := I) g T 0 hδ hδZ s
      ((((-2 : ℝ) •
            RicciDeTurckLowOrder.symmetrizedRicciConnectionDifferenceLowOrderCoefficient (I := I) (M := M) g gm (s • T) +
          (deTurckLieCovariantDerivativeArmField (I := I) (M := M) g gm g -
            deTurckLieTopOrderPairingFamily (I := I) (M := M) g T hδ hδZ
              lieDecompositionQ lieDecompositionEps s)) +
        lieCorrectionZeroVectorBundle (I := I) (M := M) g gm) +
        lieCorrectionZeroMixedConnection (I := I) (M := M) g gm g) +
        lieCorrectionZeroRiemann (I := I) (M := M) g gm := by
  rw [RicciDeTurckLowOrder.selfLow_good (I := I) (M := M)
    g g T hT hδ_lt hδ hδZ hs]
  let gm := metricPerturbationPath (I := I) g T 0 hδ hδZ s
  let Q := deTurckLieTopOrderPairingFamily (I := I) (M := M) g T hδ hδZ
    lieDecompositionQ lieDecompositionEps s
  have hlie :
      deTurckLieCoeffField (I := I) (M := M) g gm g +
          lieCorrectionZeroField (I := I) (M := M) g gm g - Q =
        (deTurckLieCovariantDerivativeArmField (I := I) (M := M) g gm g - Q) +
          lieCorrectionZeroVectorBundle (I := I) (M := M) g gm +
          lieCorrectionZeroMixedConnection (I := I) (M := M) g gm g +
          lieCorrectionZeroRiemann (I := I) (M := M) g gm := by
    calc
      _ = (deTurckLieCovariantDerivativeArmField (I := I) (M := M) g gm g - Q) +
          (lieCorrectionZeroField (I := I) (M := M) g gm g +
            deTurckLieEndoArmField (I := I) (M := M) g gm g) := by
        rw [deTurckLieCoeffField_eq_covDerivArm_add_endoArm]
        abel
      _ = _ := by
        rw [tail_base_split (I := I) (M := M) g gm g]
        simp only [sub_self, zero_add]
        abel
  calc
    _ = (-2 : ℝ) •
          RicciDeTurckLowOrder.symmetrizedRicciConnectionDifferenceLowOrderCoefficient (I := I) (M := M) g gm (s • T) +
        (deTurckLieCoeffField (I := I) (M := M) g gm g +
          lieCorrectionZeroField (I := I) (M := M) g gm g - Q) := by
      simp only [gm, Q]
      abel
    _ = _ := by
      rw [hlie]
      simp only [gm, Q]
      abel

end RicciDeTurckPairing
end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral
