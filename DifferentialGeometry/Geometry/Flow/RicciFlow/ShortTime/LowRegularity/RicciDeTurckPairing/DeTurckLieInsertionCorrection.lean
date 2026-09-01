import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegularity.RicciDeTurckPairing.MetricCoefficientBounds
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegularity.RicciDeTurckPairing.CoefficientBounds
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.CovariantJet.Naturality

noncomputable section


open Bundle Manifold MeasureTheory Set Filter DifferentialGeometry.Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Sobolev.TensorHilbert
open DifferentialGeometry.Analysis.Sobolev
  (covariantJetNormSq covariantJetNormSq_add_le covariantJetNormSq_domDomCongrSection
    covariantJetNormSq_mono covariantJetNormSq_nonneg covariantJetNormSq_reindexCoeffGen
    covariantJetNormSq_rsDomDomCongrSection deTurckLieCovariantDerivativeInsertionField
    domDomCongrSection_sub exists_covariantJetNormSq_three_operatorFieldComposition_tame_bound
    covariantJetNormSq_two_covGrad_le_three reindexCoeffGen_sub rsDomDomCongrSection
    rsDomDomCongrSection_sub rsDomDomCongrSection_toSection)
open DifferentialGeometry.Analysis.Spectral
  (ccOperatorFieldComp operatorFieldComposition_sub_left covGrad_sub lieCorrectionZeroInsertion nEndo_diff
    rsDomDomCongr toModel_rsDomDomCongr_apply)
open DifferentialGeometry.Analysis.Spectral.LieCorrectionZeroCore
  (lieCorrectionZeroInsertionFib lieCorrectionZeroInsertionFib_toModel lieCorrectionZeroNEndo)
open DifferentialGeometry.Geometry.Connection
  (slotInsertEndoCc slotInsertEndoCc_add)
open DifferentialGeometry.Geometry.Curvature
  (slotInsertEndoFib slotInsertEndoFib_apply_eval)
open DifferentialGeometry.PDE.DeTurck.RicciLinearization
open DifferentialGeometry.Analysis.Spectral.DeTurck
open DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients
open DifferentialGeometry.Analysis.Spectral.MetricRealization
open LieCorrectionZeroCore

variable
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
      [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

private noncomputable def symmetrizedSlotInsertion
    (g : SmoothRiemannianMetric I M)
    (Λ : ContMDiffSection I (E →L[ℝ] E) ∞
      (fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x)) :
    SmoothCcTensor g 2 2 :=
  let X := slotInsertEndoCc (I := I) (M := M) g 1 Λ
  X + reindexCoeffGen (I := I) (M := M) g 2 2
    (rsDomDomCongrSection (I := I) (M := M) g 2 2
      (Equiv.swap (0 : Fin 2) 1) X)
    (Equiv.swap (0 : Fin 2) 1)

private theorem covariantJetNormSq_symmetrizedSlotInsertion_le
    (g : SmoothRiemannianMetric I M)
    (Λ : ContMDiffSection I (E →L[ℝ] E) ∞
      (fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x)) :
    covariantJetNormSq (I := I) (M := M) g 2
        (symmetrizedSlotInsertion (I := I) (M := M) g Λ) ≤
      4 * (Module.finrank ℝ E : ℝ) *
        covariantJetNormSq (I := I) (M := M) g 2
          (slotInsertEndoCc (I := I) (M := M) g 0 Λ) := by
  let X : SmoothCcTensor g 2 2 :=
    slotInsertEndoCc (I := I) (M := M) g 1 Λ
  let Y : SmoothCcTensor g 2 2 :=
    reindexCoeffGen (I := I) (M := M) g 2 2
      (rsDomDomCongrSection (I := I) (M := M) g 2 2
        (Equiv.swap (0 : Fin 2) 1) X)
      (Equiv.swap (0 : Fin 2) 1)
  have hY : covariantJetNormSq (I := I) (M := M) g 2 Y =
      covariantJetNormSq (I := I) (M := M) g 2 X := by
    dsimp only [Y]
    rw [covariantJetNormSq_reindexCoeffGen, covariantJetNormSq_rsDomDomCongrSection]
  have hX : covariantJetNormSq (I := I) (M := M) g 2 X ≤
      (Module.finrank ℝ E : ℝ) *
        covariantJetNormSq (I := I) (M := M) g 2
          (slotInsertEndoCc (I := I) (M := M) g 0 Λ) := by
    simpa only [X, pow_one] using
      RicciDeTurckPairing.covariantJetNormSq_slotInsertEndoCc_le (I := I) (M := M) g 1 2 Λ
  change covariantJetNormSq (I := I) (M := M) g 2 (X + Y) ≤ _
  calc
    covariantJetNormSq (I := I) (M := M) g 2 (X + Y) ≤
        2 * (covariantJetNormSq (I := I) (M := M) g 2 X +
          covariantJetNormSq (I := I) (M := M) g 2 Y) :=
      covariantJetNormSq_add_le (I := I) (M := M) g 2 X Y
    _ = 4 * covariantJetNormSq (I := I) (M := M) g 2 X := by
      rw [hY]
      ring
    _ ≤ 4 * ((Module.finrank ℝ E : ℝ) *
        covariantJetNormSq (I := I) (M := M) g 2
          (slotInsertEndoCc (I := I) (M := M) g 0 Λ)) :=
      mul_le_mul_of_nonneg_left hX (by norm_num)
    _ = 4 * (Module.finrank ℝ E : ℝ) *
        covariantJetNormSq (I := I) (M := M) g 2
          (slotInsertEndoCc (I := I) (M := M) g 0 Λ) := by ring

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] [SigmaCompactSpace M] in
private theorem symmetrizedSlotInsertion_sub
    (g : SmoothRiemannianMetric I M)
    (Λ Γ : ContMDiffSection I (E →L[ℝ] E) ∞
      (fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x)) :
    symmetrizedSlotInsertion (I := I) (M := M) g (Λ - Γ) =
      symmetrizedSlotInsertion (I := I) (M := M) g Λ -
        symmetrizedSlotInsertion (I := I) (M := M) g Γ := by
  unfold symmetrizedSlotInsertion
  dsimp only
  rw [slotInsertEndoCc_sub, rsDomDomCongrSection_sub, reindexCoeffGen_sub]
  module

private noncomputable def deTurckLieInsertionCorrectionEndomorphism
    (g gm g_bg : SmoothRiemannianMetric I M) :
    ContMDiffSection I (E →L[ℝ] E) ∞
      (fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x) :=
  (deTurckVectorFieldCovariantDerivativeEndomorphismSection (I := I) (M := M) gm g_bg -
      deTurckVectorFieldCovariantDerivativeEndomorphismSection (I := I) (M := M) gm g) +
    endoDiffSection (I := I) (M := M) g gm g_bg

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
omit [SigmaCompactSpace M] in
private lemma deTurckLieInsertionCorrectionEndomorphism_apply
    (g gm g_bg : SmoothRiemannianMetric I M) (x : M) :
    deTurckLieInsertionCorrectionEndomorphism (I := I) (M := M) g gm g_bg x =
      (deTurckVectorFieldCovariantDerivativeEndomorphism (I := I) gm g_bg x -
        deTurckVectorFieldCovariantDerivativeEndomorphism (I := I) gm g x) +
      (lieCorrectionZeroNEndo (I := I) g gm g_bg x -
        lieCorrectionZeroNEndo (I := I) g gm g x) := by
  rw [deTurckLieInsertionCorrectionEndomorphism]
  change (_ - _) + endoDiffSection (I := I) (M := M) g gm g_bg x = _
  have hdiff : endoDiffSection (I := I) (M := M) g gm g_bg x =
      lieCorrectionZeroNEndo (I := I) g gm g_bg x -
        lieCorrectionZeroNEndo (I := I) g gm g x := by
    simp only [endoDiffSection, ContMDiffSection.coe_sub, Pi.sub_apply]
    exact (nEndo_diff (I := I) (M := M) g gm g_bg x).symm
  rw [hdiff]
  simp only [deTurckVectorFieldCovariantDerivativeEndomorphismSection_apply]

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
omit [SigmaCompactSpace M] in
private theorem deTurckLieInsertionCorrection_eq_pair
    (g gm g_bg : SmoothRiemannianMetric I M) :
    (deTurckLieCovariantDerivativeInsertionField (I := I) (M := M) g gm g_bg -
        deTurckLieCovariantDerivativeInsertionField (I := I) (M := M) g gm g) +
      (lieCorrectionZeroInsertion (I := I) (M := M) g gm g_bg -
        lieCorrectionZeroInsertion (I := I) (M := M) g gm g) =
      symmetrizedSlotInsertion (I := I) (M := M) g
        (deTurckLieInsertionCorrectionEndomorphism (I := I) (M := M) g gm g_bg) := by
  classical
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  apply ContinuousLinearMap.ext
  intro D
  apply Tensor0SSpace.toModel_injective
  apply ContinuousMultilinearMap.ext
  intro m
  let Λ := deTurckLieInsertionCorrectionEndomorphism (I := I) (M := M) g gm g_bg
  let X := slotInsertEndoCc (I := I) (M := M) g 1 Λ
  let Y := reindexCoeffGen (I := I) (M := M) g 2 2
    (rsDomDomCongrSection (I := I) (M := M) g 2 2
      (Equiv.swap (0 : Fin 2) 1) X)
    (Equiv.swap (0 : Fin 2) 1)
  have hsum :
      (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
        (X + Y).toSection x) D =
      (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
        X.toSection x) D +
      (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
        Y.toSection x) D := rfl
  change Tensor0SSpace.toModel
      ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
        ((deTurckLieCovariantDerivativeInsertionField (I := I) (M := M) g gm g_bg -
            deTurckLieCovariantDerivativeInsertionField (I := I) (M := M) g gm g) +
          (lieCorrectionZeroInsertion (I := I) (M := M) g gm g_bg -
            lieCorrectionZeroInsertion (I := I) (M := M) g gm g)).toSection x) D) m =
    Tensor0SSpace.toModel
      ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
        (X + Y).toSection x) D) m
  rw [hsum, Tensor0SSpace.toModel_add,
    add_apply]
  rw [show
      (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
        ((deTurckLieCovariantDerivativeInsertionField (I := I) (M := M) g gm g_bg -
            deTurckLieCovariantDerivativeInsertionField (I := I) (M := M) g gm g) +
          (lieCorrectionZeroInsertion (I := I) (M := M) g gm g_bg -
            lieCorrectionZeroInsertion (I := I) (M := M) g gm g)).toSection x) D =
        (deTurckLieCovariantDerivativeInsertionFib (I := I) gm g_bg x D -
          deTurckLieCovariantDerivativeInsertionFib (I := I) gm g x D) +
        (lieCorrectionZeroInsertionFib (I := I) g gm g_bg x D -
          lieCorrectionZeroInsertionFib (I := I) g gm g x D) from rfl]
  rw [Tensor0SSpace.toModel_add, add_apply,
    Tensor0SSpace.toModel_sub, sub_apply,
    Tensor0SSpace.toModel_sub, sub_apply]
  rw [deTurckLieCovariantDerivativeInsertionFib_toModel (I := I) gm g_bg x D m,
    deTurckLieCovariantDerivativeInsertionFib_toModel (I := I) gm g x D m,
    lieCorrectionZeroInsertionFib_toModel (I := I) g gm g_bg x D m,
    lieCorrectionZeroInsertionFib_toModel (I := I) g gm g x D m]
  have hX :
      (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
        X.toSection x) D =
      slotInsertEndoFib (I := I) (M := M) 2 0 x (Λ x) D := rfl
  rw [hX, slotInsertEndoFib_apply_eval]
  have hY :
      (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
        Y.toSection x) D =
      reindexCoeffFibGen (I := I) 2 2 (Equiv.swap (0 : Fin 2) 1) x
        (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
          (rsDomDomCongrSection (I := I) (M := M) g 2 2
            (Equiv.swap (0 : Fin 2) 1) X).toSection x) D := rfl
  rw [hY, reindexCoeffFibGen_apply]
  rw [show
      (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
        (rsDomDomCongrSection (I := I) (M := M) g 2 2
          (Equiv.swap (0 : Fin 2) 1) X).toSection x) =
      (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
        rsDomDomCongr (I := I) (M := M) (Equiv.swap (0 : Fin 2) 1)
          (X.toSection x)) from by
        rw [rsDomDomCongrSection_toSection]]
  rw [toModel_rsDomDomCongr_apply,
    ContinuousMultilinearMap.domDomCongr_apply]
  have hX' :
      (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
        X.toSection x)
        (Tensor0SSpace.ofModel
          (ContinuousMultilinearMap.domDomCongr
            (Equiv.swap (0 : Fin 2) 1) (Tensor0SSpace.toModel D))) =
      slotInsertEndoFib (I := I) (M := M) 2 0 x (Λ x)
        (Tensor0SSpace.ofModel
          (ContinuousMultilinearMap.domDomCongr
            (Equiv.swap (0 : Fin 2) 1) (Tensor0SSpace.toModel D))) := rfl
  rw [hX', slotInsertEndoFib_apply_eval,
    Tensor0SSpace.toModel_ofModel,
    ContinuousMultilinearMap.domDomCongr_apply]
  have harg :
      (fun k => Function.update
        (fun i => m ((Equiv.swap (0 : Fin 2) 1) i)) 0
        (tangentLinearMapToModel (Λ x)
          ((fun i => m ((Equiv.swap (0 : Fin 2) 1) i)) 0))
        ((Equiv.swap (0 : Fin 2) 1) k)) =
      Function.update m 1 (tangentLinearMapToModel (Λ x) (m 1)) := by
    funext k
    fin_cases k <;> rfl
  rw [harg]
  have hΛ := deTurckLieInsertionCorrectionEndomorphism_apply (I := I) (M := M) g gm g_bg x
  dsimp only [Λ] at hΛ ⊢
  rw [hΛ]
  have hmodel_add (A B : TangentSpace I x →L[ℝ] TangentSpace I x) :
      tangentLinearMapToModel (A + B) =
        tangentLinearMapToModel A + tangentLinearMapToModel B := by
    apply ContinuousLinearMap.ext
    intro v
    simp only [tangentLinearMapToModel_apply, add_apply, map_add]
  have hmodel_sub (A B : TangentSpace I x →L[ℝ] TangentSpace I x) :
      tangentLinearMapToModel (A - B) =
        tangentLinearMapToModel A - tangentLinearMapToModel B := by
    apply ContinuousLinearMap.ext
    intro v
    simp only [tangentLinearMapToModel_apply, sub_apply, map_sub]
  rw [hmodel_add, hmodel_sub, hmodel_sub]
  simp only [add_apply,
    sub_apply,
    ContinuousMultilinearMap.map_update_add,
    ContinuousMultilinearMap.map_update_sub]
  simp only [sub_eq_add_neg, neg_add_rev]
  ac_rfl

omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] [SigmaCompactSpace M] in
omit [I.Boundaryless] in
private theorem cometricRaiseSlot0Field_sub
    (g : SmoothRiemannianMetric I M)
    (W W' : SmoothCcTensor g 0 2) :
    cometricRaiseSlot0Field (I := I) (M := M) g 0 (W - W') =
      cometricRaiseSlot0Field (I := I) (M := M) g 0 W -
        cometricRaiseSlot0Field (I := I) (M := M) g 0 W' := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  simp only [SmoothCcTensor.toSection_sub,
    cometricRaiseSlot0Field_toSection]
  rfl

omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] [SigmaCompactSpace M] in
omit [I.Boundaryless] in
private theorem cometricRaiseSlot0Field_add
    (g : SmoothRiemannianMetric I M)
    (W W' : SmoothCcTensor g 0 2) :
    cometricRaiseSlot0Field (I := I) (M := M) g 0 (W + W') =
      cometricRaiseSlot0Field (I := I) (M := M) g 0 W +
        cometricRaiseSlot0Field (I := I) (M := M) g 0 W' := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  simp only [SmoothCcTensor.toSection_add,
    cometricRaiseSlot0Field_toSection]
  rfl

omit [SigmaCompactSpace M] in
private theorem slotInsert_deTurckLieInsertionCorrectionEndomorphism
    (g gm g_bg : SmoothRiemannianMetric I M) :
    slotInsertEndoCc (I := I) (M := M) g 0
        (deTurckLieInsertionCorrectionEndomorphism (I := I) (M := M) g gm g_bg) =
      cometricRaiseSlot0Field (I := I) (M := M) g 0
        (deTurckVectorFieldCovariantDerivativeLoweredBase (I := I) (M := M) g gm g_bg -
          deTurckVectorFieldCovariantDerivativeLoweredBase (I := I) (M := M) g gm g) := by
  rw [deTurckLieInsertionCorrectionEndomorphism, slotInsertEndoCc_add, slotInsertEndoCc_sub]
  change (deTurckVectorFieldCovariantDerivativeEndomorphismInsert (I := I) (M := M) g gm g_bg -
      deTurckVectorFieldCovariantDerivativeEndomorphismInsert (I := I) (M := M) g gm g) +
    slotInsertEndoCc (I := I) (M := M) g 0
      (endoDiffSection (I := I) (M := M) g gm g_bg) = _
  rw [endoDiffSection, slotInsertEndoCc_sub,
    deTurckVectorFieldCovariantDerivativeEndomorphismInsert_eq_cometricRaise_deTurckVectorFieldCovariantDerivativeLowered,
    deTurckVectorFieldCovariantDerivativeEndomorphismInsert_eq_cometricRaise_deTurckVectorFieldCovariantDerivativeLowered,
    connectionDifferenceDeTurckVectorFieldInsert_eq_cometricRaise,
    connectionDifferenceDeTurckVectorFieldInsert_eq_cometricRaise]
  rw [deTurckVectorFieldCovariantDerivativeLowered, deTurckVectorFieldCovariantDerivativeLowered, cometricRaiseSlot0Field_add, cometricRaiseSlot0Field_add, cometricRaiseSlot0Field_sub]
  module

omit [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
omit [I.Boundaryless] in
private theorem deTurckVectorFieldCovector_backgroundDifference_sub
    (g g_bg gT gU : SmoothRiemannianMetric I M) :
    (deTurckVectorFieldCovector (I := I) (M := M) g gT g_bg -
        deTurckVectorFieldCovector (I := I) (M := M) g gT g) -
      (deTurckVectorFieldCovector (I := I) (M := M) g gU g_bg -
        deTurckVectorFieldCovector (I := I) (M := M) g gU g) =
      ccOperatorFieldComp (I := I) (M := M) g 0 3 1
        (reindexedPureTrace (I := I) (M := M) g gT 1 (Equiv.refl _) -
          reindexedPureTrace (I := I) (M := M) g gU 1 (Equiv.refl _))
        (metricLoweredConnectionDifferenceCoefficient (I := I) g g -
          metricLoweredConnectionDifferenceCoefficient (I := I) g g_bg) := by
  rw [deTurckVectorFieldCovector_sub_eq_reindexedPureTrace_ccOperatorFieldComp (I := I) (M := M) g gT g_bg g,
    deTurckVectorFieldCovector_sub_eq_reindexedPureTrace_ccOperatorFieldComp (I := I) (M := M) g gU g_bg g]
  rw [operatorFieldComposition_sub_left]

private theorem exists_deTurckVectorFieldCovector_backgroundDifference_covariantJetNormSq_tame_bound
    (hDim : Module.finrank ℝ E = 3)
    (g g_bg : SmoothRiemannianMetric I M) :
    ∃ B : ℝ → ℝ,
      (∀ R : ℝ, 0 ≤ R → 0 ≤ B R) ∧
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
        (_hδT_le : δT ≤ (1 / 3 : ℝ)) (_hδT0 : 0 ≤ δT)
        (_hδT : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) δT)
        (_hδU_le : δU ≤ (1 / 3 : ℝ)) (_hδU0 : 0 ≤ δU)
        (_hδU : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g U) δU)
        (R A D2 D3 : ℝ),
        0 ≤ R → 0 ≤ A → 0 ≤ D2 → 0 ≤ D3 →
        covariantJetNormSq (I := I) (M := M) g 2 T ≤ R ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 2 U ≤ R ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 3 T ≤ A ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 3 U ≤ A ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 2 (T - U) ≤ D2 ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 3 (T - U) ≤ D3 ^ 2 →
      covariantJetNormSq (I := I) (M := M) g 3
          ((deTurckVectorFieldCovector (I := I) (M := M) g gT g_bg -
              deTurckVectorFieldCovector (I := I) (M := M) g gT g) -
            (deTurckVectorFieldCovector (I := I) (M := M) g gU g_bg -
              deTurckVectorFieldCovector (I := I) (M := M) g gU g)) ≤
        (B R * (D3 + D2 + A * D2)) ^ 2 := by
  obtain ⟨Bt, hBt, htrace⟩ :=
    RicciDeTurckLowOrder.exists_pureTrace_one_covariantJetNormSq_difference_bound (I := I) (M := M) hDim g
      (by norm_num : 0 ≤ (1 / 3 : ℝ)) (by norm_num : (1 / 3 : ℝ) < 1)
  obtain ⟨Ca, hCa, happ⟩ :=
    exists_covariantJetNormSq_three_operatorFieldComposition_tame_bound (I := I) (M := M) hDim g 0 3 1
  let P : SmoothCcTensor g 0 3 :=
    metricLoweredConnectionDifferenceCoefficient (I := I) g g -
      metricLoweredConnectionDifferenceCoefficient (I := I) g g_bg
  let JP2 : ℝ := covariantJetNormSq (I := I) (M := M) g 2 P
  let JP3 : ℝ := covariantJetNormSq (I := I) (M := M) g 3 P
  let Z : ℝ := Ca * (JP2 + JP3)
  let C : ℝ := Real.sqrt Z
  let B : ℝ → ℝ := fun R => C * Bt R
  have hJP2 : 0 ≤ JP2 := covariantJetNormSq_nonneg (I := I) (M := M) (m := 2) g P
  have hJP3 : 0 ≤ JP3 := covariantJetNormSq_nonneg (I := I) (M := M) (m := 3) g P
  have hZ : 0 ≤ Z := mul_nonneg hCa (add_nonneg hJP2 hJP3)
  have hCsq : C ^ 2 = Z := by
    simpa only [C] using Real.sq_sqrt hZ
  refine ⟨B, ?_, ?_⟩
  · intro R hR
    exact mul_nonneg (Real.sqrt_nonneg _) (hBt R hR)
  · intro gT gU T U hT hU hTtie hUtie
      δT δU hδT_le hδT0 hδT hδU_le hδU0 hδU
      R A D2 D3 hR hA hD2 hD3 hT2 hU2 hT3 hU3 hTU2 hTU3
    let Q : ℝ := D3 + D2 + A * D2
    let Φ : SmoothCcTensor g 3 1 :=
      reindexedPureTrace (I := I) (M := M) g gT 1 (Equiv.refl _) -
        reindexedPureTrace (I := I) (M := M) g gU 1 (Equiv.refl _)
    have hΦ3 : covariantJetNormSq (I := I) (M := M) g 3 Φ ≤
        (Bt R * Q) ^ 2 := by
      dsimp only [Φ, Q]
      rw [reindexedPureTrace_sub, covariantJetNormSq_reindexCoeffGen]
      exact htrace gT gU T U hT hU hTtie hUtie
        hδT_le hδT0 hδT hδU_le hδU0 hδU
        R A D2 D3 hR hA hD2 hD3 hT2 hU2 hT3 hU3 hTU2 hTU3
    have hΦ2 : covariantJetNormSq (I := I) (M := M) g 2 Φ ≤
        (Bt R * Q) ^ 2 :=
      (covariantJetNormSq_mono (I := I) (M := M) g (by omega : 2 ≤ 3) Φ).trans hΦ3
    rw [deTurckVectorFieldCovector_backgroundDifference_sub (I := I) (M := M) g g_bg gT gU]
    change covariantJetNormSq (I := I) (M := M) g 3
        (ccOperatorFieldComp (I := I) (M := M) g 0 3 1 Φ P) ≤
      (B R * Q) ^ 2
    calc
      covariantJetNormSq (I := I) (M := M) g 3
          (ccOperatorFieldComp (I := I) (M := M) g 0 3 1 Φ P) ≤
        Ca * (covariantJetNormSq (I := I) (M := M) g 3 Φ * JP2 +
          covariantJetNormSq (I := I) (M := M) g 2 Φ * JP3) := by
            simpa only [JP2, JP3] using happ Φ P
      _ ≤ Ca * ((Bt R * Q) ^ 2 * JP2 + (Bt R * Q) ^ 2 * JP3) := by
        apply mul_le_mul_of_nonneg_left _ hCa
        exact add_le_add
          (mul_le_mul_of_nonneg_right hΦ3 hJP2)
          (mul_le_mul_of_nonneg_right hΦ2 hJP3)
      _ = Z * (Bt R * Q) ^ 2 := by
        dsimp only [Z]
        ring
      _ = (B R * Q) ^ 2 := by
        dsimp only [B]
        calc
          Z * (Bt R * Q) ^ 2 = C ^ 2 * (Bt R * Q) ^ 2 := by rw [hCsq]
          _ = (C * Bt R * Q) ^ 2 := by ring
      _ = (B R * (D3 + D2 + A * D2)) ^ 2 := by
        simp only [Q]

omit [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
private theorem deTurckVectorFieldCovariantDerivativeLoweredBase_backgroundDifference
    (g g_bg gm : SmoothRiemannianMetric I M) :
    deTurckVectorFieldCovariantDerivativeLoweredBase (I := I) (M := M) g gm g_bg -
        deTurckVectorFieldCovariantDerivativeLoweredBase (I := I) (M := M) g gm g =
      domDomCongrSection (I := I) g (Equiv.swap (0 : Fin 2) 1)
        (covGrad (I := I) (M := M) g 0 1
          (deTurckVectorFieldCovector (I := I) (M := M) g gm g_bg -
            deTurckVectorFieldCovector (I := I) (M := M) g gm g)) := by
  unfold deTurckVectorFieldCovariantDerivativeLoweredBase
  rw [← domDomCongrSection_sub, ← covGrad_sub]

omit [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
private theorem deTurckVectorFieldCovariantDerivativeLoweredBase_backgroundDifference_sub
    (g g_bg gT gU : SmoothRiemannianMetric I M) :
    (deTurckVectorFieldCovariantDerivativeLoweredBase (I := I) (M := M) g gT g_bg -
        deTurckVectorFieldCovariantDerivativeLoweredBase (I := I) (M := M) g gT g) -
      (deTurckVectorFieldCovariantDerivativeLoweredBase (I := I) (M := M) g gU g_bg -
        deTurckVectorFieldCovariantDerivativeLoweredBase (I := I) (M := M) g gU g) =
      domDomCongrSection (I := I) g (Equiv.swap (0 : Fin 2) 1)
        (covGrad (I := I) (M := M) g 0 1
          ((deTurckVectorFieldCovector (I := I) (M := M) g gT g_bg -
              deTurckVectorFieldCovector (I := I) (M := M) g gT g) -
            (deTurckVectorFieldCovector (I := I) (M := M) g gU g_bg -
              deTurckVectorFieldCovector (I := I) (M := M) g gU g))) := by
  rw [deTurckVectorFieldCovariantDerivativeLoweredBase_backgroundDifference (I := I) (M := M) g g_bg gT,
    deTurckVectorFieldCovariantDerivativeLoweredBase_backgroundDifference (I := I) (M := M) g g_bg gU,
    ← domDomCongrSection_sub, ← covGrad_sub]

private theorem exists_deTurckVectorFieldCovariantDerivativeLoweredBase_backgroundDifference_covariantJetNormSq_tame_bound
    (hDim : Module.finrank ℝ E = 3)
    (g g_bg : SmoothRiemannianMetric I M) :
    ∃ B : ℝ → ℝ,
      (∀ R : ℝ, 0 ≤ R → 0 ≤ B R) ∧
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
        (_hδT_le : δT ≤ (1 / 3 : ℝ)) (_hδT0 : 0 ≤ δT)
        (_hδT : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) δT)
        (_hδU_le : δU ≤ (1 / 3 : ℝ)) (_hδU0 : 0 ≤ δU)
        (_hδU : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g U) δU)
        (R A D2 D3 : ℝ),
        0 ≤ R → 0 ≤ A → 0 ≤ D2 → 0 ≤ D3 →
        covariantJetNormSq (I := I) (M := M) g 2 T ≤ R ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 2 U ≤ R ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 3 T ≤ A ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 3 U ≤ A ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 2 (T - U) ≤ D2 ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 3 (T - U) ≤ D3 ^ 2 →
      covariantJetNormSq (I := I) (M := M) g 2
          ((deTurckVectorFieldCovariantDerivativeLoweredBase (I := I) (M := M) g gT g_bg -
              deTurckVectorFieldCovariantDerivativeLoweredBase (I := I) (M := M) g gT g) -
            (deTurckVectorFieldCovariantDerivativeLoweredBase (I := I) (M := M) g gU g_bg -
              deTurckVectorFieldCovariantDerivativeLoweredBase (I := I) (M := M) g gU g)) ≤
        (B R * (D3 + D2 + A * D2)) ^ 2 := by
  obtain ⟨B, hB, hω⟩ := exists_deTurckVectorFieldCovector_backgroundDifference_covariantJetNormSq_tame_bound (I := I) (M := M) hDim g g_bg
  refine ⟨B, hB, ?_⟩
  intro gT gU T U hT hU hTtie hUtie
    δT δU hδT_le hδT0 hδT hδU_le hδU0 hδU
    R A D2 D3 hR hA hD2 hD3 hT2 hU2 hT3 hU3 hTU2 hTU3
  rw [deTurckVectorFieldCovariantDerivativeLoweredBase_backgroundDifference_sub (I := I) (M := M) g g_bg gT gU, covariantJetNormSq_domDomCongrSection]
  exact (covariantJetNormSq_two_covGrad_le_three (I := I) (M := M) g
    ((deTurckVectorFieldCovector (I := I) (M := M) g gT g_bg -
        deTurckVectorFieldCovector (I := I) (M := M) g gT g) -
      (deTurckVectorFieldCovector (I := I) (M := M) g gU g_bg -
        deTurckVectorFieldCovector (I := I) (M := M) g gU g))).trans
    (hω gT gU T U hT hU hTtie hUtie
      hδT_le hδT0 hδT hδU_le hδU0 hδU
      R A D2 D3 hR hA hD2 hD3 hT2 hU2 hT3 hU3 hTU2 hTU3)

omit [NeZero (Module.finrank ℝ E)] in
private theorem covariantJetNormSq_two_cometricRaiseSlot0Field
    (g : SmoothRiemannianMetric I M) (W : SmoothCcTensor g 0 2) :
    covariantJetNormSq (I := I) (M := M) g 2
        (cometricRaiseSlot0Field (I := I) (M := M) g 0 W) =
      covariantJetNormSq (I := I) (M := M) g 2 W := by
  unfold covariantJetNormSq
  apply Finset.sum_congr rfl
  intro q _
  rw [norm_iteratedCovGrad_cometricRaiseSlot0Field_eq]


theorem exists_deTurckLieInsertionCorrection_covariantJetNormSq_tame_difference_bound
    (hDim : Module.finrank ℝ E = 3)
    (g g_bg : SmoothRiemannianMetric I M) :
    ∃ B : ℝ → ℝ,
      (∀ R : ℝ, 0 ≤ R → 0 ≤ B R) ∧
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
        (_hδT_le : δT ≤ (1 / 3 : ℝ)) (_hδT0 : 0 ≤ δT)
        (_hδT : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) δT)
        (_hδU_le : δU ≤ (1 / 3 : ℝ)) (_hδU0 : 0 ≤ δU)
        (_hδU : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g U) δU)
        (R A D2 D3 : ℝ),
        0 ≤ R → 0 ≤ A → 0 ≤ D2 → 0 ≤ D3 →
        covariantJetNormSq (I := I) (M := M) g 2 T ≤ R ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 2 U ≤ R ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 3 T ≤ A ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 3 U ≤ A ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 2 (T - U) ≤ D2 ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 3 (T - U) ≤ D3 ^ 2 →
      covariantJetNormSq (I := I) (M := M) g 2
          (((deTurckLieCovariantDerivativeInsertionField (I := I) (M := M) g gT g_bg -
                deTurckLieCovariantDerivativeInsertionField (I := I) (M := M) g gT g) +
              (lieCorrectionZeroInsertion (I := I) (M := M) g gT g_bg -
                lieCorrectionZeroInsertion (I := I) (M := M) g gT g)) -
            ((deTurckLieCovariantDerivativeInsertionField (I := I) (M := M) g gU g_bg -
                deTurckLieCovariantDerivativeInsertionField (I := I) (M := M) g gU g) +
              (lieCorrectionZeroInsertion (I := I) (M := M) g gU g_bg -
                lieCorrectionZeroInsertion (I := I) (M := M) g gU g))) ≤
        (B R * (D3 + D2 + A * D2)) ^ 2 := by
  obtain ⟨Ba, hBa, hα⟩ := exists_deTurckVectorFieldCovariantDerivativeLoweredBase_backgroundDifference_covariantJetNormSq_tame_bound (I := I) (M := M) hDim g g_bg
  let fr : ℝ := Module.finrank ℝ E
  let Z : ℝ := 4 * fr
  let C : ℝ := Real.sqrt Z
  let B : ℝ → ℝ := fun R => C * Ba R
  have hfr : 0 ≤ fr := Nat.cast_nonneg _
  have hZ : 0 ≤ Z := mul_nonneg (by norm_num) hfr
  have hCsq : C ^ 2 = Z := by
    simpa only [C] using Real.sq_sqrt hZ
  refine ⟨B, ?_, ?_⟩
  · intro R hR
    exact mul_nonneg (Real.sqrt_nonneg _) (hBa R hR)
  · intro gT gU T U hT hU hTtie hUtie
      δT δU hδT_le hδT0 hδT hδU_le hδU0 hδU
      R A D2 D3 hR hA hD2 hD3 hT2 hU2 hT3 hU3 hTU2 hTU3
    let Q : ℝ := D3 + D2 + A * D2
    let ΛT := deTurckLieInsertionCorrectionEndomorphism (I := I) (M := M) g gT g_bg
    let ΛU := deTurckLieInsertionCorrectionEndomorphism (I := I) (M := M) g gU g_bg
    let AT : SmoothCcTensor g 0 2 :=
      deTurckVectorFieldCovariantDerivativeLoweredBase (I := I) (M := M) g gT g_bg -
        deTurckVectorFieldCovariantDerivativeLoweredBase (I := I) (M := M) g gT g
    let AU : SmoothCcTensor g 0 2 :=
      deTurckVectorFieldCovariantDerivativeLoweredBase (I := I) (M := M) g gU g_bg -
        deTurckVectorFieldCovariantDerivativeLoweredBase (I := I) (M := M) g gU g
    let FT : SmoothCcTensor g 2 2 :=
      (deTurckLieCovariantDerivativeInsertionField (I := I) (M := M) g gT g_bg -
          deTurckLieCovariantDerivativeInsertionField (I := I) (M := M) g gT g) +
        (lieCorrectionZeroInsertion (I := I) (M := M) g gT g_bg -
          lieCorrectionZeroInsertion (I := I) (M := M) g gT g)
    let FU : SmoothCcTensor g 2 2 :=
      (deTurckLieCovariantDerivativeInsertionField (I := I) (M := M) g gU g_bg -
          deTurckLieCovariantDerivativeInsertionField (I := I) (M := M) g gU g) +
        (lieCorrectionZeroInsertion (I := I) (M := M) g gU g_bg -
          lieCorrectionZeroInsertion (I := I) (M := M) g gU g)
    have hFT : FT = symmetrizedSlotInsertion (I := I) (M := M) g ΛT := by
      simpa only [FT, ΛT] using
        deTurckLieInsertionCorrection_eq_pair (I := I) (M := M) g gT g_bg
    have hFU : FU = symmetrizedSlotInsertion (I := I) (M := M) g ΛU := by
      simpa only [FU, ΛU] using
        deTurckLieInsertionCorrection_eq_pair (I := I) (M := M) g gU g_bg
    have hFsub : FT - FU =
        symmetrizedSlotInsertion (I := I) (M := M) g (ΛT - ΛU) := by
      rw [hFT, hFU, symmetrizedSlotInsertion_sub]
    have hslot :
        slotInsertEndoCc (I := I) (M := M) g 0 (ΛT - ΛU) =
          cometricRaiseSlot0Field (I := I) (M := M) g 0 (AT - AU) := by
      dsimp only [ΛT, ΛU, AT, AU]
      rw [slotInsertEndoCc_sub,
        slotInsert_deTurckLieInsertionCorrectionEndomorphism (I := I) (M := M) g gT g_bg,
        slotInsert_deTurckLieInsertionCorrectionEndomorphism (I := I) (M := M) g gU g_bg,
        ← cometricRaiseSlot0Field_sub]
    have hslotJet : covariantJetNormSq (I := I) (M := M) g 2
        (slotInsertEndoCc (I := I) (M := M) g 0 (ΛT - ΛU)) =
          covariantJetNormSq (I := I) (M := M) g 2 (AT - AU) := by
      rw [hslot, covariantJetNormSq_two_cometricRaiseSlot0Field]
    have hA : covariantJetNormSq (I := I) (M := M) g 2 (AT - AU) ≤
        (Ba R * Q) ^ 2 := by
      simpa only [AT, AU, Q] using
        hα gT gU T U hT hU hTtie hUtie
          hδT_le hδT0 hδT hδU_le hδU0 hδU
          R A D2 D3 hR hA hD2 hD3 hT2 hU2 hT3 hU3 hTU2 hTU3
    change covariantJetNormSq (I := I) (M := M) g 2 (FT - FU) ≤
      (B R * Q) ^ 2
    rw [hFsub]
    calc
      covariantJetNormSq (I := I) (M := M) g 2
          (symmetrizedSlotInsertion (I := I) (M := M) g (ΛT - ΛU)) ≤
        4 * fr * covariantJetNormSq (I := I) (M := M) g 2
          (slotInsertEndoCc (I := I) (M := M) g 0 (ΛT - ΛU)) := by
            simpa only [fr] using
              covariantJetNormSq_symmetrizedSlotInsertion_le (I := I) (M := M) g (ΛT - ΛU)
      _ = 4 * fr * covariantJetNormSq (I := I) (M := M) g 2 (AT - AU) := by
        rw [hslotJet]
      _ ≤ 4 * fr * (Ba R * Q) ^ 2 :=
        mul_le_mul_of_nonneg_left hA (mul_nonneg (by norm_num) hfr)
      _ = (B R * Q) ^ 2 := by
        dsimp only [B, Z] at hCsq ⊢
        calc
          4 * fr * (Ba R * Q) ^ 2 = C ^ 2 * (Ba R * Q) ^ 2 := by
            rw [hCsq]
          _ = (C * Ba R * Q) ^ 2 := by ring

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral
