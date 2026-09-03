import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegularity.CoefficientJetBounds
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegularity.DeTurckLieFirstOrderBounds
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegularity.Uniform.ConvexJets
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegularity.FirstOrderCoefficientLipschitzBounds

noncomputable section


open Bundle Manifold MeasureTheory Set DifferentialGeometry.Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

open DifferentialGeometry.Analysis.Elliptic
open DifferentialGeometry.Analysis.Parabolic
open DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Tensor.RSTensor
open DifferentialGeometry.HCGCompactness
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.PDE.DeTurck.RicciLinearization
open DifferentialGeometry.Analysis.Spectral.MetricRealization
open DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients

private lemma two_mul_sq_add_sq_le_four_sum_sq
    (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    2 * (x ^ 2 + y ^ 2) ≤ (2 * (x + y)) ^ 2 := by
  nlinarith only [sq_nonneg x, sq_nonneg y, mul_nonneg hx hy]

variable
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
      [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private theorem domDomCongrSection_sub
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
private theorem cometricRaiseSlot0Field_sub
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

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [SigmaCompactSpace M] in
private theorem deTurckLieFirstOrderBackgroundLoweredConnectionDifference_eq_neg_lieCorrectionZeroKappa
    (g gT gB : SmoothRiemannianMetric I M) :
    deTurckLieFirstOrderBackgroundLoweredConnectionDifference (I := I) (M := M) g gT gB =
      -lieCorrectionZeroKappa (I := I) (M := M) g gT gB := by
  have h := metricConnectionDifferenceLoweredCoefficient_eq_neg_kappa
    (I := I) (M := M) g gT gB
  change lieCorrectionZeroKappa (I := I) (M := M) g gT gB =
    -deTurckLieFirstOrderBackgroundLoweredConnectionDifference (I := I) (M := M) g gT gB at h
  have hneg := congrArg Neg.neg h
  simp only [neg_neg] at hneg
  exact hneg.symm

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [SigmaCompactSpace M] in
private theorem deTurckLieFirstOrderBackgroundLoweredConnectionDifference_backgroundDifference
    (g gT gB : SmoothRiemannianMetric I M)
    (T : SmoothCcTensor g 0 2)
    (htie : ∀ (x : M) (u v : TangentSpace I x),
      gT.inner x u v =
        g.inner x u v + ccTensorBilinSymm (I := I) g T x u v) :
    deTurckLieFirstOrderBackgroundLoweredConnectionDifference (I := I) (M := M) g gT gB -
        deTurckLieFirstOrderBackgroundLoweredConnectionDifference (I := I) (M := M) g gT g =
      -lieCorrectionZeroKappa (I := I) (M := M) g g gB -
        lieCorrectionZeroPbLow (I := I) (M := M) g T g gB := by
  rw [deTurckLieFirstOrderBackgroundLoweredConnectionDifference_eq_neg_lieCorrectionZeroKappa (I := I) (M := M) g gT gB,
    deTurckLieFirstOrderBackgroundLoweredConnectionDifference_eq_neg_lieCorrectionZeroKappa (I := I) (M := M) g gT g,
    kappa_bg (I := I) (M := M) g gT gB T htie]
  module

private noncomputable def deTurckLieFirstOrderBackgroundRaisedConnectionDifference
    (g gT gB : SmoothRiemannianMetric I M) : SmoothCcTensor g 1 2 :=
  cometricRaiseSlot0Field (I := I) (M := M) g 1
    (domDomCongrSection (I := I) g lieFirstOrderRhoSlot0
      (deTurckLieFirstOrderBackgroundLoweredConnectionDifference (I := I) (M := M) g gT gB))

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
omit [I.Boundaryless] in
private theorem deTurckLieFirstOrderBackgroundRaisedConnectionDifference_backgroundDifference
    (g gT gB : SmoothRiemannianMetric I M)
    (T : SmoothCcTensor g 0 2)
    (htie : ∀ (x : M) (u v : TangentSpace I x),
      gT.inner x u v =
        g.inner x u v + ccTensorBilinSymm (I := I) g T x u v) :
    deTurckLieFirstOrderBackgroundRaisedConnectionDifference (I := I) (M := M) g gT gB -
        deTurckLieFirstOrderBackgroundRaisedConnectionDifference (I := I) (M := M) g gT g =
      cometricRaiseSlot0Field (I := I) (M := M) g 1
        (domDomCongrSection (I := I) g lieFirstOrderRhoSlot0
          (-lieCorrectionZeroKappa (I := I) (M := M) g g gB -
            lieCorrectionZeroPbLow (I := I) (M := M) g T g gB)) := by
  simp only [deTurckLieFirstOrderBackgroundRaisedConnectionDifference]
  rw [← cometricRaiseSlot0Field_sub, ← domDomCongrSection_sub,
    deTurckLieFirstOrderBackgroundLoweredConnectionDifference_backgroundDifference (I := I) (M := M) g gT gB T htie]

private noncomputable def deTurckLieFirstOrderBackgroundCoefficientDifference
    (g gT gB : SmoothRiemannianMetric I M) : SmoothCcTensor g 1 2 :=
  deTurckLieFirstOrderBackgroundCoefficient (I := I) (M := M) g gT gB -
    deTurckLieFirstOrderBackgroundCoefficient (I := I) (M := M) g gT g

omit [NeZero (Module.finrank ℝ E)] in
omit [I.Boundaryless] [SigmaCompactSpace M] in
private theorem deTurckLieFirstOrderBackgroundCoefficientDifference_eq_comp
    (g gT gB : SmoothRiemannianMetric I M) :
    deTurckLieFirstOrderBackgroundCoefficientDifference (I := I) (M := M) g gT gB =
      ccOperatorFieldComp (I := I) (M := M) g 1 1 2
        (deTurckLieFirstOrderBackgroundRaisedConnectionDifference (I := I) (M := M) g gT gB -
          deTurckLieFirstOrderBackgroundRaisedConnectionDifference (I := I) (M := M) g gT g)
        (sharpFlatEndoCc (I := I) g gT) := by
  simp only [deTurckLieFirstOrderBackgroundCoefficientDifference, deTurckLieFirstOrderBackgroundRaisedConnectionDifference, deTurckLieFirstOrderBackgroundCoefficient, lieFirstOrderRhoSlot0]
  rw [operatorFieldComposition_sub_left]

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
omit [I.Boundaryless] in
private theorem deTurckLieFirstOrderBackgroundRaisedConnectionDifference_difference
    (g gT gU gB : SmoothRiemannianMetric I M)
    (T U : SmoothCcTensor g 0 2)
    (hTtie : ∀ (x : M) (u v : TangentSpace I x),
      gT.inner x u v =
        g.inner x u v + ccTensorBilinSymm (I := I) g T x u v)
    (hUtie : ∀ (x : M) (u v : TangentSpace I x),
      gU.inner x u v =
        g.inner x u v + ccTensorBilinSymm (I := I) g U x u v) :
    (deTurckLieFirstOrderBackgroundRaisedConnectionDifference (I := I) (M := M) g gT gB -
        deTurckLieFirstOrderBackgroundRaisedConnectionDifference (I := I) (M := M) g gT g) -
      (deTurckLieFirstOrderBackgroundRaisedConnectionDifference (I := I) (M := M) g gU gB -
        deTurckLieFirstOrderBackgroundRaisedConnectionDifference (I := I) (M := M) g gU g) =
      cometricRaiseSlot0Field (I := I) (M := M) g 1
        (domDomCongrSection (I := I) g lieFirstOrderRhoSlot0
          (-lieCorrectionZeroPbLow (I := I) (M := M) g (T - U) g gB)) := by
  rw [deTurckLieFirstOrderBackgroundRaisedConnectionDifference_backgroundDifference (I := I) (M := M) g gT gB T hTtie,
    deTurckLieFirstOrderBackgroundRaisedConnectionDifference_backgroundDifference (I := I) (M := M) g gU gB U hUtie]
  rw [← cometricRaiseSlot0Field_sub, ← domDomCongrSection_sub]
  congr 2
  rw [pbLow_sub (I := I) (M := M) g T U g gB]
  module

omit [NeZero (Module.finrank ℝ E)] in
omit [I.Boundaryless] [SigmaCompactSpace M] in
private theorem deTurckLieFirstOrderBackgroundCoefficientDifference_difference_decomposition
    (g gT gU gB : SmoothRiemannianMetric I M) :
    deTurckLieFirstOrderBackgroundCoefficientDifference (I := I) (M := M) g gT gB -
        deTurckLieFirstOrderBackgroundCoefficientDifference (I := I) (M := M) g gU gB =
      ccOperatorFieldComp (I := I) (M := M) g 1 1 2
          (deTurckLieFirstOrderBackgroundRaisedConnectionDifference (I := I) (M := M) g gT gB -
            deTurckLieFirstOrderBackgroundRaisedConnectionDifference (I := I) (M := M) g gT g)
          (sharpFlatEndoCc (I := I) g gT -
            sharpFlatEndoCc (I := I) g gU) +
        ccOperatorFieldComp (I := I) (M := M) g 1 1 2
          ((deTurckLieFirstOrderBackgroundRaisedConnectionDifference (I := I) (M := M) g gT gB -
              deTurckLieFirstOrderBackgroundRaisedConnectionDifference (I := I) (M := M) g gT g) -
            (deTurckLieFirstOrderBackgroundRaisedConnectionDifference (I := I) (M := M) g gU gB -
              deTurckLieFirstOrderBackgroundRaisedConnectionDifference (I := I) (M := M) g gU g))
          (sharpFlatEndoCc (I := I) g gU) := by
  let AT : SmoothCcTensor g 1 2 :=
    deTurckLieFirstOrderBackgroundRaisedConnectionDifference (I := I) (M := M) g gT gB -
      deTurckLieFirstOrderBackgroundRaisedConnectionDifference (I := I) (M := M) g gT g
  let AU : SmoothCcTensor g 1 2 :=
    deTurckLieFirstOrderBackgroundRaisedConnectionDifference (I := I) (M := M) g gU gB -
      deTurckLieFirstOrderBackgroundRaisedConnectionDifference (I := I) (M := M) g gU g
  let ST : SmoothCcTensor g 1 1 := sharpFlatEndoCc (I := I) g gT
  let SU : SmoothCcTensor g 1 1 := sharpFlatEndoCc (I := I) g gU
  rw [deTurckLieFirstOrderBackgroundCoefficientDifference_eq_comp (I := I) (M := M) g gT gB,
    deTurckLieFirstOrderBackgroundCoefficientDifference_eq_comp (I := I) (M := M) g gU gB]
  change ccOperatorFieldComp (I := I) (M := M) g 1 1 2 AT ST -
      ccOperatorFieldComp (I := I) (M := M) g 1 1 2 AU SU =
    ccOperatorFieldComp (I := I) (M := M) g 1 1 2 AT (ST - SU) +
      ccOperatorFieldComp (I := I) (M := M) g 1 1 2 (AT - AU) SU
  have hR : ccOperatorFieldComp (I := I) (M := M) g 1 1 2 AT (ST - SU) =
      ccOperatorFieldComp (I := I) (M := M) g 1 1 2 AT ST -
        ccOperatorFieldComp (I := I) (M := M) g 1 1 2 AT SU := by
    rw [operatorFieldComposition_sub_right]
  have hL : ccOperatorFieldComp (I := I) (M := M) g 1 1 2 (AT - AU) SU =
      ccOperatorFieldComp (I := I) (M := M) g 1 1 2 AT SU -
        ccOperatorFieldComp (I := I) (M := M) g 1 1 2 AU SU := by
    rw [operatorFieldComposition_sub_left]
  rw [hR, hL]
  module

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
private theorem covariantJetNormSq_add_le
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
private theorem covariantJetNormSq_smul
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

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
private theorem covariantJetNormSq_neg
    (g : SmoothRiemannianMetric I M) {r s : ℕ} (m : ℕ)
    (S : SmoothCcTensor g r s) :
    covariantJetNormSq (I := I) (M := M) g m (-S) =
      covariantJetNormSq (I := I) (M := M) g m S := by
  simpa only [neg_one_smul, neg_one_sq, one_mul] using
    covariantJetNormSq_smul (I := I) (M := M) g m (-1 : ℝ) S

omit [NeZero (Module.finrank ℝ E)] in
private theorem covariantJetNormSq_two_domDomCongrSection
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
private theorem covariantJetNormSq_two_cometricRaise_domDomCongrSection
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
      covariantJetNormSq_two_domDomCongrSection (I := I) (M := M) g ρ S

omit [NeZero (Module.finrank ℝ E)] in
private theorem covariantJetNormSq_two_neg_lieCorrectionZeroKappa_base_eq
    (g gB : SmoothRiemannianMetric I M) :
    covariantJetNormSq (I := I) (M := M) g 2
        (-lieCorrectionZeroKappa (I := I) (M := M) g g gB) =
      covariantJetNormSq (I := I) (M := M) g 2
        (connectionDifferenceSection (I := I) gB g) := by
  rw [kappa_base_neg (I := I) (M := M) g gB]
  simp only [neg_neg]
  unfold covariantJetNormSq
  apply Finset.sum_congr rfl
  intro i _
  rw [SmoothCcTensor.norm_def, SmoothCcTensor.norm_def,
    tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs
      (I := I) (M := M) g 0 (3 + i),
    tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs
      (I := I) (M := M) g 1 (2 + i)]
  exact MeasureTheory.integral_congr_ae
    (Filter.Eventually.of_forall fun x =>
      metricLoweredConnectionDifferenceCoefficient_fiber_norm_sq_eq (I := I) (M := M) g gB i x)

private theorem exists_deTurckLieFirstOrderBackgroundRaisedConnectionDifference_pairing_second_order_bound
    (hDim : Module.finrank ℝ E = 3)
    (g gB : SmoothRiemannianMetric I M) :
    ∃ ρ L D : ℝ, 0 < ρ ∧ 0 ≤ L ∧ 0 ≤ D ∧
      ∀ (gT gU : SmoothRiemannianMetric I M)
        (T U : SmoothCcTensor g 0 2)
        (_hTtie : ∀ (x : M) (u v : TangentSpace I x),
          gT.inner x u v =
            g.inner x u v + ccTensorBilinSymm (I := I) g T x u v)
        (_hUtie : ∀ (x : M) (u v : TangentSpace I x),
          gU.inner x u v =
            g.inner x u v + ccTensorBilinSymm (I := I) g U x u v),
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ ≤ ρ →
      covariantJetNormSq (I := I) (M := M) g 2
          (deTurckLieFirstOrderBackgroundRaisedConnectionDifference (I := I) (M := M) g gT gB -
            deTurckLieFirstOrderBackgroundRaisedConnectionDifference (I := I) (M := M) g gT g) ≤ L ^ 2 ∧
        covariantJetNormSq (I := I) (M := M) g 2
          ((deTurckLieFirstOrderBackgroundRaisedConnectionDifference (I := I) (M := M) g gT gB -
              deTurckLieFirstOrderBackgroundRaisedConnectionDifference (I := I) (M := M) g gT g) -
            (deTurckLieFirstOrderBackgroundRaisedConnectionDifference (I := I) (M := M) g gU gB -
              deTurckLieFirstOrderBackgroundRaisedConnectionDifference (I := I) (M := M) g gU g)) ≤
          (D * ‖ccTensorToHs (I := I) (M := M) g 2
            (2 : ℝ) (T - U)‖) ^ 2 := by
  obtain ⟨Kp, hKp, hpb⟩ :=
    pbLow_h2_mul (I := I) (M := M) hDim g gB
  obtain ⟨Ch, hCh, hhs⟩ :=
    hs2_low2 (I := I) (M := M) g 2
  let F : SmoothCcTensor g 0 3 :=
    -lieCorrectionZeroKappa (I := I) (M := M) g g gB
  let F0 : ℝ := Real.sqrt (covariantJetNormSq (I := I) (M := M) g 2 F)
  let D : ℝ := Kp * Ch
  let L : ℝ := 2 * (F0 + D)
  have hF0 : 0 ≤ F0 := Real.sqrt_nonneg _
  have hF0sq : F0 ^ 2 = covariantJetNormSq (I := I) (M := M) g 2 F := by
    simpa only [F0] using Real.sq_sqrt
      (Finset.sum_nonneg fun _ _ => sq_nonneg _)
  have hD : 0 ≤ D := mul_nonneg hKp hCh
  have hL : 0 ≤ L :=
    mul_nonneg (by norm_num) (add_nonneg hF0 hD)
  refine ⟨1, L, D, by norm_num, hL, hD, ?_⟩
  intro gT gU T U hTtie hUtie hTHs
  let N : ℝ :=
    ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) (T - U)‖
  let LT : SmoothCcTensor g 1 2 :=
    deTurckLieFirstOrderBackgroundRaisedConnectionDifference (I := I) (M := M) g gT gB -
      deTurckLieFirstOrderBackgroundRaisedConnectionDifference (I := I) (M := M) g gT g
  let LU : SmoothCcTensor g 1 2 :=
    deTurckLieFirstOrderBackgroundRaisedConnectionDifference (I := I) (M := M) g gU gB -
      deTurckLieFirstOrderBackgroundRaisedConnectionDifference (I := I) (M := M) g gU g
  let PbT : SmoothCcTensor g 0 3 :=
    lieCorrectionZeroPbLow (I := I) (M := M) g T g gB
  have hN : 0 ≤ N := norm_nonneg _
  have hT2 : covariantJetNormSq (I := I) (M := M) g 2 T ≤ Ch ^ 2 := by
    calc
      covariantJetNormSq (I := I) (M := M) g 2 T ≤
          (Ch * ‖ccTensorToHs (I := I) (M := M) g 2
            (2 : ℝ) T‖) ^ 2 := by
        simpa only [covariantJetNormSq, Nat.reduceAdd] using hhs T
      _ ≤ (Ch * 1) ^ 2 :=
        pow_le_pow_left₀
          (mul_nonneg hCh (norm_nonneg _))
          (mul_le_mul_of_nonneg_left hTHs hCh) 2
      _ = Ch ^ 2 := by rw [mul_one]
  have hTU2 : covariantJetNormSq (I := I) (M := M) g 2 (T - U) ≤
      (Ch * N) ^ 2 := by
    simpa only [covariantJetNormSq, Nat.reduceAdd, N] using hhs (T - U)
  have hPbT : covariantJetNormSq (I := I) (M := M) g 2 PbT ≤ D ^ 2 := by
    simpa only [PbT, D] using hpb T Ch hCh hT2
  have hLT : covariantJetNormSq (I := I) (M := M) g 2 LT ≤ L ^ 2 := by
    rw [show LT =
        cometricRaiseSlot0Field (I := I) (M := M) g 1
          (domDomCongrSection (I := I) g lieFirstOrderRhoSlot0 (F - PbT)) by
      simpa only [LT, F, PbT] using
        deTurckLieFirstOrderBackgroundRaisedConnectionDifference_backgroundDifference (I := I) (M := M) g gT gB T hTtie]
    rw [covariantJetNormSq_two_cometricRaise_domDomCongrSection (I := I) (M := M) g lieFirstOrderRhoSlot0 (F - PbT)]
    calc
      covariantJetNormSq (I := I) (M := M) g 2 (F - PbT) =
          covariantJetNormSq (I := I) (M := M) g 2 (F + -PbT) := by
        rw [sub_eq_add_neg]
      _ ≤ 2 * (covariantJetNormSq (I := I) (M := M) g 2 F +
          covariantJetNormSq (I := I) (M := M) g 2 (-PbT)) :=
        covariantJetNormSq_add_le (I := I) (M := M) g 2 F (-PbT)
      _ = 2 * (F0 ^ 2 + covariantJetNormSq (I := I) (M := M) g 2 PbT) := by
        rw [covariantJetNormSq_neg (I := I) (M := M) g 2 PbT, hF0sq]
      _ ≤ 2 * (F0 ^ 2 + D ^ 2) :=
        mul_le_mul_of_nonneg_left (add_le_add le_rfl hPbT) (by norm_num)
      _ ≤ L ^ 2 := by
        simpa only [L] using two_mul_sq_add_sq_le_four_sum_sq F0 D hF0 hD
  have hPbD : covariantJetNormSq (I := I) (M := M) g 2
      (lieCorrectionZeroPbLow (I := I) (M := M) g (T - U) g gB) ≤
      (D * N) ^ 2 := by
    simpa only [D, mul_assoc] using hpb (T - U) (Ch * N)
      (mul_nonneg hCh hN) hTU2
  have hLD : covariantJetNormSq (I := I) (M := M) g 2 (LT - LU) ≤
      (D * N) ^ 2 := by
    rw [show LT - LU =
        cometricRaiseSlot0Field (I := I) (M := M) g 1
          (domDomCongrSection (I := I) g lieFirstOrderRhoSlot0
            (-lieCorrectionZeroPbLow (I := I) (M := M) g (T - U) g gB)) by
      simpa only [LT, LU] using
        deTurckLieFirstOrderBackgroundRaisedConnectionDifference_difference (I := I) (M := M) g gT gU gB T U hTtie hUtie]
    rw [covariantJetNormSq_two_cometricRaise_domDomCongrSection (I := I) (M := M) g lieFirstOrderRhoSlot0,
      covariantJetNormSq_neg (I := I) (M := M) g 2]
    exact hPbD
  simpa only [LT, LU, N] using And.intro hLT hLD

private theorem exists_sharpFlatEndoCc_pairing_second_order_bounds
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M)
    {δ₀ : ℝ} (hδ₀0 : 0 ≤ δ₀) (hδ₀ : δ₀ < 1) :
    ∃ ρ S C : ℝ, 0 < ρ ∧ 0 ≤ S ∧ 0 ≤ C ∧
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
          (sharpFlatEndoCc (I := I) g gT) ≤ S ^ 2 ∧
        covariantJetNormSq (I := I) (M := M) g 2
          (sharpFlatEndoCc (I := I) g gU) ≤ S ^ 2 ∧
        covariantJetNormSq (I := I) (M := M) g 2
          (sharpFlatEndoCc (I := I) g gT -
            sharpFlatEndoCc (I := I) g gU) ≤
          (C * ‖ccTensorToHs (I := I) (M := M) g 2
            (2 : ℝ) (T - U)‖) ^ 2 := by
  obtain ⟨ρs, Cs, hρs, hCs, hsharpPair⟩ :=
    sharp_pair_h2 (I := I) (M := M) hDim g hδ₀0 hδ₀
  obtain ⟨Ks, hKs, hsharpBdd⟩ :=
    sharp_h2_low (I := I) (M := M) g hδ₀0 hδ₀
  obtain ⟨Ch, hCh, hhs⟩ :=
    hs2_low2 (I := I) (M := M) g 2
  let ρ : ℝ := min ρs 1
  let S0 : ℝ := Ks * (1 + Ch ^ 2)
  let S : ℝ := Real.sqrt S0
  have hρ : 0 < ρ := lt_min hρs (by norm_num)
  have hS0 : 0 ≤ S0 :=
    mul_nonneg hKs (add_nonneg (by norm_num) (sq_nonneg Ch))
  have hS : 0 ≤ S := Real.sqrt_nonneg _
  have hSsq : S ^ 2 = S0 := by
    simpa only [S] using Real.sq_sqrt hS0
  refine ⟨ρ, S, Cs, hρ, hS, hCs, ?_⟩
  intro gT gU T U hT hU hTtie hUtie
    δT δU hδT_le hδT0 hδT hδU_le hδU0 hδU hTHs hUHs
  have hTHss : ‖ccTensorToHs (I := I) (M := M) g 2
      (2 : ℝ) T‖ ≤ ρs := hTHs.trans (min_le_left _ _)
  have hUHss : ‖ccTensorToHs (I := I) (M := M) g 2
      (2 : ℝ) U‖ ≤ ρs := hUHs.trans (min_le_left _ _)
  have hTHs1 : ‖ccTensorToHs (I := I) (M := M) g 2
      (2 : ℝ) T‖ ≤ 1 := hTHs.trans (min_le_right _ _)
  have hUHs1 : ‖ccTensorToHs (I := I) (M := M) g 2
      (2 : ℝ) U‖ ≤ 1 := hUHs.trans (min_le_right _ _)
  have hT2 : covariantJetNormSq (I := I) (M := M) g 2 T ≤ Ch ^ 2 := by
    calc
      covariantJetNormSq (I := I) (M := M) g 2 T ≤
          (Ch * ‖ccTensorToHs (I := I) (M := M) g 2
            (2 : ℝ) T‖) ^ 2 := by
        simpa only [covariantJetNormSq, Nat.reduceAdd] using hhs T
      _ ≤ (Ch * 1) ^ 2 :=
        pow_le_pow_left₀
          (mul_nonneg hCh (norm_nonneg _))
          (mul_le_mul_of_nonneg_left hTHs1 hCh) 2
      _ = Ch ^ 2 := by rw [mul_one]
  have hU2 : covariantJetNormSq (I := I) (M := M) g 2 U ≤ Ch ^ 2 := by
    calc
      covariantJetNormSq (I := I) (M := M) g 2 U ≤
          (Ch * ‖ccTensorToHs (I := I) (M := M) g 2
            (2 : ℝ) U‖) ^ 2 := by
        simpa only [covariantJetNormSq, Nat.reduceAdd] using hhs U
      _ ≤ (Ch * 1) ^ 2 :=
        pow_le_pow_left₀
          (mul_nonneg hCh (norm_nonneg _))
          (mul_le_mul_of_nonneg_left hUHs1 hCh) 2
      _ = Ch ^ 2 := by rw [mul_one]
  have hST : covariantJetNormSq (I := I) (M := M) g 2
      (sharpFlatEndoCc (I := I) g gT) ≤ S ^ 2 := by
    calc
      covariantJetNormSq (I := I) (M := M) g 2
          (sharpFlatEndoCc (I := I) g gT) ≤
          Ks * (1 + covariantJetNormSq (I := I) (M := M) g 2 T) :=
        hsharpBdd gT T hT hTtie hδT_le hδT0 hδT
      _ ≤ S0 := by
        dsimp only [S0]
        exact mul_le_mul_of_nonneg_left (add_le_add le_rfl hT2) hKs
      _ = S ^ 2 := hSsq.symm
  have hSU : covariantJetNormSq (I := I) (M := M) g 2
      (sharpFlatEndoCc (I := I) g gU) ≤ S ^ 2 := by
    calc
      covariantJetNormSq (I := I) (M := M) g 2
          (sharpFlatEndoCc (I := I) g gU) ≤
          Ks * (1 + covariantJetNormSq (I := I) (M := M) g 2 U) :=
        hsharpBdd gU U hU hUtie hδU_le hδU0 hδU
      _ ≤ S0 := by
        dsimp only [S0]
        exact mul_le_mul_of_nonneg_left (add_le_add le_rfl hU2) hKs
      _ = S ^ 2 := hSsq.symm
  have hSD : covariantJetNormSq (I := I) (M := M) g 2
      (sharpFlatEndoCc (I := I) g gT -
        sharpFlatEndoCc (I := I) g gU) ≤
      (Cs * ‖ccTensorToHs (I := I) (M := M) g 2
        (2 : ℝ) (T - U)‖) ^ 2 := by
    exact hsharpPair gT gU T U hT hU hTtie hUtie
      hδT_le hδT0 hδT hδU_le hδU0 hδU hTHss hUHss
  exact ⟨hST, hSU, hSD⟩

theorem exists_deTurckLieFirstOrderBackgroundCoefficient_difference_pairing_secondOrder_bound
    (hDim : Module.finrank ℝ E = 3)
    (g gB : SmoothRiemannianMetric I M)
    {δ₀ : ℝ} (hδ₀0 : 0 ≤ δ₀) (hδ₀ : δ₀ < 1) :
    ∃ ρ P B : ℝ,
      0 < ρ ∧ 0 ≤ P ∧ 0 ≤ B ∧
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
      let N := ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) (T - U)‖
      covariantJetNormSq (I := I) (M := M) g 2
          (deTurckLieFirstOrderBackgroundCoefficient (I := I) (M := M) g gT gB -
            deTurckLieFirstOrderBackgroundCoefficient (I := I) (M := M) g gT g) ≤ P ^ 2 ∧
        covariantJetNormSq (I := I) (M := M) g 2
          ((deTurckLieFirstOrderBackgroundCoefficient (I := I) (M := M) g gT gB -
              deTurckLieFirstOrderBackgroundCoefficient (I := I) (M := M) g gT g) -
            (deTurckLieFirstOrderBackgroundCoefficient (I := I) (M := M) g gU gB -
              deTurckLieFirstOrderBackgroundCoefficient (I := I) (M := M) g gU g)) ≤
          (B * N) ^ 2 := by
  obtain ⟨ρl, L, D, hρl, hL, hD, hleft⟩ :=
    exists_deTurckLieFirstOrderBackgroundRaisedConnectionDifference_pairing_second_order_bound (I := I) (M := M) hDim g gB
  obtain ⟨ρs, S, C, hρs, hS, hC, hsharp⟩ :=
    exists_sharpFlatEndoCc_pairing_second_order_bounds (I := I) (M := M) hDim g hδ₀0 hδ₀
  obtain ⟨Ca, hCa, happ⟩ :=
    operator_field_composition_h2_h2_to_h2_bound (I := I) (M := M) hDim g 1 1 2
  let ρ : ℝ := min ρl ρs
  let P : ℝ := Ca * L * S
  let B : ℝ := 2 * (Ca * L * C + Ca * D * S)
  have hρ : 0 < ρ := lt_min hρl hρs
  have hP : 0 ≤ P := mul_nonneg (mul_nonneg hCa hL) hS
  have hB : 0 ≤ B :=
    mul_nonneg (by norm_num)
      (add_nonneg
        (mul_nonneg (mul_nonneg hCa hL) hC)
        (mul_nonneg (mul_nonneg hCa hD) hS))
  refine ⟨ρ, P, B, hρ, hP, hB, ?_⟩
  intro gT gU T U hT hU hTtie hUtie
    δT δU hδT_le hδT0 hδT hδU_le hδU0 hδU hTHs hUHs
  dsimp only
  let N : ℝ :=
    ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) (T - U)‖
  let LT : SmoothCcTensor g 1 2 :=
    deTurckLieFirstOrderBackgroundRaisedConnectionDifference (I := I) (M := M) g gT gB -
      deTurckLieFirstOrderBackgroundRaisedConnectionDifference (I := I) (M := M) g gT g
  let LU : SmoothCcTensor g 1 2 :=
    deTurckLieFirstOrderBackgroundRaisedConnectionDifference (I := I) (M := M) g gU gB -
      deTurckLieFirstOrderBackgroundRaisedConnectionDifference (I := I) (M := M) g gU g
  let ST : SmoothCcTensor g 1 1 := sharpFlatEndoCc (I := I) g gT
  let SU : SmoothCcTensor g 1 1 := sharpFlatEndoCc (I := I) g gU
  have hN : 0 ≤ N := norm_nonneg _
  have hTHsl : ‖ccTensorToHs (I := I) (M := M) g 2
      (2 : ℝ) T‖ ≤ ρl := hTHs.trans (min_le_left _ _)
  have hTHss : ‖ccTensorToHs (I := I) (M := M) g 2
      (2 : ℝ) T‖ ≤ ρs := hTHs.trans (min_le_right _ _)
  have hUHss : ‖ccTensorToHs (I := I) (M := M) g 2
      (2 : ℝ) U‖ ≤ ρs := hUHs.trans (min_le_right _ _)
  obtain ⟨hLT, hLD⟩ := hleft gT gU T U hTtie hUtie hTHsl
  obtain ⟨hST, hSU, hSD⟩ :=
    hsharp gT gU T U hT hU hTtie hUtie
      hδT_le hδT0 hδT hδU_le hδU0 hδU hTHss hUHss
  let V1 : SmoothCcTensor g 1 2 :=
    ccOperatorFieldComp (I := I) (M := M) g 1 1 2 LT (ST - SU)
  let V2 : SmoothCcTensor g 1 2 :=
    ccOperatorFieldComp (I := I) (M := M) g 1 1 2 (LT - LU) SU
  let Z1 : ℝ := Ca * L * (C * N)
  let Z2 : ℝ := Ca * (D * N) * S
  have hZ1 : 0 ≤ Z1 :=
    mul_nonneg (mul_nonneg hCa hL) (mul_nonneg hC hN)
  have hZ2 : 0 ≤ Z2 :=
    mul_nonneg (mul_nonneg hCa (mul_nonneg hD hN)) hS
  have hPsiT : covariantJetNormSq (I := I) (M := M) g 2
      (deTurckLieFirstOrderBackgroundCoefficient (I := I) (M := M) g gT gB -
        deTurckLieFirstOrderBackgroundCoefficient (I := I) (M := M) g gT g) ≤ P ^ 2 := by
    change covariantJetNormSq (I := I) (M := M) g 2
      (deTurckLieFirstOrderBackgroundCoefficientDifference (I := I) (M := M) g gT gB) ≤ P ^ 2
    rw [deTurckLieFirstOrderBackgroundCoefficientDifference_eq_comp (I := I) (M := M) g gT gB]
    simpa only [LT, ST, P] using
      happ LT ST L S hL hS hLT hST
  have hV1 : covariantJetNormSq (I := I) (M := M) g 2 V1 ≤ Z1 ^ 2 := by
    simpa only [V1, Z1] using
      happ LT (ST - SU) L (C * N) hL
        (mul_nonneg hC hN) hLT hSD
  have hV2 : covariantJetNormSq (I := I) (M := M) g 2 V2 ≤ Z2 ^ 2 := by
    simpa only [V2, Z2] using
      happ (LT - LU) SU (D * N) S
        (mul_nonneg hD hN) hS hLD hSU
  refine ⟨hPsiT, ?_⟩
  change covariantJetNormSq (I := I) (M := M) g 2
    (deTurckLieFirstOrderBackgroundCoefficientDifference (I := I) (M := M) g gT gB -
      deTurckLieFirstOrderBackgroundCoefficientDifference (I := I) (M := M) g gU gB) ≤ (B * N) ^ 2
  rw [deTurckLieFirstOrderBackgroundCoefficientDifference_difference_decomposition (I := I) (M := M) g gT gU gB]
  change covariantJetNormSq (I := I) (M := M) g 2 (V1 + V2) ≤ (B * N) ^ 2
  calc
    covariantJetNormSq (I := I) (M := M) g 2 (V1 + V2) ≤
        2 * (covariantJetNormSq (I := I) (M := M) g 2 V1 +
          covariantJetNormSq (I := I) (M := M) g 2 V2) :=
      covariantJetNormSq_add_le (I := I) (M := M) g 2 V1 V2
    _ ≤ 2 * (Z1 ^ 2 + Z2 ^ 2) :=
      mul_le_mul_of_nonneg_left (add_le_add hV1 hV2) (by norm_num)
    _ ≤ (2 * (Z1 + Z2)) ^ 2 :=
      two_mul_sq_add_sq_le_four_sum_sq Z1 Z2 hZ1 hZ2
    _ = (B * N) ^ 2 := by
      simp only [Z1, Z2, B]
      ring

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] [SigmaCompactSpace M] in
private theorem slotExtend_add
    (g : SmoothRiemannianMetric I M) {r s : ℕ}
    (P Q : SmoothCcTensor g r s) :
    slotExtend (I := I) (M := M) g r s (P + Q) =
      slotExtend (I := I) (M := M) g r s P +
        slotExtend (I := I) (M := M) g r s Q := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  apply ContinuousLinearMap.ext
  intro D
  rfl

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] [SigmaCompactSpace M] in
private theorem reindexCoeffGen_add
    (g : SmoothRiemannianMetric I M) {r s : ℕ}
    (P Q : SmoothCcTensor g r s) (σ : Equiv.Perm (Fin r)) :
    reindexCoeffGen (I := I) (M := M) g r s (P + Q) σ =
      reindexCoeffGen (I := I) (M := M) g r s P σ +
        reindexCoeffGen (I := I) (M := M) g r s Q σ := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  apply ContinuousLinearMap.ext
  intro D
  rfl

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] [SigmaCompactSpace M] in
private theorem reindexCoeffGen_sub
    (g : SmoothRiemannianMetric I M) {r s : ℕ}
    (P Q : SmoothCcTensor g r s) (σ : Equiv.Perm (Fin r)) :
    reindexCoeffGen (I := I) (M := M) g r s (P - Q) σ =
      reindexCoeffGen (I := I) (M := M) g r s P σ -
        reindexCoeffGen (I := I) (M := M) g r s Q σ := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  apply ContinuousLinearMap.ext
  intro D
  rfl

omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] [SigmaCompactSpace M] in
omit [I.Boundaryless] in
private theorem deTurckLieTraceCoeffPiece_add
    (g gm : SmoothRiemannianMetric I M)
    (σ : Equiv.Perm (Fin 4)) (ρ : Equiv.Perm (Fin 3))
    (P Q : SmoothCcTensor g 1 2) :
    deTurckLieTraceCoeffPiece (I := I) (M := M) g gm σ ρ (P + Q) =
      deTurckLieTraceCoeffPiece (I := I) (M := M) g gm σ ρ P +
        deTurckLieTraceCoeffPiece (I := I) (M := M) g gm σ ρ Q := by
  unfold deTurckLieTraceCoeffPiece
  rw [slotExtend_add (I := I) (M := M), slotExtend_add (I := I) (M := M),
    operatorFieldComposition_add_right, reindexCoeffGen_add (I := I) (M := M)]

omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
omit [I.Boundaryless] [SigmaCompactSpace M] in
private theorem deTurckLieTraceCoeffPiece_sub
    (g gm : SmoothRiemannianMetric I M)
    (σ : Equiv.Perm (Fin 4)) (ρ : Equiv.Perm (Fin 3))
    (P Q : SmoothCcTensor g 1 2) :
    deTurckLieTraceCoeffPiece (I := I) (M := M) g gm σ ρ (P - Q) =
      deTurckLieTraceCoeffPiece (I := I) (M := M) g gm σ ρ P -
        deTurckLieTraceCoeffPiece (I := I) (M := M) g gm σ ρ Q := by
  unfold deTurckLieTraceCoeffPiece
  rw [slotExtend_sub, slotExtend_sub, operatorFieldComposition_sub_right,
    reindexCoeffGen_sub (I := I) (M := M)]

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [SigmaCompactSpace M] in
private theorem deTurckLieFirstOrderBackgroundConnectionDifference_self
    (g gm : SmoothRiemannianMetric I M) :
    deTurckLieFirstOrderBackgroundConnectionDifference (I := I) (M := M) g gm g =
      connectionDifferenceSection (I := I) gm g := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rfl

omit [NeZero (Module.finrank ℝ E)] in
omit [I.Boundaryless] [SigmaCompactSpace M] in
private theorem deTurckLieFirstOrderCoefficient_backgroundDifference_decomposition
    (g gm gB : SmoothRiemannianMetric I M) :
    deTurckLieFirstOrderCoeff (I := I) (M := M) g gm gB -
        deTurckLieFirstOrderCoeff (I := I) (M := M) g gm g =
      lieFirstOrderPiece (I := I) (M := M) g gm lieFirstOrderSigmaC
          lieFirstOrderRhoSlot0 (lieFirstOrderFixCd (I := I) (M := M) g gB) +
        lieFirstOrderPiece (I := I) (M := M) g gm lieFirstOrderSigmaA
          (Equiv.refl (Fin 3)) (deTurckLieFirstOrderBackgroundCoefficientDifference (I := I) (M := M) g gm gB) +
        lieFirstOrderPiece (I := I) (M := M) g gm lieFirstOrderSigmaASwap
          (Equiv.refl (Fin 3)) (deTurckLieFirstOrderBackgroundCoefficientDifference (I := I) (M := M) g gm gB) := by
  rw [deTurckLieFirstOrderCoeff_eq_lieFirstOrderPiece_sum
      (I := I) (M := M) g gm gB,
    deTurckLieFirstOrderCoeff_eq_lieFirstOrderPiece_sum
      (I := I) (M := M) g gm g,
    lieFirstOrder_connectionDifferenceBackground_decomp (I := I) (M := M) g gm gB,
    deTurckLieFirstOrderBackgroundConnectionDifference_self (I := I) (M := M) g gm,
    deTurckLieTraceCoeffPiece_add (I := I) (M := M)]
  unfold deTurckLieFirstOrderBackgroundCoefficientDifference
  change _ =
    deTurckLieTraceCoeffPiece (I := I) (M := M) g gm lieFirstOrderSigmaC
        lieFirstOrderRhoSlot0 (lieFirstOrderFixCd (I := I) (M := M) g gB) +
      deTurckLieTraceCoeffPiece (I := I) (M := M) g gm lieFirstOrderSigmaA
        (Equiv.refl (Fin 3))
          (deTurckLieFirstOrderBackgroundCoefficient (I := I) (M := M) g gm gB -
            deTurckLieFirstOrderBackgroundCoefficient (I := I) (M := M) g gm g) +
      deTurckLieTraceCoeffPiece (I := I) (M := M) g gm lieFirstOrderSigmaASwap
        (Equiv.refl (Fin 3))
          (deTurckLieFirstOrderBackgroundCoefficient (I := I) (M := M) g gm gB -
            deTurckLieFirstOrderBackgroundCoefficient (I := I) (M := M) g gm g)
  rw [deTurckLieTraceCoeffPiece_sub (I := I) (M := M),
    deTurckLieTraceCoeffPiece_sub (I := I) (M := M)]
  module

omit [NeZero (Module.finrank ℝ E)] in
private theorem covariantJetNormSq_two_reindexCoeffGen
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

omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] [SigmaCompactSpace M] in
omit [I.Boundaryless] in
private theorem deTurckLieTraceCoeff_eq_reindexedPureTrace
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


theorem exists_deTurckLieFirstOrderCoefficient_backgroundDifference_covariantJetNormSq_two_uniform_bound
    (hDim : Module.finrank ℝ E = 3)
    (gBase : SmoothRiemannianMetric I M) {Λ : ℝ} (hΛ : 1 ≤ Λ)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ B : ℝ → ℝ,
      (∀ R : ℝ, 0 ≤ R → 0 ≤ B R) ∧
      ∀ g : SmoothRiemannianMetric I M,
        MetricUniformEquivalentOn (I := I) Set.univ gBase g Λ →
        MetricCovDerivOrderBoundOn (I := I) Set.univ 1 g gBase Λ →
        MetricCovDerivOrderBoundOn (I := I) Set.univ 2 g gBase Λ →
        MetricCovDerivOrderBoundOn (I := I) Set.univ 3 g gBase Λ →
        ∀ (gm : SmoothRiemannianMetric I M) (P : SmoothCcTensor g 0 2),
          (∀ (x : M) (u v : TangentSpace I x),
            gm.inner x u v = g.inner x u v +
              ccTensorBilinSymm (I := I) g P x u v) →
          ∀ {δ : ℝ}, δ ≤ δ₀ → 0 ≤ δ →
          gFibreOpBound (I := I) (M := M) g
            (ccTensorBilinSymm (I := I) g P) δ →
          ∀ R : ℝ, 0 ≤ R →
          covariantJetNormSq (I := I) (M := M) g 2 P ≤ R ^ 2 →
          covariantJetNormSq (I := I) (M := M) g 2
            (deTurckLieFirstOrderCoeff (I := I) (M := M) g gm gBase -
              deTurckLieFirstOrderCoeff (I := I) (M := M) g gm g) ≤
            (B R) ^ 2 := by
  have hΛ0 : 0 ≤ Λ := le_trans (by norm_num) hΛ
  obtain ⟨Bt, hBt, htrace⟩ :=
    trace2_h2_uniform (I := I) (M := M) hDim gBase hΛ0 hδ₀
  obtain ⟨Bs, hBs, hsharp⟩ :=
    sharp_h2_uniform (I := I) (M := M) hDim gBase hΛ0 hδ₀
  obtain ⟨Fm, hFm, hfix⟩ :=
    lieFix_h2_uniform (I := I) (M := M) hDim gBase hΛ
  obtain ⟨Fc, hFc, hconn⟩ :=
    connFix_h2_uniform (I := I) (M := M) hDim gBase hΛ
  obtain ⟨Bp, hBp, hpb⟩ :=
    pbLow_h2_uniform (I := I) (M := M) hDim gBase hΛ
  obtain ⟨Ca, hCa, happ⟩ :=
    operatorFieldComposition_h2_h2_to_h2_uniform_bound (I := I) (M := M) hDim gBase hΛ 1 1 2
  obtain ⟨Cp, hCp, hpiece⟩ :=
    piece_h2_uniform (I := I) (M := M) hDim gBase hΛ
  let S : ℝ := Real.sqrt ((Module.finrank ℝ E : ℝ) ^ 2)
  let L : ℝ → ℝ := fun R => 2 * (Fc + Bp R)
  let Ppsi : ℝ → ℝ := fun R => Ca * L R * Bs R
  let Qfix : ℝ → ℝ := fun R => Cp * Bt R * (S * Fm)
  let Qpsi : ℝ → ℝ := fun R => Cp * Bt R * (S * Ppsi R)
  let B : ℝ → ℝ := fun R => 2 * (Qfix R + Qpsi R + Qpsi R)
  have hS : 0 ≤ S := Real.sqrt_nonneg _
  have hL : ∀ R : ℝ, 0 ≤ R → 0 ≤ L R := by
    intro R hR
    exact mul_nonneg (by norm_num) (add_nonneg hFc (hBp R hR))
  have hPpsi : ∀ R : ℝ, 0 ≤ R → 0 ≤ Ppsi R := by
    intro R hR
    exact mul_nonneg (mul_nonneg hCa (hL R hR)) (hBs R hR)
  have hQfix : ∀ R : ℝ, 0 ≤ R → 0 ≤ Qfix R := by
    intro R hR
    exact mul_nonneg (mul_nonneg hCp (hBt R hR)) (mul_nonneg hS hFm)
  have hQpsi : ∀ R : ℝ, 0 ≤ R → 0 ≤ Qpsi R := by
    intro R hR
    exact mul_nonneg (mul_nonneg hCp (hBt R hR))
      (mul_nonneg hS (hPpsi R hR))
  refine ⟨B, fun R hR =>
    mul_nonneg (by norm_num)
      (add_nonneg (add_nonneg (hQfix R hR) (hQpsi R hR))
        (hQpsi R hR)), ?_⟩
  intro g hEq hjet1 hjet2 hjet3 gm P htie δ hδ_le hδ_nonneg hbound
    R hR hP
  let Fix : SmoothCcTensor g 1 2 :=
    lieFirstOrderFixCd (I := I) (M := M) g gBase
  let CovFix : SmoothCcTensor g 0 3 :=
    -lieCorrectionZeroKappa (I := I) (M := M) g g gBase
  let Pb : SmoothCcTensor g 0 3 :=
    lieCorrectionZeroPbLow (I := I) (M := M) g P g gBase
  let Left : SmoothCcTensor g 1 2 :=
    deTurckLieFirstOrderBackgroundRaisedConnectionDifference (I := I) (M := M) g gm gBase -
      deTurckLieFirstOrderBackgroundRaisedConnectionDifference (I := I) (M := M) g gm g
  let Sharp : SmoothCcTensor g 1 1 :=
    sharpFlatEndoCc (I := I) g gm
  let Psi : SmoothCcTensor g 1 2 :=
    deTurckLieFirstOrderBackgroundCoefficientDifference (I := I) (M := M) g gm gBase
  have hTrace : ∀ σ : Equiv.Perm (Fin 4),
      covariantJetNormSq (I := I) (M := M) g 2
          (deTurckLieTraceCoeff (I := I) (M := M) g gm σ) ≤
        (Bt R) ^ 2 := by
    intro σ
    rw [deTurckLieTraceCoeff_eq_reindexedPureTrace (I := I) (M := M) g gm σ]
    simpa only [covariantJetNormSq, reindexedPureTrace, Nat.reduceAdd] using
      htrace g hEq hjet1 hjet2 gm P htie hδ_le hδ_nonneg hbound σ R hR hP
  have hSharp : covariantJetNormSq (I := I) (M := M) g 2 Sharp ≤
      (Bs R) ^ 2 := by
    simpa only [Sharp, covariantJetNormSq, Nat.reduceAdd] using
      hsharp g hEq hjet1 hjet2 gm P htie hδ_le hδ_nonneg hbound R hR hP
  have hFix : covariantJetNormSq (I := I) (M := M) g 2 Fix ≤ Fm ^ 2 := by
    simpa only [Fix, covariantJetNormSq, Nat.reduceAdd] using
      hfix g hEq hjet1 hjet2 hjet3
  have hCovFix : covariantJetNormSq (I := I) (M := M) g 2 CovFix ≤ Fc ^ 2 := by
    rw [show covariantJetNormSq (I := I) (M := M) g 2 CovFix =
        covariantJetNormSq (I := I) (M := M) g 2
          (connectionDifferenceSection (I := I) gBase g) by
      simpa only [CovFix] using
        covariantJetNormSq_two_neg_lieCorrectionZeroKappa_base_eq (I := I) (M := M) g gBase]
    simpa only [covariantJetNormSq, Nat.reduceAdd] using
      hconn g hEq hjet1 hjet2 hjet3
  have hPb : covariantJetNormSq (I := I) (M := M) g 2 Pb ≤ (Bp R) ^ 2 := by
    simpa only [Pb, covariantJetNormSq, Nat.reduceAdd] using
      hpb g hEq hjet1 hjet2 hjet3 P R hR hP
  have hLeft : covariantJetNormSq (I := I) (M := M) g 2 Left ≤
      (L R) ^ 2 := by
    rw [show Left =
        cometricRaiseSlot0Field (I := I) (M := M) g 1
          (domDomCongrSection (I := I) g lieFirstOrderRhoSlot0
            (CovFix - Pb)) by
      simpa only [Left, CovFix, Pb] using
        deTurckLieFirstOrderBackgroundRaisedConnectionDifference_backgroundDifference (I := I) (M := M) g gm gBase P htie]
    rw [covariantJetNormSq_two_cometricRaise_domDomCongrSection (I := I) (M := M) g lieFirstOrderRhoSlot0 (CovFix - Pb)]
    calc
      covariantJetNormSq (I := I) (M := M) g 2 (CovFix - Pb) =
          covariantJetNormSq (I := I) (M := M) g 2 (CovFix + -Pb) := by
        rw [sub_eq_add_neg]
      _ ≤ 2 * (covariantJetNormSq (I := I) (M := M) g 2 CovFix +
          covariantJetNormSq (I := I) (M := M) g 2 (-Pb)) :=
        covariantJetNormSq_add_le (I := I) (M := M) g 2 CovFix (-Pb)
      _ = 2 * (covariantJetNormSq (I := I) (M := M) g 2 CovFix +
          covariantJetNormSq (I := I) (M := M) g 2 Pb) := by
        rw [covariantJetNormSq_neg (I := I) (M := M) g 2 Pb]
      _ ≤ 2 * (Fc ^ 2 + (Bp R) ^ 2) :=
        mul_le_mul_of_nonneg_left (add_le_add hCovFix hPb) (by norm_num)
      _ ≤ (L R) ^ 2 := by
        simp only [L]
        nlinarith [mul_nonneg hFc (hBp R hR)]
  have hPsi : covariantJetNormSq (I := I) (M := M) g 2 Psi ≤
      (Ppsi R) ^ 2 := by
    change covariantJetNormSq (I := I) (M := M) g 2
      (deTurckLieFirstOrderBackgroundCoefficientDifference (I := I) (M := M) g gm gBase) ≤ (Ppsi R) ^ 2
    rw [deTurckLieFirstOrderBackgroundCoefficientDifference_eq_comp (I := I) (M := M) g gm gBase]
    simpa only [Left, Sharp, Ppsi, covariantJetNormSq, Nat.reduceAdd] using
      happ g hEq hjet1 hjet2 Left Sharp (L R) (Bs R)
        (hL R hR) (hBs R hR)
        (by simpa only [covariantJetNormSq, Nat.reduceAdd] using hLeft)
        (by simpa only [covariantJetNormSq, Nat.reduceAdd] using hSharp)
  let V0 : SmoothCcTensor g 3 2 :=
    lieFirstOrderPiece (I := I) (M := M) g gm lieFirstOrderSigmaC
      lieFirstOrderRhoSlot0 Fix
  let V1 : SmoothCcTensor g 3 2 :=
    lieFirstOrderPiece (I := I) (M := M) g gm lieFirstOrderSigmaA
      (Equiv.refl (Fin 3)) Psi
  let V2 : SmoothCcTensor g 3 2 :=
    lieFirstOrderPiece (I := I) (M := M) g gm lieFirstOrderSigmaASwap
      (Equiv.refl (Fin 3)) Psi
  have hV0 : covariantJetNormSq (I := I) (M := M) g 2 V0 ≤ (Qfix R) ^ 2 := by
    simpa only [V0, Qfix, S, covariantJetNormSq, Nat.reduceAdd] using
      hpiece g hEq hjet1 hjet2 gm lieFirstOrderSigmaC lieFirstOrderRhoSlot0 Fix
        (Bt R) Fm (hBt R hR) hFm
        (by simpa only [covariantJetNormSq, Nat.reduceAdd] using hTrace lieFirstOrderSigmaC)
        (by simpa only [covariantJetNormSq, Nat.reduceAdd] using hFix)
  have hV1 : covariantJetNormSq (I := I) (M := M) g 2 V1 ≤ (Qpsi R) ^ 2 := by
    simpa only [V1, Qpsi, S, covariantJetNormSq, Nat.reduceAdd] using
      hpiece g hEq hjet1 hjet2 gm lieFirstOrderSigmaA (Equiv.refl (Fin 3)) Psi
        (Bt R) (Ppsi R) (hBt R hR) (hPpsi R hR)
        (by simpa only [covariantJetNormSq, Nat.reduceAdd] using hTrace lieFirstOrderSigmaA)
        (by simpa only [covariantJetNormSq, Nat.reduceAdd] using hPsi)
  have hV2 : covariantJetNormSq (I := I) (M := M) g 2 V2 ≤ (Qpsi R) ^ 2 := by
    simpa only [V2, Qpsi, S, covariantJetNormSq, Nat.reduceAdd] using
      hpiece g hEq hjet1 hjet2 gm lieFirstOrderSigmaASwap
        (Equiv.refl (Fin 3)) Psi (Bt R) (Ppsi R)
        (hBt R hR) (hPpsi R hR)
        (by simpa only [covariantJetNormSq, Nat.reduceAdd] using
          hTrace lieFirstOrderSigmaASwap)
        (by simpa only [covariantJetNormSq, Nat.reduceAdd] using hPsi)
  have hcorr :
      deTurckLieFirstOrderCoeff (I := I) (M := M) g gm gBase -
          deTurckLieFirstOrderCoeff (I := I) (M := M) g gm g =
        V0 + V1 + V2 := by
    simpa only [V0, V1, V2, Fix, Psi] using
      deTurckLieFirstOrderCoefficient_backgroundDifference_decomposition (I := I) (M := M) g gm gBase
  rw [hcorr]
  change covariantJetNormSq (I := I) (M := M) g 2 (V0 + V1 + V2) ≤ (B R) ^ 2
  calc
    covariantJetNormSq (I := I) (M := M) g 2 (V0 + V1 + V2) ≤
        2 * (covariantJetNormSq (I := I) (M := M) g 2 (V0 + V1) +
          covariantJetNormSq (I := I) (M := M) g 2 V2) :=
      covariantJetNormSq_add_le (I := I) (M := M) g 2 (V0 + V1) V2
    _ ≤ 2 * (2 * (covariantJetNormSq (I := I) (M := M) g 2 V0 +
          covariantJetNormSq (I := I) (M := M) g 2 V1) +
        covariantJetNormSq (I := I) (M := M) g 2 V2) := by
      exact mul_le_mul_of_nonneg_left
        (add_le_add (covariantJetNormSq_add_le (I := I) (M := M) g 2 V0 V1) le_rfl)
        (by norm_num)
    _ ≤ 2 * (2 * ((Qfix R) ^ 2 + (Qpsi R) ^ 2) +
        (Qpsi R) ^ 2) := by
      exact mul_le_mul_of_nonneg_left
        (add_le_add
          (mul_le_mul_of_nonneg_left (add_le_add hV0 hV1) (by norm_num))
          hV2) (by norm_num)
    _ ≤ 4 * ((Qfix R) ^ 2 + (Qpsi R) ^ 2 + (Qpsi R) ^ 2) := by
      nlinarith [sq_nonneg (Qpsi R)]
    _ ≤ (2 * (Qfix R + Qpsi R + Qpsi R)) ^ 2 := by
      nlinarith [sq_nonneg (Qfix R), sq_nonneg (Qpsi R),
        mul_nonneg (hQfix R hR) (hQpsi R hR)]
    _ = (B R) ^ 2 := rfl

noncomputable def lowerScaleFirstOrderCoefficientBackgroundDifference
    (g gBase : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδT : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) δ)
    (hδZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g
        (0 : SmoothCcTensor g 0 2)) δ) :
    SmoothCcTensor g 3 2 :=
  (lowerScaleActionCoefficients (I := I) (M := M) g gBase T hδ_lt hδT hδZ).firstOrderCoefficient -
    (lowerScaleActionCoefficients (I := I) (M := M) g g T hδ_lt hδT hδZ).firstOrderCoefficient

private noncomputable def lowerScaleFirstOrderCoefficient_backgroundDifferencePathIntegral
    (g gBase : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδT : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) δ)
    (hδZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g
        (0 : SmoothCcTensor g 0 2)) δ) :
    SmoothCcTensor g 3 2 :=
  pathIntegralCoeffField (I := I) (M := M) g 3 2
    (fun s =>
      ricciDeTurckRemainderFirstOrderCoefficient (I := I) (M := M) g gBase T 0 hδT hδZ s -
        ricciDeTurckRemainderFirstOrderCoefficient (I := I) (M := M) g g T 0 hδT hδZ s)
    (metricPerturbationPathDomain (δ := δ) (δ' := δ))
    metricPerturbationPathDomain_isOpen
    (by
      rw [Set.uIcc_of_le zero_le_one]
      exact Icc_subset_metricPerturbationPathDomain hδ_lt hδ_lt)
    (by
      change linearizedRicciCovariantJetJointSmoothness (I := I) (M := M) g 3
        (fun s =>
          ricciDeTurckRemainderFirstOrderCoefficient (I := I) (M := M)
              g gBase T 0 hδT hδZ s -
            ricciDeTurckRemainderFirstOrderCoefficient (I := I) (M := M)
              g g T 0 hδT hδZ s)
      exact covariantJetJoint_sub (I := I) (M := M) g _ _
        (ricciDeTurckRemainderFirstOrderCoefficient_path_joint (I := I) (M := M)
          g gBase T 0 hδT hδZ)
        (ricciDeTurckRemainderFirstOrderCoefficient_path_joint (I := I) (M := M)
          g g T 0 hδT hδZ))

omit [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
private theorem lowerScaleFirstOrderCoefficient_backgroundDifferencePathIntegral_toModel
    (g gBase : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδT : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) δ)
    (hδZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g (0 : SmoothCcTensor g 0 2)) δ) (x : M) :
    TensorRSSpace.toModel
        ((lowerScaleFirstOrderCoefficient_backgroundDifferencePathIntegral
          (I := I) (M := M) g gBase T hδ_lt hδT hδZ).toSection x) =
      ∫ s in (0 : ℝ)..1, TensorRSSpace.toModel
        ((ricciDeTurckRemainderFirstOrderCoefficient (I := I) (M := M)
            g gBase T 0 hδT hδZ s -
          ricciDeTurckRemainderFirstOrderCoefficient (I := I) (M := M)
            g g T 0 hδT hδZ s).toSection x) := by
  unfold lowerScaleFirstOrderCoefficient_backgroundDifferencePathIntegral
  exact pathIntegralCoeffField_toModel (I := I) (M := M) g 3 2 _ _ _ _ _ x

private theorem lowerScaleFirstOrderCoefficient_backgroundDifference_eq_pathIntegral
    (g gBase : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδT : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) δ)
    (hδZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g
        (0 : SmoothCcTensor g 0 2)) δ) :
    lowerScaleFirstOrderCoefficientBackgroundDifference (I := I) (M := M) g gBase T hδ_lt hδT hδZ =
      lowerScaleFirstOrderCoefficient_backgroundDifferencePathIntegral (I := I) (M := M) g gBase T hδ_lt hδT hδZ := by
  classical
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  apply TensorRSSpace.toModel_injective
  have hSI : Set.uIcc (0 : ℝ) 1 ⊆
      metricPerturbationPathDomain (δ := δ) (δ' := δ) := by
    rw [Set.uIcc_of_le zero_le_one]
    exact Icc_subset_metricPerturbationPathDomain hδ_lt hδ_lt
  have hBcont :=
    jointContMDiff_toModel_continuous_slice
      (I := I) g 3 2
      (fun s => ricciDeTurckRemainderFirstOrderCoefficient (I := I) (M := M) g gBase
        T 0 hδT hδZ s)
      (metricPerturbationPathDomain (δ := δ) (δ' := δ))
      (ricciDeTurckRemainderFirstOrderCoefficient_path_joint (I := I) (M := M) g gBase T 0 hδT hδZ) x
  have hScont :=
    jointContMDiff_toModel_continuous_slice
      (I := I) g 3 2
      (fun s => ricciDeTurckRemainderFirstOrderCoefficient (I := I) (M := M) g g
        T 0 hδT hδZ s)
      (metricPerturbationPathDomain (δ := δ) (δ' := δ))
      (ricciDeTurckRemainderFirstOrderCoefficient_path_joint (I := I) (M := M) g g T 0 hδT hδZ) x
  have hBint : IntervalIntegrable
      (fun s : ℝ => TensorRSSpace.toModel
        ((ricciDeTurckRemainderFirstOrderCoefficient (I := I) (M := M) g gBase
          T 0 hδT hδZ s).toSection x))
      MeasureTheory.volume 0 1 :=
    (hBcont.mono hSI).intervalIntegrable
  have hSint : IntervalIntegrable
      (fun s : ℝ => TensorRSSpace.toModel
        ((ricciDeTurckRemainderFirstOrderCoefficient (I := I) (M := M) g g
          T 0 hδT hδZ s).toSection x))
      MeasureTheory.volume 0 1 :=
    (hScont.mono hSI).intervalIntegrable
  simp only [lowerScaleFirstOrderCoefficientBackgroundDifference, lowerScaleActionCoefficients,
    SmoothCcTensor.toSection_sub, ContMDiffSection.coe_sub, Pi.sub_apply,
    TensorRSSpace.toModel_sub]
  rw [ricciDeTurckRemainderFirstOrderPathIntegral_toModel,
    ricciDeTurckRemainderFirstOrderPathIntegral_toModel]
  rw [lowerScaleFirstOrderCoefficient_backgroundDifferencePathIntegral_toModel]
  simp only [SmoothCcTensor.toSection_sub, ContMDiffSection.coe_sub, Pi.sub_apply,
    TensorRSSpace.toModel_sub]
  rw [intervalIntegral.integral_sub hBint hSint]

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [SigmaCompactSpace M] in
private theorem rhsLow1Coeff_backgroundDifference_eq_deTurckLieFirstOrderCoefficientDifference
    (g gBase : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2)
    {δ : ℝ}
    (hδT : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) δ)
    (hδZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g
        (0 : SmoothCcTensor g 0 2)) δ)
    (s : ℝ) :
    ricciDeTurckRemainderFirstOrderCoefficient (I := I) (M := M) g gBase T 0 hδT hδZ s -
        ricciDeTurckRemainderFirstOrderCoefficient (I := I) (M := M) g g T 0 hδT hδZ s =
      deTurckLieFirstOrderCoeff (I := I) (M := M) g
          (metricPerturbationPath (I := I) g T 0 hδT hδZ s) gBase -
        deTurckLieFirstOrderCoeff (I := I) (M := M) g
          (metricPerturbationPath (I := I) g T 0 hδT hδZ s) g := by
  simp only [ricciDeTurckRemainderFirstOrderCoefficient]
  abel


theorem exists_lowerScaleFirstOrderCoefficient_backgroundDifference_covariantJetNormSq_two_uniform_bound
    (hDim : Module.finrank ℝ E = 3)
    (gBase : SmoothRiemannianMetric I M) {Λ : ℝ} (hΛ : 1 ≤ Λ)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ B : ℝ → ℝ,
      (∀ R : ℝ, 0 ≤ R → 0 ≤ B R) ∧
      ∀ g : SmoothRiemannianMetric I M,
        MetricUniformEquivalentOn (I := I) Set.univ gBase g Λ →
        (∀ a : ℕ, a ≤ 3 →
          MetricCovDerivOrderBoundOn (I := I) Set.univ a g gBase Λ) →
        ∀ (T : SmoothCcTensor g 0 2) {δ : ℝ},
          (hδ_le : δ ≤ δ₀) → 0 ≤ δ →
          (hδT : gFibreOpBound (I := I) (M := M) g
            (ccTensorBilinSymm (I := I) g T) δ) →
          (hδZ : gFibreOpBound (I := I) (M := M) g
            (ccTensorBilinSymm (I := I) g
              (0 : SmoothCcTensor g 0 2)) δ) →
          ∀ R : ℝ, 0 ≤ R →
          ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ ≤ R →
          covariantJetNormSq (I := I) (M := M) g 2
            (lowerScaleFirstOrderCoefficientBackgroundDifference (I := I) (M := M) g gBase T
              (lt_of_le_of_lt hδ_le hδ₀) hδT hδZ) ≤
            (B R) ^ 2 := by
  obtain ⟨C, hC⟩ := exists_convex_jets (I := I) (M := M) gBase hΛ
  obtain ⟨Bc, hBc, hcorr⟩ :=
    exists_deTurckLieFirstOrderCoefficient_backgroundDifference_covariantJetNormSq_two_uniform_bound (I := I) (M := M) hDim gBase hΛ hδ₀
  let B : ℝ → ℝ := fun R => Bc (C.h2C * R)
  have hB : ∀ R : ℝ, 0 ≤ R → 0 ≤ B R := by
    intro R hR
    exact hBc (C.h2C * R) (mul_nonneg hC.h2_nonneg hR)
  refine ⟨B, hB, ?_⟩
  intro g hEq hjet T δ hδ_le hδ_nonneg hδT hδZ R hR hTHs
  have hδ_lt : δ < 1 := lt_of_le_of_lt hδ_le hδ₀
  rw [lowerScaleFirstOrderCoefficient_backgroundDifference_eq_pathIntegral (I := I) (M := M) g gBase T hδ_lt hδT hδZ]
  let Φ : ℝ → SmoothCcTensor g 3 2 := fun s =>
    ricciDeTurckRemainderFirstOrderCoefficient (I := I) (M := M) g gBase T 0 hδT hδZ s -
      ricciDeTurckRemainderFirstOrderCoefficient (I := I) (M := M) g g T 0 hδT hδZ s
  let S : Set ℝ := metricPerturbationPathDomain (δ := δ) (δ' := δ)
  have hSI : Set.uIcc (0 : ℝ) 1 ⊆ S := by
    dsimp only [S]
    rw [Set.uIcc_of_le zero_le_one]
    exact Icc_subset_metricPerturbationPathDomain hδ_lt hδ_lt
  have hjoint :
      linearizedRicciCovariantJetJointSmoothness (I := I) (M := M) g 3 Φ
        (δ := δ) (δ' := δ) := by
    dsimp only [Φ]
    exact covariantJetJoint_sub (I := I) (M := M) g _ _
      (ricciDeTurckRemainderFirstOrderCoefficient_path_joint (I := I) (M := M) g gBase T 0 hδT hδZ)
      (ricciDeTurckRemainderFirstOrderCoefficient_path_joint (I := I) (M := M) g g T 0 hδT hδZ)
  obtain ⟨hpath2, _hpath3⟩ := hC.bounds g hEq hjet
  have hZero : ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ)
      (0 : SmoothCcTensor g 0 2)‖ ≤ R := by
    have hz := ccTensorToHs_smul (I := I) (M := M) g 2 (2 : ℝ) 0
      (0 : SmoothCcTensor g 0 2)
    have hz' : ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ)
        (0 : SmoothCcTensor g 0 2) = 0 := by
      simpa only [zero_smul] using hz
    rw [hz', norm_zero]
    exact hR
  have hCR : 0 ≤ C.h2C * R := mul_nonneg hC.h2_nonneg hR
  have hpoint : ∀ s ∈ Set.Icc (0 : ℝ) 1,
      covariantJetNormSq (I := I) (M := M) g 2 (Φ s) ≤ (B R) ^ 2 := by
    intro s hs
    let P : SmoothCcTensor g 0 2 :=
      convexPerturbation (I := I) g T 0 s
    let gm : SmoothRiemannianMetric I M :=
      metricPerturbationPath (I := I) g T 0 hδT hδZ s
    have hs_mem : s ∈ metricPerturbationPathDomain (δ := δ) (δ' := δ) :=
      Icc_subset_metricPerturbationPathDomain hδ_lt hδ_lt hs
    have hPtie : ∀ (x : M) (u v : TangentSpace I x),
        gm.inner x u v = g.inner x u v +
          ccTensorBilinSymm (I := I) g P x u v := by
      intro x u v
      simpa only [gm, P] using
        metricPerturbationPath_inner_of_mem (I := I) g T 0 hδT hδZ hs_mem x u v
    have hδP : gFibreOpBound (I := I) (M := M) g
        (ccTensorBilinSymm (I := I) g P) δ := by
      intro x u v
      have hraw := convexPerturbation_gFibreOpBound_abs
        (I := I) g T 0 hδT hδZ s x u v
      have heq : |1 - s| * δ + |s| * δ = δ := by
        rw [abs_of_nonneg (by linarith [hs.2] : (0 : ℝ) ≤ 1 - s),
          abs_of_nonneg hs.1]
        ring
      simpa only [P, convexPerturbation, smul_zero, zero_add, heq] using hraw
    have hP2 : covariantJetNormSq (I := I) (M := M) g 2 P ≤
        (C.h2C * R) ^ 2 := by
      simpa only [P, covariantJetNormSq, Nat.reduceAdd] using
        hpath2 T 0 R hR hTHs hZero s hs
    have hraw := hcorr g hEq (hjet 1 (by norm_num))
      (hjet 2 (by norm_num)) (hjet 3 (by norm_num)) gm P hPtie
      hδ_le hδ_nonneg hδP (C.h2C * R) hCR hP2
    rw [show Φ s =
        deTurckLieFirstOrderCoeff (I := I) (M := M) g gm gBase -
          deTurckLieFirstOrderCoeff (I := I) (M := M) g gm g by
      dsimp only [Φ, gm]
      exact rhsLow1Coeff_backgroundDifference_eq_deTurckLieFirstOrderCoefficientDifference (I := I) (M := M) g gBase T hδT hδZ s]
    simpa only [B] using hraw
  have hpath := path_jetL2_le (I := I) (M := M) g 3 2 2
    Φ S metricPerturbationPathDomain_isOpen hSI hjoint
    (B := B R) hpoint
  simpa only [lowerScaleFirstOrderCoefficient_backgroundDifferencePathIntegral, Φ, S, covariantJetNormSq, Nat.reduceAdd] using hpath

private theorem exists_deTurckLieFirstOrderCoefficient_backgroundDifference_difference_covariantJetNormSq_two_bound
    (hDim : Module.finrank ℝ E = 3)
    (g gB : SmoothRiemannianMetric I M)
    {δ₀ : ℝ} (hδ₀0 : 0 ≤ δ₀) (hδ₀ : δ₀ < 1) :
    ∃ ρ B : ℝ, 0 < ρ ∧ 0 ≤ B ∧
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
      let N := ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) (T - U)‖
      covariantJetNormSq (I := I) (M := M) g 2
          ((deTurckLieFirstOrderCoeff (I := I) (M := M) g gT gB -
              deTurckLieFirstOrderCoeff (I := I) (M := M) g gT g) -
            (deTurckLieFirstOrderCoeff (I := I) (M := M) g gU gB -
              deTurckLieFirstOrderCoeff (I := I) (M := M) g gU g)) ≤
        (B * N) ^ 2 := by
  obtain ⟨ρt, Ct, hρt, hCt, htracePair⟩ :=
    RicciDeTurckLowOrder.trace2_pair_h2 (I := I) (M := M) hDim g
  obtain ⟨ρb, Tb, hρb, hTb, htraceBdd⟩ :=
    RicciDeTurckLowOrder.trace_two_sobolev_two_bound (I := I) (M := M) hDim g
  obtain ⟨ρp, Pp, Bp, hρp, hPp, hBp, hpsi⟩ :=
    exists_deTurckLieFirstOrderBackgroundCoefficient_difference_pairing_secondOrder_bound (I := I) (M := M) hDim g gB hδ₀0 hδ₀
  obtain ⟨Cp, hCp, hpiece⟩ :=
    liePiece_pair (I := I) (M := M) hDim g
  let F : SmoothCcTensor g 1 2 :=
    lieFirstOrderFixCd (I := I) (M := M) g gB
  let F0 : ℝ := Real.sqrt (covariantJetNormSq (I := I) (M := M) g 2 F)
  let B : ℝ :=
    2 * (Cp * Ct * F0 + 2 * (Cp * (Tb * Bp + Ct * Pp)))
  let ρ : ℝ := min ρt (min ρb ρp)
  have hF0 : 0 ≤ F0 := Real.sqrt_nonneg _
  have hF0sq : F0 ^ 2 = covariantJetNormSq (I := I) (M := M) g 2 F := by
    simpa only [F0] using Real.sq_sqrt
      (Finset.sum_nonneg fun _ _ => sq_nonneg _)
  have hB : 0 ≤ B := by
    dsimp only [B]
    positivity
  have hρ : 0 < ρ := lt_min hρt (lt_min hρb hρp)
  refine ⟨ρ, B, hρ, hB, ?_⟩
  intro gT gU T U hT hU hTtie hUtie
    δT δU hδT_le hδT0 hδT hδU_le hδU0 hδU hTHs hUHs
  dsimp only
  let N : ℝ :=
    ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) (T - U)‖
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
  have hTrU : ∀ σ : Equiv.Perm (Fin 4),
      covariantJetNormSq (I := I) (M := M) g 2
          (deTurckLieTraceCoeff (I := I) (M := M) g gU σ) ≤
        Tb ^ 2 := by
    intro σ
    rw [deTurckLieTraceCoeff_eq_reindexedPureTrace (I := I) (M := M) g gU σ,
      covariantJetNormSq_two_reindexCoeffGen (I := I) (M := M)]
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
      rw [deTurckLieTraceCoeff_eq_reindexedPureTrace (I := I) (M := M) g gT σ,
        deTurckLieTraceCoeff_eq_reindexedPureTrace (I := I) (M := M) g gU σ,
        reindexCoeffGen_sub (I := I) (M := M)]
    rw [heq, covariantJetNormSq_two_reindexCoeffGen (I := I) (M := M)]
    simpa only [N] using
      htracePair T U gT gU hTtie hUtie hTHst hUHst
  have hPsiRaw := hpsi gT gU T U hT hU hTtie hUtie
    hδT_le hδT0 hδT hδU_le hδU0 hδU hTHsp hUHsp
  let PT : SmoothCcTensor g 1 2 :=
    deTurckLieFirstOrderBackgroundCoefficientDifference (I := I) (M := M) g gT gB
  let PU : SmoothCcTensor g 1 2 :=
    deTurckLieFirstOrderBackgroundCoefficientDifference (I := I) (M := M) g gU gB
  have hPT : covariantJetNormSq (I := I) (M := M) g 2 PT ≤ Pp ^ 2 := by
    simpa only [PT, deTurckLieFirstOrderBackgroundCoefficientDifference] using hPsiRaw.1
  have hPD : covariantJetNormSq (I := I) (M := M) g 2 (PT - PU) ≤
      (Bp * N) ^ 2 := by
    simpa only [PT, PU, deTurckLieFirstOrderBackgroundCoefficientDifference, N] using hPsiRaw.2
  have hFF : covariantJetNormSq (I := I) (M := M) g 2 (F - F) ≤
      (0 : ℝ) ^ 2 := by
    rw [sub_self]
    unfold covariantJetNormSq
    have hz (q : ℕ) : iteratedCovGrad (I := I) g 1 2 q
        (0 : SmoothCcTensor g 1 2) = 0 := by
      have h := DifferentialGeometry.Analysis.Sobolev.iteratedCovGrad_smul_real
        (I := I) (M := M) g 1 2 q
        (0 : ℝ) (0 : SmoothCcTensor g 1 2)
      simpa only [zero_smul] using h
    simp only [hz, norm_zero]
    norm_num
  have hFs : covariantJetNormSq (I := I) (M := M) g 2 F ≤ F0 ^ 2 :=
    hF0sq.symm.le
  let V0 : SmoothCcTensor g 3 2 :=
    lieFirstOrderPiece (I := I) (M := M) g gT lieFirstOrderSigmaC
        lieFirstOrderRhoSlot0 F -
      lieFirstOrderPiece (I := I) (M := M) g gU lieFirstOrderSigmaC
        lieFirstOrderRhoSlot0 F
  let V1 : SmoothCcTensor g 3 2 :=
    lieFirstOrderPiece (I := I) (M := M) g gT lieFirstOrderSigmaA
        (Equiv.refl (Fin 3)) PT -
      lieFirstOrderPiece (I := I) (M := M) g gU lieFirstOrderSigmaA
        (Equiv.refl (Fin 3)) PU
  let V2 : SmoothCcTensor g 3 2 :=
    lieFirstOrderPiece (I := I) (M := M) g gT lieFirstOrderSigmaASwap
        (Equiv.refl (Fin 3)) PT -
      lieFirstOrderPiece (I := I) (M := M) g gU lieFirstOrderSigmaASwap
        (Equiv.refl (Fin 3)) PU
  let Z0 : ℝ := Cp * (Tb * 0 + (Ct * N) * F0)
  let Z1 : ℝ := Cp * (Tb * (Bp * N) + (Ct * N) * Pp)
  have hZ0 : 0 ≤ Z0 := by
    dsimp only [Z0]
    positivity
  have hZ1 : 0 ≤ Z1 := by
    dsimp only [Z1]
    positivity
  have hV0 : covariantJetNormSq (I := I) (M := M) g 2 V0 ≤ Z0 ^ 2 := by
    simpa only [V0, Z0] using
      hpiece gT gU lieFirstOrderSigmaC lieFirstOrderRhoSlot0 F F
        Tb (Ct * N) F0 0 hTb (mul_nonneg hCt hN) hF0
        (by norm_num) (hTrU lieFirstOrderSigmaC) (hTrD lieFirstOrderSigmaC)
        hFs hFF
  have hV1 : covariantJetNormSq (I := I) (M := M) g 2 V1 ≤ Z1 ^ 2 := by
    simpa only [V1, Z1] using
      hpiece gT gU lieFirstOrderSigmaA (Equiv.refl (Fin 3)) PT PU
        Tb (Ct * N) Pp (Bp * N) hTb (mul_nonneg hCt hN) hPp
        (mul_nonneg hBp hN) (hTrU lieFirstOrderSigmaA)
        (hTrD lieFirstOrderSigmaA) hPT hPD
  have hV2 : covariantJetNormSq (I := I) (M := M) g 2 V2 ≤ Z1 ^ 2 := by
    simpa only [V2, Z1] using
      hpiece gT gU lieFirstOrderSigmaASwap (Equiv.refl (Fin 3)) PT PU
        Tb (Ct * N) Pp (Bp * N) hTb (mul_nonneg hCt hN) hPp
        (mul_nonneg hBp hN) (hTrU lieFirstOrderSigmaASwap)
        (hTrD lieFirstOrderSigmaASwap) hPT hPD
  have hcorr :
      (deTurckLieFirstOrderCoeff (I := I) (M := M) g gT gB -
          deTurckLieFirstOrderCoeff (I := I) (M := M) g gT g) -
        (deTurckLieFirstOrderCoeff (I := I) (M := M) g gU gB -
          deTurckLieFirstOrderCoeff (I := I) (M := M) g gU g) =
      V0 + V1 + V2 := by
    rw [deTurckLieFirstOrderCoefficient_backgroundDifference_decomposition (I := I) (M := M) g gT gB,
      deTurckLieFirstOrderCoefficient_backgroundDifference_decomposition (I := I) (M := M) g gU gB]
    dsimp only [V0, V1, V2, PT, PU, F]
    module
  rw [hcorr]
  change covariantJetNormSq (I := I) (M := M) g 2 (V0 + V1 + V2) ≤
    (B * N) ^ 2
  calc
    covariantJetNormSq (I := I) (M := M) g 2 (V0 + V1 + V2) ≤
        2 * (covariantJetNormSq (I := I) (M := M) g 2 (V0 + V1) +
          covariantJetNormSq (I := I) (M := M) g 2 V2) :=
      covariantJetNormSq_add_le (I := I) (M := M) g 2 (V0 + V1) V2
    _ ≤ 2 * (2 * (covariantJetNormSq (I := I) (M := M) g 2 V0 +
          covariantJetNormSq (I := I) (M := M) g 2 V1) +
        covariantJetNormSq (I := I) (M := M) g 2 V2) := by
      exact mul_le_mul_of_nonneg_left
        (add_le_add (covariantJetNormSq_add_le (I := I) (M := M) g 2 V0 V1) le_rfl)
        (by norm_num)
    _ ≤ 2 * (2 * (Z0 ^ 2 + Z1 ^ 2) + Z1 ^ 2) := by
      exact mul_le_mul_of_nonneg_left
        (add_le_add
          (mul_le_mul_of_nonneg_left (add_le_add hV0 hV1) (by norm_num))
          hV2) (by norm_num)
    _ ≤ 4 * (Z0 ^ 2 + Z1 ^ 2 + Z1 ^ 2) := by
      nlinarith [sq_nonneg Z1]
    _ ≤ (2 * (Z0 + Z1 + Z1)) ^ 2 := by
      nlinarith [sq_nonneg Z0, sq_nonneg Z1, mul_nonneg hZ0 hZ1]
    _ = (B * N) ^ 2 := by
      simp only [Z0, Z1, B]
      ring


theorem exists_deTurckLieFirstOrderCoefficient_backgroundDifference_pairing_secondOrder_bound
    (hDim : Module.finrank ℝ E = 3)
    (g gB : SmoothRiemannianMetric I M) :
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
          (deTurckLieFirstOrderCoeff (I := I) (M := M) g gT gB -
            deTurckLieFirstOrderCoeff (I := I) (M := M) g gU gB) ≤
        (B0 * D3 + B1 * D2 + B1 * A * D2) ^ 2 := by
  obtain ⟨ρs, L0, L1, hρs, hL0, hL1, hsame⟩ :=
    deTurckLieFirstOrder_pairing_h2_bound (I := I) (M := M) hDim g
  obtain ⟨ρc, C, hρc, hC, hcorr⟩ :=
    exists_deTurckLieFirstOrderCoefficient_backgroundDifference_difference_covariantJetNormSq_two_bound (I := I) (M := M) hDim g gB
      (δ₀ := (1 : ℝ) / 3) (by norm_num) (by norm_num)
  let ρ : ℝ := min ρs ρc
  let B0 : ℝ := 2 * L0
  let B1 : ℝ := 2 * (L1 + C)
  have hρ : 0 < ρ := lt_min hρs hρc
  have hB0 : 0 ≤ B0 := mul_nonneg (by norm_num) hL0
  have hB1 : 0 ≤ B1 :=
    mul_nonneg (by norm_num) (add_nonneg hL1 hC)
  refine ⟨ρ, B0, B1, hρ, hB0, hB1, ?_⟩
  intro gT gU T U hT hU hTtie hUtie
    δ hδ_le hδ0 hδT hδU hTHs hUHs A D3 hA hD3 hT3 hTU3
  dsimp only
  let N : ℝ :=
    ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) (T - U)‖
  let S : ℝ := L0 * D3 + L1 * N + L1 * A * N
  let X : SmoothCcTensor g 3 2 :=
    deTurckLieFirstOrderCoeff (I := I) (M := M) g gT g -
      deTurckLieFirstOrderCoeff (I := I) (M := M) g gU g
  let Y : SmoothCcTensor g 3 2 :=
    (deTurckLieFirstOrderCoeff (I := I) (M := M) g gT gB -
        deTurckLieFirstOrderCoeff (I := I) (M := M) g gT g) -
      (deTurckLieFirstOrderCoeff (I := I) (M := M) g gU gB -
        deTurckLieFirstOrderCoeff (I := I) (M := M) g gU g)
  have hN : 0 ≤ N := norm_nonneg _
  have hS : 0 ≤ S := by
    dsimp only [S]
    positivity
  have hTHss : ‖ccTensorToHs (I := I) (M := M) g 2
      (2 : ℝ) T‖ ≤ ρs := hTHs.trans (min_le_left _ _)
  have hUHss : ‖ccTensorToHs (I := I) (M := M) g 2
      (2 : ℝ) U‖ ≤ ρs := hUHs.trans (min_le_left _ _)
  have hTHsc : ‖ccTensorToHs (I := I) (M := M) g 2
      (2 : ℝ) T‖ ≤ ρc := hTHs.trans (min_le_right _ _)
  have hUHsc : ‖ccTensorToHs (I := I) (M := M) g 2
      (2 : ℝ) U‖ ≤ ρc := hUHs.trans (min_le_right _ _)
  have hX : covariantJetNormSq (I := I) (M := M) g 2 X ≤ S ^ 2 := by
    simpa only [X, S, N] using
      hsame gT gU T U hT hU hTtie hUtie hδ_le hδ0 hδT hδU
        hTHss hUHss A D3 hA hD3 hT3 hTU3
  have hY : covariantJetNormSq (I := I) (M := M) g 2 Y ≤ (C * N) ^ 2 := by
    simpa only [Y, N] using
      hcorr gT gU T U hT hU hTtie hUtie
        hδ_le hδ0 hδT hδ_le hδ0 hδU hTHsc hUHsc
  have hsplit :
      deTurckLieFirstOrderCoeff (I := I) (M := M) g gT gB -
          deTurckLieFirstOrderCoeff (I := I) (M := M) g gU gB =
        X + Y := by
    dsimp only [X, Y]
    module
  have hlin : 2 * (S + C * N) ≤
      B0 * D3 + B1 * N + B1 * A * N := by
    dsimp only [S, B0, B1]
    nlinarith [mul_nonneg hC hN,
      mul_nonneg hC (mul_nonneg hA hN)]
  rw [hsplit]
  calc
    covariantJetNormSq (I := I) (M := M) g 2 (X + Y) ≤
        2 * (covariantJetNormSq (I := I) (M := M) g 2 X +
          covariantJetNormSq (I := I) (M := M) g 2 Y) :=
      covariantJetNormSq_add_le (I := I) (M := M) g 2 X Y
    _ ≤ 2 * (S ^ 2 + (C * N) ^ 2) :=
      mul_le_mul_of_nonneg_left (add_le_add hX hY) (by norm_num)
    _ ≤ (2 * (S + C * N)) ^ 2 := by
      nlinarith [sq_nonneg S, sq_nonneg (C * N),
        mul_nonneg hS (mul_nonneg hC hN)]
    _ ≤ (B0 * D3 + B1 * N + B1 * A * N) ^ 2 :=
      pow_le_pow_left₀
        (mul_nonneg (by norm_num) (add_nonneg hS (mul_nonneg hC hN)))
        hlin 2

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral
