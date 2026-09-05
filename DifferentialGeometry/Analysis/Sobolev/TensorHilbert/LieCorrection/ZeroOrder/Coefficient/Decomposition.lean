import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.DeTurckLie.Coefficient.L2JetBound
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurckCoefficients.LieCorrection.Zero.Splitting
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.MetricPerturbation.CovariantOrderCoefficient.ReindexingNorm
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.RicciDeTurck.Remainder.Coefficient.PerOrderEnvelopes
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.DeTurckLie.FirstOrderTerm.L2JetBound
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.DeTurckVectorField.EndomorphismInsertion.TopOrderSeparation
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.OperatorField.InteriorProductJetBound
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.Derivatives.SlotFree
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.CurvatureCoefficientDifferenceJetTower.PairTrace

noncomputable section

set_option autoImplicit false

open MeasureTheory Set Filter Topology Bundle Manifold DifferentialGeometry.Tensor0SBundle ContinuousLinearMap
open scoped ENNReal NNReal BigOperators Manifold ContDiff

namespace DifferentialGeometry.Integral.Connection

open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Analysis.Spectral.MetricRealization
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
  (deTurckLieEndoTermField deTurckLieEndoTermField_toSection deTurckLieCovariantDerivativeInsertionFib
    reindexCoefficientInputSlots reindexCoefficientInputSlots_toSection reindexCoefficientInputSlotsFiber reindexCoefficientInputSlotsFiber_apply
    domDomCongrFibRank domDomCongrFibRank_apply tensor0SProdKappaFib
    tensor0SProdKappaFib_apply unitModel unitTensor
    metricConnectionDifferenceLoweredFib metricConnectionDifferenceLoweredFib_contMDiff
    metricConnectionDifferenceLoweredFib_toModel)
open DifferentialGeometry.PDE.DeTurck.RicciLinearization
  (metricPerturbationPath convexPerturbation convexPerturbation_gFibreOpBound metricPerturbationPath_inner_of_mem
    Icc_subset_metricPerturbationPathDomain)
open DifferentialGeometry.Analysis.Spectral.DeTurck
open DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Analysis.Elliptic
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Connection.Realization
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator
open LieCorrectionZeroFiberOperators

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
omit [SigmaCompactSpace M] in
theorem deTurckLieEndomorphismTerm_eq_covariantDerivativeInsertion (g₀ g₁ g_bg : SmoothRiemannianMetric I M) :
    deTurckLieEndoTermField (I := I) (M := M) g₀ g₁ g_bg =
      deTurckLieCovariantDerivativeInsertionField (I := I) (M := M) g₀ g₁ g_bg := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rw [deTurckLieEndoTermField_toSection, deTurckLieCovariantDerivativeInsertionField_toSection]

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
omit [SigmaCompactSpace M] in
theorem lieCorrectionZeroInsertion_base_eq_neg_covariantDerivativeInsertion (g₀ g₁ : SmoothRiemannianMetric I M) :
    lieCorrectionZeroInsertion (I := I) (M := M) g₀ g₁ g₀ =
      -deTurckLieCovariantDerivativeInsertionField (I := I) (M := M) g₀ g₁ g₀ := by
  have h := insert_base (I := I) (M := M) g₀ g₁ g₀
  rw [sub_self] at h
  rw [eq_neg_of_add_eq_zero_left h, deTurckLieEndomorphismTerm_eq_covariantDerivativeInsertion]

private theorem lieCorrectionZeroInsertionBase_metricPerturbationPath_perOrder_topOrderSeparated
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ Ktop : ℝ, 0 ≤ Ktop ∧ ∃ Kc : ℕ → ℝ, (∀ i, 0 ≤ Kc i) ∧
      ∀ (T T' : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀)
        (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        {δ' : ℝ} (_hδ'_le : δ' ≤ δ₀)
        (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ'),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ≤ R) →
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ≤ R) →
        ∀ (s : ℝ), s ∈ Set.Icc (0 : ℝ) 1 →
        ∀ (i : ℕ), i ≤ a →
          ‖iteratedCovGrad (I := I) g₀ 2 2 i
              (lieCorrectionZeroInsertion (I := I) (M := M) g₀
                (metricPerturbationPath (I := I) g₀ T T' hδ hδ' s) g₀)‖ ^ 2 ≤
            Ktop * (‖iteratedCovGrad (I := I) g₀ 0 2 (i + 2) T‖ ^ 2 +
              ‖iteratedCovGrad (I := I) g₀ 0 2 (i + 2) T'‖ ^ 2) +
            Kc i * (1 + ∑ j ∈ Finset.range (i + 3),
              (‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ^ 2 +
                ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ^ 2)) := by
  obtain ⟨Ktop, hnn, Kc, hKcnn, h⟩ :=
    deTurckLieCovariantDerivativeInsertionField_metricPerturbationPath_jetL2_perOrder_topOrderSeparated (I := I) (M := M) g₀ g₀ a
      ha_super hR hδ₀
  refine ⟨Ktop, hnn, Kc, hKcnn, ?_⟩
  intro T T' δ hδ_le hδ δ' hδ'_le hδ' hTball hT'ball s hs i hi
  have hb := h T T' hδ_le hδ hδ'_le hδ' hTball hT'ball s hs i hi
  rw [lieCorrectionZeroInsertion_base_eq_neg_covariantDerivativeInsertion, iteratedCovGrad_neg, norm_neg]
  exact hb

private def reindexedCometricDoubleTracePerm : Equiv.Perm (Fin 4) :=
  ⟨![1, 2, 0, 3], ![2, 0, 1, 3], by decide, by decide⟩

noncomputable def reindexedCometricDoubleTrace (g₀ g₁ : SmoothRiemannianMetric I M) :
    SmoothCcTensor g₀ 4 2 :=
  reindexCoefficientInputSlots (I := I) (M := M) g₀ 4 2
    (slotExtend (I := I) (M := M) g₀ 3 1 (cometricCastG0 (I := I) g₀ g₁))
      reindexedCometricDoubleTracePerm

omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] [SigmaCompactSpace M] in
omit [I.Boundaryless] in
theorem reindexedCometricDoubleTrace_toSection (g₀ g₁ : SmoothRiemannianMetric I M) (x : M) :
    (show Tensor0SSpace 4 I x →L[ℝ] Tensor0SSpace 2 I x from
        (reindexedCometricDoubleTrace (I := I) (M := M) g₀ g₁).toSection x) =
      cometricDoubleTraceFib (I := I) g₁ 2 x := by
  classical
  apply ContinuousLinearMap.ext
  intro D
  apply Tensor0SSpace.toModel_injective
  apply ContinuousMultilinearMap.ext
  intro m
  rw [show (m : Fin 2 → E) = Fin.cons (m 0) (Fin.tail m) from (Fin.cons_self_tail m).symm]
  change Tensor0SSpace.toModel
      ((show Tensor0SSpace 4 I x →L[ℝ] Tensor0SSpace 2 I x from
        (reindexCoefficientInputSlots (I := I) (M := M) g₀ 4 2
          (slotExtend (I := I) (M := M) g₀ 3 1 (cometricCastG0 (I := I) g₀ g₁))
          reindexedCometricDoubleTracePerm).toSection x) D) _ = _
  rw [reindexCoefficientInputSlots_toSection, reindexCoefficientInputSlotsFiber_apply, slotExtend_toSection,
    DifferentialGeometry.Analysis.Spectral.slotExtendFib_apply_eval]
  have hcast : (cometricCastG0 (I := I) g₀ g₁).toSection x
      = (cometricDoubleTraceField (I := I) g₁ 1).toSection x := rfl
  rw [hcast, cometricDoubleTraceField_toSection]
  simp only [cometricDoubleTraceFib_toModel, modelDoubleTrace_apply]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [TensorMultilinear.tensor0S_curry_toModel_apply, Tensor0SSpace.toModel_ofModel,
    ContinuousMultilinearMap.domDomCongr_apply]
  refine congrArg _ ?_
  funext i
  fin_cases i <;> rfl

omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M]
    [SigmaCompactSpace M] in
omit [I.Boundaryless] in
theorem reindexedCometricDoubleTrace_eq_pureTrace
    (g₀ g₁ : SmoothRiemannianMetric I M) :
    reindexedCometricDoubleTrace (I := I) (M := M) g₀ g₁ =
      pureTrace (I := I) (M := M) g₀ g₁ 2 := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  change
    (show Tensor0SSpace 4 I x →L[ℝ] Tensor0SSpace 2 I x from
      (reindexedCometricDoubleTrace (I := I) (M := M) g₀ g₁).toSection x) =
    (show Tensor0SSpace 4 I x →L[ℝ] Tensor0SSpace 2 I x from
      (pureTrace (I := I) (M := M) g₀ g₁ 2).toSection x)
  rw [reindexedCometricDoubleTrace_toSection, pureTrace_toSection]

private noncomputable def lieCorrectionZeroRiemannLiftFib (g₀ : SmoothRiemannianMetric I M) (x : M) :
    Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 4 I x :=
  (domDomCongrFibRank (I := I) 4 lieCorrectionZeroRiemPerm2 x).comp
    ((lieCorrectionZeroTraceStep (I := I) g₀ 4 lieCorrectionZeroRiemPerm1 x).comp
      (tensor0SProdKappaFib (I := I) (p := 2) (q := 4) x
        (lieCorrectionZeroRiemLoweredFib (I := I) g₀ x)))

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [SigmaCompactSpace M] in
omit [I.Boundaryless] in
private theorem lieCorrectionZeroRiemannLiftFib_contMDiff (g₀ : SmoothRiemannianMetric I M) :
    ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel 2 4 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel 2 4 ℝ E)
        (E := fun z : M => TensorRSSpace 2 4 I z) x
        (TensorRSSpace.ofCLM (lieCorrectionZeroRiemannLiftFib (I := I) g₀ x))) := by
  classical
  apply contMDiff_clm_section_of_pointwise (I := I) (M := M)
    (F₁ := Tensor0SModel 2 ℝ E) (V₁ := fun x : M => Tensor0SSpace 2 I x)
    (F₂ := Tensor0SModel 4 ℝ E) (V₂ := fun x : M => Tensor0SSpace 4 I x)
    (φ := fun x => lieCorrectionZeroRiemannLiftFib (I := I) g₀ x)
  intro Y
  have hprod := lieCorrectionZero_prod_section_contMDiff (I := I) (p := 2) (q := 4)
    (fun x => Y x) (fun x => lieCorrectionZeroRiemLoweredFib (I := I) g₀ x)
    Y.contMDiff (lieCorrectionZeroRiemLoweredFib_section_contMDiff (I := I) g₀)
  have htr1 := lieCorrectionZeroTraceStep_section_contMDiff (I := I) g₀ 4 lieCorrectionZeroRiemPerm1
    (fun x => tensor0SProdKappaFib (I := I) x (lieCorrectionZeroRiemLoweredFib (I := I) g₀ x) (Y x))
    hprod
  have hddc := lieCorrectionZero_ddc_section_contMDiff (I := I) (d := 4) lieCorrectionZeroRiemPerm2
    (fun x => lieCorrectionZeroTraceStep (I := I) g₀ 4 lieCorrectionZeroRiemPerm1 x
      (tensor0SProdKappaFib (I := I) x (lieCorrectionZeroRiemLoweredFib (I := I) g₀ x) (Y x))) htr1
  refine hddc.congr (fun x => ?_)
  refine congrArg (fun t => TotalSpace.mk' (Tensor0SModel 4 ℝ E)
    (E := fun z : M => Tensor0SSpace 4 I z) x t) ?_
  rw [lieCorrectionZeroRiemannLiftFib]
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, domDomCongrFibRank_apply]

noncomputable def lieCorrectionZeroRiemannLift (g₀ : SmoothRiemannianMetric I M) :
    SmoothCcTensor g₀ 2 4 where
  toSection :=
    { toFun := fun x : M =>
        (show TensorRSSpace 2 4 I x from
          TensorRSSpace.ofCLM (lieCorrectionZeroRiemannLiftFib (I := I) g₀ x))
      contMDiff_toFun := lieCorrectionZeroRiemannLiftFib_contMDiff (I := I) g₀ }
  hasCompactSupport := HasCompactSupport.of_compactSpace _

omit [SigmaCompactSpace M] in
omit [I.Boundaryless] in
private lemma lieCorrectionZeroRiemannLift_sum
    (g : SmoothRiemannianMetric I M) (x : M)
    (D : Tensor0SSpace 2 I x) (v : Fin 4 → E) :
    Tensor0SSpace.toModel
        ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 4 I x from
          (lieCorrectionZeroRiemannLift (I := I) (M := M) g).toSection x) D) v =
      ∑ e : Fin (Module.finrank ℝ E),
        Tensor0SSpace.toModel D
            ![tangentSpaceModelContinuousLinearEquiv (I := I) x
                (smoothOrthoFrame (I := I) g x e x), v 1] *
          g.inner x
            (riemannOp (LeviCivita (I := I) g) x
              ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm (v 2))
              ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm (v 3))
              ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm (v 0)))
            (smoothOrthoFrame (I := I) g x e x) := by
  classical
  set Y : Tensor0SSpace 6 I x :=
    domDomCongrFibRank (I := I) 6 lieCorrectionZeroRiemPerm1 x
      (tensor0SProdKappaFib (I := I) (p := 2) (q := 4) x
        (lieCorrectionZeroRiemLoweredFib (I := I) g x) D) with hY_def
  have hYval : ∀ w : Fin 6 → E,
      Tensor0SSpace.toModel Y w =
        Tensor0SSpace.toModel D ![w 1, w 5] *
          g.inner x
            (riemannOp (LeviCivita (I := I) g) x
              ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm (w 2))
              ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm (w 3))
              ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm (w 4)))
            ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm (w 0)) := by
    intro w
    rw [hY_def, domDomCongrFibRank_apply,
      Tensor0SSpace.toModel_ofModel,
      ContinuousMultilinearMap.domDomCongr_apply,
      tensor0SProdKappaFib_apply,
      Tensor0SSpace.toModel_ofModel,
      Bundle.continuousMultilinearMap.modelProduct_apply]
    have hDargs :
        ((fun i : Fin 6 ↦ w (lieCorrectionZeroRiemPerm1 i)) ∘
            Fin.castAdd 4) =
          ![w 1, w 5] := by
      funext i
      fin_cases i <;> rfl
    have hRargs :
        ((fun i : Fin 6 ↦ w (lieCorrectionZeroRiemPerm1 i)) ∘
            Fin.natAdd 2) =
          ![w 2, w 3, w 4, w 0] := by
      funext i
      fin_cases i <;> rfl
    rw [hDargs, hRargs]
    have hR := lieCorrectionZeroRiemLoweredFib_toModel (I := I) g x
      (fun i ↦ (tangentSpaceModelContinuousLinearEquiv (I := I) x).symm
        (![w 2, w 3, w 4, w 0] i))
    apply congrArg (fun t : ℝ ↦ Tensor0SSpace.toModel D ![w 1, w 5] * t)
    convert hR using 1 <;> with_unfolding_all rfl
  change Tensor0SSpace.toModel
      (lieCorrectionZeroRiemannLiftFib (I := I) g x D) v = _
  rw [lieCorrectionZeroRiemannLiftFib, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.comp_apply,
    domDomCongrFibRank_apply,
    Tensor0SSpace.toModel_ofModel,
    ContinuousMultilinearMap.domDomCongr_apply]
  have htop :
      (fun i : Fin 4 ↦ v (lieCorrectionZeroRiemPerm2 i)) =
        ![v 2, v 3, v 0, v 1] := by
    funext i
    fin_cases i <;> rfl
  rw [htop]
  rw [lieCorrectionZeroTraceStep, ContinuousLinearMap.comp_apply, ← hY_def]
  rw [cometricDoubleTraceFib_eq_orthoFrame_diag
    (I := I) g 4 x
    (mem_smoothOrthoFrameNeighborhood_self (I := I) (M := M) x) Y]
  rw [← Tensor0SSpace.toModelL_apply, map_sum,
    sum_apply]
  refine Finset.sum_congr rfl (fun e _ ↦ ?_)
  rw [Tensor0SSpace.toModelL_apply]
  rw [TensorMultilinear.tensor0S_curry_toModel_apply_tangent
        (I := I) (M := M) (n := 4),
      TensorMultilinear.tensor0S_curry_toModel_apply_tangent
        (I := I) (M := M) (n := 5)]
  rw [hYval]
  rfl

omit [SigmaCompactSpace M] in
omit [I.Boundaryless] in
theorem lieCorrectionZeroRiemannLift_toModel
    (g : SmoothRiemannianMetric I M) (x : M)
    (D : Tensor0SSpace 2 I x) (v : Fin 4 → E) :
    Tensor0SSpace.toModel
        ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 4 I x from
          (lieCorrectionZeroRiemannLift (I := I) (M := M) g).toSection x) D) v =
      Tensor0SSpace.toModel D
        ![tangentSpaceModelContinuousLinearEquiv (I := I) x
            (riemannOp (LeviCivita (I := I) g) x
              ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm (v 2))
              ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm (v 3))
              ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm (v 0))),
          v 1] := by
  classical
  rw [lieCorrectionZeroRiemannLift_sum]
  let Rv : TangentSpace I x :=
    riemannOp (LeviCivita (I := I) g) x
      ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm (v 2))
      ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm (v 3))
      ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm (v 0))
  let B : Fin (Module.finrank ℝ E) → TangentSpace I x :=
    fun e ↦ smoothOrthoFrame (I := I) g x e x
  change
    (∑ e, Tensor0SSpace.toModel D
          ![tangentSpaceModelContinuousLinearEquiv (I := I) x (B e), v 1] *
        g.inner x Rv (B e)) =
      Tensor0SSpace.toModel D
        ![tangentSpaceModelContinuousLinearEquiv (I := I) x Rv, v 1]
  have hpair (z : E) :
      (![z, v 1] : Fin 2 → E) =
        Fin.cons z (fun _ : Fin 1 ↦ v 1) := by
    funext i
    fin_cases i <;> rfl
  have hrep :
      Rv = ∑ e, g.inner x (B e) Rv • B e := by
    simpa only [B] using
      CurvatureCoefficientDifferenceJetTower.orthoFrame_center_repr
        (I := I) (M := M) g x Rv
  have hrepModel :
      tangentSpaceModelContinuousLinearEquiv (I := I) x Rv =
        ∑ e, g.inner x (B e) Rv •
          tangentSpaceModelContinuousLinearEquiv (I := I) x (B e) := by
    simpa only [map_sum, map_smul] using congrArg
      (tangentSpaceModelContinuousLinearEquiv (I := I) x) hrep
  calc
    _ = ∑ e, g.inner x (B e) Rv *
          Tensor0SSpace.toModel D
            ![tangentSpaceModelContinuousLinearEquiv (I := I) x (B e), v 1] := by
      refine Finset.sum_congr rfl (fun e _ ↦ ?_)
      rw [g.symm x Rv (B e), mul_comm]
    _ = ∑ e, g.inner x (B e) Rv *
          Tensor0SSpace.toModel D
            (Fin.cons (tangentSpaceModelContinuousLinearEquiv (I := I) x (B e))
              (fun _ : Fin 1 ↦ v 1)) := by
      refine Finset.sum_congr rfl (fun e _ ↦ ?_)
      rw [hpair]
    _ = Tensor0SSpace.toModel D
          (Fin.cons
            (∑ e, g.inner x (B e) Rv •
              tangentSpaceModelContinuousLinearEquiv (I := I) x (B e))
            (fun _ : Fin 1 ↦ v 1)) :=
      (CurvatureCoefficientDifferenceJetTower.toModel_cons_sum_smul
        (E := E)
        (Tensor0SSpace.toModel D)
        (Module.finrank ℝ E)
        (fun e ↦ g.inner x (B e) Rv)
        (fun e ↦ tangentSpaceModelContinuousLinearEquiv (I := I) x (B e))
        (fun _ : Fin 1 ↦ v 1)).symm
    _ = Tensor0SSpace.toModel D
          ![(∑ e, g.inner x (B e) Rv •
            tangentSpaceModelContinuousLinearEquiv (I := I) x (B e)), v 1] := by
      rw [hpair]
    _ = _ := by
      rw [← hrepModel]

omit [NeZero (Module.finrank ℝ E)] in
omit [I.Boundaryless] [SigmaCompactSpace M] in
private lemma lieCorrectionZeroRiemannDecomposition_toModel
    (g : SmoothRiemannianMetric I M) (x : M)
    (D : Tensor0SSpace 2 I x) (v : Fin 4 → E) :
    Tensor0SSpace.toModel
        ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 4 I x from
          (rsDomDomCongrSection (I := I) (M := M) g 2 4
            lieCorrectionZeroVectorBundleTracePermutation
            (reindexCoefficientInputSlots (I := I) (M := M) g 2 4
              (slotExtendIter (I := I) (M := M) g 1 3 1
                (slotFreeOpCc (I := I) (M := M) g 1))
              (Equiv.swap (0 : Fin 2) 1))).toSection x) D) v =
      -Tensor0SSpace.toModel D
        ![tangentSpaceModelContinuousLinearEquiv (I := I) x
            (riemannOp (LeviCivita (I := I) g) x
              ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm (v 2))
              ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm (v 3))
              ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm (v 0))),
          v 1] := by
  classical
  let Rv : TangentSpace I x :=
    riemannOp (LeviCivita (I := I) g) x
      ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm (v 2))
      ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm (v 3))
      ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm (v 0))
  rw [rsDomDomCongrSection_toSection,
    toModel_rsDomDomCongr_apply,
    ContinuousMultilinearMap.domDomCongr_apply]
  have hout :
      (fun i : Fin 4 ↦ v (lieCorrectionZeroVectorBundleTracePermutation i)) =
        ![v 1, v 2, v 3, v 0] := by
    funext i
    fin_cases i <;> rfl
  rw [hout]
  simp only [slotExtendIter, Nat.add_zero]
  set D' : Tensor0SSpace 2 I x :=
    Tensor0SSpace.ofModel (I := I) (x := x)
      (ContinuousMultilinearMap.domDomCongr
        (Equiv.swap (0 : Fin 2) 1)
        (Tensor0SSpace.toModel D)) with hD'_def
  have hreindex :
      ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 4 I x from
        (reindexCoefficientInputSlots (I := I) (M := M) g 2 4
          (slotExtend (I := I) (M := M) g 1 3
            (slotFreeOpCc (I := I) (M := M) g 1))
          (Equiv.swap (0 : Fin 2) 1)).toSection x) D) =
        slotExtendFib (I := I) (M := M) 1 3 x
          (show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 3 I x from
            (slotFreeOpCc (I := I) (M := M) g 1).toSection x) D' := by
    rw [hD'_def]
    exact reindexCoefficientInputSlotsFiber_apply
      (I := I) 2 4 (Equiv.swap (0 : Fin 2) 1) x _ D
  rw [hreindex]
  rw [show
    (![v 1, v 2, v 3, v 0] : Fin 4 → E) =
      Fin.cons (v 1)
        (![v 2, v 3, v 0] : Fin 3 → E) from by
    funext i
    fin_cases i <;> rfl]
  rw [slotExtendFib_apply_eval
    (I := I) (M := M) 1 3 x
    (show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 3 I x from
      (slotFreeOpCc (I := I) (M := M) g 1).toSection x)
    D' (v 1) (![v 2, v 3, v 0] : Fin 3 → E)]
  let A : Tensor0SSpace 1 I x :=
    tensor0SCurry (I := I) (M := M) (𝕜 := ℝ) 1 x D'
      ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm (v 1))
  let m : Fin 1 → TangentSpace I x := fun _ ↦
    (tangentSpaceModelContinuousLinearEquiv (I := I) x).symm (v 0)
  let mE : Fin 1 → E := fun _ ↦ v 0
  have hcurv :
      (![v 2, v 3, v 0] : Fin 3 → E) =
        Fin.cons (v 2) (Fin.cons (v 3) mE) := by
    funext i
    fin_cases i <;> rfl
  have hpair :
      ![tangentSpaceModelContinuousLinearEquiv (I := I) x Rv, v 1] =
        Fin.cons (tangentSpaceModelContinuousLinearEquiv (I := I) x Rv)
          (fun _ : Fin 1 ↦ v 1) := by
    funext i
    fin_cases i <;> rfl
  rw [hcurv, hpair]
  change
    Tensor0SSpace.toModel
        ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 3 I x from
          (slotFreeOpCc (I := I) (M := M) g 1).toSection x) A)
        (Fin.cons (v 2) (Fin.cons (v 3) mE)) =
      -Tensor0SSpace.toModel D
        (Fin.cons (tangentSpaceModelContinuousLinearEquiv (I := I) x Rv)
          (fun _ : Fin 1 ↦ v 1))
  have hsf :
      Tensor0SSpace.toModel
          ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 3 I x from
            (slotFreeOpCc (I := I) (M := M) g 1).toSection x) A)
          (Fin.cons (v 2) (Fin.cons (v 3) mE)) =
        -Tensor0SSpace.toModel A
          (Function.update mE 0
            (tangentSpaceModelContinuousLinearEquiv (I := I) x Rv)) := by
    rw [slotFreeOpCc_apply]
    have hraw := slotFreeCurvOpFib_apply_eval
      (I := I) (M := M) g 1 x A
      ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm (v 2))
      ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm (v 3)) m
    simp only [← Tensor0SSpace.toModel_apply_tangent] at hraw
    have hinput :
        (fun i ↦ tangentSpaceModelContinuousLinearEquiv (I := I) x
          ((Fin.cons ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm (v 2))
            (Fin.cons ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm (v 3)) m) :
              Fin 3 → TangentSpace I x) i)) =
          Fin.cons (v 2) (Fin.cons (v 3) mE) := by
      funext i
      fin_cases i <;> with_unfolding_all rfl
    have hupdate :
        (fun i ↦ tangentSpaceModelContinuousLinearEquiv (I := I) x
          (Function.update m 0 Rv i)) =
          Function.update mE 0
            (tangentSpaceModelContinuousLinearEquiv (I := I) x Rv) := by
      funext i
      fin_cases i
      with_unfolding_all rfl
    rw [hinput] at hraw
    simp only [Fin.sum_univ_one] at hraw
    rw [hupdate] at hraw
    exact hraw
  rw [hsf]
  have hupd :
      Function.update mE (0 : Fin 1)
          (tangentSpaceModelContinuousLinearEquiv (I := I) x Rv) =
        fun _ : Fin 1 ↦
          tangentSpaceModelContinuousLinearEquiv (I := I) x Rv := by
    funext i
    fin_cases i
    simp
  rw [hupd]
  change
    -Tensor0SSpace.toModel
        (tensor0SCurry (I := I) (M := M) (𝕜 := ℝ) 1 x
          D' ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm (v 1)))
        (fun _ : Fin 1 ↦
          tangentSpaceModelContinuousLinearEquiv (I := I) x Rv) =
      -Tensor0SSpace.toModel D
        (Fin.cons (tangentSpaceModelContinuousLinearEquiv (I := I) x Rv)
          (fun _ : Fin 1 ↦ v 1))
  rw [TensorMultilinear.tensor0S_curry_toModel_apply
      (I := I) (M := M),
    hD'_def, Tensor0SSpace.toModel_ofModel,
    ContinuousMultilinearMap.domDomCongr_apply]
  congr 1
  apply congrArg (Tensor0SSpace.toModel D)
  funext i
  fin_cases i <;> rfl

omit [SigmaCompactSpace M] in
omit [I.Boundaryless] in
theorem lieCorrectionZeroRiemannLift_eq_decomposition
    (g : SmoothRiemannianMetric I M) :
    lieCorrectionZeroRiemannLift (I := I) (M := M) g =
      -rsDomDomCongrSection (I := I) (M := M) g 2 4
        lieCorrectionZeroVectorBundleTracePermutation
        (reindexCoefficientInputSlots (I := I) (M := M) g 2 4
          (slotExtendIter (I := I) (M := M) g 1 3 1
            (slotFreeOpCc (I := I) (M := M) g 1))
          (Equiv.swap (0 : Fin 2) 1)) := by
  classical
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rw [SmoothCcTensor.toSection_neg,
    ContMDiffSection.coe_neg, Pi.neg_apply]
  apply ContinuousLinearMap.ext
  intro D
  apply Tensor0SSpace.toModel_injective
  apply ContinuousMultilinearMap.ext
  intro v
  change Tensor0SSpace.toModel
      ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 4 I x from
        (lieCorrectionZeroRiemannLift (I := I) (M := M) g).toSection x) D) v =
    Tensor0SSpace.toModel
      (-((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 4 I x from
        (rsDomDomCongrSection (I := I) (M := M) g 2 4
          lieCorrectionZeroVectorBundleTracePermutation
          (reindexCoefficientInputSlots (I := I) (M := M) g 2 4
            (slotExtendIter (I := I) (M := M) g 1 3 1
              (slotFreeOpCc (I := I) (M := M) g 1))
            (Equiv.swap (0 : Fin 2) 1))).toSection x) D)) v
  rw [Tensor0SSpace.toModel_neg,
    neg_apply,
    lieCorrectionZeroRiemannLift_toModel,
    lieCorrectionZeroRiemannDecomposition_toModel]
  ring

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
omit [I.Boundaryless] in
private theorem lieCorrectionZeroRiemannFib_eq (g₀ g₁ : SmoothRiemannianMetric I M) (x : M) :
    lieCorrectionZeroRiemFib (I := I) g₀ g₁ x =
      -((show Tensor0SSpace 4 I x →L[ℝ] Tensor0SSpace 2 I x from
            (reindexedCometricDoubleTrace (I := I) (M := M) g₀ g₁).toSection x).comp
        (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 4 I x from
            (lieCorrectionZeroRiemannLift (I := I) g₀).toSection x)) := by
  rw [lieCorrectionZeroRiemFib, reindexedCometricDoubleTrace_toSection, neg_one_smul]
  rfl

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
omit [I.Boundaryless] in
theorem lieCorrectionZeroRiemann_eq_ccOperatorFieldComp (g₀ g₁ : SmoothRiemannianMetric I M) :
    lieCorrectionZeroRiemann (I := I) (M := M) g₀ g₁ =
      -ccOperatorFieldComp (I := I) (M := M) g₀ 2 4 2
        (reindexedCometricDoubleTrace (I := I) (M := M) g₀ g₁) (lieCorrectionZeroRiemannLift (I := I) g₀) := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rw [SmoothCcTensor.toSection_neg, ContMDiffSection.coe_neg, Pi.neg_apply, operatorFieldComposition_toSection]
  exact lieCorrectionZeroRiemannFib_eq (I := I) (M := M) g₀ g₁ x

omit [SigmaCompactSpace M] in
theorem riemannianFiberNormSq_iteratedCovGrad_reindexedCometricDoubleTrace_le (g₀ g₁ : SmoothRiemannianMetric I M) (m : ℕ) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g₀ 4 (2 + m) x
        ((iteratedCovGrad (I := I) g₀ 4 2 m
          (reindexedCometricDoubleTrace (I := I) (M := M) g₀ g₁)).toSection x) ≤
      (Module.finrank ℝ E : ℝ) *
        riemannianFiberNormSq (I := I) (M := M) g₀ 3 (1 + m) x
          ((iteratedCovGrad (I := I) g₀ 3 1 m (cometricCastG0 (I := I) g₀ g₁)).toSection x) := by
  rw [reindexedCometricDoubleTrace, riemannianFiberNormSq_iteratedCovGrad_reindexCoefficientInputSlots_eq]
  exact riemannianFiberNormSq_iteratedCovGrad_slotExtend_le (I := I) (M := M) g₀ 3 1
    (cometricCastG0 (I := I) g₀ g₁) m x

theorem norm_iteratedCovGrad_reindexedCometricDoubleTrace_sq_le (g₀ g₁ : SmoothRiemannianMetric I M) (m : ℕ) :
    ‖iteratedCovGrad (I := I) g₀ 4 2 m (reindexedCometricDoubleTrace (I := I) (M := M) g₀ g₁)‖ ^ 2 ≤
      (Module.finrank ℝ E : ℝ) *
        ‖iteratedCovGrad (I := I) g₀ 3 1 m (cometricCastG0 (I := I) g₀ g₁)‖ ^ 2 := by
  have hint : MeasureTheory.Integrable
      (fun x => (Module.finrank ℝ E : ℝ) *
        riemannianFiberNormSq (I := I) (M := M) g₀ 3 (1 + m) x
          ((iteratedCovGrad (I := I) g₀ 3 1 m (cometricCastG0 (I := I) g₀ g₁)).toSection x))
      (riemannianVolumeMeasure (I := I) (M := M) g₀) :=
    (integrable_riemannianFiberNormSq_toSection (I := I) (M := M) g₀ 3 (1 + m)
      (iteratedCovGrad (I := I) g₀ 3 1 m (cometricCastG0 (I := I) g₀ g₁))).const_mul _
  have key := normSq_le_integral_of_pointwise_fiberNormSq_le_rs (I := I) (M := M) g₀ 4 (2 + m)
    (iteratedCovGrad (I := I) g₀ 4 2 m (reindexedCometricDoubleTrace (I := I) (M := M) g₀ g₁)) _ hint
    (fun x => riemannianFiberNormSq_iteratedCovGrad_reindexedCometricDoubleTrace_le (I := I) (M := M) g₀ g₁ m x)
  refine le_trans key (le_of_eq ?_)
  rw [MeasureTheory.integral_const_mul]
  refine congrArg _ ?_
  rw [← tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs (I := I) (M := M) g₀ 3 (1 + m)
      (iteratedCovGrad (I := I) g₀ 3 1 m (cometricCastG0 (I := I) g₀ g₁)),
    ← SmoothCcTensor.norm_def]

private theorem lieCorrectionZeroRiem_metricPerturbationPath_perOrder_topOrderSeparation
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ Ktop : ℝ, 0 ≤ Ktop ∧ ∃ Kc : ℕ → ℝ, (∀ i, 0 ≤ Kc i) ∧
      ∀ (T T' : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀)
        (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        {δ' : ℝ} (_hδ'_le : δ' ≤ δ₀)
        (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ'),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ≤ R) →
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ≤ R) →
        ∀ (s : ℝ), s ∈ Set.Icc (0 : ℝ) 1 →
        ∀ (i : ℕ), i ≤ a →
          ‖iteratedCovGrad (I := I) g₀ 2 2 i
              (lieCorrectionZeroRiemann (I := I) (M := M) g₀
                (metricPerturbationPath (I := I) g₀ T T' hδ hδ' s))‖ ^ 2 ≤
            Ktop * (‖iteratedCovGrad (I := I) g₀ 0 2 (i + 2) T‖ ^ 2 +
              ‖iteratedCovGrad (I := I) g₀ 0 2 (i + 2) T'‖ ^ 2) +
            Kc i * (1 + ∑ j ∈ Finset.range (i + 3),
              (‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ^ 2 +
                ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ^ 2)) := by
  classical
  obtain ⟨Λ, F, hΛ_nn, hF_nn, hcom⟩ :=
    cometricDoubleTraceField_order0sup_jetL2_ballUniform (I := I) (M := M) g₀ a
      ha_super hR hδ₀
  obtain ⟨KP, hKP_nn, hKP⟩ := exists_bound_riemannianFiberNormSq_smoothCcTensor
    (I := I) (M := M) g₀ 2 4 (lieCorrectionZeroRiemannLift (I := I) g₀)
  choose Cint hCint_nn hCint using
    (fun k : ℕ => exists_integrated_iteratedCovGrad_diagonalProductGrid_twoTerm_rs_le
      (I := I) (M := M) g₀ 4 2 2 4 k)
  set fr : ℝ := (Module.finrank ℝ E : ℝ) with hfr
  have hfr_nn : (0 : ℝ) ≤ fr := Nat.cast_nonneg _
  set NPass : ℕ → ℝ := fun i => ∑ l ∈ Finset.range (i + 1),
    ‖iteratedCovGrad (I := I) g₀ 2 4 l (lieCorrectionZeroRiemannLift (I := I) g₀)‖ ^ 2 with hNPass
  have hNPass_nn : ∀ i, 0 ≤ NPass i := fun i =>
    Finset.sum_nonneg (fun l _ => sq_nonneg _)
  refine ⟨0, le_refl 0, fun i => operatorFieldApplicationGdiag (E := E) i *
    (Cint i * (KP * (fr * F i) + fr * Λ ^ 2 * NPass i)), fun i => ?_, ?_⟩
  · exact mul_nonneg (operatorFieldApplicationGdiag_nonneg (E := E) i)
      (mul_nonneg (hCint_nn i)
        (add_nonneg (mul_nonneg hKP_nn (mul_nonneg hfr_nn (hF_nn i)))
          (mul_nonneg (mul_nonneg hfr_nn (sq_nonneg Λ)) (hNPass_nn i))))
  intro T T' δ hδ_le hδ δ' hδ'_le hδ' hTball hT'ball s hs i hi
  have hs0 : (0 : ℝ) ≤ s := hs.1
  have hs1 : s ≤ 1 := hs.2
  have h1ms : (0 : ℝ) ≤ 1 - s := by linarith
  have hδ_lt : δ < 1 := lt_of_le_of_lt hδ_le hδ₀
  have hδ'_lt : δ' < 1 := lt_of_le_of_lt hδ'_le hδ₀
  have hδP : gFibreOpBound (I := I) (M := M) g₀
      (ccTensorBilinSymm (I := I) g₀ (convexPerturbation (I := I) g₀ T T' s))
      ((1 - s) * δ' + s * δ) :=
    convexPerturbation_gFibreOpBound (I := I) (M := M) g₀ T T' hδ hδ' hs0 hs1
  have hδP_le : (1 - s) * δ' + s * δ ≤ δ₀ := by
    have e1 : (1 - s) * δ' ≤ (1 - s) * δ₀ := mul_le_mul_of_nonneg_left hδ'_le h1ms
    have e2 : s * δ ≤ s * δ₀ := mul_le_mul_of_nonneg_left hδ_le hs0
    have e3 : (1 - s) * δ₀ + s * δ₀ = δ₀ := by ring
    linarith [e1, e2, e3]
  have htie : ∀ (y : M) (v w : TangentSpace I y),
      (metricPerturbationPath (I := I) g₀ T T' hδ hδ' s).inner y v w =
        g₀.inner y v w +
          ccTensorBilinSymm (I := I) g₀ (convexPerturbation (I := I) g₀ T T' s) y v w :=
    fun y v w =>
      metricPerturbationPath_inner_of_mem (I := I) g₀ T T' hδ hδ'
        (Icc_subset_metricPerturbationPathDomain hδ_lt hδ'_lt hs) y v w
  have hPball : ∀ j : ℕ, j ≤ a + 2 →
      ‖iteratedCovGrad (I := I) g₀ 0 2 j (convexPerturbation (I := I) g₀ T T' s)‖ ≤ R := by
    intro j hj
    have heq : iteratedCovGrad (I := I) g₀ 0 2 j (convexPerturbation (I := I) g₀ T T' s)
        = (1 - s) • iteratedCovGrad (I := I) g₀ 0 2 j T'
          + s • iteratedCovGrad (I := I) g₀ 0 2 j T := by
      rw [show convexPerturbation (I := I) g₀ T T' s = (1 - s) • T' + s • T from rfl,
        iteratedCovGrad_add, iteratedCovGrad_smul, iteratedCovGrad_smul]
    rw [heq]
    calc ‖(1 - s) • iteratedCovGrad (I := I) g₀ 0 2 j T'
            + s • iteratedCovGrad (I := I) g₀ 0 2 j T‖
        ≤ ‖(1 - s) • iteratedCovGrad (I := I) g₀ 0 2 j T'‖
            + ‖s • iteratedCovGrad (I := I) g₀ 0 2 j T‖ := norm_add_le _ _
      _ = (1 - s) * ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖
            + s * ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ := by
          rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
            abs_of_nonneg h1ms, abs_of_nonneg hs0]
      _ ≤ (1 - s) * R + s * R :=
          add_le_add (mul_le_mul_of_nonneg_left (hT'ball j hj) h1ms)
            (mul_le_mul_of_nonneg_left (hTball j hj) hs0)
      _ = R := by ring
  obtain ⟨hsup0, hjet⟩ := hcom (metricPerturbationPath (I := I) g₀ T T' hδ hδ' s)
    (convexPerturbation (I := I) g₀ T T' s) hδP_le hδP htie hPball
  have hLsup : ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 4 2 x
      ((reindexedCometricDoubleTrace (I := I) (M := M) g₀
        (metricPerturbationPath (I := I) g₀ T T' hδ hδ' s)).toSection x) ≤
      Real.sqrt (fr * Λ ^ 2) ^ 2 := by
    intro x
    have h := riemannianFiberNormSq_iteratedCovGrad_reindexedCometricDoubleTrace_le (I := I) (M := M) g₀
      (metricPerturbationPath (I := I) g₀ T T' hδ hδ' s) 0 x
    rw [iteratedCovGrad_zero, iteratedCovGrad_zero] at h
    rw [Real.sq_sqrt (mul_nonneg hfr_nn (sq_nonneg Λ))]
    exact le_trans h (mul_le_mul_of_nonneg_left (hsup0 x) hfr_nn)
  have hPsup : ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 2 4 x
      ((lieCorrectionZeroRiemannLift (I := I) g₀).toSection x) ≤ Real.sqrt KP ^ 2 := by
    intro x
    rw [Real.sq_sqrt hKP_nn]
    exact hKP x
  obtain ⟨hgrid_int, hgrid_bd⟩ := hCint i
    (reindexedCometricDoubleTrace (I := I) (M := M) g₀ (metricPerturbationPath (I := I) g₀ T T' hδ hδ' s))
    (lieCorrectionZeroRiemannLift (I := I) g₀) (Real.sqrt (fr * Λ ^ 2)) (Real.sqrt KP)
    (Real.sqrt_nonneg _) (Real.sqrt_nonneg _) hLsup hPsup
  have hLsum : ∑ m ∈ Finset.range (i + 1),
      ‖iteratedCovGrad (I := I) g₀ 4 2 m
        (reindexedCometricDoubleTrace (I := I) (M := M) g₀
          (metricPerturbationPath (I := I) g₀ T T' hδ hδ' s))‖ ^ 2 ≤ fr * F i := by
    calc ∑ m ∈ Finset.range (i + 1),
          ‖iteratedCovGrad (I := I) g₀ 4 2 m
            (reindexedCometricDoubleTrace (I := I) (M := M) g₀
              (metricPerturbationPath (I := I) g₀ T T' hδ hδ' s))‖ ^ 2
        ≤ ∑ m ∈ Finset.range (i + 1), fr *
            ‖iteratedCovGrad (I := I) g₀ 3 1 m
              (cometricCastG0 (I := I) g₀
                (metricPerturbationPath (I := I) g₀ T T' hδ hδ' s))‖ ^ 2 :=
          Finset.sum_le_sum (fun m _ => norm_iteratedCovGrad_reindexedCometricDoubleTrace_sq_le (I := I) (M := M) g₀ _ m)
      _ = fr * ∑ m ∈ Finset.range (i + 1),
            ‖iteratedCovGrad (I := I) g₀ 3 1 m
              (cometricCastG0 (I := I) g₀
                (metricPerturbationPath (I := I) g₀ T T' hδ hδ' s))‖ ^ 2 := by
          rw [Finset.mul_sum]
      _ ≤ fr * F i := mul_le_mul_of_nonneg_left (hjet i hi) hfr_nn
  have hnorm : ‖iteratedCovGrad (I := I) g₀ 2 2 i
        (ccOperatorFieldComp (I := I) (M := M) g₀ 2 4 2
          (reindexedCometricDoubleTrace (I := I) (M := M) g₀ (metricPerturbationPath (I := I) g₀ T T' hδ hδ' s))
          (lieCorrectionZeroRiemannLift (I := I) g₀))‖ ^ 2 ≤
      operatorFieldApplicationGdiag (E := E) i *
        (Cint i * (Real.sqrt KP ^ 2 * ∑ m ∈ Finset.range (i + 1),
            ‖iteratedCovGrad (I := I) g₀ 4 2 m
              (reindexedCometricDoubleTrace (I := I) (M := M) g₀
                (metricPerturbationPath (I := I) g₀ T T' hδ hδ' s))‖ ^ 2
          + Real.sqrt (fr * Λ ^ 2) ^ 2 * ∑ l ∈ Finset.range (i + 1),
            ‖iteratedCovGrad (I := I) g₀ 2 4 l (lieCorrectionZeroRiemannLift (I := I) g₀)‖ ^ 2)) := by
    have key := normSq_le_integral_of_pointwise_fiberNormSq_le_rs (I := I) (M := M) g₀ 2 (2 + i)
      (iteratedCovGrad (I := I) g₀ 2 2 i
        (ccOperatorFieldComp (I := I) (M := M) g₀ 2 4 2
          (reindexedCometricDoubleTrace (I := I) (M := M) g₀ (metricPerturbationPath (I := I) g₀ T T' hδ hδ' s))
          (lieCorrectionZeroRiemannLift (I := I) g₀))) _ (hgrid_int.const_mul (operatorFieldApplicationGdiag (E := E) i))
      (fun x => riemannianFiberNormSq_iteratedCovGrad_operatorFieldComposition_diagonalProductGrid_rankLeft_le
        (I := I) (M := M) g₀ i 2 4 2
        (reindexedCometricDoubleTrace (I := I) (M := M) g₀ (metricPerturbationPath (I := I) g₀ T T' hδ hδ' s))
        (lieCorrectionZeroRiemannLift (I := I) g₀) x)
    refine le_trans key ?_
    rw [MeasureTheory.integral_const_mul]
    exact mul_le_mul_of_nonneg_left hgrid_bd (operatorFieldApplicationGdiag_nonneg (E := E) i)
  rw [lieCorrectionZeroRiemann_eq_ccOperatorFieldComp, iteratedCovGrad_neg, norm_neg]
  have hKPsq : Real.sqrt KP ^ 2 = KP := Real.sq_sqrt hKP_nn
  have hΛsq : Real.sqrt (fr * Λ ^ 2) ^ 2 = fr * Λ ^ 2 :=
    Real.sq_sqrt (mul_nonneg hfr_nn (sq_nonneg Λ))
  rw [hKPsq, hΛsq] at hnorm
  have hmid : operatorFieldApplicationGdiag (E := E) i *
      (Cint i * (KP * ∑ m ∈ Finset.range (i + 1),
          ‖iteratedCovGrad (I := I) g₀ 4 2 m
            (reindexedCometricDoubleTrace (I := I) (M := M) g₀
              (metricPerturbationPath (I := I) g₀ T T' hδ hδ' s))‖ ^ 2
        + fr * Λ ^ 2 * NPass i)) ≤
      operatorFieldApplicationGdiag (E := E) i * (Cint i * (KP * (fr * F i) + fr * Λ ^ 2 * NPass i)) := by
    refine mul_le_mul_of_nonneg_left ?_ (operatorFieldApplicationGdiag_nonneg (E := E) i)
    refine mul_le_mul_of_nonneg_left ?_ (hCint_nn i)
    have hstep := mul_le_mul_of_nonneg_left hLsum hKP_nn
    linarith
  have hsum_nn : (0 : ℝ) ≤ ∑ j ∈ Finset.range (i + 3),
      (‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ^ 2 +
        ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ^ 2) :=
    Finset.sum_nonneg (fun j _ => add_nonneg (sq_nonneg _) (sq_nonneg _))
  have hKc_nn : (0 : ℝ) ≤ operatorFieldApplicationGdiag (E := E) i *
      (Cint i * (KP * (fr * F i) + fr * Λ ^ 2 * NPass i)) :=
    mul_nonneg (operatorFieldApplicationGdiag_nonneg (E := E) i)
      (mul_nonneg (hCint_nn i)
        (add_nonneg (mul_nonneg hKP_nn (mul_nonneg hfr_nn (hF_nn i)))
          (mul_nonneg (mul_nonneg hfr_nn (sq_nonneg Λ)) (hNPass_nn i))))
  nlinarith only [le_trans hnorm hmid, hsum_nn, hKc_nn]

private theorem sq_le_two_add (t u v c1 c2 : ℝ) (ht : 0 ≤ t) (hu : 0 ≤ u) (hv : 0 ≤ v)
    (htri : t ≤ u + v) (h1 : u ^ 2 ≤ c1) (h2 : v ^ 2 ≤ c2) : t ^ 2 ≤ 2 * (c1 + c2) := by
  have huv : 0 ≤ u + v := by linarith
  nlinarith only [mul_le_mul htri htri ht huv, sq_nonneg (u - v), h1, h2, hu, hv]

omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
omit [CompactSpace M] in
private theorem normSq_iteratedCovGrad_le_scaled (g₀ : SmoothRiemannianMetric I M)
    (X : SmoothCcTensor g₀ 2 2) (Y : SmoothCcTensor g₀ 1 1) (i : ℕ) (c : ℝ)
    (hpt : ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
          ((iteratedCovGrad (I := I) g₀ 2 2 i X).toSection x) ≤
        c * riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + i) x
          ((iteratedCovGrad (I := I) g₀ 1 1 i Y).toSection x)) :
    ‖iteratedCovGrad (I := I) g₀ 2 2 i X‖ ^ 2 ≤
      c * ‖iteratedCovGrad (I := I) g₀ 1 1 i Y‖ ^ 2 := by
  have hF_int : MeasureTheory.Integrable
      (fun x => c * riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + i) x
        ((iteratedCovGrad (I := I) g₀ 1 1 i Y).toSection x))
      (riemannianVolumeMeasure (I := I) (M := M) g₀) :=
    (integrable_riemannianFiberNormSq_toSection (I := I) (M := M) g₀ 1 (1 + i)
      (iteratedCovGrad (I := I) g₀ 1 1 i Y)).const_mul c
  have key := normSq_le_integral_of_pointwise_fiberNormSq_le_rs (I := I) (M := M) g₀ 2 (2 + i)
    (iteratedCovGrad (I := I) g₀ 2 2 i X)
    (fun x => c * riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + i) x
      ((iteratedCovGrad (I := I) g₀ 1 1 i Y).toSection x))
    hF_int (fun x => hpt x)
  refine le_trans key (le_of_eq ?_)
  rw [MeasureTheory.integral_const_mul]
  congr 1
  rw [SmoothCcTensor.norm_def (I := I) (M := M) (iteratedCovGrad (I := I) g₀ 1 1 i Y)]
  exact (tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs (I := I) (M := M) g₀ 1 (1 + i)
    (iteratedCovGrad (I := I) g₀ 1 1 i Y)).symm

def endoDiffSection (g₀ g₁ g_bg : SmoothRiemannianMetric I M) :
    ContMDiffSection I (E →L[ℝ] E) ∞ (fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x) :=
  connectionDifferenceDeTurckVectorFieldSection (I := I) (M := M) g₀ g₁ g₀ -
    connectionDifferenceDeTurckVectorFieldSection (I := I) (M := M) g₀ g₁ g_bg

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
omit [SigmaCompactSpace M] in
private lemma endoDiffSection_apply (g₀ g₁ g_bg : SmoothRiemannianMetric I M) (x : M) :
    endoDiffSection (I := I) (M := M) g₀ g₁ g_bg x =
      lieCorrectionZeroNEndo (I := I) g₀ g₁ g_bg x - lieCorrectionZeroNEndo (I := I) g₀ g₁ g₀ x := by
  simp only [endoDiffSection, ContMDiffSection.coe_sub, Pi.sub_apply]
  exact (nEndo_diff (I := I) (M := M) g₀ g₁ g_bg x).symm

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
omit [SigmaCompactSpace M] in
theorem lieCorrectionZeroInsDiff_eq (g₀ g₁ g_bg : SmoothRiemannianMetric I M) :
    lieCorrectionZeroInsertion (I := I) (M := M) g₀ g₁ g_bg - lieCorrectionZeroInsertion (I := I) (M := M) g₀ g₁ g₀ =
      slotInsertEndoCc (I := I) (M := M) g₀ 1 (endoDiffSection (I := I) (M := M) g₀ g₁ g_bg)
        + reindexCoefficientInputSlots (I := I) (M := M) g₀ 2 2
            (rsDomDomCongrSection (I := I) (M := M) g₀ 2 2 (Equiv.swap (0 : Fin 2) 1)
              (slotInsertEndoCc (I := I) (M := M) g₀ 1
                (endoDiffSection (I := I) (M := M) g₀ g₁ g_bg)))
            (Equiv.swap (0 : Fin 2) 1) := by
  classical
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rw [SmoothCcTensor.toSection_add, ContMDiffSection.coe_add, Pi.add_apply]
  apply ContinuousLinearMap.ext
  intro D
  apply Tensor0SSpace.toModel_injective
  apply ContinuousMultilinearMap.ext
  intro m
  have hsum : (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
        (slotInsertEndoCc (I := I) (M := M) g₀ 1
            (endoDiffSection (I := I) (M := M) g₀ g₁ g_bg)).toSection x
          + (reindexCoefficientInputSlots (I := I) (M := M) g₀ 2 2
              (rsDomDomCongrSection (I := I) (M := M) g₀ 2 2 (Equiv.swap (0 : Fin 2) 1)
                (slotInsertEndoCc (I := I) (M := M) g₀ 1
                  (endoDiffSection (I := I) (M := M) g₀ g₁ g_bg)))
              (Equiv.swap (0 : Fin 2) 1)).toSection x) D
      = (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
          (slotInsertEndoCc (I := I) (M := M) g₀ 1
            (endoDiffSection (I := I) (M := M) g₀ g₁ g_bg)).toSection x) D
        + (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
          (reindexCoefficientInputSlots (I := I) (M := M) g₀ 2 2
              (rsDomDomCongrSection (I := I) (M := M) g₀ 2 2 (Equiv.swap (0 : Fin 2) 1)
                (slotInsertEndoCc (I := I) (M := M) g₀ 1
                  (endoDiffSection (I := I) (M := M) g₀ g₁ g_bg)))
              (Equiv.swap (0 : Fin 2) 1)).toSection x) D := rfl
  change Tensor0SSpace.toModel
      ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
        (lieCorrectionZeroInsertion (I := I) (M := M) g₀ g₁ g_bg -
          lieCorrectionZeroInsertion (I := I) (M := M) g₀ g₁ g₀).toSection x) D) m =
    Tensor0SSpace.toModel
      ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
        (slotInsertEndoCc (I := I) (M := M) g₀ 1
            (endoDiffSection (I := I) (M := M) g₀ g₁ g_bg)).toSection x
          + (reindexCoefficientInputSlots (I := I) (M := M) g₀ 2 2
              (rsDomDomCongrSection (I := I) (M := M) g₀ 2 2 (Equiv.swap (0 : Fin 2) 1)
                (slotInsertEndoCc (I := I) (M := M) g₀ 1
                  (endoDiffSection (I := I) (M := M) g₀ g₁ g_bg)))
              (Equiv.swap (0 : Fin 2) 1)).toSection x) D) m
  rw [hsum, Tensor0SSpace.toModel_add, add_apply]
  rw [show (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
        (lieCorrectionZeroInsertion (I := I) (M := M) g₀ g₁ g_bg -
          lieCorrectionZeroInsertion (I := I) (M := M) g₀ g₁ g₀).toSection x) D
      = lieCorrectionZeroInsertionFib (I := I) g₀ g₁ g_bg x D -
          lieCorrectionZeroInsertionFib (I := I) g₀ g₁ g₀ x D from rfl]
  rw [Tensor0SSpace.toModel_sub, sub_apply]
  rw [lieCorrectionZeroInsertionFib_toModel (I := I) g₀ g₁ g_bg x D m,
    lieCorrectionZeroInsertionFib_toModel (I := I) g₀ g₁ g₀ x D m]
  rw [show (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
        (slotInsertEndoCc (I := I) (M := M) g₀ 1
          (endoDiffSection (I := I) (M := M) g₀ g₁ g_bg)).toSection x) D
      = slotInsertEndoFib (I := I) (M := M) 2 0 x
          (endoDiffSection (I := I) (M := M) g₀ g₁ g_bg x) D from rfl]
  rw [slotInsertEndoFib_apply_eval (I := I) (M := M) 2 0 x
    (endoDiffSection (I := I) (M := M) g₀ g₁ g_bg x) D m]
  rw [show (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
        (reindexCoefficientInputSlots (I := I) (M := M) g₀ 2 2
            (rsDomDomCongrSection (I := I) (M := M) g₀ 2 2 (Equiv.swap (0 : Fin 2) 1)
              (slotInsertEndoCc (I := I) (M := M) g₀ 1
                (endoDiffSection (I := I) (M := M) g₀ g₁ g_bg)))
            (Equiv.swap (0 : Fin 2) 1)).toSection x) D
      = reindexCoefficientInputSlotsFiber (I := I) 2 2 (Equiv.swap (0 : Fin 2) 1) x
          (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
            (rsDomDomCongrSection (I := I) (M := M) g₀ 2 2 (Equiv.swap (0 : Fin 2) 1)
              (slotInsertEndoCc (I := I) (M := M) g₀ 1
                (endoDiffSection (I := I) (M := M) g₀ g₁ g_bg))).toSection x) D from rfl]
  rw [reindexCoefficientInputSlotsFiber_apply (I := I) 2 2 (Equiv.swap (0 : Fin 2) 1) x
    (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
      (rsDomDomCongrSection (I := I) (M := M) g₀ 2 2 (Equiv.swap (0 : Fin 2) 1)
        (slotInsertEndoCc (I := I) (M := M) g₀ 1
          (endoDiffSection (I := I) (M := M) g₀ g₁ g_bg))).toSection x) D]
  rw [show (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
        (rsDomDomCongrSection (I := I) (M := M) g₀ 2 2 (Equiv.swap (0 : Fin 2) 1)
          (slotInsertEndoCc (I := I) (M := M) g₀ 1
            (endoDiffSection (I := I) (M := M) g₀ g₁ g_bg))).toSection x)
      = (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
          rsDomDomCongr (I := I) (M := M) (Equiv.swap (0 : Fin 2) 1)
            ((slotInsertEndoCc (I := I) (M := M) g₀ 1
              (endoDiffSection (I := I) (M := M) g₀ g₁ g_bg)).toSection x)) from rfl]
  rw [toModel_rsDomDomCongr_apply (I := I) (M := M) (Equiv.swap (0 : Fin 2) 1)
    ((slotInsertEndoCc (I := I) (M := M) g₀ 1
      (endoDiffSection (I := I) (M := M) g₀ g₁ g_bg)).toSection x)
    (Tensor0SSpace.ofModel
      (ContinuousMultilinearMap.domDomCongr (Equiv.swap (0 : Fin 2) 1)
        (Tensor0SSpace.toModel D)))]
  rw [ContinuousMultilinearMap.domDomCongr_apply]
  rw [show (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
        (slotInsertEndoCc (I := I) (M := M) g₀ 1
          (endoDiffSection (I := I) (M := M) g₀ g₁ g_bg)).toSection x)
        (Tensor0SSpace.ofModel
          (ContinuousMultilinearMap.domDomCongr (Equiv.swap (0 : Fin 2) 1)
            (Tensor0SSpace.toModel D)))
      = slotInsertEndoFib (I := I) (M := M) 2 0 x
          (endoDiffSection (I := I) (M := M) g₀ g₁ g_bg x)
          (Tensor0SSpace.ofModel
            (ContinuousMultilinearMap.domDomCongr (Equiv.swap (0 : Fin 2) 1)
              (Tensor0SSpace.toModel D))) from rfl]
  rw [slotInsertEndoFib_apply_eval (I := I) (M := M) 2 0 x
    (endoDiffSection (I := I) (M := M) g₀ g₁ g_bg x)
    (Tensor0SSpace.ofModel
      (ContinuousMultilinearMap.domDomCongr (Equiv.swap (0 : Fin 2) 1)
        (Tensor0SSpace.toModel D)))
    (fun i => m ((Equiv.swap (0 : Fin 2) 1) i))]
  rw [Tensor0SSpace.toModel_ofModel, ContinuousMultilinearMap.domDomCongr_apply]
  have harg : (fun k => Function.update (fun i => m ((Equiv.swap (0 : Fin 2) 1) i)) 0
        (tangentLinearMapToModel
          (endoDiffSection (I := I) (M := M) g₀ g₁ g_bg x)
          ((fun i => m ((Equiv.swap (0 : Fin 2) 1) i)) 0))
        ((Equiv.swap (0 : Fin 2) 1) k))
      = Function.update m 1
          (tangentLinearMapToModel
            (endoDiffSection (I := I) (M := M) g₀ g₁ g_bg x) (m 1)) := by
    funext k
    have hswap0 : (Equiv.swap (0 : Fin 2) 1) 0 = 1 := Equiv.swap_apply_left 0 1
    have hswap1 : (Equiv.swap (0 : Fin 2) 1) 1 = 0 := Equiv.swap_apply_right 0 1
    simp only [Function.update_apply]
    rw [hswap0, Equiv.swap_apply_self]
    have hcond : ((Equiv.swap (0 : Fin 2) 1) k = 0) = (k = 1) := by
      apply propext
      constructor
      · intro h
        have h2 := congrArg (Equiv.swap (0 : Fin 2) 1) h
        rwa [Equiv.swap_apply_self, hswap0] at h2
      · intro h
        rw [h, hswap1]
    simp only [hcond]
  rw [harg]
  rw [endoDiffSection_apply (I := I) (M := M) g₀ g₁ g_bg x]
  have hmodelSub (A B : TangentSpace I x →L[ℝ] TangentSpace I x) (z : E) :
      tangentLinearMapToModel (A - B) z =
        tangentLinearMapToModel A z - tangentLinearMapToModel B z := by
    rw [tangentLinearMapToModel_apply, sub_apply, map_sub]
    rfl
  rw [hmodelSub, hmodelSub]
  rw [ContinuousMultilinearMap.map_update_sub, ContinuousMultilinearMap.map_update_sub]
  ring

theorem normSq_iteratedCovGrad_lieCorrectionZeroInsertionDiff_le (g₀ g₁ g_bg : SmoothRiemannianMetric I M) (i : ℕ) :
    ‖iteratedCovGrad (I := I) g₀ 2 2 i
        (lieCorrectionZeroInsertion (I := I) (M := M) g₀ g₁ g_bg -
          lieCorrectionZeroInsertion (I := I) (M := M) g₀ g₁ g₀)‖ ^ 2 ≤
      4 * (Module.finrank ℝ E : ℝ) *
        ‖iteratedCovGrad (I := I) g₀ 1 1 i
          (slotInsertEndoCc (I := I) (M := M) g₀ 0
            (endoDiffSection (I := I) (M := M) g₀ g₁ g_bg))‖ ^ 2 := by
  have hL2A : ‖iteratedCovGrad (I := I) g₀ 2 2 i
      (slotInsertEndoCc (I := I) (M := M) g₀ 1
        (endoDiffSection (I := I) (M := M) g₀ g₁ g_bg))‖ ^ 2 ≤
      (Module.finrank ℝ E : ℝ) *
        ‖iteratedCovGrad (I := I) g₀ 1 1 i
          (slotInsertEndoCc (I := I) (M := M) g₀ 0
            (endoDiffSection (I := I) (M := M) g₀ g₁ g_bg))‖ ^ 2 :=
    normSq_iteratedCovGrad_le_scaled (I := I) (M := M) g₀
      (slotInsertEndoCc (I := I) (M := M) g₀ 1 (endoDiffSection (I := I) (M := M) g₀ g₁ g_bg))
      (slotInsertEndoCc (I := I) (M := M) g₀ 0 (endoDiffSection (I := I) (M := M) g₀ g₁ g_bg))
      i (Module.finrank ℝ E : ℝ)
      (fun x => by
        have h := riemannianFiberNormSq_iteratedCovGrad_slotInsertEndoCc_le_endo (I := I) (M := M) g₀ 1
          (endoDiffSection (I := I) (M := M) g₀ g₁ g_bg) i x
        rwa [pow_one] at h)
  have hL2B : ‖iteratedCovGrad (I := I) g₀ 2 2 i
      (reindexCoefficientInputSlots (I := I) (M := M) g₀ 2 2
        (rsDomDomCongrSection (I := I) (M := M) g₀ 2 2 (Equiv.swap (0 : Fin 2) 1)
          (slotInsertEndoCc (I := I) (M := M) g₀ 1
            (endoDiffSection (I := I) (M := M) g₀ g₁ g_bg)))
        (Equiv.swap (0 : Fin 2) 1))‖ ^ 2 ≤
      (Module.finrank ℝ E : ℝ) *
        ‖iteratedCovGrad (I := I) g₀ 1 1 i
          (slotInsertEndoCc (I := I) (M := M) g₀ 0
            (endoDiffSection (I := I) (M := M) g₀ g₁ g_bg))‖ ^ 2 :=
    normSq_iteratedCovGrad_le_scaled (I := I) (M := M) g₀
      (reindexCoefficientInputSlots (I := I) (M := M) g₀ 2 2
        (rsDomDomCongrSection (I := I) (M := M) g₀ 2 2 (Equiv.swap (0 : Fin 2) 1)
          (slotInsertEndoCc (I := I) (M := M) g₀ 1
            (endoDiffSection (I := I) (M := M) g₀ g₁ g_bg)))
        (Equiv.swap (0 : Fin 2) 1))
      (slotInsertEndoCc (I := I) (M := M) g₀ 0 (endoDiffSection (I := I) (M := M) g₀ g₁ g_bg))
      i (Module.finrank ℝ E : ℝ)
      (fun x => by
        have heq := riemannianFiberNormSq_iteratedCovGrad_rsDomDomCongr_both_eq (I := I) (M := M) g₀ 2 2
          (Equiv.swap (0 : Fin 2) 1) (Equiv.swap (0 : Fin 2) 1)
          (slotInsertEndoCc (I := I) (M := M) g₀ 1
            (endoDiffSection (I := I) (M := M) g₀ g₁ g_bg)) i x
        have h := riemannianFiberNormSq_iteratedCovGrad_slotInsertEndoCc_le_endo (I := I) (M := M) g₀ 1
          (endoDiffSection (I := I) (M := M) g₀ g₁ g_bg) i x
        rw [pow_one] at h
        exact heq.trans_le h)
  have hgrad : iteratedCovGrad (I := I) g₀ 2 2 i
        (lieCorrectionZeroInsertion (I := I) (M := M) g₀ g₁ g_bg - lieCorrectionZeroInsertion (I := I) (M := M) g₀ g₁ g₀)
      = iteratedCovGrad (I := I) g₀ 2 2 i
          (slotInsertEndoCc (I := I) (M := M) g₀ 1
            (endoDiffSection (I := I) (M := M) g₀ g₁ g_bg))
        + iteratedCovGrad (I := I) g₀ 2 2 i
            (reindexCoefficientInputSlots (I := I) (M := M) g₀ 2 2
              (rsDomDomCongrSection (I := I) (M := M) g₀ 2 2 (Equiv.swap (0 : Fin 2) 1)
                (slotInsertEndoCc (I := I) (M := M) g₀ 1
                  (endoDiffSection (I := I) (M := M) g₀ g₁ g_bg)))
              (Equiv.swap (0 : Fin 2) 1)) := by
    rw [lieCorrectionZeroInsDiff_eq (I := I) (M := M) g₀ g₁ g_bg, iteratedCovGrad_add]
  rw [hgrad]
  refine le_trans (sq_le_two_add _ _ _ _ _ (norm_nonneg _) (norm_nonneg _) (norm_nonneg _)
    (norm_add_le _ _) hL2A hL2B) (le_of_eq (by ring))

private theorem lieCorrectionZeroInsertionDiff_ballUniform
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ K : ℕ → ℝ, (∀ i, 0 ≤ K i) ∧
      ∀ (T T' : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀)
        (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        {δ' : ℝ} (_hδ'_le : δ' ≤ δ₀)
        (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ'),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ≤ R) →
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ≤ R) →
        ∀ (i : ℕ), i ≤ a → ∀ (s : ℝ), s ∈ Set.Icc (0 : ℝ) 1 →
          ‖iteratedCovGrad (I := I) g₀ 2 2 i
              (lieCorrectionZeroInsertion (I := I) (M := M) g₀ (metricPerturbationPath (I := I) g₀ T T' hδ hδ' s) g_bg
                - lieCorrectionZeroInsertion (I := I) (M := M) g₀ (metricPerturbationPath (I := I) g₀ T T' hδ hδ' s) g₀)‖ ^ 2
            ≤ K i := by
  obtain ⟨K, hK_nn, hK⟩ :=
    connectionDifferenceDeTurckVectorFieldInsertDiff_metricPerturbationPath_jetL2_perOrder_ballUniform (I := I) (M := M) g₀ g_bg a
      ha_super hR hδ₀
  have hfr_nn : (0 : ℝ) ≤ 4 * (Module.finrank ℝ E : ℝ) := by positivity
  refine ⟨fun i => 4 * (Module.finrank ℝ E : ℝ) * K i,
    fun i => mul_nonneg hfr_nn (hK_nn i), ?_⟩
  intro T T' δ hδ_le hδ δ' hδ'_le hδ' hTball hT'ball i hi s hs
  have hprod := hK T T' hδ_le hδ hδ'_le hδ' hTball hT'ball i hi s hs
  have hred := normSq_iteratedCovGrad_lieCorrectionZeroInsertionDiff_le (I := I) (M := M) g₀
    (metricPerturbationPath (I := I) g₀ T T' hδ hδ' s) g_bg i
  simp only [endoDiffSection] at hred
  refine le_trans hred ?_
  exact mul_le_mul_of_nonneg_left hprod hfr_nn

private theorem lieCorrectionZeroInsertionDiff_metricPerturbationPath_perOrder_topOrderSeparation
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ Ktop : ℝ, 0 ≤ Ktop ∧ ∃ Kc : ℕ → ℝ, (∀ i, 0 ≤ Kc i) ∧
      ∀ (T T' : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀)
        (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        {δ' : ℝ} (_hδ'_le : δ' ≤ δ₀)
        (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ'),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ≤ R) →
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ≤ R) →
        ∀ (s : ℝ), s ∈ Set.Icc (0 : ℝ) 1 →
        ∀ (i : ℕ), i ≤ a →
          ‖iteratedCovGrad (I := I) g₀ 2 2 i
              (lieCorrectionZeroInsertion (I := I) (M := M) g₀ (metricPerturbationPath (I := I) g₀ T T' hδ hδ' s) g_bg
                - lieCorrectionZeroInsertion (I := I) (M := M) g₀ (metricPerturbationPath (I := I) g₀ T T' hδ hδ' s) g₀)‖ ^ 2 ≤
            Ktop * (‖iteratedCovGrad (I := I) g₀ 0 2 (i + 2) T‖ ^ 2 +
              ‖iteratedCovGrad (I := I) g₀ 0 2 (i + 2) T'‖ ^ 2) +
            Kc i * (1 + ∑ j ∈ Finset.range (i + 3),
              (‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ^ 2 +
                ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ^ 2)) := by
  obtain ⟨K, hK_nn, hK⟩ := lieCorrectionZeroInsertionDiff_ballUniform (I := I) (M := M) g₀ g_bg a ha_super hR hδ₀
  refine ⟨0, le_refl 0, K, hK_nn, ?_⟩
  intro T T' δ hδ_le hδ δ' hδ'_le hδ' hTball hT'ball s hs i hi
  have hb := hK T T' hδ_le hδ hδ'_le hδ' hTball hT'ball i hi s hs
  have hlow_nn : (0 : ℝ) ≤ ∑ j ∈ Finset.range (i + 3),
      (‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ^ 2 +
        ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ^ 2) :=
    Finset.sum_nonneg (fun j _ => add_nonneg (sq_nonneg _) (sq_nonneg _))
  nlinarith only [hb, hK_nn i, hlow_nn, mul_nonneg (hK_nn i) hlow_nn]

private noncomputable def lieCorrectionZeroVectorBundleLiftFib (g₀ g₁ : SmoothRiemannianMetric I M) (x : M) :
    Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 4 I x :=
  (domDomCongrFibRank (I := I) 4 lieCorrectionZeroVectorBundleTracePermutation x).comp
    ((tensor0SProdKappaFib (I := I) (p := 1) (q := 3) x
        (metricConnectionDifferenceLoweredFib (I := I) g₁ g₁ g₀ x)).comp
      (Tensor0SBundle.interiorProduct (𝕜 := ℝ) (I := I) 1 x
        ((PDE.DeTurck.deTurckVF (I := I) g₁ g₀ : Π b : M, TangentSpace I b) x)))

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [SigmaCompactSpace M] in
private theorem lieCorrectionZeroVectorBundleLiftFib_contMDiff (g₀ g₁ : SmoothRiemannianMetric I M) :
    ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel 2 4 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel 2 4 ℝ E)
        (E := fun z : M => TensorRSSpace 2 4 I z) x
        (TensorRSSpace.ofCLM (lieCorrectionZeroVectorBundleLiftFib (I := I) g₀ g₁ x))) := by
  classical
  apply contMDiff_clm_section_of_pointwise (I := I) (M := M)
    (F₁ := Tensor0SModel 2 ℝ E) (V₁ := fun x : M => Tensor0SSpace 2 I x)
    (F₂ := Tensor0SModel 4 ℝ E) (V₂ := fun x : M => Tensor0SSpace 4 I x)
    (φ := fun x => lieCorrectionZeroVectorBundleLiftFib (I := I) g₀ g₁ x)
  intro Y
  have hip : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel 1 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SModel 1 ℝ E)
        (E := fun z : M => Tensor0SSpace 1 I z) x
        (Tensor0SBundle.interiorProduct (𝕜 := ℝ) (I := I) 1 x
          ((PDE.DeTurck.deTurckVF (I := I) g₁ g₀ : Π b : M, TangentSpace I b) x) (Y x))) :=
    (Tensor0SBundle.contractTensor0SField (𝕜 := ℝ) (I := I) (n := (∞ : WithTop ℕ∞)) 1 Y
      (PDE.DeTurck.deTurckVF (I := I) g₁ g₀)).contMDiff
  have hprod := lieCorrectionZero_prod_section_contMDiff (I := I) (p := 1) (q := 3)
    (fun x => Tensor0SBundle.interiorProduct (𝕜 := ℝ) (I := I) 1 x
      ((PDE.DeTurck.deTurckVF (I := I) g₁ g₀ : Π b : M, TangentSpace I b) x) (Y x))
    (fun x => metricConnectionDifferenceLoweredFib (I := I) g₁ g₁ g₀ x)
    hip (metricConnectionDifferenceLoweredFib_contMDiff (I := I) g₁ g₁ g₀)
  have hddc := lieCorrectionZero_ddc_section_contMDiff (I := I) (d := 4) lieCorrectionZeroVectorBundleTracePermutation
    (fun x => tensor0SProdKappaFib (I := I) x (metricConnectionDifferenceLoweredFib (I := I) g₁ g₁ g₀ x)
      (Tensor0SBundle.interiorProduct (𝕜 := ℝ) (I := I) 1 x
        ((PDE.DeTurck.deTurckVF (I := I) g₁ g₀ : Π b : M, TangentSpace I b) x) (Y x)))
    hprod
  refine hddc.congr (fun x => ?_)
  refine congrArg (fun t => TotalSpace.mk' (Tensor0SModel 4 ℝ E)
    (E := fun z : M => Tensor0SSpace 4 I z) x t) ?_
  rw [lieCorrectionZeroVectorBundleLiftFib]
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, domDomCongrFibRank_apply]

noncomputable def lieCorrectionZeroVectorBundleLift (g₀ g₁ : SmoothRiemannianMetric I M) :
    SmoothCcTensor g₀ 2 4 where
  toSection :=
    { toFun := fun x : M =>
        (show TensorRSSpace 2 4 I x from
          TensorRSSpace.ofCLM (lieCorrectionZeroVectorBundleLiftFib (I := I) g₀ g₁ x))
      contMDiff_toFun := lieCorrectionZeroVectorBundleLiftFib_contMDiff (I := I) g₀ g₁ }
  hasCompactSupport := HasCompactSupport.of_compactSpace _

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
omit [I.Boundaryless] in
private theorem lieCorrectionZeroVectorBundleFib_eq (g₀ g₁ : SmoothRiemannianMetric I M) (x : M) :
    lieCorrectionZeroVBFib (I := I) g₀ g₁ x =
      (2 : ℝ) • ((show Tensor0SSpace 4 I x →L[ℝ] Tensor0SSpace 2 I x from
            (reindexedCometricDoubleTrace (I := I) (M := M) g₀ g₁).toSection x).comp
        (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 4 I x from
            (lieCorrectionZeroVectorBundleLift (I := I) (M := M) g₀ g₁).toSection x)) := by
  rw [lieCorrectionZeroVBFib, reindexedCometricDoubleTrace_toSection]
  rfl

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
omit [I.Boundaryless] in
theorem lieCorrectionZeroVectorBundle_eq_ccOperatorFieldComp (g₀ g₁ : SmoothRiemannianMetric I M) :
    lieCorrectionZeroVectorBundle (I := I) (M := M) g₀ g₁ =
      (2 : ℝ) • ccOperatorFieldComp (I := I) (M := M) g₀ 2 4 2
        (reindexedCometricDoubleTrace (I := I) (M := M) g₀ g₁) (lieCorrectionZeroVectorBundleLift (I := I) (M := M) g₀ g₁) := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rw [SmoothCcTensor.toSection_smul, ContMDiffSection.coe_smul, Pi.smul_apply, operatorFieldComposition_toSection]
  exact lieCorrectionZeroVectorBundleFib_eq (I := I) (M := M) g₀ g₁ x

private noncomputable def lieCorrectionZeroVectorBundleMetricConnectionDifferenceTermFiber (g₀ g₁ : SmoothRiemannianMetric I M) (x : M) :
    Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 4 I x :=
  (domDomCongrFibRank (I := I) 4 lieCorrectionZeroVectorBundleTracePermutation x).comp
    (tensor0SProdKappaFib (I := I) (p := 1) (q := 3) x
      (metricConnectionDifferenceLoweredFib (I := I) g₁ g₁ g₀ x))

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [SigmaCompactSpace M] in
private theorem lieCorrectionZeroVectorBundleMetricConnectionDifferenceTermFiber_contMDiff (g₀ g₁ : SmoothRiemannianMetric I M) :
    ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel 1 4 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel 1 4 ℝ E)
        (E := fun z : M => TensorRSSpace 1 4 I z) x
        (TensorRSSpace.ofCLM (lieCorrectionZeroVectorBundleMetricConnectionDifferenceTermFiber (I := I) g₀ g₁ x))) := by
  classical
  apply contMDiff_clm_section_of_pointwise (I := I) (M := M)
    (F₁ := Tensor0SModel 1 ℝ E) (V₁ := fun x : M => Tensor0SSpace 1 I x)
    (F₂ := Tensor0SModel 4 ℝ E) (V₂ := fun x : M => Tensor0SSpace 4 I x)
    (φ := fun x => lieCorrectionZeroVectorBundleMetricConnectionDifferenceTermFiber (I := I) g₀ g₁ x)
  intro Y
  have hprod := lieCorrectionZero_prod_section_contMDiff (I := I) (p := 1) (q := 3)
    (fun x => Y x) (fun x => metricConnectionDifferenceLoweredFib (I := I) g₁ g₁ g₀ x)
    Y.contMDiff (metricConnectionDifferenceLoweredFib_contMDiff (I := I) g₁ g₁ g₀)
  have hddc := lieCorrectionZero_ddc_section_contMDiff (I := I) (d := 4) lieCorrectionZeroVectorBundleTracePermutation
    (fun x => tensor0SProdKappaFib (I := I) x (metricConnectionDifferenceLoweredFib (I := I) g₁ g₁ g₀ x)
      (Y x)) hprod
  refine hddc.congr (fun x => ?_)
  refine congrArg (fun t => TotalSpace.mk' (Tensor0SModel 4 ℝ E)
    (E := fun z : M => Tensor0SSpace 4 I z) x t) ?_
  rw [lieCorrectionZeroVectorBundleMetricConnectionDifferenceTermFiber]
  rw [ContinuousLinearMap.comp_apply, domDomCongrFibRank_apply]

noncomputable def lieCorrectionZeroVectorBundleMetricConnectionDifferenceTerm (g₀ g₁ : SmoothRiemannianMetric I M) :
    SmoothCcTensor g₀ 1 4 where
  toSection :=
    { toFun := fun x : M =>
        (show TensorRSSpace 1 4 I x from
          TensorRSSpace.ofCLM (lieCorrectionZeroVectorBundleMetricConnectionDifferenceTermFiber (I := I) g₀ g₁ x))
      contMDiff_toFun := lieCorrectionZeroVectorBundleMetricConnectionDifferenceTermFiber_contMDiff (I := I) g₀ g₁ }
  hasCompactSupport := HasCompactSupport.of_compactSpace _

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [SigmaCompactSpace M] in
private lemma lieCorrectionZeroVectorBundleMetricConnectionDifference_unitModel (g₀ g₁ : SmoothRiemannianMetric I M) (x : M)
    (m : Fin 3 → E) :
    unitModel (I := I) (M := M) g₀ 3 (metricConnectionDifferenceLoweredCoefficient (I := I) (M := M) g₀ g₁ g₀) x m =
      g₁.inner x
        (PDE.DeTurck.connectionDifference (I := I) g₁ g₀ x
          ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm (m 0))
          ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm (m 1)))
        ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm (m 2)) := by
  rw [unitModel]
  rw [show (metricConnectionDifferenceLoweredCoefficient (I := I) (M := M) g₀ g₁ g₀).toSection x
      (unitTensor (I := I) (M := M) x) =
      (MixedSection.eval₀ (F := E) (E := (TangentSpace I : M → Type _)) x).smulRight
          (metricConnectionDifferenceLoweredFib (I := I) g₁ g₁ g₀ x)
          (ContinuousMultilinearMap.constOfIsEmpty ℝ (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ))
      from rfl]
  rw [ContinuousLinearMap.smulRight_apply, MixedSection.eval₀_apply,
    ContinuousMultilinearMap.constOfIsEmpty_apply, one_smul]
  exact metricConnectionDifferenceLoweredFib_toModel (I := I) g₁ g₁ g₀ x m

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma vb_rank0_smul_unit (x : M) (c : Tensor0SSpace 0 I x) :
    c = Tensor0SSpace.toModel c (fun i : Fin 0 => i.elim0) •
      unitTensor (I := I) (M := M) x := by
  apply Tensor0SSpace.toModel_injective
  apply ContinuousMultilinearMap.ext
  intro v
  beta_reduce
  rw [Tensor0SSpace.toModel_smul, smul_apply, smul_eq_mul]
  have h1 : Tensor0SSpace.toModel (unitTensor (I := I) (M := M) x) v = (1 : ℝ) := rfl
  rw [h1, mul_one]
  congr 1
  funext i
  exact i.elim0

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [SigmaCompactSpace M] in
private lemma vbPK_eq_slotExt (g₀ g₁ : SmoothRiemannianMetric I M) (x : M)
    (B : Tensor0SSpace 1 I x) :
    Tensor0SSpace.toModel
        (tensor0SProdKappaFib (I := I) (p := 1) (q := 3) x
          (metricConnectionDifferenceLoweredFib (I := I) g₁ g₁ g₀ x) B) =
      Tensor0SSpace.toModel
        (slotExtendFib (I := I) (M := M) 0 3 x
          (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 3 I x from
            (metricConnectionDifferenceLoweredCoefficient (I := I) (M := M) g₀ g₁ g₀).toSection x) B) := by
  classical
  apply ContinuousMultilinearMap.ext
  intro u
  rw [show (u : Fin 4 → E) = Fin.cons (u 0) (Fin.tail u) from (Fin.cons_self_tail u).symm]
  rw [tensor0SProdKappaFib_apply, Tensor0SSpace.toModel_ofModel,
    Bundle.continuousMultilinearMap.modelProduct_apply]
  rw [slotExtendFib_apply_eval (I := I) (M := M) 0 3 x
    (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 3 I x from
      (metricConnectionDifferenceLoweredCoefficient (I := I) (M := M) g₀ g₁ g₀).toSection x) B (u 0) (Fin.tail u)]
  have hc : tensor0SCurry (I := I) (M := M) (𝕜 := ℝ) 0 x B
      ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm (u 0)) =
      Tensor0SSpace.toModel B (fun _ : Fin 1 => u 0) • unitTensor (I := I) (M := M) x := by
    have h2 := vb_rank0_smul_unit (I := I) (M := M) x
      (tensor0SCurry (I := I) (M := M) (𝕜 := ℝ) 0 x B
        ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm (u 0)))
    rw [h2]
    congr 1
    rw [TensorMultilinear.tensor0S_curry_toModel_apply (I := I) (M := M) (T := B) (v0 := u 0)
      (vs := fun i : Fin 0 => i.elim0)]
    congr 1
    funext k
    fin_cases k
    rfl
  rw [hc, ContinuousLinearMap.map_smul, Tensor0SSpace.toModel_smul,
    smul_apply, smul_eq_mul]
  rw [show Tensor0SSpace.toModel
      ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 3 I x from
        (metricConnectionDifferenceLoweredCoefficient (I := I) (M := M) g₀ g₁ g₀).toSection x)
        (unitTensor (I := I) (M := M) x)) (Fin.tail u) =
      unitModel (I := I) (M := M) g₀ 3 (metricConnectionDifferenceLoweredCoefficient (I := I) (M := M) g₀ g₁ g₀) x
        (fun j => Fin.tail u j) from by rw [unitModel]]
  rw [lieCorrectionZeroVectorBundleMetricConnectionDifference_unitModel (I := I) (M := M) g₀ g₁ x (fun j => Fin.tail u j)]
  have hcast : ((Fin.cons (u 0) (Fin.tail u) : Fin 4 → E) ∘ Fin.castAdd 3) =
      (fun _ : Fin 1 => u 0) := by
    funext i
    fin_cases i
    rfl
  have hnat : ((Fin.cons (u 0) (Fin.tail u) : Fin 4 → E) ∘ Fin.natAdd 1) = Fin.tail u := by
    funext j
    have hj : Fin.natAdd 1 j = Fin.succ j := by
      apply Fin.ext
      simp [Fin.natAdd, Fin.succ, Nat.add_comm]
    change Fin.cons (u 0) (Fin.tail u) (Fin.natAdd 1 j) = Fin.tail u j
    rw [hj, Fin.cons_succ]
  rw [hcast, hnat]
  rw [metricConnectionDifferenceLoweredFib_toModel (I := I) g₁ g₁ g₀ x (fun j => Fin.tail u j)]

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [SigmaCompactSpace M] in
private lemma lieCorrectionZeroVectorBundleMetricConnectionDifferenceTerm_toModel (g₀ g₁ : SmoothRiemannianMetric I M) :
    ∀ (y : M) (d : Tensor0SSpace 1 I y),
      Tensor0SSpace.toModel
          ((show Tensor0SSpace 1 I y →L[ℝ] Tensor0SSpace 4 I y from
            (lieCorrectionZeroVectorBundleMetricConnectionDifferenceTerm (I := I) (M := M) g₀ g₁).toSection y) d) =
        ContinuousMultilinearMap.domDomCongr lieCorrectionZeroVectorBundleTracePermutation
          (Tensor0SSpace.toModel
            ((show Tensor0SSpace 1 I y →L[ℝ] Tensor0SSpace 4 I y from
              (slotExtend (I := I) (M := M) g₀ 0 3
                (metricConnectionDifferenceLoweredCoefficient (I := I) (M := M) g₀ g₁ g₀)).toSection y) d)) := by
  intro y d
  rw [show ((show Tensor0SSpace 1 I y →L[ℝ] Tensor0SSpace 4 I y from
      (lieCorrectionZeroVectorBundleMetricConnectionDifferenceTerm (I := I) (M := M) g₀ g₁).toSection y) d) =
      domDomCongrFibRank (I := I) 4 lieCorrectionZeroVectorBundleTracePermutation y
        (tensor0SProdKappaFib (I := I) (p := 1) (q := 3) y
          (metricConnectionDifferenceLoweredFib (I := I) g₁ g₁ g₀ y) d) from rfl]
  rw [domDomCongrFibRank_apply, Tensor0SSpace.toModel_ofModel]
  exact congrArg (ContinuousMultilinearMap.domDomCongr lieCorrectionZeroVectorBundleTracePermutation)
    (vbPK_eq_slotExt (I := I) (M := M) g₀ g₁ y d)

omit [SigmaCompactSpace M] in
lemma riemannianFiberNormSq_iteratedCovGrad_lieCorrectionZeroVectorBundleMetricConnectionDifferenceTerm_le (g₀ g₁ : SmoothRiemannianMetric I M) (m : ℕ) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g₀ 1 (4 + m) x
        ((iteratedCovGrad (I := I) g₀ 1 4 m (lieCorrectionZeroVectorBundleMetricConnectionDifferenceTerm (I := I) (M := M) g₀ g₁)).toSection x) ≤
      (Module.finrank ℝ E : ℝ) *
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + m) x
          ((iteratedCovGrad (I := I) g₀ 0 3 m
            (metricConnectionDifferenceLoweredCoefficient (I := I) (M := M) g₀ g₁ g₀)).toSection x) := by
  rw [riemannianFiberNormSq_iteratedCovGrad_rs_eq_of_section_domDomCongr (I := I) (M := M) g₀ 1 4
    lieCorrectionZeroVectorBundleTracePermutation
    (slotExtend (I := I) (M := M) g₀ 0 3 (metricConnectionDifferenceLoweredCoefficient (I := I) (M := M) g₀ g₁ g₀))
    (lieCorrectionZeroVectorBundleMetricConnectionDifferenceTerm (I := I) (M := M) g₀ g₁) (lieCorrectionZeroVectorBundleMetricConnectionDifferenceTerm_toModel (I := I) (M := M) g₀ g₁) m x]
  exact riemannianFiberNormSq_iteratedCovGrad_slotExtend_le (I := I) (M := M) g₀ 0 3
    (metricConnectionDifferenceLoweredCoefficient (I := I) (M := M) g₀ g₁ g₀) m x

lemma norm_iteratedCovGrad_lieCorrectionZeroVectorBundleMetricConnectionDifferenceTerm_sq_le (g₀ g₁ : SmoothRiemannianMetric I M) (m : ℕ) :
    ‖iteratedCovGrad (I := I) g₀ 1 4 m (lieCorrectionZeroVectorBundleMetricConnectionDifferenceTerm (I := I) (M := M) g₀ g₁)‖ ^ 2 ≤
      (Module.finrank ℝ E : ℝ) *
        ‖iteratedCovGrad (I := I) g₀ 0 3 m
          (metricConnectionDifferenceLoweredCoefficient (I := I) (M := M) g₀ g₁ g₀)‖ ^ 2 := by
  have hint : MeasureTheory.Integrable
      (fun x => (Module.finrank ℝ E : ℝ) *
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + m) x
          ((iteratedCovGrad (I := I) g₀ 0 3 m
            (metricConnectionDifferenceLoweredCoefficient (I := I) (M := M) g₀ g₁ g₀)).toSection x))
      (riemannianVolumeMeasure (I := I) (M := M) g₀) :=
    (integrable_riemannianFiberNormSq_toSection (I := I) (M := M) g₀ 0 (3 + m)
      (iteratedCovGrad (I := I) g₀ 0 3 m
        (metricConnectionDifferenceLoweredCoefficient (I := I) (M := M) g₀ g₁ g₀))).const_mul _
  have key := normSq_le_integral_of_pointwise_fiberNormSq_le_rs (I := I) (M := M) g₀ 1 (4 + m)
    (iteratedCovGrad (I := I) g₀ 1 4 m (lieCorrectionZeroVectorBundleMetricConnectionDifferenceTerm (I := I) (M := M) g₀ g₁)) _ hint
    (fun x => riemannianFiberNormSq_iteratedCovGrad_lieCorrectionZeroVectorBundleMetricConnectionDifferenceTerm_le (I := I) (M := M) g₀ g₁ m x)
  refine le_trans key (le_of_eq ?_)
  rw [MeasureTheory.integral_const_mul]
  refine congrArg _ ?_
  rw [← tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs (I := I) (M := M) g₀ 0 (3 + m)
      (iteratedCovGrad (I := I) g₀ 0 3 m
        (metricConnectionDifferenceLoweredCoefficient (I := I) (M := M) g₀ g₁ g₀)),
    ← SmoothCcTensor.norm_def]

omit [SigmaCompactSpace M] in
omit [I.Boundaryless] in
theorem lieCorrectionZeroVectorBundleLift_eq_ccOperatorFieldComp (g₀ g₁ : SmoothRiemannianMetric I M) :
    lieCorrectionZeroVectorBundleLift (I := I) (M := M) g₀ g₁ =
      ccOperatorFieldComp (I := I) (M := M) g₀ 2 1 4 (lieCorrectionZeroVectorBundleMetricConnectionDifferenceTerm (I := I) (M := M) g₀ g₁)
        (ipLowCc (I := I) (M := M) g₀ (deTurckVectorFieldCovector (I := I) (M := M) g₀ g₁ g₀)) := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rw [operatorFieldComposition_toSection]
  have hflat : ∀ z : TangentSpace I x,
      unitModel (I := I) (M := M) g₀ 1 (deTurckVectorFieldCovector (I := I) (M := M) g₀ g₁ g₀) x
          (fun _ : Fin 1 =>
            tangentSpaceModelContinuousLinearEquiv (I := I) x z) =
        g₀.inner x ((PDE.DeTurck.deTurckVF (I := I) g₁ g₀ :
          Π b : M, TangentSpace I b) x) z := by
    intro z
    rw [deTurckVectorFieldCovector_unitModel_apply (I := I) (M := M) g₀ g₁ g₀ x z]
    rfl
  rw [ipLowCc_toSec_ip (I := I) (M := M) g₀ (deTurckVectorFieldCovector (I := I) (M := M) g₀ g₁ g₀) x
    ((PDE.DeTurck.deTurckVF (I := I) g₁ g₀ : Π b : M, TangentSpace I b) x) hflat]
  rfl

private theorem vbPass_jetL2
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ (Λ : ℝ) (F : ℕ → ℝ), 0 ≤ Λ ∧ (∀ i, 0 ≤ F i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀)
        (_hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ)
        (_htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ≤ R) →
        (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 2 4 x
            ((lieCorrectionZeroVectorBundleLift (I := I) (M := M) g₀ g₁).toSection x) ≤ Λ) ∧
        ∀ (i : ℕ), i ≤ a →
          ∑ q ∈ Finset.range (i + 1),
            ‖iteratedCovGrad (I := I) g₀ 2 4 q (lieCorrectionZeroVectorBundleLift (I := I) (M := M) g₀ g₁)‖ ^ 2 ≤ F i := by
  classical
  obtain ⟨Λmcd, Fmcd, hΛmcd_nn, hFmcd_nn, hmcd⟩ :=
    metricConnectionDifferenceLoweredCoefficient_jetL2_ballUniform (I := I) (M := M) g₀ g₀ a ha_super hR hδ₀
  obtain ⟨cip, hcip_nn, hcip⟩ := riemannianFiberNormSq_iteratedCovGrad_ipLow_le (I := I) (M := M) g₀
  obtain ⟨cipL, hcipL_nn, hcipL⟩ := norm_iteratedCovGrad_ipLow_le (I := I) (M := M) g₀
  obtain ⟨ΛΩ, FΩ, hΛΩ_nn, hFΩ_nn, hΩgen⟩ :=
    deTurckVectorFieldCovector_lowOrder_iteratedCovGrad_norm_sq_succ_le (I := I) (M := M) g₀ g₀ a ha_super hR hδ₀
  choose CI hCI_nn hCI using
    (fun k : ℕ => exists_integrated_iteratedCovGrad_diagonalProductGrid_twoTerm_rs_le
      (I := I) (M := M) g₀ 1 2 4 1 k)
  set n : ℝ := (Module.finrank ℝ E : ℝ) with hn
  have hn_nn : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  set BS : ℝ := n * Λmcd with hBS
  set BT : ℝ := cip 0 * ΛΩ 0 with hBT
  have hBS_nn : 0 ≤ BS := mul_nonneg hn_nn hΛmcd_nn
  have hBT_nn : 0 ≤ BT := mul_nonneg (hcip_nn 0) (hΛΩ_nn 0)
  set F : ℕ → ℝ := fun i => ∑ q ∈ Finset.range (i + 1),
    operatorFieldApplicationGdiag (E := E) q * (CI q * (BT * (n * Fmcd q)
      + BS * ∑ l ∈ Finset.range (q + 1), cipL l * FΩ l)) with hF_def
  have hF_nn : ∀ i, 0 ≤ F i := fun i => Finset.sum_nonneg (fun q _ =>
    mul_nonneg (operatorFieldApplicationGdiag_nonneg (E := E) q) (mul_nonneg (hCI_nn q)
      (add_nonneg (mul_nonneg hBT_nn (mul_nonneg hn_nn (hFmcd_nn q)))
        (mul_nonneg hBS_nn (Finset.sum_nonneg (fun l _ =>
          mul_nonneg (hcipL_nn l) (hFΩ_nn l)))))))
  refine ⟨BS * BT, F, mul_nonneg hBS_nn hBT_nn, hF_nn, ?_⟩
  intro g₁ P δ hδ_le hδ htie hPball
  by_cases hM : Nonempty M
  · obtain ⟨x0⟩ := hM
    have hδ0 : 0 ≤ δ := by
      have : Nontrivial E := Module.nontrivial_of_finrank_pos (R := ℝ) (M := E)
        (Nat.pos_of_ne_zero (NeZero.ne _))
      obtain ⟨v, hv⟩ := exists_ne (0 : E)
      have hgpos : 0 < g₀.inner x0 (show TangentSpace I x0 from v)
          (show TangentSpace I x0 from v) :=
        g₀.pos x0 (show TangentSpace I x0 from v) hv
      have hb := hδ x0 (show TangentSpace I x0 from v) (show TangentSpace I x0 from v)
      have h1 : 0 ≤ δ * Real.sqrt (g₀.inner x0 (show TangentSpace I x0 from v)
            (show TangentSpace I x0 from v)) *
          Real.sqrt (g₀.inner x0 (show TangentSpace I x0 from v)
            (show TangentSpace I x0 from v)) :=
        le_trans (abs_nonneg _) hb
      rw [mul_assoc, Real.mul_self_sqrt (le_of_lt hgpos)] at h1
      exact (mul_nonneg_iff_of_pos_right hgpos).mp h1
    obtain ⟨hmcd_sup, hmcd_jets⟩ := hmcd g₁ P htie hδ_le hδ0 hδ hPball
    obtain ⟨hΩ_sup, hΩ_jets⟩ := hΩgen g₁ P htie hδ_le hδ0 hδ hPball
    have hS_sup : ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 1 4 x
        ((lieCorrectionZeroVectorBundleMetricConnectionDifferenceTerm (I := I) (M := M) g₀ g₁).toSection x) ≤ Real.sqrt BS ^ 2 := by
      intro x
      have h := riemannianFiberNormSq_iteratedCovGrad_lieCorrectionZeroVectorBundleMetricConnectionDifferenceTerm_le (I := I) (M := M) g₀ g₁ 0 x
      rw [iteratedCovGrad_zero, iteratedCovGrad_zero] at h
      rw [Real.sq_sqrt hBS_nn]
      exact le_trans h (mul_le_mul_of_nonneg_left (hmcd_sup x) hn_nn)
    have hT_sup : ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 2 1 x
        ((ipLowCc (I := I) (M := M) g₀
          (deTurckVectorFieldCovector (I := I) (M := M) g₀ g₁ g₀)).toSection x) ≤ Real.sqrt BT ^ 2 := by
      intro x
      have h := hcip (deTurckVectorFieldCovector (I := I) (M := M) g₀ g₁ g₀) 0 x
      rw [iteratedCovGrad_zero] at h
      rw [Real.sq_sqrt hBT_nn]
      refine le_trans h ?_
      rw [Finset.sum_range_one]
      exact mul_le_mul_of_nonneg_left (hΩ_sup 0 (by omega) x) (hcip_nn 0)
    refine ⟨?_, ?_⟩
    · intro x
      rw [lieCorrectionZeroVectorBundleLift_eq_ccOperatorFieldComp (I := I) (M := M) g₀ g₁]
      have h := riemannianFiberNormSq_iteratedCovGrad_operatorFieldComposition_diagonalProductGrid_rankLeft_le
        (I := I) (M := M) g₀ 0 2 1 4 (lieCorrectionZeroVectorBundleMetricConnectionDifferenceTerm (I := I) (M := M) g₀ g₁)
        (ipLowCc (I := I) (M := M) g₀ (deTurckVectorFieldCovector (I := I) (M := M) g₀ g₁ g₀)) x
      rw [diagonalGridGrowthFactor, pow_zero, one_mul,
        Finset.sum_range_one, Finset.sum_range_one] at h
      simp only [iteratedCovGrad_zero] at h
      refine le_trans h ?_
      have h1 := hS_sup x
      rw [Real.sq_sqrt hBS_nn] at h1
      have h2 := hT_sup x
      rw [Real.sq_sqrt hBT_nn] at h2
      exact mul_le_mul h1 h2
        (riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 2 1 x _) hBS_nn
    · intro i hi
      rw [lieCorrectionZeroVectorBundleLift_eq_ccOperatorFieldComp (I := I) (M := M) g₀ g₁]
      simp only [hF_def]
      refine Finset.sum_le_sum (fun q hq => ?_)
      have hq_le : q ≤ a := by
        rw [Finset.mem_range] at hq
        omega
      obtain ⟨hI_int, hI_le⟩ := hCI q (lieCorrectionZeroVectorBundleMetricConnectionDifferenceTerm (I := I) (M := M) g₀ g₁)
        (ipLowCc (I := I) (M := M) g₀ (deTurckVectorFieldCovector (I := I) (M := M) g₀ g₁ g₀))
        (Real.sqrt BS) (Real.sqrt BT) (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
        hS_sup hT_sup
      have key := normSq_le_integral_of_pointwise_fiberNormSq_le_rs (I := I) (M := M) g₀ 2 (4 + q)
        (iteratedCovGrad (I := I) g₀ 2 4 q
          (ccOperatorFieldComp (I := I) (M := M) g₀ 2 1 4 (lieCorrectionZeroVectorBundleMetricConnectionDifferenceTerm (I := I) (M := M) g₀ g₁)
            (ipLowCc (I := I) (M := M) g₀ (deTurckVectorFieldCovector (I := I) (M := M) g₀ g₁ g₀)))) _
        (hI_int.const_mul (operatorFieldApplicationGdiag (E := E) q))
        (fun x => riemannianFiberNormSq_iteratedCovGrad_operatorFieldComposition_diagonalProductGrid_rankLeft_le
          (I := I) (M := M) g₀ q 2 1 4 (lieCorrectionZeroVectorBundleMetricConnectionDifferenceTerm (I := I) (M := M) g₀ g₁)
          (ipLowCc (I := I) (M := M) g₀ (deTurckVectorFieldCovector (I := I) (M := M) g₀ g₁ g₀)) x)
      refine le_trans key ?_
      rw [MeasureTheory.integral_const_mul]
      refine le_trans (mul_le_mul_of_nonneg_left hI_le (operatorFieldApplicationGdiag_nonneg (E := E) q)) ?_
      rw [Real.sq_sqrt hBS_nn, Real.sq_sqrt hBT_nn]
      refine mul_le_mul_of_nonneg_left ?_ (operatorFieldApplicationGdiag_nonneg (E := E) q)
      refine mul_le_mul_of_nonneg_left ?_ (hCI_nn q)
      refine add_le_add ?_ ?_
      · refine mul_le_mul_of_nonneg_left ?_ hBT_nn
        calc ∑ m ∈ Finset.range (q + 1),
              ‖iteratedCovGrad (I := I) g₀ 1 4 m (lieCorrectionZeroVectorBundleMetricConnectionDifferenceTerm (I := I) (M := M) g₀ g₁)‖ ^ 2
            ≤ ∑ m ∈ Finset.range (q + 1), n *
              ‖iteratedCovGrad (I := I) g₀ 0 3 m
                (metricConnectionDifferenceLoweredCoefficient (I := I) (M := M) g₀ g₁ g₀)‖ ^ 2 :=
              Finset.sum_le_sum (fun m _ => norm_iteratedCovGrad_lieCorrectionZeroVectorBundleMetricConnectionDifferenceTerm_sq_le (I := I) (M := M) g₀ g₁ m)
          _ = n * ∑ m ∈ Finset.range (q + 1),
              ‖iteratedCovGrad (I := I) g₀ 0 3 m
                (metricConnectionDifferenceLoweredCoefficient (I := I) (M := M) g₀ g₁ g₀)‖ ^ 2 :=
              (Finset.mul_sum _ _ _).symm
          _ ≤ n * Fmcd q := mul_le_mul_of_nonneg_left (hmcd_jets q hq_le) hn_nn
      · refine mul_le_mul_of_nonneg_left ?_ hBS_nn
        refine Finset.sum_le_sum (fun l hl => ?_)
        have hl_le : l ≤ a + 1 := by
          rw [Finset.mem_range] at hl
          omega
        refine le_trans (hcipL (deTurckVectorFieldCovector (I := I) (M := M) g₀ g₁ g₀) l) ?_
        exact mul_le_mul_of_nonneg_left (hΩ_jets l hl_le) (hcipL_nn l)
  · have hEmpty : IsEmpty M := not_nonempty_iff.mp hM
    refine ⟨fun x => (hEmpty.false x).elim, ?_⟩
    intro i hi
    have hzero : ∀ q : ℕ,
        ‖iteratedCovGrad (I := I) g₀ 2 4 q (lieCorrectionZeroVectorBundleLift (I := I) (M := M) g₀ g₁)‖ ^ 2 = 0 := by
      intro q
      rw [SmoothCcTensor.norm_def,
        tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs]
      exact MeasureTheory.integral_of_isEmpty
    rw [Finset.sum_congr rfl (fun q _ => hzero q), Finset.sum_const, smul_zero]
    exact hF_nn i

private theorem lieCorrectionZeroVectorBundle_ballUniform
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ K : ℕ → ℝ, (∀ i, 0 ≤ K i) ∧
      ∀ (T T' : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀)
        (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        {δ' : ℝ} (_hδ'_le : δ' ≤ δ₀)
        (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ'),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ≤ R) →
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ≤ R) →
        ∀ (i : ℕ), i ≤ a → ∀ (s : ℝ), s ∈ Set.Icc (0 : ℝ) 1 →
          ‖iteratedCovGrad (I := I) g₀ 2 2 i
              (lieCorrectionZeroVectorBundle (I := I) (M := M) g₀ (metricPerturbationPath (I := I) g₀ T T' hδ hδ' s))‖ ^ 2
            ≤ K i := by
  classical
  obtain ⟨Λ, F, hΛ_nn, hF_nn, hcom⟩ :=
    cometricDoubleTraceField_order0sup_jetL2_ballUniform (I := I) (M := M) g₀ a
      ha_super hR hδ₀
  obtain ⟨ΛP, FP, hΛP_nn, hFP_nn, hvb⟩ := vbPass_jetL2 (I := I) (M := M) g₀ a ha_super hR hδ₀
  choose Cint hCint_nn hCint using
    (fun k : ℕ => exists_integrated_iteratedCovGrad_diagonalProductGrid_twoTerm_rs_le
      (I := I) (M := M) g₀ 4 2 2 4 k)
  set fr : ℝ := (Module.finrank ℝ E : ℝ) with hfr
  have hfr_nn : (0 : ℝ) ≤ fr := Nat.cast_nonneg _
  refine ⟨fun i => 4 * (operatorFieldApplicationGdiag (E := E) i *
    (Cint i * (ΛP * (fr * F i) + fr * Λ ^ 2 * FP i))), fun i => ?_, ?_⟩
  · refine mul_nonneg (by norm_num) (mul_nonneg (operatorFieldApplicationGdiag_nonneg (E := E) i)
      (mul_nonneg (hCint_nn i) (add_nonneg
        (mul_nonneg hΛP_nn (mul_nonneg hfr_nn (hF_nn i)))
        (mul_nonneg (mul_nonneg hfr_nn (sq_nonneg Λ)) (hFP_nn i)))))
  intro T T' δ hδ_le hδ δ' hδ'_le hδ' hTball hT'ball i hi s hs
  have hs0 : (0 : ℝ) ≤ s := hs.1
  have hs1 : s ≤ 1 := hs.2
  have h1ms : (0 : ℝ) ≤ 1 - s := by linarith
  have hδ_lt : δ < 1 := lt_of_le_of_lt hδ_le hδ₀
  have hδ'_lt : δ' < 1 := lt_of_le_of_lt hδ'_le hδ₀
  have hδP : gFibreOpBound (I := I) (M := M) g₀
      (ccTensorBilinSymm (I := I) g₀ (convexPerturbation (I := I) g₀ T T' s))
      ((1 - s) * δ' + s * δ) :=
    convexPerturbation_gFibreOpBound (I := I) (M := M) g₀ T T' hδ hδ' hs0 hs1
  have hδP_le : (1 - s) * δ' + s * δ ≤ δ₀ := by
    have e1 : (1 - s) * δ' ≤ (1 - s) * δ₀ := mul_le_mul_of_nonneg_left hδ'_le h1ms
    have e2 : s * δ ≤ s * δ₀ := mul_le_mul_of_nonneg_left hδ_le hs0
    have e3 : (1 - s) * δ₀ + s * δ₀ = δ₀ := by ring
    linarith [e1, e2, e3]
  have htie : ∀ (y : M) (v w : TangentSpace I y),
      (metricPerturbationPath (I := I) g₀ T T' hδ hδ' s).inner y v w =
        g₀.inner y v w +
          ccTensorBilinSymm (I := I) g₀ (convexPerturbation (I := I) g₀ T T' s) y v w :=
    fun y v w =>
      metricPerturbationPath_inner_of_mem (I := I) g₀ T T' hδ hδ'
        (Icc_subset_metricPerturbationPathDomain hδ_lt hδ'_lt hs) y v w
  have hPball : ∀ j : ℕ, j ≤ a + 2 →
      ‖iteratedCovGrad (I := I) g₀ 0 2 j (convexPerturbation (I := I) g₀ T T' s)‖ ≤ R := by
    intro j hj
    have heq : iteratedCovGrad (I := I) g₀ 0 2 j (convexPerturbation (I := I) g₀ T T' s)
        = (1 - s) • iteratedCovGrad (I := I) g₀ 0 2 j T'
          + s • iteratedCovGrad (I := I) g₀ 0 2 j T := by
      rw [show convexPerturbation (I := I) g₀ T T' s = (1 - s) • T' + s • T from rfl,
        iteratedCovGrad_add, iteratedCovGrad_smul, iteratedCovGrad_smul]
    rw [heq]
    calc ‖(1 - s) • iteratedCovGrad (I := I) g₀ 0 2 j T'
            + s • iteratedCovGrad (I := I) g₀ 0 2 j T‖
        ≤ ‖(1 - s) • iteratedCovGrad (I := I) g₀ 0 2 j T'‖
            + ‖s • iteratedCovGrad (I := I) g₀ 0 2 j T‖ := norm_add_le _ _
      _ = (1 - s) * ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖
            + s * ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ := by
          rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
            abs_of_nonneg h1ms, abs_of_nonneg hs0]
      _ ≤ (1 - s) * R + s * R :=
          add_le_add (mul_le_mul_of_nonneg_left (hT'ball j hj) h1ms)
            (mul_le_mul_of_nonneg_left (hTball j hj) hs0)
      _ = R := by ring
  obtain ⟨hsup0, hjet⟩ := hcom (metricPerturbationPath (I := I) g₀ T T' hδ hδ' s)
    (convexPerturbation (I := I) g₀ T T' s) hδP_le hδP htie hPball
  obtain ⟨hvbsup, hvbjet⟩ := hvb (metricPerturbationPath (I := I) g₀ T T' hδ hδ' s)
    (convexPerturbation (I := I) g₀ T T' s) hδP_le hδP htie hPball
  have hLsup : ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 4 2 x
      ((reindexedCometricDoubleTrace (I := I) (M := M) g₀
        (metricPerturbationPath (I := I) g₀ T T' hδ hδ' s)).toSection x) ≤
      Real.sqrt (fr * Λ ^ 2) ^ 2 := by
    intro x
    have h := riemannianFiberNormSq_iteratedCovGrad_reindexedCometricDoubleTrace_le (I := I) (M := M) g₀
      (metricPerturbationPath (I := I) g₀ T T' hδ hδ' s) 0 x
    rw [iteratedCovGrad_zero, iteratedCovGrad_zero] at h
    rw [Real.sq_sqrt (mul_nonneg hfr_nn (sq_nonneg Λ))]
    exact le_trans h (mul_le_mul_of_nonneg_left (hsup0 x) hfr_nn)
  have hPsup : ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 2 4 x
      ((lieCorrectionZeroVectorBundleLift (I := I) (M := M) g₀
        (metricPerturbationPath (I := I) g₀ T T' hδ hδ' s)).toSection x) ≤ Real.sqrt ΛP ^ 2 := by
    intro x
    rw [Real.sq_sqrt hΛP_nn]
    exact hvbsup x
  obtain ⟨hgrid_int, hgrid_bd⟩ := hCint i
    (reindexedCometricDoubleTrace (I := I) (M := M) g₀ (metricPerturbationPath (I := I) g₀ T T' hδ hδ' s))
    (lieCorrectionZeroVectorBundleLift (I := I) (M := M) g₀ (metricPerturbationPath (I := I) g₀ T T' hδ hδ' s))
    (Real.sqrt (fr * Λ ^ 2)) (Real.sqrt ΛP)
    (Real.sqrt_nonneg _) (Real.sqrt_nonneg _) hLsup hPsup
  have hLsum : ∑ m ∈ Finset.range (i + 1),
      ‖iteratedCovGrad (I := I) g₀ 4 2 m
        (reindexedCometricDoubleTrace (I := I) (M := M) g₀
          (metricPerturbationPath (I := I) g₀ T T' hδ hδ' s))‖ ^ 2 ≤ fr * F i := by
    calc ∑ m ∈ Finset.range (i + 1),
          ‖iteratedCovGrad (I := I) g₀ 4 2 m
            (reindexedCometricDoubleTrace (I := I) (M := M) g₀
              (metricPerturbationPath (I := I) g₀ T T' hδ hδ' s))‖ ^ 2
        ≤ ∑ m ∈ Finset.range (i + 1), fr *
            ‖iteratedCovGrad (I := I) g₀ 3 1 m
              (cometricCastG0 (I := I) g₀
                (metricPerturbationPath (I := I) g₀ T T' hδ hδ' s))‖ ^ 2 :=
          Finset.sum_le_sum (fun m _ => norm_iteratedCovGrad_reindexedCometricDoubleTrace_sq_le (I := I) (M := M) g₀ _ m)
      _ = fr * ∑ m ∈ Finset.range (i + 1),
            ‖iteratedCovGrad (I := I) g₀ 3 1 m
              (cometricCastG0 (I := I) g₀
                (metricPerturbationPath (I := I) g₀ T T' hδ hδ' s))‖ ^ 2 := by
          rw [Finset.mul_sum]
      _ ≤ fr * F i := mul_le_mul_of_nonneg_left (hjet i hi) hfr_nn
  have hnorm : ‖iteratedCovGrad (I := I) g₀ 2 2 i
        (ccOperatorFieldComp (I := I) (M := M) g₀ 2 4 2
          (reindexedCometricDoubleTrace (I := I) (M := M) g₀ (metricPerturbationPath (I := I) g₀ T T' hδ hδ' s))
          (lieCorrectionZeroVectorBundleLift (I := I) (M := M) g₀ (metricPerturbationPath (I := I) g₀ T T' hδ hδ' s)))‖ ^ 2 ≤
      operatorFieldApplicationGdiag (E := E) i *
        (Cint i * (Real.sqrt ΛP ^ 2 * ∑ m ∈ Finset.range (i + 1),
            ‖iteratedCovGrad (I := I) g₀ 4 2 m
              (reindexedCometricDoubleTrace (I := I) (M := M) g₀
                (metricPerturbationPath (I := I) g₀ T T' hδ hδ' s))‖ ^ 2
          + Real.sqrt (fr * Λ ^ 2) ^ 2 * ∑ l ∈ Finset.range (i + 1),
            ‖iteratedCovGrad (I := I) g₀ 2 4 l
              (lieCorrectionZeroVectorBundleLift (I := I) (M := M) g₀
                (metricPerturbationPath (I := I) g₀ T T' hδ hδ' s))‖ ^ 2)) := by
    have key := normSq_le_integral_of_pointwise_fiberNormSq_le_rs (I := I) (M := M) g₀ 2 (2 + i)
      (iteratedCovGrad (I := I) g₀ 2 2 i
        (ccOperatorFieldComp (I := I) (M := M) g₀ 2 4 2
          (reindexedCometricDoubleTrace (I := I) (M := M) g₀ (metricPerturbationPath (I := I) g₀ T T' hδ hδ' s))
          (lieCorrectionZeroVectorBundleLift (I := I) (M := M) g₀ (metricPerturbationPath (I := I) g₀ T T' hδ hδ' s))))
      _ (hgrid_int.const_mul (operatorFieldApplicationGdiag (E := E) i))
      (fun x => riemannianFiberNormSq_iteratedCovGrad_operatorFieldComposition_diagonalProductGrid_rankLeft_le
        (I := I) (M := M) g₀ i 2 4 2
        (reindexedCometricDoubleTrace (I := I) (M := M) g₀ (metricPerturbationPath (I := I) g₀ T T' hδ hδ' s))
        (lieCorrectionZeroVectorBundleLift (I := I) (M := M) g₀ (metricPerturbationPath (I := I) g₀ T T' hδ hδ' s)) x)
    refine le_trans key ?_
    rw [MeasureTheory.integral_const_mul]
    exact mul_le_mul_of_nonneg_left hgrid_bd (operatorFieldApplicationGdiag_nonneg (E := E) i)
  have hsmul : ‖iteratedCovGrad (I := I) g₀ 2 2 i
        (lieCorrectionZeroVectorBundle (I := I) (M := M) g₀ (metricPerturbationPath (I := I) g₀ T T' hδ hδ' s))‖ ^ 2 =
      4 * ‖iteratedCovGrad (I := I) g₀ 2 2 i
        (ccOperatorFieldComp (I := I) (M := M) g₀ 2 4 2
          (reindexedCometricDoubleTrace (I := I) (M := M) g₀ (metricPerturbationPath (I := I) g₀ T T' hδ hδ' s))
          (lieCorrectionZeroVectorBundleLift (I := I) (M := M) g₀ (metricPerturbationPath (I := I) g₀ T T' hδ hδ' s)))‖ ^ 2 := by
    rw [lieCorrectionZeroVectorBundle_eq_ccOperatorFieldComp, iteratedCovGrad_smul, norm_smul, mul_pow]
    norm_num
  rw [hsmul]
  have hΛPsq : Real.sqrt ΛP ^ 2 = ΛP := Real.sq_sqrt hΛP_nn
  have hΛsq : Real.sqrt (fr * Λ ^ 2) ^ 2 = fr * Λ ^ 2 :=
    Real.sq_sqrt (mul_nonneg hfr_nn (sq_nonneg Λ))
  rw [hΛPsq, hΛsq] at hnorm
  have hmid : operatorFieldApplicationGdiag (E := E) i *
      (Cint i * (ΛP * ∑ m ∈ Finset.range (i + 1),
          ‖iteratedCovGrad (I := I) g₀ 4 2 m
            (reindexedCometricDoubleTrace (I := I) (M := M) g₀
              (metricPerturbationPath (I := I) g₀ T T' hδ hδ' s))‖ ^ 2
        + fr * Λ ^ 2 * ∑ l ∈ Finset.range (i + 1),
          ‖iteratedCovGrad (I := I) g₀ 2 4 l
            (lieCorrectionZeroVectorBundleLift (I := I) (M := M) g₀
              (metricPerturbationPath (I := I) g₀ T T' hδ hδ' s))‖ ^ 2)) ≤
      operatorFieldApplicationGdiag (E := E) i * (Cint i * (ΛP * (fr * F i) + fr * Λ ^ 2 * FP i)) := by
    refine mul_le_mul_of_nonneg_left ?_ (operatorFieldApplicationGdiag_nonneg (E := E) i)
    refine mul_le_mul_of_nonneg_left ?_ (hCint_nn i)
    have hA := mul_le_mul_of_nonneg_left hLsum hΛP_nn
    have hB := mul_le_mul_of_nonneg_left (hvbjet i hi)
      (mul_nonneg hfr_nn (sq_nonneg Λ))
    linarith [hA, hB]
  refine le_trans (mul_le_mul_of_nonneg_left (le_trans hnorm hmid) (by norm_num : (0:ℝ) ≤ 4)) ?_
  exact le_of_eq (by ring)

private theorem lieCorrectionZeroVectorBundle_metricPerturbationPath_perOrder_topOrderSeparated
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ Ktop : ℝ, 0 ≤ Ktop ∧ ∃ Kc : ℕ → ℝ, (∀ i, 0 ≤ Kc i) ∧
      ∀ (T T' : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀)
        (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        {δ' : ℝ} (_hδ'_le : δ' ≤ δ₀)
        (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ'),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ≤ R) →
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ≤ R) →
        ∀ (s : ℝ), s ∈ Set.Icc (0 : ℝ) 1 →
        ∀ (i : ℕ), i ≤ a →
          ‖iteratedCovGrad (I := I) g₀ 2 2 i
              (lieCorrectionZeroVectorBundle (I := I) (M := M) g₀
                (metricPerturbationPath (I := I) g₀ T T' hδ hδ' s))‖ ^ 2 ≤
            Ktop * (‖iteratedCovGrad (I := I) g₀ 0 2 (i + 2) T‖ ^ 2 +
              ‖iteratedCovGrad (I := I) g₀ 0 2 (i + 2) T'‖ ^ 2) +
            Kc i * (1 + ∑ j ∈ Finset.range (i + 3),
              (‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ^ 2 +
                ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ^ 2)) := by
  obtain ⟨K, hK_nn, hK⟩ := lieCorrectionZeroVectorBundle_ballUniform (I := I) (M := M) g₀ a ha_super hR hδ₀
  refine ⟨0, le_refl 0, K, hK_nn, ?_⟩
  intro T T' δ hδ_le hδ δ' hδ'_le hδ' hTball hT'ball s hs i hi
  have hb := hK T T' hδ_le hδ hδ'_le hδ' hTball hT'ball i hi s hs
  have hlow_nn : (0 : ℝ) ≤ ∑ j ∈ Finset.range (i + 3),
      (‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ^ 2 +
        ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ^ 2) :=
    Finset.sum_nonneg (fun j _ => add_nonneg (sq_nonneg _) (sq_nonneg _))
  nlinarith only [hb, hK_nn i, hlow_nn, mul_nonneg (hK_nn i) hlow_nn]


end DifferentialGeometry.Integral.Connection

end
