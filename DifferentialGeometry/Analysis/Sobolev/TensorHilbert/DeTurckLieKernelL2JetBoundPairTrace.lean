import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.DeTurckLieKernelL2JetBoundRaisedKernelGrid
open DifferentialGeometry.Tensor.Auxiliary
open DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Analysis.Elliptic
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection

noncomputable section

set_option backward.isDefEq.respectTransparency false

open MeasureTheory Set Filter Topology Bundle Manifold DifferentialGeometry.Tensor0SBundle ContinuousLinearMap
open scoped ENNReal NNReal BigOperators Manifold ContDiff

namespace DifferentialGeometry.Analysis.Sobolev

open DifferentialGeometry
open DifferentialGeometry.PDE.RicciFlow DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
  (connDiffCovDerivBiContrFib dLaBiContrFib_contMDiff deTurckLieDLbFib deTurckLieDLbFib_contMDiff
    deTurckLieFib deTurckLieCoeffField deTurckLieCoeffField_toSection
    deTurckConnDiffCovDeriv connDiff_pairing_mdiffAt connDiffCovDerivOp dLaCovKernel_apply_extend)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

open DifferentialGeometry.Analysis.Spectral.MetricRealization
open DifferentialGeometry.PDE.DeTurck.RicciLinearization
  (realizedFam convexPerturbation realizedFam_inner_of_mem convexPerturbation_gFibreOpBound_abs
    abs_convex_smallConstant_lt_one realizedSmallSet)
open DifferentialGeometry.Analysis.Laplacian
  (metric_inner_self_nonneg metric_inner_cauchy_schwarz_sq)
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
  (covGrad connDiff_gFibreNorm_le_iteratedCovGrad_of_lt_one dLaBiContrFibFixedFrame_toModel)
open DifferentialGeometry.Geometry.Curvature
  (exists_covDerivConnDiff_gQuadratic_le_of_jetEnvelope
    abs_tensor_one_three_flat_eval_le_fibreNorm_mul_sqrt)
open DifferentialGeometry.Analysis.Sobolev.TensorHilbert
  (g0FlatCLM cotangentToDual_g0FlatCLM g0FlatCLM_apply)

open DifferentialGeometry.Analysis.Parabolic.TensorSpectral

section DLaGridBrick

open DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis.Spectral.DeTurck
open DifferentialGeometry.Analysis.Sobolev.TensorHilbert

set_option backward.isDefEq.respectTransparency false in
omit [BoundarylessManifold I M] in
private lemma pureDTdla_eq_trace_fullRaised (g₀ g₁ : SmoothRiemannianMetric I M)
    (s : ℕ) :
    cometricDoubleTraceSmoothCcTensor (I := I) (M := M) g₀ g₁ s =
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
        (cometricDoubleTraceSmoothCcTensor (I := I) (M := M) g₀ g₁ s).toSection x) Z) mm =
      ∑ c : Fin (Module.finrank ℝ E),
        Tensor0SSpace.toModel Z
          (Fin.cons ((smoothOrthoFrame (I := I) g₁ x c x : TangentSpace I x) : E)
            (Fin.cons ((smoothOrthoFrame (I := I) g₁ x c x : TangentSpace I x) : E) mm)) := by
    rw [show ((show Tensor0SSpace (s + 2) I x →L[ℝ] Tensor0SSpace s I x from
        (cometricDoubleTraceSmoothCcTensor (I := I) (M := M) g₀ g₁ s).toSection x) Z) =
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
    have h1 := smoothOrthoFrame_center_repr (I := I) (M := M) g₁ x
      (metricComparisonEndo (I := I) g₀ g₁ x (smoothOrthoFrame (I := I) g₀ x a x))
    rw [show (show E from metricComparisonEndo (I := I) g₀ g₁ x
        (smoothOrthoFrame (I := I) g₀ x a x)) =
        metricComparisonEndo (I := I) g₀ g₁ x (smoothOrthoFrame (I := I) g₀ x a x) from rfl]
    conv_lhs => rw [h1]
    refine Finset.sum_congr rfl fun c _ => ?_
    congr 1
    rw [g₁.symm x (smoothOrthoFrame (I := I) g₁ x c x)
      (metricComparisonEndo (I := I) g₀ g₁ x (smoothOrthoFrame (I := I) g₀ x a x))]
    rw [g1_inner_gInvRaisedEndo_left_dla (I := I) (M := M) g₀ g₁ x
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
        exact toModel_cons_sum_smul_dla (E := E) x (Tensor0SSpace.toModel Z)
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
        have hsum := toModel_cons_cons_sum_smul_dla (E := E) x (Tensor0SSpace.toModel Z)
          ((smoothOrthoFrame (I := I) g₁ x c x : TangentSpace I x) : E)
          (Module.finrank ℝ E)
          (fun a => g₀.inner x (smoothOrthoFrame (I := I) g₀ x a x)
            (smoothOrthoFrame (I := I) g₁ x c x))
          (fun a => (smoothOrthoFrame (I := I) g₀ x a x : E)) mm
        rw [← hsum]
        congr 2
        have hrep0 := smoothOrthoFrame_center_repr (I := I) (M := M) g₀ x
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

def pairTraceOpDla (g₀ g₁ : SmoothRiemannianMetric I M) : SmoothCcTensor g₀ 6 2 :=
  ccOperatorFieldComp (I := I) (M := M) g₀ 6 4 2
    (cometricDoubleTraceSmoothCcTensor (I := I) (M := M) g₀ g₁ 2)
    (cometricDoubleTraceSmoothCcTensor (I := I) (M := M) g₀ g₁ 4)

set_option backward.isDefEq.respectTransparency false in
omit [BoundarylessManifold I M] in
private lemma pairTraceOpDla_apply_toModel (g₀ gm : SmoothRiemannianMetric I M)
    (X : SmoothCcTensor g₀ 0 4) (x : M) (D : Tensor0SSpace 2 I x) (v : Fin 2 → E) :
    Tensor0SSpace.toModel
        ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
          (ccOperatorFieldComp (I := I) (M := M) g₀ 2 6 2 (pairTraceOpDla (I := I) (M := M) g₀ gm)
            (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 sigmaE0dla
              (slotExtendIter (I := I) (M := M) g₀ 0 4 2 X))).toSection x) D) v =
      ∑ b : Fin (Module.finrank ℝ E), ∑ a : Fin (Module.finrank ℝ E),
        Tensor0SSpace.toModel D
            ![(smoothOrthoFrame (I := I) gm x a x : E),
              (smoothOrthoFrame (I := I) gm x b x : E)] *
          unitModel (I := I) (M := M) g₀ 4 X x
            ![v 0, v 1, (smoothOrthoFrame (I := I) gm x a x : E),
              (smoothOrthoFrame (I := I) gm x b x : E)] := by
  classical
  set Y : Tensor0SSpace 6 I x :=
    (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 6 I x from
      (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 sigmaE0dla
        (slotExtendIter (I := I) (M := M) g₀ 0 4 2 X)).toSection x) D with hY_def
  have hYval : ∀ w : Fin 6 → TangentSpace I x,
      Tensor0SSpace.toModel Y w =
        Tensor0SSpace.toModel D ![w 1, w 3] *
          unitModel (I := I) (M := M) g₀ 4 X x ![w 4, w 5, w 0, w 2] := by
    intro w
    rw [hY_def]
    rw [show ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 6 I x from
        (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 sigmaE0dla
          (slotExtendIter (I := I) (M := M) g₀ 0 4 2 X)).toSection x) D) =
        ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 6 I x from
          tensorRS_domDomCongr sigmaE0dla
            ((slotExtendIter (I := I) (M := M) g₀ 0 4 2 X).toSection x)) D) from by
      rw [rsDomDomCongrSection_toSection]]
    rw [toModel_rsDomDomCongr_apply (I := I) (M := M) sigmaE0dla
      ((slotExtendIter (I := I) (M := M) g₀ 0 4 2 X).toSection x) D]
    rw [ContinuousMultilinearMap.domDomCongr_apply]
    rw [slotExtendIter_two_toModel_dla (I := I) (M := M) g₀ X x D
      (fun i => w (sigmaE0dla i))]
    refine congrArg₂ (· * ·) ?_ ?_
    · refine congrArg _ ?_
      funext k
      fin_cases k <;> rfl
    · refine congrArg _ ?_
      funext k
      fin_cases k <;> rfl
  rw [show ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
      (ccOperatorFieldComp (I := I) (M := M) g₀ 2 6 2 (pairTraceOpDla (I := I) (M := M) g₀ gm)
        (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 sigmaE0dla
          (slotExtendIter (I := I) (M := M) g₀ 0 4 2 X))).toSection x) D) =
      cometricDoubleTraceFib (I := I) gm 2 x
        (cometricDoubleTraceFib (I := I) gm 4 x Y) from by
    rw [hY_def]
    rw [appCcRS_toSection]
    rfl]
  rw [cometricDoubleTraceFib_toModel (I := I) gm 2 x]
  rw [modelDoubleTrace_apply (E := E) 2 (cometricLmodel (I := I) gm x)]
  rw [cometric_dualTrace_eq_orthoFrame_diag (I := I) gm x
    (mem_smoothOrthoFrameNbhd_self (I := I) (M := M) x)
    (Tensor0SSpace.toModel (cometricDoubleTraceFib (I := I) gm 4 x Y))
    (fun j => (v j : E))]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [cometricDoubleTraceFib_toModel (I := I) gm 4 x Y]
  rw [modelDoubleTrace_apply (E := E) 4 (cometricLmodel (I := I) gm x)]
  rw [cometric_dualTrace_eq_orthoFrame_diag (I := I) gm x
    (mem_smoothOrthoFrameNbhd_self (I := I) (M := M) x)
    (Tensor0SSpace.toModel Y)
    (Fin.cons ((smoothOrthoFrame (I := I) gm x b x : TangentSpace I x) : E)
      (Fin.cons ((smoothOrthoFrame (I := I) gm x b x : TangentSpace I x) : E)
        (fun j => (v j : E))))]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [hYval]
  rfl

def dLaSymCc (g₀ : SmoothRiemannianMetric I M) (T : SmoothCcTensor g₀ 0 2)
    (g₁ g_bg : SmoothRiemannianMetric I M) : SmoothCcTensor g₀ 0 4 :=
  domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 4) 1)
      (dLaLoweredG1Cc (I := I) (M := M) g₀ T g₁ g_bg) +
    dLaLoweredG1Cc (I := I) (M := M) g₀ T g₁ g_bg

set_option backward.isDefEq.respectTransparency false in
omit [NeZero (Module.finrank ℝ E)] in
private lemma dLaLoweredG1Cc_unitModel_apply (g₀ : SmoothRiemannianMetric I M)
    (T : SmoothCcTensor g₀ 0 2) (g₁ g_bg : SmoothRiemannianMetric I M)
    (htie : ∀ (y : M) (v w : TangentSpace I y),
      g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ T y v w)
    (x : M) (m : Fin 4 → TangentSpace I x) :
    unitModel (I := I) (M := M) g₀ 4
        (dLaLoweredG1Cc (I := I) (M := M) g₀ T g₁ g_bg) x m =
      g₁.inner x (connDiffCovDerivOp (I := I) g₁ g_bg x (m 1) (m 2) (m 3)) (m 0) := by
  rw [dLaLoweredG1Cc, unitModel_add_dla (I := I) (M := M) g₀ 4]
  rw [dLaLoweredCc_unitModel_apply (I := I) (M := M) g₀ g₁ g_bg x m]
  rw [dLaLoweredPerturbCc_unitModel_apply (I := I) (M := M) g₀ T g₁ g_bg x m]
  rw [htie x (connDiffCovDerivOp (I := I) g₁ g_bg x (m 1) (m 2) (m 3)) (m 0)]

set_option backward.isDefEq.respectTransparency false in
omit [NeZero (Module.finrank ℝ E)] in
private lemma dLaSymCc_unitModel_apply (g₀ : SmoothRiemannianMetric I M)
    (T : SmoothCcTensor g₀ 0 2) (g₁ g_bg : SmoothRiemannianMetric I M)
    (htie : ∀ (y : M) (v w : TangentSpace I y),
      g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ T y v w)
    (x : M) (m : Fin 4 → TangentSpace I x) :
    unitModel (I := I) (M := M) g₀ 4
        (dLaSymCc (I := I) (M := M) g₀ T g₁ g_bg) x m =
      g₁.inner x (connDiffCovDerivOp (I := I) g₁ g_bg x (m 0) (m 2) (m 3)) (m 1) +
        g₁.inner x (connDiffCovDerivOp (I := I) g₁ g_bg x (m 1) (m 2) (m 3)) (m 0) := by
  rw [dLaSymCc, unitModel_add_dla (I := I) (M := M) g₀ 4]
  rw [domDomCongrSection_unitModel (I := I) g₀ (Equiv.swap (0 : Fin 4) 1)
    (dLaLoweredG1Cc (I := I) (M := M) g₀ T g₁ g_bg) x]
  rw [ContinuousMultilinearMap.domDomCongr_apply]
  rw [dLaLoweredG1Cc_unitModel_apply (I := I) (M := M) g₀ T g₁ g_bg htie x
    (fun i => m ((Equiv.swap (0 : Fin 4) 1) i))]
  rw [dLaLoweredG1Cc_unitModel_apply (I := I) (M := M) g₀ T g₁ g_bg htie x m]
  rw [show (Equiv.swap (0 : Fin 4) 1) 0 = 1 from Equiv.swap_apply_left 0 1,
    show (Equiv.swap (0 : Fin 4) 1) 1 = 0 from Equiv.swap_apply_right 0 1,
    show (Equiv.swap (0 : Fin 4) 1) 2 = 2 from by decide,
    show (Equiv.swap (0 : Fin 4) 1) 3 = 3 from by decide]

private lemma iCG_succ_cometricDT_zero_dla (g₀ : SmoothRiemannianMetric I M) (s m : ℕ) :
    iteratedCovGrad (I := I) g₀ (s + 2) s (m + 1)
      (cometricDoubleTraceField (I := I) g₀ s) = 0 := by
  induction m with
  | zero =>
      rw [iteratedCovGrad_succ, iteratedCovGrad_zero]
      exact cometricDoubleTraceField_covGrad_eq_zero (I := I) g₀ s
  | succ m' ih =>
      rw [iteratedCovGrad_succ, ih, covGrad_zero]

private theorem exists_rfns_pureDT_tgrid (g₀ : SmoothRiemannianMetric I M) (s : ℕ)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ C : ℕ → ℝ, (∀ j, 0 ≤ C j) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (T : SmoothCcTensor g₀ 0 2)
        (_htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ T y v w)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀) (_hδ0 : 0 ≤ δ)
        (_hbound : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T)
          δ)
        (j : ℕ) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g₀ (s + 2) (s + j) x
            ((iteratedCovGrad (I := I) g₀ (s + 2) s j
              (cometricDoubleTraceSmoothCcTensor (I := I) (M := M) g₀ g₁ s)).toSection x) ≤
          C j * antidiagonalTupleGridPartialSum
            (fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
              ((iteratedCovGrad (I := I) g₀ 0 2 l T).toSection x)) (j + 1) := by
  classical
  obtain ⟨S, hS_nn, hS⟩ := exists_rfns_iteratedCovGrad_sharpFlatEndoCc_tgrid_dla
    (I := I) (M := M) g₀ hδ₀
  obtain ⟨c0, hc0_nn, hc0⟩ := exists_fixedField_rfns_jet_dla (I := I) (M := M) g₀ (s + 2) s
    (cometricDoubleTraceField (I := I) g₀ s)
  set fr : ℝ := (Module.finrank ℝ E : ℝ) with hfr_def
  have hfr_nn : 0 ≤ fr := Nat.cast_nonneg _
  refine ⟨fun j => diagonalGridGrowthFactor (E := E) j *
      (c0 0 * ∑ l ∈ Finset.range (j + 1), fr ^ (s + 1) * S l),
    fun j => mul_nonneg (appCcGdiag_nonneg (E := E) j)
      (mul_nonneg (hc0_nn 0) (Finset.sum_nonneg fun l _ =>
        mul_nonneg (by positivity) (hS_nn l))), ?_⟩
  intro g₁ T htie δ hδ_le hδ0 hbound j x
  set b : ℕ → ℝ := fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
    ((iteratedCovGrad (I := I) g₀ 0 2 l T).toSection x) with hb_def
  have hb : ∀ l, 0 ≤ b l :=
    fun l => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + l) x _
  have hsFlat : ∀ l : ℕ,
      riemannianFiberNormSq (I := I) (M := M) g₀ (s + 2) ((s + 2) + l) x
        ((iteratedCovGrad (I := I) g₀ (s + 2) (s + 2) l
          (endoSlotZeroCcTensor (I := I) (M := M) g₀ (s + 1)
            (fullRaisedEndoField (I := I) (M := M) g₀ g₁))).toSection x) ≤
      (fr ^ (s + 1) * S l) * Combinatorics.antidiagonalTupleGrid b l := by
    intro l
    refine le_trans (rfns_iteratedCovGrad_slotInsertEndoCc_le_endo (I := I) (M := M) g₀ (s + 1)
      (fullRaisedEndoField (I := I) (M := M) g₀ g₁) l x) ?_
    rw [← hfr_def]
    have hins : riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + l) x
        ((iteratedCovGrad (I := I) g₀ 1 1 l
          (endoSlotZeroCcTensor (I := I) (M := M) g₀ 0
            (fullRaisedEndoField (I := I) (M := M) g₀ g₁))).toSection x) ≤
        S l * Combinatorics.antidiagonalTupleGrid b l := by
      rw [← sharpFlatEndoCc_eq_slotInsert_fullRaised_dla (I := I) (M := M) g₀ g₁]
      exact hS g₁ T htie hδ_le hδ0 hbound l x
    calc fr ^ (s + 1) * riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + l) x
          ((iteratedCovGrad (I := I) g₀ 1 1 l
            (endoSlotZeroCcTensor (I := I) (M := M) g₀ 0
              (fullRaisedEndoField (I := I) (M := M) g₀ g₁))).toSection x)
        ≤ fr ^ (s + 1) * (S l * Combinatorics.antidiagonalTupleGrid b l) :=
          mul_le_mul_of_nonneg_left hins (by positivity)
      _ = (fr ^ (s + 1) * S l) * Combinatorics.antidiagonalTupleGrid b l := by ring
  rw [pureDTdla_eq_trace_fullRaised (I := I) (M := M) g₀ g₁ s]
  refine le_trans
    (riemannianFiberNormSq_iteratedCovGrad_ccTensorCompose_diagonalProductGrid_leftFactor_le
    (I := I) (M := M) g₀ j (s + 2) (s + 2) s
    (cometricDoubleTraceField (I := I) g₀ s)
    (endoSlotZeroCcTensor (I := I) (M := M) g₀ (s + 1)
      (fullRaisedEndoField (I := I) (M := M) g₀ g₁)) x) ?_
  have hzero : ∀ i' ∈ Finset.range (j + 1), i' ≠ 0 →
      riemannianFiberNormSq (I := I) (M := M) g₀ (s + 2) (s + i') x
          ((iteratedCovGrad (I := I) g₀ (s + 2) s i'
            (cometricDoubleTraceField (I := I) g₀ s)).toSection x) *
        ∑ l ∈ Finset.range (j + 1 - i'),
          riemannianFiberNormSq (I := I) (M := M) g₀ (s + 2) ((s + 2) + l) x
            ((iteratedCovGrad (I := I) g₀ (s + 2) (s + 2) l
              (endoSlotZeroCcTensor (I := I) (M := M) g₀ (s + 1)
                (fullRaisedEndoField (I := I) (M := M) g₀ g₁))).toSection x) = 0 := by
    intro i' _ hi'0
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hi'0
    rw [iCG_succ_cometricDT_zero_dla (I := I) (M := M) g₀ s m]
    rw [show ((0 : SmoothCcTensor g₀ (s + 2) (s + (m + 1))).toSection x) =
        (0 : TensorRSSpace (s + 2) (s + (m + 1)) I x) from by
      rw [SmoothCcTensor.toSection_zero]; rfl]
    rw [riemannianFiberNormSq_zero (I := I) (M := M) g₀ (s + 2) (s + (m + 1)) x]
    rw [zero_mul]
  have hsum_eq : (∑ i' ∈ Finset.range (j + 1),
      riemannianFiberNormSq (I := I) (M := M) g₀ (s + 2) (s + i') x
          ((iteratedCovGrad (I := I) g₀ (s + 2) s i'
            (cometricDoubleTraceField (I := I) g₀ s)).toSection x) *
        ∑ l ∈ Finset.range (j + 1 - i'),
          riemannianFiberNormSq (I := I) (M := M) g₀ (s + 2) ((s + 2) + l) x
            ((iteratedCovGrad (I := I) g₀ (s + 2) (s + 2) l
              (endoSlotZeroCcTensor (I := I) (M := M) g₀ (s + 1)
                (fullRaisedEndoField (I := I) (M := M) g₀ g₁))).toSection x)) =
      riemannianFiberNormSq (I := I) (M := M) g₀ (s + 2) (s + 0) x
          ((iteratedCovGrad (I := I) g₀ (s + 2) s 0
            (cometricDoubleTraceField (I := I) g₀ s)).toSection x) *
        ∑ l ∈ Finset.range (j + 1 - 0),
          riemannianFiberNormSq (I := I) (M := M) g₀ (s + 2) ((s + 2) + l) x
            ((iteratedCovGrad (I := I) g₀ (s + 2) (s + 2) l
              (endoSlotZeroCcTensor (I := I) (M := M) g₀ (s + 1)
                (fullRaisedEndoField (I := I) (M := M) g₀ g₁))).toSection x) := by
    refine Finset.sum_eq_single_of_mem 0 (Finset.mem_range.mpr (by omega)) ?_
    intro i' hi' hi'0
    exact hzero i' hi' hi'0
  rw [hsum_eq]
  have hc0' : riemannianFiberNormSq (I := I) (M := M) g₀ (s + 2) (s + 0) x
      ((iteratedCovGrad (I := I) g₀ (s + 2) s 0
        (cometricDoubleTraceField (I := I) g₀ s)).toSection x) ≤ c0 0 := hc0 0 x
  have hsumS : (∑ l ∈ Finset.range (j + 1 - 0),
      riemannianFiberNormSq (I := I) (M := M) g₀ (s + 2) ((s + 2) + l) x
        ((iteratedCovGrad (I := I) g₀ (s + 2) (s + 2) l
          (endoSlotZeroCcTensor (I := I) (M := M) g₀ (s + 1)
            (fullRaisedEndoField (I := I) (M := M) g₀ g₁))).toSection x)) ≤
      (∑ l ∈ Finset.range (j + 1), fr ^ (s + 1) * S l) *
        antidiagonalTupleGridPartialSum b (j + 1) := by
    rw [show j + 1 - 0 = j + 1 from rfl]
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun l hl => ?_
    rw [Finset.mem_range] at hl
    refine le_trans (hsFlat l) ?_
    refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg (by positivity) (hS_nn l))
    exact grid_le_dLaGridWin b hb (by omega)
  have hrfns_nn : 0 ≤ riemannianFiberNormSq (I := I) (M := M) g₀ (s + 2) (s + 0) x
      ((iteratedCovGrad (I := I) g₀ (s + 2) s 0
        (cometricDoubleTraceField (I := I) g₀ s)).toSection x) :=
    riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ (s + 2) (s + 0) x _
  have hsum_nn : 0 ≤ ∑ l ∈ Finset.range (j + 1 - 0),
      riemannianFiberNormSq (I := I) (M := M) g₀ (s + 2) ((s + 2) + l) x
        ((iteratedCovGrad (I := I) g₀ (s + 2) (s + 2) l
          (endoSlotZeroCcTensor (I := I) (M := M) g₀ (s + 1)
            (fullRaisedEndoField (I := I) (M := M) g₀ g₁))).toSection x) :=
    Finset.sum_nonneg fun l _ =>
      riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ (s + 2) ((s + 2) + l) x _
  refine le_trans (mul_le_mul_of_nonneg_left
    (mul_le_mul hc0' hsumS hsum_nn (hc0_nn 0)) (appCcGdiag_nonneg (E := E) j)) ?_
  rw [← mul_assoc, ← mul_assoc]
  rw [mul_assoc (diagonalGridGrowthFactor (E := E) j) (c0 0)]

theorem exists_rfns_pairTraceOpDla_tgrid (g₀ : SmoothRiemannianMetric I M)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ C : ℕ → ℝ, (∀ j, 0 ≤ C j) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (T : SmoothCcTensor g₀ 0 2)
        (_htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ T y v w)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀) (_hδ0 : 0 ≤ δ)
        (_hbound : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T)
          δ)
        (j : ℕ) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g₀ 6 (2 + j) x
            ((iteratedCovGrad (I := I) g₀ 6 2 j
              (pairTraceOpDla (I := I) (M := M) g₀ g₁)).toSection x) ≤
          C j * antidiagonalTupleGridPartialSum
            (fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
              ((iteratedCovGrad (I := I) g₀ 0 2 l T).toSection x)) (j + 1) := by
  classical
  obtain ⟨C2, hC2_nn, hC2⟩ := exists_rfns_pureDT_tgrid (I := I) (M := M) g₀ 2 hδ₀
  obtain ⟨C4, hC4_nn, hC4⟩ := exists_rfns_pureDT_tgrid (I := I) (M := M) g₀ 4 hδ₀
  refine ⟨fun j => diagonalGridGrowthFactor (E := E) j * ∑ i' ∈ Finset.range (j + 1),
      C2 i' * ∑ l ∈ Finset.range (j + 1 - i'), C4 l * antidiagonalTuplePairCount (i' + 1) (l + 1),
    fun j => mul_nonneg (appCcGdiag_nonneg (E := E) j)
      (Finset.sum_nonneg fun i' _ => mul_nonneg (hC2_nn i')
        (Finset.sum_nonneg fun l _ => mul_nonneg (hC4_nn l) (dLaPairCount_nonneg _ _))), ?_⟩
  intro g₁ T htie δ hδ_le hδ0 hbound j x
  set b : ℕ → ℝ := fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
    ((iteratedCovGrad (I := I) g₀ 0 2 l T).toSection x) with hb_def
  have hb : ∀ l, 0 ≤ b l :=
    fun l => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + l) x _
  set W : ℝ := antidiagonalTupleGridPartialSum b (j + 1) with hW_def
  have hW_nn : 0 ≤ W := dLaGridWin_nonneg b hb (j + 1)
  refine le_trans
    (riemannianFiberNormSq_iteratedCovGrad_ccTensorCompose_diagonalProductGrid_leftFactor_le
    (I := I) (M := M) g₀ j 6 4 2
    (cometricDoubleTraceSmoothCcTensor (I := I) (M := M) g₀ g₁ 2)
    (cometricDoubleTraceSmoothCcTensor (I := I) (M := M) g₀ g₁ 4) x) ?_
  have hcell : ∀ i' ∈ Finset.range (j + 1),
      riemannianFiberNormSq (I := I) (M := M) g₀ 4 (2 + i') x
          ((iteratedCovGrad (I := I) g₀ 4 2 i'
            (cometricDoubleTraceSmoothCcTensor (I := I) (M := M) g₀ g₁ 2)).toSection x) *
        ∑ l ∈ Finset.range (j + 1 - i'),
          riemannianFiberNormSq (I := I) (M := M) g₀ 6 (4 + l) x
            ((iteratedCovGrad (I := I) g₀ 6 4 l
              (cometricDoubleTraceSmoothCcTensor (I := I) (M := M) g₀ g₁ 4)).toSection x) ≤
      (C2 i' * ∑ l ∈ Finset.range (j + 1 - i'), C4 l * antidiagonalTuplePairCount (i' + 1) (l + 1))
        * W := by
    intro i' hi'
    rw [Finset.mem_range] at hi'
    have hA1 : riemannianFiberNormSq (I := I) (M := M) g₀ 4 (2 + i') x
        ((iteratedCovGrad (I := I) g₀ 4 2 i'
          (cometricDoubleTraceSmoothCcTensor (I := I) (M := M) g₀ g₁ 2)).toSection x) ≤
        C2 i' * antidiagonalTupleGridPartialSum b (i' + 1) :=
      hC2 g₁ T htie hδ_le hδ0 hbound i' x
    have hA2 : (∑ l ∈ Finset.range (j + 1 - i'),
        riemannianFiberNormSq (I := I) (M := M) g₀ 6 (4 + l) x
          ((iteratedCovGrad (I := I) g₀ 6 4 l
            (cometricDoubleTraceSmoothCcTensor (I := I) (M := M) g₀ g₁ 4)).toSection x)) ≤
        ∑ l ∈ Finset.range (j + 1 - i'), C4 l * antidiagonalTupleGridPartialSum b (l + 1) :=
      Finset.sum_le_sum fun l _ => hC4 g₁ T htie hδ_le hδ0 hbound l x
    have hsum_nn : 0 ≤ ∑ l ∈ Finset.range (j + 1 - i'),
        riemannianFiberNormSq (I := I) (M := M) g₀ 6 (4 + l) x
          ((iteratedCovGrad (I := I) g₀ 6 4 l
            (cometricDoubleTraceSmoothCcTensor (I := I) (M := M) g₀ g₁ 4)).toSection x) :=
      Finset.sum_nonneg fun l _ =>
        riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 6 (4 + l) x _
    have hA1_rhs_nn : 0 ≤ C2 i' * antidiagonalTupleGridPartialSum b (i' + 1) :=
      mul_nonneg (hC2_nn i') (dLaGridWin_nonneg b hb (i' + 1))
    refine le_trans (mul_le_mul hA1 hA2 hsum_nn hA1_rhs_nn) ?_
    rw [Finset.mul_sum]
    rw [show (C2 i' * ∑ l ∈ Finset.range (j + 1 - i'),
        C4 l * antidiagonalTuplePairCount (i' + 1) (l + 1)) * W =
        ∑ l ∈ Finset.range (j + 1 - i'),
          (C2 i' * (C4 l * antidiagonalTuplePairCount (i' + 1) (l + 1))) * W from by
      rw [Finset.mul_sum, Finset.sum_mul]]
    refine Finset.sum_le_sum fun l hl => ?_
    rw [Finset.mem_range] at hl
    have hpair : antidiagonalTupleGridPartialSum b (i' + 1) * antidiagonalTupleGridPartialSum b
      (l + 1) ≤
        antidiagonalTuplePairCount (i' + 1) (l + 1) * antidiagonalTupleGridPartialSum b (j + 1) :=
      dLaGridWin_mul_le b hb (i' + 1) (l + 1) (j + 1) (by omega)
    calc C2 i' * antidiagonalTupleGridPartialSum b (i' + 1) *
           (C4 l * antidiagonalTupleGridPartialSum b (l + 1))
        = (C2 i' * C4 l) * (antidiagonalTupleGridPartialSum b (i' + 1) *
          antidiagonalTupleGridPartialSum b (l + 1)) := by ring
      _ ≤ (C2 i' * C4 l) * (antidiagonalTuplePairCount (i' + 1) (l + 1) *
        antidiagonalTupleGridPartialSum b (j + 1)) := by
          refine mul_le_mul_of_nonneg_left hpair ?_
          exact mul_nonneg (hC2_nn i') (hC4_nn l)
      _ = (C2 i' * (C4 l * antidiagonalTuplePairCount (i' + 1) (l + 1))) * W := by
          rw [hW_def]
          ring
  calc diagonalGridGrowthFactor (E := E) j *
        ∑ i' ∈ Finset.range (j + 1),
          riemannianFiberNormSq (I := I) (M := M) g₀ 4 (2 + i') x
              ((iteratedCovGrad (I := I) g₀ 4 2 i'
                (cometricDoubleTraceSmoothCcTensor (I := I) (M := M) g₀ g₁ 2)).toSection x) *
            ∑ l ∈ Finset.range (j + 1 - i'),
              riemannianFiberNormSq (I := I) (M := M) g₀ 6 (4 + l) x
                ((iteratedCovGrad (I := I) g₀ 6 4 l
                  (cometricDoubleTraceSmoothCcTensor (I := I) (M := M) g₀ g₁ 4)).toSection x)
      ≤ diagonalGridGrowthFactor (E := E) j *
          ∑ i' ∈ Finset.range (j + 1),
            (C2 i' * ∑ l ∈ Finset.range (j + 1 - i'),
              C4 l * antidiagonalTuplePairCount (i' + 1) (l + 1)) * W :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum hcell) (appCcGdiag_nonneg (E := E) j)
    _ = _ := by
        rw [← Finset.sum_mul, ← mul_assoc]

set_option backward.isDefEq.respectTransparency false in
theorem deTurckLieDLaCoeffField_eq_pairTrace
    (g₀ g_bg g₁ : SmoothRiemannianMetric I M) (T : SmoothCcTensor g₀ 0 2)
    (htie : ∀ (y : M) (v w : TangentSpace I y),
      g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ T y v w) :
    deTurckLieConnDiffDerivCoeffField (I := I) (M := M) g₀ g₁ g_bg =
      (-1 : ℝ) • ccOperatorFieldComp (I := I) (M := M) g₀ 2 6 2
        (pairTraceOpDla (I := I) (M := M) g₀ g₁)
        (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 sigmaE0dla
          (slotExtendIter (I := I) (M := M) g₀ 0 4 2
            (dLaSymCc (I := I) (M := M) g₀ T g₁ g_bg))) := by
  classical
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  apply ContinuousLinearMap.ext
  intro D
  apply Tensor0SSpace.toModel_injective
  apply ContinuousMultilinearMap.ext
  intro v
  have hsmul : ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
      (((-1 : ℝ) • ccOperatorFieldComp (I := I) (M := M) g₀ 2 6 2
        (pairTraceOpDla (I := I) (M := M) g₀ g₁)
        (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 sigmaE0dla
          (slotExtendIter (I := I) (M := M) g₀ 0 4 2
            (dLaSymCc (I := I) (M := M) g₀ T g₁ g_bg)))).toSection x)) D) =
      (-1 : ℝ) • ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
        ((ccOperatorFieldComp (I := I) (M := M) g₀ 2 6 2 (pairTraceOpDla (I := I) (M := M) g₀ g₁)
          (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 sigmaE0dla
            (slotExtendIter (I := I) (M := M) g₀ 0 4 2
              (dLaSymCc (I := I) (M := M) g₀ T g₁ g_bg)))).toSection x)) D) := by
    rw [show ((((-1 : ℝ) • ccOperatorFieldComp (I := I) (M := M) g₀ 2 6 2
        (pairTraceOpDla (I := I) (M := M) g₀ g₁)
        (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 sigmaE0dla
          (slotExtendIter (I := I) (M := M) g₀ 0 4 2
            (dLaSymCc (I := I) (M := M) g₀ T g₁ g_bg)))).toSection x)) =
        (-1 : ℝ) • ((ccOperatorFieldComp (I := I) (M := M) g₀ 2 6 2
          (pairTraceOpDla (I := I) (M := M) g₀ g₁)
          (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 sigmaE0dla
            (slotExtendIter (I := I) (M := M) g₀ 0 4 2
              (dLaSymCc (I := I) (M := M) g₀ T g₁ g_bg)))).toSection x) from by
      rw [SmoothCcTensor.toSection_smul]
      rfl]
    rfl
  rw [hsmul]
  beta_reduce
  rw [Tensor0SSpace.toModel_smul, ContinuousMultilinearMap.smul_apply, smul_eq_mul]
  rw [pairTraceOpDla_apply_toModel (I := I) (M := M) g₀ g₁
    (dLaSymCc (I := I) (M := M) g₀ T g₁ g_bg) x D v]
  rw [show ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
      (deTurckLieConnDiffDerivCoeffField (I := I) (M := M) g₀ g₁ g_bg).toSection x) D) =
      (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
        connDiffCovDerivBiContrFib (I := I) g₁ g_bg x) D from rfl]
  rw [show (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
      connDiffCovDerivBiContrFib (I := I) g₁ g_bg x) =
      connDiffCovDerivBiContrFibFixedFrame (I := I) g₁ g_bg (smoothOrthoFrame (I := I) g₁ x) x from
        rfl]
  rw [dLaBiContrFibFixedFrame_toModel (I := I) g₁ g_bg (smoothOrthoFrame (I := I) g₁ x) x D v]
  have hXval : ∀ a b : Fin (Module.finrank ℝ E),
      unitModel (I := I) (M := M) g₀ 4 (dLaSymCc (I := I) (M := M) g₀ T g₁ g_bg) x
        ![v 0, v 1, (smoothOrthoFrame (I := I) g₁ x a x : E),
          (smoothOrthoFrame (I := I) g₁ x b x : E)] =
      g₁.inner x (connDiffCovDerivOp (I := I) g₁ g_bg x (v 0)
          (smoothOrthoFrame (I := I) g₁ x a x) (smoothOrthoFrame (I := I) g₁ x b x)) (v 1) +
        g₁.inner x (connDiffCovDerivOp (I := I) g₁ g_bg x (v 1)
          (smoothOrthoFrame (I := I) g₁ x a x) (smoothOrthoFrame (I := I) g₁ x b x)) (v 0) := by
    intro a b
    rw [dLaSymCc_unitModel_apply (I := I) (M := M) g₀ T g₁ g_bg htie x
      (![v 0, v 1, (smoothOrthoFrame (I := I) g₁ x a x : E),
        (smoothOrthoFrame (I := I) g₁ x b x : E)] : Fin 4 → TangentSpace I x)]
    rw [show (![v 0, v 1, (smoothOrthoFrame (I := I) g₁ x a x : E),
        (smoothOrthoFrame (I := I) g₁ x b x : E)] : Fin 4 → TangentSpace I x) 0 = v 0 from rfl]
    rw [show (![v 0, v 1, (smoothOrthoFrame (I := I) g₁ x a x : E),
        (smoothOrthoFrame (I := I) g₁ x b x : E)] : Fin 4 → TangentSpace I x) 1 = v 1 from rfl]
    rw [show (![v 0, v 1, (smoothOrthoFrame (I := I) g₁ x a x : E),
        (smoothOrthoFrame (I := I) g₁ x b x : E)] : Fin 4 → TangentSpace I x) 2 =
      smoothOrthoFrame (I := I) g₁ x a x from rfl]
    rw [show (![v 0, v 1, (smoothOrthoFrame (I := I) g₁ x a x : E),
        (smoothOrthoFrame (I := I) g₁ x b x : E)] : Fin 4 → TangentSpace I x) 3 =
      smoothOrthoFrame (I := I) g₁ x b x from rfl]
  rw [show (∑ b : Fin (Module.finrank ℝ E), ∑ a : Fin (Module.finrank ℝ E),
      Tensor0SSpace.toModel D
          ![(smoothOrthoFrame (I := I) g₁ x a x : E),
            (smoothOrthoFrame (I := I) g₁ x b x : E)] *
        unitModel (I := I) (M := M) g₀ 4 (dLaSymCc (I := I) (M := M) g₀ T g₁ g_bg) x
          ![v 0, v 1, (smoothOrthoFrame (I := I) g₁ x a x : E),
            (smoothOrthoFrame (I := I) g₁ x b x : E)]) =
      ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
        Tensor0SSpace.toModel D
            ![(smoothOrthoFrame (I := I) g₁ x a x : E),
              (smoothOrthoFrame (I := I) g₁ x b x : E)] *
          unitModel (I := I) (M := M) g₀ 4 (dLaSymCc (I := I) (M := M) g₀ T g₁ g_bg) x
            ![v 0, v 1, (smoothOrthoFrame (I := I) g₁ x a x : E),
              (smoothOrthoFrame (I := I) g₁ x b x : E)] from Finset.sum_comm]
  rw [neg_one_mul, neg_one_mul]
  congr 1
  refine Finset.sum_congr rfl fun a _ => ?_
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [hXval a b]
  ring


end DLaGridBrick

end DifferentialGeometry.Analysis.Sobolev

end
