import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.TimeTameFixedPoint
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.GreenIdentityAndIBP.TensorCovGradL2InnerDirichletBridge
import DifferentialGeometry.Analysis.Integration.Measure.CompactVolumeEquiv
import DifferentialGeometry.Analysis.Integration.Measure.FamilyContinuity
import DifferentialGeometry.Analysis.Integration.Measure.VolumeVariation
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.SlotInsertSelfAdjointPairing
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.CometricInverseDifferenceMultiplier
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.MetricArmCoeffJetTowerRaisedEndoCovariantDerivativeBound
import DifferentialGeometry.Analysis.Spectral.Tensor.Spectrum.CompactInclusion
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.MetricDiffSmallC0
import DifferentialGeometry.Analysis.Spectral.Tensor.Variational.CovDerivPointwise
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.InverseMetricRaisedEndomorphismJetBound
import DifferentialGeometry.Geometry.Connection.Laplacian.Musical
import DifferentialGeometry.Geometry.Exponential.LocalAddition
open DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Analysis.Elliptic
open DifferentialGeometry.PDE.RicciFlow DifferentialGeometry.Analysis.Parabolic
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Operator

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8

open Bundle Manifold MeasureTheory Set DifferentialGeometry.Tensor0SBundle
open scoped ENNReal Manifold Topology ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Pullback

open DifferentialGeometry
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Sobolev.TensorHilbert
open DifferentialGeometry.Geometry.Riemannian.Exponential

open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian
open DifferentialGeometry.Analysis.Parabolic DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Analysis.Spectral.MetricRealization

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [CompactSpace M] [T2Space M]
  [SigmaCompactSpace M] [BoundarylessManifold I M]

private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

noncomputable def connAddZeroCoord (p : M) : E × E :=
  extChartAt I.tangent
    (⟨connCompPt (I := I) p, (0 : E)⟩ :
      TangentBundle I (connCompOpen (I := I) p))
    (⟨connCompPt (I := I) p, (0 : E)⟩ :
      TangentBundle I (connCompOpen (I := I) p))

noncomputable def connAddTarget
    (g : SmoothRiemannianMetric I M) (p : M) : E × E → E :=
  fun z => (connAddChart (I := I) g p z).2

omit [SigmaCompactSpace M] [BoundarylessManifold I M] in
theorem connAddTarget_fd
    (g : SmoothRiemannianMetric I M) (p : M) (n : ℕ) (hn : 1 ≤ n) :
    HasFDerivAt (connAddTarget (I := I) g p)
      ((ContinuousLinearMap.snd ℝ E E).comp
        (unipotentCLE (E := E) : (E × E) →L[ℝ] (E × E)))
      (connAddZeroCoord (I := I) p) := by
  simpa only [connAddTarget, connAddZeroCoord] using
    (connAdd_fderiv (I := I) g p n hn).snd

omit [SigmaCompactSpace M] [BoundarylessManifold I M] in
theorem connAdd_vert
    (g : SmoothRiemannianMetric I M) (p : M) (n : ℕ) (hn : 1 ≤ n) (v : E) :
    fderiv ℝ (connAddTarget (I := I) g p)
        (connAddZeroCoord (I := I) p) (0, v) = v := by
  rw [(connAddTarget_fd (I := I) g p n hn).fderiv]
  simp [unipotentCLE, DifferentialGeometry.PhaseFlow.freeDiagCLE_apply]

abbrev hmfState (g₀ : SmoothRiemannianMetric I M) (a : ℕ) (R : ℝ) :
    Set (DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.tensorHs
      (I := I) (M := M) g₀ 0 1 ((a : ℝ) + 2)) :=
  lowerStateRS (I := I) (M := M) g₀ 0 1 a R

noncomputable def hmfUnknown
    (g₀ : SmoothRiemannianMetric I M) (S : SmoothCcTensor g₀ 0 1) :
    ∀ x : M, TangentSpace I x := fun x =>
  inverseMetricSharpFib (I := I) g₀ x
    (unitEvalSection (I := I) (M := M) g₀ 1 S x)

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [CompactSpace M]
  [T2Space M] [SigmaCompactSpace M] [BoundarylessManifold I M] in
theorem hmfUnknown_add
    (g₀ : SmoothRiemannianMetric I M) (S T : SmoothCcTensor g₀ 0 1)
    (x : M) :
  hmfUnknown (I := I) g₀ (S + T) x =
      hmfUnknown (I := I) g₀ S x + hmfUnknown (I := I) g₀ T x := by
  simp only [hmfUnknown, unitEvalSection_apply, SmoothCcTensor.toSection_add,
    ContMDiffSection.coe_add, Pi.add_apply]
  change inverseMetricSharpFib (I := I) g₀ x
      ((S.toSection x) (unitZeroSec (I := I) (M := M) x) +
        (T.toSection x) (unitZeroSec (I := I) (M := M) x)) =
    _
  rw [map_add]

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [CompactSpace M]
  [T2Space M] [SigmaCompactSpace M] [BoundarylessManifold I M] in
theorem hmfUnknown_smul
    (g₀ : SmoothRiemannianMetric I M) (c : ℝ) (S : SmoothCcTensor g₀ 0 1)
    (x : M) :
  hmfUnknown (I := I) g₀ (c • S) x =
      c • hmfUnknown (I := I) g₀ S x := by
  simp only [hmfUnknown, unitEvalSection_apply, SmoothCcTensor.toSection_smul,
    ContMDiffSection.coe_smul, Pi.smul_apply]
  change inverseMetricSharpFib (I := I) g₀ x
      (c • (S.toSection x) (unitZeroSec (I := I) (M := M) x)) = _
  rw [map_smul]

noncomputable def hmfUnknownLM
    (g₀ : SmoothRiemannianMetric I M) (x : M) :
    SmoothCcTensor g₀ 0 1 →ₗ[ℝ] TangentSpace I x where
  toFun S := hmfUnknown (I := I) g₀ S x
  map_add' S T := hmfUnknown_add (I := I) g₀ S T x
  map_smul' c S := hmfUnknown_smul (I := I) g₀ c S x

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [CompactSpace M]
  [T2Space M] [SigmaCompactSpace M] [BoundarylessManifold I M] in
@[simp] theorem hmfUnknownLM_apply
    (g₀ : SmoothRiemannianMetric I M) (x : M) (S : SmoothCcTensor g₀ 0 1) :
    hmfUnknownLM (I := I) g₀ x S = hmfUnknown (I := I) g₀ S x := rfl

noncomputable def hmfUnknownSec
    (g₀ : SmoothRiemannianMetric I M) (S : SmoothCcTensor g₀ 0 1) :
    Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ where
  toFun := hmfUnknown (I := I) g₀ S
  contMDiff_toFun := by
    exact ContMDiff.clm_bundle_apply (𝕜 := ℝ) (n := (∞ : WithTop ℕ∞))
      (F₁ := Tensor0SModel 1 ℝ E) (F₂ := E)
      (E₁ := fun x : M => Tensor0SSpace 1 I x)
      (E₂ := fun x : M => TangentSpace I x)
      (IM := I) (IB := I) (b := fun x : M => x)
      (inverseMetricSharpField_contMDiff (I := I) g₀)
      (contMDiff_unitEvalSection (I := I) (M := M) g₀ 1 S)

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M]
  [SigmaCompactSpace M] [BoundarylessManifold I M] in
@[simp] theorem hmfUnknownSec_apply
    (g₀ : SmoothRiemannianMetric I M) (S : SmoothCcTensor g₀ 0 1) (x : M) :
    hmfUnknownSec (I := I) g₀ S x = hmfUnknown (I := I) g₀ S x := rfl

noncomputable def hmfPrincipal
    (g₀ : SmoothRiemannianMetric I M) (S : SmoothCcTensor g₀ 0 1) :
    ∀ x : M, TangentSpace I x := fun x =>
  inverseMetricSharpFib (I := I) g₀ x
    ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 1 I x from
      connLaplacianMixed (I := I) (M := M) g₀ 0 1 S.toSection x)
      (unitZeroSec (I := I) (M := M) x))

omit [CompactSpace M] [SigmaCompactSpace M] in
theorem hmfPrincipal_eq
    (g₀ : SmoothRiemannianMetric I M) (S : SmoothCcTensor g₀ 0 1) (x : M) :
    hmfPrincipal (I := I) g₀ S x =
      connLaplacian_vector (I := I) g₀ (hmfUnknown (I := I) g₀ S) x := by
  simpa only [hmfPrincipal, hmfUnknown] using
    (sharp_connLap (I := I) (M := M) g₀ S x).symm

noncomputable def hmfDiff
    (q h : SmoothRiemannianMetric I M) (S : SmoothCcTensor q 0 1) :
    SmoothCcTensor q 0 2 :=
  operatorFieldApply (I := I) (M := M) q 2 2
    (endoSlotZeroCcTensor (I := I) (M := M) q 1
      (gInvDiffRaisedEndoField (I := I) q h))
    (covGrad (I := I) (M := M) q 0 1 S)

noncomputable def hmfFlux
    (q h : SmoothRiemannianMetric I M) (S : SmoothCcTensor q 0 1) :
    SmoothCcTensor q 0 2 :=
  covGrad (I := I) (M := M) q 0 1 S + hmfDiff (I := I) (M := M) q h S

set_option backward.isDefEq.respectTransparency false in
omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
theorem hmfFlux_apply
    (q h : SmoothRiemannianMetric I M) (S : SmoothCcTensor q 0 1)
    (x : M) (m : Fin 2 → E) :
    Tensor0SSpace.toModel
        (unitEvalSection (I := I) (M := M) q 2
          (hmfFlux (I := I) (M := M) q h S) x) m =
      Tensor0SSpace.toModel
        (unitEvalSection (I := I) (M := M) q 2
          (covGrad (I := I) (M := M) q 0 1 S) x)
        (Function.update m 0
          (metricComparisonEndo (I := I) q h x (m 0))) := by
  let D : Tensor0SSpace 2 I x :=
    unitEvalSection (I := I) (M := M) q 2
      (covGrad (I := I) (M := M) q 0 1 S) x
  have hflux :
      unitEvalSection (I := I) (M := M) q 2
          (hmfFlux (I := I) (M := M) q h S) x =
        D + slotInsertEndoFib (I := I) (M := M) 2 0 x
          (metricComparisonDiffEndo (I := I) q h x) D := by
    rw [hmfFlux, hmfDiff, unitEvalSection_apply, SmoothCcTensor.toSection_add,
      ContMDiffSection.coe_add, Pi.add_apply, ContinuousLinearMap.add_apply]
    rw [appCc_toSection, ContinuousLinearMap.comp_apply,
      slotInsertEndoCc_toSection]
    rfl
  rw [hflux, Tensor0SSpace.toModel_add,
    ContinuousMultilinearMap.add_apply, slotInsertEndoFib_apply_eval]
  change Tensor0SSpace.toModel D m +
      Tensor0SSpace.toModel D
        (Function.update m 0
          (metricComparisonDiffEndo (I := I) q h x (m 0))) =
    Tensor0SSpace.toModel D
      (Function.update m 0 (metricComparisonEndo (I := I) q h x (m 0)))
  rw [gInvRaisedEndo_eq_diff_add_id,
    ContinuousMultilinearMap.map_update_add, Function.update_eq_self]
  abel

set_option backward.isDefEq.respectTransparency false in
omit [NeZero (Module.finrank ℝ E)] [CompactSpace M]
  [SigmaCompactSpace M] [BoundarylessManifold I M] in
private theorem hmfRaised_split
    (q h : SmoothRiemannianMetric I M) :
    fullRaisedEndoField (I := I) (M := M) q h =
      gInvDiffRaisedEndoField (I := I) q h +
        fullRaisedEndoField (I := I) (M := M) q q := by
  apply ContMDiffSection.ext
  intro x
  rw [show ((gInvDiffRaisedEndoField (I := I) q h +
      fullRaisedEndoField (I := I) (M := M) q q) x) =
      gInvDiffRaisedEndoField (I := I) q h x +
        fullRaisedEndoField (I := I) (M := M) q q x from by
          rw [ContMDiffSection.coe_add]
          rfl]
  apply ContinuousLinearMap.ext
  intro v
  rw [fullRaisedEndoField_apply, ContinuousLinearMap.add_apply]
  rw [show gInvDiffRaisedEndoField (I := I) q h x =
      metricComparisonDiffEndo (I := I) q h x from rfl]
  rw [fullRaisedEndoField_apply,
    gInvRaisedEndo_eq_diff_add_id (I := I) q h x v]
  rw [show metricComparisonEndo (I := I) q q x v = v from by
    rw [gInvRaisedEndo_apply, inverseMetricSharpFib_g0FlatCLM]]

set_option backward.isDefEq.respectTransparency false in
omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
  [SigmaCompactSpace M] [BoundarylessManifold I M] in
private theorem hmfSlot_add
    (q : SmoothRiemannianMetric I M) (s : ℕ)
    (A B : ContMDiffSection I (E →L[ℝ] E) ∞
      (fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x)) :
    endoSlotZeroCcTensor (I := I) (M := M) q s (A + B) =
      endoSlotZeroCcTensor (I := I) (M := M) q s A +
        endoSlotZeroCcTensor (I := I) (M := M) q s B := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  apply ContinuousLinearMap.ext
  intro D
  rw [show ((endoSlotZeroCcTensor (I := I) (M := M) q s A +
      endoSlotZeroCcTensor (I := I) (M := M) q s B).toSection x) =
      (endoSlotZeroCcTensor (I := I) (M := M) q s A).toSection x +
        (endoSlotZeroCcTensor (I := I) (M := M) q s B).toSection x from by
          rw [SmoothCcTensor.toSection_add]
          rfl]
  rw [ContinuousLinearMap.add_apply]
  simp only [slotInsertEndoCc_toSection]
  rw [show ((A + B) x) = A x + B x from by
    rw [ContMDiffSection.coe_add]
    rfl]
  rw [slotInsertEndoFib_add_left, ContinuousLinearMap.add_apply]

set_option backward.isDefEq.respectTransparency false in
omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M]
  [BoundarylessManifold I M] in
private theorem hmfSlot_self_app
    (q : SmoothRiemannianMetric I M) (W : SmoothCcTensor q 0 2) :
    operatorFieldApply (I := I) (M := M) q 2 2
        (endoSlotZeroCcTensor (I := I) (M := M) q 1
          (fullRaisedEndoField (I := I) (M := M) q q)) W =
      W := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  apply ContinuousLinearMap.ext
  intro d
  apply Tensor0SSpace.toModel_injective
  apply ContinuousMultilinearMap.ext
  intro m
  rw [appCc_toSection, ContinuousLinearMap.comp_apply,
    slotInsertEndoCc_toSection, slotInsertEndoFib_apply_eval,
    fullRaisedEndoField_apply]
  rw [show metricComparisonEndo (I := I) q q x (m 0) = m 0 from by
    rw [gInvRaisedEndo_apply, inverseMetricSharpFib_g0FlatCLM]]
  rw [Function.update_eq_self]

omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
theorem hmfFlux_eq_full
    (q h : SmoothRiemannianMetric I M) (S : SmoothCcTensor q 0 1) :
    hmfFlux (I := I) (M := M) q h S =
      operatorFieldApply (I := I) (M := M) q 2 2
        (endoSlotZeroCcTensor (I := I) (M := M) q 1
          (fullRaisedEndoField (I := I) (M := M) q h))
        (covGrad (I := I) (M := M) q 0 1 S) := by
  rw [hmfFlux, hmfDiff, hmfRaised_split (I := I) (M := M) q h,
    hmfSlot_add (I := I) (M := M) q 1, appCc_add_left,
    hmfSlot_self_app]
  abel

omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
theorem hmfFlux_self
    (q : SmoothRiemannianMetric I M) (S : SmoothCcTensor q 0 1) :
    hmfFlux (I := I) (M := M) q q S =
      covGrad (I := I) (M := M) q 0 1 S := by
  rw [hmfFlux_eq_full, hmfSlot_self_app]

omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
theorem hmfDiff_add
    (q h : SmoothRiemannianMetric I M) (S T : SmoothCcTensor q 0 1) :
    hmfDiff (I := I) (M := M) q h (S + T) =
      hmfDiff (I := I) (M := M) q h S +
        hmfDiff (I := I) (M := M) q h T := by
  unfold hmfDiff
  rw [covGrad_add, appCc_add_right]

omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
theorem hmfDiff_smul
    (q h : SmoothRiemannianMetric I M) (c : ℝ) (S : SmoothCcTensor q 0 1) :
    hmfDiff (I := I) (M := M) q h (c • S) =
      c • hmfDiff (I := I) (M := M) q h S := by
  unfold hmfDiff
  rw [covGrad_smul, appCc_smul_right]

omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
theorem hmfFlux_add
    (q h : SmoothRiemannianMetric I M) (S T : SmoothCcTensor q 0 1) :
    hmfFlux (I := I) (M := M) q h (S + T) =
      hmfFlux (I := I) (M := M) q h S +
        hmfFlux (I := I) (M := M) q h T := by
  unfold hmfFlux
  rw [covGrad_add, hmfDiff_add]
  abel

omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
theorem hmfFlux_smul
    (q h : SmoothRiemannianMetric I M) (c : ℝ) (S : SmoothCcTensor q 0 1) :
    hmfFlux (I := I) (M := M) q h (c • S) =
      c • hmfFlux (I := I) (M := M) q h S := by
  unfold hmfFlux
  rw [covGrad_smul, hmfDiff_smul, smul_add]

noncomputable def hmfMass
    (q h : SmoothRiemannianMetric I M) (S T : SmoothCcTensor q 0 1) : ℝ :=
  ∫ x, tensorInnerPointwise (I := I) (M := M) q 0 1 x (S.toFun x) (T.toFun x)
    ∂(riemannianVolumeMeasure (I := I) (M := M) h)

noncomputable def hmfWeakForm
    (q h : SmoothRiemannianMetric I M) (S T : SmoothCcTensor q 0 1) : ℝ :=
  ∫ x, tensorInnerPointwise (I := I) (M := M) q 0 2 x
      ((hmfFlux (I := I) (M := M) q h S).toFun x)
      ((covGrad (I := I) (M := M) q 0 1 T).toFun x)
    ∂(riemannianVolumeMeasure (I := I) (M := M) h)

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
  [BoundarylessManifold I M] in
theorem hmfMass_time_cont
    (q : SmoothRiemannianMetric I M)
    (g : ℝ → SmoothRiemannianMetric I M) {K : Set ℝ} (hK : IsCompact K)
    (hcont : ∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)), ContinuousOn
      (fun p : ℝ × M => chartGramMatrix (I := I) (g p.1) x₀ p.2 i j)
      (K ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet))
    (S T : SmoothCcTensor q 0 1) :
    ContinuousOn (fun t => hmfMass (I := I) (M := M) q (g t) S T) K := by
  unfold hmfMass
  apply integral_family_cont (I := I) (M := M) hK hcont
  exact
    (SmoothCcTensor.continuous_inner_cross (I := I) (M := M) S T).continuousOn.comp
      continuousOn_snd (fun _ _ => Set.mem_univ _)

omit [CompactSpace M] [T2Space M] [SigmaCompactSpace M] in
private theorem functionRegularAt_const_time
    (f : M → ℝ) (hf : Continuous f) (t₀ : ℝ) :
    FunctionRegularAt (fun _ : ℝ => f) t₀ := by
  refine
    { hasDerivAt_time := ?_
      continuous_joint := hf.comp continuous_snd
      continuous_deriv_joint := ?_ }
  · intro x t
    have hd : deriv (fun _ : ℝ => f x) t = 0 :=
      (hasDerivAt_const (x := t) (c := f x)).deriv
    simpa only [hd] using (hasDerivAt_const (x := t) (c := f x))
  · have heq :
        (fun p : ℝ × M => deriv (fun _ : ℝ => f p.2) p.1) =
          fun _ : ℝ × M => (0 : ℝ) := by
      funext p
      exact (hasDerivAt_const (x := p.1) (c := f p.2)).deriv
    rw [heq]
    exact continuous_const

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
  [BoundarylessManifold I M] in
theorem hmfMass_hasDerivAt
    (q : SmoothRiemannianMetric I M)
    (g : ℝ → SmoothRiemannianMetric I M) (t₀ : ℝ)
    (hg : MetricFamilyRegularAt (I := I) g t₀)
    (S T : SmoothCcTensor q 0 1) :
    HasDerivAt
      (fun t => hmfMass (I := I) (M := M) q (g t) S T)
      (∫ x, (1 / 2 : ℝ) * traceTimeDerivMetric (I := I) g t₀ x *
          tensorInnerPointwise (I := I) (M := M) q 0 1 x
            (S.toFun x) (T.toFun x)
        ∂(riemannianVolumeMeasure (I := I) (M := M) (g t₀))) t₀ := by
  let f : M → ℝ := fun x =>
    tensorInnerPointwise (I := I) (M := M) q 0 1 x (S.toFun x) (T.toFun x)
  have hf : Continuous f :=
    SmoothCcTensor.continuous_inner_cross (I := I) (M := M) S T
  have hreg : FunctionRegularAt (fun _ : ℝ => f) t₀ :=
    functionRegularAt_const_time f hf t₀
  have hvar := volume_variation_formula_clean (I := I) (M := M) hg hreg
  have hderiv : ∀ x : M, deriv (fun _ : ℝ => f x) t₀ = 0 := fun x =>
    (hasDerivAt_const (x := t₀) (c := f x)).deriv
  simpa only [hmfMass, f, riemannianMeasureFamily_def, hderiv, zero_add] using hvar

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [CompactSpace M]
  [BoundarylessManifold I M] in
private lemma hmf_inner_int
    (q h : SmoothRiemannianMetric I M) {r s : ℕ}
    (S T : SmoothCcTensor q r s) :
    MeasureTheory.Integrable
      (fun x => tensorInnerPointwise (I := I) (M := M) q r s x
        (S.toFun x) (T.toFun x))
      (riemannianVolumeMeasure (I := I) (M := M) h) := by
  letI : IsFiniteMeasureOnCompacts
      (riemannianVolumeMeasure (I := I) (M := M) h) :=
    riemannianVolumeMeasure_isFiniteMeasureOnCompacts (I := I) (M := M) h
  exact (SmoothCcTensor.continuous_inner_cross (I := I)
    (M := M) S T).integrable_of_hasCompactSupport
    (SmoothCcTensor.hasCompactSupport_inner_cross (I := I) (M := M) S T)

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [CompactSpace M]
  [BoundarylessManifold I M] in
theorem hmfMass_add_left
    (q h : SmoothRiemannianMetric I M) (S₁ S₂ T : SmoothCcTensor q 0 1) :
    hmfMass (I := I) (M := M) q h (S₁ + S₂) T =
      hmfMass (I := I) (M := M) q h S₁ T +
        hmfMass (I := I) (M := M) q h S₂ T := by
  unfold hmfMass
  rw [SmoothCcTensor.toFun_add]
  simp only [Pi.add_apply, tensorInnerPointwise_add_left]
  exact MeasureTheory.integral_add
    (hmf_inner_int (I := I) (M := M) q h S₁ T)
    (hmf_inner_int (I := I) (M := M) q h S₂ T)

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [CompactSpace M]
  [BoundarylessManifold I M] in
theorem hmfMass_smul_left
    (q h : SmoothRiemannianMetric I M) (c : ℝ) (S T : SmoothCcTensor q 0 1) :
    hmfMass (I := I) (M := M) q h (c • S) T =
      c * hmfMass (I := I) (M := M) q h S T := by
  unfold hmfMass
  rw [SmoothCcTensor.toFun_smul]
  simp only [Pi.smul_apply, tensorInnerPointwise_smul_left,
    MeasureTheory.integral_const_mul]

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [CompactSpace M]
  [BoundarylessManifold I M] in
theorem hmfMass_symm
    (q h : SmoothRiemannianMetric I M) (S T : SmoothCcTensor q 0 1) :
    hmfMass (I := I) (M := M) q h S T =
      hmfMass (I := I) (M := M) q h T S := by
  unfold hmfMass
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall ?_)
  intro x
  exact tensorInnerPointwise_symm (I := I) (M := M) q 0 1 x
    (S.toFun x) (T.toFun x)

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [CompactSpace M]
  [BoundarylessManifold I M] in
theorem hmfMass_add_right
    (q h : SmoothRiemannianMetric I M) (S T₁ T₂ : SmoothCcTensor q 0 1) :
    hmfMass (I := I) (M := M) q h S (T₁ + T₂) =
      hmfMass (I := I) (M := M) q h S T₁ +
        hmfMass (I := I) (M := M) q h S T₂ := by
  rw [hmfMass_symm, hmfMass_add_left, hmfMass_symm q h T₁ S,
    hmfMass_symm q h T₂ S]

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [CompactSpace M]
  [BoundarylessManifold I M] in
theorem hmfMass_smul_right
    (q h : SmoothRiemannianMetric I M) (c : ℝ) (S T : SmoothCcTensor q 0 1) :
    hmfMass (I := I) (M := M) q h S (c • T) =
      c * hmfMass (I := I) (M := M) q h S T := by
  rw [hmfMass_symm, hmfMass_smul_left, hmfMass_symm q h T S]

omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
theorem hmfWeak_add_left
    (q h : SmoothRiemannianMetric I M) (S₁ S₂ T : SmoothCcTensor q 0 1) :
    hmfWeakForm (I := I) (M := M) q h (S₁ + S₂) T =
      hmfWeakForm (I := I) (M := M) q h S₁ T +
        hmfWeakForm (I := I) (M := M) q h S₂ T := by
  unfold hmfWeakForm
  rw [hmfFlux_add, SmoothCcTensor.toFun_add]
  simp only [Pi.add_apply, tensorInnerPointwise_add_left]
  exact MeasureTheory.integral_add
    (hmf_inner_int (I := I) (M := M) q h
      (hmfFlux (I := I) (M := M) q h S₁)
      (covGrad (I := I) (M := M) q 0 1 T))
    (hmf_inner_int (I := I) (M := M) q h
      (hmfFlux (I := I) (M := M) q h S₂)
      (covGrad (I := I) (M := M) q 0 1 T))

omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
theorem hmfWeak_smul_left
    (q h : SmoothRiemannianMetric I M) (c : ℝ) (S T : SmoothCcTensor q 0 1) :
    hmfWeakForm (I := I) (M := M) q h (c • S) T =
      c * hmfWeakForm (I := I) (M := M) q h S T := by
  unfold hmfWeakForm
  rw [hmfFlux_smul, SmoothCcTensor.toFun_smul]
  simp only [Pi.smul_apply, tensorInnerPointwise_smul_left,
    MeasureTheory.integral_const_mul]

omit [BoundarylessManifold I M] in
private theorem hmfDiff_pair_symm
    (q h : SmoothRiemannianMetric I M) (S T : SmoothCcTensor q 0 1) (x : M) :
    tensorInnerPointwise (I := I) (M := M) q 0 2 x
        ((hmfDiff (I := I) (M := M) q h S).toFun x)
        ((covGrad (I := I) (M := M) q 0 1 T).toFun x) =
      tensorInnerPointwise (I := I) (M := M) q 0 2 x
        ((hmfDiff (I := I) (M := M) q h T).toFun x)
        ((covGrad (I := I) (M := M) q 0 1 S).toFun x) := by
  obtain ⟨e, bse, hbse, horth⟩ :=
    exists_orthoFrame_basis_E (I := I) (M := M) q x
  have hslot := tensorInnerPointwise_slotΛ_self_adjoint
    (I := I) (M := M) q 1 x
    (metricComparisonDiffEndo (I := I) q h x)
    (gInvDiffRaisedEndo_g0_self_adjoint (I := I) q h x)
    ((covGrad (I := I) (M := M) q 0 1 S).toSection x)
    ((covGrad (I := I) (M := M) q 0 1 T).toSection x)
    e bse hbse horth
  calc
    tensorInnerPointwise (I := I) (M := M) q 0 2 x
        ((hmfDiff (I := I) (M := M) q h S).toFun x)
        ((covGrad (I := I) (M := M) q 0 1 T).toFun x) =
      tensorInnerPointwise (I := I) (M := M) q 0 2 x
        ((covGrad (I := I) (M := M) q 0 1 S).toFun x)
        ((hmfDiff (I := I) (M := M) q h T).toFun x) := by
          simpa only [hmfDiff, appCc_toSection, ContinuousLinearMap.comp_apply] using hslot
    _ = _ := tensorInnerPointwise_symm (I := I) (M := M) q 0 2 x _ _

omit [BoundarylessManifold I M] in
theorem hmfWeak_symm
    (q h : SmoothRiemannianMetric I M) (S T : SmoothCcTensor q 0 1) :
    hmfWeakForm (I := I) (M := M) q h S T =
      hmfWeakForm (I := I) (M := M) q h T S := by
  unfold hmfWeakForm
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall ?_)
  intro x
  simp only [hmfFlux, SmoothCcTensor.toFun_add, Pi.add_apply,
    tensorInnerPointwise_add_left]
  rw [
    tensorInnerPointwise_symm (I := I) (M := M) q 0 2 x
      ((covGrad (I := I) (M := M) q 0 1 S).toFun x)
      ((covGrad (I := I) (M := M) q 0 1 T).toFun x),
    hmfDiff_pair_symm]

omit [BoundarylessManifold I M] in
theorem hmfWeak_add_right
    (q h : SmoothRiemannianMetric I M) (S T₁ T₂ : SmoothCcTensor q 0 1) :
    hmfWeakForm (I := I) (M := M) q h S (T₁ + T₂) =
      hmfWeakForm (I := I) (M := M) q h S T₁ +
        hmfWeakForm (I := I) (M := M) q h S T₂ := by
  rw [hmfWeak_symm, hmfWeak_add_left, hmfWeak_symm q h T₁ S,
    hmfWeak_symm q h T₂ S]

omit [BoundarylessManifold I M] in
theorem hmfWeak_smul_right
    (q h : SmoothRiemannianMetric I M) (c : ℝ) (S T : SmoothCcTensor q 0 1) :
    hmfWeakForm (I := I) (M := M) q h S (c • T) =
      c * hmfWeakForm (I := I) (M := M) q h S T := by
  rw [hmfWeak_symm, hmfWeak_smul_left, hmfWeak_symm q h T S]

omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
theorem hmfWeakForm_eq
    (q h : SmoothRiemannianMetric I M) (S T : SmoothCcTensor q 0 1) :
    hmfWeakForm (I := I) (M := M) q h S T =
      ∫ x, tensorInnerPointwise (I := I) (M := M) q 0 2 x
          ((covGrad (I := I) (M := M) q 0 1 S +
            operatorFieldApply (I := I) (M := M) q 2 2
              (endoSlotZeroCcTensor (I := I) (M := M) q 1
                (gInvDiffRaisedEndoField (I := I) q h))
              (covGrad (I := I) (M := M) q 0 1 S)).toFun x)
          ((covGrad (I := I) (M := M) q 0 1 T).toFun x)
        ∂(riemannianVolumeMeasure (I := I) (M := M) h) := rfl

omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
theorem hmfWeakForm_full
    (q h : SmoothRiemannianMetric I M) (S T : SmoothCcTensor q 0 1) :
    hmfWeakForm (I := I) (M := M) q h S T =
      ∫ x, tensorInnerPointwise (I := I) (M := M) q 0 2 x
          ((operatorFieldApply (I := I) (M := M) q 2 2
            (endoSlotZeroCcTensor (I := I) (M := M) q 1
              (fullRaisedEndoField (I := I) (M := M) q h))
            (covGrad (I := I) (M := M) q 0 1 S)).toFun x)
          ((covGrad (I := I) (M := M) q 0 1 T).toFun x)
        ∂(riemannianVolumeMeasure (I := I) (M := M) h) := by
  rw [hmfWeakForm, hmfFlux_eq_full]

omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
theorem hmfWeakForm_self
    (q : SmoothRiemannianMetric I M) (S T : SmoothCcTensor q 0 1) :
    hmfWeakForm (I := I) (M := M) q q S T =
      tensorL2Inner (I := I) (M := M) q 0 2
        (covGrad (I := I) (M := M) q 0 1 S).toFun
        (covGrad (I := I) (M := M) q 0 1 T).toFun := by
  rw [hmfWeakForm, hmfFlux_self]
  rfl

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [CompactSpace M]
  [BoundarylessManifold I M] in
theorem hmfMass_self
    (q : SmoothRiemannianMetric I M) (S T : SmoothCcTensor q 0 1) :
    hmfMass (I := I) (M := M) q q S T =
      tensorL2Inner (I := I) (M := M) q 0 1 S.toFun T.toFun := rfl

omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
theorem hmfH1_self
    (q : SmoothRiemannianMetric I M) (S T : SmoothCcTensor q 0 1) :
    hmfMass (I := I) (M := M) q q S T +
        hmfWeakForm (I := I) (M := M) q q S T =
      tensorH1Inner (I := I) (M := M) q 0 1 S T := by
  rw [hmfMass_self, hmfWeakForm_self, tensorH1Inner_def,
    tensorL2Inner_covGrad_eq_integral_tensorCovDerivPointwiseInner]

omit [CompactSpace M] [T2Space M] [SigmaCompactSpace M] in
private lemma hmf_integral_le
    {μ ν : MeasureTheory.Measure M} {C : ℝ≥0∞}
    (hC0 : C ≠ 0) (hCtop : C ≠ ⊤) (hμν : μ ≤ C • ν)
    {f : M → ℝ} (hf0 : ∀ x, 0 ≤ f x)
    (hfint : MeasureTheory.Integrable f ν) :
    ∫ x, f x ∂μ ≤ C.toReal * ∫ x, f x ∂ν := by
  have hfC : MeasureTheory.Integrable f (C • ν) :=
    (MeasureTheory.integrable_smul_measure hC0 hCtop).2 hfint
  calc
    ∫ x, f x ∂μ ≤ ∫ x, f x ∂(C • ν) :=
      MeasureTheory.integral_mono_measure hμν
        (Filter.Eventually.of_forall hf0) hfC
    _ = C.toReal * ∫ x, f x ∂ν := by
      rw [MeasureTheory.integral_smul_measure, smul_eq_mul]

omit [BoundarylessManifold I M] in
private theorem hmfDiff_self_le
    (q h : SmoothRiemannianMetric I M)
    (k : ∀ y : M, TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ)
    (htie : ∀ (y : M) (v w : TangentSpace I y),
      h.inner y v w = q.inner y v w + k y v w)
    {δ : ℝ} (hδ_lt : δ < 1) (hδ_nn : 0 ≤ δ)
    (hδ : metricCauchySchwarzBound (I := I) (M := M) q k δ)
    (S : SmoothCcTensor q 0 1) (x : M) :
    tensorInnerPointwise (I := I) (M := M) q 0 2 x
        ((hmfDiff (I := I) (M := M) q h S).toFun x)
        ((covGrad (I := I) (M := M) q 0 1 S).toFun x) ≤
      (δ / (1 - δ)) *
        tensorInnerPointwise (I := I) (M := M) q 0 2 x
          ((covGrad (I := I) (M := M) q 0 1 S).toFun x)
          ((covGrad (I := I) (M := M) q 0 1 S).toFun x) := by
  rw [tensorInnerPointwise_symm (I := I) (M := M) q 0 2 x
    ((hmfDiff (I := I) (M := M) q h S).toFun x)
    ((covGrad (I := I) (M := M) q 0 1 S).toFun x)]
  simpa only [hmfDiff, appCc_toSection, ContinuousLinearMap.comp_apply] using
    (tensorInnerPointwise_gInvDiffSlot_le (I := I) (M := M)
      q h k htie hδ_lt hδ_nn hδ 1 x
      ((covGrad (I := I) (M := M) q 0 1 S).toSection x))

omit [BoundarylessManifold I M] in
private theorem hmfNegDiff_self_le
    (q h : SmoothRiemannianMetric I M)
    (k : ∀ y : M, TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ)
    (htie : ∀ (y : M) (v w : TangentSpace I y),
      h.inner y v w = q.inner y v w + k y v w)
    {δ : ℝ} (hδ_lt : δ < 1) (hδ_nn : 0 ≤ δ)
    (hδ : metricCauchySchwarzBound (I := I) (M := M) q k δ)
    (S : SmoothCcTensor q 0 1) (x : M) :
    -tensorInnerPointwise (I := I) (M := M) q 0 2 x
        ((hmfDiff (I := I) (M := M) q h S).toFun x)
        ((covGrad (I := I) (M := M) q 0 1 S).toFun x) ≤
      (δ / (1 - δ)) *
        tensorInnerPointwise (I := I) (M := M) q 0 2 x
          ((covGrad (I := I) (M := M) q 0 1 S).toFun x)
          ((covGrad (I := I) (M := M) q 0 1 S).toFun x) := by
  have hneg := negDiffSlot_point_le (I := I) (M := M)
    q h k htie hδ_lt hδ_nn hδ 1 x
    ((covGrad (I := I) (M := M) q 0 1 S).toSection x)
  calc
    -tensorInnerPointwise (I := I) (M := M) q 0 2 x
        ((hmfDiff (I := I) (M := M) q h S).toFun x)
        ((covGrad (I := I) (M := M) q 0 1 S).toFun x) =
      -tensorInnerPointwise (I := I) (M := M) q 0 2 x
        ((covGrad (I := I) (M := M) q 0 1 S).toFun x)
        ((hmfDiff (I := I) (M := M) q h S).toFun x) :=
      congrArg Neg.neg (tensorInnerPointwise_symm
        (I := I) (M := M) q 0 2 x _ _)
    _ = tensorInnerPointwise (I := I) (M := M) q 0 2 x
        ((covGrad (I := I) (M := M) q 0 1 S).toFun x)
        (-((hmfDiff (I := I) (M := M) q h S).toFun x)) := by
      have hsmul := tensorInnerPointwise_smul_right
        (I := I) (M := M) q 0 2 x (-1)
        ((covGrad (I := I) (M := M) q 0 1 S).toFun x)
        ((hmfDiff (I := I) (M := M) q h S).toFun x)
      simpa only [neg_one_smul, neg_one_mul] using hsmul.symm
    _ ≤ _ := by
      simpa only [hmfDiff, appCc_toSection, ContinuousLinearMap.comp_apply] using hneg

omit [BoundarylessManifold I M] in
theorem hmfFlux_diag_le
    (q h : SmoothRiemannianMetric I M)
    (k : ∀ y : M, TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ)
    (htie : ∀ (y : M) (v w : TangentSpace I y),
      h.inner y v w = q.inner y v w + k y v w)
    {δ : ℝ} (hδ_lt : δ < 1) (hδ_nn : 0 ≤ δ)
    (hδ : metricCauchySchwarzBound (I := I) (M := M) q k δ)
    (S : SmoothCcTensor q 0 1) (x : M) :
    tensorInnerPointwise (I := I) (M := M) q 0 2 x
        ((hmfFlux (I := I) (M := M) q h S).toFun x)
        ((covGrad (I := I) (M := M) q 0 1 S).toFun x) ≤
      (1 + δ / (1 - δ)) *
        tensorInnerPointwise (I := I) (M := M) q 0 2 x
          ((covGrad (I := I) (M := M) q 0 1 S).toFun x)
          ((covGrad (I := I) (M := M) q 0 1 S).toFun x) := by
  rw [hmfFlux, SmoothCcTensor.toFun_add, Pi.add_apply,
    tensorInnerPointwise_add_left]
  linarith [hmfDiff_self_le (I := I) (M := M)
    q h k htie hδ_lt hδ_nn hδ S x]

omit [BoundarylessManifold I M] in
theorem hmfFlux_diag_ge
    (q h : SmoothRiemannianMetric I M)
    (k : ∀ y : M, TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ)
    (htie : ∀ (y : M) (v w : TangentSpace I y),
      h.inner y v w = q.inner y v w + k y v w)
    {δ : ℝ} (hδ_lt : δ < 1) (hδ_nn : 0 ≤ δ)
    (hδ : metricCauchySchwarzBound (I := I) (M := M) q k δ)
    (S : SmoothCcTensor q 0 1) (x : M) :
    (1 - δ / (1 - δ)) *
        tensorInnerPointwise (I := I) (M := M) q 0 2 x
          ((covGrad (I := I) (M := M) q 0 1 S).toFun x)
          ((covGrad (I := I) (M := M) q 0 1 S).toFun x) ≤
      tensorInnerPointwise (I := I) (M := M) q 0 2 x
        ((hmfFlux (I := I) (M := M) q h S).toFun x)
        ((covGrad (I := I) (M := M) q 0 1 S).toFun x) := by
  rw [hmfFlux, SmoothCcTensor.toFun_add, Pi.add_apply,
    tensorInnerPointwise_add_left]
  linarith [hmfNegDiff_self_le (I := I) (M := M)
    q h k htie hδ_lt hδ_nn hδ S x]

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [CompactSpace M]
  [BoundarylessManifold I M] in
theorem hmfMass_nonneg
    (q h : SmoothRiemannianMetric I M) (S : SmoothCcTensor q 0 1) :
    0 ≤ hmfMass (I := I) (M := M) q h S S := by
  unfold hmfMass
  exact MeasureTheory.integral_nonneg fun x =>
    tensorInnerPointwise_nonneg (I := I) (M := M) q 0 1 x (S.toFun x)

omit [BoundarylessManifold I M] in
theorem hmfWeak_nonneg
    (q h : SmoothRiemannianMetric I M)
    (k : ∀ y : M, TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ)
    (htie : ∀ (y : M) (v w : TangentSpace I y),
      h.inner y v w = q.inner y v w + k y v w)
    {δ : ℝ} (hδ_half : δ < 1 / 2) (hδ_nn : 0 ≤ δ)
    (hδ : metricCauchySchwarzBound (I := I) (M := M) q k δ)
    (S : SmoothCcTensor q 0 1) :
    0 ≤ hmfWeakForm (I := I) (M := M) q h S S := by
  have hδ_lt : δ < 1 := lt_trans hδ_half (by norm_num)
  have hden : 0 < 1 - δ := sub_pos.mpr hδ_lt
  have hκ : 0 ≤ 1 - δ / (1 - δ) := by
    have hfrac : δ / (1 - δ) < 1 := (div_lt_one hden).2 (by linarith)
    linarith
  unfold hmfWeakForm
  refine MeasureTheory.integral_nonneg (fun x => ?_)
  exact (mul_nonneg hκ
    (tensorInnerPointwise_nonneg (I := I) (M := M) q 0 2 x
      ((covGrad (I := I) (M := M) q 0 1 S).toFun x))).trans
    (hmfFlux_diag_ge (I := I) (M := M)
      q h k htie hδ_lt hδ_nn hδ S x)

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [CompactSpace M]
  [BoundarylessManifold I M] in
theorem hmfMass_self_le
    (q h : SmoothRiemannianMetric I M) (C : ℝ≥0∞)
    (hC0 : C ≠ 0) (hCtop : C ≠ ⊤)
    (hvol : riemannianVolumeMeasure (I := I) (M := M) h ≤
      C • riemannianVolumeMeasure (I := I) (M := M) q)
    (S : SmoothCcTensor q 0 1) :
    hmfMass (I := I) (M := M) q h S S ≤
      C.toReal * hmfMass (I := I) (M := M) q q S S := by
  exact hmf_integral_le (M := M) hC0 hCtop hvol
    (fun x => tensorInnerPointwise_nonneg (I := I) (M := M) q 0 1 x (S.toFun x))
    (hmf_inner_int (I := I) (M := M) q q S S)

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [CompactSpace M]
  [BoundarylessManifold I M] in
theorem hmfMass_self_rev
    (q h : SmoothRiemannianMetric I M) (C : ℝ≥0∞)
    (hC0 : C ≠ 0) (hCtop : C ≠ ⊤)
    (hvol : riemannianVolumeMeasure (I := I) (M := M) q ≤
      C • riemannianVolumeMeasure (I := I) (M := M) h)
    (S : SmoothCcTensor q 0 1) :
    hmfMass (I := I) (M := M) q q S S ≤
      C.toReal * hmfMass (I := I) (M := M) q h S S := by
  exact hmf_integral_le (M := M) hC0 hCtop hvol
    (fun x => tensorInnerPointwise_nonneg (I := I) (M := M) q 0 1 x (S.toFun x))
    (hmf_inner_int (I := I) (M := M) q h S S)

omit [BoundarylessManifold I M] in
theorem hmfForm_self_le
    (q h : SmoothRiemannianMetric I M) (C : ℝ≥0∞)
    (hC0 : C ≠ 0) (hCtop : C ≠ ⊤)
    (hvol : riemannianVolumeMeasure (I := I) (M := M) h ≤
      C • riemannianVolumeMeasure (I := I) (M := M) q)
    (k : ∀ y : M, TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ)
    (htie : ∀ (y : M) (v w : TangentSpace I y),
      h.inner y v w = q.inner y v w + k y v w)
    {δ : ℝ} (hδ_lt : δ < 1) (hδ_nn : 0 ≤ δ)
    (hδ : metricCauchySchwarzBound (I := I) (M := M) q k δ)
    (S : SmoothCcTensor q 0 1) :
    hmfWeakForm (I := I) (M := M) q h S S ≤
      C.toReal * (1 + δ / (1 - δ)) *
        hmfWeakForm (I := I) (M := M) q q S S := by
  let D := covGrad (I := I) (M := M) q 0 1 S
  have hden : 0 < 1 - δ := sub_pos.mpr hδ_lt
  have hκ0 : 0 ≤ δ / (1 - δ) := div_nonneg hδ_nn hden.le
  have hcoef : 0 ≤ 1 + δ / (1 - δ) := by linarith
  have hpt : hmfWeakForm (I := I) (M := M) q h S S ≤
      (1 + δ / (1 - δ)) *
        ∫ x, tensorInnerPointwise (I := I) (M := M) q 0 2 x
          (D.toFun x) (D.toFun x)
          ∂(riemannianVolumeMeasure (I := I) (M := M) h) := by
    unfold hmfWeakForm
    rw [← MeasureTheory.integral_const_mul]
    exact MeasureTheory.integral_mono
      (hmf_inner_int (I := I) (M := M) q h
        (hmfFlux (I := I) (M := M) q h S) D)
      ((hmf_inner_int (I := I) (M := M) q h D D).const_mul
        (1 + δ / (1 - δ)))
      (fun x => hmfFlux_diag_le (I := I) (M := M)
        q h k htie hδ_lt hδ_nn hδ S x)
  have hmeasure :
      (∫ x, tensorInnerPointwise (I := I) (M := M) q 0 2 x
          (D.toFun x) (D.toFun x)
          ∂(riemannianVolumeMeasure (I := I) (M := M) h)) ≤
        C.toReal *
          ∫ x, tensorInnerPointwise (I := I) (M := M) q 0 2 x
            (D.toFun x) (D.toFun x)
            ∂(riemannianVolumeMeasure (I := I) (M := M) q) :=
    hmf_integral_le (M := M) hC0 hCtop hvol
      (fun x => tensorInnerPointwise_nonneg (I := I) (M := M) q 0 2 x (D.toFun x))
      (hmf_inner_int (I := I) (M := M) q q D D)
  calc
    hmfWeakForm (I := I) (M := M) q h S S ≤ _ := hpt
    _ ≤ (1 + δ / (1 - δ)) *
        (C.toReal *
          ∫ x, tensorInnerPointwise (I := I) (M := M) q 0 2 x
            (D.toFun x) (D.toFun x)
            ∂(riemannianVolumeMeasure (I := I) (M := M) q)) :=
      mul_le_mul_of_nonneg_left hmeasure hcoef
    _ = C.toReal * (1 + δ / (1 - δ)) *
        hmfWeakForm (I := I) (M := M) q q S S := by
      rw [hmfWeakForm_self]
      unfold tensorL2Inner
      dsimp only [D]
      ring

omit [BoundarylessManifold I M] in
theorem hmfForm_self_rev
    (q h : SmoothRiemannianMetric I M) (C : ℝ≥0∞)
    (hC0 : C ≠ 0) (hCtop : C ≠ ⊤)
    (hvol : riemannianVolumeMeasure (I := I) (M := M) q ≤
      C • riemannianVolumeMeasure (I := I) (M := M) h)
    (k : ∀ y : M, TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ)
    (htie : ∀ (y : M) (v w : TangentSpace I y),
      h.inner y v w = q.inner y v w + k y v w)
    {δ : ℝ} (hδ_half : δ < 1 / 2) (hδ_nn : 0 ≤ δ)
    (hδ : metricCauchySchwarzBound (I := I) (M := M) q k δ)
    (S : SmoothCcTensor q 0 1) :
    (1 - δ / (1 - δ)) * hmfWeakForm (I := I) (M := M) q q S S ≤
      C.toReal * hmfWeakForm (I := I) (M := M) q h S S := by
  let D := covGrad (I := I) (M := M) q 0 1 S
  have hδ_lt : δ < 1 := lt_trans hδ_half (by norm_num)
  have hden : 0 < 1 - δ := sub_pos.mpr hδ_lt
  have hfrac : δ / (1 - δ) < 1 := (div_lt_one hden).2 (by linarith)
  have hcoef : 0 ≤ 1 - δ / (1 - δ) := by linarith
  have hpt :
      (1 - δ / (1 - δ)) *
          ∫ x, tensorInnerPointwise (I := I) (M := M) q 0 2 x
            (D.toFun x) (D.toFun x)
            ∂(riemannianVolumeMeasure (I := I) (M := M) h) ≤
        hmfWeakForm (I := I) (M := M) q h S S := by
    unfold hmfWeakForm
    rw [← MeasureTheory.integral_const_mul]
    exact MeasureTheory.integral_mono
      ((hmf_inner_int (I := I) (M := M) q h D D).const_mul
        (1 - δ / (1 - δ)))
      (hmf_inner_int (I := I) (M := M) q h
        (hmfFlux (I := I) (M := M) q h S) D)
      (fun x => hmfFlux_diag_ge (I := I) (M := M)
        q h k htie hδ_lt hδ_nn hδ S x)
  have hmeasure :
      (∫ x, tensorInnerPointwise (I := I) (M := M) q 0 2 x
          (D.toFun x) (D.toFun x)
          ∂(riemannianVolumeMeasure (I := I) (M := M) q)) ≤
        C.toReal *
          ∫ x, tensorInnerPointwise (I := I) (M := M) q 0 2 x
            (D.toFun x) (D.toFun x)
            ∂(riemannianVolumeMeasure (I := I) (M := M) h) :=
    hmf_integral_le (M := M) hC0 hCtop hvol
      (fun x => tensorInnerPointwise_nonneg (I := I) (M := M) q 0 2 x (D.toFun x))
      (hmf_inner_int (I := I) (M := M) q h D D)
  rw [hmfWeakForm_self]
  change (1 - δ / (1 - δ)) *
      (∫ x, tensorInnerPointwise (I := I) (M := M) q 0 2 x
        (D.toFun x) (D.toFun x)
        ∂(riemannianVolumeMeasure (I := I) (M := M) q)) ≤ _
  calc
    _ ≤ (1 - δ / (1 - δ)) *
        (C.toReal *
          ∫ x, tensorInnerPointwise (I := I) (M := M) q 0 2 x
            (D.toFun x) (D.toFun x)
            ∂(riemannianVolumeMeasure (I := I) (M := M) h)) :=
      mul_le_mul_of_nonneg_left hmeasure hcoef
    _ = C.toReal * ((1 - δ / (1 - δ)) *
        ∫ x, tensorInnerPointwise (I := I) (M := M) q 0 2 x
          (D.toFun x) (D.toFun x)
          ∂(riemannianVolumeMeasure (I := I) (M := M) h)) := by ring
    _ ≤ C.toReal * hmfWeakForm (I := I) (M := M) q h S S :=
      mul_le_mul_of_nonneg_left hpt ENNReal.toReal_nonneg

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
  [BoundarylessManifold I M] in
theorem hmfVolumeEquiv
    (q : SmoothRiemannianMetric I M)
    (h : ℝ → SmoothRiemannianMetric I M) {a b c : ℝ} (hcb : c < b)
    (hcont : ∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)), ContinuousOn
      (fun p : ℝ × M =>
        chartGramMatrix (I := I) (h p.1) x₀ p.2 i j)
      (Ico a b ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet)) :
    ∃ C : ℝ≥0∞, C ≠ 0 ∧ C ≠ ⊤ ∧ ∀ t ∈ Icc a c,
      riemannianVolumeMeasure (I := I) (M := M) (h t) ≤
          C • riemannianVolumeMeasure (I := I) (M := M) q ∧
        riemannianVolumeMeasure (I := I) (M := M) q ≤
          C • riemannianVolumeMeasure (I := I) (M := M) (h t) := by
  apply volume_uniform_equiv (I := I) (M := M) q h isCompact_Icc
  intro x₀ i j
  exact (hcont x₀ i j).mono fun p hp =>
    ⟨⟨hp.1.1, hp.1.2.trans_lt hcb⟩, hp.2⟩

noncomputable def hmfMassH1
    (q h : SmoothRiemannianMetric I M)
    (S T : SmoothCcTensorH1 q 0 1) : ℝ :=
  hmfMass (I := I) (M := M) q h S.toCcTensor T.toCcTensor

noncomputable def hmfFormH1
    (q h : SmoothRiemannianMetric I M)
    (S T : SmoothCcTensorH1 q 0 1) : ℝ :=
  hmfWeakForm (I := I) (M := M) q h S.toCcTensor T.toCcTensor

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [CompactSpace M]
  [BoundarylessManifold I M] in
private theorem hmfMassH1_add_left
    (q h : SmoothRiemannianMetric I M)
    (S₁ S₂ T : SmoothCcTensorH1 q 0 1) :
    hmfMassH1 (I := I) (M := M) q h (S₁ + S₂) T =
      hmfMassH1 (I := I) (M := M) q h S₁ T +
        hmfMassH1 (I := I) (M := M) q h S₂ T := by
  simp only [hmfMassH1, SmoothCcTensorH1.toCcTensor_add]
  exact hmfMass_add_left (I := I) (M := M) q h _ _ _

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [CompactSpace M]
  [BoundarylessManifold I M] in
private theorem hmfMassH1_smul_left
    (q h : SmoothRiemannianMetric I M) (c : ℝ)
    (S T : SmoothCcTensorH1 q 0 1) :
    hmfMassH1 (I := I) (M := M) q h (c • S) T =
      c * hmfMassH1 (I := I) (M := M) q h S T := by
  simp only [hmfMassH1, SmoothCcTensorH1.toCcTensor_smul]
  exact hmfMass_smul_left (I := I) (M := M) q h c _ _

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [CompactSpace M]
  [BoundarylessManifold I M] in
private theorem hmfMassH1_symm
    (q h : SmoothRiemannianMetric I M) (S T : SmoothCcTensorH1 q 0 1) :
    hmfMassH1 (I := I) (M := M) q h S T =
      hmfMassH1 (I := I) (M := M) q h T S :=
  hmfMass_symm (I := I) (M := M) q h _ _

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [CompactSpace M]
  [BoundarylessManifold I M] in
private theorem hmfMassH1_add_right
    (q h : SmoothRiemannianMetric I M)
    (S T₁ T₂ : SmoothCcTensorH1 q 0 1) :
    hmfMassH1 (I := I) (M := M) q h S (T₁ + T₂) =
      hmfMassH1 (I := I) (M := M) q h S T₁ +
        hmfMassH1 (I := I) (M := M) q h S T₂ := by
  simp only [hmfMassH1, SmoothCcTensorH1.toCcTensor_add]
  exact hmfMass_add_right (I := I) (M := M) q h _ _ _

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [CompactSpace M]
  [BoundarylessManifold I M] in
private theorem hmfMassH1_smul_right
    (q h : SmoothRiemannianMetric I M) (c : ℝ)
    (S T : SmoothCcTensorH1 q 0 1) :
    hmfMassH1 (I := I) (M := M) q h S (c • T) =
      c * hmfMassH1 (I := I) (M := M) q h S T := by
  simp only [hmfMassH1, SmoothCcTensorH1.toCcTensor_smul]
  exact hmfMass_smul_right (I := I) (M := M) q h c _ _

omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
private theorem hmfFormH1_add_left
    (q h : SmoothRiemannianMetric I M)
    (S₁ S₂ T : SmoothCcTensorH1 q 0 1) :
    hmfFormH1 (I := I) (M := M) q h (S₁ + S₂) T =
      hmfFormH1 (I := I) (M := M) q h S₁ T +
        hmfFormH1 (I := I) (M := M) q h S₂ T := by
  simp only [hmfFormH1, SmoothCcTensorH1.toCcTensor_add]
  exact hmfWeak_add_left (I := I) (M := M) q h _ _ _

omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
private theorem hmfFormH1_smul_left
    (q h : SmoothRiemannianMetric I M) (c : ℝ)
    (S T : SmoothCcTensorH1 q 0 1) :
    hmfFormH1 (I := I) (M := M) q h (c • S) T =
      c * hmfFormH1 (I := I) (M := M) q h S T := by
  simp only [hmfFormH1, SmoothCcTensorH1.toCcTensor_smul]
  exact hmfWeak_smul_left (I := I) (M := M) q h c _ _

omit [BoundarylessManifold I M] in
private theorem hmfFormH1_symm
    (q h : SmoothRiemannianMetric I M) (S T : SmoothCcTensorH1 q 0 1) :
    hmfFormH1 (I := I) (M := M) q h S T =
      hmfFormH1 (I := I) (M := M) q h T S :=
  hmfWeak_symm (I := I) (M := M) q h _ _

omit [BoundarylessManifold I M] in
private theorem hmfFormH1_add_right
    (q h : SmoothRiemannianMetric I M)
    (S T₁ T₂ : SmoothCcTensorH1 q 0 1) :
    hmfFormH1 (I := I) (M := M) q h S (T₁ + T₂) =
      hmfFormH1 (I := I) (M := M) q h S T₁ +
        hmfFormH1 (I := I) (M := M) q h S T₂ := by
  simp only [hmfFormH1, SmoothCcTensorH1.toCcTensor_add]
  exact hmfWeak_add_right (I := I) (M := M) q h _ _ _

omit [BoundarylessManifold I M] in
private theorem hmfFormH1_smul_right
    (q h : SmoothRiemannianMetric I M) (c : ℝ)
    (S T : SmoothCcTensorH1 q 0 1) :
    hmfFormH1 (I := I) (M := M) q h S (c • T) =
      c * hmfFormH1 (I := I) (M := M) q h S T := by
  simp only [hmfFormH1, SmoothCcTensorH1.toCcTensor_smul]
  exact hmfWeak_smul_right (I := I) (M := M) q h c _ _

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [CompactSpace M]
  [BoundarylessManifold I M] in
theorem hmfMassH1_nonneg
    (q h : SmoothRiemannianMetric I M) (S : SmoothCcTensorH1 q 0 1) :
    0 ≤ hmfMassH1 (I := I) (M := M) q h S S :=
  hmfMass_nonneg (I := I) (M := M) q h S.toCcTensor

omit [BoundarylessManifold I M] in
theorem hmfFormH1_nonneg
    (q h : SmoothRiemannianMetric I M)
    (k : ∀ y : M, TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ)
    (htie : ∀ (y : M) (v w : TangentSpace I y),
      h.inner y v w = q.inner y v w + k y v w)
    {δ : ℝ} (hδ_half : δ < 1 / 2) (hδ_nn : 0 ≤ δ)
    (hδ : metricCauchySchwarzBound (I := I) (M := M) q k δ)
    (S : SmoothCcTensorH1 q 0 1) :
    0 ≤ hmfFormH1 (I := I) (M := M) q h S S :=
  hmfWeak_nonneg (I := I) (M := M)
    q h k htie hδ_half hδ_nn hδ S.toCcTensor

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M]
  [BoundarylessManifold I M] in
theorem hmfMassH1_diag_le
    (q h : SmoothRiemannianMetric I M) (C : ℝ≥0∞)
    (hC0 : C ≠ 0) (hCtop : C ≠ ⊤)
    (hvol : riemannianVolumeMeasure (I := I) (M := M) h ≤
      C • riemannianVolumeMeasure (I := I) (M := M) q)
    (S : SmoothCcTensorH1 q 0 1) :
    hmfMassH1 (I := I) (M := M) q h S S ≤ C.toReal * ‖S‖ ^ 2 := by
  calc
    hmfMassH1 (I := I) (M := M) q h S S ≤
        C.toReal * hmfMass (I := I) (M := M) q q S.toCcTensor S.toCcTensor :=
      hmfMass_self_le (I := I) (M := M) q h C hC0 hCtop hvol S.toCcTensor
    _ = C.toReal * ‖S.toCcTensor‖ ^ 2 := by
      rw [hmfMass_self,
        ← SmoothCcTensor.norm_sq_eq_inner_self (I := I) (M := M)]
    _ ≤ C.toReal * ‖S‖ ^ 2 :=
      mul_le_mul_of_nonneg_left
        (SmoothCcTensorH1.l2NormSq_le_h1NormSq (I := I) (M := M) S)
        ENNReal.toReal_nonneg

omit [BoundarylessManifold I M] in
theorem hmfFormH1_diag_le
    (q h : SmoothRiemannianMetric I M) (C : ℝ≥0∞)
    (hC0 : C ≠ 0) (hCtop : C ≠ ⊤)
    (hvol : riemannianVolumeMeasure (I := I) (M := M) h ≤
      C • riemannianVolumeMeasure (I := I) (M := M) q)
    (k : ∀ y : M, TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ)
    (htie : ∀ (y : M) (v w : TangentSpace I y),
      h.inner y v w = q.inner y v w + k y v w)
    {δ : ℝ} (hδ_lt : δ < 1) (hδ_nn : 0 ≤ δ)
    (hδ : metricCauchySchwarzBound (I := I) (M := M) q k δ)
    (S : SmoothCcTensorH1 q 0 1) :
    hmfFormH1 (I := I) (M := M) q h S S ≤
      (C.toReal * (1 + δ / (1 - δ))) * ‖S‖ ^ 2 := by
  have hden : 0 < 1 - δ := sub_pos.mpr hδ_lt
  have hcoef : 0 ≤ C.toReal * (1 + δ / (1 - δ)) := by
    exact mul_nonneg ENNReal.toReal_nonneg
      (by have := div_nonneg hδ_nn hden.le; linarith)
  have hfrozen :
      hmfWeakForm (I := I) (M := M) q q S.toCcTensor S.toCcTensor ≤ ‖S‖ ^ 2 := by
    rw [SmoothCcTensorH1.norm_sq_eq_inner_self,
      ← hmfH1_self (I := I) (M := M) q S.toCcTensor S.toCcTensor]
    exact le_add_of_nonneg_left
      (hmfMass_nonneg (I := I) (M := M) q q S.toCcTensor)
  exact (hmfForm_self_le (I := I) (M := M)
    q h C hC0 hCtop hvol k htie hδ_lt hδ_nn hδ S.toCcTensor).trans
      (mul_le_mul_of_nonneg_left hfrozen hcoef)

omit [BoundarylessManifold I M] in
theorem hmfH1_coercive
    (q h : SmoothRiemannianMetric I M) (C : ℝ≥0∞)
    (hC0 : C ≠ 0) (hCtop : C ≠ ⊤)
    (hvol : riemannianVolumeMeasure (I := I) (M := M) q ≤
      C • riemannianVolumeMeasure (I := I) (M := M) h)
    (k : ∀ y : M, TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ)
    (htie : ∀ (y : M) (v w : TangentSpace I y),
      h.inner y v w = q.inner y v w + k y v w)
    {δ : ℝ} (hδ_half : δ < 1 / 2) (hδ_nn : 0 ≤ δ)
    (hδ : metricCauchySchwarzBound (I := I) (M := M) q k δ)
    (S : SmoothCcTensorH1 q 0 1) :
    (1 - δ / (1 - δ)) * ‖S‖ ^ 2 ≤
      C.toReal * (hmfMassH1 (I := I) (M := M) q h S S +
        hmfFormH1 (I := I) (M := M) q h S S) := by
  let α : ℝ := 1 - δ / (1 - δ)
  have hδ_lt : δ < 1 := lt_trans hδ_half (by norm_num)
  have hden : 0 < 1 - δ := sub_pos.mpr hδ_lt
  have hfrac0 : 0 ≤ δ / (1 - δ) := div_nonneg hδ_nn hden.le
  have hfrac1 : δ / (1 - δ) < 1 := (div_lt_one hden).2 (by linarith)
  have hα0 : 0 ≤ α := by dsimp [α]; linarith
  have hα1 : α ≤ 1 := by dsimp [α]; linarith
  have hmassq0 : 0 ≤ hmfMass (I := I) (M := M) q q
      S.toCcTensor S.toCcTensor :=
    hmfMass_nonneg (I := I) (M := M) q q S.toCcTensor
  have hmasspart :
      α * hmfMass (I := I) (M := M) q q S.toCcTensor S.toCcTensor ≤
        C.toReal * hmfMassH1 (I := I) (M := M) q h S S := by
    exact (mul_le_of_le_one_left hmassq0 hα1).trans
      (hmfMass_self_rev (I := I) (M := M)
        q h C hC0 hCtop hvol S.toCcTensor)
  have hformpart :
      α * hmfWeakForm (I := I) (M := M) q q S.toCcTensor S.toCcTensor ≤
        C.toReal * hmfFormH1 (I := I) (M := M) q h S S := by
    simpa only [α, hmfFormH1] using
      (hmfForm_self_rev (I := I) (M := M)
        q h C hC0 hCtop hvol k htie hδ_half hδ_nn hδ S.toCcTensor)
  have hH1 : ‖S‖ ^ 2 =
      hmfMass (I := I) (M := M) q q S.toCcTensor S.toCcTensor +
        hmfWeakForm (I := I) (M := M) q q S.toCcTensor S.toCcTensor :=
    (SmoothCcTensorH1.norm_sq_eq_inner_self (I := I) (M := M) S).trans
      (hmfH1_self (I := I) (M := M) q S.toCcTensor S.toCcTensor).symm
  dsimp only [α] at hmasspart hformpart ⊢
  rw [hH1]
  nlinarith [hmasspart, hformpart]

private theorem bilin_sq_le
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (B : V → V → ℝ)
    (hadd : ∀ u v w, B (u + v) w = B u w + B v w)
    (hsmul : ∀ c u v, B (c • u) v = c * B u v)
    (hsymm : ∀ u v, B u v = B v u)
    (hnn : ∀ u, 0 ≤ B u u) (u v : V) :
    (B u v) ^ 2 ≤ B u u * B v v := by
  have haddR : ∀ u v w, B u (v + w) = B u v + B u w := by
    intro u v w
    rw [hsymm u (v + w), hadd, hsymm v u, hsymm w u]
  have hsmulR : ∀ c u v, B u (c • v) = c * B u v := by
    intro c u v
    rw [hsymm u (c • v), hsmul, hsymm v u]
  let a := B u u
  let b := B u v
  let c := B v v
  have hc0 : 0 ≤ c := hnn v
  have hquad : ∀ t : ℝ, 0 ≤ a + 2 * (t * b) + t ^ 2 * c := by
    intro t
    have h := hnn (u + t • v)
    have hexpand :
        B (u + t • v) (u + t • v) =
          B u u + 2 * (t * B u v) + t ^ 2 * B v v := by
      calc
        B (u + t • v) (u + t • v) =
            B u u + B u (t • v) +
              (B (t • v) u + B (t • v) (t • v)) := by
                rw [hadd, haddR, haddR]
        _ = B u u + 2 * (t * B u v) + t ^ 2 * B v v := by
          rw [hsmulR, hsmul, hsmul, hsmulR, hsymm v u]
          ring
    rw [hexpand] at h
    simpa only [a, b, c] using h
  rcases lt_or_eq_of_le hc0 with hcpos | hczero
  · have hcne : c ≠ 0 := ne_of_gt hcpos
    have h := hquad (-b / c)
    have hsimp : a + 2 * (-b / c * b) + (-b / c) ^ 2 * c =
        a - b ^ 2 / c := by
      field_simp
      ring
    rw [hsimp] at h
    have hmul : 0 * c ≤ (a - b ^ 2 / c) * c :=
      mul_le_mul_of_nonneg_right h hcpos.le
    rw [zero_mul] at hmul
    have hrhs : (a - b ^ 2 / c) * c = a * c - b ^ 2 := by
      field_simp
    rw [hrhs] at hmul
    change b ^ 2 ≤ a * c
    linarith
  · have hc : c = 0 := hczero.symm
    have hquad' : ∀ t : ℝ, 0 ≤ a + 2 * (t * b) := by
      intro t
      have h := hquad t
      rw [hc, mul_zero, add_zero] at h
      exact h
    have hb : b = 0 := by
      by_contra hbne
      rcases lt_or_gt_of_ne hbne with hbneg | hbpos
      · have hden : 0 < -(2 * b) := by linarith
        let t := (a + 1) / (-(2 * b))
        have ht : 2 * (t * b) = -(a + 1) := by
          dsimp [t]
          field_simp
        have := hquad' t
        rw [ht] at this
        linarith
      · have hden : 0 < 2 * b := by linarith
        let t := -(a + 1) / (2 * b)
        have ht : 2 * (t * b) = -(a + 1) := by
          dsimp [t]
          field_simp
        have := hquad' t
        rw [ht] at this
        linarith
    change b ^ 2 ≤ a * c
    rw [hb, hc, mul_zero]
    simp

private theorem bilin_abs_le
    {V : Type*} [SeminormedAddCommGroup V] [NormedSpace ℝ V]
    (B : V → V → ℝ)
    (hadd : ∀ u v w, B (u + v) w = B u w + B v w)
    (hsmul : ∀ c u v, B (c • u) v = c * B u v)
    (hsymm : ∀ u v, B u v = B v u)
    (hnn : ∀ u, 0 ≤ B u u) {K : ℝ} (hK : 0 ≤ K)
    (hdiag : ∀ u, B u u ≤ K * ‖u‖ ^ 2) (u v : V) :
    |B u v| ≤ K * ‖u‖ * ‖v‖ := by
  have hsq := bilin_sq_le B hadd hsmul hsymm hnn u v
  have hprod : B u u * B v v ≤
      (K * ‖u‖ ^ 2) * (K * ‖v‖ ^ 2) :=
    mul_le_mul (hdiag u) (hdiag v) (hnn v)
      (mul_nonneg hK (sq_nonneg ‖u‖))
  have hbound : (B u v) ^ 2 ≤ (K * ‖u‖ * ‖v‖) ^ 2 := by
    calc
      (B u v) ^ 2 ≤ B u u * B v v := hsq
      _ ≤ (K * ‖u‖ ^ 2) * (K * ‖v‖ ^ 2) := hprod
      _ = (K * ‖u‖ * ‖v‖) ^ 2 := by ring
  exact abs_le_of_sq_le_sq hbound
    (mul_nonneg (mul_nonneg hK (norm_nonneg u)) (norm_nonneg v))

noncomputable def hmfMassSmooth
    (q h : SmoothRiemannianMetric I M) (C : ℝ≥0∞)
    (hC0 : C ≠ 0) (hCtop : C ≠ ⊤)
    (hvol : riemannianVolumeMeasure (I := I) (M := M) h ≤
      C • riemannianVolumeMeasure (I := I) (M := M) q) :
    SmoothCcTensorH1 q 0 1 →L[ℝ] SmoothCcTensorH1 q 0 1 →L[ℝ] ℝ := by
  refine LinearMap.mkContinuous₂
    (LinearMap.mk₂ ℝ (hmfMassH1 (I := I) (M := M) q h)
      (hmfMassH1_add_left (I := I) (M := M) q h)
      (hmfMassH1_smul_left (I := I) (M := M) q h)
      (hmfMassH1_add_right (I := I) (M := M) q h)
      (hmfMassH1_smul_right (I := I) (M := M) q h))
    C.toReal ?_
  intro S T
  rw [Real.norm_eq_abs]
  exact bilin_abs_le (hmfMassH1 (I := I) (M := M) q h)
    (hmfMassH1_add_left (I := I) (M := M) q h)
    (hmfMassH1_smul_left (I := I) (M := M) q h)
    (hmfMassH1_symm (I := I) (M := M) q h)
    (hmfMassH1_nonneg (I := I) (M := M) q h)
    ENNReal.toReal_nonneg
    (hmfMassH1_diag_le (I := I) (M := M) q h C hC0 hCtop hvol) S T

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M]
  [BoundarylessManifold I M] in
@[simp] theorem hmfMassSm_apply
    (q h : SmoothRiemannianMetric I M) (C : ℝ≥0∞)
    (hC0 : C ≠ 0) (hCtop : C ≠ ⊤)
    (hvol : riemannianVolumeMeasure (I := I) (M := M) h ≤
      C • riemannianVolumeMeasure (I := I) (M := M) q)
    (S T : SmoothCcTensorH1 q 0 1) :
    hmfMassSmooth (I := I) (M := M) q h C hC0 hCtop hvol S T =
      hmfMassH1 (I := I) (M := M) q h S T := rfl

noncomputable def hmfFormSmooth
    (q h : SmoothRiemannianMetric I M) (C : ℝ≥0∞)
    (hC0 : C ≠ 0) (hCtop : C ≠ ⊤)
    (hvol : riemannianVolumeMeasure (I := I) (M := M) h ≤
      C • riemannianVolumeMeasure (I := I) (M := M) q)
    (k : ∀ y : M, TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ)
    (htie : ∀ (y : M) (v w : TangentSpace I y),
      h.inner y v w = q.inner y v w + k y v w)
    {δ : ℝ} (hδ_half : δ < 1 / 2) (hδ_nn : 0 ≤ δ)
    (hδ : metricCauchySchwarzBound (I := I) (M := M) q k δ) :
    SmoothCcTensorH1 q 0 1 →L[ℝ] SmoothCcTensorH1 q 0 1 →L[ℝ] ℝ := by
  have hδ_lt : δ < 1 := lt_trans hδ_half (by norm_num)
  have hden : 0 < 1 - δ := sub_pos.mpr hδ_lt
  have hK : 0 ≤ C.toReal * (1 + δ / (1 - δ)) :=
    mul_nonneg ENNReal.toReal_nonneg
      (by have := div_nonneg hδ_nn hden.le; linarith)
  refine LinearMap.mkContinuous₂
    (LinearMap.mk₂ ℝ (hmfFormH1 (I := I) (M := M) q h)
      (hmfFormH1_add_left (I := I) (M := M) q h)
      (hmfFormH1_smul_left (I := I) (M := M) q h)
      (hmfFormH1_add_right (I := I) (M := M) q h)
      (hmfFormH1_smul_right (I := I) (M := M) q h))
    (C.toReal * (1 + δ / (1 - δ))) ?_
  intro S T
  rw [Real.norm_eq_abs]
  exact bilin_abs_le (hmfFormH1 (I := I) (M := M) q h)
    (hmfFormH1_add_left (I := I) (M := M) q h)
    (hmfFormH1_smul_left (I := I) (M := M) q h)
    (hmfFormH1_symm (I := I) (M := M) q h)
    (hmfFormH1_nonneg (I := I) (M := M)
      q h k htie hδ_half hδ_nn hδ) hK
    (hmfFormH1_diag_le (I := I) (M := M)
      q h C hC0 hCtop hvol k htie hδ_lt hδ_nn hδ) S T

omit [BoundarylessManifold I M] in
@[simp] theorem hmfFormSm_apply
    (q h : SmoothRiemannianMetric I M) (C : ℝ≥0∞)
    (hC0 : C ≠ 0) (hCtop : C ≠ ⊤)
    (hvol : riemannianVolumeMeasure (I := I) (M := M) h ≤
      C • riemannianVolumeMeasure (I := I) (M := M) q)
    (k : ∀ y : M, TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ)
    (htie : ∀ (y : M) (v w : TangentSpace I y),
      h.inner y v w = q.inner y v w + k y v w)
    {δ : ℝ} (hδ_half : δ < 1 / 2) (hδ_nn : 0 ≤ δ)
    (hδ : metricCauchySchwarzBound (I := I) (M := M) q k δ)
    (S T : SmoothCcTensorH1 q 0 1) :
    hmfFormSmooth (I := I) (M := M) q h C hC0 hCtop hvol
        k htie hδ_half hδ_nn hδ S T =
      hmfFormH1 (I := I) (M := M) q h S T := rfl

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M]
  [BoundarylessManifold I M] in
private lemma hmf_dense
    (q : SmoothRiemannianMetric I M) :
    DenseRange (smoothToTensorH1Compl (I := I) (M := M) q 0 1) :=
  denseRange_smoothToTensorH1Compl (I := I) (M := M) q 0 1

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M]
  [BoundarylessManifold I M] in
private lemma hmf_inducing
    (q : SmoothRiemannianMetric I M) :
    IsUniformInducing
      (smoothToTensorH1Compl (I := I) (M := M) q 0 1) := by
  change IsUniformInducing
    (UniformSpace.Completion.toComplL :
      SmoothCcTensorH1 q 0 1 →L[ℝ] TensorH1Compl q 0 1)
  rw [show (UniformSpace.Completion.toComplL :
        SmoothCcTensorH1 q 0 1 → TensorH1Compl q 0 1) =
      ((↑) : SmoothCcTensorH1 q 0 1 →
        UniformSpace.Completion (SmoothCcTensorH1 q 0 1)) from
      UniformSpace.Completion.coe_toComplL]
  exact UniformSpace.Completion.isUniformInducing_coe (SmoothCcTensorH1 q 0 1)

private local instance smoothCcTensorH1FirstCountable
    (q : SmoothRiemannianMetric I M) :
    FirstCountableTopology (SmoothCcTensorH1 q 0 1) :=
  UniformSpace.firstCountableTopology (SmoothCcTensorH1 q 0 1)

private local instance smoothCcTensorH1Sequential
    (q : SmoothRiemannianMetric I M) :
    SequentialSpace (SmoothCcTensorH1 q 0 1) :=
  FrechetUrysohnSpace.to_sequentialSpace

private local instance smoothCcTensorH1DualComplete
    (q : SmoothRiemannianMetric I M) :
    CompleteSpace (SmoothCcTensorH1 q 0 1 →L[ℝ] ℝ) :=
  ContinuousLinearMap.instCompleteSpace

private noncomputable def hmfExtend
    (q : SmoothRiemannianMetric I M)
    (F : SmoothCcTensorH1 q 0 1 →L[ℝ]
      SmoothCcTensorH1 q 0 1 →L[ℝ] ℝ) :
    TensorH1Compl q 0 1 →L[ℝ] TensorH1Compl q 0 1 →L[ℝ] ℝ :=
  ContinuousLinearMap.flip
    (ContinuousLinearMap.extend
      (ContinuousLinearMap.flip
        (ContinuousLinearMap.extend F
          (smoothToTensorH1Compl (I := I) (M := M) q 0 1)))
      (smoothToTensorH1Compl (I := I) (M := M) q 0 1))

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M]
  [BoundarylessManifold I M] in
private theorem hmfExtend_coe
    (q : SmoothRiemannianMetric I M)
    (F : SmoothCcTensorH1 q 0 1 →L[ℝ]
      SmoothCcTensorH1 q 0 1 →L[ℝ] ℝ)
    (S T : SmoothCcTensorH1 q 0 1) :
    hmfExtend (I := I) (M := M) q F
        (smoothToTensorH1Compl (I := I) (M := M) q 0 1 S)
        (smoothToTensorH1Compl (I := I) (M := M) q 0 1 T) = F S T := by
  unfold hmfExtend
  rw [ContinuousLinearMap.flip_apply]
  rw [ContinuousLinearMap.extend_eq
    (ContinuousLinearMap.flip
      (ContinuousLinearMap.extend F
        (smoothToTensorH1Compl (I := I) (M := M) q 0 1)))
    (e := smoothToTensorH1Compl (I := I) (M := M) q 0 1)
    (hmf_dense (I := I) (M := M) q) (hmf_inducing (I := I) (M := M) q) T]
  rw [ContinuousLinearMap.flip_apply]
  exact congrArg (fun G => G T) (ContinuousLinearMap.extend_eq F
    (e := smoothToTensorH1Compl (I := I) (M := M) q 0 1)
    (hmf_dense (I := I) (M := M) q) (hmf_inducing (I := I) (M := M) q) S)

noncomputable def hmfMassCompl
    (q h : SmoothRiemannianMetric I M) (C : ℝ≥0∞)
    (hC0 : C ≠ 0) (hCtop : C ≠ ⊤)
    (hvol : riemannianVolumeMeasure (I := I) (M := M) h ≤
      C • riemannianVolumeMeasure (I := I) (M := M) q) :
    TensorH1Compl q 0 1 →L[ℝ] TensorH1Compl q 0 1 →L[ℝ] ℝ :=
  hmfExtend (I := I) (M := M) q
    (hmfMassSmooth (I := I) (M := M) q h C hC0 hCtop hvol)

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M]
  [BoundarylessManifold I M] in
@[simp] theorem hmfMassCompl_coe
    (q h : SmoothRiemannianMetric I M) (C : ℝ≥0∞)
    (hC0 : C ≠ 0) (hCtop : C ≠ ⊤)
    (hvol : riemannianVolumeMeasure (I := I) (M := M) h ≤
      C • riemannianVolumeMeasure (I := I) (M := M) q)
    (S T : SmoothCcTensorH1 q 0 1) :
    hmfMassCompl (I := I) (M := M) q h C hC0 hCtop hvol
        (smoothToTensorH1Compl (I := I) (M := M) q 0 1 S)
        (smoothToTensorH1Compl (I := I) (M := M) q 0 1 T) =
      hmfMassH1 (I := I) (M := M) q h S T := by
  rw [hmfMassCompl, hmfExtend_coe, hmfMassSm_apply]

noncomputable def hmfFormCompl
    (q h : SmoothRiemannianMetric I M) (C : ℝ≥0∞)
    (hC0 : C ≠ 0) (hCtop : C ≠ ⊤)
    (hvol : riemannianVolumeMeasure (I := I) (M := M) h ≤
      C • riemannianVolumeMeasure (I := I) (M := M) q)
    (k : ∀ y : M, TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ)
    (htie : ∀ (y : M) (v w : TangentSpace I y),
      h.inner y v w = q.inner y v w + k y v w)
    {δ : ℝ} (hδ_half : δ < 1 / 2) (hδ_nn : 0 ≤ δ)
    (hδ : metricCauchySchwarzBound (I := I) (M := M) q k δ) :
    TensorH1Compl q 0 1 →L[ℝ] TensorH1Compl q 0 1 →L[ℝ] ℝ :=
  hmfExtend (I := I) (M := M) q
    (hmfFormSmooth (I := I) (M := M) q h C hC0 hCtop hvol
      k htie hδ_half hδ_nn hδ)

omit [BoundarylessManifold I M] in
@[simp] theorem hmfFormCompl_coe
    (q h : SmoothRiemannianMetric I M) (C : ℝ≥0∞)
    (hC0 : C ≠ 0) (hCtop : C ≠ ⊤)
    (hvol : riemannianVolumeMeasure (I := I) (M := M) h ≤
      C • riemannianVolumeMeasure (I := I) (M := M) q)
    (k : ∀ y : M, TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ)
    (htie : ∀ (y : M) (v w : TangentSpace I y),
      h.inner y v w = q.inner y v w + k y v w)
    {δ : ℝ} (hδ_half : δ < 1 / 2) (hδ_nn : 0 ≤ δ)
    (hδ : metricCauchySchwarzBound (I := I) (M := M) q k δ)
    (S T : SmoothCcTensorH1 q 0 1) :
    hmfFormCompl (I := I) (M := M) q h C hC0 hCtop hvol
        k htie hδ_half hδ_nn hδ
        (smoothToTensorH1Compl (I := I) (M := M) q 0 1 S)
        (smoothToTensorH1Compl (I := I) (M := M) q 0 1 T) =
      hmfFormH1 (I := I) (M := M) q h S T := by
  rw [hmfFormCompl, hmfExtend_coe, hmfFormSm_apply]

omit [BoundarylessManifold I M] in
theorem hmfCompl_coercive
    (q h : SmoothRiemannianMetric I M) (C : ℝ≥0∞)
    (hC0 : C ≠ 0) (hCtop : C ≠ ⊤)
    (hvol : riemannianVolumeMeasure (I := I) (M := M) h ≤
          C • riemannianVolumeMeasure (I := I) (M := M) q ∧
        riemannianVolumeMeasure (I := I) (M := M) q ≤
          C • riemannianVolumeMeasure (I := I) (M := M) h)
    (k : ∀ y : M, TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ)
    (htie : ∀ (y : M) (v w : TangentSpace I y),
      h.inner y v w = q.inner y v w + k y v w)
    {δ : ℝ} (hδ_half : δ < 1 / 2) (hδ_nn : 0 ≤ δ)
    (hδ : metricCauchySchwarzBound (I := I) (M := M) q k δ)
    (u : TensorH1Compl q 0 1) :
    (1 - δ / (1 - δ)) * ‖u‖ ^ 2 ≤
      C.toReal *
        (hmfMassCompl (I := I) (M := M) q h C hC0 hCtop hvol.1 u u +
          hmfFormCompl (I := I) (M := M) q h C hC0 hCtop hvol.1
            k htie hδ_half hδ_nn hδ u u) := by
  let BM := hmfMassCompl (I := I) (M := M) q h C hC0 hCtop hvol.1
  let BF := hmfFormCompl (I := I) (M := M) q h C hC0 hCtop hvol.1
    k htie hδ_half hδ_nn hδ
  have hBM : Continuous (fun v : TensorH1Compl q 0 1 => BM v v) :=
    BM.continuous.clm_apply continuous_id
  have hBF : Continuous (fun v : TensorH1Compl q 0 1 => BF v v) :=
    BF.continuous.clm_apply continuous_id
  have hclosed : IsClosed {v : TensorH1Compl q 0 1 |
      (1 - δ / (1 - δ)) * ‖v‖ ^ 2 ≤
        C.toReal * (BM v v + BF v v)} :=
    isClosed_le
      (continuous_const.mul (continuous_norm.pow 2))
      (continuous_const.mul (hBM.add hBF))
  refine DenseRange.induction_on (hmf_dense (I := I) (M := M) q) u hclosed ?_
  intro S
  have hnorm :
      ‖smoothToTensorH1Compl (I := I) (M := M) q 0 1 S‖ = ‖S‖ := by
    rw [smoothToTensorH1Compl_apply, UniformSpace.Completion.norm_coe]
  rw [hmfMassCompl_coe, hmfFormCompl_coe, hnorm]
  exact hmfH1_coercive (I := I) (M := M)
    q h C hC0 hCtop hvol.2 k htie hδ_half hδ_nn hδ S

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
  [BoundarylessManifold I M] in
theorem hmfEdge_inputs
    (q : SmoothRiemannianMetric I M)
    (g : ℝ → SmoothRiemannianMetric I M) {a b : ℝ} (hab : a < b)
    (hcont : ∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)), ContinuousOn
      (fun p : ℝ × M => chartGramMatrix (I := I) (g p.1) x₀ p.2 i j)
      (Ico a b ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet))
    (hga : g a = q) :
    ∃ T : ℝ, ∃ C : ℝ≥0∞, 0 < T ∧ a + T < b ∧ C ≠ 0 ∧ C ≠ ⊤ ∧
      ∀ t ∈ Icc a (a + T),
        (riemannianVolumeMeasure (I := I) (M := M) (g t) ≤
              C • riemannianVolumeMeasure (I := I) (M := M) q ∧
            riemannianVolumeMeasure (I := I) (M := M) q ≤
              C • riemannianVolumeMeasure (I := I) (M := M) (g t)) ∧
          metricCauchySchwarzBound (I := I) (M := M) q
            (ccTensorBilinSymm (I := I) q
              (metricDifferenceCcTensor (I := I) (M := M) q (g t))) (1 / 4) := by
  obtain ⟨T, hT, hTb, hop⟩ := metricDiff_smallC0
    (I := I) (M := M) (g := g) (q := q) (a := a) (b := b)
      (δ := (1 / 4 : ℝ)) hab hcont hga (by norm_num)
  obtain ⟨C, hC0, hCtop, hvol⟩ := hmfVolumeEquiv
    (I := I) (M := M) q g (c := a + T) hTb hcont
  exact ⟨T, C, hT, hTb, hC0, hCtop, fun t ht => ⟨hvol t ht, hop t ht⟩⟩

omit [BoundarylessManifold I M] in
theorem hmfEdge_coercive
    (q : SmoothRiemannianMetric I M)
    (g : ℝ → SmoothRiemannianMetric I M) {a T : ℝ} (C : ℝ≥0∞)
    (hC0 : C ≠ 0) (hCtop : C ≠ ⊤)
    (hvol : ∀ t ∈ Icc a (a + T),
      riemannianVolumeMeasure (I := I) (M := M) (g t) ≤
          C • riemannianVolumeMeasure (I := I) (M := M) q ∧
        riemannianVolumeMeasure (I := I) (M := M) q ≤
          C • riemannianVolumeMeasure (I := I) (M := M) (g t))
    (hop : ∀ t ∈ Icc a (a + T),
      metricCauchySchwarzBound (I := I) (M := M) q
        (ccTensorBilinSymm (I := I) q
          (metricDifferenceCcTensor (I := I) (M := M) q (g t))) (1 / 4))
    (t : ℝ) (ht : t ∈ Icc a (a + T)) (u : TensorH1Compl q 0 1) :
    let k := ccTensorBilinSymm (I := I) q
      (metricDifferenceCcTensor (I := I) (M := M) q (g t))
    let htie : ∀ (y : M) (v w : TangentSpace I y),
        (g t).inner y v w = q.inner y v w + k y v w := fun y v w => by
      rw [metricDiff_symVal]
      ring
    (1 - (1 / 4 : ℝ) / (1 - (1 / 4 : ℝ))) * ‖u‖ ^ 2 ≤
      C.toReal *
        (hmfMassCompl (I := I) (M := M) q (g t) C hC0 hCtop
            (hvol t ht).1 u u +
          hmfFormCompl (I := I) (M := M) q (g t) C hC0 hCtop
            (hvol t ht).1 k htie (by norm_num) (by norm_num) (hop t ht) u u) := by
  dsimp only
  apply hmfCompl_coercive (I := I) (M := M)
    q (g t) C hC0 hCtop (hvol t ht)
    (ccTensorBilinSymm (I := I) q
      (metricDifferenceCcTensor (I := I) (M := M) q (g t)))
    (fun y v w => by rw [metricDiff_symVal]; ring)
    (δ := (1 / 4 : ℝ)) (by norm_num) (by norm_num) (hop t ht) u

omit [BoundarylessManifold I M] [SigmaCompactSpace M] in
theorem connAdd_lap_vert
    (g₀ : SmoothRiemannianMetric I M) (p : M) (n : ℕ) (hn : 1 ≤ n)
    (S : SmoothCcTensor g₀ 0 1) :
    fderiv ℝ (connAddTarget (I := I) g₀ p)
        (connAddZeroCoord (I := I) p)
        (0, hmfPrincipal (I := I) g₀ S p) =
      hmfPrincipal (I := I) g₀ S p :=
  connAdd_vert (I := I) g₀ p n hn (hmfPrincipal (I := I) g₀ S p)

end DifferentialGeometry.PDE.RicciFlow.Pullback

end
