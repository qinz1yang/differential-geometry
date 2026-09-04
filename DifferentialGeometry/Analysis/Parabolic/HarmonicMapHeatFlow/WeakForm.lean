import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.State.TensorSobolevLower
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.IntegrationByParts.FirstOrder.DirichletPairing
import DifferentialGeometry.Analysis.Integration.Measure.Riemannian.CompactVolumeEquivalence
import DifferentialGeometry.Analysis.Integration.Measure.Family.Continuity
import DifferentialGeometry.Analysis.Integration.Measure.Family.VolumeVariation
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.MetricPerturbation.SlotInsertSelfAdjointPairing
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.MetricPerturbation.InverseCometricMultiplier
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.MetricPerturbation.ComparisonEndomorphismCovariantDerivative
import DifferentialGeometry.Analysis.Spectral.Tensor.Spectrum.CompactInclusion
import DifferentialGeometry.Analysis.Spectral.Intrinsic.MetricPerturbation.Family.SmallC0
import DifferentialGeometry.Analysis.Spectral.Tensor.Variational.CovDerivPointwise
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.ConnectionDifference.MetricComparisonEndomorphismJetBounds
import DifferentialGeometry.Geometry.Connection.Laplacian.Musical
open DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Analysis.Elliptic
open DifferentialGeometry.PDE.RicciFlow DifferentialGeometry.Analysis.Parabolic
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Operator

noncomputable section

open Bundle Manifold MeasureTheory Set DifferentialGeometry.Tensor0SBundle
open scoped ENNReal Manifold Topology ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Pullback

open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Sobolev.TensorHilbert

open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian
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

abbrev harmonicMapFlowState (g₀ : SmoothRiemannianMetric I M) (a : ℕ) (R : ℝ) :
    Set (DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorHs
      (I := I) (M := M) g₀ 0 1 ((a : ℝ) + 2)) :=
  lowerStateRS (I := I) (M := M) g₀ 0 1 a R

noncomputable def harmonicMapFlowUnknown
    (g₀ : SmoothRiemannianMetric I M) (S : SmoothCcTensor g₀ 0 1) :
    ∀ x : M, TangentSpace I x := fun x =>
  inverseMetricSharpFib (I := I) g₀ x
    (unitEvalSection (I := I) (M := M) g₀ 1 S x)

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [CompactSpace M]
  [T2Space M] [SigmaCompactSpace M] [BoundarylessManifold I M] in
theorem harmonicMapFlowUnknown_add
    (g₀ : SmoothRiemannianMetric I M) (S T : SmoothCcTensor g₀ 0 1)
    (x : M) :
  harmonicMapFlowUnknown (I := I) g₀ (S + T) x =
      harmonicMapFlowUnknown (I := I) g₀ S x + harmonicMapFlowUnknown (I := I) g₀ T x := by
  simp only [harmonicMapFlowUnknown, unitEvalSection_apply, SmoothCcTensor.toSection_add,
    ContMDiffSection.coe_add, Pi.add_apply]
  change inverseMetricSharpFib (I := I) g₀ x
      ((S.toSection x) (unitZeroSec (I := I) (M := M) x) +
        (T.toSection x) (unitZeroSec (I := I) (M := M) x)) =
    _
  rw [map_add]

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [CompactSpace M]
  [T2Space M] [SigmaCompactSpace M] [BoundarylessManifold I M] in
theorem harmonicMapFlowUnknown_smul
    (g₀ : SmoothRiemannianMetric I M) (c : ℝ) (S : SmoothCcTensor g₀ 0 1)
    (x : M) :
  harmonicMapFlowUnknown (I := I) g₀ (c • S) x =
      c • harmonicMapFlowUnknown (I := I) g₀ S x := by
  simp only [harmonicMapFlowUnknown, unitEvalSection_apply, SmoothCcTensor.toSection_smul,
    ContMDiffSection.coe_smul, Pi.smul_apply]
  change inverseMetricSharpFib (I := I) g₀ x
      (c • (S.toSection x) (unitZeroSec (I := I) (M := M) x)) = _
  rw [map_smul]

noncomputable def harmonicMapFlowUnknownLM
    (g₀ : SmoothRiemannianMetric I M) (x : M) :
    SmoothCcTensor g₀ 0 1 →ₗ[ℝ] TangentSpace I x where
  toFun S := harmonicMapFlowUnknown (I := I) g₀ S x
  map_add' S T := harmonicMapFlowUnknown_add (I := I) g₀ S T x
  map_smul' c S := harmonicMapFlowUnknown_smul (I := I) g₀ c S x

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [CompactSpace M]
  [T2Space M] [SigmaCompactSpace M] [BoundarylessManifold I M] in
@[simp] theorem harmonicMapFlowUnknownLM_apply
    (g₀ : SmoothRiemannianMetric I M) (x : M) (S : SmoothCcTensor g₀ 0 1) :
    harmonicMapFlowUnknownLM (I := I) g₀ x S = harmonicMapFlowUnknown (I := I) g₀ S x := rfl

noncomputable def harmonicMapFlowUnknownSec
    (g₀ : SmoothRiemannianMetric I M) (S : SmoothCcTensor g₀ 0 1) :
    Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ where
  toFun := harmonicMapFlowUnknown (I := I) g₀ S
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
omit [I.Boundaryless] in
@[simp] theorem harmonicMapFlowUnknownSec_apply
    (g₀ : SmoothRiemannianMetric I M) (S : SmoothCcTensor g₀ 0 1) (x : M) :
    harmonicMapFlowUnknownSec (I := I) g₀ S x = harmonicMapFlowUnknown (I := I) g₀ S x := rfl

noncomputable def harmonicMapFlowPrincipal
    (g₀ : SmoothRiemannianMetric I M) (S : SmoothCcTensor g₀ 0 1) :
    ∀ x : M, TangentSpace I x := fun x =>
  inverseMetricSharpFib (I := I) g₀ x
    ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 1 I x from
      connLaplacianMixed (I := I) (M := M) g₀ 0 1 S.toSection x)
      (unitZeroSec (I := I) (M := M) x))

omit [CompactSpace M] [SigmaCompactSpace M] in
omit [CompactSpace M] in
theorem harmonicMapFlowPrincipal_eq
    (g₀ : SmoothRiemannianMetric I M) (S : SmoothCcTensor g₀ 0 1) (x : M) :
    harmonicMapFlowPrincipal (I := I) g₀ S x =
      connLaplacianVector (I := I) g₀ (harmonicMapFlowUnknown (I := I) g₀ S) x := by
  change inverseMetricSharpFib (I := I) g₀ x
      ((connLaplacianMixed (I := I) (M := M) g₀ 0 1 S.toSection x)
        (unitZeroSec (I := I) (M := M) x)) =
    connLaplacianVector (I := I) g₀
      (fun y => inverseMetricSharpFib (I := I) g₀ y
        (unitEvalSection (I := I) (M := M) g₀ 1 S y)) x
  exact (sharp_connLap (I := I) (M := M) g₀ S x).symm

noncomputable def harmonicMapFlowDiff
    (q h : SmoothRiemannianMetric I M) (S : SmoothCcTensor q 0 1) :
    SmoothCcTensor q 0 2 :=
  operatorFieldApply (I := I) (M := M) q 2 2
    (endoSlotZeroCcTensor (I := I) (M := M) q 1
      (metricComparisonDifferenceEndomorphismField (I := I) q h))
    (covGrad (I := I) (M := M) q 0 1 S)

noncomputable def harmonicMapFlowFlux
    (q h : SmoothRiemannianMetric I M) (S : SmoothCcTensor q 0 1) :
    SmoothCcTensor q 0 2 :=
  covGrad (I := I) (M := M) q 0 1 S + harmonicMapFlowDiff (I := I) (M := M) q h S

omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] [SigmaCompactSpace M] in
theorem harmonicMapFlowFlux_apply
    (q h : SmoothRiemannianMetric I M) (S : SmoothCcTensor q 0 1)
    (x : M) (m : Fin 2 → E) :
    Tensor0SSpace.toModel
        (unitEvalSection (I := I) (M := M) q 2
          (harmonicMapFlowFlux (I := I) (M := M) q h S) x) m =
      Tensor0SSpace.toModel
        (unitEvalSection (I := I) (M := M) q 2
          (covGrad (I := I) (M := M) q 0 1 S) x)
        (Function.update m 0
          (metricComparisonEndomorphism (I := I) q h x (m 0))) := by
  let D : Tensor0SSpace 2 I x :=
    unitEvalSection (I := I) (M := M) q 2
      (covGrad (I := I) (M := M) q 0 1 S) x
  have hflux :
      unitEvalSection (I := I) (M := M) q 2
          (harmonicMapFlowFlux (I := I) (M := M) q h S) x =
        D + slotInsertEndoFib (I := I) (M := M) 2 0 x
          (metricComparisonDifferenceEndomorphism (I := I) q h x) D := by
    rw [harmonicMapFlowFlux, harmonicMapFlowDiff, unitEvalSection_apply, SmoothCcTensor.toSection_add,
      ContMDiffSection.coe_add, Pi.add_apply, add_apply]
    rw [operatorFieldApplication_toSection, ContinuousLinearMap.comp_apply,
      slotInsertEndoCc_toSection]
    rfl
  rw [hflux, Tensor0SSpace.toModel_add,
    add_apply, slotInsertEndoFib_apply_eval]
  change Tensor0SSpace.toModel D m +
      Tensor0SSpace.toModel D
        (Function.update m 0
          (tangentLinearMapToModel
            (metricComparisonDifferenceEndomorphism (I := I) q h x) (m 0))) =
    Tensor0SSpace.toModel D
      (Function.update m 0
        (tangentLinearMapToModel (metricComparisonEndomorphism (I := I) q h x) (m 0)))
  have hmodel :
      tangentLinearMapToModel (metricComparisonEndomorphism (I := I) q h x) (m 0) =
        tangentLinearMapToModel
            (metricComparisonDifferenceEndomorphism (I := I) q h x) (m 0) + m 0 := by
    simpa only [tangentLinearMapToModel_apply, map_add,
      ContinuousLinearEquiv.apply_symm_apply] using
        congrArg (tangentSpaceModelContinuousLinearEquiv (I := I) x)
          (metricComparisonEndomorphism_eq_diff_add_id (I := I) q h x
            ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm (m 0)))
  rw [hmodel, ContinuousMultilinearMap.map_update_add, Function.update_eq_self]
  abel

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M]
  [SigmaCompactSpace M] [BoundarylessManifold I M] in
omit [I.Boundaryless] in
private theorem harmonicMapFlowRaised_split
    (q h : SmoothRiemannianMetric I M) :
    metricComparisonEndomorphismField (I := I) (M := M) q h =
      metricComparisonDifferenceEndomorphismField (I := I) q h +
        metricComparisonEndomorphismField (I := I) (M := M) q q := by
  apply ContMDiffSection.ext
  intro x
  rw [show ((metricComparisonDifferenceEndomorphismField (I := I) q h +
      metricComparisonEndomorphismField (I := I) (M := M) q q) x) =
      metricComparisonDifferenceEndomorphismField (I := I) q h x +
        metricComparisonEndomorphismField (I := I) (M := M) q q x from by
          rw [ContMDiffSection.coe_add]
          rfl]
  apply ContinuousLinearMap.ext
  intro v
  rw [metricComparisonEndomorphismField_apply, add_apply]
  rw [show metricComparisonDifferenceEndomorphismField (I := I) q h x =
      metricComparisonDifferenceEndomorphism (I := I) q h x from rfl]
  rw [metricComparisonEndomorphismField_apply,
    metricComparisonEndomorphism_eq_diff_add_id (I := I) q h x v]
  rw [show metricComparisonEndomorphism (I := I) q q x v = v from by
    rw [metricComparisonEndomorphism_apply, inverseMetricSharpFib_g0FlatCLM]]

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
  [SigmaCompactSpace M] [BoundarylessManifold I M] in
private theorem harmonicMapFlowSlot_add
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
  rw [add_apply]
  simp only [slotInsertEndoCc_toSection]
  rw [show ((A + B) x) = A x + B x from by
    rw [ContMDiffSection.coe_add]
    rfl]
  rw [slotInsertEndoFib_add_left, add_apply]

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M]
  [BoundarylessManifold I M] in
omit [I.Boundaryless] in
private theorem harmonicMapFlowSlot_self_app
    (q : SmoothRiemannianMetric I M) (W : SmoothCcTensor q 0 2) :
    operatorFieldApply (I := I) (M := M) q 2 2
        (endoSlotZeroCcTensor (I := I) (M := M) q 1
          (metricComparisonEndomorphismField (I := I) (M := M) q q)) W =
      W := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  apply ContinuousLinearMap.ext
  intro d
  apply Tensor0SSpace.toModel_injective
  apply ContinuousMultilinearMap.ext
  intro m
  rw [operatorFieldApplication_toSection, ContinuousLinearMap.comp_apply,
    slotInsertEndoCc_toSection, slotInsertEndoFib_apply_eval,
    metricComparisonEndomorphismField_apply]
  rw [show tangentLinearMapToModel (metricComparisonEndomorphism (I := I) q q x) (m 0) =
      m 0 from by
    rw [tangentLinearMapToModel_apply, metricComparisonEndomorphism_apply,
      inverseMetricSharpFib_g0FlatCLM, ContinuousLinearEquiv.apply_symm_apply]]
  rw [Function.update_eq_self]

omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] [SigmaCompactSpace M] in
theorem harmonicMapFlowFlux_eq_operatorFieldApply
    (q h : SmoothRiemannianMetric I M) (S : SmoothCcTensor q 0 1) :
    harmonicMapFlowFlux (I := I) (M := M) q h S =
      operatorFieldApply (I := I) (M := M) q 2 2
        (endoSlotZeroCcTensor (I := I) (M := M) q 1
          (metricComparisonEndomorphismField (I := I) (M := M) q h))
        (covGrad (I := I) (M := M) q 0 1 S) := by
  rw [harmonicMapFlowFlux, harmonicMapFlowDiff, harmonicMapFlowRaised_split (I := I) (M := M) q h,
    harmonicMapFlowSlot_add (I := I) (M := M) q 1, operatorFieldApplication_add_left,
    harmonicMapFlowSlot_self_app]
  abel

omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] [SigmaCompactSpace M] in
theorem harmonicMapFlowFlux_self
    (q : SmoothRiemannianMetric I M) (S : SmoothCcTensor q 0 1) :
    harmonicMapFlowFlux (I := I) (M := M) q q S =
      covGrad (I := I) (M := M) q 0 1 S := by
  rw [harmonicMapFlowFlux_eq_operatorFieldApply, harmonicMapFlowSlot_self_app]

omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] [SigmaCompactSpace M] in
theorem harmonicMapFlowDiff_add
    (q h : SmoothRiemannianMetric I M) (S T : SmoothCcTensor q 0 1) :
    harmonicMapFlowDiff (I := I) (M := M) q h (S + T) =
      harmonicMapFlowDiff (I := I) (M := M) q h S +
        harmonicMapFlowDiff (I := I) (M := M) q h T := by
  unfold harmonicMapFlowDiff
  rw [covGrad_add, operatorFieldApplication_add_right]

omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] [SigmaCompactSpace M] in
theorem harmonicMapFlowDiff_smul
    (q h : SmoothRiemannianMetric I M) (c : ℝ) (S : SmoothCcTensor q 0 1) :
    harmonicMapFlowDiff (I := I) (M := M) q h (c • S) =
      c • harmonicMapFlowDiff (I := I) (M := M) q h S := by
  unfold harmonicMapFlowDiff
  rw [covGrad_smul, operatorFieldApplication_smul_right]

omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] [SigmaCompactSpace M] in
theorem harmonicMapFlowFlux_add
    (q h : SmoothRiemannianMetric I M) (S T : SmoothCcTensor q 0 1) :
    harmonicMapFlowFlux (I := I) (M := M) q h (S + T) =
      harmonicMapFlowFlux (I := I) (M := M) q h S +
        harmonicMapFlowFlux (I := I) (M := M) q h T := by
  unfold harmonicMapFlowFlux
  rw [covGrad_add, harmonicMapFlowDiff_add]
  abel

omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] [SigmaCompactSpace M] in
theorem harmonicMapFlowFlux_smul
    (q h : SmoothRiemannianMetric I M) (c : ℝ) (S : SmoothCcTensor q 0 1) :
    harmonicMapFlowFlux (I := I) (M := M) q h (c • S) =
      c • harmonicMapFlowFlux (I := I) (M := M) q h S := by
  unfold harmonicMapFlowFlux
  rw [covGrad_smul, harmonicMapFlowDiff_smul, smul_add]

noncomputable def harmonicMapFlowMass
    (q h : SmoothRiemannianMetric I M) (S T : SmoothCcTensor q 0 1) : ℝ :=
  ∫ x, tensorInnerPointwise (I := I) (M := M) q 0 1 x (S.toFun x) (T.toFun x)
    ∂(riemannianVolumeMeasure (I := I) (M := M) h)

noncomputable def harmonicMapFlowWeakForm
    (q h : SmoothRiemannianMetric I M) (S T : SmoothCcTensor q 0 1) : ℝ :=
  ∫ x, tensorInnerPointwise (I := I) (M := M) q 0 2 x
      ((harmonicMapFlowFlux (I := I) (M := M) q h S).toFun x)
      ((covGrad (I := I) (M := M) q 0 1 T).toFun x)
    ∂(riemannianVolumeMeasure (I := I) (M := M) h)

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
  [BoundarylessManifold I M] in
theorem harmonicMapFlowMass_time_cont
    (q : SmoothRiemannianMetric I M)
    (g : ℝ → SmoothRiemannianMetric I M) {K : Set ℝ} (hK : IsCompact K)
    (hcont : ∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)), ContinuousOn
      (fun p : ℝ × M => DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (I := I) (g p.1) x₀ p.2 i j)
      (K ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet))
    (S T : SmoothCcTensor q 0 1) :
    ContinuousOn (fun t => harmonicMapFlowMass (I := I) (M := M) q (g t) S T) K := by
  unfold harmonicMapFlowMass
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
theorem harmonicMapFlowMass_hasDerivAt
    (q : SmoothRiemannianMetric I M)
    (g : ℝ → SmoothRiemannianMetric I M) (t₀ : ℝ)
    (hg : MetricFamilyRegularAt (I := I) g t₀)
    (S T : SmoothCcTensor q 0 1) :
    HasDerivAt
      (fun t => harmonicMapFlowMass (I := I) (M := M) q (g t) S T)
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
  have hvar := volume_variation_formula (I := I) (M := M) hg hreg
  have hderiv : ∀ x : M, deriv (fun _ : ℝ => f x) t₀ = 0 := fun x =>
    (hasDerivAt_const (x := t₀) (c := f x)).deriv
  simpa only [harmonicMapFlowMass, f, riemannianMeasureFamily_def, hderiv, zero_add] using hvar

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [CompactSpace M]
  [BoundarylessManifold I M] in
private lemma hmf_inner_int
    (q h : SmoothRiemannianMetric I M) {r s : ℕ}
    (S T : SmoothCcTensor q r s) :
    MeasureTheory.Integrable
      (fun x => tensorInnerPointwise (I := I) (M := M) q r s x
        (S.toFun x) (T.toFun x))
      (riemannianVolumeMeasure (I := I) (M := M) h) := by
  let : IsFiniteMeasureOnCompacts
      (riemannianVolumeMeasure (I := I) (M := M) h) :=
    riemannianVolumeMeasure_isFiniteMeasureOnCompacts (I := I) (M := M) h
  exact (SmoothCcTensor.continuous_inner_cross (I := I)
    (M := M) S T).integrable_of_hasCompactSupport
    (SmoothCcTensor.hasCompactSupport_inner_cross (I := I) (M := M) S T)

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [CompactSpace M]
  [BoundarylessManifold I M] in
theorem harmonicMapFlowMass_add_left
    (q h : SmoothRiemannianMetric I M) (S₁ S₂ T : SmoothCcTensor q 0 1) :
    harmonicMapFlowMass (I := I) (M := M) q h (S₁ + S₂) T =
      harmonicMapFlowMass (I := I) (M := M) q h S₁ T +
        harmonicMapFlowMass (I := I) (M := M) q h S₂ T := by
  unfold harmonicMapFlowMass
  rw [SmoothCcTensor.toFun_add]
  simp only [Pi.add_apply, tensorInnerPointwise_add_left]
  exact MeasureTheory.integral_add
    (hmf_inner_int (I := I) (M := M) q h S₁ T)
    (hmf_inner_int (I := I) (M := M) q h S₂ T)

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [CompactSpace M]
  [BoundarylessManifold I M] in
theorem harmonicMapFlowMass_smul_left
    (q h : SmoothRiemannianMetric I M) (c : ℝ) (S T : SmoothCcTensor q 0 1) :
    harmonicMapFlowMass (I := I) (M := M) q h (c • S) T =
      c * harmonicMapFlowMass (I := I) (M := M) q h S T := by
  unfold harmonicMapFlowMass
  rw [SmoothCcTensor.toFun_smul]
  simp only [Pi.smul_apply, tensorInnerPointwise_smul_left,
    MeasureTheory.integral_const_mul]

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [CompactSpace M]
  [BoundarylessManifold I M] in
theorem harmonicMapFlowMass_symm
    (q h : SmoothRiemannianMetric I M) (S T : SmoothCcTensor q 0 1) :
    harmonicMapFlowMass (I := I) (M := M) q h S T =
      harmonicMapFlowMass (I := I) (M := M) q h T S := by
  unfold harmonicMapFlowMass
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall ?_)
  intro x
  exact tensorInnerPointwise_symm (I := I) (M := M) q 0 1 x
    (S.toFun x) (T.toFun x)

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [CompactSpace M]
  [BoundarylessManifold I M] in
theorem harmonicMapFlowMass_add_right
    (q h : SmoothRiemannianMetric I M) (S T₁ T₂ : SmoothCcTensor q 0 1) :
    harmonicMapFlowMass (I := I) (M := M) q h S (T₁ + T₂) =
      harmonicMapFlowMass (I := I) (M := M) q h S T₁ +
        harmonicMapFlowMass (I := I) (M := M) q h S T₂ := by
  rw [harmonicMapFlowMass_symm, harmonicMapFlowMass_add_left, harmonicMapFlowMass_symm q h T₁ S,
    harmonicMapFlowMass_symm q h T₂ S]

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [CompactSpace M]
  [BoundarylessManifold I M] in
theorem harmonicMapFlowMass_smul_right
    (q h : SmoothRiemannianMetric I M) (c : ℝ) (S T : SmoothCcTensor q 0 1) :
    harmonicMapFlowMass (I := I) (M := M) q h S (c • T) =
      c * harmonicMapFlowMass (I := I) (M := M) q h S T := by
  rw [harmonicMapFlowMass_symm, harmonicMapFlowMass_smul_left, harmonicMapFlowMass_symm q h T S]

omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
theorem harmonicMapFlowWeak_add_left
    (q h : SmoothRiemannianMetric I M) (S₁ S₂ T : SmoothCcTensor q 0 1) :
    harmonicMapFlowWeakForm (I := I) (M := M) q h (S₁ + S₂) T =
      harmonicMapFlowWeakForm (I := I) (M := M) q h S₁ T +
        harmonicMapFlowWeakForm (I := I) (M := M) q h S₂ T := by
  unfold harmonicMapFlowWeakForm
  rw [harmonicMapFlowFlux_add, SmoothCcTensor.toFun_add]
  simp only [Pi.add_apply, tensorInnerPointwise_add_left]
  exact MeasureTheory.integral_add
    (hmf_inner_int (I := I) (M := M) q h
      (harmonicMapFlowFlux (I := I) (M := M) q h S₁)
      (covGrad (I := I) (M := M) q 0 1 T))
    (hmf_inner_int (I := I) (M := M) q h
      (harmonicMapFlowFlux (I := I) (M := M) q h S₂)
      (covGrad (I := I) (M := M) q 0 1 T))

omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
theorem harmonicMapFlowWeak_smul_left
    (q h : SmoothRiemannianMetric I M) (c : ℝ) (S T : SmoothCcTensor q 0 1) :
    harmonicMapFlowWeakForm (I := I) (M := M) q h (c • S) T =
      c * harmonicMapFlowWeakForm (I := I) (M := M) q h S T := by
  unfold harmonicMapFlowWeakForm
  rw [harmonicMapFlowFlux_smul, SmoothCcTensor.toFun_smul]
  simp only [Pi.smul_apply, tensorInnerPointwise_smul_left,
    MeasureTheory.integral_const_mul]

omit [BoundarylessManifold I M] [SigmaCompactSpace M] in
private theorem harmonicMapFlowDiff_pair_symm
    (q h : SmoothRiemannianMetric I M) (S T : SmoothCcTensor q 0 1) (x : M) :
    tensorInnerPointwise (I := I) (M := M) q 0 2 x
        ((harmonicMapFlowDiff (I := I) (M := M) q h S).toFun x)
        ((covGrad (I := I) (M := M) q 0 1 T).toFun x) =
      tensorInnerPointwise (I := I) (M := M) q 0 2 x
        ((harmonicMapFlowDiff (I := I) (M := M) q h T).toFun x)
        ((covGrad (I := I) (M := M) q 0 1 S).toFun x) := by
  obtain ⟨e, bse, hbse, horth⟩ :=
    exists_orthoFrame_basis_E (I := I) (M := M) q x
  have hfield :
      metricComparisonDifferenceEndomorphismField (I := I) q h x =
        metricComparisonDifferenceEndomorphism (I := I) q h x := rfl
  have hslot := tensorInnerPointwise_slotΛ_self_adjoint
    (I := I) (M := M) q 1 x
    (metricComparisonDifferenceEndomorphism (I := I) q h x)
    (metricComparisonDifferenceEndomorphism_g0_self_adjoint (I := I) q h x)
    ((covGrad (I := I) (M := M) q 0 1 S).toSection x)
    ((covGrad (I := I) (M := M) q 0 1 T).toSection x)
    e bse hbse horth
  calc
    tensorInnerPointwise (I := I) (M := M) q 0 2 x
        ((harmonicMapFlowDiff (I := I) (M := M) q h S).toFun x)
        ((covGrad (I := I) (M := M) q 0 1 T).toFun x) =
      tensorInnerPointwise (I := I) (M := M) q 0 2 x
        ((covGrad (I := I) (M := M) q 0 1 S).toFun x)
        ((harmonicMapFlowDiff (I := I) (M := M) q h T).toFun x) := by
          simpa only [SmoothCcTensor.toFun_apply, harmonicMapFlowDiff,
            operatorFieldApplication_toSection, ContinuousLinearMap.comp_apply,
            slotInsertEndoCc_toSection, hfield,
            TensorRSSpace.ofCLM] using hslot
    _ = _ := tensorInnerPointwise_symm (I := I) (M := M) q 0 2 x _ _

omit [BoundarylessManifold I M] in
theorem harmonicMapFlowWeak_symm
    (q h : SmoothRiemannianMetric I M) (S T : SmoothCcTensor q 0 1) :
    harmonicMapFlowWeakForm (I := I) (M := M) q h S T =
      harmonicMapFlowWeakForm (I := I) (M := M) q h T S := by
  unfold harmonicMapFlowWeakForm
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall ?_)
  intro x
  simp only [harmonicMapFlowFlux, SmoothCcTensor.toFun_add, Pi.add_apply,
    tensorInnerPointwise_add_left]
  rw [
    tensorInnerPointwise_symm (I := I) (M := M) q 0 2 x
      ((covGrad (I := I) (M := M) q 0 1 S).toFun x)
      ((covGrad (I := I) (M := M) q 0 1 T).toFun x),
    harmonicMapFlowDiff_pair_symm]

omit [BoundarylessManifold I M] in
theorem harmonicMapFlowWeak_add_right
    (q h : SmoothRiemannianMetric I M) (S T₁ T₂ : SmoothCcTensor q 0 1) :
    harmonicMapFlowWeakForm (I := I) (M := M) q h S (T₁ + T₂) =
      harmonicMapFlowWeakForm (I := I) (M := M) q h S T₁ +
        harmonicMapFlowWeakForm (I := I) (M := M) q h S T₂ := by
  rw [harmonicMapFlowWeak_symm, harmonicMapFlowWeak_add_left, harmonicMapFlowWeak_symm q h T₁ S,
    harmonicMapFlowWeak_symm q h T₂ S]

omit [BoundarylessManifold I M] in
theorem harmonicMapFlowWeak_smul_right
    (q h : SmoothRiemannianMetric I M) (c : ℝ) (S T : SmoothCcTensor q 0 1) :
    harmonicMapFlowWeakForm (I := I) (M := M) q h S (c • T) =
      c * harmonicMapFlowWeakForm (I := I) (M := M) q h S T := by
  rw [harmonicMapFlowWeak_symm, harmonicMapFlowWeak_smul_left, harmonicMapFlowWeak_symm q h T S]

omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
theorem harmonicMapFlowWeakForm_eq
    (q h : SmoothRiemannianMetric I M) (S T : SmoothCcTensor q 0 1) :
    harmonicMapFlowWeakForm (I := I) (M := M) q h S T =
      ∫ x, tensorInnerPointwise (I := I) (M := M) q 0 2 x
          ((covGrad (I := I) (M := M) q 0 1 S +
            operatorFieldApply (I := I) (M := M) q 2 2
              (endoSlotZeroCcTensor (I := I) (M := M) q 1
                (metricComparisonDifferenceEndomorphismField (I := I) q h))
              (covGrad (I := I) (M := M) q 0 1 S)).toFun x)
          ((covGrad (I := I) (M := M) q 0 1 T).toFun x)
        ∂(riemannianVolumeMeasure (I := I) (M := M) h) := rfl

omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
theorem harmonicMapFlowWeakForm_eq_operatorFieldApply
    (q h : SmoothRiemannianMetric I M) (S T : SmoothCcTensor q 0 1) :
    harmonicMapFlowWeakForm (I := I) (M := M) q h S T =
      ∫ x, tensorInnerPointwise (I := I) (M := M) q 0 2 x
          ((operatorFieldApply (I := I) (M := M) q 2 2
            (endoSlotZeroCcTensor (I := I) (M := M) q 1
              (metricComparisonEndomorphismField (I := I) (M := M) q h))
            (covGrad (I := I) (M := M) q 0 1 S)).toFun x)
          ((covGrad (I := I) (M := M) q 0 1 T).toFun x)
        ∂(riemannianVolumeMeasure (I := I) (M := M) h) := by
  rw [harmonicMapFlowWeakForm, harmonicMapFlowFlux_eq_operatorFieldApply]

omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
theorem harmonicMapFlowWeakForm_self
    (q : SmoothRiemannianMetric I M) (S T : SmoothCcTensor q 0 1) :
    harmonicMapFlowWeakForm (I := I) (M := M) q q S T =
      tensorL2Inner (I := I) (M := M) q 0 2
        (covGrad (I := I) (M := M) q 0 1 S).toFun
        (covGrad (I := I) (M := M) q 0 1 T).toFun := by
  rw [harmonicMapFlowWeakForm, harmonicMapFlowFlux_self]
  rfl

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [CompactSpace M]
  [BoundarylessManifold I M] in
theorem harmonicMapFlowMass_self
    (q : SmoothRiemannianMetric I M) (S T : SmoothCcTensor q 0 1) :
    harmonicMapFlowMass (I := I) (M := M) q q S T =
      tensorL2Inner (I := I) (M := M) q 0 1 S.toFun T.toFun := rfl

omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
theorem harmonicMapFlowH1_self
    (q : SmoothRiemannianMetric I M) (S T : SmoothCcTensor q 0 1) :
    harmonicMapFlowMass (I := I) (M := M) q q S T +
        harmonicMapFlowWeakForm (I := I) (M := M) q q S T =
      tensorH1Inner (I := I) (M := M) q 0 1 S T := by
  rw [harmonicMapFlowMass_self, harmonicMapFlowWeakForm_self, tensorH1Inner_def,
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

omit [BoundarylessManifold I M] [SigmaCompactSpace M] in
private theorem harmonicMapFlowDiff_self_le
    (q h : SmoothRiemannianMetric I M)
    (k : ∀ y : M, TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ)
    (htie : ∀ (y : M) (v w : TangentSpace I y),
      h.inner y v w = q.inner y v w + k y v w)
    {δ : ℝ} (hδ_lt : δ < 1) (hδ_nn : 0 ≤ δ)
    (hδ : metricCauchySchwarzBound (I := I) (M := M) q k δ)
    (S : SmoothCcTensor q 0 1) (x : M) :
    tensorInnerPointwise (I := I) (M := M) q 0 2 x
        ((harmonicMapFlowDiff (I := I) (M := M) q h S).toFun x)
        ((covGrad (I := I) (M := M) q 0 1 S).toFun x) ≤
      (δ / (1 - δ)) *
        tensorInnerPointwise (I := I) (M := M) q 0 2 x
          ((covGrad (I := I) (M := M) q 0 1 S).toFun x)
          ((covGrad (I := I) (M := M) q 0 1 S).toFun x) := by
  have hfield :
      metricComparisonDifferenceEndomorphismField (I := I) q h x =
        metricComparisonDifferenceEndomorphism (I := I) q h x := rfl
  rw [tensorInnerPointwise_symm (I := I) (M := M) q 0 2 x
    ((harmonicMapFlowDiff (I := I) (M := M) q h S).toFun x)
    ((covGrad (I := I) (M := M) q 0 1 S).toFun x)]
  simpa only [SmoothCcTensor.toFun_apply, harmonicMapFlowDiff,
    operatorFieldApplication_toSection, ContinuousLinearMap.comp_apply,
    slotInsertEndoCc_toSection, hfield,
    TensorRSSpace.ofCLM, gInvDiffSlotApplied] using
    (tensorInnerPointwise_gInvDiffSlot_le (I := I) (M := M)
      q h k htie hδ_lt hδ_nn hδ 1 x
      ((covGrad (I := I) (M := M) q 0 1 S).toSection x))

omit [BoundarylessManifold I M] [SigmaCompactSpace M] in
private theorem harmonicMapFlowNegDiff_self_le
    (q h : SmoothRiemannianMetric I M)
    (k : ∀ y : M, TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ)
    (htie : ∀ (y : M) (v w : TangentSpace I y),
      h.inner y v w = q.inner y v w + k y v w)
    {δ : ℝ} (hδ_lt : δ < 1) (hδ_nn : 0 ≤ δ)
    (hδ : metricCauchySchwarzBound (I := I) (M := M) q k δ)
    (S : SmoothCcTensor q 0 1) (x : M) :
    -tensorInnerPointwise (I := I) (M := M) q 0 2 x
        ((harmonicMapFlowDiff (I := I) (M := M) q h S).toFun x)
        ((covGrad (I := I) (M := M) q 0 1 S).toFun x) ≤
      (δ / (1 - δ)) *
        tensorInnerPointwise (I := I) (M := M) q 0 2 x
          ((covGrad (I := I) (M := M) q 0 1 S).toFun x)
          ((covGrad (I := I) (M := M) q 0 1 S).toFun x) := by
  have hfield :
      metricComparisonDifferenceEndomorphismField (I := I) q h x =
        metricComparisonDifferenceEndomorphism (I := I) q h x := rfl
  have hneg := negDiffSlot_point_le (I := I) (M := M)
    q h k htie hδ_lt hδ_nn hδ 1 x
    ((covGrad (I := I) (M := M) q 0 1 S).toSection x)
  calc
    -tensorInnerPointwise (I := I) (M := M) q 0 2 x
        ((harmonicMapFlowDiff (I := I) (M := M) q h S).toFun x)
        ((covGrad (I := I) (M := M) q 0 1 S).toFun x) =
      -tensorInnerPointwise (I := I) (M := M) q 0 2 x
        ((covGrad (I := I) (M := M) q 0 1 S).toFun x)
        ((harmonicMapFlowDiff (I := I) (M := M) q h S).toFun x) :=
      congrArg Neg.neg (tensorInnerPointwise_symm
        (I := I) (M := M) q 0 2 x _ _)
    _ = tensorInnerPointwise (I := I) (M := M) q 0 2 x
        ((covGrad (I := I) (M := M) q 0 1 S).toFun x)
        (-((harmonicMapFlowDiff (I := I) (M := M) q h S).toFun x)) := by
      have hsmul := tensorInnerPointwise_smul_right
        (I := I) (M := M) q 0 2 x (-1)
        ((covGrad (I := I) (M := M) q 0 1 S).toFun x)
        ((harmonicMapFlowDiff (I := I) (M := M) q h S).toFun x)
      simpa only [neg_one_smul, neg_one_mul] using hsmul.symm
    _ ≤ _ := by
      simpa only [SmoothCcTensor.toFun_apply, harmonicMapFlowDiff,
        operatorFieldApplication_toSection, ContinuousLinearMap.comp_apply,
        slotInsertEndoCc_toSection, hfield,
        TensorRSSpace.ofCLM, gInvDiffSlotApplied] using hneg

omit [BoundarylessManifold I M] [SigmaCompactSpace M] in
theorem harmonicMapFlowFlux_diag_le
    (q h : SmoothRiemannianMetric I M)
    (k : ∀ y : M, TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ)
    (htie : ∀ (y : M) (v w : TangentSpace I y),
      h.inner y v w = q.inner y v w + k y v w)
    {δ : ℝ} (hδ_lt : δ < 1) (hδ_nn : 0 ≤ δ)
    (hδ : metricCauchySchwarzBound (I := I) (M := M) q k δ)
    (S : SmoothCcTensor q 0 1) (x : M) :
    tensorInnerPointwise (I := I) (M := M) q 0 2 x
        ((harmonicMapFlowFlux (I := I) (M := M) q h S).toFun x)
        ((covGrad (I := I) (M := M) q 0 1 S).toFun x) ≤
      (1 + δ / (1 - δ)) *
        tensorInnerPointwise (I := I) (M := M) q 0 2 x
          ((covGrad (I := I) (M := M) q 0 1 S).toFun x)
          ((covGrad (I := I) (M := M) q 0 1 S).toFun x) := by
  rw [harmonicMapFlowFlux, SmoothCcTensor.toFun_add, Pi.add_apply,
    tensorInnerPointwise_add_left]
  linarith [harmonicMapFlowDiff_self_le (I := I) (M := M)
    q h k htie hδ_lt hδ_nn hδ S x]

omit [BoundarylessManifold I M] [SigmaCompactSpace M] in
theorem harmonicMapFlowFlux_diag_ge
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
        ((harmonicMapFlowFlux (I := I) (M := M) q h S).toFun x)
        ((covGrad (I := I) (M := M) q 0 1 S).toFun x) := by
  rw [harmonicMapFlowFlux, SmoothCcTensor.toFun_add, Pi.add_apply,
    tensorInnerPointwise_add_left]
  linarith [harmonicMapFlowNegDiff_self_le (I := I) (M := M)
    q h k htie hδ_lt hδ_nn hδ S x]

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [CompactSpace M]
  [BoundarylessManifold I M] in
theorem harmonicMapFlowMass_nonneg
    (q h : SmoothRiemannianMetric I M) (S : SmoothCcTensor q 0 1) :
    0 ≤ harmonicMapFlowMass (I := I) (M := M) q h S S := by
  unfold harmonicMapFlowMass
  exact MeasureTheory.integral_nonneg fun x =>
    tensorInnerPointwise_nonneg (I := I) (M := M) q 0 1 x (S.toFun x)

omit [BoundarylessManifold I M] in
theorem harmonicMapFlowWeak_nonneg
    (q h : SmoothRiemannianMetric I M)
    (k : ∀ y : M, TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ)
    (htie : ∀ (y : M) (v w : TangentSpace I y),
      h.inner y v w = q.inner y v w + k y v w)
    {δ : ℝ} (hδ_half : δ < 1 / 2) (hδ_nn : 0 ≤ δ)
    (hδ : metricCauchySchwarzBound (I := I) (M := M) q k δ)
    (S : SmoothCcTensor q 0 1) :
    0 ≤ harmonicMapFlowWeakForm (I := I) (M := M) q h S S := by
  have hδ_lt : δ < 1 := lt_trans hδ_half (by norm_num)
  have hden : 0 < 1 - δ := sub_pos.mpr hδ_lt
  have hκ : 0 ≤ 1 - δ / (1 - δ) := by
    have hfrac : δ / (1 - δ) < 1 := (div_lt_one hden).2 (by linarith)
    linarith
  unfold harmonicMapFlowWeakForm
  refine MeasureTheory.integral_nonneg (fun x => ?_)
  exact (mul_nonneg hκ
    (tensorInnerPointwise_nonneg (I := I) (M := M) q 0 2 x
      ((covGrad (I := I) (M := M) q 0 1 S).toFun x))).trans
    (harmonicMapFlowFlux_diag_ge (I := I) (M := M)
      q h k htie hδ_lt hδ_nn hδ S x)

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [CompactSpace M]
  [BoundarylessManifold I M] in
theorem harmonicMapFlowMass_self_le
    (q h : SmoothRiemannianMetric I M) (C : ℝ≥0∞)
    (hC0 : C ≠ 0) (hCtop : C ≠ ⊤)
    (hvol : riemannianVolumeMeasure (I := I) (M := M) h ≤
      C • riemannianVolumeMeasure (I := I) (M := M) q)
    (S : SmoothCcTensor q 0 1) :
    harmonicMapFlowMass (I := I) (M := M) q h S S ≤
      C.toReal * harmonicMapFlowMass (I := I) (M := M) q q S S := by
  exact hmf_integral_le (M := M) hC0 hCtop hvol
    (fun x => tensorInnerPointwise_nonneg (I := I) (M := M) q 0 1 x (S.toFun x))
    (hmf_inner_int (I := I) (M := M) q q S S)

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [CompactSpace M]
  [BoundarylessManifold I M] in
theorem harmonicMapFlowMass_self_rev
    (q h : SmoothRiemannianMetric I M) (C : ℝ≥0∞)
    (hC0 : C ≠ 0) (hCtop : C ≠ ⊤)
    (hvol : riemannianVolumeMeasure (I := I) (M := M) q ≤
      C • riemannianVolumeMeasure (I := I) (M := M) h)
    (S : SmoothCcTensor q 0 1) :
    harmonicMapFlowMass (I := I) (M := M) q q S S ≤
      C.toReal * harmonicMapFlowMass (I := I) (M := M) q h S S := by
  exact hmf_integral_le (M := M) hC0 hCtop hvol
    (fun x => tensorInnerPointwise_nonneg (I := I) (M := M) q 0 1 x (S.toFun x))
    (hmf_inner_int (I := I) (M := M) q h S S)

omit [BoundarylessManifold I M] in
theorem harmonicMapFlowForm_self_le
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
    harmonicMapFlowWeakForm (I := I) (M := M) q h S S ≤
      C.toReal * (1 + δ / (1 - δ)) *
        harmonicMapFlowWeakForm (I := I) (M := M) q q S S := by
  let D := covGrad (I := I) (M := M) q 0 1 S
  have hden : 0 < 1 - δ := sub_pos.mpr hδ_lt
  have hκ0 : 0 ≤ δ / (1 - δ) := div_nonneg hδ_nn hden.le
  have hcoef : 0 ≤ 1 + δ / (1 - δ) := by linarith
  have hpt : harmonicMapFlowWeakForm (I := I) (M := M) q h S S ≤
      (1 + δ / (1 - δ)) *
        ∫ x, tensorInnerPointwise (I := I) (M := M) q 0 2 x
          (D.toFun x) (D.toFun x)
          ∂(riemannianVolumeMeasure (I := I) (M := M) h) := by
    unfold harmonicMapFlowWeakForm
    rw [← MeasureTheory.integral_const_mul]
    exact MeasureTheory.integral_mono
      (hmf_inner_int (I := I) (M := M) q h
        (harmonicMapFlowFlux (I := I) (M := M) q h S) D)
      ((hmf_inner_int (I := I) (M := M) q h D D).const_mul
        (1 + δ / (1 - δ)))
      (fun x => harmonicMapFlowFlux_diag_le (I := I) (M := M)
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
    harmonicMapFlowWeakForm (I := I) (M := M) q h S S ≤ _ := hpt
    _ ≤ (1 + δ / (1 - δ)) *
        (C.toReal *
          ∫ x, tensorInnerPointwise (I := I) (M := M) q 0 2 x
            (D.toFun x) (D.toFun x)
            ∂(riemannianVolumeMeasure (I := I) (M := M) q)) :=
      mul_le_mul_of_nonneg_left hmeasure hcoef
    _ = C.toReal * (1 + δ / (1 - δ)) *
        harmonicMapFlowWeakForm (I := I) (M := M) q q S S := by
      rw [harmonicMapFlowWeakForm_self]
      unfold tensorL2Inner
      dsimp only [D]
      ring

omit [BoundarylessManifold I M] in
theorem harmonicMapFlowForm_self_rev
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
    (1 - δ / (1 - δ)) * harmonicMapFlowWeakForm (I := I) (M := M) q q S S ≤
      C.toReal * harmonicMapFlowWeakForm (I := I) (M := M) q h S S := by
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
        harmonicMapFlowWeakForm (I := I) (M := M) q h S S := by
    unfold harmonicMapFlowWeakForm
    rw [← MeasureTheory.integral_const_mul]
    exact MeasureTheory.integral_mono
      ((hmf_inner_int (I := I) (M := M) q h D D).const_mul
        (1 - δ / (1 - δ)))
      (hmf_inner_int (I := I) (M := M) q h
        (harmonicMapFlowFlux (I := I) (M := M) q h S) D)
      (fun x => harmonicMapFlowFlux_diag_ge (I := I) (M := M)
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
  rw [harmonicMapFlowWeakForm_self]
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
    _ ≤ C.toReal * harmonicMapFlowWeakForm (I := I) (M := M) q h S S :=
      mul_le_mul_of_nonneg_left hpt ENNReal.toReal_nonneg

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
  [BoundarylessManifold I M] in
theorem harmonicMapFlowVolumeEquiv
    (q : SmoothRiemannianMetric I M)
    (h : ℝ → SmoothRiemannianMetric I M) {a b c : ℝ} (hcb : c < b)
    (hcont : ∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)), ContinuousOn
      (fun p : ℝ × M =>
        DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (I := I) (h p.1) x₀ p.2 i j)
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

noncomputable def harmonicMapFlowMassH1
    (q h : SmoothRiemannianMetric I M)
    (S T : SmoothCcTensorH1 q 0 1) : ℝ :=
  harmonicMapFlowMass (I := I) (M := M) q h S.toCcTensor T.toCcTensor

noncomputable def harmonicMapFlowFormH1
    (q h : SmoothRiemannianMetric I M)
    (S T : SmoothCcTensorH1 q 0 1) : ℝ :=
  harmonicMapFlowWeakForm (I := I) (M := M) q h S.toCcTensor T.toCcTensor

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [CompactSpace M]
  [BoundarylessManifold I M] in
private theorem harmonicMapFlowMassH1_add_left
    (q h : SmoothRiemannianMetric I M)
    (S₁ S₂ T : SmoothCcTensorH1 q 0 1) :
    harmonicMapFlowMassH1 (I := I) (M := M) q h (S₁ + S₂) T =
      harmonicMapFlowMassH1 (I := I) (M := M) q h S₁ T +
        harmonicMapFlowMassH1 (I := I) (M := M) q h S₂ T := by
  simp only [harmonicMapFlowMassH1, SmoothCcTensorH1.toCcTensor_add]
  exact harmonicMapFlowMass_add_left (I := I) (M := M) q h _ _ _

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [CompactSpace M]
  [BoundarylessManifold I M] in
private theorem harmonicMapFlowMassH1_smul_left
    (q h : SmoothRiemannianMetric I M) (c : ℝ)
    (S T : SmoothCcTensorH1 q 0 1) :
    harmonicMapFlowMassH1 (I := I) (M := M) q h (c • S) T =
      c * harmonicMapFlowMassH1 (I := I) (M := M) q h S T := by
  simp only [harmonicMapFlowMassH1, SmoothCcTensorH1.toCcTensor_smul]
  exact harmonicMapFlowMass_smul_left (I := I) (M := M) q h c _ _

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [CompactSpace M]
  [BoundarylessManifold I M] in
private theorem harmonicMapFlowMassH1_symm
    (q h : SmoothRiemannianMetric I M) (S T : SmoothCcTensorH1 q 0 1) :
    harmonicMapFlowMassH1 (I := I) (M := M) q h S T =
      harmonicMapFlowMassH1 (I := I) (M := M) q h T S :=
  harmonicMapFlowMass_symm (I := I) (M := M) q h _ _

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [CompactSpace M]
  [BoundarylessManifold I M] in
private theorem harmonicMapFlowMassH1_add_right
    (q h : SmoothRiemannianMetric I M)
    (S T₁ T₂ : SmoothCcTensorH1 q 0 1) :
    harmonicMapFlowMassH1 (I := I) (M := M) q h S (T₁ + T₂) =
      harmonicMapFlowMassH1 (I := I) (M := M) q h S T₁ +
        harmonicMapFlowMassH1 (I := I) (M := M) q h S T₂ := by
  simp only [harmonicMapFlowMassH1, SmoothCcTensorH1.toCcTensor_add]
  exact harmonicMapFlowMass_add_right (I := I) (M := M) q h _ _ _

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [CompactSpace M]
  [BoundarylessManifold I M] in
private theorem harmonicMapFlowMassH1_smul_right
    (q h : SmoothRiemannianMetric I M) (c : ℝ)
    (S T : SmoothCcTensorH1 q 0 1) :
    harmonicMapFlowMassH1 (I := I) (M := M) q h S (c • T) =
      c * harmonicMapFlowMassH1 (I := I) (M := M) q h S T := by
  simp only [harmonicMapFlowMassH1, SmoothCcTensorH1.toCcTensor_smul]
  exact harmonicMapFlowMass_smul_right (I := I) (M := M) q h c _ _

omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
private theorem harmonicMapFlowFormH1_add_left
    (q h : SmoothRiemannianMetric I M)
    (S₁ S₂ T : SmoothCcTensorH1 q 0 1) :
    harmonicMapFlowFormH1 (I := I) (M := M) q h (S₁ + S₂) T =
      harmonicMapFlowFormH1 (I := I) (M := M) q h S₁ T +
        harmonicMapFlowFormH1 (I := I) (M := M) q h S₂ T := by
  simp only [harmonicMapFlowFormH1, SmoothCcTensorH1.toCcTensor_add]
  exact harmonicMapFlowWeak_add_left (I := I) (M := M) q h _ _ _

omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
private theorem harmonicMapFlowFormH1_smul_left
    (q h : SmoothRiemannianMetric I M) (c : ℝ)
    (S T : SmoothCcTensorH1 q 0 1) :
    harmonicMapFlowFormH1 (I := I) (M := M) q h (c • S) T =
      c * harmonicMapFlowFormH1 (I := I) (M := M) q h S T := by
  simp only [harmonicMapFlowFormH1, SmoothCcTensorH1.toCcTensor_smul]
  exact harmonicMapFlowWeak_smul_left (I := I) (M := M) q h c _ _

omit [BoundarylessManifold I M] in
private theorem harmonicMapFlowFormH1_symm
    (q h : SmoothRiemannianMetric I M) (S T : SmoothCcTensorH1 q 0 1) :
    harmonicMapFlowFormH1 (I := I) (M := M) q h S T =
      harmonicMapFlowFormH1 (I := I) (M := M) q h T S :=
  harmonicMapFlowWeak_symm (I := I) (M := M) q h _ _

omit [BoundarylessManifold I M] in
private theorem harmonicMapFlowFormH1_add_right
    (q h : SmoothRiemannianMetric I M)
    (S T₁ T₂ : SmoothCcTensorH1 q 0 1) :
    harmonicMapFlowFormH1 (I := I) (M := M) q h S (T₁ + T₂) =
      harmonicMapFlowFormH1 (I := I) (M := M) q h S T₁ +
        harmonicMapFlowFormH1 (I := I) (M := M) q h S T₂ := by
  simp only [harmonicMapFlowFormH1, SmoothCcTensorH1.toCcTensor_add]
  exact harmonicMapFlowWeak_add_right (I := I) (M := M) q h _ _ _

omit [BoundarylessManifold I M] in
private theorem harmonicMapFlowFormH1_smul_right
    (q h : SmoothRiemannianMetric I M) (c : ℝ)
    (S T : SmoothCcTensorH1 q 0 1) :
    harmonicMapFlowFormH1 (I := I) (M := M) q h S (c • T) =
      c * harmonicMapFlowFormH1 (I := I) (M := M) q h S T := by
  simp only [harmonicMapFlowFormH1, SmoothCcTensorH1.toCcTensor_smul]
  exact harmonicMapFlowWeak_smul_right (I := I) (M := M) q h c _ _

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [CompactSpace M]
  [BoundarylessManifold I M] in
theorem harmonicMapFlowMassH1_nonneg
    (q h : SmoothRiemannianMetric I M) (S : SmoothCcTensorH1 q 0 1) :
    0 ≤ harmonicMapFlowMassH1 (I := I) (M := M) q h S S :=
  harmonicMapFlowMass_nonneg (I := I) (M := M) q h S.toCcTensor

omit [BoundarylessManifold I M] in
theorem harmonicMapFlowFormH1_nonneg
    (q h : SmoothRiemannianMetric I M)
    (k : ∀ y : M, TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ)
    (htie : ∀ (y : M) (v w : TangentSpace I y),
      h.inner y v w = q.inner y v w + k y v w)
    {δ : ℝ} (hδ_half : δ < 1 / 2) (hδ_nn : 0 ≤ δ)
    (hδ : metricCauchySchwarzBound (I := I) (M := M) q k δ)
    (S : SmoothCcTensorH1 q 0 1) :
    0 ≤ harmonicMapFlowFormH1 (I := I) (M := M) q h S S :=
  harmonicMapFlowWeak_nonneg (I := I) (M := M)
    q h k htie hδ_half hδ_nn hδ S.toCcTensor

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M]
  [BoundarylessManifold I M] in
theorem harmonicMapFlowMassH1_diag_le
    (q h : SmoothRiemannianMetric I M) (C : ℝ≥0∞)
    (hC0 : C ≠ 0) (hCtop : C ≠ ⊤)
    (hvol : riemannianVolumeMeasure (I := I) (M := M) h ≤
      C • riemannianVolumeMeasure (I := I) (M := M) q)
    (S : SmoothCcTensorH1 q 0 1) :
    harmonicMapFlowMassH1 (I := I) (M := M) q h S S ≤ C.toReal * ‖S‖ ^ 2 := by
  calc
    harmonicMapFlowMassH1 (I := I) (M := M) q h S S ≤
        C.toReal * harmonicMapFlowMass (I := I) (M := M) q q S.toCcTensor S.toCcTensor :=
      harmonicMapFlowMass_self_le (I := I) (M := M) q h C hC0 hCtop hvol S.toCcTensor
    _ = C.toReal * ‖S.toCcTensor‖ ^ 2 := by
      rw [harmonicMapFlowMass_self,
        ← SmoothCcTensor.norm_sq_eq_inner_self (I := I) (M := M)]
    _ ≤ C.toReal * ‖S‖ ^ 2 :=
      mul_le_mul_of_nonneg_left
        (SmoothCcTensorH1.l2NormSq_le_h1NormSq (I := I) (M := M) S)
        ENNReal.toReal_nonneg

omit [BoundarylessManifold I M] in
theorem harmonicMapFlowFormH1_diag_le
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
    harmonicMapFlowFormH1 (I := I) (M := M) q h S S ≤
      (C.toReal * (1 + δ / (1 - δ))) * ‖S‖ ^ 2 := by
  have hden : 0 < 1 - δ := sub_pos.mpr hδ_lt
  have hcoef : 0 ≤ C.toReal * (1 + δ / (1 - δ)) := by
    exact mul_nonneg ENNReal.toReal_nonneg
      (by have := div_nonneg hδ_nn hden.le; linarith)
  have hfrozen :
      harmonicMapFlowWeakForm (I := I) (M := M) q q S.toCcTensor S.toCcTensor ≤ ‖S‖ ^ 2 := by
    rw [SmoothCcTensorH1.norm_sq_eq_inner_self,
      ← harmonicMapFlowH1_self (I := I) (M := M) q S.toCcTensor S.toCcTensor]
    exact le_add_of_nonneg_left
      (harmonicMapFlowMass_nonneg (I := I) (M := M) q q S.toCcTensor)
  exact (harmonicMapFlowForm_self_le (I := I) (M := M)
    q h C hC0 hCtop hvol k htie hδ_lt hδ_nn hδ S.toCcTensor).trans
      (mul_le_mul_of_nonneg_left hfrozen hcoef)

omit [BoundarylessManifold I M] in
theorem harmonicMapFlowH1_coercive
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
      C.toReal * (harmonicMapFlowMassH1 (I := I) (M := M) q h S S +
        harmonicMapFlowFormH1 (I := I) (M := M) q h S S) := by
  let α : ℝ := 1 - δ / (1 - δ)
  have hδ_lt : δ < 1 := lt_trans hδ_half (by norm_num)
  have hden : 0 < 1 - δ := sub_pos.mpr hδ_lt
  have hfrac0 : 0 ≤ δ / (1 - δ) := div_nonneg hδ_nn hden.le
  have hfrac1 : δ / (1 - δ) < 1 := (div_lt_one hden).2 (by linarith)
  have hα0 : 0 ≤ α := by dsimp [α]; linarith
  have hα1 : α ≤ 1 := by dsimp [α]; linarith
  have hmassq0 : 0 ≤ harmonicMapFlowMass (I := I) (M := M) q q
      S.toCcTensor S.toCcTensor :=
    harmonicMapFlowMass_nonneg (I := I) (M := M) q q S.toCcTensor
  have hmasspart :
      α * harmonicMapFlowMass (I := I) (M := M) q q S.toCcTensor S.toCcTensor ≤
        C.toReal * harmonicMapFlowMassH1 (I := I) (M := M) q h S S := by
    exact (mul_le_of_le_one_left hmassq0 hα1).trans
      (harmonicMapFlowMass_self_rev (I := I) (M := M)
        q h C hC0 hCtop hvol S.toCcTensor)
  have hformpart :
      α * harmonicMapFlowWeakForm (I := I) (M := M) q q S.toCcTensor S.toCcTensor ≤
        C.toReal * harmonicMapFlowFormH1 (I := I) (M := M) q h S S := by
    simpa only [α, harmonicMapFlowFormH1] using
      (harmonicMapFlowForm_self_rev (I := I) (M := M)
        q h C hC0 hCtop hvol k htie hδ_half hδ_nn hδ S.toCcTensor)
  have hH1 : ‖S‖ ^ 2 =
      harmonicMapFlowMass (I := I) (M := M) q q S.toCcTensor S.toCcTensor +
        harmonicMapFlowWeakForm (I := I) (M := M) q q S.toCcTensor S.toCcTensor :=
    (SmoothCcTensorH1.norm_sq_eq_inner_self (I := I) (M := M) S).trans
      (harmonicMapFlowH1_self (I := I) (M := M) q S.toCcTensor S.toCcTensor).symm
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

noncomputable def harmonicMapFlowMassSmooth
    (q h : SmoothRiemannianMetric I M) (C : ℝ≥0∞)
    (hC0 : C ≠ 0) (hCtop : C ≠ ⊤)
    (hvol : riemannianVolumeMeasure (I := I) (M := M) h ≤
      C • riemannianVolumeMeasure (I := I) (M := M) q) :
    SmoothCcTensorH1 q 0 1 →L[ℝ] SmoothCcTensorH1 q 0 1 →L[ℝ] ℝ := by
  refine LinearMap.mkContinuous₂
    (LinearMap.mk₂ ℝ (harmonicMapFlowMassH1 (I := I) (M := M) q h)
      (harmonicMapFlowMassH1_add_left (I := I) (M := M) q h)
      (harmonicMapFlowMassH1_smul_left (I := I) (M := M) q h)
      (harmonicMapFlowMassH1_add_right (I := I) (M := M) q h)
      (harmonicMapFlowMassH1_smul_right (I := I) (M := M) q h))
    C.toReal ?_
  intro S T
  rw [Real.norm_eq_abs]
  exact bilin_abs_le (harmonicMapFlowMassH1 (I := I) (M := M) q h)
    (harmonicMapFlowMassH1_add_left (I := I) (M := M) q h)
    (harmonicMapFlowMassH1_smul_left (I := I) (M := M) q h)
    (harmonicMapFlowMassH1_symm (I := I) (M := M) q h)
    (harmonicMapFlowMassH1_nonneg (I := I) (M := M) q h)
    ENNReal.toReal_nonneg
    (harmonicMapFlowMassH1_diag_le (I := I) (M := M) q h C hC0 hCtop hvol) S T

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M]
  [BoundarylessManifold I M] in
@[simp] theorem harmonicMapFlowMassSm_apply
    (q h : SmoothRiemannianMetric I M) (C : ℝ≥0∞)
    (hC0 : C ≠ 0) (hCtop : C ≠ ⊤)
    (hvol : riemannianVolumeMeasure (I := I) (M := M) h ≤
      C • riemannianVolumeMeasure (I := I) (M := M) q)
    (S T : SmoothCcTensorH1 q 0 1) :
    harmonicMapFlowMassSmooth (I := I) (M := M) q h C hC0 hCtop hvol S T =
      harmonicMapFlowMassH1 (I := I) (M := M) q h S T := rfl

noncomputable def harmonicMapFlowFormSmooth
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
    (LinearMap.mk₂ ℝ (harmonicMapFlowFormH1 (I := I) (M := M) q h)
      (harmonicMapFlowFormH1_add_left (I := I) (M := M) q h)
      (harmonicMapFlowFormH1_smul_left (I := I) (M := M) q h)
      (harmonicMapFlowFormH1_add_right (I := I) (M := M) q h)
      (harmonicMapFlowFormH1_smul_right (I := I) (M := M) q h))
    (C.toReal * (1 + δ / (1 - δ))) ?_
  intro S T
  rw [Real.norm_eq_abs]
  exact bilin_abs_le (harmonicMapFlowFormH1 (I := I) (M := M) q h)
    (harmonicMapFlowFormH1_add_left (I := I) (M := M) q h)
    (harmonicMapFlowFormH1_smul_left (I := I) (M := M) q h)
    (harmonicMapFlowFormH1_symm (I := I) (M := M) q h)
    (harmonicMapFlowFormH1_nonneg (I := I) (M := M)
      q h k htie hδ_half hδ_nn hδ) hK
    (harmonicMapFlowFormH1_diag_le (I := I) (M := M)
      q h C hC0 hCtop hvol k htie hδ_lt hδ_nn hδ) S T

omit [BoundarylessManifold I M] in
@[simp] theorem harmonicMapFlowFormSm_apply
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
    harmonicMapFlowFormSmooth (I := I) (M := M) q h C hC0 hCtop hvol
        k htie hδ_half hδ_nn hδ S T =
      harmonicMapFlowFormH1 (I := I) (M := M) q h S T := rfl

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

private noncomputable def harmonicMapFlowExtend
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
private theorem harmonicMapFlowExtend_coe
    (q : SmoothRiemannianMetric I M)
    (F : SmoothCcTensorH1 q 0 1 →L[ℝ]
      SmoothCcTensorH1 q 0 1 →L[ℝ] ℝ)
    (S T : SmoothCcTensorH1 q 0 1) :
    harmonicMapFlowExtend (I := I) (M := M) q F
        (smoothToTensorH1Compl (I := I) (M := M) q 0 1 S)
        (smoothToTensorH1Compl (I := I) (M := M) q 0 1 T) = F S T := by
  unfold harmonicMapFlowExtend
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

noncomputable def harmonicMapFlowMassCompl
    (q h : SmoothRiemannianMetric I M) (C : ℝ≥0∞)
    (hC0 : C ≠ 0) (hCtop : C ≠ ⊤)
    (hvol : riemannianVolumeMeasure (I := I) (M := M) h ≤
      C • riemannianVolumeMeasure (I := I) (M := M) q) :
    TensorH1Compl q 0 1 →L[ℝ] TensorH1Compl q 0 1 →L[ℝ] ℝ :=
  harmonicMapFlowExtend (I := I) (M := M) q
    (harmonicMapFlowMassSmooth (I := I) (M := M) q h C hC0 hCtop hvol)

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M]
  [BoundarylessManifold I M] in
theorem harmonicMapFlowMassCompl_coe
    (q h : SmoothRiemannianMetric I M) (C : ℝ≥0∞)
    (hC0 : C ≠ 0) (hCtop : C ≠ ⊤)
    (hvol : riemannianVolumeMeasure (I := I) (M := M) h ≤
      C • riemannianVolumeMeasure (I := I) (M := M) q)
    (S T : SmoothCcTensorH1 q 0 1) :
    harmonicMapFlowMassCompl (I := I) (M := M) q h C hC0 hCtop hvol
        (smoothToTensorH1Compl (I := I) (M := M) q 0 1 S)
        (smoothToTensorH1Compl (I := I) (M := M) q 0 1 T) =
      harmonicMapFlowMassH1 (I := I) (M := M) q h S T := by
  rw [harmonicMapFlowMassCompl, harmonicMapFlowExtend_coe, harmonicMapFlowMassSm_apply]

noncomputable def harmonicMapFlowFormCompl
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
  harmonicMapFlowExtend (I := I) (M := M) q
    (harmonicMapFlowFormSmooth (I := I) (M := M) q h C hC0 hCtop hvol
      k htie hδ_half hδ_nn hδ)

omit [BoundarylessManifold I M] in
theorem harmonicMapFlowFormCompl_coe
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
    harmonicMapFlowFormCompl (I := I) (M := M) q h C hC0 hCtop hvol
        k htie hδ_half hδ_nn hδ
        (smoothToTensorH1Compl (I := I) (M := M) q 0 1 S)
        (smoothToTensorH1Compl (I := I) (M := M) q 0 1 T) =
      harmonicMapFlowFormH1 (I := I) (M := M) q h S T := by
  rw [harmonicMapFlowFormCompl, harmonicMapFlowExtend_coe, harmonicMapFlowFormSm_apply]

omit [BoundarylessManifold I M] in
theorem harmonicMapFlowCompl_coercive
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
        (harmonicMapFlowMassCompl (I := I) (M := M) q h C hC0 hCtop hvol.1 u u +
          harmonicMapFlowFormCompl (I := I) (M := M) q h C hC0 hCtop hvol.1
            k htie hδ_half hδ_nn hδ u u) := by
  let BM := harmonicMapFlowMassCompl (I := I) (M := M) q h C hC0 hCtop hvol.1
  let BF := harmonicMapFlowFormCompl (I := I) (M := M) q h C hC0 hCtop hvol.1
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
  rw [harmonicMapFlowMassCompl_coe, harmonicMapFlowFormCompl_coe, hnorm]
  exact harmonicMapFlowH1_coercive (I := I) (M := M)
    q h C hC0 hCtop hvol.2 k htie hδ_half hδ_nn hδ S

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
  [BoundarylessManifold I M] in
theorem harmonicMapFlowEdge_inputs
    (q : SmoothRiemannianMetric I M)
    (g : ℝ → SmoothRiemannianMetric I M) {a b : ℝ} (hab : a < b)
    (hcont : ∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)), ContinuousOn
      (fun p : ℝ × M => DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (I := I) (g p.1) x₀ p.2 i j)
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
  obtain ⟨T, hT, hTb, hop⟩ := metricDifference_smallC0
    (I := I) (M := M) (g := g) (q := q) (a := a) (b := b)
      (δ := (1 / 4 : ℝ)) hab hcont hga (by norm_num)
  obtain ⟨C, hC0, hCtop, hvol⟩ := harmonicMapFlowVolumeEquiv
    (I := I) (M := M) q g (c := a + T) hTb hcont
  exact ⟨T, C, hT, hTb, hC0, hCtop, fun t ht => ⟨hvol t ht, hop t ht⟩⟩

omit [BoundarylessManifold I M] in
theorem harmonicMapFlowEdge_coercive
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
      rw [metricDifference_symVal]
      ring
    (1 - (1 / 4 : ℝ) / (1 - (1 / 4 : ℝ))) * ‖u‖ ^ 2 ≤
      C.toReal *
        (harmonicMapFlowMassCompl (I := I) (M := M) q (g t) C hC0 hCtop
            (hvol t ht).1 u u +
          harmonicMapFlowFormCompl (I := I) (M := M) q (g t) C hC0 hCtop
            (hvol t ht).1 k htie (by norm_num) (by norm_num) (hop t ht) u u) := by
  dsimp only
  apply harmonicMapFlowCompl_coercive (I := I) (M := M)
    q (g t) C hC0 hCtop (hvol t ht)
    (ccTensorBilinSymm (I := I) q
      (metricDifferenceCcTensor (I := I) (M := M) q (g t)))
    (fun y v w => by rw [metricDifference_symVal]; ring)
    (δ := (1 / 4 : ℝ)) (by norm_num) (by norm_num) (hop t ht) u

end DifferentialGeometry.PDE.RicciFlow.Pullback

end
