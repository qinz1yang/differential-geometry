import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegularity.RicciDeTurckPairing.LowOrderDecomposition
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegularity.FirstOrderCoefficientLipschitzBounds
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegularity.RicciDeTurckPairing.CovariantDerivativeTerm

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
  (armSlotEndoCc_toSection armSlotFib armSlotFib_apply_eval metricConnectionDifferenceLoweredCoefficient
   rsDomDomCongrSection_toSection)
open DifferentialGeometry.Analysis.Sobolev.TensorHilbert
open DifferentialGeometry.Analysis.Spectral
  (operatorFieldApply operatorFieldApplication_add_left operatorFieldApplication_assoc operatorFieldApplication_smul_right operatorFieldApplication_toSection ccOperatorFieldComp operatorFieldComposition_smul_right
   operatorFieldComposition_sub_right operatorFieldComposition_toSection operatorFieldComposition_zero_eq_operatorFieldApply deTurckLieTopOrderPairingFamily metricComparisonEndomorphismField
   permCoeff pureTrace pureTrace_toSection rsDomDomCongr slotExtend slotExtend_sub slotExtendIter
   toModel_rsDomDomCongr_apply)
open DifferentialGeometry.Geometry.Connection
  (slotInsertEndoCc slotInsertEndoCc_add slotInsertEndoCc_smul unitZeroSec)
open DifferentialGeometry.Geometry.Curvature (slotInsertEndoFib_apply_eval)
open DifferentialGeometry.PDE.DeTurck.RicciLinearization
open DifferentialGeometry.Analysis.Spectral.DeTurck
open DifferentialGeometry.Analysis.Spectral.MetricRealization

namespace LieCorrectionZeroCore

private abbrev lieCorrectionZeroMixedConnectionPermutationCycleZeroOneFour :=
  DifferentialGeometry.Analysis.Spectral.LieCorrectionZeroCore.lieCorrectionZeroMixedConnectionPermutationCycleZeroOneFour

private abbrev lieCorrectionZeroMixedConnectionPermutationCycleZeroTwoThreeOne :=
  DifferentialGeometry.Analysis.Spectral.LieCorrectionZeroCore.lieCorrectionZeroMixedConnectionPermutationCycleZeroTwoThreeOne

private abbrev lieCorrectionZeroMixedConnectionPermutationCycleZeroTwoOne :=
  DifferentialGeometry.Analysis.Spectral.LieCorrectionZeroCore.lieCorrectionZeroMixedConnectionPermutationCycleZeroTwoOne

private abbrev lieCorrectionZeroVectorBundleTracePermutation :=
  DifferentialGeometry.Analysis.Spectral.LieCorrectionZeroCore.lieCorrectionZeroVectorBundleTracePermutation

end LieCorrectionZeroCore

variable
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
      [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

namespace RicciDeTurckPairing

abbrev JointlySmoothCcTensorFamily
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (S : Set ℝ)
    (A : ℝ → SmoothCcTensor g r s) : Prop :=
  ContMDiffOn (I.prod 𝓘(ℝ, ℝ))
    (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
    (fun p : M × ℝ => TotalSpace.mk' (TensorRSModel r s ℝ E)
      (E := fun x : M => TensorRSSpace r s I x) p.1
      ((A p.2).toSection p.1))
    ((Set.univ : Set M) ×ˢ S)

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless]
    [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
theorem jointlySmoothCcTensorFamily_const
    (g : SmoothRiemannianMetric I M) {r s : ℕ} {S : Set ℝ}
    (A : SmoothCcTensor g r s) :
    JointlySmoothCcTensorFamily (I := I) g r s S (fun _ => A) := by
  exact (A.toSection.contMDiff.comp_contMDiffOn contMDiffOn_fst).mono
    (Set.subset_univ _)

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] [SigmaCompactSpace M] in
theorem jointlySmoothCcTensorFamily_ccOperatorFieldComp
    (g : SmoothRiemannianMetric I M) {a b c : ℕ} {S : Set ℝ}
    {A : ℝ → SmoothCcTensor g b c} {B : ℝ → SmoothCcTensor g a b}
    (hA : JointlySmoothCcTensorFamily (I := I) g b c S A)
    (hB : JointlySmoothCcTensorFamily (I := I) g a b S B) :
    JointlySmoothCcTensorFamily (I := I) g a c S
      (fun t => ccOperatorFieldComp (I := I) (M := M) g a b c (A t) (B t)) := by
  apply contMDiffOn_clm_section_of_pointwise_jointMR (I := I) (M := M)
    (F₁ := Tensor0SModel a ℝ E) (V₁ := fun x : M => Tensor0SSpace a I x)
    (F₂ := Tensor0SModel c ℝ E) (V₂ := fun x : M => Tensor0SSpace c I x)
    (φ := fun p : M × ℝ =>
      (show Tensor0SSpace a I p.1 →L[ℝ] Tensor0SSpace c I p.1 from
        (ccOperatorFieldComp (I := I) (M := M) g a b c
          (A p.2) (B p.2)).toSection p.1))
    (S := S)
  intro Y
  have hY : ContMDiffOn (I.prod 𝓘(ℝ, ℝ))
      (I.prod 𝓘(ℝ, Tensor0SModel a ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SModel a ℝ E)
        (E := fun x : M => Tensor0SSpace a I x) p.1 (Y p.1))
      ((Set.univ : Set M) ×ˢ S) :=
    Y.contMDiff.comp_contMDiffOn contMDiffOn_fst
  have hBY := ContMDiffOn.clm_bundle_apply (b := Prod.fst) hB hY
  have hABY := ContMDiffOn.clm_bundle_apply (b := Prod.fst) hA hBY
  refine hABY.congr (fun p _ => ?_)
  refine congrArg (fun z => TotalSpace.mk' (Tensor0SModel c ℝ E)
    (E := fun x : M => Tensor0SSpace c I x) p.1 z) ?_
  rw [operatorFieldComposition_toSection]
  rfl

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless]
    [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
theorem jointlySmoothCcTensorFamily_parameter_smul
    (g : SmoothRiemannianMetric I M) {r s : ℕ} {S : Set ℝ}
    {A : ℝ → SmoothCcTensor g r s}
    (hA : JointlySmoothCcTensorFamily (I := I) g r s S A) :
    JointlySmoothCcTensorFamily (I := I) g r s S (fun t => t • A t) := by
  letI := tensorRSBundle_topology (𝕜 := ℝ) (E := E) (H := H)
    (I := I) (M := M) r s
  intro p hp
  rw [Bundle.contMDiffWithinAt_totalSpace]
  refine ⟨contMDiffWithinAt_fst, ?_⟩
  set x := p.1 with hx
  set e := trivializationAt (TensorRSModel r s ℝ E)
    (fun z : M => TensorRSSpace r s I z) x with he
  have hA' := (Bundle.contMDiffWithinAt_totalSpace
    (F := TensorRSModel r s ℝ E)
    (E := fun z : M => TensorRSSpace r s I z)).mp (hA p hp)
  refine (contMDiffWithinAt_snd.smul hA'.2).congr_of_eventuallyEq ?_ ?_
  · have hbase : ∀ᶠ q : M × ℝ in
        nhdsWithin p ((Set.univ : Set M) ×ˢ S), q.1 ∈ e.baseSet :=
      (continuousWithinAt_fst
        (s := (Set.univ : Set M) ×ˢ S) (p := p))
        (e.open_baseSet.mem_nhds (by
          rw [he]
          exact mem_baseSet_trivializationAt _ _ x))
    filter_upwards [hbase] with q hq
    exact (e.linear ℝ hq).map_smul q.2 ((A q.2).toSection q.1)
  · exact (e.linear ℝ (by
      rw [he, ← hx]
      exact mem_baseSet_trivializationAt _ _ x)).map_smul
        p.2 ((A p.2).toSection p.1)

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless]
    [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
theorem jointlySmoothCcTensorFamily_add
    (g : SmoothRiemannianMetric I M) {r s : ℕ} {S : Set ℝ}
    {A B : ℝ → SmoothCcTensor g r s}
    (hA : JointlySmoothCcTensorFamily (I := I) g r s S A)
    (hB : JointlySmoothCcTensorFamily (I := I) g r s S B) :
    JointlySmoothCcTensorFamily (I := I) g r s S (fun t => A t + B t) := by
  have h := joint_rs_add (I := I) (r := r) (s := s) (S := S)
    (fun p : M × ℝ => (A p.2).toSection p.1)
    (fun p : M × ℝ => (B p.2).toSection p.1) hA hB
  refine h.congr (fun p _ => ?_)
  refine congrArg (fun z => TotalSpace.mk' (TensorRSModel r s ℝ E)
    (E := fun x : M => TensorRSSpace r s I x) p.1 z) ?_
  rw [SmoothCcTensor.toSection_add, ContMDiffSection.coe_add, Pi.add_apply]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless]
    [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
theorem jointlySmoothCcTensorFamily_sub
    (g : SmoothRiemannianMetric I M) {r s : ℕ} {S : Set ℝ}
    {A B : ℝ → SmoothCcTensor g r s}
    (hA : JointlySmoothCcTensorFamily (I := I) g r s S A)
    (hB : JointlySmoothCcTensorFamily (I := I) g r s S B) :
    JointlySmoothCcTensorFamily (I := I) g r s S (fun t => A t - B t) := by
  have h := joint_rs_sub (I := I) (r := r) (s := s) (S := S)
    (fun p : M × ℝ => (A p.2).toSection p.1)
    (fun p : M × ℝ => (B p.2).toSection p.1) hA hB
  refine h.congr (fun p _ => ?_)
  refine congrArg (fun z => TotalSpace.mk' (TensorRSModel r s ℝ E)
    (E := fun x : M => TensorRSSpace r s I x) p.1 z) ?_
  rw [SmoothCcTensor.toSection_sub, ContMDiffSection.coe_sub, Pi.sub_apply]

def smoothCcTensorOfCovariantSection
    (g : SmoothRiemannianMetric I M) {s : ℕ}
    (Y : Cₛ^∞⟮I; Tensor0SModel s ℝ E,
      (fun x : M => Tensor0SSpace s I x)⟯) :
    SmoothCcTensor g 0 s where
  toSection :=
    MixedSection.fromMultilinearSection
      (𝕜 := ℝ) (F := E) (IB := I)
      (E := (TangentSpace I : M → Type _)) ∞ Y
  hasCompactSupport := HasCompactSupport.of_compactSpace _

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
    [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
theorem smoothCcTensorOfCovariantSection_apply_unitTensor
    (g : SmoothRiemannianMetric I M) {s : ℕ}
    (Y : Cₛ^∞⟮I; Tensor0SModel s ℝ E,
      (fun x : M => Tensor0SSpace s I x)⟯) (x : M) :
    (smoothCcTensorOfCovariantSection (I := I) (M := M) g Y).toSection x
        (unitTensor (I := I) (M := M) x) = Y x := by
  have h := congrArg (fun Z => Z x)
    (MixedSection.toMultilinearSection_fromMultilinearSection
      (𝕜 := ℝ) (F := E) (IB := I)
      (E := (TangentSpace I : M → Type _)) ∞ Y)
  simpa only [smoothCcTensorOfCovariantSection, MixedSection.toMultilinearSection,
    unitTensor, Tensor0SSpace.ofModel] using h

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] [SigmaCompactSpace M] in
theorem jointlySmoothCcTensorFamily_slotExtendIter_two
    (g : SmoothRiemannianMetric I M) {S : Set ℝ}
    {K : ℝ → SmoothCcTensor g 0 4}
    (hK : JointlySmoothCcTensorFamily (I := I) g 0 4 S K) :
    JointlySmoothCcTensorFamily (I := I) g 2 6 S
      (fun t => slotExtendIter (I := I) (M := M) g 0 4 2 (K t)) := by
  apply contMDiffOn_clm_section_of_pointwise_jointMR (I := I) (M := M)
    (F₁ := Tensor0SModel 2 ℝ E) (V₁ := fun x : M => Tensor0SSpace 2 I x)
    (F₂ := Tensor0SModel 6 ℝ E) (V₂ := fun x : M => Tensor0SSpace 6 I x)
    (φ := fun q : M × ℝ =>
      (slotExtendIter (I := I) (M := M) g 0 4 2 (K q.2)).toSection q.1)
    (S := S)
  intro Y
  have hY : ContMDiffOn (I.prod 𝓘(ℝ, ℝ))
      (I.prod 𝓘(ℝ, Tensor0SModel 2 ℝ E)) ∞
      (fun q : M × ℝ => TotalSpace.mk' (Tensor0SModel 2 ℝ E)
        (E := fun x : M => Tensor0SSpace 2 I x) q.1 (Y q.1))
      ((Set.univ : Set M) ×ˢ S) :=
    Y.contMDiff.comp_contMDiffOn contMDiffOn_fst
  have hunit : ContMDiffOn (I.prod 𝓘(ℝ, ℝ))
      (I.prod 𝓘(ℝ, Tensor0SModel 0 ℝ E)) ∞
      (fun q : M × ℝ => TotalSpace.mk' (Tensor0SModel 0 ℝ E)
        (E := fun x : M => Tensor0SSpace 0 I x) q.1
        (unitZeroSec (I := I) (M := M) q.1))
      ((Set.univ : Set M) ×ˢ S) :=
    (unitZeroSec (I := I) (M := M)).contMDiff.comp_contMDiffOn
      contMDiffOn_fst
  have hKval := ContMDiffOn.clm_bundle_apply (b := Prod.fst) hK hunit
  have hprod := jointTensor0SProd_local (I := I) (p := 2) (q := 4)
    (S := S) (fun q : M × ℝ => Y q.1)
    (fun q : M × ℝ =>
      (show Tensor0SSpace 0 I q.1 →L[ℝ] Tensor0SSpace 4 I q.1 from
        (K q.2).toSection q.1) (unitTensor (I := I) (M := M) q.1))
    hY hKval
  have hprod' : ContMDiffOn (I.prod 𝓘(ℝ, ℝ))
      (I.prod 𝓘(ℝ, Tensor0SModel 6 ℝ E)) ∞
      (fun q : M × ℝ => TotalSpace.mk' (Tensor0SModel 6 ℝ E)
        (E := fun x : M => Tensor0SSpace 6 I x) q.1
        (tensor0SProdKappaFib (I := I) (p := 2) (q := 4) q.1
          ((show Tensor0SSpace 0 I q.1 →L[ℝ] Tensor0SSpace 4 I q.1 from
            (K q.2).toSection q.1) (unitTensor (I := I) (M := M) q.1))
          (Y q.1)))
      ((Set.univ : Set M) ×ˢ S) := by
    refine hprod.congr (fun q _ => ?_)
    refine congrArg (fun z => TotalSpace.mk' (Tensor0SModel 6 ℝ E)
      (E := fun x : M => Tensor0SSpace 6 I x) q.1 z) ?_
    rw [tensor0SProdKappaFib_apply]
  refine hprod'.congr (fun q _ => ?_)
  refine congrArg (fun z => TotalSpace.mk' (Tensor0SModel 6 ℝ E)
    (E := fun x : M => Tensor0SSpace 6 I x) q.1 z) ?_
  exact slotExtendIter_two_zero_four_apply (I := I) (M := M) g (K q.2) q.1 (Y q.1)

theorem connectionDifferenceContravariantInsertionField_metricPerturbationPath_jointlySmooth
    (g : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2)
    {δ : ℝ}
    (hδ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) δ)
    (hδZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g
        (0 : SmoothCcTensor g 0 2)) δ) :
    JointlySmoothCcTensorFamily (I := I) g 3 4
      (metricPerturbationPathDomain (δ := δ) (δ' := δ))
      (fun t => connectionDifferenceContravariantInsertionField (I := I) g
        (metricPerturbationPath (I := I) g T 0 hδ hδZ t)) := by
  have h := connIns_joint (I := I) g T 0 hδ hδZ
  simpa only [connectionDifferenceContravariantInsertionField_toSection] using h

theorem ricciCometricFourTraceCastG0_metricPerturbationPath_jointlySmooth
    (g : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2)
    {δ : ℝ}
    (hδ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) δ)
    (hδZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g
        (0 : SmoothCcTensor g 0 2)) δ) :
    JointlySmoothCcTensorFamily (I := I) g 4 2
      (metricPerturbationPathDomain (δ := δ) (δ' := δ))
      (fun t => ricciCometricFourTraceCastG0 (I := I) g
        (metricPerturbationPath (I := I) g T 0 hδ hδZ t)) := by
  apply contMDiffOn_clm_section_of_pointwise_jointMR (I := I) (M := M)
    (F₁ := Tensor0SModel 4 ℝ E) (V₁ := fun x : M => Tensor0SSpace 4 I x)
    (F₂ := Tensor0SModel 2 ℝ E) (V₂ := fun x : M => Tensor0SSpace 2 I x)
    (φ := fun p : M × ℝ =>
      (ricciCometricFourTraceCastG0 (I := I) g
        (metricPerturbationPath (I := I) g T 0 hδ hδZ p.2)).toSection p.1)
    (S := metricPerturbationPathDomain (δ := δ) (δ' := δ))
  intro Y
  have hY : ContMDiffOn (I.prod 𝓘(ℝ, ℝ))
      (I.prod 𝓘(ℝ, Tensor0SModel 4 ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SModel 4 ℝ E)
        (E := fun x : M => Tensor0SSpace 4 I x) p.1 (Y p.1))
      ((Set.univ : Set M) ×ˢ metricPerturbationPathDomain (δ := δ) (δ' := δ)) :=
    Y.contMDiff.comp_contMDiffOn contMDiffOn_fst
  have h := fourTrace_joint (I := I) g T 0 hδ hδZ
    (fun p : M × ℝ => Y p.1) hY
  refine h.congr (fun p _ => ?_)
  refine congrArg (fun z => TotalSpace.mk' (Tensor0SModel 2 ℝ E)
    (E := fun x : M => Tensor0SSpace 2 I x) p.1 z) ?_
  rw [ricciCometricFourTraceCastG0_toSection]

theorem connectionDifferenceInsertionInnerActionCoefficient_metricPerturbationPath_jointlySmooth
    (g : SmoothRiemannianMetric I M) (T W : SmoothCcTensor g 0 2)
    {δ : ℝ}
    (hδ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) δ)
    (hδZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g
        (0 : SmoothCcTensor g 0 2)) δ) :
    JointlySmoothCcTensorFamily (I := I) g 3 3
      (metricPerturbationPathDomain (δ := δ) (δ' := δ))
      (fun t => connectionDifferenceInsertionInnerActionCoefficient (I := I) (M := M) g
        (metricPerturbationPath (I := I) g T 0 hδ hδZ t) W) := by
  have hA := jointlySmoothCcTensorFamily_const (I := I) (M := M) g
    (S := metricPerturbationPathDomain (δ := δ) (δ' := δ))
    (connectionDifferenceInsertionInnerDerivativeCoefficient (I := I) (M := M) g W)
  have hB := RicciDeTurckLowOrder.connectionDifferenceLowOrderOperator_joint
    (I := I) (M := M) g T hδ hδZ
  simpa only [connectionDifferenceInsertionInnerActionCoefficient] using jointlySmoothCcTensorFamily_ccOperatorFieldComp (I := I) (M := M) g hA hB

theorem ricciQuadraticKernelDerivativeNestedTerm_metricPerturbationPath_jointlySmooth
    (g : SmoothRiemannianMetric I M) (T W : SmoothCcTensor g 0 2)
    {δ : ℝ}
    (hδ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) δ)
    (hδZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g
        (0 : SmoothCcTensor g 0 2)) δ)
    (mid : Equiv.Perm (Fin 3)) (out : Equiv.Perm (Fin 4)) :
    JointlySmoothCcTensorFamily (I := I) g 3 4
      (metricPerturbationPathDomain (δ := δ) (δ' := δ))
      (fun t => ricciQuadraticKernelDerivativeNestedTerm (I := I) (M := M) g
        (metricPerturbationPath (I := I) g T 0 hδ hδZ t) W mid out) := by
  let S := metricPerturbationPathDomain (δ := δ) (δ' := δ)
  have hinner := connectionDifferenceInsertionInnerActionCoefficient_metricPerturbationPath_jointlySmooth (I := I) (M := M) g T W hδ hδZ
  have hmid := jointlySmoothCcTensorFamily_const (I := I) (M := M) g (S := S)
    (permCoeff (I := I) (M := M) g mid)
  have hconn := connectionDifferenceContravariantInsertionField_metricPerturbationPath_jointlySmooth (I := I) (M := M) g T hδ hδZ
  have hout := jointlySmoothCcTensorFamily_const (I := I) (M := M) g (S := S)
    (permCoeff (I := I) (M := M) g out)
  have h₁ := jointlySmoothCcTensorFamily_ccOperatorFieldComp (I := I) (M := M) g hmid hinner
  have h₂ := jointlySmoothCcTensorFamily_ccOperatorFieldComp (I := I) (M := M) g hconn h₁
  have h₃ := jointlySmoothCcTensorFamily_ccOperatorFieldComp (I := I) (M := M) g hout h₂
  simpa only [ricciQuadraticKernelDerivativeNestedTerm] using h₃

theorem ricciQuadraticKernelDerivativeBareTerm_metricPerturbationPath_jointlySmooth
    (g : SmoothRiemannianMetric I M) (T W : SmoothCcTensor g 0 2)
    {δ : ℝ}
    (hδ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) δ)
    (hδZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g
        (0 : SmoothCcTensor g 0 2)) δ)
    (out : Equiv.Perm (Fin 4)) :
    JointlySmoothCcTensorFamily (I := I) g 3 4
      (metricPerturbationPathDomain (δ := δ) (δ' := δ))
      (fun t => ricciQuadraticKernelDerivativeBareTerm (I := I) (M := M) g
        (metricPerturbationPath (I := I) g T 0 hδ hδZ t) W out) := by
  let S := metricPerturbationPathDomain (δ := δ) (δ' := δ)
  have hinner := connectionDifferenceInsertionInnerActionCoefficient_metricPerturbationPath_jointlySmooth (I := I) (M := M) g T W hδ hδZ
  have hconn := connectionDifferenceContravariantInsertionField_metricPerturbationPath_jointlySmooth (I := I) (M := M) g T hδ hδZ
  have hout := jointlySmoothCcTensorFamily_const (I := I) (M := M) g (S := S)
    (permCoeff (I := I) (M := M) g out)
  have h₁ := jointlySmoothCcTensorFamily_ccOperatorFieldComp (I := I) (M := M) g hconn hinner
  have h₂ := jointlySmoothCcTensorFamily_ccOperatorFieldComp (I := I) (M := M) g hout h₁
  simpa only [ricciQuadraticKernelDerivativeBareTerm] using h₂

theorem ricciConnectionDifferenceQuadraticDerivativeCoefficient_metricPerturbationPath_jointlySmooth
    (g : SmoothRiemannianMetric I M) (T W : SmoothCcTensor g 0 2)
    {δ : ℝ}
    (hδ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) δ)
    (hδZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g
        (0 : SmoothCcTensor g 0 2)) δ) :
    JointlySmoothCcTensorFamily (I := I) g 3 2
      (metricPerturbationPathDomain (δ := δ) (δ' := δ))
      (fun t => ricciConnectionDifferenceQuadraticDerivativeCoefficient (I := I) (M := M) g
        (metricPerturbationPath (I := I) g T 0 hδ hδZ t) W) := by
  let S := metricPerturbationPathDomain (δ := δ) (δ' := δ)
  have h₀ := ricciQuadraticKernelDerivativeNestedTerm_metricPerturbationPath_jointlySmooth (I := I) (M := M) g T W hδ hδZ
    ricciQuadraticPermutation_swapZeroOne ricciQuadraticPermutation_cycleZeroThreeOneTwo
  have h₁ := ricciQuadraticKernelDerivativeNestedTerm_metricPerturbationPath_jointlySmooth (I := I) (M := M) g T W hδ hδZ
    ricciQuadraticPermutation_swapZeroOne ricciQuadraticPermutation_swapBlocks
  have h₂ := ricciQuadraticKernelDerivativeNestedTerm_metricPerturbationPath_jointlySmooth (I := I) (M := M) g T W hδ hδZ
    ricciQuadraticPermutation_rotateInputs ricciQuadraticPermutation_cycleZeroThreeTwo
  have h₃ := ricciQuadraticKernelDerivativeBareTerm_metricPerturbationPath_jointlySmooth (I := I) (M := M) g T W hδ hδZ ricciQuadraticPermutation_cycleZeroOneThreeTwo
  have h₄ := ricciQuadraticKernelDerivativeBareTerm_metricPerturbationPath_jointlySmooth (I := I) (M := M) g T W hδ hδZ ricciQuadraticPermutation_cycleZeroOneTwo
  have h₅ := ricciQuadraticKernelDerivativeNestedTerm_metricPerturbationPath_jointlySmooth (I := I) (M := M) g T W hδ hδZ
    ricciQuadraticPermutation_rotateInputs ricciQuadraticPermutation_swapZeroTwo
  have hker := jointlySmoothCcTensorFamily_add (I := I) (M := M) g
    (jointlySmoothCcTensorFamily_add (I := I) (M := M) g
      (jointlySmoothCcTensorFamily_add (I := I) (M := M) g
        (jointlySmoothCcTensorFamily_add (I := I) (M := M) g
          (jointlySmoothCcTensorFamily_add (I := I) (M := M) g h₀ h₁) h₂) h₃) h₄) h₅
  have htrace := ricciCometricFourTraceCastG0_metricPerturbationPath_jointlySmooth (I := I) (M := M) g T hδ hδZ
  have hout := jointlySmoothCcTensorFamily_ccOperatorFieldComp (I := I) (M := M) g htrace hker
  simpa only [ricciConnectionDifferenceQuadraticDerivativeCoefficient, ricciQuadraticKernelDerivativeCoefficient] using hout

theorem reindexedPureTrace_metricPerturbationPath_jointlySmooth
    (g : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2)
    {δ : ℝ}
    (hδ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) δ)
    (hδZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g
        (0 : SmoothCcTensor g 0 2)) δ)
    (p : ℕ) (σ : Equiv.Perm (Fin (p + 2))) :
    JointlySmoothCcTensorFamily (I := I) g (p + 2) p
      (metricPerturbationPathDomain (δ := δ) (δ' := δ))
      (fun t => reindexedPureTrace (I := I) (M := M) g
        (metricPerturbationPath (I := I) g T 0 hδ hδZ t) p σ) := by
  apply contMDiffOn_clm_section_of_pointwise_jointMR (I := I) (M := M)
    (F₁ := Tensor0SModel (p + 2) ℝ E)
    (V₁ := fun x : M => Tensor0SSpace (p + 2) I x)
    (F₂ := Tensor0SModel p ℝ E) (V₂ := fun x : M => Tensor0SSpace p I x)
    (φ := fun q : M × ℝ =>
      (reindexedPureTrace (I := I) (M := M) g
        (metricPerturbationPath (I := I) g T 0 hδ hδZ q.2) p σ).toSection q.1)
    (S := metricPerturbationPathDomain (δ := δ) (δ' := δ))
  intro Y
  have hY : ContMDiffOn (I.prod 𝓘(ℝ, ℝ))
      (I.prod 𝓘(ℝ, Tensor0SModel (p + 2) ℝ E)) ∞
      (fun q : M × ℝ => TotalSpace.mk' (Tensor0SModel (p + 2) ℝ E)
        (E := fun x : M => Tensor0SSpace (p + 2) I x) q.1 (Y q.1))
      ((Set.univ : Set M) ×ˢ metricPerturbationPathDomain (δ := δ) (δ' := δ)) :=
    Y.contMDiff.comp_contMDiffOn contMDiffOn_fst
  have hperm := domDomCongrField_jointContMDiffOn (I := I) σ
    (S := metricPerturbationPathDomain (δ := δ) (δ' := δ))
    (fun q : M × ℝ => Y q.1) hY
  have htr := cometricDoubleTraceFib_metricPerturbationPath_jointContMDiffOn
    (I := I) (p := p) g T 0 hδ hδZ _ hperm
  refine htr.congr (fun q _ => ?_)
  refine congrArg (fun z => TotalSpace.mk' (Tensor0SModel p ℝ E)
    (E := fun x : M => Tensor0SSpace p I x) q.1 z) ?_
  rw [show
      ((reindexedPureTrace (I := I) (M := M) g
        (metricPerturbationPath (I := I) g T 0 hδ hδZ q.2) p σ).toSection q.1)
          (Y q.1) =
        DifferentialGeometry.Analysis.Spectral.LieCorrectionZeroCore.lieCorrectionZeroTraceStep (I := I)
          (metricPerturbationPath (I := I) g T 0 hδ hδZ q.2) p σ q.1 (Y q.1) from
      congrArg (fun L => L (Y q.1))
        (reindexedPureTrace_toSection (I := I) (M := M) g
          (metricPerturbationPath (I := I) g T 0 hδ hδZ q.2) p σ q.1),
    DifferentialGeometry.Analysis.Spectral.LieCorrectionZeroCore.lieCorrectionZeroTraceStep,
    ContinuousLinearMap.comp_apply, domDomCongrFibRank_apply]

theorem pureTrace_metricPerturbationPath_jointlySmooth
    (g : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2)
    {δ : ℝ}
    (hδ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) δ)
    (hδZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g
        (0 : SmoothCcTensor g 0 2)) δ)
    (p : ℕ) :
    JointlySmoothCcTensorFamily (I := I) g (p + 2) p
      (metricPerturbationPathDomain (δ := δ) (δ' := δ))
      (fun t => pureTrace (I := I) (M := M) g
        (metricPerturbationPath (I := I) g T 0 hδ hδZ t) p) := by
  apply contMDiffOn_clm_section_of_pointwise_jointMR (I := I) (M := M)
    (F₁ := Tensor0SModel (p + 2) ℝ E)
    (V₁ := fun x : M => Tensor0SSpace (p + 2) I x)
    (F₂ := Tensor0SModel p ℝ E) (V₂ := fun x : M => Tensor0SSpace p I x)
    (φ := fun q : M × ℝ =>
      (pureTrace (I := I) (M := M) g
        (metricPerturbationPath (I := I) g T 0 hδ hδZ q.2) p).toSection q.1)
    (S := metricPerturbationPathDomain (δ := δ) (δ' := δ))
  intro Y
  have hY : ContMDiffOn (I.prod 𝓘(ℝ, ℝ))
      (I.prod 𝓘(ℝ, Tensor0SModel (p + 2) ℝ E)) ∞
      (fun q : M × ℝ => TotalSpace.mk' (Tensor0SModel (p + 2) ℝ E)
        (E := fun x : M => Tensor0SSpace (p + 2) I x) q.1 (Y q.1))
      ((Set.univ : Set M) ×ˢ metricPerturbationPathDomain (δ := δ) (δ' := δ)) :=
    Y.contMDiff.comp_contMDiffOn contMDiffOn_fst
  have htr := cometricDoubleTraceFib_metricPerturbationPath_jointContMDiffOn
    (I := I) (p := p) g T 0 hδ hδZ (fun q : M × ℝ => Y q.1) hY
  refine htr.congr (fun q _ => ?_)
  refine congrArg (fun z => TotalSpace.mk' (Tensor0SModel p ℝ E)
    (E := fun x : M => Tensor0SSpace p I x) q.1 z) ?_
  rw [pureTrace_toSection]

theorem cometricDoublePairTraceCoefficient_metricPerturbationPath_jointlySmooth
    (g : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2)
    {δ : ℝ}
    (hδ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) δ)
    (hδZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g
        (0 : SmoothCcTensor g 0 2)) δ) :
    JointlySmoothCcTensorFamily (I := I) g 6 2
      (metricPerturbationPathDomain (δ := δ) (δ' := δ))
      (fun t => cometricDoublePairTraceCoefficient (I := I) (M := M) g
        (metricPerturbationPath (I := I) g T 0 hδ hδZ t)) := by
  have h₂ := pureTrace_metricPerturbationPath_jointlySmooth (I := I) (M := M) g T hδ hδZ 2
  have h₄ := pureTrace_metricPerturbationPath_jointlySmooth (I := I) (M := M) g T hδ hδZ 4
  have hout := jointlySmoothCcTensorFamily_ccOperatorFieldComp (I := I) (M := M) g h₂ h₄
  simpa only [RicciDeTurckLowOrder.pairTrace_eq] using hout

theorem reindexedCometricDoubleTrace_metricPerturbationPath_jointlySmooth
    (g : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2)
    {δ : ℝ}
    (hδ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) δ)
    (hδZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g
        (0 : SmoothCcTensor g 0 2)) δ) :
    JointlySmoothCcTensorFamily (I := I) g 4 2
      (metricPerturbationPathDomain (δ := δ) (δ' := δ))
      (fun t => reindexedCometricDoubleTrace (I := I) (M := M) g
        (metricPerturbationPath (I := I) g T 0 hδ hδZ t)) := by
  apply contMDiffOn_clm_section_of_pointwise_jointMR (I := I) (M := M)
    (F₁ := Tensor0SModel 4 ℝ E) (V₁ := fun x : M => Tensor0SSpace 4 I x)
    (F₂ := Tensor0SModel 2 ℝ E) (V₂ := fun x : M => Tensor0SSpace 2 I x)
    (φ := fun q : M × ℝ =>
      (reindexedCometricDoubleTrace (I := I) (M := M) g
        (metricPerturbationPath (I := I) g T 0 hδ hδZ q.2)).toSection q.1)
    (S := metricPerturbationPathDomain (δ := δ) (δ' := δ))
  intro Y
  have hY : ContMDiffOn (I.prod 𝓘(ℝ, ℝ))
      (I.prod 𝓘(ℝ, Tensor0SModel 4 ℝ E)) ∞
      (fun q : M × ℝ => TotalSpace.mk' (Tensor0SModel 4 ℝ E)
        (E := fun x : M => Tensor0SSpace 4 I x) q.1 (Y q.1))
      ((Set.univ : Set M) ×ˢ metricPerturbationPathDomain (δ := δ) (δ' := δ)) :=
    Y.contMDiff.comp_contMDiffOn contMDiffOn_fst
  have htr := cometricDoubleTraceFib_metricPerturbationPath_jointContMDiffOn
    (I := I) (p := 2) g T 0 hδ hδZ
    (fun q : M × ℝ => Y q.1) hY
  refine htr.congr (fun q _ => ?_)
  refine congrArg (fun z => TotalSpace.mk' (Tensor0SModel 2 ℝ E)
    (E := fun x : M => Tensor0SSpace 2 I x) q.1 z) ?_
  exact congrArg (fun L => L (Y q.1))
    (reindexedCometricDoubleTrace_toSection (I := I) (M := M) g
      (metricPerturbationPath (I := I) g T 0 hδ hδZ q.2) q.1)

theorem lieCorrectionZeroVectorBundleMetricConnectionDifferenceTerm_metricPerturbationPath_jointlySmooth
    (g : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2)
    {δ : ℝ}
    (hδ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) δ)
    (hδZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g
        (0 : SmoothCcTensor g 0 2)) δ) :
    JointlySmoothCcTensorFamily (I := I) g 1 4
      (metricPerturbationPathDomain (δ := δ) (δ' := δ))
      (fun t => lieCorrectionZeroVectorBundleMetricConnectionDifferenceTerm (I := I) (M := M) g
        (metricPerturbationPath (I := I) g T 0 hδ hδZ t)) := by
  apply contMDiffOn_clm_section_of_pointwise_jointMR (I := I) (M := M)
    (F₁ := Tensor0SModel 1 ℝ E) (V₁ := fun x : M => Tensor0SSpace 1 I x)
    (F₂ := Tensor0SModel 4 ℝ E) (V₂ := fun x : M => Tensor0SSpace 4 I x)
    (φ := fun q : M × ℝ =>
      (lieCorrectionZeroVectorBundleMetricConnectionDifferenceTerm (I := I) (M := M) g
        (metricPerturbationPath (I := I) g T 0 hδ hδZ q.2)).toSection q.1)
    (S := metricPerturbationPathDomain (δ := δ) (δ' := δ))
  intro Y
  have hY : ContMDiffOn (I.prod 𝓘(ℝ, ℝ))
      (I.prod 𝓘(ℝ, Tensor0SModel 1 ℝ E)) ∞
      (fun q : M × ℝ => TotalSpace.mk' (Tensor0SModel 1 ℝ E)
        (E := fun x : M => Tensor0SSpace 1 I x) q.1 (Y q.1))
      ((Set.univ : Set M) ×ˢ metricPerturbationPathDomain (δ := δ) (δ' := δ)) :=
    Y.contMDiff.comp_contMDiffOn contMDiffOn_fst
  have hM := metricConnectionDifferenceLowered_selfFam_jointContMDiffOn
    (I := I) g T 0 hδ hδZ
  have hprod := jointTensor0SProd_local (I := I) (p := 1) (q := 3)
    (S := metricPerturbationPathDomain (δ := δ) (δ' := δ))
    (fun q : M × ℝ => Y q.1)
    (fun q : M × ℝ => metricConnectionDifferenceLoweredFib (I := I)
      (metricPerturbationPath (I := I) g T 0 hδ hδZ q.2)
      (metricPerturbationPath (I := I) g T 0 hδ hδZ q.2) g q.1)
    hY hM
  have hprod' : ContMDiffOn (I.prod 𝓘(ℝ, ℝ))
      (I.prod 𝓘(ℝ, Tensor0SModel 4 ℝ E)) ∞
      (fun q : M × ℝ => TotalSpace.mk' (Tensor0SModel 4 ℝ E)
        (E := fun x : M => Tensor0SSpace 4 I x) q.1
        (tensor0SProdKappaFib (I := I) q.1
          (metricConnectionDifferenceLoweredFib (I := I)
            (metricPerturbationPath (I := I) g T 0 hδ hδZ q.2)
            (metricPerturbationPath (I := I) g T 0 hδ hδZ q.2) g q.1)
          (Y q.1)))
      ((Set.univ : Set M) ×ˢ metricPerturbationPathDomain (δ := δ) (δ' := δ)) := by
    refine hprod.congr (fun q _ => ?_)
    refine congrArg (fun z => TotalSpace.mk' (Tensor0SModel 4 ℝ E)
      (E := fun x : M => Tensor0SSpace 4 I x) q.1 z) ?_
    rw [tensor0SProdKappaFib_apply]
  have hperm := domDomCongrField_jointContMDiffOn (I := I)
    LieCorrectionZeroCore.lieCorrectionZeroVectorBundleTracePermutation
    (S := metricPerturbationPathDomain (δ := δ) (δ' := δ)) _ hprod'
  refine hperm.congr (fun q _ => ?_)
  refine congrArg (fun z => TotalSpace.mk' (Tensor0SModel 4 ℝ E)
    (E := fun x : M => Tensor0SSpace 4 I x) q.1 z) ?_
  rw [show
      ((lieCorrectionZeroVectorBundleMetricConnectionDifferenceTerm (I := I) (M := M) g
        (metricPerturbationPath (I := I) g T 0 hδ hδZ q.2)).toSection q.1) (Y q.1) =
        domDomCongrFibRank (I := I) 4 LieCorrectionZeroCore.lieCorrectionZeroVectorBundleTracePermutation q.1
          (tensor0SProdKappaFib (I := I) (p := 1) (q := 3) q.1
            (metricConnectionDifferenceLoweredFib (I := I)
              (metricPerturbationPath (I := I) g T 0 hδ hδZ q.2)
              (metricPerturbationPath (I := I) g T 0 hδ hδZ q.2) g q.1)
            (Y q.1)) from rfl,
    domDomCongrFibRank_apply]

theorem lieCorrectionZeroVectorBundleDerivativeCoefficient_metricPerturbationPath_jointlySmooth
    (g : SmoothRiemannianMetric I M) (T W : SmoothCcTensor g 0 2)
    {δ : ℝ}
    (hδ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) δ)
    (hδZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g
        (0 : SmoothCcTensor g 0 2)) δ) :
    JointlySmoothCcTensorFamily (I := I) g 3 2
      (metricPerturbationPathDomain (δ := δ) (δ' := δ))
      (fun t => lieCorrectionZeroVectorBundleDerivativeCoefficient (I := I) (M := M) g
        (metricPerturbationPath (I := I) g T 0 hδ hδZ t) W) := by
  have hconn : JointlySmoothCcTensorFamily (I := I) g 3 3
      (metricPerturbationPathDomain (δ := δ) (δ' := δ))
      (fun t => RicciDeTurckLowOrder.connectionDifferenceLowOrderOperator (I := I) (M := M) g
        (metricPerturbationPath (I := I) g T 0 hδ hδZ t)) :=
    RicciDeTurckLowOrder.connectionDifferenceLowOrderOperator_joint (I := I) (M := M) g T hδ hδZ
  have htr : JointlySmoothCcTensorFamily (I := I) g 3 1
      (metricPerturbationPathDomain (δ := δ) (δ' := δ))
      (fun t => reindexedPureTrace (I := I) (M := M) g
        (metricPerturbationPath (I := I) g T 0 hδ hδZ t) 1
        (Equiv.refl (Fin 3))) := by
    simpa only using reindexedPureTrace_metricPerturbationPath_jointlySmooth (I := I) (M := M) g T hδ hδZ
      1 (Equiv.refl (Fin 3))
  have hraise := jointlySmoothCcTensorFamily_const (I := I) (M := M) g
    (S := metricPerturbationPathDomain (δ := δ) (δ' := δ))
    (cometricRaiseSlot0Field (I := I) (M := M) g 0 W)
  have hmcd := lieCorrectionZeroVectorBundleMetricConnectionDifferenceTerm_metricPerturbationPath_jointlySmooth (I := I) (M := M) g T hδ hδZ
  have hriem := reindexedCometricDoubleTrace_metricPerturbationPath_jointlySmooth (I := I) (M := M) g T hδ hδZ
  have h₁ := jointlySmoothCcTensorFamily_ccOperatorFieldComp (I := I) (M := M) g htr hconn
  have h₂ := jointlySmoothCcTensorFamily_ccOperatorFieldComp (I := I) (M := M) g hraise h₁
  have h₃ := jointlySmoothCcTensorFamily_ccOperatorFieldComp (I := I) (M := M) g hmcd h₂
  have h₄ := jointlySmoothCcTensorFamily_ccOperatorFieldComp (I := I) (M := M) g hriem h₃
  have hcore : JointlySmoothCcTensorFamily (I := I) g 3 2
      (metricPerturbationPathDomain (δ := δ) (δ' := δ))
      (fun t => lieCorrectionZeroVectorBundleUnscaledDerivativeCoefficient (I := I) (M := M) g
        (metricPerturbationPath (I := I) g T 0 hδ hδZ t) W) := by
    simpa only [lieCorrectionZeroVectorBundleUnscaledDerivativeCoefficient] using h₄
  have hcore' : linearizedRicciThreeArmHjoint (I := I) (M := M) g 3
      (fun t => lieCorrectionZeroVectorBundleUnscaledDerivativeCoefficient (I := I) (M := M) g
        (metricPerturbationPath (I := I) g T 0 hδ hδZ t) W)
      (δ := δ) (δ' := δ) := hcore
  have hs := threeArmJoint_smul (I := I) (M := M) (r := 3) g (2 : ℝ)
    (fun t => lieCorrectionZeroVectorBundleUnscaledDerivativeCoefficient (I := I) (M := M) g
      (metricPerturbationPath (I := I) g T 0 hδ hδZ t) W) hcore'
  simpa only [linearizedRicciThreeArmHjoint, lieCorrectionZeroVectorBundleDerivativeCoefficient] using hs

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [SigmaCompactSpace M] in
theorem metricConnectionDifferenceLoweredCoefficient_apply_unitTensor
    (g gm gB : SmoothRiemannianMetric I M) (x : M) :
    ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 3 I x from
      (metricConnectionDifferenceLoweredCoefficient (I := I) (M := M) g gm gB).toSection x)
        (unitTensor (I := I) (M := M) x)) =
      metricConnectionDifferenceLoweredFib (I := I) gm gm gB x := by
  rw [show
      ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 3 I x from
        (metricConnectionDifferenceLoweredCoefficient (I := I) (M := M) g gm gB).toSection x)
          (unitTensor (I := I) (M := M) x)) =
        (MixedSection.eval₀ (F := E) (E := (TangentSpace I : M → Type _)) x).smulRight
          (metricConnectionDifferenceLoweredFib (I := I) gm gm gB x)
          (ContinuousMultilinearMap.constOfIsEmpty ℝ
            (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ)) from rfl]
  rw [ContinuousLinearMap.smulRight_apply, MixedSection.eval₀_apply,
    ContinuousMultilinearMap.constOfIsEmpty_apply, one_smul]

theorem slotExtendedMetricConnectionDifferenceLoweredCoefficient_metricPerturbationPath_jointlySmooth
    (g : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2)
    {δ : ℝ}
    (hδ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) δ)
    (hδZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g
        (0 : SmoothCcTensor g 0 2)) δ) :
    JointlySmoothCcTensorFamily (I := I) g 3 6
      (metricPerturbationPathDomain (δ := δ) (δ' := δ))
      (fun t => slotExtendIter (I := I) (M := M) g 0 3 3
        (metricConnectionDifferenceLoweredCoefficient (I := I) (M := M) g
          (metricPerturbationPath (I := I) g T 0 hδ hδZ t) g)) := by
  apply contMDiffOn_clm_section_of_pointwise_jointMR (I := I) (M := M)
    (F₁ := Tensor0SModel 3 ℝ E) (V₁ := fun x : M => Tensor0SSpace 3 I x)
    (F₂ := Tensor0SModel 6 ℝ E) (V₂ := fun x : M => Tensor0SSpace 6 I x)
    (φ := fun q : M × ℝ =>
      (slotExtendIter (I := I) (M := M) g 0 3 3
        (metricConnectionDifferenceLoweredCoefficient (I := I) (M := M) g
          (metricPerturbationPath (I := I) g T 0 hδ hδZ q.2) g)).toSection q.1)
    (S := metricPerturbationPathDomain (δ := δ) (δ' := δ))
  intro Y
  have hY : ContMDiffOn (I.prod 𝓘(ℝ, ℝ))
      (I.prod 𝓘(ℝ, Tensor0SModel 3 ℝ E)) ∞
      (fun q : M × ℝ => TotalSpace.mk' (Tensor0SModel 3 ℝ E)
        (E := fun x : M => Tensor0SSpace 3 I x) q.1 (Y q.1))
      ((Set.univ : Set M) ×ˢ metricPerturbationPathDomain (δ := δ) (δ' := δ)) :=
    Y.contMDiff.comp_contMDiffOn contMDiffOn_fst
  have hM := metricConnectionDifferenceLowered_selfFam_jointContMDiffOn
    (I := I) g T 0 hδ hδZ
  have hK : ContMDiffOn (I.prod 𝓘(ℝ, ℝ))
      (I.prod 𝓘(ℝ, Tensor0SModel 3 ℝ E)) ∞
      (fun q : M × ℝ => TotalSpace.mk' (Tensor0SModel 3 ℝ E)
        (E := fun x : M => Tensor0SSpace 3 I x) q.1
        ((show Tensor0SSpace 0 I q.1 →L[ℝ] Tensor0SSpace 3 I q.1 from
          (metricConnectionDifferenceLoweredCoefficient (I := I) (M := M) g
            (metricPerturbationPath (I := I) g T 0 hδ hδZ q.2) g).toSection q.1)
          (unitTensor (I := I) (M := M) q.1)))
      ((Set.univ : Set M) ×ˢ metricPerturbationPathDomain (δ := δ) (δ' := δ)) := by
    refine hM.congr (fun q _ => ?_)
    exact congrArg (fun z => TotalSpace.mk' (Tensor0SModel 3 ℝ E)
      (E := fun x : M => Tensor0SSpace 3 I x) q.1 z)
      (metricConnectionDifferenceLoweredCoefficient_apply_unitTensor (I := I) (M := M) g
        (metricPerturbationPath (I := I) g T 0 hδ hδZ q.2) g q.1)
  have hprod := jointTensor0SProd_local (I := I) (p := 3) (q := 3)
    (S := metricPerturbationPathDomain (δ := δ) (δ' := δ))
    (fun q : M × ℝ => Y q.1)
    (fun q : M × ℝ =>
      (show Tensor0SSpace 0 I q.1 →L[ℝ] Tensor0SSpace 3 I q.1 from
        (metricConnectionDifferenceLoweredCoefficient (I := I) (M := M) g
          (metricPerturbationPath (I := I) g T 0 hδ hδZ q.2) g).toSection q.1)
        (unitTensor (I := I) (M := M) q.1))
    hY hK
  have hprod' : ContMDiffOn (I.prod 𝓘(ℝ, ℝ))
      (I.prod 𝓘(ℝ, Tensor0SModel 6 ℝ E)) ∞
      (fun q : M × ℝ => TotalSpace.mk' (Tensor0SModel 6 ℝ E)
        (E := fun x : M => Tensor0SSpace 6 I x) q.1
        (tensor0SProdKappaFib (I := I) (p := 3) (q := 3) q.1
          ((show Tensor0SSpace 0 I q.1 →L[ℝ] Tensor0SSpace 3 I q.1 from
            (metricConnectionDifferenceLoweredCoefficient (I := I) (M := M) g
              (metricPerturbationPath (I := I) g T 0 hδ hδZ q.2) g).toSection q.1)
            (unitTensor (I := I) (M := M) q.1))
          (Y q.1)))
      ((Set.univ : Set M) ×ˢ metricPerturbationPathDomain (δ := δ) (δ' := δ)) := by
    refine hprod.congr (fun q _ => ?_)
    refine congrArg (fun z => TotalSpace.mk' (Tensor0SModel 6 ℝ E)
      (E := fun x : M => Tensor0SSpace 6 I x) q.1 z) ?_
    rw [tensor0SProdKappaFib_apply]
  refine hprod'.congr (fun q _ => ?_)
  refine congrArg (fun z => TotalSpace.mk' (Tensor0SModel 6 ℝ E)
    (E := fun x : M => Tensor0SSpace 6 I x) q.1 z) ?_
  exact slotExtendIter_three_zero_three_apply (I := I) (M := M) g
    (metricConnectionDifferenceLoweredCoefficient (I := I) (M := M) g
      (metricPerturbationPath (I := I) g T 0 hδ hδZ q.2) g) q.1 (Y q.1)

theorem lieCorrectionZeroMixedConnectionHalfDerivativeCoefficient_metricPerturbationPath_jointlySmooth
    (g : SmoothRiemannianMetric I M) (T W : SmoothCcTensor g 0 2)
    {δ : ℝ}
    (hδ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) δ)
    (hδZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g
        (0 : SmoothCcTensor g 0 2)) δ)
    (σlast : Equiv.Perm (Fin 4)) :
    JointlySmoothCcTensorFamily (I := I) g 3 2
      (metricPerturbationPathDomain (δ := δ) (δ' := δ))
      (fun t => lieCorrectionZeroMixedConnectionHalfDerivativeCoefficient (I := I) (M := M) g
        (metricPerturbationPath (I := I) g T 0 hδ hδZ t) g W σlast) := by
  let S := metricPerturbationPathDomain (δ := δ) (δ' := δ)
  have hQ : JointlySmoothCcTensorFamily (I := I) g 5 3 S
      (fun t => reindexedPureTrace (I := I) (M := M) g
        (metricPerturbationPath (I := I) g T 0 hδ hδZ t) 3
        LieCorrectionZeroCore.lieCorrectionZeroMixedConnectionPermutationCycleZeroOneFour) := by
    simpa only [S] using reindexedPureTrace_metricPerturbationPath_jointlySmooth (I := I) (M := M) g T hδ hδZ
      3 LieCorrectionZeroCore.lieCorrectionZeroMixedConnectionPermutationCycleZeroOneFour
  have h₄ : JointlySmoothCcTensorFamily (I := I) g 6 4 S
      (fun t => reindexedPureTrace (I := I) (M := M) g
        (metricPerturbationPath (I := I) g T 0 hδ hδZ t) 4
        LieCorrectionZeroCore.lieCorrectionZeroMixedConnectionPermutationCycleZeroTwoThreeOne) := by
    simpa only [S] using reindexedPureTrace_metricPerturbationPath_jointlySmooth (I := I) (M := M) g T hδ hδZ
      4 LieCorrectionZeroCore.lieCorrectionZeroMixedConnectionPermutationCycleZeroTwoThreeOne
  have h₂ : JointlySmoothCcTensorFamily (I := I) g 4 2 S
      (fun t => reindexedPureTrace (I := I) (M := M) g
        (metricPerturbationPath (I := I) g T 0 hδ hδZ t) 2 σlast) := by
    simpa only [S] using reindexedPureTrace_metricPerturbationPath_jointlySmooth (I := I) (M := M) g T hδ hδZ 2 σlast
  have hslot : JointlySmoothCcTensorFamily (I := I) g 3 6 S
      (fun t => slotExtendIter (I := I) (M := M) g 0 3 3
        (metricConnectionDifferenceLoweredCoefficient (I := I) (M := M) g
          (metricPerturbationPath (I := I) g T 0 hδ hδZ t) g)) := by
    simpa only [S] using slotExtendedMetricConnectionDifferenceLoweredCoefficient_metricPerturbationPath_jointlySmooth (I := I) (M := M) g T hδ hδZ
  have hbase := jointlySmoothCcTensorFamily_const (I := I) (M := M) g (S := S)
    (ccOperatorFieldComp (I := I) (M := M) g 3 3 5
      (tensorThreeTwoProductCoefficient (I := I) (M := M) g W)
      (metricConnectionDifferenceLoweringCoefficient (I := I) (M := M) g))
  have h₁ := jointlySmoothCcTensorFamily_ccOperatorFieldComp (I := I) (M := M) g hQ hbase
  have h₂' := jointlySmoothCcTensorFamily_ccOperatorFieldComp (I := I) (M := M) g hslot h₁
  have h₃ := jointlySmoothCcTensorFamily_ccOperatorFieldComp (I := I) (M := M) g h₄ h₂'
  have hout := jointlySmoothCcTensorFamily_ccOperatorFieldComp (I := I) (M := M) g h₂ h₃
  simpa only [lieCorrectionZeroMixedConnectionHalfDerivativeCoefficient] using hout

theorem lieCorrectionZeroMixedConnectionDerivativeCoefficient_metricPerturbationPath_jointlySmooth
    (g : SmoothRiemannianMetric I M) (T W : SmoothCcTensor g 0 2)
    {δ : ℝ}
    (hδ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) δ)
    (hδZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g
        (0 : SmoothCcTensor g 0 2)) δ) :
    JointlySmoothCcTensorFamily (I := I) g 3 2
      (metricPerturbationPathDomain (δ := δ) (δ' := δ))
      (fun t => lieCorrectionZeroMixedConnectionDerivativeCoefficient (I := I) (M := M) g
        (metricPerturbationPath (I := I) g T 0 hδ hδZ t) g W) := by
  have hA := lieCorrectionZeroMixedConnectionHalfDerivativeCoefficient_metricPerturbationPath_jointlySmooth (I := I) (M := M) g T W hδ hδZ
    LieCorrectionZeroCore.lieCorrectionZeroMixedConnectionPermutationCycleZeroTwoOne
  have hB := lieCorrectionZeroMixedConnectionHalfDerivativeCoefficient_metricPerturbationPath_jointlySmooth (I := I) (M := M) g T W hδ hδZ
    (lieCorrectionZeroMixedConnectionTraceOutputSwapPermutation * LieCorrectionZeroCore.lieCorrectionZeroMixedConnectionPermutationCycleZeroTwoOne)
  have hadd := jointlySmoothCcTensorFamily_add (I := I) (M := M) g hA hB
  have hadd' : linearizedRicciThreeArmHjoint (I := I) (M := M) g 3
      (fun t =>
        lieCorrectionZeroMixedConnectionHalfDerivativeCoefficient (I := I) (M := M) g
            (metricPerturbationPath (I := I) g T 0 hδ hδZ t) g W
            LieCorrectionZeroCore.lieCorrectionZeroMixedConnectionPermutationCycleZeroTwoOne +
          lieCorrectionZeroMixedConnectionHalfDerivativeCoefficient (I := I) (M := M) g
            (metricPerturbationPath (I := I) g T 0 hδ hδZ t) g W
            (lieCorrectionZeroMixedConnectionTraceOutputSwapPermutation * LieCorrectionZeroCore.lieCorrectionZeroMixedConnectionPermutationCycleZeroTwoOne))
      (δ := δ) (δ' := δ) := hadd
  have hs := threeArmJoint_smul (I := I) (M := M) (r := 3) g (2 : ℝ) _ hadd'
  simpa only [linearizedRicciThreeArmHjoint, lieCorrectionZeroMixedConnectionDerivativeCoefficient] using hs

theorem ricciConnectionDifferenceDerivativeCoefficient_metricPerturbationPath_jointlySmooth
    (g : SmoothRiemannianMetric I M) (T W : SmoothCcTensor g 0 2)
    {δ : ℝ}
    (hδ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) δ)
    (hδZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g
        (0 : SmoothCcTensor g 0 2)) δ) :
    JointlySmoothCcTensorFamily (I := I) g 3 2
      (metricPerturbationPathDomain (δ := δ) (δ' := δ))
      (fun t => ricciConnectionDifferenceDerivativeCoefficient (I := I) (M := M) g
        (metricPerturbationPath (I := I) g T 0 hδ hδZ t) W) := by
  have hA := ricciConnectionDifferenceQuadraticDerivativeCoefficient_metricPerturbationPath_jointlySmooth (I := I) (M := M) g T W hδ hδZ
  have hD : JointlySmoothCcTensorFamily (I := I) g 3 2
      (metricPerturbationPathDomain (δ := δ) (δ' := δ))
      (fun t => RicciDeTurckLowOrder.ricciConnectionDerivativeTransposedCoefficient (I := I) (M := M) g
        (metricPerturbationPath (I := I) g T 0 hδ hδZ t)
        (symmS (I := I) (M := M) g W)) :=
    RicciDeTurckLowOrder.ricciConnectionDerivativeTransposedCoefficient_joint (I := I) (M := M) g T
      (symmS (I := I) (M := M) g W) hδ hδZ
  simpa only [ricciConnectionDifferenceDerivativeCoefficient] using jointlySmoothCcTensorFamily_add (I := I) (M := M) g hA hD

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [SigmaCompactSpace M] in
theorem deTurckLieCovariantDerivativeArmTwoCoefficient_eq_permuted_connectionDifferenceContravariantInsertionField
    (g gm : SmoothRiemannianMetric I M) :
    deTurckLieCovariantDerivativeArmTwoCoefficient (I := I) (M := M) g gm =
      ccOperatorFieldComp (I := I) (M := M) g 3 4 4
        (permCoeff (I := I) (M := M) g ricciQuadraticPermutation_swapBlocks)
        (connectionDifferenceContravariantInsertionField (I := I) g gm) := by
  rw [operatorFieldComposition_permutationCoefficient_apply_eq_rsDomDomCongrSection (I := I) (M := M) g ricciQuadraticPermutation_swapBlocks]
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rw [deTurckLieCovariantDerivativeArmTwoCoefficient, armSlotEndoCc_toSection,
    rsDomDomCongrSection_toSection]
  apply ContinuousLinearMap.ext
  intro D
  apply Tensor0SSpace.toModel_injective
  apply ContinuousMultilinearMap.ext
  intro v
  change Tensor0SSpace.toModel
      (armSlotFib (I := I) (M := M) 2 x
        (connectionDifferenceEndomorphism (I := I) (M := M) g gm x) D) v =
    Tensor0SSpace.toModel
      ((rsDomDomCongr ricciQuadraticPermutation_swapBlocks
        ((connectionDifferenceContravariantInsertionField (I := I) g gm).toSection x)) D) v
  rw [armSlotFib_apply_eval, slotInsertEndoFib_apply_eval]
  rw [toModel_rsDomDomCongr_apply,
    ContinuousMultilinearMap.domDomCongr_apply]
  rw [connectionDifferenceContravariantInsertionField_toSection, connContr21_insert]
  rw [connectionDifferenceEndomorphism_apply]
  congr 1
  funext k
  fin_cases k <;> simp [ricciQuadraticPermutation_swapBlocks] <;> rfl

theorem deTurckLieCovariantDerivativeArmTwoCoefficient_metricPerturbationPath_jointlySmooth
    (g : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2)
    {δ : ℝ}
    (hδ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) δ)
    (hδZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g
        (0 : SmoothCcTensor g 0 2)) δ) :
    JointlySmoothCcTensorFamily (I := I) g 3 4
      (metricPerturbationPathDomain (δ := δ) (δ' := δ))
      (fun t => deTurckLieCovariantDerivativeArmTwoCoefficient (I := I) (M := M) g
        (metricPerturbationPath (I := I) g T 0 hδ hδZ t)) := by
  let S := metricPerturbationPathDomain (δ := δ) (δ' := δ)
  have hp := jointlySmoothCcTensorFamily_const (I := I) (M := M) g (S := S)
    (permCoeff (I := I) (M := M) g ricciQuadraticPermutation_swapBlocks)
  have hi := connectionDifferenceContravariantInsertionField_metricPerturbationPath_jointlySmooth (I := I) (M := M) g T hδ hδZ
  have hout := jointlySmoothCcTensorFamily_ccOperatorFieldComp (I := I) (M := M) g hp hi
  simpa only [S, deTurckLieCovariantDerivativeArmTwoCoefficient_eq_permuted_connectionDifferenceContravariantInsertionField] using hout

omit [BoundarylessManifold I M] in
theorem metricComparisonSlotInsertion_metricPerturbationPath_eq
    (g : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2)
    {δ : ℝ}
    (hδ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) δ)
    (hδZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g
        (0 : SmoothCcTensor g 0 2)) δ)
    {t : ℝ} (ht : t ∈ metricPerturbationPathDomain (δ := δ) (δ' := δ)) :
    slotInsertEndoCc (I := I) (M := M) g 2
        (metricComparisonEndomorphismField (I := I) (M := M)
          (metricPerturbationPath (I := I) g T 0 hδ hδZ t) g) =
      slotInsertEndoCc (I := I) (M := M) g 2
          (metricComparisonEndomorphismField (I := I) (M := M) g g) +
        t • slotInsertEndoCc (I := I) (M := M) g 2
          (symmRaiseEndo (I := I) (M := M) g T) := by
  have htie : ∀ (x : M) (u v : TangentSpace I x),
      (metricPerturbationPath (I := I) g T 0 hδ hδZ t).inner x u v =
        g.inner x u v +
          ccTensorBilinSymm (I := I) g (t • T) x u v := by
    intro x u v
    rw [metricPerturbationPath_inner_of_mem (I := I) g T 0 hδ hδZ ht]
    simp only [convexPerturbation, smul_zero, zero_add]
  have hzero : ∀ (x : M) (u v : TangentSpace I x),
      g.inner x u v = g.inner x u v +
        ccTensorBilinSymm (I := I) g
          (0 : SmoothCcTensor g 0 2) x u v := by
    intro x u v
    rw [ccTensorBilinSymm_apply, ccTensorBilin_zero_weight,
      ccTensorBilin_zero_weight]
    ring
  have hrev := RicciDeTurckLowOrder.fullRev_sub (I := I) (M := M)
    g (metricPerturbationPath (I := I) g T 0 hδ hδZ t) g
      (t • T) (0 : SmoothCcTensor g 0 2) htie hzero
  rw [sub_zero, symmRaiseEndo_smul] at hrev
  have hfull :
      metricComparisonEndomorphismField (I := I) (M := M)
          (metricPerturbationPath (I := I) g T 0 hδ hδZ t) g =
        metricComparisonEndomorphismField (I := I) (M := M) g g +
          t • symmRaiseEndo (I := I) (M := M) g T := by
    calc
      _ = t • symmRaiseEndo (I := I) (M := M) g T +
          metricComparisonEndomorphismField (I := I) (M := M) g g :=
        (sub_eq_iff_eq_add.mp hrev)
      _ = _ := add_comm _ _
  rw [hfull, slotInsertEndoCc_add, slotInsertEndoCc_smul]

omit [BoundarylessManifold I M] in
theorem metricComparisonSlotInsertion_metricPerturbationPath_jointlySmooth
    (g : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2)
    {δ : ℝ}
    (hδ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) δ)
    (hδZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g
        (0 : SmoothCcTensor g 0 2)) δ) :
    JointlySmoothCcTensorFamily (I := I) g 3 3
      (metricPerturbationPathDomain (δ := δ) (δ' := δ))
      (fun t => slotInsertEndoCc (I := I) (M := M) g 2
        (metricComparisonEndomorphismField (I := I) (M := M)
          (metricPerturbationPath (I := I) g T 0 hδ hδZ t) g)) := by
  let S := metricPerturbationPathDomain (δ := δ) (δ' := δ)
  let A₀ := slotInsertEndoCc (I := I) (M := M) g 2
    (metricComparisonEndomorphismField (I := I) (M := M) g g)
  let A₁ := slotInsertEndoCc (I := I) (M := M) g 2
    (symmRaiseEndo (I := I) (M := M) g T)
  have h₀ := jointlySmoothCcTensorFamily_const (I := I) (M := M) g (S := S) A₀
  have h₁ := jointlySmoothCcTensorFamily_parameter_smul (I := I) (M := M) g
    (jointlySmoothCcTensorFamily_const (I := I) (M := M) g (S := S) A₁)
  have hout := jointlySmoothCcTensorFamily_add (I := I) (M := M) g h₀ h₁
  refine hout.congr (fun p hp => ?_)
  refine congrArg (fun z => TotalSpace.mk' (TensorRSModel 3 3 ℝ E)
    (E := fun x : M => TensorRSSpace 3 3 I x) p.1 z) ?_
  change (slotInsertEndoCc (I := I) (M := M) g 2
      (metricComparisonEndomorphismField (I := I) (M := M)
        (metricPerturbationPath (I := I) g T 0 hδ hδZ p.2) g)).toSection p.1 =
    (A₀ + p.2 • A₁).toSection p.1
  rw [metricComparisonSlotInsertion_metricPerturbationPath_eq (I := I) (M := M) g T hδ hδZ hp.2]

noncomputable def connectionDifferenceMetricLoweringCoefficient
    (g gm : SmoothRiemannianMetric I M) : SmoothCcTensor g 3 3 :=
  ccOperatorFieldComp (I := I) (M := M) g 3 3 3
    (slotInsertEndoCc (I := I) (M := M) g 2
      (metricComparisonEndomorphismField (I := I) (M := M) gm g))
    (ccOperatorFieldComp (I := I) (M := M) g 3 3 3
      (permCoeff (I := I) (M := M) g (finRotate 3))
      (RicciDeTurckLowOrder.connectionDifferenceLowOrderOperator (I := I) (M := M) g gm))

theorem connectionDifferenceMetricLoweringCoefficient_metricPerturbationPath_jointlySmooth
    (g : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2)
    {δ : ℝ}
    (hδ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) δ)
    (hδZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g
        (0 : SmoothCcTensor g 0 2)) δ) :
    JointlySmoothCcTensorFamily (I := I) g 3 3
      (metricPerturbationPathDomain (δ := δ) (δ' := δ))
      (fun t => connectionDifferenceMetricLoweringCoefficient (I := I) (M := M) g
        (metricPerturbationPath (I := I) g T 0 hδ hδZ t)) := by
  let S := metricPerturbationPathDomain (δ := δ) (δ' := δ)
  have hins := metricComparisonSlotInsertion_metricPerturbationPath_jointlySmooth (I := I) (M := M) g T hδ hδZ
  have hperm := jointlySmoothCcTensorFamily_const (I := I) (M := M) g (S := S)
    (permCoeff (I := I) (M := M) g (finRotate 3))
  have hconn : JointlySmoothCcTensorFamily (I := I) g 3 3 S
      (fun t => RicciDeTurckLowOrder.connectionDifferenceLowOrderOperator (I := I) (M := M) g
        (metricPerturbationPath (I := I) g T 0 hδ hδZ t)) := by
    simpa only [S] using RicciDeTurckLowOrder.connectionDifferenceLowOrderOperator_joint
      (I := I) (M := M) g T hδ hδZ
  have hinner := jointlySmoothCcTensorFamily_ccOperatorFieldComp (I := I) (M := M) g hperm hconn
  have hout := jointlySmoothCcTensorFamily_ccOperatorFieldComp (I := I) (M := M) g hins hinner
  simpa only [S, connectionDifferenceMetricLoweringCoefficient] using hout

omit [NeZero (Module.finrank ℝ E)] in
theorem connectionDifferenceMetricLoweringCoefficient_apply
    (g gm : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2)
    (hT : ∀ (x : M) (u v : TangentSpace I x),
      ccTensorBilin (I := I) g T x u v =
        ccTensorBilin (I := I) g T x v u)
    (htie : ∀ (x : M) (u v : TangentSpace I x),
      gm.inner x u v =
        g.inner x u v + ccTensorBilinSymm (I := I) g T x u v) :
    operatorFieldApply (I := I) (M := M) g 3 3
        (connectionDifferenceMetricLoweringCoefficient (I := I) (M := M) g gm)
        (covGrad (I := I) (M := M) g 0 2 T) =
      connectionDifferenceMetricLoweredTensor (I := I) (M := M) g gm := by
  rw [connectionDifferenceMetricLoweringCoefficient]
  rw [← operatorFieldApplication_assoc, ← operatorFieldApplication_assoc]
  have hconn : operatorFieldApply (I := I) (M := M) g 3 3
      (RicciDeTurckLowOrder.connectionDifferenceLowOrderOperator (I := I) (M := M) g gm)
      (covGrad (I := I) (M := M) g 0 2 T) =
      metricLoweredConnectionDifferenceCoefficient (I := I) g gm := by
    simpa only [operatorFieldComposition_zero_eq_operatorFieldApply] using
      RicciDeTurckLowOrder.connectionDifferenceLowOrderOperator_apply (I := I) (M := M) g gm T hT htie
  rw [hconn]
  have hperm : operatorFieldApply (I := I) (M := M) g 3 3
      (permCoeff (I := I) (M := M) g (finRotate 3))
      (metricLoweredConnectionDifferenceCoefficient (I := I) g gm) =
      domDomCongrSection (I := I) g (finRotate 3)
        (metricLoweredConnectionDifferenceCoefficient (I := I) g gm) := by
    simpa only [operatorFieldComposition_zero_eq_operatorFieldApply] using
      operatorFieldComposition_permutationCoefficient_apply (I := I) (M := M) g (finRotate 3)
        (metricLoweredConnectionDifferenceCoefficient (I := I) g gm)
  rw [hperm]
  rfl

noncomputable def connectionDifferenceQuadraticPairedDerivativeCoefficient
    (g gm : SmoothRiemannianMetric I M) : SmoothCcTensor g 3 4 :=
  ccOperatorFieldComp (I := I) (M := M) g 3 3 4
    (deTurckLieCovariantDerivativeArmTwoCoefficient (I := I) (M := M) g gm)
    (connectionDifferenceMetricLoweringCoefficient (I := I) (M := M) g gm)

noncomputable def connectionDifferenceQuadraticComposedDerivativeCoefficient
    (g gm : SmoothRiemannianMetric I M) : SmoothCcTensor g 3 4 :=
  ccOperatorFieldComp (I := I) (M := M) g 3 3 4
    (deTurckLieCovariantDerivativeArmTwoCoefficient (I := I) (M := M) g gm)
    (ccOperatorFieldComp (I := I) (M := M) g 3 3 3
      (permCoeff (I := I) (M := M) g (Equiv.swap (0 : Fin 3) 1))
      (connectionDifferenceMetricLoweringCoefficient (I := I) (M := M) g gm))

noncomputable def connectionDifferenceQuadraticCurvatureDerivativeCoefficient
    (g gm : SmoothRiemannianMetric I M) : SmoothCcTensor g 3 4 :=
  ccOperatorFieldComp (I := I) (M := M) g 3 4 4
      (permCoeff (I := I) (M := M) g (Equiv.swap (0 : Fin 4) 1))
      (connectionDifferenceQuadraticPairedDerivativeCoefficient (I := I) (M := M) g gm) +
    connectionDifferenceQuadraticPairedDerivativeCoefficient (I := I) (M := M) g gm +
    ccOperatorFieldComp (I := I) (M := M) g 3 4 4
      (permCoeff (I := I) (M := M) g lrPermA)
      (connectionDifferenceQuadraticComposedDerivativeCoefficient (I := I) (M := M) g gm) +
    ccOperatorFieldComp (I := I) (M := M) g 3 4 4
      (permCoeff (I := I) (M := M) g (Equiv.swap (0 : Fin 4) 2))
      (connectionDifferenceQuadraticComposedDerivativeCoefficient (I := I) (M := M) g gm) +
    ccOperatorFieldComp (I := I) (M := M) g 3 4 4
      (permCoeff (I := I) (M := M) g lrPermB)
      (connectionDifferenceQuadraticComposedDerivativeCoefficient (I := I) (M := M) g gm) +
    ccOperatorFieldComp (I := I) (M := M) g 3 4 4
      (permCoeff (I := I) (M := M) g lrPermC)
      (connectionDifferenceQuadraticComposedDerivativeCoefficient (I := I) (M := M) g gm)

theorem connectionDifferenceQuadraticPairedDerivativeCoefficient_metricPerturbationPath_jointlySmooth
    (g : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2)
    {δ : ℝ}
    (hδ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) δ)
    (hδZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g
        (0 : SmoothCcTensor g 0 2)) δ) :
    JointlySmoothCcTensorFamily (I := I) g 3 4
      (metricPerturbationPathDomain (δ := δ) (δ' := δ))
      (fun t => connectionDifferenceQuadraticPairedDerivativeCoefficient (I := I) (M := M) g
        (metricPerturbationPath (I := I) g T 0 hδ hδZ t)) := by
  have harm := deTurckLieCovariantDerivativeArmTwoCoefficient_metricPerturbationPath_jointlySmooth (I := I) (M := M) g T hδ hδZ
  have homega := connectionDifferenceMetricLoweringCoefficient_metricPerturbationPath_jointlySmooth (I := I) (M := M) g T hδ hδZ
  simpa only [connectionDifferenceQuadraticPairedDerivativeCoefficient] using jointlySmoothCcTensorFamily_ccOperatorFieldComp (I := I) (M := M) g harm homega

theorem connectionDifferenceQuadraticComposedDerivativeCoefficient_metricPerturbationPath_jointlySmooth
    (g : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2)
    {δ : ℝ}
    (hδ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) δ)
    (hδZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g
        (0 : SmoothCcTensor g 0 2)) δ) :
    JointlySmoothCcTensorFamily (I := I) g 3 4
      (metricPerturbationPathDomain (δ := δ) (δ' := δ))
      (fun t => connectionDifferenceQuadraticComposedDerivativeCoefficient (I := I) (M := M) g
        (metricPerturbationPath (I := I) g T 0 hδ hδZ t)) := by
  let S := metricPerturbationPathDomain (δ := δ) (δ' := δ)
  have harm := deTurckLieCovariantDerivativeArmTwoCoefficient_metricPerturbationPath_jointlySmooth (I := I) (M := M) g T hδ hδZ
  have hperm := jointlySmoothCcTensorFamily_const (I := I) (M := M) g (S := S)
    (permCoeff (I := I) (M := M) g (Equiv.swap (0 : Fin 3) 1))
  have homega := connectionDifferenceMetricLoweringCoefficient_metricPerturbationPath_jointlySmooth (I := I) (M := M) g T hδ hδZ
  have hswap := jointlySmoothCcTensorFamily_ccOperatorFieldComp (I := I) (M := M) g hperm homega
  simpa only [S, connectionDifferenceQuadraticComposedDerivativeCoefficient] using jointlySmoothCcTensorFamily_ccOperatorFieldComp (I := I) (M := M) g harm hswap

theorem connectionDifferenceQuadraticCurvatureDerivativeCoefficient_metricPerturbationPath_jointlySmooth
    (g : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2)
    {δ : ℝ}
    (hδ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) δ)
    (hδZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g
        (0 : SmoothCcTensor g 0 2)) δ) :
    JointlySmoothCcTensorFamily (I := I) g 3 4
      (metricPerturbationPathDomain (δ := δ) (δ' := δ))
      (fun t => connectionDifferenceQuadraticCurvatureDerivativeCoefficient (I := I) (M := M) g
        (metricPerturbationPath (I := I) g T 0 hδ hδZ t)) := by
  let S := metricPerturbationPathDomain (δ := δ) (δ' := δ)
  have hqb := connectionDifferenceQuadraticPairedDerivativeCoefficient_metricPerturbationPath_jointlySmooth (I := I) (M := M) g T hδ hδZ
  have hqa := connectionDifferenceQuadraticComposedDerivativeCoefficient_metricPerturbationPath_jointlySmooth (I := I) (M := M) g T hδ hδZ
  have hswap := jointlySmoothCcTensorFamily_const (I := I) (M := M) g (S := S)
    (permCoeff (I := I) (M := M) g (Equiv.swap (0 : Fin 4) 1))
  have hA := jointlySmoothCcTensorFamily_const (I := I) (M := M) g (S := S)
    (permCoeff (I := I) (M := M) g lrPermA)
  have hswap2 := jointlySmoothCcTensorFamily_const (I := I) (M := M) g (S := S)
    (permCoeff (I := I) (M := M) g (Equiv.swap (0 : Fin 4) 2))
  have hB := jointlySmoothCcTensorFamily_const (I := I) (M := M) g (S := S)
    (permCoeff (I := I) (M := M) g lrPermB)
  have hC := jointlySmoothCcTensorFamily_const (I := I) (M := M) g (S := S)
    (permCoeff (I := I) (M := M) g lrPermC)
  have h₀ := jointlySmoothCcTensorFamily_ccOperatorFieldComp (I := I) (M := M) g hswap hqb
  have h₂ := jointlySmoothCcTensorFamily_ccOperatorFieldComp (I := I) (M := M) g hA hqa
  have h₃ := jointlySmoothCcTensorFamily_ccOperatorFieldComp (I := I) (M := M) g hswap2 hqa
  have h₄ := jointlySmoothCcTensorFamily_ccOperatorFieldComp (I := I) (M := M) g hB hqa
  have h₅ := jointlySmoothCcTensorFamily_ccOperatorFieldComp (I := I) (M := M) g hC hqa
  have hout := jointlySmoothCcTensorFamily_add (I := I) (M := M) g
    (jointlySmoothCcTensorFamily_add (I := I) (M := M) g
      (jointlySmoothCcTensorFamily_add (I := I) (M := M) g
        (jointlySmoothCcTensorFamily_add (I := I) (M := M) g
          (jointlySmoothCcTensorFamily_add (I := I) (M := M) g h₀ hqb) h₂) h₃) h₄) h₅
  simpa only [S, connectionDifferenceQuadraticCurvatureDerivativeCoefficient] using hout

omit [NeZero (Module.finrank ℝ E)] in
theorem connectionDifferenceQuadraticCurvatureDerivativeCoefficient_apply
    (g gm : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2)
    (hT : ∀ (x : M) (u v : TangentSpace I x),
      ccTensorBilin (I := I) g T x u v =
        ccTensorBilin (I := I) g T x v u)
    (htie : ∀ (x : M) (u v : TangentSpace I x),
      gm.inner x u v =
        g.inner x u v + ccTensorBilinSymm (I := I) g T x u v) :
    operatorFieldApply (I := I) (M := M) g 3 4
        (connectionDifferenceQuadraticCurvatureDerivativeCoefficient (I := I) (M := M) g gm)
        (covGrad (I := I) (M := M) g 0 2 T) =
      connectionDifferenceQuadraticCurvatureTerm (I := I) (M := M) g gm := by
  simp only [connectionDifferenceQuadraticCurvatureDerivativeCoefficient, operatorFieldApplication_add_left]
  have hqb : operatorFieldApply (I := I) (M := M) g 3 4
      (connectionDifferenceQuadraticPairedDerivativeCoefficient (I := I) (M := M) g gm)
      (covGrad (I := I) (M := M) g 0 2 T) =
      connectionDifferenceQuadraticPairedTensor (I := I) (M := M) g gm := by
    rw [connectionDifferenceQuadraticPairedDerivativeCoefficient]
    rw [← operatorFieldApplication_assoc]
    have hω := connectionDifferenceMetricLoweringCoefficient_apply (I := I) (M := M) g gm T hT htie
    rw [hω]
    rfl
  have hqa : operatorFieldApply (I := I) (M := M) g 3 4
      (connectionDifferenceQuadraticComposedDerivativeCoefficient (I := I) (M := M) g gm)
      (covGrad (I := I) (M := M) g 0 2 T) =
      connectionDifferenceQuadraticComposedTensor (I := I) (M := M) g gm := by
    rw [connectionDifferenceQuadraticComposedDerivativeCoefficient]
    rw [← operatorFieldApplication_assoc, ← operatorFieldApplication_assoc]
    have hω := connectionDifferenceMetricLoweringCoefficient_apply (I := I) (M := M) g gm T hT htie
    rw [hω]
    have hperm : operatorFieldApply (I := I) (M := M) g 3 3
        (permCoeff (I := I) (M := M) g (Equiv.swap (0 : Fin 3) 1))
        (connectionDifferenceMetricLoweredTensor (I := I) (M := M) g gm) =
        domDomCongrSection (I := I) g (Equiv.swap (0 : Fin 3) 1)
          (connectionDifferenceMetricLoweredTensor (I := I) (M := M) g gm) := by
      simpa only [operatorFieldComposition_zero_eq_operatorFieldApply] using
        operatorFieldComposition_permutationCoefficient_apply (I := I) (M := M) g (Equiv.swap (0 : Fin 3) 1)
          (connectionDifferenceMetricLoweredTensor (I := I) (M := M) g gm)
    rw [hperm]
    rfl
  rw [← operatorFieldApplication_assoc, ← operatorFieldApplication_assoc, ← operatorFieldApplication_assoc, ← operatorFieldApplication_assoc,
    ← operatorFieldApplication_assoc]
  rw [hqb, hqa]
  have hqbPerm := operatorFieldComposition_permutationCoefficient_apply (I := I) (M := M) g (Equiv.swap (0 : Fin 4) 1)
    (connectionDifferenceQuadraticPairedTensor (I := I) (M := M) g gm)
  simp only [operatorFieldComposition_zero_eq_operatorFieldApply] at hqbPerm
  have hqaA := operatorFieldComposition_permutationCoefficient_apply (I := I) (M := M) g lrPermA
    (connectionDifferenceQuadraticComposedTensor (I := I) (M := M) g gm)
  have hqa02 := operatorFieldComposition_permutationCoefficient_apply (I := I) (M := M) g (Equiv.swap (0 : Fin 4) 2)
    (connectionDifferenceQuadraticComposedTensor (I := I) (M := M) g gm)
  have hqaB := operatorFieldComposition_permutationCoefficient_apply (I := I) (M := M) g lrPermB
    (connectionDifferenceQuadraticComposedTensor (I := I) (M := M) g gm)
  have hqaC := operatorFieldComposition_permutationCoefficient_apply (I := I) (M := M) g lrPermC
    (connectionDifferenceQuadraticComposedTensor (I := I) (M := M) g gm)
  simp only [operatorFieldComposition_zero_eq_operatorFieldApply] at hqaA hqa02 hqaB hqaC
  rw [hqbPerm, hqaA, hqa02, hqaB, hqaC]
  rfl

theorem connectionDifferenceQuadraticCurvatureTerm_metricPerturbationPath_jointlySmooth
    (g : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2)
    (hT : ∀ (x : M) (u v : TangentSpace I x),
      ccTensorBilin (I := I) g T x u v =
        ccTensorBilin (I := I) g T x v u)
    {δ : ℝ}
    (hδ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) δ)
    (hδZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g
        (0 : SmoothCcTensor g 0 2)) δ) :
    JointlySmoothCcTensorFamily (I := I) g 0 4
      (metricPerturbationPathDomain (δ := δ) (δ' := δ))
      (fun t => connectionDifferenceQuadraticCurvatureTerm (I := I) (M := M) g
        (metricPerturbationPath (I := I) g T 0 hδ hδZ t)) := by
  let S := metricPerturbationPathDomain (δ := δ) (δ' := δ)
  have hQ := connectionDifferenceQuadraticCurvatureDerivativeCoefficient_metricPerturbationPath_jointlySmooth (I := I) (M := M) g T hδ hδZ
  have hdT := jointlySmoothCcTensorFamily_const (I := I) (M := M) g (S := S)
    (covGrad (I := I) (M := M) g 0 2 T)
  have hsdT := jointlySmoothCcTensorFamily_parameter_smul (I := I) (M := M) g hdT
  have happ := jointlySmoothCcTensorFamily_ccOperatorFieldComp (I := I) (M := M) g hQ hsdT
  refine happ.congr (fun q hq => ?_)
  refine congrArg (fun z => TotalSpace.mk' (TensorRSModel 0 4 ℝ E)
    (E := fun x : M => TensorRSSpace 0 4 I x) q.1 z) ?_
  have hsymm : ∀ (x : M) (u v : TangentSpace I x),
      ccTensorBilin (I := I) g (q.2 • T) x u v =
        ccTensorBilin (I := I) g (q.2 • T) x v u := by
    intro x u v
    simp only [ccTensorBilin_apply, ccTensorModel_smul,
      ContinuousMultilinearMap.smul_apply, smul_eq_mul]
    apply congrArg (fun z : ℝ => q.2 * z)
    simpa only [ccTensorBilin_apply] using hT x u v
  have htie : ∀ (x : M) (u v : TangentSpace I x),
      (metricPerturbationPath (I := I) g T 0 hδ hδZ q.2).inner x u v =
        g.inner x u v +
          ccTensorBilinSymm (I := I) g (q.2 • T) x u v := by
    intro x u v
    rw [← show convexPerturbation (I := I) g T 0 q.2 = q.2 • T by
      simp only [convexPerturbation, smul_zero, zero_add]]
    exact metricPerturbationPath_inner_of_mem
      (I := I) g T 0 hδ hδZ hq.2 x u v
  have heq := connectionDifferenceQuadraticCurvatureDerivativeCoefficient_apply (I := I) (M := M) g
    (metricPerturbationPath (I := I) g T 0 hδ hδZ q.2) (q.2 • T) hsymm htie
  have hsec := congrArg
    (fun A : SmoothCcTensor g 0 4 => A.toSection q.1) heq
  simpa only [S, operatorFieldComposition_zero_eq_operatorFieldApply, covGrad_smul] using hsec.symm

noncomputable def lieCorrectionQuadraticZeroCoefficient
    (g gm : SmoothRiemannianMetric I M) : SmoothCcTensor g 2 2 :=
  ccOperatorFieldComp (I := I) (M := M) g 2 6 2
    (cometricDoublePairTraceCoefficient (I := I) (M := M) g gm)
    (ccOperatorFieldComp (I := I) (M := M) g 2 6 6
      (permCoeff (I := I) (M := M) g deTurckLieCovariantDerivativePairTracePermutation)
      (slotExtendIter (I := I) (M := M) g 0 4 2
        (connectionDifferenceQuadraticCurvatureTerm (I := I) (M := M) g gm)))

noncomputable def lieCorrectionCurvatureZeroCoefficient
    (g gm : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2)
    (s : ℝ) :
    SmoothCcTensor g 2 2 :=
  (-1 : ℝ) •
    ccOperatorFieldComp (I := I) (M := M) g 2 6 2
      (cometricDoublePairTraceCoefficient (I := I) (M := M) g gm)
      (ccOperatorFieldComp (I := I) (M := M) g 2 6 6
        (permCoeff (I := I) (M := M) g deTurckLieCovariantDerivativePairTracePermutation)
        (slotExtendIter (I := I) (M := M) g 0 4 2
          ((-(s / 2) : ℝ) • riemannCurvatureCoefficientField (I := I) (M := M) g T)))

theorem deTurckLieCovariantDerivative_affineZero_decomposition
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
    let gm := metricPerturbationPath (I := I) g T 0 hδ hδZ s
    (deTurckLieCovariantDerivativeArmField (I := I) (M := M) g gm g -
        deTurckLieTopOrderPairingFamily (I := I) (M := M) g T hδ hδZ
          lieDecompositionQ lieDecompositionEps s) -
      lieCorrectionQuadraticZeroCoefficient (I := I) (M := M) g gm =
        lieCorrectionCurvatureZeroCoefficient (I := I) (M := M) g gm T s := by
  dsimp only
  rw [deTurckLieEdgePairingFamily_eq_deTurckLieCovariantDerivativeExpansionPairTraceFamily (I := I) (M := M) g T hδ hδZ s]
  rw [lieCov_residual (I := I) (M := M)
    g T hδ_lt hδ hδZ hT hs]
  rw [deTurckLieCovariantDerivativeRemainderTensor_eq (I := I) (M := M) g T hδ hδZ s]
  rw [← operatorFieldComposition_permutationCoefficient_apply_eq_rsDomDomCongrSection (I := I) (M := M) g deTurckLieCovariantDerivativePairTracePermutation]
  simp only [lieCorrectionQuadraticZeroCoefficient, lieCorrectionCurvatureZeroCoefficient, slotExtendIter,
    slotExtend_sub, operatorFieldComposition_sub_right]
  module

theorem lieCorrectionQuadraticZeroCoefficient_metricPerturbationPath_jointlySmooth
    (g : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2)
    (hT : ∀ (x : M) (u v : TangentSpace I x),
      ccTensorBilin (I := I) g T x u v =
        ccTensorBilin (I := I) g T x v u)
    {δ : ℝ}
    (hδ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) δ)
    (hδZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g
        (0 : SmoothCcTensor g 0 2)) δ) :
    JointlySmoothCcTensorFamily (I := I) g 2 2
      (metricPerturbationPathDomain (δ := δ) (δ' := δ))
      (fun t => lieCorrectionQuadraticZeroCoefficient (I := I) (M := M) g
        (metricPerturbationPath (I := I) g T 0 hδ hδZ t)) := by
  let S := metricPerturbationPathDomain (δ := δ) (δ' := δ)
  have hlr := connectionDifferenceQuadraticCurvatureTerm_metricPerturbationPath_jointlySmooth (I := I) (M := M) g T hT hδ hδZ
  have hslot := jointlySmoothCcTensorFamily_slotExtendIter_two (I := I) (M := M) g hlr
  have hperm := jointlySmoothCcTensorFamily_const (I := I) (M := M) g (S := S)
    (permCoeff (I := I) (M := M) g deTurckLieCovariantDerivativePairTracePermutation)
  have hmid := jointlySmoothCcTensorFamily_ccOperatorFieldComp (I := I) (M := M) g hperm hslot
  have hpair := cometricDoublePairTraceCoefficient_metricPerturbationPath_jointlySmooth (I := I) (M := M) g T hδ hδZ
  simpa only [S, lieCorrectionQuadraticZeroCoefficient] using
    jointlySmoothCcTensorFamily_ccOperatorFieldComp (I := I) (M := M) g hpair hmid

noncomputable def lieCorrectionQuadraticFirstDerivativeIntermediateCoefficient
    (g gm : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2) :
    SmoothCcTensor g 3 6 :=
  ccOperatorFieldComp (I := I) (M := M) g 3 5 6
    (slotExtendIter (I := I) (M := M) g 3 4 2
      (connectionDifferenceQuadraticCurvatureDerivativeCoefficient (I := I) (M := M) g gm))
    (tensorThreeTwoProductCoefficient (I := I) (M := M) g T)

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
theorem lieCorrectionQuadraticFirstDerivativeIntermediateCoefficient_apply
    (g gm : SmoothRiemannianMetric I M)
    (D : SmoothCcTensor g 0 3) (W : SmoothCcTensor g 0 2) :
    operatorFieldApply (I := I) (M := M) g 3 6
        (lieCorrectionQuadraticFirstDerivativeIntermediateCoefficient (I := I) (M := M) g gm W) D =
      operatorFieldApply (I := I) (M := M) g 2 6
        (slotExtendIter (I := I) (M := M) g 0 4 2
          (operatorFieldApply (I := I) (M := M) g 3 4
            (connectionDifferenceQuadraticCurvatureDerivativeCoefficient (I := I) (M := M) g gm) D)) W := by
  have hprod : operatorFieldApply (I := I) (M := M) g 3 5
      (tensorThreeTwoProductCoefficient (I := I) (M := M) g W) D =
      operatorFieldApply (I := I) (M := M) g 2 5
        (slotExtendIter (I := I) (M := M) g 0 3 2 D) W := by
    simpa only [operatorFieldComposition_zero_eq_operatorFieldApply] using
      tensorThreeTwoProductCoefficient_apply (I := I) (M := M) g D W
  have hslot : ccOperatorFieldComp (I := I) (M := M) g 2 5 6
      (slotExtendIter (I := I) (M := M) g 3 4 2
        (connectionDifferenceQuadraticCurvatureDerivativeCoefficient (I := I) (M := M) g gm))
      (slotExtendIter (I := I) (M := M) g 0 3 2 D) =
      slotExtendIter (I := I) (M := M) g 0 4 2
        (operatorFieldApply (I := I) (M := M) g 3 4
          (connectionDifferenceQuadraticCurvatureDerivativeCoefficient (I := I) (M := M) g gm) D) := by
    simpa only [operatorFieldComposition_zero_eq_operatorFieldApply] using
      operatorFieldComposition_slotExtendIter_two_apply (I := I) (M := M) g 0 3 4
        (connectionDifferenceQuadraticCurvatureDerivativeCoefficient (I := I) (M := M) g gm) D
  rw [lieCorrectionQuadraticFirstDerivativeIntermediateCoefficient]
  calc
    _ = operatorFieldApply (I := I) (M := M) g 5 6
          (slotExtendIter (I := I) (M := M) g 3 4 2
            (connectionDifferenceQuadraticCurvatureDerivativeCoefficient (I := I) (M := M) g gm))
          (operatorFieldApply (I := I) (M := M) g 3 5
            (tensorThreeTwoProductCoefficient (I := I) (M := M) g W) D) :=
      (operatorFieldApplication_assoc (I := I) (M := M) g 3 5 6 _ _ _).symm
    _ = operatorFieldApply (I := I) (M := M) g 5 6
          (slotExtendIter (I := I) (M := M) g 3 4 2
            (connectionDifferenceQuadraticCurvatureDerivativeCoefficient (I := I) (M := M) g gm))
          (operatorFieldApply (I := I) (M := M) g 2 5
            (slotExtendIter (I := I) (M := M) g 0 3 2 D) W) := by
      rw [hprod]
    _ = operatorFieldApply (I := I) (M := M) g 2 6
          (ccOperatorFieldComp (I := I) (M := M) g 2 5 6
            (slotExtendIter (I := I) (M := M) g 3 4 2
              (connectionDifferenceQuadraticCurvatureDerivativeCoefficient (I := I) (M := M) g gm))
            (slotExtendIter (I := I) (M := M) g 0 3 2 D)) W :=
      operatorFieldApplication_assoc (I := I) (M := M) g 2 5 6 _ _ _
    _ = _ := by rw [hslot]

theorem lieCorrectionQuadraticFirstDerivativeIntermediateCoefficient_metricPerturbationPath_jointlySmooth
    (g : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2)
    {δ : ℝ}
    (hδ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) δ)
    (hδZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g
        (0 : SmoothCcTensor g 0 2)) δ) :
    JointlySmoothCcTensorFamily (I := I) g 3 6
      (metricPerturbationPathDomain (δ := δ) (δ' := δ))
      (fun t => lieCorrectionQuadraticFirstDerivativeIntermediateCoefficient (I := I) (M := M) g
        (metricPerturbationPath (I := I) g T 0 hδ hδZ t) T) := by
  let S := metricPerturbationPathDomain (δ := δ) (δ' := δ)
  apply contMDiffOn_clm_section_of_pointwise_jointMR (I := I) (M := M)
    (F₁ := Tensor0SModel 3 ℝ E) (V₁ := fun x : M => Tensor0SSpace 3 I x)
    (F₂ := Tensor0SModel 6 ℝ E) (V₂ := fun x : M => Tensor0SSpace 6 I x)
    (φ := fun q : M × ℝ =>
      (lieCorrectionQuadraticFirstDerivativeIntermediateCoefficient (I := I) (M := M) g
        (metricPerturbationPath (I := I) g T 0 hδ hδZ q.2) T).toSection q.1)
    (S := S)
  intro Y
  have hY : ContMDiffOn (I.prod 𝓘(ℝ, ℝ))
      (I.prod 𝓘(ℝ, Tensor0SModel 3 ℝ E)) ∞
      (fun q : M × ℝ => TotalSpace.mk' (Tensor0SModel 3 ℝ E)
        (E := fun x : M => Tensor0SSpace 3 I x) q.1 (Y q.1))
      ((Set.univ : Set M) ×ˢ S) :=
    Y.contMDiff.comp_contMDiffOn contMDiffOn_fst
  have hQ := connectionDifferenceQuadraticCurvatureDerivativeCoefficient_metricPerturbationPath_jointlySmooth (I := I) (M := M) g T hδ hδZ
  have hQY := ContMDiffOn.clm_bundle_apply (b := Prod.fst) hQ hY
  have hT := jointlySmoothCcTensorFamily_const (I := I) (M := M) g (S := S) T
  have hunit : ContMDiffOn (I.prod 𝓘(ℝ, ℝ))
      (I.prod 𝓘(ℝ, Tensor0SModel 0 ℝ E)) ∞
      (fun q : M × ℝ => TotalSpace.mk' (Tensor0SModel 0 ℝ E)
        (E := fun x : M => Tensor0SSpace 0 I x) q.1
        (unitTensor (I := I) (M := M) q.1))
      ((Set.univ : Set M) ×ˢ S) :=
    (unitZeroSec (I := I) (M := M)).contMDiff.comp_contMDiffOn
      contMDiffOn_fst
  have hTv := ContMDiffOn.clm_bundle_apply (b := Prod.fst) hT hunit
  have hprod := jointTensor0SProd_local (I := I) (p := 2) (q := 4)
    (S := S)
    (fun q : M × ℝ =>
      (show Tensor0SSpace 0 I q.1 →L[ℝ] Tensor0SSpace 2 I q.1 from
        T.toSection q.1) (unitTensor (I := I) (M := M) q.1))
    (fun q : M × ℝ =>
      (show Tensor0SSpace 3 I q.1 →L[ℝ] Tensor0SSpace 4 I q.1 from
        (connectionDifferenceQuadraticCurvatureDerivativeCoefficient (I := I) (M := M) g
          (metricPerturbationPath (I := I) g T 0 hδ hδZ q.2)).toSection q.1)
        (Y q.1)) hTv hQY
  have hprod' : ContMDiffOn (I.prod 𝓘(ℝ, ℝ))
      (I.prod 𝓘(ℝ, Tensor0SModel 6 ℝ E)) ∞
      (fun q : M × ℝ => TotalSpace.mk' (Tensor0SModel 6 ℝ E)
        (E := fun x : M => Tensor0SSpace 6 I x) q.1
        (tensor0SProdKappaFib (I := I) (p := 2) (q := 4) q.1
          ((show Tensor0SSpace 3 I q.1 →L[ℝ] Tensor0SSpace 4 I q.1 from
            (connectionDifferenceQuadraticCurvatureDerivativeCoefficient (I := I) (M := M) g
              (metricPerturbationPath (I := I) g T 0 hδ hδZ q.2)).toSection q.1)
            (Y q.1))
          ((show Tensor0SSpace 0 I q.1 →L[ℝ] Tensor0SSpace 2 I q.1 from
            T.toSection q.1) (unitTensor (I := I) (M := M) q.1))))
      ((Set.univ : Set M) ×ˢ S) := by
    refine hprod.congr (fun q _ => ?_)
    refine congrArg (fun z => TotalSpace.mk' (Tensor0SModel 6 ℝ E)
      (E := fun x : M => Tensor0SSpace 6 I x) q.1 z) ?_
    rw [tensor0SProdKappaFib_apply]
  refine hprod'.congr (fun q _ => ?_)
  refine congrArg (fun z => TotalSpace.mk' (Tensor0SModel 6 ℝ E)
    (E := fun x : M => Tensor0SSpace 6 I x) q.1 z) ?_
  let D := smoothCcTensorOfCovariantSection (I := I) (M := M) g Y
  have hmid := lieCorrectionQuadraticFirstDerivativeIntermediateCoefficient_apply (I := I) (M := M) g
    (metricPerturbationPath (I := I) g T 0 hδ hδZ q.2) D T
  have hval := congrArg
    (fun A : SmoothCcTensor g 0 6 =>
      (show Tensor0SSpace 0 I q.1 →L[ℝ] Tensor0SSpace 6 I q.1 from
        A.toSection q.1) (unitTensor (I := I) (M := M) q.1)) hmid
  have hD : D.toSection q.1 (unitTensor (I := I) (M := M) q.1) =
      Y q.1 := smoothCcTensorOfCovariantSection_apply_unitTensor (I := I) (M := M) g Y q.1
  simp only [operatorFieldApplication_toSection, ContinuousLinearMap.comp_apply] at hval
  rw [hD] at hval
  rw [slotExtendIter_two_zero_four_apply] at hval
  simp only [operatorFieldApplication_toSection, ContinuousLinearMap.comp_apply] at hval
  rw [hD] at hval
  exact hval

noncomputable def lieCorrectionQuadraticFirstDerivativeCoefficient
    (g gm : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2) :
    SmoothCcTensor g 3 2 :=
  ccOperatorFieldComp (I := I) (M := M) g 3 6 2
    (cometricDoublePairTraceCoefficient (I := I) (M := M) g gm)
    (ccOperatorFieldComp (I := I) (M := M) g 3 6 6
      (permCoeff (I := I) (M := M) g deTurckLieCovariantDerivativePairTracePermutation)
      (lieCorrectionQuadraticFirstDerivativeIntermediateCoefficient (I := I) (M := M) g gm T))

set_option backward.isDefEq.respectTransparency false in
omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] [SigmaCompactSpace M] in
theorem operatorFieldComposition_smul_left
    (g : SmoothRiemannianMetric I M) (a b c : ℕ)
    (s : ℝ) (Φ : SmoothCcTensor g b c) (W : SmoothCcTensor g a b) :
    ccOperatorFieldComp (I := I) (M := M) g a b c (s • Φ) W =
      s • ccOperatorFieldComp (I := I) (M := M) g a b c Φ W := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rw [show ((s • ccOperatorFieldComp (I := I) (M := M) g a b c Φ W).toSection x) =
      s • (ccOperatorFieldComp (I := I) (M := M) g a b c Φ W).toSection x from by
    rw [SmoothCcTensor.toSection_smul]
    rfl]
  rw [operatorFieldComposition_toSection, operatorFieldComposition_toSection]
  rw [show ((s • Φ).toSection x : TensorRSSpace b c I x) =
      s • Φ.toSection x from by
    rw [SmoothCcTensor.toSection_smul]
    rfl]
  rw [ContinuousLinearMap.smul_comp]

set_option backward.isDefEq.respectTransparency false in
omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] [SigmaCompactSpace M] in
theorem slotExtend_smul
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (a : ℝ) (X : SmoothCcTensor g r s) :
    slotExtend (I := I) (M := M) g r s (a • X) =
      a • slotExtend (I := I) (M := M) g r s X := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  apply ContinuousLinearMap.ext
  intro D
  rw [show ((a • slotExtend (I := I) (M := M) g r s X).toSection x) =
      a • (slotExtend (I := I) (M := M) g r s X).toSection x from by
    rw [SmoothCcTensor.toSection_smul]
    rfl]
  rw [ContinuousLinearMap.smul_apply]
  rw [show ((slotExtend (I := I) (M := M) g r s (a • X)).toSection x) D =
      (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s x).symm
        ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from
          (a • X).toSection x).comp
          (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) r x D)) from rfl]
  rw [show ((slotExtend (I := I) (M := M) g r s X).toSection x) D =
      (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s x).symm
        ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from
          X.toSection x).comp
          (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) r x D)) from rfl]
  rw [show ((a • X).toSection x : TensorRSSpace r s I x) =
      a • X.toSection x from by
    rw [SmoothCcTensor.toSection_smul]
    rfl]
  rw [ContinuousLinearMap.smul_comp, map_smul]

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] [SigmaCompactSpace M] in
theorem slotExtendIter_smul
    (g : SmoothRiemannianMetric I M) (r s w : ℕ)
    (a : ℝ) (X : SmoothCcTensor g r s) :
    slotExtendIter (I := I) (M := M) g r s w (a • X) =
      a • slotExtendIter (I := I) (M := M) g r s w X := by
  induction w with
  | zero => simp only [slotExtendIter]
  | succ w ih =>
      change slotExtend (I := I) (M := M) g (r + w) (s + w)
          (slotExtendIter (I := I) (M := M) g r s w (a • X)) = _
      rw [ih, slotExtend_smul]
      rfl

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] [SigmaCompactSpace M] in
theorem tensorThreeTwoProductCoefficient_smul
    (g : SmoothRiemannianMetric I M) (a : ℝ)
    (W : SmoothCcTensor g 0 2) :
    tensorThreeTwoProductCoefficient (I := I) (M := M) g (a • W) =
      a • tensorThreeTwoProductCoefficient (I := I) (M := M) g W := by
  rw [tensorThreeTwoProductCoefficient, slotExtendIter_smul]
  rw [operatorFieldComposition_smul_right]
  rfl

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem connectionDifferenceInsertionInnerDerivativeCoefficient_smul
    (g : SmoothRiemannianMetric I M) (a : ℝ)
    (W : SmoothCcTensor g 0 2) :
    connectionDifferenceInsertionInnerDerivativeCoefficient (I := I) (M := M) g (a • W) =
      a • connectionDifferenceInsertionInnerDerivativeCoefficient (I := I) (M := M) g W := by
  rw [connectionDifferenceInsertionInnerDerivativeCoefficient, symmRaiseEndo_smul, slotInsertEndoCc_smul,
    operatorFieldComposition_smul_left]
  rfl

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem connectionDifferenceInsertionInnerActionCoefficient_smul
    (g gm : SmoothRiemannianMetric I M) (a : ℝ)
    (W : SmoothCcTensor g 0 2) :
    connectionDifferenceInsertionInnerActionCoefficient (I := I) (M := M) g gm (a • W) =
      a • connectionDifferenceInsertionInnerActionCoefficient (I := I) (M := M) g gm W := by
  rw [connectionDifferenceInsertionInnerActionCoefficient, connectionDifferenceInsertionInnerDerivativeCoefficient_smul, operatorFieldComposition_smul_left]
  rfl

omit [NeZero (Module.finrank ℝ E)] in
theorem ricciQuadraticKernelDerivativeNestedTerm_smul
    (g gm : SmoothRiemannianMetric I M) (a : ℝ)
    (W : SmoothCcTensor g 0 2)
    (mid : Equiv.Perm (Fin 3)) (out : Equiv.Perm (Fin 4)) :
    ricciQuadraticKernelDerivativeNestedTerm (I := I) (M := M) g gm (a • W) mid out =
      a • ricciQuadraticKernelDerivativeNestedTerm (I := I) (M := M) g gm W mid out := by
  simp only [ricciQuadraticKernelDerivativeNestedTerm, connectionDifferenceInsertionInnerActionCoefficient_smul, operatorFieldComposition_smul_right]

omit [NeZero (Module.finrank ℝ E)] in
theorem ricciQuadraticKernelDerivativeBareTerm_smul
    (g gm : SmoothRiemannianMetric I M) (a : ℝ)
    (W : SmoothCcTensor g 0 2) (out : Equiv.Perm (Fin 4)) :
    ricciQuadraticKernelDerivativeBareTerm (I := I) (M := M) g gm (a • W) out =
      a • ricciQuadraticKernelDerivativeBareTerm (I := I) (M := M) g gm W out := by
  simp only [ricciQuadraticKernelDerivativeBareTerm, connectionDifferenceInsertionInnerActionCoefficient_smul, operatorFieldComposition_smul_right]

omit [NeZero (Module.finrank ℝ E)] in
theorem ricciQuadraticKernelDerivativeCoefficient_smul
    (g gm : SmoothRiemannianMetric I M) (a : ℝ)
    (W : SmoothCcTensor g 0 2) :
    ricciQuadraticKernelDerivativeCoefficient (I := I) (M := M) g gm (a • W) =
      a • ricciQuadraticKernelDerivativeCoefficient (I := I) (M := M) g gm W := by
  simp only [ricciQuadraticKernelDerivativeCoefficient, ricciQuadraticKernelDerivativeNestedTerm_smul, ricciQuadraticKernelDerivativeBareTerm_smul]
  module

omit [NeZero (Module.finrank ℝ E)] in
theorem ricciConnectionDifferenceQuadraticDerivativeCoefficient_smul
    (g gm : SmoothRiemannianMetric I M) (a : ℝ)
    (W : SmoothCcTensor g 0 2) :
    ricciConnectionDifferenceQuadraticDerivativeCoefficient (I := I) (M := M) g gm (a • W) =
      a • ricciConnectionDifferenceQuadraticDerivativeCoefficient (I := I) (M := M) g gm W := by
  rw [ricciConnectionDifferenceQuadraticDerivativeCoefficient, ricciQuadraticKernelDerivativeCoefficient_smul]
  rw [operatorFieldComposition_smul_right]
  rfl

omit [BoundarylessManifold I M] [SigmaCompactSpace M] in
theorem ricciConnectionDifferenceDerivativeTransposedCoefficient_smul
    (g gm : SmoothRiemannianMetric I M) (a : ℝ)
    (W : SmoothCcTensor g 0 2) :
    RicciDeTurckLowOrder.ricciConnectionDifferenceDerivativeTransposedCoefficient (I := I) (M := M) g gm (a • W) =
      a • RicciDeTurckLowOrder.ricciConnectionDifferenceDerivativeTransposedCoefficient (I := I) (M := M) g gm W := by
  simp only [RicciDeTurckLowOrder.ricciConnectionDifferenceDerivativeTransposedCoefficient, RicciDeTurckLowOrder.ricciConnectionDifferenceDerivativeTransposedMonomial,
    RicciDeTurckLowOrder.ricciConnectionDifferenceDerivativeMetricWeight, operatorFieldApplication_smul_right,
    curvatureDecompositionMonomialCoeffField_unitValue_smul]
  module

omit [BoundarylessManifold I M] in
theorem ricciConnectionDerivativeTransposedCoefficient_smul
    (g gm : SmoothRiemannianMetric I M) (a : ℝ)
    (W : SmoothCcTensor g 0 2) :
    RicciDeTurckLowOrder.ricciConnectionDerivativeTransposedCoefficient (I := I) (M := M) g gm (a • W) =
      a • RicciDeTurckLowOrder.ricciConnectionDerivativeTransposedCoefficient (I := I) (M := M) g gm W := by
  rw [RicciDeTurckLowOrder.ricciConnectionDerivativeTransposedCoefficient, ricciConnectionDifferenceDerivativeTransposedCoefficient_smul, operatorFieldComposition_smul_left]
  rfl

theorem ricciConnectionDifferenceDerivativeCoefficient_smul
    (g gm : SmoothRiemannianMetric I M) (a : ℝ)
    (W : SmoothCcTensor g 0 2) :
    ricciConnectionDifferenceDerivativeCoefficient (I := I) (M := M) g gm (a • W) =
      a • ricciConnectionDifferenceDerivativeCoefficient (I := I) (M := M) g gm W := by
  simp only [ricciConnectionDifferenceDerivativeCoefficient, ricciConnectionDifferenceQuadraticDerivativeCoefficient_smul, symmS_smul, ricciConnectionDerivativeTransposedCoefficient_smul]
  module

set_option backward.isDefEq.respectTransparency false in
omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] [SigmaCompactSpace M] in
theorem cometricRaiseSlot0Field_smul
    (g : SmoothRiemannianMetric I M) (s : ℕ) (a : ℝ)
    (W : SmoothCcTensor g 0 (s + 2)) :
    cometricRaiseSlot0Field (I := I) (M := M) g s (a • W) =
      a • cometricRaiseSlot0Field (I := I) (M := M) g s W := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rw [show ((a • cometricRaiseSlot0Field (I := I) (M := M) g s W).toSection x) =
      a • (cometricRaiseSlot0Field (I := I) (M := M) g s W).toSection x from by
    rw [SmoothCcTensor.toSection_smul]
    rfl]
  rw [cometricRaiseSlot0Field_toSection, cometricRaiseSlot0Field_toSection]
  rw [show ((a • W).toSection x : TensorRSSpace 0 (s + 2) I x) =
      a • W.toSection x from by
    rw [SmoothCcTensor.toSection_smul]
    rfl]
  rw [ContinuousLinearMap.smul_apply]
  apply ContinuousLinearMap.ext
  intro om
  rw [ContinuousLinearMap.smul_apply,
    cometricRaiseSlot0Fib_clm_apply, cometricRaiseSlot0Fib_clm_apply]
  rw [map_smul]

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
theorem lieCorrectionZeroVectorBundleUnscaledDerivativeCoefficient_smul
    (g gm : SmoothRiemannianMetric I M) (a : ℝ)
    (W : SmoothCcTensor g 0 2) :
    lieCorrectionZeroVectorBundleUnscaledDerivativeCoefficient (I := I) (M := M) g gm (a • W) =
      a • lieCorrectionZeroVectorBundleUnscaledDerivativeCoefficient (I := I) (M := M) g gm W := by
  simp only [lieCorrectionZeroVectorBundleUnscaledDerivativeCoefficient, cometricRaiseSlot0Field_smul, operatorFieldComposition_smul_left, operatorFieldComposition_smul_right]

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
theorem lieCorrectionZeroVectorBundleDerivativeCoefficient_smul
    (g gm : SmoothRiemannianMetric I M) (a : ℝ)
    (W : SmoothCcTensor g 0 2) :
    lieCorrectionZeroVectorBundleDerivativeCoefficient (I := I) (M := M) g gm (a • W) =
      a • lieCorrectionZeroVectorBundleDerivativeCoefficient (I := I) (M := M) g gm W := by
  simp only [lieCorrectionZeroVectorBundleDerivativeCoefficient, lieCorrectionZeroVectorBundleUnscaledDerivativeCoefficient_smul]
  module

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
theorem lieCorrectionZeroMixedConnectionHalfDerivativeCoefficient_smul
    (g gm gB : SmoothRiemannianMetric I M) (a : ℝ)
    (W : SmoothCcTensor g 0 2) (σ : Equiv.Perm (Fin 4)) :
    lieCorrectionZeroMixedConnectionHalfDerivativeCoefficient (I := I) (M := M) g gm gB (a • W) σ =
      a • lieCorrectionZeroMixedConnectionHalfDerivativeCoefficient (I := I) (M := M) g gm gB W σ := by
  simp only [lieCorrectionZeroMixedConnectionHalfDerivativeCoefficient, tensorThreeTwoProductCoefficient_smul, operatorFieldComposition_smul_left,
    operatorFieldComposition_smul_right]

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
theorem lieCorrectionZeroMixedConnectionDerivativeCoefficient_smul
    (g gm gB : SmoothRiemannianMetric I M) (a : ℝ)
    (W : SmoothCcTensor g 0 2) :
    lieCorrectionZeroMixedConnectionDerivativeCoefficient (I := I) (M := M) g gm gB (a • W) =
      a • lieCorrectionZeroMixedConnectionDerivativeCoefficient (I := I) (M := M) g gm gB W := by
  simp only [lieCorrectionZeroMixedConnectionDerivativeCoefficient, lieCorrectionZeroMixedConnectionHalfDerivativeCoefficient_smul]
  module

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
theorem lieCorrectionQuadraticFirstDerivativeIntermediateCoefficient_smul
    (g gm : SmoothRiemannianMetric I M) (a : ℝ)
    (W : SmoothCcTensor g 0 2) :
    lieCorrectionQuadraticFirstDerivativeIntermediateCoefficient (I := I) (M := M) g gm (a • W) =
      a • lieCorrectionQuadraticFirstDerivativeIntermediateCoefficient (I := I) (M := M) g gm W := by
  rw [lieCorrectionQuadraticFirstDerivativeIntermediateCoefficient, tensorThreeTwoProductCoefficient_smul]
  rw [operatorFieldComposition_smul_right]
  rfl

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
theorem lieCorrectionQuadraticFirstDerivativeCoefficient_smul
    (g gm : SmoothRiemannianMetric I M) (a : ℝ)
    (W : SmoothCcTensor g 0 2) :
    lieCorrectionQuadraticFirstDerivativeCoefficient (I := I) (M := M) g gm (a • W) =
      a • lieCorrectionQuadraticFirstDerivativeCoefficient (I := I) (M := M) g gm W := by
  simp only [lieCorrectionQuadraticFirstDerivativeCoefficient, lieCorrectionQuadraticFirstDerivativeIntermediateCoefficient_smul, operatorFieldComposition_smul_right]

theorem lieCorrectionQuadraticFirstDerivativeCoefficient_metricPerturbationPath_jointlySmooth
    (g : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2)
    {δ : ℝ}
    (hδ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) δ)
    (hδZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g
        (0 : SmoothCcTensor g 0 2)) δ) :
    JointlySmoothCcTensorFamily (I := I) g 3 2
      (metricPerturbationPathDomain (δ := δ) (δ' := δ))
      (fun t => lieCorrectionQuadraticFirstDerivativeCoefficient (I := I) (M := M) g
        (metricPerturbationPath (I := I) g T 0 hδ hδZ t) T) := by
  let S := metricPerturbationPathDomain (δ := δ) (δ' := δ)
  have hmid := lieCorrectionQuadraticFirstDerivativeIntermediateCoefficient_metricPerturbationPath_jointlySmooth (I := I) (M := M) g T hδ hδZ
  have hperm := jointlySmoothCcTensorFamily_const (I := I) (M := M) g (S := S)
    (permCoeff (I := I) (M := M) g deTurckLieCovariantDerivativePairTracePermutation)
  have hσ := jointlySmoothCcTensorFamily_ccOperatorFieldComp (I := I) (M := M) g hperm hmid
  have hpair := cometricDoublePairTraceCoefficient_metricPerturbationPath_jointlySmooth (I := I) (M := M) g T hδ hδZ
  simpa only [S, lieCorrectionQuadraticFirstDerivativeCoefficient] using
    jointlySmoothCcTensorFamily_ccOperatorFieldComp (I := I) (M := M) g hpair hσ

omit [NeZero (Module.finrank ℝ E)] in
theorem lieCorrectionQuadraticFirstDerivativeCoefficient_apply
    (g gm : SmoothRiemannianMetric I M)
    (P W : SmoothCcTensor g 0 2)
    (hP : ∀ (x : M) (u v : TangentSpace I x),
      ccTensorBilin (I := I) g P x u v =
        ccTensorBilin (I := I) g P x v u)
    (htie : ∀ (x : M) (u v : TangentSpace I x),
      gm.inner x u v =
        g.inner x u v + ccTensorBilinSymm (I := I) g P x u v) :
    operatorFieldApply (I := I) (M := M) g 2 2
        (lieCorrectionQuadraticZeroCoefficient (I := I) (M := M) g gm) W =
      operatorFieldApply (I := I) (M := M) g 3 2
        (lieCorrectionQuadraticFirstDerivativeCoefficient (I := I) (M := M) g gm W)
        (covGrad (I := I) (M := M) g 0 2 P) := by
  let dP := covGrad (I := I) (M := M) g 0 2 P
  let X := slotExtendIter (I := I) (M := M) g 0 4 2
    (connectionDifferenceQuadraticCurvatureTerm (I := I) (M := M) g gm)
  let Y := ccOperatorFieldComp (I := I) (M := M) g 3 5 6
    (slotExtendIter (I := I) (M := M) g 3 4 2
      (connectionDifferenceQuadraticCurvatureDerivativeCoefficient (I := I) (M := M) g gm))
    (tensorThreeTwoProductCoefficient (I := I) (M := M) g W)
  have hprod : operatorFieldApply (I := I) (M := M) g 3 5
      (tensorThreeTwoProductCoefficient (I := I) (M := M) g W) dP =
      operatorFieldApply (I := I) (M := M) g 2 5
        (slotExtendIter (I := I) (M := M) g 0 3 2 dP) W := by
    simpa only [operatorFieldComposition_zero_eq_operatorFieldApply] using
      tensorThreeTwoProductCoefficient_apply (I := I) (M := M) g dP W
  have hslot : ccOperatorFieldComp (I := I) (M := M) g 2 5 6
      (slotExtendIter (I := I) (M := M) g 3 4 2
        (connectionDifferenceQuadraticCurvatureDerivativeCoefficient (I := I) (M := M) g gm))
      (slotExtendIter (I := I) (M := M) g 0 3 2 dP) =
      slotExtendIter (I := I) (M := M) g 0 4 2
        (operatorFieldApply (I := I) (M := M) g 3 4
          (connectionDifferenceQuadraticCurvatureDerivativeCoefficient (I := I) (M := M) g gm) dP) := by
    simpa only [operatorFieldComposition_zero_eq_operatorFieldApply] using
      operatorFieldComposition_slotExtendIter_two_apply (I := I) (M := M) g 0 3 4
        (connectionDifferenceQuadraticCurvatureDerivativeCoefficient (I := I) (M := M) g gm) dP
  have hinner : operatorFieldApply (I := I) (M := M) g 3 6 Y dP =
      operatorFieldApply (I := I) (M := M) g 2 6 X W := by
    calc
      operatorFieldApply (I := I) (M := M) g 3 6 Y dP =
          operatorFieldApply (I := I) (M := M) g 5 6
            (slotExtendIter (I := I) (M := M) g 3 4 2
            (connectionDifferenceQuadraticCurvatureDerivativeCoefficient (I := I) (M := M) g gm))
            (operatorFieldApply (I := I) (M := M) g 3 5
              (tensorThreeTwoProductCoefficient (I := I) (M := M) g W) dP) :=
        (operatorFieldApplication_assoc (I := I) (M := M) g 3 5 6 _ _ _).symm
      _ = operatorFieldApply (I := I) (M := M) g 5 6
            (slotExtendIter (I := I) (M := M) g 3 4 2
              (connectionDifferenceQuadraticCurvatureDerivativeCoefficient (I := I) (M := M) g gm))
            (operatorFieldApply (I := I) (M := M) g 2 5
              (slotExtendIter (I := I) (M := M) g 0 3 2 dP) W) := by
        rw [hprod]
      _ = operatorFieldApply (I := I) (M := M) g 2 6
            (ccOperatorFieldComp (I := I) (M := M) g 2 5 6
              (slotExtendIter (I := I) (M := M) g 3 4 2
                (connectionDifferenceQuadraticCurvatureDerivativeCoefficient (I := I) (M := M) g gm))
              (slotExtendIter (I := I) (M := M) g 0 3 2 dP)) W :=
        operatorFieldApplication_assoc (I := I) (M := M) g 2 5 6 _ _ _
      _ = operatorFieldApply (I := I) (M := M) g 2 6
            (slotExtendIter (I := I) (M := M) g 0 4 2
              (operatorFieldApply (I := I) (M := M) g 3 4
                (connectionDifferenceQuadraticCurvatureDerivativeCoefficient (I := I) (M := M) g gm) dP)) W := by
        rw [hslot]
      _ = operatorFieldApply (I := I) (M := M) g 2 6 X W := by
        rw [connectionDifferenceQuadraticCurvatureDerivativeCoefficient_apply (I := I) (M := M) g gm P hP htie]
  rw [lieCorrectionQuadraticZeroCoefficient, lieCorrectionQuadraticFirstDerivativeCoefficient]
  change operatorFieldApply (I := I) (M := M) g 2 2
      (ccOperatorFieldComp (I := I) (M := M) g 2 6 2
        (cometricDoublePairTraceCoefficient (I := I) (M := M) g gm)
        (ccOperatorFieldComp (I := I) (M := M) g 2 6 6
          (permCoeff (I := I) (M := M) g deTurckLieCovariantDerivativePairTracePermutation) X)) W =
    operatorFieldApply (I := I) (M := M) g 3 2
      (ccOperatorFieldComp (I := I) (M := M) g 3 6 2
        (cometricDoublePairTraceCoefficient (I := I) (M := M) g gm)
        (ccOperatorFieldComp (I := I) (M := M) g 3 6 6
          (permCoeff (I := I) (M := M) g deTurckLieCovariantDerivativePairTracePermutation) Y)) dP
  calc
    _ = operatorFieldApply (I := I) (M := M) g 6 2
        (cometricDoublePairTraceCoefficient (I := I) (M := M) g gm)
        (operatorFieldApply (I := I) (M := M) g 2 6
          (ccOperatorFieldComp (I := I) (M := M) g 2 6 6
            (permCoeff (I := I) (M := M) g deTurckLieCovariantDerivativePairTracePermutation) X) W) :=
      (operatorFieldApplication_assoc (I := I) (M := M) g 2 6 2 _ _ _).symm
    _ = operatorFieldApply (I := I) (M := M) g 6 2
        (cometricDoublePairTraceCoefficient (I := I) (M := M) g gm)
        (operatorFieldApply (I := I) (M := M) g 6 6
          (permCoeff (I := I) (M := M) g deTurckLieCovariantDerivativePairTracePermutation)
          (operatorFieldApply (I := I) (M := M) g 2 6 X W)) := by
      congr 1
    _ = operatorFieldApply (I := I) (M := M) g 6 2
        (cometricDoublePairTraceCoefficient (I := I) (M := M) g gm)
        (operatorFieldApply (I := I) (M := M) g 6 6
          (permCoeff (I := I) (M := M) g deTurckLieCovariantDerivativePairTracePermutation)
          (operatorFieldApply (I := I) (M := M) g 3 6 Y dP)) := by
      rw [hinner]
    _ = operatorFieldApply (I := I) (M := M) g 6 2
        (cometricDoublePairTraceCoefficient (I := I) (M := M) g gm)
        (operatorFieldApply (I := I) (M := M) g 3 6
          (ccOperatorFieldComp (I := I) (M := M) g 3 6 6
            (permCoeff (I := I) (M := M) g deTurckLieCovariantDerivativePairTracePermutation) Y) dP) := by
      congr 1
    _ = _ :=
      operatorFieldApplication_assoc (I := I) (M := M) g 3 6 2 _ _ _

end RicciDeTurckPairing
end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral
