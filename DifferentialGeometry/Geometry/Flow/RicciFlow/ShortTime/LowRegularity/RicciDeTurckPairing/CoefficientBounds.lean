import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegularity.RicciDeTurckPairing.LinearTerms
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegularity.FirstOrderCoefficientLipschitzBounds
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.CovariantJetNaturality
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.OperatorFieldJetProduct

section

noncomputable section


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
  apply contMDiffOn_clm_section_of_apply (I := I) (M := M)
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
  let _ := tensorRSBundleTopology (𝕜 := ℝ) (E := E) (H := H)
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
  with_unfolding_all exact h

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] [SigmaCompactSpace M] in
theorem jointlySmoothCcTensorFamily_slotExtendIter_two
    (g : SmoothRiemannianMetric I M) {S : Set ℝ}
    {K : ℝ → SmoothCcTensor g 0 4}
    (hK : JointlySmoothCcTensorFamily (I := I) g 0 4 S K) :
    JointlySmoothCcTensorFamily (I := I) g 2 6 S
      (fun t => slotExtendIter (I := I) (M := M) g 0 4 2 (K t)) := by
  apply contMDiffOn_clm_section_of_apply (I := I) (M := M)
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

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
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
  refine h.congr (fun p _ => ?_)
  refine congrArg (fun z => TotalSpace.mk' (TensorRSModel 3 4 ℝ E)
    (E := fun x : M => TensorRSSpace 3 4 I x) p.1 z) ?_
  rw [connectionDifferenceContravariantInsertionField_toSection]

omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] [SigmaCompactSpace M] in
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
  apply contMDiffOn_clm_section_of_apply (I := I) (M := M)
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

omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] [SigmaCompactSpace M] in
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
  change JointlySmoothCcTensorFamily (I := I) g 3 3
    (metricPerturbationPathDomain (δ := δ) (δ' := δ))
    (fun t => ccOperatorFieldComp (I := I) (M := M) g 3 3 3
      (connectionDifferenceInsertionInnerDerivativeCoefficient (I := I) (M := M) g W)
      (RicciDeTurckLowOrder.connectionDifferenceLowOrderOperator (I := I) (M := M) g
        (metricPerturbationPath (I := I) g T 0 hδ hδZ t)))
  exact jointlySmoothCcTensorFamily_ccOperatorFieldComp (I := I) (M := M) g
    (jointlySmoothCcTensorFamily_const (I := I) (M := M) g
      (S := metricPerturbationPathDomain (δ := δ) (δ' := δ))
      (connectionDifferenceInsertionInnerDerivativeCoefficient (I := I) (M := M) g W))
    (RicciDeTurckLowOrder.connectionDifferenceLowOrderOperator_joint
      (I := I) (M := M) g T hδ hδZ)

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
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

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
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

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
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
    ricciQuadraticPermutationSwapZeroOne ricciQuadraticPermutationCycleZeroThreeOneTwo
  have h₁ := ricciQuadraticKernelDerivativeNestedTerm_metricPerturbationPath_jointlySmooth (I := I) (M := M) g T W hδ hδZ
    ricciQuadraticPermutationSwapZeroOne ricciQuadraticPermutationSwapBlocks
  have h₂ := ricciQuadraticKernelDerivativeNestedTerm_metricPerturbationPath_jointlySmooth (I := I) (M := M) g T W hδ hδZ
    ricciQuadraticPermutationRotateInputs ricciQuadraticPermutationCycleZeroThreeTwo
  have h₃ := ricciQuadraticKernelDerivativeBareTerm_metricPerturbationPath_jointlySmooth (I := I) (M := M) g T W hδ hδZ ricciQuadraticPermutationCycleZeroOneThreeTwo
  have h₄ := ricciQuadraticKernelDerivativeBareTerm_metricPerturbationPath_jointlySmooth (I := I) (M := M) g T W hδ hδZ ricciQuadraticPermutationCycleZeroOneTwo
  have h₅ := ricciQuadraticKernelDerivativeNestedTerm_metricPerturbationPath_jointlySmooth (I := I) (M := M) g T W hδ hδZ
    ricciQuadraticPermutationRotateInputs ricciQuadraticPermutationSwapZeroTwo
  have hker := jointlySmoothCcTensorFamily_add (I := I) (M := M) g
    (jointlySmoothCcTensorFamily_add (I := I) (M := M) g
      (jointlySmoothCcTensorFamily_add (I := I) (M := M) g
        (jointlySmoothCcTensorFamily_add (I := I) (M := M) g
          (jointlySmoothCcTensorFamily_add (I := I) (M := M) g h₀ h₁) h₂) h₃) h₄) h₅
  have htrace := ricciCometricFourTraceCastG0_metricPerturbationPath_jointlySmooth (I := I) (M := M) g T hδ hδZ
  have hout := jointlySmoothCcTensorFamily_ccOperatorFieldComp (I := I) (M := M) g htrace hker
  simpa only [ricciConnectionDifferenceQuadraticDerivativeCoefficient, ricciQuadraticKernelDerivativeCoefficient] using hout

omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] [SigmaCompactSpace M] in
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
  apply contMDiffOn_clm_section_of_apply (I := I) (M := M)
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

omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] [SigmaCompactSpace M] in
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
  apply contMDiffOn_clm_section_of_apply (I := I) (M := M)
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

omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] [SigmaCompactSpace M] in
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

omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] [SigmaCompactSpace M] in
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
  apply contMDiffOn_clm_section_of_apply (I := I) (M := M)
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

omit [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
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
  apply contMDiffOn_clm_section_of_apply (I := I) (M := M)
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

omit [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
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

omit [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
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
  apply contMDiffOn_clm_section_of_apply (I := I) (M := M)
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

omit [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
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

omit [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
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

omit [SigmaCompactSpace M] in
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

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless]
    [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma armSlotFib_toModel_apply (s : ℕ) (x : M)
    (Arm : TangentSpace I x →L[ℝ] (TangentSpace I x →L[ℝ] TangentSpace I x))
    (D : Tensor0SSpace (s + 1) I x) (v : Fin (s + 1 + 1) → E) :
    Tensor0SSpace.toModel (armSlotFib (I := I) (M := M) s x Arm D) v =
      Tensor0SSpace.toModel
        (DifferentialGeometry.Geometry.Curvature.slotInsertEndoFib
          (I := I) (M := M) (s + 1) 0 x
          (Arm ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm (v 0))) D)
        (Matrix.vecTail v) := by
  exact armSlotFib_apply_eval (I := I) (M := M) s x Arm D
    (fun i => (tangentSpaceModelContinuousLinearEquiv (I := I) x).symm (v i))

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [SigmaCompactSpace M] in
theorem deTurckLieCovariantDerivativeArmTwoCoefficient_eq_permuted_connectionDifferenceContravariantInsertionField
    (g gm : SmoothRiemannianMetric I M) :
    deTurckLieCovariantDerivativeArmTwoCoefficient (I := I) (M := M) g gm =
      ccOperatorFieldComp (I := I) (M := M) g 3 4 4
        (permCoeff (I := I) (M := M) g ricciQuadraticPermutationSwapBlocks)
        (connectionDifferenceContravariantInsertionField (I := I) g gm) := by
  rw [operatorFieldComposition_permutationCoefficient_apply_eq_rsDomDomCongrSection (I := I) (M := M) g ricciQuadraticPermutationSwapBlocks]
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
      ((rsDomDomCongr ricciQuadraticPermutationSwapBlocks
        ((connectionDifferenceContravariantInsertionField (I := I) g gm).toSection x)) D) v
  rw [armSlotFib_toModel_apply, slotInsertEndoFib_apply_eval]
  rw [toModel_rsDomDomCongr_apply,
    ContinuousMultilinearMap.domDomCongr_apply]
  rw [connectionDifferenceContravariantInsertionField_toSection, connContr21_insert]
  rw [connectionDifferenceEndomorphism_apply]
  congr 1
  funext k
  fin_cases k <;> simp [ricciQuadraticPermutationSwapBlocks] <;> rfl

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
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
    (permCoeff (I := I) (M := M) g ricciQuadraticPermutationSwapBlocks)
  have hi := connectionDifferenceContravariantInsertionField_metricPerturbationPath_jointlySmooth (I := I) (M := M) g T hδ hδZ
  have hout := jointlySmoothCcTensorFamily_ccOperatorFieldComp (I := I) (M := M) g hp hi
  simpa only [S, deTurckLieCovariantDerivativeArmTwoCoefficient_eq_permuted_connectionDifferenceContravariantInsertionField] using hout

omit [BoundarylessManifold I M] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
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

omit [BoundarylessManifold I M] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
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

omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] [SigmaCompactSpace M] in
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

omit [SigmaCompactSpace M] in
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

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
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

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
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

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
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

omit [SigmaCompactSpace M] in
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

omit [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
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
      smul_apply, smul_eq_mul]
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

omit [SigmaCompactSpace M] in
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

omit [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
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
omit [I.Boundaryless] in
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

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
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
  apply contMDiffOn_clm_section_of_apply (I := I) (M := M)
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
  rw [slotExtendIter_two_zero_four_apply] at hval
  simp only [operatorFieldApplication_toSection, ContinuousLinearMap.comp_apply] at hval
  generalize hddef : D.toSection q.1
    (unitTensor (I := I) (M := M) q.1) = d at hval
  have hd : d = Y q.1 := hddef.symm.trans hD
  rw [hd] at hval
  exact hval

noncomputable def lieCorrectionQuadraticFirstDerivativeCoefficient
    (g gm : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2) :
    SmoothCcTensor g 3 2 :=
  ccOperatorFieldComp (I := I) (M := M) g 3 6 2
    (cometricDoublePairTraceCoefficient (I := I) (M := M) g gm)
    (ccOperatorFieldComp (I := I) (M := M) g 3 6 6
      (permCoeff (I := I) (M := M) g deTurckLieCovariantDerivativePairTracePermutation)
      (lieCorrectionQuadraticFirstDerivativeIntermediateCoefficient (I := I) (M := M) g gm T))

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
  rw [smul_apply]
  rw [show ((slotExtend (I := I) (M := M) g r s (a • X)).toSection x) D =
      (tensor0SCurry (I := I) (M := M) (𝕜 := ℝ) s x).symm
        ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from
          (a • X).toSection x).comp
          (tensor0SCurry (I := I) (M := M) (𝕜 := ℝ) r x D)) from rfl]
  rw [show ((slotExtend (I := I) (M := M) g r s X).toSection x) D =
      (tensor0SCurry (I := I) (M := M) (𝕜 := ℝ) s x).symm
        ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from
          X.toSection x).comp
          (tensor0SCurry (I := I) (M := M) (𝕜 := ℝ) r x D)) from rfl]
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
omit [I.Boundaryless] [SigmaCompactSpace M] in
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
omit [I.Boundaryless] [SigmaCompactSpace M] in
theorem connectionDifferenceInsertionInnerActionCoefficient_smul
    (g gm : SmoothRiemannianMetric I M) (a : ℝ)
    (W : SmoothCcTensor g 0 2) :
    connectionDifferenceInsertionInnerActionCoefficient (I := I) (M := M) g gm (a • W) =
      a • connectionDifferenceInsertionInnerActionCoefficient (I := I) (M := M) g gm W := by
  rw [connectionDifferenceInsertionInnerActionCoefficient, connectionDifferenceInsertionInnerDerivativeCoefficient_smul, operatorFieldComposition_smul_left]
  rfl

omit [NeZero (Module.finrank ℝ E)] in
omit [I.Boundaryless] [SigmaCompactSpace M] in
theorem ricciQuadraticKernelDerivativeNestedTerm_smul
    (g gm : SmoothRiemannianMetric I M) (a : ℝ)
    (W : SmoothCcTensor g 0 2)
    (mid : Equiv.Perm (Fin 3)) (out : Equiv.Perm (Fin 4)) :
    ricciQuadraticKernelDerivativeNestedTerm (I := I) (M := M) g gm (a • W) mid out =
      a • ricciQuadraticKernelDerivativeNestedTerm (I := I) (M := M) g gm W mid out := by
  simp only [ricciQuadraticKernelDerivativeNestedTerm, connectionDifferenceInsertionInnerActionCoefficient_smul, operatorFieldComposition_smul_right]

omit [NeZero (Module.finrank ℝ E)] in
omit [I.Boundaryless] [SigmaCompactSpace M] in
theorem ricciQuadraticKernelDerivativeBareTerm_smul
    (g gm : SmoothRiemannianMetric I M) (a : ℝ)
    (W : SmoothCcTensor g 0 2) (out : Equiv.Perm (Fin 4)) :
    ricciQuadraticKernelDerivativeBareTerm (I := I) (M := M) g gm (a • W) out =
      a • ricciQuadraticKernelDerivativeBareTerm (I := I) (M := M) g gm W out := by
  simp only [ricciQuadraticKernelDerivativeBareTerm, connectionDifferenceInsertionInnerActionCoefficient_smul, operatorFieldComposition_smul_right]

omit [NeZero (Module.finrank ℝ E)] in
omit [I.Boundaryless] [SigmaCompactSpace M] in
theorem ricciQuadraticKernelDerivativeCoefficient_smul
    (g gm : SmoothRiemannianMetric I M) (a : ℝ)
    (W : SmoothCcTensor g 0 2) :
    ricciQuadraticKernelDerivativeCoefficient (I := I) (M := M) g gm (a • W) =
      a • ricciQuadraticKernelDerivativeCoefficient (I := I) (M := M) g gm W := by
  simp only [ricciQuadraticKernelDerivativeCoefficient, ricciQuadraticKernelDerivativeNestedTerm_smul, ricciQuadraticKernelDerivativeBareTerm_smul]
  module

omit [NeZero (Module.finrank ℝ E)] in
omit [I.Boundaryless] [SigmaCompactSpace M] in
theorem ricciConnectionDifferenceQuadraticDerivativeCoefficient_smul
    (g gm : SmoothRiemannianMetric I M) (a : ℝ)
    (W : SmoothCcTensor g 0 2) :
    ricciConnectionDifferenceQuadraticDerivativeCoefficient (I := I) (M := M) g gm (a • W) =
      a • ricciConnectionDifferenceQuadraticDerivativeCoefficient (I := I) (M := M) g gm W := by
  rw [ricciConnectionDifferenceQuadraticDerivativeCoefficient, ricciQuadraticKernelDerivativeCoefficient_smul]
  rw [operatorFieldComposition_smul_right]
  rfl

omit [BoundarylessManifold I M] [SigmaCompactSpace M] in
omit [I.Boundaryless] in
theorem ricciConnectionDifferenceDerivativeTransposedCoefficient_smul
    (g gm : SmoothRiemannianMetric I M) (a : ℝ)
    (W : SmoothCcTensor g 0 2) :
    RicciDeTurckLowOrder.ricciConnectionDifferenceDerivativeTransposedCoefficient (I := I) (M := M) g gm (a • W) =
      a • RicciDeTurckLowOrder.ricciConnectionDifferenceDerivativeTransposedCoefficient (I := I) (M := M) g gm W := by
  simp only [RicciDeTurckLowOrder.ricciConnectionDifferenceDerivativeTransposedCoefficient, RicciDeTurckLowOrder.ricciConnectionDifferenceDerivativeTransposedMonomial,
    RicciDeTurckLowOrder.ricciConnectionDifferenceDerivativeMetricWeight, operatorFieldApplication_smul_right,
    curvatureDecompositionMonomialCoeffField_unitValue_smul]
  module

omit [BoundarylessManifold I M] [SigmaCompactSpace M] in
theorem ricciConnectionDerivativeTransposedCoefficient_smul
    (g gm : SmoothRiemannianMetric I M) (a : ℝ)
    (W : SmoothCcTensor g 0 2) :
    RicciDeTurckLowOrder.ricciConnectionDerivativeTransposedCoefficient (I := I) (M := M) g gm (a • W) =
      a • RicciDeTurckLowOrder.ricciConnectionDerivativeTransposedCoefficient (I := I) (M := M) g gm W := by
  rw [RicciDeTurckLowOrder.ricciConnectionDerivativeTransposedCoefficient, ricciConnectionDifferenceDerivativeTransposedCoefficient_smul, operatorFieldComposition_smul_left]
  rfl

omit [SigmaCompactSpace M] in
theorem ricciConnectionDifferenceDerivativeCoefficient_smul
    (g gm : SmoothRiemannianMetric I M) (a : ℝ)
    (W : SmoothCcTensor g 0 2) :
    ricciConnectionDifferenceDerivativeCoefficient (I := I) (M := M) g gm (a • W) =
      a • ricciConnectionDifferenceDerivativeCoefficient (I := I) (M := M) g gm W := by
  simp only [ricciConnectionDifferenceDerivativeCoefficient, ricciConnectionDifferenceQuadraticDerivativeCoefficient_smul, symmS_smul, ricciConnectionDerivativeTransposedCoefficient_smul]
  module

omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] [SigmaCompactSpace M] in
omit [I.Boundaryless] in
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
  rw [smul_apply]
  apply ContinuousLinearMap.ext
  intro om
  rw [smul_apply,
    cometricRaiseSlot0Fib_clm_apply, cometricRaiseSlot0Fib_clm_apply]
  rw [map_smul]

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
omit [I.Boundaryless] in
theorem lieCorrectionZeroVectorBundleUnscaledDerivativeCoefficient_smul
    (g gm : SmoothRiemannianMetric I M) (a : ℝ)
    (W : SmoothCcTensor g 0 2) :
    lieCorrectionZeroVectorBundleUnscaledDerivativeCoefficient (I := I) (M := M) g gm (a • W) =
      a • lieCorrectionZeroVectorBundleUnscaledDerivativeCoefficient (I := I) (M := M) g gm W := by
  simp only [lieCorrectionZeroVectorBundleUnscaledDerivativeCoefficient, cometricRaiseSlot0Field_smul, operatorFieldComposition_smul_left, operatorFieldComposition_smul_right]

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
omit [I.Boundaryless] in
theorem lieCorrectionZeroVectorBundleDerivativeCoefficient_smul
    (g gm : SmoothRiemannianMetric I M) (a : ℝ)
    (W : SmoothCcTensor g 0 2) :
    lieCorrectionZeroVectorBundleDerivativeCoefficient (I := I) (M := M) g gm (a • W) =
      a • lieCorrectionZeroVectorBundleDerivativeCoefficient (I := I) (M := M) g gm W := by
  simp only [lieCorrectionZeroVectorBundleDerivativeCoefficient, lieCorrectionZeroVectorBundleUnscaledDerivativeCoefficient_smul]
  module

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
omit [I.Boundaryless] in
theorem lieCorrectionZeroMixedConnectionHalfDerivativeCoefficient_smul
    (g gm gB : SmoothRiemannianMetric I M) (a : ℝ)
    (W : SmoothCcTensor g 0 2) (σ : Equiv.Perm (Fin 4)) :
    lieCorrectionZeroMixedConnectionHalfDerivativeCoefficient (I := I) (M := M) g gm gB (a • W) σ =
      a • lieCorrectionZeroMixedConnectionHalfDerivativeCoefficient (I := I) (M := M) g gm gB W σ := by
  simp only [lieCorrectionZeroMixedConnectionHalfDerivativeCoefficient, tensorThreeTwoProductCoefficient_smul, operatorFieldComposition_smul_left,
    operatorFieldComposition_smul_right]

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
omit [I.Boundaryless] in
theorem lieCorrectionZeroMixedConnectionDerivativeCoefficient_smul
    (g gm gB : SmoothRiemannianMetric I M) (a : ℝ)
    (W : SmoothCcTensor g 0 2) :
    lieCorrectionZeroMixedConnectionDerivativeCoefficient (I := I) (M := M) g gm gB (a • W) =
      a • lieCorrectionZeroMixedConnectionDerivativeCoefficient (I := I) (M := M) g gm gB W := by
  simp only [lieCorrectionZeroMixedConnectionDerivativeCoefficient, lieCorrectionZeroMixedConnectionHalfDerivativeCoefficient_smul]
  module

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
omit [I.Boundaryless] in
theorem lieCorrectionQuadraticFirstDerivativeIntermediateCoefficient_smul
    (g gm : SmoothRiemannianMetric I M) (a : ℝ)
    (W : SmoothCcTensor g 0 2) :
    lieCorrectionQuadraticFirstDerivativeIntermediateCoefficient (I := I) (M := M) g gm (a • W) =
      a • lieCorrectionQuadraticFirstDerivativeIntermediateCoefficient (I := I) (M := M) g gm W := by
  rw [lieCorrectionQuadraticFirstDerivativeIntermediateCoefficient, tensorThreeTwoProductCoefficient_smul]
  rw [operatorFieldComposition_smul_right]
  rfl

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
omit [I.Boundaryless] in
theorem lieCorrectionQuadraticFirstDerivativeCoefficient_smul
    (g gm : SmoothRiemannianMetric I M) (a : ℝ)
    (W : SmoothCcTensor g 0 2) :
    lieCorrectionQuadraticFirstDerivativeCoefficient (I := I) (M := M) g gm (a • W) =
      a • lieCorrectionQuadraticFirstDerivativeCoefficient (I := I) (M := M) g gm W := by
  simp only [lieCorrectionQuadraticFirstDerivativeCoefficient, lieCorrectionQuadraticFirstDerivativeIntermediateCoefficient_smul, operatorFieldComposition_smul_right]

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
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

omit [SigmaCompactSpace M] in
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
end

section

noncomputable section


open Bundle Manifold MeasureTheory Set Filter DifferentialGeometry.Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

open DifferentialGeometry.Analysis (sq_add_sq_le_sq_add_of_nonneg)
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Analysis.Sobolev.TensorHilbert
open DifferentialGeometry.PDE.DeTurck.RicciLinearization
open DifferentialGeometry.Analysis.Spectral.DeTurck
open DifferentialGeometry.Analysis.Spectral.MetricRealization
open DifferentialGeometry.Analysis.Elliptic
  (integrable_riemannianFiberNormSq_toSection riemannianFiberNormSq)
open DifferentialGeometry.Analysis.Sobolev
  (cometricCastG0 covariantJetNormSq covariantJetNormSq_add_le covariantJetNormSq_nonneg
    covariantJetNormSq_reindexCoeffGen covariantJetNormSq_rsDomDomCongrSection
    covariantJetNormSq_slotExtend_le covariantJetNormSq_smul covariantJetNormSq_sub_le
    covariantJetNormSq_sum_six_le exists_covariantJetNormSq_two_operatorFieldComposition_le iteratedCovGrad
    normSq_le_integral_of_pointwise_fiberNormSq_le_rs
    riemannianFiberNormSq_iteratedCovGrad_slotInsertEndoCc_le_endo rsDomDomCongrSection
    tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs)
open DifferentialGeometry.Analysis.Spectral
  (operatorFieldApply operatorFieldApplication_add_left operatorFieldApplication_smul_left operatorFieldApplication_smul_right operatorFieldApplication_sub_left ccOperatorFieldComp
    operatorFieldComposition_sub_left operatorFieldComposition_sub_right ccTensorToHs ccTensorToHs_smul deTurckLieTopOrderPairingFamily
    metricComparisonEndomorphismField
    iteratedCovGrad_neg lieCorrectionZeroRiemann norm_iteratedCovGrad_domDomCongrSection permCoeff pureTrace
    pureTrace_toSection riemannianFiberNormSq_symmS_zero_le_fibreSmall slotExtend slotExtend_sub slotExtendIter
    symmS_eq_self_of_ccTensorBilin_symm)
open DifferentialGeometry.Geometry.Connection (slotInsertEndoCc)
open DifferentialGeometry.Geometry.Curvature
  (connectionDifferenceFib_apply_eval connectionDifferenceSection connectionDifferenceSection_self connectionDifferenceSection_toSection
    slotInsertEndoFib)

private lemma mul_le_one_add_mul_sum
    (R D N : ℝ) (hR : 0 ≤ R) (hD : 0 ≤ D) (hN : 0 ≤ N) :
    N * R ≤ (1 + R) * (D + N) := by
  calc
    N * R ≤ (D + N) * R :=
      mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hD) hR
    _ ≤ (D + N) * (1 + R) :=
      mul_le_mul_of_nonneg_left (le_add_of_nonneg_left zero_le_one) (add_nonneg hD hN)
    _ = (1 + R) * (D + N) := mul_comm _ _

private lemma le_one_add_mul_sum
    (R D N : ℝ) (hR : 0 ≤ R) (hD : 0 ≤ D) (hN : 0 ≤ N) :
    D ≤ (1 + R) * (D + N) := by
  calc
    D ≤ D + N := le_add_of_nonneg_right hN
    _ = 1 * (D + N) := (one_mul _).symm
    _ ≤ (1 + R) * (D + N) :=
      mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hR) (add_nonneg hD hN)

variable
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
      [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

namespace RicciDeTurckPairing

noncomputable def lowOrderZeroCoefficientPath
    (g : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2)
    {δ : ℝ}
    (hδ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) δ)
    (hδZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g
        (0 : SmoothCcTensor g 0 2)) δ)
    (s : ℝ) : SmoothCcTensor g 2 2 :=
  let gm := metricPerturbationPath (I := I) g T 0 hδ hδZ s
  (deTurckLieCovariantDerivativeArmField (I := I) (M := M) g gm g -
      deTurckLieTopOrderPairingFamily (I := I) (M := M) g T hδ hδZ
        lieDecompositionQ lieDecompositionEps s) +
    lieCorrectionZeroRiemann (I := I) (M := M) g gm

noncomputable def lowOrderFirstDerivativeCoefficientPath
    (g : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2)
    {δ : ℝ}
    (hδ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) δ)
    (hδZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g
        (0 : SmoothCcTensor g 0 2)) δ)
    (s : ℝ) : SmoothCcTensor g 3 2 :=
  let gm := metricPerturbationPath (I := I) g T 0 hδ hδZ s
  (-2 * s : ℝ) • ricciConnectionDifferenceDerivativeCoefficient (I := I) (M := M) g gm T +
    s • lieCorrectionZeroVectorBundleDerivativeCoefficient (I := I) (M := M) g gm T +
    s • lieCorrectionZeroMixedConnectionDerivativeCoefficient (I := I) (M := M) g gm g T

noncomputable def affineLowOrderZeroCoefficientPath
    (g : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2)
    {δ : ℝ}
    (hδ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) δ)
    (hδZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g
        (0 : SmoothCcTensor g 0 2)) δ)
    (s : ℝ) : SmoothCcTensor g 2 2 :=
  let gm := metricPerturbationPath (I := I) g T 0 hδ hδZ s
  lowOrderZeroCoefficientPath (I := I) (M := M) g T hδ hδZ s -
    lieCorrectionQuadraticZeroCoefficient (I := I) (M := M) g gm

noncomputable def affineLowOrderFirstDerivativeCoefficientPath
    (g : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2)
    {δ : ℝ}
    (hδ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) δ)
    (hδZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g
        (0 : SmoothCcTensor g 0 2)) δ)
    (s : ℝ) : SmoothCcTensor g 3 2 :=
  let gm := metricPerturbationPath (I := I) g T 0 hδ hδZ s
  lowOrderFirstDerivativeCoefficientPath (I := I) (M := M) g T hδ hδZ s +
    s • lieCorrectionQuadraticFirstDerivativeCoefficient (I := I) (M := M) g gm T

omit [SigmaCompactSpace M] in
theorem affineLowOrderZeroCoefficientPath_eq
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
    affineLowOrderZeroCoefficientPath (I := I) (M := M) g T hδ hδZ s =
      lieCorrectionCurvatureZeroCoefficient (I := I) (M := M) g gm T s +
        lieCorrectionZeroRiemann (I := I) (M := M) g gm := by
  dsimp only
  rw [affineLowOrderZeroCoefficientPath, lowOrderZeroCoefficientPath]
  calc
    (deTurckLieCovariantDerivativeArmField (I := I) (M := M) g
          (metricPerturbationPath (I := I) g T 0 hδ hδZ s) g -
        deTurckLieTopOrderPairingFamily (I := I) (M := M) g T hδ hδZ
          lieDecompositionQ lieDecompositionEps s) +
          lieCorrectionZeroRiemann (I := I) (M := M) g
            (metricPerturbationPath (I := I) g T 0 hδ hδZ s) -
        lieCorrectionQuadraticZeroCoefficient (I := I) (M := M) g
          (metricPerturbationPath (I := I) g T 0 hδ hδZ s) =
      ((deTurckLieCovariantDerivativeArmField (I := I) (M := M) g
            (metricPerturbationPath (I := I) g T 0 hδ hδZ s) g -
          deTurckLieTopOrderPairingFamily (I := I) (M := M) g T hδ hδZ
            lieDecompositionQ lieDecompositionEps s) -
        lieCorrectionQuadraticZeroCoefficient (I := I) (M := M) g
          (metricPerturbationPath (I := I) g T 0 hδ hδZ s)) +
        lieCorrectionZeroRiemann (I := I) (M := M) g
          (metricPerturbationPath (I := I) g T 0 hδ hδZ s) := by abel
    _ = _ := by
      rw [deTurckLieCovariantDerivative_affineZero_decomposition (I := I) (M := M)
        g T hT hδ_lt hδ hδZ hs]

theorem exists_cometricCastG0_covariantJetNormSq_two_low_bound
    (g : SmoothRiemannianMetric I M)
    {δ₀ : ℝ} (hδ₀0 : 0 ≤ δ₀) (hδ₀ : δ₀ < 1) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ (g₁ : SmoothRiemannianMetric I M)
        (P : SmoothCcTensor g 0 2)
        (_hP : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g P x u v =
            ccTensorBilin (I := I) g P x v u)
        (_htie : ∀ (x : M) (u v : TangentSpace I x),
          g₁.inner x u v =
            g.inner x u v + ccTensorBilinSymm (I := I) g P x u v)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀) (_hδ0 : 0 ≤ δ)
        (_hδ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g P) δ),
      covariantJetNormSq (I := I) (M := M) g 2
          (cometricCastG0 (I := I) g g₁) ≤
        K * (1 + covariantJetNormSq (I := I) (M := M) g 2 P) := by
  classical
  let aStar : ℕ := 2 * Module.finrank ℝ E + 10
  let Λ₀ : ℝ := (Module.finrank ℝ E : ℝ) * δ₀
  have hΛ₀0 : 0 ≤ Λ₀ :=
    mul_nonneg (Nat.cast_nonneg _) hδ₀0
  obtain ⟨Λ, F, hΛ, hF, hcast⟩ :=
    cometricCastG0_order0sup_jetL2_radiusFree
      (I := I) (M := M) g aStar hδ₀ hΛ₀0
  refine ⟨F 2, hF 2, ?_⟩
  intro g₁ P hP htie δ hδ_le hδ0 hδ
  have hsymm : symmS (I := I) (M := M) g P = P :=
    symmS_eq_self_of_ccTensorBilin_symm
      (I := I) (M := M) g P hP
  have hsup : ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g 0 2 x
          (P.toSection x) ≤ Λ₀ ^ 2 := by
    intro x
    rw [← hsymm]
    exact riemannianFiberNormSq_symmS_zero_le_fibreSmall
      (I := I) (M := M) g hδ₀0 P hδ_le hδ0 hδ x
  have hraw := (hcast g₁ P htie hδ_le hδ0 hδ hsup).2 2 (by
    dsimp only [aStar]
    omega)
  simpa only [covariantJetNormSq, Nat.reduceAdd] using hraw

theorem exists_reindexedCometricDoubleTrace_covariantJetNormSq_two_low_bound
    (g : SmoothRiemannianMetric I M)
    {δ₀ : ℝ} (hδ₀0 : 0 ≤ δ₀) (hδ₀ : δ₀ < 1) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ (g₁ : SmoothRiemannianMetric I M)
        (P : SmoothCcTensor g 0 2)
        (_hP : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g P x u v =
            ccTensorBilin (I := I) g P x v u)
        (_htie : ∀ (x : M) (u v : TangentSpace I x),
          g₁.inner x u v =
            g.inner x u v + ccTensorBilinSymm (I := I) g P x u v)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀) (_hδ0 : 0 ≤ δ)
        (_hδ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g P) δ),
      covariantJetNormSq (I := I) (M := M) g 2
          (reindexedCometricDoubleTrace (I := I) (M := M) g g₁) ≤
        K * (1 + covariantJetNormSq (I := I) (M := M) g 2 P) := by
  obtain ⟨Kc, hKc, hc⟩ :=
    exists_cometricCastG0_covariantJetNormSq_two_low_bound (I := I) (M := M) g hδ₀0 hδ₀
  let fr : ℝ := Module.finrank ℝ E
  let K : ℝ := fr * Kc
  have hfr : 0 ≤ fr := Nat.cast_nonneg _
  have hK : 0 ≤ K := mul_nonneg hfr hKc
  refine ⟨K, hK, ?_⟩
  intro g₁ P hP htie δ hδ_le hδ0 hδ
  unfold covariantJetNormSq
  calc
    ∑ i ∈ Finset.range 3,
        ‖iteratedCovGrad (I := I) g 4 2 i
          (reindexedCometricDoubleTrace (I := I) (M := M) g g₁)‖ ^ 2 ≤
      ∑ i ∈ Finset.range 3, fr *
        ‖iteratedCovGrad (I := I) g 3 1 i
          (cometricCastG0 (I := I) g g₁)‖ ^ 2 := by
        exact Finset.sum_le_sum fun i _ => by
          simpa only [fr] using
            norm_iteratedCovGrad_reindexedCometricDoubleTrace_sq_le (I := I) (M := M) g g₁ i
    _ = fr * covariantJetNormSq (I := I) (M := M) g 2
        (cometricCastG0 (I := I) g g₁) := by
      rw [← Finset.mul_sum]
    _ ≤ fr * (Kc *
        (1 + covariantJetNormSq (I := I) (M := M) g 2 P)) :=
      mul_le_mul_of_nonneg_left
        (hc g₁ P hP htie hδ_le hδ0 hδ) hfr
    _ = K * (1 + covariantJetNormSq (I := I) (M := M) g 2 P) := by
      simp only [K]
      ring

theorem exists_lieCorrectionZeroRiemann_covariantJetNormSq_two_low_bound
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M)
    {δ₀ : ℝ} (hδ₀0 : 0 ≤ δ₀) (hδ₀ : δ₀ < 1) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ (g₁ : SmoothRiemannianMetric I M)
        (P : SmoothCcTensor g 0 2)
        (_hP : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g P x u v =
            ccTensorBilin (I := I) g P x v u)
        (_htie : ∀ (x : M) (u v : TangentSpace I x),
          g₁.inner x u v =
            g.inner x u v + ccTensorBilinSymm (I := I) g P x u v)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀) (_hδ0 : 0 ≤ δ)
        (_hδ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g P) δ),
      covariantJetNormSq (I := I) (M := M) g 2
          (lieCorrectionZeroRiemann (I := I) (M := M) g g₁) ≤
        K * (1 + covariantJetNormSq (I := I) (M := M) g 2 P) := by
  obtain ⟨Kl, hKl, hlive⟩ :=
    exists_reindexedCometricDoubleTrace_covariantJetNormSq_two_low_bound (I := I) (M := M) g hδ₀0 hδ₀
  obtain ⟨Ca, hCa, happ⟩ :=
    exists_covariantJetNormSq_two_operatorFieldComposition_le (I := I) (M := M) hDim g 2 4 2
  let B : ℝ := covariantJetNormSq (I := I) (M := M) g 2
    (lieCorrectionZeroRiemannLift (I := I) g)
  let K : ℝ := Ca * Kl * B
  have hB : 0 ≤ B :=
    covariantJetNormSq_nonneg (I := I) (M := M) (m := 2) g
      (lieCorrectionZeroRiemannLift (I := I) g)
  have hK : 0 ≤ K := mul_nonneg (mul_nonneg hCa hKl) hB
  refine ⟨K, hK, ?_⟩
  intro g₁ P hP htie δ hδ_le hδ0 hδ
  have hLive := hlive g₁ P hP htie hδ_le hδ0 hδ
  have hApp := happ
    (reindexedCometricDoubleTrace (I := I) (M := M) g g₁)
    (lieCorrectionZeroRiemannLift (I := I) g)
  calc
    covariantJetNormSq (I := I) (M := M) g 2
        (lieCorrectionZeroRiemann (I := I) (M := M) g g₁) =
      covariantJetNormSq (I := I) (M := M) g 2
        (ccOperatorFieldComp (I := I) (M := M) g 2 4 2
          (reindexedCometricDoubleTrace (I := I) (M := M) g g₁)
          (lieCorrectionZeroRiemannLift (I := I) g)) := by
        rw [lieCorrectionZeroRiemann_eq_ccOperatorFieldComp (I := I) (M := M) g g₁]
        unfold covariantJetNormSq
        apply Finset.sum_congr rfl
        intro q _
        rw [iteratedCovGrad_neg, norm_neg]
    _ ≤ Ca *
        covariantJetNormSq (I := I) (M := M) g 2
          (reindexedCometricDoubleTrace (I := I) (M := M) g g₁) *
        covariantJetNormSq (I := I) (M := M) g 2
          (lieCorrectionZeroRiemannLift (I := I) g) := hApp
    _ ≤ Ca * (Kl *
        (1 + covariantJetNormSq (I := I) (M := M) g 2 P)) * B := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hLive hCa) hB
    _ = K * (1 + covariantJetNormSq (I := I) (M := M) g 2 P) := by
      simp only [K]
      ring

theorem exists_lieCorrectionCurvatureZeroCoefficient_covariantJetNormSq_two_bound
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ ρ K : ℝ, 0 < ρ ∧ 0 ≤ K ∧
      ∀ (T : SmoothCcTensor g 0 2)
        {δ : ℝ} (_hδ_le : δ ≤ 1 / 3)
        (hδT : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) δ)
        (hδZ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g
            (0 : SmoothCcTensor g 0 2)) δ)
        (R : ℝ), 0 ≤ R →
        covariantJetNormSq (I := I) (M := M) g 2 T ≤ R ^ 2 →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ ≤ ρ →
        ∀ {s : ℝ}, s ∈ Set.Icc (0 : ℝ) 1 →
      covariantJetNormSq (I := I) (M := M) g 2
          (lieCorrectionCurvatureZeroCoefficient (I := I) (M := M) g
            (metricPerturbationPath (I := I) g T 0 hδT hδZ s) T s) ≤
        K * R ^ 2 := by
  obtain ⟨Ca, hCa, happ⟩ :=
    exists_covariantJetNormSq_two_operatorFieldComposition_le (I := I) (M := M) hDim g 2 6 2
  obtain ⟨ρ, Bp, hρ, hBp, hpair⟩ :=
    RicciDeTurckLowOrder.pair_trace_sobolev_two_bound (I := I) (M := M) hDim g
  obtain ⟨Cc, hCc, hcurv⟩ :=
    exists_riemannCurvatureCoefficientField_covariantJetNormSq_bound (I := I) (M := M) hDim g
  set fr : ℝ := (Module.finrank ℝ E : ℝ) with hfrdef
  have hfr : 0 ≤ fr := Nat.cast_nonneg _
  let K : ℝ := Ca * Bp ^ 2 * (fr ^ 2 * Cc)
  have hK : 0 ≤ K :=
    mul_nonneg (mul_nonneg hCa (sq_nonneg _))
      (mul_nonneg (sq_nonneg _) hCc)
  refine ⟨ρ, K, hρ, hK, ?_⟩
  intro T δ hδ_le hδT hδZ R hR hT2 hTn s hs
  have hδ_lt : δ < 1 := lt_of_le_of_lt hδ_le (by norm_num)
  set gm : SmoothRiemannianMetric I M :=
    metricPerturbationPath (I := I) g T 0 hδT hδZ s with hgm
  set P : SmoothCcTensor g 0 2 := s • T with hcP
  have hs_mem : s ∈ metricPerturbationPathDomain (δ := δ) (δ' := δ) :=
    Icc_subset_metricPerturbationPathDomain hδ_lt hδ_lt hs
  have hsabs : ‖s‖ ≤ (1 : ℝ) := by
    rw [Real.norm_eq_abs, abs_of_nonneg hs.1]
    exact hs.2
  have hs22 : (s / 2) ^ 2 ≤ (1 : ℝ) := by
    nlinarith [hs.1, hs.2]
  have hPtie : ∀ (x : M) (u v : TangentSpace I x),
      gm.inner x u v =
        g.inner x u v + ccTensorBilinSymm (I := I) g P x u v := by
    intro x u v
    simpa only [hgm, hcP, convexPerturbation, smul_zero, zero_add] using
      metricPerturbationPath_inner_of_mem (I := I) g T 0 hδT hδZ hs_mem x u v
  have hPn :
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) P‖ ≤ ρ := by
    rw [hcP, ccTensorToHs_smul, norm_smul]
    exact (mul_le_mul_of_nonneg_right hsabs (norm_nonneg _)).trans
      (by simpa only [one_mul] using hTn)
  have hPair : covariantJetNormSq (I := I) (M := M) g 2
      (cometricDoublePairTraceCoefficient (I := I) (M := M) g gm) ≤ Bp ^ 2 :=
    hpair P gm hPtie hPn
  let V : SmoothCcTensor g 0 4 :=
    (-(s / 2) : ℝ) • riemannCurvatureCoefficientField (I := I) (M := M) g T
  have hV : covariantJetNormSq (I := I) (M := M) g 2 V ≤ Cc * R ^ 2 := by
    have hbase : covariantJetNormSq (I := I) (M := M) g 2
        (riemannCurvatureCoefficientField (I := I) (M := M) g T) ≤ Cc * R ^ 2 :=
      (hcurv T).trans (mul_le_mul_of_nonneg_left hT2 hCc)
    simp only [V, covariantJetNormSq_smul]
    calc
      (-(s / 2)) ^ 2 * covariantJetNormSq (I := I) (M := M) g 2
          (riemannCurvatureCoefficientField (I := I) (M := M) g T) =
          (s / 2) ^ 2 * covariantJetNormSq (I := I) (M := M) g 2
            (riemannCurvatureCoefficientField (I := I) (M := M) g T) := by ring
      _ ≤ covariantJetNormSq (I := I) (M := M) g 2
          (riemannCurvatureCoefficientField (I := I) (M := M) g T) := by
        simpa only [one_mul] using mul_le_mul_of_nonneg_right hs22
          (covariantJetNormSq_nonneg (I := I) (M := M) (m := 2) g
            (riemannCurvatureCoefficientField (I := I) (M := M) g T))
      _ ≤ Cc * R ^ 2 := hbase
  have hIter : slotExtendIter (I := I) (M := M) g 0 4 2 V =
      slotExtend (I := I) (M := M) g 1 5
        (slotExtend (I := I) (M := M) g 0 4 V) := rfl
  have hX : covariantJetNormSq (I := I) (M := M) g 2
      (ccOperatorFieldComp (I := I) (M := M) g 2 6 6
        (permCoeff (I := I) (M := M) g deTurckLieCovariantDerivativePairTracePermutation)
        (slotExtendIter (I := I) (M := M) g 0 4 2 V)) ≤
      fr ^ 2 * (Cc * R ^ 2) := by
    rw [operatorFieldComposition_permutationCoefficient_apply_eq_rsDomDomCongrSection (I := I) (M := M) g deTurckLieCovariantDerivativePairTracePermutation]
    calc
      covariantJetNormSq (I := I) (M := M) g 2
          (rsDomDomCongrSection (I := I) (M := M) g 2 6 deTurckLieCovariantDerivativePairTracePermutation
            (slotExtendIter (I := I) (M := M) g 0 4 2 V)) =
        covariantJetNormSq (I := I) (M := M) g 2
          (slotExtend (I := I) (M := M) g 1 5
            (slotExtend (I := I) (M := M) g 0 4 V)) := by
          rw [hIter, covariantJetNormSq_rsDomDomCongrSection]
      _ ≤ fr * covariantJetNormSq (I := I) (M := M) g 2
          (slotExtend (I := I) (M := M) g 0 4 V) :=
        covariantJetNormSq_slotExtend_le (I := I) (M := M) g 1 5 _
      _ ≤ fr * (fr * covariantJetNormSq (I := I) (M := M) g 2 V) :=
        mul_le_mul_of_nonneg_left
          (covariantJetNormSq_slotExtend_le (I := I) (M := M) g 0 4 _) hfr
      _ ≤ fr * (fr * (Cc * R ^ 2)) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hV hfr) hfr
      _ = fr ^ 2 * (Cc * R ^ 2) := by ring
  rw [hgm, lieCorrectionCurvatureZeroCoefficient, covariantJetNormSq_smul, neg_one_sq, one_mul]
  refine (happ _ _).trans ?_
  have hstep := mul_le_mul (mul_le_mul_of_nonneg_left hPair hCa) hX
    (covariantJetNormSq_nonneg (I := I) (M := M) (m := 2) g _)
    (mul_nonneg hCa (sq_nonneg _))
  refine hstep.trans ?_
  simp only [K]
  exact le_of_eq (by ring)

theorem exists_lieCorrectionCurvatureZeroCoefficient_pairing_secondOrder_bound
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ ρ B : ℝ, 0 < ρ ∧ 0 ≤ B ∧
      ∀ (T U : SmoothCcTensor g 0 2)
        {δ : ℝ} (_hδ_le : δ ≤ 1 / 3)
        (hδT : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) δ)
        (hδU : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g U) δ)
        (hδZ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g
            (0 : SmoothCcTensor g 0 2)) δ)
        (R D2 N : ℝ), 0 ≤ R → 0 ≤ D2 → 0 ≤ N →
        covariantJetNormSq (I := I) (M := M) g 2 T ≤ R ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 2 U ≤ R ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 2 (T - U) ≤ D2 ^ 2 →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ ≤ ρ →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) U‖ ≤ ρ →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) (T - U)‖ ≤ N →
        ∀ {s : ℝ}, s ∈ Set.Icc (0 : ℝ) 1 →
      covariantJetNormSq (I := I) (M := M) g 2
          (lieCorrectionCurvatureZeroCoefficient (I := I) (M := M) g
              (metricPerturbationPath (I := I) g T 0 hδT hδZ s) T s -
            lieCorrectionCurvatureZeroCoefficient (I := I) (M := M) g
              (metricPerturbationPath (I := I) g U 0 hδU hδZ s) U s) ≤
        (B * (1 + R) * (D2 + N)) ^ 2 := by
  obtain ⟨ρp, Cp, hρp, hCp, hpair⟩ :=
    RicciDeTurckLowOrder.pairTrace_pair_h2 (I := I) (M := M) hDim g
  obtain ⟨ρb, Bp, hρb, hBp, hbdd⟩ :=
    RicciDeTurckLowOrder.pair_trace_sobolev_two_bound (I := I) (M := M) hDim g
  obtain ⟨Cc, hCc, hcurv⟩ :=
    exists_riemannCurvatureCoefficientField_covariantJetNormSq_bound (I := I) (M := M) hDim g
  obtain ⟨Ca, hCa, happ⟩ :=
    exists_covariantJetNormSq_two_operatorFieldComposition_le (I := I) (M := M) hDim g 2 6 2
  let ρ : ℝ := min ρp ρb
  let fr : ℝ := Module.finrank ℝ E
  let K0 : ℝ := fr ^ 2 * Cc
  let S : ℝ := Real.sqrt (2 * Ca * K0)
  let B : ℝ := S * (Cp + Bp)
  have hρ : 0 < ρ := lt_min hρp hρb
  have hfr : 0 ≤ fr := Nat.cast_nonneg _
  have hK0 : 0 ≤ K0 := mul_nonneg (sq_nonneg _) hCc
  have hS : 0 ≤ S := Real.sqrt_nonneg _
  have hSsq : S ^ 2 = 2 * Ca * K0 := by
    simpa only [S] using Real.sq_sqrt (mul_nonneg (mul_nonneg (by norm_num) hCa) hK0)
  have hB : 0 ≤ B := mul_nonneg hS (add_nonneg hCp hBp)
  refine ⟨ρ, B, hρ, hB, ?_⟩
  intro T U δ hδ_le hδT hδU hδZ R D2 N hR hD2 hN
    hT2 hU2 hTU2 hTn hUn hTUn s hs
  have hδ_lt : δ < 1 := lt_of_le_of_lt hδ_le (by norm_num)
  let gmT : SmoothRiemannianMetric I M :=
    metricPerturbationPath (I := I) g T 0 hδT hδZ s
  let gmU : SmoothRiemannianMetric I M :=
    metricPerturbationPath (I := I) g U 0 hδU hδZ s
  let P : SmoothCcTensor g 0 2 := s • T
  let Q : SmoothCcTensor g 0 2 := s • U
  have hs_mem : s ∈ metricPerturbationPathDomain (δ := δ) (δ' := δ) :=
    Icc_subset_metricPerturbationPathDomain hδ_lt hδ_lt hs
  have hs2 : s ^ 2 ≤ (1 : ℝ) := by nlinarith [hs.1, hs.2]
  have hsabs : ‖s‖ ≤ (1 : ℝ) := by
    rw [Real.norm_eq_abs, abs_of_nonneg hs.1]
    exact hs.2
  have hPtie : ∀ (x : M) (u v : TangentSpace I x),
      gmT.inner x u v =
        g.inner x u v + ccTensorBilinSymm (I := I) g P x u v := by
    intro x u v
    simpa only [gmT, P, convexPerturbation, smul_zero, zero_add] using
      metricPerturbationPath_inner_of_mem (I := I) g T 0 hδT hδZ hs_mem x u v
  have hQtie : ∀ (x : M) (u v : TangentSpace I x),
      gmU.inner x u v =
        g.inner x u v + ccTensorBilinSymm (I := I) g Q x u v := by
    intro x u v
    simpa only [gmU, Q, convexPerturbation, smul_zero, zero_add] using
      metricPerturbationPath_inner_of_mem (I := I) g U 0 hδU hδZ hs_mem x u v
  have hPn :
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) P‖ ≤ ρp := by
    simp only [P, ccTensorToHs_smul, norm_smul]
    exact (mul_le_mul_of_nonneg_right hsabs (norm_nonneg _)).trans
      (by simpa only [one_mul] using hTn.trans (min_le_left _ _))
  have hQn :
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) Q‖ ≤ ρp := by
    simp only [Q, ccTensorToHs_smul, norm_smul]
    exact (mul_le_mul_of_nonneg_right hsabs (norm_nonneg _)).trans
      (by simpa only [one_mul] using hUn.trans (min_le_left _ _))
  have hQnb :
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) Q‖ ≤ ρb := by
    simp only [Q, ccTensorToHs_smul, norm_smul]
    exact (mul_le_mul_of_nonneg_right hsabs (norm_nonneg _)).trans
      (by simpa only [one_mul] using hUn.trans (min_le_right _ _))
  have hPQn :
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) (P - Q)‖ ≤ N := by
    rw [show P - Q = s • (T - U) by simp only [P, Q, smul_sub],
      ccTensorToHs_smul, norm_smul]
    exact (mul_le_mul_of_nonneg_right hsabs (norm_nonneg _)).trans
      (by simpa only [one_mul] using hTUn)
  let AT : SmoothCcTensor g 6 2 := cometricDoublePairTraceCoefficient (I := I) (M := M) g gmT
  let AU : SmoothCcTensor g 6 2 := cometricDoublePairTraceCoefficient (I := I) (M := M) g gmU
  have hAD : covariantJetNormSq (I := I) (M := M) g 2 (AT - AU) ≤ (Cp * N) ^ 2 := by
    have hraw := hpair P Q gmT gmU hPtie hQtie hPn hQn
    refine hraw.trans (pow_le_pow_left₀
      (mul_nonneg hCp (norm_nonneg _)) ?_ 2)
    exact mul_le_mul_of_nonneg_left hPQn hCp
  have hAU : covariantJetNormSq (I := I) (M := M) g 2 AU ≤ Bp ^ 2 := by
    simpa only [AU] using hbdd Q gmU hQtie hQnb
  have htransfer : ∀ Z : SmoothCcTensor g 0 4,
      covariantJetNormSq (I := I) (M := M) g 2
          (ccOperatorFieldComp (I := I) (M := M) g 2 6 6
            (permCoeff (I := I) (M := M) g deTurckLieCovariantDerivativePairTracePermutation)
            (slotExtendIter (I := I) (M := M) g 0 4 2 Z)) ≤
        fr ^ 2 * covariantJetNormSq (I := I) (M := M) g 2 Z := by
    intro Z
    have hIter : slotExtendIter (I := I) (M := M) g 0 4 2 Z =
        slotExtend (I := I) (M := M) g 1 5
          (slotExtend (I := I) (M := M) g 0 4 Z) := rfl
    rw [operatorFieldComposition_permutationCoefficient_apply_eq_rsDomDomCongrSection (I := I) (M := M) g deTurckLieCovariantDerivativePairTracePermutation]
    calc
      covariantJetNormSq (I := I) (M := M) g 2
          (rsDomDomCongrSection (I := I) (M := M) g 2 6 deTurckLieCovariantDerivativePairTracePermutation
            (slotExtendIter (I := I) (M := M) g 0 4 2 Z)) =
        covariantJetNormSq (I := I) (M := M) g 2
          (slotExtend (I := I) (M := M) g 1 5
            (slotExtend (I := I) (M := M) g 0 4 Z)) := by
              rw [hIter, covariantJetNormSq_rsDomDomCongrSection]
      _ ≤ fr * covariantJetNormSq (I := I) (M := M) g 2
          (slotExtend (I := I) (M := M) g 0 4 Z) :=
        covariantJetNormSq_slotExtend_le (I := I) (M := M) g 1 5 _
      _ ≤ fr * (fr * covariantJetNormSq (I := I) (M := M) g 2 Z) :=
        mul_le_mul_of_nonneg_left
          (covariantJetNormSq_slotExtend_le (I := I) (M := M) g 0 4 _) hfr
      _ = fr ^ 2 * covariantJetNormSq (I := I) (M := M) g 2 Z := by ring
  let ZT : SmoothCcTensor g 0 4 :=
    (-(s / 2) : ℝ) • riemannCurvatureCoefficientField (I := I) (M := M) g T
  let ZU : SmoothCcTensor g 0 4 :=
    (-(s / 2) : ℝ) • riemannCurvatureCoefficientField (I := I) (M := M) g U
  let ZD : SmoothCcTensor g 0 4 := ZT - ZU
  have hs22 : (s / 2) ^ 2 ≤ (1 : ℝ) := by nlinarith [hs.1, hs.2]
  have hZT : covariantJetNormSq (I := I) (M := M) g 2 ZT ≤ Cc * R ^ 2 := by
    have hbase := (hcurv T).trans (mul_le_mul_of_nonneg_left hT2 hCc)
    simp only [ZT, covariantJetNormSq_smul]
    have hcoef : (-(s / 2) : ℝ) ^ 2 ≤ 1 := by nlinarith
    exact (mul_le_of_le_one_left
      (covariantJetNormSq_nonneg (I := I) (M := M) (m := 2) g _) hcoef).trans hbase
  have hZD : covariantJetNormSq (I := I) (M := M) g 2 ZD ≤ Cc * D2 ^ 2 := by
    have hbase : covariantJetNormSq (I := I) (M := M) g 2
        (riemannCurvatureCoefficientField (I := I) (M := M) g T -
          riemannCurvatureCoefficientField (I := I) (M := M) g U) ≤ Cc * D2 ^ 2 := by
      rw [riemannCurvatureCoefficientField_sub (I := I) (M := M) g T U]
      exact (hcurv (T - U)).trans
        (mul_le_mul_of_nonneg_left hTU2 hCc)
    rw [show ZD = (-(s / 2) : ℝ) •
        (riemannCurvatureCoefficientField (I := I) (M := M) g T -
          riemannCurvatureCoefficientField (I := I) (M := M) g U) by
          simp only [ZD, ZT, ZU, smul_sub], covariantJetNormSq_smul]
    have hcoef : (-(s / 2) : ℝ) ^ 2 ≤ 1 := by nlinarith
    exact (mul_le_of_le_one_left
      (covariantJetNormSq_nonneg (I := I) (M := M) (m := 2) g _) hcoef).trans hbase
  let XT : SmoothCcTensor g 2 6 :=
    ccOperatorFieldComp (I := I) (M := M) g 2 6 6
      (permCoeff (I := I) (M := M) g deTurckLieCovariantDerivativePairTracePermutation)
      (slotExtendIter (I := I) (M := M) g 0 4 2 ZT)
  let XU : SmoothCcTensor g 2 6 :=
    ccOperatorFieldComp (I := I) (M := M) g 2 6 6
      (permCoeff (I := I) (M := M) g deTurckLieCovariantDerivativePairTracePermutation)
      (slotExtendIter (I := I) (M := M) g 0 4 2 ZU)
  let XD : SmoothCcTensor g 2 6 :=
    ccOperatorFieldComp (I := I) (M := M) g 2 6 6
      (permCoeff (I := I) (M := M) g deTurckLieCovariantDerivativePairTracePermutation)
      (slotExtendIter (I := I) (M := M) g 0 4 2 ZD)
  have hXD_eq : XT - XU = XD := by
    simp only [XT, XU, XD, ZD, slotExtendIter]
    rw [slotExtend_sub, slotExtend_sub]
    rw [operatorFieldComposition_sub_right]
  have hXT : covariantJetNormSq (I := I) (M := M) g 2 XT ≤ K0 * R ^ 2 := by
    calc
      covariantJetNormSq (I := I) (M := M) g 2 XT ≤
          fr ^ 2 * covariantJetNormSq (I := I) (M := M) g 2 ZT := by
            simpa only [XT] using htransfer ZT
      _ ≤ fr ^ 2 * (Cc * R ^ 2) :=
        mul_le_mul_of_nonneg_left hZT (sq_nonneg _)
      _ = K0 * R ^ 2 := by simp only [K0]; ring
  have hXD : covariantJetNormSq (I := I) (M := M) g 2 (XT - XU) ≤
      K0 * D2 ^ 2 := by
    rw [hXD_eq]
    calc
      covariantJetNormSq (I := I) (M := M) g 2 XD ≤
          fr ^ 2 * covariantJetNormSq (I := I) (M := M) g 2 ZD := by
            simpa only [XD] using htransfer ZD
      _ ≤ fr ^ 2 * (Cc * D2 ^ 2) :=
        mul_le_mul_of_nonneg_left hZD (sq_nonneg _)
      _ = K0 * D2 ^ 2 := by simp only [K0]; ring
  have hsplit :
      lieCorrectionCurvatureZeroCoefficient (I := I) (M := M) g gmT T s -
          lieCorrectionCurvatureZeroCoefficient (I := I) (M := M) g gmU U s =
        (-1 : ℝ) •
          (ccOperatorFieldComp (I := I) (M := M) g 2 6 2 (AT - AU) XT +
            ccOperatorFieldComp (I := I) (M := M) g 2 6 2 AU (XT - XU)) := by
    simp only [lieCorrectionCurvatureZeroCoefficient, AT, AU, XT, XU, ZT, ZU]
    rw [operatorFieldComposition_sub_left, operatorFieldComposition_sub_right]
    module
  let x : ℝ := S * Cp * N * R
  let y : ℝ := S * Bp * D2
  have hx : 0 ≤ x :=
    mul_nonneg (mul_nonneg (mul_nonneg hS hCp) hN) hR
  have hy : 0 ≤ y := mul_nonneg (mul_nonneg hS hBp) hD2
  have hterm1 : covariantJetNormSq (I := I) (M := M) g 2
      (ccOperatorFieldComp (I := I) (M := M) g 2 6 2 (AT - AU) XT) ≤
      Ca * (Cp * N) ^ 2 * (K0 * R ^ 2) := by
    refine (happ (AT - AU) XT).trans ?_
    exact mul_le_mul
      (mul_le_mul_of_nonneg_left hAD hCa) hXT
      (covariantJetNormSq_nonneg (I := I) (M := M) (m := 2) g XT)
      (mul_nonneg hCa (sq_nonneg _))
  have hterm2 : covariantJetNormSq (I := I) (M := M) g 2
      (ccOperatorFieldComp (I := I) (M := M) g 2 6 2 AU (XT - XU)) ≤
      Ca * Bp ^ 2 * (K0 * D2 ^ 2) := by
    refine (happ AU (XT - XU)).trans ?_
    exact mul_le_mul
      (mul_le_mul_of_nonneg_left hAU hCa) hXD
      (covariantJetNormSq_nonneg (I := I) (M := M) (m := 2) g (XT - XU))
      (mul_nonneg hCa (sq_nonneg _))
  have hxSq : 2 * (Ca * (Cp * N) ^ 2 * (K0 * R ^ 2)) = x ^ 2 := by
    simp only [x, mul_pow, hSsq]
    ring
  have hySq : 2 * (Ca * Bp ^ 2 * (K0 * D2 ^ 2)) = y ^ 2 := by
    simp only [y, mul_pow, hSsq]
    ring
  have hsum : covariantJetNormSq (I := I) (M := M) g 2
      (ccOperatorFieldComp (I := I) (M := M) g 2 6 2 (AT - AU) XT +
        ccOperatorFieldComp (I := I) (M := M) g 2 6 2 AU (XT - XU)) ≤
      (x + y) ^ 2 := by
    refine (covariantJetNormSq_add_le (I := I) (M := M) g 2 _ _).trans ?_
    calc
      2 * (covariantJetNormSq (I := I) (M := M) g 2
            (ccOperatorFieldComp (I := I) (M := M) g 2 6 2 (AT - AU) XT) +
          covariantJetNormSq (I := I) (M := M) g 2
            (ccOperatorFieldComp (I := I) (M := M) g 2 6 2 AU (XT - XU))) ≤
        2 * (Ca * (Cp * N) ^ 2 * (K0 * R ^ 2) +
          Ca * Bp ^ 2 * (K0 * D2 ^ 2)) :=
            mul_le_mul_of_nonneg_left (add_le_add hterm1 hterm2) (by norm_num)
      _ = x ^ 2 + y ^ 2 := by rw [← hxSq, ← hySq]; ring
      _ ≤ (x + y) ^ 2 := sq_add_sq_le_sq_add_of_nonneg hx hy
  have hF1 : N * R ≤ (1 + R) * (D2 + N) := by
    exact mul_le_one_add_mul_sum R D2 N hR hD2 hN
  have hF2 : D2 ≤ (1 + R) * (D2 + N) := by
    exact le_one_add_mul_sum R D2 N hR hD2 hN
  have hxy : x + y ≤ B * (1 + R) * (D2 + N) := by
    calc
      x + y ≤ S * Cp * ((1 + R) * (D2 + N)) +
          S * Bp * ((1 + R) * (D2 + N)) :=
        by
          simpa only [x, y, mul_assoc] using
            (add_le_add
              (mul_le_mul_of_nonneg_left hF1 (mul_nonneg hS hCp))
              (mul_le_mul_of_nonneg_left hF2 (mul_nonneg hS hBp)))
      _ = B * (1 + R) * (D2 + N) := by simp only [B]; ring
  change covariantJetNormSq (I := I) (M := M) g 2
      (lieCorrectionCurvatureZeroCoefficient (I := I) (M := M) g gmT T s -
        lieCorrectionCurvatureZeroCoefficient (I := I) (M := M) g gmU U s) ≤
    (B * (1 + R) * (D2 + N)) ^ 2
  rw [hsplit, covariantJetNormSq_smul]
  norm_num
  exact hsum.trans
    (pow_le_pow_left₀ (add_nonneg hx hy) hxy 2)

theorem exists_affineLowOrderZeroCoefficientPath_pairing_secondOrder_bound
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ ρ B : ℝ, 0 < ρ ∧ 0 ≤ B ∧
      ∀ (T U : SmoothCcTensor g 0 2)
        (_hT : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g T x u v =
            ccTensorBilin (I := I) g T x v u)
        (_hU : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g U x u v =
            ccTensorBilin (I := I) g U x v u)
        {δ : ℝ} (_hδ_le : δ ≤ 1 / 3)
        (hδT : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) δ)
        (hδU : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g U) δ)
        (hδZ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g
            (0 : SmoothCcTensor g 0 2)) δ)
        (R D2 N : ℝ), 0 ≤ R → 0 ≤ D2 → 0 ≤ N →
        covariantJetNormSq (I := I) (M := M) g 2 T ≤ R ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 2 U ≤ R ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 2 (T - U) ≤ D2 ^ 2 →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ ≤ ρ →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) U‖ ≤ ρ →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) (T - U)‖ ≤ N →
        ∀ {s : ℝ}, s ∈ Set.Icc (0 : ℝ) 1 →
      covariantJetNormSq (I := I) (M := M) g 2
          (affineLowOrderZeroCoefficientPath (I := I) (M := M) g T hδT hδZ s -
            affineLowOrderZeroCoefficientPath (I := I) (M := M) g U hδU hδZ s) ≤
        (B * (1 + R) * (D2 + N)) ^ 2 := by
  obtain ⟨ρc, Bc, hρc, hBc, hcurv⟩ :=
    exists_lieCorrectionCurvatureZeroCoefficient_pairing_secondOrder_bound (I := I) (M := M) hDim g
  obtain ⟨ρr, Cr, hρr, hCr, hriem⟩ :=
    exists_lieCorrectionZeroRiemann_covariantJetNormSq_difference_bound (I := I) (M := M) hDim g
  let ρ : ℝ := min ρc ρr
  let B : ℝ := 2 * (Bc + Cr)
  have hρ : 0 < ρ := lt_min hρc hρr
  have hB : 0 ≤ B := mul_nonneg (by norm_num) (add_nonneg hBc hCr)
  refine ⟨ρ, B, hρ, hB, ?_⟩
  intro T U hT hU δ hδ_le hδT hδU hδZ R D2 N hR hD2 hN
    hT2 hU2 hTU2 hTn hUn hTUn s hs
  have hδ_lt : δ < 1 := lt_of_le_of_lt hδ_le (by norm_num)
  let gmT : SmoothRiemannianMetric I M :=
    metricPerturbationPath (I := I) g T 0 hδT hδZ s
  let gmU : SmoothRiemannianMetric I M :=
    metricPerturbationPath (I := I) g U 0 hδU hδZ s
  let P : SmoothCcTensor g 0 2 := s • T
  let Q : SmoothCcTensor g 0 2 := s • U
  let Z : ℝ := (1 + R) * (D2 + N)
  have hs_mem : s ∈ metricPerturbationPathDomain (δ := δ) (δ' := δ) :=
    Icc_subset_metricPerturbationPathDomain hδ_lt hδ_lt hs
  have hsabs : ‖s‖ ≤ (1 : ℝ) := by
    rw [Real.norm_eq_abs, abs_of_nonneg hs.1]
    exact hs.2
  have hPtie : ∀ (x : M) (u v : TangentSpace I x),
      gmT.inner x u v =
        g.inner x u v + ccTensorBilinSymm (I := I) g P x u v := by
    intro x u v
    simpa only [gmT, P, convexPerturbation, smul_zero, zero_add] using
      metricPerturbationPath_inner_of_mem (I := I) g T 0 hδT hδZ hs_mem x u v
  have hQtie : ∀ (x : M) (u v : TangentSpace I x),
      gmU.inner x u v =
        g.inner x u v + ccTensorBilinSymm (I := I) g Q x u v := by
    intro x u v
    simpa only [gmU, Q, convexPerturbation, smul_zero, zero_add] using
      metricPerturbationPath_inner_of_mem (I := I) g U 0 hδU hδZ hs_mem x u v
  have hPn :
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) P‖ ≤ ρr := by
    simp only [P, ccTensorToHs_smul, norm_smul]
    exact (mul_le_mul_of_nonneg_right hsabs (norm_nonneg _)).trans
      (by simpa only [one_mul] using hTn.trans (min_le_right _ _))
  have hQn :
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) Q‖ ≤ ρr := by
    simp only [Q, ccTensorToHs_smul, norm_smul]
    exact (mul_le_mul_of_nonneg_right hsabs (norm_nonneg _)).trans
      (by simpa only [one_mul] using hUn.trans (min_le_right _ _))
  have hPQn :
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) (P - Q)‖ ≤ N := by
    rw [show P - Q = s • (T - U) by simp only [P, Q, smul_sub],
      ccTensorToHs_smul, norm_smul]
    exact (mul_le_mul_of_nonneg_right hsabs (norm_nonneg _)).trans
      (by simpa only [one_mul] using hTUn)
  have hc : covariantJetNormSq (I := I) (M := M) g 2
      (lieCorrectionCurvatureZeroCoefficient (I := I) (M := M) g gmT T s -
        lieCorrectionCurvatureZeroCoefficient (I := I) (M := M) g gmU U s) ≤
      (Bc * Z) ^ 2 := by
    simpa only [gmT, gmU, Z, mul_assoc] using
      hcurv T U hδ_le hδT hδU hδZ R D2 N hR hD2 hN
        hT2 hU2 hTU2
        (hTn.trans (min_le_left _ _))
        (hUn.trans (min_le_left _ _)) hTUn hs
  have hr0 : covariantJetNormSq (I := I) (M := M) g 2
      (lieCorrectionZeroRiemann (I := I) (M := M) g gmT -
        lieCorrectionZeroRiemann (I := I) (M := M) g gmU) ≤
      (Cr * N) ^ 2 :=
    (hriem P Q gmT gmU hPtie hQtie hPn hQn).trans
      (pow_le_pow_left₀ (mul_nonneg hCr (norm_nonneg _))
        (mul_le_mul_of_nonneg_left hPQn hCr) 2)
  have hZ : 0 ≤ Z :=
    mul_nonneg (add_nonneg (by norm_num) hR) (add_nonneg hD2 hN)
  have hNZ : N ≤ Z := by
    simp only [Z]
    nlinarith [mul_nonneg hR (add_nonneg hD2 hN)]
  have hr : covariantJetNormSq (I := I) (M := M) g 2
      (lieCorrectionZeroRiemann (I := I) (M := M) g gmT -
        lieCorrectionZeroRiemann (I := I) (M := M) g gmU) ≤
      (Cr * Z) ^ 2 :=
    hr0.trans (pow_le_pow_left₀ (mul_nonneg hCr hN)
      (mul_le_mul_of_nonneg_left hNZ hCr) 2)
  rw [affineLowOrderZeroCoefficientPath_eq (I := I) (M := M) g T hT hδ_lt hδT hδZ hs,
    affineLowOrderZeroCoefficientPath_eq (I := I) (M := M) g U hU hδ_lt hδU hδZ hs]
  change covariantJetNormSq (I := I) (M := M) g 2
      ((lieCorrectionCurvatureZeroCoefficient (I := I) (M := M) g gmT T s +
          lieCorrectionZeroRiemann (I := I) (M := M) g gmT) -
        (lieCorrectionCurvatureZeroCoefficient (I := I) (M := M) g gmU U s +
          lieCorrectionZeroRiemann (I := I) (M := M) g gmU)) ≤
    (B * (1 + R) * (D2 + N)) ^ 2
  rw [show
    (lieCorrectionCurvatureZeroCoefficient (I := I) (M := M) g gmT T s +
        lieCorrectionZeroRiemann (I := I) (M := M) g gmT) -
      (lieCorrectionCurvatureZeroCoefficient (I := I) (M := M) g gmU U s +
        lieCorrectionZeroRiemann (I := I) (M := M) g gmU) =
      (lieCorrectionCurvatureZeroCoefficient (I := I) (M := M) g gmT T s -
        lieCorrectionCurvatureZeroCoefficient (I := I) (M := M) g gmU U s) +
      (lieCorrectionZeroRiemann (I := I) (M := M) g gmT -
        lieCorrectionZeroRiemann (I := I) (M := M) g gmU) by module]
  refine (covariantJetNormSq_add_le (I := I) (M := M) g 2 _ _).trans ?_
  calc
    2 * (covariantJetNormSq (I := I) (M := M) g 2
          (lieCorrectionCurvatureZeroCoefficient (I := I) (M := M) g gmT T s -
            lieCorrectionCurvatureZeroCoefficient (I := I) (M := M) g gmU U s) +
        covariantJetNormSq (I := I) (M := M) g 2
          (lieCorrectionZeroRiemann (I := I) (M := M) g gmT -
            lieCorrectionZeroRiemann (I := I) (M := M) g gmU)) ≤
      2 * ((Bc * Z) ^ 2 + (Cr * Z) ^ 2) :=
        mul_le_mul_of_nonneg_left (add_le_add hc hr) (by norm_num)
    _ ≤ 2 * ((Bc * Z + Cr * Z) ^ 2) :=
      mul_le_mul_of_nonneg_left
        (sq_add_sq_le_sq_add_of_nonneg (mul_nonneg hBc hZ) (mul_nonneg hCr hZ)) (by norm_num)
    _ ≤ (2 * (Bc + Cr) * Z) ^ 2 := by
      nlinarith [sq_nonneg (Bc * Z + Cr * Z)]
    _ = (B * (1 + R) * (D2 + N)) ^ 2 := by
      simp only [B, Z]
      ring

theorem exists_affineLowOrderZeroCoefficientPath_covariantJetNormSq_two_bound
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ ρ : ℝ, ∃ B : ℝ → ℝ,
      0 < ρ ∧ (∀ R : ℝ, 0 ≤ R → 0 ≤ B R) ∧
      ∀ (T : SmoothCcTensor g 0 2)
        (_hT : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g T x u v =
            ccTensorBilin (I := I) g T x v u)
        {δ : ℝ} (_hδ_le : δ ≤ 1 / 3) (_hδ0 : 0 ≤ δ)
        (hδT : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) δ)
        (hδZ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g
            (0 : SmoothCcTensor g 0 2)) δ)
        (R : ℝ), 0 ≤ R →
        covariantJetNormSq (I := I) (M := M) g 2 T ≤ R ^ 2 →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ ≤ ρ →
        ∀ {s : ℝ}, s ∈ Set.Icc (0 : ℝ) 1 →
      covariantJetNormSq (I := I) (M := M) g 2
          (affineLowOrderZeroCoefficientPath (I := I) (M := M) g T hδT hδZ s) ≤
        (B R) ^ 2 := by
  obtain ⟨ρ, Kc, hρ, hKc, hcurv⟩ :=
    exists_lieCorrectionCurvatureZeroCoefficient_covariantJetNormSq_two_bound (I := I) (M := M) hDim g
  obtain ⟨Kr, hKr, hriem⟩ :=
    exists_lieCorrectionZeroRiemann_covariantJetNormSq_two_low_bound (I := I) (M := M) hDim g
      (δ₀ := (1 : ℝ) / 3) (by norm_num) (by norm_num)
  let X : ℝ → ℝ := fun R =>
    2 * (Kc * R ^ 2 + Kr * (1 + R ^ 2))
  let B : ℝ → ℝ := fun R => Real.sqrt (X R)
  have hX : ∀ R : ℝ, 0 ≤ R → 0 ≤ X R := by
    intro R hR
    have hc : 0 ≤ Kc * R ^ 2 := mul_nonneg hKc (sq_nonneg _)
    have hr : 0 ≤ Kr * (1 + R ^ 2) :=
      mul_nonneg hKr (by positivity)
    simp only [X]
    linarith
  refine ⟨ρ, B, hρ, fun R hR => Real.sqrt_nonneg _, ?_⟩
  intro T hT δ hδ_le hδ0 hδT hδZ R hR hT2 hTn s hs
  have hδ_lt : δ < 1 := lt_of_le_of_lt hδ_le (by norm_num)
  set gm : SmoothRiemannianMetric I M :=
    metricPerturbationPath (I := I) g T 0 hδT hδZ s with hgm
  set P : SmoothCcTensor g 0 2 := s • T with hcP
  have hs_mem : s ∈ metricPerturbationPathDomain (δ := δ) (δ' := δ) :=
    Icc_subset_metricPerturbationPathDomain hδ_lt hδ_lt hs
  have hs2 : s ^ 2 ≤ (1 : ℝ) := by nlinarith [hs.1, hs.2]
  have hPsymm : ∀ (x : M) (u v : TangentSpace I x),
      ccTensorBilin (I := I) g P x u v =
        ccTensorBilin (I := I) g P x v u := by
    intro x u v
    simp only [hcP, ccTensorBilin_apply, ccTensorModel_smul,
      smul_apply, smul_eq_mul]
    apply congrArg (fun z : ℝ => s * z)
    simpa only [ccTensorBilin_apply] using hT x u v
  have hPtie : ∀ (x : M) (u v : TangentSpace I x),
      gm.inner x u v =
        g.inner x u v + ccTensorBilinSymm (I := I) g P x u v := by
    intro x u v
    simpa only [hgm, hcP, convexPerturbation, smul_zero, zero_add] using
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
    simpa only [hcP, convexPerturbation, smul_zero, zero_add, heq] using hraw
  have hP2 : covariantJetNormSq (I := I) (M := M) g 2 P ≤ R ^ 2 := by
    rw [hcP, covariantJetNormSq_smul]
    exact (mul_le_of_le_one_left
      (covariantJetNormSq_nonneg (I := I) (M := M) (m := 2) g T) hs2).trans hT2
  have hc : covariantJetNormSq (I := I) (M := M) g 2
      (lieCorrectionCurvatureZeroCoefficient (I := I) (M := M) g gm T s) ≤ Kc * R ^ 2 := by
    rw [hgm]
    exact hcurv T hδ_le hδT hδZ R hR hT2 hTn hs
  have hr : covariantJetNormSq (I := I) (M := M) g 2
      (lieCorrectionZeroRiemann (I := I) (M := M) g gm) ≤ Kr * (1 + R ^ 2) := by
    refine (hriem gm P hPsymm hPtie hδ_le hδ0 hδP).trans ?_
    exact mul_le_mul_of_nonneg_left (by linarith [hP2]) hKr
  rw [affineLowOrderZeroCoefficientPath_eq (I := I) (M := M) g T hT hδ_lt hδT hδZ hs]
  refine (covariantJetNormSq_add_le (I := I) (M := M) g 2 _ _).trans ?_
  rw [show (B R) ^ 2 = X R from Real.sq_sqrt (hX R hR)]
  simp only [X]
  linarith

omit [SigmaCompactSpace M] in
theorem lowOrderFirstDerivativeCoefficientPath_jointlySmooth
    (g : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2)
    {δ : ℝ}
    (hδ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) δ)
    (hδZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g
        (0 : SmoothCcTensor g 0 2)) δ) :
    JointlySmoothCcTensorFamily (I := I) g 3 2
      (metricPerturbationPathDomain (δ := δ) (δ' := δ))
      (lowOrderFirstDerivativeCoefficientPath (I := I) (M := M) g T hδ hδZ) := by
  have hR := ricciConnectionDifferenceDerivativeCoefficient_metricPerturbationPath_jointlySmooth (I := I) (M := M) g T T hδ hδZ
  have hR' : linearizedRicciThreeArmHjoint (I := I) (M := M) g 3
      (fun t => ricciConnectionDifferenceDerivativeCoefficient (I := I) (M := M) g
        (metricPerturbationPath (I := I) g T 0 hδ hδZ t) T)
      (δ := δ) (δ' := δ) := hR
  have hRN := threeArmJoint_smul (I := I) (M := M) (r := 3) g (-2 : ℝ) _ hR'
  have hRN' : JointlySmoothCcTensorFamily (I := I) g 3 2
      (metricPerturbationPathDomain (δ := δ) (δ' := δ))
      (fun t => (-2 : ℝ) • ricciConnectionDifferenceDerivativeCoefficient (I := I) (M := M) g
        (metricPerturbationPath (I := I) g T 0 hδ hδZ t) T) := hRN
  have hRNP := jointlySmoothCcTensorFamily_parameter_smul (I := I) (M := M) g hRN'
  have hV := lieCorrectionZeroVectorBundleDerivativeCoefficient_metricPerturbationPath_jointlySmooth (I := I) (M := M) g T T hδ hδZ
  have hVP := jointlySmoothCcTensorFamily_parameter_smul (I := I) (M := M) g hV
  have hA := lieCorrectionZeroMixedConnectionDerivativeCoefficient_metricPerturbationPath_jointlySmooth (I := I) (M := M) g T T hδ hδZ
  have hAP := jointlySmoothCcTensorFamily_parameter_smul (I := I) (M := M) g hA
  have hsum := jointlySmoothCcTensorFamily_add (I := I) (M := M) g
    (jointlySmoothCcTensorFamily_add (I := I) (M := M) g hRNP hVP) hAP
  refine hsum.congr (fun q _ => ?_)
  refine congrArg (fun z => TotalSpace.mk' (TensorRSModel 3 2 ℝ E)
    (E := fun x : M => TensorRSSpace 3 2 I x) q.1 z) ?_
  rw [lowOrderFirstDerivativeCoefficientPath]
  simp only [smul_smul]
  congr 2
  ring_nf

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
theorem lieCorrectionZeroRiemann_metricPerturbationPath_jointlySmooth
    (g : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2)
    {δ : ℝ}
    (hδ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) δ)
    (hδZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g
        (0 : SmoothCcTensor g 0 2)) δ) :
    JointlySmoothCcTensorFamily (I := I) g 2 2
      (metricPerturbationPathDomain (δ := δ) (δ' := δ))
      (fun t => lieCorrectionZeroRiemann (I := I) (M := M) g
        (metricPerturbationPath (I := I) g T 0 hδ hδZ t)) := by
  have hLive := reindexedCometricDoubleTrace_metricPerturbationPath_jointlySmooth (I := I) (M := M) g T hδ hδZ
  have hPass := jointlySmoothCcTensorFamily_const (I := I) (M := M) g
    (S := metricPerturbationPathDomain (δ := δ) (δ' := δ))
    (lieCorrectionZeroRiemannLift (I := I) g)
  have happ := jointlySmoothCcTensorFamily_ccOperatorFieldComp (I := I) (M := M) g hLive hPass
  have happ' : linearizedRicciThreeArmHjoint (I := I) (M := M) g 2
      (fun t => ccOperatorFieldComp (I := I) (M := M) g 2 4 2
        (reindexedCometricDoubleTrace (I := I) (M := M) g
          (metricPerturbationPath (I := I) g T 0 hδ hδZ t))
        (lieCorrectionZeroRiemannLift (I := I) g))
      (δ := δ) (δ' := δ) := happ
  have hs := threeArmJoint_smul (I := I) (M := M) (r := 2) g (-1 : ℝ) _ happ'
  simpa only [linearizedRicciThreeArmHjoint, lieCorrectionZeroRiemann_eq_ccOperatorFieldComp,
    neg_one_smul] using hs

omit [SigmaCompactSpace M] in
theorem lowOrderZeroCoefficientPath_jointlySmooth
    (g : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2)
    {δ : ℝ}
    (hδ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) δ)
    (hδZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g
        (0 : SmoothCcTensor g 0 2)) δ) :
    JointlySmoothCcTensorFamily (I := I) g 2 2
      (metricPerturbationPathDomain (δ := δ) (δ' := δ))
      (lowOrderZeroCoefficientPath (I := I) (M := M) g T hδ hδZ) := by
  have hLie : JointlySmoothCcTensorFamily (I := I) g 2 2
      (metricPerturbationPathDomain (δ := δ) (δ' := δ))
      (fun t => lieDecomposition0 (I := I) (M := M) g
        (metricPerturbationPath (I := I) g T 0 hδ hδZ t) g T hδ hδZ t) :=
    lieDecomposition_joint (I := I) (M := M) g g T hδ hδZ
  have hR := lieCorrectionZeroRiemann_metricPerturbationPath_jointlySmooth (I := I) (M := M) g T hδ hδZ
  change JointlySmoothCcTensorFamily (I := I) g 2 2
    (metricPerturbationPathDomain (δ := δ) (δ' := δ))
    (fun t =>
      (deTurckLieCovariantDerivativeArmField (I := I) (M := M) g
          (metricPerturbationPath (I := I) g T 0 hδ hδZ t) g -
        deTurckLieTopOrderPairingFamily (I := I) (M := M) g T hδ hδZ
          lieDecompositionQ lieDecompositionEps t) +
      lieCorrectionZeroRiemann (I := I) (M := M) g
        (metricPerturbationPath (I := I) g T 0 hδ hδZ t))
  exact jointlySmoothCcTensorFamily_add (I := I) (M := M) g hLie hR

omit [SigmaCompactSpace M] in
theorem affineLowOrderZeroCoefficientPath_jointlySmooth
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
      (affineLowOrderZeroCoefficientPath (I := I) (M := M) g T hδ hδZ) := by
  have hL := lowOrderZeroCoefficientPath_jointlySmooth (I := I) (M := M) g T hδ hδZ
  have hQ := lieCorrectionQuadraticZeroCoefficient_metricPerturbationPath_jointlySmooth (I := I) (M := M) g T hT hδ hδZ
  change JointlySmoothCcTensorFamily (I := I) g 2 2
    (metricPerturbationPathDomain (δ := δ) (δ' := δ))
    (fun t => lowOrderZeroCoefficientPath (I := I) (M := M) g T hδ hδZ t -
      lieCorrectionQuadraticZeroCoefficient (I := I) (M := M) g
        (metricPerturbationPath (I := I) g T 0 hδ hδZ t))
  exact jointlySmoothCcTensorFamily_sub (I := I) (M := M) g hL hQ

omit [SigmaCompactSpace M] in
theorem affineLowOrderFirstDerivativeCoefficientPath_jointlySmooth
    (g : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2)
    {δ : ℝ}
    (hδ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) δ)
    (hδZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g
        (0 : SmoothCcTensor g 0 2)) δ) :
    JointlySmoothCcTensorFamily (I := I) g 3 2
      (metricPerturbationPathDomain (δ := δ) (δ' := δ))
      (affineLowOrderFirstDerivativeCoefficientPath (I := I) (M := M) g T hδ hδZ) := by
  have hL := lowOrderFirstDerivativeCoefficientPath_jointlySmooth (I := I) (M := M) g T hδ hδZ
  have hQ := lieCorrectionQuadraticFirstDerivativeCoefficient_metricPerturbationPath_jointlySmooth (I := I) (M := M) g T hδ hδZ
  have hQP := jointlySmoothCcTensorFamily_parameter_smul (I := I) (M := M) g hQ
  change JointlySmoothCcTensorFamily (I := I) g 3 2
    (metricPerturbationPathDomain (δ := δ) (δ' := δ))
    (fun t => lowOrderFirstDerivativeCoefficientPath (I := I) (M := M) g T hδ hδZ t +
      t • lieCorrectionQuadraticFirstDerivativeCoefficient (I := I) (M := M) g
        (metricPerturbationPath (I := I) g T 0 hδ hδZ t) T)
  exact jointlySmoothCcTensorFamily_add (I := I) (M := M) g hL hQP

omit [SigmaCompactSpace M] in
theorem lowerScalePathIntegrand_apply_decomposition
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
    operatorFieldApply (I := I) (M := M) g 2 2
        (RicciDeTurckLowOrder.pathIntegrand (I := I) (M := M)
          g g T hδ hδZ s) T =
      operatorFieldApply (I := I) (M := M) g 2 2
          (lowOrderZeroCoefficientPath (I := I) (M := M) g T hδ hδZ s) T +
        operatorFieldApply (I := I) (M := M) g 3 2
          (lowOrderFirstDerivativeCoefficientPath (I := I) (M := M) g T hδ hδZ s)
          (covGrad (I := I) (M := M) g 0 2 T) := by
  let P : SmoothCcTensor g 0 2 := s • T
  let gm : SmoothRiemannianMetric I M :=
    metricPerturbationPath (I := I) g T 0 hδ hδZ s
  have hs_mem : s ∈ metricPerturbationPathDomain (δ := δ) (δ' := δ) :=
    Icc_subset_metricPerturbationPathDomain hδ_lt hδ_lt hs
  have htie : ∀ (x : M) (u v : TangentSpace I x),
      gm.inner x u v =
        g.inner x u v + ccTensorBilinSymm (I := I) g P x u v := by
    intro x u v
    rw [← show convexPerturbation (I := I) g T 0 s = P by
      simp only [P, convexPerturbation, smul_zero, zero_add]]
    exact metricPerturbationPath_inner_of_mem
      (I := I) g T 0 hδ hδZ hs_mem x u v
  have hP : ∀ (x : M) (u v : TangentSpace I x),
      ccTensorBilin (I := I) g P x u v =
        ccTensorBilin (I := I) g P x v u := by
    intro x u v
    simp only [P, ccTensorBilin_apply, ccTensorModel_smul,
      smul_apply, smul_eq_mul]
    apply congrArg (fun z : ℝ => s * z)
    simpa only [ccTensorBilin_apply] using hT x u v
  have hric := ricciConnectionDifferenceDerivativeCoefficient_apply (I := I) (M := M) g gm P T hP htie
  have hvb := lieCorrectionZeroVectorBundleDerivativeCoefficient_apply (I := I) (M := M) g gm P T hP htie
  have hamix := lieCorrectionZeroMixedConnectionDerivativeCoefficient_apply (I := I) (M := M) g gm g P T hP htie
  rw [lowerScalePathIntegrand_decomposition (I := I) (M := M) g T hT hδ_lt hδ hδZ hs]
  simp only [operatorFieldApplication_add_left, operatorFieldApplication_smul_left]
  rw [lieCorrectionZeroVectorBundle_eq_expansion (I := I) (M := M) g gm,
    lieCorrectionZeroMixedConnection_eq_expansion (I := I) (M := M) g gm g]
  rw [hric, hvb, hamix]
  rw [show covGrad (I := I) (M := M) g 0 2 P =
      s • covGrad (I := I) (M := M) g 0 2 T by
    exact covGrad_smul (I := I) (M := M) g 0 2 s T]
  simp only [operatorFieldApplication_smul_right, lowOrderZeroCoefficientPath, lowOrderFirstDerivativeCoefficientPath, gm,
    operatorFieldApplication_add_left, operatorFieldApplication_smul_left, smul_smul]
  abel

omit [SigmaCompactSpace M] in
theorem lowerScalePathIntegrand_apply_affine_decomposition
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
    operatorFieldApply (I := I) (M := M) g 2 2
        (RicciDeTurckLowOrder.pathIntegrand (I := I) (M := M)
          g g T hδ hδZ s) T =
      operatorFieldApply (I := I) (M := M) g 2 2
          (affineLowOrderZeroCoefficientPath (I := I) (M := M) g T hδ hδZ s) T +
        operatorFieldApply (I := I) (M := M) g 3 2
          (affineLowOrderFirstDerivativeCoefficientPath (I := I) (M := M) g T hδ hδZ s)
          (covGrad (I := I) (M := M) g 0 2 T) := by
  let gm := metricPerturbationPath (I := I) g T 0 hδ hδZ s
  have htie : ∀ (x : M) (u v : TangentSpace I x),
      gm.inner x u v =
        g.inner x u v +
          ccTensorBilinSymm (I := I) g (s • T) x u v := by
    intro x u v
    rw [← show convexPerturbation (I := I) g T 0 s = s • T by
      simp only [convexPerturbation, smul_zero, zero_add]]
    exact metricPerturbationPath_inner_of_mem
      (I := I) g T 0 hδ hδZ
        (Icc_subset_metricPerturbationPathDomain hδ_lt hδ_lt hs) x u v
  have hsT : ∀ (x : M) (u v : TangentSpace I x),
      ccTensorBilin (I := I) g (s • T) x u v =
        ccTensorBilin (I := I) g (s • T) x v u := by
    intro x u v
    simp only [ccTensorBilin_apply, ccTensorModel_smul,
      smul_apply, smul_eq_mul]
    apply congrArg (fun z : ℝ => s * z)
    simpa only [ccTensorBilin_apply] using hT x u v
  have hq := lieCorrectionQuadraticFirstDerivativeCoefficient_apply (I := I) (M := M) g gm (s • T) T hsT htie
  have hqT : operatorFieldApply (I := I) (M := M) g 2 2
      (lieCorrectionQuadraticZeroCoefficient (I := I) (M := M) g gm) T =
      s • operatorFieldApply (I := I) (M := M) g 3 2
        (lieCorrectionQuadraticFirstDerivativeCoefficient (I := I) (M := M) g gm T)
          (covGrad (I := I) (M := M) g 0 2 T) := by
    rw [hq]
    rw [show covGrad (I := I) (M := M) g 0 2 (s • T) =
        s • covGrad (I := I) (M := M) g 0 2 T by
      exact covGrad_smul (I := I) (M := M) g 0 2 s T]
    simp only [operatorFieldApplication_smul_right]
  rw [lowerScalePathIntegrand_apply_decomposition (I := I) (M := M) g T hT hδ_lt hδ hδZ hs]
  simp only [affineLowOrderZeroCoefficientPath, affineLowOrderFirstDerivativeCoefficientPath, operatorFieldApplication_sub_left, operatorFieldApplication_add_left,
    operatorFieldApplication_smul_left]
  rw [hqT]
  abel

noncomputable def lowOrderZeroCoefficientPathIntegral
    (g : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) δ)
    (hδZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g
        (0 : SmoothCcTensor g 0 2)) δ) :
    SmoothCcTensor g 2 2 :=
  pathIntegralCoeffField (I := I) (M := M) g 2 2
    (lowOrderZeroCoefficientPath (I := I) (M := M) g T hδ hδZ)
    (metricPerturbationPathDomain (δ := δ) (δ' := δ))
    metricPerturbationPathDomain_isOpen
    (by
      rw [Set.uIcc_of_le zero_le_one]
      exact Icc_subset_metricPerturbationPathDomain hδ_lt hδ_lt)
    (lowOrderZeroCoefficientPath_jointlySmooth (I := I) (M := M) g T hδ hδZ)

noncomputable def lowOrderFirstDerivativeCoefficientPathIntegral
    (g : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) δ)
    (hδZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g
        (0 : SmoothCcTensor g 0 2)) δ) :
    SmoothCcTensor g 3 2 :=
  pathIntegralCoeffField (I := I) (M := M) g 3 2
    (lowOrderFirstDerivativeCoefficientPath (I := I) (M := M) g T hδ hδZ)
    (metricPerturbationPathDomain (δ := δ) (δ' := δ))
    metricPerturbationPathDomain_isOpen
    (by
      rw [Set.uIcc_of_le zero_le_one]
      exact Icc_subset_metricPerturbationPathDomain hδ_lt hδ_lt)
    (lowOrderFirstDerivativeCoefficientPath_jointlySmooth (I := I) (M := M) g T hδ hδZ)

noncomputable def affineLowOrderZeroCoefficientPathIntegral
    (g : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2)
    (hT : ∀ (x : M) (u v : TangentSpace I x),
      ccTensorBilin (I := I) g T x u v =
        ccTensorBilin (I := I) g T x v u)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) δ)
    (hδZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g
        (0 : SmoothCcTensor g 0 2)) δ) :
    SmoothCcTensor g 2 2 :=
  pathIntegralCoeffField (I := I) (M := M) g 2 2
    (affineLowOrderZeroCoefficientPath (I := I) (M := M) g T hδ hδZ)
    (metricPerturbationPathDomain (δ := δ) (δ' := δ))
    metricPerturbationPathDomain_isOpen
    (by
      rw [Set.uIcc_of_le zero_le_one]
      exact Icc_subset_metricPerturbationPathDomain hδ_lt hδ_lt)
    (affineLowOrderZeroCoefficientPath_jointlySmooth (I := I) (M := M) g T hT hδ hδZ)

noncomputable def affineLowOrderZeroCoefficientPathIntegralDifference
    (g : SmoothRiemannianMetric I M) (T U : SmoothCcTensor g 0 2)
    (hT : ∀ (x : M) (u v : TangentSpace I x),
      ccTensorBilin (I := I) g T x u v =
        ccTensorBilin (I := I) g T x v u)
    (hU : ∀ (x : M) (u v : TangentSpace I x),
      ccTensorBilin (I := I) g U x u v =
        ccTensorBilin (I := I) g U x v u)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδT : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) δ)
    (hδU : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g U) δ)
    (hδZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g
        (0 : SmoothCcTensor g 0 2)) δ) :
    SmoothCcTensor g 2 2 :=
  pathIntegralCoeffField (I := I) (M := M) g 2 2
    (fun s =>
      affineLowOrderZeroCoefficientPath (I := I) (M := M) g T hδT hδZ s -
        affineLowOrderZeroCoefficientPath (I := I) (M := M) g U hδU hδZ s)
    (metricPerturbationPathDomain (δ := δ) (δ' := δ))
    metricPerturbationPathDomain_isOpen
    (by
      rw [Set.uIcc_of_le zero_le_one]
      exact Icc_subset_metricPerturbationPathDomain hδ_lt hδ_lt)
    (jointlySmoothCcTensorFamily_sub (I := I) (M := M) g
      (affineLowOrderZeroCoefficientPath_jointlySmooth (I := I) (M := M) g T hT hδT hδZ)
      (affineLowOrderZeroCoefficientPath_jointlySmooth (I := I) (M := M) g U hU hδU hδZ))

omit [SigmaCompactSpace M] in
theorem lowOrderZeroCoefficientPathIntegral_sub
    (g : SmoothRiemannianMetric I M) (T U : SmoothCcTensor g 0 2)
    (hT : ∀ (x : M) (u v : TangentSpace I x),
      ccTensorBilin (I := I) g T x u v =
        ccTensorBilin (I := I) g T x v u)
    (hU : ∀ (x : M) (u v : TangentSpace I x),
      ccTensorBilin (I := I) g U x u v =
        ccTensorBilin (I := I) g U x v u)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδT : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) δ)
    (hδU : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g U) δ)
    (hδZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g
        (0 : SmoothCcTensor g 0 2)) δ) :
    affineLowOrderZeroCoefficientPathIntegral (I := I) (M := M) g T hT hδ_lt hδT hδZ -
        affineLowOrderZeroCoefficientPathIntegral (I := I) (M := M) g U hU hδ_lt hδU hδZ =
      affineLowOrderZeroCoefficientPathIntegralDifference (I := I) (M := M)
        g T U hT hU hδ_lt hδT hδU hδZ := by
  classical
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  apply TensorRSSpace.toModel_injective
  have hSI : Set.uIcc (0 : ℝ) 1 ⊆
      metricPerturbationPathDomain (δ := δ) (δ' := δ) := by
    rw [Set.uIcc_of_le zero_le_one]
    exact Icc_subset_metricPerturbationPathDomain hδ_lt hδ_lt
  have hTcont :=
    jointContMDiff_toModel_continuous_slice
      (I := I) g 2 2
      (affineLowOrderZeroCoefficientPath (I := I) (M := M) g T hδT hδZ)
      (metricPerturbationPathDomain (δ := δ) (δ' := δ))
      (affineLowOrderZeroCoefficientPath_jointlySmooth (I := I) (M := M) g T hT hδT hδZ) x
  have hUcont :=
    jointContMDiff_toModel_continuous_slice
      (I := I) g 2 2
      (affineLowOrderZeroCoefficientPath (I := I) (M := M) g U hδU hδZ)
      (metricPerturbationPathDomain (δ := δ) (δ' := δ))
      (affineLowOrderZeroCoefficientPath_jointlySmooth (I := I) (M := M) g U hU hδU hδZ) x
  have hTint : IntervalIntegrable
      (fun s : ℝ => TensorRSSpace.toModel
        ((affineLowOrderZeroCoefficientPath (I := I) (M := M) g T hδT hδZ s).toSection x))
      MeasureTheory.volume 0 1 :=
    (hTcont.mono hSI).intervalIntegrable
  have hUint : IntervalIntegrable
      (fun s : ℝ => TensorRSSpace.toModel
        ((affineLowOrderZeroCoefficientPath (I := I) (M := M) g U hδU hδZ s).toSection x))
      MeasureTheory.volume 0 1 :=
    (hUcont.mono hSI).intervalIntegrable
  simp only [affineLowOrderZeroCoefficientPathIntegral, affineLowOrderZeroCoefficientPathIntegralDifference, pathIntegralCoeffField_toModel,
    SmoothCcTensor.toSection_sub, ContMDiffSection.coe_sub, Pi.sub_apply,
    TensorRSSpace.toModel_sub]
  rw [intervalIntegral.integral_sub hTint hUint]

theorem exists_affineLowOrderZeroCoefficientPathIntegral_pairing_secondOrder_bound
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ ρ B : ℝ, 0 < ρ ∧ 0 ≤ B ∧
      ∀ (T U : SmoothCcTensor g 0 2)
        (hT : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g T x u v =
            ccTensorBilin (I := I) g T x v u)
        (hU : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g U x u v =
            ccTensorBilin (I := I) g U x v u)
        {δ : ℝ} (hδ_le : δ ≤ 1 / 3)
        (hδT : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) δ)
        (hδU : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g U) δ)
        (hδZ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g
            (0 : SmoothCcTensor g 0 2)) δ)
        (R D2 N : ℝ), 0 ≤ R → 0 ≤ D2 → 0 ≤ N →
        covariantJetNormSq (I := I) (M := M) g 2 T ≤ R ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 2 U ≤ R ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 2 (T - U) ≤ D2 ^ 2 →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ ≤ ρ →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) U‖ ≤ ρ →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) (T - U)‖ ≤ N →
      covariantJetNormSq (I := I) (M := M) g 2
          (affineLowOrderZeroCoefficientPathIntegral (I := I) (M := M) g T hT
              (lt_of_le_of_lt hδ_le (by norm_num)) hδT hδZ -
            affineLowOrderZeroCoefficientPathIntegral (I := I) (M := M) g U hU
              (lt_of_le_of_lt hδ_le (by norm_num)) hδU hδZ) ≤
        (B * (1 + R) * (D2 + N)) ^ 2 := by
  obtain ⟨ρ, B, hρ, hB, hpoint⟩ :=
    exists_affineLowOrderZeroCoefficientPath_pairing_secondOrder_bound (I := I) (M := M) hDim g
  refine ⟨ρ, B, hρ, hB, ?_⟩
  intro T U hT hU δ hδ_le hδT hδU hδZ R D2 N hR hD2 hN
    hT2 hU2 hTU2 hTn hUn hTUn
  have hδ_lt : δ < 1 := lt_of_le_of_lt hδ_le (by norm_num)
  let S : Set ℝ := metricPerturbationPathDomain (δ := δ) (δ' := δ)
  let Φ : ℝ → SmoothCcTensor g 2 2 := fun s =>
    affineLowOrderZeroCoefficientPath (I := I) (M := M) g T hδT hδZ s -
      affineLowOrderZeroCoefficientPath (I := I) (M := M) g U hδU hδZ s
  have hSI : Set.uIcc (0 : ℝ) 1 ⊆ S := by
    dsimp only [S]
    rw [Set.uIcc_of_le zero_le_one]
    exact Icc_subset_metricPerturbationPathDomain hδ_lt hδ_lt
  have hjoint : JointlySmoothCcTensorFamily (I := I) g 2 2 S Φ := by
    dsimp only [S, Φ]
    exact jointlySmoothCcTensorFamily_sub (I := I) (M := M) g
      (affineLowOrderZeroCoefficientPath_jointlySmooth (I := I) (M := M) g T hT hδT hδZ)
      (affineLowOrderZeroCoefficientPath_jointlySmooth (I := I) (M := M) g U hU hδU hδZ)
  have hBtot : 0 ≤ B * (1 + R) * (D2 + N) :=
    mul_nonneg (mul_nonneg hB (add_nonneg (by norm_num) hR))
      (add_nonneg hD2 hN)
  have hpath := path_jetL2_le (I := I) (M := M) g 2 2 2
    Φ S metricPerturbationPathDomain_isOpen hSI hjoint
    (fun s hs => by
      simpa only [Φ, covariantJetNormSq, Nat.reduceAdd] using
        hpoint T U hT hU hδ_le hδT hδU hδZ R D2 N
          hR hD2 hN hT2 hU2 hTU2 hTn hUn hTUn hs)
  rw [lowOrderZeroCoefficientPathIntegral_sub (I := I) (M := M)
    g T U hT hU hδ_lt hδT hδU hδZ]
  simpa only [affineLowOrderZeroCoefficientPathIntegralDifference, Φ, S, covariantJetNormSq, Nat.reduceAdd] using hpath

theorem exists_affineLowOrderZeroCoefficientPathIntegral_covariantJetNormSq_two_bound
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ ρ : ℝ, ∃ B : ℝ → ℝ,
      0 < ρ ∧ (∀ R : ℝ, 0 ≤ R → 0 ≤ B R) ∧
      ∀ (T : SmoothCcTensor g 0 2)
        (hT : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g T x u v =
            ccTensorBilin (I := I) g T x v u)
        {δ : ℝ} (hδ_le : δ ≤ 1 / 3) (hδ0 : 0 ≤ δ)
        (hδT : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) δ)
        (hδZ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g
            (0 : SmoothCcTensor g 0 2)) δ)
        (R : ℝ), 0 ≤ R →
        covariantJetNormSq (I := I) (M := M) g 2 T ≤ R ^ 2 →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ ≤ ρ →
      covariantJetNormSq (I := I) (M := M) g 2
          (affineLowOrderZeroCoefficientPathIntegral (I := I) (M := M) g T hT
            (lt_of_le_of_lt hδ_le (by norm_num)) hδT hδZ) ≤
        (B R) ^ 2 := by
  obtain ⟨ρ, B, hρ, hB, hpoint⟩ :=
    exists_affineLowOrderZeroCoefficientPath_covariantJetNormSq_two_bound (I := I) (M := M) hDim g
  refine ⟨ρ, B, hρ, hB, ?_⟩
  intro T hT δ hδ_le hδ0 hδT hδZ R hR hT2 hTn
  have hδ_lt : δ < 1 := lt_of_le_of_lt hδ_le (by norm_num)
  have hSI : Set.uIcc (0 : ℝ) 1 ⊆
      metricPerturbationPathDomain (δ := δ) (δ' := δ) := by
    rw [Set.uIcc_of_le zero_le_one]
    exact Icc_subset_metricPerturbationPathDomain hδ_lt hδ_lt
  have hpath := path_jetL2_le (I := I) (M := M) g 2 2 2
    (affineLowOrderZeroCoefficientPath (I := I) (M := M) g T hδT hδZ)
    (metricPerturbationPathDomain (δ := δ) (δ' := δ))
    metricPerturbationPathDomain_isOpen hSI
    (affineLowOrderZeroCoefficientPath_jointlySmooth (I := I) (M := M) g T hT hδT hδZ)
    (B := B R)
    (fun s hs => by
      simpa only [covariantJetNormSq, Nat.reduceAdd] using
        hpoint T hT hδ_le hδ0 hδT hδZ R hR hT2 hTn hs)
  simpa only [affineLowOrderZeroCoefficientPathIntegral, covariantJetNormSq, Nat.reduceAdd] using hpath

theorem exists_connectionDifferenceLowOrderOperator_covariantJetNormSq_two_bound
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ B : ℝ → ℝ,
      (∀ R : ℝ, 0 ≤ R → 0 ≤ B R) ∧
      ∀ (gm : SmoothRiemannianMetric I M)
        (T : SmoothCcTensor g 0 2)
        (_hT : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g T x u v =
            ccTensorBilin (I := I) g T x v u)
        (_htie : ∀ (x : M) (u v : TangentSpace I x),
          gm.inner x u v =
            g.inner x u v + ccTensorBilinSymm (I := I) g T x u v)
        {δ : ℝ} (_hδ_le : δ ≤ 1 / 3) (_hδ0 : 0 ≤ δ)
        (_hδT : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) δ)
        (_hδZ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g
            (0 : SmoothCcTensor g 0 2)) δ)
        (R A : ℝ), 0 ≤ R → 0 ≤ A →
        covariantJetNormSq (I := I) (M := M) g 2 T ≤ R ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 3 T ≤ A ^ 2 →
      covariantJetNormSq (I := I) (M := M) g 2
          (connectionDifferenceSection (I := I) gm g) ≤
        (B R * (1 + A)) ^ 2 := by
  obtain ⟨C0, C1, hC0, hC1, hpair⟩ :=
    connSec_sub_tame (I := I) (M := M) hDim g
      (δ₀ := (1 : ℝ) / 3) (by norm_num) (by norm_num)
  let B : ℝ → ℝ := fun R => C0 0 + C1 0 * R
  refine ⟨B, ?_, ?_⟩
  · intro R hR
    exact add_nonneg (hC0 0 (by norm_num))
      (mul_nonneg (hC1 0 (by norm_num)) hR)
  intro gm T hT htie δ hδ_le hδ0 hδT hδZ
    R A hR hA hT2 hT3
  have hzeroSymm : ∀ (x : M) (u v : TangentSpace I x),
      ccTensorBilin (I := I) g (0 : SmoothCcTensor g 0 2) x u v =
        ccTensorBilin (I := I) g (0 : SmoothCcTensor g 0 2) x v u := by
    intro x u v
    rw [ccTensorBilin_zero_weight, ccTensorBilin_zero_weight]
  have hzeroTie : ∀ (x : M) (u v : TangentSpace I x),
      g.inner x u v =
        g.inner x u v +
          ccTensorBilinSymm (I := I) g
            (0 : SmoothCcTensor g 0 2) x u v := by
    intro x u v
    rw [ccTensorBilinSymm_apply, ccTensorBilin_zero_weight,
      ccTensorBilin_zero_weight]
    ring
  have h02 :
      covariantJetNormSq (I := I) (M := M) g 2
          (0 : SmoothCcTensor g 0 2) ≤ (0 : ℝ) ^ 2 := by
    rw [show (0 : SmoothCcTensor g 0 2) =
        (0 : ℝ) • T by simp, covariantJetNormSq_smul]
    norm_num
  have hraw :
      covariantJetNormSq (I := I) (M := M) g 2
          (connectionDifferenceSection (I := I) gm g -
            connectionDifferenceSection (I := I) g g) ≤
        (C0 0 * A + C1 0 * R + C1 0 * A * R) ^ 2 :=
    hpair gm g T (0 : SmoothCcTensor g 0 2) hT hzeroSymm
      htie hzeroTie hδ_le hδ0 hδT hδ_le hδ0 hδZ
      0 A R A (by norm_num) hA hR hA h02 hT3
      (by simpa only [sub_zero] using hT2)
      (by simpa only [sub_zero] using hT3)
  rw [connectionDifferenceSection_self (I := I) (M := M) g, sub_zero] at hraw
  have hc0 : 0 ≤ C0 0 := hC0 0 (by norm_num)
  have hc1 : 0 ≤ C1 0 := hC1 0 (by norm_num)
  have hold : 0 ≤ C0 0 * A + C1 0 * R + C1 0 * A * R :=
    add_nonneg (add_nonneg (mul_nonneg hc0 hA) (mul_nonneg hc1 hR))
      (mul_nonneg (mul_nonneg hc1 hA) hR)
  have hlin :
      C0 0 * A + C1 0 * R + C1 0 * A * R ≤
        B R * (1 + A) := by
    dsimp only [B]
    nlinarith [mul_nonneg hc0 (by norm_num : (0 : ℝ) ≤ 1),
      mul_nonneg hc1 hR]
  exact hraw.trans (pow_le_pow_left₀ hold hlin 2)

theorem exists_connectionDifferenceInsertionInnerDerivativeCoefficient_covariantJetNormSq_two_bound
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ B : ℝ → ℝ,
      (∀ R : ℝ, 0 ≤ R → 0 ≤ B R) ∧
      ∀ (gm : SmoothRiemannianMetric I M)
        (T : SmoothCcTensor g 0 2)
        (_hT : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g T x u v =
            ccTensorBilin (I := I) g T x v u)
        (_htie : ∀ (x : M) (u v : TangentSpace I x),
          gm.inner x u v =
            g.inner x u v + ccTensorBilinSymm (I := I) g T x u v)
        {δ : ℝ} (_hδ_le : δ ≤ 1 / 3) (_hδ0 : 0 ≤ δ)
        (_hδT : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) δ)
        (_hδZ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g
            (0 : SmoothCcTensor g 0 2)) δ)
        (R A : ℝ), 0 ≤ R → 0 ≤ A →
        covariantJetNormSq (I := I) (M := M) g 2 T ≤ R ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 3 T ≤ A ^ 2 →
      covariantJetNormSq (I := I) (M := M) g 2
          (connectionDifferenceContrInsertionInnerField (I := I) g gm) ≤
        (B R * (1 + A)) ^ 2 := by
  obtain ⟨C, hC, hsec⟩ := exists_connectionDifferenceLowOrderOperator_covariantJetNormSq_two_bound (I := I) (M := M) hDim g
  let B : ℝ → ℝ := fun R => 3 * C R
  refine ⟨B, fun R hR => mul_nonneg (by norm_num) (hC R hR), ?_⟩
  intro gm T hT htie δ hδ_le hδ0 hδT hδZ
    R A hR hA hT2 hT3
  have hs := hsec gm T hT htie hδ_le hδ0 hδT hδZ
    R A hR hA hT2 hT3
  rw [connectionDifferenceContrInsertionInnerField_eq_reindex_slotExtend
      (I := I) (M := M) g gm,
    covariantJetNormSq_reindexCoeffGen (I := I) (M := M) g]
  calc
    covariantJetNormSq (I := I) (M := M) g 2
        (slotExtend (I := I) (M := M) g 1 2
          (connectionDifferenceSection (I := I) gm g)) ≤
      (Module.finrank ℝ E : ℝ) *
        covariantJetNormSq (I := I) (M := M) g 2
          (connectionDifferenceSection (I := I) gm g) :=
      covariantJetNormSq_slotExtend_le (I := I) (M := M) g 1 2 _
    _ = 3 * covariantJetNormSq (I := I) (M := M) g 2
          (connectionDifferenceSection (I := I) gm g) := by rw [hDim]; norm_num
    _ ≤ 3 * (C R * (1 + A)) ^ 2 :=
      mul_le_mul_of_nonneg_left hs (by norm_num)
    _ ≤ (B R * (1 + A)) ^ 2 := by
      simp only [B]
      nlinarith [sq_nonneg (C R * (1 + A))]

theorem exists_connectionDifferenceContravariantInsertionField_covariantJetNormSq_two_bound
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ B : ℝ → ℝ,
      (∀ R : ℝ, 0 ≤ R → 0 ≤ B R) ∧
      ∀ (gm : SmoothRiemannianMetric I M)
        (T : SmoothCcTensor g 0 2)
        (_hT : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g T x u v =
            ccTensorBilin (I := I) g T x v u)
        (_htie : ∀ (x : M) (u v : TangentSpace I x),
          gm.inner x u v =
            g.inner x u v + ccTensorBilinSymm (I := I) g T x u v)
        {δ : ℝ} (_hδ_le : δ ≤ 1 / 3) (_hδ0 : 0 ≤ δ)
        (_hδT : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) δ)
        (_hδZ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g
            (0 : SmoothCcTensor g 0 2)) δ)
        (R A : ℝ), 0 ≤ R → 0 ≤ A →
        covariantJetNormSq (I := I) (M := M) g 2 T ≤ R ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 3 T ≤ A ^ 2 →
      covariantJetNormSq (I := I) (M := M) g 2
          (connectionDifferenceContravariantInsertionField (I := I) g gm) ≤
        (B R * (1 + A)) ^ 2 := by
  obtain ⟨C, hC, hsec⟩ := exists_connectionDifferenceLowOrderOperator_covariantJetNormSq_two_bound (I := I) (M := M) hDim g
  let B : ℝ → ℝ := fun R => 3 * C R
  refine ⟨B, fun R hR => mul_nonneg (by norm_num) (hC R hR), ?_⟩
  intro gm T hT htie δ hδ_le hδ0 hδT hδZ
    R A hR hA hT2 hT3
  have hs := hsec gm T hT htie hδ_le hδ0 hδT hδZ
    R A hR hA hT2 hT3
  rw [connectionDifferenceContravariantInsertionField_eq_reindex_slotExtend_two
      (I := I) (M := M) g gm,
    covariantJetNormSq_reindexCoeffGen (I := I) (M := M) g]
  calc
    covariantJetNormSq (I := I) (M := M) g 2
        (slotExtend (I := I) (M := M) g 2 3
          (slotExtend (I := I) (M := M) g 1 2
            (connectionDifferenceSection (I := I) gm g))) ≤
      (Module.finrank ℝ E : ℝ) *
        covariantJetNormSq (I := I) (M := M) g 2
          (slotExtend (I := I) (M := M) g 1 2
            (connectionDifferenceSection (I := I) gm g)) :=
      covariantJetNormSq_slotExtend_le (I := I) (M := M) g 2 3 _
    _ ≤ (Module.finrank ℝ E : ℝ) *
        ((Module.finrank ℝ E : ℝ) *
          covariantJetNormSq (I := I) (M := M) g 2
            (connectionDifferenceSection (I := I) gm g)) :=
      mul_le_mul_of_nonneg_left
        (covariantJetNormSq_slotExtend_le (I := I) (M := M) g 1 2 _)
        (Nat.cast_nonneg _)
    _ = 9 * covariantJetNormSq (I := I) (M := M) g 2
          (connectionDifferenceSection (I := I) gm g) := by
      rw [hDim]
      ring
    _ ≤ 9 * (C R * (1 + A)) ^ 2 :=
      mul_le_mul_of_nonneg_left hs (by norm_num)
    _ = (B R * (1 + A)) ^ 2 := by simp only [B]; ring

theorem iteratedCovGrad_slotInsertEndoCc_normSq_le
    (g : SmoothRiemannianMetric I M) (s i : ℕ)
    (Λ : ContMDiffSection I (E →L[ℝ] E) ∞
      (fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x)) :
    ‖iteratedCovGrad (I := I) g (s + 1) (s + 1) i
        (slotInsertEndoCc (I := I) (M := M) g s Λ)‖ ^ 2 ≤
      (Module.finrank ℝ E : ℝ) ^ s *
        ‖iteratedCovGrad (I := I) g 1 1 i
          (slotInsertEndoCc (I := I) (M := M) g 0 Λ)‖ ^ 2 := by
  let F : M → ℝ := fun x => (Module.finrank ℝ E : ℝ) ^ s *
    riemannianFiberNormSq (I := I) (M := M) g 1 (1 + i) x
      ((iteratedCovGrad (I := I) g 1 1 i
        (slotInsertEndoCc (I := I) (M := M) g 0 Λ)).toSection x)
  have hF : MeasureTheory.Integrable F
      (riemannianVolumeMeasure (I := I) (M := M) g) := by
    dsimp only [F]
    exact (integrable_riemannianFiberNormSq_toSection
      (I := I) (M := M) g 1 (1 + i)
      (iteratedCovGrad (I := I) g 1 1 i
        (slotInsertEndoCc (I := I) (M := M) g 0 Λ))).const_mul _
  have hsq := normSq_le_integral_of_pointwise_fiberNormSq_le_rs
    (I := I) (M := M) g (s + 1) ((s + 1) + i)
    (iteratedCovGrad (I := I) g (s + 1) (s + 1) i
      (slotInsertEndoCc (I := I) (M := M) g s Λ))
    F hF (fun x =>
      riemannianFiberNormSq_iteratedCovGrad_slotInsertEndoCc_le_endo
        (I := I) (M := M) g s Λ i x)
  have hint :
      (∫ x, riemannianFiberNormSq (I := I) (M := M) g 1 (1 + i) x
          ((iteratedCovGrad (I := I) g 1 1 i
            (slotInsertEndoCc (I := I) (M := M) g 0 Λ)).toSection x)
        ∂(riemannianVolumeMeasure (I := I) (M := M) g)) =
        ‖iteratedCovGrad (I := I) g 1 1 i
          (slotInsertEndoCc (I := I) (M := M) g 0 Λ)‖ ^ 2 := by
    rw [SmoothCcTensor.norm_def,
      tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs]
  dsimp only [F] at hsq
  rw [MeasureTheory.integral_const_mul, hint] at hsq
  exact hsq

theorem covariantJetNormSq_slotInsertEndoCc_le
    (g : SmoothRiemannianMetric I M) (s m : ℕ)
    (Λ : ContMDiffSection I (E →L[ℝ] E) ∞
      (fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x)) :
    covariantJetNormSq (I := I) (M := M) g m
        (slotInsertEndoCc (I := I) (M := M) g s Λ) ≤
      (Module.finrank ℝ E : ℝ) ^ s *
        covariantJetNormSq (I := I) (M := M) g m
          (slotInsertEndoCc (I := I) (M := M) g 0 Λ) := by
  unfold covariantJetNormSq
  calc
    ∑ i ∈ Finset.range (m + 1),
        ‖iteratedCovGrad (I := I) g (s + 1) (s + 1) i
          (slotInsertEndoCc (I := I) (M := M) g s Λ)‖ ^ 2 ≤
      ∑ i ∈ Finset.range (m + 1), (Module.finrank ℝ E : ℝ) ^ s *
        ‖iteratedCovGrad (I := I) g 1 1 i
          (slotInsertEndoCc (I := I) (M := M) g 0 Λ)‖ ^ 2 :=
      Finset.sum_le_sum fun i _ =>
        iteratedCovGrad_slotInsertEndoCc_normSq_le (I := I) (M := M) g s i Λ
    _ = (Module.finrank ℝ E : ℝ) ^ s *
        ∑ i ∈ Finset.range (m + 1),
          ‖iteratedCovGrad (I := I) g 1 1 i
            (slotInsertEndoCc (I := I) (M := M) g 0 Λ)‖ ^ 2 := by
      rw [Finset.mul_sum]

theorem covariantJetNormSq_slotInsertEndoCc_symmRaiseEndo_le
    (g : SmoothRiemannianMetric I M) (s m : ℕ)
    (D : SmoothCcTensor g 0 2)
    (hD : symmS (I := I) (M := M) g D = D) :
    covariantJetNormSq (I := I) (M := M) g m
        (slotInsertEndoCc (I := I) (M := M) g s
          (symmRaiseEndo (I := I) (M := M) g D)) ≤
      (Module.finrank ℝ E : ℝ) ^ s *
        covariantJetNormSq (I := I) (M := M) g m D := by
  have h0 :
      covariantJetNormSq (I := I) (M := M) g m
          (slotInsertEndoCc (I := I) (M := M) g 0
            (symmRaiseEndo (I := I) (M := M) g D)) =
        covariantJetNormSq (I := I) (M := M) g m D := by
    rw [insert_symmRaise_eq (I := I) (M := M) g D]
    calc
      covariantJetNormSq (I := I) (M := M) g m
          (cometricRaiseSlot0Field (I := I) (M := M) g 0
            (domDomCongrSection (I := I) g
              (Equiv.swap (0 : Fin 2) 1)
              (symmS (I := I) (M := M) g D))) =
        covariantJetNormSq (I := I) (M := M) g m
          (domDomCongrSection (I := I) g
            (Equiv.swap (0 : Fin 2) 1)
            (symmS (I := I) (M := M) g D)) := by
          unfold covariantJetNormSq
          apply Finset.sum_congr rfl
          intro q _
          rw [norm_iteratedCovGrad_cometricRaiseSlot0Field_eq
            (I := I) (M := M) g 0
            (domDomCongrSection (I := I) g
              (Equiv.swap (0 : Fin 2) 1)
              (symmS (I := I) (M := M) g D)) q]
      _ = covariantJetNormSq (I := I) (M := M) g m
          (symmS (I := I) (M := M) g D) := by
        unfold covariantJetNormSq
        apply Finset.sum_congr rfl
        intro q _
        rw [norm_iteratedCovGrad_domDomCongrSection
          (I := I) (M := M) g (Equiv.swap (0 : Fin 2) 1)
          (symmS (I := I) (M := M) g D) q]
      _ = covariantJetNormSq (I := I) (M := M) g m D := by rw [hD]
  have hslot := covariantJetNormSq_slotInsertEndoCc_le (I := I) (M := M) g s m
    (symmRaiseEndo (I := I) (M := M) g D)
  rw [h0] at hslot
  exact hslot

omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] [SigmaCompactSpace M] in
omit [I.Boundaryless] in
theorem sharpFlatEndoCc_eq_slotInsertEndoCc_zero
    (g gm : SmoothRiemannianMetric I M) :
    sharpFlatEndoCc (I := I) g gm =
      slotInsertEndoCc (I := I) (M := M) g 0
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
        (slotInsertEndoCc (I := I) (M := M) g 0
          (metricComparisonEndomorphismField (I := I) (M := M) g gm)).toSection x) om =
      slotInsertEndoFib (I := I) (M := M) 1 0 x
        (metricComparisonEndomorphism (I := I) g gm x) om from rfl]
  rw [cotangentToDual_slotInsertEndoFib' (I := I) (M := M) x
    (metricComparisonEndomorphism (I := I) g gm x) om w]
  rw [show (show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 1 I x from
        (sharpFlatEndoCc (I := I) g gm).toSection x) om =
      g0FlatCLM (I := I) g x (inverseMetricSharpFib (I := I) gm x om) from rfl]
  rw [cotangentToDual_g0FlatCLM]
  rw [show cotangentToDual (I := I) om
      (metricComparisonEndomorphism (I := I) g gm x w) =
      gm.inner x (inverseMetricSharpFib (I := I) gm x om)
        (metricComparisonEndomorphism (I := I) g gm x w) from by
    rw [← cotangentToDualLinear_apply]
    exact (inverseMetricSharpFib_inner (I := I) gm x om
      (metricComparisonEndomorphism (I := I) g gm x w)).symm]
  rw [show metricComparisonEndomorphism (I := I) g gm x w =
      inverseMetricSharpFib (I := I) gm x (g0FlatCLM (I := I) g x w) from by
    rw [metricComparisonEndomorphism_apply]]
  rw [gm.symm x (inverseMetricSharpFib (I := I) gm x om)
    (inverseMetricSharpFib (I := I) gm x (g0FlatCLM (I := I) g x w))]
  rw [inverseMetricSharpFib_inner (I := I) gm x
    (g0FlatCLM (I := I) g x w) (inverseMetricSharpFib (I := I) gm x om)]
  rw [cotangentToDualLinear_apply, cotangentToDual_g0FlatCLM]
  rw [g.symm x w (inverseMetricSharpFib (I := I) gm x om)]

theorem exists_sharpFlatEndoCc_covariantJetNormSq_two_bound
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
  have hsymm : symmS (I := I) (M := M) g P = P :=
    symmS_eq_self_of_ccTensorBilin_symm
      (I := I) (M := M) g P hP
  have hsup : ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g 0 2 x
          (P.toSection x) ≤ Λ₀ ^ 2 := by
    intro x
    rw [← hsymm]
    exact riemannianFiberNormSq_symmS_zero_le_fibreSmall
      (I := I) (M := M) g hδ₀0 P hδ_le hδ0 hδ x
  simpa only [covariantJetNormSq, Nat.reduceAdd] using
    (hFlow gm P htie hδ_le hδ0 hδ hsup).2 2 (by omega)

theorem exists_metricComparisonSlotInsertion_covariantJetNormSq_two_low_bound
    (g : SmoothRiemannianMetric I M) (s : ℕ)
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
          (slotInsertEndoCc (I := I) (M := M) g s
            (metricComparisonEndomorphismField (I := I) (M := M) g gm)) ≤
        K * (1 + covariantJetNormSq (I := I) (M := M) g 2 P) := by
  obtain ⟨K₀, hK₀, hsharp⟩ :=
    exists_sharpFlatEndoCc_covariantJetNormSq_two_bound (I := I) (M := M) g hδ₀0 hδ₀
  let fr : ℝ := Module.finrank ℝ E
  let K : ℝ := fr ^ s * K₀
  have hfr : 0 ≤ fr := Nat.cast_nonneg _
  have hK : 0 ≤ K := mul_nonneg (pow_nonneg hfr s) hK₀
  refine ⟨K, hK, ?_⟩
  intro gm P hP htie δ hδ_le hδ0 hδ
  calc
    covariantJetNormSq (I := I) (M := M) g 2
        (slotInsertEndoCc (I := I) (M := M) g s
          (metricComparisonEndomorphismField (I := I) (M := M) g gm)) ≤
      fr ^ s * covariantJetNormSq (I := I) (M := M) g 2
        (slotInsertEndoCc (I := I) (M := M) g 0
          (metricComparisonEndomorphismField (I := I) (M := M) g gm)) := by
      simpa only [fr] using covariantJetNormSq_slotInsertEndoCc_le (I := I) (M := M) g s 2
        (metricComparisonEndomorphismField (I := I) (M := M) g gm)
    _ = fr ^ s * covariantJetNormSq (I := I) (M := M) g 2
        (sharpFlatEndoCc (I := I) g gm) := by
      rw [sharpFlatEndoCc_eq_slotInsertEndoCc_zero (I := I) (M := M) g gm]
    _ ≤ fr ^ s * (K₀ *
        (1 + covariantJetNormSq (I := I) (M := M) g 2 P)) :=
      mul_le_mul_of_nonneg_left
        (hsharp gm P hP htie hδ_le hδ0 hδ) (pow_nonneg hfr s)
    _ = K * (1 + covariantJetNormSq (I := I) (M := M) g 2 P) := by
      simp only [K]
      ring

theorem exists_connectionDifferenceInsertionInnerActionCoefficient_covariantJetNormSq_two_bound
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ ρ B : ℝ, 0 < ρ ∧ 0 ≤ B ∧
      ∀ (gm : SmoothRiemannianMetric I M)
        (P W : SmoothCcTensor g 0 2)
        (_hP : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g P x u v =
            ccTensorBilin (I := I) g P x v u)
        (_hW : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g W x u v =
            ccTensorBilin (I := I) g W x v u)
        (_htie : ∀ (x : M) (u v : TangentSpace I x),
          gm.inner x u v =
            g.inner x u v + ccTensorBilinSymm (I := I) g P x u v)
        (R : ℝ), 0 ≤ R →
        covariantJetNormSq (I := I) (M := M) g 2 W ≤ R ^ 2 →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) P‖ ≤ ρ →
      covariantJetNormSq (I := I) (M := M) g 2
          (connectionDifferenceInsertionInnerActionCoefficient (I := I) (M := M) g gm W) ≤
        (B * R) ^ 2 := by
  obtain ⟨ρ, Cc, hρ, hCc, hconn⟩ :=
    RicciDeTurckLowOrder.low_connection_coefficient_sobolev_two_bound (I := I) (M := M) hDim g
  obtain ⟨Ci, hCi, hi⟩ :=
    exists_covariantJetNormSq_two_operatorFieldComposition_le (I := I) (M := M) hDim g 3 3 3
  obtain ⟨Ca, hCa, ha⟩ :=
    exists_covariantJetNormSq_two_operatorFieldComposition_le (I := I) (M := M) hDim g 3 3 3
  let JP : ℝ := covariantJetNormSq (I := I) (M := M) g 2
    (permCoeff (I := I) (M := M) g (finRotate 3))
  let fr : ℝ := Module.finrank ℝ E
  let K : ℝ := Ca * Ci * fr ^ 2 * JP * Cc ^ 2
  let B : ℝ := Real.sqrt K
  have hJP : 0 ≤ JP := covariantJetNormSq_nonneg (I := I) (M := M) (m := 2) g _
  have hfr : 0 ≤ fr := Nat.cast_nonneg _
  have hK : 0 ≤ K := by
    dsimp only [K]
    positivity
  have hB : 0 ≤ B := Real.sqrt_nonneg _
  have hBsq : B ^ 2 = K := by
    simpa only [B] using Real.sq_sqrt hK
  refine ⟨ρ, B, hρ, hB, ?_⟩
  intro gm P W hP hW htie R hR hW2 hPn
  have hsymm : symmS (I := I) (M := M) g W = W :=
    symmS_eq_self_of_ccTensorBilin_symm
      (I := I) (M := M) g W hW
  have hins := covariantJetNormSq_slotInsertEndoCc_symmRaiseEndo_le (I := I) (M := M) g 2 2 W hsymm
  have hone :
      covariantJetNormSq (I := I) (M := M) g 2
          (connectionDifferenceInsertionInnerDerivativeCoefficient (I := I) (M := M) g W) ≤
        Ci * (fr ^ 2 * R ^ 2) * JP := by
    rw [connectionDifferenceInsertionInnerDerivativeCoefficient]
    have hraw := hi
      (slotInsertEndoCc (I := I) (M := M) g 2
        (symmRaiseEndo (I := I) (M := M) g W))
      (permCoeff (I := I) (M := M) g (finRotate 3))
    calc
      covariantJetNormSq (I := I) (M := M) g 2
          (ccOperatorFieldComp (I := I) (M := M) g 3 3 3
            (slotInsertEndoCc (I := I) (M := M) g 2
              (symmRaiseEndo (I := I) (M := M) g W))
            (permCoeff (I := I) (M := M) g (finRotate 3))) ≤
        Ci * covariantJetNormSq (I := I) (M := M) g 2
            (slotInsertEndoCc (I := I) (M := M) g 2
              (symmRaiseEndo (I := I) (M := M) g W)) * JP := by
          simpa only [JP] using hraw
      _ ≤ Ci * (fr ^ 2 * covariantJetNormSq (I := I) (M := M) g 2 W) * JP :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hins hCi) hJP
      _ ≤ Ci * (fr ^ 2 * R ^ 2) * JP :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hW2 (pow_nonneg hfr 2)) hCi) hJP
  have hc := hconn P gm htie hPn
  rw [connectionDifferenceInsertionInnerActionCoefficient]
  have hraw := ha
    (connectionDifferenceInsertionInnerDerivativeCoefficient (I := I) (M := M) g W)
    (RicciDeTurckLowOrder.connectionDifferenceLowOrderOperator (I := I) (M := M) g gm)
  calc
    covariantJetNormSq (I := I) (M := M) g 2
        (ccOperatorFieldComp (I := I) (M := M) g 3 3 3
          (connectionDifferenceInsertionInnerDerivativeCoefficient (I := I) (M := M) g W)
          (RicciDeTurckLowOrder.connectionDifferenceLowOrderOperator (I := I) (M := M) g gm)) ≤
      Ca * covariantJetNormSq (I := I) (M := M) g 2
          (connectionDifferenceInsertionInnerDerivativeCoefficient (I := I) (M := M) g W) *
        covariantJetNormSq (I := I) (M := M) g 2
          (RicciDeTurckLowOrder.connectionDifferenceLowOrderOperator (I := I) (M := M) g gm) := hraw
    _ ≤ Ca * (Ci * (fr ^ 2 * R ^ 2) * JP) * Cc ^ 2 :=
      mul_le_mul
        (mul_le_mul_of_nonneg_left hone hCa) hc
        (covariantJetNormSq_nonneg (I := I) (M := M) (m := 2) g _)
        (mul_nonneg hCa
          (mul_nonneg
            (mul_nonneg hCi
              (mul_nonneg (pow_nonneg hfr 2) (sq_nonneg R))) hJP))
    _ = K * R ^ 2 := by simp only [K]; ring
    _ = (B * R) ^ 2 := by rw [mul_pow, hBsq]

noncomputable def ricciQuadraticPermutationJetCap
    (g : SmoothRiemannianMetric I M) : ℝ :=
  covariantJetNormSq (I := I) (M := M) g 2
      (permCoeff (I := I) (M := M) g ricciQuadraticPermutationCycleZeroThreeOneTwo) +
    covariantJetNormSq (I := I) (M := M) g 2
      (permCoeff (I := I) (M := M) g ricciQuadraticPermutationSwapBlocks) +
    covariantJetNormSq (I := I) (M := M) g 2
      (permCoeff (I := I) (M := M) g ricciQuadraticPermutationCycleZeroThreeTwo) +
    covariantJetNormSq (I := I) (M := M) g 2
      (permCoeff (I := I) (M := M) g ricciQuadraticPermutationCycleZeroOneThreeTwo) +
    covariantJetNormSq (I := I) (M := M) g 2
      (permCoeff (I := I) (M := M) g ricciQuadraticPermutationCycleZeroOneTwo) +
    covariantJetNormSq (I := I) (M := M) g 2
      (permCoeff (I := I) (M := M) g ricciQuadraticPermutationSwapZeroTwo) +
    covariantJetNormSq (I := I) (M := M) g 2
      (permCoeff (I := I) (M := M) g ricciQuadraticPermutationSwapZeroOne) +
    covariantJetNormSq (I := I) (M := M) g 2
      (permCoeff (I := I) (M := M) g ricciQuadraticPermutationRotateInputs)

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem ricciQuadraticPermutationJetCap_nonneg (g : SmoothRiemannianMetric I M) :
    0 ≤ ricciQuadraticPermutationJetCap (I := I) (M := M) g := by
  unfold ricciQuadraticPermutationJetCap
  have h1 := covariantJetNormSq_nonneg (I := I) (M := M) (m := 2) g
    (permCoeff (I := I) (M := M) g ricciQuadraticPermutationCycleZeroThreeOneTwo)
  have h2 := covariantJetNormSq_nonneg (I := I) (M := M) (m := 2) g
    (permCoeff (I := I) (M := M) g ricciQuadraticPermutationSwapBlocks)
  have h3 := covariantJetNormSq_nonneg (I := I) (M := M) (m := 2) g
    (permCoeff (I := I) (M := M) g ricciQuadraticPermutationCycleZeroThreeTwo)
  have h4 := covariantJetNormSq_nonneg (I := I) (M := M) (m := 2) g
    (permCoeff (I := I) (M := M) g ricciQuadraticPermutationCycleZeroOneThreeTwo)
  have h5 := covariantJetNormSq_nonneg (I := I) (M := M) (m := 2) g
    (permCoeff (I := I) (M := M) g ricciQuadraticPermutationCycleZeroOneTwo)
  have h6 := covariantJetNormSq_nonneg (I := I) (M := M) (m := 2) g
    (permCoeff (I := I) (M := M) g ricciQuadraticPermutationSwapZeroTwo)
  have h7 := covariantJetNormSq_nonneg (I := I) (M := M) (m := 2) g
    (permCoeff (I := I) (M := M) g ricciQuadraticPermutationSwapZeroOne)
  have h8 := covariantJetNormSq_nonneg (I := I) (M := M) (m := 2) g
    (permCoeff (I := I) (M := M) g ricciQuadraticPermutationRotateInputs)
  linarith

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem covariantJetNormSq_ricciQuadraticPermutation_four_le
    (g : SmoothRiemannianMetric I M) (pm : Equiv.Perm (Fin 4))
    (hpm : pm = ricciQuadraticPermutationCycleZeroThreeOneTwo ∨ pm = ricciQuadraticPermutationSwapBlocks ∨ pm = ricciQuadraticPermutationCycleZeroThreeTwo ∨
      pm = ricciQuadraticPermutationCycleZeroOneThreeTwo ∨ pm = ricciQuadraticPermutationCycleZeroOneTwo ∨ pm = ricciQuadraticPermutationSwapZeroTwo) :
    covariantJetNormSq (I := I) (M := M) g 2
        (permCoeff (I := I) (M := M) g pm) ≤
      ricciQuadraticPermutationJetCap (I := I) (M := M) g := by
  have h1 := covariantJetNormSq_nonneg (I := I) (M := M) (m := 2) g
    (permCoeff (I := I) (M := M) g ricciQuadraticPermutationCycleZeroThreeOneTwo)
  have h2 := covariantJetNormSq_nonneg (I := I) (M := M) (m := 2) g
    (permCoeff (I := I) (M := M) g ricciQuadraticPermutationSwapBlocks)
  have h3 := covariantJetNormSq_nonneg (I := I) (M := M) (m := 2) g
    (permCoeff (I := I) (M := M) g ricciQuadraticPermutationCycleZeroThreeTwo)
  have h4 := covariantJetNormSq_nonneg (I := I) (M := M) (m := 2) g
    (permCoeff (I := I) (M := M) g ricciQuadraticPermutationCycleZeroOneThreeTwo)
  have h5 := covariantJetNormSq_nonneg (I := I) (M := M) (m := 2) g
    (permCoeff (I := I) (M := M) g ricciQuadraticPermutationCycleZeroOneTwo)
  have h6 := covariantJetNormSq_nonneg (I := I) (M := M) (m := 2) g
    (permCoeff (I := I) (M := M) g ricciQuadraticPermutationSwapZeroTwo)
  have h7 := covariantJetNormSq_nonneg (I := I) (M := M) (m := 2) g
    (permCoeff (I := I) (M := M) g ricciQuadraticPermutationSwapZeroOne)
  have h8 := covariantJetNormSq_nonneg (I := I) (M := M) (m := 2) g
    (permCoeff (I := I) (M := M) g ricciQuadraticPermutationRotateInputs)
  unfold ricciQuadraticPermutationJetCap
  rcases hpm with rfl | rfl | rfl | rfl | rfl | rfl <;> linarith

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem covariantJetNormSq_ricciQuadraticPermutation_three_le
    (g : SmoothRiemannianMetric I M) (pm : Equiv.Perm (Fin 3))
    (hpm : pm = ricciQuadraticPermutationSwapZeroOne ∨ pm = ricciQuadraticPermutationRotateInputs) :
    covariantJetNormSq (I := I) (M := M) g 2
        (permCoeff (I := I) (M := M) g pm) ≤
      ricciQuadraticPermutationJetCap (I := I) (M := M) g := by
  have h1 := covariantJetNormSq_nonneg (I := I) (M := M) (m := 2) g
    (permCoeff (I := I) (M := M) g ricciQuadraticPermutationCycleZeroThreeOneTwo)
  have h2 := covariantJetNormSq_nonneg (I := I) (M := M) (m := 2) g
    (permCoeff (I := I) (M := M) g ricciQuadraticPermutationSwapBlocks)
  have h3 := covariantJetNormSq_nonneg (I := I) (M := M) (m := 2) g
    (permCoeff (I := I) (M := M) g ricciQuadraticPermutationCycleZeroThreeTwo)
  have h4 := covariantJetNormSq_nonneg (I := I) (M := M) (m := 2) g
    (permCoeff (I := I) (M := M) g ricciQuadraticPermutationCycleZeroOneThreeTwo)
  have h5 := covariantJetNormSq_nonneg (I := I) (M := M) (m := 2) g
    (permCoeff (I := I) (M := M) g ricciQuadraticPermutationCycleZeroOneTwo)
  have h6 := covariantJetNormSq_nonneg (I := I) (M := M) (m := 2) g
    (permCoeff (I := I) (M := M) g ricciQuadraticPermutationSwapZeroTwo)
  have h7 := covariantJetNormSq_nonneg (I := I) (M := M) (m := 2) g
    (permCoeff (I := I) (M := M) g ricciQuadraticPermutationSwapZeroOne)
  have h8 := covariantJetNormSq_nonneg (I := I) (M := M) (m := 2) g
    (permCoeff (I := I) (M := M) g ricciQuadraticPermutationRotateInputs)
  unfold ricciQuadraticPermutationJetCap
  rcases hpm with rfl | rfl <;> linarith

theorem exists_ricciQuadraticKernelDerivativeCoefficient_covariantJetNormSq_two_bound
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ ρ : ℝ, ∃ B : ℝ → ℝ, 0 < ρ ∧
      (∀ R : ℝ, 0 ≤ R → 0 ≤ B R) ∧
      ∀ (gm : SmoothRiemannianMetric I M)
        (P W : SmoothCcTensor g 0 2)
        (_hP : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g P x u v =
            ccTensorBilin (I := I) g P x v u)
        (_hW : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g W x u v =
            ccTensorBilin (I := I) g W x v u)
        (_htie : ∀ (x : M) (u v : TangentSpace I x),
          gm.inner x u v =
            g.inner x u v + ccTensorBilinSymm (I := I) g P x u v)
        {δ : ℝ} (_hδ_le : δ ≤ 1 / 3) (_hδ0 : 0 ≤ δ)
        (_hδP : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g P) δ)
        (_hδZ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g
            (0 : SmoothCcTensor g 0 2)) δ)
        (R A : ℝ), 0 ≤ R → 0 ≤ A →
        covariantJetNormSq (I := I) (M := M) g 2 P ≤ R ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 3 P ≤ A ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 2 W ≤ R ^ 2 →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) P‖ ≤ ρ →
      covariantJetNormSq (I := I) (M := M) g 2
          (ricciQuadraticKernelDerivativeCoefficient (I := I) (M := M) g gm W) ≤
        (B R * (1 + A)) ^ 2 := by
  obtain ⟨Co, hCo, hoapp⟩ :=
    exists_covariantJetNormSq_two_operatorFieldComposition_le (I := I) (M := M) hDim g 3 4 4
  obtain ⟨Cc, hCc, hcapp⟩ :=
    exists_covariantJetNormSq_two_operatorFieldComposition_le (I := I) (M := M) hDim g 3 3 4
  obtain ⟨Cm, hCm, hmapp⟩ :=
    exists_covariantJetNormSq_two_operatorFieldComposition_le (I := I) (M := M) hDim g 3 3 3
  obtain ⟨Bo, hBo, hout⟩ := exists_connectionDifferenceContravariantInsertionField_covariantJetNormSq_two_bound (I := I) (M := M) hDim g
  obtain ⟨ρ, Bi, hρ, hBi, hinn⟩ := exists_connectionDifferenceInsertionInnerActionCoefficient_covariantJetNormSq_two_bound (I := I) (M := M) hDim g
  let J : ℝ := ricciQuadraticPermutationJetCap (I := I) (M := M) g
  let KZ : ℝ → ℝ := fun R => (1 + Cm * J) * (Bi * R) ^ 2
  let L : ℝ → ℝ := fun R =>
    94 * Co * J * (Cc * Bo R ^ 2 * KZ R)
  let B : ℝ → ℝ := fun R => Real.sqrt (L R)
  have hJ : 0 ≤ J := ricciQuadraticPermutationJetCap_nonneg (I := I) (M := M) g
  have hKZ : ∀ R : ℝ, 0 ≤ R → 0 ≤ KZ R := by
    intro R hR
    exact mul_nonneg
      (add_nonneg (by norm_num) (mul_nonneg hCm hJ))
      (sq_nonneg (Bi * R))
  have hL : ∀ R : ℝ, 0 ≤ R → 0 ≤ L R := by
    intro R hR
    exact mul_nonneg
      (mul_nonneg (mul_nonneg (by norm_num) hCo) hJ)
      (mul_nonneg (mul_nonneg hCc (sq_nonneg (Bo R))) (hKZ R hR))
  refine ⟨ρ, B, hρ, fun R hR => Real.sqrt_nonneg _, ?_⟩
  intro gm P W hP hW htie δ hδ_le hδ0 hδP hδZ
    R A hR hA hP2 hP3 hW2 hPn
  let S : ℝ := (1 + A) ^ 2
  let Q : ℝ := Co * J * (Cc * (Bo R ^ 2 * S) * KZ R)
  have hS : 0 ≤ S := sq_nonneg _
  have hO :
      covariantJetNormSq (I := I) (M := M) g 2
          (connectionDifferenceContravariantInsertionField (I := I) g gm) ≤
        Bo R ^ 2 * S := by
    calc
      _ ≤ (Bo R * (1 + A)) ^ 2 :=
        hout gm P hP htie hδ_le hδ0 hδP hδZ
          R A hR hA hP2 hP3
      _ = Bo R ^ 2 * S := by simp only [S]; ring
  have hI :
      covariantJetNormSq (I := I) (M := M) g 2
          (connectionDifferenceInsertionInnerActionCoefficient (I := I) (M := M) g gm W) ≤
        (Bi * R) ^ 2 := hinn gm P W hP hW htie R hR hW2 hPn
  have hZdir :
      covariantJetNormSq (I := I) (M := M) g 2
          (connectionDifferenceInsertionInnerActionCoefficient (I := I) (M := M) g gm W) ≤ KZ R := by
    refine hI.trans ?_
    simp only [KZ]
    have hz : 0 ≤ (Bi * R) ^ 2 := sq_nonneg _
    nlinarith [mul_nonneg hCm hJ]
  have hZmid : ∀ pm : Equiv.Perm (Fin 3),
      (pm = ricciQuadraticPermutationSwapZeroOne ∨ pm = ricciQuadraticPermutationRotateInputs) →
      covariantJetNormSq (I := I) (M := M) g 2
          (ccOperatorFieldComp (I := I) (M := M) g 3 3 3
            (permCoeff (I := I) (M := M) g pm)
            (connectionDifferenceInsertionInnerActionCoefficient (I := I) (M := M) g gm W)) ≤ KZ R := by
    intro pm hpm
    have hp := covariantJetNormSq_ricciQuadraticPermutation_three_le (I := I) (M := M) g pm hpm
    have hraw := hmapp
      (permCoeff (I := I) (M := M) g pm)
      (connectionDifferenceInsertionInnerActionCoefficient (I := I) (M := M) g gm W)
    refine hraw.trans ?_
    have hmul :
        Cm * covariantJetNormSq (I := I) (M := M) g 2
              (permCoeff (I := I) (M := M) g pm) *
            covariantJetNormSq (I := I) (M := M) g 2
              (connectionDifferenceInsertionInnerActionCoefficient (I := I) (M := M) g gm W) ≤
          Cm * J * (Bi * R) ^ 2 :=
      mul_le_mul (mul_le_mul_of_nonneg_left hp hCm) hI
        (covariantJetNormSq_nonneg (I := I) (M := M) (m := 2) g _)
        (mul_nonneg hCm hJ)
    refine hmul.trans ?_
    simp only [KZ]
    have hz : 0 ≤ (Bi * R) ^ 2 := sq_nonneg _
    nlinarith [mul_nonneg hCm hJ]
  have hQ : 0 ≤ Q := by
    exact mul_nonneg (mul_nonneg hCo hJ)
      (mul_nonneg
        (mul_nonneg hCc (mul_nonneg (sq_nonneg (Bo R)) hS))
        (hKZ R hR))
  have hblk : ∀ pm : Equiv.Perm (Fin 4),
      (pm = ricciQuadraticPermutationCycleZeroThreeOneTwo ∨ pm = ricciQuadraticPermutationSwapBlocks ∨ pm = ricciQuadraticPermutationCycleZeroThreeTwo ∨
        pm = ricciQuadraticPermutationCycleZeroOneThreeTwo ∨ pm = ricciQuadraticPermutationCycleZeroOneTwo ∨ pm = ricciQuadraticPermutationSwapZeroTwo) →
      ∀ Z : SmoothCcTensor g 3 3,
      covariantJetNormSq (I := I) (M := M) g 2 Z ≤ KZ R →
      covariantJetNormSq (I := I) (M := M) g 2
          (ccOperatorFieldComp (I := I) (M := M) g 3 4 4
            (permCoeff (I := I) (M := M) g pm)
            (ccOperatorFieldComp (I := I) (M := M) g 3 3 4
              (connectionDifferenceContravariantInsertionField (I := I) g gm) Z)) ≤ Q := by
    intro pm hpm Z hZ
    have hp := covariantJetNormSq_ricciQuadraticPermutation_four_le (I := I) (M := M) g pm hpm
    have hmraw := hcapp
      (connectionDifferenceContravariantInsertionField (I := I) g gm) Z
    have hm :
        covariantJetNormSq (I := I) (M := M) g 2
            (ccOperatorFieldComp (I := I) (M := M) g 3 3 4
              (connectionDifferenceContravariantInsertionField (I := I) g gm) Z) ≤
          Cc * (Bo R ^ 2 * S) * KZ R := by
      refine hmraw.trans ?_
      exact mul_le_mul
        (mul_le_mul_of_nonneg_left hO hCc) hZ
        (covariantJetNormSq_nonneg (I := I) (M := M) (m := 2) g Z)
        (mul_nonneg hCc (mul_nonneg (sq_nonneg (Bo R)) hS))
    have horaw := hoapp
      (permCoeff (I := I) (M := M) g pm)
      (ccOperatorFieldComp (I := I) (M := M) g 3 3 4
        (connectionDifferenceContravariantInsertionField (I := I) g gm) Z)
    refine horaw.trans ?_
    have hfin := mul_le_mul
      (mul_le_mul_of_nonneg_left hp hCo) hm
      (covariantJetNormSq_nonneg (I := I) (M := M) (m := 2) g _)
      (mul_nonneg hCo hJ)
    simpa only [Q] using hfin
  have hx0 := hblk ricciQuadraticPermutationCycleZeroThreeOneTwo (Or.inl rfl) _
    (hZmid ricciQuadraticPermutationSwapZeroOne (Or.inl rfl))
  have hx1 := hblk ricciQuadraticPermutationSwapBlocks (Or.inr (Or.inl rfl)) _
    (hZmid ricciQuadraticPermutationSwapZeroOne (Or.inl rfl))
  have hx2 := hblk ricciQuadraticPermutationCycleZeroThreeTwo (Or.inr (Or.inr (Or.inl rfl))) _
    (hZmid ricciQuadraticPermutationRotateInputs (Or.inr rfl))
  have hx3 := hblk ricciQuadraticPermutationCycleZeroOneThreeTwo
    (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) _ hZdir
  have hx4 := hblk ricciQuadraticPermutationCycleZeroOneTwo
    (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))) _ hZdir
  have hx5 := hblk ricciQuadraticPermutationSwapZeroTwo
    (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))) _
    (hZmid ricciQuadraticPermutationRotateInputs (Or.inr rfl))
  rw [ricciQuadraticKernelDerivativeCoefficient]
  refine (covariantJetNormSq_sum_six_le (I := I) (M := M) g 2 _ _ _ _ _ _
    hx0 hx1 hx2 hx3 hx4 hx5).trans ?_
  calc
    94 * Q = L R * S := by simp only [Q, L]; ring
    _ = (B R * (1 + A)) ^ 2 := by
      have hBR : B R ^ 2 = L R := by
        simpa only [B] using Real.sq_sqrt (hL R hR)
      simpa only [S, mul_pow] using
        congrArg (fun x : ℝ => x * (1 + A) ^ 2) hBR.symm
    _ ≤ (B R * (1 + A)) ^ 2 := le_rfl

omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] [SigmaCompactSpace M] in
omit [I.Boundaryless] in
theorem cometricDoubleTraceCoefficient_eq_pureTrace
    (g gm : SmoothRiemannianMetric I M) :
    cometricDoubleTraceCoefficient (I := I) (M := M) g gm =
      pureTrace (I := I) (M := M) g gm 2 := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rw [cometricDoubleTraceCoefficient_toSection, pureTrace_toSection]

omit [NeZero (Module.finrank ℝ E)] in
theorem covariantJetNormSq_ricciFourTraceCombination_le
    (g : SmoothRiemannianMetric I M) (F : SmoothCcTensor g 4 2) :
    covariantJetNormSq (I := I) (M := M) g 2
        (((1 : ℝ) / 2) •
          (reindexCoeffGen (I := I) (M := M) g 4 2 F
                fourTraceArgPerm0231 +
            reindexCoeffGen (I := I) (M := M) g 4 2 F
                fourTraceArgPerm0321 -
            F -
            reindexCoeffGen (I := I) (M := M) g 4 2 F
                fourTraceArgPerm2301)) ≤
      22 * covariantJetNormSq (I := I) (M := M) g 2 F := by
  have h0 := covariantJetNormSq_nonneg (I := I) (M := M) (m := 2) g F
  have h1 := covariantJetNormSq_add_le (I := I) (M := M) g 2
    (reindexCoeffGen (I := I) (M := M) g 4 2 F fourTraceArgPerm0231)
    (reindexCoeffGen (I := I) (M := M) g 4 2 F fourTraceArgPerm0321)
  have h2 := covariantJetNormSq_sub_le (I := I) (M := M) g 2
    (reindexCoeffGen (I := I) (M := M) g 4 2 F fourTraceArgPerm0231 +
      reindexCoeffGen (I := I) (M := M) g 4 2 F fourTraceArgPerm0321) F
  have h3 := covariantJetNormSq_sub_le (I := I) (M := M) g 2
    (reindexCoeffGen (I := I) (M := M) g 4 2 F fourTraceArgPerm0231 +
        reindexCoeffGen (I := I) (M := M) g 4 2 F fourTraceArgPerm0321 - F)
    (reindexCoeffGen (I := I) (M := M) g 4 2 F fourTraceArgPerm2301)
  rw [covariantJetNormSq_reindexCoeffGen, covariantJetNormSq_reindexCoeffGen] at h1
  rw [covariantJetNormSq_reindexCoeffGen] at h3
  rw [covariantJetNormSq_smul]
  norm_num at h1 h2 h3 ⊢
  linarith

theorem exists_ricciCometricFourTraceCastG0_covariantJetNormSq_two_bound
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ ρ B : ℝ, 0 < ρ ∧ 0 ≤ B ∧
      ∀ (P : SmoothCcTensor g 0 2)
        (gm : SmoothRiemannianMetric I M),
        (∀ (x : M) (u v : TangentSpace I x),
          gm.inner x u v =
            g.inner x u v + ccTensorBilinSymm (I := I) g P x u v) →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) P‖ ≤ ρ →
        covariantJetNormSq (I := I) (M := M) g 2
            (ricciCometricFourTraceCastG0 (I := I) g gm) ≤ B ^ 2 := by
  obtain ⟨ρ, C, hρ, hC, hbdd⟩ :=
    RicciDeTurckLowOrder.trace_two_sobolev_two_bound (I := I) (M := M) hDim g
  let L : ℝ := 22 * C ^ 2
  let B : ℝ := Real.sqrt L
  have hL : 0 ≤ L := mul_nonneg (by norm_num) (sq_nonneg C)
  refine ⟨ρ, B, hρ, Real.sqrt_nonneg _, ?_⟩
  intro P gm htie hPn
  have hF : covariantJetNormSq (I := I) (M := M) g 2
      (cometricDoubleTraceCoefficient (I := I) (M := M) g gm) ≤ C ^ 2 := by
    rw [cometricDoubleTraceCoefficient_eq_pureTrace]
    exact hbdd P gm htie hPn
  rw [ricciCometricFourTraceCastG0_eq_reindex_combination
    (I := I) (M := M) g gm]
  refine (covariantJetNormSq_ricciFourTraceCombination_le (I := I) (M := M) g _).trans ?_
  rw [show B ^ 2 = L by simpa only [B] using Real.sq_sqrt hL]
  simp only [L]
  exact mul_le_mul_of_nonneg_left hF (by norm_num)

theorem exists_ricciConnectionDifferenceQuadraticDerivativeCoefficient_covariantJetNormSq_two_bound
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ ρ : ℝ, ∃ B : ℝ → ℝ, 0 < ρ ∧
      (∀ R : ℝ, 0 ≤ R → 0 ≤ B R) ∧
      ∀ (gm : SmoothRiemannianMetric I M)
        (P W : SmoothCcTensor g 0 2)
        (_hP : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g P x u v =
            ccTensorBilin (I := I) g P x v u)
        (_hW : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g W x u v =
            ccTensorBilin (I := I) g W x v u)
        (_htie : ∀ (x : M) (u v : TangentSpace I x),
          gm.inner x u v =
            g.inner x u v + ccTensorBilinSymm (I := I) g P x u v)
        {δ : ℝ} (_hδ_le : δ ≤ 1 / 3) (_hδ0 : 0 ≤ δ)
        (_hδP : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g P) δ)
        (_hδZ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g
            (0 : SmoothCcTensor g 0 2)) δ)
        (R A : ℝ), 0 ≤ R → 0 ≤ A →
        covariantJetNormSq (I := I) (M := M) g 2 P ≤ R ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 3 P ≤ A ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 2 W ≤ R ^ 2 →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) P‖ ≤ ρ →
      covariantJetNormSq (I := I) (M := M) g 2
          (ricciConnectionDifferenceQuadraticDerivativeCoefficient (I := I) (M := M) g gm W) ≤
        (B R * (1 + A)) ^ 2 := by
  obtain ⟨ρk, Bk, hρk, hBk, hker⟩ :=
    exists_ricciQuadraticKernelDerivativeCoefficient_covariantJetNormSq_two_bound (I := I) (M := M) hDim g
  obtain ⟨ρt, Bt, hρt, hBt, htrace⟩ :=
    exists_ricciCometricFourTraceCastG0_covariantJetNormSq_two_bound (I := I) (M := M) hDim g
  obtain ⟨Ca, hCa, happ⟩ :=
    exists_covariantJetNormSq_two_operatorFieldComposition_le (I := I) (M := M) hDim g 3 4 2
  let ρ : ℝ := min ρk ρt
  let L : ℝ → ℝ := fun R => Ca * Bt ^ 2 * Bk R ^ 2
  let B : ℝ → ℝ := fun R => Real.sqrt (L R)
  have hρ : 0 < ρ := lt_min hρk hρt
  have hL : ∀ R : ℝ, 0 ≤ R → 0 ≤ L R := by
    intro R hR
    exact mul_nonneg
      (mul_nonneg hCa (sq_nonneg Bt)) (sq_nonneg (Bk R))
  refine ⟨ρ, B, hρ, fun R hR => Real.sqrt_nonneg _, ?_⟩
  intro gm P W hP hW htie δ hδ_le hδ0 hδP hδZ
    R A hR hA hP2 hP3 hW2 hPn
  have hPnk : ‖ccTensorToHs (I := I) (M := M) g 2
      (2 : ℝ) P‖ ≤ ρk := hPn.trans (min_le_left _ _)
  have hPnt : ‖ccTensorToHs (I := I) (M := M) g 2
      (2 : ℝ) P‖ ≤ ρt := hPn.trans (min_le_right _ _)
  have hk := hker gm P W hP hW htie hδ_le hδ0 hδP hδZ
    R A hR hA hP2 hP3 hW2 hPnk
  have ht := htrace P gm htie hPnt
  rw [ricciConnectionDifferenceQuadraticDerivativeCoefficient]
  have hraw := happ
    (ricciCometricFourTraceCastG0 (I := I) g gm)
    (ricciQuadraticKernelDerivativeCoefficient (I := I) (M := M) g gm W)
  refine hraw.trans ?_
  calc
    Ca * covariantJetNormSq (I := I) (M := M) g 2
          (ricciCometricFourTraceCastG0 (I := I) g gm) *
        covariantJetNormSq (I := I) (M := M) g 2
          (ricciQuadraticKernelDerivativeCoefficient (I := I) (M := M) g gm W) ≤
      Ca * Bt ^ 2 * (Bk R * (1 + A)) ^ 2 :=
        mul_le_mul (mul_le_mul_of_nonneg_left ht hCa) hk
          (covariantJetNormSq_nonneg (I := I) (M := M) (m := 2) g _)
          (mul_nonneg hCa (sq_nonneg Bt))
    _ = L R * (1 + A) ^ 2 := by simp only [L]; ring
    _ = (B R * (1 + A)) ^ 2 := by
      have hBR : B R ^ 2 = L R := by
        simpa only [B] using Real.sq_sqrt (hL R hR)
      simpa only [mul_pow] using
        congrArg (fun x : ℝ => x * (1 + A) ^ 2) hBR.symm
    _ ≤ (B R * (1 + A)) ^ 2 := le_rfl

theorem exists_ricciConnectionDifferenceDerivativeCoefficient_covariantJetNormSq_two_bound
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ ρ : ℝ, ∃ B : ℝ → ℝ, 0 < ρ ∧
      (∀ R : ℝ, 0 ≤ R → 0 ≤ B R) ∧
      ∀ (gm : SmoothRiemannianMetric I M)
        (P W : SmoothCcTensor g 0 2)
        (_hP : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g P x u v =
            ccTensorBilin (I := I) g P x v u)
        (_hW : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g W x u v =
            ccTensorBilin (I := I) g W x v u)
        (_htie : ∀ (x : M) (u v : TangentSpace I x),
          gm.inner x u v =
            g.inner x u v + ccTensorBilinSymm (I := I) g P x u v)
        {δ : ℝ} (_hδ_le : δ ≤ 1 / 3) (_hδ0 : 0 ≤ δ)
        (_hδP : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g P) δ)
        (_hδZ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g
            (0 : SmoothCcTensor g 0 2)) δ)
        (R A : ℝ), 0 ≤ R → 0 ≤ A →
        covariantJetNormSq (I := I) (M := M) g 2 P ≤ R ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 3 P ≤ A ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 2 W ≤ R ^ 2 →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) P‖ ≤ ρ →
      covariantJetNormSq (I := I) (M := M) g 2
          (ricciConnectionDifferenceDerivativeCoefficient (I := I) (M := M) g gm W) ≤
        (B R * (1 + A)) ^ 2 := by
  obtain ⟨ρ, Ba, hρ, hBa, haa⟩ := exists_ricciConnectionDifferenceQuadraticDerivativeCoefficient_covariantJetNormSq_two_bound (I := I) (M := M) hDim g
  obtain ⟨Bd, hBd, hda⟩ :=
    exists_ricciConnectionDerivativeTransposedCoefficient_covariantJetNormSq_two_bound (I := I) (M := M) hDim g
  let L : ℝ → ℝ := fun R => 2 * (Ba R ^ 2 + Bd R ^ 2)
  let B : ℝ → ℝ := fun R => Real.sqrt (L R)
  have hL : ∀ R : ℝ, 0 ≤ R → 0 ≤ L R := by
    intro R hR
    exact mul_nonneg (by norm_num)
      (add_nonneg (sq_nonneg (Ba R)) (sq_nonneg (Bd R)))
  refine ⟨ρ, B, hρ, fun R hR => Real.sqrt_nonneg _, ?_⟩
  intro gm P W hP hW htie δ hδ_le hδ0 hδP hδZ
    R A hR hA hP2 hP3 hW2 hPn
  have hsymm : symmS (I := I) (M := M) g W = W :=
    symmS_eq_self_of_ccTensorBilin_symm
      (I := I) (M := M) g W hW
  have hW2' : covariantJetNormSq (I := I) (M := M) g 2
      (symmS (I := I) (M := M) g W) ≤ R ^ 2 := by
    simpa only [hsymm] using hW2
  have ha := haa gm P W hP hW htie hδ_le hδ0 hδP hδZ
    R A hR hA hP2 hP3 hW2 hPn
  have hd := hda gm P (symmS (I := I) (M := M) g W)
    hP htie hδ_le hδ0 hδP R A hR hA hP2 hP3 hW2'
  rw [ricciConnectionDifferenceDerivativeCoefficient]
  refine (covariantJetNormSq_add_le (I := I) (M := M) g 2 _ _).trans ?_
  calc
    2 * (covariantJetNormSq (I := I) (M := M) g 2
          (ricciConnectionDifferenceQuadraticDerivativeCoefficient (I := I) (M := M) g gm W) +
        covariantJetNormSq (I := I) (M := M) g 2
          (RicciDeTurckLowOrder.ricciConnectionDerivativeTransposedCoefficient (I := I) (M := M) g gm
            (symmS (I := I) (M := M) g W))) ≤
      2 * ((Ba R * (1 + A)) ^ 2 + (Bd R * (1 + A)) ^ 2) :=
        mul_le_mul_of_nonneg_left (add_le_add ha hd) (by norm_num)
    _ = L R * (1 + A) ^ 2 := by simp only [L]; ring
    _ = (B R * (1 + A)) ^ 2 := by
      have hBR : B R ^ 2 = L R := by
        simpa only [B] using Real.sq_sqrt (hL R hR)
      simpa only [mul_pow] using
        congrArg (fun x : ℝ => x * (1 + A) ^ 2) hBR.symm

omit [NeZero (Module.finrank ℝ E)] in
theorem covariantJetNormSq_cometricRaiseSlot0Field
    (g : SmoothRiemannianMetric I M) (s m : ℕ)
    (W : SmoothCcTensor g 0 (s + 2)) :
    covariantJetNormSq (I := I) (M := M) g m
        (cometricRaiseSlot0Field (I := I) (M := M) g s W) =
      covariantJetNormSq (I := I) (M := M) g m W := by
  unfold covariantJetNormSq
  apply Finset.sum_congr rfl
  intro q _
  rw [norm_iteratedCovGrad_cometricRaiseSlot0Field_eq
    (I := I) (M := M) g s W q]

omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] [SigmaCompactSpace M] in
omit [I.Boundaryless] in
theorem cometricRaiseSlot0Field_zero_sub
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

end RicciDeTurckPairing
end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral
end

section

noncomputable section


open Bundle Manifold MeasureTheory Set Filter DifferentialGeometry.Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Sobolev (covariantJetNormSq
  covariantJetNormSq_add_le covariantJetNormSq_nonneg covariantJetNormSq_smul
  covariantJetNormSq_rsDomDomCongrSection covariantJetNormSq_slotExtend_le
  covariantJetNormSq_sum_six_le exists_covariantJetNormSq_two_operatorFieldComposition_le)
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Analysis.Sobolev.TensorHilbert
open DifferentialGeometry.Analysis.Sobolev (metricConnectionDifferenceLoweredCoefficient)
open DifferentialGeometry.Analysis.Spectral
  (ccOperatorFieldComp operatorFieldComposition_sub_left operatorFieldComposition_sub_right ccTensorToHs ccTensorToHs_smul
    metricComparisonEndomorphismField permCoeff slotExtend slotExtend_sub slotExtendIter
    symmS_eq_self_of_ccTensorBilin_symm)
open DifferentialGeometry.Geometry.Connection
  (slotInsertEndoCc slotInsertEndoCc_add)
open DifferentialGeometry.PDE.DeTurck.RicciLinearization
open DifferentialGeometry.Analysis.Spectral.DeTurck
open DifferentialGeometry.Analysis.Spectral.MetricRealization

private lemma weighted_three_term_le_product_sum
    (l0 l1 D3 D2 A N : ℝ)
    (hl0 : 0 ≤ l0) (hl1 : 0 ≤ l1) (hD3 : 0 ≤ D3)
    (hD2 : 0 ≤ D2) (hA : 0 ≤ A) (hN : 0 ≤ N) :
    l0 * D3 + l1 * D2 + l1 * A * D2 ≤
      (l0 + l1) * (D3 + D2 + A * D2 + N) := by
  nlinarith only [mul_nonneg hl0 hD2,
    mul_nonneg hl0 (mul_nonneg hA hD2), mul_nonneg hl0 hN,
    mul_nonneg hl1 hD3, mul_nonneg hl1 hN]

private lemma mul_le_mul_one_add
    (l A D : ℝ) (hl : 0 ≤ l) (hA : 0 ≤ A) (hD : 0 ≤ D) :
    l * D ≤ l * (1 + A) * D := by
  calc
    l * D = (l * 1) * D := by ring
    _ ≤ (l * (1 + A)) * D :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (le_add_of_nonneg_right hA) hl) hD

private lemma add_le_four_term_sum
    (D3 D2 A N : ℝ) (hD3 : 0 ≤ D3) (hD2 : 0 ≤ D2) (hA : 0 ≤ A) :
    D2 + N ≤ D3 + D2 + A * D2 + N := by
  nlinarith only [hD3, mul_nonneg hA hD2]

variable
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
      [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

namespace RicciDeTurckPairing

theorem exists_lieCorrectionZeroVectorBundleDerivativeCoefficient_secondOrder_bound
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ ρ : ℝ, ∃ B : ℝ → ℝ, 0 < ρ ∧
      (∀ R : ℝ, 0 ≤ R → 0 ≤ B R) ∧
      ∀ (gm : SmoothRiemannianMetric I M)
        (P W : SmoothCcTensor g 0 2)
        (_hP : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g P x u v =
            ccTensorBilin (I := I) g P x v u)
        (_htie : ∀ (x : M) (u v : TangentSpace I x),
          gm.inner x u v =
            g.inner x u v + ccTensorBilinSymm (I := I) g P x u v)
        {δ : ℝ} (_hδ_le : δ ≤ 1 / 3) (_hδ0 : 0 ≤ δ)
        (_hδP : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g P) δ)
        (R A : ℝ), 0 ≤ R → 0 ≤ A →
        covariantJetNormSq (I := I) (M := M) g 2 P ≤ R ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 3 P ≤ A ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 2 W ≤ R ^ 2 →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) P‖ ≤ ρ →
      covariantJetNormSq (I := I) (M := M) g 2
          (lieCorrectionZeroVectorBundleDerivativeCoefficient (I := I) (M := M) g gm W) ≤
        (B R * (1 + A)) ^ 2 := by
  obtain ⟨ρt, Ct, hρt, hCt, htrace⟩ :=
    RicciDeTurckLowOrder.trace_one_sobolev_two_bound (I := I) (M := M) hDim g
  obtain ⟨ρc, Cc, hρc, hCc, hconn⟩ :=
    RicciDeTurckLowOrder.low_connection_coefficient_sobolev_two_bound (I := I) (M := M) hDim g
  obtain ⟨Bm, hBm, hmcd⟩ :=
    RicciDeTurckLowOrder.metric_connection_difference_coefficient_sobolev_two_bound (I := I) (M := M) hDim g
      (by norm_num : (0 : ℝ) ≤ 1 / 3) (by norm_num : (1 : ℝ) / 3 < 1)
  obtain ⟨Kr, hKr, hriem⟩ :=
    exists_reindexedCometricDoubleTrace_covariantJetNormSq_two_low_bound (I := I) (M := M) g
      (by norm_num : (0 : ℝ) ≤ 1 / 3) (by norm_num : (1 : ℝ) / 3 < 1)
  obtain ⟨C0, hC0, happ0⟩ :=
    exists_covariantJetNormSq_two_operatorFieldComposition_le (I := I) (M := M) hDim g 3 3 1
  obtain ⟨C1, hC1, happ1⟩ :=
    exists_covariantJetNormSq_two_operatorFieldComposition_le (I := I) (M := M) hDim g 3 1 1
  obtain ⟨C2, hC2, happ2⟩ :=
    exists_covariantJetNormSq_two_operatorFieldComposition_le (I := I) (M := M) hDim g 3 1 4
  obtain ⟨C3, hC3, happ3⟩ :=
    exists_covariantJetNormSq_two_operatorFieldComposition_le (I := I) (M := M) hDim g 3 4 2
  let ρ : ℝ := min ρt ρc
  let fr : ℝ := Module.finrank ℝ E
  let Z0 : ℝ := C0 * Ct ^ 2 * Cc ^ 2
  let Z1 : ℝ → ℝ := fun R => C1 * R ^ 2 * Z0
  let Z2 : ℝ → ℝ := fun R => C2 * (fr * Bm R ^ 2) * Z1 R
  let Zr : ℝ → ℝ := fun R => Kr * (1 + R ^ 2)
  let L : ℝ → ℝ := fun R => 4 * C3 * Zr R * Z2 R
  let B : ℝ → ℝ := fun R => Real.sqrt (L R)
  have hρ : 0 < ρ := lt_min hρt hρc
  have hfr : 0 ≤ fr := Nat.cast_nonneg _
  have hZ0 : 0 ≤ Z0 :=
    mul_nonneg (mul_nonneg hC0 (sq_nonneg Ct)) (sq_nonneg Cc)
  have hZ1 : ∀ R : ℝ, 0 ≤ R → 0 ≤ Z1 R := by
    intro R hR
    exact mul_nonneg (mul_nonneg hC1 (sq_nonneg R)) hZ0
  have hZ2 : ∀ R : ℝ, 0 ≤ R → 0 ≤ Z2 R := by
    intro R hR
    exact mul_nonneg
      (mul_nonneg hC2 (mul_nonneg hfr (sq_nonneg (Bm R))))
      (hZ1 R hR)
  have hZr : ∀ R : ℝ, 0 ≤ R → 0 ≤ Zr R := by
    intro R hR
    exact mul_nonneg hKr (add_nonneg (by norm_num) (sq_nonneg R))
  have hL : ∀ R : ℝ, 0 ≤ R → 0 ≤ L R := by
    intro R hR
    exact mul_nonneg
      (mul_nonneg (mul_nonneg (by norm_num) hC3) (hZr R hR))
      (hZ2 R hR)
  refine ⟨ρ, B, hρ, fun R hR => Real.sqrt_nonneg _, ?_⟩
  intro gm P W hP htie δ hδ_le hδ0 hδP
    R A hR hA hP2 hP3 hW2 hPn
  let S : ℝ := (1 + A) ^ 2
  have hS : 0 ≤ S := sq_nonneg _
  have hPnt : ‖ccTensorToHs (I := I) (M := M) g 2
      (2 : ℝ) P‖ ≤ ρt := hPn.trans (min_le_left _ _)
  have hPnc : ‖ccTensorToHs (I := I) (M := M) g 2
      (2 : ℝ) P‖ ≤ ρc := hPn.trans (min_le_right _ _)
  have htr : covariantJetNormSq (I := I) (M := M) g 2
      (reindexedPureTrace (I := I) (M := M) g gm 1 (Equiv.refl _)) ≤ Ct ^ 2 := by
    rw [covariantJetNormSq_reindexedPureTrace]
    exact htrace P gm htie hPnt
  have hc : covariantJetNormSq (I := I) (M := M) g 2
      (RicciDeTurckLowOrder.connectionDifferenceLowOrderOperator (I := I) (M := M) g gm) ≤ Cc ^ 2 :=
    hconn P gm htie hPnc
  have hz0 : covariantJetNormSq (I := I) (M := M) g 2
      (ccOperatorFieldComp (I := I) (M := M) g 3 3 1
        (reindexedPureTrace (I := I) (M := M) g gm 1 (Equiv.refl _))
        (RicciDeTurckLowOrder.connectionDifferenceLowOrderOperator (I := I) (M := M) g gm)) ≤ Z0 := by
    refine (happ0 _ _).trans ?_
    simpa only [Z0] using
      mul_le_mul (mul_le_mul_of_nonneg_left htr hC0) hc
        (covariantJetNormSq_nonneg (I := I) (M := M) (m := 2) g _)
        (mul_nonneg hC0 (sq_nonneg Ct))
  have hw : covariantJetNormSq (I := I) (M := M) g 2
      (cometricRaiseSlot0Field (I := I) (M := M) g 0 W) ≤ R ^ 2 := by
    rw [covariantJetNormSq_cometricRaiseSlot0Field (I := I) (M := M) g 0 2 W]
    exact hW2
  have hz1 : covariantJetNormSq (I := I) (M := M) g 2
      (ccOperatorFieldComp (I := I) (M := M) g 3 1 1
        (cometricRaiseSlot0Field (I := I) (M := M) g 0 W)
        (ccOperatorFieldComp (I := I) (M := M) g 3 3 1
          (reindexedPureTrace (I := I) (M := M) g gm 1 (Equiv.refl _))
          (RicciDeTurckLowOrder.connectionDifferenceLowOrderOperator (I := I) (M := M) g gm))) ≤ Z1 R := by
    refine (happ1 _ _).trans ?_
    simpa only [Z1] using
      mul_le_mul (mul_le_mul_of_nonneg_left hw hC1) hz0
        (covariantJetNormSq_nonneg (I := I) (M := M) (m := 2) g _)
        (mul_nonneg hC1 (sq_nonneg R))
  have hm0 : covariantJetNormSq (I := I) (M := M) g 2
      (metricConnectionDifferenceLoweredCoefficient (I := I) (M := M) g gm g) ≤
        Bm R ^ 2 * S := by
    calc
      _ ≤ (Bm R * (1 + A)) ^ 2 :=
        hmcd gm P hP htie hδ_le hδ0 hδP
          R A hR hA hP2 hP3
      _ = Bm R ^ 2 * S := by simp only [S]; ring
  have hvm : covariantJetNormSq (I := I) (M := M) g 2
      (lieCorrectionZeroVectorBundleMetricConnectionDifferenceTerm (I := I) (M := M) g gm) ≤
        fr * Bm R ^ 2 * S := by
    refine (covariantJetNormSq_lieCorrectionZeroVectorBundleMetricConnectionDifferenceTerm_le (I := I) (M := M) g gm).trans ?_
    calc
      (Module.finrank ℝ E : ℝ) *
          covariantJetNormSq (I := I) (M := M) g 2
            (metricConnectionDifferenceLoweredCoefficient (I := I) (M := M) g gm g) ≤
        fr * (Bm R ^ 2 * S) :=
          mul_le_mul_of_nonneg_left hm0 hfr
      _ = fr * Bm R ^ 2 * S := by ring
  have hz2 : covariantJetNormSq (I := I) (M := M) g 2
      (ccOperatorFieldComp (I := I) (M := M) g 3 1 4
        (lieCorrectionZeroVectorBundleMetricConnectionDifferenceTerm (I := I) (M := M) g gm)
        (ccOperatorFieldComp (I := I) (M := M) g 3 1 1
          (cometricRaiseSlot0Field (I := I) (M := M) g 0 W)
          (ccOperatorFieldComp (I := I) (M := M) g 3 3 1
            (reindexedPureTrace (I := I) (M := M) g gm 1 (Equiv.refl _))
            (RicciDeTurckLowOrder.connectionDifferenceLowOrderOperator (I := I) (M := M) g gm)))) ≤
        Z2 R * S := by
    refine (happ2 _ _).trans ?_
    have hmul := mul_le_mul
      (mul_le_mul_of_nonneg_left hvm hC2) hz1
      (covariantJetNormSq_nonneg (I := I) (M := M) (m := 2) g _)
      (mul_nonneg hC2
        (mul_nonneg (mul_nonneg hfr (sq_nonneg (Bm R))) hS))
    refine hmul.trans_eq ?_
    simp only [Z2]
    ring
  have hr : covariantJetNormSq (I := I) (M := M) g 2
      (reindexedCometricDoubleTrace (I := I) (M := M) g gm) ≤ Zr R := by
    refine (hriem gm P hP htie hδ_le hδ0 hδP).trans ?_
    exact mul_le_mul_of_nonneg_left (add_le_add le_rfl hP2) hKr
  have hcore : covariantJetNormSq (I := I) (M := M) g 2
      (lieCorrectionZeroVectorBundleUnscaledDerivativeCoefficient (I := I) (M := M) g gm W) ≤
        C3 * Zr R * (Z2 R * S) := by
    rw [lieCorrectionZeroVectorBundleUnscaledDerivativeCoefficient]
    refine (happ3 _ _).trans ?_
    exact mul_le_mul (mul_le_mul_of_nonneg_left hr hC3) hz2
      (covariantJetNormSq_nonneg (I := I) (M := M) (m := 2) g _)
      (mul_nonneg hC3 (hZr R hR))
  rw [lieCorrectionZeroVectorBundleDerivativeCoefficient, covariantJetNormSq_smul]
  norm_num
  refine (mul_le_mul_of_nonneg_left hcore (by norm_num)).trans ?_
  calc
    4 * (C3 * Zr R * (Z2 R * S)) = L R * S := by
      simp only [L]
      ring
    _ = (B R * (1 + A)) ^ 2 := by
      have hBR : B R ^ 2 = L R := by
        simpa only [B] using Real.sq_sqrt (hL R hR)
      simpa only [S, mul_pow] using
        congrArg (fun x : ℝ => x * (1 + A) ^ 2) hBR.symm
    _ ≤ (B R * (1 + A)) ^ 2 := le_rfl

theorem covariantJetNormSq_slotExtendIter_three_le
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (F : SmoothCcTensor g r s) :
    covariantJetNormSq (I := I) (M := M) g 2
        (slotExtendIter (I := I) (M := M) g r s 3 F) ≤
      (Module.finrank ℝ E : ℝ) ^ 3 *
        covariantJetNormSq (I := I) (M := M) g 2 F := by
  let fr : ℝ := Module.finrank ℝ E
  have hfr : 0 ≤ fr := Nat.cast_nonneg _
  simp only [slotExtendIter, Nat.add_zero]
  calc
    covariantJetNormSq (I := I) (M := M) g 2
        (slotExtend (I := I) (M := M) g (r + 2) (s + 2)
          (slotExtend (I := I) (M := M) g (r + 1) (s + 1)
            (slotExtend (I := I) (M := M) g r s F))) ≤
      fr * covariantJetNormSq (I := I) (M := M) g 2
        (slotExtend (I := I) (M := M) g (r + 1) (s + 1)
          (slotExtend (I := I) (M := M) g r s F)) :=
        covariantJetNormSq_slotExtend_le (I := I) (M := M) g (r + 2) (s + 2) _
    _ ≤ fr * (fr * covariantJetNormSq (I := I) (M := M) g 2
        (slotExtend (I := I) (M := M) g r s F)) :=
      mul_le_mul_of_nonneg_left
        (covariantJetNormSq_slotExtend_le (I := I) (M := M) g (r + 1) (s + 1) _) hfr
    _ ≤ fr * (fr * (fr * covariantJetNormSq (I := I) (M := M) g 2 F)) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left
          (covariantJetNormSq_slotExtend_le (I := I) (M := M) g r s F) hfr) hfr
    _ = fr ^ 3 * covariantJetNormSq (I := I) (M := M) g 2 F := by ring

theorem exists_tensorThreeTwoProductCoefficient_covariantJetNormSq_two_bound
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ W : SmoothCcTensor g 0 2,
      covariantJetNormSq (I := I) (M := M) g 2
          (tensorThreeTwoProductCoefficient (I := I) (M := M) g W) ≤
        C * covariantJetNormSq (I := I) (M := M) g 2 W := by
  obtain ⟨Ca, hCa, happ⟩ :=
    exists_covariantJetNormSq_two_operatorFieldComposition_le (I := I) (M := M) hDim g 3 5 5
  let J : ℝ := covariantJetNormSq (I := I) (M := M) g 2
    (permCoeff (I := I) (M := M) g tensorThreeTwoBlockPermutation)
  let fr : ℝ := Module.finrank ℝ E
  let C : ℝ := Ca * J * fr ^ 3
  have hJ : 0 ≤ J := covariantJetNormSq_nonneg (I := I) (M := M) (m := 2) g _
  have hfr : 0 ≤ fr := Nat.cast_nonneg _
  have hC : 0 ≤ C :=
    mul_nonneg (mul_nonneg hCa hJ) (pow_nonneg hfr 3)
  refine ⟨C, hC, ?_⟩
  intro W
  rw [tensorThreeTwoProductCoefficient]
  refine (happ _ _).trans ?_
  have hs := covariantJetNormSq_slotExtendIter_three_le (I := I) (M := M) g 0 2 W
  have hmul := mul_le_mul_of_nonneg_left hs (mul_nonneg hCa hJ)
  refine hmul.trans_eq ?_
  simp only [J, fr, C]
  ring

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] [SigmaCompactSpace M] in
theorem slotExtendIter_sub
    (g : SmoothRiemannianMetric I M) (r s w : ℕ)
    (A B : SmoothCcTensor g r s) :
    slotExtendIter (I := I) (M := M) g r s w (A - B) =
      slotExtendIter (I := I) (M := M) g r s w A -
        slotExtendIter (I := I) (M := M) g r s w B := by
  induction w with
  | zero => simp only [slotExtendIter]
  | succ w ih =>
      change slotExtend (I := I) (M := M) g (r + w) (s + w)
          (slotExtendIter (I := I) (M := M) g r s w (A - B)) = _
      rw [ih, slotExtend_sub]
      rfl

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M]
  [SigmaCompactSpace M] in
theorem tensorThreeTwoProductCoefficient_sub
    (g : SmoothRiemannianMetric I M)
    (A B : SmoothCcTensor g 0 2) :
    tensorThreeTwoProductCoefficient (I := I) (M := M) g (A - B) =
      tensorThreeTwoProductCoefficient (I := I) (M := M) g A -
        tensorThreeTwoProductCoefficient (I := I) (M := M) g B := by
  rw [tensorThreeTwoProductCoefficient, tensorThreeTwoProductCoefficient, tensorThreeTwoProductCoefficient, ← operatorFieldComposition_sub_right,
    ← slotExtendIter_sub]

theorem exists_lieCorrectionZeroMixedConnectionDerivativeCoefficient_covariantJetNormSq_two_bound
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ ρ : ℝ, ∃ B : ℝ → ℝ, 0 < ρ ∧
      (∀ R : ℝ, 0 ≤ R → 0 ≤ B R) ∧
      ∀ (gm : SmoothRiemannianMetric I M)
        (P W : SmoothCcTensor g 0 2)
        (_hP : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g P x u v =
            ccTensorBilin (I := I) g P x v u)
        (_htie : ∀ (x : M) (u v : TangentSpace I x),
          gm.inner x u v =
            g.inner x u v + ccTensorBilinSymm (I := I) g P x u v)
        {δ : ℝ} (_hδ_le : δ ≤ 1 / 3) (_hδ0 : 0 ≤ δ)
        (_hδP : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g P) δ)
        (R A : ℝ), 0 ≤ R → 0 ≤ A →
        covariantJetNormSq (I := I) (M := M) g 2 P ≤ R ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 3 P ≤ A ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 2 W ≤ R ^ 2 →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) P‖ ≤ ρ →
      covariantJetNormSq (I := I) (M := M) g 2
          (lieCorrectionZeroMixedConnectionDerivativeCoefficient (I := I) (M := M) g gm g W) ≤
        (B R * (1 + A)) ^ 2 := by
  obtain ⟨ρ2, Ct2, hρ2, hCt2, htrace2⟩ :=
    RicciDeTurckLowOrder.trace_two_sobolev_two_bound (I := I) (M := M) hDim g
  obtain ⟨ρ3, Ct3, hρ3, hCt3, htrace3⟩ :=
    RicciDeTurckLowOrder.trace_three_sobolev_two_bound (I := I) (M := M) hDim g
  obtain ⟨ρ4, Ct4, hρ4, hCt4, htrace4⟩ :=
    RicciDeTurckLowOrder.trace_four_sobolev_two_bound (I := I) (M := M) hDim g
  obtain ⟨Bm, hBm, hmcd⟩ :=
    RicciDeTurckLowOrder.metric_connection_difference_coefficient_sobolev_two_bound (I := I) (M := M) hDim g
      (by norm_num : (0 : ℝ) ≤ 1 / 3) (by norm_num : (1 : ℝ) / 3 < 1)
  obtain ⟨Cp, hCp, hprod⟩ := exists_tensorThreeTwoProductCoefficient_covariantJetNormSq_two_bound (I := I) (M := M) hDim g
  obtain ⟨C0, hC0, happ0⟩ :=
    exists_covariantJetNormSq_two_operatorFieldComposition_le (I := I) (M := M) hDim g 3 3 5
  obtain ⟨C1, hC1, happ1⟩ :=
    exists_covariantJetNormSq_two_operatorFieldComposition_le (I := I) (M := M) hDim g 3 5 3
  obtain ⟨C2, hC2, happ2⟩ :=
    exists_covariantJetNormSq_two_operatorFieldComposition_le (I := I) (M := M) hDim g 3 3 6
  obtain ⟨C3, hC3, happ3⟩ :=
    exists_covariantJetNormSq_two_operatorFieldComposition_le (I := I) (M := M) hDim g 3 6 4
  obtain ⟨C4, hC4, happ4⟩ :=
    exists_covariantJetNormSq_two_operatorFieldComposition_le (I := I) (M := M) hDim g 3 4 2
  let ρ : ℝ := min ρ2 (min ρ3 ρ4)
  let fr : ℝ := Module.finrank ℝ E
  let Jm : ℝ := covariantJetNormSq (I := I) (M := M) g 2
    (metricConnectionDifferenceLoweringCoefficient (I := I) (M := M) g)
  let Zp : ℝ → ℝ := fun R => Cp * R ^ 2
  let Z0 : ℝ → ℝ := fun R => C0 * Zp R * Jm
  let Z1 : ℝ → ℝ := fun R => C1 * Ct3 ^ 2 * Z0 R
  let Zm : ℝ → ℝ := fun R => fr ^ 3 * Bm R ^ 2
  let Z2 : ℝ → ℝ := fun R => C2 * Zm R * Z1 R
  let Z3 : ℝ → ℝ := fun R => C3 * Ct4 ^ 2 * Z2 R
  let Q : ℝ → ℝ := fun R => C4 * Ct2 ^ 2 * Z3 R
  let L : ℝ → ℝ := fun R => 16 * Q R
  let B : ℝ → ℝ := fun R => Real.sqrt (L R)
  have hρ : 0 < ρ := lt_min hρ2 (lt_min hρ3 hρ4)
  have hfr : 0 ≤ fr := Nat.cast_nonneg _
  have hJm : 0 ≤ Jm := covariantJetNormSq_nonneg (I := I) (M := M) (m := 2) g _
  have hZp : ∀ R : ℝ, 0 ≤ R → 0 ≤ Zp R := by
    intro R hR
    exact mul_nonneg hCp (sq_nonneg R)
  have hZ0 : ∀ R : ℝ, 0 ≤ R → 0 ≤ Z0 R := by
    intro R hR
    exact mul_nonneg (mul_nonneg hC0 (hZp R hR)) hJm
  have hZ1 : ∀ R : ℝ, 0 ≤ R → 0 ≤ Z1 R := by
    intro R hR
    exact mul_nonneg (mul_nonneg hC1 (sq_nonneg Ct3)) (hZ0 R hR)
  have hZm : ∀ R : ℝ, 0 ≤ R → 0 ≤ Zm R := by
    intro R hR
    exact mul_nonneg (pow_nonneg hfr 3) (sq_nonneg (Bm R))
  have hZ2 : ∀ R : ℝ, 0 ≤ R → 0 ≤ Z2 R := by
    intro R hR
    exact mul_nonneg (mul_nonneg hC2 (hZm R hR)) (hZ1 R hR)
  have hZ3 : ∀ R : ℝ, 0 ≤ R → 0 ≤ Z3 R := by
    intro R hR
    exact mul_nonneg (mul_nonneg hC3 (sq_nonneg Ct4)) (hZ2 R hR)
  have hQ : ∀ R : ℝ, 0 ≤ R → 0 ≤ Q R := by
    intro R hR
    exact mul_nonneg (mul_nonneg hC4 (sq_nonneg Ct2)) (hZ3 R hR)
  have hL : ∀ R : ℝ, 0 ≤ R → 0 ≤ L R := by
    intro R hR
    exact mul_nonneg (by norm_num) (hQ R hR)
  refine ⟨ρ, B, hρ, fun R hR => Real.sqrt_nonneg _, ?_⟩
  intro gm P W hP htie δ hδ_le hδ0 hδP
    R A hR hA hP2 hP3 hW2 hPn
  let S : ℝ := (1 + A) ^ 2
  have hS : 0 ≤ S := sq_nonneg _
  have hPn2 : ‖ccTensorToHs (I := I) (M := M) g 2
      (2 : ℝ) P‖ ≤ ρ2 := hPn.trans (min_le_left _ _)
  have hPn3 : ‖ccTensorToHs (I := I) (M := M) g 2
      (2 : ℝ) P‖ ≤ ρ3 :=
    hPn.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hPn4 : ‖ccTensorToHs (I := I) (M := M) g 2
      (2 : ℝ) P‖ ≤ ρ4 :=
    hPn.trans ((min_le_right _ _).trans (min_le_right _ _))
  have ht2 : ∀ σ : Equiv.Perm (Fin 4),
      covariantJetNormSq (I := I) (M := M) g 2
          (reindexedPureTrace (I := I) (M := M) g gm 2 σ) ≤ Ct2 ^ 2 := by
    intro σ
    rw [covariantJetNormSq_reindexedPureTrace]
    exact htrace2 P gm htie hPn2
  have ht3 : ∀ σ : Equiv.Perm (Fin 5),
      covariantJetNormSq (I := I) (M := M) g 2
          (reindexedPureTrace (I := I) (M := M) g gm 3 σ) ≤ Ct3 ^ 2 := by
    intro σ
    rw [covariantJetNormSq_reindexedPureTrace]
    exact htrace3 P gm htie hPn3
  have ht4 : ∀ σ : Equiv.Perm (Fin 6),
      covariantJetNormSq (I := I) (M := M) g 2
          (reindexedPureTrace (I := I) (M := M) g gm 4 σ) ≤ Ct4 ^ 2 := by
    intro σ
    rw [covariantJetNormSq_reindexedPureTrace]
    exact htrace4 P gm htie hPn4
  have hp : covariantJetNormSq (I := I) (M := M) g 2
      (tensorThreeTwoProductCoefficient (I := I) (M := M) g W) ≤ Zp R := by
    refine (hprod W).trans ?_
    exact mul_le_mul_of_nonneg_left hW2 hCp
  have hm0 : covariantJetNormSq (I := I) (M := M) g 2
      (metricConnectionDifferenceLoweredCoefficient (I := I) (M := M) g gm g) ≤
        Bm R ^ 2 * S := by
    calc
      _ ≤ (Bm R * (1 + A)) ^ 2 :=
        hmcd gm P hP htie hδ_le hδ0 hδP
          R A hR hA hP2 hP3
      _ = Bm R ^ 2 * S := by simp only [S]; ring
  have hms : covariantJetNormSq (I := I) (M := M) g 2
      (slotExtendIter (I := I) (M := M) g 0 3 3
        (metricConnectionDifferenceLoweredCoefficient (I := I) (M := M) g gm g)) ≤
        Zm R * S := by
    refine (covariantJetNormSq_slotExtendIter_three_le (I := I) (M := M) g 0 3 _).trans ?_
    have hmul := mul_le_mul_of_nonneg_left hm0 (pow_nonneg hfr 3)
    refine hmul.trans_eq ?_
    simp only [Zm, fr]
    ring
  have hhalf : ∀ σlast : Equiv.Perm (Fin 4),
      covariantJetNormSq (I := I) (M := M) g 2
          (lieCorrectionZeroMixedConnectionHalfDerivativeCoefficient (I := I) (M := M) g gm g W σlast) ≤
        Q R * S := by
    intro σlast
    let X0 : SmoothCcTensor g 3 5 :=
      ccOperatorFieldComp (I := I) (M := M) g 3 3 5
        (tensorThreeTwoProductCoefficient (I := I) (M := M) g W)
        (metricConnectionDifferenceLoweringCoefficient (I := I) (M := M) g)
    let X1 : SmoothCcTensor g 3 3 :=
      ccOperatorFieldComp (I := I) (M := M) g 3 5 3
        (reindexedPureTrace (I := I) (M := M) g gm 3
          DifferentialGeometry.Analysis.Spectral.LieCorrectionZeroCore.lieCorrectionZeroMixedConnectionPermutationCycleZeroOneFour) X0
    let X2 : SmoothCcTensor g 3 6 :=
      ccOperatorFieldComp (I := I) (M := M) g 3 3 6
        (slotExtendIter (I := I) (M := M) g 0 3 3
          (metricConnectionDifferenceLoweredCoefficient (I := I) (M := M) g gm g)) X1
    let X3 : SmoothCcTensor g 3 4 :=
      ccOperatorFieldComp (I := I) (M := M) g 3 6 4
        (reindexedPureTrace (I := I) (M := M) g gm 4
          DifferentialGeometry.Analysis.Spectral.LieCorrectionZeroCore.lieCorrectionZeroMixedConnectionPermutationCycleZeroTwoThreeOne) X2
    let X4 : SmoothCcTensor g 3 2 :=
      ccOperatorFieldComp (I := I) (M := M) g 3 4 2
        (reindexedPureTrace (I := I) (M := M) g gm 2 σlast) X3
    have hx0 : covariantJetNormSq (I := I) (M := M) g 2 X0 ≤ Z0 R := by
      dsimp only [X0]
      refine (happ0 _ _).trans ?_
      simpa only [Z0, Jm] using
        mul_le_mul (mul_le_mul_of_nonneg_left hp hC0) le_rfl
          hJm (mul_nonneg hC0 (hZp R hR))
    have hx1 : covariantJetNormSq (I := I) (M := M) g 2 X1 ≤ Z1 R := by
      dsimp only [X1]
      refine (happ1 _ _).trans ?_
      simpa only [Z1] using
        mul_le_mul (mul_le_mul_of_nonneg_left
          (ht3 DifferentialGeometry.Analysis.Spectral.LieCorrectionZeroCore.lieCorrectionZeroMixedConnectionPermutationCycleZeroOneFour) hC1) hx0
          (covariantJetNormSq_nonneg (I := I) (M := M) (m := 2) g X0)
          (mul_nonneg hC1 (sq_nonneg Ct3))
    have hx2 : covariantJetNormSq (I := I) (M := M) g 2 X2 ≤ Z2 R * S := by
      dsimp only [X2]
      refine (happ2 _ _).trans ?_
      have hmul := mul_le_mul
        (mul_le_mul_of_nonneg_left hms hC2) hx1
        (covariantJetNormSq_nonneg (I := I) (M := M) (m := 2) g X1)
        (mul_nonneg hC2 (mul_nonneg (hZm R hR) hS))
      refine hmul.trans_eq ?_
      simp only [Z2]
      ring
    have hx3 : covariantJetNormSq (I := I) (M := M) g 2 X3 ≤ Z3 R * S := by
      dsimp only [X3]
      refine (happ3 _ _).trans ?_
      have hmul := mul_le_mul
        (mul_le_mul_of_nonneg_left
          (ht4 DifferentialGeometry.Analysis.Spectral.LieCorrectionZeroCore.lieCorrectionZeroMixedConnectionPermutationCycleZeroTwoThreeOne) hC3) hx2
        (covariantJetNormSq_nonneg (I := I) (M := M) (m := 2) g X2)
        (mul_nonneg hC3 (sq_nonneg Ct4))
      refine hmul.trans_eq ?_
      simp only [Z3]
      ring
    have hx4 : covariantJetNormSq (I := I) (M := M) g 2 X4 ≤ Q R * S := by
      dsimp only [X4]
      refine (happ4 _ _).trans ?_
      have hmul := mul_le_mul
        (mul_le_mul_of_nonneg_left (ht2 σlast) hC4) hx3
        (covariantJetNormSq_nonneg (I := I) (M := M) (m := 2) g X3)
        (mul_nonneg hC4 (sq_nonneg Ct2))
      refine hmul.trans_eq ?_
      simp only [Q]
      ring
    simpa only [lieCorrectionZeroMixedConnectionHalfDerivativeCoefficient, X0, X1, X2, X3, X4] using hx4
  let Y0 := lieCorrectionZeroMixedConnectionHalfDerivativeCoefficient (I := I) (M := M) g gm g W
    DifferentialGeometry.Analysis.Spectral.LieCorrectionZeroCore.lieCorrectionZeroMixedConnectionPermutationCycleZeroTwoOne
  let Y1 := lieCorrectionZeroMixedConnectionHalfDerivativeCoefficient (I := I) (M := M) g gm g W
    (lieCorrectionZeroMixedConnectionTraceOutputSwapPermutation * DifferentialGeometry.Analysis.Spectral.LieCorrectionZeroCore.lieCorrectionZeroMixedConnectionPermutationCycleZeroTwoOne)
  have hy0 : covariantJetNormSq (I := I) (M := M) g 2 Y0 ≤ Q R * S :=
    hhalf DifferentialGeometry.Analysis.Spectral.LieCorrectionZeroCore.lieCorrectionZeroMixedConnectionPermutationCycleZeroTwoOne
  have hy1 : covariantJetNormSq (I := I) (M := M) g 2 Y1 ≤ Q R * S :=
    hhalf (lieCorrectionZeroMixedConnectionTraceOutputSwapPermutation * DifferentialGeometry.Analysis.Spectral.LieCorrectionZeroCore.lieCorrectionZeroMixedConnectionPermutationCycleZeroTwoOne)
  have hadd := covariantJetNormSq_add_le (I := I) (M := M) g 2 Y0 Y1
  have hsum : covariantJetNormSq (I := I) (M := M) g 2 (Y0 + Y1) ≤
      4 * (Q R * S) := by linarith
  rw [lieCorrectionZeroMixedConnectionDerivativeCoefficient, covariantJetNormSq_smul]
  norm_num
  change 4 * covariantJetNormSq (I := I) (M := M) g 2 (Y0 + Y1) ≤ _
  refine (mul_le_mul_of_nonneg_left hsum (by norm_num)).trans ?_
  calc
    4 * (4 * (Q R * S)) = L R * S := by simp only [L]; ring
    _ = (B R * (1 + A)) ^ 2 := by
      have hBR : B R ^ 2 = L R := by
        simpa only [B] using Real.sq_sqrt (hL R hR)
      simpa only [S, mul_pow] using
        congrArg (fun x : ℝ => x * (1 + A) ^ 2) hBR.symm
    _ ≤ (B R * (1 + A)) ^ 2 := le_rfl

theorem exists_rotatedConnectionDifferenceLowOrderOperator_covariantJetNormSq_two_bound
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ ρ B : ℝ, 0 < ρ ∧ 0 ≤ B ∧
      ∀ (P : SmoothCcTensor g 0 2)
        (gm : SmoothRiemannianMetric I M),
        (∀ (x : M) (u v : TangentSpace I x),
          gm.inner x u v =
            g.inner x u v + ccTensorBilinSymm (I := I) g P x u v) →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) P‖ ≤ ρ →
        covariantJetNormSq (I := I) (M := M) g 2
            (ccOperatorFieldComp (I := I) (M := M) g 3 3 3
              (permCoeff (I := I) (M := M) g (finRotate 3))
              (RicciDeTurckLowOrder.connectionDifferenceLowOrderOperator (I := I) (M := M) g gm)) ≤
          B ^ 2 := by
  obtain ⟨ρ, Cc, hρ, hCc, hconn⟩ :=
    RicciDeTurckLowOrder.low_connection_coefficient_sobolev_two_bound (I := I) (M := M) hDim g
  obtain ⟨C0, hC0, happ0⟩ :=
    exists_covariantJetNormSq_two_operatorFieldComposition_le (I := I) (M := M) hDim g 3 3 3
  let J : ℝ := covariantJetNormSq (I := I) (M := M) g 2
    (permCoeff (I := I) (M := M) g (finRotate 3))
  let L : ℝ := C0 * J * Cc ^ 2
  let B : ℝ := Real.sqrt L
  have hJ : 0 ≤ J := covariantJetNormSq_nonneg (I := I) (M := M) (m := 2) g _
  have hL : 0 ≤ L :=
    mul_nonneg (mul_nonneg hC0 hJ) (sq_nonneg Cc)
  refine ⟨ρ, B, hρ, Real.sqrt_nonneg _, ?_⟩
  intro P gm htie hPn
  have hc : covariantJetNormSq (I := I) (M := M) g 2
      (RicciDeTurckLowOrder.connectionDifferenceLowOrderOperator (I := I) (M := M) g gm) ≤ Cc ^ 2 :=
    hconn P gm htie hPn
  refine (happ0 _ _).trans ?_
  rw [show B ^ 2 = L by simpa only [B] using Real.sq_sqrt hL]
  simpa only [L, J] using
    mul_le_mul (le_refl (C0 * J)) hc
      (covariantJetNormSq_nonneg (I := I) (M := M) (m := 2) g _)
      (mul_nonneg hC0 hJ)

omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] [SigmaCompactSpace M] in
omit [I.Boundaryless] in
theorem metricComparisonSlotInsertion_eq
    (g gm : SmoothRiemannianMetric I M) (P : SmoothCcTensor g 0 2)
    (htie : ∀ (x : M) (u v : TangentSpace I x),
      gm.inner x u v =
        g.inner x u v + ccTensorBilinSymm (I := I) g P x u v) :
    slotInsertEndoCc (I := I) (M := M) g 2
        (metricComparisonEndomorphismField (I := I) (M := M) gm g) =
      slotInsertEndoCc (I := I) (M := M) g 2
          (metricComparisonEndomorphismField (I := I) (M := M) g g) +
        slotInsertEndoCc (I := I) (M := M) g 2
          (symmRaiseEndo (I := I) (M := M) g P) := by
  have hzero : ∀ (x : M) (u v : TangentSpace I x),
      g.inner x u v = g.inner x u v +
        ccTensorBilinSymm (I := I) g
          (0 : SmoothCcTensor g 0 2) x u v := by
    intro x u v
    rw [ccTensorBilinSymm_apply, ccTensorBilin_zero_weight,
      ccTensorBilin_zero_weight]
    ring
  have hrev := RicciDeTurckLowOrder.fullRev_sub (I := I) (M := M)
    g gm g P (0 : SmoothCcTensor g 0 2) htie hzero
  rw [sub_zero] at hrev
  have hfull :
      metricComparisonEndomorphismField (I := I) (M := M) gm g =
        metricComparisonEndomorphismField (I := I) (M := M) g g +
          symmRaiseEndo (I := I) (M := M) g P := by
    calc
      _ = symmRaiseEndo (I := I) (M := M) g P +
          metricComparisonEndomorphismField (I := I) (M := M) g g :=
        sub_eq_iff_eq_add.mp hrev
      _ = _ := add_comm _ _
  rw [hfull, slotInsertEndoCc_add]

theorem exists_metricComparisonSlotInsertion_covariantJetNormSq_two_bound
    (g : SmoothRiemannianMetric I M) :
    ∃ B : ℝ → ℝ, (∀ R : ℝ, 0 ≤ R → 0 ≤ B R) ∧
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
          (slotInsertEndoCc (I := I) (M := M) g 2
            (metricComparisonEndomorphismField (I := I) (M := M) gm g)) ≤ B R ^ 2 := by
  let F₀ : SmoothCcTensor g 3 3 :=
    slotInsertEndoCc (I := I) (M := M) g 2
      (metricComparisonEndomorphismField (I := I) (M := M) g g)
  let J₀ : ℝ := covariantJetNormSq (I := I) (M := M) g 2 F₀
  let fr : ℝ := Module.finrank ℝ E
  let L : ℝ → ℝ := fun R => 2 * (J₀ + fr ^ 2 * R ^ 2)
  let B : ℝ → ℝ := fun R => Real.sqrt (L R)
  have hJ₀ : 0 ≤ J₀ := covariantJetNormSq_nonneg (I := I) (M := M) (m := 2) g F₀
  have hfr : 0 ≤ fr := Nat.cast_nonneg _
  have hL : ∀ R : ℝ, 0 ≤ L R := by
    intro R
    exact mul_nonneg (by norm_num)
      (add_nonneg hJ₀ (mul_nonneg (pow_nonneg hfr 2) (sq_nonneg R)))
  refine ⟨B, fun R hR => Real.sqrt_nonneg _, ?_⟩
  intro gm P hP htie R hR hP2
  have hsymm : symmS (I := I) (M := M) g P = P :=
    symmS_eq_self_of_ccTensorBilin_symm
      (I := I) (M := M) g P hP
  have hpert :
      covariantJetNormSq (I := I) (M := M) g 2
          (slotInsertEndoCc (I := I) (M := M) g 2
            (symmRaiseEndo (I := I) (M := M) g P)) ≤
        fr ^ 2 * R ^ 2 := by
    refine (covariantJetNormSq_slotInsertEndoCc_symmRaiseEndo_le (I := I) (M := M) g 2 2 P hsymm).trans ?_
    exact mul_le_mul_of_nonneg_left hP2 (pow_nonneg hfr 2)
  rw [metricComparisonSlotInsertion_eq (I := I) (M := M) g gm P htie]
  refine (covariantJetNormSq_add_le (I := I) (M := M) g 2 F₀
    (slotInsertEndoCc (I := I) (M := M) g 2
      (symmRaiseEndo (I := I) (M := M) g P))).trans ?_
  rw [show B R ^ 2 = L R by
    simpa only [B] using Real.sq_sqrt (hL R)]
  exact mul_le_mul_of_nonneg_left (add_le_add le_rfl hpert) (by norm_num)

theorem exists_operatorFieldComposition_covariantJetNormSq_two_bound
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) (p r c : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (Φ : SmoothCcTensor g r c) (W : SmoothCcTensor g p r)
        (X Y : ℝ), 0 ≤ X → 0 ≤ Y →
        covariantJetNormSq (I := I) (M := M) g 2 Φ ≤ X ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 2 W ≤ Y ^ 2 →
      covariantJetNormSq (I := I) (M := M) g 2
          (ccOperatorFieldComp (I := I) (M := M) g p r c Φ W) ≤
        (C * X * Y) ^ 2 := by
  obtain ⟨K, hK, happ⟩ := exists_covariantJetNormSq_two_operatorFieldComposition_le (I := I) (M := M) hDim g p r c
  let C : ℝ := Real.sqrt K
  have hC : 0 ≤ C := Real.sqrt_nonneg _
  have hCsq : C ^ 2 = K := by
    simpa only [C] using Real.sq_sqrt hK
  refine ⟨C, hC, ?_⟩
  intro Φ W X Y hX hY hΦ hW
  refine (happ Φ W).trans ?_
  calc
    K * covariantJetNormSq (I := I) (M := M) g 2 Φ *
        covariantJetNormSq (I := I) (M := M) g 2 W ≤
      K * X ^ 2 * Y ^ 2 :=
        mul_le_mul (mul_le_mul_of_nonneg_left hΦ hK) hW
          (covariantJetNormSq_nonneg (I := I) (M := M) (m := 2) g W)
          (mul_nonneg hK (sq_nonneg X))
    _ = (C * X * Y) ^ 2 := by rw [← hCsq]; ring

theorem exists_operatorFieldComposition_difference_covariantJetNormSq_two_bound
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) (p r c : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (ΦT ΦU : SmoothCcTensor g r c)
        (WT WU : SmoothCcTensor g p r)
        (FD FB WB WD : ℝ),
        0 ≤ FD → 0 ≤ FB → 0 ≤ WB → 0 ≤ WD →
        covariantJetNormSq (I := I) (M := M) g 2 (ΦT - ΦU) ≤ FD ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 2 ΦU ≤ FB ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 2 WT ≤ WB ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 2 (WT - WU) ≤ WD ^ 2 →
      covariantJetNormSq (I := I) (M := M) g 2
          (ccOperatorFieldComp (I := I) (M := M) g p r c ΦT WT -
            ccOperatorFieldComp (I := I) (M := M) g p r c ΦU WU) ≤
        (C * (FD * WB + FB * WD)) ^ 2 := by
  obtain ⟨C₀, hC₀, happ⟩ :=
    exists_operatorFieldComposition_covariantJetNormSq_two_bound (I := I) (M := M) hDim g p r c
  let C : ℝ := 2 * C₀
  refine ⟨C, mul_nonneg (by norm_num) hC₀, ?_⟩
  intro ΦT ΦU WT WU FD FB WB WD hFD hFB hWB hWD
    hΦdiff hΦU hWT hWdiff
  let X : SmoothCcTensor g p c :=
    ccOperatorFieldComp (I := I) (M := M) g p r c (ΦT - ΦU) WT
  let Y : SmoothCcTensor g p c :=
    ccOperatorFieldComp (I := I) (M := M) g p r c ΦU (WT - WU)
  let x : ℝ := C₀ * FD * WB
  let y : ℝ := C₀ * FB * WD
  have hx0 : 0 ≤ x := mul_nonneg (mul_nonneg hC₀ hFD) hWB
  have hy0 : 0 ≤ y := mul_nonneg (mul_nonneg hC₀ hFB) hWD
  have hX : covariantJetNormSq (I := I) (M := M) g 2 X ≤ x ^ 2 := by
    simpa only [X, x] using happ (ΦT - ΦU) WT FD WB hFD hWB hΦdiff hWT
  have hY : covariantJetNormSq (I := I) (M := M) g 2 Y ≤ y ^ 2 := by
    simpa only [Y, y] using happ ΦU (WT - WU) FB WD hFB hWD hΦU hWdiff
  have hsplit :
      ccOperatorFieldComp (I := I) (M := M) g p r c ΦT WT -
          ccOperatorFieldComp (I := I) (M := M) g p r c ΦU WU = X + Y := by
    simp only [X, Y, operatorFieldComposition_sub_left, operatorFieldComposition_sub_right]
    module
  rw [hsplit]
  refine (covariantJetNormSq_add_le (I := I) (M := M) g 2 X Y).trans ?_
  calc
    2 * (covariantJetNormSq (I := I) (M := M) g 2 X +
        covariantJetNormSq (I := I) (M := M) g 2 Y) ≤
      2 * (x ^ 2 + y ^ 2) :=
        mul_le_mul_of_nonneg_left (add_le_add hX hY) (by norm_num)
    _ ≤ (2 * (x + y)) ^ 2 := by
      nlinarith [sq_nonneg x, sq_nonneg y, mul_nonneg hx0 hy0]
    _ = (C * (FD * WB + FB * WD)) ^ 2 := by
      simp only [C, x, y]
      ring

omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] [SigmaCompactSpace M] in
omit [I.Boundaryless] in
theorem connectionDifferenceMetricLoweringCoefficient_eq
    (g gm : SmoothRiemannianMetric I M) :
    connectionDifferenceMetricLoweringCoefficient (I := I) (M := M) g gm =
      ccOperatorFieldComp (I := I) (M := M) g 3 3 3
        (slotInsertEndoCc (I := I) (M := M) g 2
          (metricComparisonEndomorphismField (I := I) (M := M) gm g))
        (ccOperatorFieldComp (I := I) (M := M) g 3 3 3
          (permCoeff (I := I) (M := M) g (finRotate 3))
          (RicciDeTurckLowOrder.connectionDifferenceLowOrderOperator (I := I) (M := M) g gm)) := by
  rfl

theorem exists_connectionDifferenceMetricLoweringCoefficient_product_covariantJetNormSq_two_bound
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (gm : SmoothRiemannianMetric I M) (X Y : ℝ),
        0 ≤ X → 0 ≤ Y →
        covariantJetNormSq (I := I) (M := M) g 2
            (slotInsertEndoCc (I := I) (M := M) g 2
              (metricComparisonEndomorphismField (I := I) (M := M) gm g)) ≤ X ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 2
            (ccOperatorFieldComp (I := I) (M := M) g 3 3 3
              (permCoeff (I := I) (M := M) g (finRotate 3))
              (RicciDeTurckLowOrder.connectionDifferenceLowOrderOperator (I := I) (M := M) g gm)) ≤ Y ^ 2 →
      covariantJetNormSq (I := I) (M := M) g 2
          (connectionDifferenceMetricLoweringCoefficient (I := I) (M := M) g gm) ≤ (C * X * Y) ^ 2 := by
  obtain ⟨C, hC, happ⟩ := exists_operatorFieldComposition_covariantJetNormSq_two_bound (I := I) (M := M) hDim g 3 3 3
  refine ⟨C, hC, ?_⟩
  intro gm X Y hX hY hf hi
  rw [connectionDifferenceMetricLoweringCoefficient_eq (I := I) (M := M) g gm]
  exact happ _ _ X Y hX hY hf hi

theorem exists_connectionDifferenceMetricLoweringCoefficient_covariantJetNormSq_two_bound
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ ρ : ℝ, ∃ B : ℝ → ℝ, 0 < ρ ∧
      (∀ R : ℝ, 0 ≤ R → 0 ≤ B R) ∧
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
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) P‖ ≤ ρ →
      covariantJetNormSq (I := I) (M := M) g 2
          (connectionDifferenceMetricLoweringCoefficient (I := I) (M := M) g gm) ≤ B R ^ 2 := by
  obtain ⟨ρ, Bi, hρ, hBi, hinner⟩ :=
    exists_rotatedConnectionDifferenceLowOrderOperator_covariantJetNormSq_two_bound (I := I) (M := M) hDim g
  obtain ⟨Bf, hBf, hfull⟩ := exists_metricComparisonSlotInsertion_covariantJetNormSq_two_bound (I := I) (M := M) g
  obtain ⟨Ca, hCa, hmul⟩ := exists_connectionDifferenceMetricLoweringCoefficient_product_covariantJetNormSq_two_bound (I := I) (M := M) hDim g
  let B : ℝ → ℝ := fun R => Ca * Bf R * Bi
  refine ⟨ρ, B, hρ, fun R hR =>
    mul_nonneg (mul_nonneg hCa (hBf R hR)) hBi, ?_⟩
  intro gm P hP htie R hR hP2 hPn
  have hi := hinner P gm htie hPn
  have hf : covariantJetNormSq (I := I) (M := M) g 2
      (slotInsertEndoCc (I := I) (M := M) g 2
        (metricComparisonEndomorphismField (I := I) (M := M) gm g)) ≤ Bf R ^ 2 :=
    hfull gm P hP htie R hR hP2
  exact hmul gm (Bf R) Bi (hBf R hR) hBi hf hi

theorem exists_connectionDifferenceMetricLoweringCoefficient_pairing_secondOrder_bound
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ ρ : ℝ, ∃ B : ℝ → ℝ, 0 < ρ ∧
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
            g.inner x u v + ccTensorBilinSymm (I := I) g U x u v),
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ ≤ ρ →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) U‖ ≤ ρ →
        ∀ (R D2 N : ℝ), 0 ≤ R → 0 ≤ D2 → 0 ≤ N →
        covariantJetNormSq (I := I) (M := M) g 2 T ≤ R ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 2 U ≤ R ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 2 (T - U) ≤ D2 ^ 2 →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) (T - U)‖ ≤ N →
      covariantJetNormSq (I := I) (M := M) g 2
          (connectionDifferenceMetricLoweringCoefficient (I := I) (M := M) g gT -
            connectionDifferenceMetricLoweringCoefficient (I := I) (M := M) g gU) ≤
        (B R * (D2 + N)) ^ 2 := by
  obtain ⟨ρcp, Cc, hρcp, hCc, hcp⟩ :=
    RicciDeTurckLowOrder.connLow_pair_h2 (I := I) (M := M) hDim g
  obtain ⟨ρcb, Bc, hρcb, hBc, hcb⟩ :=
    RicciDeTurckLowOrder.low_connection_coefficient_sobolev_two_bound (I := I) (M := M) hDim g
  obtain ⟨Cr, hCr, hrev⟩ :=
    RicciDeTurckLowOrder.reverse_slot_sobolev_two_bound (I := I) (M := M) g
  obtain ⟨P, hP, happ⟩ :=
    exists_operatorFieldComposition_difference_covariantJetNormSq_two_bound (I := I) (M := M) hDim g 3 3 3
  let ρ : ℝ := min ρcp ρcb
  let fr : ℝ := Module.finrank ℝ E
  let a : ℝ := fr * Bc
  let b : ℝ → ℝ := fun R => Cr * (1 + R) * Cc
  let B : ℝ → ℝ := fun R => P * (a + b R)
  have hfr : 0 ≤ fr := Nat.cast_nonneg _
  have ha : 0 ≤ a := mul_nonneg hfr hBc
  have hb : ∀ R : ℝ, 0 ≤ R → 0 ≤ b R := fun R hR =>
    mul_nonneg (mul_nonneg hCr (add_nonneg (by norm_num) hR)) hCc
  refine ⟨ρ, B, lt_min hρcp hρcb,
    fun R hR => mul_nonneg hP (add_nonneg ha (hb R hR)), ?_⟩
  intro gT gU T U hT hU hTtie hUtie hTn hUn
    R D2 N hR hD2 hN hT2 hU2 hTU2 hTUn
  have hTnc : ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ ≤ ρcp :=
    hTn.trans (min_le_left _ _)
  have hUnc : ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) U‖ ≤ ρcp :=
    hUn.trans (min_le_left _ _)
  have hTnb : ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ ≤ ρcb :=
    hTn.trans (min_le_right _ _)
  let FT : SmoothCcTensor g 3 3 :=
    slotInsertEndoCc (I := I) (M := M) g 2
      (metricComparisonEndomorphismField (I := I) (M := M) gT g)
  let FU : SmoothCcTensor g 3 3 :=
    slotInsertEndoCc (I := I) (M := M) g 2
      (metricComparisonEndomorphismField (I := I) (M := M) gU g)
  let WT : SmoothCcTensor g 3 3 :=
    ccOperatorFieldComp (I := I) (M := M) g 3 3 3
      (permCoeff (I := I) (M := M) g (finRotate 3))
      (RicciDeTurckLowOrder.connectionDifferenceLowOrderOperator (I := I) (M := M) g gT)
  let WU : SmoothCcTensor g 3 3 :=
    ccOperatorFieldComp (I := I) (M := M) g 3 3 3
      (permCoeff (I := I) (M := M) g (finRotate 3))
      (RicciDeTurckLowOrder.connectionDifferenceLowOrderOperator (I := I) (M := M) g gU)
  have hFD : covariantJetNormSq (I := I) (M := M) g 2 (FT - FU) ≤
      (fr * D2) ^ 2 := by
    calc
      covariantJetNormSq (I := I) (M := M) g 2 (FT - FU) ≤
          fr ^ 2 * covariantJetNormSq (I := I) (M := M) g 2 (T - U) := by
        simpa only [FT, FU, fr] using
          RicciDeTurckLowOrder.revSlot_pair_h2 (I := I) (M := M)
            g gT gU T U hT hU hTtie hUtie
      _ ≤ fr ^ 2 * D2 ^ 2 :=
        mul_le_mul_of_nonneg_left hTU2 (sq_nonneg fr)
      _ = (fr * D2) ^ 2 := by ring
  have hFB : covariantJetNormSq (I := I) (M := M) g 2 FU ≤
      (Cr * (1 + R)) ^ 2 := by
    simpa only [FU] using hrev gU U hU hUtie R hR hU2
  have hWT : covariantJetNormSq (I := I) (M := M) g 2 WT ≤ Bc ^ 2 := by
    change covariantJetNormSq (I := I) (M := M) g 2
      (ccOperatorFieldComp (I := I) (M := M) g 3 3 3
        (permCoeff (I := I) (M := M) g (finRotate 3))
        (RicciDeTurckLowOrder.connectionDifferenceLowOrderOperator (I := I) (M := M) g gT)) ≤ Bc ^ 2
    rw [operatorFieldComposition_permutationCoefficient_apply_eq_rsDomDomCongrSection (I := I) (M := M) g,
      covariantJetNormSq_rsDomDomCongrSection (I := I) (M := M) g]
    exact hcb T gT hTtie hTnb
  have hWD : covariantJetNormSq (I := I) (M := M) g 2 (WT - WU) ≤
      (Cc * N) ^ 2 := by
    change covariantJetNormSq (I := I) (M := M) g 2
      (ccOperatorFieldComp (I := I) (M := M) g 3 3 3
          (permCoeff (I := I) (M := M) g (finRotate 3))
          (RicciDeTurckLowOrder.connectionDifferenceLowOrderOperator (I := I) (M := M) g gT) -
        ccOperatorFieldComp (I := I) (M := M) g 3 3 3
          (permCoeff (I := I) (M := M) g (finRotate 3))
          (RicciDeTurckLowOrder.connectionDifferenceLowOrderOperator (I := I) (M := M) g gU)) ≤
        (Cc * N) ^ 2
    rw [← operatorFieldComposition_sub_right]
    have hp := operatorFieldComposition_permutationCoefficient_apply_eq_rsDomDomCongrSection (I := I) (M := M) g (finRotate 3)
      (RicciDeTurckLowOrder.connectionDifferenceLowOrderOperator (I := I) (M := M) g gT -
        RicciDeTurckLowOrder.connectionDifferenceLowOrderOperator (I := I) (M := M) g gU)
    rw [hp, covariantJetNormSq_rsDomDomCongrSection (I := I) (M := M) g]
    have hc := hcp T U gT gU hTtie hUtie hTnc hUnc
    exact hc.trans (pow_le_pow_left₀
      (mul_nonneg hCc (norm_nonneg _))
      (mul_le_mul_of_nonneg_left hTUn hCc) 2)
  have hraw := happ FT FU WT WU
    (fr * D2) (Cr * (1 + R)) Bc (Cc * N)
    (mul_nonneg hfr hD2)
    (mul_nonneg hCr (add_nonneg (by norm_num) hR)) hBc
    (mul_nonneg hCc hN) hFD hFB hWT hWD
  let L : ℝ := P * (a * D2 + b R * N)
  have hL0 : 0 ≤ L :=
    mul_nonneg hP (add_nonneg (mul_nonneg ha hD2)
      (mul_nonneg (hb R hR) hN))
  have hraw' : covariantJetNormSq (I := I) (M := M) g 2
      (connectionDifferenceMetricLoweringCoefficient (I := I) (M := M) g gT -
        connectionDifferenceMetricLoweringCoefficient (I := I) (M := M) g gU) ≤ L ^ 2 := by
    have hraw0 : covariantJetNormSq (I := I) (M := M) g 2
        (connectionDifferenceMetricLoweringCoefficient (I := I) (M := M) g gT -
          connectionDifferenceMetricLoweringCoefficient (I := I) (M := M) g gU) ≤
        (P * (fr * D2 * Bc + Cr * (1 + R) * (Cc * N))) ^ 2 := by
      simpa only [connectionDifferenceMetricLoweringCoefficient, FT, FU, WT, WU] using hraw
    refine hraw0.trans_eq ?_
    simp only [L, a, b]
    ring
  have hlead : L ≤ B R * (D2 + N) := by
    simp only [L, B]
    calc
      P * (a * D2 + b R * N) ≤
          P * ((a + b R) * (D2 + N)) :=
        mul_le_mul_of_nonneg_left
          (by nlinarith [mul_nonneg ha hN, mul_nonneg (hb R hR) hD2]) hP
      _ = P * (a + b R) * (D2 + N) := by rw [mul_assoc]
  exact hraw'.trans (pow_le_pow_left₀ hL0 hlead 2)

private theorem quadratic_arm_pairing_scale_sq (p l o b d a q : ℝ) :
    (p * ((l * a * q) * o + (b * a) * (d * q))) ^ 2 =
      (p * (l * o + b * d) * a * q) ^ 2 := by
  ring

theorem exists_connectionDifferenceQuadraticArmDerivativeCoefficients_pairing_secondOrder_bound
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ ρ : ℝ, ∃ B : ℝ → ℝ, 0 < ρ ∧
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
        {δ : ℝ} (_hδ_le : δ ≤ 1 / 3) (_hδ0 : 0 ≤ δ)
        (_hδT : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) δ)
        (_hδU : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g U) δ)
        (_hδZ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g
            (0 : SmoothCcTensor g 0 2)) δ),
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ ≤ ρ →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) U‖ ≤ ρ →
        ∀ (R A D2 D3 N : ℝ),
        0 ≤ R → 0 ≤ A → 0 ≤ D2 → 0 ≤ D3 → 0 ≤ N →
        covariantJetNormSq (I := I) (M := M) g 2 T ≤ R ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 2 U ≤ R ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 3 T ≤ A ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 3 U ≤ A ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 2 (T - U) ≤ D2 ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 3 (T - U) ≤ D3 ^ 2 →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) (T - U)‖ ≤ N →
      let D := D3 + D2 + A * D2 + N
      covariantJetNormSq (I := I) (M := M) g 2
          (connectionDifferenceQuadraticPairedDerivativeCoefficient (I := I) (M := M) g gT -
            connectionDifferenceQuadraticPairedDerivativeCoefficient (I := I) (M := M) g gU) ≤
          (B R * (1 + A) * D) ^ 2 ∧
        covariantJetNormSq (I := I) (M := M) g 2
          (connectionDifferenceQuadraticComposedDerivativeCoefficient (I := I) (M := M) g gT -
            connectionDifferenceQuadraticComposedDerivativeCoefficient (I := I) (M := M) g gU) ≤
          (B R * (1 + A) * D) ^ 2 := by
  obtain ⟨ρop, Bod, hρop, hBod, hop⟩ :=
    exists_connectionDifferenceMetricLoweringCoefficient_pairing_secondOrder_bound (I := I) (M := M) hDim g
  obtain ⟨ρob, Bo, hρob, hBo, hob⟩ :=
    exists_connectionDifferenceMetricLoweringCoefficient_covariantJetNormSq_two_bound (I := I) (M := M) hDim g
  obtain ⟨L0, L1, hL0, hL1, hlp⟩ :=
    lieArm2_pair_h2 (I := I) (M := M) hDim g
  obtain ⟨Bl, hBl, hlb⟩ :=
    deTurck_lie_arm_two_coefficient_sobolev_two_bound (I := I) (M := M) hDim g
  obtain ⟨P, hP, happ⟩ :=
    exists_operatorFieldComposition_difference_covariantJetNormSq_two_bound (I := I) (M := M) hDim g 3 3 4
  let ρ : ℝ := min ρop ρob
  let Ld : ℝ → ℝ := fun R => L0 R + L1 R
  let B : ℝ → ℝ := fun R =>
    P * (Ld R * Bo R + Bl R * Bod R)
  have hLd : ∀ R : ℝ, 0 ≤ R → 0 ≤ Ld R := fun R hR =>
    add_nonneg (hL0 R hR) (hL1 R hR)
  have hB : ∀ R : ℝ, 0 ≤ R → 0 ≤ B R := fun R hR =>
    mul_nonneg hP
      (add_nonneg (mul_nonneg (hLd R hR) (hBo R hR))
        (mul_nonneg (hBl R hR) (hBod R hR)))
  refine ⟨ρ, B, lt_min hρop hρob, hB, ?_⟩
  intro gT gU T U hT hU hTtie hUtie δ hδ_le hδ0 hδT hδU hδZ
    hTn hUn R A D2 D3 N hR hA hD2 hD3 hN
    hT2 hU2 hT3 hU3 hTU2 hTU3 hTUn
  dsimp only
  let D : ℝ := D3 + D2 + A * D2 + N
  have hD : 0 ≤ D :=
    add_nonneg (add_nonneg (add_nonneg hD3 hD2) (mul_nonneg hA hD2)) hN
  have honeA : 0 ≤ 1 + A := add_nonneg (by norm_num) hA
  have hTnop : ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ ≤ ρop :=
    hTn.trans (min_le_left _ _)
  have hUnop : ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) U‖ ≤ ρop :=
    hUn.trans (min_le_left _ _)
  have hTnob : ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ ≤ ρob :=
    hTn.trans (min_le_right _ _)
  let LT : SmoothCcTensor g 3 4 := deTurckLieCovariantDerivativeArmTwoCoefficient (I := I) (M := M) g gT
  let LU : SmoothCcTensor g 3 4 := deTurckLieCovariantDerivativeArmTwoCoefficient (I := I) (M := M) g gU
  let OT : SmoothCcTensor g 3 3 := connectionDifferenceMetricLoweringCoefficient (I := I) (M := M) g gT
  let OU : SmoothCcTensor g 3 3 := connectionDifferenceMetricLoweringCoefficient (I := I) (M := M) g gU
  have hlraw := hlp gT gU T U hT hU hTtie hUtie
    hδ_le hδ0 hδT hδ_le hδ0 hδU
    R A D2 D3 hR hA hD2 hD3 hU2 hT3 hTU2 hTU3
  let X : ℝ := L0 R * D3 + L1 R * D2 + L1 R * A * D2
  have hX : 0 ≤ X :=
    add_nonneg (add_nonneg (mul_nonneg (hL0 R hR) hD3)
      (mul_nonneg (hL1 R hR) hD2))
      (mul_nonneg (mul_nonneg (hL1 R hR) hA) hD2)
  have hXD : X ≤ Ld R * D := by
    simp only [X, Ld, D]
    exact weighted_three_term_le_product_sum (L0 R) (L1 R) D3 D2 A N
      (hL0 R hR) (hL1 R hR) hD3 hD2 hA hN
  have hXDA : X ≤ Ld R * (1 + A) * D := by
    refine hXD.trans ?_
    exact mul_le_mul_one_add (Ld R) A D (hLd R hR) hA hD
  have hLD : covariantJetNormSq (I := I) (M := M) g 2 (LT - LU) ≤
      (Ld R * (1 + A) * D) ^ 2 := by
    have h0 : covariantJetNormSq (I := I) (M := M) g 2 (LT - LU) ≤ X ^ 2 := by
      simpa only [LT, LU, X] using hlraw
    exact h0.trans (pow_le_pow_left₀ hX hXDA 2)
  have hlU : covariantJetNormSq (I := I) (M := M) g 2 LU ≤
      (Bl R * (1 + A)) ^ 2 := by
    have h0 : covariantJetNormSq (I := I) (M := M) g 2 LU ≤
        (Bl R * A) ^ 2 := by
      simpa only [LU] using hlb gU U hU hUtie hδ_le hδ0 hδU hδZ
        R A hR hA hU2 hU3
    exact h0.trans (pow_le_pow_left₀ (mul_nonneg (hBl R hR) hA)
      (mul_le_mul_of_nonneg_left (le_add_of_nonneg_left zero_le_one) (hBl R hR)) 2)
  have hoT : covariantJetNormSq (I := I) (M := M) g 2 OT ≤ (Bo R) ^ 2 := by
    simpa only [OT] using hob gT T hT hTtie R hR hT2 hTnob
  have hop0 := hop gT gU T U hT hU hTtie hUtie hTnop hUnop
    R D2 N hR hD2 hN hT2 hU2 hTU2 hTUn
  have hsmall : D2 + N ≤ D := by
    simp only [D]
    exact add_le_four_term_sum D3 D2 A N hD3 hD2 hA
  have hoD : covariantJetNormSq (I := I) (M := M) g 2 (OT - OU) ≤
      (Bod R * D) ^ 2 := by
    have h0 : covariantJetNormSq (I := I) (M := M) g 2 (OT - OU) ≤
        (Bod R * (D2 + N)) ^ 2 := by
      simpa only [OT, OU] using hop0
    exact h0.trans (pow_le_pow_left₀
      (mul_nonneg (hBod R hR) (add_nonneg hD2 hN))
      (mul_le_mul_of_nonneg_left hsmall (hBod R hR)) 2)
  have hqraw := happ LT LU OT OU
    (Ld R * (1 + A) * D) (Bl R * (1 + A))
    (Bo R) (Bod R * D)
    (mul_nonneg (mul_nonneg (hLd R hR) honeA) hD)
    (mul_nonneg (hBl R hR) honeA) (hBo R hR)
    (mul_nonneg (hBod R hR) hD) hLD hlU hoT hoD
  have hq : covariantJetNormSq (I := I) (M := M) g 2
      (connectionDifferenceQuadraticPairedDerivativeCoefficient (I := I) (M := M) g gT -
        connectionDifferenceQuadraticPairedDerivativeCoefficient (I := I) (M := M) g gU) ≤
      (B R * (1 + A) * D) ^ 2 := by
    have h0 : covariantJetNormSq (I := I) (M := M) g 2
        (connectionDifferenceQuadraticPairedDerivativeCoefficient (I := I) (M := M) g gT -
          connectionDifferenceQuadraticPairedDerivativeCoefficient (I := I) (M := M) g gU) ≤
        (P * ((Ld R * (1 + A) * D) * Bo R +
          (Bl R * (1 + A)) * (Bod R * D))) ^ 2 := by
      simpa only [connectionDifferenceQuadraticPairedDerivativeCoefficient, LT, LU, OT, OU] using hqraw
    refine h0.trans_eq ?_
    simpa only [B] using
      quadratic_arm_pairing_scale_sq P (Ld R) (Bo R) (Bl R) (Bod R) (1 + A) D
  let ST : SmoothCcTensor g 3 3 :=
    ccOperatorFieldComp (I := I) (M := M) g 3 3 3
      (permCoeff (I := I) (M := M) g (Equiv.swap (0 : Fin 3) 1)) OT
  let SU : SmoothCcTensor g 3 3 :=
    ccOperatorFieldComp (I := I) (M := M) g 3 3 3
      (permCoeff (I := I) (M := M) g (Equiv.swap (0 : Fin 3) 1)) OU
  have hsT : covariantJetNormSq (I := I) (M := M) g 2 ST ≤ (Bo R) ^ 2 := by
    change covariantJetNormSq (I := I) (M := M) g 2
      (ccOperatorFieldComp (I := I) (M := M) g 3 3 3
        (permCoeff (I := I) (M := M) g (Equiv.swap (0 : Fin 3) 1)) OT) ≤
      (Bo R) ^ 2
    rw [operatorFieldComposition_permutationCoefficient_apply_eq_rsDomDomCongrSection (I := I) (M := M) g,
      covariantJetNormSq_rsDomDomCongrSection (I := I) (M := M) g]
    exact hoT
  have hsD : covariantJetNormSq (I := I) (M := M) g 2 (ST - SU) ≤
      (Bod R * D) ^ 2 := by
    change covariantJetNormSq (I := I) (M := M) g 2
      (ccOperatorFieldComp (I := I) (M := M) g 3 3 3
          (permCoeff (I := I) (M := M) g (Equiv.swap (0 : Fin 3) 1)) OT -
        ccOperatorFieldComp (I := I) (M := M) g 3 3 3
          (permCoeff (I := I) (M := M) g (Equiv.swap (0 : Fin 3) 1)) OU) ≤
      (Bod R * D) ^ 2
    rw [← operatorFieldComposition_sub_right]
    have hp := operatorFieldComposition_permutationCoefficient_apply_eq_rsDomDomCongrSection (I := I) (M := M) g (Equiv.swap (0 : Fin 3) 1) (OT - OU)
    rw [hp, covariantJetNormSq_rsDomDomCongrSection (I := I) (M := M) g]
    exact hoD
  have haraw := happ LT LU ST SU
    (Ld R * (1 + A) * D) (Bl R * (1 + A))
    (Bo R) (Bod R * D)
    (mul_nonneg (mul_nonneg (hLd R hR) honeA) hD)
    (mul_nonneg (hBl R hR) honeA) (hBo R hR)
    (mul_nonneg (hBod R hR) hD) hLD hlU hsT hsD
  have ha : covariantJetNormSq (I := I) (M := M) g 2
      (connectionDifferenceQuadraticComposedDerivativeCoefficient (I := I) (M := M) g gT -
        connectionDifferenceQuadraticComposedDerivativeCoefficient (I := I) (M := M) g gU) ≤
      (B R * (1 + A) * D) ^ 2 := by
    have h0 : covariantJetNormSq (I := I) (M := M) g 2
        (connectionDifferenceQuadraticComposedDerivativeCoefficient (I := I) (M := M) g gT -
          connectionDifferenceQuadraticComposedDerivativeCoefficient (I := I) (M := M) g gU) ≤
        (P * ((Ld R * (1 + A) * D) * Bo R +
          (Bl R * (1 + A)) * (Bod R * D))) ^ 2 := by
      simpa only [connectionDifferenceQuadraticComposedDerivativeCoefficient, LT, LU, ST, SU, OT, OU] using haraw
    refine h0.trans_eq ?_
    simpa only [B] using
      quadratic_arm_pairing_scale_sq P (Ld R) (Bo R) (Bl R) (Bod R) (1 + A) D
  exact ⟨hq, ha⟩

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
private theorem covariantJetNormSq_sum_six_sq_le
    (g : SmoothRiemannianMetric I M) {r s : ℕ}
    (A B C D E' F : SmoothCcTensor g r s) (X : ℝ)
    (hA : covariantJetNormSq (I := I) (M := M) g 2 A ≤ X ^ 2)
    (hB : covariantJetNormSq (I := I) (M := M) g 2 B ≤ X ^ 2)
    (hC : covariantJetNormSq (I := I) (M := M) g 2 C ≤ X ^ 2)
    (hD : covariantJetNormSq (I := I) (M := M) g 2 D ≤ X ^ 2)
    (hE : covariantJetNormSq (I := I) (M := M) g 2 E' ≤ X ^ 2)
    (hF : covariantJetNormSq (I := I) (M := M) g 2 F ≤ X ^ 2) :
    covariantJetNormSq (I := I) (M := M) g 2 (A + B + C + D + E' + F) ≤
      (32 * X) ^ 2 := by
  have hAB : covariantJetNormSq (I := I) (M := M) g 2 (A + B) ≤
      (2 * X) ^ 2 := by
    refine (covariantJetNormSq_add_le (I := I) (M := M) g 2 A B).trans ?_
    nlinarith [sq_nonneg X]
  have hABC : covariantJetNormSq (I := I) (M := M) g 2 (A + B + C) ≤
      (4 * X) ^ 2 := by
    refine (covariantJetNormSq_add_le (I := I) (M := M) g 2 (A + B) C).trans ?_
    nlinarith [sq_nonneg X]
  have hABCD : covariantJetNormSq (I := I) (M := M) g 2 (A + B + C + D) ≤
      (8 * X) ^ 2 := by
    refine (covariantJetNormSq_add_le (I := I) (M := M) g 2 (A + B + C) D).trans ?_
    nlinarith [sq_nonneg X]
  have hABCDE : covariantJetNormSq (I := I) (M := M) g 2
      (A + B + C + D + E') ≤ (16 * X) ^ 2 := by
    refine (covariantJetNormSq_add_le (I := I) (M := M) g 2 (A + B + C + D) E').trans ?_
    nlinarith [sq_nonneg X]
  refine (covariantJetNormSq_add_le (I := I) (M := M) g 2
    (A + B + C + D + E') F).trans ?_
  nlinarith [sq_nonneg X]

theorem exists_connectionDifferenceQuadraticCurvatureDerivativeCoefficient_pairing_secondOrder_bound
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ ρ : ℝ, ∃ B : ℝ → ℝ, 0 < ρ ∧
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
        {δ : ℝ} (_hδ_le : δ ≤ 1 / 3) (_hδ0 : 0 ≤ δ)
        (_hδT : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) δ)
        (_hδU : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g U) δ)
        (_hδZ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g
            (0 : SmoothCcTensor g 0 2)) δ),
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ ≤ ρ →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) U‖ ≤ ρ →
        ∀ (R A D2 D3 N : ℝ),
        0 ≤ R → 0 ≤ A → 0 ≤ D2 → 0 ≤ D3 → 0 ≤ N →
        covariantJetNormSq (I := I) (M := M) g 2 T ≤ R ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 2 U ≤ R ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 3 T ≤ A ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 3 U ≤ A ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 2 (T - U) ≤ D2 ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 3 (T - U) ≤ D3 ^ 2 →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) (T - U)‖ ≤ N →
      covariantJetNormSq (I := I) (M := M) g 2
          (connectionDifferenceQuadraticCurvatureDerivativeCoefficient (I := I) (M := M) g gT -
            connectionDifferenceQuadraticCurvatureDerivativeCoefficient (I := I) (M := M) g gU) ≤
        (B R * (1 + A) * (D3 + D2 + A * D2 + N)) ^ 2 := by
  obtain ⟨ρ, Bq, hρ, hBq, hqba⟩ :=
    exists_connectionDifferenceQuadraticArmDerivativeCoefficients_pairing_secondOrder_bound (I := I) (M := M) hDim g
  let B : ℝ → ℝ := fun R => 32 * Bq R
  refine ⟨ρ, B, hρ,
    fun R hR => mul_nonneg (by norm_num) (hBq R hR), ?_⟩
  intro gT gU T U hT hU hTtie hUtie δ hδ_le hδ0 hδT hδU hδZ
    hTn hUn R A D2 D3 N hR hA hD2 hD3 hN
    hT2 hU2 hT3 hU3 hTU2 hTU3 hTUn
  let S : ℝ := Bq R * (1 + A) * (D3 + D2 + A * D2 + N)
  have hpair := hqba gT gU T U hT hU hTtie hUtie
    hδ_le hδ0 hδT hδU hδZ hTn hUn
    R A D2 D3 N hR hA hD2 hD3 hN
    hT2 hU2 hT3 hU3 hTU2 hTU3 hTUn
  have hq : covariantJetNormSq (I := I) (M := M) g 2
      (connectionDifferenceQuadraticPairedDerivativeCoefficient (I := I) (M := M) g gT -
        connectionDifferenceQuadraticPairedDerivativeCoefficient (I := I) (M := M) g gU) ≤ S ^ 2 := by
    simpa only [S] using hpair.1
  have ha : covariantJetNormSq (I := I) (M := M) g 2
      (connectionDifferenceQuadraticComposedDerivativeCoefficient (I := I) (M := M) g gT -
        connectionDifferenceQuadraticComposedDerivativeCoefficient (I := I) (M := M) g gU) ≤ S ^ 2 := by
    simpa only [S] using hpair.2
  let Q0 : SmoothCcTensor g 3 4 :=
    ccOperatorFieldComp (I := I) (M := M) g 3 4 4
      (permCoeff (I := I) (M := M) g (Equiv.swap (0 : Fin 4) 1))
      (connectionDifferenceQuadraticPairedDerivativeCoefficient (I := I) (M := M) g gT) -
    ccOperatorFieldComp (I := I) (M := M) g 3 4 4
      (permCoeff (I := I) (M := M) g (Equiv.swap (0 : Fin 4) 1))
      (connectionDifferenceQuadraticPairedDerivativeCoefficient (I := I) (M := M) g gU)
  let Q1 : SmoothCcTensor g 3 4 :=
    connectionDifferenceQuadraticPairedDerivativeCoefficient (I := I) (M := M) g gT - connectionDifferenceQuadraticPairedDerivativeCoefficient (I := I) (M := M) g gU
  let A0 : SmoothCcTensor g 3 4 :=
    ccOperatorFieldComp (I := I) (M := M) g 3 4 4
      (permCoeff (I := I) (M := M) g lrPermA)
      (connectionDifferenceQuadraticComposedDerivativeCoefficient (I := I) (M := M) g gT) -
    ccOperatorFieldComp (I := I) (M := M) g 3 4 4
      (permCoeff (I := I) (M := M) g lrPermA)
      (connectionDifferenceQuadraticComposedDerivativeCoefficient (I := I) (M := M) g gU)
  let A1 : SmoothCcTensor g 3 4 :=
    ccOperatorFieldComp (I := I) (M := M) g 3 4 4
      (permCoeff (I := I) (M := M) g (Equiv.swap (0 : Fin 4) 2))
      (connectionDifferenceQuadraticComposedDerivativeCoefficient (I := I) (M := M) g gT) -
    ccOperatorFieldComp (I := I) (M := M) g 3 4 4
      (permCoeff (I := I) (M := M) g (Equiv.swap (0 : Fin 4) 2))
      (connectionDifferenceQuadraticComposedDerivativeCoefficient (I := I) (M := M) g gU)
  let A2 : SmoothCcTensor g 3 4 :=
    ccOperatorFieldComp (I := I) (M := M) g 3 4 4
      (permCoeff (I := I) (M := M) g lrPermB)
      (connectionDifferenceQuadraticComposedDerivativeCoefficient (I := I) (M := M) g gT) -
    ccOperatorFieldComp (I := I) (M := M) g 3 4 4
      (permCoeff (I := I) (M := M) g lrPermB)
      (connectionDifferenceQuadraticComposedDerivativeCoefficient (I := I) (M := M) g gU)
  let A3 : SmoothCcTensor g 3 4 :=
    ccOperatorFieldComp (I := I) (M := M) g 3 4 4
      (permCoeff (I := I) (M := M) g lrPermC)
      (connectionDifferenceQuadraticComposedDerivativeCoefficient (I := I) (M := M) g gT) -
    ccOperatorFieldComp (I := I) (M := M) g 3 4 4
      (permCoeff (I := I) (M := M) g lrPermC)
      (connectionDifferenceQuadraticComposedDerivativeCoefficient (I := I) (M := M) g gU)
  have hperm (σ : Equiv.Perm (Fin 4)) :
      covariantJetNormSq (I := I) (M := M) g 2
          (ccOperatorFieldComp (I := I) (M := M) g 3 4 4
              (permCoeff (I := I) (M := M) g σ)
              (connectionDifferenceQuadraticComposedDerivativeCoefficient (I := I) (M := M) g gT) -
            ccOperatorFieldComp (I := I) (M := M) g 3 4 4
              (permCoeff (I := I) (M := M) g σ)
              (connectionDifferenceQuadraticComposedDerivativeCoefficient (I := I) (M := M) g gU)) ≤ S ^ 2 := by
    rw [← operatorFieldComposition_sub_right]
    have hp := operatorFieldComposition_permutationCoefficient_apply_eq_rsDomDomCongrSection (I := I) (M := M) g σ
      (connectionDifferenceQuadraticComposedDerivativeCoefficient (I := I) (M := M) g gT - connectionDifferenceQuadraticComposedDerivativeCoefficient (I := I) (M := M) g gU)
    rw [hp, covariantJetNormSq_rsDomDomCongrSection (I := I) (M := M) g]
    exact ha
  have hQ0 : covariantJetNormSq (I := I) (M := M) g 2 Q0 ≤ S ^ 2 := by
    change covariantJetNormSq (I := I) (M := M) g 2
      (ccOperatorFieldComp (I := I) (M := M) g 3 4 4
          (permCoeff (I := I) (M := M) g (Equiv.swap (0 : Fin 4) 1))
          (connectionDifferenceQuadraticPairedDerivativeCoefficient (I := I) (M := M) g gT) -
        ccOperatorFieldComp (I := I) (M := M) g 3 4 4
          (permCoeff (I := I) (M := M) g (Equiv.swap (0 : Fin 4) 1))
          (connectionDifferenceQuadraticPairedDerivativeCoefficient (I := I) (M := M) g gU)) ≤ S ^ 2
    rw [← operatorFieldComposition_sub_right]
    have hp := operatorFieldComposition_permutationCoefficient_apply_eq_rsDomDomCongrSection (I := I) (M := M) g (Equiv.swap (0 : Fin 4) 1)
      (connectionDifferenceQuadraticPairedDerivativeCoefficient (I := I) (M := M) g gT - connectionDifferenceQuadraticPairedDerivativeCoefficient (I := I) (M := M) g gU)
    rw [hp, covariantJetNormSq_rsDomDomCongrSection (I := I) (M := M) g]
    exact hq
  have hQ1 : covariantJetNormSq (I := I) (M := M) g 2 Q1 ≤ S ^ 2 := by
    simpa only [Q1] using hq
  have hA0 : covariantJetNormSq (I := I) (M := M) g 2 A0 ≤ S ^ 2 := by
    simpa only [A0] using hperm lrPermA
  have hA1 : covariantJetNormSq (I := I) (M := M) g 2 A1 ≤ S ^ 2 := by
    simpa only [A1] using hperm (Equiv.swap (0 : Fin 4) 2)
  have hA2 : covariantJetNormSq (I := I) (M := M) g 2 A2 ≤ S ^ 2 := by
    simpa only [A2] using hperm lrPermB
  have hA3 : covariantJetNormSq (I := I) (M := M) g 2 A3 ≤ S ^ 2 := by
    simpa only [A3] using hperm lrPermC
  have hsplit :
      connectionDifferenceQuadraticCurvatureDerivativeCoefficient (I := I) (M := M) g gT - connectionDifferenceQuadraticCurvatureDerivativeCoefficient (I := I) (M := M) g gU =
        Q0 + Q1 + A0 + A1 + A2 + A3 := by
    simp only [connectionDifferenceQuadraticCurvatureDerivativeCoefficient, Q0, Q1, A0, A1, A2, A3]
    module
  rw [hsplit]
  have hsum := covariantJetNormSq_sum_six_sq_le (I := I) (M := M) g
    Q0 Q1 A0 A1 A2 A3 S hQ0 hQ1 hA0 hA1 hA2 hA3
  refine hsum.trans_eq ?_
  simp only [B, S]
  ring

theorem exists_deTurckLieCovariantDerivativeArmTwoCoefficient_covariantJetNormSq_two_bound
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ B : ℝ → ℝ, (∀ R : ℝ, 0 ≤ R → 0 ≤ B R) ∧
      ∀ (gm : SmoothRiemannianMetric I M)
        (P : SmoothCcTensor g 0 2)
        (_hP : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g P x u v =
            ccTensorBilin (I := I) g P x v u)
        (_htie : ∀ (x : M) (u v : TangentSpace I x),
          gm.inner x u v =
            g.inner x u v + ccTensorBilinSymm (I := I) g P x u v)
        {δ : ℝ} (_hδ_le : δ ≤ 1 / 3) (_hδ0 : 0 ≤ δ)
        (_hδP : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g P) δ)
        (_hδZ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g
            (0 : SmoothCcTensor g 0 2)) δ)
        (R A : ℝ), 0 ≤ R → 0 ≤ A →
        covariantJetNormSq (I := I) (M := M) g 2 P ≤ R ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 3 P ≤ A ^ 2 →
      covariantJetNormSq (I := I) (M := M) g 2
          (deTurckLieCovariantDerivativeArmTwoCoefficient (I := I) (M := M) g gm) ≤
        (B R * (1 + A)) ^ 2 := by
  obtain ⟨Bc, hBc, hconn⟩ := exists_connectionDifferenceContravariantInsertionField_covariantJetNormSq_two_bound (I := I) (M := M) hDim g
  obtain ⟨Ca, hCa, happ⟩ := exists_operatorFieldComposition_covariantJetNormSq_two_bound (I := I) (M := M) hDim g 3 4 4
  let J : ℝ := covariantJetNormSq (I := I) (M := M) g 2
    (permCoeff (I := I) (M := M) g ricciQuadraticPermutationSwapBlocks)
  let Cp : ℝ := Real.sqrt J
  let B : ℝ → ℝ := fun R => Ca * Cp * Bc R
  have hJ : 0 ≤ J := covariantJetNormSq_nonneg (I := I) (M := M) (m := 2) g _
  have hCp : 0 ≤ Cp := Real.sqrt_nonneg _
  have hCp2 : Cp ^ 2 = J := by
    simpa only [Cp] using Real.sq_sqrt hJ
  have hperm : covariantJetNormSq (I := I) (M := M) g 2
      (permCoeff (I := I) (M := M) g ricciQuadraticPermutationSwapBlocks) ≤ Cp ^ 2 := by
    change J ≤ Cp ^ 2
    exact hCp2.symm.le
  refine ⟨B, fun R hR =>
    mul_nonneg (mul_nonneg hCa hCp) (hBc R hR), ?_⟩
  intro gm P hP htie δ hδ_le hδ0 hδP hδZ R A hR hA hP2 hP3
  have hc := hconn gm P hP htie hδ_le hδ0 hδP hδZ
    R A hR hA hP2 hP3
  have hraw := happ
    (permCoeff (I := I) (M := M) g ricciQuadraticPermutationSwapBlocks)
    (connectionDifferenceContravariantInsertionField (I := I) g gm)
    Cp (Bc R * (1 + A)) hCp
    (mul_nonneg (hBc R hR) (add_nonneg (by norm_num) hA))
    hperm hc
  rw [deTurckLieCovariantDerivativeArmTwoCoefficient_eq_permuted_connectionDifferenceContravariantInsertionField (I := I) (M := M) g gm]
  refine hraw.trans_eq ?_
  simp only [B]
  ring

theorem exists_connectionDifferenceQuadraticArmDerivativeCoefficients_covariantJetNormSq_two_bound
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ ρ : ℝ, ∃ Bq Ba : ℝ → ℝ, 0 < ρ ∧
      (∀ R : ℝ, 0 ≤ R → 0 ≤ Bq R) ∧
      (∀ R : ℝ, 0 ≤ R → 0 ≤ Ba R) ∧
      ∀ (gm : SmoothRiemannianMetric I M)
        (P : SmoothCcTensor g 0 2)
        (_hP : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g P x u v =
            ccTensorBilin (I := I) g P x v u)
        (_htie : ∀ (x : M) (u v : TangentSpace I x),
          gm.inner x u v =
            g.inner x u v + ccTensorBilinSymm (I := I) g P x u v)
        {δ : ℝ} (_hδ_le : δ ≤ 1 / 3) (_hδ0 : 0 ≤ δ)
        (_hδP : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g P) δ)
        (_hδZ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g
            (0 : SmoothCcTensor g 0 2)) δ)
        (R A : ℝ), 0 ≤ R → 0 ≤ A →
        covariantJetNormSq (I := I) (M := M) g 2 P ≤ R ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 3 P ≤ A ^ 2 →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) P‖ ≤ ρ →
      covariantJetNormSq (I := I) (M := M) g 2
          (connectionDifferenceQuadraticPairedDerivativeCoefficient (I := I) (M := M) g gm) ≤
          (Bq R * (1 + A)) ^ 2 ∧
        covariantJetNormSq (I := I) (M := M) g 2
          (connectionDifferenceQuadraticComposedDerivativeCoefficient (I := I) (M := M) g gm) ≤
          (Ba R * (1 + A)) ^ 2 := by
  obtain ⟨ρ, Bo, hρ, hBo, homega⟩ :=
    exists_connectionDifferenceMetricLoweringCoefficient_covariantJetNormSq_two_bound (I := I) (M := M) hDim g
  obtain ⟨Bl, hBl, harm⟩ := exists_deTurckLieCovariantDerivativeArmTwoCoefficient_covariantJetNormSq_two_bound (I := I) (M := M) hDim g
  obtain ⟨Cb, hCb, hb⟩ := exists_operatorFieldComposition_covariantJetNormSq_two_bound (I := I) (M := M) hDim g 3 3 4
  obtain ⟨Cs, hCs, hs⟩ := exists_operatorFieldComposition_covariantJetNormSq_two_bound (I := I) (M := M) hDim g 3 3 3
  let Jp : ℝ := covariantJetNormSq (I := I) (M := M) g 2
    (permCoeff (I := I) (M := M) g (Equiv.swap (0 : Fin 3) 1))
  let Cp : ℝ := Real.sqrt Jp
  let Bs : ℝ → ℝ := fun R => Cs * Cp * Bo R
  let Bq : ℝ → ℝ := fun R => Cb * Bl R * Bo R
  let Ba : ℝ → ℝ := fun R => Cb * Bl R * Bs R
  have hJp : 0 ≤ Jp := covariantJetNormSq_nonneg (I := I) (M := M) (m := 2) g _
  have hCp : 0 ≤ Cp := Real.sqrt_nonneg _
  have hCp2 : Cp ^ 2 = Jp := by
    simpa only [Cp] using Real.sq_sqrt hJp
  have hp : covariantJetNormSq (I := I) (M := M) g 2
      (permCoeff (I := I) (M := M) g
        (Equiv.swap (0 : Fin 3) 1)) ≤ Cp ^ 2 := by
    change Jp ≤ Cp ^ 2
    exact hCp2.symm.le
  have hBs : ∀ R : ℝ, 0 ≤ R → 0 ≤ Bs R := by
    intro R hR
    exact mul_nonneg (mul_nonneg hCs hCp) (hBo R hR)
  refine ⟨ρ, Bq, Ba, hρ,
    fun R hR => mul_nonneg (mul_nonneg hCb (hBl R hR)) (hBo R hR),
    fun R hR => mul_nonneg (mul_nonneg hCb (hBl R hR)) (hBs R hR), ?_⟩
  intro gm P hP htie δ hδ_le hδ0 hδP hδZ R A hR hA hP2 hP3 hPn
  have ho := homega gm P hP htie R hR hP2 hPn
  have hl := harm gm P hP htie hδ_le hδ0 hδP hδZ
    R A hR hA hP2 hP3
  have honeA : 0 ≤ 1 + A := add_nonneg (by norm_num) hA
  have hqraw := hb
    (deTurckLieCovariantDerivativeArmTwoCoefficient (I := I) (M := M) g gm)
    (connectionDifferenceMetricLoweringCoefficient (I := I) (M := M) g gm)
    (Bl R * (1 + A)) (Bo R)
    (mul_nonneg (hBl R hR) honeA) (hBo R hR) hl ho
  have hq : covariantJetNormSq (I := I) (M := M) g 2
      (connectionDifferenceQuadraticPairedDerivativeCoefficient (I := I) (M := M) g gm) ≤
      (Bq R * (1 + A)) ^ 2 := by
    change covariantJetNormSq (I := I) (M := M) g 2
      (ccOperatorFieldComp (I := I) (M := M) g 3 3 4
        (deTurckLieCovariantDerivativeArmTwoCoefficient (I := I) (M := M) g gm)
        (connectionDifferenceMetricLoweringCoefficient (I := I) (M := M) g gm)) ≤ _
    refine hqraw.trans_eq ?_
    simp only [Bq]
    ring
  have hsraw := hs
    (permCoeff (I := I) (M := M) g (Equiv.swap (0 : Fin 3) 1))
    (connectionDifferenceMetricLoweringCoefficient (I := I) (M := M) g gm)
    Cp (Bo R) hCp (hBo R hR) hp ho
  have hswap : covariantJetNormSq (I := I) (M := M) g 2
      (ccOperatorFieldComp (I := I) (M := M) g 3 3 3
        (permCoeff (I := I) (M := M) g (Equiv.swap (0 : Fin 3) 1))
        (connectionDifferenceMetricLoweringCoefficient (I := I) (M := M) g gm)) ≤ Bs R ^ 2 := by
    refine hsraw.trans_eq ?_
    simp only [Bs]
  have haraw := hb
    (deTurckLieCovariantDerivativeArmTwoCoefficient (I := I) (M := M) g gm)
    (ccOperatorFieldComp (I := I) (M := M) g 3 3 3
      (permCoeff (I := I) (M := M) g (Equiv.swap (0 : Fin 3) 1))
      (connectionDifferenceMetricLoweringCoefficient (I := I) (M := M) g gm))
    (Bl R * (1 + A)) (Bs R)
    (mul_nonneg (hBl R hR) honeA) (hBs R hR) hl hswap
  have ha : covariantJetNormSq (I := I) (M := M) g 2
      (connectionDifferenceQuadraticComposedDerivativeCoefficient (I := I) (M := M) g gm) ≤
      (Ba R * (1 + A)) ^ 2 := by
    change covariantJetNormSq (I := I) (M := M) g 2
      (ccOperatorFieldComp (I := I) (M := M) g 3 3 4
        (deTurckLieCovariantDerivativeArmTwoCoefficient (I := I) (M := M) g gm)
        (ccOperatorFieldComp (I := I) (M := M) g 3 3 3
          (permCoeff (I := I) (M := M) g (Equiv.swap (0 : Fin 3) 1))
          (connectionDifferenceMetricLoweringCoefficient (I := I) (M := M) g gm))) ≤ _
    refine haraw.trans_eq ?_
    simp only [Ba]
    ring
  exact ⟨hq, ha⟩

private noncomputable def quadraticCurvaturePermutationJetCap
    (g : SmoothRiemannianMetric I M) : ℝ :=
  covariantJetNormSq (I := I) (M := M) g 2
      (permCoeff (I := I) (M := M) g (Equiv.swap (0 : Fin 4) 1)) +
    covariantJetNormSq (I := I) (M := M) g 2
      (permCoeff (I := I) (M := M) g lrPermA) +
    covariantJetNormSq (I := I) (M := M) g 2
      (permCoeff (I := I) (M := M) g (Equiv.swap (0 : Fin 4) 2)) +
    covariantJetNormSq (I := I) (M := M) g 2
      (permCoeff (I := I) (M := M) g lrPermB) +
    covariantJetNormSq (I := I) (M := M) g 2
      (permCoeff (I := I) (M := M) g lrPermC)

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
private theorem quadraticCurvaturePermutationJetCap_nonneg (g : SmoothRiemannianMetric I M) :
    0 ≤ quadraticCurvaturePermutationJetCap (I := I) (M := M) g := by
  unfold quadraticCurvaturePermutationJetCap
  have h0 := covariantJetNormSq_nonneg (I := I) (M := M) (m := 2) g
    (permCoeff (I := I) (M := M) g (Equiv.swap (0 : Fin 4) 1))
  have h1 := covariantJetNormSq_nonneg (I := I) (M := M) (m := 2) g
    (permCoeff (I := I) (M := M) g lrPermA)
  have h2 := covariantJetNormSq_nonneg (I := I) (M := M) (m := 2) g
    (permCoeff (I := I) (M := M) g (Equiv.swap (0 : Fin 4) 2))
  have h3 := covariantJetNormSq_nonneg (I := I) (M := M) (m := 2) g
    (permCoeff (I := I) (M := M) g lrPermB)
  have h4 := covariantJetNormSq_nonneg (I := I) (M := M) (m := 2) g
    (permCoeff (I := I) (M := M) g lrPermC)
  linarith

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
private theorem covariantJetNormSq_permutationCoefficient_le_quadraticCurvaturePermutationJetCap
    (g : SmoothRiemannianMetric I M) (pm : Equiv.Perm (Fin 4))
    (hpm : pm = Equiv.swap (0 : Fin 4) 1 ∨ pm = lrPermA ∨
      pm = Equiv.swap (0 : Fin 4) 2 ∨ pm = lrPermB ∨ pm = lrPermC) :
    covariantJetNormSq (I := I) (M := M) g 2
        (permCoeff (I := I) (M := M) g pm) ≤
      quadraticCurvaturePermutationJetCap (I := I) (M := M) g := by
  have h0 := covariantJetNormSq_nonneg (I := I) (M := M) (m := 2) g
    (permCoeff (I := I) (M := M) g (Equiv.swap (0 : Fin 4) 1))
  have h1 := covariantJetNormSq_nonneg (I := I) (M := M) (m := 2) g
    (permCoeff (I := I) (M := M) g lrPermA)
  have h2 := covariantJetNormSq_nonneg (I := I) (M := M) (m := 2) g
    (permCoeff (I := I) (M := M) g (Equiv.swap (0 : Fin 4) 2))
  have h3 := covariantJetNormSq_nonneg (I := I) (M := M) (m := 2) g
    (permCoeff (I := I) (M := M) g lrPermB)
  have h4 := covariantJetNormSq_nonneg (I := I) (M := M) (m := 2) g
    (permCoeff (I := I) (M := M) g lrPermC)
  unfold quadraticCurvaturePermutationJetCap
  rcases hpm with rfl | rfl | rfl | rfl | rfl <;> linarith

theorem exists_connectionDifferenceQuadraticCurvatureDerivativeCoefficient_covariantJetNormSq_two_bound
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ ρ : ℝ, ∃ B : ℝ → ℝ, 0 < ρ ∧
      (∀ R : ℝ, 0 ≤ R → 0 ≤ B R) ∧
      ∀ (gm : SmoothRiemannianMetric I M)
        (P : SmoothCcTensor g 0 2)
        (_hP : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g P x u v =
            ccTensorBilin (I := I) g P x v u)
        (_htie : ∀ (x : M) (u v : TangentSpace I x),
          gm.inner x u v =
            g.inner x u v + ccTensorBilinSymm (I := I) g P x u v)
        {δ : ℝ} (_hδ_le : δ ≤ 1 / 3) (_hδ0 : 0 ≤ δ)
        (_hδP : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g P) δ)
        (_hδZ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g
            (0 : SmoothCcTensor g 0 2)) δ)
        (R A : ℝ), 0 ≤ R → 0 ≤ A →
        covariantJetNormSq (I := I) (M := M) g 2 P ≤ R ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 3 P ≤ A ^ 2 →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) P‖ ≤ ρ →
      covariantJetNormSq (I := I) (M := M) g 2
          (connectionDifferenceQuadraticCurvatureDerivativeCoefficient (I := I) (M := M) g gm) ≤
        (B R * (1 + A)) ^ 2 := by
  obtain ⟨ρ, Bq, Ba, hρ, hBq, hBa, hqba⟩ :=
    exists_connectionDifferenceQuadraticArmDerivativeCoefficients_covariantJetNormSq_two_bound (I := I) (M := M) hDim g
  obtain ⟨Ca, hCa, happ⟩ := exists_operatorFieldComposition_covariantJetNormSq_two_bound (I := I) (M := M) hDim g 3 4 4
  let Jp : ℝ := quadraticCurvaturePermutationJetCap (I := I) (M := M) g
  let Cp : ℝ := Real.sqrt Jp
  let D : ℝ → ℝ := fun R => Bq R + Ba R
  let E₀ : ℝ := 1 + Ca * Cp
  let L : ℝ → ℝ := fun R => 94 * (E₀ * D R) ^ 2
  let B : ℝ → ℝ := fun R => Real.sqrt (L R)
  have hJp : 0 ≤ Jp := quadraticCurvaturePermutationJetCap_nonneg (I := I) (M := M) g
  have hCp : 0 ≤ Cp := Real.sqrt_nonneg _
  have hCp2 : Cp ^ 2 = Jp := by
    simpa only [Cp] using Real.sq_sqrt hJp
  have hD : ∀ R : ℝ, 0 ≤ R → 0 ≤ D R := by
    intro R hR
    exact add_nonneg (hBq R hR) (hBa R hR)
  have hE₀ : 0 ≤ E₀ :=
    add_nonneg (by norm_num) (mul_nonneg hCa hCp)
  have hL : ∀ R : ℝ, 0 ≤ R → 0 ≤ L R := by
    intro R hR
    exact mul_nonneg (by norm_num) (sq_nonneg _)
  refine ⟨ρ, B, hρ, fun R hR => Real.sqrt_nonneg _, ?_⟩
  intro gm P hP htie δ hδ_le hδ0 hδP hδZ R A hR hA hP2 hP3 hPn
  obtain ⟨hqb, hqa⟩ := hqba gm P hP htie hδ_le hδ0 hδP hδZ
    R A hR hA hP2 hP3 hPn
  have honeA : 0 ≤ 1 + A := add_nonneg (by norm_num) hA
  have hamp : 0 ≤ D R * (1 + A) := mul_nonneg (hD R hR) honeA
  have hqbD : covariantJetNormSq (I := I) (M := M) g 2
      (connectionDifferenceQuadraticPairedDerivativeCoefficient (I := I) (M := M) g gm) ≤
      (D R * (1 + A)) ^ 2 := by
    refine hqb.trans (pow_le_pow_left₀
      (mul_nonneg (hBq R hR) honeA) ?_ 2)
    exact mul_le_mul_of_nonneg_right
      (le_add_of_nonneg_right (hBa R hR)) honeA
  have hqaD : covariantJetNormSq (I := I) (M := M) g 2
      (connectionDifferenceQuadraticComposedDerivativeCoefficient (I := I) (M := M) g gm) ≤
      (D R * (1 + A)) ^ 2 := by
    refine hqa.trans (pow_le_pow_left₀
      (mul_nonneg (hBa R hR) honeA) ?_ 2)
    exact mul_le_mul_of_nonneg_right
      (le_add_of_nonneg_left (hBq R hR)) honeA
  have hperm (pm : Equiv.Perm (Fin 4))
      (hpm : pm = Equiv.swap (0 : Fin 4) 1 ∨ pm = lrPermA ∨
        pm = Equiv.swap (0 : Fin 4) 2 ∨ pm = lrPermB ∨ pm = lrPermC) :
      covariantJetNormSq (I := I) (M := M) g 2
          (permCoeff (I := I) (M := M) g pm) ≤ Cp ^ 2 := by
    refine (covariantJetNormSq_permutationCoefficient_le_quadraticCurvaturePermutationJetCap (I := I) (M := M) g pm hpm).trans_eq ?_
    exact hCp2.symm
  let Q : ℝ := (E₀ * D R * (1 + A)) ^ 2
  have hsmall : Ca * Cp ≤ E₀ := by
    simp only [E₀]
    linarith
  have hone : (1 : ℝ) ≤ E₀ := by
    simp only [E₀]
    exact le_add_of_nonneg_right (mul_nonneg hCa hCp)
  have hqbQ : covariantJetNormSq (I := I) (M := M) g 2
      (connectionDifferenceQuadraticPairedDerivativeCoefficient (I := I) (M := M) g gm) ≤ Q := by
    refine hqbD.trans ?_
    simp only [Q]
    refine pow_le_pow_left₀ hamp ?_ 2
    calc
      D R * (1 + A) = 1 * D R * (1 + A) := by ring
      _ ≤ E₀ * D R * (1 + A) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hone (hD R hR)) honeA
  have hact (pm : Equiv.Perm (Fin 4))
      (hpm : pm = Equiv.swap (0 : Fin 4) 1 ∨ pm = lrPermA ∨
        pm = Equiv.swap (0 : Fin 4) 2 ∨ pm = lrPermB ∨ pm = lrPermC)
      (W : SmoothCcTensor g 3 4)
      (hW : covariantJetNormSq (I := I) (M := M) g 2 W ≤
        (D R * (1 + A)) ^ 2) :
      covariantJetNormSq (I := I) (M := M) g 2
          (ccOperatorFieldComp (I := I) (M := M) g 3 4 4
            (permCoeff (I := I) (M := M) g pm) W) ≤ Q := by
    have hraw := happ
      (permCoeff (I := I) (M := M) g pm) W
      Cp (D R * (1 + A)) hCp hamp (hperm pm hpm) hW
    refine hraw.trans ?_
    simp only [Q]
    refine pow_le_pow_left₀ (mul_nonneg (mul_nonneg hCa hCp) hamp) ?_ 2
    calc
      Ca * Cp * (D R * (1 + A)) = Ca * Cp * D R * (1 + A) := by ring
      _ ≤ E₀ * D R * (1 + A) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hsmall (hD R hR)) honeA
  have hx0 := hact (Equiv.swap (0 : Fin 4) 1) (Or.inl rfl) _ hqbD
  have hx1 := hqbQ
  have hx2 := hact lrPermA (Or.inr (Or.inl rfl)) _ hqaD
  have hx3 := hact (Equiv.swap (0 : Fin 4) 2)
    (Or.inr (Or.inr (Or.inl rfl))) _ hqaD
  have hx4 := hact lrPermB
    (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) _ hqaD
  have hx5 := hact lrPermC
    (Or.inr (Or.inr (Or.inr (Or.inr rfl)))) _ hqaD
  rw [connectionDifferenceQuadraticCurvatureDerivativeCoefficient]
  refine (covariantJetNormSq_sum_six_le (I := I) (M := M) g 2 _ _ _ _ _ _
    hx0 hx1 hx2 hx3 hx4 hx5).trans ?_
  calc
    94 * Q = L R * (1 + A) ^ 2 := by simp only [Q, L]; ring
    _ = B R ^ 2 * (1 + A) ^ 2 := by
      rw [show B R ^ 2 = L R by
        simpa only [B] using Real.sq_sqrt (hL R hR)]
    _ = (B R * (1 + A)) ^ 2 := by ring
    _ ≤ (B R * (1 + A)) ^ 2 := le_rfl

theorem covariantJetNormSq_slotExtendIter_two_le
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (F : SmoothCcTensor g r s) :
    covariantJetNormSq (I := I) (M := M) g 2
        (slotExtendIter (I := I) (M := M) g r s 2 F) ≤
      (Module.finrank ℝ E : ℝ) ^ 2 *
        covariantJetNormSq (I := I) (M := M) g 2 F := by
  let fr : ℝ := Module.finrank ℝ E
  have hfr : 0 ≤ fr := Nat.cast_nonneg _
  simp only [slotExtendIter, Nat.add_zero]
  calc
    covariantJetNormSq (I := I) (M := M) g 2
        (slotExtend (I := I) (M := M) g (r + 1) (s + 1)
          (slotExtend (I := I) (M := M) g r s F)) ≤
      fr * covariantJetNormSq (I := I) (M := M) g 2
        (slotExtend (I := I) (M := M) g r s F) :=
      covariantJetNormSq_slotExtend_le (I := I) (M := M) g (r + 1) (s + 1) _
    _ ≤ fr * (fr * covariantJetNormSq (I := I) (M := M) g 2 F) :=
      mul_le_mul_of_nonneg_left
        (covariantJetNormSq_slotExtend_le (I := I) (M := M) g r s F) hfr
    _ = fr ^ 2 * covariantJetNormSq (I := I) (M := M) g 2 F := by ring

theorem exists_lieCorrectionQuadraticFirstDerivativeIntermediateCoefficient_covariantJetNormSq_two_bound
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ ρ : ℝ, ∃ B : ℝ → ℝ, 0 < ρ ∧
      (∀ R : ℝ, 0 ≤ R → 0 ≤ B R) ∧
      ∀ (gm : SmoothRiemannianMetric I M)
        (P W : SmoothCcTensor g 0 2)
        (_hP : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g P x u v =
            ccTensorBilin (I := I) g P x v u)
        (_htie : ∀ (x : M) (u v : TangentSpace I x),
          gm.inner x u v =
            g.inner x u v + ccTensorBilinSymm (I := I) g P x u v)
        {δ : ℝ} (_hδ_le : δ ≤ 1 / 3) (_hδ0 : 0 ≤ δ)
        (_hδP : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g P) δ)
        (_hδZ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g
            (0 : SmoothCcTensor g 0 2)) δ)
        (R A : ℝ), 0 ≤ R → 0 ≤ A →
        covariantJetNormSq (I := I) (M := M) g 2 P ≤ R ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 3 P ≤ A ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 2 W ≤ R ^ 2 →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) P‖ ≤ ρ →
      covariantJetNormSq (I := I) (M := M) g 2
          (lieCorrectionQuadraticFirstDerivativeIntermediateCoefficient (I := I) (M := M) g gm W) ≤
        (B R * (1 + A)) ^ 2 := by
  obtain ⟨ρ, Bo, hρ, hBo, hop⟩ :=
    exists_connectionDifferenceQuadraticCurvatureDerivativeCoefficient_covariantJetNormSq_two_bound (I := I) (M := M) hDim g
  obtain ⟨Ct, hCt, hprod⟩ := exists_tensorThreeTwoProductCoefficient_covariantJetNormSq_two_bound (I := I) (M := M) hDim g
  obtain ⟨Ca, hCa, happ⟩ := exists_operatorFieldComposition_covariantJetNormSq_two_bound (I := I) (M := M) hDim g 3 5 6
  let fr : ℝ := Module.finrank ℝ E
  let Cr : ℝ := Real.sqrt Ct
  let B : ℝ → ℝ := fun R => Ca * fr * Bo R * Cr * R
  have hfr : 0 ≤ fr := Nat.cast_nonneg _
  have hCr : 0 ≤ Cr := Real.sqrt_nonneg _
  have hCr2 : Cr ^ 2 = Ct := by
    simpa only [Cr] using Real.sq_sqrt hCt
  refine ⟨ρ, B, hρ, fun R hR =>
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hCa hfr) (hBo R hR)) hCr) hR,
    ?_⟩
  intro gm P W hP htie δ hδ_le hδ0 hδP hδZ
    R A hR hA hP2 hP3 hW2 hPn
  have hop' := hop gm P hP htie hδ_le hδ0 hδP hδZ
    R A hR hA hP2 hP3 hPn
  have honeA : 0 ≤ 1 + A := add_nonneg (by norm_num) hA
  have hslot : covariantJetNormSq (I := I) (M := M) g 2
      (slotExtendIter (I := I) (M := M) g 3 4 2
        (connectionDifferenceQuadraticCurvatureDerivativeCoefficient (I := I) (M := M) g gm)) ≤
      (fr * Bo R * (1 + A)) ^ 2 := by
    refine (covariantJetNormSq_slotExtendIter_two_le (I := I) (M := M) g 3 4 _).trans ?_
    calc
      fr ^ 2 * covariantJetNormSq (I := I) (M := M) g 2
          (connectionDifferenceQuadraticCurvatureDerivativeCoefficient (I := I) (M := M) g gm) ≤
        fr ^ 2 * (Bo R * (1 + A)) ^ 2 :=
          mul_le_mul_of_nonneg_left hop' (pow_nonneg hfr 2)
      _ = (fr * Bo R * (1 + A)) ^ 2 := by ring
  have hp : covariantJetNormSq (I := I) (M := M) g 2
      (tensorThreeTwoProductCoefficient (I := I) (M := M) g W) ≤ (Cr * R) ^ 2 := by
    refine (hprod W).trans ?_
    calc
      Ct * covariantJetNormSq (I := I) (M := M) g 2 W ≤ Ct * R ^ 2 :=
        mul_le_mul_of_nonneg_left hW2 hCt
      _ = (Cr * R) ^ 2 := by rw [mul_pow, hCr2]
  rw [lieCorrectionQuadraticFirstDerivativeIntermediateCoefficient]
  have hraw := happ
    (slotExtendIter (I := I) (M := M) g 3 4 2
      (connectionDifferenceQuadraticCurvatureDerivativeCoefficient (I := I) (M := M) g gm))
    (tensorThreeTwoProductCoefficient (I := I) (M := M) g W)
    (fr * Bo R * (1 + A)) (Cr * R)
    (mul_nonneg (mul_nonneg hfr (hBo R hR)) honeA)
    (mul_nonneg hCr hR) hslot hp
  refine hraw.trans_eq ?_
  simp only [B]
  ring

theorem exists_lieCorrectionQuadraticFirstDerivativeCoefficient_covariantJetNormSq_two_bound
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ ρ : ℝ, ∃ B : ℝ → ℝ, 0 < ρ ∧
      (∀ R : ℝ, 0 ≤ R → 0 ≤ B R) ∧
      ∀ (gm : SmoothRiemannianMetric I M)
        (P W : SmoothCcTensor g 0 2)
        (_hP : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g P x u v =
            ccTensorBilin (I := I) g P x v u)
        (_htie : ∀ (x : M) (u v : TangentSpace I x),
          gm.inner x u v =
            g.inner x u v + ccTensorBilinSymm (I := I) g P x u v)
        {δ : ℝ} (_hδ_le : δ ≤ 1 / 3) (_hδ0 : 0 ≤ δ)
        (_hδP : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g P) δ)
        (_hδZ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g
            (0 : SmoothCcTensor g 0 2)) δ)
        (R A : ℝ), 0 ≤ R → 0 ≤ A →
        covariantJetNormSq (I := I) (M := M) g 2 P ≤ R ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 3 P ≤ A ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 2 W ≤ R ^ 2 →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) P‖ ≤ ρ →
      covariantJetNormSq (I := I) (M := M) g 2
          (lieCorrectionQuadraticFirstDerivativeCoefficient (I := I) (M := M) g gm W) ≤
        (B R * (1 + A)) ^ 2 := by
  obtain ⟨ρm, Bm, hρm, hBm, hmid⟩ :=
    exists_lieCorrectionQuadraticFirstDerivativeIntermediateCoefficient_covariantJetNormSq_two_bound (I := I) (M := M) hDim g
  obtain ⟨ρp, Bp, hρp, hBp, hpair⟩ :=
    RicciDeTurckLowOrder.pair_trace_sobolev_two_bound (I := I) (M := M) hDim g
  obtain ⟨Ca, hCa, happ⟩ := exists_operatorFieldComposition_covariantJetNormSq_two_bound (I := I) (M := M) hDim g 3 6 2
  let ρ : ℝ := min ρm ρp
  let B : ℝ → ℝ := fun R => Ca * Bp * Bm R
  have hρ : 0 < ρ := lt_min hρm hρp
  refine ⟨ρ, B, hρ, fun R hR =>
    mul_nonneg (mul_nonneg hCa hBp) (hBm R hR), ?_⟩
  intro gm P W hP htie δ hδ_le hδ0 hδP hδZ
    R A hR hA hP2 hP3 hW2 hPn
  have hPnM : ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) P‖ ≤ ρm :=
    hPn.trans (min_le_left _ _)
  have hPnP : ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) P‖ ≤ ρp :=
    hPn.trans (min_le_right _ _)
  have hm := hmid gm P W hP htie hδ_le hδ0 hδP hδZ
    R A hR hA hP2 hP3 hW2 hPnM
  have hp : covariantJetNormSq (I := I) (M := M) g 2
      (cometricDoublePairTraceCoefficient (I := I) (M := M) g gm) ≤ Bp ^ 2 :=
    hpair P gm htie hPnP
  have hs : covariantJetNormSq (I := I) (M := M) g 2
      (ccOperatorFieldComp (I := I) (M := M) g 3 6 6
        (permCoeff (I := I) (M := M) g deTurckLieCovariantDerivativePairTracePermutation)
        (lieCorrectionQuadraticFirstDerivativeIntermediateCoefficient (I := I) (M := M) g gm W)) ≤
      (Bm R * (1 + A)) ^ 2 := by
    rw [operatorFieldComposition_permutationCoefficient_apply_eq_rsDomDomCongrSection (I := I) (M := M) g deTurckLieCovariantDerivativePairTracePermutation,
      covariantJetNormSq_rsDomDomCongrSection (I := I) (M := M) g]
    exact hm
  rw [lieCorrectionQuadraticFirstDerivativeCoefficient]
  have hraw := happ
    (cometricDoublePairTraceCoefficient (I := I) (M := M) g gm)
    (ccOperatorFieldComp (I := I) (M := M) g 3 6 6
      (permCoeff (I := I) (M := M) g deTurckLieCovariantDerivativePairTracePermutation)
      (lieCorrectionQuadraticFirstDerivativeIntermediateCoefficient (I := I) (M := M) g gm W))
    Bp (Bm R * (1 + A)) hBp
    (mul_nonneg (hBm R hR) (add_nonneg (by norm_num) hA)) hp hs
  refine hraw.trans_eq ?_
  simp only [B]
  ring

private theorem intermediate_coefficient_pairing_scale_sq (p f c d b r a q : ℝ) :
    (p * ((f * d * a * q) * (c * r) +
      (f * b * a) * (c * q))) ^ 2 =
      (p * f * c * (d * r + b) * a * q) ^ 2 := by
  ring

theorem exists_lieCorrectionQuadraticFirstDerivativeIntermediateCoefficient_pairing_secondOrder_bound
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ ρ : ℝ, ∃ B : ℝ → ℝ, 0 < ρ ∧
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
        {δ : ℝ} (_hδ_le : δ ≤ 1 / 3) (_hδ0 : 0 ≤ δ)
        (_hδT : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) δ)
        (_hδU : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g U) δ)
        (_hδZ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g
            (0 : SmoothCcTensor g 0 2)) δ),
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ ≤ ρ →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) U‖ ≤ ρ →
        ∀ (R A D2 D3 N : ℝ),
        0 ≤ R → 0 ≤ A → 0 ≤ D2 → 0 ≤ D3 → 0 ≤ N →
        covariantJetNormSq (I := I) (M := M) g 2 T ≤ R ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 2 U ≤ R ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 3 T ≤ A ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 3 U ≤ A ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 2 (T - U) ≤ D2 ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 3 (T - U) ≤ D3 ^ 2 →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) (T - U)‖ ≤ N →
      covariantJetNormSq (I := I) (M := M) g 2
          (lieCorrectionQuadraticFirstDerivativeIntermediateCoefficient (I := I) (M := M) g gT T -
            lieCorrectionQuadraticFirstDerivativeIntermediateCoefficient (I := I) (M := M) g gU U) ≤
        (B R * (1 + A) * (D3 + D2 + A * D2 + N)) ^ 2 := by
  obtain ⟨ρd, Bd, hρd, hBd, hopd⟩ :=
    exists_connectionDifferenceQuadraticCurvatureDerivativeCoefficient_pairing_secondOrder_bound (I := I) (M := M) hDim g
  obtain ⟨ρb, Bb, hρb, hBb, hopb⟩ :=
    exists_connectionDifferenceQuadraticCurvatureDerivativeCoefficient_covariantJetNormSq_two_bound (I := I) (M := M) hDim g
  obtain ⟨Ct, hCt, hprod⟩ := exists_tensorThreeTwoProductCoefficient_covariantJetNormSq_two_bound (I := I) (M := M) hDim g
  obtain ⟨P, hP, happ⟩ :=
    exists_operatorFieldComposition_difference_covariantJetNormSq_two_bound (I := I) (M := M) hDim g 3 5 6
  let ρ : ℝ := min ρd ρb
  let fr : ℝ := Module.finrank ℝ E
  let Cr : ℝ := Real.sqrt Ct
  let B : ℝ → ℝ := fun R =>
    P * fr * Cr * (Bd R * R + Bb R)
  have hfr : 0 ≤ fr := Nat.cast_nonneg _
  have hCr : 0 ≤ Cr := Real.sqrt_nonneg _
  have hCr2 : Cr ^ 2 = Ct := by
    simpa only [Cr] using Real.sq_sqrt hCt
  have hB : ∀ R : ℝ, 0 ≤ R → 0 ≤ B R := fun R hR =>
    mul_nonneg (mul_nonneg (mul_nonneg hP hfr) hCr)
      (add_nonneg (mul_nonneg (hBd R hR) hR) (hBb R hR))
  refine ⟨ρ, B, lt_min hρd hρb, hB, ?_⟩
  intro gT gU T U hT hU hTtie hUtie δ hδ_le hδ0 hδT hδU hδZ
    hTn hUn R A D2 D3 N hR hA hD2 hD3 hN
    hT2 hU2 hT3 hU3 hTU2 hTU3 hTUn
  let D : ℝ := D3 + D2 + A * D2 + N
  have hD : 0 ≤ D :=
    add_nonneg (add_nonneg (add_nonneg hD3 hD2) (mul_nonneg hA hD2)) hN
  have honeA : 0 ≤ 1 + A := add_nonneg (by norm_num) hA
  have hTnd : ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ ≤ ρd :=
    hTn.trans (min_le_left _ _)
  have hUnd : ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) U‖ ≤ ρd :=
    hUn.trans (min_le_left _ _)
  have hUnb : ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) U‖ ≤ ρb :=
    hUn.trans (min_le_right _ _)
  let OT : SmoothCcTensor g 3 4 := connectionDifferenceQuadraticCurvatureDerivativeCoefficient (I := I) (M := M) g gT
  let OU : SmoothCcTensor g 3 4 := connectionDifferenceQuadraticCurvatureDerivativeCoefficient (I := I) (M := M) g gU
  let ST : SmoothCcTensor g 5 6 :=
    slotExtendIter (I := I) (M := M) g 3 4 2 OT
  let SU : SmoothCcTensor g 5 6 :=
    slotExtendIter (I := I) (M := M) g 3 4 2 OU
  let PT : SmoothCcTensor g 3 5 := tensorThreeTwoProductCoefficient (I := I) (M := M) g T
  let PU : SmoothCcTensor g 3 5 := tensorThreeTwoProductCoefficient (I := I) (M := M) g U
  have hoD : covariantJetNormSq (I := I) (M := M) g 2 (OT - OU) ≤
      (Bd R * (1 + A) * D) ^ 2 := by
    simpa only [OT, OU, D] using
      hopd gT gU T U hT hU hTtie hUtie hδ_le hδ0 hδT hδU hδZ
        hTnd hUnd R A D2 D3 N hR hA hD2 hD3 hN
        hT2 hU2 hT3 hU3 hTU2 hTU3 hTUn
  have hoB : covariantJetNormSq (I := I) (M := M) g 2 OU ≤
      (Bb R * (1 + A)) ^ 2 := by
    simpa only [OU] using
      hopb gU U hU hUtie hδ_le hδ0 hδU hδZ
        R A hR hA hU2 hU3 hUnb
  have hsD : covariantJetNormSq (I := I) (M := M) g 2 (ST - SU) ≤
      (fr * Bd R * (1 + A) * D) ^ 2 := by
    change covariantJetNormSq (I := I) (M := M) g 2
      (slotExtendIter (I := I) (M := M) g 3 4 2 OT -
        slotExtendIter (I := I) (M := M) g 3 4 2 OU) ≤ _
    rw [← slotExtendIter_sub]
    calc
      covariantJetNormSq (I := I) (M := M) g 2
          (slotExtendIter (I := I) (M := M) g 3 4 2 (OT - OU)) ≤
        fr ^ 2 * covariantJetNormSq (I := I) (M := M) g 2 (OT - OU) := by
          simpa only [fr] using covariantJetNormSq_slotExtendIter_two_le (I := I) (M := M) g 3 4 (OT - OU)
      _ ≤ fr ^ 2 * (Bd R * (1 + A) * D) ^ 2 :=
        mul_le_mul_of_nonneg_left hoD (sq_nonneg fr)
      _ = (fr * Bd R * (1 + A) * D) ^ 2 := by ring
  have hsB : covariantJetNormSq (I := I) (M := M) g 2 SU ≤
      (fr * Bb R * (1 + A)) ^ 2 := by
    change covariantJetNormSq (I := I) (M := M) g 2
      (slotExtendIter (I := I) (M := M) g 3 4 2 OU) ≤ _
    calc
      covariantJetNormSq (I := I) (M := M) g 2
          (slotExtendIter (I := I) (M := M) g 3 4 2 OU) ≤
        fr ^ 2 * covariantJetNormSq (I := I) (M := M) g 2 OU := by
          simpa only [fr] using covariantJetNormSq_slotExtendIter_two_le (I := I) (M := M) g 3 4 OU
      _ ≤ fr ^ 2 * (Bb R * (1 + A)) ^ 2 :=
        mul_le_mul_of_nonneg_left hoB (sq_nonneg fr)
      _ = (fr * Bb R * (1 + A)) ^ 2 := by ring
  have hpT : covariantJetNormSq (I := I) (M := M) g 2 PT ≤ (Cr * R) ^ 2 := by
    change covariantJetNormSq (I := I) (M := M) g 2
      (tensorThreeTwoProductCoefficient (I := I) (M := M) g T) ≤ _
    refine (hprod T).trans ?_
    calc
      Ct * covariantJetNormSq (I := I) (M := M) g 2 T ≤ Ct * R ^ 2 :=
        mul_le_mul_of_nonneg_left hT2 hCt
      _ = (Cr * R) ^ 2 := by rw [mul_pow, hCr2]
  have hsmall : D2 ≤ D := by
    simp only [D]
    nlinarith [mul_nonneg hA hD2]
  have hpD : covariantJetNormSq (I := I) (M := M) g 2 (PT - PU) ≤
      (Cr * D) ^ 2 := by
    have h0 : covariantJetNormSq (I := I) (M := M) g 2 (PT - PU) ≤
        (Cr * D2) ^ 2 := by
      change covariantJetNormSq (I := I) (M := M) g 2
        (tensorThreeTwoProductCoefficient (I := I) (M := M) g T -
          tensorThreeTwoProductCoefficient (I := I) (M := M) g U) ≤ _
      rw [← tensorThreeTwoProductCoefficient_sub]
      refine (hprod (T - U)).trans ?_
      calc
        Ct * covariantJetNormSq (I := I) (M := M) g 2 (T - U) ≤ Ct * D2 ^ 2 :=
          mul_le_mul_of_nonneg_left hTU2 hCt
        _ = (Cr * D2) ^ 2 := by rw [mul_pow, hCr2]
    exact h0.trans (pow_le_pow_left₀ (mul_nonneg hCr hD2)
      (mul_le_mul_of_nonneg_left hsmall hCr) 2)
  have hraw := happ ST SU PT PU
    (fr * Bd R * (1 + A) * D) (fr * Bb R * (1 + A))
    (Cr * R) (Cr * D)
    (mul_nonneg (mul_nonneg (mul_nonneg hfr (hBd R hR)) honeA) hD)
    (mul_nonneg (mul_nonneg hfr (hBb R hR)) honeA)
    (mul_nonneg hCr hR) (mul_nonneg hCr hD)
    hsD hsB hpT hpD
  have h0 : covariantJetNormSq (I := I) (M := M) g 2
      (lieCorrectionQuadraticFirstDerivativeIntermediateCoefficient (I := I) (M := M) g gT T -
        lieCorrectionQuadraticFirstDerivativeIntermediateCoefficient (I := I) (M := M) g gU U) ≤
      (P * ((fr * Bd R * (1 + A) * D) * (Cr * R) +
        (fr * Bb R * (1 + A)) * (Cr * D))) ^ 2 := by
    simpa only [lieCorrectionQuadraticFirstDerivativeIntermediateCoefficient, ST, SU, PT, PU, OT, OU] using hraw
  refine h0.trans_eq ?_
  simpa only [B] using
    intermediate_coefficient_pairing_scale_sq P fr Cr (Bd R) (Bb R) R (1 + A) D

private theorem first_derivative_coefficient_pairing_scale_sq (p c m b d a q : ℝ) :
    (p * ((c * q) * (m * a) + b * (d * a * q))) ^ 2 =
      (p * (c * m + b * d) * a * q) ^ 2 := by
  ring

theorem exists_lieCorrectionQuadraticFirstDerivativeCoefficient_pairing_secondOrder_bound
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ ρ : ℝ, ∃ B : ℝ → ℝ, 0 < ρ ∧
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
        {δ : ℝ} (_hδ_le : δ ≤ 1 / 3) (_hδ0 : 0 ≤ δ)
        (_hδT : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) δ)
        (_hδU : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g U) δ)
        (_hδZ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g
            (0 : SmoothCcTensor g 0 2)) δ),
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ ≤ ρ →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) U‖ ≤ ρ →
        ∀ (R A D2 D3 N : ℝ),
        0 ≤ R → 0 ≤ A → 0 ≤ D2 → 0 ≤ D3 → 0 ≤ N →
        covariantJetNormSq (I := I) (M := M) g 2 T ≤ R ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 2 U ≤ R ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 3 T ≤ A ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 3 U ≤ A ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 2 (T - U) ≤ D2 ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 3 (T - U) ≤ D3 ^ 2 →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) (T - U)‖ ≤ N →
      covariantJetNormSq (I := I) (M := M) g 2
          (lieCorrectionQuadraticFirstDerivativeCoefficient (I := I) (M := M) g gT T -
            lieCorrectionQuadraticFirstDerivativeCoefficient (I := I) (M := M) g gU U) ≤
        (B R * (1 + A) * (D3 + D2 + A * D2 + N)) ^ 2 := by
  obtain ⟨ρmd, Bmd, hρmd, hBmd, hmidd⟩ :=
    exists_lieCorrectionQuadraticFirstDerivativeIntermediateCoefficient_pairing_secondOrder_bound (I := I) (M := M) hDim g
  obtain ⟨ρmb, Bmb, hρmb, hBmb, hmidb⟩ :=
    exists_lieCorrectionQuadraticFirstDerivativeIntermediateCoefficient_covariantJetNormSq_two_bound (I := I) (M := M) hDim g
  obtain ⟨ρpp, Cp, hρpp, hCp, hpairp⟩ :=
    RicciDeTurckLowOrder.pairTrace_pair_h2 (I := I) (M := M) hDim g
  obtain ⟨ρpb, Bp, hρpb, hBp, hbddp⟩ :=
    RicciDeTurckLowOrder.pair_trace_sobolev_two_bound (I := I) (M := M) hDim g
  obtain ⟨P, hP, happ⟩ :=
    exists_operatorFieldComposition_difference_covariantJetNormSq_two_bound (I := I) (M := M) hDim g 3 6 2
  let ρ : ℝ := min (min ρmd ρmb) (min ρpp ρpb)
  let B : ℝ → ℝ := fun R =>
    P * (Cp * Bmb R + Bp * Bmd R)
  have hB : ∀ R : ℝ, 0 ≤ R → 0 ≤ B R := fun R hR =>
    mul_nonneg hP
      (add_nonneg (mul_nonneg hCp (hBmb R hR))
        (mul_nonneg hBp (hBmd R hR)))
  have hρ : 0 < ρ := lt_min (lt_min hρmd hρmb) (lt_min hρpp hρpb)
  refine ⟨ρ, B, hρ, hB, ?_⟩
  intro gT gU T U hT hU hTtie hUtie δ hδ_le hδ0 hδT hδU hδZ
    hTn hUn R A D2 D3 N hR hA hD2 hD3 hN
    hT2 hU2 hT3 hU3 hTU2 hTU3 hTUn
  let D : ℝ := D3 + D2 + A * D2 + N
  have hD : 0 ≤ D :=
    add_nonneg (add_nonneg (add_nonneg hD3 hD2) (mul_nonneg hA hD2)) hN
  have honeA : 0 ≤ 1 + A := add_nonneg (by norm_num) hA
  have hND : N ≤ D := by
    simp only [D]
    nlinarith [mul_nonneg hA hD2]
  have hTnmd : ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ ≤ ρmd :=
    hTn.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hUnmd : ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) U‖ ≤ ρmd :=
    hUn.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hTnmb : ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ ≤ ρmb :=
    hTn.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hTnpp : ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ ≤ ρpp :=
    hTn.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hUnpp : ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) U‖ ≤ ρpp :=
    hUn.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hUnpb : ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) U‖ ≤ ρpb :=
    hUn.trans ((min_le_right _ _).trans (min_le_right _ _))
  let MT : SmoothCcTensor g 3 6 := lieCorrectionQuadraticFirstDerivativeIntermediateCoefficient (I := I) (M := M) g gT T
  let MU : SmoothCcTensor g 3 6 := lieCorrectionQuadraticFirstDerivativeIntermediateCoefficient (I := I) (M := M) g gU U
  let ST : SmoothCcTensor g 3 6 :=
    ccOperatorFieldComp (I := I) (M := M) g 3 6 6
      (permCoeff (I := I) (M := M) g deTurckLieCovariantDerivativePairTracePermutation) MT
  let SU : SmoothCcTensor g 3 6 :=
    ccOperatorFieldComp (I := I) (M := M) g 3 6 6
      (permCoeff (I := I) (M := M) g deTurckLieCovariantDerivativePairTracePermutation) MU
  let PT : SmoothCcTensor g 6 2 := cometricDoublePairTraceCoefficient (I := I) (M := M) g gT
  let PU : SmoothCcTensor g 6 2 := cometricDoublePairTraceCoefficient (I := I) (M := M) g gU
  have hmD : covariantJetNormSq (I := I) (M := M) g 2 (MT - MU) ≤
      (Bmd R * (1 + A) * D) ^ 2 := by
    simpa only [MT, MU, D] using
      hmidd gT gU T U hT hU hTtie hUtie hδ_le hδ0 hδT hδU hδZ
        hTnmd hUnmd R A D2 D3 N hR hA hD2 hD3 hN
        hT2 hU2 hT3 hU3 hTU2 hTU3 hTUn
  have hmT : covariantJetNormSq (I := I) (M := M) g 2 MT ≤
      (Bmb R * (1 + A)) ^ 2 := by
    simpa only [MT] using
      hmidb gT T T hT hTtie hδ_le hδ0 hδT hδZ
        R A hR hA hT2 hT3 hT2 hTnmb
  have hsD : covariantJetNormSq (I := I) (M := M) g 2 (ST - SU) ≤
      (Bmd R * (1 + A) * D) ^ 2 := by
    change covariantJetNormSq (I := I) (M := M) g 2
      (ccOperatorFieldComp (I := I) (M := M) g 3 6 6
          (permCoeff (I := I) (M := M) g deTurckLieCovariantDerivativePairTracePermutation) MT -
        ccOperatorFieldComp (I := I) (M := M) g 3 6 6
          (permCoeff (I := I) (M := M) g deTurckLieCovariantDerivativePairTracePermutation) MU) ≤ _
    rw [← operatorFieldComposition_sub_right]
    have hp := operatorFieldComposition_permutationCoefficient_apply_eq_rsDomDomCongrSection (I := I) (M := M) g deTurckLieCovariantDerivativePairTracePermutation (MT - MU)
    rw [hp, covariantJetNormSq_rsDomDomCongrSection (I := I) (M := M) g]
    exact hmD
  have hsT : covariantJetNormSq (I := I) (M := M) g 2 ST ≤
      (Bmb R * (1 + A)) ^ 2 := by
    change covariantJetNormSq (I := I) (M := M) g 2
      (ccOperatorFieldComp (I := I) (M := M) g 3 6 6
        (permCoeff (I := I) (M := M) g deTurckLieCovariantDerivativePairTracePermutation) MT) ≤ _
    rw [operatorFieldComposition_permutationCoefficient_apply_eq_rsDomDomCongrSection (I := I) (M := M) g,
      covariantJetNormSq_rsDomDomCongrSection (I := I) (M := M) g]
    exact hmT
  have hp0 := hpairp T U gT gU hTtie hUtie hTnpp hUnpp
  have hpD : covariantJetNormSq (I := I) (M := M) g 2 (PT - PU) ≤
      (Cp * D) ^ 2 := by
    have h0 : covariantJetNormSq (I := I) (M := M) g 2 (PT - PU) ≤
        (Cp * ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) (T - U)‖) ^ 2 := by
      simpa only [PT, PU] using hp0
    have hnormD : ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) (T - U)‖ ≤ D :=
      hTUn.trans hND
    exact h0.trans (pow_le_pow_left₀
      (mul_nonneg hCp (norm_nonneg _))
      (mul_le_mul_of_nonneg_left hnormD hCp) 2)
  have hpU : covariantJetNormSq (I := I) (M := M) g 2 PU ≤ Bp ^ 2 := by
    simpa only [PU] using hbddp U gU hUtie hUnpb
  have hraw := happ PT PU ST SU
    (Cp * D) Bp (Bmb R * (1 + A)) (Bmd R * (1 + A) * D)
    (mul_nonneg hCp hD) hBp (mul_nonneg (hBmb R hR) honeA)
    (mul_nonneg (mul_nonneg (hBmd R hR) honeA) hD)
    hpD hpU hsT hsD
  have h0 : covariantJetNormSq (I := I) (M := M) g 2
      (lieCorrectionQuadraticFirstDerivativeCoefficient (I := I) (M := M) g gT T -
        lieCorrectionQuadraticFirstDerivativeCoefficient (I := I) (M := M) g gU U) ≤
      (P * ((Cp * D) * (Bmb R * (1 + A)) +
        Bp * (Bmd R * (1 + A) * D))) ^ 2 := by
    simpa only [lieCorrectionQuadraticFirstDerivativeCoefficient, PT, PU, ST, SU, MT, MU] using hraw
  refine h0.trans_eq ?_
  simpa only [B] using
    first_derivative_coefficient_pairing_scale_sq P Cp (Bmb R) Bp (Bmd R) (1 + A) D

theorem exists_lowOrderFirstDerivativeCoefficientPath_covariantJetNormSq_two_bound
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ ρ : ℝ, ∃ B : ℝ → ℝ, 0 < ρ ∧
      (∀ R : ℝ, 0 ≤ R → 0 ≤ B R) ∧
      ∀ (T : SmoothCcTensor g 0 2)
        (_hT : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g T x u v =
            ccTensorBilin (I := I) g T x v u)
        {δ : ℝ} (_hδ_le : δ ≤ 1 / 3) (_hδ0 : 0 ≤ δ)
        (hδT : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) δ)
        (hδZ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g
            (0 : SmoothCcTensor g 0 2)) δ)
        (R A : ℝ), 0 ≤ R → 0 ≤ A →
        covariantJetNormSq (I := I) (M := M) g 2 T ≤ R ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 3 T ≤ A ^ 2 →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ ≤ ρ →
        ∀ {s : ℝ}, s ∈ Set.Icc (0 : ℝ) 1 →
      covariantJetNormSq (I := I) (M := M) g 2
          (lowOrderFirstDerivativeCoefficientPath (I := I) (M := M) g T hδT hδZ s) ≤
        (B R * (1 + A)) ^ 2 := by
  obtain ⟨ρr, Br, hρr, hBr, hric⟩ :=
    exists_ricciConnectionDifferenceDerivativeCoefficient_covariantJetNormSq_two_bound (I := I) (M := M) hDim g
  obtain ⟨ρv, Bv, hρv, hBv, hvb⟩ :=
    exists_lieCorrectionZeroVectorBundleDerivativeCoefficient_secondOrder_bound (I := I) (M := M) hDim g
  obtain ⟨ρa, Ba, hρa, hBa, hamix⟩ :=
    exists_lieCorrectionZeroMixedConnectionDerivativeCoefficient_covariantJetNormSq_two_bound (I := I) (M := M) hDim g
  let ρ : ℝ := min ρr (min ρv ρa)
  let L : ℝ → ℝ := fun R =>
    2 * (2 * (4 * Br R ^ 2 + Bv R ^ 2) + Ba R ^ 2)
  let B : ℝ → ℝ := fun R => Real.sqrt (L R)
  have hρ : 0 < ρ := lt_min hρr (lt_min hρv hρa)
  have hL : ∀ R : ℝ, 0 ≤ R → 0 ≤ L R := by
    intro R hR
    exact mul_nonneg (by norm_num)
      (add_nonneg
        (mul_nonneg (by norm_num)
          (add_nonneg (mul_nonneg (by norm_num) (sq_nonneg (Br R)))
            (sq_nonneg (Bv R))))
        (sq_nonneg (Ba R)))
  refine ⟨ρ, B, hρ, fun R hR => Real.sqrt_nonneg _, ?_⟩
  intro T hT δ hδ_le hδ0 hδT hδZ R A hR hA hT2 hT3 hTn s hs
  have hδ_lt : δ < 1 := lt_of_le_of_lt hδ_le (by norm_num)
  set gm : SmoothRiemannianMetric I M :=
    metricPerturbationPath (I := I) g T 0 hδT hδZ s with hgm
  set P : SmoothCcTensor g 0 2 := s • T with hcP
  have hs_mem : s ∈ metricPerturbationPathDomain (δ := δ) (δ' := δ) :=
    Icc_subset_metricPerturbationPathDomain hδ_lt hδ_lt hs
  have hs2 : s ^ 2 ≤ (1 : ℝ) := by nlinarith [hs.1, hs.2]
  have hsabs : ‖s‖ ≤ (1 : ℝ) := by
    rw [Real.norm_eq_abs, abs_of_nonneg hs.1]
    exact hs.2
  have hPsymm : ∀ (x : M) (u v : TangentSpace I x),
      ccTensorBilin (I := I) g P x u v =
        ccTensorBilin (I := I) g P x v u := by
    intro x u v
    simp only [hcP, ccTensorBilin_apply, ccTensorModel_smul,
      smul_apply, smul_eq_mul]
    apply congrArg (fun z : ℝ => s * z)
    simpa only [ccTensorBilin_apply] using hT x u v
  have hPtie : ∀ (x : M) (u v : TangentSpace I x),
      gm.inner x u v =
        g.inner x u v + ccTensorBilinSymm (I := I) g P x u v := by
    intro x u v
    simpa only [hgm, hcP, convexPerturbation, smul_zero, zero_add] using
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
    simpa only [hcP, convexPerturbation, smul_zero, zero_add, heq] using hraw
  have hP2 : covariantJetNormSq (I := I) (M := M) g 2 P ≤ R ^ 2 := by
    rw [hcP, covariantJetNormSq_smul]
    exact (mul_le_of_le_one_left
      (covariantJetNormSq_nonneg (I := I) (M := M) (m := 2) g T) hs2).trans hT2
  have hP3 : covariantJetNormSq (I := I) (M := M) g 3 P ≤ A ^ 2 := by
    rw [hcP, covariantJetNormSq_smul]
    exact (mul_le_of_le_one_left
      (covariantJetNormSq_nonneg (I := I) (M := M) (m := 3) g T) hs2).trans hT3
  have hPn : ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) P‖ ≤ ρ := by
    rw [hcP, ccTensorToHs_smul, norm_smul]
    exact (mul_le_mul_of_nonneg_right hsabs (norm_nonneg _)).trans
      (by simpa only [one_mul] using hTn)
  have hPnr : ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) P‖ ≤ ρr :=
    hPn.trans (min_le_left _ _)
  have hPnv : ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) P‖ ≤ ρv :=
    hPn.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hPna : ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) P‖ ≤ ρa :=
    hPn.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hr := hric gm P T hPsymm hT hPtie hδ_le hδ0 hδP hδZ
    R A hR hA hP2 hP3 hT2 hPnr
  have hv := hvb gm P T hPsymm hPtie hδ_le hδ0 hδP
    R A hR hA hP2 hP3 hT2 hPnv
  have ha := hamix gm P T hPsymm hPtie hδ_le hδ0 hδP
    R A hR hA hP2 hP3 hT2 hPna
  have hrs : covariantJetNormSq (I := I) (M := M) g 2
      ((-2 * s : ℝ) • ricciConnectionDifferenceDerivativeCoefficient (I := I) (M := M) g gm T) ≤
      4 * (Br R * (1 + A)) ^ 2 := by
    rw [covariantJetNormSq_smul]
    calc
      (-2 * s) ^ 2 * covariantJetNormSq (I := I) (M := M) g 2
          (ricciConnectionDifferenceDerivativeCoefficient (I := I) (M := M) g gm T) =
        4 * s ^ 2 * covariantJetNormSq (I := I) (M := M) g 2
          (ricciConnectionDifferenceDerivativeCoefficient (I := I) (M := M) g gm T) := by ring
      _ ≤ 4 * 1 * covariantJetNormSq (I := I) (M := M) g 2
          (ricciConnectionDifferenceDerivativeCoefficient (I := I) (M := M) g gm T) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hs2 (by norm_num))
          (covariantJetNormSq_nonneg (I := I) (M := M) (m := 2) g _)
      _ ≤ 4 * 1 * (Br R * (1 + A)) ^ 2 :=
        mul_le_mul_of_nonneg_left hr (by norm_num)
      _ = 4 * (Br R * (1 + A)) ^ 2 := by ring
  have hvs : covariantJetNormSq (I := I) (M := M) g 2
      (s • lieCorrectionZeroVectorBundleDerivativeCoefficient (I := I) (M := M) g gm T) ≤
      (Bv R * (1 + A)) ^ 2 := by
    rw [covariantJetNormSq_smul]
    exact (mul_le_of_le_one_left
      (covariantJetNormSq_nonneg (I := I) (M := M) (m := 2) g _) hs2).trans hv
  have has : covariantJetNormSq (I := I) (M := M) g 2
      (s • lieCorrectionZeroMixedConnectionDerivativeCoefficient (I := I) (M := M) g gm g T) ≤
      (Ba R * (1 + A)) ^ 2 := by
    rw [covariantJetNormSq_smul]
    exact (mul_le_of_le_one_left
      (covariantJetNormSq_nonneg (I := I) (M := M) (m := 2) g _) hs2).trans ha
  rw [lowOrderFirstDerivativeCoefficientPath]
  rw [← hgm]
  set X := (-2 * s : ℝ) •
    ricciConnectionDifferenceDerivativeCoefficient (I := I) (M := M) g gm T with hX
  set Y := s •
    lieCorrectionZeroVectorBundleDerivativeCoefficient (I := I) (M := M) g gm T with hY
  set Z := s •
    lieCorrectionZeroMixedConnectionDerivativeCoefficient (I := I) (M := M) g gm g T with hZ
  have hvs' : covariantJetNormSq (I := I) (M := M) g 2 Y ≤
      (Bv R * (1 + A)) ^ 2 := by simpa only [Y] using hvs
  have has' : covariantJetNormSq (I := I) (M := M) g 2 Z ≤
      (Ba R * (1 + A)) ^ 2 := by simpa only [Z] using has
  have hrv := covariantJetNormSq_add_le (I := I) (M := M) g 2
    X Y
  refine (covariantJetNormSq_add_le (I := I) (M := M) g 2 _ _).trans ?_
  calc
    2 * (covariantJetNormSq (I := I) (M := M) g 2
          (X + Y) + covariantJetNormSq (I := I) (M := M) g 2 Z) ≤
      2 * (2 * (covariantJetNormSq (I := I) (M := M) g 2
            X + covariantJetNormSq (I := I) (M := M) g 2 Y) +
        covariantJetNormSq (I := I) (M := M) g 2 Z) :=
        mul_le_mul_of_nonneg_left (add_le_add hrv le_rfl) (by norm_num)
    _ ≤ 2 * (2 * (4 * (Br R * (1 + A)) ^ 2 +
          (Bv R * (1 + A)) ^ 2) +
        (Ba R * (1 + A)) ^ 2) :=
      mul_le_mul_of_nonneg_left
        (add_le_add
          (mul_le_mul_of_nonneg_left (add_le_add hrs hvs') (by norm_num))
          has') (by norm_num)
    _ = L R * (1 + A) ^ 2 := by simp only [L]; ring
    _ = (B R * (1 + A)) ^ 2 := by
      have hBR : B R ^ 2 = L R := by
        simpa only [B] using Real.sq_sqrt (hL R hR)
      simpa only [mul_pow] using
        congrArg (fun x : ℝ => x * (1 + A) ^ 2) hBR.symm

theorem exists_affineLowOrderFirstDerivativeCoefficientPath_covariantJetNormSq_two_bound
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ ρ : ℝ, ∃ B : ℝ → ℝ, 0 < ρ ∧
      (∀ R : ℝ, 0 ≤ R → 0 ≤ B R) ∧
      ∀ (T : SmoothCcTensor g 0 2)
        (_hT : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g T x u v =
            ccTensorBilin (I := I) g T x v u)
        {δ : ℝ} (_hδ_le : δ ≤ 1 / 3) (_hδ0 : 0 ≤ δ)
        (hδT : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) δ)
        (hδZ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g
            (0 : SmoothCcTensor g 0 2)) δ)
        (R A : ℝ), 0 ≤ R → 0 ≤ A →
        covariantJetNormSq (I := I) (M := M) g 2 T ≤ R ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 3 T ≤ A ^ 2 →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ ≤ ρ →
        ∀ {s : ℝ}, s ∈ Set.Icc (0 : ℝ) 1 →
      covariantJetNormSq (I := I) (M := M) g 2
          (affineLowOrderFirstDerivativeCoefficientPath (I := I) (M := M) g T hδT hδZ s) ≤
        (B R * (1 + A)) ^ 2 := by
  obtain ⟨ρl, Bl, hρl, hBl, hlow⟩ :=
    exists_lowOrderFirstDerivativeCoefficientPath_covariantJetNormSq_two_bound (I := I) (M := M) hDim g
  obtain ⟨ρq, Bq, hρq, hBq, hquad⟩ :=
    exists_lieCorrectionQuadraticFirstDerivativeCoefficient_covariantJetNormSq_two_bound (I := I) (M := M) hDim g
  let ρ : ℝ := min ρl ρq
  let L : ℝ → ℝ := fun R => 2 * (Bl R ^ 2 + Bq R ^ 2)
  let B : ℝ → ℝ := fun R => Real.sqrt (L R)
  have hρ : 0 < ρ := lt_min hρl hρq
  have hL : ∀ R : ℝ, 0 ≤ R → 0 ≤ L R := by
    intro R hR
    exact mul_nonneg (by norm_num)
      (add_nonneg (sq_nonneg (Bl R)) (sq_nonneg (Bq R)))
  refine ⟨ρ, B, hρ, fun R hR => Real.sqrt_nonneg _, ?_⟩
  intro T hT δ hδ_le hδ0 hδT hδZ R A hR hA hT2 hT3 hTn s hs
  have hl := hlow T hT hδ_le hδ0 hδT hδZ R A hR hA hT2 hT3
    (hTn.trans (min_le_left _ _)) hs
  have hδ_lt : δ < 1 := lt_of_le_of_lt hδ_le (by norm_num)
  set gm : SmoothRiemannianMetric I M :=
    metricPerturbationPath (I := I) g T 0 hδT hδZ s with hgm
  set P : SmoothCcTensor g 0 2 := s • T with hcP
  have hs_mem : s ∈ metricPerturbationPathDomain (δ := δ) (δ' := δ) :=
    Icc_subset_metricPerturbationPathDomain hδ_lt hδ_lt hs
  have hs2 : s ^ 2 ≤ (1 : ℝ) := by nlinarith [hs.1, hs.2]
  have hsabs : ‖s‖ ≤ (1 : ℝ) := by
    rw [Real.norm_eq_abs, abs_of_nonneg hs.1]
    exact hs.2
  have hPsymm : ∀ (x : M) (u v : TangentSpace I x),
      ccTensorBilin (I := I) g P x u v =
        ccTensorBilin (I := I) g P x v u := by
    intro x u v
    simp only [hcP, ccTensorBilin_apply, ccTensorModel_smul,
      smul_apply, smul_eq_mul]
    apply congrArg (fun z : ℝ => s * z)
    simpa only [ccTensorBilin_apply] using hT x u v
  have hPtie : ∀ (x : M) (u v : TangentSpace I x),
      gm.inner x u v =
        g.inner x u v + ccTensorBilinSymm (I := I) g P x u v := by
    intro x u v
    simpa only [hgm, hcP, convexPerturbation, smul_zero, zero_add] using
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
    simpa only [hcP, convexPerturbation, smul_zero, zero_add, heq] using hraw
  have hP2 : covariantJetNormSq (I := I) (M := M) g 2 P ≤ R ^ 2 := by
    rw [hcP, covariantJetNormSq_smul]
    exact (mul_le_of_le_one_left
      (covariantJetNormSq_nonneg (I := I) (M := M) (m := 2) g T) hs2).trans hT2
  have hP3 : covariantJetNormSq (I := I) (M := M) g 3 P ≤ A ^ 2 := by
    rw [hcP, covariantJetNormSq_smul]
    exact (mul_le_of_le_one_left
      (covariantJetNormSq_nonneg (I := I) (M := M) (m := 3) g T) hs2).trans hT3
  have hPn : ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) P‖ ≤ ρq := by
    rw [hcP, ccTensorToHs_smul, norm_smul]
    exact (mul_le_mul_of_nonneg_right hsabs (norm_nonneg _)).trans
      (by simpa only [one_mul] using hTn.trans (min_le_right _ _))
  have hq := hquad gm P T hPsymm hPtie hδ_le hδ0 hδP hδZ
    R A hR hA hP2 hP3 hT2 hPn
  have hqs : covariantJetNormSq (I := I) (M := M) g 2
      (s • lieCorrectionQuadraticFirstDerivativeCoefficient (I := I) (M := M) g gm T) ≤
      (Bq R * (1 + A)) ^ 2 := by
    rw [covariantJetNormSq_smul]
    exact (mul_le_of_le_one_left
      (covariantJetNormSq_nonneg (I := I) (M := M) (m := 2) g _) hs2).trans hq
  rw [affineLowOrderFirstDerivativeCoefficientPath]
  rw [← hgm]
  set X := lowOrderFirstDerivativeCoefficientPath (I := I) (M := M) g T hδT hδZ s with hX
  set Y := s •
    lieCorrectionQuadraticFirstDerivativeCoefficient (I := I) (M := M) g gm T with hY
  have hqs' : covariantJetNormSq (I := I) (M := M) g 2 Y ≤
      (Bq R * (1 + A)) ^ 2 := by simpa only [Y] using hqs
  refine (covariantJetNormSq_add_le (I := I) (M := M) g 2 _ _).trans ?_
  calc
    2 * (covariantJetNormSq (I := I) (M := M) g 2 X +
        covariantJetNormSq (I := I) (M := M) g 2 Y) ≤
      2 * ((Bl R * (1 + A)) ^ 2 + (Bq R * (1 + A)) ^ 2) :=
        mul_le_mul_of_nonneg_left (add_le_add hl hqs') (by norm_num)
    _ = L R * (1 + A) ^ 2 := by simp only [L]; ring
    _ = (B R * (1 + A)) ^ 2 := by
      have hBR : B R ^ 2 = L R := by
        simpa only [B] using Real.sq_sqrt (hL R hR)
      simpa only [mul_pow] using
        congrArg (fun x : ℝ => x * (1 + A) ^ 2) hBR.symm

end RicciDeTurckPairing
end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral
end

section

noncomputable section


open Bundle Manifold MeasureTheory Set Filter DifferentialGeometry.Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Sobolev (covariantJetNormSq
  covariantJetNormSq_add_le covariantJetNormSq_nonneg
  exists_covariantJetNormSq_two_operatorFieldComposition_le)
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Analysis.Sobolev.TensorHilbert
open DifferentialGeometry.Analysis.Spectral
  (ccOperatorFieldComp operatorFieldComposition_sub_left operatorFieldComposition_sub_right ccTensorToHs permCoeff
    symmS_eq_self_of_ccTensorBilin_symm)
open DifferentialGeometry.Geometry.Connection (slotInsertEndoCc)
open DifferentialGeometry.PDE.DeTurck.RicciLinearization
open DifferentialGeometry.Analysis.Spectral.DeTurck
open DifferentialGeometry.Analysis.Spectral.MetricRealization

variable
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
      [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

namespace RicciDeTurckPairing

noncomputable def lowOrderFirstDerivativePathIntegral
    (g : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) δ)
    (hδZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g
        (0 : SmoothCcTensor g 0 2)) δ) :
    SmoothCcTensor g 3 2 :=
  pathIntegralCoeffField (I := I) (M := M) g 3 2
    (affineLowOrderFirstDerivativeCoefficientPath (I := I) (M := M) g T hδ hδZ)
    (metricPerturbationPathDomain (δ := δ) (δ' := δ))
    metricPerturbationPathDomain_isOpen
    (by
      rw [Set.uIcc_of_le zero_le_one]
      exact Icc_subset_metricPerturbationPathDomain hδ_lt hδ_lt)
    (affineLowOrderFirstDerivativeCoefficientPath_jointlySmooth (I := I) (M := M) g T hδ hδZ)

noncomputable def lowOrderFirstDerivativePathIntegralDifference
    (g : SmoothRiemannianMetric I M) (T U : SmoothCcTensor g 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδT : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) δ)
    (hδU : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g U) δ)
    (hδZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g
        (0 : SmoothCcTensor g 0 2)) δ) :
    SmoothCcTensor g 3 2 :=
  pathIntegralCoeffField (I := I) (M := M) g 3 2
    (fun s =>
      affineLowOrderFirstDerivativeCoefficientPath (I := I) (M := M) g T hδT hδZ s -
        affineLowOrderFirstDerivativeCoefficientPath (I := I) (M := M) g U hδU hδZ s)
    (metricPerturbationPathDomain (δ := δ) (δ' := δ))
    metricPerturbationPathDomain_isOpen
    (by
      rw [Set.uIcc_of_le zero_le_one]
      exact Icc_subset_metricPerturbationPathDomain hδ_lt hδ_lt)
    (jointlySmoothCcTensorFamily_sub (I := I) (M := M) g
      (affineLowOrderFirstDerivativeCoefficientPath_jointlySmooth (I := I) (M := M) g T hδT hδZ)
      (affineLowOrderFirstDerivativeCoefficientPath_jointlySmooth (I := I) (M := M) g U hδU hδZ))

omit [SigmaCompactSpace M] in
theorem lowOrderFirstDerivativePathIntegral_sub
    (g : SmoothRiemannianMetric I M) (T U : SmoothCcTensor g 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδT : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) δ)
    (hδU : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g U) δ)
    (hδZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g
        (0 : SmoothCcTensor g 0 2)) δ) :
    lowOrderFirstDerivativePathIntegral (I := I) (M := M) g T hδ_lt hδT hδZ -
        lowOrderFirstDerivativePathIntegral (I := I) (M := M) g U hδ_lt hδU hδZ =
      lowOrderFirstDerivativePathIntegralDifference (I := I) (M := M)
        g T U hδ_lt hδT hδU hδZ := by
  classical
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  apply TensorRSSpace.toModel_injective
  have hSI : Set.uIcc (0 : ℝ) 1 ⊆
      metricPerturbationPathDomain (δ := δ) (δ' := δ) := by
    rw [Set.uIcc_of_le zero_le_one]
    exact Icc_subset_metricPerturbationPathDomain hδ_lt hδ_lt
  have hTcont :=
    jointContMDiff_toModel_continuous_slice
      (I := I) g 3 2
      (affineLowOrderFirstDerivativeCoefficientPath (I := I) (M := M) g T hδT hδZ)
      (metricPerturbationPathDomain (δ := δ) (δ' := δ))
      (affineLowOrderFirstDerivativeCoefficientPath_jointlySmooth (I := I) (M := M) g T hδT hδZ) x
  have hUcont :=
    jointContMDiff_toModel_continuous_slice
      (I := I) g 3 2
      (affineLowOrderFirstDerivativeCoefficientPath (I := I) (M := M) g U hδU hδZ)
      (metricPerturbationPathDomain (δ := δ) (δ' := δ))
      (affineLowOrderFirstDerivativeCoefficientPath_jointlySmooth (I := I) (M := M) g U hδU hδZ) x
  have hTint : IntervalIntegrable
      (fun s : ℝ => TensorRSSpace.toModel
        ((affineLowOrderFirstDerivativeCoefficientPath (I := I) (M := M) g T hδT hδZ s).toSection x))
      MeasureTheory.volume 0 1 :=
    (hTcont.mono hSI).intervalIntegrable
  have hUint : IntervalIntegrable
      (fun s : ℝ => TensorRSSpace.toModel
        ((affineLowOrderFirstDerivativeCoefficientPath (I := I) (M := M) g U hδU hδZ s).toSection x))
      MeasureTheory.volume 0 1 :=
    (hUcont.mono hSI).intervalIntegrable
  simp only [lowOrderFirstDerivativePathIntegral, lowOrderFirstDerivativePathIntegralDifference, pathIntegralCoeffField_toModel,
    SmoothCcTensor.toSection_sub, ContMDiffSection.coe_sub, Pi.sub_apply,
    TensorRSSpace.toModel_sub]
  rw [intervalIntegral.integral_sub hTint hUint]

theorem exists_connectionDifferenceInsertionInnerDerivativeCoefficient_pairing_secondOrder_bound
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (T U : SmoothCcTensor g 0 2)
        (_hT : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g T x u v =
            ccTensorBilin (I := I) g T x v u)
        (_hU : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g U x u v =
            ccTensorBilin (I := I) g U x v u)
        (D2 : ℝ), 0 ≤ D2 →
        covariantJetNormSq (I := I) (M := M) g 2 (T - U) ≤ D2 ^ 2 →
      covariantJetNormSq (I := I) (M := M) g 2
          (connectionDifferenceInsertionInnerDerivativeCoefficient (I := I) (M := M) g T -
            connectionDifferenceInsertionInnerDerivativeCoefficient (I := I) (M := M) g U) ≤
        (C * D2) ^ 2 := by
  obtain ⟨K, hK, happ⟩ := exists_covariantJetNormSq_two_operatorFieldComposition_le (I := I) (M := M) hDim g 3 3 3
  let P : SmoothCcTensor g 3 3 :=
    permCoeff (I := I) (M := M) g (finRotate 3)
  let J : ℝ := covariantJetNormSq (I := I) (M := M) g 2 P
  let fr : ℝ := Module.finrank ℝ E
  let L : ℝ := K * fr ^ 2 * J
  let C : ℝ := Real.sqrt L
  have hJ : 0 ≤ J := covariantJetNormSq_nonneg (I := I) (M := M) (m := 2) g P
  have hfr : 0 ≤ fr := Nat.cast_nonneg _
  have hL : 0 ≤ L := by
    dsimp only [L]
    positivity
  have hC : 0 ≤ C := Real.sqrt_nonneg _
  have hCsq : C ^ 2 = L := by
    simpa only [C] using Real.sq_sqrt hL
  refine ⟨C, hC, ?_⟩
  intro T U hT hU D2 hD2 hTU2
  let D : SmoothCcTensor g 0 2 := T - U
  have hDsymm : ∀ (x : M) (u v : TangentSpace I x),
      ccTensorBilin (I := I) g D x u v =
        ccTensorBilin (I := I) g D x v u := by
    intro x u v
    simpa only [D, ccTensorBilin_apply, ccTensorModel_sub, sub_apply] using
        congrArg₂ (fun a b : ℝ => a - b) (hT x u v) (hU x u v)
  have hDself : symmS (I := I) (M := M) g D = D :=
    symmS_eq_self_of_ccTensorBilin_symm
      (I := I) (M := M) g D hDsymm
  have hraise :
      symmRaiseEndo (I := I) (M := M) g T -
          symmRaiseEndo (I := I) (M := M) g U =
        symmRaiseEndo (I := I) (M := M) g D := by
    have hneg : symmRaiseEndo (I := I) (M := M) g (-U) =
        -symmRaiseEndo (I := I) (M := M) g U := by
      rw [show -U = (-1 : ℝ) • U by simp, symmRaiseEndo_smul]
      exact neg_one_smul ℝ
        (symmRaiseEndo (I := I) (M := M) g U)
    calc
      symmRaiseEndo (I := I) (M := M) g T -
          symmRaiseEndo (I := I) (M := M) g U =
        symmRaiseEndo (I := I) (M := M) g T +
          -symmRaiseEndo (I := I) (M := M) g U := sub_eq_add_neg _ _
      _ = symmRaiseEndo (I := I) (M := M) g T +
          symmRaiseEndo (I := I) (M := M) g (-U) := by rw [hneg]
      _ = symmRaiseEndo (I := I) (M := M) g (T + -U) :=
        (symmRaiseEndo_add (I := I) (M := M) g T (-U)).symm
      _ = symmRaiseEndo (I := I) (M := M) g D := by rfl
  have hins : covariantJetNormSq (I := I) (M := M) g 2
      (slotInsertEndoCc (I := I) (M := M) g 2
        (symmRaiseEndo (I := I) (M := M) g D)) ≤
        fr ^ 2 * D2 ^ 2 := by
    refine (covariantJetNormSq_slotInsertEndoCc_symmRaiseEndo_le (I := I) (M := M) g 2 2 D hDself).trans ?_
    exact mul_le_mul_of_nonneg_left
      (by simpa only [D] using hTU2) (pow_nonneg hfr 2)
  have hform :
      connectionDifferenceInsertionInnerDerivativeCoefficient (I := I) (M := M) g T -
          connectionDifferenceInsertionInnerDerivativeCoefficient (I := I) (M := M) g U =
        ccOperatorFieldComp (I := I) (M := M) g 3 3 3
          (slotInsertEndoCc (I := I) (M := M) g 2
            (symmRaiseEndo (I := I) (M := M) g D)) P := by
    rw [connectionDifferenceInsertionInnerDerivativeCoefficient, connectionDifferenceInsertionInnerDerivativeCoefficient, ← operatorFieldComposition_sub_left,
      ← slotInsertEndoCc_sub, hraise]
  rw [hform]
  refine (happ _ _).trans ?_
  calc
    K * covariantJetNormSq (I := I) (M := M) g 2
          (slotInsertEndoCc (I := I) (M := M) g 2
            (symmRaiseEndo (I := I) (M := M) g D)) * J ≤
        K * (fr ^ 2 * D2 ^ 2) * J :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hins hK) hJ
    _ = L * D2 ^ 2 := by simp only [L]; ring
    _ = (C * D2) ^ 2 := by rw [mul_pow, hCsq]

theorem exists_connectionDifferenceInsertionInnerDerivativeCoefficient_secondOrder_bound
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (W : SmoothCcTensor g 0 2)
        (_hW : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g W x u v =
            ccTensorBilin (I := I) g W x v u)
        (R : ℝ), 0 ≤ R →
        covariantJetNormSq (I := I) (M := M) g 2 W ≤ R ^ 2 →
      covariantJetNormSq (I := I) (M := M) g 2
          (connectionDifferenceInsertionInnerDerivativeCoefficient (I := I) (M := M) g W) ≤
        (C * R) ^ 2 := by
  obtain ⟨K, hK, happ⟩ := exists_covariantJetNormSq_two_operatorFieldComposition_le (I := I) (M := M) hDim g 3 3 3
  let P : SmoothCcTensor g 3 3 :=
    permCoeff (I := I) (M := M) g (finRotate 3)
  let J : ℝ := covariantJetNormSq (I := I) (M := M) g 2 P
  let fr : ℝ := Module.finrank ℝ E
  let L : ℝ := K * fr ^ 2 * J
  let C : ℝ := Real.sqrt L
  have hJ : 0 ≤ J := covariantJetNormSq_nonneg (I := I) (M := M) (m := 2) g P
  have hfr : 0 ≤ fr := Nat.cast_nonneg _
  have hL : 0 ≤ L := by
    dsimp only [L]
    positivity
  have hC : 0 ≤ C := Real.sqrt_nonneg _
  have hCsq : C ^ 2 = L := by
    simpa only [C] using Real.sq_sqrt hL
  refine ⟨C, hC, ?_⟩
  intro W hW R hR hW2
  have hWself : symmS (I := I) (M := M) g W = W :=
    symmS_eq_self_of_ccTensorBilin_symm
      (I := I) (M := M) g W hW
  have hins : covariantJetNormSq (I := I) (M := M) g 2
      (slotInsertEndoCc (I := I) (M := M) g 2
        (symmRaiseEndo (I := I) (M := M) g W)) ≤
        fr ^ 2 * R ^ 2 := by
    refine (covariantJetNormSq_slotInsertEndoCc_symmRaiseEndo_le (I := I) (M := M) g 2 2 W hWself).trans ?_
    exact mul_le_mul_of_nonneg_left hW2 (pow_nonneg hfr 2)
  rw [connectionDifferenceInsertionInnerDerivativeCoefficient]
  refine (happ _ _).trans ?_
  calc
    K * covariantJetNormSq (I := I) (M := M) g 2
          (slotInsertEndoCc (I := I) (M := M) g 2
            (symmRaiseEndo (I := I) (M := M) g W)) * J ≤
        K * (fr ^ 2 * R ^ 2) * J :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hins hK) hJ
    _ = L * R ^ 2 := by simp only [L]; ring
    _ = (C * R) ^ 2 := by rw [mul_pow, hCsq]

theorem exists_connectionDifferenceInsertionInnerActionCoefficient_pairing_secondOrder_bound
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
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
            g.inner x u v + ccTensorBilinSymm (I := I) g U x u v),
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ ≤ ρ →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) U‖ ≤ ρ →
        ∀ (R D2 N : ℝ), 0 ≤ R → 0 ≤ D2 → 0 ≤ N →
        covariantJetNormSq (I := I) (M := M) g 2 U ≤ R ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 2 (T - U) ≤ D2 ^ 2 →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) (T - U)‖ ≤ N →
      covariantJetNormSq (I := I) (M := M) g 2
          (connectionDifferenceInsertionInnerActionCoefficient (I := I) (M := M) g gT T -
            connectionDifferenceInsertionInnerActionCoefficient (I := I) (M := M) g gU U) ≤
        (B * (D2 + R * N)) ^ 2 := by
  obtain ⟨ρp, Cp, hρp, hCp, hpair⟩ :=
    RicciDeTurckLowOrder.connLow_pair_h2 (I := I) (M := M) hDim g
  obtain ⟨ρb, Cb, hρb, hCb, hbdd⟩ :=
    RicciDeTurckLowOrder.low_connection_coefficient_sobolev_two_bound (I := I) (M := M) hDim g
  obtain ⟨Ci, hCi, hinPair⟩ :=
    exists_connectionDifferenceInsertionInnerDerivativeCoefficient_pairing_secondOrder_bound (I := I) (M := M) hDim g
  obtain ⟨Cib, hCib, hinBdd⟩ :=
    exists_connectionDifferenceInsertionInnerDerivativeCoefficient_secondOrder_bound (I := I) (M := M) hDim g
  obtain ⟨Ca, hCa, happ⟩ :=
    exists_operatorFieldComposition_covariantJetNormSq_two_bound (I := I) (M := M) hDim g 3 3 3
  let ρ : ℝ := min ρp ρb
  let B : ℝ := 2 * Ca * (Ci * Cb + Cib * Cp)
  have hρ : 0 < ρ := lt_min hρp hρb
  have hB : 0 ≤ B := by
    dsimp only [B]
    positivity
  refine ⟨ρ, B, hρ, hB, ?_⟩
  intro gT gU T U hT hU hTtie hUtie hTn hUn
    R D2 N hR hD2 hN hU2 hTU2 hTUn
  let IT : SmoothCcTensor g 3 3 := connectionDifferenceInsertionInnerDerivativeCoefficient (I := I) (M := M) g T
  let IU : SmoothCcTensor g 3 3 := connectionDifferenceInsertionInnerDerivativeCoefficient (I := I) (M := M) g U
  let CT : SmoothCcTensor g 3 3 :=
    RicciDeTurckLowOrder.connectionDifferenceLowOrderOperator (I := I) (M := M) g gT
  let CU : SmoothCcTensor g 3 3 :=
    RicciDeTurckLowOrder.connectionDifferenceLowOrderOperator (I := I) (M := M) g gU
  let X : SmoothCcTensor g 3 3 :=
    ccOperatorFieldComp (I := I) (M := M) g 3 3 3 (IT - IU) CT
  let Y : SmoothCcTensor g 3 3 :=
    ccOperatorFieldComp (I := I) (M := M) g 3 3 3 IU (CT - CU)
  let x : ℝ := Ca * (Ci * D2) * Cb
  let y : ℝ := Ca * (Cib * R) * (Cp * N)
  have hx0 : 0 ≤ x := by dsimp only [x]; positivity
  have hy0 : 0 ≤ y := by dsimp only [y]; positivity
  have hTnp : ‖ccTensorToHs (I := I) (M := M) g 2
      (2 : ℝ) T‖ ≤ ρp := hTn.trans (min_le_left _ _)
  have hUnp : ‖ccTensorToHs (I := I) (M := M) g 2
      (2 : ℝ) U‖ ≤ ρp := hUn.trans (min_le_left _ _)
  have hTnb : ‖ccTensorToHs (I := I) (M := M) g 2
      (2 : ℝ) T‖ ≤ ρb := hTn.trans (min_le_right _ _)
  have hITdiff : covariantJetNormSq (I := I) (M := M) g 2 (IT - IU) ≤
      (Ci * D2) ^ 2 := by
    simpa only [IT, IU] using hinPair T U hT hU D2 hD2 hTU2
  have hIU : covariantJetNormSq (I := I) (M := M) g 2 IU ≤
      (Cib * R) ^ 2 := by
    simpa only [IU] using hinBdd U hU R hR hU2
  have hCT : covariantJetNormSq (I := I) (M := M) g 2 CT ≤ Cb ^ 2 := by
    simpa only [CT] using hbdd T gT hTtie hTnb
  have hCdiff : covariantJetNormSq (I := I) (M := M) g 2 (CT - CU) ≤
      (Cp * N) ^ 2 := by
    have hp := hpair T U gT gU hTtie hUtie hTnp hUnp
    exact hp.trans
      (pow_le_pow_left₀ (mul_nonneg hCp (norm_nonneg _))
        (mul_le_mul_of_nonneg_left hTUn hCp) 2)
  have hX : covariantJetNormSq (I := I) (M := M) g 2 X ≤ x ^ 2 := by
    simpa only [X, x] using
      happ (IT - IU) CT (Ci * D2) Cb
        (mul_nonneg hCi hD2) hCb hITdiff hCT
  have hY : covariantJetNormSq (I := I) (M := M) g 2 Y ≤ y ^ 2 := by
    simpa only [Y, y] using
      happ IU (CT - CU) (Cib * R) (Cp * N)
        (mul_nonneg hCib hR) (mul_nonneg hCp hN) hIU hCdiff
  have hsplit :
      connectionDifferenceInsertionInnerActionCoefficient (I := I) (M := M) g gT T -
          connectionDifferenceInsertionInnerActionCoefficient (I := I) (M := M) g gU U = X + Y := by
    simp only [connectionDifferenceInsertionInnerActionCoefficient, X, Y, IT, IU, CT, CU,
      operatorFieldComposition_sub_left, operatorFieldComposition_sub_right]
    module
  have hlead : 2 * (x + y) ≤ B * (D2 + R * N) := by
    have hgap : B * (D2 + R * N) =
        2 * (x + y) +
          2 * Ca * (Cib * Cp * D2 + Ci * Cb * R * N) := by
      simp only [B, x, y]
      ring
    rw [hgap]
    exact le_add_of_nonneg_right
      (mul_nonneg (mul_nonneg (by norm_num) hCa)
        (add_nonneg
          (mul_nonneg (mul_nonneg hCib hCp) hD2)
          (mul_nonneg
            (mul_nonneg (mul_nonneg hCi hCb) hR) hN)))
  rw [hsplit]
  refine (covariantJetNormSq_add_le (I := I) (M := M) g 2 X Y).trans ?_
  calc
    2 * (covariantJetNormSq (I := I) (M := M) g 2 X +
        covariantJetNormSq (I := I) (M := M) g 2 Y) ≤
      2 * (x ^ 2 + y ^ 2) :=
        mul_le_mul_of_nonneg_left (add_le_add hX hY) (by norm_num)
    _ ≤ (2 * (x + y)) ^ 2 := by
      nlinarith [mul_nonneg hx0 hy0]
    _ ≤ (B * (D2 + R * N)) ^ 2 :=
      pow_le_pow_left₀
        (mul_nonneg (by norm_num) (add_nonneg hx0 hy0)) hlead 2

noncomputable def ricciQuadraticKernelDerivativeBlock
    (g gm : SmoothRiemannianMetric I M) (pm : Equiv.Perm (Fin 4))
    (Z : SmoothCcTensor g 3 3) : SmoothCcTensor g 3 4 :=
  ccOperatorFieldComp (I := I) (M := M) g 3 4 4
    (permCoeff (I := I) (M := M) g pm)
    (ccOperatorFieldComp (I := I) (M := M) g 3 3 4
      (connectionDifferenceContravariantInsertionField (I := I) g gm) Z)

theorem exists_ricciQuadraticKernelDerivativeBlock_pairing_secondOrder_bound
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (gT gU : SmoothRiemannianMetric I M)
        (pm : Equiv.Perm (Fin 4)) (ZT ZU : SmoothCcTensor g 3 3)
        (P OD OU ZB ZD : ℝ),
        0 ≤ P → 0 ≤ OD → 0 ≤ OU → 0 ≤ ZB → 0 ≤ ZD →
        covariantJetNormSq (I := I) (M := M) g 2
            (permCoeff (I := I) (M := M) g pm) ≤ P ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 2
            (connectionDifferenceContravariantInsertionField (I := I) g gT -
              connectionDifferenceContravariantInsertionField (I := I) g gU) ≤ OD ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 2
            (connectionDifferenceContravariantInsertionField (I := I) g gU) ≤ OU ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 2 ZT ≤ ZB ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 2 (ZT - ZU) ≤ ZD ^ 2 →
      covariantJetNormSq (I := I) (M := M) g 2
          (ricciQuadraticKernelDerivativeBlock (I := I) (M := M) g gT pm ZT -
            ricciQuadraticKernelDerivativeBlock (I := I) (M := M) g gU pm ZU) ≤
        (C * P * (OD * ZB + OU * ZD)) ^ 2 := by
  obtain ⟨C4, hC4, hout⟩ :=
    exists_operatorFieldComposition_covariantJetNormSq_two_bound (I := I) (M := M) hDim g 3 4 4
  obtain ⟨C3, hC3, hinn⟩ :=
    exists_operatorFieldComposition_covariantJetNormSq_two_bound (I := I) (M := M) hDim g 3 3 4
  let C : ℝ := 2 * C4 * C3
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro gT gU pm ZT ZU P OD OU ZB ZD
    hP hOD hOU hZB hZD hp hoDiff hoU hZT hZdiff
  let OT : SmoothCcTensor g 3 4 :=
    connectionDifferenceContravariantInsertionField (I := I) g gT
  let OUf : SmoothCcTensor g 3 4 :=
    connectionDifferenceContravariantInsertionField (I := I) g gU
  let X : SmoothCcTensor g 3 4 :=
    ccOperatorFieldComp (I := I) (M := M) g 3 3 4 (OT - OUf) ZT
  let Y : SmoothCcTensor g 3 4 :=
    ccOperatorFieldComp (I := I) (M := M) g 3 3 4 OUf (ZT - ZU)
  let x : ℝ := C3 * OD * ZB
  let y : ℝ := C3 * OU * ZD
  have hx0 : 0 ≤ x := by dsimp only [x]; positivity
  have hy0 : 0 ≤ y := by dsimp only [y]; positivity
  have hX : covariantJetNormSq (I := I) (M := M) g 2 X ≤ x ^ 2 := by
    simpa only [X, x, OT, OUf] using
      hinn (connectionDifferenceContravariantInsertionField (I := I) g gT -
          connectionDifferenceContravariantInsertionField (I := I) g gU) ZT
        OD ZB hOD hZB hoDiff hZT
  have hY : covariantJetNormSq (I := I) (M := M) g 2 Y ≤ y ^ 2 := by
    simpa only [Y, y, OUf] using
      hinn (connectionDifferenceContravariantInsertionField (I := I) g gU) (ZT - ZU)
        OU ZD hOU hZD hoU hZdiff
  have hinner :
      ccOperatorFieldComp (I := I) (M := M) g 3 3 4 OT ZT -
          ccOperatorFieldComp (I := I) (M := M) g 3 3 4 OUf ZU = X + Y := by
    simp only [X, Y, OT, OUf, operatorFieldComposition_sub_left, operatorFieldComposition_sub_right]
    module
  have hsum : covariantJetNormSq (I := I) (M := M) g 2 (X + Y) ≤
      (2 * (x + y)) ^ 2 := by
    refine (covariantJetNormSq_add_le (I := I) (M := M) g 2 X Y).trans ?_
    calc
      2 * (covariantJetNormSq (I := I) (M := M) g 2 X +
          covariantJetNormSq (I := I) (M := M) g 2 Y) ≤
        2 * (x ^ 2 + y ^ 2) :=
          mul_le_mul_of_nonneg_left (add_le_add hX hY) (by norm_num)
      _ ≤ (2 * (x + y)) ^ 2 := by
        nlinarith [mul_nonneg hx0 hy0]
  have hform :
      ricciQuadraticKernelDerivativeBlock (I := I) (M := M) g gT pm ZT -
          ricciQuadraticKernelDerivativeBlock (I := I) (M := M) g gU pm ZU =
        ccOperatorFieldComp (I := I) (M := M) g 3 4 4
          (permCoeff (I := I) (M := M) g pm) (X + Y) := by
    rw [ricciQuadraticKernelDerivativeBlock, ricciQuadraticKernelDerivativeBlock, ← operatorFieldComposition_sub_right, hinner]
  rw [hform]
  have hxy0 : 0 ≤ 2 * (x + y) :=
    mul_nonneg (by norm_num) (add_nonneg hx0 hy0)
  refine (hout _ _ P (2 * (x + y)) hP hxy0 hp hsum).trans_eq ?_
  simp only [C, x, y]
  ring

end RicciDeTurckPairing
end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral
end

section

noncomputable section


open Bundle Manifold MeasureTheory Set Filter DifferentialGeometry.Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Sobolev (covariantJetNormSq
  covariantJetNormSq_add_le covariantJetNormSq_nonneg
  covariantJetNormSq_reindexCoeffGen covariantJetNormSq_smul)
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Analysis.Sobolev.TensorHilbert
open DifferentialGeometry.Analysis.Sobolev (metricConnectionDifferenceLoweredCoefficient)
open DifferentialGeometry.Analysis.Spectral
  (ccOperatorFieldComp operatorFieldComposition_sub_left ccTensorToHs pureTrace slotExtendIter)
open DifferentialGeometry.PDE.DeTurck.RicciLinearization
open DifferentialGeometry.Analysis.Spectral.DeTurck
open DifferentialGeometry.Analysis.Spectral.MetricRealization

private lemma le_square_one_add (x : ℝ) :
    x ≤ (1 + x) ^ 2 := by
  nlinarith only [sq_nonneg x]

private lemma second_le_four_term_sum
    (D3 D2 A N : ℝ) (hD3 : 0 ≤ D3) (hD2 : 0 ≤ D2)
    (hA : 0 ≤ A) (hN : 0 ≤ N) :
    D2 ≤ D3 + D2 + A * D2 + N := by
  nlinarith only [hD3, hN, mul_nonneg hA hD2]

private lemma first_le_four_term_sum
    (D3 D2 A N : ℝ) (hD2 : 0 ≤ D2) (hA : 0 ≤ A) (hN : 0 ≤ N) :
    D3 ≤ D3 + D2 + A * D2 + N := by
  nlinarith only [hD2, hN, mul_nonneg hA hD2]

private lemma middle_le_four_term_sum
    (D3 D2 A N : ℝ) (hD3 : 0 ≤ D3) (hN : 0 ≤ N) :
    D2 + A * D2 ≤ D3 + D2 + A * D2 + N := by
  linarith only [hD3, hN]

variable
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
      [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

namespace RicciDeTurckPairing

private lemma mul_sq_mul_sq (a b : ℝ) : a ^ 2 * b ^ 2 = (a * b) ^ 2 := by
  rw [mul_pow]

private lemma reassociate_four_factor_sq_left (a b c d : ℝ) :
    (a * (b * d) * c) ^ 2 = (a * b * c * d) ^ 2 := by
  ring

private lemma reassociate_four_factor_sq_left' (a b c d : ℝ) :
    (a * b * (c * d)) ^ 2 = (a * b * c * d) ^ 2 := by
  ring

private lemma factor_common_product (p a b c d : ℝ) :
    p * (a * c * d + b * c * d) = p * (a + b) * c * d := by
  ring

private lemma mixed_pairing_scale_sq (p a b c d e f : ℝ) :
    (p * ((a * d) * (b * c) + e * (f * c * d))) ^ 2 =
      (p * (a * b + e * f) * c * d) ^ 2 := by
  ring

theorem exists_lieCorrectionZeroMixedConnectionHalfDerivativeCoefficient_pairing_secondOrder_bound
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ ρ : ℝ, ∃ B : ℝ → ℝ, 0 < ρ ∧
      (∀ R : ℝ, 0 ≤ R → 0 ≤ B R) ∧
      ∀ (σ : Equiv.Perm (Fin 4))
        (gT gU : SmoothRiemannianMetric I M)
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
        {δ : ℝ} (_hδ_le : δ ≤ 1 / 3) (_hδ0 : 0 ≤ δ)
        (_hδT : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) δ)
        (_hδU : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g U) δ)
        (_hδZ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g
            (0 : SmoothCcTensor g 0 2)) δ),
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ ≤ ρ →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) U‖ ≤ ρ →
        ∀ (R A D2 D3 N : ℝ),
        0 ≤ R → 0 ≤ A → 0 ≤ D2 → 0 ≤ D3 → 0 ≤ N →
        covariantJetNormSq (I := I) (M := M) g 2 T ≤ R ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 2 U ≤ R ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 3 T ≤ A ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 3 U ≤ A ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 2 (T - U) ≤ D2 ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 3 (T - U) ≤ D3 ^ 2 →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) (T - U)‖ ≤ N →
      covariantJetNormSq (I := I) (M := M) g 2
          (lieCorrectionZeroMixedConnectionHalfDerivativeCoefficient (I := I) (M := M) g gT g T σ -
            lieCorrectionZeroMixedConnectionHalfDerivativeCoefficient (I := I) (M := M) g gU g U σ) ≤
        (B R * (1 + A) * (D3 + D2 + A * D2 + N)) ^ 2 := by
  obtain ⟨ρ2p, Ct2, hρ2p, hCt2, ht2p⟩ :=
    RicciDeTurckLowOrder.trace2_pair_h2 (I := I) (M := M) hDim g
  obtain ⟨ρ2b, Bt2, hρ2b, hBt2, ht2b⟩ :=
    RicciDeTurckLowOrder.trace_two_sobolev_two_bound (I := I) (M := M) hDim g
  obtain ⟨ρ3p, Ct3, hρ3p, hCt3, ht3p⟩ :=
    RicciDeTurckLowOrder.trace3_pair_h2 (I := I) (M := M) hDim g
  obtain ⟨ρ3b, Bt3, hρ3b, hBt3, ht3b⟩ :=
    RicciDeTurckLowOrder.trace_three_sobolev_two_bound (I := I) (M := M) hDim g
  obtain ⟨ρ4p, Ct4, hρ4p, hCt4, ht4p⟩ :=
    RicciDeTurckLowOrder.trace4_pair_h2 (I := I) (M := M) hDim g
  obtain ⟨ρ4b, Bt4, hρ4b, hBt4, ht4b⟩ :=
    RicciDeTurckLowOrder.trace_four_sobolev_two_bound (I := I) (M := M) hDim g
  obtain ⟨B0m, B1m, hB0m, hB1m, hmcdp⟩ :=
    RicciDeTurckLowOrder.mcd_pair_h2 (I := I) (M := M) hDim g
      (δ₀ := (1 : ℝ) / 3) (by norm_num) (by norm_num)
  obtain ⟨Bm, hBm, hmcdb⟩ :=
    RicciDeTurckLowOrder.metric_connection_difference_coefficient_sobolev_two_bound (I := I) (M := M) hDim g
      (δ₀ := (1 : ℝ) / 3) (by norm_num) (by norm_num)
  obtain ⟨Cp, hCp, hprod⟩ := exists_tensorThreeTwoProductCoefficient_covariantJetNormSq_two_bound (I := I) (M := M) hDim g
  obtain ⟨C0, hC0, happ0⟩ :=
    exists_operatorFieldComposition_covariantJetNormSq_two_bound (I := I) (M := M) hDim g 3 3 5
  obtain ⟨C1, hC1, happ1⟩ :=
    exists_operatorFieldComposition_covariantJetNormSq_two_bound (I := I) (M := M) hDim g 3 5 3
  obtain ⟨P1, hP1, hpair1⟩ :=
    exists_operatorFieldComposition_difference_covariantJetNormSq_two_bound (I := I) (M := M) hDim g 3 5 3
  obtain ⟨C2, hC2, happ2⟩ :=
    exists_operatorFieldComposition_covariantJetNormSq_two_bound (I := I) (M := M) hDim g 3 3 6
  obtain ⟨P2, hP2, hpair2⟩ :=
    exists_operatorFieldComposition_difference_covariantJetNormSq_two_bound (I := I) (M := M) hDim g 3 3 6
  obtain ⟨C3, hC3, happ3⟩ :=
    exists_operatorFieldComposition_covariantJetNormSq_two_bound (I := I) (M := M) hDim g 3 6 4
  obtain ⟨P3, hP3, hpair3⟩ :=
    exists_operatorFieldComposition_difference_covariantJetNormSq_two_bound (I := I) (M := M) hDim g 3 6 4
  obtain ⟨C4, hC4, happ4⟩ :=
    exists_operatorFieldComposition_covariantJetNormSq_two_bound (I := I) (M := M) hDim g 3 4 2
  obtain ⟨P4, hP4, hpair4⟩ :=
    exists_operatorFieldComposition_difference_covariantJetNormSq_two_bound (I := I) (M := M) hDim g 3 4 2
  let fr : ℝ := Module.finrank ℝ E
  let Jm : ℝ := covariantJetNormSq (I := I) (M := M) g 2
    (metricConnectionDifferenceLoweringCoefficient (I := I) (M := M) g)
  let FP : ℝ := 1 + Cp
  let FM : ℝ := 1 + fr ^ 3
  let M1 : ℝ := 1 + Jm
  let ρ : ℝ := min (min ρ2p ρ2b) (min (min ρ3p ρ3b) (min ρ4p ρ4b))
  let S0 : ℝ → ℝ := fun R => C0 * (FP * R) * M1
  let D0 : ℝ := C0 * FP * M1
  let S1 : ℝ → ℝ := fun R => C1 * Bt3 * S0 R
  let D1 : ℝ → ℝ := fun R => P1 * (Ct3 * S0 R + Bt3 * D0)
  let SM : ℝ → ℝ := fun R => FM * Bm R
  let DM : ℝ → ℝ := fun R => FM * (B0m R + B1m R)
  let S2 : ℝ → ℝ := fun R => C2 * SM R * S1 R
  let D2c : ℝ → ℝ := fun R => P2 * (DM R * S1 R + SM R * D1 R)
  let S3 : ℝ → ℝ := fun R => C3 * Bt4 * S2 R
  let D3c : ℝ → ℝ := fun R => P3 * (Ct4 * S2 R + Bt4 * D2c R)
  let D4c : ℝ → ℝ := fun R => P4 * (Ct2 * S3 R + Bt2 * D3c R)
  let B : ℝ → ℝ := D4c
  have hfr : 0 ≤ fr := Nat.cast_nonneg _
  have hJm : 0 ≤ Jm := covariantJetNormSq_nonneg (I := I) (M := M) (m := 2) g _
  have hFP : 0 ≤ FP := add_nonneg (by norm_num) hCp
  have hFM : 0 ≤ FM := add_nonneg (by norm_num) (pow_nonneg hfr 3)
  have hM1 : 0 ≤ M1 := add_nonneg (by norm_num) hJm
  have hρ : 0 < ρ :=
    lt_min (lt_min hρ2p hρ2b)
      (lt_min (lt_min hρ3p hρ3b) (lt_min hρ4p hρ4b))
  have hS0 : ∀ R : ℝ, 0 ≤ R → 0 ≤ S0 R := fun R hR =>
    mul_nonneg (mul_nonneg hC0 (mul_nonneg hFP hR)) hM1
  have hD0 : 0 ≤ D0 := mul_nonneg (mul_nonneg hC0 hFP) hM1
  have hS1 : ∀ R : ℝ, 0 ≤ R → 0 ≤ S1 R := fun R hR =>
    mul_nonneg (mul_nonneg hC1 hBt3) (hS0 R hR)
  have hD1 : ∀ R : ℝ, 0 ≤ R → 0 ≤ D1 R := fun R hR =>
    mul_nonneg hP1
      (add_nonneg (mul_nonneg hCt3 (hS0 R hR)) (mul_nonneg hBt3 hD0))
  have hSM : ∀ R : ℝ, 0 ≤ R → 0 ≤ SM R := fun R hR =>
    mul_nonneg hFM (hBm R hR)
  have hDM : ∀ R : ℝ, 0 ≤ R → 0 ≤ DM R := fun R hR =>
    mul_nonneg hFM (add_nonneg (hB0m R hR) (hB1m R hR))
  have hS2 : ∀ R : ℝ, 0 ≤ R → 0 ≤ S2 R := fun R hR =>
    mul_nonneg (mul_nonneg hC2 (hSM R hR)) (hS1 R hR)
  have hD2c : ∀ R : ℝ, 0 ≤ R → 0 ≤ D2c R := fun R hR =>
    mul_nonneg hP2
      (add_nonneg (mul_nonneg (hDM R hR) (hS1 R hR))
        (mul_nonneg (hSM R hR) (hD1 R hR)))
  have hS3 : ∀ R : ℝ, 0 ≤ R → 0 ≤ S3 R := fun R hR =>
    mul_nonneg (mul_nonneg hC3 hBt4) (hS2 R hR)
  have hD3c : ∀ R : ℝ, 0 ≤ R → 0 ≤ D3c R := fun R hR =>
    mul_nonneg hP3
      (add_nonneg (mul_nonneg hCt4 (hS2 R hR))
        (mul_nonneg hBt4 (hD2c R hR)))
  have hD4c : ∀ R : ℝ, 0 ≤ R → 0 ≤ D4c R := fun R hR =>
    mul_nonneg hP4
      (add_nonneg (mul_nonneg hCt2 (hS3 R hR))
        (mul_nonneg hBt2 (hD3c R hR)))
  refine ⟨ρ, B, hρ, fun R hR => hD4c R hR, ?_⟩
  intro σ gT gU T U hT hU hTtie hUtie δ hδ_le hδ0 hδT hδU hδZ
    hTn hUn R A D2 D3 N hR hA hD2 hD3 hN
    hT2 hU2 hT3 hU3 hTU2 hTU3 hTUn
  let D : ℝ := D3 + D2 + A * D2 + N
  have hD : 0 ≤ D :=
    add_nonneg (add_nonneg (add_nonneg hD3 hD2) (mul_nonneg hA hD2)) hN
  have h1A : 0 ≤ 1 + A := add_nonneg (by norm_num) hA
  have hNle : N ≤ D := by
    dsimp only [D]
    exact le_add_of_nonneg_left
      (add_nonneg (add_nonneg hD3 hD2) (mul_nonneg hA hD2))
  have hD2le : D2 ≤ D := by
    dsimp only [D]
    exact second_le_four_term_sum D3 D2 A N hD3 hD2 hA hN
  have hρ2p_le : ρ ≤ ρ2p := (min_le_left _ _).trans (min_le_left _ _)
  have hρ2b_le : ρ ≤ ρ2b := (min_le_left _ _).trans (min_le_right _ _)
  have hρ3p_le : ρ ≤ ρ3p :=
    (min_le_right _ _).trans ((min_le_left _ _).trans (min_le_left _ _))
  have hρ3b_le : ρ ≤ ρ3b :=
    (min_le_right _ _).trans ((min_le_left _ _).trans (min_le_right _ _))
  have hρ4p_le : ρ ≤ ρ4p :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hρ4b_le : ρ ≤ ρ4b :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  let PrT : SmoothCcTensor g 3 5 := tensorThreeTwoProductCoefficient (I := I) (M := M) g T
  let PrU : SmoothCcTensor g 3 5 := tensorThreeTwoProductCoefficient (I := I) (M := M) g U
  let Mo : SmoothCcTensor g 3 3 := metricConnectionDifferenceLoweringCoefficient (I := I) (M := M) g
  let T2T : SmoothCcTensor g 4 2 := reindexedPureTrace (I := I) (M := M) g gT 2 σ
  let T2U : SmoothCcTensor g 4 2 := reindexedPureTrace (I := I) (M := M) g gU 2 σ
  let T3T : SmoothCcTensor g 5 3 := reindexedPureTrace (I := I) (M := M) g gT 3
    DifferentialGeometry.Analysis.Spectral.LieCorrectionZeroCore.lieCorrectionZeroMixedConnectionPermutationCycleZeroOneFour
  let T3U : SmoothCcTensor g 5 3 := reindexedPureTrace (I := I) (M := M) g gU 3
    DifferentialGeometry.Analysis.Spectral.LieCorrectionZeroCore.lieCorrectionZeroMixedConnectionPermutationCycleZeroOneFour
  let T4T : SmoothCcTensor g 6 4 := reindexedPureTrace (I := I) (M := M) g gT 4
    DifferentialGeometry.Analysis.Spectral.LieCorrectionZeroCore.lieCorrectionZeroMixedConnectionPermutationCycleZeroTwoThreeOne
  let T4U : SmoothCcTensor g 6 4 := reindexedPureTrace (I := I) (M := M) g gU 4
    DifferentialGeometry.Analysis.Spectral.LieCorrectionZeroCore.lieCorrectionZeroMixedConnectionPermutationCycleZeroTwoThreeOne
  let McT : SmoothCcTensor g 0 3 :=
    metricConnectionDifferenceLoweredCoefficient (I := I) (M := M) g gT g
  let McU : SmoothCcTensor g 0 3 :=
    metricConnectionDifferenceLoweredCoefficient (I := I) (M := M) g gU g
  let ExT : SmoothCcTensor g 3 6 :=
    slotExtendIter (I := I) (M := M) g 0 3 3 McT
  let ExU : SmoothCcTensor g 3 6 :=
    slotExtendIter (I := I) (M := M) g 0 3 3 McU
  let Z0T : SmoothCcTensor g 3 5 :=
    ccOperatorFieldComp (I := I) (M := M) g 3 3 5 PrT Mo
  let Z0U : SmoothCcTensor g 3 5 :=
    ccOperatorFieldComp (I := I) (M := M) g 3 3 5 PrU Mo
  let Z1T : SmoothCcTensor g 3 3 :=
    ccOperatorFieldComp (I := I) (M := M) g 3 5 3 T3T Z0T
  let Z1U : SmoothCcTensor g 3 3 :=
    ccOperatorFieldComp (I := I) (M := M) g 3 5 3 T3U Z0U
  let Z2T : SmoothCcTensor g 3 6 :=
    ccOperatorFieldComp (I := I) (M := M) g 3 3 6 ExT Z1T
  let Z2U : SmoothCcTensor g 3 6 :=
    ccOperatorFieldComp (I := I) (M := M) g 3 3 6 ExU Z1U
  let Z3T : SmoothCcTensor g 3 4 :=
    ccOperatorFieldComp (I := I) (M := M) g 3 6 4 T4T Z2T
  let Z3U : SmoothCcTensor g 3 4 :=
    ccOperatorFieldComp (I := I) (M := M) g 3 6 4 T4U Z2U
  let Z4T : SmoothCcTensor g 3 2 :=
    ccOperatorFieldComp (I := I) (M := M) g 3 4 2 T2T Z3T
  let Z4U : SmoothCcTensor g 3 2 :=
    ccOperatorFieldComp (I := I) (M := M) g 3 4 2 T2U Z3U
  have hCp_le : Cp ≤ FP ^ 2 := by
    dsimp only [FP]
    exact le_square_one_add Cp
  have hJm_le : Jm ≤ M1 ^ 2 := by
    dsimp only [M1]
    exact le_square_one_add Jm
  have hPrT : covariantJetNormSq (I := I) (M := M) g 2 PrT ≤ (FP * R) ^ 2 := by
    calc
      covariantJetNormSq (I := I) (M := M) g 2 PrT ≤
          Cp * covariantJetNormSq (I := I) (M := M) g 2 T := by
        simpa only [PrT] using hprod T
      _ ≤ Cp * R ^ 2 := mul_le_mul_of_nonneg_left hT2 hCp
      _ ≤ FP ^ 2 * R ^ 2 := mul_le_mul_of_nonneg_right hCp_le (sq_nonneg R)
      _ = (FP * R) ^ 2 := mul_sq_mul_sq FP R
  have hPrU : covariantJetNormSq (I := I) (M := M) g 2 PrU ≤ (FP * R) ^ 2 := by
    calc
      covariantJetNormSq (I := I) (M := M) g 2 PrU ≤
          Cp * covariantJetNormSq (I := I) (M := M) g 2 U := by
        simpa only [PrU] using hprod U
      _ ≤ Cp * R ^ 2 := mul_le_mul_of_nonneg_left hU2 hCp
      _ ≤ FP ^ 2 * R ^ 2 := mul_le_mul_of_nonneg_right hCp_le (sq_nonneg R)
      _ = (FP * R) ^ 2 := mul_sq_mul_sq FP R
  have hPrD : covariantJetNormSq (I := I) (M := M) g 2 (PrT - PrU) ≤
      (FP * D) ^ 2 := by
    calc
      covariantJetNormSq (I := I) (M := M) g 2 (PrT - PrU) =
          covariantJetNormSq (I := I) (M := M) g 2
            (tensorThreeTwoProductCoefficient (I := I) (M := M) g (T - U)) := by
        dsimp only [PrT, PrU]
        rw [tensorThreeTwoProductCoefficient_sub]
      _ ≤ Cp * covariantJetNormSq (I := I) (M := M) g 2 (T - U) := hprod (T - U)
      _ ≤ Cp * D2 ^ 2 := mul_le_mul_of_nonneg_left hTU2 hCp
      _ ≤ FP ^ 2 * D ^ 2 :=
        (mul_le_mul_of_nonneg_right hCp_le (sq_nonneg D2)).trans
          (mul_le_mul_of_nonneg_left
            (pow_le_pow_left₀ hD2 hD2le 2) (sq_nonneg FP))
      _ = (FP * D) ^ 2 := mul_sq_mul_sq FP D
  have hMo : covariantJetNormSq (I := I) (M := M) g 2 Mo ≤ M1 ^ 2 := by
    simpa only [Mo, Jm] using hJm_le
  have hT2U : covariantJetNormSq (I := I) (M := M) g 2 T2U ≤ Bt2 ^ 2 := by
    dsimp only [T2U]
    rw [covariantJetNormSq_reindexedPureTrace]
    exact ht2b U gU hUtie (hUn.trans hρ2b_le)
  have hT2D : covariantJetNormSq (I := I) (M := M) g 2 (T2T - T2U) ≤
      (Ct2 * D) ^ 2 := by
    have hraw := ht2p T U gT gU hTtie hUtie
      (hTn.trans hρ2p_le) (hUn.trans hρ2p_le)
    have hmul : Ct2 * ‖ccTensorToHs (I := I) (M := M) g 2
        (2 : ℝ) (T - U)‖ ≤ Ct2 * D :=
      (mul_le_mul_of_nonneg_left hTUn hCt2).trans
        (mul_le_mul_of_nonneg_left hNle hCt2)
    calc
      covariantJetNormSq (I := I) (M := M) g 2 (T2T - T2U) =
          covariantJetNormSq (I := I) (M := M) g 2
            (pureTrace (I := I) (M := M) g gT 2 -
              pureTrace (I := I) (M := M) g gU 2) := by
        dsimp only [T2T, T2U]
        rw [reindexedPureTrace_sub, covariantJetNormSq_reindexCoeffGen]
      _ ≤ (Ct2 * ‖ccTensorToHs (I := I) (M := M) g 2
          (2 : ℝ) (T - U)‖) ^ 2 := hraw
      _ ≤ (Ct2 * D) ^ 2 :=
        pow_le_pow_left₀ (mul_nonneg hCt2 (norm_nonneg _)) hmul 2
  have hT3T : covariantJetNormSq (I := I) (M := M) g 2 T3T ≤ Bt3 ^ 2 := by
    dsimp only [T3T]
    rw [covariantJetNormSq_reindexedPureTrace]
    exact ht3b T gT hTtie (hTn.trans hρ3b_le)
  have hT3U : covariantJetNormSq (I := I) (M := M) g 2 T3U ≤ Bt3 ^ 2 := by
    dsimp only [T3U]
    rw [covariantJetNormSq_reindexedPureTrace]
    exact ht3b U gU hUtie (hUn.trans hρ3b_le)
  have hT3D : covariantJetNormSq (I := I) (M := M) g 2 (T3T - T3U) ≤
      (Ct3 * D) ^ 2 := by
    have hraw := ht3p T U gT gU hTtie hUtie
      (hTn.trans hρ3p_le) (hUn.trans hρ3p_le)
    have hmul : Ct3 * ‖ccTensorToHs (I := I) (M := M) g 2
        (2 : ℝ) (T - U)‖ ≤ Ct3 * D :=
      (mul_le_mul_of_nonneg_left hTUn hCt3).trans
        (mul_le_mul_of_nonneg_left hNle hCt3)
    calc
      covariantJetNormSq (I := I) (M := M) g 2 (T3T - T3U) =
          covariantJetNormSq (I := I) (M := M) g 2
            (pureTrace (I := I) (M := M) g gT 3 -
              pureTrace (I := I) (M := M) g gU 3) := by
        dsimp only [T3T, T3U]
        rw [reindexedPureTrace_sub, covariantJetNormSq_reindexCoeffGen]
      _ ≤ (Ct3 * ‖ccTensorToHs (I := I) (M := M) g 2
          (2 : ℝ) (T - U)‖) ^ 2 := hraw
      _ ≤ (Ct3 * D) ^ 2 :=
        pow_le_pow_left₀ (mul_nonneg hCt3 (norm_nonneg _)) hmul 2
  have hT4U : covariantJetNormSq (I := I) (M := M) g 2 T4U ≤ Bt4 ^ 2 := by
    dsimp only [T4U]
    rw [covariantJetNormSq_reindexedPureTrace]
    exact ht4b U gU hUtie (hUn.trans hρ4b_le)
  have hT4D : covariantJetNormSq (I := I) (M := M) g 2 (T4T - T4U) ≤
      (Ct4 * D) ^ 2 := by
    have hraw := ht4p T U gT gU hTtie hUtie
      (hTn.trans hρ4p_le) (hUn.trans hρ4p_le)
    have hmul : Ct4 * ‖ccTensorToHs (I := I) (M := M) g 2
        (2 : ℝ) (T - U)‖ ≤ Ct4 * D :=
      (mul_le_mul_of_nonneg_left hTUn hCt4).trans
        (mul_le_mul_of_nonneg_left hNle hCt4)
    calc
      covariantJetNormSq (I := I) (M := M) g 2 (T4T - T4U) =
          covariantJetNormSq (I := I) (M := M) g 2
            (pureTrace (I := I) (M := M) g gT 4 -
              pureTrace (I := I) (M := M) g gU 4) := by
        dsimp only [T4T, T4U]
        rw [reindexedPureTrace_sub, covariantJetNormSq_reindexCoeffGen]
      _ ≤ (Ct4 * ‖ccTensorToHs (I := I) (M := M) g 2
          (2 : ℝ) (T - U)‖) ^ 2 := hraw
      _ ≤ (Ct4 * D) ^ 2 :=
        pow_le_pow_left₀ (mul_nonneg hCt4 (norm_nonneg _)) hmul 2
  have hMcT : covariantJetNormSq (I := I) (M := M) g 2 McT ≤
      (Bm R * (1 + A)) ^ 2 := by
    simpa only [McT] using
      hmcdb gT T hT hTtie hδ_le hδ0 hδT R A hR hA hT2 hT3
  have hMcU : covariantJetNormSq (I := I) (M := M) g 2 McU ≤
      (Bm R * (1 + A)) ^ 2 := by
    simpa only [McU] using
      hmcdb gU U hU hUtie hδ_le hδ0 hδU R A hR hA hU2 hU3
  let M0 : ℝ := B0m R * D3 + B1m R * D2 + B1m R * A * D2
  have hM0 : 0 ≤ M0 := by
    dsimp only [M0]
    exact add_nonneg
      (add_nonneg (mul_nonneg (hB0m R hR) hD3)
        (mul_nonneg (hB1m R hR) hD2))
      (mul_nonneg (mul_nonneg (hB1m R hR) hA) hD2)
  have hM0le : M0 ≤ (B0m R + B1m R) * D := by
    have hD3le : D3 ≤ D := by
      dsimp only [D]
      exact first_le_four_term_sum D3 D2 A N hD2 hA hN
    have hrestle : D2 + A * D2 ≤ D := by
      dsimp only [D]
      exact middle_le_four_term_sum D3 D2 A N hD3 hN
    calc
      M0 = B0m R * D3 + B1m R * (D2 + A * D2) := by
        simp only [M0]
        ring
      _ ≤ B0m R * D + B1m R * D :=
        add_le_add
          (mul_le_mul_of_nonneg_left hD3le (hB0m R hR))
          (mul_le_mul_of_nonneg_left hrestle (hB1m R hR))
      _ = (B0m R + B1m R) * D := by ring
  have hMcD : covariantJetNormSq (I := I) (M := M) g 2 (McT - McU) ≤ M0 ^ 2 := by
    simpa only [McT, McU, M0] using
      hmcdp gT gU T U hT hU hTtie hUtie
        hδ_le hδ0 hδT hδ_le hδ0 hδU
        R A D2 D3 hR hA hD2 hD3 hU2 hT3 hTU2 hTU3
  have hfr3_le : fr ^ 3 ≤ FM ^ 2 := by
    dsimp only [FM]
    exact le_square_one_add (fr ^ 3)
  have hExT : covariantJetNormSq (I := I) (M := M) g 2 ExT ≤
      (SM R * (1 + A)) ^ 2 := by
    calc
      covariantJetNormSq (I := I) (M := M) g 2 ExT ≤
          fr ^ 3 * covariantJetNormSq (I := I) (M := M) g 2 McT := by
        simpa only [ExT, fr] using covariantJetNormSq_slotExtendIter_three_le (I := I) (M := M) g 0 3 McT
      _ ≤ fr ^ 3 * (Bm R * (1 + A)) ^ 2 :=
        mul_le_mul_of_nonneg_left hMcT (pow_nonneg hfr 3)
      _ ≤ FM ^ 2 * (Bm R * (1 + A)) ^ 2 :=
        mul_le_mul_of_nonneg_right hfr3_le (sq_nonneg _)
      _ = (SM R * (1 + A)) ^ 2 := by
        simp only [SM]
        simpa only [mul_assoc] using mul_sq_mul_sq FM (Bm R * (1 + A))
  have hExU : covariantJetNormSq (I := I) (M := M) g 2 ExU ≤
      (SM R * (1 + A)) ^ 2 := by
    calc
      covariantJetNormSq (I := I) (M := M) g 2 ExU ≤
          fr ^ 3 * covariantJetNormSq (I := I) (M := M) g 2 McU := by
        simpa only [ExU, fr] using covariantJetNormSq_slotExtendIter_three_le (I := I) (M := M) g 0 3 McU
      _ ≤ fr ^ 3 * (Bm R * (1 + A)) ^ 2 :=
        mul_le_mul_of_nonneg_left hMcU (pow_nonneg hfr 3)
      _ ≤ FM ^ 2 * (Bm R * (1 + A)) ^ 2 :=
        mul_le_mul_of_nonneg_right hfr3_le (sq_nonneg _)
      _ = (SM R * (1 + A)) ^ 2 := by
        simp only [SM]
        simpa only [mul_assoc] using mul_sq_mul_sq FM (Bm R * (1 + A))
  have hExD : covariantJetNormSq (I := I) (M := M) g 2 (ExT - ExU) ≤
      (DM R * D) ^ 2 := by
    calc
      covariantJetNormSq (I := I) (M := M) g 2 (ExT - ExU) =
          covariantJetNormSq (I := I) (M := M) g 2
            (slotExtendIter (I := I) (M := M) g 0 3 3 (McT - McU)) := by
        dsimp only [ExT, ExU]
        rw [slotExtendIter_sub]
      _ ≤ fr ^ 3 * covariantJetNormSq (I := I) (M := M) g 2 (McT - McU) := by
        simpa only [fr] using covariantJetNormSq_slotExtendIter_three_le (I := I) (M := M) g 0 3 (McT - McU)
      _ ≤ fr ^ 3 * M0 ^ 2 :=
        mul_le_mul_of_nonneg_left hMcD (pow_nonneg hfr 3)
      _ ≤ fr ^ 3 * ((B0m R + B1m R) * D) ^ 2 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hM0 hM0le 2)
          (pow_nonneg hfr 3)
      _ ≤ FM ^ 2 * ((B0m R + B1m R) * D) ^ 2 :=
        mul_le_mul_of_nonneg_right hfr3_le (sq_nonneg _)
      _ = (DM R * D) ^ 2 := by
        simp only [DM]
        simpa only [mul_assoc] using mul_sq_mul_sq FM ((B0m R + B1m R) * D)
  have hZ0T : covariantJetNormSq (I := I) (M := M) g 2 Z0T ≤ (S0 R) ^ 2 := by
    simpa only [Z0T, S0] using
      happ0 PrT Mo (FP * R) M1 (mul_nonneg hFP hR) hM1 hPrT hMo
  have hZ0D : covariantJetNormSq (I := I) (M := M) g 2 (Z0T - Z0U) ≤
      (D0 * D) ^ 2 := by
    have heq : Z0T - Z0U =
        ccOperatorFieldComp (I := I) (M := M) g 3 3 5 (PrT - PrU) Mo := by
      simp only [Z0T, Z0U, operatorFieldComposition_sub_left]
    rw [heq]
    have hraw := happ0 (PrT - PrU) Mo (FP * D) M1
      (mul_nonneg hFP hD) hM1 hPrD hMo
    calc
      covariantJetNormSq (I := I) (M := M) g 2
          (ccOperatorFieldComp (I := I) (M := M) g 3 3 5 (PrT - PrU) Mo) ≤
        (C0 * (FP * D) * M1) ^ 2 := hraw
      _ = (D0 * D) ^ 2 := by
        simp only [D0]
        exact reassociate_four_factor_sq_left C0 FP M1 D
  have hZ1T : covariantJetNormSq (I := I) (M := M) g 2 Z1T ≤ (S1 R) ^ 2 := by
    simpa only [Z1T, S1] using
      happ1 T3T Z0T Bt3 (S0 R) hBt3 (hS0 R hR) hT3T hZ0T
  have hZ1D : covariantJetNormSq (I := I) (M := M) g 2 (Z1T - Z1U) ≤
      (D1 R * D) ^ 2 := by
    have hraw := hpair1 T3T T3U Z0T Z0U
      (Ct3 * D) Bt3 (S0 R) (D0 * D)
      (mul_nonneg hCt3 hD) hBt3 (hS0 R hR) (mul_nonneg hD0 hD)
      hT3D hT3U hZ0T hZ0D
    calc
      covariantJetNormSq (I := I) (M := M) g 2 (Z1T - Z1U) ≤
          (P1 * ((Ct3 * D) * S0 R + Bt3 * (D0 * D))) ^ 2 := by
        simpa only [Z1T, Z1U] using hraw
      _ = (D1 R * D) ^ 2 := by
        simp only [D1]
        simpa only [one_mul, mul_one] using
          mixed_pairing_scale_sq P1 Ct3 (S0 R) 1 D Bt3 D0
  have hZ2T : covariantJetNormSq (I := I) (M := M) g 2 Z2T ≤
      (S2 R * (1 + A)) ^ 2 := by
    have hraw := happ2 ExT Z1T (SM R * (1 + A)) (S1 R)
      (mul_nonneg (hSM R hR) h1A) (hS1 R hR) hExT hZ1T
    calc
      covariantJetNormSq (I := I) (M := M) g 2 Z2T ≤
          (C2 * (SM R * (1 + A)) * S1 R) ^ 2 := by
        simpa only [Z2T] using hraw
      _ = (S2 R * (1 + A)) ^ 2 := by
        simp only [S2]
        exact reassociate_four_factor_sq_left C2 (SM R) (S1 R) (1 + A)
  have hZ2D : covariantJetNormSq (I := I) (M := M) g 2 (Z2T - Z2U) ≤
      (D2c R * (1 + A) * D) ^ 2 := by
    let u : ℝ := P2 *
      ((DM R * D) * S1 R + (SM R * (1 + A)) * (D1 R * D))
    let v : ℝ := D2c R * (1 + A) * D
    have hu : 0 ≤ u := by
      dsimp only [u]
      exact mul_nonneg hP2
        (add_nonneg (mul_nonneg (mul_nonneg (hDM R hR) hD) (hS1 R hR))
          (mul_nonneg (mul_nonneg (hSM R hR) h1A)
            (mul_nonneg (hD1 R hR) hD)))
    have huv : u ≤ v := by
      have hbase : DM R * S1 R ≤ DM R * S1 R * (1 + A) := by
        calc
          DM R * S1 R = DM R * S1 R * 1 := by ring
          _ ≤ DM R * S1 R * (1 + A) :=
            mul_le_mul_of_nonneg_left (le_add_of_nonneg_right hA)
              (mul_nonneg (hDM R hR) (hS1 R hR))
      have hfirst : DM R * S1 R * D ≤ DM R * S1 R * (1 + A) * D :=
        mul_le_mul_of_nonneg_right hbase hD
      calc
        u = P2 * (DM R * S1 R * D + SM R * D1 R * (1 + A) * D) := by
          simp only [u]
          ring
        _ ≤ P2 * (DM R * S1 R * (1 + A) * D +
            SM R * D1 R * (1 + A) * D) :=
          mul_le_mul_of_nonneg_left (add_le_add hfirst le_rfl) hP2
        _ = v := by
          simp only [v, D2c]
          exact factor_common_product P2 (DM R * S1 R) (SM R * D1 R) (1 + A) D
    have hraw := hpair2 ExT ExU Z1T Z1U
      (DM R * D) (SM R * (1 + A)) (S1 R) (D1 R * D)
      (mul_nonneg (hDM R hR) hD) (mul_nonneg (hSM R hR) h1A)
      (hS1 R hR) (mul_nonneg (hD1 R hR) hD)
      hExD hExU hZ1T hZ1D
    calc
      covariantJetNormSq (I := I) (M := M) g 2 (Z2T - Z2U) ≤ u ^ 2 := by
        simpa only [Z2T, Z2U, u] using hraw
      _ ≤ v ^ 2 := pow_le_pow_left₀ hu huv 2
      _ = (D2c R * (1 + A) * D) ^ 2 := rfl
  have hZ3T : covariantJetNormSq (I := I) (M := M) g 2 Z3T ≤
      (S3 R * (1 + A)) ^ 2 := by
    have hT4T : covariantJetNormSq (I := I) (M := M) g 2 T4T ≤ Bt4 ^ 2 := by
      dsimp only [T4T]
      rw [covariantJetNormSq_reindexedPureTrace]
      exact ht4b T gT hTtie (hTn.trans hρ4b_le)
    have hraw := happ3 T4T Z2T Bt4 (S2 R * (1 + A))
      hBt4 (mul_nonneg (hS2 R hR) h1A) hT4T hZ2T
    calc
      covariantJetNormSq (I := I) (M := M) g 2 Z3T ≤
          (C3 * Bt4 * (S2 R * (1 + A))) ^ 2 := by
        simpa only [Z3T] using hraw
      _ = (S3 R * (1 + A)) ^ 2 := by
        simp only [S3]
        exact reassociate_four_factor_sq_left' C3 Bt4 (S2 R) (1 + A)
  have hZ3D : covariantJetNormSq (I := I) (M := M) g 2 (Z3T - Z3U) ≤
      (D3c R * (1 + A) * D) ^ 2 := by
    have hraw := hpair3 T4T T4U Z2T Z2U
      (Ct4 * D) Bt4 (S2 R * (1 + A)) (D2c R * (1 + A) * D)
      (mul_nonneg hCt4 hD) hBt4 (mul_nonneg (hS2 R hR) h1A)
      (mul_nonneg (mul_nonneg (hD2c R hR) h1A) hD)
      hT4D hT4U hZ2T hZ2D
    calc
      covariantJetNormSq (I := I) (M := M) g 2 (Z3T - Z3U) ≤
          (P3 * ((Ct4 * D) * (S2 R * (1 + A)) +
            Bt4 * (D2c R * (1 + A) * D))) ^ 2 := by
        simpa only [Z3T, Z3U] using hraw
      _ = (D3c R * (1 + A) * D) ^ 2 := by
        simp only [D3c]
        exact mixed_pairing_scale_sq P3 Ct4 (S2 R) (1 + A) D Bt4 (D2c R)
  have hZ4D : covariantJetNormSq (I := I) (M := M) g 2 (Z4T - Z4U) ≤
      (D4c R * (1 + A) * D) ^ 2 := by
    have hraw := hpair4 T2T T2U Z3T Z3U
      (Ct2 * D) Bt2 (S3 R * (1 + A)) (D3c R * (1 + A) * D)
      (mul_nonneg hCt2 hD) hBt2 (mul_nonneg (hS3 R hR) h1A)
      (mul_nonneg (mul_nonneg (hD3c R hR) h1A) hD)
      hT2D hT2U hZ3T hZ3D
    calc
      covariantJetNormSq (I := I) (M := M) g 2 (Z4T - Z4U) ≤
          (P4 * ((Ct2 * D) * (S3 R * (1 + A)) +
            Bt2 * (D3c R * (1 + A) * D))) ^ 2 := by
        simpa only [Z4T, Z4U] using hraw
      _ = (D4c R * (1 + A) * D) ^ 2 := by
        simp only [D4c]
        exact mixed_pairing_scale_sq P4 Ct2 (S3 R) (1 + A) D Bt2 (D3c R)
  have hhalfT : lieCorrectionZeroMixedConnectionHalfDerivativeCoefficient (I := I) (M := M) g gT g T σ = Z4T := by rfl
  have hhalfU : lieCorrectionZeroMixedConnectionHalfDerivativeCoefficient (I := I) (M := M) g gU g U σ = Z4U := by rfl
  simpa only [hhalfT, hhalfU, B, D] using hZ4D

theorem exists_lieCorrectionZeroMixedConnectionDerivativeCoefficient_pairing_secondOrder_bound
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ ρ : ℝ, ∃ B : ℝ → ℝ, 0 < ρ ∧
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
        {δ : ℝ} (_hδ_le : δ ≤ 1 / 3) (_hδ0 : 0 ≤ δ)
        (_hδT : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) δ)
        (_hδU : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g U) δ)
        (_hδZ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g
            (0 : SmoothCcTensor g 0 2)) δ),
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ ≤ ρ →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) U‖ ≤ ρ →
        ∀ (R A D2 D3 N : ℝ),
        0 ≤ R → 0 ≤ A → 0 ≤ D2 → 0 ≤ D3 → 0 ≤ N →
        covariantJetNormSq (I := I) (M := M) g 2 T ≤ R ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 2 U ≤ R ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 3 T ≤ A ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 3 U ≤ A ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 2 (T - U) ≤ D2 ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 3 (T - U) ≤ D3 ^ 2 →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) (T - U)‖ ≤ N →
      covariantJetNormSq (I := I) (M := M) g 2
          (lieCorrectionZeroMixedConnectionDerivativeCoefficient (I := I) (M := M) g gT g T -
            lieCorrectionZeroMixedConnectionDerivativeCoefficient (I := I) (M := M) g gU g U) ≤
        (B R * (1 + A) * (D3 + D2 + A * D2 + N)) ^ 2 := by
  obtain ⟨ρ, Bh, hρ, hBh, hhalf⟩ :=
    exists_lieCorrectionZeroMixedConnectionHalfDerivativeCoefficient_pairing_secondOrder_bound (I := I) (M := M) hDim g
  let B : ℝ → ℝ := fun R => 4 * Bh R
  refine ⟨ρ, B, hρ, fun R hR => mul_nonneg (by norm_num) (hBh R hR), ?_⟩
  intro gT gU T U hT hU hTtie hUtie δ hδ_le hδ0 hδT hδU hδZ
    hTn hUn R A D2 D3 N hR hA hD2 hD3 hN
    hT2 hU2 hT3 hU3 hTU2 hTU3 hTUn
  let σ1 : Equiv.Perm (Fin 4) :=
    DifferentialGeometry.Analysis.Spectral.LieCorrectionZeroCore.lieCorrectionZeroMixedConnectionPermutationCycleZeroTwoOne
  let σ2 : Equiv.Perm (Fin 4) :=
    lieCorrectionZeroMixedConnectionTraceOutputSwapPermutation * DifferentialGeometry.Analysis.Spectral.LieCorrectionZeroCore.lieCorrectionZeroMixedConnectionPermutationCycleZeroTwoOne
  let X : SmoothCcTensor g 3 2 :=
    lieCorrectionZeroMixedConnectionHalfDerivativeCoefficient (I := I) (M := M) g gT g T σ1 -
      lieCorrectionZeroMixedConnectionHalfDerivativeCoefficient (I := I) (M := M) g gU g U σ1
  let Y : SmoothCcTensor g 3 2 :=
    lieCorrectionZeroMixedConnectionHalfDerivativeCoefficient (I := I) (M := M) g gT g T σ2 -
      lieCorrectionZeroMixedConnectionHalfDerivativeCoefficient (I := I) (M := M) g gU g U σ2
  let S : ℝ := Bh R * (1 + A) * (D3 + D2 + A * D2 + N)
  have hS : 0 ≤ S :=
    mul_nonneg (mul_nonneg (hBh R hR) (add_nonneg (by norm_num) hA))
      (add_nonneg (add_nonneg (add_nonneg hD3 hD2) (mul_nonneg hA hD2)) hN)
  have hX : covariantJetNormSq (I := I) (M := M) g 2 X ≤ S ^ 2 := by
    simpa only [X, S, σ1] using
      hhalf σ1 gT gU T U hT hU hTtie hUtie
        hδ_le hδ0 hδT hδU hδZ hTn hUn
        R A D2 D3 N hR hA hD2 hD3 hN
        hT2 hU2 hT3 hU3 hTU2 hTU3 hTUn
  have hY : covariantJetNormSq (I := I) (M := M) g 2 Y ≤ S ^ 2 := by
    simpa only [Y, S, σ2] using
      hhalf σ2 gT gU T U hT hU hTtie hUtie
        hδ_le hδ0 hδT hδU hδZ hTn hUn
        R A D2 D3 N hR hA hD2 hD3 hN
        hT2 hU2 hT3 hU3 hTU2 hTU3 hTUn
  have hsum : covariantJetNormSq (I := I) (M := M) g 2 (X + Y) ≤ (2 * S) ^ 2 := by
    refine (covariantJetNormSq_add_le (I := I) (M := M) g 2 X Y).trans ?_
    calc
      2 * (covariantJetNormSq (I := I) (M := M) g 2 X +
          covariantJetNormSq (I := I) (M := M) g 2 Y) ≤
        2 * (S ^ 2 + S ^ 2) :=
          mul_le_mul_of_nonneg_left (add_le_add hX hY) (by norm_num)
      _ = (2 * S) ^ 2 := by ring
  have hsplit :
      lieCorrectionZeroMixedConnectionDerivativeCoefficient (I := I) (M := M) g gT g T -
          lieCorrectionZeroMixedConnectionDerivativeCoefficient (I := I) (M := M) g gU g U =
        (2 : ℝ) • (X + Y) := by
    simp only [lieCorrectionZeroMixedConnectionDerivativeCoefficient, X, Y, σ1, σ2]
    module
  rw [hsplit, covariantJetNormSq_smul]
  norm_num
  calc
    4 * covariantJetNormSq (I := I) (M := M) g 2 (X + Y) ≤
        4 * (2 * S) ^ 2 := mul_le_mul_of_nonneg_left hsum (by norm_num)
    _ = (B R * (1 + A) * (D3 + D2 + A * D2 + N)) ^ 2 := by
      simp only [B, S]
      ring

end RicciDeTurckPairing
end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral
end

section

noncomputable section


open Bundle Manifold MeasureTheory Set Filter DifferentialGeometry.Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Sobolev (covariantJetNormSq
  covariantJetNormSq_reindexCoeffGen covariantJetNormSq_smul)
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Analysis.Sobolev.TensorHilbert
open DifferentialGeometry.Analysis.Sobolev (metricConnectionDifferenceLoweredCoefficient)
open DifferentialGeometry.Analysis.Spectral (ccOperatorFieldComp ccTensorToHs pureTrace)
open DifferentialGeometry.PDE.DeTurck.RicciLinearization
open DifferentialGeometry.Analysis.Spectral.DeTurck
open DifferentialGeometry.Analysis.Spectral.MetricRealization

private lemma le_square_one_add_vectorBundleDerivative (x : ℝ) :
    x ≤ (1 + x) ^ 2 := by
  nlinarith only [sq_nonneg x]

private lemma second_le_four_term_sum_vectorBundleDerivative
    (D3 D2 A N : ℝ) (hD3 : 0 ≤ D3) (hD2 : 0 ≤ D2)
    (hA : 0 ≤ A) (hN : 0 ≤ N) :
    D2 ≤ D3 + D2 + A * D2 + N := by
  nlinarith only [hD3, hN, mul_nonneg hA hD2]

private lemma first_le_four_term_sum_vectorBundleDerivative
    (D3 D2 A N : ℝ) (hD2 : 0 ≤ D2) (hA : 0 ≤ A) (hN : 0 ≤ N) :
    D3 ≤ D3 + D2 + A * D2 + N := by
  nlinarith only [hD2, hN, mul_nonneg hA hD2]

private lemma middle_le_four_term_sum_vectorBundleDerivative
    (D3 D2 A N : ℝ) (hD3 : 0 ≤ D3) (hN : 0 ≤ N) :
    D2 + A * D2 ≤ D3 + D2 + A * D2 + N := by
  linarith only [hD3, hN]

variable
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
      [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

namespace RicciDeTurckPairing

private theorem exists_lieCorrectionZeroVectorBundleMetricConnectionDifferenceTerm_pairing_second_order_bounds
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ SM DM : ℝ → ℝ,
      (∀ R : ℝ, 0 ≤ R → 0 ≤ SM R) ∧
      (∀ R : ℝ, 0 ≤ R → 0 ≤ DM R) ∧
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
        {δ : ℝ} (_hδ_le : δ ≤ 1 / 3) (_hδ0 : 0 ≤ δ)
        (_hδT : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) δ)
        (_hδU : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g U) δ)
        (R A D2 D3 D : ℝ),
        0 ≤ R → 0 ≤ A → 0 ≤ D2 → 0 ≤ D3 → 0 ≤ D →
        D3 ≤ D → D2 + A * D2 ≤ D →
        covariantJetNormSq (I := I) (M := M) g 2 T ≤ R ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 2 U ≤ R ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 3 T ≤ A ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 3 U ≤ A ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 2 (T - U) ≤ D2 ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 3 (T - U) ≤ D3 ^ 2 →
      covariantJetNormSq (I := I) (M := M) g 2
          (lieCorrectionZeroVectorBundleMetricConnectionDifferenceTerm (I := I) (M := M) g gT) ≤
          (SM R * (1 + A)) ^ 2 ∧
        covariantJetNormSq (I := I) (M := M) g 2
          (lieCorrectionZeroVectorBundleMetricConnectionDifferenceTerm (I := I) (M := M) g gU) ≤
          (SM R * (1 + A)) ^ 2 ∧
        covariantJetNormSq (I := I) (M := M) g 2
          (lieCorrectionZeroVectorBundleMetricConnectionDifferenceTerm (I := I) (M := M) g gT -
            lieCorrectionZeroVectorBundleMetricConnectionDifferenceTerm (I := I) (M := M) g gU) ≤
          (DM R * D) ^ 2 := by
  obtain ⟨B0m, B1m, hB0m, hB1m, hmcdp⟩ :=
    RicciDeTurckLowOrder.mcd_pair_h2 (I := I) (M := M) hDim g
      (δ₀ := (1 : ℝ) / 3) (by norm_num) (by norm_num)
  obtain ⟨Bm, hBm, hmcdb⟩ :=
    RicciDeTurckLowOrder.metric_connection_difference_coefficient_sobolev_two_bound (I := I) (M := M) hDim g
      (δ₀ := (1 : ℝ) / 3) (by norm_num) (by norm_num)
  let fr : ℝ := Module.finrank ℝ E
  let SM : ℝ → ℝ := fun R => (1 + fr) * Bm R
  let DM : ℝ → ℝ := fun R => (1 + fr) * (B0m R + B1m R)
  have hfr : 0 ≤ fr := Nat.cast_nonneg _
  have hSM : ∀ R : ℝ, 0 ≤ R → 0 ≤ SM R := fun R hR =>
    mul_nonneg (add_nonneg (by norm_num) hfr) (hBm R hR)
  have hDM : ∀ R : ℝ, 0 ≤ R → 0 ≤ DM R := fun R hR =>
    mul_nonneg (add_nonneg (by norm_num) hfr)
      (add_nonneg (hB0m R hR) (hB1m R hR))
  refine ⟨SM, DM, hSM, hDM, ?_⟩
  intro gT gU T U hT hU hTtie hUtie δ hδ_le hδ0 hδT hδU
    R A D2 D3 D hR hA hD2 hD3 hD hD3le hrestle
    hT2 hU2 hT3 hU3 hTU2 hTU3
  let M0 : ℝ := B0m R * D3 + B1m R * D2 + B1m R * A * D2
  have hM0 : 0 ≤ M0 := by
    dsimp only [M0]
    exact add_nonneg
      (add_nonneg (mul_nonneg (hB0m R hR) hD3)
        (mul_nonneg (hB1m R hR) hD2))
      (mul_nonneg (mul_nonneg (hB1m R hR) hA) hD2)
  have hM0le : M0 ≤ (B0m R + B1m R) * D := by
    calc
      M0 = B0m R * D3 + B1m R * (D2 + A * D2) := by
        simp only [M0]
        ring
      _ ≤ B0m R * D + B1m R * D :=
        add_le_add
          (mul_le_mul_of_nonneg_left hD3le (hB0m R hR))
          (mul_le_mul_of_nonneg_left hrestle (hB1m R hR))
      _ = (B0m R + B1m R) * D := by ring
  have hfr_le : fr ≤ (1 + fr) ^ 2 := le_square_one_add fr
  have hVmT : covariantJetNormSq (I := I) (M := M) g 2
      (lieCorrectionZeroVectorBundleMetricConnectionDifferenceTerm (I := I) (M := M) g gT) ≤
      (SM R * (1 + A)) ^ 2 := by
    have hm := hmcdb gT T hT hTtie hδ_le hδ0 hδT
      R A hR hA hT2 hT3
    calc
      covariantJetNormSq (I := I) (M := M) g 2
          (lieCorrectionZeroVectorBundleMetricConnectionDifferenceTerm (I := I) (M := M) g gT) ≤
          fr * covariantJetNormSq (I := I) (M := M) g 2
            (metricConnectionDifferenceLoweredCoefficient (I := I) (M := M) g gT g) := by
        simpa only [fr] using covariantJetNormSq_lieCorrectionZeroVectorBundleMetricConnectionDifferenceTerm_le (I := I) (M := M) g gT
      _ ≤ fr * (Bm R * (1 + A)) ^ 2 :=
        mul_le_mul_of_nonneg_left hm hfr
      _ ≤ (1 + fr) ^ 2 * (Bm R * (1 + A)) ^ 2 :=
        mul_le_mul_of_nonneg_right hfr_le (sq_nonneg _)
      _ = (SM R * (1 + A)) ^ 2 := by
        simp only [SM]
        ring
  have hVmU : covariantJetNormSq (I := I) (M := M) g 2
      (lieCorrectionZeroVectorBundleMetricConnectionDifferenceTerm (I := I) (M := M) g gU) ≤
      (SM R * (1 + A)) ^ 2 := by
    have hm := hmcdb gU U hU hUtie hδ_le hδ0 hδU
      R A hR hA hU2 hU3
    calc
      covariantJetNormSq (I := I) (M := M) g 2
          (lieCorrectionZeroVectorBundleMetricConnectionDifferenceTerm (I := I) (M := M) g gU) ≤
          fr * covariantJetNormSq (I := I) (M := M) g 2
            (metricConnectionDifferenceLoweredCoefficient (I := I) (M := M) g gU g) := by
        simpa only [fr] using covariantJetNormSq_lieCorrectionZeroVectorBundleMetricConnectionDifferenceTerm_le (I := I) (M := M) g gU
      _ ≤ fr * (Bm R * (1 + A)) ^ 2 :=
        mul_le_mul_of_nonneg_left hm hfr
      _ ≤ (1 + fr) ^ 2 * (Bm R * (1 + A)) ^ 2 :=
        mul_le_mul_of_nonneg_right hfr_le (sq_nonneg _)
      _ = (SM R * (1 + A)) ^ 2 := by
        simp only [SM]
        ring
  have hVmD : covariantJetNormSq (I := I) (M := M) g 2
      (lieCorrectionZeroVectorBundleMetricConnectionDifferenceTerm (I := I) (M := M) g gT -
        lieCorrectionZeroVectorBundleMetricConnectionDifferenceTerm (I := I) (M := M) g gU) ≤ (DM R * D) ^ 2 := by
    have hm := hmcdp gT gU T U hT hU hTtie hUtie
      hδ_le hδ0 hδT hδ_le hδ0 hδU
      R A D2 D3 hR hA hD2 hD3 hU2 hT3 hTU2 hTU3
    calc
      covariantJetNormSq (I := I) (M := M) g 2
          (lieCorrectionZeroVectorBundleMetricConnectionDifferenceTerm (I := I) (M := M) g gT -
            lieCorrectionZeroVectorBundleMetricConnectionDifferenceTerm (I := I) (M := M) g gU) ≤
          fr * covariantJetNormSq (I := I) (M := M) g 2
            (metricConnectionDifferenceLoweredCoefficient (I := I) (M := M) g gT g -
              metricConnectionDifferenceLoweredCoefficient (I := I) (M := M) g gU g) := by
        simpa only [fr] using covariantJetNormSq_lieCorrectionZeroVectorBundleMetricConnectionDifferenceTerm_sub_le (I := I) (M := M) g gT gU
      _ ≤ fr * M0 ^ 2 := by
        simpa only [M0] using mul_le_mul_of_nonneg_left hm hfr
      _ ≤ fr * ((B0m R + B1m R) * D) ^ 2 :=
        mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ hM0 hM0le 2) hfr
      _ ≤ (1 + fr) ^ 2 * ((B0m R + B1m R) * D) ^ 2 :=
        mul_le_mul_of_nonneg_right hfr_le (sq_nonneg _)
      _ = (DM R * D) ^ 2 := by
        simp only [DM]
        ring
  exact ⟨hVmT, hVmU, hVmD⟩

theorem exists_lieCorrectionZeroVectorBundleDerivativeCoefficient_pairing_secondOrder_bound
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ ρ : ℝ, ∃ B : ℝ → ℝ, 0 < ρ ∧
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
        {δ : ℝ} (_hδ_le : δ ≤ 1 / 3) (_hδ0 : 0 ≤ δ)
        (_hδT : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) δ)
        (_hδU : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g U) δ)
        (_hδZ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g
            (0 : SmoothCcTensor g 0 2)) δ),
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ ≤ ρ →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) U‖ ≤ ρ →
        ∀ (R A D2 D3 N : ℝ),
        0 ≤ R → 0 ≤ A → 0 ≤ D2 → 0 ≤ D3 → 0 ≤ N →
        covariantJetNormSq (I := I) (M := M) g 2 T ≤ R ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 2 U ≤ R ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 3 T ≤ A ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 3 U ≤ A ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 2 (T - U) ≤ D2 ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 3 (T - U) ≤ D3 ^ 2 →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) (T - U)‖ ≤ N →
      covariantJetNormSq (I := I) (M := M) g 2
          (lieCorrectionZeroVectorBundleDerivativeCoefficient (I := I) (M := M) g gT T -
            lieCorrectionZeroVectorBundleDerivativeCoefficient (I := I) (M := M) g gU U) ≤
        (B R * (1 + A) * (D3 + D2 + A * D2 + N)) ^ 2 := by
  obtain ⟨ρt1p, Ct1, hρt1p, hCt1, ht1p⟩ :=
    RicciDeTurckLowOrder.trace1_pair_h2 (I := I) (M := M) hDim g
  obtain ⟨ρt1b, Bt1, hρt1b, hBt1, ht1b⟩ :=
    RicciDeTurckLowOrder.trace_one_sobolev_two_bound (I := I) (M := M) hDim g
  obtain ⟨ρcp, Cc, hρcp, hCc, hcp⟩ :=
    RicciDeTurckLowOrder.connLow_pair_h2 (I := I) (M := M) hDim g
  obtain ⟨ρcb, Bc, hρcb, hBc, hcb⟩ :=
    RicciDeTurckLowOrder.low_connection_coefficient_sobolev_two_bound (I := I) (M := M) hDim g
  obtain ⟨ρt2p, Ct2, hρt2p, hCt2, ht2p⟩ :=
    RicciDeTurckLowOrder.trace2_pair_h2 (I := I) (M := M) hDim g
  obtain ⟨ρt2b, Bt2, hρt2b, hBt2, ht2b⟩ :=
    RicciDeTurckLowOrder.trace_two_sobolev_two_bound (I := I) (M := M) hDim g
  obtain ⟨SM, DM, hSM, hDM, hvm⟩ :=
    exists_lieCorrectionZeroVectorBundleMetricConnectionDifferenceTerm_pairing_second_order_bounds (I := I) (M := M) hDim g
  obtain ⟨C0, hC0, happ0⟩ :=
    exists_operatorFieldComposition_covariantJetNormSq_two_bound (I := I) (M := M) hDim g 3 3 1
  obtain ⟨P0, hP0, hpair0⟩ :=
    exists_operatorFieldComposition_difference_covariantJetNormSq_two_bound (I := I) (M := M) hDim g 3 3 1
  obtain ⟨C1, hC1, happ1⟩ :=
    exists_operatorFieldComposition_covariantJetNormSq_two_bound (I := I) (M := M) hDim g 3 1 1
  obtain ⟨P1, hP1, hpair1⟩ :=
    exists_operatorFieldComposition_difference_covariantJetNormSq_two_bound (I := I) (M := M) hDim g 3 1 1
  obtain ⟨C2, hC2, happ2⟩ :=
    exists_operatorFieldComposition_covariantJetNormSq_two_bound (I := I) (M := M) hDim g 3 1 4
  obtain ⟨P2, hP2, hpair2⟩ :=
    exists_operatorFieldComposition_difference_covariantJetNormSq_two_bound (I := I) (M := M) hDim g 3 1 4
  obtain ⟨C3, hC3, happ3⟩ :=
    exists_operatorFieldComposition_covariantJetNormSq_two_bound (I := I) (M := M) hDim g 3 4 2
  obtain ⟨P3, hP3, hpair3⟩ :=
    exists_operatorFieldComposition_difference_covariantJetNormSq_two_bound (I := I) (M := M) hDim g 3 4 2
  let ρ : ℝ :=
    min (min ρt1p ρt1b) (min (min ρcp ρcb) (min ρt2p ρt2b))
  let S0 : ℝ := C0 * Bt1 * Bc
  let D0 : ℝ := P0 * (Ct1 * Bc + Bt1 * Cc)
  let S1 : ℝ → ℝ := fun R => C1 * R * S0
  let D1 : ℝ → ℝ := fun R => P1 * (S0 + R * D0)
  let S2 : ℝ → ℝ := fun R => C2 * SM R * S1 R
  let D2c : ℝ → ℝ := fun R => P2 * (DM R * S1 R + SM R * D1 R)
  let D3c : ℝ → ℝ := fun R => P3 * (Ct2 * S2 R + Bt2 * D2c R)
  let B : ℝ → ℝ := fun R => 2 * D3c R
  have hρ : 0 < ρ :=
    lt_min (lt_min hρt1p hρt1b)
      (lt_min (lt_min hρcp hρcb) (lt_min hρt2p hρt2b))
  have hS0 : 0 ≤ S0 := mul_nonneg (mul_nonneg hC0 hBt1) hBc
  have hD0 : 0 ≤ D0 :=
    mul_nonneg hP0
      (add_nonneg (mul_nonneg hCt1 hBc) (mul_nonneg hBt1 hCc))
  have hS1 : ∀ R : ℝ, 0 ≤ R → 0 ≤ S1 R := fun R hR =>
    mul_nonneg (mul_nonneg hC1 hR) hS0
  have hD1 : ∀ R : ℝ, 0 ≤ R → 0 ≤ D1 R := fun R hR =>
    mul_nonneg hP1 (add_nonneg hS0 (mul_nonneg hR hD0))
  have hS2 : ∀ R : ℝ, 0 ≤ R → 0 ≤ S2 R := fun R hR =>
    mul_nonneg (mul_nonneg hC2 (hSM R hR)) (hS1 R hR)
  have hD2c : ∀ R : ℝ, 0 ≤ R → 0 ≤ D2c R := fun R hR =>
    mul_nonneg hP2
      (add_nonneg (mul_nonneg (hDM R hR) (hS1 R hR))
        (mul_nonneg (hSM R hR) (hD1 R hR)))
  have hD3c : ∀ R : ℝ, 0 ≤ R → 0 ≤ D3c R := fun R hR =>
    mul_nonneg hP3
      (add_nonneg (mul_nonneg hCt2 (hS2 R hR))
        (mul_nonneg hBt2 (hD2c R hR)))
  have hB : ∀ R : ℝ, 0 ≤ R → 0 ≤ B R := fun R hR =>
    mul_nonneg (by norm_num) (hD3c R hR)
  refine ⟨ρ, B, hρ, hB, ?_⟩
  intro gT gU T U hT hU hTtie hUtie δ hδ_le hδ0 hδT hδU hδZ
    hTn hUn R A D2 D3 N hR hA hD2 hD3 hN
    hT2 hU2 hT3 hU3 hTU2 hTU3 hTUn
  let D : ℝ := D3 + D2 + A * D2 + N
  have hD : 0 ≤ D :=
    add_nonneg (add_nonneg (add_nonneg hD3 hD2) (mul_nonneg hA hD2)) hN
  have h1A : 0 ≤ 1 + A := add_nonneg (by norm_num) hA
  have hNle : N ≤ D := by
    dsimp only [D]
    exact le_add_of_nonneg_left
      (add_nonneg (add_nonneg hD3 hD2) (mul_nonneg hA hD2))
  have hD2le : D2 ≤ D := by
    dsimp only [D]
    exact second_le_four_term_sum D3 D2 A N hD3 hD2 hA hN
  have hρt1p_le : ρ ≤ ρt1p :=
    (min_le_left _ _).trans (min_le_left _ _)
  have hρt1b_le : ρ ≤ ρt1b :=
    (min_le_left _ _).trans (min_le_right _ _)
  have hρcp_le : ρ ≤ ρcp :=
    (min_le_right _ _).trans ((min_le_left _ _).trans (min_le_left _ _))
  have hρcb_le : ρ ≤ ρcb :=
    (min_le_right _ _).trans ((min_le_left _ _).trans (min_le_right _ _))
  have hρt2p_le : ρ ≤ ρt2p :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hρt2b_le : ρ ≤ ρt2b :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  have hTt1p := hTn.trans hρt1p_le
  have hUt1p := hUn.trans hρt1p_le
  have hTt1b := hTn.trans hρt1b_le
  have hUt1b := hUn.trans hρt1b_le
  have hTcp := hTn.trans hρcp_le
  have hUcp := hUn.trans hρcp_le
  have hTcb := hTn.trans hρcb_le
  have hUcb := hUn.trans hρcb_le
  have hTt2p := hTn.trans hρt2p_le
  have hUt2p := hUn.trans hρt2p_le
  have hUt2b := hUn.trans hρt2b_le
  let TrT : SmoothCcTensor g 3 1 :=
    reindexedPureTrace (I := I) (M := M) g gT 1 (Equiv.refl _)
  let TrU : SmoothCcTensor g 3 1 :=
    reindexedPureTrace (I := I) (M := M) g gU 1 (Equiv.refl _)
  let CnT : SmoothCcTensor g 3 3 :=
    RicciDeTurckLowOrder.connectionDifferenceLowOrderOperator (I := I) (M := M) g gT
  let CnU : SmoothCcTensor g 3 3 :=
    RicciDeTurckLowOrder.connectionDifferenceLowOrderOperator (I := I) (M := M) g gU
  let Rt : SmoothCcTensor g 1 1 :=
    cometricRaiseSlot0Field (I := I) (M := M) g 0 T
  let Ru : SmoothCcTensor g 1 1 :=
    cometricRaiseSlot0Field (I := I) (M := M) g 0 U
  let VmT : SmoothCcTensor g 1 4 := lieCorrectionZeroVectorBundleMetricConnectionDifferenceTerm (I := I) (M := M) g gT
  let VmU : SmoothCcTensor g 1 4 := lieCorrectionZeroVectorBundleMetricConnectionDifferenceTerm (I := I) (M := M) g gU
  let LvT : SmoothCcTensor g 4 2 := reindexedCometricDoubleTrace (I := I) (M := M) g gT
  let LvU : SmoothCcTensor g 4 2 := reindexedCometricDoubleTrace (I := I) (M := M) g gU
  let Z0T : SmoothCcTensor g 3 1 :=
    ccOperatorFieldComp (I := I) (M := M) g 3 3 1 TrT CnT
  let Z0U : SmoothCcTensor g 3 1 :=
    ccOperatorFieldComp (I := I) (M := M) g 3 3 1 TrU CnU
  let Z1T : SmoothCcTensor g 3 1 :=
    ccOperatorFieldComp (I := I) (M := M) g 3 1 1 Rt Z0T
  let Z1U : SmoothCcTensor g 3 1 :=
    ccOperatorFieldComp (I := I) (M := M) g 3 1 1 Ru Z0U
  let Z2T : SmoothCcTensor g 3 4 :=
    ccOperatorFieldComp (I := I) (M := M) g 3 1 4 VmT Z1T
  let Z2U : SmoothCcTensor g 3 4 :=
    ccOperatorFieldComp (I := I) (M := M) g 3 1 4 VmU Z1U
  let Z3T : SmoothCcTensor g 3 2 :=
    ccOperatorFieldComp (I := I) (M := M) g 3 4 2 LvT Z2T
  let Z3U : SmoothCcTensor g 3 2 :=
    ccOperatorFieldComp (I := I) (M := M) g 3 4 2 LvU Z2U
  have hTrT : covariantJetNormSq (I := I) (M := M) g 2 TrT ≤ Bt1 ^ 2 := by
    dsimp only [TrT]
    rw [covariantJetNormSq_reindexedPureTrace]
    exact ht1b T gT hTtie hTt1b
  have hTrU : covariantJetNormSq (I := I) (M := M) g 2 TrU ≤ Bt1 ^ 2 := by
    dsimp only [TrU]
    rw [covariantJetNormSq_reindexedPureTrace]
    exact ht1b U gU hUtie hUt1b
  have hTrD : covariantJetNormSq (I := I) (M := M) g 2 (TrT - TrU) ≤
      (Ct1 * D) ^ 2 := by
    have hraw := ht1p T U gT gU hTtie hUtie hTt1p hUt1p
    have hmul : Ct1 * ‖ccTensorToHs (I := I) (M := M) g 2
        (2 : ℝ) (T - U)‖ ≤ Ct1 * D :=
      (mul_le_mul_of_nonneg_left hTUn hCt1).trans
        (mul_le_mul_of_nonneg_left hNle hCt1)
    calc
      covariantJetNormSq (I := I) (M := M) g 2 (TrT - TrU) =
          covariantJetNormSq (I := I) (M := M) g 2
            (pureTrace (I := I) (M := M) g gT 1 -
              pureTrace (I := I) (M := M) g gU 1) := by
        dsimp only [TrT, TrU]
        rw [reindexedPureTrace_sub, covariantJetNormSq_reindexCoeffGen]
      _ ≤ (Ct1 * ‖ccTensorToHs (I := I) (M := M) g 2
          (2 : ℝ) (T - U)‖) ^ 2 := hraw
      _ ≤ (Ct1 * D) ^ 2 :=
        pow_le_pow_left₀ (mul_nonneg hCt1 (norm_nonneg _)) hmul 2
  have hCnT : covariantJetNormSq (I := I) (M := M) g 2 CnT ≤ Bc ^ 2 := by
    simpa only [CnT] using hcb T gT hTtie hTcb
  have hCnU : covariantJetNormSq (I := I) (M := M) g 2 CnU ≤ Bc ^ 2 := by
    simpa only [CnU] using hcb U gU hUtie hUcb
  have hCnD : covariantJetNormSq (I := I) (M := M) g 2 (CnT - CnU) ≤
      (Cc * D) ^ 2 := by
    have hraw := hcp T U gT gU hTtie hUtie hTcp hUcp
    have hmul : Cc * ‖ccTensorToHs (I := I) (M := M) g 2
        (2 : ℝ) (T - U)‖ ≤ Cc * D :=
      (mul_le_mul_of_nonneg_left hTUn hCc).trans
        (mul_le_mul_of_nonneg_left hNle hCc)
    exact hraw.trans
      (pow_le_pow_left₀ (mul_nonneg hCc (norm_nonneg _)) hmul 2)
  have hRt : covariantJetNormSq (I := I) (M := M) g 2 Rt ≤ R ^ 2 := by
    simpa only [Rt, covariantJetNormSq_cometricRaiseSlot0Field] using hT2
  have hRu : covariantJetNormSq (I := I) (M := M) g 2 Ru ≤ R ^ 2 := by
    simpa only [Ru, covariantJetNormSq_cometricRaiseSlot0Field] using hU2
  have hRd : covariantJetNormSq (I := I) (M := M) g 2 (Rt - Ru) ≤ D ^ 2 := by
    calc
      covariantJetNormSq (I := I) (M := M) g 2 (Rt - Ru) =
          covariantJetNormSq (I := I) (M := M) g 2 (T - U) := by
        dsimp only [Rt, Ru]
        rw [← cometricRaiseSlot0Field_zero_sub, covariantJetNormSq_cometricRaiseSlot0Field]
      _ ≤ D2 ^ 2 := hTU2
      _ ≤ D ^ 2 := pow_le_pow_left₀ hD2 hD2le 2
  have hD3le : D3 ≤ D := by
    dsimp only [D]
    exact first_le_four_term_sum D3 D2 A N hD2 hA hN
  have hrestle : D2 + A * D2 ≤ D := by
    dsimp only [D]
    exact middle_le_four_term_sum D3 D2 A N hD3 hN
  obtain ⟨hVmT, hVmU, hVmD⟩ :=
    hvm gT gU T U hT hU hTtie hUtie hδ_le hδ0 hδT hδU
      R A D2 D3 D hR hA hD2 hD3 hD hD3le hrestle
      hT2 hU2 hT3 hU3 hTU2 hTU3
  have hLvU : covariantJetNormSq (I := I) (M := M) g 2 LvU ≤ Bt2 ^ 2 := by
    dsimp only [LvU]
    rw [reindexedCometricDoubleTrace_eq_pureTrace]
    exact ht2b U gU hUtie hUt2b
  have hLvD : covariantJetNormSq (I := I) (M := M) g 2 (LvT - LvU) ≤
      (Ct2 * D) ^ 2 := by
    have hraw := ht2p T U gT gU hTtie hUtie hTt2p hUt2p
    have hmul : Ct2 * ‖ccTensorToHs (I := I) (M := M) g 2
        (2 : ℝ) (T - U)‖ ≤ Ct2 * D :=
      (mul_le_mul_of_nonneg_left hTUn hCt2).trans
        (mul_le_mul_of_nonneg_left hNle hCt2)
    calc
      covariantJetNormSq (I := I) (M := M) g 2 (LvT - LvU) =
          covariantJetNormSq (I := I) (M := M) g 2
            (pureTrace (I := I) (M := M) g gT 2 -
              pureTrace (I := I) (M := M) g gU 2) := by
        dsimp only [LvT, LvU]
        rw [reindexedCometricDoubleTrace_eq_pureTrace, reindexedCometricDoubleTrace_eq_pureTrace]
      _ ≤ (Ct2 * ‖ccTensorToHs (I := I) (M := M) g 2
          (2 : ℝ) (T - U)‖) ^ 2 := hraw
      _ ≤ (Ct2 * D) ^ 2 :=
        pow_le_pow_left₀ (mul_nonneg hCt2 (norm_nonneg _)) hmul 2
  have hZ0T : covariantJetNormSq (I := I) (M := M) g 2 Z0T ≤ S0 ^ 2 := by
    simpa only [Z0T, S0] using
      happ0 TrT CnT Bt1 Bc hBt1 hBc hTrT hCnT
  have hZ0D : covariantJetNormSq (I := I) (M := M) g 2 (Z0T - Z0U) ≤
      (D0 * D) ^ 2 := by
    have hraw := hpair0 TrT TrU CnT CnU
      (Ct1 * D) Bt1 Bc (Cc * D)
      (mul_nonneg hCt1 hD) hBt1 hBc (mul_nonneg hCc hD)
      hTrD hTrU hCnT hCnD
    calc
      covariantJetNormSq (I := I) (M := M) g 2 (Z0T - Z0U) ≤
          (P0 * ((Ct1 * D) * Bc + Bt1 * (Cc * D))) ^ 2 := by
        simpa only [Z0T, Z0U] using hraw
      _ = (D0 * D) ^ 2 := by
        apply congrArg (fun x : ℝ => x ^ 2)
        simp only [D0]
        ring
  have hZ1T : covariantJetNormSq (I := I) (M := M) g 2 Z1T ≤ (S1 R) ^ 2 := by
    simpa only [Z1T, S1] using
      happ1 Rt Z0T R S0 hR hS0 hRt hZ0T
  have hZ1D : covariantJetNormSq (I := I) (M := M) g 2 (Z1T - Z1U) ≤
      (D1 R * D) ^ 2 := by
    have hraw := hpair1 Rt Ru Z0T Z0U D R S0 (D0 * D)
      hD hR hS0 (mul_nonneg hD0 hD) hRd hRu hZ0T hZ0D
    calc
      covariantJetNormSq (I := I) (M := M) g 2 (Z1T - Z1U) ≤
          (P1 * (D * S0 + R * (D0 * D))) ^ 2 := by
        simpa only [Z1T, Z1U] using hraw
      _ = (D1 R * D) ^ 2 := by
        apply congrArg (fun x : ℝ => x ^ 2)
        simp only [D1]
        ring
  have hZ2T : covariantJetNormSq (I := I) (M := M) g 2 Z2T ≤
      (S2 R * (1 + A)) ^ 2 := by
    have hraw := happ2 VmT Z1T (SM R * (1 + A)) (S1 R)
      (mul_nonneg (hSM R hR) h1A) (hS1 R hR) hVmT hZ1T
    calc
      covariantJetNormSq (I := I) (M := M) g 2 Z2T ≤
          (C2 * (SM R * (1 + A)) * S1 R) ^ 2 := by
        simpa only [Z2T] using hraw
      _ = (S2 R * (1 + A)) ^ 2 := by
        apply congrArg (fun x : ℝ => x ^ 2)
        simp only [S2]
        ring
  have hZ2D : covariantJetNormSq (I := I) (M := M) g 2 (Z2T - Z2U) ≤
      (D2c R * (1 + A) * D) ^ 2 := by
    let u : ℝ := P2 *
      ((DM R * D) * S1 R + (SM R * (1 + A)) * (D1 R * D))
    let v : ℝ := D2c R * (1 + A) * D
    have hu : 0 ≤ u := by
      dsimp only [u]
      exact mul_nonneg hP2
        (add_nonneg (mul_nonneg (mul_nonneg (hDM R hR) hD) (hS1 R hR))
          (mul_nonneg (mul_nonneg (hSM R hR) h1A)
            (mul_nonneg (hD1 R hR) hD)))
    have huv : u ≤ v := by
      have hfirst : DM R * S1 R * D ≤ DM R * S1 R * (1 + A) * D := by
        have hbase : DM R * S1 R ≤ DM R * S1 R * (1 + A) := by
          calc
            DM R * S1 R = DM R * S1 R * 1 := by ring
            _ ≤ DM R * S1 R * (1 + A) :=
              mul_le_mul_of_nonneg_left
                (le_add_of_nonneg_right hA)
                (mul_nonneg (hDM R hR) (hS1 R hR))
        exact mul_le_mul_of_nonneg_right hbase hD
      calc
        u = P2 * (DM R * S1 R * D + SM R * D1 R * (1 + A) * D) := by
          simp only [u]
          ring
        _ ≤ P2 * (DM R * S1 R * (1 + A) * D +
            SM R * D1 R * (1 + A) * D) :=
          mul_le_mul_of_nonneg_left (add_le_add hfirst le_rfl) hP2
        _ = v := by simp only [v, D2c]; ring
    have hraw := hpair2 VmT VmU Z1T Z1U
      (DM R * D) (SM R * (1 + A)) (S1 R) (D1 R * D)
      (mul_nonneg (hDM R hR) hD) (mul_nonneg (hSM R hR) h1A)
      (hS1 R hR) (mul_nonneg (hD1 R hR) hD)
      hVmD hVmU hZ1T hZ1D
    calc
      covariantJetNormSq (I := I) (M := M) g 2 (Z2T - Z2U) ≤ u ^ 2 := by
        simpa only [Z2T, Z2U, u] using hraw
      _ ≤ v ^ 2 := pow_le_pow_left₀ hu huv 2
      _ = (D2c R * (1 + A) * D) ^ 2 := rfl
  have hZ3D : covariantJetNormSq (I := I) (M := M) g 2 (Z3T - Z3U) ≤
      (D3c R * (1 + A) * D) ^ 2 := by
    have hraw := hpair3 LvT LvU Z2T Z2U
      (Ct2 * D) Bt2 (S2 R * (1 + A)) (D2c R * (1 + A) * D)
      (mul_nonneg hCt2 hD) hBt2 (mul_nonneg (hS2 R hR) h1A)
      (mul_nonneg (mul_nonneg (hD2c R hR) h1A) hD)
      hLvD hLvU hZ2T hZ2D
    calc
      covariantJetNormSq (I := I) (M := M) g 2 (Z3T - Z3U) ≤
          (P3 * ((Ct2 * D) * (S2 R * (1 + A)) +
            Bt2 * (D2c R * (1 + A) * D))) ^ 2 := by
        simpa only [Z3T, Z3U] using hraw
      _ = (D3c R * (1 + A) * D) ^ 2 := by
        apply congrArg (fun x : ℝ => x ^ 2)
        simp only [D3c]
        ring
  have hcoreT : lieCorrectionZeroVectorBundleUnscaledDerivativeCoefficient (I := I) (M := M) g gT T = Z3T := by rfl
  have hcoreU : lieCorrectionZeroVectorBundleUnscaledDerivativeCoefficient (I := I) (M := M) g gU U = Z3U := by rfl
  have hvb :
      lieCorrectionZeroVectorBundleDerivativeCoefficient (I := I) (M := M) g gT T -
          lieCorrectionZeroVectorBundleDerivativeCoefficient (I := I) (M := M) g gU U =
        (2 : ℝ) • (Z3T - Z3U) := by
    simp only [lieCorrectionZeroVectorBundleDerivativeCoefficient, hcoreT, hcoreU]
    module
  rw [hvb, covariantJetNormSq_smul]
  norm_num
  calc
    4 * covariantJetNormSq (I := I) (M := M) g 2 (Z3T - Z3U) ≤
        4 * (D3c R * (1 + A) * D) ^ 2 :=
      mul_le_mul_of_nonneg_left hZ3D (by norm_num)
    _ = (B R * (1 + A) * (D3 + D2 + A * D2 + N)) ^ 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, ← mul_pow]
      apply congrArg (fun x : ℝ => x ^ 2)
      simp only [B, D]
      ring

end RicciDeTurckPairing
end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral
end
end
end
end
end
end
end
