import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Fields.Convergence

import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Fields.SourceEstimates
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Limits.Equation
import DifferentialGeometry.Geometry.Metric.Convergence.Curvature.RicciFromJets
import DifferentialGeometry.Geometry.Metric.Convergence.CovariantDerivative.Norm.Continuity
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.Geometry.Curvature

set_option autoImplicit false

noncomputable section

open Set Bundle Manifold TopologicalSpace DifferentialGeometry.Tensor0SBundle
open scoped Manifold Topology ContDiff

open DifferentialGeometry.PDE.RicciFlow (metric_derivWithin_eq_neg_two_ricci)

namespace DifferentialGeometry
namespace CheegerGromovCompactness

private theorem function_le_max_zero_one_two
    (C : Nat → Real) {a : Nat} (ha : a ≤ 2) :
    C a ≤ max (C 0) (max (C 1) (C 2)) := by
  interval_cases a <;> simp only [le_max_iff] <;> aesop

private theorem le_max_zero_add_one_of_le_add
    {target err source Cmax : Real}
    (htri : target ≤ source + err) (herr : err < 1)
    (hsource : source ≤ Cmax) :
    target ≤ max 0 (Cmax + 1) := by
  calc
    target ≤ source + err := htri
    _ ≤ Cmax + 1 := add_le_add hsource herr.le
    _ ≤ max 0 (Cmax + 1) := le_max_right _ _

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]

variable {X : PointedFlowSeq (I := I)}
variable {P : PointedRiemannianManifold (I := I)}
variable {subseq : Nat → Nat}
variable (Φ : PointedCGHMaps (I := I) X P subseq)

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
private theorem ricNorm_restrict
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [T2Space M]
    [BoundarylessManifold I M] [IsManifold I 1 M]
    (g : SmoothRiemannianMetric I M) (U : TopologicalSpace.Opens M)
    [SigmaCompactSpace U] [T2Space U] [BoundarylessManifold I U]
    [IsManifold I 1 U]
    (x : U) :
    normSq0S (I := I) (g.restrictOpen (I := I) U) x 2
        (metricRicci (I := I) (g.restrictOpen (I := I) U) x) =
      normSq0S (I := I) g (x : M) 2 (metricRicci (I := I) g (x : M)) := by
  have hsec :
      metricRicci (I := I) (g.restrictOpen (I := I) U) x =
        metricRicci (I := I) g (x : M) := by
    ext slots
    have h := metricRicci_restrictOpen_eval (I := I) g U x slots
    have hslots :
        (fun q => mfderiv I I (Subtype.val : U → M) x (slots q)) =
          (fun q => (show TangentSpace I (x : M) from slots q)) := by
      funext q
      rw [mfderiv_subtype_val_apply]
    rw [hslots] at h
    change metricRicci (I := I) (g.restrictOpen (I := I) U) x slots =
      metricRicci (I := I) g (x : M)
        (fun q => (show TangentSpace I (x : M) from slots q))
    exact h
  rw [normSq0S_restrictOpen_apply (I := I) g U 2 x, hsec]

omit [NeZero (Module.finrank ℝ E)] in
theorem gSeqExt_ricci
    (R : letI : TopologicalSpace P.M := P.topology
      letI : ChartedSpace H P.M := P.charted
      letI : IsManifold I ∞ P.M := P.smooth
      SmoothRiemannianMetric I P.M)
    (bf : BumpFamily (I := I) Φ) (hsrc : SourceIsSigmaCompact Φ) (htgt : TargetIsSigmaCompact Φ)
    (k : Nat) (t : Real) (x : P.M)
    (hx : letI : TopologicalSpace P.M := P.topology; x ∈ bf.grow k)
    (v w : letI : TopologicalSpace P.M := P.topology
      letI : ChartedSpace H P.M := P.charted
      TangentSpace I x) :
    letI : TopologicalSpace P.M := P.topology
    letI : ChartedSpace H P.M := P.charted
    letI : T2Space P.M := P.t2
    letI : IsManifold I ∞ P.M := P.smooth
    letI : SigmaCompactSpace P.M := P.sigmaCompact
    letI : TopologicalSpace (SourceDomain (I := I) Φ k) := sourceDomTop (I := I) Φ k
    letI : ChartedSpace H (SourceDomain (I := I) Φ k) := sourceDomCharted (I := I) Φ k
    letI : T2Space (SourceDomain (I := I) Φ k) := sourceDomT2 (I := I) Φ k
    letI : IsManifold I ∞ (SourceDomain (I := I) Φ k) := sourceDomSmooth (I := I) Φ k
    letI : SigmaCompactSpace (SourceDomain (I := I) Φ k) :=
      sourceDomSigmaOf (I := I) Φ k (hsrc k)
    ricciTensor (I := I) (gSeqExt (I := I) Φ R bf hsrc htgt k t) x v w =
      ricciTensor (I := I) (sourceMetric (I := I) Φ hsrc htgt k t)
        ⟨x, bf.grow_subset k hx⟩ v w := by
  classical
  let : TopologicalSpace P.M := P.topology
  let : ChartedSpace H P.M := P.charted
  let : T2Space P.M := P.t2
  let : IsManifold I ∞ P.M := P.smooth
  let : SigmaCompactSpace P.M := P.sigmaCompact
  let : TopologicalSpace (SourceDomain (I := I) Φ k) := sourceDomTop (I := I) Φ k
  let : ChartedSpace H (SourceDomain (I := I) Φ k) := sourceDomCharted (I := I) Φ k
  let : T2Space (SourceDomain (I := I) Φ k) := sourceDomT2 (I := I) Φ k
  let : IsManifold I ∞ (SourceDomain (I := I) Φ k) := sourceDomSmooth (I := I) Φ k
  let : SigmaCompactSpace (SourceDomain (I := I) Φ k) :=
    sourceDomSigmaOf (I := I) Φ k (hsrc k)
  let : IsManifold I 1 (SourceDomain (I := I) Φ k) :=
    IsManifold.of_le (I := I) (M := SourceDomain (I := I) Φ k)
      (n := (∞ : WithTop ℕ∞)) (by decide)
  let : IsManifold I 2 (SourceDomain (I := I) Φ k) :=
    IsManifold.of_le (I := I) (M := SourceDomain (I := I) Φ k)
      (n := (∞ : WithTop ℕ∞)) (by decide)
  let : IsManifold I ((∞ : WithTop ℕ∞) + 1) (SourceDomain (I := I) Φ k) := by
    change IsManifold I ∞ (SourceDomain (I := I) Φ k)
    infer_instance
  obtain ⟨W, hWopen, hgrowW, hW1⟩ := bf.chi_one k
  let O : TopologicalSpace.Opens (SourceDomain (I := I) Φ k) :=
    ⟨Subtype.val ⁻¹' W, hWopen.preimage continuous_subtype_val⟩
  let : ChartedSpace H ↥O :=
    TopologicalSpace.Opens.instChartedSpace
      (H := H) (M := SourceDomain (I := I) Φ k) (s := O)
  let : IsManifold I ∞ ↥O := { O.instHasGroupoid (contDiffGroupoid ∞ I) with }
  let : SigmaCompactSpace ↥O := isSigmaCompact_iff_sigmaCompactSpace.mp
    (Geometry.isSigmaCompact_of_isOpen I O.isOpen)
  let : T2Space ↥O := inferInstance
  let : IsManifold I 1 ↥O :=
    IsManifold.of_le (I := I) (M := ↥O) (n := (∞ : WithTop ℕ∞)) (by decide)
  let : IsManifold I 2 ↥O :=
    IsManifold.of_le (I := I) (M := ↥O) (n := (∞ : WithTop ℕ∞)) (by decide)
  let : IsManifold I ((∞ : WithTop ℕ∞) + 1) ↥O := by
    change IsManifold I ∞ ↥O
    infer_instance
  let xsrc : SourceDomain (I := I) Φ k := ⟨x, bf.grow_subset k hx⟩
  have hxO : xsrc ∈ O := hgrowW hx
  have hres :
      (sourceMetric (I := I) Φ hsrc htgt k t).restrictOpen (I := I) O =
        (sourceMetricRestriction (I := I) Φ (k := k)
          (gSeqExt (I := I) Φ R bf hsrc htgt k t)).restrictOpen (I := I) O := by
    apply smoothRiemannianMetric_eq_of_inner (I := I)
    funext y
    ext a b
    rw [SmoothRiemannianMetric.restrictOpen_inner,
      SmoothRiemannianMetric.restrictOpen_inner]
    change (sourceMetric (I := I) Φ hsrc htgt k t).inner
        (y : SourceDomain (I := I) Φ k)
        (show TangentSpace I (y : SourceDomain (I := I) Φ k) from a)
        (show TangentSpace I (y : SourceDomain (I := I) Φ k) from b) =
      (sourceMetricRestriction (I := I) Φ (k := k) (gSeqExt (I := I) Φ R bf hsrc htgt k t)).inner
        (y : SourceDomain (I := I) Φ k)
        (show TangentSpace I (y : SourceDomain (I := I) Φ k) from a)
        (show TangentSpace I (y : SourceDomain (I := I) Φ k) from b)
    rw [resSource_inner (I := I) Φ k]
    change (sourceMetric (I := I) Φ hsrc htgt k t).inner
        (y : SourceDomain (I := I) Φ k)
        (show TangentSpace I (y : SourceDomain (I := I) Φ k) from a)
        (show TangentSpace I (y : SourceDomain (I := I) Φ k) from b) =
      (gSeqExt (I := I) Φ R bf hsrc htgt k t).inner
        (((y : SourceDomain (I := I) Φ k) : P.M))
        (show TangentSpace I (((y : SourceDomain (I := I) Φ k) : P.M)) from a)
        (show TangentSpace I (((y : SourceDomain (I := I) Φ k) : P.M)) from b)
    rw [gSeqExt_inner_of_mem (I := I) Φ R bf hsrc htgt k t
      ((y : SourceDomain (I := I) Φ k) : P.M)
      (y : SourceDomain (I := I) Φ k).2
      (show TangentSpace I (((y : SourceDomain (I := I) Φ k) : P.M)) from a)
      (show TangentSpace I (((y : SourceDomain (I := I) Φ k) : P.M)) from b)]
    rw [hW1 _ y.2]
    simp
  have hricSource :
      ricciTensor (I := I) (sourceMetric (I := I) Φ hsrc htgt k t) xsrc
          (show TangentSpace I xsrc from v) (show TangentSpace I xsrc from w) =
        ricciTensor (I := I)
          (sourceMetricRestriction (I := I) Φ (k := k) (gSeqExt (I := I) Φ R bf hsrc htgt k t))
          xsrc (show TangentSpace I xsrc from v) (show TangentSpace I xsrc from w) := by
    let xO : O := ⟨xsrc, hxO⟩
    let vO : TangentSpace I xO := show E from v
    let wO : TangentSpace I xO := show E from w
    have hvO : mfderiv I I (Subtype.val : O → SourceDomain (I := I) Φ k) xO vO =
        (show TangentSpace I xsrc from v) := by
      rw [mfderiv_subtype_val_apply]
    have hwO : mfderiv I I (Subtype.val : O → SourceDomain (I := I) Φ k) xO wO =
        (show TangentSpace I xsrc from w) := by
      rw [mfderiv_subtype_val_apply]
    change ricciTensor (I := I) (sourceMetric (I := I) Φ hsrc htgt k t) xsrc
        (show TangentSpace I xsrc from v) (show TangentSpace I xsrc from w) =
      ricciTensor (I := I)
        (sourceMetricRestriction (I := I) Φ (k := k) (gSeqExt (I := I) Φ R bf hsrc htgt k t)) xsrc
        (show TangentSpace I xsrc from v) (show TangentSpace I xsrc from w)
    calc
      _ = ricciTensor (I := I)
          ((sourceMetric (I := I) Φ hsrc htgt k t).restrictOpen (I := I) O)
          xO vO wO := by
        rw [ricciTensor_restrictOpen, hvO, hwO]
      _ = ricciTensor (I := I)
          ((sourceMetricRestriction (I := I) Φ (k := k)
            (gSeqExt (I := I) Φ R bf hsrc htgt k t)).restrictOpen (I := I) O)
          xO vO wO := by rw [hres]
      _ = _ := by
        rw [ricciTensor_restrictOpen, hvO, hwO]
  let sourceTopInst : TopologicalSpace ↥(sourceOpen (I := I) Φ k) :=
    sourceDomTop (I := I) Φ k
  let sourceChartedInst : ChartedSpace H ↥(sourceOpen (I := I) Φ k) :=
    sourceDomCharted (I := I) Φ k
  let sourceSmoothInst : IsManifold I ∞ ↥(sourceOpen (I := I) Φ k) :=
    sourceDomSmooth (I := I) Φ k
  let sourceSigma : SigmaCompactSpace ↥(sourceOpen (I := I) Φ k) := by
    change SigmaCompactSpace (SourceDomain (I := I) Φ k)
    exact sourceDomSigmaOf (I := I) Φ k (hsrc k)
  let sourceT2 : T2Space ↥(sourceOpen (I := I) Φ k) := by
    change T2Space (SourceDomain (I := I) Φ k)
    exact sourceDomT2 (I := I) Φ k
  have sourceSigmaInst : SigmaCompactSpace ↥(sourceOpen (I := I) Φ k) := sourceSigma
  have sourceT2Inst : T2Space ↥(sourceOpen (I := I) Φ k) := sourceT2
  have hricAmbient :
      ricciTensor (I := I)
          (sourceMetricRestriction (I := I) Φ (k := k) (gSeqExt (I := I) Φ R bf hsrc htgt k t)) xsrc
          (show TangentSpace I xsrc from v) (show TangentSpace I xsrc from w) =
        ricciTensor (I := I) (gSeqExt (I := I) Φ R bf hsrc htgt k t) x v w := by
    have h :=
      @ricciTensor_restrictOpen E _ _ _ _ H _ I P.M
        P.topology P.charted P.smooth P.t2
        (by infer_instance) (by infer_instance)
        (gSeqExt (I := I) Φ R bf hsrc htgt k t) (sourceOpen (I := I) Φ k)
        sourceSigma sourceT2 (by infer_instance) (by infer_instance) xsrc
        (show TangentSpace I xsrc from v) (show TangentSpace I xsrc from w)
    rw [mfderiv_subtype_val_apply, mfderiv_subtype_val_apply] at h
    exact h
  change ricciTensor (I := I) (gSeqExt (I := I) Φ R bf hsrc htgt k t) x v w =
    ricciTensor (I := I) (sourceMetric (I := I) Φ hsrc htgt k t) xsrc
      (show TangentSpace I xsrc from v) (show TangentSpace I xsrc from w)
  exact hricAmbient.symm.trans hricSource.symm

omit [NeZero (Module.finrank ℝ E)] in
theorem gSeqExt_scalar
    (R : letI : TopologicalSpace P.M := P.topology
      letI : ChartedSpace H P.M := P.charted
      letI : IsManifold I ∞ P.M := P.smooth
      SmoothRiemannianMetric I P.M)
    (bf : BumpFamily (I := I) Φ) (hsrc : SourceIsSigmaCompact Φ) (htgt : TargetIsSigmaCompact Φ)
    (k : Nat) (t : Real) (x : P.M)
    (hx : letI : TopologicalSpace P.M := P.topology; x ∈ bf.grow k) :
    letI : TopologicalSpace P.M := P.topology
    letI : ChartedSpace H P.M := P.charted
    letI : T2Space P.M := P.t2
    letI : IsManifold I ∞ P.M := P.smooth
    letI : SigmaCompactSpace P.M := P.sigmaCompact
    letI : TopologicalSpace (X.term (subseq k)).M := (X.term (subseq k)).topology
    letI : ChartedSpace H (X.term (subseq k)).M := (X.term (subseq k)).charted
    letI : T2Space (X.term (subseq k)).M := (X.term (subseq k)).t2
    letI : IsManifold I ∞ (X.term (subseq k)).M := (X.term (subseq k)).smooth
    letI : SigmaCompactSpace (X.term (subseq k)).M := (X.term (subseq k)).sigmaCompact
    metricScalarAt (I := I) (gSeqExt (I := I) Φ R bf hsrc htgt k t) x =
      (X.term (subseq k)).S.scalar t (Φ.map k x) := by
  classical
  let : TopologicalSpace P.M := P.topology
  let : ChartedSpace H P.M := P.charted
  let : T2Space P.M := P.t2
  let : IsManifold I ∞ P.M := P.smooth
  let : SigmaCompactSpace P.M := P.sigmaCompact
  let : TopologicalSpace (X.term (subseq k)).M := (X.term (subseq k)).topology
  let : ChartedSpace H (X.term (subseq k)).M := (X.term (subseq k)).charted
  let : T2Space (X.term (subseq k)).M := (X.term (subseq k)).t2
  let : IsManifold I ∞ (X.term (subseq k)).M := (X.term (subseq k)).smooth
  let : SigmaCompactSpace (X.term (subseq k)).M := (X.term (subseq k)).sigmaCompact
  let : IsManifold I 1 (X.term (subseq k)).M :=
    IsManifold.of_le (I := I) (M := (X.term (subseq k)).M)
      (n := (∞ : WithTop ℕ∞)) (by decide)
  let : IsManifold I 2 (X.term (subseq k)).M :=
    IsManifold.of_le (I := I) (M := (X.term (subseq k)).M)
      (n := (∞ : WithTop ℕ∞)) (by decide)
  let : IsManifold I ((∞ : WithTop ℕ∞) + 1) (X.term (subseq k)).M := by
    change IsManifold I ∞ (X.term (subseq k)).M
    infer_instance
  let : TopologicalSpace (SourceDomain (I := I) Φ k) := sourceDomTop (I := I) Φ k
  let : ChartedSpace H (SourceDomain (I := I) Φ k) := sourceDomCharted (I := I) Φ k
  let : T2Space (SourceDomain (I := I) Φ k) := sourceDomT2 (I := I) Φ k
  let : IsManifold I ∞ (SourceDomain (I := I) Φ k) := sourceDomSmooth (I := I) Φ k
  let : SigmaCompactSpace (SourceDomain (I := I) Φ k) :=
    sourceDomSigmaOf (I := I) Φ k (hsrc k)
  let : IsManifold I 1 (SourceDomain (I := I) Φ k) :=
    IsManifold.of_le (I := I) (M := SourceDomain (I := I) Φ k)
      (n := (∞ : WithTop ℕ∞)) (by decide)
  let : IsManifold I 2 (SourceDomain (I := I) Φ k) :=
    IsManifold.of_le (I := I) (M := SourceDomain (I := I) Φ k)
      (n := (∞ : WithTop ℕ∞)) (by decide)
  let : IsManifold I ((∞ : WithTop ℕ∞) + 1) (SourceDomain (I := I) Φ k) := by
    change IsManifold I ∞ (SourceDomain (I := I) Φ k)
    infer_instance
  let : SigmaCompactSpace ↑(targetOpen (I := I) Φ k) :=
    targetDomSigmaOf (I := I) Φ k (htgt k)
  let : T2Space ↑(targetOpen (I := I) Φ k) := targetDomT2 (I := I) Φ k
  let : IsManifold I 1 ↑(targetOpen (I := I) Φ k) :=
    IsManifold.of_le (I := I) (M := ↑(targetOpen (I := I) Φ k))
      (n := (∞ : WithTop ℕ∞)) (by decide)
  let : IsManifold I ((∞ : WithTop ℕ∞) + 1) ↑(targetOpen (I := I) Φ k) := by
    change IsManifold I ∞ ↑(targetOpen (I := I) Φ k)
    infer_instance
  let : TopologicalSpace (TargetDomain (I := I) Φ k) := targetDomTop (I := I) Φ k
  let : ChartedSpace H (TargetDomain (I := I) Φ k) := targetDomCharted (I := I) Φ k
  let : T2Space (TargetDomain (I := I) Φ k) := targetDomT2 (I := I) Φ k
  let : IsManifold I ∞ (TargetDomain (I := I) Φ k) := targetDomSmooth (I := I) Φ k
  let : SigmaCompactSpace (TargetDomain (I := I) Φ k) :=
    targetDomSigmaOf (I := I) Φ k (htgt k)
  let : IsManifold I 1 (TargetDomain (I := I) Φ k) :=
    IsManifold.of_le (I := I) (M := TargetDomain (I := I) Φ k)
      (n := (∞ : WithTop ℕ∞)) (by decide)
  let : IsManifold I 2 (TargetDomain (I := I) Φ k) :=
    IsManifold.of_le (I := I) (M := TargetDomain (I := I) Φ k)
      (n := (∞ : WithTop ℕ∞)) (by decide)
  let : IsManifold I ((∞ : WithTop ℕ∞) + 1) (TargetDomain (I := I) Φ k) := by
    change IsManifold I ∞ (TargetDomain (I := I) Φ k)
    infer_instance
  obtain ⟨W, hWopen, hgrowW, hW1⟩ := bf.chi_one k
  let O : TopologicalSpace.Opens (SourceDomain (I := I) Φ k) :=
    ⟨Subtype.val ⁻¹' W, hWopen.preimage continuous_subtype_val⟩
  let : ChartedSpace H ↑O :=
    TopologicalSpace.Opens.instChartedSpace
      (H := H) (M := SourceDomain (I := I) Φ k) (s := O)
  let : IsManifold I ∞ ↑O := { O.instHasGroupoid (contDiffGroupoid ∞ I) with }
  let : SigmaCompactSpace ↑O := isSigmaCompact_iff_sigmaCompactSpace.mp
    (Geometry.isSigmaCompact_of_isOpen I O.isOpen)
  let : T2Space ↑O := inferInstance
  let : IsManifold I 1 ↑O :=
    IsManifold.of_le (I := I) (M := ↑O) (n := (∞ : WithTop ℕ∞)) (by decide)
  let : IsManifold I 2 ↑O :=
    IsManifold.of_le (I := I) (M := ↑O) (n := (∞ : WithTop ℕ∞)) (by decide)
  let : IsManifold I ((∞ : WithTop ℕ∞) + 1) ↑O := by
    change IsManifold I ∞ ↑O
    infer_instance
  let xsrc : SourceDomain (I := I) Φ k := ⟨x, bf.grow_subset k hx⟩
  have hxO : xsrc ∈ O := hgrowW hx
  have hres :
      (sourceMetric (I := I) Φ hsrc htgt k t).restrictOpen (I := I) O =
        (sourceMetricRestriction (I := I) Φ (k := k)
          (gSeqExt (I := I) Φ R bf hsrc htgt k t)).restrictOpen (I := I) O := by
    apply smoothRiemannianMetric_eq_of_inner (I := I)
    funext y
    ext a b
    rw [SmoothRiemannianMetric.restrictOpen_inner,
      SmoothRiemannianMetric.restrictOpen_inner]
    change (sourceMetric (I := I) Φ hsrc htgt k t).inner
        (y : SourceDomain (I := I) Φ k)
        (show TangentSpace I (y : SourceDomain (I := I) Φ k) from a)
        (show TangentSpace I (y : SourceDomain (I := I) Φ k) from b) =
      (sourceMetricRestriction (I := I) Φ (k := k) (gSeqExt (I := I) Φ R bf hsrc htgt k t)).inner
        (y : SourceDomain (I := I) Φ k)
        (show TangentSpace I (y : SourceDomain (I := I) Φ k) from a)
        (show TangentSpace I (y : SourceDomain (I := I) Φ k) from b)
    rw [resSource_inner (I := I) Φ k]
    change (sourceMetric (I := I) Φ hsrc htgt k t).inner
        (y : SourceDomain (I := I) Φ k)
        (show TangentSpace I (y : SourceDomain (I := I) Φ k) from a)
        (show TangentSpace I (y : SourceDomain (I := I) Φ k) from b) =
      (gSeqExt (I := I) Φ R bf hsrc htgt k t).inner
        (((y : SourceDomain (I := I) Φ k) : P.M))
        (show TangentSpace I (((y : SourceDomain (I := I) Φ k) : P.M)) from a)
        (show TangentSpace I (((y : SourceDomain (I := I) Φ k) : P.M)) from b)
    rw [gSeqExt_inner_of_mem (I := I) Φ R bf hsrc htgt k t
      ((y : SourceDomain (I := I) Φ k) : P.M)
      (y : SourceDomain (I := I) Φ k).2
      (show TangentSpace I (((y : SourceDomain (I := I) Φ k) : P.M)) from a)
      (show TangentSpace I (((y : SourceDomain (I := I) Φ k) : P.M)) from b)]
    rw [hW1 _ y.2]
    simp
  have hscalarSource :
      metricScalarAt (I := I) (sourceMetric (I := I) Φ hsrc htgt k t) xsrc =
        metricScalarAt (I := I)
          (sourceMetricRestriction (I := I) Φ (k := k) (gSeqExt (I := I) Φ R bf hsrc htgt k t)) xsrc := by
    rw [← metricScalarAt_restrictOpen (I := I)
        (sourceMetric (I := I) Φ hsrc htgt k t) O ⟨xsrc, hxO⟩,
      ← metricScalarAt_restrictOpen (I := I)
        (sourceMetricRestriction (I := I) Φ (k := k) (gSeqExt (I := I) Φ R bf hsrc htgt k t))
        O ⟨xsrc, hxO⟩,
      hres]
  let sourceTopInst : TopologicalSpace ↑(sourceOpen (I := I) Φ k) :=
    sourceDomTop (I := I) Φ k
  let sourceChartedInst : ChartedSpace H ↑(sourceOpen (I := I) Φ k) :=
    sourceDomCharted (I := I) Φ k
  let sourceSmoothInst : IsManifold I ∞ ↑(sourceOpen (I := I) Φ k) :=
    sourceDomSmooth (I := I) Φ k
  let sourceSigma : SigmaCompactSpace ↑(sourceOpen (I := I) Φ k) := by
    change SigmaCompactSpace (SourceDomain (I := I) Φ k)
    exact sourceDomSigmaOf (I := I) Φ k (hsrc k)
  let sourceT2 : T2Space ↑(sourceOpen (I := I) Φ k) := by
    change T2Space (SourceDomain (I := I) Φ k)
    exact sourceDomT2 (I := I) Φ k
  have sourceSigmaInst : SigmaCompactSpace ↑(sourceOpen (I := I) Φ k) := sourceSigma
  have sourceT2Inst : T2Space ↑(sourceOpen (I := I) Φ k) := sourceT2
  have hscalarAmbient :=
    @metricScalarAt_restrictOpen E _ _ _ _ H _ I P.M
      P.topology P.charted P.smooth P.t2
      (by infer_instance) (by infer_instance)
      (gSeqExt (I := I) Φ R bf hsrc htgt k t) (sourceOpen (I := I) Φ k)
      sourceSigma sourceT2 (by infer_instance) (by infer_instance) xsrc
  calc
    metricScalarAt (I := I) (gSeqExt (I := I) Φ R bf hsrc htgt k t) x =
        metricScalarAt (I := I) (sourceMetric (I := I) Φ hsrc htgt k t) xsrc :=
      hscalarAmbient.symm.trans hscalarSource.symm
    _ = (sourceFlow (I := I) Φ k (hsrc k) (htgt k)).scalar t xsrc := rfl
    _ = (solutionOnRestrictOpen (I := I) (X.term (subseq k)).S
          (targetOpen (I := I) Φ k)).scalar t
          (sourceTargetDiff (I := I) Φ k xsrc) := by
      simpa only [sourceFlow] using
        DifferentialGeometry.PDE.RicciFlow.scalar_pullback (I := I)
          (solutionOnRestrictOpen (I := I) (X.term (subseq k)).S
            (targetOpen (I := I) Φ k))
          (sourceTargetDiff (I := I) Φ k) t xsrc
    _ = (X.term (subseq k)).S.scalar t
          ((sourceTargetDiff (I := I) Φ k xsrc : TargetDomain (I := I) Φ k) :
            (X.term (subseq k)).M) := by
      exact scalar_restrictOpen (I := I) (X.term (subseq k)).S
        (targetOpen (I := I) Φ k) t (sourceTargetDiff (I := I) Φ k xsrc)
    _ = (X.term (subseq k)).S.scalar t (Φ.map k x) := by
      rw [sourceTargetDiff_apply]

omit [NeZero (Module.finrank ℝ E)] in
theorem gSeqExt_ricNorm
    (R : letI : TopologicalSpace P.M := P.topology
      letI : ChartedSpace H P.M := P.charted
      letI : IsManifold I ∞ P.M := P.smooth
      SmoothRiemannianMetric I P.M)
    (bf : BumpFamily (I := I) Φ) (hsrc : SourceIsSigmaCompact Φ) (htgt : TargetIsSigmaCompact Φ)
    (k : Nat) (t : Real) (x : P.M)
    (hx : letI : TopologicalSpace P.M := P.topology; x ∈ bf.grow k) :
    letI : TopologicalSpace P.M := P.topology
    letI : ChartedSpace H P.M := P.charted
    letI : T2Space P.M := P.t2
    letI : IsManifold I ∞ P.M := P.smooth
    letI : SigmaCompactSpace P.M := P.sigmaCompact
    letI : TopologicalSpace (X.term (subseq k)).M := (X.term (subseq k)).topology
    letI : ChartedSpace H (X.term (subseq k)).M := (X.term (subseq k)).charted
    letI : T2Space (X.term (subseq k)).M := (X.term (subseq k)).t2
    letI : IsManifold I ∞ (X.term (subseq k)).M := (X.term (subseq k)).smooth
    letI : SigmaCompactSpace (X.term (subseq k)).M := (X.term (subseq k)).sigmaCompact
    normSq0S (I := I) (gSeqExt (I := I) Φ R bf hsrc htgt k t) x 2
        (metricRicci (I := I) (gSeqExt (I := I) Φ R bf hsrc htgt k t) x) =
      DifferentialGeometry.PDE.RicciFlow.ricciNorm (I := I)
        (X.term (subseq k)).S t (Φ.map k x) := by
  classical
  let : TopologicalSpace P.M := P.topology
  let : ChartedSpace H P.M := P.charted
  let : T2Space P.M := P.t2
  let : IsManifold I ∞ P.M := P.smooth
  let : SigmaCompactSpace P.M := P.sigmaCompact
  let : IsManifold I 1 P.M :=
    IsManifold.of_le (I := I) (M := P.M) (n := (∞ : WithTop ℕ∞)) (by decide)
  let : IsManifold I 2 P.M :=
    IsManifold.of_le (I := I) (M := P.M) (n := (∞ : WithTop ℕ∞)) (by decide)
  let : IsManifold I ((∞ : WithTop ℕ∞) + 1) P.M := by
    change IsManifold I ∞ P.M
    infer_instance
  let : TopologicalSpace (X.term (subseq k)).M := (X.term (subseq k)).topology
  let : ChartedSpace H (X.term (subseq k)).M := (X.term (subseq k)).charted
  let : T2Space (X.term (subseq k)).M := (X.term (subseq k)).t2
  let : IsManifold I ∞ (X.term (subseq k)).M := (X.term (subseq k)).smooth
  let : SigmaCompactSpace (X.term (subseq k)).M := (X.term (subseq k)).sigmaCompact
  let : IsManifold I 1 (X.term (subseq k)).M :=
    IsManifold.of_le (I := I) (M := (X.term (subseq k)).M)
      (n := (∞ : WithTop ℕ∞)) (by decide)
  let : IsManifold I 2 (X.term (subseq k)).M :=
    IsManifold.of_le (I := I) (M := (X.term (subseq k)).M)
      (n := (∞ : WithTop ℕ∞)) (by decide)
  let : IsManifold I ((∞ : WithTop ℕ∞) + 1) (X.term (subseq k)).M := by
    change IsManifold I ∞ (X.term (subseq k)).M
    infer_instance
  let : TopologicalSpace (SourceDomain (I := I) Φ k) := sourceDomTop (I := I) Φ k
  let : ChartedSpace H (SourceDomain (I := I) Φ k) := sourceDomCharted (I := I) Φ k
  let : T2Space (SourceDomain (I := I) Φ k) := sourceDomT2 (I := I) Φ k
  let : IsManifold I ∞ (SourceDomain (I := I) Φ k) := sourceDomSmooth (I := I) Φ k
  let : SigmaCompactSpace (SourceDomain (I := I) Φ k) :=
    sourceDomSigmaOf (I := I) Φ k (hsrc k)
  let : IsManifold I 1 (SourceDomain (I := I) Φ k) :=
    IsManifold.of_le (I := I) (M := SourceDomain (I := I) Φ k)
      (n := (∞ : WithTop ℕ∞)) (by decide)
  let : IsManifold I 2 (SourceDomain (I := I) Φ k) :=
    IsManifold.of_le (I := I) (M := SourceDomain (I := I) Φ k)
      (n := (∞ : WithTop ℕ∞)) (by decide)
  let : IsManifold I ((∞ : WithTop ℕ∞) + 1) (SourceDomain (I := I) Φ k) := by
    change IsManifold I ∞ (SourceDomain (I := I) Φ k)
    infer_instance
  let : SigmaCompactSpace ↑(targetOpen (I := I) Φ k) :=
    targetDomSigmaOf (I := I) Φ k (htgt k)
  let : T2Space ↑(targetOpen (I := I) Φ k) := targetDomT2 (I := I) Φ k
  let : IsManifold I 1 ↑(targetOpen (I := I) Φ k) :=
    IsManifold.of_le (I := I) (M := ↑(targetOpen (I := I) Φ k))
      (n := (∞ : WithTop ℕ∞)) (by decide)
  let : IsManifold I 2 ↑(targetOpen (I := I) Φ k) :=
    IsManifold.of_le (I := I) (M := ↑(targetOpen (I := I) Φ k))
      (n := (∞ : WithTop ℕ∞)) (by decide)
  let : IsManifold I ((∞ : WithTop ℕ∞) + 1) ↑(targetOpen (I := I) Φ k) := by
    change IsManifold I ∞ ↑(targetOpen (I := I) Φ k)
    infer_instance
  let : TopologicalSpace (TargetDomain (I := I) Φ k) := targetDomTop (I := I) Φ k
  let : ChartedSpace H (TargetDomain (I := I) Φ k) := targetDomCharted (I := I) Φ k
  let : T2Space (TargetDomain (I := I) Φ k) := targetDomT2 (I := I) Φ k
  let : IsManifold I ∞ (TargetDomain (I := I) Φ k) := targetDomSmooth (I := I) Φ k
  let : SigmaCompactSpace (TargetDomain (I := I) Φ k) :=
    targetDomSigmaOf (I := I) Φ k (htgt k)
  let : IsManifold I 1 (TargetDomain (I := I) Φ k) :=
    IsManifold.of_le (I := I) (M := TargetDomain (I := I) Φ k)
      (n := (∞ : WithTop ℕ∞)) (by decide)
  let : IsManifold I 2 (TargetDomain (I := I) Φ k) :=
    IsManifold.of_le (I := I) (M := TargetDomain (I := I) Φ k)
      (n := (∞ : WithTop ℕ∞)) (by decide)
  let : IsManifold I ((∞ : WithTop ℕ∞) + 1) (TargetDomain (I := I) Φ k) := by
    change IsManifold I ∞ (TargetDomain (I := I) Φ k)
    infer_instance
  obtain ⟨W, hWopen, hgrowW, hW1⟩ := bf.chi_one k
  let O : TopologicalSpace.Opens (SourceDomain (I := I) Φ k) :=
    ⟨Subtype.val ⁻¹' W, hWopen.preimage continuous_subtype_val⟩
  let : ChartedSpace H ↑O :=
    TopologicalSpace.Opens.instChartedSpace
      (H := H) (M := SourceDomain (I := I) Φ k) (s := O)
  let : IsManifold I ∞ ↑O := { O.instHasGroupoid (contDiffGroupoid ∞ I) with }
  let : SigmaCompactSpace ↑O := isSigmaCompact_iff_sigmaCompactSpace.mp
    (Geometry.isSigmaCompact_of_isOpen I O.isOpen)
  let : T2Space ↑O := inferInstance
  let : IsManifold I 1 ↑O :=
    IsManifold.of_le (I := I) (M := ↑O) (n := (∞ : WithTop ℕ∞)) (by decide)
  let : IsManifold I 2 ↑O :=
    IsManifold.of_le (I := I) (M := ↑O) (n := (∞ : WithTop ℕ∞)) (by decide)
  let : IsManifold I ((∞ : WithTop ℕ∞) + 1) ↑O := by
    change IsManifold I ∞ ↑O
    infer_instance
  let xsrc : SourceDomain (I := I) Φ k := ⟨x, bf.grow_subset k hx⟩
  have hxO : xsrc ∈ O := hgrowW hx
  have hres :
      (sourceMetric (I := I) Φ hsrc htgt k t).restrictOpen (I := I) O =
        (sourceMetricRestriction (I := I) Φ (k := k)
          (gSeqExt (I := I) Φ R bf hsrc htgt k t)).restrictOpen (I := I) O := by
    apply smoothRiemannianMetric_eq_of_inner (I := I)
    funext y
    ext a b
    rw [SmoothRiemannianMetric.restrictOpen_inner,
      SmoothRiemannianMetric.restrictOpen_inner]
    change (sourceMetric (I := I) Φ hsrc htgt k t).inner
        (y : SourceDomain (I := I) Φ k)
        (show TangentSpace I (y : SourceDomain (I := I) Φ k) from a)
        (show TangentSpace I (y : SourceDomain (I := I) Φ k) from b) =
      (sourceMetricRestriction (I := I) Φ (k := k) (gSeqExt (I := I) Φ R bf hsrc htgt k t)).inner
        (y : SourceDomain (I := I) Φ k)
        (show TangentSpace I (y : SourceDomain (I := I) Φ k) from a)
        (show TangentSpace I (y : SourceDomain (I := I) Φ k) from b)
    rw [resSource_inner (I := I) Φ k]
    change (sourceMetric (I := I) Φ hsrc htgt k t).inner
        (y : SourceDomain (I := I) Φ k)
        (show TangentSpace I (y : SourceDomain (I := I) Φ k) from a)
        (show TangentSpace I (y : SourceDomain (I := I) Φ k) from b) =
      (gSeqExt (I := I) Φ R bf hsrc htgt k t).inner
        (((y : SourceDomain (I := I) Φ k) : P.M))
        (show TangentSpace I (((y : SourceDomain (I := I) Φ k) : P.M)) from a)
        (show TangentSpace I (((y : SourceDomain (I := I) Φ k) : P.M)) from b)
    rw [gSeqExt_inner_of_mem (I := I) Φ R bf hsrc htgt k t
      ((y : SourceDomain (I := I) Φ k) : P.M)
      (y : SourceDomain (I := I) Φ k).2
      (show TangentSpace I (((y : SourceDomain (I := I) Φ k) : P.M)) from a)
      (show TangentSpace I (((y : SourceDomain (I := I) Φ k) : P.M)) from b)]
    rw [hW1 _ y.2]
    simp
  have hnormSource :
      normSq0S (I := I) (sourceMetric (I := I) Φ hsrc htgt k t) xsrc 2
          (metricRicci (I := I) (sourceMetric (I := I) Φ hsrc htgt k t) xsrc) =
        normSq0S (I := I)
          (sourceMetricRestriction (I := I) Φ (k := k)
            (gSeqExt (I := I) Φ R bf hsrc htgt k t)) xsrc 2
          (metricRicci (I := I)
            (sourceMetricRestriction (I := I) Φ (k := k)
              (gSeqExt (I := I) Φ R bf hsrc htgt k t)) xsrc) := by
    rw [← ricNorm_restrict (I := I)
        (sourceMetric (I := I) Φ hsrc htgt k t) O ⟨xsrc, hxO⟩,
      ← ricNorm_restrict (I := I)
        (sourceMetricRestriction (I := I) Φ (k := k)
          (gSeqExt (I := I) Φ R bf hsrc htgt k t)) O ⟨xsrc, hxO⟩,
      hres]
  let sourceTopInst : TopologicalSpace ↑(sourceOpen (I := I) Φ k) :=
    sourceDomTop (I := I) Φ k
  let sourceChartedInst : ChartedSpace H ↑(sourceOpen (I := I) Φ k) :=
    sourceDomCharted (I := I) Φ k
  let sourceSmoothInst : IsManifold I ∞ ↑(sourceOpen (I := I) Φ k) :=
    sourceDomSmooth (I := I) Φ k
  let sourceSigma : SigmaCompactSpace ↑(sourceOpen (I := I) Φ k) := by
    change SigmaCompactSpace (SourceDomain (I := I) Φ k)
    exact sourceDomSigmaOf (I := I) Φ k (hsrc k)
  let sourceT2 : T2Space ↑(sourceOpen (I := I) Φ k) := by
    change T2Space (SourceDomain (I := I) Φ k)
    exact sourceDomT2 (I := I) Φ k
  have sourceSigmaInst : SigmaCompactSpace ↑(sourceOpen (I := I) Φ k) := sourceSigma
  have sourceT2Inst : T2Space ↑(sourceOpen (I := I) Φ k) := sourceT2
  have hnormAmbient :=
    ricNorm_restrict (E := E) (H := H) (I := I)
      (gSeqExt (I := I) Φ R bf hsrc htgt k t) (sourceOpen (I := I) Φ k)
      xsrc
  calc
    normSq0S (I := I) (gSeqExt (I := I) Φ R bf hsrc htgt k t) x 2
        (metricRicci (I := I) (gSeqExt (I := I) Φ R bf hsrc htgt k t) x) =
        normSq0S (I := I) (sourceMetric (I := I) Φ hsrc htgt k t) xsrc 2
          (metricRicci (I := I) (sourceMetric (I := I) Φ hsrc htgt k t) xsrc) :=
      hnormAmbient.symm.trans hnormSource.symm
    _ = DifferentialGeometry.PDE.RicciFlow.ricciNorm (I := I)
          (sourceFlow (I := I) Φ k (hsrc k) (htgt k)) t xsrc := by
      rfl
    _ = DifferentialGeometry.PDE.RicciFlow.ricciNorm (I := I)
          (solutionOnRestrictOpen (I := I) (X.term (subseq k)).S
            (targetOpen (I := I) Φ k)) t
          (sourceTargetDiff (I := I) Φ k xsrc) := by
      simpa only [sourceFlow] using
        DifferentialGeometry.PDE.RicciFlow.ricciNorm_pullback (I := I)
          (solutionOnRestrictOpen (I := I) (X.term (subseq k)).S
            (targetOpen (I := I) Φ k))
          (sourceTargetDiff (I := I) Φ k) t xsrc
    _ = DifferentialGeometry.PDE.RicciFlow.ricciNorm (I := I)
          (X.term (subseq k)).S t
          ((sourceTargetDiff (I := I) Φ k xsrc : TargetDomain (I := I) Φ k) :
            (X.term (subseq k)).M) := by
      exact ricciNorm_restrictOpen (I := I) (X.term (subseq k)).S
        (targetOpen (I := I) Φ k) t (sourceTargetDiff (I := I) Φ k xsrc)
    _ = DifferentialGeometry.PDE.RicciFlow.ricciNorm (I := I)
          (X.term (subseq k)).S t (Φ.map k x) := by
      rw [sourceTargetDiff_apply]

omit [NeZero (Module.finrank ℝ E)] in
theorem gSeqExt_pde
    (R : letI : TopologicalSpace P.M := P.topology
      letI : ChartedSpace H P.M := P.charted
      letI : IsManifold I ∞ P.M := P.smooth
      SmoothRiemannianMetric I P.M)
    (bf : BumpFamily (I := I) Φ) (hsrc : SourceIsSigmaCompact Φ) (htgt : TargetIsSigmaCompact Φ)
    (k : Nat) (β ψ t : Real) (hwin : Set.Icc β ψ ⊆ X.D.regular)
    (ht : t ∈ Set.Icc β ψ) (x : P.M)
    (hx : letI : TopologicalSpace P.M := P.topology; x ∈ bf.grow k)
    (v w : letI : TopologicalSpace P.M := P.topology
      letI : ChartedSpace H P.M := P.charted
      TangentSpace I x) :
    letI : TopologicalSpace P.M := P.topology
    letI : ChartedSpace H P.M := P.charted
    letI : T2Space P.M := P.t2
    letI : IsManifold I ∞ P.M := P.smooth
    letI : SigmaCompactSpace P.M := P.sigmaCompact
    HasDerivWithinAt
      (fun s : Real => (gSeqExt (I := I) Φ R bf hsrc htgt k s).inner x v w)
      ((-2 : Real) * ricciTensor (I := I)
        (gSeqExt (I := I) Φ R bf hsrc htgt k t) x v w)
      (Set.Icc β ψ) t := by
  classical
  let : TopologicalSpace P.M := P.topology
  let : ChartedSpace H P.M := P.charted
  let : T2Space P.M := P.t2
  let : IsManifold I ∞ P.M := P.smooth
  let : SigmaCompactSpace P.M := P.sigmaCompact
  let : TopologicalSpace (SourceDomain (I := I) Φ k) := sourceDomTop (I := I) Φ k
  let : ChartedSpace H (SourceDomain (I := I) Φ k) := sourceDomCharted (I := I) Φ k
  let : T2Space (SourceDomain (I := I) Φ k) := sourceDomT2 (I := I) Φ k
  let : IsManifold I ∞ (SourceDomain (I := I) Φ k) := sourceDomSmooth (I := I) Φ k
  let : SigmaCompactSpace (SourceDomain (I := I) Φ k) :=
    sourceDomSigmaOf (I := I) Φ k (hsrc k)
  let : IsManifold I 1 (SourceDomain (I := I) Φ k) :=
    IsManifold.of_le (I := I) (M := SourceDomain (I := I) Φ k)
      (n := (∞ : WithTop ℕ∞)) (by decide)
  let : IsManifold I 2 (SourceDomain (I := I) Φ k) :=
    IsManifold.of_le (I := I) (M := SourceDomain (I := I) Φ k)
      (n := (∞ : WithTop ℕ∞)) (by decide)
  let : IsManifold I ((∞ : WithTop ℕ∞) + 1) (SourceDomain (I := I) Φ k) := by
    change IsManifold I ∞ (SourceDomain (I := I) Φ k)
    infer_instance
  let xsrc : SourceDomain (I := I) Φ k := ⟨x, bf.grow_subset k hx⟩
  let vsrc : TangentSpace I xsrc := show E from v
  let wsrc : TangentSpace I xsrc := show E from w
  let τ : RealTimeInterval.RegularTime X.D := ⟨t, hwin ht⟩
  have hflow := metric_derivWithin_eq_neg_two_ricci (I := I)
    (sourceFlow (I := I) Φ k (hsrc k) (htgt k))
    (isSolutionOn_sourceFlow (I := I) Φ k (hsrc k) (htgt k)) τ xsrc vsrc wsrc
  have hflow' : HasDerivWithinAt
      (fun s : Real => (sourceMetric (I := I) Φ hsrc htgt k s).inner xsrc vsrc wsrc)
      ((-2 : Real) * ricciTensor (I := I)
        (sourceMetric (I := I) Φ hsrc htgt k t) xsrc vsrc wsrc)
      X.D.carrier t := by
    change HasDerivWithinAt
      (fun s : Real => (sourceMetric (I := I) Φ hsrc htgt k s).inner xsrc vsrc wsrc)
      ((-2 : Real) * metricRicciAt (I := I)
        (sourceMetric (I := I) Φ hsrc htgt k t) xsrc (vec2 (I := I) vsrc wsrc))
      X.D.carrier t at hflow
    exact hflow.congr_deriv (by rw [metricRicciAt_apply_eq_ricciTensor])
  have hcoeff : ∀ s : Real,
      (gSeqExt (I := I) Φ R bf hsrc htgt k s).inner x v w =
        (sourceMetric (I := I) Φ hsrc htgt k s).inner xsrc vsrc wsrc := by
    intro s
    rw [gSeqExt_inner_of_mem (I := I) Φ R bf hsrc htgt k s x xsrc.2 v w]
    obtain ⟨W, _hWopen, hgrowW, hW1⟩ := bf.chi_one k
    rw [hW1 x (hgrowW hx)]
    simp only [one_smul, sub_self, zero_smul, add_zero]
    have hxsrc' : (⟨x, xsrc.2⟩ : SourceDomain (I := I) Φ k) = xsrc := Subtype.ext rfl
    rw [hxsrc']
  have hwindow : Set.Icc β ψ ⊆ X.D.carrier :=
    hwin.trans X.D.regular_subset
  have hder : HasDerivWithinAt
      (fun s : Real => (gSeqExt (I := I) Φ R bf hsrc htgt k s).inner x v w)
      ((-2 : Real) * ricciTensor (I := I)
        (sourceMetric (I := I) Φ hsrc htgt k t) xsrc vsrc wsrc)
      (Set.Icc β ψ) t :=
    hflow'.congr_mono (fun s _hs => hcoeff s) (hcoeff t) hwindow
  have hric := gSeqExt_ricci (I := I) Φ R bf hsrc htgt k t x hx v w
  exact hder.congr_deriv (congrArg (fun q : Real => (-2 : Real) * q) hric.symm)

theorem FlowMetricConvergenceData.gInf_pde
    (R : letI : TopologicalSpace P.M := P.topology
      letI : ChartedSpace H P.M := P.charted
      letI : IsManifold I ∞ P.M := P.smooth
      SmoothRiemannianMetric I P.M)
    (bf : BumpFamily (I := I) Φ) (hsrc : SourceIsSigmaCompact Φ) (htgt : TargetIsSigmaCompact Φ)
    (β ψ : Real) (hwin : Set.Icc β ψ ⊆ X.D.regular)
    (cLow : Real) (hcLow : 0 < cLow)
    (hbound : letI : TopologicalSpace P.M := P.topology
        letI : ChartedSpace H P.M := P.charted
        letI : IsManifold I ∞ P.M := P.smooth
      ∀ (k : Nat) (t : Real), t ∈ Set.Icc β ψ →
        ∀ (y : SourceDomain (I := I) Φ k)
          (v : letI : TopologicalSpace (SourceDomain (I := I) Φ k) :=
              sourceDomTop (I := I) Φ k
            letI : ChartedSpace H (SourceDomain (I := I) Φ k) :=
              sourceDomCharted (I := I) Φ k
            TangentSpace I y),
          cLow * R.inner (y : P.M) v v ≤
            letI : TopologicalSpace (SourceDomain (I := I) Φ k) :=
              sourceDomTop (I := I) Φ k
            letI : ChartedSpace H (SourceDomain (I := I) Φ k) :=
              sourceDomCharted (I := I) Φ k
            letI : IsManifold I ∞ (SourceDomain (I := I) Φ k) :=
              sourceDomSmooth (I := I) Φ k
            (sourceMetric (I := I) Φ hsrc htgt k t).inner y v v)
    (hcovTail : letI : TopologicalSpace P.M := P.topology
        letI : ChartedSpace H P.M := P.charted
        letI : T2Space P.M := P.t2
        letI : IsManifold I ∞ P.M := P.smooth
        letI : SigmaCompactSpace P.M := P.sigmaCompact
      ∀ q : Nat, ∃ C : Real, ∀ (k : Nat) (t : Real), t ∈ Set.Icc β ψ →
        ∀ z : P.M, z ∈ bf.grow k →
          metricCovDerivNorm (I := I) q
            (gSeqExt (I := I) Φ R bf hsrc htgt k t) R z ≤ C)
    (co : FlowMetricConvergenceData (I := I) Φ R bf hsrc htgt β ψ)
    (x : P.M)
    (v w : letI : TopologicalSpace P.M := P.topology
      letI : ChartedSpace H P.M := P.charted
      TangentSpace I x)
    {t : Real} (ht : t ∈ Set.Icc β ψ) :
    letI : TopologicalSpace P.M := P.topology
    letI : ChartedSpace H P.M := P.charted
    letI : T2Space P.M := P.t2
    letI : IsManifold I ∞ P.M := P.smooth
    letI : SigmaCompactSpace P.M := P.sigmaCompact
    HasDerivWithinAt (fun s : Real ↦ (co.gInf s).inner x v w)
      ((-2 : Real) * ricciTensor (I := I) (co.gInf t) x v w)
      (Set.Icc β ψ) t := by
  classical
  let : TopologicalSpace P.M := P.topology
  let : ChartedSpace H P.M := P.charted
  let : T2Space P.M := P.t2
  let : IsManifold I ∞ P.M := P.smooth
  let : SigmaCompactSpace P.M := P.sigmaCompact
  obtain ⟨kgrow, hkgrow⟩ := bf.grow_cover {x} isCompact_singleton
  let gTail : Nat → Real → SmoothRiemannianMetric I P.M := fun k s ↦
    gSeqExt (I := I) Φ R bf hsrc htgt (co.φ (k + kgrow)) s
  have hxgrow : ∀ k : Nat, x ∈ bf.grow (co.φ (k + kgrow)) := by
    intro k
    have hkgrow_add : kgrow ≤ k + kgrow := by omega
    have hadd_phi : k + kgrow ≤ co.φ (k + kgrow) := by
      simpa only [id_eq] using co.hφ.id_le (k + kgrow)
    exact hkgrow (co.φ (k + kgrow)) (hkgrow_add.trans hadd_phi) (Set.mem_singleton x)
  have hconvTail : ∀ p : Nat, ∀ ε : Real, 0 < ε →
      ∃ k0 : Nat, ∀ k : Nat, k0 ≤ k → ∀ u ∈ Set.Icc β ψ,
        ∀ a : Nat, a ≤ p →
          metricDerivNorm (I := I) a (gTail k u) (co.gInf u) R x < ε := by
    intro p ε hε
    obtain ⟨k0, hk0⟩ := co.convergencePt {x} isCompact_singleton p ε hε
    refine ⟨k0, fun k hk u hu a ha ↦ ?_⟩
    simpa only [gTail] using
      hk0 (k + kgrow) (by omega) u hu a ha x (Set.mem_singleton x)
  have hinner : ∀ u ∈ Set.Icc β ψ, ∀ ξ η : TangentSpace I x,
      Filter.Tendsto (fun k ↦ (gTail k u).inner x ξ η) Filter.atTop
        (nhds ((co.gInf u).inner x ξ η)) := by
    intro u hu ξ η
    refine metricInner_tendsto (I := I) (fun k ↦ gTail k u) (co.gInf u) R x ?_ ξ η
    intro ε hε
    obtain ⟨k0, hk0⟩ := hconvTail 0 ε hε
    exact ⟨k0, fun k hk ↦ hk0 k hk u hu 0 le_rfl⟩
  let lam : Real := min cLow 1
  have hlam : 0 < lam := by
    simpa only [lam] using lt_min hcLow one_pos
  have hlowSeq : ∀ k : Nat, ∀ u ∈ Set.Icc β ψ, ∀ ξ : TangentSpace I x,
      lam * R.inner x ξ ξ ≤ (gTail k u).inner x ξ ξ := by
    intro k u hu ξ
    simpa only [lam, gTail] using
      gSeqExt_lower (I := I) Φ R bf hsrc htgt cLow β ψ hcLow hbound
        (co.φ (k + kgrow)) u hu x ξ
  have hlowInf : ∀ u ∈ Set.Icc β ψ, ∀ ξ : TangentSpace I x,
      lam * R.inner x ξ ξ ≤ (co.gInf u).inner x ξ ξ := by
    intro u hu ξ
    exact ge_of_tendsto (hinner u hu ξ ξ)
      (Filter.Eventually.of_forall fun k ↦ hlowSeq k u hu ξ)
  choose C hC using hcovTail
  let Cmax : Real := max (C 0) (max (C 1) (C 2))
  let B0 : Real := max 0 (Cmax + 1)
  have hB0 : 0 ≤ B0 := by
    exact le_max_left _ _
  have hCmax : ∀ a : Nat, a ≤ 2 → C a ≤ Cmax := by
    intro a ha
    exact function_le_max_zero_one_two C ha
  have hbddSeqC : ∀ k : Nat, ∀ u ∈ Set.Icc β ψ, ∀ a : Nat, a ≤ 2 →
      metricCovDerivNorm (I := I) a (gTail k u) R x ≤ C a := by
    intro k u hu a _ha
    simpa only [gTail] using
      hC a (co.φ (k + kgrow)) u hu x (hxgrow k)
  have hbddSeq : ∀ k : Nat, ∀ u ∈ Set.Icc β ψ, ∀ a : Nat, a ≤ 2 →
      metricCovDerivNorm (I := I) a (gTail k u) R x ≤ B0 := by
    intro k u hu a ha
    exact le_trans (hbddSeqC k u hu a ha)
      (le_trans (hCmax a ha)
        (le_trans (le_add_of_nonneg_right zero_le_one) (le_max_right _ _)))
  have hbddInf : ∀ u ∈ Set.Icc β ψ, ∀ a : Nat, a ≤ 2 →
      metricCovDerivNorm (I := I) a (co.gInf u) R x ≤ B0 := by
    intro u hu a ha
    obtain ⟨k0, hk0⟩ := hconvTail 2 1 one_pos
    have hd := hk0 k0 le_rfl u hu a ha
    have htri := covNorm_le_add (I := I) a (co.gInf u) (gTail k0 u) R x
    rw [metricDerivNorm_symm (I := I) a (co.gInf u) (gTail k0 u) R x] at htri
    have hseq := hbddSeqC k0 u hu a ha
    have hCa := hCmax a ha
    exact le_max_zero_add_one_of_le_add htri hd (le_trans hseq hCa)
  have hRicConvergence : ∀ ε : Real, 0 < ε → ∃ k0 : Nat, ∀ k : Nat, k0 ≤ k →
      ∀ u ∈ Set.Icc β ψ,
        |ricciTensor (I := I) (gTail k u) x v w -
          ricciTensor (I := I) (co.gInf u) x v w| < ε :=
    ricciConvergence_of_dnConvergence (I := I) R x gTail co.gInf β ψ lam B0 hlam hB0
      hlowSeq hlowInf hbddSeq hbddInf (hconvTail 2) v w
  refine metric_limit_pde_of_metric_sequence (I := I) gTail β ψ co.gInf x v w ?_
    (fun u hu ↦ hinner u hu v w) hRicConvergence ht
  refine ⟨0, fun k _hk u hu ↦ ?_⟩
  simpa only [gTail] using
    gSeqExt_pde (I := I) Φ R bf hsrc htgt (co.φ (k + kgrow)) β ψ u hwin hu x
      (hxgrow k) v w

theorem FlowMetricConvergenceData.scalar_convergence_at
    (R : letI : TopologicalSpace P.M := P.topology
      letI : ChartedSpace H P.M := P.charted
      letI : IsManifold I ∞ P.M := P.smooth
      SmoothRiemannianMetric I P.M)
    (bf : BumpFamily (I := I) Φ) (hsrc : SourceIsSigmaCompact Φ) (htgt : TargetIsSigmaCompact Φ)
    (β ψ : Real) (cLow : Real) (hcLow : 0 < cLow)
    (hbound : letI : TopologicalSpace P.M := P.topology
        letI : ChartedSpace H P.M := P.charted
        letI : IsManifold I ∞ P.M := P.smooth
      ∀ (k : Nat) (t : Real), t ∈ Set.Icc β ψ →
        ∀ (y : SourceDomain (I := I) Φ k)
          (v : letI : TopologicalSpace (SourceDomain (I := I) Φ k) :=
              sourceDomTop (I := I) Φ k
            letI : ChartedSpace H (SourceDomain (I := I) Φ k) :=
              sourceDomCharted (I := I) Φ k
            TangentSpace I y),
          cLow * R.inner (y : P.M) v v ≤
            letI : TopologicalSpace (SourceDomain (I := I) Φ k) :=
              sourceDomTop (I := I) Φ k
            letI : ChartedSpace H (SourceDomain (I := I) Φ k) :=
              sourceDomCharted (I := I) Φ k
            letI : IsManifold I ∞ (SourceDomain (I := I) Φ k) :=
              sourceDomSmooth (I := I) Φ k
            (sourceMetric (I := I) Φ hsrc htgt k t).inner y v v)
    (hcovTail : letI : TopologicalSpace P.M := P.topology
        letI : ChartedSpace H P.M := P.charted
        letI : T2Space P.M := P.t2
        letI : IsManifold I ∞ P.M := P.smooth
        letI : SigmaCompactSpace P.M := P.sigmaCompact
      ∀ q : Nat, ∃ C : Real, ∀ (k : Nat) (t : Real), t ∈ Set.Icc β ψ →
        ∀ z : P.M, z ∈ bf.grow k →
          metricCovDerivNorm (I := I) q
            (gSeqExt (I := I) Φ R bf hsrc htgt k t) R z ≤ C)
    (co : FlowMetricConvergenceData (I := I) Φ R bf hsrc htgt β ψ)
    {t : Real} (ht : t ∈ Set.Icc β ψ) (x : P.M) :
    letI : TopologicalSpace P.M := P.topology
    letI : ChartedSpace H P.M := P.charted
    letI : T2Space P.M := P.t2
    letI : IsManifold I ∞ P.M := P.smooth
    letI : SigmaCompactSpace P.M := P.sigmaCompact
    Filter.Tendsto
      (fun k ↦
        letI : TopologicalSpace (X.term ((subseq ∘ co.φ) k)).M :=
          (X.term ((subseq ∘ co.φ) k)).topology
        letI : ChartedSpace H (X.term ((subseq ∘ co.φ) k)).M :=
          (X.term ((subseq ∘ co.φ) k)).charted
        letI : IsManifold I ∞ (X.term ((subseq ∘ co.φ) k)).M :=
          (X.term ((subseq ∘ co.φ) k)).smooth
        letI : IsManifold I ((∞ : WithTop ℕ∞) + 1)
            (X.term ((subseq ∘ co.φ) k)).M := by
          change IsManifold I ∞ (X.term ((subseq ∘ co.φ) k)).M
          infer_instance
        letI : SigmaCompactSpace (X.term ((subseq ∘ co.φ) k)).M :=
          (X.term ((subseq ∘ co.φ) k)).sigmaCompact
        letI : T2Space (X.term ((subseq ∘ co.φ) k)).M :=
          (X.term ((subseq ∘ co.φ) k)).t2
        (X.term ((subseq ∘ co.φ) k)).S.scalar t (Φ.map (co.φ k) x))
      Filter.atTop (nhds (metricScalarAt (I := I) (co.gInf t) x)) := by
  classical
  let : TopologicalSpace P.M := P.topology
  let : ChartedSpace H P.M := P.charted
  let : T2Space P.M := P.t2
  let : IsManifold I ∞ P.M := P.smooth
  let : SigmaCompactSpace P.M := P.sigmaCompact
  obtain ⟨kgrow, hkgrow⟩ := bf.grow_cover {x} isCompact_singleton
  let gTail : Nat → Real → SmoothRiemannianMetric I P.M := fun k s ↦
    gSeqExt (I := I) Φ R bf hsrc htgt (co.φ (k + kgrow)) s
  have hxgrow : ∀ k : Nat, x ∈ bf.grow (co.φ (k + kgrow)) := by
    intro k
    have hkgrow_add : kgrow ≤ k + kgrow := by omega
    have hadd_phi : k + kgrow ≤ co.φ (k + kgrow) := by
      simpa only [id_eq] using co.hφ.id_le (k + kgrow)
    exact hkgrow (co.φ (k + kgrow)) (hkgrow_add.trans hadd_phi) (Set.mem_singleton x)
  have hconvTail : ∀ p : Nat, ∀ ε : Real, 0 < ε →
      ∃ k0 : Nat, ∀ k : Nat, k0 ≤ k → ∀ u ∈ Set.Icc β ψ,
        ∀ a : Nat, a ≤ p →
          metricDerivNorm (I := I) a (gTail k u) (co.gInf u) R x < ε := by
    intro p ε hε
    obtain ⟨k0, hk0⟩ := co.convergencePt {x} isCompact_singleton p ε hε
    refine ⟨k0, fun k hk u hu a ha ↦ ?_⟩
    simpa only [gTail] using
      hk0 (k + kgrow) (by omega) u hu a ha x (Set.mem_singleton x)
  have hinner : ∀ u ∈ Set.Icc β ψ, ∀ ξ η : TangentSpace I x,
      Filter.Tendsto (fun k ↦ (gTail k u).inner x ξ η) Filter.atTop
        (nhds ((co.gInf u).inner x ξ η)) := by
    intro u hu ξ η
    refine metricInner_tendsto (I := I) (fun k ↦ gTail k u) (co.gInf u) R x ?_ ξ η
    intro ε hε
    obtain ⟨k0, hk0⟩ := hconvTail 0 ε hε
    exact ⟨k0, fun k hk ↦ hk0 k hk u hu 0 le_rfl⟩
  let lam : Real := min cLow 1
  have hlam : 0 < lam := by
    simpa only [lam] using lt_min hcLow one_pos
  have hlowSeq : ∀ k : Nat, ∀ u ∈ Set.Icc β ψ, ∀ ξ : TangentSpace I x,
      lam * R.inner x ξ ξ ≤ (gTail k u).inner x ξ ξ := by
    intro k u hu ξ
    simpa only [lam, gTail] using
      gSeqExt_lower (I := I) Φ R bf hsrc htgt cLow β ψ hcLow hbound
        (co.φ (k + kgrow)) u hu x ξ
  have hlowInf : ∀ u ∈ Set.Icc β ψ, ∀ ξ : TangentSpace I x,
      lam * R.inner x ξ ξ ≤ (co.gInf u).inner x ξ ξ := by
    intro u hu ξ
    exact ge_of_tendsto (hinner u hu ξ ξ)
      (Filter.Eventually.of_forall fun k ↦ hlowSeq k u hu ξ)
  choose C hC using hcovTail
  let Cmax : Real := max (C 0) (max (C 1) (C 2))
  let B0 : Real := max 0 (Cmax + 1)
  have hB0 : 0 ≤ B0 := le_max_left _ _
  have hCmax : ∀ a : Nat, a ≤ 2 → C a ≤ Cmax := by
    intro a ha
    exact function_le_max_zero_one_two C ha
  have hbddSeqC : ∀ k : Nat, ∀ u ∈ Set.Icc β ψ, ∀ a : Nat, a ≤ 2 →
      metricCovDerivNorm (I := I) a (gTail k u) R x ≤ C a := by
    intro k u hu a _ha
    simpa only [gTail] using
      hC a (co.φ (k + kgrow)) u hu x (hxgrow k)
  have hbddSeq : ∀ k : Nat, ∀ u ∈ Set.Icc β ψ, ∀ a : Nat, a ≤ 2 →
      metricCovDerivNorm (I := I) a (gTail k u) R x ≤ B0 := by
    intro k u hu a ha
    exact le_trans (hbddSeqC k u hu a ha)
      (le_trans (hCmax a ha)
        (le_trans (le_add_of_nonneg_right zero_le_one) (le_max_right _ _)))
  have hbddInf : ∀ u ∈ Set.Icc β ψ, ∀ a : Nat, a ≤ 2 →
      metricCovDerivNorm (I := I) a (co.gInf u) R x ≤ B0 := by
    intro u hu a ha
    obtain ⟨k0, hk0⟩ := hconvTail 2 1 one_pos
    have hd := hk0 k0 le_rfl u hu a ha
    have htri := covNorm_le_add (I := I) a (co.gInf u) (gTail k0 u) R x
    rw [metricDerivNorm_symm (I := I) a (co.gInf u) (gTail k0 u) R x] at htri
    have hseq := hbddSeqC k0 u hu a ha
    have hCa := hCmax a ha
    exact le_max_zero_add_one_of_le_add htri hd (le_trans hseq hCa)
  have hScalarConvergence : ∀ ε : Real, 0 < ε → ∃ k0 : Nat, ∀ k : Nat, k0 ≤ k →
      ∀ u ∈ Set.Icc β ψ,
        |metricScalarAt (I := I) (gTail k u) x -
          metricScalarAt (I := I) (co.gInf u) x| < ε :=
    scalarConvergence_of_dnConvergence (I := I) R x gTail co.gInf β ψ lam B0 hlam hB0
      hlowSeq hlowInf hbddSeq hbddInf (hconvTail 2)
  have hscalarTail : Filter.Tendsto
      (fun k ↦ metricScalarAt (I := I) (gTail k t) x) Filter.atTop
      (nhds (metricScalarAt (I := I) (co.gInf t) x)) := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨k0, hk0⟩ := hScalarConvergence ε hε
    refine ⟨k0, fun k hk ↦ ?_⟩
    rw [Real.dist_eq]
    exact hk0 k hk t ht
  rw [← Filter.tendsto_add_atTop_iff_nat kgrow]
  refine hscalarTail.congr' ?_
  filter_upwards with k
  simpa only [gTail, Function.comp_apply] using
    gSeqExt_scalar (I := I) Φ R bf hsrc htgt (co.φ (k + kgrow)) t x (hxgrow k)

theorem FlowMetricConvergenceData.ricNorm_convergence_at
    (R : letI : TopologicalSpace P.M := P.topology
      letI : ChartedSpace H P.M := P.charted
      letI : IsManifold I ∞ P.M := P.smooth
      SmoothRiemannianMetric I P.M)
    (bf : BumpFamily (I := I) Φ) (hsrc : SourceIsSigmaCompact Φ) (htgt : TargetIsSigmaCompact Φ)
    (β ψ : Real) (cLow : Real) (hcLow : 0 < cLow)
    (hbound : letI : TopologicalSpace P.M := P.topology
        letI : ChartedSpace H P.M := P.charted
        letI : IsManifold I ∞ P.M := P.smooth
      ∀ (k : Nat) (t : Real), t ∈ Set.Icc β ψ →
        ∀ (y : SourceDomain (I := I) Φ k)
          (v : letI : TopologicalSpace (SourceDomain (I := I) Φ k) :=
              sourceDomTop (I := I) Φ k
            letI : ChartedSpace H (SourceDomain (I := I) Φ k) :=
              sourceDomCharted (I := I) Φ k
            TangentSpace I y),
          cLow * R.inner (y : P.M) v v ≤
            letI : TopologicalSpace (SourceDomain (I := I) Φ k) :=
              sourceDomTop (I := I) Φ k
            letI : ChartedSpace H (SourceDomain (I := I) Φ k) :=
              sourceDomCharted (I := I) Φ k
            letI : IsManifold I ∞ (SourceDomain (I := I) Φ k) :=
              sourceDomSmooth (I := I) Φ k
            (sourceMetric (I := I) Φ hsrc htgt k t).inner y v v)
    (hcovTail : letI : TopologicalSpace P.M := P.topology
        letI : ChartedSpace H P.M := P.charted
        letI : T2Space P.M := P.t2
        letI : IsManifold I ∞ P.M := P.smooth
        letI : SigmaCompactSpace P.M := P.sigmaCompact
      ∀ q : Nat, ∃ C : Real, ∀ (k : Nat) (t : Real), t ∈ Set.Icc β ψ →
        ∀ z : P.M, z ∈ bf.grow k →
          metricCovDerivNorm (I := I) q
            (gSeqExt (I := I) Φ R bf hsrc htgt k t) R z ≤ C)
    (co : FlowMetricConvergenceData (I := I) Φ R bf hsrc htgt β ψ)
    {t : Real} (ht : t ∈ Set.Icc β ψ) (x : P.M) :
    letI : TopologicalSpace P.M := P.topology
    letI : ChartedSpace H P.M := P.charted
    letI : T2Space P.M := P.t2
    letI : IsManifold I ∞ P.M := P.smooth
    letI : SigmaCompactSpace P.M := P.sigmaCompact
    Filter.Tendsto
      (fun k ↦
        letI : TopologicalSpace (X.term ((subseq ∘ co.φ) k)).M :=
          (X.term ((subseq ∘ co.φ) k)).topology
        letI : ChartedSpace H (X.term ((subseq ∘ co.φ) k)).M :=
          (X.term ((subseq ∘ co.φ) k)).charted
        letI : IsManifold I ∞ (X.term ((subseq ∘ co.φ) k)).M :=
          (X.term ((subseq ∘ co.φ) k)).smooth
        letI : IsManifold I ((∞ : WithTop ℕ∞) + 1)
            (X.term ((subseq ∘ co.φ) k)).M := by
          change IsManifold I ∞ (X.term ((subseq ∘ co.φ) k)).M
          infer_instance
        letI : SigmaCompactSpace (X.term ((subseq ∘ co.φ) k)).M :=
          (X.term ((subseq ∘ co.φ) k)).sigmaCompact
        letI : T2Space (X.term ((subseq ∘ co.φ) k)).M :=
          (X.term ((subseq ∘ co.φ) k)).t2
        DifferentialGeometry.PDE.RicciFlow.ricciNorm (I := I)
          (X.term ((subseq ∘ co.φ) k)).S t (Φ.map (co.φ k) x))
      Filter.atTop
      (nhds (normSq0S (I := I) (co.gInf t) x 2
        (metricRicci (I := I) (co.gInf t) x))) := by
  classical
  let : TopologicalSpace P.M := P.topology
  let : ChartedSpace H P.M := P.charted
  let : T2Space P.M := P.t2
  let : IsManifold I ∞ P.M := P.smooth
  let : SigmaCompactSpace P.M := P.sigmaCompact
  obtain ⟨kgrow, hkgrow⟩ := bf.grow_cover {x} isCompact_singleton
  let gTail : Nat → Real → SmoothRiemannianMetric I P.M := fun k s ↦
    gSeqExt (I := I) Φ R bf hsrc htgt (co.φ (k + kgrow)) s
  have hxgrow : ∀ k : Nat, x ∈ bf.grow (co.φ (k + kgrow)) := by
    intro k
    have hkgrow_add : kgrow ≤ k + kgrow := by omega
    have hadd_phi : k + kgrow ≤ co.φ (k + kgrow) := by
      simpa only [id_eq] using co.hφ.id_le (k + kgrow)
    exact hkgrow (co.φ (k + kgrow)) (hkgrow_add.trans hadd_phi) (Set.mem_singleton x)
  have hconvTail : ∀ p : Nat, ∀ ε : Real, 0 < ε →
      ∃ k0 : Nat, ∀ k : Nat, k0 ≤ k → ∀ u ∈ Set.Icc β ψ,
        ∀ a : Nat, a ≤ p →
          metricDerivNorm (I := I) a (gTail k u) (co.gInf u) R x < ε := by
    intro p ε hε
    obtain ⟨k0, hk0⟩ := co.convergencePt {x} isCompact_singleton p ε hε
    refine ⟨k0, fun k hk u hu a ha ↦ ?_⟩
    simpa only [gTail] using
      hk0 (k + kgrow) (by omega) u hu a ha x (Set.mem_singleton x)
  have hinner : ∀ u ∈ Set.Icc β ψ, ∀ ξ η : TangentSpace I x,
      Filter.Tendsto (fun k ↦ (gTail k u).inner x ξ η) Filter.atTop
        (nhds ((co.gInf u).inner x ξ η)) := by
    intro u hu ξ η
    refine metricInner_tendsto (I := I) (fun k ↦ gTail k u) (co.gInf u) R x ?_ ξ η
    intro ε hε
    obtain ⟨k0, hk0⟩ := hconvTail 0 ε hε
    exact ⟨k0, fun k hk ↦ hk0 k hk u hu 0 le_rfl⟩
  let lam : Real := min cLow 1
  have hlam : 0 < lam := by
    simpa only [lam] using lt_min hcLow one_pos
  have hlowSeq : ∀ k : Nat, ∀ u ∈ Set.Icc β ψ, ∀ ξ : TangentSpace I x,
      lam * R.inner x ξ ξ ≤ (gTail k u).inner x ξ ξ := by
    intro k u hu ξ
    simpa only [lam, gTail] using
      gSeqExt_lower (I := I) Φ R bf hsrc htgt cLow β ψ hcLow hbound
        (co.φ (k + kgrow)) u hu x ξ
  have hlowInf : ∀ u ∈ Set.Icc β ψ, ∀ ξ : TangentSpace I x,
      lam * R.inner x ξ ξ ≤ (co.gInf u).inner x ξ ξ := by
    intro u hu ξ
    exact ge_of_tendsto (hinner u hu ξ ξ)
      (Filter.Eventually.of_forall fun k ↦ hlowSeq k u hu ξ)
  choose C hC using hcovTail
  let Cmax : Real := max (C 0) (max (C 1) (C 2))
  let B0 : Real := max 0 (Cmax + 1)
  have hB0 : 0 ≤ B0 := le_max_left _ _
  have hCmax : ∀ a : Nat, a ≤ 2 → C a ≤ Cmax := by
    intro a ha
    exact function_le_max_zero_one_two C ha
  have hbddSeqC : ∀ k : Nat, ∀ u ∈ Set.Icc β ψ, ∀ a : Nat, a ≤ 2 →
      metricCovDerivNorm (I := I) a (gTail k u) R x ≤ C a := by
    intro k u hu a _ha
    simpa only [gTail] using
      hC a (co.φ (k + kgrow)) u hu x (hxgrow k)
  have hbddSeq : ∀ k : Nat, ∀ u ∈ Set.Icc β ψ, ∀ a : Nat, a ≤ 2 →
      metricCovDerivNorm (I := I) a (gTail k u) R x ≤ B0 := by
    intro k u hu a ha
    exact le_trans (hbddSeqC k u hu a ha)
      (le_trans (hCmax a ha)
        (le_trans (le_add_of_nonneg_right zero_le_one) (le_max_right _ _)))
  have hbddInf : ∀ u ∈ Set.Icc β ψ, ∀ a : Nat, a ≤ 2 →
      metricCovDerivNorm (I := I) a (co.gInf u) R x ≤ B0 := by
    intro u hu a ha
    obtain ⟨k0, hk0⟩ := hconvTail 2 1 one_pos
    have hd := hk0 k0 le_rfl u hu a ha
    have htri := covNorm_le_add (I := I) a (co.gInf u) (gTail k0 u) R x
    rw [metricDerivNorm_symm (I := I) a (co.gInf u) (gTail k0 u) R x] at htri
    have hseq := hbddSeqC k0 u hu a ha
    have hCa := hCmax a ha
    exact le_max_zero_add_one_of_le_add htri hd (le_trans hseq hCa)
  have hRicNormConvergence : ∀ ε : Real, 0 < ε →
      ∃ k0 : Nat, ∀ k : Nat, k0 ≤ k → ∀ u ∈ Set.Icc β ψ,
        |normSq0S (I := I) (gTail k u) x 2
              (metricRicci (I := I) (gTail k u) x) -
            normSq0S (I := I) (co.gInf u) x 2
              (metricRicci (I := I) (co.gInf u) x)| < ε :=
    ricNormConvergence_of_dn (I := I) R x gTail co.gInf β ψ lam B0 hlam hB0
      hlowSeq hlowInf hbddSeq hbddInf (hconvTail 2)
  have hricNormTail : Filter.Tendsto
      (fun k ↦ normSq0S (I := I) (gTail k t) x 2
        (metricRicci (I := I) (gTail k t) x))
      Filter.atTop
      (nhds (normSq0S (I := I) (co.gInf t) x 2
        (metricRicci (I := I) (co.gInf t) x))) := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨k0, hk0⟩ := hRicNormConvergence ε hε
    refine ⟨k0, fun k hk ↦ ?_⟩
    rw [Real.dist_eq]
    exact hk0 k hk t ht
  rw [← Filter.tendsto_add_atTop_iff_nat kgrow]
  refine hricNormTail.congr' ?_
  filter_upwards with k
  simpa only [gTail, Function.comp_apply] using
    gSeqExt_ricNorm (I := I) Φ R bf hsrc htgt (co.φ (k + kgrow)) t x (hxgrow k)

end CheegerGromovCompactness
end DifferentialGeometry
