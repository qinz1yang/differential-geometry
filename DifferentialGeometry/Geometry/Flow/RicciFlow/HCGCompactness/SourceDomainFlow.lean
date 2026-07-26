import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.SolutionPullback
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.SolutionRestrictOpen
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.PointedConvergence

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

/-!
# Brick 2 of the P4 conv engine — the per-`k` pulled-back flow on `SourceDomain Φ k`

For a pointed flow sequence `X`, limit data `L`, a subsequence `subseq`, comparison
maps `Φ : PointedCGHMaps X L subseq`, and an index `k`, the `k`th sequence flow
`S_k := (X.term (subseq k)).S` is restricted to the open target `targetOpen Φ k`
(Brick 1, `solutionOn_restrictOpen`) and then pulled back along the source-target
diffeomorphism `sourceTargetDiff Φ k` (P1.4, `solutionOn_pullback`).  The result

`sourceFlow Φ k hσsrc hσtgt : SolutionOn (M := SourceDomain Φ k) D`

is a Ricci-flow solution (`isSolutionOn_sourceFlow`), and its metric family
coincides with the `pullbackMetric` slot of `SourceDomainMetricData.ofRestrictPullback`
(`sourceFlow_metric_eq`), identifying the flow with the conv field's `g_k` slot.

The two sigma-compactness inputs `hσsrc`/`hσtgt` mirror `ofRestrictPullback`.
`BoundarylessManifold` on every domain is automatic here from `[I.Boundaryless]`
(Mathlib `BoundarylessManifold.open` / the boundaryless-model instance), so it is
not carried as data.
-/

noncomputable section

open Set Function Filter Bundle Manifold Tensor0SBundle
open scoped Manifold Topology ContDiff
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.PDE.RicciFlow (SolutionOn IsSolutionOn)

namespace DifferentialGeometry
namespace HCGCompactness

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]

/-- The `k`th sequence flow restricted to the open target `targetOpen Φ k` and
pulled back along the source-target diffeomorphism `sourceTargetDiff Φ k`, giving a
Ricci-flow solution on the source domain `SourceDomain Φ k`.  This is the flow the
conv field identifies with the metric slot `Φ^* g_k(t)` near a compact of the limit
manifold. -/
noncomputable def sourceFlow
    {X : PointedFlowSeq (I := I)}
    {P : PointedRiemannianManifold (I := I)}
    {subseq : Nat -> Nat}
    (Φ : PointedCGHMaps (I := I) X P subseq) (k : Nat)
    (hσsrc : letI : TopologicalSpace P.M := P.topology; IsSigmaCompact (Φ.source k))
    (hσtgt :
      letI : TopologicalSpace (X.term (subseq k)).M :=
        (X.term (subseq k)).topology
      IsSigmaCompact (Φ.target k)) :
    letI : TopologicalSpace (SourceDomain (I := I) Φ k) := sourceDomTop (I := I) Φ k
    letI : ChartedSpace H (SourceDomain (I := I) Φ k) := sourceDomCharted (I := I) Φ k
    letI : T2Space (SourceDomain (I := I) Φ k) := sourceDomT2 (I := I) Φ k
    letI : IsManifold I ∞ (SourceDomain (I := I) Φ k) := sourceDomSmooth (I := I) Φ k
    letI : SigmaCompactSpace (SourceDomain (I := I) Φ k) :=
      sourceDomSigmaOf (I := I) Φ k hσsrc
    letI : IsManifold I 1 (SourceDomain (I := I) Φ k) :=
      IsManifold.of_le (I := I) (M := SourceDomain (I := I) Φ k) (n := (∞ : WithTop ℕ∞))
        (by decide : (1 : WithTop ℕ∞) ≤ ∞)
    letI : IsManifold I ((∞ : WithTop ℕ∞) + 1) (SourceDomain (I := I) Φ k) := by
      change IsManifold I ∞ (SourceDomain (I := I) Φ k)
      infer_instance
    SolutionOn (I := I) (M := SourceDomain (I := I) Φ k) X.D := by
  letI : TopologicalSpace (X.term (subseq k)).M :=
    (X.term (subseq k)).topology
  letI : ChartedSpace H (X.term (subseq k)).M :=
    (X.term (subseq k)).charted
  letI : T2Space (X.term (subseq k)).M := (X.term (subseq k)).t2
  letI : IsManifold I ∞ (X.term (subseq k)).M :=
    (X.term (subseq k)).smooth
  letI : IsManifold I 1 (X.term (subseq k)).M :=
    IsManifold.of_le (I := I) (M := (X.term (subseq k)).M) (n := (∞ : WithTop ℕ∞))
      (by decide : (1 : WithTop ℕ∞) ≤ ∞)
  letI : IsManifold I 2 (X.term (subseq k)).M :=
    IsManifold.of_le (I := I) (M := (X.term (subseq k)).M) (n := (∞ : WithTop ℕ∞))
      (by decide : (2 : WithTop ℕ∞) ≤ ∞)
  letI : IsManifold I ((∞ : WithTop ℕ∞) + 1) (X.term (subseq k)).M := by
    change IsManifold I ∞ (X.term (subseq k)).M
    infer_instance
  letI : SigmaCompactSpace (X.term (subseq k)).M :=
    (X.term (subseq k)).sigmaCompact
  letI : TopologicalSpace (SourceDomain (I := I) Φ k) := sourceDomTop (I := I) Φ k
  letI : ChartedSpace H (SourceDomain (I := I) Φ k) := sourceDomCharted (I := I) Φ k
  letI : T2Space (SourceDomain (I := I) Φ k) := sourceDomT2 (I := I) Φ k
  letI : IsManifold I ∞ (SourceDomain (I := I) Φ k) := sourceDomSmooth (I := I) Φ k
  letI : SigmaCompactSpace (SourceDomain (I := I) Φ k) :=
    sourceDomSigmaOf (I := I) Φ k hσsrc
  -- Target instances phrased at the `↥(targetOpen Φ k)` form the `restrictOpen` call needs.
  letI : SigmaCompactSpace ↥(targetOpen (I := I) Φ k) :=
    targetDomSigmaOf (I := I) Φ k hσtgt
  letI : T2Space ↥(targetOpen (I := I) Φ k) := targetDomT2 (I := I) Φ k
  letI : IsManifold I 1 ↥(targetOpen (I := I) Φ k) :=
    IsManifold.of_le (I := I) (M := ↥(targetOpen (I := I) Φ k)) (n := (∞ : WithTop ℕ∞))
      (by decide : (1 : WithTop ℕ∞) ≤ ∞)
  letI : IsManifold I ((∞ : WithTop ℕ∞) + 1) ↥(targetOpen (I := I) Φ k) := by
    change IsManifold I ∞ ↥(targetOpen (I := I) Φ k)
    infer_instance
  -- Target-domain instances (abbrev form) for the pullback along `sourceTargetDiff`.
  letI : TopologicalSpace (TargetDomain (I := I) Φ k) := targetDomTop (I := I) Φ k
  letI : ChartedSpace H (TargetDomain (I := I) Φ k) := targetDomCharted (I := I) Φ k
  letI : IsManifold I ∞ (TargetDomain (I := I) Φ k) := targetDomSmooth (I := I) Φ k
  letI : IsManifold I 1 (TargetDomain (I := I) Φ k) :=
    IsManifold.of_le (I := I) (M := TargetDomain (I := I) Φ k) (n := (∞ : WithTop ℕ∞))
      (by decide : (1 : WithTop ℕ∞) ≤ ∞)
  letI : IsManifold I ((∞ : WithTop ℕ∞) + 1) (TargetDomain (I := I) Φ k) := by
    change IsManifold I ∞ (TargetDomain (I := I) Φ k)
    infer_instance
  letI : SigmaCompactSpace (TargetDomain (I := I) Φ k) :=
    targetDomSigmaOf (I := I) Φ k hσtgt
  letI : T2Space (TargetDomain (I := I) Φ k) := targetDomT2 (I := I) Φ k
  exact
    DifferentialGeometry.PDE.RicciFlow.solutionOn_pullback (I := I)
      (solutionOn_restrictOpen (I := I) (X.term (subseq k)).S (targetOpen (I := I) Φ k))
      (sourceTargetDiff (I := I) Φ k)

/-- The pulled-back flow `sourceFlow Φ k` is a Ricci-flow solution: compose Brick 1's
`isSolutionOn_restrictOpen` with P1.4's `isSolutionOn_pullback`. -/
theorem isSolutionOn_sourceFlow
    {X : PointedFlowSeq (I := I)}
    {P : PointedRiemannianManifold (I := I)}
    {subseq : Nat -> Nat}
    (Φ : PointedCGHMaps (I := I) X P subseq) (k : Nat)
    (hσsrc : letI : TopologicalSpace P.M := P.topology; IsSigmaCompact (Φ.source k))
    (hσtgt :
      letI : TopologicalSpace (X.term (subseq k)).M :=
        (X.term (subseq k)).topology
      IsSigmaCompact (Φ.target k)) :
    letI : TopologicalSpace (SourceDomain (I := I) Φ k) := sourceDomTop (I := I) Φ k
    letI : ChartedSpace H (SourceDomain (I := I) Φ k) := sourceDomCharted (I := I) Φ k
    letI : T2Space (SourceDomain (I := I) Φ k) := sourceDomT2 (I := I) Φ k
    letI : IsManifold I ∞ (SourceDomain (I := I) Φ k) := sourceDomSmooth (I := I) Φ k
    letI : SigmaCompactSpace (SourceDomain (I := I) Φ k) :=
      sourceDomSigmaOf (I := I) Φ k hσsrc
    letI : IsManifold I 1 (SourceDomain (I := I) Φ k) :=
      IsManifold.of_le (I := I) (M := SourceDomain (I := I) Φ k) (n := (∞ : WithTop ℕ∞))
        (by decide : (1 : WithTop ℕ∞) ≤ ∞)
    letI : IsManifold I ((∞ : WithTop ℕ∞) + 1) (SourceDomain (I := I) Φ k) := by
      change IsManifold I ∞ (SourceDomain (I := I) Φ k)
      infer_instance
    IsSolutionOn (I := I) (sourceFlow (I := I) Φ k hσsrc hσtgt) := by
  letI : TopologicalSpace (X.term (subseq k)).M :=
    (X.term (subseq k)).topology
  letI : ChartedSpace H (X.term (subseq k)).M :=
    (X.term (subseq k)).charted
  letI : T2Space (X.term (subseq k)).M := (X.term (subseq k)).t2
  letI : IsManifold I ∞ (X.term (subseq k)).M :=
    (X.term (subseq k)).smooth
  letI : IsManifold I 1 (X.term (subseq k)).M :=
    IsManifold.of_le (I := I) (M := (X.term (subseq k)).M) (n := (∞ : WithTop ℕ∞))
      (by decide : (1 : WithTop ℕ∞) ≤ ∞)
  letI : IsManifold I 2 (X.term (subseq k)).M :=
    IsManifold.of_le (I := I) (M := (X.term (subseq k)).M) (n := (∞ : WithTop ℕ∞))
      (by decide : (2 : WithTop ℕ∞) ≤ ∞)
  letI : IsManifold I ((∞ : WithTop ℕ∞) + 1) (X.term (subseq k)).M := by
    change IsManifold I ∞ (X.term (subseq k)).M
    infer_instance
  letI : SigmaCompactSpace (X.term (subseq k)).M :=
    (X.term (subseq k)).sigmaCompact
  letI : TopologicalSpace (SourceDomain (I := I) Φ k) := sourceDomTop (I := I) Φ k
  letI : ChartedSpace H (SourceDomain (I := I) Φ k) := sourceDomCharted (I := I) Φ k
  letI : T2Space (SourceDomain (I := I) Φ k) := sourceDomT2 (I := I) Φ k
  letI : IsManifold I ∞ (SourceDomain (I := I) Φ k) := sourceDomSmooth (I := I) Φ k
  letI : IsManifold I 1 (SourceDomain (I := I) Φ k) :=
    IsManifold.of_le (I := I) (M := SourceDomain (I := I) Φ k) (n := (∞ : WithTop ℕ∞))
      (by decide : (1 : WithTop ℕ∞) ≤ ∞)
  letI : IsManifold I 2 (SourceDomain (I := I) Φ k) :=
    IsManifold.of_le (I := I) (M := SourceDomain (I := I) Φ k) (n := (∞ : WithTop ℕ∞))
      (by decide : (2 : WithTop ℕ∞) ≤ ∞)
  letI : IsManifold I ((∞ : WithTop ℕ∞) + 1) (SourceDomain (I := I) Φ k) := by
    change IsManifold I ∞ (SourceDomain (I := I) Φ k)
    infer_instance
  letI : SigmaCompactSpace (SourceDomain (I := I) Φ k) :=
    sourceDomSigmaOf (I := I) Φ k hσsrc
  -- Target instances phrased at the `↥(targetOpen Φ k)` form `isSolutionOn_restrictOpen` needs.
  letI : SigmaCompactSpace ↥(targetOpen (I := I) Φ k) :=
    targetDomSigmaOf (I := I) Φ k hσtgt
  letI : T2Space ↥(targetOpen (I := I) Φ k) := targetDomT2 (I := I) Φ k
  letI : IsManifold I 1 ↥(targetOpen (I := I) Φ k) :=
    IsManifold.of_le (I := I) (M := ↥(targetOpen (I := I) Φ k)) (n := (∞ : WithTop ℕ∞))
      (by decide : (1 : WithTop ℕ∞) ≤ ∞)
  letI : IsManifold I ((∞ : WithTop ℕ∞) + 1) ↥(targetOpen (I := I) Φ k) := by
    change IsManifold I ∞ ↥(targetOpen (I := I) Φ k)
    infer_instance
  -- Target-domain instances (abbrev form) for the pullback along `sourceTargetDiff`.
  letI : TopologicalSpace (TargetDomain (I := I) Φ k) := targetDomTop (I := I) Φ k
  letI : ChartedSpace H (TargetDomain (I := I) Φ k) := targetDomCharted (I := I) Φ k
  letI : T2Space (TargetDomain (I := I) Φ k) := targetDomT2 (I := I) Φ k
  letI : IsManifold I ∞ (TargetDomain (I := I) Φ k) := targetDomSmooth (I := I) Φ k
  letI : IsManifold I 1 (TargetDomain (I := I) Φ k) :=
    IsManifold.of_le (I := I) (M := TargetDomain (I := I) Φ k) (n := (∞ : WithTop ℕ∞))
      (by decide : (1 : WithTop ℕ∞) ≤ ∞)
  letI : IsManifold I 2 (TargetDomain (I := I) Φ k) :=
    IsManifold.of_le (I := I) (M := TargetDomain (I := I) Φ k) (n := (∞ : WithTop ℕ∞))
      (by decide : (2 : WithTop ℕ∞) ≤ ∞)
  letI : IsManifold I ((∞ : WithTop ℕ∞) + 1) (TargetDomain (I := I) Φ k) := by
    change IsManifold I ∞ (TargetDomain (I := I) Φ k)
    infer_instance
  letI : SigmaCompactSpace (TargetDomain (I := I) Φ k) :=
    targetDomSigmaOf (I := I) Φ k hσtgt
  exact
    DifferentialGeometry.PDE.RicciFlow.isSolutionOn_pullback (I := I)
      (solutionOn_restrictOpen (I := I) (X.term (subseq k)).S (targetOpen (I := I) Φ k))
      (isSolutionOn_restrictOpen (I := I) (X.term (subseq k)).S
        (X.term (subseq k)).isSolution (targetOpen (I := I) Φ k))
      (sourceTargetDiff (I := I) Φ k)

/-- **Metric identity.**  The metric family of `sourceFlow Φ k` coincides with the
`pullbackMetric` slot of `SourceDomainMetricData.ofRestrictPullback`: both are the
`sourceTargetDiff`-pullback of the target-restricted `k`th sequence metric.  This
identifies the flow with the conv field's `g_k` slot. -/
theorem sourceFlow_metric_eq
    {X : PointedFlowSeq (I := I)}
    {P : PointedRiemannianManifold (I := I)}
    {subseq : Nat -> Nat}
    (Φ : PointedCGHMaps (I := I) X P subseq) (k : Nat)
    (hσsrc : letI : TopologicalSpace P.M := P.topology; IsSigmaCompact (Φ.source k))
    (hσtgt :
      letI : TopologicalSpace (X.term (subseq k)).M :=
        (X.term (subseq k)).topology
      IsSigmaCompact (Φ.target k))
    (referenceMetric :
      letI : TopologicalSpace (SourceDomain (I := I) Φ k) := sourceDomTop (I := I) Φ k
      letI : ChartedSpace H (SourceDomain (I := I) Φ k) := sourceDomCharted (I := I) Φ k
      letI : IsManifold I ∞ (SourceDomain (I := I) Φ k) := sourceDomSmooth (I := I) Φ k
      Real -> SmoothRiemannianMetric I (SourceDomain (I := I) Φ k))
    (gInf : letI : TopologicalSpace P.M := P.topology;
      letI : ChartedSpace H P.M := P.charted; letI : IsManifold I ∞ P.M := P.smooth;
      Real -> SmoothRiemannianMetric I P.M)
    (t : Real) :
    letI : TopologicalSpace (SourceDomain (I := I) Φ k) := sourceDomTop (I := I) Φ k
    letI : ChartedSpace H (SourceDomain (I := I) Φ k) := sourceDomCharted (I := I) Φ k
    letI : T2Space (SourceDomain (I := I) Φ k) := sourceDomT2 (I := I) Φ k
    letI : IsManifold I ∞ (SourceDomain (I := I) Φ k) := sourceDomSmooth (I := I) Φ k
    letI : SigmaCompactSpace (SourceDomain (I := I) Φ k) :=
      sourceDomSigmaOf (I := I) Φ k hσsrc
    letI : IsManifold I 1 (SourceDomain (I := I) Φ k) :=
      IsManifold.of_le (I := I) (M := SourceDomain (I := I) Φ k) (n := (∞ : WithTop ℕ∞))
        (by decide : (1 : WithTop ℕ∞) ≤ ∞)
    letI : IsManifold I ((∞ : WithTop ℕ∞) + 1) (SourceDomain (I := I) Φ k) := by
      change IsManifold I ∞ (SourceDomain (I := I) Φ k)
      infer_instance
    (sourceFlow (I := I) Φ k hσsrc hσtgt).family.metric t
      = (SourceDomainMetricData.ofRestrictPullback (I := I) hσsrc hσtgt referenceMetric gInf).pullbackMetric t := by
  rfl

/-! ## Cited-input restriction primitives (metric-equivalence)

The window metric-equivalence `MetricUniformEquivalentOnWindow` transports to the
`sourceFlow` in two steps: this restriction analog to the open target, then the
existing `metricUniformEquivalentOnWindow_pullback` (`WindowDataPullback.lean`) along
`sourceTargetDiff`.  The restriction step is definitional: `restrictOpen_inner` is
`rfl`, so the inner-product bounds are literally the original bounds at `↑x`.
(The corresponding `MovingShiBoundOn` restriction is a genuine missing frontier —
see the `.md` note; it needs a `ricCovTower_restrictOpen` naturality lemma that the
banked restriction bricks do not provide.) -/

section RestrictOpenEquiv

variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M]

/-- **Metric uniform equivalence restricts to an open subtype.**  If `h` is
`C`-uniformly equivalent to `gRef` on `K ⊆ M`, then `h.restrictOpen U` is `C`-uniformly
equivalent to `gRef.restrictOpen U` on any `V ⊆ ↥U` whose image sits in `K`.  Both
inner products are unchanged by restriction (`restrictOpen_inner`, `rfl`), so the
bounds transport with the same constant `C`. -/
theorem metricUniformEquivalentOn_restrictOpen
    (K : Set M) (gRef h : SmoothRiemannianMetric I M) (C : Real)
    (hEq : MetricUniformEquivalentOn (I := I) K gRef h C)
    (U : TopologicalSpace.Opens M) [SigmaCompactSpace U] [T2Space U]
    {V : Set U} (hV : ∀ x ∈ V, (x : M) ∈ K) :
    MetricUniformEquivalentOn (I := I) V
      (gRef.restrictOpen (I := I) U) (h.restrictOpen (I := I) U) C := by
  refine ⟨hEq.1, fun x hx v => ?_⟩
  simp only [SmoothRiemannianMetric.restrictOpen_inner]
  exact hEq.2 (x : M) (hV x hx) v

/-- **Window metric uniform equivalence restricts to an open subtype.**  The time-window
version of `metricUniformEquivalentOn_restrictOpen`; applied slotwise over the sequence
`gSeq` and the window `[β, ψ]`. -/
theorem metricUniformEquivalentOnWindow_restrictOpen
    (K : Set M) (β ψ : Real) (gRef : SmoothRiemannianMetric I M)
    (gSeq : Nat -> Real -> SmoothRiemannianMetric I M) (B : Real -> Real)
    (hEq : MetricUniformEquivalentOnWindow (I := I) K β ψ gRef gSeq B)
    (U : TopologicalSpace.Opens M) [SigmaCompactSpace U] [T2Space U]
    {V : Set U} (hV : ∀ x ∈ V, (x : M) ∈ K) :
    MetricUniformEquivalentOnWindow (I := I) V β ψ
      (gRef.restrictOpen (I := I) U)
      (fun i t => (gSeq i t).restrictOpen (I := I) U) B := by
  intro i t ht
  exact metricUniformEquivalentOn_restrictOpen (I := I) K gRef (gSeq i t) (B t)
    (hEq i t ht) U hV

end RestrictOpenEquiv

end HCGCompactness
end DifferentialGeometry

end
