import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Convergence
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Regularized.Length
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Segment.Value
import Mathlib.Topology.Order.WithTop

noncomputable section

namespace DifferentialGeometry.CheegerGromovCompactness
open Bundle Filter Set
open scoped Manifold ContDiff
open Geometry.Curvature
open PDE.RicciFlow.Perelman
universe u uE uH

section UpperBound

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]

theorem FlowMetricConvergenceData.eventually_lSegmentValue_lt_lLength_add
    {X : PointedFlowSeq.{u, uE, uH} (I := I)}
    {L : PointedFlowData.{u, uE, uH} (I := I) X.D}
    {subseq : Nat → Nat}
    (Phi : PointedCGHMaps (I := I) X (L.atTime 0) subseq)
    (R : let : TopologicalSpace (L.atTime 0).M := (L.atTime 0).topology
      let : ChartedSpace H (L.atTime 0).M := (L.atTime 0).charted
      let : IsManifold I ∞ (L.atTime 0).M := (L.atTime 0).smooth
      SmoothRiemannianMetric I (L.atTime 0).M)
    (bf : BumpFamily (I := I) Phi) (hsrc : SourceIsSigmaCompact Phi) (htgt : TargetIsSigmaCompact Phi)
    (beta psi : Real) (cLow : Real) (hcLow : 0 < cLow)
    (hbound : let : TopologicalSpace (L.atTime 0).M := (L.atTime 0).topology
        let : ChartedSpace H (L.atTime 0).M := (L.atTime 0).charted
        let : IsManifold I ∞ (L.atTime 0).M := (L.atTime 0).smooth
      ∀ (k : Nat) (t : Real), t ∈ Icc beta psi →
        ∀ (y : SourceDomain (I := I) Phi k)
          (v : let : TopologicalSpace (SourceDomain (I := I) Phi k) :=
              sourceDomTop (I := I) Phi k
            let : ChartedSpace H (SourceDomain (I := I) Phi k) :=
              sourceDomCharted (I := I) Phi k
            TangentSpace I y),
          cLow * R.inner (y : (L.atTime 0).M) v v ≤
            let : TopologicalSpace (SourceDomain (I := I) Phi k) :=
                sourceDomTop (I := I) Phi k
            let : ChartedSpace H (SourceDomain (I := I) Phi k) :=
              sourceDomCharted (I := I) Phi k
            let : IsManifold I ∞ (SourceDomain (I := I) Phi k) :=
              sourceDomSmooth (I := I) Phi k
            (sourceMetric (I := I) Phi hsrc htgt k t).inner y v v)
    (hcovTail : let : TopologicalSpace (L.atTime 0).M := (L.atTime 0).topology
        let : ChartedSpace H (L.atTime 0).M := (L.atTime 0).charted
        let : T2Space (L.atTime 0).M := (L.atTime 0).t2
        let : IsManifold I ∞ (L.atTime 0).M := (L.atTime 0).smooth
        let : SigmaCompactSpace (L.atTime 0).M := (L.atTime 0).sigmaCompact
      ∀ q : Nat, q ≤ 2 → ∃ C : Real, ∀ (k : Nat) (t : Real), t ∈ Icc beta psi →
        ∀ z : (L.atTime 0).M, z ∈ bf.grow k →
          metricCovDerivNorm (I := I) q
            (gSeqExt (I := I) Phi R bf hsrc htgt k t) R z ≤ C)
    (co : FlowMetricConvergenceData (I := I) Phi R bf hsrc htgt beta psi)
    (htime : Icc beta psi ⊆ X.D.carrier)
    (hLmetric : let : TopologicalSpace (L.atTime 0).M := (L.atTime 0).topology
        let : ChartedSpace H (L.atTime 0).M := (L.atTime 0).charted
        let : T2Space (L.atTime 0).M := (L.atTime 0).t2
        let : IsManifold I ∞ (L.atTime 0).M := (L.atTime 0).smooth
        let : SigmaCompactSpace (L.atTime 0).M := (L.atTime 0).sigmaCompact
        let : TopologicalSpace L.M := L.topology
        let : ChartedSpace H L.M := L.charted
        let : T2Space L.M := L.t2
        let : IsManifold I ∞ L.M := L.smooth
        let : SigmaCompactSpace L.M := L.sigmaCompact
      ∀ t ∈ Icc beta psi, L.S.family.metric t = co.gInf t)
    (T a b : Real) (ha : 0 ≤ a) (hab : a ≤ b)
    (alpha : Real → (L.atTime 0).M)
    (halpha : let : TopologicalSpace (L.atTime 0).M := (L.atTime 0).topology
      let : ChartedSpace H (L.atTime 0).M := (L.atTime 0).charted
      let : IsManifold I ∞ (L.atTime 0).M := (L.atTime 0).smooth
      ContMDiff 𝓘(Real, Real) I 1 alpha)
    (hback : MapsTo (fun s ↦ T - s) (Icc a b) (Icc beta psi))
    (Ω : (k : Nat) → Set ((X.term (subseq (co.φ k))).M × Real))
    (hpreconnected : ∀ k,
      let : TopologicalSpace (X.term (subseq (co.φ k))).M :=
        (X.term (subseq (co.φ k))).topology
      PreconnectedSpace (X.term (subseq (co.φ k))).M)
    (hscalar : ∀ᶠ k in atTop,
      let : TopologicalSpace (X.term (subseq (co.φ k))).M :=
        (X.term (subseq (co.φ k))).topology
      let : ChartedSpace H (X.term (subseq (co.φ k))).M :=
        (X.term (subseq (co.φ k))).charted
      let : T2Space (X.term (subseq (co.φ k))).M :=
        (X.term (subseq (co.φ k))).t2
      let : IsManifold I ∞ (X.term (subseq (co.φ k))).M :=
        (X.term (subseq (co.φ k))).smooth
      let : SigmaCompactSpace (X.term (subseq (co.φ k))).M :=
        (X.term (subseq (co.φ k))).sigmaCompact
      BddBelow ((fun q : (X.term (subseq (co.φ k))).M × Real =>
        (X.term (subseq (co.φ k))).S.scalar q.2 q.1) '' Ω k))
    (hseg : ∀ᶠ k in atTop,
      let : TopologicalSpace (X.term (subseq (co.φ k))).M :=
        (X.term (subseq (co.φ k))).topology
      let : ChartedSpace H (X.term (subseq (co.φ k))).M :=
        (X.term (subseq (co.φ k))).charted
      let : T2Space (X.term (subseq (co.φ k))).M :=
        (X.term (subseq (co.φ k))).t2
      let : IsManifold I ∞ (X.term (subseq (co.φ k))).M :=
        (X.term (subseq (co.φ k))).smooth
      let : SigmaCompactSpace (X.term (subseq (co.φ k))).M :=
        (X.term (subseq (co.φ k))).sigmaCompact
      let : LocallyCompactSpace (X.term (subseq (co.φ k))).M :=
        Manifold.locallyCompact_of_finiteDimensional (M := (X.term (subseq (co.φ k))).M) I
      let : RegularSpace (X.term (subseq (co.φ k))).M := inferInstance
      let : PreconnectedSpace (X.term (subseq (co.φ k))).M := hpreconnected k
      isFiniteActionLCurve (X.term (subseq (co.φ k))).S T (Ω k) a b
        (fun r ↦ Phi.map (co.φ k) (alpha r)))
    {ε : Real} (hε : 0 < ε) :
    ∀ᶠ k in atTop,
      let : TopologicalSpace (X.term (subseq (co.φ k))).M :=
        (X.term (subseq (co.φ k))).topology
      let : ChartedSpace H (X.term (subseq (co.φ k))).M :=
        (X.term (subseq (co.φ k))).charted
      let : T2Space (X.term (subseq (co.φ k))).M :=
        (X.term (subseq (co.φ k))).t2
      let : IsManifold I ∞ (X.term (subseq (co.φ k))).M :=
        (X.term (subseq (co.φ k))).smooth
      let : SigmaCompactSpace (X.term (subseq (co.φ k))).M :=
        (X.term (subseq (co.φ k))).sigmaCompact
      let : LocallyCompactSpace (X.term (subseq (co.φ k))).M :=
        Manifold.locallyCompact_of_finiteDimensional (M := (X.term (subseq (co.φ k))).M) I
      let : RegularSpace (X.term (subseq (co.φ k))).M := inferInstance
      let : PreconnectedSpace (X.term (subseq (co.φ k))).M := hpreconnected k
      lSegmentValue (X.term (subseq (co.φ k))).S T (Ω k) a b
          (Phi.map (co.φ k) (alpha a)) (Phi.map (co.φ k) (alpha b)) <
        let : TopologicalSpace (L.atTime 0).M := (L.atTime 0).topology
        let : ChartedSpace H (L.atTime 0).M := (L.atTime 0).charted
        let : T2Space (L.atTime 0).M := (L.atTime 0).t2
        let : IsManifold I ∞ (L.atTime 0).M := (L.atTime 0).smooth
        let : SigmaCompactSpace (L.atTime 0).M := (L.atTime 0).sigmaCompact
        let : TopologicalSpace L.M := L.topology
        let : ChartedSpace H L.M := L.charted
        let : T2Space L.M := L.t2
        let : IsManifold I ∞ L.M := L.smooth
        let : SigmaCompactSpace L.M := L.sigmaCompact
        ((lLength L.S T alpha a b + ε : Real) : WithTop Real) := by
  let : TopologicalSpace (L.atTime 0).M := (L.atTime 0).topology
  let : ChartedSpace H (L.atTime 0).M := (L.atTime 0).charted
  let : T2Space (L.atTime 0).M := (L.atTime 0).t2
  let : IsManifold I ∞ (L.atTime 0).M := (L.atTime 0).smooth
  let : IsManifold I ((∞ : WithTop ℕ∞) + 1) (L.atTime 0).M := by
    change IsManifold I ∞ (L.atTime 0).M
    infer_instance
  let : SigmaCompactSpace (L.atTime 0).M := (L.atTime 0).sigmaCompact
  let : TopologicalSpace L.M := L.topology
  let : ChartedSpace H L.M := L.charted
  let : T2Space L.M := L.t2
  let : IsManifold I ∞ L.M := L.smooth
  let : IsManifold I ((∞ : WithTop ℕ∞) + 1) L.M := by
    change IsManifold I ∞ L.M
    infer_instance
  let : SigmaCompactSpace L.M := L.sigmaCompact
  have hconv := FlowMetricConvergenceData.tendsto_lLength_map
    (I := I) Phi R bf hsrc htgt beta psi cLow hcLow
    hbound hcovTail co htime hLmetric T a b alpha halpha
    (by simpa only [uIcc_of_le hab] using hback)
  have haction : ∀ᶠ k in atTop,
      let : TopologicalSpace (X.term (subseq (co.φ k))).M :=
        (X.term (subseq (co.φ k))).topology
      let : ChartedSpace H (X.term (subseq (co.φ k))).M :=
        (X.term (subseq (co.φ k))).charted
      let : T2Space (X.term (subseq (co.φ k))).M :=
        (X.term (subseq (co.φ k))).t2
      let : IsManifold I ∞ (X.term (subseq (co.φ k))).M :=
        (X.term (subseq (co.φ k))).smooth
      let : SigmaCompactSpace (X.term (subseq (co.φ k))).M :=
        (X.term (subseq (co.φ k))).sigmaCompact
      lLength (X.term (subseq (co.φ k))).S T
        (fun r ↦ Phi.map (co.φ k) (alpha r)) a b <
          lLength L.S T alpha a b + ε := by
    exact hconv.eventually_lt_const (by linarith)
  filter_upwards [hscalar, hseg, haction] with k hscalar_k hseg_k haction_k
  let : TopologicalSpace (X.term (subseq (co.φ k))).M :=
    (X.term (subseq (co.φ k))).topology
  let : ChartedSpace H (X.term (subseq (co.φ k))).M :=
    (X.term (subseq (co.φ k))).charted
  let : T2Space (X.term (subseq (co.φ k))).M :=
    (X.term (subseq (co.φ k))).t2
  let : IsManifold I ∞ (X.term (subseq (co.φ k))).M :=
    (X.term (subseq (co.φ k))).smooth
  let : SigmaCompactSpace (X.term (subseq (co.φ k))).M :=
    (X.term (subseq (co.φ k))).sigmaCompact
  let : LocallyCompactSpace (X.term (subseq (co.φ k))).M :=
    Manifold.locallyCompact_of_finiteDimensional (M := (X.term (subseq (co.φ k))).M) I
  let : RegularSpace (X.term (subseq (co.φ k))).M := inferInstance
  let : PreconnectedSpace (X.term (subseq (co.φ k))).M := hpreconnected k
  obtain ⟨m, hm⟩ := hscalar_k
  have hR : ∀ q ∈ Ω k, -(-m) ≤ (X.term (subseq (co.φ k))).S.scalar q.2 q.1 := by
    intro q hq
    simpa only [neg_neg] using hm ⟨q, hq, rfl⟩
  calc
    lSegmentValue (X.term (subseq (co.φ k))).S T (Ω k) a b
        (Phi.map (co.φ k) (alpha a)) (Phi.map (co.φ k) (alpha b)) ≤
        (lLength (X.term (subseq (co.φ k))).S T
          (fun r ↦ Phi.map (co.φ k) (alpha r)) a b : WithTop Real) := by
      exact lSegmentValue_le_lLength (X.term (subseq (co.φ k))).S T (-m) (Ω k) ha hab hR
        _ _ _ hseg_k rfl rfl
    _ < ((lLength L.S T alpha a b + ε : Real) : WithTop Real) :=
      WithTop.coe_lt_coe.mpr haction_k

end UpperBound

section Sobolev

open Function MeasureTheory
open Analysis.Parabolic.TimeSobolev PDE.RicciFlow
open scoped Topology Interval

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]

theorem FlowMetricConvergenceData.tendsto_lSegmentValue_of_timeH1
    {X : PointedFlowSeq.{u, uE, uH} (I := I)}
    {L : PointedFlowData.{u, uE, uH} (I := I) X.D}
    {subseq : Nat → Nat}
    (Phi : PointedCGHMaps (I := I) X (L.atTime 0) subseq)
    (R : let : TopologicalSpace (L.atTime 0).M := (L.atTime 0).topology
      let : ChartedSpace H (L.atTime 0).M := (L.atTime 0).charted
      let : IsManifold I ∞ (L.atTime 0).M := (L.atTime 0).smooth
      SmoothRiemannianMetric I (L.atTime 0).M)
    (bf : BumpFamily (I := I) Phi) (hSrc : SourceIsSigmaCompact Phi) (hTgt : TargetIsSigmaCompact Phi)
    (beta psi cLow : Real) (hcLow : 0 < cLow)
    (hBound : let : TopologicalSpace (L.atTime 0).M := (L.atTime 0).topology
        let : ChartedSpace H (L.atTime 0).M := (L.atTime 0).charted
        let : IsManifold I ∞ (L.atTime 0).M := (L.atTime 0).smooth
      ∀ (k : Nat) (t : Real), t ∈ Icc beta psi →
        ∀ (z : SourceDomain (I := I) Phi k)
          (v : let : TopologicalSpace (SourceDomain (I := I) Phi k) :=
              sourceDomTop (I := I) Phi k
            let : ChartedSpace H (SourceDomain (I := I) Phi k) :=
              sourceDomCharted (I := I) Phi k
            TangentSpace I z),
          cLow * R.inner (z : (L.atTime 0).M) v v ≤
            let : TopologicalSpace (SourceDomain (I := I) Phi k) :=
              sourceDomTop (I := I) Phi k
            let : ChartedSpace H (SourceDomain (I := I) Phi k) :=
              sourceDomCharted (I := I) Phi k
            let : IsManifold I ∞ (SourceDomain (I := I) Phi k) :=
              sourceDomSmooth (I := I) Phi k
            (sourceMetric (I := I) Phi hSrc hTgt k t).inner z v v)
    (hCovTail : let : TopologicalSpace (L.atTime 0).M := (L.atTime 0).topology
        let : ChartedSpace H (L.atTime 0).M := (L.atTime 0).charted
        let : T2Space (L.atTime 0).M := (L.atTime 0).t2
        let : IsManifold I ∞ (L.atTime 0).M := (L.atTime 0).smooth
        let : SigmaCompactSpace (L.atTime 0).M := (L.atTime 0).sigmaCompact
      ∀ q : Nat, q ≤ 2 → ∃ C : Real, ∀ (k : Nat) (t : Real), t ∈ Icc beta psi →
        ∀ z : (L.atTime 0).M, z ∈ bf.grow k →
          metricCovDerivNorm (I := I) q
            (gSeqExt (I := I) Phi R bf hSrc hTgt k t) R z ≤ C)
    (co : FlowMetricConvergenceData (I := I) Phi R bf hSrc hTgt beta psi)
    (hReg : Icc beta psi ⊆ X.D.regular)
    (hLMetric : let : TopologicalSpace L.M := L.topology
        let : ChartedSpace H L.M := L.charted
        let : T2Space L.M := L.t2
        let : IsManifold I ∞ L.M := L.smooth
        let : SigmaCompactSpace L.M := L.sigmaCompact
      ∀ t ∈ Icc beta psi, L.S.family.metric t = co.gInf t)
    (hLimPreconnected : let : TopologicalSpace L.M := L.topology
      PreconnectedSpace L.M)
    (T a b K0 : Real) (ha : 0 ≤ a) (hab : a ≤ b)
    (x y : L.M) (ΩLim : Set (L.M × Real))
    (Ω : (k : Nat) → Set ((X.term (subseq (co.φ k))).M × Real))
    (hTermPreconnected : ∀ k,
      let : TopologicalSpace (X.term (subseq (co.φ k))).M :=
        (X.term (subseq (co.φ k))).topology
      PreconnectedSpace (X.term (subseq (co.φ k))).M)
    (hScalar : ∀ᶠ k in atTop,
      let : TopologicalSpace (X.term (subseq (co.φ k))).M :=
        (X.term (subseq (co.φ k))).topology
      let : ChartedSpace H (X.term (subseq (co.φ k))).M :=
        (X.term (subseq (co.φ k))).charted
      let : T2Space (X.term (subseq (co.φ k))).M :=
        (X.term (subseq (co.φ k))).t2
      let : IsManifold I ∞ (X.term (subseq (co.φ k))).M :=
        (X.term (subseq (co.φ k))).smooth
      let : SigmaCompactSpace (X.term (subseq (co.φ k))).M :=
        (X.term (subseq (co.φ k))).sigmaCompact
      ∀ q ∈ Ω k, -K0 ≤ (X.term (subseq (co.φ k))).S.scalar q.2 q.1)
    (hScalarLim : let : TopologicalSpace L.M := L.topology
      let : ChartedSpace H L.M := L.charted
      let : T2Space L.M := L.t2
      let : IsManifold I ∞ L.M := L.smooth
      let : SigmaCompactSpace L.M := L.sigmaCompact
      ∀ q ∈ ΩLim, -K0 ≤ L.S.scalar q.2 q.1)
    (delta : Real → L.M)
    (hDeltaC1 : let : TopologicalSpace L.M := L.topology
      let : ChartedSpace H L.M := L.charted
      let : IsManifold I ∞ L.M := L.smooth
      ContMDiff 𝓘(Real, Real) I 1 delta)
    (hDeltaAtt : let : TopologicalSpace L.M := L.topology
      let : ChartedSpace H L.M := L.charted
      let : IsManifold I ∞ L.M := L.smooth
      let : T2Space L.M := L.t2
      let : LocallyCompactSpace L.M := Manifold.locallyCompact_of_finiteDimensional I
      let : RegularSpace L.M := inferInstance
      let : PreconnectedSpace L.M := hLimPreconnected
      isLSegmentMinimizer L.S T ΩLim (a ^ 2) (b ^ 2) x y delta)
    (hDeltaMap : ∀ᶠ k in atTop,
      let : TopologicalSpace (X.term (subseq (co.φ k))).M :=
        (X.term (subseq (co.φ k))).topology
      let : ChartedSpace H (X.term (subseq (co.φ k))).M :=
        (X.term (subseq (co.φ k))).charted
      let : T2Space (X.term (subseq (co.φ k))).M :=
        (X.term (subseq (co.φ k))).t2
      let : IsManifold I ∞ (X.term (subseq (co.φ k))).M :=
        (X.term (subseq (co.φ k))).smooth
      let : SigmaCompactSpace (X.term (subseq (co.φ k))).M :=
        (X.term (subseq (co.φ k))).sigmaCompact
      let : LocallyCompactSpace (X.term (subseq (co.φ k))).M :=
        Manifold.locallyCompact_of_finiteDimensional I
      let : RegularSpace (X.term (subseq (co.φ k))).M := inferInstance
      let : PreconnectedSpace (X.term (subseq (co.φ k))).M := hTermPreconnected k
      isFiniteActionLCurve (X.term (subseq (co.φ k))).S T (Ω k)
        (a ^ 2) (b ^ 2) (fun r ↦ Phi.map (co.φ k) (delta r)))
    (alpha : Nat → Real → L.M) (alphaLim : Real → L.M)
    (hTermAtt : ∀ᶠ k in atTop,
      let : TopologicalSpace (X.term (subseq (co.φ k))).M :=
        (X.term (subseq (co.φ k))).topology
      let : ChartedSpace H (X.term (subseq (co.φ k))).M :=
        (X.term (subseq (co.φ k))).charted
      let : T2Space (X.term (subseq (co.φ k))).M :=
        (X.term (subseq (co.φ k))).t2
      let : IsManifold I ∞ (X.term (subseq (co.φ k))).M :=
        (X.term (subseq (co.φ k))).smooth
      let : SigmaCompactSpace (X.term (subseq (co.φ k))).M :=
        (X.term (subseq (co.φ k))).sigmaCompact
      let : LocallyCompactSpace (X.term (subseq (co.φ k))).M :=
        Manifold.locallyCompact_of_finiteDimensional I
      let : RegularSpace (X.term (subseq (co.φ k))).M := inferInstance
      let : PreconnectedSpace (X.term (subseq (co.φ k))).M := hTermPreconnected k
      isLSegmentMinimizer (X.term (subseq (co.φ k))).S T (Ω k)
        (a ^ 2) (b ^ 2) (Phi.map (co.φ k) x) (Phi.map (co.φ k) y)
        (squareRootReparametrization (fun s ↦ Phi.map (co.φ k) (alpha k s))))
    (hLimSeg : let : TopologicalSpace L.M := L.topology
      let : ChartedSpace H L.M := L.charted
      let : IsManifold I ∞ L.M := L.smooth
      let : T2Space L.M := L.t2
      let : LocallyCompactSpace L.M := Manifold.locallyCompact_of_finiteDimensional I
      let : RegularSpace L.M := inferInstance
      let : PreconnectedSpace L.M := hLimPreconnected
      isFiniteActionLCurve L.S T ΩLim (a ^ 2) (b ^ 2) (squareRootReparametrization alphaLim))
    (hLimA : squareRootReparametrization alphaLim (a ^ 2) = x)
    (hLimB : squareRootReparametrization alphaLim (b ^ 2) = y)
    (u : Nat → timeH1 E (b - a)) (uLim : timeH1 E (b - a))
    (z0 : L.M)
    (hChart : let : TopologicalSpace L.M := L.topology
      let : ChartedSpace H L.M := L.charted
      ∀ n, MapsTo (alpha n) (Icc a b) (chartAt H z0).source)
    (hRep : let : TopologicalSpace L.M := L.topology
      let : ChartedSpace H L.M := L.charted
      let : IsManifold I ∞ L.M := L.smooth
      ∀ n, EqOn (u n).toFun
        (fun r ↦ extChartAt I z0 (alpha n (a + r))) (Icc (0 : Real) (b - a)))
    (hLimChart : let : TopologicalSpace L.M := L.topology
      let : ChartedSpace H L.M := L.charted
      MapsTo alphaLim (Icc a b) (chartAt H z0).source)
    (hLimRep : let : TopologicalSpace L.M := L.topology
      let : ChartedSpace H L.M := L.charted
      let : IsManifold I ∞ L.M := L.smooth
      EqOn uLim.toFun
        (fun r ↦ extChartAt I z0 (alphaLim (a + r))) (Icc (0 : Real) (b - a)))
    (Kc : Set E) (hKc : IsCompact Kc)
    (hKChart : let : TopologicalSpace L.M := L.topology
      let : ChartedSpace H L.M := L.charted
      let : IsManifold I ∞ L.M := L.smooth
      Kc ⊆ (extChartAt I z0).target)
    (huK : ∀ n (r : Icc (0 : Real) (b - a)), (u n).toFun r.1 ∈ Kc)
    (hu : TendstoUniformly
      (fun n (r : Icc (0 : Real) (b - a)) ↦ (u n).toFun r.1)
      (fun r ↦ uLim.toFun r.1) atTop)
    (hdu : ∀ z : timeL2 E (b - a), Tendsto
      (fun n ↦ inner Real (u n).deriv z) atTop
      (nhds (inner Real uLim.deriv z)))
    (hBackSq : MapsTo (fun s ↦ T - s ^ 2) (Icc a b) (Icc beta psi)) :
    let : TopologicalSpace L.M := L.topology
    let : ChartedSpace H L.M := L.charted
    let : IsManifold I ∞ L.M := L.smooth
    let : T2Space L.M := L.t2
    let : LocallyCompactSpace L.M := Manifold.locallyCompact_of_finiteDimensional I
    let : RegularSpace L.M := inferInstance
    let : PreconnectedSpace L.M := hLimPreconnected
    Tendsto (fun k ↦
      let : TopologicalSpace (X.term (subseq (co.φ k))).M :=
        (X.term (subseq (co.φ k))).topology
      let : ChartedSpace H (X.term (subseq (co.φ k))).M :=
        (X.term (subseq (co.φ k))).charted
      let : T2Space (X.term (subseq (co.φ k))).M :=
        (X.term (subseq (co.φ k))).t2
      let : IsManifold I ∞ (X.term (subseq (co.φ k))).M :=
        (X.term (subseq (co.φ k))).smooth
      let : SigmaCompactSpace (X.term (subseq (co.φ k))).M :=
        (X.term (subseq (co.φ k))).sigmaCompact
      let : LocallyCompactSpace (X.term (subseq (co.φ k))).M :=
        Manifold.locallyCompact_of_finiteDimensional I
      let : RegularSpace (X.term (subseq (co.φ k))).M := inferInstance
      let : PreconnectedSpace (X.term (subseq (co.φ k))).M := hTermPreconnected k
      lSegmentValue (X.term (subseq (co.φ k))).S T (Ω k)
        (a ^ 2) (b ^ 2) (Phi.map (co.φ k) x) (Phi.map (co.φ k) y))
      atTop (nhds (lSegmentValue L.S T ΩLim (a ^ 2) (b ^ 2) x y)) := by
  classical
  let : TopologicalSpace (L.atTime 0).M := (L.atTime 0).topology
  let : ChartedSpace H (L.atTime 0).M := (L.atTime 0).charted
  let : T2Space (L.atTime 0).M := (L.atTime 0).t2
  let : IsManifold I ∞ (L.atTime 0).M := (L.atTime 0).smooth
  let : SigmaCompactSpace (L.atTime 0).M := (L.atTime 0).sigmaCompact
  let : TopologicalSpace L.M := L.topology
  let : ChartedSpace H L.M := L.charted
  let : T2Space L.M := L.t2
  let : IsManifold I ∞ L.M := L.smooth
  let : SigmaCompactSpace L.M := L.sigmaCompact
  let : LocallyCompactSpace L.M := Manifold.locallyCompact_of_finiteDimensional I
  let : RegularSpace L.M := inferInstance
  let : PreconnectedSpace L.M := hLimPreconnected
  have hb : 0 ≤ b := ha.trans hab
  have habSq : a ^ 2 ≤ b ^ 2 := (sq_le_sq₀ ha hb).2 hab
  have hBackRaw : MapsTo (fun s ↦ T - s) (Icc (a ^ 2) (b ^ 2)) (Icc beta psi) := by
    intro t ht
    have ht0 : 0 ≤ t := (sq_nonneg a).trans ht.1
    have hs : Real.sqrt t ∈ Icc a b := by
      constructor
      · simpa only [Real.sqrt_sq ha] using Real.sqrt_le_sqrt ht.1
      · simpa only [Real.sqrt_sq hb] using Real.sqrt_le_sqrt ht.2
    simpa only [Real.sq_sqrt ht0] using hBackSq hs
  let A : Nat → Real := fun k ↦
    let : TopologicalSpace (X.term (subseq (co.φ k))).M :=
      (X.term (subseq (co.φ k))).topology
    let : ChartedSpace H (X.term (subseq (co.φ k))).M :=
      (X.term (subseq (co.φ k))).charted
    let : T2Space (X.term (subseq (co.φ k))).M :=
      (X.term (subseq (co.φ k))).t2
    let : IsManifold I ∞ (X.term (subseq (co.φ k))).M :=
      (X.term (subseq (co.φ k))).smooth
    let : SigmaCompactSpace (X.term (subseq (co.φ k))).M :=
      (X.term (subseq (co.φ k))).sigmaCompact
    lRegularizedAction (X.term (subseq (co.φ k))).S T
      (fun s ↦ Phi.map (co.φ k) (alpha k s)) a b
  let A0 : Real := lLength L.S T delta (a ^ 2) (b ^ 2)
  let V : Nat → WithTop Real := fun k ↦
    let : TopologicalSpace (X.term (subseq (co.φ k))).M :=
      (X.term (subseq (co.φ k))).topology
    let : ChartedSpace H (X.term (subseq (co.φ k))).M :=
      (X.term (subseq (co.φ k))).charted
    let : T2Space (X.term (subseq (co.φ k))).M :=
      (X.term (subseq (co.φ k))).t2
    let : IsManifold I ∞ (X.term (subseq (co.φ k))).M :=
      (X.term (subseq (co.φ k))).smooth
    let : SigmaCompactSpace (X.term (subseq (co.φ k))).M :=
      (X.term (subseq (co.φ k))).sigmaCompact
    let : LocallyCompactSpace (X.term (subseq (co.φ k))).M :=
      Manifold.locallyCompact_of_finiteDimensional I
    let : RegularSpace (X.term (subseq (co.φ k))).M := inferInstance
    let : PreconnectedSpace (X.term (subseq (co.φ k))).M := hTermPreconnected k
    lSegmentValue (X.term (subseq (co.φ k))).S T (Ω k)
      (a ^ 2) (b ^ 2) (Phi.map (co.φ k) x) (Phi.map (co.φ k) y)
  let V0 : WithTop Real := lSegmentValue L.S T ΩLim (a ^ 2) (b ^ 2) x y
  have hVal : V =ᶠ[atTop] fun k => (A k : WithTop Real) := by
    filter_upwards [hTermAtt] with k hTermAttK
    let : TopologicalSpace (X.term (subseq (co.φ k))).M :=
      (X.term (subseq (co.φ k))).topology
    let : ChartedSpace H (X.term (subseq (co.φ k))).M :=
      (X.term (subseq (co.φ k))).charted
    let : T2Space (X.term (subseq (co.φ k))).M :=
      (X.term (subseq (co.φ k))).t2
    let : IsManifold I ∞ (X.term (subseq (co.φ k))).M :=
      (X.term (subseq (co.φ k))).smooth
    let : SigmaCompactSpace (X.term (subseq (co.φ k))).M :=
      (X.term (subseq (co.φ k))).sigmaCompact
    let : LocallyCompactSpace (X.term (subseq (co.φ k))).M :=
      Manifold.locallyCompact_of_finiteDimensional I
    let : RegularSpace (X.term (subseq (co.φ k))).M := inferInstance
    let : PreconnectedSpace (X.term (subseq (co.φ k))).M := hTermPreconnected k
    calc
      V k = (lLength (X.term (subseq (co.φ k))).S T
          (squareRootReparametrization (fun s ↦ Phi.map (co.φ k) (alpha k s)))
          (a ^ 2) (b ^ 2) : WithTop Real) := hTermAttK.2.2.2
      _ = (A k : WithTop Real) := congrArg (fun r : Real ↦ (r : WithTop Real))
        (lLength_squareRootReparametrization_sq (I := I) (X.term (subseq (co.φ k))).S T
          (fun s ↦ Phi.map (co.φ k) (alpha k s)) a b ha hb)
  have hVal0 : V0 = (A0 : WithTop Real) := (hDeltaAtt).2.2.2
  have hTime : Icc beta psi ⊆ X.D.carrier := hReg.trans X.D.regular_subset
  have hUpper (ε : Real) (hε : 0 < ε) :
      ∀ᶠ k in atTop, A k < A0 + ε := by
    have hScalarBdd : ∀ᶠ k in atTop,
        let : TopologicalSpace (X.term (subseq (co.φ k))).M :=
          (X.term (subseq (co.φ k))).topology
        let : ChartedSpace H (X.term (subseq (co.φ k))).M :=
          (X.term (subseq (co.φ k))).charted
        let : IsManifold I ∞ (X.term (subseq (co.φ k))).M :=
          (X.term (subseq (co.φ k))).smooth
        BddBelow ((fun q : (X.term (subseq (co.φ k))).M × Real =>
          (X.term (subseq (co.φ k))).S.scalar q.2 q.1) '' Ω k) := by
      filter_upwards [hScalar] with k hk
      refine ⟨-K0, ?_⟩
      rintro z ⟨q, hq, rfl⟩
      exact hk q hq
    have h := FlowMetricConvergenceData.eventually_lSegmentValue_lt_lLength_add
      (I := I) Phi R bf hSrc hTgt beta psi cLow hcLow
      hBound hCovTail co hTime hLMetric T (a ^ 2) (b ^ 2) (sq_nonneg a)
      habSq delta hDeltaC1 hBackRaw Ω hTermPreconnected hScalarBdd hDeltaMap hε
    filter_upwards [h, hVal] with k hk hValK
    have hk' : V k < ((A0 + ε : Real) : WithTop Real) := by
      simpa only [V, A0, hDeltaAtt.2.1, hDeltaAtt.2.2.1] using hk
    rw [hValK] at hk'
    exact WithTop.coe_lt_coe.mp hk'
  have hLsc : lRegularizedAction L.S T alphaLim a b ≤ liminf A atTop := by
    simpa only [A] using
      FlowMetricConvergenceData.lRegularizedAction_le_liminf_of_timeH1
        (I := I) Phi R bf hSrc hTgt beta psi cLow hcLow
        hBound hCovTail co hReg hLMetric T a b hab z0 alpha alphaLim
        u uLim hChart hRep hLimChart hLimRep Kc hKc
        hKChart huK hu hdu hBackSq
  have hCurve : A0 ≤ lRegularizedAction L.S T alphaLim a b := by
    apply WithTop.coe_le_coe.mp
    calc
      (A0 : WithTop Real) = V0 := hVal0.symm
      _ ≤ (lLength L.S T (squareRootReparametrization alphaLim)
          (a ^ 2) (b ^ 2) : WithTop Real) :=
        lSegmentValue_le_lLength L.S T K0 ΩLim (sq_nonneg a) habSq hScalarLim
          x y (squareRootReparametrization alphaLim) hLimSeg hLimA hLimB
      _ = (lRegularizedAction L.S T alphaLim a b : WithTop Real) :=
        congrArg (fun r : Real ↦ (r : WithTop Real))
          (lLength_squareRootReparametrization_sq (I := I) L.S T alphaLim a b ha hb)
  have hLow : A0 ≤ liminf A atTop := hCurve.trans hLsc
  let C : Real := -(2 * K0 / 3) *
    (b ^ 2 * Real.sqrt (b ^ 2) - a ^ 2 * Real.sqrt (a ^ 2))
  have hAloEv : ∀ᶠ k in atTop, C ≤ A k := by
    filter_upwards [hScalar, hTermAtt] with k hScalarK hTermAttK
    let : TopologicalSpace (X.term (subseq (co.φ k))).M :=
      (X.term (subseq (co.φ k))).topology
    let : ChartedSpace H (X.term (subseq (co.φ k))).M :=
      (X.term (subseq (co.φ k))).charted
    let : T2Space (X.term (subseq (co.φ k))).M :=
      (X.term (subseq (co.φ k))).t2
    let : IsManifold I ∞ (X.term (subseq (co.φ k))).M :=
      (X.term (subseq (co.φ k))).smooth
    let : SigmaCompactSpace (X.term (subseq (co.φ k))).M :=
      (X.term (subseq (co.φ k))).sigmaCompact
    let : LocallyCompactSpace (X.term (subseq (co.φ k))).M :=
      Manifold.locallyCompact_of_finiteDimensional I
    let : RegularSpace (X.term (subseq (co.φ k))).M := inferInstance
    let : PreconnectedSpace (X.term (subseq (co.φ k))).M := hTermPreconnected k
    have hAtt := hTermAttK
    have hAttCurve : isFiniteActionLCurve (X.term (subseq (co.φ k))).S T (Ω k)
        (a ^ 2) (b ^ 2)
        (squareRootReparametrization (fun s ↦ Phi.map (co.φ k) (alpha k s))) := hAtt.1
    have hAttInt : IntervalIntegrable
        (lDensity (X.term (subseq (co.φ k))).S T
          (squareRootReparametrization (fun s ↦ Phi.map (co.φ k) (alpha k s))))
        volume (a ^ 2) (b ^ 2) := hAttCurve.2.2.1
    have hAttGraph : ∀ s ∈ Icc (a ^ 2) (b ^ 2),
        (squareRootReparametrization (fun r ↦ Phi.map (co.φ k) (alpha k r)) s, T - s) ∈ Ω k :=
      hAttCurve.2.2.2
    have hScalarCurve : ∀ s ∈ Icc (a ^ 2) (b ^ 2),
        -K0 ≤ (X.term (subseq (co.φ k))).S.scalar (T - s)
          (squareRootReparametrization (fun r ↦ Phi.map (co.φ k) (alpha k r)) s) :=
      fun s hs ↦ hScalarK
        (squareRootReparametrization (fun r ↦ Phi.map (co.φ k) (alpha k r)) s, T - s)
        (hAttGraph s hs)
    have hLower := lLength_ge_of_scalar_lower_bound (I := I) (X.term (subseq (co.φ k))).S
      T (a ^ 2) (b ^ 2) K0 (sq_nonneg a) habSq
      (squareRootReparametrization (fun s ↦ Phi.map (co.φ k) (alpha k s))) hScalarCurve hAttInt
    rw [lLength_squareRootReparametrization_sq (I := I) (X.term (subseq (co.φ k))).S T
      (fun s ↦ Phi.map (co.φ k) (alpha k s)) a b ha hb] at hLower
    simpa only [C, A] using hLower
  have hAlo : IsBoundedUnder (· ≥ ·) atTop A :=
    isBoundedUnder_of_eventually_ge hAloEv
  have hA : Tendsto A atTop (nhds A0) := by
    refine Metric.tendsto_atTop.2 fun ε hε ↦ ?_
    have hlo : ∀ᶠ k in atTop, A0 - ε < A k :=
      eventually_lt_of_lt_liminf
        ((sub_lt_self A0 hε).trans_le hLow) hAlo
    have hhi := hUpper ε hε
    have hd : ∀ᶠ k in atTop, dist (A k) A0 < ε := by
      filter_upwards [hlo, hhi] with k hklo hkhi
      rw [Real.dist_eq]
      exact abs_lt.2 ⟨by linarith, by linarith⟩
    exact hd.exists_forall_of_atTop
  have hCoe : Tendsto (fun k ↦ (A k : WithTop Real)) atTop
      (nhds (A0 : WithTop Real)) :=
    WithTop.continuous_coe.continuousAt.tendsto.comp hA
  have hV : Tendsto V atTop (nhds V0) := by
    rw [hVal0]
    exact hCoe.congr' hVal.symm
  simpa only [V, V0] using hV

end Sobolev

end DifferentialGeometry.CheegerGromovCompactness
