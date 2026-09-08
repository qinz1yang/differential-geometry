import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Convergence
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Segment.Value

noncomputable section

namespace DifferentialGeometry.CheegerGromovCompactness
open Bundle Filter Set
open scoped Manifold ContDiff
open Geometry.Curvature
open PDE.RicciFlow.Perelman
universe u uE uH
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

end DifferentialGeometry.CheegerGromovCompactness
