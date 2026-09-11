import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Cost.Convergence
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.ReducedVolume.Defs

noncomputable section

namespace DifferentialGeometry.CheegerGromovCompactness

open Bundle Filter Function MeasureTheory Set
open scoped ContDiff Manifold Topology Interval

open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.Perelman

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]

theorem FlowMetricConvergenceData.tendsto_redDensity_of_timeH1
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
    (T K0 tau : Real) (htau : 0 ≤ tau)
    (x y : L.M)
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
      ∀ t ∈ Icc (T - tau) T, ∀ z, -K0 ≤ (X.term (subseq (co.φ k))).S.scalar t z)
    (hScalarLim : let : TopologicalSpace L.M := L.topology
      let : ChartedSpace H L.M := L.charted
      let : T2Space L.M := L.t2
      let : IsManifold I ∞ L.M := L.smooth
      let : SigmaCompactSpace L.M := L.sigmaCompact
      ∀ t ∈ Icc (T - tau) T, ∀ z, -K0 ≤ L.S.scalar t z)
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
      isLSegmentMinimizer L.S T Set.univ 0 tau x y delta)
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
      isFiniteActionLCurve (X.term (subseq (co.φ k))).S T Set.univ
        0 tau (fun r ↦ Phi.map (co.φ k) (delta r)))
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
      isLSegmentMinimizer (X.term (subseq (co.φ k))).S T Set.univ
        0 tau (Phi.map (co.φ k) x) (Phi.map (co.φ k) y)
        (squareRootReparametrization (fun s ↦ Phi.map (co.φ k) (alpha k s))))
    (hLimSeg : let : TopologicalSpace L.M := L.topology
      let : ChartedSpace H L.M := L.charted
      let : IsManifold I ∞ L.M := L.smooth
      let : T2Space L.M := L.t2
      let : LocallyCompactSpace L.M := Manifold.locallyCompact_of_finiteDimensional I
      let : RegularSpace L.M := inferInstance
      let : PreconnectedSpace L.M := hLimPreconnected
      isFiniteActionLCurve L.S T Set.univ 0 tau (squareRootReparametrization alphaLim))
    (hLimA : squareRootReparametrization alphaLim 0 = x)
    (hLimB : squareRootReparametrization alphaLim tau = y)
    (u : Nat → timeH1 E (Real.sqrt tau)) (uLim : timeH1 E (Real.sqrt tau))
    (z0 : L.M)
    (hChart : let : TopologicalSpace L.M := L.topology
      let : ChartedSpace H L.M := L.charted
      ∀ n, MapsTo (alpha n) (Icc (0 : Real) (Real.sqrt tau)) (chartAt H z0).source)
    (hRep : let : TopologicalSpace L.M := L.topology
      let : ChartedSpace H L.M := L.charted
      let : IsManifold I ∞ L.M := L.smooth
      ∀ n, EqOn (u n).toFun
        (fun r ↦ extChartAt I z0 (alpha n r)) (Icc (0 : Real) (Real.sqrt tau)))
    (hLimChart : let : TopologicalSpace L.M := L.topology
      let : ChartedSpace H L.M := L.charted
      MapsTo alphaLim (Icc (0 : Real) (Real.sqrt tau)) (chartAt H z0).source)
    (hLimRep : let : TopologicalSpace L.M := L.topology
      let : ChartedSpace H L.M := L.charted
      let : IsManifold I ∞ L.M := L.smooth
      EqOn uLim.toFun
        (fun r ↦ extChartAt I z0 (alphaLim r)) (Icc (0 : Real) (Real.sqrt tau)))
    (Kc : Set E) (hKc : IsCompact Kc)
    (hKChart : let : TopologicalSpace L.M := L.topology
      let : ChartedSpace H L.M := L.charted
      let : IsManifold I ∞ L.M := L.smooth
      Kc ⊆ (extChartAt I z0).target)
    (huK : ∀ n (r : Icc (0 : Real) (Real.sqrt tau)), (u n).toFun r.1 ∈ Kc)
    (hu : TendstoUniformly
      (fun n (r : Icc (0 : Real) (Real.sqrt tau)) ↦ (u n).toFun r.1)
      (fun r ↦ uLim.toFun r.1) atTop)
    (hdu : ∀ z : timeL2 E (Real.sqrt tau), Tendsto
      (fun n ↦ inner Real (u n).deriv z) atTop
      (nhds (inner Real uLim.deriv z)))
    (hBackSq : MapsTo (fun s ↦ T - s ^ 2) (Icc (0 : Real) (Real.sqrt tau)) (Icc beta psi)) :
    let : TopologicalSpace L.M := L.topology
    let : ChartedSpace H L.M := L.charted
    let : IsManifold I ∞ L.M := L.smooth
    Tendsto (fun k ↦
      let : TopologicalSpace (X.term (subseq (co.φ k))).M :=
        (X.term (subseq (co.φ k))).topology
      let : ChartedSpace H (X.term (subseq (co.φ k))).M :=
        (X.term (subseq (co.φ k))).charted
      let : IsManifold I ∞ (X.term (subseq (co.φ k))).M :=
        (X.term (subseq (co.φ k))).smooth
      redDensity (X.term (subseq (co.φ k))).S T
        (Phi.map (co.φ k) x) (Phi.map (co.φ k) y) tau)
      atTop (nhds (redDensity L.S T x y tau)) := by
  have hCost := FlowMetricConvergenceData.tendsto_lCost_of_timeH1
    Phi R bf hSrc hTgt beta psi cLow hcLow hBound hCovTail co hReg hLMetric
    hLimPreconnected T K0 tau htau x y hTermPreconnected hScalar hScalarLim
    delta hDeltaC1 hDeltaAtt hDeltaMap alpha alphaLim hTermAtt hLimSeg hLimA hLimB
    u uLim z0 hChart hRep hLimChart hLimRep Kc hKc hKChart huK hu hdu hBackSq
  have hRed := hCost.div_const (2 * Real.sqrt tau)
  have hExp := ((hRed.neg.sub_const
      (((Module.finrank Real E : Real) / 2) * Real.log tau)).sub_const
      (((Module.finrank Real E : Real) / 2) * Real.log (4 * Real.pi)))
  simpa only [Function.comp_def, redDensity, redLength] using
    Real.continuous_exp.continuousAt.tendsto.comp hExp

end DifferentialGeometry.CheegerGromovCompactness
