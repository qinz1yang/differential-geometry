import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Segment.Value
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Segment.Convergence
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Segment.RegularizedComparison
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Minimizer.Existence

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

theorem FlowMetricConvergenceData.tendsto_lCost_of_timeH1
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
      lCost (X.term (subseq (co.φ k))).S T
        (Phi.map (co.φ k) x) (Phi.map (co.φ k) y) tau)
      atTop (nhds (lCost L.S T x y tau)) := by
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
  let : PseudoMetricSpace L.M := (L.S.base.metric T).toPseudoMetricSpace
  let : TopologicalSpace L.M := L.topology
  let (k : ℕ) : TopologicalSpace (X.term (subseq (co.φ k))).M :=
    (X.term (subseq (co.φ k))).topology
  let (k : ℕ) : ChartedSpace H (X.term (subseq (co.φ k))).M :=
    (X.term (subseq (co.φ k))).charted
  let (k : ℕ) : T2Space (X.term (subseq (co.φ k))).M :=
    (X.term (subseq (co.φ k))).t2
  let (k : ℕ) : IsManifold I ∞ (X.term (subseq (co.φ k))).M :=
    (X.term (subseq (co.φ k))).smooth
  let (k : ℕ) : SigmaCompactSpace (X.term (subseq (co.φ k))).M :=
    (X.term (subseq (co.φ k))).sigmaCompact
  let (k : ℕ) : LocallyCompactSpace (X.term (subseq (co.φ k))).M :=
    Manifold.locallyCompact_of_finiteDimensional I
  let (k : ℕ) : RegularSpace (X.term (subseq (co.φ k))).M := inferInstance
  let (k : ℕ) : PreconnectedSpace (X.term (subseq (co.φ k))).M := hTermPreconnected k
  have hwindow (r : ℝ) (hr : r ∈ Icc 0 tau) : T - r ∈ Icc (T - tau) T :=
    ⟨sub_le_sub_left hr.2 T, sub_le_self T hr.1⟩
  have hslice (P : Type u) (r : ℝ) (hr : r ∈ Icc 0 tau) (z : P) :
      (z, T - r) ∈ (univ : Set (P × ℝ)) ↔
        (z, T - r) ∈ (univ : Set P) ×ˢ Icc (T - tau) T := by
    simp only [mem_univ, mem_prod, true_and, true_iff]
    exact hwindow r hr
  let ΩLim : Set (L.M × ℝ) := univ ×ˢ Icc (T - tau) T
  let Ω (k : ℕ) : Set ((X.term (subseq (co.φ k))).M × ℝ) := univ ×ˢ Icc (T - tau) T
  have hScalarSlice : ∀ᶠ k in atTop, ∀ q ∈ Ω k,
      -K0 ≤ (X.term (subseq (co.φ k))).S.scalar q.2 q.1 := by
    filter_upwards [hScalar] with k hk q hq
    exact hk q.2 hq.2 q.1
  have hScalarLimSlice : ∀ q ∈ ΩLim, -K0 ≤ L.S.scalar q.2 q.1 :=
    fun q hq => hScalarLim q.2 hq.2 q.1
  have hDeltaAttSlice : isLSegmentMinimizer L.S T ΩLim 0 tau x y delta :=
    (isLSegmentMinimizer_congr_region L.S T x y delta (hslice L.M)).mp hDeltaAtt
  have hDeltaMapSlice : ∀ᶠ k in atTop,
      isFiniteActionLCurve (X.term (subseq (co.φ k))).S T (Ω k) 0 tau
        (fun r => Phi.map (co.φ k) (delta r)) := by
    filter_upwards [hDeltaMap] with k hk
    exact (isFiniteActionLCurve_congr_region (X.term (subseq (co.φ k))).S T _
      (fun r hr => hslice (X.term (subseq (co.φ k))).M r hr _)).mp hk
  have hTermAttSlice : ∀ᶠ k in atTop,
      isLSegmentMinimizer (X.term (subseq (co.φ k))).S T (Ω k) 0 tau
        (Phi.map (co.φ k) x) (Phi.map (co.φ k) y)
        (squareRootReparametrization (fun s => Phi.map (co.φ k) (alpha k s))) := by
    filter_upwards [hTermAtt] with k hk
    exact (isLSegmentMinimizer_congr_region (X.term (subseq (co.φ k))).S T _ _ _
      (hslice (X.term (subseq (co.φ k))).M)).mp hk
  have hLimSegSlice : isFiniteActionLCurve L.S T ΩLim 0 tau
      (squareRootReparametrization alphaLim) :=
    (isFiniteActionLCurve_congr_region L.S T _
      (fun r hr => hslice L.M r hr _)).mp hLimSeg
  have hb : 0 ≤ Real.sqrt tau := Real.sqrt_nonneg tau
  have hv := FlowMetricConvergenceData.tendsto_lSegmentValue_of_timeH1
    Phi R bf hSrc hTgt beta psi cLow hcLow hBound hCovTail co hReg hLMetric
    hLimPreconnected T 0 (Real.sqrt tau) K0 (le_refl 0) hb x y
    ΩLim Ω hTermPreconnected hScalarSlice hScalarLimSlice
  rw [sub_zero] at hv
  simp only [zero_add, zero_pow (by decide : 2 ≠ 0), Real.sq_sqrt htau] at hv
  have hValue := hv delta hDeltaC1 hDeltaAttSlice hDeltaMapSlice alpha alphaLim hTermAttSlice
    hLimSegSlice hLimA hLimB u uLim z0 hChart hRep hLimChart hLimRep
    Kc hKc hKChart huK hu hdu hBackSq
  have hLimEq : lSegmentValue L.S T ΩLim 0 tau x y = lSegmentValue L.S T univ 0 tau x y :=
    (lSegmentValue_congr_region L.S T x y (hslice L.M)).symm
  have hTermEq (k : ℕ) :
      lSegmentValue (X.term (subseq (co.φ k))).S T (Ω k) 0 tau
        (Phi.map (co.φ k) x) (Phi.map (co.φ k) y) =
      lSegmentValue (X.term (subseq (co.φ k))).S T univ 0 tau
        (Phi.map (co.φ k) x) (Phi.map (co.φ k) y) :=
    (lSegmentValue_congr_region (X.term (subseq (co.φ k))).S T _ _
      (hslice (X.term (subseq (co.φ k))).M)).symm
  rw [hLimEq] at hValue
  have hValueUniv := hValue.congr' (Eventually.of_forall hTermEq)
  let C : Nat → Real := fun k ↦
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
    lCost (X.term (subseq (co.φ k))).S T
      (Phi.map (co.φ k) x) (Phi.map (co.φ k) y) tau
  let C0 : Real := lCost L.S T x y tau
  have hregSq : ∀ s ∈ Icc (0 : Real) (Real.sqrt tau),
      T - s ^ 2 ∈ X.D.regular :=
    fun s hs ↦ hReg (hBackSq hs)
  have hEqLim :
      lSegmentValue L.S T Set.univ 0 tau x y =
        (C0 : WithTop Real) := by
    let topM : TopologicalSpace L.M := inferInstance
    let : PseudoMetricSpace L.M := (L.S.base.metric T).toPseudoMetricSpace
    let : TopologicalSpace L.M := topM
    have hMet : MetricFamilySmoothOn (I := I) (M := L.M) X.D
        L.S.family.metric := L.isSolution.smoothMetric
    have hSc : ScalarSTContOn (I := I) (M := L.M) L.S :=
      ⟨L.isSolution.scalarCont⟩
    have hEq := lSegmentValue_eq_lRegularizedCostC1_of_isFiniteActionLCurve
      L.S hMet hSc T K0 0 (Real.sqrt tau) (le_refl 0) hb
      (fun r hr z ↦ hScalarLim (T - r)
        (hwindow r (by simpa only [zero_pow (by decide : 2 ≠ 0), Real.sq_sqrt htau] using hr)) z) hregSq x y delta
      (by simpa only [zero_pow (by decide : 2 ≠ 0), Real.sq_sqrt htau] using hDeltaAtt.1)
      (by simpa only [zero_pow (by decide : 2 ≠ 0)] using hDeltaAtt.2.1)
      (by simpa only [Real.sq_sqrt htau] using hDeltaAtt.2.2.1)
    simpa only [zero_pow (by decide : 2 ≠ 0), Real.sq_sqrt htau] using
      hEq.trans (congrArg (fun r : Real ↦ (r : WithTop Real))
        (lCost_eq_regularity (I := I) L.S T x y tau htau).symm)
  have hEqTerm : ∀ᶠ k in atTop,
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
      lSegmentValue (X.term (subseq (co.φ k))).S T Set.univ
        0 tau
        (Phi.map (co.φ k) x) (Phi.map (co.φ k) y) =
          (C k : WithTop Real) := by
    filter_upwards [hScalar, hTermAtt] with k hScalarK hAttK
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
    let topM : TopologicalSpace (X.term (subseq (co.φ k))).M := inferInstance
    let : PseudoMetricSpace (X.term (subseq (co.φ k))).M :=
      ((X.term (subseq (co.φ k))).S.base.metric T).toPseudoMetricSpace
    let : TopologicalSpace (X.term (subseq (co.φ k))).M := topM
    have hMet : MetricFamilySmoothOn (I := I)
        (M := (X.term (subseq (co.φ k))).M) X.D
        (X.term (subseq (co.φ k))).S.family.metric :=
      (X.term (subseq (co.φ k))).isSolution.smoothMetric
    have hSc : ScalarSTContOn (I := I)
        (M := (X.term (subseq (co.φ k))).M)
        (X.term (subseq (co.φ k))).S :=
      ⟨(X.term (subseq (co.φ k))).isSolution.scalarCont⟩
    have hEq := lSegmentValue_eq_lRegularizedCostC1_of_isFiniteActionLCurve
      (X.term (subseq (co.φ k))).S hMet hSc T K0 0 (Real.sqrt tau) (le_refl 0) hb
      (fun r hr z ↦ hScalarK (T - r)
        (hwindow r (by simpa only [zero_pow (by decide : 2 ≠ 0), Real.sq_sqrt htau] using hr)) z)
      hregSq (Phi.map (co.φ k) x) (Phi.map (co.φ k) y)
      (squareRootReparametrization (fun s ↦ Phi.map (co.φ k) (alpha k s)))
      (by simpa only [zero_pow (by decide : 2 ≠ 0), Real.sq_sqrt htau] using hAttK.1)
      (by simpa only [zero_pow (by decide : 2 ≠ 0)] using hAttK.2.1)
      (by simpa only [Real.sq_sqrt htau] using hAttK.2.2.1)
    simpa only [zero_pow (by decide : 2 ≠ 0), Real.sq_sqrt htau] using
      hEq.trans (congrArg (fun r : Real ↦ (r : WithTop Real))
        (lCost_eq_regularity (I := I) (X.term (subseq (co.φ k))).S T
          (Phi.map (co.φ k) x) (Phi.map (co.φ k) y) tau htau).symm)
  have hCoe : Tendsto (fun k ↦ (C k : WithTop Real)) atTop
      (nhds (C0 : WithTop Real)) := by
    rw [← hEqLim]
    exact hValueUniv.congr' hEqTerm
  have hCost : Tendsto C atTop (nhds C0) := by
    have h :=
      (WithTop.tendsto_untopD (0 : Real)
        (WithTop.coe_ne_top : (C0 : WithTop Real) ≠ ⊤)).comp hCoe
    simpa only [Function.comp_def, WithTop.untopD_coe] using h
  exact hCost

end DifferentialGeometry.CheegerGromovCompactness
