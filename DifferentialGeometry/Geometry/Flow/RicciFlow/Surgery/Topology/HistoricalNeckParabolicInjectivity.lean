import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistoricalNeckParabolicShi
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistoricalNeckInjectivity

noncomputable section
open Set Bundle Manifold
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open scoped Manifold ContDiff Topology NNReal ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u
variable {H : ObservedHistory.{u}} {i : Fin H.eventCount}
  {first : Fin (H.eventCount + 1)} {hle : first ≤ i.castSucc}

private local instance (K : Set (H.event i).incoming.terminalRegularOpen) :
    SigmaCompactSpace (H.backwardSurvivorFootprintInterior first i hle K) := by
  let : SigmaCompactSpace (H.backwardSurvivorDomain first i.castSucc hle) :=
    isSigmaCompact_iff_sigmaCompactSpace.mp
      (Geometry.isSigmaCompact_of_isOpen ThreeModel
        (H.backwardSurvivorDomain first i.castSucc hle).isOpen)
  let : SigmaCompactSpace (H.backwardSurvivorTerminalFace first i hle) :=
    isSigmaCompact_iff_sigmaCompactSpace.mp
      (Geometry.isSigmaCompact_of_isOpen ThreeModel
        (H.backwardSurvivorTerminalFace first i hle).isOpen)
  exact isSigmaCompact_iff_sigmaCompactSpace.mp
    (Geometry.isSigmaCompact_of_isOpen ThreeModel
      (H.backwardSurvivorFootprintInterior first i hle K).isOpen)

theorem exists_parabolic_historical_footprint_injectivity
    {Phi : ℝ → ℝ} (hPhi : Perelman.AdmissiblePinchingFunction Phi) :
    ∃ Q0 η : ℝ, 0 < Q0 ∧ 0 < η ∧
      ∀ {H : ObservedHistory.{u}} {i : Fin H.eventCount}
        {first : Fin (H.eventCount + 1)} {hle : first ≤ i.castSucc},
      ∀ {δ₀ δ eps : ℝ} {k : ℕ} (N : NormalizedNeck (H.event i).terminal.metric δ₀ k)
    (_ : Q0 ≤ N.scale)
    (_ : δ₀ ≤ δ) (_ : δ < 1) (_ : δ₀ ≤ eps)
    (_ : eps ≤ 1 / 8646) (_ : ⌈eps⁻¹⌉₊ ≤ k)
    (a : ℝ) (_ : 24 < a) (_ : δ⁻¹ + 1 ≤ a) (_ : 4 * a < eps⁻¹)
    {q : ℝ} {C : ℝ≥0} (_ : 0 < q) (_ : q ≤ N.scale)
    (_ : ∀ j : Fin H.eventCount, first ≤ j.castSucc → j.castSucc ≤ i.castSucc →
      ∀ x : (H.stage j.castSucc).Carrier, ∀ t ∈ Ioo (H.time j.castSucc) (H.time j.succ),
      q < (H.event j).incoming.flow.scalar t x →
      |derivWithin (fun v => (H.event j).incoming.flow.scalar v x) (Iic t) t| ≤
        C * (H.event j).incoming.flow.scalar t x ^ 2)
    (_ : ∀ j : Fin H.eventCount, first ≤ j.castSucc → j.castSucc ≤ i.castSucc →
      Perelman.PhiAlmostNonnegative (H.event j).incoming.flow
        (Ico (H.time j.castSucc) (H.time j.succ)) Phi)
    (_ : ∀ x ∈ N.chart '' {z : neckBuffer δ₀ | -(3*a) ≤ z.val.2 ∧ z.val.2 ≤ 3*a},
      Nonempty (BackwardPointTrace H first i.castSucc hle x.val))
    {θ : ℝ} (hθ : 0 < θ) (_ : H.time first ≤ H.time i.succ - θ / N.scale)
    (_ : 6 * C * θ ≤ 1),
    let K := N.chart '' {z : neckBuffer δ₀ | -(3*a) ≤ z.val.2 ∧ z.val.2 ≤ 3*a}
    let B := 4 * Real.sqrt 3 * (N.scale + Phi (4*N.scale) + Phi 0)
    ∃ (p : H.backwardSurvivorFootprintInterior first i hle K)
      (G : ℝ → SmoothRiemannianMetric ThreeModel
        (H.backwardSurvivorFootprintInterior first i hle K)),
      H.backwardSurvivorFootprintMap first i hle K p = N.center ∧
      (∀ (j : Fin H.eventCount) (hf : first ≤ j.castSucc) (hl : j.succ ≤ i.castSucc),
        ∀ t ∈ Icc (H.time j.castSucc) (H.time j.succ),
          G t = ((H.backwardSurvivorSlabMetric first i.castSucc hle j hf hl t).restrictOpen
            (H.backwardSurvivorTerminalFace first i hle)).restrictOpen
              (H.backwardSurvivorFootprintInterior first i hle K)) ∧
      (∀ t ∈ Icc (H.time i.castSucc) (H.time i.succ),
        G t = (H.backwardSurvivorTerminalFaceMetric first i hle t).restrictOpen
          (H.backwardSurvivorFootprintInterior first i hle K)) ∧
      G (H.time i.succ) = localPullMetric (H.event i).terminal.metric
        (H.backwardSurvivorFootprintMap first i hle K)
        (H.backwardSurvivorFootprintMap_isLocalDiffeomorph first i hle K) ∧
      IsSolutionOn ({ base := { metric := G } } :
        SolutionOn (I := ThreeModel) (M := H.backwardSurvivorFootprintInterior first i hle K)
          (RealTimeInterval.closed (H.time i.succ - θ / N.scale) (H.time i.succ)
            (sub_le_self _ (div_nonneg hθ.le N.scale_pos.le)))) ∧
      (∀ t ∈ Icc (H.time i.succ - θ / N.scale) (H.time i.succ), ∀ x : H.backwardSurvivorFootprintInterior first i hle K,
        normSq0S (G t) x 4 (metricRm04At (G t) x) ≤ B ^ 2) ∧
      IsCompact (riemannianClosedBallOf (G (H.time i.succ)) p
        (2*a / Real.sqrt N.scale)) ∧
      ∃ S : SolutionOn (I := ThreeModel)
          (M := H.backwardSurvivorFootprintInterior first i hle K)
          (RealTimeInterval.closed (-θ) 0 (neg_nonpos.mpr hθ.le)),
        (∀ s : ℝ, S.base.metric s = scaleMetric N.scale N.scale_pos
          (G (H.time i.succ + s / N.scale))) ∧
        S.base.metric 0 = scaleMetric N.scale N.scale_pos
          (localPullMetric (H.event i).terminal.metric
            (H.backwardSurvivorFootprintMap first i hle K)
            (H.backwardSurvivorFootprintMap_isLocalDiffeomorph first i hle K)) ∧
        IsSolutionOn S ∧
        IsCompact (riemannianClosedBallOf (S.base.metric 0) p (2*a)) ∧
        (∀ s ∈ Icc (-θ) 0, ∀ x ∈ riemannianClosedBallOf (S.base.metric 0) p (2*a),
          curvDerivNormSq 0 (S.base.metric s) x ≤ (8 * Real.sqrt 3) ^ 2) ∧
        (∀ m : ℕ, ∀ s ∈ Icc (-(θ / 2)) 0,
          ∀ x ∈ riemannianClosedBallOf (S.base.metric 0) p ((2*a) / 4),
            curvDerivNorm m (S.base.metric s) x ≤
              shiLocalUniformBound 3 m ((8 * Real.sqrt 3) * (θ / 4))
                (((2*a) / (4 * Real.exp (9 * (8 * Real.sqrt 3) * θ))) *
                  Real.sqrt (8 * Real.sqrt 3) /
                    (4 * Real.exp (9 * (8 * Real.sqrt 3) * (θ / 4)))) *
                  (8 * Real.sqrt 3) / Real.sqrt (θ / 4) ^ m) ∧
        ∃ (g' : SmoothRiemannianMetric ThreeModel
            (H.backwardSurvivorFootprintInterior first i hle K))
          (U : Set (H.backwardSurvivorFootprintInterior first i hle K)),
          RiemannianMetricComplete g' ∧ IsOpen U ∧
          riemannianClosedBallOf (S.base.metric 0) p (2*a) ⊆ U ∧
          (∀ x ∈ U, g'.inner x = (S.base.metric 0).inner x) ∧
          (∀ x (v : TangentSpace ThreeModel x),
            (S.base.metric 0).inner x v v ≤ g'.inner x v v) ∧
          (∀ m : ℕ, ∀ x ∈ U, curvDerivNorm m g' x = curvDerivNorm m (S.base.metric 0) x) ∧
          (∀ r : ℝ, 0 ≤ r → r < 2*a →
            riemannianClosedBallOf g' p r = riemannianClosedBallOf (S.base.metric 0) p r) ∧
          ∀ x ∈ riemannianClosedBallOf g' p (a / 8),
            Set.InjOn (fun v : TangentSpace ThreeModel x =>
              Geometry.Riemannian.Exponential.expMap g' x v)
              {v | Real.sqrt (g'.inner x v v) < η} := by
  obtain ⟨Q0,hQ0,hflow⟩ := exists_parabolic_historical_footprint_curvature_derivative_bounds hPhi
  obtain ⟨η,hη,hinj⟩ := exists_complete_historical_footprint_metric_with_injectivity
  refine ⟨Q0,η,hQ0,hη,?_⟩
  intro H i first hle δ₀ δ eps k N hQlarge hδ hδ1 hprecision hsmall hk a ha hpublic hfit
    q C hq hqQ hbound hpinch htrace θ hθ hc htime
  obtain ⟨p,G,hp,hslabs,hlast,hterminal,hsol,hRm,hcompact,S,hmetric,hzero,hS,hcpt,hcurv,hjets⟩ :=
    hflow N hQlarge hδ hδ1 hprecision hsmall hk a ha hpublic hfit hq hqQ
      hbound hpinch htrace hθ hc htime
  dsimp only
  refine ⟨p,G,hp,hslabs,hlast,hterminal,hsol,hRm,hcompact,S,hmetric,hzero,hS,hcpt,hcurv,hjets,?_⟩
  exact hinj N hprecision hk a ha hfit htrace p hp (S.base.metric 0) hzero hcpt
    (hcurv 0 ⟨by linarith,le_rfl⟩)

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
