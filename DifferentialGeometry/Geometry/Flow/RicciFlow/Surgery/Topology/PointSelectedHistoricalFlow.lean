import DifferentialGeometry.Geometry.Curvature.ComponentPointPicking
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.ParabolicTerminalBallFlow

noncomputable section
open Set Filter
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Tensor0SBundle
open scoped Manifold ContDiff Topology NNReal ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

theorem exists_point_selected_historical_flows
    (H : ℕ → RetainedCoreHistory.{u})
    (i : ∀ n, Fin (H n).eventCount)
    (p y : ∀ n, ((H n).toHistory.event (i n)).incoming.terminalRegularOpen)
    (A : ℕ → ℝ) (hA : ∀ n, 0 < A n) {D : ℝ} (hD : 0 ≤ D)
    (hcompact : ∀ n, IsCompact (riemannianClosedBallOf
      (scaleMetric (A n) (hA n) ((H n).toHistory.event (i n)).terminal.metric) (p n) (D + 1)))
    (hy : ∀ n, riemannianEDistOf
      (scaleMetric (A n) (hA n) ((H n).toHistory.event (i n)).terminal.metric) (p n) (y n) ≤
        ENNReal.ofReal D)
    (hpositive : ∀ n, 0 < metricScalarAt ((H n).toHistory.event (i n)).terminal.metric (y n))
    (hescape : Tendsto (fun n => metricScalarAt ((H n).toHistory.event (i n)).terminal.metric (y n) / A n)
      atTop atTop) :
    ∃ (x : ∀ n, ((H n).toHistory.event (i n)).incoming.terminalRegularOpen) (r : ℕ → ℝ),
      (∀ n, 0 < r n ∧ r n < (D + 1)/Real.sqrt (A n) ∧
        riemannianEDistOf ((H n).toHistory.event (i n)).terminal.metric (p n) (x n) <
          ENNReal.ofReal ((D + 1)/Real.sqrt (A n)) ∧
        0 < metricScalarAt ((H n).toHistory.event (i n)).terminal.metric (x n)) ∧
      Tendsto (fun n => metricScalarAt ((H n).toHistory.event (i n)).terminal.metric (x n) / A n)
        atTop atTop ∧
      Tendsto (fun n => metricScalarAt ((H n).toHistory.event (i n)).terminal.metric (x n) * r n ^ 2)
        atTop atTop ∧
      (∀ n, IsCompact (riemannianClosedBallOf ((H n).toHistory.event (i n)).terminal.metric (x n) (r n))) ∧
      (∀ n z, z ∈ riemannianClosedBallOf ((H n).toHistory.event (i n)).terminal.metric (x n) (r n) →
        riemannianEDistOf ((H n).toHistory.event (i n)).terminal.metric (p n) z <
          ENNReal.ofReal ((D + 1)/Real.sqrt (A n)) ∧
        metricScalarAt ((H n).toHistory.event (i n)).terminal.metric z ≤
          (16/9 : ℝ) * metricScalarAt ((H n).toHistory.event (i n)).terminal.metric (x n)) ∧
      ∀ n, ∀ (first : Fin (H n).eventCount) (hle : first.castSucc ≤ (i n).castSucc),
        let Q := metricScalarAt ((H n).toHistory.event (i n)).terminal.metric (x n)
    ∀ {q : ℝ} {C : ℝ≥0} (hq : 0 < q) (hqQ : q ≤ Q)
    {Phi : ℝ → ℝ} (hPhi : Perelman.AdmissiblePinchingFunction Phi)
    (hbound : ∀ j : Fin (H n).eventCount, first.castSucc ≤ j.castSucc → j.castSucc ≤ (i n).castSucc →
      ∀ y : ((H n).stage j.castSucc).Carrier, ∀ t ∈ Ioo ((H n).time j.castSucc) ((H n).time j.succ),
      q < ((H n).toHistory.event j).incoming.flow.scalar t y →
      |derivWithin (fun v => ((H n).toHistory.event j).incoming.flow.scalar v y) (Iic t) t| ≤
        C * ((H n).toHistory.event j).incoming.flow.scalar t y ^ 2)
    (hpinch : ∀ j : Fin (H n).eventCount, first.castSucc ≤ j.castSucc → j.castSucc ≤ (i n).castSucc →
      Perelman.PhiAlmostNonnegative ((H n).toHistory.event j).incoming.flow
        (Ico ((H n).time j.castSucc) ((H n).time j.succ)) Phi)
    {θ : ℝ} (hθ : 0 < θ)
    (hc : (H n).time (i n).succ-θ/Q ∈ Ico ((H n).time first.castSucc) ((H n).time first.succ))
    (hcap : ∀ j : Fin (H n).eventCount, (H n).time j.succ ∈ Ioc ((H n).time (i n).succ-θ/Q) ((H n).time (i n).castSucc) →
      ∀ y ∈ ((H n).toHistory.event j).capRegion,
        4 * Q ≤ metricScalarAt ((H n).toHistory.event j).outputMetric y)
    (_ : 6 * C * θ ≤ 1),
    let K := riemannianClosedBallOf ((H n).toHistory.event (i n)).terminal.metric (x n) (r n)
    IsCompact K ∧
    ∃ p : (H n).toHistory.backwardSurvivorFootprintInterior first.castSucc (i n) hle K,
      (H n).toHistory.backwardSurvivorFootprintMap first.castSucc (i n) hle K p = (x n) ∧
    range ((H n).toHistory.backwardSurvivorFootprintMap first.castSucc (i n) hle K) = interior K ∧
    ∃ G : ℝ → SmoothRiemannianMetric ThreeModel
        ((H n).toHistory.backwardSurvivorFootprintInterior first.castSucc (i n) hle K),
      (∀ (j : Fin (H n).eventCount) (hf : first.castSucc ≤ j.castSucc) (hl : j.succ ≤ (i n).castSucc),
        ∀ t ∈ Icc ((H n).time j.castSucc) ((H n).time j.succ),
          G t = (((H n).toHistory.backwardSurvivorSlabMetric first.castSucc (i n).castSucc hle j hf hl t).restrictOpen
            ((H n).toHistory.backwardSurvivorTerminalFace first.castSucc (i n) hle)).restrictOpen
              ((H n).toHistory.backwardSurvivorFootprintInterior first.castSucc (i n) hle K)) ∧
      (∀ t ∈ Icc ((H n).time (i n).castSucc) ((H n).time (i n).succ),
        G t = ((H n).toHistory.backwardSurvivorTerminalFaceMetric first.castSucc (i n) hle t).restrictOpen
          ((H n).toHistory.backwardSurvivorFootprintInterior first.castSucc (i n) hle K)) ∧
      G ((H n).time (i n).succ) = localPullMetric ((H n).toHistory.event (i n)).terminal.metric
        ((H n).toHistory.backwardSurvivorFootprintMap first.castSucc (i n) hle K)
        ((H n).toHistory.backwardSurvivorFootprintMap_isLocalDiffeomorph first.castSucc (i n) hle K) ∧
      IsSolutionOn ({ base := { metric := G } } :
        SolutionOn (I := ThreeModel) (M := (H n).toHistory.backwardSurvivorFootprintInterior first.castSucc (i n) hle K)
          (RealTimeInterval.closed ((H n).time (i n).succ-θ/Q) ((H n).time (i n).succ)
            (hc.2.le.trans ((H n).time_strictMono.monotone (by
              change first.val+1 ≤ (i n).val+1
              exact Nat.succ_le_succ hle))))) ∧
      (∀ t ∈ Icc ((H n).time (i n).succ-θ/Q) ((H n).time (i n).succ), ∀ z : (H n).toHistory.backwardSurvivorFootprintInterior first.castSucc (i n) hle K,
        normSq0S (G t) z 4 (metricRm04At (G t) z) ≤
          (4 * Real.sqrt 3 * (Q + Phi (4*Q) + Phi 0)) ^ 2) ∧
      (∀ r' : ℝ, r' < (r n) →
        IsCompact (riemannianClosedBallOf (G ((H n).time (i n).succ)) p r')) ∧
      ∃ S : SolutionOn (I := ThreeModel)
          (M := (H n).toHistory.backwardSurvivorFootprintInterior first.castSucc (i n) hle K)
          (RealTimeInterval.closed (-θ) 0 (neg_nonpos.mpr hθ.le)),
        (∀ s : ℝ, S.base.metric s = scaleMetric Q (lt_of_lt_of_le hq hqQ)
          (G ((H n).time (i n).succ+s/Q))) ∧
        IsSolutionOn S ∧
        IsCompact (riemannianClosedBallOf (S.base.metric 0) p (Real.sqrt Q * ((r n)/2))) ∧
        (∀ s ∈ Icc (-θ) 0, ∀ z,
          CheegerGromovCompactness.curvDerivNormSq 0 (S.base.metric s) z ≤
            (4 * Real.sqrt 3 * (Q + Phi (4*Q) + Phi 0) / Q)^2) ∧
        ∀ m : ℕ, ∀ s ∈ Icc (-(θ/2)) 0,
          ∀ z ∈ riemannianClosedBallOf (S.base.metric 0) p ((Real.sqrt Q * ((r n)/2))/4),
            CheegerGromovCompactness.curvDerivNorm m (S.base.metric s) z ≤
              shiLocalUniformBound 3 m
                ((4 * Real.sqrt 3 * (Q + Phi (4*Q) + Phi 0) / Q) * (θ/4))
                (((Real.sqrt Q*((r n)/2)) / (4 * Real.exp
                  (9 * (4 * Real.sqrt 3 * (Q + Phi (4*Q) + Phi 0) / Q) * θ))) *
                  Real.sqrt (4 * Real.sqrt 3 * (Q + Phi (4*Q) + Phi 0) / Q) /
                    (4 * Real.exp (9 * (4 * Real.sqrt 3 * (Q + Phi (4*Q) + Phi 0) / Q) * (θ/4)))) *
                (4 * Real.sqrt 3 * (Q + Phi (4*Q) + Phi 0) / Q) / Real.sqrt (θ/4)^m := by
  let g := fun n => ((H n).toHistory.event (i n)).terminal.metric
  obtain ⟨x,r,hr,hQ,hQr,hcpt,hbound⟩ := exists_rescaled_scalar_point_selection_in_component
    g p y A hA hD hcompact hy hpositive hescape
  refine ⟨x,r,hr,hQ,hQr,hcpt,hbound,?_⟩
  intro n first hle
  dsimp only
  intro q C hq hqQ Phi hPhi hderiv hpinch θ hθ hc hcap htime
  exact (H n).exists_parabolic_terminal_ball_flow first (i n) hle (x n) (hr n).1 (hcpt n)
    hq hqQ hPhi hderiv hpinch (fun z hz => ((hbound n z hz).2).trans (by nlinarith [(hr n).2.2.2])) hθ hc hcap htime

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
