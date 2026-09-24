import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TerminalBallFlow
import DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.Shi.Derivatives.ParabolicTerminalBall

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

theorem RetainedCoreHistory.exists_parabolic_terminal_ball_flow
    {P : OrientedThreeStage.{u}} (H : RetainedCoreHistory P) (first i : Fin H.eventCount) (hle : first.castSucc ≤ i.castSucc)
    (x : (H.toHistory.event i).incoming.terminalRegularOpen) {r : ℝ} (hr : 0 < r)
    (hcompact : IsCompact (riemannianClosedBallOf (H.toHistory.event i).terminal.metric x r))
    {q Q : ℝ} {C : ℝ≥0} (hq : 0 < q) (hqQ : q ≤ Q)
    {Phi : ℝ → ℝ} (hPhi : Perelman.AdmissiblePinchingFunction Phi)
    (hbound : ∀ j : Fin H.eventCount, first.castSucc ≤ j.castSucc → j.castSucc ≤ i.castSucc →
      ∀ x : (H.stage j.castSucc).Carrier, ∀ t ∈ Ioo (H.time j.castSucc) (H.time j.succ),
      q < (H.toHistory.event j).incoming.flow.scalar t x →
      |derivWithin (fun v => (H.toHistory.event j).incoming.flow.scalar v x) (Iic t) t| ≤
        C * (H.toHistory.event j).incoming.flow.scalar t x ^ 2)
    (hpinch : ∀ j : Fin H.eventCount, first.castSucc ≤ j.castSucc → j.castSucc ≤ i.castSucc →
      Perelman.PhiAlmostNonnegative (H.toHistory.event j).incoming.flow
        (Ico (H.time j.castSucc) (H.time j.succ)) Phi)
    (hscalar : ∀ z ∈ riemannianClosedBallOf (H.toHistory.event i).terminal.metric x r,
      metricScalarAt (H.toHistory.event i).terminal.metric z ≤ 2 * Q)
    {θ : ℝ} (hθ : 0 < θ)
    (hc : H.time i.succ-θ/Q ∈ Ico (H.time first.castSucc) (H.time first.succ))
    (hcap : ∀ j : Fin H.eventCount, H.time j.succ ∈ Ioc (H.time i.succ-θ/Q) (H.time i.castSucc) →
      ∀ y ∈ (H.toHistory.event j).capRegion,
        4 * Q ≤ metricScalarAt (H.toHistory.event j).outputMetric y)
    (htime : 6 * C * θ ≤ 1) :
    let K := riemannianClosedBallOf (H.toHistory.event i).terminal.metric x r
    IsCompact K ∧
    ∃ p : H.toHistory.backwardSurvivorFootprintInterior first.castSucc i hle K,
      H.toHistory.backwardSurvivorFootprintMap first.castSucc i hle K p = x ∧
    range (H.toHistory.backwardSurvivorFootprintMap first.castSucc i hle K) = interior K ∧
    ∃ G : ℝ → SmoothRiemannianMetric ThreeModel
        (H.toHistory.backwardSurvivorFootprintInterior first.castSucc i hle K),
      (∀ (j : Fin H.eventCount) (hf : first.castSucc ≤ j.castSucc) (hl : j.succ ≤ i.castSucc),
        ∀ t ∈ Icc (H.time j.castSucc) (H.time j.succ),
          G t = ((H.toHistory.backwardSurvivorSlabMetric first.castSucc i.castSucc hle j hf hl t).restrictOpen
            (H.toHistory.backwardSurvivorTerminalFace first.castSucc i hle)).restrictOpen
              (H.toHistory.backwardSurvivorFootprintInterior first.castSucc i hle K)) ∧
      (∀ t ∈ Icc (H.time i.castSucc) (H.time i.succ),
        G t = (H.toHistory.backwardSurvivorTerminalFaceMetric first.castSucc i hle t).restrictOpen
          (H.toHistory.backwardSurvivorFootprintInterior first.castSucc i hle K)) ∧
      G (H.time i.succ) = localPullMetric (H.toHistory.event i).terminal.metric
        (H.toHistory.backwardSurvivorFootprintMap first.castSucc i hle K)
        (H.toHistory.backwardSurvivorFootprintMap_isLocalDiffeomorph first.castSucc i hle K) ∧
      IsSolutionOn ({ base := { metric := G } } :
        SolutionOn (I := ThreeModel) (M := H.toHistory.backwardSurvivorFootprintInterior first.castSucc i hle K)
          (RealTimeInterval.closed (H.time i.succ-θ/Q) (H.time i.succ)
            (hc.2.le.trans (H.time_strictMono.monotone (by
              change first.val+1 ≤ i.val+1
              exact Nat.succ_le_succ hle))))) ∧
      (∀ t ∈ Icc (H.time i.succ-θ/Q) (H.time i.succ), ∀ x : H.toHistory.backwardSurvivorFootprintInterior first.castSucc i hle K,
        normSq0S (G t) x 4 (metricRm04At (G t) x) ≤
          (4 * Real.sqrt 3 * (Q + Phi (4*Q) + Phi 0)) ^ 2) ∧
      (∀ r' : ℝ, r' < r →
        IsCompact (riemannianClosedBallOf (G (H.time i.succ)) p r')) ∧
      ∃ S : SolutionOn (I := ThreeModel)
          (M := H.toHistory.backwardSurvivorFootprintInterior first.castSucc i hle K)
          (RealTimeInterval.closed (-θ) 0 (neg_nonpos.mpr hθ.le)),
        (∀ s : ℝ, S.base.metric s = scaleMetric Q (lt_of_lt_of_le hq hqQ)
          (G (H.time i.succ+s/Q))) ∧
        IsSolutionOn S ∧
        IsCompact (riemannianClosedBallOf (S.base.metric 0) p (Real.sqrt Q * (r/2))) ∧
        (∀ s ∈ Icc (-θ) 0, ∀ z,
          CheegerGromovCompactness.curvDerivNormSq 0 (S.base.metric s) z ≤
            (4 * Real.sqrt 3 * (Q + Phi (4*Q) + Phi 0) / Q)^2) ∧
        ∀ m : ℕ, ∀ s ∈ Icc (-(θ/2)) 0,
          ∀ z ∈ riemannianClosedBallOf (S.base.metric 0) p ((Real.sqrt Q * (r/2))/4),
            CheegerGromovCompactness.curvDerivNorm m (S.base.metric s) z ≤
              shiLocalUniformBound 3 m
                ((4 * Real.sqrt 3 * (Q + Phi (4*Q) + Phi 0) / Q) * (θ/4))
                (((Real.sqrt Q*(r/2)) / (4 * Real.exp
                  (9 * (4 * Real.sqrt 3 * (Q + Phi (4*Q) + Phi 0) / Q) * θ))) *
                  Real.sqrt (4 * Real.sqrt 3 * (Q + Phi (4*Q) + Phi 0) / Q) /
                    (4 * Real.exp (9 * (4 * Real.sqrt 3 * (Q + Phi (4*Q) + Phi 0) / Q) * (θ/4)))) *
                (4 * Real.sqrt 3 * (Q + Phi (4*Q) + Phi 0) / Q) / Real.sqrt (θ/4)^m := by
  have hQ : 0 < Q := hq.trans_le hqQ
  have htime' : 6*C*(H.time i.succ-(H.time i.succ-θ/Q))*Q ≤ 1 := by
    have heq : 6*C*(H.time i.succ-(H.time i.succ-θ/Q))*Q = 6*C*θ := by field_simp; ring
    rwa [heq]
  obtain ⟨hcpt,p,hp,hrange,G,hslabs,hlast,hterminal,hsol,hRm,hball⟩ :=
    H.exists_terminal_ball_flow first i hle x hr hcompact hq hqQ hPhi hbound hpinch hscalar
      hc hcap htime'
  dsimp only
  refine ⟨hcpt,p,hp,hrange,G,hslabs,hlast,hterminal,hsol,hRm,hball,?_⟩
  let K := riemannianClosedBallOf (H.toHistory.event i).terminal.metric x r
  let c := H.time i.succ-θ/Q
  have hcs : c ≤ H.time i.succ := sub_le_self _ (div_nonneg hθ.le hQ.le)
  let T : SolutionOn (I := ThreeModel)
      (M := H.toHistory.backwardSurvivorFootprintInterior first.castSucc i hle K)
      (RealTimeInterval.closed c (H.time i.succ) hcs) := {base.metric := G}
  let S := T.parabolicClosedWindow (H.time i.succ) Q θ hQ hθ.le
  let B := 4 * Real.sqrt 3 * (Q + Phi (4*Q) + Phi 0)
  have hB : 0 < B := by
    have hp4 := hPhi.pos (4*Q)
    have hp0 := hPhi.pos 0
    dsimp only [B]
    positivity
  have hradius : 0 < Real.sqrt Q * (r/2) := mul_pos (Real.sqrt_pos.mpr hQ) (half_pos hr)
  have heq : (Real.sqrt Q * (r/2))/Real.sqrt Q = r/2 := by field_simp
  have hcpt' : IsCompact (riemannianClosedBallOf (T.base.metric (H.time i.succ)) p
      ((Real.sqrt Q * (r/2))/Real.sqrt Q)) := by
    rw [heq]
    exact hball (r/2) (by linarith)
  have hcurv : ∀ t ∈ Icc c (H.time i.succ),
      ∀ z ∈ riemannianClosedBallOf (T.base.metric (H.time i.succ)) p
        ((Real.sqrt Q*(r/2))/Real.sqrt Q),
          CheegerGromovCompactness.curvDerivNormSq 0 (T.base.metric t) z ≤ (B/Q*Q)^2 := by
    intro t ht z _
    rw [div_mul_cancel₀ B hQ.ne']
    exact hRm t ht z
  let _ : SigmaCompactSpace (H.toHistory.backwardSurvivorFootprintInterior first.castSucc i hle K) := by
    let _ : SigmaCompactSpace (H.toHistory.backwardSurvivorDomain first.castSucc i.castSucc hle) :=
      isSigmaCompact_iff_sigmaCompactSpace.mp
        (Geometry.isSigmaCompact_of_isOpen ThreeModel
          (H.toHistory.backwardSurvivorDomain first.castSucc i.castSucc hle).isOpen)
    let _ : SigmaCompactSpace (H.toHistory.backwardSurvivorTerminalFace first.castSucc i hle) :=
      isSigmaCompact_iff_sigmaCompactSpace.mp
        (Geometry.isSigmaCompact_of_isOpen ThreeModel
          (H.toHistory.backwardSurvivorTerminalFace first.castSucc i hle).isOpen)
    exact isSigmaCompact_iff_sigmaCompactSpace.mp
      (Geometry.isSigmaCompact_of_isOpen ThreeModel
        (H.toHistory.backwardSurvivorFootprintInterior first.castSucc i hle K).isOpen)
  have hh := shi_curvDerivNorm_parabolicClosedWindow_on_terminal_ball T hsol hQ hθ
    (div_pos hB hQ) hradius Subset.rfl Subset.rfl p hcpt' hcurv
  refine ⟨S,fun _ => rfl,hh.1,hh.2.1,?_,?_⟩
  · intro s hs z
    change CheegerGromovCompactness.curvDerivNormSq 0
      (scaleMetric Q hQ (G (H.time i.succ+s/Q))) z ≤ (B/Q)^2
    rw [CheegerGromovCompactness.curvDerivNormSq_scaleMetric]
    have ht : H.time i.succ+s/Q ∈ Icc c (H.time i.succ) := by
      have hlo := div_le_div_of_nonneg_right hs.1 hQ.le
      have hhi := div_le_div_of_nonneg_right hs.2 hQ.le
      simp only [neg_div,zero_div] at hlo hhi
      dsimp only [c]
      constructor <;> linarith
    calc
      Q⁻¹^(0+2) * CheegerGromovCompactness.curvDerivNormSq 0
        (G (H.time i.succ+s/Q)) z ≤ Q⁻¹^(0+2)*B^2 :=
          mul_le_mul_of_nonneg_left (hRm _ ht z) (by positivity)
      _ = (B/Q)^2 := by simp only [Nat.zero_add,div_pow,inv_pow]; ring
  · have hdim : Module.finrank ℝ ThreeSpace = 3 := by simp [ThreeSpace]
    simpa only [hdim,Nat.cast_ofNat,show (3 : ℝ)^2=9 by norm_num] using hh.2.2.2

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
