import DifferentialGeometry.Geometry.Measure.LocalIsometry
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistorySurvivorIncomingCurvature
import DifferentialGeometry.Geometry.Metric.Distance.LocalPullCompactness
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.Noncollapsing.Parabolic
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.Noncollapsing.Invariance
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
    (H : RetainedCoreHistory.{u}) (first i : Fin H.eventCount) (hle : first.castSucc ≤ i.castSucc)
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

end

noncomputable section
open Set
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Tensor0SBundle
open scoped Manifold ContDiff ENNReal NNReal

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

private theorem exists_uniform_pinching_test_radius {Phi : ℝ → ℝ}
    (hPhi : AdmissiblePinchingFunction Phi) {θ : ℝ} (hθ : 0 < θ) :
    ∃ α : ℝ, 0 < α ∧ α ≤ 1 ∧ α ^ 2 ≤ θ ∧
      ∀ Q : ℝ, 1 ≤ Q →
        (α / Real.sqrt Q) ^ 2 ≤ θ / Q ∧
        (α / Real.sqrt Q) ^ 4 * (4 * Real.sqrt 3 * (Q + Phi (4 * Q) + Phi 0)) ^ 2 ≤ 1 := by
  let B := 4 * Real.sqrt 3 * (1 + Phi 4 + Phi 0)
  have hB : 0 < B := by dsimp only [B]; positivity [hPhi.pos 4, hPhi.pos 0]
  let α := min 1 (min θ (1 / B))
  have hα : 0 < α := lt_min zero_lt_one (lt_min hθ (one_div_pos.mpr hB))
  have hα1 : α ≤ 1 := min_le_left _ _
  have hαθ : α ≤ θ := (min_le_right _ _).trans (min_le_left _ _)
  have hαB : α ≤ 1 / B := (min_le_right _ _).trans (min_le_right _ _)
  have hαsq : α ^ 2 ≤ α := by nlinarith
  have hαsqB : α ^ 2 * B ≤ 1 :=
    (mul_le_mul_of_nonneg_right hαsq hB.le).trans ((le_div_iff₀ hB).mp hαB)
  refine ⟨α, hα, hα1, hαsq.trans hαθ, ?_⟩
  intro Q hQ
  have hQpos : 0 < Q := zero_lt_one.trans_le hQ
  have hsqrt : 0 < Real.sqrt Q := Real.sqrt_pos.mpr hQpos
  have hradsq : (α / Real.sqrt Q) ^ 2 = α ^ 2 / Q := by
    rw [div_pow, Real.sq_sqrt hQpos.le]
  constructor
  · rw [hradsq]
    exact div_le_div_of_nonneg_right (hαsq.trans hαθ) hQpos.le
  have hfour := hPhi.rescale_le hQ 4
  change Q⁻¹ * Phi (Q * 4) ≤ Phi 4 at hfour
  have hfour' := (inv_mul_le_iff₀ hQpos).mp hfour
  have hzero : Phi 0 ≤ Q * Phi 0 := by nlinarith [hPhi.pos 0]
  have hin : Q + Phi (4 * Q) + Phi 0 ≤ Q * (1 + Phi 4 + Phi 0) := by
    rw [mul_comm Q 4] at hfour'
    nlinarith
  have hbound : 4 * Real.sqrt 3 * (Q + Phi (4 * Q) + Phi 0) ≤ B * Q := by
    have hh := mul_le_mul_of_nonneg_left hin (by positivity : 0 ≤ 4 * Real.sqrt 3)
    dsimp only [B]
    nlinarith
  have hcurv : 0 ≤ 4 * Real.sqrt 3 * (Q + Phi (4 * Q) + Phi 0) := by
    positivity [hPhi.pos (4 * Q), hPhi.pos 0]
  have hb2 := pow_le_pow_left₀ hcurv hbound 2
  have heq : (α / Real.sqrt Q) ^ 4 * (B * Q) ^ 2 = (α ^ 2 * B) ^ 2 := by
    have hs := Real.sq_sqrt hQpos.le
    field_simp
    nlinarith [sq_nonneg (Real.sqrt Q)]
  calc
    (α / Real.sqrt Q) ^ 4 * (4 * Real.sqrt 3 * (Q + Phi (4 * Q) + Phi 0)) ^ 2
      ≤ (α / Real.sqrt Q) ^ 4 * (B * Q) ^ 2 := mul_le_mul_of_nonneg_left hb2 (by positivity)
    _ = (α ^ 2 * B) ^ 2 := heq
    _ ≤ 1 := by nlinarith [mul_nonneg (sq_nonneg α) hB.le]

end DifferentialGeometry.PDE.RicciFlow.Perelman

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.FlowMetricBall

private theorem isParabolicallyRmControlled_of_uniform_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [IsManifold I 1 M] [T2Space M]
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D)
    {time : D.FlowTime} (B : FlowMetricBall S time) {K : ℝ}
    (hinterval : Icc ((time : ℝ) - B.radius ^ 2) time ⊆ D.carrier)
    (hcurv : ∀ t ∈ D.carrier, ∀ x : M,
      normSq0S (S.base.metric t) x 4 (metricRm04At (S.base.metric t) x) ≤ K ^ 2)
    (hscale : B.radius ^ 4 * K ^ 2 ≤ 1) : B.IsParabolicallyRmControlled := by
  refine ⟨hinterval, ?_⟩
  intro t ht x hx
  have h := mul_le_mul_of_nonneg_left (hcurv t (hinterval ht) x)
    (by positivity : 0 ≤ B.radius ^ 4)
  exact h.trans hscale

end DifferentialGeometry.PDE.RicciFlow.Perelman.FlowMetricBall

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

private local instance (H : RetainedCoreHistory.{u})
    (first i : Fin H.eventCount) (hle : first.castSucc ≤ i.castSucc)
    (K : Set (H.toHistory.event i).incoming.terminalRegularOpen) :
    SigmaCompactSpace (H.toHistory.backwardSurvivorFootprintInterior first.castSucc i hle K) := by
  let : SigmaCompactSpace (H.toHistory.backwardSurvivorDomain first.castSucc i.castSucc hle) :=
    isSigmaCompact_iff_sigmaCompactSpace.mp
      (Geometry.isSigmaCompact_of_isOpen ThreeModel
        (H.toHistory.backwardSurvivorDomain first.castSucc i.castSucc hle).isOpen)
  let : SigmaCompactSpace (H.toHistory.backwardSurvivorTerminalFace first.castSucc i hle) :=
    isSigmaCompact_iff_sigmaCompactSpace.mp
      (Geometry.isSigmaCompact_of_isOpen ThreeModel
        (H.toHistory.backwardSurvivorTerminalFace first.castSucc i hle).isOpen)
  exact isSigmaCompact_iff_sigmaCompactSpace.mp
    (Geometry.isSigmaCompact_of_isOpen ThreeModel
      (H.toHistory.backwardSurvivorFootprintInterior first.castSucc i hle K).isOpen)

theorem RetainedCoreHistory.exists_parabolically_controlled_terminal_ball
    (H : RetainedCoreHistory.{u}) (first i : Fin H.eventCount) (hle : first.castSucc ≤ i.castSucc)
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
    {c : ℝ} (hc : c ∈ Ico (H.time first.castSucc) (H.time first.succ))
    (hcap : ∀ j : Fin H.eventCount, H.time j.succ ∈ Ioc c (H.time i.castSucc) →
      ∀ y ∈ (H.toHistory.event j).capRegion,
        4 * Q ≤ metricScalarAt (H.toHistory.event j).outputMetric y)
    (htime : 6 * C * (H.time i.succ - c) * Q ≤ 1)
    {ρ : ℝ} (hρ : 0 < ρ) (hρr : ρ < r)
    (hwindow : ρ ^ 2 ≤ H.time i.succ - c)
    (hscale : ρ ^ 4 * (4 * Real.sqrt 3 * (Q + Phi (4 * Q) + Phi 0)) ^ 2 ≤ 1) :
    let K := riemannianClosedBallOf (H.toHistory.event i).terminal.metric x r
    let hab : c ≤ H.time i.succ :=
      hc.2.le.trans (H.time_strictMono.monotone (by
        change first.val + 1 ≤ i.val + 1
        exact Nat.succ_le_succ hle))
    ∃ (p : H.toHistory.backwardSurvivorFootprintInterior first.castSucc i hle K)
      (S : SolutionOn (I := ThreeModel)
        (M := H.toHistory.backwardSurvivorFootprintInterior first.castSucc i hle K)
        (RealTimeInterval.closed c (H.time i.succ) hab)),
      H.toHistory.backwardSurvivorFootprintMap first.castSucc i hle K p = x ∧
      range (H.toHistory.backwardSurvivorFootprintMap first.castSucc i hle K) = interior K ∧
      IsSolutionOn S ∧
      S.base.metric (H.time i.succ) = localPullMetric (H.toHistory.event i).terminal.metric
        (H.toHistory.backwardSurvivorFootprintMap first.castSucc i hle K)
        (H.toHistory.backwardSurvivorFootprintMap_isLocalDiffeomorph first.castSucc i hle K) ∧
      (∀ (j : Fin H.eventCount) (hf : first.castSucc ≤ j.castSucc) (hl : j.succ ≤ i.castSucc),
        ∀ t ∈ Icc (H.time j.castSucc) (H.time j.succ),
          S.base.metric t = ((H.toHistory.backwardSurvivorSlabMetric first.castSucc i.castSucc hle j hf hl t).restrictOpen
            (H.toHistory.backwardSurvivorTerminalFace first.castSucc i hle)).restrictOpen
              (H.toHistory.backwardSurvivorFootprintInterior first.castSucc i hle K)) ∧
      (∀ t ∈ Icc (H.time i.castSucc) (H.time i.succ),
        S.base.metric t = (H.toHistory.backwardSurvivorTerminalFaceMetric first.castSucc i hle t).restrictOpen
          (H.toHistory.backwardSurvivorFootprintInterior first.castSucc i hle K)) ∧
      ∃ B : Perelman.FlowMetricBall S ⟨H.time i.succ, hab, le_rfl⟩,
        B.center = p ∧ B.radius = ρ ∧ B.IsParabolicallyRmControlled ∧
        B.set = riemannianBallOf (S.base.metric (H.time i.succ)) p ρ ∧
        H.toHistory.backwardSurvivorFootprintMap first.castSucc i hle K '' B.set =
          riemannianBallOf (H.toHistory.event i).terminal.metric x ρ ∧
        IsCompact (riemannianClosedBallOf (S.base.metric (H.time i.succ)) p ρ) := by
  intro K hab
  obtain ⟨_, p, hp, hrange, G, hslabs, hlast, hterminal, hsol, hRm, hcompact'⟩ :=
    H.exists_terminal_ball_flow first i hle x hr hcompact hq hqQ hPhi hbound hpinch hscalar
      hc hcap htime
  let S : SolutionOn (I := ThreeModel)
      (M := H.toHistory.backwardSurvivorFootprintInterior first.castSucc i hle K)
      (RealTimeInterval.closed c (H.time i.succ) hab) := { base := { metric := G } }
  let B : Perelman.FlowMetricBall S ⟨H.time i.succ, hab, le_rfl⟩ := ⟨p, ρ, hρ⟩
  have hinterval : Icc (H.time i.succ - ρ ^ 2) (H.time i.succ) ⊆ Icc c (H.time i.succ) := by
    intro t ht
    exact ⟨by linarith [ht.1], ht.2⟩
  have htest : B.IsParabolicallyRmControlled :=
    Perelman.FlowMetricBall.isParabolicallyRmControlled_of_uniform_bound S B hinterval hRm hscale
  have hmid : ρ < (ρ + r) / 2 := by linarith
  have hmidr : (ρ + r) / 2 < r := by linarith
  have himage : H.toHistory.backwardSurvivorFootprintMap first.castSucc i hle K '' B.set =
      riemannianBallOf (H.toHistory.event i).terminal.metric x ρ := by
    change _ '' riemannianBallOf (G (H.time i.succ)) p ρ = _
    rw [hterminal]
    have h := Geometry.Metric.image_riemannianBallOf_localPullMetric
      (H.toHistory.event i).terminal.metric
      (H.toHistory.backwardSurvivorFootprintMap first.castSucc i hle K)
      (H.toHistory.backwardSurvivorFootprintMap_isLocalDiffeomorph first.castSucc i hle K)
      (H.toHistory.backwardSurvivorFootprintMap_injective first.castSucc i hle K)
      p hρ hmid (hterminal ▸ hcompact' ((ρ + r) / 2) hmidr)
    exact h.trans (congrArg (fun y => riemannianBallOf (H.toHistory.event i).terminal.metric y ρ) hp)
  exact ⟨p, S, hp, hrange, hsol, hterminal, hslabs, hlast,
    B, rfl, rfl, htest, rfl, himage, hcompact' ρ hρr⟩


theorem exists_uniform_parabolically_controlled_terminal_ball_radius
    {Phi : ℝ → ℝ} (hPhi : Perelman.AdmissiblePinchingFunction Phi)
    {θ : ℝ} (hθ : 0 < θ) :
    ∃ α : ℝ, 0 < α ∧ α ≤ 1 ∧ α ^ 2 ≤ θ ∧
    ∀ (H : RetainedCoreHistory.{u})
      (first i : Fin H.eventCount) (hle : first.castSucc ≤ i.castSucc)
      (x : (H.toHistory.event i).incoming.terminalRegularOpen) {r : ℝ} (hr : 0 < r)
      (hcompact : IsCompact (riemannianClosedBallOf (H.toHistory.event i).terminal.metric x r))
      {q Q : ℝ} {C : ℝ≥0} (hq : 0 < q) (hqQ : q ≤ Q) (hQ : 1 ≤ Q),
    ( ∀ j : Fin H.eventCount, first.castSucc ≤ j.castSucc → j.castSucc ≤ i.castSucc →
      ∀ x : (H.stage j.castSucc).Carrier, ∀ t ∈ Ioo (H.time j.castSucc) (H.time j.succ),
      q < (H.toHistory.event j).incoming.flow.scalar t x →
      |derivWithin (fun v => (H.toHistory.event j).incoming.flow.scalar v x) (Iic t) t| ≤
        C * (H.toHistory.event j).incoming.flow.scalar t x ^ 2) →
    ( ∀ j : Fin H.eventCount, first.castSucc ≤ j.castSucc → j.castSucc ≤ i.castSucc →
      Perelman.PhiAlmostNonnegative (H.toHistory.event j).incoming.flow
        (Ico (H.time j.castSucc) (H.time j.succ)) Phi) →
    ( ∀ z ∈ riemannianClosedBallOf (H.toHistory.event i).terminal.metric x r,
      metricScalarAt (H.toHistory.event i).terminal.metric z ≤ 2 * Q) →
    ∀ (hc : H.time i.succ - θ / Q ∈ Ico (H.time first.castSucc) (H.time first.succ)),
    ( ∀ j : Fin H.eventCount, H.time j.succ ∈ Ioc (H.time i.succ - θ / Q) (H.time i.castSucc) →
      ∀ y ∈ (H.toHistory.event j).capRegion,
        4 * Q ≤ metricScalarAt (H.toHistory.event j).outputMetric y) →
    6 * C * θ ≤ 1 →
    α / Real.sqrt Q < r →
    let K := riemannianClosedBallOf (H.toHistory.event i).terminal.metric x r
    let hab : H.time i.succ - θ / Q ≤ H.time i.succ :=
      hc.2.le.trans (H.time_strictMono.monotone (by
        change first.val + 1 ≤ i.val + 1
        exact Nat.succ_le_succ hle))
    ∃ (p : H.toHistory.backwardSurvivorFootprintInterior first.castSucc i hle K)
      (S : SolutionOn (I := ThreeModel)
        (M := H.toHistory.backwardSurvivorFootprintInterior first.castSucc i hle K)
        (RealTimeInterval.closed (H.time i.succ - θ / Q) (H.time i.succ) hab)),
      H.toHistory.backwardSurvivorFootprintMap first.castSucc i hle K p = x ∧
      range (H.toHistory.backwardSurvivorFootprintMap first.castSucc i hle K) = interior K ∧
      IsSolutionOn S ∧
      S.base.metric (H.time i.succ) = localPullMetric (H.toHistory.event i).terminal.metric
        (H.toHistory.backwardSurvivorFootprintMap first.castSucc i hle K)
        (H.toHistory.backwardSurvivorFootprintMap_isLocalDiffeomorph first.castSucc i hle K) ∧
      (∀ (j : Fin H.eventCount) (hf : first.castSucc ≤ j.castSucc) (hl : j.succ ≤ i.castSucc),
        ∀ t ∈ Icc (H.time j.castSucc) (H.time j.succ),
          S.base.metric t = ((H.toHistory.backwardSurvivorSlabMetric first.castSucc i.castSucc hle j hf hl t).restrictOpen
            (H.toHistory.backwardSurvivorTerminalFace first.castSucc i hle)).restrictOpen
              (H.toHistory.backwardSurvivorFootprintInterior first.castSucc i hle K)) ∧
      (∀ t ∈ Icc (H.time i.castSucc) (H.time i.succ),
        S.base.metric t = (H.toHistory.backwardSurvivorTerminalFaceMetric first.castSucc i hle t).restrictOpen
          (H.toHistory.backwardSurvivorFootprintInterior first.castSucc i hle K)) ∧
      ∃ B : Perelman.FlowMetricBall S ⟨H.time i.succ, hab, le_rfl⟩,
        B.center = p ∧ B.radius = α / Real.sqrt Q ∧ B.IsParabolicallyRmControlled ∧
        B.set = riemannianBallOf (S.base.metric (H.time i.succ)) p (α / Real.sqrt Q) ∧
        H.toHistory.backwardSurvivorFootprintMap first.castSucc i hle K '' B.set =
          riemannianBallOf (H.toHistory.event i).terminal.metric x (α / Real.sqrt Q) ∧
        IsCompact (riemannianClosedBallOf (S.base.metric (H.time i.succ)) p (α / Real.sqrt Q)) := by
  obtain ⟨α, hα, hα1, hαθ, hchoice⟩ := Perelman.exists_uniform_pinching_test_radius hPhi hθ
  refine ⟨α, hα, hα1, hαθ, ?_⟩
  intro H first i hle x r hr hcompact q Q C hq hqQ hQ hbound hpinch hscalar hc hcap htime hradius
  have hQpos : 0 < Q := zero_lt_one.trans_le hQ
  have hrho : 0 < α / Real.sqrt Q := div_pos hα (Real.sqrt_pos.mpr hQpos)
  have htime' : 6 * C * (H.time i.succ - (H.time i.succ - θ / Q)) * Q ≤ 1 := by
    have heq : 6 * C * (H.time i.succ - (H.time i.succ - θ / Q)) * Q = 6 * C * θ := by
      field_simp
      ring
    rwa [heq]
  have hwindow : (α / Real.sqrt Q) ^ 2 ≤ H.time i.succ - (H.time i.succ - θ / Q) := by
    simpa only [sub_sub_cancel] using (hchoice Q hQ).1
  exact H.exists_parabolically_controlled_terminal_ball first i hle x hr hcompact hq hqQ hPhi
    hbound hpinch hscalar hc hcap htime' hrho hradius hwindow (hchoice Q hQ).2

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

end

noncomputable section
open Set
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Integral.Measure
open scoped Manifold ContDiff ENNReal NNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

universe u
variable (H : ObservedHistory.{u}) (first last : Fin (H.eventCount + 1)) (hle : first ≤ last)
  {s : ℝ} (G : (H.stage last).IncomingSlab (H.time last) s) (L : G.TerminalLimitMetric)

private local instance : SigmaCompactSpace G.terminalRegularOpen :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (Geometry.isSigmaCompact_of_isOpen ThreeModel G.terminalRegularOpen.isOpen)
private local instance (K : Set G.terminalRegularOpen) :
    SigmaCompactSpace (H.backwardSurvivorIncomingFootprint first last hle G K) := by
  let : SigmaCompactSpace (H.backwardSurvivorDomain first last hle) :=
    isSigmaCompact_iff_sigmaCompactSpace.mp
      (Geometry.isSigmaCompact_of_isOpen ThreeModel (H.backwardSurvivorDomain first last hle).isOpen)
  let : SigmaCompactSpace (H.backwardSurvivorIncomingDomain first last hle G) :=
    isSigmaCompact_iff_sigmaCompactSpace.mp
      (Geometry.isSigmaCompact_of_isOpen ThreeModel (H.backwardSurvivorIncomingDomain first last hle G).isOpen)
  exact isSigmaCompact_iff_sigmaCompactSpace.mp
    (Geometry.isSigmaCompact_of_isOpen ThreeModel
      (H.backwardSurvivorIncomingFootprint first last hle G K).isOpen)

theorem exists_parabolically_controlled_incoming_terminal_ball
    (hinit : G.flow.base.metric (H.time last) = H.initialMetric last)
    (x : G.terminalRegularOpen) {r : ℝ} (hr : 0 < r)
    (hcompact : IsCompact (riemannianClosedBallOf L.metric x r))
    {q Q : ℝ} {C : ℝ≥0} (hq : 0 < q) (hqQ : q ≤ Q)
    {Phi : ℝ → ℝ} (hPhi : Perelman.AdmissiblePinchingFunction Phi)
    (hbound : ∀ j : Fin H.eventCount, first ≤ j.castSucc → j.succ ≤ last →
      ∀ y : (H.stage j.castSucc).Carrier, ∀ t ∈ Ioo (H.time j.castSucc) (H.time j.succ),
      q < (H.event j).incoming.flow.scalar t y →
      |derivWithin (fun v => (H.event j).incoming.flow.scalar v y) (Iic t) t| ≤
        C * (H.event j).incoming.flow.scalar t y ^ 2)
    (hfinal : ∀ y ∈ riemannianClosedBallOf L.metric x r, ∀ t ∈ Ioo (H.time last) s, q < G.flow.scalar t y.val →
      |derivWithin (fun v => G.flow.scalar v y.val) (Iic t) t| ≤ C * G.flow.scalar t y.val ^ 2)
    (hpinch : ∀ j : Fin H.eventCount, first ≤ j.castSucc → j.succ ≤ last →
      Perelman.PhiAlmostNonnegative (H.event j).incoming.flow
        (Ico (H.time j.castSucc) (H.time j.succ)) Phi)
    (hpinchFinal : Perelman.PhiAlmostNonnegative G.flow (Ico (H.time last) s) Phi)
    (hscalar : ∀ y ∈ riemannianClosedBallOf L.metric x r, metricScalarAt L.metric y ≤ 2 * Q)
    (htrace : ∀ y ∈ riemannianClosedBallOf L.metric x r, Nonempty (BackwardPointTrace H first last hle y.val))
    {c : ℝ} (hc : H.time first ≤ c) (hcs : c ≤ s)
    (htime : 6 * C * (s - c) * Q ≤ 1)
    {ρ : ℝ} (hρ : 0 < ρ) (hρr : ρ < r)
    (hwindow : ρ ^ 2 ≤ s - c)
    (hscale : ρ ^ 4 * (4 * Real.sqrt 3 * (Q + Phi (4 * Q) + Phi 0)) ^ 2 ≤ 1) :
    let K := riemannianClosedBallOf L.metric x r
    ∃ (p : H.backwardSurvivorIncomingFootprint first last hle G K)
      (S : SolutionOn (I := ThreeModel)
        (M := H.backwardSurvivorIncomingFootprint first last hle G K)
        (RealTimeInterval.closed c s hcs)),
      H.backwardSurvivorIncomingFootprintMap first last hle G K p = x ∧
      range (H.backwardSurvivorIncomingFootprintMap first last hle G K) = interior K ∧
      IsSolutionOn S ∧
      S.base.metric s = localPullMetric L.metric
        (H.backwardSurvivorIncomingFootprintMap first last hle G K)
        (H.backwardSurvivorIncomingFootprintMap_isLocalDiffeomorph first last hle G K) ∧
      (∀ (j : Fin H.eventCount) (hf : first ≤ j.castSucc) (hl : j.succ ≤ last),
        ∀ t ∈ Icc (H.time j.castSucc) (H.time j.succ),
          S.base.metric t = ((H.backwardSurvivorSlabMetric first last hle j hf hl t).restrictOpen
            (H.backwardSurvivorIncomingDomain first last hle G)).restrictOpen
              (H.backwardSurvivorIncomingFootprint first last hle G K)) ∧
      (∀ t ∈ Icc (H.time last) s,
        S.base.metric t = (H.backwardSurvivorIncomingMetric first last hle G L t).restrictOpen
          (H.backwardSurvivorIncomingFootprint first last hle G K)) ∧
      ∃ B : Perelman.FlowMetricBall S ⟨s, hcs, le_rfl⟩,
        B.center = p ∧ B.radius = ρ ∧ B.IsParabolicallyRmControlled ∧
        B.set = riemannianBallOf (S.base.metric s) p ρ ∧
        H.backwardSurvivorIncomingFootprintMap first last hle G K '' B.set =
          riemannianBallOf L.metric x ρ ∧
        B.volume = riemannianVolumeMeasure ThreeModel G.terminalRegularOpen L.metric
          (riemannianBallOf L.metric x ρ) ∧
        IsCompact (riemannianClosedBallOf (S.base.metric s) p ρ) := by
  intro K
  obtain ⟨hrange, gflow, hslabs, hlast, hterminal, hsol, hRm⟩ :=
    H.exists_backwardSurvivorIncomingFootprint_curvature_bound first last hle G L hinit K
      hq hqQ hPhi hbound hfinal hpinch hpinchFinal hscalar htrace hc hcs htime
  obtain ⟨p, hp, hcompact'⟩ := H.exists_incomingFootprint_point_isCompact_terminal_closedBall
    first last hle G L x hr hcompact hrange (gflow s) hterminal
  let S : SolutionOn (I := ThreeModel)
      (M := H.backwardSurvivorIncomingFootprint first last hle G K)
      (RealTimeInterval.closed c s hcs) := { base := { metric := gflow } }
  let B : Perelman.FlowMetricBall S ⟨s, hcs, le_rfl⟩ := ⟨p, ρ, hρ⟩
  have hinterval : Icc (s - ρ ^ 2) s ⊆ Icc c s := by
    intro t ht
    exact ⟨by linarith [ht.1], ht.2⟩
  have htest : B.IsParabolicallyRmControlled := by
    refine ⟨hinterval, ?_⟩
    intro t ht z hz
    exact (mul_le_mul_of_nonneg_left (hRm t (hinterval ht) z) (by positivity)).trans hscale
  have hmid : ρ < (ρ + r) / 2 := by linarith
  have hmidr : (ρ + r) / 2 < r := by linarith
  have hcompactmid : IsCompact (riemannianClosedBallOf
      (localPullMetric L.metric (H.backwardSurvivorIncomingFootprintMap first last hle G K)
        (H.backwardSurvivorIncomingFootprintMap_isLocalDiffeomorph first last hle G K)) p ((ρ + r) / 2)) :=
    hterminal ▸ hcompact' ((ρ + r) / 2) hmidr
  have himage : H.backwardSurvivorIncomingFootprintMap first last hle G K '' B.set =
      riemannianBallOf L.metric x ρ := by
    change _ '' riemannianBallOf (gflow s) p ρ = _
    rw [hterminal]
    have h := Geometry.Metric.image_riemannianBallOf_localPullMetric L.metric
      (H.backwardSurvivorIncomingFootprintMap first last hle G K)
      (H.backwardSurvivorIncomingFootprintMap_isLocalDiffeomorph first last hle G K)
      (H.backwardSurvivorIncomingFootprintMap_injective first last hle G K)
      p hρ hmid hcompactmid
    exact h.trans (congrArg (fun y => riemannianBallOf L.metric y ρ) hp)
  have hvolume : B.volume = riemannianVolumeMeasure ThreeModel G.terminalRegularOpen L.metric
      (riemannianBallOf L.metric x ρ) := by
    rw [Perelman.FlowMetricBall.volume_eq_riemannianVolumeMeasure]
    change riemannianVolumeMeasure _ _ (gflow s) (riemannianBallOf (gflow s) p ρ) = _
    rw [hterminal]
    have h := Geometry.Measure.riemannianVolumeMeasure_ball_eq_of_localPullMetric L.metric
      (H.backwardSurvivorIncomingFootprintMap first last hle G K)
      (H.backwardSurvivorIncomingFootprintMap_isLocalDiffeomorph first last hle G K)
      (H.backwardSurvivorIncomingFootprintMap_injective first last hle G K)
      p hρ hmid hcompactmid
    exact h.trans (congrArg (fun y => riemannianVolumeMeasure ThreeModel G.terminalRegularOpen L.metric
      (riemannianBallOf L.metric y ρ)) hp)
  exact ⟨p, S, hp, hrange, hsol, hterminal, hslabs, hlast,
    B, rfl, rfl, htest, rfl, himage, hvolume, hcompact' ρ hρr⟩


theorem exists_uniform_parabolically_controlled_incoming_terminal_ball_radius
    {Phi : ℝ → ℝ} (hPhi : Perelman.AdmissiblePinchingFunction Phi)
    {θ : ℝ} (hθ : 0 < θ) :
    ∃ α : ℝ, 0 < α ∧ α ≤ 1 ∧ α ^ 2 ≤ θ ∧
    ∀ (H : ObservedHistory.{u}) (first last : Fin (H.eventCount + 1)) (hle : first ≤ last)
      {s : ℝ} (G : (H.stage last).IncomingSlab (H.time last) s) (L : G.TerminalLimitMetric)
      (x : G.terminalRegularOpen) {r q Q : ℝ} {C : ℝ≥0} (hQ : 1 ≤ Q),
    G.flow.base.metric (H.time last) = H.initialMetric last →
    0 < r → IsCompact (riemannianClosedBallOf L.metric x r) →
    0 < q → q ≤ Q →
    (∀ j : Fin H.eventCount, first ≤ j.castSucc → j.succ ≤ last →
      ∀ y : (H.stage j.castSucc).Carrier, ∀ t ∈ Ioo (H.time j.castSucc) (H.time j.succ),
      q < (H.event j).incoming.flow.scalar t y →
      |derivWithin (fun v => (H.event j).incoming.flow.scalar v y) (Iic t) t| ≤
        C * (H.event j).incoming.flow.scalar t y ^ 2) →
    (∀ y ∈ riemannianClosedBallOf L.metric x r, ∀ t ∈ Ioo (H.time last) s, q < G.flow.scalar t y.val →
      |derivWithin (fun v => G.flow.scalar v y.val) (Iic t) t| ≤ C * G.flow.scalar t y.val ^ 2) →
    (∀ j : Fin H.eventCount, first ≤ j.castSucc → j.succ ≤ last →
      Perelman.PhiAlmostNonnegative (H.event j).incoming.flow
        (Ico (H.time j.castSucc) (H.time j.succ)) Phi) →
    (Perelman.PhiAlmostNonnegative G.flow (Ico (H.time last) s) Phi) →
    (∀ y ∈ riemannianClosedBallOf L.metric x r, metricScalarAt L.metric y ≤ 2 * Q) →
    (∀ y ∈ riemannianClosedBallOf L.metric x r, Nonempty (BackwardPointTrace H first last hle y.val)) →
    H.time first ≤ s - θ / Q →
    6 * C * θ ≤ 1 →
    α / Real.sqrt Q < r →
    let K := riemannianClosedBallOf L.metric x r
    ∃ (p : H.backwardSurvivorIncomingFootprint first last hle G K)
      (S : SolutionOn (I := ThreeModel)
        (M := H.backwardSurvivorIncomingFootprint first last hle G K)
        (RealTimeInterval.closed (s - θ / Q) s (sub_le_self s (div_nonneg hθ.le (zero_le_one.trans hQ))))),
      H.backwardSurvivorIncomingFootprintMap first last hle G K p = x ∧
      range (H.backwardSurvivorIncomingFootprintMap first last hle G K) = interior K ∧
      IsSolutionOn S ∧
      S.base.metric s = localPullMetric L.metric
        (H.backwardSurvivorIncomingFootprintMap first last hle G K)
        (H.backwardSurvivorIncomingFootprintMap_isLocalDiffeomorph first last hle G K) ∧
      (∀ (j : Fin H.eventCount) (hf : first ≤ j.castSucc) (hl : j.succ ≤ last),
        ∀ t ∈ Icc (H.time j.castSucc) (H.time j.succ),
          S.base.metric t = ((H.backwardSurvivorSlabMetric first last hle j hf hl t).restrictOpen
            (H.backwardSurvivorIncomingDomain first last hle G)).restrictOpen
              (H.backwardSurvivorIncomingFootprint first last hle G K)) ∧
      (∀ t ∈ Icc (H.time last) s,
        S.base.metric t = (H.backwardSurvivorIncomingMetric first last hle G L t).restrictOpen
          (H.backwardSurvivorIncomingFootprint first last hle G K)) ∧
      ∃ B : Perelman.FlowMetricBall S ⟨s, sub_le_self s (div_nonneg hθ.le (zero_le_one.trans hQ)), le_rfl⟩,
        B.center = p ∧ B.radius = α / Real.sqrt Q ∧ B.IsParabolicallyRmControlled ∧
        B.set = riemannianBallOf (S.base.metric s) p (α / Real.sqrt Q) ∧
        H.backwardSurvivorIncomingFootprintMap first last hle G K '' B.set =
          riemannianBallOf L.metric x (α / Real.sqrt Q) ∧
        B.volume = riemannianVolumeMeasure ThreeModel G.terminalRegularOpen L.metric
          (riemannianBallOf L.metric x (α / Real.sqrt Q)) ∧
        IsCompact (riemannianClosedBallOf (S.base.metric s) p (α / Real.sqrt Q)) := by
  obtain ⟨α, hα, hα1, hαθ, hchoice⟩ := Perelman.exists_uniform_pinching_test_radius hPhi hθ
  refine ⟨α, hα, hα1, hαθ, ?_⟩
  intro H first last hle s G L x r q Q C hQ hinit hr hcompact hq hqQ
    hbound hfinal hpinch hpinchFinal hscalar htrace hc htime hradius
  have hQpos : 0 < Q := zero_lt_one.trans_le hQ
  have hrho : 0 < α / Real.sqrt Q := div_pos hα (Real.sqrt_pos.mpr hQpos)
  have hcs : s - θ / Q ≤ s := sub_le_self s (div_nonneg hθ.le hQpos.le)
  have htime' : 6 * C * (s - (s - θ / Q)) * Q ≤ 1 := by
    have heq : 6 * C * (s - (s - θ / Q)) * Q = 6 * C * θ := by field_simp; ring
    rwa [heq]
  have hwindow : (α / Real.sqrt Q) ^ 2 ≤ s - (s - θ / Q) := by
    simpa only [sub_sub_cancel] using (hchoice Q hQ).1
  exact H.exists_parabolically_controlled_incoming_terminal_ball first last hle G L hinit x hr hcompact
    hq hqQ hPhi hbound hfinal hpinch hpinchFinal hscalar htrace hc hcs htime' hrho hradius
    hwindow (hchoice Q hQ).2

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory
