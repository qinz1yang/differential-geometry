import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistoricalNeckShi
import DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.Shi.Derivatives.ParabolicTerminalBall
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.PinchingDatum

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

theorem exists_parabolic_historical_footprint_curvature_derivative_bounds
    {Phi : ℝ → ℝ} (hPhi : Perelman.AdmissiblePinchingFunction Phi) :
    ∃ Q0 : ℝ, 0 < Q0 ∧
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
        ∀ m : ℕ, ∀ s ∈ Icc (-(θ / 2)) 0,
          ∀ x ∈ riemannianClosedBallOf (S.base.metric 0) p ((2*a) / 4),
            curvDerivNorm m (S.base.metric s) x ≤
              shiLocalUniformBound 3 m ((8 * Real.sqrt 3) * (θ / 4))
                (((2*a) / (4 * Real.exp (9 * (8 * Real.sqrt 3) * θ))) *
                  Real.sqrt (8 * Real.sqrt 3) /
                    (4 * Real.exp (9 * (8 * Real.sqrt 3) * (θ / 4)))) *
                  (8 * Real.sqrt 3) / Real.sqrt (θ / 4) ^ m := by
  obtain ⟨Q0,hQ0,hQbound⟩ := Perelman.exists_forall_rescalePinchingFunction_le
    (B := 4) hPhi (by norm_num : (0 : ℝ) < 1 / 2)
  refine ⟨Q0,hQ0,?_⟩
  intro H i first hle δ₀ δ eps k N hQlarge hδ hδ1 hprecision hsmall hk a ha hpublic hfit
    q C hq hqQ hbound hpinch htrace θ hθ hc htime
  have hpinch4 := hQbound N.scale hQlarge 4 ⟨by norm_num,le_rfl⟩
  have hpinch0 := hQbound N.scale hQlarge 0 ⟨le_rfl,by norm_num⟩
  simp only [Perelman.rescalePinchingFunction, mul_zero, inv_mul_eq_div] at hpinch4 hpinch0
  rw [div_le_iff₀ N.scale_pos] at hpinch4 hpinch0
  have hp : Phi (4*N.scale) + Phi 0 ≤ N.scale := by
    rw [mul_comm N.scale 4] at hpinch4
    linarith
  let c := H.time i.succ - θ / N.scale
  have hcs : c < H.time i.succ := sub_lt_self _ (div_pos hθ N.scale_pos)
  have hbudget : 6 * C * (H.time i.succ - c) * N.scale ≤ 1 := by
    have heq : 6 * C * (H.time i.succ - c) * N.scale = 6 * C * θ := by
      dsimp only [c]
      field_simp [N.scale_pos.ne']
      ring
    rwa [heq]
  obtain ⟨p,G,hpcenter,hslabs,hlast,hterminal,hsol,hRm,hcompact,_⟩ :=
    N.exists_historical_footprint_curvature_derivative_bounds hδ hδ1 hprecision hsmall hk
      a ha hpublic hfit hq hqQ hPhi hbound hpinch htrace hc hcs hbudget
  dsimp only
  let K := N.chart '' {z : neckBuffer δ₀ | -(3*a) ≤ z.val.2 ∧ z.val.2 ≤ 3*a}
  let Gsol : SolutionOn (I := ThreeModel)
      (M := H.backwardSurvivorFootprintInterior first i hle K)
      (RealTimeInterval.closed c (H.time i.succ) hcs.le) := { base := { metric := G } }
  let S := Gsol.parabolicClosedWindow (H.time i.succ) N.scale θ N.scale_pos hθ.le
  have hcurv : ∀ t ∈ Icc (H.time i.succ - θ / N.scale) (H.time i.succ),
      ∀ x ∈ riemannianClosedBallOf (Gsol.base.metric (H.time i.succ)) p
          ((2*a) / Real.sqrt N.scale),
        curvDerivNormSq 0 (Gsol.base.metric t) x ≤ ((8 * Real.sqrt 3) * N.scale) ^ 2 := by
    intro t ht x _
    have hh := hRm t ht x
    have hB : 4 * Real.sqrt 3 * (N.scale + Phi (4*N.scale) + Phi 0) ≤
        (8 * Real.sqrt 3) * N.scale := by
      nlinarith only [mul_le_mul_of_nonneg_left hp (by positivity : 0 ≤ 4 * Real.sqrt 3)]
    have hpos4 := hPhi.pos (4*N.scale)
    have hpos0 := hPhi.pos 0
    have hscale := N.scale_pos
    exact hh.trans (pow_le_pow_left₀ (by positivity) hB 2)
  have hh := shi_curvDerivNorm_parabolicClosedWindow_on_terminal_ball Gsol hsol
    N.scale_pos hθ (by positivity : 0 < 8 * Real.sqrt 3) (by linarith : 0 < 2*a)
    Subset.rfl Subset.rfl p hcompact hcurv
  refine ⟨p,G,hpcenter,hslabs,hlast,hterminal,hsol,hRm,hcompact,S,?_,?_,hh.1,hh.2.1,
    hh.2.2.1,?_⟩
  · exact fun s => rfl
  · change (Gsol.parabolicClosedWindow (H.time i.succ) N.scale θ N.scale_pos hθ.le).base.metric 0 = _
    rw [SolutionOn.parabolicClosedWindow_metric_zero]
    exact congrArg (scaleMetric N.scale N.scale_pos) hterminal
  · have hdim : Module.finrank ℝ ThreeSpace = 3 := by simp [ThreeSpace]
    simpa only [hdim, Nat.cast_ofNat, show (3 : ℝ)^2 = 9 by norm_num] using hh.2.2.2

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
