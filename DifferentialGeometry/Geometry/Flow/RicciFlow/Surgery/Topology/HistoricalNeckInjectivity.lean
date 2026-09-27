import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistoricalNeckLift
import DifferentialGeometry.Geometry.Neck.InjectivityRadius

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

theorem exists_complete_historical_footprint_metric_with_injectivity :
    ∃ η : ℝ, 0 < η ∧
      ∀ {H : ObservedHistory.{u}} {i : Fin H.eventCount}
        {first : Fin (H.eventCount + 1)} {hle : first ≤ i.castSucc},
        ∀ {δ₀ eps : ℝ} {k : ℕ} (N : NormalizedNeck (H.event i).terminal.metric δ₀ k),
          δ₀ ≤ eps → ⌈eps⁻¹⌉₊ ≤ k → ∀ a : ℝ, 24 < a → 4*a < eps⁻¹ →
          (∀ x ∈ N.chart '' {z : neckBuffer δ₀ | -(3*a) ≤ z.val.2 ∧ z.val.2 ≤ 3*a},
            Nonempty (BackwardPointTrace H first i.castSucc hle x.val)) →
          let K := N.chart '' {z : neckBuffer δ₀ | -(3*a) ≤ z.val.2 ∧ z.val.2 ≤ 3*a}
          ∀ (p : H.backwardSurvivorFootprintInterior first i hle K),
            H.backwardSurvivorFootprintMap first i hle K p = N.center →
          ∀ g₀ : SmoothRiemannianMetric ThreeModel
              (H.backwardSurvivorFootprintInterior first i hle K),
            g₀ = scaleMetric N.scale N.scale_pos
              (localPullMetric (H.event i).terminal.metric
                (H.backwardSurvivorFootprintMap first i hle K)
                (H.backwardSurvivorFootprintMap_isLocalDiffeomorph first i hle K)) →
            IsCompact (riemannianClosedBallOf g₀ p (2*a)) →
            (∀ x ∈ riemannianClosedBallOf g₀ p (2*a),
              curvDerivNormSq 0 g₀ x ≤ (8 * Real.sqrt 3)^2) →
            ∃ (g' : SmoothRiemannianMetric ThreeModel
                (H.backwardSurvivorFootprintInterior first i hle K))
              (U : Set (H.backwardSurvivorFootprintInterior first i hle K)),
              RiemannianMetricComplete g' ∧ IsOpen U ∧
              riemannianClosedBallOf g₀ p (2*a) ⊆ U ∧
              (∀ x ∈ U, g'.inner x = g₀.inner x) ∧
              (∀ x (v : TangentSpace ThreeModel x), g₀.inner x v v ≤ g'.inner x v v) ∧
              (∀ m : ℕ, ∀ x ∈ U, curvDerivNorm m g' x = curvDerivNorm m g₀ x) ∧
              (∀ r : ℝ, 0 ≤ r → r < 2*a →
                riemannianClosedBallOf g' p r = riemannianClosedBallOf g₀ p r) ∧
              ∀ x ∈ riemannianClosedBallOf g' p (a / 8),
                Set.InjOn (fun v : TangentSpace ThreeModel x =>
                  Geometry.Riemannian.Exponential.expMap g' x v)
                  {v | Real.sqrt (g'.inner x v v) < η} := by
  obtain ⟨η,hη,hinj⟩ :=
    Perelman.CanonicalNeighborhood.FiniteHorn.exists_complete_metric_extension_with_injectivity_of_normalizedNeck.{u}
      (K := (8 * Real.sqrt 3)^2) (ρ := 1/4) (by norm_num) (by
        have hs : (Real.sqrt (3 : ℝ))^2 = 3 := Real.sq_sqrt (by norm_num)
        nlinarith)
  refine ⟨η,hη,?_⟩
  intro H i first hle δ₀ eps k N hprecision hk a ha hfit htrace
  dsimp only
  intro p hp g₀ hg₀ hcpt hcurv
  obtain ⟨hδ',N',hsmall',hscale,_,hcenter,_,_⟩ :=
    N.exists_historical_footprint_neck hprecision a ha hfit htrace
  let K := N.chart '' {z : neckBuffer δ₀ | -(3*a) ≤ z.val.2 ∧ z.val.2 ≤ 3*a}
  let f := H.backwardSurvivorFootprintMap first i hle K
  have hcenter' : N'.center = p :=
    H.backwardSurvivorFootprintMap_injective first i hle K (hcenter.trans hp.symm)
  have hscaled : scaleMetric N'.scale N'.scale_pos
      (localPullMetric (H.event i).terminal.metric f
        (H.backwardSurvivorFootprintMap_isLocalDiffeomorph first i hle K)) = g₀ := by
    simpa only [hscale] using hg₀.symm
  have hinv : (2 / a)⁻¹ = a / 2 := by field_simp
  have hk' : ⌈(2 / a)⁻¹⌉₊ ≤ k := by
    apply (Nat.ceil_mono (show (2 / a)⁻¹ ≤ eps⁻¹ by rw [hinv]; linarith)).trans hk
  have hfit' : 2 * (a / 8) + (1/4 : ℝ) < (2 / a)⁻¹ := by rw [hinv]; linarith
  have hcompact' : IsCompact (riemannianClosedBallOf
      (scaleMetric N'.scale N'.scale_pos
        (localPullMetric (H.event i).terminal.metric f
          (H.backwardSurvivorFootprintMap_isLocalDiffeomorph first i hle K))) N'.center (2*a)) := by
    rw [hscaled,hcenter']
    exact hcpt
  have hbound' : ∀ x ∈ riemannianClosedBallOf
      (scaleMetric N'.scale N'.scale_pos
        (localPullMetric (H.event i).terminal.metric f
          (H.backwardSurvivorFootprintMap_isLocalDiffeomorph first i hle K))) N'.center (2*a),
      curvDerivNormSq 0
        (scaleMetric N'.scale N'.scale_pos
          (localPullMetric (H.event i).terminal.metric f
            (H.backwardSurvivorFootprintMap_isLocalDiffeomorph first i hle K))) x ≤
        (8 * Real.sqrt 3)^2 := by
    rw [hscaled,hcenter']
    exact hcurv
  have hh := hinj (M := H.backwardSurvivorFootprintInterior first i hle K)
    (g := localPullMetric (H.event i).terminal.metric f
      (H.backwardSurvivorFootprintMap_isLocalDiffeomorph first i hle K))
    (eps := 2/a) N' le_rfl hsmall' hk' (a := a/8) (R := 2*a)
    (by linarith : 0 < a/8) hfit' (by linarith : a/8+(1/4 : ℝ) ≤ 2*a) hcompact' hbound'
  simpa only [hscaled,hcenter'] using hh

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
