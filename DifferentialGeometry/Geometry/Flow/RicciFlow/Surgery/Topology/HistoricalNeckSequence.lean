import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistoricalNeckParabolicShi

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

theorem exists_parabolic_historical_footprint_sequence
    {Phi : ℝ → ℝ} (hPhi : Perelman.AdmissiblePinchingFunction Phi) :
    ∃ Q0 : ℝ, 0 < Q0 ∧
      ∀ (A : ℕ → ObservedHistory.{u}) (i : ∀ n, Fin (A n).eventCount)
        (first : ∀ n, Fin ((A n).eventCount + 1)) (hle : ∀ n, first n ≤ (i n).castSucc)
        (δ₀ : ℕ → ℝ) (δ eps : ℝ) (k : ℕ → ℕ)
        (N : ∀ n, NormalizedNeck ((A n).event (i n)).terminal.metric (δ₀ n) (k n)),
        (∀ n, Q0 ≤ (N n).scale) → (∀ n, δ₀ n ≤ δ) → δ < 1 →
        (∀ n, δ₀ n ≤ eps) → eps ≤ 1/8646 → (∀ n, ⌈eps⁻¹⌉₊ ≤ k n) →
        ∀ a : ℝ, 24 < a → δ⁻¹+1 ≤ a → 4*a < eps⁻¹ →
        ∀ (q : ℕ → ℝ) (C : ℝ≥0), (∀ n, 0 < q n) → (∀ n, q n ≤ (N n).scale) →
        (∀ n, ∀ j : Fin (A n).eventCount, first n ≤ j.castSucc → j.castSucc ≤ (i n).castSucc →
          ∀ x : ((A n).stage j.castSucc).Carrier,
          ∀ t ∈ Ioo ((A n).time j.castSucc) ((A n).time j.succ),
            q n < ((A n).event j).incoming.flow.scalar t x →
            |derivWithin (fun v => ((A n).event j).incoming.flow.scalar v x) (Iic t) t| ≤
              C * ((A n).event j).incoming.flow.scalar t x ^ 2) →
        (∀ n, ∀ j : Fin (A n).eventCount, first n ≤ j.castSucc → j.castSucc ≤ (i n).castSucc →
          Perelman.PhiAlmostNonnegative ((A n).event j).incoming.flow
            (Ico ((A n).time j.castSucc) ((A n).time j.succ)) Phi) →
        (∀ n, ∀ x ∈ (N n).chart ''
          {z : neckBuffer (δ₀ n) | -(3*a) ≤ z.val.2 ∧ z.val.2 ≤ 3*a},
            Nonempty (BackwardPointTrace (A n) (first n) (i n).castSucc (hle n) x.val)) →
        ∀ (θ : ℝ) (hθ : 0 < θ),
          (∀ n, (A n).time (first n) ≤ (A n).time (i n).succ - θ / (N n).scale) →
          6*C*θ ≤ 1 →
          ∃ (p : ∀ n, (A n).backwardSurvivorFootprintInterior (first n) (i n) (hle n) ((N n).chart '' {z : neckBuffer (δ₀ n) | -(3*a) ≤ z.val.2 ∧ z.val.2 ≤ 3*a}))
            (G : ∀ n, ℝ → SmoothRiemannianMetric ThreeModel ((A n).backwardSurvivorFootprintInterior (first n) (i n) (hle n) ((N n).chart '' {z : neckBuffer (δ₀ n) | -(3*a) ≤ z.val.2 ∧ z.val.2 ≤ 3*a})))
            (S : ∀ n, SolutionOn (I := ThreeModel) (M := (A n).backwardSurvivorFootprintInterior (first n) (i n) (hle n) ((N n).chart '' {z : neckBuffer (δ₀ n) | -(3*a) ≤ z.val.2 ∧ z.val.2 ≤ 3*a}))
              (RealTimeInterval.closed (-θ) 0 (neg_nonpos.mpr hθ.le))),
            (∀ n,
      (A n).backwardSurvivorFootprintMap (first n) (i n) (hle n) ((N n).chart '' {z : neckBuffer (δ₀ n) | -(3*a) ≤ z.val.2 ∧ z.val.2 ≤ 3*a}) (p n) = (N n).center ∧
      (∀ (j : Fin (A n).eventCount) (hf : (first n) ≤ j.castSucc) (hl : j.succ ≤ (i n).castSucc),
        ∀ t ∈ Icc ((A n).time j.castSucc) ((A n).time j.succ),
          (G n) t = (((A n).backwardSurvivorSlabMetric (first n) (i n).castSucc (hle n) j hf hl t).restrictOpen
            ((A n).backwardSurvivorTerminalFace (first n) (i n) (hle n))).restrictOpen
              ((A n).backwardSurvivorFootprintInterior (first n) (i n) (hle n) ((N n).chart '' {z : neckBuffer (δ₀ n) | -(3*a) ≤ z.val.2 ∧ z.val.2 ≤ 3*a}))) ∧
      (∀ t ∈ Icc ((A n).time (i n).castSucc) ((A n).time (i n).succ),
        (G n) t = ((A n).backwardSurvivorTerminalFaceMetric (first n) (i n) (hle n) t).restrictOpen
          ((A n).backwardSurvivorFootprintInterior (first n) (i n) (hle n) ((N n).chart '' {z : neckBuffer (δ₀ n) | -(3*a) ≤ z.val.2 ∧ z.val.2 ≤ 3*a}))) ∧
      (G n) ((A n).time (i n).succ) = localPullMetric ((A n).event (i n)).terminal.metric
        ((A n).backwardSurvivorFootprintMap (first n) (i n) (hle n) ((N n).chart '' {z : neckBuffer (δ₀ n) | -(3*a) ≤ z.val.2 ∧ z.val.2 ≤ 3*a}))
        ((A n).backwardSurvivorFootprintMap_isLocalDiffeomorph (first n) (i n) (hle n) ((N n).chart '' {z : neckBuffer (δ₀ n) | -(3*a) ≤ z.val.2 ∧ z.val.2 ≤ 3*a})) ∧
      IsSolutionOn ({ base := { metric := (G n) } } :
        SolutionOn (I := ThreeModel) (M := (A n).backwardSurvivorFootprintInterior (first n) (i n) (hle n) ((N n).chart '' {z : neckBuffer (δ₀ n) | -(3*a) ≤ z.val.2 ∧ z.val.2 ≤ 3*a}))
          (RealTimeInterval.closed ((A n).time (i n).succ - θ / (N n).scale) ((A n).time (i n).succ)
            (sub_le_self _ (div_nonneg hθ.le (N n).scale_pos.le)))) ∧
      (∀ t ∈ Icc ((A n).time (i n).succ - θ / (N n).scale) ((A n).time (i n).succ), ∀ x : (A n).backwardSurvivorFootprintInterior (first n) (i n) (hle n) ((N n).chart '' {z : neckBuffer (δ₀ n) | -(3*a) ≤ z.val.2 ∧ z.val.2 ≤ 3*a}),
        normSq0S ((G n) t) x 4 (metricRm04At ((G n) t) x) ≤ (4 * Real.sqrt 3 * ((N n).scale + Phi (4*(N n).scale) + Phi 0)) ^ 2) ∧
      IsCompact (riemannianClosedBallOf ((G n) ((A n).time (i n).succ)) (p n)
        (2*a / Real.sqrt (N n).scale)) ∧
        (∀ s : ℝ, (S n).base.metric s = scaleMetric (N n).scale (N n).scale_pos
          ((G n) ((A n).time (i n).succ + s / (N n).scale))) ∧
        (S n).base.metric 0 = scaleMetric (N n).scale (N n).scale_pos
          (localPullMetric ((A n).event (i n)).terminal.metric
            ((A n).backwardSurvivorFootprintMap (first n) (i n) (hle n) ((N n).chart '' {z : neckBuffer (δ₀ n) | -(3*a) ≤ z.val.2 ∧ z.val.2 ≤ 3*a}))
            ((A n).backwardSurvivorFootprintMap_isLocalDiffeomorph (first n) (i n) (hle n) ((N n).chart '' {z : neckBuffer (δ₀ n) | -(3*a) ≤ z.val.2 ∧ z.val.2 ≤ 3*a}))) ∧
        IsSolutionOn (S n) ∧
        IsCompact (riemannianClosedBallOf ((S n).base.metric 0) (p n) (2*a)) ∧
        (∀ s ∈ Icc (-θ) 0, ∀ x ∈ riemannianClosedBallOf ((S n).base.metric 0) (p n) (2*a),
          curvDerivNormSq 0 ((S n).base.metric s) x ≤ (8 * Real.sqrt 3) ^ 2)) ∧
            ∃ B : ℕ → ℝ, (∀ m, 0 ≤ B m) ∧
              ∀ n m, ∀ s ∈ Icc (-(θ/2)) 0,
                ∀ x ∈ riemannianClosedBallOf ((S n).base.metric 0) (p n) (a/2),
                  curvDerivNorm m ((S n).base.metric s) x ≤ B m := by
  obtain ⟨Q0,hQ0,hflow⟩ := exists_parabolic_historical_footprint_curvature_derivative_bounds hPhi
  refine ⟨Q0,hQ0,?_⟩
  intro A i first hle δ₀ δ eps k N hQlarge hδ hδ1 hprecision hsmall hk a ha hpublic hfit
    q C hq hqQ hbound hpinch htrace θ hθ hc htime
  have hall := fun n => hflow (N n) (hQlarge n) (hδ n) hδ1 (hprecision n) hsmall (hk n)
    a ha hpublic hfit (hq n) (hqQ n) (hbound n) (hpinch n) (htrace n) hθ (hc n) htime
  choose p G hp hslabs hlast hterminal hsol hRm hcompact S hmetric hzero hS hcpt hcurv hjets using hall
  refine ⟨p,G,S,fun n => ⟨hp n,hslabs n,hlast n,hterminal n,hsol n,hRm n,hcompact n,
    hmetric n,hzero n,hS n,hcpt n,hcurv n⟩,?_⟩
  let B : ℕ → ℝ := fun m => shiLocalUniformBound 3 m ((8 * Real.sqrt 3) * (θ / 4))
          (((2*a) / (4 * Real.exp (9 * (8 * Real.sqrt 3) * θ))) *
            Real.sqrt (8 * Real.sqrt 3) /
              (4 * Real.exp (9 * (8 * Real.sqrt 3) * (θ / 4)))) *
            (8 * Real.sqrt 3) / Real.sqrt (θ / 4) ^ m
  refine ⟨fun m => max (B m) 0, fun m => le_max_right _ _, ?_⟩
  intro n m s hs x hx
  apply (le_max_left (B m) 0).trans'
  have hh := hjets n m s hs x
  apply hh
  simpa only [show (2*a)/4 = a/2 by ring] using hx

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
