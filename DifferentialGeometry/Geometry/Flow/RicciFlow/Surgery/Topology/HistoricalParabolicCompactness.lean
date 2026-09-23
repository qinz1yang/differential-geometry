import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistoricalNeckSequence
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistoricalFlowCompactness

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

theorem exists_parabolic_historical_footprint_flow_limit
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
              (∀ n m, ∀ s ∈ Icc (-(θ/2)) 0,
                ∀ x ∈ riemannianClosedBallOf ((S n).base.metric 0) (p n) (a/2),
                  curvDerivNorm m ((S n).base.metric s) x ≤ B m) ∧
      ∃ phi : ℕ → ℕ, StrictMono phi ∧
        ∃ Q : Type, ∃ top : TopologicalSpace Q, letI := top
        ∃ charts : ChartedSpace ThreeSpace Q, letI := charts
        ∃ hman : IsManifold ThreeModel ∞ Q, letI := hman
        ∃ hT2 : T2Space Q, letI := hT2
        ∃ hSecondCountable : SecondCountableTopology Q, letI := hSecondCountable
        ∃ (gQ : SmoothRiemannianMetric ThreeModel Q)
          (V : TopologicalSpace.Opens Q) (q : Q)
          (Φ : ∀ n, PartialDiffeomorph ThreeModel ThreeModel Q
            ((A (phi n)).backwardSurvivorFootprintInterior
              (first (phi n)) (i (phi n)) (hle (phi n)) ((N (phi n)).chart '' {z : neckBuffer (δ₀ (phi n)) | -(3*a) ≤ z.val.2 ∧ z.val.2 ≤ 3*a})) ∞)
          (G : ℕ → SmoothRiemannianMetric ThreeModel V),
          IsCompact (closure (V : Set Q)) ∧ q ∈ V ∧
          (∀ n, closure (V : Set Q) ⊆ (Φ n).source) ∧
          (∀ n, Φ n q = p (phi n)) ∧
          (∀ n, riemannianClosedBallOf ((S (phi n)).base.metric 0) (p (phi n)) (a/16) ⊆
            (Φ n) '' (V : Set Q)) ∧
          (∀ n, (Φ n) '' closure (V : Set Q) ⊆
            riemannianClosedBallOf ((S (phi n)).base.metric 0) (p (phi n)) (a/8)) ∧
          (∀ n (x : V) (v w : TangentSpace ThreeModel x),
            (G n).inner x v w = ((S (phi n)).base.metric 0).inner (Φ n x)
              (mfderiv ThreeModel ThreeModel (Φ n) (x : Q) v)
              (mfderiv ThreeModel ThreeModel (Φ n) (x : Q) w)) ∧
          MetricCInfConvergenceOnCompacts G (gQ.restrictOpen V) (gQ.restrictOpen V) ∧
          ∃ L : ℕ → SolutionOn (I := ThreeModel) (M := V)
              (RealTimeInterval.closed (-θ) 0 (neg_nonpos.mpr hθ.le)),
            (∀ n, IsSolutionOn (L n)) ∧
            (∀ n t (x : V) (v w : TangentSpace ThreeModel x),
              ((L n).base.metric t).inner x v w = ((S (phi n)).base.metric t).inner (Φ n x)
                (mfderiv ThreeModel ThreeModel (Φ n) x v)
                (mfderiv ThreeModel ThreeModel (Φ n) x w)) ∧
            (∀ n, (L n).base.metric 0 = G n) ∧
            ∃ rho : ℕ → ℕ, StrictMono rho ∧ ∃ g : ℝ → SmoothRiemannianMetric ThreeModel V,
              g 0 = gQ.restrictOpen V ∧
              IsSolutionOn ({base.metric := g} : SolutionOn (I := ThreeModel) (M := V)
                (RealTimeInterval.closed (-(θ/4)) 0 (by linarith))) ∧
              ∀ B : Set V, IsCompact B → ∀ m : ℕ, ∀ ε : ℝ, 0 < ε →
                ∃ N0 : ℕ, ∀ n ≥ N0, ∀ t ∈ Icc (-(θ/4)) 0,
                  metricDerivNormSupOn B m ((L (rho n)).base.metric t) (g t)
                    (gQ.restrictOpen V) < ε := by
  let Q0 : ℝ := (exists_parabolic_historical_footprint_sequence.{u} hPhi).choose
  have hQ0 : 0 < Q0 := (exists_parabolic_historical_footprint_sequence.{u} hPhi).choose_spec.1
  have hsequence := @(exists_parabolic_historical_footprint_sequence.{u} hPhi).choose_spec.2
  refine ⟨Q0,hQ0,?_⟩
  intro A i first hle δ₀ δ eps k N hQlarge hδ hδ1 hprecision hsmall hk a ha hpublic hfit
    q C hq hqQ hbound hpinch htrace θ hθ hc htime
  have hex := hsequence A i first hle δ₀ δ eps k N hQlarge hδ hδ1
    hprecision hsmall hk a ha hpublic hfit q C hq hqQ hbound hpinch htrace θ hθ hc htime
  let p := hex.choose
  let G := hex.choose_spec.choose
  let S := hex.choose_spec.choose_spec.choose
  have hstat := hex.choose_spec.choose_spec.choose_spec.1
  let B := hex.choose_spec.choose_spec.choose_spec.2.choose
  have hB := hex.choose_spec.choose_spec.choose_spec.2.choose_spec.1
  have hjets := hex.choose_spec.choose_spec.choose_spec.2.choose_spec.2
  refine ⟨p,G,S,hstat,B,hB,hjets,?_⟩
  apply exists_historical_footprint_flow_limit A i first hle δ₀ eps k N hprecision hk
    a ha hfit hθ htrace p
  · exact fun n => (hstat n).1
  · intro n
    rcases hstat n with ⟨_,_,_,_,_,_,_,_,_,hS,_,_⟩
    exact hS
  · intro n
    rcases hstat n with ⟨_,_,_,_,_,_,_,_,hzero,_,_,_⟩
    exact hzero
  · intro n
    rcases hstat n with ⟨_,_,_,_,_,_,_,_,_,_,hcpt,_⟩
    exact hcpt
  · intro n
    rcases hstat n with ⟨_,_,_,_,_,_,_,_,_,_,_,hcurv⟩
    exact hcurv 0 ⟨by linarith,le_rfl⟩
  · intro m
    exact ⟨B m,hB m,fun n => hjets n m⟩

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
