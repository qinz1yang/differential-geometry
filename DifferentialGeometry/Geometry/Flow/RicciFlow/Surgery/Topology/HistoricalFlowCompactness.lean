import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistoricalNeckInjectivity
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Limits.LocalMetricExtraction
import DifferentialGeometry.Bundle.FiberBundleHausdorff

noncomputable section
open Set Bundle Manifold Filter
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

attribute [local instance] PointedRiemannianManifold.topology
  PointedRiemannianManifold.charted PointedRiemannianManifold.smooth
  PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact
  PointedRiemannianManifold.t2TangentBundle

theorem exists_historical_footprint_flow_limit
    (A : ℕ → ObservedHistory.{u}) (i : ∀ n, Fin (A n).eventCount)
    (first : ∀ n, Fin ((A n).eventCount + 1)) (hle : ∀ n, first n ≤ (i n).castSucc)
    (δ₀ : ℕ → ℝ) (eps : ℝ) (k : ℕ → ℕ)
    (N : ∀ n, NormalizedNeck ((A n).event (i n)).terminal.metric (δ₀ n) (k n))
    (hprecision : ∀ n, δ₀ n ≤ eps) (hk : ∀ n, ⌈eps⁻¹⌉₊ ≤ k n)
    (a : ℝ) (ha : 24 < a) (hfit : 4 * a < eps⁻¹)
    {θ : ℝ} (hθ : 0 < θ)
    (htrace : ∀ n, ∀ x ∈ (N n).chart ''
      {z : neckBuffer (δ₀ n) | -(3*a) ≤ z.val.2 ∧ z.val.2 ≤ 3*a},
        Nonempty (BackwardPointTrace (A n) (first n) (i n).castSucc (hle n) x.val)) :
    ∀ (p : ∀ n, (A n).backwardSurvivorFootprintInterior (first n) (i n) (hle n) ((N n).chart '' {z : neckBuffer (δ₀ n) | -(3*a) ≤ z.val.2 ∧ z.val.2 ≤ 3*a})),
      (∀ n, (A n).backwardSurvivorFootprintMap (first n) (i n) (hle n) ((N n).chart '' {z : neckBuffer (δ₀ n) | -(3*a) ≤ z.val.2 ∧ z.val.2 ≤ 3*a}) (p n) =
        (N n).center) →
    ∀ S : ∀ n, SolutionOn (I := ThreeModel) (M := ((A n).backwardSurvivorFootprintInterior (first n) (i n) (hle n) ((N n).chart '' {z : neckBuffer (δ₀ n) | -(3*a) ≤ z.val.2 ∧ z.val.2 ≤ 3*a})))
        (RealTimeInterval.closed (-θ) 0 (neg_nonpos.mpr hθ.le)),
      (∀ n, IsSolutionOn (S n)) →
      (∀ n, (S n).base.metric 0 = scaleMetric (N n).scale (N n).scale_pos
        (localPullMetric ((A n).event (i n)).terminal.metric
          ((A n).backwardSurvivorFootprintMap (first n) (i n) (hle n) ((N n).chart '' {z : neckBuffer (δ₀ n) | -(3*a) ≤ z.val.2 ∧ z.val.2 ≤ 3*a}))
          ((A n).backwardSurvivorFootprintMap_isLocalDiffeomorph (first n) (i n) (hle n) ((N n).chart '' {z : neckBuffer (δ₀ n) | -(3*a) ≤ z.val.2 ∧ z.val.2 ≤ 3*a})))) →
      (∀ n, IsCompact (riemannianClosedBallOf ((S n).base.metric 0) (p n) (2*a))) →
      (∀ n, ∀ x ∈ riemannianClosedBallOf ((S n).base.metric 0) (p n) (2*a),
        curvDerivNormSq 0 ((S n).base.metric 0) x ≤ (8 * Real.sqrt 3)^2) →
      (∀ m : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ n, ∀ t ∈ Icc (-(θ/2)) 0,
        ∀ x ∈ riemannianClosedBallOf ((S n).base.metric 0) (p n) (a/2), curvDerivNorm m ((S n).base.metric t) x ≤ C) →
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
  intro p hp S hS hzero hcpt hcurv hflowJets
  let g₀ := fun n => (S n).base.metric 0
  have hg₀ := hzero
  have hderiv : ∀ m : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ n,
      ∀ x ∈ riemannianClosedBallOf (g₀ n) (p n) (a/2), curvDerivNorm m (g₀ n) x ≤ C := by
    intro m
    obtain ⟨C,hC,hb⟩ := hflowJets m
    exact ⟨C,hC,fun n => hb n 0 ⟨by linarith,le_rfl⟩⟩
  classical
  let K := fun n => (N n).chart ''
    {z : neckBuffer (δ₀ n) | -(3*a) ≤ z.val.2 ∧ z.val.2 ≤ 3*a}
  let W := fun n => (A n).backwardSurvivorFootprintInterior (first n) (i n) (hle n) (K n)
  let η : ℝ := exists_complete_historical_footprint_metric_with_injectivity.{u}.choose
  have hη : 0 < η := exists_complete_historical_footprint_metric_with_injectivity.{u}.choose_spec.1
  have hinjectivity := @exists_complete_historical_footprint_metric_with_injectivity.{u}.choose_spec.2
  choose g' U hcomplete hU hKU heq hlemetric hjets hclosed hinj using fun n =>
    hinjectivity (N n) (hprecision n) (hk n) a ha hfit (htrace n) (p n) (hp n)
      (g₀ n) (hg₀ n) (hcpt n) (hcurv n)
  let X : PointedRiemannianSeq.{u,0,0} ThreeModel := {
    obj := fun n => { M := W n, basepoint := p n, metric := g' n } }
  have hcompleteX : SeqMetricComplete X := ⟨fun n => (hcomplete n).complete⟩
  have hconn : ∀ n, ConnectedSpace (X.obj n).M := by
    intro n
    exact (N n).connectedSpace_historical_footprint (hprecision n) a (by linarith) hfit (htrace n)
  have hjetsX : ∀ m : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ᶠ n in Filter.atTop, HasLocalCurvDerivBound (X.obj n) (X.obj n).basepoint (a/8) m C := by
    intro m
    obtain ⟨C,hC,hbound⟩ := hderiv m
    refine ⟨C,hC,Filter.Eventually.of_forall fun n x hx => ?_⟩
    have hx' : x ∈ riemannianClosedBallOf (g₀ n) (p n) (a/8) := by
      rw [← hclosed n (a/8) (by linarith) (by linarith)]
      exact hx
    have hx2 : x ∈ riemannianClosedBallOf (g₀ n) (p n) (2*a) :=
      hx'.trans (ENNReal.ofReal_le_ofReal (by linarith))
    change curvDerivNorm m (g' n) x ≤ C
    rw [hjets n m x (hKU n hx2)]
    exact hbound n x (hx'.trans (ENNReal.ofReal_le_ofReal (by linarith)))
  have hinjX : ∀ᶠ n in Filter.atTop, ∀ x : (X.obj n).M,
      riemannianEDistOf (X.obj n).metric (X.obj n).basepoint x ≤ ENNReal.ofReal (a/16) →
        HasInjRadiusAt (X.obj n) x η := by
    refine Filter.Eventually.of_forall fun n x hx => ?_
    exact hasInjRadiusAt_of_expMap_injOn (X.obj n) x hη
      (hinj n x (hx.trans (ENNReal.ofReal_le_ofReal (by linarith))))
  have hagree : ∀ᶠ n in Filter.atTop, ∀ x ∈ riemannianBallOf
      (X.obj n).metric (X.obj n).basepoint (a/8), (g₀ n).inner x = (X.obj n).metric.inner x := by
    refine Filter.Eventually.of_forall fun n x hx => ?_
    have hx' : x ∈ riemannianClosedBallOf (g₀ n) (p n) (a/8) := by
      rw [← hclosed n (a/8) (by linarith) (by linarith)]
      exact le_of_lt (show riemannianEDistOf (g' n) (p n) x < ENNReal.ofReal (a/8) from hx)
    exact (heq n x (hKU n (hx'.trans (ENNReal.ofReal_le_ofReal (by linarith))))).symm
  have hslab : Icc (-(θ/4)) 0 ⊆
      (RealTimeInterval.closed (-θ) 0 (neg_nonpos.mpr hθ.le)).carrier := by
    intro t ht
    exact ⟨by linarith [ht.1],ht.2⟩
  have hregular : Ico (-(θ/4)) 0 ⊆
      (RealTimeInterval.closed (-θ) 0 (neg_nonpos.mpr hθ.le)).regular := by
    intro t ht
    exact ⟨by linarith [ht.1],ht.2⟩
  apply exists_local_flow_limit_of_local_metric_agreement X
    (fun n => (S n : SolutionOn (I := ThreeModel) (M := (X.obj n).M) _)) hS hcompleteX hconn
    (by linarith : 0 ≤ a/16) (by linarith : a/16 < a/8) hη
    (by linarith : -(θ/4) < 0) hslab hregular hjetsX hinjX hagree
  · intro n
    exact hclosed n (a/16) (by linarith) (by linarith)
  · intro n x hx
    rw [← hclosed n (a/8) (by linarith) (by linarith)]
    exact le_of_lt (show riemannianEDistOf (g' n) (p n) x < ENNReal.ofReal (a/8) from hx)
  · intro m
    obtain ⟨C,hC,hb⟩ := hflowJets m
    refine ⟨C,hC,Filter.Eventually.of_forall fun n t ht x hx => ?_⟩
    exact hb n t ⟨by linarith [ht.1],ht.2⟩ x
      (hx.trans (ENNReal.ofReal_le_ofReal (by linarith)))

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
