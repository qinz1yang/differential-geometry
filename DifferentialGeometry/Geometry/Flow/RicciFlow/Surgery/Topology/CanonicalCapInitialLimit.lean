import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CanonicalCapWindowFlow
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.InitialTimeConvergence
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.MarkedWindow
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.AmbientSpatialCap

import DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.ScalarDerivativeBounds

set_option autoImplicit false
noncomputable section
open Set Filter Function Bundle Manifold
open DifferentialGeometry.Geometry.Neck DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open DifferentialGeometry.CheegerGromovCompactness
open scoped Manifold ContDiff Topology NNReal ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

universe u
private local instance : Fact (Module.finrank ℝ ThreeSpace = 3) := ⟨by simp⟩

theorem exists_uniform_canonical_cap_window_convergence_and_uniform_scalar_derivative_bounds_at_vanishing_age
    (N : ℕ) (D r eps : ℝ)
    (heps : 0 < eps) (hepssmall : eps ≤ 1 / 1000)
    (hr : StandardCap.transitionEnd + eps⁻¹ + 1 < r)
    (hfit : 64 * (r + eps⁻¹) < D) :
    ∃ C₀ B Cderiv : ℝ, 0 < C₀ ∧ 1 ≤ B ∧ 0 < Cderiv ∧
      ∀ C : ℝ≥0, ∃ η ε₀ δ₀ : ℝ, 0 < η ∧ 0 < ε₀ ∧ ε₀ ≤ 1 / 2 ∧ 0 < δ₀ ∧
      ∀ (H : ℕ → ObservedHistory.{u}) (event : ∀ i, Fin (H i).eventCount)
        (last : ∀ i, Fin ((H i).eventCount + 1)) (hle : ∀ i, (event i).succ ≤ last i)
        (time : ℕ → ℝ)
        (G : ∀ i, ((H i).stage (last i)).IncomingSlab ((H i).time (last i)) (time i))
        (L : ∀ i, (G i).TerminalLimitMetric),
      (∀ i, (G i).flow.base.metric ((H i).time (last i)) = (H i).initialMetric (last i)) →
      ∀ (parameters : ℕ → CutoffParameters)
        (records : ∀ i k, GeometricCutoffRecord (H i) k (parameters i))
        (boundary : ∀ i, ((H i).event (event i)).RetainedBoundaryIndex),
      let cap := fun i => (records i (event i)).static (boundary i)
      let q := fun i => (cap i).neck.scale
      let age := fun i => q i * (time i - (H i).time (event i).succ)
      (∀ i, (cap i).hasCanonicalWindow) →
      (∀ i, D + 1 ≤ (parameters i).modelRadius) →
      (∀ i, max ⌈eps⁻¹⌉₊ N + 2 ≤ (parameters i).modelOrder) →
      (∀ i, (parameters i).modelAccuracy ≤ ε₀) →
      Tendsto (fun i => (parameters i).modelAccuracy) atTop (𝓝 0) →
      ∀ (q₀ a₀ : ℕ → ℝ), (∀ i, 0 < q₀ i) →
      (∀ i, q₀ i ≤ C₀ * q i) → (∀ i, 1 ≤ a₀ i * q i) →
      (∀ i x, InFixedHamiltonIveyRegion ((H i).initialMetric 0) (a₀ i) x) →
      (∀ i x, -3 / a₀ i ≤ metricScalarAt ((H i).initialMetric 0) x) →
      (∀ i k, (event i).succ ≤ k.castSucc → k.succ ≤ last i →
        ∀ b, (records i k).delta b ≤ δ₀) →
      (∀ i k, (event i).succ ≤ k.castSucc → k.succ ≤ last i →
        ∀ x : ((H i).stage k.castSucc).Carrier,
        ∀ t ∈ Ioo ((H i).time k.castSucc) ((H i).time k.succ),
          q₀ i < ((H i).event k).incoming.flow.scalar t x →
          |derivWithin (fun v => ((H i).event k).incoming.flow.scalar v x) (Iic t) t| ≤
            C * ((H i).event k).incoming.flow.scalar t x ^ 2) →
      (∀ i x, ∀ t ∈ Ioo ((H i).time (last i)) (time i), q₀ i < (G i).flow.scalar t x →
        |derivWithin (fun v => (G i).flow.scalar v x) (Iic t) t| ≤ C * (G i).flow.scalar t x ^ 2) →
      (∀ i, age i ≤ η) → Tendsto age atTop (𝓝 0) →
      ∀ (z : ℕ → ThreeBall) (x : ∀ i, (G i).terminalRegularOpen)
        (trace : ∀ i, BackwardPointTrace (H i) (event i).succ (last i) (hle i) (x i).val),
      (∀ i, (trace i).point (event i).succ le_rfl (hle i) =
        (cap i).inclusion ((cap i).witness.cap (z i))) →
      ∃ (x₀ : ∀ i, ((H i).event (event i)).incoming.terminalRegularOpen)
        (delta : ℕ → ℝ) (order : ℕ → ℕ)
        (datum : ∀ i, normalizedDatum ((H i).event (event i)).terminal.metric
          (x₀ i) (delta i) (order i))
        (w : ∀ i, StandardCap.CanonicalStaticInsertionWitness (datum i)
          (parameters i).fixed.collarLength (parameters i).fixed.collar_pos
          (parameters i).modelRadius (parameters i).modelOrder (parameters i).modelAccuracy),
        (∀ i, metricScalarAt ((H i).event (event i)).terminal.metric (x₀ i) = q i) ∧
        (∀ i y (v z : TangentSpace ThreeModel y), (w i).windowMetric.inner y v z =
          q i * ((H i).initialMetric (event i).succ).inner ((cap i).window y)
            (mfderiv ThreeModel ThreeModel (cap i).window y v)
            (mfderiv ThreeModel ThreeModel (cap i).window y z)) ∧
        ∃ (u : ℕ → standardCapWindow D)
          (Ξ : ∀ i, standardCapWindow D →
            (H i).backwardSurvivorIncomingDomain (event i).succ (last i) (hle i) (G i))
          (hΞ : ∀ i, IsLocalDiffeomorph ThreeModel ThreeModel ∞ (Ξ i))
          (gflow : ∀ i, ℝ → SmoothRiemannianMetric ThreeModel
            ((H i).backwardSurvivorIncomingDomain (event i).succ (last i) (hle i) (G i)))
          (hmargin : ∀ i, D ≤ (parameters i).modelRadius)
          (hpos : ∀ i, 0 ≤ age i)
          (S : ∀ i, SolutionOn (I := ThreeModel) (M := standardCapWindow D)
            (RealTimeInterval.closed 0 (age i) (hpos i))),
          (∀ i, ‖(u i).val‖ ≤ StandardCap.transitionEnd) ∧
          (∀ i, (cap i).window ⟨(u i).val,
            (u i).property.trans_le (add_le_add (hmargin i) (le_refl 1))⟩ =
              (cap i).inclusion ((cap i).witness.cap (z i))) ∧
          (∀ i, IsSmoothEmbedding ThreeModel ThreeModel ∞ (Ξ i)) ∧
          (∀ i y, (H i).backwardSurvivorMap (event i).succ (last i) (hle i)
            (event i).succ le_rfl (hle i) ((Ξ i y).val) =
              (cap i).window ⟨y.val, y.property.trans_le (add_le_add (hmargin i) (le_refl 1))⟩) ∧
          (∀ i, (H i).backwardSurvivorIncomingMap (event i).succ (last i) (hle i)
            (G i) (Ξ i (u i)) = x i) ∧
          (∀ i k (hf : (event i).succ ≤ k.castSucc) (hl : k.succ ≤ last i),
            ∀ t ∈ Icc ((H i).time k.castSucc) ((H i).time k.succ),
              gflow i t = ((H i).backwardSurvivorSlabMetric (event i).succ (last i)
                (hle i) k hf hl t).restrictOpen
                  ((H i).backwardSurvivorIncomingDomain (event i).succ (last i) (hle i) (G i))) ∧
          (∀ i t, t ∈ Icc ((H i).time (last i)) (time i) →
            gflow i t = (H i).backwardSurvivorIncomingMetric (event i).succ (last i)
              (hle i) (G i) (L i) t) ∧
          (∀ i, IsSolutionOn (S i)) ∧
          (∀ i y (j k : Fin (Module.finrank ℝ ThreeSpace)),
            ContMDiffOn (𝓘(ℝ, ℝ).prod ThreeModel) 𝓘(ℝ) ∞
              (fun z : ℝ × standardCapWindow D => DifferentialGeometry.Tensor.Coordinates.chartGramMatrix
                ((S i).base.metric z.1) y z.2 j k)
              (Icc 0 (age i) ×ˢ (trivializationAt ThreeSpace (TangentSpace ThreeModel) y).baseSet)) ∧
          (∀ i j, j ≤ N → ∀ t ∈ Icc 0 (age i),
            ∀ y : standardCapWindow D, ‖y.val‖ ≤ r → curvDerivNormSq j ((S i).base.metric t) y ≤ B) ∧
          (2 ≤ N →
            (∀ i t, t ∈ Icc 0 (age i) → ∀ y : standardCapWindow D, ‖y.val‖ ≤ r →
              1 / 2 ≤ (S i).scalar t y → ∀ v : TangentSpace ThreeModel y,
                |Perelman.CanonicalNeighborhood.scalarDifferential (S i) t y v| ≤
                  Cderiv * (S i).scalar t y * Real.sqrt ((S i).scalar t y) *
                    Real.sqrt (((S i).base.metric t).inner y v v)) ∧
            (∀ i t, t ∈ Ioc 0 (age i) → ∀ y : standardCapWindow D, ‖y.val‖ ≤ r →
              1 / 2 ≤ (S i).scalar t y →
                |derivWithin (fun s => (S i).scalar s y) (Iic t) t| ≤
                  Cderiv * (S i).scalar t y ^ 2) ∧
            ∀ᶠ i in atTop, ∀ y : standardCapWindow D, ‖y.val‖ ≤ StandardCap.transitionEnd →
              1 / 2 ≤ (S i).scalar (age i) y) ∧
          (∀ i, (S i).base.metric 0 = (w i).windowMetric.restrictOpenOfSubset
            (show standardCapWindow D ≤ standardCapWindow (parameters i).modelRadius from
              fun _ hy => hy.trans_le (add_le_add (hmargin i) (le_refl 1)))) ∧
          (∀ i t, (S i).base.metric t = localPullMetric
            (scaleMetric (q i) (cap i).neck.scale_pos
              (gflow i ((H i).time (event i).succ + t / q i))) (Ξ i) (hΞ i)) ∧
          (∀ i y (v z : TangentSpace ThreeModel y), ((S i).base.metric (age i)).inner y v z =
            (scaleMetric (q i) (cap i).neck.scale_pos (L i).metric).inner
              ((H i).backwardSurvivorIncomingMap (event i).succ (last i) (hle i) (G i) (Ξ i y))
              (mfderiv ThreeModel ThreeModel
                ((H i).backwardSurvivorIncomingMap (event i).succ (last i) (hle i) (G i) ∘ Ξ i) y v)
              (mfderiv ThreeModel ThreeModel
                ((H i).backwardSurvivorIncomingMap (event i).succ (last i) (hle i) (G i) ∘ Ξ i) y z)) ∧
          (∀ a : ℝ, a < r → MetricCPConvergenceOn {y : standardCapWindow D | ‖y.val‖ ≤ a} N
            (fun i => (S i).base.metric (age i))
            (StandardCap.metric.restrictOpen (standardCapWindow D))
            (StandardCap.metric.restrictOpen (standardCapWindow D))) ∧
          (∀ a : ℝ, StandardCap.transitionEnd ≤ a → a < r → 2 ≤ N →
            ∃ (phi : ℕ → ℕ) (uLim : standardCapWindow D), StrictMono phi ∧
              ‖uLim.val‖ ≤ StandardCap.transitionEnd ∧ Tendsto (u ∘ phi) atTop (𝓝 uLim) ∧
              ∃ hlim : 1 ≤ metricScalarAt StandardCap.metric uLim.val,
                metricScalarAt (scaleMetric (metricScalarAt StandardCap.metric uLim.val)
                  (zero_lt_one.trans_le hlim) (StandardCap.metric.restrictOpen (standardCapWindow D))) uLim = 1 ∧
                Tendsto (fun n => metricScalarAt (L (phi n)).metric (x (phi n)) / q (phi n)) atTop
                  (𝓝 (metricScalarAt StandardCap.metric uLim.val)) ∧
                ∃ hR : ∀ n, 0 < metricScalarAt (L (phi n)).metric (x (phi n)),
                  MetricCPConvergenceOn {y : standardCapWindow D | ‖y.val‖ ≤ a} N
                    (fun n => localPullMetric
                      (scaleMetric (metricScalarAt (L (phi n)).metric (x (phi n))) (hR n) (L (phi n)).metric)
                      ((H (phi n)).backwardSurvivorIncomingMap (event (phi n)).succ (last (phi n))
                        (hle (phi n)) (G (phi n)) ∘ Ξ (phi n))
                      (isLocalDiffeomorph_comp
                        ((H (phi n)).backwardSurvivorIncomingMap_isLocalDiffeomorph
                          (event (phi n)).succ (last (phi n)) (hle (phi n)) (G (phi n))) (hΞ (phi n))))
                    (scaleMetric (metricScalarAt StandardCap.metric uLim.val)
                      (zero_lt_one.trans_le hlim) (StandardCap.metric.restrictOpen (standardCapWindow D)))
                    (scaleMetric (metricScalarAt StandardCap.metric uLim.val)
                      (zero_lt_one.trans_le hlim) (StandardCap.metric.restrictOpen (standardCapWindow D)))) ∧
          ∀ r₀ epsilon : ℝ, 0 < epsilon → epsilon < 1 / 11 →
            StandardCap.transitionEnd + epsilon⁻¹ + 1 < r₀ → r₀ + epsilon⁻¹ < r →
            ⌈epsilon⁻¹⌉₊ ≤ N → ∀ᶠ i in atTop,
              let Φ := (H i).backwardSurvivorIncomingMap (event i).succ (last i) (hle i) (G i) ∘ Ξ i
              let metric := scaleMetric (q i) (cap i).neck.scale_pos (L i).metric
              ∃ (p tip : standardCapWindow D), p.val = r₀ • (spherePoint : ThreeSpace) ∧ tip.val = 0 ∧
                ∃ (nk : SpatialNeck metric epsilon (Φ p)) (K : CompactDomain (G i).terminalRegularOpen),
                  K.carrier = Φ '' {y : standardCapWindow D | ‖y.val‖ ≤ r₀} ∧
                  Nonempty (CapCore K.carrier) ∧ x i ∈ interior K.carrier ∧
                  Φ tip ∈ interior K.carrier ∧
                  (∀ v : neckBuffer epsilon, ∃ y : standardCapWindow D,
                    y.val = (r₀ + v.val.2) • (v.val.1 : ThreeSpace) ∧ nk.map v.val = Φ y) ∧
                  frontier K.carrier = range (fun y : Sphere 2 => nk.map (y, 0)) ∧
                  IsSmoothEmbedding I2 I3 ∞ (fun y : Sphere 2 => nk.map (y, 0)) ∧
                  (∀ y : Sphere 2, ∀ t ∈ Ioo (-epsilon⁻¹) epsilon⁻¹,
                    nk.map (y, t) ∈ K.carrier ↔ t ≤ 0) ∧
                  |metricScalarAt metric (Φ p) - 1| ≤ epsilon ∧
                  K.carrier ⊆ riemannianBallOf metric (Φ tip) (2 * r₀) := by
  obtain ⟨C₀, B, hC₀, hB, huniform⟩ :=
    exists_uniform_canonical_cap_window_flow_with_uniform_curvature_derivative_bounds N D r eps
      heps hepssmall hr hfit
  obtain ⟨Cderiv, hCderiv, hrelative⟩ :=
    exists_relative_scalar_derivative_bounds_of_curvature_jets
      (I := ThreeModel) (M := standardCapWindow D) B (zero_le_one.trans hB)
  refine ⟨C₀, B, Cderiv, hC₀, hB, hCderiv, ?_⟩
  intro C
  obtain ⟨η, ε₀, δ₀, hη, hε₀, hεhalf, hδ₀, hproducer⟩ := huniform C
  refine ⟨η, ε₀, δ₀, hη, hε₀, hεhalf, hδ₀, ?_⟩
  intro H event last hle time G L hinit parameters records boundary cap q age
    hcanonical hmargin hm herror herrorlim q₀ a₀ hq₀ hqcap hacap hfixed hlower hδ hderiv hfinal
    hage hagelim z x trace hbirth
  have rows (i : ℕ) := hproducer (H i) (event i) (last i) (hle i) (time i) (G i) (L i)
    (hinit i) (parameters i) (records i) (boundary i) (hcanonical i) (hmargin i) (hm i)
    (herror i) (q₀ i) (a₀ i) (hq₀ i) (hqcap i) (hacap i) (hfixed i) (hlower i)
    (hδ i) (hderiv i) (hfinal i) (hage i) (z i) (x i) (trace i) (hbirth i)
  classical
  choose x₀ delta order datum w hwscalar hwmetric u hu hucap Ξ hΞsmooth hΞbirth hΞpoint
    hΞ gflow S hslabs hlast hS hzero hmetric hgram hjets hterminal using rows
  have hD : 0 < D := by
    have := StandardCap.transitionEnd_pos
    have := inv_pos.mpr heps
    linarith
  have hmargin' (i) : D ≤ (parameters i).modelRadius := by linarith [hmargin i]
  have hpos (i) : 0 ≤ age i := by
    have hp := (cap i).neck.scale_pos
    have ht := ((H i).time_strictMono.monotone (hle i)).trans_lt (G i).lt
    exact (mul_pos hp (sub_pos.mpr ht)).le
  have hconvergence : ∀ a : ℝ, a < r →
      MetricCPConvergenceOn {y : standardCapWindow D | ‖y.val‖ ≤ a} N
        (fun i => (S i).base.metric (age i))
        (StandardCap.metric.restrictOpen (standardCapWindow D))
        (StandardCap.metric.restrictOpen (standardCapWindow D)) := by
    intro a har
    let wsmall := fun i => (w i).restrictWindow hD (hmargin' i)
    apply StandardCap.metric_cp_convergence_on_insertion_window_at_vanishing_age
      D a r har (by linarith [inv_pos.mpr heps]) N
      (fun i => ((H i).event (event i)).incoming.terminalRegularOpen)
      (fun i => ((H i).event (event i)).terminal.metric) x₀ delta order
      (fun i => (parameters i).modelOrder) datum
      (fun i => (parameters i).fixed.collarLength) (fun i => (parameters i).modelAccuracy)
      (fun i => (parameters i).fixed.collar_pos) wsmall
      (fun i => by have hi := hm i; omega) (fun i => (herror i).trans hεhalf) herrorlim
      (fun i => RealTimeInterval.closed 0 (age i) (hpos i)) age hpos hagelim S hS
      (fun _ => Subset.rfl) (fun _ => Subset.rfl) ?_ hgram (fun _ => Real.sqrt B) ?_
    · intro i
      rw [hzero i]
      exact ((w i).restrictWindow_windowMetric hD (hmargin' i)).symm
    · intro i j hj t ht y hy
      exact Real.sqrt_le_sqrt (hjets i j hj t ht y hy.le)
  refine ⟨x₀, delta, order, datum, w, hwscalar, hwmetric, u, Ξ, hΞ, gflow, hmargin', hpos, S,
    hu, hucap, hΞsmooth, hΞbirth, hΞpoint, hslabs, hlast, hS, hgram, hjets, ?_, hzero, hmetric, hterminal, hconvergence, ?_, ?_⟩
  · intro hN
    have hbounds (i : ℕ) := hrelative _ (S i) (hS i) 0 (age i) Subset.rfl Subset.rfl
      {y : standardCapWindow D | ‖y.val‖ ≤ r}
      (fun j hj t ht y hy => hjets i j (hj.trans hN) t ht y hy)
    refine ⟨fun i => (hbounds i).1, fun i => (hbounds i).2, ?_⟩
    have ha : StandardCap.transitionEnd < r := by linarith [inv_pos.mpr heps]
    have haD : StandardCap.transitionEnd < D + 1 := by linarith [inv_pos.mpr heps]
    have hlower := StandardCap.eventually_half_lt_metricScalarAt_of_metric_cp_convergence
      haD hN (fun i => (S i).base.metric (age i))
      (hconvergence StandardCap.transitionEnd ha)
    filter_upwards [hlower] with i hi
    intro y hy
    exact (hi y hy).le
  · intro a hmark har hN
    have haD : a < D + 1 := by linarith [inv_pos.mpr heps]
    obtain ⟨phi, uLim, hphi, huLim, hmarklim, hlim, hratio, hR, hnormalized⟩ :=
      StandardCap.exists_scalar_normalized_marked_window_limit hmark haD hN
      (fun i => (S i).base.metric (age i)) (hconvergence a har) u hu
      (fun i => (G i).terminalRegularOpen) (fun i => (L i).metric) q
      (fun i => (cap i).neck.scale_pos)
      (fun i => (H i).backwardSurvivorIncomingMap (event i).succ (last i) (hle i) (G i) ∘ Ξ i)
      (fun i => isLocalDiffeomorph_comp
        ((H i).backwardSurvivorIncomingMap_isLocalDiffeomorph (event i).succ (last i) (hle i) (G i))
        (hΞ i)) x hΞpoint hterminal
    refine ⟨phi, uLim, hphi, huLim, hmarklim, hlim, ?_, hratio, hR, hnormalized⟩
    rw [metricScalarAt_scaleMetric, metricScalarAt_restrictOpen,
      inv_mul_cancel₀ (zero_lt_one.trans_le hlim).ne']
  · intro r₀ epsilon hε hεsmall hr₀ hroom hN
    have hfit' : r₀ + epsilon⁻¹ + 1 ≤ D := by
      have hrpos : 1 < r := by linarith [StandardCap.transitionEnd_pos, inv_pos.mpr heps]
      linarith [inv_pos.mpr heps]
    have hcap := StandardCap.eventually_spatial_cap_frontier_of_metric_cp_convergence
      D r₀ epsilon hε hεsmall hr₀ hfit' N hN
      (fun i => (S i).base.metric (age i)) (hconvergence _ hroom)
      (fun i => (G i).terminalRegularOpen)
      (fun i => scaleMetric (q i) (cap i).neck.scale_pos (L i).metric)
      (fun i => (H i).backwardSurvivorIncomingMap (event i).succ (last i) (hle i) (G i) ∘ Ξ i)
      (fun i => isLocalDiffeomorph_comp
        ((H i).backwardSurvivorIncomingMap_isLocalDiffeomorph (event i).succ (last i) (hle i) (G i))
        (hΞ i))
      (fun i => ((H i).backwardSurvivorIncomingMap_injective (event i).succ (last i) (hle i) (G i)).comp
        (hΞsmooth i).isEmbedding.injective) hterminal
    filter_upwards [hcap] with i hi
    obtain ⟨p, tip, hp, htip, nk, K, hK, hcore, htipin, hmarks, hmap, hfront, hsmooth,
      hside, hscalar, hball⟩ := hi
    refine ⟨p, tip, hp, htip, nk, K, hK, hcore, ?_, htipin, hmap, hfront, hsmooth,
      hside, hscalar, hball⟩
    have hx := hmarks (u i) (hu i)
    change (H i).backwardSurvivorIncomingMap (event i).succ (last i) (hle i) (G i) (Ξ i (u i)) ∈ _ at hx
    rwa [hΞpoint i] at hx


theorem exists_uniform_canonical_cap_window_convergence_and_scalar_derivative_bounds_at_vanishing_age
    (N : ℕ) (D r eps : ℝ) (C : ℝ≥0)
    (heps : 0 < eps) (hepssmall : eps ≤ 1 / 1000)
    (hr : StandardCap.transitionEnd + eps⁻¹ + 1 < r)
    (hfit : 64 * (r + eps⁻¹) < D) :
    ∃ C₀ η ε₀ δ₀ B Cderiv : ℝ, 0 < C₀ ∧ 1 ≤ B ∧ 0 < Cderiv ∧ 0 < η ∧ 0 < ε₀ ∧ ε₀ ≤ 1 / 2 ∧ 0 < δ₀ ∧
      ∀ (H : ℕ → ObservedHistory.{u}) (event : ∀ i, Fin (H i).eventCount)
        (last : ∀ i, Fin ((H i).eventCount + 1)) (hle : ∀ i, (event i).succ ≤ last i)
        (time : ℕ → ℝ)
        (G : ∀ i, ((H i).stage (last i)).IncomingSlab ((H i).time (last i)) (time i))
        (L : ∀ i, (G i).TerminalLimitMetric),
      (∀ i, (G i).flow.base.metric ((H i).time (last i)) = (H i).initialMetric (last i)) →
      ∀ (parameters : ℕ → CutoffParameters)
        (records : ∀ i k, GeometricCutoffRecord (H i) k (parameters i))
        (boundary : ∀ i, ((H i).event (event i)).RetainedBoundaryIndex),
      let cap := fun i => (records i (event i)).static (boundary i)
      let q := fun i => (cap i).neck.scale
      let age := fun i => q i * (time i - (H i).time (event i).succ)
      (∀ i, (cap i).hasCanonicalWindow) →
      (∀ i, D + 1 ≤ (parameters i).modelRadius) →
      (∀ i, max ⌈eps⁻¹⌉₊ N + 2 ≤ (parameters i).modelOrder) →
      (∀ i, (parameters i).modelAccuracy ≤ ε₀) →
      Tendsto (fun i => (parameters i).modelAccuracy) atTop (𝓝 0) →
      ∀ (q₀ a₀ : ℕ → ℝ), (∀ i, 0 < q₀ i) →
      (∀ i, q₀ i ≤ C₀ * q i) → (∀ i, 1 ≤ a₀ i * q i) →
      (∀ i x, InFixedHamiltonIveyRegion ((H i).initialMetric 0) (a₀ i) x) →
      (∀ i x, -3 / a₀ i ≤ metricScalarAt ((H i).initialMetric 0) x) →
      (∀ i k, (event i).succ ≤ k.castSucc → k.succ ≤ last i →
        ∀ b, (records i k).delta b ≤ δ₀) →
      (∀ i k, (event i).succ ≤ k.castSucc → k.succ ≤ last i →
        ∀ x : ((H i).stage k.castSucc).Carrier,
        ∀ t ∈ Ioo ((H i).time k.castSucc) ((H i).time k.succ),
          q₀ i < ((H i).event k).incoming.flow.scalar t x →
          |derivWithin (fun v => ((H i).event k).incoming.flow.scalar v x) (Iic t) t| ≤
            C * ((H i).event k).incoming.flow.scalar t x ^ 2) →
      (∀ i x, ∀ t ∈ Ioo ((H i).time (last i)) (time i), q₀ i < (G i).flow.scalar t x →
        |derivWithin (fun v => (G i).flow.scalar v x) (Iic t) t| ≤ C * (G i).flow.scalar t x ^ 2) →
      (∀ i, age i ≤ η) → Tendsto age atTop (𝓝 0) →
      ∀ (z : ℕ → ThreeBall) (x : ∀ i, (G i).terminalRegularOpen)
        (trace : ∀ i, BackwardPointTrace (H i) (event i).succ (last i) (hle i) (x i).val),
      (∀ i, (trace i).point (event i).succ le_rfl (hle i) =
        (cap i).inclusion ((cap i).witness.cap (z i))) →
      ∃ (x₀ : ∀ i, ((H i).event (event i)).incoming.terminalRegularOpen)
        (delta : ℕ → ℝ) (order : ℕ → ℕ)
        (datum : ∀ i, normalizedDatum ((H i).event (event i)).terminal.metric
          (x₀ i) (delta i) (order i))
        (w : ∀ i, StandardCap.CanonicalStaticInsertionWitness (datum i)
          (parameters i).fixed.collarLength (parameters i).fixed.collar_pos
          (parameters i).modelRadius (parameters i).modelOrder (parameters i).modelAccuracy),
        (∀ i, metricScalarAt ((H i).event (event i)).terminal.metric (x₀ i) = q i) ∧
        (∀ i y (v z : TangentSpace ThreeModel y), (w i).windowMetric.inner y v z =
          q i * ((H i).initialMetric (event i).succ).inner ((cap i).window y)
            (mfderiv ThreeModel ThreeModel (cap i).window y v)
            (mfderiv ThreeModel ThreeModel (cap i).window y z)) ∧
        ∃ (u : ℕ → standardCapWindow D)
          (Ξ : ∀ i, standardCapWindow D →
            (H i).backwardSurvivorIncomingDomain (event i).succ (last i) (hle i) (G i))
          (hΞ : ∀ i, IsLocalDiffeomorph ThreeModel ThreeModel ∞ (Ξ i))
          (gflow : ∀ i, ℝ → SmoothRiemannianMetric ThreeModel
            ((H i).backwardSurvivorIncomingDomain (event i).succ (last i) (hle i) (G i)))
          (hmargin : ∀ i, D ≤ (parameters i).modelRadius)
          (hpos : ∀ i, 0 ≤ age i)
          (S : ∀ i, SolutionOn (I := ThreeModel) (M := standardCapWindow D)
            (RealTimeInterval.closed 0 (age i) (hpos i))),
          (∀ i, ‖(u i).val‖ ≤ StandardCap.transitionEnd) ∧
          (∀ i, (cap i).window ⟨(u i).val,
            (u i).property.trans_le (add_le_add (hmargin i) (le_refl 1))⟩ =
              (cap i).inclusion ((cap i).witness.cap (z i))) ∧
          (∀ i, IsSmoothEmbedding ThreeModel ThreeModel ∞ (Ξ i)) ∧
          (∀ i y, (H i).backwardSurvivorMap (event i).succ (last i) (hle i)
            (event i).succ le_rfl (hle i) ((Ξ i y).val) =
              (cap i).window ⟨y.val, y.property.trans_le (add_le_add (hmargin i) (le_refl 1))⟩) ∧
          (∀ i, (H i).backwardSurvivorIncomingMap (event i).succ (last i) (hle i)
            (G i) (Ξ i (u i)) = x i) ∧
          (∀ i k (hf : (event i).succ ≤ k.castSucc) (hl : k.succ ≤ last i),
            ∀ t ∈ Icc ((H i).time k.castSucc) ((H i).time k.succ),
              gflow i t = ((H i).backwardSurvivorSlabMetric (event i).succ (last i)
                (hle i) k hf hl t).restrictOpen
                  ((H i).backwardSurvivorIncomingDomain (event i).succ (last i) (hle i) (G i))) ∧
          (∀ i t, t ∈ Icc ((H i).time (last i)) (time i) →
            gflow i t = (H i).backwardSurvivorIncomingMetric (event i).succ (last i)
              (hle i) (G i) (L i) t) ∧
          (∀ i, IsSolutionOn (S i)) ∧
          (∀ i y (j k : Fin (Module.finrank ℝ ThreeSpace)),
            ContMDiffOn (𝓘(ℝ, ℝ).prod ThreeModel) 𝓘(ℝ) ∞
              (fun z : ℝ × standardCapWindow D => DifferentialGeometry.Tensor.Coordinates.chartGramMatrix
                ((S i).base.metric z.1) y z.2 j k)
              (Icc 0 (age i) ×ˢ (trivializationAt ThreeSpace (TangentSpace ThreeModel) y).baseSet)) ∧
          (∀ i j, j ≤ N → ∀ t ∈ Icc 0 (age i),
            ∀ y : standardCapWindow D, ‖y.val‖ ≤ r → curvDerivNormSq j ((S i).base.metric t) y ≤ B) ∧
          (2 ≤ N →
            (∀ i t, t ∈ Icc 0 (age i) → ∀ y : standardCapWindow D, ‖y.val‖ ≤ r →
              1 / 2 ≤ (S i).scalar t y → ∀ v : TangentSpace ThreeModel y,
                |Perelman.CanonicalNeighborhood.scalarDifferential (S i) t y v| ≤
                  Cderiv * (S i).scalar t y * Real.sqrt ((S i).scalar t y) *
                    Real.sqrt (((S i).base.metric t).inner y v v)) ∧
            (∀ i t, t ∈ Ioc 0 (age i) → ∀ y : standardCapWindow D, ‖y.val‖ ≤ r →
              1 / 2 ≤ (S i).scalar t y →
                |derivWithin (fun s => (S i).scalar s y) (Iic t) t| ≤
                  Cderiv * (S i).scalar t y ^ 2) ∧
            ∀ᶠ i in atTop, ∀ y : standardCapWindow D, ‖y.val‖ ≤ StandardCap.transitionEnd →
              1 / 2 ≤ (S i).scalar (age i) y) ∧
          (∀ i, (S i).base.metric 0 = (w i).windowMetric.restrictOpenOfSubset
            (show standardCapWindow D ≤ standardCapWindow (parameters i).modelRadius from
              fun _ hy => hy.trans_le (add_le_add (hmargin i) (le_refl 1)))) ∧
          (∀ i t, (S i).base.metric t = localPullMetric
            (scaleMetric (q i) (cap i).neck.scale_pos
              (gflow i ((H i).time (event i).succ + t / q i))) (Ξ i) (hΞ i)) ∧
          (∀ i y (v z : TangentSpace ThreeModel y), ((S i).base.metric (age i)).inner y v z =
            (scaleMetric (q i) (cap i).neck.scale_pos (L i).metric).inner
              ((H i).backwardSurvivorIncomingMap (event i).succ (last i) (hle i) (G i) (Ξ i y))
              (mfderiv ThreeModel ThreeModel
                ((H i).backwardSurvivorIncomingMap (event i).succ (last i) (hle i) (G i) ∘ Ξ i) y v)
              (mfderiv ThreeModel ThreeModel
                ((H i).backwardSurvivorIncomingMap (event i).succ (last i) (hle i) (G i) ∘ Ξ i) y z)) ∧
          (∀ a : ℝ, a < r → MetricCPConvergenceOn {y : standardCapWindow D | ‖y.val‖ ≤ a} N
            (fun i => (S i).base.metric (age i))
            (StandardCap.metric.restrictOpen (standardCapWindow D))
            (StandardCap.metric.restrictOpen (standardCapWindow D))) ∧
          (∀ a : ℝ, StandardCap.transitionEnd ≤ a → a < r → 2 ≤ N →
            ∃ (phi : ℕ → ℕ) (uLim : standardCapWindow D), StrictMono phi ∧
              ‖uLim.val‖ ≤ StandardCap.transitionEnd ∧ Tendsto (u ∘ phi) atTop (𝓝 uLim) ∧
              ∃ hlim : 1 ≤ metricScalarAt StandardCap.metric uLim.val,
                metricScalarAt (scaleMetric (metricScalarAt StandardCap.metric uLim.val)
                  (zero_lt_one.trans_le hlim) (StandardCap.metric.restrictOpen (standardCapWindow D))) uLim = 1 ∧
                Tendsto (fun n => metricScalarAt (L (phi n)).metric (x (phi n)) / q (phi n)) atTop
                  (𝓝 (metricScalarAt StandardCap.metric uLim.val)) ∧
                ∃ hR : ∀ n, 0 < metricScalarAt (L (phi n)).metric (x (phi n)),
                  MetricCPConvergenceOn {y : standardCapWindow D | ‖y.val‖ ≤ a} N
                    (fun n => localPullMetric
                      (scaleMetric (metricScalarAt (L (phi n)).metric (x (phi n))) (hR n) (L (phi n)).metric)
                      ((H (phi n)).backwardSurvivorIncomingMap (event (phi n)).succ (last (phi n))
                        (hle (phi n)) (G (phi n)) ∘ Ξ (phi n))
                      (isLocalDiffeomorph_comp
                        ((H (phi n)).backwardSurvivorIncomingMap_isLocalDiffeomorph
                          (event (phi n)).succ (last (phi n)) (hle (phi n)) (G (phi n))) (hΞ (phi n))))
                    (scaleMetric (metricScalarAt StandardCap.metric uLim.val)
                      (zero_lt_one.trans_le hlim) (StandardCap.metric.restrictOpen (standardCapWindow D)))
                    (scaleMetric (metricScalarAt StandardCap.metric uLim.val)
                      (zero_lt_one.trans_le hlim) (StandardCap.metric.restrictOpen (standardCapWindow D)))) ∧
          ∀ r₀ epsilon : ℝ, 0 < epsilon → epsilon < 1 / 11 →
            StandardCap.transitionEnd + epsilon⁻¹ + 1 < r₀ → r₀ + epsilon⁻¹ < r →
            ⌈epsilon⁻¹⌉₊ ≤ N → ∀ᶠ i in atTop,
              let Φ := (H i).backwardSurvivorIncomingMap (event i).succ (last i) (hle i) (G i) ∘ Ξ i
              let metric := scaleMetric (q i) (cap i).neck.scale_pos (L i).metric
              ∃ (p tip : standardCapWindow D), p.val = r₀ • (spherePoint : ThreeSpace) ∧ tip.val = 0 ∧
                ∃ (nk : SpatialNeck metric epsilon (Φ p)) (K : CompactDomain (G i).terminalRegularOpen),
                  K.carrier = Φ '' {y : standardCapWindow D | ‖y.val‖ ≤ r₀} ∧
                  Nonempty (CapCore K.carrier) ∧ x i ∈ interior K.carrier ∧
                  Φ tip ∈ interior K.carrier ∧
                  (∀ v : neckBuffer epsilon, ∃ y : standardCapWindow D,
                    y.val = (r₀ + v.val.2) • (v.val.1 : ThreeSpace) ∧ nk.map v.val = Φ y) ∧
                  frontier K.carrier = range (fun y : Sphere 2 => nk.map (y, 0)) ∧
                  IsSmoothEmbedding I2 I3 ∞ (fun y : Sphere 2 => nk.map (y, 0)) ∧
                  (∀ y : Sphere 2, ∀ t ∈ Ioo (-epsilon⁻¹) epsilon⁻¹,
                    nk.map (y, t) ∈ K.carrier ↔ t ≤ 0) ∧
                  |metricScalarAt metric (Φ p) - 1| ≤ epsilon ∧
                  K.carrier ⊆ riemannianBallOf metric (Φ tip) (2 * r₀) := by
  obtain ⟨C₀, B, Cderiv, hC₀, hB, hCderiv, huniform⟩ :=
    exists_uniform_canonical_cap_window_convergence_and_uniform_scalar_derivative_bounds_at_vanishing_age
      N D r eps heps hepssmall hr hfit
  obtain ⟨η, ε₀, δ₀, hη, hε₀, hεhalf, hδ₀, hproducer⟩ := huniform C
  exact ⟨C₀, η, ε₀, δ₀, B, Cderiv, hC₀, hB, hCderiv, hη, hε₀, hεhalf, hδ₀, hproducer⟩

theorem exists_uniform_canonical_cap_window_convergence_at_vanishing_age
    (N : ℕ) (D r eps : ℝ) (C : ℝ≥0)
    (heps : 0 < eps) (hepssmall : eps ≤ 1 / 1000)
    (hr : StandardCap.transitionEnd + eps⁻¹ + 1 < r)
    (hfit : 64 * (r + eps⁻¹) < D) :
    ∃ C₀ η ε₀ δ₀ B : ℝ, 0 < C₀ ∧ 1 ≤ B ∧ 0 < η ∧ 0 < ε₀ ∧ ε₀ ≤ 1 / 2 ∧ 0 < δ₀ ∧
      ∀ (H : ℕ → ObservedHistory.{u}) (event : ∀ i, Fin (H i).eventCount)
        (last : ∀ i, Fin ((H i).eventCount + 1)) (hle : ∀ i, (event i).succ ≤ last i)
        (time : ℕ → ℝ)
        (G : ∀ i, ((H i).stage (last i)).IncomingSlab ((H i).time (last i)) (time i))
        (L : ∀ i, (G i).TerminalLimitMetric),
      (∀ i, (G i).flow.base.metric ((H i).time (last i)) = (H i).initialMetric (last i)) →
      ∀ (parameters : ℕ → CutoffParameters)
        (records : ∀ i k, GeometricCutoffRecord (H i) k (parameters i))
        (boundary : ∀ i, ((H i).event (event i)).RetainedBoundaryIndex),
      let cap := fun i => (records i (event i)).static (boundary i)
      let q := fun i => (cap i).neck.scale
      let age := fun i => q i * (time i - (H i).time (event i).succ)
      (∀ i, (cap i).hasCanonicalWindow) →
      (∀ i, D + 1 ≤ (parameters i).modelRadius) →
      (∀ i, max ⌈eps⁻¹⌉₊ N + 2 ≤ (parameters i).modelOrder) →
      (∀ i, (parameters i).modelAccuracy ≤ ε₀) →
      Tendsto (fun i => (parameters i).modelAccuracy) atTop (𝓝 0) →
      ∀ (q₀ a₀ : ℕ → ℝ), (∀ i, 0 < q₀ i) →
      (∀ i, q₀ i ≤ C₀ * q i) → (∀ i, 1 ≤ a₀ i * q i) →
      (∀ i x, InFixedHamiltonIveyRegion ((H i).initialMetric 0) (a₀ i) x) →
      (∀ i x, -3 / a₀ i ≤ metricScalarAt ((H i).initialMetric 0) x) →
      (∀ i k, (event i).succ ≤ k.castSucc → k.succ ≤ last i →
        ∀ b, (records i k).delta b ≤ δ₀) →
      (∀ i k, (event i).succ ≤ k.castSucc → k.succ ≤ last i →
        ∀ x : ((H i).stage k.castSucc).Carrier,
        ∀ t ∈ Ioo ((H i).time k.castSucc) ((H i).time k.succ),
          q₀ i < ((H i).event k).incoming.flow.scalar t x →
          |derivWithin (fun v => ((H i).event k).incoming.flow.scalar v x) (Iic t) t| ≤
            C * ((H i).event k).incoming.flow.scalar t x ^ 2) →
      (∀ i x, ∀ t ∈ Ioo ((H i).time (last i)) (time i), q₀ i < (G i).flow.scalar t x →
        |derivWithin (fun v => (G i).flow.scalar v x) (Iic t) t| ≤ C * (G i).flow.scalar t x ^ 2) →
      (∀ i, age i ≤ η) → Tendsto age atTop (𝓝 0) →
      ∀ (z : ℕ → ThreeBall) (x : ∀ i, (G i).terminalRegularOpen)
        (trace : ∀ i, BackwardPointTrace (H i) (event i).succ (last i) (hle i) (x i).val),
      (∀ i, (trace i).point (event i).succ le_rfl (hle i) =
        (cap i).inclusion ((cap i).witness.cap (z i))) →
      ∃ (x₀ : ∀ i, ((H i).event (event i)).incoming.terminalRegularOpen)
        (delta : ℕ → ℝ) (order : ℕ → ℕ)
        (datum : ∀ i, normalizedDatum ((H i).event (event i)).terminal.metric
          (x₀ i) (delta i) (order i))
        (w : ∀ i, StandardCap.CanonicalStaticInsertionWitness (datum i)
          (parameters i).fixed.collarLength (parameters i).fixed.collar_pos
          (parameters i).modelRadius (parameters i).modelOrder (parameters i).modelAccuracy),
        (∀ i, metricScalarAt ((H i).event (event i)).terminal.metric (x₀ i) = q i) ∧
        (∀ i y (v z : TangentSpace ThreeModel y), (w i).windowMetric.inner y v z =
          q i * ((H i).initialMetric (event i).succ).inner ((cap i).window y)
            (mfderiv ThreeModel ThreeModel (cap i).window y v)
            (mfderiv ThreeModel ThreeModel (cap i).window y z)) ∧
        ∃ (u : ℕ → standardCapWindow D)
          (Ξ : ∀ i, standardCapWindow D →
            (H i).backwardSurvivorIncomingDomain (event i).succ (last i) (hle i) (G i))
          (hΞ : ∀ i, IsLocalDiffeomorph ThreeModel ThreeModel ∞ (Ξ i))
          (gflow : ∀ i, ℝ → SmoothRiemannianMetric ThreeModel
            ((H i).backwardSurvivorIncomingDomain (event i).succ (last i) (hle i) (G i)))
          (hmargin : ∀ i, D ≤ (parameters i).modelRadius)
          (hpos : ∀ i, 0 ≤ age i)
          (S : ∀ i, SolutionOn (I := ThreeModel) (M := standardCapWindow D)
            (RealTimeInterval.closed 0 (age i) (hpos i))),
          (∀ i, ‖(u i).val‖ ≤ StandardCap.transitionEnd) ∧
          (∀ i, (cap i).window ⟨(u i).val,
            (u i).property.trans_le (add_le_add (hmargin i) (le_refl 1))⟩ =
              (cap i).inclusion ((cap i).witness.cap (z i))) ∧
          (∀ i, IsSmoothEmbedding ThreeModel ThreeModel ∞ (Ξ i)) ∧
          (∀ i y, (H i).backwardSurvivorMap (event i).succ (last i) (hle i)
            (event i).succ le_rfl (hle i) ((Ξ i y).val) =
              (cap i).window ⟨y.val, y.property.trans_le (add_le_add (hmargin i) (le_refl 1))⟩) ∧
          (∀ i, (H i).backwardSurvivorIncomingMap (event i).succ (last i) (hle i)
            (G i) (Ξ i (u i)) = x i) ∧
          (∀ i k (hf : (event i).succ ≤ k.castSucc) (hl : k.succ ≤ last i),
            ∀ t ∈ Icc ((H i).time k.castSucc) ((H i).time k.succ),
              gflow i t = ((H i).backwardSurvivorSlabMetric (event i).succ (last i)
                (hle i) k hf hl t).restrictOpen
                  ((H i).backwardSurvivorIncomingDomain (event i).succ (last i) (hle i) (G i))) ∧
          (∀ i t, t ∈ Icc ((H i).time (last i)) (time i) →
            gflow i t = (H i).backwardSurvivorIncomingMetric (event i).succ (last i)
              (hle i) (G i) (L i) t) ∧
          (∀ i, IsSolutionOn (S i)) ∧
          (∀ i y (j k : Fin (Module.finrank ℝ ThreeSpace)),
            ContMDiffOn (𝓘(ℝ, ℝ).prod ThreeModel) 𝓘(ℝ) ∞
              (fun z : ℝ × standardCapWindow D => DifferentialGeometry.Tensor.Coordinates.chartGramMatrix
                ((S i).base.metric z.1) y z.2 j k)
              (Icc 0 (age i) ×ˢ (trivializationAt ThreeSpace (TangentSpace ThreeModel) y).baseSet)) ∧
          (∀ i j, j ≤ N → ∀ t ∈ Icc 0 (age i),
            ∀ y : standardCapWindow D, ‖y.val‖ ≤ r → curvDerivNormSq j ((S i).base.metric t) y ≤ B) ∧
          (∀ i, (S i).base.metric 0 = (w i).windowMetric.restrictOpenOfSubset
            (show standardCapWindow D ≤ standardCapWindow (parameters i).modelRadius from
              fun _ hy => hy.trans_le (add_le_add (hmargin i) (le_refl 1)))) ∧
          (∀ i t, (S i).base.metric t = localPullMetric
            (scaleMetric (q i) (cap i).neck.scale_pos
              (gflow i ((H i).time (event i).succ + t / q i))) (Ξ i) (hΞ i)) ∧
          (∀ i y (v z : TangentSpace ThreeModel y), ((S i).base.metric (age i)).inner y v z =
            (scaleMetric (q i) (cap i).neck.scale_pos (L i).metric).inner
              ((H i).backwardSurvivorIncomingMap (event i).succ (last i) (hle i) (G i) (Ξ i y))
              (mfderiv ThreeModel ThreeModel
                ((H i).backwardSurvivorIncomingMap (event i).succ (last i) (hle i) (G i) ∘ Ξ i) y v)
              (mfderiv ThreeModel ThreeModel
                ((H i).backwardSurvivorIncomingMap (event i).succ (last i) (hle i) (G i) ∘ Ξ i) y z)) ∧
          (∀ a : ℝ, a < r → MetricCPConvergenceOn {y : standardCapWindow D | ‖y.val‖ ≤ a} N
            (fun i => (S i).base.metric (age i))
            (StandardCap.metric.restrictOpen (standardCapWindow D))
            (StandardCap.metric.restrictOpen (standardCapWindow D))) ∧
          (∀ a : ℝ, StandardCap.transitionEnd ≤ a → a < r → 2 ≤ N →
            ∃ (phi : ℕ → ℕ) (uLim : standardCapWindow D), StrictMono phi ∧
              ‖uLim.val‖ ≤ StandardCap.transitionEnd ∧ Tendsto (u ∘ phi) atTop (𝓝 uLim) ∧
              ∃ hlim : 1 ≤ metricScalarAt StandardCap.metric uLim.val,
                metricScalarAt (scaleMetric (metricScalarAt StandardCap.metric uLim.val)
                  (zero_lt_one.trans_le hlim) (StandardCap.metric.restrictOpen (standardCapWindow D))) uLim = 1 ∧
                Tendsto (fun n => metricScalarAt (L (phi n)).metric (x (phi n)) / q (phi n)) atTop
                  (𝓝 (metricScalarAt StandardCap.metric uLim.val)) ∧
                ∃ hR : ∀ n, 0 < metricScalarAt (L (phi n)).metric (x (phi n)),
                  MetricCPConvergenceOn {y : standardCapWindow D | ‖y.val‖ ≤ a} N
                    (fun n => localPullMetric
                      (scaleMetric (metricScalarAt (L (phi n)).metric (x (phi n))) (hR n) (L (phi n)).metric)
                      ((H (phi n)).backwardSurvivorIncomingMap (event (phi n)).succ (last (phi n))
                        (hle (phi n)) (G (phi n)) ∘ Ξ (phi n))
                      (isLocalDiffeomorph_comp
                        ((H (phi n)).backwardSurvivorIncomingMap_isLocalDiffeomorph
                          (event (phi n)).succ (last (phi n)) (hle (phi n)) (G (phi n))) (hΞ (phi n))))
                    (scaleMetric (metricScalarAt StandardCap.metric uLim.val)
                      (zero_lt_one.trans_le hlim) (StandardCap.metric.restrictOpen (standardCapWindow D)))
                    (scaleMetric (metricScalarAt StandardCap.metric uLim.val)
                      (zero_lt_one.trans_le hlim) (StandardCap.metric.restrictOpen (standardCapWindow D)))) ∧
          ∀ r₀ epsilon : ℝ, 0 < epsilon → epsilon < 1 / 11 →
            StandardCap.transitionEnd + epsilon⁻¹ + 1 < r₀ → r₀ + epsilon⁻¹ < r →
            ⌈epsilon⁻¹⌉₊ ≤ N → ∀ᶠ i in atTop,
              let Φ := (H i).backwardSurvivorIncomingMap (event i).succ (last i) (hle i) (G i) ∘ Ξ i
              let metric := scaleMetric (q i) (cap i).neck.scale_pos (L i).metric
              ∃ (p tip : standardCapWindow D), p.val = r₀ • (spherePoint : ThreeSpace) ∧ tip.val = 0 ∧
                ∃ (nk : SpatialNeck metric epsilon (Φ p)) (K : CompactDomain (G i).terminalRegularOpen),
                  K.carrier = Φ '' {y : standardCapWindow D | ‖y.val‖ ≤ r₀} ∧
                  Nonempty (CapCore K.carrier) ∧ x i ∈ interior K.carrier ∧
                  Φ tip ∈ interior K.carrier ∧
                  (∀ v : neckBuffer epsilon, ∃ y : standardCapWindow D,
                    y.val = (r₀ + v.val.2) • (v.val.1 : ThreeSpace) ∧ nk.map v.val = Φ y) ∧
                  frontier K.carrier = range (fun y : Sphere 2 => nk.map (y, 0)) ∧
                  IsSmoothEmbedding I2 I3 ∞ (fun y : Sphere 2 => nk.map (y, 0)) ∧
                  (∀ y : Sphere 2, ∀ t ∈ Ioo (-epsilon⁻¹) epsilon⁻¹,
                    nk.map (y, t) ∈ K.carrier ↔ t ≤ 0) ∧
                  |metricScalarAt metric (Φ p) - 1| ≤ epsilon ∧
                  K.carrier ⊆ riemannianBallOf metric (Φ tip) (2 * r₀) := by
  obtain ⟨C₀, η, ε₀, δ₀, B, Cderiv, hC₀, hB, hCderiv, hη, hε₀, hεhalf, hδ₀, hproducer⟩ :=
    exists_uniform_canonical_cap_window_convergence_and_scalar_derivative_bounds_at_vanishing_age
      N D r eps C heps hepssmall hr hfit
  refine ⟨C₀, η, ε₀, δ₀, B, hC₀, hB, hη, hε₀, hεhalf, hδ₀, ?_⟩
  intro H event last hle time G L hinit parameters records boundary cap q age
    hcanonical hmargin hm herror herrorlim q₀ a₀ hq₀ hqcap hacap hfixed hlower hδ hderiv hfinal
    hage hagelim z x trace hbirth
  obtain ⟨x₀, delta, order, datum, w, hwscalar, hwmetric, u, Ξ, hΞ, gflow, hmargin', hpos, S,
    hu, hucap, hΞsmooth, hΞbirth, hΞpoint, hslabs, hlast, hS, hgram, hjets, hbounds, hzero,
    hmetric, hterminal, hconvergence, hmarked, hcaps⟩ :=
    hproducer H event last hle time G L hinit parameters records boundary hcanonical hmargin hm
      herror herrorlim q₀ a₀ hq₀ hqcap hacap hfixed hlower hδ hderiv hfinal hage hagelim z x trace hbirth
  exact ⟨x₀, delta, order, datum, w, hwscalar, hwmetric, u, Ξ, hΞ, gflow, hmargin', hpos, S,
    hu, hucap, hΞsmooth, hΞbirth, hΞpoint, hslabs, hlast, hS, hgram, hjets, hzero,
    hmetric, hterminal, hconvergence, hmarked, hcaps⟩

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory
