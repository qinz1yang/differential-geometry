import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CanonicalCapInitialLimit
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.MarkedScalarBounds
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistoricalIncomingScalarDerivative

set_option autoImplicit false
noncomputable section
open Set Filter Manifold
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff Topology NNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory
universe u

theorem exists_uniform_scalar_derivative_bounds_at_canonical_cap_points_of_vanishing_age
    (N : ℕ) (hN : 2 ≤ N) (D r eps : ℝ)
    (heps : 0 < eps) (hepssmall : eps ≤ 1 / 1000)
    (hr : StandardCap.transitionEnd + eps⁻¹ + 1 < r)
    (hfit : 64 * (r + eps⁻¹) < D) :
    ∃ C₀ Cphys : ℝ, 0 < C₀ ∧ 0 < Cphys ∧
      ∀ (C : ℝ≥0), ∃ (η ε₀ δ₀ : ℝ), 0 < η ∧ 0 < ε₀ ∧ ε₀ ≤ 1 / 2 ∧ 0 < δ₀ ∧
      ∀ (H : ℕ → ObservedHistory.{u}) (event : ∀ i, Fin (H i).eventCount)
        (last : ∀ i, Fin ((H i).eventCount + 1)) (hle : ∀ i, (event i).succ ≤ last i)
        (time : ℕ → ℝ)
        (A : ∀ i, ((H i).stage (last i)).ClosedSlab ((H i).time (last i)) (time i)),
      (∀ i, (A i).flow.base.metric ((H i).time (last i)) = (H i).initialMetric (last i)) →
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
      (∀ i x, ∀ t ∈ Ioo ((H i).time (last i)) (time i), q₀ i < (A i).flow.scalar t x →
        |derivWithin (fun v => (A i).flow.scalar v x) (Iic t) t| ≤ C * (A i).flow.scalar t x ^ 2) →
      (∀ i, age i ≤ η) → Tendsto age atTop (𝓝 0) →
      ∀ (z : ℕ → ThreeBall) (x : ∀ i, ((H i).stage (last i)).Carrier)
        (trace : ∀ i, BackwardPointTrace (H i) (event i).succ (last i) (hle i) (x i)),
      (∀ i, (trace i).point (event i).succ le_rfl (hle i) =
        (cap i).inclusion ((cap i).witness.cap (z i))) →
      ∀ᶠ i in atTop,
        (∀ v : TangentSpace ThreeModel (x i),
          |(show ℝ from mfderiv ThreeModel 𝓘(ℝ, ℝ) ((A i).flow.scalar (time i)) (x i) v)| ≤
            Cphys * (A i).flow.scalar (time i) (x i) * Real.sqrt ((A i).flow.scalar (time i) (x i)) *
              Real.sqrt (((A i).flow.base.metric (time i)).inner (x i) v v)) ∧
        |derivWithin (fun t => (A i).flow.scalar t (x i)) (Iic (time i)) (time i)| ≤
          Cphys * (A i).flow.scalar (time i) (x i) ^ 2 := by
  obtain ⟨C₀, B, Cderiv, hC₀, hB, hCderiv, huniform⟩ :=
    exists_uniform_canonical_cap_window_convergence_and_uniform_scalar_derivative_bounds_at_vanishing_age
      N D r eps heps hepssmall hr hfit
  have hcore : StandardCap.transitionEnd < r := by linarith [inv_pos.mpr heps]
  have hcoreD : StandardCap.transitionEnd < D + 1 := by linarith [hfit, inv_pos.mpr heps, StandardCap.transitionEnd_pos]
  obtain ⟨Cphys, hCphys, hphysical⟩ :=
    StandardCap.exists_eventually_relative_scalar_derivative_bounds_of_metric_cp_convergence
      hcoreD hN B (zero_le_one.trans hB)
  refine ⟨C₀, Cphys, hC₀, hCphys, ?_⟩
  intro C
  obtain ⟨η, ε₀, δ₀, hη, hε₀, hεhalf, hδ₀, hproducer⟩ := huniform C
  refine ⟨η, ε₀, δ₀, hη, hε₀, hεhalf, hδ₀, ?_⟩
  intro H event last hle time A hinit parameters records boundary cap q age
    hcanonical hmargin hm herror herrorlim q₀ a₀ hq₀ hqcap hacap hfixed hlower hδ hderiv hfinal
    hage hagelim z x trace hbirth
  let G i := (A i).restrictIncoming le_rfl (A i).lt le_rfl
  let L i := (A i).endpointTerminalLimitMetric ((H i).stage (last i))
  let x' (i : ℕ) : (G i).terminalRegularOpen := ⟨x i, by
    change x i ∈ (G i).terminalRegularRegion
    rw [(A i).terminalRegularRegion_eq_univ ((H i).stage (last i))]
    trivial⟩
  obtain ⟨x₀, delta, order, datum, w, hwscalar, hwmetric, u, Ξ, hΞ, gflow, hmargin', hpos, S,
    hu, hucap, hΞsmooth, hΞbirth, hΞpoint, hslabs, hlast, hS, hgram, hjets, hbounds, hzero,
    hmetric, hterminal, hconvergence, hmarked, hcaps⟩ :=
    hproducer H event last hle time G L hinit parameters records boundary hcanonical hmargin hm
      herror herrorlim q₀ a₀ hq₀ hqcap hacap hfixed hlower hδ hderiv hfinal hage hagelim z x' trace hbirth
  have hagepos (i : ℕ) : 0 < age i := by
    exact mul_pos (cap i).neck.scale_pos
      (sub_pos.mpr (((H i).time_strictMono.monotone (hle i)).trans_lt (A i).lt))
  have hp := hphysical (fun i => RealTimeInterval.closed 0 (age i) (hpos i)) age hagepos
    S hS (fun _ => Subset.rfl) (fun _ => Subset.rfl)
    (fun i j hj t ht y hy => hjets i j (hj.trans hN) t ht y (hy.trans hcore.le))
    (hconvergence StandardCap.transitionEnd hcore)
    (fun i => (H i).backwardSurvivorIncomingDomain (event i).succ (last i) (hle i) (G i))
    gflow Ξ hΞ q (fun i => (H i).time (event i).succ)
    (fun i => (cap i).neck.scale_pos) (fun i t _ => hmetric i t)
  filter_upwards [hp] with i hi
  have hb := hi (u i) (hu i)
  have hclock : (H i).time (event i).succ + age i / q i = time i := by
    dsimp only [age]
    rw [mul_div_cancel_left₀ _ (show q i ≠ 0 from (cap i).neck.scale_pos.ne')]
    ring
  rw [hclock] at hb
  have hpoint : (Ξ i (u i)).val.val = x i := congrArg Subtype.val (hΞpoint i)
  have hgradient := (H i).scalar_gradient_bound_closed_slab_endpoint_of_backwardSurvivorIncomingMetric
    (event i).succ (last i) (hle i) (A i) (gflow i (time i))
    (hlast i (time i) ⟨(A i).lt.le, le_rfl⟩) (Ξ i (u i)) hb.1
  have heq := (H i).scalar_eventually_eq_backwardSurvivorIncomingDomain_of_closed_slab_endpoint
    (event i).succ (last i) (hle i) (A i) (gflow i) (hlast i) (Ξ i (u i))
  have htime := hb.2
  rw [heq.derivWithin_eq_of_mem (mem_Iic.mpr le_rfl),
    heq.eq_of_nhdsWithin (mem_Iic.mpr le_rfl)] at htime
  rw [hpoint] at hgradient htime
  exact ⟨hgradient, htime⟩

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory
