import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistorySurvivorIncomingDerivatives
import DifferentialGeometry.Geometry.Metric.Distance.MetricLocality
import DifferentialGeometry.Geometry.Metric.Distance.LocalBall
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.Derivatives.LocalPullback
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TerminalBackwardFlow
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CanonicalCapWindows
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.PreparedCapBallCurvature
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.InitialCapScale
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CanonicalCapScalar

noncomputable section
open Set DifferentialGeometry
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.CheegerGromovCompactness
open scoped Manifold ContDiff NNReal ENNReal
namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory
universe u
variable (H : ObservedHistory.{u}) (first last : Fin (H.eventCount + 1)) (hle : first ≤ last)
  {s : ℝ} (G : (H.stage last).IncomingSlab (H.time last) s) (L : G.TerminalLimitMetric)

theorem curvDerivNorm_scaleMetric_terminal_le_on_closedBall_of_backwardPointTrace
    (hinit : G.flow.base.metric (H.time last) = H.initialMetric last)
    (x : G.terminalRegularOpen) {a r q Q θ : ℝ} {C : ℝ≥0}
    (ha : 0 ≤ a) (hr : 0 < r) (hq : 0 < q) (hqQ : q ≤ Q) (hQ : 1 ≤ Q) (hθ : 0 < θ)
    (hcompact : IsCompact (riemannianClosedBallOf L.metric x ((a + r) / Real.sqrt Q)))
    {Phi : ℝ → ℝ} (hPhi : Perelman.AdmissiblePinchingFunction Phi)
    (hbound : ∀ j : Fin H.eventCount, first ≤ j.castSucc → j.succ ≤ last →
      ∀ y : (H.stage j.castSucc).Carrier, ∀ t ∈ Ioo (H.time j.castSucc) (H.time j.succ),
      q < (H.event j).incoming.flow.scalar t y →
      |derivWithin (fun v => (H.event j).incoming.flow.scalar v y) (Iic t) t| ≤
        C * (H.event j).incoming.flow.scalar t y ^ 2)
    (hfinal : ∀ y ∈ riemannianClosedBallOf L.metric x ((a + r) / Real.sqrt Q),
      ∀ t ∈ Ioo (H.time last) s, q < G.flow.scalar t y.val →
      |derivWithin (fun v => G.flow.scalar v y.val) (Iic t) t| ≤ C * G.flow.scalar t y.val ^ 2)
    (hpinch : ∀ j : Fin H.eventCount, first ≤ j.castSucc → j.succ ≤ last →
      Perelman.PhiAlmostNonnegative (H.event j).incoming.flow
        (Ico (H.time j.castSucc) (H.time j.succ)) Phi)
    (hpinchFinal : Perelman.PhiAlmostNonnegative G.flow (Ico (H.time last) s) Phi)
    (hscalar : ∀ y ∈ riemannianClosedBallOf L.metric x ((a + r) / Real.sqrt Q),
      metricScalarAt L.metric y ≤ 2 * Q)
    (htrace : ∀ y ∈ riemannianClosedBallOf L.metric x ((a + r) / Real.sqrt Q),
      Nonempty (BackwardPointTrace H first last hle y.val))
    (hc : H.time first ≤ s - θ / Q) (htime : 6 * C * θ ≤ 1) :
    let B := 4 * Real.sqrt 3 * (1 + Phi 4 + Phi 0)
    ∀ y ∈ riemannianClosedBallOf L.metric x (a / Real.sqrt Q),
    ∀ m : ℕ, curvDerivNorm m (scaleMetric Q (zero_lt_one.trans_le hQ) L.metric) y ≤
      shiLocalUniformBound 3 m (B * (θ / 4))
        (((r / 2) / (4 * Real.exp (9 * B * θ))) * Real.sqrt B /
          (4 * Real.exp (9 * B * (θ / 4)))) * B / Real.sqrt (θ / 4) ^ m := by
  dsimp only
  intro y hy m
  have hQpos : 0 < Q := zero_lt_one.trans_le hQ
  have hsub : riemannianClosedBallOf L.metric y (r / Real.sqrt Q) ⊆
      riemannianClosedBallOf L.metric x ((a + r) / Real.sqrt Q) :=
    riemannianClosedBallOf_subset_of_add_radius_le L.metric
      (div_nonneg ha (Real.sqrt_nonneg _)) (div_nonneg hr.le (Real.sqrt_nonneg _))
      (by rw [add_div]) hy
  exact H.curvDerivNorm_scaleMetric_terminal_le_of_backwardPointTrace first last hle G L
    hinit y hr hq hqQ hQ hθ
    (hcompact.of_isClosed_subset (Geometry.Metric.isClosed_riemannianClosedBallOf L.metric y _) hsub)
    hPhi hbound (fun z hz => hfinal z (hsub hz)) hpinch hpinchFinal
    (fun z hz => hscalar z (hsub hz)) (fun z hz => htrace z (hsub hz)) hc htime m

theorem curvDerivNorm_localPullMetric_terminal_le_on_set_of_backwardPointTrace
    (hinit : G.flow.base.metric (H.time last) = H.initialMetric last)
    (x : G.terminalRegularOpen) {a r q Q θ : ℝ} {C : ℝ≥0}
    (ha : 0 ≤ a) (hr : 0 < r) (hq : 0 < q) (hqQ : q ≤ Q) (hQ : 1 ≤ Q) (hθ : 0 < θ)
    (hcompact : IsCompact (riemannianClosedBallOf L.metric x ((a + r) / Real.sqrt Q)))
    {Phi : ℝ → ℝ} (hPhi : Perelman.AdmissiblePinchingFunction Phi)
    (hbound : ∀ j : Fin H.eventCount, first ≤ j.castSucc → j.succ ≤ last →
      ∀ y : (H.stage j.castSucc).Carrier, ∀ t ∈ Ioo (H.time j.castSucc) (H.time j.succ),
      q < (H.event j).incoming.flow.scalar t y →
      |derivWithin (fun v => (H.event j).incoming.flow.scalar v y) (Iic t) t| ≤
        C * (H.event j).incoming.flow.scalar t y ^ 2)
    (hfinal : ∀ y ∈ riemannianClosedBallOf L.metric x ((a + r) / Real.sqrt Q),
      ∀ t ∈ Ioo (H.time last) s, q < G.flow.scalar t y.val →
      |derivWithin (fun v => G.flow.scalar v y.val) (Iic t) t| ≤ C * G.flow.scalar t y.val ^ 2)
    (hpinch : ∀ j : Fin H.eventCount, first ≤ j.castSucc → j.succ ≤ last →
      Perelman.PhiAlmostNonnegative (H.event j).incoming.flow
        (Ico (H.time j.castSucc) (H.time j.succ)) Phi)
    (hpinchFinal : Perelman.PhiAlmostNonnegative G.flow (Ico (H.time last) s) Phi)
    (hscalar : ∀ y ∈ riemannianClosedBallOf L.metric x ((a + r) / Real.sqrt Q),
      metricScalarAt L.metric y ≤ 2 * Q)
    (htrace : ∀ y ∈ riemannianClosedBallOf L.metric x ((a + r) / Real.sqrt Q),
      Nonempty (BackwardPointTrace H first last hle y.val))
    (hc : H.time first ≤ s - θ / Q) (htime : 6 * C * θ ≤ 1) :
    ∀ {E J X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
      [TopologicalSpace J] {I : ModelWithCorners ℝ E J}
      [TopologicalSpace X] [ChartedSpace J X] [IsManifold I ∞ X] [T2Space X]
      (Φ : X → G.terminalRegularOpen) (hΦ : IsLocalDiffeomorph I ThreeModel ∞ Φ)
      (K : Set X),
      MapsTo Φ K (riemannianClosedBallOf L.metric x (a / Real.sqrt Q)) →
      let B := 4 * Real.sqrt 3 * (1 + Phi 4 + Phi 0)
      ∀ y ∈ K, ∀ m : ℕ,
        curvDerivNorm m (localPullMetric (scaleMetric Q (zero_lt_one.trans_le hQ) L.metric) Φ hΦ) y ≤
          shiLocalUniformBound 3 m (B * (θ / 4))
            (((r / 2) / (4 * Real.exp (9 * B * θ))) * Real.sqrt B /
              (4 * Real.exp (9 * B * (θ / 4)))) * B / Real.sqrt (θ / 4) ^ m := by
  intro E _ _ _ J _ I X _ _ _ _ Φ hΦ K hK
  dsimp only
  intro y hy m
  rw [curvDerivNorm_localPullMetric]
  exact H.curvDerivNorm_scaleMetric_terminal_le_on_closedBall_of_backwardPointTrace
    first last hle G L hinit x ha hr hq hqQ hQ hθ hcompact hPhi hbound hfinal
    hpinch hpinchFinal hscalar htrace hc htime (Φ y) (hK hy) m

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

end

noncomputable section
open Set DifferentialGeometry
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.CheegerGromovCompactness
open scoped Manifold ContDiff NNReal ENNReal
namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory
universe u
variable (H : ObservedHistory.{u}) (first last : Fin (H.eventCount + 1)) (hle : first ≤ last)
  {s : ℝ} (G : (H.stage last).IncomingSlab (H.time last) s) (L : G.TerminalLimitMetric)

include hle in
theorem curvature_derivative_bound_on_closedBall_or_recent_static_cap
    (hinit : G.flow.base.metric (H.time last) = H.initialMetric last)
    (x : G.terminalRegularOpen) {a r q Q θ : ℝ} {C : ℝ≥0}
    (ha : 0 ≤ a) (hr : 0 < r) (hq : 0 < q) (hqQ : q ≤ Q) (hQ : 1 ≤ Q) (hθ : 0 < θ)
    (hcompact : IsCompact (riemannianClosedBallOf L.metric x ((a + r) / Real.sqrt Q)))
    {Phi : ℝ → ℝ} (hPhi : Perelman.AdmissiblePinchingFunction Phi)
    (hbound : ∀ j : Fin H.eventCount, first ≤ j.castSucc → j.succ ≤ last →
      ∀ y : (H.stage j.castSucc).Carrier, ∀ t ∈ Ioo (H.time j.castSucc) (H.time j.succ),
      q < (H.event j).incoming.flow.scalar t y →
      |derivWithin (fun v => (H.event j).incoming.flow.scalar v y) (Iic t) t| ≤
        C * (H.event j).incoming.flow.scalar t y ^ 2)
    (hfinal : ∀ y ∈ riemannianClosedBallOf L.metric x ((a + r) / Real.sqrt Q),
      ∀ t ∈ Ioo (H.time last) s, q < G.flow.scalar t y.val →
      |derivWithin (fun v => G.flow.scalar v y.val) (Iic t) t| ≤ C * G.flow.scalar t y.val ^ 2)
    (hpinch : ∀ j : Fin H.eventCount, first ≤ j.castSucc → j.succ ≤ last →
      Perelman.PhiAlmostNonnegative (H.event j).incoming.flow
        (Ico (H.time j.castSucc) (H.time j.succ)) Phi)
    (hpinchFinal : Perelman.PhiAlmostNonnegative G.flow (Ico (H.time last) s) Phi)
    (hscalar : ∀ y ∈ riemannianClosedBallOf L.metric x ((a + r) / Real.sqrt Q),
      metricScalarAt L.metric y ≤ (3 / 2 : ℝ) * Q)
    {parameters : CutoffParameters}
    (records : ∀ j : Fin H.eventCount, GeometricCutoffRecord H j parameters)
    (hθsmall : θ ≤ 1 / 4)
    (hcrossTime : ∀ j : Fin H.eventCount, first ≤ j.castSucc → j.succ ≤ last →
      s - θ / Q < H.time j.succ)
    (hcap : ∀ j : Fin H.eventCount, first ≤ j.castSucc → j.succ ≤ last →
      ∀ (b : (H.event j).RetainedBoundaryIndex) (z : ThreeBall),
        ((records j).static b).neck.scale / 2 ≤
          metricScalarAt ((records j).static b).witness.metric (((records j).static b).witness.cap z))
    (hc : H.time first ≤ s - θ / Q) (htime : 6 * C * θ ≤ 1) :
    let B := 4 * Real.sqrt 3 * (1 + Phi 4 + Phi 0)
    (∀ y ∈ riemannianClosedBallOf L.metric x (a / Real.sqrt Q),
    ∀ m : ℕ, curvDerivNorm m (scaleMetric Q (zero_lt_one.trans_le hQ) L.metric) y ≤
      shiLocalUniformBound 3 m (B * (θ / 4))
        (((r / 2) / (4 * Real.exp (9 * B * θ))) * Real.sqrt B /
          (4 * Real.exp (9 * B * (θ / 4)))) * B / Real.sqrt (θ / 4) ^ m) ∨
      ∃ y ∈ riemannianClosedBallOf L.metric x ((a + r) / Real.sqrt Q),
        ∃ (j : Fin H.eventCount), first ≤ j.castSucc ∧ ∃ (hl : j.succ ≤ last)
          (A : BackwardPointTrace H j.succ last hl y.val)
          (b : (H.event j).RetainedBoundaryIndex) (z : ThreeBall),
          ¬ Nonempty (BackwardPointTrace H first last hle y.val) ∧
          (H.event j).transition.trace.presentation ((H.event j).transition.trace.capping.cap b.val z) =
            Sum.inl (A.point j.succ le_rfl hl) ∧
          A.point j.succ le_rfl hl = ((records j).static b).inclusion (((records j).static b).witness.cap z) ∧
          metricScalarAt (H.event j).outputMetric (A.point j.succ le_rfl hl) < 2 * Q ∧
          ((records j).static b).neck.scale < 4 * Q ∧
          0 < ((records j).static b).neck.scale * (s - H.time j.succ) ∧
          ((records j).static b).neck.scale * (s - H.time j.succ) < 4 * θ ∧
          ((records j).static b).neck.scale * (s - H.time j.succ) < 1 := by
  dsimp only
  rcases H.backward_traces_on_set_or_recent_presented_cap first last hle G L hinit
    (riemannianClosedBallOf L.metric x ((a + r) / Real.sqrt Q)) hq hqQ hθsmall htime
    hcrossTime hscalar (fun j hf hl => hbound j hf.le hl) hfinal
    (fun j _ _ => (records j).old_eq_retained) (fun j _ _ => (records j).static) hcap with
    htraces | hcapbirth
  · left
    apply H.curvDerivNorm_scaleMetric_terminal_le_on_closedBall_of_backwardPointTrace
      first last hle G L hinit x ha hr hq hqQ hQ hθ hcompact hPhi hbound hfinal
      hpinch hpinchFinal _ htraces hc htime
    intro y hy
    have := hscalar y hy
    have hQpos : 0 < Q := zero_lt_one.trans_le hQ
    linarith
  · obtain ⟨y, hy, j, hf, hl, A, b, z, hrest⟩ := hcapbirth
    exact Or.inr ⟨y, hy, j, hf, hl, A, b, z, hrest⟩

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

end

noncomputable section
open Set Function Bundle Manifold DifferentialGeometry
open DifferentialGeometry.Geometry.Neck DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness
open scoped Manifold ContDiff NNReal ENNReal
namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory
universe u
private local instance : Fact (Module.finrank ℝ ThreeSpace = 3) := ⟨by simp⟩

theorem exists_uniform_canonical_cap_closedBall_curvature_derivative_bound
    (N : ℕ) (D r eps : ℝ) (C : ℝ≥0)
    (heps : 0 < eps) (hepssmall : eps ≤ 1 / 1000)
    (hr : StandardCap.transitionEnd + eps⁻¹ + 1 < r)
    (hfit : 64 * (r + eps⁻¹) < D) :
    ∃ C₀ η ε₀ δ₀ B : ℝ, 0 < C₀ ∧ 1 ≤ B ∧ 0 < η ∧ 0 < ε₀ ∧ ε₀ ≤ 1 / 2 ∧ 0 < δ₀ ∧
      ∀ (H : ObservedHistory.{u}) (j : Fin H.eventCount) (last : Fin (H.eventCount + 1))
        (hle : j.succ ≤ last) (s : ℝ) (G : (H.stage last).IncomingSlab (H.time last) s)
        (L : G.TerminalLimitMetric), G.flow.base.metric (H.time last) = H.initialMetric last →
      ∀ (parameters : CutoffParameters) (records : ∀ k : Fin H.eventCount, GeometricCutoffRecord H k parameters)
        (b : (H.event j).RetainedBoundaryIndex),
      ((records j).static b).hasCanonicalWindow → D + 1 ≤ parameters.modelRadius →
      max ⌈eps⁻¹⌉₊ N + 2 ≤ parameters.modelOrder → parameters.modelAccuracy ≤ ε₀ →
      ∀ q₀ a₀ : ℝ, 0 < q₀ → q₀ ≤ C₀ * ((records j).static b).neck.scale →
      1 ≤ a₀ * ((records j).static b).neck.scale →
      (∀ x, InFixedHamiltonIveyRegion (H.initialMetric 0) a₀ x) →
      (∀ x, -3 / a₀ ≤ metricScalarAt (H.initialMetric 0) x) →
      (∀ k : Fin H.eventCount, j.succ ≤ k.castSucc → k.succ ≤ last → ∀ c, (records k).delta c ≤ δ₀) →
      (∀ k : Fin H.eventCount, j.succ ≤ k.castSucc → k.succ ≤ last →
        ∀ y : (H.stage k.castSucc).Carrier, ∀ t ∈ Ioo (H.time k.castSucc) (H.time k.succ),
          q₀ < (H.event k).incoming.flow.scalar t y →
          |derivWithin (fun v => (H.event k).incoming.flow.scalar v y) (Iic t) t| ≤
            C * (H.event k).incoming.flow.scalar t y ^ 2) →
      (∀ y : (H.stage last).Carrier, ∀ t ∈ Ioo (H.time last) s, q₀ < G.flow.scalar t y →
        |derivWithin (fun v => G.flow.scalar v y) (Iic t) t| ≤ C * G.flow.scalar t y ^ 2) →
      ((records j).static b).neck.scale * (s - H.time j.succ) ≤ η →
      ∀ (z : ThreeBall) (x : G.terminalRegularOpen)
        (A : BackwardPointTrace H j.succ last hle x.val),
      A.point j.succ le_rfl hle = ((records j).static b).inclusion (((records j).static b).witness.cap z) →
      ∀ (Q Cscale d ρ : ℝ) (hQ : 0 < Q), 0 < Cscale →
      ((records j).static b).neck.scale ≤ Cscale * Q → 0 ≤ d → 0 ≤ ρ →
      ∀ y : G.terminalRegularOpen,
      riemannianEDistOf L.metric x y ≤ ENNReal.ofReal (d / Real.sqrt Q) →
      2 * StandardCap.transitionEnd + (d + ρ) * Real.sqrt Cscale < r / 2 →
      ∀ p ∈ riemannianClosedBallOf L.metric y (ρ / Real.sqrt Q), ∀ k ≤ N,
        curvDerivNormSq k (scaleMetric Q hQ L.metric) p ≤ Cscale ^ (k+2) * B ∧
        curvDerivNorm k (scaleMetric Q hQ L.metric) p ≤ Real.sqrt (Cscale ^ (k+2) * B) := by
  obtain ⟨C₀, hC₀, _, η, ε₀, δ₀, B, hB, hη, hε₀, hεhalf, hδ₀, hprepared⟩ :=
    exists_uniform_prepared_incoming_cap_closedBall_curvature_derivative_bound.{u, 0, 0, u} N D r eps C heps hepssmall hr hfit
  refine ⟨C₀, η, ε₀, δ₀, B, hC₀, hB, hη, hε₀, hεhalf, hδ₀, ?_⟩
  intro H j last hle s G L hinit parameters records b hcanonical hmargin hm hε q₀ a₀ hq₀
    hq₀cap hacap hfixed hlower hδ hderiv hfinal htime z x A hbirth Q Cscale d ρ hQ hCscale
    hscale hd hρ y hnear hreserve
  let S := (records j).static b
  obtain ⟨x₀, δ, k, datum, w, hdatum, hmetric, hcap⟩ := hcanonical
  obtain ⟨u, hu, hucap⟩ := hcap z
  have hD : 0 < D := by
    have := StandardCap.transitionEnd_pos
    have := inv_pos.mpr heps
    linarith
  let inc : standardCapWindow D → standardCapWindow parameters.modelRadius :=
    TopologicalSpace.Opens.inclusion (by
      intro v hv
      change ‖v‖ < parameters.modelRadius + 1
      change ‖v‖ < D + 1 at hv
      linarith)
  let uSmall : standardCapWindow D := ⟨u.val, by
    change ‖u.val‖ < D + 1
    have := inv_pos.mpr heps
    linarith⟩
  have hinc : inc uSmall = u := Subtype.ext rfl
  have hmetric' : ∀ v (a b : TangentSpace ThreeModel v), w.windowMetric.inner v a b =
      S.neck.scale * (H.initialMetric j.succ).inner (S.window v)
        (mfderiv ThreeModel ThreeModel S.window v a) (mfderiv ThreeModel ThreeModel S.window v b) := by
    intro v a b
    rw [← H.event_output j]
    exact hmetric v a b
  have hbirth' : A.point j.succ le_rfl hle = (S.window ∘ inc) uSmall := by
    rw [Function.comp_apply, hinc, hucap]
    exact hbirth
  obtain ⟨Ξ, hΞ, hΞbirth, hΞpoint, hΞmetric, hΞjets, hball⟩ :=
    hprepared w hmargin hm hε H j.succ last hle s G L hinit S.window S.window_smooth
      S.neck.scale q₀ a₀ S.neck.scale_pos hq₀ hq₀cap hacap hmetric' parameters records
      hfixed hlower hδ hderiv hfinal htime uSmall x A hbirth'
  apply hball Q Cscale d ρ hQ hCscale hscale hd hρ y hnear
  change 2 * ‖u.val‖ + (d + ρ) * Real.sqrt Cscale < r / 2
  linarith

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

end

noncomputable section
open Set Function Bundle Manifold DifferentialGeometry
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open scoped Manifold ContDiff NNReal ENNReal
namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory
universe u

theorem exists_uniform_terminal_closedBall_curvature_derivative_bound
    (N : ℕ) (D rcap eps : ℝ) (C : ℝ≥0)
    (heps : 0 < eps) (hepssmall : eps ≤ 1 / 1000)
    (hrcap : StandardCap.transitionEnd + eps⁻¹ + 1 < rcap)
    (hfit : 64 * (rcap + eps⁻¹) < D) :
    ∃ C₀ η ε₀ δ₀ Bcap : ℝ, 0 < C₀ ∧ 1 ≤ Bcap ∧ 0 < η ∧ 0 < ε₀ ∧ ε₀ ≤ 1 / 2 ∧ 0 < δ₀ ∧
      ∀ (H : ObservedHistory.{u}) (first last : Fin (H.eventCount + 1)), first ≤ last →
      ∀ (s : ℝ) (G : (H.stage last).IncomingSlab (H.time last) s) (L : G.TerminalLimitMetric),
      G.flow.base.metric (H.time last) = H.initialMetric last →
      ∀ (x : G.terminalRegularOpen) (a r q Q θ : ℝ),
      0 ≤ a → 0 < r → 0 < q → q ≤ Q → ∀ hQ : 1 ≤ Q, 0 < θ → θ ≤ 1 / 4 →
      6 * C * θ ≤ 1 → 4 * θ ≤ η →
      2 * StandardCap.transitionEnd + (2 * a + r) * 2 < rcap / 2 →
      IsCompact (riemannianClosedBallOf L.metric x ((a + r) / Real.sqrt Q)) →
      ∀ (Phi : ℝ → ℝ), Perelman.AdmissiblePinchingFunction Phi →
      (∀ k : Fin H.eventCount, first ≤ k.castSucc → k.succ ≤ last →
        ∀ y : (H.stage k.castSucc).Carrier, ∀ t ∈ Ioo (H.time k.castSucc) (H.time k.succ),
          q < (H.event k).incoming.flow.scalar t y →
          |derivWithin (fun v => (H.event k).incoming.flow.scalar v y) (Iic t) t| ≤
            C * (H.event k).incoming.flow.scalar t y ^ 2) →
      (∀ y : (H.stage last).Carrier, ∀ t ∈ Ioo (H.time last) s, q < G.flow.scalar t y →
        |derivWithin (fun v => G.flow.scalar v y) (Iic t) t| ≤ C * G.flow.scalar t y ^ 2) →
      (∀ k : Fin H.eventCount, first ≤ k.castSucc → k.succ ≤ last →
        Perelman.PhiAlmostNonnegative (H.event k).incoming.flow
          (Ico (H.time k.castSucc) (H.time k.succ)) Phi) →
      Perelman.PhiAlmostNonnegative G.flow (Ico (H.time last) s) Phi →
      (∀ y ∈ riemannianClosedBallOf L.metric x ((a + r) / Real.sqrt Q),
        metricScalarAt L.metric y ≤ (3 / 2 : ℝ) * Q) →
      ∀ (parameters : CutoffParameters) (records : ∀ k : Fin H.eventCount, GeometricCutoffRecord H k parameters),
      D + 1 ≤ parameters.modelRadius → max ⌈eps⁻¹⌉₊ N + 2 ≤ parameters.modelOrder →
      parameters.modelAccuracy ≤ ε₀ →
      (∀ k : Fin H.eventCount, first ≤ k.castSucc → k.succ ≤ last →
        ∀ b : (H.event k).RetainedBoundaryIndex, ((records k).static b).hasCanonicalWindow) →
      (∀ k : Fin H.eventCount, first ≤ k.castSucc → k.succ ≤ last → ∀ b, (records k).delta b ≤ δ₀) →
      (∀ k : Fin H.eventCount, first ≤ k.castSucc → k.succ ≤ last →
        ∀ (b : (H.event k).RetainedBoundaryIndex) (z : ThreeBall),
          ((records k).static b).neck.scale / 2 ≤
            metricScalarAt ((records k).static b).witness.metric (((records k).static b).witness.cap z)) →
      ∀ a₀ : ℝ,
      (∀ y, InFixedHamiltonIveyRegion (H.initialMetric 0) a₀ y) →
      (∀ y, -3 / a₀ ≤ metricScalarAt (H.initialMetric 0) y) →
      (∀ k : Fin H.eventCount, first ≤ k.castSucc → k.succ ≤ last →
        ∀ b : (H.event k).RetainedBoundaryIndex,
          q ≤ C₀ * ((records k).static b).neck.scale ∧ 1 ≤ a₀ * ((records k).static b).neck.scale) →
      H.time first ≤ s - θ / Q →
      (∀ k : Fin H.eventCount, first ≤ k.castSucc → k.succ ≤ last → s - θ / Q < H.time k.succ) →
      let B := 4 * Real.sqrt 3 * (1 + Phi 4 + Phi 0)
      ∀ y ∈ riemannianClosedBallOf L.metric x (a / Real.sqrt Q), ∀ m ≤ N,
        curvDerivNorm m (scaleMetric Q (zero_lt_one.trans_le hQ) L.metric) y ≤
          max (shiLocalUniformBound 3 m (B * (θ / 4))
            (((r / 2) / (4 * Real.exp (9 * B * θ))) * Real.sqrt B /
              (4 * Real.exp (9 * B * (θ / 4)))) * B / Real.sqrt (θ / 4) ^ m)
            (Real.sqrt ((4 : ℝ) ^ (m+2) * Bcap)) := by
  obtain ⟨C₀, η, ε₀, δ₀, Bcap, hC₀, hBcap, hη, hε₀, hεhalf, hδ₀, hcapjets⟩ :=
    exists_uniform_canonical_cap_closedBall_curvature_derivative_bound N D rcap eps C
      heps hepssmall hrcap hfit
  refine ⟨C₀, η, ε₀, δ₀, Bcap, hC₀, hBcap, hη, hε₀, hεhalf, hδ₀, ?_⟩
  intro H first last hle s G L hinit x a r q Q θ ha hr hq hqQ hQ hθ hθsmall
    hbudget hηθ hreserve hcompact Phi hPhi hderiv hfinal hpinch hpinchFinal hscalar
    parameters records hmargin hm haccuracy hcanonical hδ hcap a₀ hfixed hlower hscalePremises
    hroom hcrossTime
  dsimp only
  rcases H.curvature_derivative_bound_on_closedBall_or_recent_static_cap first last hle G L
    hinit x ha hr hq hqQ hQ hθ hcompact hPhi hderiv (fun y _ => hfinal y.val)
    hpinch hpinchFinal hscalar records hθsmall hcrossTime hcap hroom hbudget with
    hjets | ⟨z, hz, j, hf, hl, A, b, u, _, _, hbirth, _, hcapscale, _, hage, _⟩
  · intro y hy m _
    exact (hjets y hy m).trans (le_max_left _ _)
  · have hQpos : 0 < Q := zero_lt_one.trans_le hQ
    have hnear : riemannianEDistOf L.metric z x ≤ ENNReal.ofReal ((a + r) / Real.sqrt Q) := by
      rw [riemannianEDistOf_comm]
      exact hz
    have hwhole := hcapjets H j last hl s G L hinit parameters records b (hcanonical j hf hl b)
      hmargin hm haccuracy q a₀ hq (hscalePremises j hf hl b).1 (hscalePremises j hf hl b).2
      hfixed hlower (fun k hk hkl => hδ k ((hf.trans j.castSucc_lt_succ.le).trans hk) hkl)
      (fun k hk hkl => hderiv k ((hf.trans j.castSucc_lt_succ.le).trans hk) hkl)
      hfinal (hage.le.trans hηθ) u z A hbirth Q 4 (a + r) a hQpos (by norm_num)
      hcapscale.le (by linarith) ha x hnear (by norm_num; nlinarith [hreserve])
    intro y hy m hmN
    exact (hwhole y hy m hmN).2.trans (le_max_right _ _)

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

end

noncomputable section
open Set Function Bundle Manifold DifferentialGeometry
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open scoped Manifold ContDiff NNReal ENNReal
namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory
universe u

theorem exists_uniform_terminal_closedBall_curvature_derivative_bound_of_initialIdentification
    (P : OrientedThreeStage.{u}) (g : P.Metric)
    (N : ℕ) (D Dbig rcap eps c ρ q : ℝ) (C : ℝ≥0)
    (hmargin : D + 1 ≤ Dbig) (hc : 0 < c) (hρ : 0 < ρ) (hq : 0 < q)
    (heps : 0 < eps) (hepssmall : eps ≤ 1 / 1000)
    (hrcap : StandardCap.transitionEnd + eps⁻¹ + 1 < rcap)
    (hfit : 64 * (rcap + eps⁻¹) < D) :
    ∃ (Phi : ℝ → ℝ) (η ε₀ δ₀ Bcap : ℝ), Perelman.AdmissiblePinchingFunction Phi ∧
      1 ≤ Bcap ∧ 0 < η ∧ 0 < ε₀ ∧ ε₀ ≤ 1 / 2 ∧ 0 < δ₀ ∧
      ∀ (H : ObservedHistory.{u}), InitialIdentification P g H →
      ∀ (first last : Fin (H.eventCount + 1)), first ≤ last →
      ∀ (s : ℝ) (G : (H.stage last).IncomingSlab (H.time last) s) (L : G.TerminalLimitMetric),
      G.flow.base.metric (H.time last) = H.initialMetric last →
      ∀ (x : G.terminalRegularOpen) (a r Q θ : ℝ),
      0 ≤ a → 0 < r → q ≤ Q → ∀ hQ : 1 ≤ Q, 0 < θ → θ ≤ 1 / 4 →
      6 * C * θ ≤ 1 → 4 * θ ≤ η →
      2 * StandardCap.transitionEnd + (2 * a + r) * 2 < rcap / 2 →
      IsCompact (riemannianClosedBallOf L.metric x ((a + r) / Real.sqrt Q)) →
      (∀ k : Fin H.eventCount, first ≤ k.castSucc → k.succ ≤ last →
        ∀ y : (H.stage k.castSucc).Carrier, ∀ t ∈ Ioo (H.time k.castSucc) (H.time k.succ),
          q < (H.event k).incoming.flow.scalar t y →
          |derivWithin (fun v => (H.event k).incoming.flow.scalar v y) (Iic t) t| ≤
            C * (H.event k).incoming.flow.scalar t y ^ 2) →
      (∀ y : (H.stage last).Carrier, ∀ t ∈ Ioo (H.time last) s, q < G.flow.scalar t y →
        |derivWithin (fun v => G.flow.scalar v y) (Iic t) t| ≤ C * G.flow.scalar t y ^ 2) →
      (∀ y ∈ riemannianClosedBallOf L.metric x ((a + r) / Real.sqrt Q),
        metricScalarAt L.metric y ≤ (3 / 2 : ℝ) * Q) →
      ∀ (parameters : CutoffParameters) (records : ∀ k : Fin H.eventCount, GeometricCutoffRecord H k parameters),
      parameters.modelRadius = Dbig → parameters.recenterConstant ≤ c → max ⌈eps⁻¹⌉₊ N + 2 ≤ parameters.modelOrder →
      parameters.modelAccuracy ≤ ε₀ →
      (∀ k : Fin H.eventCount, first ≤ k.castSucc → k.succ ≤ last →
        ∀ b : (H.event k).RetainedBoundaryIndex, ((records k).static b).hasCanonicalWindow) →
      (∀ k : Fin H.eventCount, first ≤ k.castSucc → k.succ ≤ last → parameters.delta (H.time k.succ) ≤ δ₀) →
      (∀ k : Fin H.eventCount, first ≤ k.castSucc → k.succ ≤ last → parameters.neckRadius (H.time k.succ) ≤ ρ) →
      H.time first ≤ s - θ / Q →
      (∀ k : Fin H.eventCount, first ≤ k.castSucc → k.succ ≤ last → s - θ / Q < H.time k.succ) →
      let B := 4 * Real.sqrt 3 * (1 + Phi 4 + Phi 0)
      ∀ y ∈ riemannianClosedBallOf L.metric x (a / Real.sqrt Q), ∀ m ≤ N,
        curvDerivNorm m (scaleMetric Q (zero_lt_one.trans_le hQ) L.metric) y ≤
          max (shiLocalUniformBound 3 m (B * (θ / 4))
            (((r / 2) / (4 * Real.exp (9 * B * θ))) * Real.sqrt B /
              (4 * Real.exp (9 * B * (θ / 4)))) * B / Real.sqrt (θ / 4) ^ m)
            (Real.sqrt ((4 : ℝ) ^ (m+2) * Bcap)) := by
  obtain ⟨C₀, η, εjet, δjet, Bcap, hC₀, hBcap, hη, hεjet, hεjethalf, hδjet, hbound⟩ :=
    exists_uniform_terminal_closedBall_curvature_derivative_bound N D rcap eps C
      heps hepssmall hrcap hfit
  have hDbig : StandardCap.transitionEnd < Dbig := by
    have := StandardCap.transitionEnd_pos
    have := inv_pos.mpr heps
    linarith
  obtain ⟨εscalar, hεscalar, hcaplower⟩ := exists_presented_cap_scalar_lower_bound_of_canonical_window Dbig hDbig
  obtain ⟨a₀, δscale, _, hδscale, hscales⟩ :=
    exists_uniform_identified_initial_pinching_and_static_cap_scale P g
      (q₀ := q) (C₀ := C₀) hc hρ hC₀
  obtain ⟨Phi, hPhi, hpinch⟩ := Perelman.exists_admissiblePinchingFunction_for_identified_incomingSlabs P g
  refine ⟨Phi, η, min εjet εscalar, min δjet δscale, Bcap, hPhi, hBcap, hη,
    lt_min hεjet hεscalar, (min_le_left _ _).trans hεjethalf, lt_min hδjet hδscale, ?_⟩
  intro H hH first last hle s G L hinit x a r Q θ ha hr hqQ hQ hθ hθsmall hbudget
    hηθ hreserve hcompact hderiv hfinal hscalar parameters records hmodel hpc hm haccuracy
    hcanonical hδ hrad hroom hcrossTime
  obtain ⟨hfixed, hlower, hscale⟩ := hscales H hH parameters hpc records
  have hcap : ∀ k : Fin H.eventCount, first ≤ k.castSucc → k.succ ≤ last →
      ∀ (b : (H.event k).RetainedBoundaryIndex) (z : ThreeBall),
        ((records k).static b).neck.scale / 2 ≤
          metricScalarAt ((records k).static b).witness.metric (((records k).static b).witness.cap z) := by
    intro k hf hl b z
    have hb := hcaplower (H.event k) (fixed := parameters.fixed)
      (m := parameters.modelOrder) (ε := parameters.modelAccuracy)
    rw [← hmodel] at hb
    exact hb (haccuracy.trans (min_le_right _ _)) (by omega) ((records k).static b)
      (hcanonical k hf hl b) z
  exact hbound H first last hle s G L hinit x a r q Q θ ha hr hq hqQ hQ hθ hθsmall
    hbudget hηθ hreserve hcompact Phi hPhi hderiv hfinal
    (fun k _ _ => hpinch H hH parameters records k.castSucc (H.time k.succ)
      (H.event k).incoming (H.event_initial k))
    (hpinch H hH parameters records last s G hinit) hscalar parameters records
    (by rw [hmodel]; exact hmargin) hm (haccuracy.trans (min_le_left _ _)) hcanonical
    (fun k hf hl b => ((records k).delta_le b).trans ((hδ k hf hl).trans (min_le_left _ _)))
    hcap a₀ hfixed hlower
    (fun k hf hl => hscale k ((hδ k hf hl).trans (min_le_right _ _)) (hrad k hf hl))
    hroom hcrossTime

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

end
