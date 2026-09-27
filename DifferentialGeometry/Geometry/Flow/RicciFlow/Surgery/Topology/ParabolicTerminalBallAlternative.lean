import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.ParabolicTerminalBallFlow
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TerminalBackwardFlow
import DifferentialGeometry.Geometry.Curvature.Bounds.ScalarNorm
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TerminalCapVolume

noncomputable section
open Set Bundle Manifold DifferentialGeometry
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Integral.Measure
open scoped Manifold ContDiff Topology NNReal ENNReal
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

theorem exists_uniform_parabolically_controlled_incoming_ball_or_recent_cap
    {Phi : ℝ → ℝ} (hPhi : Perelman.AdmissiblePinchingFunction Phi)
    {θ : ℝ} (hθ : 0 < θ) (hθsmall : θ ≤ 1 / 4) :
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
    (∀ y ∈ riemannianClosedBallOf L.metric x r, metricScalarAt L.metric y ≤ (3 / 2 : ℝ) * Q) →
    (∀ j : Fin H.eventCount, first ≤ j.castSucc → j.succ ≤ last →
      s - θ / Q < H.time j.succ) →
    ∀ (parameters : CutoffParameters) (records : ∀ j : Fin H.eventCount, GeometricCutoffRecord H j parameters),
    (∀ j : Fin H.eventCount, first ≤ j.castSucc → j.succ ≤ last →
      ∀ (b : (H.event j).RetainedBoundaryIndex) (z : ThreeBall),
        ((records j).static b).neck.scale / 2 ≤
          metricScalarAt ((records j).static b).witness.metric (((records j).static b).witness.cap z)) →
    H.time first ≤ s - θ / Q →
    6 * C * θ ≤ 1 →
    α / Real.sqrt Q < r →
    let K := riemannianClosedBallOf L.metric x r
    (∃ (p : H.backwardSurvivorIncomingFootprint first last hle G K)
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
        IsCompact (riemannianClosedBallOf (S.base.metric s) p (α / Real.sqrt Q))) ∨
      ∃ y ∈ K, ∃ (j : Fin H.eventCount), first ≤ j.castSucc ∧
        ∃ (hl : j.succ ≤ last) (A : BackwardPointTrace H j.succ last hl y.val)
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
  obtain ⟨α, hα, hα1, hαθ, hball⟩ :=
    exists_uniform_parabolically_controlled_incoming_terminal_ball_radius hPhi hθ
  refine ⟨α, hα, hα1, hαθ, ?_⟩
  intro H first last hle s G L x r q Q C hQ hinit hr hcompact hq hqQ
    hbound hfinal hpinch hpinchFinal hscalar hcrossTime parameters records hcap hc hbudget hradius
  let K := riemannianClosedBallOf L.metric x r
  rcases H.backward_traces_on_set_or_recent_presented_cap first last hle G L hinit K
    hq hqQ hθsmall hbudget hcrossTime hscalar (fun j hf hl => hbound j hf.le hl) hfinal
    (fun j _ _ => (records j).old_eq_retained) (fun j _ _ => (records j).static) hcap with
    htraces | hcapbirth
  · left
    apply hball H first last hle G L x hQ hinit hr hcompact hq hqQ
      hbound hfinal hpinch hpinchFinal _ htraces hc hbudget hradius
    intro y hy
    have := hscalar y hy
    have hQpos : 0 < Q := zero_lt_one.trans_le hQ
    linarith
  · obtain ⟨y, hy, j, hf, hl, A, b, z, hrest⟩ := hcapbirth
    exact Or.inr ⟨y, hy, j, hf, hl, A, b, z, hrest⟩

theorem exists_uniform_parabolically_controlled_ball_or_recent_cap_of_spatial_rm_bound
    {Phi : ℝ → ℝ} (hPhi : Perelman.AdmissiblePinchingFunction Phi)
    {θ : ℝ} (hθ : 0 < θ) (hθsmall : θ ≤ 1 / 4) :
    ∃ α : ℝ, 0 < α ∧ α ≤ 1 ∧ α ^ 2 ≤ θ ∧
    ∀ (H : ObservedHistory.{u}) (first last : Fin (H.eventCount + 1)) (hle : first ≤ last)
      {s : ℝ} (G : (H.stage last).IncomingSlab (H.time last) s) (L : G.TerminalLimitMetric)
      (x : G.terminalRegularOpen) {r q : ℝ} {C : ℝ≥0} (hr : 0 < r),
    r ≤ 1 → let Q := 16 / r ^ 2;
    G.flow.base.metric (H.time last) = H.initialMetric last →
    IsCompact (riemannianClosedBallOf L.metric x (r / 2)) →
    0 < q → q ≤ Q →
    (∀ j : Fin H.eventCount, first ≤ j.castSucc → j.succ ≤ last →
      ∀ y : (H.stage j.castSucc).Carrier, ∀ t ∈ Ioo (H.time j.castSucc) (H.time j.succ),
      q < (H.event j).incoming.flow.scalar t y →
      |derivWithin (fun v => (H.event j).incoming.flow.scalar v y) (Iic t) t| ≤
        C * (H.event j).incoming.flow.scalar t y ^ 2) →
    (∀ y ∈ riemannianClosedBallOf L.metric x (r / 2), ∀ t ∈ Ioo (H.time last) s, q < G.flow.scalar t y.val →
      |derivWithin (fun v => G.flow.scalar v y.val) (Iic t) t| ≤ C * G.flow.scalar t y.val ^ 2) →
    (∀ j : Fin H.eventCount, first ≤ j.castSucc → j.succ ≤ last →
      Perelman.PhiAlmostNonnegative (H.event j).incoming.flow
        (Ico (H.time j.castSucc) (H.time j.succ)) Phi) →
    (Perelman.PhiAlmostNonnegative G.flow (Ico (H.time last) s) Phi) →
    (∀ y ∈ riemannianBallOf L.metric x r,
      r ^ 4 * normSq0S L.metric y 4 (metricRm04At L.metric y) ≤ 1) →
    (∀ j : Fin H.eventCount, first ≤ j.castSucc → j.succ ≤ last →
      s - θ / Q < H.time j.succ) →
    ∀ (parameters : CutoffParameters) (records : ∀ j : Fin H.eventCount, GeometricCutoffRecord H j parameters),
    (∀ j : Fin H.eventCount, first ≤ j.castSucc → j.succ ≤ last →
      ∀ (b : (H.event j).RetainedBoundaryIndex) (z : ThreeBall),
        ((records j).static b).neck.scale / 2 ≤
          metricScalarAt ((records j).static b).witness.metric (((records j).static b).witness.cap z)) →
    H.time first ≤ s - θ / Q →
    6 * C * θ ≤ 1 →
    let K := riemannianClosedBallOf L.metric x (r / 2)
    (∃ (p : H.backwardSurvivorIncomingFootprint first last hle G K)
      (S : SolutionOn (I := ThreeModel)
        (M := H.backwardSurvivorIncomingFootprint first last hle G K)
        (RealTimeInterval.closed (s - θ / Q) s (sub_le_self s (div_nonneg hθ.le (by positivity : 0 ≤ Q))))),
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
      ∃ B : Perelman.FlowMetricBall S ⟨s, sub_le_self s (div_nonneg hθ.le (by positivity : 0 ≤ Q)), le_rfl⟩,
        B.center = p ∧ B.radius = α * r / 4 ∧ B.IsParabolicallyRmControlled ∧
        B.set = riemannianBallOf (S.base.metric s) p (α * r / 4) ∧
        H.backwardSurvivorIncomingFootprintMap first last hle G K '' B.set =
          riemannianBallOf L.metric x (α * r / 4) ∧
        B.volume = riemannianVolumeMeasure ThreeModel G.terminalRegularOpen L.metric
          (riemannianBallOf L.metric x (α * r / 4)) ∧
        IsCompact (riemannianClosedBallOf (S.base.metric s) p (α * r / 4))) ∨
      ∃ y ∈ K, ∃ (j : Fin H.eventCount), first ≤ j.castSucc ∧
        ∃ (hl : j.succ ≤ last) (A : BackwardPointTrace H j.succ last hl y.val)
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
  obtain ⟨α, hα, hα1, hαθ, htest⟩ :=
    exists_uniform_parabolically_controlled_incoming_ball_or_recent_cap hPhi hθ hθsmall
  refine ⟨α, hα, hα1, hαθ, ?_⟩
  intro H first last hle s G L x r q C hr hr1
  dsimp only
  intro hinit hcompact hq hqQ hbound hfinal hpinch hpinchFinal hRm hcrossTime parameters records hcap hc hbudget
  let Q := 16 / r ^ 2
  have hr2 : 0 < r ^ 2 := sq_pos_of_pos hr
  have hQ : 1 ≤ Q := by
    dsimp [Q]
    apply (le_div_iff₀ hr2).mpr
    nlinarith
  have hroot : Real.sqrt Q = 4 / r := by
    dsimp [Q]
    rw [Real.sqrt_div (by norm_num : (0 : ℝ) ≤ 16), Real.sqrt_sq hr.le]
    norm_num
  have hrad : α / Real.sqrt Q = α * r / 4 := by rw [hroot]; field_simp
  have hradius : α / Real.sqrt Q < r / 2 := by rw [hrad]; nlinarith
  have hscalar : ∀ y ∈ riemannianClosedBallOf L.metric x (r / 2),
      metricScalarAt L.metric y ≤ (3 / 2 : ℝ) * Q := by
    intro y hy
    have hyball : y ∈ riemannianBallOf L.metric x r :=
      hy.trans_lt ((ENNReal.ofReal_lt_ofReal_iff hr).mpr (by linarith))
    have hs := scalar_abs_le_div_sq_of_rm_bound L.metric y hr.ne' (hRm y hyball)
    have hsc : metricScalarAt L.metric y ≤ 9 / r ^ 2 := by
      apply (le_abs_self _).trans
      norm_num only [ThreeSpace, finrank_euclideanSpace, Fintype.card_fin, Nat.cast_ofNat, Nat.reducePow, OfNat.ofNat] at hs ⊢
      exact hs
    have h9 : 9 / r ^ 2 ≤ (3 / 2 : ℝ) * Q := by
      dsimp [Q]
      field_simp
      norm_num
    exact hsc.trans h9
  have h := htest H first last hle G L x hQ hinit (half_pos hr) hcompact hq hqQ
    hbound hfinal hpinch hpinchFinal hscalar hcrossTime parameters records hcap hc hbudget hradius
  simpa only [Q, hrad] using h

theorem exists_uniform_parabolic_ball_or_volume_lower_of_spatial_rm_bound
    (D rcap eps R₁ : ℝ) (C : ℝ≥0)
    (heps : 0 < eps) (hepssmall : eps ≤ 1 / 1000)
    (hrcap : StandardCap.transitionEnd + eps⁻¹ + 1 < rcap)
    (hfit : 64 * (rcap + eps⁻¹) < D)
    (hR₁ : 0 < R₁) (hRmargin : R₁ + 1 < D)
    (hreserve : 2 * StandardCap.transitionEnd + 4 < R₁ / 2) :
    ∃ C₀ η ε₀ δ₀ κ : ℝ, 0 < C₀ ∧ 0 < κ ∧ 0 < η ∧ 0 < ε₀ ∧ ε₀ ≤ 1 / 2 ∧ 0 < δ₀ ∧
    ∀ (Phi : ℝ → ℝ), Perelman.AdmissiblePinchingFunction Phi →
    ∀ (θ : ℝ) (hθ : 0 < θ), θ ≤ 1 / 4 → 4 * θ ≤ η →
    ∃ α : ℝ, 0 < α ∧ α ≤ 1 ∧ α ^ 2 ≤ θ ∧
    ∀ (H : ObservedHistory.{u}) (first last : Fin (H.eventCount + 1)) (hle : first ≤ last)
      {s : ℝ} (G : (H.stage last).IncomingSlab (H.time last) s) (L : G.TerminalLimitMetric)
      (x : G.terminalRegularOpen) {r q : ℝ} (hr : 0 < r),
    r ≤ 1 → let Q := 16 / r ^ 2;
    G.flow.base.metric (H.time last) = H.initialMetric last →
    IsCompact (riemannianClosedBallOf L.metric x (r / 2)) →
    0 < q → q ≤ Q →
    (∀ j : Fin H.eventCount, first ≤ j.castSucc → j.succ ≤ last →
      ∀ y : (H.stage j.castSucc).Carrier, ∀ t ∈ Ioo (H.time j.castSucc) (H.time j.succ),
      q < (H.event j).incoming.flow.scalar t y →
      |derivWithin (fun v => (H.event j).incoming.flow.scalar v y) (Iic t) t| ≤
        C * (H.event j).incoming.flow.scalar t y ^ 2) →
    (∀ y : (H.stage last).Carrier, ∀ t ∈ Ioo (H.time last) s, q < G.flow.scalar t y →
      |derivWithin (fun v => G.flow.scalar v y) (Iic t) t| ≤ C * G.flow.scalar t y ^ 2) →
    (∀ j : Fin H.eventCount, first ≤ j.castSucc → j.succ ≤ last →
      Perelman.PhiAlmostNonnegative (H.event j).incoming.flow
        (Ico (H.time j.castSucc) (H.time j.succ)) Phi) →
    (Perelman.PhiAlmostNonnegative G.flow (Ico (H.time last) s) Phi) →
    (∀ y ∈ riemannianBallOf L.metric x r,
      r ^ 4 * normSq0S L.metric y 4 (metricRm04At L.metric y) ≤ 1) →
    (∀ j : Fin H.eventCount, first ≤ j.castSucc → j.succ ≤ last →
      s - θ / Q < H.time j.succ) →
    ∀ (parameters : CutoffParameters) (records : ∀ j : Fin H.eventCount, GeometricCutoffRecord H j parameters),
    (∀ j : Fin H.eventCount, first ≤ j.castSucc → j.succ ≤ last →
      ∀ (b : (H.event j).RetainedBoundaryIndex) (z : ThreeBall),
        ((records j).static b).neck.scale / 2 ≤
          metricScalarAt ((records j).static b).witness.metric (((records j).static b).witness.cap z)) →
    D + 1 ≤ parameters.modelRadius → ⌈eps⁻¹⌉₊ + 2 ≤ parameters.modelOrder →
    parameters.modelAccuracy ≤ ε₀ →
    (∀ k : Fin H.eventCount, first ≤ k.castSucc → k.succ ≤ last →
      ∀ b : (H.event k).RetainedBoundaryIndex, ((records k).static b).hasCanonicalWindow) →
    (∀ k : Fin H.eventCount, first ≤ k.castSucc → k.succ ≤ last → ∀ b, (records k).delta b ≤ δ₀) →
    ∀ a₀ : ℝ,
    (∀ y, InFixedHamiltonIveyRegion (H.initialMetric 0) a₀ y) →
    (∀ y, -3 / a₀ ≤ metricScalarAt (H.initialMetric 0) y) →
    (∀ k : Fin H.eventCount, first ≤ k.castSucc → k.succ ≤ last →
      ∀ b : (H.event k).RetainedBoundaryIndex,
        q ≤ C₀ * ((records k).static b).neck.scale ∧ 1 ≤ a₀ * ((records k).static b).neck.scale) →
    H.time first ≤ s - θ / Q →
    6 * C * θ ≤ 1 →
    let K := riemannianClosedBallOf L.metric x (r / 2)
    (∃ (p : H.backwardSurvivorIncomingFootprint first last hle G K)
      (S : SolutionOn (I := ThreeModel)
        (M := H.backwardSurvivorIncomingFootprint first last hle G K)
        (RealTimeInterval.closed (s - θ / Q) s (sub_le_self s (div_nonneg hθ.le (by positivity : 0 ≤ Q))))),
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
      ∃ B : Perelman.FlowMetricBall S ⟨s, sub_le_self s (div_nonneg hθ.le (by positivity : 0 ≤ Q)), le_rfl⟩,
        B.center = p ∧ B.radius = α * r / 4 ∧ B.IsParabolicallyRmControlled ∧
        B.set = riemannianBallOf (S.base.metric s) p (α * r / 4) ∧
        H.backwardSurvivorIncomingFootprintMap first last hle G K '' B.set =
          riemannianBallOf L.metric x (α * r / 4) ∧
        B.volume = riemannianVolumeMeasure ThreeModel G.terminalRegularOpen L.metric
          (riemannianBallOf L.metric x (α * r / 4)) ∧
        IsCompact (riemannianClosedBallOf (S.base.metric s) p (α * r / 4))) ∨
      ENNReal.ofReal κ * ENNReal.ofReal (α * r / 4) ^ 3 ≤
        riemannianVolumeMeasure ThreeModel G.terminalRegularOpen L.metric
          (riemannianBallOf L.metric x (α * r / 4)) := by
  obtain ⟨C₀,η,ε₀,δ₀,κ,hC₀,hκ,hη,hε₀,hεhalf,hδ₀,hvolume⟩ :=
    exists_uniform_canonical_cap_nearby_ball_volume_lower D rcap eps R₁ C heps hepssmall
      hrcap hfit hR₁ hRmargin
  refine ⟨C₀,η,ε₀,δ₀,κ,hC₀,hκ,hη,hε₀,hεhalf,hδ₀,?_⟩
  intro Phi hPhi θ hθ hθsmall hηθ
  obtain ⟨α,hα,hα1,hαθ,hball⟩ :=
    exists_uniform_parabolically_controlled_ball_or_recent_cap_of_spatial_rm_bound hPhi hθ hθsmall
  refine ⟨α,hα,hα1,hαθ,?_⟩
  intro H first last hle s G L x r q hr hr1
  dsimp only
  intro hinit hcompact hq hqQ hderiv hfinal hpinch hpinchFinal hRm hcrossTime parameters records hcap
    hmargin hm haccuracy hcanonical hδ a₀ hfixed hlower hscalePremises hroom hbudget
  let Q := 16 / r ^ 2
  rcases hball H first last hle G L x hr hr1 hinit hcompact hq hqQ
    hderiv (fun y _ => hfinal y.val) hpinch hpinchFinal hRm hcrossTime parameters records hcap
    hroom hbudget with htested | hrecent
  · exact Or.inl htested
  · right
    obtain ⟨y,hy,j,hf,hl,A,b,z,_,_,hbirth,_,hscale,_,hage,_⟩ := hrecent
    have hQ : 0 < Q := div_pos (by norm_num) (sq_pos_of_pos hr)
    have hroot : Real.sqrt Q = 4 / r := by
      dsimp [Q]
      rw [Real.sqrt_div (by norm_num : (0 : ℝ) ≤ 16), Real.sqrt_sq hr.le]
      norm_num
    have hhalf : 2 / Real.sqrt Q = r / 2 := by rw [hroot]; field_simp; norm_num
    have hnear : riemannianEDistOf L.metric y x ≤ ENNReal.ofReal (2 / Real.sqrt Q) := by
      rw [riemannianEDistOf_comm,hhalf]
      exact hy
    have hsmall : α * Real.sqrt (4 : ℝ) ≤ 1 := by
      norm_num
      nlinarith
    have hv := hvolume H j last hl s G L hinit parameters records b
      (hcanonical j hf hl b) hmargin hm haccuracy q a₀ hq (hscalePremises j hf hl b).1
      (hscalePremises j hf hl b).2 hfixed hlower
      (fun k hk hkl => hδ k ((hf.trans j.castSucc_lt_succ.le).trans hk) hkl)
      (fun k hk hkl => hderiv k ((hf.trans j.castSucc_lt_succ.le).trans hk) hkl)
      hfinal (hage.le.trans hηθ) z y A hbirth Q 4 2 hQ hscale.le (by norm_num) x hnear
      (by linarith [hreserve]) α hα hsmall
    have hrad : α / Real.sqrt Q = α * r / 4 := by rw [hroot]; field_simp
    simpa only [hrad] using hv

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory
