import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CanonicalCapWindows
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.PreparedCapWindowGeometry

set_option autoImplicit false
noncomputable section
open Set Function Bundle Manifold DifferentialGeometry
open DifferentialGeometry.Geometry.Neck DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Metric DifferentialGeometry.CheegerGromovCompactness
open scoped Manifold ContDiff NNReal ENNReal
namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory
universe u
private local instance : Fact (Module.finrank ℝ ThreeSpace = 3) := ⟨by simp⟩

theorem exists_uniform_canonical_cap_window_flow_with_uniform_curvature_derivative_bounds
    (N : ℕ) (D r eps : ℝ)
    (heps : 0 < eps) (hepssmall : eps ≤ 1 / 1000)
    (hr : StandardCap.transitionEnd + eps⁻¹ + 1 < r)
    (hfit : 64 * (r + eps⁻¹) < D) :
    ∃ C₀ B : ℝ, 0 < C₀ ∧ 1 ≤ B ∧ ∀ C : ℝ≥0,
      ∃ η ε₀ δ₀ : ℝ, 0 < η ∧ 0 < ε₀ ∧ ε₀ ≤ 1 / 2 ∧ 0 < δ₀ ∧
      ∀ (H : ObservedHistory.{u}) (j : Fin H.eventCount) (last : Fin (H.eventCount + 1))
        (hle : j.succ ≤ last) (s : ℝ) (G : (H.stage last).IncomingSlab (H.time last) s)
        (L : G.TerminalLimitMetric), G.flow.base.metric (H.time last) = H.initialMetric last →
      ∀ (parameters : CutoffParameters) (records : ∀ k : Fin H.eventCount, GeometricCutoffRecord H k parameters)
        (b : (H.event j).RetainedBoundaryIndex),
      ((records j).static b).hasCanonicalWindow → ∀ (hmargin : D + 1 ≤ parameters.modelRadius),
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
      let cap := (records j).static b
      let q := cap.neck.scale
      ∃ (x₀ : (H.event j).incoming.terminalRegularOpen) (δ : ℝ) (k : ℕ)
        (datum : normalizedDatum (H.event j).terminal.metric x₀ δ k)
        (w : StandardCap.CanonicalStaticInsertionWitness datum parameters.fixed.collarLength
          parameters.fixed.collar_pos parameters.modelRadius parameters.modelOrder parameters.modelAccuracy),
        metricScalarAt (H.event j).terminal.metric x₀ = q ∧
        (∀ y (v z : TangentSpace ThreeModel y), w.windowMetric.inner y v z =
          q * (H.initialMetric j.succ).inner (cap.window y)
            (mfderiv ThreeModel ThreeModel cap.window y v)
            (mfderiv ThreeModel ThreeModel cap.window y z)) ∧
        let inc : standardCapWindow D → standardCapWindow parameters.modelRadius :=
          TopologicalSpace.Opens.inclusion (by
            intro y hy
            change ‖y‖ < parameters.modelRadius + 1
            change ‖y‖ < D + 1 at hy
            linarith)
        ∃ u : standardCapWindow D, ‖u.val‖ ≤ StandardCap.transitionEnd ∧
          cap.window (inc u) = cap.inclusion (cap.witness.cap z) ∧
          ∃ Ξ : standardCapWindow D → H.backwardSurvivorIncomingDomain j.succ last hle G,
            IsSmoothEmbedding ThreeModel ThreeModel ∞ Ξ ∧
            (∀ y, H.backwardSurvivorMap j.succ last hle j.succ le_rfl hle (Ξ y).val = cap.window (inc y)) ∧
            H.backwardSurvivorIncomingMap j.succ last hle G (Ξ u) = x ∧
            ∃ (hΞ : IsLocalDiffeomorph ThreeModel ThreeModel ∞ Ξ)
              (gflow : ℝ → SmoothRiemannianMetric ThreeModel
                (H.backwardSurvivorIncomingDomain j.succ last hle G))
              (S : SolutionOn (I := ThreeModel) (M := standardCapWindow D)
                (RealTimeInterval.closed 0 (q * (s - H.time j.succ))
                  (by
                    have ht := (H.time_strictMono.monotone hle).trans_lt G.lt
                    exact (mul_pos cap.neck.scale_pos (sub_pos.mpr ht)).le))),
              (∀ (l : Fin H.eventCount) (hf : j.succ ≤ l.castSucc) (hl : l.succ ≤ last),
                ∀ t ∈ Icc (H.time l.castSucc) (H.time l.succ),
                  gflow t = (H.backwardSurvivorSlabMetric j.succ last hle l hf hl t).restrictOpen
                    (H.backwardSurvivorIncomingDomain j.succ last hle G)) ∧
              (∀ t ∈ Icc (H.time last) s,
                gflow t = H.backwardSurvivorIncomingMetric j.succ last hle G L t) ∧
              IsSolutionOn S ∧ S.base.metric 0 = w.windowMetric.restrictOpenOfSubset
                (show standardCapWindow D ≤ standardCapWindow parameters.modelRadius from
                  fun _ hy => hy.trans_le (add_le_add (show D ≤ parameters.modelRadius by linarith) (le_refl 1))) ∧
              (∀ t, S.base.metric t = localPullMetric
                (scaleMetric q cap.neck.scale_pos (gflow (H.time j.succ + t / q))) Ξ hΞ) ∧
              (∀ (y : standardCapWindow D) (l k : Fin (Module.finrank ℝ ThreeSpace)),
                ContMDiffOn (𝓘(ℝ, ℝ).prod ThreeModel) 𝓘(ℝ) ∞
                  (fun z : ℝ × standardCapWindow D => DifferentialGeometry.Tensor.Coordinates.chartGramMatrix
                    (S.base.metric z.1) y z.2 l k)
                  (Icc 0 (q * (s - H.time j.succ)) ×ˢ
                    (trivializationAt ThreeSpace (TangentSpace ThreeModel) y).baseSet)) ∧
              (∀ l ≤ N, ∀ t ∈ Icc 0 (q * (s - H.time j.succ)),
                ∀ y : standardCapWindow D, ‖y.val‖ ≤ r → curvDerivNormSq l (S.base.metric t) y ≤ B) ∧
              ∀ y (v z : TangentSpace ThreeModel y),
                (S.base.metric (q * (s - H.time j.succ))).inner y v z =
                  (scaleMetric q cap.neck.scale_pos L.metric).inner
                    (H.backwardSurvivorIncomingMap j.succ last hle G (Ξ y))
                    (mfderiv ThreeModel ThreeModel (H.backwardSurvivorIncomingMap j.succ last hle G ∘ Ξ) y v)
                    (mfderiv ThreeModel ThreeModel (H.backwardSurvivorIncomingMap j.succ last hle G ∘ Ξ) y z) := by
  obtain ⟨C₀, hC₀, _, B, hB, hforall⟩ :=
    exists_uniform_prepared_incoming_cap_window_flow_with_uniform_curvature_derivative_bounds.{u, 0, 0, u}
      N D r eps heps hepssmall hr hfit
  refine ⟨C₀, B, hC₀, hB, ?_⟩
  intro C
  obtain ⟨η, ε₀, δ₀, hη, hε₀, hεhalf, hδ₀, hprepared⟩ := hforall C
  refine ⟨η, ε₀, δ₀, hη, hε₀, hεhalf, hδ₀, ?_⟩
  intro H j last hle s G L hinit parameters records b hcanonical hmargin hm hε q₀ a₀ hq₀
    hq₀cap hacap hfixed hlower hδ hderiv hfinal htime z x A hbirth
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
  obtain ⟨Ξ, hΞs, hΞbirth, hΞpoint, hΞ, gflow, flow, hslabs, hlast,
    hflow, hzero, hlocal, hgram, hjets, hterminal, _, _⟩ :=
    hprepared w hmargin hm hε H j.succ last hle s G L hinit S.window S.window_smooth
      S.neck.scale q₀ a₀ S.neck.scale_pos hq₀ hq₀cap hacap hmetric' parameters records
      hfixed hlower hδ hderiv hfinal htime uSmall x A hbirth'
  refine ⟨x₀, δ, k, datum, w, hdatum, hmetric', uSmall, hu, ?_,
    Ξ, hΞs, hΞbirth, hΞpoint, hΞ, gflow, flow, hslabs, hlast,
    hflow, hzero, hlocal, hgram, hjets, hterminal⟩
  exact (congrArg S.window hinc).trans hucap

theorem exists_uniform_canonical_cap_window_flow_with_curvature_derivative_bounds
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
      ((records j).static b).hasCanonicalWindow → ∀ (hmargin : D + 1 ≤ parameters.modelRadius),
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
      let cap := (records j).static b
      let q := cap.neck.scale
      ∃ (x₀ : (H.event j).incoming.terminalRegularOpen) (δ : ℝ) (k : ℕ)
        (datum : normalizedDatum (H.event j).terminal.metric x₀ δ k)
        (w : StandardCap.CanonicalStaticInsertionWitness datum parameters.fixed.collarLength
          parameters.fixed.collar_pos parameters.modelRadius parameters.modelOrder parameters.modelAccuracy),
        metricScalarAt (H.event j).terminal.metric x₀ = q ∧
        (∀ y (v z : TangentSpace ThreeModel y), w.windowMetric.inner y v z =
          q * (H.initialMetric j.succ).inner (cap.window y)
            (mfderiv ThreeModel ThreeModel cap.window y v)
            (mfderiv ThreeModel ThreeModel cap.window y z)) ∧
        let inc : standardCapWindow D → standardCapWindow parameters.modelRadius :=
          TopologicalSpace.Opens.inclusion (by
            intro y hy
            change ‖y‖ < parameters.modelRadius + 1
            change ‖y‖ < D + 1 at hy
            linarith)
        ∃ u : standardCapWindow D, ‖u.val‖ ≤ StandardCap.transitionEnd ∧
          cap.window (inc u) = cap.inclusion (cap.witness.cap z) ∧
          ∃ Ξ : standardCapWindow D → H.backwardSurvivorIncomingDomain j.succ last hle G,
            IsSmoothEmbedding ThreeModel ThreeModel ∞ Ξ ∧
            (∀ y, H.backwardSurvivorMap j.succ last hle j.succ le_rfl hle (Ξ y).val = cap.window (inc y)) ∧
            H.backwardSurvivorIncomingMap j.succ last hle G (Ξ u) = x ∧
            ∃ (hΞ : IsLocalDiffeomorph ThreeModel ThreeModel ∞ Ξ)
              (gflow : ℝ → SmoothRiemannianMetric ThreeModel
                (H.backwardSurvivorIncomingDomain j.succ last hle G))
              (S : SolutionOn (I := ThreeModel) (M := standardCapWindow D)
                (RealTimeInterval.closed 0 (q * (s - H.time j.succ))
                  (by
                    have ht := (H.time_strictMono.monotone hle).trans_lt G.lt
                    exact (mul_pos cap.neck.scale_pos (sub_pos.mpr ht)).le))),
              (∀ (l : Fin H.eventCount) (hf : j.succ ≤ l.castSucc) (hl : l.succ ≤ last),
                ∀ t ∈ Icc (H.time l.castSucc) (H.time l.succ),
                  gflow t = (H.backwardSurvivorSlabMetric j.succ last hle l hf hl t).restrictOpen
                    (H.backwardSurvivorIncomingDomain j.succ last hle G)) ∧
              (∀ t ∈ Icc (H.time last) s,
                gflow t = H.backwardSurvivorIncomingMetric j.succ last hle G L t) ∧
              IsSolutionOn S ∧ S.base.metric 0 = w.windowMetric.restrictOpenOfSubset
                (show standardCapWindow D ≤ standardCapWindow parameters.modelRadius from
                  fun _ hy => hy.trans_le (add_le_add (show D ≤ parameters.modelRadius by linarith) (le_refl 1))) ∧
              (∀ t, S.base.metric t = localPullMetric
                (scaleMetric q cap.neck.scale_pos (gflow (H.time j.succ + t / q))) Ξ hΞ) ∧
              (∀ (y : standardCapWindow D) (l k : Fin (Module.finrank ℝ ThreeSpace)),
                ContMDiffOn (𝓘(ℝ, ℝ).prod ThreeModel) 𝓘(ℝ) ∞
                  (fun z : ℝ × standardCapWindow D => DifferentialGeometry.Tensor.Coordinates.chartGramMatrix
                    (S.base.metric z.1) y z.2 l k)
                  (Icc 0 (q * (s - H.time j.succ)) ×ˢ
                    (trivializationAt ThreeSpace (TangentSpace ThreeModel) y).baseSet)) ∧
              (∀ l ≤ N, ∀ t ∈ Icc 0 (q * (s - H.time j.succ)),
                ∀ y : standardCapWindow D, ‖y.val‖ ≤ r → curvDerivNormSq l (S.base.metric t) y ≤ B) ∧
              ∀ y (v z : TangentSpace ThreeModel y),
                (S.base.metric (q * (s - H.time j.succ))).inner y v z =
                  (scaleMetric q cap.neck.scale_pos L.metric).inner
                    (H.backwardSurvivorIncomingMap j.succ last hle G (Ξ y))
                    (mfderiv ThreeModel ThreeModel (H.backwardSurvivorIncomingMap j.succ last hle G ∘ Ξ) y v)
                    (mfderiv ThreeModel ThreeModel (H.backwardSurvivorIncomingMap j.succ last hle G ∘ Ξ) y z) := by
  obtain ⟨C₀, B, hC₀, hB, hforall⟩ :=
    exists_uniform_canonical_cap_window_flow_with_uniform_curvature_derivative_bounds
      N D r eps heps hepssmall hr hfit
  obtain ⟨η, ε₀, δ₀, hη, hε₀, hεhalf, hδ₀, hresult⟩ := hforall C
  exact ⟨C₀, η, ε₀, δ₀, B, hC₀, hB, hη, hε₀, hεhalf, hδ₀, hresult⟩

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory
