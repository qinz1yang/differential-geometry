import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CanonicalCapWindows
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.PreparedCapWindowGeometry
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.WindowVolumeComparison

noncomputable section
open Set Function Bundle Manifold DifferentialGeometry
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open scoped Manifold ContDiff NNReal ENNReal
namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory
universe u
private local instance : Fact (Module.finrank ℝ ThreeSpace = 3) := ⟨by simp⟩
private local instance {P : OrientedThreeStage.{u}} {a s : ℝ}
    (G : P.IncomingSlab a s) : SigmaCompactSpace G.terminalRegularOpen :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen ThreeModel G.terminalRegularOpen.isOpen)

theorem exists_uniform_canonical_cap_nearby_ball_volume_lower
    (D r eps R₁ : ℝ) (C : ℝ≥0)
    (heps : 0 < eps) (hepssmall : eps ≤ 1 / 1000)
    (hr : StandardCap.transitionEnd + eps⁻¹ + 1 < r)
    (hfit : 64 * (r + eps⁻¹) < D)
    (hR₁ : 0 < R₁) (hRmargin : R₁ + 1 < D) :
    ∃ C₀ η ε₀ δ₀ κ : ℝ, 0 < C₀ ∧ 0 < κ ∧ 0 < η ∧ 0 < ε₀ ∧ ε₀ ≤ 1 / 2 ∧ 0 < δ₀ ∧
      ∀ (H : ObservedHistory.{u}) (j : Fin H.eventCount) (last : Fin (H.eventCount + 1))
        (hle : j.succ ≤ last) (s : ℝ) (G : (H.stage last).IncomingSlab (H.time last) s)
        (L : G.TerminalLimitMetric), G.flow.base.metric (H.time last) = H.initialMetric last →
      ∀ (parameters : CutoffParameters) (records : ∀ k : Fin H.eventCount, GeometricCutoffRecord H k parameters)
        (b : (H.event j).RetainedBoundaryIndex),
      ((records j).static b).hasCanonicalWindow → D + 1 ≤ parameters.modelRadius →
      ⌈eps⁻¹⌉₊ + 2 ≤ parameters.modelOrder → parameters.modelAccuracy ≤ ε₀ →
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
      ∀ (Q Cscale d : ℝ), 0 < Q →
      ((records j).static b).neck.scale ≤ Cscale * Q → 0 ≤ d →
      ∀ y : G.terminalRegularOpen,
      riemannianEDistOf L.metric x y ≤ ENNReal.ofReal (d / Real.sqrt Q) →
      2 * StandardCap.transitionEnd + d * Real.sqrt Cscale < R₁ / 2 →
      ∀ a : ℝ, 0 < a → a * Real.sqrt Cscale ≤ 1 →
        ENNReal.ofReal κ * ENNReal.ofReal (a / Real.sqrt Q) ^ 3 ≤
          Integral.Measure.riemannianVolumeMeasure ThreeModel G.terminalRegularOpen L.metric
            (riemannianBallOf L.metric y (a / Real.sqrt Q)) := by
  obtain ⟨C₀, hC₀, _, η, ε₀, δ₀, B, hB, hη, hε₀, hεhalf, hδ₀, hprepared⟩ :=
    exists_uniform_prepared_incoming_cap_curvature_derivative_bound.{u, 0, 0, u}
      0 D r eps C heps hepssmall hr hfit
  obtain ⟨κ,hκ,hvolume⟩ := StandardCap.exists_uniform_nearby_scaled_window_ball_volume_lower R₁ hR₁
  refine ⟨C₀, η, ε₀, δ₀, κ, hC₀, hκ, hη, hε₀, hεhalf, hδ₀, ?_⟩
  intro H j last hle s G L hinit parameters records b hcanonical hmargin hm hε q₀ a₀ hq₀
    hq₀cap hacap hfixed hlower hδ hderiv hfinal htime z x A hbirth Q Cscale d hQ
    hscale hd y hnear hreserve a ha hsmall
  let S := (records j).static b
  have hCscale : 0 < Cscale := by
    have hpos : 0 < Cscale * Q := S.neck.scale_pos.trans_le hscale
    exact (mul_pos_iff_of_pos_right hQ).mp hpos
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
  obtain ⟨Ξ, hΞ, hΞbirth, hΞpoint, hΞmetric, hΞjets⟩ :=
    hprepared w hmargin (by simpa only [Nat.max_zero] using hm) hε H j.succ last hle s G L
      hinit S.window S.window_smooth S.neck.scale q₀ a₀ S.neck.scale_pos hq₀ hq₀cap hacap
      hmetric' parameters records hfixed hlower hδ hderiv hfinal htime uSmall x A hbirth'
  let Φ := H.backwardSurvivorIncomingMap j.succ last hle G ∘ Ξ
  have hlocal : IsLocalDiffeomorph ThreeModel ThreeModel ∞ Φ :=
    isLocalDiffeomorph_comp (H.backwardSurvivorIncomingMap_isLocalDiffeomorph j.succ last hle G)
      (fun p => Perelman.KappaSolutions.immersionAt_isLocalDiffeomorphAt_of_finrank_eq rfl
        (hΞ.isImmersion.isImmersionAt p))
  have hinj : Function.Injective Φ :=
    (H.backwardSurvivorIncomingMap_injective j.succ last hle G).comp hΞ.isEmbedding.injective
  have hemb : IsSmoothEmbedding ThreeModel ThreeModel ∞ Φ :=
    Perelman.KappaSolutions.localDiffeomorph_isSmoothEmbedding_of_injective hlocal hinj
  apply hvolume L.metric Φ hemb S.neck.scale Q Cscale S.neck.scale_pos hQ hCscale
    hscale hΞmetric hRmargin uSmall y d hd
  · simpa only [Φ, Function.comp_apply, hΞpoint] using hnear
  · change 2 * ‖u.val‖ + d * Real.sqrt Cscale < R₁ / 2
    linarith
  · exact ha
  · exact hsmall

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory
