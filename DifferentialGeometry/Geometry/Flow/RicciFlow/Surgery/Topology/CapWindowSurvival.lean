import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistorySurvivorIncoming
import DifferentialGeometry.Topology.Manifold.SmoothEmbeddingOpenTarget
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistorySurvivorFirstLossIncoming
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.EventCutScaleProtection
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistorySurvivorInitialCurvature
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.LocalInitialSpatialCap
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.WindowFlowDistance
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.EqualDimensionImmersion
import DifferentialGeometry.Geometry.Metric.DistancePullback
import DifferentialGeometry.Geometry.Metric.PullbackScaling
import DifferentialGeometry.Geometry.Curvature.Bounds.ScalarNorm

noncomputable section
open Set Function Bundle Manifold DifferentialGeometry
open DifferentialGeometry.Geometry.Neck DifferentialGeometry.Geometry.Metric
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open scoped Manifold ContDiff ENNReal NNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

universe u

private local instance (D : ℝ) : SigmaCompactSpace (standardCapWindow D) :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (Geometry.isSigmaCompact_of_isOpen ThreeModel (standardCapWindow D).isOpen)

private theorem terminal_chart_metric
    (H : ObservedHistory.{u}) (first : Fin (H.eventCount + 1))
    (i : Fin H.eventCount) (hf : first ≤ i.castSucc) {D q : ℝ} (hq : 0 < q)
    (Ξ : standardCapWindow D → H.backwardSurvivorTerminalFace first i hf)
    (hΞ : IsLocalDiffeomorph ThreeModel ThreeModel ∞ Ξ)
    (G : ℝ → SmoothRiemannianMetric ThreeModel (H.backwardSurvivorTerminalFace first i hf))
    (hlast : ∀ t ∈ Icc (H.time i.castSucc) (H.time i.succ),
      G t = H.backwardSurvivorTerminalFaceMetric first i hf t)
    {Δ : RealTimeInterval} (L : SolutionOn (I := ThreeModel) (M := standardCapWindow D) Δ)
    (hmetric : ∀ t, L.base.metric t =
      localPullMetric (scaleMetric q hq (G (H.time first + t / q))) Ξ hΞ) :
    ∀ x (v w : TangentSpace ThreeModel x),
      (L.base.metric (q * (H.time i.succ - H.time first))).inner x v w =
        (scaleMetric q hq (H.event i).terminal.metric).inner
          ((H.backwardSurvivorTerminalFaceMap first i hf ∘ Ξ) x)
          (mfderiv ThreeModel ThreeModel (H.backwardSurvivorTerminalFaceMap first i hf ∘ Ξ) x v)
          (mfderiv ThreeModel ThreeModel (H.backwardSurvivorTerminalFaceMap first i hf ∘ Ξ) x w) := by
  intro x v w
  rw [hmetric, mul_div_cancel_left₀ _ hq.ne', add_sub_cancel,
    hlast _ ⟨(H.time_strictMono i.castSucc_lt_succ).le, le_rfl⟩,
    H.backwardSurvivorTerminalFaceMetric_terminal]
  rw [localPullMetric_inner, scaleMetric_inner, localPullMetric_inner, scaleMetric_inner]
  rw [mfderiv_comp x
    ((H.backwardSurvivorTerminalFaceMap_isLocalDiffeomorph first i hf).contMDiff.mdifferentiableAt (by simp))
    (hΞ.contMDiff.mdifferentiableAt (by simp))]
  rfl

theorem exists_uniform_cap_window_survival_time
    (D r eps C₀ : ℝ) (C : ℝ≥0) (hC₀ : 0 < C₀)
    (heps : 0 < eps) (hepssmall : eps ≤ 1 / 1000)
    (hr : StandardCap.transitionEnd + eps⁻¹ + 1 < r)
    (hfit : 64 * (r + eps⁻¹) < D) :
    ∃ η ε₀ δ₀ : ℝ, 0 < η ∧ 0 < ε₀ ∧ ε₀ ≤ 1 / 2 ∧ 0 < δ₀ ∧
      ∀ {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
        [FiniteDimensional ℝ E] [Fact (Module.finrank ℝ E = 3)]
        [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
        [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
        {g : SmoothRiemannianMetric I M} {x₀ : M} {δ : ℝ} {k : ℕ}
        {d : normalizedDatum g x₀ δ k} {A : ℝ} {hA : 0 < A} {m : ℕ} {ζ : ℝ}
        (w : StandardCap.CanonicalStaticInsertionWitness d A hA D m ζ),
      ⌈eps⁻¹⌉₊ + 2 ≤ m → ζ ≤ ε₀ →
      (∀ x : standardCapWindow D, ∀ v : TangentSpace ThreeModel x,
        w.windowMetric.inner x v v ≤ (3/2 : ℝ) * StandardCap.metric.inner x.val v v) →
      ∀ (H : ObservedHistory.{u}) (first last : Fin (H.eventCount + 1)) (hle : first ≤ last)
        (J : standardCapWindow D → (H.stage first).Carrier),
      IsSmoothEmbedding ThreeModel ThreeModel ∞ J →
      ∀ (q q₀ a₀ : ℝ), 0 < q → 0 < q₀ → q₀ ≤ C₀ * q → 1 ≤ a₀ * q →
      (∀ x (v z : TangentSpace ThreeModel x), w.windowMetric.inner x v z =
        q * (H.initialMetric first).inner (J x) (mfderiv ThreeModel ThreeModel J x v)
          (mfderiv ThreeModel ThreeModel J x z)) →
      (∀ x, metricScalarAt (H.initialMetric first) (J x) ≤ C₀ * q) →
      ∀ (parameters : CutoffParameters) (records : ∀ j : Fin H.eventCount, GeometricCutoffRecord H j parameters),
      (∀ x, InFixedHamiltonIveyRegion (H.initialMetric 0) a₀ x) →
      (∀ x, -3 / a₀ ≤ metricScalarAt (H.initialMetric 0) x) →
      (∀ j : Fin H.eventCount, first ≤ j.castSucc → j.succ ≤ last → ∀ b, (records j).delta b ≤ δ₀) →
      (∀ j : Fin H.eventCount, first ≤ j.castSucc → j.succ ≤ last →
        ∀ x : (H.stage j.castSucc).Carrier, ∀ t ∈ Ioo (H.time j.castSucc) (H.time j.succ),
          q₀ < (H.event j).incoming.flow.scalar t x →
          |derivWithin (fun v => (H.event j).incoming.flow.scalar v x) (Iic t) t| ≤
            C * (H.event j).incoming.flow.scalar t x ^ 2) →
      q * (H.time last - H.time first) ≤ η →
      ∀ (z : standardCapWindow D) (endpoint : (H.stage last).Carrier)
        (A : BackwardPointTrace H first last hle endpoint), A.point first le_rfl hle = J z →
      ∃ Ψ : standardCapWindow D → H.backwardSurvivorDomain first last hle,
        IsSmoothEmbedding ThreeModel ThreeModel ∞ Ψ ∧
        ∀ x, H.backwardSurvivorMap first last hle first le_rfl hle (Ψ x) = J x := by
  let K := (2 * Real.sqrt 3 * (C₀ + max (2 * C₀) (Real.exp 4))) ^ 2
  let Cs := 9 * Real.sqrt K + 1
  have hCs : 0 < Cs := by dsimp [Cs]; positivity
  have hr0 : 0 < r := by linarith [StandardCap.transitionEnd_pos, inv_pos.mpr heps]
  have hD : 0 < D := by linarith [inv_pos.mpr heps]
  obtain ⟨ηcap, ε₀, Ccap, hηcap, hηcap1, hε₀, hεhalf, _, hcap⟩ :=
    StandardCap.exists_uniform_spatial_cap_frontier_of_local_curvature D r 1 K eps heps
      (hepssmall.trans_lt (by norm_num)) hr hfit (by norm_num)
  obtain ⟨ηdist, hηdist, hdist⟩ :=
    StandardCap.exists_uniform_window_flow_edist_bound_of_initial_metric_upper K
  obtain ⟨δ₀, hδ₀, hprotect⟩ := exists_cutoff_cap_protection_tolerance_of_scaled_subset
    hCs (by positivity : 0 ≤ 4 * (D + 1)) (by norm_num : (0 : ℝ) < 1/2)
  let η := min ηcap (min ηdist (8 * C * C₀ + 1)⁻¹)
  have hη : 0 < η := lt_min hηcap (lt_min hηdist (by positivity))
  refine ⟨η, ε₀, δ₀, hη, hε₀, hεhalf, hδ₀, ?_⟩
  intro E H0 M _ _ _ _ _ I _ _ _ _ _ g x₀ δ k d A hA m ζ w hm hζ hupper
    H first last hle J hJ q q₀ a₀ hq hq₀ hq₀Q haq hzero hscalar parameters records
    hfixed hlower hδ hderiv htime z endpoint Atrace hanchor
  have htime8 : 8 * C * (H.time last - H.time first) * (C₀ * q) ≤ 1 := by
    have hh := htime.trans ((min_le_right _ _).trans (min_le_right _ _))
    have hden : 0 < 8 * (C : ℝ) * C₀ + 1 := by positivity
    have hm := (le_div_iff₀ hden).mp (show q * (H.time last - H.time first) ≤
      1 / (8 * (C : ℝ) * C₀ + 1) from by simpa only [one_div] using hh)
    have ht0 := H.time_strictMono.monotone hle
    nlinarith [mul_nonneg hq.le (sub_nonneg.mpr ht0)]
  have hsurvive : range J ⊆ range (H.backwardSurvivorMap first last hle first le_rfl hle) := by
    by_contra hnot
    obtain ⟨i, hf, hl, _, Ξ, hΞs, hbirth, xbad, hbad⟩ :=
      H.exists_first_event_incoming_chart_of_initial_scalar_bound first last hle J hJ
        hq₀ hq₀Q hscalar hderiv htime8 hnot
    have hΞ : IsLocalDiffeomorph ThreeModel ThreeModel ∞ Ξ := fun x =>
      Perelman.KappaSolutions.immersionAt_isLocalDiffeomorphAt_of_finrank_eq rfl
        (hΞs.isImmersion.isImmersionAt x)
    let θ := q * (H.time i.succ - H.time first)
    have hθ : 0 < θ := mul_pos hq (sub_pos.mpr (H.time_strictMono (hf.trans_lt i.castSucc_lt_succ)))
    have hθη : θ ≤ η :=
      (mul_le_mul_of_nonneg_left (sub_le_sub_right (H.time_strictMono.monotone hl) _) hq.le).trans htime
    have hθcap : θ ≤ ηcap := hθη.trans (min_le_left _ _)
    have hθdist : θ ≤ ηdist := hθη.trans ((min_le_right _ _).trans (min_le_left _ _))
    have hθ1 : θ ≤ 1 := hθcap.trans hηcap1
    have htime2 : 2 * C * C₀ * θ ≤ 1 := by
      have ht0 := H.time_strictMono.monotone hl
      dsimp only [θ]
      nlinarith [mul_nonneg hq.le (sub_nonneg.mpr (H.time_strictMono.monotone hle)),
        mul_nonneg C.coe_nonneg hC₀.le]
    obtain ⟨G, hslabs, hlast, L, hL, hLzero, hmetric, hgram, hRm⟩ :=
      exists_normalized_backwardSurvivor_chart_solution_curvature_bound Ξ hΞ J hbirth
        hq₀ hq hq₀Q w.windowMetric hzero haq
        (fun x j hj hji => hderiv j hj (by
          exact (Fin.succ_le_succ_iff.mpr (show j ≤ i from hji)).trans hl) _)
        hscalar records hfixed hlower htime2
    have hcurv : ∀ t ∈ Icc 0 θ, ∀ x : standardCapWindow D,
        nablaKRm04NormSqIntrinsic L 0 t x ≤ K := by
      simpa only [nablaKRm04NormSqIntrinsic, nablaKRm04Field_zero, Nat.add_zero] using hRm
    let Φ := H.backwardSurvivorTerminalFaceMap first i hf ∘ Ξ
    have hΦ : IsLocalDiffeomorph ThreeModel ThreeModel ∞ Φ :=
      isLocalDiffeomorph_comp (H.backwardSurvivorTerminalFaceMap_isLocalDiffeomorph first i hf) hΞ
    have hΦinj : Injective Φ :=
      (H.backwardSurvivorTerminalFaceMap_injective first i hf).comp hΞs.isEmbedding.injective
    let h := scaleMetric q hq (H.event i).terminal.metric
    have hmet := terminal_chart_metric H first i hf hq Ξ hΞ G hlast L hmetric
    have hcurvlocal : ∀ t ∈ Icc 0 θ, ∀ x : standardCapWindow D, ‖x.val‖ ≤ 64*(r+eps⁻¹) →
        nablaKRm04NormSqIntrinsic L 0 t x ≤ K := fun t ht x _ => hcurv t ht x
    have htcap : θ ∈ Icc 0 (min ηcap θ) := ⟨hθ.le, le_min hθcap le_rfl⟩
    obtain ⟨_, hinner⟩ := hcap w hm hζ _ θ hθ hθ1 (fun _ ht => ht) (fun _ ht => ht)
      L hL hLzero hgram hcurvlocal θ htcap h Φ hΦ hΦinj hmet
    obtain ⟨p, ztip, _, _, boundary, Kinner, hKinner, _, hinterior, _, _, hfront, _, _, hsc, _⟩ :=
      hinner 0 ⟨neg_lt_zero.mpr (inv_pos.mpr heps), inv_pos.mpr heps⟩
    have hLK : Kinner.carrier ⊆ range Φ := by rw [hKinner]; exact image_subset_range _ _
    have hconnected : IsPreconnected (range Φ) := by
      let : PreconnectedSpace (standardCapWindow D) := by
        apply isPreconnected_iff_preconnectedSpace.mp
        change IsPreconnected {x : ThreeSpace | ‖x‖ < D+1}
        simpa only [Metric.ball, dist_zero_right] using
          (convex_ball (0 : ThreeSpace) (D+1)).isPreconnected
      exact isPreconnected_range hΦ.contMDiff.continuous
    have hscalarouter : ∀ y ∈ range Φ, metricScalarAt h y ≤ Cs := by
      rintro _ ⟨x, rfl⟩
      have hscal := scalar_abs_le_rm (L.base.metric θ) x
      have hdim : Module.finrank ℝ (TangentSpace ThreeModel x) = 3 := by
        change Module.finrank ℝ ThreeSpace = 3
        simp [ThreeSpace]
      rw [hdim] at hscal
      have hnorm : Real.sqrt (normSq0S (L.base.metric θ) x 4 (metricRm04At (L.base.metric θ) x)) ≤
          Real.sqrt K := Real.sqrt_le_sqrt (hRm θ ⟨hθ.le, le_rfl⟩ x)
      have heq := (curvature_of_injective_local_isometry (L.base.metric θ) h Φ hΦ hΦinj hmet x).1
      rw [← heq]
      dsimp only [Cs]
      norm_num only [Nat.cast_ofNat, show (3 : ℝ)^2=9 by norm_num] at hscal
      nlinarith [le_abs_self (metricScalarAt (L.base.metric θ) x)]
    have hdiam : ∀ x ∈ range Φ, ∀ y ∈ range Φ,
        riemannianEDistOf h x y ≤ ENNReal.ofReal (4 * (D+1)) := by
      rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩
      have hmapdist := edistOf_le_of_quad_of_localDiffeomorph (L.base.metric θ) h Φ hΦ
        (by norm_num : (0 : ℝ) < 1) (fun a v => by rw [← hmet]; simp only [one_mul]; rfl) x y
      have hlocaldist := hdist D _ θ hθdist (fun _ ht => ht) (fun _ ht => ht) L hL
        (fun x v => by rw [hLzero]; exact hupper x v) hcurv θ ⟨hθ.le, le_rfl⟩ x y
      have hx : ‖x.val‖ < D+1 := x.property
      have hy : ‖y.val‖ < D+1 := y.property
      simp only [Real.sqrt_one, ENNReal.ofReal_one, one_mul] at hmapdist
      exact hmapdist.trans (hlocaldist.trans (ENNReal.ofReal_le_ofReal (by linarith)))
    have hcross := H.exists_regularCrossing_of_backwardSurvivor_initial_eq first last hle J i hf hl
      Ξ hbirth z endpoint Atrace hanchor
    have hKold := hprotect H i parameters (records i) (records i).old_eq_retained (hδ i hf hl)
      q hq eps (Φ p) boundary hepssmall 0
      ⟨neg_lt_zero.mpr (inv_pos.mpr heps), inv_pos.mpr heps⟩ Kinner.carrier (range Φ)
      hLK Kinner.compact hconnected ⟨Φ ztip, hinterior⟩ hfront hscalarouter
      (by linarith [(abs_lt.mp hsc).1] : (1/2:ℝ) ≤ metricScalarAt h (Φ p)) hdiam
      (Φ z) (mem_range_self z) _ hcross
    obtain ⟨old, _, _, hcrossbad⟩ := (H.event i).exists_oldTerminal_eq_of_mem_interior_old
      (Φ xbad) (hKold (Φ xbad) (mem_range_self xbad))
    exact hbad ((H.event i).oldOutput old) hcrossbad
  have hF := H.backwardSurvivorMap_isSmoothEmbedding first last hle first le_rfl hle
  exact ⟨hF.lift J hsurvive, hF.isSmoothEmbedding_lift hJ (by simp) hsurvive,
    hF.comp_lift hsurvive⟩

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory


noncomputable section
open Set Function Bundle Manifold DifferentialGeometry
open DifferentialGeometry.Geometry.Neck DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff ENNReal NNReal
namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory
universe u

theorem exists_uniform_incoming_cap_window_survival_time
    (D r eps C₀ : ℝ) (C : ℝ≥0) (hC₀ : 0 < C₀)
    (heps : 0 < eps) (hepssmall : eps ≤ 1 / 1000)
    (hr : StandardCap.transitionEnd + eps⁻¹ + 1 < r)
    (hfit : 64 * (r + eps⁻¹) < D) :
    ∃ η ε₀ δ₀ : ℝ, 0 < η ∧ 0 < ε₀ ∧ ε₀ ≤ 1 / 2 ∧ 0 < δ₀ ∧
      ∀ {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
        [FiniteDimensional ℝ E] [Fact (Module.finrank ℝ E = 3)]
        [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
        [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
        {g : SmoothRiemannianMetric I M} {x₀ : M} {δ : ℝ} {k : ℕ}
        {d : normalizedDatum g x₀ δ k} {A : ℝ} {hA : 0 < A} {m : ℕ} {ζ : ℝ}
        (w : StandardCap.CanonicalStaticInsertionWitness d A hA D m ζ),
      ⌈eps⁻¹⌉₊ + 2 ≤ m → ζ ≤ ε₀ →
      (∀ x : standardCapWindow D, ∀ v : TangentSpace ThreeModel x,
        w.windowMetric.inner x v v ≤ (3/2 : ℝ) * StandardCap.metric.inner x.val v v) →
      ∀ (H : ObservedHistory.{u}) (first last : Fin (H.eventCount + 1)) (hle : first ≤ last)
        (s : ℝ) (G : (H.stage last).IncomingSlab (H.time last) s),
      G.flow.base.metric (H.time last) = H.initialMetric last →
      ∀ (J : standardCapWindow D → (H.stage first).Carrier),
      IsSmoothEmbedding ThreeModel ThreeModel ∞ J →
      ∀ (q q₀ a₀ : ℝ), 0 < q → 0 < q₀ → q₀ ≤ C₀ * q → 1 ≤ a₀ * q →
      (∀ x (v z : TangentSpace ThreeModel x), w.windowMetric.inner x v z =
        q * (H.initialMetric first).inner (J x) (mfderiv ThreeModel ThreeModel J x v)
          (mfderiv ThreeModel ThreeModel J x z)) →
      (∀ x, metricScalarAt (H.initialMetric first) (J x) ≤ C₀ * q) →
      ∀ (parameters : CutoffParameters) (records : ∀ j : Fin H.eventCount, GeometricCutoffRecord H j parameters),
      (∀ x, InFixedHamiltonIveyRegion (H.initialMetric 0) a₀ x) →
      (∀ x, -3 / a₀ ≤ metricScalarAt (H.initialMetric 0) x) →
      (∀ j : Fin H.eventCount, first ≤ j.castSucc → j.succ ≤ last → ∀ b, (records j).delta b ≤ δ₀) →
      (∀ j : Fin H.eventCount, first ≤ j.castSucc → j.succ ≤ last →
        ∀ x : (H.stage j.castSucc).Carrier, ∀ t ∈ Ioo (H.time j.castSucc) (H.time j.succ),
          q₀ < (H.event j).incoming.flow.scalar t x →
          |derivWithin (fun v => (H.event j).incoming.flow.scalar v x) (Iic t) t| ≤
            C * (H.event j).incoming.flow.scalar t x ^ 2) →
      (∀ x : (H.stage last).Carrier, ∀ t ∈ Ioo (H.time last) s,
        q₀ < G.flow.scalar t x →
        |derivWithin (fun v => G.flow.scalar v x) (Iic t) t| ≤ C * G.flow.scalar t x ^ 2) →
      q * (s - H.time first) ≤ η →
      ∀ (z : standardCapWindow D) (endpoint : (H.stage last).Carrier)
        (A : BackwardPointTrace H first last hle endpoint), A.point first le_rfl hle = J z →
      ∃ Ψ : standardCapWindow D → H.backwardSurvivorIncomingDomain first last hle G,
        IsSmoothEmbedding ThreeModel ThreeModel ∞ Ψ ∧
        ∀ x, H.backwardSurvivorMap first last hle first le_rfl hle (Ψ x).val = J x := by
  obtain ⟨η₀, ε₀, δ₀, hη₀, hε₀, hεhalf, hδ₀, hsurvive⟩ :=
    exists_uniform_cap_window_survival_time D r eps C₀ C hC₀ heps hepssmall hr hfit
  let η := min η₀ (8 * C * C₀ + 1)⁻¹
  have hη : 0 < η := lt_min hη₀ (by positivity)
  refine ⟨η, ε₀, δ₀, hη, hε₀, hεhalf, hδ₀, ?_⟩
  intro E H0 M _ _ _ _ _ I _ _ _ _ _ g x₀ δ k d A hA m ζ w hm hζ hupper
    H first last hle s G hinit J hJ q q₀ a₀ hq hq₀ hq₀Q haq hzero hscalar parameters records
    hfixed hlower hδ hderiv hfinal htime z endpoint Atrace hanchor
  have hprior : q * (H.time last - H.time first) ≤ η₀ :=
    (mul_le_mul_of_nonneg_left (sub_le_sub_right G.lt.le _) hq.le).trans
      (htime.trans (min_le_left _ _))
  obtain ⟨Ψ, hΨ, hbirth⟩ := hsurvive w hm hζ hupper H first last hle J hJ
    q q₀ a₀ hq hq₀ hq₀Q haq hzero hscalar parameters records hfixed hlower hδ hderiv
    hprior z endpoint Atrace hanchor
  have htime8 : 8 * C * (s - H.time first) * (C₀ * q) ≤ 1 := by
    have hh := htime.trans (min_le_right _ _)
    have hden : 0 < 8 * (C : ℝ) * C₀ + 1 := by positivity
    have hm := (le_div_iff₀ hden).mp (show q * (s - H.time first) ≤
      1 / (8 * (C : ℝ) * C₀ + 1) from by simpa only [one_div] using hh)
    have ht0 := (H.time_strictMono.monotone hle).trans G.lt.le
    nlinarith [mul_nonneg hq.le (sub_nonneg.mpr ht0)]
  have hregular (x : standardCapWindow D) : (Ψ x).val ∈ G.terminalRegularRegion := by
    let B : BackwardPointTrace H first last hle (Ψ x).val := Classical.choice (Ψ x).property
    apply B.mem_incoming_terminalRegularRegion_of_initial_scalar_bound G hinit (Ψ x).val hq₀ hq₀Q
      (fun j hf hl => hderiv j hf hl _) isOpen_univ (mem_univ _)
      (fun y _ => hfinal y) ?_ htime8
    rw [← H.backwardSurvivorMap_eq_point first last hle first le_rfl hle (Ψ x) B, hbirth]
    exact hscalar x
  let Ξ : standardCapWindow D → H.backwardSurvivorIncomingDomain first last hle G :=
    fun x => ⟨Ψ x, hregular x⟩
  exact ⟨Ξ, DifferentialGeometry.Topology.Manifold.isSmoothEmbedding_intoOpen ThreeModel ThreeModel
    (H.backwardSurvivorIncomingDomain first last hle G) Ξ hΨ, hbirth⟩

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory
