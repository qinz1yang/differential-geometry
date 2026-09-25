import DifferentialGeometry.Geometry.Neck.ProductCapExclusion
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CapWindowSurvival
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistorySurvivorIncoming
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistorySurvivorInitialCurvature
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.LocalInitialSpatialCap

noncomputable section
open Set Function Bundle Manifold DifferentialGeometry
open DifferentialGeometry.Geometry.Neck DifferentialGeometry.Geometry.Metric
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open scoped Manifold ContDiff ENNReal NNReal
namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory
universe u
theorem exists_uniform_incoming_cap_geometry
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
        (s : ℝ) (G : (H.stage last).IncomingSlab (H.time last) s) (L : G.TerminalLimitMetric),
      G.flow.base.metric (H.time last) = H.initialMetric last →
      ∀ (J : standardCapWindow D → (H.stage first).Carrier),
      IsSmoothEmbedding ThreeModel ThreeModel ∞ J →
      ∀ (q q₀ a₀ : ℝ) (hq : 0 < q), 0 < q₀ → q₀ ≤ C₀ * q → 1 ≤ a₀ * q →
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
      ∀ (z : standardCapWindow D) (x : G.terminalRegularOpen)
        (A : BackwardPointTrace H first last hle x.val), ‖z.val‖ < r →
        A.point first le_rfl hle = J z →
      ∃ (Ξ : standardCapWindow D → H.backwardSurvivorIncomingDomain first last hle G),
        IsSmoothEmbedding ThreeModel ThreeModel ∞ Ξ ∧
        (∀ y, H.backwardSurvivorMap first last hle first le_rfl hle (Ξ y).val = J y) ∧
        ∃ (p tip : standardCapWindow D), p.val = r • (spherePoint : ThreeSpace) ∧ tip.val = 0 ∧
          ∃ (nk : SpatialNeck (scaleMetric q hq L.metric) eps
              (H.backwardSurvivorIncomingMap first last hle G (Ξ p)))
            (K : CompactDomain G.terminalRegularOpen),
            x ∈ interior K.carrier ∧ Nonempty (CapCore K.carrier) ∧
            K.carrier = (H.backwardSurvivorIncomingMap first last hle G ∘ Ξ) ''
              {y : standardCapWindow D | ‖y.val‖ ≤ r} ∧
            frontier K.carrier = range (fun y : Sphere 2 => nk.map (y, 0)) ∧
            |metricScalarAt (scaleMetric q hq L.metric)
              (H.backwardSurvivorIncomingMap first last hle G (Ξ p)) - 1| < 1/8 ∧
            K.carrier ⊆ riemannianBallOf (scaleMetric q hq L.metric)
              (H.backwardSurvivorIncomingMap first last hle G (Ξ tip)) (2*r) := by
  let K₀ := (2 * Real.sqrt 3 * (C₀ + max (2 * C₀) (Real.exp 4))) ^ 2
  obtain ⟨η₁, ε₁, δ₀, hη₁, hε₁, hε₁half, hδ₀, hsurvive⟩ :=
    exists_uniform_incoming_cap_window_survival_time D r eps C₀ C hC₀ heps hepssmall hr hfit
  obtain ⟨η₂, ε₂, Ccap, hη₂, hη₂one, hε₂, hε₂half, _, hcap⟩ :=
    StandardCap.exists_uniform_spatial_cap_frontier_of_local_curvature D r 1 K₀ eps heps
      (hepssmall.trans_lt (by norm_num)) hr hfit (by norm_num)
  let η := min η₁ (min η₂ (2 * C * C₀ + 1)⁻¹)
  refine ⟨η, min ε₁ ε₂, δ₀, lt_min hη₁ (lt_min hη₂ (by positivity)),
    lt_min hε₁ hε₂, (min_le_left _ _).trans hε₁half, hδ₀, ?_⟩
  intro E H0 M _ _ _ _ _ I _ _ _ _ _ g x₀ δ k d A hA m ζ w hm hζ hupper
    H first last hle s G L hinit J hJ q q₀ a₀ hq hq₀ hq₀Q haq hzero hscalar parameters records
    hfixed hlower hδ hderiv hfinal htime z x Atrace hz hanchor
  obtain ⟨Ξ, hΞs, hbirth⟩ := hsurvive w hm (hζ.trans (min_le_left _ _)) hupper
    H first last hle s G hinit J hJ q q₀ a₀ hq hq₀ hq₀Q haq hzero hscalar parameters records
    hfixed hlower hδ hderiv hfinal (htime.trans (min_le_left _ _)) z x.val Atrace hanchor
  have hΞ : IsLocalDiffeomorph ThreeModel ThreeModel ∞ Ξ := fun y =>
    Perelman.KappaSolutions.immersionAt_isLocalDiffeomorphAt_of_finrank_eq rfl
      (hΞs.isImmersion.isImmersionAt y)
  let θ := q * (s - H.time first)
  have hθ : 0 < θ := mul_pos hq (sub_pos.mpr ((H.time_strictMono.monotone hle).trans_lt G.lt))
  have hθ₂ : θ ≤ η₂ := htime.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hθone : θ ≤ 1 := hθ₂.trans hη₂one
  have htime2 : 2 * C * C₀ * θ ≤ 1 := by
    have hh := htime.trans ((min_le_right _ _).trans (min_le_right _ _))
    have hden : 0 < 2 * (C : ℝ) * C₀ + 1 := by positivity
    have hm := (le_div_iff₀ hden).mp (show θ ≤ 1 / (2 * (C : ℝ) * C₀ + 1) from
      by simpa only [one_div] using hh)
    nlinarith
  obtain ⟨gflow, hslabs, hlast, S, hS, hSzero, hmetric, hgram, hRm⟩ :=
    exists_normalized_backwardSurvivorIncoming_chart_solution_curvature_bound G L hinit Ξ hΞ J hbirth
      hq₀ hq hq₀Q w.windowMetric hzero haq
      (fun y j hf hl => hderiv j hf hl _) (fun y => hfinal _) hscalar records hfixed hlower htime2
  let Φ := H.backwardSurvivorIncomingMap first last hle G ∘ Ξ
  have hΦ : IsLocalDiffeomorph ThreeModel ThreeModel ∞ Φ :=
    isLocalDiffeomorph_comp (H.backwardSurvivorIncomingMap_isLocalDiffeomorph first last hle G) hΞ
  have hΦinj : Injective Φ :=
    (H.backwardSurvivorIncomingMap_injective first last hle G).comp hΞs.isEmbedding.injective
  let h := scaleMetric q hq L.metric
  have hmet : ∀ y (v w : TangentSpace ThreeModel y), (S.base.metric θ).inner y v w =
      h.inner (Φ y) (mfderiv ThreeModel ThreeModel Φ y v) (mfderiv ThreeModel ThreeModel Φ y w) := by
    intro y v w
    rw [hmetric]
    have hclock : H.time first + θ / q = s := by dsimp only [θ]; field_simp; ring
    rw [hclock, hlast s ⟨G.lt.le, le_rfl⟩, H.backwardSurvivorIncomingMetric_terminal]
    rw [localPullMetric_inner, scaleMetric_inner, localPullMetric_inner]
    dsimp only [h]
    rw [scaleMetric_inner]
    dsimp only [Φ]
    rw [mfderiv_comp y
      ((H.backwardSurvivorIncomingMap_isLocalDiffeomorph first last hle G).contMDiff.mdifferentiableAt (by simp))
      (hΞ.contMDiff.mdifferentiableAt (by simp))]
    rfl
  have hcurv : ∀ t ∈ Icc 0 θ, ∀ y : standardCapWindow D, ‖y.val‖ ≤ 64*(r+eps⁻¹) →
      nablaKRm04NormSqIntrinsic S 0 t y ≤ K₀ := by
    intro t ht y _
    simpa only [nablaKRm04NormSqIntrinsic, nablaKRm04Field_zero, Nat.add_zero] using hRm t ht y
  obtain ⟨_, hinner⟩ := hcap w hm (hζ.trans (min_le_right _ _)) _ θ hθ hθone
    (fun _ ht => ht) (fun _ ht => ht) S hS hSzero hgram hcurv θ
      ⟨hθ.le, le_min hθ₂ le_rfl⟩ h Φ hΦ hΦinj hmet
  obtain ⟨p, tip, hp, htip, nk, K, hK, hcore, _, hint, _, hfront, _, _, hsc, hball⟩ :=
    hinner 0 ⟨neg_lt_zero.mpr (inv_pos.mpr heps), inv_pos.mpr heps⟩
  have hpoint : Φ z = x :=
    H.backwardSurvivorIncomingMap_eq_of_initial_point_eq first last hle G J Ξ hbirth x Atrace z hanchor.symm
  refine ⟨Ξ, hΞs, hbirth, p, tip, hp, htip, nk, K, ?_, hcore, ?_, hfront, hsc, ?_⟩
  · rw [← hpoint]
    exact hint z (by simpa only [add_zero] using hz)
  · simpa only [add_zero] using hK
  · simpa only [add_zero, h, Φ, Function.comp_apply] using hball

theorem exists_uniform_incoming_cap_product_exclusion
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
        (s : ℝ) (G : (H.stage last).IncomingSlab (H.time last) s) (L : G.TerminalLimitMetric),
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
      ∀ (z : standardCapWindow D) (x : G.terminalRegularOpen)
        (A : BackwardPointTrace H first last hle x.val), ‖z.val‖ < r →
        A.point first le_rfl hle = J z →
      ∀ (Q A : ℝ) (hQ : 0 < Q), Q / q ≤ A →
      ∀ {F H' : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
        [TopologicalSpace H'] {Jp : ModelWithCorners ℝ F H'} [Jp.Boundaryless]
        {N : Type*} [TopologicalSpace N] [ChartedSpace H' N] [IsManifold Jp ∞ N]
        [T2Space N] [ConnectedSpace N] [SigmaCompactSpace N]
        (hprod : SmoothRiemannianMetric Jp N), Module.finrank ℝ F = 2 →
      ∀ (O : TopologicalSpace.Opens (N × ℝ)) (V : TopologicalSpace.Opens G.terminalRegularOpen)
        (Φ : O ≃ₘ⟮Jp.prod 𝓘(ℝ), I3⟯ V),
      riemannianBallOf (scaleMetric Q hQ L.metric) x (4 * Real.sqrt A * r) ⊆ V →
      ∀ δprod : ℝ, δprod ≤ 1/4 → 720 * δprod < ((7/8 : ℝ) / A) / 16 →
      (∀ y : V, ∀ n : ℕ, n ≤ 2 →
        metricDerivNorm n (Diffeomorph.pullbackMetricCross ((scaleMetric Q hQ L.metric).restrictOpen V) Φ)
          ((hprod.prod (euclideanMetric (E := ℝ))).restrictOpen O)
          ((hprod.prod (euclideanMetric (E := ℝ))).restrictOpen O) (Φ.symm y) ≤ δprod) → False := by
  obtain ⟨η, ε₀, δ₀, hη, hε₀, hεhalf, hδ₀, hgeometry⟩ :=
    exists_uniform_incoming_cap_geometry D r eps C₀ C hC₀ heps hepssmall hr hfit
  refine ⟨η, ε₀, δ₀, hη, hε₀, hεhalf, hδ₀, ?_⟩
  intro E H0 M _ _ _ _ _ I _ _ _ _ _ g x₀ δ k d A hA m ζ w hm hζ hupper
    H first last hle s G L hinit J hJ q q₀ a₀ hq hq₀ hq₀Q haq hzero hscalar parameters records
    hfixed hlower hδ hderiv hfinal htime z x Atrace hz hanchor Q Aratio hQ hratio
    F H' _ _ _ _ Jp _ N _ _ _ _ _ _ hprod hdim O V Φ hcapture δprod hδprod hδsmall hproduct
  obtain ⟨Ξ, _, _, p, tip, _, _, nk, K, hx, _, _, hfront, hsc, hball⟩ :=
    hgeometry w hm hζ hupper H first last hle s G L hinit J hJ q q₀ a₀ hq hq₀ hq₀Q haq
      hzero hscalar parameters records hfixed hlower hδ hderiv hfinal htime z x Atrace hz hanchor
  apply nk.not_mem_interior_of_frontier_in_scaled_product_chart L.metric hq hQ
    (by norm_num : (0 : ℝ) ≤ 7/8) hratio hepssmall
    (s := 0) ⟨neg_lt_zero.mpr (inv_pos.mpr heps), inv_pos.mpr heps⟩ K.compact hfront
    (by linarith [(abs_lt.mp hsc).1] : (7/8:ℝ) ≤ metricScalarAt (scaleMetric q hq L.metric)
      (H.backwardSurvivorIncomingMap first last hle G (Ξ p))) hball hprod hdim O V Φ
      (by convert hcapture using 2; ring) hδprod hδsmall (fun y _ n hn => hproduct y n hn) hx


end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory
