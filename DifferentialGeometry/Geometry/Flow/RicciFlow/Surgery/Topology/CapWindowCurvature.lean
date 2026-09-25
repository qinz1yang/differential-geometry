import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CapWindowGeometry
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.LocalWindowCurvatureHorizon
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.Derivatives.LocalPullbackScaling
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.WindowMetricComparison

set_option autoImplicit false
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

theorem exists_uniform_incoming_cap_window_flow_with_uniform_curvature_derivative_bounds
    (N : ℕ) (D r eps C₀ : ℝ) (hC₀ : 0 < C₀)
    (heps : 0 < eps) (hepssmall : eps ≤ 1 / 1000)
    (hr : StandardCap.transitionEnd + eps⁻¹ + 1 < r)
    (hfit : 64 * (r + eps⁻¹) < D) :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ C : ℝ≥0,
      ∃ η ε₀ δ₀ : ℝ, 0 < η ∧ 0 < ε₀ ∧ ε₀ ≤ 1 / 2 ∧ 0 < δ₀ ∧
      ∀ {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
        [FiniteDimensional ℝ E] [Fact (Module.finrank ℝ E = 3)]
        [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
        [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
        {g : SmoothRiemannianMetric I M} {x₀ : M} {δ : ℝ} {k : ℕ}
        {d : normalizedDatum g x₀ δ k} {A : ℝ} {hA : 0 < A} {m : ℕ} {ζ : ℝ}
        (w : StandardCap.CanonicalStaticInsertionWitness d A hA D m ζ),
      max ⌈eps⁻¹⌉₊ N + 2 ≤ m → ζ ≤ ε₀ →
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
        (A : BackwardPointTrace H first last hle x.val),
        A.point first le_rfl hle = J z →
      ∃ Ξ : standardCapWindow D → H.backwardSurvivorIncomingDomain first last hle G,
        IsSmoothEmbedding ThreeModel ThreeModel ∞ Ξ ∧
        (∀ y, H.backwardSurvivorMap first last hle first le_rfl hle (Ξ y).val = J y) ∧
        H.backwardSurvivorIncomingMap first last hle G (Ξ z) = x ∧
        ∃ (hΞ : IsLocalDiffeomorph ThreeModel ThreeModel ∞ Ξ)
          (gflow : ℝ → SmoothRiemannianMetric ThreeModel
            (H.backwardSurvivorIncomingDomain first last hle G))
          (S : SolutionOn (I := ThreeModel) (M := standardCapWindow D)
            (RealTimeInterval.closed 0 (q * (s - H.time first))
              (by have ht := (H.time_strictMono.monotone hle).trans_lt G.lt; positivity))),
          (∀ (j : Fin H.eventCount) (hf : first ≤ j.castSucc) (hl : j.succ ≤ last),
            ∀ t ∈ Icc (H.time j.castSucc) (H.time j.succ),
              gflow t = (H.backwardSurvivorSlabMetric first last hle j hf hl t).restrictOpen
                (H.backwardSurvivorIncomingDomain first last hle G)) ∧
          (∀ t ∈ Icc (H.time last) s,
            gflow t = H.backwardSurvivorIncomingMetric first last hle G L t) ∧
          IsSolutionOn S ∧ S.base.metric 0 = w.windowMetric ∧
          (∀ t, S.base.metric t = localPullMetric
            (scaleMetric q hq (gflow (H.time first + t / q))) Ξ hΞ) ∧
          (∀ (y : standardCapWindow D) (j k : Fin (Module.finrank ℝ ThreeSpace)),
            ContMDiffOn (𝓘(ℝ, ℝ).prod ThreeModel) 𝓘(ℝ) ∞
              (fun z : ℝ × standardCapWindow D => DifferentialGeometry.Tensor.Coordinates.chartGramMatrix
                (S.base.metric z.1) y z.2 j k)
              (Icc 0 (q * (s - H.time first)) ×ˢ
                (trivializationAt ThreeSpace (TangentSpace ThreeModel) y).baseSet)) ∧
          (∀ j ≤ N, ∀ t ∈ Icc 0 (q * (s - H.time first)),
            ∀ y : standardCapWindow D, ‖y.val‖ ≤ r → curvDerivNormSq j (S.base.metric t) y ≤ B) ∧
          (∀ y (v z : TangentSpace ThreeModel y),
            (S.base.metric (q * (s - H.time first))).inner y v z =
              (scaleMetric q hq L.metric).inner
                (H.backwardSurvivorIncomingMap first last hle G (Ξ y))
                (mfderiv ThreeModel ThreeModel (H.backwardSurvivorIncomingMap first last hle G ∘ Ξ) y v)
                (mfderiv ThreeModel ThreeModel (H.backwardSurvivorIncomingMap first last hle G ∘ Ξ) y z)) ∧
        (∀ y : standardCapWindow D, ‖y.val‖ < D → ∀ v : TangentSpace ThreeModel y,
          (1/4:ℝ)*StandardCap.metric.inner y.val v v ≤
            (scaleMetric q hq L.metric).inner (H.backwardSurvivorIncomingMap first last hle G (Ξ y))
              (mfderiv ThreeModel ThreeModel (H.backwardSurvivorIncomingMap first last hle G ∘ Ξ) y v)
              (mfderiv ThreeModel ThreeModel (H.backwardSurvivorIncomingMap first last hle G ∘ Ξ) y v) ∧
          (scaleMetric q hq L.metric).inner (H.backwardSurvivorIncomingMap first last hle G (Ξ y))
              (mfderiv ThreeModel ThreeModel (H.backwardSurvivorIncomingMap first last hle G ∘ Ξ) y v)
              (mfderiv ThreeModel ThreeModel (H.backwardSurvivorIncomingMap first last hle G ∘ Ξ) y v) ≤
            4*StandardCap.metric.inner y.val v v) ∧
        ∀ j ≤ N, ∀ y : standardCapWindow D, ‖y.val‖ ≤ r →
          curvDerivNormSq j L.metric (H.backwardSurvivorIncomingMap first last hle G (Ξ y)) ≤
            q^(j+2)*B := by
  let K₀ := (2 * Real.sqrt 3 * (C₀ + max (2 * C₀) (Real.exp 4))) ^ 2
  have hrpos : 0 < r := by linarith [StandardCap.transitionEnd_pos, inv_pos.mpr heps]
  obtain ⟨B,hB,hjets⟩ :=
    StandardCap.exists_uniform_window_flow_curvature_derivative_bound_of_local_curvature_bounded_horizon
      N (32*r) 1 K₀ (by positivity)
  refine ⟨B, hB, ?_⟩
  intro C
  obtain ⟨η₁,ε₀,δ₀,hη₁,hε₀,hεhalf,hδ₀,hsurvive⟩ :=
    exists_uniform_incoming_cap_window_survival_time D r eps C₀ C hC₀ heps hepssmall hr hfit
  obtain ⟨τ,hτ,hmetricBound⟩ :=
    StandardCap.exists_uniform_window_flow_inner_bounds_of_local_curvature K₀
  let η := min η₁ (min τ (min 1 (2*C*C₀+1)⁻¹))
  refine ⟨η,ε₀,δ₀,lt_min hη₁ (lt_min hτ (lt_min (by norm_num) (by positivity))),hε₀,hεhalf,hδ₀,?_⟩
  intro E H0 M _ _ _ _ _ I _ _ _ _ _ g x₀ δ k d A hA m ζ w hm hζ hupper
    H first last hle s G L hinit J hJ q q₀ a₀ hq hq₀ hq₀Q haq hzero hscalar parameters records
    hfixed hlower hδ hderiv hfinal htime z x Atrace hanchor
  obtain ⟨Ξ, hΞs, hbirth⟩ := hsurvive w (by omega) (hζ) hupper
    H first last hle s G hinit J hJ q q₀ a₀ hq hq₀ hq₀Q haq hzero hscalar parameters records
    hfixed hlower hδ hderiv hfinal (htime.trans (min_le_left _ _)) z x.val Atrace hanchor
  have hΞ : IsLocalDiffeomorph ThreeModel ThreeModel ∞ Ξ := fun y =>
    Perelman.KappaSolutions.immersionAt_isLocalDiffeomorphAt_of_finrank_eq rfl
      (hΞs.isImmersion.isImmersionAt y)
  let θ := q * (s - H.time first)
  have hθ : 0 < θ := mul_pos hq (sub_pos.mpr ((H.time_strictMono.monotone hle).trans_lt G.lt))
  have hθτ : θ ≤ τ := htime.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hθone : θ ≤ 1 := htime.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have htime2 : 2 * C * C₀ * θ ≤ 1 := by
    have hh := htime.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
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
  have hcurv : ∀ t ∈ Icc 0 θ, ∀ y : standardCapWindow D, ‖y.val‖ ≤ 32*r →
      nablaKRm04NormSqIntrinsic S 0 t y ≤ K₀ := by
    intro t ht y _
    simpa only [nablaKRm04NormSqIntrinsic, nablaKRm04Field_zero, Nat.add_zero] using hRm t ht y
  have hjetsS := hjets w (hζ.trans hεhalf) (by omega) (by linarith [inv_pos.mpr heps])
    _ θ hθ hθone (fun _ ht => ht) (fun _ ht => ht) S hS hSzero hgram hcurv
  have hpoint : Φ z = x :=
    H.backwardSurvivorIncomingMap_eq_of_initial_point_eq first last hle G J Ξ hbirth x Atrace z hanchor.symm
  have hmetricControl := hmetricBound w (hζ.trans hεhalf) _ θ hθτ
    (fun _ ht => ht) (fun _ ht => ht) S hS hSzero
    (fun t ht y _ => by
      simpa only [nablaKRm04NormSqIntrinsic,nablaKRm04Field_zero,Nat.add_zero] using hRm t ht y)
    θ ⟨hθ.le,le_rfl⟩
  have halljets : ∀ j ≤ N, ∀ t ∈ Icc 0 θ,
      ∀ y : standardCapWindow D, ‖y.val‖ ≤ r → curvDerivNormSq j (S.base.metric t) y ≤ B := by
    intro j hj t ht y hy
    rw [curvNormSq_eq]
    apply hjetsS j hj t ht y
    have he : 32*r/32=r := by ring
    rw [he]
    exact hy
  refine ⟨Ξ, hΞs, hbirth, hpoint, hΞ, gflow, S, hslabs, hlast, hS, hSzero,
    hmetric, hgram, halljets, hmet, ?_, ?_⟩
  · intro y hy v
    have hb := hmetricControl y hy v
    rwa [hmet] at hb
  intro j hj y hy
  have hnorm : curvDerivNormSq j (S.base.metric θ) y ≤ B := by
    rw [curvNormSq_eq]
    apply hjetsS j hj θ ⟨hθ.le,le_rfl⟩ y
    have he : 32*r/32=r := by ring
    rw [he]
    exact hy
  apply curvDerivNormSq_le_of_scaled_local_isometry
    (S.base.metric θ) L.metric Φ hΦ hq ?_ rfl hnorm
  intro a v w
  simpa only [h,scaleMetric_inner] using hmet a v w

theorem exists_uniform_incoming_cap_window_flow_with_curvature_derivative_bounds_of_radius_lower_bound
    (C₀ : ℝ) (C : ℝ≥0) (hC₀ : 0 < C₀) :
    ∃ η ε₀ : ℝ, 0 < η ∧ 0 < ε₀ ∧ ε₀ ≤ 1 / 2 ∧
      ∀ (N : ℕ) (D r : ℝ), 65 ≤ D → 0 < r → 32 * r < D →
      ∃ δ₀ B : ℝ, 1 ≤ B ∧ 0 < δ₀ ∧
      ∀ {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
        [FiniteDimensional ℝ E] [Fact (Module.finrank ℝ E = 3)]
        [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
        [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
        {g : SmoothRiemannianMetric I M} {x₀ : M} {δ : ℝ} {k : ℕ}
        {d : normalizedDatum g x₀ δ k} {A : ℝ} {hA : 0 < A} {m : ℕ} {ζ : ℝ}
        (w : StandardCap.CanonicalStaticInsertionWitness d A hA D m ζ),
      max 2 N + 2 ≤ m → ζ ≤ ε₀ →
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
        (A : BackwardPointTrace H first last hle x.val),
        A.point first le_rfl hle = J z →
      ∃ Ξ : standardCapWindow D → H.backwardSurvivorIncomingDomain first last hle G,
        IsSmoothEmbedding ThreeModel ThreeModel ∞ Ξ ∧
        (∀ y, H.backwardSurvivorMap first last hle first le_rfl hle (Ξ y).val = J y) ∧
        H.backwardSurvivorIncomingMap first last hle G (Ξ z) = x ∧
        ∃ (hΞ : IsLocalDiffeomorph ThreeModel ThreeModel ∞ Ξ)
          (gflow : ℝ → SmoothRiemannianMetric ThreeModel
            (H.backwardSurvivorIncomingDomain first last hle G))
          (S : SolutionOn (I := ThreeModel) (M := standardCapWindow D)
            (RealTimeInterval.closed 0 (q * (s - H.time first))
              (by have ht := (H.time_strictMono.monotone hle).trans_lt G.lt; positivity))),
          (∀ (j : Fin H.eventCount) (hf : first ≤ j.castSucc) (hl : j.succ ≤ last),
            ∀ t ∈ Icc (H.time j.castSucc) (H.time j.succ),
              gflow t = (H.backwardSurvivorSlabMetric first last hle j hf hl t).restrictOpen
                (H.backwardSurvivorIncomingDomain first last hle G)) ∧
          (∀ t ∈ Icc (H.time last) s,
            gflow t = H.backwardSurvivorIncomingMetric first last hle G L t) ∧
          IsSolutionOn S ∧ S.base.metric 0 = w.windowMetric ∧
          (∀ t, S.base.metric t = localPullMetric
            (scaleMetric q hq (gflow (H.time first + t / q))) Ξ hΞ) ∧
          (∀ (y : standardCapWindow D) (j k : Fin (Module.finrank ℝ ThreeSpace)),
            ContMDiffOn (𝓘(ℝ, ℝ).prod ThreeModel) 𝓘(ℝ) ∞
              (fun z : ℝ × standardCapWindow D => DifferentialGeometry.Tensor.Coordinates.chartGramMatrix
                (S.base.metric z.1) y z.2 j k)
              (Icc 0 (q * (s - H.time first)) ×ˢ
                (trivializationAt ThreeSpace (TangentSpace ThreeModel) y).baseSet)) ∧
          (∀ j ≤ N, ∀ t ∈ Icc 0 (q * (s - H.time first)),
            ∀ y : standardCapWindow D, ‖y.val‖ ≤ r → curvDerivNormSq j (S.base.metric t) y ≤ B) ∧
          (∀ y (v z : TangentSpace ThreeModel y),
            (S.base.metric (q * (s - H.time first))).inner y v z =
              (scaleMetric q hq L.metric).inner
                (H.backwardSurvivorIncomingMap first last hle G (Ξ y))
                (mfderiv ThreeModel ThreeModel (H.backwardSurvivorIncomingMap first last hle G ∘ Ξ) y v)
                (mfderiv ThreeModel ThreeModel (H.backwardSurvivorIncomingMap first last hle G ∘ Ξ) y z)) ∧
        (∀ y : standardCapWindow D, ‖y.val‖ < D → ∀ v : TangentSpace ThreeModel y,
          (1/4:ℝ)*StandardCap.metric.inner y.val v v ≤
            (scaleMetric q hq L.metric).inner (H.backwardSurvivorIncomingMap first last hle G (Ξ y))
              (mfderiv ThreeModel ThreeModel (H.backwardSurvivorIncomingMap first last hle G ∘ Ξ) y v)
              (mfderiv ThreeModel ThreeModel (H.backwardSurvivorIncomingMap first last hle G ∘ Ξ) y v) ∧
          (scaleMetric q hq L.metric).inner (H.backwardSurvivorIncomingMap first last hle G (Ξ y))
              (mfderiv ThreeModel ThreeModel (H.backwardSurvivorIncomingMap first last hle G ∘ Ξ) y v)
              (mfderiv ThreeModel ThreeModel (H.backwardSurvivorIncomingMap first last hle G ∘ Ξ) y v) ≤
            4*StandardCap.metric.inner y.val v v) ∧
        ∀ j ≤ N, ∀ y : standardCapWindow D, ‖y.val‖ ≤ r →
          curvDerivNormSq j L.metric (H.backwardSurvivorIncomingMap first last hle G (Ξ y)) ≤
            q^(j+2)*B := by
  let K₀ := (2 * Real.sqrt 3 * (C₀ + max (2 * C₀) (Real.exp 4))) ^ 2
  obtain ⟨η₁, ε₀, hη₁, hε₀, hεhalf, hsurvive⟩ :=
    exists_uniform_incoming_cap_window_survival_time_of_radius_lower_bound C₀ C hC₀
  obtain ⟨τ, hτ, hmetricBound⟩ :=
    StandardCap.exists_uniform_window_flow_inner_bounds_of_local_curvature K₀
  let η := min η₁ (min τ (min 1 (2 * C * C₀ + 1)⁻¹))
  refine ⟨η, ε₀, lt_min hη₁ (lt_min hτ (lt_min (by norm_num) (by positivity))), hε₀, hεhalf, ?_⟩
  intro N D r hD hrpos hfit
  obtain ⟨δ₀, hδ₀, hsurvive⟩ := hsurvive D hD
  obtain ⟨B, hB, hjets⟩ :=
    StandardCap.exists_uniform_window_flow_curvature_derivative_bound_of_local_curvature_bounded_horizon
      N (32 * r) 1 K₀ (by positivity)
  refine ⟨δ₀, B, hB, hδ₀, ?_⟩
  intro E H0 M _ _ _ _ _ I _ _ _ _ _ g x₀ δ k d A hA m ζ w hm hζ hupper
    H first last hle s G L hinit J hJ q q₀ a₀ hq hq₀ hq₀Q haq hzero hscalar parameters records
    hfixed hlower hδ hderiv hfinal htime z x Atrace hanchor
  obtain ⟨Ξ, hΞs, hbirth⟩ := hsurvive w (by omega) (hζ) hupper
    H first last hle s G hinit J hJ q q₀ a₀ hq hq₀ hq₀Q haq hzero hscalar parameters records
    hfixed hlower hδ hderiv hfinal (htime.trans (min_le_left _ _)) z x.val Atrace hanchor
  have hΞ : IsLocalDiffeomorph ThreeModel ThreeModel ∞ Ξ := fun y =>
    Perelman.KappaSolutions.immersionAt_isLocalDiffeomorphAt_of_finrank_eq rfl
      (hΞs.isImmersion.isImmersionAt y)
  let θ := q * (s - H.time first)
  have hθ : 0 < θ := mul_pos hq (sub_pos.mpr ((H.time_strictMono.monotone hle).trans_lt G.lt))
  have hθτ : θ ≤ τ := htime.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hθone : θ ≤ 1 := htime.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have htime2 : 2 * C * C₀ * θ ≤ 1 := by
    have hh := htime.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
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
  have hcurv : ∀ t ∈ Icc 0 θ, ∀ y : standardCapWindow D, ‖y.val‖ ≤ 32*r →
      nablaKRm04NormSqIntrinsic S 0 t y ≤ K₀ := by
    intro t ht y _
    simpa only [nablaKRm04NormSqIntrinsic, nablaKRm04Field_zero, Nat.add_zero] using hRm t ht y
  have hjetsS := hjets w (hζ.trans hεhalf) (by omega) hfit
    _ θ hθ hθone (fun _ ht => ht) (fun _ ht => ht) S hS hSzero hgram hcurv
  have hpoint : Φ z = x :=
    H.backwardSurvivorIncomingMap_eq_of_initial_point_eq first last hle G J Ξ hbirth x Atrace z hanchor.symm
  have hmetricControl := hmetricBound w (hζ.trans hεhalf) _ θ hθτ
    (fun _ ht => ht) (fun _ ht => ht) S hS hSzero
    (fun t ht y _ => by
      simpa only [nablaKRm04NormSqIntrinsic,nablaKRm04Field_zero,Nat.add_zero] using hRm t ht y)
    θ ⟨hθ.le,le_rfl⟩
  have halljets : ∀ j ≤ N, ∀ t ∈ Icc 0 θ,
      ∀ y : standardCapWindow D, ‖y.val‖ ≤ r → curvDerivNormSq j (S.base.metric t) y ≤ B := by
    intro j hj t ht y hy
    rw [curvNormSq_eq]
    apply hjetsS j hj t ht y
    have he : 32*r/32=r := by ring
    rw [he]
    exact hy
  refine ⟨Ξ, hΞs, hbirth, hpoint, hΞ, gflow, S, hslabs, hlast, hS, hSzero,
    hmetric, hgram, halljets, hmet, ?_, ?_⟩
  · intro y hy v
    have hb := hmetricControl y hy v
    rwa [hmet] at hb
  intro j hj y hy
  have hnorm : curvDerivNormSq j (S.base.metric θ) y ≤ B := by
    rw [curvNormSq_eq]
    apply hjetsS j hj θ ⟨hθ.le,le_rfl⟩ y
    have he : 32*r/32=r := by ring
    rw [he]
    exact hy
  apply curvDerivNormSq_le_of_scaled_local_isometry
    (S.base.metric θ) L.metric Φ hΦ hq ?_ rfl hnorm
  intro a v w
  simpa only [h,scaleMetric_inner] using hmet a v w

theorem exists_uniform_incoming_cap_window_flow_with_curvature_derivative_bounds
    (N : ℕ) (D r eps C₀ : ℝ) (C : ℝ≥0) (hC₀ : 0 < C₀)
    (heps : 0 < eps) (hepssmall : eps ≤ 1 / 1000)
    (hr : StandardCap.transitionEnd + eps⁻¹ + 1 < r)
    (hfit : 64 * (r + eps⁻¹) < D) :
    ∃ η ε₀ δ₀ B : ℝ, 1 ≤ B ∧ 0 < η ∧ 0 < ε₀ ∧ ε₀ ≤ 1 / 2 ∧ 0 < δ₀ ∧
      ∀ {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
        [FiniteDimensional ℝ E] [Fact (Module.finrank ℝ E = 3)]
        [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
        [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
        {g : SmoothRiemannianMetric I M} {x₀ : M} {δ : ℝ} {k : ℕ}
        {d : normalizedDatum g x₀ δ k} {A : ℝ} {hA : 0 < A} {m : ℕ} {ζ : ℝ}
        (w : StandardCap.CanonicalStaticInsertionWitness d A hA D m ζ),
      max ⌈eps⁻¹⌉₊ N + 2 ≤ m → ζ ≤ ε₀ →
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
        (A : BackwardPointTrace H first last hle x.val),
        A.point first le_rfl hle = J z →
      ∃ Ξ : standardCapWindow D → H.backwardSurvivorIncomingDomain first last hle G,
        IsSmoothEmbedding ThreeModel ThreeModel ∞ Ξ ∧
        (∀ y, H.backwardSurvivorMap first last hle first le_rfl hle (Ξ y).val = J y) ∧
        H.backwardSurvivorIncomingMap first last hle G (Ξ z) = x ∧
        ∃ (hΞ : IsLocalDiffeomorph ThreeModel ThreeModel ∞ Ξ)
          (gflow : ℝ → SmoothRiemannianMetric ThreeModel
            (H.backwardSurvivorIncomingDomain first last hle G))
          (S : SolutionOn (I := ThreeModel) (M := standardCapWindow D)
            (RealTimeInterval.closed 0 (q * (s - H.time first))
              (by have ht := (H.time_strictMono.monotone hle).trans_lt G.lt; positivity))),
          (∀ (j : Fin H.eventCount) (hf : first ≤ j.castSucc) (hl : j.succ ≤ last),
            ∀ t ∈ Icc (H.time j.castSucc) (H.time j.succ),
              gflow t = (H.backwardSurvivorSlabMetric first last hle j hf hl t).restrictOpen
                (H.backwardSurvivorIncomingDomain first last hle G)) ∧
          (∀ t ∈ Icc (H.time last) s,
            gflow t = H.backwardSurvivorIncomingMetric first last hle G L t) ∧
          IsSolutionOn S ∧ S.base.metric 0 = w.windowMetric ∧
          (∀ t, S.base.metric t = localPullMetric
            (scaleMetric q hq (gflow (H.time first + t / q))) Ξ hΞ) ∧
          (∀ (y : standardCapWindow D) (j k : Fin (Module.finrank ℝ ThreeSpace)),
            ContMDiffOn (𝓘(ℝ, ℝ).prod ThreeModel) 𝓘(ℝ) ∞
              (fun z : ℝ × standardCapWindow D => DifferentialGeometry.Tensor.Coordinates.chartGramMatrix
                (S.base.metric z.1) y z.2 j k)
              (Icc 0 (q * (s - H.time first)) ×ˢ
                (trivializationAt ThreeSpace (TangentSpace ThreeModel) y).baseSet)) ∧
          (∀ j ≤ N, ∀ t ∈ Icc 0 (q * (s - H.time first)),
            ∀ y : standardCapWindow D, ‖y.val‖ ≤ r → curvDerivNormSq j (S.base.metric t) y ≤ B) ∧
          (∀ y (v z : TangentSpace ThreeModel y),
            (S.base.metric (q * (s - H.time first))).inner y v z =
              (scaleMetric q hq L.metric).inner
                (H.backwardSurvivorIncomingMap first last hle G (Ξ y))
                (mfderiv ThreeModel ThreeModel (H.backwardSurvivorIncomingMap first last hle G ∘ Ξ) y v)
                (mfderiv ThreeModel ThreeModel (H.backwardSurvivorIncomingMap first last hle G ∘ Ξ) y z)) ∧
        (∀ y : standardCapWindow D, ‖y.val‖ < D → ∀ v : TangentSpace ThreeModel y,
          (1/4:ℝ)*StandardCap.metric.inner y.val v v ≤
            (scaleMetric q hq L.metric).inner (H.backwardSurvivorIncomingMap first last hle G (Ξ y))
              (mfderiv ThreeModel ThreeModel (H.backwardSurvivorIncomingMap first last hle G ∘ Ξ) y v)
              (mfderiv ThreeModel ThreeModel (H.backwardSurvivorIncomingMap first last hle G ∘ Ξ) y v) ∧
          (scaleMetric q hq L.metric).inner (H.backwardSurvivorIncomingMap first last hle G (Ξ y))
              (mfderiv ThreeModel ThreeModel (H.backwardSurvivorIncomingMap first last hle G ∘ Ξ) y v)
              (mfderiv ThreeModel ThreeModel (H.backwardSurvivorIncomingMap first last hle G ∘ Ξ) y v) ≤
            4*StandardCap.metric.inner y.val v v) ∧
        ∀ j ≤ N, ∀ y : standardCapWindow D, ‖y.val‖ ≤ r →
          curvDerivNormSq j L.metric (H.backwardSurvivorIncomingMap first last hle G (Ξ y)) ≤
            q^(j+2)*B := by
  have hinv : 1000 ≤ eps⁻¹ := by
    have hh := inv_anti₀ heps hepssmall
    norm_num at hh
    exact hh
  have hD : 65 ≤ D := by linarith [StandardCap.transitionEnd_pos]
  have hrpos : 0 < r := by linarith [StandardCap.transitionEnd_pos]
  obtain ⟨η, ε₀, hη, hε₀, hεhalf, hflow⟩ :=
    exists_uniform_incoming_cap_window_flow_with_curvature_derivative_bounds_of_radius_lower_bound C₀ C hC₀
  obtain ⟨δ₀, B, hB, hδ₀, hflow⟩ := hflow N D r hD hrpos (by linarith)
  refine ⟨η, ε₀, δ₀, B, hB, hη, hε₀, hεhalf, hδ₀, ?_⟩
  intro E H M _ _ _ _ _ I _ _ _ _ _ g x₀ δ k d A hA m ζ w hm
  have hceil : 2 ≤ ⌈eps⁻¹⌉₊ := by
    exact_mod_cast (show (2 : ℝ) ≤ (⌈eps⁻¹⌉₊ : ℝ) from
      (by linarith : (2 : ℝ) ≤ eps⁻¹).trans (Nat.le_ceil _))
  exact hflow w (by omega)


theorem exists_uniform_incoming_cap_curvature_derivative_bound
    (N : ℕ) (D r eps C₀ : ℝ) (C : ℝ≥0) (hC₀ : 0 < C₀)
    (heps : 0 < eps) (hepssmall : eps ≤ 1 / 1000)
    (hr : StandardCap.transitionEnd + eps⁻¹ + 1 < r)
    (hfit : 64 * (r + eps⁻¹) < D) :
    ∃ η ε₀ δ₀ B : ℝ, 1 ≤ B ∧ 0 < η ∧ 0 < ε₀ ∧ ε₀ ≤ 1 / 2 ∧ 0 < δ₀ ∧
      ∀ {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
        [FiniteDimensional ℝ E] [Fact (Module.finrank ℝ E = 3)]
        [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
        [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
        {g : SmoothRiemannianMetric I M} {x₀ : M} {δ : ℝ} {k : ℕ}
        {d : normalizedDatum g x₀ δ k} {A : ℝ} {hA : 0 < A} {m : ℕ} {ζ : ℝ}
        (w : StandardCap.CanonicalStaticInsertionWitness d A hA D m ζ),
      max ⌈eps⁻¹⌉₊ N + 2 ≤ m → ζ ≤ ε₀ →
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
        (A : BackwardPointTrace H first last hle x.val),
        A.point first le_rfl hle = J z →
      ∃ Ξ : standardCapWindow D → H.backwardSurvivorIncomingDomain first last hle G,
        IsSmoothEmbedding ThreeModel ThreeModel ∞ Ξ ∧
        (∀ y, H.backwardSurvivorMap first last hle first le_rfl hle (Ξ y).val = J y) ∧
        H.backwardSurvivorIncomingMap first last hle G (Ξ z) = x ∧
        (∀ y : standardCapWindow D, ‖y.val‖ < D → ∀ v : TangentSpace ThreeModel y,
          (1/4:ℝ)*StandardCap.metric.inner y.val v v ≤
            (scaleMetric q hq L.metric).inner (H.backwardSurvivorIncomingMap first last hle G (Ξ y))
              (mfderiv ThreeModel ThreeModel (H.backwardSurvivorIncomingMap first last hle G ∘ Ξ) y v)
              (mfderiv ThreeModel ThreeModel (H.backwardSurvivorIncomingMap first last hle G ∘ Ξ) y v) ∧
          (scaleMetric q hq L.metric).inner (H.backwardSurvivorIncomingMap first last hle G (Ξ y))
              (mfderiv ThreeModel ThreeModel (H.backwardSurvivorIncomingMap first last hle G ∘ Ξ) y v)
              (mfderiv ThreeModel ThreeModel (H.backwardSurvivorIncomingMap first last hle G ∘ Ξ) y v) ≤
            4*StandardCap.metric.inner y.val v v) ∧
        ∀ j ≤ N, ∀ y : standardCapWindow D, ‖y.val‖ ≤ r →
          curvDerivNormSq j L.metric (H.backwardSurvivorIncomingMap first last hle G (Ξ y)) ≤
            q^(j+2)*B := by
  obtain ⟨η, ε₀, δ₀, B, hB, hη, hε₀, hεhalf, hδ₀, hflow⟩ :=
    exists_uniform_incoming_cap_window_flow_with_curvature_derivative_bounds N D r eps C₀ C
      hC₀ heps hepssmall hr hfit
  refine ⟨η, ε₀, δ₀, B, hB, hη, hε₀, hεhalf, hδ₀, ?_⟩
  intro E H0 M _ _ _ _ _ I _ _ _ _ _ g x₀ δ k d A hA m ζ w hm hζ hupper
    H first last hle s G L hinit J hJ q q₀ a₀ hq hq₀ hq₀Q haq hzero hscalar parameters records
    hfixed hlower hδ hderiv hfinal htime z x Atrace hanchor
  obtain ⟨Ξ, hΞs, hbirth, hpoint, hΞ, gflow, S, hslabs, hlast, hS, hSzero,
    hmetric, hgram, halljets, hterminal, hcontrol, hjets⟩ :=
    hflow w hm hζ hupper H first last hle s G L hinit J hJ q q₀ a₀ hq hq₀ hq₀Q haq
      hzero hscalar parameters records hfixed hlower hδ hderiv hfinal htime z x Atrace hanchor
  exact ⟨Ξ, hΞs, hbirth, hpoint, hcontrol, hjets⟩

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory
