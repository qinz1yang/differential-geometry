import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.PreparedCapWindowGeometry
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.UniformWindowJets_S54

/-!
# CH12-S54, group 2: the prepared cap-window kernel with a jets constant independent of `D`, `r`

`PreparedCapWindowGeometry.lean:943`
(`exists_uniform_prepared_incoming_cap_window_flow_with_curvature_derivative_bounds_of_radius_lower_bound`)
chooses its jets constant `B` after `(N, D, r)`.  The proof below is that proof (and the proof of
`CapWindowCurvature.lean:200` that it calls), with the Shi local estimate re-centred at the evaluation
point (`window_flow_curvature_derivative_bound_local_S54`), so that `B` depends on `N` only.
The conclusion is the statement of `:943` verbatim except for the order of the quantifiers
`∀ N, ∃ B, ∀ D r, ∃ δ₀`.
-/

set_option autoImplicit false

noncomputable section

open Set Function Bundle Manifold DifferentialGeometry
open DifferentialGeometry.Geometry.Neck DifferentialGeometry.Geometry.Metric
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Topology.Manifold DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open scoped Manifold ContDiff ENNReal NNReal

namespace GC.LongTime.Ch12

universe u uE uH uM

private local instance (D : ℝ) : SigmaCompactSpace (standardCapWindow D) :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (Geometry.isSigmaCompact_of_isOpen ThreeModel (standardCapWindow D).isOpen)

private theorem window_inclusion_isSmoothEmbedding_S54 {D D' : ℝ} (hDD : D ≤ D') :
    IsSmoothEmbedding ThreeModel ThreeModel ∞
      (TopologicalSpace.Opens.inclusion
        (show standardCapWindow D ≤ standardCapWindow D' from
          by
          intro x hx
          change ‖x‖ < D' + 1
          change ‖x‖ < D + 1 at hx
          linarith only [hx, hDD])) := by
  let inc := TopologicalSpace.Opens.inclusion
    (show standardCapWindow D ≤ standardCapWindow D' from
      by
          intro x hx
          change ‖x‖ < D' + 1
          change ‖x‖ < D + 1 at hx
          linarith only [hx, hDD])
  have hc : ContMDiff ThreeModel ThreeModel ∞ inc := contMDiff_inclusion _
  have hl := DifferentialGeometry.Topology.Manifold.isLocalDiffeomorph_of_injective_mfderiv
    inc hc (fun x => by rw [mfderiv_opens_incl]; exact fun v w h => h) rfl
  apply Perelman.KappaSolutions.localDiffeomorph_isSmoothEmbedding_of_injective hl
  intro x y h
  exact Subtype.ext (congrArg (fun z : standardCapWindow D' => z.val) h)

private theorem prepared_window_restriction_bounds_S54
    {D Dbig : ℝ} (hD : 0 < D) (hmargin : D + 1 ≤ Dbig)
    {E : Type uE} {H : Type uH} {M : Type uM} {N : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [Fact (Module.finrank ℝ E = 3)]
    [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
    [TopologicalSpace N] [ChartedSpace ThreeSpace N] [IsManifold ThreeModel ∞ N]
    {g : SmoothRiemannianMetric I M} {x₀ : M} {δ : ℝ} {k : ℕ}
    {d : normalizedDatum g x₀ δ k} {A : ℝ} {hA : 0 < A} {m : ℕ} {ζ : ℝ}
    (w : StandardCap.CanonicalStaticInsertionWitness d A hA Dbig m ζ) (hζ : ζ ≤ 1 / 2)
    (h : SmoothRiemannianMetric ThreeModel N)
    (Jbig : standardCapWindow Dbig → N) (hJbig : IsSmoothEmbedding ThreeModel ThreeModel ∞ Jbig)
    {q C₀ : ℝ}
    (hzero : ∀ x (v z : TangentSpace ThreeModel x), w.windowMetric.inner x v z =
      q * h.inner (Jbig x) (mfderiv ThreeModel ThreeModel Jbig x v)
        (mfderiv ThreeModel ThreeModel Jbig x z))
    (hscalarbig : ∀ x : standardCapWindow Dbig, ‖x.val‖ < Dbig → metricScalarAt h (Jbig x) ≤ C₀*q) :
    let hDD : D ≤ Dbig := by linarith only [hmargin];
    let inc := TopologicalSpace.Opens.inclusion
      (show standardCapWindow D ≤ standardCapWindow Dbig from by
        intro x hx
        change ‖x‖ < Dbig+1
        change ‖x‖ < D+1 at hx
        linarith only [hx,hmargin]);
    let ws := w.restrictWindow hD hDD;
    let J := Jbig ∘ inc;
    IsSmoothEmbedding ThreeModel ThreeModel ∞ J ∧
    (∀ x : standardCapWindow D, ∀ v : TangentSpace ThreeModel x,
      ws.windowMetric.inner x v v ≤ (3/2:ℝ)*StandardCap.metric.inner x.val v v) ∧
    (∀ x (v z : TangentSpace ThreeModel x), ws.windowMetric.inner x v z =
      q*h.inner (J x) (mfderiv ThreeModel ThreeModel J x v) (mfderiv ThreeModel ThreeModel J x z)) ∧
    ∀ x : standardCapWindow D, metricScalarAt h (J x) ≤ C₀*q := by
  intro hDD inc ws J
  have hJ := hJbig.comp (window_inclusion_isSmoothEmbedding_S54 hDD) (by simp)
  have hpoint (x : standardCapWindow D) : ‖(inc x).val‖ < Dbig := x.property.trans_le hmargin
  refine ⟨hJ,?_,?_,fun x => hscalarbig (inc x) (hpoint x)⟩
  · intro x v
    rw [StandardCap.CanonicalStaticInsertionWitness.restrictWindow_windowMetric]
    change w.windowMetric.inner (inc x) v v ≤ _
    have hb := (w.window_inner_bounds hζ (hpoint x) v).2
    rw [standardCapMetric_eq_metric] at hb
    change w.windowMetric.inner (inc x) v v ≤ (3/2:ℝ)*StandardCap.metric.inner x.val v v at hb
    exact hb
  · intro x v z
    rw [StandardCap.CanonicalStaticInsertionWitness.restrictWindow_windowMetric]
    change w.windowMetric.inner (inc x) v z = _
    have hz := hzero (inc x) (show TangentSpace ThreeModel (inc x) from v)
      (show TangentSpace ThreeModel (inc x) from z)
    let hs : standardCapWindow D ≤ standardCapWindow Dbig := by
      intro y hy
      change ‖y‖ < Dbig + 1
      change ‖y‖ < D + 1 at hy
      linarith only [hy,hmargin]
    have hd := mfderiv_comp x (hJbig.contMDiff.mdifferentiableAt (by simp))
      ((contMDiff_inclusion (I := ThreeModel) (n := ∞) hs).mdifferentiableAt (by simp))
    simp only [mfderiv_opens_incl] at hd
    dsimp only [TangentSpace] at hd hz ⊢
    rw [hd]
    exact hz

theorem exists_uniform_incoming_cap_window_flow_with_curvature_derivative_bounds_uniform_S54
    (C₀ : ℝ) (C : ℝ≥0) (hC₀ : 0 < C₀) :
    ∃ η ε₀ : ℝ, 0 < η ∧ 0 < ε₀ ∧ ε₀ ≤ 1 / 2 ∧
      ∀ (N : ℕ), ∃ B : ℝ, 1 ≤ B ∧ ∀ (D r : ℝ), 65 ≤ D → 0 < r → 32 * r < D →
      ∃ δ₀ : ℝ, 0 < δ₀ ∧
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
  intro N
  obtain ⟨B, hB, hjets⟩ := window_flow_curvature_derivative_bound_local_S54 N 1 K₀
  refine ⟨B, hB, ?_⟩
  intro D r hD hrpos hfit
  obtain ⟨δ₀, hδ₀, hsurvive⟩ := hsurvive D hD
  refine ⟨δ₀, hδ₀, ?_⟩
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
  have hcurv : ∀ t ∈ Icc 0 θ, ∀ y : standardCapWindow D,
      nablaKRm04NormSqIntrinsic S 0 t y ≤ K₀ := by
    intro t ht y
    simpa only [nablaKRm04NormSqIntrinsic, nablaKRm04Field_zero, Nat.add_zero] using hRm t ht y
  have hjetsS : ∀ j ≤ N, ∀ t ∈ Icc 0 θ, ∀ y : standardCapWindow D, ‖y.val‖ ≤ r →
      nablaKRm04NormSqIntrinsic S j t y ≤ B := by
    intro j hj t ht y hy
    exact hjets w (hζ.trans hεhalf) (by omega) _ θ hθ hθone (fun _ ht => ht) (fun _ ht => ht)
      S hS hSzero hgram y (by linarith) (fun s hs z _ => hcurv s hs z) j hj t ht
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
    exact hjetsS j hj t ht y hy
  refine ⟨Ξ, hΞs, hbirth, hpoint, hΞ, gflow, S, hslabs, hlast, hS, hSzero,
    hmetric, hgram, halljets, hmet, ?_, ?_⟩
  · intro y hy v
    have hb := hmetricControl y hy v
    rwa [hmet] at hb
  intro j hj y hy
  have hnorm : curvDerivNormSq j (S.base.metric θ) y ≤ B := by
    rw [curvNormSq_eq]
    exact hjetsS j hj θ ⟨hθ.le,le_rfl⟩ y hy
  apply curvDerivNormSq_le_of_scaled_local_isometry
    (S.base.metric θ) L.metric Φ hΦ hq ?_ rfl hnorm
  intro a v w
  simpa only [h,scaleMetric_inner] using hmet a v w

theorem exists_uniform_prepared_incoming_cap_window_flow_with_curvature_derivative_bounds_uniform_S54
    (C : ℝ≥0) :
    ∃ C₀ : ℝ, 0 < C₀ ∧ (
      ∀ {E : Type uE} {H : Type uH} {M : Type uM} {N : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
        [FiniteDimensional ℝ E] [Fact (Module.finrank ℝ E = 3)]
        [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
        [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
        [TopologicalSpace N] [ChartedSpace ThreeSpace N] [IsManifold ThreeModel ∞ N]
        [T2Space N]
        {g : SmoothRiemannianMetric I M} {x₀ : M} {δ : ℝ} {k : ℕ}
        {d : normalizedDatum g x₀ δ k} {A : ℝ} {hA : 0 < A} {D : ℝ}
        {m : ℕ} {ε : ℝ} (w : StandardCap.CanonicalStaticInsertionWitness d A hA D m ε),
        ε ≤ 1 / 2 → 2 ≤ m →
        ∀ (h : SmoothRiemannianMetric ThreeModel N) (J : standardCapWindow D → N),
        IsSmoothEmbedding ThreeModel ThreeModel ∞ J →
        ∀ q : ℝ, 0 < q →
        (∀ x v z, w.windowMetric.inner x v z =
          q * h.inner (J x) (mfderiv ThreeModel ThreeModel J x v)
            (mfderiv ThreeModel ThreeModel J x z)) →
        ∀ x : standardCapWindow D, ‖x.val‖ < D →
          |metricScalarAt h (J x)| ≤ C₀ * q) ∧
    ∃ η ε₀ : ℝ, 0 < η ∧ 0 < ε₀ ∧ ε₀ ≤ 1 / 2 ∧
      ∀ (N : ℕ), ∃ B : ℝ, 1 ≤ B ∧ ∀ (D r : ℝ), 65 ≤ D → 0 < r → 32 * r < D →
      ∃ δ₀ : ℝ, 0 < δ₀ ∧
      ∀ {E : Type uE} {H : Type uH} {M : Type uM} [NormedAddCommGroup E] [NormedSpace ℝ E]
        [FiniteDimensional ℝ E] [Fact (Module.finrank ℝ E = 3)]
        [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
        [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
        {g : SmoothRiemannianMetric I M} {x₀ : M} {δ : ℝ} {k : ℕ}
        {d : normalizedDatum g x₀ δ k} {A : ℝ} {hA : 0 < A} {Dbig : ℝ} {m : ℕ} {ζ : ℝ}
        (w : StandardCap.CanonicalStaticInsertionWitness d A hA Dbig m ζ)
        (hmargin : D + 1 ≤ Dbig),
      max 2 N + 2 ≤ m → ζ ≤ ε₀ →
      let inc : standardCapWindow D → standardCapWindow Dbig := TopologicalSpace.Opens.inclusion
        (show standardCapWindow D ≤ standardCapWindow Dbig from by
          intro x hx
          change ‖x‖ < Dbig + 1
          change ‖x‖ < D + 1 at hx
          linarith only [hx, hmargin]);
      ∀ (H : ObservedHistory.{u}) (first last : Fin (H.eventCount + 1)) (hle : first ≤ last)
        (s : ℝ) (G : (H.stage last).IncomingSlab (H.time last) s) (L : G.TerminalLimitMetric),
      G.flow.base.metric (H.time last) = H.initialMetric last →
      ∀ (Jbig : standardCapWindow Dbig → (H.stage first).Carrier),
      IsSmoothEmbedding ThreeModel ThreeModel ∞ Jbig →
      let J := Jbig ∘ inc;
      ∀ (q q₀ a₀ : ℝ) (hq : 0 < q), 0 < q₀ → q₀ ≤ C₀ * q → 1 ≤ a₀ * q →
      (∀ x (v z : TangentSpace ThreeModel x), w.windowMetric.inner x v z =
        q * (H.initialMetric first).inner (Jbig x) (mfderiv ThreeModel ThreeModel Jbig x v)
          (mfderiv ThreeModel ThreeModel Jbig x z)) →
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
          IsSolutionOn S ∧ S.base.metric 0 = w.windowMetric.restrictOpenOfSubset
            (show standardCapWindow D ≤ standardCapWindow Dbig from
              fun _ hx => hx.trans_le (add_le_add (show D ≤ Dbig by linarith) (le_refl 1))) ∧
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
  obtain ⟨C₀,hC₀,hbound⟩ :=
    StandardCap.exists_uniform_window_image_scalar_bound_of_scaled_pullback
  refine ⟨C₀,hC₀,hbound,?_⟩
  obtain ⟨η, ε₀, hη, hε₀, hεhalf, hjets⟩ :=
    exists_uniform_incoming_cap_window_flow_with_curvature_derivative_bounds_uniform_S54 C₀ C hC₀
  refine ⟨η, ε₀, hη, hε₀, hεhalf, ?_⟩
  intro N
  obtain ⟨B, hB, hjets⟩ := hjets N
  refine ⟨B, hB, ?_⟩
  intro D r hD65 hrpos hfit
  obtain ⟨δ₀, hδ₀, hjets⟩ := hjets D r hD65 hrpos hfit
  refine ⟨δ₀, hδ₀, ?_⟩
  intro E H0 M _ _ _ _ _ I _ _ _ _ _ g x₀ δ k d A hA Dbig m ζ w hmargin hm hζ
    inc H first last hle s G L hinit Jbig hJbig J q q₀ a₀ hq hq₀ hq₀Q haq hzero
    parameters records hfixed hlower hδ hderiv hfinal htime z x Atrace hanchor
  have hD : 0 < D := by linarith
  have hDD : D ≤ Dbig := by linarith only [hmargin]
  obtain ⟨wsmall,hwsmall⟩ : ∃ ws : StandardCap.CanonicalStaticInsertionWitness d A hA D m ζ,
      ws = w.restrictWindow hD hDD := ⟨_,rfl⟩
  obtain ⟨hJ,hupperRaw,hmetricRaw,hscalar⟩ := prepared_window_restriction_bounds_S54
    (E := E) (H := H0) (M := M) (N := (H.stage first).Carrier) (I := I)
    (g := g) (x₀ := x₀) (δ := δ) (k := k) (d := d) (A := A) (hA := hA) (m := m) (ζ := ζ)
    hD hmargin w
    (hζ.trans hεhalf) (H.initialMetric first) Jbig hJbig hzero
    (fun x hx => (le_abs_self _).trans (hbound (E := E) (H := H0) (M := M) (N := (H.stage first).Carrier) (I := I)
      (g := g) (x₀ := x₀) (δ := δ) (k := k) (d := d) (A := A) (hA := hA) (D := Dbig)
      (m := m) (ε := ζ) w (hζ.trans hεhalf) (by omega)
      (H.initialMetric first) Jbig hJbig q hq hzero x hx))
  have hupper : ∀ x : standardCapWindow D, ∀ v : TangentSpace ThreeModel x,
      wsmall.windowMetric.inner x v v ≤ (3/2:ℝ)*StandardCap.metric.inner x.val v v := by
    rw [hwsmall]
    exact hupperRaw
  have hmetric : ∀ x (v t : TangentSpace ThreeModel x), wsmall.windowMetric.inner x v t =
      q*(H.initialMetric first).inner (J x)
        (mfderiv ThreeModel ThreeModel J x v) (mfderiv ThreeModel ThreeModel J x t) := by
    rw [hwsmall]
    exact hmetricRaw
  obtain ⟨Ξ, hΞs, hbirth, hpoint, hΞ, gflow, S, hslabs, hlast, hS, hSzero,
    hmetricS, hgram, halljets, hterminal, hcontrol, hcurv⟩ := hjets (E := E) (H := H0) (M := M) (I := I)
    (g := g) (x₀ := x₀) (δ := δ) (k := k) (d := d) (A := A) (hA := hA)
    (m := m) (ζ := ζ) wsmall hm hζ hupper H first last hle s G L hinit J hJ
    q q₀ a₀ hq hq₀ hq₀Q haq hmetric hscalar parameters records hfixed hlower hδ hderiv hfinal
    htime z x Atrace hanchor
  refine ⟨Ξ, hΞs, hbirth, hpoint, hΞ, gflow, S, hslabs, hlast, hS, ?_,
    hmetricS, hgram, halljets, hterminal, hcontrol, hcurv⟩
  rw [hSzero, hwsmall, StandardCap.CanonicalStaticInsertionWitness.restrictWindow_windowMetric]

end GC.LongTime.Ch12
