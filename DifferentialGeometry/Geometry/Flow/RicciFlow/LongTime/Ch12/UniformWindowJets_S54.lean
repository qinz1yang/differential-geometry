import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.LocalWindowCurvatureHorizon

/-!
# CH12-S54, group 1: window jets with a constant independent of the radius

`StandardCap.exists_uniform_window_flow_curvature_derivative_bound_of_local_curvature_bounded_horizon`
centres the Shi local derivative estimate at the tip of the window, so its constant depends on the
radius `ρ`.  Here the estimate is re-centred at the evaluation point with a fixed radius.
-/

set_option autoImplicit false

noncomputable section

open Set Function Bundle Manifold DifferentialGeometry
open DifferentialGeometry.Geometry.Metric DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Neck DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.Tensor0SBundle
open scoped Manifold ContDiff Topology ENNReal NNReal

namespace GC.LongTime.Ch12

section Ball

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [Fact (Module.finrank ℝ E = 3)]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {g : SmoothRiemannianMetric I M} {x₀ : M} {δ : ℝ} {k : ℕ}
  {d : normalizedDatum g x₀ δ k} {A : ℝ} {hA : 0 < A} {D : ℝ}
  {m : ℕ} {ε : ℝ}

/-- `exists_window_intrinsic_ball_control` at an arbitrary centre `c` (not only the tip). -/
theorem window_intrinsic_ball_control_at_S54
    (w : StandardCap.CanonicalStaticInsertionWitness d A hA D m ε)
    (heps : ε ≤ 1 / 2) {ρ : ℝ} (hρ : 0 < ρ) (c : standardCapWindow D)
    (hc : ‖c.val‖ + ρ < D) :
    IsCompact {y : standardCapWindow D |
      riemannianEDistOf w.windowMetric c y ≤ ENNReal.ofReal (ρ / 4)} ∧
      {y : standardCapWindow D |
        riemannianEDistOf w.windowMetric c y ≤ ENNReal.ofReal (ρ / 4)} ⊆
        {y : standardCapWindow D | ‖y.val‖ ≤ ‖c.val‖ + ρ} := by
  have hid : IsLocalDiffeomorph ThreeModel ThreeModel ∞ (@id (standardCapWindow D)) :=
    (Diffeomorph.refl ThreeModel (standardCapWindow D) ∞).isLocalDiffeomorph
  have hnorm (x : standardCapWindow D)
      (hx : x.val ∈ riemannianClosedBallOf StandardCap.metric c.val ρ) :
      ‖x.val‖ ≤ ‖c.val‖ + ρ := by
    have h1 := StandardCap.radial_difference_le_edist c.val x.val
    have h2 : riemannianEDistOf StandardCap.metric c.val x.val ≤ ENNReal.ofReal ρ := hx
    have h3 := (ENNReal.ofReal_le_ofReal_iff hρ.le).mp (h1.trans h2)
    have h4 := (abs_le.mp h3).2
    linarith
  have hcpt : IsCompact (riemannianClosedBallOf StandardCap.metric c.val ρ) :=
    StandardCap.isCompact_metric_closedBall c.val ρ.toNNReal
  have hsource : riemannianClosedBallOf StandardCap.metric c.val ρ ⊆ standardCapWindow D := by
    intro x hx
    have hh := hnorm ⟨x, by
      change ‖x‖ < D + 1
      have hx' : ‖x‖ ≤ ‖c.val‖ + ρ := by
        have h1 := StandardCap.radial_difference_le_edist c.val x
        have h2 : riemannianEDistOf StandardCap.metric c.val x ≤ ENNReal.ofReal ρ := hx
        have h3 := (ENNReal.ofReal_le_ofReal_iff hρ.le).mp (h1.trans h2)
        have h4 := (abs_le.mp h3).2
        linarith
      linarith⟩ hx
    change ‖x‖ < D + 1
    linarith
  have hlow (x : standardCapWindow D)
      (hx : x.val ∈ riemannianClosedBallOf StandardCap.metric c.val ρ)
      (v : TangentSpace ThreeModel x) :
      StandardCap.metric.inner x.val v v ≤ (2 : ℝ)^2 * w.windowMetric.inner (id x)
        (mfderiv ThreeModel ThreeModel id x v) (mfderiv ThreeModel ThreeModel id x v) := by
    rw [mfderiv_id]
    change StandardCap.metric.inner x.val v v ≤ 2^2 * w.windowMetric.inner x v v
    have hb := (w.window_inner_bounds heps ((hnorm x hx).trans_lt hc) v).1
    rw [standardCapMetric_eq_metric, SmoothRiemannianMetric.restrictOpen_inner] at hb
    have hn := metric_inner_self_nonneg w.windowMetric x v
    nlinarith
  have hcap := ball_subset_image_of_metric_lower_on_opens w.windowMetric StandardCap.metric
    (standardCapWindow D) id hid injective_id c hρ (by norm_num : (0 : ℝ) < 2)
    hcpt hsource hlow
  refine ⟨?_, ?_⟩
  · exact isCompact_riemannianClosedBallOf_of_metric_lower_on_opens w.windowMetric
      StandardCap.metric (standardCapWindow D) id hid injective_id c hρ
      (by norm_num : (0 : ℝ) < 2) (by linarith : ρ / 4 < ρ / 2) hcpt hsource hlow
  · intro y hy
    have hy' : y ∈ riemannianBallOf w.windowMetric (id c) (ρ / 2) :=
      hy.trans_lt ((ENNReal.ofReal_lt_ofReal_iff (by positivity : 0 < ρ / 2)).mpr
        (by linarith))
    obtain ⟨z, hz, hzy⟩ := hcap hy'
    change z = y at hzy
    subst y
    exact hnorm z hz

end Ball

section Jets

private local instance (V : TopologicalSpace.Opens ThreeSpace) : SigmaCompactSpace V :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen ThreeModel V.isOpen)

private local instance : NeZero (Module.finrank ℝ ThreeSpace) := ⟨by simp⟩

private theorem initial_curvature_norm_le_of_metric_bound_S54
    {D : ℝ} {J : RealTimeInterval}
    (L : SolutionOn (I := ThreeModel) (M := standardCapWindow D) J)
    (g₀ : SmoothRiemannianMetric ThreeModel (standardCapWindow D))
    (hzero : L.base.metric 0 = g₀) (j : ℕ) (x : standardCapWindow D) {C : ℝ}
    (hb : Real.sqrt (normSq0S g₀ x (4 + j) (iterCov g₀ 4 (metricRm04 g₀) j x)) ≤ C) :
    nablaKRm04NormSqIntrinsic L j 0 x ≤ C ^ 2 := by
  rw [← curvNormSq_eq, hzero]
  unfold curvDerivNormSq
  rw [curvCovDeriv_normSq_eq]
  exact (Real.sqrt_le_iff).mp hb |>.2

/-- Local (re-centred) window jets: the constant depends only on `(N, T, K)`; neither on the radius
of the region where the curvature bound is available nor on the window size `D`. -/
theorem window_flow_curvature_derivative_bound_local_S54 (N : ℕ) (T K : ℝ) :
    ∃ B : ℝ, 1 ≤ B ∧
      ∀ {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
        [FiniteDimensional ℝ E] [Fact (Module.finrank ℝ E = 3)]
        [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
        [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
        {g : SmoothRiemannianMetric I M} {x₀ : M} {δ : ℝ} {k : ℕ}
        {d : normalizedDatum g x₀ δ k} {A : ℝ} {hA : 0 < A} {D : ℝ}
        {m : ℕ} {ζ : ℝ} (w : StandardCap.CanonicalStaticInsertionWitness d A hA D m ζ),
      ζ ≤ 1/2 → N+2 ≤ m →
      ∀ (J : RealTimeInterval) (θ : ℝ), 0 < θ → θ ≤ T →
        Icc 0 θ ⊆ J.carrier → Ioo 0 θ ⊆ J.regular →
        ∀ L : SolutionOn (I := ThreeModel) (M := standardCapWindow D) J,
        IsSolutionOn L → L.base.metric 0 = w.windowMetric →
        (∀ (p : standardCapWindow D) (i j : Fin (Module.finrank ℝ ThreeSpace)),
          ContMDiffOn (𝓘(ℝ, ℝ).prod ThreeModel) 𝓘(ℝ, ℝ) ∞
            (fun q : ℝ × standardCapWindow D =>
              DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (L.base.metric q.1) p q.2 i j)
            (Icc 0 θ ×ˢ (trivializationAt ThreeSpace (TangentSpace ThreeModel) p).baseSet)) →
        ∀ x : standardCapWindow D, ‖x.val‖ + 4 < D →
        (∀ t ∈ Icc 0 θ, ∀ y : standardCapWindow D, ‖y.val‖ ≤ ‖x.val‖ + 4 →
          nablaKRm04NormSqIntrinsic L 0 t y ≤ K) →
        ∀ j ≤ N, ∀ t ∈ Icc 0 θ, nablaKRm04NormSqIntrinsic L j t x ≤ B := by
  classical
  choose A hA hinit using StandardCap.exists_uniform_window_curvature_derivative_bounds
  obtain ⟨B,hB,hbound⟩ :=
    exists_uniform_initial_curvature_derivative_bound_on_compact_ball_of_open_regular_interval
    (I := ThreeModel) N T (4/4) K (by norm_num) (fun j => (A j)^2)
    (fun _ _ _ => sq_nonneg _)
  refine ⟨B,hB,?_⟩
  intro E H M _ _ _ _ _ I _ _ _ _ _ g x₀ δ k d A₀ hA₀ D m ζ w hζ hm
    J θ hθ hθT hslab hreg L hL hzero hgram x hxD hcurv j hj t ht
  obtain ⟨hcompact, hsub⟩ := window_intrinsic_ball_control_at_S54 w hζ (ρ := 4)
    (by norm_num) x hxD
  have hcompactL : IsCompact {y : standardCapWindow D |
      riemannianEDistOf (L.base.metric 0) x y ≤ ENNReal.ofReal (4/4)} := by
    rwa [hzero]
  have houter (y : standardCapWindow D)
      (hy : riemannianEDistOf (L.base.metric 0) x y ≤ ENNReal.ofReal (4/4)) :
      ‖y.val‖ ≤ ‖x.val‖ + 4 := by
    rw [hzero] at hy
    exact hsub hy
  apply hbound (standardCapWindow D) J L θ hθ hθT hL hslab hreg hgram x hcompactL
    (fun s hs y hy => hcurv s hs y (houter y hy))
    (fun k hk hkN y hy => initial_curvature_norm_le_of_metric_bound_S54 L w.windowMetric
      hzero k y (hinit k w hζ (by omega) y ((houter y hy).trans_lt hxD))) j hj t ht x
  rw [riemannianEDistOf_self]
  exact zero_le
end Jets

end GC.LongTime.Ch12
