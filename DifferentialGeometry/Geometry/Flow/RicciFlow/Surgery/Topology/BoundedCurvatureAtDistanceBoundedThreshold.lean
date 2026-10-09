import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.BoundedCurvatureAtDistance
import DifferentialGeometry.Geometry.Metric.Distance.Ball

set_option autoImplicit false

noncomputable section

open Set Filter
open DifferentialGeometry.CheegerGromovCompactness DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Integral.Measure
open scoped Manifold ContDiff Topology NNReal ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

universe u

attribute [local instance] PointedRiemannianManifold.topology PointedRiemannianManifold.charted
  PointedRiemannianManifold.smooth PointedRiemannianManifold.t2
  PointedRiemannianManifold.sigmaCompact PointedRiemannianManifold.t2TangentBundle

private local instance {P : OrientedThreeStage.{u}} {a s : ℝ} (G : P.IncomingSlab a s) :
    SigmaCompactSpace G.terminalRegularOpen :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen ThreeModel G.terminalRegularOpen.isOpen)

private local instance pointedLimitRegular (L : PointedRiemannianManifold.{u, 0, 0} ThreeModel) :
    RegularSpace L.M := by
  let _ : LocallyCompactSpace L.M := ChartedSpace.locallyCompactSpace ThreeSpace L.M
  infer_instance

private theorem eventually_scalar_le_on_inner_ball_of_pointed_convergence
    {X : PointedRiemannianSeq.{u, 0, 0} ThreeModel}
    {L : PointedRiemannianManifold.{u, 0, 0} ThreeModel} {f : ℕ → ℕ}
    (F : PointedRiemannianConvergenceMaps X L f) (M : MetricConvergenceData F)
    (hcanonical : ∀ n, M.domain n = CanonicalMetricCompactness.canonicalSourceData F n)
    {rho : ℝ} (hcompact : ∀ R : ℝ, 0 ≤ R → R < rho →
      IsCompact (riemannianClosedBallOf L.metric L.basepoint R))
    {R : ℝ} (hR : 0 < R) (hRrho : R < rho) :
    ∃ B : ℝ, ∀ᶠ n in atTop, ∀ y : (X.obj (f n)).M,
      riemannianEDistOf (X.obj (f n)).metric (X.obj (f n)).basepoint y < ENNReal.ofReal R →
        metricScalarAt (X.obj (f n)).metric y ≤ B := by
  let R' := (R + rho) / 2
  let factor := (R + R') / (2 * R)
  have hRR' : R < R' := by dsimp only [R']; linarith
  have hfactor : 1 < factor := by
    dsimp only [factor]
    rw [lt_div_iff₀ (by positivity)]
    linarith
  have hbuffer : factor * R < R' := by
    have heq : factor * R = (R + R') / 2 := by dsimp only [factor]; field_simp
    rw [heq]
    linarith
  have hK := hcompact R' (by dsimp only [R']; linarith) (by dsimp only [R']; linarith)
  have hconv : metricSourceConvergesOn F (CanonicalMetricCompactness.canonicalSourceData F)
      (riemannianClosedBallOf L.metric L.basepoint R') 0 := by
    have heq : M.domain = CanonicalMetricCompactness.canonicalSourceData F := funext hcanonical
    rw [← heq]
    exact M.converges _ hK 0
  obtain ⟨B, _, hB⟩ := Perelman.KappaSolutions.exists_pointed_scalar_bound_on_compact M
    hcanonical _ hK
  refine ⟨B, ?_⟩
  filter_upwards [pointed_metric_eventually_inverse_ball_capture L.basepoint hR.le hfactor
    hbuffer hK hconv, hB] with n hn hb
  intro y hy
  have hy' : y ∈ riemannianClosedBallOf (X.obj (f n)).metric (F.map n L.basepoint) R := by
    change y ∈ riemannianClosedBallOf (X.obj (f n)).metric ((F.partialDiffeomorph n) L.basepoint) R
    rw [F.basepoint_map]
    exact hy.le
  obtain ⟨_, _, hin, heq⟩ := hn.2 y hy'
  have hmem : (F.partialDiffeomorph n).symm y ∈ riemannianClosedBallOf L.metric L.basepoint R' :=
    riemannianClosedBallOf_mono _ _ hbuffer.le hin
  have h := hb.2 _ hmem
  rw [heq] at h
  exact (le_abs_self _).trans h

private theorem scaleMetric_mul_eq {M : Type*} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
    [IsManifold ThreeModel ∞ M] (g : SmoothRiemannianMetric ThreeModel M) {a b c : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : c = a * b) :
    scaleMetric c hc g = scaleMetric a ha (scaleMetric b hb g) := by
  apply SmoothRiemannianMetric.ext_inner
  intro z v w
  simp only [scaleMetric_inner]
  rw [habc]
  ring

private theorem isCompact_closedBall_of_lt_dist_puncture {W : Type*} [MetricSpace W]
    {q : UniformSpace.Completion W} {d : ℝ} (hK : IsCompact (Metric.closedBall q d))
    (hcover : Metric.closedBall q d ⊆
      insert q (range (fun z : W => (z : UniformSpace.Completion W))))
    (x : W) {r : ℝ} (hr : r < dist (x : UniformSpace.Completion W) q)
    (hd : dist (x : UniformSpace.Completion W) q + r ≤ d) :
    IsCompact (Metric.closedBall x r) := by
  let K := Metric.closedBall (x : UniformSpace.Completion W) r
  have hKd : K ⊆ Metric.closedBall q d := by
    intro z hz
    have hz' : dist z (x : UniformSpace.Completion W) ≤ r := hz
    change dist z q ≤ d
    linarith [dist_triangle z (x : UniformSpace.Completion W) q]
  have hKc : IsCompact K := hK.of_isClosed_subset Metric.isClosed_closedBall hKd
  have hKr : K ⊆ range (fun z : W => (z : UniformSpace.Completion W)) := by
    intro z hz
    rcases hcover (hKd hz) with hzq | hzr
    · exfalso
      have hz' : dist z (x : UniformSpace.Completion W) ≤ r := hz
      rw [hzq, dist_comm] at hz'
      linarith
    · exact hzr
  have hpre : (fun z : W => (z : UniformSpace.Completion W)) ⁻¹' K = Metric.closedBall x r := by
    ext z
    simp only [K, mem_preimage, Metric.mem_closedBall, UniformSpace.Completion.dist_eq]
  rw [← hpre]
  exact ((UniformSpace.Completion.isUniformInducing_coe W).isInducing.isCompact_preimage_iff
    hKr).mpr hKc

private theorem exists_riemannianEDistOf_lt_of_mem_Icc_scalar {M : Type*} [TopologicalSpace M]
    [ChartedSpace ThreeSpace M] [IsManifold ThreeModel ∞ M]
    (g : SmoothRiemannianMetric ThreeModel M) {f : M → ℝ} (hf : Continuous f) {y z : M}
    {r : ℝ} (hyz : riemannianEDistOf g y z < ENNReal.ofReal r) {c : ℝ}
    (hc : c ∈ Icc (f y) (f z)) :
    ∃ x, f x = c ∧ riemannianEDistOf g x z < ENNReal.ofReal r := by
  have hr : 0 < r := ENNReal.ofReal_pos.mp (lt_of_le_of_lt bot_le hyz)
  have hconn := (isPathConnected_riemannianBallOf g z hr).isConnected.isPreconnected
  have hy : y ∈ riemannianBallOf g z r := by
    change riemannianEDistOf g z y < _
    rwa [riemannianEDistOf_comm]
  have hz : z ∈ riemannianBallOf g z r := by
    change riemannianEDistOf g z z < _
    rw [riemannianEDistOf_self]
    exact ENNReal.ofReal_pos.mpr hr
  obtain ⟨x, hx, hfx⟩ := hconn.intermediate_value hy hz hf.continuousOn hc
  refine ⟨x, hfx, ?_⟩
  have hx' : riemannianEDistOf g z x < ENNReal.ofReal r := hx
  rwa [riemannianEDistOf_comm]

theorem exists_isometric_ray_with_spatialNecks_of_bounded_threshold
    (P : ℕ → OrientedThreeStage.{u}) (a s : ℕ → ℝ) (A : ∀ i, (P i).ClosedSlab (a i) (s i))
    (Ctime Cgrad : ℝ≥0) (q : ℕ → ℝ)
    (htime : ∀ i y, ∀ t ∈ Ioo (a i) (s i), q i < (A i).flow.scalar t y →
      |derivWithin (fun v => (A i).flow.scalar v y) (Iic t) t| ≤
        Ctime * (A i).flow.scalar t y ^ 2)
    (hgradient : ∀ i y, ∀ t ∈ Ioo (a i) (s i), q i < (A i).flow.scalar t y →
      ∀ v : TangentSpace ThreeModel y,
        |Perelman.CanonicalNeighborhood.scalarDifferential
            ((A i).restrictIncoming le_rfl (A i).lt le_rfl).flow t y v| ≤
          Cgrad * (A i).flow.scalar t y * Real.sqrt ((A i).flow.scalar t y) *
            Real.sqrt (((A i).flow.base.metric t).inner y v v))
    (x : ∀ i, ((A i).restrictIncoming le_rfl (A i).lt le_rfl).terminalRegularOpen)
    (hQ : ∀ i, 1 ≤ (A i).flow.scalar (s i) (x i).val)
    (hqQ : ∀ i, q i ≤ (A i).flow.scalar (s i) (x i).val)
    {eps C1 C2 alpha : ℝ} (halpha : 0 < alpha) (halpha1 : alpha < 1 / 11)
    (heps : 13000 * (13000 * eps) ≤
      min (neckModelTolerance (alpha / 26000)) ((alpha / 26000) / 64))
    (hW : ∀ i y, q i < (A i).flow.scalar (s i) y →
      ∃ W : SpatialCanonicalWitness ((A i).flow.base.metric (s i)) eps C1 C2 y,
        W.capTubeHasNeckChart eps)
    {rho : ℝ} (hrho : 0 < rho) (f : ℕ → ℕ) (hf : StrictMono f)
    (r : ℕ → ℝ) (hr : ∀ n, 0 < r n) (hrlim : Tendsto r atTop (𝓝 rho))
    (Pl : PointedRiemannianManifold.{u, 0, 0} ThreeModel)
    (F : PointedRiemannianConvergenceMaps
      ({ obj := fun i =>
          { M := ((A i).restrictIncoming le_rfl (A i).lt le_rfl).terminalRegularOpen
            basepoint := x i
            metric := scaleMetric ((A i).flow.scalar (s i) (x i).val)
              (zero_lt_one.trans_le (hQ i)) ((A i).endpointTerminalLimitMetric (P i)).metric } } :
        PointedRiemannianSeq.{u, 0, 0} ThreeModel) Pl f)
    (M : MetricConvergenceData F)
    (hcanonical : ∀ n, M.domain n = CanonicalMetricCompactness.canonicalSourceData F n)
    (hradial : ∀ z : Pl.M, riemannianEDistOf Pl.metric Pl.basepoint z < ENNReal.ofReal rho)
    (hcompact : ∀ R : ℝ, 0 ≤ R → R < rho →
      IsCompact (riemannianClosedBallOf Pl.metric Pl.basepoint R))
    (hcapture : ∀ n, riemannianClosedBallOf
      (scaleMetric ((A (f n)).flow.scalar (s (f n)) (x (f n)).val)
        (zero_lt_one.trans_le (hQ (f n))) ((A (f n)).endpointTerminalLimitMetric (P (f n))).metric)
      (x (f n)) (r n) ⊆ F.target n)
    (hlower : ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, ∀ y ∈ F.source n, ∀ v : TangentSpace ThreeModel y,
      (1 - ε) * Pl.metric.inner y v v ≤
        (scaleMetric ((A (f n)).flow.scalar (s (f n)) (x (f n)).val)
          (zero_lt_one.trans_le (hQ (f n)))
          ((A (f n)).endpointTerminalLimitMetric (P (f n))).metric).inner (F.map n y)
          (mfderiv ThreeModel ThreeModel (F.map n) y v)
          (mfderiv ThreeModel ThreeModel (F.map n) y v))
    (z : ∀ n, ((A (f n)).restrictIncoming le_rfl (A (f n)).lt le_rfl).terminalRegularOpen)
    (hfinite : ∀ n, riemannianEDistOf
      (scaleMetric ((A (f n)).flow.scalar (s (f n)) (x (f n)).val)
        (zero_lt_one.trans_le (hQ (f n))) ((A (f n)).endpointTerminalLimitMetric (P (f n))).metric)
      (x (f n)) (z n) ≠ ⊤)
    (hdist : Tendsto (fun n => (riemannianEDistOf
      (scaleMetric ((A (f n)).flow.scalar (s (f n)) (x (f n)).val)
        (zero_lt_one.trans_le (hQ (f n))) ((A (f n)).endpointTerminalLimitMetric (P (f n))).metric)
      (x (f n)) (z n)).toReal) atTop (𝓝 rho))
    (hhigh : Tendsto (fun n => metricScalarAt
      ((A (f n)).endpointTerminalLimitMetric (P (f n))).metric (z n) /
        (A (f n)).flow.scalar (s (f n)) (x (f n)).val) atTop atTop) :
    let _ : EMetricSpace Pl.M := Pl.emetricSpace
    ∃ g : C(Ico 0 rho, Pl.M), Isometry g ∧ g ⟨0, le_rfl, hrho⟩ = Pl.basepoint ∧
      Tendsto (fun t => metricScalarAt Pl.metric (g t))
        (comap (Subtype.val : Ico 0 rho → ℝ) (𝓝 rho)) atTop ∧
      ∀ᶠ t : Ico 0 rho in comap (Subtype.val : Ico 0 rho → ℝ) (𝓝 rho),
        Nonempty (SpatialNeck Pl.metric alpha (g t)) := by
  intro _
  let G := fun i => (A i).restrictIncoming le_rfl (A i).lt le_rfl
  let L := fun i => (A i).endpointTerminalLimitMetric (P i)
  let Q := fun i => (A i).flow.scalar (s i) (x i).val
  have hQpos : ∀ i, 0 < Q i := fun i => zero_lt_one.trans_le (hQ i)
  have hLscalar (i : ℕ) (y : (G i).terminalRegularOpen) :
      metricScalarAt (L i).metric y = (A i).flow.scalar (s i) y.val :=
    metricScalarAt_restrictOpen _ _ _
  have hXscalar (i : ℕ) (y : (G i).terminalRegularOpen) :
      metricScalarAt (scaleMetric (Q i) (hQpos i) (L i).metric) y =
        metricScalarAt (L i).metric y / Q i := by
    rw [metricScalarAt_scaleMetric, inv_mul_eq_div]
  have hinner : ∀ R : ℝ, 0 < R → R < rho → ∃ B : ℝ,
      ∀ᶠ n in atTop, ∀ y : (G (f n)).terminalRegularOpen,
        riemannianEDistOf (scaleMetric (Q (f n)) (hQpos (f n)) (L (f n)).metric)
          (x (f n)) y < ENNReal.ofReal R →
            metricScalarAt (L (f n)).metric y / Q (f n) ≤ B := by
    intro R hR hRrho
    obtain ⟨B, hB⟩ :=
      eventually_scalar_le_on_inner_ball_of_pointed_convergence F M hcanonical hcompact hR hRrho
    refine ⟨B, hB.mono fun n hn y hy => ?_⟩
    rw [← hXscalar]
    exact hn y hy
  obtain ⟨κ₁, hκ₁, A', ell, y, γ, _, hAlim, helllim, _, hy, _, _, hends, _, _, _, hmin,
      φ, g, hφ, hg, hgbase, hconv, _, hscalar, _, _, hblowup⟩ :=
    exists_isometric_terminal_scalar_blowup_curve_of_scalar_escape P a s G L Q hQpos q 1
      (Eventually.of_forall fun i => by simpa only [one_mul] using hqQ i) Cgrad hgradient x Pl
      f hf F M hcanonical hrho r hr hrlim
      (fun n y hy => hcapture n (show riemannianEDistOf _ _ y ≤ _ from le_of_lt hy)) hlower
      hcompact hradial (fun _ => Ctime)
      (fun i y t ht hy => htime i y t ht ((hqQ i).trans_lt hy))
      (fun i => (hLscalar i (x i)).le) z hfinite hdist hhigh hinner
  refine ⟨g, hg, hgbase, hblowup, ?_⟩
  have hsub : StrictMono (fun n => f (κ₁ (φ n))) := hf.comp (hκ₁.comp hφ)
  have hpos : ∀ᶠ t : Ico 0 rho in comap (Subtype.val : Ico 0 rho → ℝ) (𝓝 rho), 0 < (t : ℝ) :=
    (tendsto_comap : Tendsto (Subtype.val : Ico 0 rho → ℝ) _ (𝓝 rho)).eventually
      (eventually_gt_nhds hrho)
  filter_upwards [hblowup.eventually_gt_atTop (max 2 (C2 + 1)), hpos] with τ hτ hτpos
  let F2 := (F.compSubseq κ₁ hκ₁).compSubseq φ hφ
  let M2 := (M.compSubseq κ₁ hκ₁).compSubseq φ hφ
  have hcanonical2 (n : ℕ) :
      M2.domain n = CanonicalMetricCompactness.canonicalSourceData F2 n := by
    change ((M.domain (κ₁ (φ n))).compSubseq κ₁ hκ₁ (φ n)).compSubseq φ hφ n = _
    rw [hcanonical (κ₁ (φ n))]
    rfl
  have hRτ : Tendsto (fun n => metricScalarAt (L (f (κ₁ (φ n)))).metric (γ (φ n) τ) /
      Q (f (κ₁ (φ n)))) atTop (𝓝 (metricScalarAt Pl.metric (g τ))) := hscalar τ
  have hellτ : ∀ᶠ n in atTop, (τ : ℝ) < ell (φ n) :=
    (helllim.comp hφ.tendsto_atTop).eventually (eventually_gt_nhds τ.property.2)
  have hbig := hRτ.eventually (eventually_gt_nhds hτ)
  have hAbig := (hAlim.comp hφ.tendsto_atTop).eventually_gt_atTop
    (C2 * (metricScalarAt Pl.metric (g τ) + 1))
  have hRτup := hRτ.eventually (eventually_lt_nhds (lt_add_one (metricScalarAt Pl.metric (g τ))))
  apply nonempty_spatial_neck_at_limit_of_endpoint_blowup M2 hcanonical2 halpha halpha1
    (fun n => γ (φ n) τ) (fun n => γ (φ n) (ell (φ n))) (g τ) τ.property.1 τ.property.2
    hcompact ((le_max_left _ _).trans_lt hτ)
    ((hconv {τ} isCompact_singleton).tendsto_at (mem_singleton τ)) ?_ (fun n => ell (φ n))
    (helllim.comp hφ.tendsto_atTop) ?_ ?_ ?_
  · refine (hAlim.comp hφ.tendsto_atTop).congr fun n => ?_
    change A' (φ n) = metricScalarAt (scaleMetric (Q (f (κ₁ (φ n)))) (hQpos _)
      (L (f (κ₁ (φ n)))).metric) (γ (φ n) (ell (φ n)))
    rw [hXscalar, (hends (φ n)).2, hy]
  · filter_upwards [hellτ] with n hn
    change riemannianEDistOf (scaleMetric (Q (f (κ₁ (φ n)))) (hQpos _)
      (L (f (κ₁ (φ n)))).metric) (γ (φ n) τ) (γ (φ n) (ell (φ n))) ≤ _
    rw [hmin (φ n) τ ⟨τ.property.1, hn.le⟩ (ell (φ n)) ⟨τ.property.1.trans hn.le, le_rfl⟩,
      abs_sub_comm, abs_of_pos (sub_pos.mpr hn)]
  · filter_upwards [hellτ] with n hn
    change riemannianEDistOf (scaleMetric (Q (f (κ₁ (φ n)))) (hQpos _)
      (L (f (κ₁ (φ n)))).metric) (x (f (κ₁ (φ n)))) _ ≤ _
    rw [← (hends (φ n)).1, hmin (φ n) 0 ⟨le_rfl, τ.property.1.trans hn.le⟩ τ
      ⟨τ.property.1, hn.le⟩, zero_sub, abs_neg, abs_of_nonneg τ.property.1]
  · filter_upwards [hellτ, hbig, hAbig, hRτup] with n hn hnbig hnA hnup
    have hQi : 0 < (A (f (κ₁ (φ n)))).flow.scalar (s (f (κ₁ (φ n)))) (x (f (κ₁ (φ n)))).val :=
      hQpos _
    have hRt : metricScalarAt (L (f (κ₁ (φ n)))).metric (γ (φ n) τ) =
        (A (f (κ₁ (φ n)))).flow.scalar (s (f (κ₁ (φ n)))) (γ (φ n) τ).val := hLscalar _ _
    have hRe : metricScalarAt (L (f (κ₁ (φ n)))).metric (y (φ n)) =
        (A (f (κ₁ (φ n)))).flow.scalar (s (f (κ₁ (φ n)))) (y (φ n)).val := hLscalar _ _
    have h1 : max 2 (C2 + 1) *
        (A (f (κ₁ (φ n)))).flow.scalar (s (f (κ₁ (φ n)))) (x (f (κ₁ (φ n)))).val <
        (A (f (κ₁ (φ n)))).flow.scalar (s (f (κ₁ (φ n)))) (γ (φ n) τ).val := by
      rw [← hRt]
      exact (lt_div_iff₀ hQi).mp hnbig
    have h2 : q (f (κ₁ (φ n))) ≤
        (A (f (κ₁ (φ n)))).flow.scalar (s (f (κ₁ (φ n)))) (x (f (κ₁ (φ n)))).val := hqQ _
    have h3 : (A (f (κ₁ (φ n)))).flow.scalar (s (f (κ₁ (φ n)))) (γ (φ n) τ).val <
        (metricScalarAt Pl.metric (g τ) + 1) *
          (A (f (κ₁ (φ n)))).flow.scalar (s (f (κ₁ (φ n)))) (x (f (κ₁ (φ n)))).val := by
      rw [← hRt]
      exact (div_lt_iff₀ hQi).mp hnup
    have h4 : C2 * (metricScalarAt Pl.metric (g τ) + 1) *
        (A (f (κ₁ (φ n)))).flow.scalar (s (f (κ₁ (φ n)))) (x (f (κ₁ (φ n)))).val <
        (A (f (κ₁ (φ n)))).flow.scalar (s (f (κ₁ (φ n)))) (y (φ n)).val := by
      rw [← hRe]
      have hh := hy (φ n)
      rw [div_eq_iff hQi.ne'] at hh
      rw [hh]
      exact mul_lt_mul_of_pos_right hnA hQi
    have hm2 := le_max_left (2 : ℝ) (C2 + 1)
    have hmC := le_max_right (2 : ℝ) (C2 + 1)
    have hq : q (f (κ₁ (φ n))) <
        (A (f (κ₁ (φ n)))).flow.scalar (s (f (κ₁ (φ n)))) (γ (φ n) τ).val := by
      nlinarith
    obtain ⟨W0, _⟩ := hW _ _ hq
    have hC2pos : 0 ≤ C2 := zero_le_one.trans W0.one_le_comparison_constant
    have hleft : C2 * (A (f (κ₁ (φ n)))).flow.scalar (s (f (κ₁ (φ n)))) (γ (φ n) 0).val <
        (A (f (κ₁ (φ n)))).flow.scalar (s (f (κ₁ (φ n)))) (γ (φ n) τ).val := by
      rw [(hends (φ n)).1]
      nlinarith
    have hright : C2 * (A (f (κ₁ (φ n)))).flow.scalar (s (f (κ₁ (φ n)))) (γ (φ n) τ).val <
        (A (f (κ₁ (φ n)))).flow.scalar (s (f (κ₁ (φ n)))) (γ (φ n) (ell (φ n))).val := by
      rw [(hends (φ n)).2]
      nlinarith
    have hmin' : ∀ a ∈ Icc 0 (ell (φ n)), ∀ b ∈ Icc 0 (ell (φ n)), riemannianEDistOf
        (scaleMetric ((A (f (κ₁ (φ n)))).flow.scalar (s (f (κ₁ (φ n)))) (x (f (κ₁ (φ n)))).val)
          hQi ((A (f (κ₁ (φ n)))).endpointTerminalLimitMetric (P (f (κ₁ (φ n))))).metric)
        (γ (φ n) a) (γ (φ n) b) = ENNReal.ofReal |a - b| := hmin (φ n)
    exact (A (f (κ₁ (φ n)))).nonempty_scaled_spatialNeck_of_minimizing_segment hQi
      (lt_of_le_of_lt (min_le_right _ _) (by linarith)) heps (hW _) hτpos hn hmin' hq hleft
      hright

theorem RetainedCoreHistory.exists_local_backward_limit_at_final_slab_end_of_bounded_threshold
    (H : ℕ → RetainedCoreHistory.{u}) (time : ℕ → ℝ)
    (A : ∀ i, ((H i).stage (Fin.last (H i).eventCount)).ClosedSlab
      ((H i).time (Fin.last (H i).eventCount)) (time i))
    (hinit : ∀ i, (A i).flow.base.metric ((H i).time (Fin.last (H i).eventCount)) =
      (H i).initialMetric (Fin.last (H i).eventCount))
    (hs : ∀ i, (H i).horizon < time i) (Ctime : ℝ≥0) (q : ℕ → ℝ) (hq : ∀ i, 0 < q i)
    (hderiv : ∀ i (j : Fin (H i).eventCount) (y : ((H i).stage j.castSucc).Carrier),
      ∀ t ∈ Ioo ((H i).time j.castSucc) ((H i).time j.succ),
        q i < ((H i).toHistory.event j).incoming.flow.scalar t y →
        |derivWithin (fun v => ((H i).toHistory.event j).incoming.flow.scalar v y) (Iic t) t| ≤
          Ctime * ((H i).toHistory.event j).incoming.flow.scalar t y ^ 2)
    (hfinal : ∀ i y, ∀ t ∈ Ioo ((H i).time (Fin.last (H i).eventCount)) (time i),
      q i < (A i).flow.scalar t y →
      |derivWithin (fun v => (A i).flow.scalar v y) (Iic t) t| ≤
        Ctime * (A i).flow.scalar t y ^ 2)
    (x : ∀ i, ((A i).restrictIncoming le_rfl (A i).lt le_rfl).terminalRegularOpen)
    (hQ : ∀ i, 1 ≤ (A i).flow.scalar (time i) (x i).val)
    (hqQ : ∀ i, q i ≤ (A i).flow.scalar (time i) (x i).val)
    {θ₀ : ℝ} (hθ₀ : 0 < θ₀)
    (hwindow : ∀ i, (H i).time (Fin.last (H i).eventCount) ≤
      time i - θ₀ / (A i).flow.scalar (time i) (x i).val)
    {Phi : ℝ → ℝ} (hPhi : Perelman.AdmissiblePinchingFunction Phi)
    (hpinch : ∀ i j, Perelman.PhiAlmostNonnegative ((H i).toHistory.event j).incoming.flow
      (Ico ((H i).time j.castSucc) ((H i).time j.succ)) Phi)
    (hpinchFinal : ∀ i, Perelman.PhiAlmostNonnegative
      ((A i).restrictIncoming le_rfl (A i).lt le_rfl).flow
      (Ico ((H i).time (Fin.last (H i).eventCount)) (time i)) Phi)
    {κ σ₀ : ℝ} (σ : ℕ → ℝ) (hκ : 0 < κ) (hσ₀ : 0 < σ₀)
    (hσQ : ∀ i, σ₀ ≤ σ i * Real.sqrt ((A i).flow.scalar (time i) (x i).val))
    (htested : ∀ i (t : ℝ) (ht : (H i).horizon < t) (hts : t < time i),
      let B := (H i).extendHorizon t ht.le
        (((A i).restrictIncoming le_rfl (A i).lt le_rfl).closedPrefix t
          ((H i).time_le_horizon.trans_lt ht) hts) (hinit i)
      let tm : Icc (0 : ℝ) B.horizon := ⟨t, (H i).horizon_nonneg.trans ht.le, le_rfl⟩
      ∀ (y : (B.toHistory.stageAt tm).Carrier) (b : ℝ), 0 < b → b ≤ σ i →
        B.toHistory.isParabolicallyRmControlledBall tm y b →
          ENNReal.ofReal κ * ENNReal.ofReal b ^ 3 ≤
            riemannianVolumeMeasure ThreeModel (B.toHistory.stageAt tm).Carrier
              (B.toHistory.stageMetric (B.toHistory.activeStage tm) tm)
              (riemannianBallOf (B.toHistory.stageMetric (B.toHistory.activeStage tm) tm) y b))
    {eps C1 C2 : ℝ}
    (hW : ∀ i y, q i < (A i).flow.scalar (time i) y →
      ∃ W : SpatialCanonicalWitness ((A i).flow.base.metric (time i)) eps C1 C2 y,
        W.capTubeHasNeckChart eps)
    {f : ℕ → ℕ} (hf : StrictMono f) (Pl : PointedRiemannianManifold.{u, 0, 0} ThreeModel)
    (F : PointedRiemannianConvergenceMaps
      ({ obj := fun i =>
          { M := ((A i).restrictIncoming le_rfl (A i).lt le_rfl).terminalRegularOpen
            basepoint := x i
            metric := scaleMetric ((A i).flow.scalar (time i) (x i).val)
              (zero_lt_one.trans_le (hQ i))
              ((A i).endpointTerminalLimitMetric
                ((H i).stage (Fin.last (H i).eventCount))).metric } } :
        PointedRiemannianSeq.{u, 0, 0} ThreeModel) Pl f)
    (M : MetricConvergenceData F)
    (hcanonical : ∀ n, M.domain n = CanonicalMetricCompactness.canonicalSourceData F n)
    (W : TopologicalSpace.Opens Pl.M) (xW : ℕ → W) {R₀ : ℝ} (hR₀ : 0 < R₀)
    (hQW : ∀ n, 2 ≤ metricScalarAt Pl.metric (xW n : Pl.M))
    (hQWlim : Tendsto (fun n => metricScalarAt Pl.metric (xW n : Pl.M)) atTop atTop)
    (hcompactW : ∀ n, IsCompact (riemannianClosedBallOf (Pl.metric.restrictOpen W) (xW n)
      (4 * R₀ / Real.sqrt (metricScalarAt Pl.metric (xW n : Pl.M))))) :
    ∃ (j : ℕ → ℕ) (_ : StrictMono j) (A₂ : ℕ → ℝ) (hA₂ : ∀ n, 0 < A₂ n),
      Tendsto (fun n => A₂ n / metricScalarAt Pl.metric (xW (j n) : Pl.M)) atTop (𝓝 1) ∧
      ∃ (P₂ : PointedRiemannianManifold.{u, 0, 0} ThreeModel) (V : TopologicalSpace.Opens P₂.M)
        (hp : P₂.basepoint ∈ V) (_ : PathConnectedSpace V) (tau : ℝ) (htau : 0 < tau)
        (g : ℝ → SmoothRiemannianMetric ThreeModel V),
        g 0 = P₂.metric.restrictOpen V ∧
        IsSolutionOn ({ base.metric := g } : SolutionOn (I := ThreeModel) (M := V)
          (RealTimeInterval.closed (-tau) 0 (by linarith))) ∧
        (∀ t ∈ Icc (-tau) 0, ∀ y : V, metricAlgebraicCurvatureTensorAt (g t) y ∈
          algebraicCurvatureOperatorNonnegativeCone (I := ThreeModel)) ∧
        metricScalarAt P₂.metric P₂.basepoint = 1 ∧
        ∃ C : ℕ → PartialDiffeomorph ThreeModel ThreeModel V W ∞,
          (∀ n, C n ⟨P₂.basepoint, hp⟩ = xW (j n)) ∧
          ∃ r : ℝ, 0 < r ∧ IsCompact (riemannianClosedBallOf (g 0) ⟨P₂.basepoint, hp⟩ r) ∧
          (∀ᶠ n in atTop, riemannianClosedBallOf (g 0) ⟨P₂.basepoint, hp⟩ r ⊆ (C n).source ∧
            riemannianClosedBallOf (scaleMetric (A₂ n) (hA₂ n) (Pl.metric.restrictOpen W))
              (xW (j n)) (r / 4) ⊆ (C n) '' riemannianClosedBallOf (g 0) ⟨P₂.basepoint, hp⟩ r) ∧
          ∀ eta : ℝ, 0 < eta → ∀ᶠ n in atTop,
            ∀ a ∈ riemannianClosedBallOf (g 0) ⟨P₂.basepoint, hp⟩ r,
            ∀ b ∈ riemannianClosedBallOf (g 0) ⟨P₂.basepoint, hp⟩ r,
              |(riemannianEDistOf (scaleMetric (A₂ n) (hA₂ n) (Pl.metric.restrictOpen W))
                (C n a) (C n b)).toReal - (riemannianEDistOf (g 0) a b).toReal| < eta := by
  let G := fun i => (A i).restrictIncoming le_rfl (A i).lt le_rfl
  let L := fun i => (A i).endpointTerminalLimitMetric ((H i).stage (Fin.last (H i).eventCount))
  let Q := fun i => (A i).flow.scalar (time i) (x i).val
  have hQpos : ∀ i, 0 < Q i := fun i => zero_lt_one.trans_le (hQ i)
  have hLscalar (i : ℕ) (y : (G i).terminalRegularOpen) :
      metricScalarAt (L i).metric y = (A i).flow.scalar (time i) y.val :=
    metricScalarAt_restrictOpen _ _ _
  obtain ⟨k, hk, hqk, hratio, hcmp⟩ :=
    CheegerGromovCompactness.exists_scalar_rescaled_source_comparison _ f Pl F M hcanonical W xW
      hR₀ hQW hcompactW
  let y : ∀ m, (G (f (k m))).terminalRegularOpen := fun m =>
    F.partialDiffeomorph (k m) (xW m : Pl.M)
  let qk : ℕ → ℝ := fun m => metricScalarAt
    (scaleMetric (Q (f (k m))) (hQpos _) (L (f (k m))).metric) (y m)
  let Q₂ : ℕ → ℝ := fun m => metricScalarAt (L (f (k m))).metric (y m)
  have hQ₂eq (m : ℕ) : Q₂ m = qk m * Q (f (k m)) := by
    change Q₂ m = metricScalarAt (scaleMetric (Q (f (k m))) (hQpos _) (L (f (k m))).metric)
      (y m) * Q (f (k m))
    rw [metricScalarAt_scaleMetric, mul_comm, ← mul_assoc, mul_inv_cancel₀ (hQpos _).ne',
      one_mul]
  have hqk1 (m : ℕ) : 1 ≤ qk m := hqk m
  have hQ₂ (m : ℕ) : 1 ≤ Q₂ m := by
    rw [hQ₂eq]
    nlinarith [hqk1 m, hQ (f (k m))]
  have hQQ₂ (m : ℕ) : Q (f (k m)) ≤ Q₂ m := by
    rw [hQ₂eq]
    nlinarith [hqk1 m, hQpos (f (k m))]
  have hqQ₂ (m : ℕ) : q (f (k m)) ≤ Q₂ m := (hqQ _).trans (hQQ₂ m)
  have hfk : StrictMono (fun m => f (k m)) := hf.comp hk
  have hqklim : Tendsto qk atTop atTop := by
    have hhalf : ∀ᶠ m in atTop, (1 / 2 : ℝ) < qk m / metricScalarAt Pl.metric (xW m : Pl.M) :=
      hratio.eventually (eventually_gt_nhds (by norm_num))
    apply tendsto_atTop_mono' atTop _ ((hQWlim.atTop_div_const (by norm_num : (0 : ℝ) < 2)))
    filter_upwards [hhalf] with m hm
    have hR := (by linarith [hQW m] : (0 : ℝ) < metricScalarAt Pl.metric (xW m : Pl.M))
    have := (lt_div_iff₀ hR).mp hm
    linarith
  have hQ₂lim : Tendsto Q₂ atTop atTop :=
    tendsto_atTop_mono (fun m =>
      (le_mul_of_one_le_right (by linarith [hqk1 m]) (hQ (f (k m)))).trans_eq
      (hQ₂eq m).symm) hqklim
  have hqy : ∀ᶠ m in atTop, q (f (k m)) < (A (f (k m))).flow.scalar (time (f (k m))) (y m).val := by
    filter_upwards [hqklim.eventually_gt_atTop 1] with m hm
    rw [← hLscalar]
    change q (f (k m)) < Q₂ m
    rw [hQ₂eq]
    nlinarith [hqQ (f (k m)), hQpos (f (k m))]
  obtain ⟨m₀, hm₀⟩ := hqy.exists
  obtain ⟨W₀, _⟩ := hW _ _ hm₀
  have hC2 : 1 ≤ C2 := W₀.one_le_comparison_constant
  have hbuffer₂ := RetainedCoreHistory.final_slab_scalar_buffer_of_spatialCanonicalWitness
    (fun m => H (f (k m))) (fun m => time (f (k m)))
    (fun m => A (f (k m))) Ctime (fun m => q (f (k m))) y Q₂ hQ₂ (fun m => hLscalar _ _) hC2
    (fun m => hW (f (k m))) hqy hθ₀ (fun m => (hwindow (f (k m))).trans
      (sub_le_sub_left (div_le_div_of_nonneg_left hθ₀.le (hQpos _) (hQQ₂ m)) _))
  have hσpos (i : ℕ) : 0 < σ i := by
    by_contra hneg
    have h1 : σ i * Real.sqrt ((A i).flow.scalar (time i) (x i).val) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (not_lt.mp hneg) (Real.sqrt_nonneg _)
    linarith [hσQ i]
  let inc := DifferentialGeometry.Topology.PartialDiffeomorph.subtypeVal (I := ThreeModel) W ⟨xW 0⟩
  let Fcmp := fun m => inc.trans (F.partialDiffeomorph (k m))
  let Gcmp := fun m => scaleMetric (qk m) (lt_of_lt_of_le zero_lt_one (hqk1 m))
    (Pl.metric.restrictOpen W)
  have hHeq (m : ℕ) := scaleMetric_mul_eq (L (f (k m))).metric
    (lt_of_lt_of_le zero_lt_one (hqk1 m)) (hQpos (f (k m))) (zero_lt_one.trans_le (hQ₂ m))
    (hQ₂eq m)
  have hcapture (m : ℕ) : riemannianClosedBallOf
      (scaleMetric (Q₂ m) (zero_lt_one.trans_le (hQ₂ m)) (L (f (k m))).metric) (y m) (R₀ / 4) ⊆
        (Fcmp m) '' riemannianClosedBallOf (Gcmp m) (xW m) R₀ := by
    rw [hHeq m]
    exact (hcmp m).2.2.2.1
  have hBconv : ∀ eta : ℝ, 0 < eta → ∀ᶠ m in atTop,
      ∀ z ∈ riemannianClosedBallOf (Gcmp m) (xW m) R₀, ∀ v : TangentSpace ThreeModel z,
        (1 - eta) * (Gcmp m).inner z v v ≤
          (scaleMetric (Q₂ m) (zero_lt_one.trans_le (hQ₂ m)) (L (f (k m))).metric).inner
            (Fcmp m z) (mfderiv ThreeModel ThreeModel (Fcmp m) z v)
            (mfderiv ThreeModel ThreeModel (Fcmp m) z v) ∧
        (scaleMetric (Q₂ m) (zero_lt_one.trans_le (hQ₂ m)) (L (f (k m))).metric).inner
            (Fcmp m z) (mfderiv ThreeModel ThreeModel (Fcmp m) z v)
            (mfderiv ThreeModel ThreeModel (Fcmp m) z v) ≤ (1 + eta) * (Gcmp m).inner z v v := by
    intro eta heta
    have hlim : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 2)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop
        (tendsto_atTop_add_const_right atTop 2 tendsto_natCast_atTop_atTop)
    filter_upwards [hlim.eventually (eventually_lt_nhds heta)] with m hm
    intro z hz v
    rw [hHeq m]
    have hh := (hcmp m).2.2.1 z hz v
    have hg := metric_inner_self_nonneg (Gcmp m) z v
    exact ⟨(mul_le_mul_of_nonneg_right (by linarith : 1 - eta ≤ 1 - 1 / ((m : ℝ) + 2)) hg).trans
      hh.1, hh.2.trans (mul_le_mul_of_nonneg_right
        (by linarith : 1 + 1 / ((m : ℝ) + 2) ≤ 1 + eta) hg)⟩
  obtain ⟨j, hj, P₂, V, hp, hpath, tau, htau, g, hgb, hbase₂, hsol, hnonneg, C, hcenter, r, hr,
      hcpt, hcap, hdist⟩ :=
    RetainedCoreHistory.exists_nonnegative_local_flow_with_comparison_of_final_slab_window
      (fun m => H (f (k m))) (fun m => time (f (k m)))
      (fun m => A (f (k m))) (fun m => hinit _) Ctime (fun m => q (f (k m))) (fun m => hq _)
      (fun m => hderiv _) (fun m => hfinal _) y Q₂ hQ₂ hqQ₂ hQ₂lim hPhi (fun m => hpinch _)
      (fun m => hpinchFinal _) hbuffer₂ (fun m => hs _) (fun m => rfl) (fun m => σ (f (k m)))
      hκ hσ₀ (fun m => (hσQ (f (k m))).trans (mul_le_mul_of_nonneg_left
        (Real.sqrt_le_sqrt (hQQ₂ m)) (hσpos _).le)) (fun m => htested (f (k m)))
      Gcmp xW Fcmp hR₀ (fun m => (hcmp m).2.1) (fun m => rfl) hcapture hBconv
  exact ⟨j, hj, fun n => qk (j n), fun n => lt_of_lt_of_le zero_lt_one (hqk1 (j n)),
    hratio.comp hj.tendsto_atTop, P₂, V, hp, hpath, tau, htau, g, hgb, hsol, hnonneg, hbase₂, C,
    hcenter, r, hr, hcpt, hcap, hdist⟩

theorem RetainedCoreHistory.final_slab_punctured_cone_end_exclusion_of_bounded_threshold
    (H : ℕ → RetainedCoreHistory.{u}) (time : ℕ → ℝ)
    (A : ∀ i, ((H i).stage (Fin.last (H i).eventCount)).ClosedSlab
      ((H i).time (Fin.last (H i).eventCount)) (time i))
    (hinit : ∀ i, (A i).flow.base.metric ((H i).time (Fin.last (H i).eventCount)) =
      (H i).initialMetric (Fin.last (H i).eventCount))
    (hs : ∀ i, (H i).horizon < time i) (Ctime : ℝ≥0) (q : ℕ → ℝ) (hq : ∀ i, 0 < q i)
    (hderiv : ∀ i (j : Fin (H i).eventCount) (y : ((H i).stage j.castSucc).Carrier),
      ∀ t ∈ Ioo ((H i).time j.castSucc) ((H i).time j.succ),
        q i < ((H i).toHistory.event j).incoming.flow.scalar t y →
        |derivWithin (fun v => ((H i).toHistory.event j).incoming.flow.scalar v y) (Iic t) t| ≤
          Ctime * ((H i).toHistory.event j).incoming.flow.scalar t y ^ 2)
    (hfinal : ∀ i y, ∀ t ∈ Ioo ((H i).time (Fin.last (H i).eventCount)) (time i),
      q i < (A i).flow.scalar t y →
      |derivWithin (fun v => (A i).flow.scalar v y) (Iic t) t| ≤
        Ctime * (A i).flow.scalar t y ^ 2)
    (x : ∀ i, ((A i).restrictIncoming le_rfl (A i).lt le_rfl).terminalRegularOpen)
    (hQ : ∀ i, 1 ≤ (A i).flow.scalar (time i) (x i).val)
    (hqQ : ∀ i, q i ≤ (A i).flow.scalar (time i) (x i).val)
    {θ₀ : ℝ} (hθ₀ : 0 < θ₀)
    (hwindow : ∀ i, (H i).time (Fin.last (H i).eventCount) ≤
      time i - θ₀ / (A i).flow.scalar (time i) (x i).val)
    {Phi : ℝ → ℝ} (hPhi : Perelman.AdmissiblePinchingFunction Phi)
    (hpinch : ∀ i j, Perelman.PhiAlmostNonnegative ((H i).toHistory.event j).incoming.flow
      (Ico ((H i).time j.castSucc) ((H i).time j.succ)) Phi)
    (hpinchFinal : ∀ i, Perelman.PhiAlmostNonnegative
      ((A i).restrictIncoming le_rfl (A i).lt le_rfl).flow
      (Ico ((H i).time (Fin.last (H i).eventCount)) (time i)) Phi)
    {κ σ₀ : ℝ} (σ : ℕ → ℝ) (hκ : 0 < κ) (hσ₀ : 0 < σ₀)
    (hσQ : ∀ i, σ₀ ≤ σ i * Real.sqrt ((A i).flow.scalar (time i) (x i).val))
    (htested : ∀ i (t : ℝ) (ht : (H i).horizon < t) (hts : t < time i),
      let B := (H i).extendHorizon t ht.le
        (((A i).restrictIncoming le_rfl (A i).lt le_rfl).closedPrefix t
          ((H i).time_le_horizon.trans_lt ht) hts) (hinit i)
      let tm : Icc (0 : ℝ) B.horizon := ⟨t, (H i).horizon_nonneg.trans ht.le, le_rfl⟩
      ∀ (y : (B.toHistory.stageAt tm).Carrier) (b : ℝ), 0 < b → b ≤ σ i →
        B.toHistory.isParabolicallyRmControlledBall tm y b →
          ENNReal.ofReal κ * ENNReal.ofReal b ^ 3 ≤
            riemannianVolumeMeasure ThreeModel (B.toHistory.stageAt tm).Carrier
              (B.toHistory.stageMetric (B.toHistory.activeStage tm) tm)
              (riemannianBallOf (B.toHistory.stageMetric (B.toHistory.activeStage tm) tm) y b))
    {eps C1 C2 : ℝ}
    (hW : ∀ i y, q i < (A i).flow.scalar (time i) y →
      ∃ W : SpatialCanonicalWitness ((A i).flow.base.metric (time i)) eps C1 C2 y,
        W.capTubeHasNeckChart eps)
    {f : ℕ → ℕ} (hf : StrictMono f) (Pl : PointedRiemannianManifold.{u, 0, 0} ThreeModel)
    (F : PointedRiemannianConvergenceMaps
      ({ obj := fun i =>
          { M := ((A i).restrictIncoming le_rfl (A i).lt le_rfl).terminalRegularOpen
            basepoint := x i
            metric := scaleMetric ((A i).flow.scalar (time i) (x i).val)
              (zero_lt_one.trans_le (hQ i))
              ((A i).endpointTerminalLimitMetric
                ((H i).stage (Fin.last (H i).eventCount))).metric } } :
        PointedRiemannianSeq.{u, 0, 0} ThreeModel) Pl f)
    (M : MetricConvergenceData F)
    (hcanonical : ∀ n, M.domain n = CanonicalMetricCompactness.canonicalSourceData F n)
    (W : TopologicalSpace.Opens Pl.M) (hWc : PathConnectedSpace W) :
    let _ : PathConnectedSpace W := hWc
    let _ : PseudoMetricSpace W := (Pl.metric.restrictOpen W).toPseudoMetricSpace
    let _ : MetricSpace W := MetricSpace.ofT0PseudoMetricSpace W
    ∀ (qW : UniformSpace.Completion W) (delta : ℝ), 0 < delta →
      IsCompact (Metric.closedBall qW delta) →
      Metric.closedBall qW delta ⊆
        insert qW (range (fun z : W => (z : UniformSpace.Completion W))) →
      Nonempty (DifferentialGeometry.Toponogov.PuncturedConeApproximation qW delta) →
      ∀ xW : ℕ → W, Tendsto (fun n => (xW n : UniformSpace.Completion W)) atTop (𝓝 qW) →
      Tendsto (fun n => metricScalarAt Pl.metric (xW n : Pl.M)) atTop atTop →
      ∀ c : ℝ, 0 < c →
      (∀ᶠ n in atTop, c ≤ metricScalarAt Pl.metric (xW n : Pl.M) *
        dist (xW n : UniformSpace.Completion W) qW ^ 2) →
      (∃ B : ℝ, ∀ᶠ n in atTop, metricScalarAt Pl.metric (xW n : Pl.M) *
        dist (xW n : UniformSpace.Completion W) qW ^ 2 ≤ B) → False := by
  intro instPath instPseudo instMetric
  let _ : PathConnectedSpace W := instPath
  let _ : PseudoMetricSpace W := instPseudo
  let _ : MetricSpace W := instMetric
  intro qW delta hdelta hK hcover hcone xW hx hQW c hc hlower hupper
  obtain ⟨B, hB⟩ := hupper
  have hd0 : Tendsto (fun n => dist (xW n : UniformSpace.Completion W) qW) atTop (𝓝 0) :=
    (tendsto_iff_dist_tendsto_zero).mp hx
  let R₀ := min 1 (Real.sqrt c / 8)
  have hsc : 0 < Real.sqrt c := Real.sqrt_pos.mpr hc
  have hR₀ : 0 < R₀ := lt_min one_pos (by positivity)
  have hev : ∀ᶠ n in atTop, 2 ≤ metricScalarAt Pl.metric (xW n : Pl.M) ∧
      c ≤ metricScalarAt Pl.metric (xW n : Pl.M) * dist (xW n : UniformSpace.Completion W) qW ^ 2 ∧
      metricScalarAt Pl.metric (xW n : Pl.M) * dist (xW n : UniformSpace.Completion W) qW ^ 2 ≤ B ∧
      dist (xW n : UniformSpace.Completion W) qW < delta / 2 := by
    filter_upwards [hQW.eventually_ge_atTop 2, hlower, hB,
      hd0.eventually (eventually_lt_nhds (half_pos hdelta))] with n h1 h2 h3 h4
    exact ⟨h1, h2, h3, h4⟩
  obtain ⟨N, hN⟩ := eventually_atTop.mp hev
  let xW' : ℕ → W := fun n => xW (n + N)
  have hN' (n : ℕ) := hN (n + N) (Nat.le_add_left N n)
  have hcompactW : ∀ n, IsCompact (riemannianClosedBallOf (Pl.metric.restrictOpen W) (xW' n)
      (4 * R₀ / Real.sqrt (metricScalarAt Pl.metric (xW' n : Pl.M)))) := by
    intro n
    obtain ⟨h1, h2, _, h4⟩ := hN' n
    have hRn : 0 < metricScalarAt Pl.metric (xW' n : Pl.M) := by linarith
    have hsR := Real.sqrt_pos.mpr hRn
    have hdn : 0 < dist (xW' n : UniformSpace.Completion W) qW := by
      rcases (dist_nonneg (x := (xW' n : UniformSpace.Completion W)) (y := qW)).lt_or_eq
        with hlt | heq
      · exact hlt
      · exfalso
        change c ≤ metricScalarAt Pl.metric (xW' n : Pl.M) *
          dist (xW' n : UniformSpace.Completion W) qW ^ 2 at h2
        rw [← heq] at h2
        simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero] at h2
        linarith
    have hcd : Real.sqrt c ≤ Real.sqrt (metricScalarAt Pl.metric (xW' n : Pl.M)) *
        dist (xW' n : UniformSpace.Completion W) qW := by
      rw [← Real.sqrt_sq hdn.le, ← Real.sqrt_mul hRn.le]
      exact Real.sqrt_le_sqrt h2
    have hrad : 4 * R₀ / Real.sqrt (metricScalarAt Pl.metric (xW' n : Pl.M)) ≤
        dist (xW' n : UniformSpace.Completion W) qW / 2 := by
      rw [div_le_iff₀ hsR]
      have hR8 : R₀ ≤ Real.sqrt c / 8 := min_le_right _ _
      nlinarith
    have hball : riemannianClosedBallOf (Pl.metric.restrictOpen W) (xW' n)
        (4 * R₀ / Real.sqrt (metricScalarAt Pl.metric (xW' n : Pl.M))) =
          Metric.closedBall (xW' n)
            (4 * R₀ / Real.sqrt (metricScalarAt Pl.metric (xW' n : Pl.M))) := by
      ext z
      change edist (xW' n) z ≤ ENNReal.ofReal _ ↔ dist z (xW' n) ≤ _
      rw [edist_dist, ENNReal.ofReal_le_ofReal_iff (by positivity), dist_comm]
    rw [hball]
    have h4' : dist (xW' n : UniformSpace.Completion W) qW < delta / 2 := h4
    exact isCompact_closedBall_of_lt_dist_puncture hK hcover (xW' n) (by linarith) (by linarith)
  have hQW' : Tendsto (fun n => metricScalarAt Pl.metric (xW' n : Pl.M)) atTop atTop :=
    hQW.comp (tendsto_add_atTop_nat N)
  obtain ⟨j, hj, A₂, hA₂, hratio, P₂, V, hp, hpath, tau, htau, g, hgb, hsol, hnonneg, hbase₂,
      C, hcenter, r, hr, hcpt, hcap, hdist⟩ :=
    RetainedCoreHistory.exists_local_backward_limit_at_final_slab_end_of_bounded_threshold
      H time A
      hinit hs Ctime q hq hderiv hfinal x hQ hqQ hθ₀ hwindow hPhi hpinch hpinchFinal σ hκ
      hσ₀ hσQ htested hW hf Pl F M hcanonical W xW' hR₀ (fun n => (hN' n).1) hQW' hcompactW
  let _ : PseudoMetricSpace V := (P₂.metric.restrictOpen V).toPseudoMetricSpace
  let _ : MetricSpace V := MetricSpace.ofT0PseudoMetricSpace V
  let _ : SigmaCompactSpace V := isSigmaCompact_iff_sigmaCompactSpace.mp
    (Geometry.isSigmaCompact_of_isOpen ThreeModel V.isOpen)
  let S : SolutionOn (I := ThreeModel) (M := V)
      (RealTimeInterval.closed (-tau) 0 (by linarith)) := { base.metric := g }
  have hsec : ∀ t ∈ Icc (-tau) 0, SecLower (S.base.metric t) 0 univ := by
    intro t ht z _ v w
    have h := (metricAlgebraicCurvatureTensorAt_mem_curvatureOperatorNonnegativeCone_iff_sectional
      (g t) z (by simp [ThreeSpace])).mp (hnonneg t ht z) v w
    have hslots : (fun i => ![v, w, w, v] i) = vec4 (I := ThreeModel) v w w v := by
      funext i
      fin_cases i <;> rfl
    simpa only [S, zero_mul, metricRm04StandardAt_apply, hslots] using h
  have hmetric0 : ∀ a b : V, edist a b = riemannianEDistOf (S.base.metric 0) a b := by
    intro a b
    change edist a b = riemannianEDistOf (g 0) a b
    rw [hgb]
    rfl
  let p : V := ⟨P₂.basepoint, hp⟩
  have hscalar0 : metricScalarAt (S.base.metric 0) p ≠ 0 := by
    change metricScalarAt (g 0) p ≠ 0
    rw [hgb, metricScalarAt_restrictOpen, hbase₂]
    norm_num
  have hRj : Tendsto (fun n => metricScalarAt Pl.metric (xW' (j n) : Pl.M)) atTop atTop :=
    hQW'.comp hj.tendsto_atTop
  have hcmp : ∀ᶠ n in atTop, metricScalarAt Pl.metric (xW' (j n) : Pl.M) / 2 ≤ A₂ n ∧
      A₂ n ≤ 2 * metricScalarAt Pl.metric (xW' (j n) : Pl.M) := by
    filter_upwards [hratio.eventually (Ioo_mem_nhds (by norm_num : (1 / 2 : ℝ) < 1)
      (by norm_num : (1 : ℝ) < 2))] with n hn
    have hRpos : 0 < metricScalarAt Pl.metric (xW' (j n) : Pl.M) := by linarith [(hN' (j n)).1]
    have hl := (lt_div_iff₀ hRpos).mp hn.1
    have hu := (div_lt_iff₀ hRpos).mp hn.2
    exact ⟨by linarith, hu.le⟩
  have hAtop : Tendsto A₂ atTop atTop :=
    tendsto_atTop_mono' atTop (hcmp.mono fun _ h => h.1)
      (hRj.atTop_div_const (by norm_num : (0 : ℝ) < 2))
  let rho := fun n => 1 / Real.sqrt (A₂ n)
  have hrho (n : ℕ) : 0 < rho n := one_div_pos.mpr (Real.sqrt_pos.mpr (hA₂ n))
  have hrho0 : Tendsto rho atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (Real.tendsto_sqrt_atTop.comp hAtop)
  have hballP : riemannianClosedBallOf (g 0) p r = Metric.closedBall p r := by
    rw [hgb]
    ext z
    change edist p z ≤ ENNReal.ofReal r ↔ dist z p ≤ r
    rw [edist_dist, ENNReal.ofReal_le_ofReal_iff hr.le, dist_comm]
  have hballH (n : ℕ) : riemannianClosedBallOf
      (scaleMetric (A₂ n) (hA₂ n) (Pl.metric.restrictOpen W)) (xW' (j n)) (r / 4) =
        Metric.closedBall (xW' (j n)) (r / 4 * rho n) := by
    have hscale : r / 4 = Real.sqrt (A₂ n) * (r / 4 * rho n) := by
      dsimp only [rho]
      field_simp [(Real.sqrt_pos.mpr (hA₂ n)).ne']
    conv_lhs => rw [hscale]
    rw [riemannianClosedBallOf_scaleMetric]
    ext z
    change edist (xW' (j n)) z ≤ ENNReal.ofReal (r / 4 * rho n) ↔ dist z (xW' (j n)) ≤ _
    rw [edist_dist, ENNReal.ofReal_le_ofReal_iff (by have := hrho n; positivity), dist_comm]
  have hdistH (n : ℕ) (a b : W) : (riemannianEDistOf
      (scaleMetric (A₂ n) (hA₂ n) (Pl.metric.restrictOpen W)) a b).toReal = dist a b / rho n := by
    rw [edistOf_scale, ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.sqrt_nonneg _)]
    change Real.sqrt (A₂ n) * (edist a b).toReal = _
    rw [edist_dist, ENNReal.toReal_ofReal dist_nonneg]
    dsimp only [rho]
    rw [one_div, div_inv_eq_mul, mul_comm]
  have hdistP (a b : V) : (riemannianEDistOf (g 0) a b).toReal = dist a b := by
    rw [hgb]
    change (edist a b).toReal = _
    rw [edist_dist, ENNReal.toReal_ofReal dist_nonneg]
  apply solution_not_rescaled_cone_limit (M := V) htau S hsol hmetric0 hsec p hscalar0
    hcone.some (fun n => xW' (j n)) (fun n z => C n z) rho hrho hrho0 hcenter hr
    (lower := Real.sqrt (c / 2)) (B := Real.sqrt (max 1 (2 * B)) + 1)
    (Real.sqrt_pos.mpr (half_pos hc)) (hballP ▸ hcpt)
  · filter_upwards [hcmp] with n hn
    obtain ⟨_, h2, h3, _⟩ := hN' (j n)
    set d := dist ((xW' (j n) : W) : UniformSpace.Completion W) qW
    have hd0 : 0 ≤ d := dist_nonneg
    have hdiv : d / rho n = Real.sqrt (A₂ n) * d := by
      dsimp only [rho]
      rw [one_div, div_inv_eq_mul, mul_comm]
    have hsq : (Real.sqrt (A₂ n) * d) ^ 2 = A₂ n * d ^ 2 := by
      rw [mul_pow, Real.sq_sqrt (hA₂ n).le]
    have hz : 0 ≤ Real.sqrt (A₂ n) * d := mul_nonneg (Real.sqrt_nonneg _) hd0
    change c ≤ metricScalarAt Pl.metric (xW' (j n) : Pl.M) * d ^ 2 at h2
    change metricScalarAt Pl.metric (xW' (j n) : Pl.M) * d ^ 2 ≤ B at h3
    rw [hdiv]
    constructor
    · have hlow : c / 2 ≤ (Real.sqrt (A₂ n) * d) ^ 2 := by
        rw [hsq]
        have := mul_le_mul_of_nonneg_right hn.1 (sq_nonneg d)
        nlinarith
      calc Real.sqrt (c / 2) ≤ Real.sqrt ((Real.sqrt (A₂ n) * d) ^ 2) := Real.sqrt_le_sqrt hlow
        _ = Real.sqrt (A₂ n) * d := Real.sqrt_sq hz
    · have hup : (Real.sqrt (A₂ n) * d) ^ 2 ≤ max 1 (2 * B) := by
        rw [hsq]
        have := mul_le_mul_of_nonneg_right hn.2 (sq_nonneg d)
        exact (by nlinarith : A₂ n * d ^ 2 ≤ 2 * B).trans (le_max_right _ _)
      have := Real.le_sqrt_of_sq_le hup
      linarith
  · filter_upwards [hcap] with n hn
    rw [← hballH n, ← hballP]
    exact hn.2
  · intro eta heta
    filter_upwards [hdist eta heta] with n hn
    intro a ha b hb
    have h := hn a (hballP ▸ ha) b (hballP ▸ hb)
    rw [hdistH, hdistP] at h
    exact h

theorem RetainedCoreHistory.exists_normalized_scalar_bound_of_bounded_threshold
    (H : ℕ → RetainedCoreHistory.{u}) (time : ℕ → ℝ)
    (A : ∀ i, ((H i).stage (Fin.last (H i).eventCount)).ClosedSlab
      ((H i).time (Fin.last (H i).eventCount)) (time i))
    (hinit : ∀ i, (A i).flow.base.metric ((H i).time (Fin.last (H i).eventCount)) =
      (H i).initialMetric (Fin.last (H i).eventCount))
    (hs : ∀ i, (H i).horizon < time i) (Ctime Cgrad : ℝ≥0) (q : ℕ → ℝ) (hq : ∀ i, 0 < q i)
    (hderiv : ∀ i (j : Fin (H i).eventCount) (y : ((H i).stage j.castSucc).Carrier),
      ∀ t ∈ Ioo ((H i).time j.castSucc) ((H i).time j.succ),
        q i < ((H i).toHistory.event j).incoming.flow.scalar t y →
        |derivWithin (fun v => ((H i).toHistory.event j).incoming.flow.scalar v y) (Iic t) t| ≤
          Ctime * ((H i).toHistory.event j).incoming.flow.scalar t y ^ 2)
    (hfinal : ∀ i y, ∀ t ∈ Ioo ((H i).time (Fin.last (H i).eventCount)) (time i),
      q i < (A i).flow.scalar t y →
      |derivWithin (fun v => (A i).flow.scalar v y) (Iic t) t| ≤
        Ctime * (A i).flow.scalar t y ^ 2)
    (hgradient : ∀ i y, ∀ t ∈ Ioo ((H i).time (Fin.last (H i).eventCount)) (time i),
      q i < (A i).flow.scalar t y → ∀ v : TangentSpace ThreeModel y,
        |Perelman.CanonicalNeighborhood.scalarDifferential
            ((A i).restrictIncoming le_rfl (A i).lt le_rfl).flow t y v| ≤
          Cgrad * (A i).flow.scalar t y * Real.sqrt ((A i).flow.scalar t y) *
            Real.sqrt (((A i).flow.base.metric t).inner y v v))
    (x : ∀ i, ((A i).restrictIncoming le_rfl (A i).lt le_rfl).terminalRegularOpen)
    (hQ : ∀ i, 1 ≤ (A i).flow.scalar (time i) (x i).val)
    (hqQ : ∀ i, q i ≤ (A i).flow.scalar (time i) (x i).val)
    (hQlim : Tendsto (fun i => (A i).flow.scalar (time i) (x i).val) atTop atTop)
    {θ₀ : ℝ} (hθ₀ : 0 < θ₀)
    (hwindow : ∀ i, (H i).time (Fin.last (H i).eventCount) ≤
      time i - θ₀ / (A i).flow.scalar (time i) (x i).val)
    {Phi : ℝ → ℝ} (hPhi : Perelman.AdmissiblePinchingFunction Phi)
    (hpinch : ∀ i j, Perelman.PhiAlmostNonnegative ((H i).toHistory.event j).incoming.flow
      (Ico ((H i).time j.castSucc) ((H i).time j.succ)) Phi)
    (hpinchFinal : ∀ i, Perelman.PhiAlmostNonnegative
      ((A i).restrictIncoming le_rfl (A i).lt le_rfl).flow
      (Ico ((H i).time (Fin.last (H i).eventCount)) (time i)) Phi)
    {κ σ₀ : ℝ} (σ : ℕ → ℝ) (hκ : 0 < κ) (hσ₀ : 0 < σ₀)
    (hσQ : ∀ i, σ₀ ≤ σ i * Real.sqrt ((A i).flow.scalar (time i) (x i).val))
    (htested : ∀ i (t : ℝ) (ht : (H i).horizon < t) (hts : t < time i),
      let B := (H i).extendHorizon t ht.le
        (((A i).restrictIncoming le_rfl (A i).lt le_rfl).closedPrefix t
          ((H i).time_le_horizon.trans_lt ht) hts) (hinit i)
      let tm : Icc (0 : ℝ) B.horizon := ⟨t, (H i).horizon_nonneg.trans ht.le, le_rfl⟩
      ∀ (y : (B.toHistory.stageAt tm).Carrier) (b : ℝ), 0 < b → b ≤ σ i →
        B.toHistory.isParabolicallyRmControlledBall tm y b →
          ENNReal.ofReal κ * ENNReal.ofReal b ^ 3 ≤
            riemannianVolumeMeasure ThreeModel (B.toHistory.stageAt tm).Carrier
              (B.toHistory.stageMetric (B.toHistory.activeStage tm) tm)
              (riemannianBallOf (B.toHistory.stageMetric (B.toHistory.activeStage tm) tm) y b))
    {eps C1 C2 : ℝ}
    (heps : 13000 * (13000 * eps) ≤
      min (neckModelTolerance (1 / 4000000 / 26000)) (1 / 4000000 / 26000 / 64))
    (hW : ∀ i y, q i < (A i).flow.scalar (time i) y →
      ∃ W : SpatialCanonicalWitness ((A i).flow.base.metric (time i)) eps C1 C2 y,
        W.capTubeHasNeckChart eps) :
    ∀ R : ℝ, 0 < R → ∃ B : ℝ, ∀ᶠ i in atTop,
      ∀ y : ((A i).restrictIncoming le_rfl (A i).lt le_rfl).terminalRegularOpen,
        riemannianEDistOf (scaleMetric ((A i).flow.scalar (time i) (x i).val)
          (zero_lt_one.trans_le (hQ i))
          ((A i).endpointTerminalLimitMetric ((H i).stage (Fin.last (H i).eventCount))).metric)
          (x i) y < ENNReal.ofReal R →
        metricScalarAt
          ((A i).endpointTerminalLimitMetric ((H i).stage (Fin.last (H i).eventCount))).metric y /
            (A i).flow.scalar (time i) (x i).val ≤ B := by
  intro R hR
  by_contra hB
  have hL1 := RetainedCoreHistory.exists_pointed_convergence_at_scalar_escape_of_final_slab_window
    H time A hinit hs Ctime Cgrad q hq hderiv hfinal hgradient x hQ hqQ θ₀ hθ₀ hwindow
    ⟨R, hR, hB⟩ Phi hPhi hpinch hpinchFinal κ σ₀ σ hκ hσ₀ hσQ htested
  dsimp only at hL1
  obtain ⟨rho, hrho, ind, hind, z, f, hf, r, hr, hrlim, Pl, F₀, M, _, hcan, hradial, hcompact,
      hcapture, hmetric, hfinite, hdist, hescape⟩ := hL1
  let F := PointedRiemannianConvergenceMaps.liftTargetOpen
    (S := { obj := fun i =>
          { M := ((A (ind i)).restrictIncoming le_rfl (A (ind i)).lt le_rfl).terminalRegularOpen
            basepoint := x (ind i)
            metric := scaleMetric ((A (ind i)).flow.scalar (time (ind i)) (x (ind i)).val)
              (zero_lt_one.trans_le (hQ (ind i)))
              ((A (ind i)).endpointTerminalLimitMetric
                ((H (ind i)).stage (Fin.last (H (ind i)).eventCount))).metric } })
    (fun i => connectedComponentOpen (I := ThreeModel) (x (ind i)))
    (fun i => (mem_connectedComponent : x (ind i) ∈
      connectedComponentOpen (I := ThreeModel) (x (ind i)))) F₀
  have halpha : (0 : ℝ) < 1 / 4000000 := by norm_num
  obtain ⟨g, hg, _, hblow, hnecks⟩ :=
    exists_isometric_ray_with_spatialNecks_of_bounded_threshold
    (fun i => (H (ind i)).stage (Fin.last (H (ind i)).eventCount))
    (fun i => (H (ind i)).time (Fin.last (H (ind i)).eventCount)) (fun i => time (ind i))
    (fun i => A (ind i)) Ctime Cgrad (fun i => q (ind i)) (fun i => hfinal (ind i))
    (fun i => hgradient (ind i)) (fun i => x (ind i)) (fun i => hQ (ind i))
    (fun i => hqQ (ind i)) halpha (by norm_num) heps
    (fun i => hW (ind i)) hrho f hf r (fun n => (hr n).1) hrlim Pl F M hcan hradial hcompact
    hcapture (fun ε hε => (hmetric ε hε).mono fun n hn y hy v => (hn y hy v).1)
    (fun n => z (f n)) hfinite hdist hescape
  have hsec := metricRm04StandardAt_nonneg_of_normalized_terminal_pinching
    (fun i => (H (ind i)).stage (Fin.last (H (ind i)).eventCount))
    (fun i => (H (ind i)).time (Fin.last (H (ind i)).eventCount)) (fun i => time (ind i))
    (fun i => A (ind i)) (fun i => x (ind i)) (fun i => hQ (ind i)) hPhi
    (fun i => hpinchFinal (ind i)) Pl F M hcan (hQlim.comp (hind.comp hf).tendsto_atTop)
  let _ : EMetricSpace Pl.M := Pl.emetricSpace
  have hfin : ∀ a b : Pl.M, edist a b ≠ ⊤ := by
    intro a b
    apply ne_top_of_le_ne_top _ (edist_triangle_left a b Pl.basepoint)
    exact ENNReal.add_ne_top.mpr ⟨(hradial a).ne_top, (hradial b).ne_top⟩
  let _ : MetricSpace Pl.M := EMetricSpace.toMetricSpace hfin
  obtain ⟨qc, hqc, _⟩ :=
    DifferentialGeometry.Geometry.exists_completion_endpoint_of_isometry hrho hg
  obtain ⟨W, hWc, hrest⟩ := exists_punctured_cone_end_of_spatial_necks Pl.metric
    (fun _ _ => rfl) hrho halpha (by norm_num) hsec g hg hblow qc hqc hnecks
  let _ : PathConnectedSpace W := hWc
  let mW : MetricSpace W :=
    let _ : PseudoMetricSpace W := (Pl.metric.restrictOpen W).toPseudoMetricSpace
    MetricSpace.ofT0PseudoMetricSpace W
  let _ : MetricSpace W := mW
  let _ : PseudoMetricSpace W := mW.toPseudoMetricSpace
  let _ : UniformSpace W := mW.toPseudoMetricSpace.toUniformSpace
  let eW : PseudoEMetricSpace W :=
    @PseudoMetricSpace.toPseudoEMetricSpace W mW.toPseudoMetricSpace
  let _ : WeakPseudoEMetricSpace W :=
    @PseudoEMetricSpace.toWeakPseudoEMetricSpace W eW
  obtain ⟨qW, delta, hdelta, _, _, hK, hcover, xW, _, _, _, hxW, _, hQW, hlowerW, hupperW,
    hcone⟩ := hrest
  have hQW' : Tendsto (fun n => metricScalarAt Pl.metric (xW n : Pl.M)) atTop atTop := by
    simpa only [metricScalarAt_restrictOpen] using hQW
  have hlower' : ∀ᶠ n in atTop, ((2 * (1 / 4000000 : ℝ))⁻¹) ^ 2 / 8 ≤
      metricScalarAt Pl.metric (xW n : Pl.M) *
        dist (xW n : UniformSpace.Completion W) qW ^ 2 :=
    Eventually.of_forall fun n => by simpa only [metricScalarAt_restrictOpen] using hlowerW n
  have hupper' : ∃ B : ℝ, ∀ᶠ n in atTop, metricScalarAt Pl.metric (xW n : Pl.M) *
      dist (xW n : UniformSpace.Completion W) qW ^ 2 ≤ B := by
    obtain ⟨B, _, hB⟩ := hupperW
    exact ⟨B, by simpa only [metricScalarAt_restrictOpen] using hB⟩
  exact RetainedCoreHistory.final_slab_punctured_cone_end_exclusion_of_bounded_threshold
    (fun i => H (ind i)) (fun i => time (ind i)) (fun i => A (ind i)) (fun i => hinit (ind i))
    (fun i => hs (ind i)) Ctime (fun i => q (ind i)) (fun i => hq _) (fun i => hderiv (ind i))
    (fun i => hfinal (ind i)) (fun i => x (ind i)) (fun i => hQ _) (fun i => hqQ _)
    hθ₀ (fun i => hwindow _) hPhi (fun i => hpinch _)
    (fun i => hpinchFinal _) (fun i => σ (ind i)) hκ hσ₀ (fun i => hσQ _)
    (fun i => htested (ind i)) (fun i => hW (ind i)) hf Pl F M hcan W hWc qW delta hdelta hK
    hcover hcone xW hxW hQW' _ (by norm_num) hlower' hupper'

theorem RetainedCoreHistory.exists_scalar_bound_at_distance_of_bounded_threshold
    (κ C1 C2 : ℝ) (hκ : 0 < κ) (Ctime Cgrad : ℝ≥0) {phi : ℝ → ℝ}
    (hphi : Perelman.AdmissiblePinchingFunction phi) :
    ∃ εcone : ℝ, 0 < εcone ∧ ∀ ε : ℝ, ε ≤ εcone → ∀ A : ℝ, 0 < A → ∀ Cq : ℝ,
      ∃ Q Λ : ℝ, 1 ≤ Q ∧ 1 ≤ Λ ∧
      ∀ (H : RetainedCoreHistory.{u})
        (hend : H.time (Fin.last H.eventCount) = H.horizon) {t : ℝ}
        (S : (H.stage (Fin.last H.eventCount)).ClosedSlab (H.time (Fin.last H.eventCount)) t)
        (hS : S.flow.base.metric (H.time (Fin.last H.eventCount)) =
          H.initialMetric (Fin.last H.eventCount))
        (y : (H.stage (Fin.last H.eventCount)).Carrier) (q ρ : ℝ),
        0 < q → q ≤ Cq * S.flow.scalar t y → Λ ≤ S.flow.scalar t y →
        H.time (Fin.last H.eventCount) ≤ t - Λ / S.flow.scalar t y →
        (∀ x, q < S.flow.scalar t x →
          ∃ W : SpatialCanonicalWitness (S.flow.base.metric t) ε C1 C2 x,
            W.capTubeHasNeckChart ε) →
        H.EventSlabsDerivative Ctime q (Fin.last H.eventCount) →
        (S.restrictIncoming le_rfl S.lt le_rfl).DerivativeBoundBefore Ctime q t →
        (S.restrictIncoming le_rfl S.lt le_rfl).GradientBoundBefore Cgrad q t →
        H.EventSlabsPinched phi →
        Perelman.PhiAlmostNonnegative (S.restrictIncoming le_rfl S.lt le_rfl).flow
          (Ico (H.time (Fin.last H.eventCount)) t) phi →
        H.TerminalNoncollapsedBefore hend (S.restrictIncoming le_rfl S.lt le_rfl) hS κ ρ t →
        Λ ≤ ρ * Real.sqrt (S.flow.scalar t y) →
        ∀ z ∈ riemannianBallOf (S.flow.base.metric t) y (A / Real.sqrt (S.flow.scalar t y)),
          S.flow.scalar t z ≤ Q * S.flow.scalar t y := by
  have hmin : 0 < min (neckModelTolerance (1 / 4000000 / 26000)) (1 / 4000000 / 26000 / 64) :=
    lt_min (neckModelTolerance_pos (by norm_num)) (by norm_num)
  refine ⟨min (neckModelTolerance (1 / 4000000 / 26000)) (1 / 4000000 / 26000 / 64) /
    (13000 * 13000), by positivity, ?_⟩
  intro ε hεle A hA Cq
  have heps : 13000 * (13000 * ε) ≤
      min (neckModelTolerance (1 / 4000000 / 26000)) (1 / 4000000 / 26000 / 64) := by
    have h := (le_div_iff₀ (by norm_num : (0 : ℝ) < 13000 * 13000)).mp hεle
    linarith
  let K := max Cq 1
  have hK : 1 ≤ K := le_max_right _ _
  by_contra hcon
  push Not at hcon
  have hn0 (n : ℕ) : (0 : ℝ) ≤ n := n.cast_nonneg
  choose H hend t S hS y q ρ hq hqy hΛ hwin hW hderiv hfinal hgrad hpinch hpinchF hnc hρ z hz
    hbad using fun n : ℕ => hcon ((n : ℝ) + K + 1) ((n : ℝ) + K + 1)
      (by linarith [hn0 n]) (by linarith [hn0 n])
  have hRy (n : ℕ) : (n : ℝ) + K + 1 ≤ (S n).flow.scalar (t n) (y n) := hΛ n
  have hRpos (n : ℕ) : 0 < (S n).flow.scalar (t n) (y n) := by linarith [hRy n, hn0 n]
  have hqK (n : ℕ) : q n ≤ K * (S n).flow.scalar (t n) (y n) :=
    (hqy n).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (hRpos n).le)
  have hcmem (n : ℕ) : max (q n) ((S n).flow.scalar (t n) (y n)) ∈
      Icc ((S n).flow.scalar (t n) (y n)) ((S n).flow.scalar (t n) (z n)) := by
    refine ⟨le_max_right _ _, max_le ?_ ?_⟩
    · nlinarith [hbad n, hqK n, hRpos n, hn0 n]
    · nlinarith [hbad n, hRpos n, hn0 n]
  have hcontR (n : ℕ) : Continuous ((S n).flow.scalar (t n)) :=
    (metricScalar_smooth ((S n).flow.base.metric (t n))).continuous
  choose xc hxc hxz using fun n => exists_riemannianEDistOf_lt_of_mem_Icc_scalar
    ((S n).flow.base.metric (t n)) (hcontR n)
      (show riemannianEDistOf ((S n).flow.base.metric (t n)) (y n) (z n) <
        ENNReal.ofReal (A / Real.sqrt ((S n).flow.scalar (t n) (y n))) from hz n) (hcmem n)
  let x : ∀ n, ((S n).restrictIncoming le_rfl (S n).lt le_rfl).terminalRegularOpen := fun n =>
    ⟨xc n, by
      change xc n ∈ ((S n).restrictIncoming le_rfl (S n).lt le_rfl).terminalRegularRegion
      rw [(S n).terminalRegularRegion_eq_univ _]
      trivial⟩
  have hRx (n : ℕ) : (S n).flow.scalar (t n) (x n).val =
      max (q n) ((S n).flow.scalar (t n) (y n)) := hxc n
  have hyx (n : ℕ) : (S n).flow.scalar (t n) (y n) ≤ (S n).flow.scalar (t n) (x n).val := by
    rw [hRx]
    exact le_max_right _ _
  have hxK (n : ℕ) : (S n).flow.scalar (t n) (x n).val ≤ K * (S n).flow.scalar (t n) (y n) := by
    rw [hRx]
    exact max_le (hqK n) (le_mul_of_one_le_left (hRpos n).le hK)
  have hQ (n : ℕ) : 1 ≤ (S n).flow.scalar (t n) (x n).val := by
    linarith [hyx n, hRy n, hn0 n]
  have hqQ (n : ℕ) : q n ≤ (S n).flow.scalar (t n) (x n).val := by
    rw [hRx]
    exact le_max_left _ _
  have hQlim : Tendsto (fun n => (S n).flow.scalar (t n) (x n).val) atTop atTop := by
    refine tendsto_atTop_mono (fun n => ?_)
      (tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop)
    linarith [hyx n, hRy n, hK]
  have hwindow (n : ℕ) : (H n).time (Fin.last (H n).eventCount) ≤
      t n - 1 / (S n).flow.scalar (t n) (x n).val := by
    have h1 : 1 / (S n).flow.scalar (t n) (x n).val ≤ 1 / (S n).flow.scalar (t n) (y n) :=
      one_div_le_one_div_of_le (hRpos n) (hyx n)
    have h2 : 1 / (S n).flow.scalar (t n) (y n) ≤
        ((n : ℝ) + K + 1) / (S n).flow.scalar (t n) (y n) :=
      div_le_div_of_nonneg_right (by linarith [hn0 n]) (hRpos n).le
    linarith [hwin n]
  have hσQ (n : ℕ) : 1 ≤ ρ n * Real.sqrt ((S n).flow.scalar (t n) (x n).val) := by
    have h1 : 1 ≤ ρ n * Real.sqrt ((S n).flow.scalar (t n) (y n)) :=
      le_trans (by linarith [hn0 n]) (hρ n)
    have hρpos : 0 ≤ ρ n := by
      by_contra hneg
      have := mul_nonpos_of_nonpos_of_nonneg (not_le.mp hneg).le (Real.sqrt_nonneg
        ((S n).flow.scalar (t n) (y n)))
      linarith
    exact h1.trans (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (hyx n)) hρpos)
  obtain ⟨B, hB⟩ :=
    RetainedCoreHistory.exists_normalized_scalar_bound_of_bounded_threshold
    H t S hS (fun n => by rw [← hend n]; exact (S n).lt) Ctime Cgrad q hq
    (fun n j y' t' ht hqy' => hderiv n j (Fin.castSucc_lt_last j) y' t' ht hqy')
    (fun n y' t' ht hqy' => hfinal n y' t' ht hqy')
    (fun n y' t' ht hqy' => hgrad n y' t' ht hqy') x hQ hqQ hQlim one_pos hwindow hphi
    (fun n => hpinch n) (fun n => hpinchF n) ρ hκ one_pos hσQ
    (fun n T hT hTs => by
      intro _ tm yy b _ hbρ hball
      exact hnc n T (by rw [hend n]; exact hT) hTs hTs.le tm yy b le_rfl hbρ hball)
    heps (fun n => hW n) (A * Real.sqrt K + 1) (by positivity)
  obtain ⟨n, hn, hnB⟩ := (hB.and (eventually_gt_atTop ⌈B * K⌉₊)).exists
  let z' : ((S n).restrictIncoming le_rfl (S n).lt le_rfl).terminalRegularOpen :=
    ⟨z n, by
      change z n ∈ ((S n).restrictIncoming le_rfl (S n).lt le_rfl).terminalRegularRegion
      rw [(S n).terminalRegularRegion_eq_univ _]
      trivial⟩
  have hsx := Real.sqrt_pos.mpr (zero_lt_one.trans_le (hQ n))
  have hsy := Real.sqrt_pos.mpr (hRpos n)
  have hratio : Real.sqrt ((S n).flow.scalar (t n) (x n).val) ≤
      Real.sqrt K * Real.sqrt ((S n).flow.scalar (t n) (y n)) := by
    rw [← Real.sqrt_mul (zero_le_one.trans hK)]
    exact Real.sqrt_le_sqrt (hxK n)
  have hdist : riemannianEDistOf (scaleMetric ((S n).flow.scalar (t n) (x n).val)
      (zero_lt_one.trans_le (hQ n)) ((S n).endpointTerminalLimitMetric _).metric) (x n) z' <
        ENNReal.ofReal (A * Real.sqrt K + 1) := by
    rw [DifferentialGeometry.edistOf_scale, (S n).riemannianEDistOf_endpointTerminalLimitMetric]
    change ENNReal.ofReal (Real.sqrt ((S n).flow.scalar (t n) (x n).val)) *
      riemannianEDistOf ((S n).flow.base.metric (t n)) (xc n) (z n) < _
    calc ENNReal.ofReal (Real.sqrt ((S n).flow.scalar (t n) (x n).val)) *
          riemannianEDistOf ((S n).flow.base.metric (t n)) (xc n) (z n) <
        ENNReal.ofReal (Real.sqrt ((S n).flow.scalar (t n) (x n).val)) *
          ENNReal.ofReal (A / Real.sqrt ((S n).flow.scalar (t n) (y n))) :=
          ENNReal.mul_lt_mul_right (ENNReal.ofReal_pos.mpr hsx).ne' ENNReal.ofReal_ne_top (hxz n)
      _ = ENNReal.ofReal (Real.sqrt ((S n).flow.scalar (t n) (x n).val) *
          (A / Real.sqrt ((S n).flow.scalar (t n) (y n)))) :=
          (ENNReal.ofReal_mul hsx.le).symm
      _ ≤ ENNReal.ofReal (A * Real.sqrt K) := by
          apply ENNReal.ofReal_le_ofReal
          rw [mul_div_assoc', div_le_iff₀ hsy]
          nlinarith [hratio]
      _ < ENNReal.ofReal (A * Real.sqrt K + 1) :=
          (ENNReal.ofReal_lt_ofReal_iff (by positivity)).mpr (by linarith)
  have hle := hn z' hdist
  have hscal : metricScalarAt ((S n).endpointTerminalLimitMetric _).metric z' =
      (S n).flow.scalar (t n) (z n) := metricScalarAt_restrictOpen _ _ _
  rw [hscal, div_le_iff₀ (zero_lt_one.trans_le (hQ n))] at hle
  have hceil : B * K ≤ (n : ℝ) := (Nat.le_ceil (B * K)).trans (by exact_mod_cast hnB.le)
  have hbig := hbad n
  have hxKn := hxK n
  have hRyn := hRpos n
  have hn1 := hn0 n
  rcases le_or_gt 0 B with hB0 | hB0
  · have h1 : B * (S n).flow.scalar (t n) (x n).val ≤
        B * (K * (S n).flow.scalar (t n) (y n)) := mul_le_mul_of_nonneg_left hxKn hB0
    have h2 : B * K * (S n).flow.scalar (t n) (y n) ≤ n * (S n).flow.scalar (t n) (y n) :=
      mul_le_mul_of_nonneg_right hceil hRyn.le
    nlinarith
  · have h1 : B * (S n).flow.scalar (t n) (x n).val ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg hB0.le (zero_le_one.trans (hQ n))
    nlinarith

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
