import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.Local.BoundedCurvatureAtDistanceBoundedThreshold_P6L
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.Local.TerminalScalarRayWindow_P6WB

/-!
# P6WIN-B G1：`BoundedThreshold:98`（ray-with-necks）的时间窗形（`_P6WB`）

P6CON G2b 窗口 spine 的 B 段（hgradient 链）：`BT:98_P6L` 的 `hgradient` 只传给 `TSR:490` ⇒ 改传
`TSR:490` 窗口形（`TerminalScalarRayWindow_P6WB`）：`U` 后加 `c : ℕ → ℝ`、`hc : ∀ i, c i < s i`（F6），
`hgradient` 加 guard `c i ≤ t →`。`hW`（只在终端时刻 `s i` 与 segment 点求值）、`Rad`、`hU`、结论逐字。
私有引理（`BT` 的 inner-ball scalar bound）复制为 `_P6WB`。
consumer：`BT:98_P6L`（全 slab 形）⇐ 窗口形取 `c i = a i`。
-/

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

private theorem eventually_scalar_le_on_inner_ball_of_pointed_convergence_P6WB
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

/-- **`_P6WB`（`BT:98` 窗口形）**：`BT:98_P6L` 的 `hgradient` 只在窗口 `[c i, s i)` 内要
（guard `c i ≤ t`，窗口起点 `c i < s i` 在 `U` 之后给出；只传给 `TSR:490` 窗口形）。
`hW`（终端时刻 `s i`）、`Rad`、`hU`、其余前提、结论、证明体逐字。 -/
theorem exists_isometric_ray_with_spatialNecks_of_bounded_threshold_window_P6WB
    (P : ℕ → OrientedThreeStage.{u}) (a s : ℕ → ℝ) (A : ∀ i, (P i).ClosedSlab (a i) (s i))
    (Cgrad : ℝ≥0) (q : ℕ → ℝ) (U : ∀ i, Set (P i).Carrier)
    (c : ℕ → ℝ) (hc : ∀ i, c i < s i)
    (hgradient : ∀ i, ∀ y ∈ U i, ∀ t ∈ Ioo (a i) (s i), c i ≤ t →
      q i < (A i).flow.scalar t y →
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
    (hW : ∀ i, ∀ y ∈ U i, q i < (A i).flow.scalar (s i) y →
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
        (A (f n)).flow.scalar (s (f n)) (x (f n)).val) atTop atTop)
    {Rad : ℝ} (hRad : rho < Rad)
    (hU : ∀ i, ∀ y : ((A i).restrictIncoming le_rfl (A i).lt le_rfl).terminalRegularOpen,
      riemannianEDistOf (scaleMetric ((A i).flow.scalar (s i) (x i).val)
        (zero_lt_one.trans_le (hQ i)) ((A i).endpointTerminalLimitMetric (P i)).metric)
        (x i) y < ENNReal.ofReal Rad → ∀ᶠ τ in 𝓝[<] s i,
        riemannianBallOf ((A i).flow.base.metric τ) y.val
          (2 * (Perelman.CanonicalNeighborhood.localPropagationRadius Cgrad /
            Real.sqrt (2 * (A i).flow.scalar (s i) (x i).val))) ⊆ U i) :
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
      eventually_scalar_le_on_inner_ball_of_pointed_convergence_P6WB F M hcanonical hcompact hR
        hRrho
    refine ⟨B, hB.mono fun n hn y hy => ?_⟩
    rw [← hXscalar]
    exact hn y hy
  obtain ⟨κ₁, hκ₁, A', ell, y, γ, _, hAlim, helllim, _, hy, _, _, hends, _, _, _, hmin,
      φ, g, hφ, hg, hgbase, hconv, _, hscalar, _, _, hblowup⟩ :=
    exists_isometric_terminal_scalar_blowup_curve_of_scalar_escape_window_P6WB P a s G L Q hQpos
      q 1 (Eventually.of_forall fun i => by simpa only [one_mul] using hqQ i) Cgrad U c hc
      hgradient x Pl
      f hf F M hcanonical hrho r hr hrlim
      (fun n y hy => hcapture n (show riemannianEDistOf _ _ y ≤ _ from le_of_lt hy)) hlower
      hcompact hradial
      (fun i => (hLscalar i (x i)).le) z hfinite hdist hhigh hinner hRad hU
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
    have hUmem : (γ (φ n) τ).val ∈ U (f (κ₁ (φ n))) := by
      have hd : riemannianEDistOf (scaleMetric (Q (f (κ₁ (φ n)))) (hQpos _)
          (L (f (κ₁ (φ n)))).metric) (x (f (κ₁ (φ n)))) (γ (φ n) τ) < ENNReal.ofReal Rad := by
        rw [← (hends (φ n)).1, hmin (φ n) 0 ⟨le_rfl, τ.property.1.trans hn.le⟩ τ
          ⟨τ.property.1, hn.le⟩, zero_sub, abs_neg, abs_of_nonneg τ.property.1]
        exact (ENNReal.ofReal_lt_ofReal_iff (hrho.trans hRad)).mpr (τ.property.2.trans hRad)
      obtain ⟨τ', hτ'⟩ := (hU (f (κ₁ (φ n))) (γ (φ n) τ) hd).exists
      apply hτ'
      change riemannianEDistOf _ (γ (φ n) τ).val (γ (φ n) τ).val < _
      rw [riemannianEDistOf_self]
      apply ENNReal.ofReal_pos.mpr
      have hlpr := Perelman.CanonicalNeighborhood.localPropagationRadius_pos Cgrad.coe_nonneg
      have hsq : 0 < Real.sqrt (2 * (A (f (κ₁ (φ n)))).flow.scalar (s (f (κ₁ (φ n))))
          (x (f (κ₁ (φ n)))).val) := Real.sqrt_pos.mpr (by linarith [hQpos (f (κ₁ (φ n)))])
      positivity
    obtain ⟨W0, _⟩ := hW _ _ hUmem hq
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
    exact (A (f (κ₁ (φ n)))).nonempty_scaled_spatialNeck_of_minimizing_segment_P6L hQi
      (lt_of_le_of_lt (min_le_right _ _) (by linarith)) heps hτpos hn hmin'
      (hW _ _ hUmem hq) hleft hright

/-- consumer：`BT:98_P6L`（全 slab `hgradient`）⇐ 窗口形（`c i = a i`）。 -/
example : type_of% @exists_isometric_ray_with_spatialNecks_of_bounded_threshold_P6L.{0} :=
  fun P a s A Cgrad q U hgradient =>
    exists_isometric_ray_with_spatialNecks_of_bounded_threshold_window_P6WB P a s A Cgrad q U
      a (fun i => (A i).lt) (fun i y hy t ht _ => hgradient i y hy t ht)

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
