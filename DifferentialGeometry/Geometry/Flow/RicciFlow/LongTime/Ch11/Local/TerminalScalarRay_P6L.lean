import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.Local.TerminalCurvatureEscape_P6L
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TerminalScalarRay

/-!
# L6-A 第 4 层：`TerminalScalarRay` 的局部化（`_P6L`，合同表 §3 行 7）

局部化合同 `docs/geometrization/chapter8/design-C11-P6-localization-contract-20261006.md` §2 (G)
与 rev1 §R2：原 `ST/TerminalScalarRay.lean:24,104,343,490` 的 `hgradient : ∀ x : Carrier`
在证明里只经 `TerminalScalarBall:110` 于 **segment 点** `γ n t` 的小球上求值（l.85）⇒
`hgradient` 限于 `U n`，加 segment 点处的移动球包含 `hU`（半径 `2·rad_C/√(2Q n)`；l.85 的
实际半径 `2·rad_C/√(2AQ n)`（`A ≥ 1`）更小，由 `riemannianBallOf_mono` 收）。
* `:24`/`:104`：`hU : ∀ t, ∀ᶠ n, ∀ᶠ τ in 𝓝[<] s n, B_τ(γ n t, 2·rad_C/√(2Q n)) ⊆ U n`；
* `:343`：segment 族 `γ n` 在 `[0, ell n]` 上，`hU` eventually in n、∀ t ∈ [0, ell n]；
* `:490`：segment 由内部的 `TCE:358_P6L` 产生 ⇒ 用先验半径 `Rad`（`rho < Rad`，合 rev1 9.3 的
  假设域 ⊋ 结论域余量）：`∀ n, ∀ y, d_{Q·L}(basepoint n, y) < Rad → ∀ᶠ τ, B_τ(y, …) ⊆ U n`；
  **删 `D`/`htime`**（原只传给 `TCE:358`，其 `_P6L` 版已删 Df，合同 §1.4）。
证明体照抄；结论逐字。
-/

set_option autoImplicit false
noncomputable section
open Set Filter Manifold
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open scoped Manifold ContDiff Topology ENNReal NNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

/-- **`_P6L`**：原 `terminal_scalar_limit_tendsto_atTop_of_endpoint_blowup`（`TSR:24`）。
`hgradient` 限于 `U n`；加 segment 点 `γ n t` 处移动球包含 `hU`。结论逐字。 -/
theorem terminal_scalar_limit_tendsto_atTop_of_endpoint_blowup_P6L
    (P : ℕ → OrientedThreeStage.{u}) (a s : ℕ → ℝ)
    (G : ∀ n, (P n).IncomingSlab (a n) (s n))
    (L : ∀ n, (G n).TerminalLimitMetric)
    (Q : ℕ → ℝ) (hQ : ∀ n, 0 < Q n)
    (q : ℕ → ℝ) (qbar : ℝ) (hq : ∀ᶠ n in atTop, q n ≤ qbar * Q n)
    (C : ℝ≥0)
    (U : ∀ n, Set (P n).Carrier)
    (hgradient : ∀ n, ∀ x ∈ U n, ∀ t ∈ Ioo (a n) (s n),
      q n < (G n).flow.scalar t x → ∀ v : TangentSpace ThreeModel x,
      |scalarDifferential (G n).flow t x v| ≤ C * (G n).flow.scalar t x *
        Real.sqrt ((G n).flow.scalar t x) * Real.sqrt (((G n).flow.base.metric t).inner x v v))
    (p : ∀ n, (G n).terminalRegularOpen)
    (hp : Tendsto (fun n => metricScalarAt (L n).metric (p n) / Q n) atTop atTop)
    (rho : ℝ) (ell : ℕ → ℝ) (hell : Tendsto ell atTop (𝓝 rho))
    (γ : ∀ n, Ico 0 rho → (G n).terminalRegularOpen)
    (hdist : ∀ t : Ico 0 rho, ∀ᶠ n in atTop,
      riemannianEDistOf (scaleMetric (Q n) (hQ n) (L n).metric) (γ n t) (p n) ≤
        ENNReal.ofReal (ell n - t))
    (f : Ico 0 rho → ℝ)
    (hscalar : ∀ t, Tendsto (fun n => metricScalarAt (L n).metric (γ n t) / Q n)
      atTop (𝓝 (f t)))
    (hU : ∀ t : Ico 0 rho, ∀ᶠ n in atTop, ∀ᶠ τ in 𝓝[<] s n,
      riemannianBallOf ((G n).flow.base.metric τ) (γ n t).val
        (2 * (localPropagationRadius C / Real.sqrt (2 * Q n))) ⊆ U n) :
    Tendsto f (comap (Subtype.val : Ico 0 rho → ℝ) (𝓝 rho)) atTop := by
  apply tendsto_atTop.mpr
  intro B
  let A := max qbar (max B 0) + 1
  have hA1 : 1 ≤ A := by
    have hb : (0 : ℝ) ≤ max qbar (max B 0) := (le_max_right B 0).trans (le_max_right _ _)
    dsimp only [A]
    linarith
  have hA : 0 < A := by
    have hb : (0 : ℝ) ≤ max qbar (max B 0) := (le_max_right B 0).trans (le_max_right _ _)
    dsimp only [A]
    linarith
  have hqA : qbar ≤ A := by
    dsimp only [A]
    linarith [le_max_left qbar (max B 0)]
  have hBA : B < A := by
    dsimp only [A]
    linarith [(le_max_left B 0).trans (le_max_right qbar (max B 0))]
  let d := localPropagationRadius C / (2 * Real.sqrt (2 * A))
  have hd : 0 < d := div_pos (localPropagationRadius_pos C.coe_nonneg) (by positivity)
  have hgap : Tendsto (fun t : Ico 0 rho => rho - (t : ℝ))
      (comap (Subtype.val : Ico 0 rho → ℝ) (𝓝 rho)) (𝓝 0) := by
    simpa only [sub_self] using (tendsto_const_nhds (x := rho)).sub
      (tendsto_comap : Tendsto (Subtype.val : Ico 0 rho → ℝ) _ (𝓝 rho))
  filter_upwards [hgap.eventually (Iio_mem_nhds hd)] with t ht
  by_contra hnot
  have hfB : f t < B := lt_of_not_ge hnot
  have hbound : ∀ᶠ n in atTop, metricScalarAt (L n).metric (γ n t) ≤ A * Q n := by
    filter_upwards [(hscalar t).eventually (Iio_mem_nhds (hfB.trans hBA))] with n hn
    exact (div_le_iff₀ (hQ n)).mp hn.le
  have hremain : ∀ᶠ n in atTop, ell n - (t : ℝ) < d :=
    (hell.sub_const (t : ℝ)).eventually (Iio_mem_nhds ht)
  have hhigh := hp.eventually_gt_atTop (6 * A)
  obtain ⟨n, hn, hr, hb, hlarge, hqn, hUn⟩ :=
    ((hdist t).and (hremain.and (hbound.and (hhigh.and (hq.and (hU t)))))).exists
  have hscaled : p n ∈ riemannianClosedBallOf
      (scaleMetric (Q n) (hQ n) (L n).metric) (γ n t) d :=
    hn.trans (ENNReal.ofReal_le_ofReal hr.le)
  have hradius : d = Real.sqrt (Q n) *
      (localPropagationRadius C / (2 * Real.sqrt (2 * (A * Q n)))) := by
    dsimp only [d]
    rw [show 2 * (A * Q n) = (2 * A) * Q n by ring,
      Real.sqrt_mul (by positivity : 0 ≤ 2 * A)]
    field_simp [ne_of_gt (Real.sqrt_pos.mpr (hQ n)),
      ne_of_gt (Real.sqrt_pos.mpr (by positivity : 0 < 2 * A))]
  rw [hradius, DifferentialGeometry.riemannianClosedBallOf_scaleMetric] at hscaled
  have hradle : 2 * (localPropagationRadius C / Real.sqrt (2 * (A * Q n))) ≤
      2 * (localPropagationRadius C / Real.sqrt (2 * Q n)) := by
    have hlpr : 0 ≤ localPropagationRadius C := (localPropagationRadius_pos C.coe_nonneg).le
    have hsq : Real.sqrt (2 * Q n) ≤ Real.sqrt (2 * (A * Q n)) :=
      Real.sqrt_le_sqrt (by nlinarith [hQ n])
    have hdiv := div_le_div_of_nonneg_left hlpr (Real.sqrt_pos.mpr (by linarith [hQ n])) hsq
    linarith
  have hUn' : ∀ᶠ τ in 𝓝[<] s n, riemannianBallOf ((G n).flow.base.metric τ) (γ n t).val
      (2 * (localPropagationRadius C / Real.sqrt (2 * (A * Q n)))) ⊆ U n :=
    hUn.mono fun τ hτ =>
      (DifferentialGeometry.riemannianBallOf_mono _ _ hradle).trans hτ
  have hlocal := (L n).scalar_le_on_small_ball_of_gradient_bound_P6L C (mul_pos hA (hQ n))
    (hqn.trans (mul_le_mul_of_nonneg_right hqA (hQ n).le)) (U n)
    (hgradient n) (γ n t) hUn' hb (p n) hscaled
  have hquot : metricScalarAt (L n).metric (p n) / Q n ≤ 6 * A := by
    apply (div_le_iff₀ (hQ n)).mpr
    nlinarith only [hlocal]
  exact hlarge.not_ge hquot



attribute [local instance] PointedRiemannianManifold.topology PointedRiemannianManifold.charted
  PointedRiemannianManifold.smooth PointedRiemannianManifold.t2
  PointedRiemannianManifold.sigmaCompact PointedRiemannianManifold.t2TangentBundle

private local instance {P : OrientedThreeStage.{u}} {a s : ℝ}
    {G : P.IncomingSlab a s} : SigmaCompactSpace G.terminalRegularOpen :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen ThreeModel G.terminalRegularOpen.isOpen)

/-- **`_P6L`**：原 `terminal_pointed_scalar_tendsto_atTop_of_endpoint_blowup`（`TSR:104`）。
`hgradient` 限于 `U n`；加 `hU`（同 `:24_P6L`）。结论逐字。 -/
theorem terminal_pointed_scalar_tendsto_atTop_of_endpoint_blowup_P6L
    (P : ℕ → OrientedThreeStage.{u}) (a s : ℕ → ℝ)
    (G : ∀ n, (P n).IncomingSlab (a n) (s n))
    (L : ∀ n, (G n).TerminalLimitMetric)
    (Q : ℕ → ℝ) (hQ : ∀ n, 0 < Q n)
    (q : ℕ → ℝ) (qbar : ℝ) (hq : ∀ᶠ n in atTop, q n ≤ qbar * Q n)
    (C : ℝ≥0)
    (U : ∀ n, Set (P n).Carrier)
    (hgradient : ∀ n, ∀ x ∈ U n, ∀ t ∈ Ioo (a n) (s n),
      q n < (G n).flow.scalar t x → ∀ v : TangentSpace ThreeModel x,
      |scalarDifferential (G n).flow t x v| ≤ C * (G n).flow.scalar t x *
        Real.sqrt ((G n).flow.scalar t x) * Real.sqrt (((G n).flow.base.metric t).inner x v v))
    (basepoint p : ∀ n, (G n).terminalRegularOpen)
    (hp : Tendsto (fun n => metricScalarAt (L n).metric (p n) / Q n) atTop atTop)
    (rho : ℝ) (ell : ℕ → ℝ) (hell : Tendsto ell atTop (𝓝 rho))
    (γ : ∀ n, Ico 0 rho → (G n).terminalRegularOpen)
    (hdist : ∀ t : Ico 0 rho, ∀ᶠ n in atTop,
      riemannianEDistOf (scaleMetric (Q n) (hQ n) (L n).metric) (γ n t) (p n) ≤
        ENNReal.ofReal (ell n - t))
    (limit : PointedRiemannianManifold.{u, 0, 0} ThreeModel)
    (maps : PointedRiemannianConvergenceMaps
      ({ obj := fun n =>
          { M := (G n).terminalRegularOpen
            topology := inferInstance
            charted := inferInstance
            smooth := inferInstance
            sigmaCompact := inferInstance
            t2 := inferInstance
            t2TangentBundle := inferInstance
            basepoint := basepoint n
            metric := scaleMetric (Q n) (hQ n) (L n).metric } } :
        PointedRiemannianSeq.{u, 0, 0} ThreeModel) limit id)
    (metricConvergence : MetricConvergenceData maps)
    (hcanonical : ∀ n,
      metricConvergence.domain n = CanonicalMetricCompactness.canonicalSourceData maps n)
    (curve : Ico 0 rho → limit.M)
    (hstay : ∀ t : Ico 0 rho, ∀ᶠ n in atTop, γ n t ∈ maps.target n)
    (hconv : ∀ t : Ico 0 rho, Tendsto (fun n => (maps.partialDiffeomorph n).symm (γ n t))
      atTop (𝓝 (curve t)))
    (hU : ∀ t : Ico 0 rho, ∀ᶠ n in atTop, ∀ᶠ τ in 𝓝[<] s n,
      riemannianBallOf ((G n).flow.base.metric τ) (γ n t).val
        (2 * (localPropagationRadius C / Real.sqrt (2 * Q n))) ⊆ U n) :
    Tendsto (fun t => metricScalarAt limit.metric (curve t))
      (comap (Subtype.val : Ico 0 rho → ℝ) (𝓝 rho)) atTop := by
  refine terminal_scalar_limit_tendsto_atTop_of_endpoint_blowup_P6L P a s G L Q hQ q qbar hq C
    U hgradient p hp rho ell hell γ hdist _ ?_ hU
  intro t
  have ht := pointedScalar_tendsto_of_inverse_tendsto metricConvergence hcanonical
    (fun n => γ n t) (hstay t) (hconv t)
  convert ht using 1
  funext n
  change metricScalarAt (L n).metric (γ n t) / Q n =
    metricScalarAt (scaleMetric (Q n) (hQ n) (L n).metric) (γ n t)
  rw [metricScalarAt_scaleMetric]
  ring


/-- **`_P6L`**：原 `exists_isometric_terminal_scalar_blowup_curve_of_minimizing_segments`
（`TSR:343`）。`hgradient` 限于 `U n`；加 segment 点处移动球包含 `hU`（eventually in n，
∀ t ∈ [0, ell n]；只在末尾调 `:24_P6L` 时用于 `t < ell (φ k)`）。结论逐字。 -/
theorem exists_isometric_terminal_scalar_blowup_curve_of_minimizing_segments_P6L
    (P : ℕ → OrientedThreeStage.{u}) (a s : ℕ → ℝ)
    (G : ∀ n, (P n).IncomingSlab (a n) (s n))
    (L : ∀ n, (G n).TerminalLimitMetric)
    (Q : ℕ → ℝ) (hQ : ∀ n, 0 < Q n)
    (q : ℕ → ℝ) (qbar : ℝ) (hq : ∀ᶠ n in atTop, q n ≤ qbar * Q n)
    (C : ℝ≥0)
    (U : ∀ n, Set (P n).Carrier)
    (hgradient : ∀ n, ∀ x ∈ U n, ∀ t ∈ Ioo (a n) (s n),
      q n < (G n).flow.scalar t x → ∀ v : TangentSpace ThreeModel x,
      |scalarDifferential (G n).flow t x v| ≤ C * (G n).flow.scalar t x *
        Real.sqrt ((G n).flow.scalar t x) * Real.sqrt (((G n).flow.base.metric t).inner x v v))
    (basepoint : ∀ n, (G n).terminalRegularOpen)
    (limit : PointedRiemannianManifold.{u, 0, 0} ThreeModel)
    (σ : ℕ → ℕ) (hσ : StrictMono σ)
    (maps : PointedRiemannianConvergenceMaps
      ({ obj := fun n =>
          { M := (G n).terminalRegularOpen
            basepoint := basepoint n
            metric := scaleMetric (Q n) (hQ n) (L n).metric } } :
        PointedRiemannianSeq.{u, 0, 0} ThreeModel) limit σ)
    (Mconv : MetricConvergenceData maps)
    (hcanonical : ∀ n, Mconv.domain n = CanonicalMetricCompactness.canonicalSourceData maps n)
    {rho : ℝ} (hrho : 0 < rho)
    (r ell : ℕ → ℝ) (hr : ∀ n, 0 < r n) (hell : ∀ n, 0 ≤ ell n)
    (hrconv : Tendsto r atTop (𝓝 rho)) (hellconv : Tendsto ell atTop (𝓝 rho))
    (htarget : ∀ n, riemannianBallOf (scaleMetric (Q (σ n)) (hQ (σ n)) (L (σ n)).metric)
      (basepoint (σ n)) (r n) ⊆ maps.target n)
    (hlower : ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop,
      ∀ x ∈ maps.source n, ∀ v : TangentSpace ThreeModel x,
        (1 - ε) * limit.metric.inner x v v ≤
          (scaleMetric (Q (σ n)) (hQ (σ n)) (L (σ n)).metric).inner (maps.partialDiffeomorph n x)
            (mfderiv ThreeModel ThreeModel (maps.partialDiffeomorph n) x v)
            (mfderiv ThreeModel ThreeModel (maps.partialDiffeomorph n) x v))
    (hcompact : ∀ R : ℝ, 0 ≤ R → R < rho →
      IsCompact (riemannianClosedBallOf limit.metric limit.basepoint R))
    (hradial : ∀ x : limit.M, riemannianEDistOf limit.metric limit.basepoint x < ENNReal.ofReal rho)
    (γ : ∀ n, ℝ → (G (σ n)).terminalRegularOpen)
    (hγ : ∀ n, ContMDiffOn 𝓘(ℝ, ℝ) ThreeModel 1 (γ n) (Icc 0 (ell n)))
    (hstart : ∀ n, γ n 0 = basepoint (σ n))
    (hmin : ∀ n, ∀ t ∈ Icc 0 (ell n), ∀ u ∈ Icc 0 (ell n),
      riemannianEDistOf (scaleMetric (Q (σ n)) (hQ (σ n)) (L (σ n)).metric)
        (γ n t) (γ n u) = ENNReal.ofReal |t - u|)
    (hhigh : Tendsto (fun n => metricScalarAt (L (σ n)).metric (γ n (ell n)) / Q (σ n))
      atTop atTop)
    (hU : ∀ᶠ n in atTop, ∀ t ∈ Icc 0 (ell n), ∀ᶠ τ in 𝓝[<] s (σ n),
      riemannianBallOf ((G (σ n)).flow.base.metric τ) (γ n t).val
        (2 * (localPropagationRadius C / Real.sqrt (2 * Q (σ n)))) ⊆ U (σ n)) :
    let _ : EMetricSpace limit.M := limit.emetricSpace
    ∃ (φ : ℕ → ℕ) (g : C(Ico 0 rho, limit.M)), StrictMono φ ∧ Isometry g ∧
      g ⟨0, le_rfl, hrho⟩ = limit.basepoint ∧
      (∀ K : Set (Ico 0 rho), IsCompact K →
        TendstoUniformlyOn (fun n (t : Ico 0 rho) =>
          (maps.partialDiffeomorph (φ n)).symm (γ (φ n) t)) g atTop K) ∧
      (∀ t : Ico 0 rho, ∀ᶠ n in atTop, γ (φ n) t ∈ maps.target (φ n)) ∧
      (∀ t : Ico 0 rho, Tendsto (fun n => metricScalarAt (L (σ (φ n))).metric
        (γ (φ n) t) / Q (σ (φ n))) atTop (𝓝 (metricScalarAt limit.metric (g t)))) ∧
      Tendsto g (comap (Subtype.val : Ico 0 rho → ℝ) (𝓝 rho)) (cocompact limit.M) ∧
      (∀ x : limit.M, ¬ Tendsto g (comap (Subtype.val : Ico 0 rho → ℝ) (𝓝 rho)) (𝓝 x)) ∧
      Tendsto (fun t => metricScalarAt limit.metric (g t))
        (comap (Subtype.val : Ico 0 rho → ℝ) (𝓝 rho)) atTop := by
  let _ : NeZero (Module.finrank ℝ ThreeSpace) := ⟨by simp [ThreeSpace]⟩
  have hupper : ∀ K : Set limit.M, IsCompact K → ∀ D : ℝ, 1 < D → ∀ᶠ n in atTop,
      ∀ x ∈ K, ∀ v : TangentSpace ThreeModel x,
        (scaleMetric (Q (σ n)) (hQ (σ n)) (L (σ n)).metric).inner (maps.partialDiffeomorph n x)
          (mfderiv ThreeModel ThreeModel (maps.partialDiffeomorph n) x v)
          (mfderiv ThreeModel ThreeModel (maps.partialDiffeomorph n) x v) ≤
            D ^ 2 * limit.metric.inner x v v := by
    intro K hK D hD
    obtain ⟨N, hN⟩ := Perelman.KappaSolutions.exists_pointed_full_ambient_quadratic_control
      Mconv (fun n => by rw [hcanonical n]; rfl) K hK (D ^ 2 - 1) (by nlinarith)
    filter_upwards [eventually_ge_atTop N] with n hn
    intro x hx v
    have hh := (abs_le.mp ((hN n hn).2 x hx v)).2
    change (scaleMetric (Q (σ n)) (hQ (σ n)) (L (σ n)).metric).inner (maps.partialDiffeomorph n x)
      (mfderiv ThreeModel ThreeModel (maps.partialDiffeomorph n) x v)
      (mfderiv ThreeModel ThreeModel (maps.partialDiffeomorph n) x v) - limit.metric.inner x v v ≤
        (D ^ 2 - 1) * limit.metric.inner x v v at hh
    nlinarith
  let _ : EMetricSpace limit.M := limit.emetricSpace
  obtain ⟨φ, g, hφ, hg, hbase, hconv, hescape, hmissing⟩ :=
    maps.exists_isometric_segment_subseq_limit_with_missing_endpoint hrho r ell hr hell hrconv
      hellconv
      htarget hlower hupper hcompact hradial γ hγ hstart hmin
  have hstay (t : Ico 0 rho) : ∀ᶠ n in atTop, γ (φ n) t ∈ maps.target (φ n) := by
    filter_upwards [hφ.tendsto_atTop (hrconv.eventually_const_lt t.property.2),
      hφ.tendsto_atTop (hellconv.eventually_const_lt t.property.2)] with n hn hn'
    apply htarget (φ n)
    change riemannianEDistOf (scaleMetric (Q (σ (φ n))) (hQ (σ (φ n))) (L (σ (φ n))).metric)
      (basepoint (σ (φ n))) (γ (φ n) t) < ENNReal.ofReal (r (φ n))
    have hd := hmin (φ n) 0 ⟨le_rfl, t.property.1.trans hn'.le⟩ t ⟨t.property.1, hn'.le⟩
    rw [hstart] at hd
    simp only [zero_sub, abs_neg, abs_of_nonneg t.property.1] at hd
    rw [hd]
    exact (ENNReal.ofReal_lt_ofReal_iff (hr (φ n))).mpr hn
  let maps' := maps.compSubseq φ hφ
  have hcanonical' (n : ℕ) : (Mconv.compSubseq φ hφ).domain n =
      CanonicalMetricCompactness.canonicalSourceData maps' n := by
    change (Mconv.domain (φ n)).compSubseq φ hφ n = _
    rw [hcanonical (φ n)]
    rfl
  have hlimit (t : Ico 0 rho) : Tendsto (fun n => metricScalarAt (L (σ (φ n))).metric
      (γ (φ n) t) / Q (σ (φ n))) atTop (𝓝 (metricScalarAt limit.metric (g t))) := by
    have ht := pointedScalar_tendsto_of_inverse_tendsto (Mconv.compSubseq φ hφ) hcanonical'
      (fun n => γ (φ n) t) (hstay t)
      ((hconv {t} isCompact_singleton).tendsto_at (mem_singleton t))
    convert ht using 1
    funext n
    change metricScalarAt (L (σ (φ n))).metric (γ (φ n) t) / Q (σ (φ n)) =
      metricScalarAt (scaleMetric (Q (σ (φ n))) (hQ (σ (φ n))) (L (σ (φ n))).metric) (γ (φ n) t)
    rw [metricScalarAt_scaleMetric]
    ring
  have hdist (t : Ico 0 rho) : ∀ᶠ n in atTop,
      riemannianEDistOf (scaleMetric (Q (σ (φ n))) (hQ (σ (φ n))) (L (σ (φ n))).metric)
        (γ (φ n) t) (γ (φ n) (ell (φ n))) ≤ ENNReal.ofReal (ell (φ n) - t) := by
    filter_upwards [hφ.tendsto_atTop (hellconv.eventually_const_lt t.property.2)] with n hn
    change (t : ℝ) < ell (φ n) at hn
    have hd := hmin (φ n) t ⟨t.property.1, hn.le⟩ (ell (φ n)) ⟨hell (φ n), le_rfl⟩
    simpa only [abs_of_nonpos (sub_nonpos.mpr hn.le), neg_sub] using hd.le
  refine ⟨φ, g, hφ, hg, hbase, hconv, hstay, hlimit, hescape, hmissing, ?_⟩
  have hUφ : ∀ t : Ico 0 rho, ∀ᶠ k in atTop, ∀ᶠ τ in 𝓝[<] s (σ (φ k)),
      riemannianBallOf ((G (σ (φ k))).flow.base.metric τ) (γ (φ k) t).val
        (2 * (localPropagationRadius C / Real.sqrt (2 * Q (σ (φ k))))) ⊆ U (σ (φ k)) := by
    intro t
    filter_upwards [hφ.tendsto_atTop.eventually hU,
      hφ.tendsto_atTop (hellconv.eventually_const_lt t.property.2)] with k hk hk'
    change (t : ℝ) < ell (φ k) at hk'
    exact hk t ⟨t.property.1, hk'.le⟩
  exact terminal_scalar_limit_tendsto_atTop_of_endpoint_blowup_P6L
    (fun n => P (σ (φ n))) (fun n => a (σ (φ n))) (fun n => s (σ (φ n)))
    (fun n => G (σ (φ n))) (fun n => L (σ (φ n)))
    (fun n => Q (σ (φ n))) (fun n => hQ (σ (φ n)))
    (fun n => q (σ (φ n))) qbar ((hσ.comp hφ).tendsto_atTop.eventually hq) C
    (fun n => U (σ (φ n))) (fun n => hgradient (σ (φ n))) (fun n => γ (φ n) (ell (φ n)))
    (hhigh.comp hφ.tendsto_atTop) rho (ell ∘ φ) (hellconv.comp hφ.tendsto_atTop)
    (fun n t => γ (φ n) t) hdist (fun t => metricScalarAt limit.metric (g t)) hlimit hUφ

/-- **`_P6L`**：原 `exists_isometric_terminal_scalar_blowup_curve_of_scalar_escape`
（`TSR:490`）。`hgradient` 限于 `U n`；加先验半径 `Rad`（`rho < Rad`）与 `hU`：基点的
`Q·L`-距离 `< Rad` 的点处移动球包含（成员关系：segment 点 `γ n t` 距基点 `= t ≤ ell n`，
`ell n → rho < Rad`）；**删 `D`/`htime`**（只传给 `TCE:358`，其 `_P6L` 版无 Df）。结论逐字。 -/
theorem exists_isometric_terminal_scalar_blowup_curve_of_scalar_escape_P6L
    (P : ℕ → OrientedThreeStage.{u}) (a s : ℕ → ℝ)
    (G : ∀ n, (P n).IncomingSlab (a n) (s n))
    (L : ∀ n, (G n).TerminalLimitMetric)
    (Q : ℕ → ℝ) (hQ : ∀ n, 0 < Q n)
    (q : ℕ → ℝ) (qbar : ℝ) (hq : ∀ᶠ n in atTop, q n ≤ qbar * Q n)
    (C : ℝ≥0)
    (U : ∀ n, Set (P n).Carrier)
    (hgradient : ∀ n, ∀ x ∈ U n, ∀ t ∈ Ioo (a n) (s n),
      q n < (G n).flow.scalar t x → ∀ v : TangentSpace ThreeModel x,
      |scalarDifferential (G n).flow t x v| ≤ C * (G n).flow.scalar t x *
        Real.sqrt ((G n).flow.scalar t x) * Real.sqrt (((G n).flow.base.metric t).inner x v v))
    (basepoint : ∀ n, (G n).terminalRegularOpen)
    (limit : PointedRiemannianManifold.{u, 0, 0} ThreeModel)
    (σ : ℕ → ℕ) (hσ : StrictMono σ)
    (maps : PointedRiemannianConvergenceMaps
      ({ obj := fun n =>
          { M := (G n).terminalRegularOpen
            basepoint := basepoint n
            metric := scaleMetric (Q n) (hQ n) (L n).metric } } :
        PointedRiemannianSeq.{u, 0, 0} ThreeModel) limit σ)
    (Mconv : MetricConvergenceData maps)
    (hcanonical : ∀ n, Mconv.domain n = CanonicalMetricCompactness.canonicalSourceData maps n)
    {rho : ℝ} (hrho : 0 < rho)
    (r : ℕ → ℝ) (hr : ∀ n, 0 < r n) (hrconv : Tendsto r atTop (𝓝 rho))
    (htarget : ∀ n, riemannianBallOf (scaleMetric (Q (σ n)) (hQ (σ n)) (L (σ n)).metric)
      (basepoint (σ n)) (r n) ⊆ maps.target n)
    (hlower : ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop,
      ∀ x ∈ maps.source n, ∀ v : TangentSpace ThreeModel x,
        (1 - ε) * limit.metric.inner x v v ≤
          (scaleMetric (Q (σ n)) (hQ (σ n)) (L (σ n)).metric).inner (maps.partialDiffeomorph n x)
            (mfderiv ThreeModel ThreeModel (maps.partialDiffeomorph n) x v)
            (mfderiv ThreeModel ThreeModel (maps.partialDiffeomorph n) x v))
    (hcompact : ∀ R : ℝ, 0 ≤ R → R < rho →
      IsCompact (riemannianClosedBallOf limit.metric limit.basepoint R))
    (hradial : ∀ x : limit.M, riemannianEDistOf limit.metric limit.basepoint x < ENNReal.ofReal rho)
    (hbaseScalar : ∀ n, metricScalarAt (L n).metric (basepoint n) ≤ Q n)
    (z : ∀ n, (G (σ n)).terminalRegularOpen)
    (hfinite : ∀ n, riemannianEDistOf (scaleMetric (Q (σ n)) (hQ (σ n)) (L (σ n)).metric)
      (basepoint (σ n)) (z n) ≠ ⊤)
    (hdist : Tendsto (fun n => (riemannianEDistOf
      (scaleMetric (Q (σ n)) (hQ (σ n)) (L (σ n)).metric) (basepoint (σ n)) (z n)).toReal)
      atTop (𝓝 rho))
    (hhigh : Tendsto (fun n => metricScalarAt (L (σ n)).metric (z n) / Q (σ n)) atTop atTop)
    (hinner : ∀ R : ℝ, 0 < R → R < rho → ∃ B : ℝ,
      ∀ᶠ n in atTop, ∀ y : (G (σ n)).terminalRegularOpen,
        riemannianEDistOf (scaleMetric (Q (σ n)) (hQ (σ n)) (L (σ n)).metric)
          (basepoint (σ n)) y < ENNReal.ofReal R →
            metricScalarAt (L (σ n)).metric y / Q (σ n) ≤ B)
    {Rad : ℝ} (hRad : rho < Rad)
    (hU : ∀ n, ∀ y : (G n).terminalRegularOpen,
      riemannianEDistOf (scaleMetric (Q n) (hQ n) (L n).metric) (basepoint n) y <
        ENNReal.ofReal Rad → ∀ᶠ τ in 𝓝[<] s n,
        riemannianBallOf ((G n).flow.base.metric τ) y.val
          (2 * (localPropagationRadius C / Real.sqrt (2 * Q n))) ⊆ U n) :
    let _ : EMetricSpace limit.M := limit.emetricSpace
    ∃ κ : ℕ → ℕ, StrictMono κ ∧
      ∃ (A ell : ℕ → ℝ) (y : ∀ n, (G (σ (κ n))).terminalRegularOpen)
        (γ : ∀ n, ℝ → (G (σ (κ n))).terminalRegularOpen),
        (∀ n, A n = min ((n : ℝ) + 2)
          (metricScalarAt (L (σ (κ n))).metric (z (κ n)) / Q (σ (κ n)))) ∧
        Tendsto A atTop atTop ∧ Tendsto ell atTop (𝓝 rho) ∧
        (∀ n, 0 < ell n) ∧
        (∀ n, metricScalarAt (L (σ (κ n))).metric (y n) / Q (σ (κ n)) = A n) ∧
        (∀ n, riemannianEDistOf (scaleMetric (Q (σ (κ n))) (hQ (σ (κ n))) (L (σ (κ n))).metric)
          (basepoint (σ (κ n))) (y n) = ENNReal.ofReal (ell n)) ∧
        (∀ n, ENNReal.ofReal (ell n) ≤ riemannianEDistOf
          (scaleMetric (Q (σ (κ n))) (hQ (σ (κ n))) (L (σ (κ n))).metric)
          (basepoint (σ (κ n))) (z (κ n))) ∧
        (∀ n, γ n 0 = basepoint (σ (κ n)) ∧ γ n (ell n) = y n) ∧
        (∀ n, ContMDiffOn 𝓘(ℝ, ℝ) ThreeModel ∞ (γ n) (Icc 0 (ell n))) ∧
        (∀ n, ∀ t ∈ Ico 0 (ell n),
          metricScalarAt (L (σ (κ n))).metric (γ n t) / Q (σ (κ n)) < A n) ∧
        (∀ n, ∀ t ∈ Icc 0 (ell n),
          metricScalarAt (L (σ (κ n))).metric (γ n t) / Q (σ (κ n)) ≤ A n) ∧
        (∀ n, ∀ t ∈ Icc 0 (ell n), ∀ u ∈ Icc 0 (ell n),
          riemannianEDistOf (scaleMetric (Q (σ (κ n))) (hQ (σ (κ n))) (L (σ (κ n))).metric)
            (γ n t) (γ n u) = ENNReal.ofReal |t - u|) ∧
        ∃ (φ : ℕ → ℕ) (g : C(Ico 0 rho, limit.M)), StrictMono φ ∧ Isometry g ∧
          g ⟨0, le_rfl, hrho⟩ = limit.basepoint ∧
          (∀ K : Set (Ico 0 rho), IsCompact K →
            TendstoUniformlyOn (fun n (t : Ico 0 rho) =>
              (maps.partialDiffeomorph (κ (φ n))).symm (γ (φ n) t)) g atTop K) ∧
          (∀ t : Ico 0 rho, ∀ᶠ n in atTop, γ (φ n) t ∈ maps.target (κ (φ n))) ∧
          (∀ t : Ico 0 rho, Tendsto (fun n => metricScalarAt (L (σ (κ (φ n)))).metric
            (γ (φ n) t) / Q (σ (κ (φ n)))) atTop (𝓝 (metricScalarAt limit.metric (g t)))) ∧
          Tendsto g (comap (Subtype.val : Ico 0 rho → ℝ) (𝓝 rho)) (cocompact limit.M) ∧
          (∀ x : limit.M, ¬ Tendsto g (comap (Subtype.val : Ico 0 rho → ℝ) (𝓝 rho)) (𝓝 x)) ∧
          Tendsto (fun t => metricScalarAt limit.metric (g t))
            (comap (Subtype.val : Ico 0 rho → ℝ) (𝓝 rho)) atTop := by
  obtain ⟨κ, hκ, A, ell, y, γ, hA, hAlim, helllim, hell, hy, hlength, hshort,
      hends, hγ, hbelow, hbound, hmin⟩ :=
    exists_terminal_minimizing_segments_at_scalar_escape_radius_P6L
      (fun n => P (σ n)) (fun n => a (σ n)) (fun n => s (σ n))
      (fun n => G (σ n)) (fun n => L (σ n)) (fun n => basepoint (σ n)) z
      (fun n => Q (σ n)) (fun n => hQ (σ n))
      (fun n => hbaseScalar (σ n)) hfinite hrho hdist hhigh hinner
  let maps' := maps.compSubseq κ hκ
  have hcanonical' (n : ℕ) : (Mconv.compSubseq κ hκ).domain n =
      CanonicalMetricCompactness.canonicalSourceData maps' n := by
    change (Mconv.domain (κ n)).compSubseq κ hκ n = _
    rw [hcanonical (κ n)]
    rfl
  have hhigh' : Tendsto (fun n => metricScalarAt (L (σ (κ n))).metric (γ n (ell n)) / Q (σ (κ n)))
      atTop atTop := by
    simpa only [(hends _).2, hy] using hAlim
  have hU' : ∀ᶠ n in atTop, ∀ t ∈ Icc 0 (ell n), ∀ᶠ τ in 𝓝[<] s (σ (κ n)),
      riemannianBallOf ((G (σ (κ n))).flow.base.metric τ) (γ n t).val
        (2 * (localPropagationRadius C / Real.sqrt (2 * Q (σ (κ n))))) ⊆ U (σ (κ n)) := by
    filter_upwards [helllim.eventually_lt_const hRad] with n hn t ht
    apply hU (σ (κ n)) (γ n t)
    have hd := hmin n 0 ⟨le_rfl, (hell n).le⟩ t ht
    rw [(hends n).1] at hd
    rw [hd, zero_sub, abs_neg, abs_of_nonneg ht.1]
    exact (ENNReal.ofReal_lt_ofReal_iff (hrho.trans hRad)).mpr (ht.2.trans_lt hn)
  let _ : EMetricSpace limit.M := limit.emetricSpace
  obtain ⟨φ, g, hφ, hg, hbase, hconv, hstay, hscalar, hescape, hmissing, hblowup⟩ :=
    exists_isometric_terminal_scalar_blowup_curve_of_minimizing_segments_P6L
      P a s G L Q hQ q qbar hq C U hgradient basepoint limit (σ ∘ κ) (hσ.comp hκ)
      maps' (Mconv.compSubseq κ hκ) hcanonical' hrho (r ∘ κ) ell
      (fun n => hr (κ n)) (fun n => (hell n).le) (hrconv.comp hκ.tendsto_atTop) helllim
      (fun n => htarget (κ n))
      (fun ε hε => hκ.tendsto_atTop.eventually (hlower ε hε)) hcompact hradial
      γ (fun n => (hγ n).of_le (by simp)) (fun n => (hends n).1) hmin hhigh' hU'
  exact ⟨κ, hκ, A, ell, y, γ, hA, hAlim, helllim, hell, hy, hlength, hshort,
    hends, hγ, hbelow, hbound, hmin, φ, g, hφ, hg, hbase, hconv, hstay, hscalar,
    hescape, hmissing, hblowup⟩

/-- consumer：原 `TSR:24` 的全局形（carrier 全局 `hgradient`）由 `_P6L` 版（`U n = univ`）推出。 -/
example (P : ℕ → OrientedThreeStage.{u}) (a s : ℕ → ℝ)
    (G : ∀ n, (P n).IncomingSlab (a n) (s n))
    (L : ∀ n, (G n).TerminalLimitMetric)
    (Q : ℕ → ℝ) (hQ : ∀ n, 0 < Q n)
    (q : ℕ → ℝ) (qbar : ℝ) (hq : ∀ᶠ n in atTop, q n ≤ qbar * Q n)
    (C : ℝ≥0)
    (hgradient : ∀ n, ∀ x : (P n).Carrier, ∀ t ∈ Ioo (a n) (s n),
      q n < (G n).flow.scalar t x → ∀ v : TangentSpace ThreeModel x,
      |scalarDifferential (G n).flow t x v| ≤ C * (G n).flow.scalar t x *
        Real.sqrt ((G n).flow.scalar t x) * Real.sqrt (((G n).flow.base.metric t).inner x v v))
    (p : ∀ n, (G n).terminalRegularOpen)
    (hp : Tendsto (fun n => metricScalarAt (L n).metric (p n) / Q n) atTop atTop)
    (rho : ℝ) (ell : ℕ → ℝ) (hell : Tendsto ell atTop (𝓝 rho))
    (γ : ∀ n, Ico 0 rho → (G n).terminalRegularOpen)
    (hdist : ∀ t : Ico 0 rho, ∀ᶠ n in atTop,
      riemannianEDistOf (scaleMetric (Q n) (hQ n) (L n).metric) (γ n t) (p n) ≤
        ENNReal.ofReal (ell n - t))
    (f : Ico 0 rho → ℝ)
    (hscalar : ∀ t, Tendsto (fun n => metricScalarAt (L n).metric (γ n t) / Q n)
      atTop (𝓝 (f t))) :
    Tendsto f (comap (Subtype.val : Ico 0 rho → ℝ) (𝓝 rho)) atTop :=
  terminal_scalar_limit_tendsto_atTop_of_endpoint_blowup_P6L P a s G L Q hQ q qbar hq C
    (fun _ => univ) (fun n x _ => hgradient n x) p hp rho ell hell γ hdist f hscalar
    (fun _ => Eventually.of_forall fun _ => Eventually.of_forall fun _ => subset_univ _)

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
