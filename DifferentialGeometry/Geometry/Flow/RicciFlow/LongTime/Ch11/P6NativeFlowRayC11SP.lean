import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6NativeNzeroFlowC11SP

set_option autoImplicit false

/-!
# G9′：`hnzero` ⇐ ray 点列上的 cone 点 flow（O-CH11-NATIVE-NJ，后缀 `_C11SP`）

lead 00:0x 裁定 (b)：SPINE-B G9 的车道内 binder `hflowN` 可以收窄，但不改 SPINE-B 文件。本文件：
* `cone_flow_exclusion_adm_C11SP`：A2 史无关 exclusion 的孪生，`hflow` 只对满足平移封闭谓词 `Adm` 的
  点列要求（A2 原定理签名不动）。
* `puncturedConeEnd_ray_C11SP`：A1 cone end 的孪生，保留 `xW n = ray (times n)`。
* `native_hnzero_of_flowRay_C11SP`（PROVISIONAL[hflowN′]）：结论 = `hnzero` 体（G9 逐字），
  `hflowN′` 的 flow 子句只对 ray 点列要求。
-/

noncomputable section

open Set Filter DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Collapse
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.PDE.RicciFlow DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open GC.GeneralFlow
open scoped Manifold ContDiff Topology ENNReal NNReal

namespace GC.LongTime.Ch11

universe u

attribute [local instance] PointedRiemannianManifold.topology PointedRiemannianManifold.charted
  PointedRiemannianManifold.smooth PointedRiemannianManifold.t2
  PointedRiemannianManifold.sigmaCompact PointedRiemannianManifold.t2TangentBundle

/-- pointed limit 的 `RegularSpace`（同 A2 / A1 的 private local instance；W 形 metric 需要）。 -/
private local instance pointedLimitRegular_FR_C11SP
    (L : PointedRiemannianManifold.{u, 0, 0} ThreeModel) : RegularSpace L.M := by
  let _ : LocallyCompactSpace L.M := ChartedSpace.locallyCompactSpace ThreeSpace L.M
  infer_instance

private theorem isCompact_closedBall_of_lt_dist_puncture_FR_C11SP {W : Type*} [MetricSpace W]
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

/-- A2 `guard_cone_flow_exclusion_C11SP` 的孪生：`hflow` 只对满足 `Adm`（对平移封闭）的点列要求；
cone 端点点列本身满足 `Adm`。证明逐字（`hflow` 只在尾段 `xW (· + N)` 上调用一次）。 -/
theorem cone_flow_exclusion_adm_C11SP
    (Pl : PointedRiemannianManifold.{u, 0, 0} ThreeModel)
    (W : TopologicalSpace.Opens Pl.M) (hWc : PathConnectedSpace W)
    (Adm : (ℕ → W) → Prop) (hAdm : ∀ (xW : ℕ → W) (N : ℕ), Adm xW → Adm (fun n => xW (n + N)))
    (hflow : ∀ (xW : ℕ → W), Adm xW → ∀ (R₀ : ℝ), 0 < R₀ →
        (∀ n, 2 ≤ metricScalarAt Pl.metric (xW n : Pl.M)) →
        Tendsto (fun n => metricScalarAt Pl.metric (xW n : Pl.M)) atTop atTop →
        (∀ n, IsCompact (riemannianClosedBallOf (Pl.metric.restrictOpen W) (xW n)
          (4 * R₀ / Real.sqrt (metricScalarAt Pl.metric (xW n : Pl.M))))) →
        ∃ (j : ℕ → ℕ) (_ : StrictMono j) (A₂ : ℕ → ℝ) (hA₂ : ∀ n, 0 < A₂ n),
          Tendsto (fun n => A₂ n / metricScalarAt Pl.metric (xW (j n) : Pl.M)) atTop (𝓝 1) ∧
          ∃ (P₂ : PointedRiemannianManifold.{u, 0, 0} ThreeModel)
            (V : TopologicalSpace.Opens P₂.M)
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
              (∀ᶠ n in atTop,
                riemannianClosedBallOf (g 0) ⟨P₂.basepoint, hp⟩ r ⊆ (C n).source ∧
                riemannianClosedBallOf (scaleMetric (A₂ n) (hA₂ n) (Pl.metric.restrictOpen W))
                  (xW (j n)) (r / 4) ⊆
                    (C n) '' riemannianClosedBallOf (g 0) ⟨P₂.basepoint, hp⟩ r) ∧
              ∀ eta : ℝ, 0 < eta → ∀ᶠ n in atTop,
                ∀ a ∈ riemannianClosedBallOf (g 0) ⟨P₂.basepoint, hp⟩ r,
                ∀ b ∈ riemannianClosedBallOf (g 0) ⟨P₂.basepoint, hp⟩ r,
                  |(riemannianEDistOf
                      (scaleMetric (A₂ n) (hA₂ n) (Pl.metric.restrictOpen W))
                      (C n a) (C n b)).toReal -
                    (riemannianEDistOf (g 0) a b).toReal| < eta) :
    let _ : PathConnectedSpace W := hWc
    let _ : PseudoMetricSpace W := (Pl.metric.restrictOpen W).toPseudoMetricSpace
    let _ : MetricSpace W := MetricSpace.ofT0PseudoMetricSpace W
    ∀ (qW : UniformSpace.Completion W) (delta : ℝ), 0 < delta →
      IsCompact (Metric.closedBall qW delta) →
      Metric.closedBall qW delta ⊆
        insert qW (range (fun z : W => (z : UniformSpace.Completion W))) →
      Nonempty (DifferentialGeometry.Toponogov.PuncturedConeApproximation qW delta) →
      ∀ xW : ℕ → W, Adm xW →
      Tendsto (fun n => (xW n : UniformSpace.Completion W)) atTop (𝓝 qW) →
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
  intro qW delta hdelta hK hcover hcone xW hadm hx hQW c hc hlower hupper
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
    exact isCompact_closedBall_of_lt_dist_puncture_FR_C11SP hK hcover (xW' n) (by linarith)
      (by linarith)
  have hQW' : Tendsto (fun n => metricScalarAt Pl.metric (xW' n : Pl.M)) atTop atTop :=
    hQW.comp (tendsto_add_atTop_nat N)
  obtain ⟨j, hj, A₂, hA₂, hratio, P₂, V, hp, hpath, tau, htau, g, hgb, hsol, hnonneg, hbase₂,
      C, hcenter, r, hr, hcpt, hcap, hdist⟩ :=
    hflow xW' (hAdm xW N hadm) R₀ hR₀ (fun n => (hN' n).1) hQW' hcompactW
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

/-- A1 `guard_puncturedConeEnd_C11SP` 的孪生：保留 `coneEnd_of_operatorNonneg_neckedRay_C11SP` 已给出的
"cone 端点点列在 ray 上"（`xW n = ray (times n)`，`times n → rho`）。 -/
theorem puncturedConeEnd_ray_C11SP :
    ∀ (Pl : PointedRiemannianManifold.{u, 0, 0} ThreeModel) (rho : ℝ) (hrho : 0 < rho)
      (ray : C(Ico (0 : ℝ) rho, Pl.M)),
      (let _ : EMetricSpace Pl.M := Pl.emetricSpace;
        metricScalarAt Pl.metric Pl.basepoint = 1 ∧
        (∀ z : Pl.M, metricAlgebraicCurvatureTensorAt Pl.metric z ∈
          algebraicCurvatureOperatorNonnegativeCone) ∧
        (∀ y : Pl.M, riemannianEDistOf Pl.metric Pl.basepoint y < ENNReal.ofReal rho) ∧
        (∀ R : ℝ, 0 ≤ R → R < rho →
          IsCompact (riemannianClosedBallOf Pl.metric Pl.basepoint R)) ∧
        Isometry ray ∧ ray ⟨0, le_rfl, hrho⟩ = Pl.basepoint ∧
        Tendsto ray (comap (Subtype.val : Ico (0 : ℝ) rho → ℝ) (𝓝 rho))
          (cocompact Pl.M) ∧
        (∀ y : Pl.M, ¬ Tendsto ray
          (comap (Subtype.val : Ico (0 : ℝ) rho → ℝ) (𝓝 rho)) (𝓝 y)) ∧
        Tendsto (fun v => metricScalarAt Pl.metric (ray v))
          (comap (Subtype.val : Ico (0 : ℝ) rho → ℝ) (𝓝 rho)) atTop ∧
        ∀ᶠ v : Ico (0 : ℝ) rho in
            comap (Subtype.val : Ico (0 : ℝ) rho → ℝ) (𝓝 rho),
          Nonempty (SpatialNeck Pl.metric (1 / 4000000) (ray v))) →
    ∃ W : TopologicalSpace.Opens Pl.M, ∃ hWc : PathConnectedSpace W,
      let _ : PathConnectedSpace W := hWc
      let _ : PseudoMetricSpace W := (Pl.metric.restrictOpen W).toPseudoMetricSpace
      let _ : MetricSpace W := MetricSpace.ofT0PseudoMetricSpace W
      ∃ (qW : UniformSpace.Completion W) (delta : ℝ), 0 < delta ∧
        IsCompact (Metric.closedBall qW delta) ∧
        Metric.closedBall qW delta ⊆
          insert qW (range (fun z : W => (z : UniformSpace.Completion W))) ∧
        Nonempty (DifferentialGeometry.Toponogov.PuncturedConeApproximation qW delta) ∧
        ∃ xW : ℕ → W, (∃ times : ℕ → Ico (0 : ℝ) rho, (∀ n, (xW n : Pl.M) = ray (times n)) ∧
            Tendsto (fun n => (times n : ℝ)) atTop (𝓝 rho)) ∧
          Tendsto (fun n => (xW n : UniformSpace.Completion W)) atTop (𝓝 qW) ∧
          Tendsto (fun n => metricScalarAt Pl.metric (xW n : Pl.M)) atTop atTop ∧
          ∃ c : ℝ, 0 < c ∧
            (∀ᶠ n in atTop, c ≤ metricScalarAt Pl.metric (xW n : Pl.M) *
              dist (xW n : UniformSpace.Completion W) qW ^ 2) ∧
            ∃ B : ℝ, ∀ᶠ n in atTop, metricScalarAt Pl.metric (xW n : Pl.M) *
              dist (xW n : UniformSpace.Completion W) qW ^ 2 ≤ B := by
  intro Pl rho hrho ray h
  let _ : EMetricSpace Pl.M := Pl.emetricSpace
  obtain ⟨_hbase, hnonneg, hradial, _hcompact, hray, _hray0, _hcoc, _hmiss, hblow,
    hnecks⟩ := h
  have hfin : ∀ a b : Pl.M, edist a b ≠ ⊤ := by
    intro a b
    apply ne_top_of_le_ne_top _ (edist_triangle_left a b Pl.basepoint)
    exact ENNReal.add_ne_top.mpr ⟨(hradial a).ne_top, (hradial b).ne_top⟩
  let _ : MetricSpace Pl.M := EMetricSpace.toMetricSpace hfin
  obtain ⟨_qc, _hqc, W, hWc, hrest⟩ := coneEnd_of_operatorNonneg_neckedRay_C11SP Pl.metric
    (fun _ _ => rfl) hnonneg hrho ray hray hblow hnecks
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
  obtain ⟨qW, delta, hdelta, _, _, hK, hcover, xW, times, hxt, htimes, hxW, _, hQW, hlowerW,
    hupperW,
    hcone, _⟩ := hrest
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
  exact ⟨W, hWc, qW, delta, hdelta, hK, hcover, hcone, xW, ⟨times, hxt, htimes⟩, hxW, hQW',
    ((2 * (1 / 4000000 : ℝ))⁻¹) ^ 2 / 8, by norm_num, hlower', hupper'⟩

/-- **G9′（PROVISIONAL[hflowN′]）**：`hnzero` ⇐ native 版 necked ray + **ray 点列上**的 cone 点 flow。
`hflowN′` = G9 的 `hflowN`，flow 子句只对 `xW n = ray (times n)`、`times n → rho` 的点列要求
（lead 00:0x 裁定 (b)）；
结论（`hnzero` 体）与 G9 逐字相同。 -/
theorem native_hnzero_of_flowRay_C11SP
    (P : OrientedThreeStage.{u}) (g : P.Metric)
    (hflowN' :
      ∃ ε₀ : ℝ, 0 < ε₀ ∧
        ∀ {pBase : CutoffParameters} {Γf : ClosedBirthConstants}
          {ε C1 C2 : ℝ} {Ctime : ℝ≥0}
          (S : PreparedSpatialChain pBase Γf P g) (F : GC.Interface.RawSurgery P g)
          (q : CutoffParameters), F.tower = S.tower →
          (∀ t : ℝ, 0 ≤ t → q.delta t = (chainDiagonal_C11A S).delta t ∧
            q.neckRadius t = (chainDiagonal_C11A S).neckRadius t) →
          pBase.modelAccuracy ≤ ε₀ → capWindowRadius_C11E + 1 ≤ pBase.modelRadius →
          2 ≤ pBase.modelOrder → CanonicalLateTimeCore_P6X F ε C1 C2 Ctime →
          ε ≤ coneAccuracy →
          C1ceil_C11SC.{u} Γf ≤ C1 → C2ceil_C11SC.{u} Γf ≤ C2 →
        ∀ A : ℝ, 0 < A →
        ∀ idx : ℕ → ℕ,
        let H : ℕ → ObservedHistory.{u} := fun i => (F.tower.history (idx i)).toHistory
        ∀ (t : ∀ i, Icc (0 : ℝ) (H i).horizon) (s : ℕ → RegularSlice F.observation),
          (∀ i, (s i).time = (t i : ℝ)) →
        ∀ (p x : ∀ i, ((H i).stageAt (t i)).Carrier) (r : ℕ → ℝ),
          (∀ i, 2 * r i ^ 2 < (t i : ℝ)) →
          (∀ i, hasSmallParabolicCurvature (H i) (t i) (p i) (r i)) →
          (∀ i, ENNReal.ofReal (A⁻¹ * r i ^ 3) ≤
            ballVolume ((H i).stageMetric ((H i).activeStage (t i)) (t i)) (p i) (r i)) →
          (∀ i, x i ∈ riemannianBallOf
            ((H i).stageMetric ((H i).activeStage (t i)) (t i)) (p i) (A * r i)) →
          Tendsto (fun i => (t i : ℝ)) atTop atTop →
          Tendsto (fun i => metricScalarAt
            ((H i).stageMetric ((H i).activeStage (t i)) (t i)) (x i) * r i ^ 2) atTop atTop →
          (∀ i, r i < q.neckRadius (t i)) →
          Tendsto (fun i => r i / q.neckRadius (t i)) atTop (𝓝 0) →
          Tendsto (fun i => r i / Real.sqrt (t i : ℝ)) atTop (𝓝 0) →
        ∃ (rho : ℝ) (hrho : 0 < rho),
          ∃ Pl : PointedRiemannianManifold.{u, 0, 0} ThreeModel,
          let _ : EMetricSpace Pl.M := Pl.emetricSpace
          ∃ ray : C(Ico (0 : ℝ) rho, Pl.M),
            (metricScalarAt Pl.metric Pl.basepoint = 1 ∧
             (∀ z : Pl.M, metricAlgebraicCurvatureTensorAt Pl.metric z ∈
               algebraicCurvatureOperatorNonnegativeCone) ∧
             (∀ y : Pl.M, riemannianEDistOf Pl.metric Pl.basepoint y < ENNReal.ofReal rho) ∧
             (∀ R : ℝ, 0 ≤ R → R < rho →
               IsCompact (riemannianClosedBallOf Pl.metric Pl.basepoint R)) ∧
             Isometry ray ∧ ray ⟨0, le_rfl, hrho⟩ = Pl.basepoint ∧
             Tendsto ray (comap (Subtype.val : Ico (0 : ℝ) rho → ℝ) (𝓝 rho))
               (cocompact Pl.M) ∧
             (∀ y : Pl.M, ¬ Tendsto ray
               (comap (Subtype.val : Ico (0 : ℝ) rho → ℝ) (𝓝 rho)) (𝓝 y)) ∧
             Tendsto (fun v => metricScalarAt Pl.metric (ray v))
               (comap (Subtype.val : Ico (0 : ℝ) rho → ℝ) (𝓝 rho)) atTop ∧
             ∀ᶠ v : Ico (0 : ℝ) rho in
                 comap (Subtype.val : Ico (0 : ℝ) rho → ℝ) (𝓝 rho),
               Nonempty (SpatialNeck Pl.metric (1 / 4000000) (ray v))) ∧
            ∀ W : TopologicalSpace.Opens Pl.M,
            ∀ (xW : ℕ → W),
              (∃ times : ℕ → Ico (0 : ℝ) rho, (∀ n, (xW n : Pl.M) = ray (times n)) ∧
                Tendsto (fun n => (times n : ℝ)) atTop (𝓝 rho)) →
            ∀ (R₀ : ℝ), 0 < R₀ →
              (∀ n, 2 ≤ metricScalarAt Pl.metric (xW n : Pl.M)) →
              Tendsto (fun n => metricScalarAt Pl.metric (xW n : Pl.M)) atTop atTop →
              (∀ n, IsCompact (riemannianClosedBallOf (Pl.metric.restrictOpen W) (xW n)
                (4 * R₀ / Real.sqrt (metricScalarAt Pl.metric (xW n : Pl.M))))) →
              ∃ (j : ℕ → ℕ) (_ : StrictMono j) (A₂ : ℕ → ℝ) (hA₂ : ∀ n, 0 < A₂ n),
                Tendsto (fun n => A₂ n / metricScalarAt Pl.metric (xW (j n) : Pl.M)) atTop (𝓝 1) ∧
                ∃ (P₂ : PointedRiemannianManifold.{u, 0, 0} ThreeModel)
                  (V : TopologicalSpace.Opens P₂.M)
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
                    (∀ᶠ n in atTop,
                      riemannianClosedBallOf (g 0) ⟨P₂.basepoint, hp⟩ r ⊆ (C n).source ∧
                      riemannianClosedBallOf (scaleMetric (A₂ n) (hA₂ n) (Pl.metric.restrictOpen W))
                        (xW (j n)) (r / 4) ⊆
                          (C n) '' riemannianClosedBallOf (g 0) ⟨P₂.basepoint, hp⟩ r) ∧
                    ∀ eta : ℝ, 0 < eta → ∀ᶠ n in atTop,
                      ∀ a ∈ riemannianClosedBallOf (g 0) ⟨P₂.basepoint, hp⟩ r,
                      ∀ b ∈ riemannianClosedBallOf (g 0) ⟨P₂.basepoint, hp⟩ r,
                        |(riemannianEDistOf
                            (scaleMetric (A₂ n) (hA₂ n) (Pl.metric.restrictOpen W))
                            (C n a) (C n b)).toReal -
                          (riemannianEDistOf (g 0) a b).toReal| < eta) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧
      ∀ {pBase : CutoffParameters} {Γf : ClosedBirthConstants}
        {ε C1 C2 : ℝ} {Ctime : ℝ≥0}
        (S : PreparedSpatialChain pBase Γf P g) (F : GC.Interface.RawSurgery P g)
        (q : CutoffParameters), F.tower = S.tower →
        (∀ t : ℝ, 0 ≤ t → q.delta t = (chainDiagonal_C11A S).delta t ∧
          q.neckRadius t = (chainDiagonal_C11A S).neckRadius t) →
        pBase.modelAccuracy ≤ ε₀ → capWindowRadius_C11E + 1 ≤ pBase.modelRadius →
        2 ≤ pBase.modelOrder → CanonicalLateTimeCore_P6X F ε C1 C2 Ctime →
        ε ≤ coneAccuracy →
        C1ceil_C11SC.{u} Γf ≤ C1 → C2ceil_C11SC.{u} Γf ≤ C2 →
      ∀ A : ℝ, 0 < A →
      ∀ idx : ℕ → ℕ,
      let H : ℕ → ObservedHistory.{u} := fun i => (F.tower.history (idx i)).toHistory
      ∀ (t : ∀ i, Icc (0 : ℝ) (H i).horizon) (s : ℕ → RegularSlice F.observation),
        (∀ i, (s i).time = (t i : ℝ)) →
      ∀ (p x : ∀ i, ((H i).stageAt (t i)).Carrier) (r : ℕ → ℝ),
        (∀ i, 2 * r i ^ 2 < (t i : ℝ)) →
        (∀ i, hasSmallParabolicCurvature (H i) (t i) (p i) (r i)) →
        (∀ i, ENNReal.ofReal (A⁻¹ * r i ^ 3) ≤
          ballVolume ((H i).stageMetric ((H i).activeStage (t i)) (t i)) (p i) (r i)) →
        (∀ i, x i ∈ riemannianBallOf
          ((H i).stageMetric ((H i).activeStage (t i)) (t i)) (p i) (A * r i)) →
        Tendsto (fun i => (t i : ℝ)) atTop atTop →
        Tendsto (fun i => metricScalarAt
          ((H i).stageMetric ((H i).activeStage (t i)) (t i)) (x i) * r i ^ 2) atTop atTop →
        (∀ i, r i < q.neckRadius (t i)) →
        Tendsto (fun i => r i / q.neckRadius (t i)) atTop (𝓝 0) →
        Tendsto (fun i => r i / Real.sqrt (t i : ℝ)) atTop (𝓝 0) →
      False := by
  obtain ⟨ε₁, hε₁, hflow⟩ := hflowN'
  refine ⟨ε₁, hε₁, ?_⟩
  intro pBase Γf ε C1 C2 Ctime S F q hTower hdiag hacc hrad hord hb hε hC1 hC2 A hA idx H
    t s hs p x r htime hsmall hvol hx htlim hbad hnat hzero hratio
  obtain ⟨rho, hrho, Pl, ray, ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩, hflowPl⟩ :=
    hflow S F q hTower hdiag hacc hrad hord hb hε hC1 hC2 A hA idx t s hs p x r htime hsmall hvol
      hx htlim hbad hnat hzero hratio
  obtain ⟨W, hWc, qW, delta, hdelta, hK, hcover, hcone, xW, hxt, hxW, hQW, c, hc, hlower, B,
    hB⟩ := puncturedConeEnd_ray_C11SP Pl rho hrho ray ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
  exact cone_flow_exclusion_adm_C11SP Pl W hWc
    (fun xW => ∃ times : ℕ → Ico (0 : ℝ) rho, (∀ n, (xW n : Pl.M) = ray (times n)) ∧
      Tendsto (fun n => (times n : ℝ)) atTop (𝓝 rho))
    (fun xW N h => by
      obtain ⟨times, ht, hlim⟩ := h
      exact ⟨fun n => times (n + N), fun n => ht (n + N), hlim.comp (tendsto_add_atTop_nat N)⟩)
    (hflowPl W) qW delta hdelta hK hcover hcone xW hxt hxW hQW c hc hlower ⟨B, hB⟩

end GC.LongTime.Ch11
