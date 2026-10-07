import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.BoundedCurvatureAtDistanceTracedCone
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.Local.BoundedCurvatureAtDistanceCone3_P6L

/-!
# L6-B：`BoundedCurvatureAtDistanceTracedCone:89 / 182 / 380 / 493` 的局部化（`_P6L`，接口 #14）

原 `ST/BoundedCurvatureAtDistanceTracedCone.lean` 四层。改动（同 Cone5_P6L 的 Cone:603/686/880）：
* TC:89：`hW` 限于 `U m`，加中心成员 `hyU : ∀ᶠ m in atTop, (y m).val ∈ U m`（原 l.153/165 求值点）。
* TC:182/380/493：`U` 放 `hderiv` 前；`hderiv` footprint 形（trace 名 `B`）、`hfinal`/`hW` 限于 `U i`、
  `htested` 中心 `HEq` 于 `U i`。xW 中心成员前提（rev1a C2.3）与 `htrace` 同形：TC:182
  `hxWU : ∀ m n, m ≤ n → B_{Q(f n)·L}(F.map n (xW m), 1) ⊆ U (f n)`；TC:380 eventually 形（与
  `htrace` 合并后同一 `ψ` 重标号）；TC:493 在结论内 `htrace` 后加 eventually 形。TC:182 内由
  `Q(f(k m)) ≤ Q₂ m` 给 Cone:365_P6L 的 `hU`（中心 `y m`、半径 1）与 TC:89_P6L 的 `hyU`。
* 接口 #14（TP:97 约定）：`…_of_trace_chains_of_radius_P6L` 收 `Rad`、`hU`（`hqQ` 后）、
  `hradial : ∀ z : Pl.M, d(base, z) < rho`、`rho + 2 ≤ Rad`；xW 前提由桥
  `RetainedCoreHistory.eventually_unit_ball_subset_of_radius_P6L` 供给。
私有 TC:33/50/60 复制为 `_P6L`；其余证明体照抄；结论逐字。
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

private theorem isCompact_riemannianClosedBallOf_endpoint_of_traces_P6L {P : OrientedThreeStage.{u}}
    {a b : ℝ}
    (A : P.ClosedSlab a b)
    (g : SmoothRiemannianMetric ThreeModel
      (A.restrictIncoming le_rfl A.lt le_rfl).terminalRegularOpen)
    (p : (A.restrictIncoming le_rfl A.lt le_rfl).terminalRegularOpen) (r : ℝ) :
    IsCompact (riemannianClosedBallOf g p r) := by
  have hU : (A.restrictIncoming le_rfl A.lt le_rfl).terminalRegularRegion = univ :=
    A.terminalRegularRegion_eq_univ P
  have : CompactSpace (A.restrictIncoming le_rfl A.lt le_rfl).terminalRegularOpen :=
    isCompact_iff_compactSpace.mp (by
      change IsCompact (A.restrictIncoming le_rfl A.lt le_rfl).terminalRegularRegion
      rw [hU]
      exact isCompact_univ)
  exact (isClosed_le (Geometry.Riemannian.continuous_riemannianEDist g p)
    continuous_const).isCompact

private theorem scaleMetric_mul_eq_P6L {M : Type*} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
    [IsManifold ThreeModel ∞ M] (g : SmoothRiemannianMetric ThreeModel M) {a b c : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : c = a * b) :
    scaleMetric c hc g = scaleMetric a ha (scaleMetric b hb g) := by
  apply SmoothRiemannianMetric.ext_inner
  intro z v w
  simp only [scaleMetric_inner]
  rw [habc]
  ring

private theorem isCompact_closedBall_of_lt_dist_puncture_P6L {W : Type*} [MetricSpace W]
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

/-- 尺度单调：`a ≤ b` ⇒ `B_{b·g}(p, r) ⊆ B_{a·g}(p, r)`（`edistOf_scale`）。 -/
private theorem riemannianBallOf_scaleMetric_subset_of_le_P6L {N : Type*} [TopologicalSpace N]
    [ChartedSpace ThreeSpace N] [IsManifold ThreeModel ∞ N]
    (g : SmoothRiemannianMetric ThreeModel N) {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (hab : a ≤ b)
    (p : N) (r : ℝ) :
    riemannianBallOf (scaleMetric b hb g) p r ⊆ riemannianBallOf (scaleMetric a ha g) p r := by
  intro z hz
  change riemannianEDistOf (scaleMetric a ha g) p z < ENNReal.ofReal r
  have hz' : riemannianEDistOf (scaleMetric b hb g) p z < ENNReal.ofReal r := hz
  rw [DifferentialGeometry.edistOf_scale] at hz' ⊢
  refine lt_of_le_of_lt ?_ hz'
  gcongr

/-- **`_P6L`**：原 `RetainedCoreHistory.final_slab_scalar_buffer_of_spatialCanonicalWitness_of_traces`
（TC:89）。改动：`hW` 限于 `U m`；加 `hyU`。结论逐字。 -/
theorem RetainedCoreHistory.final_slab_scalar_buffer_of_spatialCanonicalWitness_of_traces_P6L
    (H : ℕ → RetainedCoreHistory.{u}) (time : ℕ → ℝ)
    (A : ∀ m, ((H m).stage (Fin.last (H m).eventCount)).ClosedSlab
      ((H m).time (Fin.last (H m).eventCount)) (time m))
    (Ctime : ℝ≥0) (q : ℕ → ℝ)
    (y : ∀ m, ((A m).restrictIncoming le_rfl (A m).lt le_rfl).terminalRegularOpen)
    (Q₂ : ℕ → ℝ) (hQ₂ : ∀ m, 1 ≤ Q₂ m)
    (hQ₂y : ∀ m, Q₂ m = (A m).flow.scalar (time m) (y m).val)
    {eps C1 C2 : ℝ} (hC2 : 1 ≤ C2)
    (U : ∀ m, Set ((H m).stage (Fin.last (H m).eventCount)).Carrier)
    (hW : ∀ m, ∀ z ∈ U m, q m < (A m).flow.scalar (time m) z →
      ∃ W : SpatialCanonicalWitness ((A m).flow.base.metric (time m)) eps C1 C2 z,
        W.capTubeHasNeckChart eps)
    (hqy : ∀ᶠ m in atTop, q m < (A m).flow.scalar (time m) (y m).val)
    (hyU : ∀ᶠ m in atTop, (y m).val ∈ U m)
    {θ₀ : ℝ} (hθ₀ : 0 < θ₀)
    (htr : ∀ m, ∃ first : Fin ((H m).eventCount + 1),
      (H m).time first ≤ time m - θ₀ / (A m).flow.scalar (time m) (y m).val ∧
      ∀ z ∈ riemannianBallOf ((A m).flow.base.metric (time m)) (y m).val
        (Real.sqrt ((A m).flow.scalar (time m) (y m).val))⁻¹,
        Nonempty (BackwardPointTrace (H m).toHistory first (Fin.last (H m).eventCount)
          (Fin.le_last first) z)) :
    ∀ R : ℝ, 0 < R → R < 1 → ∃ r Amax θ : ℝ,
      0 < r ∧ R + r < 1 ∧ 1 ≤ Amax ∧ 0 < θ ∧ 6 * Ctime * (Amax * θ) ≤ 1 ∧
      ∀ᶠ m in atTop,
        IsCompact (riemannianClosedBallOf
          (scaleMetric (Q₂ m) (zero_lt_one.trans_le (hQ₂ m))
            ((A m).endpointTerminalLimitMetric ((H m).stage (Fin.last (H m).eventCount))).metric)
          (y m) (R + r)) ∧
        (∀ z ∈ riemannianClosedBallOf
          (scaleMetric (Q₂ m) (zero_lt_one.trans_le (hQ₂ m))
            ((A m).endpointTerminalLimitMetric ((H m).stage (Fin.last (H m).eventCount))).metric)
          (y m) (R + r),
          metricScalarAt
            ((A m).endpointTerminalLimitMetric ((H m).stage (Fin.last (H m).eventCount))).metric z ≤
            2 * (Amax * Q₂ m)) ∧
        ∃ first : Fin ((H m).eventCount + 1),
          (∀ z ∈ riemannianClosedBallOf
            (scaleMetric (Q₂ m) (zero_lt_one.trans_le (hQ₂ m))
              ((A m).endpointTerminalLimitMetric ((H m).stage (Fin.last (H m).eventCount))).metric)
            (y m) (R + r),
            Nonempty (BackwardPointTrace (H m).toHistory first
              (Fin.last (H m).eventCount) (Fin.le_last first) z.val)) ∧
          (H m).time first ≤ time m - θ / Q₂ m := by
    intro R hR hR1
    let r := (1 - R) / 2
    have hr : 0 < r := by dsimp only [r]; linarith
    have hRr : R + r < 1 := by dsimp only [r]; linarith
    let θ := min θ₀ (1 / (6 * ((Ctime : ℝ) + 1) * C2))
    have hθ : 0 < θ := lt_min hθ₀ (by positivity)
    have hθθ₀ : θ ≤ θ₀ := min_le_left _ _
    have hθbudget : θ * (6 * ((Ctime : ℝ) + 1) * C2) ≤ 1 :=
      (le_div_iff₀ (by positivity)).mp (min_le_right _ _)
    have hbudget : 6 * (Ctime : ℝ) * (C2 * θ) ≤ 1 := by
      have hC : (0 : ℝ) ≤ Ctime := Ctime.coe_nonneg
      nlinarith [mul_nonneg (zero_le_one.trans hC2) hθ.le]
    refine ⟨r, C2, θ, hr, hRr, hC2, hθ, hbudget, ?_⟩
    filter_upwards [hqy, hyU] with m hm hmU
    obtain ⟨first, hfirst, htrf⟩ := htr m
    rw [← hQ₂y] at hfirst
    have hball : ∀ z ∈ riemannianClosedBallOf
        (scaleMetric (Q₂ m) (zero_lt_one.trans_le (hQ₂ m))
          ((A m).endpointTerminalLimitMetric ((H m).stage (Fin.last (H m).eventCount))).metric)
        (y m) (R + r), z.val ∈ riemannianBallOf ((A m).flow.base.metric (time m))
          (y m).val (Real.sqrt ((A m).flow.scalar (time m) (y m).val))⁻¹ := by
      intro z hz
      obtain ⟨Wm, _⟩ := hW _ _ hmU hm
      have hQ₂pos : 0 < Q₂ m := zero_lt_one.trans_le (hQ₂ m)
      have hz' := ((A m).mem_scaled_endpoint_closedBall_iff (Q₂ m) hQ₂pos (y m) z (R + r)).mp hz
      have hsq : 0 < Real.sqrt (Q₂ m) := Real.sqrt_pos.mpr hQ₂pos
      change riemannianEDistOf _ _ _ < _
      apply lt_of_le_of_lt hz'
      rw [ENNReal.ofReal_lt_ofReal_iff (by rw [inv_pos]; exact Real.sqrt_pos.mpr Wm.Q_pos)]
      rw [← hQ₂y, div_lt_iff₀ hsq, inv_mul_cancel₀ hsq.ne']
      exact hRr
    refine ⟨isCompact_riemannianClosedBallOf_endpoint_of_traces_P6L (A m) _ _ _, ?_,
      first, fun z hz => htrf z.val (hball z hz), ?_⟩
    · intro z hz
      obtain ⟨Wm, _⟩ := hW _ _ hmU hm
      have hQ₂pos : 0 < Q₂ m := zero_lt_one.trans_le (hQ₂ m)
      have hb := (Wm.scalar_bounds _ (Wm.ball_inside
        (riemannianBallOf_mono _ _ Wm.radius_lower (hball z hz)))).2
      have hLz : metricScalarAt
          ((A m).endpointTerminalLimitMetric ((H m).stage (Fin.last (H m).eventCount))).metric z =
          (A m).flow.scalar (time m) z.val :=
        metricScalarAt_restrictOpen _ _ _
      rw [hLz]
      have : (A m).flow.scalar (time m) z.val ≤ C2 * Q₂ m := by
        rw [hQ₂y]
        exact hb
      nlinarith [hQ₂pos]
    · have hdiv : θ / Q₂ m ≤ θ₀ / Q₂ m :=
        div_le_div_of_nonneg_right hθθ₀ (zero_le_one.trans (hQ₂ m))
      linarith

/-- **`_P6L`**：原 `RetainedCoreHistory.exists_local_backward_limit_at_final_slab_end_of_trace_chains`
（TC:182）。改动见文件头（`U`、footprint `hderiv`、`hxWU`）。结论逐字。 -/
theorem RetainedCoreHistory.exists_local_backward_limit_at_final_slab_end_of_trace_chains_P6L
    (H : ℕ → RetainedCoreHistory.{u}) (time : ℕ → ℝ)
    (A : ∀ i, ((H i).stage (Fin.last (H i).eventCount)).ClosedSlab
      ((H i).time (Fin.last (H i).eventCount)) (time i))
    (hinit : ∀ i, (A i).flow.base.metric ((H i).time (Fin.last (H i).eventCount)) =
      (H i).initialMetric (Fin.last (H i).eventCount))
    (hs : ∀ i, (H i).horizon < time i) (Ctime : ℝ≥0) (q : ℕ → ℝ) (hq : ∀ i, 0 < q i)
    (U : ∀ i, Set ((H i).stage (Fin.last (H i).eventCount)).Carrier)
    (hderiv : ∀ i, ∀ j : Fin (H i).eventCount,
      ∀ (first : Fin ((H i).eventCount + 1)) (hf : first ≤ j.castSucc),
      ∀ z ∈ U i, ∀ B : BackwardPointTrace (H i).toHistory first (Fin.last (H i).eventCount)
        (Fin.le_last first) z,
      ∀ t ∈ Ioo ((H i).time j.castSucc) ((H i).time j.succ),
      q i < ((H i).toHistory.event j).incoming.flow.scalar t
        (B.point j.castSucc hf (Fin.le_last _)) →
      |derivWithin (fun v => ((H i).toHistory.event j).incoming.flow.scalar v
        (B.point j.castSucc hf (Fin.le_last _))) (Iic t) t| ≤
        Ctime * ((H i).toHistory.event j).incoming.flow.scalar t
          (B.point j.castSucc hf (Fin.le_last _)) ^ 2)
    (hfinal : ∀ i, ∀ y ∈ U i, ∀ t ∈ Ioo ((H i).time (Fin.last (H i).eventCount)) (time i),
      q i < (A i).flow.scalar t y →
      |derivWithin (fun v => (A i).flow.scalar v y) (Iic t) t| ≤
        Ctime * (A i).flow.scalar t y ^ 2)
    (x : ∀ i, ((A i).restrictIncoming le_rfl (A i).lt le_rfl).terminalRegularOpen)
    (hQ : ∀ i, 1 ≤ (A i).flow.scalar (time i) (x i).val)
    (hqQ : ∀ i, q i ≤ (A i).flow.scalar (time i) (x i).val)
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
      ∀ z ∈ U i, ∀ (y : (B.toHistory.stageAt tm).Carrier), HEq y z →
      ∀ (b : ℝ), 0 < b → b ≤ σ i →
        B.toHistory.isParabolicallyRmControlledBall tm y b →
          ENNReal.ofReal κ * ENNReal.ofReal b ^ 3 ≤
            riemannianVolumeMeasure ThreeModel (B.toHistory.stageAt tm).Carrier
              (B.toHistory.stageMetric (B.toHistory.activeStage tm) tm)
              (riemannianBallOf (B.toHistory.stageMetric (B.toHistory.activeStage tm) tm) y b))
    {eps C1 C2 : ℝ}
    (hW : ∀ i, ∀ y ∈ U i, q i < (A i).flow.scalar (time i) y →
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
      (4 * R₀ / Real.sqrt (metricScalarAt Pl.metric (xW n : Pl.M)))))
    {θ₂ : ℝ} (hθ₂ : 0 < θ₂)
    (htrace : ∀ m n, m ≤ n → ∃ first : Fin ((H (f n)).eventCount + 1),
      (H (f n)).time first ≤ time (f n) - θ₂ /
        (A (f n)).flow.scalar (time (f n)) (F.map n (xW m : Pl.M)).val ∧
      ∀ z ∈ riemannianBallOf ((A (f n)).flow.base.metric (time (f n)))
        (F.map n (xW m : Pl.M)).val
        (Real.sqrt ((A (f n)).flow.scalar (time (f n))
          (F.map n (xW m : Pl.M)).val))⁻¹,
        Nonempty (BackwardPointTrace (H (f n)).toHistory first (Fin.last (H (f n)).eventCount)
          (Fin.le_last first) z))
    (hxWU : ∀ m n, m ≤ n → ∀ z ∈ riemannianBallOf
      (scaleMetric ((A (f n)).flow.scalar (time (f n)) (x (f n)).val)
        (zero_lt_one.trans_le (hQ (f n)))
        ((A (f n)).endpointTerminalLimitMetric
          ((H (f n)).stage (Fin.last (H (f n)).eventCount))).metric)
      (F.map n (xW m : Pl.M)) 1, z.val ∈ U (f n)) :
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
  have hyball (m : ℕ) : ∀ z ∈ riemannianBallOf
      (scaleMetric (Q₂ m) (zero_lt_one.trans_le (hQ₂ m)) (L (f (k m))).metric) (y m) 1,
      z.val ∈ U (f (k m)) := fun z hz =>
    hxWU m (k m) (hk.id_le m) z (riemannianBallOf_scaleMetric_subset_of_le_P6L _ (hQpos _)
      (zero_lt_one.trans_le (hQ₂ m)) (hQQ₂ m) _ _ hz)
  have hyU (m : ℕ) : (y m).val ∈ U (f (k m)) := by
    refine hyball m (y m) ?_
    change riemannianEDistOf _ (y m) (y m) < ENNReal.ofReal 1
    rw [riemannianEDistOf_self]
    exact ENNReal.ofReal_pos.mpr one_pos
  obtain ⟨m₀, hm₀⟩ := hqy.exists
  obtain ⟨W₀, _⟩ := hW _ _ (hyU m₀) hm₀
  have hC2 : 1 ≤ C2 := W₀.one_le_comparison_constant
  have hbuffer₂ :=
    RetainedCoreHistory.final_slab_scalar_buffer_of_spatialCanonicalWitness_of_traces_P6L
    (fun m => H (f (k m))) (fun m => time (f (k m)))
    (fun m => A (f (k m))) Ctime (fun m => q (f (k m))) y Q₂ hQ₂ (fun m => hLscalar _ _) hC2
    (fun m => U (f (k m))) (fun m => hW (f (k m))) hqy (Eventually.of_forall hyU)
    hθ₂ (fun m => htrace m (k m) (hk.id_le m))
  have hσpos (i : ℕ) : 0 < σ i := by
    by_contra hneg
    have h1 : σ i * Real.sqrt ((A i).flow.scalar (time i) (x i).val) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (not_lt.mp hneg) (Real.sqrt_nonneg _)
    linarith [hσQ i]
  let inc := DifferentialGeometry.Topology.PartialDiffeomorph.subtypeVal (I := ThreeModel) W ⟨xW 0⟩
  let Fcmp := fun m => inc.trans (F.partialDiffeomorph (k m))
  let Gcmp := fun m => scaleMetric (qk m) (lt_of_lt_of_le zero_lt_one (hqk1 m))
    (Pl.metric.restrictOpen W)
  have hHeq (m : ℕ) := scaleMetric_mul_eq_P6L (L (f (k m))).metric
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
    RetainedCoreHistory.exists_nonnegative_local_flow_with_comparison_of_final_slab_window_P6L
      (fun m => H (f (k m))) (fun m => time (f (k m)))
      (fun m => A (f (k m))) (fun m => hinit _) Ctime (fun m => q (f (k m))) (fun m => hq _)
      (fun m => U (f (k m))) (fun m => hderiv _) (fun m => hfinal _) y Q₂ hQ₂ hqQ₂ hQ₂lim
      hyball hPhi (fun m => hpinch _)
      (fun m => hpinchFinal _) hbuffer₂ (fun m => hs _) (fun m => rfl) (fun m => σ (f (k m)))
      hκ hσ₀ (fun m => (hσQ (f (k m))).trans (mul_le_mul_of_nonneg_left
        (Real.sqrt_le_sqrt (hQQ₂ m)) (hσpos _).le)) (fun m => htested (f (k m)))
      Gcmp xW Fcmp hR₀ (fun m => (hcmp m).2.1) (fun m => rfl) hcapture hBconv
  exact ⟨j, hj, fun n => qk (j n), fun n => lt_of_lt_of_le zero_lt_one (hqk1 (j n)),
    hratio.comp hj.tendsto_atTop, P₂, V, hp, hpath, tau, htau, g, hgb, hsol, hnonneg, hbase₂, C,
    hcenter, r, hr, hcpt, hcap, hdist⟩

/-- **`_P6L`**：原
`RetainedCoreHistory.exists_local_backward_limit_at_final_slab_end_of_eventual_traces`（TC:380）。
改动见文件头（`U`、footprint `hderiv`、eventually 形 `hxWU`）。结论逐字。 -/
theorem RetainedCoreHistory.exists_local_backward_limit_at_final_slab_end_of_eventual_traces_P6L
    (H : ℕ → RetainedCoreHistory.{u}) (time : ℕ → ℝ)
    (A : ∀ i, ((H i).stage (Fin.last (H i).eventCount)).ClosedSlab
      ((H i).time (Fin.last (H i).eventCount)) (time i))
    (hinit : ∀ i, (A i).flow.base.metric ((H i).time (Fin.last (H i).eventCount)) =
      (H i).initialMetric (Fin.last (H i).eventCount))
    (hs : ∀ i, (H i).horizon < time i) (Ctime : ℝ≥0) (q : ℕ → ℝ) (hq : ∀ i, 0 < q i)
    (U : ∀ i, Set ((H i).stage (Fin.last (H i).eventCount)).Carrier)
    (hderiv : ∀ i, ∀ j : Fin (H i).eventCount,
      ∀ (first : Fin ((H i).eventCount + 1)) (hf : first ≤ j.castSucc),
      ∀ z ∈ U i, ∀ B : BackwardPointTrace (H i).toHistory first (Fin.last (H i).eventCount)
        (Fin.le_last first) z,
      ∀ t ∈ Ioo ((H i).time j.castSucc) ((H i).time j.succ),
      q i < ((H i).toHistory.event j).incoming.flow.scalar t
        (B.point j.castSucc hf (Fin.le_last _)) →
      |derivWithin (fun v => ((H i).toHistory.event j).incoming.flow.scalar v
        (B.point j.castSucc hf (Fin.le_last _))) (Iic t) t| ≤
        Ctime * ((H i).toHistory.event j).incoming.flow.scalar t
          (B.point j.castSucc hf (Fin.le_last _)) ^ 2)
    (hfinal : ∀ i, ∀ y ∈ U i, ∀ t ∈ Ioo ((H i).time (Fin.last (H i).eventCount)) (time i),
      q i < (A i).flow.scalar t y →
      |derivWithin (fun v => (A i).flow.scalar v y) (Iic t) t| ≤
        Ctime * (A i).flow.scalar t y ^ 2)
    (x : ∀ i, ((A i).restrictIncoming le_rfl (A i).lt le_rfl).terminalRegularOpen)
    (hQ : ∀ i, 1 ≤ (A i).flow.scalar (time i) (x i).val)
    (hqQ : ∀ i, q i ≤ (A i).flow.scalar (time i) (x i).val)
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
      ∀ z ∈ U i, ∀ (y : (B.toHistory.stageAt tm).Carrier), HEq y z →
      ∀ (b : ℝ), 0 < b → b ≤ σ i →
        B.toHistory.isParabolicallyRmControlledBall tm y b →
          ENNReal.ofReal κ * ENNReal.ofReal b ^ 3 ≤
            riemannianVolumeMeasure ThreeModel (B.toHistory.stageAt tm).Carrier
              (B.toHistory.stageMetric (B.toHistory.activeStage tm) tm)
              (riemannianBallOf (B.toHistory.stageMetric (B.toHistory.activeStage tm) tm) y b))
    {eps C1 C2 : ℝ}
    (hW : ∀ i, ∀ y ∈ U i, q i < (A i).flow.scalar (time i) y →
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
      (4 * R₀ / Real.sqrt (metricScalarAt Pl.metric (xW n : Pl.M)))))
    {θ₂ : ℝ} (hθ₂ : 0 < θ₂)
    (htrace : ∀ m, ∀ᶠ n in atTop, ∃ first : Fin ((H (f n)).eventCount + 1),
      (H (f n)).time first ≤ time (f n) - θ₂ /
        (A (f n)).flow.scalar (time (f n)) (F.map n (xW m : Pl.M)).val ∧
      ∀ z ∈ riemannianBallOf ((A (f n)).flow.base.metric (time (f n)))
        (F.map n (xW m : Pl.M)).val
        (Real.sqrt ((A (f n)).flow.scalar (time (f n))
          (F.map n (xW m : Pl.M)).val))⁻¹,
        Nonempty (BackwardPointTrace (H (f n)).toHistory first (Fin.last (H (f n)).eventCount)
          (Fin.le_last first) z))
    (hxWU : ∀ m, ∀ᶠ n in atTop, ∀ z ∈ riemannianBallOf
      (scaleMetric ((A (f n)).flow.scalar (time (f n)) (x (f n)).val)
        (zero_lt_one.trans_le (hQ (f n)))
        ((A (f n)).endpointTerminalLimitMetric
          ((H (f n)).stage (Fin.last (H (f n)).eventCount))).metric)
      (F.map n (xW m : Pl.M)) 1, z.val ∈ U (f n)) :
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
  choose N hN using fun m => eventually_atTop.mp ((htrace m).and (hxWU m))
  let ψ : ℕ → ℕ := fun n => n + ∑ m ∈ Finset.range (n + 1), N m
  have hψ : StrictMono ψ := strictMono_nat_of_lt_succ fun n => by
    change n + ∑ m ∈ Finset.range (n + 1), N m < n + 1 + ∑ m ∈ Finset.range (n + 1 + 1), N m
    rw [Finset.sum_range_succ _ (n + 1)]
    omega
  have hNψ (m n : ℕ) (hmn : m ≤ n) : N m ≤ ψ n := by
    have h1 : N m ≤ ∑ i ∈ Finset.range (n + 1), N i :=
      Finset.single_le_sum (f := N) (fun _ _ => Nat.zero_le _)
        (Finset.mem_range.mpr (Nat.lt_succ_of_le hmn))
    change N m ≤ n + ∑ i ∈ Finset.range (n + 1), N i
    omega
  have hcan' (n : ℕ) : (M.compSubseq ψ hψ).domain n =
      CanonicalMetricCompactness.canonicalSourceData (F.compSubseq ψ hψ) n := by
    change (M.domain (ψ n)).compSubseq ψ hψ n = _
    rw [hcanonical (ψ n)]
    rfl
  exact RetainedCoreHistory.exists_local_backward_limit_at_final_slab_end_of_trace_chains_P6L
    H time A hinit hs Ctime q hq U hderiv hfinal x hQ hqQ hPhi hpinch hpinchFinal σ hκ hσ₀
    hσQ htested hW (hf.comp hψ) Pl (F.compSubseq ψ hψ) (M.compSubseq ψ hψ) hcan' W xW hR₀ hQW
    hQWlim hcompactW hθ₂ (fun m n hmn => (hN m (ψ n) (hNψ m n hmn)).1)
    (fun m n hmn => (hN m (ψ n) (hNψ m n hmn)).2)

/-- **`_P6L`（接口 #14 核心形）**：原
`RetainedCoreHistory.final_slab_punctured_cone_end_exclusion_of_trace_chains`（TC:493）。改动见文件头
（`U`、footprint `hderiv`；结论内 `htrace` 后 eventually 形 xW unit-ball 前提）。结论逐字。 -/
theorem RetainedCoreHistory.final_slab_punctured_cone_end_exclusion_of_trace_chains_P6L
    (H : ℕ → RetainedCoreHistory.{u}) (time : ℕ → ℝ)
    (A : ∀ i, ((H i).stage (Fin.last (H i).eventCount)).ClosedSlab
      ((H i).time (Fin.last (H i).eventCount)) (time i))
    (hinit : ∀ i, (A i).flow.base.metric ((H i).time (Fin.last (H i).eventCount)) =
      (H i).initialMetric (Fin.last (H i).eventCount))
    (hs : ∀ i, (H i).horizon < time i) (Ctime : ℝ≥0) (q : ℕ → ℝ) (hq : ∀ i, 0 < q i)
    (U : ∀ i, Set ((H i).stage (Fin.last (H i).eventCount)).Carrier)
    (hderiv : ∀ i, ∀ j : Fin (H i).eventCount,
      ∀ (first : Fin ((H i).eventCount + 1)) (hf : first ≤ j.castSucc),
      ∀ z ∈ U i, ∀ B : BackwardPointTrace (H i).toHistory first (Fin.last (H i).eventCount)
        (Fin.le_last first) z,
      ∀ t ∈ Ioo ((H i).time j.castSucc) ((H i).time j.succ),
      q i < ((H i).toHistory.event j).incoming.flow.scalar t
        (B.point j.castSucc hf (Fin.le_last _)) →
      |derivWithin (fun v => ((H i).toHistory.event j).incoming.flow.scalar v
        (B.point j.castSucc hf (Fin.le_last _))) (Iic t) t| ≤
        Ctime * ((H i).toHistory.event j).incoming.flow.scalar t
          (B.point j.castSucc hf (Fin.le_last _)) ^ 2)
    (hfinal : ∀ i, ∀ y ∈ U i, ∀ t ∈ Ioo ((H i).time (Fin.last (H i).eventCount)) (time i),
      q i < (A i).flow.scalar t y →
      |derivWithin (fun v => (A i).flow.scalar v y) (Iic t) t| ≤
        Ctime * (A i).flow.scalar t y ^ 2)
    (x : ∀ i, ((A i).restrictIncoming le_rfl (A i).lt le_rfl).terminalRegularOpen)
    (hQ : ∀ i, 1 ≤ (A i).flow.scalar (time i) (x i).val)
    (hqQ : ∀ i, q i ≤ (A i).flow.scalar (time i) (x i).val)
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
      ∀ z ∈ U i, ∀ (y : (B.toHistory.stageAt tm).Carrier), HEq y z →
      ∀ (b : ℝ), 0 < b → b ≤ σ i →
        B.toHistory.isParabolicallyRmControlledBall tm y b →
          ENNReal.ofReal κ * ENNReal.ofReal b ^ 3 ≤
            riemannianVolumeMeasure ThreeModel (B.toHistory.stageAt tm).Carrier
              (B.toHistory.stageMetric (B.toHistory.activeStage tm) tm)
              (riemannianBallOf (B.toHistory.stageMetric (B.toHistory.activeStage tm) tm) y b))
    {eps C1 C2 : ℝ}
    (hW : ∀ i, ∀ y ∈ U i, q i < (A i).flow.scalar (time i) y →
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
      ∀ θ₂ : ℝ, 0 < θ₂ → (∀ m, ∀ᶠ n in atTop, ∃ first : Fin ((H (f n)).eventCount + 1),
        (H (f n)).time first ≤ time (f n) - θ₂ /
          (A (f n)).flow.scalar (time (f n)) (F.map n (xW m : Pl.M)).val ∧
        ∀ z ∈ riemannianBallOf ((A (f n)).flow.base.metric (time (f n)))
          (F.map n (xW m : Pl.M)).val
          (Real.sqrt ((A (f n)).flow.scalar (time (f n))
            (F.map n (xW m : Pl.M)).val))⁻¹,
          Nonempty (BackwardPointTrace (H (f n)).toHistory first
            (Fin.last (H (f n)).eventCount) (Fin.le_last first) z)) →
      (∀ m, ∀ᶠ n in atTop, ∀ z ∈ riemannianBallOf
        (scaleMetric ((A (f n)).flow.scalar (time (f n)) (x (f n)).val)
          (zero_lt_one.trans_le (hQ (f n)))
          ((A (f n)).endpointTerminalLimitMetric
            ((H (f n)).stage (Fin.last (H (f n)).eventCount))).metric)
        (F.map n (xW m : Pl.M)) 1, z.val ∈ U (f n)) →
      ∀ c : ℝ, 0 < c →
      (∀ᶠ n in atTop, c ≤ metricScalarAt Pl.metric (xW n : Pl.M) *
        dist (xW n : UniformSpace.Completion W) qW ^ 2) →
      (∃ B : ℝ, ∀ᶠ n in atTop, metricScalarAt Pl.metric (xW n : Pl.M) *
        dist (xW n : UniformSpace.Completion W) qW ^ 2 ≤ B) → False := by
  intro instPath instPseudo instMetric
  let _ : PathConnectedSpace W := instPath
  let _ : PseudoMetricSpace W := instPseudo
  let _ : MetricSpace W := instMetric
  intro qW delta hdelta hK hcover hcone xW hx hQW θ₂ hθ₂ htrace hxWU c hc hlower hupper
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
    exact isCompact_closedBall_of_lt_dist_puncture_P6L hK hcover (xW' n) (by linarith) (by linarith)
  have hQW' : Tendsto (fun n => metricScalarAt Pl.metric (xW' n : Pl.M)) atTop atTop :=
    hQW.comp (tendsto_add_atTop_nat N)
  obtain ⟨j, hj, A₂, hA₂, hratio, P₂, V, hp, hpath, tau, htau, g, hgb, hsol, hnonneg, hbase₂,
      C, hcenter, r, hr, hcpt, hcap, hdist⟩ :=
    RetainedCoreHistory.exists_local_backward_limit_at_final_slab_end_of_eventual_traces_P6L
      H time A
      hinit hs Ctime q hq U hderiv hfinal x hQ hqQ hPhi hpinch hpinchFinal σ hκ
      hσ₀ hσQ htested hW hf Pl F M hcanonical W xW' hR₀ (fun n => (hN' n).1) hQW' hcompactW
      hθ₂ (fun m => htrace (m + N)) (fun m => hxWU (m + N))
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

/-- **桥（rev1a C2.1/C2.3，供 TP:97_P6L）**：`hU` 于 `Rad`、极限点 `z` 距基点 `< rho`、
`rho + 2 ≤ Rad` ⇒ eventually `B_{Q(f n)·L}(F.map n z, 1) ⊆ U (f n)`（度量收敛
`eventually_riemannianEDistOf_map_lt_of_metric_convergence` + 三角不等式）。 -/
theorem RetainedCoreHistory.eventually_unit_ball_subset_of_radius_P6L
    (H : ℕ → RetainedCoreHistory.{u}) (time : ℕ → ℝ)
    (A : ∀ i, ((H i).stage (Fin.last (H i).eventCount)).ClosedSlab
      ((H i).time (Fin.last (H i).eventCount)) (time i))
    (U : ∀ i, Set ((H i).stage (Fin.last (H i).eventCount)).Carrier)
    (x : ∀ i, ((A i).restrictIncoming le_rfl (A i).lt le_rfl).terminalRegularOpen)
    (hQ : ∀ i, 1 ≤ (A i).flow.scalar (time i) (x i).val)
    (Rad : ℝ) (hU : ∀ i, ∀ y ∈ riemannianBallOf
      (scaleMetric ((A i).flow.scalar (time i) (x i).val) (zero_lt_one.trans_le (hQ i))
        ((A i).endpointTerminalLimitMetric ((H i).stage (Fin.last (H i).eventCount))).metric)
      (x i) Rad, y.val ∈ U i)
    {f : ℕ → ℕ} (Pl : PointedRiemannianManifold.{u, 0, 0} ThreeModel)
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
    {rho : ℝ} (hRad : rho + 2 ≤ Rad) (z : Pl.M)
    (hz : riemannianEDistOf Pl.metric Pl.basepoint z < ENNReal.ofReal rho) :
    ∀ᶠ n in atTop, ∀ w ∈ riemannianBallOf
      (scaleMetric ((A (f n)).flow.scalar (time (f n)) (x (f n)).val)
        (zero_lt_one.trans_le (hQ (f n)))
        ((A (f n)).endpointTerminalLimitMetric
          ((H (f n)).stage (Fin.last (H (f n)).eventCount))).metric)
      (F.map n z) 1, w.val ∈ U (f n) := by
  have href : ∀ k, (M.domain k).referenceMetric = (M.domain k).limitMetric := fun k => by
    rw [hcanonical k]
    rfl
  have hrho : 0 < rho := ENNReal.ofReal_pos.mp (lt_of_le_of_lt zero_le hz)
  have key : ∀ {N : Type u} [TopologicalSpace N] [ChartedSpace ThreeSpace N]
      [IsManifold ThreeModel ∞ N] (g : SmoothRiemannianMetric ThreeModel N) (a b c : N),
      riemannianEDistOf g a b < ENNReal.ofReal rho → riemannianEDistOf g b c < ENNReal.ofReal 1 →
      riemannianEDistOf g a c < ENNReal.ofReal Rad := by
    intro N _ _ _ g a b c hab hbc
    calc riemannianEDistOf g a c ≤ riemannianEDistOf g a b + riemannianEDistOf g b c :=
          riemannianEDistOf_triangle _ _ _ _
      _ < ENNReal.ofReal rho + ENNReal.ofReal 1 := ENNReal.add_lt_add hab hbc
      _ = ENNReal.ofReal (rho + 1) := (ENNReal.ofReal_add hrho.le zero_le_one).symm
      _ ≤ ENNReal.ofReal Rad := ENNReal.ofReal_le_ofReal (by linarith)
  filter_upwards [eventually_riemannianEDistOf_map_lt_of_metric_convergence M href _ _ hz]
    with n hn w hw
  have hx0 : F.map n Pl.basepoint = x (f n) := by
    simpa only [PointedRiemannianConvergenceMaps.map] using F.basepoint_map n
  rw [hx0] at hn
  exact hU (f n) w (key _ _ _ _ hn hw)

/-- **`_P6L`（TP:97 约定的 `Rad` 形，供 TP:97_P6L）**：TC:493_P6L 加 `Rad`、
`hU : ∀ i, ∀ y ∈ B_{Q i·L i}(x i, Rad), y.val ∈ U i`（`hqQ` 后）、极限半径
`hradial : ∀ z : Pl.M, d(base, z) < rho`（TL:47_P6L 的输出形）与 `hRad : rho + 2 ≤ Rad`；
xW unit-ball 前提由桥 `RetainedCoreHistory.eventually_unit_ball_subset_of_radius_P6L` 供给。 -/
theorem RetainedCoreHistory.final_slab_punctured_cone_end_exclusion_of_trace_chains_of_radius_P6L
    (H : ℕ → RetainedCoreHistory.{u}) (time : ℕ → ℝ)
    (A : ∀ i, ((H i).stage (Fin.last (H i).eventCount)).ClosedSlab
      ((H i).time (Fin.last (H i).eventCount)) (time i))
    (hinit : ∀ i, (A i).flow.base.metric ((H i).time (Fin.last (H i).eventCount)) =
      (H i).initialMetric (Fin.last (H i).eventCount))
    (hs : ∀ i, (H i).horizon < time i) (Ctime : ℝ≥0) (q : ℕ → ℝ) (hq : ∀ i, 0 < q i)
    (U : ∀ i, Set ((H i).stage (Fin.last (H i).eventCount)).Carrier)
    (hderiv : ∀ i, ∀ j : Fin (H i).eventCount,
      ∀ (first : Fin ((H i).eventCount + 1)) (hf : first ≤ j.castSucc),
      ∀ z ∈ U i, ∀ B : BackwardPointTrace (H i).toHistory first (Fin.last (H i).eventCount)
        (Fin.le_last first) z,
      ∀ t ∈ Ioo ((H i).time j.castSucc) ((H i).time j.succ),
      q i < ((H i).toHistory.event j).incoming.flow.scalar t
        (B.point j.castSucc hf (Fin.le_last _)) →
      |derivWithin (fun v => ((H i).toHistory.event j).incoming.flow.scalar v
        (B.point j.castSucc hf (Fin.le_last _))) (Iic t) t| ≤
        Ctime * ((H i).toHistory.event j).incoming.flow.scalar t
          (B.point j.castSucc hf (Fin.le_last _)) ^ 2)
    (hfinal : ∀ i, ∀ y ∈ U i, ∀ t ∈ Ioo ((H i).time (Fin.last (H i).eventCount)) (time i),
      q i < (A i).flow.scalar t y →
      |derivWithin (fun v => (A i).flow.scalar v y) (Iic t) t| ≤
        Ctime * (A i).flow.scalar t y ^ 2)
    (x : ∀ i, ((A i).restrictIncoming le_rfl (A i).lt le_rfl).terminalRegularOpen)
    (hQ : ∀ i, 1 ≤ (A i).flow.scalar (time i) (x i).val)
    (hqQ : ∀ i, q i ≤ (A i).flow.scalar (time i) (x i).val)
    (Rad : ℝ) (hU : ∀ i, ∀ y ∈ riemannianBallOf
      (scaleMetric ((A i).flow.scalar (time i) (x i).val) (zero_lt_one.trans_le (hQ i))
        ((A i).endpointTerminalLimitMetric ((H i).stage (Fin.last (H i).eventCount))).metric)
      (x i) Rad, y.val ∈ U i)
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
      ∀ z ∈ U i, ∀ (y : (B.toHistory.stageAt tm).Carrier), HEq y z →
      ∀ (b : ℝ), 0 < b → b ≤ σ i →
        B.toHistory.isParabolicallyRmControlledBall tm y b →
          ENNReal.ofReal κ * ENNReal.ofReal b ^ 3 ≤
            riemannianVolumeMeasure ThreeModel (B.toHistory.stageAt tm).Carrier
              (B.toHistory.stageMetric (B.toHistory.activeStage tm) tm)
              (riemannianBallOf (B.toHistory.stageMetric (B.toHistory.activeStage tm) tm) y b))
    {eps C1 C2 : ℝ}
    (hW : ∀ i, ∀ y ∈ U i, q i < (A i).flow.scalar (time i) y →
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
    {rho : ℝ}
    (hradial : ∀ z : Pl.M, riemannianEDistOf Pl.metric Pl.basepoint z < ENNReal.ofReal rho)
    (hRad : rho + 2 ≤ Rad)
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
      ∀ θ₂ : ℝ, 0 < θ₂ → (∀ m, ∀ᶠ n in atTop, ∃ first : Fin ((H (f n)).eventCount + 1),
        (H (f n)).time first ≤ time (f n) - θ₂ /
          (A (f n)).flow.scalar (time (f n)) (F.map n (xW m : Pl.M)).val ∧
        ∀ z ∈ riemannianBallOf ((A (f n)).flow.base.metric (time (f n)))
          (F.map n (xW m : Pl.M)).val
          (Real.sqrt ((A (f n)).flow.scalar (time (f n))
            (F.map n (xW m : Pl.M)).val))⁻¹,
          Nonempty (BackwardPointTrace (H (f n)).toHistory first
            (Fin.last (H (f n)).eventCount) (Fin.le_last first) z)) →
      ∀ c : ℝ, 0 < c →
      (∀ᶠ n in atTop, c ≤ metricScalarAt Pl.metric (xW n : Pl.M) *
        dist (xW n : UniformSpace.Completion W) qW ^ 2) →
      (∃ B : ℝ, ∀ᶠ n in atTop, metricScalarAt Pl.metric (xW n : Pl.M) *
        dist (xW n : UniformSpace.Completion W) qW ^ 2 ≤ B) → False := by
  intro instPath instPseudo instMetric qW delta hdelta hK hcover hcone xW hx hQW θ₂ hθ₂ htrace
  exact RetainedCoreHistory.final_slab_punctured_cone_end_exclusion_of_trace_chains_P6L H time A
    hinit hs Ctime q hq U hderiv hfinal x hQ hqQ hPhi hpinch hpinchFinal σ hκ hσ₀ hσQ htested hW
    hf Pl F M hcanonical W hWc qW delta hdelta hK hcover hcone xW hx hQW θ₂ hθ₂ htrace
    (fun m => RetainedCoreHistory.eventually_unit_ball_subset_of_radius_P6L H time A U x hQ Rad
      hU Pl F M hcanonical hRad _ (hradial _))

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

open Set

/-- consumer：原 TC:89 由 `_P6L` 版（`U m = univ`）推出。 -/
example :
    type_of%
      @RetainedCoreHistory.final_slab_scalar_buffer_of_spatialCanonicalWitness_of_traces.{0} := by
  intro H time A Ctime q y Q₂ hQ₂ hQ₂y eps C1 C2 hC2 hW hqy θ₀ hθ₀ htr
  exact RetainedCoreHistory.final_slab_scalar_buffer_of_spatialCanonicalWitness_of_traces_P6L
    H time A Ctime q y Q₂ hQ₂ hQ₂y hC2 (fun _ => univ) (fun m z _ => hW m z) hqy
    (Eventually.of_forall fun _ => mem_univ _) hθ₀ htr

/-- consumer：原 TC:182 由 `_P6L` 版（`U i = univ`）推出。 -/
example :
    type_of%
      @RetainedCoreHistory.exists_local_backward_limit_at_final_slab_end_of_trace_chains.{0} := by
  intro H time A hinit hs Ctime q hq hderiv hfinal x hQ hqQ Phi hPhi hpinch hpinchFinal κ σ₀ σ hκ
    hσ₀ hσQ htested eps C1 C2 hW f hf Pl F M hcanonical W xW R₀ hR₀ hQW hQWlim hcompactW θ₂ hθ₂
    htrace
  exact RetainedCoreHistory.exists_local_backward_limit_at_final_slab_end_of_trace_chains_P6L
    H time A hinit hs Ctime q hq (fun _ => univ) (fun i j _ _ _ _ _ t ht h => hderiv i j _ t ht h)
    (fun i y _ => hfinal i y) x hQ hqQ hPhi hpinch hpinchFinal σ hκ hσ₀ hσQ
    (by
      intro i t ht hts B' tm _ _ y _
      exact htested i t ht hts y)
    (fun i y _ => hW i y) hf Pl F M hcanonical W xW hR₀ hQW hQWlim hcompactW hθ₂ htrace
    (fun _ _ _ _ _ => mem_univ _)

/-- consumer：原 TC:380 由 `_P6L` 版（`U i = univ`）推出。 -/
example :
    type_of%
      @RetainedCoreHistory.exists_local_backward_limit_at_final_slab_end_of_eventual_traces.{0}
    := by
  intro H time A hinit hs Ctime q hq hderiv hfinal x hQ hqQ Phi hPhi hpinch hpinchFinal κ σ₀ σ hκ
    hσ₀ hσQ htested eps C1 C2 hW f hf Pl F M hcanonical W xW R₀ hR₀ hQW hQWlim hcompactW θ₂ hθ₂
    htrace
  exact RetainedCoreHistory.exists_local_backward_limit_at_final_slab_end_of_eventual_traces_P6L
    H time A hinit hs Ctime q hq (fun _ => univ) (fun i j _ _ _ _ _ t ht h => hderiv i j _ t ht h)
    (fun i y _ => hfinal i y) x hQ hqQ hPhi hpinch hpinchFinal σ hκ hσ₀ hσQ
    (by
      intro i t ht hts B' tm _ _ y _
      exact htested i t ht hts y)
    (fun i y _ => hW i y) hf Pl F M hcanonical W xW hR₀ hQW hQWlim hcompactW hθ₂ htrace
    (fun _ => Eventually.of_forall fun _ _ _ => mem_univ _)

/-- consumer：原 TC:493 由 `_P6L` 版（`U i = univ`）推出。 -/
example :
    type_of% @RetainedCoreHistory.final_slab_punctured_cone_end_exclusion_of_trace_chains.{0} := by
  intro H time A hinit hs Ctime q hq hderiv hfinal x hQ hqQ Phi hPhi hpinch hpinchFinal κ σ₀ σ hκ
    hσ₀ hσQ htested eps C1 C2 hW f hf Pl F M hcanonical W hWc instPath instPseudo instMetric qW
    delta hdelta hK hcover hcone xW hx hQW θ₂ hθ₂ htrace
  exact RetainedCoreHistory.final_slab_punctured_cone_end_exclusion_of_trace_chains_P6L
    H time A hinit hs Ctime q hq (fun _ => univ) (fun i j _ _ _ _ _ t ht h => hderiv i j _ t ht h)
    (fun i y _ => hfinal i y) x hQ hqQ hPhi hpinch hpinchFinal σ hκ hσ₀ hσQ
    (by
      intro i t ht hts B' tm _ _ y _
      exact htested i t ht hts y)
    (fun i y _ => hW i y) hf Pl F M hcanonical W hWc qW delta hdelta hK hcover hcone xW hx hQW
    θ₂ hθ₂ htrace (fun _ => Eventually.of_forall fun _ _ _ => mem_univ _)

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
