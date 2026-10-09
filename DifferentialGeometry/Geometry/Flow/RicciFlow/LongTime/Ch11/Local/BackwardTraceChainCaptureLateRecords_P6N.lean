import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.Local.BackwardTraceChainCaptureTimeWindow_P6N

/-!
# G2（方案 B）窗口 spine 1：`BTDT:58` + `BTCC:91/358/409` 的 late-records + 窗口 pinching 形（`_P6N`）

lead 02:0x 裁定方案 B：不截取 history；P5 late records `∀ i, T₀ ≤ time i.succ → GeometricCutoffRecord …`
直接喂。[V] `BTCC:91` 只在找到的事件 `j`（`u ≤ u' = time j.succ`）上用 `records j`、`hcan j`、
`hscale j`（经 `exists_cap_of_not_regularCrossing_target`、`exists_window_point_of_edist_le`），
pinching 只经 `BTDT:58` 在 `[u', t]` 上用（`CrossingRoom.sqrt_rmNormSq_stageMetric_le_of_pinched`）。
改动（在 G1 窗口形之上）：
* `{T₀} (records : ∀ i, T₀ ≤ time i.succ → record)`、`hcan`/`hscale` 同形；`hTu : T₀ ≤ u`（`hut` 后）；
* `hpinch : ∀ j, PhiAlmostNonnegative … (Ico (time j.castSucc) (time j.succ) ∩ Ici u) phi`、
  `hlast`/`hfinalPinch` 于 `Icc (time last) horizon ∩ Ici u`（窗口 pinching）；
* `:358/:409` 的结论 = `CapWindowPoint` 的**展开形**
  （late records：`∃ j (hT : T₀ ≤ time j.succ) hl A b x, …`），不新建 def。
辅助：`exists_window_point_of_edist_le_record_P6N`（private 原引理的单 record 版）、窗口 pinching 版
`sqrt_rmNormSq_stageMetric_le_of_pinched_window_P6N`、`phiAlmostNonnegative_mono_P6N`。
consumer：G1 窗口形（全 family、全 pinching）⇐ 本文件（`T₀ = 0`）。
-/

set_option autoImplicit false

noncomputable section

open Set TopologicalSpace Manifold
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open scoped Manifold ContDiff NNReal ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

private local instance : Fact (Module.finrank ℝ ThreeSpace = 3) := ⟨by simp⟩
private local instance : NeZero (Module.finrank ℝ ThreeSpace) := ⟨by simp⟩

open private ObservedHistory.activeStage_eq_of_time_mem
  ObservedHistory.time_lt_succ_of_activeStage_eq_castSucc
  ObservedHistory.backwardSurvivorInitialMetric_inner_le_exp
  ObservedHistory.initialMetric_inner_le_exp_of_normSq_le
  BackwardPointTrace.apply_point_eq_of_stage_eq from
  DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.BackwardTraceDistortion

open private ObservedHistory.initialMetric_inner_le_exp_of_normSq_le_of_eq_last from
  DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.BackwardTraceDistortionTerminal

namespace RetainedCoreHistory

variable (H : RetainedCoreHistory.{u})

theorem phiAlmostNonnegative_mono_P6N {P : OrientedThreeStage.{u}} {D : RealTimeInterval}
    {S : SolutionOn (I := ThreeModel) (M := P.Carrier) D} {W W' : Set ℝ} {phi : ℝ → ℝ}
    (h : Perelman.PhiAlmostNonnegative S W phi) (hW : W' ⊆ W) :
    Perelman.PhiAlmostNonnegative S W' phi :=
  fun t ht x => h t (hW ht) x

private theorem lt_time_succ_of_activeStage_eq_late_P6N (t : Icc (0 : ℝ) H.toHistory.horizon)
    (i : Fin H.eventCount) (hi : H.toHistory.activeStage t = i.castSucc) :
    (t : ℝ) < H.time i.succ := by
  have hval : (H.toHistory.activeStage t).val < H.toHistory.eventCount := by
    rw [hi]
    exact i.isLt
  have h := H.toHistory.activeStage_before_next t hval
  have he : (⟨(H.toHistory.activeStage t).val + 1, Nat.succ_lt_succ hval⟩ :
      Fin (H.toHistory.eventCount + 1)) = i.succ := by
    ext
    simp [hi]
  rw [he] at h
  exact h

/-- `CrossingRoom` 的 `sqrt_rmNormSq_stageMetric_le_of_pinched` 的窗口形：pinching 只在
`[a, ∞)` 与各 slab 之交上要，求值时刻 `a ≤ v`。证明照抄。 -/
theorem sqrt_rmNormSq_stageMetric_le_of_pinched_window_P6N {phi : ℝ → ℝ} {a : ℝ}
    (hphi : Perelman.AdmissiblePinchingFunction phi)
    (hpinch : ∀ j : Fin H.eventCount, Perelman.PhiAlmostNonnegative
      (H.toHistory.event j).incoming.flow (Ico (H.time j.castSucc) (H.time j.succ) ∩ Ici a) phi)
    (v : Icc (0 : ℝ) H.toHistory.horizon) (hav : a ≤ (v : ℝ))
    (hv : H.toHistory.activeStage v = Fin.last H.eventCount →
      ∃ h : H.time (Fin.last H.eventCount) < H.horizon,
        Perelman.PhiAlmostNonnegative (H.finalSlab h).flow
          (Icc (H.time (Fin.last H.eventCount)) H.horizon ∩ Ici a) phi)
    (z : (H.stage (H.toHistory.activeStage v)).Carrier) :
    Real.sqrt (normSq0S (H.toHistory.stageMetric (H.toHistory.activeStage v) v) z 4
        (metricRm04At (H.toHistory.stageMetric (H.toHistory.activeStage v) v) z)) ≤
      4 * Real.sqrt 3 * (1 + phi 1 + phi 0) *
        max (metricScalarAt (H.toHistory.stageMetric (H.toHistory.activeStage v) v) z) 1 := by
  have hdim : Module.finrank ℝ ThreeSpace = 3 := by simp
  have hlow := H.toHistory.activeStage_time_le v
  have hnext := H.lt_time_succ_of_activeStage_eq_late_P6N v
  have hup := v.2.2
  generalize H.toHistory.activeStage v = k at hlow hnext hv z ⊢
  cases k using Fin.lastCases with
  | last =>
    obtain ⟨h, hfp⟩ := hv rfl
    have := IsManifold.of_le (I := ThreeModel) (M := (H.stage (Fin.last H.eventCount)).Carrier)
      (n := ∞) (m := 1) (by decide)
    have hb :=
      Perelman.CanonicalNeighborhood.sqrt_rmNormSq_le_mul_max_scalar_one_of_phiAlmostNonnegative
      hphi hfp hdim ⟨⟨hlow, hup⟩, hav⟩ z
    rw [ObservedHistory.stageMetric_last_of_lt (h := h)]
    exact hb
  | cast i =>
    have := IsManifold.of_le (I := ThreeModel) (M := (H.stage i.castSucc).Carrier)
      (n := ∞) (m := 1) (by decide)
    have hb :=
      Perelman.CanonicalNeighborhood.sqrt_rmNormSq_le_mul_max_scalar_one_of_phiAlmostNonnegative
      hphi (hpinch i) hdim ⟨⟨hlow, hnext i rfl⟩, hav⟩ z
    rw [ObservedHistory.stageMetric_castSucc_apply]
    exact hb

/-- `BackwardTraceDistortion` 的 private `exists_window_point_of_edist_le` 的单 record 版（`_P6N`）：
原证明只用 `records j` 与 `hcan j`。 -/
theorem exists_window_point_of_edist_le_record_P6N {p : CutoffParameters} {j : Fin H.eventCount}
    (R : GeometricCutoffRecord H.toHistory j p)
    (hcan : ∀ b, (R.static b).hasCanonicalWindow)
    (hacc : p.modelAccuracy ≤ 1 / 2)
    (b : (H.toHistory.event j).RetainedBoundaryIndex) {M dd Dcap Dstar : ℝ}
    (hsM : (R.static b).neck.scale ≤ 4 * M)
    (hDstar : Dcap ≤ Dstar) (hDmodel : Dstar ≤ p.modelRadius)
    (xz : standardCapWindow p.modelRadius) (hxzn : ‖xz.val‖ ≤ StandardCap.transitionEnd)
    (q : (H.toHistory.stage j.succ).Carrier)
    (hnear : riemannianEDistOf (H.toHistory.initialMetric j.succ)
      ((R.static b).window xz) q ≤ ENNReal.ofReal dd)
    (hdd0 : 0 ≤ dd) (hwin : 2 * StandardCap.transitionEnd + Real.sqrt (8 * M) * dd < Dcap) :
    ∃ x : standardCapWindow p.modelRadius,
      ‖x.val‖ < Dcap ∧ (R.static b).window x = q := by
  obtain ⟨x₀, δ, kk, d, w, -, hinner, -⟩ := hcan b
  have hspos : 0 < (R.static b).neck.scale := (R.static b).neck.scale_pos
  have hlocW : IsLocalDiffeomorph ThreeModel ThreeModel ∞ (R.static b).window :=
    DifferentialGeometry.Topology.Manifold.isLocalDiffeomorph_of_injective_mfderiv _
      (R.static b).window_smooth.contMDiff
      (fun q => ((R.static b).window_smooth.isImmersion.isImmersionAt
        q).mfderiv_injective (by simp)) rfl
  have hinjW := (R.static b).window_smooth.isEmbedding.injective
  have hsmall := w.properties.window_close
  change Geometry.Metric.metricDerivENormSupOn
    {y : standardCapWindow p.modelRadius |
      (riemannianEDistOf StandardCap.metric 0 y.val).toReal < p.modelRadius} p.modelOrder
    w.windowMetric (StandardCap.metric.restrictOpen (standardCapWindow p.modelRadius))
      (StandardCap.metric.restrictOpen (standardCapWindow p.modelRadius)) <
        ENNReal.ofReal p.modelAccuracy at hsmall
  simp only [StandardCap.distance_zero] at hsmall
  rw [H.toHistory.event_output j] at hinner
  have hTE := StandardCap.transitionEnd_pos
  set sc := (R.static b).neck.scale with hsc
  have hL : 0 < Real.sqrt (2 * sc) := Real.sqrt_pos.mpr (by positivity)
  have hU : 0 < Real.sqrt (2 / sc) := Real.sqrt_pos.mpr (by positivity)
  have hLU : Real.sqrt (2 * sc) * Real.sqrt (2 / sc) = 2 := by
    rw [← Real.sqrt_mul (by positivity), show 2 * sc * (2 / sc) = 2 * 2 by field_simp,
      Real.sqrt_mul_self (by norm_num)]
  have hL8 : Real.sqrt (2 * sc) ≤ Real.sqrt (8 * M) := Real.sqrt_le_sqrt (by linarith)
  have hsqrt8 : 0 ≤ Real.sqrt (8 * M) := Real.sqrt_nonneg _
  have hkey : Real.sqrt (2 * sc) * (Real.sqrt (2 / sc) * ‖xz.val‖ + dd) < Dcap := by
    have h1 : Real.sqrt (2 * sc) * dd ≤ Real.sqrt (8 * M) * dd :=
      mul_le_mul_of_nonneg_right hL8 hdd0
    have h2 : Real.sqrt (2 * sc) * (Real.sqrt (2 / sc) * ‖xz.val‖) ≤
        2 * StandardCap.transitionEnd := by
      rw [← mul_assoc, hLU]
      linarith
    nlinarith
  have hxzD : ‖xz.val‖ < Dcap := by
    have h0 : 0 ≤ Real.sqrt (8 * M) * dd := mul_nonneg (Real.sqrt_nonneg _) hdd0
    linarith
  have hgap : Real.sqrt (2 / sc) * ‖xz.val‖ + dd < Dcap / Real.sqrt (2 * sc) := by
    rw [lt_div_iff₀ hL]
    linarith
  set r' := (Dcap / Real.sqrt (2 * sc) - (Real.sqrt (2 / sc) * ‖xz.val‖ + dd)) / 2 with hr'
  have hmargin : Real.sqrt (2 / sc) * ‖xz.val‖ + dd + r' < Dcap / Real.sqrt (2 * sc) := by
    rw [hr']
    linarith
  have hr'pos : 0 < r' := by
    rw [hr']
    linarith
  have hbd : ∀ x : standardCapWindow p.modelRadius, ‖x.val‖ < p.modelRadius →
      ∀ v : TangentSpace ThreeModel x,
        (1 - p.modelAccuracy) * StandardCap.metric.inner x.val v v ≤
            w.windowMetric.inner x v v ∧
          w.windowMetric.inner x v v ≤
            (1 + p.modelAccuracy) * StandardCap.metric.inner x.val v v := by
    intro x hx v
    have hn := Geometry.Metric.metricDerivNorm_lt_of_sup_lt _ _ _ _ _ hsmall (Nat.zero_le _)
      (x := x) hx
    simpa only [SmoothRiemannianMetric.restrictOpen_inner] using
      Geometry.Metric.inner_bounds_of_metricDerivNorm_le
        (StandardCap.metric.restrictOpen (standardCapWindow p.modelRadius)) w.windowMetric x
        hn.le v
  have hacc0 := p.modelAccuracy_pos
  have hball := StandardCap.window_ball_subset_image_ball_of_metric_bounds
    (H.toHistory.initialMetric j.succ) (D := p.modelRadius) (R := Dcap) (r := r')
    (by linarith) hL hU hdd0 (R.static b).window hlocW hinjW
    (fun x hx v => by
      obtain ⟨hlo, -⟩ := hbd x (hx.trans_le (hDstar.trans hDmodel)) v
      have hi := hinner x v v
      have hn := metric_inner_self_nonneg StandardCap.metric x.val v
      rw [Real.sq_sqrt (by positivity)]
      nlinarith)
    (fun x hx v => by
      obtain ⟨-, hup⟩ := hbd x (hx.trans_le (hDstar.trans hDmodel)) v
      have hi := hinner x v v
      have hn := metric_inner_self_nonneg StandardCap.metric x.val v
      rw [Real.sq_sqrt (by positivity), div_mul_eq_mul_div, le_div_iff₀ hspos]
      nlinarith)
    xz hxzD (q) hnear hmargin
  have hcenter : q ∈
      riemannianBallOf (H.toHistory.initialMetric j.succ)
        (q) r' := by
    change riemannianEDistOf _ _ _ < ENNReal.ofReal r'
    rw [riemannianEDistOf_self]
    exact ENNReal.ofReal_pos.mpr hr'pos
  obtain ⟨x, hxn, hxeq⟩ := hball hcenter
  exact ⟨x, hxn, hxeq⟩


private theorem normSq_stageMetric_le_of_backwardPointTrace_of_final_late_P6N
    {Ctime : ℝ≥0} {qcan M : ℝ} {phi : ℝ → ℝ}
    (hphi : Perelman.AdmissiblePinchingFunction phi)
    {u t : Icc (0 : ℝ) H.toHistory.horizon} (hut : u ≤ t)
    (hpinch : ∀ j : Fin H.eventCount, Perelman.PhiAlmostNonnegative
      (H.toHistory.event j).incoming.flow (Ico (H.time j.castSucc) (H.time j.succ) ∩ Ici (u : ℝ))
      phi)
    (hlast : H.toHistory.activeStage t = Fin.last H.eventCount →
      ∃ h : H.time (Fin.last H.eventCount) < H.horizon,
        Perelman.PhiAlmostNonnegative (H.finalSlab h).flow
          (Icc (H.time (Fin.last H.eventCount)) H.horizon ∩ Ici (u : ℝ)) phi)
    {p : (H.toHistory.stage (H.toHistory.activeStage t)).Carrier}
    (A : BackwardPointTrace H.toHistory (H.toHistory.activeStage u)
      (H.toHistory.activeStage t) (H.toHistory.activeStage_mono hut) p)
    (hslabs : ∀ i : Fin H.toHistory.eventCount, ∀ hf : H.toHistory.activeStage u ≤ i.castSucc,
      ∀ hl : i.succ ≤ H.toHistory.activeStage t,
      ∀ v ∈ Ioo (H.toHistory.time i.castSucc) (H.toHistory.time i.succ), (u : ℝ) ≤ v →
      qcan < (H.toHistory.event i).incoming.flow.scalar v
        (A.point i.castSucc hf (i.castSucc_lt_succ.le.trans hl)) →
      |derivWithin (fun w => (H.toHistory.event i).incoming.flow.scalar w
        (A.point i.castSucc hf (i.castSucc_lt_succ.le.trans hl))) (Iic v) v| ≤
        Ctime * (H.toHistory.event i).incoming.flow.scalar v
          (A.point i.castSucc hf (i.castSucc_lt_succ.le.trans hl)) ^ 2)
    (hcurrent : ∀ j : Fin H.toHistory.eventCount, ∀ y : (H.toHistory.stage j.castSucc).Carrier,
      j.castSucc = H.toHistory.activeStage t → HEq y p →
      ∀ v ∈ Ioo (H.toHistory.time j.castSucc) t, (u : ℝ) ≤ v →
      qcan < (H.toHistory.event j).incoming.flow.scalar v y →
      |derivWithin (fun w => (H.toHistory.event j).incoming.flow.scalar w y) (Iic v) v| ≤
        Ctime * (H.toHistory.event j).incoming.flow.scalar v y ^ 2)
    (hfinal : ∀ h : H.toHistory.time (Fin.last H.toHistory.eventCount) < H.toHistory.horizon,
      ∀ y : (H.toHistory.stage (Fin.last H.toHistory.eventCount)).Carrier,
      H.toHistory.activeStage t = Fin.last H.toHistory.eventCount → HEq y p →
      ∀ v ∈ Ioo (H.toHistory.time (Fin.last H.toHistory.eventCount)) t, (u : ℝ) ≤ v →
      qcan < ((H.toHistory.finalSlab h).restrictIncoming le_rfl h le_rfl).flow.scalar v y →
      |derivWithin (fun w =>
        ((H.toHistory.finalSlab h).restrictIncoming le_rfl h le_rfl).flow.scalar w y) (Iic v) v| ≤
        Ctime * ((H.toHistory.finalSlab h).restrictIncoming le_rfl h le_rfl).flow.scalar v y ^ 2)
    (hM : 1 ≤ M) (hqcan : qcan ≤ M)
    (hscalar : metricScalarAt (H.toHistory.stageMetric (H.toHistory.activeStage t) t) p ≤ M)
    (htime : Ctime * M * ((t : ℝ) - u) ≤ 1 / 2)
    (v : Icc (0 : ℝ) H.toHistory.horizon) (huv : u ≤ v) (hvt : v ≤ t) :
    normSq0S (H.toHistory.stageMetric (H.toHistory.activeStage v) v)
        (A.point (H.toHistory.activeStage v) (H.toHistory.activeStage_mono huv)
          (H.toHistory.activeStage_mono hvt)) 4
        (metricRm04At (H.toHistory.stageMetric (H.toHistory.activeStage v) v)
          (A.point (H.toHistory.activeStage v) (H.toHistory.activeStage_mono huv)
            (H.toHistory.activeStage_mono hvt))) ≤
      (8 * Real.sqrt 3 * (1 + phi 1 + phi 0) * M) ^ 2 := by
  have hC : 0 ≤ 4 * Real.sqrt 3 * (1 + phi 1 + phi 0) := by
    have := hphi.pos 0
    have := hphi.pos 1
    positivity
  have hscal := H.scalar_le_two_mul_of_backwardPointTrace_of_derivative_bounds_window_P6N hut A
    hslabs hcurrent hfinal (by linarith) hqcan hscalar htime v huv hvt
  have hs := H.sqrt_rmNormSq_stageMetric_le_of_pinched_window_P6N hphi hpinch v huv
    (fun h => hlast (le_antisymm (Fin.le_last _) (h ▸ H.toHistory.activeStage_mono hvt)))
    (A.point (H.toHistory.activeStage v) (H.toHistory.activeStage_mono huv)
      (H.toHistory.activeStage_mono hvt))
  have hmax : max (metricScalarAt (H.toHistory.stageMetric (H.toHistory.activeStage v) v)
      (A.point (H.toHistory.activeStage v) (H.toHistory.activeStage_mono huv)
        (H.toHistory.activeStage_mono hvt))) 1 ≤ 2 * M := max_le hscal (by linarith)
  have h1 := hs.trans (mul_le_mul_of_nonneg_left hmax hC)
  have hN := normSq0S_nonneg (H.toHistory.stageMetric (H.toHistory.activeStage v) v)
    (A.point (H.toHistory.activeStage v) (H.toHistory.activeStage_mono huv)
      (H.toHistory.activeStage_mono hvt)) 4
    (metricRm04At (H.toHistory.stageMetric (H.toHistory.activeStage v) v)
      (A.point (H.toHistory.activeStage v) (H.toHistory.activeStage_mono huv)
        (H.toHistory.activeStage_mono hvt)))
  rw [← Real.sq_sqrt hN]
  calc _ ≤ (4 * Real.sqrt 3 * (1 + phi 1 + phi 0) * (2 * M)) ^ 2 :=
        pow_le_pow_left₀ (Real.sqrt_nonneg _) h1 2
    _ = (8 * Real.sqrt 3 * (1 + phi 1 + phi 0) * M) ^ 2 := by ring

private theorem exists_cap_capture_of_chain_point_without_trace_of_comparison_late_P6N
    {p : CutoffParameters}
    {T₀ : ℝ} (records : ∀ i : Fin H.eventCount, T₀ ≤ H.time i.succ →
      GeometricCutoffRecord H.toHistory i p)
    (hcan : ∀ i hi b, ((records i hi).static b).hasCanonicalWindow)
    (hscale : ∀ i hi b z, ((records i hi).static b).neck.scale / 2 ≤
      metricScalarAt ((records i hi).static b).witness.metric
        (((records i hi).static b).witness.cap z))
    (hacc : p.modelAccuracy ≤ 1 / 2)
    {Ctime : ℝ≥0} {qcan M Dcap Dstar : ℝ} {phi : ℝ → ℝ}
    (hphi : Perelman.AdmissiblePinchingFunction phi)
    {u t : Icc (0 : ℝ) H.toHistory.horizon} (hut : u ≤ t) (hTu : T₀ ≤ (u : ℝ))
    (hpinch : ∀ j : Fin H.eventCount, Perelman.PhiAlmostNonnegative
      (H.toHistory.event j).incoming.flow (Ico (H.time j.castSucc) (H.time j.succ) ∩ Ici (u : ℝ))
      phi)
    (hlast : H.toHistory.activeStage t = Fin.last H.eventCount →
      ∃ h : H.time (Fin.last H.eventCount) < H.horizon,
        Perelman.PhiAlmostNonnegative (H.finalSlab h).flow
          (Icc (H.time (Fin.last H.eventCount)) H.horizon ∩ Ici (u : ℝ)) phi)
    (hcmp : ∀ (q : (H.toHistory.stage (H.toHistory.activeStage t)).Carrier) (C : ℝ),
      (∀ s ∈ Icc (H.toHistory.time (H.toHistory.activeStage t)) (t : ℝ),
        normSq0S (H.toHistory.stageMetric (H.toHistory.activeStage t) s) q 4
          (metricRm04At (H.toHistory.stageMetric (H.toHistory.activeStage t) s) q) ≤ C) →
      ∀ w : TangentSpace ThreeModel q,
        (H.toHistory.initialMetric (H.toHistory.activeStage t)).inner q w w ≤
          Real.exp (18 * Real.sqrt C * ((t : ℝ) - H.toHistory.time (H.toHistory.activeStage t))) *
            (H.toHistory.stageMetric (H.toHistory.activeStage t) t).inner q w w)
    {N : ℕ} (pc : ℕ → (H.toHistory.stage (H.toHistory.activeStage t)).Carrier) (δ : ℕ → ℝ)
    (hδ : ∀ k ≤ N, 0 < δ k)
    (hchain : ∀ k < N, pc (k + 1) ∈
      riemannianBallOf (H.toHistory.stageMetric (H.toHistory.activeStage t) t) (pc k) (δ k))
    (z : (H.toHistory.stage (H.toHistory.activeStage t)).Carrier)
    (hz : ∃ k ≤ N,
      z ∈ riemannianBallOf (H.toHistory.stageMetric (H.toHistory.activeStage t) t) (pc k) (δ k))
    (hzt : IsEmpty (BackwardPointTrace H.toHistory (H.toHistory.activeStage u)
      (H.toHistory.activeStage t) (H.toHistory.activeStage_mono hut) z))
    (U : Set (H.toHistory.stage (H.toHistory.activeStage t)).Carrier)
    (hchainU : ∀ k ≤ N, ∀ x ∈ riemannianBallOf
        (H.toHistory.stageMetric (H.toHistory.activeStage t) t) (pc k) (δ k), x ∈ U)
    (hslabs : ∀ i : Fin H.toHistory.eventCount,
      ∀ (first : Fin (H.toHistory.eventCount + 1)) (hle : first ≤ H.toHistory.activeStage t),
      ∀ hf : first ≤ i.castSucc, ∀ hl : i.succ ≤ H.toHistory.activeStage t,
      ∀ z ∈ U, ∀ A : BackwardPointTrace H.toHistory first (H.toHistory.activeStage t) hle z,
      ∀ v ∈ Ioo (H.toHistory.time i.castSucc) (H.toHistory.time i.succ), (u : ℝ) ≤ v →
      qcan < (H.toHistory.event i).incoming.flow.scalar v
        (A.point i.castSucc hf (i.castSucc_lt_succ.le.trans hl)) →
      |derivWithin (fun w => (H.toHistory.event i).incoming.flow.scalar w
        (A.point i.castSucc hf (i.castSucc_lt_succ.le.trans hl))) (Iic v) v| ≤
        Ctime * (H.toHistory.event i).incoming.flow.scalar v
          (A.point i.castSucc hf (i.castSucc_lt_succ.le.trans hl)) ^ 2)
    (hcur : ∀ j : Fin H.toHistory.eventCount, ∀ y : (H.toHistory.stage j.castSucc).Carrier,
      j.castSucc = H.toHistory.activeStage t → ∀ z ∈ U, HEq y z →
      ∀ v ∈ Ioo (H.toHistory.time j.castSucc) t, (u : ℝ) ≤ v →
      qcan < (H.toHistory.event j).incoming.flow.scalar v y →
      |derivWithin (fun w => (H.toHistory.event j).incoming.flow.scalar w y) (Iic v) v| ≤
        Ctime * (H.toHistory.event j).incoming.flow.scalar v y ^ 2)
    (hfinal : ∀ h : H.toHistory.time (Fin.last H.toHistory.eventCount) < H.toHistory.horizon,
      ∀ y : (H.toHistory.stage (Fin.last H.toHistory.eventCount)).Carrier,
      H.toHistory.activeStage t = Fin.last H.toHistory.eventCount → ∀ z ∈ U, HEq y z →
      ∀ v ∈ Ioo (H.toHistory.time (Fin.last H.toHistory.eventCount)) t, (u : ℝ) ≤ v →
      qcan < ((H.toHistory.finalSlab h).restrictIncoming le_rfl h le_rfl).flow.scalar v y →
      |derivWithin (fun w =>
        ((H.toHistory.finalSlab h).restrictIncoming le_rfl h le_rfl).flow.scalar w y) (Iic v) v| ≤
        Ctime * ((H.toHistory.finalSlab h).restrictIncoming le_rfl h le_rfl).flow.scalar v y ^ 2)
    (hM : 1 ≤ M) (hqcan : qcan ≤ M)
    (hspace : ∀ k ≤ N, ∀ x ∈ riemannianBallOf
        (H.toHistory.stageMetric (H.toHistory.activeStage t) t) (pc k) (δ k),
      metricScalarAt (H.toHistory.stageMetric (H.toHistory.activeStage t) t) x ≤ M)
    (htime : Ctime * M * ((t : ℝ) - u) ≤ 1 / 2)
    (hDstar : Dcap ≤ Dstar) (hDmodel : Dstar ≤ p.modelRadius)
    (hwin : 2 * StandardCap.transitionEnd + Real.sqrt (8 * M) *
      Real.exp (9 * (8 * Real.sqrt 3 * (1 + phi 1 + phi 0) * M) * ((t : ℝ) - u)) *
        ∑ i ∈ Finset.range (N + 1), δ i < Dcap) :
    ∃ (j : Fin H.eventCount) (hT : T₀ ≤ H.time j.succ) (hl : j.succ ≤ H.toHistory.activeStage t)
      (A : BackwardPointTrace H.toHistory j.succ (H.toHistory.activeStage t) hl (pc 0))
      (b : (H.toHistory.event j).RetainedBoundaryIndex) (x : standardCapWindow p.modelRadius),
      A.point j.succ le_rfl hl = ((records j hT).static b).window x ∧ ‖x.val‖ < Dcap ∧
      ((records j hT).static b).neck.scale ≤ 4 * M ∧
      ((records j hT).static b).neck.scale * ((t : ℝ) - H.time j.succ) ≤
        4 * M * ((t : ℝ) - u) := by
  classical
  set S : Set (H.toHistory.stage (H.toHistory.activeStage t)).Carrier :=
    {w | ∃ k ≤ N, w ∈ riemannianBallOf
      (H.toHistory.stageMetric (H.toHistory.activeStage t) t) (pc k) (δ k)} with hSdef
  let good : Fin H.eventCount → Prop := fun j =>
    H.toHistory.activeStage u ≤ j.castSucc ∧ ∃ (hl : j.succ ≤ H.toHistory.activeStage t)
      (w : (H.toHistory.stage (H.toHistory.activeStage t)).Carrier), w ∈ S ∧
      ∃ A : BackwardPointTrace H.toHistory j.succ (H.toHistory.activeStage t) hl w,
        ∀ p' : (H.toHistory.stage j.castSucc).Carrier,
          ¬ (H.toHistory.event j).RegularCrossing p' (A.point j.succ le_rfl hl)
  obtain ⟨j₀, hf₀, hl₀, A₀, hno₀⟩ :=
    H.toHistory.exists_latest_event_without_regularCrossing _ z hzt
  let T := Finset.univ.filter good
  have hTne : T.Nonempty :=
    ⟨j₀, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hf₀, hl₀, z, hz, A₀, hno₀⟩⟩
  obtain ⟨j, hjT, hjmax⟩ : ∃ j ∈ T, ∀ j' ∈ T, j' ≤ j :=
    ⟨T.max' hTne, T.max'_mem hTne, fun j' h => T.le_max' j' h⟩
  obtain ⟨-, hfj, hlj, zs, hzs, As, hnos⟩ := Finset.mem_filter.mp hjT
  have htr : ∀ w ∈ S,
      Nonempty (BackwardPointTrace H.toHistory j.succ (H.toHistory.activeStage t) hlj w) := by
    intro w hw
    by_contra hn
    obtain ⟨j', hf', hl', A', hno'⟩ :=
      H.toHistory.exists_latest_event_without_regularCrossing hlj w (not_nonempty_iff.mp hn)
    have hmem : j' ∈ T := Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      hfj.trans ((Fin.castSucc_lt_succ (i := j)).le.trans hf'), hl', w, hw, A', hno'⟩
    have h1 : j'.val ≤ j.val := hjmax j' hmem
    have h2 : j.val + 1 ≤ j'.val := hf'
    omega
  have hyS : pc 0 ∈ S := by
    refine ⟨0, Nat.zero_le _, ?_⟩
    change riemannianEDistOf _ (pc 0) (pc 0) < ENNReal.ofReal (δ 0)
    rw [riemannianEDistOf_self]
    exact ENNReal.ofReal_pos.mpr (hδ 0 (Nat.zero_le _))
  let u' : Icc (0 : ℝ) H.toHistory.horizon :=
    ⟨H.toHistory.time j.succ, H.toHistory.time_nonneg _, H.toHistory.time_le_horizon_at _⟩
  have hau' : H.toHistory.activeStage u' = j.succ := H.toHistory.activeStage_at_time j.succ
  have hu'u : u ≤ u' := by
    change (u : ℝ) ≤ H.toHistory.time j.succ
    by_contra hle
    have h := H.toHistory.le_activeStage u j.succ (not_le.mp hle).le
    exact absurd (h.trans hfj) (not_le_of_gt (Fin.castSucc_lt_succ (i := j)))
  have huu' : (u : ℝ) ≤ u' := hu'u
  have hT : T₀ ≤ H.time j.succ := hTu.trans huu'
  have hu't : u' ≤ t := by
    change H.toHistory.time j.succ ≤ (t : ℝ)
    exact (H.toHistory.time_strictMono.monotone hlj).trans (H.toHistory.activeStage_time_le t)
  have htime' : Ctime * M * ((t : ℝ) - u') ≤ 1 / 2 := by
    have hu : (u : ℝ) ≤ u' := hu'u
    have hC : 0 ≤ (Ctime : ℝ) * M := mul_nonneg Ctime.coe_nonneg (by linarith)
    nlinarith
  have hspaceS : ∀ q ∈ S,
      metricScalarAt (H.toHistory.stageMetric (H.toHistory.activeStage t) t) q ≤ M := by
    rintro q ⟨k, hk, hq⟩
    exact hspace k hk q hq
  have hSU : ∀ q ∈ S, q ∈ U := by
    rintro q ⟨k, hk, hq⟩
    exact hchainU k hk q hq
  have hRm : ∀ q ∈ S,
      ∀ Aq : BackwardPointTrace H.toHistory j.succ (H.toHistory.activeStage t) hlj q,
      ∀ (v : Icc (0 : ℝ) H.toHistory.horizon) (huv : u' ≤ v) (hvt : v ≤ t),
        normSq0S (H.toHistory.stageMetric (H.toHistory.activeStage v) v)
            ((Aq.restrictFirst (le_of_eq hau'.symm) (H.toHistory.activeStage_mono hu't)).point
              (H.toHistory.activeStage v) (H.toHistory.activeStage_mono huv)
              (H.toHistory.activeStage_mono hvt)) 4
          (metricRm04At (H.toHistory.stageMetric (H.toHistory.activeStage v) v)
            ((Aq.restrictFirst (le_of_eq hau'.symm) (H.toHistory.activeStage_mono hu't)).point
              (H.toHistory.activeStage v) (H.toHistory.activeStage_mono huv)
              (H.toHistory.activeStage_mono hvt))) ≤
          (8 * Real.sqrt 3 * (1 + phi 1 + phi 0) * M) ^ 2 := fun q hq Aq v huv hvt =>
    RetainedCoreHistory.normSq_stageMetric_le_of_backwardPointTrace_of_final_late_P6N H hphi
      hu't (fun j => phiAlmostNonnegative_mono_P6N (hpinch j)
        (inter_subset_inter_right _ (Ici_subset_Ici.mpr huu')))
      (fun hl => (hlast hl).imp fun _ hp => phiAlmostNonnegative_mono_P6N hp
        (inter_subset_inter_right _ (Ici_subset_Ici.mpr huu')))
      (Aq.restrictFirst (le_of_eq hau'.symm) (H.toHistory.activeStage_mono hu't))
      (fun i hf hl w hw huw => hslabs i _ _ hf hl q (hSU q hq)
        (Aq.restrictFirst (le_of_eq hau'.symm) (H.toHistory.activeStage_mono hu't)) w hw
        (huu'.trans huw))
      (fun j y hj hy w hw huw => hcur j y hj q (hSU q hq) hy w hw (huu'.trans huw))
      (fun h y ht hy w hw huw => hfinal h y ht q (hSU q hq) hy w hw (huu'.trans huw)) hM hqcan
      (hspaceS q hq) htime' v huv hvt
  obtain ⟨b, zc, hzc⟩ := (records j hT).exists_cap_of_not_regularCrossing_target hnos
  obtain ⟨-, -, -, -, -, -, -, hcap⟩ := hcan j hT b
  obtain ⟨xz, hxzn, hxz⟩ := hcap zc
  have hsM : ((records j hT).static b).neck.scale ≤ 4 * M := by
    have hb := H.scalar_le_two_mul_of_backwardPointTrace_of_derivative_bounds_window_P6N hu't
      (As.restrictFirst (le_of_eq hau'.symm) (H.toHistory.activeStage_mono hu't))
      (fun i hf hl w hw huw => hslabs i _ _ hf hl zs (hSU zs hzs)
        (As.restrictFirst (le_of_eq hau'.symm) (H.toHistory.activeStage_mono hu't)) w hw
        (huu'.trans huw))
      (fun j y hj hy w hw huw => hcur j y hj zs (hSU zs hzs) hy w hw (huu'.trans huw))
      (fun h y ht hy w hw huw => hfinal h y ht zs (hSU zs hzs) hy w hw (huu'.trans huw))
      (by linarith) hqcan (hspaceS zs hzs) htime' u' le_rfl hu't
    have heq := BackwardPointTrace.apply_point_eq_of_stage_eq As
      (fun m q => metricScalarAt (H.toHistory.stageMetric m (H.toHistory.time j.succ)) q)
      hau' ((le_of_eq hau'.symm).trans (H.toHistory.activeStage_mono (le_refl u')))
      (H.toHistory.activeStage_mono hu't) le_rfl hlj
    have h2 : metricScalarAt ((records j hT).static b).witness.metric
        (((records j hT).static b).witness.cap zc) ≤ 2 * M := by
      rw [((records j hT).static b).scalar_eq, ← hzc, H.toHistory.event_output j,
        ← H.toHistory.stageMetric_initial]
      exact heq.symm.le.trans hb
    linarith [hscale j hT b zc]
  have hage : ((records j hT).static b).neck.scale * ((t : ℝ) - H.time j.succ) ≤
      4 * M * ((t : ℝ) - u) := by
    have hu : (u : ℝ) ≤ H.time j.succ := hu'u
    have hT : H.time j.succ ≤ (t : ℝ) := hu't
    nlinarith [mul_le_mul_of_nonneg_left hsM (sub_nonneg.mpr hT)]
  have hΛ0 : 0 ≤ 8 * Real.sqrt 3 * (1 + phi 1 + phi 0) * M := by
    have := hphi.pos 0
    have := hphi.pos 1
    have : 0 ≤ M := by linarith
    positivity
  have hlocal : ∀ q : H.toHistory.backwardSurvivorDomain j.succ (H.toHistory.activeStage t) hlj,
      q.val ∈ S → ∀ v : TangentSpace ThreeModel q,
        (H.toHistory.backwardSurvivorInitialMetric j.succ (H.toHistory.activeStage t) hlj j.succ
          le_rfl hlj).inner q v v ≤
        Real.exp (18 * (8 * Real.sqrt 3 * (1 + phi 1 + phi 0) * M) *
          ((t : ℝ) - H.toHistory.time j.succ)) *
          ((H.toHistory.stageMetric (H.toHistory.activeStage t) t).restrictOpen
            (H.toHistory.backwardSurvivorDomain j.succ (H.toHistory.activeStage t) hlj)).inner
            q v v := by
    intro q hq v
    have hb1 : ∀ v : Icc (0 : ℝ) H.toHistory.horizon, H.toHistory.time j.succ ≤ v →
        (v : ℝ) ≤ H.toHistory.time (H.toHistory.activeStage t) →
        ∀ (hf : j.succ ≤ H.toHistory.activeStage v)
          (hl : H.toHistory.activeStage v ≤ H.toHistory.activeStage t),
          normSq0S (H.toHistory.stageMetric (H.toHistory.activeStage v) v)
              ((Classical.choice q.property).point (H.toHistory.activeStage v) hf hl) 4
            (metricRm04At (H.toHistory.stageMetric (H.toHistory.activeStage v) v)
              ((Classical.choice q.property).point (H.toHistory.activeStage v) hf hl)) ≤
            (8 * Real.sqrt 3 * (1 + phi 1 + phi 0) * M) ^ 2 := fun v hv1 hv2 _ _ =>
      hRm q.val hq (Classical.choice q.property) v hv1
        (hv2.trans (H.toHistory.activeStage_time_le t))
    have hb2 : ∀ s ∈ Icc (H.toHistory.time (H.toHistory.activeStage t)) (t : ℝ),
        normSq0S (H.toHistory.stageMetric (H.toHistory.activeStage t) s) q.val 4
          (metricRm04At (H.toHistory.stageMetric (H.toHistory.activeStage t) s) q.val) ≤
          (8 * Real.sqrt 3 * (1 + phi 1 + phi 0) * M) ^ 2 := by
      intro s hs
      let v : Icc (0 : ℝ) H.toHistory.horizon :=
        ⟨s, (H.toHistory.time_nonneg _).trans hs.1, hs.2.trans t.2.2⟩
      have hav : H.toHistory.activeStage v = H.toHistory.activeStage t :=
        ObservedHistory.activeStage_eq_of_time_mem H.toHistory v _ hs.1 (fun i' h =>
          hs.2.trans_lt
            (ObservedHistory.time_lt_succ_of_activeStage_eq_castSucc H.toHistory t i' h))
      have huv : u' ≤ v := by
        change H.toHistory.time j.succ ≤ s
        exact (H.toHistory.time_strictMono.monotone hlj).trans hs.1
      have hb := hRm q.val hq (Classical.choice q.property) v huv hs.2
      have heq := BackwardPointTrace.apply_point_eq_of_stage_eq
        ((Classical.choice q.property).restrictFirst (le_of_eq hau'.symm)
          (H.toHistory.activeStage_mono hu't))
        (fun m x => normSq0S (H.toHistory.stageMetric m s) x 4
          (metricRm04At (H.toHistory.stageMetric m s) x))
        hav (H.toHistory.activeStage_mono huv) (H.toHistory.activeStage_mono hs.2)
        (H.toHistory.activeStage_mono hu't) le_rfl
      rw [BackwardPointTrace.endpoint_eq] at heq
      exact heq.symm.le.trans hb
    have h1 := ObservedHistory.backwardSurvivorInitialMetric_inner_le_exp H.toHistory hlj q hb1 v
    have h2 := hcmp q.val _ hb2 v
    rw [Real.sqrt_sq hΛ0] at h1 h2
    rw [SmoothRiemannianMetric.restrictOpen_inner]
    calc _ ≤ _ := h1
      _ ≤ _ := mul_le_mul_of_nonneg_left h2 (Real.exp_pos _).le
      _ = _ := by
        rw [← mul_assoc, ← Real.exp_add]
        congr 2
        ring
  set U := H.toHistory.backwardSurvivorDomain j.succ (H.toHistory.activeStage t) hlj with hUdef
  let y' : U := ⟨pc 0, htr (pc 0) hyS⟩
  let z' : U := ⟨zs, htr zs hzs⟩
  obtain ⟨kz, hkz, hzk⟩ := hzs
  have hz'' := riemannianEDistOf_lt_sqrt_mul_sum_of_ball_chain
    (H.toHistory.stageMetric (H.toHistory.activeStage t) t) U
    (H.toHistory.backwardSurvivorInitialMetric j.succ (H.toHistory.activeStage t) hlj j.succ
      le_rfl hlj) (Real.exp_pos (18 * (8 * Real.sqrt 3 * (1 + phi 1 + phi 0) * M) *
        ((t : ℝ) - H.toHistory.time j.succ))) hδ
    (fun k hk w hw => htr w ⟨k, hk, hw⟩) hchain (fun q hq v => hlocal q hq v) y' rfl kz hkz
    z' hzk
  have hmono : ∑ i ∈ Finset.range (kz + 1), δ i ≤ ∑ i ∈ Finset.range (N + 1), δ i :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.mpr (by omega))
      (fun i hi _ => (hδ i (by have := Finset.mem_range.mp hi; omega)).le)
  have hmap := Geometry.Metric.edistOf_le_of_quad_of_localDiffeomorph
    (H.toHistory.backwardSurvivorInitialMetric j.succ (H.toHistory.activeStage t) hlj j.succ
      le_rfl hlj)
    (H.toHistory.initialMetric j.succ)
    (H.toHistory.backwardSurvivorMap j.succ (H.toHistory.activeStage t) hlj j.succ le_rfl hlj)
    (H.toHistory.backwardSurvivorMap_isLocalDiffeomorph _ _ hlj j.succ le_rfl hlj) one_pos
    (fun x v => by
      rw [one_mul, ObservedHistory.backwardSurvivorInitialMetric, localPullMetric_inner])
    y' z'
  have hΦz : H.toHistory.backwardSurvivorMap j.succ (H.toHistory.activeStage t) hlj j.succ le_rfl
      hlj z' = As.point j.succ le_rfl hlj :=
    H.toHistory.backwardSurvivorMap_eq_point _ _ hlj j.succ le_rfl hlj z' As
  have hexp : Real.sqrt (Real.exp (18 * (8 * Real.sqrt 3 * (1 + phi 1 + phi 0) * M) *
      ((t : ℝ) - H.toHistory.time j.succ))) =
      Real.exp (9 * (8 * Real.sqrt 3 * (1 + phi 1 + phi 0) * M) *
        ((t : ℝ) - H.toHistory.time j.succ)) := by
    rw [show 18 * (8 * Real.sqrt 3 * (1 + phi 1 + phi 0) * M) *
        ((t : ℝ) - H.toHistory.time j.succ) =
        9 * (8 * Real.sqrt 3 * (1 + phi 1 + phi 0) * M) * ((t : ℝ) - H.toHistory.time j.succ) +
        9 * (8 * Real.sqrt 3 * (1 + phi 1 + phi 0) * M) * ((t : ℝ) - H.toHistory.time j.succ)
        by ring, Real.exp_add, Real.sqrt_mul_self (Real.exp_pos _).le]
  have hsum0 : 0 ≤ ∑ i ∈ Finset.range (N + 1), δ i :=
    Finset.sum_nonneg fun i hi => (hδ i (by have := Finset.mem_range.mp hi; omega)).le
  set dd := Real.exp (9 * (8 * Real.sqrt 3 * (1 + phi 1 + phi 0) * M) *
      ((t : ℝ) - H.toHistory.time j.succ)) * ∑ i ∈ Finset.range (N + 1), δ i with hdd
  have hnear : riemannianEDistOf (H.toHistory.initialMetric j.succ)
      (((records j hT).static b).window xz)
      ((Classical.choice (htr (pc 0) hyS)).point j.succ le_rfl hlj) ≤ ENNReal.ofReal dd := by
    rw [hxz, ← hzc, ← hΦz, riemannianEDistOf_comm]
    rw [hexp] at hz''
    refine hmap.trans ?_
    rw [Real.sqrt_one, ENNReal.ofReal_one, one_mul]
    refine hz''.le.trans (ENNReal.ofReal_le_ofReal ?_)
    exact mul_le_mul_of_nonneg_left hmono (Real.exp_pos _).le
  have hwin' : 2 * StandardCap.transitionEnd + Real.sqrt (8 * M) *
      (Real.exp (9 * (8 * Real.sqrt 3 * (1 + phi 1 + phi 0) * M) * ((t : ℝ) - u)) *
        ∑ i ∈ Finset.range (N + 1), δ i) < Dcap := by
    rw [← mul_assoc]
    exact hwin
  have hdd' : dd ≤ Real.exp (9 * (8 * Real.sqrt 3 * (1 + phi 1 + phi 0) * M) *
      ((t : ℝ) - u)) * ∑ i ∈ Finset.range (N + 1), δ i := by
    have hu : (u : ℝ) ≤ H.toHistory.time j.succ := hu'u
    refine mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr ?_) hsum0
    exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  obtain ⟨x, hxn', hxeq⟩ := RetainedCoreHistory.exists_window_point_of_edist_le_record_P6N H
    (records j hT) (hcan j hT) hacc b hsM hDstar hDmodel xz hxzn _
    (hnear.trans (ENNReal.ofReal_le_ofReal hdd'))
    (mul_nonneg (Real.exp_pos _).le hsum0) hwin'
  exact ⟨j, hT, hlj, Classical.choice (htr (pc 0) hyS), b, x, hxeq.symm, hxn', hsM, hage⟩

/-- **`_P6N`（`BTCC:358` 窗口形）**：`BTCC:358_P6L` 的 `hslabs`/`hcurrent` 只在 `[u, t]` 内要
（guard `(u : ℝ) ≤ v`）。结论逐字。 -/
theorem capWindowPoint_of_chain_point_without_trace_late_P6N {p : CutoffParameters}
    {T₀ : ℝ} (records : ∀ i : Fin H.eventCount, T₀ ≤ H.time i.succ →
      GeometricCutoffRecord H.toHistory i p)
    (hcan : ∀ i hi b, ((records i hi).static b).hasCanonicalWindow)
    (hscale : ∀ i hi b z, ((records i hi).static b).neck.scale / 2 ≤
      metricScalarAt ((records i hi).static b).witness.metric
        (((records i hi).static b).witness.cap z))
    (hacc : p.modelAccuracy ≤ 1 / 2)
    {Ctime : ℝ≥0} {qcan M Dcap Dstar θcap : ℝ} {phi : ℝ → ℝ}
    (hphi : Perelman.AdmissiblePinchingFunction phi)
    {u t : Icc (0 : ℝ) H.toHistory.horizon} (hut : u ≤ t) (hTu : T₀ ≤ (u : ℝ))
    (hpinch : ∀ j : Fin H.eventCount, Perelman.PhiAlmostNonnegative
      (H.toHistory.event j).incoming.flow (Ico (H.time j.castSucc) (H.time j.succ) ∩ Ici (u : ℝ))
      phi) (i : Fin H.eventCount)
    (hi : H.toHistory.activeStage t = i.castSucc)
    {N : ℕ} (pc : ℕ → (H.toHistory.stage (H.toHistory.activeStage t)).Carrier) (δ : ℕ → ℝ)
    (hδ : ∀ k ≤ N, 0 < δ k)
    (hchain : ∀ k < N, pc (k + 1) ∈
      riemannianBallOf (H.toHistory.stageMetric (H.toHistory.activeStage t) t) (pc k) (δ k))
    (z : (H.toHistory.stage (H.toHistory.activeStage t)).Carrier)
    (hz : ∃ k ≤ N,
      z ∈ riemannianBallOf (H.toHistory.stageMetric (H.toHistory.activeStage t) t) (pc k) (δ k))
    (hzt : IsEmpty (BackwardPointTrace H.toHistory (H.toHistory.activeStage u)
      (H.toHistory.activeStage t) (H.toHistory.activeStage_mono hut) z))
    (U : Set (H.toHistory.stage (H.toHistory.activeStage t)).Carrier)
    (hchainU : ∀ k ≤ N, ∀ x ∈ riemannianBallOf
        (H.toHistory.stageMetric (H.toHistory.activeStage t) t) (pc k) (δ k), x ∈ U)
    (hslabs : ∀ i : Fin H.toHistory.eventCount,
      ∀ (first : Fin (H.toHistory.eventCount + 1)) (hle : first ≤ H.toHistory.activeStage t),
      ∀ hf : first ≤ i.castSucc, ∀ hl : i.succ ≤ H.toHistory.activeStage t,
      ∀ z ∈ U, ∀ A : BackwardPointTrace H.toHistory first (H.toHistory.activeStage t) hle z,
      ∀ v ∈ Ioo (H.toHistory.time i.castSucc) (H.toHistory.time i.succ), (u : ℝ) ≤ v →
      qcan < (H.toHistory.event i).incoming.flow.scalar v
        (A.point i.castSucc hf (i.castSucc_lt_succ.le.trans hl)) →
      |derivWithin (fun w => (H.toHistory.event i).incoming.flow.scalar w
        (A.point i.castSucc hf (i.castSucc_lt_succ.le.trans hl))) (Iic v) v| ≤
        Ctime * (H.toHistory.event i).incoming.flow.scalar v
          (A.point i.castSucc hf (i.castSucc_lt_succ.le.trans hl)) ^ 2)
    (hcurrent : ∀ y : (H.toHistory.stage i.castSucc).Carrier, ∀ z ∈ U, HEq y z →
      ∀ v ∈ Ioo (H.toHistory.time i.castSucc) t, (u : ℝ) ≤ v →
      qcan < (H.toHistory.event i).incoming.flow.scalar v y →
      |derivWithin (fun w => (H.toHistory.event i).incoming.flow.scalar w y) (Iic v) v| ≤
        Ctime * (H.toHistory.event i).incoming.flow.scalar v y ^ 2)
    (hM : 1 ≤ M) (hqcan : qcan ≤ M)
    (hspace : ∀ k ≤ N, ∀ x ∈ riemannianBallOf
        (H.toHistory.stageMetric (H.toHistory.activeStage t) t) (pc k) (δ k),
      metricScalarAt (H.toHistory.stageMetric (H.toHistory.activeStage t) t) x ≤ M)
    (htime : Ctime * M * ((t : ℝ) - u) ≤ 1 / 2)
    (hDstar : Dcap ≤ Dstar) (hDmodel : Dstar ≤ p.modelRadius)
    (hθ : 4 * M * ((t : ℝ) - u) ≤ θcap)
    (hwin : 2 * StandardCap.transitionEnd + Real.sqrt (8 * M) *
      Real.exp (9 * (8 * Real.sqrt 3 * (1 + phi 1 + phi 0) * M) * ((t : ℝ) - u)) *
        ∑ i ∈ Finset.range (N + 1), δ i < Dcap) :
    ∃ (j : Fin H.eventCount) (hT : T₀ ≤ H.time j.succ) (hl : j.succ ≤ H.toHistory.activeStage t)
      (A : BackwardPointTrace H.toHistory j.succ (H.toHistory.activeStage t) hl (pc 0))
      (b : (H.toHistory.event j).RetainedBoundaryIndex) (x : standardCapWindow p.modelRadius),
      A.point j.succ le_rfl hl = ((records j hT).static b).window x ∧ ‖x.val‖ < Dcap + 1 ∧
        (t : ℝ) - H.time j.succ ≤ θcap * (((records j hT).static b).neck.scale)⁻¹ := by
  have hne : H.toHistory.activeStage t ≠ Fin.last H.eventCount := by
    rw [hi]
    exact Fin.castSucc_ne_last i
  obtain ⟨j, hT, hl, A, b, x, hx, hxn, -, hage⟩ :=
    exists_cap_capture_of_chain_point_without_trace_of_comparison_late_P6N H records hcan hscale
      hacc hphi hut hTu hpinch (fun h => absurd h hne)
      (fun q _ hb w => ObservedHistory.initialMetric_inner_le_exp_of_normSq_le H.toHistory hi q
        (H.toHistory.activeStage_time_le t)
        (ObservedHistory.time_lt_succ_of_activeStage_eq_castSucc H.toHistory t i hi) hb w)
      pc δ hδ hchain z hz hzt U hchainU hslabs
      (fun j y hj => by
        have : j = i := Fin.castSucc_injective _ (hj.trans hi)
        subst this
        exact hcurrent y)
      (fun _ _ h => absurd h hne) hM hqcan hspace htime hDstar hDmodel hwin
  refine ⟨j, hT, hl, A, b, x, hx, by linarith, ?_⟩
  rw [← div_eq_mul_inv, le_div_iff₀ ((records j hT).static b).neck.scale_pos]
  linarith

/-- **`_P6N`（`BTCC:409` 窗口形）**：`BTCC:409_P6L` 的 `hslabs`/`hfinal` 只在 `[u, t]` 内要
（guard `(u : ℝ) ≤ v`）。结论逐字。 -/
theorem capWindowPoint_of_chain_point_without_trace_of_activeStage_eq_last_late_P6N
    {p : CutoffParameters}
    {T₀ : ℝ} (records : ∀ i : Fin H.eventCount, T₀ ≤ H.time i.succ →
      GeometricCutoffRecord H.toHistory i p)
    (hcan : ∀ i hi b, ((records i hi).static b).hasCanonicalWindow)
    (hscale : ∀ i hi b z, ((records i hi).static b).neck.scale / 2 ≤
      metricScalarAt ((records i hi).static b).witness.metric
        (((records i hi).static b).witness.cap z))
    (hacc : p.modelAccuracy ≤ 1 / 2)
    {Ctime : ℝ≥0} {qcan M Dcap Dstar θcap : ℝ} {phi : ℝ → ℝ}
    (hphi : Perelman.AdmissiblePinchingFunction phi)
    {u t : Icc (0 : ℝ) H.toHistory.horizon} (hut : u ≤ t) (hTu : T₀ ≤ (u : ℝ))
    (hpinch : ∀ j : Fin H.eventCount, Perelman.PhiAlmostNonnegative
      (H.toHistory.event j).incoming.flow (Ico (H.time j.castSucc) (H.time j.succ) ∩ Ici (u : ℝ))
      phi)
    (h : H.time (Fin.last H.eventCount) < H.horizon)
    (hlastA : H.toHistory.activeStage t = Fin.last H.eventCount)
    (hfinalPinch : Perelman.PhiAlmostNonnegative (H.finalSlab h).flow
      (Icc (H.time (Fin.last H.eventCount)) H.horizon ∩ Ici (u : ℝ)) phi)
    {N : ℕ} (pc : ℕ → (H.toHistory.stage (H.toHistory.activeStage t)).Carrier) (δ : ℕ → ℝ)
    (hδ : ∀ k ≤ N, 0 < δ k)
    (hchain : ∀ k < N, pc (k + 1) ∈
      riemannianBallOf (H.toHistory.stageMetric (H.toHistory.activeStage t) t) (pc k) (δ k))
    (z : (H.toHistory.stage (H.toHistory.activeStage t)).Carrier)
    (hz : ∃ k ≤ N,
      z ∈ riemannianBallOf (H.toHistory.stageMetric (H.toHistory.activeStage t) t) (pc k) (δ k))
    (hzt : IsEmpty (BackwardPointTrace H.toHistory (H.toHistory.activeStage u)
      (H.toHistory.activeStage t) (H.toHistory.activeStage_mono hut) z))
    (U : Set (H.toHistory.stage (H.toHistory.activeStage t)).Carrier)
    (hchainU : ∀ k ≤ N, ∀ x ∈ riemannianBallOf
        (H.toHistory.stageMetric (H.toHistory.activeStage t) t) (pc k) (δ k), x ∈ U)
    (hslabs : ∀ i : Fin H.toHistory.eventCount,
      ∀ (first : Fin (H.toHistory.eventCount + 1)) (hle : first ≤ H.toHistory.activeStage t),
      ∀ hf : first ≤ i.castSucc, ∀ hl : i.succ ≤ H.toHistory.activeStage t,
      ∀ z ∈ U, ∀ A : BackwardPointTrace H.toHistory first (H.toHistory.activeStage t) hle z,
      ∀ v ∈ Ioo (H.toHistory.time i.castSucc) (H.toHistory.time i.succ), (u : ℝ) ≤ v →
      qcan < (H.toHistory.event i).incoming.flow.scalar v
        (A.point i.castSucc hf (i.castSucc_lt_succ.le.trans hl)) →
      |derivWithin (fun w => (H.toHistory.event i).incoming.flow.scalar w
        (A.point i.castSucc hf (i.castSucc_lt_succ.le.trans hl))) (Iic v) v| ≤
        Ctime * (H.toHistory.event i).incoming.flow.scalar v
          (A.point i.castSucc hf (i.castSucc_lt_succ.le.trans hl)) ^ 2)
    (hfinal : ∀ y : (H.toHistory.stage (Fin.last H.eventCount)).Carrier, ∀ z ∈ U, HEq y z →
      ∀ v ∈ Ioo (H.time (Fin.last H.eventCount)) t, (u : ℝ) ≤ v →
      qcan < ((H.finalSlab h).restrictIncoming le_rfl h le_rfl).flow.scalar v y →
      |derivWithin (fun w => ((H.finalSlab h).restrictIncoming le_rfl h le_rfl).flow.scalar w y)
        (Iic v) v| ≤ Ctime * ((H.finalSlab h).restrictIncoming le_rfl h le_rfl).flow.scalar v y ^ 2)
    (hM : 1 ≤ M) (hqcan : qcan ≤ M)
    (hspace : ∀ k ≤ N, ∀ x ∈ riemannianBallOf
        (H.toHistory.stageMetric (H.toHistory.activeStage t) t) (pc k) (δ k),
      metricScalarAt (H.toHistory.stageMetric (H.toHistory.activeStage t) t) x ≤ M)
    (htime : Ctime * M * ((t : ℝ) - u) ≤ 1 / 2)
    (hDstar : Dcap ≤ Dstar) (hDmodel : Dstar ≤ p.modelRadius)
    (hθ : 4 * M * ((t : ℝ) - u) ≤ θcap)
    (hwin : 2 * StandardCap.transitionEnd + Real.sqrt (8 * M) *
      Real.exp (9 * (8 * Real.sqrt 3 * (1 + phi 1 + phi 0) * M) * ((t : ℝ) - u)) *
        ∑ i ∈ Finset.range (N + 1), δ i < Dcap) :
    ∃ (j : Fin H.eventCount) (hT : T₀ ≤ H.time j.succ) (hl : j.succ ≤ H.toHistory.activeStage t)
      (A : BackwardPointTrace H.toHistory j.succ (H.toHistory.activeStage t) hl (pc 0))
      (b : (H.toHistory.event j).RetainedBoundaryIndex) (x : standardCapWindow p.modelRadius),
      A.point j.succ le_rfl hl = ((records j hT).static b).window x ∧ ‖x.val‖ < Dcap + 1 ∧
        (t : ℝ) - H.time j.succ ≤ θcap * (((records j hT).static b).neck.scale)⁻¹ := by
  obtain ⟨j, hT, hl, A, b, x, hx, hxn, -, hage⟩ :=
    exists_cap_capture_of_chain_point_without_trace_of_comparison_late_P6N H records hcan hscale
      hacc hphi hut hTu hpinch (fun _ => ⟨h, hfinalPinch⟩)
      (fun q _ hb w => ObservedHistory.initialMetric_inner_le_exp_of_normSq_le_of_eq_last
        H.toHistory hlastA h q (H.toHistory.activeStage_time_le t) t.2.2 hb w)
      pc δ hδ hchain z hz hzt U hchainU hslabs
      (fun j _ hj => absurd (hj.trans hlastA) (Fin.castSucc_ne_last j))
      (fun _ y _ => hfinal y) hM hqcan hspace htime hDstar hDmodel hwin
  refine ⟨j, hT, hl, A, b, x, hx, by linarith, ?_⟩
  rw [← div_eq_mul_inv, le_div_iff₀ ((records j hT).static b).neck.scale_pos]
  linarith

/-- consumer：G1 窗口形 `BTCC:358`（全 family、全 `EventSlabsPinched`）⇐ late-records 形取 `T₀ = 0`
（`0 ≤ time` 平凡），结论展开形 = `CapWindowPoint`。 -/
example : type_of% @capWindowPoint_of_chain_point_without_trace_window_P6N.{u} := by
  intro H p records hcan hscale hacc Ctime qcan M Dcap Dstar θcap phi hphi hpinch u t hut i hi N pc
    δ hδ hchain z hz hzt U hchainU hslabs hcurrent hM hqcan hspace htime hDstar hDmodel hθ hwin
  obtain ⟨j, -, hl, A, b, x, hx, hxn, hθ'⟩ := capWindowPoint_of_chain_point_without_trace_late_P6N
    H (T₀ := 0) (fun i _ => records i) (fun i _ b => hcan i b) (fun i _ b z => hscale i b z) hacc
    hphi hut u.2.1 (fun j => phiAlmostNonnegative_mono_P6N (hpinch j) inter_subset_left) i hi pc δ
    hδ hchain z hz hzt U hchainU hslabs hcurrent hM hqcan hspace htime hDstar hDmodel hθ hwin
  exact ⟨j, hl, A, b, x, hx, hxn, hθ'⟩

end RetainedCoreHistory

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
