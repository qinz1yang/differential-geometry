import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6StageTransferP6ST2

/-!
# S-c G3：buffered transfer 的逆否 ⇒ localized bad points（O-CH11-STAB2 G3，后缀 `_P6ST2`）

R-C11-7 D-11 / D-12。G1 transfer 的逆否：footprint 层（`BufferedFootprintData_P6ST2`）+ 目标层 `¬ witness`
⇒ **frequently** 在 `(v n, p)`（**同一个 crossing 前点 `p`**）没有 fine-margin witness
（`frequently_not_fineMargin_P6ST2`）。与 `v n → s`、`Q_n / Q₊ → 1`（合同 `scalar_tendsto` 生产，不再是
binder）和 seed-distance 的显式 eventual binder 合取，即得 CX-STAGE 的 `LeftLocalizedBadAt_CXST`
（history 层 `stage_class_localizedBad_P6ST2`：time = slab 时刻，Bad = fine-margin 坏，
scalar / seed distance 取 history 度量）。

精度层级（D-11）显式：
* `ε_in`：P6P compactness 输入精度，与本层无关（`false_of_rerun_decoupled_P6P` 自行量化）；
* `η_bad := ηfine ≤ neckModelTolerance (ηout/2)`，带 margins `m`：localized 坏点 = 没有
  `(ηfine, C1, C2)` 且 `HasMargins m` 的 witness；
* `η_recovery ≤ η_bad`：`fineMargin_of_recovery_P6ST2`——恢复的 witness 精度 `η_rec ≤ ηfine`、常数
  `≤ (C1, C2)`、margins `m' ≥ m` ⇒ fine-margin witness，与坏点矛盾。**recovery 必须同时输出 margins**：
  坏点谓词是 fine-margin 坏而非 `¬ Good_{η_bad}`（`HasSpatialCanonicalTimeControl` 不记录 margins）。
-/

set_option autoImplicit false

noncomputable section

open Set Filter Function
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open scoped Manifold NNReal Topology ContDiff ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

open Perelman.CanonicalNeighborhood.FiniteHorn

section Recovery

variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold I3 ∞ M] [T2Space M] [SigmaCompactSpace M] {g : SmoothRiemannianMetric I3 M}
  {x : M}

/-- `HasMargins` 对 margin 参数单调：`m ≤ m'` 时 `HasMargins m' ⇒ HasMargins m`。 -/
theorem hasMargins_mono_P6ST2 {eps C1 C2 m m' : ℝ} {W : SpatialCanonicalWitness g eps C1 C2 x}
    (h : W.HasMargins m') (hm : m ≤ m') : W.HasMargins m := by
  obtain ⟨hshape, hrad, hin, hout, hdeep⟩ := h
  have hsq : 0 < Real.sqrt (metricScalarAt g x) := Real.sqrt_pos.mpr W.Q_pos
  have hr : 0 ≤ W.radius := (inv_pos.mpr hsq).le.trans W.radius_lower
  refine ⟨hshape, ?_, ?_, ?_, ?_⟩
  · exact (div_le_div_of_nonneg_right (by linarith) hsq.le).trans hrad
  · exact (riemannianBallOf_mono g x (mul_le_mul_of_nonneg_right (by linarith) hr)).trans hin
  · exact hout.trans (riemannianBallOf_mono g x (mul_le_mul_of_nonneg_right (by linarith) hr))
  · intro c d hcd y hy
    exact (div_le_div_of_nonneg_right (by linarith) hsq.le).trans (hdeep c d hcd y hy)

/-- **`η_recovery ≤ η_bad` 层**：恢复 witness（精度 `ηrec ≤ ηbad < 1/11`、常数 `C1r ≤ C1`、`C2r ≤ C2`、
margins `m' ≥ m`、chart）⇒ `(ηbad, C1, C2)` 的 fine-margin witness。 -/
theorem fineMargin_of_recovery_P6ST2 {ηrec ηbad C1r C2r C1 C2 m m' : ℝ} (hη : ηrec ≤ ηbad)
    (hsmall : ηbad < 1 / 11) (hC1 : C1r ≤ C1) (hC2 : C2r ≤ C2) (hm : m ≤ m')
    {W : SpatialCanonicalWitness g ηrec C1r C2r x} (hc : W.capTubeHasNeckChart ηrec)
    (hW : W.HasMargins m') :
    ∃ W' : SpatialCanonicalWitness g ηbad C1 C2 x,
      W'.capTubeHasNeckChart ηbad ∧ W'.HasMargins m :=
  ⟨(W.monoEps hη hsmall).enlargeConstants hC1 hC2,
    (hc.mono_eps hη hsmall hη hsmall).enlarge_constants hC1 hC2,
    (hasMargins_monoEps_P6ST2 (hasMargins_mono_P6ST2 hW hm) hη hsmall).enlarge_constants hC1 hC2⟩

end Recovery

/-- 标量在 stage / 度量 / 点的 `HEq` 下不变。 -/
theorem scalar_heq_P6ST2 {P Q : OrientedThreeStage.{u}} (hPQ : P = Q) {g : P.Metric}
    {g' : Q.Metric} (hg : HEq g g') {x : P.Carrier} {x' : Q.Carrier} (hx : HEq x x') :
    metricScalarAt g x = metricScalarAt g' x' := by
  subst hPQ
  cases eq_of_heq hg
  cases eq_of_heq hx
  rfl

namespace MetricCutCapEvent

variable {P Q : OrientedThreeStage.{u}} {a s : ℝ} {E : MetricCutCapEvent P Q a s}
  {p : P.Carrier} {q : Q.Carrier} {ηfine ηout C1 C2 m : ℝ} {k : ℕ}

/-- **G1 的逆否（event 层）**：footprint 层 + `ηfine ≤ neckModelTolerance (ηout/2)` + 目标层 `¬ witness`
（常数 `C1out ≥ 2C1`、`C2out ≥ 1000C2`）⇒ frequently 在 `(v n, p)` 没有 fine-margin witness。 -/
theorem frequently_not_fineMargin_P6ST2 (D : E.BufferedFootprintData_P6ST2 p q ηout C1 C2 m k)
    (hle : ηfine ≤ neckModelTolerance (ηout / 2)) {C1out C2out : ℝ} (h1 : 2 * C1 ≤ C1out)
    (h2 : 1000 * C2 ≤ C2out)
    (hnot : ¬ ∃ W : SpatialCanonicalWitness E.outputMetric ηout C1out C2out q,
      W.capTubeHasNeckChart ηout) :
    ∃ᶠ n in atTop, ¬ ∃ W : SpatialCanonicalWitness (E.incoming.flow.base.metric (D.v n)) ηfine
      C1 C2 p, W.capTubeHasNeckChart ηfine ∧ W.HasMargins m := by
  intro h
  exact hnot (spatialWitness_of_bufferedTransfer_P6ST2
    (BufferedTransferData_P6ST2.ofFootprint_P6ST2 D hle (h.mono fun _ hn => not_not.mp hn)) h1 h2)

end MetricCutCapEvent

namespace ObservedHistory

/-- slab 内 history 度量 `HEq` event incoming 度量。 -/
theorem stageMetric_slab_heq_P6ST2 {H : ObservedHistory.{u}} (i : Fin H.eventCount)
    {t : Icc (0 : ℝ) H.horizon} (h0 : H.time i.castSucc ≤ t) (h1 : (t : ℝ) < H.time i.succ) :
    HEq (H.stageMetric (H.activeStage t) t) ((H.event i).incoming.flow.base.metric t) :=
  (stageMetric_heq_of_idx_P6S2 H (H.activeStage_eq_castSucc_P6ST2 i t h0 h1) _).trans
    (heq_of_eq (stageMetric_castSucc_apply i _))

end ObservedHistory

namespace GeometricCutoffRecord

variable {H : ObservedHistory.{u}} {i : Fin H.eventCount} {p : CutoffParameters}

/-- **G3 主定理（history 层 localized bad points）**：stage 时刻 post 点 `y`（`¬ Good_{ηout,C1out,C2out}`），
S-a（`hcapW`）+ `hfoot`（在 `y` 的 crossing 对上给 footprint 数据 `D`，并给出沿 `D.v` 的 seed-distance
eventual 界：`d_t(seed t, z) ≤ D0 + L/(4√R_y)`，`(t, z)` 是 `(D.v n, p')` 的 history 版）⇒
`LeftLocalizedBadAt_CXST`：time = slab 时刻，Bad = fine-margin 坏（`ηfine`、`HasMargins m`），scalar /
seed distance 取 history 度量，`σ = time i.succ`、`R = R_y`。曲率比 `→ 1` 由合同 `scalar_tendsto` 生产；
坏点就是 crossing 前点 `p'` 本身（空间 localized）。 -/
theorem stage_class_localizedBad_P6ST2 (R : GeometricCutoffRecord H i p)
    {ηfine ηout C1 C2 m C1out C2out : ℝ} {k : ℕ} {Ctime : ℝ≥0}
    (h1 : 2 * C1 ≤ C1out) (h2 : 1000 * C2 ≤ C2out) (hle : ηfine ≤ neckModelTolerance (ηout / 2))
    (hcapW : ∀ (b : (H.event i).RetainedBoundaryIndex) (x : ThreeBall),
      ∃ W : SpatialCanonicalWitness (H.event i).outputMetric ηout C1out C2out
        ((R.static b).inclusion ((R.static b).witness.cap x)), W.capTubeHasNeckChart ηout)
    {y : (H.stageAt (H.stageTime i.succ)).Carrier}
    (seed : ∀ t : Icc (0 : ℝ) H.horizon, (H.stageAt t).Carrier) {L : ℝ} {D0 : ℝ≥0∞}
    (hfoot : ∀ (p' : (H.stage i.castSucc).Carrier) (q : (H.stage i.succ).Carrier), HEq y q →
      (H.event i).RegularCrossing p' q →
      ∃ D : (H.event i).BufferedFootprintData_P6ST2 p' q ηout C1 C2 m k, ∀ᶠ n in atTop,
        ∀ (t : Icc (0 : ℝ) H.horizon) (z : (H.stageAt t).Carrier), (t : ℝ) = D.v n →
          HEq z p' →
          riemannianEDistOf (H.stageMetric (H.activeStage t) t) (seed t) z ≤
            D0 + ENNReal.ofReal (L / (4 * Real.sqrt (metricScalarAt
              (H.stageMetric (H.activeStage (H.stageTime i.succ)) (H.stageTime i.succ)) y))))
    (hsel : ¬ H.HasSpatialCanonicalTimeControl ηout C1out C2out Ctime (H.stageTime i.succ) y) :
    LeftLocalizedBadAt_CXST (fun t : Icc (0 : ℝ) H.horizon => (t : ℝ))
      (fun t z => ¬ ∃ W : SpatialCanonicalWitness (H.stageMetric (H.activeStage t) t) ηfine C1 C2 z,
        W.capTubeHasNeckChart ηfine ∧ W.HasMargins m)
      (fun t z => metricScalarAt (H.stageMetric (H.activeStage t) t) z)
      (fun t z => riemannianEDistOf (H.stageMetric (H.activeStage t) t) (seed t) z)
      (H.time i.succ)
      (metricScalarAt (H.stageMetric (H.activeStage (H.stageTime i.succ)) (H.stageTime i.succ)) y)
      L D0 := by
  have hP : H.stageAt (H.stageTime i.succ) = H.stage i.succ :=
    congrArg H.stage (H.activeStage_stageTime i.succ)
  obtain ⟨q, hq⟩ : ∃ q : (H.stage i.succ).Carrier, HEq y q :=
    ⟨cast (congrArg OrientedThreeStage.Carrier hP) y, (cast_heq _ _).symm⟩
  have hg : HEq (H.stageMetric (H.activeStage (H.stageTime i.succ)) (H.stageTime i.succ))
      (H.event i).outputMetric :=
    (ObservedHistory.stageMetric_heq_of_idx_P6S2 H (H.activeStage_stageTime i.succ) _).trans
      (heq_of_eq ((H.stageMetric_initial i.succ).trans (H.event_output i).symm))
  rcases R.postCover_P6S2 q with ⟨b, x, hbx⟩ | ⟨p', hcross⟩
  · exact (R.false_of_stage_cap_P6S2 hcapW b x (hq.trans (heq_of_eq hbx)) hsel).elim
  obtain ⟨D, hD⟩ := hfoot p' q hq hcross
  have hnot : ¬ ∃ W : SpatialCanonicalWitness (H.event i).outputMetric ηout C1out C2out q,
      W.capTubeHasNeckChart ηout := fun hW =>
    hsel ((ObservedHistory.hasSpatialCanonicalTimeControl_iff_of_boundary_P6S
      (Or.inl (H.boundary_of_stageTime_P6S i.succ))).mpr
        ((ObservedHistory.spatial_iff_heq_P6S2 hP hg hq).mpr hW))
  have hfreq := MetricCutCapEvent.frequently_not_fineMargin_P6ST2 D hle h1 h2 hnot
  have hRy := scalar_heq_P6ST2 hP hg hq
  intro δ hδ ε hε
  have hratio : ∀ᶠ n in atTop, |metricScalarAt ((H.event i).incoming.flow.base.metric (D.v n)) p' /
      metricScalarAt (H.event i).outputMetric q - 1| < ε := by
    filter_upwards [Metric.tendsto_nhds.mp D.ratio_tendsto_one ε hε] with n hn
    rwa [Real.dist_eq] at hn
  obtain ⟨n, hbad, hn1, hn2, hn3⟩ := (hfreq.and_eventually ((D.v_tendsto.eventually
    (lt_mem_nhds (sub_lt_self (H.time i.succ) hδ))).and (hratio.and hD))).exists
  have hIcc := H.mem_Icc_of_mem_slab_P6ST2 i (D.v_mem n)
  let t : Icc (0 : ℝ) H.horizon := ⟨D.v n, hIcc⟩
  have ht0 : H.time i.castSucc ≤ t := (D.v_mem n).1.le
  have ht1 : (t : ℝ) < H.time i.succ := (D.v_mem n).2
  have hPt : H.stageAt t = H.stage i.castSucc :=
    congrArg H.stage (H.activeStage_eq_castSucc_P6ST2 i t ht0 ht1)
  obtain ⟨z, hz⟩ : ∃ z : (H.stageAt t).Carrier, HEq z p' :=
    ⟨cast (congrArg OrientedThreeStage.Carrier hPt).symm p', cast_heq _ _⟩
  have hsc := scalar_heq_P6ST2 hPt (ObservedHistory.stageMetric_slab_heq_P6ST2 i ht0 ht1) hz
  refine ⟨t, z, hn1, ht1, fun hW => hbad ((ObservedHistory.fineMargin_slab_iff_P6ST2 i ht0 ht1
    hz).mp hW), ?_, hn3 t z rfl hz⟩
  change |metricScalarAt (H.stageMetric (H.activeStage t) t) z / _ - 1| < ε
  rw [hsc, hRy]
  exact hn2

end GeometricCutoffRecord

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
