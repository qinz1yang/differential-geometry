import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.HistoryCanonicalTransportC11RD
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.IncomingSlabCanonicalBounds
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.MasterFlowCompatibility
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TowerInductionStep

set_option autoImplicit false

/-!
# S-CH11-REPROVE-D (G4)：closed-seam receiver 的 birth / strict / stage-zero 分支

G2 / G3 里 S5 剩下的唯一物理输入是每步的 closed-seam receiver `closed`
（astra `PreparedOverlapExtension.lean:1131
exists_spatialCanonicalWitness_on_buffered_same_tail_observation_with_closed_seam`）。astra 证它时用
`AffineEventPrefix`（`CutoffRecordConcatenation`，SKIP，不在树内）把 `J.restrict T` 的时刻 `t` 平移到
native 尾 `Kplus` 的时刻 `tK`，再用 `NativeEstimates`（`PreparedObservationData`，闭包含 SKIP）
的 canonical 估计。这里把这两处依赖显式化后在树内重证其余部分：

* `canonical_strict_of_slabs_C11RD`：`NativeEstimates.exists_spatialCanonicalWitness_of_strict_birth`
  （`PreparedOverlapExtension.lean:24`）的重证，输入是 `NativeEstimates` 的两条
  `SpatiallyCanonicalBefore` 条款（树内 `IncomingSlab.SpatiallyCanonicalBefore`）；
* `canonical_native_overlap_C11RD`：单个 overlap 时刻 `(tA, tK)`（stage 相等 + 度量 `HEq`）上的
  三分支（stage-zero 出生：`Qzero` 矛盾；一般出生：`hBirth`；严格：`hStrict`），witness 常数用
  `enlargeConstants` 上调到 `(max C1s Cbirth, max C2s (max Cbirth Cgrad))`；
* `closed_of_native_overlap_C11RD`：对每个 `T < J.horizon`、`b ≤ t` 提供 native 时刻 `tK`
  （`hshift`，即 `AffineEventPrefix` 的 `stageAt_shift_eq / sliceMetric_shift_heq` 的结论）后，
  得到 G2 `canonical_step_C11RD` / G3 `historyCanonicalSupply_of_chain_C11RD` 要的 `closed`
  （阈值 `Q := max Qbirth Qzero`）。

**剩余输入**：`hshift`（affine overlap，astra `AffineEventPrefix`）与 native 的 canonical 估计
（`hev / hfin / hBirth / hzero`，astra `ClosedBirthPreparedClass.control` 的 `NativeEstimates` 与 birth
witness 条款）。
-/

noncomputable section

open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open Set
open scoped Manifold ContDiff

namespace GC.LongTime.Ch11

universe u

/-- `NativeEstimates.exists_spatialCanonicalWitness_of_strict_birth` 的树内重证：native 历史 `K`
的每个 event 的 incoming slab 与 final slab 有 `SpatiallyCanonicalBefore ε C1s C2s qs`，则在严格晚于
active stage 出生、严格早于 horizon 的时刻 `t`，标量曲率 `> qs` 的点有带 neck chart 的 witness。 -/
theorem canonical_strict_of_slabs_C11RD {K : RetainedCoreHistory.{u}} {ε C1s C2s qs : ℝ}
    (hev : ∀ j : Fin K.eventCount,
      (K.toHistory.event j).incoming.SpatiallyCanonicalBefore ε C1s C2s qs (K.time j.succ))
    (hfin : ∀ hfinal : K.time (Fin.last K.eventCount) < K.horizon,
      ((K.finalSlab hfinal).restrictIncoming le_rfl hfinal le_rfl).SpatiallyCanonicalBefore
        ε C1s C2s qs K.horizon)
    (t : Icc (0 : ℝ) K.horizon) (htop : (t : ℝ) < K.horizon)
    (hbirth : K.time (K.toHistory.activeStage t) < (t : ℝ)) :
    ∀ x : (K.toHistory.stageAt t).Carrier,
      qs < metricScalarAt (K.toHistory.stageMetric (K.toHistory.activeStage t) t) x →
      ∃ W : SpatialCanonicalWitness
        (K.toHistory.stageMetric (K.toHistory.activeStage t) t) ε C1s C2s x,
        W.capTubeHasNeckChart ε := by
  have hdom := K.toHistory.activeStage_mem t
  change ∀ x : (K.stage (K.toHistory.activeStage t)).Carrier, _
  generalize hj : K.toHistory.activeStage t = j at hbirth hdom ⊢
  cases j using Fin.lastCases with
  | last =>
    have hfinal : K.time (Fin.last K.eventCount) < K.horizon := hbirth.trans htop
    intro x hx
    rw [ObservedHistory.stageMetric_last_of_lt (h := hfinal)] at hx ⊢
    exact hfin hfinal x t ⟨hbirth, htop⟩ hx
  | cast i =>
    simp only [ObservedHistory.stageDomain, Fin.lastCases_castSucc, Set.mem_Ico] at hdom
    intro x hx
    rw [ObservedHistory.stageMetric_castSucc_apply] at hx ⊢
    exact hev i x t ⟨hbirth, hdom.2⟩ hx

/-- 单个 overlap 时刻上的三分支：目标历史 `A` 在 `tA` 与 native 历史 `K` 在 `tK` 的 stage / 度量相同，
`Qall = max Qbirth Qzero` 以上的点：stage-zero 出生与 `hzero`（`< Qzero`）矛盾；
出生时刻用 `hBirth`；严格晚于出生用 `hStrict`；witness 常数上调到
`(max C1s Cbirth, max C2s (max Cbirth Cgrad))`。 -/
theorem canonical_native_overlap_C11RD {A : ObservedHistory.{u}} {K : RetainedCoreHistory.{u}}
    {tA : Icc (0 : ℝ) A.horizon} {tK : Icc (0 : ℝ) K.horizon}
    (hstage : A.stageAt tA = K.toHistory.stageAt tK)
    (hmetric : HEq (A.stageMetric (A.activeStage tA) tA)
      (K.toHistory.stageMetric (K.toHistory.activeStage tK) tK))
    {ε C1s C2s Cbirth Cgrad qs Qbirth Qzero Qall : ℝ} (hqs : qs ≤ Qbirth)
    (hQall : Qall = max Qbirth Qzero)
    (hzero : ∀ y : (K.stage 0).Carrier, metricScalarAt (K.initialMetric 0) y < Qzero)
    (hBirth : K.time (K.toHistory.activeStage tK) = (tK : ℝ) → K.toHistory.activeStage tK ≠ 0 →
      ∀ y : (K.toHistory.stageAt tK).Carrier,
      Qbirth < metricScalarAt (K.initialMetric (K.toHistory.activeStage tK)) y →
      ∃ W : SpatialCanonicalWitness (K.initialMetric (K.toHistory.activeStage tK))
        ε Cbirth (max Cbirth Cgrad) y, W.capTubeHasNeckChart ε)
    (hStrict : K.time (K.toHistory.activeStage tK) < (tK : ℝ) →
      ∀ y : (K.toHistory.stageAt tK).Carrier,
      qs < metricScalarAt (K.toHistory.stageMetric (K.toHistory.activeStage tK) tK) y →
      ∃ W : SpatialCanonicalWitness
        (K.toHistory.stageMetric (K.toHistory.activeStage tK) tK) ε C1s C2s y,
        W.capTubeHasNeckChart ε) :
    ∀ x : (A.stageAt tA).Carrier,
      Qall < metricScalarAt (A.stageMetric (A.activeStage tA) tA) x →
      ∃ W : SpatialCanonicalWitness (A.stageMetric (A.activeStage tA) tA)
        ε (max C1s Cbirth) (max C2s (max Cbirth Cgrad)) x, W.capTubeHasNeckChart ε := by
  have hBirthAll : Qbirth ≤ Qall := by
    rw [hQall]
    exact le_max_left _ _
  have hZeroAll : Qzero ≤ Qall := by
    rw [hQall]
    exact le_max_right _ _
  refine canonical_of_overlap_C11RD hstage hmetric ?_
  intro xK hxK
  by_cases hbirth : K.time (K.toHistory.activeStage tK) = (tK : ℝ)
  · have hmetricBirth :
        K.toHistory.stageMetric (K.toHistory.activeStage tK) tK =
          K.initialMetric (K.toHistory.activeStage tK) := by
      rw [← hbirth]
      exact K.toHistory.stageMetric_initial _
    have hxBirth : Qall < metricScalarAt (K.initialMetric (K.toHistory.activeStage tK)) xK := by
      rw [← hmetricBirth]
      exact hxK
    by_cases hz : K.toHistory.activeStage tK = 0
    · have hzeroK : ∀ y : (K.stage (K.toHistory.activeStage tK)).Carrier,
          metricScalarAt (K.initialMetric (K.toHistory.activeStage tK)) y < Qzero := by
        have key : ∀ j : Fin (K.eventCount + 1), j = 0 →
            ∀ y : (K.stage j).Carrier, metricScalarAt (K.initialMetric j) y < Qzero := by
          rintro j rfl
          exact hzero
        exact key _ hz
      exact ((not_lt_of_ge (hZeroAll.trans hxBirth.le)) (hzeroK xK)).elim
    · obtain ⟨WK, hWK⟩ := hBirth hbirth hz xK (hBirthAll.trans_lt hxBirth)
      rw [hmetricBirth]
      exact ⟨WK.enlargeConstants (le_max_right _ _) (le_max_right _ _),
        hWK.enlarge_constants (le_max_right _ _) (le_max_right _ _)⟩
  · have hstrict : K.time (K.toHistory.activeStage tK) < (tK : ℝ) :=
      lt_of_le_of_ne (K.toHistory.activeStage_time_le tK) hbirth
    obtain ⟨WK, hWK⟩ := hStrict hstrict xK ((hqs.trans hBirthAll).trans_lt hxK)
    exact ⟨WK.enlargeConstants (le_max_left _ _) (le_max_left _ _),
      hWK.enlarge_constants (le_max_left _ _) (le_max_left _ _)⟩

/-- **closed receiver（native overlap 形）**：`J.restrict T` 的每个时刻 `t ≥ b` 对应 native 历史 `K` 的
一个 `tK < K.horizon`（`hshift`，astra `AffineEventPrefix` 的 `stageAt_shift_eq /
sliceMetric_shift_heq`），native 的 birth / strict witness（`hBirth / hStrict`，astra `NativeEstimates` 与
`ClosedBirthPreparedClass.control`）与 stage-zero 界 `hzero` ⇒ G2 的 `closed`（阈值
`Qall = max Qbirth Qzero`，常数 `(max C1s Cbirth, max C2s (max Cbirth Cgrad))`）。 -/
theorem closed_of_native_overlap_C11RD (J K : RetainedCoreHistory.{u}) (b : ℝ)
    {ε C1s C2s Cbirth Cgrad qs Qbirth Qzero Qall : ℝ} (hqs : qs ≤ Qbirth)
    (hQall : Qall = max Qbirth Qzero)
    (hzero : ∀ y : (K.stage 0).Carrier, metricScalarAt (K.initialMetric 0) y < Qzero)
    (hBirth : ∀ tK : Icc (0 : ℝ) K.horizon, (tK : ℝ) < K.horizon →
      K.time (K.toHistory.activeStage tK) = (tK : ℝ) → K.toHistory.activeStage tK ≠ 0 →
      ∀ y : (K.toHistory.stageAt tK).Carrier,
        Qbirth < metricScalarAt (K.initialMetric (K.toHistory.activeStage tK)) y →
        ∃ W : SpatialCanonicalWitness (K.initialMetric (K.toHistory.activeStage tK))
          ε Cbirth (max Cbirth Cgrad) y, W.capTubeHasNeckChart ε)
    (hStrict : ∀ tK : Icc (0 : ℝ) K.horizon, (tK : ℝ) < K.horizon →
      K.time (K.toHistory.activeStage tK) < (tK : ℝ) →
      ∀ y : (K.toHistory.stageAt tK).Carrier,
        qs < metricScalarAt (K.toHistory.stageMetric (K.toHistory.activeStage tK) tK) y →
        ∃ W : SpatialCanonicalWitness
          (K.toHistory.stageMetric (K.toHistory.activeStage tK) tK) ε C1s C2s y,
          W.capTubeHasNeckChart ε)
    (hshift : ∀ T : Icc (0 : ℝ) J.horizon, (T : ℝ) < J.horizon →
      ∀ t : Icc (0 : ℝ) (J.restrict T).toHistory.horizon, b ≤ (t : ℝ) →
        ∃ tK : Icc (0 : ℝ) K.horizon, (tK : ℝ) < K.horizon ∧
          (J.restrict T).toHistory.stageAt t = K.toHistory.stageAt tK ∧
          HEq ((J.restrict T).toHistory.stageMetric ((J.restrict T).toHistory.activeStage t) t)
            (K.toHistory.stageMetric (K.toHistory.activeStage tK) tK)) :
    ∀ T : Icc (0 : ℝ) J.horizon, (T : ℝ) < J.horizon →
      ∀ t : Icc (0 : ℝ) (J.restrict T).toHistory.horizon, b ≤ (t : ℝ) →
        ∀ x : ((J.restrict T).toHistory.stageAt t).Carrier,
          Qall < metricScalarAt
            ((J.restrict T).toHistory.stageMetric ((J.restrict T).toHistory.activeStage t) t) x →
          ∃ W : SpatialCanonicalWitness
            ((J.restrict T).toHistory.stageMetric ((J.restrict T).toHistory.activeStage t) t)
            ε (max C1s Cbirth) (max C2s (max Cbirth Cgrad)) x,
            W.capTubeHasNeckChart ε := by
  intro T hT t hbt
  obtain ⟨tK, htop, hstage, hmetric⟩ := hshift T hT t hbt
  exact canonical_native_overlap_C11RD hstage hmetric hqs hQall hzero (hBirth tK htop)
    (hStrict tK htop)

/-- 同上，但 strict 分支的 `hStrict` 换成 native 历史的两条 `SpatiallyCanonicalBefore` 条款
（astra `NativeEstimates` 的 spatial 部分）：最终输入 = `hev / hfin / hBirth / hzero / hshift`。 -/
theorem closed_of_native_slabs_C11RD (J K : RetainedCoreHistory.{u}) (b : ℝ)
    {ε C1s C2s Cbirth Cgrad qs Qbirth Qzero Qall : ℝ} (hqs : qs ≤ Qbirth)
    (hQall : Qall = max Qbirth Qzero)
    (hzero : ∀ y : (K.stage 0).Carrier, metricScalarAt (K.initialMetric 0) y < Qzero)
    (hBirth : ∀ tK : Icc (0 : ℝ) K.horizon, (tK : ℝ) < K.horizon →
      K.time (K.toHistory.activeStage tK) = (tK : ℝ) → K.toHistory.activeStage tK ≠ 0 →
      ∀ y : (K.toHistory.stageAt tK).Carrier,
        Qbirth < metricScalarAt (K.initialMetric (K.toHistory.activeStage tK)) y →
        ∃ W : SpatialCanonicalWitness (K.initialMetric (K.toHistory.activeStage tK))
          ε Cbirth (max Cbirth Cgrad) y, W.capTubeHasNeckChart ε)
    (hev : ∀ j : Fin K.eventCount,
      (K.toHistory.event j).incoming.SpatiallyCanonicalBefore ε C1s C2s qs (K.time j.succ))
    (hfin : ∀ hfinal : K.time (Fin.last K.eventCount) < K.horizon,
      ((K.finalSlab hfinal).restrictIncoming le_rfl hfinal le_rfl).SpatiallyCanonicalBefore
        ε C1s C2s qs K.horizon)
    (hshift : ∀ T : Icc (0 : ℝ) J.horizon, (T : ℝ) < J.horizon →
      ∀ t : Icc (0 : ℝ) (J.restrict T).toHistory.horizon, b ≤ (t : ℝ) →
        ∃ tK : Icc (0 : ℝ) K.horizon, (tK : ℝ) < K.horizon ∧
          (J.restrict T).toHistory.stageAt t = K.toHistory.stageAt tK ∧
          HEq ((J.restrict T).toHistory.stageMetric ((J.restrict T).toHistory.activeStage t) t)
            (K.toHistory.stageMetric (K.toHistory.activeStage tK) tK)) :
    ∀ T : Icc (0 : ℝ) J.horizon, (T : ℝ) < J.horizon →
      ∀ t : Icc (0 : ℝ) (J.restrict T).toHistory.horizon, b ≤ (t : ℝ) →
        ∀ x : ((J.restrict T).toHistory.stageAt t).Carrier,
          Qall < metricScalarAt
            ((J.restrict T).toHistory.stageMetric ((J.restrict T).toHistory.activeStage t) t) x →
          ∃ W : SpatialCanonicalWitness
            ((J.restrict T).toHistory.stageMetric ((J.restrict T).toHistory.activeStage t) t)
            ε (max C1s Cbirth) (max C2s (max Cbirth Cgrad)) x,
            W.capTubeHasNeckChart ε :=
  closed_of_native_overlap_C11RD J K b hqs hQall hzero hBirth
    (fun tK htop hbirth => canonical_strict_of_slabs_C11RD hev hfin tK htop hbirth) hshift

/-- step 的阈值（astra `PreparedSpatialStep.lean` 的 `hthreshold`）：`Q ≤ r⁻²`（`threshold_le`）、
`ρ` 在 `[0, ∞)` 上 antitone、`ρ > 0` 且 `ρ E = r`（`radius_after`）⇒ `E ≤ t` 时 `Q ≤ (ρ t)⁻²`，
即 G2 / G3 的 `hthr`。 -/
theorem threshold_of_antitone_C11RD {ρ : ℝ → ℝ} {Q r E : ℝ} (hE : 0 ≤ E)
    (hanti : AntitoneOn ρ (Ici 0)) (hρpos : ∀ t : ℝ, 0 ≤ t → 0 < ρ t) (hρE : ρ E = r)
    (hQ : Q ≤ (r ^ 2)⁻¹) : ∀ t : ℝ, E ≤ t → Q ≤ (ρ t ^ 2)⁻¹ := by
  intro t ht
  have h0 : 0 ≤ t := hE.trans ht
  have hle : ρ t ≤ r := hρE ▸ hanti (mem_Ici.2 hE) (mem_Ici.2 h0) ht
  exact hQ.trans (inv_anti₀ (pow_pos (hρpos t h0) 2) (pow_le_pow_left₀ (hρpos t h0).le hle 2))

/-! ## Consumer -/

/-- consumer：G2 的一步 `canonical_step_C11RD` 的 `closed` 由 native 数据给出
（`closed_of_native_slabs_C11RD`），`hthr` 由 `threshold_of_antitone_C11RD` 给出（阈值
`Q := max Qbirth Qzero`）；剩下的输入 = 旧前缀的 canonical + native 估计 + `hshift`。 -/
example {H J K : RetainedCoreHistory.{u}} (hIJ : H.toHistory.IsPrefixOf J.toHistory)
    (ρH ρJ : ℝ → ℝ) (E B b : ℝ)
    {ε C1s C2s Cbirth Cgrad qs Qbirth Qzero : ℝ} (hE : H.horizon = E) (hJB : J.horizon = B)
    (hE0 : 0 ≤ E) (hEB : E < B) (hbE : b ≤ E) (hρ : ∀ t : ℝ, t ≤ E → ρJ t = ρH t)
    {r : ℝ} (hanti : AntitoneOn ρJ (Ici 0)) (hρpos : ∀ t : ℝ, 0 ≤ t → 0 < ρJ t)
    (hρE : ρJ E = r) (hQ : max Qbirth Qzero ≤ (r ^ 2)⁻¹) (hqs : qs ≤ Qbirth)
    (hzero : ∀ y : (K.stage 0).Carrier, metricScalarAt (K.initialMetric 0) y < Qzero)
    (hBirth : ∀ tK : Icc (0 : ℝ) K.horizon, (tK : ℝ) < K.horizon →
      K.time (K.toHistory.activeStage tK) = (tK : ℝ) → K.toHistory.activeStage tK ≠ 0 →
      ∀ y : (K.toHistory.stageAt tK).Carrier,
        Qbirth < metricScalarAt (K.initialMetric (K.toHistory.activeStage tK)) y →
        ∃ W : SpatialCanonicalWitness (K.initialMetric (K.toHistory.activeStage tK))
          ε Cbirth (max Cbirth Cgrad) y, W.capTubeHasNeckChart ε)
    (hev : ∀ j : Fin K.eventCount,
      (K.toHistory.event j).incoming.SpatiallyCanonicalBefore ε C1s C2s qs (K.time j.succ))
    (hfin : ∀ hfinal : K.time (Fin.last K.eventCount) < K.horizon,
      ((K.finalSlab hfinal).restrictIncoming le_rfl hfinal le_rfl).SpatiallyCanonicalBefore
        ε C1s C2s qs K.horizon)
    (hshift : ∀ T : Icc (0 : ℝ) J.horizon, (T : ℝ) < J.horizon →
      ∀ t : Icc (0 : ℝ) (J.restrict T).toHistory.horizon, b ≤ (t : ℝ) →
        ∃ tK : Icc (0 : ℝ) K.horizon, (tK : ℝ) < K.horizon ∧
          (J.restrict T).toHistory.stageAt t = K.toHistory.stageAt tK ∧
          HEq ((J.restrict T).toHistory.stageMetric ((J.restrict T).toHistory.activeStage t) t)
            (K.toHistory.stageMetric (K.toHistory.activeStage tK) tK))
    (hH : ∀ t : Icc (0 : ℝ) H.toHistory.horizon, (t : ℝ) < E →
      ∀ x : (H.toHistory.stageAt t).Carrier,
        (ρH t ^ 2)⁻¹ < metricScalarAt (H.toHistory.stageMetric (H.toHistory.activeStage t) t) x →
        ∃ W : SpatialCanonicalWitness
          (H.toHistory.stageMetric (H.toHistory.activeStage t) t)
          ε (max C1s Cbirth) (max C2s (max Cbirth Cgrad)) x,
          W.capTubeHasNeckChart ε) :
    ∀ t : Icc (0 : ℝ) J.toHistory.horizon, (t : ℝ) < B →
      ∀ x : (J.toHistory.stageAt t).Carrier,
        (ρJ t ^ 2)⁻¹ < metricScalarAt (J.toHistory.stageMetric (J.toHistory.activeStage t) t) x →
        ∃ W : SpatialCanonicalWitness
          (J.toHistory.stageMetric (J.toHistory.activeStage t) t)
          ε (max C1s Cbirth) (max C2s (max Cbirth Cgrad)) x,
          W.capTubeHasNeckChart ε :=
  canonical_step_C11RD hIJ ρH ρJ E B (max Qbirth Qzero) b hE hJB hE0 hEB hbE hρ
    (fun t ht _ => threshold_of_antitone_C11RD hE0 hanti hρpos hρE hQ t ht) hH
    (closed_of_native_slabs_C11RD J K b hqs rfl hzero hBirth hev hfin hshift)

end GC.LongTime.Ch11
