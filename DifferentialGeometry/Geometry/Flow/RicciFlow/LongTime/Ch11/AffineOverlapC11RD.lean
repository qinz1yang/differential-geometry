import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.NativeCanonicalReceiverC11RD
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.History.EventTimeTranslation
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.SlabTimeTranslation

set_option autoImplicit false

/-!
# S-CH11-REPROVE-D (G5)：affine overlap（`AffineEventPrefix` 的 shift API）的显式 binder 重证

G4 的 `closed_of_native_slabs_C11RD` 还差 `hshift`：`J.restrict T` 在时刻 `t ≥ b` 的 stage / 度量与 native 尾
`Kplus` 在平移后的时刻 `tK` 相同。astra 用 `AffineEventPrefix`（`CutoffRecordConcatenation.lean:394`）的
`stageAt_shift_eq / sliceMetric_shift_heq`（`AffineHistoryParabolicBall.lean:165–195`）得到；这两个文件都
不在树内。`AffineEventPrefix` 本身只是**呈现等式**的打包：

* `count_eq : J.eventCount = offset + K.eventCount`；
* `time_eq : J.time (offset + j) = K.time j + c`；`stage_eq : J.stage (offset + j) = K.stage j`；
* `event_heq : J.coreEvent (offset + i) ≍ translate_retained_event (K.coreEvent i) c`。

这里把这四条（外加最后一个 slab 的度量 `hfinal`）作为**显式 binder**，在树内重证：

* `affine_overlap_C11RD`：一段 presentation `K → J`（平移 `c`）上，对 `tJ = t + c` 得 stage 相等与
  切片度量 `HEq`（`activeStage_shift_eq` + `stageAt_shift_eq` + `sliceMetric_shift_heq`）；
* `hshift_of_affine_C11RD`：两段 presentation 共享尾 `L`（`L → Kplus` 平移 `a`，`L → J` 平移 `b`）
  ⇒ G4 的 `hshift`（closed-seam proof 的前半，`PreparedOverlapExtension.lean:1146–1190`）；
* `closed_of_affine_slabs_C11RD`：`hshift_of_affine_C11RD` + G4 `closed_of_native_slabs_C11RD`，
  即 G2 / G3 的 `closed` 只依赖呈现等式与 native 的 canonical 估计。
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

private def affIdx_C11RD {K J : RetainedCoreHistory.{u}} {offset : ℕ}
    (hcount : J.eventCount = offset + K.eventCount) (j : Fin (K.eventCount + 1)) :
    Fin (J.eventCount + 1) :=
  ⟨offset + j.val, by have := j.isLt; omega⟩

private theorem affIdx_le_iff_C11RD {K J : RetainedCoreHistory.{u}} {offset : ℕ}
    (hcount : J.eventCount = offset + K.eventCount) {j k : Fin (K.eventCount + 1)} :
    affIdx_C11RD hcount j ≤ affIdx_C11RD hcount k ↔ j ≤ k := by
  change offset + j.val ≤ offset + k.val ↔ j.val ≤ k.val
  omega

private theorem retained_event_incoming_heq_C11RD
    {P Q P' Q' : OrientedThreeStage.{u}} {a s a' s' : ℝ}
    (hP : P = P') (hQ : Q = Q') (ha : a = a') (hs : s = s')
    {E : RetainedCoreEvent P Q a s} {E' : RetainedCoreEvent P' Q' a' s'}
    (hE : HEq E E') (t : ℝ) :
    HEq (E.incoming.flow.base.metric t) (E'.incoming.flow.base.metric t) := by
  cases hP
  cases hQ
  cases ha
  cases hs
  cases eq_of_heq hE
  exact HEq.rfl

/-- `c ≥ 0`（`AffineEventPrefix.shift_nonneg`）：`J` 的第 `offset` 个时刻非负，等于 `0 + c`。 -/
private theorem aff_shift_nonneg_C11RD {K J : RetainedCoreHistory.{u}} {c : ℝ} {offset : ℕ}
    (hcount : J.eventCount = offset + K.eventCount)
    (htime : ∀ j : Fin (K.eventCount + 1),
      J.toHistory.time (affIdx_C11RD hcount j) = K.toHistory.time j + c) :
    0 ≤ c := by
  have h := J.toHistory.time_nonneg (affIdx_C11RD hcount 0)
  rw [htime, K.toHistory.time_zero, zero_add] at h
  exact h

/-- `activeStage_shift_eq`：平移后的时刻的 active stage = 源 active stage 的平移。 -/
private theorem aff_activeStage_C11RD {K J : RetainedCoreHistory.{u}} {c : ℝ} {offset : ℕ}
    (hcount : J.eventCount = offset + K.eventCount)
    (htime : ∀ j : Fin (K.eventCount + 1),
      J.toHistory.time (affIdx_C11RD hcount j) = K.toHistory.time j + c)
    (t : Icc (0 : ℝ) K.horizon) (tJ : Icc (0 : ℝ) J.horizon) (htJ : (tJ : ℝ) = (t : ℝ) + c) :
    J.toHistory.activeStage tJ = affIdx_C11RD hcount (K.toHistory.activeStage t) := by
  apply J.toHistory.activeStage_eq_of_maximal
  · rw [htime, htJ]
    exact add_le_add (K.toHistory.activeStage_time_le t) (le_refl c)
  · intro j hj
    by_cases ho : j.val < offset
    · change j.val ≤ offset + (K.toHistory.activeStage t).val
      omega
    · have hc' : J.toHistory.eventCount = offset + K.eventCount := hcount
      let k : Fin (K.eventCount + 1) :=
        ⟨j.val - offset, by have := j.isLt; omega⟩
      have he : affIdx_C11RD hcount k = j := by
        apply Fin.ext
        change offset + (j.val - offset) = j.val
        omega
      have ht : K.toHistory.time k ≤ (t : ℝ) := by
        rw [← he, htime, htJ] at hj
        linarith
      rw [← he]
      exact (affIdx_le_iff_C11RD hcount).mpr (K.toHistory.le_activeStage t k ht)

/-- `stageMetric_shift_heq`：第 `j` 个 stage 的度量在平移后相同（最后一个 stage 用 `hfinal`，
其余用 `event_heq` 给出 incoming 度量的平移）。 -/
private theorem aff_stageMetric_C11RD {K J : RetainedCoreHistory.{u}} {c : ℝ} {offset : ℕ}
    (hcount : J.eventCount = offset + K.eventCount)
    (htime : ∀ j : Fin (K.eventCount + 1),
      J.toHistory.time (affIdx_C11RD hcount j) = K.toHistory.time j + c)
    (hstage : ∀ j : Fin (K.eventCount + 1), J.stage (affIdx_C11RD hcount j) = K.stage j)
    (hevent : ∀ i : Fin K.eventCount,
      HEq (J.coreEvent ⟨offset + i.val, by have := i.isLt; omega⟩)
        (GC.GeneralFlow.translate_retained_event (K.coreEvent i) c))
    (hfinal : ∀ t : ℝ,
      HEq (J.toHistory.stageMetric (Fin.last J.eventCount) (t + c))
        (K.toHistory.stageMetric (Fin.last K.eventCount) t))
    (j : Fin (K.eventCount + 1)) (t : ℝ) :
    HEq (J.toHistory.stageMetric (affIdx_C11RD hcount j) (t + c))
      (K.toHistory.stageMetric j t) := by
  cases j using Fin.lastCases with
  | last =>
    have hl : affIdx_C11RD hcount (Fin.last K.eventCount) = Fin.last J.eventCount := by
      apply Fin.ext
      change offset + K.eventCount = J.eventCount
      omega
    rw [hl]
    exact hfinal t
  | cast i =>
    have hc : affIdx_C11RD hcount i.castSucc =
        (⟨offset + i.val, by have := i.isLt; omega⟩ : Fin J.eventCount).castSucc := rfl
    rw [hc, ObservedHistory.stageMetric_castSucc_apply, ObservedHistory.stageMetric_castSucc_apply]
    have hs : affIdx_C11RD hcount i.succ =
        (⟨offset + i.val, by have := i.isLt; omega⟩ : Fin J.eventCount).succ := by
      apply Fin.ext
      change offset + (i.val + 1) = offset + i.val + 1
      omega
    have hmetric := retained_event_incoming_heq_C11RD
      (hstage i.castSucc) (by simpa only [hs] using hstage i.succ) (htime i.castSucc)
      (by simpa only [hs] using htime i.succ) (hevent i) (t + c)
    have key : HEq
        ((J.coreEvent ⟨offset + i.val, by have := i.isLt; omega⟩).incoming.flow.base.metric
          (t + c))
        ((K.coreEvent i).incoming.flow.base.metric t) := by
      have h2 := hmetric.trans
        (heq_of_eq ((K.coreEvent i).incoming.timeTranslate_metric c (t + c)))
      rwa [add_sub_cancel_right] at h2
    exact key

/-! ## 公共 shift API（显式 binder） -/

/-- `AffineEventPrefix` 的 `stageAt_shift_eq` + `sliceMetric_shift_heq` 的显式 binder 版：一段 affine
presentation `K → J`（平移 `c`，偏移 `offset`）上，`J` 在 `tJ = t + c` 的 stage 与切片度量与 `K` 在 `t`
的相同。 -/
theorem affine_overlap_C11RD {K J : RetainedCoreHistory.{u}} {c : ℝ} {offset : ℕ}
    (count : J.eventCount = offset + K.eventCount)
    (time : ∀ j : Fin (K.eventCount + 1),
      J.time ⟨offset + j.val, by omega⟩ = K.time j + c)
    (stage : ∀ j : Fin (K.eventCount + 1),
      J.stage ⟨offset + j.val, by omega⟩ = K.stage j)
    (event : ∀ i : Fin K.eventCount,
      HEq (J.coreEvent ⟨offset + i.val, by omega⟩)
        (GC.GeneralFlow.translate_retained_event (K.coreEvent i) c))
    (final : ∀ t : ℝ,
      HEq (J.toHistory.stageMetric (Fin.last J.eventCount) (t + c))
        (K.toHistory.stageMetric (Fin.last K.eventCount) t))
    (t : Icc (0 : ℝ) K.horizon) (tJ : Icc (0 : ℝ) J.horizon) (htJ : (tJ : ℝ) = (t : ℝ) + c) :
    J.toHistory.stageAt tJ = K.toHistory.stageAt t ∧
      HEq (J.toHistory.stageMetric (J.toHistory.activeStage tJ) tJ)
        (K.toHistory.stageMetric (K.toHistory.activeStage t) t) := by
  refine ⟨?_, ?_⟩
  · change J.stage (J.toHistory.activeStage tJ) = K.stage (K.toHistory.activeStage t)
    rw [aff_activeStage_C11RD count time t tJ htJ]
    exact stage _
  · rw [aff_activeStage_C11RD count time t tJ htJ, htJ]
    exact aff_stageMetric_C11RD count time stage event final _ _

/-- G4 的 `hshift`：两段 affine presentation 共享尾 `L`（`L → Kplus` 平移 `a`，`L → J` 平移 `b`），
则 `J.restrict T` 在 `t ≥ b` 的 stage / 度量与 `Kplus` 在 `tK = t - b + a` 的相同
（astra `PreparedOverlapExtension.lean:1146–1190`）。 -/
theorem hshift_of_affine_C11RD {L Kplus J : RetainedCoreHistory.{u}} {a b : ℝ} {oK oJ : ℕ}
    (countK : Kplus.eventCount = oK + L.eventCount)
    (timeK : ∀ j : Fin (L.eventCount + 1),
      Kplus.time ⟨oK + j.val, by omega⟩ = L.time j + a)
    (stageK : ∀ j : Fin (L.eventCount + 1),
      Kplus.stage ⟨oK + j.val, by omega⟩ = L.stage j)
    (eventK : ∀ i : Fin L.eventCount,
      HEq (Kplus.coreEvent ⟨oK + i.val, by omega⟩)
        (GC.GeneralFlow.translate_retained_event (L.coreEvent i) a))
    (finalK : ∀ t : ℝ,
      HEq (Kplus.toHistory.stageMetric (Fin.last Kplus.eventCount) (t + a))
        (L.toHistory.stageMetric (Fin.last L.eventCount) t))
    (countJ : J.eventCount = oJ + L.eventCount)
    (timeJ : ∀ j : Fin (L.eventCount + 1),
      J.time ⟨oJ + j.val, by omega⟩ = L.time j + b)
    (stageJ : ∀ j : Fin (L.eventCount + 1),
      J.stage ⟨oJ + j.val, by omega⟩ = L.stage j)
    (eventJ : ∀ i : Fin L.eventCount,
      HEq (J.coreEvent ⟨oJ + i.val, by omega⟩)
        (GC.GeneralFlow.translate_retained_event (L.coreEvent i) b))
    (finalJ : ∀ t : ℝ,
      HEq (J.toHistory.stageMetric (Fin.last J.eventCount) (t + b))
        (L.toHistory.stageMetric (Fin.last L.eventCount) t))
    (hKhor : Kplus.horizon = L.horizon + a) (hJhor : J.horizon = L.horizon + b) :
    ∀ T : Icc (0 : ℝ) J.horizon, (T : ℝ) < J.horizon →
      ∀ t : Icc (0 : ℝ) (J.restrict T).toHistory.horizon, b ≤ (t : ℝ) →
        ∃ tK : Icc (0 : ℝ) Kplus.horizon, (tK : ℝ) < Kplus.horizon ∧
          (J.restrict T).toHistory.stageAt t = Kplus.toHistory.stageAt tK ∧
          HEq ((J.restrict T).toHistory.stageMetric ((J.restrict T).toHistory.activeStage t) t)
            (Kplus.toHistory.stageMetric (Kplus.toHistory.activeStage tK) tK) := by
  intro T hT t hbt
  have ha : 0 ≤ a := aff_shift_nonneg_C11RD countK timeK
  have htT : (t : ℝ) ≤ (T : ℝ) := t.2.2
  have htJ : (t : ℝ) ≤ J.horizon := htT.trans T.2.2
  have htJ' : (t : ℝ) ≤ L.horizon + b := hJhor ▸ htJ
  let s : Icc (0 : ℝ) L.horizon := ⟨(t : ℝ) - b, sub_nonneg.mpr hbt, by linarith⟩
  let tJ : Icc (0 : ℝ) J.horizon := ⟨t, t.2.1, htJ⟩
  let tK : Icc (0 : ℝ) Kplus.horizon :=
    ⟨(t : ℝ) - b + a, by have := s.2.1; change 0 ≤ (t : ℝ) - b at this; linarith, by
      rw [hKhor]
      have := s.2.2
      change (t : ℝ) - b ≤ L.horizon at this
      linarith⟩
  have hJ := affine_overlap_C11RD countJ timeJ stageJ eventJ finalJ s tJ
    (by change (t : ℝ) = (t : ℝ) - b + b; ring)
  have hK := affine_overlap_C11RD countK timeK stageK eventK finalK s tK rfl
  refine ⟨tK, ?_, ?_, ?_⟩
  · have hlt : (t : ℝ) < J.horizon := htT.trans_lt hT
    have hlt' : (t : ℝ) < L.horizon + b := hJhor ▸ hlt
    change (t : ℝ) - b + a < Kplus.horizon
    rw [hKhor]
    linarith
  · exact (J.toHistory.restrict_stageAt T t).trans (hJ.1.trans hK.1.symm)
  · exact (J.toHistory.restrict_sliceMetric T t).trans (hJ.2.trans hK.2.symm)

/-- G2 / G3 的 `closed`（阈值 `Qall = max Qbirth Qzero`）只依赖两段 affine presentation 的呈现等式与 native
历史 `Kplus` 的 canonical 估计：`hshift_of_affine_C11RD` + G4 `closed_of_native_slabs_C11RD`。 -/
theorem closed_of_affine_slabs_C11RD {L Kplus J : RetainedCoreHistory.{u}} {a b : ℝ}
    {oK oJ : ℕ}
    (countK : Kplus.eventCount = oK + L.eventCount)
    (timeK : ∀ j : Fin (L.eventCount + 1),
      Kplus.time ⟨oK + j.val, by omega⟩ = L.time j + a)
    (stageK : ∀ j : Fin (L.eventCount + 1),
      Kplus.stage ⟨oK + j.val, by omega⟩ = L.stage j)
    (eventK : ∀ i : Fin L.eventCount,
      HEq (Kplus.coreEvent ⟨oK + i.val, by omega⟩)
        (GC.GeneralFlow.translate_retained_event (L.coreEvent i) a))
    (finalK : ∀ t : ℝ,
      HEq (Kplus.toHistory.stageMetric (Fin.last Kplus.eventCount) (t + a))
        (L.toHistory.stageMetric (Fin.last L.eventCount) t))
    (countJ : J.eventCount = oJ + L.eventCount)
    (timeJ : ∀ j : Fin (L.eventCount + 1),
      J.time ⟨oJ + j.val, by omega⟩ = L.time j + b)
    (stageJ : ∀ j : Fin (L.eventCount + 1),
      J.stage ⟨oJ + j.val, by omega⟩ = L.stage j)
    (eventJ : ∀ i : Fin L.eventCount,
      HEq (J.coreEvent ⟨oJ + i.val, by omega⟩)
        (GC.GeneralFlow.translate_retained_event (L.coreEvent i) b))
    (finalJ : ∀ t : ℝ,
      HEq (J.toHistory.stageMetric (Fin.last J.eventCount) (t + b))
        (L.toHistory.stageMetric (Fin.last L.eventCount) t))
    (hKhor : Kplus.horizon = L.horizon + a) (hJhor : J.horizon = L.horizon + b)
    {ε C1s C2s Cbirth Cgrad qs Qbirth Qzero Qall : ℝ} (hqs : qs ≤ Qbirth)
    (hQall : Qall = max Qbirth Qzero)
    (hzero : ∀ y : (Kplus.stage 0).Carrier, metricScalarAt (Kplus.initialMetric 0) y < Qzero)
    (hBirth : ∀ tK : Icc (0 : ℝ) Kplus.horizon, (tK : ℝ) < Kplus.horizon →
      Kplus.time (Kplus.toHistory.activeStage tK) = (tK : ℝ) →
      Kplus.toHistory.activeStage tK ≠ 0 →
      ∀ y : (Kplus.toHistory.stageAt tK).Carrier,
        Qbirth < metricScalarAt (Kplus.initialMetric (Kplus.toHistory.activeStage tK)) y →
        ∃ W : SpatialCanonicalWitness (Kplus.initialMetric (Kplus.toHistory.activeStage tK))
          ε Cbirth (max Cbirth Cgrad) y, W.capTubeHasNeckChart ε)
    (hev : ∀ j : Fin Kplus.eventCount,
      (Kplus.toHistory.event j).incoming.SpatiallyCanonicalBefore ε C1s C2s qs
        (Kplus.time j.succ))
    (hfin : ∀ hfinal : Kplus.time (Fin.last Kplus.eventCount) < Kplus.horizon,
      ((Kplus.finalSlab hfinal).restrictIncoming le_rfl hfinal le_rfl).SpatiallyCanonicalBefore
        ε C1s C2s qs Kplus.horizon) :
    ∀ T : Icc (0 : ℝ) J.horizon, (T : ℝ) < J.horizon →
      ∀ t : Icc (0 : ℝ) (J.restrict T).toHistory.horizon, b ≤ (t : ℝ) →
        ∀ x : ((J.restrict T).toHistory.stageAt t).Carrier,
          Qall < metricScalarAt
            ((J.restrict T).toHistory.stageMetric ((J.restrict T).toHistory.activeStage t) t) x →
          ∃ W : SpatialCanonicalWitness
            ((J.restrict T).toHistory.stageMetric ((J.restrict T).toHistory.activeStage t) t)
            ε (max C1s Cbirth) (max C2s (max Cbirth Cgrad)) x,
            W.capTubeHasNeckChart ε :=
  closed_of_native_slabs_C11RD J Kplus b hqs hQall hzero hBirth hev hfin
    (hshift_of_affine_C11RD countK timeK stageK eventK finalK countJ timeJ stageJ eventJ finalJ
      hKhor hJhor)

/-! ## Consumer：G2 一步的 `closed` 与 `hthr` 都由本车道（G4 + G5）给出 -/

/-- consumer：astra `PreparedSpatialStep` 的 `hcanonical`（`t < B` 上 canonical）的端到端树内版——
旧前缀 `H` 的 canonical（`hH`）+ 两段 affine presentation 的呈现等式 + native 历史 `Kplus` 的 canonical
估计（`hBirth / hev / hfin / hzero`）+ 半径的 antitone / 阈值，经 `canonical_step_C11RD`、
`closed_of_affine_slabs_C11RD`、`threshold_of_antitone_C11RD`。 -/
example {H L Kplus J : RetainedCoreHistory.{u}} {a b E B : ℝ} {oK oJ : ℕ}
    (countK : Kplus.eventCount = oK + L.eventCount)
    (timeK : ∀ j : Fin (L.eventCount + 1),
      Kplus.time ⟨oK + j.val, by omega⟩ = L.time j + a)
    (stageK : ∀ j : Fin (L.eventCount + 1),
      Kplus.stage ⟨oK + j.val, by omega⟩ = L.stage j)
    (eventK : ∀ i : Fin L.eventCount,
      HEq (Kplus.coreEvent ⟨oK + i.val, by omega⟩)
        (GC.GeneralFlow.translate_retained_event (L.coreEvent i) a))
    (finalK : ∀ t : ℝ,
      HEq (Kplus.toHistory.stageMetric (Fin.last Kplus.eventCount) (t + a))
        (L.toHistory.stageMetric (Fin.last L.eventCount) t))
    (countJ : J.eventCount = oJ + L.eventCount)
    (timeJ : ∀ j : Fin (L.eventCount + 1),
      J.time ⟨oJ + j.val, by omega⟩ = L.time j + b)
    (stageJ : ∀ j : Fin (L.eventCount + 1),
      J.stage ⟨oJ + j.val, by omega⟩ = L.stage j)
    (eventJ : ∀ i : Fin L.eventCount,
      HEq (J.coreEvent ⟨oJ + i.val, by omega⟩)
        (GC.GeneralFlow.translate_retained_event (L.coreEvent i) b))
    (finalJ : ∀ t : ℝ,
      HEq (J.toHistory.stageMetric (Fin.last J.eventCount) (t + b))
        (L.toHistory.stageMetric (Fin.last L.eventCount) t))
    (hKhor : Kplus.horizon = L.horizon + a) (hJhor : J.horizon = L.horizon + b)
    (hIJ : H.toHistory.IsPrefixOf J.toHistory) (ρH ρJ : ℝ → ℝ)
    {ε C1s C2s Cbirth Cgrad qs Qbirth Qzero r : ℝ}
    (hE : H.horizon = E) (hJB : J.horizon = B) (hE0 : 0 ≤ E) (hEB : E < B) (hbE : b ≤ E)
    (hρ : ∀ t : ℝ, t ≤ E → ρJ t = ρH t) (hanti : AntitoneOn ρJ (Ici 0))
    (hρpos : ∀ t : ℝ, 0 ≤ t → 0 < ρJ t) (hρE : ρJ E = r)
    (hQ : max Qbirth Qzero ≤ (r ^ 2)⁻¹) (hqs : qs ≤ Qbirth)
    (hzero : ∀ y : (Kplus.stage 0).Carrier, metricScalarAt (Kplus.initialMetric 0) y < Qzero)
    (hBirth : ∀ tK : Icc (0 : ℝ) Kplus.horizon, (tK : ℝ) < Kplus.horizon →
      Kplus.time (Kplus.toHistory.activeStage tK) = (tK : ℝ) →
      Kplus.toHistory.activeStage tK ≠ 0 →
      ∀ y : (Kplus.toHistory.stageAt tK).Carrier,
        Qbirth < metricScalarAt (Kplus.initialMetric (Kplus.toHistory.activeStage tK)) y →
        ∃ W : SpatialCanonicalWitness (Kplus.initialMetric (Kplus.toHistory.activeStage tK))
          ε Cbirth (max Cbirth Cgrad) y, W.capTubeHasNeckChart ε)
    (hev : ∀ j : Fin Kplus.eventCount,
      (Kplus.toHistory.event j).incoming.SpatiallyCanonicalBefore ε C1s C2s qs
        (Kplus.time j.succ))
    (hfin : ∀ hfinal : Kplus.time (Fin.last Kplus.eventCount) < Kplus.horizon,
      ((Kplus.finalSlab hfinal).restrictIncoming le_rfl hfinal le_rfl).SpatiallyCanonicalBefore
        ε C1s C2s qs Kplus.horizon)
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
    (closed_of_affine_slabs_C11RD countK timeK stageK eventK finalK countJ timeJ stageJ eventJ
      finalJ hKhor hJhor hqs rfl hzero hBirth hev hfin)

end GC.LongTime.Ch11
