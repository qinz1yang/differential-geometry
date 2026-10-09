import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.LGeometry.Action.PhysicalWeightedStageAttainment
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.LGeometry.Action.ClosedEventWeightedMinimum
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.LGeometry.Action.DistinctPoleWeightedTemporalSupport
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.ParabolicSeedVolume

/-!
# S-CH11-FIX9 port of astra `HalfClockActionEndpoint`（`PortC11P`）

来源：donor `HalfClockActionEndpoint.lean`（Jui-Hui `chapter11-astra` @ `a73e4bdbfd`）。
donor 文本在本树 elaboration 失败。本 port 只有 elaboration 层面修补（no statement / definition /
proof idea altered；不加 `set_option`）：
* `hMstage`：`simp only [Mweight, tracedPhysicalWeightedMinimum, dite_eq_left hseedHalf]` 之后剩
  `sInf (range … (H.activeStage ⟨↑t - b ^ 2, _⟩) …) = sInf (range … first …)`（`first` 是 let）
  → 补 `rfl`；
* `hl` / `hevent` / `hendclock` 的 `simpa only [hi] using …`（`hi : first = i.succ`，`first` 是 let，
  simp 不展开）→ `rw [← hi]; exact …`；
* `hev`：`(Ioi_mem_nhds hb).and …` 的 `Ioi 0 ∈ 𝓝 b` 不能用 `.and` 的点记号 → 先 `have h0 : ∀ᶠ w in 𝓝 b,
  0 < w := Ioi_mem_nhds hb` 再 `h0.and …`。
* `hexponent` 的 `field_simp [hr.ne', hsqrt.ne'] <;> ring`：`field_simp` 已关掉目标，`ring` 永不执行 →
  删去；`hcut` 的 `field_simp [hr.ne'] <;> ring`（`<;>` 触发 unnecessarySeqFocus）→ 换行 `ring`。

原路径 `HalfClockActionEndpoint` 是只 import 本文件的 re-export shim。
-/

set_option autoImplicit false
noncomputable section

open Set Filter
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped Manifold ContDiff ENNReal Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory
universe u

theorem exists_half_clock_action_endpoint_and_seed_volume_of_traced_bound
    (H : ObservedHistory.{u}) (parameters : CutoffParameters)
    (records : ∀ i : Fin H.eventCount, GeometricCutoffRecord H i parameters)
    (a₀ : ℝ) (ha₀ : 0 < a₀)
    (hfixed : ∀ y, InFixedHamiltonIveyRegion (H.initialMetric 0) a₀ y)
    (hscalar : ∀ y, -3 / a₀ ≤ metricScalarAt (H.initialMetric 0) y)
    (t : Icc (0 : ℝ) H.horizon) (p x : (H.stageAt t).Carrier)
    (r A : ℝ) (hA : 0 < A) (hT : 2 * r ^ 2 < t.val)
    (hseed : GC.LongTime.hasSmallParabolicCurvature H t p r)
    (hvolume : ENNReal.ofReal (A⁻¹ * r ^ 3) ≤
      DifferentialGeometry.Geometry.Collapse.ballVolume (H.stageMetric (H.activeStage t) t) p r)
    (aSeed : Icc (0 : ℝ) H.horizon) (hSeedTime : aSeed ≤ t)
    (hSeedClock : (aSeed : ℝ) = t.val - r ^ 2)
    (seedTrace : BackwardPointTrace H (H.activeStage aSeed) (H.activeStage t)
      (H.activeStage_mono hSeedTime) p)
    (hbound : ∀ w ∈ Ioc (0 : ℝ) (r / Real.sqrt 2),
      H.tracedPhysicalWeightedMinimum aSeed t hSeedTime p x seedTrace (3 / a₀) r A w ≤
        ((2 * r * w * Real.exp
          (DifferentialGeometry.Analysis.SingularBarrier.bound
            (2 * A + 160 * DifferentialGeometry.Analysis.CutoffProfile.derivBound ^ 2 +
              3 / 40) * w ^ 2 / r ^ 2 + 32 * w / r) : ℝ) : WithTop ℝ)) :
    let Cweight := DifferentialGeometry.Analysis.SingularBarrier.bound
      (2 * A + 160 * DifferentialGeometry.Analysis.CutoffProfile.derivBound ^ 2 + 3 / 40)
    let D := Real.exp (Cweight / 2 + 32 / Real.sqrt 2) + 1
    let b := r / Real.sqrt 2
    ∃ (a : Icc (0 : ℝ) H.horizon) (has : aSeed ≤ a) (hat : a ≤ t),
      (a : ℝ) = t.val - r ^ 2 / 2 ∧
      let first := H.activeStage a
      let last := H.activeStage t
      let hle := H.activeStage_mono hat
      let O := seedTrace.point first (H.activeStage_mono has) hle
      let Mweight := H.tracedPhysicalWeightedMinimum aSeed t hSeedTime p x seedTrace
        (3 / a₀) r A
      ∃ (q : (H.stage first).Carrier) (L action : ℝ),
        Mweight b = H.physicalWeightedCost first last hle t.val (3 / a₀) r A b x O q ∧
        H.regularizedCost first last hle t.val (3 / a₀) 0 b x q = (L : WithTop ℝ) ∧
        L ≤ (D - 1) * r ∧
        riemannianEDistOf (H.stageMetric first a) O q < ENNReal.ofReal (r / 10) ∧
        (action : WithTop ℝ) ∈ H.regularizedActionValues first last hle
          t.val (3 / a₀) 0 b x q ∧
        action < D * r ∧
        0 < A⁻¹ * Real.exp (-57) / 512 ∧
        ∀ s : ℝ, 0 < s → s ≤ r / 2 →
          ENNReal.ofReal ((A⁻¹ * Real.exp (-57) / 512) * s ^ 3) ≤
            DifferentialGeometry.Geometry.Collapse.ballVolume (H.stageMetric first a) O s := by
  classical
  intro Cweight D b
  have hr : 0 < r := hseed.1
  have hsqrt : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hb : 0 < b := div_pos hr hsqrt
  have hr2 : 0 < r ^ 2 := sq_pos_of_pos hr
  have hb2 : b ^ 2 = r ^ 2 / 2 := by
    dsimp only [b]
    rw [div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  have hbr : b < r := by nlinarith only [hb2, hr2, hr, hb]
  have h4b : 4 * b ^ 2 < t.val := by nlinarith only [hb2, hT]
  have ha0 : 0 < t.val - b ^ 2 := by nlinarith only [hb2, hT, hr2]
  let a : Icc (0 : ℝ) H.horizon := ⟨t.val - b ^ 2,
    ha0.le, (sub_le_self t.val (sq_nonneg b)).trans t.property.2⟩
  have has : aSeed ≤ a := by
    change (aSeed : ℝ) ≤ t.val - b ^ 2
    rw [hSeedClock]
    nlinarith only [hb2, hr2]
  have hat : a ≤ t := sub_le_self t.val (sq_nonneg b)
  have halt : a.val < t.val := sub_lt_self t.val (sq_pos_of_pos hb)
  refine ⟨a, has, hat, ?_, ?_⟩
  · change t.val - b ^ 2 = t.val - r ^ 2 / 2
    rw [hb2]
  intro first last hle O Mweight
  let upper : ℝ → ℝ := fun w =>
    2 * r * w * Real.exp (Cweight * w ^ 2 / r ^ 2 + 32 * w / r)
  have hexponent : Cweight * b ^ 2 / r ^ 2 + 32 * b / r =
      Cweight / 2 + 32 / Real.sqrt 2 := by
    rw [hb2]
    dsimp only [b]
    field_simp [hr.ne', hsqrt.ne']
  have hupperb : upper b = 2 * r * b * (D - 1) := by
    dsimp only [upper, D]
    rw [hexponent]
    ring
  have hbudget : upper b ≤ 2 * r * b * D := by
    rw [hupperb]
    have hpositive : 0 < 2 * r * b := by positivity
    nlinarith only [hpositive]
  have hboundb : Mweight b ≤ ((upper b : ℝ) : WithTop ℝ) :=
    hbound b ⟨hb, le_rfl⟩
  have hMstage : Mweight b = sInf (Set.range
      (H.physicalWeightedCost first last hle t.val (3 / a₀) r A b x O)) := by
    have hseedHalf : (aSeed : ℝ) ≤ t.val - b ^ 2 := has
    simp only [Mweight, tracedPhysicalWeightedMinimum, dite_eq_left hseedHalf]
    rfl
  have hmem : a.val ∈ H.stageDomain first := H.activeStage_mem a
  have hend : a.val < H.stageEndTime first := by
    generalize first = j at hmem ⊢
    cases j using Fin.lastCases with
    | last =>
      rw [H.stageEndTime_last]
      exact halt.trans_le t.property.2
    | cast i =>
      simp only [stageDomain, Fin.lastCases_castSucc, mem_Ico] at hmem
      simpa only [H.stageEndTime_castSucc] using hmem.2
  have hmin : ∃ q : (H.stage first).Carrier,
      Mweight b = H.physicalWeightedCost first last hle t.val (3 / a₀) r A b x O q := by
    by_cases hstrict : H.time first < a.val
    · have hclock (w : ℝ) (hw : w ∈ Icc b b) :
          t.val - w ^ 2 ∈ Ioo (H.time first) (H.stageEndTime first) := by
        have hw' : w = b := le_antisymm hw.2 hw.1
        subst w
        exact ⟨hstrict, hend⟩
      obtain ⟨q, hq, _⟩ := H.physicalWeightedCost_minima_on_half_clock_of_cutoff_records
        parameters records ha₀ hfixed hscalar first last hle t.val r A b b hr hb le_rfl
        hb2.le hT (H.activeStage_mem t) hclock x O b ⟨le_rfl, le_rfl⟩
      exact ⟨q, hMstage.trans hq⟩
    · have hstart : H.time first = a.val :=
        le_antisymm (H.activeStage_time_le a) (le_of_not_gt hstrict)
      have hfirst0 : first ≠ 0 := by
        intro hz
        have hztime : H.time first = 0 := by rw [hz, H.time_zero]
        have hapos : 0 < a.val := ha0
        linarith only [hstart, hztime, hapos]
      obtain ⟨i, hi⟩ := Fin.eq_succ_of_ne_zero hfirst0
      have hl : i.succ ≤ H.activeStage t := by
        rw [← hi]
        exact hle
      have hevent : t.val - b ^ 2 = H.time i.succ := by
        rw [← hi]
        exact hstart.symm
      have hendclock : t.val - b ^ 2 < H.stageEndTime i.succ := by
        rw [← hi]
        exact hend
      have hclockContinuous : ContinuousAt (fun w : ℝ => t.val - w ^ 2) b := by
        fun_prop
      have h0 : ∀ᶠ w in 𝓝 b, 0 < w := Ioi_mem_nhds hb
      have hev : ∀ᶠ w in 𝓝 b, 0 < w ∧ t.val - w ^ 2 < H.stageEndTime i.succ :=
        h0.and (hclockContinuous.eventually (Iio_mem_nhds hendclock))
      have hevleft : ∀ᶠ w in 𝓝[<] b,
          (0 < w ∧ t.val - w ^ 2 < H.stageEndTime i.succ) ∧ w < b :=
        (hev.filter_mono nhdsWithin_le_nhds).and self_mem_nhdsWithin
      obtain ⟨c, ⟨hc, hentry⟩, hcb⟩ := hevleft.exists
      have hupper : ContinuousAt upper b := by dsimp only [upper]; fun_prop
      have hpreceding (w : ℝ) (hw : w ∈ Ico c b) :
          H.tracedPhysicalWeightedMinimum aSeed t hSeedTime p x seedTrace (3 / a₀) r A w ≤
            ((upper w : ℝ) : WithTop ℝ) :=
        hbound w ⟨hc.trans_le hw.1, hw.2.le⟩
      obtain ⟨hfSeed, qi, _Li, m, hMk, hWm, _⟩ :=
        H.exists_closed_event_traced_weighted_minimum_of_preceding_stage_bound
          parameters records a₀ ha₀ hfixed hscalar t p x r A D c b hr hc hcb hb2.le hT
          aSeed hSeedTime hSeedClock seedTrace i hl hevent hentry upper hupper hbudget
          hpreceding
      have htransport (j : Fin (H.eventCount + 1))
          (hjs : H.activeStage aSeed ≤ j) (hjl : j ≤ last) (hj : j = first)
          (qj : (H.stage j).Carrier)
          (hq : Mweight b = H.physicalWeightedCost j last hjl t.val (3 / a₀) r A b x
            (seedTrace.point j hjs hjl) qj) :
          ∃ q : (H.stage first).Carrier,
            Mweight b = H.physicalWeightedCost first last hle t.val (3 / a₀) r A b x O q := by
        subst j
        exact ⟨qj, hq⟩
      exact htransport i.succ hfSeed hl hi.symm qi (hMk.trans hWm.symm)
  obtain ⟨q, hq⟩ := hmin
  have hbootstrap : H.physicalWeightedCost first last hle t.val (3 / a₀) r A b x O q ≤
      ((2 * r * b * D : ℝ) : WithTop ℝ) :=
    hq.symm.trans_le (hboundb.trans (WithTop.coe_le_coe.mpr hbudget))
  have hlow := H.regularizedCost_ge_neg_clock_of_recent records ha₀ hfixed hscalar
    first last hle t.val b hb h4b x q
  have hshifted (L : ℝ)
      (hL : H.regularizedCost first last hle t.val (3 / a₀) 0 b x q = (L : WithTop ℝ)) :
      0 < L + r := by
    have hLb : -b ≤ L := WithTop.coe_le_coe.mp (hlow.trans_eq hL)
    linarith only [hLb, hbr]
  obtain ⟨hinside, L, hL, hLbound, hLstrict⟩ :=
    H.regularizedCost_lt_action_budget_of_weighted_bootstrap first last hle
      t.val (3 / a₀) r A b D x O q hr hb hshifted hbootstrap
  have hcut : r * (A * (1 - 2 * b ^ 2 / r ^ 2) + 1 / 10) = r / 10 := by
    rw [hb2]
    field_simp [hr.ne']
    ring
  have hnear : riemannianEDistOf (H.stageMetric first a) O q < ENNReal.ofReal (r / 10) := by
    change riemannianEDistOf (H.stageMetric first (t.val - b ^ 2)) O q < _
    rwa [hcut] at hinside
  have hInf : sInf (H.regularizedActionValues first last hle t.val (3 / a₀) 0 b x q) <
      ((D * r : ℝ) : WithTop ℝ) := hLstrict
  obtain ⟨V, hV, hVlt⟩ : ∃ V ∈ H.regularizedActionValues first last hle
      t.val (3 / a₀) 0 b x q, V < ((D * r : ℝ) : WithTop ℝ) := by
    rcases (H.regularizedActionValues first last hle t.val (3 / a₀) 0 b x q).eq_empty_or_nonempty with
      hempty | hnonempty
    · rw [hempty, WithTop.sInf_empty] at hInf
      exact absurd hInf not_top_lt
    · exact exists_lt_of_csInf_lt hnonempty hInf
  obtain ⟨action, haction⟩ := WithTop.ne_top_iff_exists.mp (ne_top_of_lt hVlt)
  have hactionMem : (action : WithTop ℝ) ∈ H.regularizedActionValues first last hle
      t.val (3 / a₀) 0 b x q := by rw [haction]; exact hV
  have hactionLt : action < D * r :=
    WithTop.coe_lt_coe.mp (haction.trans_lt hVlt)
  have hcoefficient : 0 < A⁻¹ * Real.exp (-57) / 512 := by positivity
  have hy : p ∈ riemannianBallOf (H.stageMetric (H.activeStage t) t) p (r / 4) := by
    change riemannianEDistOf _ p p < ENNReal.ofReal (r / 4)
    rw [riemannianEDistOf_self]
    exact ENNReal.ofReal_pos.mpr (by positivity)
  have hv : t.val - r ^ 2 ≤ a.val := by rw [← hSeedClock]; exact has
  have htraceVolume := (GC.LongTime.hasSmallParabolicCurvature.volume_lower_along_nearby_trace
    hseed hvolume hy a hat hv).2
    (seedTrace.restrictFirst (H.activeStage_mono has) hle)
  refine ⟨q, L, action, hq, hL, hLbound, hnear, hactionMem, hactionLt, hcoefficient, ?_⟩
  exact htraceVolume

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory
