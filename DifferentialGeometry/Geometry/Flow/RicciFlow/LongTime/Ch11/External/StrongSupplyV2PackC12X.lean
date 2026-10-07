import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.EnhancedSuppliesFromAstraC11P2
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.External.StrongNeckFullC12X
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistorySurvivorAction
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.StrongNeckPullbackTransport

set_option autoImplicit false

/-!
# O-C12X-S16C (G1)：survivor-domain 侧打包（Full strong neck ⇒ hStrong v2 的 neck 分支体）

设计 `docs/geometrization/chapter8/out/CH12X-S16-design.md` §2 "晚期 slice 打包"：从最后 stage
上 `y` 处的 `HistoryStrongNeckFull_C12X`（O-C12X-S16B G2a）出发，取
* `U := backwardSurvivorDomain first last`；
* `a := t − R⁻¹`（Full 的时间子句给 `time first ≤ a`，故 `first ≤ activeStage a`）；
* `E`：`regularOpenBackwardTrace_iff_le_survivorDomain_C11P2` + `backwardSurvivorDomain_mono_first`
  （`regularOpenBackwardTrace_survivorDomain_C12X`）；
* `S := gflow` 换到闭窗口 `[t − R⁻¹, t]`（`isSolutionOn_timeRestrict`、`StrongNeck.ofMetricEq`）；
* 窗口子句：event stage 上 slab 子句 + `backwardSurvivorSlabMetric_before`，最后 stage 上 current
  子句 + `localPullMetric_subtype_val`；trace map 与 survivor map 由
  `backwardSurvivorMap_comp_inclusion_first` 对齐（`atStage_eq_backwardSurvivorMap_C12X`）。

主结论 `strongNeckV2Branch_of_full_C12X` 的结论 = `StrongCanonicalSupplyV2_C11E` neck 分支的体
（`H := s.history`，`t := s.time`）。
-/

noncomputable section

open DifferentialGeometry DifferentialGeometry.Topology
open DifferentialGeometry.PDE.RicciFlow DifferentialGeometry.PDE.RicciFlow.Perelman
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness (metricScalarAt_restrictOpen)
open Set TopologicalSpace
open scoped Manifold ContDiff

namespace GC.LongTime.Ch11

universe u

variable {H : ObservedHistory.{u}} {first first' : Fin (H.eventCount + 1)}
  {hle : first ≤ Fin.last H.eventCount}

/-- 起点后移的 survivor domain 带 regular open backward trace。 -/
theorem regularOpenBackwardTrace_survivorDomain_C12X (hff : first ≤ first') :
    Nonempty (RegularOpenBackwardTrace_C11E H first'
      (H.backwardSurvivorDomain first (Fin.last H.eventCount) hle)) :=
  regularOpenBackwardTrace_iff_le_survivorDomain_C11P2.2
    (H.backwardSurvivorDomain_mono_first hff)

/-- trace map = 原起点的 survivor map。 -/
theorem atStage_eq_backwardSurvivorMap_C12X (hff : first ≤ first')
    (E : RegularOpenBackwardTrace_C11E H first'
      (H.backwardSurvivorDomain first (Fin.last H.eventCount) hle))
    (j : Fin (H.eventCount + 1)) (hj : first' ≤ j) (hl : j ≤ Fin.last H.eventCount) :
    E.atStage j hj hl =
      H.backwardSurvivorMap first (Fin.last H.eventCount) hle j (hff.trans hj) hl := by
  funext x
  exact congrFun (H.backwardSurvivorMap_comp_inclusion_first (hfirst := hle)
    (hnext := Fin.le_last first') hff j hj hl) x

section flow

variable {s' : ℝ}
  {G : (H.stage (Fin.last H.eventCount)).IncomingSlab (H.time (Fin.last H.eventCount)) s'}
  {gflow : ℝ → SmoothRiemannianMetric ThreeModel
    (H.backwardSurvivorDomain first (Fin.last H.eventCount) hle)}

/-- survivor flow 在 stage `m` 的时段内 = stage 度量沿 survivor map 的拉回。 -/
private theorem s16c_pullback_at
    (hG : ∀ τ ∈ Icc (H.time (Fin.last H.eventCount)) H.horizon,
      G.flow.base.metric τ = H.stageMetric (Fin.last H.eventCount) τ)
    (hs' : H.horizon < s')
    (hslab : ∀ (j : Fin H.eventCount) (hf : first ≤ j.castSucc)
      (hl : j.succ ≤ Fin.last H.eventCount), ∀ τ ∈ Icc (H.time j.castSucc) (H.time j.succ),
        gflow τ = H.backwardSurvivorSlabMetric first (Fin.last H.eventCount) hle j hf hl τ)
    (hcur : ∀ τ ∈ Ico (H.time (Fin.last H.eventCount)) s',
      gflow τ = (G.flow.base.metric τ).restrictOpen
        (H.backwardSurvivorDomain first (Fin.last H.eventCount) hle))
    (m : Fin (H.eventCount + 1)) (hm : first ≤ m) {v : ℝ} (hmv : H.time m ≤ v)
    (hvh : v ≤ H.horizon) (hnext : ∀ i : Fin H.eventCount, m = i.castSucc → v < H.time i.succ) :
    gflow v = localPullMetric (H.stageMetric m v)
      (H.backwardSurvivorMap first (Fin.last H.eventCount) hle m hm (Fin.le_last _))
      (H.backwardSurvivorMap_isLocalDiffeomorph first _ hle m hm (Fin.le_last _)) := by
  rcases Fin.eq_castSucc_or_eq_last m with ⟨i, rfl⟩ | rfl
  · have hvi := hnext i rfl
    rw [hslab i hm (Fin.le_last _) v ⟨hmv, hvi.le⟩,
      H.backwardSurvivorSlabMetric_before first _ hle i hm (Fin.le_last _) hvi,
      ObservedHistory.stageMetric_castSucc_apply]
  · rw [hcur v ⟨hmv, hvh.trans_lt hs'⟩, hG v ⟨hmv, hvh⟩, ← localPullMetric_subtype_val]
    have hmap : H.backwardSurvivorMap first (Fin.last H.eventCount) hle (Fin.last H.eventCount)
        hm (Fin.le_last _) = Subtype.val :=
      funext fun z => H.backwardSurvivorMap_last first _ hle z
    apply SmoothRiemannianMetric.ext_inner
    intro z p q
    rw [localPullMetric_inner, localPullMetric_inner, hmap]

/-- **窗口子句**（v2 的 `∀ v, a ≤ v → S.base.metric v = (E.atStage …)^* stageMetric`）：
slab / current 子句 + 最后 stage 与 stage 度量一致 ⇒ 对 `first' ≤ activeStage v` 的每个时刻成立。 -/
theorem survivorFlow_window_C12X
    (hG : ∀ τ ∈ Icc (H.time (Fin.last H.eventCount)) H.horizon,
      G.flow.base.metric τ = H.stageMetric (Fin.last H.eventCount) τ)
    (hs' : H.horizon < s')
    (hslab : ∀ (j : Fin H.eventCount) (hf : first ≤ j.castSucc)
      (hl : j.succ ≤ Fin.last H.eventCount), ∀ τ ∈ Icc (H.time j.castSucc) (H.time j.succ),
        gflow τ = H.backwardSurvivorSlabMetric first (Fin.last H.eventCount) hle j hf hl τ)
    (hcur : ∀ τ ∈ Ico (H.time (Fin.last H.eventCount)) s',
      gflow τ = (G.flow.base.metric τ).restrictOpen
        (H.backwardSurvivorDomain first (Fin.last H.eventCount) hle))
    (hff : first ≤ first')
    (E : RegularOpenBackwardTrace_C11E H first'
      (H.backwardSurvivorDomain first (Fin.last H.eventCount) hle))
    (v : Icc (0 : ℝ) H.horizon) (hv : first' ≤ H.activeStage v) :
    gflow v = localPullMetric (H.stageMetric (H.activeStage v) v)
      (E.atStage (H.activeStage v) hv (Fin.le_last _)) (E.atStage_isLocalDiffeomorph _ _ _) := by
  have hnext : ∀ i : Fin H.eventCount, H.activeStage v = i.castSucc →
      (v : ℝ) < H.time i.succ := by
    intro i hi
    have h1 : (H.activeStage v).val < H.eventCount := by
      rw [hi, Fin.val_castSucc]
      exact i.isLt
    have h2 := H.activeStage_before_next v h1
    have heq : (⟨(H.activeStage v).val + 1, by omega⟩ : Fin (H.eventCount + 1)) = i.succ :=
      Fin.ext (by simp [hi])
    rwa [heq] at h2
  rw [s16c_pullback_at hG hs' hslab hcur (H.activeStage v) (hff.trans hv)
    (H.activeStage_time_le v) v.2.2 hnext]
  apply SmoothRiemannianMetric.ext_inner
  intro z p q
  rw [localPullMetric_inner, localPullMetric_inner,
    atStage_eq_backwardSurvivorMap_C12X hff E (H.activeStage v) hv (Fin.le_last _)]

end flow

/-- **G1 主结论**：最后 stage 上 `y` 处的 Full strong neck（`HistoryStrongNeckFull_C12X`，入射 slab
`G` 在 `[time last, t]` 上与 stage 度量一致，`t = horizon`）⇒ hStrong v2 neck 分支的体
（`U` = survivor domain，`a = t − R⁻¹`，trace `E`，闭窗口解 `S`，窗口子句，终端子句，`StrongNeck`）。 -/
theorem strongNeckV2Branch_of_full_C12X (H : ObservedHistory.{u}) {s' : ℝ}
    {G : (H.stage (Fin.last H.eventCount)).IncomingSlab (H.time (Fin.last H.eventCount)) s'}
    {ε t : ℝ} {y : (H.stage (Fin.last H.eventCount)).Carrier}
    (hG : ∀ τ ∈ Icc (H.time (Fin.last H.eventCount)) t,
      G.flow.base.metric τ = H.stageMetric (Fin.last H.eventCount) τ)
    (ht : H.horizon = t)
    (hpos : 0 < metricScalarAt (H.stageMetric (Fin.last H.eventCount) t) y)
    (hfull : H.HistoryStrongNeckFull_C12X (Fin.last H.eventCount) G ε y t) :
    ∃ (U : Opens (H.stage (Fin.last H.eventCount)).Carrier) (hyU : y ∈ U)
      (a : Icc (0 : ℝ) H.horizon)
      (E : RegularOpenBackwardTrace_C11E H (H.activeStage a) U)
      (S : SolutionOn (I := ThreeModel) (M := U)
        (RealTimeInterval.closed
          (t - (metricScalarAt (H.stageMetric (Fin.last H.eventCount) t) y)⁻¹) t
          (sub_le_self _ (inv_nonneg.mpr hpos.le)))),
      (a : ℝ) = t - (metricScalarAt (H.stageMetric (Fin.last H.eventCount) t) y)⁻¹ ∧
      IsSolutionOn S ∧
      (∀ v : Icc (0 : ℝ) H.horizon, ∀ hav : a ≤ v,
        S.base.metric v =
          localPullMetric (H.stageMetric (H.activeStage v) v)
            (E.atStage (H.activeStage v) (H.activeStage_mono hav) (Fin.le_last _))
            (E.atStage_isLocalDiffeomorph _ _ _)) ∧
      S.base.metric t = (H.stageMetric (Fin.last H.eventCount) t).restrictOpen U ∧
      Nonempty (StrongNeck S ε ⟨y, hyU⟩ t) := by
  subst ht
  obtain ⟨first, hle, hts, gflow, htk, hfirst, hslab, hcur, hsol, z, rfl, ⟨nk⟩⟩ := hfull
  have hR0 := inv_nonneg.mpr nk.Q_pos.le
  have hs' : H.horizon < s' := (nk.time_domain ⟨sub_le_self _ hR0, le_rfl⟩).2
  have hGh : ∀ τ ∈ Icc (H.time (Fin.last H.eventCount)) H.horizon,
      G.flow.base.metric τ = H.stageMetric (Fin.last H.eventCount) τ := hG
  have hcurh : gflow H.horizon = (H.stageMetric (Fin.last H.eventCount) H.horizon).restrictOpen
      (H.backwardSurvivorDomain first (Fin.last H.eventCount) hle) := by
    rw [hcur _ ⟨htk, hs'⟩, hGh _ ⟨htk, le_rfl⟩]
  have hscal : metricScalarAt (gflow H.horizon) z =
      metricScalarAt (H.stageMetric (Fin.last H.eventCount) H.horizon) z.val := by
    rw [hcurh, metricScalarAt_restrictOpen]
  have hfirst' : H.time first ≤
      H.horizon - (metricScalarAt (H.stageMetric (Fin.last H.eventCount) H.horizon) z.val)⁻¹ := by
    have hG' : G.flow.scalar H.horizon z.val =
        metricScalarAt (H.stageMetric (Fin.last H.eventCount) H.horizon) z.val := by
      change metricScalarAt (G.flow.base.metric H.horizon) z.val = _
      rw [hGh _ ⟨htk, le_rfl⟩]
    rw [← hG']
    exact hfirst
  let a : Icc (0 : ℝ) H.horizon :=
    ⟨_, (H.time_nonneg first).trans hfirst', sub_le_self _ (inv_nonneg.mpr hpos.le)⟩
  have hfa : first ≤ H.activeStage a := H.le_activeStage a first hfirst'
  obtain ⟨E⟩ := regularOpenBackwardTrace_survivorDomain_C12X (hle := hle) hfa
  refine ⟨H.backwardSurvivorDomain first (Fin.last H.eventCount) hle, z.2, a, E,
    ⟨⟨gflow⟩⟩, rfl, ?_, fun v hav => survivorFlow_window_C12X hGh hs' hslab hcur hfa E v
      (H.activeStage_mono hav), hcurh, ⟨nk.ofMetricEq (fun _ => rfl) ?_⟩⟩
  · exact isSolutionOn_timeRestrict hsol
      (fun r hr => ⟨hfirst'.trans hr.1, hr.2.trans_lt hs'⟩)
      (fun r hr => ⟨hfirst'.trans_lt hr.1, hr.2.trans hs'⟩)
  · intro r hr
    change r ∈ Icc (H.horizon - (metricScalarAt (gflow H.horizon) z)⁻¹) H.horizon at hr
    rw [hscal] at hr
    exact hr

end GC.LongTime.Ch11
