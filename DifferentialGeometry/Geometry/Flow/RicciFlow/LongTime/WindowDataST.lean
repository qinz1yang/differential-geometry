import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.IsotopyExtendST
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspP1.SurgeryTransportSG
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspP1.MeridianTop
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.PostStageStaticST
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspExteriorStaticST
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.MorreyAreaBarrierIF

/-!
# regular 时刻 `t₀` 的 window 数据（lane S-A14-STATIC，G6）

O-IFACE design §A.5 rev3 的 window 数据（`exists_C1_barrier_of_window_IF` 的参数）：对
`t₀ ∉ O.eventTimes`、`E.start < t₀`，在 event-free 开区间 `I = Ioo a b ∋ t₀` 上

* `G : ℝ → SmoothRiemannianMetric (𝓡 3) (postStage t₀).Carrier`：G1 的 stage flow 的 metric
  （`MetricFamilySmoothOn D G`、`D.regular ∈ 𝓝 t₀`、`G t₀ = postMetric t₀`），以及
  **`hder`**：`∀ t ∈ I, ∀ x A B, HasDerivAt (fun r => (G r).inner x A B)
  (-2 * ricciTensor (G t) x A B) t`（G2 的 Ricci flow 方程）；
* `Φ : ℝ → (postStage t₀).Carrier ≃ₘ (postStage t₀).Carrier`：S-A14-SURGERY 的 CP1-D5 isotopy
  （survivor domain `D` 上紧支撑 joint `C^∞`）经 `isotopyExtend_ST`（G6a）延拓到整个 stage 的 diffeo 族，
  joint `C^∞`、`Φ t₀ = refl`；
* 对 `t ∈ I`：`ι = stageDiffeo_ST`（G1 的 cast diffeo），`G t = ι^* postMetric t`
  （`pullbackMetricCross`），`ι ∘ Φ t ∘ γ_{t₀} = γ_t`，且 **image equality**
  `(ι ∘ Φ t) '' region t₀ = region t`（比 `MapsTo` 强，regular 时刻 HT-L 用 `(ι ∘ Φ t)⁻¹`）。

关键点：无事件区间里 `activeStage` 常值，所以 SG 的 `ι_t = windowEmbed_SG t` 与 `ι_{t₀}` 只差 G1 的 cast
（`stageDiffeo_windowEmbed_ST`）；`region` 的对应来自 SG 的 `windowTransport_region_SG`
（`range ι_{t₀}` 内）与 "`range ι_{t₀}` 外 `Φ` 是恒等且 cusp 内部像都在 `range ι_t` 里"（外）。
-/

set_option autoImplicit false
noncomputable section

open Set Function Filter Manifold DifferentialGeometry DifferentialGeometry.Topology
open DifferentialGeometry.PDE.RicciFlow DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.Geometry.Curvature GC.Endpoint GC.LongTime.CuspP1
open DifferentialGeometry.Geometry.Hyperbolic
open scoped Manifold ContDiff Topology

namespace GC.LongTime

universe u

/-- `backwardSurvivorMap` 在 stage 下标的（命题）等式下 `HEq`。 -/
theorem survivorMap_heq_of_eq_ST (H : ObservedHistory.{u}) (first last : Fin (H.eventCount + 1))
    (hle : first ≤ last) {j j' : Fin (H.eventCount + 1)} (hj : j = j') (h1 : first ≤ j)
    (h2 : j ≤ last) (h1' : first ≤ j') (h2' : j' ≤ last)
    (w : H.backwardSurvivorDomain first last hle) :
    HEq (H.backwardSurvivorMap first last hle j h1 h2 w)
      (H.backwardSurvivorMap first last hle j' h1' h2' w) := by
  subst hj
  rfl

variable {P : OrientedThreeStage.{u}} {g : P.Metric}

/-- 无事件窗口里 `activeStage` 相同的两个时刻 `t t'`：SG 的 `ι_t = windowEmbed_SG t` 与 `ι_{t'}`
只差 G1 的 cast diffeo `stageDiffeo_ST`。 -/
theorem stageDiffeo_windowEmbed_ST (T : ObservationTower P g) (N : ℕ)
    (Fs Ls : Fin ((T.history N).eventCount + 1)) (hFL : Fs ≤ Ls) (J : Set ℝ)
    (hJh : ∀ t ∈ J, 0 ≤ t ∧ t ≤ (T.history N).horizon)
    (hst : ∀ t (h0 : 0 ≤ t) (h1 : t ≤ (T.history N).horizon), t ∈ J →
      Fs ≤ (T.history N).activeStage ⟨t, h0, h1⟩ ∧ (T.history N).activeStage ⟨t, h0, h1⟩ ≤ Ls)
    {t t' : ℝ} (ht : t ∈ J) (ht' : t' ∈ J)
    (hact : (T.history N).activeStage ⟨t, (hJh t ht).1, (hJh t ht).2⟩ =
      (T.history N).activeStage ⟨t', (hJh t' ht').1, (hJh t' ht').2⟩)
    (h : postStage T t' = postStage T t) (w : (T.history N).backwardSurvivorDomain Fs Ls hFL) :
    stageDiffeo_ST h (windowEmbed_SG T N Fs Ls hFL J hJh hst t' ht' w) =
      windowEmbed_SG T N Fs Ls hFL J hJh hst t ht w := by
  apply eq_of_heq
  refine (heq_stageDiffeo_ST_apply h _).trans ?_
  refine (carrierHomeo_heq_CPD2 _ _).trans ?_
  refine HEq.trans ?_ (carrierHomeo_heq_CPD2 _ _).symm
  exact survivorMap_heq_of_eq_ST _ _ _ _ hact.symm _ _ _ _ w

/-- 无事件区间上 `activeStage`（固定 history `n`）常值（任意次序）。 -/
theorem activeStage_eq_any_ST (O : ObservationTower P g) (n : ℕ) {a b : ℝ} (ha : 0 ≤ a)
    (hno : ∀ s ∈ O.eventTimes, s ∉ Ioo a b) {t t' : ℝ} (ht : t ∈ Ioo a b)
    (ht' : t' ∈ Ioo a b) (ht0 : 0 ≤ t) (ht'0 : 0 ≤ t') (htn : t ≤ n) (ht'n : t' ≤ n) :
    (O.history n).activeStage (timeIn_ST O n ht0 htn) =
      (O.history n).activeStage (timeIn_ST O n ht'0 ht'n) := by
  rcases le_total t t' with h | h
  · exact activeStage_eq_of_no_event_ST O n ha hno ht ht' h ht0 ht'0 htn ht'n
  · exact (activeStage_eq_of_no_event_ST O n ha hno ht' ht h ht'0 ht0 ht'n htn).symm

section Main

variable {F : GC.Interface.RawSurgery P g} {K : ℕ}

/-- **G6 主定理（`window_data_of_no_event_ST`）**：regular 时刻 `t₀`（`E.start < t₀`、`t₀ ∉ O.eventTimes`）
的 window 数据（O-IFACE design §A.5 rev3 的形状，`MapsTo` 加强为 image equality，外加 `hder`）。
`cores`、`E`、`i₀`、`port`、`loop`、`γ` + `hγ` 是 `PrescribedCuspMeridian` /
`PrescribedCuspMeridianTop_CPQ` 共有的字段（`M.exterior`、`M.model`、`M.port`、`M.loop`、
`M.transported`、`M.prescribed`）。 -/
theorem window_data_of_no_event_ST (cores : PersistentHyperbolicCores F K)
    (E : PersistentCuspExterior cores) (i₀ : Fin cores.count)
    (port : Fin (E.truncation i₀).count) (loop : freeLoop Torus)
    (γ : (t : ℝ) → E.start ≤ t → freeLoop (postStage F.observation t).Carrier)
    (hγ : ∀ t (ht : E.start ≤ t) x, γ t ht x = cores.map i₀ t (E.after_cores.trans ht)
      ((E.truncation i₀).cuspMap port (loop x, halfZero)))
    {t₀ : ℝ} (ht₀ : E.start < t₀) (hreg : t₀ ∉ F.observation.eventTimes) :
    ∃ (I : Set ℝ) (D : RealTimeInterval)
      (G : ℝ → SmoothRiemannianMetric (𝓡 3) (postStage F.observation t₀).Carrier)
      (Φ : ℝ → (postStage F.observation t₀).Carrier ≃ₘ⟮𝓡 3, 𝓡 3⟯
        (postStage F.observation t₀).Carrier),
      IsOpen I ∧ t₀ ∈ I ∧ MetricFamilySmoothOn D G ∧ D.regular ∈ 𝓝 t₀ ∧
      G t₀ = postMetric F.observation t₀ ∧
      (∀ t ∈ I, ∀ (x : (postStage F.observation t₀).Carrier) (A B : TangentSpace ThreeModel x),
        HasDerivAt (fun r : ℝ => (G r).inner x A B)
          (-2 * ricciTensor (I := ThreeModel) (G t) x A B) t) ∧
      ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 3)) (𝓡 3) ∞
        (fun p : ℝ × (postStage F.observation t₀).Carrier => Φ p.1 p.2) (I ×ˢ univ) ∧
      Φ t₀ = Diffeomorph.refl (𝓡 3) (postStage F.observation t₀).Carrier ∞ ∧
      ∀ t ∈ I, ∀ ht : E.start ≤ t,
        ∃ ι : (postStage F.observation t₀).Carrier ≃ₘ⟮𝓡 3, 𝓡 3⟯ (postStage F.observation t).Carrier,
          G t = Diffeomorph.pullbackMetricCross (postMetric F.observation t) ι ∧
          (∀ θ, ι (Φ t (γ t₀ ht₀.le θ)) = γ t ht θ) ∧
          (fun p => ι (Φ t p)) '' E.region t₀ = E.region t := by
  classical
  have hcs : cores.start < t₀ := lt_of_le_of_lt E.after_cores ht₀
  have ht0pos : 0 < t₀ := cores.start_pos.trans hcs
  obtain ⟨a0, b0, ha0, ha0t, htb0, hno⟩ :=
    exists_noEvent_interval_ST F.observation ht0pos hreg
  obtain ⟨Dt, S, hS, hsm, hDreg, hmeq⟩ :=
    exists_stageFlow_of_no_event_ST F.observation ha0 hno (t₀ := t₀) ⟨ha0t, htb0⟩
  have hSc : ∀ i, IsCompact (range (E.truncation i).inclusion) := fun i =>
    isCompact_range (E.truncation i).inclusion.continuous
  have hdom : ∀ i, range (E.truncation i).inclusion ⊆ cores.domain i t₀ := fun i =>
    range_inclusion_subset_domain_ST E i ht₀.le
  obtain ⟨N, Fs, Ls, hFL, J, U, z, hJh, hst, hτJ, hJo, -, hJstart, hUo, hSU, hUd, hz, hemb, hag,
      -⟩ :=
    exists_static_identification_SG cores hcs (fun i => range (E.truncation i).inclusion) hSc hdom
  have hJ' : IsOpen (J ∩ Ioi E.start ∩ Ioo a0 b0) := (hJo.inter isOpen_Ioi).inter isOpen_Ioo
  obtain ⟨l, u, ⟨hl, hu⟩, hIoo⟩ :=
    mem_nhds_iff_exists_Ioo_subset.mp (hJ'.mem_nhds ⟨⟨hτJ, ht₀⟩, ha0t, htb0⟩)
  obtain ⟨a, b, hτab, hIcc⟩ : ∃ a b : ℝ, (a < t₀ ∧ t₀ < b) ∧
      Icc a b ⊆ J ∩ Ioi E.start ∩ Ioo a0 b0 :=
    ⟨(l + t₀) / 2, (t₀ + u) / 2, ⟨by linarith, by linarith⟩,
      fun t ht => hIoo ⟨by linarith [ht.1], by linarith [ht.2]⟩⟩
  have hJab : Icc a b ⊆ J := fun t ht => (hIcc ht).1.1
  have hEab : ∀ t ∈ Icc a b, E.start ≤ t := fun t ht => (hIcc ht).1.2.le
  have hIno : ∀ t ∈ Icc a b, t ∈ Ioo a0 b0 := fun t ht => (hIcc ht).2
  obtain ⟨Φd, C, hCc, hsmd, hself, hcoc, hsupp, hmap⟩ := exists_window_isotopy_SG cores N Fs Ls
    hFL J hJh hst z U (fun i => range (E.truncation i).inclusion) hJo hJstart hUo hSc hSU hUd hz
    hag (a := a) (b := b) (hτab.1.le.trans hτab.2.le) hJab
  have hι₀ld := windowEmbed_isLocalDiffeomorph_SG F.observation N Fs Ls hFL J hJh hst t₀ hτJ
  have hι₀inj := windowEmbed_injective_SG F.observation N Fs Ls hFL J hJh hst t₀ hτJ
  have : Nonempty ((F.observation.history N).backwardSurvivorDomain Fs Ls hFL) :=
    ⟨z i₀ (t₀, (cores.model i₀).basepoint)⟩
  have hsmX := contMDiff_isotopyExtend_ST (hemb t₀ hτJ).1 hι₀ld hsmd hCc hsupp
  refine ⟨Ioo a b, Dt, S.base.metric, fun t => isotopyDiffeo_ST hι₀inj hself hcoc hsmX t₀ t,
    isOpen_Ioo, hτab, hS.smoothMetric,
    Filter.mem_of_superset (isOpen_Ioo.mem_nhds ⟨ha0t, htb0⟩) hDreg,
    (hmeq t₀ ⟨ha0t, htb0⟩).trans (postMetricAt_ST_self _ _), ?_, ?_, ?_, ?_⟩
  · intro t ht x A B
    have hts : t ∈ Ioo a0 b0 := hIno t (Ioo_subset_Icc_self ht)
    have hd := (hS.equation ⟨t, hDreg hts⟩ x A B).hasDerivAt (Dt.regular_mem_nhds (hDreg hts))
    have hric : RicciAtFamily.toTensorField (I := ThreeModel) S.ricciAt t x A B =
        ricciTensor (I := ThreeModel) (S.base.metric t) x A B :=
      DifferentialGeometry.metricRicciAt_apply_eq_ricciTensor (I := ThreeModel) _ x A B
    rw [hric] at hd
    exact hd
  · refine ContMDiff.contMDiffOn ?_
    exact hsmX.comp (f := fun p : ℝ × (postStage F.observation t₀).Carrier => ((t₀, p.1), p.2))
      ((contMDiff_const.prodMk contMDiff_fst).prodMk contMDiff_snd)
  · ext x
    exact isotopyExtend_self_ST hι₀inj hself t₀ x
  · intro t ht hE
    have htIcc : t ∈ Icc a b := Ioo_subset_Icc_self ht
    have ht₀Icc : t₀ ∈ Icc a b := ⟨hτab.1.le, hτab.2.le⟩
    have htJ : t ∈ J := hJab htIcc
    have hnoI : t ∈ Ioo a0 b0 := hIno t htIcc
    have hp : postStage F.observation t₀ = postStage F.observation t :=
      postStage_eq_of_no_event_ST F.observation ha0 hno ⟨ha0t, htb0⟩ hnoI
    have hact : (F.observation.history N).activeStage ⟨t, (hJh t htJ).1, (hJh t htJ).2⟩ =
        (F.observation.history N).activeStage ⟨t₀, (hJh t₀ hτJ).1, (hJh t₀ hτJ).2⟩ :=
      activeStage_eq_any_ST F.observation N ha0 hno hnoI ⟨ha0t, htb0⟩ (hJh t htJ).1 (hJh t₀ hτJ).1
        ((hJh t htJ).2.trans (F.observation.horizon_eq N).le)
        ((hJh t₀ hτJ).2.trans (F.observation.horizon_eq N).le)
    have hY : ∀ w, stageDiffeo_ST hp (windowEmbed_SG F.observation N Fs Ls hFL J hJh hst t₀ hτJ w) =
        windowEmbed_SG F.observation N Fs Ls hFL J hJh hst t htJ w :=
      stageDiffeo_windowEmbed_ST F.observation N Fs Ls hFL J hJh hst htJ hτJ hact hp
    have hΦ : ∀ i, ∀ x ∈ range (E.truncation i).inclusion,
        Φd t₀ t (z i (t₀, x)) = z i (t, x) := fun i x hx => hmap i t₀ ht₀Icc t htIcc x hx
    have hΦ' : ∀ i, ∀ x ∈ range (E.truncation i).inclusion,
        Φd t t₀ (z i (t, x)) = z i (t₀, x) := fun i x hx => hmap i t htIcc t₀ ht₀Icc x hx
    refine ⟨stageDiffeo_ST hp, ?_, ?_, ?_⟩
    · rw [hmeq t hnoI, postMetricAt_ST_of_eq F.observation hp,
        Diffeomorph.pullbackMetricCross_eq_pullbackMetric]
    · intro θ
      rw [hγ t₀ ht₀.le θ, hγ t hE θ]
      have hy₀ : (E.truncation i₀).cuspMap port (loop θ, halfZero) ∈
          range (E.truncation i₀).inclusion := by
        rw [(E.truncation i₀).cusp_zero]
        exact ⟨_, rfl⟩
      have h1 := hag i₀ t₀ hτJ (E.after_cores.trans ht₀.le) _ (hSU i₀ hy₀)
      have h2 := hag i₀ t htJ (E.after_cores.trans hE) _ (hSU i₀ hy₀)
      change stageDiffeo_ST hp (isotopyExtend_ST
        (windowEmbed_SG F.observation N Fs Ls hFL J hJh hst t₀ hτJ) Φd t₀ t
        (cores.map i₀ t₀ (E.after_cores.trans ht₀.le) _)) = _
      rw [← h1, isotopyExtend_apply_ST hι₀inj, hΦ i₀ _ hy₀, hY, h2]
    · have hiff : ∀ x, x ∈ E.region t₀ ↔ stageDiffeo_ST hp (isotopyExtend_ST
          (windowEmbed_SG F.observation N Fs Ls hFL J hJh hst t₀ hτJ) Φd t₀ t x) ∈ E.region t := by
        intro x
        constructor
        · intro hx
          by_cases hr : x ∈ range (windowEmbed_SG F.observation N Fs Ls hFL J hJh hst t₀ hτJ)
          · obtain ⟨w, rfl⟩ := hr
            rw [isotopyExtend_apply_ST hι₀inj, hY]
            have hreg_t := windowTransport_region_SG cores N Fs Ls hFL J hJh hst z U
              (fun i => range (E.truncation i).inclusion) hSU hag Φd t₀ t hτJ htJ
              (z i₀ (t₀, (cores.model i₀).basepoint)) E
              (fun _ _ hx => hx) hΦ hΦ' hself hcoc ht₀.le hE
            have hmem : windowTransport_SG F.observation N Fs Ls hFL J hJh hst Φd t₀ t hτJ htJ
                (z i₀ (t₀, (cores.model i₀).basepoint))
                (windowEmbed_SG F.observation N Fs Ls hFL J hJh hst t₀ hτJ w) ∈
                E.region t ∩ range (windowEmbed_SG F.observation N Fs Ls hFL J hJh hst t htJ) := by
              rw [← hreg_t]
              exact ⟨_, ⟨hx, ⟨w, rfl⟩⟩, rfl⟩
            rw [windowTransport_apply_SG] at hmem
            exact hmem.1
          · rw [isotopyExtend_of_not_range_ST _ _ hr, region_eq_compl_cuspPart_ST E hE]
            intro hmem
            obtain ⟨j, y, ⟨c, hc, rfl⟩, hy⟩ := Set.mem_iUnion.1 hmem
            apply hr
            have hz := hag j t htJ (E.after_cores.trans hE) _ (hSU j ⟨c, rfl⟩)
            rw [← hY] at hz
            have h3 : stageDiffeo_ST hp (windowEmbed_SG F.observation N Fs Ls hFL J hJh hst t₀ hτJ
                (z j (t, (E.truncation j).inclusion c))) = stageDiffeo_ST hp x := hz.trans hy
            exact ⟨z j (t, (E.truncation j).inclusion c), (stageDiffeo_ST hp).injective h3⟩
        · intro hx
          by_contra hnot
          rw [region_eq_compl_cuspPart_ST E ht₀.le, Set.mem_compl_iff, not_not] at hnot
          obtain ⟨j, y, ⟨c, hc, rfl⟩, rfl⟩ := Set.mem_iUnion.1 hnot
          have hc0 : (E.truncation j).inclusion c ∈ range (E.truncation j).inclusion := ⟨c, rfl⟩
          have h0 := hag j t₀ hτJ (E.after_cores.trans ht₀.le) _ (hSU j hc0)
          have h1 := hag j t htJ (E.after_cores.trans hE) _ (hSU j hc0)
          rw [← h0, isotopyExtend_apply_ST hι₀inj, hΦ j _ hc0, hY, h1,
            region_eq_compl_cuspPart_ST E hE] at hx
          exact hx (Set.mem_iUnion.2 ⟨j, _, ⟨c, hc, rfl⟩, rfl⟩)
      ext y
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact (hiff x).1 hx
      · intro hy
        refine ⟨isotopyExtend_ST (windowEmbed_SG F.observation N Fs Ls hFL J hJh hst t₀ hτJ) Φd
          t t₀ ((stageDiffeo_ST hp).symm y), ?_, ?_⟩
        · rw [hiff]
          rw [isotopyExtend_comp_ST hι₀inj hcoc, isotopyExtend_self_ST hι₀inj hself,
            Diffeomorph.apply_symm_apply]
          exact hy
        · change stageDiffeo_ST hp (isotopyExtend_ST _ Φd t₀ t (isotopyExtend_ST _ Φd t t₀ _)) = y
          rw [isotopyExtend_comp_ST hι₀inj hcoc, isotopyExtend_self_ST hι₀inj hself,
            Diffeomorph.apply_symm_apply]

end Main

section Consumer

open DifferentialGeometry.Geometry DifferentialGeometry.Geometry.MinimalSurface

variable {F : GC.Interface.RawSurgery P g} {K : ℕ} {cores : PersistentHyperbolicCores F K}

/-- G6 consumer（type alignment，无转换）：`PrescribedCuspMeridian` 的 window 数据原样喂给 O-IFACE G2 的
`exists_C1_barrier_of_window_IF`（`hG hD hG₀ hΦ hΦ₀ hι`；`MapsTo` 由 image equality 的 `.le` 得到）。 -/
example (M : PrescribedCuspMeridian cores) {t₀ : ℝ} (ht₀ : M.exterior.start < t₀)
    (hreg : t₀ ∉ F.observation.eventTimes) (A : ℝ → ℝ)
    (hA_le : ∀ (t : ℝ) (ht : M.exterior.start ≤ t)
      (v : C(closedDisk, (postStage F.observation t).Carrier)),
      DiskSmoothUpToBoundary (E := EuclideanSpace ℝ (Fin 3)) v →
      DiskWeakJordanTrace (M.transported t ht) v → range v ⊆ M.exterior.region t →
      A t ≤ riemannianDiskArea (postMetric F.observation t) v) : True := by
  obtain ⟨I, D, G, Φ, hI, ht₀I, hG, hD, hG₀, -, hΦ, hΦ₀, hι⟩ :=
    window_data_of_no_event_ST cores M.exterior M.model M.port M.loop M.transported M.prescribed
      ht₀ hreg
  have _key := @exists_C1_barrier_of_window_IF P g F.observation
    (fun t => M.exterior.region t) M.exterior.start M.transported A t₀ ht₀.le hA_le I hI ht₀I G D
    hG hD hG₀ Φ hΦ hΦ₀ (fun t ht hts => by
      obtain ⟨ι, h1, h2, h3⟩ := hι t ht hts
      exact ⟨ι, h1, h2, fun p hp => h3.le ⟨p, hp, rfl⟩⟩)
  trivial

/-- G6 consumer：`PrescribedCuspMeridianTop_CPQ`（Top 版）同样适用——`window_data_of_no_event_ST` 只用
`exterior / model / port / loop / transported / prescribed` 六个同名字段。 -/
example (M : PrescribedCuspMeridianTop_CPQ cores) {t₀ : ℝ} (ht₀ : M.exterior.start < t₀)
    (hreg : t₀ ∉ F.observation.eventTimes) : True := by
  have _w := window_data_of_no_event_ST cores M.exterior M.model M.port M.loop M.transported
    M.prescribed ht₀ hreg
  trivial

end Consumer

end GC.LongTime
