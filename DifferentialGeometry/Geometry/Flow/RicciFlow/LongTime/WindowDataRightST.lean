import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.WindowDataST
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.PostStageRightST

/-!
# 右端点 window 数据（lane S-A14-STATIC，G7b）

G6 的 `window_data_of_no_event_ST` 只处理 regular 时刻 `t₀`（两侧 event-free）。手术时刻 `t₀`
（`t₀ ∈ O.eventTimes`）的 HT-R / barrier 用右侧：`(t₀, t₀ + η)` 内无新事件即可（`t₀` 本身可以是
event 时刻，stage 恰于 `t₀` 开始）。本文件把 G6 的证明改到右端点：

* `G`：G7a 的 stage flow metric，`MetricFamilySmoothOn D G` 在 `[t₀, b)` 上（`Ico t₀ b ⊆ D.carrier`，
  `Ioo t₀ b ⊆ D.regular`，含 `t₀` 的单侧光滑），`G t₀ = postMetric t₀`（= outgoing stage 的 initial metric），
  `(t₀, b)` 上 `HasDerivAt`、`t₀` 处右导数 `HasDerivWithinAt … (Ici t₀) t₀`（`∂ₜ g = -2 Ric`）；
* `Φ`：SG 的 isotopy（`[t₀, b]` 在窗口 `J` 内；`J` 是 `t₀` 的开邻域，跨 event 的左侧也在 `J` 里，但我们只用
  `t ∈ [t₀, b)`，那里 active stage 常值）经 `isotopyExtend_ST` 延拓成全 stage 的 joint `C^∞` diffeo 族；
* 对 `t ∈ Ico t₀ b`：cast `ι`、`G t = ι^* postMetric t`、`ι ∘ Φ t ∘ γ_{t₀} = γ_t`、
  `(ι ∘ Φ t) '' region t₀ = region t`。
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

section Main

variable {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g} {K : ℕ}

/-- **G7b 主定理**：右端点 window 数据（`E.start < t₀`，`(t₀, b₁)` 内无新事件；`t₀` 可以是
event 时刻）。 -/
theorem window_data_right_of_no_event_ST (cores : PersistentHyperbolicCores F K)
    (E : PersistentCuspExterior cores) (i₀ : Fin cores.count)
    (port : Fin (E.truncation i₀).count) (loop : freeLoop Torus)
    (γ : (t : ℝ) → E.start ≤ t → freeLoop (postStage F.observation t).Carrier)
    (hγ : ∀ t (ht : E.start ≤ t) x, γ t ht x = cores.map i₀ t (E.after_cores.trans ht)
      ((E.truncation i₀).cuspMap port (loop x, halfZero)))
    {t₀ b₁ : ℝ} (ht₀ : E.start < t₀) (hab : t₀ < b₁)
    (hno : ∀ s ∈ F.observation.eventTimes, s ∉ Ioo t₀ b₁) :
    ∃ (b : ℝ) (D : RealTimeInterval)
      (G : ℝ → SmoothRiemannianMetric (𝓡 3) (postStage F.observation t₀).Carrier)
      (Φ : ℝ → (postStage F.observation t₀).Carrier ≃ₘ⟮𝓡 3, 𝓡 3⟯
        (postStage F.observation t₀).Carrier),
      t₀ < b ∧ b ≤ b₁ ∧ MetricFamilySmoothOn D G ∧ Ico t₀ b ⊆ D.carrier ∧
      Ioo t₀ b ⊆ D.regular ∧ G t₀ = postMetric F.observation t₀ ∧
      (∀ t ∈ Ioo t₀ b, ∀ (x : (postStage F.observation t₀).Carrier)
        (A B : TangentSpace ThreeModel x),
        HasDerivAt (fun r : ℝ => (G r).inner x A B)
          (-2 * ricciTensor (I := ThreeModel) (G t) x A B) t) ∧
      (∀ (x : (postStage F.observation t₀).Carrier) (A B : TangentSpace ThreeModel x),
        HasDerivWithinAt (fun r : ℝ => (G r).inner x A B)
          (-2 * ricciTensor (I := ThreeModel) (G t₀) x A B) (Ici t₀) t₀) ∧
      ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 3)) (𝓡 3) ∞
        (fun p : ℝ × (postStage F.observation t₀).Carrier => Φ p.1 p.2) (Ico t₀ b ×ˢ univ) ∧
      Φ t₀ = Diffeomorph.refl (𝓡 3) (postStage F.observation t₀).Carrier ∞ ∧
      ∀ t ∈ Ico t₀ b, ∀ ht : E.start ≤ t,
        ∃ ι : (postStage F.observation t₀).Carrier ≃ₘ⟮𝓡 3, 𝓡 3⟯ (postStage F.observation t).Carrier,
          G t = Diffeomorph.pullbackMetricCross (postMetric F.observation t) ι ∧
          (∀ θ, ι (Φ t (γ t₀ ht₀.le θ)) = γ t ht θ) ∧
          (fun p => ι (Φ t p)) '' E.region t₀ = E.region t := by
  classical
  have hcs : cores.start < t₀ := lt_of_le_of_lt E.after_cores ht₀
  have ht0pos : 0 < t₀ := cores.start_pos.trans hcs
  obtain ⟨Dt, S, hS, hSsm, hsm, hcar, hDreg, hmeq, hmeq₀, hderI, hderR⟩ :=
    exists_stageFlow_right_of_no_event_ST F.observation ht0pos.le hab hno
  have hSc : ∀ i, IsCompact (range (E.truncation i).inclusion) := fun i =>
    isCompact_range (E.truncation i).inclusion.continuous
  have hdom : ∀ i, range (E.truncation i).inclusion ⊆ cores.domain i t₀ := fun i =>
    range_inclusion_subset_domain_ST E i ht₀.le
  obtain ⟨N, Fs, Ls, hFL, J, U, z, hJh, hst, hτJ, hJo, -, hJstart, hUo, hSU, hUd, hz, hemb, hag,
      -⟩ :=
    exists_static_identification_SG cores hcs (fun i => range (E.truncation i).inclusion) hSc hdom
  have hJ' : IsOpen (J ∩ Ioi E.start ∩ Iio b₁) := (hJo.inter isOpen_Ioi).inter isOpen_Iio
  obtain ⟨l, u, ⟨hl, hu⟩, hIoo⟩ :=
    mem_nhds_iff_exists_Ioo_subset.mp (hJ'.mem_nhds ⟨⟨hτJ, ht₀⟩, hab⟩)
  have htb : t₀ < (t₀ + u) / 2 := by linarith
  have hb1 : (t₀ + u) / 2 < b₁ := (hIoo ⟨by linarith, by linarith⟩).2
  have hIcc : Icc t₀ ((t₀ + u) / 2) ⊆ J ∩ Ioi E.start ∩ Iio b₁ := fun t ht =>
    hIoo ⟨by linarith [ht.1], by linarith [ht.2]⟩
  set b := (t₀ + u) / 2 with hbdef
  have hJab : Icc t₀ b ⊆ J := fun t ht => (hIcc ht).1.1
  have hIno : ∀ t ∈ Icc t₀ b, t ∈ Ico t₀ b₁ := fun t ht => ⟨ht.1, ht.2.trans_lt hb1⟩
  obtain ⟨Φd, C, hCc, hsmd, hself, hcoc, hsupp, hmap⟩ := exists_window_isotopy_SG cores N Fs Ls
    hFL J hJh hst z U (fun i => range (E.truncation i).inclusion) hJo hJstart hUo hSc hSU hUd hz
    hag (a := t₀) (b := b) htb.le hJab
  have hι₀ld := windowEmbed_isLocalDiffeomorph_SG F.observation N Fs Ls hFL J hJh hst t₀ hτJ
  have hι₀inj := windowEmbed_injective_SG F.observation N Fs Ls hFL J hJh hst t₀ hτJ
  have : Nonempty ((F.observation.history N).backwardSurvivorDomain Fs Ls hFL) :=
    ⟨z i₀ (t₀, (cores.model i₀).basepoint)⟩
  have hsmX := contMDiff_isotopyExtend_ST (hemb t₀ hτJ).1 hι₀ld hsmd hCc hsupp
  refine ⟨b, Dt, S.base.metric, fun t => isotopyDiffeo_ST hι₀inj hself hcoc hsmX t₀ t, htb,
    hb1.le, hSsm, fun t ht => hcar ⟨ht.1, ht.2.trans hb1⟩,
    fun t ht => hDreg ⟨ht.1, ht.2.trans hb1⟩, hmeq₀,
    fun t ht => hderI t ⟨ht.1, ht.2.trans hb1⟩, hderR, ?_, ?_, ?_⟩
  · refine ContMDiff.contMDiffOn ?_
    exact hsmX.comp (f := fun p : ℝ × (postStage F.observation t₀).Carrier => ((t₀, p.1), p.2))
      ((contMDiff_const.prodMk contMDiff_fst).prodMk contMDiff_snd)
  · ext x
    exact isotopyExtend_self_ST hι₀inj hself t₀ x
  · intro t ht hE
    have htIcc : t ∈ Icc t₀ b := Ico_subset_Icc_self ht
    have ht₀Icc : t₀ ∈ Icc t₀ b := ⟨le_rfl, htb.le⟩
    have htJ : t ∈ J := hJab htIcc
    have hnoI : t ∈ Ico t₀ b₁ := hIno t htIcc
    have hp : postStage F.observation t₀ = postStage F.observation t :=
      postStage_eq_of_no_event_right_ST F.observation ht0pos.le hno ⟨le_rfl, hab⟩ hnoI
    have hact : (F.observation.history N).activeStage ⟨t, (hJh t htJ).1, (hJh t htJ).2⟩ =
        (F.observation.history N).activeStage ⟨t₀, (hJh t₀ hτJ).1, (hJh t₀ hτJ).2⟩ :=
      (activeStage_eq_of_no_event_right_ST F.observation N ht0pos.le hno ⟨le_rfl, hab⟩ hnoI ht.1
        (hJh t₀ hτJ).1 (hJh t htJ).1 ((hJh t₀ hτJ).2.trans (F.observation.horizon_eq N).le)
        ((hJh t htJ).2.trans (F.observation.horizon_eq N).le)).symm
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

variable {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g} {K : ℕ}
  {cores : PersistentHyperbolicCores F K}

/-- G7b consumer：`PrescribedCuspMeridian`、`PrescribedCuspMeridianTop_CPQ` 的字段原样喂进去；
`b₁` 由 `exists_noEvent_right_interval_ST` 给出（`t₀` 是任意时刻，包括 event 时刻）。 -/
example (M : PrescribedCuspMeridian cores) {t₀ : ℝ} (ht₀ : M.exterior.start < t₀) : True := by
  obtain ⟨b₁, hab, hno⟩ := exists_noEvent_right_interval_ST F.observation t₀
  have _w := window_data_right_of_no_event_ST cores M.exterior M.model M.port M.loop M.transported
    M.prescribed ht₀ hab hno
  trivial

example (M : PrescribedCuspMeridianTop_CPQ cores) {t₀ : ℝ} (ht₀ : M.exterior.start < t₀) :
    True := by
  obtain ⟨b₁, hab, hno⟩ := exists_noEvent_right_interval_ST F.observation t₀
  have _w := window_data_right_of_no_event_ST cores M.exterior M.model M.port M.loop M.transported
    M.prescribed ht₀ hab hno
  trivial

end Consumer

end GC.LongTime
