import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.WindowDataST
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.PostStageGeneralST

/-!
# regular 时刻 `t₀` 的 window 数据加强版：`Φ` 在边界曲线上的 `t`-速度（lane S-A14-STATIC-2，G1）

`window_data_of_no_event_ST`（G6）把 `Φ` 藏在 `∃` 里，结论里没有 `Φ` 的 `t`-速度信息。本文件复制
G6 的构造（同一个 `Φd`、`isotopyExtend_ST`、`stageDiffeo_ST`），在原有条款之外多一条 **`hvel`**
（O-W-CURV 冻结的形状）：对每个 `s`，`W s := ∂_r|_{t₀} Φ r (γ_{t₀}(s))` 在 `postMetric t₀` 下满足
`√(g(W s, W s))·√t₀ < cores.accuracy t₀`（parabolic scaling 下的速度小）。

数学：`Φ r (γ_{t₀}(s)) = ι_{t₀}(z(r, x))`（`x = cuspMap(loop s, halfZero) ∈ range inclusion`），其
`t`-速度就是 `static_patches` 在 `x` 的 patch 的 `track` 速度经 cast diffeo
`c : postStage t₀ ≃ stageAt` 的搬运：`c ∘ Φ_·(γ_{t₀} s) = track(·, x)`（`HEq` 链：
`heq_stageDiffeo_ST_apply`、`ι_r(Φ_r γ_{t₀}) = γ_r`、patch `agrees`、无事件区间 `activeStage` 常值），
再链式法则 + `postMetric = pullbackMetric stageMetric c`（G5 的 HEq 桥）+ patch 的 `speed` 字段。
把 G6 证明里 `∀ t ∈ I` 的条款先作为 `hlast`（显式 `ι := stageDiffeo_ST hp`）证出，供 `hvel` 复用。
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

variable {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g} {K : ℕ}

section Velocity

/-- 无事件窗口内 `t₀` 处，任何与 `cores.map i r · x` 在 `r ≈ t₀` 上 `HEq` 的光滑曲线 `φ`
（`φ r ∈ postStage t₀`）的 `t₀`-速度 `φ'(t₀)` 在 `postMetric t₀` 下满足 patch 的 speed 界
`g(φ', φ') < acc² / t₀`：`static_patches` 在 `x` 的 patch 的 `track` 经 `postStage t₀ = stageAt`
的 cast diffeo `c` 满足 `c ∘ φ = track(·, x)`（活跃 stage 常值），链式法则给 `dc φ' = ∂_t track`。 -/
theorem velocity_of_heq_curve_ST2 (cores : PersistentHyperbolicCores F K) {a0 b0 : ℝ}
    (ha0 : 0 ≤ a0) (hno : ∀ s ∈ F.observation.eventTimes, s ∉ Ioo a0 b0) {t₀ : ℝ}
    (ht₀ : t₀ ∈ Ioo a0 b0) (hstart : cores.start < t₀) (i : Fin cores.count)
    (x : (cores.model i).Carrier) (hx : x ∈ cores.domain i t₀)
    (φ : ℝ → (postStage F.observation t₀).Carrier) (y : (postStage F.observation t₀).Carrier)
    (hy : φ t₀ = y) (hφ : MDifferentiableAt 𝓘(ℝ, ℝ) (𝓡 3) φ t₀)
    (hheq : ∀ᶠ r in 𝓝 t₀, ∀ hr : cores.start ≤ r, HEq (φ r) (cores.map i r hr x)) :
    (postMetric F.observation t₀).inner y (mfderiv 𝓘(ℝ, ℝ) (𝓡 3) φ t₀ 1)
      (mfderiv 𝓘(ℝ, ℝ) (𝓡 3) φ t₀ 1) < cores.accuracy t₀ ^ 2 / t₀ := by
  classical
  subst hy
  obtain ⟨P0⟩ := cores.static_patches i t₀ hstart.le x hx
  have hm : t₀ ∈ Ioo P0.a P0.b := ⟨P0.before, P0.after⟩
  have hI : t₀ ∈ Icc (0 : ℝ) (F.tower.history P0.n).horizon :=
    ⟨P0.a_nonneg.trans P0.before.le, P0.after.le.trans P0.horizon⟩
  have hsp := P0.speed ⟨t₀, hI⟩ hm hstart.le x P0.mem_neighborhood
  have hstage := postStage_eq_stageAt_tower_ST F P0.n ⟨t₀, hI⟩
  let c := stageDiffeo_ST hstage
  let H := (F.tower.history P0.n).toHistory
  let j := H.activeStage ⟨t₀, hI⟩
  let trk : ℝ × (cores.model i).Carrier → (H.stage j).Carrier := fun p =>
    H.backwardSurvivorMap P0.first P0.last P0.ordered j (P0.stages ⟨t₀, hI⟩ hm).1
      (P0.stages ⟨t₀, hI⟩ hm).2 (P0.map p)
  have hev : ∀ᶠ r in 𝓝 t₀, c (φ r) = trk (r, x) := by
    filter_upwards [isOpen_Ioo.mem_nhds hm, isOpen_Ioo.mem_nhds ht₀, Ioi_mem_nhds hstart, hheq]
      with r hr1 hr2 hr3 hr4
    have hr0 : 0 ≤ r := P0.a_nonneg.trans hr1.1.le
    have hrh : r ≤ (F.tower.history P0.n).horizon := hr1.2.le.trans P0.horizon
    have hag := P0.agrees ⟨r, hr0, hrh⟩ hr1 hr3.le x P0.mem_neighborhood
    have hact : H.activeStage ⟨r, hr0, hrh⟩ = j :=
      activeStage_eq_any_ST F.observation P0.n ha0 hno hr2 ht₀ hr0 (P0.a_nonneg.trans P0.before.le)
        (hrh.trans (F.observation.horizon_eq P0.n).le)
        (hI.2.trans (F.observation.horizon_eq P0.n).le)
    refine eq_of_heq ?_
    refine (heq_stageDiffeo_ST_apply hstage _).trans ?_
    refine (hr4 hr3.le).trans ?_
    refine hag.symm.trans ?_
    exact survivorMap_heq_of_eq_ST H _ _ _ hact _ _ _ _ _
  have hmapAt : ContMDiffAt (𝓘(ℝ, ℝ).prod (𝓡 3)) (𝓡 3) ∞ P0.map (t₀, x) :=
    P0.smooth.contMDiffAt
      ((isOpen_Ioo.prod P0.neighborhood.isOpen).mem_nhds ⟨hm, P0.mem_neighborhood⟩)
  have hbs := (H.backwardSurvivorMap_isLocalDiffeomorph P0.first P0.last P0.ordered j
    (P0.stages ⟨t₀, hI⟩ hm).1 (P0.stages ⟨t₀, hI⟩ hm).2).contMDiff
  have htrk : MDifferentiableAt (𝓘(ℝ, ℝ).prod (𝓡 3)) (𝓡 3) trk (t₀, x) :=
    (hbs.contMDiffAt.comp (t₀, x) hmapAt).mdifferentiableAt (by simp)
  have hpairD : HasMFDerivAt 𝓘(ℝ, ℝ) (𝓘(ℝ, ℝ).prod (𝓡 3)) (fun r : ℝ => (r, x)) t₀
      ((ContinuousLinearMap.id ℝ ℝ).prod (0 : ℝ →L[ℝ] EuclideanSpace ℝ (Fin 3))) :=
    (hasMFDerivAt_id (I := 𝓘(ℝ, ℝ)) t₀).prodMk
      (hasMFDerivAt_const (I := 𝓘(ℝ, ℝ)) (I' := 𝓡 3) x t₀)
  have hpair : MDifferentiableAt 𝓘(ℝ, ℝ) (𝓘(ℝ, ℝ).prod (𝓡 3)) (fun r : ℝ => (r, x)) t₀ :=
    hpairD.mdifferentiableAt
  have hcd : MDifferentiableAt (𝓡 3) (𝓡 3) c (φ t₀) := c.contMDiff.mdifferentiableAt (by simp)
  have hψ := HasMFDerivAt.comp t₀ htrk.hasMFDerivAt hpair.hasMFDerivAt
  have hcφ := HasMFDerivAt.comp t₀ hcd.hasMFDerivAt hφ.hasMFDerivAt
  have hcφ' := hcφ.congr_of_eventuallyEq_abuse
    (f₁ := fun r : ℝ => trk (r, x)) (hev.mono fun r hr => hr.symm)
  have hW : mfderiv (𝓡 3) (𝓡 3) c (φ t₀) (mfderiv 𝓘(ℝ, ℝ) (𝓡 3) φ t₀ 1) =
      mfderiv (𝓘(ℝ, ℝ).prod (𝓡 3)) (𝓡 3) trk (t₀, x) ((1 : ℝ), (0 : EuclideanSpace ℝ (Fin 3))) := by
    have h := congrArg (fun L => L (1 : ℝ)) (hcφ'.mfderiv.symm.trans hψ.mfderiv)
    rw [hpairD.mfderiv] at h
    exact h
  have hc0 : c (φ t₀) = trk (t₀, x) := hev.self_of_nhds
  have hpb : Diffeomorph.pullbackMetric (H.stageMetric j t₀) c = postMetric F.observation t₀ :=
    eq_of_heq ((heq_pullbackMetric_stageDiffeo_ST hstage _).trans
      (postMetric_heq_stageMetric_tower_ST F P0.n ⟨t₀, hI⟩).symm)
  rw [← hpb, Diffeomorph.pullbackMetric_inner, hW, hc0]
  exact hsp

/-- `velocity_of_heq_curve_ST2` 的 scaled 形式：`√(g(φ', φ'))·√t₀ < acc t₀`（parabolic scaling 下
的速度）。 -/
theorem velocity_sqrt_of_heq_curve_ST2 (cores : PersistentHyperbolicCores F K) {a0 b0 : ℝ}
    (ha0 : 0 ≤ a0) (hno : ∀ s ∈ F.observation.eventTimes, s ∉ Ioo a0 b0) {t₀ : ℝ}
    (ht₀ : t₀ ∈ Ioo a0 b0) (hstart : cores.start < t₀) (i : Fin cores.count)
    (x : (cores.model i).Carrier) (hx : x ∈ cores.domain i t₀)
    (φ : ℝ → (postStage F.observation t₀).Carrier) (y : (postStage F.observation t₀).Carrier)
    (hy : φ t₀ = y) (hφ : MDifferentiableAt 𝓘(ℝ, ℝ) (𝓡 3) φ t₀)
    (hheq : ∀ᶠ r in 𝓝 t₀, ∀ hr : cores.start ≤ r, HEq (φ r) (cores.map i r hr x)) :
    Real.sqrt ((postMetric F.observation t₀).inner y (mfderiv 𝓘(ℝ, ℝ) (𝓡 3) φ t₀ 1)
        (mfderiv 𝓘(ℝ, ℝ) (𝓡 3) φ t₀ 1)) * Real.sqrt t₀ < cores.accuracy t₀ := by
  subst hy
  have h := velocity_of_heq_curve_ST2 cores ha0 hno ht₀ hstart i x hx φ _ rfl hφ hheq
  have hpos : 0 < t₀ := cores.start_pos.trans hstart
  have hQ := metric_inner_self_nonneg (postMetric F.observation t₀) (φ t₀)
    (mfderiv 𝓘(ℝ, ℝ) (𝓡 3) φ t₀ 1)
  rw [← Real.sqrt_mul hQ, Real.sqrt_lt' (cores.accuracy_pos t₀ hstart.le)]
  exact (lt_div_iff₀ hpos).mp h

/-- 纯算术：`√Q·√t < a` ⇒ `Q < a² / t`（`Q ≥ 0`、`t > 0`）。 -/
theorem lt_div_of_sqrt_mul_sqrt_lt_ST2 {Q a t : ℝ} (hQ : 0 ≤ Q) (ht : 0 < t)
    (h : Real.sqrt Q * Real.sqrt t < a) : Q < a ^ 2 / t := by
  rw [← Real.sqrt_mul hQ] at h
  have ha : 0 < a := lt_of_le_of_lt (Real.sqrt_nonneg _) h
  rw [Real.sqrt_lt' ha] at h
  exact (lt_div_iff₀ ht).mpr h

end Velocity

section Main

/-- **G1 主定理（`window_data_flux_of_no_event_ST2`）**：`window_data_of_no_event_ST` 的加强版，
在 `Φ t₀ = refl` 之后多一条 `hvel`：`Φ` 在 `γ_{t₀}(s)` 处的 `t₀`-速度 `W s` 满足
`√(g_{t₀}(W s, W s))·√t₀ < cores.accuracy t₀`（与 BOUNDARY `velocity_postMetric_BD` 第二条同形）。
前提与原定理逐字相同。 -/
theorem window_data_flux_of_no_event_ST2 (cores : PersistentHyperbolicCores F K)
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
      (∀ s : ℝ,
        Real.sqrt ((postMetric F.observation t₀).inner (loopLift (γ t₀ ht₀.le) s)
            (mfderiv 𝓘(ℝ, ℝ) (𝓡 3) (fun r : ℝ => Φ r (loopLift (γ t₀ ht₀.le) s)) t₀ 1)
            (mfderiv 𝓘(ℝ, ℝ) (𝓡 3) (fun r : ℝ => Φ r (loopLift (γ t₀ ht₀.le) s)) t₀ 1)) *
          Real.sqrt t₀ < cores.accuracy t₀) ∧
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
  have hlast : ∀ t ∈ Ioo a b, ∀ hE : E.start ≤ t,
      ∃ hp : postStage F.observation t₀ = postStage F.observation t,
        S.base.metric t = Diffeomorph.pullbackMetricCross (postMetric F.observation t)
          (stageDiffeo_ST hp) ∧
        (∀ θ, stageDiffeo_ST hp (isotopyExtend_ST
          (windowEmbed_SG F.observation N Fs Ls hFL J hJh hst t₀ hτJ) Φd t₀ t
          (γ t₀ ht₀.le θ)) = γ t hE θ) ∧
        (fun p => stageDiffeo_ST hp (isotopyExtend_ST
          (windowEmbed_SG F.observation N Fs Ls hFL J hJh hst t₀ hτJ) Φd t₀ t p)) ''
          E.region t₀ = E.region t := by
    intro t ht hE
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
    refine ⟨hp, ?_, ?_, ?_⟩
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
  refine ⟨Ioo a b, Dt, S.base.metric, fun t => isotopyDiffeo_ST hι₀inj hself hcoc hsmX t₀ t,
    isOpen_Ioo, hτab, hS.smoothMetric,
    Filter.mem_of_superset (isOpen_Ioo.mem_nhds ⟨ha0t, htb0⟩) hDreg,
    (hmeq t₀ ⟨ha0t, htb0⟩).trans (postMetricAt_ST_self _ _), ?_, ?_, ?_, ?_, ?_⟩
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
  · intro s
    have hy₀ : (E.truncation i₀).cuspMap port (loop (s : loopCircle), halfZero) ∈
        range (E.truncation i₀).inclusion := by
      rw [(E.truncation i₀).cusp_zero]
      exact ⟨_, rfl⟩
    have hγ0 : loopLift (γ t₀ ht₀.le) s = cores.map i₀ t₀ (E.after_cores.trans ht₀.le)
        ((E.truncation i₀).cuspMap port (loop (s : loopCircle), halfZero)) :=
      hγ t₀ ht₀.le (s : loopCircle)
    refine velocity_sqrt_of_heq_curve_ST2 cores ha0 hno ⟨ha0t, htb0⟩ hcs i₀
      ((E.truncation i₀).cuspMap port (loop (s : loopCircle), halfZero)) (hdom i₀ hy₀) _
      (loopLift (γ t₀ ht₀.le) s) ?_ ?_ ?_
    · change isotopyExtend_ST (windowEmbed_SG F.observation N Fs Ls hFL J hJh hst t₀ hτJ) Φd t₀ t₀
        (loopLift (γ t₀ ht₀.le) s) = _
      exact isotopyExtend_self_ST hι₀inj hself t₀ _
    · exact (hsmX.comp (f := fun r : ℝ => ((t₀, r), loopLift (γ t₀ ht₀.le) s))
        ((contMDiff_const.prodMk contMDiff_id).prodMk contMDiff_const)).mdifferentiableAt
        (by simp)
    · filter_upwards [isOpen_Ioo.mem_nhds hτab] with r hr hcr
      have hE : E.start ≤ r := hEab r (Ioo_subset_Icc_self hr)
      obtain ⟨hp, -, h2, -⟩ := hlast r hr hE
      have h3 := h2 (s : loopCircle)
      rw [hγ r hE (s : loopCircle)] at h3
      exact (heq_stageDiffeo_ST_apply hp _).symm.trans (heq_of_eq h3)
  · intro t ht hE
    obtain ⟨hp, h1, h2, h3⟩ := hlast t ht hE
    exact ⟨stageDiffeo_ST hp, h1, h2, h3⟩

end Main

section Consumer

open DifferentialGeometry.Geometry DifferentialGeometry.Geometry.MinimalSurface

variable {cores : PersistentHyperbolicCores F K}

/-- G1 consumer（type alignment + 用到 `hvel`）：`PrescribedCuspMeridian` 的加强 window 数据照旧喂给
O-IFACE G2 的 `exists_C1_barrier_of_window_IF`（`hvel` 之外的条款逐字同 G6 的 consumer），并且
`hvel` 本身给出 flux 被积函数里速度因子的平方形式 `g(W, W) < acc² / t₀`。 -/
example (M : PrescribedCuspMeridian cores) {t₀ : ℝ} (ht₀ : M.exterior.start < t₀)
    (hreg : t₀ ∉ F.observation.eventTimes) (A : ℝ → ℝ)
    (hA_le : ∀ (t : ℝ) (ht : M.exterior.start ≤ t)
      (v : C(closedDisk, (postStage F.observation t).Carrier)),
      DiskSmoothUpToBoundary (E := EuclideanSpace ℝ (Fin 3)) v →
      DiskWeakJordanTrace (M.transported t ht) v → range v ⊆ M.exterior.region t →
      A t ≤ riemannianDiskArea (postMetric F.observation t) v) : True := by
  obtain ⟨I, D, G, Φ, hI, ht₀I, hG, hD, hG₀, -, hΦ, hΦ₀, hvel, hι⟩ :=
    window_data_flux_of_no_event_ST2 cores M.exterior M.model M.port M.loop M.transported
      M.prescribed ht₀ hreg
  have _key := @exists_C1_barrier_of_window_IF P g F.observation
    (fun t => M.exterior.region t) M.exterior.start M.transported A t₀ ht₀.le hA_le I hI ht₀I G D
    hG hD hG₀ Φ hΦ hΦ₀ (fun t ht hts => by
      obtain ⟨ι, h1, h2, h3⟩ := hι t ht hts
      exact ⟨ι, h1, h2, fun p hp => h3.le ⟨p, hp, rfl⟩⟩)
  have _sq : ∀ s : ℝ,
      (postMetric F.observation t₀).inner (loopLift (M.transported t₀ ht₀.le) s)
        (mfderiv 𝓘(ℝ, ℝ) (𝓡 3) (fun r : ℝ => Φ r (loopLift (M.transported t₀ ht₀.le) s)) t₀ 1)
        (mfderiv 𝓘(ℝ, ℝ) (𝓡 3) (fun r : ℝ => Φ r (loopLift (M.transported t₀ ht₀.le) s)) t₀ 1) <
        cores.accuracy t₀ ^ 2 / t₀ := fun s => by
    have hpos : 0 < t₀ := cores.start_pos.trans (M.exterior.after_cores.trans_lt ht₀)
    exact lt_div_of_sqrt_mul_sqrt_lt_ST2 (metric_inner_self_nonneg _ _ _) hpos (hvel s)
  trivial

/-- G1 consumer：`PrescribedCuspMeridianTop_CPQ`（Top 版）同样适用，`hvel` 的点是
`M.transported t₀`。 -/
example (M : PrescribedCuspMeridianTop_CPQ cores) {t₀ : ℝ} (ht₀ : M.exterior.start < t₀)
    (hreg : t₀ ∉ F.observation.eventTimes) : True := by
  obtain ⟨I, D, G, Φ, -, -, -, -, -, -, -, -, hvel, -⟩ :=
    window_data_flux_of_no_event_ST2 cores M.exterior M.model M.port M.loop M.transported
      M.prescribed ht₀ hreg
  have _v : ∀ s : ℝ,
      Real.sqrt ((postMetric F.observation t₀).inner (loopLift (M.transported t₀ ht₀.le) s)
        (mfderiv 𝓘(ℝ, ℝ) (𝓡 3) (fun r : ℝ => Φ r (loopLift (M.transported t₀ ht₀.le) s)) t₀ 1)
        (mfderiv 𝓘(ℝ, ℝ) (𝓡 3) (fun r : ℝ => Φ r (loopLift (M.transported t₀ ht₀.le) s)) t₀ 1)) *
        Real.sqrt t₀ < cores.accuracy t₀ := hvel
  trivial

end Consumer

end GC.LongTime
