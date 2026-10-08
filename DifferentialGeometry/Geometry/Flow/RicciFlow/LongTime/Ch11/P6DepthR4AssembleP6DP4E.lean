import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6DepthR4PickP6DP4E
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6J10WireStayProdP6JW

/-!
# 深度归纳期 4 / R4 前半装配（DEPTH4E-1 续，后缀 `_P6DP4E`）：单族逐 `k` 的 R4 中心取点与数据搬运

`exists_R4_center_family_P6DP4E`：一个塔族（`K k`、event `i k`、`σ k = time (i k)⁺`）加上逐 `k` 的坏集
（`∃ p′ ↦ q ≍ y k` 的 crossing，且 `∃ᶠ t ↑ time (i k)⁺` 坏）⇒ 选出 R4 中心族 `(t_k, y′_k ≍ p′_k)`，并带上：
坏性；`σ − t ≤ 1/R`；DEPTH4D T1′ 的 hgood（`L = Λ − 2`）；T2 的 hwin。
所用引理：
* 取点 `exists_pick_frequently_eventually_P6DP4E`，好集合为
  - `hcomp_R4_eventually_P6DP4E`（δ = 1/√R）；
  - `eventually_close_P6DP4E`；
  - `aSeed < t`；
  - `time (i k)⁻ < t`；
* `y′` 用 `exists_heq_stageAt_P6JW` 取，`activeStage t = (i k).castSucc` 用
  `activeStage_eq_castSucc_of_mem_P6FF`；
* 搬运用 DEPTH4D 的 `hgood_center_transport_seq_P6DP4D` / `window_center_transport_P6DP4D`。
前提 = records 结构数据 + `hOld`（DIST 已登记形）+ 两端 output 标量 `< scale/2`（⇐ hsepWK 形，
`scalar_lt_half_scale_of_sep*`）。跨族对角化（`K = m`，BCDBOOT 合同否定）属于 E2，见 state。
-/

set_option autoImplicit false

noncomputable section

open Set Filter
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open scoped NNReal Topology Manifold ContDiff ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

/-- **event slab 内的时刻是 Icc 点（`_P6DP4E`）**。 -/
theorem mem_Icc_of_mem_slab_P6DP4E (K : RetainedCoreHistory.{u}) (e : Fin K.eventCount) {t : ℝ}
    (ht : t ∈ Ioo (K.time e.castSucc) (K.time e.succ)) : t ∈ Icc (0 : ℝ) K.toHistory.horizon := by
  have h0 : K.time 0 ≤ K.time e.castSucc := K.time_strictMono.monotone (Fin.zero_le _)
  have h1 : K.time e.succ ≤ K.time (Fin.last K.eventCount) :=
    K.time_strictMono.monotone (Fin.le_last _)
  have h2 := K.time_le_horizon
  rw [K.time_zero] at h0
  exact ⟨by linarith [ht.1], by linarith [ht.2]⟩

/-- **单族 R4 中心取点 + 数据搬运（`_P6DP4E`，PROVED 相对 records / hOld / 两端标量条件）**。 -/
theorem exists_R4_center_family_P6DP4E :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧
    ∀ {eps C1' C2' : ℝ} {Ctime' : ℝ≥0} (K : ℕ → RetainedCoreHistory.{u})
      (i : ∀ k, Fin (K k).eventCount) {q : ℕ → CutoffParameters}
      (rec : ∀ k, GeometricCutoffRecord (K k).toHistory (i k) (q k))
      (Tn aSeed σ : ∀ k, Icc (0 : ℝ) (K k).toHistory.horizon)
      (haT : ∀ k, aSeed k ≤ Tn k) (hsT : ∀ k, σ k ≤ Tn k) (has : ∀ k, aSeed k ≤ σ k)
      (p : ∀ k, ((K k).toHistory.stageAt (Tn k)).Carrier)
      (seedTrace : ∀ k, BackwardPointTrace (K k).toHistory ((K k).toHistory.activeStage (aSeed k))
        ((K k).toHistory.activeStage (Tn k)) ((K k).toHistory.activeStage_mono (haT k)) (p k))
      (y : ∀ k, ((K k).toHistory.stageAt (σ k)).Carrier) (R Λ : ℕ → ℝ),
      (∀ k, 0 < R k) → (∀ k, 2 ≤ Λ k) → (∀ k, (aSeed k : ℝ) < σ k) →
      (∀ k, (σ k : ℝ) = (K k).time (i k).succ) →
      ∀ (hf : ∀ k, (K k).toHistory.activeStage (aSeed k) ≤ (i k).castSucc)
        (hl : ∀ k, (i k).succ ≤ (K k).toHistory.activeStage (Tn k)),
      (∀ k, ((K k).toHistory.event (i k)).old =
        ((K k).toHistory.event (i k)).transition.trace.retainedCore) →
      (∀ k b, ((rec k).static b).hasCanonicalWindow) →
      (∀ k, (q k).modelAccuracy ≤ ε₀) → (∀ k, 2 ≤ (q k).modelOrder) →
      (∀ k, StandardCap.transitionEnd + 10 < (q k).modelRadius) →
      (∀ k b, metricScalarAt ((K k).toHistory.event (i k)).outputMetric
          ((seedTrace k).point (i k).succ ((hf k).trans (Fin.castSucc_lt_succ (i := i k)).le)
            (hl k)) < ((rec k).static b).neck.scale / 2) →
      (∀ k (wp : ((K k).toHistory.stage (i k).succ).Carrier), HEq (y k) wp →
        ∀ b, metricScalarAt ((K k).toHistory.event (i k)).outputMetric wp <
          ((rec k).static b).neck.scale / 2) →
      (∀ k, ∀ (v : Icc (0 : ℝ) (K k).toHistory.horizon) (hav : aSeed k ≤ v) (hvs : v ≤ σ k),
        (σ k : ℝ) - Λ k ^ 2 / R k ≤ (v : ℝ) →
        ∀ z : ((K k).toHistory.stageAt v).Carrier,
          riemannianEDistOf ((K k).toHistory.stageMetric ((K k).toHistory.activeStage v) v)
              ((seedTrace k).point ((K k).toHistory.activeStage v)
                ((K k).toHistory.activeStage_mono hav)
                ((K k).toHistory.activeStage_mono (hvs.trans (hsT k)))) z ≤
            riemannianEDistOf ((K k).toHistory.stageMetric ((K k).toHistory.activeStage (σ k))
                (σ k))
                ((seedTrace k).point ((K k).toHistory.activeStage (σ k))
                  ((K k).toHistory.activeStage_mono (has k))
                  ((K k).toHistory.activeStage_mono (hsT k))) (y k) +
              ENNReal.ofReal (Λ k / Real.sqrt (R k)) →
          4 * R k ≤ metricScalarAt ((K k).toHistory.stageMetric
            ((K k).toHistory.activeStage v) v) z →
          (K k).toHistory.HasSpatialCanonicalTimeControl eps C1' C2' Ctime' v z) →
      ∀ (Bad : ∀ k, ((K k).toHistory.stage (i k).castSucc).Carrier → ℝ → Prop),
      (∀ k, ∃ (pm : ((K k).toHistory.stage (i k).castSucc).Carrier)
          (wp : ((K k).toHistory.stage (i k).succ).Carrier),
          HEq (y k) wp ∧ ((K k).toHistory.event (i k)).RegularCrossing pm wp ∧
          ∃ᶠ t in 𝓝[<] (K k).time (i k).succ, Bad k pm t) →
      ∃ (pm : ∀ k, ((K k).toHistory.stage (i k).castSucc).Carrier)
        (t : ∀ k, Icc (0 : ℝ) (K k).toHistory.horizon)
        (y' : ∀ k, ((K k).toHistory.stageAt (t k)).Carrier)
        (hat : ∀ k, aSeed k ≤ t k) (hts : ∀ k, t k ≤ σ k),
        (∀ k, Bad k (pm k) (t k)) ∧ (∀ k, HEq (y' k) (pm k)) ∧
        (∀ k, (σ k : ℝ) - t k ≤ 1 / R k) ∧
        ∀ k, ∀ (v : Icc (0 : ℝ) (K k).toHistory.horizon) (hav : aSeed k ≤ v) (hvt : v ≤ t k),
          (t k : ℝ) - (Λ k - 2) ^ 2 / R k ≤ (v : ℝ) →
          ∀ z : ((K k).toHistory.stageAt v).Carrier,
            riemannianEDistOf ((K k).toHistory.stageMetric ((K k).toHistory.activeStage v) v)
                ((seedTrace k).point ((K k).toHistory.activeStage v)
                  ((K k).toHistory.activeStage_mono hav)
                  ((K k).toHistory.activeStage_mono (hvt.trans ((hts k).trans (hsT k))))) z ≤
              riemannianEDistOf ((K k).toHistory.stageMetric ((K k).toHistory.activeStage (t k))
                  (t k))
                  ((seedTrace k).point ((K k).toHistory.activeStage (t k))
                    ((K k).toHistory.activeStage_mono (hat k))
                    ((K k).toHistory.activeStage_mono ((hts k).trans (hsT k)))) (y' k) +
                ENNReal.ofReal ((Λ k - 2) / Real.sqrt (R k)) →
            4 * R k ≤ metricScalarAt ((K k).toHistory.stageMetric
              ((K k).toHistory.activeStage v) v) z →
            (K k).toHistory.HasSpatialCanonicalTimeControl eps C1' C2' Ctime' v z := by
  obtain ⟨ε₀, hε₀, hR4⟩ := hcomp_R4_eventually_P6DP4E.{u}
  refine ⟨ε₀, hε₀, ?_⟩
  intro eps C1' C2' Ctime' K i q rec Tn aSeed σ haT hsT has p seedTrace y R Λ hR hΛ hasl hσ hf hl
    hOld hcan hacc hm hDm hseed hysc hgood Bad hbad
  choose pm wp hwp hcr hfreq using hbad
  -- good set per k: the R4 hcomp (δ = 1/√R), closeness, lateness w.r.t. aSeed and the slab start
  have hgoodset : ∀ k, ∀ᶠ t' in 𝓝[<] (K k).time (i k).succ,
      (∀ (tt : Icc (0 : ℝ) (K k).toHistory.horizon), (tt : ℝ) = t' →
        ∀ (hat : aSeed k ≤ tt) (hts : tt ≤ σ k) (yy : ((K k).toHistory.stageAt tt).Carrier),
        HEq yy (pm k) →
        riemannianEDistOf ((K k).toHistory.stageMetric ((K k).toHistory.activeStage tt) tt)
            ((seedTrace k).point ((K k).toHistory.activeStage tt)
              ((K k).toHistory.activeStage_mono hat)
              ((K k).toHistory.activeStage_mono (hts.trans (hsT k)))) yy ≤
          riemannianEDistOf ((K k).toHistory.stageMetric ((K k).toHistory.activeStage (σ k))
              (σ k))
              ((seedTrace k).point ((K k).toHistory.activeStage (σ k))
                ((K k).toHistory.activeStage_mono (has k))
                ((K k).toHistory.activeStage_mono (hsT k))) (y k) +
            ENNReal.ofReal (1 / Real.sqrt (R k))) ∧
      ((σ k : ℝ) - t' ≤ 1 / R k ∧ t' < σ k) ∧ (aSeed k : ℝ) < t' ∧
      (K k).time (i k).castSucc < t' := by
    intro k
    have hδ : 0 < 1 / Real.sqrt (R k) := by
      have := Real.sqrt_pos.mpr (hR k)
      positivity
    have h1 := hR4 (K k) (i k) (rec k) (haT k) (seedTrace k) (hf k) (hl k) (hOld k) (hcan k)
      (hacc k) (hm k) (hDm k) (hcr k) (hseed k) (hysc k (wp k) (hwp k)) hδ (σ k) (hσ k) (hsT k)
      (has k) (y k) (hwp k)
    have h2 := eventually_close_P6DP4E (s := (σ k : ℝ)) (hR k)
    rw [hσ k] at h2
    have h3 : ∀ᶠ t' in 𝓝[<] (K k).time (i k).succ, (aSeed k : ℝ) < t' :=
      Filter.mem_of_superset (Ioo_mem_nhdsLT (show (aSeed k : ℝ) < (K k).time (i k).succ from
        (hσ k) ▸ hasl k)) fun t' ht' => ht'.1
    have h4 : ∀ᶠ t' in 𝓝[<] (K k).time (i k).succ, (K k).time (i k).castSucc < t' :=
      Filter.mem_of_superset
        (Ioo_mem_nhdsLT ((K k).time_strictMono (Fin.castSucc_lt_succ (i := i k))))
        fun t' ht' => ht'.1
    filter_upwards [h1, h2, h3, h4] with t' a b c d
    refine ⟨a, ?_, c, d⟩
    rw [hσ k]
    exact b
  obtain ⟨t', ht'⟩ := exists_pick_frequently_eventually_P6DP4E hfreq hgoodset
  have hmem : ∀ k, t' k ∈ Ioo ((K k).time (i k).castSucc) ((K k).time (i k).succ) := fun k =>
    ⟨(ht' k).2.2.2.2, by rw [← hσ k]; exact (ht' k).2.2.1.2⟩
  let t : ∀ k, Icc (0 : ℝ) (K k).toHistory.horizon := fun k =>
    ⟨t' k, mem_Icc_of_mem_slab_P6DP4E (K k) (i k) (hmem k)⟩
  have hact : ∀ k, (K k).toHistory.activeStage (t k) = (i k).castSucc := fun k =>
    RetainedCoreHistory.activeStage_eq_castSucc_of_mem_P6FF (H := K k) (i k) (t k) (hmem k)
  choose y' hy' using fun k => ObservedHistory.exists_heq_stageAt_P6JW (K k).toHistory (hact k)
    (pm k)
  have hat : ∀ k, aSeed k ≤ t k := fun k => (ht' k).2.2.2.1.le
  have hts : ∀ k, t k ≤ σ k := fun k => (ht' k).2.2.1.2.le
  have hclose : ∀ k, (σ k : ℝ) - t k ≤ 1 / R k := fun k => (ht' k).2.2.1.1
  have hcomp := fun k => (ht' k).2.1 (t k) rfl (hat k) (hts k) (y' k) (hy' k)
  refine ⟨pm, t, y', hat, hts, fun k => (ht' k).1, hy', hclose, ?_⟩
  exact ObservedHistory.hgood_center_transport_seq_P6DP4D (fun k => (K k).toHistory) Tn aSeed σ t
    haT hsT has hat hts p seedTrace y y' hR hΛ hclose hgood hcomp

/-- **consumer（E1 输出 ⇒ R4 中心的 hwin′）**：`exists_R4_center_family_P6DP4E` 输出的 `σ − t ≤ 1/R`
与原中心的 `hwin`（`∀ T > 0, ∀ᶠ k, aSeed ≤ σ − T/R`）经 T2 给出 R4 中心的 `hwin′`（同理 `hT₀′`、半深度′）。 -/
example {aSeed σ t R : ℕ → ℝ} (hclose : ∀ k, σ k - t k ≤ 1 / R k)
    (hwin : ∀ T : ℝ, 0 < T → ∀ᶠ k in atTop, aSeed k ≤ σ k - T / R k) :
    ∀ T : ℝ, 0 < T → ∀ᶠ k in atTop, aSeed k ≤ t k - T / R k :=
  ObservedHistory.window_center_transport_P6DP4D hclose hwin

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
