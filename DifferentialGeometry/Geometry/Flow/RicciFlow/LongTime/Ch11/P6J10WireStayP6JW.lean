import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6TerminalBCDLocalDerivP6F3

/-!
# J10WIRE G2：FOOT3 `hstayΩ` ⇐ CXJD 逐 trace `hstop` 形（索引桥，O-CH11-J10WIRE，后缀 `_P6JW`）

* `ObservedHistory.stay_of_hstop_bridge_P6JW`（PROVED，单 history）：**索引桥**。FOOT3 的 `hstayΩ` 用
  event 索引 trace `B : first → e`（`e = (i k)⁻`）、中间 stage `m`、`activeStage v = m`、`zz ≍ B.point m`；
  CXJD / CXJT0 的 `hstop` 用 activeStage 索引 trace `A : activeStage a → activeStage tt`、
  `A.point (activeStage v)`。
  桥：`activeStage tt = e`（`tt` 在 incoming slab 内部）与 `activeStage v = m` 两次 `subst`，
  取 `a := v`、`A := B.restrictFirst`（`restrictFirst.point` 按定义 = `B.point`），`zz = B.point` 由 HEq 得。
  逐 trace、逐 `v` 覆盖 `hstayΩ` 的全部量词（R-C11-17 (3)）。
* `hstayΩ_of_hstop_P6JW`（PROVED，蕴含式）：`hstopE ⇒ hstayΩ`。`hstopE` = `hstayΩ` 的前缀**逐字**
  （`∀ T r ind c … i hi, ∀ᶠ k, ∀ p′ q, y ≍ q → RegularCrossing p′ q →
  ∀ᶠ t ∈ 𝓝[<] time (i k)⁺`），体换成 CXJD 的逐 trace 形：`∀ tt (= t) ≤ σ`，
  `∀ a ∈ [t − T/R, tt]`（`aSeed ≤ a`），`∀ z′ ∈ stageAt tt`（与球 `B_t(p′, r/√R)` 中的点 HEq），
  `∀ A : activeStage a → activeStage tt, ∀ v ∈ [a, tt]`，
  `d_v(seed(v), A(v)) ≤ d_σ(seed(σ), y) + L/√R`。
* `hderivL_of_hgood_firstExit_P6JW`（PROVISIONAL，binder `hstopE`）：FOOT3 G3 `hderivL_of_hgood_P6F3`
  以 `hstayΩ_of_hstop_P6JW hstopE` 付 `hstayΩ`，结论逐字。
**`hstopE` 的 producer（repair target，PROVISIONAL）**：CXJD `hstop_of_firstExit_CXJD` 在 `σ′ := tt`
（`activeStage tt = (i k)⁻ < last`，event slab 内部，`hσlast` 自动成立）、`a := a`、`z := z′`、`A := A` 处实例化，
预算 `L′ = L/2`；另需三项：(a) 参考点跨 crossing：`d_t(seed(t), p′) ≤ d_σ(seed(σ), y) + L/(4√R)`（`t → σ⁻`，
`surgery_no_shortcut_C11D` 的 terminal 极限；`y` 与 `seed(σ)` 不在 cap window 内区由 `hscale` + 树内
`exists_not_ageZeroCapPoint_of_scalar_lt_C11G` 给）；(b) hgood 从 `(σ, y, L)` 迁移到 `(t, p′, L/2)`（区域包含）；
(c) 端点球控制 `B_t(p′, r/√R)` 上 `R ≤ Cball·R`（CXJD `hz` 前提；`hstayΩ` 前缀不含）+ CXJD binder 族
（records / `hOld` / `hcan` / ε₀ / `hscale` / Hamilton–Ivey）在 `hstayΩ` 同一量化层（∀ ind c …，逐 k）。
**R-C11-17 对账**：(1)/(2) 同 G1（CXJD 链两端整球 Ric、`E_cross = 0`）；(3) 量词——桥逐 trace、逐 `v`
覆盖（`a := v`），`hstopE` 的量词层（∀ 起点 a、∀ z′、∀ A、∀ v）与 CXJD `hstop_of_firstExit_CXJD` 的结论层相同。
-/

set_option autoImplicit false

noncomputable section

open Set Filter Function
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open DifferentialGeometry.Geometry.Collapse
open scoped Manifold NNReal Topology ContDiff ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

/-- **索引桥（`_P6JW`，PROVED）**：activeStage 索引的逐 trace `hstop`（`tt` 处、起点 `a ≥ lo`）⇒ event 索引
trace `B : first → e`（`activeStage tt = e`）在 `activeStage v = m`、`zz ≍ B.point m` 处的同一距离界。 -/
theorem ObservedHistory.stay_of_hstop_bridge_P6JW (H : ObservedHistory.{u})
    {Tn aSeed σ : Icc (0 : ℝ) H.horizon} (haT : aSeed ≤ Tn) (hsT : σ ≤ Tn)
    {pT : (H.stageAt Tn).Carrier}
    (seedTrace : BackwardPointTrace H (H.activeStage aSeed) (H.activeStage Tn)
      (H.activeStage_mono haT) pT)
    (Bd : ℝ≥0∞) (lo : ℝ) {tt : Icc (0 : ℝ) H.horizon} (htσ : tt ≤ σ)
    {e : Fin (H.eventCount + 1)} (he : H.activeStage tt = e) (Pz : (H.stage e).Carrier → Prop)
    (hstop : ∀ (a : Icc (0 : ℝ) H.horizon) (haS : aSeed ≤ a) (hat : a ≤ tt), lo ≤ (a : ℝ) →
      ∀ z' : (H.stageAt tt).Carrier, (∀ z : (H.stage e).Carrier, HEq z' z → Pz z) →
      ∀ (A : BackwardPointTrace H (H.activeStage a) (H.activeStage tt) (H.activeStage_mono hat) z')
        (v : Icc (0 : ℝ) H.horizon) (hav : a ≤ v) (hvt : v ≤ tt),
        riemannianEDistOf (H.stageMetric (H.activeStage v) v)
          (seedTrace.point (H.activeStage v) (H.activeStage_mono (haS.trans hav))
            (H.activeStage_mono ((hvt.trans htσ).trans hsT)))
          (A.point (H.activeStage v) (H.activeStage_mono hav) (H.activeStage_mono hvt)) ≤ Bd)
    {first : Fin (H.eventCount + 1)} (hfl : first ≤ e) (z : (H.stage e).Carrier) (hz : Pz z)
    (B : BackwardPointTrace H first e hfl z) (m : Fin (H.eventCount + 1)) (hf : first ≤ m)
    (hm : m ≤ e) (v : Icc (0 : ℝ) H.horizon) (hav : aSeed ≤ v) (hvt : v ≤ tt)
    (hlo : lo ≤ (v : ℝ)) (hvm : H.activeStage v = m) (zz : (H.stageAt v).Carrier)
    (hzz : HEq zz (B.point m hf hm)) :
    riemannianEDistOf (H.stageMetric (H.activeStage v) v)
      (seedTrace.point (H.activeStage v) (H.activeStage_mono hav)
        (H.activeStage_mono ((hvt.trans htσ).trans hsT))) zz ≤ Bd := by
  subst he
  subst hvm
  have hzz' : zz = B.point (H.activeStage v) hf hm := eq_of_heq hzz
  subst hzz'
  exact hstop v hav hvt hlo z (fun z'' h => (eq_of_heq h) ▸ hz) (B.restrictFirst hf hm) v le_rfl
    hvt

/-- **`hstopE ⇒ hstayΩ`（`_P6JW`，PROVED）**：前缀逐字；`t` 取在 incoming slab 内部（`Ioo_mem_nhdsLT`），
`tt := ⟨t, _, _⟩`，`activeStage tt = (i k)⁻`，逐点调用索引桥。 -/
theorem hstayΩ_of_hstop_P6JW {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {ε C1 C2 : ℝ} {Ctime : ℝ≥0}
    (hstopE :
      ∀ (T r : ℝ), 0 < T → 0 < r →
      ∀ (ind : ℕ → ℕ) (c : ℕ → ℝ) (hc : ∀ k, 0 < c k),
        let Kh : ℕ → ObservedHistory.{u} := fun k =>
          ((F.tower.history (ind k)).rescale_P6N (c k) (hc k)).toHistory
        ∀ (Tn : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (pT : ∀ k, ((Kh k).stageAt (Tn k)).Carrier),
          (∀ k : ℕ, (k : ℝ) + 1 ≤ c k * (Tn k : ℝ)) →
        ∀ (aSeed : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (haT : ∀ k, aSeed k ≤ Tn k),
          (∀ k, (aSeed k : ℝ) = (Tn k : ℝ) - 1 ^ (2 : ℕ)) → (∀ k, 1 ≤ (aSeed k : ℝ)) →
          (∀ k, GC.LongTime.hasSmallParabolicCurvature (Kh k) (Tn k) (pT k) 1) →
        ∀ (seedTrace : ∀ k, BackwardPointTrace (Kh k) ((Kh k).activeStage (aSeed k))
            ((Kh k).activeStage (Tn k)) ((Kh k).activeStage_mono (haT k)) (pT k))
          (σ : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (y : ∀ k, ((Kh k).stageAt (σ k)).Carrier)
          (R : ℕ → ℝ) (hsT : ∀ k, σ k ≤ Tn k) (has : ∀ k, aSeed k ≤ σ k) (L : ℕ → ℝ),
          (∀ k, R k =
            metricScalarAt ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k)) (y k)) →
          (∀ k, 0 < R k) → (∀ k : ℕ, (k : ℝ) + 1 ≤ R k) →
          Tendsto L atTop atTop →
          (∀ k, ¬ (Kh k).HasSpatialCanonicalTimeControl ε C1 C2 Ctime (σ k) (y k)) →
          (∀ k, ∀ (v : Icc (0 : ℝ) (Kh k).horizon) (hav : aSeed k ≤ v) (hvs : v ≤ σ k),
            (σ k : ℝ) - L k ^ (2 : ℕ) / R k ≤ (v : ℝ) →
            ∀ z : ((Kh k).stageAt v).Carrier,
              riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage v) v)
                  ((seedTrace k).point ((Kh k).activeStage v) ((Kh k).activeStage_mono hav)
                    ((Kh k).activeStage_mono (hvs.trans (hsT k)))) z ≤
                riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k))
                    ((seedTrace k).point ((Kh k).activeStage (σ k))
                      ((Kh k).activeStage_mono (has k)) ((Kh k).activeStage_mono (hsT k))) (y k) +
                  ENNReal.ofReal (L k / Real.sqrt (R k)) →
              4 * R k ≤ metricScalarAt ((Kh k).stageMetric ((Kh k).activeStage v) v) z →
              (Kh k).HasSpatialCanonicalTimeControl ε C1 C2 Ctime v z) →
          (∀ T : ℝ, 0 < T → ∀ᶠ k in atTop, (aSeed k : ℝ) ≤ σ k - T / R k) →
          (∀ T : ℝ, 0 < T → ∀ᶠ k in atTop, (Tn k : ℝ) - 1 ^ (2 : ℕ) / 2 ≤ (σ k : ℝ) - T / R k) →
          Tendsto (fun k => R k * ((σ k : ℝ) - ((Tn k : ℝ) - 1 ^ (2 : ℕ) / 2))) atTop atTop →
          Tendsto (fun k => 1 / 200 * Real.sqrt (R k)) atTop atTop →
        ∀ i : ∀ k, Fin (Kh k).eventCount, (∀ k, (σ k : ℝ) = (Kh k).time (i k).succ) →
        ∀ᶠ k in atTop, ∀ (p' : ((Kh k).stage (i k).castSucc).Carrier)
          (q : ((Kh k).stage (i k).succ).Carrier), HEq (y k) q →
          ((Kh k).event (i k)).RegularCrossing p' q →
          ∀ᶠ t in 𝓝[<] (Kh k).time (i k).succ,
            ∀ (tt : Icc (0 : ℝ) (Kh k).horizon), (tt : ℝ) = t → ∀ (htσ : tt ≤ σ k)
              (a : Icc (0 : ℝ) (Kh k).horizon) (haS' : aSeed k ≤ a) (hat : a ≤ tt),
              t - T / R k ≤ (a : ℝ) →
            ∀ z' : ((Kh k).stageAt tt).Carrier,
              (∀ z : ((Kh k).stage (i k).castSucc).Carrier, HEq z' z →
                z ∈ riemannianBallOf (((Kh k).event (i k)).incoming.flow.base.metric t) p'
                  (r / Real.sqrt (R k))) →
            ∀ (A : BackwardPointTrace (Kh k) ((Kh k).activeStage a) ((Kh k).activeStage tt)
                ((Kh k).activeStage_mono hat) z')
              (v : Icc (0 : ℝ) (Kh k).horizon) (hav : a ≤ v) (hvt : v ≤ tt),
              riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage v) v)
                  ((seedTrace k).point ((Kh k).activeStage v)
                    ((Kh k).activeStage_mono (haS'.trans hav))
                    ((Kh k).activeStage_mono ((hvt.trans htσ).trans (hsT k))))
                  (A.point ((Kh k).activeStage v) ((Kh k).activeStage_mono hav)
                    ((Kh k).activeStage_mono hvt)) ≤
                riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k))
                    ((seedTrace k).point ((Kh k).activeStage (σ k))
                      ((Kh k).activeStage_mono (has k)) ((Kh k).activeStage_mono (hsT k))) (y k) +
                  ENNReal.ofReal (L k / Real.sqrt (R k))) :
      ∀ (T r : ℝ), 0 < T → 0 < r →
      ∀ (ind : ℕ → ℕ) (c : ℕ → ℝ) (hc : ∀ k, 0 < c k),
        let Kh : ℕ → ObservedHistory.{u} := fun k =>
          ((F.tower.history (ind k)).rescale_P6N (c k) (hc k)).toHistory
        ∀ (Tn : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (pT : ∀ k, ((Kh k).stageAt (Tn k)).Carrier),
          (∀ k : ℕ, (k : ℝ) + 1 ≤ c k * (Tn k : ℝ)) →
        ∀ (aSeed : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (haT : ∀ k, aSeed k ≤ Tn k),
          (∀ k, (aSeed k : ℝ) = (Tn k : ℝ) - 1 ^ (2 : ℕ)) → (∀ k, 1 ≤ (aSeed k : ℝ)) →
          (∀ k, GC.LongTime.hasSmallParabolicCurvature (Kh k) (Tn k) (pT k) 1) →
        ∀ (seedTrace : ∀ k, BackwardPointTrace (Kh k) ((Kh k).activeStage (aSeed k))
            ((Kh k).activeStage (Tn k)) ((Kh k).activeStage_mono (haT k)) (pT k))
          (σ : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (y : ∀ k, ((Kh k).stageAt (σ k)).Carrier)
          (R : ℕ → ℝ) (hsT : ∀ k, σ k ≤ Tn k) (has : ∀ k, aSeed k ≤ σ k) (L : ℕ → ℝ),
          (∀ k, R k =
            metricScalarAt ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k)) (y k)) →
          (∀ k, 0 < R k) → (∀ k : ℕ, (k : ℝ) + 1 ≤ R k) →
          Tendsto L atTop atTop →
          (∀ k, ¬ (Kh k).HasSpatialCanonicalTimeControl ε C1 C2 Ctime (σ k) (y k)) →
          (∀ k, ∀ (v : Icc (0 : ℝ) (Kh k).horizon) (hav : aSeed k ≤ v) (hvs : v ≤ σ k),
            (σ k : ℝ) - L k ^ (2 : ℕ) / R k ≤ (v : ℝ) →
            ∀ z : ((Kh k).stageAt v).Carrier,
              riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage v) v)
                  ((seedTrace k).point ((Kh k).activeStage v) ((Kh k).activeStage_mono hav)
                    ((Kh k).activeStage_mono (hvs.trans (hsT k)))) z ≤
                riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k))
                    ((seedTrace k).point ((Kh k).activeStage (σ k))
                      ((Kh k).activeStage_mono (has k)) ((Kh k).activeStage_mono (hsT k))) (y k) +
                  ENNReal.ofReal (L k / Real.sqrt (R k)) →
              4 * R k ≤ metricScalarAt ((Kh k).stageMetric ((Kh k).activeStage v) v) z →
              (Kh k).HasSpatialCanonicalTimeControl ε C1 C2 Ctime v z) →
          (∀ T : ℝ, 0 < T → ∀ᶠ k in atTop, (aSeed k : ℝ) ≤ σ k - T / R k) →
          (∀ T : ℝ, 0 < T → ∀ᶠ k in atTop, (Tn k : ℝ) - 1 ^ (2 : ℕ) / 2 ≤ (σ k : ℝ) - T / R k) →
          Tendsto (fun k => R k * ((σ k : ℝ) - ((Tn k : ℝ) - 1 ^ (2 : ℕ) / 2))) atTop atTop →
          Tendsto (fun k => 1 / 200 * Real.sqrt (R k)) atTop atTop →
        ∀ i : ∀ k, Fin (Kh k).eventCount, (∀ k, (σ k : ℝ) = (Kh k).time (i k).succ) →
        ∀ᶠ k in atTop, ∀ (p' : ((Kh k).stage (i k).castSucc).Carrier)
          (q : ((Kh k).stage (i k).succ).Carrier), HEq (y k) q →
          ((Kh k).event (i k)).RegularCrossing p' q →
          ∀ᶠ t in 𝓝[<] (Kh k).time (i k).succ,
            ∀ (first : Fin ((Kh k).eventCount + 1)) (hfl : first ≤ (i k).castSucc),
            ∀ z ∈ riemannianBallOf (((Kh k).event (i k)).incoming.flow.base.metric t) p'
                (r / Real.sqrt (R k)),
            ∀ (B : BackwardPointTrace (Kh k) first (i k).castSucc hfl z)
              (m : Fin ((Kh k).eventCount + 1)) (hf : first ≤ m) (hm : m ≤ (i k).castSucc)
              (v : Icc (0 : ℝ) (Kh k).horizon) (hav : aSeed k ≤ v) (hvs : v ≤ σ k),
              t - T / R k ≤ (v : ℝ) → (v : ℝ) ≤ t → (Kh k).activeStage v = m →
            ∀ zz : ((Kh k).stageAt v).Carrier, HEq zz (B.point m hf hm) →
              riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage v) v)
                  ((seedTrace k).point ((Kh k).activeStage v) ((Kh k).activeStage_mono hav)
                    ((Kh k).activeStage_mono (hvs.trans (hsT k)))) zz ≤
                riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k))
                    ((seedTrace k).point ((Kh k).activeStage (σ k))
                      ((Kh k).activeStage_mono (has k)) ((Kh k).activeStage_mono (hsT k))) (y k) +
                  ENNReal.ofReal (L k / Real.sqrt (R k)) := by
  intro T r hT hr ind c hc Kh Tn pT hTc aSeed haT hclock hone hsm seedTrace σ y R hsT has L hRdef
    hRpos hRr hL hsel hgood haS hTnS hroom hradii i hi
  filter_upwards [hstopE T r hT hr ind c hc Tn pT hTc aSeed haT hclock hone hsm seedTrace σ y R hsT
    has L hRdef hRpos hRr hL hsel hgood haS hTnS hroom hradii i hi] with k hk
  intro p' q hq hcross
  have hcs : (Kh k).time (i k).castSucc < (Kh k).time (i k).succ :=
    (Kh k).time_strictMono Fin.castSucc_lt_succ
  filter_upwards [hk p' q hq hcross, Ioo_mem_nhdsLT hcs] with t ht hti
  intro first hfl z hz B m hf hm v hav hvs hlo hvt hvm zz hzz
  have ht0 : 0 ≤ t := ((Kh k).time_nonneg _).trans hti.1.le
  have htσ' : t ≤ (σ k : ℝ) := by
    rw [hi k]
    exact hti.2.le
  let tt : Icc (0 : ℝ) (Kh k).horizon := ⟨t, ht0, htσ'.trans (σ k).2.2⟩
  have htσ : tt ≤ σ k := htσ'
  have he : (Kh k).activeStage tt = (i k).castSucc :=
    (Kh k).activeStage_eq_of_mem_slab_P6F3 (i k) tt hti.1.le hti.2
  exact (Kh k).stay_of_hstop_bridge_P6JW (haT k) (hsT k) (seedTrace k) _ (t - T / R k) htσ he
    (fun z => z ∈ riemannianBallOf (((Kh k).event (i k)).incoming.flow.base.metric t) p'
      (r / Real.sqrt (R k))) (ht tt rfl htσ) hfl z hz B m hf hm v hav hvt hlo hvm zz hzz

/-- **G2（`_P6JW`，PROVISIONAL：binder `hstopE`）**：FOOT3 G3 `hderivL_of_hgood_P6F3` 以
`hstayΩ_of_hstop_P6JW hstopE` 付 `hstayΩ`；结论逐字（`Cg := 4`、`Cder := Ctime`）。 -/
theorem hderivL_of_hgood_firstExit_P6JW {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {ε C1 C2 : ℝ} {Ctime : ℝ≥0}
    (hstopE :
      ∀ (T r : ℝ), 0 < T → 0 < r →
      ∀ (ind : ℕ → ℕ) (c : ℕ → ℝ) (hc : ∀ k, 0 < c k),
        let Kh : ℕ → ObservedHistory.{u} := fun k =>
          ((F.tower.history (ind k)).rescale_P6N (c k) (hc k)).toHistory
        ∀ (Tn : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (pT : ∀ k, ((Kh k).stageAt (Tn k)).Carrier),
          (∀ k : ℕ, (k : ℝ) + 1 ≤ c k * (Tn k : ℝ)) →
        ∀ (aSeed : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (haT : ∀ k, aSeed k ≤ Tn k),
          (∀ k, (aSeed k : ℝ) = (Tn k : ℝ) - 1 ^ (2 : ℕ)) → (∀ k, 1 ≤ (aSeed k : ℝ)) →
          (∀ k, GC.LongTime.hasSmallParabolicCurvature (Kh k) (Tn k) (pT k) 1) →
        ∀ (seedTrace : ∀ k, BackwardPointTrace (Kh k) ((Kh k).activeStage (aSeed k))
            ((Kh k).activeStage (Tn k)) ((Kh k).activeStage_mono (haT k)) (pT k))
          (σ : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (y : ∀ k, ((Kh k).stageAt (σ k)).Carrier)
          (R : ℕ → ℝ) (hsT : ∀ k, σ k ≤ Tn k) (has : ∀ k, aSeed k ≤ σ k) (L : ℕ → ℝ),
          (∀ k, R k =
            metricScalarAt ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k)) (y k)) →
          (∀ k, 0 < R k) → (∀ k : ℕ, (k : ℝ) + 1 ≤ R k) →
          Tendsto L atTop atTop →
          (∀ k, ¬ (Kh k).HasSpatialCanonicalTimeControl ε C1 C2 Ctime (σ k) (y k)) →
          (∀ k, ∀ (v : Icc (0 : ℝ) (Kh k).horizon) (hav : aSeed k ≤ v) (hvs : v ≤ σ k),
            (σ k : ℝ) - L k ^ (2 : ℕ) / R k ≤ (v : ℝ) →
            ∀ z : ((Kh k).stageAt v).Carrier,
              riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage v) v)
                  ((seedTrace k).point ((Kh k).activeStage v) ((Kh k).activeStage_mono hav)
                    ((Kh k).activeStage_mono (hvs.trans (hsT k)))) z ≤
                riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k))
                    ((seedTrace k).point ((Kh k).activeStage (σ k))
                      ((Kh k).activeStage_mono (has k)) ((Kh k).activeStage_mono (hsT k))) (y k) +
                  ENNReal.ofReal (L k / Real.sqrt (R k)) →
              4 * R k ≤ metricScalarAt ((Kh k).stageMetric ((Kh k).activeStage v) v) z →
              (Kh k).HasSpatialCanonicalTimeControl ε C1 C2 Ctime v z) →
          (∀ T : ℝ, 0 < T → ∀ᶠ k in atTop, (aSeed k : ℝ) ≤ σ k - T / R k) →
          (∀ T : ℝ, 0 < T → ∀ᶠ k in atTop, (Tn k : ℝ) - 1 ^ (2 : ℕ) / 2 ≤ (σ k : ℝ) - T / R k) →
          Tendsto (fun k => R k * ((σ k : ℝ) - ((Tn k : ℝ) - 1 ^ (2 : ℕ) / 2))) atTop atTop →
          Tendsto (fun k => 1 / 200 * Real.sqrt (R k)) atTop atTop →
        ∀ i : ∀ k, Fin (Kh k).eventCount, (∀ k, (σ k : ℝ) = (Kh k).time (i k).succ) →
        ∀ᶠ k in atTop, ∀ (p' : ((Kh k).stage (i k).castSucc).Carrier)
          (q : ((Kh k).stage (i k).succ).Carrier), HEq (y k) q →
          ((Kh k).event (i k)).RegularCrossing p' q →
          ∀ᶠ t in 𝓝[<] (Kh k).time (i k).succ,
            ∀ (tt : Icc (0 : ℝ) (Kh k).horizon), (tt : ℝ) = t → ∀ (htσ : tt ≤ σ k)
              (a : Icc (0 : ℝ) (Kh k).horizon) (haS' : aSeed k ≤ a) (hat : a ≤ tt),
              t - T / R k ≤ (a : ℝ) →
            ∀ z' : ((Kh k).stageAt tt).Carrier,
              (∀ z : ((Kh k).stage (i k).castSucc).Carrier, HEq z' z →
                z ∈ riemannianBallOf (((Kh k).event (i k)).incoming.flow.base.metric t) p'
                  (r / Real.sqrt (R k))) →
            ∀ (A : BackwardPointTrace (Kh k) ((Kh k).activeStage a) ((Kh k).activeStage tt)
                ((Kh k).activeStage_mono hat) z')
              (v : Icc (0 : ℝ) (Kh k).horizon) (hav : a ≤ v) (hvt : v ≤ tt),
              riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage v) v)
                  ((seedTrace k).point ((Kh k).activeStage v)
                    ((Kh k).activeStage_mono (haS'.trans hav))
                    ((Kh k).activeStage_mono ((hvt.trans htσ).trans (hsT k))))
                  (A.point ((Kh k).activeStage v) ((Kh k).activeStage_mono hav)
                    ((Kh k).activeStage_mono hvt)) ≤
                riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k))
                    ((seedTrace k).point ((Kh k).activeStage (σ k))
                      ((Kh k).activeStage_mono (has k)) ((Kh k).activeStage_mono (hsT k))) (y k) +
                  ENNReal.ofReal (L k / Real.sqrt (R k))) :
      ∀ (T r : ℝ), 0 < T → 0 < r →
      ∀ (ind : ℕ → ℕ) (c : ℕ → ℝ) (hc : ∀ k, 0 < c k),
        let Kh : ℕ → ObservedHistory.{u} := fun k =>
          ((F.tower.history (ind k)).rescale_P6N (c k) (hc k)).toHistory
        ∀ (Tn : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (pT : ∀ k, ((Kh k).stageAt (Tn k)).Carrier),
          (∀ k : ℕ, (k : ℝ) + 1 ≤ c k * (Tn k : ℝ)) →
        ∀ (aSeed : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (haT : ∀ k, aSeed k ≤ Tn k),
          (∀ k, (aSeed k : ℝ) = (Tn k : ℝ) - 1 ^ (2 : ℕ)) → (∀ k, 1 ≤ (aSeed k : ℝ)) →
          (∀ k, GC.LongTime.hasSmallParabolicCurvature (Kh k) (Tn k) (pT k) 1) →
        ∀ (seedTrace : ∀ k, BackwardPointTrace (Kh k) ((Kh k).activeStage (aSeed k))
            ((Kh k).activeStage (Tn k)) ((Kh k).activeStage_mono (haT k)) (pT k))
          (σ : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (y : ∀ k, ((Kh k).stageAt (σ k)).Carrier)
          (R : ℕ → ℝ) (hsT : ∀ k, σ k ≤ Tn k) (has : ∀ k, aSeed k ≤ σ k) (L : ℕ → ℝ),
          (∀ k, R k =
            metricScalarAt ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k)) (y k)) →
          (∀ k, 0 < R k) → (∀ k : ℕ, (k : ℝ) + 1 ≤ R k) →
          Tendsto L atTop atTop →
          (∀ k, ¬ (Kh k).HasSpatialCanonicalTimeControl ε C1 C2 Ctime (σ k) (y k)) →
          (∀ k, ∀ (v : Icc (0 : ℝ) (Kh k).horizon) (hav : aSeed k ≤ v) (hvs : v ≤ σ k),
            (σ k : ℝ) - L k ^ (2 : ℕ) / R k ≤ (v : ℝ) →
            ∀ z : ((Kh k).stageAt v).Carrier,
              riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage v) v)
                  ((seedTrace k).point ((Kh k).activeStage v) ((Kh k).activeStage_mono hav)
                    ((Kh k).activeStage_mono (hvs.trans (hsT k)))) z ≤
                riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k))
                    ((seedTrace k).point ((Kh k).activeStage (σ k))
                      ((Kh k).activeStage_mono (has k)) ((Kh k).activeStage_mono (hsT k))) (y k) +
                  ENNReal.ofReal (L k / Real.sqrt (R k)) →
              4 * R k ≤ metricScalarAt ((Kh k).stageMetric ((Kh k).activeStage v) v) z →
              (Kh k).HasSpatialCanonicalTimeControl ε C1 C2 Ctime v z) →
          (∀ T : ℝ, 0 < T → ∀ᶠ k in atTop, (aSeed k : ℝ) ≤ σ k - T / R k) →
          (∀ T : ℝ, 0 < T → ∀ᶠ k in atTop, (Tn k : ℝ) - 1 ^ (2 : ℕ) / 2 ≤ (σ k : ℝ) - T / R k) →
          Tendsto (fun k => R k * ((σ k : ℝ) - ((Tn k : ℝ) - 1 ^ (2 : ℕ) / 2))) atTop atTop →
          Tendsto (fun k => 1 / 200 * Real.sqrt (R k)) atTop atTop →
        ∀ i : ∀ k, Fin (Kh k).eventCount, (∀ k, (σ k : ℝ) = (Kh k).time (i k).succ) →
        ∀ᶠ k in atTop, ∀ (p' : ((Kh k).stage (i k).castSucc).Carrier)
          (q : ((Kh k).stage (i k).succ).Carrier), HEq (y k) q →
          ((Kh k).event (i k)).RegularCrossing p' q →
          ∀ᶠ t in 𝓝[<] (Kh k).time (i k).succ,
            (∀ (first : Fin ((Kh k).eventCount + 1)) (hfl : first ≤ (i k).castSucc),
              ∀ z ∈ riemannianBallOf (((Kh k).event (i k)).incoming.flow.base.metric t) p'
                  (r / Real.sqrt (R k)),
              ∀ (B : BackwardPointTrace (Kh k) first (i k).castSucc hfl z)
                (i' : Fin (Kh k).eventCount) (hf : first ≤ i'.castSucc)
                (hij : i'.castSucc < (i k).castSucc),
              ∀ v' ∈ Ioo ((Kh k).time i'.castSucc) ((Kh k).time i'.succ), t - T / R k ≤ v' →
                4 * R k < ((Kh k).event i').incoming.flow.scalar v'
                  (B.point i'.castSucc hf hij.le) →
                |derivWithin (fun w' => ((Kh k).event i').incoming.flow.scalar w'
                    (B.point i'.castSucc hf hij.le)) (Iic v') v'| ≤
                  Ctime * ((Kh k).event i').incoming.flow.scalar v'
                    (B.point i'.castSucc hf hij.le) ^ 2) ∧
            ∀ z ∈ riemannianBallOf (((Kh k).event (i k)).incoming.flow.base.metric t) p'
                (r / Real.sqrt (R k)),
              ∀ v' ∈ Ioo ((Kh k).time (i k).castSucc) t, t - T / R k ≤ v' →
                4 * R k < ((Kh k).event (i k)).incoming.flow.scalar v' z →
                |derivWithin (fun w' => ((Kh k).event (i k)).incoming.flow.scalar w' z)
                    (Iic v') v'| ≤
                  Ctime * ((Kh k).event (i k)).incoming.flow.scalar v' z ^ 2 :=
  hderivL_of_hgood_P6F3 (hstayΩ_of_hstop_P6JW hstopE)

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
