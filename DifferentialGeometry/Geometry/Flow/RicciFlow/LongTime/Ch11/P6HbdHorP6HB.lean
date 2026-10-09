import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6HbdStageP6HB

/-!
# hbd 的 (H°) 支：final slab 闭端点经左移重跑（O-CH11-HREST2 G2，后缀 `_P6HB`）

目标 = HREST G2 `hrestS_of_branches_P6HR` 的 **`hhor`** 槽逐字（= G3 `hbd` 槽的右析取支）：selection
前缀 + `∀ k, time last < horizon ∧ σ k = horizon` ⇒ `False`。走**左移**（lead 裁定先走），不换 history，
故无 metric / trace / seed-volume 的 transport adapter。证明链与 G1 同构：
1. 逐项局部化 = binder **`hlocH`**：final slab `[time last, horizon]` 光滑闭 slab 的闭端点 `σ = horizon`
   处坏点 ⇒ `σ` 左侧 localized fine-margin 坏点（CX-STAGE `LeftLocalizedBadAt_CXST` 形，seed distance 用
   dite 取 seed trace 点）。这是 S-c 的**无 surgery 特例**：footprint 取 `J = id`、comparison 来自闭 slab 上
   `g(t) → g(horizon)` 的 `C^k` 连续、seed 点在 final stage 内不变（seed distance 连续）；transfer 同 STAB2 G1。
2. 序列 + 左移：G1a `rerun_data_of_localized_P6HB`，左端 `lo = time last`（`< horizon = σ`）⇒ 重跑点在 final
   slab **内部**（`time last < t < horizon`），新 `hgood` 阈值 **8**。
3. fine-margin 坏 ⇒ `¬ Good η₁ C1₁ C2₁ Ctime₁`：G1 `not_good_of_not_fineMargin_P6HB`（neck 半 STAB4 G1′，
   cap / whole 半 binder `hcw`）。
4. 收口 binder **`hrerunF8`** = `hrestS_of_branches_P6HR` 的 `hfinal` 槽逐字，仅两处改动：坏点谓词
   `¬ Good η₁ C1₁ C2₁ Ctime₁` 与阈值 `8 * R k`。
显式 binder（**PROVISIONAL**）与 owner：`hlocH`（STAB 线：S-c 无 surgery 特例，`J = id` 的 footprint /
comparison / seed-distance 连续 + STAB2 G1 transfer 逆否）、`hcw`（STAB4）、`hrerunF8`（HREST `hcloseF` /
HCLOSEF `hcloseF_plus_P6HF` 与 `hgapF` 的 Cg = 8 孪生 + P6P 精度解耦）。
陈述由 build-logs/scratch/O-CH11-HREST2/mk_g2.py 从 HREST G2 binder 文本生成。
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

open Perelman.CanonicalNeighborhood.FiniteHorn

namespace ObservedHistory

/-- **(H°) 支（`hhor` 槽）⇐ 左移重跑**：见文件头。 -/
theorem hbd_hor_of_leftShift_P6HB {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {ε C1 C2 : ℝ} {Ctime : ℝ≥0}
    {ηfine C1f C2f m η₁ C1₁ C2₁ : ℝ} {Ctime₁ : ℝ≥0}
    (hη₁ : η₁ ≤ ηfine) (hηf : ηfine < 1 / 11) (hC1₁ : max C1₁ 9 ≤ C1f) (hC2₁ : C2₁ ≤ C2f)
    (hm : m ≤ 1 / 20)
    (hlocH : ∀ (nn : ℕ) (cc : ℝ) (hcc : 0 < cc),
      let H : ObservedHistory.{u} := ((F.tower.history nn).rescale_P6N cc hcc).toHistory
      ∀ (Tn aSeed : Icc (0 : ℝ) H.horizon) (haT : aSeed ≤ Tn) (pT : (H.stageAt Tn).Carrier)
        (seedTrace : BackwardPointTrace H (H.activeStage aSeed) (H.activeStage Tn)
          (H.activeStage_mono haT) pT)
        (σ : Icc (0 : ℝ) H.horizon) (hsT : σ ≤ Tn) (has : aSeed ≤ σ)
        (y : (H.stageAt σ).Carrier),
        H.time (Fin.last H.eventCount) < H.horizon → (σ : ℝ) = H.horizon → aSeed < σ →
        0 < metricScalarAt (H.stageMetric (H.activeStage σ) σ) y →
        ¬ H.HasSpatialCanonicalTimeControl ε C1 C2 Ctime σ y →
        ∀ L : ℝ, 0 < L →
        LeftLocalizedBadAt_CXST (fun t : Icc (0 : ℝ) H.horizon => (t : ℝ))
          (fun t z => ¬ ∃ W : SpatialCanonicalWitness (H.stageMetric (H.activeStage t) t)
            ηfine C1f C2f z, W.capTubeHasNeckChart ηfine ∧ W.HasMargins m)
          (fun t z => metricScalarAt (H.stageMetric (H.activeStage t) t) z)
          (fun t z => if h : aSeed ≤ t ∧ t ≤ Tn then
            riemannianEDistOf (H.stageMetric (H.activeStage t) t)
              (seedTrace.point (H.activeStage t) (H.activeStage_mono h.1)
                (H.activeStage_mono h.2)) z
            else 0)
          σ (metricScalarAt (H.stageMetric (H.activeStage σ) σ) y) L
          (riemannianEDistOf (H.stageMetric (H.activeStage σ) σ)
            (seedTrace.point (H.activeStage σ) (H.activeStage_mono has)
              (H.activeStage_mono hsT)) y))
    (hcw : ∀ (Pst : OrientedThreeStage.{u}) (gg : Pst.Metric) (x : Pst.Carrier)
      (W : SpatialCanonicalWitness gg η₁ C1₁ C2₁ x), W.capTubeHasNeckChart η₁ →
      ((∃ c d, W.alternative = .cap c d) ∨ W.domain.carrier = connectedComponent x) →
      ∃ W' : SpatialCanonicalWitness gg ηfine C1f C2f x,
        W'.capTubeHasNeckChart ηfine ∧ W'.HasMargins m)
    (hrerunF8 :
      ∀ (ind : ℕ → ℕ) (c : ℕ → ℝ) (hc : ∀ k, 0 < c k),
        let Kh : ℕ → ObservedHistory.{u} := fun k =>
          ((F.tower.history (ind k)).rescale_P6N (c k) (hc k)).toHistory
        ∀ (Tn : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (pT : ∀ k, ((Kh k).stageAt (Tn k)).Carrier),
          (∀ k : ℕ, (k : ℝ) + 1 ≤ c k * (Tn k : ℝ)) →
        ∀ (aSeed : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (haT : ∀ k, aSeed k ≤ Tn k),
          (∀ k, (aSeed k : ℝ) = (Tn k : ℝ) - 1 ^ 2) → (∀ k, 1 ≤ (aSeed k : ℝ)) →
          (∀ k, GC.LongTime.hasSmallParabolicCurvature (Kh k) (Tn k) (pT k) 1) →
        ∀ (seedTrace : ∀ k, BackwardPointTrace (Kh k) ((Kh k).activeStage (aSeed k))
            ((Kh k).activeStage (Tn k)) ((Kh k).activeStage_mono (haT k)) (pT k))
          (σ : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (y : ∀ k, ((Kh k).stageAt (σ k)).Carrier)
          (R : ℕ → ℝ) (hsT : ∀ k, σ k ≤ Tn k) (has : ∀ k, aSeed k ≤ σ k) (L : ℕ → ℝ),
          (∀ k, R k =
            metricScalarAt ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k)) (y k)) →
          (∀ k, 0 < R k) → (∀ k : ℕ, (k : ℝ) + 1 ≤ R k) →
          Tendsto L atTop atTop →
          (∀ k, ¬ (Kh k).HasSpatialCanonicalTimeControl η₁ C1₁ C2₁ Ctime₁ (σ k) (y k)) →
          (∀ k, ∀ (v : Icc (0 : ℝ) (Kh k).horizon) (hav : aSeed k ≤ v) (hvs : v ≤ σ k),
            (σ k : ℝ) - L k ^ 2 / R k ≤ (v : ℝ) →
            ∀ z : ((Kh k).stageAt v).Carrier,
              riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage v) v)
                  ((seedTrace k).point ((Kh k).activeStage v) ((Kh k).activeStage_mono hav)
                    ((Kh k).activeStage_mono (hvs.trans (hsT k)))) z ≤
                riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k))
                    ((seedTrace k).point ((Kh k).activeStage (σ k))
                      ((Kh k).activeStage_mono (has k)) ((Kh k).activeStage_mono (hsT k))) (y k) +
                  ENNReal.ofReal (L k / Real.sqrt (R k)) →
              8 * R k ≤ metricScalarAt ((Kh k).stageMetric ((Kh k).activeStage v) v) z →
              (Kh k).HasSpatialCanonicalTimeControl ε C1 C2 Ctime v z) →
          (∀ T : ℝ, 0 < T → ∀ᶠ k in atTop, (aSeed k : ℝ) ≤ σ k - T / R k) →
          (∀ T : ℝ, 0 < T → ∀ᶠ k in atTop, (Tn k : ℝ) - 1 ^ 2 / 2 ≤ (σ k : ℝ) - T / R k) →
          Tendsto (fun k => R k * ((σ k : ℝ) - ((Tn k : ℝ) - 1 ^ 2 / 2))) atTop atTop →
          Tendsto (fun k => 1 / 200 * Real.sqrt (R k)) atTop atTop →
        (∀ k, (Kh k).time (Fin.last (Kh k).eventCount) < (σ k : ℝ) ∧
          (σ k : ℝ) < (Kh k).horizon) → False) :
      ∀ (ind : ℕ → ℕ) (c : ℕ → ℝ) (hc : ∀ k, 0 < c k),
        let Kh : ℕ → ObservedHistory.{u} := fun k =>
          ((F.tower.history (ind k)).rescale_P6N (c k) (hc k)).toHistory
        ∀ (Tn : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (pT : ∀ k, ((Kh k).stageAt (Tn k)).Carrier),
          (∀ k : ℕ, (k : ℝ) + 1 ≤ c k * (Tn k : ℝ)) →
        ∀ (aSeed : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (haT : ∀ k, aSeed k ≤ Tn k),
          (∀ k, (aSeed k : ℝ) = (Tn k : ℝ) - 1 ^ 2) → (∀ k, 1 ≤ (aSeed k : ℝ)) →
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
            (σ k : ℝ) - L k ^ 2 / R k ≤ (v : ℝ) →
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
          (∀ T : ℝ, 0 < T → ∀ᶠ k in atTop, (Tn k : ℝ) - 1 ^ 2 / 2 ≤ (σ k : ℝ) - T / R k) →
          Tendsto (fun k => R k * ((σ k : ℝ) - ((Tn k : ℝ) - 1 ^ 2 / 2))) atTop atTop →
          Tendsto (fun k => 1 / 200 * Real.sqrt (R k)) atTop atTop →
        (∀ k, (Kh k).time (Fin.last (Kh k).eventCount) < (Kh k).horizon ∧
          (σ k : ℝ) = (Kh k).horizon) → False := by
  intro ind c hc Kh Tn pT hTc aSeed haT hclock h1 hsm seedTrace σ y R hsT has L hRdef hRpos hRr hL
    hsel hgood hwin hwin' hroom hradii hH
  have hloc : ∀ k, aSeed k < σ k → 0 < L k →
      LeftLocalizedBadAt_CXST (fun t : Icc (0 : ℝ) (Kh k).horizon => (t : ℝ))
        (fun t z => ¬ ∃ W : SpatialCanonicalWitness ((Kh k).stageMetric ((Kh k).activeStage t) t)
          ηfine C1f C2f z, W.capTubeHasNeckChart ηfine ∧ W.HasMargins m)
        (fun t z => metricScalarAt ((Kh k).stageMetric ((Kh k).activeStage t) t) z)
        (fun t z => if h : aSeed k ≤ t ∧ t ≤ Tn k then
          riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage t) t)
            ((seedTrace k).point ((Kh k).activeStage t) ((Kh k).activeStage_mono h.1)
              ((Kh k).activeStage_mono h.2)) z
          else 0)
        (σ k) (R k) (L k)
        (riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k))
          ((seedTrace k).point ((Kh k).activeStage (σ k)) ((Kh k).activeStage_mono (has k))
            ((Kh k).activeStage_mono (hsT k))) (y k)) := by
    intro k hak hLk
    rw [hRdef k]
    exact hlocH (ind k) (c k) (hc k) (Tn k) (aSeed k) (haT k) (pT k) (seedTrace k) (σ k) (hsT k)
      (has k) (y k) (hH k).1 (hH k).2 hak (hRdef k ▸ hRpos k) (hsel k) (L k) hLk
  have hlo : ∀ k, (Kh k).time (Fin.last (Kh k).eventCount) < σ k := fun k => by
    rw [(hH k).2]
    exact (hH k).1
  have hdat := rerun_data_of_localized_P6HB (ε := ε) (C1 := C1) (C2 := C2) (Ctime := Ctime)
    Tn aSeed haT pT seedTrace σ y R L hsT has hRpos hRr hL hgood hwin hwin' hroom
    (fun k => (Kh k).time (Fin.last (Kh k).eventCount)) hlo hloc
  choose φ hφ hφk t z R' hsT' has' hR'def hlt hbad hR'pos hR'r hgood' hwin2 hwin3 hroom' hradii'
    using hdat
  have hTc' : ∀ k : ℕ, (k : ℝ) + 1 ≤ c (φ k) * (Tn (φ k) : ℝ) := fun k => by
    have h := hTc (φ k)
    have hk : (k : ℝ) ≤ (φ k : ℝ) := by exact_mod_cast hφk k
    linarith
  exact hrerunF8 (fun k => ind (φ k)) (fun k => c (φ k)) (fun k => hc (φ k))
    (fun k => Tn (φ k)) (fun k => pT (φ k)) hTc' (fun k => aSeed (φ k)) (fun k => haT (φ k))
    (fun k => hclock (φ k)) (fun k => h1 (φ k)) (fun k => hsm (φ k)) (fun k => seedTrace (φ k))
    t z R' hsT' has' (fun k => L (φ k) / 2) hR'def hR'pos (fun k => (hR'r k).le)
    ((hL.comp hφ.tendsto_atTop).atTop_div_const two_pos)
    (fun k => not_good_of_not_fineMargin_P6HB hη₁ hηf hC1₁ hC2₁ hm hcw (hbad k))
    hgood' hwin2 hwin3 hroom' hradii'
    (fun k => ⟨(hlt k).1, (hlt k).2.trans_eq (hH (φ k)).2⟩)

end ObservedHistory

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
