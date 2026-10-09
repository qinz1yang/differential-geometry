import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6LeftShiftCoreP6HB
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6FineMarginImproveP6ST4
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6HrestBoundaryP6HR

/-!
# hbd 的 (S) 支：stage 时刻类经左移重跑（O-CH11-HREST2 G1，后缀 `_P6HB`）

目标 = HREST G2 `hrestS_of_branches_P6HR` 的 **`hstage`** 槽逐字（= G3 `hbd` 槽的左析取支）：selection
前缀 + `∀ k, ∃ i, σ k = time i.succ` ⇒ `False`。证明链（全部本车道证出，剩显式 binder 见下）：
1. 逐项局部化（`stage_localizedBad_P6HB`，G1a）：post-cover 的 cap 支由 **`hcapW`** 收口；crossing 支由
   **`hfoot`**（STAB2 footprint 合同）+ STAB2 G1 transfer 逆否 + **`hcen`**（种子中心位移）⇒
   `LeftLocalizedBadAt_CXST`（fine-margin 坏，曲率比任意接近 1，seed-distance 余量 `L/(4√R)`）。
2. 序列 + 左移（`rerun_data_of_localized_P6HB`，G1a）：子列 `φ`、CX-STAGE localized 序列、P6BND2
   `leftShift_rerun_P6S2`（新 `hgood` 阈值 **8**、窗口 `L/2`）、新窗口条件；重跑点在 event `i (φ k)` 内部。
3. fine-margin 坏 ⇒ `¬ Good η₁ C1₁ C2₁ Ctime₁`（`not_good_of_not_fineMargin_P6HB`）：neck 型由 STAB4 G1′
   `fineGood_implies_fineMarginGood_P6ST4` 付（margins `1/20`）；cap / whole-component 型留 binder
   **`hcw`**。
4. 收口 binder **`hrerunE8`** = `hrestS_of_branches_P6HR` 的 `hev` 槽逐字，仅两处改动：坏点谓词
   `¬ Good η₁ C1₁ C2₁ Ctime₁`（Good 区仍 `(ε, C1, C2, Ctime)`，精度解耦）与阈值 `8 * R k`。
显式 binder（**PROVISIONAL**）与 owner：`hcapW`（HCAPW `hcapW_of_standardClose_P6CW`；records 存在性一并
在此 binder）、`hfoot`（STAB3 `nonempty_footprintData_of_scalarBound_P6ST3` 的 terminal 曲率界 `hL`，
R-C11-8 Q3）、`hcen`（seed 距离沿 crossing 的左半连续，新，无 owner）、`hcw`（STAB4：cap 深度余量 BLOCKED、
positive/round 走 OPEN-C）、`hrerunE8`（P6CG Cg 化收口 `false_of_selection_eventSlab_lateHI_closed_Cg_P6S3`
已有；缺 P6SEL2 G1a / `hgapN` / P6SEL3 evb 的 Cg = 8 化 + P6P 精度解耦）。
陈述由 build-logs/scratch/O-CH11-HREST2/mk_g1.py 从 HREST G2 binder 文本生成。
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

/-- **fine-margin 坏 ⇒ `¬ Good η₁`**：neck 型 witness 由 STAB4 G1′
`fineGood_implies_fineMarginGood_P6ST4` 改善成 fine-margin witness（与坏点矛盾）；
cap / whole-component 型由 binder `hcw` 改善。 -/
theorem not_good_of_not_fineMargin_P6HB {H : ObservedHistory.{u}}
    {ηfine C1f C2f m η₁ C1₁ C2₁ : ℝ} {Ctime₁ : ℝ≥0}
    (hη₁ : η₁ ≤ ηfine) (hηf : ηfine < 1 / 11) (hC1₁ : max C1₁ 9 ≤ C1f) (hC2₁ : C2₁ ≤ C2f)
    (hm : m ≤ 1 / 20)
    (hcw : ∀ (Pst : OrientedThreeStage.{u}) (gg : Pst.Metric) (x : Pst.Carrier)
      (W : SpatialCanonicalWitness gg η₁ C1₁ C2₁ x), W.capTubeHasNeckChart η₁ →
      ((∃ c d, W.alternative = .cap c d) ∨ W.domain.carrier = connectedComponent x) →
      ∃ W' : SpatialCanonicalWitness gg ηfine C1f C2f x,
        W'.capTubeHasNeckChart ηfine ∧ W'.HasMargins m)
    {t : Icc (0 : ℝ) H.horizon} {z : (H.stageAt t).Carrier}
    (hbad : ¬ ∃ W : SpatialCanonicalWitness (H.stageMetric (H.activeStage t) t) ηfine C1f C2f z,
      W.capTubeHasNeckChart ηfine ∧ W.HasMargins m) :
    ¬ H.HasSpatialCanonicalTimeControl η₁ C1₁ C2₁ Ctime₁ t z := by
  intro hg
  rcases fineGood_implies_fineMarginGood_P6ST4 hη₁ hηf hC1₁ hC2₁ hm hg.1 with h | ⟨W, hW, hcap⟩
  · exact hbad h
  · exact hbad (hcw _ _ _ W hW hcap)

/-- **(S) 支（`hstage` 槽）⇐ 左移重跑**：见文件头。 -/
theorem hbd_stage_of_leftShift_P6HB {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {ε C1 C2 : ℝ} {Ctime : ℝ≥0}
    {ηfine C1f C2f m η₁ C1₁ C2₁ : ℝ} {kk : ℕ} {Ctime₁ : ℝ≥0}
    (hC1f : 2 * C1f ≤ C1) (hC2f : 1000 * C2f ≤ C2) (hle : ηfine ≤ neckModelTolerance (ε / 2))
    (hη₁ : η₁ ≤ ηfine) (hηf : ηfine < 1 / 11) (hC1₁ : max C1₁ 9 ≤ C1f) (hC2₁ : C2₁ ≤ C2f)
    (hm : m ≤ 1 / 20)
    (hcapW : ∀ (nn : ℕ) (cc : ℝ) (hcc : 0 < cc),
      let H : ObservedHistory.{u} := ((F.tower.history nn).rescale_P6N cc hcc).toHistory
      ∀ i : Fin H.eventCount, ∃ (pp : CutoffParameters) (Rc : GeometricCutoffRecord H i pp),
        ∀ (b : (H.event i).RetainedBoundaryIndex) (x : ThreeBall),
          ∃ W : SpatialCanonicalWitness (H.event i).outputMetric ε C1 C2
            ((Rc.static b).inclusion ((Rc.static b).witness.cap x)), W.capTubeHasNeckChart ε)
    (hfoot : ∀ (nn : ℕ) (cc : ℝ) (hcc : 0 < cc),
      let H : ObservedHistory.{u} := ((F.tower.history nn).rescale_P6N cc hcc).toHistory
      ∀ (i : Fin H.eventCount) (σ : Icc (0 : ℝ) H.horizon) (y : (H.stageAt σ).Carrier),
        (σ : ℝ) = H.time i.succ → ¬ H.HasSpatialCanonicalTimeControl ε C1 C2 Ctime σ y →
        ∀ (p' : (H.stage i.castSucc).Carrier) (q : (H.stage i.succ).Carrier), HEq y q →
          (H.event i).RegularCrossing p' q →
          Nonempty ((H.event i).BufferedFootprintData_P6ST2 p' q ε C1f C2f m kk))
    (hcen : ∀ (nn : ℕ) (cc : ℝ) (hcc : 0 < cc),
      let H : ObservedHistory.{u} := ((F.tower.history nn).rescale_P6N cc hcc).toHistory
      ∀ (Tn aSeed : Icc (0 : ℝ) H.horizon) (haT : aSeed ≤ Tn) (pT : (H.stageAt Tn).Carrier)
        (seedTrace : BackwardPointTrace H (H.activeStage aSeed) (H.activeStage Tn)
          (H.activeStage_mono haT) pT)
        (i : Fin H.eventCount) (σ : Icc (0 : ℝ) H.horizon) (hsT : σ ≤ Tn) (has : aSeed ≤ σ)
        (y : (H.stageAt σ).Carrier), (σ : ℝ) = H.time i.succ →
        ¬ H.HasSpatialCanonicalTimeControl ε C1 C2 Ctime σ y →
        ∀ (p' : (H.stage i.castSucc).Carrier) (q : (H.stage i.succ).Carrier), HEq y q →
        ∀ (D : (H.event i).BufferedFootprintData_P6ST2 p' q ε C1f C2f m kk) (η : ℝ), 0 < η →
        ∀ᶠ n in atTop, ∀ (t : Icc (0 : ℝ) H.horizon) (z : (H.stageAt t).Carrier),
          (t : ℝ) = D.v n → HEq z p' → ∀ (hav : aSeed ≤ t) (hvt : t ≤ Tn),
          riemannianEDistOf (H.stageMetric (H.activeStage t) t)
              (seedTrace.point (H.activeStage t) (H.activeStage_mono hav)
                (H.activeStage_mono hvt)) z ≤
            riemannianEDistOf (H.stageMetric (H.activeStage σ) σ)
                (seedTrace.point (H.activeStage σ) (H.activeStage_mono has)
                  (H.activeStage_mono hsT)) y +
              ENNReal.ofReal η)
    (hcw : ∀ (Pst : OrientedThreeStage.{u}) (gg : Pst.Metric) (x : Pst.Carrier)
      (W : SpatialCanonicalWitness gg η₁ C1₁ C2₁ x), W.capTubeHasNeckChart η₁ →
      ((∃ c d, W.alternative = .cap c d) ∨ W.domain.carrier = connectedComponent x) →
      ∃ W' : SpatialCanonicalWitness gg ηfine C1f C2f x,
        W'.capTubeHasNeckChart ηfine ∧ W'.HasMargins m)
    (hrerunE8 :
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
        (∀ k, ∃ j : Fin (Kh k).eventCount, (Kh k).time j.castSucc < (σ k : ℝ) ∧
          (σ k : ℝ) < (Kh k).time j.succ) → (∀ k : ℕ, (k : ℝ) + 1 < R k) → False) :
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
        (∀ k, ∃ i : Fin (Kh k).eventCount, (σ k : ℝ) = (Kh k).time i.succ) → False := by
  intro ind c hc Kh Tn pT hTc aSeed haT hclock h1 hsm seedTrace σ y R hsT has L hRdef hRpos hRr hL
    hsel hgood hwin hwin' hroom hradii hS
  choose i hi using hS
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
    have hW := hcapW (ind k) (c k) (hc k) (i k)
    choose pp Rc hW using hW
    rw [hRdef k]
    exact Rc.stage_localizedBad_P6HB hC1f hC2f hle hW (haT k) (seedTrace k) (hsT k) (has k) (y k)
      (hi k) hak (hRdef k ▸ hRpos k) hLk
      (hfoot (ind k) (c k) (hc k) (i k) (σ k) (y k) (hi k) (hsel k))
      (hcen (ind k) (c k) (hc k) (Tn k) (aSeed k) (haT k) (pT k) (seedTrace k) (i k) (σ k)
        (hsT k) (has k) (y k) (hi k) (hsel k))
      (hsel k)
  have hlo : ∀ k, (Kh k).time (i k).castSucc < σ k := fun k => by
    rw [hi k]
    exact (Kh k).time_strictMono (Fin.castSucc_lt_succ (i := i k))
  have hdat := rerun_data_of_localized_P6HB (ε := ε) (C1 := C1) (C2 := C2) (Ctime := Ctime)
    Tn aSeed haT pT seedTrace σ y R L hsT has hRpos hRr hL hgood hwin hwin' hroom
    (fun k => (Kh k).time (i k).castSucc) hlo hloc
  choose φ hφ hφk t z R' hsT' has' hR'def hlt hbad hR'pos hR'r hgood' hwin2 hwin3 hroom' hradii'
    using hdat
  have hTc' : ∀ k : ℕ, (k : ℝ) + 1 ≤ c (φ k) * (Tn (φ k) : ℝ) := fun k => by
    have h := hTc (φ k)
    have hk : (k : ℝ) ≤ (φ k : ℝ) := by exact_mod_cast hφk k
    linarith
  exact hrerunE8 (fun k => ind (φ k)) (fun k => c (φ k)) (fun k => hc (φ k))
    (fun k => Tn (φ k)) (fun k => pT (φ k)) hTc' (fun k => aSeed (φ k)) (fun k => haT (φ k))
    (fun k => hclock (φ k)) (fun k => h1 (φ k)) (fun k => hsm (φ k)) (fun k => seedTrace (φ k))
    t z R' hsT' has' (fun k => L (φ k) / 2) hR'def hR'pos (fun k => (hR'r k).le)
    ((hL.comp hφ.tendsto_atTop).atTop_div_const two_pos)
    (fun k => not_good_of_not_fineMargin_P6HB hη₁ hηf hC1₁ hC2₁ hm hcw (hbad k))
    hgood' hwin2 hwin3 hroom' hradii'
    (fun k => ⟨i (φ k), (hlt k).1, (hlt k).2.trans_eq (hi (φ k))⟩) hR'r

end ObservedHistory

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
