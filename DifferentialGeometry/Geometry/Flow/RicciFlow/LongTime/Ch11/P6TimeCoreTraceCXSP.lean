import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6LateTimeCoreCxspP6TC
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6TraceGoodSuffixCXSP

set_option autoImplicit false

/-!
# CX-SPINE：time core 的种子半窗与已有 trace 标量控制

消费新版 `CanonicalLateTimeCore_P6X`，不另设 Good 或时间导数前提。
先取 `seedGoodWindow_of_timeCore_P6TC` 的 KG/TG，再固定
Hstar = max 4 (20000*KG)、T = 2*TG；二者先于全部 history/seed/trace queries。
Q = Hstar/r² 后，原 A*r moving footprint 内 R >= Q/2 的点具有完整 Good。

第二定理直接消费 TimeLocal:99：已有 trace B 的区间位于种子半深窗口，
只要求实际 regular 导数请求点在 R > M 时满足 moving footprint。
总预算 Ctime*M*(tau-a) 只支付一次，给同一 B 全区间 R <= 2M。
不生产 trace 存在性或 footprint；不声称 full hspine 已闭合。

-/

noncomputable section

open Set Filter DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Collapse
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped Manifold ContDiff ENNReal NNReal

namespace GC.LongTime.Ch11

universe u

/-- 新版 time core 在同一 seed 半窗生产 Q/2 阈值的完整 Good；常数先于查询。 -/
theorem seed_half_window_good_of_time_core_CXSP
    {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g}
    {ε C1 C2 : ℝ} {Ctime : ℝ≥0}
    (hcore : CanonicalLateTimeCore_P6X F ε C1 C2 Ctime) {A : ℝ} (hA : 0 < A) :
    ∃ Hstar T : ℝ, 4 ≤ Hstar ∧ 0 < T ∧
      ∀ n, let H := (F.tower.history n).toHistory
      ∀ (t : Icc (0 : ℝ) H.horizon) (p : (H.stageAt t).Carrier) (r : ℝ),
        T ≤ (t : ℝ) → 2 * r ^ 2 < (t : ℝ) → hasSmallParabolicCurvature H t p r →
        ENNReal.ofReal (A⁻¹ * r ^ 3) ≤ ballVolume (H.stageMetric (H.activeStage t) t) p r →
      ∀ (aSeed : Icc (0 : ℝ) H.horizon) (haT : aSeed ≤ t),
        (aSeed : ℝ) = (t : ℝ) - r ^ 2 →
      ∀ seedTrace : BackwardPointTrace H (H.activeStage aSeed) (H.activeStage t)
          (H.activeStage_mono haT) p,
      let Q := Hstar / r ^ 2
      ∀ (v : Icc (0 : ℝ) H.horizon) (hav : aSeed ≤ v) (hvt : v ≤ t),
        (t : ℝ) - r ^ 2 / 2 ≤ (v : ℝ) →
      ∀ y ∈ riemannianBallOf (H.stageMetric (H.activeStage v) v)
          (seedTrace.point (H.activeStage v) (H.activeStage_mono hav)
            (H.activeStage_mono hvt)) (A * r),
        Q / 2 ≤ metricScalarAt (H.stageMetric (H.activeStage v) v) y →
        H.HasSpatialCanonicalTimeControl ε C1 C2 Ctime v y := by
  obtain ⟨KG, TG, _, hTG, hbody⟩ := seedGoodWindow_of_timeCore_P6TC hcore hA
  let Hstar : ℝ := max 4 (20000 * KG)
  refine ⟨Hstar, 2 * TG, le_max_left _ _, by positivity, ?_⟩
  intro n H t p r hTt htime hsmall hvol aSeed haT hclock seedTrace Q
    v hav hvt hhalf y hy hR
  have hcoeff : 10000 * KG ≤ Hstar / 2 := by
    have hmax : 20000 * KG ≤ Hstar := le_max_right _ _
    linarith
  have hthreshold : (10000 * KG) * (r ^ 2)⁻¹ ≤ Q / 2 := by
    calc
      _ ≤ (Hstar / 2) * (r ^ 2)⁻¹ :=
        mul_le_mul_of_nonneg_right hcoeff (inv_nonneg.mpr (sq_nonneg r))
      _ = Q / 2 := by
        dsimp only [Q]
        simp only [div_eq_mul_inv]
        ring
  exact hbody n t p r hTt htime hsmall hvol aSeed haT hclock seedTrace
    v hav hvt hhalf y hy (hthreshold.trans hR)

/-- time core 对同一 history 的已有 trace 给全区间 R <= 2M。
footprint 仅在 TimeLocal 实际请求的 regular 且 R > M 的点需要。 -/
theorem seed_trace_scalar_le_two_mul_of_time_core_CXSP
    {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g}
    {ε C1 C2 : ℝ} {Ctime : ℝ≥0}
    (hcore : CanonicalLateTimeCore_P6X F ε C1 C2 Ctime) {A : ℝ} (hA : 0 < A) :
    ∃ Hstar T : ℝ, 4 ≤ Hstar ∧ 0 < T ∧
      ∀ n, let H := (F.tower.history n).toHistory
      ∀ (t : Icc (0 : ℝ) H.horizon) (p : (H.stageAt t).Carrier) (r : ℝ),
        T ≤ (t : ℝ) → 2 * r ^ 2 < (t : ℝ) → hasSmallParabolicCurvature H t p r →
        ENNReal.ofReal (A⁻¹ * r ^ 3) ≤ ballVolume (H.stageMetric (H.activeStage t) t) p r →
      ∀ (aSeed : Icc (0 : ℝ) H.horizon) (haT : aSeed ≤ t),
        (aSeed : ℝ) = (t : ℝ) - r ^ 2 →
      ∀ seedTrace : BackwardPointTrace H (H.activeStage aSeed) (H.activeStage t)
          (H.activeStage_mono haT) p,
      let Q := Hstar / r ^ 2
      ∀ (a tau : Icc (0 : ℝ) H.horizon) (has : aSeed ≤ a) (hat : a ≤ tau)
        (htaut : tau ≤ t), (t : ℝ) - r ^ 2 / 2 ≤ (a : ℝ) →
      ∀ (y : (H.stageAt tau).Carrier)
        (B : BackwardPointTrace H (H.activeStage a) (H.activeStage tau)
          (H.activeStage_mono hat) y) (M : ℝ), Q / 2 ≤ M →
        (∀ (v : Icc (0 : ℝ) H.horizon) (hav : a ≤ v) (hvt : v ≤ tau),
          H.time (H.activeStage v) < (v : ℝ) → (v : ℝ) < H.horizon →
          M < metricScalarAt (H.stageMetric (H.activeStage v) v)
            (B.point (H.activeStage v) (H.activeStage_mono hav)
              (H.activeStage_mono hvt)) →
          B.point (H.activeStage v) (H.activeStage_mono hav) (H.activeStage_mono hvt) ∈
            riemannianBallOf (H.stageMetric (H.activeStage v) v)
              (seedTrace.point (H.activeStage v) (H.activeStage_mono (has.trans hav))
                (H.activeStage_mono (hvt.trans htaut))) (A * r)) →
        metricScalarAt (H.stageMetric (H.activeStage tau) tau) y ≤ M →
        Ctime * M * ((tau : ℝ) - a) ≤ 1 / 2 →
      ∀ (v : Icc (0 : ℝ) H.horizon) (hav : a ≤ v) (hvt : v ≤ tau),
        metricScalarAt (H.stageMetric (H.activeStage v) v)
          (B.point (H.activeStage v) (H.activeStage_mono hav)
            (H.activeStage_mono hvt)) ≤ 2 * M := by
  obtain ⟨Hstar, T, hHstar, hT, hgood⟩ :=
    seed_half_window_good_of_time_core_CXSP hcore hA
  refine ⟨Hstar, T, hHstar, hT, ?_⟩
  intro n H t p r hTt htime hsmall hvol aSeed haT hclock seedTrace Q
    a tau has hat htaut hhalf y B M hQM hfoot hscalar hbudget
  have hQ : 0 < Q := div_pos (by linarith) (sq_pos_of_pos hsmall.1)
  have hM : 0 < M := (half_pos hQ).trans_le hQM
  apply B.scalar_le_two_mul_of_time_local_derivative_control hat hM
    (fun v hav hvt hage htop hR => ?_) hscalar hbudget
  have hwindow := hgood n t p r hTt htime hsmall hvol aSeed haT hclock seedTrace
    v (has.trans hav) (hvt.trans htaut)
    (hhalf.trans (show (a : ℝ) ≤ v from hav))
    (B.point (H.activeStage v) (H.activeStage_mono hav) (H.activeStage_mono hvt))
    (hfoot v hav hvt hage htop hR) (hQM.trans_lt hR).le
  exact hwindow.2 hage htop

/-- 原尺度 selected closure 的可核查 adapter：沿已有 selected → TimeCore producer，
输出统一 seed 半窗 Good。hP6 是原合同的全部 closure，仍未在本车道支付；
其局部高点 Good 来自 selector，不是把目标统一 Good 当成新假设。 -/
theorem seed_half_window_good_of_selected_CXSP {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {q : CutoffParameters} {ε C1 C2 : ℝ} {Ctime : ℝ≥0}
    (hanti : AntitoneOn q.neckRadius (Ici 0))
    (hcan : HistoryCanonicalSupply_C11S F q.neckRadius ε C1 C2)
    (hder : TimeDerivativeSupply_C11E F q.neckRadius Ctime)
    (hP6 : ∀ A : ℝ, 1 < A → ∀ (ind : ℕ → ℕ),
      let Kh : ℕ → ObservedHistory.{u} := fun k => (F.tower.history (ind k)).toHistory
      ∀ (Tn : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (pT : ∀ k, ((Kh k).stageAt (Tn k)).Carrier)
        (r : ℕ → ℝ), (∀ k, 0 < r k) → (∀ k : ℕ, (k : ℝ) + 1 ≤ (Tn k : ℝ)) →
        (∀ k, 2 * r k ^ 2 < (Tn k : ℝ)) →
        (∀ k, hasSmallParabolicCurvature (Kh k) (Tn k) (pT k) (r k)) →
        (∀ k, ENNReal.ofReal (A⁻¹ * r k ^ 3) ≤
          ballVolume ((Kh k).stageMetric ((Kh k).activeStage (Tn k)) (Tn k)) (pT k) (r k)) →
      ∀ (aSeed : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (haT : ∀ k, aSeed k ≤ Tn k),
        (∀ k, (aSeed k : ℝ) = (Tn k : ℝ) - r k ^ 2) →
      ∀ (seedTrace : ∀ k, BackwardPointTrace (Kh k) ((Kh k).activeStage (aSeed k))
          ((Kh k).activeStage (Tn k)) ((Kh k).activeStage_mono (haT k)) (pT k))
        (σ : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (y : ∀ k, ((Kh k).stageAt (σ k)).Carrier)
        (R : ℕ → ℝ) (hsT : ∀ k, σ k ≤ Tn k) (has : ∀ k, aSeed k ≤ σ k) (L : ℕ → ℝ),
        (∀ k, R k = metricScalarAt ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k)) (y k)) →
        (∀ k, 0 < R k) → (∀ k : ℕ, (k : ℝ) + 1 ≤ R k * r k ^ 2) →
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
        (∀ T : ℝ, 0 < T → ∀ᶠ k in atTop, (Tn k : ℝ) - r k ^ 2 / 2 ≤ (σ k : ℝ) - T / R k) →
        Tendsto (fun k => R k * ((σ k : ℝ) - ((Tn k : ℝ) - r k ^ 2 / 2))) atTop atTop →
        Tendsto (fun k => r k / 200 * Real.sqrt (R k)) atTop atTop → False) {A : ℝ} (hA : 0 < A) :
    ∃ Hstar T : ℝ, 4 ≤ Hstar ∧ 0 < T ∧
      ∀ n, let H := (F.tower.history n).toHistory
      ∀ (t : Icc (0 : ℝ) H.horizon) (p : (H.stageAt t).Carrier) (r : ℝ),
        T ≤ (t : ℝ) → 2 * r ^ 2 < (t : ℝ) → hasSmallParabolicCurvature H t p r →
        ENNReal.ofReal (A⁻¹ * r ^ 3) ≤ ballVolume (H.stageMetric (H.activeStage t) t) p r →
      ∀ (aSeed : Icc (0 : ℝ) H.horizon) (haT : aSeed ≤ t),
        (aSeed : ℝ) = (t : ℝ) - r ^ 2 →
      ∀ seedTrace : BackwardPointTrace H (H.activeStage aSeed) (H.activeStage t)
          (H.activeStage_mono haT) p,
      let Q := Hstar / r ^ 2
      ∀ (v : Icc (0 : ℝ) H.horizon) (hav : aSeed ≤ v) (hvt : v ≤ t),
        (t : ℝ) - r ^ 2 / 2 ≤ (v : ℝ) →
      ∀ y ∈ riemannianBallOf (H.stageMetric (H.activeStage v) v)
          (seedTrace.point (H.activeStage v) (H.activeStage_mono hav)
            (H.activeStage_mono hvt)) (A * r),
        Q / 2 ≤ metricScalarAt (H.stageMetric (H.activeStage v) v) y →
        H.HasSpatialCanonicalTimeControl ε C1 C2 Ctime v y := by
  exact seed_half_window_good_of_time_core_CXSP
    (canonicalLateTimeCore_of_selected_P6TC hanti hcan hder hP6) hA

end GC.LongTime.Ch11

end
