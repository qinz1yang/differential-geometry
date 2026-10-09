import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.Kappa.KappaSeedScaleWideC11Q4b
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6SelectionP6X

/-!
# seed-window 与 selection ceiling 的分工（CX-SEEDWIN）

按 R-C11-7 D-7，`hseedWin` 是独立 construction/selection 义务。
antitone 将左端点条件展开到全部 shifted-seed window，不需 global doubling。
坏点 ceiling 重证树内 selector 的实际论证：canonical + time derivative + antitone。
它不依赖 doubling，也不能由 `hseedWin` 单独推出。现有 P6SEL 的相同 hypotheses 保持不变。
-/

set_option autoImplicit false

noncomputable section

open Set Filter DifferentialGeometry
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped Manifold ContDiff NNReal Topology

namespace GC.LongTime.Ch11

universe u

/-- 左端点的 seed-window 条件经 antitone 支付整个 shifted-seed 区间。 -/
theorem seedScale_of_seedWindow_CXCW {nr : ℝ → ℝ} (hanti : AntitoneOn nr (Ici 0))
    {Tn r : ℕ → ℝ} (hT : ∀ n, 2 * r n ^ 2 < Tn n)
    (hseedWin : ∀ᶠ n in atTop, nr (Tn n - r n ^ 2 / 2) ≤ r n) :
    ∀ᶠ n in atTop, ∀ v : ℝ, Tn n - r n ^ 2 / 2 ≤ v → v ≤ Tn n → nr v ≤ r n := by
  filter_upwards [hseedWin] with n hn
  intro v hv _
  have hleft : 0 ≤ Tn n - r n ^ 2 / 2 := by nlinarith [hT n, sq_nonneg (r n)]
  exact (hanti hleft (hleft.trans hv) hv).trans hn

/-- 若真实 native radius 在窗口两端相同，则 selection ratio 可支付 seed-window。
`hsame` 仍为显式条件；这里没有证明 P6SEL 避开 activation windows。 -/
theorem seedWindow_of_sameRadius_ratio_CXCW {nr : ℝ → ℝ} {Tn r : ℕ → ℝ}
    (hnr : ∀ n, 0 < nr (Tn n))
    (hsame : ∀ᶠ n in atTop, nr (Tn n - r n ^ 2 / 2) = nr (Tn n))
    (hratio : Tendsto (fun n => r n / nr (Tn n)) atTop atTop) :
    ∀ᶠ n in atTop, nr (Tn n - r n ^ 2 / 2) ≤ r n := by
  filter_upwards [hsame, hratio.eventually_ge_atTop 1] with n hn hr
  rw [hn]
  have h := (le_div_iff₀ (hnr n)).mp hr
  simpa using h

/-- 坏点在 top-time native threshold 以下；重证 selector 的 ceiling，不用 doubling。
空间 witness 与 time-control 两部分均显式保留，不能只用 seed-Good。 -/
theorem badPoint_scalar_le_native_CXCW (H : ObservedHistory.{u}) (q : CutoffParameters)
    {eps C1 C2 C1' C2' : ℝ} (hC1 : C1 ≤ C1') (hC2 : C2 ≤ C2')
    {Ctime Ctime' : ℝ≥0} (hCtime : Ctime ≤ Ctime')
    (hanti : AntitoneOn q.neckRadius (Ici 0))
    (hcanonical : ∀ (v : Icc (0 : ℝ) H.horizon) (z : (H.stageAt v).Carrier),
      (q.neckRadius v ^ 2)⁻¹ < metricScalarAt (H.stageMetric (H.activeStage v) v) z →
      ∃ W : Perelman.CanonicalNeighborhood.FiniteHorn.SpatialCanonicalWitness
        (H.stageMetric (H.activeStage v) v) eps C1 C2 z, W.capTubeHasNeckChart eps)
    (hderivative : ∀ (v : Icc (0 : ℝ) H.horizon) (z : (H.stageAt v).Carrier),
      H.time (H.activeStage v) < (v : ℝ) → (v : ℝ) < H.horizon →
      (q.neckRadius v ^ 2)⁻¹ < metricScalarAt (H.stageMetric (H.activeStage v) v) z →
      |derivWithin (fun t => metricScalarAt (H.stageMetric (H.activeStage v) t) z)
        (Iic (v : ℝ)) v| ≤ Ctime * metricScalarAt (H.stageMetric (H.activeStage v) v) z ^ 2)
    (T v : Icc (0 : ℝ) H.horizon) (hvT : v ≤ T) (z : (H.stageAt v).Carrier)
    (hbad : ¬ H.HasSpatialCanonicalTimeControl eps C1' C2' Ctime' v z) :
    metricScalarAt (H.stageMetric (H.activeStage v) v) z ≤ (q.neckRadius T ^ 2)⁻¹ := by
  have hlocal : metricScalarAt (H.stageMetric (H.activeStage v) v) z ≤
      (q.neckRadius v ^ 2)⁻¹ := by
    by_contra hnot
    have hhigh := lt_of_not_ge hnot
    obtain ⟨W, hW⟩ := hcanonical v z hhigh
    apply hbad
    refine ⟨⟨W.enlargeConstants hC1 hC2, hW.enlarge_constants hC1 hC2⟩, ?_⟩
    intro hage htop
    exact (hderivative v z hage htop hhigh).trans
      (mul_le_mul_of_nonneg_right (NNReal.coe_le_coe.mpr hCtime) (sq_nonneg _))
  have hrT := q.neckRadius_pos T T.2.1
  have hrv := q.neckRadius_pos v v.2.1
  have hrad : q.neckRadius T ≤ q.neckRadius v := hanti v.2.1 T.2.1 hvT
  have hsq : q.neckRadius T ^ 2 ≤ q.neckRadius v ^ 2 := by nlinarith
  exact hlocal.trans ((inv_le_inv₀ (sq_pos_of_pos hrv) (sq_pos_of_pos hrT)).mpr hsq)

/-- selection ratio 与窗口条件共同消费：坏点 ceiling 仍独立传入，且确实用于 ratio。
无 doubling；若两端 native radius 相同，两个原消费结论同时成立。 -/
theorem selection_ratio_seedWindow_CXCW {nr : ℝ → ℝ} {Tn r R : ℕ → ℝ}
    (hnr : ∀ n, 0 < nr (Tn n)) (hr : ∀ n, 0 < r n)
    (hRle : ∀ n, R n ≤ (nr (Tn n) ^ 2)⁻¹)
    (hdiv : Tendsto (fun n => r n / 200 * Real.sqrt (R n)) atTop atTop)
    (hsame : ∀ᶠ n in atTop, nr (Tn n - r n ^ 2 / 2) = nr (Tn n)) :
    Tendsto (fun n => r n / nr (Tn n)) atTop atTop ∧
      ∀ᶠ n in atTop, nr (Tn n - r n ^ 2 / 2) ≤ r n := by
  have hratio := ratio_of_selection_C11Q4b hnr hr hRle hdiv
  exact ⟨hratio, seedWindow_of_sameRadius_ratio_CXCW hnr hsame hratio⟩

end GC.LongTime.Ch11
