import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6SeedComponentCXSP
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6SeedScaleP6A
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6SeedArithmeticCXSP
import Mathlib.Order.Filter.AtTopBot.Field

/-!
# CX-SPINE：原 scalar 坏点序列的实际 last-crossing anchor

在原 history 的同一 compact stage 上，原 p 到 x 的 smooth minimizing segment 由
connected-component producer 产生，再在同一段上取最后一次 Q = Hbase/r² crossing。
完整尾段仍在原 A*r 球内；归一化端点距离严格小于 A*sqrt(Hbase)。
序列只取 i ↦ i+N 的尾列，H、t、p、x、r 均保持同源。端点 scalar/Q 发散直接产生
固定 normalized ball 的 scalar failure，不借用 P6(b) 的 non-Good 序列。

最后的 volume lemma 只把同一个 seed 的数值下界由 A 换成 Awork≥A；它不扩大
任何 hw(A) 结论或改变原球 footprint。若后续 TimeCore 在 Awork 使用该下界，
必须显式给出 A≤Awork；first-level escape 仍须支付自己的 buffer 与半径 fit。
-/

set_option autoImplicit false
noncomputable section

open Set Filter DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Collapse
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open GC.GeneralFlow
open scoped Manifold ContDiff Topology ENNReal

namespace GC.LongTime.Ch11

universe u

/-- 从实际 small seed 与坏点生产同一 smooth minimizing segment 的最后等高点。 -/
theorem exists_seed_scalar_anchor_CXSP
    {H : ObservedHistory.{u}} {t : Icc (0 : ℝ) H.horizon}
    {p x : (H.stageAt t).Carrier} {A r Hbase : ℝ}
    (hA : 0 < A) (hHbase : 4 ≤ Hbase)
    (hsmall : hasSmallParabolicCurvature H t p r)
    (hx : x ∈ riemannianBallOf (H.stageMetric (H.activeStage t) t) p (A * r))
    (hhigh : Hbase * (r ^ 2)⁻¹ < metricScalarAt (H.stageMetric (H.activeStage t) t) x) :
    let g := H.stageMetric (H.activeStage t) t
    let Q := Hbase * (r ^ 2)⁻¹
    let hQ : 0 < Q := mul_pos (by linarith only [hHbase])
      (inv_pos.mpr (sq_pos_of_pos hsmall.1))
    ∃ (L : ℝ) (γ : ℝ → (H.stageAt t).Carrier) (s : ℝ),
      0 ≤ L ∧ L < A * r ∧ γ 0 = p ∧ γ L = x ∧
      ContMDiff 𝓘(ℝ, ℝ) ThreeModel ∞ γ ∧
      (∀ v, γ v ∈ connectedComponent p) ∧
      (∀ a ∈ Icc (0 : ℝ) L, ∀ b ∈ Icc (0 : ℝ) L,
        riemannianEDistOf g (γ a) (γ b) = ENNReal.ofReal |a - b|) ∧
      s ∈ Ioo (0 : ℝ) L ∧ metricScalarAt g (γ s) = Q ∧
      γ s ∈ riemannianBallOf g p (A * r) ∧
      (∀ w ∈ Icc (0 : ℝ) L, metricScalarAt g (γ w) = Q → w ≤ s) ∧
      (∀ v ∈ Icc (0 : ℝ) (L - s),
        γ (s + v) ∈ riemannianBallOf g p (A * r) ∧ Q ≤ metricScalarAt g (γ (s + v))) ∧
      (∀ v ∈ Ioc (0 : ℝ) (L - s), Q < metricScalarAt g (γ (s + v))) ∧
      riemannianEDistOf g (γ s) x = ENNReal.ofReal (L - s) ∧ L - s < A * r ∧
      riemannianEDistOf (scaleMetric Q hQ g) (γ s) x <
        ENNReal.ofReal (A * Real.sqrt Hbase) ∧
      metricScalarAt g x / Q = metricScalarAt g x * r ^ 2 / Hbase := by
  intro g Q hQ
  have hr : 0 < r := hsmall.1
  have hH : 0 < Hbase := by linarith only [hHbase]
  have hi : 0 < (r ^ 2)⁻¹ := inv_pos.mpr (sq_pos_of_pos hr)
  have hpball : p ∈ riemannianBallOf g p r := by
    change riemannianEDistOf g p p < ENNReal.ofReal r
    rw [riemannianEDistOf_self]
    exact ENNReal.ofReal_pos.mpr hr
  have hpR : metricScalarAt g p ≤ 3 * (r ^ 2)⁻¹ :=
    (le_abs_self _).trans (hasSmallParabolicCurvature_scalar_abs_le_C11S hsmall hpball)
  have hseed : metricScalarAt g p < Q := hpR.trans_lt
    (mul_lt_mul_of_pos_right (by linarith only [hHbase]) hi)
  have hpx : p ≠ x := by
    intro heq
    rw [heq] at hseed
    exact (hseed.trans hhigh).false
  obtain ⟨L, γ, hL, hlen, hstart, hend, hsmooth, hcomp, hdist⟩ :=
    exists_seed_segment_of_compact_CXSP g p x hx hpx
  obtain ⟨s, hs, hanchor, hlast, hclosed, hopen, hdistend, hshort, _htaildist⟩ :=
    exists_scalar_high_tail_on_segment_CXSP g hsmooth.continuous.continuousOn
      hL hlen hdist (by simpa only [hstart] using hseed)
      (by simpa only [hend] using hhigh)
  have hfoot (v : ℝ) (hv : v ∈ Icc (0 : ℝ) (L - s)) :
      γ (s + v) ∈ riemannianBallOf g p (A * r) ∧
        Q ≤ metricScalarAt g (γ (s + v)) := by
    simpa only [hstart] using hclosed v hv
  have hanchorBall : γ s ∈ riemannianBallOf g p (A * r) := by
    simpa only [add_zero] using (hfoot 0 ⟨le_rfl, sub_nonneg.mpr hs.2.le⟩).1
  have hdistx : riemannianEDistOf g (γ s) x = ENNReal.ofReal (L - s) := by
    simpa only [hend] using hdistend
  refine ⟨L, γ, s, hL, hlen, hstart, hend, hsmooth, hcomp, hdist, hs, hanchor,
    hanchorBall, hlast, hfoot, hopen, hdistx, hshort, ?_, ?_⟩
  · rw [edistOf_scale, hdistx, ← ENNReal.ofReal_mul (Real.sqrt_nonneg Q)]
    apply (ENNReal.ofReal_lt_ofReal_iff (mul_pos hA (Real.sqrt_pos.mpr hH))).mpr
    calc
      Real.sqrt Q * (L - s) < Real.sqrt Q * (A * r) :=
        mul_lt_mul_of_pos_left hshort (Real.sqrt_pos.mpr hQ)
      _ = A * Real.sqrt Hbase := by
        dsimp only [Q]
        rw [sqrt_seed_scale_CXSP hH hr]
        field_simp [hr.ne']
  · dsimp only [Q]
    field_simp [hH.ne', hr.ne']

/-- 原 history 序列的尾列产生指定阈值 anchor、原球内的完整尾段与实际 scalar failure。 -/
theorem exists_scalar_anchor_sequence_CXSP
    (H : ℕ → ObservedHistory.{u})
    (t : ∀ i, Icc (0 : ℝ) (H i).horizon)
    (p x : ∀ i, ((H i).stageAt (t i)).Carrier) (r : ℕ → ℝ)
    {A Hbase : ℝ} (hA : 0 < A) (hHbase : 4 ≤ Hbase)
    (hsmall : ∀ i, hasSmallParabolicCurvature (H i) (t i) (p i) (r i))
    (hx : ∀ i, x i ∈ riemannianBallOf
      ((H i).stageMetric ((H i).activeStage (t i)) (t i)) (p i) (A * r i))
    (hbad : Tendsto (fun i => metricScalarAt
      ((H i).stageMetric ((H i).activeStage (t i)) (t i)) (x i) * r i ^ 2) atTop atTop) :
    ∃ N : ℕ,
      let φ : ℕ → ℕ := fun i => i + N
      StrictMono φ ∧ ∃ anchor : ∀ i, ((H (φ i)).stageAt (t (φ i))).Carrier,
      let g := fun i => (H (φ i)).stageMetric ((H (φ i)).activeStage (t (φ i))) (t (φ i))
      let Q := fun i => Hbase * (r (φ i) ^ 2)⁻¹
      let hQ : ∀ i, 0 < Q i := fun i => mul_pos (by linarith only [hHbase])
        (inv_pos.mpr (sq_pos_of_pos (hsmall (φ i)).1))
      (∀ i, metricScalarAt (g i) (anchor i) = Q i) ∧
      (∀ i, riemannianEDistOf (g i) (p (φ i)) (anchor i) ≤ ENNReal.ofReal (A * r (φ i))) ∧
      (∀ i, ∃ (L : ℝ) (γ : ℝ → ((H (φ i)).stageAt (t (φ i))).Carrier) (s : ℝ),
        0 ≤ L ∧ L < A * r (φ i) ∧ γ 0 = p (φ i) ∧ γ L = x (φ i) ∧
        ContMDiff 𝓘(ℝ, ℝ) ThreeModel ∞ γ ∧
        (∀ v, γ v ∈ connectedComponent (p (φ i))) ∧
        (∀ a ∈ Icc (0 : ℝ) L, ∀ b ∈ Icc (0 : ℝ) L,
          riemannianEDistOf (g i) (γ a) (γ b) = ENNReal.ofReal |a - b|) ∧
        s ∈ Ioo (0 : ℝ) L ∧ γ s = anchor i ∧
        (∀ w ∈ Icc (0 : ℝ) L, metricScalarAt (g i) (γ w) = Q i → w ≤ s) ∧
        (∀ v ∈ Icc (0 : ℝ) (L - s),
          γ (s + v) ∈ riemannianBallOf (g i) (p (φ i)) (A * r (φ i)) ∧
            Q i ≤ metricScalarAt (g i) (γ (s + v))) ∧
        (∀ v ∈ Ioc (0 : ℝ) (L - s), Q i < metricScalarAt (g i) (γ (s + v))) ∧
        riemannianEDistOf (g i) (anchor i) (x (φ i)) = ENNReal.ofReal (L - s) ∧
        L - s < A * r (φ i)) ∧
      (∀ i, riemannianEDistOf (scaleMetric (Q i) (hQ i) (g i)) (anchor i) (x (φ i)) <
        ENNReal.ofReal (A * Real.sqrt Hbase)) ∧
      (∀ i, metricScalarAt (g i) (x (φ i)) / Q i =
        metricScalarAt (g i) (x (φ i)) * r (φ i) ^ 2 / Hbase) ∧
      Tendsto (fun i => metricScalarAt (g i) (x (φ i)) / Q i) atTop atTop ∧
      ∃ R : ℝ, 0 < R ∧ R + 2 ≤ A * Real.sqrt Hbase + 3 ∧
        ¬ ∃ B : ℝ, ∀ᶠ i in atTop, ∀ z : ((H (φ i)).stageAt (t (φ i))).Carrier,
          riemannianEDistOf (scaleMetric (Q i) (hQ i) (g i)) (anchor i) z <
            ENNReal.ofReal R → metricScalarAt (g i) z / Q i ≤ B := by
  have hH : 0 < Hbase := by linarith only [hHbase]
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hbad.eventually_gt_atTop Hbase)
  refine ⟨N, ?_⟩
  intro φ
  have hφ : StrictMono φ := fun i j hij => Nat.add_lt_add_right hij N
  have hhigh (i : ℕ) : Hbase * (r (φ i) ^ 2)⁻¹ <
      metricScalarAt ((H (φ i)).stageMetric ((H (φ i)).activeStage (t (φ i)))
        (t (φ i))) (x (φ i)) := by
    rw [← div_eq_mul_inv]
    exact (div_lt_iff₀ (sq_pos_of_pos (hsmall (φ i)).1)).mpr
      (hN (φ i) (Nat.le_add_left N i))
  have hgeom := fun i => exists_seed_scalar_anchor_CXSP hA hHbase
    (hsmall (φ i)) (hx (φ i)) (hhigh i)
  choose L γ s hL hlen hstart hend hsmooth hcomp hdist hs hanchor hanchorBall hlast
    hclosed hopen hdistend hshort hnorm hratio using hgeom
  refine ⟨hφ, fun i => γ i (s i), ?_⟩
  intro g Q hQ
  have hlim : Tendsto (fun i => metricScalarAt (g i) (x (φ i)) / Q i) atTop atTop := by
    have heq : (fun i => metricScalarAt (g i) (x (φ i)) / Q i) =
        fun i => metricScalarAt (g i) (x (φ i)) * r (φ i) ^ 2 / Hbase := funext hratio
    rw [heq]
    exact (hbad.comp hφ.tendsto_atTop).atTop_div_const hH
  refine ⟨hanchor, (fun i => (hanchorBall i).le), ?_, hnorm, hratio, hlim, ?_⟩
  · intro i
    exact ⟨L i, γ i, s i, hL i, hlen i, hstart i, hend i, hsmooth i, hcomp i, hdist i,
      hs i, rfl, hlast i, hclosed i, hopen i, hdistend i, hshort i⟩
  · refine ⟨A * Real.sqrt Hbase + 1, by positivity, by linarith, ?_⟩
    rintro ⟨B, hB⟩
    obtain ⟨i, hi, hRi⟩ := (hB.and (hlim.eventually_gt_atTop B)).exists
    have hxR : riemannianEDistOf (scaleMetric (Q i) (hQ i) (g i))
        (γ i (s i)) (x (φ i)) < ENNReal.ofReal (A * Real.sqrt Hbase + 1) :=
      (hnorm i).trans_le (ENNReal.ofReal_le_ofReal (by linarith))
    exact (hi (x (φ i)) hxR).not_gt hRi

/-- Awork≥A 只减小同一个 seed 的 volume 下界；不扩大任何空间结论。 -/
theorem seed_volume_of_parameter_le_CXSP
    {H : ObservedHistory.{u}} {t : Icc (0 : ℝ) H.horizon}
    {p : (H.stageAt t).Carrier} {r A Awork : ℝ}
    (hsmall : hasSmallParabolicCurvature H t p r) (hA : 0 < A) (hAA : A ≤ Awork)
    (hvol : ENNReal.ofReal (A⁻¹ * r ^ 3) ≤
      ballVolume (H.stageMetric (H.activeStage t) t) p r) :
    ENNReal.ofReal (Awork⁻¹ * r ^ 3) ≤
      ballVolume (H.stageMetric (H.activeStage t) t) p r := by
  apply le_trans (ENNReal.ofReal_le_ofReal ?_) hvol
  exact mul_le_mul_of_nonneg_right ((inv_le_inv₀ (hA.trans_le hAA) hA).mpr hAA)
    (pow_nonneg hsmall.1.le 3)

end GC.LongTime.Ch11
