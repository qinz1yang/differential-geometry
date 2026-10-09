import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspP1.NeckBandSigmaNK2
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspP1.SurgerySepWindowSG2

/-!
# G4 的 consumer：切割球面 `Σ_b` 的 `hcut` 形状（S-W-NECK-2，后缀 `_NK2`）

`not_mem_level_sphere_of_slice_post_NK2`（`(a, b) = (σ_b, 51)`，`a Z − b = z_s − 50`）经 G2
`neckSlab_fifty_eq_level_NK2` 与 TOPGLUE 的 `carrierHomeo` 搬运，给 SURGERY-2 / IMS06 用的形状：
`postStage F.observation s` 上开盘内光滑、`q(∂D)` 与 band `{|σ_b Z − 51| < 20}` 的闭包不交、满足 IMS05′
（显式参数）的盘 `q` 不碰 `e_s '' Σ_b`（`e_s = sliceHomeo_SG2`）。`d` 对 retained boundary 一致。
-/

set_option autoImplicit false
noncomputable section
open Set Manifold Filter
open DifferentialGeometry DifferentialGeometry.Geometry DifferentialGeometry.Topology
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology GC.LongTime
open scoped Manifold ContDiff Topology
namespace GC.LongTime.CuspP1
universe u

/-- **切割球面的 IMS06′（`hcut` 形状）**：`R.delta b.1.1 ≤ 1/40000`、`hcol : δ_s⁻¹ > 100`。
`s ∈ [τ₀ − d, τ₀)`，`q(∂D)` 与 band `{|σ_b · Z − 51| < 20}`（`= {|z_s − 50| < 20}`）的闭包不交且满足
IMS05′（`postSliceMetric_TG` 下）的开盘内光滑盘不碰 `e_s '' Σ_b`。 -/
theorem not_mem_cut_sphere_of_slice_post_NK2 {P : OrientedThreeStage.{u}} {g : P.Metric}
    (F : GC.Interface.RawSurgery P g) (n : ℕ)
    (i : Fin (F.tower.history n).toHistory.eventCount) {p : CutoffParameters}
    (R : GeometricCutoffRecord (F.tower.history n).toHistory i p)
    (hcol : ∀ b : ((F.tower.history n).toHistory.event i).RetainedBoundaryIndex,
      100 < ((R.static b).delta)⁻¹)
    (hδ : ∀ b : ((F.tower.history n).toHistory.event i).RetainedBoundaryIndex,
      R.delta b.1.1 ≤ 1 / 40000) :
    ∃ d : ℝ, 0 < d ∧ ∀ (s : ℝ) (hs0 : 0 ≤ s) (hsh : s ≤ (F.tower.history n).toHistory.horizon)
      (hact : (F.tower.history n).toHistory.activeStage ⟨s, hs0, hsh⟩ = i.castSucc)
      (h0 : (F.tower.history n).toHistory.time i.castSucc ≤ s),
      (F.tower.history n).toHistory.time i.succ - d ≤ s →
      ∀ h1 : s < (F.tower.history n).toHistory.time i.succ,
      ∀ b : ((F.tower.history n).toHistory.event i).RetainedBoundaryIndex,
      ∀ q : C(closedDisk, (postStage F.observation s).Carrier),
        DiskSmoothInterior (E := ThreeSpace) q →
        (∀ θ : loopCircle, diskTrace q θ ∉
          closure {x : (postStage F.observation s).Carrier |
            x ∈ Set.range (postSliceChart_TG F n (R.backward b.1.1) h0 h1) ∧
              |retainedSign_NK2 b * postSliceHeight_TG F n (R.backward b.1.1) h0 h1 x - 51| <
                20}) →
        (∀ (z₀ : ℂ) (ρ : ℝ), z₀ ∈ Metric.ball (0 : ℂ) 1 → 0 < ρ →
          IsCompact {z : ℂ | z ∈ Metric.ball (0 : ℂ) 1 ∧
            diskEDist_NK (postSliceMetric_TG F n (R.backward b.1.1) s) q z₀ z ≤
              ENNReal.ofReal ρ} →
          (∃ z ∈ Metric.ball (0 : ℂ) 1,
            diskEDist_NK (postSliceMetric_TG F n (R.backward b.1.1) s) q z₀ z =
              ENNReal.ofReal ρ) →
          (∀ z ∈ Metric.ball (0 : ℂ) 1,
            diskEDist_NK (postSliceMetric_TG F n (R.backward b.1.1) s) q z₀ z ≤
              ENNReal.ofReal ρ →
            ∀ᶠ w in 𝓝 z, 1 / 2 ≤
              metricScalarAt (postSliceMetric_TG F n (R.backward b.1.1) s)
                (diskExtension q w)) →
          ρ ≤ 2 * Real.pi * Real.sqrt (2 / (3 * (1 / 2)))) →
        ∀ ζ : closedDisk, q ζ ∉ sliceHomeo_SG2 F.observation n i s hs0 hsh hact ''
          neckSlab_SG2 R b {50} := by
  have hex : ∀ b : ((F.tower.history n).toHistory.event i).RetainedBoundaryIndex,
      ∃ d : ℝ, 0 < d ∧ ∀ (s : ℝ) (h0 : (F.tower.history n).toHistory.time i.castSucc ≤ s),
      (F.tower.history n).toHistory.time i.succ - d ≤ s →
      ∀ h1 : s < (F.tower.history n).toHistory.time i.succ,
      ∀ a b' : ℝ, a * a = 1 → |b'| + 20 ≤ (R.delta b.1.1)⁻¹ →
      ∀ q : C(closedDisk, (postStage F.observation s).Carrier),
        DiskSmoothInterior (E := ThreeSpace) q →
        (∀ θ : loopCircle, diskTrace q θ ∉
          closure {x : (postStage F.observation s).Carrier |
            x ∈ Set.range (postSliceChart_TG F n (R.backward b.1.1) h0 h1) ∧
              |a * postSliceHeight_TG F n (R.backward b.1.1) h0 h1 x - b'| < 20}) →
        (∀ (z₀ : ℂ) (ρ : ℝ), z₀ ∈ Metric.ball (0 : ℂ) 1 → 0 < ρ →
          IsCompact {z : ℂ | z ∈ Metric.ball (0 : ℂ) 1 ∧
            diskEDist_NK (postSliceMetric_TG F n (R.backward b.1.1) s) q z₀ z ≤
              ENNReal.ofReal ρ} →
          (∃ z ∈ Metric.ball (0 : ℂ) 1,
            diskEDist_NK (postSliceMetric_TG F n (R.backward b.1.1) s) q z₀ z =
              ENNReal.ofReal ρ) →
          (∀ z ∈ Metric.ball (0 : ℂ) 1,
            diskEDist_NK (postSliceMetric_TG F n (R.backward b.1.1) s) q z₀ z ≤
              ENNReal.ofReal ρ →
            ∀ᶠ w in 𝓝 z, 1 / 2 ≤
              metricScalarAt (postSliceMetric_TG F n (R.backward b.1.1) s)
                (diskExtension q w)) →
          ρ ≤ 2 * Real.pi * Real.sqrt (2 / (3 * (1 / 2)))) →
        ∀ ζ : closedDisk, ¬ (q ζ ∈ Set.range (postSliceChart_TG F n (R.backward b.1.1) h0 h1) ∧
          a * postSliceHeight_TG F n (R.backward b.1.1) h0 h1 (q ζ) - b' = 0) :=
    fun b => not_mem_level_sphere_of_slice_post_NK2 F n (R.backward b.1.1)
      (R.two_le_order_NK b.1.1) (hδ b)
  choose d hd hlevel using hex
  obtain ⟨d₀, hd₀, hle⟩ := exists_pos_le_of_finite_NK2 d hd
  refine ⟨d₀, hd₀, fun s hs0 hsh hact h0 hs1 h1 b q hq htrace hIMS05 ζ => ?_⟩
  have hδb : (40000 : ℝ) ≤ (R.delta b.1.1)⁻¹ := by
    have hpos := R.delta_pos b.1.1
    rw [le_inv_comm₀ (by norm_num) hpos]
    simpa using hδ b
  have hsb : (F.tower.history n).toHistory.time i.succ - d b ≤ s := by linarith [hle b]
  have hnot := hlevel b s h0 hsb h1 (retainedSign_NK2 b) 51 (retainedSign_mul_self_NK2 b)
    (by rw [abs_of_pos (by norm_num : (0 : ℝ) < 51)]; linarith) q hq htrace hIMS05 ζ
  rintro ⟨x, hx, hxq⟩
  obtain ⟨hxr, hxl⟩ := (neckSlab_fifty_eq_level_NK2 R b
    (by linarith [hcol b])).subset hx
  have hcancel : carrierHomeo_CPD2 (postStage_eq_castSucc_TG F n i h0 h1)
      (sliceHomeo_SG2 F.observation n i s hs0 hsh hact x) = x :=
    carrierHomeo_cancel_TG (postStage_eq_castSucc_TG F n i h0 h1) x
  refine hnot ⟨?_, ?_⟩
  · rw [← hxq, range_postSliceChart_TG, mem_preimage, hcancel]
    exact hxr
  · rw [← hxq, postSliceHeight_apply_TG, hcancel]
    exact hxl

end GC.LongTime.CuspP1
