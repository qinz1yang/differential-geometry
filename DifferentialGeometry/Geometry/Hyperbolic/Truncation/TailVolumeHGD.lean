import DifferentialGeometry.Geometry.Hyperbolic.Truncation.DepthTowerGlobalHGD
import DifferentialGeometry.Geometry.Hyperbolic.TruncationVolume

/-!
# HG03 派生项 G3：tail-volume（S-HG-DERIV G3，后缀 `_HGD`）

输入 `exists_depth_tower_HGD` 与 donor 的 `volume_iUnion_cusp_tail`（cusp 尾部体积
`vol (cuspMap '' {a < depth}) = area * ofReal (exp (-a))`）、`volume_compl_range_inclusion`：

* `exists_truncation_tail_volume_eq_HGD`：`vol (core)ᶜ = A * ofReal (exp (-S))`，`A < ⊤`
  （`A` = 参考截断的 cusp torus 体积之和 ≤ `vol H < ⊤`）；
* `exists_truncation_tail_volume_lt_HGD`：任意 `ε > 0`，存在截断使 `vol (core)ᶜ < ε`；
* `exists_core_volume_ge_HGD`：`ofReal v ≤ vol H` ⇒ 存在核心体积 `≥ 3v/4`（ch12 HG09 用）。
-/

set_option autoImplicit false

noncomputable section

open scoped Manifold ContDiff ENNReal Topology
open Set MeasureTheory Filter GC.Endpoint

namespace DifferentialGeometry.Geometry.Hyperbolic

universe u

/-- **G3a（tail-volume 显式公式）**：存在参考截断 `Tr₀` 与 `A < ⊤`，对每个 `S ≥ 0` 有截断 `Tr`，
`vol (core)ᶜ = A * ofReal (exp (-S))`（`A` = `Tr₀` 的核心补体积 = cusp torus 体积之和）。 -/
theorem exists_truncation_tail_volume_eq_HGD (H : FiniteVolumeHyperbolicModel.{u}) :
    ∃ A : ℝ≥0∞, A < ⊤ ∧ ∀ S : ℝ, 0 ≤ S → ∃ Tr : HyperbolicTruncation H,
      Integral.Measure.riemannianVolumeMeasure (𝓡 3) H.Carrier H.metric (range Tr.inclusion)ᶜ =
        A * ENNReal.ofReal (Real.exp (-S)) := by
  obtain ⟨Tr₀, hT⟩ := exists_depth_tower_HGD H
  refine ⟨∑ i, Integral.Measure.riemannianVolumeMeasure torusModel Torus
    (Tr₀.cusp i).torusMetric univ, ?_, fun S hS => ?_⟩
  · rw [← Tr₀.volume_compl_range_inclusion]
    exact lt_of_le_of_lt (measure_mono (subset_univ _)) H.finite_volume
  · obtain ⟨Tr, hTr⟩ := hT S hS
    refine ⟨Tr, ?_⟩
    rw [hTr, Tr₀.volume_iUnion_cusp_tail (fun _ => S) (fun _ => hS), Finset.sum_mul]

/-- **G3b**：任意 `ε > 0`，存在截断使核心补的体积 `< ε`。 -/
theorem exists_truncation_tail_volume_lt_HGD (H : FiniteVolumeHyperbolicModel.{u})
    {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ Tr : HyperbolicTruncation H,
      Integral.Measure.riemannianVolumeMeasure (𝓡 3) H.Carrier H.metric (range Tr.inclusion)ᶜ <
        ε := by
  obtain ⟨A, hA, hS⟩ := exists_truncation_tail_volume_eq_HGD H
  have h1 : Tendsto (fun S : ℝ => ENNReal.ofReal (Real.exp (-S))) atTop (𝓝 0) := by
    simpa using ENNReal.tendsto_ofReal Real.tendsto_exp_neg_atTop_nhds_zero
  have h2 : Tendsto (fun S : ℝ => A * ENNReal.ofReal (Real.exp (-S))) atTop (𝓝 (A * 0)) :=
    ENNReal.Tendsto.const_mul h1 (Or.inr hA.ne)
  rw [mul_zero] at h2
  obtain ⟨S, hlt, hS0⟩ := ((h2.eventually (gt_mem_nhds hε)).and (eventually_ge_atTop 0)).exists
  obtain ⟨Tr, hTr⟩ := hS S hS0
  exact ⟨Tr, hTr ▸ hlt⟩

/-- **G3c（ch12 HG09 用的核心体积）**：`ofReal v ≤ vol H`，`0 < v` ⇒ 存在核心体积 `≥ 3v/4`。 -/
theorem exists_core_volume_ge_HGD (H : FiniteVolumeHyperbolicModel.{u}) {v : ℝ} (hv : 0 < v)
    (hvol : ENNReal.ofReal v ≤
      Integral.Measure.riemannianVolumeMeasure (𝓡 3) H.Carrier H.metric univ) :
    ∃ Tr : HyperbolicTruncation H, ENNReal.ofReal (3 * v / 4) ≤
      Integral.Measure.riemannianVolumeMeasure (𝓡 3) H.Carrier H.metric (range Tr.inclusion) := by
  obtain ⟨Tr, hTr⟩ := exists_truncation_tail_volume_lt_HGD H
    (ε := ENNReal.ofReal (v / 4)) (ENNReal.ofReal_pos.mpr (by positivity))
  refine ⟨Tr, ?_⟩
  let μ := Integral.Measure.riemannianVolumeMeasure (𝓡 3) H.Carrier H.metric
  have hsplit : μ univ ≤ μ (range Tr.inclusion) + μ (range Tr.inclusion)ᶜ := by
    calc μ univ = μ (range Tr.inclusion ∪ (range Tr.inclusion)ᶜ) := by rw [union_compl_self]
      _ ≤ _ := measure_union_le _ _
  have hle : ENNReal.ofReal v ≤ μ (range Tr.inclusion) + ENNReal.ofReal (v / 4) :=
    hvol.trans (hsplit.trans (add_le_add le_rfl hTr.le))
  have h34 : ENNReal.ofReal (3 * v / 4) = ENNReal.ofReal v - ENNReal.ofReal (v / 4) := by
    rw [← ENNReal.ofReal_sub _ (by positivity)]
    congr 1
    ring
  rw [h34, tsub_le_iff_right]
  exact hle

/-- consumer（ch12 HG09）：MGL08 的体积下界 `∃ v > 0, ∀ H, ofReal v ≤ vol H` ⇒
每个 `H` 有体积 `≥ 3v/4` 的核心。 -/
example (hMGL08 : ∃ v : ℝ, 0 < v ∧ ∀ H : FiniteVolumeHyperbolicModel.{u},
    ENNReal.ofReal v ≤ Integral.Measure.riemannianVolumeMeasure (𝓡 3) H.Carrier H.metric univ) :
    ∃ v : ℝ, 0 < v ∧ ∀ H : FiniteVolumeHyperbolicModel.{u}, ∃ Tr : HyperbolicTruncation H,
      ENNReal.ofReal (3 * v / 4) ≤
        Integral.Measure.riemannianVolumeMeasure (𝓡 3) H.Carrier H.metric (range Tr.inclusion) := by
  obtain ⟨v, hv, h⟩ := hMGL08
  exact ⟨v, hv, fun H => exists_core_volume_ge_HGD H hv (h H)⟩

end DifferentialGeometry.Geometry.Hyperbolic
