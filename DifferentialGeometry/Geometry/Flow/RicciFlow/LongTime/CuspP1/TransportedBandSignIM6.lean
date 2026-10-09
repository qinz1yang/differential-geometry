import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspP1.TransportedBandIM6

/-!
# ⑧ 的只用符号版（O-W-IMS06 G7，后缀 `_IM6`）

S-W-TOPGLUE G2 把 NECK G5 的 band 估计搬到 postStage 时，度量是归一化的 slice 度量
`postSliceMetric_TG = scaleMetric (r²)⁻¹ (postMetric s)`，所以 band 上只有
`R_post = r⁻² R_slice ≥ (3/5) r⁻² > 0`，不是 `R_post ≥ 1/2`。⑧ 的论证只用符号：
collar 上 `R_post < 0`、band 上 `R_post ≥ 0` ⇒ 不交。本文件给 G5 `transported_not_mem_band_IM6`
的 `0 ≤ R` 版（G5 原版保留）。
-/

set_option autoImplicit false
noncomputable section

open Set Function Filter Manifold
open DifferentialGeometry DifferentialGeometry.Topology DifferentialGeometry.Geometry
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology GC.Endpoint GC.LongTime
open scoped Manifold ContDiff Topology

namespace GC.LongTime.CuspP1

universe u

/-- 抽象（符号版）：开邻域上 `S < 0`、`B` 上 `S ≥ 0` ⇒ 不在 `closure B`。 -/
theorem not_mem_closure_of_open_neg_nonneg_IM6 {X : Type*} [TopologicalSpace X] (S : X → ℝ)
    {O B : Set X} (hO : IsOpen O) (hneg : ∀ x ∈ O, S x < 0) (hB : ∀ p ∈ B, 0 ≤ S p)
    {x : X} (hx : x ∈ O) : x ∉ closure B := by
  intro hcl
  obtain ⟨p, hpO, hpB⟩ := mem_closure_iff.mp hcl O hO hx
  linarith [hneg p hpO, hB p hpB]

variable {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g} {K : ℕ}
  {cores : PersistentHyperbolicCores F K}

/-- **⑧（符号版）**：collar 上 `R_post < 0`、band 上 `R_post ≥ 0` ⇒ `γ_s` 不进 band 闭包。 -/
theorem transported_not_mem_band_nonneg_IM6 (M : PrescribedCuspMeridianTop_CPQ cores) {s : ℝ}
    (hs : M.exterior.start ≤ s)
    (hneg : ∀ p ∈ cores.map M.model s (M.exterior.after_cores.trans hs) ''
      riemannianBallOf (cores.model M.model).metric (cores.model M.model).basepoint
        (cores.accuracy s)⁻¹, metricScalarAt (postMetric F.observation s) p < 0)
    {ι : Type*} (N : ι → Set (postStage F.observation s).Carrier)
    (Z : ι → (postStage F.observation s).Carrier → ℝ)
    (hR : ∀ b, ∀ p ∈ N b, |Z b p| < 20 → 0 ≤ metricScalarAt (postMetric F.observation s) p)
    (b : ι) (θ : loopCircle) :
    M.transported s hs θ ∉ closure {p | p ∈ N b ∧ |Z b p| < 20} :=
  not_mem_closure_of_open_neg_nonneg_IM6 (metricScalarAt (postMetric F.observation s))
    (isOpen_collar_IM6 M.model (M.exterior.after_cores.trans hs)) hneg
    (fun p hp => hR b p hp.1 hp.2) (transported_mem_collar_IM6 M hs θ)

/-- consumer：G5 的 `1/2 ≤ R` 版是符号版的特例。 -/
example (M : PrescribedCuspMeridianTop_CPQ cores) {s : ℝ} (hs : M.exterior.start ≤ s)
    (hneg : ∀ p ∈ cores.map M.model s (M.exterior.after_cores.trans hs) ''
      riemannianBallOf (cores.model M.model).metric (cores.model M.model).basepoint
        (cores.accuracy s)⁻¹, metricScalarAt (postMetric F.observation s) p < 0)
    {ι : Type*} (N : ι → Set (postStage F.observation s).Carrier)
    (Z : ι → (postStage F.observation s).Carrier → ℝ)
    (hR : ∀ b, ∀ p ∈ N b, |Z b p| < 20 → 1 / 2 ≤ metricScalarAt (postMetric F.observation s) p)
    (b : ι) (θ : loopCircle) :
    M.transported s hs θ ∉ closure {p | p ∈ N b ∧ |Z b p| < 20} :=
  transported_not_mem_band_nonneg_IM6 M hs hneg N Z
    (fun b p hp hz => by linarith [hR b p hp hz]) b θ

end GC.LongTime.CuspP1
