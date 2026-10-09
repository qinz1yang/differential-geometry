import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspP1.TransportedBandIM6

/-!
# ⑧ 的集合版：`γ_s` 不在任何 `R ≥ 0` 的集合里（O-W-IMS06 G10，后缀 `_IM6`）

S-A14-SURGERY-2 G3′（`exists_window_separation_SG2`）的分离要求 `γ_s θ ∉ e_s '' N_b`，其中
`N_b = {0 ≤ z_s ≤ 50}` 是整段保留 collar（不只是 IMS06′ 的 band 闭包）。只要 `N_b` 上 `R_post ≥ 0`
（neck closeness 在整个 collar 上，`δ_s⁻¹ > 100`），collar `O_s` 上 `R_post < 0` 就给出 `γ_s θ ∉ N_b`。
本文件给任意集合 `S` 的版本（`S` 上 `R ≥ 0` ⇒ `γ_s` 不在 `S` 里，也不在其闭包里）。
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

variable {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g} {K : ℕ}
  {cores : PersistentHyperbolicCores F K}

/-- **⑧（集合版）**：collar 上 `R_post < 0`、`S` 上 `R_post ≥ 0` ⇒ `γ_s θ ∉ closure S`。 -/
theorem transported_not_mem_closure_of_scalar_nonneg_IM6
    (M : PrescribedCuspMeridianTop_CPQ cores) {s : ℝ} (hs : M.exterior.start ≤ s)
    (hneg : ∀ p ∈ cores.map M.model s (M.exterior.after_cores.trans hs) ''
      riemannianBallOf (cores.model M.model).metric (cores.model M.model).basepoint
        (cores.accuracy s)⁻¹, metricScalarAt (postMetric F.observation s) p < 0)
    {S : Set (postStage F.observation s).Carrier}
    (hS : ∀ p ∈ S, 0 ≤ metricScalarAt (postMetric F.observation s) p) (θ : loopCircle) :
    M.transported s hs θ ∉ closure S := by
  intro hcl
  obtain ⟨p, hpO, hpS⟩ := mem_closure_iff.mp hcl _
    (isOpen_collar_IM6 M.model (M.exterior.after_cores.trans hs))
    (transported_mem_collar_IM6 M hs θ)
  linarith [hneg p hpO, hS p hpS]

/-- 推论：`γ_s θ ∉ S`（SURGERY-2 G3′ 的 `hγ` 第二合取项形状：`∀ b, γ_s θ ∉ e_s '' N_b`）。 -/
theorem transported_not_mem_of_scalar_nonneg_IM6
    (M : PrescribedCuspMeridianTop_CPQ cores) {s : ℝ} (hs : M.exterior.start ≤ s)
    (hneg : ∀ p ∈ cores.map M.model s (M.exterior.after_cores.trans hs) ''
      riemannianBallOf (cores.model M.model).metric (cores.model M.model).basepoint
        (cores.accuracy s)⁻¹, metricScalarAt (postMetric F.observation s) p < 0)
    {ι : Type*} (S : ι → Set (postStage F.observation s).Carrier)
    (hS : ∀ b, ∀ p ∈ S b, 0 ≤ metricScalarAt (postMetric F.observation s) p) (θ : loopCircle) :
    ∀ b, M.transported s hs θ ∉ S b := fun b h =>
  transported_not_mem_closure_of_scalar_nonneg_IM6 M hs hneg (hS b) θ (subset_closure h)

end GC.LongTime.CuspP1
