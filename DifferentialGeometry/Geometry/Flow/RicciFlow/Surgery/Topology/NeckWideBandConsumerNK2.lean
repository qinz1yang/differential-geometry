import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.NeckWideBandNK2

/-!
# G1 的 consumer（S-W-NECK-2，后缀 `_NK2`）

`GeometricCutoffRecord` 的 `backward α`（晚期 `R.delta α ≤ 1/40000`，`order ≥ 2` 由 `order_lower` 给）上，
`slice_band_estimates_center_NK2` 在 band `{|Z − 26| < 26}`（覆盖 `Z ∈ (0, 52) ⊇ [1, 51]`，
即 static `{0 ≤ z_s ≤ 50}` 的 `σ = +1` 侧）与 `{|Z + 26| < 26}`（`σ = −1` 侧）上同时给出 `R ≥ 3/5`、
`(dz)² ≤ 2 g` 与闭包 `⊆ range`。
-/

set_option autoImplicit false
noncomputable section
open Set Manifold
open DifferentialGeometry DifferentialGeometry.Geometry DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff
namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
universe u

example {H : ObservedHistory.{u}} {i : Fin H.eventCount} {p : CutoffParameters}
    (R : GeometricCutoffRecord H i p) (α : (H.event i).transition.trace.tubes.Index)
    (hδ : R.delta α ≤ 1 / 40000) :
    ∃ d : ℝ, 0 < d ∧ ∀ s : ℝ, H.time i.succ - d ≤ s → s < H.time i.succ →
      ∀ c₀ : ℝ, |c₀| = 26 →
        closure {x : (H.stage i.castSucc).Carrier |
            x ∈ Set.range (R.backward α).sliceChart_NK ∧
              |(R.backward α).sliceHeight_NK x - c₀| < 26} ⊆
          Set.range (R.backward α).sliceChart_NK ∧
        ∀ x ∈ Set.range (R.backward α).sliceChart_NK,
          |(R.backward α).sliceHeight_NK x - c₀| < 26 →
          3 / 5 ≤ metricScalarAt ((R.backward α).sliceMetric_NK s) x ∧
          ∀ v : TangentSpace ThreeModel x,
            (show ℝ from mfderiv ThreeModel 𝓘(ℝ, ℝ) (R.backward α).sliceHeight_NK x v) ^ 2 ≤
              2 * ((R.backward α).sliceMetric_NK s).inner x v v := by
  obtain ⟨d, hd, h⟩ := (R.backward α).slice_band_estimates_center_NK2 (R.two_le_order_NK α) hδ
  refine ⟨d, hd, fun s hs1 hs2 c₀ hc => ?_⟩
  have hpos := R.delta_pos α
  have h40 : (40000 : ℝ) ≤ (R.delta α)⁻¹ := by
    rw [le_inv_comm₀ (by norm_num) hpos]
    simpa using hδ
  obtain ⟨h1, h2, h3⟩ := h s hs1 hs2 c₀ 26 (by rw [hc]; linarith)
  exact ⟨h1, fun x hx hz => ⟨h2 x hx hz, h3 x hx hz⟩⟩

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
