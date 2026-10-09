import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspP1.NeckBandShiftNK2

/-!
# G2 的 consumer（S-W-NECK-2，后缀 `_NK2`）

切割球面 `Σ_b = {z_s = 50}` 落在 NECK 坐标 `Z = σ_b · 51` 的一个任意窄 band 里（对 `w > 0`
`{|Z − σ_b · 51| < w}`），整段 `N_b = {0 ≤ z_s ≤ 50}` 落在 `{|Z − σ_b · 26| < 26}` 里。
-/

set_option autoImplicit false
noncomputable section
open Set Manifold
open DifferentialGeometry DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
namespace GC.LongTime.CuspP1
universe u

example {H : ObservedHistory.{u}} {i : Fin H.eventCount} {p : CutoffParameters}
    (R : GeometricCutoffRecord H i p) (b : (H.event i).RetainedBoundaryIndex) {w : ℝ}
    (hw : 0 < w) :
    neckSlab_SG2 R b {50} ⊆ {x | x ∈ Set.range (R.backward b.1.1).sliceChart_NK ∧
      |(R.backward b.1.1).sliceHeight_NK x - retainedSign_NK2 b * 51| < w} := by
  intro x hx
  obtain ⟨hr, hz⟩ := neckSlab_fifty_height_NK2 R b hx
  exact ⟨hr, by rw [hz, sub_self, abs_zero]; exact hw⟩

example {H : ObservedHistory.{u}} {i : Fin H.eventCount} {p : CutoffParameters}
    (R : GeometricCutoffRecord H i p) (b : (H.event i).RetainedBoundaryIndex) :
    neckSlab_SG2 R b (Icc 0 50) ⊆ {x | x ∈ Set.range (R.backward b.1.1).sliceChart_NK ∧
      |(R.backward b.1.1).sliceHeight_NK x - retainedSign_NK2 b * (1 + 25)| < 26} :=
  neckSlab_subset_center_band_NK2 R b (m := 25) (w := 26) fun z hz => by
    rw [abs_lt]
    constructor <;> linarith [hz.1, hz.2]

end GC.LongTime.CuspP1
