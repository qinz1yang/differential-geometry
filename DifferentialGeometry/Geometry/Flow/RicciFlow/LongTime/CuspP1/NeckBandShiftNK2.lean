import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspP1.SurgerySepEventSG2
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.NeckWideBandNK2

/-!
# R3：static 坐标 `z_s` 与 NECK 坐标 `Z` 的对齐（S-W-NECK-2 G2，后缀 `_NK2`）

SURGERY-2 的切割系统用 static neck `(R.static b).neck`（坐标 `z_s`，`z_s = 0` 是切割球面，
`z_s ≥ 0` 是 unchanged 侧）；NECK 的 `sliceChart_NK` / `sliceHeight_NK` 属于原 neck
`R.neck b.1.1` 的 backward `R.backward b.1.1`（高度 `0` = tube 中点，落在 removed band 里）。
`GeometricCutoffRecord.recenter_chart` 给 `chart_static (v, z_s) = chart_orig (v, ±(1 + z_s))`，
所以 `Z = σ_b · (1 + z_s)`，`σ_b = if b.1.2 then 1 else -1`（符号 = retained 侧）。

* `retainedSign_NK2 b`、`retainedSign_mul_self_NK2`：符号 `σ_b`，`σ_b² = 1`；
* `sliceChart_apply_NK2`、`sliceHeight_sliceChart_NK2`：`sliceChart_NK` 就是原 neck 的 chart，
  `sliceHeight_NK ∘ sliceChart_NK = (·).1.2`；
* **`neckSlab_subset_height_NK2`**：`neckSlab R b S ⊆ {x ∈ range sliceChart | σ_b Z x − 1 ∈ S}`
  （无额外前提）；`neckSlab_eq_height_NK2` 是等式（`S ⊆ static buffer` 时）；
* **`neckSlab_subset_center_band_NK2`**：`z_s ∈ S ⇒ |z_s − m| < w` 时 slab ⊆ 以 `σ_b(1 + m)` 为中心、
  半宽 `w` 的 `Z`-band：`Icc 0 50`（`m = 25, w = 26`）对应中心 `σ_b · 26`、半宽 `26`；
  `Σ_b = {z_s = 50}`（`m = 50`）对应中心 `σ_b · 51`（`Z = ±51`）；
* `retainedSign_mul_height_NK2`：`x ∈ neckSlab R b S ⇒ Z x = σ_b (1 + z_s)`（`z_s ∈ S` 为某个值）。
-/

set_option autoImplicit false
noncomputable section
open Set Manifold
open DifferentialGeometry DifferentialGeometry.PDE.RicciFlow.Surgery.Topology GC.LongTime
open scoped Manifold ContDiff
namespace GC.LongTime.CuspP1
universe u

section Shift

variable {H : ObservedHistory.{u}} {i : Fin H.eventCount} {p : CutoffParameters}

/-- retained boundary `b` 的符号 `σ_b = ±1`（`b.1.2 = true` 取 `+1`）。 -/
def retainedSign_NK2 (b : (H.event i).RetainedBoundaryIndex) : ℝ :=
  if b.1.2 then 1 else -1

theorem retainedSign_mul_self_NK2 (b : (H.event i).RetainedBoundaryIndex) :
    retainedSign_NK2 b * retainedSign_NK2 b = 1 := by
  unfold retainedSign_NK2
  split_ifs <;> norm_num

theorem abs_retainedSign_NK2 (b : (H.event i).RetainedBoundaryIndex) :
    |retainedSign_NK2 b| = 1 := by
  unfold retainedSign_NK2
  split_ifs <;> norm_num

/-- `sliceChart_NK` 就是原 neck 的 chart（`terminal_chart`）。 -/
theorem sliceChart_apply_NK2 (R : GeometricCutoffRecord H i p)
    (α : (H.event i).transition.trace.tubes.Index) (y : neckBuffer (R.delta α)) :
    (R.backward α).sliceChart_NK y = ((R.neck α).chart y).1 :=
  (R.backward α).terminal_chart _ y

/-- 高度坐标在 `sliceChart_NK` 上就是柱坐标的 `ℝ` 分量。 -/
theorem sliceHeight_sliceChart_NK2 (R : GeometricCutoffRecord H i p)
    (α : (H.event i).transition.trace.tubes.Index) (y : neckBuffer (R.delta α)) :
    (R.backward α).sliceHeight_NK ((R.backward α).sliceChart_NK y) = y.1.2 :=
  chartHeight_chart_NK
    ((R.backward α).stageChart_smooth i le_rfl _).isEmbedding.injective y

/-- **G2（⊆）**：static slab `{z_s ∈ S}` 落在 NECK 坐标的 `{σ_b Z − 1 ∈ S}` 里，
`Z = σ_b (1 + z_s)`。 -/
theorem neckSlab_subset_height_NK2 (R : GeometricCutoffRecord H i p)
    (b : (H.event i).RetainedBoundaryIndex) (S : Set ℝ) :
    neckSlab_SG2 R b S ⊆ {x | x ∈ Set.range (R.backward b.1.1).sliceChart_NK ∧
      retainedSign_NK2 b * (R.backward b.1.1).sliceHeight_NK x - 1 ∈ S} := by
  rintro _ ⟨y, hy, rfl⟩
  have hbuf := R.recenter_in_buffer b y
  have hchart := R.recenter_chart b y hbuf
  set y' : neckBuffer (R.delta b.1.1) := ⟨_, hbuf⟩ with hy'
  have hx : ((R.static b).neck.chart y).1 = (R.backward b.1.1).sliceChart_NK y' := by
    rw [sliceChart_apply_NK2, hchart]
  refine ⟨?_, ?_⟩
  · rw [hx]
    exact ⟨y', rfl⟩
  · rw [hx, sliceHeight_sliceChart_NK2]
    have h1 : y'.1.2 = retainedSign_NK2 b * (1 + y.1.2) := rfl
    have h2 : retainedSign_NK2 b * (retainedSign_NK2 b * (1 + y.1.2)) - 1 = y.1.2 := by
      have := retainedSign_mul_self_NK2 b
      linear_combination (1 + y.1.2) * this
    rw [h1, h2]
    exact hy

/-- **G2（=）**：`S ⊆ static buffer` 时 static slab 恰为 NECK 坐标的 `{σ_b Z − 1 ∈ S}`。 -/
theorem neckSlab_eq_height_NK2 (R : GeometricCutoffRecord H i p)
    (b : (H.event i).RetainedBoundaryIndex) {S : Set ℝ}
    (hS : S ⊆ Ioo (-((R.static b).delta)⁻¹ - 1) (((R.static b).delta)⁻¹ + 1)) :
    neckSlab_SG2 R b S = {x | x ∈ Set.range (R.backward b.1.1).sliceChart_NK ∧
      retainedSign_NK2 b * (R.backward b.1.1).sliceHeight_NK x - 1 ∈ S} := by
  refine (neckSlab_subset_height_NK2 R b S).antisymm ?_
  rintro _ ⟨⟨y', rfl⟩, hz⟩
  rw [sliceHeight_sliceChart_NK2] at hz
  have hmem : ((y'.1.1, retainedSign_NK2 b * y'.1.2 - 1) : NeckCylinder) ∈
      neckBuffer (R.static b).delta := hS hz
  refine ⟨⟨_, hmem⟩, hz, ?_⟩
  have hbuf := R.recenter_in_buffer b ⟨_, hmem⟩
  rw [R.recenter_chart b ⟨_, hmem⟩ hbuf, sliceChart_apply_NK2]
  have key : ∀ w : neckBuffer (R.delta b.1.1), w.1 = y'.1 →
      ((R.neck b.1.1).chart w).1 = ((R.neck b.1.1).chart y').1 := fun w hw => by
    rw [Subtype.ext hw]
  refine key _ (Prod.ext rfl ?_)
  have := retainedSign_mul_self_NK2 b
  change retainedSign_NK2 b * (1 + (retainedSign_NK2 b * y'.1.2 - 1)) = y'.1.2
  linear_combination y'.1.2 * this

/-- **G2（band）**：`S` 里的 `z_s` 都满足 `|z_s − m| < w` 时，static slab 落在以 `σ_b (1 + m)` 为中心、
半宽 `w` 的 NECK 高度 band 里。 -/
theorem neckSlab_subset_center_band_NK2 (R : GeometricCutoffRecord H i p)
    (b : (H.event i).RetainedBoundaryIndex) {S : Set ℝ} {m w : ℝ}
    (hSm : ∀ z ∈ S, |z - m| < w) :
    neckSlab_SG2 R b S ⊆ {x | x ∈ Set.range (R.backward b.1.1).sliceChart_NK ∧
      |(R.backward b.1.1).sliceHeight_NK x - retainedSign_NK2 b * (1 + m)| < w} := by
  intro x hx
  obtain ⟨hr, hz⟩ := neckSlab_subset_height_NK2 R b S hx
  refine ⟨hr, ?_⟩
  have h1 := hSm _ hz
  have h2 : (R.backward b.1.1).sliceHeight_NK x - retainedSign_NK2 b * (1 + m) =
      retainedSign_NK2 b * (retainedSign_NK2 b * (R.backward b.1.1).sliceHeight_NK x - 1 - m) := by
    have := retainedSign_mul_self_NK2 b
    linear_combination (-(R.backward b.1.1).sliceHeight_NK x) * this
  rw [h2, abs_mul, abs_retainedSign_NK2, one_mul]
  exact h1

/-- 切割球面 `Σ_b = {z_s = 50}`：`Z = σ_b · 51`（原 neck 坐标 `z = ±51`）。 -/
theorem neckSlab_fifty_height_NK2 (R : GeometricCutoffRecord H i p)
    (b : (H.event i).RetainedBoundaryIndex) {x : (H.stage i.castSucc).Carrier}
    (hx : x ∈ neckSlab_SG2 R b {50}) :
    x ∈ Set.range (R.backward b.1.1).sliceChart_NK ∧
      (R.backward b.1.1).sliceHeight_NK x = retainedSign_NK2 b * 51 := by
  obtain ⟨hr, hz⟩ := neckSlab_subset_height_NK2 R b {50} hx
  refine ⟨hr, ?_⟩
  have h50 : retainedSign_NK2 b * (R.backward b.1.1).sliceHeight_NK x - 1 = 50 := hz
  have := retainedSign_mul_self_NK2 b
  linear_combination retainedSign_NK2 b * h50 - (R.backward b.1.1).sliceHeight_NK x * this

end Shift

end GC.LongTime.CuspP1
