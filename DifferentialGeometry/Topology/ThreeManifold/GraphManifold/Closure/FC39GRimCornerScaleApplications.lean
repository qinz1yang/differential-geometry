import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39GRimCornerScale
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39P0Adapted

/-!
# FC39 GROUP G, RIMBOX R2 kernel: consumer

Lane FC39-G-RIMBOX. For every actual endpoint `e` of the raw rows and every safe neighbourhood
system, the labelled tube chart `κ_e` (centred at the rim base point) has a scale `l₀ > 0` below
which the closed square `l • [-3, 3]²` lies in its target and is carried by `κ_e⁻¹` into the safe
corner base `safe.cornerBase e`; the normalized chart of such a scale on `rimBox 3` reads
`κ_e = l • v`.
-/

set_option autoImplicit false

noncomputable section

open Set Function
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert GC.GraphManifold
open Manifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold.Assembly.FC39P0

variable {W : CompactCarrier.{u}} {n : ℕ} {E : BoundaryTori W n}

/-- **Small corner scales inside the safe corner base.** -/
theorem FC39RowsV2.exists_cornerScale_safe_GRIM (Rw : FC39RowsV2 W E)
    (safe : ProducerSafeNeighbourhoods Rw) (e : Rw.edge.EdgeEnd) :
    ∃ l₀ : ℝ, 0 < l₀ ∧ ∀ l, 0 < l → l ≤ l₀ → ∀ v : ℝ × ℝ, |v.1| ≤ 3 → |v.2| ≤ 3 →
      l • v ∈ (Rw.labelledTubes.chart e).target ∧
        (Rw.labelledTubes.chart e).toPartialEquiv.symm (l • v) ∈ safe.cornerBase e := by
  have hsrc : Rw.junctions.rimBase e.1 ∈ (Rw.labelledTubes.chart e).source := by
    rw [Rw.labelledTubes.chart_source e]
    exact Rw.labelledTubes.rimBase_mem e
  have hc0 : Rw.labelledTubes.chart e (Rw.junctions.rimBase e.1) = 0 :=
    Rw.labelledTubes.chart_center e
  exact exists_cornerScale_GRIM (Rw.labelledTubes.chart e) hsrc hc0 (safe.cornerBase e).isOpen
    (safe.rimBase_mem e) (by norm_num)

/-- The normalized corner chart of a small scale: on `rimBox 3` the tube chart reads `l • v`, and
the chart lands in the safe corner base. -/
theorem FC39RowsV2.exists_scaledCornerChart_GRIM (Rw : FC39RowsV2 W E)
    (safe : ProducerSafeNeighbourhoods Rw) (e : Rw.edge.EdgeEnd) :
    ∃ (l : ℝ) (hl : 0 < l) (hbox : ∀ v ∈ rimBox 3, l • v ∈ (Rw.labelledTubes.chart e).target),
      (scaledChart_GRIM (Rw.labelledTubes.chart e) l 3 hl hbox).source = rimBox 3 ∧
      ∀ v ∈ rimBox 3,
        Rw.labelledTubes.chart e (scaledChart_GRIM (Rw.labelledTubes.chart e) l 3 hl hbox v) =
            l • v ∧
          scaledChart_GRIM (Rw.labelledTubes.chart e) l 3 hl hbox v ∈ safe.cornerBase e := by
  obtain ⟨l₀, hl₀, h⟩ := Rw.exists_cornerScale_safe_GRIM safe e
  have hbox : ∀ v ∈ rimBox 3, l₀ • v ∈ (Rw.labelledTubes.chart e).target :=
    fun v hv => (h l₀ hl₀ le_rfl v hv.1.le hv.2.le).1
  exact ⟨l₀, hl₀, hbox, rfl, fun v hv =>
    ⟨chart_scaledChart_GRIM _ l₀ 3 hl₀ hbox hv, (h l₀ hl₀ le_rfl v hv.1.le hv.2.le).2⟩⟩

end GC.GraphManifold.Assembly.FC39P0
