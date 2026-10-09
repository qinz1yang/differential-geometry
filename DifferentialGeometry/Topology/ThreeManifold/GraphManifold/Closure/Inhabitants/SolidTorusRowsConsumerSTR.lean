import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.Inhabitants.SolidTorusRowsSTR

/-!
# S-SOLIDTORUS4 (suffix `_STR`), G5 consumer

What a consumer of the rows and cover facts reads: the slim family is empty, the edge bundle of the
rows has one interval component, the ball and cusp are separated, and every point of the solid
torus is in the ball, in the cusp, or in the region `{u ≤ κ, h ≤ -1/4}` (the cover of FDC04).
-/

set_option autoImplicit false

noncomputable section

open Set Function
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold

namespace GC.GraphManifold.Assembly.FC39P0.SolidTorusSTR

open GC.GraphManifold.Assembly.FC39P0.SolidTorusSTI GC.GraphManifold.Assembly.FC39P0

/-- The slim family of the rows is empty. -/
theorem rows_slim_count_STR : rows_STR.slimPieces.count = 0 := rfl

/-- The edge bundle of the rows has exactly one interval component and no circle component. -/
theorem rows_edge_components_STR :
    rows_STR.edgeModels.intervalCount = 1 ∧ rows_STR.edgeModels.circleCount = 0 :=
  ⟨rfl, rfl⟩

/-- **The cover read pointwise**: every point of the solid torus is in the ball `{u ≥ κ}`, in the
cusp `{h ≥ -1/4}`, or in `{u ≤ κ, h ≤ -1/4}`. -/
theorem cover_pointwise_STR (p : Wc.Carrier) :
    4 / 5 ≤ uW_STR p ∨ -(1 / 4 : ℝ) ≤ X135Radial.height p ∨
      (uW_STR p ≤ 4 / 5 ∧ X135Radial.height p ≤ -(1 / 4 : ℝ)) := by
  have hp : p ∈ ((⋃ i, range (ballZeroDomainsL_STR.piece i).map) ∪
      ⋃ b, range (X135Radial.radialCuspCores.piece b).map) ∪
      (cutChoice_STR ballZeroDomainsL_STR).slimSet ∪ (cutChoice_STR ballZeroDomainsL_STR).M₂ := by
    exact (Set.ext_iff.1 cover_STR.cover p).2 (mem_univ p)
  rcases hp with (hz | hs) | hm
  · rw [unionZC_STR] at hz
    rcases hz with hz | hz
    · exact Or.inl hz
    · exact Or.inr (Or.inl hz)
  · rw [slimSet_eq_STR] at hs
    exact hs.elim
  · rw [M2_eq_STR] at hm
    exact Or.inr (Or.inr hm)

end GC.GraphManifold.Assembly.FC39P0.SolidTorusSTR
