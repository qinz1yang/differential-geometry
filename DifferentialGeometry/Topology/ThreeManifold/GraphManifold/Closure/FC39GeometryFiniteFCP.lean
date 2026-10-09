import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39RegionFiniteFCP

/-!
# FC39: the finite lists of `C₁` and `M₃` for the cut geometry `H`

Lane S-FINCOMP, group G4 (suffix `_FCP`). `StageCutGeometry74 A D` (draft 74 §4.1, `H`) carries the
junction rim facts `H.rims`; the FDC04 finite-list clause for the two-stratum piece is therefore a
property of `H` itself, with no further row.

* `StageCutGeometry74.finite_lists_FCP`: `C₁ = R.circle.cbase` and `D.M₃` are finite disjoint
  unions of compact connected pieces, for `R = H.rows`.
-/

set_option autoImplicit false

noncomputable section

open Set Function
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert GC.GraphManifold
open Manifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold.Assembly.FC39P0

variable {W : CompactCarrier.{u}} {n : ℕ} {E : BoundaryTori W n} {A : SmoothStageGeometry74 W E}
  {D : StageCutChoice74 A}

/-- **The FDC04 finite lists of the two-stratum piece, from the cut geometry** (see the module
docstring). -/
theorem StageCutGeometry74.finite_lists_FCP (H : StageCutGeometry74 A D) :
    (∃ (m : ℕ) (Bc : Fin m → Set H.rows.circle.Base), (∀ i, IsCompact (Bc i)) ∧
      (∀ i, IsConnected (Bc i)) ∧ Pairwise (Disjoint on Bc) ∧
      H.rows.circle.cbase = ⋃ i, Bc i) ∧
    (∃ (m : ℕ) (Bm : Fin m → Set W.Carrier), (∀ i, IsCompact (Bm i)) ∧
      (∀ i, IsConnected (Bm i)) ∧ Pairwise (Disjoint on Bm) ∧ D.M₃ = ⋃ i, Bm i) := by
  obtain ⟨m, Bc, h1, h2, -, -, -, h6, h7⟩ := H.rims.circle_cbase_finite_components_FCP
  exact ⟨⟨m, Bc, h1, h2, h6, h7⟩, H.rims.circle_region_finite_components_FCP⟩

end GC.GraphManifold.Assembly.FC39P0
