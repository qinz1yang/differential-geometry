import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyCycleVertical

/-!
# FC42 packet H1 (part a): consumers of vertical propagation

Lane ASM-CYC2.

* `DecompositionCertificate.handle_vertical_subset_region_diff_interior`: the vertical face of a
  handle lies in the circle region but not in its ambient interior (density of the handle's
  interior points and `circ_handle_disjoint`);
* `DecompositionCertificate.handle_vertical_not_mem_otherPieces`: at interior times the vertical
  face meets no vertex, no other handle and no edge circle piece (vertical propagation + no third
  piece).
-/

set_option autoImplicit false

noncomputable section

open Set Function Filter
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert GC.GraphManifold Manifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold.Assembly

local instance diskChartsH1A_ASMCYC2 : ChartedSpace (EuclideanHalfSpace 2) (ClosedCell 2) :=
  DifferentialGeometry.Topology.Handle.closedCellChartedSpaceSucc 1

local instance diskSmoothH1A_ASMCYC2 : IsManifold (𝓡∂ 2) ∞ (ClosedCell 2) :=
  DifferentialGeometry.Topology.Handle.closedCellIsManifold 1

namespace DecompositionCertificate

variable {W : CompactCarrier.{u}} {n : ℕ} {E : BoundaryTori W n} (D : DecompositionCertificate W E)

/-- The vertical face of a handle lies in the circle region, off its ambient interior. -/
theorem handle_vertical_subset_region_diff_interior (h : Fin D.handleCount) :
    (D.handle h).vertical ⊆ D.circ.region \ interior D.circ.region := by
  intro z hz
  refine ⟨D.handle_vertical_subset_region h hz, fun hint => ?_⟩
  obtain ⟨p, -, rfl⟩ := hz
  obtain ⟨w, hw1, hw2⟩ := inter_interior_range_nonempty finrank_handleModel
    (D.handle h).smooth (D.handle h).mfderiv_bijective isOpen_interior ⟨_, hint, ⟨p, rfl⟩⟩
  exact Set.disjoint_left.mp (D.circ_handle_disjoint h) hw1 hw2

/-- At interior times the vertical face meets no other piece. -/
theorem handle_vertical_not_mem_otherPieces (h : Fin D.handleCount) {x : ClosedCell 2}
    (hx : x ∈ diskRim) {t : Icc (0 : ℝ) 1} (ht0 : 0 < (t : ℝ)) (ht1 : (t : ℝ) < 1) :
    (D.handle h).map (x, t) ∉ D.otherPieces h := fun hC =>
  D.false_of_vertical_mem_otherPieces h hx ht0 ht1
    (D.handle_vertical_subset_region h ⟨(x, t), ⟨hx, mem_univ _⟩, rfl⟩) hC

end DecompositionCertificate

end GC.GraphManifold.Assembly
