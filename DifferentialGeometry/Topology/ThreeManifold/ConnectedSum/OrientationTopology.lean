import DifferentialGeometry.Topology.ThreeManifold.ConnectedSum.AssemblyReduction
import DifferentialGeometry.Topology.ThreeManifold.ConnectedSum.OrientationPrelude
import DifferentialGeometry.Topology.Manifold.SmoothOrientationComposition
import DifferentialGeometry.Topology.Manifold.SmoothOrientationCompatible

set_option autoImplicit false
noncomputable section
open Set Function Manifold Topology TopologicalSpace Metric
open scoped Manifold ContDiff Topology

namespace OrientationAssembly
open DifferentialGeometry.Topology ConnectedSumQuotient

universe u v

variable {M : ClosedOrientedManifold.{u} 3} {N : ClosedOrientedManifold.{v} 3}
variable (c : OrientedBallChart M) (d : OrientedBallChart N)
  (aD : csSphere ≃ₘ⟮𝓡 2, 𝓡 2⟯ csSphere)

variable [ChartedSpace csModel (ConnectedSumQuotient c.toBallChart d.toBallChart aD.toHomeomorph)]
variable [IsManifold (𝓡 3) ∞ (ConnectedSumQuotient c.toBallChart d.toBallChart aD.toHomeomorph)]

theorem isOpen_range_interiorLeft
    (hL : ∀ (f : OpenPartialHomeomorph M.Carrier csModel), f ∈ atlas csModel M.Carrier →
      (leftChart c.toBallChart d.toBallChart aD.toHomeomorph hn3 f).symm ∈
        atlas csModel (ConnectedSumQuotient c.toBallChart d.toBallChart aD.toHomeomorph)) :
    IsOpen (Set.range (interiorLeft c.toBallChart d.toBallChart aD)) :=
  (interiorLeft_isLocalDiffeomorph c.toBallChart d.toBallChart aD hL).isOpen_range

theorem isOpen_range_interiorRight
    (hR : ∀ (g : OpenPartialHomeomorph N.Carrier csModel), g ∈ atlas csModel N.Carrier →
      (rightChart c.toBallChart d.toBallChart aD.toHomeomorph hn3 g).symm ∈
        atlas csModel (ConnectedSumQuotient c.toBallChart d.toBallChart aD.toHomeomorph)) :
    IsOpen (Set.range (interiorRight c.toBallChart d.toBallChart aD)) :=
  (interiorRight_isLocalDiffeomorph c.toBallChart d.toBallChart aD hR).isOpen_range

omit [ChartedSpace csModel (ConnectedSumQuotient c.toBallChart d.toBallChart aD.toHomeomorph)]
  [IsManifold (𝓡 3) ∞ (ConnectedSumQuotient c.toBallChart d.toBallChart aD.toHomeomorph)] in
theorem range_interiorLeft_disjoint_range_interiorRight :
    Disjoint (Set.range (interiorLeft c.toBallChart d.toBallChart aD))
      (Set.range (interiorRight c.toBallChart d.toBallChart aD)) := by
  rw [Set.disjoint_left]
  rintro x ⟨u, rfl⟩ ⟨v, hv⟩
  exact interiorLeft_ne_interiorRight c.toBallChart d.toBallChart aD u v hv.symm

theorem mem_seamShell_of_norm_one (z : csSphere) :
    (z : csModel) ∈ SeamShell :=
  ConnectedSumQuotient.mem_SeamShell_of_norm_one z

omit [ChartedSpace csModel (ConnectedSumQuotient c.toBallChart d.toBallChart aD.toHomeomorph)]
  [IsManifold (𝓡 3) ∞ (ConnectedSumQuotient c.toBallChart d.toBallChart aD.toHomeomorph)] in
theorem seamMap_of_unit (z : csSphere) :
    ∃ w : Seam, seamMap c.toBallChart d.toBallChart aD.toHomeomorph w =
      inl c.toBallChart d.toBallChart aD.toHomeomorph (c.toBallChart.boundaryMap z) :=
  ConnectedSumQuotient.seamMap_of_unit c.toBallChart d.toBallChart aD z

omit [ChartedSpace csModel (ConnectedSumQuotient c.toBallChart d.toBallChart aD.toHomeomorph)]
  [IsManifold (𝓡 3) ∞ (ConnectedSumQuotient c.toBallChart d.toBallChart aD.toHomeomorph)] in
theorem range_interior_left_right_union_seamChartX_source :
    Set.range (interiorLeft c.toBallChart d.toBallChart aD) ∪
        Set.range (interiorRight c.toBallChart d.toBallChart aD) ∪
        (seamChartX c.toBallChart d.toBallChart aD.toHomeomorph).source = Set.univ := by
  rw [seamChartX_source]
  ext x
  simp only [mem_union, mem_range, mem_univ, iff_true]
  rcases interior_seam_cover c.toBallChart d.toBallChart aD x with h | h | h
  · exact Or.inl (Or.inl h)
  · exact Or.inl (Or.inr h)
  · exact Or.inr h

end OrientationAssembly
