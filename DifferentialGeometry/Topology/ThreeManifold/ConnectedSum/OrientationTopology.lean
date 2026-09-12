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
  obtain ⟨z, hz, -⟩ := (inl_eq_inr_iff c.toBallChart d.toBallChart aD.toHomeomorph
    (c.toBallChart.interiorToPunctured u) (d.toBallChart.interiorToPunctured v)).mp hv.symm
  have h1 : ((c.toBallChart.boundaryMap z : c.toBallChart.Punctured) : M.Carrier) =
      ((c.toBallChart.interiorToPunctured u : c.toBallChart.Punctured) : M.Carrier) :=
    congrArg Subtype.val hz
  have hnot : ((c.toBallChart.interiorToPunctured u : c.toBallChart.Punctured) : M.Carrier) ∉
      c.toBallChart.chart '' Metric.closedBall 0 1 := by
    rw [← BallChart.mem_interior]
    exact u.2
  have hmem : ((c.toBallChart.boundaryMap z : c.toBallChart.Punctured) : M.Carrier) ∈
      c.toBallChart.chart '' Metric.closedBall 0 1 :=
    ⟨(z : csModel), by simp [Metric.mem_closedBall], rfl⟩
  exact hnot (h1 ▸ hmem)

theorem mem_seamShell_of_norm_one (z : csSphere) :
    (z : csModel) ∈ SeamShell := by
  rw [SeamShell]
  have h := norm_coe_sphere z
  constructor <;> linarith

omit [ChartedSpace csModel (ConnectedSumQuotient c.toBallChart d.toBallChart aD.toHomeomorph)]
  [IsManifold (𝓡 3) ∞ (ConnectedSumQuotient c.toBallChart d.toBallChart aD.toHomeomorph)] in
theorem seamMap_of_unit (z : csSphere) :
    ∃ w : Seam, seamMap c.toBallChart d.toBallChart aD.toHomeomorph w =
      inl c.toBallChart d.toBallChart aD.toHomeomorph (c.toBallChart.boundaryMap z) := by
  refine ⟨⟨(z : csModel), mem_seamShell_of_norm_one z⟩, ?_⟩
  have hnorm : ‖((⟨(z : csModel), mem_seamShell_of_norm_one z⟩ : Seam) : csModel)‖ = 1 :=
    norm_coe_sphere z
  rw [seamMap_of_one_le c.toBallChart d.toBallChart aD.toHomeomorph _ (le_of_eq hnorm.symm),
    seamLeft_eq_of_one_le c.toBallChart d.toBallChart aD.toHomeomorph _ (le_of_eq hnorm.symm)]
  refine congrArg (inl c.toBallChart d.toBallChart aD.toHomeomorph) (Subtype.ext ?_)
  rw [radialMap_seamDir_coe c.toBallChart
      (⟨(z : csModel), mem_seamShell_of_norm_one z⟩ : Seam) (le_of_eq hnorm.symm),
    BallChart.boundaryMap_val]

omit [ChartedSpace csModel (ConnectedSumQuotient c.toBallChart d.toBallChart aD.toHomeomorph)]
  [IsManifold (𝓡 3) ∞ (ConnectedSumQuotient c.toBallChart d.toBallChart aD.toHomeomorph)] in
theorem range_interior_left_right_union_seamChartX_source :
    Set.range (interiorLeft c.toBallChart d.toBallChart aD) ∪
        Set.range (interiorRight c.toBallChart d.toBallChart aD) ∪
        (seamChartX c.toBallChart d.toBallChart aD.toHomeomorph).source = Set.univ := by
  rw [seamChartX_source]
  ext x
  simp only [mem_union, mem_range, mem_univ, iff_true]
  obtain ⟨y, rfl⟩ | ⟨y, rfl⟩ := jointly_surjective c.toBallChart d.toBallChart aD.toHomeomorph x
  · obtain ⟨z, rfl⟩ | ⟨z, rfl⟩ := c.toBallChart.interior_boundary_cover y
    · exact Or.inl (Or.inl ⟨z, rfl⟩)
    · exact Or.inr (seamMap_of_unit c d aD z)
  · obtain ⟨z, rfl⟩ | ⟨z, rfl⟩ := d.toBallChart.interior_boundary_cover y
    · exact Or.inl (Or.inr ⟨z, rfl⟩)
    · refine Or.inr ?_
      obtain ⟨w, hw⟩ := seamMap_of_unit c d aD (aD.symm z)
      refine ⟨w, ?_⟩
      rw [hw, boundary_eq c.toBallChart d.toBallChart aD.toHomeomorph (aD.symm z)]
      simp

end OrientationAssembly


