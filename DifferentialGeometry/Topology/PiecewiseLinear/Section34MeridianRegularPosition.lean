import DifferentialGeometry.Topology.PiecewiseLinear.Section34RegularCylindricalCrossings
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CurveHeightSides
import DifferentialGeometry.Topology.PiecewiseLinear.CylindricalFrontier

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

open Classical in
theorem IsCylindricalDiagram.exists_regular_meridian_position
    {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    (D : Geometry.SimplicialComplex ℝ E) (M : Geometry.SimplicialComplex ℝ F)
    [Finite D.faces] [Finite M.faces] (hD : IsPLBall 2 D.space)
    (hM : IsCombinatorialManifoldWithBoundary 3 M)
    {f : E × ℝ → F} (hf : IsCylindricalDiagram f D.space M.space)
    (hends : ∀ x ∈ D.space, f (x, 0) = f (x, 1))
    (hdim : Module.finrank ℝ F = 3) {J : Set F} (hJ : IsPLSphere 1 J)
    (hJB : J ⊆ (boundaryComplex 3 M).space) :
    ∃ r ∈ Ioo (1 / 4 : ℝ) (3 / 4),
      (J ∩ f '' (D.space ×ˢ {r})).Finite ∧
      (∀ x ∈ D.space, f (x, r) ∈ J →
        (x, r) ∈ closure (((D.space ×ˢ Icc (1 / 4) (3 / 4)) ∩ f ⁻¹' J) ∩
          {y | y.2 < r}) ∧
        (x, r) ∈ closure (((D.space ×ˢ Icc (1 / 4) (3 / 4)) ∩ f ⁻¹' J) ∩
          {y | r < y.2})) ∧
      ∀ y ∈ J ∩ f '' ((boundaryComplex 2 D).space ×ˢ {r}),
        ∃ (e : OpenPartialHomeomorph (ℝ × ℝ) (boundaryComplex 3 M).space) (ε : ℝ),
          0 < ε ∧ (e (0, 0) : F) = y ∧
          Ioo (-ε) ε ×ˢ Ioo (-ε) ε ⊆ e.source ∧
          ∀ p ∈ Ioo (-ε) ε ×ˢ Ioo (-ε) ε,
            ((e p : F) ∈ J ↔ p.1 = 0) ∧
              ((e p : F) ∈ f '' ((boundaryComplex 2 D).space ×ˢ {r}) ↔ p.2 = 0) := by
  let P := (boundaryComplex 2 D).space
  have hPD : P ⊆ D.space := boundaryComplex_space_subset 2 D
  have hP : IsPLSphere 1 P := isPLSphere_boundaryComplex_space_of_isPLBall D hD
  have hside := hf.boundary D hD.isCombinatorialManifoldWithBoundary
  have hsideB : IsCylindricalDiagram f P (boundaryComplex 3 M).space :=
    hf.image_side_eq_boundaryComplex D M hD hM hdim ▸ hside
  obtain ⟨r, L, hr, hLfin, hL, hcard, hrv, hfinite, hcharts⟩ :=
    hsideB.exists_finite_slice_axis_charts hP (fun x hx => hends x (hPD hx)) hJ
      (a := 1 / 4) (b := 3 / 4) (by norm_num) (by norm_num) (by norm_num)
      (Or.inl (by norm_num))
  let _ : Finite L.faces := hLfin.to_subtype
  have hr01 : r ∈ Icc (0 : ℝ) 1 := by constructor <;> linarith [hr.1, hr.2]
  have hmeet : (boundaryComplex 3 M).space ∩ f '' (D.space ×ˢ {r}) =
      f '' (P ×ˢ {r}) := by
    rw [← hf.image_side_eq_boundaryComplex D M hD hM hdim]
    exact hf.image_subcylinder_inter_slice hPD hside.image_top_eq_bottom hr01
  have htrace : J ∩ f '' (D.space ×ˢ {r}) = J ∩ f '' (P ×ˢ {r}) := by
    ext y
    exact ⟨fun h => ⟨h.1, hmeet.subset ⟨hJB h.1, h.2⟩⟩,
      fun h => ⟨h.1, image_mono (prod_mono hPD Subset.rfl) h.2⟩⟩
  refine ⟨r, hr, htrace ▸ hfinite, ?_, hcharts⟩
  intro x hxD hxJ
  obtain ⟨z, hz, heq⟩ := hmeet.subset ⟨hJB hxJ, ⟨(x, r), ⟨hxD, rfl⟩, rfl⟩⟩
  have hzx : z.1 = x :=
    (hf.isPLHomeomorphOn_slice hD.isPolyhedron hr01).bijOn.injOn (hPD hz.1) hxD
      (by rw [show (z.1, r) = z from Prod.ext rfl hz.2.symm]; exact heq)
  have hxP : x ∈ P := hzx ▸ hz.1
  have hxL : (x, r) ∈ L.space ∩ {y | y.2 = r} := by
    rw [hL]
    exact ⟨⟨⟨hxP, hr.1.le, hr.2.le⟩, hxJ⟩, rfl⟩
  obtain ⟨hlo, hhi⟩ := mem_closure_height_sides_of_notMem_vertex_image L hcard
    (LinearMap.snd ℝ E ℝ) hrv hxL
  have hsub : L.space ⊆ (D.space ×ˢ Icc (1 / 4) (3 / 4)) ∩ f ⁻¹' J := by
    rw [hL]
    exact inter_subset_inter_left _ (prod_mono hPD Subset.rfl)
  exact ⟨closure_mono (inter_subset_inter_left _ hsub) hlo,
    closure_mono (inter_subset_inter_left _ hsub) hhi⟩

end DifferentialGeometry.Topology.PiecewiseLinear
