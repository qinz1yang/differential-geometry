import DifferentialGeometry.Topology.PiecewiseLinear.Section34InteriorFillingQuadrantRegions
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CrossingNeighborhoodQuadrants

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem IsPLHomeomorphInto.crossing_traces_of_image {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    {P C : Set (EuclideanSpace ℝ (Fin 3))} {u : EuclideanSpace ℝ (Fin 3) → M}
    (hu : IsPLHomeomorphInto 3 u P) (hP : IsClosed P) (hCP : C ⊆ interior P)
    {f : (ℝ × ℝ) × ℝ → EuclideanSpace ℝ (Fin 3)}
    (hf : IsCylindricalDiagram f spliceSquare C) {A B : Set M}
    (hA : IsClosed A) (hB : IsClosed B)
    (hregA : closure (interior A) = A) (hregB : closure (interior B) = B)
    (hfirst : u '' (f '' (section34MarkedRibbon 0 ∪ section34MarkedRibbon 2)) =
      u '' C ∩ frontier A)
    (hsecond : u '' (f '' (section34MarkedRibbon 1 ∪ section34MarkedRibbon 3)) =
      u '' C ∩ frontier B)
    (hpages : ∀ j : Fin 4, u '' (f '' section34MarkedRibbon j) = u '' C ∩
      ![frontier A ∩ B, frontier B ∩ A, frontier A \ interior B, frontier B \ interior A] j) :
    let X := closure (interior (P ∩ u ⁻¹' A))
    let Y := closure (interior (P ∩ u ⁻¹' B))
    f '' (section34MarkedRibbon 0 ∪ section34MarkedRibbon 2) = C ∩ frontier X ∧
      f '' (section34MarkedRibbon 1 ∪ section34MarkedRibbon 3) = C ∩ frontier Y ∧
      ∀ j : Fin 4, f '' section34MarkedRibbon j = C ∩
        ![frontier X ∩ Y, frontier Y ∩ X, frontier X \ interior Y, frontier Y \ interior X] j := by
  let X := closure (interior (P ∩ u ⁻¹' A))
  let Y := closure (interior (P ∩ u ⁻¹' B))
  have himage {D S : Set (EuclideanSpace ℝ (Fin 3))} {T : Set M}
      (hDC : D ⊆ C) (hST : ∀ x ∈ C, x ∈ S ↔ u x ∈ T)
      (hD : u '' D = u '' C ∩ T) : D = C ∩ S := by
    apply (hu.injOn.image_eq_image_iff (hDC.trans (hCP.trans interior_subset))
      (inter_subset_left.trans (hCP.trans interior_subset))).mp
    rw [hD]
    apply Subset.antisymm
    · rintro _ ⟨⟨x, hxC, rfl⟩, hxT⟩
      exact ⟨x, ⟨hxC, (hST x hxC).mpr hxT⟩, rfl⟩
    · rintro _ ⟨x, ⟨hxC, hxS⟩, rfl⟩
      exact ⟨⟨x, hxC, rfl⟩, (hST x hxC).mp hxS⟩
  have hD (j : Fin 4) : f '' section34MarkedRibbon j ⊆ C :=
    (image_mono (section34_marked_ribbon_subset_cylinder j)).trans hf.image_eq.subset
  have hAX (x : EuclideanSpace ℝ (Fin 3)) (hx : x ∈ C) :
      x ∈ frontier X ↔ u x ∈ frontier A :=
    (hu.regularized_clipped_region_frontier hregA (hCP hx)).1
  have hBY (x : EuclideanSpace ℝ (Fin 3)) (hx : x ∈ C) :
      x ∈ frontier Y ↔ u x ∈ frontier B :=
    (hu.regularized_clipped_region_frontier hregB (hCP hx)).1
  have hXA (x : EuclideanSpace ℝ (Fin 3)) (hx : x ∈ C) : x ∈ X ↔ u x ∈ A :=
    (hu.regularized_clipped_region hP hA hregA).2.2.2 x (hCP hx)
  have hYB (x : EuclideanSpace ℝ (Fin 3)) (hx : x ∈ C) : x ∈ Y ↔ u x ∈ B :=
    (hu.regularized_clipped_region hP hB hregB).2.2.2 x (hCP hx)
  refine ⟨himage (by rw [image_union]; exact union_subset (hD 0) (hD 2)) hAX hfirst,
    himage (by rw [image_union]; exact union_subset (hD 1) (hD 3)) hBY hsecond, ?_⟩
  intro j
  apply himage (hD j) ?_ (hpages j)
  intro x hx
  fin_cases j
  · exact (hAX x hx).and (hYB x hx)
  · exact (hBY x hx).and (hXA x hx)
  · exact (hAX x hx).and (hu.regularized_clipped_region_frontier hregB (hCP hx)).2.not
  · exact (hBY x hx).and (hu.regularized_clipped_region_frontier hregA (hCP hx)).2.not

end DifferentialGeometry.Topology.PiecewiseLinear
