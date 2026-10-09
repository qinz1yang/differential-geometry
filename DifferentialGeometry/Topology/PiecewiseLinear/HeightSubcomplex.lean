/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.DerivedNeighborhoodRetraction

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem mem_restrict_affine_lt_vertices_iff
    (K : Geometry.SimplicialComplex ℝ E) (a : E →ᵃ[ℝ] ℝ) (r : ℝ) {v : E} :
    v ∈ (restrict K {x | a x < r}).vertices ↔ v ∈ K.vertices ∧ a v < r := by
  change ({v} ∈ K.faces ∧ convexHull ℝ (({v} : Finset E) : Set E) ⊆ {x | a x < r}) ↔ _
  simp only [Finset.coe_singleton, convexHull_singleton, singleton_subset_iff, mem_ofPred_eq]
  rfl

theorem mem_restrict_affine_lt_faces_iff
    (K : Geometry.SimplicialComplex ℝ E) (a : E →ᵃ[ℝ] ℝ) (r : ℝ) {s : Finset E} :
    s ∈ (restrict K {x | a x < r}).faces ↔ s ∈ K.faces ∧ ∀ v ∈ s, a v < r := by
  constructor
  · rintro ⟨hs, hsub⟩
    exact ⟨hs, fun v hv => hsub (subset_convexHull ℝ _ hv)⟩
  · rintro ⟨hs, hverts⟩
    exact ⟨hs, convexHull_min hverts ((convex_Iio r).affine_preimage a)⟩

theorem subcomplexBarycentricMass_pos_on_affine_lt
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (a : E →ᵃ[ℝ] ℝ) (r : ℝ) {x : E} (hx : x ∈ K.space ∩ {x | a x < r}) :
    0 < subcomplexBarycentricMass K (restrict K {x | a x < r}) x := by
  classical
  obtain ⟨s, hs, hxs⟩ := exists_face_mem_openSimplex K hx.1
  have hxc := openSimplex_subset_convexHull s hxs
  obtain ⟨v, hvs, hvr⟩ : ∃ v ∈ s, a v < r := by
    by_contra h
    push Not at h
    have hsub : convexHull ℝ (s : Set E) ⊆ {y | r ≤ a y} :=
      convexHull_min h ((convex_Ici r).affine_preimage a)
    exact not_lt_of_ge (show r ≤ a x from hsub hxc) (show a x < r from hx.2)
  have hvL : v ∈ (restrict K {x | a x < r}).vertices := by
    refine ⟨K.down_closed hs (Finset.singleton_subset_iff.mpr hvs)
      (Finset.singleton_nonempty v), ?_⟩
    simpa only [Finset.coe_singleton, convexHull_singleton, singleton_subset_iff, mem_ofPred_eq]
        using hvr
  rw [subcomplexBarycentricMass_eq_sum_filter K _ hs hxc]
  exact Finset.sum_pos' (fun w hw => weights_nonneg hxc (Finset.mem_filter.mp hw).1)
    ⟨v, Finset.mem_filter.mpr ⟨hvs, hvL⟩, (mem_openSimplex_self_iff (K.indep hs) hxc).mp hxs v hvs⟩

theorem subcomplexBarycentricProjection_mem_restrict_affine_lt
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (a : E →ᵃ[ℝ] ℝ) (r : ℝ) {x : E} (hx : x ∈ K.space ∩ {x | a x < r}) :
    subcomplexBarycentricProjection K (restrict K {x | a x < r}) x ∈
      (restrict K {x | a x < r}).space := by
  classical
  let L := restrict K {x | a x < r}
  obtain ⟨s, hs, hxs⟩ := K.mem_space_iff.mp hx.1
  have hp := subcomplexBarycentricProjection_mem_convexHull_filter K L hs hxs
    (subcomplexBarycentricMass_pos_on_affine_lt K a r hx)
  have hne : (s.filter fun v => v ∈ L.vertices).Nonempty :=
    Finset.coe_nonempty.mp (convexHull_nonempty_iff.mp ⟨_, hp⟩)
  refine L.convexHull_subset_space ⟨K.down_closed hs (Finset.filter_subset _ _) hne, ?_⟩ hp
  apply convexHull_min _ ((convex_Iio r).affine_preimage a)
  intro v hv
  exact restrict_space_subset K _ (L.vertices_subset_space (Finset.mem_filter.mp hv).2)

theorem continuousOn_subcomplexBarycentricProjection_affine_lt [FiniteDimensional ℝ E]
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces] (a : E →ᵃ[ℝ] ℝ) (r : ℝ) :
    ContinuousOn (subcomplexBarycentricProjection K (restrict K {x | a x < r}))
      (K.space ∩ {x | a x < r}) := by
  exact (((continuousOn_subcomplexBarycentricMass K _).mono inter_subset_left).inv₀
    (fun x hx => (subcomplexBarycentricMass_pos_on_affine_lt K a r hx).ne')).smul
    ((continuousOn_subcomplexBarycentricMoment K _).mono inter_subset_left)

theorem subcomplexBarycentricProjection_image_affine_lt
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces] (a : E →ᵃ[ℝ] ℝ) (r : ℝ) :
    subcomplexBarycentricProjection K (restrict K {x | a x < r}) ''
      (K.space ∩ {x | a x < r}) = (restrict K {x | a x < r}).space := by
  apply Subset.antisymm
  · rintro y ⟨x, hx, rfl⟩
    exact subcomplexBarycentricProjection_mem_restrict_affine_lt K a r hx
  · intro x hx
    exact ⟨x, ⟨space_mono_of_faces_subset (restrict_faces_subset K _) hx,
      restrict_space_subset K _ hx⟩,
      subcomplexBarycentricProjection_eq_self (restrict_faces_subset K _) hx⟩

theorem isPreconnected_restrict_affine_lt_of_isPreconnected [FiniteDimensional ℝ E]
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces] (a : E →ᵃ[ℝ] ℝ) (r : ℝ)
    (h : IsPreconnected (K.space ∩ {x | a x < r})) :
    IsPreconnected (restrict K {x | a x < r}).space := by
  rw [← subcomplexBarycentricProjection_image_affine_lt K a r]
  exact h.image _ (continuousOn_subcomplexBarycentricProjection_affine_lt K a r)

end DifferentialGeometry.Topology.PiecewiseLinear
