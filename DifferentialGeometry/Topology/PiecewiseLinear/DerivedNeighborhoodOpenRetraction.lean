/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.DerivedNeighborhoodRetraction

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

open Classical in
theorem exists_isOpen_homotopic_retraction_of_faces_subset
    {A B : Geometry.SimplicialComplex ℝ E} [Finite A.faces] (hBA : B.faces ⊆ A.faces) :
    ∃ N : Set E, IsOpen N ∧ B.space ⊆ N ∧ ∃ g : C(↥(A.space ∩ N), ↥B.space),
      ContinuousMap.Homotopic
        (⟨inclusion inter_subset_left, continuous_inclusion inter_subset_left⟩ :
          C(↥(A.space ∩ N), ↥A.space))
        ((⟨inclusion (space_mono_of_faces_subset hBA),
          continuous_inclusion (space_mono_of_faces_subset hBA)⟩ :
            C(↥B.space, ↥A.space)).comp g) := by
  have hnhds : ∀ x ∈ B.space, ∃ V : Set E, IsOpen V ∧ x ∈ V ∧
      V ∩ A.space ⊆ derivedNeighborhoodSpace A B := by
    intro x hx
    obtain ⟨V, hV, hVN⟩ :=
      mem_nhdsWithin_iff_exists_mem_nhds_inter.mp (derivedNeighborhood_mem_nhdsWithin hBA hx)
    obtain ⟨V', hV'V, hV'o, hxV'⟩ := mem_nhds_iff.mp hV
    exact ⟨V', hV'o, hxV', fun y hy => hVN ⟨hV'V hy.1, hy.2⟩⟩
  choose! V hVo hxV hVN using hnhds
  refine ⟨⋃ x ∈ B.space, V x, isOpen_biUnion fun x hx => hVo x hx,
    fun x hx => mem_iUnion₂.mpr ⟨x, hx, hxV x hx⟩, ?_⟩
  have hsub : A.space ∩ (⋃ x ∈ B.space, V x) ⊆ derivedNeighborhoodSpace A B := by
    rintro y ⟨hyA, hy⟩
    obtain ⟨x, hx, hyx⟩ := mem_iUnion₂.mp hy
    exact hVN x hx ⟨hyx, hyA⟩
  let R := derivedNeighborhoodStrongDeformationRetract hBA
  let ι : C(↥(A.space ∩ ⋃ x ∈ B.space, V x), derivedNeighborhoodSpace A B) :=
    ⟨fun w => ⟨w.1, hsub w.2⟩, continuous_subtype_val.subtype_mk _⟩
  let g : C(↥(A.space ∩ ⋃ x ∈ B.space, V x), ↥B.space) :=
    ⟨fun w => ⟨((R.retraction (ι w) : derivedNeighborhoodSpace A B) : E), (R.retraction (ι w)).2⟩,
      (continuous_subtype_val.comp (continuous_subtype_val.comp
        (R.retraction.continuous.comp ι.continuous))).subtype_mk _⟩
  refine ⟨g, ⟨{ toFun := fun q => ⟨((R.homotopy (q.1, ι q.2) : derivedNeighborhoodSpace A B) : E),
      derivedNeighborhood_space_subset A B (R.homotopy (q.1, ι q.2)).2⟩
                continuous_toFun := (continuous_subtype_val.comp (R.homotopy.continuous.comp
                  (continuous_fst.prodMk (ι.continuous.comp continuous_snd)))).subtype_mk _
                map_zero_left := fun w => by
                  apply Subtype.ext
                  change ((R.homotopy (0, ι w) : derivedNeighborhoodSpace A B) : E) = w.1
                  rw [R.homotopy.apply_zero]
                  rfl
                map_one_left := fun w => by
                  apply Subtype.ext
                  change ((R.homotopy (1, ι w) : derivedNeighborhoodSpace A B) : E) =
                    ((R.retraction (ι w) : derivedNeighborhoodSpace A B) : E)
                  rw [R.homotopy.apply_one]
                  rfl }⟩⟩

end DifferentialGeometry.Topology.PiecewiseLinear
