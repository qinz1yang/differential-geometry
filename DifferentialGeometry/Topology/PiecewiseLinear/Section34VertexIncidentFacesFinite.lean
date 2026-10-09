/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.DiskBallNeighborhoodImage
import DifferentialGeometry.Topology.PiecewiseLinear.Section34Frame

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

variable {Ea : Type} [NormedAddCommGroup Ea] [NormedSpace ℝ Ea]
  {M : Type u} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  {U : Set M} {𝒦 𝒦' : LocallyFinitePLPieceIn Ea 3 M U}

theorem finite_setOf_section34Faces_incident_vertex
    (hsub : IsSubdivision 𝒦'.complex 𝒦.complex)
    (w : Section34VertexIndex 𝒦 𝒦') (k : ℕ) :
    {s : Section34SimplexIndex 𝒦 k | Section34Incident w.1 s.1}.Finite := by
  obtain ⟨a, ha⟩ := 𝒦'.complex.nonempty_of_mem_faces w.2.1
  have haK : a ∈ 𝒦.complex.space := by
    rw [← hsub.space_eq]
    exact 𝒦'.complex.convexHull_subset_space w.2.1
      (subset_convexHull ℝ _ (Finset.mem_coe.mpr ha))
  refine Set.Finite.of_finite_image (f := fun s : Section34SimplexIndex 𝒦 k => s.1)
    ((𝒦.finite_faces_inter_of_isCompact (isCompact_singleton (x := a))
      (singleton_subset_iff.mpr haK)).subset ?_) Subtype.val_injective.injOn
  rintro _ ⟨s, hs, rfl⟩
  exact ⟨s.2.1, a, hs (Finset.mem_coe.mpr ha), mem_singleton a⟩

end DifferentialGeometry.Topology.PiecewiseLinear
