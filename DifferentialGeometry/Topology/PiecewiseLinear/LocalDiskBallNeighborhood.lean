/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.LocalSurfaceLink
import DifferentialGeometry.Topology.PiecewiseLinear.ManifoldSubdivision
import DifferentialGeometry.Topology.PiecewiseLinear.SurfaceSplitDiskNeighborhood

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

open Classical in
theorem isPLSphere_two_geometricLink_of_isSubdivision_of_forall_vertex
    {T : Geometry.SimplicialComplex ℝ E} [Finite T.faces] (hT : ∀ s ∈ T.faces, s.card ≤ 4)
    {t : Finset E} (ht : t ∈ T.faces)
    (hlk : ∀ w ∈ t, IsPLSphere 2 (SimplicialComplex.geometricLink T {w}).space) {x : E}
    (hx : x ∈ openSimplex t) {J : Geometry.SimplicialComplex ℝ E} [Finite J.faces]
    (hJ : IsSubdivision J T) (hxJ : ({x} : Finset E) ∈ J.faces) :
    IsPLSphere 2 (SimplicialComplex.geometricLink J {x}).space := by
  obtain ⟨w, hw⟩ := T.nonempty_of_mem_faces ht
  have htc := hT t ht
  by_cases h4 : t.card = 4
  · exact isPLSphere_geometricLink_of_forall_card_le T (m := 2) hT ht h4 hx hJ hxJ
  have hsph : IsPLSphere (2 - (t.card - 1)) (SimplicialComplex.geometricLink T t).space := by
    by_cases h1 : t.card = 1
    · obtain ⟨v, rfl⟩ := Finset.card_eq_one.mp h1
      rw [h1]
      exact hlk v (Finset.mem_singleton_self v)
    · obtain ⟨t', hwt', rfl⟩ : ∃ t', w ∉ t' ∧ t = insert w t' :=
        ⟨t.erase w, Finset.notMem_erase w t, (Finset.insert_erase hw).symm⟩
      have hcins := Finset.card_insert_of_notMem hwt' (s := t')
      have hcard' : t'.card = (t'.card - 1) + 1 := by omega
      have hw' : ({w} : Finset E) ∈ T.faces :=
        T.down_closed ht (Finset.singleton_subset_iff.mpr (Finset.mem_insert_self w t'))
          (Finset.singleton_nonempty w)
      have hsL : t' ∈ (SimplicialComplex.geometricLink T {w}).faces :=
        (SimplicialComplex.mem_geometricLink_singleton T w t').mpr
          ⟨Finset.card_pos.mp (by omega), hwt', ht⟩
      have hlkw := hlk w (Finset.mem_insert_self w t')
      rw [geometricLink_insert T hwt']
      have h := isPLSphere_geometricLink_faces_of_isPLSphere (m := 1) _ hlkw hsL hcard'
        (by omega)
      rw [hcins]
      rwa [show 2 - (t'.card + 1 - 1) = 1 - (t'.card - 1) by omega]
  have h := isPLSphere_geometricLink_of_isPLSphere_geometricLink T ht hx hJ hxJ
    (show t.card = (t.card - 1) + 1 by have := Finset.card_pos.mpr ⟨w, hw⟩; omega) hsph
  rwa [show t.card - 1 + (2 - (t.card - 1)) = 2 by omega] at h

open Classical in
theorem exists_isPLBall_nhdsWithin_of_isPLBall_two {T : Geometry.SimplicialComplex ℝ E}
    [Finite T.faces] (hT : ∀ s ∈ T.faces, s.card ≤ 4) {O : Set E} (hO : IsOpen O)
    (hlk : ∀ t ∈ T.faces, (convexHull ℝ (t : Set E) ∩ O).Nonempty → ∀ w ∈ t,
      IsPLSphere 2 (SimplicialComplex.geometricLink T {w}).space)
    {D : Set E} (hD : IsPLBall 2 D) (hDT : D ⊆ T.space) (hDO : D ⊆ O) :
    ∃ N : Set E, IsPLBall 3 N ∧ D ⊆ N ∧ N ⊆ T.space ∩ O ∧ ∀ x ∈ D, N ∈ 𝓝[T.space] x := by
  have hlink : ∀ J : Geometry.SimplicialComplex ℝ E, IsSubdivision J T → J.faces.Finite →
      ∀ v ∈ O, ({v} : Finset E) ∈ J.faces →
        IsPLSphere 2 (SimplicialComplex.geometricLink J {v}).space ∨
          IsPLBall 2 (SimplicialComplex.geometricLink J {v}).space := by
    intro J hJ hJfin v hv hvJ
    have : Finite J.faces := hJfin.to_subtype
    have hvT : v ∈ T.space := by
      rw [← hJ.space_eq]
      exact J.convexHull_subset_space hvJ (by simp)
    obtain ⟨t, ht, hvt⟩ := exists_face_mem_openSimplex T hvT
    exact Or.inl (isPLSphere_two_geometricLink_of_isSubdivision_of_forall_vertex hT ht
      (hlk t ht ⟨v, openSimplex_subset_convexHull t hvt, hv⟩) hvt hJ hvJ)
  obtain ⟨K', L, hK', hK'fin, hLK', hL, hLO, hLn⟩ :=
    exists_isSubdivision_neighborhood_of_forall_geometricLink hD.isPolyhedron.isCompact hDT hO
      hDO hlink
  have : Finite K'.faces := hK'fin.to_subtype
  have : Finite L.faces := (hK'fin.subset hLK').to_subtype
  have hDL : D ⊆ L.space := fun x hx => mem_of_mem_nhdsWithin (hDT hx) (hLn x hx)
  obtain ⟨R, A, -, -, -, -, -, hN, hDN, hNL, hNn⟩ :=
    hL.exists_isPLBall_derivedNeighborhood_disk hD hDL
  have hLT : L.space ⊆ T.space := by
    rw [← hK'.space_eq]
    exact space_mono_of_faces_subset hLK'
  exact ⟨_, hN, hDN, fun y hy => ⟨hLT (hNL hy), hLO (hNL hy)⟩,
    fun x hx => nhdsWithin_le_of_mem (hLn x hx) (hNn x hx)⟩

end DifferentialGeometry.Topology.PiecewiseLinear
