/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.LocallyFiniteManifoldExhaustion
import DifferentialGeometry.Topology.PiecewiseLinear.SubdivisionSubordinateToCover

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) X] {U : Set X}

open Classical in
theorem LocallyFinitePLPieceIn.locallyFinite_secondDerived
    (T : LocallyFinitePLPieceIn E 3 X U) :
    LocallyFinite fun s : (secondDerived T.complex).faces =>
      (Subtype.val : (secondDerived T.complex).space → E) ⁻¹'
        convexHull ℝ (s.1 : Set E) := by
  let J := secondDerived T.complex
  have hJT : J.space = T.complex.space := (secondDerived_isSubdivision T.complex).space_eq
  intro x
  obtain ⟨S, hfin, hS, hnhds⟩ := T.exists_finite_subcomplex_neighborhood (hJT.subset x.2)
  let _ : Finite S.faces := hfin.to_subtype
  let R := secondDerived S
  have hRJ : R.faces ⊆ J.faces := secondDerived_faces_subset hS
  have hRnhds : R.space ∈ 𝓝[J.space] (x : E) := by
    simpa only [R, (secondDerived_isSubdivision S).space_eq, hJT] using hnhds
  let V := interior ((Subtype.val : J.space → E) ⁻¹' R.space)
  have hV : V ∈ 𝓝 x := interior_mem_nhds.mpr (preimage_coe_mem_nhds_subtype.mpr hRnhds)
  refine ⟨V, hV, ((Set.toFinite R.faces).preimage Subtype.val_injective.injOn).subset ?_⟩
  rintro s ⟨y, hys, hyV⟩
  exact mem_faces_of_mem_nhdsWithin_space hRJ s.2 hys
    (preimage_coe_mem_nhds_subtype.mp (mem_interior_iff_mem_nhds.mp hyV))

open Classical in
theorem LocallyFinitePLPieceIn.isPLDerivedNeighborhoodExhaustion_secondDerived
    {m : ℕ} (T : LocallyFinitePLPieceIn (EuclideanSpace ℝ (Fin m)) 3 X U)
    (hT : IsCombinatorialManifoldWithBoundary 3 T.complex)
    (L : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin m)))
    (hL : L.faces ⊆ (@secondDerived _ _ _ (Classical.decEq _) T.complex).faces)
    (hcard : ∀ s ∈ L.faces, s.card ≤ 2) :
    IsPLDerivedNeighborhoodExhaustion (n := 3)
      (T.map '' (@derivedNeighborhood _ _ _ (Classical.decEq _)
        (@secondDerived _ _ _ (Classical.decEq _) T.complex) L).space)
      (T.map '' L.space) U := by
  let _ : DecidableEq (EuclideanSpace ℝ (Fin m)) := Classical.decEq _
  let J := secondDerived T.complex
  let T' := T.subdivide J (secondDerived_isSubdivision T.complex) T.locallyFinite_secondDerived
  obtain ⟨A, hfin, hAJ, hman, hmono, hfaces, -, hnhds⟩ :=
    T.exists_finite_manifold_exhaustion_secondDerived hT
  let B : ℕ → Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin m)) :=
    fun i => restrict L (A i).space
  have hBA (i : ℕ) : (B i).faces ⊆ (A i).faces := fun s hs =>
    ((mem_restrict_faces_iff_of_faces_subset J L (A i) hL (hAJ i)).mp hs).2
  have hBmono : Monotone (fun i => (B i).faces) := by
    intro i j hij s hs
    exact ⟨hs.1, hs.2.trans (space_mono_of_faces_subset (hmono hij))⟩
  have hBunion : (⋃ i, (B i).space) = L.space :=
    iUnion_restrict_space_of_faces_iUnion J L A hL hfaces
  have hDunion : derivedNeighborhoodExhaustionAmbient A B =
      (derivedNeighborhood J L).space :=
    iUnion_derivedNeighborhood_restrict_space J L A hL hfaces
  have hNrange : range (fun x : derivedNeighborhoodExhaustionAmbient A B => T'.map x) =
      T.map '' (derivedNeighborhood J L).space := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨x, hDunion ▸ x.2, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, hDunion.symm ▸ hx⟩, rfl⟩
  have hCore : (fun x : derivedNeighborhoodExhaustionAmbient A B => T'.map x) ''
      derivedNeighborhoodExhaustionCore A B = T.map '' L.space := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x, hBunion ▸ hx, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      have hxD : x ∈ derivedNeighborhoodExhaustionAmbient A B := by
        rw [hDunion]
        exact mem_of_mem_nhdsWithin (space_mono_of_faces_subset hL hx)
          (T'.derivedNeighborhood_mem_nhdsWithin hL hx)
      refine ⟨⟨x, hxD⟩, ?_, rfl⟩
      change x ∈ ⋃ i, (B i).space
      exact hBunion.symm.subset hx
  refine ⟨m, T', A, B, hfaces, hfin, hBA, fun i s hs => hcard s hs.1, hman,
    ?_, hmono, hBmono, ?_, ?_, hNrange, hCore⟩
  · intro i
    let _ : Finite (A i).faces := (hfin i).to_subtype
    exact (hman i).derivedNeighborhood (B i)
  · intro i j _ s hs hsj
    exact ⟨hsj.1, (A i).convexHull_subset_space hs⟩
  · intro i x hx
    rw [hDunion]
    apply derivedNeighborhood_restrict_space_mem_nhdsWithin J (A (i + 1)) L
      (hAJ (i + 1)) hL
    rw [(secondDerived_isSubdivision T.complex).space_eq]
    exact hnhds i (derivedNeighborhood_space_subset (A i) (B i) hx)

end DifferentialGeometry.Topology.PiecewiseLinear
