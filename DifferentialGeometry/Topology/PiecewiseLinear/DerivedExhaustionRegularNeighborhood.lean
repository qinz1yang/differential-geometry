/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.LocallyFinitePieceTransport
import DifferentialGeometry.Topology.PiecewiseLinear.LocallyFinitePieceRestriction

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {X : Type*} [TopologicalSpace X]

open Classical in
theorem IsPLDerivedNeighborhoodExhaustion.isLocallyFinitePolyhedralManifoldWithBoundary
    {n : ℕ} [ChartedSpace (EuclideanSpace ℝ (Fin n)) X] {N K U : Set X}
    (h : IsPLDerivedNeighborhoodExhaustion (n := n) N K U) :
    IsLocallyFinitePolyhedralManifoldWithBoundary (n := n) n N := by
  obtain ⟨m, T, A, L, hJ, hfin, -, -, -, hman, hAm, hLm, -, hnhds, hN, -⟩ := h
  let D : ℕ → Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin m)) :=
    fun i => @derivedNeighborhood _ _ _ (Classical.decEq _) (A i) (L i)
  have hDfin (i : ℕ) : (D i).faces.Finite := by
    let _ : Finite (A i).faces := (hfin i).to_subtype
    exact @derivedNeighborhood_faces_finite _ _ _ (Classical.decEq _) (A i) (L i) _
  have hAJ (i : ℕ) : (A i).faces ⊆ T.complex.faces := by
    intro s hs
    rw [hJ]
    exact mem_iUnion.mpr ⟨i, hs⟩
  have hDT (i : ℕ) : (D i).space ⊆ T.complex.space :=
    (@derivedNeighborhood_space_subset _ _ _ (Classical.decEq _) (A i) (L i)).trans
      (space_mono_of_faces_subset (hAJ i))
  have hDm : Monotone (fun i => (D i).faces) := fun i j hij =>
    @derivedNeighborhood_faces_mono _ _ _ (Classical.decEq _) (A i) (A j) (L i) (L j)
      (hAm hij) (hLm hij)
  let B := derivedNeighborhoodExhaustionAmbient A L
  have hBT : B ⊆ T.complex.space := iUnion_subset hDT
  let g : B → X := fun x => T.map x
  have hg : IsEmbedding g := T.isEmbedding.comp (IsEmbedding.inclusion hBT)
  have hRange : range g = N := hN
  have hUnion : (⋃ i, T.map '' (D i).space) = N := by
    rw [← hRange]
    ext y
    constructor
    · intro hy
      obtain ⟨i, x, hx, rfl⟩ := mem_iUnion.mp hy
      exact ⟨⟨x, mem_iUnion.mpr ⟨i, hx⟩⟩, rfl⟩
    · rintro ⟨x, rfl⟩
      obtain ⟨i, hi⟩ := mem_iUnion.mp x.2
      exact mem_iUnion.mpr ⟨i, x, hi, rfl⟩
  have hTargetNhds (i : ℕ) {x : X} (hx : x ∈ T.map '' (D i).space) :
      T.map '' (D (i + 1)).space ∈ 𝓝[N] x := by
    obtain ⟨y, hy, rfl⟩ := hx
    let z : B := ⟨y, mem_iUnion.mpr ⟨i, hy⟩⟩
    have hpre : (Subtype.val : B → EuclideanSpace ℝ (Fin m)) ⁻¹' (D (i + 1)).space ∈
        𝓝 z := preimage_coe_mem_nhds_subtype.mpr (hnhds i hy)
    have himage := hg.isInducing.image_mem_nhdsWithin hpre
    rw [hRange] at himage
    exact Filter.mem_of_superset himage (by rintro _ ⟨w, hw, rfl⟩; exact ⟨w, hw, rfl⟩)
  let P (i : ℕ) : PLPiece n X (T.map '' (D i).space) :=
    ⟨m, T.restrict (D i) (hDfin i) (hDT i)⟩
  let tower : LocallyFinitePieceTower n X N := {
    N := fun i => T.map '' (D i).space
    piece := P
    subset_nhdsWithin := fun i x hx => hTargetNhds i hx
    iUnion_eq := hUnion
    core := D
    core_le := fun _ => Subset.rfl
    subset_core := fun i => image_mono (space_mono_of_faces_subset (hDm (Nat.le_succ i)))
    coreImage := D
    coreImage_le := fun i => hDm (Nat.le_succ i)
    embed := fun _ => id
    embedInv := fun _ => id
    embed_isGlueIso := by
      intro i
      refine ⟨?_, ?_, fun _ _ _ _ => rfl, fun _ _ _ _ => rfl⟩
      · intro s hs
        simpa only [Finset.image_id] using hs
      · intro s hs
        simpa only [Finset.image_id] using hs
    map_embed := fun i x hx => congrArg T.map
      (simplicialMap_eq_of_forall_affineOn (D i) id
        (fun _ _ => ⟨AffineMap.id ℝ _, fun _ _ => rfl⟩) hx) }
  exact ⟨tower, hman⟩

open Classical in
theorem LocallyFinitePLPieceIn.isLocallyFiniteRegularNeighborhoodOf_secondDerived
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) X] {U : Set X} (hU : IsOpen U)
    (T : LocallyFinitePLPieceIn E 3 X U)
    (hT : IsCombinatorialManifoldWithBoundary 3 T.complex)
    (L : Geometry.SimplicialComplex ℝ E) (hL : L.faces ⊆ (secondDerived T.complex).faces)
    (hcard : ∀ s ∈ L.faces, s.card ≤ 2) :
    IsLocallyFiniteRegularNeighborhoodOf (n := 3)
      (T.map '' (derivedNeighborhood (secondDerived T.complex) L).space)
      (T.map '' L.space) U := by
  have h := T.isPLDerivedNeighborhoodExhaustion_secondDerived_of_finiteDimensional hT L hL hcard
  refine ⟨h, ?_, h.isLocallyFinitePolyhedralManifoldWithBoundary⟩
  let T' := T.subdivide (secondDerived T.complex) (secondDerived_isSubdivision T.complex)
    T.locallyFinite_secondDerived
  exact T'.image_derivedNeighborhood_mem_nhdsSet hU hL

end DifferentialGeometry.Topology.PiecewiseLinear
