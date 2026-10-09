/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.LocallyFiniteDerivedManifold
import DifferentialGeometry.Topology.PiecewiseLinear.GeneratedSubcomplex

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace X] {U : Set X}

open Classical in
theorem LocallyFinitePLPieceIn.exists_finite_subcomplex_covering_isCompact
    {d : ℕ} [ChartedSpace (EuclideanSpace ℝ (Fin d)) X]
    (T : LocallyFinitePLPieceIn E d X U) {P : Set E} (hP : IsCompact P)
    (hPT : P ⊆ T.complex.space) :
    ∃ S : Geometry.SimplicialComplex ℝ E, S.faces.Finite ∧ S.faces ⊆ T.complex.faces ∧
      P ⊆ S.space := by
  let C : Set T.complex.space := (Subtype.val : T.complex.space → E) ⁻¹' P
  have hC : IsCompact C := by
    rw [Subtype.isCompact_iff, Subtype.image_preimage_coe, inter_eq_right.mpr hPT]
    exact hP
  let A : Set (Finset E) := Subtype.val ''
    {s : T.complex.faces | ((Subtype.val : T.complex.space → E) ⁻¹'
      convexHull ℝ (s.1 : Set E) ∩ C).Nonempty}
  have hA : A.Finite := (T.locallyFinite.finite_nonempty_inter_compact hC).image Subtype.val
  refine ⟨subcomplexGeneratedBy T.complex A, ?_,
    subcomplexGeneratedBy_faces_subset T.complex A, ?_⟩
  · apply (hA.biUnion fun s _ => s.powerset.finite_toSet).subset
    rintro s ⟨t, ht, hst, -⟩
    exact mem_biUnion ht.2 (Finset.mem_powerset.mpr hst)
  · intro x hx
    obtain ⟨s, hs, hxs⟩ := T.complex.mem_space_iff.mp (hPT hx)
    apply (subcomplexGeneratedBy T.complex A).convexHull_subset_space _ hxs
    exact ⟨s, ⟨hs, ⟨⟨s, hs⟩, ⟨⟨x, hPT hx⟩, hxs, hx⟩, rfl⟩⟩,
      Finset.Subset.rfl, T.complex.nonempty_of_mem_faces hs⟩

open Classical in
theorem LocallyFinitePLPieceIn.exists_finite_manifold_exhaustion_secondDerived
    [FiniteDimensional ℝ E] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) X]
    (T : LocallyFinitePLPieceIn E 3 X U) {n : ℕ}
    (hT : IsCombinatorialManifoldWithBoundary (n + 1) T.complex) :
    ∃ A : ℕ → Geometry.SimplicialComplex ℝ E,
      (∀ i, (A i).faces.Finite) ∧
      (∀ i, (A i).faces ⊆ (secondDerived T.complex).faces) ∧
      (∀ i, IsCombinatorialManifoldWithBoundary (n + 1) (A i)) ∧
      Monotone (fun i => (A i).faces) ∧
      (secondDerived T.complex).faces = ⋃ i, (A i).faces ∧
      (⋃ i, (A i).space) = T.complex.space ∧
      ∀ i {x : E}, x ∈ (A i).space → (A (i + 1)).space ∈ 𝓝[T.complex.space] x := by
  let _ : WeaklyLocallyCompactSpace T.complex.space := ⟨fun x => by
    obtain ⟨S, hfin, hS, hnhds⟩ := T.exists_finite_subcomplex_neighborhood x.2
    let _ : Finite S.faces := hfin.to_subtype
    refine ⟨(Subtype.val : T.complex.space → E) ⁻¹' S.space, ?_,
      preimage_coe_mem_nhds_subtype.mpr hnhds⟩
    rw [Subtype.isCompact_iff, Subtype.image_preimage_coe,
      inter_eq_right.mpr (space_mono_of_faces_subset hS)]
    exact SimplicialComplex.isCompact_geometricSpace S⟩
  let C : ℕ → Set E := fun i =>
    (Subtype.val : T.complex.space → E) '' compactCovering T.complex.space i
  have hC (i : ℕ) : IsCompact (C i) :=
    (isCompact_compactCovering T.complex.space i).image continuous_subtype_val
  have hCT (i : ℕ) : C i ⊆ T.complex.space := by
    rintro x ⟨y, -, rfl⟩
    exact y.2
  have hcover : ∀ x ∈ T.complex.space, ∃ i, x ∈ C i := by
    intro x hx
    obtain ⟨i, hi⟩ := exists_mem_compactCovering (⟨x, hx⟩ : T.complex.space)
    exact ⟨i, ⟨x, hx⟩, hi, rfl⟩
  let J := secondDerived T.complex
  have hJT : J.space = T.complex.space := (secondDerived_isSubdivision T.complex).space_eq
  let P := {S : Geometry.SimplicialComplex ℝ E // S.faces.Finite ∧ S.faces ⊆ J.faces ∧
    IsCombinatorialManifoldWithBoundary (n + 1) S}
  have hPT (S : P) : S.1.space ⊆ T.complex.space := by
    rw [← hJT]
    exact space_mono_of_faces_subset S.2.2.1
  have hstep : ∀ i (S : P), ∃ R : P,
      ∀ x ∈ S.1.space ∪ C i, R.1.space ∈ 𝓝[T.complex.space] x := by
    intro i S
    let _ : Finite S.1.faces := S.2.1.to_subtype
    obtain ⟨F, hfin, hF, hcoverF⟩ := T.exists_finite_subcomplex_covering_isCompact
      ((SimplicialComplex.isCompact_geometricSpace S.1).union (hC i))
      (union_subset (hPT S) (hCT i))
    refine ⟨⟨derivedNeighborhood T.complex F,
      T.derivedNeighborhood_faces_finite_of_finite_core F hF hfin,
      derivedNeighborhood_faces_subset T.complex F,
      T.isCombinatorialManifoldWithBoundary_derivedNeighborhood hT F hF⟩, ?_⟩
    exact fun x hx => T.derivedNeighborhood_mem_nhdsWithin hF (hcoverF hx)
  choose f hf using hstep
  let start : P := ⟨⊥, finite_empty, empty_subset _, by intro v hv; exact False.elim hv⟩
  let seq : ℕ → P := Nat.rec start (fun i S => f i S)
  let A : ℕ → Geometry.SimplicialComplex ℝ E := fun i => (seq i).1
  have hnhds (i : ℕ) {x : E} (hx : x ∈ (A i).space) :
      (A (i + 1)).space ∈ 𝓝[T.complex.space] x := hf i (seq i) x (Or.inl hx)
  have hspaceStep (i : ℕ) : (A i).space ⊆ (A (i + 1)).space := fun x hx =>
    mem_of_mem_nhdsWithin (hPT (seq i) hx) (hnhds i hx)
  have hmono : Monotone (fun i => (A i).faces) := by
    apply monotone_nat_of_le_succ
    intro i s hs
    exact mem_faces_of_mem_openSimplex_of_mem_space (seq (i + 1)).2.2.1
      ((seq i).2.2.1 hs) (centroid_mem_openSimplex ((A i).nonempty_of_mem_faces hs))
      (hspaceStep i ((A i).convexHull_subset_space hs
        (s.centroid_mem_convexHull ((A i).nonempty_of_mem_faces hs))))
  have hspace : (⋃ i, (A i).space) = T.complex.space := by
    apply Subset.antisymm (iUnion_subset fun i => hPT (seq i))
    intro x hx
    obtain ⟨i, hi⟩ := hcover x hx
    exact mem_iUnion.mpr ⟨i + 1, mem_of_mem_nhdsWithin hx
      (hf i (seq i) x (Or.inr hi))⟩
  refine ⟨A, fun i => (seq i).2.1, fun i => (seq i).2.2.1,
    fun i => (seq i).2.2.2, hmono, ?_, hspace, hnhds⟩
  apply Subset.antisymm
  · intro s hs
    have hcent : s.centroid ℝ id ∈ T.complex.space := by
      rw [← hJT]
      exact J.convexHull_subset_space hs (s.centroid_mem_convexHull
        (J.nonempty_of_mem_faces hs))
    obtain ⟨i, hi⟩ := mem_iUnion.mp (hspace.symm ▸ hcent)
    exact mem_iUnion.mpr ⟨i, mem_faces_of_mem_openSimplex_of_mem_space (seq i).2.2.1 hs
      (centroid_mem_openSimplex (J.nonempty_of_mem_faces hs)) hi⟩
  · exact iUnion_subset fun i => (seq i).2.2.1

end DifferentialGeometry.Topology.PiecewiseLinear
