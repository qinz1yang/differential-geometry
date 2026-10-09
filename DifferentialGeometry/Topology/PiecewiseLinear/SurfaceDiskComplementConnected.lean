/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.Connected.ClosedCover
import DifferentialGeometry.Topology.PiecewiseLinear.ManifoldDisjointUnion
import DifferentialGeometry.Topology.PiecewiseLinear.ManifoldInteriorConnected
import DifferentialGeometry.Topology.PiecewiseLinear.ManifoldSubcomplexBoundary
import DifferentialGeometry.Topology.PiecewiseLinear.SurfaceSubcomplexComplement

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

open Classical in
private theorem exists_manifold_disjoint_disk_union {ι : Type*} [Finite ι]
    {D : ι → Set E} {r : ι → (Fin 3 → ℝ) → E}
    (hr : ∀ i, IsPLHomeomorphOn (r i) (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) (D i))
    (hdisj : Pairwise fun i j => Disjoint (D i) (D j)) :
    ∃ A : Geometry.SimplicialComplex ℝ E, A.faces.Finite ∧
      IsCombinatorialManifoldWithBoundary 2 A ∧ A.space = ⋃ i, D i ∧
      (boundaryComplex 2 A).space = ⋃ i, r i '' stdSimplexBoundary 2 := by
  classical
  have hD : ∀ i, IsPLBall 2 (D i) := fun i => ⟨r i, hr i⟩
  choose L hLfin hLD using fun i => (hD i).isPolyhedron.exists_simplicialComplex
  let _ : ∀ i, Finite (L i).faces := fun i => (hLfin i).to_subtype
  have hL : ∀ i, IsCombinatorialManifoldWithBoundary 2 (L i) := fun i =>
    ((hLD i).symm ▸ hD i).isCombinatorialManifoldWithBoundary
  have hLbd : ∀ i, (boundaryComplex 2 (L i)).space = r i '' stdSimplexBoundary 2 := by
    intro i
    rw [boundaryComplex_space_of_isPLHomeomorphOn_stdSimplex (L i) ((hLD i).symm ▸ hr i),
      simplexBoundary_stdVertices_space]
  have key : ∀ s : Finset ι,
      ∃ A : Geometry.SimplicialComplex ℝ E, A.faces.Finite ∧
        IsCombinatorialManifoldWithBoundary 2 A ∧ A.space = ⋃ i ∈ s, D i ∧
        (boundaryComplex 2 A).space = ⋃ i ∈ s, r i '' stdSimplexBoundary 2 := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      refine ⟨⊥, Set.finite_empty, ?_, ?_, ?_⟩
      · intro v hv
        exact False.elim hv
      · simp [Geometry.SimplicialComplex.space_bot]
      · have hbd : (boundaryComplex 2 (⊥ : Geometry.SimplicialComplex ℝ E)).space = ∅ :=
          eq_empty_iff_forall_notMem.mpr fun x hx => by
            have h := boundaryComplex_space_subset 2 (⊥ : Geometry.SimplicialComplex ℝ E) hx
            simp only [Geometry.SimplicialComplex.space_bot, mem_empty_iff_false] at h
        simp [hbd]
    | insert i s his ih =>
      obtain ⟨A, hAfin, hA, hAsp, hAbd⟩ := ih
      let _ : Finite A.faces := hAfin.to_subtype
      have hdis : Disjoint (L i).space A.space := by
        rw [hLD i, hAsp]
        exact disjoint_iUnion₂_right.mpr fun j hj => hdisj fun hij => his (hij ▸ hj)
      obtain ⟨B, hBfin, hB, hBsp, hBbd⟩ :=
        (hL i).exists_space_disjoint_union (L i) A hA hdis
      refine ⟨B, hBfin, hB, ?_, ?_⟩
      · rw [hBsp, hLD i, hAsp, Finset.set_biUnion_insert]
      · rw [hBbd, hLbd i, hAbd, Finset.set_biUnion_insert]
  let _ := Fintype.ofFinite ι
  simpa using key Finset.univ

open Classical in
theorem IsCombinatorialManifold.isConnected_sdiff_iUnion_of_isPLBall_two
    {ι : Type*} [Finite ι] {K : Geometry.SimplicialComplex ℝ E} [Finite K.faces]
    (hK : IsCombinatorialManifold 2 K) (hKc : IsConnected K.space) {D : ι → Set E}
    (hD : ∀ i, IsPLBall 2 (D i)) (hDK : ∀ i, D i ⊆ K.space)
    (hdisj : Pairwise fun i j => Disjoint (D i) (D j)) :
    IsConnected (K.space \ ⋃ i, D i) := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · simpa only [iUnion_of_empty, sdiff_empty] using hKc
  choose r hr using hD
  have hD : ∀ i, IsPLBall 2 (D i) := fun i => ⟨r i, hr i⟩
  have hDc : ∀ i, IsClosed (D i) := fun i => (hD i).isPolyhedron.isClosed
  have hrD : ∀ i, r i '' stdSimplexBoundary 2 ⊆ D i := fun i => by
    rw [← (hr i).image_eq]
    exact image_mono fun x hx => hx.1
  have hrconn : ∀ i, IsConnected (r i '' stdSimplexBoundary 2) := fun i =>
    (isConnected_stdSimplexBoundary 0).image (r i)
      ((hr i).isPiecewiseAffineOn.continuousOn.mono fun x hx => hx.1)
  have hfr : ∀ i, D i ∩ closure (K.space \ D i) = r i '' stdSimplexBoundary 2 := fun i =>
    hK.inter_closure_sdiff_eq_image_stdSimplexBoundary K (hr i) (hDK i)
  let Q := closure (K.space \ ⋃ i, D i)
  have hQK : Q ⊆ K.space := closure_minimal sdiff_subset (isPolyhedron_space K).isClosed
  have hmeet : ∀ i, Q ∩ D i = r i '' stdSimplexBoundary 2 := by
    intro i
    apply Subset.antisymm
    · rintro x ⟨hxQ, hxD⟩
      rw [← hfr i]
      exact ⟨hxD, closure_mono (sdiff_subset_sdiff_right (subset_iUnion D i)) hxQ⟩
    · intro x hx
      have hx' : x ∈ D i ∩ closure (K.space \ D i) := (hfr i).symm ▸ hx
      refine ⟨?_, hx'.1⟩
      have hO : IsOpen (⋃ j : {j // j ≠ i}, D j)ᶜ :=
        (isClosed_iUnion_of_finite fun j : {j // j ≠ i} => hDc j).isOpen_compl
      have hxO : x ∈ (⋃ j : {j // j ≠ i}, D j)ᶜ := by
        intro hxU
        obtain ⟨j, hxj⟩ := mem_iUnion.mp hxU
        exact disjoint_left.mp (hdisj j.2) hxj hx'.1
      apply closure_mono (s := (⋃ j : {j // j ≠ i}, D j)ᶜ ∩ (K.space \ D i)) ?_
        (hO.inter_closure ⟨hxO, hx'.2⟩)
      rintro y ⟨hyO, hyK, hyD⟩
      refine ⟨hyK, ?_⟩
      intro hy
      obtain ⟨j, hyj⟩ := mem_iUnion.mp hy
      by_cases hji : j = i
      · exact hyD (hji ▸ hyj)
      · exact hyO (mem_iUnion.mpr ⟨⟨j, hji⟩, hyj⟩)
  have hQnonempty : Q.Nonempty := by
    obtain ⟨i⟩ := hι
    obtain ⟨x, hx⟩ := (hrconn i).nonempty
    exact ⟨x, ((hmeet i).symm ▸ hx).1⟩
  have hcover : Q ∪ ⋃ i, D i = K.space := by
    apply Subset.antisymm (union_subset hQK (iUnion_subset hDK))
    intro x hx
    by_cases hxD : x ∈ ⋃ i, D i
    · exact Or.inr hxD
    · exact Or.inl (subset_closure ⟨hx, hxD⟩)
  have hQc : IsPreconnected Q := by
    have key : ∀ s : Finset ι, IsPreconnected (Q ∪ ⋃ i ∈ s, D i) → IsPreconnected Q := by
      intro s
      induction s using Finset.induction_on with
      | empty => simp
      | insert i s his ih =>
        intro hc
        have heq : Q ∪ ⋃ j ∈ insert i s, D j = (Q ∪ ⋃ j ∈ s, D j) ∪ D i := by
          rw [Finset.set_biUnion_insert]
          ext x
          simp only [mem_union]
          tauto
        rw [heq] at hc
        have hdis : Disjoint (⋃ j ∈ s, D j) (D i) :=
          disjoint_iUnion₂_left.mpr fun j hj => hdisj fun hji => his (hji ▸ hj)
        have hi : (Q ∪ ⋃ j ∈ s, D j) ∩ D i = r i '' stdSimplexBoundary 2 := by
          rw [union_inter_distrib_right, hdis.inter_eq, union_empty, hmeet i]
        exact ih (isPreconnected_left_of_isClosed_union
          (isClosed_closure.union (isClosed_biUnion_finset fun j hj => hDc j)) (hDc i) hc
          (hi.symm ▸ (hrconn i).isPreconnected))
    let _ := Fintype.ofFinite ι
    exact key Finset.univ (by simpa only [Finset.mem_univ, iUnion_true, hcover] using
      hKc.isPreconnected)
  obtain ⟨A, hAfin, hA, hAsp, hAbd⟩ := exists_manifold_disjoint_disk_union hr hdisj
  let _ : Finite A.faces := hAfin.to_subtype
  have hAK : A.space ⊆ K.space := hAsp ▸ iUnion_subset hDK
  obtain ⟨R, hRfin, hR, hRsp, hRbd⟩ :=
    hK.exists_isCombinatorialManifoldWithBoundary_closure_sdiff_two hA hAK
  let _ : Finite R.faces := hRfin.to_subtype
  rw [hAsp] at hRsp
  have hRc : IsConnected R.space := hRsp.symm ▸ ⟨hQnonempty, hQc⟩
  have hdiff : R.space \ (boundaryComplex 2 R).space = K.space \ ⋃ i, D i := by
    rw [hRsp, hRbd, hAbd]
    ext x
    constructor
    · rintro ⟨hxQ, hxB⟩
      refine ⟨hQK hxQ, ?_⟩
      intro hxD
      obtain ⟨i, hxi⟩ := mem_iUnion.mp hxD
      exact hxB (mem_iUnion.mpr ⟨i, hmeet i ▸ ⟨hxQ, hxi⟩⟩)
    · rintro ⟨hxK, hxD⟩
      refine ⟨subset_closure ⟨hxK, hxD⟩, ?_⟩
      intro hxB
      obtain ⟨i, hxi⟩ := mem_iUnion.mp hxB
      exact hxD (mem_iUnion.mpr ⟨i, hrD i hxi⟩)
  rw [← hdiff]
  exact hR.isConnected_sdiff_boundaryComplex_space hRc

theorem IsCombinatorialManifold.isConnected_sdiff_of_isPLBall_two
    {K : Geometry.SimplicialComplex ℝ E} [Finite K.faces]
    (hK : IsCombinatorialManifold 2 K) (hKc : IsConnected K.space) {D : Set E}
    (hD : IsPLBall 2 D) (hDK : D ⊆ K.space) : IsConnected (K.space \ D) := by
  have hdisj : Pairwise fun (_ _ : Unit) => Disjoint D D :=
    fun _ _ h => (h (Subsingleton.elim _ _)).elim
  simpa only [iUnion_const] using
    hK.isConnected_sdiff_iUnion_of_isPLBall_two hKc (D := fun _ : Unit => D)
    (fun _ => hD) (fun _ => hDK) hdisj

end DifferentialGeometry.Topology.PiecewiseLinear
