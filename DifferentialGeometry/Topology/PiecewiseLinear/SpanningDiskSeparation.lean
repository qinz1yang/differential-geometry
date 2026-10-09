/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.SpanningDiskNeighborhood
import DifferentialGeometry.Topology.PiecewiseLinear.SurfaceSpanningDisk
import DifferentialGeometry.Topology.PiecewiseLinear.SurfaceSplitSeparation
import DifferentialGeometry.Topology.PiecewiseLinear.SeparatingSurface

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

open Classical in
theorem IsCombinatorialManifoldWithBoundary.exists_polyhedral_separator_of_spanning_disk
    (S : Geometry.SimplicialComplex ℝ E) [Finite S.faces]
    (hS : IsCombinatorialManifoldWithBoundary 2 S) (hor : IsOrientable 2 S)
    (hdim : Module.finrank ℝ E = 3) {A D U H T : Set E} {r : (Fin 3 → ℝ) → E}
    (hr : IsPLHomeomorphOn r (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) D)
    (hmeet : D ∩ S.space = r '' stdSimplexBoundary 2)
    (hA : IsCompact A) (hAn : A ∈ 𝓝ˢ[S.space] (r '' stdSimplexBoundary 2))
    (hBd : Disjoint (r '' stdSimplexBoundary 2) (boundaryComplex 2 S).space)
    (hU : IsOpen U) (hDU : D ⊆ U) (hAU : A ⊆ U)
    (hH : IsClosed H) (hT : IsClosed T) (hsep : Separates S.space H T)
    (havoid : D ∪ A ⊆ (H ∪ T)ᶜ) :
    ∃ (B P : Geometry.SimplicialComplex ℝ E) (M V Q : Set E) (q : (Fin 3 → ℝ) → E),
      B.faces.Finite ∧ IsPLBall 3 B.space ∧ B.space ⊆ U ∧ Disjoint B.space (H ∪ T) ∧
      P.faces.Finite ∧ IsPLHomeomorphOn q (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) M ∧
      D ⊆ M ∧ M ⊆ (boundaryComplex 3 B).space ∧ M \ D ⊆ S.space ∩ A ∧
      V ⊆ S.space ∩ A ∧ V ⊆ B.space ∧ IsPLBall 2 Q ∧ Q ⊆ (boundaryComplex 3 B).space ∧
      (boundaryComplex 3 B).space = M ∪ Q ∧ M ∩ Q = q '' stdSimplexBoundary 2 ∧
      S.space ∩ B.space = (M ∩ S.space) ∪ V ∧
      frontier B.space = (boundaryComplex 3 B).space ∧
      P.space = closure (S.space \ B.space) ∪ (boundaryComplex 3 B).space ∧
      P.space ∩ B.space = (boundaryComplex 3 B).space ∧
      P.space \ B.space = S.space \ B.space ∧ Separates P.space H T ∧
      (P.space \ S.space).Nonempty := by
  have hD : IsPLBall 2 D := ⟨r, hr⟩
  obtain ⟨D₁, D₂, q₁, q₂, hq₁, hq₂, hD₁, hD₂, hpair, hD₁A, hD₂A, hlocal⟩ :=
    hS.exists_disk_pair_of_spanning_disk S hor hr hmeet hBd hAn
  have hcompact : IsCompact (D ∪ A) := hD.isPolyhedron.isCompact.union hA
  have hDAU : D ∪ A ⊆ U \ (H ∪ T) :=
    fun x hx => ⟨(union_subset hDU hAU) hx, havoid hx⟩
  obtain ⟨L, hLfin, hL, hDAL, hLU⟩ :=
    exists_isCombinatorialManifoldWithBoundary_neighborhood (n := 2) (by simpa using hdim)
      hcompact (hU.sdiff (hH.union hT)) hDAU
  let _ : Finite L.faces := hLfin.to_subtype
  have hD₁L : D₁ ⊆ L.space := hD₁A.trans
    ((union_subset_union Subset.rfl inter_subset_right).trans (hDAL.trans interior_subset))
  have hD₂L : D₂ ⊆ L.space := hD₂A.trans
    ((union_subset_union Subset.rfl inter_subset_right).trans (hDAL.trans interior_subset))
  have hD₁C : D₁ ⊆ S.space ∪ D := hD₁A.trans (by
    rintro x (hx | hx)
    · exact Or.inr hx
    · exact Or.inl hx.1)
  have hD₂C : D₂ ⊆ S.space ∪ D := hD₂A.trans (by
    rintro x (hx | hx)
    · exact Or.inr hx
    · exact Or.inl hx.1)
  have hsepD : Separates (S.space ∪ D) H T := by
    apply hsep.mono ((isPolyhedron_space S).isClosed.union hD.isPolyhedron.isClosed)
      subset_union_left
    · rintro x hx (hxS | hxD)
      · exact hsep.left_subset_compl hx hxS
      · exact havoid (Or.inl hxD) (Or.inl hx)
    · rintro x hx (hxS | hxD)
      · exact hsep.right_subset_compl hx hxS
      · exact havoid (Or.inl hxD) (Or.inr hx)
  have hDboundary : Disjoint D (boundaryComplex 3 L).space := by
    rw [← frontier_space_eq_boundaryComplex_space_of_finrank (n := 2)
      (by simpa using hdim) L hL]
    exact disjoint_left.mpr fun x hx hxF => hxF.2 (hDAL (Or.inl hx))
  have hD₁int : D ⊆ q₁ '' openSimplex (stdVertices 1) := by
    rw [hq₁.image_openSimplex_stdVertices]
    exact hD₁
  have hD₂int : D ⊆ q₂ '' openSimplex (stdVertices 1) := by
    rw [hq₂.image_openSimplex_stdVertices]
    exact hD₂
  obtain ⟨N, B, q, V, Q, C, hBfin, hN, hB, hDN, hNL, -, hNavoid, -, hBN,
    hq, hMB, hV, hVB, hQ, hQB, hboundary, hMQ, -, hCtrace, hC'trace, hout,
    hfront, hCclosed, hCsep⟩ :=
    hL.exists_surface_split_preserving_separation hdim hH hT
      ((isPolyhedron_space S).isClosed.union hD.isPolyhedron.isClosed) hsepD hD hq₁ hq₂
      hD₁int hD₂int (hD₁.trans sdiff_subset) (hD₂.trans sdiff_subset) hpair
      hD₁L hD₂L hD₁C hD₂C hlocal hDboundary
  let _ : Finite B.faces := hBfin.to_subtype
  let M := D₂ ∩ N
  have hDM : D ⊆ M := fun x hx => ⟨(hD₂ hx).1, hDN hx⟩
  have hDB : D ⊆ B.space := hDM.trans (hMB.trans (boundaryComplex_space_subset 3 B))
  have hVM : V ⊆ S.space ∩ A := by
    rw [hV]
    apply inter_subset_right.trans
    apply closure_minimal ?_ ((isPolyhedron_space S).isClosed.inter hA.isClosed)
    rintro x ⟨hx, hxD⟩
    rcases hD₁A hx with hx | hx
    · exact (hxD hx).elim
    · exact hx
  have hMD : M \ D ⊆ S.space ∩ A := by
    rintro x ⟨hx, hxD⟩
    rcases hD₂A hx.1 with hx | hx
    · exact (hxD hx).elim
    · exact hx
  have hSout : C \ B.space = S.space \ B.space := by
    rw [hout]
    ext x
    constructor
    · rintro ⟨hxS | hxD, hxB⟩
      · exact ⟨hxS, hxB⟩
      · exact (hxB (hDB hxD)).elim
    · exact fun hx => ⟨Or.inl hx.1, hx.2⟩
  have hfrontB : frontier B.space = (boundaryComplex 3 B).space :=
    hfront.trans hboundary.symm
  have hCB : C ∩ B.space = (boundaryComplex 3 B).space := hC'trace.trans hboundary.symm
  have hCeq : C = closure (S.space \ B.space) ∪ (boundaryComplex 3 B).space := by
    apply Subset.antisymm
    · intro x hxC
      by_cases hxB : x ∈ B.space
      · exact Or.inr (hCB.subset ⟨hxC, hxB⟩)
      · exact Or.inl (subset_closure ((hSout.subset ⟨hxC, hxB⟩)))
    · apply union_subset
      · apply closure_minimal ?_ hCclosed
        exact fun x hx => (hSout.symm.subset hx).1
      · exact fun x hx => (hCB.symm.subset hx).1
  have hCpoly : IsPolyhedron C := by
    rw [hCeq]
    exact ((isPolyhedron_space S).closure_sdiff hB.isPolyhedron).union
      (isPolyhedron_space (boundaryComplex 3 B))
  obtain ⟨P, hPfin, hPspace⟩ := hCpoly.exists_simplicialComplex
  have hStrace : S.space ∩ B.space = (M ∩ S.space) ∪ V := by
    apply Subset.antisymm
    · intro x hx
      rcases hCtrace.subset ⟨Or.inl hx.1, hx.2⟩ with hxM | hxV
      · exact Or.inl ⟨hxM, hx.1⟩
      · exact Or.inr hxV
    · rintro x (hx | hx)
      · exact ⟨hx.2, boundaryComplex_space_subset 3 B (hMB hx.1)⟩
      · exact ⟨(hVM hx).1, hVB hx⟩
  refine ⟨B, P, M, V, Q, q, hBfin, hB, hBN.trans (hNL.trans (hLU.trans sdiff_subset)),
    disjoint_left.mpr (fun x hx => hNavoid (hBN hx)), hPfin, hq, hDM, hMB, hMD, hVM,
    hVB, hQ, hQB, hboundary, hMQ, hStrace, hfrontB, hPspace.trans hCeq,
    by rwa [hPspace], by rwa [hPspace], hPspace.symm ▸ hCsep, ?_⟩
  have hp : r (stdCenter 1) ∈ D \ r '' stdSimplexBoundary 2 := by
    rw [← hr.image_openSimplex_stdVertices]
    exact mem_image_of_mem r (stdCenter_mem_openSimplex 1)
  refine ⟨r (stdCenter 1), ?_, fun hx => hp.2 (hmeet.subset ⟨hp.1, hx⟩)⟩
  rw [hPspace]
  exact (hCB.symm.subset (hMB (hDM hp.1))).1

open Classical in
theorem IsCommonAnnularDerivedNeighborhood.exists_polyhedral_separator_of_spanning_disk
    {K : Geometry.SimplicialComplex ℝ E}
    (S : Geometry.SimplicialComplex ℝ E) [Finite S.faces]
    (hS : IsCombinatorialManifoldWithBoundary 2 S) (hor : IsOrientable 2 S)
    (hdim : Module.finrank ℝ E = 3) {A D U H T : Set E} {r : (Fin 3 → ℝ) → E}
    (hcommon : IsCommonAnnularDerivedNeighborhood K A (r '' stdSimplexBoundary 2) S.space D)
    (hr : IsPLHomeomorphOn r (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) D)
    (hmeet : D ∩ S.space = r '' stdSimplexBoundary 2)
    (hBd : Disjoint (r '' stdSimplexBoundary 2) (boundaryComplex 2 S).space)
    (hU : IsOpen U) (hDU : D ⊆ U) (hAU : A ⊆ U)
    (hH : IsClosed H) (hT : IsClosed T) (hsep : Separates S.space H T)
    (havoid : D ∪ A ⊆ (H ∪ T)ᶜ) :
    ∃ (B P : Geometry.SimplicialComplex ℝ E) (M V Q : Set E) (q : (Fin 3 → ℝ) → E),
      B.faces.Finite ∧ IsPLBall 3 B.space ∧ B.space ⊆ U ∧ Disjoint B.space (H ∪ T) ∧
      P.faces.Finite ∧ IsPLHomeomorphOn q (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) M ∧
      D ⊆ M ∧ M ⊆ (boundaryComplex 3 B).space ∧ M \ D ⊆ S.space ∩ A ∧
      V ⊆ S.space ∩ A ∧ V ⊆ B.space ∧ IsPLBall 2 Q ∧ Q ⊆ (boundaryComplex 3 B).space ∧
      (boundaryComplex 3 B).space = M ∪ Q ∧ M ∩ Q = q '' stdSimplexBoundary 2 ∧
      S.space ∩ B.space = (M ∩ S.space) ∪ V ∧
      frontier B.space = (boundaryComplex 3 B).space ∧
      P.space = closure (S.space \ B.space) ∪ (boundaryComplex 3 B).space ∧
      P.space ∩ B.space = (boundaryComplex 3 B).space ∧
      P.space \ B.space = S.space \ B.space ∧ Separates P.space H T ∧
      (P.space \ S.space).Nonempty := by
  have hAn : A ∈ 𝓝ˢ[S.space] (r '' stdSimplexBoundary 2) := by
    obtain ⟨R, L, P₀, P₁, -, -, -, -, hRK, -, hP₀, -, hP₀R, -, -, -, -, hn, -⟩ :=
      hcommon
    obtain ⟨O, hO, hJO, hOA⟩ := _root_.mem_nhdsSetWithin.mp hn
    refine _root_.mem_nhdsSetWithin.mpr ⟨O, hO, hJO, ?_⟩
    have hSK : S.space ⊆ K.space := by
      rw [← hP₀]
      exact (space_mono_of_faces_subset hP₀R).trans hRK.space_eq.subset
    exact fun x hx => hOA ⟨hx.1, hSK hx.2⟩
  exact hS.exists_polyhedral_separator_of_spanning_disk S hor hdim hr hmeet
    hcommon.isPolyhedron.isCompact hAn hBd hU hDU hAU hH hT hsep havoid

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
open Classical in
theorem IsSphericalShell.exists_polyhedral_separator_of_spanning_disk
    {X B₀ B₁ : Set (EuclideanSpace ℝ (Fin 3))} (hX : IsSphericalShell X B₀ B₁)
    (S : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3))) [Finite S.faces]
    (hS : IsCombinatorialManifold 2 S) (hconn : IsConnected S.space)
    (hsep : Separates S.space B₀ B₁)
    {D : Set (EuclideanSpace ℝ (Fin 3))} {r : (Fin 3 → ℝ) → EuclideanSpace ℝ (Fin 3)}
    (hr : IsPLHomeomorphOn r (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) D)
    (hmeet : D ∩ S.space = r '' stdSimplexBoundary 2) (hDX : D ⊆ interior X) :
    ∃ K A B P : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3)),
      K.faces.Finite ∧ IsPLBall 3 K.space ∧ A.faces.Finite ∧
      IsCombinatorialManifoldWithBoundary 3 A ∧ IsTopologicalSolidTorus A.space ∧
      r '' stdSimplexBoundary 2 ⊆ interior A.space ∧ A.space ⊆ interior X ∧
      Disjoint A.space B₀ ∧ Disjoint A.space B₁ ∧ (D \ A.space).Nonempty ∧
      IsCommonAnnularDerivedNeighborhood K A.space (r '' stdSimplexBoundary 2) S.space D ∧
      B.faces.Finite ∧ IsPLBall 3 B.space ∧ B.space ⊆ interior X ∧
      Disjoint B.space B₀ ∧ Disjoint B.space B₁ ∧ D ⊆ frontier B.space ∧
      P.faces.Finite ∧ P.space ⊆ interior X ∧
      P.space = closure (S.space \ B.space) ∪ frontier B.space ∧
      P.space ∩ B.space = frontier B.space ∧
      P.space \ B.space = S.space \ B.space ∧ Separates P.space B₀ B₁ ∧
      (P.space \ S.space).Nonempty := by
  classical
  let _ : DecidableEq (EuclideanSpace ℝ (Fin 3)) := Classical.decEq _
  obtain ⟨K, A, hKfin, hK, hAfin, hA, hsolid, hJA, hAX, hA₀, hA₁, hremain, hcommon⟩ :=
    hX.exists_spanning_disk_annular_neighborhood S hS hconn hsep hr hmeet
  have hBd : Disjoint (r '' stdSimplexBoundary 2) (boundaryComplex 2 S).space := by
    apply disjoint_left.mpr
    intro x _ hxB
    obtain ⟨s, hs, _⟩ := (boundaryComplex 2 S).mem_space_iff.mp hxB
    rw [hS.boundaryComplex_faces_eq_empty S] at hs
    exact hs.elim
  have havoid : D ∪ A.space ⊆ (B₀ ∪ B₁)ᶜ := by
    intro x hx hxB
    have hxX := (union_subset hDX hAX) hx
    have hxF := hX.frontier_eq.symm.subset hxB
    exact hxF.2 hxX
  obtain ⟨B, P, M, V, Q, q, hBfin, hB, hBX, hBdis, hPfin, -, hDM, hMB,
    -, -, -, -, -, -, -, -, hfront, hPspace, hPB, hout, hsepP, hnew⟩ :=
    hcommon.exists_polyhedral_separator_of_spanning_disk S
      hS.isCombinatorialManifoldWithBoundary
      (hS.isOrientable_of_finrank_eq_three S (by simp) hconn) (by simp)
      hr hmeet hBd isOpen_interior hDX hAX hX.isCompact_left.isClosed
      hX.isCompact_right.isClosed hsep havoid
  rw [← hfront] at hMB hPspace hPB
  have hPX : P.space ⊆ interior X := by
    rw [hPspace]
    exact union_subset
      ((closure_minimal sdiff_subset (isPolyhedron_space S).isClosed).trans
        (hX.subset_interior_of_separates hconn.isPreconnected hsep))
      (hB.isPolyhedron.isClosed.frontier_subset.trans hBX)
  exact ⟨K, A, B, P, hKfin, hK, hAfin, hA, hsolid, hJA, hAX, hA₀, hA₁, hremain,
    hcommon, hBfin, hB, hBX, hBdis.mono_right subset_union_left,
    hBdis.mono_right subset_union_right, hDM.trans hMB, hPfin, hPX, hPspace,
    hPB, hout, hsepP, hnew⟩

end DifferentialGeometry.Topology.PiecewiseLinear
