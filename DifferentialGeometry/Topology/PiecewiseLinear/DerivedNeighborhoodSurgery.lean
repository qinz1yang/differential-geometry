/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.DerivedNeighborhoodManifold
import DifferentialGeometry.Topology.PiecewiseLinear.DerivedNeighborhoodRestriction
import DifferentialGeometry.Topology.PiecewiseLinear.ExistsIsPLBallSupersetOfExteriorCompression
import DifferentialGeometry.Topology.PiecewiseLinear.FrontierBoundary
import DifferentialGeometry.Topology.PiecewiseLinear.ManifoldComplement
import DifferentialGeometry.Topology.PiecewiseLinear.ManifoldInvariance
import DifferentialGeometry.Topology.PiecewiseLinear.SeparatingSurface

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

open Classical in
theorem exists_face_meets_of_mem_derivedNeighborhood_space
    {K L : Geometry.SimplicialComplex ℝ E} {x : E}
    (hx : x ∈ (derivedNeighborhood K L).space) :
    ∃ σ ∈ K.faces, (convexHull ℝ (σ : Set E) ∩ L.space).Nonempty ∧
      x ∈ convexHull ℝ (σ : Set E) := by
  obtain ⟨u, hu, hxu⟩ := (derivedNeighborhood K L).mem_space_iff.mp hx
  obtain ⟨d, hd, hne, hL, rfl⟩ := (mem_derivedNeighborhood_faces_iff K L).mp hu
  obtain ⟨e, he, htop⟩ := hd.exists_top hne
  obtain ⟨τ, hτ, hτe⟩ := hL e he
  obtain ⟨σ, hσ, heσ⟩ :=
    (barycentricSubdivision_isSubdivision K).exists_face_subset (hd.mem_faces he)
  refine ⟨σ, hσ, ⟨τ.centroid ℝ id, heσ (subset_convexHull ℝ (e : Set E)
    (Finset.mem_coe.mpr hτe)), L.convexHull_subset_space hτ
      (τ.centroid_mem_convexHull (L.nonempty_of_mem_faces hτ))⟩, ?_⟩
  exact heσ (convexHull_image_subset (barycentricSubdivision K)
    (centroid_mem_openSimplex_of_mem_faces _) hd htop hxu)

theorem subset_of_isPreconnected_of_eq_inter {Y : Type*} [TopologicalSpace Y] {A S W R : Set Y}
    (hA : IsPreconnected A) (hAS : A ⊆ S) (hW : IsOpen W) (hR : R = W ∩ S) (hRc : IsClosed R)
    (hne : (A ∩ R).Nonempty) : A ⊆ R := by
  subst hR
  rcases isPreconnected_iff_subset_of_disjoint.mp hA W (W ∩ S)ᶜ hW hRc.isOpen_compl
    (fun y hy => by
      by_cases hyR : y ∈ W ∩ S
      · exact Or.inl hyR.1
      · exact Or.inr hyR)
    (by
      rw [Set.eq_empty_iff_forall_notMem]
      rintro y ⟨hyA, hyW, hyR⟩
      exact hyR ⟨hyW, hAS hyA⟩) with h | h
  · exact fun y hy => ⟨h hy, hAS hy⟩
  · obtain ⟨y, hyA, hyR⟩ := hne
    exact (h hyA hyR).elim

open Classical in
theorem derivedNeighborhood_space_inter_subset_of_eq_inter
    {K S L : Geometry.SimplicialComplex ℝ E} (hS : S.faces ⊆ K.faces) {W : Set E}
    (hW : IsOpen W) (hL : L.space = W ∩ S.space) (hLc : IsClosed L.space) :
    (derivedNeighborhood K L).space ∩ S.space ⊆ L.space := by
  rw [derivedNeighborhood_space_inter_subcomplex K S L hS]
  intro x hx
  obtain ⟨σ, hσ, hne, hxσ⟩ := exists_face_meets_of_mem_derivedNeighborhood_space hx
  exact subset_of_isPreconnected_of_eq_inter (convex_convexHull ℝ _).isPreconnected
    (S.convexHull_subset_space hσ) hW hL hLc hne hxσ

theorem restrict_space_eq_of_eq_inter {K S : Geometry.SimplicialComplex ℝ E}
    (hS : S.faces ⊆ K.faces) {W R : Set E} (hW : IsOpen W) (hR : R = W ∩ S.space)
    (hRc : IsClosed R) : (restrict K R).space = R ∧ (restrict K R).faces ⊆ S.faces := by
  have hRS : R ⊆ S.space := hR ▸ inter_subset_right
  have hfaces : (restrict K R).faces ⊆ S.faces := by
    intro σ hσ
    exact ((mem_restrict_faces_iff_of_faces_subset K K S subset_rfl hS).mp
      ⟨hσ.1, hσ.2.trans hRS⟩).2
  refine ⟨Subset.antisymm (restrict_space_subset K R) fun x hxR => ?_, hfaces⟩
  obtain ⟨σ, hσ, hxσ⟩ := S.mem_space_iff.mp (hRS hxR)
  have hσR := subset_of_isPreconnected_of_eq_inter (convex_convexHull ℝ _).isPreconnected
    (S.convexHull_subset_space hσ) hW hR hRc ⟨x, hxσ, hxR⟩
  exact (restrict K R).convexHull_subset_space ⟨hS hσ, hσR⟩ hxσ

theorem exists_isSubdivision_restrict_space_diam_lt [FiniteDimensional ℝ E]
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces] {P Q : Set E} (hP : IsPolyhedron P)
    (hPK : P ⊆ K.space) (hQ : IsPolyhedron Q) (hQK : Q ⊆ K.space) {ε : ℝ} (hε : 0 < ε) :
    ∃ T : Geometry.SimplicialComplex ℝ E, IsSubdivision T K ∧ T.faces.Finite ∧
      (restrict T P).space = P ∧ (restrict T Q).space = Q ∧
        ∀ s ∈ T.faces, Metric.diam (convexHull ℝ (s : Set E)) < ε := by
  obtain ⟨K₁, hK₁, hK₁fin, hP₁⟩ := exists_isSubdivision_restrict_space K hP hPK
  have : Finite K₁.faces := hK₁fin.to_subtype
  obtain ⟨K₂, hK₂, hK₂fin, hQ₂⟩ :=
    exists_isSubdivision_restrict_space K₁ hQ (by rw [hK₁.space_eq]; exact hQK)
  have : Finite K₂.faces := hK₂fin.to_subtype
  have hP₂ : (restrict K₂ P).space = P := by
    have h := (hK₂.restrict (restrict K₁ P) (restrict_faces_subset K₁ P)).space_eq
    rwa [hP₁] at h
  obtain ⟨N, hN⟩ := ((Set.toFinite K₂.faces).image (fun s : Finset E => s.card)).bddAbove
  have hcard : ∀ s ∈ K₂.faces, s.card ≤ N + 1 :=
    fun s hs => (hN (mem_image_of_mem _ hs)).trans (Nat.le_succ N)
  obtain ⟨T, hT, hTfin, -, hdiam⟩ := exists_isSubdivision_diam_lt K₂ hcard hε
  have hPT : (restrict T P).space = P := by
    have h := (hT.restrict (restrict K₂ P) (restrict_faces_subset K₂ P)).space_eq
    rwa [hP₂] at h
  have hQT : (restrict T Q).space = Q := by
    have h := (hT.restrict (restrict K₂ Q) (restrict_faces_subset K₂ Q)).space_eq
    rwa [hQ₂] at h
  exact ⟨T, hT.trans (hK₂.trans hK₁), hTfin, hPT, hQT, hdiam⟩

open Classical in
theorem derivedNeighborhood_space_subset_cthickening
    {K L : Geometry.SimplicialComplex ℝ E} {ε : ℝ}
    (hdiam : ∀ s ∈ K.faces, Metric.diam (convexHull ℝ (s : Set E)) < ε) :
    (derivedNeighborhood K L).space ⊆ Metric.cthickening ε L.space := by
  intro x hx
  obtain ⟨σ, hσ, ⟨y, hyσ, hyL⟩, hxσ⟩ := exists_face_meets_of_mem_derivedNeighborhood_space hx
  refine Metric.mem_cthickening_of_dist_le x y ε L.space hyL ?_
  exact ((Metric.dist_le_diam_of_mem (σ.finite_toSet.isCompact_convexHull ℝ).isBounded hxσ
    hyσ).trans (hdiam σ hσ).le)

variable [FiniteDimensional ℝ E]

open Classical in
theorem IsCombinatorialManifoldWithBoundary.complement_derivedNeighborhood
    {K : Geometry.SimplicialComplex ℝ E} [Finite K.faces]
    (hK : IsCombinatorialManifoldWithBoundary 3 K) (L : Geometry.SimplicialComplex ℝ E) :
    IsCombinatorialManifoldWithBoundary 3 (subcomplexGeneratedBy (PiecewiseLinear.secondDerived K)
        (PiecewiseLinear.derivedNeighborhood K L).facesᶜ) ∧
      (subcomplexGeneratedBy (PiecewiseLinear.secondDerived K)
        (PiecewiseLinear.derivedNeighborhood K L).facesᶜ).space =
          closure (K.space \ (PiecewiseLinear.derivedNeighborhood K L).space) := by
  have : Finite (PiecewiseLinear.derivedNeighborhood K L).faces :=
    (derivedNeighborhood_faces_finite K L).to_subtype
  have : Finite (boundaryComplex 3 K).faces := (boundaryComplex_faces_finite 3 K).to_subtype
  have hK₂ : IsCombinatorialManifoldWithBoundary 3 (PiecewiseLinear.secondDerived K) :=
    hK.of_isSubdivision (secondDerived_isSubdivision K)
  have hN : IsCombinatorialManifoldWithBoundary 3 (PiecewiseLinear.derivedNeighborhood K L) :=
    hK.derivedNeighborhood (n := 2) L
  have hbd := boundaryComplex_space_of_isSubdivision (n := 2) K (PiecewiseLinear.secondDerived K)
    hK (secondDerived_isSubdivision K)
  have hB : IsCombinatorialManifoldWithBoundary 2 (boundaryComplex 3 K) :=
    (isCombinatorialManifold_boundaryComplex (n := 2) K hK).isCombinatorialManifoldWithBoundary
  have hD : IsCombinatorialManifoldWithBoundary 2
      (restrict (PiecewiseLinear.derivedNeighborhood K L)
        (boundaryComplex 3 (PiecewiseLinear.secondDerived K)).space) := by
    rw [hbd, restrict_derivedNeighborhood_eq K (boundaryComplex 3 K) L
      (boundaryComplex_faces_subset 3 K)]
    exact hB.derivedNeighborhood (n := 1) L
  refine ⟨hK₂.complement (PiecewiseLinear.secondDerived K) (PiecewiseLinear.derivedNeighborhood K L)
    hN (derivedNeighborhood_faces_subset K L) hD, ?_⟩
  rw [← closure_space_sdiff_space_eq_subcomplexGeneratedBy (PiecewiseLinear.secondDerived K)
    (PiecewiseLinear.secondDerived K) (PiecewiseLinear.derivedNeighborhood K L) subset_rfl
    (derivedNeighborhood_faces_subset K L), (secondDerived_isSubdivision K).space_eq]

open Classical in
theorem IsCombinatorialManifoldWithBoundary.exists_remove_of_eq_inter
    {X : Geometry.SimplicialComplex ℝ E} [Finite X.faces]
    (hX : IsCombinatorialManifoldWithBoundary 3 X) {G R U W : Set E} (hG : IsPolyhedron G)
    (hU : IsOpen U) (hW : IsOpen W) (hR : R = W ∩ (G ∩ X.space)) (hRc : IsCompact R)
    (hRU : R ⊆ U) :
    ∃ X' : Geometry.SimplicialComplex ℝ E, X'.faces.Finite ∧
      IsCombinatorialManifoldWithBoundary 3 X' ∧
        (∃ Z : Set E, IsClosed Z ∧ Z ⊆ U ∧ X'.space \ Z = X.space \ Z) ∧
          G ∩ X'.space = (G ∩ X.space) \ R ∧
            ∀ x ∈ G ∩ interior X.space, x ∉ R → x ∈ interior X'.space := by
  obtain ⟨ε, hε, hεU⟩ := hRc.exists_cthickening_subset_open hU hRU
  have hGX : IsPolyhedron (G ∩ X.space) := hG.inter (isPolyhedron_space X)
  obtain ⟨T, hT, hTfin, hTG, -, hdiam⟩ := exists_isSubdivision_restrict_space_diam_lt X hGX
    inter_subset_right hGX inter_subset_right hε
  have : Finite T.faces := hTfin.to_subtype
  have hTm : IsCombinatorialManifoldWithBoundary 3 T := hX.of_isSubdivision hT
  have hTsp : T.space = X.space := hT.space_eq
  have hRS : R = W ∩ (restrict T (G ∩ X.space)).space := by rw [hTG]; exact hR
  obtain ⟨hLsp, hLS⟩ := restrict_space_eq_of_eq_inter (restrict_faces_subset T (G ∩ X.space))
    hW hRS hRc.isClosed
  have hLT : (restrict T R).faces ⊆ T.faces := restrict_faces_subset T R
  set Nb := PiecewiseLinear.derivedNeighborhood T (restrict T R) with hNbdef
  have : Finite Nb.faces := (derivedNeighborhood_faces_finite T _).to_subtype
  have hNbc : IsClosed Nb.space := (isPolyhedron_space _).isCompact.isClosed
  have hNbZ : Nb.space ⊆ Metric.cthickening ε R := by
    rw [← hLsp]
    exact derivedNeighborhood_space_subset_cthickening hdiam
  have hNbG : ∀ x ∈ G ∩ X.space, x ∈ Nb.space → x ∈ R := by
    intro x hx hxN
    have h := derivedNeighborhood_space_inter_subset_of_eq_inter (K := T)
      (restrict_faces_subset T (G ∩ X.space)) hW (hLsp.trans hRS) (hLsp.symm ▸ hRc.isClosed)
      ⟨hxN, by rw [hTG]; exact hx⟩
    rwa [hLsp] at h
  obtain ⟨hX'm, hX'sp⟩ := hTm.complement_derivedNeighborhood (restrict T R)
  set X' := subcomplexGeneratedBy (PiecewiseLinear.secondDerived T) Nb.facesᶜ with hX'def
  have hX'X : X'.space ⊆ X.space := by
    rw [hX'sp, ← hTsp]
    exact closure_minimal sdiff_subset (isPolyhedron_space T).isCompact.isClosed
  have hRX' : ∀ x ∈ R, x ∉ X'.space := by
    intro x hx hxX'
    rw [hX'sp] at hxX'
    obtain ⟨u, hu, hsub⟩ := mem_nhdsWithin_iff_exists_mem_nhds_inter.mp
      (derivedNeighborhood_mem_nhdsWithin hLT (hLsp.symm ▸ hx))
    obtain ⟨y, hyu, hyT, hyN⟩ := mem_closure_iff_nhds.mp hxX' u hu
    exact hyN (hsub ⟨hyu, hyT⟩)
  refine ⟨X', subcomplexGeneratedBy_faces_finite _ _, hX'm, ⟨Metric.cthickening ε R,
    Metric.isClosed_cthickening, hεU, ?_⟩, ?_, ?_⟩
  · ext x
    constructor
    · rintro ⟨hx, hxZ⟩
      exact ⟨hX'X hx, hxZ⟩
    · rintro ⟨hx, hxZ⟩
      refine ⟨?_, hxZ⟩
      rw [hX'sp]
      exact subset_closure ⟨hTsp.symm ▸ hx, fun hN => hxZ (hNbZ hN)⟩
  · ext x
    constructor
    · rintro ⟨hxG, hxX'⟩
      exact ⟨⟨hxG, hX'X hxX'⟩, fun hxR => hRX' x hxR hxX'⟩
    · rintro ⟨⟨hxG, hxX⟩, hxR⟩
      refine ⟨hxG, ?_⟩
      rw [hX'sp]
      exact subset_closure ⟨hTsp.symm ▸ hxX, fun hN => hxR (hNbG x ⟨hxG, hxX⟩ hN)⟩
  · rintro x ⟨hxG, hxi⟩ hxR
    have hxN : x ∉ Nb.space := fun hN => hxR (hNbG x ⟨hxG, interior_subset hxi⟩ hN)
    refine mem_interior.mpr ⟨interior X.space ∩ Nb.spaceᶜ,
      fun y hy => ?_, isOpen_interior.inter hNbc.isOpen_compl, ⟨hxi, hxN⟩⟩
    rw [hX'sp]
    exact subset_closure ⟨hTsp.symm ▸ interior_subset hy.1, hy.2⟩

open Classical in
theorem IsCombinatorialManifoldWithBoundary.exists_add_of_eq_inter
    (hdim : Module.finrank ℝ E = 3) {X : Geometry.SimplicialComplex ℝ E} [Finite X.faces]
    (hX : IsCombinatorialManifoldWithBoundary 3 X) {G R U W : Set E} (hG : IsPolyhedron G)
    (hU : IsOpen U) (hW : IsOpen W) (hR : R = W ∩ (G \ interior X.space)) (hRc : IsCompact R)
    (hRU : R ⊆ U) :
    ∃ X' : Geometry.SimplicialComplex ℝ E, X'.faces.Finite ∧
      IsCombinatorialManifoldWithBoundary 3 X' ∧
        (∃ Z : Set E, IsClosed Z ∧ Z ⊆ U ∧ X'.space \ Z = X.space \ Z) ∧
          G ∩ X'.space = G ∩ X.space ∪ R ∧ R ⊆ interior X'.space ∧ X.space ⊆ X'.space := by
  have hXc : IsCompact X.space := (isPolyhedron_space X).isCompact
  obtain ⟨A, hAfin, hA, hXGA, -⟩ := exists_isCombinatorialManifoldWithBoundary_neighborhood
    (n := 2) hdim (hXc.union hG.isCompact) isOpen_univ (subset_univ _)
  have : Finite A.faces := hAfin.to_subtype
  have hRG : R ⊆ G := fun x hx => (hR ▸ hx : x ∈ W ∩ (G \ interior X.space)).2.1
  have hGA : G ⊆ interior A.space := subset_union_right.trans hXGA
  have hXA : X.space ⊆ interior A.space := subset_union_left.trans hXGA
  obtain ⟨ε, hε, hεU⟩ := hRc.exists_cthickening_subset_open (hU.inter isOpen_interior)
    (subset_inter hRU (hRG.trans hGA))
  obtain ⟨T, hT, hTfin, hTX, hTG, hdiam⟩ := exists_isSubdivision_restrict_space_diam_lt A
    (isPolyhedron_space X) (hXA.trans interior_subset) hG (hGA.trans interior_subset) hε
  have : Finite T.faces := hTfin.to_subtype
  have hTm : IsCombinatorialManifoldWithBoundary 3 T := hA.of_isSubdivision hT
  have hTsp : T.space = A.space := hT.space_eq
  have : Finite (restrict T X.space).faces := (restrict_faces_finite T X.space).to_subtype
  have hTXm : IsCombinatorialManifoldWithBoundary 3 (restrict T X.space) := by
    refine hX.of_isPLHomeomorphOn (f := id) ?_
    rw [hTX]
    exact (isPolyhedron_space X).isPLHomeomorphOn_id
  have hTXT : (restrict T X.space).faces ⊆ T.faces := restrict_faces_subset T X.space
  have hbdT : (boundaryComplex 3 T).space = frontier A.space := by
    rw [← frontier_space_eq_boundaryComplex_space_of_finrank (n := 2) hdim T hTm, hTsp]
  have hDempty : IsCombinatorialManifoldWithBoundary 2
      (restrict (restrict T X.space) (boundaryComplex 3 T).space) := by
    intro v hv
    exfalso
    have hvv : v ∈ convexHull ℝ (({v} : Finset E) : Set E) :=
      subset_convexHull ℝ _ (Finset.mem_coe.mpr (Finset.mem_singleton_self v))
    have hvX : v ∈ X.space := hTX ▸ (restrict T X.space).convexHull_subset_space hv.1 hvv
    have hvB : v ∈ (boundaryComplex 3 T).space := hv.2 hvv
    rw [hbdT] at hvB
    exact hvB.2 (hXA hvX)
  set Y := subcomplexGeneratedBy T (restrict T X.space).facesᶜ with hYdef
  have : Finite Y.faces := (subcomplexGeneratedBy_faces_finite T _).to_subtype
  have hYm : IsCombinatorialManifoldWithBoundary 3 Y :=
    hTm.complement T (restrict T X.space) hTXm hTXT hDempty
  have hYT : Y.faces ⊆ T.faces := subcomplexGeneratedBy_faces_subset T _
  have hYsp : Y.space = closure (A.space \ X.space) := by
    rw [← closure_space_sdiff_space_eq_subcomplexGeneratedBy T T (restrict T X.space) subset_rfl
      hTXT, hTsp, hTX]
  have hYint : Disjoint Y.space (interior X.space) := by
    rw [hYsp]
    exact (Set.disjoint_left.mpr fun x hx hxi => hx.2 (interior_subset hxi)).closure_left
      isOpen_interior
  have hmemY : ∀ x ∈ interior A.space, x ∉ interior X.space → x ∈ Y.space := by
    intro x hxA hxX
    rw [hYsp, mem_closure_iff_nhds]
    intro t ht
    have hxc : x ∈ closure X.spaceᶜ := by
      rw [closure_compl]
      exact hxX
    obtain ⟨y, hyt, hyX⟩ := mem_closure_iff_nhds.mp hxc (t ∩ interior A.space)
      (Filter.inter_mem ht (isOpen_interior.mem_nhds hxA))
    exact ⟨y, hyt.1, interior_subset hyt.2, hyX⟩
  have hTGT : (restrict T G).faces ⊆ T.faces := restrict_faces_subset T G
  have hSY : (restrict Y (restrict T G).space).faces ⊆ Y.faces :=
    restrict_faces_subset Y (restrict T G).space
  have hSsp : (restrict Y (restrict T G).space).space = Y.space ∩ G := by
    rw [restrict_space_eq_inter_of_faces_subset T Y (restrict T G) hYT hTGT, hTG]
  have hGY : G ∩ Y.space = G \ interior X.space := by
    ext x
    constructor
    · rintro ⟨hxG, hxY⟩
      exact ⟨hxG, fun hxi => Set.disjoint_left.mp hYint hxY hxi⟩
    · rintro ⟨hxG, hxi⟩
      exact ⟨hxG, hmemY x (hGA hxG) hxi⟩
  have hRS : R = W ∩ (restrict Y (restrict T G).space).space := by
    rw [hSsp, inter_comm Y.space G, hGY]
    exact hR
  obtain ⟨hLsp, hLS⟩ := restrict_space_eq_of_eq_inter hSY hW hRS hRc.isClosed
  have hLY : (restrict Y R).faces ⊆ Y.faces := hLS.trans hSY
  set Nb := PiecewiseLinear.derivedNeighborhood Y (restrict Y R) with hNbdef
  have : Finite Nb.faces := (derivedNeighborhood_faces_finite Y _).to_subtype
  have hNbY : Nb.space ⊆ Y.space := derivedNeighborhood_space_subset Y (restrict Y R)
  have hNbZ : Nb.space ⊆ Metric.cthickening ε R := by
    rw [← hLsp]
    exact derivedNeighborhood_space_subset_cthickening fun s hs => hdiam s (hYT hs)
  have hNbG : ∀ x ∈ G, x ∈ Nb.space → x ∈ R := by
    intro x hxG hxN
    have h := derivedNeighborhood_space_inter_subset_of_eq_inter (K := Y) hSY hW
      (hLsp.trans hRS) (hLsp.symm ▸ hRc.isClosed)
      ⟨hxN, by rw [hSsp]; exact ⟨hNbY hxN, hxG⟩⟩
    rwa [hLsp] at h
  obtain ⟨hY₁m, hY₁sp⟩ := hYm.complement_derivedNeighborhood (restrict Y R)
  set Y₁ := subcomplexGeneratedBy (PiecewiseLinear.secondDerived Y) Nb.facesᶜ with hY₁def
  have : Finite Y₁.faces := (subcomplexGeneratedBy_faces_finite _ _).to_subtype
  have hY₁T₂ : Y₁.faces ⊆ (PiecewiseLinear.secondDerived T).faces :=
    (subcomplexGeneratedBy_faces_subset _ _).trans (secondDerived_faces_subset hYT)
  have hT₂m : IsCombinatorialManifoldWithBoundary 3 (PiecewiseLinear.secondDerived T) :=
    hTm.of_isSubdivision (secondDerived_isSubdivision T)
  have hT₂sp : (PiecewiseLinear.secondDerived T).space = A.space :=
    (secondDerived_isSubdivision T).space_eq.trans hTsp
  have hZA : Metric.cthickening ε R ⊆ interior A.space := hεU.trans inter_subset_right
  have hfrY₁ : frontier A.space ⊆ Y₁.space := by
    intro x hx
    have hxA : x ∈ A.space := (isPolyhedron_space A).isClosed.frontier_subset hx
    have hxX : x ∉ X.space := fun h => hx.2 (hXA h)
    have hxY : x ∈ Y.space := by
      rw [hYsp]
      exact subset_closure ⟨hxA, hxX⟩
    rw [hY₁sp]
    exact subset_closure ⟨hxY, fun h => hx.2 (hZA (hNbZ h))⟩
  have hbdT₂ : (boundaryComplex 3 (PiecewiseLinear.secondDerived T)).space = frontier A.space := by
    rw [← frontier_space_eq_boundaryComplex_space_of_finrank (n := 2) hdim _ hT₂m, hT₂sp]
  have hDbd : IsCombinatorialManifoldWithBoundary 2
      (restrict Y₁ (boundaryComplex 3 (PiecewiseLinear.secondDerived T)).space) := by
    have heq : restrict Y₁ (boundaryComplex 3 (PiecewiseLinear.secondDerived T)).space =
        boundaryComplex 3 (PiecewiseLinear.secondDerived T) := by
      ext σ
      rw [mem_restrict_faces_iff_of_faces_subset (PiecewiseLinear.secondDerived T) Y₁ _ hY₁T₂
        (boundaryComplex_faces_subset 3 _)]
      refine ⟨fun h => h.2, fun h => ⟨?_, h⟩⟩
      have hσ : convexHull ℝ (σ : Set E) ⊆ Y₁.space :=
        ((boundaryComplex 3 (PiecewiseLinear.secondDerived T)).convexHull_subset_space h).trans
          (hbdT₂.symm ▸ hfrY₁)
      exact ((mem_restrict_faces_iff_of_faces_subset (PiecewiseLinear.secondDerived T)
        (PiecewiseLinear.secondDerived T) Y₁ subset_rfl hY₁T₂).mp
          ⟨boundaryComplex_faces_subset 3 _ h, hσ⟩).2
    rw [heq]
    exact (isCombinatorialManifold_boundaryComplex (n := 2) _
      hT₂m).isCombinatorialManifoldWithBoundary
  have hX'm := hT₂m.complement (PiecewiseLinear.secondDerived T) Y₁ hY₁m hY₁T₂ hDbd
  set X' := subcomplexGeneratedBy (PiecewiseLinear.secondDerived T) Y₁.facesᶜ with hX'def
  have hX'sp : X'.space = closure (A.space \ Y₁.space) := by
    rw [← closure_space_sdiff_space_eq_subcomplexGeneratedBy (PiecewiseLinear.secondDerived T)
      (PiecewiseLinear.secondDerived T) Y₁ subset_rfl hY₁T₂, hT₂sp]
  have hY₁Y : Y₁.space ⊆ Y.space := by
    rw [hY₁sp]
    exact closure_minimal sdiff_subset (isPolyhedron_space Y).isCompact.isClosed
  have hXX' : X.space ⊆ X'.space := by
    refine (hX.subset_closure_interior_space hdim).trans ?_
    rw [hX'sp]
    refine closure_mono fun y hy => ⟨interior_subset (hXA (interior_subset hy)), fun hyY₁ => ?_⟩
    exact Set.disjoint_left.mp hYint (hY₁Y hyY₁) hy
  have hout : ∀ x ∈ X'.space, x ∉ X.space → x ∈ Nb.space := by
    intro x hx hxX
    by_contra hxN
    rw [hX'sp] at hx
    obtain ⟨y, ⟨hyX, hyN⟩, hyA, hyY₁⟩ := mem_closure_iff_nhds.mp hx (X.spaceᶜ ∩ Nb.spaceᶜ)
      ((isPolyhedron_space X).isClosed.isOpen_compl.inter
        (isPolyhedron_space Nb).isClosed.isOpen_compl |>.mem_nhds ⟨hxX, hxN⟩)
    have hyY : y ∈ Y.space := by
      rw [hYsp]
      exact subset_closure ⟨hyA, hyX⟩
    exact hyY₁ (by rw [hY₁sp]; exact subset_closure ⟨hyY, hyN⟩)
  have hRint : R ⊆ interior X'.space := by
    intro x hx
    obtain ⟨u, hu, hsub⟩ := mem_nhdsWithin_iff_exists_mem_nhds_inter.mp
      (derivedNeighborhood_mem_nhdsWithin hLY (hLsp.symm ▸ hx))
    refine mem_interior.mpr ⟨interior u ∩ interior A.space, fun y hy => ?_,
      isOpen_interior.inter isOpen_interior,
      ⟨mem_interior_iff_mem_nhds.mpr hu, hGA (hRG hx)⟩⟩
    rw [hX'sp]
    refine subset_closure ⟨interior_subset hy.2, fun hyY₁ => ?_⟩
    rw [hY₁sp] at hyY₁
    obtain ⟨z, hzu, hzY, hzN⟩ := mem_closure_iff_nhds.mp hyY₁ (interior u)
      (isOpen_interior.mem_nhds hy.1)
    exact hzN (hsub ⟨interior_subset hzu, hzY⟩)
  refine ⟨X', subcomplexGeneratedBy_faces_finite _ _, hX'm, ⟨Metric.cthickening ε R,
    Metric.isClosed_cthickening, hεU.trans inter_subset_left, ?_⟩, ?_, hRint, hXX'⟩
  · ext x
    constructor
    · rintro ⟨hx, hxZ⟩
      by_contra hxX
      exact hxZ (hNbZ (hout x hx fun h => hxX ⟨h, hxZ⟩))
    · rintro ⟨hx, hxZ⟩
      exact ⟨hXX' hx, hxZ⟩
  · ext x
    constructor
    · rintro ⟨hxG, hxX'⟩
      by_cases hxX : x ∈ X.space
      · exact Or.inl ⟨hxG, hxX⟩
      · exact Or.inr (hNbG x hxG (hout x hxX' hxX))
    · rintro (⟨hxG, hxX⟩ | hxR)
      · exact ⟨hxG, hXX' hxX⟩
      · exact ⟨hRG hxR, interior_subset (hRint hxR)⟩

theorem IsCombinatorialManifoldWithBoundary.exists_add_remove_of_eq_inter
    (hdim : Module.finrank ℝ E = 3) {X : Geometry.SimplicialComplex ℝ E} [Finite X.faces]
    (hX : IsCombinatorialManifoldWithBoundary 3 X) {G R R' U W W' : Set E}
    (hG : IsPolyhedron G) (hU : IsOpen U) (hW : IsOpen W)
    (hR : R = W ∩ (G \ interior X.space)) (hRc : IsCompact R) (hRU : R ⊆ U) (hW' : IsOpen W')
    (hR' : R' = W' ∩ (G ∩ X.space)) (hR'c : IsCompact R') (hR'U : R' ⊆ U)
    (hRR' : Disjoint R R') :
    ∃ X' : Geometry.SimplicialComplex ℝ E, X'.faces.Finite ∧
      IsCombinatorialManifoldWithBoundary 3 X' ∧
        (∃ Z : Set E, IsClosed Z ∧ Z ⊆ U ∧ X'.space \ Z = X.space \ Z) ∧
          G ∩ X'.space = (G ∩ X.space ∪ R) \ R' ∧
            ∀ x ∈ G, x ∈ interior X.space ∪ R → x ∉ R' → x ∈ interior X'.space := by
  obtain ⟨X₁, hX₁fin, hX₁, ⟨Z₁, hZ₁, hZ₁U, hZ₁eq⟩, hGX₁, hRint, hXX₁⟩ :=
    hX.exists_add_of_eq_inter hdim hG hU hW hR hRc hRU
  have : Finite X₁.faces := hX₁fin.to_subtype
  have hR'₁ : R' = (W' ∩ Rᶜ) ∩ (G ∩ X₁.space) := by
    rw [hGX₁]
    ext x
    constructor
    · intro hx
      have hx' : x ∈ W' ∩ (G ∩ X.space) := hR' ▸ hx
      exact ⟨⟨hx'.1, fun hxR => Set.disjoint_left.mp hRR' hxR hx⟩, Or.inl hx'.2⟩
    · rintro ⟨⟨hxW, hxR⟩, hxGX | hxR'⟩
      · exact hR' ▸ ⟨hxW, hxGX⟩
      · exact (hxR hxR').elim
  obtain ⟨X₂, hX₂fin, hX₂, ⟨Z₂, hZ₂, hZ₂U, hZ₂eq⟩, hGX₂, hint₂⟩ :=
    hX₁.exists_remove_of_eq_inter hG hU (hW'.inter hRc.isClosed.isOpen_compl) hR'₁ hR'c hR'U
  refine ⟨X₂, hX₂fin, hX₂, ⟨Z₁ ∪ Z₂, hZ₁.union hZ₂, union_subset hZ₁U hZ₂U, ?_⟩, ?_, ?_⟩
  · calc X₂.space \ (Z₁ ∪ Z₂) = X₂.space \ (Z₂ ∪ Z₁) := by rw [union_comm]
      _ = (X₂.space \ Z₂) \ Z₁ := Set.sdiff_sdiff.symm
      _ = (X₁.space \ Z₂) \ Z₁ := by rw [hZ₂eq]
      _ = (X₁.space \ Z₁) \ Z₂ := Set.sdiff_sdiff_comm
      _ = (X.space \ Z₁) \ Z₂ := by rw [hZ₁eq]
      _ = X.space \ (Z₁ ∪ Z₂) := Set.sdiff_sdiff
  · rw [hGX₂, hGX₁]
  · intro x hxG hx hxR'
    have hx₁ : x ∈ interior X₁.space :=
      hx.elim (fun h => interior_mono hXX₁ h) (fun h => hRint h)
    exact hint₂ x ⟨hxG, hx₁⟩ hxR'

end DifferentialGeometry.Topology.PiecewiseLinear
