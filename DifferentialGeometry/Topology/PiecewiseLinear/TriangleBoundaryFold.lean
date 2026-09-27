/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.TriangleBoundaryMove

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

open Classical in
theorem exists_isPLHomeomorphOn_disk_boundary_two_edge_deletion
    (K L : Geometry.SimplicialComplex ℝ E) [Finite K.faces] [Finite L.faces]
    (hK : IsPLBall 2 K.space) (hL : IsPLBall 2 L.space)
    {a b c : E} (hab : a ≠ b) (hca : c ≠ a) (hcb : c ≠ b)
    (ht : ({c, a, b} : Finset E) ∈ K.faces)
    (htrace : (boundaryComplex 2 K).space ∩ convexHull ℝ ({c, a, b} : Set E) =
      segment ℝ a c ∪ segment ℝ c b)
    (hLspace : L.space = closure (K.space \ convexHull ℝ ({c, a, b} : Set E)))
    {C : Set E} (hC : IsPolyhedron C)
    (htri : convexHull ℝ ({c, a, b} : Set E) \ {a, b} ⊆ interior C) :
    ∃ e : E ≃ₜ E, IsPLHomeomorphOn e univ univ ∧ EqOn e id Cᶜ ∧
      EqOn e id (frontier C) ∧ e '' C = C ∧
      e '' (boundaryComplex 2 K).space = (boundaryComplex 2 L).space := by
  let T : Finset E := {c, a, b}
  have hind : AffineIndependent ℝ ((↑) : T → E) := K.indep ht
  have hc : c ∉ ({a, b} : Finset E) := by simpa using And.intro hca hcb
  have ha : a ∉ ({b} : Finset E) := by simpa using hab
  have hb : b ∉ ({a} : Finset E) := by simpa using hab.symm
  have hcard : T.card = 3 := by simp [T, hc, hab]
  let A := simplexComplex T hind
  let _ : Finite A.faces := (simplexComplex_faces_finite T hind).to_subtype
  let _ : Finite (boundaryComplex 2 K).faces := (boundaryComplex_faces_finite 2 K).to_subtype
  have hAspace : A.space = convexHull ℝ ({c, a, b} : Set E) := by
    simpa only [T, Finset.coe_insert, Finset.coe_pair, Finset.coe_singleton] using
      simplexComplex_space T hind (Finset.insert_nonempty c _)
  have hAball : IsPLBall 2 A.space := by
    rw [show A.space = convexHull ℝ (T : Set E) from
      simplexComplex_space T hind (Finset.insert_nonempty c _)]
    exact isPLBall_convexHull_of_affineIndependent T hind hcard
  have hAsub : A.space ⊆ K.space := by
    rw [show A.space = convexHull ℝ (T : Set E) from
      simplexComplex_space T hind (Finset.insert_nonempty c _)]
    exact K.convexHull_subset_space ht
  have hAbd : (boundaryComplex 2 A).space = (simplexBoundary T hind).space := by
    rw [show A = simplexComplex T hind from rfl, boundaryComplex_simplexComplex hind hcard]
  obtain ⟨u, hu, _, _, _, hua, hub, humove⟩ :=
    exists_isPLHomeomorphOn_segment_triangle_move hab hca hcb hind hC htri
  have huArc : IsPLHomeomorphOn u (segment ℝ a b)
      (segment ℝ a c ∪ segment ℝ c b) := by
    rw [← humove]
    exact hu.restrict (isPLBall_segment hab).isPolyhedron (subset_univ _)
  have hγ := (isPLHomeomorphOn_lineMap_Icc_segment hab).trans huArc
  let R := closure ((boundaryComplex 2 K).space \ A.space)
  have hRsub : R ⊆ (boundaryComplex 2 K).space :=
    closure_minimal sdiff_subset (isPolyhedron_space (boundaryComplex 2 K)).isClosed
  have hdiff : (boundaryComplex 2 K).space \ A.space =
      (boundaryComplex 2 K).space \ (segment ℝ a c ∪ segment ℝ c b) := by
    rw [hAspace]
    ext x
    have h := Set.ext_iff.mp htrace x
    simp only [mem_sdiff, mem_inter_iff] at h ⊢
    tauto
  have hsegsub : segment ℝ a c ∪ segment ℝ c b ⊆ (boundaryComplex 2 K).space :=
    htrace.symm.subset.trans inter_subset_left
  have hends : (segment ℝ a c ∪ segment ℝ c b) ∩ R = {a, b} := by
    change (segment ℝ a c ∪ segment ℝ c b) ∩
      closure ((boundaryComplex 2 K).space \ A.space) = _
    rw [hdiff]
    simpa only [Function.comp_apply, AffineMap.lineMap_apply_zero,
      AffineMap.lineMap_apply_one, hua, hub] using
      hγ.inter_closure_circle_sdiff
        (isPLSphere_boundaryComplex_space_of_isPLBall K hK) hsegsub
  have hmeet : convexHull ℝ ({c, a, b} : Set E) ∩ R ⊆ {a, b} := by
    intro x hx
    exact hends.subset ⟨htrace.subset ⟨hRsub hx.2, hx.1⟩, hx.2⟩
  have hR : IsPolyhedron R :=
    (isPolyhedron_space (boundaryComplex 2 K)).closure_sdiff hAball.isPolyhedron
  obtain ⟨e, he, hfix, hfront, hfixR, himageC, _, _, hmove⟩ :=
    exists_isPLHomeomorphOn_segment_triangle_move_fixed_on hab hca hcb hind hC hR htri hmeet
  have hcover : (boundaryComplex 2 K).space = R ∪ (segment ℝ a c ∪ segment ℝ c b) := by
    apply Subset.antisymm
    · intro x hx
      by_cases hxA : x ∈ A.space
      · exact Or.inr (htrace.subset ⟨hx, hAspace ▸ hxA⟩)
      · exact Or.inl (subset_closure ⟨hx, hxA⟩)
    · exact union_subset hRsub hsegsub
  have hAdiff : (boundaryComplex 2 A).space \ (boundaryComplex 2 K).space =
      (boundaryComplex 2 A).space \ (segment ℝ a c ∪ segment ℝ c b) := by
    ext x
    constructor
    · rintro ⟨hx, hxK⟩
      exact ⟨hx, fun hxseg => hxK (hsegsub hxseg)⟩
    · rintro ⟨hx, hxseg⟩
      exact ⟨hx, fun hxK => hxseg (htrace.subset
        ⟨hxK, hAspace ▸ boundaryComplex_space_subset 2 A hx⟩)⟩
  have hcomplement0 : closure ((boundaryComplex 2 A).space \ segment ℝ a b) =
      segment ℝ a c ∪ segment ℝ c b := by
    rw [hAbd]
    have herase : ({a, b} : Finset E).erase b = {a} := by
      rw [Finset.pair_comm a b, Finset.erase_insert hb]
    simpa only [T, Finset.coe_pair, convexHull_pair, Finset.mem_insert,
      Finset.mem_singleton, iUnion_iUnion_eq_or_left, iUnion_iUnion_eq_left,
      Finset.erase_insert ha, herase, Finset.coe_insert, Finset.coe_singleton,
      segment_symm ℝ c a, union_comm] using
      closure_simplexBoundary_sdiff_face ({a, b} : Finset E) (Finset.insert_nonempty a _)
        hc hind
  have hsegA : segment ℝ a b ⊆ (boundaryComplex 2 A).space := by
    rw [hAbd]
    have hedge : ({a, b} : Finset E) ∈ (simplexBoundary T hind).faces := by
      refine ⟨Finset.subset_insert _ _, Finset.insert_nonempty _ _, ?_⟩
      intro heq
      exact hc (heq.symm ▸ Finset.mem_insert_self c ({a, b} : Finset E))
    simpa only [Finset.coe_pair, convexHull_pair] using
      (simplexBoundary T hind).convexHull_subset_space hedge
  have hAends : segment ℝ a b ∩ (segment ℝ a c ∪ segment ℝ c b) = {a, b} := by
    rw [← hcomplement0]
    simpa only [AffineMap.lineMap_apply_zero, AffineMap.lineMap_apply_one] using
      (isPLHomeomorphOn_lineMap_Icc_segment hab).inter_closure_circle_sdiff
        (isPLSphere_boundaryComplex_space_of_isPLBall A hAball) hsegA
  have hAcovers : (boundaryComplex 2 A).space =
      segment ℝ a b ∪ (segment ℝ a c ∪ segment ℝ c b) := by
    rw [← hcomplement0]
    apply Subset.antisymm
    · intro x hx
      by_cases hxseg : x ∈ segment ℝ a b
      · exact Or.inl hxseg
      · exact Or.inr (subset_closure ⟨hx, hxseg⟩)
    · exact union_subset hsegA (closure_minimal sdiff_subset
        (isPLSphere_boundaryComplex_space_of_isPLBall A hAball).isPolyhedron.isClosed)
  have hcomplement : closure ((boundaryComplex 2 A).space \
      (segment ℝ a c ∪ segment ℝ c b)) = segment ℝ a b := by
    have hdiffA : (boundaryComplex 2 A).space \ (segment ℝ a c ∪ segment ℝ c b) =
        segment ℝ a b \ {a, b} := by
      rw [hAcovers, ← hAends]
      ext x
      simp only [mem_sdiff, mem_union, mem_inter_iff]
      tauto
    rw [hdiffA]
    simpa only [AffineMap.lineMap_apply_zero, AffineMap.lineMap_apply_one] using
      (isPLHomeomorphOn_lineMap_Icc_segment hab).closure_sdiff_endpoints zero_lt_one
  have hfixinv (S : Set E) (hS : EqOn e id S) : EqOn e.symm id S := by
    intro x hx
    apply e.injective
    simpa only [id_eq, e.apply_symm_apply] using (hS hx).symm
  have hCinv : e.symm '' C = C := by
    calc
      e.symm '' C = e.symm '' (e '' C) := congrArg (e.symm '' ·) himageC.symm
      _ = C := by simp only [image_image, e.symm_apply_apply, image_id']
  have hmoveinv : e.symm '' (segment ℝ a c ∪ segment ℝ c b) = segment ℝ a b := by
    rw [← hmove]
    simp only [image_image, e.symm_apply_apply, image_id']
  refine ⟨e.symm, he.homeomorph_symm, hfixinv _ hfix, hfixinv _ hfront, hCinv, ?_⟩
  rw [boundaryComplex_space_of_closure_sdiff K A L hK.isCombinatorialManifoldWithBoundary
    hAball.isCombinatorialManifoldWithBoundary hAsub hL.isCombinatorialManifoldWithBoundary
    (hAspace.symm ▸ hLspace), hAdiff, hcomplement]
  change e.symm '' (boundaryComplex 2 K).space = R ∪ segment ℝ a b
  rw [hcover, image_union, (hfixinv _ hfixR).image_eq_self, hmoveinv]

end DifferentialGeometry.Topology.PiecewiseLinear
