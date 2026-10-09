/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.ArcTriangleMove
import DifferentialGeometry.Topology.PiecewiseLinear.BoundaryComplement
import DifferentialGeometry.Topology.PiecewiseLinear.CircleComplementaryArc
import DifferentialGeometry.Topology.PiecewiseLinear.PLDiskArcGluing

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem IsPLHomeomorphOn.inter_closure_circle_sdiff
    {S A : Set E} (hS : IsPLSphere 1 S) {γ : ℝ → E}
    (hγ : IsPLHomeomorphOn γ (Icc 0 1) A) (hAS : A ⊆ S) :
    A ∩ closure (S \ A) = {γ 0, γ 1} := by
  obtain ⟨B, δ, hδ, hδ0, hδ1, hunion, hinter⟩ :=
    exists_complementary_arc_of_isPLSphere_one hS hγ hAS
  have hdiff : S \ A = B \ {δ 0, δ 1} := by
    rw [hδ0, hδ1, ← hunion, ← hinter]
    ext x
    simp only [mem_sdiff, mem_union, mem_inter_iff]
    tauto
  rw [hdiff, hδ.closure_sdiff_endpoints zero_lt_one, hinter]

omit [FiniteDimensional ℝ E] in
open Classical in
theorem closure_simplexBoundary_sdiff_face (T : Finset E) (hT : T.Nonempty)
    {a : E} (ha : a ∉ T)
    (hind : AffineIndependent ℝ ((↑) : ↥(insert a T : Finset E) → E)) :
    closure ((simplexBoundary (insert a T) hind).space \ convexHull ℝ (T : Set E)) =
      ⋃ v ∈ T, convexHull ℝ ((insert a (T.erase v) : Finset E) : Set E) := by
  let R : Set E := ⋃ v ∈ T, convexHull ℝ ((insert a (T.erase v) : Finset E) : Set E)
  have hcard : 2 ≤ (insert a T).card := by
    rw [Finset.card_insert_of_notMem ha]
    have := Finset.card_pos.mpr hT
    omega
  have hbd : (simplexBoundary (insert a T) hind).space =
      convexHull ℝ (T : Set E) ∪ R := by
    rw [simplexBoundary_space _ _ hcard]
    ext x
    constructor
    · intro hx
      obtain ⟨v, hv, hx⟩ := mem_iUnion₂.mp hx
      rcases Finset.mem_insert.mp hv with rfl | hv
      · exact Or.inl (by simpa only [Finset.erase_insert ha] using hx)
      · exact Or.inr (mem_iUnion₂.mpr ⟨v, hv, by
          simpa only [Finset.erase_insert_of_ne (ne_of_mem_of_not_mem hv ha).symm] using hx⟩)
    · rintro (hx | hx)
      · exact mem_iUnion₂.mpr ⟨a, Finset.mem_insert_self a T, by
          simpa only [Finset.erase_insert ha] using hx⟩
      · obtain ⟨v, hv, hxv⟩ := mem_iUnion₂.mp hx
        exact mem_iUnion₂.mpr ⟨v, Finset.mem_insert_of_mem hv, by
          simpa only [Finset.erase_insert_of_ne (ne_of_mem_of_not_mem hv ha).symm] using hxv⟩
  have hRclosed : IsClosed R := T.finite_toSet.isClosed_biUnion fun v _ =>
    ((insert a (T.erase v) : Finset E).finite_toSet.isCompact_convexHull ℝ).isClosed
  apply Subset.antisymm
  · apply closure_minimal _ hRclosed
    intro x hx
    rw [hbd] at hx
    exact hx.1.resolve_left hx.2
  · intro x hx
    obtain ⟨v, hv, hxv⟩ := mem_iUnion₂.mp hx
    apply (convexHull_subset_closure_openSimplex (Finset.insert_nonempty a (T.erase v))).trans _ hxv
    apply closure_mono
    intro y hy
    refine ⟨?_, fun hyT => ?_⟩
    · rw [hbd]
      exact Or.inr (mem_iUnion₂.mpr ⟨v, hv, openSimplex_subset_convexHull _ hy⟩)
    · have hsub := subset_of_mem_openSimplex_of_mem_convexHull hind
        (Finset.insert_subset_insert a (Finset.erase_subset v T))
        (Finset.subset_insert a T) hy hyT
      exact ha (hsub (Finset.mem_insert_self a _))

open Classical in
theorem exists_isPLHomeomorphOn_disk_boundary_one_edge_deletion
    (K L : Geometry.SimplicialComplex ℝ E) [Finite K.faces] [Finite L.faces]
    (hK : IsPLBall 2 K.space) (hL : IsPLBall 2 L.space)
    {a b c : E} (hab : a ≠ b) (hca : c ≠ a) (hcb : c ≠ b)
    (ht : ({c, a, b} : Finset E) ∈ K.faces)
    (htrace : (boundaryComplex 2 K).space ∩ convexHull ℝ ({c, a, b} : Set E) =
      segment ℝ a b)
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
  let R := closure ((boundaryComplex 2 K).space \ A.space)
  have hRsub : R ⊆ (boundaryComplex 2 K).space :=
    closure_minimal sdiff_subset (isPolyhedron_space (boundaryComplex 2 K)).isClosed
  have hdiff : (boundaryComplex 2 K).space \ A.space =
      (boundaryComplex 2 K).space \ segment ℝ a b := by
    rw [hAspace]
    ext x
    have h := Set.ext_iff.mp htrace x
    simp only [mem_sdiff, mem_inter_iff] at h ⊢
    tauto
  have hsegsub : segment ℝ a b ⊆ (boundaryComplex 2 K).space :=
    htrace.symm.subset.trans inter_subset_left
  have hends : segment ℝ a b ∩ R = {a, b} := by
    change segment ℝ a b ∩ closure ((boundaryComplex 2 K).space \ A.space) = _
    rw [hdiff]
    simpa only [AffineMap.lineMap_apply_zero, AffineMap.lineMap_apply_one] using
      (isPLHomeomorphOn_lineMap_Icc_segment hab).inter_closure_circle_sdiff
        (isPLSphere_boundaryComplex_space_of_isPLBall K hK) hsegsub
  have hmeet : convexHull ℝ ({c, a, b} : Set E) ∩ R ⊆ {a, b} := by
    intro x hx
    exact hends.subset ⟨htrace.subset ⟨hRsub hx.2, hx.1⟩, hx.2⟩
  have hR : IsPolyhedron R :=
    (isPolyhedron_space (boundaryComplex 2 K)).closure_sdiff hAball.isPolyhedron
  obtain ⟨e, he, hfix, hfront, hfixR, himageC, _, _, hmove⟩ :=
    exists_isPLHomeomorphOn_segment_triangle_move_fixed_on hab hca hcb hind hC hR htri hmeet
  have hcover : (boundaryComplex 2 K).space = R ∪ segment ℝ a b := by
    apply Subset.antisymm
    · intro x hx
      by_cases hxA : x ∈ A.space
      · exact Or.inr (htrace.subset ⟨hx, hAspace ▸ hxA⟩)
      · exact Or.inl (subset_closure ⟨hx, hxA⟩)
    · exact union_subset hRsub hsegsub
  have hAdiff : (boundaryComplex 2 A).space \ (boundaryComplex 2 K).space =
      (boundaryComplex 2 A).space \ segment ℝ a b := by
    ext x
    constructor
    · rintro ⟨hx, hxK⟩
      exact ⟨hx, fun hxseg => hxK (hsegsub hxseg)⟩
    · rintro ⟨hx, hxseg⟩
      exact ⟨hx, fun hxK => hxseg (htrace.subset
        ⟨hxK, hAspace ▸ boundaryComplex_space_subset 2 A hx⟩)⟩
  have hcomplement : closure ((boundaryComplex 2 A).space \ segment ℝ a b) =
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
  refine ⟨e, he, hfix, hfront, himageC, ?_⟩
  rw [boundaryComplex_space_of_closure_sdiff K A L hK.isCombinatorialManifoldWithBoundary
    hAball.isCombinatorialManifoldWithBoundary hAsub hL.isCombinatorialManifoldWithBoundary
    (hAspace.symm ▸ hLspace), hAdiff, hcomplement]
  change e '' (boundaryComplex 2 K).space = R ∪ (segment ℝ a c ∪ segment ℝ c b)
  rw [hcover, image_union, hfixR.image_eq_self, hmove]

end DifferentialGeometry.Topology.PiecewiseLinear
