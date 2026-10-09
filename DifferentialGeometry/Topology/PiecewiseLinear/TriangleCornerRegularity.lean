/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.BoundaryArcCardinality
import DifferentialGeometry.Topology.PiecewiseLinear.LinkUnionSection
import DifferentialGeometry.Topology.PiecewiseLinear.TriangleBoundaryVertices
import DifferentialGeometry.Topology.PiecewiseLinear.VertexSectionSubdivision

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem height_section_subsingleton_of_boundary_vertices_of_one_low
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [DecidableEq E] (L : Geometry.SimplicialComplex ℝ E) [Finite L.faces]
    (hL : IsCombinatorialManifoldWithBoundary 1 L) {a b : E}
    (hb : {b} ∈ (boundaryComplex 1 L).faces)
    (f : E →ₗ[ℝ] ℝ) (r : ℝ) (hfa : f a < r) (hfb : f b ≠ r)
    (hother : ∀ v ∈ L.vertices, v ≠ a → v ≠ b → f v < r) :
    (L.space ∩ {x | f x = r}).Subsingleton := by
  rcases lt_or_gt_of_ne hfb with hfblt | hfbgt
  · rintro x ⟨hxL, hfx⟩
    obtain ⟨s, hs, hxs⟩ := L.mem_space_iff.mp hxL
    have hslt : (s : Set E) ⊆ {z | f z < r} := by
      intro v hv
      have hvL : v ∈ L.vertices := by
        change {v} ∈ L.faces
        exact L.down_closed hs (Finset.singleton_subset_iff.mpr hv)
          (Finset.singleton_nonempty v)
      by_cases hva : v = a
      · exact hva ▸ hfa
      · by_cases hvb : v = b
        · exact hvb ▸ hfblt
        · exact hother v hvL hva hvb
    have hxlt := convexHull_min hslt (convex_halfSpace_lt f.isLinear r) hxs
    exact ((ne_of_lt hxlt) hfx).elim
  · apply height_section_subsingleton_of_unique_high_boundary_vertex L hL hb f r hfbgt
    intro v hv hvb
    by_cases hva : v = a
    · exact hva ▸ hfa
    · exact hother v hv hva hvb

theorem singleton_mem_boundaryComplex_of_common_triangle_boundary
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [DecidableEq E] (M N : Geometry.SimplicialComplex ℝ E)
    [Finite N.faces]
    (T : Finset E) (hT : AffineIndependent ℝ ((↑) : T → E)) (hcard : T.card = 3)
    (hNspace : N.space = convexHull ℝ (T : Set E))
    (hboundary : (boundaryComplex 2 M).space = (boundaryComplex 2 N).space)
    {q : E} (hq : q ∈ T) : {q} ∈ (boundaryComplex 2 M).faces := by
  have hqN := singleton_mem_boundaryComplex_of_mem_triangle_vertex N T hT hcard hNspace hq
  have hqMspace : q ∈ (boundaryComplex 2 M).space := by
    rw [hboundary]
    exact (boundaryComplex 2 N).convexHull_subset_space hqN
      (subset_convexHull ℝ _ (by simp))
  obtain ⟨s, hs, hqs⟩ := (boundaryComplex 2 M).mem_space_iff.mp hqMspace
  obtain ⟨m, -, hm⟩ :=
    exists_linearMap_lt_on_convexHull_sdiff_singleton T hT (by omega) hq
  have hqs' : q ∈ s := by
    by_contra hqnot
    have hslt : (s : Set E) ⊆ {x | m q < m x} := by
      intro v hv
      have hvM : v ∈ (boundaryComplex 2 M).space :=
        (boundaryComplex 2 M).convexHull_subset_space hs
          (subset_convexHull ℝ _ (Finset.mem_coe.mpr hv))
      have hvN : v ∈ N.space :=
        boundaryComplex_space_subset 2 N (hboundary ▸ hvM)
      apply hm v
      exact ⟨hNspace ▸ hvN, fun hvq => hqnot (hvq ▸ hv)⟩
    have hlt := convexHull_min hslt (convex_halfSpace_gt m.isLinear (m q)) hqs
    exact (lt_irrefl (m q) hlt).elim
  exact (boundaryComplex 2 M).down_closed hs
    (Finset.singleton_subset_iff.mpr hqs') (Finset.singleton_nonempty q)

theorem eventually_notMem_heightSingularPoints_of_triangle_vertex
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [dE : DecidableEq E] (hdimE : Module.finrank ℝ E = 3)
    (R M N : Geometry.SimplicialComplex ℝ E) [Finite R.faces] [Finite M.faces]
    [Finite N.faces] (hR : IsPLSphere 2 R.space) (hMR : M.faces ⊆ R.faces)
    (hcover : ∀ s ∈ R.faces, s ∈ M.faces ∨ s ∈ N.faces)
    (hM : IsPLBall 2 M.space) (T : Finset E)
    (hT : AffineIndependent ℝ ((↑) : T → E)) (hcard : T.card = 3)
    {p q : E} (hp : p ∈ T) (hq : q ∈ T)
    (hNspace : N.space = convexHull ℝ (T : Set E))
    (hboundaryMN : (boundaryComplex 2 M).space = (boundaryComplex 2 N).space)
    (ℓ : E →L[ℝ] ℝ)
    (hhalf : ∀ᶠ x in 𝓝 q, x ∈ M.space → ℓ x ≤ ℓ q)
    (hboundary : ∀ᶠ x in 𝓝 q,
      x ∈ (boundaryComplex 2 M).space ↔ x ∈ M.space ∧ ℓ x = ℓ q) :
    ∀ᶠ f : E →L[ℝ] ℝ in 𝓝 ℓ,
      InjOn f (insert q R.vertices ∪ (T : Set E)) →
      (∀ x ∈ convexHull ℝ (T : Set E) \ {p}, f p < f x) →
        q ∉ heightSingularPoints R.space f := by
  classical
  cases Subsingleton.elim dE (Classical.decEq E)
  let L := SimplicialComplex.geometricLink M {q}
  let _ : Finite L.faces :=
    ((Set.toFinite M.faces).subset (SimplicialComplex.geometricLink_le M {q})).to_subtype
  let _ : Finite (boundaryComplex 2 M).faces :=
    (boundaryComplex_faces_finite 2 M).to_subtype
  have hqM : {q} ∈ (boundaryComplex 2 M).faces :=
    singleton_mem_boundaryComplex_of_common_triangle_boundary M N T hT hcard hNspace
      hboundaryMN hq
  have hqR : {q} ∈ R.faces := hMR (boundaryComplex_faces_subset 2 M hqM)
  obtain ⟨a, b, hab, ha, hb, hpair⟩ :=
    exists_geometricLink_boundary_pair_of_isPLBall M hM hqM
  have hman : IsCombinatorialManifoldWithBoundary 2 M :=
    hM.isCombinatorialManifoldWithBoundary
  have hlinkBall : IsPLBall 1 L.space := by
    have h := ((hman.mem_boundaryComplex_faces_iff M).mp hqM).2.2
    simpa only [L, Finset.card_singleton, Nat.reduceSub] using h
  have hlink : IsCombinatorialManifoldWithBoundary 1 L :=
    hlinkBall.isCombinatorialManifoldWithBoundary
  have haB : {a} ∈ (boundaryComplex 1 L).faces := by
    change {a} ∈ (boundaryComplex 1 (SimplicialComplex.geometricLink M {q})).faces
    rw [← geometricLink_boundaryComplex (n := 1) M q]
    exact ha
  have hbB : {b} ∈ (boundaryComplex 1 L).faces := by
    change {b} ∈ (boundaryComplex 1 (SimplicialComplex.geometricLink M {q})).faces
    rw [← geometricLink_boundaryComplex (n := 1) M q]
    exact hb
  have hside := geometricLink_vertices_lt_of_halfSpace_boundary_germ
    M hM ℓ hqM ha hb hab hhalf hboundary
  have hvertices : (insert q L.vertices).Finite := by
    apply Set.Finite.insert
    exact Set.Finite.preimage Finset.singleton_injective.injOn (Set.toFinite L.faces)
  have horder := eventually_preserves_strict_order hvertices ℓ
  have haBM : {a} ∈ (boundaryComplex 2 M).faces :=
    SimplicialComplex.geometricLink_le (boundaryComplex 2 M) {q} ha
  have hbBM : {b} ∈ (boundaryComplex 2 M).faces :=
    SimplicialComplex.geometricLink_le (boundaryComplex 2 M) {q} hb
  have haR : a ∈ R.vertices :=
    hMR (boundaryComplex_faces_subset 2 M haBM)
  have hbR : b ∈ R.vertices :=
    hMR (boundaryComplex_faces_subset 2 M hbBM)
  have haq : a ≠ q := ne_of_mem_of_not_mem
    ((SimplicialComplex.geometricLink (boundaryComplex 2 M) {q}).vertices_subset_space ha)
    (notMem_geometricLink_space (boundaryComplex 2 M))
  have hbq : b ≠ q := ne_of_mem_of_not_mem
    ((SimplicialComplex.geometricLink (boundaryComplex 2 M) {q}).vertices_subset_space hb)
    (notMem_geometricLink_space (boundaryComplex 2 M))
  filter_upwards [horder] with f hforder
  intro hfinj hstrict
  have hfinjR : InjOn f (insert q R.vertices) := hfinj.mono subset_union_left
  have hfinjT : InjOn f (T : Set E) := hfinj.mono subset_union_right
  have hfa : f a ≠ f q := fun heq => haq (hfinjR (by simp [haR]) (by simp) heq)
  have hfb : f b ≠ f q := fun heq => hbq (hfinjR (by simp [hbR]) (by simp) heq)
  have hother : ∀ v ∈ L.vertices, v ≠ a → v ≠ b → f v < f q := by
    intro v hv hva hvb
    exact hforder v (by simp [hv]) q (by simp) (hside v hv hva hvb)
  have hcap := geometricLink_section_subsingleton_of_simplex_vertex
    T hT hcard hq N hNspace f hfinjT
  have hfne : f ≠ 0 := by
    obtain ⟨u, hu, v, hv, huv⟩ :=
      Finset.one_lt_card.mp (show 1 < T.card by omega)
    intro hfzero
    apply huv
    apply hfinjT hu hv
    simp only [hfzero, zero_apply]
  have hfull : ((SimplicialComplex.geometricLink R {q}).space ∩
      {x | f x = f q}).encard ≤ 2 := by
    by_cases hqp : q = p
    · subst q
      have hcapEmpty : (SimplicialComplex.geometricLink N {p}).space ∩
          {x | f x = f p} = ∅ := by
        rw [Set.eq_empty_iff_forall_notMem]
        rintro x ⟨hxN, hfx⟩
        have hxT : x ∈ convexHull ℝ (T : Set E) :=
          hNspace ▸ space_mono_of_faces_subset
            (SimplicialComplex.geometricLink_le N {p}) hxN
        have hxp : x ≠ p :=
          ne_of_mem_of_not_mem hxN (notMem_geometricLink_space N)
        exact (ne_of_lt (hstrict x ⟨hxT, hxp⟩)) hfx.symm
      have hret : (L.space ∩ {x | f x = f p}).encard ≤ 2 := by
        simpa only [ContinuousLinearMap.coe_coe] using
          height_section_encard_le_two_of_boundary_vertices L hlink haB hbB
            f.toLinearMap (f p) hfa hfb hother
      have hsub : (SimplicialComplex.geometricLink R {p}).space ∩
          {x | f x = f p} ⊆ L.space ∩ {x | f x = f p} := by
        rintro x ⟨hxR, hfx⟩
        rcases geometricLink_space_subset_union_of_faces_cover R M N hcover hxR with hxM | hxN
        · exact ⟨hxM, hfx⟩
        · have : x ∈ (SimplicialComplex.geometricLink N {p}).space ∩
              {x | f x = f p} := ⟨hxN, hfx⟩
          rw [hcapEmpty] at this
          exact this.elim
      exact (encard_mono hsub).trans hret
    · have hsegN : segment ℝ q p ⊆ (boundaryComplex 2 N).space :=
        segment_subset_boundaryComplex_of_space_eq_convexHull N T hT hcard hNspace
          hq hp hqp
      have hray : ∀ t : ℝ, 0 < t → t ≤ 1 →
          q + t • (p - q) ∈ (boundaryComplex 2 M).space := by
        intro t ht ht1
        rw [hboundaryMN]
        apply hsegN
        simpa only [AffineMap.lineMap_apply_module', add_comm] using
          lineMap_mem_segment ℝ q p ⟨ht.le, ht1⟩
      obtain ⟨c, hc, hz⟩ := exists_ray_mem_geometricLink_space
        (boundaryComplex 2 M) hqM hray (Ne.symm hqp)
      have hzpair : q + c • (p - q) = a ∨ q + c • (p - q) = b := by
        rw [hpair] at hz
        exact hz
      have hfpq : f p < f q :=
        hstrict q ⟨subset_convexHull ℝ (T : Set E) hq, by simpa only [mem_singleton_iff]⟩
      have hzlt : f (q + c • (p - q)) < f q := by
        have hmul : c * (f p - f q) < 0 :=
          mul_neg_of_pos_of_neg hc (sub_neg.mpr hfpq)
        simp only [map_add, map_smul, map_sub, smul_eq_mul]
        linarith
      have hret : (L.space ∩ {x | f x = f q}).Subsingleton := by
        rcases hzpair with hza | hzb
        · have hfalt : f a < f q := by rwa [hza] at hzlt
          simpa only [ContinuousLinearMap.coe_coe] using
            height_section_subsingleton_of_boundary_vertices_of_one_low
              L hlink hbB f.toLinearMap (f q) hfalt hfb hother
        · have hfblt : f b < f q := by rwa [hzb] at hzlt
          simpa only [ContinuousLinearMap.coe_coe] using
            height_section_subsingleton_of_boundary_vertices_of_one_low
              L hlink haB f.toLinearMap (f q) hfblt hfa
                (fun v hv hvb hva => hother v hv hva hvb)
      exact geometricLink_section_encard_le_two_of_faces_cover R M N hcover f hret hcap
  exact notMem_heightSingularPoints_of_geometricLink_section_encard_le_two_of_injOn
    hdimE R hR hqR f hfne hfinjR hfull

end DifferentialGeometry.Topology.PiecewiseLinear
