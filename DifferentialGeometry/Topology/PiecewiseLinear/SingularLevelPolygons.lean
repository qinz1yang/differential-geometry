/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.Combinatorics.EvenDegree
import DifferentialGeometry.Topology.PiecewiseLinear.CircleIntersection
import DifferentialGeometry.Topology.PiecewiseLinear.PlanarCycleRealization

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem exists_isPLSphere_one_of_mem_space_of_degree_eq_two_except
    (G : Geometry.SimplicialComplex ℝ E) [Finite G.faces]
    (hcard : ∀ s ∈ G.faces, s.card ≤ 2) (hdimE : Module.finrank ℝ E = 3)
    (ℓ : E →ₗ[ℝ] ℝ) (hℓ : ℓ ≠ 0) {r : ℝ} (hGr : G.space ⊆ {x | ℓ x = r})
    (p : E) (hdegree : ∀ v : G.vertices, (v : E) ≠ p →
      ((SimplicialComplex.edgeGraph G).neighborSet v).ncard = 2)
    {x : E} (hx : x ∈ G.space) (hxp : x ≠ p) :
    ∃ J : Set E, IsPLSphere 1 J ∧ J ⊆ G.space ∧ x ∈ J := by
  classical
  let _ : Finite G.vertices := (SimplicialComplex.finite_vertices G).to_subtype
  have heven : ∀ v : G.vertices, Even ((SimplicialComplex.edgeGraph G).neighborSet v).ncard := by
    by_cases hp : p ∈ G.vertices
    · let a : G.vertices := ⟨p, hp⟩
      have hother : ∀ v : G.vertices, v ≠ a →
          Even ((SimplicialComplex.edgeGraph G).neighborSet v).ncard := by
        intro v hv
        rw [hdegree v (fun h => hv (Subtype.ext h))]
        exact ⟨1, rfl⟩
      intro v
      by_cases hv : v = a
      · exact hv ▸ Combinatorics.even_neighborSet_ncard_of_forall_ne
          (SimplicialComplex.edgeGraph G) a hother
      · exact hother v hv
    · intro v
      rw [hdegree v (fun h => hp (h ▸ v.2))]
      exact ⟨1, rfl⟩
  have hedge (u v : G.vertices) (huv : (SimplicialComplex.edgeGraph G).Adj u v) :
      ∃ J : Set E, IsPLSphere 1 J ∧ J ⊆ G.space ∧ segment ℝ (u : E) (v : E) ⊆ J := by
    obtain ⟨a, q, hq, hqe⟩ := Combinatorics.exists_cycle_of_adj_of_even_neighborSet_ncard
      (SimplicialComplex.edgeGraph G) heven huv
    obtain ⟨J, hJ, hJG, hJq⟩ := exists_isPLSphere_one_of_isCycle_of_subset_fiber G hdimE ℓ hℓ hGr q
        hq
    exact ⟨J, hJ, hJG, hJq u v hqe⟩
  obtain ⟨s, hs, hxs⟩ := G.mem_space_iff.mp hx
  by_cases hcard₁ : s.card = 1
  · obtain ⟨v, rfl⟩ := Finset.card_eq_one.mp hcard₁
    have hxv : x = v := by simpa only [Finset.coe_singleton, convexHull_singleton,
        mem_singleton_iff] using hxs
    subst x
    let u : G.vertices := ⟨v, hs⟩
    have hnonempty : ((SimplicialComplex.edgeGraph G).neighborSet u).Nonempty :=
      Set.nonempty_of_ncard_ne_zero (by rw [hdegree u hxp]; decide)
    obtain ⟨w, huw⟩ := hnonempty
    obtain ⟨J, hJ, hJG, hseg⟩ := hedge u w huw
    exact ⟨J, hJ, hJG, hseg (left_mem_segment ℝ (u : E) (w : E))⟩
  · have hcard₂ : s.card = 2 := by
      have := Finset.card_pos.mpr (G.nonempty_of_mem_faces hs)
      have := hcard s hs
      omega
    obtain ⟨u, v, huv, rfl⟩ := Finset.card_eq_two.mp hcard₂
    have hu : u ∈ G.vertices := G.down_closed hs (by simp) (Finset.singleton_nonempty u)
    have hv : v ∈ G.vertices := G.down_closed hs (by simp) (Finset.singleton_nonempty v)
    have hadj : (SimplicialComplex.edgeGraph G).Adj ⟨u, hu⟩ ⟨v, hv⟩ := by
      refine ⟨fun h => huv (congrArg Subtype.val h), ?_⟩
      convert hs using 1
    obtain ⟨J, hJ, hJG, hseg⟩ := hedge ⟨u, hu⟩ ⟨v, hv⟩ hadj
    exact ⟨J, hJ, hJG, hseg (by simpa only [Finset.coe_pair, convexHull_pair] using hxs)⟩

theorem mem_sUnion_levelPolygons_of_ne_vertex
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsCombinatorialManifold 2 K) (hdimE : Module.finrank ℝ E = 3)
    (ℓ : E →ₗ[ℝ] ℝ) (hℓ : ℓ ≠ 0) (hinj : InjOn ℓ K.vertices)
    {p x : E} (hp : p ∈ K.vertices) (hx : x ∈ K.space) (hxp : x ≠ p) (hheight : ℓ x = ℓ p) :
    x ∈ ⋃₀ levelPolygons K.space ℓ (ℓ p) := by
  obtain ⟨G, hGfin, hGspace, hcard, hneighbors⟩ :=
    exists_triangulation_fiber_of_isCombinatorialManifold K hK hdimE ℓ hℓ hinj (ℓ p)
  let _ : Finite G.faces := hGfin.to_subtype
  have hdegree : ∀ v : G.vertices, (v : E) ≠ p →
      ((SimplicialComplex.edgeGraph G).neighborSet v).ncard = 2 := by
    intro v hvp
    have hvlevel : ℓ v = ℓ p := (hGspace ▸ G.vertices_subset_space v.2).2
    have hvK : (v : E) ∉ K.vertices := fun hv => hvp (hinj hv hp hvlevel)
    obtain ⟨a, b, hab, hpair⟩ := hneighbors v v.2 hvK
    rw [SimplicialComplex.ncard_neighborSet_edgeGraph, hpair, Set.ncard_pair hab]
  obtain ⟨J, hJ, hJG, hxJ⟩ := exists_isPLSphere_one_of_mem_space_of_degree_eq_two_except
    G hcard hdimE ℓ hℓ (hGspace.trans_le inter_subset_right) p hdegree
    (hGspace.symm ▸ And.intro hx hheight) hxp
  exact mem_sUnion.mpr ⟨J, ⟨hJ, hJG.trans_eq hGspace⟩, hxJ⟩

theorem fiber_eq_singleton_union_sUnion_levelPolygons
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsCombinatorialManifold 2 K) (hdimE : Module.finrank ℝ E = 3)
    (ℓ : E →ₗ[ℝ] ℝ) (hℓ : ℓ ≠ 0) (hinj : InjOn ℓ K.vertices)
    {p : E} (hp : p ∈ K.vertices) :
    K.space ∩ {x | ℓ x = ℓ p} = {p} ∪ ⋃₀ levelPolygons K.space ℓ (ℓ p) := by
  apply Subset.antisymm
  · intro x hx
    by_cases hxp : x = p
    · exact Or.inl hxp
    · exact Or.inr (mem_sUnion_levelPolygons_of_ne_vertex K hK hdimE ℓ hℓ hinj hp hx.1 hxp hx.2)
  · rintro x (rfl | hx)
    · exact ⟨K.vertices_subset_space hp, rfl⟩
    · obtain ⟨J, hJ, hxJ⟩ := mem_sUnion.mp hx
      exact hJ.2 hxJ

open Classical in
theorem inter_subset_singleton_levelPolygons_of_ne
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsCombinatorialManifold 2 K) (hdimE : Module.finrank ℝ E = 3)
    (ℓ : E →ₗ[ℝ] ℝ) (hℓ : ℓ ≠ 0) (hinj : InjOn ℓ K.vertices)
    {p : E} (hp : p ∈ K.vertices) {J T : Set E}
    (hJ : J ∈ levelPolygons K.space ℓ (ℓ p)) (hT : T ∈ levelPolygons K.space ℓ (ℓ p))
    (hJT : J ≠ T) : J ∩ T ⊆ {p} := by
  obtain ⟨G, hGfin, hGspace, hcard, hneighbors⟩ :=
    exists_triangulation_fiber_of_isCombinatorialManifold K hK hdimE ℓ hℓ hinj (ℓ p)
  let _ : Finite G.faces := hGfin.to_subtype
  have hdegree : ∀ v ∈ G.vertices, v ≠ p → {w | w ≠ v ∧ {v, w} ∈ G.faces}.ncard = 2 := by
    intro v hv hvp
    have hvlevel : ℓ v = ℓ p := (hGspace ▸ G.vertices_subset_space hv).2
    have hvK : v ∉ K.vertices := fun hv => hvp (hinj hv hp hvlevel)
    obtain ⟨a, b, hab, hpair⟩ := hneighbors v hv hvK
    rw [hpair, Set.ncard_pair hab]
  intro x hx
  by_contra hxp
  exact hJT (eq_of_isPLSphere_one_of_mem_inter_of_degree_eq_two_except G hcard p hdegree
    hJ.1 hT.1 (hJ.2.trans_eq hGspace.symm) (hT.2.trans_eq hGspace.symm) hx.1 hx.2 hxp)

theorem pairwiseDisjoint_sdiff_singleton_levelPolygons
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsCombinatorialManifold 2 K) (hdimE : Module.finrank ℝ E = 3)
    (ℓ : E →ₗ[ℝ] ℝ) (hℓ : ℓ ≠ 0) (hinj : InjOn ℓ K.vertices)
    {p : E} (hp : p ∈ K.vertices) :
    (levelPolygons K.space ℓ (ℓ p)).PairwiseDisjoint (fun J => J \ {p}) := by
  intro J hJ T hT hJT
  apply Set.disjoint_left.mpr
  rintro x ⟨hxJ, hxp⟩ ⟨hxT, -⟩
  exact hxp (inter_subset_singleton_levelPolygons_of_ne K hK hdimE ℓ hℓ hinj hp hJ hT hJT ⟨hxJ,
      hxT⟩)

theorem singleton_mem_nhdsWithin_fiber_iff_notMem_sUnion_levelPolygons
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsCombinatorialManifold 2 K) (hdimE : Module.finrank ℝ E = 3)
    (ℓ : E →ₗ[ℝ] ℝ) (hℓ : ℓ ≠ 0) (hinj : InjOn ℓ K.vertices)
    {p : E} (hp : p ∈ K.vertices) :
    {p} ∈ 𝓝[K.space ∩ {x | ℓ x = ℓ p}] p ↔ p ∉ ⋃₀ levelPolygons K.space ℓ (ℓ p) := by
  constructor
  · intro hisolated hpC
    obtain ⟨J, hJ, hpJ⟩ := mem_sUnion.mp hpC
    exact hJ.1.not_singleton_mem_nhdsWithin_one hpJ (nhdsWithin_mono p hJ.2 hisolated)
  · intro hpC
    have hclosed : IsClosed (⋃₀ levelPolygons K.space ℓ (ℓ p)) := by
      rw [sUnion_eq_biUnion]
      exact (finite_levelPolygons K (fun s hs => hK.card_le K hs) hdimE ℓ hℓ hinj (ℓ
          p)).isClosed_biUnion
        (fun J hJ => hJ.1.isPolyhedron.isClosed)
    apply mem_nhdsWithin_iff_exists_mem_nhds_inter.mpr
    refine ⟨(⋃₀ levelPolygons K.space ℓ (ℓ p))ᶜ, hclosed.isOpen_compl.mem_nhds hpC, ?_⟩
    rintro x ⟨hxC, hx⟩
    rw [fiber_eq_singleton_union_sUnion_levelPolygons K hK hdimE ℓ hℓ hinj hp] at hx
    exact hx.resolve_right hxC

theorem mem_sUnion_levelPolygons_of_mem_heightSingularPoints
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsCombinatorialManifold 2 K) (hdimE : Module.finrank ℝ E = 3)
    (ℓ : E →ₗ[ℝ] ℝ) (hℓ : ℓ ≠ 0) (hinj : InjOn ℓ K.vertices)
    {p : E} (hp : p ∈ heightSingularPoints K.space ℓ) :
    p ∈ ⋃₀ levelPolygons K.space ℓ (ℓ p) := by
  have hpv := heightSingularPoints_subset_vertices K hK.isCombinatorialManifoldWithBoundary hdimE ℓ
      hℓ hinj hp
  by_contra hpC
  exact hp.2.2 ((singleton_mem_nhdsWithin_fiber_iff_notMem_sUnion_levelPolygons K hK hdimE ℓ hℓ hinj
      hpv).mpr hpC)

end DifferentialGeometry.Topology.PiecewiseLinear
