import DifferentialGeometry.Topology.PiecewiseLinear.HeightIndex
import DifferentialGeometry.Topology.PiecewiseLinear.ManifoldSubspace
import DifferentialGeometry.Topology.PiecewiseLinear.PolygonalSchoenflies
import Mathlib.Data.ENat.BigOperators

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem convexHull_subset_of_isPLSphere_one_of_mem_openSimplex
    (G : Geometry.SimplicialComplex ℝ E) [Finite G.faces]
    (hcard : ∀ s ∈ G.faces, s.card ≤ 2) {J : Set E} (hJ : IsPLSphere 1 J)
    (hJG : J ⊆ G.space) {s : Finset E} (hs : s ∈ G.faces) (hsCard : s.card = 2)
    {x : E} (hxs : x ∈ openSimplex s) (hxJ : x ∈ J) : convexHull ℝ (s : Set E) ⊆ J := by
  classical
  obtain ⟨H, hHfin, hHspace⟩ := hJ.isPolyhedron.exists_simplicialComplex
  let _ : Finite H.faces := hHfin.to_subtype
  have hH : IsCombinatorialManifold 1 H :=
    (hHspace.symm ▸ hJ).isCombinatorialManifold
  have hdim : Module.finrank ℝ (vectorSpan ℝ (s : Set E)) = 1 := by
    have h := (G.indep hs).finrank_vectorSpan (show Fintype.card s = 1 + 1 by
      simpa only [Fintype.card_coe] using hsCard)
    have hrange : Set.range ((↑) : s → E) = (s : Set E) := by ext y; simp
    rwa [hrange] at h
  have hlocal : ∀ y ∈ openSimplex s, y ∈ J → J ∈ 𝓝[openSimplex s] y := by
    intro y hys hyJ
    have hGlocal := eventually_mem_space_iff_sub_mem_vectorSpan G hs
      (fun t ht _ => (hcard t ht).trans_eq hsCard.symm) hys
    have hsub : ∀ᶠ z in 𝓝 y, z ∈ H.space → z - y ∈ vectorSpan ℝ (s : Set E) := by
      filter_upwards [hGlocal] with z hz hzH
      exact hz.mp (hJG (hHspace ▸ hzH))
    have hHlocal := eventually_mem_space_iff_sub_mem_submodule H hH
      (vectorSpan ℝ (s : Set E)) hdim (hHspace.symm ▸ hyJ) hsub
    have hgerm : ∀ᶠ z in 𝓝 y, z ∈ G.space → z ∈ J := by
      filter_upwards [hGlocal, hHlocal] with z hzG hzH hz
      exact hHspace ▸ hzH.mpr (hzG.mp hz)
    apply mem_nhdsWithin_iff_exists_mem_nhds_inter.mpr
    refine ⟨{z | z ∈ G.space → z ∈ J}, hgerm, ?_⟩
    rintro z ⟨hz, hzs⟩
    exact hz (G.convexHull_subset_space hs (openSimplex_subset_convexHull s hzs))
  let _ : PreconnectedSpace (openSimplex s) :=
    Subtype.preconnectedSpace (convex_openSimplex s).isPreconnected
  have hclosed : IsClosed ((↑) ⁻¹' J : Set (openSimplex s)) :=
    hJ.isPolyhedron.isClosed.preimage continuous_subtype_val
  have hopen : IsOpen ((↑) ⁻¹' J : Set (openSimplex s)) := by
    apply isOpen_iff_mem_nhds.mpr
    intro y hy
    have hn := hlocal y y.property hy
    rwa [nhdsWithin_eq_map_subtype_coe] at hn
  have hfull : ((↑) ⁻¹' J : Set (openSimplex s)) = univ :=
    IsClopen.eq_univ ⟨hclosed, hopen⟩ ⟨⟨x, hxs⟩, hxJ⟩
  have hsub : openSimplex s ⊆ J := fun y hy =>
    (show (⟨y, hy⟩ : openSimplex s) ∈ ((↑) ⁻¹' J : Set (openSimplex s)) by rw [hfull]; trivial)
  exact (convexHull_subset_closure_openSimplex (G.nonempty_of_mem_faces hs)).trans
    (closure_minimal hsub hJ.isPolyhedron.isClosed)

theorem restrict_space_eq_of_isPLSphere_one (G : Geometry.SimplicialComplex ℝ E)
    [Finite G.faces] (hcard : ∀ s ∈ G.faces, s.card ≤ 2) {J : Set E}
    (hJ : IsPLSphere 1 J) (hJG : J ⊆ G.space) : (restrict G J).space = J := by
  classical
  refine Subset.antisymm (restrict_space_subset G J) ?_
  intro x hx
  obtain ⟨s, hs, hxs⟩ := exists_face_mem_openSimplex G (hJG hx)
  have hsub : convexHull ℝ (s : Set E) ⊆ J := by
    by_cases hsc : s.card = 1
    · obtain ⟨v, rfl⟩ := Finset.card_eq_one.mp hsc
      have hxv : x = v := by
        simpa only [Finset.coe_singleton, convexHull_singleton, mem_singleton_iff] using
          openSimplex_subset_convexHull _ hxs
      simpa only [Finset.coe_singleton, convexHull_singleton, singleton_subset_iff, ← hxv] using hx
    · have hsCard : s.card = 2 := by
        have := Finset.card_pos.mpr (G.nonempty_of_mem_faces hs)
        have := hcard s hs
        omega
      exact convexHull_subset_of_isPLSphere_one_of_mem_openSimplex G hcard hJ hJG hs hsCard hxs hx
  exact (restrict G J).convexHull_subset_space ⟨hs, hsub⟩ (openSimplex_subset_convexHull s hxs)

theorem finite_isPLSphere_one_subsets (G : Geometry.SimplicialComplex ℝ E)
    [Finite G.faces] (hcard : ∀ s ∈ G.faces, s.card ≤ 2) :
    {J | IsPLSphere 1 J ∧ J ⊆ G.space}.Finite := by
  classical
  let F := (Set.toFinite G.faces).toFinset
  let carrier : Finset (Finset E) → Set E := fun A => ⋃ s ∈ A, convexHull ℝ (s : Set E)
  apply (F.powerset.finite_toSet.image carrier).subset
  rintro J ⟨hJ, hJG⟩
  let A := F.filter (fun s : Finset E => convexHull ℝ (s : Set E) ⊆ J)
  refine ⟨A, Finset.mem_powerset.mpr (Finset.filter_subset _ _), ?_⟩
  rw [← restrict_space_eq_of_isPLSphere_one G hcard hJ hJG]
  ext x
  rw [(restrict G J).mem_space_iff]
  simp only [carrier, mem_iUnion, exists_prop, A, F, Finset.mem_filter,
    Set.Finite.mem_toFinset, mem_restrict_faces_iff]

theorem finite_levelPolygons (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hcardK : ∀ s ∈ K.faces, s.card ≤ 3) {n : ℕ} (hdimE : Module.finrank ℝ E = n + 1)
    (ℓ : E →ₗ[ℝ] ℝ) (hℓ : ℓ ≠ 0) (hinj : InjOn ℓ K.vertices) (r : ℝ) :
    (levelPolygons K.space ℓ r).Finite := by
  obtain ⟨G, hGfin, hGspace, hcard, _⟩ :=
    exists_triangulation_fiber_of_injOn_vertices K hcardK hdimE ℓ hℓ hinj r
  let _ : Finite G.faces := hGfin.to_subtype
  simpa only [levelPolygons, hGspace] using finite_isPLSphere_one_subsets G hcard

theorem heightIndex_lt_top (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsCombinatorialManifold 2 K) (hdimE : Module.finrank ℝ E = 3)
    (ℓ : E →ₗ[ℝ] ℝ) (hℓ : ℓ ≠ 0) (hinj : InjOn ℓ K.vertices) :
    heightIndex K.space ℓ < ⊤ := by
  let _ := (finite_heightSingularPoints K hK.isCombinatorialManifoldWithBoundary
    hdimE ℓ hℓ hinj).fintype
  rw [heightIndex, tsum_fintype]
  apply ENat.sum_lt_top.mpr
  intro p _
  exact lt_of_le_of_lt tsub_le_self (finite_levelPolygons K (fun s hs => hK.card_le K hs)
    hdimE ℓ hℓ hinj (ℓ p)).encard_lt_top

theorem natCast_toNat_heightIndex (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsCombinatorialManifold 2 K) (hdimE : Module.finrank ℝ E = 3)
    (ℓ : E →ₗ[ℝ] ℝ) (hℓ : ℓ ≠ 0) (hinj : InjOn ℓ K.vertices) :
    ((heightIndex K.space ℓ).toNat : ℕ∞) = heightIndex K.space ℓ :=
  ENat.natCast_toNat (heightIndex_lt_top K hK hdimE ℓ hℓ hinj).ne

end DifferentialGeometry.Topology.PiecewiseLinear
