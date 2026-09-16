import DifferentialGeometry.Topology.PiecewiseLinear.FiberCoordinates
import DifferentialGeometry.Topology.PiecewiseLinear.PolygonalCycles

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem exists_isPLSphere_one_of_isCycle_of_subset_fiber
    (G : Geometry.SimplicialComplex ℝ E) [Finite G.faces] (hdimE : Module.finrank ℝ E = 3)
    (ℓ : E →ₗ[ℝ] ℝ) (hℓ : ℓ ≠ 0) {r : ℝ} (hGr : G.space ⊆ {x | ℓ x = r})
    {a : G.vertices} (p : (SimplicialComplex.edgeGraph G).Walk a a) (hp : p.IsCycle) :
    ∃ J : Set E, IsPLSphere 1 J ∧ J ⊆ G.space ∧
      ∀ u v : G.vertices, s(u, v) ∈ p.edges → segment ℝ (u : E) (v : E) ⊆ J := by
  classical
  obtain ⟨e, π, hleft, hfixed, -⟩ := exists_affine_coordinates_of_linear_fiber hdimE ℓ hℓ r
  have hπinj : InjOn π G.space := by
    intro x hx y hy hxy
    exact ((hfixed x).mpr (hGr hx)).symm.trans ((congrArg e hxy).trans ((hfixed y).mpr (hGr hy)))
  obtain ⟨L, hLfin, hLspace, hLfaces, -⟩ := exists_simplicialComplex_image_of_affineOn_faces G (f := π)
    (fun _ _ => ⟨π.toAffineMap, fun _ _ => rfl⟩) hπinj
  have hvertex (v : G.vertices) : π v ∈ L.vertices := by
    apply (hLfaces {π v}).mpr
    refine ⟨{(v : E)}, v.2, ?_⟩
    simp only [Finset.image_singleton]
  let ψ : G.vertices → L.vertices := fun v => ⟨π v, hvertex v⟩
  have hψinj : Function.Injective ψ := by
    intro u v huv
    apply Subtype.ext
    exact hπinj (G.vertices_subset_space u.2) (G.vertices_subset_space v.2)
      (congrArg Subtype.val huv)
  let φ : SimplicialComplex.edgeGraph G →g SimplicialComplex.edgeGraph L :=
    { toFun := ψ
      map_rel' := by
        intro u v huv
        refine ⟨fun h => huv.1 (hψinj h), ?_⟩
        apply (hLfaces _).mpr
        refine ⟨{(u : E), (v : E)}, ?_, ?_⟩
        · exact huv.2
        · ext y
          simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_image]
          change (y = π u ∨ y = π v) ↔ ∃ x, (x = (u : E) ∨ x = (v : E)) ∧ π x = y
          constructor
          · rintro (rfl | rfl)
            · exact ⟨u, Or.inl rfl, rfl⟩
            · exact ⟨v, Or.inr rfl, rfl⟩
          · rintro ⟨x, (rfl | rfl), rfl⟩
            · exact Or.inl rfl
            · exact Or.inr rfl }
  have hcycle : (p.map φ).IsCycle :=
    (SimpleGraph.Walk.isCycle_map_iff_of_injective hψinj).mpr hp
  obtain ⟨J, hJL, -, -, hJedges⟩ := exists_polygonalCircle_of_isCycle L (p.map φ) hcycle
  have hJP := (isPLSphere_one_carrier J).isPolyhedron
  have he : IsPLHomeomorphOn e J.carrier (e '' J.carrier) :=
    isPLHomeomorphOn_of_isPiecewiseAffineOn_of_bijOn hJP
      ((isPiecewiseAffineOn_of_affine e isOpen_univ).mono_of_isPolyhedron hJP (subset_univ _))
      ⟨fun x hx => mem_image_of_mem e hx, hleft.injective.injOn, fun _ h => h⟩
  refine ⟨e '' J.carrier, (isPLSphere_one_carrier J).of_isPLHomeomorphOn he, ?_, ?_⟩
  · rintro x ⟨y, hy, rfl⟩
    obtain ⟨z, hz, hzπ⟩ := hLspace ▸ hJL hy
    rw [← hzπ, (hfixed z).mpr (hGr hz)]
    exact hz
  · intro u v huv x hx
    have hmap : s(φ u, φ v) ∈ (p.map φ).edges := by
      rw [SimpleGraph.Walk.edges_map]
      exact List.mem_map.mpr ⟨s(u, v), huv, rfl⟩
    have hπx : π x ∈ segment ℝ (π u) (π v) := by
      have hx' := mem_image_of_mem π.toAffineMap hx
      rw [image_segment] at hx'
      exact hx'
    have hxJ : π x ∈ J.carrier := hJedges (φ u) (φ v)
      (SimpleGraph.Walk.adj_toSubgraph_iff_mem_edges.mpr hmap) hπx
    have hface : {(u : E), (v : E)} ∈ G.faces := by
      exact (p.adj_of_mem_edges huv).2
    have hxG : x ∈ G.space := G.convexHull_subset_space hface
      (by simpa only [Finset.coe_pair, convexHull_pair] using hx)
    exact ⟨π x, hxJ, (hfixed x).mpr (hGr hxG)⟩

end DifferentialGeometry.Topology.PiecewiseLinear
