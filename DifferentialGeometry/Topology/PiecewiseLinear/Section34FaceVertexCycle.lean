/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.Section34IncidentEdges

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

variable {Ea : Type} [NormedAddCommGroup Ea] [NormedSpace ℝ Ea] [FiniteDimensional ℝ Ea]
  {M : Type u} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  {U : Set M} {𝒦 𝒦' : LocallyFinitePLPieceIn Ea 3 M U}

theorem exists_section34Face_vertex_cycle
    (hsubdiv : IsSubdivision 𝒦'.complex 𝒦.complex) (hmap : 𝒦'.map = 𝒦.map)
    (ends : Section34EdgeIndex 𝒦 𝒦' → Section34VertexIndex 𝒦 𝒦' × Section34VertexIndex 𝒦 𝒦')
    (hends : ∀ e, (e.1 : Set Ea) = ((ends e).1.1 : Set Ea) ∪ ((ends e).2.1 : Set Ea))
    (s : Section34SimplexIndex 𝒦 3) :
    ∃ (n : ℕ) (v : Fin (n + 3) → Section34VertexIndex 𝒦 𝒦'),
      Function.Injective v ∧ (∀ w, Section34Incident w.1 s.1 ↔ ∃ i, v i = w) ∧
      ∀ i j, i ≠ j → ((SimpleGraph.cycleGraph (n + 3)).Adj i j ↔
        ∃ e : Section34EdgeIndex 𝒦 𝒦',
          (v i = (ends e).1 ∧ v j = (ends e).2) ∨
            (v i = (ends e).2 ∧ v j = (ends e).1)) := by
  classical
  set R : Set Ea := ⋃ u ∈ s.1, convexHull ℝ ((s.1.erase u : Finset Ea) : Set Ea)
  have hRs : R ⊆ convexHull ℝ (s.1 : Set Ea) :=
    iUnion₂_subset fun u _ => convexHull_mono (Finset.coe_subset.mpr (Finset.erase_subset u s.1))
  have hs𝒦 : convexHull ℝ (s.1 : Set Ea) ⊆ 𝒦.complex.space :=
    𝒦.complex.convexHull_subset_space s.2.1
  have hsp' : 𝒦'.complex.space = 𝒦.complex.space := hsubdiv.1
  have hRsph : IsPLSphere 1 R := isPLSphere_biUnion_erase s.1 (𝒦.complex.indep s.2.1) s.2.2
  have hL₀ : (restrict 𝒦.complex R).space = R := by
    refine Subset.antisymm (restrict_space_subset _ _) fun x hx => ?_
    obtain ⟨u, hu, hxu⟩ := mem_iUnion₂.mp hx
    have hcard : (s.1.erase u).card = 2 := by rw [Finset.card_erase_of_mem hu, s.2.2]
    exact (restrict 𝒦.complex R).convexHull_subset_space
      ⟨𝒦.complex.down_closed s.2.1 (Finset.erase_subset u s.1) (Finset.card_pos.mp (by omega)),
        subset_iUnion₂ (s := fun u (_ : u ∈ s.1) =>
          convexHull ℝ ((s.1.erase u : Finset Ea) : Set Ea)) u hu⟩ hxu
  set L := restrict 𝒦'.complex R
  have hLsub : IsSubdivision L (restrict 𝒦.complex R) := by
    have := hsubdiv.restrict (restrict 𝒦.complex R) (restrict_faces_subset _ _)
    rwa [hL₀] at this
  have hLsp : L.space = R := hLsub.1.trans hL₀
  have hRc : IsCompact R := hRsph.isPolyhedron.isCompact
  have hLfin : L.faces.Finite := by
    refine (𝒦'.finite_faces_inter_of_isCompact hRc ((hRs.trans hs𝒦).trans hsp'.ge)).subset ?_
    rintro σ ⟨hσ, hσR⟩
    obtain ⟨q, hq⟩ := 𝒦'.complex.nonempty_of_mem_faces hσ
    exact ⟨hσ, q, subset_convexHull ℝ _ (Finset.mem_coe.mpr hq),
      hσR (subset_convexHull ℝ _ (Finset.mem_coe.mpr hq))⟩
  have : Finite L.faces := hLfin.to_subtype
  have hLman : IsCombinatorialManifold 1 L :=
    IsPLSphere.isCombinatorialManifold (n := 0) (by rw [hLsp]; exact hRsph)
  have hLconn : (SimplicialComplex.edgeGraph L).Connected :=
    edgeGraph_connected_of_isConnected_space L (by rw [hLsp]; exact hRsph.isConnected)
  let _ : Fintype L.vertices := (SimplicialComplex.finite_vertices L).fintype
  have hdeg : ∀ v, ((SimplicialComplex.edgeGraph L).neighborSet v).ncard = 2 :=
    ncard_neighborSet_edgeGraph_eq_two hLman
  have hgraphR : ∀ x ∈ R, 𝒦'.map x ∈ graphSkeletonSpace 𝒦 := fun x hx => by
    rw [hmap]
    exact map_mem_graphSkeletonSpace_of_mem_biUnion_convexHull_erase s hx
  have hRof : ∀ σ : Finset Ea, σ ∈ 𝒦'.complex.faces →
      simplexBody 𝒦' σ ⊆ graphSkeletonSpace 𝒦 → (σ : Set Ea) ⊆ convexHull ℝ (s.1 : Set Ea) →
        convexHull ℝ (σ : Set Ea) ⊆ R := by
    intro σ hσ hσg hσs y hy
    have hy𝒦 : y ∈ 𝒦.complex.space := hsp'.le (𝒦'.complex.convexHull_subset_space hσ hy)
    have hys : y ∈ convexHull ℝ (s.1 : Set Ea) := convexHull_min hσs (convex_convexHull ℝ _) hy
    have hyg : 𝒦.map y ∈ graphSkeletonSpace 𝒦 := by
      rw [← hmap]
      exact hσg ⟨y, hy, rfl⟩
    exact mem_biUnion_convexHull_erase_of_map_mem_graphSkeletonSpace s hy𝒦 hys hyg
  have hvR : ∀ v : L.vertices, (v : Ea) ∈ R := fun v =>
    v.2.2 (subset_convexHull ℝ _ (by simp))
  let wv : L.vertices → Section34VertexIndex 𝒦 𝒦' := fun v =>
    ⟨{(v : Ea)}, v.2.1, Finset.card_singleton _, by
      rintro _ ⟨y, hy, rfl⟩
      exact hgraphR y (v.2.2 hy)⟩
  have hwv : ∀ v : L.vertices, (wv v).1 = {(v : Ea)} := fun _ => rfl
  have hwvinj : Function.Injective wv := by
    intro v v' hvv
    have h1 := congrArg Subtype.val hvv
    rw [hwv, hwv, Finset.singleton_inj] at h1
    exact Subtype.ext h1
  have hwvinc : ∀ v : L.vertices, Section34Incident (wv v).1 s.1 := by
    intro v
    change ((({(v : Ea)} : Finset Ea)) : Set Ea) ⊆ convexHull ℝ (s.1 : Set Ea)
    rw [Finset.coe_singleton, singleton_subset_iff]
    exact hRs (hvR v)
  have hwvsurj : ∀ w : Section34VertexIndex 𝒦 𝒦', Section34Incident w.1 s.1 →
      ∃ v : L.vertices, wv v = w := by
    intro w hw
    obtain ⟨a, ha⟩ := Finset.card_eq_one.mp w.2.2.1
    have haR : convexHull ℝ (({a} : Finset Ea) : Set Ea) ⊆ R := by
      rw [← ha]
      exact hRof w.1 w.2.1 w.2.2.2 hw
    have haL : ({a} : Finset Ea) ∈ L.faces := ⟨ha ▸ w.2.1, haR⟩
    exact ⟨⟨a, haL⟩, Subtype.ext ha.symm⟩
  have hadj : ∀ v v' : L.vertices, v ≠ v' →
      ((SimplicialComplex.edgeGraph L).Adj v v' ↔
        ∃ e : Section34EdgeIndex 𝒦 𝒦',
          (wv v = (ends e).1 ∧ wv v' = (ends e).2) ∨
            (wv v = (ends e).2 ∧ wv v' = (ends e).1)) := by
    intro v v' hvv
    have hww : wv v ≠ wv v' := fun he => hvv (hwvinj he)
    constructor
    · rintro ⟨-, hvL⟩
      have hcard : ({(v : Ea), (v' : Ea)} : Finset Ea).card = 2 :=
        Finset.card_pair fun he => hvv (Subtype.ext he)
      let e : Section34EdgeIndex 𝒦 𝒦' :=
        ⟨{(v : Ea), (v' : Ea)}, hvL.1, hcard, by
          rintro _ ⟨y, hy, rfl⟩
          exact hgraphR y (hvL.2 hy)⟩
      have hve : (wv v).1 ⊆ e.1 := by
        change ({(v : Ea)} : Finset Ea) ⊆ {(v : Ea), (v' : Ea)}
        simp
      have hv'e : (wv v').1 ⊆ e.1 := by
        change ({(v' : Ea)} : Finset Ea) ⊆ {(v : Ea), (v' : Ea)}
        simp
      have h₁ := eq_or_eq_of_section34VertexIndex_subset e (hends e) hve
      have h₂ := eq_or_eq_of_section34VertexIndex_subset e (hends e) hv'e
      refine ⟨e, ?_⟩
      rcases h₁ with h₁ | h₁ <;> rcases h₂ with h₂ | h₂
      · exact (hww (h₁.trans h₂.symm)).elim
      · exact Or.inl ⟨h₁, h₂⟩
      · exact Or.inr ⟨h₁, h₂⟩
      · exact (hww (h₁.trans h₂.symm)).elim
    · rintro ⟨e, he⟩
      have hew : (e.1 : Set Ea) = ((wv v).1 : Set Ea) ∪ ((wv v').1 : Set Ea) := by
        rcases he with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
        · rw [h₁, h₂]
          exact hends e
        · rw [h₁, h₂, union_comm]
          exact hends e
      have hepair : e.1 = {(v : Ea), (v' : Ea)} := by
        apply Finset.coe_injective
        rw [hew, hwv, hwv]
        simp [Set.pair_comm]
      refine ⟨hvv, ?_⟩
      rw [← hepair]
      refine ⟨e.2.1, hRof e.1 e.2.1 e.2.2.2 ?_⟩
      rw [hepair, Finset.coe_pair]
      exact insert_subset_iff.mpr ⟨hRs (hvR v), singleton_subset_iff.mpr (hRs (hvR v'))⟩
  obtain ⟨g⟩ := (SimplicialComplex.edgeGraph L).exists_cycleGraphIsoOfConnectedDegreeTwo hLconn hdeg
  have h3 := (SimplicialComplex.edgeGraph L).three_le_card_of_connected_degree_two hLconn hdeg
  obtain ⟨m, hm⟩ : ∃ m, Fintype.card L.vertices = m + 3 :=
    ⟨Fintype.card L.vertices - 3, by omega⟩
  rw [hm] at g
  refine ⟨m, fun i => wv (g i), hwvinj.comp g.injective, ?_, ?_⟩
  · intro w
    constructor
    · intro hw
      obtain ⟨v, hv⟩ := hwvsurj w hw
      obtain ⟨i, rfl⟩ := g.surjective v
      exact ⟨i, hv⟩
    · rintro ⟨i, rfl⟩
      exact hwvinc (g i)
  · intro i j hij
    rw [← g.map_adj_iff]
    exact hadj (g i) (g j) (fun he => hij (g.injective he))

end DifferentialGeometry.Topology.PiecewiseLinear
