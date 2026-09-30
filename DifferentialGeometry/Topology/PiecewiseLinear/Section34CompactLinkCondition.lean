/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.LinkGraphConnectivity
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactVocabulary

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem IsCombinatorialManifoldWithBoundary.mem_connectedComponentIn_sdiff_openEdge
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {L : Geometry.SimplicialComplex ℝ E} [Finite L.faces]
    (hL : IsCombinatorialManifoldWithBoundary 2 L) (hconn : IsConnected L.space)
    {e : Finset E} (he : e ∈ L.faces) (hcard : e.card = 2) {a b : E}
    (ha : {a} ∈ L.faces) (hb : {b} ∈ L.faces) :
    b ∈ connectedComponentIn (L.space \ (convexHull ℝ (e : Set E) \ (e : Set E))) a := by
  classical
  obtain ⟨x, y, hxy, rfl⟩ := Finset.card_eq_two.mp hcard
  set S := L.space \ (convexHull ℝ (({x, y} : Finset E) : Set E) \ (({x, y} : Finset E) : Set E))
  have hxv : x ∈ L.vertices :=
    L.down_closed he (Finset.singleton_subset_iff.mpr (by simp)) (Finset.singleton_nonempty x)
  have hyv : y ∈ L.vertices :=
    L.down_closed he (Finset.singleton_subset_iff.mpr (by simp)) (Finset.singleton_nonempty y)
  let u : L.vertices := ⟨x, hxv⟩
  let v : L.vertices := ⟨y, hyv⟩
  have huv : (SimplicialComplex.edgeGraph L).Adj u v := by
    refine ⟨fun h => hxy (congrArg Subtype.val h), ?_⟩
    convert he using 2
  have hG := edgeGraph_connected_delete_edge_of_isCombinatorialManifoldWithBoundary L hL hconn huv
  have hvertex : ∀ w : L.vertices, (w : E) ∈ S := by
    intro w
    have hw₁ : ({(w : E)} : Finset E) ∈ L.faces := w.2
    refine ⟨L.convexHull_subset_space hw₁ (subset_convexHull ℝ _ (by simp)), fun hw => hw.2 ?_⟩
    have hmem : (w : E) ∈ convexHull ℝ (({(w : E)} : Finset E) : Set E) ∩
        convexHull ℝ (({x, y} : Finset E) : Set E) :=
      ⟨subset_convexHull ℝ _ (by simp), hw.1⟩
    rw [L.convexHull_inter_convexHull hw₁ he] at hmem
    obtain ⟨z, hzw, hzxy⟩ := convexHull_nonempty_iff.mp ⟨_, hmem⟩
    rw [Finset.coe_singleton, mem_singleton_iff] at hzw
    rw [← hzw]
    exact hzxy
  have hstep : ∀ p q : L.vertices,
      ((SimplicialComplex.edgeGraph L).deleteEdges {s(u, v)}).Adj p q →
        (q : E) ∈ connectedComponentIn S p := by
    intro p q hpq
    rw [SimpleGraph.deleteEdges_adj] at hpq
    obtain ⟨⟨-, hface⟩, hnot⟩ := hpq
    have hseg : convexHull ℝ (({(p : E), (q : E)} : Finset E) : Set E) ⊆ S := by
      intro z hz
      refine ⟨L.convexHull_subset_space hface hz, fun hze => hze.2 ?_⟩
      have hmem : z ∈ convexHull ℝ (({(p : E), (q : E)} : Finset E) : Set E) ∩
          convexHull ℝ (({x, y} : Finset E) : Set E) := ⟨hz, hze.1⟩
      rw [L.convexHull_inter_convexHull hface he] at hmem
      have hboth : ¬ (x ∈ (({(p : E), (q : E)} : Finset E) : Set E) ∧
          y ∈ (({(p : E), (q : E)} : Finset E) : Set E)) := by
        rintro ⟨hx, hy⟩
        apply hnot
        simp only [Finset.coe_insert, Finset.coe_singleton, mem_insert_iff,
          mem_singleton_iff] at hx hy
        have hpu : ∀ r : L.vertices, (r : E) = x → r = u := fun r hr => Subtype.ext hr
        have hpv : ∀ r : L.vertices, (r : E) = y → r = v := fun r hr => Subtype.ext hr
        rw [mem_singleton_iff]
        rcases hx with hx | hx <;> rcases hy with hy | hy
        · exact absurd (hx.trans hy.symm) hxy
        · rw [hpu p hx.symm, hpv q hy.symm]
        · rw [hpu q hx.symm, hpv p hy.symm, Sym2.eq_swap]
        · exact absurd (hx.trans hy.symm) hxy
      have hsub : (({(p : E), (q : E)} : Finset E) : Set E) ∩ (({x, y} : Finset E) : Set E) ⊆
          {x} ∨ (({(p : E), (q : E)} : Finset E) : Set E) ∩ (({x, y} : Finset E) : Set E) ⊆
          {y} := by
        by_cases hx : x ∈ (({(p : E), (q : E)} : Finset E) : Set E)
        · left
          rintro w ⟨hwpq, hwxy⟩
          simp only [Finset.coe_insert, Finset.coe_singleton, mem_insert_iff,
            mem_singleton_iff] at hwxy ⊢
          rcases hwxy with h | h
          · exact h
          · rw [h] at hwpq
            exact absurd ⟨hx, hwpq⟩ hboth
        · right
          rintro w ⟨hwpq, hwxy⟩
          simp only [Finset.coe_insert, Finset.coe_singleton, mem_insert_iff,
            mem_singleton_iff] at hwxy ⊢
          rcases hwxy with h | h
          · rw [h] at hwpq
            exact absurd hwpq hx
          · exact h
      rcases hsub with hsub | hsub
      · have hzx := convexHull_mono (𝕜 := ℝ) hsub hmem
        rw [convexHull_singleton, mem_singleton_iff] at hzx
        simp [hzx]
      · have hzy := convexHull_mono (𝕜 := ℝ) hsub hmem
        rw [convexHull_singleton, mem_singleton_iff] at hzy
        simp [hzy]
    exact (convex_convexHull ℝ _).isPreconnected.subset_connectedComponentIn
      (subset_convexHull ℝ _ (by simp)) hseg (subset_convexHull ℝ _ (by simp))
  have hreach : ∀ p q : L.vertices,
      ((SimplicialComplex.edgeGraph L).deleteEdges {s(u, v)}).Reachable p q →
        (q : E) ∈ connectedComponentIn S p := by
    intro p q ⟨w⟩
    induction w with
    | nil => exact mem_connectedComponentIn (hvertex _)
    | @cons p r q hpr w ih =>
      rw [connectedComponentIn_eq (hstep p r hpr)]
      exact ih
  exact hreach ⟨a, ha⟩ ⟨b, hb⟩ (hG.preconnected _ _)

open Classical in
theorem IsCombinatorialManifoldWithBoundary.section34CompactLinkCondition
    {K : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3))} (hK : K.faces.Finite)
    (hKm : IsCombinatorialManifoldWithBoundary 3 K) : Section34CompactLinkCondition K := by
  intro v hv e he hcard a b ha hb
  have : Finite (SimplicialComplex.geometricLink K {v}).faces :=
    (hK.subset (geometricLink_faces_subset K {v})).to_subtype
  have hlink : IsPLSphere 2 (SimplicialComplex.geometricLink K {v}).space ∨
      IsPLBall 2 (SimplicialComplex.geometricLink K {v}).space := by
    convert hKm v hv
  rcases hlink with hS | hB
  · exact hS.isCombinatorialManifold.isCombinatorialManifoldWithBoundary
      |>.mem_connectedComponentIn_sdiff_openEdge hS.isConnected he hcard ha hb
  · exact hB.isCombinatorialManifoldWithBoundary.mem_connectedComponentIn_sdiff_openEdge
      hB.isConnected he hcard ha hb

end DifferentialGeometry.Topology.PiecewiseLinear
