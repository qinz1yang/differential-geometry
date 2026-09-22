/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.BoundaryGluing
import DifferentialGeometry.Topology.PiecewiseLinear.BoundedSurfaceComponent
import DifferentialGeometry.Topology.PiecewiseLinear.ManifoldInteriorConnected
import DifferentialGeometry.Topology.PiecewiseLinear.MoiseChain
import DifferentialGeometry.Topology.PiecewiseLinear.SurfaceInteriorFrontierOpen
import DifferentialGeometry.Topology.PiecewiseLinear.SurfaceInteriorFrontierContact
import DifferentialGeometry.Topology.PiecewiseLinear.TriodFrontierWitnesses
import DifferentialGeometry.Topology.PiecewiseLinear.ExistsTriodChartAtCommonBoundary

/-!
# Three polyhedral surfaces with a common boundary

The assembly proves the existing `Moise267` from four reviewed OK, frozen leaves whose proofs
remain OPEN. The source is Moise
26.7, printed page 195, with the three-arc argument of 2.7, printed pages 20--21. The common
boundary is nonempty and may have several connected components. No connectedness of that
boundary is assumed.

The local chart is the product version of the small disk transverse to a common boundary
edge. Its three pages meet the coordinate plane in the positive horizontal ray, negative
horizontal ray and positive vertical ray. The chart records the actual three surface germs,
not just three subsets of their images. In the three-arc leaf, the closed surface obtained
from each pair prevents two distinct local sectors from belonging to the same global side.
Its conclusion consists of two frontier contact points and one point on the other side of
their pair. It does not assert a global frontier formula or a bounded complementary region.

Open leaves, owned by the three-surface lane, all reviewed OK and frozen:

* `exists_triod_chart_at_common_boundary`: a regular common boundary point and a PL chart
  displaying the three surface germs as the three coordinate pages.
* `exists_surface_interior_frontier_contact`: every complementary component touches the
  interior of at least one surface; its frontier cannot be supported only on the boundary.
* `isOpen_preimage_frontier_component_surface_interior`: contact with a complementary
  component is relatively open in a surface interior, away from the other closed obstacles.
* `exists_frontier_pair_witnesses_of_triod_chart`: the cyclic order of the three transverse
  arcs gives two interior frontier contacts and a third interior point in the other side.

Boundary gluing, connectedness and density of each surface interior, and bounded-side
separation for each closed pair are supplied by proved real modules. The assembly propagates
the two contact points over their connected interiors, excludes the third interior from the
closure of the exterior, and uses the unbounded hypothesis only to select the opposite
bounded side. Thus none of the leaves restates `Moise267`.

The first review and lead due diligence are recorded in
`consult/BA-section26-three-surfaces-first-review-digest.md`. No hypotheses were added.
The first interior contact is propagated before the selected chart point is used. The fourth
leaf must use the full two-component theorem with both frontiers equal to the closed pair;
three local sectors alone do not rule out reconnection outside the chart.

The joint fixture is UNTESTED in Lean. Take the two complementary annuli of a PL torus and
push a copy of one annulus inward, fixing its two boundary circles. The three annuli have
disjoint interiors and the same two boundary circles. This tests both the local three-page
chart and the global bounded-side conclusion. An empty common boundary is excluded by the
named input itself.

Proved and imported on 2026-09-22 (Gemini batch, lead-accepted with zero-diagnostic checks and an
axiom audit; statements byte-identical with the frozen leaves):
`isOpen_preimage_frontier_component_surface_interior`, `exists_surface_interior_frontier_contact`,
`exists_frontier_pair_witnesses_of_triod_chart`.

Proved and imported (Opus 5.5 fill worker, lead-accepted on 2026-09-22 with a zero-diagnostic
check and an axiom audit; statement byte-identical with the frozen leaf):
`exists_triod_chart_at_common_boundary` (a boundary point that is a vertex of none of the three
surfaces; the existing `exists_isPLHomeomorphOn_straighten_rays`). With this the file has no
`sorry` left: the assembly `moise267` is a real proof, and the module is ready to be promoted out
of `Skeleton/`. Note the `DecidableEq` mismatch on `EuclideanSpace ℝ (Fin 3)`: `boundaryComplex`
in these statements uses the `WithLp` instance, not the classical one, so generic `open Classical`
lemmas must swap the instance.

Promoted out of `Skeleton/` on 2026-09-22: every former leaf is proved in an imported real module
(`SurfaceInteriorFrontierOpen`, `SurfaceInteriorFrontierContact`, `TriodFrontierWitnesses` from the
Gemini batch; `ExistsTriodChartAtCommonBoundary` from an Opus 5.5 worker), so `moise267` below is
an unconditional proof of `Moise267`, and the skeleton vocabulary of this file is now real.
-/

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

private theorem isBounded_component_of_not_mem_unbounded_component
    (K : Geometry.SimplicialComplex ℝ E3) [Finite K.faces]
    (hK : IsCombinatorialManifold 2 K) (hconn : IsConnected K.space)
    {x y : E3} (hx : x ∈ K.spaceᶜ) (hy : y ∈ K.spaceᶜ)
    (hunbounded : ¬ Bornology.IsBounded (connectedComponentIn K.spaceᶜ x))
    (hyx : y ∉ connectedComponentIn K.spaceᶜ x) :
    Bornology.IsBounded (connectedComponentIn K.spaceᶜ y) := by
  obtain ⟨a, ha, b, hb, hbounded, _, hcover, _, _, _⟩ :=
    hK.exists_bounded_connectedComponentIn_pair_compl K (by simp) hconn
  have hxB : x ∈ connectedComponentIn K.spaceᶜ b := by
    rcases hcover.symm.subset hx with hxA | hxB
    · exact (hunbounded ((connectedComponentIn_eq hxA) ▸ hbounded)).elim
    · exact hxB
  have hyA : y ∈ connectedComponentIn K.spaceᶜ a := by
    rcases hcover.symm.subset hy with hyA | hyB
    · exact hyA
    · exact (hyx ((connectedComponentIn_eq hxB).subset hyB)).elim
  exact (connectedComponentIn_eq hyA) ▸ hbounded

theorem moise267 : Moise267 := by
  classical
  intro M hfin hM hconn hboundary hne hdisjoint x hx hunbounded
  let d : DecidableEq E3 := inferInstance
  have hd : d = Classical.decEq E3 := Subsingleton.elim _ _
  let B := (boundaryComplex 2 (M 0)).space
  let I : Fin 3 → Set E3 := fun i => (M i).space \ B
  let U := connectedComponentIn (⋃ i, (M i).space)ᶜ x
  have hB (i : Fin 3) : B = (boundaryComplex 2 (M i)).space := hboundary 0 i
  have hBc (i : Fin 3) :
      B = (@boundaryComplex E3 _ _ (Classical.decEq E3) 2 (M i)).space := by
    have h := hB i
    change B = (@boundaryComplex E3 _ _ d 2 (M i)).space at h
    rwa [hd] at h
  have hBS (i : Fin 3) : B ⊆ (M i).space :=
    (hB i).subset.trans (boundaryComplex_space_subset 2 (M i))
  have hpoly (i : Fin 3) : IsPolyhedron (M i).space := by
    let _ : Finite (M i).faces := (hfin i).to_subtype
    exact isPolyhedron_space (M i)
  have hclosed : IsClosed (⋃ i, (M i).space) :=
    isClosed_iUnion_of_finite fun i => (hpoly i).isClosed
  have hUopen : IsOpen U := hclosed.isOpen_compl.connectedComponentIn
  have hinter (i j : Fin 3) (hij : i ≠ j) : (M i).space ∩ (M j).space = B := by
    apply Subset.antisymm _ (subset_inter (hBS i) (hBS j))
    rintro z ⟨hzi, hzj⟩
    by_contra hzB
    exact disjoint_left.mp (hdisjoint i j hij)
      ⟨hzi, fun h => hzB ((hB i).symm ▸ h)⟩
      ⟨hzj, fun h => hzB ((hB j).symm ▸ h)⟩
  have hpair (i j : Fin 3) (hij : i ≠ j) :
      ∃ K : Geometry.SimplicialComplex ℝ E3,
        K.faces.Finite ∧ IsCombinatorialManifold 2 K ∧ IsConnected K.space ∧
          K.space = (M i).space ∪ (M j).space := by
    let _ : Finite (M i).faces := (hfin i).to_subtype
    let _ : Finite (M j).faces := (hfin j).to_subtype
    obtain ⟨K, hKfin, hK, hKspace⟩ := exists_isCombinatorialManifold_space_union
      (M i) (M j) (hM i) (hM j)
      ((hinter i j hij).trans (hBc i)) ((hinter i j hij).trans (hBc j))
    have hmeet : ((M i).space ∩ (M j).space).Nonempty := by
      rw [hinter i j hij]
      exact hne
    exact ⟨K, hKfin, hK, hKspace.symm ▸ IsConnected.union hmeet (hconn i) (hconn j), hKspace⟩
  have hIconn (i : Fin 3) : IsConnected (I i) := by
    let _ : Finite (M i).faces := (hfin i).to_subtype
    have h := (hM i).isConnected_sdiff_boundaryComplex_space (hconn i)
    change IsConnected ((M i).space \
      (@boundaryComplex E3 _ _ (Classical.decEq E3) 2 (M i)).space) at h
    rw [← hd] at h
    simpa only [I, hB i] using h
  have hIdense (i : Fin 3) : (M i).space ⊆ closure (I i) := by
    let _ : Finite (M i).faces := (hfin i).to_subtype
    simpa only [I, hB i] using (hM i).space_subset_closure_sdiff_boundaryComplex_space
  have hpropagate (i : Fin 3) {z : E3} (hzI : z ∈ I i) (hzfront : z ∈ frontier U) :
      (M i).space ⊆ frontier U := by
    let _ : Finite (M i).faces := (hfin i).to_subtype
    let T := ⋃ j : {j : Fin 3 // j ≠ i}, (M j).space
    have hT : IsClosed T := isClosed_iUnion_of_finite fun j => (hpoly j).isClosed
    have hTinter : (M i).space ∩ T ⊆ (boundaryComplex 2 (M i)).space := by
      rintro y ⟨hyi, hyT⟩
      obtain ⟨j, hyj⟩ := mem_iUnion.mp hyT
      exact (hB i).subset ((hinter i j j.property.symm).subset ⟨hyi, hyj⟩)
    have htotal : (M i).space ∪ T = ⋃ j, (M j).space := by
      ext y
      constructor
      · rintro (hyi | hyT)
        · exact mem_iUnion.mpr ⟨i, hyi⟩
        · obtain ⟨j, hyj⟩ := mem_iUnion.mp hyT
          exact mem_iUnion.mpr ⟨j, hyj⟩
      · intro hy
        obtain ⟨j, hyj⟩ := mem_iUnion.mp hy
        by_cases hji : j = i
        · exact Or.inl (hji ▸ hyj)
        · exact Or.inr (mem_iUnion.mpr ⟨⟨j, hji⟩, hyj⟩)
    have hopen : IsOpen (((↑) : I i → E3) ⁻¹' frontier U) := by
      change IsOpen (((↑) : ↥((M i).space \ B) → E3) ⁻¹'
        frontier (connectedComponentIn (⋃ j, (M j).space)ᶜ x))
      rw [hB i]
      simpa only [htotal] using
        isOpen_preimage_frontier_component_surface_interior (M i) (hM i) hT hTinter x
    let _ : PreconnectedSpace (I i) := Subtype.preconnectedSpace (hIconn i).isPreconnected
    have hall := (show IsClopen (((↑) : I i → E3) ⁻¹' frontier U) from
      ⟨isClosed_frontier.preimage continuous_subtype_val, hopen⟩).eq_univ
        ⟨⟨z, hzI⟩, hzfront⟩
    have hIsub : I i ⊆ frontier U := by
      intro y hy
      have : (⟨y, hy⟩ : I i) ∈ (((↑) : I i → E3) ⁻¹' frontier U) := by
        rw [hall]
        exact mem_univ _
      exact this
    exact (hIdense i).trans (closure_minimal hIsub isClosed_frontier)
  obtain ⟨p, e, hpB, hpsource, hep, he, htrace⟩ :=
    exists_triod_chart_at_common_boundary M hfin hM hboundary hne hdisjoint
  obtain ⟨l, z, hzI, hzfront⟩ :=
    exists_surface_interior_frontier_contact M hfin hM hconn hboundary hne hdisjoint hx
  have hpfront : p ∈ frontier U :=
    hpropagate l (by simpa only [I, hB l] using hzI) hzfront (hBS l hpB)
  obtain ⟨i, j, k, hij, hik, hjk, ⟨u, huI, hufront⟩, ⟨v, hvI, hvfront⟩, w, hwI, hwX⟩ :=
    exists_frontier_pair_witnesses_of_triod_chart (fun i => (M i).space) B
      hinter hpair e hpB hpsource hep he htrace hx hpfront
  have hfrontPair : (M i).space ∪ (M j).space ⊆ frontier U :=
    union_subset (hpropagate i huI hufront) (hpropagate j hvI hvfront)
  have hIpair : I k ⊆ ((M i).space ∪ (M j).space)ᶜ := by
    rintro y ⟨hyk, hyB⟩ (hyi | hyj)
    · exact hyB ((hinter i k hik).subset ⟨hyi, hyk⟩)
    · exact hyB ((hinter j k hjk).subset ⟨hyj, hyk⟩)
  let X := connectedComponentIn ((M i).space ∪ (M j).space)ᶜ x
  have hUX : U ⊆ X := connectedComponentIn_mono x (by
    intro y hy hpairmem
    exact hy (hpairmem.elim (fun h => mem_iUnion.mpr ⟨i, h⟩)
      (fun h => mem_iUnion.mpr ⟨j, h⟩)))
  have hIcomponent := (hIconn k).isPreconnected.subset_connectedComponentIn hwI hIpair
  have hInotX : ∀ y ∈ I k, y ∉ X := by
    intro y hy hyX
    have heq := (connectedComponentIn_eq hyX).trans
      (connectedComponentIn_eq (hIcomponent hy)).symm
    exact hwX (heq.symm ▸ mem_connectedComponentIn (hIpair hwI))
  have hfrontTotal : frontier U ⊆ ⋃ i, (M i).space := by
    intro y hy
    by_contra hyTotal
    have hyU : y ∈ U :=
      (DifferentialGeometry.Topology.closure_connectedComponentIn_inter _ x).subset
        ⟨hy.1, hyTotal⟩
    exact hy.2 (hUopen.interior_eq.symm ▸ hyU)
  have hfront : frontier U = (M i).space ∪ (M j).space := by
    apply Subset.antisymm _ hfrontPair
    intro y hy
    by_contra hyPair
    obtain ⟨a, hya⟩ := mem_iUnion.mp (hfrontTotal hy)
    have hak : a = k := by
      have hai : a ≠ i := fun h => hyPair (Or.inl (h ▸ hya))
      have haj : a ≠ j := fun h => hyPair (Or.inr (h ▸ hya))
      omega
    have hyk : y ∈ I k :=
      ⟨hak ▸ hya, fun hyB => hyPair (Or.inl (hBS i hyB))⟩
    exact hInotX y hyk
      ((DifferentialGeometry.Topology.closure_connectedComponentIn_inter _ x).subset
        ⟨closure_mono hUX hy.1, hyPair⟩)
  refine ⟨i, j, k, hij, hik, hjk, hfront, ?_⟩
  intro y hy
  have hyI : y ∈ I k := by simpa only [I, hB k] using hy
  obtain ⟨K, hKfin, hK, hKconn, hKspace⟩ := hpair i j hij
  let _ : Finite K.faces := hKfin.to_subtype
  have hxK : x ∈ K.spaceᶜ := by
    rw [hKspace]
    exact fun h => hx (h.elim (fun hi => mem_iUnion.mpr ⟨i, hi⟩)
      (fun hj => mem_iUnion.mpr ⟨j, hj⟩))
  have hyK : y ∈ K.spaceᶜ := by rw [hKspace]; exact hIpair hyI
  have hXunbounded : ¬ Bornology.IsBounded (connectedComponentIn K.spaceᶜ x) := by
    rw [hKspace]
    exact fun h => hunbounded (h.subset hUX)
  have hyX : y ∉ connectedComponentIn K.spaceᶜ x := by rw [hKspace]; exact hInotX y hyI
  simpa only [hKspace] using
    isBounded_component_of_not_mem_unbounded_component K hK hKconn hxK hyK hXunbounded hyX

end DifferentialGeometry.Topology.PiecewiseLinear
