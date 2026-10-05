import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39P0Regression

/-!
# FC39 producer, packet P0 (gate 1): regression test C, the projection to the dry circle link

Review 49 (regression tests, C): the projection theorem
`LabelledCornerCompatibility → DryCircleLink (original) → DryCircleLink (swapped)`, the first step
DERIVED from the contract fields (`CircleRestrictionLink`, the `endOfCorner` bijection,
`corner_center`, the junction field `rim_fibre`), not a new test hypothesis:

* `LabelledCornerCompatibility.dryCircleLink` — the labelled compatibility projects to the old dry
  `CircleLink` of the original data;
* `LabelledCornerCompatibility.dryCircleLink_swap` — hence the dry link of the swapped data holds;
* `regressionC_projected` — test C with the dry links derived: the dry link holds for the original
  AND the swapped data, the swapped rim charts form a rim chart layer, the old S11b formula fails
  for them, and the new contract rejects them.
-/

set_option autoImplicit false

noncomputable section

open Set Function
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert GC.GraphManifold
open Manifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold.Assembly.FC39P0

variable {W : CompactCarrier.{u}}

/-- **The labelled compatibility projects to the dry `CircleLink`** (derived from the restriction
link, the corner–endpoint bijection, `corner_center` and `rim_fibre`). -/
theorem LabelledCornerCompatibility.dryCircleLink {n : ℕ} {E : BoundaryTori W n}
    {Pr : FC39Prepared W E} {H : EdgeLayer W} {circ : CircleRegion W} {K : RimChartLayer W H circ}
    (L : LabelledCornerCompatibility Pr H circ K) :
    DryCircleLink Pr.rows.edge Pr.rows.circle circ := by
  refine ⟨L.circleLink.region_eq, L.circleLink.ι, L.circleLink.ι_isOpenEmbedding,
    L.circleLink.proj_eq, fun k => ?_, fun c hc => ?_⟩
  · refine ⟨(L.endOfCorner k).1, (L.endOfCorner k).2, ?_⟩
    rw [L.corner_center k]
    exact Pr.rows.junctions.rim_fibre _ (Pr.rows.edge.frontier_cbase_subset (L.endOfCorner k).2)
  · let e : Pr.rows.edge.EdgeEnd := ⟨c, hc⟩
    refine ⟨L.endOfCorner.symm e, ?_⟩
    have he : (L.endOfCorner (L.endOfCorner.symm e)).1 = c := by
      rw [Equiv.apply_symm_apply]
    rw [L.corner_center, he]
    exact Pr.rows.junctions.rim_fibre c (Pr.rows.edge.frontier_cbase_subset hc)

/-- The dry link of the swapped data follows from the labelled compatibility of the original. -/
theorem LabelledCornerCompatibility.dryCircleLink_swap {n : ℕ} {E : BoundaryTori W n}
    {Pr : FC39Prepared W E} {H : EdgeLayer W} {circ : CircleRegion W} {K : RimChartLayer W H circ}
    (L : LabelledCornerCompatibility Pr H circ K) :
    DryCircleLink Pr.rows.edge Pr.rows.circle (swapAxesRegion circ) :=
  L.dryCircleLink.swapAxes

/-- **Regression test C with the dry links derived.** For any labelled compatibility and the vertex
formula at one rim: the dry link holds for the original and for the swapped data, the swapped rim
charts form a rim chart layer, the old S11b formula fails for them, and the new contract rejects
them. -/
theorem regressionC_projected {n : ℕ} {E : BoundaryTori W n} {Pr : FC39Prepared W E}
    {H : EdgeLayer W} {circ : CircleRegion W} (K : RimChartLayer W H circ)
    (L : LabelledCornerCompatibility Pr H circ K) (h : Fin H.handleCount) (b : Bool)
    (V₀ : Set W.Carrier) (θ : Circle)
    (hv : ∀ {p}, p ∈ (K.rimChart h b).source → (K.rimChart h b p ∈ V₀ ↔ p.2.2 ≤ 0)) :
    DryCircleLink Pr.rows.edge Pr.rows.circle circ ∧
      DryCircleLink Pr.rows.edge Pr.rows.circle (swapAxesRegion circ) ∧
      Nonempty (RimChartLayer W H (swapAxesRegion circ)) ∧
      (¬ ∀ {p}, p ∈ (K.swap.rimChart h b).source → (K.swap.rimChart h b p ∈ V₀ ↔ p.2.2 ≤ 0)) ∧
      IsEmpty (LabelledCornerCompatibility Pr H (swapAxesRegion circ) K.swap) := by
  obtain ⟨h1, h2, h3, h4⟩ := regressionC K L h b V₀ θ hv
  exact ⟨L.dryCircleLink, h1 L.dryCircleLink, h2, h3, h4⟩

end GC.GraphManifold.Assembly.FC39P0
