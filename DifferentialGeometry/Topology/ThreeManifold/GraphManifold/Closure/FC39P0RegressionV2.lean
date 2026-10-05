import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39P0SphereCornersDry
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39P0CornersV2

/-!
# FC39 producer, regression test C over the prepared rows V2 (D58-1, G1b)

Lane FC39-G-GFF(b). The Pr-indexed regression theorems of `FC39P0Regression.lean` and
`FC39P0SphereCornersDry.lean` (review 49, test C) for `LabelledCornerCompatibilityV2` over
`Pr : FC39PreparedV2 W E`: the V2 contract still rejects the axis-swapped data and still projects to
the dry circle link. The proofs are the accepted ones (they read `height_eq`, the restriction link,
`endOfCorner`, `corner_center` and `rim_fibre`, never the global face functions); the generic
pieces (`swapAxesRegion`, `RimChartLayer.swap`, `not_rimVertex_swap`, `DryCircleLink.swapAxes`)
are reused.

* `isEmpty_labelled_swap_GGFF`, `regressionC_GGFF`;
* `LabelledCornerCompatibilityV2.dryCircleLink`, `.dryCircleLink_swap`, `regressionC_projected_GGFF`.
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

/-- **The V2 contract rejects the swapped data**: with an original labelled compatibility, the
swapped one would give `X = λ y = λ x` on the rim box, hence `λ = 0`. -/
theorem isEmpty_labelled_swap_GGFF {n : ℕ} {E : BoundaryTori W n} {Pr : FC39PreparedV2 W E}
    {H : EdgeLayer W} {circ : CircleRegion W} {K : RimChartLayer W H circ}
    (L : LabelledCornerCompatibilityV2 Pr H circ K) (h : Fin H.handleCount) :
    IsEmpty (LabelledCornerCompatibilityV2 Pr H (swapAxesRegion circ) K.swap) := by
  refine ⟨fun L' => ?_⟩
  have hbox : ((1 : ℝ), (0 : ℝ)) ∈ rimBox 2 := by
    refine ⟨?_, ?_⟩ <;> norm_num [abs_lt]
  have hp : ((1 : Circle), ((1 : ℝ), (0 : ℝ))) ∈ (K.rimChart h false).source :=
    (K.rim_source h false).2 hbox
  have hp' : ((1 : Circle), ((0 : ℝ), (1 : ℝ))) ∈ (K.swap.rimChart h false).source :=
    (K.swap.rim_source h false).2 (swap_mem_rimBox_iff.1 hbox)
  obtain ⟨hx, h1⟩ := L.height_eq h false _ hp
  obtain ⟨hx', h2⟩ := L'.height_eq h false _ hp'
  have hscale := circ.cornerScale_pos (K.handleCorner h false)
  change Pr.rows.edge.height ⟨K.rimChart h false ((1 : Circle), ((1 : ℝ), (0 : ℝ))), hx'⟩ -
      Pr.rows.edge.level = circ.cornerScale (K.handleCorner h false) * 0 at h2
  rw [h1] at h2
  simp only [mul_one, mul_zero] at h2
  exact hscale.ne' h2

/-- **Regression test C over V2.** -/
theorem regressionC_GGFF {n : ℕ} {E : BoundaryTori W n} {Pr : FC39PreparedV2 W E}
    {H : EdgeLayer W} {circ : CircleRegion W} (K : RimChartLayer W H circ)
    (L : LabelledCornerCompatibilityV2 Pr H circ K) (h : Fin H.handleCount) (b : Bool)
    (V₀ : Set W.Carrier) (θ : Circle)
    (hv : ∀ {p}, p ∈ (K.rimChart h b).source → (K.rimChart h b p ∈ V₀ ↔ p.2.2 ≤ 0)) :
    (DryCircleLink Pr.rows.edge Pr.rows.circle circ →
        DryCircleLink Pr.rows.edge Pr.rows.circle (swapAxesRegion circ)) ∧
      Nonempty (RimChartLayer W H (swapAxesRegion circ)) ∧
      (¬ ∀ {p}, p ∈ (K.swap.rimChart h b).source → (K.swap.rimChart h b p ∈ V₀ ↔ p.2.2 ≤ 0)) ∧
      IsEmpty (LabelledCornerCompatibilityV2 Pr H (swapAxesRegion circ) K.swap) :=
  ⟨DryCircleLink.swapAxes, ⟨K.swap⟩, not_rimVertex_swap K h b V₀ θ hv,
    isEmpty_labelled_swap_GGFF L h⟩

/-- **The labelled compatibility V2 projects to the dry `CircleLink`.** -/
theorem LabelledCornerCompatibilityV2.dryCircleLink {n : ℕ} {E : BoundaryTori W n}
    {Pr : FC39PreparedV2 W E} {H : EdgeLayer W} {circ : CircleRegion W}
    {K : RimChartLayer W H circ} (L : LabelledCornerCompatibilityV2 Pr H circ K) :
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

/-- The dry link of the swapped data follows from the labelled compatibility V2 of the original. -/
theorem LabelledCornerCompatibilityV2.dryCircleLink_swap {n : ℕ} {E : BoundaryTori W n}
    {Pr : FC39PreparedV2 W E} {H : EdgeLayer W} {circ : CircleRegion W}
    {K : RimChartLayer W H circ} (L : LabelledCornerCompatibilityV2 Pr H circ K) :
    DryCircleLink Pr.rows.edge Pr.rows.circle (swapAxesRegion circ) :=
  L.dryCircleLink.swapAxes

/-- **Regression test C with the dry links derived, over V2.** -/
theorem regressionC_projected_GGFF {n : ℕ} {E : BoundaryTori W n} {Pr : FC39PreparedV2 W E}
    {H : EdgeLayer W} {circ : CircleRegion W} (K : RimChartLayer W H circ)
    (L : LabelledCornerCompatibilityV2 Pr H circ K) (h : Fin H.handleCount) (b : Bool)
    (V₀ : Set W.Carrier) (θ : Circle)
    (hv : ∀ {p}, p ∈ (K.rimChart h b).source → (K.rimChart h b p ∈ V₀ ↔ p.2.2 ≤ 0)) :
    DryCircleLink Pr.rows.edge Pr.rows.circle circ ∧
      DryCircleLink Pr.rows.edge Pr.rows.circle (swapAxesRegion circ) ∧
      Nonempty (RimChartLayer W H (swapAxesRegion circ)) ∧
      (¬ ∀ {p}, p ∈ (K.swap.rimChart h b).source → (K.swap.rimChart h b p ∈ V₀ ↔ p.2.2 ≤ 0)) ∧
      IsEmpty (LabelledCornerCompatibilityV2 Pr H (swapAxesRegion circ) K.swap) := by
  obtain ⟨h1, h2, h3, h4⟩ := regressionC_GGFF K L h b V₀ θ hv
  exact ⟨L.dryCircleLink, h1 L.dryCircleLink, h2, h3, h4⟩

end GC.GraphManifold.Assembly.FC39P0
