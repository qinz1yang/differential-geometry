import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39GRimRimChartBindingApplications
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39GRimCircleRegionApplications
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39GRimRoundApplications
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39GRimEdgeCircleApplications

/-!
# FC39 GROUP G, RIMBOX (G8): the joint adapted edge–rim data V2

Lane FC39-G-RIMBOXc; frozen target D58-1 / D58-4 (`Closure/FC39P0AdaptedV2.lean`):
`exists_adaptedEdgeRimDataV2_GRIM (Pr) (safe) : Nonempty (AdaptedEdgeRimDataV2 Pr safe)`.

One-shot assembly (sheet §1 G8, D62-1):
* handles, corner charts and rim charts of every interval end: G6
  (`FC39PreparedV2.exists_handleRimChartFamily_GRIM`, the new flow handles with ONE flow per
  component, the scale frozen last);
* edge layer and its component link: the new handles + the edge-circle pieces of lane
  FC39-RIMBOX-ROUND (`EdgeComponentModels.edgeComponentsLink_GRND`, index bijections = id);
* circle region, restriction link, global face link, corner ↔ endpoint equivalence, rounding: G8a
  of lane FC39-RIMBOX-ROUND (`FC39PreparedV2.exists_circleRegion_of_cornerCharts_GRND`) applied to
  the per-endpoint corner charts of G6;
* rim chart layer: `handleCorner h b = endOfCorner⁻¹ (endpointEquiv (h, b))`, rims = the G6 rim
  charts (`rim_proj` / `target_full` via `rim_proj_of_rowProj_GRND` / `target_full_of_tube_GRND`;
  disjoint targets via `rimTargets_disjoint_GRIM`);
* labelled compatibility: labels from G8a, heights / horizontal equations from G6;
* `components_eq`, `circle_eq` by `rfl`; `product`, `rim_closure_in_safe` from G6;
  `rounding_in_safe` by `LabelledCornerCompatibilityV2.rounding_in_safe_GRND`.
-/

set_option autoImplicit false

noncomputable section

open Set Function
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert GC.GraphManifold
open Manifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold.Assembly.FC39P0

variable {W : CompactCarrier.{u}} {n : ℕ} {E : BoundaryTori W n}

/-- The base component of the endpoint `(i, b)` is the interval component `i`. -/
theorem FC39RowsV2.endpoint_component_GRIM (Rw : FC39RowsV2 W E)
    (i : Fin Rw.edgeModels.intervalCount) (b : Bool) :
    (Rw.edgeModels.endpointEquiv (i, b)).component = Rw.edgeModels.componentEquiv (.inl i) := by
  refine ActualComponent.eq_of_mem (z := (Rw.edgeModels.endpointEquiv (i, b)).1)
    (mem_connectedComponentIn (Rw.edge.frontier_cbase_subset (Rw.edgeModels.endpointEquiv (i, b)).2))
    ?_
  rw [← Rw.edgeModels.intervalBase_range i, Rw.edgeModels.endpointEquiv_apply]
  exact mem_range_self _

/-- **G8: the joint adapted edge–rim data over the prepared rows V2 exist** (the frozen RIMBOX
target, D58-1 / D58-4; the remaining explicit argument of `strongCertificate_of_adapted_GFIN`). -/
theorem exists_adaptedEdgeRimDataV2_GRIM (Pr : FC39PreparedV2 W E)
    (safe : ProducerSafeNeighbourhoods Pr.rows) : Nonempty (AdaptedEdgeRimDataV2 Pr safe) := by
  classical
  obtain ⟨H, lam, κ, χ, hH, hc⟩ := Pr.exists_handleRimChartFamily_GRIM safe
  -- per endpoint
  let ib : Pr.rows.edge.EdgeEnd → Fin Pr.rows.edgeModels.intervalCount × Bool := fun e => Pr.rows.edgeModels.endpointEquiv.symm e
  let lamE : Pr.rows.edge.EdgeEnd → ℝ := fun e => lam (ib e).1 (ib e).2
  let κE : Pr.rows.edge.EdgeEnd →
      PartialDiffeomorph 𝓘(ℝ, ℝ × ℝ) (𝓡 2) (ℝ × ℝ) Pr.rows.circle.Base ∞ :=
    fun e => κ (ib e).1 (ib e).2
  have hibe : ∀ e, Pr.rows.edgeModels.endpointEquiv ((ib e).1, (ib e).2) = e := fun e =>
    Pr.rows.edgeModels.endpointEquiv.apply_symm_apply e
  have hκE : ∀ i b, κE (Pr.rows.edgeModels.endpointEquiv (i, b)) = κ i b := by
    intro i b
    simp only [κE, ib, Equiv.symm_apply_apply]
  have hlamE : ∀ i b, lamE (Pr.rows.edgeModels.endpointEquiv (i, b)) = lam i b := by
    intro i b
    simp only [lamE, ib, Equiv.symm_apply_apply]
  have hcE : ∀ e, 0 < lamE e ∧ (κE e).source = rimBox 3 ∧
      κE e (0, 0) = Pr.rows.junctions.rimBase e.1 ∧
      (κE e).target ⊆ (safe.cornerBase e : Set _) ∩
        (Pr.globalFaces.base : Set Pr.rows.circle.Base) ∧
      (∀ v ∈ rimBox 3,
        Pr.globalFaces.fn (Pr.globalFaces.actualFace.symm (.vertical e.component)) (κE e v) =
          -(lamE e * v.1) ∧
        Pr.globalFaces.fn (Pr.globalFaces.actualFace.symm
          (.horizontal (Pr.rows.junctions.horizontal e))) (κE e v) = -(lamE e * v.2)) ∧
      (∀ f v, f ≠ Pr.globalFaces.actualFace.symm (.vertical e.component) →
        f ≠ Pr.globalFaces.actualFace.symm (.horizontal (Pr.rows.junctions.horizontal e)) →
        v ∈ rimBox 3 → Pr.globalFaces.fn f (κE e v) < 0) := by
    intro e
    obtain ⟨h1, h2, -, h4, h5, h6, h7, -⟩ := hc (ib e).1 (ib e).2
    rw [hibe e] at h4 h5 h6 h7
    exact ⟨h1, h2, h4, h5, h6, h7⟩
  obtain ⟨circ, L, G, eoc, hscale, hchartι, htargetι, hfirst, hsecond, hcenter⟩ :=
    Pr.exists_circleRegion_of_cornerCharts_GRND safe lamE κE (fun e => (hcE e).1)
      (fun e => (hcE e).2.1) (fun e => (hcE e).2.2.1) (fun e => (hcE e).2.2.2.1)
      (fun e v hv => ((hcE e).2.2.2.2.1 v hv).1) (fun e v hv => ((hcE e).2.2.2.2.1 v hv).2)
      (fun e => (hcE e).2.2.2.2.2)
  -- the edge layer and its component link
  let edges : EdgeLayer W := Pr.rows.edgeModels.edgeLayer_GRND H
  let comps : EdgeComponentsLink Pr.rows.edge Pr.rows.edgeModels edges :=
    Pr.rows.edgeModels.edgeComponentsLink_GRND H (fun i => (hH i).1) (fun i => (hH i).2.1)
      (fun i => (hH i).2.2.1) (fun i => (hH i).2.2.2)
  -- the corner of an end
  let hcorner : Fin Pr.rows.edgeModels.intervalCount → Bool → Fin circ.cornerCount :=
    fun h b => eoc.symm (Pr.rows.edgeModels.endpointEquiv (h, b))
  have heoc : ∀ (h : Fin Pr.rows.edgeModels.intervalCount) (b : Bool),
      eoc (hcorner h b) = Pr.rows.edgeModels.endpointEquiv (h, b) := fun h b =>
    eoc.apply_symm_apply _
  have hchart : ∀ (h : Fin Pr.rows.edgeModels.intervalCount) (b : Bool) v, v ∈ rimBox 2 →
      L.ι (circ.cornerChart (hcorner h b) v) = κ h b v := by
    intro h b v hv
    rw [hchartι _ v hv, heoc, hκE]
  have htgt : ∀ (h : Fin Pr.rows.edgeModels.intervalCount) (b : Bool) c,
      c ∈ (circ.cornerChart (hcorner h b)).target ↔ L.ι c ∈ κ h b '' rimBox 2 := by
    intro h b c
    rw [htargetι, heoc, hκE]
  have hscaleHB : ∀ (h : Fin Pr.rows.edgeModels.intervalCount) (b : Bool),
      circ.cornerScale (hcorner h b) = lam h b := by
    intro h b
    rw [hscale, heoc, hlamE]
  have hfirstHB : ∀ (h : Fin Pr.rows.edgeModels.intervalCount) (b : Bool),
      G.faceOfDefining (circ.cornerFirst (hcorner h b)) =
        .vertical (Pr.rows.edgeModels.componentEquiv (.inl h)) := by
    intro h b
    rw [hfirst, heoc, Pr.rows.endpoint_component_GRIM]
  have hsecondHB : ∀ (h : Fin Pr.rows.edgeModels.intervalCount) (b : Bool),
      G.faceOfDefining (circ.cornerSecond (hcorner h b)) =
        .horizontal (Pr.rows.junctions.horizontal (Pr.rows.edgeModels.endpointEquiv (h, b))) := by
    intro h b
    rw [hsecond, heoc]
  -- the rim chart layer
  let rims : RimChartLayer W edges circ :=
    { handleCorner := hcorner
      handleCorner_bijective := by
        have hb : Bijective fun hb : Fin Pr.rows.edgeModels.intervalCount × Bool =>
            eoc.symm (Pr.rows.edgeModels.endpointEquiv hb) :=
          (Pr.rows.edgeModels.endpointEquiv.trans eoc.symm).bijective
        exact hb
      rimChart := χ
      rim_source := fun h b {p} => ((hc h b).2.2.2.2.2.2.2.1 p)
      rim_proj := fun h b => L.rim_proj_of_rowProj_GRND (hchart h b)
        (fun p => (hc h b).2.2.2.2.2.2.2.1 p) (hc h b).2.2.2.2.2.2.2.2.1
      rim_label := fun h b => (hc h b).2.2.2.2.2.2.2.2.2.2.1
      rim_disjoint := by
        intro h b h' b' hne
        refine Pr.rimTargets_disjoint_GRIM safe ?_ (hc h b).2.2.2.2.2.2.2.2.2.2.2.2.1
          (hc h' b').2.2.2.2.2.2.2.2.2.2.2.2.1
        intro heq
        exact hne (Prod.ext_iff.mpr (by
          have := Pr.rows.edgeModels.endpointEquiv.injective heq
          exact ⟨congrArg Prod.fst this, congrArg Prod.snd this⟩)) }
  -- the labelled compatibility
  let lab : LabelledCornerCompatibilityV2 Pr edges circ rims :=
    { edgeLink := comps
      circleLink := L
      globalFaces := G
      endOfCorner := eoc
      corner_center := hcenter
      endpoint_label := fun h b => (heoc h b).symm
      first_label := fun h b => hfirstHB h b
      second_label := fun h b => hsecondHB h b
      height_eq := fun h b p hp => by
        obtain ⟨hx, hh⟩ := (hc h b).2.2.2.2.2.2.2.2.2.2.2.2.2.1 p hp
        exact ⟨hx, hh.trans (congrArg (· * p.2.1) (hscaleHB h b).symm)⟩
      horizontal_eq := fun h b p hp =>
        ((hc h b).2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 p hp).trans
          (congrArg (· * p.2.2) (hscaleHB h b).symm)
      target_full := fun h b => L.target_full_of_tube_GRND (hchart h b) (htgt h b)
        (hc h b).2.2.2.2.2.2.2.2.2.1
      target_in_raw_tube := fun h b => (hc h b).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 }
  have hsafe : ∀ (h : Fin edges.handleCount) (b : Bool),
      closure (rims.rimChart h b).target ⊆ safe.corner (lab.edgeLink.endOfHandle h b) :=
    fun h b => (hc h b).2.2.2.2.2.2.2.2.2.2.2.2.1
  exact ⟨{ edges := edges
           circ := circ
           components := comps
           circle := L
           rims := rims
           labelled := lab
           components_eq := rfl
           circle_eq := rfl
           product := fun h b => (hc h b).2.2.2.2.2.2.2.2.2.2.2.1
           rim_closure_in_safe := hsafe
           rounding_in_safe := lab.rounding_in_safe_GRND hsafe }⟩

end GC.GraphManifold.Assembly.FC39P0
