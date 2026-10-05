import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39GRimRimChartBinding

/-!
# FC39 GROUP G, RIMBOX route B (binding G6): consumers of the per-end rim charts

Lane FC39-G-RIMBOXc.

* `FC39PreparedV2.exists_handleRimChartFamily_GRIM` — the handles of ALL interval components with,
  at every end, the corner chart and the rim chart (`choose` over `exists_handleRimCharts_GRIM`; the
  form G8 uses);
* `FC39PreparedV2.rimTargets_disjoint_GRIM` — rim charts at distinct endpoints whose target closures lie
  in the safe tubes have disjoint targets (`corner_closure_disjoint`; `RimChartLayer.rim_disjoint`).
-/

set_option autoImplicit false

noncomputable section

open Set Function
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert GC.GraphManifold
open Manifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold.Assembly.FC39P0

local instance diskChartsRCBA_GRIM : ChartedSpace (EuclideanHalfSpace 2) (ClosedCell 2) :=
  DifferentialGeometry.Topology.Handle.closedCellChartedSpaceSucc 1

variable {W : CompactCarrier.{u}} {n : ℕ} {E : BoundaryTori W n}

/-- **The handles and the per-end corner / rim charts of all interval components.** -/
theorem FC39PreparedV2.exists_handleRimChartFamily_GRIM (Pr : FC39PreparedV2 W E)
    (safe : ProducerSafeNeighbourhoods Pr.rows) :
    ∃ (H : Fin Pr.rows.edgeModels.intervalCount → EdgeHandle W)
      (lam : Fin Pr.rows.edgeModels.intervalCount → Bool → ℝ)
      (κ : Fin Pr.rows.edgeModels.intervalCount → Bool →
        PartialDiffeomorph 𝓘(ℝ, ℝ × ℝ) (𝓡 2) (ℝ × ℝ) Pr.rows.circle.Base ∞)
      (χ : Fin Pr.rows.edgeModels.intervalCount → Bool →
        PartialDiffeomorph ((𝓡 1).prod 𝓘(ℝ, ℝ × ℝ)) W.model (Circle × (ℝ × ℝ)) W.Carrier ∞),
      (∀ i,
        range (H i).map =
          Pr.rows.edge.wholeComponent (Pr.rows.edgeModels.componentEquiv (.inl i)) ∧
        (∀ w t, ∃ hx : (H i).map (w, t) ∈ Pr.rows.edge.source,
          Pr.rows.edge.proj ⟨(H i).map (w, t), hx⟩ = Pr.rows.edgeModels.intervalBase i t) ∧
        (∀ t, range (fun w => (H i).map (w, t)) =
          Pr.rows.edge.disk (Pr.rows.edgeModels.intervalBase i t)) ∧
        (∀ t, (fun w => (H i).map (w, t)) '' diskRim =
          Pr.rows.edge.rim (Pr.rows.edgeModels.intervalBase i t))) ∧
      ∀ i b,
        0 < (lam i b) ∧
        (κ i b).source = rimBox 3 ∧
        (∀ v ∈ rimBox 3, Pr.rows.labelledTubes.chart (Pr.rows.edgeModels.endpointEquiv (i, b))
          ((κ i b) v) = (lam i b) • v) ∧
        (κ i b) (0, 0) = Pr.rows.junctions.rimBase (Pr.rows.edgeModels.endpointEquiv (i, b)).1 ∧
        (κ i b).target ⊆ (safe.cornerBase (Pr.rows.edgeModels.endpointEquiv (i, b)) : Set _) ∩
          (Pr.globalFaces.base : Set Pr.rows.circle.Base) ∧
        (∀ v ∈ rimBox 3,
          Pr.globalFaces.fn (Pr.globalFaces.actualFace.symm
              (.vertical (Pr.rows.edgeModels.endpointEquiv (i, b)).component)) ((κ i b) v) =
            -((lam i b) * v.1) ∧
          Pr.globalFaces.fn (Pr.globalFaces.actualFace.symm (.horizontal
              (Pr.rows.junctions.horizontal (Pr.rows.edgeModels.endpointEquiv (i, b))))) ((κ i b) v) =
            -((lam i b) * v.2)) ∧
        (∀ f v, f ≠ Pr.globalFaces.actualFace.symm
              (.vertical (Pr.rows.edgeModels.endpointEquiv (i, b)).component) →
          f ≠ Pr.globalFaces.actualFace.symm (.horizontal
              (Pr.rows.junctions.horizontal (Pr.rows.edgeModels.endpointEquiv (i, b)))) →
          v ∈ rimBox 3 → Pr.globalFaces.fn f ((κ i b) v) < 0) ∧
        (∀ p, p ∈ (χ i b).source ↔ p.2 ∈ rimBox 2) ∧
        (∀ p ∈ (χ i b).source, ∃ hx : (χ i b) p ∈ Pr.rows.circle.domain,
          Pr.rows.circle.proj ⟨(χ i b) p, hx⟩ = (κ i b) p.2) ∧
        (χ i b).target = Pr.rows.circle.tube ((κ i b) '' rimBox 2) ∧
        (χ i b) '' {p | p.2 = (0, 0)} = (fun x : ClosedCell 2 => (H i).map (x, iccEnd b)) '' diskRim ∧
        RimProductAt (χ i b) (H i) b ∧
        closure (χ i b).target ⊆ safe.corner (Pr.rows.edgeModels.endpointEquiv (i, b)) ∧
        (∀ p ∈ (χ i b).source, ∃ hx : (χ i b) p ∈ Pr.rows.edge.source,
          Pr.rows.edge.height ⟨(χ i b) p, hx⟩ - Pr.rows.edge.level = (lam i b) * p.2.1) ∧
        (∀ p ∈ (χ i b).source, Pr.rows.slim.residualFn
          (Pr.rows.junctions.horizontal (Pr.rows.edgeModels.endpointEquiv (i, b))) ((χ i b) p) =
            (lam i b) * p.2.2) ∧
        (χ i b).target ⊆ Pr.rows.labelledTubes.tube (Pr.rows.edgeModels.endpointEquiv (i, b)) := by
  choose H hH using Pr.exists_handleRimCharts_GRIM safe
  have h2 := fun i b => (hH i).2.2.2.2 b
  choose lam κ χ hlkc using h2
  exact ⟨H, lam, κ, χ, fun i => ⟨(hH i).1, (hH i).2.1, (hH i).2.2.1, (hH i).2.2.2.1⟩, hlkc⟩

/-- **Rim charts at distinct endpoints have disjoint targets** when their target closures lie in
the safe tubes of their endpoints. -/
theorem FC39PreparedV2.rimTargets_disjoint_GRIM (Pr : FC39PreparedV2 W E)
    (safe : ProducerSafeNeighbourhoods Pr.rows) {e e' : Pr.rows.edge.EdgeEnd} (hne : e ≠ e')
    {χ χ' : PartialDiffeomorph ((𝓡 1).prod 𝓘(ℝ, ℝ × ℝ)) W.model (Circle × (ℝ × ℝ)) W.Carrier ∞}
    (h : closure χ.target ⊆ safe.corner e) (h' : closure χ'.target ⊆ safe.corner e') :
    Disjoint χ.target χ'.target :=
  (safe.corner_closure_disjoint hne).mono (subset_closure.trans (h.trans subset_closure))
    (subset_closure.trans (h'.trans subset_closure))

end GC.GraphManifold.Assembly.FC39P0
