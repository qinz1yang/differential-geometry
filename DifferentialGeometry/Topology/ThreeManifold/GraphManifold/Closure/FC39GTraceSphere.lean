import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39GTraceAtlas
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39GSafeSphere

/-!
# FC39 GROUP G, lane FC39-G-TRACE: the S³ regression of the labelled trace atlas

The general trace pack (`FC39GTraceTop.lean`, `FC39GTraceRows.lean`, `FC39GTraceAtlas.lean`) applied
to the S³ rows `sphereRowsW sphereJunctions` (the wide rows of the non-vacuous strong certificate).
Non-vacuity: four labels, four registered corners each carrying exactly two labels; the zero sets of
the S³ global face functions inside `C₁` are traces, hence lie in `∂C₁`.
-/

set_option autoImplicit false

noncomputable section

open Set Function
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert GC.GraphManifold
open Manifold
open scoped Manifold ContDiff Topology

namespace GC.GraphManifold.Assembly.FC39P0

/-- F1 on the S³ rows: finitely many labels. -/
theorem sphere_finite_circleFace_GTR : Finite (sphereRowsW sphereJunctions).CircleFace :=
  FC39RowsV2.finite_circleFace_GTR _

/-- The S³ rows have exactly four labels (the general finiteness is not vacuous). -/
theorem sphere_circleFace_card_GTR : Nat.card (sphereRowsW sphereJunctions).CircleFace = 4 := by
  rw [← Nat.card_congr (sphereGlobalFacesW sphereJunctions).actualFace]
  change Nat.card (Fin 4) = 4
  simp

/-- F1 on the S³ rows: every trace is compact. -/
theorem sphere_isCompact_baseTrace_GTR (f : (sphereRowsW sphereJunctions).CircleFace) :
    IsCompact ((sphereRowsW sphereJunctions).baseTrace f) :=
  FC39RowsV2.isCompact_baseTrace_GTR _ f

/-- F2 on the S³ rows: `∂C₁ = ⋃ f, B f`. -/
theorem sphere_frontier_eq_iUnion_GTR :
    frontier (sphereRowsW sphereJunctions).circle.cbase =
      ⋃ f, (sphereRowsW sphereJunctions).baseTrace f :=
  FC39RowsV2.frontier_cbase_eq_iUnion_baseTrace_GTR _

/-- **Non-vacuity of the corner clauses**: the four S³ corners each carry exactly two labels. -/
theorem sphere_corner_labels_GTR (e : (sphereRowsW sphereJunctions).edge.EdgeEnd) :
    {f : (sphereRowsW sphereJunctions).CircleFace |
      (sphereRowsW sphereJunctions).junctions.rimBase e.1 ∈
        (sphereRowsW sphereJunctions).baseTrace f}.ncard = 2 :=
  FC39RowsV2.ncard_labels_rimBase_GTR _ e

/-- The S³ rows have four registered corners. -/
theorem sphere_edgeEnd_card_GTR : Nat.card (sphereRowsW sphereJunctions).edge.EdgeEnd = 4 :=
  sphere_edgeEnd_card_GSAFE

/-- Depth at most two on the S³ base. -/
theorem sphere_ncard_labels_le_two_GTR (c : (sphereRowsW sphereJunctions).circle.Base) :
    {f : (sphereRowsW sphereJunctions).CircleFace |
      c ∈ (sphereRowsW sphereJunctions).baseTrace f}.ncard ≤ 2 :=
  FC39RowsV2.ncard_labels_le_two_GTR _ c

/-- Saturation (A2) on the S³ rows. -/
theorem sphere_residualSet_inter_region_GTR (G : (sphereRowsW sphereJunctions).slim.ResidualFace) :
    (sphereRowsW sphereJunctions).slim.residualSet G ∩ (sphereRowsW sphereJunctions).circle.region =
      (sphereRowsW sphereJunctions).circle.tube
        ((sphereRowsW sphereJunctions).baseTrace (.horizontal G)) :=
  FC39RowsV2.residualSet_inter_region_eq_tube_GTR _ G

/-- The corner atlas at every S³ corner. -/
theorem sphere_corner_atlas_GTR (e : (sphereRowsW sphereJunctions).edge.EdgeEnd) :
    ∃ V : TopologicalSpace.Opens (sphereRowsW sphereJunctions).circle.Base,
      (sphereRowsW sphereJunctions).junctions.rimBase e.1 ∈ V ∧
      (V : Set (sphereRowsW sphereJunctions).circle.Base) ⊆
        (sphereRowsW sphereJunctions).labelledTubes.base e ∧
      (∀ c ∈ V, c ∈ (sphereRowsW sphereJunctions).circle.cbase ↔
        0 ≤ ((sphereRowsW sphereJunctions).labelledTubes.chart e c).1 ∧
          0 ≤ ((sphereRowsW sphereJunctions).labelledTubes.chart e c).2) ∧
      (∀ c ∈ V, c ∈ (sphereRowsW sphereJunctions).baseTrace (.vertical e.component) ↔
        c ∈ (sphereRowsW sphereJunctions).circle.cbase ∧
          ((sphereRowsW sphereJunctions).labelledTubes.chart e c).1 = 0) ∧
      (∀ c ∈ V, c ∈ (sphereRowsW sphereJunctions).baseTrace
          (.horizontal ((sphereRowsW sphereJunctions).junctions.horizontal e)) ↔
        c ∈ (sphereRowsW sphereJunctions).circle.cbase ∧
          ((sphereRowsW sphereJunctions).labelledTubes.chart e c).2 = 0) ∧
      ∀ f : (sphereRowsW sphereJunctions).CircleFace, f ≠ .vertical e.component →
        f ≠ .horizontal ((sphereRowsW sphereJunctions).junctions.horizontal e) →
        Disjoint ((sphereRowsW sphereJunctions).baseTrace f)
          (V : Set (sphereRowsW sphereJunctions).circle.Base) :=
  FC39RowsV2.exists_corner_atlas_GTR _ e

/-- **Regression against the S³ global face functions**: the zero set inside `C₁` of each S³
global face function is a trace (`face_eq`), hence lies in `∂C₁` (general F2). -/
theorem sphere_globalFaces_zero_subset_frontier_GTR (f : (sphereGlobalFacesW sphereJunctions).Face) :
    {c | c ∈ (sphereRowsW sphereJunctions).circle.cbase ∧
        (sphereGlobalFacesW sphereJunctions).fn f c = 0} ⊆
      frontier (sphereRowsW sphereJunctions).circle.cbase := by
  rw [(sphereGlobalFacesW sphereJunctions).face_eq f]
  exact FC39RowsV2.baseTrace_subset_frontier_GTR _ _

/-- **Regression of exhaustiveness on the S³ global face functions**: at a point of `∂C₁` the
global face functions vanishing there are exactly those of the labels through the point. -/
theorem sphere_globalFaces_zero_iff_GTR {c : (sphereRowsW sphereJunctions).circle.Base}
    (hc : c ∈ (sphereRowsW sphereJunctions).circle.cbase)
    {f : (sphereGlobalFacesW sphereJunctions).Face} :
    (sphereGlobalFacesW sphereJunctions).fn f c = 0 ↔
      c ∈ (sphereRowsW sphereJunctions).baseTrace
        ((sphereGlobalFacesW sphereJunctions).actualFace f) := by
  rw [← (sphereGlobalFacesW sphereJunctions).face_eq f]
  exact ⟨fun h => ⟨hc, h⟩, fun h => h.2⟩

/-- The labelled trace atlas at every point of the S³ frontier. -/
theorem sphere_labelled_atlas_GTR {c : (sphereRowsW sphereJunctions).circle.Base}
    (hc : c ∈ frontier (sphereRowsW sphereJunctions).circle.cbase) :
    ∃ U : TopologicalSpace.Opens (sphereRowsW sphereJunctions).circle.Base, c ∈ U ∧
      ∃ (L : Finset (sphereRowsW sphereJunctions).CircleFace)
        (φ : (sphereRowsW sphereJunctions).CircleFace →
          (sphereRowsW sphereJunctions).circle.Base → ℝ),
        (∀ f, f ∈ L ↔ c ∈ (sphereRowsW sphereJunctions).baseTrace f) ∧ 1 ≤ L.card ∧
        L.card ≤ 2 ∧
        (∀ f ∈ L, ContMDiffOn (𝓡 2) 𝓘(ℝ, ℝ) ∞ (φ f) U ∧ φ f c = 0 ∧
          (sphereRowsW sphereJunctions).baseTrace f ∩ U =
            {c' | c' ∈ U ∧ c' ∈ (sphereRowsW sphereJunctions).circle.cbase ∧ φ f c' = 0}) ∧
        (Surjective fun w : TangentSpace (𝓡 2) c =>
          fun f : L => mfderiv (𝓡 2) 𝓘(ℝ, ℝ) (φ f) c w) ∧
        (sphereRowsW sphereJunctions).circle.cbase ∩ U =
          {c' | c' ∈ U ∧ ∀ f ∈ L, φ f c' ≤ 0} ∧
        ∀ f, f ∉ L → Disjoint ((sphereRowsW sphereJunctions).baseTrace f)
          (U : Set (sphereRowsW sphereJunctions).circle.Base) :=
  FC39RowsV2.labelled_baseTrace_atlas_GTR _ hc

end GC.GraphManifold.Assembly.FC39P0
