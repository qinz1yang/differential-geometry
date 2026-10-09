import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TerminalSphericalRegion
import Mathlib.Topology.Order.Compact

set_option autoImplicit false
noncomputable section
open Set Manifold
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff Topology
namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab

universe u
variable {P : OrientedThreeStage.{u}} {a s : ℝ} {G : P.IncomingSlab a s}

theorem TerminalLimitMetric.exists_connected_compact_neighborhood_scalar_sublevel_component_with_bound
    (L : G.TerminalLimitMetric) {A B : ℝ}
    (y : G.terminalRegularOpen)
    (hyA : metricScalarAt L.metric y ≤ A) :
    ∃ (U : Set G.terminalRegularOpen) (A' : ℝ),
      IsOpen U ∧ IsConnected U ∧ IsCompact (closure U) ∧
      closure U ⊆ {x : G.terminalRegularOpen | ConnectedComponents.mk x = ConnectedComponents.mk y} ∧
      {x : G.terminalRegularOpen |
        ConnectedComponents.mk x = ConnectedComponents.mk y ∧ metricScalarAt L.metric x ≤ A} ⊆ U ∧
      A < A' ∧ B < A' ∧
      ∀ x ∈ closure U, metricScalarAt L.metric x ≤ A' := by
  obtain ⟨U, hUopen, hUconn, hUcompact, hUcomponent, hUlow, _⟩ :=
    L.exists_connected_compact_neighborhood_scalar_sublevel_component
      A (ConnectedComponents.mk y) ⟨y, rfl, hyA⟩
  obtain ⟨x₀, hx₀, hmax⟩ := hUcompact.exists_isMaxOn
    ⟨y, subset_closure (hUlow ⟨rfl, hyA⟩)⟩
    ((metricScalar_smooth L.metric).continuous.continuousOn)
  let A' := max (A + 1) (max (B + 1) (metricScalarAt L.metric x₀ + 1))
  have hAA' : A < A' := by
    dsimp [A']
    exact lt_of_lt_of_le (by linarith) (le_max_left _ _)
  have hBA' : B < A' := by
    dsimp [A']
    exact lt_of_lt_of_le (by linarith) (le_trans (le_max_left _ _) (le_max_right _ _))
  refine ⟨U, A', hUopen, hUconn, hUcompact, hUcomponent, hUlow, hAA', hBA', ?_⟩
  intro x hx
  exact (hmax hx).trans (by
    dsimp [A']
    exact (le_add_of_nonneg_right (by norm_num)).trans
      ((le_max_right _ _).trans (le_max_right _ _)))


theorem TerminalLimitMetric.exists_connected_compact_region_covering_scalar_sublevel_of_compact_connected_neighborhood
    (L : G.TerminalLimitMetric) :
    ∃ η : ℝ, 0 < η ∧ ∀ δ : ℝ, 0 < δ → δ ≤ η →
      ∃ C2 q : ℝ, 1 ≤ C2 ∧ 0 < q ∧
        ∀ (A : ℝ) (y : G.terminalRegularOpen), 0 < A →
          metricScalarAt L.metric y ≤ A → ¬ IsCompact (connectedComponent y) →
          ∃ U : Set G.terminalRegularOpen, ∃ A' : ℝ, ∃ C : Set G.terminalRegularOpen,
            IsOpen U ∧ IsConnected U ∧ IsCompact (closure U) ∧
            closure U ⊆ {x | ConnectedComponents.mk x = ConnectedComponents.mk y} ∧
            {x | ConnectedComponents.mk x = ConnectedComponents.mk y ∧
              metricScalarAt L.metric x ≤ A} ⊆ U ∧
            A < A' ∧ q < 4 * C2 * A' ∧
            IsCompact C ∧ IsConnected C ∧ IsConnected (interior C) ∧
            closure (interior C) = C ∧ y ∈ interior C ∧
            {x | x ∈ connectedComponent y ∧ metricScalarAt L.metric x ≤ A} ⊆ interior C ∧
            closure U ⊆ interior C ∧ C ⊆ connectedComponent y ∧
            (∀ x ∈ C, metricScalarAt L.metric x ≤ 8 * C2^2 * A') := by
  obtain ⟨η, hη, hregion⟩ := L.exists_connected_spherical_region
  refine ⟨η, hη, ?_⟩
  intro δ hδ hδη
  obtain ⟨C2, q, hC2, hq, hregion⟩ := hregion δ hδ hδη
  refine ⟨C2, q, hC2, hq, ?_⟩
  intro A y hA hyA hnoncompact
  obtain ⟨U, A', hUopen, hUconn, hUcompact, hUcomponent, hUlow, hAA', hApos⟩ :=
    L.exists_connected_compact_neighborhood_scalar_sublevel_component_with_bound
      (B := q + 1) y hyA
  have hA'pos : 0 < A' := lt_trans hA hAA'
  have hqA' : q < 4 * C2 * A' := by
    have hC2pos : 0 < C2 := lt_of_lt_of_le zero_lt_one hC2
    nlinarith
  obtain ⟨ι, v, neck, level, b, C, hb, hcompact, hconn, hinteriorconn,
    hregular, hyint, hcomponent, hscalar, hdisjoint, hfrontier,
    hfrontierscalar, hatlas, hnecks⟩ :=
      hregion A' y hA'pos hqA' (hyA.trans hAA'.le) hnoncompact
  have hUscalar : ∀ x ∈ U, metricScalarAt L.metric x ≤ A' := by
    intro x hx
    exact hApos.2 x (subset_closure hx)
  have hyU : y ∈ U := hUlow ⟨rfl, hyA⟩
  have hyC : y ∈ C := interior_subset hyint
  have hdisj : Disjoint U (frontier C) := by
    apply disjoint_left.mpr
    intro x hxU hxfront
    nlinarith [hUscalar x hxU, hfrontierscalar x hxfront]
  have hUint : U ⊆ interior C :=
    DifferentialGeometry.Topology.isPreconnected_subset_interior_of_meets_of_disjoint_frontier
      hUconn.isPreconnected ⟨y, hyU, hyC⟩ hdisj
  have hCsub : closure U ⊆ C := by
    rw [← hregular]
    exact closure_mono hUint
  have hUclosureInterior : closure U ⊆ interior C := by
    intro x hx
    by_contra hxint
    have hxfront : x ∈ frontier C :=
      ⟨subset_closure (hCsub hx), hxint⟩
    nlinarith [hApos.2 x hx, hfrontierscalar x hxfront]
  have hlowA : {x : G.terminalRegularOpen |
      x ∈ connectedComponent y ∧ metricScalarAt L.metric x ≤ A} ⊆ interior C := by
    intro x hx
    have hxU := hUlow ⟨ConnectedComponents.coe_eq_coe'.mpr hx.1, hx.2⟩
    exact hUint hxU
  exact ⟨U, A', C, hUopen, hUconn, hUcompact, hUcomponent, hUlow, hAA', hqA',
    hcompact, hconn, hinteriorconn, hregular, hyint, hlowA, hUclosureInterior,
    hcomponent, hscalar⟩

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab
