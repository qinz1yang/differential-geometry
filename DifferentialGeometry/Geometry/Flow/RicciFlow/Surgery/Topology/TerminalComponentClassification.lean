import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.DiscardedCanonicalCoverage
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.CompactCanonicalClassification

noncomputable section
open Set
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Perelman
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open DifferentialGeometry.Topology
open scoped Manifold ContDiff NNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab

universe u
variable {P : OrientedThreeStage.{u}} {a s : ℝ} (G : P.IncomingSlab a s)

attribute [local instance] OrientedThreeStage.component_compact

theorem TerminalLimitMetric.exists_late_component_canonical_neighborhoods_with_cap_neck_charts
    (g : G.TerminalLimitMetric) {eps : ℝ} (heps : 0 < eps) (hsmall : eps < 1 / 11) :
    ∃ C L : ℝ, 1 ≤ C ∧ 0 < L ∧
      ∀ c : ConnectedComponents P.Carrier,
        (∀ x : G.terminalRegularOpen, ConnectedComponents.mk x.val = c →
          L < metricScalarAt g.metric x) →
        ∃ d ∈ Ico a s, ∀ t ∈ Ioo d s,
          ∃ W : ∀ x : P.componentOpen c,
              CanonicalWitness (G.componentTimeShift c) eps C C x (t - a),
            ∀ x, (W x).capTubeHasNeckChart eps := by
  obtain ⟨Phi, hPhi, hpinch⟩ :=
    exists_admissiblePinchingFunction_phiAlmostNonnegative_closedOpen
      G.lt G.flow G.equation (by simp [ThreeSpace])
  obtain ⟨C, Q, hC, hQ, hcanonical⟩ :=
    G.exists_component_canonical_neighborhoods_with_cap_neck_charts heps hsmall
  obtain ⟨epsCan, hepsCan, hambient⟩ := G.exists_all_point_canonical_neighborhoods
  obtain ⟨C1, C2, Q0, _, hC2, hQ0, hW⟩ := hambient epsCan hepsCan le_rfl
  have hbound : ∀ x : P.Carrier, ∀ t ∈ Ioo a s, Q0 < G.flow.scalar t x →
      |derivWithin (fun v => G.flow.scalar v x) (Iic t) t| ≤
        (⟨C2, zero_le_one.trans hC2⟩ : ℝ≥0) * G.flow.scalar t x ^ 2 := by
    intro x t ht hhigh
    exact (hW x t ⟨ht.1.le, ht.2⟩ hhigh.le).some.time_derivative
  refine ⟨C, Q + 1, hC, by linarith, ?_⟩
  intro c hterminal
  obtain ⟨d, hd, hhigh⟩ := g.eventually_scalar_gt_on_closed_set hQ0 hbound hPhi hpinch
    (P.componentOpen_isClosed c) (show Q < Q + 1 from lt_add_one Q) hterminal
  refine ⟨d, hd, ?_⟩
  intro t ht
  choose W hchart using fun x : P.componentOpen c =>
    hcanonical c x t ⟨hd.1.trans ht.1.le, ht.2⟩ (hhigh t ht x.val x.property).le
  exact ⟨W, hchart⟩

theorem TerminalLimitMetric.exists_component_poincareStandard_threshold
    (g : G.TerminalLimitMetric) :
    ∃ L : ℝ, 0 < L ∧ ∀ c : ConnectedComponents P.Carrier,
      (∀ x : G.terminalRegularOpen, ConnectedComponents.mk x.val = c →
        L < metricScalarAt g.metric x) →
      isPoincareStandard (P.toClosedOrientedManifold.component c).Carrier := by
  obtain ⟨eta, heta, hclass⟩ := exists_compact_canonical_poincareStandard_tolerance.{u}
  let eps := min eta (1 / 22)
  have heps : 0 < eps := lt_min heta (by norm_num)
  have hsmall : eps < 1 / 11 := (min_le_right _ _).trans_lt (by norm_num)
  obtain ⟨C, L, hC, hL, hlate⟩ :=
    g.exists_late_component_canonical_neighborhoods_with_cap_neck_charts G heps hsmall
  refine ⟨L, hL, ?_⟩
  intro c hterminal
  obtain ⟨d, hd, hW⟩ := hlate c hterminal
  obtain ⟨t, ht⟩ := exists_between hd.2
  obtain ⟨W, hchart⟩ := hW t ht
  exact hclass eps (min_le_left _ _) (P.toClosedOrientedManifold.component c)
    (G.componentTimeShift c) C C (t - a) W hchart


theorem exists_component_poincareStandard_tolerance_of_canonical_neighborhoods :
    ∃ eta : ℝ, 0 < eta ∧ ∀ eps : ℝ, eps ≤ eta →
      ∀ (P : OrientedThreeStage.{u}) (a s : ℝ) (G : P.IncomingSlab a s)
        (g : G.TerminalLimitMetric) (C1 C2 q R : ℝ),
      0 < q → q < R →
      (∀ x : P.Carrier, ∀ t ∈ Ioo a s, q < G.flow.scalar t x →
        ∃ W : CanonicalWitness G.flow eps C1 C2 x t, W.capTubeHasNeckChart eps) →
      ∀ c : ConnectedComponents P.Carrier,
        (∀ x : G.terminalRegularOpen, ConnectedComponents.mk x.val = c →
          R < metricScalarAt g.metric x) →
        isPoincareStandard (P.toClosedOrientedManifold.component c).Carrier := by
  obtain ⟨eta, heta, hclass⟩ := exists_compact_component_canonical_poincareStandard_tolerance.{u}
  refine ⟨eta, heta, ?_⟩
  intro eps heps P a s G g C1 C2 q R hq hqR hcanonical c hterminal
  obtain ⟨Phi, hPhi, hpinch⟩ :=
    exists_admissiblePinchingFunction_phiAlmostNonnegative_closedOpen
      G.lt G.flow G.equation (by simp [ThreeSpace])
  have hbound : ∀ x : P.Carrier, ∀ t ∈ Ioo a s, q < G.flow.scalar t x →
      |derivWithin (fun v => G.flow.scalar v x) (Iic t) t| ≤
        (⟨max C2 0, le_max_right _ _⟩ : ℝ≥0) * G.flow.scalar t x ^ 2 := by
    intro x t ht hx
    obtain ⟨W, _⟩ := hcanonical x t ht hx
    exact W.time_derivative.trans
      (mul_le_mul_of_nonneg_right (le_max_left C2 0) (sq_nonneg _))
  obtain ⟨d, hd, hhigh⟩ := g.eventually_scalar_gt_on_closed_set hq hbound hPhi hpinch
    (P.componentOpen_isClosed c) hqR hterminal
  obtain ⟨t, ht⟩ := exists_between hd.2
  have htime : t ∈ Ioo a s := ⟨hd.1.trans_lt ht.1, ht.2⟩
  choose W hchart using fun x : (P.toClosedOrientedManifold.component c).Carrier =>
    hcanonical x.val t htime (hhigh t ht x.val x.property)
  exact hclass eps heps P.toClosedOrientedManifold G.flow c C1 C2 t W hchart

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab
