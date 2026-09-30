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


theorem exists_component_poincareStandard_tolerance_of_spatial_neighborhoods :
    ∃ eta : ℝ, 0 < eta ∧ ∀ eps : ℝ, eps ≤ eta →
      ∀ (P : OrientedThreeStage.{u}) (a s : ℝ) (G : P.IncomingSlab a s)
        (g : G.TerminalLimitMetric) (q0 q R : ℝ) (C : ℝ≥0),
      0 < q0 → q < R →
      (∀ x : P.Carrier, ∀ t ∈ Ioo a s, q0 < G.flow.scalar t x →
        |derivWithin (fun v => G.flow.scalar v x) (Iic t) t| ≤ C * G.flow.scalar t x ^ 2) →
      ∀ c : ConnectedComponents P.Carrier,
      (∀ (t : ℝ), t ∈ Ioo a s →
        ∀ x : (P.toClosedOrientedManifold.component c).Carrier, q < G.flow.scalar t x.val →
        ¬ Nonempty (SpatialNeck ((G.flow.base.metric t).restrictOpen (P.componentOpen c)) eps x) →
        Nonempty (PositiveComponent (M := (P.toClosedOrientedManifold.component c).Carrier) univ) ∨
        admitsConstantPositiveSectionalCurvature (I := ThreeModel)
          (M := (P.toClosedOrientedManifold.component c).Carrier) ∨
        ∃ (K : CompactDomain (P.toClosedOrientedManifold.component c).Carrier)
          (v : (P.toClosedOrientedManifold.component c).Carrier)
          (nk : SpatialNeck ((G.flow.base.metric t).restrictOpen (P.componentOpen c)) eps v)
          (level : ℝ),
          0 < metricScalarAt ((G.flow.base.metric t).restrictOpen (P.componentOpen c)) x ∧
          Nonempty (CapCore K.carrier) ∧ |level| ≤ 4 ∧
          frontier K.carrier = range (fun z : Sphere 2 => nk.map (z, level)) ∧
          riemannianBallOf ((G.flow.base.metric t).restrictOpen (P.componentOpen c)) x
            (1000 / Real.sqrt (metricScalarAt ((G.flow.base.metric t).restrictOpen
              (P.componentOpen c)) x)) ⊆ interior K.carrier) →
      (∀ x : G.terminalRegularOpen, ConnectedComponents.mk x.val = c →
        R < metricScalarAt g.metric x) →
      isPoincareStandard (P.toClosedOrientedManifold.component c).Carrier := by
  obtain ⟨eta, heta, hclass⟩ := exists_compact_spatial_poincareStandard_tolerance.{u}
  refine ⟨eta, heta, ?_⟩
  intro eps heps P a s G g q0 q R C hq0 hqR hderiv c hspatial hterminal
  obtain ⟨Phi, hPhi, hpinch⟩ :=
    exists_admissiblePinchingFunction_phiAlmostNonnegative_closedOpen
      G.lt G.flow G.equation (by simp [ThreeSpace])
  obtain ⟨d, hd, hhigh⟩ := g.eventually_scalar_gt_on_closed_set hq0 hderiv hPhi hpinch
    (P.componentOpen_isClosed c) hqR hterminal
  obtain ⟨t, ht⟩ := exists_between hd.2
  have htime : t ∈ Ioo a s := ⟨hd.1.trans_lt ht.1, ht.2⟩
  exact hclass eps heps (P.toClosedOrientedManifold.component c)
    ((G.flow.base.metric t).restrictOpen (P.componentOpen c))
    (fun x hx => hspatial t htime x (hhigh t ht x.val x.property) hx)


theorem exists_component_poincareStandard_tolerance_of_canonical_neighborhoods :
    ∃ eta : ℝ, 0 < eta ∧ ∀ eps : ℝ, eps ≤ eta →
      ∀ (P : OrientedThreeStage.{u}) (a s : ℝ) (G : P.IncomingSlab a s)
        (g : G.TerminalLimitMetric) (C1 C2 q R : ℝ),
      0 < q → q < R →
      (∀ x : P.Carrier, ∀ t ∈ Ioo a s, q < G.flow.scalar t x →
        ∃ W : CanonicalWitness G.flow eps C1 C2 x t, W.capTubeHasNeckChart eps) →
      ∀ Ctime : ℝ≥0, (∀ x : P.Carrier, ∀ t ∈ Ioo a s, q < G.flow.scalar t x →
        |derivWithin (fun v => G.flow.scalar v x) (Iic t) t| ≤ Ctime * G.flow.scalar t x ^ 2) →
      ∀ c : ConnectedComponents P.Carrier,
        (∀ x : G.terminalRegularOpen, ConnectedComponents.mk x.val = c →
          R < metricScalarAt g.metric x) →
        isPoincareStandard (P.toClosedOrientedManifold.component c).Carrier := by
  obtain ⟨eta, heta, hclass⟩ := exists_component_poincareStandard_tolerance_of_spatial_neighborhoods.{u}
  refine ⟨eta, heta, ?_⟩
  intro eps heps P a s G g C1 C2 q R hq hqR hcanonical Ctime hbound c hterminal
  apply hclass eps heps P a s G g q q R Ctime hq hqR hbound c ?_ hterminal
  intro t ht x hqx hx
  let U := P.componentOpen c
  let xU : U := ⟨x.val, x.property⟩
  let _ : CompactSpace U := (P.toClosedOrientedManifold.component c).compact
  let _ : SigmaCompactSpace U := inferInstance
  have hU : (U : Set P.Carrier) = connectedComponent (xU : P.Carrier) := by
    ext y
    change ConnectedComponents.mk y = c ↔ y ∈ connectedComponent (xU : P.Carrier)
    constructor
    · intro hy
      exact ConnectedComponents.coe_eq_coe'.mp (hy.trans xU.property.symm)
    · intro hy
      exact (ConnectedComponents.coe_eq_coe'.mpr hy).trans xU.property
  obtain ⟨W, hchart⟩ := hcanonical x.val t ht hqx
  rcases W.spatial_cap_or_whole_on_connectedComponent_of_not_spatial_neck
      U xU hU hchart hx with hp | hr | hc
  · exact Or.inl hp
  · obtain ⟨z, hr⟩ := hr
    exact Or.inr (Or.inl
      (admitsConstantPositiveSectionalCurvature_of_roundComponent
        (P.toClosedOrientedManifold.component c) hr.some))
  · exact Or.inr (Or.inr hc)

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab
