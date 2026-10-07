import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.EventDistanceScalar
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistoryPresentation

set_option autoImplicit false
noncomputable section

open Set Manifold
open DifferentialGeometry DifferentialGeometry.Geometry
open scoped Manifold ContDiff NNReal ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

/-- Transport scalar data after identifying the actual terminal open and old
point domains. The same output function is retained by equality elimination. -/
private theorem scalar_data_transport
    {P Q : OrientedThreeStage.{u}} {α : Type u} [TopologicalSpace α]
    {U V : TopologicalSpace.Opens P.Carrier} (hU : U = V)
    {old old' : Set α} (hold : old = old')
    {g : SmoothRiemannianMetric ThreeModel U}
    {g' : SmoothRiemannianMetric ThreeModel V} (hg : HEq g g')
    {output output' : Q.Metric} (hout : output = output')
    {i : C(old, U)} {i' : C(old', V)} (hi : HEq i i')
    {o : C(old, Q.Carrier)} {o' : C(old', Q.Carrier)} (ho : HEq o o')
    {C : ℝ≥0}
    (h : ∀ (p : U) (N : ℝ≥0), ∃ G : Q.Carrier → ℝ,
      (∀ z : old, G (o z) =
        (min (riemannianEDistOf g (i z) p) (N : ℝ≥0∞)).toReal) ∧
      ∀ y z, edist (G y) (G z) ≤ (C : ℝ≥0∞) * riemannianEDistOf output y z) :
    ∀ (p : V) (N : ℝ≥0), ∃ G : Q.Carrier → ℝ,
      (∀ z : old', G (o' z) =
        (min (riemannianEDistOf g' (i' z) p) (N : ℝ≥0∞)).toReal) ∧
      ∀ y z, edist (G y) (G z) ≤ (C : ℝ≥0∞) * riemannianEDistOf output' y z := by
  cases hU
  cases hold
  cases eq_of_heq hg
  cases hout
  cases eq_of_heq hi
  cases eq_of_heq ho
  exact h

/-- Vary finite truncations to recover the actual original terminal distance,
including infinite distances and disconnected terminal components. -/
theorem MetricCutCapEvent.HasUniformDistanceScalar.oldTerminal_edist_le
    {P Q : OrientedThreeStage.{u}} {a s : ℝ} {C : ℝ≥0}
    {E : MetricCutCapEvent P Q a s} (h : E.HasUniformDistanceScalar C)
    (z w : E.old) :
    riemannianEDistOf E.terminal.metric (E.oldTerminal z) (E.oldTerminal w) ≤
      (C : ℝ≥0∞) * riemannianEDistOf E.outputMetric (E.oldOutput z) (E.oldOutput w) := by
  let d := riemannianEDistOf E.terminal.metric (E.oldTerminal z) (E.oldTerminal w)
  let B := (C : ℝ≥0∞) * riemannianEDistOf E.outputMetric (E.oldOutput z) (E.oldOutput w)
  have hmin (N : ℝ≥0) : min d (N : ℝ≥0∞) ≤ B := by
    obtain ⟨G, hG, hLip⟩ := h (E.oldTerminal w) N
    have hzero : G (E.oldOutput w) = 0 := by
      rw [hG w, riemannianEDistOf_self]
      simp
    have hbound := hLip (E.oldOutput z) (E.oldOutput w)
    rw [hG z, hzero] at hbound
    change edist ((min d (N : ℝ≥0∞)).toReal) 0 ≤ B at hbound
    have hfin : min d (N : ℝ≥0∞) ≠ ⊤ :=
      ne_top_of_le_ne_top ENNReal.coe_ne_top (min_le_right _ _)
    simpa only [edist_dist, Real.dist_eq, sub_zero,
      abs_of_nonneg ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hfin] using hbound
  change d ≤ B
  by_contra hle
  have hBd : B < d := lt_of_not_ge hle
  have hBfin : B ≠ ⊤ := ne_top_of_lt hBd
  let N : ℝ≥0 := B.toNNReal + 1
  have hBN : B < (N : ℝ≥0∞) := by
    calc
      B = (B.toNNReal : ℝ≥0∞) := (ENNReal.coe_toNNReal hBfin).symm
      _ < ((B.toNNReal + 1 : ℝ≥0) : ℝ≥0∞) :=
        ENNReal.coe_lt_coe.mpr (lt_add_of_pos_right _ zero_lt_one)
  exact (not_lt_of_ge (hmin N)) (lt_min hBd hBN)

/-- The actual presentation identifies both metrics and both retained point
maps. Transport preserves the same constant, truncation and scalar function. -/
theorem MetricCutCapEvent.SamePresentation.hasUniformDistanceScalar
    {P Q P' Q' : OrientedThreeStage.{u}} {a s a' s' : ℝ} {C : ℝ≥0}
    {E : MetricCutCapEvent P Q a s} {F : MetricCutCapEvent P' Q' a' s'}
    (R : E.SamePresentation F) (h : E.HasUniformDistanceScalar C) :
    F.HasUniformDistanceScalar C := by
  cases R.incomingStage_eq
  cases R.outgoingStage_eq
  cases R.leftTime_eq
  cases R.eventTime_eq
  cases E
  cases F
  cases R.discarded_eq
  cases R.capped_eq
  cases eq_of_heq R.transition_heq
  exact scalar_data_transport (eq_of_heq R.terminalRegion_heq)
    (eq_of_heq R.old_heq) R.terminalMetric_heq (eq_of_heq R.outputMetric_heq)
    R.oldTerminal_heq R.oldOutput_heq h

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
