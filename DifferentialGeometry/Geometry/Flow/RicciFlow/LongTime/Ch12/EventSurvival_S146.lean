import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.EventSurvival_S140

/-!
# CH12-S146, group 1a: forward survival of a point through ONE event (G1c of S140)

`event_survival_S146` = the slab forward estimate `hslab` (S137 `slab_forward_ball_S137` at `E.incoming`, `E.terminal`,
an inline binder) + `terminal_ball_survives_S140`.  The protected ball is the OPEN ball `B_out(q, A)` produced by the
barrier, and survivors are measured strictly inside it (`exp(9 Kb (s-a)) ℓ < A`).
-/

set_option autoImplicit false

noncomputable section

open Set Manifold DifferentialGeometry DifferentialGeometry.Topology
  DifferentialGeometry.PDE.RicciFlow.Surgery.Topology DifferentialGeometry.Geometry.Riemannian
  DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Tensor0SBundle
open scoped Manifold ContDiff ENNReal

namespace GC.LongTime.Ch12

universe u

theorem event_survival_S146 {P Q : OrientedThreeStage.{u}} {a s : ℝ} (E : MetricCutCapEvent P Q a s)
    (hslab : ∀ {u w : P.Carrier} {Kb ℓ R : ℝ}, 0 ≤ Kb → 0 ≤ ℓ →
      Real.exp (9 * Kb * (s - a)) * ℓ < R →
      (∀ t ∈ Ico a s, ∀ x ∈ riemannianBallOf (E.incoming.flow.base.metric t) u R,
        Real.sqrt (normSq0S (E.incoming.flow.base.metric t) x 4 (E.incoming.flow.base.rm04 t x)) ≤ Kb) →
      riemannianEDistOf (E.incoming.flow.base.metric a) u w < ENNReal.ofReal ℓ →
      ∃ u' w' : E.incoming.terminalRegularOpen, u'.val = u ∧ w'.val = w ∧
        riemannianEDistOf E.terminal.metric u' w' ≤ ENNReal.ofReal (Real.exp (9 * Kb * (s - a)) * ℓ))
    {u : P.Carrier} {q : Q.Carrier} (hcross : E.RegularCrossing u q) {Kb ℓ R A : ℝ}
    (hK : 0 ≤ Kb) (hℓ : 0 ≤ ℓ) (hroom : Real.exp (9 * Kb * (s - a)) * ℓ < R)
    (hRm : ∀ t ∈ Ico a s, ∀ x ∈ riemannianBallOf (E.incoming.flow.base.metric t) u R,
      Real.sqrt (normSq0S (E.incoming.flow.base.metric t) x 4 (E.incoming.flow.base.rm04 t x)) ≤ Kb)
    (hprot : riemannianBallOf E.outputMetric q A ⊆ interior (range E.oldOutput))
    (hA : Real.exp (9 * Kb * (s - a)) * ℓ < A)
    {w : P.Carrier} (hw : riemannianEDistOf (E.incoming.flow.base.metric a) u w < ENNReal.ofReal ℓ) :
    ∃ y, E.RegularCrossing w y ∧
      riemannianEDistOf E.outputMetric q y ≤ ENNReal.ofReal (Real.exp (9 * Kb * (s - a)) * ℓ) := by
  obtain ⟨u', w', hu', hw', hd⟩ := hslab hK hℓ hroom hRm hw
  have hr0 : 0 ≤ Real.exp (9 * Kb * (s - a)) * ℓ := by positivity
  have hcross' : E.RegularCrossing u'.val q := hu'.symm ▸ hcross
  have hmid : Real.exp (9 * Kb * (s - a)) * ℓ < (Real.exp (9 * Kb * (s - a)) * ℓ + A) / 2 := by
    linarith
  have hmidA : (Real.exp (9 * Kb * (s - a)) * ℓ + A) / 2 < A := by linarith
  have hprot' : riemannianClosedBallOf E.outputMetric q
      ((Real.exp (9 * Kb * (s - a)) * ℓ + A) / 2) ⊆ interior (range E.oldOutput) := by
    refine Set.Subset.trans ?_ hprot
    intro y hy
    exact lt_of_le_of_lt hy ((ENNReal.ofReal_lt_ofReal_iff (by linarith)).2 hmidA)
  obtain ⟨y, hy1, hy2⟩ := terminal_ball_survives_S140 E hcross' hr0 hmid hprot' w' hd
  exact ⟨y, hw' ▸ hy2, hy1⟩

end GC.LongTime.Ch12
