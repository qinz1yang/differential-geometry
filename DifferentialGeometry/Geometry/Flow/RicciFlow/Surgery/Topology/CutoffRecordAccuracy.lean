import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.GeometricCutoff

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

/-- Enlarge the parameter bounds for accuracy and neck radius at the same event.
All six geometric data fields are retained. Membership in a cutoff class with
additional upper bounds on the new parameters requires separate proofs. -/
theorem GeometricCutoffRecord.exists_of_delta_le_of_neckRadius_le
    {H : ObservedHistory.{u}} {i : Fin H.eventCount} {p q : CutoffParameters}
    (R : GeometricCutoffRecord H i p)
    (hdelta : p.delta (H.time i.succ) ≤ q.delta (H.time i.succ))
    (hneck : p.neckRadius (H.time i.succ) ≤ q.neckRadius (H.time i.succ))
    (hprotected : p.protectedRadius (H.time i.succ) = q.protectedRadius (H.time i.succ))
    (hfixed : p.fixed = q.fixed) (hradius : p.modelRadius = q.modelRadius)
    (horder : p.modelOrder = q.modelOrder) (haccuracy : p.modelAccuracy = q.modelAccuracy)
    (hrecenter : p.recenterConstant = q.recenterConstant) :
    ∃ S : GeometricCutoffRecord H i q,
      S.nominalRadius = R.nominalRadius ∧ S.delta = R.delta ∧ S.order = R.order ∧
      HEq S.neck R.neck ∧ HEq S.backward R.backward ∧ HEq S.static R.static := by
  have htime : 0 ≤ H.time i.succ := by
    rw [← H.time_zero]
    exact H.time_strictMono.monotone (Fin.zero_le i.succ)
  have hbudget : p.delta (H.time i.succ) ^ 2 * p.neckRadius (H.time i.succ) ≤
      q.delta (H.time i.succ) ^ 2 * q.neckRadius (H.time i.succ) :=
    mul_le_mul (pow_le_pow_left₀ (p.delta_pos _ htime).le hdelta 2) hneck
      (p.neckRadius_pos _ htime).le (sq_nonneg _)
  cases p with
  | mk delta neckRadius protectedRadius delta_pos delta_lt_one neckRadius_pos
      protectedRadius_pos fixed modelRadius modelRadius_pos modelOrder modelAccuracy
      modelAccuracy_pos recenterConstant recenterConstant_ge_four =>
    cases q with
    | mk delta' neckRadius' protectedRadius' delta_pos' delta_lt_one' neckRadius_pos'
        protectedRadius_pos' fixed' modelRadius' modelRadius_pos' modelOrder' modelAccuracy'
        modelAccuracy_pos' recenterConstant' recenterConstant_ge_four' =>
      dsimp only at hfixed hradius horder haccuracy hrecenter hprotected
      cases hfixed
      cases hradius
      cases horder
      cases haccuracy
      cases hrecenter
      exact ⟨{
        singular := R.singular
        nominalRadius := R.nominalRadius
        nominal_pos := R.nominal_pos
        nominal_small := fun h => (R.nominal_small h).trans_le hbudget
        nominal_time := R.nominal_time
        delta := R.delta
        delta_pos := R.delta_pos
        delta_le := fun a => (R.delta_le a).trans hdelta
        order := R.order
        order_lower := R.order_lower
        neck := R.neck
        scale_eq := R.scale_eq
        buffer_disjoint := R.buffer_disjoint
        tube_eq := R.tube_eq
        tube_in_buffer := R.tube_in_buffer
        backward := R.backward
        retained_terminal := R.retained_terminal
        protected_interior := by simpa only [← hprotected] using R.protected_interior
        retained_meets_protected := by simpa only [← hprotected] using R.retained_meets_protected
        one_retained_side := R.one_retained_side
        no_cuts_discard := R.no_cuts_discard
        static := R.static
        recenter_scale := R.recenter_scale
        recenter_mark := R.recenter_mark
        recenter_delta := R.recenter_delta
        recenter_scale_comparison := R.recenter_scale_comparison
        recenter_chart := R.recenter_chart
        recenter_in_buffer := R.recenter_in_buffer
        old_eq_retained := R.old_eq_retained
        curvature_preserving := R.curvature_preserving
        scalar_preserving := R.scalar_preserving }, rfl, rfl, rfl, HEq.rfl, HEq.rfl, HEq.rfl⟩

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
