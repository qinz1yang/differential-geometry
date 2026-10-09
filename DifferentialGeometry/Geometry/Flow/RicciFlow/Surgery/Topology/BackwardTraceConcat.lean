import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.Backward

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.BackwardPointTrace

universe u

variable {H : ObservedHistory.{u}} {first mid last : Fin (H.eventCount + 1)}
  {hml : mid ≤ last} {endpoint : (H.stage last).Carrier}

def concat (B : BackwardPointTrace H mid last hml endpoint) {hfm : first ≤ mid}
    (A : BackwardPointTrace H first mid hfm (B.point mid le_rfl hml)) :
    BackwardPointTrace H first last (hfm.trans hml) endpoint where
  point j hf hl := if hj : j ≤ mid then A.point j hf hj else B.point j (le_of_not_ge hj) hl
  endpoint_eq := by
    by_cases h : last ≤ mid
    · have he : mid = last := le_antisymm hml h
      subst he
      simp only [dite_eq_left h]
      exact A.endpoint_eq.trans B.endpoint_eq
    · simp only [dite_eq_right h]
      exact B.endpoint_eq
  crossing i hf hl := by
    by_cases hs : i.succ ≤ mid
    · have hc : i.castSucc ≤ mid := i.castSucc_lt_succ.le.trans hs
      simp only [dite_eq_left hs, dite_eq_left hc]
      exact A.crossing i hf hs
    · have hm : mid ≤ i.castSucc := Fin.le_castSucc_iff.mpr (lt_of_not_ge hs)
      by_cases hc : i.castSucc ≤ mid
      · have he : i.castSucc = mid := le_antisymm hc hm
        subst he
        simp only [dite_eq_right hs, dite_eq_left hc]
        have hA : A.point i.castSucc hf hc = B.point i.castSucc le_rfl hml := A.endpoint_eq
        rw [hA]
        exact B.crossing i le_rfl hl
      · simp only [dite_eq_right hs, dite_eq_right hc]
        exact B.crossing i hm hl

theorem concat_point_of_le (B : BackwardPointTrace H mid last hml endpoint) {hfm : first ≤ mid}
    (A : BackwardPointTrace H first mid hfm (B.point mid le_rfl hml))
    (j : Fin (H.eventCount + 1)) (hf : first ≤ j) (hl : j ≤ last) (hj : j ≤ mid) :
    (B.concat A).point j hf hl = A.point j hf hj := by
  change (if hj : j ≤ mid then A.point j hf hj else B.point j (le_of_not_ge hj) hl) = _
  rw [dite_eq_left hj]

theorem concat_point_of_ge (B : BackwardPointTrace H mid last hml endpoint) {hfm : first ≤ mid}
    (A : BackwardPointTrace H first mid hfm (B.point mid le_rfl hml))
    (j : Fin (H.eventCount + 1)) (hf : first ≤ j) (hl : j ≤ last) (hj : mid ≤ j) :
    (B.concat A).point j hf hl = B.point j hj hl := by
  change (if hj : j ≤ mid then A.point j hf hj else B.point j (le_of_not_ge hj) hl) = _
  by_cases h : j ≤ mid
  · rw [dite_eq_left h]
    have he : j = mid := le_antisymm h hj
    subst he
    exact A.endpoint_eq
  · rw [dite_eq_right h]

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.BackwardPointTrace
