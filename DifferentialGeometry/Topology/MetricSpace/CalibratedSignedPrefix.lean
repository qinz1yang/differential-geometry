import DifferentialGeometry.Topology.MetricSpace.SignedPrefix

open Set

namespace Metric

variable {X : Type*} [MetricSpace X]

theorem exists_calibrated_signed_prefix
    (hcurves : ∀ p a : X, ∀ η : ℝ, 0 < η →
      ∃ c : unitInterval → X, Continuous c ∧ c 0 = p ∧ c 1 = a ∧
        eVariationOn c univ < ENNReal.ofReal (dist p a + η))
    (o aPlus aMinus : X) {L η : ℝ} (hL : 0 < L) (hη : 0 < η)
    (hplus : dist o aPlus = L) (hminus : dist o aMinus = L) :
    ∃ Q : Icc (-L) L → X, LipschitzWith 1 Q ∧
      Q ⟨0, ⟨by linarith, hL.le⟩⟩ = o ∧
      (∀ s t, |s.val - t.val| - ((2 * L - dist aPlus aMinus) + 2 * η) ≤ dist (Q s) (Q t)) ∧
      (∀ t, dist (Q t) o ≤ |t.val|) ∧
      ∀ t : Icc (0 : ℝ) L,
        t.val - η ≤ L - dist (Q ⟨t.val, ⟨by linarith [t.property.1], t.property.2⟩⟩) aPlus ∧
        L - dist (Q ⟨t.val, ⟨by linarith [t.property.1], t.property.2⟩⟩) aPlus ≤ t.val ∧
        -t.val ≤ L - dist (Q ⟨-t.val, ⟨by linarith [t.property.2], by linarith [t.property.1]⟩⟩) aPlus ∧
        L - dist (Q ⟨-t.val, ⟨by linarith [t.property.2], by linarith [t.property.1]⟩⟩) aPlus ≤
          -t.val + (2 * L - dist aPlus aMinus) + η := by
  obtain ⟨qp, qm, hpLip, hmLip, hp0, hm0, _, hd, hcross, hcal, _⟩ :=
    exists_opposite_calibrated_prefixes hcurves o aPlus aMinus hL hη hplus hminus
  have hE : 0 ≤ 2 * L - dist aPlus aMinus := by
    have hh := dist_triangle aPlus o aMinus
    rw [dist_comm aPlus o, hplus, hminus] at hh
    linarith
  obtain ⟨Q, hQ, hQ0, halign, hlow, hrad⟩ := exists_signed_prefix_of_opposite_prefixes
    hL.le hE hη.le qp qm hpLip hmLip hp0 hm0
    (fun s t hst => (hd s t hst).1) (fun s t hst => (hd s t hst).2.2.1)
    (fun t u => (hcross t u).1)
  refine ⟨Q, hQ, hQ0, ?_, hrad, ?_⟩
  · intro s t
    linarith [hlow s t]
  · intro t
    rw [(halign t).1, (halign t).2]
    exact hcal t

end Metric
