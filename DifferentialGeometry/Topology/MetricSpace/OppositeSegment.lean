import DifferentialGeometry.Topology.MetricSpace.SegmentExteriorDistance

set_option autoImplicit false

open Set Metric

namespace Metric

variable {X : Type*} [MetricSpace X]

theorem segment_interior_outside_of_point_outside {D : ℝ} (hD : 0 ≤ D)
    {σ τ : Icc (0 : ℝ) D → X} (hσ : Isometry σ) (hτ : Isometry τ)
    (ho : IsOpen (σ '' {t | 0 < (t : ℝ) ∧ (t : ℝ) < D}))
    (hzero : τ ⟨0, le_rfl, hD⟩ = σ ⟨0, le_rfl, hD⟩)
    (hend : τ ⟨D, hD, le_rfl⟩ = σ ⟨D, hD, le_rfl⟩)
    {w : Icc (0 : ℝ) D} (hw : τ w ∉ range σ) :
    ∀ t : Icc (0 : ℝ) D, 0 < (t : ℝ) → (t : ℝ) < D → τ t ∉ range σ := by
  have hw0 : 0 < (w : ℝ) := by
    apply lt_of_le_of_ne w.property.1
    intro heq
    apply hw
    exact ⟨⟨0, le_rfl, hD⟩, hzero.symm.trans (congrArg τ (Subtype.ext heq))⟩
  have hwD : (w : ℝ) < D := by
    apply lt_of_le_of_ne w.property.2
    intro heq
    apply hw
    exact ⟨⟨D, hD, le_rfl⟩, hend.symm.trans (congrArg τ (Subtype.ext heq.symm))⟩
  let : PreconnectedSpace (Ioo (0 : ℝ) D) := Subtype.preconnectedSpace isPreconnected_Ioo
  let f : Ioo (0 : ℝ) D → X := fun s => τ ⟨s, s.property.1.le, s.property.2.le⟩
  have hf : Continuous f := hτ.continuous.comp (by fun_prop)
  have havoid (s : Ioo (0 : ℝ) D) :
      f s ≠ σ ⟨0, le_rfl, hD⟩ ∧ f s ≠ σ ⟨D, hD, le_rfl⟩ := by
    constructor
    · intro heq
      rw [← hzero] at heq
      have ht := congrArg (fun t : Icc (0 : ℝ) D => (t : ℝ)) (hτ.injective heq)
      change (s : ℝ) = 0 at ht
      linarith [s.property.1]
    · intro heq
      rw [← hend] at heq
      have ht := congrArg (fun t : Icc (0 : ℝ) D => (t : ℝ)) (hτ.injective heq)
      change (s : ℝ) = D at ht
      linarith [s.property.2]
  intro t ht0 htD htin
  obtain ⟨s, hs⟩ := htin
  let u : Ioo (0 : ℝ) D := ⟨t, ht0, htD⟩
  have hs0 : 0 < (s : ℝ) := by
    apply lt_of_le_of_ne s.property.1
    intro heq
    exact (havoid u).1 (hs.symm.trans (congrArg σ (Subtype.ext heq.symm)))
  have hsD : (s : ℝ) < D := by
    apply lt_of_le_of_ne s.property.2
    intro heq
    exact (havoid u).2 (hs.symm.trans (congrArg σ (Subtype.ext heq)))
  obtain ⟨v, hv⟩ := exists_segment_endpoint_on_curve_of_exit hD hσ ho hf
    ⟨τ t, ⟨u, rfl⟩, s, ⟨hs0, hsD⟩, hs⟩ ⟨⟨w, hw0, hwD⟩, hw⟩
  exact hv.elim (havoid v).1 (havoid v).2

end Metric
