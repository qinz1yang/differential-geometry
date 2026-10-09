import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CanonicalNeighborhoodInduction

set_option autoImplicit false
noncomputable section
open Set DifferentialGeometry DifferentialGeometry.Integral.Measure
open scoped Manifold ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
universe u

/-- Enlarge the radius ceiling on the same history, with a positive coefficient
chosen before the history and observation time. -/
theorem exists_noncollapsedBefore_radius_enlargement
    {κ ρ σ : ℝ} (hκ : 0 < κ) (hρ : 0 < ρ) (hσ : 0 < σ) :
    ∃ κ' : ℝ, 0 < κ' ∧ ∀ (H : RetainedCoreHistory.{u}) (t₀ : ℝ),
      H.NoncollapsedBefore κ ρ t₀ → H.NoncollapsedBefore κ' σ t₀ := by
  let a : ℝ := min 1 (ρ / σ)
  have ha : 0 < a := lt_min one_pos (div_pos hρ hσ)
  have ha1 : a ≤ 1 := min_le_left _ _
  have haσ : a * σ ≤ ρ := (le_div_iff₀ hσ).mp (min_le_right _ _)
  refine ⟨κ * a ^ 3, mul_pos hκ (pow_pos ha 3), ?_⟩
  intro H t₀ hnc t p r ht hr hball
  have hr0 : 0 < r := hball.1
  have har : a * r ≤ r := mul_le_of_le_one_left hr0.le ha1
  have harρ : a * r ≤ ρ :=
    (mul_le_mul_of_nonneg_left hr ha.le).trans haσ
  have hsmall := hball.mono_radius H.toHistory (mul_pos ha hr0) har
  have hv := hnc t p (a * r) ht harρ hsmall
  calc ENNReal.ofReal (κ * a ^ 3) * ENNReal.ofReal r ^ 3
      = ENNReal.ofReal κ * ENNReal.ofReal (a * r) ^ 3 := by
        rw [ENNReal.ofReal_mul hκ.le, ENNReal.ofReal_mul ha.le,
          ENNReal.ofReal_pow ha.le, mul_pow, mul_assoc]
    _ ≤ _ := hv
    _ ≤ _ := MeasureTheory.measure_mono (riemannianBallOf_mono _ _ har)

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
