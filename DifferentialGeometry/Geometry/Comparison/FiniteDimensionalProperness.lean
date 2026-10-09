import DifferentialGeometry.Geometry.Comparison.VaryingLocalGeometry
import DifferentialGeometry.Topology.MetricSpace.HopfRinow

set_option autoImplicit false

open Set Metric

namespace DifferentialGeometry.Geometry.Comparison.Toponogov

theorem properSpace_of_local_comparison_and_dimH
    {X : Type*} [MetricSpace X] [CompleteSpace X]
    (hcurves : ∀ a b : X, ∀ ε : ℝ, 0 < ε →
      ∃ c : unitInterval → X, Continuous c ∧ c 0 = a ∧ c 1 = b ∧
        eVariationOn c univ < ENNReal.ofReal (dist a b + ε))
    {κ : ℝ} (hκ : 0 ≤ κ) {n : ℕ} (hdim : dimH (univ : Set X) ≤ n)
    (hlocal : ∀ p : X, ∃ Ω : Set X, IsOpen Ω ∧ fourPointComparison κ Ω ∧ p ∈ Ω) :
    ProperSpace X := by
  let : LocallyCompactSpace (univ : Set X) :=
    locallyCompactSpace_of_nonnegative_parameter_local_comparison_and_dimH
      hcurves hκ isOpen_univ hdim (fun p _ => hlocal p)
  let : LocallyCompactSpace X := (Homeomorph.Set.univ X).locallyCompactSpace_iff.mp inferInstance
  exact properSpace_of_arbitrarily_short_curves hcurves

end DifferentialGeometry.Geometry.Comparison.Toponogov
