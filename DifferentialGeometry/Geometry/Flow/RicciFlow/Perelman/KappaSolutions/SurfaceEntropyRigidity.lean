import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.SurfaceEntropyBasic
import Mathlib.Topology.Order.MonotoneConvergence

set_option autoImplicit false

noncomputable section

open Filter Set
open scoped Topology Manifold ContDiff
open DifferentialGeometry.Geometry.Curvature

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [CompactSpace M] [Nonempty M]

theorem surfaceEntropy_rigidity_of_backward_minimum
    (g : ℝ → SmoothRiemannianMetric I M) (C : ℝ)
    (hC : ∀ t : ℝ, t ≤ 0 → totalScalarCurvature (g t) = C)
    (hpositive : ∀ t : ℝ, t ≤ 0 → ∀ x : M, 0 < metricScalarAt (I := I) (g t) x)
    (hmono : AntitoneOn (fun t => surfaceEntropy (g t)) (Iic (0 : ℝ)))
    (tau : ℕ → ℝ) (htau : Tendsto tau atTop atTop)
    (hbackward : Tendsto (fun n => surfaceEntropy (g (-tau n)))
      atTop (𝓝 (C * Real.log C))) :
    ∀ t : ℝ, t ≤ 0 → surfaceEntropy (g t) = C * Real.log C ∧
      ∃ c : ℝ, ∀ x : M, metricScalarAt (I := I) (g t) x = c := by
  intro t ht
  have hminimum := surfaceEntropy_lower_and_eq_iff_constant (g t) (hpositive t ht)
  rw [hC t ht] at hminimum
  have hupperEventually : ∀ᶠ n in atTop,
      surfaceEntropy (g t) ≤ surfaceEntropy (g (-tau n)) := by
    filter_upwards [htau (eventually_ge_atTop (-t))] with n hn
    change -t ≤ tau n at hn
    have hnt : -tau n ≤ t := by linarith
    exact hmono (hnt.trans ht) ht hnt
  have hupper : surfaceEntropy (g t) ≤ C * Real.log C :=
    le_of_tendsto_of_tendsto
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => surfaceEntropy (g t))
        atTop (𝓝 (surfaceEntropy (g t)))) hbackward hupperEventually
  have heq : surfaceEntropy (g t) = C * Real.log C :=
    le_antisymm hupper hminimum.1
  exact ⟨heq, hminimum.2.mp heq⟩

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
