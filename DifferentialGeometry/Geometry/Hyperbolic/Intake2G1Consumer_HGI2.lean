import DifferentialGeometry.Geometry.Hyperbolic.RawMetricThinness

/-!
# Consumer of the G1 intake (S-HG-INTAKE-2, suffix `_HGI2`)

`RawMetricThinness`: for a hyperbolic truncation `Tr` of a finite-volume model `H` and `o : H`
there are tolerances `η, δ > 0` such that the volume superlevel set of a map with raw pullback
derivative error `≤ δ` lies in the ball of radius `1 / (2 w)` around `o`.  Here we read off the
two positive tolerances.
-/

set_option autoImplicit false

namespace DifferentialGeometry.Geometry.Hyperbolic

universe u

theorem raw_thinness_tolerances_pos_HGI2 {H : FiniteVolumeHyperbolicModel.{u}}
    (Tr : HyperbolicTruncation H) (o : H.Carrier) : ∃ η δ : ℝ, 0 < η ∧ 0 < δ := by
  obtain ⟨η, hη, δ, hδ, -⟩ :=
    HyperbolicTruncation.exists_volume_superlevel_preimage_subset_ball_of_raw_pullback_derivatives.{
      u, 0, 0, 0} Tr o
  exact ⟨η, δ, hη, hδ⟩

end DifferentialGeometry.Geometry.Hyperbolic
