import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.UniformNormalizedDerivativeBounds

set_option autoImplicit false

noncomputable section

open DifferentialGeometry DifferentialGeometry.Topology
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.Geometry.Collapse DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian Set
open scoped Manifold ContDiff ENNReal

namespace GC.LongTime.Ch12

universe u

/-- W1: WBD04 wiring.  From the physical whole-ball bound (WBD03 / W5) and positivity of the
radius function, the normalized-metric bound with a single constant `C w` (the exact shape
consumed by the T4 assembly). -/
theorem exists_normalized_bound_of_physical_W1 {P : OrientedThreeStage.{u}} {g : P.Metric}
    (F : GC.Interface.RawSurgery P g) (K : ℕ)
    (b T : ℝ → ℝ) (A : ℝ → ℕ → ℝ)
    (hb : ∀ w : ℝ, 0 < w → 0 < b w)
    (hphysical : ∀ w : ℝ, 0 < w → ∀ s : RegularSlice F.observation,
      T w ≤ s.time → ∀ (p : s.stage.Carrier) (ρ : ℝ), 0 < ρ →
      ρ ≤ b w * Real.sqrt s.time →
      (∃ z ∈ connectedComponent p, ¬ SectionalBoundedBelowAt s.metric z 0) →
      (∀ q ∈ riemannianBallOf s.metric p ρ,
        SectionalBoundedBelowAt s.metric q (-(ρ ^ 2)⁻¹)) →
      ENNReal.ofReal (w * ρ ^ 3) ≤ ballVolume s.metric p ρ →
      ∀ k : ℕ, k ≤ K → ∀ q ∈ riemannianBallOf s.metric p ρ,
        curvatureDerivativeNorm s.metric k q ≤ A w k * (ρ ^ (k + 2))⁻¹) :
    ∃ (b' T' C : ℝ → ℝ), (∀ w : ℝ, 0 < w → 0 < b' w) ∧ (∀ w, 0 < C w) ∧
      ∀ w : ℝ, 0 < w → ∀ s : RegularSlice F.observation, T' w ≤ s.time →
      ∀ (p : s.stage.Carrier) (r : ℝ), 0 < r → r ≤ b' w →
        (∃ z ∈ connectedComponent p,
          ¬ SectionalBoundedBelowAt s.normalizedMetric z 0) →
        (∀ q ∈ riemannianBallOf s.normalizedMetric p r,
          SectionalBoundedBelowAt s.normalizedMetric q (-(r ^ 2)⁻¹)) →
        ENNReal.ofReal (w * r ^ 3) ≤ ballVolume s.normalizedMetric p r →
        ∀ k : ℕ, k ≤ K → ∀ q ∈ riemannianBallOf s.normalizedMetric p r,
          curvatureDerivativeNorm s.normalizedMetric k q ≤ C w * (r ^ (k + 2))⁻¹ := by
  obtain ⟨C, hC, h⟩ := exists_uniform_normalized_derivative_bound_of_physical F K b T A hphysical
  exact ⟨b, T, C, hb, hC, h⟩

end GC.LongTime.Ch12
