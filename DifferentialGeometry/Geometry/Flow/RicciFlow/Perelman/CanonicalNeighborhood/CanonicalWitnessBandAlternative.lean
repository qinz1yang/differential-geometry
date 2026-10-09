import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.CanonicalStrictBounds

set_option autoImplicit false
noncomputable section
open Set
open scoped Manifold ContDiff Topology
namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold I3 ∞ M] [T2Space M] [SigmaCompactSpace M]
  {D : RealTimeInterval} {S : SolutionOn (I := I3) (M := M) D}
  {eps C1 C2 A : ℝ} {x y : M} {t : ℝ}

theorem CanonicalWitness.scalar_band_at_four_mul_level
    (W : CanonicalWitness S eps C1 C2 x t) (hA : 0 < A)
    (hQ : S.scalar t x = 4 * C2 * A) :
    ∀ z ∈ W.domain.carrier,
      2 * A < S.scalar t z ∧ S.scalar t z ≤ 4 * C2 ^ 2 * A := by
  have hC2 : 0 < C2 := zero_lt_one.trans_le W.one_le_comparison_constant
  intro z hz
  have hb := W.scalar_bounds z hz
  rw [hQ] at hb
  have hlo : C2⁻¹ * (4 * C2 * A) = 4 * A := by
    field_simp
  have hhi : C2 * (4 * C2 * A) = 4 * C2 ^ 2 * A := by ring
  rw [hlo, hhi] at hb
  exact ⟨by linarith [hb.1], hb.2⟩

theorem CanonicalWitness.neck_or_cap_at_four_mul_level
    (W : CanonicalWitness S eps C1 C2 x t) (hA : 0 < A)
    (hQ : S.scalar t x = 4 * C2 * A)
    (hy : y ∈ connectedComponent x) (hyA : S.scalar t y ≤ A) :
    (∃ nk : LocalNeck S eps x t W.domain.carrier,
      W.alternative = CanonicalAlternative.neck nk) ∨
    ∃ cap : LocalCap S eps x t W.domain.carrier,
      ∃ hdepth : ∀ z ∈ cap.tube,
        10000 / Real.sqrt (S.scalar t x) ≤ metricDistance (S.base.metric t) x z,
        W.alternative = CanonicalAlternative.cap cap hdepth := by
  have hC2 : 0 < C2 := zero_lt_one.trans_le W.one_le_comparison_constant
  apply W.alternative_eq_neck_or_cap_of_mul_scalar_lt hy
  rw [hQ]
  have hmul := mul_le_mul_of_nonneg_left hyA hC2.le
  nlinarith [mul_pos hC2 hA]

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
