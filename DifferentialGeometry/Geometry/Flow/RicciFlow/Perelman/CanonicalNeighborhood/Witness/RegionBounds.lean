import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.CanonicalStrictBounds

set_option autoImplicit false

open Set
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold I3 ∞ M] [T2Space M] [SigmaCompactSpace M]
  {D : RealTimeInterval} {S : SolutionOn (I := I3) (M := M) D}
  {eps C1 C2 t : ℝ} {p : M}

theorem CanonicalWitness.scalar_le_on_union_region
    (witness : CanonicalWitness S eps C1 C2 p t)
    {W V : Set M} (hV : V ⊆ W ∪ witness.domain.carrier) (hp : p ∈ W)
    {B : ℝ} (hB : ∀ x ∈ W, S.scalar t x ≤ B) :
    ∀ x ∈ V, S.scalar t x ≤ C2 * B := by
  have hC2 := witness.one_le_comparison_constant
  have hBpos : 0 < B := witness.Q_pos.trans_le (hB p hp)
  have hBmul : B ≤ C2 * B := le_mul_of_one_le_left hBpos.le hC2
  intro x hx
  rcases hV hx with hxW | hxV
  · exact (hB x hxW).trans hBmul
  · exact (witness.scalar_bounds x hxV).2.trans
      (mul_le_mul_of_nonneg_left (hB p hp) (zero_le_one.trans hC2))

theorem CanonicalWitness.scalar_le_sq_mul_at_mem_domain
    (witness : CanonicalWitness S eps C1 C2 p t) {anchor : M}
    (hanchor : anchor ∈ witness.domain.carrier) :
    ∀ x ∈ witness.domain.carrier, S.scalar t x ≤ C2 ^ 2 * S.scalar t anchor := by
  have hC2 : 0 < C2 := zero_lt_one.trans_le witness.one_le_comparison_constant
  have hcenter : S.scalar t p ≤ C2 * S.scalar t anchor := by
    have h := mul_le_mul_of_nonneg_left (witness.scalar_bounds anchor hanchor).1 hC2.le
    simpa only [← mul_assoc, mul_inv_cancel₀ hC2.ne', one_mul] using h
  intro x hx
  have h := (witness.scalar_bounds x hx).2.trans (mul_le_mul_of_nonneg_left hcenter hC2.le)
  nlinarith

theorem CanonicalWitness.scalar_le_max_on_union_region_of_anchor
    (witness : CanonicalWitness S eps C1 C2 p t)
    {W V : Set M} (hV : V ⊆ W ∪ witness.domain.carrier)
    {anchor : M} (hanchor : anchor ∈ witness.domain.carrier)
    {B : ℝ} (hB : ∀ x ∈ W, S.scalar t x ≤ B) :
    ∀ x ∈ V, S.scalar t x ≤ max B (C2 ^ 2 * S.scalar t anchor) := by
  intro x hx
  rcases hV hx with hxW | hxV
  · exact (hB x hxW).trans (le_max_left _ _)
  · exact (witness.scalar_le_sq_mul_at_mem_domain hanchor x hxV).trans (le_max_right _ _)

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
