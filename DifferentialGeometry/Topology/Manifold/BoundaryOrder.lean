import DifferentialGeometry.Topology.Manifold.BoundaryExtrema
import Mathlib.Topology.NhdsSet
import Mathlib.Tactic.Linarith

noncomputable section
open Set Filter Topology
open scoped ContDiff Manifold

namespace DifferentialGeometry.Topology.Manifold

theorem boundary_value_lt_of_inward_coordinate
    {E H W : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    [TopologicalSpace W] [ChartedSpace H W] [CompactSpace W]
    {u q : W → ℝ} {a b k : ℝ}
    (hreg : ∀ x, mvfderiv I u x ≠ 0)
    (hboundary : ∀ x, I.IsBoundaryPoint x → u x = a ∨ u x = b)
    (γ : ℝ → W) (hγ : ContinuousWithinAt γ (Ici 0) 0)
    (hlocal : u =ᶠ[𝓝 (γ 0)] q) (hk : 0 < k)
    (hcoordinate : ∀ᶠ t in 𝓝[≥] (0 : ℝ), q (γ t) = a + k * t) : a < b := by
  have hpatch : ∀ᶠ t in 𝓝[≥] (0 : ℝ), u (γ t) = a + k * t :=
    (hlocal.comp_tendsto hγ).trans hcoordinate
  obtain ⟨r, hr, hwithin⟩ := (nhdsGE_basis_of_exists_gt (exists_gt (0 : ℝ))).mem_iff.mp hpatch
  have ht : (r / 2 : ℝ) ∈ Ico 0 r := by constructor <;> linarith only [hr]
  have habove : a < u (γ (r / 2)) := by
    rw [hwithin ht]
    have hpos : 0 < k * (r / 2) := mul_pos hk (by linarith only [hr])
    linarith only [hpos]
  by_contra hab
  have hbound := range_subset_Icc_of_boundary_values (le_of_not_gt hab) hreg
    (fun x hx ↦ (hboundary x hx).symm) (mem_range_self (γ (r / 2)))
  exact (not_lt_of_ge hbound.2) habove

end DifferentialGeometry.Topology.Manifold
