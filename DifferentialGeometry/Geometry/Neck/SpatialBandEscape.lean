import DifferentialGeometry.Geometry.Neck.SpatialUnitBandReturn
import Mathlib.Order.Filter.AtTopBot.Basic

open Set Manifold Filter
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

theorem tendsto_spatial_neck_midpoint_cocompact_of_avoids_earlier_band
    {M : Type*} [TopologicalSpace M] [ChartedSpace ThreeSpace M] [IsManifold I3 ∞ M]
    [T2Space M] (g : SmoothRiemannianMetric I3 M) {eps : ℝ}
    (heps : eps ≤ 1 / 156000) (p : ℕ → M) (neck : ∀ n, SpatialNeck g eps (p n))
    (havoid : ∀ i j : ℕ, i < j →
      (neck j).map ((neck j).center, 3 / 2) ∉
        (neck i).map '' (univ ×ˢ Icc (1 : ℝ) 2)) :
    Tendsto (fun n => (neck n).map ((neck n).center, 3 / 2)) atTop (cocompact M) := by
  classical
  apply hasBasis_cocompact.tendsto_right_iff.mpr
  intro K hK
  by_contra h
  have hfreq : ∃ᶠ n in atTop, (neck n).map ((neck n).center, 3 / 2) ∈ K := by
    simpa only [not_eventually, mem_compl_iff, not_not] using h
  obtain ⟨s, hs, hmem⟩ := extraction_of_frequently_atTop hfreq
  obtain ⟨i, j, hij, hj⟩ := exists_spatial_neck_unit_band_return_in_compact g hK heps
    (fun n => p (s n)) (fun n => neck (s n)) hmem
  exact havoid (s i) (s j) (hs hij) hj

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
