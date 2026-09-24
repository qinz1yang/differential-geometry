import DifferentialGeometry.Geometry.Neck.SpatialUnitBandReturn

set_option autoImplicit false
open Set Manifold
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold I3 ∞ M] [T2Space M]
  (g : SmoothRiemannianMetric I3 M) {eps : ℝ} {K : Set M}
  (hK : IsCompact K) (heps : eps ≤ 1 / 156000) (p : ℕ → M)
  (neck : ∀ n, SpatialNeck g eps (p n))
  (hp : ∀ n, (neck n).map ((neck n).center, 3 / 2) ∈ K)
  (W : ℕ → Set M) (hW : Monotone W)

include hK heps hp hW in
theorem exists_spatial_neck_midpoint_mem_of_monotone
    (hband : ∀ n, (neck n).map '' (univ ×ˢ Icc (1 : ℝ) 2) ⊆ W (n + 1)) :
    ∃ n, (neck n).map ((neck n).center, 3 / 2) ∈ W n := by
  obtain ⟨i, j, hij, hreturn⟩ :=
    exists_spatial_neck_unit_band_return_in_compact g hK heps p neck hp
  exact ⟨j, hW (Nat.succ_le_of_lt hij) (hband i hreturn)⟩

include hK heps hp hW in
theorem not_forall_spatial_neck_unit_band_subset_sdiff :
    ¬ ∀ n, (neck n).map '' (univ ×ˢ Icc (1 : ℝ) 2) ⊆ W (n + 1) \ W n := by
  intro hband
  obtain ⟨n, hn⟩ := exists_spatial_neck_midpoint_mem_of_monotone g hK heps p neck hp W hW
    (fun n x hx => (hband n hx).1)
  exact (hband n ⟨((neck n).center, 3 / 2), ⟨mem_univ _, by norm_num⟩, rfl⟩).2 hn

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
