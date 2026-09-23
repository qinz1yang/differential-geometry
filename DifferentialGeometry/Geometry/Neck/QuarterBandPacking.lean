import DifferentialGeometry.Geometry.Neck.SpatialBandReturn
import DifferentialGeometry.Geometry.Neck.SpatialChart

noncomputable section

open Set
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold I3 ∞ M] [T2Space M]

theorem not_exists_monotone_fresh_neck_quarter_bands_in_compact
    (g : SmoothRiemannianMetric I3 M) {K : Set M} (hcompact : IsCompact K)
    {eps : ℝ} (heps : eps ≤ 1 / 156000)
    (p : ℕ → M) (neck : ∀ n, SpatialNeck g eps (p n))
    (hquarter : ∀ n, (neck n).map ((neck n).center, 1 / 4) ∈ K)
    (W : ℕ → Set M) (hW : Monotone W)
    (hband : ∀ n, (neck n).map '' (univ ×ˢ Icc (1 / 8 : ℝ) (3 / 8)) ⊆ W (n + 1))
    (hfresh : ∀ n, (neck n).map ((neck n).center, 1 / 4) ∉ W n) : False := by
  obtain ⟨i, j, hij, hreturn⟩ :=
    exists_spatial_neck_interior_quarter_band_return_in_compact g hcompact heps p neck hquarter
  exact hfresh j (hW (by omega) (hband i hreturn))

theorem not_exists_monotone_fresh_neck_quarter_bands_on_scalar_sublevels
    (g : SmoothRiemannianMetric I3 M) (hcompact : ∀ L : ℝ,
      IsCompact {x : M | metricScalarAt g x ≤ L})
    {eps Q : ℝ} (heps : eps ≤ 1 / 156000)
    (p : ℕ → M) (neck : ∀ n, SpatialNeck g eps (p n))
    (hQ : ∀ n, metricScalarAt g (p n) ≤ Q)
    (W : ℕ → Set M) (hW : Monotone W)
    (hband : ∀ n, (neck n).map '' (univ ×ˢ Icc (1 / 8 : ℝ) (3 / 8)) ⊆ W (n + 1))
    (hfresh : ∀ n, (neck n).map ((neck n).center, 1 / 4) ∉ W n) : False := by
  have hquarter (n : ℕ) : metricScalarAt g ((neck n).map ((neck n).center, 1 / 4)) ≤
      (1 + 4323 * eps) * Q := by
    have hlen : (1 : ℝ) < eps⁻¹ :=
      (one_lt_inv₀ (neck n).eps_pos).mpr (by linarith [(neck n).eps_small])
    have hscalar := ((neck n).scalar_bounds_on_image_window
      ⟨((neck n).center, 1 / 4), ⟨mem_univ _, by constructor <;> linarith⟩, rfl⟩).2
    exact hscalar.trans (mul_le_mul_of_nonneg_left (hQ n) (by linarith [(neck n).eps_pos]))
  exact not_exists_monotone_fresh_neck_quarter_bands_in_compact g
    (hcompact ((1 + 4323 * eps) * Q)) heps p neck hquarter W hW hband hfresh

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
