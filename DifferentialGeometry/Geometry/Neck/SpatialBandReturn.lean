import DifferentialGeometry.Geometry.Neck.CompactSide
import DifferentialGeometry.Geometry.Neck.SpatialFixedRecentering

set_option autoImplicit false
noncomputable section
open Set Manifold
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ThreeSpace M] [IsManifold I3 ∞ M]
  [T2Space M] (g : SmoothRiemannianMetric I3 M) {eps : ℝ} {K : Set M}
  (hK : IsCompact K) (heps : eps ≤ 1 / 156000) (p : ℕ → M)
  (neck : ∀ n, SpatialNeck g eps (p n))

include hK heps

theorem exists_spatial_neck_band_return_in_compact
    (a r : ℝ) (ha : |a| ≤ 4) (hr : 0 < r) (hreps : r < (13000 * eps)⁻¹)
    (hp : ∀ n, (neck n).map ((neck n).center, a) ∈ K) :
    ∃ i j : ℕ, i < j ∧
      (neck j).map ((neck j).center, a) ∈
        (neck i).map '' (univ ×ˢ Icc (a - r) (a + r)) := by
  classical
  let q : ℕ → M := fun n => (neck n).map ((neck n).center, a)
  have hchoose (n : ℕ) : ∃ out : SpatialNeck g (13000 * eps) (q n),
      out.center = (neck n).center ∧
      out.map = partialDiffeomorphTransMixed
        (DifferentialGeometry.Geometry.Metric.cylinderAxialDiffeomorph
          (I := I2) (M := Sphere 2) a 1 (by norm_num)).toPartialDiffeomorph
        (neck n).map :=
    ((neck n).exists_at_coordinate_mul heps (neck n).center ha).2
  choose out hcenter hmap using hchoose
  obtain ⟨i, j, hij, hj⟩ :=
    exists_spatial_neck_slab_return_in_compact g hK q out hp r hr hreps
  obtain ⟨⟨v, t⟩, ht, heq⟩ := hj
  refine ⟨i, j, hij, (v, a + t), ?_, ?_⟩
  · exact ⟨mem_univ _, by constructor <;> linarith [ht.2.1, ht.2.2]⟩
  · rw [(neck i).translated_map_apply (neck i).center (out i) (hmap i) v t] at heq
    exact heq

theorem exists_spatial_neck_interior_quarter_band_return_in_compact
    (hp : ∀ n, (neck n).map ((neck n).center, 1 / 4) ∈ K) :
    ∃ i j : ℕ, i < j ∧
      (neck j).map ((neck j).center, 1 / 4) ∈
        (neck i).map '' (univ ×ˢ Icc (1 / 8 : ℝ) (3 / 8)) := by
  have halpha : 0 < 13000 * eps := mul_pos (by norm_num) (neck 0).eps_pos
  have hr : (1 / 8 : ℝ) < (13000 * eps)⁻¹ :=
    (lt_inv_comm₀ (by norm_num) halpha).mpr (by linarith)
  simpa only [show (1 / 4 : ℝ) - 1 / 8 = 1 / 8 by norm_num,
    show (1 / 4 : ℝ) + 1 / 8 = 3 / 8 by norm_num] using
    exists_spatial_neck_band_return_in_compact g hK heps p neck
      (1 / 4) (1 / 8) (by norm_num) (by norm_num) hr hp

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
