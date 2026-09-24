import DifferentialGeometry.Geometry.Neck.CompactSide
import DifferentialGeometry.Geometry.Neck.SpatialFixedRecentering

set_option autoImplicit false
noncomputable section
open Set Manifold
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

theorem exists_spatial_neck_unit_band_return_in_compact
    {M : Type*} [TopologicalSpace M] [ChartedSpace ThreeSpace M] [IsManifold I3 ∞ M]
    [T2Space M] (g : SmoothRiemannianMetric I3 M) {eps : ℝ} {K : Set M}
    (hK : IsCompact K) (heps : eps ≤ 1 / 156000) (p : ℕ → M)
    (neck : ∀ n, SpatialNeck g eps (p n))
    (hp : ∀ n, (neck n).map ((neck n).center, 3 / 2) ∈ K) :
    ∃ i j : ℕ, i < j ∧
      (neck j).map ((neck j).center, 3 / 2) ∈
        (neck i).map '' (univ ×ˢ Icc (1 : ℝ) 2) := by
  classical
  let q : ℕ → M := fun n => (neck n).map ((neck n).center, 3 / 2)
  have hchoose (n : ℕ) : ∃ out : SpatialNeck g (13000 * eps) (q n),
      out.center = (neck n).center ∧
      out.map = partialDiffeomorphTransMixed
        (DifferentialGeometry.Geometry.Metric.cylinderAxialDiffeomorph
          (I := I2) (M := Sphere 2) (3 / 2) 1 (by norm_num)).toPartialDiffeomorph
        (neck n).map :=
    ((neck n).exists_at_coordinate_mul heps (neck n).center (by norm_num)).2
  choose out hcenter hmap using hchoose
  obtain ⟨i, j, hij, hj⟩ :=
    exists_spatial_neck_half_slab_return_in_compact g hK q out hp
  obtain ⟨⟨v, t⟩, ht, heq⟩ := hj
  refine ⟨i, j, hij, (v, 3 / 2 + t), ?_, ?_⟩
  · exact ⟨mem_univ _, by constructor <;> linarith [ht.2.1, ht.2.2]⟩
  · rw [(neck i).translated_map_apply (neck i).center (out i) (hmap i) v t] at heq
    exact heq

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
