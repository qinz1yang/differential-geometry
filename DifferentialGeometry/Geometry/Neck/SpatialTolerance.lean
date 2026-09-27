import DifferentialGeometry.Geometry.Neck.Spatial
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.ComparisonComposition

noncomputable section
open Set
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open Surgery.Topology

def SpatialNeck.mono {M : Type*} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
    [IsManifold I3 ∞ M] {g : SmoothRiemannianMetric I3 M} {p : M} {e f : ℝ}
    (nk : SpatialNeck g e p) (hef : e ≤ f) (hf : f < 1 / 11) : SpatialNeck g f p where
  eps_pos := nk.eps_pos.trans_le hef
  eps_small := hf
  Q_pos := nk.Q_pos
  cylinder := nk.cylinder
  map := nk.map
  center := nk.center
  center_eq := nk.center_eq
  domain := by
    have hinv := inv_anti₀ nk.eps_pos hef
    exact fun y hy => nk.domain ⟨hy.1, (neg_le_neg hinv).trans_lt hy.2.1, hy.2.2.trans_le hinv⟩
  comparison := by
    have hinv := inv_anti₀ nk.eps_pos hef
    exact nk.comparison.mono
      (fun y hy => ⟨hy.1, (neg_le_neg hinv).trans_lt hy.2.1, hy.2.2.trans_le hinv⟩)
      (Nat.ceil_le_ceil hinv) hef

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
