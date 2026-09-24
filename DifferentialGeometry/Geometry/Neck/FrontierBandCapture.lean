import DifferentialGeometry.Geometry.Neck.Spatial
import DifferentialGeometry.Topology.Connected.CoverBySides

noncomputable section

open Set Manifold
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold I3 ∞ M]
  {g : SmoothRiemannianMetric I3 M} {eps : ℝ} {p : M}

theorem SpatialNeck.closed_unit_band_subset_interior_of_frontier_level_two
    (nk : SpatialNeck g eps p) {K : Set M} {b : ℝ} (hb : b = -2 ∨ b = 2)
    (hfront : frontier K = range (fun q : Sphere 2 => nk.map (q, b)))
    (hmeet : (nk.map '' (univ ×ˢ Icc (-1 : ℝ) 1) ∩ K).Nonempty) :
    nk.map '' (univ ×ˢ Icc (-1 : ℝ) 1) ⊆ interior K := by
  have hlen : (2 : ℝ) < eps⁻¹ :=
    (lt_inv_comm₀ (by norm_num) nk.eps_pos).mpr (by linarith [nk.eps_small])
  have hsrc : univ ×ˢ Icc (-1 : ℝ) 1 ⊆ nk.map.source := by
    intro z hz
    exact nk.domain ⟨hz.1, by linarith [hz.2.1], by linarith [hz.2.2]⟩
  have hbsrc (q : Sphere 2) : (q, b) ∈ nk.map.source := by
    apply nk.domain
    refine ⟨mem_univ _, ?_, ?_⟩ <;> rcases hb with rfl | rfl <;> linarith
  let _ : ConnectedSpace (Sphere 2) := isConnected_iff_connectedSpace.mp
    (isConnected_sphere (Module.one_lt_rank_of_one_lt_finrank (by simp [ThreeSpace]))
      (0 : ThreeSpace) zero_le_one)
  apply DifferentialGeometry.Topology.isPreconnected_subset_interior_of_meets_of_disjoint_frontier
    ((isPreconnected_univ.prod isPreconnected_Icc).image nk.map
      (nk.map.contMDiffOn_toFun.continuousOn.mono hsrc)) hmeet
  rw [hfront, disjoint_left]
  rintro x ⟨z, hz, rfl⟩ ⟨q, hq⟩
  have he := nk.map.toPartialEquiv.injOn (hbsrc q) (hsrc hz) hq
  have hh : b = z.2 := congrArg Prod.snd he
  rcases hb with rfl | rfl <;> linarith [hz.2.1, hz.2.2]

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
