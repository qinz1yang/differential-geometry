import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Convergence.Maps
import Mathlib.Topology.Connected.PathConnected

set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff

namespace DifferentialGeometry.CheegerGromovCompactness

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}

attribute [local instance] PointedRiemannianManifold.topology
  PointedRiemannianManifold.charted PointedRiemannianManifold.smooth
  PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact

theorem PointedRiemannianConvergenceMaps.path_connected_space_of_frequently_path_connected_targets
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {L : PointedRiemannianManifold.{u, uE, uH} (I := I)} {σ : ℕ → ℕ}
    (Φ : PointedRiemannianConvergenceMaps X L σ)
    (htarget : ∃ᶠ n in atTop, IsPathConnected (Φ.target n)) : PathConnectedSpace L.M := by
  apply pathConnectedSpace_iff_univ.mpr
  refine ⟨L.basepoint, mem_univ _, ?_⟩
  intro x _
  obtain ⟨N, hN⟩ := Φ.source_subset (isCompact_singleton (x := x))
  obtain ⟨n, htn, hn⟩ := (htarget.and_eventually (eventually_ge_atTop N)).exists
  have hsource : IsPathConnected (Φ.source n) := by
    have hh := htn.image' (Φ.partialDiffeomorph n).symm.contMDiffOn_toFun.continuousOn
    have heq : (Φ.partialDiffeomorph n).symm '' Φ.target n = Φ.source n := by
      ext y
      constructor
      · rintro ⟨z, hz, rfl⟩
        exact (Φ.partialDiffeomorph n).map_target' hz
      · intro hy
        refine ⟨Φ.partialDiffeomorph n y, (Φ.partialDiffeomorph n).map_source' hy, ?_⟩
        exact (Φ.partialDiffeomorph n).left_inv hy
    rwa [heq] at hh
  exact (hsource.joinedIn L.basepoint (Φ.base_mem n) x
    (hN n hn (mem_singleton x))).mono (subset_univ _)

end DifferentialGeometry.CheegerGromovCompactness
