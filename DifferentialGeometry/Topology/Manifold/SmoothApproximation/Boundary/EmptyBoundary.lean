import DifferentialGeometry.Topology.Manifold.SmoothApproximation.Boundary.Applications

/-!
# LFR04 for half-space-modelled manifolds with empty boundary

`nonempty_diffeomorph_of_diffeomorph_of_boundary_eq_empty`: a `C^k` diffeomorphism (`1 ≤ k`)
between compact manifolds modelled on the half-space `𝓡∂ (n + 1)` whose source has empty boundary
yields a smooth diffeomorphism. (The boundaryless-MODEL case is W-1's
`nonempty_diffeomorph_of_diffeomorph`.) This is the `O = ∅` case of
`nonempty_diffeomorph_of_diffeomorph_smooth_near_boundary`; the general with-boundary LFR04 needs
in addition the collar straightening (see `build-logs/worker-W-2b.md`).
-/

set_option autoImplicit false

noncomputable section

open Set
open scoped Manifold ContDiff

namespace DifferentialGeometry.Topology.Manifold.SmoothApproximation

variable {n : ℕ}
  {A : Type*} [TopologicalSpace A] [ChartedSpace (EuclideanHalfSpace (n + 1)) A]
  [IsManifold (𝓡∂ (n + 1)) ∞ A] [T2Space A] [CompactSpace A]
  {B : Type*} [TopologicalSpace B] [ChartedSpace (EuclideanHalfSpace (n + 1)) B]
  [IsManifold (𝓡∂ (n + 1)) ∞ B]

/-- LFR04 when the source has empty boundary (half-space model, any `C^k`, `1 ≤ k`). -/
theorem nonempty_diffeomorph_of_diffeomorph_of_boundary_eq_empty {k : ℕ} (hk : 1 ≤ k)
    (h : A ≃ₘ^k⟮𝓡∂ (n + 1), 𝓡∂ (n + 1)⟯ B) (hb : (𝓡∂ (n + 1)).boundary A = ∅) :
    Nonempty (A ≃ₘ⟮𝓡∂ (n + 1), 𝓡∂ (n + 1)⟯ B) :=
  nonempty_diffeomorph_of_diffeomorph_smooth_near_boundary hk h isOpen_empty hb.subset
    contMDiffOn_empty

end DifferentialGeometry.Topology.Manifold.SmoothApproximation
