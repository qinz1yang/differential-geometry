import DifferentialGeometry.Geometry.MinimalSurface.Plateau.Regularity.BoundaryTraceInjectivity
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.Regularity.InteriorBranchExclusion
import DifferentialGeometry.Geometry.MinimalSurface.FixedBoundary.InducedDiskMetric

set_option autoImplicit false

noncomputable section

open Set Metric
open DifferentialGeometry DifferentialGeometry.Topology
open scoped Manifold ContDiff

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

/-- Consumer of the IMS03 boundary-trace kernels: boundary rank and interior separation make the
weakly monotone boundary phase injective and every boundary fiber a singleton. -/
theorem boundary_phase_injective_and_fibers_singleton_IM
    {γ : freeLoop M} {q : C(closedDisk, M)} {Q : ℂ → M}
    (hQ : SmoothDiskExtension (E := E) q Q)
    (hγ : IsSmoothEmbeddedLoop (E := E) γ)
    {σ : C(loopCircle, loopCircle)} (hσ : IsWeaklyMonotoneOnce σ)
    (htrace : diskTrace q = γ.comp σ)
    (hrank : ∀ z ∈ sphere (0 : ℂ) 1,
      Function.Injective (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) Q z))
    (hseparate : ∀ z : closedDisk, ‖(z : ℂ)‖ < 1 → ∀ θ : loopCircle, q z ≠ γ θ) :
    Function.Injective σ ∧
      ∀ (θ : loopCircle) (z : closedDisk), q z = q (diskBoundary θ) → z = diskBoundary θ :=
  ⟨hQ.injective_boundary_phase hγ hσ htrace hrank,
    hQ.boundary_fiber_eq hγ hσ htrace hrank hseparate⟩

/-- Consumer of the induced-metric kernel: a rank-one-immersed smooth disk extension carries the
pullback metric of the ambient metric on an open neighborhood of the closed disk. -/
theorem exists_open_pullback_neighborhood_IM
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    {u : C(closedDisk, M)} {U : ℂ → M} (hU : SmoothDiskExtension (E := E) u U)
    (himm : ∀ z ∈ closedBall (0 : ℂ) 1,
      Function.Injective (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U z)) :
    ∃ N : TopologicalSpace.Opens ℂ, closedBall (0 : ℂ) 1 ⊆ N := by
  obtain ⟨N, _, _, hN, _⟩ := hU.exists_pullback_metric_neighborhood g himm
  exact ⟨N, hN⟩

/-- Consumer of the interior-branch lemma: a weakly monotone factor of an embedded loop has
degree one or minus one. -/
theorem factor_degree_one_or_neg_one_IM
    {γ : freeLoop M} {u : C(closedDisk, M)} (hu : DiskWeakJordanTrace γ u)
    (hγ : Function.Injective γ) {τ ρ : C(loopCircle, loopCircle)}
    (hfactor : diskTrace u = (γ.comp τ).comp ρ) (F : C(ℝ, ℝ)) (n : ℤ)
    (hlift : ∀ t : ℝ, (F t : loopCircle) = ρ (t : loopCircle))
    (hshift : ∀ t : ℝ, F (t + 1) = F t + (n : ℝ)) : n = 1 ∨ n = -1 :=
  hu.integer_shift_eq_one_or_neg_one_of_factor hγ hfactor F n hlift hshift

end DifferentialGeometry.Geometry
