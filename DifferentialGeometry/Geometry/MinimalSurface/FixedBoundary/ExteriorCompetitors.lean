import DifferentialGeometry.Geometry.MinimalSurface.ExteriorDiskArea
import Mathlib.Geometry.Manifold.LocalDiffeomorph

set_option autoImplicit false
noncomputable section

open DifferentialGeometry DifferentialGeometry.Topology Set
open scoped Manifold ContDiff

namespace DifferentialGeometry.Geometry.MinimalSurface

variable {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) N]

/-- Ambient diffeomorphisms transport the actual exterior disk class, including
its prescribed boundary parameterization and immersion through the boundary. -/
theorem isExteriorSpanningDisk.comp_diffeomorph
    {W : Set M} {γ : freeLoop M} {u : C(closedDisk, M)}
    (hu : isExteriorSpanningDisk W γ u) (Φ : Diffeomorph (𝓡 3) (𝓡 3) M N ∞) :
    isExteriorSpanningDisk (Φ '' W) ((⟨Φ, Φ.continuous⟩ : C(M, N)).comp γ)
      ((⟨Φ, Φ.continuous⟩ : C(M, N)).comp u) := by
  rcases hu with ⟨htrace, hfrontier, hemb, hrange, hint, U, hU, himm⟩
  refine ⟨?_, ?_, Φ.toHomeomorph.isEmbedding.comp hemb, ?_, ?_, Φ ∘ U,
    hU.comp ⟨Φ, Φ.continuous⟩ Φ.contMDiff, ?_⟩
  · ext θ
    change Φ (u (diskBoundary θ)) = Φ (γ θ)
    exact congrArg Φ (congrArg (fun f : freeLoop M => f θ) htrace)
  · rintro _ ⟨θ, rfl⟩
    have hΦfrontier : Φ '' frontier W = frontier (Φ '' W) :=
      Φ.toHomeomorph.image_frontier W
    rw [← hΦfrontier]
    exact mem_image_of_mem Φ (hfrontier (mem_range_self θ))
  · rintro _ ⟨z, rfl⟩
    exact mem_image_of_mem Φ (hrange (mem_range_self z))
  · intro z hz
    have hΦinterior : Φ '' interior W = interior (Φ '' W) :=
      Φ.toHomeomorph.image_interior W
    rw [← hΦinterior]
    exact mem_image_of_mem Φ (hint z hz)
  · intro z hz
    rw [mfderiv_comp (I' := 𝓡 3)]
    · change Function.Injective
        ((mfderiv (𝓡 3) (𝓡 3) Φ (U z)) ∘ (mfderiv 𝓘(ℝ, ℂ) (𝓡 3) U z))
      exact (Φ.mfderivToContinuousLinearEquiv (by simp) (U z)).injective.comp (himm z hz)
    · exact Φ.mdifferentiable (by simp) (U z)
    · obtain ⟨_, V, hV, hDV, hUs⟩ := hU
      exact (hUs.contMDiffAt (hV.mem_nhds (hDV hz))).mdifferentiableAt (by simp)

/-- A diffeomorphism preserving the exterior and fixing the boundary curve
pointwise gives an admissible fixed-boundary competitor. -/
theorem isExteriorSpanningDisk.comp_diffeomorph_of_fixed_boundary
    {W : Set M} {γ : freeLoop M} {u : C(closedDisk, M)}
    (hu : isExteriorSpanningDisk W γ u) (Φ : Diffeomorph (𝓡 3) (𝓡 3) M M ∞)
    (hW : Φ '' W = W) (hγ : ∀ θ, Φ (γ θ) = γ θ) :
    isExteriorSpanningDisk W γ ((⟨Φ, Φ.continuous⟩ : C(M, M)).comp u) := by
  have htrace : (⟨Φ, Φ.continuous⟩ : C(M, M)).comp γ = γ := by
    ext θ
    exact hγ θ
  simpa only [hW, htrace] using hu.comp_diffeomorph Φ

/-- Ambient diffeomorphisms supported inside the exterior interior preserve the
fixed-boundary competitor class. No separate region or boundary law is needed. -/
theorem isExteriorSpanningDisk.comp_diffeomorph_of_eqOn_compl_interior
    {W : Set M} {γ : freeLoop M} {u : C(closedDisk, M)}
    (hu : isExteriorSpanningDisk W γ u) (Φ : Diffeomorph (𝓡 3) (𝓡 3) M M ∞)
    (hΦ : Set.EqOn Φ id (interior W)ᶜ) :
    isExteriorSpanningDisk W γ ((⟨Φ, Φ.continuous⟩ : C(M, M)).comp u) := by
  apply hu.comp_diffeomorph_of_fixed_boundary Φ
  · have hfix : Set.EqOn Φ id Wᶜ := by
      intro x hx
      exact hΦ (fun hxi => hx (interior_subset hxi))
    apply compl_injective
    calc
      (Φ '' W)ᶜ = Φ '' Wᶜ := (Φ.toHomeomorph.image_compl W).symm
      _ = Wᶜ := hfix.image_eq_self
  · intro θ
    exact hΦ (hu.2.1 (mem_range_self θ)).2

end DifferentialGeometry.Geometry.MinimalSurface
