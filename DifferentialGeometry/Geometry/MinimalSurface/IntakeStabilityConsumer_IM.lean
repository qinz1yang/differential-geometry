import DifferentialGeometry.Geometry.MinimalSurface.Stability.EveryAreaMinimizer

set_option autoImplicit false

noncomputable section

open DifferentialGeometry DifferentialGeometry.Topology Filter Set
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry.MinimalSurface

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]

/-- Consumer of the IMS03 stability kernel: along an ambient flow of diffeomorphisms that is the
identity outside the interior of the exterior and fixes the attaining disk at `t₀`, the actual
area has vanishing first derivative and nonnegative second derivative at `t₀`. -/
theorem area_derivative_tests_along_diffeo_flow_IM
    (g : SmoothRiemannianMetric (𝓡 3) M) {W : Set M} {γ : freeLoop M}
    {u : C(closedDisk, M)} (hu : isExteriorSpanningDisk W γ u)
    (harea : riemannianDiskArea g u = leastExteriorDiskArea g W γ)
    (Φ : ℝ → Diffeomorph (𝓡 3) (𝓡 3) M M ∞) {t₀ a b : ℝ}
    (hcenter : ∀ z : closedDisk, Φ t₀ (u z) = u z)
    (hsupport : ∀ᶠ t in 𝓝 t₀, EqOn (Φ t) id (interior W)ᶜ)
    (hfirst : HasDerivAt
      (fun t => riemannianDiskArea g ((⟨Φ t, (Φ t).continuous⟩ : C(M, M)).comp u)) a t₀)
    (hsecond : HasDerivAt (deriv
      (fun t => riemannianDiskArea g ((⟨Φ t, (Φ t).continuous⟩ : C(M, M)).comp u))) b t₀) :
    a = 0 ∧ 0 ≤ b := by
  have heq : (⟨Φ t₀, (Φ t₀).continuous⟩ : C(M, M)).comp u = u := by
    ext z
    exact hcenter z
  refine area_derivative_tests_of_attains_leastExteriorDiskArea g (W := W) (γ := γ)
    (v := fun t => (⟨Φ t, (Φ t).continuous⟩ : C(M, M)).comp u) (t₀ := t₀) ?_ ?_
    hfirst hsecond
  · simpa only [heq] using harea
  · filter_upwards [hsupport] with t ht
    exact hu.comp_diffeomorph_of_eqOn_compl_interior (Φ t) ht

end DifferentialGeometry.Geometry.MinimalSurface
