import DifferentialGeometry.Analysis.Calculus.SecondDerivative.Minimum
import DifferentialGeometry.Geometry.MinimalSurface.FixedBoundary.ExteriorCompetitors

set_option autoImplicit false
noncomputable section

open DifferentialGeometry DifferentialGeometry.Topology Filter Set
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry.MinimalSurface

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]

/-- Attainment of the actual exterior disk infimum gives a local minimum along
every variation that remains in the same fixed-boundary competitor class. -/
theorem isLocalMin_area_of_attains_leastExteriorDiskArea
    (g : SmoothRiemannianMetric (𝓡 3) M) {W : Set M} {γ : freeLoop M}
    {v : ℝ → C(closedDisk, M)} {t₀ : ℝ}
    (harea : riemannianDiskArea g (v t₀) = leastExteriorDiskArea g W γ)
    (hv : ∀ᶠ t in 𝓝 t₀, isExteriorSpanningDisk W γ (v t)) :
    IsLocalMin (fun t => riemannianDiskArea g (v t)) t₀ := by
  filter_upwards [hv] with t ht
  rw [harea]
  exact leastExteriorDiskArea_le g W γ (v t) ht

/-- Every attaining exterior disk satisfies the first and second derivative
tests along any admissible variation whose actual area derivatives exist.
Identifying these derivatives with geometric variation formulas is separate. -/
theorem area_derivative_tests_of_attains_leastExteriorDiskArea
    (g : SmoothRiemannianMetric (𝓡 3) M) {W : Set M} {γ : freeLoop M}
    {v : ℝ → C(closedDisk, M)} {t₀ a b : ℝ}
    (harea : riemannianDiskArea g (v t₀) = leastExteriorDiskArea g W γ)
    (hv : ∀ᶠ t in 𝓝 t₀, isExteriorSpanningDisk W γ (v t))
    (hfirst : HasDerivAt (fun t => riemannianDiskArea g (v t)) a t₀)
    (hsecond : HasDerivAt (deriv (fun t => riemannianDiskArea g (v t))) b t₀) :
    a = 0 ∧ 0 ≤ b := by
  have hmin := isLocalMin_area_of_attains_leastExteriorDiskArea g harea hv
  refine ⟨hmin.hasDerivAt_eq_zero hfirst, ?_⟩
  rw [← hsecond.deriv]
  exact Analysis.second_deriv_nonneg_of_isLocalMin hmin hfirst.continuousAt

/-- Ambient diffeomorphisms supported in the exterior's interior test every
attaining disk without choosing a preferred minimizer. The support condition
ensures preservation of the exterior and the exact boundary curve. -/
theorem isLocalMin_area_comp_diffeomorph_of_attains_leastExteriorDiskArea
    (g : SmoothRiemannianMetric (𝓡 3) M) {W : Set M} {γ : freeLoop M}
    {u : C(closedDisk, M)} (hu : isExteriorSpanningDisk W γ u)
    (harea : riemannianDiskArea g u = leastExteriorDiskArea g W γ)
    (Φ : ℝ → Diffeomorph (𝓡 3) (𝓡 3) M M ∞) {t₀ : ℝ}
    (hcenter : ∀ z : closedDisk, Φ t₀ (u z) = u z)
    (hsupport : ∀ᶠ t in 𝓝 t₀, EqOn (Φ t) id (interior W)ᶜ) :
    IsLocalMin
      (fun t => riemannianDiskArea g ((⟨Φ t, (Φ t).continuous⟩ : C(M, M)).comp u)) t₀ := by
  apply isLocalMin_area_of_attains_leastExteriorDiskArea g
  · have heq : ((⟨Φ t₀, (Φ t₀).continuous⟩ : C(M, M)).comp u) = u := by
      ext z
      exact hcenter z
    simpa only [heq] using harea
  · filter_upwards [hsupport] with t ht
    exact hu.comp_diffeomorph_of_eqOn_compl_interior (Φ t) ht

end DifferentialGeometry.Geometry.MinimalSurface
