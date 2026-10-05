import DifferentialGeometry.Geometry.Connection.Hessian.Scalar
import DifferentialGeometry.Geometry.Comparison.Volume.BoundaryGeodesicContact
import Mathlib.Analysis.Convex.Deriv

/-!
A negative ambient covariant Hessian makes its defining function concave along actual
geodesics. Nonnegative endpoint values then keep the entire segment on the positive side.
-/

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set
open scoped Manifold ContDiff Topology
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Riemannian.Geodesic

namespace DifferentialGeometry.Geometry.Riemannian.VolumeComparison

variable {E : Type*} [ambientNorm : NormedAddCommGroup E]
  [ambientSpace : NormedSpace ℝ E] [ambientFinite : FiniteDimensional ℝ E]

theorem boundary_geodesic_concave (g : SmoothRiemannianMetric 𝓘(ℝ, E) E) (u : E → ℝ)
    (hu : ContDiff ℝ ∞ u) (γ : ℝ → E) (a b : ℝ)
    (hcont : ContinuousOn γ (Icc a b)) (hγ : ContDiffOn ℝ 2 γ (Ioo a b))
    (hgeo : IsGeodesicOn g γ (Ioo a b))
    (hH : ∀ t ∈ Ioo a b, ∀ v : E, v ≠ 0 → abstractHessian g u (γ t) v v < 0) :
    ConcaveOn ℝ (Icc a b) (u ∘ γ) := by
  have hu2 : ContDiff ℝ 2 u := hu.of_le (by simp)
  have hc2 : ContDiffOn ℝ 2 (u ∘ γ) (Ioo a b) :=
    hu2.contDiffOn.comp hγ (fun t ht => mem_univ (γ t))
  have hc1 : ContDiffOn ℝ 1 (deriv (u ∘ γ)) (Ioo a b) :=
    hc2.deriv_of_isOpen isOpen_Ioo (by norm_num)
  apply concaveOn_of_deriv2_nonpos (convex_Icc a b)
    (hu.continuous.comp_continuousOn hcont)
  · simpa only [interior_Icc] using hc2.differentiableOn (by norm_num)
  · simpa only [interior_Icc] using hc1.differentiableOn (by norm_num)
  · intro t ht
    rw [interior_Icc] at ht
    have hγt : ContDiffAt ℝ 2 γ t := (hγ t ht).contDiffAt (isOpen_Ioo.mem_nhds ht)
    have hscalar := abstractHessian_apply_velocity_of_hasGeodesicEquationAt g
      hu2.contDiffAt.contMDiffAt hγt.contMDiffAt BoundarylessManifold.isInteriorPoint (hgeo t ht)
    have hvelocity : mfderiv 𝓘(ℝ) 𝓘(ℝ, E) γ t
        ((NormedSpace.fromTangentSpace t).symm 1) = deriv γ t := by
      rw [mfderiv_eq_fderiv]
      change fderiv ℝ γ t 1 = deriv γ t
      exact fderiv_apply_one_eq_deriv
    dsimp only at hscalar
    rw [hvelocity] at hscalar
    have hn : abstractHessian g u (γ t) (deriv γ t) (deriv γ t) ≤ 0 := by
      by_cases hv : deriv γ t = 0
      · have hz : abstractHessian g u (γ t) (0 : E) (0 : E) = 0 := by
          exact congrArg (fun L : TangentSpace 𝓘(ℝ, E) (γ t) →L[ℝ] ℝ => L 0)
            (abstractHessian g u (γ t)).map_zero
        have heq := congrArg (fun v : E => abstractHessian g u (γ t) v v) hv
        exact (heq.trans hz).le
      · exact (hH t ht (deriv γ t) hv).le
    have hnonpos : iteratedDeriv 2 (u ∘ γ) t ≤ 0 := hscalar ▸ hn
    simpa only [iteratedDeriv_eq_iterate] using hnonpos

theorem boundary_geodesic_nonneg (g : SmoothRiemannianMetric 𝓘(ℝ, E) E) (u : E → ℝ)
    (hu : ContDiff ℝ ∞ u) (γ : ℝ → E) (a b : ℝ) (hab : a ≤ b)
    (hcont : ContinuousOn γ (Icc a b)) (hγ : ContDiffOn ℝ 2 γ (Ioo a b))
    (hgeo : IsGeodesicOn g γ (Ioo a b))
    (hH : ∀ t ∈ Ioo a b, ∀ v : E, v ≠ 0 → abstractHessian g u (γ t) v v < 0)
    (ha : 0 ≤ u (γ a)) (hb : 0 ≤ u (γ b)) : ∀ t ∈ Icc a b, 0 ≤ u (γ t) := by
  have hc := boundary_geodesic_concave g u hu γ a b hcont hγ hgeo hH
  have hsegment := (hc.convex_ge 0).segment_subset
    ⟨⟨le_rfl, hab⟩, ha⟩ ⟨⟨hab, le_rfl⟩, hb⟩
  intro t ht
  exact (hsegment (Icc_subset_segment ht)).2

theorem boundary_geodesic_pos (g : SmoothRiemannianMetric 𝓘(ℝ, E) E) (u : E → ℝ)
    (hu : ContDiff ℝ ∞ u) (γ : ℝ → E) (a b : ℝ) (hab : a ≤ b)
    (hcont : ContinuousOn γ (Icc a b)) (hγ : ContDiffOn ℝ 2 γ (Ioo a b))
    (hgeo : IsGeodesicOn g γ (Ioo a b))
    (hH : ∀ t ∈ Ioo a b, ∀ v : E, v ≠ 0 → abstractHessian g u (γ t) v v < 0)
    (hvel : ∀ t ∈ Ioo a b, deriv γ t ≠ 0)
    (ha : 0 ≤ u (γ a)) (hb : 0 ≤ u (γ b)) : ∀ t ∈ Ioo a b, 0 < u (γ t) := by
  have hnonneg := boundary_geodesic_nonneg g u hu γ a b hab hcont hγ hgeo hH ha hb
  intro t ht
  by_contra hn
  have hzero : u (γ t) = 0 :=
    le_antisymm (le_of_not_gt hn) (hnonneg t (Ioo_subset_Icc_self ht))
  have hinside : ∀ᶠ s in 𝓝 t, 0 ≤ u (γ s) := by
    filter_upwards [isOpen_Ioo.mem_nhds ht] with s hs
    exact hnonneg s (Ioo_subset_Icc_self hs)
  have hu2 : ContDiff ℝ 2 u := hu.of_le (by simp)
  have hγt := (hγ t ht).contDiffAt (isOpen_Ioo.mem_nhds ht)
  apply boundary_geodesic_zero_contact g u γ t hu2.contDiffAt hγt (hgeo t ht)
    hzero hinside (hvel t ht)
  intro v htangent hv
  exact hH t ht v hv

end DifferentialGeometry.Geometry.Riemannian.VolumeComparison
