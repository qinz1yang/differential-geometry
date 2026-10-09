import DifferentialGeometry.Geometry.Connection.Hessian.Scalar
import DifferentialGeometry.Analysis.Calculus.LocalExtrema

/-!
An actual ambient geodesic with nonzero velocity cannot have an interior zero contact
with a tangent-negative smooth defining function while remaining on its positive side.
-/

set_option autoImplicit false

noncomputable section

open Manifold Filter
open scoped Manifold ContDiff Topology
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Riemannian.Geodesic

namespace DifferentialGeometry.Geometry.Riemannian.VolumeComparison

variable {E : Type*} [ambientNorm : NormedAddCommGroup E]
  [ambientSpace : NormedSpace ℝ E] [ambientFinite : FiniteDimensional ℝ E]

theorem boundary_geodesic_zero_contact (g : SmoothRiemannianMetric 𝓘(ℝ, E) E)
    (u : E → ℝ) (γ : ℝ → E) (t : ℝ) (hu : ContDiffAt ℝ 2 u (γ t))
    (hγ : ContDiffAt ℝ 2 γ t) (hgeo : HasGeodesicEquationAt g γ t)
    (hzero : u (γ t) = 0) (hinside : ∀ᶠ s in 𝓝 t, 0 ≤ u (γ s))
    (hvel : deriv γ t ≠ 0)
    (hneg : ∀ v : E, fderiv ℝ u (γ t) v = 0 → v ≠ 0 →
      abstractHessian g u (γ t) v v < 0) : False := by
  have hud : DifferentiableAt ℝ u (γ t) := hu.differentiableAt (by norm_num)
  have hγd : DifferentiableAt ℝ γ t := hγ.differentiableAt (by norm_num)
  have hder : HasDerivAt (u ∘ γ) (fderiv ℝ u (γ t) (deriv γ t)) t :=
    hud.hasFDerivAt.comp_hasDerivAt t hγd.hasDerivAt
  have hmin : IsLocalMin (u ∘ γ) t := by
    filter_upwards [hinside] with s hs
    simpa only [Function.comp_apply, hzero] using hs
  have htangent : fderiv ℝ u (γ t) (deriv γ t) = 0 :=
    hmin.hasDerivAt_eq_zero hder
  have hH := abstractHessian_apply_velocity_of_hasGeodesicEquationAt g
    hu.contMDiffAt hγ.contMDiffAt BoundarylessManifold.isInteriorPoint hgeo
  have hvelocity : mfderiv 𝓘(ℝ) 𝓘(ℝ, E) γ t
      ((NormedSpace.fromTangentSpace t).symm 1) = deriv γ t := by
    rw [mfderiv_eq_fderiv]
    change fderiv ℝ γ t 1 = deriv γ t
    exact fderiv_apply_one_eq_deriv
  dsimp only at hH
  rw [hvelocity] at hH
  have hsecond : deriv (deriv (u ∘ γ)) t < 0 := by
    have hn := hneg (deriv γ t) htangent hvel
    rw [hH] at hn
    simpa only [iteratedDeriv_succ, iteratedDeriv_one, iteratedDeriv_zero] using hn
  have hmax := hmin.neg.deriv_deriv_nonpos hder.continuousAt.neg
  have hinner : deriv (fun s => -(u ∘ γ) s) = fun s => -deriv (u ∘ γ) s := by
    funext s
    exact deriv.neg
  have houter : deriv (fun s => -deriv (u ∘ γ) s) t =
      -deriv (deriv (u ∘ γ)) t := deriv.neg
  rw [hinner, houter] at hmax
  linarith

end DifferentialGeometry.Geometry.Riemannian.VolumeComparison
