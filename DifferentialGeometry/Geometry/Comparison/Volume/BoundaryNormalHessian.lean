import DifferentialGeometry.Geometry.Comparison.Volume.BoundaryDefiningHessian

/-!
The defining-function Hessian is expressed through an actual covariant normal derivative,
by differentiating its cooriented metric-dual covector using native metric compatibility.
-/

set_option autoImplicit false

noncomputable section

open Bundle Manifold
open scoped Manifold ContDiff Topology
open DifferentialGeometry.Geometry.Connection

namespace DifferentialGeometry.Geometry.Riemannian.VolumeComparison

variable {E : Type*} [ambientNorm : NormedAddCommGroup E]
  [ambientSpace : NormedSpace ℝ E] [ambientFinite : FiniteDimensional ℝ E]

attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace in
theorem boundary_normal_hessian
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) E) (u a : E → ℝ)
    (ν : ∀ x : E, TangentSpace 𝓘(ℝ, E) x) (p : E)
    (hu : ContDiff ℝ ∞ u) (ha : ContDiff ℝ ∞ a)
    (hν : MDifferentiableAt 𝓘(ℝ, E) (𝓘(ℝ, E).prod 𝓘(ℝ, E))
      (fun x => (⟨x, ν x⟩ : TangentBundle 𝓘(ℝ, E) E)) p)
    (hdual : ∀ᶠ x in 𝓝 p, mvfderiv 𝓘(ℝ, E) u x = (-a x) • metricFlat g ν x)
    (v w : E) :
    abstractHessian g u p v w =
      -mvfderiv 𝓘(ℝ, E) a p v * g.inner p (ν p) w -
        a p * g.inner p (LeviCivita g ν p v) w := by
  let D := cotangentCov (LeviCivita g)
  have hdu : MDiffAtCotangent (mvfderiv 𝓘(ℝ, E) u) p :=
    (cotangentCov_mvfderiv_smooth hu.contMDiff p).mdifferentiableAt (by simp)
  have hflat : MDiffAtCotangent (metricFlat g ν) p := metricFlat_mdiff g hν
  have hna : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ) (fun x => -a x) p :=
    ha.neg.contMDiff.mdifferentiableAt (by simp)
  have hscaled : MDiffAtCotangent ((fun x => -a x) • metricFlat g ν) p :=
    hna.smul_section hflat
  have hcongr := D.isCovariantDerivativeOnUniv.congr_of_eventuallyEq hdu hscaled
    Filter.univ_mem hdual
  have hD := D.isCovariantDerivativeOnUniv.leibniz hflat hna
  have hda : mvfderiv 𝓘(ℝ, E) (fun x => -a x) p = -mvfderiv 𝓘(ℝ, E) a p :=
    mvfderiv_neg
  let vT : TangentSpace 𝓘(ℝ, E) p := v
  let wT : TangentSpace 𝓘(ℝ, E) p := w
  have hcalc := congrArg
    (fun B : TangentSpace 𝓘(ℝ, E) p →L[ℝ] TangentSpace 𝓘(ℝ, E) p →L[ℝ] ℝ => B vT wT)
    (hcongr.trans hD)
  rw [hda] at hcalc
  simp only [add_apply, smul_apply, ContinuousLinearMap.smulRight_apply,
    neg_apply, smul_eq_mul, metricFlat_apply] at hcalc
  have hduality := cotangentCov_metricDuality g hν vT wT
  change D (metricFlat g ν) p vT wT = _ at hduality
  rw [hduality] at hcalc
  exact hcalc.trans (by dsimp only [vT, wT]; ring)

attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace in
theorem boundary_hessian_negative_of_normal_derivative
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) E) (u a : E → ℝ)
    (ν : ∀ x : E, TangentSpace 𝓘(ℝ, E) x) (p : E)
    (hu : ContDiff ℝ ∞ u) (ha : ContDiff ℝ ∞ a)
    (hν : MDifferentiableAt 𝓘(ℝ, E) (𝓘(ℝ, E).prod 𝓘(ℝ, E))
      (fun x => (⟨x, ν x⟩ : TangentBundle 𝓘(ℝ, E) E)) p)
    (hdual : ∀ᶠ x in 𝓝 p, mvfderiv 𝓘(ℝ, E) u x = (-a x) • metricFlat g ν x)
    (hapos : 0 < a p)
    (hII : ∀ v : E, fderiv ℝ u p v = 0 → v ≠ 0 →
      0 < g.inner p (LeviCivita g ν p v) v) :
    ∀ v : E, fderiv ℝ u p v = 0 → v ≠ 0 → abstractHessian g u p v v < 0 := by
  intro v htangent hv
  have hmv : mvfderiv 𝓘(ℝ, E) u p v = fderiv ℝ u p v := by
    unfold mvfderiv
    rw [mfderiv_eq_fderiv]
    rfl
  have hpdual : mvfderiv 𝓘(ℝ, E) u p = (-a p) • metricFlat g ν p :=
    Filter.Eventually.self_of_nhds
      (p := fun x : E => mvfderiv 𝓘(ℝ, E) u x = (-a x) • metricFlat g ν x) (x := p) hdual
  have hpair := congrArg (fun B : TangentSpace 𝓘(ℝ, E) p →L[ℝ] ℝ => B v) hpdual
  have horth : g.inner p (ν p) v = 0 := by
    change mvfderiv 𝓘(ℝ, E) u p v = -a p * g.inner p (ν p) v at hpair
    rw [hmv, htangent] at hpair
    exact (mul_eq_zero.mp hpair.symm).resolve_left (neg_ne_zero.mpr hapos.ne')
  have hformula := boundary_normal_hessian g u a ν p hu ha hν hdual v v
  rw [horth, mul_zero, zero_sub] at hformula
  rw [hformula]
  exact neg_neg_of_pos (mul_pos hapos (hII v htangent hv))

end DifferentialGeometry.Geometry.Riemannian.VolumeComparison
