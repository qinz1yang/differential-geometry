import DifferentialGeometry.Geometry.Connection.ParallelTransport.Derivative.CovariantDerivativeAlong

noncomputable section

open Manifold
open scoped ContDiff

namespace DifferentialGeometry.Geometry.Riemannian

open AlongCurve CovariantDerivativeAlong

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

theorem covDeriv_comp_affine
    (g : SmoothRiemannianMetric I M) (γ : ℝ → M)
    (V : ∀ t, TangentSpace I (γ t)) (c d t : ℝ) :
    covDerivAlong (I := I) g
        (fun s => γ (c * s + d)) (fun s => V (c * s + d)) t =
      c • covDerivAlong (I := I) g γ V (c * t + d) := by
  rw [covDerivAlong_def, covDerivAlong_def]
  rw [← map_smul]
  congr 1
  have hrep :
      chartRepAt (I := I) (fun s => γ (c * s + d))
          (fun s => V (c * s + d)) t =
        fun s => chartRepAt (I := I) γ V (c * t + d) (c * s + d) := rfl
  have hcurve :
      chartCurve (I := I) (γ (c * t + d)) (fun s => γ (c * s + d)) =
        fun s => chartCurve (I := I) (γ (c * t + d)) γ (c * s + d) := rfl
  rw [hrep, chartCovDerivAlong_def, chartCovDerivAlong_def, hcurve]
  have hderiv (f : ℝ → E) :
      deriv (fun s => f (c * s + d)) t = c • deriv f (c * t + d) := by
    calc
      deriv (fun s => f (c * s + d)) t =
          deriv (fun s => (fun r => f (r + d)) (c * s)) t := rfl
      _ = c • deriv (fun r => f (r + d)) (c * t) :=
        deriv_comp_mul_left c (fun r : ℝ => f (r + d)) t
      _ = c • deriv f (c * t + d) := by rw [deriv_comp_add_const]
  rw [hderiv, hderiv,
    ChartChristoffel.contraction_smul_left, smul_add]

namespace Variation

noncomputable def curveVelocity (γ : ℝ → M) (t : ℝ) : TangentSpace I (γ t) :=
  mfderiv (𝓘(ℝ, ℝ)) I γ t (1 : ℝ)

end Variation

open Variation

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] in
theorem curveVelocity_comp_affine
    (γ : ℝ → M) (c d t : ℝ)
    (hγ : MDifferentiableAt 𝓘(ℝ, ℝ) I γ (c * t + d)) :
    curveVelocity (I := I) (fun s => γ (c * s + d)) t =
      c • curveVelocity (I := I) γ (c * t + d) := by
  let a : ℝ → ℝ := fun s => c * s + d
  have ha : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) a t := by
    have ha_inf : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ a := by
      exact contMDiff_const.mul contMDiff_id |>.add contMDiff_const
    exact ha_inf.contMDiffAt.mdifferentiableAt (by simp)
  have hcomp :=
    mfderiv_comp_apply (f := a) (g := γ) (x := t) hγ ha (1 : ℝ)
  have ha_one : mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) a t (1 : ℝ) = c := by
    rw [mfderiv_eq_fderiv]
    have hfd : HasFDerivAt a (c • (1 : ℝ →L[ℝ] ℝ)) t := by
      have hadd : HasFDerivAt a
          ((c • (1 : ℝ →L[ℝ] ℝ)) + (0 : ℝ →L[ℝ] ℝ)) t := by
        change HasFDerivAt (fun s : ℝ => c * s + d)
          ((c • (1 : ℝ →L[ℝ] ℝ)) + (0 : ℝ →L[ℝ] ℝ)) t
        refine HasFDerivAt.add ?_ (hasFDerivAt_const (x := t) d)
        refine ((c • (1 : ℝ →L[ℝ] ℝ)).hasFDerivAt
          (x := t)).congr_of_eventuallyEq ?_
        filter_upwards with s
        simp only [smul_apply, one_apply_eq_self, smul_eq_mul]
      rw [add_zero] at hadd
      exact hadd
    rw [hfd.fderiv]
    change c • ((1 : ℝ →L[ℝ] ℝ) (1 : ℝ)) = c
    rw [one_apply_eq_self, smul_eq_mul, mul_one]
  change mfderiv 𝓘(ℝ, ℝ) I (γ ∘ a) t (1 : ℝ) =
    c • mfderiv 𝓘(ℝ, ℝ) I γ (a t) (1 : ℝ)
  rw [hcomp, ha_one]
  let A := mfderiv 𝓘(ℝ, ℝ) I γ (a t)
  have hA : A
        ((tangentSpaceModelContinuousLinearEquiv
          (I := 𝓘(ℝ, ℝ)) (a t)).symm c) =
      c • A
        ((tangentSpaceModelContinuousLinearEquiv
          (I := 𝓘(ℝ, ℝ)) (a t)).symm 1) := by
    rw [← A.map_smul]
    congr 1
    apply (tangentSpaceModelContinuousLinearEquiv
      (I := 𝓘(ℝ, ℝ)) (a t)).injective
    simp
  with_unfolding_all exact hA

end DifferentialGeometry.Geometry.Riemannian
