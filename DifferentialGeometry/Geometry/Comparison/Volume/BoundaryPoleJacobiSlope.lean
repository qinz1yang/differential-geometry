import DifferentialGeometry.Geometry.Comparison.Volume.BoundaryPoleJacobiFrame

/-!
The actual pole velocity derivative has ordinary derivative equal to its initial direction.
Its positive-time divided field therefore converges to that direction without a limit premise.
-/

set_option autoImplicit false

noncomputable section

open Bundle Filter Manifold Set
open scoped Manifold ContDiff Topology
open DifferentialGeometry.Geometry.Riemannian.Variation
open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong
open DifferentialGeometry.Geometry.Riemannian.AlongCurve

namespace DifferentialGeometry.Geometry.Riemannian.VolumeComparison

variable {E : Type*} [ambientNorm : NormedAddCommGroup E]
  [ambientSpace : NormedSpace ℝ E] [ambientFinite : FiniteDimensional ℝ E]

theorem boundaryPoleJacobiLinear_hasDerivAt_zero
    (G : SmoothRiemannianMetric 𝓘(ℝ, E) E) (y v w : E) :
    HasDerivAt (fun t => boundaryPoleJacobiLinear G y v t w) w 0 := by
  let γ := boundaryPoleFlowFamily G y v
  let J : ∀ t : ℝ, TangentSpace 𝓘(ℝ, E) (γ t) :=
    fun t => boundaryPoleJacobiLinear G y v t w
  have ht := G.mem_geodesicFlowDomain_zero (r := ⊤) le_top
    (⟨y, v⟩ : TangentBundle 𝓘(ℝ, E) E)
  have hfield : ContMDiffAt 𝓘(ℝ) (𝓘(ℝ, E)).tangent 2
      (fun t => (⟨γ t, J t⟩ : TangentBundle 𝓘(ℝ, E) E)) 0 :=
    (boundaryPoleJacobiLinear_jacobi G y v w 0 ht).2.of_le (by norm_num)
  have hrep : chartRepAt (I := 𝓘(ℝ, E)) γ J 0 =
      (fun t => boundaryPoleJacobiLinear G y v t w) := by
    funext t
    rw [chartRepAt_apply, TangentBundle.continuousLinearMapAt_model_space]
    rfl
  have hdiff := differentiableAt_chartRepAt_of_contMDiffAt_two hfield
  rw [hrep] at hdiff
  have hinit := boundaryPoleJacobiLinear_initial G y v w
  have hcoord := covDerivAlong_chartCoord G γ J 0
  rw [TangentBundle.continuousLinearMapAt_model_space] at hcoord
  change (covDerivAlong G γ J 0 : E) = chartCovDerivAlong G (γ 0) γ
    (chartRepAt (I := 𝓘(ℝ, E)) γ J 0) 0 at hcoord
  rw [chartCovDerivAlong_def, hrep] at hcoord
  dsimp only at hcoord
  rw [hinit.1, ChartChristoffel.contraction_zero_right, add_zero] at hcoord
  have hcov : covDerivAlong G γ J 0 = w := hinit.2
  rw [hcov] at hcoord
  exact hdiff.hasDerivAt.congr_deriv hcoord.symm

theorem boundaryPoleJacobiLinear_div_tendsto
    (G : SmoothRiemannianMetric 𝓘(ℝ, E) E) (y v w : E) :
    Tendsto (fun t : ℝ => t⁻¹ • boundaryPoleJacobiLinear G y v t w)
      (𝓝[>] (0 : ℝ)) (𝓝 w) := by
  have hs := (hasDerivAt_iff_tendsto_slope).mp
    (boundaryPoleJacobiLinear_hasDerivAt_zero G y v w)
  have hfun : slope (fun t => boundaryPoleJacobiLinear G y v t w) 0 =
      (fun t : ℝ => t⁻¹ • boundaryPoleJacobiLinear G y v t w) := by
    funext t
    rw [slope_def_module, (boundaryPoleJacobiLinear_initial G y v w).1, sub_zero, sub_zero]
  rw [hfun] at hs
  exact hs.mono_left (nhdsWithin_mono 0 (fun x hx => ne_of_gt hx))

end DifferentialGeometry.Geometry.Riemannian.VolumeComparison
