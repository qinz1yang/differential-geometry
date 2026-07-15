import DifferentialGeometry.Geometry.Exponential.JacobiVariation

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Nonsingularity of `d exp` from radial Jacobi nonvanishing (Step A item 3a)

The reduction that turns the covariant-Grönwall conclusion `J_w(1) ≠ 0`
(`Variation/CovariantGronwall.lean:covGronwall_ne_zero`, instantiated on the radial
Jacobi field) into injectivity of `d(exp_p)_x` — the `hloc` input that
`Comparison/ExpBallDiffeo.lean:exists_expBall_diffeo` needs for the Step A item-3a
ball diffeomorphism.

* `injective_of_ball_ne_zero` — a continuous linear map nonzero on a punctured ball
  around `0` is injective (a linear kernel meeting every neighbourhood of `0`).
* `mfderiv_exp_injective_of_jacobi` — if the radial Jacobi field `J_w` (the variation
  field of `s ↦ exp_p((x+s·w))`) has `J_w(1) ≠ 0` for all small `w ≠ 0`, then
  `d(exp_p)_x` is injective.  The endpoint identification `J_w(1) = d(exp_p)_x w` is
  `radial_jacobi_one`.
-/

noncomputable section

open Set Function Manifold Bundle
open scoped Topology Manifold ContDiff

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian

open DifferentialGeometry.Geometry.Riemannian.Exponential

section LinearAlgebra

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A continuous linear map that is nonzero at every point of a punctured ball around
`0` is injective: its kernel is a subspace, so if it were nontrivial it would contain
arbitrarily small nonzero vectors, contradicting nonvanishing on the ball. -/
theorem injective_of_ball_ne_zero (L : E →L[ℝ] F) {r : ℝ} (hr : 0 < r)
    (h : ∀ w : E, 0 < ‖w‖ → ‖w‖ < r → L w ≠ 0) : Function.Injective L := by
  rw [injective_iff_map_eq_zero L]
  intro w hw
  by_contra hne
  have hwpos : 0 < ‖w‖ := norm_pos_iff.mpr hne
  set c : ℝ := r / (2 * ‖w‖) with hc
  have hcpos : 0 < c := by rw [hc]; positivity
  have hnorm : ‖c • w‖ = r / 2 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hcpos, hc]
    field_simp
  refine h (c • w) ?_ ?_ ?_
  · rw [hnorm]; positivity
  · rw [hnorm]; linarith
  · rw [map_smul]
    show c • L w = 0
    rw [hw, smul_zero]

end LinearAlgebra

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [InnerProductSpace ℝ E] [Module.Finite ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [I.Boundaryless] [CompleteSpace E] [T2Space (TangentBundle I M)]
  [T2Space M] [SigmaCompactSpace M]

/-- **`d exp` is injective from radial Jacobi nonvanishing (Step A item 3a heart).**
If for every small `w ≠ 0` the radial Jacobi field of `exp_p` at `x` is nonzero at the
endpoint `v = 1`, then the vector-slot differential `d(exp_p)_x` is injective.

The hypothesis `hjac` is exactly what `covGronwall_ne_zero` produces once the radial
regularity, the curvature-norm bound, and the Grönwall smallness are supplied; the
endpoint identification `J_w(1) = d(exp_p)_x w` is `radial_jacobi_one`. -/
theorem mfderiv_exp_injective_of_jacobi
    (g : SmoothRiemannianMetric I M) (p : M) {x : E}
    (hx : ‖x‖ < expMapC2Radius (I := I) g p) {r : ℝ} (hr : 0 < r)
    (hjac : ∀ w : E, 0 < ‖w‖ → ‖w‖ < r →
      mfderiv (𝓘(ℝ, ℝ)) I (fun s : ℝ =>
        (expMap (I := I) g p (show TangentSpace I p from ((1 : ℝ) • (x + s • w))) : M))
        0 (1 : ℝ) ≠ 0) :
    Function.Injective
      (mfderiv (𝓘(ℝ, E)) I
        (fun b : E => (expMap (I := I) g p (show TangentSpace I p from b) : M)) x) := by
  refine injective_of_ball_ne_zero _ hr (fun w hw0 hwr => ?_)
  rw [← radial_jacobi_one (I := I) g p x w hx]
  exact hjac w hw0 hwr

end Riemannian
end Geometry
end DifferentialGeometry
