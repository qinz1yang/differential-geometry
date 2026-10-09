import DifferentialGeometry.Geometry.Fibration.ManifoldBlockDerivative
import DifferentialGeometry.Geometry.Collapse.FiniteSurface.VerticalDerivativeBridge

/-!
# Consumers of FC02 on a manifold

* `norm_mvfderiv_scaleBlock_le`: the scale block `(0, ρ)` has derivative at most `Λν` once
  `|dρ(v)| ≤ Λν`.
* `norm_mvfderiv_scaleBlock_le_riemannian`: on a complete Riemannian manifold whose distance is the
  Riemannian distance, a `Λ`-Lipschitz scale gives the scale block's Riemannian bound
  `‖d(0, ρ)(v)‖ ≤ Λ √(g_x(v, v))` (the `Λ` term of FC02/CGP02 in the physical norm).
-/

set_option autoImplicit false

noncomputable section

open Set Filter Function
open scoped Topology Manifold ContDiff

namespace DifferentialGeometry.Geometry.Collapse

section General

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W]

/-- The scale block `(0, ρ)` (cutoff `1`, coordinate `0`) has derivative at most `Λν` at `v` once
`|dρ(v)| ≤ Λν`. -/
theorem norm_mvfderiv_scaleBlock_le {ρ : M → ℝ} {x : M} (hρ : MDifferentiableAt I 𝓘(ℝ, ℝ) ρ x)
    (hρ0 : 0 ≤ ρ x) (v : TangentSpace I x) {Λ ν : ℝ} (hl : |mvfderiv I ρ x v| ≤ Λ * ν) :
    ‖mvfderiv I (fun y => WithLp.toLp 2 ((ρ y * 1) • (0 : W), ρ y * 1)) x v‖ ≤ Λ * ν := by
  have h0 : mvfderiv I (fun _ : M => (0 : W)) x v = 0 := by
    rw [mvfderiv_const]
    rfl
  have h1 : mvfderiv I (fun _ : M => (1 : ℝ)) x v = 0 := by
    rw [mvfderiv_const]
    rfl
  have h := norm_mvfderiv_block_apply_le (R := ρ) (ζ := fun _ => (1 : ℝ))
    (η := fun _ => (0 : W)) hρ mdifferentiableAt_const mdifferentiableAt_const v (ν := ν)
    (a := 0) (b := 0) (C := 0) (l := Λ) hρ0 (by norm_num) (by simp)
    (by rw [h0, norm_zero, mul_zero, zero_mul]) (by rw [h1, abs_zero, mul_zero, zero_mul]) hl
  have he : (0 + (0 + 1) * (0 + Λ)) * ν = Λ * ν := by ring
  rw [he] at h
  exact h

end General

section Riemannian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [CompleteSpace M]
  {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W]

/-- **The scale block in the Riemannian norm**: for a `Λ`-Lipschitz scale on a complete Riemannian
manifold (distance = Riemannian distance), `‖d(0, ρ)(v)‖ ≤ Λ √(g_x(v, v))`. -/
theorem norm_mvfderiv_scaleBlock_le_riemannian (g : SmoothRiemannianMetric I M)
    (hmetric : ∀ a b : M, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)) {ρ : M → ℝ}
    {Λ : ℝ} (hΛ : 0 ≤ Λ) (hρL : LipschitzWith (Real.toNNReal Λ) ρ) {x : M}
    (hρ : MDifferentiableAt I 𝓘(ℝ, ℝ) ρ x) (hρ0 : 0 ≤ ρ x) (v : TangentSpace I x) :
    ‖mvfderiv I (fun y => WithLp.toLp 2 ((ρ y * 1) • (0 : W), ρ y * 1)) x v‖ ≤
      Λ * Real.sqrt (g.inner x v v) :=
  norm_mvfderiv_scaleBlock_le hρ hρ0 v
    (DifferentialGeometry.Geometry.Riemannian.Geodesic.abs_mvfderiv_le_of_lipschitzWith_riemannianEDistOf
      g hmetric hΛ hρL hρ v)

end Riemannian

end DifferentialGeometry.Geometry.Collapse
