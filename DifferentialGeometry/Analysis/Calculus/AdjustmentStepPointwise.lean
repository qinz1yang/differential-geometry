import DifferentialGeometry.Analysis.InnerProductSpace.AdjustmentFactorization
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace

/-!
# CFS17 / CFS20 for an adjustment, pointwise along a tangent vector (GAF02's stage step)

Blueprint `master207B.tex`, CFS17 / CFS20 (the cumulative value and derivative bounds of one
adjustment stage) in the form GAF02 (B:5797) needs on a manifold: the derivative of the previous
map is a continuous linear map `Df : T →L H` on a tangent space `T` whose norm is NOT the metric
norm, so every derivative bound is stated pointwise, `‖(·) w‖ ≤ (…) · N` with `N = √g(w, w)`.

For the adjustment `Ψ y = y + ψ(y)(P(π_Q y) − π_Q y)` (`adjustmentMap`):
* `hasFDerivAt_adjustmentMap_GAF3`: its derivative
  `DΨ(y) = id + ψ(y)(DP(π_Q y)π_Q − π_Q) + Dψ(y) ⊗ (P(π_Q y) − π_Q y)`.
* `adjustmentMap_step_value_GAF3`: `‖Ψ(y) − z₀‖ ≤ (E₀ + a)ρ` from `‖y − z₀‖ ≤ E₀ρ` and
  `‖P(π_Q y) − π_Q y‖ ≤ aρ`, `ψ(y) ∈ [0, 1]`.
* `adjustmentMap_step_deriv_GAF3`: with a comparison operator `A` (`‖id − A‖ ≤ 1`,
  `‖DP(π_Q y) − A‖ ≤ d`), the cutoff bound `‖Dψ(y)‖ ≤ b/ρ`, the original derivative
  `‖DF₀ w‖ ≤ LN`, the normal error `‖(id − A)π_Q DF₀ w‖ ≤ νN` and the prior error
  `‖Df w − DF₀ w‖ ≤ H₀N`:
  `‖DΨ(y)(Df w) − DF₀ w‖ ≤ (ab(L + H₀) + d(L + H₀) + ν + 2H₀)N` — exactly CFS20's derivative budget
  (`projected_cutoff_adjustment_cumulative_le`, pointwise).
* `mvfderiv_comp_apply_of_differentiableAt_GAF3`: for `f : M → H` and `Ψ : H → H'` differentiable at
  `f q`, `d(Ψ ∘ f)_q w = DΨ(f q)(df_q w)`.
-/

set_option autoImplicit false

open Filter Set
open scoped Topology Manifold ContDiff

namespace DifferentialGeometry.Analysis

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- The derivative of an adjustment map. -/
theorem hasFDerivAt_adjustmentMap_GAF3 (Q : Submodule ℝ H) [Q.HasOrthogonalProjection]
    {P : H → H} {ψ : H → ℝ} {y : H} (hP : DifferentiableAt ℝ P (Q.starProjection y))
    (hψ : DifferentiableAt ℝ ψ y) :
    HasFDerivAt (adjustmentMap Q P ψ)
      (ContinuousLinearMap.id ℝ H +
        (ψ y • ((fderiv ℝ P (Q.starProjection y)).comp Q.starProjection - Q.starProjection) +
          (fderiv ℝ ψ y).smulRight (P (Q.starProjection y) - Q.starProjection y))) y := by
  have hv : HasFDerivAt (fun z => P (Q.starProjection z) - Q.starProjection z)
      ((fderiv ℝ P (Q.starProjection y)).comp Q.starProjection - Q.starProjection) y :=
    (hP.hasFDerivAt.comp y Q.starProjection.hasFDerivAt).sub Q.starProjection.hasFDerivAt
  exact (hasFDerivAt_id y).add (hψ.hasFDerivAt.smul hv)

/-- CFS20's value step for one adjustment. -/
theorem adjustmentMap_step_value_GAF3 (Q : Submodule ℝ H) [Q.HasOrthogonalProjection]
    {P : H → H} {ψ : H → ℝ} {y z₀ : H} {a E₀ ρ : ℝ}
    (hψI : ψ y ∈ Icc (0 : ℝ) 1)
    (hvalue : ‖P (Q.starProjection y) - Q.starProjection y‖ ≤ a * ρ)
    (hprior : ‖y - z₀‖ ≤ E₀ * ρ) :
    ‖adjustmentMap Q P ψ y - z₀‖ ≤ (E₀ + a) * ρ := by
  rw [adjustmentMap_apply]
  have h1 : ‖ψ y • (P (Q.starProjection y) - Q.starProjection y)‖ ≤ a * ρ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hψI.1]
    have h := mul_le_mul_of_nonneg_right hψI.2 (norm_nonneg
      (P (Q.starProjection y) - Q.starProjection y))
    linarith
  have h2 : y + ψ y • (P (Q.starProjection y) - Q.starProjection y) - z₀ =
      (y - z₀) + ψ y • (P (Q.starProjection y) - Q.starProjection y) := by abel
  rw [h2]
  calc _ ≤ ‖y - z₀‖ + ‖ψ y • (P (Q.starProjection y) - Q.starProjection y)‖ := norm_add_le _ _
    _ ≤ E₀ * ρ + a * ρ := add_le_add hprior h1
    _ = (E₀ + a) * ρ := by ring

/-- **CFS20's derivative step for one adjustment, pointwise along a tangent vector.** -/
theorem adjustmentMap_step_deriv_GAF3 (Q : Submodule ℝ H) [Q.HasOrthogonalProjection]
    {T : Type*} [NormedAddCommGroup T] [NormedSpace ℝ T]
    {P : H → H} {ψ : H → ℝ} {y : H} (hP : DifferentiableAt ℝ P (Q.starProjection y))
    (hψ : DifferentiableAt ℝ ψ y) (A : H →L[ℝ] H) (Df DF₀ : T →L[ℝ] H) (w : T)
    {a b d L ν H₀ ρ N : ℝ} (hb : 0 ≤ b) (hd : 0 ≤ d) (hL : 0 ≤ L) (hH : 0 ≤ H₀)
    (hρ : 0 < ρ) (hN : 0 ≤ N) (hψI : ψ y ∈ Icc (0 : ℝ) 1)
    (hA : ‖ContinuousLinearMap.id ℝ H - A‖ ≤ 1)
    (hvalue : ‖P (Q.starProjection y) - Q.starProjection y‖ ≤ a * ρ)
    (hcut : ‖fderiv ℝ ψ y‖ ≤ b / ρ)
    (hcomparison : ‖fderiv ℝ P (Q.starProjection y) - A‖ ≤ d)
    (hfirst : ‖DF₀ w‖ ≤ L * N)
    (hnormal : ‖(ContinuousLinearMap.id ℝ H - A) (Q.starProjection (DF₀ w))‖ ≤ ν * N)
    (hprior : ‖Df w - DF₀ w‖ ≤ H₀ * N) :
    ‖fderiv ℝ (adjustmentMap Q P ψ) y (Df w) - DF₀ w‖ ≤
      (a * b * (L + H₀) + d * (L + H₀) + ν + 2 * H₀) * N := by
  rw [(hasFDerivAt_adjustmentMap_GAF3 Q hP hψ).fderiv]
  set u := Df w with hu
  set D := fderiv ℝ P (Q.starProjection y) with hD
  set v := P (Q.starProjection y) - Q.starProjection y with hv
  have hQ1 : ∀ z : H, ‖Q.starProjection z‖ ≤ ‖z‖ := fun z => Q.norm_starProjection_apply_le z
  have hu_le : ‖u‖ ≤ (L + H₀) * N := by
    have h' : ‖u‖ ≤ ‖DF₀ w‖ + ‖u - DF₀ w‖ := by
      have := norm_add_le (DF₀ w) (u - DF₀ w)
      rwa [add_sub_cancel] at this
    linarith
  -- the three pieces of `DΨ(y) u − DF₀ w`
  have hsplit : (ContinuousLinearMap.id ℝ H +
        (ψ y • (D.comp Q.starProjection - Q.starProjection) +
          (fderiv ℝ ψ y).smulRight v)) u - DF₀ w =
      (u - DF₀ w) + ψ y • ((D - A) (Q.starProjection u) -
        (ContinuousLinearMap.id ℝ H - A) (Q.starProjection u)) + (fderiv ℝ ψ y u) • v := by
    simp only [add_apply, ContinuousLinearMap.id_apply, smul_apply, sub_apply,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.smulRight_apply, smul_sub]
    abel
  rw [hsplit]
  -- the normal piece
  have hnorm_u : ‖(ContinuousLinearMap.id ℝ H - A) (Q.starProjection u)‖ ≤ ν * N + H₀ * N := by
    have heq : (ContinuousLinearMap.id ℝ H - A) (Q.starProjection u) =
        (ContinuousLinearMap.id ℝ H - A) (Q.starProjection (DF₀ w)) +
          (ContinuousLinearMap.id ℝ H - A) (Q.starProjection (u - DF₀ w)) := by
      rw [← map_add, ← map_add, add_sub_cancel]
    rw [heq]
    refine (norm_add_le _ _).trans (add_le_add hnormal ?_)
    calc _ ≤ ‖ContinuousLinearMap.id ℝ H - A‖ * ‖Q.starProjection (u - DF₀ w)‖ :=
          ContinuousLinearMap.le_opNorm _ _
      _ ≤ 1 * ‖u - DF₀ w‖ := mul_le_mul hA (hQ1 _) (norm_nonneg _) zero_le_one
      _ ≤ H₀ * N := by rw [one_mul]; exact hprior
  have hcomp_u : ‖(D - A) (Q.starProjection u)‖ ≤ d * ((L + H₀) * N) :=
    calc _ ≤ ‖D - A‖ * ‖Q.starProjection u‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ d * ((L + H₀) * N) := mul_le_mul hcomparison ((hQ1 u).trans hu_le) (norm_nonneg _) hd
  have hmid : ‖ψ y • ((D - A) (Q.starProjection u) -
      (ContinuousLinearMap.id ℝ H - A) (Q.starProjection u))‖ ≤
        d * ((L + H₀) * N) + (ν * N + H₀ * N) := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hψI.1]
    have h := norm_sub_le ((D - A) (Q.starProjection u))
      ((ContinuousLinearMap.id ℝ H - A) (Q.starProjection u))
    have hnn : 0 ≤ ‖(D - A) (Q.starProjection u) -
        (ContinuousLinearMap.id ℝ H - A) (Q.starProjection u)‖ := norm_nonneg _
    calc _ ≤ 1 * ‖(D - A) (Q.starProjection u) -
          (ContinuousLinearMap.id ℝ H - A) (Q.starProjection u)‖ :=
          mul_le_mul_of_nonneg_right hψI.2 hnn
      _ ≤ _ := by linarith
  have hcutu : ‖(fderiv ℝ ψ y u) • v‖ ≤ a * b * ((L + H₀) * N) := by
    rw [norm_smul]
    have h1 : ‖fderiv ℝ ψ y u‖ ≤ b / ρ * ((L + H₀) * N) :=
      (ContinuousLinearMap.le_opNorm _ _).trans
        (mul_le_mul hcut hu_le (norm_nonneg _) (div_nonneg hb hρ.le))
    have h2 := mul_le_mul h1 hvalue (norm_nonneg _) (by positivity)
    have h3 : b / ρ * ((L + H₀) * N) * (a * ρ) = a * b * ((L + H₀) * N) := by
      field_simp
    linarith
  calc _ ≤ ‖(u - DF₀ w) + ψ y • ((D - A) (Q.starProjection u) -
        (ContinuousLinearMap.id ℝ H - A) (Q.starProjection u))‖ + ‖(fderiv ℝ ψ y u) • v‖ :=
        norm_add_le _ _
    _ ≤ (‖u - DF₀ w‖ + ‖ψ y • ((D - A) (Q.starProjection u) -
        (ContinuousLinearMap.id ℝ H - A) (Q.starProjection u))‖) + ‖(fderiv ℝ ψ y u) • v‖ :=
        add_le_add_left (norm_add_le _ _) _
    _ ≤ (H₀ * N + (d * ((L + H₀) * N) + (ν * N + H₀ * N))) + a * b * ((L + H₀) * N) :=
        add_le_add (add_le_add hprior hmid) hcutu
    _ = (a * b * (L + H₀) + d * (L + H₀) + ν + 2 * H₀) * N := by ring

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {G : Type*} [TopologicalSpace G]
  {I : ModelWithCorners ℝ E G} {M : Type*} [TopologicalSpace M] [ChartedSpace G M]
  {H' : Type*} [NormedAddCommGroup H'] [NormedSpace ℝ H']

/-- The chain rule for a vector-valued map on a manifold followed by a map of normed spaces. -/
theorem mvfderiv_comp_apply_of_differentiableAt_GAF3 {f : M → H} {Ψ : H → H'} {q : M}
    (hf : MDifferentiableAt I 𝓘(ℝ, H) f q) (hΨ : DifferentiableAt ℝ Ψ (f q))
    (w : TangentSpace I q) :
    mvfderiv I (Ψ ∘ f) q w = fderiv ℝ Ψ (f q) (mvfderiv I f q w) := by
  rw [mvfderiv_comp_apply q hΨ.mdifferentiableAt hf w, mvfderiv_eq_fderiv]
  rfl

end DifferentialGeometry.Analysis
