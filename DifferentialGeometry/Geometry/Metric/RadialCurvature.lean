import DifferentialGeometry.Geometry.Metric.RadialConnection
import DifferentialGeometry.Geometry.Curvature.Coordinates.RiemannTensorBridge
import Mathlib.Analysis.Calculus.ContDiff.Deriv

noncomputable section
open DifferentialGeometry DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Curvature
open Bundle Manifold Set
open scoped Manifold InnerProductSpace Topology ContDiff
namespace DifferentialGeometry.Geometry.Riemannian
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

private def coeff (g : SmoothRiemannianMetric 𝓘(ℝ, E) E) (y u v : E) : E :=
  tangentSpaceModelContinuousLinearEquiv (I := 𝓘(ℝ, E)) y
    ((leviCivitaConnectionOfMetric (I := 𝓘(ℝ, E)) g
      (constantModelVectorField v) y)
      ((tangentSpaceModelContinuousLinearEquiv (I := 𝓘(ℝ, E)) y).symm u))

omit [FiniteDimensional ℝ E] in
private lemma const_smooth (v : E) :
    ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) ∞
      (T% (constantModelVectorField (𝕜 := ℝ) v)) := by
  apply (contMDiff_vectorSpace_iff_contDiff (𝕜 := ℝ)).mpr
  exact contDiff_const

private theorem riemann_model
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) E)
    (B : E → E →L[ℝ] E →L[ℝ] ℝ) {x : E}
    (hB : (fun y : E => tangentBilinearFormToModel y (g.inner y)) =ᶠ[𝓝 x] B)
    (hBdiff : DifferentiableAt ℝ B x) (hco : IsCoercive (B x))
    (u v z : E) :
    tangentSpaceModelContinuousLinearEquiv (I := 𝓘(ℝ, E)) x
      (riemannOp (cov := LeviCivita (I := 𝓘(ℝ, E)) g) x
        (constantModelVectorField u x) (constantModelVectorField v x)
        (constantModelVectorField z x)) =
      fderiv ℝ (fun y => coeff g y v z) x u -
      fderiv ℝ (fun y => coeff g y u z) x v +
      coeff g x u (coeff g x v z) - coeff g x v (coeff g x u z) := by
  let : CovariantDerivative.ContMDiffCovariantDerivative
      (LeviCivita (I := 𝓘(ℝ, E)) g) ∞ := LeviCivita_isContMDiff g
  have hc (p q : E) := covApply_mdifferentiableAt
    (cov := LeviCivita (I := 𝓘(ℝ, E)) g) (x := x)
    (const_smooth p) (const_smooth q)
  have hconv (p q : E) :
      (fun y : E => (tangentSpaceModelContinuousLinearEquiv (I := 𝓘(ℝ, E)) y).symm
        (coeff g y p q)) =
      covApply (LeviCivita (I := 𝓘(ℝ, E)) g)
        (constantModelVectorField p) (constantModelVectorField q) := by
    funext y
    simp only [coeff, ContinuousLinearEquiv.symm_apply_apply]
    rfl
  have hcov (p q s : E) := cov_eq_fderiv_add g B hB hBdiff hco
    (fun y => coeff g y p q) (by simpa only [coeff, ContinuousLinearEquiv.symm_apply_apply, covApply, LeviCivita, constantModelVectorField] using hc p q) s
  rw [riemannOp_apply_smooth _ (const_smooth u) (const_smooth v) (const_smooth z)]
  rw [riemannSec_def]
  have hbr : VectorField.mlieBracket 𝓘(ℝ, E)
      (constantModelVectorField u) (constantModelVectorField v) x = 0 := by
    rw [← VectorField.mlieBracketWithin_univ,
      VectorField.mlieBracketWithin_eq_lieBracketWithin]
    change VectorField.lieBracketWithin ℝ (fun _ : E => u) (fun _ : E => v) univ x = 0
    simp [VectorField.lieBracketWithin]
  rw [hbr, map_zero, sub_zero, map_sub]
  rw [← hconv v z, ← hconv u z]
  change (tangentSpaceModelContinuousLinearEquiv (I := 𝓘(ℝ, E)) x)
    ((leviCivitaConnectionOfMetric g _ x) ((tangentSpaceModelContinuousLinearEquiv (I := 𝓘(ℝ, E)) x).symm u)) -
    (tangentSpaceModelContinuousLinearEquiv (I := 𝓘(ℝ, E)) x)
    ((leviCivitaConnectionOfMetric g _ x) ((tangentSpaceModelContinuousLinearEquiv (I := 𝓘(ℝ, E)) x).symm v)) = _
  rw [hcov v z u, hcov u z v]
  rw [← const_cov_eq_nhds g B hB hBdiff hco u (coeff g x v z),
    ← const_cov_eq_nhds g B hB hBdiff hco v (coeff g x u z)]
  change _ + coeff g x u (coeff g x v z) -
    (_ + coeff g x v (coeff g x u z)) = _
  abel
omit [FiniteDimensional ℝ E] in
private theorem norm_deriv {x : E} (hx : x ≠ 0) :
    HasFDerivAt (fun y : E => ‖y‖) (‖x‖⁻¹ • innerSL ℝ x) x := by
  have hn : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  have h := (hasStrictFDerivAt_norm_sq x).hasFDerivAt.sqrt (pow_ne_zero 2 hn)
  convert h using 1
  · funext y
    simp only [Real.sqrt_sq (norm_nonneg y)]
  · ext u
    simp only [smul_apply, smul_eq_mul, Real.sqrt_sq (norm_nonneg x)]
    field_simp
    simp [mul_comm]

private def expr (A B C : ℝ → ℝ) (y u v : E) : E :=
  A ‖y‖ • (⟪y, u⟫_ℝ • v + ⟪y, v⟫_ℝ • u) +
    (B ‖y‖ * ⟪u, v⟫_ℝ + C ‖y‖ * ⟪y, u⟫_ℝ * ⟪y, v⟫_ℝ) • y

omit [FiniteDimensional ℝ E] in
private theorem expr_fderiv {A B C : ℝ → ℝ} {A' B' C' : ℝ} {x : E}
    (hA : HasDerivAt A A' ‖x‖) (hB : HasDerivAt B B' ‖x‖)
    (hC : HasDerivAt C C' ‖x‖) (hx : x ≠ 0) (t u v : E) :
    fderiv ℝ (fun y => expr A B C y u v) x t =
      (A' / ‖x‖ * ⟪x, t⟫_ℝ) • (⟪x, u⟫_ℝ • v + ⟪x, v⟫_ℝ • u) +
      A ‖x‖ • (⟪t, u⟫_ℝ • v + ⟪t, v⟫_ℝ • u) +
      (B' / ‖x‖ * ⟪x, t⟫_ℝ * ⟪u, v⟫_ℝ +
        C' / ‖x‖ * ⟪x, t⟫_ℝ * ⟪x, u⟫_ℝ * ⟪x, v⟫_ℝ +
        C ‖x‖ * (⟪t, u⟫_ℝ * ⟪x, v⟫_ℝ + ⟪x, u⟫_ℝ * ⟪t, v⟫_ℝ)) • x +
      (B ‖x‖ * ⟪u, v⟫_ℝ + C ‖x‖ * ⟪x, u⟫_ℝ * ⟪x, v⟫_ℝ) • t := by
  have hnorm := norm_deriv hx
  have hAN := hA.comp_hasFDerivAt x hnorm
  have hBN := hB.comp_hasFDerivAt x hnorm
  have hCN := hC.comp_hasFDerivAt x hnorm
  have hi (w : E) : HasFDerivAt (fun y : E => ⟪y, w⟫_ℝ) (innerSL ℝ w) x := by
    convert (innerSL ℝ w).hasFDerivAt (x := x) using 1
    funext y
    exact real_inner_comm w y
  have h := (hAN.smul (((hi u).smul_const v).add ((hi v).smul_const u))).add
    (((hBN.mul_const ⟪u, v⟫_ℝ).add ((hCN.mul (hi u)).mul (hi v))).smul
      (hasFDerivAt_id x))
  change HasFDerivAt (fun y => expr A B C y u v) _ x at h
  rw [h.fderiv]
  simp only [add_apply, ContinuousLinearMap.smulRight_apply, smul_apply,
    ContinuousLinearMap.id_apply, innerSL_apply_apply, smul_eq_mul, Function.comp_apply,
    real_inner_comm u t, real_inner_comm v t, Pi.add_apply, Pi.mul_apply, id_eq]
  simp only [div_eq_mul_inv, mul_smul, add_smul, smul_add]
  module
private def alpha (a : ℝ → ℝ) (r : ℝ) := deriv a r / (a r * r) - 1 / r ^ 2
private def beta (a : ℝ → ℝ) (r : ℝ) := (1 - a r * deriv a r / r) / r ^ 2
private def gamma (a : ℝ → ℝ) (r : ℝ) := -(2 * alpha a r + beta a r) / r ^ 2

private theorem beta_deriv {a : ℝ → ℝ} {r : ℝ}
    (ha : ContDiff ℝ ∞ a) (hr : r ≠ 0) :
    HasDerivAt (beta a)
      (-(deriv a r ^ 2 + a r * deriv (deriv a) r) / r ^ 3 - 2 / r ^ 3 +
        3 * a r * deriv a r / r ^ 4) r := by
  have h1 := (ha.differentiable (by simp) r).hasDerivAt
  have h2 := ((ha.deriv' (n := ∞)).differentiable (by simp) r).hasDerivAt
  have h := (((h1.mul h2).div (hasDerivAt_id r) hr).const_sub 1).div
    ((hasDerivAt_id r).pow 2) (pow_ne_zero 2 hr)
  convert h using 1 <;> first | rfl | (dsimp; field_simp; ring)

private theorem coeff_differentiable {a : ℝ → ℝ} {r : ℝ}
    (ha : ContDiff ℝ ∞ a) (hr : r ≠ 0) (har : a r ≠ 0) :
    DifferentiableAt ℝ (alpha a) r ∧ DifferentiableAt ℝ (gamma a) r := by
  have h1 := ha.differentiable (by simp) r
  have h2 := (ha.deriv' (n := ∞)).differentiable (by simp) r
  have hA : DifferentiableAt ℝ (alpha a) r :=
    (h2.div (h1.mul differentiableAt_id) (mul_ne_zero har hr)).sub
      ((differentiableAt_const (c := (1 : ℝ))).div (differentiableAt_id.pow 2) (pow_ne_zero 2 hr))
  refine ⟨hA, ?_⟩
  exact ((hA.const_mul 2).add (beta_deriv ha hr).differentiableAt).neg.div
    (differentiableAt_id.pow 2) (pow_ne_zero 2 hr)

private theorem coeff_eventually_eq
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) E) {a : ℝ → ℝ} {x : E}
    (hg : (fun y : E => tangentBilinearFormToModel y (g.inner y)) =ᶠ[𝓝 x]
      radialBilinearField a)
    (ha : ContDiff ℝ ∞ a) (hx : x ≠ 0) (hane : a ‖x‖ ≠ 0) (u v : E) :
    (fun y => coeff g y u v) =ᶠ[𝓝 x]
      (fun y => expr (alpha a) (beta a) (gamma a) y u v) := by
  filter_upwards [hg.eventuallyEq_nhds, eventually_ne_nhds hx,
    (ha.continuous.comp continuous_norm).continuousAt.eventually_ne hane] with y hy hyny hany
  exact leviCivita_const_of_radialBilinearField g hy
    ((ha.differentiable (by simp) ‖y‖).hasDerivAt) hyny hany u v

omit [FiniteDimensional ℝ E] in
private theorem radial_coercive {a : ℝ → ℝ} {x : E}
    (hx : x ≠ 0) (hane : a ‖x‖ ≠ 0) : IsCoercive (radialBilinearField a x) := by
  refine ⟨min ((a ‖x‖ / ‖x‖) ^ 2) 1,
    lt_min (sq_pos_of_ne_zero (div_ne_zero hane (norm_ne_zero_iff.mpr hx))) zero_lt_one, ?_⟩
  intro u
  simpa only [pow_two, mul_assoc] using radialBilinearField_lower_bound a hx u

theorem metricRm04StdAt_radialBilinearField_radial
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) E) {a : ℝ → ℝ} {x v : E}
    (hg : (fun y : E => tangentBilinearFormToModel y (g.inner y)) =ᶠ[𝓝 x]
      radialBilinearField a)
    (ha : ContDiff ℝ ∞ a) (hx : x ≠ 0) (hane : a ‖x‖ ≠ 0)
    (hv : ⟪x, v⟫_ℝ = 0) :
    metricRm04StandardAt (I := 𝓘(ℝ, E)) g x
      ((tangentSpaceModelContinuousLinearEquiv (I := 𝓘(ℝ, E)) x).symm x)
      ((tangentSpaceModelContinuousLinearEquiv (I := 𝓘(ℝ, E)) x).symm v)
      ((tangentSpaceModelContinuousLinearEquiv (I := 𝓘(ℝ, E)) x).symm v)
      ((tangentSpaceModelContinuousLinearEquiv (I := 𝓘(ℝ, E)) x).symm x) =
      -a ‖x‖ * deriv (deriv a) ‖x‖ * ‖v‖ ^ 2 := by
  have hn : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  have heq := coeff_eventually_eq g hg ha hx hane
  have heqp (u w : E) := (heq u w).eq_of_nhds
  have hdiff := differentiableAt_radialBilinearField
    (ha.differentiable (by simp) ‖x‖) hx
  have hA := (coeff_differentiable ha hn hane).1.hasDerivAt
  have hB := beta_deriv ha hn
  have hC := (coeff_differentiable ha hn hane).2.hasDerivAt
  rw [rm04_eq_inner_riem]
  change tangentBilinearFormToModel x (g.inner x) x
    ((tangentSpaceModelContinuousLinearEquiv (I := 𝓘(ℝ, E)) x)
      (riemannOp (cov := LeviCivita (I := 𝓘(ℝ, E)) g) x
        (constantModelVectorField x x) (constantModelVectorField v x)
        (constantModelVectorField v x))) = _
  rw [hg.eq_of_nhds, riemann_model g _ hg hdiff (radial_coercive hx hane)]
  rw [(heq v v).fderiv_eq, (heq x v).fderiv_eq,
    heqp v v, heqp x v, heqp x _, heqp v _]
  rw [expr_fderiv hA hB hC hx, expr_fderiv hA hB hC hx]
  rw [radialBilinearField_radial]
  simp only [expr, inner_add_right, inner_sub_right, inner_zero_right,
    real_inner_smul_right, real_inner_self_eq_norm_sq,
    hv, zero_mul, mul_zero, zero_smul, add_zero, zero_add]
  dsimp only [alpha, beta, gamma]
  field_simp
  ring

theorem metricRm04StdAt_radialBilinearField_tangential
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) E) {a : ℝ → ℝ} {x v w : E}
    (hg : (fun y : E => tangentBilinearFormToModel y (g.inner y)) =ᶠ[𝓝 x]
      radialBilinearField a)
    (ha : ContDiff ℝ ∞ a) (hx : x ≠ 0) (hane : a ‖x‖ ≠ 0)
    (hv : ⟪x, v⟫_ℝ = 0) (hw : ⟪x, w⟫_ℝ = 0) :
    metricRm04StandardAt (I := 𝓘(ℝ, E)) g x
      ((tangentSpaceModelContinuousLinearEquiv (I := 𝓘(ℝ, E)) x).symm v)
      ((tangentSpaceModelContinuousLinearEquiv (I := 𝓘(ℝ, E)) x).symm w)
      ((tangentSpaceModelContinuousLinearEquiv (I := 𝓘(ℝ, E)) x).symm w)
      ((tangentSpaceModelContinuousLinearEquiv (I := 𝓘(ℝ, E)) x).symm v) =
      a ‖x‖ ^ 2 * (1 - deriv a ‖x‖ ^ 2) / ‖x‖ ^ 4 *
        (‖v‖ ^ 2 * ‖w‖ ^ 2 - ⟪v, w⟫_ℝ ^ 2) := by
  have hvx : ⟪v, x⟫_ℝ = 0 := (real_inner_comm x v).trans hv
  have hwx : ⟪w, x⟫_ℝ = 0 := (real_inner_comm x w).trans hw
  have hn : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  have heq := coeff_eventually_eq g hg ha hx hane
  have heqp (u z : E) := (heq u z).eq_of_nhds
  have hdiff := differentiableAt_radialBilinearField
    (ha.differentiable (by simp) ‖x‖) hx
  have hA := (coeff_differentiable ha hn hane).1.hasDerivAt
  have hB := beta_deriv ha hn
  have hC := (coeff_differentiable ha hn hane).2.hasDerivAt
  rw [rm04_eq_inner_riem]
  change tangentBilinearFormToModel x (g.inner x) v
    ((tangentSpaceModelContinuousLinearEquiv (I := 𝓘(ℝ, E)) x)
      (riemannOp (cov := LeviCivita (I := 𝓘(ℝ, E)) g) x
        (constantModelVectorField v x) (constantModelVectorField w x)
        (constantModelVectorField w x))) = _
  rw [hg.eq_of_nhds, riemann_model g _ hg hdiff (radial_coercive hx hane)]
  rw [(heq w w).fderiv_eq, (heq v w).fderiv_eq,
    heqp w w, heqp v w, heqp v _, heqp w _]
  rw [expr_fderiv hA hB hC hx, expr_fderiv hA hB hC hx]
  rw [radialBilinearField_tangential a x _ hv]
  simp only [expr, inner_add_right, inner_sub_right,
    real_inner_smul_right, real_inner_self_eq_norm_sq,
    hv, hw, hvx, hwx, inner_zero_right, real_inner_comm w v,
    zero_mul, mul_zero, zero_smul, add_zero, zero_add]
  dsimp only [alpha, beta, gamma]
  field_simp
  ring

private theorem alpha_deriv {a : ℝ → ℝ} {r : ℝ}
    (ha : ContDiff ℝ ∞ a) (hr : r ≠ 0) (har : a r ≠ 0) :
    HasDerivAt (alpha a)
      (deriv (deriv a) r / (a r * r) - deriv a r ^ 2 / (a r ^ 2 * r) -
        deriv a r / (a r * r ^ 2) + 2 / r ^ 3) r := by
  have h1 := (ha.differentiable (by simp) r).hasDerivAt
  have h2 := ((ha.deriv' (n := ∞)).differentiable (by simp) r).hasDerivAt
  have h := (h2.div (h1.mul (hasDerivAt_id r)) (mul_ne_zero har hr)).sub
    ((hasDerivAt_const r (1 : ℝ)).div ((hasDerivAt_id r).pow 2) (pow_ne_zero 2 hr))
  convert h using 1 <;> first | rfl | (dsimp; field_simp; ring)

theorem metricRm04StdAt_radialBilinearField
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) E) {a : ℝ → ℝ} {x : E}
    (hg : (fun y : E => tangentBilinearFormToModel y (g.inner y)) =ᶠ[𝓝 x]
      radialBilinearField a)
    (ha : ContDiff ℝ ∞ a) (hx : x ≠ 0) (hane : a ‖x‖ ≠ 0) (u v w z : E) :
    let r := ‖x‖
    let kR := -a r * deriv (deriv a) r / r ^ 2
    let kT := a r ^ 2 * (1 - deriv a r ^ 2) / r ^ 4
    metricRm04StandardAt (I := 𝓘(ℝ, E)) g x
      ((tangentSpaceModelContinuousLinearEquiv (I := 𝓘(ℝ, E)) x).symm u)
      ((tangentSpaceModelContinuousLinearEquiv (I := 𝓘(ℝ, E)) x).symm v)
      ((tangentSpaceModelContinuousLinearEquiv (I := 𝓘(ℝ, E)) x).symm w)
      ((tangentSpaceModelContinuousLinearEquiv (I := 𝓘(ℝ, E)) x).symm z) =
      kT * (⟪u, z⟫_ℝ * ⟪v, w⟫_ℝ - ⟪u, w⟫_ℝ * ⟪v, z⟫_ℝ) +
        (kR - kT) / r ^ 2 *
          (⟪x, u⟫_ℝ * ⟪x, z⟫_ℝ * ⟪v, w⟫_ℝ +
            ⟪x, v⟫_ℝ * ⟪x, w⟫_ℝ * ⟪u, z⟫_ℝ -
            ⟪x, u⟫_ℝ * ⟪x, w⟫_ℝ * ⟪v, z⟫_ℝ -
            ⟪x, v⟫_ℝ * ⟪x, z⟫_ℝ * ⟪u, w⟫_ℝ) := by
  have hn : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  have heq := coeff_eventually_eq g hg ha hx hane
  have heqp (p q : E) := (heq p q).eq_of_nhds
  have hdiff := differentiableAt_radialBilinearField
    (ha.differentiable (by simp) ‖x‖) hx
  have hA := alpha_deriv ha hn hane
  have hB := beta_deriv ha hn
  have hC := (coeff_differentiable ha hn hane).2.hasDerivAt
  dsimp only
  rw [rm04_eq_inner_riem]
  change tangentBilinearFormToModel x (g.inner x) z
    ((tangentSpaceModelContinuousLinearEquiv (I := 𝓘(ℝ, E)) x)
      (riemannOp (cov := LeviCivita (I := 𝓘(ℝ, E)) g) x
        (constantModelVectorField u x) (constantModelVectorField v x)
        (constantModelVectorField w x))) = _
  rw [hg.eq_of_nhds, riemann_model g _ hg hdiff (radial_coercive hx hane)]
  rw [(heq v w).fderiv_eq, (heq u w).fderiv_eq,
    heqp v w, heqp u w, heqp u _, heqp v _]
  rw [expr_fderiv hA hB hC hx, expr_fderiv hA hB hC hx]
  rw [radialBilinearField_apply]
  simp only [expr, inner_add_right, inner_sub_right,
    real_inner_smul_right, real_inner_self_eq_norm_sq]
  simp only [real_inner_comm]
  dsimp only [alpha, beta, gamma]
  field_simp
  ring

theorem metricRm04StdAt_radialBilinearField_plane
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) E) {a : ℝ → ℝ} {x : E}
    (hg : (fun y : E => tangentBilinearFormToModel y (g.inner y)) =ᶠ[𝓝 x]
      radialBilinearField a)
    (ha : ContDiff ℝ ∞ a) (hx : x ≠ 0) (hane : a ‖x‖ ≠ 0) (u v : E) :
    let r := ‖x‖
    let uT := u - (⟪x, u⟫_ℝ / r ^ 2) • x
    let vT := v - (⟪x, v⟫_ℝ / r ^ 2) • x
    metricRm04StandardAt (I := 𝓘(ℝ, E)) g x
      ((tangentSpaceModelContinuousLinearEquiv (I := 𝓘(ℝ, E)) x).symm u)
      ((tangentSpaceModelContinuousLinearEquiv (I := 𝓘(ℝ, E)) x).symm v)
      ((tangentSpaceModelContinuousLinearEquiv (I := 𝓘(ℝ, E)) x).symm v)
      ((tangentSpaceModelContinuousLinearEquiv (I := 𝓘(ℝ, E)) x).symm u) =
      -a r * deriv (deriv a) r / r ^ 4 * ‖⟪x, u⟫_ℝ • v - ⟪x, v⟫_ℝ • u‖ ^ 2 +
        a r ^ 2 * (1 - deriv a r ^ 2) / r ^ 4 *
          (‖uT‖ ^ 2 * ‖vT‖ ^ 2 - ⟪uT, vT⟫_ℝ ^ 2) := by
  have hn : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  dsimp only
  rw [metricRm04StdAt_radialBilinearField g hg ha hx hane]
  simp only [← real_inner_self_eq_norm_sq, inner_sub_left, inner_sub_right,
    real_inner_smul_left, real_inner_smul_right]
  simp only [real_inner_comm]
  rw [real_inner_self_eq_norm_sq x]
  field_simp
  ring

theorem metricRm04StdAt_radialBilinearField_nonneg
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) E) {a : ℝ → ℝ} {x : E}
    (hg : (fun y : E => tangentBilinearFormToModel y (g.inner y)) =ᶠ[𝓝 x]
      radialBilinearField a)
    (ha : ContDiff ℝ ∞ a) (hx : x ≠ 0) (hapos : 0 < a ‖x‖)
    (hconc : deriv (deriv a) ‖x‖ ≤ 0) (hslope : |deriv a ‖x‖| ≤ 1) (u v : E) :
    0 ≤ metricRm04StandardAt (I := 𝓘(ℝ, E)) g x
      ((tangentSpaceModelContinuousLinearEquiv (I := 𝓘(ℝ, E)) x).symm u)
      ((tangentSpaceModelContinuousLinearEquiv (I := 𝓘(ℝ, E)) x).symm v)
      ((tangentSpaceModelContinuousLinearEquiv (I := 𝓘(ℝ, E)) x).symm v)
      ((tangentSpaceModelContinuousLinearEquiv (I := 𝓘(ℝ, E)) x).symm u) := by
  rw [metricRm04StdAt_radialBilinearField_plane g hg ha hx hapos.ne' u v]
  apply add_nonneg
  · exact mul_nonneg (div_nonneg
      (mul_nonneg_of_nonpos_of_nonpos (neg_nonpos.mpr hapos.le) hconc)
      (by positivity)) (sq_nonneg _)
  · apply mul_nonneg
    · exact div_nonneg (mul_nonneg (sq_nonneg _)
        (sub_nonneg.mpr ((sq_le_one_iff_abs_le_one _).mpr hslope))) (by positivity)
    · simpa only [real_inner_self_eq_norm_sq, ← pow_two, sub_nonneg] using
        real_inner_mul_inner_self_le
          (u - (⟪x, u⟫_ℝ / ‖x‖ ^ 2) • x) (v - (⟪x, v⟫_ℝ / ‖x‖ ^ 2) • x)
end DifferentialGeometry.Geometry.Riemannian
