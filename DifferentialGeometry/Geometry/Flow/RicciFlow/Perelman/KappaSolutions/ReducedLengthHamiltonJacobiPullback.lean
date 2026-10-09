import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.ReducedLengthHamiltonJacobi
import DifferentialGeometry.Geometry.Operator.GradientPullback
import DifferentialGeometry.Geometry.Operator.NormGradSqScaling
import Mathlib.Geometry.Manifold.LocalDiffeomorph
import DifferentialGeometry.Geometry.Curvature.Naturality.Pullback.LocalCross
import DifferentialGeometry.Geometry.Curvature.Metric.Scaling

set_option autoImplicit false
noncomputable section
namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
open Filter Set
open DifferentialGeometry.Geometry.Operator DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness CanonicalNeighborhood
open scoped _root_.Manifold ContDiff _root_.Topology
universe u uE uH
variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E
variable (F : PointedFlowData.{u, uE, uH} (I := I) ancientTimeInterval)
attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
variable {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners ℝ E' H'}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H' M] [IsManifold J ∞ M]

omit [I.Boundaryless] in
private theorem hamiltonian_rescaled_pullback
    (Φ : PartialDiffeomorph J I M F.M ∞) {x : M} (hx : x ∈ Φ.source)
    {c theta : ℝ} (hc : 0 < c) (htheta : 0 < theta)
    (g : SmoothRiemannianMetric J M)
    (hg : ∀ v w : TangentSpace J x,
      g.inner x v w = c⁻¹ * (F.S.base.metric (-(c * theta))).inner (Φ x)
        (mfderiv J I Φ x v) (mfderiv J I Φ x w))
    (phi : ℝ → M → ℝ)
    (hphi : MDifferentiableAt (𝓘(ℝ, ℝ).prod J) 𝓘(ℝ, ℝ)
      (fun z : ℝ × M => phi z.1 z.2) (theta, x)) :
    c * (deriv (fun a => phi (a / c) (Φ.symm (Φ x))) (c * theta) +
      (1 / 2 : ℝ) * normGradSqFun (F.S.base.metric (-(c * theta)))
        (fun y => phi ((c * theta) / c) (Φ.symm y)) (Φ x) -
      (1 / 2 : ℝ) * F.S.scalar (-(c * theta)) (Φ x) +
      phi ((c * theta) / c) (Φ.symm (Φ x)) / (2 * (c * theta))) =
    deriv (fun a => phi a x) theta + (1 / 2 : ℝ) * normGradSqFun g (phi theta) x -
      (c / 2) * F.S.scalar (-(c * theta)) (Φ x) + phi theta x / (2 * theta) := by
  have hleft (y : M) (hy : y ∈ Φ.source) : Φ.symm (Φ y) = y := Φ.left_inv' hy
  have hcancel : c * theta / c = theta := mul_div_cancel_left₀ theta hc.ne'
  have htime : DifferentiableAt ℝ (fun a => phi a x) theta :=
    (hphi.comp theta (mdifferentiableAt_id.prodMk mdifferentiableAt_const)).differentiableAt
  have hderiv : deriv (fun a => phi (a / c) x) (c * theta) =
      deriv (fun a => phi a x) theta / c := by
    have houter : HasDerivAt (fun a => phi a x) (deriv (fun a => phi a x) theta)
        (c * theta / c) := hcancel.symm ▸ htime.hasDerivAt
    simpa only [one_div, div_eq_mul_inv, Function.comp_def, id_eq, one_mul] using
      (houter.comp (c * theta) ((hasDerivAt_id (c * theta)).div_const c)).deriv
  have hspace : MDifferentiableAt J 𝓘(ℝ, ℝ) (phi theta) x :=
    hphi.comp x (mdifferentiableAt_const.prodMk mdifferentiableAt_id)
  have hinv := Φ.symm.mdifferentiableAt (by simp) (Φ.map_source' hx)
  have hfun : MDifferentiableAt I 𝓘(ℝ, ℝ) (fun y => phi theta (Φ.symm y)) (Φ x) := by
    apply MDifferentiableAt.comp (Φ x) _ hinv
    simpa only [hleft x hx] using hspace
  have hsurj : Function.Surjective (mfderiv J I Φ x) :=
    ((Φ.isLocalDiffeomorphAt J I ∞ hx).mfderivToContinuousLinearEquiv (by simp)).surjective
  have hnorm := normGradSqFun_eq_of_pullback_inner g
    (scaleMetric c⁻¹ (inv_pos.mpr hc) (F.S.base.metric (-(c * theta)))) Φ x
    (Φ.mdifferentiableAt (by simp) hx)
    (by intro v w; rw [scaleMetric_inner]; exact hg v w) hsurj
    (fun y => phi theta (Φ.symm y)) hfun
  have heq : (fun y => phi theta (Φ.symm (Φ y))) =ᶠ[𝓝 x] phi theta := by
    filter_upwards [Φ.open_source.mem_nhds hx] with y hy
    rw [hleft y hy]
  have hgrad : gradientFun g (fun y => phi theta (Φ.symm (Φ y))) x =
      gradientFun g (phi theta) x := by
    have hval : phi theta (Φ.symm (Φ x)) = phi theta x :=
      congrArg (phi theta) (hleft x hx)
    have hmf := heq.mfderiv_eq (I := J) (I' := 𝓘(ℝ, ℝ))
    have hmv : mvfderiv J (fun y => phi theta (Φ.symm (Φ y))) x =
        mvfderiv J (phi theta) x := by
      unfold mvfderiv
      rw [hmf]
      dsimp only
      rw [hval]
      apply ContinuousLinearMap.ext
      intro v
      rfl
    exact congrArg (fun A : TangentSpace J x →L[ℝ] ℝ =>
      metricSharp g x A.toLinearMap) hmv
  change g.inner x
    (gradientFun g (fun y => phi theta (Φ.symm (Φ y))) x)
    (gradientFun g (fun y => phi theta (Φ.symm (Φ y))) x) = _ at hnorm
  rw [hgrad, normGradSqFun_scaleMetric, inv_inv] at hnorm
  change normGradSqFun g (phi theta) x = _ at hnorm
  rw [hcancel, hleft x hx, hderiv, hnorm]
  field_simp

private theorem redLength_upper_test_pullback_of_touching
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F)
    (p : F.M) (Φ : PartialDiffeomorph J I M F.M ∞) {x : M} (hx : x ∈ Φ.source)
    {c theta : ℝ} (hc : 0 < c) (htheta : 0 < theta)
    (g : SmoothRiemannianMetric J M)
    (hg : ∀ v w : TangentSpace J x,
      g.inner x v w = c⁻¹ * (F.S.base.metric (-(c * theta))).inner (Φ x)
        (mfderiv J I Φ x v) (mfderiv J I Φ x w))
    (phi : ℝ → M → ℝ)
    (hphi : MDifferentiableAt (𝓘(ℝ, ℝ).prod J) 𝓘(ℝ, ℝ)
      (fun z : ℝ × M => phi z.1 z.2) (theta, x))
    (heq : redLength F.S 0 p (Φ x) (c * theta) = phi theta x)
    (hupper : ∀ᶠ z : ℝ × M in 𝓝 (theta, x),
      redLength F.S 0 p (Φ z.2) (c * z.1) ≤ phi z.1 z.2) :
    deriv (fun a => phi a x) theta + (1 / 2 : ℝ) * normGradSqFun g (phi theta) x -
      (c / 2) * F.S.scalar (-(c * theta)) (Φ x) + phi theta x / (2 * theta) ≤ 0 := by
  let psi : ℝ → F.M → ℝ := fun a y => phi (a / c) (Φ.symm y)
  have hleft (y : M) (hy : y ∈ Φ.source) : Φ.symm (Φ y) = y := Φ.left_inv' hy
  have hcancel : c * theta / c = theta := mul_div_cancel_left₀ theta hc.ne'
  have hinv := Φ.symm.mdifferentiableAt (by simp) (Φ.map_source' hx)
  have hmap : MDifferentiableAt (𝓘(ℝ, ℝ).prod I) (𝓘(ℝ, ℝ).prod J)
      (fun z : ℝ × F.M => (z.1 / c, Φ.symm z.2)) (c * theta, Φ x) := by
    have hdiv : MDifferentiableAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ)
        (fun z : ℝ × F.M => z.1 / c) (c * theta, Φ x) := by
      simp only [div_eq_mul_inv]
      exact mdifferentiableAt_fst.mul mdifferentiableAt_const
    have hsnd : MDifferentiableAt (𝓘(ℝ, ℝ).prod I) J
        (fun z : ℝ × F.M => Φ.symm z.2) (c * theta, Φ x) :=
      hinv.comp (c * theta, Φ x) (f := Prod.snd) mdifferentiableAt_snd
    exact hdiv.prodMk hsnd
  have hpsi : MDifferentiableAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ)
      (fun z : ℝ × F.M => psi z.1 z.2) (c * theta, Φ x) := by
    change MDifferentiableAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ)
      ((fun z : ℝ × M => phi z.1 z.2) ∘ (fun z : ℝ × F.M => (z.1 / c, Φ.symm z.2))) _
    apply MDifferentiableAt.comp (c * theta, Φ x) _ hmap
    simpa only [hcancel, hleft x hx] using hphi
  have hpsieq : redLength F.S 0 p (Φ x) (c * theta) = psi (c * theta) (Φ x) := by
    simpa only [psi, hcancel, hleft x hx] using heq
  have htend : Tendsto (fun z : ℝ × F.M => (z.1 / c, Φ.symm z.2))
      (𝓝 (c * theta, Φ x)) (𝓝 (theta, x)) := by
    simpa only [hcancel, hleft x hx] using hmap.continuousAt.tendsto
  have hpsile : ∀ᶠ z : ℝ × F.M in 𝓝 (c * theta, Φ x),
      redLength F.S 0 p z.2 z.1 ≤ psi z.1 z.2 := by
    have htarget : ∀ᶠ z : ℝ × F.M in 𝓝 (c * theta, Φ x), z.2 ∈ Φ.target :=
      continuous_snd.continuousAt.tendsto.eventually (Φ.open_target.mem_nhds (Φ.map_source' hx))
    filter_upwards [htend.eventually hupper, htarget] with z hz hzt
    have hright : Φ (Φ.symm z.2) = z.2 := Φ.right_inv' hzt
    simpa only [hright, mul_div_cancel₀ z.1 hc.ne'] using hz
  have h := ancient_redLength_hamilton_jacobi_upper_test_terminal F hF
    (mul_pos hc htheta) p (Φ x) psi hpsi hpsieq hpsile
  have hm := mul_nonpos_of_nonneg_of_nonpos hc.le h
  change c * (deriv (fun a => phi (a / c) (Φ.symm (Φ x))) (c * theta) +
    (1 / 2 : ℝ) * normGradSqFun (F.S.base.metric (-(c * theta)))
      (fun y => phi ((c * theta) / c) (Φ.symm y)) (Φ x) -
    (1 / 2 : ℝ) * F.S.scalar (-(c * theta)) (Φ x) +
    phi ((c * theta) / c) (Φ.symm (Φ x)) / (2 * (c * theta))) ≤ 0 at hm
  rwa [hamiltonian_rescaled_pullback F Φ hx hc htheta g hg phi hphi] at hm

private theorem redLength_lower_test_pullback_of_touching
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F)
    (p : F.M) (Φ : PartialDiffeomorph J I M F.M ∞) {x : M} (hx : x ∈ Φ.source)
    {c theta : ℝ} (hc : 0 < c) (htheta : 0 < theta)
    (g : SmoothRiemannianMetric J M)
    (hg : ∀ v w : TangentSpace J x,
      g.inner x v w = c⁻¹ * (F.S.base.metric (-(c * theta))).inner (Φ x)
        (mfderiv J I Φ x v) (mfderiv J I Φ x w))
    (phi : ℝ → M → ℝ)
    (hphi : MDifferentiableAt (𝓘(ℝ, ℝ).prod J) 𝓘(ℝ, ℝ)
      (fun z : ℝ × M => phi z.1 z.2) (theta, x))
    (heq : redLength F.S 0 p (Φ x) (c * theta) = phi theta x)
    (hlower : ∀ᶠ z : ℝ × M in 𝓝 (theta, x),
      phi z.1 z.2 ≤ redLength F.S 0 p (Φ z.2) (c * z.1)) :
    0 ≤ deriv (fun a => phi a x) theta + (1 / 2 : ℝ) * normGradSqFun g (phi theta) x -
      (c / 2) * F.S.scalar (-(c * theta)) (Φ x) + phi theta x / (2 * theta) := by
  let psi : ℝ → F.M → ℝ := fun a y => phi (a / c) (Φ.symm y)
  have hleft (y : M) (hy : y ∈ Φ.source) : Φ.symm (Φ y) = y := Φ.left_inv' hy
  have hcancel : c * theta / c = theta := mul_div_cancel_left₀ theta hc.ne'
  have hinv := Φ.symm.mdifferentiableAt (by simp) (Φ.map_source' hx)
  have hmap : MDifferentiableAt (𝓘(ℝ, ℝ).prod I) (𝓘(ℝ, ℝ).prod J)
      (fun z : ℝ × F.M => (z.1 / c, Φ.symm z.2)) (c * theta, Φ x) := by
    have hdiv : MDifferentiableAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ)
        (fun z : ℝ × F.M => z.1 / c) (c * theta, Φ x) := by
      simp only [div_eq_mul_inv]
      exact mdifferentiableAt_fst.mul mdifferentiableAt_const
    have hsnd : MDifferentiableAt (𝓘(ℝ, ℝ).prod I) J
        (fun z : ℝ × F.M => Φ.symm z.2) (c * theta, Φ x) :=
      hinv.comp (c * theta, Φ x) (f := Prod.snd) mdifferentiableAt_snd
    exact hdiv.prodMk hsnd
  have hpsi : MDifferentiableAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ)
      (fun z : ℝ × F.M => psi z.1 z.2) (c * theta, Φ x) := by
    change MDifferentiableAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ)
      ((fun z : ℝ × M => phi z.1 z.2) ∘ (fun z : ℝ × F.M => (z.1 / c, Φ.symm z.2))) _
    apply MDifferentiableAt.comp (c * theta, Φ x) _ hmap
    simpa only [hcancel, hleft x hx] using hphi
  have hpsieq : redLength F.S 0 p (Φ x) (c * theta) = psi (c * theta) (Φ x) := by
    simpa only [psi, hcancel, hleft x hx] using heq
  have htend : Tendsto (fun z : ℝ × F.M => (z.1 / c, Φ.symm z.2))
      (𝓝 (c * theta, Φ x)) (𝓝 (theta, x)) := by
    simpa only [hcancel, hleft x hx] using hmap.continuousAt.tendsto
  have hpsige : ∀ᶠ z : ℝ × F.M in 𝓝 (c * theta, Φ x),
      psi z.1 z.2 ≤ redLength F.S 0 p z.2 z.1 := by
    have htarget : ∀ᶠ z : ℝ × F.M in 𝓝 (c * theta, Φ x), z.2 ∈ Φ.target :=
      continuous_snd.continuousAt.tendsto.eventually (Φ.open_target.mem_nhds (Φ.map_source' hx))
    filter_upwards [htend.eventually hlower, htarget] with z hz hzt
    have hright : Φ (Φ.symm z.2) = z.2 := Φ.right_inv' hzt
    simpa only [hright, mul_div_cancel₀ z.1 hc.ne'] using hz
  have h := ancient_redLength_hamilton_jacobi_lower_test_terminal F hF
    (mul_pos hc htheta) p (Φ x) psi hpsi hpsieq hpsige
  have hm := mul_nonneg hc.le h
  change 0 ≤ c * (deriv (fun a => phi (a / c) (Φ.symm (Φ x))) (c * theta) +
    (1 / 2 : ℝ) * normGradSqFun (F.S.base.metric (-(c * theta)))
      (fun y => phi ((c * theta) / c) (Φ.symm y)) (Φ x) -
    (1 / 2 : ℝ) * F.S.scalar (-(c * theta)) (Φ x) +
    phi ((c * theta) / c) (Φ.symm (Φ x)) / (2 * (c * theta))) at hm
  rwa [hamiltonian_rescaled_pullback F Φ hx hc htheta g hg phi hphi] at hm

theorem ancient_redLength_hamilton_jacobi_upper_test_pullback
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F)
    (p : F.M) (Φ : PartialDiffeomorph J I M F.M ∞) {x : M} (hx : x ∈ Φ.source)
    {c theta : ℝ} (hc : 0 < c) (htheta : 0 < theta)
    (g : SmoothRiemannianMetric J M)
    (hg : ∀ v w : TangentSpace J x,
      g.inner x v w = c⁻¹ * (F.S.base.metric (-(c * theta))).inner (Φ x)
        (mfderiv J I Φ x v) (mfderiv J I Φ x w))
    (phi : ℝ → M → ℝ)
    (hphi : MDifferentiableAt (𝓘(ℝ, ℝ).prod J) 𝓘(ℝ, ℝ)
      (fun z : ℝ × M => phi z.1 z.2) (theta, x))
    (hmax : IsLocalMax (fun z : ℝ × M =>
      redLength F.S 0 p (Φ z.2) (c * z.1) - phi z.1 z.2) (theta, x)) :
    deriv (fun a => phi a x) theta + (1 / 2 : ℝ) * normGradSqFun g (phi theta) x -
      (c / 2) * F.S.scalar (-(c * theta)) (Φ x) +
      redLength F.S 0 p (Φ x) (c * theta) / (2 * theta) ≤ 0 := by
  let d := redLength F.S 0 p (Φ x) (c * theta) - phi theta x
  let psi : ℝ → M → ℝ := fun a y => phi a y + d
  have hpsi : MDifferentiableAt (𝓘(ℝ, ℝ).prod J) 𝓘(ℝ, ℝ)
      (fun z : ℝ × M => psi z.1 z.2) (theta, x) := hphi.add mdifferentiableAt_const
  have heq : redLength F.S 0 p (Φ x) (c * theta) = psi theta x := by
    dsimp only [psi, d]
    ring
  have hupper : ∀ᶠ z : ℝ × M in 𝓝 (theta, x),
      redLength F.S 0 p (Φ z.2) (c * z.1) ≤ psi z.1 z.2 := by
    filter_upwards [hmax] with z hz
    change redLength F.S 0 p (Φ z.2) (c * z.1) - phi z.1 z.2 ≤
      redLength F.S 0 p (Φ x) (c * theta) - phi theta x at hz
    dsimp only [psi, d]
    linarith
  have h := redLength_upper_test_pullback_of_touching F hF p Φ hx hc htheta g hg
    psi hpsi heq hupper
  have hspace : MDifferentiableAt J 𝓘(ℝ, ℝ) (phi theta) x :=
    hphi.comp x (mdifferentiableAt_const.prodMk mdifferentiableAt_id)
  have hgrad : gradientFun g (psi theta) x = gradientFun g (phi theta) x := by
    change gradientFun g (fun y => phi theta y + d) x = _
    rw [gradientFun_add g hspace mdifferentiableAt_const, gradientFun_const, add_zero]
  have hnorm : normGradSqFun g (psi theta) x = normGradSqFun g (phi theta) x := by
    change g.inner x (gradientFun g (psi theta) x) (gradientFun g (psi theta) x) = _
    rw [hgrad]
    rfl
  rw [hnorm, ← heq] at h
  simpa only [psi, deriv_add_const] using h

theorem ancient_redLength_hamilton_jacobi_lower_test_pullback
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F)
    (p : F.M) (Φ : PartialDiffeomorph J I M F.M ∞) {x : M} (hx : x ∈ Φ.source)
    {c theta : ℝ} (hc : 0 < c) (htheta : 0 < theta)
    (g : SmoothRiemannianMetric J M)
    (hg : ∀ v w : TangentSpace J x,
      g.inner x v w = c⁻¹ * (F.S.base.metric (-(c * theta))).inner (Φ x)
        (mfderiv J I Φ x v) (mfderiv J I Φ x w))
    (phi : ℝ → M → ℝ)
    (hphi : MDifferentiableAt (𝓘(ℝ, ℝ).prod J) 𝓘(ℝ, ℝ)
      (fun z : ℝ × M => phi z.1 z.2) (theta, x))
    (hmin : IsLocalMin (fun z : ℝ × M =>
      redLength F.S 0 p (Φ z.2) (c * z.1) - phi z.1 z.2) (theta, x)) :
    0 ≤ deriv (fun a => phi a x) theta + (1 / 2 : ℝ) * normGradSqFun g (phi theta) x -
      (c / 2) * F.S.scalar (-(c * theta)) (Φ x) +
      redLength F.S 0 p (Φ x) (c * theta) / (2 * theta) := by
  let d := redLength F.S 0 p (Φ x) (c * theta) - phi theta x
  let psi : ℝ → M → ℝ := fun a y => phi a y + d
  have hpsi : MDifferentiableAt (𝓘(ℝ, ℝ).prod J) 𝓘(ℝ, ℝ)
      (fun z : ℝ × M => psi z.1 z.2) (theta, x) := hphi.add mdifferentiableAt_const
  have heq : redLength F.S 0 p (Φ x) (c * theta) = psi theta x := by
    dsimp only [psi, d]
    ring
  have hlower : ∀ᶠ z : ℝ × M in 𝓝 (theta, x),
      psi z.1 z.2 ≤ redLength F.S 0 p (Φ z.2) (c * z.1) := by
    filter_upwards [hmin] with z hz
    change redLength F.S 0 p (Φ x) (c * theta) - phi theta x ≤
      redLength F.S 0 p (Φ z.2) (c * z.1) - phi z.1 z.2 at hz
    dsimp only [psi, d]
    linarith
  have h := redLength_lower_test_pullback_of_touching F hF p Φ hx hc htheta g hg
    psi hpsi heq hlower
  have hspace : MDifferentiableAt J 𝓘(ℝ, ℝ) (phi theta) x :=
    hphi.comp x (mdifferentiableAt_const.prodMk mdifferentiableAt_id)
  have hgrad : gradientFun g (psi theta) x = gradientFun g (phi theta) x := by
    change gradientFun g (fun y => phi theta y + d) x = _
    rw [gradientFun_add g hspace mdifferentiableAt_const, gradientFun_const, add_zero]
  have hnorm : normGradSqFun g (psi theta) x = normGradSqFun g (phi theta) x := by
    change g.inner x (gradientFun g (psi theta) x) (gradientFun g (psi theta) x) = _
    rw [hgrad]
    rfl
  rw [hnorm, ← heq] at h
  simpa only [psi, deriv_add_const] using h

theorem ancient_redLength_hamilton_jacobi_upper_test_of_local_pullback_metric
    [J.Boundaryless] [T2Space M]
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F)
    (p : F.M) (Φ : PartialDiffeomorph J I M F.M ∞)
    (U : TopologicalSpace.Opens M) (hU : (U : Set M) ⊆ Φ.source) {x : M} (hx : x ∈ U)
    {c theta : ℝ} (hc : 0 < c) (htheta : 0 < theta)
    (g : SmoothRiemannianMetric J M)
    (hg : ∀ y ∈ U, ∀ v w : TangentSpace J y,
      g.inner y v w = c⁻¹ * (F.S.base.metric (-(c * theta))).inner (Φ y)
        (mfderiv J I Φ y v) (mfderiv J I Φ y w))
    (phi : ℝ → M → ℝ)
    (hphi : MDifferentiableAt (𝓘(ℝ, ℝ).prod J) 𝓘(ℝ, ℝ)
      (fun z : ℝ × M => phi z.1 z.2) (theta, x))
    (htest : IsLocalMax (fun z : ℝ × M =>
      redLength F.S 0 p (Φ z.2) (c * z.1) - phi z.1 z.2) (theta, x)) :
    deriv (fun a => phi a x) theta + (1 / 2 : ℝ) * normGradSqFun g (phi theta) x -
      (1 / 2 : ℝ) * metricScalarAt g x +
      redLength F.S 0 p (Φ x) (c * theta) / (2 * theta) ≤ 0 := by
  have hscalar : metricScalarAt g x = c * F.S.scalar (-(c * theta)) (Φ x) := by
    have h := metricScalarAt_eq_of_partialDiffeomorph_inner g
      (scaleMetric c⁻¹ (inv_pos.mpr hc) (F.S.base.metric (-(c * theta)))) Φ U hU
      (by intro y hy v w; rw [scaleMetric_inner]; exact hg y hy v w) hx
    simpa only [metricScalarAt_scaleMetric, inv_inv, SolutionOn.scalar, SolutionFamily.scalar] using h
  have h := ancient_redLength_hamilton_jacobi_upper_test_pullback
    F hF p Φ (hU hx) hc htheta g (hg x hx) phi hphi htest
  rw [hscalar]
  nlinarith

theorem ancient_redLength_hamilton_jacobi_lower_test_of_local_pullback_metric
    [J.Boundaryless] [T2Space M]
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F)
    (p : F.M) (Φ : PartialDiffeomorph J I M F.M ∞)
    (U : TopologicalSpace.Opens M) (hU : (U : Set M) ⊆ Φ.source) {x : M} (hx : x ∈ U)
    {c theta : ℝ} (hc : 0 < c) (htheta : 0 < theta)
    (g : SmoothRiemannianMetric J M)
    (hg : ∀ y ∈ U, ∀ v w : TangentSpace J y,
      g.inner y v w = c⁻¹ * (F.S.base.metric (-(c * theta))).inner (Φ y)
        (mfderiv J I Φ y v) (mfderiv J I Φ y w))
    (phi : ℝ → M → ℝ)
    (hphi : MDifferentiableAt (𝓘(ℝ, ℝ).prod J) 𝓘(ℝ, ℝ)
      (fun z : ℝ × M => phi z.1 z.2) (theta, x))
    (htest : IsLocalMin (fun z : ℝ × M =>
      redLength F.S 0 p (Φ z.2) (c * z.1) - phi z.1 z.2) (theta, x)) :
    0 ≤ deriv (fun a => phi a x) theta + (1 / 2 : ℝ) * normGradSqFun g (phi theta) x -
      (1 / 2 : ℝ) * metricScalarAt g x +
      redLength F.S 0 p (Φ x) (c * theta) / (2 * theta) := by
  have hscalar : metricScalarAt g x = c * F.S.scalar (-(c * theta)) (Φ x) := by
    have h := metricScalarAt_eq_of_partialDiffeomorph_inner g
      (scaleMetric c⁻¹ (inv_pos.mpr hc) (F.S.base.metric (-(c * theta)))) Φ U hU
      (by intro y hy v w; rw [scaleMetric_inner]; exact hg y hy v w) hx
    simpa only [metricScalarAt_scaleMetric, inv_inv, SolutionOn.scalar, SolutionFamily.scalar] using h
  have h := ancient_redLength_hamilton_jacobi_lower_test_pullback
    F hF p Φ (hU hx) hc htheta g (hg x hx) phi hphi htest
  rw [hscalar]
  nlinarith

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
