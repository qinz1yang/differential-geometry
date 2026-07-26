import DifferentialGeometry.Geometry.Exponential.GaussLemma
import DifferentialGeometry.Geometry.Metric.DistanceScaling
import DifferentialGeometry.Geometry.Operator.Gradient
import DifferentialGeometry.Geometry.Topology.FiberBundleT2

set_option autoImplicit false

/-!
# Pointwise gradient bound for intrinsically Lipschitz functions

This file proves the differentiability-point estimate used to identify the
intrinsic weak gradient of a Riemannian-distance Lipschitz function.  The proof
tests the function only on radial exponential curves based at the point, so the
Lipschitz constant is not enlarged by a coordinate-comparison constant.
-/

noncomputable section

open Bundle Filter Manifold Set
open scoped ENNReal Manifold NNReal Topology

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian

open DifferentialGeometry.Geometry.Riemannian.Exponential
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Integral.Measure

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I (↑(⊤ : ℕ∞) : WithTop ℕ∞) M]

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- At every differentiability point, the Riemannian norm of the gradient of
an intrinsically `L`-Lipschitz real function is at most `L`. -/
private theorem grad_norm_le_lip_ne
    [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [T2Space M]
    (g : SmoothRiemannianMetric I M) {u : M → ℝ} {L : ℝ≥0} {x : M}
    (hu : ∀ y z, edist (u y) (u z) ≤
      (L : ℝ≥0∞) * riemannianEDistOf (I := I) g y z)
    (hux : MDifferentiableAt I 𝓘(ℝ, ℝ) u x) :
    Real.sqrt (g.inner x (gradFun (I := I) g u x)
      (gradFun (I := I) g u x)) ≤ (L : ℝ) := by
  classical
  letI : CompleteSpace E := FiniteDimensional.complete ℝ E
  letI : T2Space (TangentBundle I M) := inferInstance
  let F : E → ℝ := fun v =>
    u (expMap (I := I) g x (show TangentSpace I x from v))
  have hexp0 :
      expMap (I := I) g x (show TangentSpace I x from (0 : E)) = x :=
    expMap_zero (I := I) g x
  have hexp : HasMFDerivAt 𝓘(ℝ, E) I
      (fun v : E =>
        (expMap (I := I) g x (show TangentSpace I x from v) : M))
      (0 : E) (ContinuousLinearMap.id ℝ E) := by
    have h := ((expMap_contMDiffAt_zero (I := I) g x).mdifferentiableAt
      one_ne_zero).hasMFDerivAt
    rw [mfderiv_expMap_at_zero (I := I) g x] at h
    exact h
  have hu_at : HasMFDerivAt I 𝓘(ℝ, ℝ) u x
      (mfderiv I 𝓘(ℝ, ℝ) u x) :=
    hux.hasMFDerivAt
  have hu_exp : HasMFDerivAt I 𝓘(ℝ, ℝ) u
      ((fun v : E =>
        (expMap (I := I) g x (show TangentSpace I x from v) : M)) 0)
      (mfderiv I 𝓘(ℝ, ℝ) u x) := by
    change HasMFDerivAt I 𝓘(ℝ, ℝ) u
      (expMap (I := I) g x (show TangentSpace I x from (0 : E)))
      (mfderiv I 𝓘(ℝ, ℝ) u x)
    rw [hexp0]
    exact hu_at
  have hF : HasFDerivAt F (mfderiv I 𝓘(ℝ, ℝ) u x) 0 := by
    have hcomp := hu_exp.comp (0 : E) hexp
    simpa only [F, Function.comp_apply, ContinuousLinearMap.comp_id] using
      hcomp.hasFDerivAt
  let v : TangentSpace I x := gradFun (I := I) g u x
  let vE : E := show E from v
  let duv : ℝ := show ℝ from mfderiv I 𝓘(ℝ, ℝ) u x v
  let s : ℝ := Real.sqrt (g.inner x v v)
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hline : HasDerivAt (fun t : ℝ => F (t • vE)) duv 0 := by
    have ht : HasDerivAt (fun t : ℝ => t • vE) vE 0 := by
      simpa using (hasDerivAt_id (0 : ℝ)).smul_const vE
    have hc := hF.comp_hasDerivAt_of_eq (0 : ℝ) ht (by simp)
    simpa only [Function.comp_apply, vE, duv] using hc
  have hsmall : ∀ᶠ t in 𝓝 (0 : ℝ),
      ‖t • vE‖ < expMapC2Radius (I := I) g x := by
    have hR : 0 < expMapC2Radius (I := I) g x :=
      expMapC2Radius_pos (I := I) g x
    have hc : ContinuousAt (fun t : ℝ => t • vE) 0 := by
      fun_prop
    have hc0 : Tendsto (fun t : ℝ => t • vE) (𝓝 0) (𝓝 0) := by
      simpa only [ContinuousAt, zero_smul] using hc
    have hb : Metric.ball (0 : E) (expMapC2Radius (I := I) g x) ∈
        𝓝 (0 : E) := Metric.ball_mem_nhds _ hR
    filter_upwards [hc0.eventually hb] with t ht
    simpa only [Metric.mem_ball, dist_zero_right] using ht
  letI : RiemannianBundle (fun y : M ↦ TangentSpace I y) :=
    ⟨g.toRiemannianMetric⟩
  have hEnorm : ∀ (y : M) (w : TangentSpace I y),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner y w w)) := by
    intro y w
    rw [← ofReal_norm_eq_enorm, norm_eq_sqrt_real_inner]
    rfl
  have hsmul (t : ℝ) :
      g.inner x (t • v) (t • v) = t ^ 2 * g.inner x v v := by
    rw [(g.inner x).map_smul t v, ContinuousLinearMap.smul_apply,
      (g.inner x v).map_smul t v]
    simp only [smul_eq_mul]
    ring
  have hradial : ∀ᶠ t in 𝓝 (0 : ℝ),
      |F (t • vE) - F 0| ≤ (L : ℝ) * s * |t| := by
    filter_upwards [hsmall] with t ht
    have hdist : riemannianEDistOf (I := I) g x
        (expMap (I := I) g x
          (show TangentSpace I x from (t • vE))) ≤
        ENNReal.ofReal (Real.sqrt
          (g.inner x (t • v) (t • v))) := by
      change riemannianEDist I x
        (expMap (I := I) g x
          (show TangentSpace I x from (t • vE))) ≤ _
      exact edist_exp_le_radius (I := I) g x (t • vE) hEnorm ht
    have hENN : edist (u x)
        (u (expMap (I := I) g x
          (show TangentSpace I x from (t • vE)))) ≤
        (L : ℝ≥0∞) * ENNReal.ofReal
          (Real.sqrt (g.inner x (t • v) (t • v))) :=
      (hu x _).trans (by gcongr)
    have hreal := (ENNReal.toReal_le_toReal
      (edist_ne_top _ _) (by finiteness)).2 hENN
    rw [edist_dist, ENNReal.toReal_ofReal dist_nonneg,
      ENNReal.toReal_mul, ENNReal.coe_toReal,
      ENNReal.toReal_ofReal (Real.sqrt_nonneg _)] at hreal
    have hs_smul : Real.sqrt (g.inner x (t • v) (t • v)) = |t| * s := by
      rw [hsmul, Real.sqrt_mul (sq_nonneg t), Real.sqrt_sq_eq_abs]
    rw [hs_smul] at hreal
    simpa only [F, zero_smul, hexp0, Real.dist_eq, abs_sub_comm,
      mul_assoc, mul_comm, mul_left_comm, vE] using hreal
  have hdu : |duv| ≤ (L : ℝ) * s := by
    have hradial' : ∀ᶠ t in 𝓝 (0 : ℝ),
        ‖F (t • vE) - F ((0 : ℝ) • vE)‖ ≤
          (L : ℝ) * s * ‖t - 0‖ := by
      simpa only [zero_smul, sub_zero, Real.norm_eq_abs] using hradial
    have h := hline.le_of_lip' (mul_nonneg (NNReal.coe_nonneg L) hs0) hradial'
    simpa only [Real.norm_eq_abs, mul_assoc] using h
  have hinner0 : 0 ≤ g.inner x v v := by
    rcases eq_or_ne v 0 with hv | hv
    · rw [hv]
      simp
    · exact (g.pos x v hv).le
  have hduv : g.inner x v v = duv := by
    simpa only [v, duv] using inner_gradFun (I := I) g u x v
  have hinner : g.inner x v v ≤ (L : ℝ) * s := by
    calc
      g.inner x v v = |g.inner x v v| := by
        rw [abs_of_nonneg hinner0]
      _ = |duv| := by rw [hduv]
      _ ≤ (L : ℝ) * s := hdu
  have hs_sq : s ^ 2 = g.inner x v v := by
    exact Real.sq_sqrt hinner0
  change s ≤ (L : ℝ)
  by_cases hs : s = 0
  · simpa only [hs] using NNReal.coe_nonneg L
  · have hspos : 0 < s := lt_of_le_of_ne hs0 (Ne.symm hs)
    nlinarith

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- At every differentiability point, the Riemannian norm of the gradient of
an intrinsically `L`-Lipschitz real function is at most `L`. -/
theorem grad_norm_le_lip
    [I.Boundaryless] [T2Space M]
    (g : SmoothRiemannianMetric I M) {u : M → ℝ} {L : ℝ≥0} {x : M}
    (hu : ∀ y z, edist (u y) (u z) ≤
      (L : ℝ≥0∞) * riemannianEDistOf (I := I) g y z)
    (hux : MDifferentiableAt I 𝓘(ℝ, ℝ) u x) :
    Real.sqrt (g.inner x (gradFun (I := I) g u x)
      (gradFun (I := I) g u x)) ≤ (L : ℝ) := by
  classical
  by_cases hdim : Module.finrank ℝ E = 0
  · have hvE : (show E from gradFun (I := I) g u x) = 0 :=
      (finrank_zero_iff_forall_zero.mp hdim) _
    have hv : gradFun (I := I) g u x = (0 : TangentSpace I x) := hvE
    rw [hv]
    simpa only [map_zero, Real.sqrt_zero] using NNReal.coe_nonneg L
  · letI : NeZero (Module.finrank ℝ E) := ⟨hdim⟩
    exact grad_norm_le_lip_ne (I := I) g hu hux

/-- The Riemannian norm of the everywhere-defined gradient representative of
an intrinsically `L`-Lipschitz real function is at most `L` at every point. -/
theorem grad_norm_le_lip_all
    [I.Boundaryless] [T2Space M]
    (g : SmoothRiemannianMetric I M) {u : M → ℝ} {L : ℝ≥0} {x : M}
    (hu : ∀ y z, edist (u y) (u z) ≤
      (L : ℝ≥0∞) * riemannianEDistOf (I := I) g y z) :
    Real.sqrt (g.inner x (gradFun (I := I) g u x)
      (gradFun (I := I) g u x)) ≤ (L : ℝ) := by
  by_cases hux : MDifferentiableAt I 𝓘(ℝ, ℝ) u x
  · exact grad_norm_le_lip (I := I) g hu hux
  · have hmf : mfderiv I 𝓘(ℝ, ℝ) u x = 0 :=
      mfderiv_zero_of_not_mdifferentiableAt hux
    have hgrad : gradFun (I := I) g u x = (0 : TangentSpace I x) :=
      gradFun_eq_zero_of_mfderiv_eq_zero (I := I) g u hmf
    rw [hgrad]
    simpa only [map_zero, Real.sqrt_zero] using NNReal.coe_nonneg L

end Riemannian
end Geometry
end DifferentialGeometry

end
