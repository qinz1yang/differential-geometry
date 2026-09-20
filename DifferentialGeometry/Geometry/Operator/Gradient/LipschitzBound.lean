import DifferentialGeometry.Geometry.Operator.Gradient.NormSquared
import DifferentialGeometry.Geometry.Operator.Scalar.Calculus
import Mathlib.Analysis.SpecialFunctions.Sqrt
import DifferentialGeometry.Geometry.Exponential.GaussLemma.Basic
import DifferentialGeometry.Geometry.Exponential.MinimizingGeodesic
import DifferentialGeometry.Geometry.Metric.Comparison.DistanceScaling
import DifferentialGeometry.Geometry.Operator.Gradient.Basic
import DifferentialGeometry.Bundle.FiberBundleHausdorff
import DifferentialGeometry.Analysis.Calculus.Derivative.Curve

open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Operator

set_option autoImplicit false

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
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I (↑(⊤ : ℕ∞) : WithTop ℕ∞) M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
private theorem grad_norm_le_lip_ne
    [I.Boundaryless] [T2Space M]
    (g : SmoothRiemannianMetric I M) {u : M → ℝ} {L : ℝ≥0} {x : M}
    (hu : ∀ y z, edist (u y) (u z) ≤
      (L : ℝ≥0∞) * riemannianEDistOf (I := I) g y z)
    (hux : MDifferentiableAt I 𝓘(ℝ, ℝ) u x) :
    Real.sqrt (g.inner x (gradFun (I := I) g u x)
      (gradFun (I := I) g u x)) ≤ (L : ℝ) := by
  classical
  let : CompleteSpace E := FiniteDimensional.complete ℝ E
  let : T2Space (TangentBundle I M) := inferInstance
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
    convert! hcomp.hasFDerivAt using 1
  let v : TangentSpace I x := gradFun (I := I) g u x
  let vE : E := show E from v
  let duv : ℝ := show ℝ from mfderiv I 𝓘(ℝ, ℝ) u x v
  let s : ℝ := Real.sqrt (g.inner x v v)
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hline : HasDerivAt (fun t : ℝ => F (t • vE)) duv 0 := by
    have ht : HasDerivAt (fun t : ℝ => t • vE) vE 0 := by
      simpa using (hasDerivAt_id (0 : ℝ)).smul_const vE
    have hc := hF.comp_hasDerivAt_of_eq (0 : ℝ) ht (by simp)
    convert! hc using 1
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
  let : RiemannianBundle (fun y : M ↦ TangentSpace I y) :=
    ⟨g.toRiemannianMetric⟩
  have hEnorm : ∀ (y : M) (w : TangentSpace I y),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner y w w)) := by
    intro y w
    rw [← ofReal_norm, norm_eq_sqrt_real_inner]
    rfl
  have hsmul (t : ℝ) :
      g.inner x (t • v) (t • v) = t ^ 2 * g.inner x v v := by
    rw [(g.inner x).map_smul t v, smul_apply,
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

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
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
  · let : NeZero (Module.finrank ℝ E) := ⟨hdim⟩
    exact grad_norm_le_lip_ne (I := I) g hu hux

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

theorem grad_norm_sq_le_of_sqrt_lipschitz
    [I.Boundaryless] [T2Space M]
    (g : SmoothRiemannianMetric I M) {u : M → ℝ} {K : ℝ≥0}
    (hu : ∀ y, 0 ≤ u y)
    (hLip : ∀ y z, edist (Real.sqrt (u y)) (Real.sqrt (u z)) ≤
      (K : ℝ≥0∞) * riemannianEDistOf g y z) (x : M) :
    g.inner x (gradFun g u x) (gradFun g u x) ≤ 4 * (K : ℝ) ^ 2 * u x := by
  by_cases hd : MDifferentiableAt I 𝓘(ℝ, ℝ) u x
  · by_cases hz : u x = 0
    · have hm : IsLocalMin u x := Eventually.of_forall fun y => by rw [hz]; exact hu y
      have hg : gradFun g u x = 0 := gradientFun_eq_zero_of_isLocalMin g hm hd
      simp only [hg, map_zero, hz, mul_zero, le_refl]
    · have hs : MDifferentiableAt I 𝓘(ℝ, ℝ) (fun y => Real.sqrt (u y)) x :=
        (Real.hasDerivAt_sqrt hz).differentiableAt.mdifferentiableAt.comp x hd
      have heq : (fun y => Real.sqrt (u y) ^ 2) = u := funext fun y => Real.sq_sqrt (hu y)
      have hgrad : gradFun g u x = (2 * Real.sqrt (u x)) • gradFun g (fun y => Real.sqrt (u y)) x := by
        have h := gradientFun_pow g 1 hs
        norm_num only [Nat.reduceAdd, Nat.cast_ofNat, pow_one] at h
        rw [heq] at h
        exact h
      have hn := grad_norm_le_lip_all g hLip (x := x)
      have hnonneg : 0 ≤ g.inner x (gradFun g (fun y => Real.sqrt (u y)) x)
          (gradFun g (fun y => Real.sqrt (u y)) x) := metric_inner_self_nonneg g x _
      have hsq := (sq_le_sq₀ (Real.sqrt_nonneg _) K.coe_nonneg).mpr hn
      rw [Real.sq_sqrt hnonneg] at hsq
      rw [hgrad]
      simp only [map_smul, smul_apply, smul_eq_mul]
      calc
        _ = (4 * Real.sqrt (u x) ^ 2) *
            g.inner x (gradFun g (fun y => Real.sqrt (u y)) x)
              (gradFun g (fun y => Real.sqrt (u y)) x) := by ring
        _ ≤ (4 * Real.sqrt (u x) ^ 2) * (K : ℝ) ^ 2 :=
          mul_le_mul_of_nonneg_left hsq (by positivity)
        _ = _ := by rw [Real.sq_sqrt (hu x)]; ring
  · rw [gradFun_eq_zero_of_mfderiv_eq_zero g u (mfderiv_zero_of_not_mdifferentiableAt hd)]
    simp only [map_zero]
    exact mul_nonneg (by positivity) (hu x)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
private theorem lip_of_grad_norm_le_ne
    [I.Boundaryless] [T2Space M] [T2Space (TangentBundle I M)]
    [SigmaCompactSpace M] [ConnectedSpace M]
    [NeZero (Module.finrank ℝ E)]
    (g : SmoothRiemannianMetric I M)
    (hg : RiemannianMetricComplete (I := I) g)
    {u : M → ℝ} {L : ℝ≥0}
    (hu : ContMDiff I (modelWithCornersSelf ℝ ℝ)
      (↑(⊤ : ℕ∞) : WithTop ℕ∞) u)
    (hgrad : ∀ x : M,
      Real.sqrt (g.inner x (gradFun (I := I) g u x)
        (gradFun (I := I) g u x)) ≤ (L : ℝ)) :
    ∀ x y : M, edist (u x) (u y) ≤
      (L : ℝ≥0∞) * riemannianEDistOf (I := I) g x y := by
  classical
  let : IsManifold I 1 M :=
    IsManifold.of_le (I := I) (M := M)
      (n := (↑(⊤ : ℕ∞) : WithTop ℕ∞))
      (by decide : (1 : WithTop ℕ∞) ≤ (↑(⊤ : ℕ∞) : WithTop ℕ∞))
  let : TopologicalSpace.MetrizableSpace M :=
    Manifold.metrizableSpace I M
  let : T3Space M := inferInstance
  let : RiemannianBundle (fun x : M => TangentSpace I x) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
    ⟨⟨g.inner, g.contMDiff.continuous, by intro x v w; rfl⟩⟩
  let : PseudoEMetricSpace M :=
    PseudoEMetricSpace.ofRiemannianMetric I M
  let : CompleteSpace M := hg.complete
  have hEnorm : IsMetricNorm (I := I) (M := M) g := by
    intro x v
    exact tensor0SBundle_enorm_eq_riemannianBundle_enorm (I := I) g x v
  intro x y
  have hfin : riemannianEDist I x y ≠ (∞ : ENNReal) :=
    riemannianEDist_ne_top (I := I) x y
  obtain ⟨v, hv_end, hv_norm⟩ :=
    minExp_of_ne_top (I := I) g hEnorm x y hfin
  let gamma : ℝ → M := intrinsicGeodesic (I := I) g hEnorm x v
  have hgamma_smooth : ContMDiff (modelWithCornersSelf ℝ ℝ) I 1 gamma := by
    exact contMDiffOn_univ.mp
      (intrinsicGeodesic_contMDiffOn (I := I) g hEnorm x v)
  have hderiv : ∀ t : ℝ, HasDerivAt (fun s : ℝ => u (gamma s))
      (NormedSpace.fromTangentSpace (u (gamma t))
        (mfderiv I (modelWithCornersSelf ℝ ℝ) u (gamma t)
          (mfderiv (modelWithCornersSelf ℝ ℝ) I gamma t
            (DifferentialGeometry.Analysis.Calculus.realTangentOne t)))) t := by
    intro t
    exact DifferentialGeometry.Analysis.Calculus.hasDerivAt_comp_mfderiv_along
      I u gamma t
        ((hu (gamma t)).mdifferentiableAt (by simp))
        ((hgamma_smooth t).mdifferentiableAt (by simp))
  have hbound : ∀ t : ℝ,
      ‖NormedSpace.fromTangentSpace (u (gamma t))
        (mfderiv I (modelWithCornersSelf ℝ ℝ) u (gamma t)
          (mfderiv (modelWithCornersSelf ℝ ℝ) I gamma t
            (DifferentialGeometry.Analysis.Calculus.realTangentOne t)))‖ ≤
        (L : ℝ) * (riemannianEDist I x y).toReal := by
    intro t
    let w : TangentSpace I (gamma t) :=
      mfderiv (modelWithCornersSelf ℝ ℝ) I gamma t
        (DifferentialGeometry.Analysis.Calculus.realTangentOne t)
    have hw_eq : w = mfderiv (modelWithCornersSelf ℝ ℝ) I gamma t (1 : ℝ) := by
      rfl
    have hdu : mfderiv I (modelWithCornersSelf ℝ ℝ) u (gamma t) w =
        g.inner (gamma t) (gradFun (I := I) g u (gamma t)) w := by
      exact (inner_gradFun (I := I) g u (gamma t) w).symm
    have hcs := abs_inner_le_sqrt_mul_sqrt (I := I) g (gamma t)
      (gradFun (I := I) g u (gamma t)) w
    have hspeed_sq : g.inner (gamma t) w w = g.inner x v v := by
      rw [hw_eq]
      exact intrinsicGeodesic_speedSq_eq (I := I) g hEnorm x v t
    have hspeed : Real.sqrt (g.inner (gamma t) w w) =
        (riemannianEDist I x y).toReal := by
      rw [hspeed_sq, hv_norm]
    calc
      ‖NormedSpace.fromTangentSpace (u (gamma t))
          (mfderiv I (modelWithCornersSelf ℝ ℝ) u (gamma t) w)‖ =
          |g.inner (gamma t) (gradFun (I := I) g u (gamma t)) w| := by
            rw [hdu]
            rfl
      _ ≤ Real.sqrt (g.inner (gamma t)
            (gradFun (I := I) g u (gamma t))
            (gradFun (I := I) g u (gamma t))) *
          Real.sqrt (g.inner (gamma t) w w) := hcs
      _ ≤ (L : ℝ) * Real.sqrt (g.inner (gamma t) w w) := by
        exact mul_le_mul_of_nonneg_right (hgrad (gamma t)) (Real.sqrt_nonneg _)
      _ = (L : ℝ) * (riemannianEDist I x y).toReal := by rw [hspeed]
  have hreal : |u y - u x| ≤
      (L : ℝ) * (riemannianEDist I x y).toReal := by
    have hmv := norm_image_sub_le_of_norm_deriv_le_segment_01'
      (f := fun s : ℝ => u (gamma s))
      (f' := fun t => NormedSpace.fromTangentSpace (u (gamma t))
        (mfderiv I (modelWithCornersSelf ℝ ℝ) u (gamma t)
          (mfderiv (modelWithCornersSelf ℝ ℝ) I gamma t
            (DifferentialGeometry.Analysis.Calculus.realTangentOne t))))
      (C := (L : ℝ) * (riemannianEDist I x y).toReal)
      (fun t _ => (hderiv t).hasDerivWithinAt)
      (fun t _ => hbound t)
    have hgamma_zero : gamma 0 = x :=
      intrinsicGeodesic_zero (I := I) g hEnorm x v
    have hgamma_one : gamma 1 = y := by
      exact hv_end
    simpa only [hgamma_zero, hgamma_one, Real.norm_eq_abs] using hmv
  have htarget : ENNReal.ofReal |u y - u x| ≤
      ENNReal.ofReal ((L : ℝ) * (riemannianEDist I x y).toReal) :=
    ENNReal.ofReal_le_ofReal hreal
  rw [ENNReal.ofReal_mul (NNReal.coe_nonneg L),
    ENNReal.ofReal_toReal hfin] at htarget
  simpa only [edist_dist, Real.dist_eq, abs_sub_comm, riemannianEDistOf,
    ENNReal.coe_nnreal_eq] using htarget

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem lip_of_grad_norm_le
    [I.Boundaryless] [T2Space M] [T2Space (TangentBundle I M)]
    [SigmaCompactSpace M] [ConnectedSpace M]
    (g : SmoothRiemannianMetric I M)
    (hg : RiemannianMetricComplete (I := I) g)
    {u : M → ℝ} {L : ℝ≥0}
    (hu : ContMDiff I (modelWithCornersSelf ℝ ℝ)
      (↑(⊤ : ℕ∞) : WithTop ℕ∞) u)
    (hgrad : ∀ x : M,
      Real.sqrt (g.inner x (gradFun (I := I) g u x)
        (gradFun (I := I) g u x)) ≤ (L : ℝ)) :
    ∀ x y : M, edist (u x) (u y) ≤
      (L : ℝ≥0∞) * riemannianEDistOf (I := I) g x y := by
  classical
  by_cases hdim : Module.finrank ℝ E = 0
  · let _ : Subsingleton E :=
      (Module.finrank_zero_iff (R := ℝ) (M := E)).mp hdim
    let _ : Subsingleton H := I.injective.subsingleton
    let _ : DiscreteTopology M := ChartedSpace.discreteTopology H M
    let _ : Subsingleton M :=
      subsingleton_of_preconnected_totallyDisconnected
    intro x y
    rw [Subsingleton.elim y x]
    simp only [edist_self, riemannianEDistOf_self, mul_zero, le_refl]
  · let _ : NeZero (Module.finrank ℝ E) := ⟨hdim⟩
    exact lip_of_grad_norm_le_ne (I := I) g hg hu hgrad

open scoped ContDiff in
theorem exists_lipschitz_constant_of_smooth_compact_support
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [ConnectedSpace M] (g : SmoothRiemannianMetric I M) (hg : RiemannianMetricComplete g)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ) ∞ f) (hc : HasCompactSupport f) :
    ∃ C : ℝ≥0, ∀ x y, edist (f x) (f y) ≤ C * riemannianEDistOf g x y := by
  have hN : Continuous (fun x => Real.sqrt (normGradSqFun g f x)) :=
    Real.continuous_sqrt.comp (normGradSqFun_continuous g hf)
  obtain ⟨B, hB⟩ := hc.exists_bound_of_continuousOn hN.continuousOn
  refine ⟨⟨max B 0, le_max_right B 0⟩, lip_of_grad_norm_le g hg hf ?_⟩
  intro x
  by_cases hx : x ∈ tsupport f
  · exact ((le_abs_self _).trans (hB x hx)).trans (le_max_left B 0)
  · have hz : gradFun g f x = 0 := by
      by_contra hn
      exact hx (support_gradFun_subset g f hn)
    simp only [hz, map_zero, Real.sqrt_zero]
    exact le_max_right B 0


end Riemannian
end Geometry
end DifferentialGeometry

end
