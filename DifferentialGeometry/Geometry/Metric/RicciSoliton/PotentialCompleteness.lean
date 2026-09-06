import DifferentialGeometry.Analysis.ODE.LinearGrowthComplete
import DifferentialGeometry.Geometry.Metric.LipschitzGradient
import DifferentialGeometry.Geometry.Metric.RicciSoliton.ScalarLowerBound

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set
open scoped ContDiff ENNReal Manifold

namespace DifferentialGeometry.Geometry

open Connection Curvature Operator
open Riemannian
open Riemannian.Exponential

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E] [NeZero (Module.finrank Real E)]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [T2Space (TangentBundle I M)]
  [SigmaCompactSpace M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem gradientRicciSoliton_potential_gradient_linear_growth
    [ConnectedSpace M]
    (g : SmoothRiemannianMetric I M) (f : C^∞⟮I, M; Real⟯)
    (sigma : Real) (hcomplete : RiemannianMetricComplete (I := I) g)
    (hsol : gradientRicciSoliton (I := I) g f sigma) (p : M) :
    ∃ A : Real, 0 ≤ A ∧ ∀ x : M,
      Real.sqrt (g.inner x (gradFun (I := I) g f x)
        (gradFun (I := I) g f x)) ≤
        A * (1 + (riemannianEDistOf (I := I) g p x).toReal) := by
  classical
  let : RiemannianBundle (fun x : M => TangentSpace I x) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
    ⟨⟨g.inner, g.contMDiff.continuous, by intro x v w; rfl⟩⟩
  obtain ⟨C, hC⟩ := gradientRicciSoliton_hamilton_constant hsol
  let lower : Real :=
    min 0 ((Module.finrank Real E : Real) * sigma / 2)
  let q : M → Real := fun x => 1 + sigma * f x + C - lower
  let u : M → Real := fun x => Real.sqrt (q x)
  have hinner_nonneg (x : M) :
      0 ≤ g.inner x (gradFun (I := I) g f x)
        (gradFun (I := I) g f x) :=
    gInner_self_nonneg (I := I) g x (gradFun (I := I) g f x)
  have hq_identity (x : M) :
      q x = 1 + metricScalarAt (I := I) g x - lower +
        g.inner x (gradFun (I := I) g f x)
          (gradFun (I := I) g f x) := by
    dsimp only [q]
    linarith [hC x]
  have hq_lower (x : M) :
      1 + g.inner x (gradFun (I := I) g f x)
          (gradFun (I := I) g f x) ≤ q x := by
    rw [hq_identity]
    have hR := gradientRicciSoliton_scalar_lower_bound
      (I := I) g f sigma hcomplete hsol x
    dsimp only [lower]
    linarith
  have hq_pos (x : M) : 0 < q x := by
    have := hq_lower x
    nlinarith [hinner_nonneg x]
  have hq_smooth : ContMDiff I (modelWithCornersSelf Real Real)
      (↑(⊤ : ℕ∞) : WithTop ℕ∞) q := by
    dsimp only [q]
    exact (((contMDiff_const.add (contMDiff_const.mul f.contMDiff)).add
      contMDiff_const).sub contMDiff_const)
  have hu_smooth : ContMDiff I (modelWithCornersSelf Real Real)
      (↑(⊤ : ℕ∞) : WithTop ℕ∞) u := by
    intro x
    exact (Real.contDiffAt_sqrt (hq_pos x).ne').contMDiffAt.comp x
      (hq_smooth x)
  have hu_pos (x : M) : 0 < u x := by
    exact Real.sqrt_pos.2 (hq_pos x)
  have hu_sq (x : M) : u x ^ 2 = q x := by
    exact Real.sq_sqrt (hq_pos x).le
  have hgrad_q (x : M) :
      gradFun (I := I) g q x =
        sigma • gradFun (I := I) g f x := by
    have hf_diff : MDifferentiableAt I (modelWithCornersSelf Real Real) f x :=
      (f.contMDiff x).mdifferentiableAt (by simp)
    have hc_diff : MDifferentiableAt I (modelWithCornersSelf Real Real)
        (fun _ : M => 1 + C - lower) x :=
      mdifferentiableAt_const
    have hsigma_diff : MDifferentiableAt I (modelWithCornersSelf Real Real)
        (fun y : M => sigma * f y) x :=
      (mdifferentiableAt_const (c := sigma)).mul hf_diff
    rw [show q = fun y : M => (1 + C - lower) + sigma * f y by
      funext y
      dsimp only [q]
      ring]
    change gradFun (I := I) g
      ((fun _ : M => 1 + C - lower) + (fun y : M => sigma * f y)) x = _
    rw [Operator.gradFun_add (I := I) g hc_diff hsigma_diff,
      Operator.gradFun_const (I := I) g (1 + C - lower) x]
    have hscale := Operator.gradFun_const_smul (I := I) g sigma hf_diff
    change 0 + gradFun (I := I) g (sigma • (f : M → Real)) x = _
    rw [hscale, zero_add]
  have hgrad_u (x : M) :
      gradFun (I := I) g u x =
        (sigma / (2 * u x)) • gradFun (I := I) g f x := by
    have hq_diff : MDifferentiableAt I (modelWithCornersSelf Real Real) q x :=
      (hq_smooth x).mdifferentiableAt (by simp)
    have hsqrt_diff : DifferentiableAt Real Real.sqrt (q x) :=
      (Real.hasDerivAt_sqrt (hq_pos x).ne').differentiableAt
    have hcomp := Operator.gradFun_comp (I := I) g hsqrt_diff hq_diff
    calc
      gradFun (I := I) g u x =
          deriv Real.sqrt (q x) • gradFun (I := I) g q x := hcomp
      _ = (sigma / (2 * u x)) • gradFun (I := I) g f x := by
        rw [(Real.hasDerivAt_sqrt (hq_pos x).ne').deriv, hgrad_q,
          smul_smul]
        congr 1
        dsimp only [u]
        field_simp
  have hgrad_u_bound (x : M) :
      Real.sqrt (g.inner x (gradFun (I := I) g u x)
        (gradFun (I := I) g u x)) ≤ |sigma| / 2 := by
    let s : Real := Real.sqrt (g.inner x (gradFun (I := I) g f x)
      (gradFun (I := I) g f x))
    have hs_nonneg : 0 ≤ s := Real.sqrt_nonneg _
    have hs_le_u : s ≤ u x := by
      apply Real.sqrt_le_iff.mpr
      refine ⟨(hu_pos x).le, ?_⟩
      have hin_le : g.inner x (gradFun (I := I) g f x)
          (gradFun (I := I) g f x) ≤ q x := by
        linarith [hq_lower x]
      rw [hu_sq]
      exact hin_le
    have hnorm :
        Real.sqrt (g.inner x (gradFun (I := I) g u x)
          (gradFun (I := I) g u x)) =
          |sigma / (2 * u x)| * s := by
      rw [hgrad_u, gInner_smul_self (I := I) g x,
        Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq_eq_abs]
    rw [hnorm, abs_div, abs_of_pos (mul_pos (by norm_num) (hu_pos x))]
    have hcoeff : 0 ≤ |sigma| / (2 * u x) :=
      div_nonneg (abs_nonneg _) (mul_nonneg (by norm_num) (hu_pos x).le)
    calc
      |sigma| / (2 * u x) * s ≤
          |sigma| / (2 * u x) * u x :=
        mul_le_mul_of_nonneg_left hs_le_u hcoeff
      _ = |sigma| / 2 := by field_simp [(hu_pos x).ne']
  let K : NNReal := ⟨|sigma| / 2, div_nonneg (abs_nonneg _) (by norm_num)⟩
  have hu_lip : ∀ x y : M, edist (u x) (u y) ≤
      (K : ENNReal) * riemannianEDistOf (I := I) g x y := by
    apply lip_of_grad_norm_le (I := I) g hcomplete hu_smooth
    intro x
    change Real.sqrt (g.inner x (gradFun (I := I) g u x)
      (gradFun (I := I) g u x)) ≤ |sigma| / 2
    exact hgrad_u_bound x
  let A : Real := u p + |sigma| / 2
  refine ⟨A, add_nonneg (Real.sqrt_nonneg _) (div_nonneg (abs_nonneg _) (by norm_num)), ?_⟩
  intro x
  let d : Real := (riemannianEDistOf (I := I) g p x).toReal
  have hfin : riemannianEDistOf (I := I) g p x ≠ (∞ : ENNReal) :=
    riemannianEDist_ne_top (I := I) p x
  have hu_real : |u p - u x| ≤ (K : Real) * d := by
    have hrhs :
        (K : ENNReal) * riemannianEDistOf (I := I) g p x ≠
          (∞ : ENNReal) :=
      ENNReal.mul_ne_top ENNReal.coe_ne_top hfin
    have h := ENNReal.toReal_mono
      hrhs
      (hu_lip p x)
    rw [edist_dist, ENNReal.toReal_ofReal dist_nonneg,
      ENNReal.toReal_mul, ENNReal.coe_toReal,
      Real.dist_eq] at h
    simpa only [d] using h
  have hu_growth : u x ≤ u p + |sigma| / 2 * d := by
    have habs : u x - u p ≤ |u p - u x| :=
      le_abs_self (u x - u p) |>.trans_eq (abs_sub_comm (u x) (u p))
    change |u p - u x| ≤ (|sigma| / 2) * d at hu_real
    linarith
  have hgrad_le_u :
      Real.sqrt (g.inner x (gradFun (I := I) g f x)
        (gradFun (I := I) g f x)) ≤ u x := by
    apply Real.sqrt_le_iff.mpr
    refine ⟨(hu_pos x).le, ?_⟩
    have hin_le : g.inner x (gradFun (I := I) g f x)
        (gradFun (I := I) g f x) ≤ q x := by
      linarith [hq_lower x]
    simpa only [hu_sq] using hin_le
  have hd_nonneg : 0 ≤ d := ENNReal.toReal_nonneg
  calc
    Real.sqrt (g.inner x (gradFun (I := I) g f x)
        (gradFun (I := I) g f x)) ≤ u x := hgrad_le_u
    _ ≤ u p + |sigma| / 2 * d := hu_growth
    _ ≤ A * (1 + d) := by
      dsimp only [A]
      nlinarith [Real.sqrt_nonneg (q p), abs_nonneg sigma]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem gradientRicciSoliton_exists_globalIntegralCurve_potential
    [ConnectedSpace M]
    (g : SmoothRiemannianMetric I M) (f : C^∞⟮I, M; Real⟯)
    (sigma : Real) (hcomplete : RiemannianMetricComplete (I := I) g)
    (hsol : gradientRicciSoliton (I := I) g f sigma) :
    ∀ x : M, ∃ gamma : Real → M,
      gamma 0 = x ∧
        IsMIntegralCurve gamma (fun y => gradFun (I := I) g f y) := by
  let v : (x : M) → TangentSpace I x :=
    fun x => gradFun (I := I) g f x
  have hv : ContMDiff I (I.prod (modelWithCornersSelf Real E))
      (↑(⊤ : ℕ∞) : WithTop ℕ∞)
      (fun x : M => (⟨x, v x⟩ : TangentBundle I M)) :=
    gradFun_contMDiff_total_section (I := I) g f.contMDiff
  let p : M := Classical.choice inferInstance
  obtain ⟨A, hA, hgrowth⟩ :=
    gradientRicciSoliton_potential_gradient_linear_growth
      (I := I) g f sigma hcomplete hsol p
  exact DifferentialGeometry.Analysis.ODE.exists_globalIntegralCurve_of_linearGrowth
    (I := I) g hcomplete v hv p hA hgrowth

end DifferentialGeometry.Geometry

end
