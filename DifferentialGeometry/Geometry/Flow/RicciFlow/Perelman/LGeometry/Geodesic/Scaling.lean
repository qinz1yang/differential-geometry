import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Geodesic.ExponentialMap
import DifferentialGeometry.Geometry.Flow.RicciFlow.Scaling.Parabolic
import DifferentialGeometry.Geometry.Connection.ParallelTransport.CovariantDerivativeScaling

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open Bundle Set
open scoped Manifold ContDiff Topology Pointwise

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
  [InnerProductSpace Real E] [FiniteDimensional Real E]
  [NeZero (Module.finrank Real E)]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]
variable {D : RealTimeInterval}

private lemma sqrtR_pos {R : Real} (hR : 0 < R) :
    0 < Real.sqrt R :=
  Real.sqrt_pos.2 hR

private lemma sqrtR_sq {R : Real} (hR : 0 < R) :
    (Real.sqrt R) ^ 2 = R :=
  Real.sq_sqrt hR.le

private lemma para_reg_time
    (t0 R T s : Real) (hR : 0 < R) :
    paraTime t0 R (paraBack t0 R T - (Real.sqrt R * s) ^ 2) =
      T - s ^ 2 := by
  rw [show (Real.sqrt R * s) ^ 2 = R * s ^ 2 by
    rw [mul_pow, sqrtR_sq hR]]
  unfold paraTime paraBack
  field_simp [ne_of_gt hR]
  ring

private lemma para_reg_time_inv
    (t0 R T r : Real) (hR : 0 < R) :
    paraTime t0 R (paraBack t0 R T - r ^ 2) =
      T - ((Real.sqrt R)⁻¹ * r) ^ 2 := by
  have hc : Real.sqrt R ≠ 0 := ne_of_gt (sqrtR_pos hR)
  have hsqrtSq : (Real.sqrt R) ^ 2 = R := sqrtR_sq hR
  unfold paraTime paraBack
  field_simp [ne_of_gt hR, hc]
  nlinarith

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [InnerProductSpace Real E] [FiniteDimensional Real E]
  [NeZero (Module.finrank Real E)] [SigmaCompactSpace M]
  [I.Boundaryless] [IsManifold I ∞ M] [T2Space M] in
private theorem lVelocity_mul
    (alpha : Real → M) (c : Real) (hc : c ≠ 0) (s : Real) :
    lVelocity (I := I) (fun r => alpha (c * r)) s =
      c • lVelocity (I := I) alpha (c * s) := by
  by_cases halpha :
      MDifferentiableAt (modelWithCornersSelf Real Real) I alpha (c * s)
  · let A : TangentSpace (modelWithCornersSelf Real Real) s →L[Real]
        TangentSpace (modelWithCornersSelf Real Real) (c * s) :=
      modelLinearMapToTangent
        (x := s) (y := c * s) (A := c • ContinuousLinearMap.id Real Real)
    have hscaleM : HasMFDerivAt (modelWithCornersSelf Real Real)
        (modelWithCornersSelf Real Real) (fun r : Real => c * r) s A := by
      exact HasFDerivAt.hasMFDerivAt_model
        ((hasFDerivAt_id s).const_mul c)
    have hcomp := halpha.hasMFDerivAt.comp s hscaleM
    have hmodel := congrArg tangentLinearMapToModel hcomp.mfderiv
    rw [tangentLinearMapToModel_comp] at hmodel
    have hA : tangentLinearMapToModel A =
        c • ContinuousLinearMap.id Real Real := by
      exact tangentLinearMapToModel_modelLinearMapToTangent
    rw [hA] at hmodel
    have happ := congrArg (fun L : Real →L[Real] E => L 1) hmodel
    have hfun : (alpha ∘ fun r : Real => c * r) =
        (fun r : Real => alpha (c * r)) := by
      rfl
    rw [hfun] at happ
    apply (tangentSpaceModelContinuousLinearEquiv
      (I := I) (alpha (c * s))).injective
    simpa only [lVelocity, tangentLinearMapToModel_apply,
      tangentSpaceModelContinuousLinearEquiv_apply,
      tangentSpaceModelContinuousLinearEquiv_symm_apply,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply,
      Function.comp_apply, smul_apply, id_eq, map_smul] using happ
  · have hcomp : ¬MDifferentiableAt (modelWithCornersSelf Real Real) I
        (fun r => alpha (c * r)) s := by
      intro hcurve
      let beta : Real → M := fun r => alpha (c * r)
      have hcurve' : MDifferentiableAt (modelWithCornersSelf Real Real) I beta
          (c⁻¹ * (c * s)) := by
        simpa only [beta, inv_mul_cancel_left₀ hc] using hcurve
      have hinv : MDifferentiableAt (modelWithCornersSelf Real Real)
          (modelWithCornersSelf Real Real) (fun r : Real => c⁻¹ * r) (c * s) := by
        exact mdifferentiableAt_iff_differentiableAt.mpr
          ((differentiableAt_const c⁻¹).mul differentiableAt_id)
      have hback := hcurve'.comp (c * s) hinv
      have heq : beta ∘ (fun r : Real => c⁻¹ * r) = alpha := by
        funext r
        simp only [beta, Function.comp_apply]
        field_simp [hc]
      rw [heq] at hback
      exact halpha hback
    simp only [lVelocity, mfderiv_zero_of_not_mdifferentiableAt hcomp,
      mfderiv_zero_of_not_mdifferentiableAt halpha]
    change (0 : E) = c • (0 : E)
    simp

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [InnerProductSpace Real E] [NeZero (Module.finrank Real E)]
  [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
private theorem gradientFun_smul_ne
    (g : SmoothRiemannianMetric I M) (a : Real) (ha : a ≠ 0)
    (f : M → Real) (x : M) :
    gradientFun (I := I) g (a • f) x =
      a • gradientFun (I := I) g f x := by
  by_cases hf : MDifferentiableAt I (modelWithCornersSelf Real Real) f x
  · exact gradientFun_const_smul (I := I) g a hf
  · have haf : ¬MDifferentiableAt I (modelWithCornersSelf Real Real) (a • f) x := by
      intro haf
      have hinv := haf.const_smul a⁻¹
      apply hf
      simpa only [smul_smul, inv_mul_cancel₀ ha, one_smul] using hinv
    have hzaf : gradientFun (I := I) g (a • f) x = 0 :=
      gradientFun_eq_zero_of_mfderiv_eq_zero (I := I) g (a • f)
        (mfderiv_zero_of_not_mdifferentiableAt haf)
    have hzf : gradientFun (I := I) g f x = 0 :=
      gradientFun_eq_zero_of_mfderiv_eq_zero (I := I) g f
        (mfderiv_zero_of_not_mdifferentiableAt hf)
    rw [hzaf, hzf, smul_zero]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [InnerProductSpace Real E] [NeZero (Module.finrank Real E)]
  [SigmaCompactSpace M] in
theorem lRegAccel_para
    (S : SolutionOn (I := I) (M := M) D)
    (t0 R : Real) (hR : 0 < R) (ht0 : t0 ∈ D.carrier)
    (T s : Real) (x : M) (A : TangentSpace I x) :
    lRegAccel (paraSolution (I := I) S t0 R hR ht0)
        (paraBack t0 R T) (Real.sqrt R * s) x
        ((Real.sqrt R)⁻¹ • A) =
      R⁻¹ • lRegAccel S T s x A := by
  let SR := paraSolution (I := I) S t0 R hR ht0
  let TR := paraBack t0 R T
  let g := S.base.metric (T - s ^ 2)
  let gR := SR.base.metric (TR - (Real.sqrt R * s) ^ 2)
  have htime : paraTime t0 R (TR - (Real.sqrt R * s) ^ 2) =
      T - s ^ 2 := para_reg_time t0 R T s hR
  have hgR : gR = scaleMetric (I := I) R hR g := by
    simp only [gR, SR, TR, paraSolution_metric, htime, g]
  apply metricFlatLinear_injective (I := I) gR x
  ext Y
  rw [metricFlatLinear_apply, metricFlatLinear_apply]
  rw [gR.symm x _ Y, gR.symm x _ Y]
  have hscalar :
      SR.scalar (TR - (Real.sqrt R * s) ^ 2) =
        R⁻¹ • S.scalar (T - s ^ 2) := by
    funext y
    simp only [SR, TR, paraSolution_scalar, htime,
      Pi.smul_apply, smul_eq_mul]
  have hgrad :
      gradientFun (I := I) gR
          (SR.scalar (TR - (Real.sqrt R * s) ^ 2)) x =
        (R⁻¹ * R⁻¹) •
          gradientFun (I := I) g (S.scalar (T - s ^ 2)) x := by
    rw [hscalar, hgR, gradientFun_scale]
    rw [gradientFun_smul_ne (I := I) g R⁻¹ (inv_ne_zero (ne_of_gt hR))]
    simp only [smul_smul]
  have hric :
      SR.ricciAt (TR - (Real.sqrt R * s) ^ 2) x
          (vec2 Y ((Real.sqrt R)⁻¹ • A)) =
        (Real.sqrt R)⁻¹ * S.ricciAt (T - s ^ 2) x (vec2 Y A) := by
    change SR.base.ricciAt (TR - (Real.sqrt R * s) ^ 2) x
        (vec2 Y ((Real.sqrt R)⁻¹ • A)) = _
    rw [show SR.base.ricciAt (TR - (Real.sqrt R * s) ^ 2) =
        S.base.ricciAt (T - s ^ 2) by
      have hsec := congrFun
        (paraSolution_ricci (I := I) S t0 R hR ht0)
        (TR - (Real.sqrt R * s) ^ 2)
      funext y
      have hy := congrArg (fun q => q y) hsec
      simpa only [SolutionFamily.ricci_apply, htime] using hy]
    have hleft : Function.update (vec2 Y A) (1 : Fin 2)
        ((Real.sqrt R)⁻¹ • A) = vec2 Y ((Real.sqrt R)⁻¹ • A) := by
      funext i
      fin_cases i <;> simp [vec2]
    have hright : Function.update (vec2 Y A) (1 : Fin 2) A = vec2 Y A := by
      funext i
      fin_cases i <;> simp [vec2]
    have hmap := (S.base.ricciAt (T - s ^ 2) x).map_update_smul
      (vec2 Y A) (1 : Fin 2) (Real.sqrt R)⁻¹ A
    rw [hleft, hright] at hmap
    simpa only [smul_eq_mul, SolutionOn.ricciAt] using hmap
  have hleft := lRegAccel_inner SR TR (Real.sqrt R * s) x
    ((Real.sqrt R)⁻¹ • A) Y
  have hold := lRegAccel_inner S T s x A Y
  have hright :
      gR.inner x Y (R⁻¹ • lRegAccel S T s x A) =
        g.inner x Y (lRegAccel S T s x A) := by
    rw [(gR.inner x Y).map_smul, hgR, scaleMetric_inner]
    simp only [smul_eq_mul]
    field_simp [ne_of_gt hR]
  rw [hleft, hright, hold]
  rw [show SR.base.metric (TR - (Real.sqrt R * s) ^ 2) = gR by rfl]
  rw [hgrad, hgR, scaleMetric_inner, hric]
  rw [show S.base.metric (T - s ^ 2) = g by rfl]
  simp only [map_smul, smul_apply, smul_eq_mul]
  have hsqrt0 : Real.sqrt R ≠ 0 := ne_of_gt (sqrtR_pos hR)
  have hsqrtSq : (Real.sqrt R) ^ 2 = R := sqrtR_sq hR
  field_simp [ne_of_gt hR, hsqrt0]
  rw [hsqrtSq]
  ring

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [InnerProductSpace Real E] [NeZero (Module.finrank Real E)]
  [SigmaCompactSpace M] in
theorem isLRegCurve_para
    (S : SolutionOn (I := I) (M := M) D)
    (t0 R : Real) (hR : 0 < R) (ht0 : t0 ∈ D.carrier)
    (T : Real) {alpha : Real → M} {J : Set Real} {x : M}
    {Z : TangentSpace I x}
    (halpha : IsLRegCurveOn S T alpha J x Z) :
    IsLRegCurveOn (paraSolution (I := I) S t0 R hR ht0)
      (paraBack t0 R T)
      (fun r => alpha ((Real.sqrt R)⁻¹ * r))
      (Real.sqrt R • J) x ((Real.sqrt R)⁻¹ • Z) := by
  let c := Real.sqrt R
  let ci := c⁻¹
  let SR := paraSolution (I := I) S t0 R hR ht0
  let TR := paraBack t0 R T
  let alphaR : Real → M := fun r => alpha (ci * r)
  have hc : c ≠ 0 := ne_of_gt (sqrtR_pos hR)
  have hci : ci ≠ 0 := inv_ne_zero hc
  have hstart : alphaR 0 = x := by
    simpa only [alphaR, mul_zero] using halpha.1
  have hvel : lVelocity (I := I) alphaR 0 = 2 • (ci • Z) := by
    rw [show lVelocity (I := I) alphaR 0 =
        ci • lVelocity (I := I) alpha (ci * 0) by
      simpa only [alphaR] using lVelocity_mul (I := I) alpha ci hci 0]
    rw [mul_zero, halpha.2.1]
    exact smul_comm ci (2 : Nat) Z
  refine ⟨hstart, hvel, ?_⟩
  intro r hr
  have hs : ci * r ∈ J := by
    have := (Set.mem_smul_set_iff_inv_smul_mem₀ hc J r).mp hr
    simpa only [c, ci, smul_eq_mul] using this
  obtain ⟨hreg, hmdiff, hrepDiff, heq⟩ := halpha.2.2 (ci * r) hs
  have htime : paraTime t0 R (TR - r ^ 2) = T - (ci * r) ^ 2 := by
    simpa only [TR, c, ci] using para_reg_time_inv t0 R T r hR
  have hregR : TR - r ^ 2 ∈ (paraInterval D t0 R ht0).regular := by
    change paraTime t0 R (TR - r ^ 2) ∈ D.regular
    rwa [htime]
  have hparam : MDifferentiableAt (modelWithCornersSelf Real Real)
      (modelWithCornersSelf Real Real) (fun q : Real => ci * q) r := by
    exact mdifferentiableAt_iff_differentiableAt.mpr
      ((differentiableAt_const ci).mul differentiableAt_id)
  have hmdiffR : MDifferentiableAt (modelWithCornersSelf Real Real) I alphaR r := by
    change MDifferentiableAt (modelWithCornersSelf Real Real) I
      (alpha ∘ fun q : Real => ci * q) r
    exact hmdiff.comp r hparam
  have hvelAll : ∀ q : Real,
      lVelocity (I := I) alphaR q =
        ci • lVelocity (I := I) alpha (ci * q) := by
    intro q
    simpa only [alphaR] using lVelocity_mul (I := I) alpha ci hci q
  have hrep :
      chartRepAt (I := I) alphaR
          (fun q => lVelocity (I := I) alphaR q) r =
        fun q => ci • chartRepAt (I := I) alpha
          (fun u => lVelocity (I := I) alpha u) (ci * r) (ci * q) := by
    funext q
    rw [chartRepAt_apply, chartRepAt_apply, hvelAll q]
    simp only [alphaR]
    rw [map_smul]
  have hrepDiffR : DifferentiableAt Real
      (chartRepAt (I := I) alphaR
        (fun q => lVelocity (I := I) alphaR q) r) r := by
    rw [hrep]
    exact (hrepDiff.comp r (by fun_prop)).const_smul ci
  refine ⟨hregR, hmdiffR, hrepDiffR, ?_⟩
  have hmetric : SR.base.metric (TR - r ^ 2) =
      scaleMetric (I := I) R hR (S.base.metric (T - (ci * r) ^ 2)) := by
    simp only [SR, paraSolution_metric, htime]
  have hrform : r = c * (ci * r) := by
    simp [ci, hc]
  have hcomp :
      covDerivAlong (I := I) (S.base.metric (T - (ci * r) ^ 2)) alphaR
          (fun q => lVelocity (I := I) alpha (ci * q)) r =
        ci • covDerivAlong (I := I) (S.base.metric (T - (ci * r) ^ 2))
          alpha (fun q => lVelocity (I := I) alpha q) (ci * r) := by
    simpa only [alphaR] using
      covDeriv_comp_mul (I := I) (S.base.metric (T - (ci * r) ^ 2))
        alpha (fun q => lVelocity (I := I) alpha q) ci r
  have hciSq : ci * ci = R⁻¹ := by
    dsimp only [ci, c]
    have hsqrtSq : (Real.sqrt R) ^ 2 = R := sqrtR_sq hR
    field_simp [hc, ne_of_gt hR]
    nlinarith
  have hcov :
      covDerivAlong (I := I) (SR.base.metric (TR - r ^ 2)) alphaR
          (fun q => lVelocity (I := I) alphaR q) r =
        R⁻¹ • lRegAccel S T (ci * r) (alpha (ci * r))
          (lVelocity (I := I) alpha (ci * r)) := by
    calc
      _ = covDerivAlong (I := I)
          (scaleMetric (I := I) R hR (S.base.metric (T - (ci * r) ^ 2)))
          alphaR (fun q => lVelocity (I := I) alphaR q) r := by rw [hmetric]
      _ = covDerivAlong (I := I) (S.base.metric (T - (ci * r) ^ 2))
          alphaR (fun q => lVelocity (I := I) alphaR q) r :=
        covDerivAlong_scale (I := I) R hR _ _ _ r
      _ = covDerivAlong (I := I) (S.base.metric (T - (ci * r) ^ 2))
          alphaR (fun q => ci • lVelocity (I := I) alpha (ci * q)) r := by
        congr 1
        funext q
        exact hvelAll q
      _ = ci • covDerivAlong (I := I) (S.base.metric (T - (ci * r) ^ 2))
          alphaR (fun q => lVelocity (I := I) alpha (ci * q)) r :=
        covDerivAlong_smul (I := I) _ _ ci _ r
      _ = ci • (ci • covDerivAlong (I := I)
          (S.base.metric (T - (ci * r) ^ 2)) alpha
          (fun q => lVelocity (I := I) alpha q) (ci * r)) := by rw [hcomp]
      _ = ci • (ci • lRegAccel S T (ci * r) (alpha (ci * r))
          (lVelocity (I := I) alpha (ci * r))) := by rw [heq]
      _ = R⁻¹ • lRegAccel S T (ci * r) (alpha (ci * r))
          (lVelocity (I := I) alpha (ci * r)) := by
        rw [smul_smul, hciSq]
  have hpoint : alphaR r = alpha (ci * r) := rfl
  have hvelr : lVelocity (I := I) alphaR r =
      ci • lVelocity (I := I) alpha (ci * r) := hvelAll r
  have hacc :
      lRegAccel SR TR r (alphaR r) (lVelocity (I := I) alphaR r) =
        R⁻¹ • lRegAccel S T (ci * r) (alpha (ci * r))
          (lVelocity (I := I) alpha (ci * r)) := by
    rw [hpoint, hvelr]
    have hbase := lRegAccel_para (I := I) S t0 R hR ht0 T (ci * r)
      (alpha (ci * r)) (lVelocity (I := I) alpha (ci * r))
    rw [← hrform] at hbase
    simpa only [SR, TR, c, ci] using hbase
  change covDerivAlong (I := I) (SR.base.metric (TR - r ^ 2)) alphaR
      (fun q => lVelocity (I := I) alphaR q) r =
    lRegAccel SR TR r (alphaR r) (lVelocity (I := I) alphaR r)
  exact hcov.trans hacc.symm

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [InnerProductSpace Real E] [NeZero (Module.finrank Real E)]
  [SigmaCompactSpace M] in
theorem isLRegCurve_unpara
    (S : SolutionOn (I := I) (M := M) D)
    (t0 R : Real) (hR : 0 < R) (ht0 : t0 ∈ D.carrier)
    (T : Real) {beta : Real → M} {K : Set Real} {x : M}
    {W : TangentSpace I x}
    (hbeta : IsLRegCurveOn
      (paraSolution (I := I) S t0 R hR ht0) (paraBack t0 R T)
      beta K x W) :
    IsLRegCurveOn S T (fun s => beta (Real.sqrt R * s))
      ((Real.sqrt R)⁻¹ • K) x (Real.sqrt R • W) := by
  let c := Real.sqrt R
  let ci := c⁻¹
  let SR := paraSolution (I := I) S t0 R hR ht0
  let TR := paraBack t0 R T
  let alpha : Real → M := fun s => beta (c * s)
  have hc : c ≠ 0 := ne_of_gt (sqrtR_pos hR)
  have hci : ci ≠ 0 := inv_ne_zero hc
  have hstart : alpha 0 = x := by
    simpa only [alpha, mul_zero] using hbeta.1
  have hvel : lVelocity (I := I) alpha 0 = 2 • (c • W) := by
    rw [show lVelocity (I := I) alpha 0 =
        c • lVelocity (I := I) beta (c * 0) by
      simpa only [alpha] using lVelocity_mul (I := I) beta c hc 0]
    rw [mul_zero, hbeta.2.1]
    exact smul_comm c (2 : Nat) W
  refine ⟨hstart, hvel, ?_⟩
  intro s hs
  have hr : c * s ∈ K := by
    have hmem := (Set.mem_smul_set_iff_inv_smul_mem₀ hci K s).mp hs
    simpa only [ci, inv_inv, smul_eq_mul] using hmem
  obtain ⟨hregR, hmdiff, hrepDiff, heq⟩ := hbeta.2.2 (c * s) hr
  have htime : paraTime t0 R (TR - (c * s) ^ 2) = T - s ^ 2 := by
    simpa only [TR, c] using para_reg_time t0 R T s hR
  have hreg : T - s ^ 2 ∈ D.regular := by
    change paraTime t0 R (TR - (c * s) ^ 2) ∈ D.regular at hregR
    rwa [htime] at hregR
  have hparam : MDifferentiableAt (modelWithCornersSelf Real Real)
      (modelWithCornersSelf Real Real) (fun q : Real => c * q) s := by
    exact mdifferentiableAt_iff_differentiableAt.mpr
      ((differentiableAt_const c).mul differentiableAt_id)
  have hmdiffA : MDifferentiableAt (modelWithCornersSelf Real Real) I alpha s := by
    change MDifferentiableAt (modelWithCornersSelf Real Real) I
      (beta ∘ fun q : Real => c * q) s
    exact hmdiff.comp s hparam
  have hvelAll : ∀ q : Real,
      lVelocity (I := I) alpha q =
        c • lVelocity (I := I) beta (c * q) := by
    intro q
    simpa only [alpha] using lVelocity_mul (I := I) beta c hc q
  have hrep :
      chartRepAt (I := I) alpha
          (fun q => lVelocity (I := I) alpha q) s =
        fun q => c • chartRepAt (I := I) beta
          (fun u => lVelocity (I := I) beta u) (c * s) (c * q) := by
    funext q
    rw [chartRepAt_apply, chartRepAt_apply, hvelAll q]
    simp only [alpha]
    rw [map_smul]
  have hrepDiffA : DifferentiableAt Real
      (chartRepAt (I := I) alpha
        (fun q => lVelocity (I := I) alpha q) s) s := by
    rw [hrep]
    exact (hrepDiff.comp s (by fun_prop)).const_smul c
  refine ⟨hreg, hmdiffA, hrepDiffA, ?_⟩
  have hmetric : SR.base.metric (TR - (c * s) ^ 2) =
      scaleMetric (I := I) R hR (S.base.metric (T - s ^ 2)) := by
    simp only [SR, paraSolution_metric, htime]
  have hcomp :
      covDerivAlong (I := I) (S.base.metric (T - s ^ 2)) alpha
          (fun q => lVelocity (I := I) beta (c * q)) s =
        c • covDerivAlong (I := I) (S.base.metric (T - s ^ 2)) beta
          (fun q => lVelocity (I := I) beta q) (c * s) := by
    simpa only [alpha] using
      covDeriv_comp_mul (I := I) (S.base.metric (T - s ^ 2))
        beta (fun q => lVelocity (I := I) beta q) c s
  have hcSq : c * c = R := by
    simpa only [c, pow_two] using sqrtR_sq hR
  have hcov :
      covDerivAlong (I := I) (S.base.metric (T - s ^ 2)) alpha
          (fun q => lVelocity (I := I) alpha q) s =
        R • lRegAccel SR TR (c * s) (beta (c * s))
          (lVelocity (I := I) beta (c * s)) := by
    calc
      _ = covDerivAlong (I := I) (S.base.metric (T - s ^ 2)) alpha
          (fun q => c • lVelocity (I := I) beta (c * q)) s := by
        congr 1
        funext q
        exact hvelAll q
      _ = c • covDerivAlong (I := I) (S.base.metric (T - s ^ 2)) alpha
          (fun q => lVelocity (I := I) beta (c * q)) s :=
        covDerivAlong_smul (I := I) _ _ c _ s
      _ = c • (c • covDerivAlong (I := I) (S.base.metric (T - s ^ 2)) beta
          (fun q => lVelocity (I := I) beta q) (c * s)) := by rw [hcomp]
      _ = R • covDerivAlong (I := I) (SR.base.metric (TR - (c * s) ^ 2)) beta
          (fun q => lVelocity (I := I) beta q) (c * s) := by
        rw [smul_smul, hcSq]
        congr 1
        rw [hmetric]
        exact (covDerivAlong_scale (I := I) R hR _ _ _ (c * s)).symm
      _ = R • lRegAccel SR TR (c * s) (beta (c * s))
          (lVelocity (I := I) beta (c * s)) := by rw [heq]
  have hpoint : alpha s = beta (c * s) := rfl
  have hvels : lVelocity (I := I) alpha s =
      c • lVelocity (I := I) beta (c * s) := hvelAll s
  have hbase := lRegAccel_para (I := I) S t0 R hR ht0 T s
    (beta (c * s)) (lVelocity (I := I) alpha s)
  have hciVel : ci • lVelocity (I := I) alpha s =
      lVelocity (I := I) beta (c * s) := by
    rw [hvels, smul_smul]
    simp only [ci, inv_mul_cancel₀ hc, one_smul]
  have hbase' :
      lRegAccel SR TR (c * s) (beta (c * s))
          (lVelocity (I := I) beta (c * s)) =
        R⁻¹ • lRegAccel S T s (beta (c * s))
          (lVelocity (I := I) alpha s) := by
    simpa only [SR, TR, c, ci, hciVel] using hbase
  have hacc :
      lRegAccel S T s (alpha s) (lVelocity (I := I) alpha s) =
        R • lRegAccel SR TR (c * s) (beta (c * s))
          (lVelocity (I := I) beta (c * s)) := by
    rw [hpoint, hbase', smul_smul]
    simp only [mul_inv_cancel₀ (ne_of_gt hR), one_smul]
  change covDerivAlong (I := I) (S.base.metric (T - s ^ 2)) alpha
      (fun q => lVelocity (I := I) alpha q) s =
    lRegAccel S T s (alpha s) (lVelocity (I := I) alpha s)
  exact hcov.trans hacc.symm

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [InnerProductSpace Real E] [NeZero (Module.finrank Real E)]
  [SigmaCompactSpace M] in
theorem lRegDomain_para
    (S : SolutionOn (I := I) (M := M) D)
    (t0 R : Real) (hR : 0 < R) (ht0 : t0 ∈ D.carrier)
    (T : Real) (x : M) (Z : TangentSpace I x) :
    lRegDomain (paraSolution (I := I) S t0 R hR ht0)
        (paraBack t0 R T) x ((Real.sqrt R)⁻¹ • Z) =
      Real.sqrt R • lRegDomain S T x Z := by
  let c := Real.sqrt R
  let ci := c⁻¹
  let SR := paraSolution (I := I) S t0 R hR ht0
  let TR := paraBack t0 R T
  have hc : c ≠ 0 := ne_of_gt (sqrtR_pos hR)
  have hci : ci ≠ 0 := inv_ne_zero hc
  ext r
  constructor
  · intro hr
    obtain ⟨beta, K, hKopen, hKconn, h0K, hrK, hbeta⟩ := hr
    apply (Set.mem_smul_set_iff_inv_smul_mem₀ hc (lRegDomain S T x Z) r).2
    have hcurve : IsLRegCurveOn S T (fun s => beta (c * s))
        (ci • K) x Z := by
      simpa only [SR, TR, c, ci, smul_smul, mul_inv_cancel₀ hc, one_smul] using
        isLRegCurve_unpara (I := I) S t0 R hR ht0 T hbeta
    refine ⟨fun s => beta (c * s), ci • K, hKopen.smul₀ hci, ?_, ?_, ?_, hcurve⟩
    · rw [← Set.image_smul]
      exact hKconn.image (fun s : Real => ci • s)
        (continuous_const_smul ci).continuousOn
    · exact (Set.zero_mem_smul_set_iff hci).2 h0K
    · simpa only [smul_eq_mul] using
        (Set.smul_mem_smul_set_iff₀ hci K r).2 hrK
  · intro hr
    have hs : ci * r ∈ lRegDomain S T x Z := by
      have := (Set.mem_smul_set_iff_inv_smul_mem₀ hc
        (lRegDomain S T x Z) r).1 hr
      simpa only [c, ci, smul_eq_mul] using this
    obtain ⟨alpha, J, hJopen, hJconn, h0J, hsJ, halpha⟩ := hs
    have hcurve := isLRegCurve_para (I := I) S t0 R hR ht0 T halpha
    refine ⟨fun q => alpha (ci * q), c • J, hJopen.smul₀ hc, ?_, ?_, ?_, ?_⟩
    · rw [← Set.image_smul]
      exact hJconn.image (fun s : Real => c • s)
        (continuous_const_smul c).continuousOn
    · exact (Set.zero_mem_smul_set_iff hc).2 h0J
    · exact (Set.mem_smul_set_iff_inv_smul_mem₀ hc J r).2 (by
        simpa only [c, ci, smul_eq_mul] using hsJ)
    · simpa only [SR, TR, c, ci] using hcurve

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [InnerProductSpace Real E] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem lRegCurve_para
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (t0 R : Real) (hR : 0 < R) (ht0 : t0 ∈ D.carrier)
    (T : Real) (x : M) (Z : TangentSpace I x) (s : Real) :
    lRegCurve (paraSolution (I := I) S t0 R hR ht0)
        (paraBack t0 R T) x ((Real.sqrt R)⁻¹ • Z) (Real.sqrt R * s) =
      lRegCurve S T x Z s := by
  let c := Real.sqrt R
  let ci := c⁻¹
  let SR := paraSolution (I := I) S t0 R hR ht0
  let TR := paraBack t0 R T
  have hc : c ≠ 0 := ne_of_gt (sqrtR_pos hR)
  have hSR : IsSolutionOn (I := I) SR := by
    simpa only [SR] using paraSol (I := I) S hS t0 R hR ht0
  by_cases hs : s ∈ lRegDomain S T x Z
  · obtain ⟨alpha, J, hJopen, hJconn, h0J, hsJ, halpha⟩ := hs
    have hcurve := isLRegCurve_para (I := I) S t0 R hR ht0 T halpha
    have hJconnR : IsPreconnected (c • J) := by
      rw [← Set.image_smul]
      exact hJconn.image (fun q : Real => c • q)
        (continuous_const_smul c).continuousOn
    have h0JR : (0 : Real) ∈ c • J :=
      (Set.zero_mem_smul_set_iff hc).2 h0J
    have hsJR : c * s ∈ c • J := by
      simpa only [smul_eq_mul] using
        (Set.smul_mem_smul_set_iff₀ hc J s).2 hsJ
    have hscaled := lRegCurve_eqOn SR hSR TR (hJopen.smul₀ hc)
      hJconnR h0JR (by simpa only [SR, TR, c, ci] using hcurve) hsJR
    have horig := lRegCurve_eqOn S hS T hJopen hJconn h0J halpha hsJ
    calc
      lRegCurve SR TR x (ci • Z) (c * s) = alpha (ci * (c * s)) := by
        simpa only [SR, TR, c, ci] using hscaled
      _ = alpha s := by simp only [ci, inv_mul_cancel_left₀ hc]
      _ = lRegCurve S T x Z s := horig.symm
  · have hsR : c * s ∉ lRegDomain SR TR x (ci • Z) := by
      rw [lRegDomain_para (I := I) S t0 R hR ht0 T x Z]
      intro hmem
      have hs' : c • s ∈ c • lRegDomain S T x Z := by
        simpa only [smul_eq_mul] using hmem
      exact hs ((Set.smul_mem_smul_set_iff₀ hc (lRegDomain S T x Z) s).1 hs')
    rw [lRegCurve_of_not_mem hsR, lRegCurve_of_not_mem hs]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [InnerProductSpace Real E] [NeZero (Module.finrank Real E)]
  [SigmaCompactSpace M] in
theorem lExpDomain_para
    (S : SolutionOn (I := I) (M := M) D)
    (t0 R : Real) (hR : 0 < R) (ht0 : t0 ∈ D.carrier)
    (T : Real) (x : M) (Z : TangentSpace I x) (tau : Real) :
    R * tau ∈ lExpDomain (paraSolution (I := I) S t0 R hR ht0)
        (paraBack t0 R T) x ((Real.sqrt R)⁻¹ • Z) ↔
      tau ∈ lExpDomain S T x Z := by
  let c := Real.sqrt R
  let ci := c⁻¹
  let SR := paraSolution (I := I) S t0 R hR ht0
  let TR := paraBack t0 R T
  have hc : c ≠ 0 := ne_of_gt (sqrtR_pos hR)
  have hsqrt : Real.sqrt (R * tau) = c * Real.sqrt tau := by
    simpa only [c] using Real.sqrt_mul hR.le tau
  simp only [lExpDomain, mem_ofPred_eq]
  rw [show lRegDomain SR TR x (ci • Z) =
      c • lRegDomain S T x Z by
    simpa only [SR, TR, c, ci] using
      lRegDomain_para (I := I) S t0 R hR ht0 T x Z]
  constructor
  · rintro ⟨hRtau, hdom⟩
    have htau : 0 ≤ tau := (mul_nonneg_iff_of_pos_left hR).1 hRtau
    have hmem := (Set.mem_smul_set_iff_inv_smul_mem₀ hc
      (lRegDomain S T x Z) (Real.sqrt (R * tau))).1 hdom
    rw [hsqrt] at hmem
    have hdom' : Real.sqrt tau ∈ lRegDomain S T x Z := by
      simpa only [smul_eq_mul, inv_mul_cancel_left₀ hc] using hmem
    exact ⟨htau, hdom'⟩
  · rintro ⟨htau, hdom⟩
    refine ⟨mul_nonneg hR.le htau, ?_⟩
    rw [hsqrt]
    simpa only [smul_eq_mul] using
      (Set.smul_mem_smul_set_iff₀ hc (lRegDomain S T x Z)
        (Real.sqrt tau)).2 hdom

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [InnerProductSpace Real E] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem lExp_para
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (t0 R : Real) (hR : 0 < R) (ht0 : t0 ∈ D.carrier)
    (T : Real) (x : M) (Z : TangentSpace I x) (tau : Real) :
    lExp (paraSolution (I := I) S t0 R hR ht0)
        (paraBack t0 R T) x ((Real.sqrt R)⁻¹ • Z) (R * tau) =
      lExp S T x Z tau := by
  simpa only [lExp, Real.sqrt_mul hR.le tau] using
    lRegCurve_para (I := I) S hS t0 R hR ht0 T x Z (Real.sqrt tau)

end DifferentialGeometry.PDE.RicciFlow.Perelman
