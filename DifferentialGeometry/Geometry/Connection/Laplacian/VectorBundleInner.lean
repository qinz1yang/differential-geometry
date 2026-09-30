import DifferentialGeometry.Geometry.Connection.Laplacian.VectorBundle
import DifferentialGeometry.Geometry.Operator.Gradient.Regularity
import DifferentialGeometry.Geometry.Metric.TensorInner.Fiber.MetricData

set_option autoImplicit false

noncomputable section

open Bundle CovariantDerivative
open DifferentialGeometry
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator
open scoped Manifold ContDiff BigOperators Topology InnerProductSpace

namespace DifferentialGeometry.Geometry.Connection

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace Real F]
  [FiniteDimensional Real F]
variable {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, NormedAddCommGroup (V x)] [∀ x, InnerProductSpace Real (V x)]
  [FiberBundle F V] [VectorBundle Real F V]
  [ContMDiffVectorBundle ∞ F V I]
  [IsContMDiffRiemannianBundle I ∞ F V]

omit [T2Space M] in
private theorem abstractHessian_inner_bundle_apply
    (g : SmoothRiemannianMetric I M) (cov : CovariantDerivative I F V)
    [ContMDiffCovariantDerivative cov ∞] (hcov : cov.IsMetricCompatible)
    (u v : Cₛ^∞⟮I; F, V⟯)
    (X : (y : M) → TangentSpace I y)
    (hXsmooth : ContMDiff I (I.prod 𝓘(Real, E)) ∞ (T% X)) (x : M) :
    abstractHessian (I := I) g (fun y ↦ inner Real (u y) (v y)) x (X x) (X x) =
      inner Real
          (cov (covApply cov (fun y ↦ X y) (fun y ↦ u y)) x (X x) -
            cov (fun y ↦ u y) x
              ((LeviCivita (I := I) g) (fun y ↦ X y) x (X x)))
          (v x) +
        inner Real (cov (fun y ↦ u y) x (X x))
          (cov (fun y ↦ v y) x (X x)) +
        inner Real (cov (fun y ↦ u y) x (X x))
          (cov (fun y ↦ v y) x (X x)) +
        inner Real (u x)
          (cov (covApply cov (fun y ↦ X y) (fun y ↦ v y)) x (X x) -
            cov (fun y ↦ v y) x
              ((LeviCivita (I := I) g) (fun y ↦ X y) x (X x))) := by
  let f : M → Real := fun y ↦ inner Real (u y) (v y)
  have hf : ContMDiff I 𝓘(Real, Real) ∞ f := u.contMDiff.inner_bundle v.contMDiff
  have htheta : MDiffAtCotangent (mvfderiv (I := I) f) x :=
    ((cotangentCov_mvfderiv_smooth (I := I) hf) x).mdifferentiableAt (by simp)
  have hX : MDiffAt (T% X) x :=
    (hXsmooth x).mdifferentiableAt (by simp)
  have hdu : MDiffAt
      (T% (covApply cov X (fun y ↦ u y))) x := by
    exact ((contMDiffOn_univ.mp (covApply_contMDiffOn (cov := cov)
      hXsmooth (by simpa using u.contMDiff))) x).mdifferentiableAt (by simp)
  have hdv : MDiffAt
      (T% (covApply cov X (fun y ↦ v y))) x := by
    exact ((contMDiffOn_univ.mp (covApply_contMDiffOn (cov := cov)
      hXsmooth (by simpa using v.contMDiff))) x).mdifferentiableAt (by simp)
  have hhess := cotangentCovAt_apply_of_diff
    (LeviCivita (I := I) g) htheta hX hX
  have hfirst :
      (fun y : M ↦ mvfderiv (I := I) f y (X y)) =
        fun y ↦
          inner Real (covApply cov X (fun z ↦ u z) y) (v y) +
            inner Real (u y) (covApply cov X (fun z ↦ v z) y) := by
    funext y
    exact hcov.mvfderiv_inner_eq (fun z ↦ X z)
      u.mdifferentiableAt v.mdifferentiableAt
  have hleft := hcov.mvfderiv_inner_eq
    (σ := covApply cov X (fun y ↦ u y))
    (τ := fun y ↦ v y) (x := x) (fun y ↦ X y)
    hdu v.mdifferentiableAt
  have hright := hcov.mvfderiv_inner_eq
    (σ := fun y ↦ u y)
    (τ := covApply cov X (fun y ↦ v y))
    (x := x) (fun y ↦ X y) u.mdifferentiableAt hdv
  have hbase := hcov.mvfderiv_inner_eq (x := x)
    (fun y ↦ (LeviCivita (I := I) g) (fun z ↦ X z) y (X y))
    u.mdifferentiableAt v.mdifferentiableAt
  change
    ((cotangentCov (LeviCivita (I := I) g)).toFun
      (mvfderiv (I := I) f) x (X x)) (X x) = _
  rw [cotangentCov_toFun, cotangentCovFun_apply, hhess]
  unfold cotangentScalar
  rw [hfirst]
  rw [mvfderiv_fun_add
    (hdu.inner_bundle v.mdifferentiableAt)
    (u.mdifferentiableAt.inner_bundle hdv)]
  simp only [add_apply]
  rw [hleft, hright, hbase]
  dsimp only [f]
  simp only [covApply_apply, inner_sub_left, inner_sub_right]
  abel_nf

private theorem abstractHessian_eq_inner_cov_gradient
    (g : SmoothRiemannianMetric I M)
    {f : M → Real} (hf : ContMDiff I 𝓘(Real, Real) ∞ f)
    (x : M) (hx : I.IsInteriorPoint x) (v w : TangentSpace I x) :
    g.inner x
        ((LeviCivita (I := I) g)
          (fun y ↦ gradientFun (I := I) g f y) x v)
        w =
      abstractHessian (I := I) g f x v w := by
  classical
  let W : (y : M) → TangentSpace I y := FiberBundle.extend E w
  have hWx : W x = w := by simp [W]
  have hWat : MDiffAt (T% W) x := FiberBundle.mdifferentiableAt_extend ..
  let cov := LeviCivita (I := I) g
  let theta : (y : M) → TangentSpace I y →L[Real] Real :=
    mvfderiv (I := I) f
  have hgrad : MDiffAt
      (T% fun y : M ↦ gradientFun (I := I) g f y) x :=
    (gradientFun_smooth (I := I) g hf).mdifferentiableAt (by simp)
  have htheta : MDiffAtCotangent theta x :=
    ((cotangentCov_mvfderiv_smooth (I := I) hf) x).mdifferentiableAt (by simp)
  have hpair := cotangentCov_dualPairing cov htheta hWat v
  have hfun : (fun y : M ↦ theta y (W y)) =
      fun y ↦ g.inner y (gradientFun (I := I) g f y) (W y) := by
    funext y
    exact (inner_gradientFun (I := I) g f y (W y)).symm
  have hxgood : x ∈ chartLeviCivitaGoodSet (I := I) x := by
    refine mem_chartLeviCivitaGoodSet_iff.mpr ⟨mem_extChartAt_source x,
      mem_baseSet_trivializationAt E (TangentSpace I) x, ?_⟩
    exact I.isInteriorPoint_iff.mp hx
  have hmetric := chartLeviCivita_isMetricCompatibleOn
    (I := I) g x hgrad hWat hxgood v
  rw [← LeviCivita_chart_apply (I := I) g x hxgood hgrad v,
    ← LeviCivita_chart_apply (I := I) g x hxgood hWat v] at hmetric
  have hmetric' :
      mvfderiv (I := I)
          (fun y ↦ g.inner y (gradientFun (I := I) g f y) (W y)) x v =
        g.inner x
            (cov (fun y ↦ gradientFun (I := I) g f y) x v)
            (W x) +
          g.inner x (gradientFun (I := I) g f x) (cov W x v) := by
    rw [show mvfderiv (I := I)
        (fun y ↦ g.inner y (gradientFun (I := I) g f y) (W y)) x v =
      mfderiv I 𝓘(Real, Real)
        (fun y ↦ g.inner y (gradientFun (I := I) g f y) (W y)) x v from rfl]
    exact hmetric
  rw [hfun] at hpair
  have hgradInner :
      g.inner x (gradientFun (I := I) g f x) (cov W x v) =
        theta x (cov W x v) :=
    inner_gradientFun (I := I) g f x (cov W x v)
  rw [hgradInner] at hmetric'
  have hkey :
      g.inner x
          (cov (fun y ↦ gradientFun (I := I) g f y) x v)
          (W x) =
        ((cotangentCov cov) theta x v) (W x) := by
    linarith [hmetric'.symm.trans hpair]
  rw [hWx] at hkey
  rw [hkey]
  rfl

private theorem sum_abstractHessian_smoothOrthoFrame_eq_laplacian
    (g : SmoothRiemannianMetric I M)
    {f : M → Real} (hf : ContMDiff I 𝓘(Real, Real) ∞ f)
    (x : M) (hx : I.IsInteriorPoint x) :
    ∑ i : Fin (Module.finrank Real E),
        abstractHessian (I := I) g f x
          (smoothOrthoFrame (I := I) g x i x)
          (smoothOrthoFrame (I := I) g x i x) =
      laplacian (I := I) (LeviCivita (I := I) g) g f x := by
  classical
  let D := (DifferentialGeometry.Tensor0SBundle.tangentMetricData
    (I := I) g x).metric
  let : InnerProductSpace.Core Real (TangentSpace I x) := D.toCore
  let : NormedAddCommGroup (TangentSpace I x) :=
    @InnerProductSpace.Core.toNormedAddCommGroup Real (TangentSpace I x)
      _ _ _ D.toCore
  let : InnerProductSpace Real (TangentSpace I x) :=
    @InnerProductSpace.ofCore Real (TangentSpace I x) _ _ _ D.toCore.toCore
  let frame : Fin (Module.finrank Real E) → TangentSpace I x :=
    fun i ↦ smoothOrthoFrame (I := I) g x i x
  have hframe : Orthonormal Real frame := by
    rw [orthonormal_iff_ite]
    intro i j
    let _ : NeZero (Module.finrank Real E) :=
      ⟨Nat.ne_of_gt (lt_of_le_of_lt (Nat.zero_le i.val) i.isLt)⟩
    change g.inner x (frame i) (frame j) = if i = j then 1 else 0
    exact smoothOrthoFrame_orthonormal_at_center (I := I) g x i j
  have hcard : Fintype.card (Fin (Module.finrank Real E)) =
      Module.finrank Real (TangentSpace I x) := by
    simpa using (show Module.finrank Real E =
      Module.finrank Real (TangentSpace I x) from rfl)
  have hspan : ⊤ ≤ Submodule.span Real (Set.range frame) := by
    have hbasis := (basisOfLinearIndependentOfCardEqFinrank' frame hframe.linearIndependent hcard).span_eq
    rw [coe_basisOfLinearIndependentOfCardEqFinrank'] at hbasis
    exact hbasis.ge
  let basis : OrthonormalBasis (Fin (Module.finrank Real E)) Real
      (TangentSpace I x) := OrthonormalBasis.mk hframe hspan
  have hbasis (i : Fin (Module.finrank Real E)) : basis i = frame i := by
    simp [basis]
  unfold laplacian divergence
  rw [LinearMap.trace_eq_sum_inner _ basis]
  apply Finset.sum_congr rfl
  intro i hi
  rw [hbasis]
  change abstractHessian (I := I) g f x (frame i) (frame i) =
    g.inner x (frame i)
      ((LeviCivita (I := I) g)
        (fun y ↦ gradientFun (I := I) g f y) x (frame i))
  rw [g.symm]
  exact (abstractHessian_eq_inner_cov_gradient
    (I := I) g hf x hx (frame i) (frame i)).symm

theorem mvfderiv_inner_endomorphism_apply_of_cov_eq_zero
    (cov : CovariantDerivative I F V)
    (hcov : cov.IsMetricCompatible)
    (A : Cₛ^∞⟮I; F →L[Real] F, (fun x : M ↦ V x →L[Real] V x)⟯)
    (v : Cₛ^∞⟮I; F, V⟯) (x : M) (X : TangentSpace I x)
    (hv : cov v x = 0) :
    mvfderiv I (fun y ↦ inner Real (A y (v y)) (v y)) x X =
      inner Real
        ((HomConnectionGen.homBundleCovariantDerivativeGen
          I M F V F V cov cov (fun y ↦ A y) x X) (v x))
        (v x) := by
  let Av : Cₛ^∞⟮I; F, V⟯ :=
    ⟨fun y ↦ A y (v y),
      ContMDiff.clm_bundle_apply (b := id) A.contMDiff v.contMDiff⟩
  have hinner := hcov.mvfderiv_inner_eq (x := x)
    (fun _ : M ↦ X) Av.mdifferentiableAt v.mdifferentiableAt
  have happly := HomConnectionGen.homBundleCovariantDerivativeGen_apply
    I M F V F V cov cov A v x X
  have happly' :
      (HomConnectionGen.homBundleCovariantDerivativeGen
        I M F V F V cov cov A x X) (v x) =
        cov Av x X - A x (cov v x X) := happly
  change
    mvfderiv I (fun y ↦ inner Real (Av y) (v y)) x X = _
  rw [hinner]
  have hcovv : cov v x X = 0 := by rw [hv]; rfl
  rw [happly']
  simp only [hcovv, map_zero, sub_zero, inner_zero_right, add_zero]

theorem laplacian_inner_bundle
    (g : SmoothRiemannianMetric I M) (cov : CovariantDerivative I F V)
    [ContMDiffCovariantDerivative cov ∞] (hcov : cov.IsMetricCompatible)
    (u v : Cₛ^∞⟮I; F, V⟯) (x : M) (hx : I.IsInteriorPoint x) :
    laplacian (I := I) (LeviCivita (I := I) g) g
        (fun y ↦ inner Real (u y) (v y)) x =
      inner Real (rawBundleConnLap (I := I) g cov (fun y ↦ u y) x) (v x) +
        2 * ∑ i : Fin (Module.finrank Real E),
          inner Real
            (cov (fun y ↦ u y) x (smoothOrthoFrame (I := I) g x i x))
            (cov (fun y ↦ v y) x (smoothOrthoFrame (I := I) g x i x)) +
        inner Real (u x)
          (rawBundleConnLap (I := I) g cov (fun y ↦ v y) x) := by
  classical
  have hf : ContMDiff I 𝓘(Real, Real) ∞
      (fun y ↦ inner Real (u y) (v y)) :=
    u.contMDiff.inner_bundle v.contMDiff
  rw [← sum_abstractHessian_smoothOrthoFrame_eq_laplacian
    (I := I) g hf x hx]
  rw [rawBundleConnLap_def, rawBundleConnLap_def]
  have hdir (i : Fin (Module.finrank Real E)) :=
    let _ : NeZero (Module.finrank Real E) :=
      ⟨Nat.ne_of_gt (lt_of_le_of_lt (Nat.zero_le i.val) i.isLt)⟩
    abstractHessian_inner_bundle_apply
      (I := I) g cov hcov u v
      (smoothOrthoFrame (I := I) g x i)
      (smoothOrthoFrame_smooth (I := I) g x i) x
  rw [Finset.sum_congr rfl (fun i _ ↦ hdir i)]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
    Finset.sum_add_distrib]
  simp only [sum_inner, inner_sum]
  ring

theorem laplacian_inner_bundle_of_cov_right_eq_zero
    (g : SmoothRiemannianMetric I M) (cov : CovariantDerivative I F V)
    [ContMDiffCovariantDerivative cov ∞] (hcov : cov.IsMetricCompatible)
    (u v : Cₛ^∞⟮I; F, V⟯) (x : M)
    (hx : I.IsInteriorPoint x)
    (hv : cov (fun y ↦ v y) x = 0) :
    laplacian (I := I) (LeviCivita (I := I) g) g
        (fun y ↦ inner Real (u y) (v y)) x =
      inner Real (rawBundleConnLap (I := I) g cov (fun y ↦ u y) x) (v x) +
        inner Real (u x)
          (rawBundleConnLap (I := I) g cov (fun y ↦ v y) x) := by
  rw [laplacian_inner_bundle (I := I) g cov hcov u v x hx]
  simp [hv]

theorem inner_rawBundleConnLap_self_eq_zero_of_eventually_unit
    (g : SmoothRiemannianMetric I M) (cov : CovariantDerivative I F V)
    [ContMDiffCovariantDerivative cov ∞] (hcov : cov.IsMetricCompatible)
    (v : Cₛ^∞⟮I; F, V⟯) (x : M)
    (hx : I.IsInteriorPoint x)
    (hv : cov (fun y ↦ v y) x = 0)
    (hunit : ∀ᶠ y in 𝓝 x, inner Real (v y) (v y) = 1) :
    inner Real (v x)
        (rawBundleConnLap (I := I) g cov (fun y ↦ v y) x) = 0 := by
  have hvv : ContMDiff I 𝓘(Real, Real) ∞
      (fun y ↦ inner Real (v y) (v y)) :=
    v.contMDiff.inner_bundle v.contMDiff
  have hlapZero :
      laplacian (I := I) (LeviCivita (I := I) g) g
        (fun y ↦ inner Real (v y) (v y)) x = 0 := by
    calc
      _ = laplacian (I := I) (LeviCivita (I := I) g) g
          (fun _ : M ↦ (1 : Real)) x :=
        laplacian_congr_of_eventuallyEq (I := I)
          (LeviCivita (I := I) g) g hvv.contMDiffAt
            contMDiffAt_const hunit
      _ = 0 := laplacian_const (I := I)
        (LeviCivita (I := I) g) g (1 : Real) x
  have hlap := laplacian_inner_bundle_of_cov_right_eq_zero
    (I := I) g cov hcov v v x hx hv
  rw [hlapZero] at hlap
  rw [real_inner_comm] at hlap
  linarith

theorem laplacian_inner_endomorphism_apply_of_normal_eigenvector
    (g : SmoothRiemannianMetric I M) (cov : CovariantDerivative I F V)
    [ContMDiffCovariantDerivative cov ∞] (hcov : cov.IsMetricCompatible)
    (A : Cₛ^∞⟮I; F →L[Real] F, (fun x : M ↦ V x →L[Real] V x)⟯)
    (v : Cₛ^∞⟮I; F, V⟯) (x : M) {eigenvalue : Real}
    (hx : I.IsInteriorPoint x)
    (hA : ((A x : V x →L[Real] V x) : V x →ₗ[Real] V x).IsSymmetric)
    (heigen : A x (v x) = eigenvalue • v x)
    (hv : cov (fun y ↦ v y) x = 0)
    (hunit : ∀ᶠ y in 𝓝 x, inner Real (v y) (v y) = 1) :
    laplacian (I := I) (LeviCivita (I := I) g) g
        (fun y ↦ inner Real (A y (v y)) (v y)) x =
      inner Real
        (rawBundleEndomorphismConnLap (I := I) g cov (fun y ↦ A y) x (v x))
        (v x) := by
  let q : M → Real := fun y ↦ inner Real (A y (v y)) (v y)
  change laplacian (I := I) (LeviCivita (I := I) g) g q x = _
  let Av : Cₛ^∞⟮I; F, V⟯ :=
    ⟨fun y ↦ A y (v y),
      ContMDiff.clm_bundle_apply (b := id) A.contMDiff v.contMDiff⟩
  let lapv := rawBundleConnLap (I := I) g cov (fun y ↦ v y) x
  have hlapv : inner Real (v x) lapv = 0 :=
    inner_rawBundleConnLap_self_eq_zero_of_eventually_unit
      (I := I) g cov hcov v x hx hv hunit
  have happly := rawBundleEndomorphismConnLap_apply
    (I := I) g cov A v x
  have hnormal (i : Fin (Module.finrank Real E)) :
      cov (fun y ↦ v y) x (smoothOrthoFrame (I := I) g x i x) = 0 := by
    rw [hv]
    rfl
  simp_rw [hnormal] at happly
  simp only [map_zero, Finset.sum_const_zero, smul_zero, sub_zero] at happly
  have hlapAv :
      rawBundleConnLap (I := I) g cov (fun y ↦ Av y) x =
        rawBundleEndomorphismConnLap (I := I) g cov (fun y ↦ A y) x (v x) +
          A x lapv := by
    change rawBundleConnLap (I := I) g cov (fun y ↦ A y (v y)) x = _
    rw [happly]
    abel
  have hlap := laplacian_inner_bundle_of_cov_right_eq_zero
    (I := I) g cov hcov Av v x hx hv
  have hAlapv : inner Real (A x lapv) (v x) = 0 := by
    calc
      inner Real (A x lapv) (v x) = inner Real lapv (A x (v x)) := hA _ _
      _ = eigenvalue * inner Real lapv (v x) := by
        rw [heigen, inner_smul_right]
      _ = 0 := by rw [real_inner_comm, hlapv, mul_zero]
  have hAvlapv : inner Real (Av x) lapv = 0 := by
    change inner Real (A x (v x)) lapv = 0
    rw [heigen, inner_smul_left, conj_trivial, hlapv, mul_zero]
  have hlapq :
      laplacian (I := I) (LeviCivita (I := I) g) g q x =
        inner Real (rawBundleConnLap (I := I) g cov (fun y ↦ Av y) x) (v x) +
          inner Real (Av x) lapv := by
    have hq : q = fun y ↦ inner Real (Av y) (v y) := by
      funext y
      rfl
    rw [hq]
    simpa only [lapv] using hlap
  rw [hlapq, hlapAv]
  simp only [inner_add_left, hAlapv, add_zero, hAvlapv]

end DifferentialGeometry.Geometry.Connection
