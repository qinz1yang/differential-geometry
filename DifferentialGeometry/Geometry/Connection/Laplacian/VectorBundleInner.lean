import DifferentialGeometry.Geometry.Connection.Laplacian.VectorBundle
import DifferentialGeometry.Geometry.Curvature.Bochner.WeitzenbockIdentity
import DifferentialGeometry.Geometry.Operator.LaplacianBridge

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

theorem mvfderiv_inner_endomorphism_apply_of_cov_eq_zero
    (cov : CovariantDerivative I F V)
    [ContMDiffCovariantDerivative cov ∞] (hcov : cov.IsMetricCompatible)
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
    [NeZero (Module.finrank Real E)]
    [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (cov : CovariantDerivative I F V)
    [ContMDiffCovariantDerivative cov ∞] (hcov : cov.IsMetricCompatible)
    (u v : Cₛ^∞⟮I; F, V⟯) (x : M) :
    ΔG (I := I) g
        ⟨fun y ↦ inner Real (u y) (v y),
          u.contMDiff.inner_bundle v.contMDiff⟩ x =
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
    (I := I) g hf x]
  rw [rawBundleConnLap_def, rawBundleConnLap_def]
  have hdir (i : Fin (Module.finrank Real E)) :=
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
    [NeZero (Module.finrank Real E)]
    [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (cov : CovariantDerivative I F V)
    [ContMDiffCovariantDerivative cov ∞] (hcov : cov.IsMetricCompatible)
    (u v : Cₛ^∞⟮I; F, V⟯) (x : M)
    (hv : cov (fun y ↦ v y) x = 0) :
    ΔG (I := I) g
        ⟨fun y ↦ inner Real (u y) (v y),
          u.contMDiff.inner_bundle v.contMDiff⟩ x =
      inner Real (rawBundleConnLap (I := I) g cov (fun y ↦ u y) x) (v x) +
        inner Real (u x)
          (rawBundleConnLap (I := I) g cov (fun y ↦ v y) x) := by
  rw [laplacian_inner_bundle (I := I) g cov hcov u v x]
  simp [hv]

theorem inner_rawBundleConnLap_self_eq_zero_of_eventually_unit
    [NeZero (Module.finrank Real E)]
    [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (cov : CovariantDerivative I F V)
    [ContMDiffCovariantDerivative cov ∞] (hcov : cov.IsMetricCompatible)
    (v : Cₛ^∞⟮I; F, V⟯) (x : M)
    (hv : cov (fun y ↦ v y) x = 0)
    (hunit : ∀ᶠ y in 𝓝 x, inner Real (v y) (v y) = 1) :
    inner Real (v x)
        (rawBundleConnLap (I := I) g cov (fun y ↦ v y) x) = 0 := by
  have hvv : ContMDiff I 𝓘(Real, Real) ∞
      (fun y ↦ inner Real (v y) (v y)) :=
    v.contMDiff.inner_bundle v.contMDiff
  have hone : ContMDiff I 𝓘(Real, Real) ∞ (fun _ : M ↦ (1 : Real)) :=
    contMDiff_const
  have hlapZero :
      ΔG (I := I) g ⟨fun y ↦ inner Real (v y) (v y), hvv⟩ x = 0 := by
    calc
      _ = ΔG (I := I) g ⟨fun _ : M ↦ (1 : Real), hone⟩ x :=
        Δ_g_congr_of_eventuallyEq (I := I) g hvv hone hunit
      _ = 0 := Δ_g_const (I := I) g (1 : Real) x
  have hlap := laplacian_inner_bundle_of_cov_right_eq_zero
    (I := I) g cov hcov v v x hv
  rw [hlapZero] at hlap
  rw [real_inner_comm] at hlap
  linarith

theorem laplacian_inner_endomorphism_apply_of_normal_eigenvector
    [NeZero (Module.finrank Real E)]
    [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (cov : CovariantDerivative I F V)
    [ContMDiffCovariantDerivative cov ∞] (hcov : cov.IsMetricCompatible)
    (A : Cₛ^∞⟮I; F →L[Real] F, (fun x : M ↦ V x →L[Real] V x)⟯)
    (v : Cₛ^∞⟮I; F, V⟯) (x : M) {eigenvalue : Real}
    (hA : ((A x : V x →L[Real] V x) : V x →ₗ[Real] V x).IsSymmetric)
    (heigen : A x (v x) = eigenvalue • v x)
    (hv : cov (fun y ↦ v y) x = 0)
    (hunit : ∀ᶠ y in 𝓝 x, inner Real (v y) (v y) = 1) :
    ΔG (I := I) g
        ⟨fun y ↦ inner Real (A y (v y)) (v y),
          (ContMDiff.clm_bundle_apply (b := id) A.contMDiff v.contMDiff).inner_bundle
            v.contMDiff⟩ x =
      inner Real
        (rawBundleEndomorphismConnLap (I := I) g cov (fun y ↦ A y) x (v x))
        (v x) := by
  let q : C^∞⟮I, M; Real⟯ :=
    ⟨fun y ↦ inner Real (A y (v y)) (v y),
      (ContMDiff.clm_bundle_apply (b := id) A.contMDiff v.contMDiff).inner_bundle
        v.contMDiff⟩
  change ΔG (I := I) g q x = _
  let Av : Cₛ^∞⟮I; F, V⟯ :=
    ⟨fun y ↦ A y (v y),
      ContMDiff.clm_bundle_apply (b := id) A.contMDiff v.contMDiff⟩
  let lapv := rawBundleConnLap (I := I) g cov (fun y ↦ v y) x
  have hlapv : inner Real (v x) lapv = 0 :=
    inner_rawBundleConnLap_self_eq_zero_of_eventually_unit
      (I := I) g cov hcov v x hv hunit
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
    (I := I) g cov hcov Av v x hv
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
      ΔG (I := I) g q x =
        inner Real (rawBundleConnLap (I := I) g cov (fun y ↦ Av y) x) (v x) +
          inner Real (Av x) lapv := by
    have hq : q =
        (⟨fun y ↦ inner Real (Av y) (v y),
          Av.contMDiff.inner_bundle v.contMDiff⟩ : C^∞⟮I, M; Real⟯) := by
      ext y
      rfl
    rw [hq]
    simpa only [lapv] using hlap
  rw [hlapq, hlapAv]
  simp only [inner_add_left, hAlapv, add_zero, hAvlapv]

end DifferentialGeometry.Geometry.Connection
