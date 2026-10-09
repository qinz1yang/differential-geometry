import DifferentialGeometry.Geometry.Metric.Coordinates.InnerExpansion
import DifferentialGeometry.Geometry.Curvature.DimensionTwo.RicciScalar
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.Identities.ContractedBianchi
import DifferentialGeometry.Geometry.Curvature.Bochner.WeitzenbockIdentity
import DifferentialGeometry.Geometry.Connection.NormalSection
import DifferentialGeometry.Geometry.Metric.Conformal.VectorField
import DifferentialGeometry.Geometry.Connection.Hessian
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.TensorAction.HomBundleLeibniz
import DifferentialGeometry.Geometry.Operator.Gradient.NormSquared

set_option autoImplicit false
noncomputable section

namespace DifferentialGeometry.Geometry

open Bundle CovariantDerivative
open Connection Curvature Operator
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [T2Space M]

section Hessian
variable [BoundarylessManifold I M]

private theorem hessian_derivative_skew_of_covariantDerivative_eq_zero
    (g : SmoothRiemannianMetric I M)
    (X V W Z : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M)
    (hV : LeviCivita g V x = 0) (hW : LeviCivita g W x = 0)
    (hZ : LeviCivita g Z x = 0) :
    LeviCivita g (fun y => (LeviCivita g).hessian (LeviCivita g) X y (W y) (Z y))
        x (V x) -
      LeviCivita g (fun y => (LeviCivita g).hessian (LeviCivita g) X y (V y) (Z y))
        x (W x) =
      riemannOp (LeviCivita g) x (V x) (W x) (LeviCivita g X x (Z x)) -
        LeviCivita g X x (riemannOp (LeviCivita g) x (V x) (W x) (Z x)) := by
  let cov := LeviCivita g
  let D := HomConnectionGen.homBundleCovariantDerivativeGen
    I M E (TangentSpace I) E (TangentSpace I) cov cov
  have hcov : ContMDiffCovariantDerivative cov ∞ := inferInstance
  let A : Cₛ^∞⟮I; E →L[Real] E,
      (fun y : M => TangentSpace I y →L[Real] TangentSpace I y)⟯ :=
    ⟨cov X, contMDiffOn_univ.mp
      (hcov.contMDiff.contMDiff (by simpa using X.contMDiff.contMDiffOn))⟩
  let BW : Cₛ^∞⟮I; E →L[Real] E,
      (fun y : M => TangentSpace I y →L[Real] TangentSpace I y)⟯ :=
    ⟨covApply D W A, contMDiffOn_univ.mp
      (covApply_contMDiffOn (cov := D) W.contMDiff (by simpa using A.contMDiff))⟩
  let BV : Cₛ^∞⟮I; E →L[Real] E,
      (fun y : M => TangentSpace I y →L[Real] TangentSpace I y)⟯ :=
    ⟨covApply D V A, contMDiffOn_univ.mp
      (covApply_contMDiffOn (cov := D) V.contMDiff (by simpa using A.contMDiff))⟩
  have hleft := HomConnectionGen.homBundleCovariantDerivativeGen_apply
    I M E (TangentSpace I) E (TangentSpace I) cov cov BW Z x (V x)
  have hright := HomConnectionGen.homBundleCovariantDerivativeGen_apply
    I M E (TangentSpace I) E (TangentSpace I) cov cov BV Z x (W x)
  change D BW x (V x) (Z x) = cov (fun y => BW y (Z y)) x (V x) -
    BW x (cov Z x (V x)) at hleft
  change D BV x (W x) (Z x) = cov (fun y => BV y (Z y)) x (W x) -
    BV x (cov Z x (W x)) at hright
  have hZ' : cov Z x = 0 := hZ
  simp only [hZ', zero_apply, map_zero, sub_zero] at hleft hright
  have ht := (CovariantDerivative.torsion_eq_zero_iff cov).mp
    (LeviCivita_torsion_eq_zero g) (x := x) V.mdifferentiableAt W.mdifferentiableAt
  have hbracket : VectorField.mlieBracket I V W x = 0 := by
    change cov W x (V x) - cov V x (W x) = VectorField.mlieBracket I V W x at ht
    have hV' : cov V x = 0 := hV
    have hW' : cov W x = 0 := hW
    simpa only [hV', hW', zero_apply, sub_self] using ht.symm
  have hcurv := HomConnection.riemannSec_homBundle_apply_eq
    I M E (TangentSpace I) E (TangentSpace I) cov cov V W A Z x
  rw [riemannSec_def, hbracket, map_zero] at hcurv
  change (D BW x (V x) - D BV x (W x) - 0) (Z x) = _ at hcurv
  simp only [sub_zero, sub_apply] at hcurv
  rw [hleft, hright] at hcurv
  change _ = riemannSec cov V W (fun y => A y (Z y)) x -
    A x (riemannSec cov V W Z x) at hcurv
  have hAZ := A.contMDiff.clm_bundle_apply Z.contMDiff
  rw [← riemannOp_apply_smooth (cov := cov) V.contMDiff W.contMDiff hAZ,
    ← riemannOp_apply_smooth (cov := cov) V.contMDiff W.contMDiff Z.contMDiff] at hcurv
  exact hcurv


private theorem hessian_skew
    (g : SmoothRiemannianMetric I M)
    (X V W : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) :
    (LeviCivita g).hessian (LeviCivita g) X x (V x) (W x) -
      (LeviCivita g).hessian (LeviCivita g) X x (W x) (V x) =
      riemannOp (LeviCivita g) x (V x) (W x) (X x) := by
  have hX2 : ContMDiffAt I (I.prod 𝓘(Real, E)) 2 (T% (X : (x : M) → TangentSpace I x)) x :=
    X.contMDiff.contMDiffAt.of_le (by norm_cast)
  rw [(LeviCivita g).hessian_apply_of_contMDiffAt inferInstance (LeviCivita g)
    hX2 W.mdifferentiableAt,
    (LeviCivita g).hessian_apply_of_contMDiffAt inferInstance (LeviCivita g)
    hX2 V.mdifferentiableAt,
    riemannOp_apply_smooth (cov := LeviCivita g) V.contMDiff W.contMDiff X.contMDiff,
    riemannSec_def]
  have ht := (CovariantDerivative.torsion_eq_zero_iff (LeviCivita g)).mp
    (LeviCivita_torsion_eq_zero g) (x := x) V.mdifferentiableAt W.mdifferentiableAt
  change LeviCivita g W x (V x) - LeviCivita g V x (W x) =
    VectorField.mlieBracket I V W x at ht
  rw [← ht, map_sub]
  change (_ - _) - (_ - _) =
    LeviCivita g (fun y => LeviCivita g X y (W y)) x (V x) -
      LeviCivita g (fun y => LeviCivita g X y (V y)) x (W x) - (_ - _)
  abel

private theorem hessian_conformal_pair
    (g : SmoothRiemannianMetric I M)
    (X V W Z : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (φ : C^∞⟮I, M; Real⟯)
    (hX : ∀ (y : M) (v w : TangentSpace I y),
      g.inner y (LeviCivita g X y v) w + g.inner y v (LeviCivita g X y w) =
        φ y * g.inner y v w) (x : M) :
    g.inner x ((LeviCivita g).hessian (LeviCivita g) X x (V x) (W x)) (Z x) +
      g.inner x (W x) ((LeviCivita g).hessian (LeviCivita g) X x (V x) (Z x)) =
      mvfderiv I (φ : M → Real) x (V x) * g.inner x (W x) (Z x) := by
  let AW : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
    ⟨covApply (LeviCivita g) W X,
      contMDiffOn_univ.mp (covApply_contMDiffOn (cov := LeviCivita g)
        W.contMDiff (by simpa using X.contMDiff))⟩
  let AZ : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
    ⟨covApply (LeviCivita g) Z X,
      contMDiffOn_univ.mp (covApply_contMDiffOn (cov := LeviCivita g)
        Z.contMDiff (by simpa using X.contMDiff))⟩
  have hpair : (fun y => g.inner y (AW y) (Z y) + g.inner y (W y) (AZ y)) =
      fun y => φ y * g.inner y (W y) (Z y) := funext fun y => hX y (W y) (Z y)
  have hd := congrArg (fun f : M → Real => mvfderiv I f x (V x)) hpair
  change mvfderiv I ((fun y => g.inner y (AW y) (Z y)) +
    (fun y => g.inner y (W y) (AZ y))) x (V x) = _ at hd
  rw [mvfderiv_add ((contMDiff_g_inner_of_smooth_sections g AW Z).mdifferentiableAt (by simp))
    ((contMDiff_g_inner_of_smooth_sections g W AZ).mdifferentiableAt (by simp)),
    mvfderiv_mul_at (V x) (φ.contMDiff.mdifferentiableAt (by simp))
    ((contMDiff_g_inner_of_smooth_sections g W Z).mdifferentiableAt (by simp)), add_apply] at hd
  have h₁ := (LeviCivita_isMetricCompatible g).apply
    (x := x) AW.mdifferentiableAt Z.mdifferentiableAt (V x)
  have h₂ := (LeviCivita_isMetricCompatible g).apply
    (x := x) W.mdifferentiableAt AZ.mdifferentiableAt (V x)
  have h₃ := (LeviCivita_isMetricCompatible g).apply
    (x := x) W.mdifferentiableAt Z.mdifferentiableAt (V x)
  change mvfderiv I (fun y => g.inner y (AW y) (Z y)) x (V x) = _ at h₁
  change mvfderiv I (fun y => g.inner y (W y) (AZ y)) x (V x) = _ at h₂
  change mvfderiv I (fun y => g.inner y (W y) (Z y)) x (V x) = _ at h₃
  rw [h₁, h₂, h₃] at hd
  have hX2 : ContMDiffAt I (I.prod 𝓘(Real, E)) 2 (T% (X : (x : M) → TangentSpace I x)) x :=
    X.contMDiff.contMDiffAt.of_le (by norm_cast)
  rw [(LeviCivita g).hessian_apply_of_contMDiffAt inferInstance (LeviCivita g)
    hX2 W.mdifferentiableAt,
    (LeviCivita g).hessian_apply_of_contMDiffAt inferInstance (LeviCivita g)
    hX2 Z.mdifferentiableAt]
  simp only [map_sub, sub_apply]
  have ha := hX x (LeviCivita g W x (V x)) (Z x)
  have hb := hX x (W x) (LeviCivita g Z x (V x))
  change _ + g.inner x (LeviCivita g W x (V x)) (LeviCivita g X x (Z x)) = _ at ha
  change g.inner x (LeviCivita g X x (W x)) (LeviCivita g Z x (V x)) + _ = _ at hb
  change g.inner x (LeviCivita g (fun y => LeviCivita g X y (W y)) x (V x)) (Z x) +
    g.inner x (LeviCivita g X x (W x)) (LeviCivita g Z x (V x)) +
    (g.inner x (LeviCivita g W x (V x)) (LeviCivita g X x (Z x)) +
    g.inner x (W x) (LeviCivita g (fun y => LeviCivita g X y (Z y)) x (V x))) = _ at hd
  rw [mul_add] at hd
  linarith

private theorem hessian_conformal_inner
    (g : SmoothRiemannianMetric I M)
    (X V W Z : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (φ κ : C^∞⟮I, M; Real⟯)
    (hX : ∀ (y : M) (v w : TangentSpace I y),
      g.inner y (LeviCivita g X y v) w + g.inner y v (LeviCivita g X y w) =
        φ y * g.inner y v w)
    (hR : ∀ (y : M) (v w z : TangentSpace I y),
      riemannOp (LeviCivita g) y v w z =
        κ y • (g.inner y w z • v - g.inner y v z • w)) (x : M) :
    g.inner x ((LeviCivita g).hessian (LeviCivita g) X x (V x) (W x)) (Z x) =
      κ x * (g.inner x (X x) (W x) * g.inner x (V x) (Z x) -
        g.inner x (V x) (W x) * g.inner x (X x) (Z x)) +
      (mvfderiv I (φ : M → Real) x (V x) * g.inner x (W x) (Z x) +
        mvfderiv I (φ : M → Real) x (W x) * g.inner x (V x) (Z x) -
        mvfderiv I (φ : M → Real) x (Z x) * g.inner x (V x) (W x)) / 2 := by
  have h₁ := hessian_conformal_pair g X V W Z φ hX x
  have h₂ := hessian_conformal_pair g X W V Z φ hX x
  have h₃ := hessian_conformal_pair g X Z V W φ hX x
  have h₄ := congrArg (fun v => g.inner x v (Z x)) (hessian_skew g X V W x)
  have h₅ := congrArg (fun v => g.inner x v (W x)) (hessian_skew g X V Z x)
  have h₆ := congrArg (fun v => g.inner x v (V x)) (hessian_skew g X W Z x)
  simp only [hR, map_smul, map_sub, sub_apply, smul_apply, smul_eq_mul] at h₄ h₅ h₆
  rw [g.symm x (W x) _] at h₁
  rw [g.symm x (V x) _] at h₂
  rw [g.symm x (V x) _] at h₃
  simp only [g.symm x (W x) (X x), g.symm x (V x) (X x),
    g.symm x (Z x) (X x), g.symm x (W x) (V x),
    g.symm x (Z x) (V x), g.symm x (Z x) (W x)] at h₄ h₅ h₆
  linarith

omit [FiniteDimensional Real E] [IsManifold I ∞ M] [T2Space M] [BoundarylessManifold I M] in
private theorem derivative_expression
    (κ a b c d p e q r : C^∞⟮I, M; Real⟯) (x : M) (v : TangentSpace I x) :
    mvfderiv I (fun y => κ y * (a y * b y - c y * d y) +
      (p y * e y + q y * b y - r y * c y) / 2) x v =
    mvfderiv I (κ : M → Real) x v * (a x * b x - c x * d x) +
      κ x * (mvfderiv I (a : M → Real) x v * b x +
        a x * mvfderiv I (b : M → Real) x v -
        (mvfderiv I (c : M → Real) x v * d x +
          c x * mvfderiv I (d : M → Real) x v)) +
      (mvfderiv I (p : M → Real) x v * e x +
        p x * mvfderiv I (e : M → Real) x v +
        (mvfderiv I (q : M → Real) x v * b x +
          q x * mvfderiv I (b : M → Real) x v) -
        (mvfderiv I (r : M → Real) x v * c x +
          r x * mvfderiv I (c : M → Real) x v)) / 2 := by
  have hd (f : C^∞⟮I, M; Real⟯) : MDifferentiableAt I 𝓘(Real) f x :=
    f.contMDiff.mdifferentiableAt (by simp)
  change mvfderiv I ((κ : M → Real) * ((a : M → Real) * (b : M → Real) - (c : M → Real) * (d : M → Real)) +
    (((p : M → Real) * (e : M → Real) + (q : M → Real) * (b : M → Real) - (r : M → Real) * (c : M → Real)) *
      fun _ => (2 : Real)⁻¹)) x v = _
  rw [mvfderiv_add ((hd κ).mul (((hd a).mul (hd b)).sub ((hd c).mul (hd d))))
    (((((hd p).mul (hd e)).add ((hd q).mul (hd b))).sub ((hd r).mul (hd c))).mul
      mdifferentiableAt_const), add_apply]
  simp only [_root_.mvfderiv_mul (hd κ) (((hd a).mul (hd b)).sub ((hd c).mul (hd d))),
    _root_.mvfderiv_mul ((((hd p).mul (hd e)).add ((hd q).mul (hd b))).sub
      ((hd r).mul (hd c))) mdifferentiableAt_const,
    mvfderiv_sub ((hd a).mul (hd b)) ((hd c).mul (hd d)),
    mvfderiv_sub (((hd p).mul (hd e)).add ((hd q).mul (hd b))) ((hd r).mul (hd c)),
    mvfderiv_add ((hd p).mul (hd e)) ((hd q).mul (hd b)),
    _root_.mvfderiv_mul (hd a) (hd b), _root_.mvfderiv_mul (hd c) (hd d),
    _root_.mvfderiv_mul (hd p) (hd e), _root_.mvfderiv_mul (hd q) (hd b),
    _root_.mvfderiv_mul (hd r) (hd c), mvfderiv_const, zero_apply,
    Pi.mul_apply, Pi.sub_apply, Pi.add_apply, sub_apply, add_apply, smul_apply, smul_eq_mul,
    mul_zero, div_eq_mul_inv]
  ring

private theorem normal_inner_derivative
    (g : SmoothRiemannianMetric I M)
    (Y Z : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (x : M) (v : TangentSpace I x) (hZ : LeviCivita g Z x = 0) :
    mvfderiv I (fun y => g.inner y (Y y) (Z y)) x v =
      g.inner x (LeviCivita g Y x v) (Z x) := by
  have h := (LeviCivita_isMetricCompatible g).apply
    (x := x) Y.mdifferentiableAt Z.mdifferentiableAt v
  change mvfderiv I (fun y => g.inner y (Y y) (Z y)) x v = _ at h
  simpa only [hZ, zero_apply, map_zero, add_zero] using h

omit [T2Space M] [BoundarylessManifold I M] in
private theorem normal_mvfderiv_derivative
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; Real⟯)
    (Z : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (x : M) (v : TangentSpace I x) (hZ : LeviCivita g Z x = 0) :
    mvfderiv I (fun y => mvfderiv I (φ : M → Real) y (Z y)) x v =
      abstractHessian g φ x v (Z x) := by
  have h := cotangentCov_dualPairing (LeviCivita g)
    ((cotangentCov_mvfderiv_smooth φ.contMDiff).mdifferentiableAt (by simp))
    Z.mdifferentiableAt v
  simpa only [hZ, zero_apply, map_zero, add_zero, abstractHessian] using h

private theorem hessian_conformal_derivative_inner
    (g : SmoothRiemannianMetric I M)
    (X U V W Z : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (φ κ : C^∞⟮I, M; Real⟯)
    (hX : ∀ (y : M) (v w : TangentSpace I y),
      g.inner y (LeviCivita g X y v) w + g.inner y v (LeviCivita g X y w) =
        φ y * g.inner y v w)
    (hR : ∀ (y : M) (v w z : TangentSpace I y),
      riemannOp (LeviCivita g) y v w z =
        κ y • (g.inner y w z • v - g.inner y v z • w)) (x : M)
    (hV : LeviCivita g V x = 0) (hW : LeviCivita g W x = 0)
    (hZ : LeviCivita g Z x = 0) :
    g.inner x (LeviCivita g
      (fun y => (LeviCivita g).hessian (LeviCivita g) X y (V y) (W y)) x (U x)) (Z x) =
      mvfderiv I (κ : M → Real) x (U x) *
        (g.inner x (X x) (W x) * g.inner x (V x) (Z x) -
          g.inner x (V x) (W x) * g.inner x (X x) (Z x)) +
      κ x * (g.inner x (LeviCivita g X x (U x)) (W x) * g.inner x (V x) (Z x) -
        g.inner x (V x) (W x) * g.inner x (LeviCivita g X x (U x)) (Z x)) +
      (abstractHessian g φ x (U x) (V x) * g.inner x (W x) (Z x) +
        abstractHessian g φ x (U x) (W x) * g.inner x (V x) (Z x) -
        abstractHessian g φ x (U x) (Z x) * g.inner x (V x) (W x)) / 2 := by
  let pair (Y Z : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) : C^∞⟮I, M; Real⟯ :=
    ⟨fun y => g.inner y (Y y) (Z y), contMDiff_g_inner_of_smooth_sections g Y Z⟩
  let df (Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) : C^∞⟮I, M; Real⟯ :=
    ⟨fun y => mvfderiv I (φ : M → Real) y (Y y), mvfderiv_apply_contMDiff I φ φ.contMDiff Y⟩
  have hcov : CovariantDerivative.ContMDiffCovariantDerivative (LeviCivita g) ∞ := inferInstance
  have hA := contMDiffOn_univ.mp
    (hcov.contMDiff.contMDiff (by simpa using X.contMDiff.contMDiffOn))
  have hHom : CovariantDerivative.ContMDiffCovariantDerivative
      (HomConnectionGen.homBundleCovariantDerivativeGen
        I M E (TangentSpace I) E (TangentSpace I) (LeviCivita g) (LeviCivita g)) ∞ :=
    inferInstance
  have hH := contMDiffOn_univ.mp
    (hHom.contMDiff.contMDiff (by simpa using hA.contMDiffOn))
  let HVW : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
    ⟨fun y => (LeviCivita g).hessian (LeviCivita g) X y (V y) (W y),
      (hH.clm_bundle_apply V.contMDiff).clm_bundle_apply W.contMDiff⟩
  have heq := congrArg (fun f : M → Real => mvfderiv I f x (U x))
    (funext fun y => hessian_conformal_inner g X V W Z φ κ hX hR y)
  have hd := derivative_expression κ (pair X W) (pair V Z) (pair V W) (pair X Z)
    (df V) (pair W Z) (df W) (df Z) x (U x)
  change mvfderiv I (fun y => g.inner y (HVW y) (Z y)) x (U x) = _ at heq
  rw [normal_inner_derivative g HVW Z x (U x) hZ] at heq
  change _ = mvfderiv I
    (fun y => κ y * (pair X W y * pair V Z y - pair V W y * pair X Z y) +
      (df V y * pair W Z y + df W y * pair V Z y - df Z y * pair V W y) / 2) x (U x) at heq
  rw [hd] at heq
  simp only [pair, df, ContMDiffMap.coeFn_mk] at heq
  rw [normal_inner_derivative g X W x (U x) hW,
    normal_inner_derivative g V Z x (U x) hZ,
    normal_inner_derivative g V W x (U x) hW,
    normal_inner_derivative g X Z x (U x) hZ,
    normal_inner_derivative g W Z x (U x) hZ,
    normal_mvfderiv_derivative g φ V x (U x) hV,
    normal_mvfderiv_derivative g φ W x (U x) hW,
    normal_mvfderiv_derivative g φ Z x (U x) hZ] at heq
  change g.inner x (LeviCivita g
    (fun y => (LeviCivita g).hessian (LeviCivita g) X y (V y) (W y)) x (U x)) (Z x) = _ at heq
  simpa only [hV, hW, zero_apply, map_zero, zero_mul, mul_zero, add_zero, zero_add] using heq


end Hessian

section Surface
variable [I.Boundaryless]


omit [T2Space M] [I.Boundaryless] in
private theorem exists_orthonormal_pair_of_finrank_eq_two
    (g : SmoothRiemannianMetric I M) (hn : Module.finrank Real E = 2) (x : M) :
    ∃ B : Fin 2 → TangentSpace I x,
      ∀ i j, g.inner x (B i) (B j) = if i = j then 1 else 0 := by
  let _ : NeZero (Module.finrank Real E) := ⟨by omega⟩
  refine ⟨fun i => smoothOrthoFrame g x (Fin.cast hn.symm i) x, ?_⟩
  intro i j
  simpa only [Fin.cast_inj] using
    smoothOrthoFrame_orthonormal_at_center g x (Fin.cast hn.symm i) (Fin.cast hn.symm j)

private theorem abstractHessian_pair_eq_laplacian_of_finrank_eq_two
    (g : SmoothRiemannianMetric I M) (hn : Module.finrank Real E = 2)
    (f : C^∞⟮I, M; Real⟯) (x : M) (B : Fin 2 → TangentSpace I x)
    (hB : ∀ i j, g.inner x (B i) (B j) = if i = j then 1 else 0) :
    abstractHessian g f x (B 0) (B 0) + abstractHessian g f x (B 1) (B 1) =
      ΔG g f x := by
  let C : Fin (Module.finrank Real E) → TangentSpace I x := fun i => B (Fin.cast hn i)
  have hC : ∀ i j, g.inner x (C i) (C j) = if i = j then 1 else 0 := by
    intro i j
    simpa only [C, Fin.cast_inj] using hB (Fin.cast hn i) (Fin.cast hn j)
  have hs := sum_abstractHessian_orthonormal_eq_laplacian g f.contMDiff x C hC
  have heq : (∑ i : Fin (Module.finrank Real E), abstractHessian g f x (C i) (C i)) =
      ∑ i : Fin 2, abstractHessian g f x (B i) (B i) := by
    exact Fintype.sum_equiv (finCongr hn) _ _ (fun _ => rfl)
  rw [heq, Fin.sum_univ_two] at hs
  exact hs

omit [T2Space M] [I.Boundaryless] in
private theorem mvfderiv_eq_orthonormal_pair_of_finrank_eq_two
    (g : SmoothRiemannianMetric I M) (hn : Module.finrank Real E = 2)
    (f : M → Real) (x : M) (B : Fin 2 → TangentSpace I x)
    (hB : ∀ i j, g.inner x (B i) (B j) = if i = j then 1 else 0)
    (v : TangentSpace I x) :
    mvfderiv I f x v =
      g.inner x v (B 0) * mvfderiv I f x (B 0) +
        g.inner x v (B 1) * mvfderiv I f x (B 1) := by
  have hv := Riemannian.expand_orthonormal g x (ι := Fin 2) (by rw [Fintype.card_fin]; exact hn.symm) B hB v
  rw [Fin.sum_univ_two] at hv
  conv_lhs => rw [hv]
  rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul,
    g.symm x (B 0) v, g.symm x (B 1) v]

private theorem conformal_factor_curvature_identity
    (g : SmoothRiemannianMetric I M) (hn : Module.finrank Real E = 2)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (φ κ : C^∞⟮I, M; Real⟯)
    (hX : ∀ (y : M) (v w : TangentSpace I y),
      g.inner y (LeviCivita g X y v) w + g.inner y v (LeviCivita g X y w) =
        φ y * g.inner y v w)
    (hR : ∀ (y : M) (v w z : TangentSpace I y),
      riemannOp (LeviCivita g) y v w z =
        κ y • (g.inner y w z • v - g.inner y v z • w)) (x : M) :
    ΔG g φ x + 2 * κ x * φ x + 2 * mvfderiv I (κ : M → Real) x (X x) = 0 := by
  obtain ⟨B, hB⟩ := exists_orthonormal_pair_of_finrank_eq_two g hn x
  obtain ⟨V, hVx, hV⟩ := exists_section_with_value_and_covariantDerivative_zero (LeviCivita g) x (B 0)
  obtain ⟨W, hWx, hW⟩ := exists_section_with_value_and_covariantDerivative_zero (LeviCivita g) x (B 1)
  have h00 : g.inner x (V x) (V x) = 1 := by rw [hVx]; simpa using hB 0 0
  have h11 : g.inner x (W x) (W x) = 1 := by rw [hWx]; simpa using hB 1 1
  have h01 : g.inner x (V x) (W x) = 0 := by rw [hVx, hWx]; simpa using hB 0 1
  have h10 : g.inner x (W x) (V x) = 0 := by rw [g.symm, h01]
  have hleft := hessian_conformal_derivative_inner g X V W V W φ κ hX hR x hW hV hW
  have hright := hessian_conformal_derivative_inner g X W V V W φ κ hX hR x hV hV hW
  have hcomm := congrArg (fun z => g.inner x z (W x))
    (hessian_derivative_skew_of_covariantDerivative_eq_zero g X V W V x hV hW hV)
  simp only [map_sub, hR, map_smul, smul_apply, sub_apply, smul_eq_mul] at hcomm
  simp only [h00, h11, h01, h10, mul_zero, mul_one, zero_mul, zero_add, add_zero,
    sub_zero, zero_sub] at hleft hright hcomm
  rw [hleft, hright] at hcomm
  have hA0 := hX x (V x) (V x)
  rw [g.symm x (V x) _, h00, mul_one] at hA0
  have htr := abstractHessian_pair_eq_laplacian_of_finrank_eq_two g hn φ x B hB
  rw [← hVx, ← hWx] at htr
  have hderiv := mvfderiv_eq_orthonormal_pair_of_finrank_eq_two g hn (κ : M → Real) x B hB (X x)
  rw [← hVx, ← hWx] at hderiv
  rw [g.symm x (V x) (LeviCivita g X x (V x))] at hcomm
  linear_combination 2 * hcomm - 2 * κ x * hA0 - htr + 2 * hderiv

open DifferentialGeometry.Integral.DivergenceTheorem

theorem IsConformalVectorField.laplacian_divergence_add_scalarCurv_mul_divergence_of_finrank_eq_two
    (g : SmoothRiemannianMetric I M) (hn : Module.finrank Real E = 2)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (hX : IsConformalVectorField g X) (x : M) :
    ΔG g ⟨divergenceG g X, divergence_g_contMDiff g X⟩ x +
      scalarCurv g x * divergenceG g X x = -mvfderiv I (scalarCurv g) x (X x) := by
  let φ : C^∞⟮I, M; Real⟯ := ⟨divergenceG g X, divergence_g_contMDiff g X⟩
  let κ : C^∞⟮I, M; Real⟯ :=
    ⟨fun y => scalarCurv g y / 2, (scalarCurv_contMDiff g).div_const 2⟩
  have hφ : ∀ (y : M) (v w : TangentSpace I y),
      g.inner y (LeviCivita g X y v) w + g.inner y v (LeviCivita g X y w) =
        φ y * g.inner y v w := by
    intro y v w
    have h := (isConformalVectorField_iff_covariantDerivative_eq_divergence g X).mp hX y v w
    rw [hn] at h
    norm_num only [Nat.cast_ofNat, div_self (by norm_num : (2 : Real) ≠ 0), one_mul] at h
    exact h
  have h := conformal_factor_curvature_identity g hn X φ κ hφ
    (fun y v w z => by
      let _ : NeZero (Module.finrank Real E) := ⟨by omega⟩
      rw [riemannOp_eq_scalar_div_two_of_finrank_eq_two g hn, metricScalar_eq_scal g y]
      rfl) x
  have hd : mvfderiv I (κ : M → Real) x (X x) =
      mvfderiv I (scalarCurv g) x (X x) / 2 := by
    change mvfderiv I ((scalarCurv g) * fun _ => (2 : Real)⁻¹) x (X x) = _
    rw [_root_.mvfderiv_mul ((scalarCurv_contMDiff g).mdifferentiableAt (by simp))
      mdifferentiableAt_const, add_apply, smul_apply, smul_apply, mvfderiv_const]
    simp only [zero_apply, smul_eq_mul, mul_zero, zero_add, div_eq_mul_inv]
    ring
  rw [hd] at h
  change ΔG g φ x + 2 * (scalarCurv g x / 2) * divergenceG g X x +
    2 * (mvfderiv I (scalarCurv g) x (X x) / 2) = 0 at h
  change ΔG g φ x + scalarCurv g x * divergenceG g X x = _
  linarith

theorem IsConformalVectorField.laplacian_divergence_of_constant_scalarCurv
    (g : SmoothRiemannianMetric I M) (hn : Module.finrank Real E = 2)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (hX : IsConformalVectorField g X) {R : Real}
    (hR : ∀ y, scalarCurv g y = R) (x : M) :
    ΔG g ⟨divergenceG g X, divergence_g_contMDiff g X⟩ x =
      -R * divergenceG g X x := by
  have h := IsConformalVectorField.laplacian_divergence_add_scalarCurv_mul_divergence_of_finrank_eq_two g hn X hX x
  have hf : scalarCurv g = fun _ => R := funext hR
  rw [hf, mvfderiv_const, zero_apply, neg_zero] at h
  linarith

end Surface

end DifferentialGeometry.Geometry
