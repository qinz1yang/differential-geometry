import DifferentialGeometry.Geometry.Connection.Product
import DifferentialGeometry.Geometry.Connection.ChartBridge.Scalar.Hessian
import DifferentialGeometry.Geometry.Curvature.Riemann.Basic.Field
import DifferentialGeometry.Geometry.Operator.Gradient.NormSquared

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Bundle
open scoped Manifold ContDiff

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace Real F]
  [FiniteDimensional Real F]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {G : Type*} [TopologicalSpace G]
variable {J : ModelWithCorners Real F G}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M]
variable {N : Type*} [TopologicalSpace N] [ChartedSpace G N] [IsManifold J ∞ N]
  [T2Space N]

private def productLift
    (X : (x : M) → TangentSpace I x) (Y : (x : N) → TangentSpace J x)
    (x : M × N) : TangentSpace (I.prod J) x :=
  (X x.1, Y x.2)

omit [FiniteDimensional Real E] [FiniteDimensional Real F]
    [IsManifold I ∞ M] [IsManifold J ∞ N] [T2Space M] [T2Space N] in
@[simp] private theorem productLift_apply
    (X : (x : M) → TangentSpace I x) (Y : (x : N) → TangentSpace J x)
    (x : M × N) :
    productLift (I := I) (J := J) X Y x = (X x.1, Y x.2) := rfl

theorem Operator.gradFun_prod
    (g : SmoothRiemannianMetric I M) (h : SmoothRiemannianMetric J N)
    (f : C^∞⟮I, M; Real⟯) (k : C^∞⟮J, N; Real⟯) (x : M × N) :
    Operator.gradFun (I := I.prod J) (g.prod h)
        (fun q : M × N => f q.1 + k q.2) x =
      (Operator.gradFun (I := I) g f x.1,
        Operator.gradFun (I := J) h k x.2) := by
  rw [← productLift_apply]
  symm
  apply Connection.gradFun_unique (I := I.prod J) (g.prod h)
  intro z
  let zM : TangentSpace I x.1 := z.1
  let zN : TangentSpace J x.2 := z.2
  have hfprod : ContMDiff (I.prod J) 𝓘(Real) ∞ (fun q : M × N => f q.1) :=
    f.contMDiff.comp contMDiff_fst
  have hkprod : ContMDiff (I.prod J) 𝓘(Real) ∞ (fun q : M × N => k q.2) :=
    k.contMDiff.comp contMDiff_snd
  have hdfst : mvfderiv (I := I.prod J) (fun q : M × N => f q.1) x z =
      mvfderiv (I := I) f x.1 zM := by
    rw [show (fun q : M × N => f q.1) = f ∘ Prod.fst by rfl]
    rw [mvfderiv_comp_apply x
      (f.contMDiff.mdifferentiableAt (by simp)) mdifferentiableAt_fst z]
    rw [mfderiv_fst]
    change mvfderiv (I := I) f x.1 z.1 = mvfderiv (I := I) f x.1 zM
    rfl
  have hdsnd : mvfderiv (I := I.prod J) (fun q : M × N => k q.2) x z =
      mvfderiv (I := J) k x.2 zN := by
    rw [show (fun q : M × N => k q.2) = k ∘ Prod.snd by rfl]
    rw [mvfderiv_comp_apply x
      (k.contMDiff.mdifferentiableAt (by simp)) mdifferentiableAt_snd z]
    rw [mfderiv_snd]
    change mvfderiv (I := J) k x.2 z.2 = mvfderiv (I := J) k x.2 zN
    rfl
  have hfstLift : mfderiv (I.prod J) I Prod.fst x
      (productLift (I := I) (J := J)
        (fun q : M => Operator.gradFun (I := I) g f q)
        (fun q : N => Operator.gradFun (I := J) h k q) x) =
      Operator.gradFun (I := I) g f x.1 := by
    rw [productLift_apply, mfderiv_fst]
    rfl
  have hsndLift : mfderiv (I.prod J) J Prod.snd x
      (productLift (I := I) (J := J)
        (fun q : M => Operator.gradFun (I := I) g f q)
        (fun q : N => Operator.gradFun (I := J) h k q) x) =
      Operator.gradFun (I := J) h k x.2 := by
    rw [productLift_apply, mfderiv_snd]
    rfl
  have hfstz : mfderiv (I.prod J) I Prod.fst x z = zM := by
    rw [mfderiv_fst]
    rfl
  have hsndz : mfderiv (I.prod J) J Prod.snd x z = zN := by
    rw [mfderiv_snd]
    rfl
  rw [SmoothRiemannianMetric.prod_inner_mfderiv, hfstLift, hsndLift, hfstz, hsndz]
  rw [Connection.gradFun_metricDual_mvfderiv,
    Connection.gradFun_metricDual_mvfderiv]
  calc
    mvfderiv (I := I) f x.1 zM + mvfderiv (I := J) k x.2 zN =
        mvfderiv (I := I.prod J) (fun q : M × N => f q.1) x z +
          mvfderiv (I := I.prod J) (fun q : M × N => k q.2) x z := by
      rw [hdfst, hdsnd]
    _ = mvfderiv (I := I.prod J)
        ((fun q : M × N => f q.1) + (fun q : M × N => k q.2)) x z := by
      rw [mvfderiv_add
        (hfprod.mdifferentiableAt (by simp)) (hkprod.mdifferentiableAt (by simp)),
        add_apply]
    _ = mvfderiv (I := I.prod J) (fun q : M × N => f q.1 + k q.2) x z := rfl

set_option backward.isDefEq.respectTransparency false in
theorem Operator.normGradSqFun_prod
    (g : SmoothRiemannianMetric I M) (h : SmoothRiemannianMetric J N)
    (f : C^∞⟮I, M; Real⟯) (k : C^∞⟮J, N; Real⟯) (x : M × N) :
    Operator.normGradSqFun (I := I.prod J) (g.prod h)
        (fun q : M × N => f q.1 + k q.2) x =
      Operator.normGradSqFun (I := I) g f x.1 +
        Operator.normGradSqFun (I := J) h k x.2 := by
  rw [Operator.normGradSqFun_def,
    Operator.gradFun_prod (I := I) (J := J) g h f k x,
    SmoothRiemannianMetric.prod_inner_mfderiv, mfderiv_fst, mfderiv_snd]
  change g.inner x.1 (Operator.gradFun (I := I) g f x.1)
        (Operator.gradFun (I := I) g f x.1) +
      h.inner x.2 (Operator.gradFun (I := J) h k x.2)
        (Operator.gradFun (I := J) h k x.2) = _
  rw [← Operator.normGradSqFun_def, ← Operator.normGradSqFun_def]

theorem Operator.hessFun_prod
    [I.Boundaryless] [J.Boundaryless]
    (g : SmoothRiemannianMetric I M) (h : SmoothRiemannianMetric J N)
    (f : C^∞⟮I, M; Real⟯) (k : C^∞⟮J, N; Real⟯)
    (x : M × N) (u v : TangentSpace (I.prod J) x) :
    Operator.hessFun (I := I.prod J) (g.prod h)
        (fun q : M × N => f q.1 + k q.2) x u v =
      Operator.hessFun (I := I) g f x.1 u.1 v.1 +
        Operator.hessFun (I := J) h k x.2 u.2 v.2 := by
  let uM : TangentSpace I x.1 := u.1
  let uN : TangentSpace J x.2 := u.2
  let vM : TangentSpace I x.1 := v.1
  let vN : TangentSpace J x.2 := v.2
  change Operator.hessFun (I := I.prod J) (g.prod h)
      (fun q : M × N => f q.1 + k q.2) x u v =
    Operator.hessFun (I := I) g f x.1 uM vM +
      Operator.hessFun (I := J) h k x.2 uN vN
  have hF : ContMDiff (I.prod J) 𝓘(Real) ∞
      (fun q : M × N => f q.1 + k q.2) :=
    (f.contMDiff.comp contMDiff_fst).add (k.contMDiff.comp contMDiff_snd)
  have hgrad :
      (fun q : M × N => Operator.gradFun (I := I.prod J) (g.prod h)
        (fun p : M × N => f p.1 + k p.2) q) =
      productLift (I := I) (J := J)
        (fun q : M => Operator.gradFun (I := I) g f q)
        (fun q : N => Operator.gradFun (I := J) h k q) := by
    funext q
    rw [Operator.gradFun_prod (I := I) (J := J) g h f k q]
    exact (productLift_apply (I := I) (J := J)
      (fun p : M => Operator.gradFun (I := I) g f p)
      (fun p : N => Operator.gradFun (I := J) h k p) q).symm
  have hgradM := Connection.gradFun_contMDiff_total_section
    (I := I) g f.contMDiff
  have hgradN := Connection.gradFun_contMDiff_total_section
    (I := J) h k.contMDiff
  let X := Curvature.smoothExtensionTangent (I := I) x.1 uM
  let Y := Curvature.smoothExtensionTangent (I := J) x.2 uN
  have hX := Curvature.smoothExtensionTangent_contMDiff (I := I) x.1 uM
  have hY := Curvature.smoothExtensionTangent_contMDiff (I := J) x.2 uN
  have hXx : X x.1 = uM := Curvature.smoothExtensionTangent_eq x.1 uM
  have hYx : Y x.2 = uN := Curvature.smoothExtensionTangent_eq x.2 uN
  have hu : u = productLift (I := I) (J := J) X Y x := by
    rw [productLift_apply, hXx, hYx]
    exact (Prod.eta u).symm
  let A : (q : M) → TangentSpace I q := fun q =>
    (Connection.LeviCivita (I := I) g).toFun
      (fun p => Operator.gradFun (I := I) g f p) q (X q)
  let B : (q : N) → TangentSpace J q := fun q =>
    (Connection.LeviCivita (I := J) h).toFun
      (fun p => Operator.gradFun (I := J) h k p) q (Y q)
  have hconn : (Connection.LeviCivita (I := I.prod J) (g.prod h)).toFun
      (fun q : M × N => Operator.gradFun (I := I.prod J) (g.prod h)
        (fun p : M × N => f p.1 + k p.2) q) x u =
      productLift (I := I) (J := J) A B x := by
    rw [hgrad, hu]
    change (Connection.LeviCivita (I := I.prod J) (g.prod h)).toFun
        (fun p : M × N =>
          (Operator.gradFun (I := I) g f p.1,
            Operator.gradFun (I := J) h k p.2)) x (X x.1, Y x.2) =
      (A x.1, B x.2)
    simpa only [A, B] using Connection.leviCivita_prod (I := I) (J := J) g h
      X (fun p => Operator.gradFun (I := I) g f p)
      Y (fun p => Operator.gradFun (I := J) h k p)
      hX hgradM hY hgradN x
  have hfstConn : mfderiv (I.prod J) I Prod.fst x
      (productLift (I := I) (J := J) A B x) = A x.1 := by
    rw [productLift_apply, mfderiv_fst]
    rfl
  have hsndConn : mfderiv (I.prod J) J Prod.snd x
      (productLift (I := I) (J := J) A B x) = B x.2 := by
    rw [productLift_apply, mfderiv_snd]
    rfl
  have hfstv : mfderiv (I.prod J) I Prod.fst x v = vM := by
    rw [mfderiv_fst]
    rfl
  have hsndv : mfderiv (I.prod J) J Prod.snd x v = vN := by
    rw [mfderiv_snd]
    rfl
  rw [Connection.hessFun_eq_cov_grad (I := I.prod J) (g.prod h) hF x u v]
  rw [Connection.hessFun_eq_cov_grad (I := I) g f.contMDiff x.1 uM vM]
  rw [Connection.hessFun_eq_cov_grad (I := J) h k.contMDiff x.2 uN vN]
  rw [hconn, SmoothRiemannianMetric.prod_inner_mfderiv,
    hfstConn, hsndConn, hfstv, hsndv]
  change g.inner x.1
      ((Connection.LeviCivita (I := I) g).toFun
        (fun p => Operator.gradFun (I := I) g f p) x.1 (X x.1)) vM +
    h.inner x.2
      ((Connection.LeviCivita (I := J) h).toFun
        (fun p => Operator.gradFun (I := J) h k p) x.2 (Y x.2)) vN = _
  rw [hXx, hYx]

end DifferentialGeometry.Geometry
