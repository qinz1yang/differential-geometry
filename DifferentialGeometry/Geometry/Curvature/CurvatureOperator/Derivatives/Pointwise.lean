import DifferentialGeometry.Geometry.Connection.LeviCivita.Curvature.Sections
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.Derivatives.ParsevalTrace

noncomputable section

set_option autoImplicit false

open Bundle Manifold DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Geometry.Connection DifferentialGeometry.Geometry.Curvature
open scoped Manifold Topology ContDiff

namespace DifferentialGeometry
namespace Integral
namespace Connection

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private noncomputable def tangentExt
    (x : M) (v : TangentSpace I x) :
    ContMDiffSection I E ∞ (TangentSpace I : M -> Type _) :=
  ContMDiffSection.mk
    (smoothExtensionTangent (I := I) x v)
    (smoothExtensionTangent_contMDiff (I := I) x v)

noncomputable def nablaRiemannOp
    (g : SmoothRiemannianMetric I M) (x : M)
    (D X Y Z : TangentSpace I x) : TangentSpace I x :=
  nablaBaseSlotCurv (I := I) g
    (tangentExt (I := I) x D)
    (tangentExt (I := I) x X)
    (tangentExt (I := I) x Y) x Z

omit [CompleteSpace E] [I.Boundaryless] [BoundarylessManifold I M] [SigmaCompactSpace M] in
private theorem nablaRiemannOp_eq_curvCov
    (g : SmoothRiemannianMetric I M) (x : M)
    (D X Y Z : TangentSpace I x) :
    nablaRiemannOp (I := I) g x D X Y Z =
      curvCovDerivOpAt (I := I) (LeviCivita (I := I) g)
        (tangentExt (I := I) x D)
        (tangentExt (I := I) x X)
        (tangentExt (I := I) x Y)
        (tangentExt (I := I) x Z) x := by
  rfl

omit [I.Boundaryless] [BoundarylessManifold I M] [SigmaCompactSpace M] in
theorem canNablaRm_apply
    (g : SmoothRiemannianMetric I M)
    (D X Y Z W : ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M -> Type _))
    (x : M) :
    let cov := leviCivitaConnectionOfMetric (I := I) g
    let hcov :=
      leviCivitaConnectionOfMetric_contMDiffCovariantDerivativeLocally
        (I := I) (M := M) g
    let Rm04 : Tensor04Section (I := I) (M := M) :=
      CovariantDerivative.rm04Section (I := I) g cov hcov
    totalNabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        4 cov Rm04 x (vec5 (I := I) (D x) (X x) (Y x) (Z x) (W x)) =
      g.inner x (W x) (curvCovDerivOpAt (I := I) cov D X Y Z x) := by
  classical
  let cov := leviCivitaConnectionOfMetric (I := I) g
  let hcov :=
    leviCivitaConnectionOfMetric_contMDiffCovariantDerivativeLocally
      (I := I) (M := M) g
  let Rm04 : Tensor04Section (I := I) (M := M) :=
    CovariantDerivative.rm04Section (I := I) g cov hcov
  let Rcurv : ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M -> Type _) :=
    ⟨fun p : M =>
      connectionRiemannCurvatureField (I := I) cov
        (fun q : M => X q) (fun q : M => Y q) (fun q : M => Z q) p,
      by
        intro p
        exact CovariantDerivative.curvField_contMDiffAt
          (I := I) cov hcov X Y Z p⟩
  let DX : ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M -> Type _) :=
    ⟨fun p : M => (cov (fun q : M => X q) p) (D p), by
      intro p
      exact CovariantDerivative.cov_smooth_apply_contMDiffAt
        (I := I) cov hcov D X p⟩
  let DY : ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M -> Type _) :=
    ⟨fun p : M => (cov (fun q : M => Y q) p) (D p), by
      intro p
      exact CovariantDerivative.cov_smooth_apply_contMDiffAt
        (I := I) cov hcov D Y p⟩
  let DZ : ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M -> Type _) :=
    ⟨fun p : M => (cov (fun q : M => Z q) p) (D p), by
      intro p
      exact CovariantDerivative.cov_smooth_apply_contMDiffAt
        (I := I) cov hcov D Z p⟩
  let DW : ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M -> Type _) :=
    ⟨fun p : M => (cov (fun q : M => W q) p) (D p), by
      intro p
      exact CovariantDerivative.cov_smooth_apply_contMDiffAt
        (I := I) cov hcov D W p⟩
  let slots : Fin 4 -> ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M -> Type _)
    | ⟨0, _⟩ => X
    | ⟨1, _⟩ => Y
    | ⟨2, _⟩ => Z
    | ⟨3, _⟩ => W
  dsimp only
  have htotal :=
    totalNabla0SFun_apply_section
      (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      4 cov D Rm04 x (vec4 (I := I) (X x) (Y x) (Z x) (W x))
  have heval :=
    nabla0SFun_eval_smooth_slots
      (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      cov D slots Rm04 x
  have hfun :
      (fun p : M => Rm04 p (fun a : Fin 4 => slots a p)) =
        fun p : M => g.inner p (W p) (Rcurv p) := by
    funext p
    change
      CovariantDerivative.rm04Section (I := I) g cov hcov p
          (vec4 (I := I) (X p) (Y p) (Z p) (W p)) =
        g.inner p (W p)
          (connectionRiemannCurvatureField (I := I) cov
            (fun q : M => X q) (fun q : M => Y q) (fun q : M => Z q) p)
    exact CovariantDerivative.rm04Section_apply_smooth
      (I := I) g cov hcov X Y Z W p
  have hDmd : MDiffAt (T% fun p : M => D p) x :=
    (D.contMDiff.contMDiffAt (x := x)).mdifferentiableAt (by simp)
  have hWmd : MDiffAt (T% fun p : M => W p) x :=
    (W.contMDiff.contMDiffAt (x := x)).mdifferentiableAt (by simp)
  have hRmd : MDiffAt (T% fun p : M => Rcurv p) x :=
    (Rcurv.contMDiff.contMDiffAt (x := x)).mdifferentiableAt (by simp)
  have hmetric :=
    metric_compatible_apply
      (I := I) (x := x)
      (leviCivitaConnectionOfMetric_isMetricCompatible (I := I) g)
      (fun p : M => D p) (fun p : M => W p) (fun p : M => Rcurv p)
      hDmd hWmd hRmd
  have hderiv :
      mvfderiv (I := I)
          (fun p : M => Rm04 p (fun a : Fin 4 => slots a p))
          x (D x) =
        g.inner x (DW x) (Rcurv x) +
          g.inner x (W x) ((cov (fun p : M => Rcurv p) x) (D x)) := by
    rw [hfun, hmetric]
    rfl
  have hcorr0 :
      Rm04 x
          (Function.update (fun b : Fin 4 => slots b x) 0
            ((cov (fun p : M => slots 0 p) x) (D x))) =
        g.inner x (W x)
          (connectionRiemannCurvatureField (I := I) cov
            (fun p : M => DX p) (fun p : M => Y p) (fun p : M => Z p) x) := by
    change
      CovariantDerivative.rm04Section (I := I) g cov hcov x
          (vec4 (I := I) (DX x) (Y x) (Z x) (W x)) = _
    exact CovariantDerivative.rm04Section_apply_smooth
      (I := I) g cov hcov DX Y Z W x
  have hcorr1 :
      Rm04 x
          (Function.update (fun b : Fin 4 => slots b x) 1
            ((cov (fun p : M => slots 1 p) x) (D x))) =
        g.inner x (W x)
          (connectionRiemannCurvatureField (I := I) cov
            (fun p : M => X p) (fun p : M => DY p) (fun p : M => Z p) x) := by
    change
      CovariantDerivative.rm04Section (I := I) g cov hcov x
          (vec4 (I := I) (X x) (DY x) (Z x) (W x)) = _
    exact CovariantDerivative.rm04Section_apply_smooth
      (I := I) g cov hcov X DY Z W x
  have hcorr2 :
      Rm04 x
          (Function.update (fun b : Fin 4 => slots b x) 2
            ((cov (fun p : M => slots 2 p) x) (D x))) =
        g.inner x (W x)
          (connectionRiemannCurvatureField (I := I) cov
            (fun p : M => X p) (fun p : M => Y p) (fun p : M => DZ p) x) := by
    change
      CovariantDerivative.rm04Section (I := I) g cov hcov x
          (vec4 (I := I) (X x) (Y x) (DZ x) (W x)) = _
    exact CovariantDerivative.rm04Section_apply_smooth
      (I := I) g cov hcov X Y DZ W x
  have hcorr3 :
      Rm04 x
          (Function.update (fun b : Fin 4 => slots b x) 3
            ((cov (fun p : M => slots 3 p) x) (D x))) =
        g.inner x (DW x) (Rcurv x) := by
    change
      CovariantDerivative.rm04Section (I := I) g cov hcov x
          (vec4 (I := I) (X x) (Y x) (Z x) (DW x)) =
        g.inner x (DW x)
          (connectionRiemannCurvatureField (I := I) cov
            (fun p : M => X p) (fun p : M => Y p) (fun p : M => Z p) x)
    exact CovariantDerivative.rm04Section_apply_smooth
      (I := I) g cov hcov X Y Z DW x
  have hcorr :
      (∑ a : Fin 4,
          Rm04 x
            (Function.update (fun b : Fin 4 => slots b x) a
              ((cov (fun p : M => slots a p) x) (D x)))) =
        g.inner x (W x)
            (connectionRiemannCurvatureField (I := I) cov
              (fun p : M => DX p) (fun p : M => Y p) (fun p : M => Z p) x) +
          g.inner x (W x)
            (connectionRiemannCurvatureField (I := I) cov
              (fun p : M => X p) (fun p : M => DY p) (fun p : M => Z p) x) +
          g.inner x (W x)
            (connectionRiemannCurvatureField (I := I) cov
              (fun p : M => X p) (fun p : M => Y p) (fun p : M => DZ p) x) +
          g.inner x (DW x) (Rcurv x) := by
    rw [Fin.sum_univ_four, hcorr0, hcorr1, hcorr2, hcorr3]
  have hRcurv_fun :
      (fun p : M => Rcurv p) =
        fun p : M =>
          connectionRiemannCurvatureField (I := I) cov
            (fun q : M => X q) (fun q : M => Y q) (fun q : M => Z q) p := rfl
  have hDX_fun :
      (fun p : M => DX p) =
        fun p : M => (cov (fun q : M => X q) p) (D p) := rfl
  have hDY_fun :
      (fun p : M => DY p) =
        fun p : M => (cov (fun q : M => Y q) p) (D p) := rfl
  have hDZ_fun :
      (fun p : M => DZ p) =
        fun p : M => (cov (fun q : M => Z q) p) (D p) := rfl
  calc
    totalNabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        4 cov Rm04 x (vec5 (I := I) (D x) (X x) (Y x) (Z x) (W x)) =
      nabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        4 cov D Rm04 x (vec4 (I := I) (X x) (Y x) (Z x) (W x)) := by
          rw [show vec5 (I := I) (D x) (X x) (Y x) (Z x) (W x) =
              Fin.cons (D x) (vec4 (I := I) (X x) (Y x) (Z x) (W x)) by
            funext a
            fin_cases a <;> rfl]
          exact htotal
    _ = nabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        4 cov D Rm04 x (fun a : Fin 4 => slots a x) := by
          congr 1
          funext a
          fin_cases a <;> rfl
    _ = mvfderiv (I := I)
          (fun p : M => Rm04 p (fun a : Fin 4 => slots a p))
          x (D x) -
        ∑ a : Fin 4,
          Rm04 x
            (Function.update (fun b : Fin 4 => slots b x) a
              ((cov (fun p : M => slots a p) x) (D x))) := heval
    _ = g.inner x (W x) (curvCovDerivOpAt (I := I) cov D X Y Z x) := by
      rw [hderiv, hcorr]
      rw [hRcurv_fun, hDX_fun, hDY_fun, hDZ_fun]
      simp only [curvCovDerivOpAt, sub_eq_add_neg, map_add, map_neg]
      ring

omit [I.Boundaryless] [BoundarylessManifold I M] [SigmaCompactSpace M] in
theorem nablaRm04_apply
    (g : SmoothRiemannianMetric I M) (x : M)
    (D X Y Z W : TangentSpace I x) :
    let cov := leviCivitaConnectionOfMetric (I := I) g
    let hcov :=
      leviCivitaConnectionOfMetric_contMDiffCovariantDerivativeLocally
        (I := I) (M := M) g
    let Rm04 : Tensor04Section (I := I) (M := M) :=
      CovariantDerivative.rm04Section (I := I) g cov hcov
    totalNabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        4 cov Rm04 x (vec5 (I := I) D X Y Z W) =
      g.inner x W (nablaRiemannOp (I := I) g x D X Y Z) := by
  let Ds := tangentExt (I := I) x D
  let Xs := tangentExt (I := I) x X
  let Ys := tangentExt (I := I) x Y
  let Zs := tangentExt (I := I) x Z
  let Ws := tangentExt (I := I) x W
  have h := canNablaRm_apply (I := I) g Ds Xs Ys Zs Ws x
  have hDs : Ds x = D := smoothExtensionTangent_eq (I := I) x D
  have hXs : Xs x = X := smoothExtensionTangent_eq (I := I) x X
  have hYs : Ys x = Y := smoothExtensionTangent_eq (I := I) x Y
  have hZs : Zs x = Z := smoothExtensionTangent_eq (I := I) x Z
  have hWs : Ws x = W := smoothExtensionTangent_eq (I := I) x W
  rw [hDs, hXs, hYs, hZs, hWs] at h
  rw [nablaRiemannOp_eq_curvCov (I := I)]
  rw [LeviCivita_eq_leviCivitaConnectionOfMetric]
  exact h

omit [I.Boundaryless] [BoundarylessManifold I M] [SigmaCompactSpace M] in
theorem nablaRiemannOp_eq
    (g : SmoothRiemannianMetric I M)
    (D X Y Z : ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M -> Type _))
    (x : M) :
    nablaRiemannOp (I := I) g x (D x) (X x) (Y x) (Z x) =
      curvCovDerivOpAt (I := I)
        (leviCivitaConnectionOfMetric (I := I) g) D X Y Z x := by
  let lhs :=
    nablaRiemannOp (I := I) g x (D x) (X x) (Y x) (Z x)
  let rhs :=
    curvCovDerivOpAt (I := I)
      (leviCivitaConnectionOfMetric (I := I) g) D X Y Z x
  let Q := tangentExt (I := I) x (lhs - rhs)
  have hQx : Q x = lhs - rhs :=
    smoothExtensionTangent_eq (I := I) x (lhs - rhs)
  have hpoint :=
    nablaRm04_apply (I := I) g x (D x) (X x) (Y x) (Z x) (lhs - rhs)
  have hsection :=
    canNablaRm_apply (I := I) g D X Y Z Q x
  rw [hQx] at hsection
  have hpair :
      g.inner x (lhs - rhs) lhs = g.inner x (lhs - rhs) rhs := by
    exact hpoint.symm.trans hsection
  have hzero : g.inner x (lhs - rhs) (lhs - rhs) = 0 := by
    rw [map_sub, hpair, sub_self]
  have hsub : lhs - rhs = 0 := by
    by_contra hne
    exact (ne_of_gt (g.pos x (lhs - rhs) hne)) hzero
  exact sub_eq_zero.mp hsub

omit [I.Boundaryless] [BoundarylessManifold I M] [SigmaCompactSpace M] in
theorem nablaRiemannOp_sec
    (g : SmoothRiemannianMetric I M)
    (D X Y Z : ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M -> Type _))
    (x : M) :
    nablaRiemannOp (I := I) g x (D x) (X x) (Y x) (Z x) =
      nablaCurvSec
        (leviCivitaConnectionOfMetric (I := I) g) D X Y Z x := by
  rw [nablaRiemannOp_eq]
  rfl

end Connection
end Integral
end DifferentialGeometry

end
