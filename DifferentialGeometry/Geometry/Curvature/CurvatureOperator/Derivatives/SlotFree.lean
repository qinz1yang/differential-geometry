import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.TensorAction.Field
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.Derivatives.Pointwise

noncomputable section

open Bundle Manifold DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Geometry.Connection DifferentialGeometry.Geometry.Curvature
open scoped Manifold Topology ContDiff BigOperators

namespace DifferentialGeometry
namespace Integral
namespace Connection

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

noncomputable def slotFreeOpCc (g : SmoothRiemannianMetric I M) (s : ℕ) :
    L2.SmoothCcTensor g s (s + 2) where
  toSection :=
    { toFun := fun x => TensorRSSpace.ofCLM
        (slotFreeCurvOpFib (I := I) (M := M) g s x)
      contMDiff_toFun := slotFreeCurvOpFib_contMDiff (I := I) (M := M) g s }
  hasCompactSupport := HasCompactSupport.of_compactSpace _

omit [I.Boundaryless] [SigmaCompactSpace M] in
@[simp] theorem slotFreeOpCc_apply
    (g : SmoothRiemannianMetric I M) (s : ℕ) (x : M) :
    (slotFreeOpCc (I := I) (M := M) g s).toSection x =
      TensorRSSpace.ofCLM
        (slotFreeCurvOpFib (I := I) (M := M) g s x) := rfl

omit [CompactSpace M] [SigmaCompactSpace M] in
private lemma slotFree_riem_eval
    (g : SmoothRiemannianMetric I M) (s : ℕ)
    (P Q : ContMDiffSection I E ∞ (fun y : M => TangentSpace I y))
    (B : ContMDiffSection I (Tensor0SModel s ℝ E) ∞
      (fun y : M => Tensor0SSpace s I y))
    (y : M) (q : Fin s → TangentSpace I y) :
    Tensor0SSpace.eval
        ((show Tensor0SSpace s I y →L[ℝ] Tensor0SSpace (s + 2) I y from
          TensorRSSpace.ofCLM
            (slotFreeCurvOpFib (I := I) (M := M) g s y)) (B y))
        (Fin.cons (P y) (Fin.cons (Q y) q)) =
      Tensor0SSpace.eval
        (riemannSec
          (Tensor0SNabla.tensor0SCovariantDerivative I M s
          (LeviCivita (I := I) g))
          (fun z => P z) (fun z => Q z) (fun z => B z) y) q := by
  classical
  change Tensor0SSpace.eval
      (slotFreeCurvOpFib (I := I) (M := M) g s y (B y))
      (Fin.cons (P y) (Fin.cons (Q y) q)) = _
  rw [slotFreeCurvOpFib_apply_eval (I := I) (M := M) g s y (B y)
    (P y) (Q y) q]
  rw [riemannSec_tensor0SCov_apply_eval (I := I) (M := M) g s P Q
    (fun z => B z) B.contMDiff y q]
  apply congrArg Neg.neg
  refine Finset.sum_congr rfl (fun k _ => ?_)
  refine congrArg (fun z : TangentSpace I y =>
    Tensor0SSpace.eval (B y) (Function.update q k z)) ?_
  rw [baseSlotCurv]
  rw [riemannSec_eq_riemannOp_smooth
    (cov := LeviCivita (I := I) g) P.contMDiff Q.contMDiff
    (smoothExtensionTangent_contMDiff (I := I) y (q k))]
  rw [smoothExtensionTangent_eq (I := I) y (q k)]

omit [SigmaCompactSpace M] in
private theorem slotFree_cov_sec
    (g : SmoothRiemannianMetric I M) (s : ℕ)
    (D U W : ContMDiffSection I E ∞ (fun y : M => TangentSpace I y))
    (Asec : ContMDiffSection I (Tensor0SModel s ℝ E) ∞
      (fun y : M => Tensor0SSpace s I y))
    (x : M) (m : Fin s → TangentSpace I x) :
    Tensor0SSpace.eval
        ((show Tensor0SSpace s I x →L[ℝ] Tensor0SSpace (s + 2) I x from
          TensorRSNabla.tensorRSCovariantDerivative I M s (s + 2)
            (LeviCivita (I := I) g)
            (slotFreeOpCc (I := I) (M := M) g s).toSection x (D x)) (Asec x))
        (Fin.cons (U x) (Fin.cons (W x) m)) =
      Tensor0SSpace.eval
        (nablaTensor0SCurv (I := I) g s D U W (fun y => Asec y) x) m := by
  classical
  let V : ∀ y : M, Tensor0SSpace (s + 2) I y := fun y =>
    (show Tensor0SSpace s I y →L[ℝ] Tensor0SSpace (s + 2) I y from
      (slotFreeOpCc (I := I) (M := M) g s).toSection y) (Asec y)
  have hV_smooth :
      ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel (s + 2) ℝ E)) ∞
        (fun y : M => TotalSpace.mk' (Tensor0SModel (s + 2) ℝ E)
          (E := fun z : M => Tensor0SSpace (s + 2) I z) y (V y)) := by
    exact ContMDiff.clm_bundle_apply (b := id)
      (slotFreeOpCc (I := I) (M := M) g s).toSection.contMDiff Asec.contMDiff
  have hV_at : TensorSectionMDiffAt (I := I) (s + 2) V x :=
    (hV_smooth x).mdifferentiableAt (by simp)
  let VU : ∀ y : M, Tensor0SSpace (s + 1) I y := fun y =>
    Tensor0SNabla.curriedSection I M V y (U y)
  have hVU_smooth :
      ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel (s + 1) ℝ E)) ∞
        (fun y : M => TotalSpace.mk' (Tensor0SModel (s + 1) ℝ E)
          (E := fun z : M => Tensor0SSpace (s + 1) I z) y (VU y)) := by
    exact ContMDiff.clm_bundle_apply (b := id)
      ((Tensor0SNabla.contMDiff_curriedSection_iff_section I M V).mp hV_smooth)
      U.contMDiff
  have hVU_at : TensorSectionMDiffAt (I := I) (s + 1) VU x :=
    (hVU_smooth x).mdifferentiableAt (by simp)
  let DU : ContMDiffSection I E ∞ (fun y : M => TangentSpace I y) :=
    ⟨fun y => (LeviCivita (I := I) g).toFun (fun z => U z) y (D y),
      covApply_contMDiff (cov := LeviCivita (I := I) g) D.contMDiff U.contMDiff⟩
  let DW : ContMDiffSection I E ∞ (fun y : M => TangentSpace I y) :=
    ⟨fun y => (LeviCivita (I := I) g).toFun (fun z => W z) y (D y),
      covApply_contMDiff (cov := LeviCivita (I := I) g) D.contMDiff W.contMDiff⟩
  let DA : ContMDiffSection I (Tensor0SModel s ℝ E) ∞
      (fun y : M => Tensor0SSpace s I y) :=
    ⟨fun y => Tensor0SNabla.tensor0SCovariantDerivative I M s
        (LeviCivita (I := I) g) (fun z => Asec z) y (D y),
      covApply_contMDiff
        (cov := Tensor0SNabla.tensor0SCovariantDerivative I M s
          (LeviCivita (I := I) g)) D.contMDiff Asec.contMDiff⟩
  have hDUfun :
      covApply (LeviCivita (I := I) g) (fun y => D y) (fun y => U y) =
        (fun y => DU y) := by
    funext y
    rfl
  have hDWfun :
      covApply (LeviCivita (I := I) g) (fun y => D y) (fun y => W y) =
        (fun y => DW y) := by
    funext y
    rfl
  have hDAfun :
      covApply (Tensor0SNabla.tensor0SCovariantDerivative I M s
          (LeviCivita (I := I) g)) (fun y => D y) (fun y => Asec y) =
        (fun y => DA y) := by
    funext y
    rfl
  have hVW :
      (fun y : M => Tensor0SNabla.curriedSection I M VU y (W y)) =
        (fun y : M => riemannSec
          (Tensor0SNabla.tensor0SCovariantDerivative I M s
            (LeviCivita (I := I) g))
          (fun z => U z) (fun z => W z) (fun z => Asec z) y) := by
    funext y
    apply (tensor0SSpaceFiberContinuousLinearEquiv (I := I) s y).injective
    apply ContinuousMultilinearMap.ext
    intro q
    change Tensor0SSpace.eval
        (Tensor0SNabla.curriedSection I M VU y (W y)) q =
      Tensor0SSpace.eval
        (riemannSec
          (Tensor0SNabla.tensor0SCovariantDerivative I M s
            (LeviCivita (I := I) g))
          (fun z => U z) (fun z => W z) (fun z => Asec z) y) q
    rw [Tensor0SNabla.curriedSection_apply,
      TensorMultilinear.tensor0S_curry_apply_eval]
    change Tensor0SSpace.eval
        (Tensor0SNabla.curriedSection I M V y (U y)) (Fin.cons (W y) q) = _
    rw [Tensor0SNabla.curriedSection_apply,
      TensorMultilinear.tensor0S_curry_apply_eval]
    simpa only [V, slotFreeOpCc_apply] using
      slotFree_riem_eval (I := I) (M := M) g s U W Asec y q
  have hDU :
      Tensor0SSpace.eval (V x)
          (Fin.cons ((LeviCivita (I := I) g).toFun (fun y => U y) x (D x))
            (Fin.cons (W x) m)) =
        Tensor0SSpace.eval
          (riemannSec
            (Tensor0SNabla.tensor0SCovariantDerivative I M s
              (LeviCivita (I := I) g))
            (fun y => DU y) (fun y => W y) (fun y => Asec y) x) m := by
    change Tensor0SSpace.eval (V x) (Fin.cons (DU x) (Fin.cons (W x) m)) =
      Tensor0SSpace.eval
        (riemannSec
          (Tensor0SNabla.tensor0SCovariantDerivative I M s
            (LeviCivita (I := I) g))
          (fun y => DU y) (fun y => W y) (fun y => Asec y) x) m
    exact slotFree_riem_eval (I := I) (M := M) g s DU W Asec x m
  have hDW :
      Tensor0SSpace.eval (VU x)
          (Fin.cons ((LeviCivita (I := I) g).toFun (fun y => W y) x (D x)) m) =
        Tensor0SSpace.eval
          (riemannSec
            (Tensor0SNabla.tensor0SCovariantDerivative I M s
              (LeviCivita (I := I) g))
            (fun y => U y) (fun y => DW y) (fun y => Asec y) x) m := by
    change Tensor0SSpace.eval
        (Tensor0SNabla.curriedSection I M V x (U x)) (Fin.cons (DW x) m) =
      Tensor0SSpace.eval
        (riemannSec
          (Tensor0SNabla.tensor0SCovariantDerivative I M s
            (LeviCivita (I := I) g))
          (fun y => U y) (fun y => DW y) (fun y => Asec y) x) m
    rw [Tensor0SNabla.curriedSection_apply,
      TensorMultilinear.tensor0S_curry_apply_eval]
    exact slotFree_riem_eval (I := I) (M := M) g s U DW Asec x m
  have hDA :
      Tensor0SSpace.eval
          ((show Tensor0SSpace s I x →L[ℝ] Tensor0SSpace (s + 2) I x from
            (slotFreeOpCc (I := I) (M := M) g s).toSection x)
            (Tensor0SNabla.tensor0SCovariantDerivative I M s
              (LeviCivita (I := I) g) (fun y => Asec y) x (D x)))
          (Fin.cons (U x) (Fin.cons (W x) m)) =
        Tensor0SSpace.eval
          (riemannSec
            (Tensor0SNabla.tensor0SCovariantDerivative I M s
              (LeviCivita (I := I) g))
            (fun y => U y) (fun y => W y) (fun y => DA y) x) m := by
    change Tensor0SSpace.eval
        ((show Tensor0SSpace s I x →L[ℝ] Tensor0SSpace (s + 2) I x from
          (slotFreeOpCc (I := I) (M := M) g s).toSection x) (DA x))
        (Fin.cons (U x) (Fin.cons (W x) m)) =
      Tensor0SSpace.eval
        (riemannSec
          (Tensor0SNabla.tensor0SCovariantDerivative I M s
            (LeviCivita (I := I) g))
          (fun y => U y) (fun y => W y) (fun y => DA y) x) m
    exact slotFree_riem_eval (I := I) (M := M) g s U W DA x m
  have hHom := TensorRSNabla.tensorRSCovariantDerivative_apply
    (I := I) (M := M) s (s + 2) (LeviCivita (I := I) g)
    (slotFreeOpCc (I := I) (M := M) g s).toSection Asec x (D x)
  have hpeelU := tensor0SCovariantDerivative_succ_consEval_peel_natural
    (I := I) (M := M) g (s + 1) V hV_at U (D x) (Fin.cons (W x) m)
  have hpeelW := tensor0SCovariantDerivative_succ_consEval_peel_natural
    (I := I) (M := M) g s VU hVU_at W (D x) m
  rw [hHom, Tensor0SSpace.eval_sub]
  change
    Tensor0SSpace.eval
        (Tensor0SNabla.tensor0SCovariantDerivative I M (s + 2)
          (LeviCivita (I := I) g) V x (D x))
        (Fin.cons (U x) (Fin.cons (W x) m)) -
      Tensor0SSpace.eval
        ((show Tensor0SSpace s I x →L[ℝ] Tensor0SSpace (s + 2) I x from
          (slotFreeOpCc (I := I) (M := M) g s).toSection x)
          (Tensor0SNabla.tensor0SCovariantDerivative I M s
            (LeviCivita (I := I) g) (fun y => Asec y) x (D x)))
        (Fin.cons (U x) (Fin.cons (W x) m)) = _
  rw [hpeelU, hpeelW, hVW, hDU, hDW, hDA]
  rw [nablaTensor0SCurv_def]
  rw [hDUfun, hDWfun, hDAfun]
  simp only [Tensor0SSpace.eval_sub]
  ring

omit [SigmaCompactSpace M] in
theorem slotFree_cov_eval
    (g : SmoothRiemannianMetric I M) (s : ℕ) (x : M)
    (d : TangentSpace I x) (A : Tensor0SSpace s I x)
    (u w : TangentSpace I x) (m : Fin s → TangentSpace I x) :
    Tensor0SSpace.eval
        ((show Tensor0SSpace s I x →L[ℝ] Tensor0SSpace (s + 2) I x from
          TensorRSNabla.tensorRSCovariantDerivative I M s (s + 2)
            (LeviCivita (I := I) g)
            (slotFreeOpCc (I := I) (M := M) g s).toSection x d) A)
        (Fin.cons u (Fin.cons w m)) =
      - ∑ k : Fin s, Tensor0SSpace.eval A
          (Function.update m k
            (nablaRiemannOp (I := I) g x d u w (m k))) := by
  classical
  obtain ⟨Asec, hAsec⟩ := ContMDiffSection.exists_eq_at (I := I)
    (F := Tensor0SModel s ℝ E) (V := fun y : M => Tensor0SSpace s I y)
    (n := (⊤ : ℕ∞)) x A
  obtain ⟨D, hD⟩ := ContMDiffSection.exists_eq_at (I := I)
    (F := E) (V := fun y : M => TangentSpace I y)
    (n := (⊤ : ℕ∞)) x d
  obtain ⟨U, hU⟩ := ContMDiffSection.exists_eq_at (I := I)
    (F := E) (V := fun y : M => TangentSpace I y)
    (n := (⊤ : ℕ∞)) x u
  obtain ⟨W, hW⟩ := ContMDiffSection.exists_eq_at (I := I)
    (F := E) (V := fun y : M => TangentSpace I y)
    (n := (⊤ : ℕ∞)) x w
  rw [← hAsec, ← hD, ← hU, ← hW]
  rw [slotFree_cov_sec (I := I) (M := M) g s D U W Asec x m]
  rw [nablaTensor0SCurv_apply_eval (I := I) g s D U W
    (fun y => Asec y) Asec.contMDiff x m]
  apply congrArg Neg.neg
  refine Finset.sum_congr rfl (fun k _ => ?_)
  refine congrArg (fun z : TangentSpace I x =>
    Tensor0SSpace.eval (Asec x) (Function.update m k z)) ?_
  let Q : ContMDiffSection I E ∞ (fun y : M => TangentSpace I y) :=
    ⟨smoothExtensionTangent (I := I) x (m k),
      smoothExtensionTangent_contMDiff (I := I) x (m k)⟩
  rw [nablaBaseSlotCurv_eq_nablaCurvSec]
  have h := (nablaRiemannOp_sec (I := I) g D U W Q x).symm
  change nablaCurvSec (LeviCivita (I := I) g) D U W Q x =
    nablaRiemannOp (I := I) g x (D x) (U x) (W x) (Q x) at h
  simpa only [Q, ContMDiffSection.coeFn_mk,
    smoothExtensionTangent_eq] using h

end Connection
end Integral
end DifferentialGeometry

end
