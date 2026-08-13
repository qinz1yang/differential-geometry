import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.PointedConvergence
import DifferentialGeometry.Tensor.RSTensor.NablaOnTensors.TotalNabla0SLinear
import DifferentialGeometry.Geometry.Metric.SmoothVectorFieldExtGlobal
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.RicciConnDiffPalatini
open DifferentialGeometry.Tensor.RicciIdentity
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace DifferentialGeometry
namespace HCGCompactness

open scoped Manifold ContDiff Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [T2Space M] [IsManifold I ∞ M] [SigmaCompactSpace M]
noncomputable def covDerivOfField
    (gRef : SmoothRiemannianMetric I M)
    (A0 :
      Tensor0SBundle.Tensor0SField (𝕜 := Real) (E := E) (H := H)
        (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) 2) :
    (a : Nat) ->
      Tensor0SBundle.Tensor0SField (𝕜 := Real) (E := E) (H := H)
        (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) (a + 2) :=
  Nat.rec
    (motive := fun a : Nat =>
      Tensor0SBundle.Tensor0SField (𝕜 := Real) (E := E) (H := H)
        (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) (a + 2))
    A0
    (fun a A =>
      by
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
          metricCovDerivStep (I := I) gRef a A)

omit [SigmaCompactSpace M] in
theorem covDerivOfField_succ
    (gRef : SmoothRiemannianMetric I M)
    (A0 :
      Tensor0SBundle.Tensor0SField (𝕜 := Real) (E := E) (H := H)
        (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) 2)
    (a : Nat) :
    covDerivOfField (I := I) gRef A0 (a + 1)
      = metricCovDerivStep (I := I) gRef a (covDerivOfField (I := I) gRef A0 a) :=
  rfl

omit [SigmaCompactSpace M] in
theorem metricCovDeriv_succ
    (h gRef : SmoothRiemannianMetric I M) (a : Nat) :
    metricCovDeriv (I := I) h gRef (a + 1)
      = metricCovDerivStep (I := I) gRef a (metricCovDeriv (I := I) h gRef a) :=
  rfl

omit [SigmaCompactSpace M] in
theorem metricCovDeriv_eq_covDerivOfField
    (h gRef : SmoothRiemannianMetric I M) (a : Nat) :
    metricCovDeriv (I := I) h gRef a
      = covDerivOfField (I := I) gRef
          (Tensor0SBundle.metricTensorField (I := I) h) a :=
  rfl

omit [SigmaCompactSpace M] in
theorem metricCovDerivStep_apply
    (gRef : SmoothRiemannianMetric I M) (a : Nat)
    (A :
      Tensor0SBundle.Tensor0SField (𝕜 := Real) (E := E) (H := H)
        (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) (a + 2))
    (x : M) :
    metricCovDerivStep (I := I) gRef a A x
      = Tensor0SBundle.totalNabla0SFun (𝕜 := Real) (E := E) (H := H)
          (I := I) (M := M) (a + 2)
          (leviCivitaConnectionOfMetric (I := I) gRef) A x :=
  rfl

omit [SigmaCompactSpace M] in
theorem metricCovDeriv_succ_eval_smooth_slots_gen
    (h gRef : SmoothRiemannianMetric I M) (a : Nat)
    (X : ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M -> Type _))
    (V : Fin (a + 2) -> ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M -> Type _))
    (x : M) :
    metricCovDeriv (I := I) h gRef (a + 1) x
        (Fin.cons (X x) (fun q : Fin (a + 2) => V q x)) =
      extDerivFun (I := I)
          (fun y : M => metricCovDeriv (I := I) h gRef a y
            (fun q : Fin (a + 2) => V q y)) x (X x) -
        ∑ p : Fin (a + 2),
          metricCovDeriv (I := I) h gRef a x
            (Function.update (fun q : Fin (a + 2) => V q x) p
              (((leviCivitaConnectionOfMetric (I := I) gRef)
                  (fun y : M => V p y) x) (X x))) := by
  rw [metricCovDeriv_succ, metricCovDerivStep_apply,
    Tensor0SBundle.totalNabla0SFun_apply_section]
  exact Tensor0SBundle.nabla0SFun_eval_smooth_slots
    (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
    (leviCivitaConnectionOfMetric (I := I) gRef) X V
    (metricCovDeriv (I := I) h gRef a) x

omit [SigmaCompactSpace M] in
theorem metricCovDerivStep_smul
    (gRef : SmoothRiemannianMetric I M) (c : Real) (a : Nat)
    (A :
      Tensor0SBundle.Tensor0SField (𝕜 := Real) (E := E) (H := H)
        (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) (a + 2)) :
    metricCovDerivStep (I := I) gRef a (c • A)
      = c • metricCovDerivStep (I := I) gRef a A := by
  refine DFunLike.ext _ _ (fun x => ?_)
  rw [metricCovDerivStep_apply, ContMDiffSection.coe_smul, Pi.smul_apply,
    metricCovDerivStep_apply, Tensor0SBundle.totalNabla0SFun_smul]

omit [SigmaCompactSpace M] in
theorem covDerivOfField_smul
    (gRef : SmoothRiemannianMetric I M) (c : Real)
    (A0 :
      Tensor0SBundle.Tensor0SField (𝕜 := Real) (E := E) (H := H)
        (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) 2)
    (a : Nat) :
    covDerivOfField (I := I) gRef (c • A0) a
      = c • covDerivOfField (I := I) gRef A0 a := by
  induction a with
  | zero => rfl
  | succ n ih =>
      rw [covDerivOfField_succ, covDerivOfField_succ, ih, metricCovDerivStep_smul]

omit [SigmaCompactSpace M] in
theorem metricCovDerivStep_add
    (gRef : SmoothRiemannianMetric I M) (a : Nat)
    (A B :
      Tensor0SBundle.Tensor0SField (𝕜 := Real) (E := E) (H := H)
        (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) (a + 2)) :
    metricCovDerivStep (I := I) gRef a (A + B)
      = metricCovDerivStep (I := I) gRef a A + metricCovDerivStep (I := I) gRef a B := by
  refine DFunLike.ext _ _ (fun x => ?_)
  rw [metricCovDerivStep_apply, ContMDiffSection.coe_add, Pi.add_apply,
    metricCovDerivStep_apply, metricCovDerivStep_apply,
    Tensor0SBundle.totalNabla0SFun_add]

omit [SigmaCompactSpace M] in
theorem covDerivOfField_add
    (gRef : SmoothRiemannianMetric I M)
    (A0 B0 :
      Tensor0SBundle.Tensor0SField (𝕜 := Real) (E := E) (H := H)
        (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) 2)
    (a : Nat) :
    covDerivOfField (I := I) gRef (A0 + B0) a
      = covDerivOfField (I := I) gRef A0 a + covDerivOfField (I := I) gRef B0 a := by
  induction a with
  | zero => rfl
  | succ n ih =>
      rw [covDerivOfField_succ, covDerivOfField_succ, covDerivOfField_succ, ih,
        metricCovDerivStep_add]

omit [SigmaCompactSpace M] in
theorem covDerivOfField_sub
    (gRef : SmoothRiemannianMetric I M)
    (A0 B0 :
      Tensor0SBundle.Tensor0SField (𝕜 := Real) (E := E) (H := H)
        (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) 2)
    (a : Nat) :
    covDerivOfField (I := I) gRef (A0 - B0) a
      = covDerivOfField (I := I) gRef A0 a - covDerivOfField (I := I) gRef B0 a := by
  rw [sub_eq_add_neg, covDerivOfField_add, ← neg_one_smul Real B0,
    covDerivOfField_smul, neg_one_smul, ← sub_eq_add_neg]

noncomputable def covStep
    (gRef : SmoothRiemannianMetric I M) (s : Nat)
    (A : Tensor0SBundle.Tensor0SField (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) s) :
    Tensor0SBundle.Tensor0SField (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) (s + 1) := by
  haveI : IsManifold I 1 M :=
    IsManifold.of_le (I := I) (M := M) (n := ∞)
      (by decide : (1 : WithTop ℕ∞) ≤ ∞)
  haveI : IsManifold I 2 M :=
    IsManifold.of_le (I := I) (M := M) (n := ∞)
      (by decide : (2 : WithTop ℕ∞) ≤ ∞)
  haveI : IsManifold I ((∞ : WithTop ℕ∞) + 1) M := by
    change IsManifold I ∞ M
    infer_instance
  let cov :=
    DifferentialGeometry.Geometry.Connection.leviCivitaConnectionOfMetric (I := I) gRef
  let hcov :
      CovariantDerivative.ContMDiffCovariantDerivativeLocally
        (I := I) (E := E) (M := M) cov (∞ : WithTop ℕ∞) := by
    simpa [cov] using
      leviCivitaConnectionOfMetric_contMDiffCovariantDerivativeLocally
        (I := I) (M := M) gRef
  let hreg :=
    Tensor0SBundle.totalNabla0S_reg (E := E) (H := H)
      (I := I) (M := M) s cov hcov A
  exact
    Tensor0SBundle.totalNabla0S (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) s cov A hreg

omit [SigmaCompactSpace M] in
@[simp] theorem covStep_apply
    (gRef : SmoothRiemannianMetric I M) (s : Nat)
    (A : Tensor0SBundle.Tensor0SField (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) s) (x : M) :
    covStep (I := I) gRef s A x
      = Tensor0SBundle.totalNabla0SFun (𝕜 := Real) (E := E) (H := H)
          (I := I) (M := M) s
          (DifferentialGeometry.Geometry.Connection.leviCivitaConnectionOfMetric (I := I) gRef)
          A x :=
  rfl

omit [SigmaCompactSpace M] in
theorem covStep_add
    (gRef : SmoothRiemannianMetric I M) (s : Nat)
    (A B : Tensor0SBundle.Tensor0SField (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) s) :
    covStep (I := I) gRef s (A + B)
      = covStep (I := I) gRef s A + covStep (I := I) gRef s B := by
  refine DFunLike.ext _ _ (fun x => ?_)
  rw [covStep_apply, ContMDiffSection.coe_add, Pi.add_apply,
    covStep_apply, covStep_apply, Tensor0SBundle.totalNabla0SFun_add]

omit [SigmaCompactSpace M] in
theorem covStep_smul
    (gRef : SmoothRiemannianMetric I M) (c : Real) (s : Nat)
    (A : Tensor0SBundle.Tensor0SField (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) s) :
    covStep (I := I) gRef s (c • A)
      = c • covStep (I := I) gRef s A := by
  refine DFunLike.ext _ _ (fun x => ?_)
  rw [covStep_apply, ContMDiffSection.coe_smul, Pi.smul_apply,
    covStep_apply, Tensor0SBundle.totalNabla0SFun_smul]

omit [SigmaCompactSpace M] in
theorem covStep_sub
    (gRef : SmoothRiemannianMetric I M) (s : Nat)
    (A B : Tensor0SBundle.Tensor0SField (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) s) :
    covStep (I := I) gRef s (A - B)
      = covStep (I := I) gRef s A - covStep (I := I) gRef s B := by
  rw [sub_eq_add_neg, covStep_add, ← neg_one_smul Real B,
    covStep_smul, neg_one_smul, ← sub_eq_add_neg]

omit [SigmaCompactSpace M] in
theorem covStep_eval_smooth_slots
    (g₂ : SmoothRiemannianMetric I M) (r : Nat)
    (A : Tensor0SBundle.Tensor0SField (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) r)
    (X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (V : Fin r -> ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M -> Type _))
    (x : M) :
    covStep (I := I) g₂ r A x (Fin.cons (X x) (fun q : Fin r => V q x))
      = extDerivFun (I := I)
          (fun y : M => A y (fun q : Fin r => V q y)) x (X x) -
        ∑ q : Fin r,
          A x (Function.update (fun b : Fin r => V b x) q
            (((leviCivitaConnectionOfMetric (I := I) g₂)
                (fun y : M => V q y) x) (X x))) := by
  haveI : IsManifold I 1 M :=
    IsManifold.of_le (I := I) (M := M) (n := ∞) (by decide : (1 : WithTop ℕ∞) ≤ ∞)
  haveI : IsManifold I 2 M :=
    IsManifold.of_le (I := I) (M := M) (n := ∞) (by decide : (2 : WithTop ℕ∞) ≤ ∞)
  haveI : IsManifold I ((∞ : WithTop ℕ∞) + 1) M := by
    change IsManifold I ∞ M
    infer_instance
  haveI : IsManifold I (1 + 1) M :=
    IsManifold.of_le (I := I) (M := M) (n := ∞)
      (by decide : ((1 : WithTop ℕ∞) + 1) ≤ ∞)
  haveI : ContMDiffVectorBundle 1 E (TangentSpace I : M -> Type _) I :=
    TangentBundle.contMDiffVectorBundle (I := I) (M := M) (n := 1)
  rw [covStep_apply, Tensor0SBundle.totalNabla0SFun_apply_section]
  exact Tensor0SBundle.nabla0SFun_eval_smooth_slots
    (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
    (leviCivitaConnectionOfMetric (I := I) g₂) X V A x

noncomputable def iterCov
    (gRef : SmoothRiemannianMetric I M) (r : Nat)
    (A0 : Tensor0SBundle.Tensor0SField (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) r) :
    (a : Nat) ->
      Tensor0SBundle.Tensor0SField (𝕜 := Real) (E := E) (H := H)
        (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) (r + a) :=
  Nat.rec A0 (fun a A => covStep (I := I) gRef (r + a) A)

omit [SigmaCompactSpace M] in
theorem iterCov_succ
    (gRef : SmoothRiemannianMetric I M) (r : Nat)
    (A0 : Tensor0SBundle.Tensor0SField (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) r)
    (a : Nat) :
    iterCov (I := I) gRef r A0 (a + 1)
      = covStep (I := I) gRef (r + a) (iterCov (I := I) gRef r A0 a) :=
  rfl

omit [SigmaCompactSpace M] in
theorem iterCov_add
    (gRef : SmoothRiemannianMetric I M) (r : Nat)
    (A0 B0 : Tensor0SBundle.Tensor0SField (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) r)
    (a : Nat) :
    iterCov (I := I) gRef r (A0 + B0) a
      = iterCov (I := I) gRef r A0 a + iterCov (I := I) gRef r B0 a := by
  induction a with
  | zero => rfl
  | succ n ih =>
      rw [iterCov_succ, iterCov_succ, iterCov_succ, ih, covStep_add]

noncomputable def diffStep
    (g₁ g₂ : SmoothRiemannianMetric I M) (s : Nat)
    (S : Tensor0SBundle.Tensor0SField (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) s) :
    Tensor0SBundle.Tensor0SField (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) (s + 1) :=
  covStep (I := I) g₁ s S - covStep (I := I) g₂ s S

omit [SigmaCompactSpace M] in
theorem diffStep_apply
    (g₁ g₂ : SmoothRiemannianMetric I M) (s : Nat)
    (S : Tensor0SBundle.Tensor0SField (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) s)
    (X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (V : Fin s -> ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M -> Type _))
    (x : M) :
    diffStep (I := I) g₁ g₂ s S x
        (Fin.cons (X x) (fun q : Fin s => V q x)) =
      -∑ a : Fin s,
        (S x)
          (Function.update (fun b : Fin s => V b x) a
            (((CovariantDerivative.difference
                (leviCivitaConnectionOfMetric (I := I) g₁)
                (leviCivitaConnectionOfMetric (I := I) g₂) x) (V a x)) (X x))) := by
  haveI : IsManifold I 1 M :=
    IsManifold.of_le (I := I) (M := M) (n := ∞) (by decide : (1 : WithTop ℕ∞) ≤ ∞)
  haveI : IsManifold I 2 M :=
    IsManifold.of_le (I := I) (M := M) (n := ∞) (by decide : (2 : WithTop ℕ∞) ≤ ∞)
  haveI : IsManifold I ((∞ : WithTop ℕ∞) + 1) M := by
    change IsManifold I ∞ M
    infer_instance
  haveI : IsManifold I (1 + 1) M :=
    IsManifold.of_le (I := I) (M := M) (n := ∞)
      (by decide : ((1 : WithTop ℕ∞) + 1) ≤ ∞)
  haveI : ContMDiffVectorBundle 1 E (TangentSpace I : M -> Type _) I :=
    TangentBundle.contMDiffVectorBundle (I := I) (M := M) (n := 1)
  have hsec : diffStep (I := I) g₁ g₂ s S x =
      covStep (I := I) g₁ s S x - covStep (I := I) g₂ s S x := by
    change (covStep (I := I) g₁ s S - covStep (I := I) g₂ s S) x = _
    rw [ContMDiffSection.coe_sub, Pi.sub_apply]
  rw [hsec]
  change (covStep (I := I) g₁ s S x) (Fin.cons (X x) (fun q : Fin s => V q x))
      - (covStep (I := I) g₂ s S x) (Fin.cons (X x) (fun q : Fin s => V q x)) = _
  rw [covStep_apply, covStep_apply,
    Tensor0SBundle.totalNabla0SFun_apply_section,
    Tensor0SBundle.totalNabla0SFun_apply_section]
  exact Tensor0SBundle.nabla0SFun_sub_cov (I := I)
    (leviCivitaConnectionOfMetric (I := I) g₁)
    (leviCivitaConnectionOfMetric (I := I) g₂) X V S x

omit [SigmaCompactSpace M] in
theorem diffStep_eval
    (g₁ g₂ : SmoothRiemannianMetric I M) (s : Nat)
    (S : Tensor0SBundle.Tensor0SField (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) s)
    (x : M) (v : TangentSpace I x) (slots : Fin s -> TangentSpace I x) :
    diffStep (I := I) g₁ g₂ s S x (Fin.cons v slots) =
      -∑ a : Fin s,
        (S x)
          (Function.update slots a
            (((CovariantDerivative.difference
                (leviCivitaConnectionOfMetric (I := I) g₁)
                (leviCivitaConnectionOfMetric (I := I) g₂) x) (slots a)) v)) := by
  classical
  obtain ⟨Xf, hXsm, hXv⟩ :=
    Geometry.Riemannian.exists_contMDiff_vectorField_eq (I := I) x v
  choose Vf hVsm hVv using fun a : Fin s =>
    Geometry.Riemannian.exists_contMDiff_vectorField_eq (I := I) x (slots a)
  have key := diffStep_apply (I := I) g₁ g₂ s S
    (ContMDiffSection.mk Xf hXsm)
    (fun a : Fin s => ContMDiffSection.mk (Vf a) (hVsm a)) x
  simp only [ContMDiffSection.coeFn_mk, hXv, hVv] at key
  exact key

noncomputable def telescAccum
    (g₁ g₂ : SmoothRiemannianMetric I M) (r : Nat)
    (T : Tensor0SBundle.Tensor0SField (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) r) :
    (N : Nat) ->
      Tensor0SBundle.Tensor0SField (𝕜 := Real) (E := E) (H := H)
        (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) (r + N)
  | 0 => 0
  | (N + 1) =>
      covStep (I := I) g₁ (r + N) (telescAccum g₁ g₂ r T N)
        + diffStep (I := I) g₁ g₂ (r + N) (iterCov (I := I) g₂ r T N)

omit [SigmaCompactSpace M] in
theorem iterCov_telescoping
    (g₁ g₂ : SmoothRiemannianMetric I M) (r : Nat)
    (T : Tensor0SBundle.Tensor0SField (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) r)
    (N : Nat) :
    iterCov (I := I) g₁ r T N
      = iterCov (I := I) g₂ r T N + telescAccum (I := I) g₁ g₂ r T N := by
  induction N with
  | zero => exact (add_zero T).symm
  | succ n ih =>
      rw [iterCov_succ, ih, covStep_add, iterCov_succ (gRef := g₂)]
      simp only [telescAccum, diffStep]
      abel

omit [SigmaCompactSpace M] in
theorem diffStep_leibniz
    (g₁ g₂ : SmoothRiemannianMetric I M) (s : Nat)
    (S : Tensor0SBundle.Tensor0SField (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) s) :
    covStep (I := I) g₂ (s + 1) (diffStep (I := I) g₁ g₂ s S)
      = diffStep (I := I) g₁ g₂ (s + 1) (covStep (I := I) g₂ s S)
        + (covStep (I := I) g₂ (s + 1) (covStep (I := I) g₁ s S)
            - covStep (I := I) g₁ (s + 1) (covStep (I := I) g₂ s S)) := by
  simp only [diffStep]
  rw [covStep_sub]
  abel

omit [SigmaCompactSpace M] in
theorem iterCov_succ_diffStep
    (g₁ g₂ : SmoothRiemannianMetric I M) (r : Nat)
    (T : Tensor0SBundle.Tensor0SField (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) r)
    (N : Nat) :
    iterCov (I := I) g₁ r T (N + 1)
      = covStep (I := I) g₂ (r + N) (iterCov (I := I) g₁ r T N)
        + diffStep (I := I) g₁ g₂ (r + N) (iterCov (I := I) g₁ r T N) := by
  rw [iterCov_succ]
  simp only [diffStep]
  abel

omit [SigmaCompactSpace M] in
theorem diffStep_leibniz_eval
    (g₁ g₂ : SmoothRiemannianMetric I M) (s : Nat)
    (S : Tensor0SBundle.Tensor0SField (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) s)
    (W V : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (Vslots : Fin s -> ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M -> Type _))
    (x : M) :
    covStep (I := I) g₂ (s + 1) (diffStep (I := I) g₁ g₂ s S) x
        (Fin.cons (W x) (Fin.cons (V x) (fun a : Fin s => Vslots a x)))
      = (-∑ a : Fin s,
          (S x) (Function.update (fun b : Fin s => Vslots b x) a
            (covDerivConnDiff (I := I) g₂ g₁
              (fun y : M => W y) (fun y : M => V y) (fun y : M => Vslots a y) x)))
        - ∑ a : Fin s,
            covStep (I := I) g₂ s S x
              (Fin.cons (W x) (Function.update (fun b : Fin s => Vslots b x) a
                ((CovariantDerivative.difference
                    (leviCivitaConnectionOfMetric (I := I) g₁)
                    (leviCivitaConnectionOfMetric (I := I) g₂) x
                    (Vslots a x)) (V x)))) := by
  classical
  haveI : IsManifold I 1 M :=
    IsManifold.of_le (I := I) (M := M) (n := ∞) (by decide : (1 : WithTop ℕ∞) ≤ ∞)
  haveI : IsManifold I 2 M :=
    IsManifold.of_le (I := I) (M := M) (n := ∞) (by decide : (2 : WithTop ℕ∞) ≤ ∞)
  haveI : IsManifold I ((∞ : WithTop ℕ∞) + 1) M := by
    change IsManifold I ∞ M
    infer_instance
  haveI : IsManifold I (1 + 1) M :=
    IsManifold.of_le (I := I) (M := M) (n := ∞)
      (by decide : ((1 : WithTop ℕ∞) + 1) ≤ ∞)
  haveI : ContMDiffVectorBundle 1 E (TangentSpace I : M -> Type _) I :=
    TangentBundle.contMDiffVectorBundle (I := I) (M := M) (n := 1)
  haveI hcov₁ : CovariantDerivative.ContMDiffCovariantDerivative
      (leviCivitaConnectionOfMetric (I := I) g₁)
        (∞ : WithTop ℕ∞) := leviCivitaConnectionOfMetric_contMDiffCovariantDerivative (I := I) g₁
  haveI hcov₂ : CovariantDerivative.ContMDiffCovariantDerivative
      (leviCivitaConnectionOfMetric (I := I) g₂)
        (∞ : WithTop ℕ∞) := leviCivitaConnectionOfMetric_contMDiffCovariantDerivative (I := I) g₂
  set VV : Fin (s + 1) → ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M -> Type _) := Fin.cons V Vslots with hVVdef
  have hVVpt : ∀ y : M, (fun q : Fin (s + 1) => VV q y)
      = Fin.cons (V y) (fun a : Fin s => Vslots a y) := by
    intro y
    funext q
    refine Fin.cases ?_ (fun i => ?_) q <;> simp [hVVdef]
  rw [show Fin.cons (V x) (fun a : Fin s => Vslots a x)
        = (fun q : Fin (s + 1) => VV q x) from (hVVpt x).symm,
    covStep_eval_smooth_slots (I := I) g₂ (s + 1) (diffStep (I := I) g₁ g₂ s S) W VV x]
  have hInt : (fun y : M => (diffStep (I := I) g₁ g₂ s S) y (fun q : Fin (s + 1) => VV q y))
      = (fun y : M => -∑ a : Fin s, (S y) (Function.update (fun b : Fin s => Vslots b y) a
          ((CovariantDerivative.difference
              (leviCivitaConnectionOfMetric (I := I) g₁)
              (leviCivitaConnectionOfMetric (I := I) g₂) y
              (Vslots a y)) (V y)))) := by
    funext y
    rw [hVVpt y]
    exact diffStep_apply (I := I) g₁ g₂ s S V Vslots y
  rw [hInt]
  set cov₁ := leviCivitaConnectionOfMetric (I := I) g₁ with hcdef₁
  set cov₂ := leviCivitaConnectionOfMetric (I := I) g₂ with hcdef₂
  set Dsec : Fin s → ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _) :=
    fun a => ContMDiffSection.mk (diffSec cov₂ cov₁ (fun y : M => V y) (fun y : M => Vslots a y))
      (diffSec_contMDiff cov₂ cov₁ V.contMDiff (by simpa using (Vslots a).contMDiff)) with hDdef
  set τ : Fin s → Fin s → ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _) :=
    fun a => Function.update Vslots a (Dsec a) with hτdef
  have hDval : ∀ (a : Fin s) (y : M),
      (Dsec a) y = (CovariantDerivative.difference cov₁ cov₂ y (Vslots a y)) (V y) := by
    intro a y
    rw [hDdef]
    rfl
  have hτeval : ∀ (a : Fin s) (y : M),
      (fun b : Fin s => (τ a b) y)
        = Function.update (fun b : Fin s => Vslots b y) a
            ((CovariantDerivative.difference cov₁ cov₂ y (Vslots a y)) (V y)) := by
    intro a y
    funext b
    simp only [hτdef]
    rcases eq_or_ne b a with hb | hb
    · subst hb
      rw [Function.update_self, Function.update_self]
      exact hDval b y
    · rw [Function.update_of_ne hb, Function.update_of_ne hb]
  have hdiff : ∀ a : Fin s,
      MDifferentiableAt I 𝓘(Real, Real) (fun y : M => (S y) (fun b : Fin s => (τ a b) y)) x := by
    intro a
    have hSAt : ContMDiffAt I 𝓘(Real, Real) (∞ : WithTop ℕ∞)
        (fun y : M => (S y) (fun b : Fin s => (τ a b) y)) x := by
      have hS := (S.contMDiff x).of_le (le_refl (∞ : WithTop ℕ∞))
      have hEval := TensorMultilinear.contMDiffAt_section_apply_gen (I := I) (M := M) (n := s)
        (x₀ := x)
        (T := fun y : M => S y) hS (v := fun b : Fin s => fun y : M => (τ a b) y)
        (hv := fun b => ((τ a b).contMDiff.contMDiffAt))
      simpa [Tensor0SBundle.Tensor0SSpace.toModel,
        Tensor0SBundle.tensor0SSpace_continuousLinearEquiv_apply] using hEval
    exact hSAt.mdifferentiableAt (by simp)
  simp only [← hτeval]
  have hDF : extDerivFun (I := I)
        (fun y : M => -∑ a : Fin s, (S y) (fun b : Fin s => (τ a b) y)) x (W x)
      = -∑ a : Fin s,
          extDerivFun (I := I) (fun y : M => (S y) (fun b : Fin s => (τ a b) y)) x (W x) := by
    have h1 : (fun y : M => -∑ a : Fin s, (S y) (fun b : Fin s => (τ a b) y))
        = (fun y : M => -(Finset.univ.sum
            (fun a : Fin s => fun y' : M => (S y') (fun b : Fin s => (τ a b) y'))) y) := by
      funext y; simp only [Finset.sum_apply]
    rw [h1, extDerivFun_neg_at (I := I) (W x)
          (mdiffAt_finset_sum (I := I) Finset.univ _ (fun a _ => hdiff a)),
        extDerivFun_finset_sum_at (I := I) Finset.univ
          (fun a : Fin s => fun y : M => (S y) (fun b : Fin s => (τ a b) y)) (W x)
          (fun a _ => hdiff a)]
  rw [hDF]
  have hEDF : ∀ a : Fin s,
      extDerivFun (I := I) (fun y : M => (S y) (fun b : Fin s => (τ a b) y)) x (W x)
      = (covStep (I := I) g₂ s S) x (Fin.cons (W x) (fun b : Fin s => (τ a b) x))
        + ∑ b : Fin s, (S x) (Function.update (fun b' : Fin s => (τ a b') x) b
            ((cov₂ (fun y : M => (τ a b) y) x) (W x))) := by
    intro a
    have hcs : (covStep (I := I) g₂ s S) x (Fin.cons (W x) (fun b : Fin s => (τ a b) x))
        = Tensor0SBundle.nabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
            s cov₂ W S x (fun b : Fin s => (τ a b) x) := by
      rw [covStep_apply, Tensor0SBundle.totalNabla0SFun_apply_section]
    rw [hcs, Tensor0SBundle.nabla0SFun_eval_smooth_slots (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) cov₂ W (τ a) S x]
    ring
  simp only [hEDF]
  rw [Finset.sum_add_distrib]
  have hFib :
      (∑ a : Fin s, ∑ b : Fin s, (S x) (Function.update (fun b' : Fin s => (τ a b') x) b
          ((cov₂ (fun y : M => (τ a b) y) x) (W x))))
        + (∑ q : Fin (s + 1), ((diffStep (I := I) g₁ g₂ s S) x)
            (Function.update (fun b : Fin (s + 1) => (VV b) x) q
              ((cov₂ (fun y : M => (VV q) y) x) (W x))))
        = ∑ a : Fin s, (S x) (Function.update (fun b : Fin s => (Vslots b) x) a
            (covDerivConnDiff (I := I) g₂ g₁ (fun y : M => W y) (fun y : M => V y)
              (fun y : M => (Vslots a) y) x)) := by
    have hFact1 : ∀ a : Fin s,
        (cov₂ (fun y : M => (τ a a) y) x) (W x)
        = covDerivConnDiff (I := I) g₂ g₁ (fun y => W y) (fun y => V y) (fun y => (Vslots a) y) x
          + (CovariantDerivative.difference cov₁ cov₂ x (Vslots a x)) ((cov₂
            (fun y : M => V y) x) (W x))
          + (CovariantDerivative.difference cov₁ cov₂ x
              ((cov₂ (fun y : M => (Vslots a) y) x) (W x))) (V x) := by
      intro a
      have hτaa : (fun y : M => (τ a a) y) = (fun y : M => (Dsec a) y) := by
        simp only [hτdef, Function.update_self]
      rw [hτaa, covDerivConnDiff_eq,
        show LeviCivita (I := I) g₂ = cov₂ from
          (LeviCivita_eq_leviCivitaConnectionOfMetric g₂).trans hcdef₂.symm,
        show LeviCivita (I := I) g₁ = cov₁ from
          (LeviCivita_eq_leviCivitaConnectionOfMetric g₁).trans hcdef₁.symm]
      simp only [covDerivDiff, covApply, hDdef, ContMDiffSection.coeFn_mk]
      abel
    have hD :
        (∑ a : Fin s, ∑ b : Fin s, (S x) (Function.update (fun b' : Fin s => (τ a b') x) b
            ((cov₂ (fun y : M => (τ a b) y) x) (W x))))
        = (∑ a : Fin s, (S x) (Function.update (fun b : Fin s => (Vslots b) x) a
              (covDerivConnDiff (I := I) g₂ g₁ (fun y => W y) (fun y => V y) (fun y =>
                (Vslots a) y) x)))
          + (∑ a : Fin s, (S x) (Function.update (fun b : Fin s => (Vslots b) x) a
              ((CovariantDerivative.difference cov₁ cov₂ x ((Vslots a) x)) ((cov₂
                (fun y => V y) x) (W x)))))
          + (∑ a : Fin s, (S x) (Function.update (fun b : Fin s => (Vslots b) x) a
              ((CovariantDerivative.difference cov₁ cov₂ x ((cov₂ (fun y => (Vslots a) y) x)
                (W x))) (V x))))
          + (∑ a : Fin s, ∑ b ∈ Finset.univ.erase a, (S x)
              (Function.update (Function.update (fun c : Fin s => (Vslots c) x) a
                  ((CovariantDerivative.difference cov₁ cov₂ x ((Vslots a) x)) (V x))) b
                ((cov₂ (fun y => (Vslots b) y) x) (W x)))) := by
      rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun a _ => ?_)
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ a), hτeval a x, Function.update_idem,
        hFact1 a, ContinuousMultilinearMap.map_update_add,
        ContinuousMultilinearMap.map_update_add]
      have herase : ∀ b ∈ Finset.univ.erase a,
          (S x) (Function.update (Function.update (fun c : Fin s => (Vslots c) x) a
              ((CovariantDerivative.difference cov₁ cov₂ x ((Vslots a) x)) (V x))) b
            ((cov₂ (fun y : M => (τ a b) y) x) (W x)))
          = (S x) (Function.update (Function.update (fun c : Fin s => (Vslots c) x) a
              ((CovariantDerivative.difference cov₁ cov₂ x ((Vslots a) x)) (V x))) b
            ((cov₂ (fun y : M => (Vslots b) y) x) (W x))) := by
        intro b hb
        have hba : b ≠ a := Finset.ne_of_mem_erase hb
        have : (fun y : M => (τ a b) y) = (fun y : M => (Vslots b) y) := by
          simp only [hτdef, Function.update_of_ne hba]
        rw [this]
      rw [Finset.sum_congr rfl herase]
    have hβ :
        (∑ q : Fin (s + 1), ((diffStep (I := I) g₁ g₂ s S) x)
            (Function.update (fun b : Fin (s + 1) => (VV b) x) q ((cov₂ (fun y : M =>
              (VV q) y) x) (W x))))
        = -(∑ a : Fin s, (S x) (Function.update (fun b : Fin s => (Vslots b) x) a
              ((CovariantDerivative.difference cov₁ cov₂ x ((Vslots a) x)) ((cov₂
                (fun y => V y) x) (W x)))))
          - (∑ a : Fin s, (S x) (Function.update (fun b : Fin s => (Vslots b) x) a
              ((CovariantDerivative.difference cov₁ cov₂ x ((cov₂ (fun y => (Vslots a) y) x)
                (W x))) (V x))))
          - (∑ j : Fin s, ∑ a ∈ Finset.univ.erase j, (S x)
              (Function.update (Function.update (fun c : Fin s => (Vslots c) x) j
                  ((cov₂ (fun y => (Vslots j) y) x) (W x))) a
                ((CovariantDerivative.difference cov₁ cov₂ x ((Vslots a) x)) (V x)))) := by
      rw [Fin.sum_univ_succ]
      simp only [hVVpt x, Fin.update_cons_zero, ← Fin.cons_update]
      simp only [hVVdef, Fin.cons_zero, Fin.cons_succ]
      simp only [diffStep_eval, ← hcdef₁, ← hcdef₂]
      have hj : ∀ j : Fin s,
          (∑ a : Fin s, (S x) (Function.update (Function.update (fun c : Fin s => (Vslots c) x) j
                ((cov₂ (fun y : M => (Vslots j) y) x) (W x))) a
              ((CovariantDerivative.difference cov₁ cov₂ x
                  ((Function.update (fun c : Fin s => (Vslots c) x) j
                    ((cov₂ (fun y : M => (Vslots j) y) x) (W x))) a)) (V x))))
          = (S x) (Function.update (fun b : Fin s => (Vslots b) x) j
                ((CovariantDerivative.difference cov₁ cov₂ x ((cov₂ (fun y => (Vslots j) y) x)
                  (W x))) (V x)))
            + ∑ a ∈ Finset.univ.erase j, (S x)
                (Function.update (Function.update (fun c : Fin s => (Vslots c) x) j
                    ((cov₂ (fun y => (Vslots j) y) x) (W x))) a
                  ((CovariantDerivative.difference cov₁ cov₂ x ((Vslots a) x)) (V x))) := by
        intro j
        rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j), Function.update_self,
          Function.update_idem]
        refine congrArg _ (Finset.sum_congr rfl (fun a ha => ?_))
        rw [Function.update_of_ne (Finset.ne_of_mem_erase ha)]
      simp only [hj, neg_add, Finset.sum_add_distrib, Finset.sum_neg_distrib]
      abel
    rw [hD, hβ]
    have hYY' :
        (∑ a : Fin s, ∑ b ∈ Finset.univ.erase a, (S x)
            (Function.update (Function.update (fun c : Fin s => (Vslots c) x) a
                ((CovariantDerivative.difference cov₁ cov₂ x ((Vslots a) x)) (V x))) b
              ((cov₂ (fun y => (Vslots b) y) x) (W x))))
        = (∑ j : Fin s, ∑ a ∈ Finset.univ.erase j, (S x)
            (Function.update (Function.update (fun c : Fin s => (Vslots c) x) j
                ((cov₂ (fun y => (Vslots j) y) x) (W x))) a
              ((CovariantDerivative.difference cov₁ cov₂ x ((Vslots a) x)) (V x)))) := by
      rw [Finset.sum_comm' (s := Finset.univ) (t := fun a : Fin s => Finset.univ.erase a)
        (t' := Finset.univ) (s' := fun b : Fin s => Finset.univ.erase b)
        (h := fun a b => by
          simp only [Finset.mem_univ, Finset.mem_erase, true_and, and_true]
          exact ⟨Ne.symm, Ne.symm⟩)]
      refine Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun a ha => ?_))
      rw [Function.update_comm (Finset.ne_of_mem_erase ha)]
    rw [hYY']
    abel
  linarith [hFib]

end HCGCompactness

end DifferentialGeometry
