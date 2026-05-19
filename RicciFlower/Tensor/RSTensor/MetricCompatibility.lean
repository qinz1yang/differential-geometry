import RicciFlower.Connection.MetricCompatibility
import RicciFlower.Tensor.RSTensor.Metric
import RicciFlower.Tensor.RSTensor.CoordinateBasis
import RicciFlower.Tensor.RSTensor.NablaOnTensors
import RicciFlower.VectorBundle.Section
import RicciFlower.VectorBundle.PartialMfderiv

set_option autoImplicit false
set_option linter.style.longLine false

/-!
# Metric compatibility as `nabla g = 0`

This file turns the pointwise definition of a metric-compatible connection into
the covariant-tensor statement that the induced covariant derivative of the
metric `(0,2)` tensor vanishes.
-/

namespace Tensor0SBundle

noncomputable section

set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [Module.Finite Real E] [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- The smooth metric as a `(0,2)` tensor field at the regularity level used by
the tensor covariant-derivative API. -/
def metricTensorField
    [IsManifold I 1 M] [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    (g : RicciFlower.SmoothRiemannianMetric I M) :
    Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 2 := by
  let gInf : Bundle.ContMDiffRiemannianMetric I (∞ : WithTop ℕ∞) E
      (TangentSpace I : M -> Type _) :=
    { inner := Bundle.ContMDiffRiemannianMetric.inner g
      symm := g.symm
      pos := g.pos
      isVonNBounded := g.isVonNBounded
      contMDiff := g.contMDiff.of_le (by simp) }
  exact RiemannianMetric.to02Tensor (I := I) (M := M)
    (n := (∞ : WithTop ℕ∞)) gInf

@[simp]
theorem metricTensorField_apply
    [IsManifold I 1 M] [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    (g : RicciFlower.SmoothRiemannianMetric I M) (x : M)
    (v : Fin 2 -> TangentSpace I x) :
    metricTensorField (I := I) g x v = g.inner x (v 0) (v 1) := by
  simp [metricTensorField]

/-- Evaluation form of `∇ g = 0` on smooth tangent-field slots.

This is exactly the metric-compatibility identity rewritten through
`nabla0SFun_eval_smooth_slots`. -/
theorem nabla_metric_eval
    [IsManifold I 1 M] [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (g : RicciFlower.SmoothRiemannianMetric I M)
    (hmc : RicciFlower.Connection.IsMetricCompatible (I := I) cov g)
    (X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (V : Fin 2 -> ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M -> Type _))
    (x : M) :
    (nabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 cov X
      (metricTensorField (I := I) g) x)
        (fun a : Fin 2 => V a x) = 0 := by
  classical
  let A : Real :=
    g.inner x ((cov (fun y : M => V 0 y) x) (X x)) (V 1 x)
  let B : Real :=
    g.inner x (V 0 x) ((cov (fun y : M => V 1 y) x) (X x))
  have hX : MDiffAt (T% (fun y : M => X y)) x :=
    X.contMDiff.contMDiffAt.mdifferentiableAt (by simp)
  have hV0 : MDiffAt (T% (fun y : M => V 0 y)) x :=
    (V 0).contMDiff.contMDiffAt.mdifferentiableAt (by simp)
  have hV1 : MDiffAt (T% (fun y : M => V 1 y)) x :=
    (V 1).contMDiff.contMDiffAt.mdifferentiableAt (by simp)
  have hmc_apply :=
    RicciFlower.Connection.metric_compatible_apply (I := I) hmc
      (fun y : M => X y) (fun y : M => V 0 y) (fun y : M => V 1 y)
      hX hV0 hV1
  have hderiv :
      extDerivFun (I := I)
          (fun p : M =>
            metricTensorField (I := I) g p (fun a : Fin 2 => V a p))
          x (X x) = A + B := by
    have hderiv' :
        extDerivFun (I := I)
            (fun p : M => g.inner p (V 0 p) (V 1 p)) x (X x) = A + B := by
      rw [RicciFlower.extDerivFun_real_eq_mfderiv]
      simpa [A, B] using hmc_apply
    simpa using hderiv'
  have hsum :
      (∑ a : Fin 2,
        metricTensorField (I := I) g x
          (Function.update (fun b : Fin 2 => V b x) a
            ((cov (fun p : M => V a p) x) (X x)))) = A + B := by
    rw [Fin.sum_univ_two]
    simp [A, B]
  have heval :=
    nabla0SFun_eval_smooth_slots (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) cov X V
      (metricTensorField (I := I) g) x
  rw [heval, hsum, hderiv]
  ring

/-- Tensor form of `∇ g = 0` for a metric-compatible connection. -/
theorem nabla_metric_zero
    [T2Space M] [IsManifold I 1 M] [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (g : RicciFlower.SmoothRiemannianMetric I M)
    (hmc : RicciFlower.Connection.IsMetricCompatible (I := I) cov g)
    (X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (x : M) :
    nabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 cov X
      (metricTensorField (I := I) g) x = 0 := by
  classical
  let basis : Module.Basis (Fin (Module.finrank Real (TangentSpace I x))) Real
      (TangentSpace I x) :=
    Module.finBasis Real (TangentSpace I x)
  apply ext0S_basis (I := I) basis
  intro slots
  let V : Fin 2 -> ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M -> Type _) :=
    fun a =>
      (ContMDiffSection.exists_eq_at
        (I := I) (F := E) (V := TangentSpace I) (n := (⊤ : ℕ∞))
        x (basis (slots a))).choose
  have hV : ∀ a : Fin 2, V a x = basis (slots a) := by
    intro a
    exact
      (ContMDiffSection.exists_eq_at
        (I := I) (F := E) (V := TangentSpace I) (n := (⊤ : ℕ∞))
        x (basis (slots a))).choose_spec
  have hzero := nabla_metric_eval (I := I) cov g hmc X V x
  simp only [component0S_apply]
  convert hzero using 2
  ext a
  exact (hV a).symm

/-- The covariant derivative of the zero covariant tensor field is zero. -/
theorem nabla_zero
    [T2Space M] [IsManifold I 1 M] [IsManifold I 2 M]
    [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    (s : ℕ)
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (x : M) :
    nabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) s cov X
      (0 : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        (n := (∞ : WithTop ℕ∞)) s) x = 0 := by
  classical
  let basis : Module.Basis (Fin (Module.finrank Real (TangentSpace I x))) Real
      (TangentSpace I x) :=
    Module.finBasis Real (TangentSpace I x)
  apply ext0S_basis (I := I) basis
  intro slots
  let V : Fin s -> ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M -> Type _) :=
    fun a =>
      (ContMDiffSection.exists_eq_at
        (I := I) (F := E) (V := TangentSpace I) (n := (⊤ : ℕ∞))
        x (basis (slots a))).choose
  have hV : ∀ a : Fin s, V a x = basis (slots a) := by
    intro a
    exact
      (ContMDiffSection.exists_eq_at
        (I := I) (F := E) (V := TangentSpace I) (n := (⊤ : ℕ∞))
        x (basis (slots a))).choose_spec
  have hzero :
      (nabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) s cov X
        (0 : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
          (n := (∞ : WithTop ℕ∞)) s) x)
          (fun a : Fin s => V a x) = 0 := by
    have heval :=
      nabla0SFun_eval_smooth_slots (𝕜 := Real) (E := E) (H := H)
        (I := I) (M := M) cov X V
        (0 : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
          (n := (∞ : WithTop ℕ∞)) s) x
    simpa using heval
  simp only [component0S_apply]
  convert hzero using 2
  ext a
  exact (hV a).symm

/-- The zero `(0,s+1)` tensor field realizes `∇0 = 0`. -/
theorem zero_realizes_nabla
    [T2Space M] [IsManifold I 1 M] [IsManifold I 2 M]
    [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    (s : ℕ)
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _)) :
    TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      s cov
      (0 : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        (n := (∞ : WithTop ℕ∞)) s)
      (0 : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        (n := (∞ : WithTop ℕ∞)) (s + 1)) := by
  intro X x slots
  rw [nabla_zero (I := I) s cov X x]
  simp

/-- The zero `(0,3)` tensor field realizes the first covariant derivative of
the metric tensor for a metric-compatible connection. -/
theorem zero_realizes_metric
    [T2Space M] [IsManifold I 1 M] [IsManifold I 2 M]
    [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (g : RicciFlower.SmoothRiemannianMetric I M)
    (hmc : RicciFlower.Connection.IsMetricCompatible (I := I) cov g) :
    TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      2 cov (metricTensorField (I := I) g)
      (0 : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        (n := (∞ : WithTop ℕ∞)) 3) := by
  intro X x slots
  rw [nabla_metric_zero (I := I) cov g hmc X x]
  simp

end

end Tensor0SBundle
