import RicciFlower.Tensor.RSTensor.NablaOnTensors.RawDefs
import RicciFlower.Tensor.RSTensor.CoordinateBasis
import RicciFlower.Tensor.RSTensor.NablaOnTensors.Connection.Endomorphism
import RicciFlower.Tensor.RSTensor.NablaOnTensors.Regularity.Tensor0S
import RicciFlower.VectorBundle.PartialMfderiv
import Mathlib.GroupTheory.Perm.Fin

/-!
# Higher-order covariant derivative interfaces

This module adds a small total-derivative interface on top of the existing
directional `nabla0SFun` / `nablaRSFun` API.  The analytic regularity of the
resulting fields is kept explicit through realization predicates.
-/

namespace TensorLieDeriv

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

open Bundle Set IsManifold ContinuousLinearMap Tensor0SBundle
open scoped Manifold Topology Bundle ContDiff

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable [FiniteDimensional 𝕜 E]

section Model

/-- Model-space total covariant derivative of a covariant tensor.

The output is a tensor with one leading derivative slot.  Evaluating the first
slot at `X` recovers the usual directional model formula. -/
noncomputable def totalCovDeriv_tensor0SModelAt (s : ℕ)
    (Dα : E →L[𝕜] Tensor0SModel s 𝕜 E) (Γ : E →L[𝕜] E →L[𝕜] E)
    (α : Tensor0SModel s 𝕜 E) : Tensor0SModel (s + 1) 𝕜 E :=
  ContinuousLinearMap.uncurryLeft
    (𝕜 := 𝕜) (n := s) (Ei := fun _ : Fin (s + 1) => E) (G := 𝕜)
    (LinearMap.toContinuousLinearMap
      { toFun := fun X =>
          covariantDeriv_tensor0SModelAt (𝕜 := 𝕜) (E := E) s
            (Dα X) (Γ X) α
        map_add' := by
          intro X Y
          simp only [map_add]
          rw [covariantDeriv_tensor0SModelAt_apply]
          rw [covariantDeriv_tensor0SModelAt_apply]
          rw [covariantDeriv_tensor0SModelAt_apply]
          rw [lieDeriv_correction_add_right]
          abel
        map_smul' := by
          intro c X
          simp only [map_smul]
          rw [covariantDeriv_tensor0SModelAt_apply]
          rw [covariantDeriv_tensor0SModelAt_apply]
          rw [lieDeriv_correction_smul_right]
          ext slots
          simp [sub_eq_add_neg] })

@[simp]
theorem totalCovDeriv_tensor0SModelAt_apply_cons (s : ℕ)
    (Dα : E →L[𝕜] Tensor0SModel s 𝕜 E) (Γ : E →L[𝕜] E →L[𝕜] E)
    (α : Tensor0SModel s 𝕜 E) (X : E) (slots : Fin s → E) :
    totalCovDeriv_tensor0SModelAt (𝕜 := 𝕜) (E := E) s Dα Γ α
        (Fin.cons X slots) =
      covariantDeriv_tensor0SModelAt (𝕜 := 𝕜) (E := E) s (Dα X) (Γ X) α slots := by
  unfold totalCovDeriv_tensor0SModelAt
  rw [ContinuousLinearMap.uncurryLeft_apply]
  rfl

end Model

end

end TensorLieDeriv

namespace Tensor0SBundle

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

open Bundle Set IsManifold ContinuousLinearMap TensorLieDeriv
open scoped Manifold Topology Bundle ContDiff

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable [FiniteDimensional 𝕜 E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I 1 M] [IsManifold I 2 M]
variable [IsManifold I (∞ : WithTop ℕ∞) M]
variable [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]

/-- Canonical pointwise total covariant derivative of a covariant tensor field.

The output has one leading derivative slot.  This is the tensor-level analogue
of `nabla0SFun`; evaluating the first slot should recover the old directional
API.  The bundled version below keeps smoothness of this new field explicit. -/
noncomputable def totalNabla0SFun (s : ℕ)
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (α : Tensor0SField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s)
    (x₀ : M) : Tensor0SSpace (s + 1) I x₀ :=
  (trivializationAt (Tensor0SModel (s + 1) 𝕜 E)
    (fun x : M => Tensor0SSpace (s + 1) I x) x₀).symm x₀
    (totalCovDeriv_tensor0SModelAt (𝕜 := 𝕜) (E := E) s
      (fderivWithin 𝕜
        (tensor0SModelInChart (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
          s x₀ (fun x => α x))
        (Set.range I) (extChartAt I x₀ x₀))
      (connectionEndomorphismInChartL (𝕜 := 𝕜) (I := I) cov x₀
        (extChartAt I x₀ x₀))
      (tensor0SModelAt (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
        s x₀ x₀ (α x₀)))

/-- Structural congruence for the canonical total covariant derivative. -/
theorem totalNabla0SFun_congr (s : ℕ)
    {cov cov' : CovariantDerivative I E (TangentSpace I : M → Type _)}
    {α β : Tensor0SField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s}
    (hcov : cov = cov') (hα : α = β) (x : M) :
    totalNabla0SFun (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
        s cov α x =
      totalNabla0SFun (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
        s cov' β x := by
  cases hcov
  cases hα
  rfl

/-- Regularity predicate for the canonical total covariant derivative.

This is explicit for the same reason as `Nabla0SRegular`: the construction is
pointwise canonical, while smoothness of the resulting field is an analytic
input or separate theorem. -/
abbrev TotalNabla0SRegular (s : ℕ)
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (α : Tensor0SField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s) : Prop :=
  letI := tensor0SBundle_topology (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
    (s + 1)
  ContMDiff I (I.prod 𝓘(𝕜, Tensor0SModel (s + 1) 𝕜 E)) (∞ : WithTop ℕ∞)
    (fun x : M =>
      (⟨x, totalNabla0SFun (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
        s cov α x⟩ :
        TotalSpace (Tensor0SModel (s + 1) 𝕜 E)
          (fun x : M => Tensor0SSpace (s + 1) I x)))

/-- Bundled total covariant derivative of a covariant tensor field. -/
noncomputable def totalNabla0S (s : ℕ)
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (α : Tensor0SField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s)
    (hreg : TotalNabla0SRegular (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      s cov α) :
    Tensor0SField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) (s + 1) :=
  letI := tensor0SBundle_topology (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
    (s + 1)
  ⟨totalNabla0SFun (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
    s cov α, hreg⟩

@[simp] theorem totalNabla0S_apply (s : ℕ)
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (α : Tensor0SField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s)
    (hreg : TotalNabla0SRegular (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      s cov α)
    (x : M) :
    totalNabla0S (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
        s cov α hreg x =
      totalNabla0SFun (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
        s cov α x := rfl

/-- Model-slot evaluation of the canonical total covariant derivative at the
center of the fixed chart. -/
theorem totalNabla0SFun_apply_tangentConstInChart (s : ℕ)
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (α : Tensor0SField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s)
    (x₀ : M) (X : E) (slots : Fin s → E) :
    totalNabla0SFun (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
        s cov α x₀
        (Fin.cons (tangentConstInChart (𝕜 := 𝕜) (I := I) x₀ X x₀)
          (fun a : Fin s => tangentConstInChart (𝕜 := 𝕜) (I := I) x₀ (slots a) x₀))
      =
    covariantDeriv_tensor0SModelAt (𝕜 := 𝕜) (E := E) s
      (fderivWithin 𝕜
        (tensor0SModelInChart (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
          s x₀ (fun x => α x))
        (Set.range I) (extChartAt I x₀ x₀) X)
      (connectionEndomorphismInChartL (𝕜 := 𝕜) (I := I) cov x₀
        (extChartAt I x₀ x₀) X)
      (tensor0SModelAt (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
        s x₀ x₀ (α x₀))
      slots := by
  simp only [tangentConstInChart_apply]
  have hslots :
      Fin.cons
          ((trivializationAt E (TangentSpace I : M → Type _) x₀).symmL 𝕜 x₀ X)
          (fun a : Fin s =>
            (trivializationAt E (TangentSpace I : M → Type _) x₀).symmL 𝕜 x₀
              (slots a))
        =
      (fun a : Fin (s + 1) =>
        (trivializationAt E (TangentSpace I : M → Type _) x₀).symmL 𝕜 x₀
          ((Fin.cons X slots : Fin (s + 1) → E) a)) := by
    funext a
    cases a using Fin.cases <;> simp
  rw [hslots]
  rw [← tensor0SModelAt_apply (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
    (s + 1) x₀ x₀
    (totalNabla0SFun (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      s cov α x₀) (Fin.cons X slots)]
  unfold totalNabla0SFun
  rw [tensor0SModelAt_trivializationAt_symm]
  rw [totalCovDeriv_tensor0SModelAt_apply_cons]

/-- Certification frontier for the canonical total covariant derivative.

Contracting the new leading derivative slot against a smooth vector field
recovers the existing directional derivative.  This is the tensor-level
agreement theorem needed before using `totalNabla0SFun` as the canonical
`∇α`. -/
theorem totalNabla0SFun_apply_section (s : ℕ)
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _))
    (α : Tensor0SField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s)
    (x : M) (slots : Fin s → TangentSpace I x) :
    totalNabla0SFun (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
        s cov α x (Fin.cons (X x) slots) =
      nabla0SFun (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
        s cov X α x slots := by
  classical
  let e := trivializationAt E (TangentSpace I : M → Type _) x
  let y₀ : E := extChartAt I x x
  let Xmodel : E := e.continuousLinearMapAt 𝕜 x (X x)
  let slotsModel : Fin s → E := fun a => e.continuousLinearMapAt 𝕜 x (slots a)
  have hXinput :
      tangentConstInChart (𝕜 := 𝕜) (I := I) x Xmodel x = X x := by
    change
      tangentConstInChart (𝕜 := 𝕜) (I := I) x
          ((trivializationAt E (TangentSpace I : M → Type _) x).continuousLinearMapAt
            𝕜 x (X x)) x =
        X x
    exact tangentConstInChart_self_continuousLinearMapAt
      (𝕜 := 𝕜) (I := I) x (X x)
  have hslotsInput :
      (fun a : Fin s =>
        tangentConstInChart (𝕜 := 𝕜) (I := I) x (slotsModel a) x) = slots := by
    funext a
    change
      tangentConstInChart (𝕜 := 𝕜) (I := I) x
          ((trivializationAt E (TangentSpace I : M → Type _) x).continuousLinearMapAt
            𝕜 x (slots a)) x =
        slots a
    exact tangentConstInChart_self_continuousLinearMapAt
      (𝕜 := 𝕜) (I := I) x (slots a)
  have hinput :
      Fin.cons
          (tangentConstInChart (𝕜 := 𝕜) (I := I) x Xmodel x)
          (fun a : Fin s =>
            tangentConstInChart (𝕜 := 𝕜) (I := I) x (slotsModel a) x)
        =
      (Fin.cons (X x) slots : Fin (s + 1) → TangentSpace I x) := by
    funext a
    cases a using Fin.cases with
    | zero => exact hXinput
    | succ a => exact congrFun hslotsInput a
  have hmpull :
      VectorField.mpullbackWithin 𝓘(𝕜, E) I (extChartAt I x).symm
          (fun y : M => X y) (Set.range I) y₀ =
        Xmodel := by
    simp only [y₀, Xmodel, e, VectorField.mpullbackWithin_apply]
    rw [extChartAt_to_inv]
    rw [TangentBundle.continuousLinearMapAt_trivializationAt
      (I := I) (x₀ := x) (x := x) (mem_chart_source H x)]
    rw [mfderiv_extChartAt_self]
    exact mfderivWithin_extChartAt_symm_inverse_apply (I := I) (x := x) (X x)
  have htotal := totalNabla0SFun_apply_tangentConstInChart
    (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
    s cov α x Xmodel slotsModel
  have hself := nabla0SFun_apply_selfChart_slots
    (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
    s cov X α x slotsModel
  have hfixed := fixedChartNabla0SModel_apply_slots
    (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
    (n := (∞ : WithTop ℕ∞)) s cov X α x y₀ slotsModel
  calc
    totalNabla0SFun (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
        s cov α x (Fin.cons (X x) slots)
        =
      totalNabla0SFun (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
        s cov α x
        (Fin.cons
          (tangentConstInChart (𝕜 := 𝕜) (I := I) x Xmodel x)
          (fun a : Fin s =>
            tangentConstInChart (𝕜 := 𝕜) (I := I) x (slotsModel a) x)) := by
          rw [hinput]
    _ =
      covariantDeriv_tensor0SModelAt (𝕜 := 𝕜) (E := E) s
        (fderivWithin 𝕜
          (tensor0SModelInChart (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
            s x (fun x => α x))
          (Set.range I) (extChartAt I x x) Xmodel)
        (connectionEndomorphismInChartL (𝕜 := 𝕜) (I := I) cov x
          (extChartAt I x x) Xmodel)
        (tensor0SModelAt (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
          s x x (α x))
        slotsModel := htotal
    _ =
      fixedChartNabla0SModel (𝕜 := 𝕜) (E := E) (H := H)
        (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) s cov X α x y₀ slotsModel := by
          rw [hfixed]
          rw [covariantDeriv_tensor0SModelAt_apply_slots]
          rw [hmpull]
          have hΓ (v : E) :
              connectionEndomorphismInChartL (𝕜 := 𝕜) (I := I) cov x
                  (extChartAt I x x) Xmodel v =
                connectionEndomorphismInChart (𝕜 := 𝕜) (I := I) cov
                  (fun x => X x) x (extChartAt I x x) v := by
            change
              connectionEndomorphismInChartL (𝕜 := 𝕜) (I := I) cov x
                  (extChartAt I x x)
                  ((trivializationAt E (TangentSpace I : M → Type _)
                    x).continuousLinearMapAt 𝕜 x (X x)) v =
                connectionEndomorphismInChart (𝕜 := 𝕜) (I := I) cov
                  (fun x => X x) x (extChartAt I x x) v
            exact connectionEndomorphismInChartL_apply_center_modelVector
              (𝕜 := 𝕜) (I := I) cov (fun x => X x) x v
          simp_rw [hΓ]
          rw [tensor0SModelInChart_center_eq_tensor0SModelAt
            (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
            s x (fun y => α y)]
    _ =
      (nabla0SFun (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
        s cov X α x)
        (fun a : Fin s =>
          tangentConstInChart (𝕜 := 𝕜) (I := I) x (slotsModel a) x) := by
          exact hself.symm
    _ =
      nabla0SFun (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
        s cov X α x slots := by
          rw [hslotsInput]

/-- A supplied `(0,s+1)` field realizes the total covariant derivative of a
`(0,s)` field when contraction against any smooth vector field gives the
existing directional derivative. -/
def TotalNabla0SRealizes (s : ℕ)
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (α : Tensor0SField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s)
    (nablaAlpha : Tensor0SField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) (s + 1)) : Prop :=
  ∀ (X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _))
    (x : M) (slots : Fin s → TangentSpace I x),
      nablaAlpha x (Fin.cons (X x) slots) =
        nabla0SFun (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
          s cov X α x slots

/-- A supplied `(r,s+1)` field realizes the total covariant derivative of a
mixed `(r,s)` field. -/
def TotalNablaRSRealizes (r s : ℕ)
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (T : TensorRSField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) r s)
    (nablaT : TensorRSField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) r (s + 1)) : Prop :=
  ∀ (X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _))
    (x : M) (β : Tensor0SSpace r I x) (slots : Fin s → TangentSpace I x),
      nablaT x β (Fin.cons (X x) slots) =
        nablaRSFun (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
          r s cov X T x β slots

theorem TotalNabla0SRealizes.apply {s : ℕ}
    {cov : CovariantDerivative I E (TangentSpace I : M → Type _)}
    {α : Tensor0SField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s}
    {nablaAlpha : Tensor0SField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) (s + 1)}
    (h : TotalNabla0SRealizes (𝕜 := 𝕜) (E := E) (H := H)
      (I := I) (M := M) s cov α nablaAlpha)
    (X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _))
    (x : M) (slots : Fin s → TangentSpace I x) :
    nablaAlpha x (Fin.cons (X x) slots) =
    nabla0SFun (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
        s cov X α x slots :=
  h X x slots

/-- Congruence for total covariant-derivative realizations at a fixed
covariant valence. -/
theorem TotalNabla0SRealizes.congr {s : ℕ}
    {cov : CovariantDerivative I E (TangentSpace I : M → Type _)}
    {α β : Tensor0SField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s}
    {nablaAlpha nablaBeta : Tensor0SField (𝕜 := 𝕜) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) (s + 1)}
    (hα : α = β) (hnabla : nablaAlpha = nablaBeta)
    (h : TotalNabla0SRealizes (𝕜 := 𝕜) (E := E) (H := H)
      (I := I) (M := M) s cov α nablaAlpha) :
    TotalNabla0SRealizes (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      s cov β nablaBeta := by
  cases hα
  cases hnabla
  exact h

/-- Canonical valence transport for covariant tensor fields.  This keeps
dependent casts explicit and reusable in higher-derivative jet constructions. -/
def tensor0SFieldCast {s t : ℕ}
    (hst : s = t)
    (α : Tensor0SField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s) :
    Tensor0SField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) t := by
  subst t
  exact α

@[simp] theorem tensor0SFieldCast_rfl {s : ℕ}
    (α : Tensor0SField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s) :
    tensor0SFieldCast (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      rfl α = α := rfl

theorem tensor0SFieldCast_proof_irrel {s t : ℕ}
    (hst hst' : s = t)
    (α : Tensor0SField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s) :
    tensor0SFieldCast (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      hst α =
    tensor0SFieldCast (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      hst' α := by
  cases hst
  cases hst'
  rfl

/-- Transport a total covariant-derivative realization across an equality of
covariant valences.  This is the basic cast-normalization lemma needed by
higher-derivative unpackers. -/
theorem TotalNabla0SRealizes.cast {s t : ℕ}
    (hst : s = t)
    {cov : CovariantDerivative I E (TangentSpace I : M → Type _)}
    {α : Tensor0SField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s}
    {nablaAlpha : Tensor0SField (𝕜 := 𝕜) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) (s + 1)}
    (h : TotalNabla0SRealizes (𝕜 := 𝕜) (E := E) (H := H)
      (I := I) (M := M) s cov α nablaAlpha) :
    TotalNabla0SRealizes (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      t cov
      (by
        subst t
        exact α :
        Tensor0SField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
          (n := (∞ : WithTop ℕ∞)) t)
      (by
        subst t
        exact nablaAlpha :
        Tensor0SField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
          (n := (∞ : WithTop ℕ∞)) (t + 1)) := by
  subst t
  simpa using h

/-- Transport a total covariant-derivative realization using the canonical
`tensor0SFieldCast` transport on both fields. -/
theorem TotalNabla0SRealizes.castField {s t : ℕ}
    (hst : s = t)
    {cov : CovariantDerivative I E (TangentSpace I : M → Type _)}
    {α : Tensor0SField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s}
    {nablaAlpha : Tensor0SField (𝕜 := 𝕜) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) (s + 1)}
    (h : TotalNabla0SRealizes (𝕜 := 𝕜) (E := E) (H := H)
      (I := I) (M := M) s cov α nablaAlpha) :
    TotalNabla0SRealizes (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      t cov
      (tensor0SFieldCast (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
        hst α)
      (tensor0SFieldCast (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
        (congrArg (fun n : ℕ => n + 1) hst) nablaAlpha) := by
  subst t
  simpa using h

/-- The canonical bundled total derivative realizes the total-nabla predicate,
modulo the single contraction-agreement certification theorem above. -/
theorem totalNabla0S_realizes (s : ℕ)
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (α : Tensor0SField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s)
    (hreg : TotalNabla0SRegular (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      s cov α) :
    TotalNabla0SRealizes (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      s cov α
      (totalNabla0S (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
        s cov α hreg) := by
  intro X x slots
  rw [totalNabla0S_apply]
  exact totalNabla0SFun_apply_section
    (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) s cov X α x slots

/-- Canonical first and second spatial covariant derivatives of a covariant
tensor field, bundled with their realization witnesses.

The constructor using the canonical `totalNabla0S` fields lives in
`Regularity/TotalNabla0S.lean`, where `totalNabla0S_reg` is available without
creating an import cycle. -/
structure CanonicalSpatialDerivs0S {s : ℕ}
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (A : Tensor0SField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s) where
  nablaA : Tensor0SField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
    (n := (∞ : WithTop ℕ∞)) (s + 1)
  nabla2A : Tensor0SField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
    (n := (∞ : WithTop ℕ∞)) (s + 2)
  first : TotalNabla0SRealizes (𝕜 := 𝕜) (E := E) (H := H) (I := I)
    (M := M) s cov A nablaA
  second : TotalNabla0SRealizes (𝕜 := 𝕜) (E := E) (H := H) (I := I)
    (M := M) (s + 1) cov nablaA nabla2A

/-- Definition 14.5 for any supplied total covariant derivative realization:
evaluating the total derivative on smooth moving slots agrees with the usual
tensorial derivation rule. -/
theorem TotalNabla0SRealizes.eval_smooth_slots {s : ℕ}
    {cov : CovariantDerivative I E (TangentSpace I : M → Type _)}
    {α : Tensor0SField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s}
    {nablaAlpha : Tensor0SField (𝕜 := 𝕜) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) (s + 1)}
    (h : TotalNabla0SRealizes (𝕜 := 𝕜) (E := E) (H := H)
      (I := I) (M := M) s cov α nablaAlpha)
    (X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _))
    (V : Fin s → ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M → Type _))
    (x₀ : M) :
    nablaAlpha x₀ (Fin.cons (X x₀) (fun a : Fin s => V a x₀)) =
      extDerivFun (I := I) (fun p : M => α p (fun a : Fin s => V a p))
        x₀ (X x₀) -
        ∑ a : Fin s,
          α x₀
            (Function.update (fun b : Fin s => V b x₀) a
              ((cov (fun p : M => V a p) x₀) (X x₀))) := by
  calc
    nablaAlpha x₀ (Fin.cons (X x₀) (fun a : Fin s => V a x₀))
        = nabla0SFun (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
            s cov X α x₀ (fun a : Fin s => V a x₀) := by
          exact h.apply X x₀ (fun a : Fin s => V a x₀)
    _ = extDerivFun (I := I) (fun p : M => α p (fun a : Fin s => V a p))
          x₀ (X x₀) -
          ∑ a : Fin s,
            α x₀
              (Function.update (fun b : Fin s => V b x₀) a
                ((cov (fun p : M => V a p) x₀) (X x₀))) := by
          exact nabla0SFun_eval_smooth_slots
            (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
            cov X V α x₀

/-- Definition 14.5 for any supplied total covariant derivative realization:
evaluating the total derivative on `C¹` moving slots agrees with the usual
tensorial derivation rule. -/
theorem TotalNabla0SRealizes.eval_C1_slots {s : ℕ}
    {cov : CovariantDerivative I E (TangentSpace I : M → Type _)}
    {α : Tensor0SField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s}
    {nablaAlpha : Tensor0SField (𝕜 := 𝕜) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) (s + 1)}
    (h : TotalNabla0SRealizes (𝕜 := 𝕜) (E := E) (H := H)
      (I := I) (M := M) s cov α nablaAlpha)
    (X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _))
    (V : Fin s → (x : M) → TangentSpace I x)
    (x₀ : M)
    (hV_at : ∀ a : Fin s,
      ContMDiffAt I (I.prod 𝓘(𝕜, E)) (1 : WithTop ℕ∞)
        (fun y : M => (⟨y, V a y⟩ : TotalSpace E (TangentSpace I : M → Type _))) x₀) :
    nablaAlpha x₀ (Fin.cons (X x₀) (fun a : Fin s => V a x₀)) =
      extDerivFun (I := I) (fun p : M => α p (fun a : Fin s => V a p))
        x₀ (X x₀) -
        ∑ a : Fin s,
          α x₀
            (Function.update (fun b : Fin s => V b x₀) a
              ((cov (V a) x₀) (X x₀))) := by
  calc
    nablaAlpha x₀ (Fin.cons (X x₀) (fun a : Fin s => V a x₀))
        = nabla0SFun (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
            s cov X α x₀ (fun a : Fin s => V a x₀) := by
          exact h.apply X x₀ (fun a : Fin s => V a x₀)
    _ = extDerivFun (I := I) (fun p : M => α p (fun a : Fin s => V a p))
          x₀ (X x₀) -
          ∑ a : Fin s,
            α x₀
              (Function.update (fun b : Fin s => V b x₀) a
                ((cov (V a) x₀) (X x₀))) := by
          exact nabla0SFun_eval_C1_slots
            (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
            cov X V α x₀ hV_at

theorem TotalNablaRSRealizes.apply {r s : ℕ}
    {cov : CovariantDerivative I E (TangentSpace I : M → Type _)}
    {T : TensorRSField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) r s}
    {nablaT : TensorRSField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) r (s + 1)}
    (h : TotalNablaRSRealizes (𝕜 := 𝕜) (E := E) (H := H)
      (I := I) (M := M) r s cov T nablaT)
    (X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _))
    (x : M) (β : Tensor0SSpace r I x) (slots : Fin s → TangentSpace I x) :
    nablaT x β (Fin.cons (X x) slots) =
      nablaRSFun (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
        r s cov X T x β slots :=
  h X x β slots

/-- Definition 14.5 for any supplied mixed total covariant derivative
realization: evaluating the total derivative on moving input and output slots
agrees with the usual mixed-tensor derivation rule.

This is the direct realization-level wrapper around
`nablaRSFun_eval_moving_raw`; it keeps the local regularity assumptions on the
moving slots explicit. -/
theorem TotalNablaRSRealizes.eval_moving_slots {r s : ℕ}
    {cov : CovariantDerivative I E (TangentSpace I : M -> Type _)}
    {T : TensorRSField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) r s}
    {nablaT : TensorRSField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) r (s + 1)}
    (h : TotalNablaRSRealizes (𝕜 := 𝕜) (E := E) (H := H)
      (I := I) (M := M) r s cov T nablaT)
    (X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (β : (x : M) -> Tensor0SSpace (𝕜 := 𝕜) (E := E) (H := H) (I := I)
      (M := M) r x)
    (V : Fin s -> (x : M) -> TangentSpace I x) (x₀ : M)
    (hpair : MDifferentiableAt I 𝓘(𝕜, 𝕜)
      (fun p : M => (T p (β p)) (fun a : Fin s => V a p)) x₀)
    (hβmodel : DifferentiableWithinAt 𝕜
      (tensor0SModelInChart (𝕜 := 𝕜) (E := E) (H := H) (I := I)
        (M := M) r x₀ β)
      (Set.range I) (extChartAt I x₀ x₀))
    (hV : ∀ a : Fin s, MDiffAt (T% (V a)) x₀)
    (hVmodel : ∀ a : Fin s,
      DifferentiableWithinAt 𝕜
        (tangentFieldModelInChart (𝕜 := 𝕜) (I := I) x₀ (V a))
        (Set.range I) (extChartAt I x₀ x₀))
    (hcoord : ∀ a : Fin s, ∀ i : Fin (Module.finrank 𝕜 E),
      MDifferentiableAt I 𝓘(𝕜, 𝕜)
        (fun p : M =>
          (Module.finBasis 𝕜 E).coord i
            (tangentFieldModelInChart (𝕜 := 𝕜) (I := I) x₀ (V a)
              (extChartAt I x₀ p))) x₀) :
    nablaT x₀ (β x₀) (Fin.cons (X x₀) (fun a : Fin s => V a x₀)) =
      extDerivFun (I := I) (fun p : M => (T p (β p)) (fun a : Fin s => V a p))
        x₀ (X x₀) -
        (T x₀ (localCovariantDerivTensor0SAt
          (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) r cov X β x₀))
          (fun a : Fin s => V a x₀) -
        ∑ a : Fin s,
          (T x₀ (β x₀))
            (Function.update (fun b : Fin s => V b x₀) a
              ((cov (V a) x₀) (X x₀))) := by
  calc
    nablaT x₀ (β x₀) (Fin.cons (X x₀) (fun a : Fin s => V a x₀))
        = nablaRSFun (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
            r s cov X T x₀ (β x₀) (fun a : Fin s => V a x₀) := by
          exact h.apply X x₀ (β x₀) (fun a : Fin s => V a x₀)
    _ = extDerivFun (I := I)
          (fun p : M => (T p (β p)) (fun a : Fin s => V a p)) x₀ (X x₀) -
        (T x₀ (localCovariantDerivTensor0SAt
          (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) r cov X β x₀))
          (fun a : Fin s => V a x₀) -
        ∑ a : Fin s,
          (T x₀ (β x₀))
            (Function.update (fun b : Fin s => V b x₀) a
              ((cov (V a) x₀) (X x₀))) := by
          exact nablaRSFun_eval_moving_raw
            (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
            cov X T β V x₀ hpair hβmodel hV hVmodel hcoord

/-- Component form of `TotalNablaRSRealizes.eval_moving_slots`.

The hypotheses `hβ_at`, `hX_at`, and `hV_at` identify the moving input and
lower slots with the chosen pointwise basis at `x₀`. -/
theorem TotalNablaRSRealizes.component_moving_slots {r s : ℕ}
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    {cov : CovariantDerivative I E (TangentSpace I : M -> Type _)}
    {T : TensorRSField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) r s}
    {nablaT : TensorRSField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) r (s + 1)}
    (h : TotalNablaRSRealizes (𝕜 := 𝕜) (E := E) (H := H)
      (I := I) (M := M) r s cov T nablaT)
    (X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (β : (x : M) -> Tensor0SSpace (𝕜 := 𝕜) (E := E) (H := H) (I := I)
      (M := M) r x)
    (V : Fin s -> (x : M) -> TangentSpace I x) (x₀ : M)
    (basis : Module.Basis Idx 𝕜 (TangentSpace I x₀))
    (upper : Fin r -> Idx) (lower : Fin (s + 1) -> Idx)
    (hβ_at : β x₀ = basisTensor0S (I := I) basis upper)
    (hX_at : X x₀ = basis (lower 0))
    (hV_at : ∀ a : Fin s, V a x₀ = basis (lower a.succ))
    (hpair : MDifferentiableAt I 𝓘(𝕜, 𝕜)
      (fun p : M => (T p (β p)) (fun a : Fin s => V a p)) x₀)
    (hβmodel : DifferentiableWithinAt 𝕜
      (tensor0SModelInChart (𝕜 := 𝕜) (E := E) (H := H) (I := I)
        (M := M) r x₀ β)
      (Set.range I) (extChartAt I x₀ x₀))
    (hV : ∀ a : Fin s, MDiffAt (T% (V a)) x₀)
    (hVmodel : ∀ a : Fin s,
      DifferentiableWithinAt 𝕜
        (tangentFieldModelInChart (𝕜 := 𝕜) (I := I) x₀ (V a))
        (Set.range I) (extChartAt I x₀ x₀))
    (hcoord : ∀ a : Fin s, ∀ i : Fin (Module.finrank 𝕜 E),
      MDifferentiableAt I 𝓘(𝕜, 𝕜)
        (fun p : M =>
          (Module.finBasis 𝕜 E).coord i
            (tangentFieldModelInChart (𝕜 := 𝕜) (I := I) x₀ (V a)
              (extChartAt I x₀ p))) x₀) :
    componentRS (I := I) basis (nablaT x₀) upper lower =
      extDerivFun (I := I) (fun p : M => (T p (β p)) (fun a : Fin s => V a p))
        x₀ (X x₀) -
        (T x₀ (localCovariantDerivTensor0SAt
          (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) r cov X β x₀))
          (fun a : Fin s => V a x₀) -
        ∑ a : Fin s,
          (T x₀ (β x₀))
            (Function.update (fun b : Fin s => V b x₀) a
              ((cov (V a) x₀) (X x₀))) := by
  let slots : Fin s -> TangentSpace I x₀ := fun a => V a x₀
  have hslots :
      (fun a : Fin (s + 1) => basis (lower a)) =
        Fin.cons (X x₀) slots := by
    funext a
    cases a using Fin.cases with
    | zero =>
        simp [slots, hX_at]
    | succ a =>
        simp [slots, hV_at a]
  have hEval :=
    TotalNablaRSRealizes.eval_moving_slots
      (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      h X β V x₀ hpair hβmodel hV hVmodel hcoord
  simpa [componentRS_apply, hβ_at, hslots, slots] using hEval

/-- A total covariant-derivative realization for a covariant tensor field also
realizes the mixed-tensor derivative after embedding both fields with zero
upper slots. -/
theorem TotalNabla0SRealizes.toRS0 {s : ℕ}
    {cov : CovariantDerivative I E (TangentSpace I : M → Type _)}
    {α : Tensor0SField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s}
    {nablaAlpha : Tensor0SField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) (s + 1)}
    (h : TotalNabla0SRealizes (𝕜 := 𝕜) (E := E) (H := H)
      (I := I) (M := M) s cov α nablaAlpha) :
    TotalNablaRSRealizes (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      0 s cov
      (tensor0SField_toRS0 (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
        (∞ : WithTop ℕ∞) α)
      (tensor0SField_toRS0 (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
        (∞ : WithTop ℕ∞) nablaAlpha) := by
  intro X x β slots
  rw [tensor0SField_toRS0_apply, Tensor0SSpace.toRS0_apply]
  rw [nablaRSFun_toRS0, Tensor0SSpace.toRS0_apply]
  simp only [ContinuousMultilinearMap.smul_apply]
  rw [h.apply X x slots]

/-- Second total covariant derivative of a covariant tensor, defined by
iteration.  Internally the output valence is `(s + 1) + 1`, with derivative
slots first. -/
noncomputable def totalNabla20S (s : ℕ)
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (α : Tensor0SField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s)
    (hreg1 : TotalNabla0SRegular (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      s cov α)
    (hreg2 : TotalNabla0SRegular (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (s + 1) cov
      (totalNabla0S (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
        s cov α hreg1)) :
    Tensor0SField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) ((s + 1) + 1) :=
  totalNabla0S (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
    (s + 1) cov
    (totalNabla0S (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      s cov α hreg1)
    hreg2

/-- Same second derivative, normalized for consumers that state the output
valence as `s + 2`. -/
noncomputable def totalNabla20S_succSucc (s : ℕ)
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (α : Tensor0SField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s)
    (hreg1 : TotalNabla0SRegular (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      s cov α)
    (hreg2 : TotalNabla0SRegular (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (s + 1) cov
      (totalNabla0S (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
        s cov α hreg1)) :
    Tensor0SField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) (s + 2) :=
  totalNabla20S (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
    s cov α hreg1 hreg2

/-- Recursive realization predicate for the `k`-th covariant derivative of a
covariant tensor field.  The derivative slots are placed first; the Lean valence
is therefore `k + s`. -/
inductive HigherCovDeriv0SRealizes
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    {s : ℕ}
    (α : Tensor0SField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s) :
    (k : ℕ) →
      Tensor0SField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
        (n := (∞ : WithTop ℕ∞)) (k + s) → Prop
  | zero :
      HigherCovDeriv0SRealizes cov α 0
        (by
          simpa :
            Tensor0SField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
              (n := (∞ : WithTop ℕ∞)) (0 + s))
  | succ {k : ℕ}
      {αk : Tensor0SField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
        (n := (∞ : WithTop ℕ∞)) (k + s)}
      {αk1 : Tensor0SField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
        (n := (∞ : WithTop ℕ∞)) ((k + s) + 1)}
      (hk : HigherCovDeriv0SRealizes cov α k αk)
      (hstep : TotalNabla0SRealizes (𝕜 := 𝕜) (E := E) (H := H)
        (I := I) (M := M) (k + s) cov αk αk1) :
      HigherCovDeriv0SRealizes cov α (k + 1)
        (by
          simpa [Nat.add_assoc, Nat.succ_add, Nat.add_comm, Nat.add_left_comm] using αk1 :
            Tensor0SField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
              (n := (∞ : WithTop ℕ∞)) ((k + 1) + s))

/-- Recursive realization predicate for the `k`-th covariant derivative of a
mixed tensor field. -/
inductive HigherCovDerivRSRealizes
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    {r s : ℕ}
    (T : TensorRSField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) r s) :
    (k : ℕ) →
      TensorRSField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
        (n := (∞ : WithTop ℕ∞)) r (k + s) → Prop
  | zero :
      HigherCovDerivRSRealizes cov T 0
        (by
          simpa :
            TensorRSField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
              (n := (∞ : WithTop ℕ∞)) r (0 + s))
  | succ {k : ℕ}
      {Tk : TensorRSField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
        (n := (∞ : WithTop ℕ∞)) r (k + s)}
      {Tk1 : TensorRSField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
        (n := (∞ : WithTop ℕ∞)) r ((k + s) + 1)}
      (hk : HigherCovDerivRSRealizes cov T k Tk)
      (hstep : TotalNablaRSRealizes (𝕜 := 𝕜) (E := E) (H := H)
        (I := I) (M := M) r (k + s) cov Tk Tk1) :
      HigherCovDerivRSRealizes cov T (k + 1)
        (by
          simpa [Nat.add_assoc, Nat.succ_add, Nat.add_comm, Nat.add_left_comm] using Tk1 :
            TensorRSField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
              (n := (∞ : WithTop ℕ∞)) r ((k + 1) + s))

/-- Normalized recursive realization predicate for the `k`-th covariant
derivative of a covariant tensor field.

Unlike `HigherCovDeriv0SRealizes`, the output valence is written as `s + k`,
so the zero case and successor case reduce definitionally.  This is the
preferred realization shape for iterated product-rule constructions. -/
inductive IterNabla0SRealizes
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    {s : ℕ}
    (α : Tensor0SField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s) :
    (k : ℕ) →
      Tensor0SField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
        (n := (∞ : WithTop ℕ∞)) (s + k) → Prop
  | zero :
      IterNabla0SRealizes cov α 0 α
  | succ {k : ℕ}
      {αk : Tensor0SField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
        (n := (∞ : WithTop ℕ∞)) (s + k)}
      {αk1 : Tensor0SField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
        (n := (∞ : WithTop ℕ∞)) ((s + k) + 1)}
      (hk : IterNabla0SRealizes cov α k αk)
      (hstep : TotalNabla0SRealizes (𝕜 := 𝕜) (E := E) (H := H)
        (I := I) (M := M) (s + k) cov αk αk1) :
      IterNabla0SRealizes cov α (k + 1) αk1

/-- Unpack the first derivative realization from the normalized iterated
predicate. -/
theorem IterNabla0SRealizes.one {s : ℕ}
    {cov : CovariantDerivative I E (TangentSpace I : M -> Type _)}
    {α : Tensor0SField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s}
    {α1 : Tensor0SField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) (s + 1)}
    (h : IterNabla0SRealizes (𝕜 := 𝕜) (E := E) (H := H)
      (I := I) (M := M) cov α 1 α1) :
    TotalNabla0SRealizes (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      s cov α α1 := by
  exact
    match h with
    | IterNabla0SRealizes.succ IterNabla0SRealizes.zero hstep =>
        hstep

/-- Pointwise form of `IterNabla0SRealizes.one`. -/
theorem IterNabla0SRealizes.one_apply {s : ℕ}
    {cov : CovariantDerivative I E (TangentSpace I : M -> Type _)}
    {α : Tensor0SField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s}
    {α1 : Tensor0SField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) (s + 1)}
    (h : IterNabla0SRealizes (𝕜 := 𝕜) (E := E) (H := H)
      (I := I) (M := M) cov α 1 α1)
    (X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (x : M) (slots : Fin s -> TangentSpace I x) :
    α1 x (Fin.cons (X x) slots) =
      nabla0SFun (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
        s cov X α x slots :=
  (IterNabla0SRealizes.one (𝕜 := 𝕜) (E := E) (H := H)
    (I := I) (M := M) h).apply X x slots

/-- Decompose a normalized successor derivative realization into the previous
derivative field and the final total-nabla step. -/
theorem IterNabla0SRealizes.succ_inv {s k : ℕ}
    {cov : CovariantDerivative I E (TangentSpace I : M -> Type _)}
    {α : Tensor0SField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s}
    {αk1 : Tensor0SField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) (s + (k + 1))}
    (h : IterNabla0SRealizes (𝕜 := 𝕜) (E := E) (H := H)
      (I := I) (M := M) cov α (k + 1) αk1) :
    ∃ αk : Tensor0SField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
        (n := (∞ : WithTop ℕ∞)) (s + k),
      IterNabla0SRealizes (𝕜 := 𝕜) (E := E) (H := H)
        (I := I) (M := M) cov α k αk ∧
      TotalNabla0SRealizes (𝕜 := 𝕜) (E := E) (H := H)
        (I := I) (M := M) (s + k) cov αk αk1 := by
  exact
    match h with
    | IterNabla0SRealizes.succ hk hstep =>
        ⟨_, hk, hstep⟩

/-- Decompose a normalized second derivative realization into its two
successive total-nabla steps. -/
theorem IterNabla0SRealizes.two {s : ℕ}
    {cov : CovariantDerivative I E (TangentSpace I : M -> Type _)}
    {α : Tensor0SField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s}
    {α2 : Tensor0SField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) (s + 2)}
    (h : IterNabla0SRealizes (𝕜 := 𝕜) (E := E) (H := H)
      (I := I) (M := M) cov α 2 α2) :
    ∃ α1 : Tensor0SField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
        (n := (∞ : WithTop ℕ∞)) (s + 1),
      TotalNabla0SRealizes (𝕜 := 𝕜) (E := E) (H := H)
        (I := I) (M := M) s cov α α1 ∧
      TotalNabla0SRealizes (𝕜 := 𝕜) (E := E) (H := H)
        (I := I) (M := M) (s + 1) cov α1 α2 := by
  rcases IterNabla0SRealizes.succ_inv (𝕜 := 𝕜) (E := E) (H := H)
      (I := I) (M := M) (k := 1) h with ⟨α1, h1, hstep2⟩
  exact ⟨α1, IterNabla0SRealizes.one (I := I) h1, hstep2⟩

/-- Decompose a normalized third derivative realization into its three
successive total-nabla steps. -/
theorem IterNabla0SRealizes.three {s : ℕ}
    {cov : CovariantDerivative I E (TangentSpace I : M -> Type _)}
    {α : Tensor0SField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s}
    {α3 : Tensor0SField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) (s + 3)}
    (h : IterNabla0SRealizes (𝕜 := 𝕜) (E := E) (H := H)
      (I := I) (M := M) cov α 3 α3) :
    ∃ (α1 : Tensor0SField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
          (n := (∞ : WithTop ℕ∞)) (s + 1))
      (α2 : Tensor0SField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
          (n := (∞ : WithTop ℕ∞)) (s + 2)),
      TotalNabla0SRealizes (𝕜 := 𝕜) (E := E) (H := H)
        (I := I) (M := M) s cov α α1 ∧
      TotalNabla0SRealizes (𝕜 := 𝕜) (E := E) (H := H)
        (I := I) (M := M) (s + 1) cov α1 α2 ∧
      TotalNabla0SRealizes (𝕜 := 𝕜) (E := E) (H := H)
        (I := I) (M := M) (s + 2) cov α2 α3 := by
  rcases IterNabla0SRealizes.succ_inv (𝕜 := 𝕜) (E := E) (H := H)
      (I := I) (M := M) (k := 2) h with ⟨α2, h2, hstep3⟩
  rcases IterNabla0SRealizes.two (𝕜 := 𝕜) (E := E) (H := H)
      (I := I) (M := M) h2 with ⟨α1, hstep1, hstep2⟩
  exact ⟨α1, α2, hstep1, hstep2, hstep3⟩

/-- Decompose a normalized fourth derivative realization into its four
successive total-nabla steps. -/
theorem IterNabla0SRealizes.four {s : ℕ}
    {cov : CovariantDerivative I E (TangentSpace I : M -> Type _)}
    {α : Tensor0SField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s}
    {α4 : Tensor0SField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) (s + 4)}
    (h : IterNabla0SRealizes (𝕜 := 𝕜) (E := E) (H := H)
      (I := I) (M := M) cov α 4 α4) :
    ∃ (α1 : Tensor0SField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
          (n := (∞ : WithTop ℕ∞)) (s + 1))
      (α2 : Tensor0SField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
          (n := (∞ : WithTop ℕ∞)) (s + 2))
      (α3 : Tensor0SField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
          (n := (∞ : WithTop ℕ∞)) (s + 3)),
      TotalNabla0SRealizes (𝕜 := 𝕜) (E := E) (H := H)
        (I := I) (M := M) s cov α α1 ∧
      TotalNabla0SRealizes (𝕜 := 𝕜) (E := E) (H := H)
        (I := I) (M := M) (s + 1) cov α1 α2 ∧
      TotalNabla0SRealizes (𝕜 := 𝕜) (E := E) (H := H)
        (I := I) (M := M) (s + 2) cov α2 α3 ∧
      TotalNabla0SRealizes (𝕜 := 𝕜) (E := E) (H := H)
        (I := I) (M := M) (s + 3) cov α3 α4 := by
  rcases IterNabla0SRealizes.succ_inv (𝕜 := 𝕜) (E := E) (H := H)
      (I := I) (M := M) (k := 3) h with ⟨α3, h3, hstep4⟩
  rcases IterNabla0SRealizes.three (𝕜 := 𝕜) (E := E) (H := H)
      (I := I) (M := M) h3 with ⟨α1, α2, hstep1, hstep2, hstep3⟩
  exact ⟨α1, α2, α3, hstep1, hstep2, hstep3, hstep4⟩

/-- Infinite normalized covariant derivative jet for a covariant tensor field.

The field `term k` is the intended `k`-th total covariant derivative, with
valence normalized as `s + k`.  This packages the data needed by future
all-order Leibniz/product-rule constructions without using the older
`k + s` cast-heavy shape. -/
structure IterNabla0SJet
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    {s : ℕ}
    (α : Tensor0SField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s) where
  term : (k : ℕ) ->
    Tensor0SField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) (s + k)
  zero_eq : term 0 = α
  step : ∀ k : ℕ,
    TotalNabla0SRealizes (𝕜 := 𝕜) (E := E) (H := H)
      (I := I) (M := M) (s + k) cov (term k) (term (k + 1))

/-- Every level of an `IterNabla0SJet` realizes the corresponding normalized
iterated covariant derivative. -/
theorem IterNabla0SJet.realizes {s k : ℕ}
    {cov : CovariantDerivative I E (TangentSpace I : M -> Type _)}
    {α : Tensor0SField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s}
    (J : IterNabla0SJet (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      cov α) :
    IterNabla0SRealizes (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      cov α k (J.term k) := by
  induction k with
  | zero =>
      simpa [J.zero_eq] using
        (IterNabla0SRealizes.zero :
          IterNabla0SRealizes (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
            cov α 0 α)
  | succ k ih =>
      exact IterNabla0SRealizes.succ ih (J.step k)

/-- Tail of a covariant derivative jet, starting from the first derivative
field. -/
noncomputable def IterNabla0SJet.tail {s : ℕ}
    {cov : CovariantDerivative I E (TangentSpace I : M -> Type _)}
    {α : Tensor0SField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s}
    (J : IterNabla0SJet (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      cov α) :
    IterNabla0SJet (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      cov (J.term 1) where
  term k :=
    tensor0SFieldCast (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (by omega : s + (k + 1) = (s + 1) + k)
      (J.term (k + 1))
  zero_eq := by
    simp [tensor0SFieldCast]
  step k := by
    let hst : s + (k + 1) = (s + 1) + k := by omega
    let hnext : s + (k + 1 + 1) = (s + 1) + (k + 1) := by omega
    refine TotalNabla0SRealizes.congr (𝕜 := 𝕜) (E := E) (H := H)
      (I := I) (M := M) ?_ ?_
      (TotalNabla0SRealizes.castField (𝕜 := 𝕜) (E := E) (H := H)
        (I := I) (M := M) hst (J.step (k + 1)))
    · exact tensor0SFieldCast_proof_irrel (𝕜 := 𝕜) (E := E) (H := H)
        (I := I) (M := M)
        hst
        (by omega : s + (k + 1) = (s + 1) + k)
        (J.term (k + 1))
    · exact tensor0SFieldCast_proof_irrel (𝕜 := 𝕜) (E := E) (H := H)
        (I := I) (M := M)
        (congrArg (fun n : ℕ => n + 1) hst)
        hnext
        (J.term (k + 1 + 1))

/-- Normalized recursive realization predicate for the `k`-th covariant
derivative of a mixed tensor field.

The output lower valence is written as `s + k`; this avoids the `0 + s`
transport artifacts of `HigherCovDerivRSRealizes` in induction and product-rule
arguments. -/
inductive IterNablaRSRealizes
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    {r s : ℕ}
    (T : TensorRSField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) r s) :
    (k : ℕ) →
      TensorRSField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
        (n := (∞ : WithTop ℕ∞)) r (s + k) → Prop
  | zero :
      IterNablaRSRealizes cov T 0 T
  | succ {k : ℕ}
      {Tk : TensorRSField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
        (n := (∞ : WithTop ℕ∞)) r (s + k)}
      {Tk1 : TensorRSField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
        (n := (∞ : WithTop ℕ∞)) r ((s + k) + 1)}
      (hk : IterNablaRSRealizes cov T k Tk)
      (hstep : TotalNablaRSRealizes (𝕜 := 𝕜) (E := E) (H := H)
        (I := I) (M := M) r (s + k) cov Tk Tk1) :
      IterNablaRSRealizes cov T (k + 1) Tk1

/-- Embed a normalized covariant iterated-derivative realization as the
corresponding mixed realization with zero upper slots. -/
theorem IterNabla0SRealizes.toRS0 {s k : ℕ}
    {cov : CovariantDerivative I E (TangentSpace I : M → Type _)}
    {α : Tensor0SField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s}
    {αk : Tensor0SField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) (s + k)}
    (h : IterNabla0SRealizes (𝕜 := 𝕜) (E := E) (H := H)
      (I := I) (M := M) cov α k αk) :
    IterNablaRSRealizes (𝕜 := 𝕜) (E := E) (H := H)
      (I := I) (M := M) cov
      (tensor0SField_toRS0 (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
        (∞ : WithTop ℕ∞) α)
      k
      (tensor0SField_toRS0 (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
        (∞ : WithTop ℕ∞) αk) := by
  induction h with
  | zero =>
      exact IterNablaRSRealizes.zero
  | succ hk hstep ih =>
      exact IterNablaRSRealizes.succ ih hstep.toRS0

/-- Unpack the first derivative realization from the normalized mixed
iterated predicate. -/
theorem IterNablaRSRealizes.one {r s : ℕ}
    {cov : CovariantDerivative I E (TangentSpace I : M -> Type _)}
    {T : TensorRSField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) r s}
    {T1 : TensorRSField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) r (s + 1)}
    (h : IterNablaRSRealizes (𝕜 := 𝕜) (E := E) (H := H)
      (I := I) (M := M) cov T 1 T1) :
    TotalNablaRSRealizes (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      r s cov T T1 := by
  exact
    match h with
    | IterNablaRSRealizes.succ IterNablaRSRealizes.zero hstep =>
        hstep

/-- Pointwise form of `IterNablaRSRealizes.one`. -/
theorem IterNablaRSRealizes.one_apply {r s : ℕ}
    {cov : CovariantDerivative I E (TangentSpace I : M -> Type _)}
    {T : TensorRSField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) r s}
    {T1 : TensorRSField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) r (s + 1)}
    (h : IterNablaRSRealizes (𝕜 := 𝕜) (E := E) (H := H)
      (I := I) (M := M) cov T 1 T1)
    (X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (x : M) (β : Tensor0SSpace r I x) (slots : Fin s -> TangentSpace I x) :
    T1 x β (Fin.cons (X x) slots) =
      nablaRSFun (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
        r s cov X T x β slots :=
  (IterNablaRSRealizes.one (𝕜 := 𝕜) (E := E) (H := H)
    (I := I) (M := M) h).apply X x β slots

/-- Decompose a normalized mixed successor derivative realization into the
previous derivative field and the final total-nabla step. -/
theorem IterNablaRSRealizes.succ_inv {r s k : ℕ}
    {cov : CovariantDerivative I E (TangentSpace I : M -> Type _)}
    {T : TensorRSField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) r s}
    {Tk1 : TensorRSField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) r (s + (k + 1))}
    (h : IterNablaRSRealizes (𝕜 := 𝕜) (E := E) (H := H)
      (I := I) (M := M) cov T (k + 1) Tk1) :
    ∃ Tk : TensorRSField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
        (n := (∞ : WithTop ℕ∞)) r (s + k),
      IterNablaRSRealizes (𝕜 := 𝕜) (E := E) (H := H)
        (I := I) (M := M) cov T k Tk ∧
      TotalNablaRSRealizes (𝕜 := 𝕜) (E := E) (H := H)
        (I := I) (M := M) r (s + k) cov Tk Tk1 := by
  exact
    match h with
    | IterNablaRSRealizes.succ hk hstep =>
        ⟨_, hk, hstep⟩

/-- Infinite normalized covariant derivative jet for a mixed tensor field.

The lower valence of `term k` is normalized as `s + k`, matching
`IterNablaRSRealizes` and avoiding the older `k + s` transport artifacts. -/
structure IterNablaRSJet
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    {r s : ℕ}
    (T : TensorRSField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) r s) where
  term : (k : ℕ) ->
    TensorRSField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) r (s + k)
  zero_eq : term 0 = T
  step : ∀ k : ℕ,
    TotalNablaRSRealizes (𝕜 := 𝕜) (E := E) (H := H)
      (I := I) (M := M) r (s + k) cov (term k) (term (k + 1))

/-- Every level of an `IterNablaRSJet` realizes the corresponding normalized
iterated covariant derivative. -/
theorem IterNablaRSJet.realizes {r s k : ℕ}
    {cov : CovariantDerivative I E (TangentSpace I : M -> Type _)}
    {T : TensorRSField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) r s}
    (J : IterNablaRSJet (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      cov T) :
    IterNablaRSRealizes (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      cov T k (J.term k) := by
  induction k with
  | zero =>
      simpa [J.zero_eq] using
        (IterNablaRSRealizes.zero :
          IterNablaRSRealizes (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
            cov T 0 T)
  | succ k ih =>
      exact IterNablaRSRealizes.succ ih (J.step k)

/-- Embed a normalized covariant derivative jet as a mixed derivative jet with
zero upper slots. -/
noncomputable def IterNabla0SJet.toRS0 {s : ℕ}
    {cov : CovariantDerivative I E (TangentSpace I : M -> Type _)}
    {α : Tensor0SField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s}
    (J : IterNabla0SJet (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      cov α) :
    IterNablaRSJet (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      cov
      (tensor0SField_toRS0 (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
        (∞ : WithTop ℕ∞) α) where
  term k :=
    tensor0SField_toRS0 (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (∞ : WithTop ℕ∞) (J.term k)
  zero_eq := by
    rw [J.zero_eq]
  step k :=
    (J.step k).toRS0

/-- Unpack the first derivative realization of a `(1,2)` mixed tensor into
the corresponding total-nabla realization. -/
theorem HigherCovDerivRSRealizes.one_12
    {cov : CovariantDerivative I E (TangentSpace I : M -> Type _)}
    {T : TensorRSField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 1 2}
    {T1 : TensorRSField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 1 3}
    (h : HigherCovDerivRSRealizes (𝕜 := 𝕜) (E := E) (H := H)
      (I := I) (M := M) cov T 1 T1) :
    TotalNablaRSRealizes (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      1 2 cov T T1 := by
  exact
    match h with
    | HigherCovDerivRSRealizes.succ HigherCovDerivRSRealizes.zero hstep =>
        by simpa using hstep

/-- Pointwise form of `HigherCovDerivRSRealizes.one_12`. -/
theorem HigherCovDerivRSRealizes.one_apply_12
    {cov : CovariantDerivative I E (TangentSpace I : M -> Type _)}
    {T : TensorRSField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 1 2}
    {T1 : TensorRSField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 1 3}
    (h : HigherCovDerivRSRealizes (𝕜 := 𝕜) (E := E) (H := H)
      (I := I) (M := M) cov T 1 T1)
    (X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (x : M) (β : Tensor0SSpace 1 I x) (slots : Fin 2 -> TangentSpace I x) :
    T1 x β (Fin.cons (X x) slots) =
      nablaRSFun (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
        1 2 cov X T x β slots :=
  (HigherCovDerivRSRealizes.one_12 (𝕜 := 𝕜) (E := E) (H := H)
    (I := I) (M := M) h).apply X x β slots

theorem higherCovDeriv0SRealizes_two_apply {s : ℕ}
    {cov : CovariantDerivative I E (TangentSpace I : M → Type _)}
    {nablaAlpha : Tensor0SField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) (s + 1)}
    {nabla2Alpha : Tensor0SField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) ((s + 1) + 1)}
    (h2 : TotalNabla0SRealizes (𝕜 := 𝕜) (E := E) (H := H)
      (I := I) (M := M) (s + 1) cov nablaAlpha nabla2Alpha)
    (X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _))
    (x : M) (slots : Fin (s + 1) → TangentSpace I x) :
    nabla2Alpha x (Fin.cons (X x) slots) =
      nabla0SFun (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
        (s + 1) cov X nablaAlpha x slots :=
  h2.apply X x slots

end

section RealLinearity

set_option backward.isDefEq.respectTransparency false

open Bundle Set IsManifold ContinuousLinearMap TensorLieDeriv
open scoped Manifold Topology Bundle ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I 1 M] [IsManifold I 2 M]
variable [IsManifold I (∞ : WithTop ℕ∞) M]
variable [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]

/-- Difference of two directional covariant derivatives on the same covariant
tensor field.  This is the lower-slot action of the connection-difference
tensor, and is the invariant form of the MSM135 shorthand
`(∇ - ∇ₖ)T = (Γ - Γₖ) * T` for covariant tensors. -/
theorem nabla0SFun_sub_cov
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    [ContMDiffVectorBundle 1 E (TangentSpace I : M -> Type _) I]
    {s : ℕ}
    (cov cov' : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (V : Fin s -> ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M -> Type _))
    (α : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s)
    (x : M) :
    ((nabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
          s cov X α x) -
        nabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
          s cov' X α x) (fun a : Fin s => V a x) =
      -∑ a : Fin s,
        α x
          (Function.update (fun b : Fin s => V b x) a
            (((CovariantDerivative.difference cov cov' x) (V a x)) (X x))) := by
  classical
  let slots : Fin s -> TangentSpace I x := fun a => V a x
  have hcov := nabla0SFun_eval_smooth_slots (I := I) cov X V α x
  have hcov' := nabla0SFun_eval_smooth_slots (I := I) cov' X V α x
  have hdiff (a : Fin s) :
      α x
          (Function.update slots a ((cov (fun p : M => V a p) x) (X x))) -
        α x
          (Function.update slots a ((cov' (fun p : M => V a p) x) (X x))) =
        α x
          (Function.update slots a
            (((CovariantDerivative.difference cov cov' x) (V a x)) (X x))) := by
    have hconn :
        ((CovariantDerivative.difference cov cov' x) (V a x)) (X x) =
          ((cov (fun p : M => V a p) x) (X x)) -
            ((cov' (fun p : M => V a p) x) (X x)) := by
      have h :=
        IsCovariantDerivativeOn.difference_apply
          (hcov := cov.isCovariantDerivativeOnUniv)
          (hcov' := cov'.isCovariantDerivativeOnUniv)
          (σ := fun p : M => V a p) (x := x) (hx := by trivial)
          ((V a).contMDiff.contMDiffAt.mdifferentiableAt (by simp))
      exact congrArg (fun L : TangentSpace I x →L[Real] TangentSpace I x => L (X x)) h
    rw [hconn]
    exact ((α x).map_update_sub slots a
      ((cov (fun p : M => V a p) x) (X x))
      ((cov' (fun p : M => V a p) x) (X x))).symm
  let D : Real :=
    (extDerivFun (I := I) (fun p : M => α p (fun a : Fin s => V a p)) x) (X x)
  let Scov : Real :=
    ∑ a : Fin s,
      α x (Function.update slots a ((cov (fun p : M => V a p) x) (X x)))
  let Scov' : Real :=
    ∑ a : Fin s,
      α x (Function.update slots a ((cov' (fun p : M => V a p) x) (X x)))
  let Sdiff : Real :=
    ∑ a : Fin s,
      α x
        (Function.update slots a
          (((CovariantDerivative.difference cov cov' x) (V a x)) (X x)))
  have hsum : Scov - Scov' = Sdiff := by
    dsimp [Scov, Scov', Sdiff]
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    exact hdiff a
  change
    (nabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
          s cov X α x) slots -
        (nabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
          s cov' X α x) slots =
      -∑ a : Fin s,
        α x
          (Function.update slots a
            (((CovariantDerivative.difference cov cov' x) (V a x)) (X x)))
  rw [hcov, hcov']
  change (D - Scov) - (D - Scov') = -Sdiff
  rw [← hsum]
  ring

/-- Two-covariant-slot specialization of `nabla0SFun_sub_cov`.

This is the invariant form of the MSM135 component identity that the
difference of two covariant derivatives on a two-tensor is the connection
difference acting on the two lower slots. -/
theorem nabla0SFun_sub_cov_two
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    [ContMDiffVectorBundle 1 E (TangentSpace I : M -> Type _) I]
    (cov cov' : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (X Y Z : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (α : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 2)
    (x : M) :
    ((nabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
          2 cov X α x) -
        nabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
          2 cov' X α x)
        (fun q : Fin 2 => if q = 0 then Y x else Z x) =
      -((α x)
          (fun q : Fin 2 =>
            if q = 0 then
              ((CovariantDerivative.difference cov cov' x) (Y x)) (X x)
            else Z x) +
        (α x)
          (fun q : Fin 2 =>
            if q = 0 then Y x
            else ((CovariantDerivative.difference cov cov' x) (Z x)) (X x))) := by
  classical
  let V : Fin 2 -> ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M -> Type _) :=
    fun q => if q = 0 then Y else Z
  let DY : TangentSpace I x :=
    ((CovariantDerivative.difference cov cov' x) (Y x)) (X x)
  let DZ : TangentSpace I x :=
    ((CovariantDerivative.difference cov cov' x) (Z x)) (X x)
  have hupdate0 :
      Function.update (fun b : Fin 2 => V b x) (0 : Fin 2) DY =
        (fun q : Fin 2 => if q = 0 then DY else Z x) := by
    funext q
    fin_cases q <;> simp [V, DY]
  have hupdate1 :
      Function.update (fun b : Fin 2 => V b x) (1 : Fin 2) DZ =
        (fun q : Fin 2 => if q = 0 then Y x else DZ) := by
    funext q
    fin_cases q <;> simp [V, DZ]
  have h := nabla0SFun_sub_cov (I := I) cov cov' X V α x
  have hslots :
      (fun q : Fin 2 => if q = 0 then Y x else Z x) =
        (fun q : Fin 2 => V q x) := by
    funext q
    fin_cases q <;> simp [V]
  calc
    ((nabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
          2 cov X α x) -
        nabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
          2 cov' X α x)
        (fun q : Fin 2 => if q = 0 then Y x else Z x)
        =
      ((nabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
          2 cov X α x) -
        nabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
          2 cov' X α x)
        (fun q : Fin 2 => V q x) := by
          rw [hslots]
    _ = -∑ a : Fin 2,
          α x
            (Function.update (fun b : Fin 2 => V b x) a
              (((CovariantDerivative.difference cov cov' x) (V a x)) (X x))) := h
    _ = -((α x)
          (fun q : Fin 2 =>
            if q = 0 then
              ((CovariantDerivative.difference cov cov' x) (Y x)) (X x)
            else Z x) +
        (α x)
          (fun q : Fin 2 =>
            if q = 0 then Y x
            else ((CovariantDerivative.difference cov cov' x) (Z x)) (X x))) := by
          rw [Fin.sum_univ_two]
          simp [V, DY, DZ, hupdate0, hupdate1]

/-- The directional covariant derivative of covariant tensor fields is
additive in the tensor argument.  This Real-specialized form matches the
smooth-section extension API used throughout the RicciFlower geometry layer. -/
theorem nabla0SFun_add [T2Space M] {s : ℕ}
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _))
    (α β : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s)
    (x : M) :
    nabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        s cov X (α + β) x =
      nabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
          s cov X α x +
        nabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
          s cov X β x := by
  classical
  let basis : Module.Basis (Fin (Module.finrank Real (TangentSpace I x))) Real
      (TangentSpace I x) :=
    Module.finBasis Real (TangentSpace I x)
  apply ext0S_basis (I := I) basis
  intro idx
  let V : Fin s -> ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M -> Type _) :=
    fun a =>
      (ContMDiffSection.exists_eq_at
        (I := I) (F := E) (V := TangentSpace I) (n := (⊤ : ℕ∞))
        x (basis (idx a))).choose
  have hV : ∀ a : Fin s, V a x = basis (idx a) := by
    intro a
    exact
      (ContMDiffSection.exists_eq_at
        (I := I) (F := E) (V := TangentSpace I) (n := (⊤ : ℕ∞))
        x (basis (idx a))).choose_spec
  have hslots : (fun a : Fin s => V a x) = fun a : Fin s => basis (idx a) := by
    funext a
    exact hV a
  have hsum := nabla0SFun_eval_smooth_slots (I := I) cov X V (α + β) x
  have hα := nabla0SFun_eval_smooth_slots (I := I) cov X V α x
  have hβ := nabla0SFun_eval_smooth_slots (I := I) cov X V β x
  have hfα : MDifferentiableAt I 𝓘(Real, Real)
      (fun p : M => α p (fun a : Fin s => V a p)) x :=
    (tensor0SField_eval_smooth_slots_contMDiffAt (I := I) α V x).mdifferentiableAt
      (by simp)
  have hfβ : MDifferentiableAt I 𝓘(Real, Real)
      (fun p : M => β p (fun a : Fin s => V a p)) x :=
    (tensor0SField_eval_smooth_slots_contMDiffAt (I := I) β V x).mdifferentiableAt
      (by simp)
  have hext :
      extDerivFun (I := I)
          (fun p : M => (α + β) p (fun a : Fin s => V a p)) x (X x) =
        extDerivFun (I := I)
            (fun p : M => α p (fun a : Fin s => V a p)) x (X x) +
          extDerivFun (I := I)
            (fun p : M => β p (fun a : Fin s => V a p)) x (X x) := by
    change
      extDerivFun (I := I)
          ((fun p : M => α p (fun a : Fin s => V a p)) +
            fun p : M => β p (fun a : Fin s => V a p)) x (X x) =
        extDerivFun (I := I)
            (fun p : M => α p (fun a : Fin s => V a p)) x (X x) +
          extDerivFun (I := I)
            (fun p : M => β p (fun a : Fin s => V a p)) x (X x)
    rw [extDerivFun_add hfα hfβ]
    rfl
  simp only [component0S_apply]
  rw [← hslots]
  change
    (nabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        s cov X (α + β) x) (fun a : Fin s => V a x) =
      (nabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
          s cov X α x) (fun a : Fin s => V a x) +
        (nabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
          s cov X β x) (fun a : Fin s => V a x)
  rw [hsum, hα, hβ, hext]
  simp [Finset.sum_add_distrib]
  ring

/-- The directional covariant derivative of covariant tensor fields is
homogeneous under constant scalar multiplication of the tensor argument. -/
theorem nabla0SFun_smul [T2Space M] {s : ℕ}
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _))
    (c : Real)
    (α : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s)
    (x : M) :
    nabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        s cov X (c • α) x =
      c • nabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
          s cov X α x := by
  classical
  let basis : Module.Basis (Fin (Module.finrank Real (TangentSpace I x))) Real
      (TangentSpace I x) :=
    Module.finBasis Real (TangentSpace I x)
  apply ext0S_basis (I := I) basis
  intro idx
  let V : Fin s -> ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M -> Type _) :=
    fun a =>
      (ContMDiffSection.exists_eq_at
        (I := I) (F := E) (V := TangentSpace I) (n := (⊤ : ℕ∞))
        x (basis (idx a))).choose
  have hV : ∀ a : Fin s, V a x = basis (idx a) := by
    intro a
    exact
      (ContMDiffSection.exists_eq_at
        (I := I) (F := E) (V := TangentSpace I) (n := (⊤ : ℕ∞))
        x (basis (idx a))).choose_spec
  have hslots : (fun a : Fin s => V a x) = fun a : Fin s => basis (idx a) := by
    funext a
    exact hV a
  have hsmul := nabla0SFun_eval_smooth_slots (I := I) cov X V (c • α) x
  have hα := nabla0SFun_eval_smooth_slots (I := I) cov X V α x
  have hfα : MDifferentiableAt I 𝓘(Real, Real)
      (fun p : M => α p (fun a : Fin s => V a p)) x :=
    (tensor0SField_eval_smooth_slots_contMDiffAt (I := I) α V x).mdifferentiableAt
      (by simp)
  have hext :
      extDerivFun (I := I)
          (fun p : M => (c • α) p (fun a : Fin s => V a p)) x (X x) =
        c *
          extDerivFun (I := I)
            (fun p : M => α p (fun a : Fin s => V a p)) x (X x) := by
    have h := RicciFlower.extDerivFun_const_mul I c hfα
    exact congrArg (fun L : TangentSpace I x →L[Real] Real => L (X x)) h
  simp only [component0S_apply]
  rw [← hslots]
  change
    (nabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        s cov X (c • α) x) (fun a : Fin s => V a x) =
      c *
        (nabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
          s cov X α x) (fun a : Fin s => V a x)
  rw [hsmul, hα, hext]
  simp only [coe_comp', ContinuousLinearEquiv.coe_coe, Function.comp_apply,
    ContMDiffSection.coe_smul, Pi.smul_apply, ContinuousMultilinearMap.smul_apply,
    smul_eq_mul]
  rw [← Finset.mul_sum]
  ring

/-- The directional covariant derivative of the zero covariant tensor field is zero. -/
theorem nabla0SFun_zero [T2Space M] {s : ℕ}
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (x : M) :
    nabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        s cov X
        (0 : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
          (n := (∞ : WithTop ℕ∞)) s) x = 0 := by
  have h := nabla0SFun_smul (I := I) (s := s) cov X (0 : Real)
    (0 : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s) x
  simpa using h

/-- The directional covariant derivative of covariant tensor fields commutes
with finite sums. -/
theorem nabla0SFun_sum [T2Space M] {ι : Type*} {s : ℕ}
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (S : Finset ι)
    (T : ι -> Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s)
    (x : M) :
    nabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        s cov X (Finset.sum S T) x =
      Finset.sum S fun i =>
        nabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
          s cov X (T i) x := by
  classical
  refine Finset.induction_on S ?base ?step
  · change nabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        s cov X
        (0 : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
          (n := (∞ : WithTop ℕ∞)) s) x = 0
    exact nabla0SFun_zero (I := I) (s := s) cov X x
  · intro i A hi ih
    rw [Finset.sum_insert hi, nabla0SFun_add (I := I) cov X (T i) (Finset.sum A T) x]
    rw [ih, Finset.sum_insert hi]

set_option linter.unusedSectionVars false in
private theorem extDerivFun_mul_real_local
    {f g : M -> Real} {x : M} (v : TangentSpace I x)
    (hf : MDifferentiableAt I 𝓘(Real, Real) f x)
    (hg : MDifferentiableAt I 𝓘(Real, Real) g x) :
    extDerivFun (I := I) (fun y : M => f y * g y) x v =
      f x * extDerivFun (I := I) g x v +
        extDerivFun (I := I) f x v * g x := by
  change extDerivFun (I := I) (f • g) x v =
      f x * extDerivFun (I := I) g x v +
        extDerivFun (I := I) f x v * g x
  have hprod := fromTangentSpace_mfderiv_smul_apply
    (I := I) (f := f) (g := g) hf hg v
  simpa [extDerivFun, Pi.smul_apply, smul_eq_mul, mul_comm, mul_left_comm, mul_assoc]
    using hprod

set_option backward.isDefEq.respectTransparency false in
/-- Moving-slot product rule for the directional covariant derivative of
covariant tensor fields.

This is the evaluated Leibniz rule behind later total-derivative product
realization statements.  It keeps the derivative field out of the statement and
therefore avoids premature slot-permutation choices. -/
theorem nabla0SFun_product_eval_smooth_slots [T2Space M] [IsManifold I ⊤ M] {s q : ℕ}
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (V : Fin (s + q) -> ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M -> Type _))
    (α : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s)
    (β : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) q)
    (x : M) :
    (nabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        (s + q) cov X
        (tensor0SField_product (𝕜 := Real) (E := E) (H := H)
          (I := I) (M := M) (∞ : WithTop ℕ∞) α β) x)
      (fun a : Fin (s + q) => V a x) =
      (nabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
          s cov X α x)
        (fun a : Fin s => V (Fin.castAdd q a) x) *
        β x (fun b : Fin q => V (Fin.natAdd s b) x) +
      α x (fun a : Fin s => V (Fin.castAdd q a) x) *
        (nabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
          q cov X β x)
          (fun b : Fin q => V (Fin.natAdd s b) x) := by
  classical
  let γ : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) (s + q) :=
    tensor0SField_product (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (∞ : WithTop ℕ∞) α β
  let Vα : Fin s -> ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M -> Type _) := fun a => V (Fin.castAdd q a)
  let Vβ : Fin q -> ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M -> Type _) := fun b => V (Fin.natAdd s b)
  let f : M -> Real := fun p => α p (fun a : Fin s => Vα a p)
  let g : M -> Real := fun p => β p (fun b : Fin q => Vβ b p)
  have hγ := nabla0SFun_eval_smooth_slots (I := I) cov X V γ x
  have hα := nabla0SFun_eval_smooth_slots (I := I) cov X Vα α x
  have hβ := nabla0SFun_eval_smooth_slots (I := I) cov X Vβ β x
  have hf : MDifferentiableAt I 𝓘(Real, Real) f x :=
    (tensor0SField_eval_smooth_slots_contMDiffAt (I := I) α Vα x).mdifferentiableAt
      (by simp)
  have hg : MDifferentiableAt I 𝓘(Real, Real) g x :=
    (tensor0SField_eval_smooth_slots_contMDiffAt (I := I) β Vβ x).mdifferentiableAt
      (by simp)
  have hprod :
      extDerivFun (I := I) (fun p : M => γ p (fun a : Fin (s + q) => V a p))
          x (X x) =
        f x * extDerivFun (I := I) g x (X x) +
          extDerivFun (I := I) f x (X x) * g x := by
    have hmul := extDerivFun_mul_real_local
      (I := I) (M := M) (x := x) (X x) hf hg
    simpa [γ, f, g, Vα, Vβ, tensor0SField_product_apply,
      Bundle.continuousMultilinearMap.product_fun_apply, mul_comm, mul_left_comm, mul_assoc]
      using hmul
  have hcorr :
      (∑ a : Fin (s + q),
        γ x
          (Function.update (fun b : Fin (s + q) => V b x) a
            ((cov (fun p : M => V a p) x) (X x)))) =
        (∑ a : Fin s,
          α x
            (Function.update (fun b : Fin s => Vα b x) a
              ((cov (fun p : M => Vα a p) x) (X x)))) * g x +
        f x *
          (∑ b : Fin q,
            β x
              (Function.update (fun c : Fin q => Vβ c x) b
                ((cov (fun p : M => Vβ b p) x) (X x)))) := by
    rw [Fin.sum_univ_add]
    simp only [γ, f, g, Vα, Vβ, tensor0SField_product_apply,
      Bundle.continuousMultilinearMap.product_fun_apply]
    have hleft :
        (∑ a : Fin s,
          α x
            (Function.update (fun b : Fin (s + q) => V b x)
                (Fin.castAdd q a)
                ((cov (fun p : M => V (Fin.castAdd q a) p) x) (X x)) ∘
              Fin.castAdd q) *
            β x
              (Function.update (fun b : Fin (s + q) => V b x)
                  (Fin.castAdd q a)
                  ((cov (fun p : M => V (Fin.castAdd q a) p) x) (X x)) ∘
                Fin.natAdd s)) =
          (∑ a : Fin s,
            α x
              (Function.update (fun b : Fin s => V (Fin.castAdd q b) x) a
                ((cov (fun p : M => V (Fin.castAdd q a) p) x) (X x)))) *
            β x (fun b : Fin q => V (Fin.natAdd s b) x) := by
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun a _ => ?_
      congr 2
      · funext b
        by_cases hba : b = a
        · subst b
          simp
        · have hidx : Fin.castAdd q b ≠ Fin.castAdd q a := by
            intro h
            exact hba (Fin.castAdd_injective s q h)
          simp [Function.update_of_ne hidx, Function.update_of_ne hba]
      · funext b
        have hidx : Fin.natAdd s b ≠ Fin.castAdd q a := by
          intro h
          have hval := congrArg Fin.val h
          simp [Fin.val_natAdd, Fin.val_castAdd] at hval
          omega
        simp [Function.update_of_ne hidx]
    have hright :
        (∑ b : Fin q,
          α x
            (Function.update (fun a : Fin (s + q) => V a x)
                (Fin.natAdd s b)
                ((cov (fun p : M => V (Fin.natAdd s b) p) x) (X x)) ∘
              Fin.castAdd q) *
            β x
              (Function.update (fun a : Fin (s + q) => V a x)
                  (Fin.natAdd s b)
                  ((cov (fun p : M => V (Fin.natAdd s b) p) x) (X x)) ∘
                Fin.natAdd s)) =
          α x (fun a : Fin s => V (Fin.castAdd q a) x) *
            (∑ b : Fin q,
              β x
                (Function.update (fun c : Fin q => V (Fin.natAdd s c) x) b
                  ((cov (fun p : M => V (Fin.natAdd s b) p) x) (X x)))) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun b _ => ?_
      congr 2
      · funext a
        have hidx : Fin.castAdd q a ≠ Fin.natAdd s b := by
          intro h
          have hval := congrArg Fin.val h
          simp [Fin.val_castAdd, Fin.val_natAdd] at hval
          omega
        simp [Function.update_of_ne hidx]
      · funext c
        by_cases hcb : c = b
        · subst c
          simp
        · have hidx : Fin.natAdd s c ≠ Fin.natAdd s b := by
            intro h
            exact hcb (Fin.natAdd_injective q s h)
          simp [Function.update_of_ne hidx, Function.update_of_ne hcb]
    change
      (∑ a : Fin s,
          α x
            (Function.update (fun b : Fin (s + q) => V b x)
                (Fin.castAdd q a)
                ((cov (fun p : M => V (Fin.castAdd q a) p) x) (X x)) ∘
              Fin.castAdd q) *
            β x
              (Function.update (fun b : Fin (s + q) => V b x)
                  (Fin.castAdd q a)
                  ((cov (fun p : M => V (Fin.castAdd q a) p) x) (X x)) ∘
                Fin.natAdd s)) +
        (∑ b : Fin q,
          α x
            (Function.update (fun a : Fin (s + q) => V a x)
                (Fin.natAdd s b)
                ((cov (fun p : M => V (Fin.natAdd s b) p) x) (X x)) ∘
              Fin.castAdd q) *
            β x
              (Function.update (fun a : Fin (s + q) => V a x)
                  (Fin.natAdd s b)
                  ((cov (fun p : M => V (Fin.natAdd s b) p) x) (X x)) ∘
                Fin.natAdd s)) =
          (∑ a : Fin s,
            α x
              (Function.update (fun b : Fin s => V (Fin.castAdd q b) x) a
                ((cov (fun p : M => V (Fin.castAdd q a) p) x) (X x)))) *
            β x (fun b : Fin q => V (Fin.natAdd s b) x) +
          α x (fun a : Fin s => V (Fin.castAdd q a) x) *
            (∑ b : Fin q,
              β x
                (Function.update (fun c : Fin q => V (Fin.natAdd s c) x) b
                  ((cov (fun p : M => V (Fin.natAdd s b) p) x) (X x))))
    rw [hleft, hright]
  rw [hγ, hα, hβ]
  rw [hprod, hcorr]
  ring

/-- Product rule for a supplied total derivative of a tensor product.

The field `nablaProd` is allowed to be any smooth `(0, s + q + 1)` field whose
pointwise contraction is the usual Leibniz expression in the supplied total
derivatives of the two factors.  This separates the slot-normalization and
smoothness construction from the realization proof. -/
theorem TotalNabla0SRealizes.product_of_apply [T2Space M] [IsManifold I ⊤ M] {s q : ℕ}
    {cov : CovariantDerivative I E (TangentSpace I : M -> Type _)}
    {α : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s}
    {β : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) q}
    {nablaAlpha : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) (s + 1)}
    {nablaBeta : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) (q + 1)}
    {nablaProd : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) ((s + q) + 1)}
    (hα : TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) s cov α nablaAlpha)
    (hβ : TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) q cov β nablaBeta)
    (hprod :
      ∀ (X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
        (x : M) (slots : Fin (s + q) -> TangentSpace I x),
        nablaProd x (Fin.cons (X x) slots) =
          nablaAlpha x (Fin.cons (X x) (fun a : Fin s => slots (Fin.castAdd q a))) *
            β x (fun b : Fin q => slots (Fin.natAdd s b)) +
          α x (fun a : Fin s => slots (Fin.castAdd q a)) *
            nablaBeta x (Fin.cons (X x) (fun b : Fin q => slots (Fin.natAdd s b)))) :
    TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (s + q) cov
      (tensor0SField_product (𝕜 := Real) (E := E) (H := H)
        (I := I) (M := M) (∞ : WithTop ℕ∞) α β)
      nablaProd := by
  intro X x slots
  let V : Fin (s + q) -> ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M -> Type _) := fun a =>
    (ContMDiffSection.exists_eq_at
      (I := I) (F := E) (V := TangentSpace I)
      (n := (⊤ : ℕ∞)) x (slots a)).choose
  have hV_at : ∀ a : Fin (s + q), V a x = slots a := by
    intro a
    exact
      (ContMDiffSection.exists_eq_at
        (I := I) (F := E) (V := TangentSpace I)
        (n := (⊤ : ℕ∞)) x (slots a)).choose_spec
  have hEval := nabla0SFun_product_eval_smooth_slots
    (I := I) (s := s) (q := q) cov X V α β x
  calc
    nablaProd x (Fin.cons (X x) slots)
        = nablaAlpha x (Fin.cons (X x) (fun a : Fin s => slots (Fin.castAdd q a))) *
            β x (fun b : Fin q => slots (Fin.natAdd s b)) +
          α x (fun a : Fin s => slots (Fin.castAdd q a)) *
            nablaBeta x (Fin.cons (X x) (fun b : Fin q => slots (Fin.natAdd s b))) := by
          exact hprod X x slots
    _ = (nabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
            s cov X α x) (fun a : Fin s => slots (Fin.castAdd q a)) *
          β x (fun b : Fin q => slots (Fin.natAdd s b)) +
        α x (fun a : Fin s => slots (Fin.castAdd q a)) *
          (nabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
            q cov X β x) (fun b : Fin q => slots (Fin.natAdd s b)) := by
          rw [hα.apply X x (fun a : Fin s => slots (Fin.castAdd q a)),
            hβ.apply X x (fun b : Fin q => slots (Fin.natAdd s b))]
    _ = (nabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
          (s + q) cov X
          (tensor0SField_product (𝕜 := Real) (E := E) (H := H)
            (I := I) (M := M) (∞ : WithTop ℕ∞) α β) x) slots := by
          simpa [V, hV_at] using hEval.symm

/-- Reindex `(∇α) ⊗ β` so the derivative slot is the leading slot of the
product derivative. -/
noncomputable def productDerivLeftPerm (s q : ℕ) :
    Fin ((s + 1) + q) ≃ Fin ((s + q) + 1) :=
  finCongr (by omega)

/-- Reindex `α ⊗ (∇β)` so the derivative slot of `∇β` is moved to the
leading slot of the product derivative. -/
noncomputable def productDerivRightPerm (s q : ℕ) :
    Fin (s + (q + 1)) ≃ Fin ((s + q) + 1) :=
  (finCongr (by omega : s + (q + 1) = (s + q) + 1)).trans
    (Fin.cycleRange ⟨s, by omega⟩)

/-- Left Leibniz term for the total derivative of a tensor product. -/
noncomputable def tensor0SField_productDerivLeft [IsManifold I ⊤ M] {s q : ℕ}
    (nablaAlpha : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) (s + 1))
    (β : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) q) :
    Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) ((s + q) + 1) :=
  tensor0SField_permute (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
    (∞ : WithTop ℕ∞) (productDerivLeftPerm s q)
    (tensor0SField_product (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (∞ : WithTop ℕ∞) nablaAlpha β)

/-- Right Leibniz term for the total derivative of a tensor product. -/
noncomputable def tensor0SField_productDerivRight [IsManifold I ⊤ M] {s q : ℕ}
    (α : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s)
    (nablaBeta : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) (q + 1)) :
    Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) ((s + q) + 1) :=
  tensor0SField_permute (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
    (∞ : WithTop ℕ∞) (productDerivRightPerm s q)
    (tensor0SField_product (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (∞ : WithTop ℕ∞) α nablaBeta)

/-- The Leibniz total derivative field for a tensor product. -/
noncomputable def tensor0SField_productDeriv [IsManifold I ⊤ M] {s q : ℕ}
    (α : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s)
    (β : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) q)
    (nablaAlpha : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) (s + 1))
    (nablaBeta : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) (q + 1)) :
    Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) ((s + q) + 1) :=
  tensor0SField_productDerivLeft (I := I) (M := M) nablaAlpha β +
    tensor0SField_productDerivRight (I := I) (M := M) α nablaBeta

private theorem productDerivLeftPerm_zero {s q : ℕ} :
    productDerivLeftPerm s q (Fin.castAdd q (0 : Fin (s + 1))) =
      (0 : Fin ((s + q) + 1)) := by
  ext
  simp [productDerivLeftPerm]

private theorem productDerivLeftPerm_succ {s q : ℕ} (a : Fin s) :
    productDerivLeftPerm s q (Fin.castAdd q a.succ) =
      (Fin.castAdd q a).succ := by
  ext
  simp [productDerivLeftPerm]

private theorem productDerivLeftPerm_right {s q : ℕ} (b : Fin q) :
    productDerivLeftPerm s q (Fin.natAdd (s + 1) b) =
      (Fin.natAdd s b).succ := by
  ext
  simp [productDerivLeftPerm, Fin.val_natAdd]
  omega

private theorem productDerivRightPerm_left {s q : ℕ} (a : Fin s) :
    productDerivRightPerm s q (Fin.castAdd (q + 1) a) =
      (Fin.castAdd q a).succ := by
  ext
  rw [productDerivRightPerm]
  change (Fin.cycleRange (⟨s, by omega⟩ : Fin ((s + q) + 1))
      (finCongr (by omega : s + (q + 1) = (s + q) + 1)
        (Fin.castAdd (q + 1) a))).val =
    ((Fin.castAdd q a).succ).val
  have hlt : (finCongr (by omega : s + (q + 1) = (s + q) + 1)
      (Fin.castAdd (q + 1) a)) < (⟨s, by omega⟩ : Fin ((s + q) + 1)) := by
    rw [Fin.lt_def]
    change a.val < s
    exact a.is_lt
  rw [Fin.coe_cycleRange_of_lt hlt]
  change a.val + 1 = a.val + 1
  rfl

private theorem productDerivRightPerm_zero {s q : ℕ} :
    productDerivRightPerm s q (Fin.natAdd s (0 : Fin (q + 1))) =
      (0 : Fin ((s + q) + 1)) := by
  ext
  rw [productDerivRightPerm]
  change (Fin.cycleRange (⟨s, by omega⟩ : Fin ((s + q) + 1))
      (finCongr (by omega : s + (q + 1) = (s + q) + 1)
        (Fin.natAdd s (0 : Fin (q + 1))))).val = 0
  have heq : finCongr (by omega : s + (q + 1) = (s + q) + 1)
      (Fin.natAdd s (0 : Fin (q + 1))) =
      (⟨s, by omega⟩ : Fin ((s + q) + 1)) := by
    ext
    change s = s
    rfl
  rw [heq, Fin.cycleRange_self]
  rfl

private theorem productDerivRightPerm_succ {s q : ℕ} (b : Fin q) :
    productDerivRightPerm s q (Fin.natAdd s b.succ) =
      (Fin.natAdd s b).succ := by
  ext
  rw [productDerivRightPerm]
  change (Fin.cycleRange (⟨s, by omega⟩ : Fin ((s + q) + 1))
      (finCongr (by omega : s + (q + 1) = (s + q) + 1)
        (Fin.natAdd s b.succ))).val =
    ((Fin.natAdd s b).succ).val
  have hgt : (⟨s, by omega⟩ : Fin ((s + q) + 1)) <
      finCongr (by omega : s + (q + 1) = (s + q) + 1) (Fin.natAdd s b.succ) := by
    rw [Fin.lt_def]
    change s < s + (b.val + 1)
    omega
  rw [Fin.cycleRange_of_gt hgt]
  change s + b.val + 1 = s + b.val + 1
  rfl

/-- Extend a covariant slot permutation by fixing a new leading derivative slot. -/
noncomputable def leadingSlotPerm {s q : ℕ} (e : Fin s ≃ Fin q) :
    Fin (s + 1) ≃ Fin (q + 1) where
  toFun i := Fin.cases (0 : Fin (q + 1)) (fun a : Fin s => (e a).succ) i
  invFun j := Fin.cases (0 : Fin (s + 1)) (fun b : Fin q => (e.symm b).succ) j
  left_inv := by
    intro i
    ext
    refine Fin.cases (by simp) (fun a => ?_) i
    simp
  right_inv := by
    intro j
    ext
    refine Fin.cases (by simp) (fun b => ?_) j
    simp

@[simp]
theorem leadingSlotPerm_zero {s q : ℕ} (e : Fin s ≃ Fin q) :
    leadingSlotPerm e (0 : Fin (s + 1)) = (0 : Fin (q + 1)) := rfl

@[simp]
theorem leadingSlotPerm_succ {s q : ℕ} (e : Fin s ≃ Fin q) (a : Fin s) :
    leadingSlotPerm e a.succ = (e a).succ := rfl

/-- Iterate `leadingSlotPerm` through `k` total covariant derivatives.

This is the slot bookkeeping needed when a tensor field is first permuted and
then differentiated repeatedly: each total derivative adds one new leading
slot which should be fixed by the old permutation. -/
noncomputable def iterLeadingSlotPerm {s q : ℕ} (e : Fin s ≃ Fin q) :
    (k : ℕ) -> Fin (s + k) ≃ Fin (q + k)
  | 0 =>
      (finCongr (by omega : s + 0 = s)).trans
        (e.trans (finCongr (by omega : q = q + 0)))
  | k + 1 =>
      (finCongr (by omega : s + (k + 1) = (s + k) + 1)).trans
        ((leadingSlotPerm (iterLeadingSlotPerm e k)).trans
          (finCongr (by omega : (q + k) + 1 = q + (k + 1))))

set_option linter.unusedSectionVars false in
theorem tensor0SField_permute_leading_apply_cons [IsManifold I ⊤ M] {s q : ℕ}
    (e : Fin s ≃ Fin q)
    (α : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) (s + 1))
    (x : M) (v : TangentSpace I x) (slots : Fin q -> TangentSpace I x) :
    tensor0SField_permute (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        (∞ : WithTop ℕ∞) (leadingSlotPerm e) α x (Fin.cons v slots) =
      α x (Fin.cons v (fun a : Fin s => slots (e a))) := by
  simp only [tensor0SField_permute_apply, ContinuousMultilinearMap.domDomCongr_apply]
  congr 1
  funext a
  refine Fin.cases ?zero ?succ a
  · rfl
  · intro a
    rfl

set_option linter.unusedSectionVars false in
theorem nabla0SFun_permute_eval_smooth_slots [T2Space M] [IsManifold I ⊤ M] {s q : ℕ}
    (e : Fin s ≃ Fin q)
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (V : Fin q -> ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M -> Type _))
    (α : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s)
    (x : M) :
    (nabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        q cov X
        (tensor0SField_permute (𝕜 := Real) (E := E) (H := H)
          (I := I) (M := M) (∞ : WithTop ℕ∞) e α) x)
      (fun b : Fin q => V b x) =
      (nabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
          s cov X α x) (fun a : Fin s => V (e a) x) := by
  classical
  let Vα : Fin s -> ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M -> Type _) := fun a => V (e a)
  have hperm := nabla0SFun_eval_smooth_slots (I := I) cov X V
    (tensor0SField_permute (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (∞ : WithTop ℕ∞) e α) x
  have hα := nabla0SFun_eval_smooth_slots (I := I) cov X Vα α x
  rw [hperm, hα]
  have hscalar :
      (fun p : M =>
        tensor0SField_permute (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
          (∞ : WithTop ℕ∞) e α p (fun b : Fin q => V b p)) =
        (fun p : M => α p (fun a : Fin s => V (e a) p)) := by
    funext p
    simp [tensor0SField_permute_apply, ContinuousMultilinearMap.domDomCongr_apply]
  rw [hscalar]
  have hsum :
      (∑ b : Fin q,
        tensor0SField_permute (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
          (∞ : WithTop ℕ∞) e α x
          (Function.update (fun b : Fin q => V b x) b
            ((cov (fun p : M => V b p) x) (X x)))) =
        ∑ a : Fin s,
          α x
          (Function.update (fun a : Fin s => V (e a) x) a
              ((cov (fun p : M => V (e a) p) x) (X x))) := by
    symm
    refine Fintype.sum_equiv e
      (fun a : Fin s =>
        α x
          (Function.update (fun a : Fin s => V (e a) x) a
            ((cov (fun p : M => V (e a) p) x) (X x))))
      (fun b : Fin q =>
        tensor0SField_permute (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
          (∞ : WithTop ℕ∞) e α x
          (Function.update (fun b : Fin q => V b x) b
            ((cov (fun p : M => V b p) x) (X x)))) ?_
    intro a
    simp only [tensor0SField_permute_apply, ContinuousMultilinearMap.domDomCongr_apply]
    congr 1
    funext c
    by_cases hca : c = a
    · subst c
      simp
    · have hne : e c ≠ e a := fun h => hca (e.injective h)
      simp [Function.update_of_ne, hca, hne]
  rw [hsum]

set_option linter.unusedSectionVars false in
theorem tensor0SModelInChart_permute_top [IsManifold I ⊤ M] {s q : ℕ} (e : Fin s ≃ Fin q)
    (x₀ : M)
    (α : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s)
    (y : E) :
    tensor0SModelInChart (𝕜 := Real) (E := E) (H := H)
        (I := I) (M := M) q x₀
        (fun x : M =>
          tensor0SField_permute (𝕜 := Real) (E := E) (H := H)
            (I := I) (M := M) (∞ : WithTop ℕ∞) e α x) y =
      tensor0SModelDomDomCongrL (𝕜 := Real) (E := E) e
        (tensor0SModelInChart (𝕜 := Real) (E := E) (H := H)
          (I := I) (M := M) s x₀ (fun x : M => α x) y) := by
  apply ContinuousMultilinearMap.ext
  intro slots
  simp [tensor0SModelInChart_apply, tensor0SField_permute_apply,
    ContinuousMultilinearMap.domDomCongr_apply]

set_option linter.unusedSectionVars false in
theorem fixedChartNabla0SModel_permute_top_apply_slots [IsManifold I ⊤ M] {s q : ℕ}
    (e : Fin s ≃ Fin q)
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (α : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s)
    (x : M) (slots : Fin q -> E) :
    fixedChartNabla0SModel (𝕜 := Real) (E := E) (H := H)
        (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) q cov X
        (tensor0SField_permute (𝕜 := Real) (E := E) (H := H)
          (I := I) (M := M) (∞ : WithTop ℕ∞) e α)
        x (extChartAt I x x) slots =
      fixedChartNabla0SModel (𝕜 := Real) (E := E) (H := H)
        (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) s cov X α
        x (extChartAt I x x) (fun a : Fin s => slots (e a)) := by
  classical
  unfold fixedChartNabla0SModel covariantDeriv_tensor0SModelWithin
  rw [tensor0SModelInChart_permute_top (I := I) (M := M) e x α (extChartAt I x x)]
  refine covariantDeriv_tensor0SModelAt_domDomCongr_apply_slots
    (𝕜 := Real) (E := E) e
    (fderivWithin Real
      (tensor0SModelInChart (𝕜 := Real) (E := E) (H := H)
        (I := I) (M := M) s x (fun x : M => α x))
      (range I) (extChartAt I x x)
      (VectorField.mpullbackWithin 𝓘(Real, E) I (extChartAt I x).symm X (range I)
        (extChartAt I x x)))
    (fderivWithin Real
      (fun z : E =>
        tensor0SModelDomDomCongrL (𝕜 := Real) (E := E) e
          (tensor0SModelInChart (𝕜 := Real) (E := E) (H := H)
            (I := I) (M := M) s x (fun x : M => α x) z))
      (range I) (extChartAt I x x)
      (VectorField.mpullbackWithin 𝓘(Real, E) I (extChartAt I x).symm X (range I)
        (extChartAt I x x)))
    (connectionEndomorphismInChart (𝕜 := Real) (I := I) cov (fun x => X x) x
      (extChartAt I x x))
    (tensor0SModelInChart (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) s x (fun x : M => α x) (extChartAt I x x))
    ?_ slots
  intro τ
  let A : E -> Tensor0SModel (𝕜 := Real) (E := E) s :=
    tensor0SModelInChart (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) s x (fun x : M => α x)
  have hA : DifferentiableWithinAt Real A (range I) (extChartAt I x x) := by
    exact tensor0SModelInChart_differentiableWithinAt_center_of_contMDiffAt
      (I := I) α x (α.contMDiff x)
  have hRange : extChartAt I x x ∈ range I :=
    extChartAt_target_subset_range x (mem_extChartAt_target (I := I) x)
  have hderiv := fderivWithin_tensor0SModelDomDomCongrL_apply
    (𝕜 := Real) (E := E) e A hA (I.uniqueDiffOn (extChartAt I x x) hRange)
  have hfun :
      (fun z : E =>
        tensor0SModelDomDomCongrL (𝕜 := Real) (E := E) e (A z)) =
      (fun z : E =>
        tensor0SModelDomDomCongrL (𝕜 := Real) (E := E) e
          (tensor0SModelInChart (𝕜 := Real) (E := E) (H := H)
            (I := I) (M := M) s x (fun x : M => α x) z)) := rfl
  rw [← hfun, hderiv]
  simp [A, tensor0SModelDomDomCongrL_apply, ContinuousMultilinearMap.domDomCongr_apply]

set_option linter.unusedSectionVars false in
theorem nabla0SFun_permute_apply [IsManifold I ⊤ M] {s q : ℕ}
    (e : Fin s ≃ Fin q)
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (α : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s)
    (x : M) (slots : Fin q -> TangentSpace I x) :
    (nabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        q cov X
        (tensor0SField_permute (𝕜 := Real) (E := E) (H := H)
          (I := I) (M := M) (∞ : WithTop ℕ∞) e α) x) slots =
      (nabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        s cov X α x) (fun a : Fin s => slots (e a)) := by
  let tr := trivializationAt E (TangentSpace I : M -> Type _) x
  let slotsModel : Fin q -> E :=
    fun b => tr.continuousLinearMapAt Real x (slots b)
  have hslotsQ :
      (fun b : Fin q =>
        tangentConstInChart (𝕜 := Real) (I := I) x (slotsModel b) x) = slots := by
    funext b
    change
      tangentConstInChart (𝕜 := Real) (I := I) x
          ((trivializationAt E (TangentSpace I : M -> Type _) x).continuousLinearMapAt
            Real x (slots b)) x =
        slots b
    exact tangentConstInChart_self_continuousLinearMapAt
      (𝕜 := Real) (I := I) x (slots b)
  have hslotsS :
      (fun a : Fin s =>
        tangentConstInChart (𝕜 := Real) (I := I) x (slotsModel (e a)) x) =
        (fun a : Fin s => slots (e a)) := by
    funext a
    change
      tangentConstInChart (𝕜 := Real) (I := I) x
          ((trivializationAt E (TangentSpace I : M -> Type _) x).continuousLinearMapAt
            Real x (slots (e a))) x =
        slots (e a)
    exact tangentConstInChart_self_continuousLinearMapAt
      (𝕜 := Real) (I := I) x (slots (e a))
  have hselfQ := nabla0SFun_apply_selfChart_slots
    (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
    q cov X
    (tensor0SField_permute (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (∞ : WithTop ℕ∞) e α) x slotsModel
  have hselfS := nabla0SFun_apply_selfChart_slots
    (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
    s cov X α x (fun a : Fin s => slotsModel (e a))
  calc
    (nabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        q cov X
        (tensor0SField_permute (𝕜 := Real) (E := E) (H := H)
          (I := I) (M := M) (∞ : WithTop ℕ∞) e α) x) slots
        =
      fixedChartNabla0SModel (𝕜 := Real) (E := E) (H := H)
        (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) q cov X
        (tensor0SField_permute (𝕜 := Real) (E := E) (H := H)
          (I := I) (M := M) (∞ : WithTop ℕ∞) e α)
        x (extChartAt I x x) slotsModel := by
          rw [← hslotsQ]
          exact hselfQ
    _ =
      fixedChartNabla0SModel (𝕜 := Real) (E := E) (H := H)
        (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) s cov X α
        x (extChartAt I x x) (fun a : Fin s => slotsModel (e a)) := by
          exact fixedChartNabla0SModel_permute_top_apply_slots
            (I := I) (M := M) e cov X α x slotsModel
    _ =
      (nabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        s cov X α x) (fun a : Fin s => slots (e a)) := by
          rw [← hslotsS]
          exact hselfS.symm

set_option linter.unusedSectionVars false in
theorem TotalNabla0SRealizes.permute [IsManifold I ⊤ M] {s q : ℕ}
    (e : Fin s ≃ Fin q)
    {cov : CovariantDerivative I E (TangentSpace I : M -> Type _)}
    {α : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s}
    {nablaAlpha : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) (s + 1)}
    (hα : TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) s cov α nablaAlpha) :
    TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      q cov
      (tensor0SField_permute (𝕜 := Real) (E := E) (H := H)
        (I := I) (M := M) (∞ : WithTop ℕ∞) e α)
      (tensor0SField_permute (𝕜 := Real) (E := E) (H := H)
        (I := I) (M := M) (∞ : WithTop ℕ∞) (leadingSlotPerm e) nablaAlpha) := by
  intro X x slots
  calc
    tensor0SField_permute (𝕜 := Real) (E := E) (H := H)
        (I := I) (M := M) (∞ : WithTop ℕ∞) (leadingSlotPerm e) nablaAlpha x
        (Fin.cons (X x) slots)
        =
      nablaAlpha x (Fin.cons (X x) (fun a : Fin s => slots (e a))) := by
        exact tensor0SField_permute_leading_apply_cons (I := I) (M := M)
          e nablaAlpha x (X x) slots
    _ =
      (nabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        s cov X α x) (fun a : Fin s => slots (e a)) := by
        exact hα.apply X x (fun a : Fin s => slots (e a))
    _ =
      (nabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        q cov X
        (tensor0SField_permute (𝕜 := Real) (E := E) (H := H)
          (I := I) (M := M) (∞ : WithTop ℕ∞) e α) x) slots := by
        exact (nabla0SFun_permute_apply (I := I) (M := M) e cov X α x slots).symm

/-- Slot permutations commute with a full covariant derivative jet.  The
permutation is extended by fixing every leading derivative slot. -/
noncomputable def IterNabla0SJet.permute [IsManifold I ⊤ M] {s q : ℕ}
    (e : Fin s ≃ Fin q)
    {cov : CovariantDerivative I E (TangentSpace I : M -> Type _)}
    {α : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s}
    (J : IterNabla0SJet (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      cov α) :
    IterNabla0SJet (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      cov
      (tensor0SField_permute (𝕜 := Real) (E := E) (H := H)
        (I := I) (M := M) (∞ : WithTop ℕ∞) e α) where
  term k :=
    tensor0SField_permute (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (∞ : WithTop ℕ∞) (iterLeadingSlotPerm e k)
      (J.term k)
  zero_eq := by
    ext x slots
    simp [tensor0SField_permute_apply, ContinuousMultilinearMap.domDomCongr_apply,
      iterLeadingSlotPerm, J.zero_eq]
  step k := by
    exact TotalNabla0SRealizes.permute (I := I) (M := M)
      (iterLeadingSlotPerm e k) (J.step k)

/-- Recursive Leibniz product field associated to two covariant derivative
jets.

The `k`-th term is the finite binary Leibniz tree obtained by differentiating
`α ⊗ β` `k` times, with derivative slots normalized to the front.  This is the
field-level object needed before proving the all-order product realization
theorem used in MSM135 Lemma 4.5. -/
noncomputable def tensor0SField_productJetTerm [IsManifold I ⊤ M] {s q : ℕ}
    {cov : CovariantDerivative I E (TangentSpace I : M -> Type _)}
    {α : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s}
    {β : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) q}
    (Jα : IterNabla0SJet (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      cov α)
    (Jβ : IterNabla0SJet (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      cov β) :
    (k : ℕ) ->
      Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        (n := (∞ : WithTop ℕ∞)) ((s + q) + k)
  | 0 =>
      tensor0SFieldCast (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        (by omega : s + q = (s + q) + 0)
        (tensor0SField_product (𝕜 := Real) (E := E) (H := H)
          (I := I) (M := M) (∞ : WithTop ℕ∞) α β)
  | k + 1 =>
      tensor0SFieldCast (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        (by omega : ((s + q) + 1) + k = (s + q) + (k + 1))
        (tensor0SField_permute (𝕜 := Real) (E := E) (H := H)
            (I := I) (M := M) (∞ : WithTop ℕ∞)
            (iterLeadingSlotPerm (productDerivLeftPerm s q) k)
            (tensor0SField_productJetTerm
              (IterNabla0SJet.tail (𝕜 := Real) (E := E) (H := H)
                (I := I) (M := M) Jα) Jβ k) +
          tensor0SField_permute (𝕜 := Real) (E := E) (H := H)
            (I := I) (M := M) (∞ : WithTop ℕ∞)
            (iterLeadingSlotPerm (productDerivRightPerm s q) k)
            (tensor0SField_productJetTerm Jα
              (IterNabla0SJet.tail (𝕜 := Real) (E := E) (H := H)
                (I := I) (M := M) Jβ) k))

set_option linter.unusedSectionVars false in
theorem tensor0SField_productDerivLeft_apply_cons [IsManifold I ⊤ M] {s q : ℕ}
    (nablaAlpha : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) (s + 1))
    (β : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) q)
    (x : M) (v : TangentSpace I x) (slots : Fin (s + q) -> TangentSpace I x) :
    tensor0SField_productDerivLeft (I := I) (M := M) nablaAlpha β x
        (Fin.cons v slots) =
      nablaAlpha x (Fin.cons v (fun a : Fin s => slots (Fin.castAdd q a))) *
        β x (fun b : Fin q => slots (Fin.natAdd s b)) := by
  simp only [tensor0SField_productDerivLeft, tensor0SField_permute_apply,
    tensor0SField_product_apply, ContinuousMultilinearMap.domDomCongr_apply,
    Bundle.continuousMultilinearMap.product_fun_apply]
  congr 2
  · funext a
    refine Fin.cases ?zero ?succ a
    · simp [productDerivLeftPerm_zero]
    · intro a
      simp [productDerivLeftPerm_succ]
  · funext b
    simp [productDerivLeftPerm_right]

set_option linter.unusedSectionVars false in
theorem tensor0SField_productDerivRight_apply_cons [IsManifold I ⊤ M] {s q : ℕ}
    (α : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s)
    (nablaBeta : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) (q + 1))
    (x : M) (v : TangentSpace I x) (slots : Fin (s + q) -> TangentSpace I x) :
    tensor0SField_productDerivRight (I := I) (M := M) α nablaBeta x
        (Fin.cons v slots) =
      α x (fun a : Fin s => slots (Fin.castAdd q a)) *
        nablaBeta x (Fin.cons v (fun b : Fin q => slots (Fin.natAdd s b))) := by
  simp only [tensor0SField_productDerivRight, tensor0SField_permute_apply,
    tensor0SField_product_apply, ContinuousMultilinearMap.domDomCongr_apply,
    Bundle.continuousMultilinearMap.product_fun_apply]
  congr 2
  · funext a
    simp [productDerivRightPerm_left]
  · funext b
    refine Fin.cases ?zero ?succ b
    · simp [productDerivRightPerm_zero]
    · intro b
      simp [productDerivRightPerm_succ]

theorem tensor0SField_productDeriv_apply_cons [IsManifold I ⊤ M] {s q : ℕ}
    (α : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s)
    (β : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) q)
    (nablaAlpha : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) (s + 1))
    (nablaBeta : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) (q + 1))
    (x : M) (v : TangentSpace I x) (slots : Fin (s + q) -> TangentSpace I x) :
    tensor0SField_productDeriv (I := I) (M := M) α β nablaAlpha nablaBeta x
        (Fin.cons v slots) =
      nablaAlpha x (Fin.cons v (fun a : Fin s => slots (Fin.castAdd q a))) *
        β x (fun b : Fin q => slots (Fin.natAdd s b)) +
      α x (fun a : Fin s => slots (Fin.castAdd q a)) *
        nablaBeta x (Fin.cons v (fun b : Fin q => slots (Fin.natAdd s b))) := by
  simp [tensor0SField_productDeriv, tensor0SField_productDerivLeft_apply_cons,
    tensor0SField_productDerivRight_apply_cons]

/-- The tensor product of two total-derivative realizations realizes the
Leibniz total derivative field of the tensor product. -/
theorem TotalNabla0SRealizes.product [T2Space M] [IsManifold I ⊤ M] {s q : ℕ}
    {cov : CovariantDerivative I E (TangentSpace I : M -> Type _)}
    {α : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s}
    {β : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) q}
    {nablaAlpha : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) (s + 1)}
    {nablaBeta : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) (q + 1)}
    (hα : TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) s cov α nablaAlpha)
    (hβ : TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) q cov β nablaBeta) :
    TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (s + q) cov
      (tensor0SField_product (𝕜 := Real) (E := E) (H := H)
        (I := I) (M := M) (∞ : WithTop ℕ∞) α β)
      (tensor0SField_productDeriv (I := I) (M := M) α β nablaAlpha nablaBeta) := by
  refine TotalNabla0SRealizes.product_of_apply (I := I) hα hβ ?_
  intro X x slots
  exact tensor0SField_productDeriv_apply_cons (I := I) (M := M)
    α β nablaAlpha nablaBeta x (X x) slots

/-- The recursive Leibniz product field starts with the checked first product
rule.  This is the base case for the future all-order product-jet theorem. -/
theorem tensor0SField_productJetTerm_step_zero [T2Space M] [IsManifold I ⊤ M] {s q : ℕ}
    {cov : CovariantDerivative I E (TangentSpace I : M -> Type _)}
    {α : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s}
    {β : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) q}
    (Jα : IterNabla0SJet (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      cov α)
    (Jβ : IterNabla0SJet (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      cov β) :
    TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (s + q) cov
      (tensor0SField_productJetTerm (I := I) (M := M) Jα Jβ 0)
      (tensor0SField_productJetTerm (I := I) (M := M) Jα Jβ 1) := by
  have hα : TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) s cov α (Jα.term 1) :=
    IterNabla0SRealizes.one (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (IterNabla0SJet.realizes (𝕜 := Real) (E := E) (H := H)
        (I := I) (M := M) (k := 1) Jα)
  have hβ : TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) q cov β (Jβ.term 1) :=
    IterNabla0SRealizes.one (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (IterNabla0SJet.realizes (𝕜 := Real) (E := E) (H := H)
        (I := I) (M := M) (k := 1) Jβ)
  refine TotalNabla0SRealizes.congr (𝕜 := Real) (E := E) (H := H)
    (I := I) (M := M) ?hsource ?htarget
    (TotalNabla0SRealizes.product (I := I) (M := M)
      (s := s) (q := q) hα hβ)
  · simp [tensor0SField_productJetTerm, tensor0SFieldCast]
  · ext x slots
    simp [tensor0SField_productJetTerm, tensor0SField_productDeriv,
      tensor0SField_productDerivLeft, tensor0SField_productDerivRight,
      tensor0SFieldCast, tensor0SField_permute_apply, iterLeadingSlotPerm,
      ContinuousMultilinearMap.domDomCongr_apply]

/-- Total derivative realization for the left Leibniz summand
`(∇α) ⊗ β`, after the derivative slot has been normalized. -/
theorem TotalNabla0SRealizes.productDerivLeft [T2Space M] [IsManifold I ⊤ M] {s q : ℕ}
    {cov : CovariantDerivative I E (TangentSpace I : M -> Type _)}
    {β : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) q}
    {nablaAlpha : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) (s + 1)}
    {nablaBeta : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) (q + 1)}
    {nablaAlpha1 : Tensor0SField (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) ((s + 1) + 1)}
    (hα : TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (s + 1) cov nablaAlpha nablaAlpha1)
    (hβ : TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) q cov β nablaBeta) :
    TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      ((s + q) + 1) cov
      (tensor0SField_productDerivLeft (I := I) (M := M) nablaAlpha β)
      (tensor0SField_permute (𝕜 := Real) (E := E) (H := H)
        (I := I) (M := M) (∞ : WithTop ℕ∞)
        (leadingSlotPerm (productDerivLeftPerm s q))
        (tensor0SField_productDeriv (I := I) (M := M)
          nablaAlpha β nablaAlpha1 nablaBeta)) := by
  have hprod := TotalNabla0SRealizes.product (I := I) (M := M)
    (s := s + 1) (q := q) hα hβ
  exact TotalNabla0SRealizes.permute (I := I) (M := M)
    (productDerivLeftPerm s q) hprod

/-- Total derivative realization for the right Leibniz summand
`α ⊗ (∇β)`, after the derivative slot has been normalized. -/
theorem TotalNabla0SRealizes.productDerivRight [T2Space M] [IsManifold I ⊤ M] {s q : ℕ}
    {cov : CovariantDerivative I E (TangentSpace I : M -> Type _)}
    {α : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s}
    {nablaAlpha : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) (s + 1)}
    {nablaBeta : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) (q + 1)}
    {nablaBeta1 : Tensor0SField (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) ((q + 1) + 1)}
    (hα : TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) s cov α nablaAlpha)
    (hβ : TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (q + 1) cov nablaBeta nablaBeta1) :
    TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      ((s + q) + 1) cov
      (tensor0SField_productDerivRight (I := I) (M := M) α nablaBeta)
      (tensor0SField_permute (𝕜 := Real) (E := E) (H := H)
        (I := I) (M := M) (∞ : WithTop ℕ∞)
        (leadingSlotPerm (productDerivRightPerm s q))
        (tensor0SField_productDeriv (I := I) (M := M)
          α nablaBeta nablaAlpha nablaBeta1)) := by
  have hprod := TotalNabla0SRealizes.product (I := I) (M := M)
    (s := s) (q := q + 1) hα hβ
  exact TotalNabla0SRealizes.permute (I := I) (M := M)
    (productDerivRightPerm s q) hprod

/-- Order-one normalized iterated derivative realization for a tensor
product.  This is the first checked case of the Leibniz tower needed for
Lemma 4.5. -/
theorem IterNabla0SRealizes.product_one [T2Space M] [IsManifold I ⊤ M] {s q : ℕ}
    {cov : CovariantDerivative I E (TangentSpace I : M -> Type _)}
    {α : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s}
    {β : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) q}
    {α1 : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) (s + 1)}
    {β1 : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) (q + 1)}
    (hα : IterNabla0SRealizes (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) cov α 1 α1)
    (hβ : IterNabla0SRealizes (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) cov β 1 β1) :
    IterNabla0SRealizes (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      cov
      (tensor0SField_product (𝕜 := Real) (E := E) (H := H)
        (I := I) (M := M) (∞ : WithTop ℕ∞) α β)
      1
      (tensor0SField_productDeriv (I := I) (M := M) α β α1 β1) := by
  refine IterNabla0SRealizes.succ IterNabla0SRealizes.zero ?_
  have hαtot : TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) s cov α α1 :=
    IterNabla0SRealizes.one (I := I) hα
  have hβtot : TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) q cov β β1 :=
    IterNabla0SRealizes.one (I := I) hβ
  exact TotalNabla0SRealizes.product (I := I) (M := M) (s := s) (q := q)
    (cov := cov) (α := α) (β := β) (nablaAlpha := α1) (nablaBeta := β1)
    hαtot hβtot

/-- The directional covariant derivative of mixed tensor fields is additive in
the tensor argument.  The proof extends the fixed upper input and lower slots
to smooth local sections, then applies the raw moving-slot additivity theorem. -/
theorem nablaRSFun_add [T2Space M] {r s : ℕ}
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _))
    (T U : TensorRSField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) r s)
    (x : M) :
    nablaRSFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        r s cov X (T + U) x =
      nablaRSFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
          r s cov X T x +
        nablaRSFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
          r s cov X U x := by
  classical
  letI := tensor0SBundle_topology (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) r
  letI := tensor0SBundle_fiber (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) r
  letI := tensor0SBundle_vector (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) r
  letI := tensor0SBundle_smooth (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
    (n := (∞ : WithTop ℕ∞)) r
  let basis : Module.Basis (Fin (Module.finrank Real (TangentSpace I x))) Real
      (TangentSpace I x) :=
    Module.finBasis Real (TangentSpace I x)
  apply extRS_basis (I := I) basis
  intro upper lower
  let βsec : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) r :=
    (ContMDiffSection.exists_eq_at
      (I := I) (F := Tensor0SModel r Real E)
      (V := fun y : M => Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I)
        (M := M) r y)
      (n := (⊤ : ℕ∞)) x (basisTensor0S (I := I) basis upper)).choose
  have hβ_at : βsec x = basisTensor0S (I := I) basis upper := by
    exact
      (ContMDiffSection.exists_eq_at
        (I := I) (F := Tensor0SModel r Real E)
        (V := fun y : M => Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I)
          (M := M) r y)
        (n := (⊤ : ℕ∞)) x (basisTensor0S (I := I) basis upper)).choose_spec
  let V : Fin s → ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M → Type _) :=
    fun a =>
      (ContMDiffSection.exists_eq_at
        (I := I) (F := E) (V := TangentSpace I) (n := (⊤ : ℕ∞))
        x (basis (lower a))).choose
  have hV_at : ∀ a : Fin s, V a x = basis (lower a) := by
    intro a
    exact
      (ContMDiffSection.exists_eq_at
        (I := I) (F := E) (V := TangentSpace I) (n := (⊤ : ℕ∞))
        x (basis (lower a))).choose_spec
  have hpairT : MDifferentiableAt I 𝓘(Real, Real)
      (fun p : M => (T p (βsec p)) (fun a : Fin s => V a p)) x :=
    (tensorRSField_eval_smooth_input_slots_contMDiffAt (I := I)
      T βsec V x).mdifferentiableAt (by simp)
  have hpairU : MDifferentiableAt I 𝓘(Real, Real)
      (fun p : M => (U p (βsec p)) (fun a : Fin s => V a p)) x :=
    (tensorRSField_eval_smooth_input_slots_contMDiffAt (I := I)
      U βsec V x).mdifferentiableAt (by simp)
  have hβmodel : DifferentiableWithinAt Real
      (tensor0SModelInChart (𝕜 := Real) (E := E) (H := H) (I := I)
        (M := M) r x (fun p : M => βsec p))
      (Set.range I) (extChartAt I x x) := by
    exact tensor0SModelInChart_differentiableWithinAt_center_of_contMDiffAt
      (I := I) βsec x (βsec.contMDiff x)
  have hV : ∀ a : Fin s, MDiffAt (T% (fun p : M => V a p)) x := by
    intro a
    exact (V a).contMDiff.contMDiffAt.mdifferentiableAt (by simp)
  have hVmodel : ∀ a : Fin s,
      DifferentiableWithinAt Real
        (tangentFieldModelInChart (𝕜 := Real) (I := I) x (fun p : M => V a p))
        (Set.range I) (extChartAt I x x) := by
    intro a
    exact tangentFieldModelInChart_differentiableWithinAt_center_of_contMDiffAt
      (I := I) (fun p : M => V a p) x ((V a).contMDiff.contMDiffAt)
  have hcoord : ∀ a : Fin s, ∀ i : Fin (Module.finrank Real E),
      MDifferentiableAt I 𝓘(Real, Real)
        (fun p : M =>
          (Module.finBasis Real E).coord i
            (tangentFieldModelInChart (𝕜 := Real) (I := I) x (fun q : M => V a q)
              (extChartAt I x p))) x := by
    intro a i
    exact tangentFieldModelInChart_coord_mdiffAt_center_of_contMDiffAt
      (I := I) (fun p : M => V a p) x ((V a).contMDiff.contMDiffAt) i
  have hraw := nablaRSFun_add_raw
    (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
    (r := r) (s := s) cov X T U (fun p : M => βsec p)
    (fun a : Fin s => fun p : M => V a p) x
    hpairT hpairU hβmodel hV hVmodel hcoord
  simp only [componentRS_apply]
  simpa [hβ_at, hV_at] using hraw

/-- The directional covariant derivative of mixed tensor fields is homogeneous
under constant scalar multiplication. -/
theorem nablaRSFun_smul [T2Space M] {r s : ℕ}
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _))
    (c : Real)
    (T : TensorRSField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) r s)
    (x : M) :
    nablaRSFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        r s cov X (c • T) x =
      c • nablaRSFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        r s cov X T x := by
  classical
  letI := tensor0SBundle_topology (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) r
  letI := tensor0SBundle_fiber (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) r
  letI := tensor0SBundle_vector (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) r
  letI := tensor0SBundle_smooth (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
    (n := (∞ : WithTop ℕ∞)) r
  let basis : Module.Basis (Fin (Module.finrank Real (TangentSpace I x))) Real
      (TangentSpace I x) :=
    Module.finBasis Real (TangentSpace I x)
  apply extRS_basis (I := I) basis
  intro upper lower
  let βsec : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) r :=
    (ContMDiffSection.exists_eq_at
      (I := I) (F := Tensor0SModel r Real E)
      (V := fun y : M => Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I)
        (M := M) r y)
      (n := (⊤ : ℕ∞)) x (basisTensor0S (I := I) basis upper)).choose
  have hβ_at : βsec x = basisTensor0S (I := I) basis upper := by
    exact
      (ContMDiffSection.exists_eq_at
        (I := I) (F := Tensor0SModel r Real E)
        (V := fun y : M => Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I)
          (M := M) r y)
        (n := (⊤ : ℕ∞)) x (basisTensor0S (I := I) basis upper)).choose_spec
  let V : Fin s → ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M → Type _) :=
    fun a =>
      (ContMDiffSection.exists_eq_at
        (I := I) (F := E) (V := TangentSpace I) (n := (⊤ : ℕ∞))
        x (basis (lower a))).choose
  have hV_at : ∀ a : Fin s, V a x = basis (lower a) := by
    intro a
    exact
      (ContMDiffSection.exists_eq_at
        (I := I) (F := E) (V := TangentSpace I) (n := (⊤ : ℕ∞))
        x (basis (lower a))).choose_spec
  have hpairT : MDifferentiableAt I 𝓘(Real, Real)
      (fun p : M => (T p (βsec p)) (fun a : Fin s => V a p)) x :=
    (tensorRSField_eval_smooth_input_slots_contMDiffAt (I := I)
      T βsec V x).mdifferentiableAt (by simp)
  have hβmodel : DifferentiableWithinAt Real
      (tensor0SModelInChart (𝕜 := Real) (E := E) (H := H) (I := I)
        (M := M) r x (fun p : M => βsec p))
      (Set.range I) (extChartAt I x x) := by
    exact tensor0SModelInChart_differentiableWithinAt_center_of_contMDiffAt
      (I := I) βsec x (βsec.contMDiff x)
  have hV : ∀ a : Fin s, MDiffAt (T% (fun p : M => V a p)) x := by
    intro a
    exact (V a).contMDiff.contMDiffAt.mdifferentiableAt (by simp)
  have hVmodel : ∀ a : Fin s,
      DifferentiableWithinAt Real
        (tangentFieldModelInChart (𝕜 := Real) (I := I) x (fun p : M => V a p))
        (Set.range I) (extChartAt I x x) := by
    intro a
    exact tangentFieldModelInChart_differentiableWithinAt_center_of_contMDiffAt
      (I := I) (fun p : M => V a p) x ((V a).contMDiff.contMDiffAt)
  have hcoord : ∀ a : Fin s, ∀ i : Fin (Module.finrank Real E),
      MDifferentiableAt I 𝓘(Real, Real)
        (fun p : M =>
          (Module.finBasis Real E).coord i
            (tangentFieldModelInChart (𝕜 := Real) (I := I) x (fun q : M => V a q)
              (extChartAt I x p))) x := by
    intro a i
    exact tangentFieldModelInChart_coord_mdiffAt_center_of_contMDiffAt
      (I := I) (fun p : M => V a p) x ((V a).contMDiff.contMDiffAt) i
  have hraw := nablaRSFun_smul_raw
    (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
    (r := r) (s := s) cov X c T (fun p : M => βsec p)
    (fun a : Fin s => fun p : M => V a p) x
    hpairT hβmodel hV hVmodel hcoord
  simp only [componentRS_apply]
  simpa [hβ_at, hV_at, ContinuousLinearMap.smul_apply,
    ContinuousMultilinearMap.smul_apply, Pi.smul_apply, smul_eq_mul] using hraw

/-- The directional covariant derivative of the zero mixed tensor field is
zero. -/
theorem nablaRSFun_zero [T2Space M] {r s : ℕ}
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _))
    (x : M) :
    nablaRSFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        r s cov X
        (0 : TensorRSField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
          (n := (∞ : WithTop ℕ∞)) r s) x =
      0 := by
  letI := tensorRSBundle_topology (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) r s
  letI := tensorRSBundle_fiber (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) r s
  letI := tensorRSBundle_vector (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) r s
  letI := tensorRSBundle_smooth (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
    (n := (∞ : WithTop ℕ∞)) r s
  classical
  letI := tensor0SBundle_topology (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) r
  letI := tensor0SBundle_fiber (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) r
  letI := tensor0SBundle_vector (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) r
  letI := tensor0SBundle_smooth (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
    (n := (∞ : WithTop ℕ∞)) r
  let basis : Module.Basis (Fin (Module.finrank Real (TangentSpace I x))) Real
      (TangentSpace I x) :=
    Module.finBasis Real (TangentSpace I x)
  apply extRS_basis (I := I) basis
  intro upper lower
  let βsec : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) r :=
    (ContMDiffSection.exists_eq_at
      (I := I) (F := Tensor0SModel r Real E)
      (V := fun y : M => Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I)
        (M := M) r y)
      (n := (⊤ : ℕ∞)) x (basisTensor0S (I := I) basis upper)).choose
  have hβ_at : βsec x = basisTensor0S (I := I) basis upper := by
    exact
      (ContMDiffSection.exists_eq_at
        (I := I) (F := Tensor0SModel r Real E)
        (V := fun y : M => Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I)
          (M := M) r y)
        (n := (⊤ : ℕ∞)) x (basisTensor0S (I := I) basis upper)).choose_spec
  let V : Fin s → ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M → Type _) :=
    fun a =>
      (ContMDiffSection.exists_eq_at
        (I := I) (F := E) (V := TangentSpace I) (n := (⊤ : ℕ∞))
        x (basis (lower a))).choose
  have hV_at : ∀ a : Fin s, V a x = basis (lower a) := by
    intro a
    exact
      (ContMDiffSection.exists_eq_at
        (I := I) (F := E) (V := TangentSpace I) (n := (⊤ : ℕ∞))
        x (basis (lower a))).choose_spec
  have hβmodel : DifferentiableWithinAt Real
      (tensor0SModelInChart (𝕜 := Real) (E := E) (H := H) (I := I)
        (M := M) r x (fun p : M => βsec p))
      (Set.range I) (extChartAt I x x) := by
    exact tensor0SModelInChart_differentiableWithinAt_center_of_contMDiffAt
      (I := I) βsec x (βsec.contMDiff x)
  have hV : ∀ a : Fin s, MDiffAt (T% (fun p : M => V a p)) x := by
    intro a
    exact (V a).contMDiff.contMDiffAt.mdifferentiableAt (by simp)
  have hVmodel : ∀ a : Fin s,
      DifferentiableWithinAt Real
        (tangentFieldModelInChart (𝕜 := Real) (I := I) x (fun p : M => V a p))
        (Set.range I) (extChartAt I x x) := by
    intro a
    exact tangentFieldModelInChart_differentiableWithinAt_center_of_contMDiffAt
      (I := I) (fun p : M => V a p) x ((V a).contMDiff.contMDiffAt)
  have hcoord : ∀ a : Fin s, ∀ i : Fin (Module.finrank Real E),
      MDifferentiableAt I 𝓘(Real, Real)
        (fun p : M =>
          (Module.finBasis Real E).coord i
            (tangentFieldModelInChart (𝕜 := Real) (I := I) x (fun q : M => V a q)
              (extChartAt I x p))) x := by
    intro a i
    exact tangentFieldModelInChart_coord_mdiffAt_center_of_contMDiffAt
      (I := I) (fun p : M => V a p) x ((V a).contMDiff.contMDiffAt) i
  have hraw := nablaRSFun_sum_raw
    (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
    (ι := PUnit) (r := r) (s := s) cov X (∅ : Finset PUnit)
    (fun _ : PUnit =>
      (0 : TensorRSField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        (n := (∞ : WithTop ℕ∞)) r s))
    (fun p : M => βsec p) (fun a : Fin s => fun p : M => V a p) x
    (by intro i hi; simp at hi) hβmodel hV hVmodel hcoord
  simp only [componentRS_apply]
  simpa [hβ_at, hV_at] using hraw

/-- The directional covariant derivative of mixed tensor fields commutes with
finite sums. -/
theorem nablaRSFun_sum [T2Space M] {ι : Type*} {r s : ℕ}
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _))
    (S : Finset ι)
    (T : ι → TensorRSField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) r s)
    (x : M) :
    nablaRSFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        r s cov X (Finset.sum S T) x =
      Finset.sum S fun i =>
        nablaRSFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
          r s cov X (T i) x := by
  classical
  refine Finset.induction_on S ?base ?step
  · change nablaRSFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        r s cov X
        (0 : TensorRSField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
          (n := (∞ : WithTop ℕ∞)) r s) x = 0
    exact nablaRSFun_zero (I := I) (r := r) (s := s) cov X x
  · intro i A hi ih
    rw [Finset.sum_insert hi, nablaRSFun_add (I := I) cov X (T i) (Finset.sum A T) x]
    rw [ih, Finset.sum_insert hi]

/-- Total covariant derivative realizations are additive in the tensor field. -/
theorem TotalNabla0SRealizes.add [T2Space M] {s : ℕ}
    {cov : CovariantDerivative I E (TangentSpace I : M → Type _)}
    {α β : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s}
    {nablaAlpha nablaBeta :
      Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        (n := (∞ : WithTop ℕ∞)) (s + 1)}
    (hα : TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) s cov α nablaAlpha)
    (hβ : TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) s cov β nablaBeta) :
    TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      s cov (α + β) (nablaAlpha + nablaBeta) := by
  intro X x slots
  have hα' := hα X x slots
  have hβ' := hβ X x slots
  calc
    (nablaAlpha + nablaBeta) x (Fin.cons (X x) slots)
        = nablaAlpha x (Fin.cons (X x) slots) +
            nablaBeta x (Fin.cons (X x) slots) := rfl
    _ = nabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
            s cov X α x slots +
          nabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
            s cov X β x slots := by rw [hα', hβ']
    _ = nabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
          s cov X (α + β) x slots := by
        rw [nabla0SFun_add (I := I) cov X α β x]
        rfl

/-- Total covariant derivative realizations are homogeneous under constant
scalar multiplication of the tensor field. -/
theorem TotalNabla0SRealizes.smul [T2Space M] {s : ℕ}
    {cov : CovariantDerivative I E (TangentSpace I : M → Type _)}
    (c : Real)
    {α : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s}
    {nablaAlpha :
      Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        (n := (∞ : WithTop ℕ∞)) (s + 1)}
    (hα : TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) s cov α nablaAlpha) :
    TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      s cov (c • α) (c • nablaAlpha) := by
  intro X x slots
  have hα' := hα X x slots
  calc
    (c • nablaAlpha) x (Fin.cons (X x) slots)
        = c • nablaAlpha x (Fin.cons (X x) slots) := rfl
    _ = c • nabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
          s cov X α x slots := by rw [hα']
    _ = nabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
          s cov X (c • α) x slots := by
        rw [nabla0SFun_smul (I := I) cov X c α x]
        rfl

/-- The zero field realizes the total derivative of the zero covariant tensor
field. -/
theorem TotalNabla0SRealizes.zero [T2Space M] {s : ℕ}
    {cov : CovariantDerivative I E (TangentSpace I : M -> Type _)} :
    TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      s cov
      (0 : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        (n := (∞ : WithTop ℕ∞)) s)
      (0 : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        (n := (∞ : WithTop ℕ∞)) (s + 1)) := by
  intro X x slots
  change (0 : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I)
      (M := M) (s + 1) x) (Fin.cons (X x) slots) =
    nabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      s cov X
      (0 : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        (n := (∞ : WithTop ℕ∞)) s) x slots
  rw [nabla0SFun_zero (I := I) (s := s) cov X x]
  rfl

/-- Total covariant derivative realizations commute with finite sums of
covariant tensor fields. -/
theorem TotalNabla0SRealizes.sum [T2Space M] {ι : Type*} {s : ℕ}
    {cov : CovariantDerivative I E (TangentSpace I : M -> Type _)}
    (S : Finset ι)
    (T : ι -> Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s)
    (nablaT : ι -> Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) (s + 1))
    (hT : ∀ i, i ∈ S ->
      TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H)
        (I := I) (M := M) s cov (T i) (nablaT i)) :
    TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      s cov (Finset.sum S T) (Finset.sum S nablaT) := by
  classical
  revert hT
  refine Finset.induction_on S ?base ?step
  · intro _hT
    exact TotalNabla0SRealizes.zero (I := I) (s := s) (cov := cov)
  · intro i A hi ih hT
    rw [Finset.sum_insert hi, Finset.sum_insert hi]
    exact TotalNabla0SRealizes.add (I := I)
      (hT i (by simp [hi]))
      (ih fun j hj => hT j (by simp [hj]))

/-- Normalized iterated covariant-derivative realizations are additive in the
tensor field. -/
theorem IterNabla0SRealizes.add [T2Space M] {s k : ℕ}
    {cov : CovariantDerivative I E (TangentSpace I : M -> Type _)}
    {α β : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s}
    {αk βk : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) (s + k)}
    (hα : IterNabla0SRealizes (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) cov α k αk)
    (hβ : IterNabla0SRealizes (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) cov β k βk) :
    IterNabla0SRealizes (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      cov (α + β) k (αk + βk) := by
  induction k generalizing α β with
  | zero =>
      cases hα
      cases hβ
      exact IterNabla0SRealizes.zero
  | succ k ih =>
      rcases IterNabla0SRealizes.succ_inv (𝕜 := Real) (E := E) (H := H)
          (I := I) (M := M) (k := k) hα with ⟨αprev, hαprev, hαstep⟩
      rcases IterNabla0SRealizes.succ_inv (𝕜 := Real) (E := E) (H := H)
          (I := I) (M := M) (k := k) hβ with ⟨βprev, hβprev, hβstep⟩
      refine IterNabla0SRealizes.succ (ih hαprev hβprev) ?_
      exact TotalNabla0SRealizes.add (I := I) hαstep hβstep

/-- Normalized iterated covariant-derivative realizations are homogeneous under
constant scalar multiplication. -/
theorem IterNabla0SRealizes.smul [T2Space M] {s k : ℕ}
    (c : Real)
    {cov : CovariantDerivative I E (TangentSpace I : M -> Type _)}
    {α : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s}
    {αk : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) (s + k)}
    (hα : IterNabla0SRealizes (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) cov α k αk) :
    IterNabla0SRealizes (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      cov (c • α) k (c • αk) := by
  induction k generalizing α with
  | zero =>
      cases hα
      exact IterNabla0SRealizes.zero
  | succ k ih =>
      rcases IterNabla0SRealizes.succ_inv (𝕜 := Real) (E := E) (H := H)
          (I := I) (M := M) (k := k) hα with ⟨αprev, hαprev, hαstep⟩
      refine IterNabla0SRealizes.succ (ih hαprev) ?_
      exact TotalNabla0SRealizes.smul (I := I) c hαstep

/-- The zero field realizes all normalized iterated covariant derivatives of
the zero field. -/
theorem IterNabla0SRealizes.zero_field [T2Space M] {s k : ℕ}
    {cov : CovariantDerivative I E (TangentSpace I : M -> Type _)} :
    IterNabla0SRealizes (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      cov
      (0 : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        (n := (∞ : WithTop ℕ∞)) s)
      k
      (0 : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        (n := (∞ : WithTop ℕ∞)) (s + k)) := by
  induction k with
  | zero =>
      exact IterNabla0SRealizes.zero
  | succ k ih =>
      refine IterNabla0SRealizes.succ ih ?_
      exact TotalNabla0SRealizes.zero (I := I) (s := s + k) (cov := cov)

/-- Normalized iterated covariant-derivative realizations commute with finite
sums. -/
theorem IterNabla0SRealizes.sum [T2Space M] {ι : Type*} {s k : ℕ}
    {cov : CovariantDerivative I E (TangentSpace I : M -> Type _)}
    (S : Finset ι)
    (T : ι -> Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s)
    (Tk : ι -> Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) (s + k))
    (hT : ∀ i, i ∈ S ->
      IterNabla0SRealizes (𝕜 := Real) (E := E) (H := H)
        (I := I) (M := M) cov (T i) k (Tk i)) :
    IterNabla0SRealizes (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      cov (Finset.sum S T) k (Finset.sum S Tk) := by
  classical
  revert hT
  refine Finset.induction_on S ?base ?step
  · intro _hT
    exact IterNabla0SRealizes.zero_field (I := I) (s := s) (k := k) (cov := cov)
  · intro i A hi ih hT
    rw [Finset.sum_insert hi, Finset.sum_insert hi]
    exact IterNabla0SRealizes.add (I := I)
      (hT i (by simp [hi]))
      (ih fun j hj => hT j (by simp [hj]))

/-- Normalized iterated covariant-derivative realizations commute with
finite weighted sums. -/
theorem IterNabla0SRealizes.sum_smul [T2Space M] {ι : Type*} {s k : ℕ}
    {cov : CovariantDerivative I E (TangentSpace I : M -> Type _)}
    (S : Finset ι) (c : ι -> Real)
    (T : ι -> Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s)
    (Tk : ι -> Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) (s + k))
    (hT : ∀ i, i ∈ S ->
      IterNabla0SRealizes (𝕜 := Real) (E := E) (H := H)
        (I := I) (M := M) cov (T i) k (Tk i)) :
    IterNabla0SRealizes (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      cov
      (Finset.sum S fun i => c i • T i)
      k
      (Finset.sum S fun i => c i • Tk i) := by
  exact IterNabla0SRealizes.sum (I := I) (M := M) (cov := cov) S
    (fun i => c i • T i) (fun i => c i • Tk i)
    (fun i hi => IterNabla0SRealizes.smul (I := I) (M := M)
      (c i) (hT i hi))

/-- The recursive Leibniz product fields differentiate to the next recursive
Leibniz product field.

This is the realization step behind the future all-order product jet. -/
theorem tensor0SField_productJetTerm_step [T2Space M] [IsManifold I ⊤ M] {s q : ℕ}
    {cov : CovariantDerivative I E (TangentSpace I : M -> Type _)}
    {α : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s}
    {β : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) q}
    (Jα : IterNabla0SJet (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      cov α)
    (Jβ : IterNabla0SJet (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      cov β) :
    ∀ k : ℕ,
      TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        ((s + q) + k) cov
        (tensor0SField_productJetTerm (I := I) (M := M) Jα Jβ k)
        (tensor0SField_productJetTerm (I := I) (M := M) Jα Jβ (k + 1)) := by
  intro k
  induction k generalizing s q α β with
  | zero =>
      exact tensor0SField_productJetTerm_step_zero (I := I) (M := M) Jα Jβ
  | succ k ih =>
      let Jαtail := IterNabla0SJet.tail (𝕜 := Real) (E := E) (H := H)
        (I := I) (M := M) Jα
      let Jβtail := IterNabla0SJet.tail (𝕜 := Real) (E := E) (H := H)
        (I := I) (M := M) Jβ
      have hleft0 :=
        ih (s := s + 1) (q := q) (α := Jα.term 1) (β := β)
          Jαtail Jβ
      have hright0 :=
        ih (s := s) (q := q + 1) (α := α) (β := Jβ.term 1)
          Jα Jβtail
      have hleft :=
        TotalNabla0SRealizes.permute (I := I) (M := M)
          (iterLeadingSlotPerm (productDerivLeftPerm s q) k) hleft0
      have hright :=
        TotalNabla0SRealizes.permute (I := I) (M := M)
          (iterLeadingSlotPerm (productDerivRightPerm s q) k) hright0
      have hsum := TotalNabla0SRealizes.add (I := I) hleft hright
      refine TotalNabla0SRealizes.congr (𝕜 := Real) (E := E) (H := H)
        (I := I) (M := M) ?hsource ?htarget
        (TotalNabla0SRealizes.castField (𝕜 := Real) (E := E) (H := H)
          (I := I) (M := M)
          (by omega : (((s + q) + 1) + k) = ((s + q) + (k + 1)))
          hsum)
      · simp [tensor0SField_productJetTerm, tensor0SFieldCast, Jαtail, Jβtail]
      · ext x slots
        simp [tensor0SField_productJetTerm, tensor0SFieldCast, Jαtail, Jβtail,
          iterLeadingSlotPerm]

/-- Product of two covariant derivative jets, with terms given by the recursive
Leibniz product tree. -/
noncomputable def IterNabla0SJet.product [T2Space M] [IsManifold I ⊤ M] {s q : ℕ}
    {cov : CovariantDerivative I E (TangentSpace I : M -> Type _)}
    {α : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s}
    {β : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) q}
    (Jα : IterNabla0SJet (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      cov α)
    (Jβ : IterNabla0SJet (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      cov β) :
    IterNabla0SJet (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      cov
      (tensor0SField_product (𝕜 := Real) (E := E) (H := H)
        (I := I) (M := M) (∞ : WithTop ℕ∞) α β) where
  term k := tensor0SField_productJetTerm (I := I) (M := M) Jα Jβ k
  zero_eq := by
    simp [tensor0SField_productJetTerm, tensor0SFieldCast]
  step k := tensor0SField_productJetTerm_step (I := I) (M := M) Jα Jβ k

/-- The explicit second total derivative field of a tensor product obtained by
differentiating the two first Leibniz summands. -/
noncomputable def tensor0SField_productDerivSecond [IsManifold I ⊤ M] {s q : ℕ}
    (α : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s)
    (β : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) q)
    (α1 : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) (s + 1))
    (β1 : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) (q + 1))
    (α2 : Tensor0SField (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) ((s + 1) + 1))
    (β2 : Tensor0SField (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) ((q + 1) + 1)) :
    Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) (((s + q) + 1) + 1) :=
  tensor0SField_permute (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (∞ : WithTop ℕ∞)
      (leadingSlotPerm (productDerivLeftPerm s q))
      (tensor0SField_productDeriv (I := I) (M := M) α1 β α2 β1) +
    tensor0SField_permute (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (∞ : WithTop ℕ∞)
      (leadingSlotPerm (productDerivRightPerm s q))
      (tensor0SField_productDeriv (I := I) (M := M) α β1 α1 β2)

/-- The first Leibniz derivative field has the explicit second Leibniz
derivative field above as a total derivative. -/
theorem TotalNabla0SRealizes.productDeriv [T2Space M] [IsManifold I ⊤ M] {s q : ℕ}
    {cov : CovariantDerivative I E (TangentSpace I : M -> Type _)}
    {α : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s}
    {β : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) q}
    {α1 : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) (s + 1)}
    {β1 : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) (q + 1)}
    {α2 : Tensor0SField (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) ((s + 1) + 1)}
    {β2 : Tensor0SField (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) ((q + 1) + 1)}
    (hα0 : TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) s cov α α1)
    (hβ0 : TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) q cov β β1)
    (hα1 : TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (s + 1) cov α1 α2)
    (hβ1 : TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (q + 1) cov β1 β2) :
    TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      ((s + q) + 1) cov
      (tensor0SField_productDeriv (I := I) (M := M) α β α1 β1)
      (tensor0SField_productDerivSecond (I := I) (M := M) α β α1 β1 α2 β2) := by
  rw [tensor0SField_productDeriv]
  exact TotalNabla0SRealizes.add (I := I)
    (TotalNabla0SRealizes.productDerivLeft (I := I) (M := M) hα1 hβ0)
    (TotalNabla0SRealizes.productDerivRight (I := I) (M := M) hα0 hβ1)

/-- Normalized order-two product realization.  The first-derivative fields of
the two factors are returned because the explicit second Leibniz field depends
on those choices. -/
theorem IterNabla0SRealizes.product_two [T2Space M] [IsManifold I ⊤ M] {s q : ℕ}
    {cov : CovariantDerivative I E (TangentSpace I : M -> Type _)}
    {α : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s}
    {β : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) q}
    {α2 : Tensor0SField (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) (s + 2)}
    {β2 : Tensor0SField (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) (q + 2)}
    (hα : IterNabla0SRealizes (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) cov α 2 α2)
    (hβ : IterNabla0SRealizes (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) cov β 2 β2) :
    ∃ (α1 : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
          (n := (∞ : WithTop ℕ∞)) (s + 1))
      (β1 : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
          (n := (∞ : WithTop ℕ∞)) (q + 1)),
      IterNabla0SRealizes (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        cov
        (tensor0SField_product (𝕜 := Real) (E := E) (H := H)
          (I := I) (M := M) (∞ : WithTop ℕ∞) α β)
        2
        (tensor0SField_productDerivSecond (I := I) (M := M) α β α1 β1 α2 β2) := by
  rcases IterNabla0SRealizes.two (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) hα with ⟨α1, hα0, hα1⟩
  rcases IterNabla0SRealizes.two (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) hβ with ⟨β1, hβ0, hβ1⟩
  refine ⟨α1, β1, ?_⟩
  refine IterNabla0SRealizes.succ
    (αk := tensor0SField_productDeriv (I := I) (M := M) α β α1 β1)
    ?hprod0 ?hprod1
  · refine IterNabla0SRealizes.succ IterNabla0SRealizes.zero ?_
    exact TotalNabla0SRealizes.product (I := I) (M := M) (s := s) (q := q)
      (cov := cov) (α := α) (β := β) (nablaAlpha := α1) (nablaBeta := β1)
      hα0 hβ0
  · exact TotalNabla0SRealizes.productDeriv (I := I) (M := M)
      (s := s) (q := q) (cov := cov) (α := α) (β := β)
      (α1 := α1) (β1 := β1) (α2 := α2) (β2 := β2)
      hα0 hβ0 hα1 hβ1

/-- The explicit third total derivative field of a tensor product obtained by
differentiating the second Leibniz field. -/
noncomputable def tensor0SField_productDerivThird [IsManifold I ⊤ M] {s q : ℕ}
    (α : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s)
    (β : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) q)
    (α1 : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) (s + 1))
    (β1 : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) (q + 1))
    (α2 : Tensor0SField (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) (s + 2))
    (β2 : Tensor0SField (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) (q + 2))
    (α3 : Tensor0SField (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) (s + 3))
    (β3 : Tensor0SField (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) (q + 3)) :
    Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) ((((s + q) + 1) + 1) + 1) :=
  tensor0SField_permute (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (∞ : WithTop ℕ∞)
      (leadingSlotPerm (leadingSlotPerm (productDerivLeftPerm s q)))
      (tensor0SField_productDerivSecond (I := I) (M := M) α1 β α2 β1 α3 β2) +
    tensor0SField_permute (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (∞ : WithTop ℕ∞)
      (leadingSlotPerm (leadingSlotPerm (productDerivRightPerm s q)))
      (tensor0SField_productDerivSecond (I := I) (M := M) α β1 α1 β2 α2 β3)

/-- The second Leibniz derivative field has the explicit third Leibniz
derivative field above as a total derivative. -/
theorem TotalNabla0SRealizes.productDerivSecond [T2Space M] [IsManifold I ⊤ M]
    {s q : ℕ}
    {cov : CovariantDerivative I E (TangentSpace I : M -> Type _)}
    {α : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s}
    {β : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) q}
    {α1 : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) (s + 1)}
    {β1 : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) (q + 1)}
    {α2 : Tensor0SField (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) (s + 2)}
    {β2 : Tensor0SField (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) (q + 2)}
    {α3 : Tensor0SField (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) (s + 3)}
    {β3 : Tensor0SField (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) (q + 3)}
    (hα0 : TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) s cov α α1)
    (hβ0 : TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) q cov β β1)
    (hα1 : TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (s + 1) cov α1 α2)
    (hβ1 : TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (q + 1) cov β1 β2)
    (hα2 : TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (s + 2) cov α2 α3)
    (hβ2 : TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (q + 2) cov β2 β3) :
    TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (((s + q) + 1) + 1) cov
      (tensor0SField_productDerivSecond (I := I) (M := M) α β α1 β1 α2 β2)
      (tensor0SField_productDerivThird (I := I) (M := M)
        α β α1 β1 α2 β2 α3 β3) := by
  rw [tensor0SField_productDerivSecond]
  exact TotalNabla0SRealizes.add (I := I)
    (TotalNabla0SRealizes.permute (I := I) (M := M)
      (leadingSlotPerm (productDerivLeftPerm s q))
      (TotalNabla0SRealizes.productDeriv (I := I) (M := M)
        (s := s + 1) (q := q) (cov := cov)
        (α := α1) (β := β) (α1 := α2) (β1 := β1)
        (α2 := α3) (β2 := β2) hα1 hβ0 hα2 hβ1))
    (TotalNabla0SRealizes.permute (I := I) (M := M)
      (leadingSlotPerm (productDerivRightPerm s q))
      (TotalNabla0SRealizes.productDeriv (I := I) (M := M)
        (s := s) (q := q + 1) (cov := cov)
        (α := α) (β := β1) (α1 := α1) (β1 := β2)
        (α2 := α2) (β2 := β3) hα0 hβ1 hα1 hβ2))

/-- Normalized order-three product realization.  As in the order-two case,
the intermediate factor derivatives are returned because the explicit Leibniz
field depends on those choices. -/
theorem IterNabla0SRealizes.product_three [T2Space M] [IsManifold I ⊤ M] {s q : ℕ}
    {cov : CovariantDerivative I E (TangentSpace I : M -> Type _)}
    {α : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s}
    {β : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) q}
    {α3 : Tensor0SField (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) (s + 3)}
    {β3 : Tensor0SField (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) (q + 3)}
    (hα : IterNabla0SRealizes (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) cov α 3 α3)
    (hβ : IterNabla0SRealizes (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) cov β 3 β3) :
    ∃ (α1 : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
          (n := (∞ : WithTop ℕ∞)) (s + 1))
      (α2 : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
          (n := (∞ : WithTop ℕ∞)) (s + 2))
      (β1 : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
          (n := (∞ : WithTop ℕ∞)) (q + 1))
      (β2 : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
          (n := (∞ : WithTop ℕ∞)) (q + 2)),
      IterNabla0SRealizes (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        cov
        (tensor0SField_product (𝕜 := Real) (E := E) (H := H)
          (I := I) (M := M) (∞ : WithTop ℕ∞) α β)
        3
        (tensor0SField_productDerivThird (I := I) (M := M)
          α β α1 β1 α2 β2 α3 β3) := by
  rcases IterNabla0SRealizes.three (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) hα with ⟨α1, α2, hα0, hα1, hα2⟩
  rcases IterNabla0SRealizes.three (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) hβ with ⟨β1, β2, hβ0, hβ1, hβ2⟩
  refine ⟨α1, α2, β1, β2, ?_⟩
  refine IterNabla0SRealizes.succ
    (k := 2)
    (αk := tensor0SField_productDerivSecond (I := I) (M := M)
      α β α1 β1 α2 β2) ?hprod2 ?hprod3
  · refine IterNabla0SRealizes.succ
      (αk := tensor0SField_productDeriv (I := I) (M := M) α β α1 β1)
      ?hprod1 ?hprod2step
    · refine IterNabla0SRealizes.succ IterNabla0SRealizes.zero ?_
      exact TotalNabla0SRealizes.product (I := I) (M := M) (s := s) (q := q)
        (cov := cov) (α := α) (β := β) (nablaAlpha := α1) (nablaBeta := β1)
        hα0 hβ0
    · exact TotalNabla0SRealizes.productDeriv (I := I) (M := M)
        (s := s) (q := q) (cov := cov) (α := α) (β := β)
        (α1 := α1) (β1 := β1) (α2 := α2) (β2 := β2)
        hα0 hβ0 hα1 hβ1
  · exact TotalNabla0SRealizes.productDerivSecond (I := I) (M := M)
      (s := s) (q := q) (cov := cov) (α := α) (β := β)
      (α1 := α1) (β1 := β1) (α2 := α2) (β2 := β2)
      (α3 := α3) (β3 := β3) hα0 hβ0 hα1 hβ1 hα2 hβ2

/-- The explicit fourth total derivative field of a tensor product obtained by
differentiating the third Leibniz field. -/
noncomputable def tensor0SField_productDerivFourth [IsManifold I ⊤ M] {s q : ℕ}
    (α : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s)
    (β : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) q)
    (α1 : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) (s + 1))
    (β1 : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) (q + 1))
    (α2 : Tensor0SField (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) (s + 2))
    (β2 : Tensor0SField (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) (q + 2))
    (α3 : Tensor0SField (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) (s + 3))
    (β3 : Tensor0SField (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) (q + 3))
    (α4 : Tensor0SField (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) (s + 4))
    (β4 : Tensor0SField (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) (q + 4)) :
    Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) (((((s + q) + 1) + 1) + 1) + 1) :=
  tensor0SField_permute (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (∞ : WithTop ℕ∞)
      (leadingSlotPerm (leadingSlotPerm (leadingSlotPerm (productDerivLeftPerm s q))))
      (tensor0SField_productDerivThird (I := I) (M := M)
        α1 β α2 β1 α3 β2 α4 β3) +
    tensor0SField_permute (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (∞ : WithTop ℕ∞)
      (leadingSlotPerm (leadingSlotPerm (leadingSlotPerm (productDerivRightPerm s q))))
      (tensor0SField_productDerivThird (I := I) (M := M)
        α β1 α1 β2 α2 β3 α3 β4)

/-- The third Leibniz derivative field has the explicit fourth Leibniz
derivative field above as a total derivative. -/
theorem TotalNabla0SRealizes.productDerivThird [T2Space M] [IsManifold I ⊤ M]
    {s q : ℕ}
    {cov : CovariantDerivative I E (TangentSpace I : M -> Type _)}
    {α : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s}
    {β : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) q}
    {α1 : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) (s + 1)}
    {β1 : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) (q + 1)}
    {α2 : Tensor0SField (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) (s + 2)}
    {β2 : Tensor0SField (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) (q + 2)}
    {α3 : Tensor0SField (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) (s + 3)}
    {β3 : Tensor0SField (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) (q + 3)}
    {α4 : Tensor0SField (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) (s + 4)}
    {β4 : Tensor0SField (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) (q + 4)}
    (hα0 : TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) s cov α α1)
    (hβ0 : TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) q cov β β1)
    (hα1 : TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (s + 1) cov α1 α2)
    (hβ1 : TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (q + 1) cov β1 β2)
    (hα2 : TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (s + 2) cov α2 α3)
    (hβ2 : TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (q + 2) cov β2 β3)
    (hα3 : TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (s + 3) cov α3 α4)
    (hβ3 : TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (q + 3) cov β3 β4) :
    TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      ((((s + q) + 1) + 1) + 1) cov
      (tensor0SField_productDerivThird (I := I) (M := M)
        α β α1 β1 α2 β2 α3 β3)
      (tensor0SField_productDerivFourth (I := I) (M := M)
        α β α1 β1 α2 β2 α3 β3 α4 β4) := by
  rw [tensor0SField_productDerivThird]
  exact TotalNabla0SRealizes.add (I := I)
    (TotalNabla0SRealizes.permute (I := I) (M := M)
      (leadingSlotPerm (leadingSlotPerm (productDerivLeftPerm s q)))
      (TotalNabla0SRealizes.productDerivSecond (I := I) (M := M)
        (s := s + 1) (q := q) (cov := cov)
        (α := α1) (β := β) (α1 := α2) (β1 := β1)
        (α2 := α3) (β2 := β2) (α3 := α4) (β3 := β3)
        hα1 hβ0 hα2 hβ1 hα3 hβ2))
    (TotalNabla0SRealizes.permute (I := I) (M := M)
      (leadingSlotPerm (leadingSlotPerm (productDerivRightPerm s q)))
      (TotalNabla0SRealizes.productDerivSecond (I := I) (M := M)
        (s := s) (q := q + 1) (cov := cov)
        (α := α) (β := β1) (α1 := α1) (β1 := β2)
        (α2 := α2) (β2 := β3) (α3 := α3) (β3 := β4)
        hα0 hβ1 hα1 hβ2 hα2 hβ3))

/-- Normalized order-four product realization.  This extends the checked
recursive Leibniz tower one level beyond `product_three`; the remaining
all-order frontier is to replace these manually enumerated levels by a
general antidiagonal or expression-tree construction. -/
theorem IterNabla0SRealizes.product_four [T2Space M] [IsManifold I ⊤ M] {s q : ℕ}
    {cov : CovariantDerivative I E (TangentSpace I : M -> Type _)}
    {α : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s}
    {β : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) q}
    {α4 : Tensor0SField (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) (s + 4)}
    {β4 : Tensor0SField (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) (q + 4)}
    (hα : IterNabla0SRealizes (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) cov α 4 α4)
    (hβ : IterNabla0SRealizes (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) cov β 4 β4) :
    ∃ (α1 : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
          (n := (∞ : WithTop ℕ∞)) (s + 1))
      (α2 : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
          (n := (∞ : WithTop ℕ∞)) (s + 2))
      (α3 : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
          (n := (∞ : WithTop ℕ∞)) (s + 3))
      (β1 : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
          (n := (∞ : WithTop ℕ∞)) (q + 1))
      (β2 : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
          (n := (∞ : WithTop ℕ∞)) (q + 2))
      (β3 : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
          (n := (∞ : WithTop ℕ∞)) (q + 3)),
      IterNabla0SRealizes (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        cov
        (tensor0SField_product (𝕜 := Real) (E := E) (H := H)
          (I := I) (M := M) (∞ : WithTop ℕ∞) α β)
        4
        (tensor0SField_productDerivFourth (I := I) (M := M)
          α β α1 β1 α2 β2 α3 β3 α4 β4) := by
  rcases IterNabla0SRealizes.four (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) hα with ⟨α1, α2, α3, hα0, hα1, hα2, hα3⟩
  rcases IterNabla0SRealizes.four (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) hβ with ⟨β1, β2, β3, hβ0, hβ1, hβ2, hβ3⟩
  refine ⟨α1, α2, α3, β1, β2, β3, ?_⟩
  refine IterNabla0SRealizes.succ
    (k := 3)
    (αk := tensor0SField_productDerivThird (I := I) (M := M)
      α β α1 β1 α2 β2 α3 β3) ?hprod3 ?hprod4
  · refine IterNabla0SRealizes.succ
      (k := 2)
      (αk := tensor0SField_productDerivSecond (I := I) (M := M)
        α β α1 β1 α2 β2) ?hprod2 ?hprod3step
    · refine IterNabla0SRealizes.succ
        (αk := tensor0SField_productDeriv (I := I) (M := M) α β α1 β1)
        ?hprod1 ?hprod2step
      · refine IterNabla0SRealizes.succ IterNabla0SRealizes.zero ?_
        exact TotalNabla0SRealizes.product (I := I) (M := M) (s := s) (q := q)
          (cov := cov) (α := α) (β := β) (nablaAlpha := α1) (nablaBeta := β1)
          hα0 hβ0
      · exact TotalNabla0SRealizes.productDeriv (I := I) (M := M)
          (s := s) (q := q) (cov := cov) (α := α) (β := β)
          (α1 := α1) (β1 := β1) (α2 := α2) (β2 := β2)
          hα0 hβ0 hα1 hβ1
    · exact TotalNabla0SRealizes.productDerivSecond (I := I) (M := M)
        (s := s) (q := q) (cov := cov) (α := α) (β := β)
        (α1 := α1) (β1 := β1) (α2 := α2) (β2 := β2)
        (α3 := α3) (β3 := β3) hα0 hβ0 hα1 hβ1 hα2 hβ2
  · exact TotalNabla0SRealizes.productDerivThird (I := I) (M := M)
      (s := s) (q := q) (cov := cov) (α := α) (β := β)
      (α1 := α1) (β1 := β1) (α2 := α2) (β2 := β2)
      (α3 := α3) (β3 := β3) (α4 := α4) (β4 := β4)
      hα0 hβ0 hα1 hβ1 hα2 hβ2 hα3 hβ3

/-- Total covariant derivative realizations are additive in mixed tensor
fields. -/
theorem TotalNablaRSRealizes.add [T2Space M] {r s : ℕ}
    {cov : CovariantDerivative I E (TangentSpace I : M → Type _)}
    {T U : TensorRSField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) r s}
    {nablaT nablaU :
      TensorRSField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        (n := (∞ : WithTop ℕ∞)) r (s + 1)}
    (hT : TotalNablaRSRealizes (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) r s cov T nablaT)
    (hU : TotalNablaRSRealizes (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) r s cov U nablaU) :
    TotalNablaRSRealizes (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      r s cov (T + U) (nablaT + nablaU) := by
  intro X x β slots
  have hT' := hT X x β slots
  have hU' := hU X x β slots
  calc
    (nablaT + nablaU) x β (Fin.cons (X x) slots)
        = nablaT x β (Fin.cons (X x) slots) +
            nablaU x β (Fin.cons (X x) slots) := rfl
    _ = nablaRSFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
            r s cov X T x β slots +
          nablaRSFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
            r s cov X U x β slots := by rw [hT', hU']
    _ = nablaRSFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
          r s cov X (T + U) x β slots := by
        rw [nablaRSFun_add (I := I) cov X T U x]
        rfl

/-- Total covariant derivative realizations are homogeneous under constant
scalar multiplication of mixed tensor fields. -/
theorem TotalNablaRSRealizes.smul [T2Space M] {r s : ℕ}
    {cov : CovariantDerivative I E (TangentSpace I : M → Type _)}
    (c : Real)
    {T : TensorRSField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) r s}
    {nablaT :
      TensorRSField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        (n := (∞ : WithTop ℕ∞)) r (s + 1)}
    (hT : TotalNablaRSRealizes (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) r s cov T nablaT) :
    TotalNablaRSRealizes (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      r s cov (c • T) (c • nablaT) := by
  intro X x β slots
  have hT' := hT X x β slots
  calc
    (c • nablaT) x β (Fin.cons (X x) slots)
        = c • nablaT x β (Fin.cons (X x) slots) := rfl
    _ = c • nablaRSFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
          r s cov X T x β slots := by rw [hT']
    _ = nablaRSFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
          r s cov X (c • T) x β slots := by
        rw [nablaRSFun_smul (I := I) cov X c T x]
        rfl

/-- The zero mixed tensor field realizes its own zero total covariant
derivative. -/
theorem TotalNablaRSRealizes.zero [T2Space M] {r s : ℕ}
    {cov : CovariantDerivative I E (TangentSpace I : M → Type _)} :
    TotalNablaRSRealizes (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      r s cov
      (0 : TensorRSField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        (n := (∞ : WithTop ℕ∞)) r s)
      (0 : TensorRSField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        (n := (∞ : WithTop ℕ∞)) r (s + 1)) := by
  letI := tensorRSBundle_topology (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) r s
  letI := tensorRSBundle_fiber (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) r s
  letI := tensorRSBundle_vector (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) r s
  letI := tensorRSBundle_smooth (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
    (n := (∞ : WithTop ℕ∞)) r s
  letI := tensorRSBundle_topology (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
    r (s + 1)
  letI := tensorRSBundle_fiber (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
    r (s + 1)
  letI := tensorRSBundle_vector (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
    r (s + 1)
  letI := tensorRSBundle_smooth (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
    (n := (∞ : WithTop ℕ∞)) r (s + 1)
  intro X x β slots
  rw [nablaRSFun_zero (I := I) (r := r) (s := s) cov X x]
  rfl

/-- Total covariant derivative realizations commute with finite sums of mixed
tensor fields. -/
theorem TotalNablaRSRealizes.sum [T2Space M] {ι : Type*} {r s : ℕ}
    {cov : CovariantDerivative I E (TangentSpace I : M → Type _)}
    {T : ι → TensorRSField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) r s}
    {nablaT : ι → TensorRSField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) r (s + 1)}
    (S : Finset ι)
    (hT : ∀ i : ι, i ∈ S →
      TotalNablaRSRealizes (𝕜 := Real) (E := E) (H := H)
        (I := I) (M := M) r s cov (T i) (nablaT i)) :
    TotalNablaRSRealizes (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      r s cov (Finset.sum S T) (Finset.sum S nablaT) := by
  classical
  revert hT
  refine Finset.induction_on S ?base ?step
  · intro _hT
    simpa using
      (TotalNablaRSRealizes.zero (I := I) (r := r) (s := s) (cov := cov) :
        TotalNablaRSRealizes (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
          r s cov
          (0 : TensorRSField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
            (n := (∞ : WithTop ℕ∞)) r s)
          (0 : TensorRSField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
            (n := (∞ : WithTop ℕ∞)) r (s + 1)))
  · intro i A hi ih hT
    rw [Finset.sum_insert hi, Finset.sum_insert hi]
    exact TotalNablaRSRealizes.add (I := I)
      (hT i (Finset.mem_insert_self i A))
      (ih fun j hj => hT j (Finset.mem_insert_of_mem hj))

/-- Normalized iterated mixed-tensor covariant-derivative realizations are
additive in the tensor field. -/
theorem IterNablaRSRealizes.add [T2Space M] {r s k : ℕ}
    {cov : CovariantDerivative I E (TangentSpace I : M -> Type _)}
    {T U : TensorRSField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) r s}
    {Tk Uk : TensorRSField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) r (s + k)}
    (hT : IterNablaRSRealizes (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) cov T k Tk)
    (hU : IterNablaRSRealizes (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) cov U k Uk) :
    IterNablaRSRealizes (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      cov (T + U) k (Tk + Uk) := by
  induction k generalizing T U with
  | zero =>
      cases hT
      cases hU
      exact IterNablaRSRealizes.zero
  | succ k ih =>
      rcases IterNablaRSRealizes.succ_inv (𝕜 := Real) (E := E) (H := H)
          (I := I) (M := M) (k := k) hT with ⟨Tprev, hTprev, hTstep⟩
      rcases IterNablaRSRealizes.succ_inv (𝕜 := Real) (E := E) (H := H)
          (I := I) (M := M) (k := k) hU with ⟨Uprev, hUprev, hUstep⟩
      refine IterNablaRSRealizes.succ (ih hTprev hUprev) ?_
      exact TotalNablaRSRealizes.add (I := I) hTstep hUstep

/-- Normalized iterated mixed-tensor covariant-derivative realizations are
homogeneous under constant scalar multiplication. -/
theorem IterNablaRSRealizes.smul [T2Space M] {r s k : ℕ}
    (c : Real)
    {cov : CovariantDerivative I E (TangentSpace I : M -> Type _)}
    {T : TensorRSField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) r s}
    {Tk : TensorRSField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) r (s + k)}
    (hT : IterNablaRSRealizes (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) cov T k Tk) :
    IterNablaRSRealizes (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      cov (c • T) k (c • Tk) := by
  induction k generalizing T with
  | zero =>
      cases hT
      exact IterNablaRSRealizes.zero
  | succ k ih =>
      rcases IterNablaRSRealizes.succ_inv (𝕜 := Real) (E := E) (H := H)
          (I := I) (M := M) (k := k) hT with ⟨Tprev, hTprev, hTstep⟩
      refine IterNablaRSRealizes.succ (ih hTprev) ?_
      exact TotalNablaRSRealizes.smul (I := I) c hTstep

/-- The zero mixed tensor field realizes all normalized iterated covariant
derivatives of the zero mixed tensor field. -/
theorem IterNablaRSRealizes.zero_field [T2Space M] {r s k : ℕ}
    {cov : CovariantDerivative I E (TangentSpace I : M -> Type _)} :
    IterNablaRSRealizes (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      cov
      (0 : TensorRSField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        (n := (∞ : WithTop ℕ∞)) r s)
      k
      (0 : TensorRSField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        (n := (∞ : WithTop ℕ∞)) r (s + k)) := by
  induction k with
  | zero =>
      exact IterNablaRSRealizes.zero
  | succ k ih =>
      refine IterNablaRSRealizes.succ ih ?_
      exact TotalNablaRSRealizes.zero (I := I) (r := r) (s := s + k) (cov := cov)

/-- Normalized iterated mixed-tensor covariant-derivative realizations commute
with finite sums. -/
theorem IterNablaRSRealizes.sum [T2Space M] {ι : Type*} {r s k : ℕ}
    {cov : CovariantDerivative I E (TangentSpace I : M -> Type _)}
    (S : Finset ι)
    (T : ι -> TensorRSField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) r s)
    (Tk : ι -> TensorRSField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) r (s + k))
    (hT : ∀ i, i ∈ S ->
      IterNablaRSRealizes (𝕜 := Real) (E := E) (H := H)
        (I := I) (M := M) cov (T i) k (Tk i)) :
    IterNablaRSRealizes (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      cov (Finset.sum S T) k (Finset.sum S Tk) := by
  classical
  revert hT
  refine Finset.induction_on S ?base ?step
  · intro _hT
    exact IterNablaRSRealizes.zero_field (I := I) (r := r) (s := s)
      (k := k) (cov := cov)
  · intro i A hi ih hT
    rw [Finset.sum_insert hi, Finset.sum_insert hi]
    exact IterNablaRSRealizes.add (I := I)
      (hT i (by simp [hi]))
      (ih fun j hj => hT j (by simp [hj]))

/-- Normalized iterated mixed-tensor covariant-derivative realizations commute
with finite weighted sums. -/
theorem IterNablaRSRealizes.sum_smul [T2Space M] {ι : Type*} {r s k : ℕ}
    {cov : CovariantDerivative I E (TangentSpace I : M -> Type _)}
    (S : Finset ι) (c : ι -> Real)
    (T : ι -> TensorRSField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) r s)
    (Tk : ι -> TensorRSField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) r (s + k))
    (hT : ∀ i, i ∈ S ->
      IterNablaRSRealizes (𝕜 := Real) (E := E) (H := H)
        (I := I) (M := M) cov (T i) k (Tk i)) :
    IterNablaRSRealizes (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      cov
      (Finset.sum S fun i => c i • T i)
      k
      (Finset.sum S fun i => c i • Tk i) := by
  exact IterNablaRSRealizes.sum (I := I) (M := M) (cov := cov) S
    (fun i => c i • T i) (fun i => c i • Tk i)
    (fun i hi => IterNablaRSRealizes.smul (I := I) (M := M)
      (c i) (hT i hi))

/-- Sum of two covariant derivative jets. -/
noncomputable def IterNabla0SJet.add [T2Space M] {s : ℕ}
    {cov : CovariantDerivative I E (TangentSpace I : M -> Type _)}
    {α β : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s}
    (Jα : IterNabla0SJet (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      cov α)
    (Jβ : IterNabla0SJet (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      cov β) :
    IterNabla0SJet (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      cov (α + β) where
  term k := Jα.term k + Jβ.term k
  zero_eq := by
    simp [Jα.zero_eq, Jβ.zero_eq]
  step k := TotalNabla0SRealizes.add (I := I) (Jα.step k) (Jβ.step k)

/-- Constant scalar multiple of a covariant derivative jet. -/
noncomputable def IterNabla0SJet.smul [T2Space M] {s : ℕ}
    (c : Real)
    {cov : CovariantDerivative I E (TangentSpace I : M -> Type _)}
    {α : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s}
    (Jα : IterNabla0SJet (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      cov α) :
    IterNabla0SJet (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      cov (c • α) where
  term k := c • Jα.term k
  zero_eq := by
    simp [Jα.zero_eq]
  step k := TotalNabla0SRealizes.smul (I := I) c (Jα.step k)

/-- Zero covariant derivative jet. -/
noncomputable def IterNabla0SJet.zero_field [T2Space M] {s : ℕ}
    {cov : CovariantDerivative I E (TangentSpace I : M -> Type _)} :
    IterNabla0SJet (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      cov
      (0 : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        (n := (∞ : WithTop ℕ∞)) s) where
  term _k := 0
  zero_eq := rfl
  step k := TotalNabla0SRealizes.zero (I := I) (s := s + k) (cov := cov)

/-- Finite sum of covariant derivative jets. -/
noncomputable def IterNabla0SJet.sum [T2Space M] {ι : Type*} {s : ℕ}
    {cov : CovariantDerivative I E (TangentSpace I : M -> Type _)}
    (S : Finset ι)
    (T : ι -> Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s)
    (J : ∀ i,
      IterNabla0SJet (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        cov (T i)) :
    IterNabla0SJet (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      cov (Finset.sum S T) where
  term k := Finset.sum S fun i => (J i).term k
  zero_eq := by
    exact Finset.sum_congr rfl (fun i _hi => (J i).zero_eq)
  step k := by
    refine TotalNabla0SRealizes.sum (I := I) (M := M)
      (S := S)
      (T := fun i => (J i).term k)
      (nablaT := fun i => (J i).term (k + 1))
      ?_
    intro i hi
    exact (J i).step k

/-- Finite weighted sum of covariant derivative jets. -/
noncomputable def IterNabla0SJet.sum_smul [T2Space M] {ι : Type*} {s : ℕ}
    {cov : CovariantDerivative I E (TangentSpace I : M -> Type _)}
    (S : Finset ι) (c : ι -> Real)
    (T : ι -> Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s)
    (J : ∀ i,
      IterNabla0SJet (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        cov (T i)) :
    IterNabla0SJet (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      cov (Finset.sum S fun i => c i • T i) :=
  IterNabla0SJet.sum (I := I) (M := M) (cov := cov) S
    (fun i => c i • T i)
    (fun i => IterNabla0SJet.smul (I := I) (M := M) (c i) (J i))

/-- Sum of two mixed tensor derivative jets. -/
noncomputable def IterNablaRSJet.add [T2Space M] {r s : ℕ}
    {cov : CovariantDerivative I E (TangentSpace I : M -> Type _)}
    {T U : TensorRSField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) r s}
    (JT : IterNablaRSJet (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      cov T)
    (JU : IterNablaRSJet (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      cov U) :
    IterNablaRSJet (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      cov (T + U) where
  term k := JT.term k + JU.term k
  zero_eq := by
    simp [JT.zero_eq, JU.zero_eq]
  step k := TotalNablaRSRealizes.add (I := I) (JT.step k) (JU.step k)

/-- Constant scalar multiple of a mixed tensor derivative jet. -/
noncomputable def IterNablaRSJet.smul [T2Space M] {r s : ℕ}
    (c : Real)
    {cov : CovariantDerivative I E (TangentSpace I : M -> Type _)}
    {T : TensorRSField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) r s}
    (JT : IterNablaRSJet (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      cov T) :
    IterNablaRSJet (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      cov (c • T) where
  term k := c • JT.term k
  zero_eq := by
    simp [JT.zero_eq]
  step k := TotalNablaRSRealizes.smul (I := I) c (JT.step k)

/-- Zero mixed tensor derivative jet. -/
noncomputable def IterNablaRSJet.zero_field [T2Space M] {r s : ℕ}
    {cov : CovariantDerivative I E (TangentSpace I : M -> Type _)} :
    IterNablaRSJet (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      cov
      (0 : TensorRSField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        (n := (∞ : WithTop ℕ∞)) r s) where
  term _k := 0
  zero_eq := rfl
  step k := TotalNablaRSRealizes.zero (I := I) (r := r) (s := s + k) (cov := cov)

/-- Finite sum of mixed tensor derivative jets. -/
noncomputable def IterNablaRSJet.sum [T2Space M] {ι : Type*} {r s : ℕ}
    {cov : CovariantDerivative I E (TangentSpace I : M -> Type _)}
    (S : Finset ι)
    (T : ι -> TensorRSField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) r s)
    (J : ∀ i,
      IterNablaRSJet (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        cov (T i)) :
    IterNablaRSJet (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      cov (Finset.sum S T) where
  term k := Finset.sum S fun i => (J i).term k
  zero_eq := by
    exact Finset.sum_congr rfl (fun i _hi => (J i).zero_eq)
  step k := by
    refine TotalNablaRSRealizes.sum (I := I) (M := M)
      (S := S)
      (T := fun i => (J i).term k)
      (nablaT := fun i => (J i).term (k + 1))
      ?_
    intro i hi
    exact (J i).step k

/-- Finite weighted sum of mixed tensor derivative jets. -/
noncomputable def IterNablaRSJet.sum_smul [T2Space M] {ι : Type*} {r s : ℕ}
    {cov : CovariantDerivative I E (TangentSpace I : M -> Type _)}
    (S : Finset ι) (c : ι -> Real)
    (T : ι -> TensorRSField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) r s)
    (J : ∀ i,
      IterNablaRSJet (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        cov (T i)) :
    IterNablaRSJet (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      cov (Finset.sum S fun i => c i • T i) :=
  IterNablaRSJet.sum (I := I) (M := M) (cov := cov) S
    (fun i => c i • T i)
    (fun i => IterNablaRSJet.smul (I := I) (M := M) (c i) (J i))

end RealLinearity

end Tensor0SBundle
