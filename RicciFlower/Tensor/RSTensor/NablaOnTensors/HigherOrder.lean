import RicciFlower.Tensor.RSTensor.NablaOnTensors.RawDefs
import RicciFlower.Tensor.RSTensor.CoordinateBasis
import RicciFlower.Tensor.RSTensor.NablaOnTensors.Connection.Endomorphism
import RicciFlower.Tensor.RSTensor.NablaOnTensors.Regularity.Tensor0S
import RicciFlower.VectorBundle.PartialMfderiv

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

end RealLinearity

end Tensor0SBundle
