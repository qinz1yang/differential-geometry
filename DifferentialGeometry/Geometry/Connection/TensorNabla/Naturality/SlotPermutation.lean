import DifferentialGeometry.Geometry.Connection.TensorNabla.Iterated.Linearity
import DifferentialGeometry.Tensor.Multilinear.Bundle.DomainPermutation

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry
namespace Tensor0SBundle


open scoped Manifold ContDiff BigOperators
open Bundle

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [CompleteSpace E] [IsManifold I ∞ M]

def frontExtendEquiv {s s' : ℕ} (e : Fin s ≃ Fin s') : Fin (s + 1) ≃ Fin (s' + 1) :=
  (finSuccEquiv s).trans ((Equiv.optionCongr e).trans (finSuccEquiv s').symm)

@[simp] theorem frontExtendEquiv_zero {s s' : ℕ} (e : Fin s ≃ Fin s') :
    frontExtendEquiv e 0 = 0 := by
  simp [frontExtendEquiv]

@[simp] theorem frontExtendEquiv_succ {s s' : ℕ} (e : Fin s ≃ Fin s') (i : Fin s) :
    frontExtendEquiv e i.succ = (e i).succ := by
  simp [frontExtendEquiv]

@[simp] theorem cons_apply_frontExtendEquiv {s s' : ℕ} (e : Fin s ≃ Fin s')
    {α : Type*} (c : α) (g : Fin s' → α) (i : Fin (s + 1)) :
    (Fin.cons c g : Fin (s' + 1) → α) (frontExtendEquiv e i)
      = (Fin.cons c (g ∘ e) : Fin (s + 1) → α) i := by
  rcases Fin.eq_zero_or_eq_succ i with h | ⟨j, h⟩
  · subst h; rw [frontExtendEquiv_zero, Fin.cons_zero, Fin.cons_zero]
  · subst h; rw [frontExtendEquiv_succ, Fin.cons_succ, Fin.cons_succ, Function.comp_apply]

omit [CompleteSpace E] in
theorem nabla0SFun_domDomCongr [T2Space M] [IsManifold I 1 M] [IsManifold I 2 M]
    {s s' : ℕ}
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (e : Fin s ≃ Fin s')
    (Z : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s)
    (x : M) (slots : Fin s' -> TangentSpace I x) :
    (nabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) s' cov X
        (Tensor0SField.domDomCongr (∞ : WithTop ℕ∞) e Z) x) slots
      = (nabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) s cov X Z x)
          (slots ∘ e) := by
  classical
  let V : Fin s' -> ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M -> Type _) :=
    fun a =>
      (ContMDiffSection.exists_eq_at
        (I := I) (F := E) (V := TangentSpace I) (n := (⊤ : ℕ∞))
        x (slots a)).choose
  have hV : ∀ a : Fin s', V a x = slots a := fun a =>
    (ContMDiffSection.exists_eq_at
      (I := I) (F := E) (V := TangentSpace I) (n := (⊤ : ℕ∞))
      x (slots a)).choose_spec
  have h1 := nabla0SFun_eval_smooth_slots (I := I) cov X V
    (Tensor0SField.domDomCongr (∞ : WithTop ℕ∞) e Z) x
  have h2 := nabla0SFun_eval_smooth_slots (I := I) cov X (fun a : Fin s => V (e a)) Z x
  rw [show slots = (fun a : Fin s' => V a x) from (funext hV).symm, h1,
    show ((fun a : Fin s' => V a x) ∘ e) = (fun a : Fin s => V (e a) x) from rfl, h2]
  refine congrArg₂ (· - ·) ?_ ?_
  · congr 1
  · refine Fintype.sum_equiv e.symm _ _ ?_
    intro a
    change (ContinuousMultilinearMap.domDomCongr e
      (tensor0SSpaceFiberContinuousLinearEquiv (I := I) s x (Z x))) _ = _
    rw [ContinuousMultilinearMap.domDomCongr_apply]
    simp only [tensor0SSpaceFiberContinuousLinearEquiv_apply_apply]
    congr 1
    funext i
    simp only [Function.update_apply, Equiv.apply_symm_apply,
      Equiv.eq_symm_apply]

omit [CompleteSpace E] in
theorem totalNabla0SFun_domDomCongr [T2Space M] [IsManifold I 1 M] [IsManifold I 2 M]
    {s s' : ℕ}
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (e : Fin s ≃ Fin s')
    (Z : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s)
    (x : M) :
    totalNabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) s' cov
        (Tensor0SField.domDomCongr (∞ : WithTop ℕ∞) e Z) x
      = (totalNabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
          s cov Z x).domDomCongr (frontExtendEquiv e) := by
  classical
  let Z' : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s' :=
    Tensor0SField.domDomCongr (∞ : WithTop ℕ∞) e Z
  change totalNabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      s' cov Z' x = _
  let basis : Module.Basis (Fin (Module.finrank Real (TangentSpace I x))) Real
      (TangentSpace I x) :=
    Module.finBasis Real (TangentSpace I x)
  apply ext0S_basis (I := I) basis
  intro idx
  let X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _) :=
    (ContMDiffSection.exists_eq_at
      (I := I) (F := E) (V := TangentSpace I) (n := (⊤ : ℕ∞))
      x (basis (idx 0))).choose
  have hX : X x = basis (idx 0) :=
    (ContMDiffSection.exists_eq_at
      (I := I) (F := E) (V := TangentSpace I) (n := (⊤ : ℕ∞))
      x (basis (idx 0))).choose_spec
  have hcons :
      (fun a : Fin (s' + 1) => basis (idx a))
        = Fin.cons (X x) (fun a : Fin s' => basis (idx a.succ)) := by
    funext a
    induction a using Fin.cases with
    | zero => rw [Fin.cons_zero]; exact hX.symm
    | succ j => rw [Fin.cons_succ]
  rw [component0S_apply, component0S_apply, hcons,
    totalNabla0SFun_apply_section]
  have hperm :
      nabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
          s' cov X Z' x (fun a : Fin s' => basis (idx a.succ)) =
        nabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
          s cov X Z x ((fun a : Fin s' => basis (idx a.succ)) ∘ e) := by
    exact nabla0SFun_domDomCongr (I := I) cov X e Z x
      (fun a : Fin s' => basis (idx a.succ))
  rw [hperm, Tensor0SSpace.domDomCongr_apply]
  simp only [cons_apply_frontExtendEquiv]
  rw [totalNabla0SFun_apply_section]

omit [CompleteSpace E] in
theorem totalNabla0SRealizes_domDomCongr [T2Space M] [IsManifold I 1 M] [IsManifold I 2 M]
    {s s' : ℕ}
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (e : Fin s ≃ Fin s')
    (Z : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s)
    (nablaZ : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) (s + 1))
    (hZ : TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      s cov Z nablaZ) :
    TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      s' cov
      (Tensor0SField.domDomCongr (∞ : WithTop ℕ∞) e Z)
      (Tensor0SField.domDomCongr (∞ : WithTop ℕ∞) (frontExtendEquiv e) nablaZ) := by
  intro X x slots
  change (nablaZ x).domDomCongr (frontExtendEquiv e) (Fin.cons (X x) slots) = _
  rw [Tensor0SSpace.domDomCongr_apply]
  simp only [cons_apply_frontExtendEquiv]
  exact (hZ X x (slots ∘ e)).trans
    (nabla0SFun_domDomCongr (I := I) cov X e Z x slots).symm

omit [CompleteSpace E] in
theorem totalNabla0SRealizes_unique [T2Space M] {s : ℕ}
    {cov : CovariantDerivative I E (TangentSpace I : M -> Type _)}
    {α : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s}
    {n1 n2 : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) (s + 1)}
    (h1 : TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) s cov α n1)
    (h2 : TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) s cov α n2) :
    n1 = n2 := by
  refine DFunLike.ext _ _ (fun x => ?_)
  refine tensor0SSpace_ext (I := I) (s + 1) x (fun v => ?_)
  obtain ⟨X, hX⟩ :
      ∃ X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _),
        X x = v 0 :=
    ⟨(ContMDiffSection.exists_eq_at (I := I) (F := E) (V := TangentSpace I)
        (n := (⊤ : ℕ∞)) x (v 0)).choose,
      (ContMDiffSection.exists_eq_at (I := I) (F := E) (V := TangentSpace I)
        (n := (⊤ : ℕ∞)) x (v 0)).choose_spec⟩
  have hcons : Fin.cons (X x) (Fin.tail v) = v := by
    rw [hX]; exact Fin.cons_self_tail v
  have e1 := h1 X x (Fin.tail v)
  have e2 := h2 X x (Fin.tail v)
  rw [hcons] at e1 e2
  exact e1.trans e2.symm

end Tensor0SBundle
end DifferentialGeometry
