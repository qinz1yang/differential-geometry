import DifferentialGeometry.Geometry.Connection.TensorNabla.Tensor0S.Algebra.ContractionLeibniz
import DifferentialGeometry.Geometry.Connection.TensorNabla.Naturality.SlotPermutation
import DifferentialGeometry.Tensor.Multilinear.Bundle.DomainPermutation
import DifferentialGeometry.Tensor.RSTensor.Algebra.Product
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Slope

set_option autoImplicit false

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

noncomputable def leibnizRightEquiv (s q : ℕ) : Fin (s + (q + 1)) ≃ Fin (s + q + 1) :=
  (finCongr (by omega : s + (q + 1) = s + q + 1)).trans
    (Fin.cycleRange ⟨s, by omega⟩)

def leibnizLeftEquiv (s q : ℕ) : Fin (s + 1 + q) ≃ Fin (s + q + 1) :=
  finCongr (by omega)

omit [CompleteSpace E] in
theorem nabla0S_product_realizes {s q : ℕ}
    [T2Space M] [IsManifold I 1 M] [IsManifold I 2 M]
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (A : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s)
    (B : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) q)
    (nablaA : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) (s + 1))
    (nablaB : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) (q + 1))
    (hA : TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      s cov A nablaA)
    (hB : TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      q cov B nablaB) :
    TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (s + q) cov
      (tensor0SFieldProduct (∞ : WithTop ℕ∞) A B)
      (Tensor0SField.domDomCongr (∞ : WithTop ℕ∞) (leibnizLeftEquiv s q)
          (tensor0SFieldProduct (∞ : WithTop ℕ∞) nablaA B)
        + Tensor0SField.domDomCongr (∞ : WithTop ℕ∞) (leibnizRightEquiv s q)
          (tensor0SFieldProduct (∞ : WithTop ℕ∞) A nablaB)) := by
  classical
  intro X x slots
  let V : Fin (s + q) -> ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M -> Type _) :=
    fun a =>
      (ContMDiffSection.exists_eq_at
        (I := I) (F := E) (V := TangentSpace I) (n := (⊤ : ℕ∞))
        x (slots a)).choose
  have hV : ∀ a : Fin (s + q), V a x = slots a := fun a =>
    (ContMDiffSection.exists_eq_at
      (I := I) (F := E) (V := TangentSpace I) (n := (⊤ : ℕ∞))
      x (slots a)).choose_spec
  have hslots : (fun a : Fin (s + q) => V a x) = slots := funext hV
  have hmain :=
    nabla0SFun_product_eval (I := I) cov A B nablaA nablaB hA hB X V x
  rw [show slots = (fun a : Fin (s + q) => V a x) from hslots.symm, hmain]
  change
    (Tensor0SSpace.domDomCongr
        (tensor0SFieldProduct (∞ : WithTop ℕ∞) nablaA B x)
        (leibnizLeftEquiv s q))
        (Fin.cons (X x) (fun a : Fin (s + q) => V a x)) +
      (Tensor0SSpace.domDomCongr
        (tensor0SFieldProduct (∞ : WithTop ℕ∞) A nablaB x)
        (leibnizRightEquiv s q))
        (Fin.cons (X x) (fun a : Fin (s + q) => V a x)) = _
  rw [Tensor0SSpace.domDomCongr_apply, Tensor0SSpace.domDomCongr_apply,
    tensor0SField_product_apply, tensor0SField_product_apply]
  refine congrArg₂ (· + ·)
    (congrArg₂ (· * ·) (congrArg (nablaA x) ?_) (congrArg (B x) ?_))
    (congrArg₂ (· * ·) (congrArg (A x) ?_) (congrArg (nablaB x) ?_))
  · funext a
    refine Fin.cases ?_ (fun a => ?_) a
    · simp only [leibnizLeftEquiv, Function.comp_apply, finCongr_apply, Fin.cons_zero]
      rw [show (Fin.cast (by omega : s + 1 + q = s + q + 1) (Fin.castAdd q (0 : Fin (s + 1))))
            = (0 : Fin (s + q + 1)) from by
        ext; simp only [Fin.val_cast, Fin.val_castAdd, Fin.val_zero]]
      exact Fin.cons_zero _ _
    · simp only [leibnizLeftEquiv, Function.comp_apply, finCongr_apply]
      rw [show (Fin.cast (by omega : s + 1 + q = s + q + 1) (Fin.castAdd q a.succ))
            = (Fin.castAdd q a).succ from by
        ext; simp only [Fin.val_cast, Fin.val_castAdd, Fin.val_succ]]
      simp only [Fin.cons_succ]
  · funext a
    simp only [leibnizLeftEquiv, finCongr_apply, Function.comp_apply]
    rw [show (Fin.cast (by omega : s + 1 + q = s + q + 1) (Fin.natAdd (s + 1) a))
          = (Fin.natAdd s a).succ from by
      ext; simp only [Fin.val_cast, Fin.val_natAdd, Fin.val_succ]; omega]
    rw [Fin.cons_succ]
  · funext a
    have hidx : leibnizRightEquiv s q (Fin.castAdd (q + 1) a) = (Fin.castAdd q a).succ := by
      rw [leibnizRightEquiv, Equiv.trans_apply, finCongr_apply,
        show (Fin.cast (by omega : s + (q + 1) = s + q + 1) (Fin.castAdd (q + 1) a))
            = (⟨a, by omega⟩ : Fin (s + q + 1)) from by ext; simp,
        Fin.cycleRange_of_lt (by simp only [Fin.lt_def]; omega)]
      ext
      rw [Fin.val_add_one_of_lt (by simp only [Fin.lt_def, Fin.val_last]; omega)]
      simp [Fin.val_succ]
    simp only [Function.comp_apply, hidx, Fin.cons_succ]
  · funext a
    refine Fin.cases ?_ (fun a => ?_) a
    · have hidx : leibnizRightEquiv s q (Fin.natAdd s (0 : Fin (q + 1))) = 0 := by
        rw [leibnizRightEquiv, Equiv.trans_apply, finCongr_apply,
          show (Fin.cast (by omega : s + (q + 1) = s + q + 1) (Fin.natAdd s (0 : Fin (q + 1))))
              = (⟨s, by omega⟩ : Fin (s + q + 1)) from by ext; simp,
          Fin.cycleRange_self]
      simp only [Function.comp_apply, hidx, Fin.cons_zero]
    · have hidx : leibnizRightEquiv s q (Fin.natAdd s a.succ) = (Fin.natAdd s a).succ := by
        rw [leibnizRightEquiv, Equiv.trans_apply, finCongr_apply,
          show (Fin.cast (by omega : s + (q + 1) = s + q + 1) (Fin.natAdd s a.succ))
              = (⟨s + 1 + a, by omega⟩ : Fin (s + q + 1)) from by
            ext; simp [Fin.val_succ]; omega,
          Fin.cycleRange_of_gt (by simp only [Fin.lt_def]; omega)]
        ext; simp [Fin.val_succ]; omega
      simp only [Function.comp_apply, hidx, Fin.cons_succ]

noncomputable def tensor0SProductNabla
    {p q : Nat}
    (A : Tensor0SField (E := E) (H := H) (I := I) (M := M) ∞ p)
    (nablaA : Tensor0SField (E := E) (H := H) (I := I) (M := M) ∞ (p + 1))
    (B : Tensor0SField (E := E) (H := H) (I := I) (M := M) ∞ q)
    (nablaB : Tensor0SField (E := E) (H := H) (I := I) (M := M) ∞ (q + 1)) :
    Tensor0SField (E := E) (H := H) (I := I) (M := M) ∞ (p + q + 1) :=
  Tensor0SField.domDomCongr ∞ (leibnizLeftEquiv p q)
      (tensor0SFieldProduct ∞ nablaA B) +
    Tensor0SField.domDomCongr ∞ (leibnizRightEquiv p q)
      (tensor0SFieldProduct ∞ A nablaB)

omit [CompleteSpace E] in
theorem tensor0SProductNabla_realizes
    {p q : Nat} [T2Space M]
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (A : Tensor0SField (E := E) (H := H) (I := I) (M := M) ∞ p)
    (nablaA : Tensor0SField (E := E) (H := H) (I := I) (M := M) ∞ (p + 1))
    (B : Tensor0SField (E := E) (H := H) (I := I) (M := M) ∞ q)
    (nablaB : Tensor0SField (E := E) (H := H) (I := I) (M := M) ∞ (q + 1))
    (hA : TotalNabla0SRealizes p cov A nablaA)
    (hB : TotalNabla0SRealizes q cov B nablaB) :
    TotalNabla0SRealizes (p + q) cov (tensor0SFieldProduct ∞ A B)
      (tensor0SProductNabla A nablaA B nablaB) := by
  exact nabla0S_product_realizes cov A B nablaA nablaB hA hB

omit [CompleteSpace E] in
theorem tensor0SProductNabla_apply
    {p q : Nat}
    (A : Tensor0SField (E := E) (H := H) (I := I) (M := M) ∞ p)
    (nablaA : Tensor0SField (E := E) (H := H) (I := I) (M := M) ∞ (p + 1))
    (B : Tensor0SField (E := E) (H := H) (I := I) (M := M) ∞ q)
    (nablaB : Tensor0SField (E := E) (H := H) (I := I) (M := M) ∞ (q + 1))
    (x : M) (X : TangentSpace I x)
    (vA : Fin p -> TangentSpace I x) (vB : Fin q -> TangentSpace I x) :
    tensor0SProductNabla A nablaA B nablaB x
        (Fin.cons X (Fin.append vA vB)) =
      nablaA x (Fin.cons X vA) * B x vB +
        A x vA * nablaB x (Fin.cons X vB) := by
  simp only [tensor0SProductNabla, ContMDiffSection.coe_add, Pi.add_apply,
    Tensor0SSpace.add_apply, Tensor0SField.domDomCongr_apply,
    Tensor0SSpace.domDomCongr_apply, tensor0SField_product_apply]
  refine congrArg₂ (· + ·)
    (congrArg₂ (· * ·) (congrArg (nablaA x) ?_) (congrArg (B x) ?_))
    (congrArg₂ (· * ·) (congrArg (A x) ?_) (congrArg (nablaB x) ?_))
  · funext i
    refine Fin.cases ?_ (fun a => ?_) i
    · simp only [Function.comp_apply, leibnizLeftEquiv, finCongr_apply,
        Fin.cons_zero]
      rw [show (Fin.cast (by omega : p + 1 + q = p + q + 1)
          (Fin.castAdd q (0 : Fin (p + 1)))) = (0 : Fin (p + q + 1)) from by
        ext
        simp]
      simp
    · simp only [Function.comp_apply, leibnizLeftEquiv, finCongr_apply]
      rw [show (Fin.cast (by omega : p + 1 + q = p + q + 1)
          (Fin.castAdd q a.succ)) = (Fin.castAdd q a).succ from by
        ext
        simp]
      simp [Fin.append]
  · funext i
    simp only [Function.comp_apply, leibnizLeftEquiv, finCongr_apply]
    rw [show (Fin.cast (by omega : p + 1 + q = p + q + 1)
        (Fin.natAdd (p + 1) i)) = (Fin.natAdd p i).succ from by
      ext
      simp [Fin.val_succ]
      omega]
    simp [Fin.append]
  · funext i
    simp only [Function.comp_apply]
    have hidx : leibnizRightEquiv p q (Fin.castAdd (q + 1) i) =
        (Fin.castAdd q i).succ := by
      rw [leibnizRightEquiv, Equiv.trans_apply, finCongr_apply,
        show (Fin.cast (by omega : p + (q + 1) = p + q + 1)
            (Fin.castAdd (q + 1) i)) = (⟨i, by omega⟩ : Fin (p + q + 1)) from by
          ext
          simp,
        Fin.cycleRange_of_lt (by simp only [Fin.lt_def]; omega)]
      ext
      rw [Fin.val_add_one_of_lt (by simp only [Fin.lt_def, Fin.val_last]; omega)]
      simp [Fin.val_succ]
    rw [hidx]
    simp [Fin.append]
  · funext i
    refine Fin.cases ?_ (fun a => ?_) i
    · simp only [Function.comp_apply]
      have hidx : leibnizRightEquiv p q (Fin.natAdd p (0 : Fin (q + 1))) = 0 := by
        rw [leibnizRightEquiv, Equiv.trans_apply, finCongr_apply,
          show (Fin.cast (by omega : p + (q + 1) = p + q + 1)
              (Fin.natAdd p (0 : Fin (q + 1)))) = (⟨p, by omega⟩ : Fin (p + q + 1)) from by
            ext
            simp,
          Fin.cycleRange_self]
      rw [hidx]
      simp
    · simp only [Function.comp_apply]
      have hidx : leibnizRightEquiv p q (Fin.natAdd p a.succ) =
          (Fin.natAdd p a).succ := by
        rw [leibnizRightEquiv, Equiv.trans_apply, finCongr_apply,
          show (Fin.cast (by omega : p + (q + 1) = p + q + 1)
              (Fin.natAdd p a.succ)) = (⟨p + 1 + a, by omega⟩ : Fin (p + q + 1)) from by
            ext
            simp [Fin.val_succ]
            omega,
          Fin.cycleRange_of_gt (by simp only [Fin.lt_def]; omega)]
        ext
        simp [Fin.val_succ]
        omega
      rw [hidx]
      simp [Fin.append]

private theorem cons_append_comp_leibnizLeft
    {p q : Nat} {Z : Type*} (X : Z) (vA : Fin p -> Z) (vB : Fin q -> Z) :
    (Fin.cons X (Fin.append vA vB)) ∘ leibnizLeftEquiv p q =
      Fin.append (Fin.cons X vA) vB := by
  funext i
  refine Fin.addCases ?_ ?_ i
  · intro j
    refine Fin.cases ?_ (fun a => ?_) j
    · simp only [Function.comp_apply]
      rw [show leibnizLeftEquiv p q (Fin.castAdd q (0 : Fin (p + 1))) =
          (0 : Fin (p + q + 1)) from by
        rw [leibnizLeftEquiv, finCongr_apply]
        ext
        simp]
      simp [Fin.append]
    · simp only [Function.comp_apply]
      rw [show leibnizLeftEquiv p q (Fin.castAdd q a.succ) =
          (Fin.castAdd q a).succ from by
        rw [leibnizLeftEquiv, finCongr_apply]
        ext
        simp]
      simp [Fin.append]
  · intro j
    simp only [Function.comp_apply]
    rw [show leibnizLeftEquiv p q (Fin.natAdd (p + 1) j) =
          (Fin.natAdd p j).succ from by
      rw [leibnizLeftEquiv, finCongr_apply]
      ext
      simp [Fin.val_succ]
      omega]
    simp [Fin.append]

private theorem cons_append_comp_leibnizRight
    {p q : Nat} {Z : Type*} (X : Z) (vA : Fin p -> Z) (vB : Fin q -> Z) :
    (Fin.cons X (Fin.append vA vB)) ∘ leibnizRightEquiv p q =
      Fin.append vA (Fin.cons X vB) := by
  funext i
  refine Fin.addCases ?_ ?_ i
  · intro j
    simp only [Function.comp_apply]
    have hidx : leibnizRightEquiv p q (Fin.castAdd (q + 1) j) =
        (Fin.castAdd q j).succ := by
      rw [leibnizRightEquiv, Equiv.trans_apply, finCongr_apply,
        show (Fin.cast (by omega : p + (q + 1) = p + q + 1)
            (Fin.castAdd (q + 1) j)) = (⟨j, by omega⟩ : Fin (p + q + 1)) from by
          ext
          simp,
        Fin.cycleRange_of_lt (by simp only [Fin.lt_def]; omega)]
      ext
      rw [Fin.val_add_one_of_lt (by simp only [Fin.lt_def, Fin.val_last]; omega)]
      simp [Fin.val_succ]
    rw [hidx]
    simp [Fin.append]
  · intro j
    refine Fin.cases ?_ (fun a => ?_) j
    · simp only [Function.comp_apply]
      have hidx : leibnizRightEquiv p q
          (Fin.natAdd p (0 : Fin (q + 1))) = 0 := by
        rw [leibnizRightEquiv, Equiv.trans_apply, finCongr_apply,
          show (Fin.cast (by omega : p + (q + 1) = p + q + 1)
              (Fin.natAdd p (0 : Fin (q + 1)))) =
              (⟨p, by omega⟩ : Fin (p + q + 1)) from by
            ext
            simp,
          Fin.cycleRange_self]
      rw [hidx]
      simp [Fin.append]
    · simp only [Function.comp_apply]
      have hidx : leibnizRightEquiv p q (Fin.natAdd p a.succ) =
          (Fin.natAdd p a).succ := by
        rw [leibnizRightEquiv, Equiv.trans_apply, finCongr_apply,
          show (Fin.cast (by omega : p + (q + 1) = p + q + 1)
              (Fin.natAdd p a.succ)) =
              (⟨p + 1 + a, by omega⟩ : Fin (p + q + 1)) from by
            ext
            simp [Fin.val_succ]
            omega,
          Fin.cycleRange_of_gt (by simp only [Fin.lt_def]; omega)]
        ext
        simp [Fin.val_succ]
        omega
      rw [hidx]
      simp [Fin.append]

noncomputable def tensor0SProductNabla2
    {p q : Nat}
    (A : Tensor0SField (E := E) (H := H) (I := I) (M := M) ∞ p)
    (nablaA : Tensor0SField (E := E) (H := H) (I := I) (M := M) ∞ (p + 1))
    (nabla2A : Tensor0SField (E := E) (H := H) (I := I) (M := M) ∞ (p + 2))
    (B : Tensor0SField (E := E) (H := H) (I := I) (M := M) ∞ q)
    (nablaB : Tensor0SField (E := E) (H := H) (I := I) (M := M) ∞ (q + 1))
    (nabla2B : Tensor0SField (E := E) (H := H) (I := I) (M := M) ∞ (q + 2)) :
    Tensor0SField (E := E) (H := H) (I := I) (M := M) ∞ (p + q + 2) :=
  Tensor0SField.domDomCongr ∞ (frontExtendEquiv (leibnizLeftEquiv p q))
      (tensor0SProductNabla nablaA nabla2A B nablaB) +
    Tensor0SField.domDomCongr ∞ (frontExtendEquiv (leibnizRightEquiv p q))
      (tensor0SProductNabla A nablaA nablaB nabla2B)

omit [CompleteSpace E] in
theorem tensor0SProductNabla2_apply
    {p q : Nat}
    (A : Tensor0SField (E := E) (H := H) (I := I) (M := M) ∞ p)
    (nablaA : Tensor0SField (E := E) (H := H) (I := I) (M := M) ∞ (p + 1))
    (nabla2A : Tensor0SField (E := E) (H := H) (I := I) (M := M) ∞ (p + 2))
    (B : Tensor0SField (E := E) (H := H) (I := I) (M := M) ∞ q)
    (nablaB : Tensor0SField (E := E) (H := H) (I := I) (M := M) ∞ (q + 1))
    (nabla2B : Tensor0SField (E := E) (H := H) (I := I) (M := M) ∞ (q + 2))
    (x : M) (X Y : TangentSpace I x)
    (vA : Fin p -> TangentSpace I x) (vB : Fin q -> TangentSpace I x) :
    tensor0SProductNabla2 A nablaA nabla2A B nablaB nabla2B x
        (Fin.cons X (Fin.cons Y (Fin.append vA vB))) =
      nabla2A x (Fin.cons X (Fin.cons Y vA)) * B x vB +
        nablaA x (Fin.cons Y vA) * nablaB x (Fin.cons X vB) +
        nablaA x (Fin.cons X vA) * nablaB x (Fin.cons Y vB) +
        A x vA * nabla2B x (Fin.cons X (Fin.cons Y vB)) := by
  have hleft :
      (Fin.cons X (Fin.cons Y (Fin.append vA vB))) ∘
          frontExtendEquiv (leibnizLeftEquiv p q) =
        Fin.cons X (Fin.append (Fin.cons Y vA) vB) := by
    funext i
    simp only [Function.comp_apply]
    rw [cons_apply_frontExtendEquiv]
    rw [cons_append_comp_leibnizLeft]
  have hright :
      (Fin.cons X (Fin.cons Y (Fin.append vA vB))) ∘
          frontExtendEquiv (leibnizRightEquiv p q) =
        Fin.cons X (Fin.append vA (Fin.cons Y vB)) := by
    funext i
    simp only [Function.comp_apply]
    rw [cons_apply_frontExtendEquiv]
    rw [cons_append_comp_leibnizRight]
  simp only [tensor0SProductNabla2, ContMDiffSection.coe_add, Pi.add_apply,
    Tensor0SSpace.add_apply, Tensor0SField.domDomCongr_apply,
    Tensor0SSpace.domDomCongr_apply]
  change
    tensor0SProductNabla nablaA nabla2A B nablaB x
          ((Fin.cons X (Fin.cons Y (Fin.append vA vB))) ∘
            frontExtendEquiv (leibnizLeftEquiv p q)) +
        tensor0SProductNabla A nablaA nablaB nabla2B x
          ((Fin.cons X (Fin.cons Y (Fin.append vA vB))) ∘
            frontExtendEquiv (leibnizRightEquiv p q)) = _
  rw [hleft, hright,
    tensor0SProductNabla_apply nablaA nabla2A B nablaB x X
      (Fin.cons Y vA) vB,
    tensor0SProductNabla_apply A nablaA nablaB nabla2B x X
      vA (Fin.cons Y vB)]
  ring

omit [CompleteSpace E] in
theorem tensor0SProductNabla2_realizes
    {p q : Nat} [T2Space M]
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (A : Tensor0SField (E := E) (H := H) (I := I) (M := M) ∞ p)
    (nablaA : Tensor0SField (E := E) (H := H) (I := I) (M := M) ∞ (p + 1))
    (nabla2A : Tensor0SField (E := E) (H := H) (I := I) (M := M) ∞ (p + 2))
    (B : Tensor0SField (E := E) (H := H) (I := I) (M := M) ∞ q)
    (nablaB : Tensor0SField (E := E) (H := H) (I := I) (M := M) ∞ (q + 1))
    (nabla2B : Tensor0SField (E := E) (H := H) (I := I) (M := M) ∞ (q + 2))
    (hA : TotalNabla0SRealizes p cov A nablaA)
    (h2A : TotalNabla0SRealizes (p + 1) cov nablaA nabla2A)
    (hB : TotalNabla0SRealizes q cov B nablaB)
    (h2B : TotalNabla0SRealizes (q + 1) cov nablaB nabla2B) :
    TotalNabla0SRealizes (p + q + 1) cov
      (tensor0SProductNabla A nablaA B nablaB)
      (tensor0SProductNabla2 A nablaA nabla2A B nablaB nabla2B) := by
  have hleftProd := tensor0SProductNabla_realizes cov
    nablaA nabla2A B nablaB h2A hB
  have hleft := totalNabla0SRealizes_domDomCongr cov
    (leibnizLeftEquiv p q)
    (tensor0SFieldProduct ∞ nablaA B)
    (tensor0SProductNabla nablaA nabla2A B nablaB) hleftProd
  have hrightProd := tensor0SProductNabla_realizes cov
    A nablaA nablaB nabla2B hA h2B
  have hright := totalNabla0SRealizes_domDomCongr cov
    (leibnizRightEquiv p q)
    (tensor0SFieldProduct ∞ A nablaB)
    (tensor0SProductNabla A nablaA nablaB nabla2B) hrightProd
  have hsum := TotalNabla0SRealizes.add hleft hright
  simpa only [tensor0SProductNabla, tensor0SProductNabla2] using hsum

omit [CompleteSpace E] in
theorem tensor0SFieldProduct_hasDerivAt
    {p q : Nat} {t : Real} {x : M}
    (A : Real -> Tensor0SField (E := E) (H := H) (I := I) (M := M) ∞ p)
    (B : Real -> Tensor0SField (E := E) (H := H) (I := I) (M := M) ∞ q)
    (Adot : Tensor0SSpace p I x) (Bdot : Tensor0SSpace q I x)
    (hAt : forall v : Fin p -> TangentSpace I x,
      HasDerivAt (fun r : Real => A r x v) (Adot v) t)
    (hBt : forall v : Fin q -> TangentSpace I x,
      HasDerivAt (fun r : Real => B r x v) (Bdot v) t)
    (v : Fin (p + q) -> TangentSpace I x) :
    HasDerivAt
      (fun r : Real => tensor0SFieldProduct ∞ (A r) (B r) x v)
      ((Adot.product (B t x) + (A t x).product Bdot) v) t := by
  simp only [tensor0SField_product_apply, Tensor0SSpace.add_apply,
    Tensor0SSpace.product_apply]
  apply hasDerivAt_iff_tendsto_slope.mpr
  have hmul :=
    (hAt (v ∘ Fin.castAdd q)).mul (hBt (v ∘ Fin.natAdd p))
  have hslope := hasDerivAt_iff_tendsto_slope.mp hmul
  convert hslope using 1
  funext r
  rfl


end Tensor0SBundle
end DifferentialGeometry
