import DifferentialGeometry.Tensor.RSTensor.ContractionLeibniz
import DifferentialGeometry.Tensor.Multilinear.DomDomCongrSection

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

/-!
# The field-level two-sided tensor-product Leibniz rule

`nabla0SFun_product_eval` is the *evaluated* Leibniz rule.  This file lifts it to
a **field-level** identity for the canonical covariant derivative:

`∇(A ⊗ B) = (∇A ⊗ B) + (A ⊗ ∇B)·σ`

where `σ = Fin.cycleRange s` moves the new (front) derivative slot of `A ⊗ ∇B`
from the middle (position `s`) to the front, to match `∇(A ⊗ B)`.  Both terms are
reindexed to rank `s + q + 1` via `finCongr` (the `(s+1)+q = (s+q)+1` rank
identification) using `MultilinearSection.domDomCongr`.

This is the field identity that the iterated Leibniz norm bound
`|∇ᵐ(A∗B)| ≤ Σ_c \binom m c |∇ᶜA||∇^{m−c}B|` iterates.
-/

namespace Tensor0SBundle

set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff BigOperators
open Bundle

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [CompleteSpace E] [IsManifold I ∞ M]

/-- The rank-changing slot equivalence for the second Leibniz term: identify
`Fin (s + (q + 1))` with `Fin (s + q + 1)` and cycle the middle derivative slot
(position `s`) to the front. -/
noncomputable def leibnizRightEquiv (s q : ℕ) : Fin (s + (q + 1)) ≃ Fin (s + q + 1) :=
  (finCongr (by omega : s + (q + 1) = s + q + 1)).trans
    (Fin.cycleRange ⟨s, by omega⟩)

/-- The rank-changing slot equivalence for the first Leibniz term: just the rank
identification `Fin (s + 1 + q) ≃ Fin (s + q + 1)`. -/
def leibnizLeftEquiv (s q : ℕ) : Fin (s + 1 + q) ≃ Fin (s + q + 1) :=
  finCongr (by omega)

/-- **The field-level two-sided tensor-product Leibniz rule.**  For smooth
covariant tensor fields `A`, `B` with realized covariant derivatives `nablaA`,
`nablaB`, the tensor product `A ⊗ B` has covariant derivative realized by
`(∇A ⊗ B) + (A ⊗ ∇B)·cycleRange`. -/
theorem nabla0S_product_realizes {s q : ℕ}
    [T2Space M] [IsManifold I 1 M] [IsManifold I 2 M]
    [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
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
      (MultilinearSection.product (𝕜 := Real) (F := E) (IB := I)
        (E := TangentSpace I) (n := (∞ : WithTop ℕ∞)) (s := s) (q := q) A B)
      (MultilinearSection.domDomCongr (𝕜 := Real) (F := E) (IB := I)
          (E := TangentSpace I) (∞ : WithTop ℕ∞) (leibnizLeftEquiv s q)
          (MultilinearSection.product (𝕜 := Real) (F := E) (IB := I)
            (E := TangentSpace I) (n := (∞ : WithTop ℕ∞)) (s := s + 1) (q := q)
            nablaA B)
        + MultilinearSection.domDomCongr (𝕜 := Real) (F := E) (IB := I)
          (E := TangentSpace I) (∞ : WithTop ℕ∞) (leibnizRightEquiv s q)
          (MultilinearSection.product (𝕜 := Real) (F := E) (IB := I)
            (E := TangentSpace I) (n := (∞ : WithTop ℕ∞)) (s := s) (q := q + 1)
            A nablaB)) := by
  classical
  intro X x slots
  let V : Fin (s + q) -> ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M -> Type _) :=
    fun a =>
      (ContMDiffSection.exists_eq_at_gen
        (I := I) (F := E) (V := TangentSpace I) (n := (⊤ : ℕ∞))
        x (slots a)).choose
  have hV : ∀ a : Fin (s + q), V a x = slots a := fun a =>
    (ContMDiffSection.exists_eq_at_gen
      (I := I) (F := E) (V := TangentSpace I) (n := (⊤ : ℕ∞))
      x (slots a)).choose_spec
  have hslots : (fun a : Fin (s + q) => V a x) = slots := funext hV
  have hmain :=
    nabla0SFun_product_eval (I := I) cov A B nablaA nablaB hA hB X V x
  -- Reduce the goal's RHS (the product `nabla0SFun`) by the evaluated Leibniz rule
  -- and rewrite slots by `V · x`.
  rw [show slots = (fun a : Fin (s + q) => V a x) from hslots.symm, hmain]
  -- Evaluate both `domDomCongr` summands on the left.
  change
    (ContinuousMultilinearMap.domDomCongr (leibnizLeftEquiv s q)
        ((MultilinearSection.product (𝕜 := Real) (F := E) (IB := I)
          (E := TangentSpace I) (n := (∞ : WithTop ℕ∞))
          (s := s + 1) (q := q) nablaA B) x))
        (Fin.cons (X x) (fun a : Fin (s + q) => V a x)) +
      (ContinuousMultilinearMap.domDomCongr (leibnizRightEquiv s q)
        ((MultilinearSection.product (𝕜 := Real) (F := E) (IB := I)
          (E := TangentSpace I) (n := (∞ : WithTop ℕ∞))
          (s := s) (q := q + 1) A nablaB) x))
        (Fin.cons (X x) (fun a : Fin (s + q) => V a x)) = _
  rw [Tensor0SSpace.domDomCongr_apply, Tensor0SSpace.domDomCongr_apply,
    tensor0SField_product_apply, tensor0SField_product_apply]
  refine congrArg₂ (· + ·)
    (congrArg₂ (· * ·) (congrArg (nablaA x) ?_) (congrArg (B x) ?_))
    (congrArg₂ (· * ·) (congrArg (A x) ?_) (congrArg (nablaB x) ?_))
  · -- nablaA's slots
    funext a
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
  · -- B's slots
    funext a
    simp only [leibnizLeftEquiv, finCongr_apply, Function.comp_apply]
    rw [show (Fin.cast (by omega : s + 1 + q = s + q + 1) (Fin.natAdd (s + 1) a))
          = (Fin.natAdd s a).succ from by
      ext; simp only [Fin.val_cast, Fin.val_natAdd, Fin.val_succ]; omega]
    rw [Fin.cons_succ]
  · -- A's slots
    funext a
    have hidx : leibnizRightEquiv s q (Fin.castAdd (q + 1) a) = (Fin.castAdd q a).succ := by
      rw [leibnizRightEquiv, Equiv.trans_apply, finCongr_apply,
        show (Fin.cast (by omega : s + (q + 1) = s + q + 1) (Fin.castAdd (q + 1) a))
            = (⟨a, by omega⟩ : Fin (s + q + 1)) from by ext; simp,
        Fin.cycleRange_of_lt (by simp only [Fin.lt_def]; omega)]
      ext
      rw [Fin.val_add_one_of_lt (by simp only [Fin.lt_def, Fin.val_last]; omega)]
      simp [Fin.val_succ]
    simp only [Function.comp_apply, hidx, Fin.cons_succ]
  · -- nablaB's slots
    funext a
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

end Tensor0SBundle
