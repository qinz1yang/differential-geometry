import DifferentialGeometry.Tensor.RSTensor.Tensor0SRiemannian.Comparison
import DifferentialGeometry.Tensor.RSTensor.ContractionLeibniz

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false

/-!
# The Frobenius norm is multiplicative on tensor products

`normSq0S g x (s+q) (A ⊗ B) = normSq0S g x s A * normSq0S g x q B`: in a
`g`-orthonormal basis the squared norm is the sum of squares of the components,
the components of a tensor product factor as `(A⊗B)_{IJ} = A_I B_J`, and
`∑_{I,J} (A_I B_J)² = (∑_I A_I²)(∑_J B_J²)`.

This is the base case (`m = 0`) of the iterated-Leibniz product-norm bound
`|∇ᵐ(A∗B)| ≤ ∑_c \binom m c |∇ᶜA| |∇^{m−c}B|` used in MSM135 equation (3.4).
-/

noncomputable section

namespace Tensor0SBundle

open scoped Manifold ContDiff BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I 1 M] [IsManifold I 2 M]
variable [IsManifold I (∞ : WithTop ℕ∞) M] [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
variable [T2Space M]

/-- **The Frobenius norm squares are multiplicative on tensor products.** -/
theorem normSq0S_product {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (g : SmoothMetric_gen I M) (x : M) {s q : ℕ}
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (hinv :
      MetricInverseInBasis_gen (I := I) g x basis (identityInvMetric (Idx := Idx)))
    (A : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s)
    (B : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) q) :
    normSq0S (I := I) g x (s + q)
        (MultilinearSection.product (𝕜 := Real) (F := E) (IB := I)
          (E := TangentSpace I) (n := (∞ : WithTop ℕ∞)) (s := s) (q := q) A B x)
      = normSq0S (I := I) g x s (A x) * normSq0S (I := I) g x q (B x) := by
  classical
  rw [normSq0S_identity_eq_sum_sq (I := I) g x (s + q) basis hinv,
    normSq0S_identity_eq_sum_sq (I := I) g x s basis hinv,
    normSq0S_identity_eq_sum_sq (I := I) g x q basis hinv,
    Finset.sum_mul_sum,
    ← Fintype.sum_prod_type
      (f := fun p : (Fin s -> Idx) × (Fin q -> Idx) =>
        component0S (I := I) basis (A x) p.1 ^ 2
          * component0S (I := I) basis (B x) p.2 ^ 2)]
  refine Fintype.sum_equiv
    { toFun := fun slots : Fin (s + q) -> Idx =>
        (slots ∘ Fin.castAdd q, slots ∘ Fin.natAdd s)
      invFun := fun p => Fin.addCases p.1 p.2
      left_inv := fun slots => by
        funext i
        refine Fin.addCases (fun a => ?_) (fun b => ?_) i
        · simp only [Fin.addCases_left, Function.comp_apply]
        · simp only [Fin.addCases_right, Function.comp_apply]
      right_inv := fun p => by
        obtain ⟨f, h⟩ := p
        refine Prod.ext ?_ ?_
        · funext a; simp only [Function.comp_apply, Fin.addCases_left]
        · funext b; simp only [Function.comp_apply, Fin.addCases_right] }
    _ _ ?_
  intro slots
  have hprod :
      component0S (I := I) basis
          (MultilinearSection.product (𝕜 := Real) (F := E) (IB := I)
            (E := TangentSpace I) (n := (∞ : WithTop ℕ∞)) (s := s) (q := q) A B x)
          slots
        = component0S (I := I) basis (A x) (slots ∘ Fin.castAdd q)
          * component0S (I := I) basis (B x) (slots ∘ Fin.natAdd s) := by
    rw [component0S_apply, component0S_apply, component0S_apply,
      tensor0SField_product_apply]
    rfl
  rw [hprod, mul_pow]
  rfl

/-- `normSq0S` is invariant under reindexing the tensor slots by any equivalence
`Fin s ≃ Fin s'` (a permutation together with a rank identification): the squared
Frobenius norm is a sum over all index tuples, which the reindexing merely
permutes.  (Needed because the second Leibniz term `A∗∇B` carries the new
derivative slot in the middle rather than at the front, and the two product
orders give the propositionally-but-not-definitionally-equal ranks
`(s+1)+q = (s+q)+1`.) -/
theorem normSq0S_domDomCongr {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (g : SmoothMetric_gen I M) (x : M) {s s' : ℕ}
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (hinv :
      MetricInverseInBasis_gen (I := I) g x basis (identityInvMetric (Idx := Idx)))
    (e : Fin s ≃ Fin s') (T : Tensor0SSpace s I x) :
    normSq0S (I := I) g x s' (T.domDomCongr e) = normSq0S (I := I) g x s T := by
  classical
  rw [normSq0S_identity_eq_sum_sq (I := I) g x s' basis hinv,
    normSq0S_identity_eq_sum_sq (I := I) g x s basis hinv]
  refine Fintype.sum_equiv (Equiv.arrowCongr e.symm (Equiv.refl Idx)) _ _ ?_
  intro w
  simp only [component0S_apply, Equiv.arrowCongr_apply, Equiv.symm_symm,
    Equiv.coe_refl, Function.comp, id_eq]
  rw [Tensor0SSpace.domDomCongr_apply]

end Tensor0SBundle
