import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.Data.Finsupp.Basic
import Mathlib.Algebra.Group.Prod
import Mathlib.Algebra.Group.TypeTags.Basic
import Mathlib.LinearAlgebra.TensorProduct.Pi
import Mathlib.LinearAlgebra.TensorProduct.Prod
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.LinearAlgebra.Finsupp.Defs
import Mathlib.RingTheory.Finiteness.Basic

open scoped TensorProduct

noncomputable section

namespace DifferentialGeometry.Algebra.Module

open TensorProduct

theorem finite_tensorProduct_baseChange {R : Type*} [CommSemiring R] {A : Type*} [Semiring A]
    [Algebra R A] {M : Type*} [AddCommMonoid M] [Module R M] (h : Module.Finite R M) :
    Module.Finite A (A ⊗[R] M) := by
  classical
  obtain ⟨s, hs⟩ := h.fg_top
  exact ⟨s.image (TensorProduct.mk R A M 1), by
    rw [Finset.coe_image, ← Submodule.baseChange_span (A := A) (s := (↑s : Set M)), hs,
      Submodule.baseChange_top]⟩

theorem finrank_tensorProduct_prod (G₁ G₂ : Type*) [AddCommGroup G₁] [AddCommGroup G₂]
    [Module.Finite ℚ (ℚ ⊗[ℤ] G₁)] [Module.Finite ℚ (ℚ ⊗[ℤ] G₂)] :
    Module.finrank ℚ (ℚ ⊗[ℤ] (G₁ × G₂)) =
      Module.finrank ℚ (ℚ ⊗[ℤ] G₁) + Module.finrank ℚ (ℚ ⊗[ℤ] G₂) := by
  rw [(TensorProduct.prodRight ℤ ℚ ℚ G₁ G₂).finrank_eq, Module.finrank_prod]

theorem finrank_tensorProduct_prod_fin_int (G : Type*) [AddCommGroup G]
    [Module.Finite ℚ (ℚ ⊗[ℤ] G)] (b : ℕ) :
    Module.finrank ℚ (ℚ ⊗[ℤ] (G × (Fin b → ℤ))) = Module.finrank ℚ (ℚ ⊗[ℤ] G) + b := by
  have hfin : Module.Finite ℚ (ℚ ⊗[ℤ] (Fin b → ℤ)) :=
    Module.Finite.equiv (TensorProduct.piScalarRight ℤ ℚ ℚ (Fin b)).symm
  rw [finrank_tensorProduct_prod G (Fin b → ℤ),
    (TensorProduct.piScalarRight ℤ ℚ ℚ (Fin b)).finrank_eq, Module.finrank_pi]
  simp

theorem finrank_tensorProduct_int : Module.finrank ℚ (ℚ ⊗[ℤ] ℤ) = 1 := by
  have e : ℚ ⊗[ℤ] (Fin 1 → ℤ) ≃ₗ[ℚ] ℚ ⊗[ℤ] ℤ :=
    LinearEquiv.baseChange ℤ ℚ (Fin 1 → ℤ) ℤ
      (AddEquiv.toIntLinearEquiv (AddEquiv.funUnique (Fin 1) ℤ))
  rw [← e.finrank_eq]
  have hfin : Module.Finite ℚ (ℚ ⊗[ℤ] (Fin 1 → ℤ)) :=
    Module.Finite.equiv (TensorProduct.piScalarRight ℤ ℚ ℚ (Fin 1)).symm
  rw [(TensorProduct.piScalarRight ℤ ℚ ℚ (Fin 1)).finrank_eq, Module.finrank_pi]
  simp

theorem nat_eq_of_addEquiv_prod_fin_int (G : Type*) [AddCommGroup G]
    [Module.Finite ℚ (ℚ ⊗[ℤ] G)] {b b' : ℕ} (e : G × (Fin b → ℤ) ≃+ G × (Fin b' → ℤ)) :
    b = b' := by
  have h := (LinearEquiv.baseChange ℤ ℚ (G × (Fin b → ℤ)) (G × (Fin b' → ℤ))
    e.toIntLinearEquiv).finrank_eq
  rw [finrank_tensorProduct_prod_fin_int G b, finrank_tensorProduct_prod_fin_int G b'] at h
  omega

theorem nat_eq_of_addEquiv_prod_fin_int_of_finite (G : Type*) [AddCommGroup G]
    [Module.Finite ℤ G] {b b' : ℕ} (e : G × (Fin b → ℤ) ≃+ G × (Fin b' → ℤ)) : b = b' := by
  have hfin : Module.Finite ℚ (ℚ ⊗[ℤ] G) :=
    finite_tensorProduct_baseChange (R := ℤ) (A := ℚ) (M := G) (inferInstance)
  exact nat_eq_of_addEquiv_prod_fin_int G e

theorem nat_eq_of_addEquiv_prod_fin_int_of_addEquiv_left (A X : Type*) [AddCommGroup A]
    [AddCommGroup X] [Module.Finite ℤ A] {b b' : ℕ} (e : X ≃+ A × (Fin b → ℤ))
    (e' : X ≃+ A × (Fin b' → ℤ)) : b = b' :=
  (nat_eq_of_addEquiv_prod_fin_int_of_finite A (e'.symm.trans e)).symm

theorem nat_eq_of_mulEquiv_prod_fin_multiplicativeInt (A : Type*) [CommGroup A]
    [Module.Finite ℤ (Additive A)] {b b' : ℕ}
    (e : A × (Fin b → Multiplicative ℤ) ≃* A × (Fin b' → Multiplicative ℤ)) : b = b' :=
  nat_eq_of_addEquiv_prod_fin_int_of_finite (Additive A)
    ((AddEquiv.refl _).trans
      (({ toFun := e, invFun := e.symm, left_inv := e.left_inv, right_inv := e.right_inv,
          map_add' := e.map_mul } :
          Additive (A × (Fin b → Multiplicative ℤ)) ≃+
            Additive (A × (Fin b' → Multiplicative ℤ))).trans
        (AddEquiv.refl _)))

theorem not_nonempty_addEquiv_prod_fin_int_one_zero :
    ¬ Nonempty (ℤ × (Fin 1 → ℤ) ≃+ ℤ × (Fin 0 → ℤ)) :=
  fun ⟨e⟩ => Nat.one_ne_zero (nat_eq_of_addEquiv_prod_fin_int_of_finite ℤ e)

theorem nat_eq_of_addEquiv_prod_fin_int_swap :
    (1 : ℕ) = 1 :=
  nat_eq_of_addEquiv_prod_fin_int_of_finite (ℤ × ℤ)
    (AddEquiv.prodCongr (AddEquiv.prodComm (M := ℤ) (N := ℤ)) (AddEquiv.refl (Fin 1 → ℤ)))

private def sumPUnitEquivNat : ℕ ⊕ PUnit.{1} ≃ ℕ where
  toFun := Sum.elim (· + 1) fun _ => 0
  invFun n := if n = 0 then Sum.inr PUnit.unit else Sum.inl (n - 1)
  left_inv x := by rcases x with n | u <;> simp
  right_inv n := by
    dsimp only
    split_ifs with h
    · simpa using h.symm
    · simp only [Sum.elim_inl]
      omega

private def punitFinsuppAddEquivInt : (PUnit.{1} →₀ ℤ) ≃+ ℤ :=
  (Finsupp.linearEquivFunOnFinite ℤ ℤ PUnit.{1}).toAddEquiv.trans
    (AddEquiv.funUnique PUnit.{1} ℤ)

private def shiftAddEquiv : (ℕ →₀ ℤ) × ℤ ≃+ (ℕ →₀ ℤ) :=
  ((AddEquiv.prodCongr (AddEquiv.refl (ℕ →₀ ℤ)) punitFinsuppAddEquivInt.symm).trans
    (Finsupp.sumFinsuppAddEquivProdFinsupp (M := ℤ)).symm).trans
    (Finsupp.domCongr sumPUnitEquivNat)

private def nonFiniteCounterexample :
    (ℕ →₀ ℤ) × (Fin 1 → ℤ) ≃+ (ℕ →₀ ℤ) × (Fin 0 → ℤ) :=
  (AddEquiv.prodCongr (AddEquiv.refl (ℕ →₀ ℤ)) (AddEquiv.funUnique (Fin 1) ℤ)).trans
    (shiftAddEquiv.trans (AddEquiv.prodUnique (M := ℕ →₀ ℤ)).symm)

theorem not_forall_nat_eq_of_addEquiv_prod_fin_int :
    ¬ (∀ (G : Type) [AddCommGroup G] (b b' : ℕ),
        Nonempty (G × (Fin b → ℤ) ≃+ G × (Fin b' → ℤ)) → b = b') :=
  fun h => Nat.one_ne_zero (h (ℕ →₀ ℤ) 1 0 ⟨nonFiniteCounterexample⟩)

end DifferentialGeometry.Algebra.Module
