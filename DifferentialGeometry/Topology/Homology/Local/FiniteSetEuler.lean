import DifferentialGeometry.Topology.Homology.Local.FiniteSet
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.Data.Fintype.Order

set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits Set Function
namespace Poincare.Homology
universe u
variable (X : TopCat.{u}) [T2Space X] (Z : Set X) (hZ : Z.Finite)
  (k : Type u) [Field k]
include hZ


theorem finiteHomologyType_finitePuncture
    (h : ∀ p : Z, Poincare.HomologicalComplex.finiteHomologyType
      (relativeChainComplex X ({p.val}ᶜ : Set X) (ModuleCat.of k k))) :
    Poincare.HomologicalComplex.finiteHomologyType
      (relativeChainComplex X Zᶜ (ModuleCat.of k k)) := by
  let := hZ.to_subtype
  constructor
  · intro n
    let : ∀ p : Z, FiniteDimensional k (relativeHomology X ({p.val}ᶜ : Set X) (ModuleCat.of k k) n) :=
      fun p => (h p).1 n
    exact (finitePunctureHomologyLinearEquiv X Z (ModuleCat.of k k) hZ n).symm.finiteDimensional
  · choose N hN using fun p => (h p).2
    obtain ⟨B,hB⟩ := Finite.exists_le N
    exact ⟨B,fun n hn => isZero_relativeHomology_finitePuncture X Z (ModuleCat.of k k) hZ n
      (fun p => hN p n ((hB p).trans_lt hn))⟩


theorem relativeEulerChar_finitePuncture
    (h : ∀ p : Z, Poincare.HomologicalComplex.finiteHomologyType
      (relativeChainComplex X ({p.val}ᶜ : Set X) (ModuleCat.of k k))) :
    relativeEulerChar X Zᶜ k = ∑ᶠ p : Z, relativeEulerChar X ({p.val}ᶜ : Set X) k := by
  let := hZ.fintype
  rw [finsum_eq_sum_of_fintype]
  have hd (n : ℕ) : Module.finrank k (relativeHomology X Zᶜ (ModuleCat.of k k) n) =
      ∑ p : Z, Module.finrank k (relativeHomology X ({p.val}ᶜ : Set X) (ModuleCat.of k k) n) := by
    let : ∀ p : Z, FiniteDimensional k (relativeHomology X ({p.val}ᶜ : Set X) (ModuleCat.of k k) n) :=
      fun p => (h p).1 n
    exact (finitePunctureHomologyLinearEquiv X Z (ModuleCat.of k k) hZ n).finrank_eq.trans
      (Module.finrank_pi_fintype k)
  have hs (p : Z) : HasFiniteSupport (fun n : ℕ =>
      (ComplexShape.down ℕ).χ n * (Module.finrank k
        (relativeHomology X ({p.val}ᶜ : Set X) (ModuleCat.of k k) n) : ℤ)) := by
    obtain ⟨N,hN⟩ := (h p).2
    apply (Finset.finite_toSet (Finset.range (N + 1))).subset
    intro n hn
    by_contra he
    have hnN : N < n := by simpa using he
    let : Subsingleton (relativeHomology X ({p.val}ᶜ : Set X) (ModuleCat.of k k) n) :=
      ModuleCat.isZero_iff_subsingleton.mp (hN n hnN)
    have hz := Module.finrank_zero_of_subsingleton (R := k)
      (M := relativeHomology X ({p.val}ᶜ : Set X) (ModuleCat.of k k) n)
    exact hn (by simp [hz])
  change (∑ᶠ n : ℕ, (ComplexShape.down ℕ).χ n *
      (Module.finrank k (relativeHomology X Zᶜ (ModuleCat.of k k) n) : ℤ)) = _
  simp_rw [hd, Nat.cast_sum, Finset.mul_sum]
  exact finsum_sum_comm Finset.univ _ (fun p _ => hs p)
end Poincare.Homology
