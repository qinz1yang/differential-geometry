import DifferentialGeometry.Topology.Homology.Algebra.EulerCharacteristic
import Mathlib.AlgebraicTopology.SimplicialSet.Homology.Nondegenerate
import Mathlib.Algebra.Category.ModuleCat.Products
import Mathlib.Algebra.DirectSum.Finsupp
import Mathlib.LinearAlgebra.Dimension.Constructions

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits DirectSum

universe u

namespace DifferentialGeometry.SSet

variable {k : Type u} [Field k] (X : _root_.SSet.{u}) (R : ModuleCat.{u} k)

private def normalizedChainComplexXIso (n : ℕ) :
    (X.normalizedChainComplex R).X n ≅ ModuleCat.of k (⨁ (_ : X.nonDegenerate n), R) := by
  classical
  exact (X.isColimitCofanNormalizedChainComplex R n).coconePointUniqueUpToIso
    (ModuleCat.coproductCoconeIsColimit (fun _ : X.nonDegenerate n => R))

theorem finiteDimensional_normalizedChainComplex_X (n : ℕ)
    [Finite (X.nonDegenerate n)] [FiniteDimensional k R] :
    FiniteDimensional k ((X.normalizedChainComplex R).X n) := by
  classical
  let : Fintype (X.nonDegenerate n) := Fintype.ofFinite (X.nonDegenerate n)
  let e := (normalizedChainComplexXIso X R n).toLinearEquiv.trans
    (DirectSum.linearEquivFunOnFintype k (X.nonDegenerate n) (fun _ => R))
  exact e.symm.finiteDimensional

theorem finrank_normalizedChainComplex_X (n : ℕ) [Finite (X.nonDegenerate n)] :
    Module.finrank k ((X.normalizedChainComplex R).X n) =
      Nat.card (X.nonDegenerate n) * Module.finrank k R := by
  classical
  let : Fintype (X.nonDegenerate n) := Fintype.ofFinite (X.nonDegenerate n)
  let e := (normalizedChainComplexXIso X R n).toLinearEquiv.trans
    (finsuppLEquivDirectSum k R (X.nonDegenerate n)).symm
  rw [e.finrank_eq, Module.finrank_finsupp]
  simp

theorem finiteDimensional_homology (n : ℕ)
    [Finite (X.nonDegenerate n)] [FiniteDimensional k R] :
    FiniteDimensional k (X.homology (C := ModuleCat.{u} k) R n) := by
  have := finiteDimensional_normalizedChainComplex_X X R n
  have := DifferentialGeometry.HomologicalComplex.finiteDimensional_homology (X.normalizedChainComplex R) n
  exact (isoOfQuasiIsoAt (X.toNormalizedChainComplex R) n).symm.toLinearEquiv.finiteDimensional

theorem homologyEulerChar_chainComplex_eq_normalizedChainComplex :
    (X.chainComplex R).homologyEulerChar = (X.normalizedChainComplex R).homologyEulerChar := by
  unfold _root_.HomologicalComplex.homologyEulerChar GradedObject.eulerChar
  congr 1
  funext n
  congr 2
  exact (isoOfQuasiIsoAt (X.toNormalizedChainComplex R) n).toLinearEquiv.finrank_eq

theorem eulerChar_normalizedChainComplex_eq_homologyEulerChar
    [X.Finite] [FiniteDimensional k R] :
    (X.normalizedChainComplex R).eulerChar = (X.chainComplex R).homologyEulerChar := by
  have : ∀ n : ℕ, FiniteDimensional k ((X.normalizedChainComplex R).X n) :=
    fun n => finiteDimensional_normalizedChainComplex_X X R n
  rw [homologyEulerChar_chainComplex_eq_normalizedChainComplex]
  apply DifferentialGeometry.HomologicalComplex.eulerChar_eq_homologyEulerChar
  obtain ⟨d, _⟩ := X.hasDimensionLT_of_finite
  exact ⟨d, fun n hn => X.isZero_normalizedChainComplex_X_of_hasDimensionLT R n d hn.le⟩

variable (k)

theorem homologyEulerChar_eq_sum_card_nonDegenerate [X.Finite]
    (d : ℕ) [X.HasDimensionLT d] :
    (X.chainComplex (ModuleCat.of k k)).homologyEulerChar =
      ∑ n ∈ Finset.range d, (-1 : ℤ) ^ n * Nat.card (X.nonDegenerate n) := by
  rw [← eulerChar_normalizedChainComplex_eq_homologyEulerChar]
  have hs : GradedObject.finrankSupport (X.normalizedChainComplex (ModuleCat.of k k)).X ⊆
      Finset.range d := by
    rw [GradedObject.finrankSupport_subset_iff]
    intro n hn
    have := ModuleCat.subsingleton_of_isZero
      (X.isZero_normalizedChainComplex_X_of_hasDimensionLT (ModuleCat.of k k) n d
        (by simpa [Finset.mem_range] using hn))
    exact Module.finrank_zero_of_subsingleton
  rw [_root_.HomologicalComplex.eulerChar_eq_sum_finSet_of_finrankSupport_subset _ _ hs]
  simp [finrank_normalizedChainComplex_X, ComplexShape.χ]

theorem homologyEulerChar_eq_finsum_card_nonDegenerate [X.Finite] :
    (X.chainComplex (ModuleCat.of k k)).homologyEulerChar =
      ∑ᶠ n : ℕ, (-1 : ℤ) ^ n * Nat.card (X.nonDegenerate n) := by
  obtain ⟨d, _⟩ := X.hasDimensionLT_of_finite
  rw [homologyEulerChar_eq_sum_card_nonDegenerate (X := X) (k := k) d]
  symm
  apply finsum_eq_sum_of_support_subset
  intro n hn
  by_contra hnd
  have hdn : d ≤ n := by simpa [Finset.mem_range] using hnd
  have : IsEmpty (X.nonDegenerate n) := by
    rw [X.nonDegenerate_eq_empty_of_hasDimensionLT d n hdn]
    infer_instance
  simp only [Function.mem_support, Nat.card_of_isEmpty, Nat.cast_zero, mul_zero,
    ne_eq, not_true_eq_false] at hn

theorem homologyEulerChar_eq_of_coefficients [X.Finite] (K : Type u) [Field K] :
    (X.chainComplex (ModuleCat.of k k)).homologyEulerChar =
      (X.chainComplex (ModuleCat.of K K)).homologyEulerChar := by
  rw [homologyEulerChar_eq_finsum_card_nonDegenerate,
    homologyEulerChar_eq_finsum_card_nonDegenerate]

end DifferentialGeometry.SSet
