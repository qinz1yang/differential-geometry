import Mathlib.Algebra.Homology.EulerCharacteristic
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Category.ModuleCat.Products
import Mathlib.AlgebraicTopology.SingularHomology.HomotopyInvariance
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Topology.Homotopy.Contractible

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicTopology
open scoped ContinuousMap

universe u

namespace DifferentialGeometry.Homology

variable (k : Type u) [Field k]

def finiteHomologyType (X : TopCat.{u}) : Prop :=
  (∀ n : ℕ, FiniteDimensional k
    (((singularHomologyFunctor (ModuleCat.{u} k) n).obj (ModuleCat.of k k)).obj X)) ∧
    ∃ N : ℕ, ∀ n : ℕ, N < n →
      IsZero (((singularHomologyFunctor (ModuleCat.{u} k) n).obj (ModuleCat.of k k)).obj X)

def eulerChar (X : TopCat.{u}) : ℤ :=
  GradedObject.eulerChar (ComplexShape.down ℕ)
    (fun n ↦ ((singularHomologyFunctor (ModuleCat.{u} k) n).obj (ModuleCat.of k k)).obj X)

variable {X Y : TopCat.{u}}

@[simps hom inv]
def singularHomologyIso (e : X ≃ₕ Y) (n : ℕ) :
    ((singularHomologyFunctor (ModuleCat.{u} k) n).obj (ModuleCat.of k k)).obj X ≅
      ((singularHomologyFunctor (ModuleCat.{u} k) n).obj (ModuleCat.of k k)).obj Y where
  hom := ((singularHomologyFunctor (ModuleCat.{u} k) n).obj (ModuleCat.of k k)).map
    (TopCat.ofHom e.toFun)
  inv := ((singularHomologyFunctor (ModuleCat.{u} k) n).obj (ModuleCat.of k k)).map
    (TopCat.ofHom e.invFun)
  hom_inv_id := by
    rw [← Functor.map_comp]
    have H : TopCat.Homotopy
        (TopCat.ofHom e.toFun ≫ TopCat.ofHom e.invFun) (𝟙 X) := e.left_inv.some
    have h := H.congr_homologyMap_singularChainComplexFunctor (ModuleCat.of k k) n
    change ((singularHomologyFunctor (ModuleCat.{u} k) n).obj (ModuleCat.of k k)).map _ =
      ((singularHomologyFunctor (ModuleCat.{u} k) n).obj (ModuleCat.of k k)).map (𝟙 X) at h
    exact h.trans (CategoryTheory.Functor.map_id _ X)
  inv_hom_id := by
    rw [← Functor.map_comp]
    have H : TopCat.Homotopy
        (TopCat.ofHom e.invFun ≫ TopCat.ofHom e.toFun) (𝟙 Y) := e.right_inv.some
    have h := H.congr_homologyMap_singularChainComplexFunctor (ModuleCat.of k k) n
    change ((singularHomologyFunctor (ModuleCat.{u} k) n).obj (ModuleCat.of k k)).map _ =
      ((singularHomologyFunctor (ModuleCat.{u} k) n).obj (ModuleCat.of k k)).map (𝟙 Y) at h
    exact h.trans (CategoryTheory.Functor.map_id _ Y)


@[simp]
theorem singularHomologyIso_refl (X : TopCat.{u}) (n : ℕ) :
    singularHomologyIso k (ContinuousMap.HomotopyEquiv.refl X) n = Iso.refl _ := by
  apply Iso.ext
  exact CategoryTheory.Functor.map_id
    ((singularHomologyFunctor (ModuleCat.{u} k) n).obj (ModuleCat.of k k)) X


@[simp]
theorem singularHomologyIso_symm (e : X ≃ₕ Y) (n : ℕ) :
    singularHomologyIso k e.symm n = (singularHomologyIso k e n).symm := rfl


@[simp]
theorem singularHomologyIso_trans {Z : TopCat.{u}} (e : X ≃ₕ Y) (f : Y ≃ₕ Z) (n : ℕ) :
    singularHomologyIso k (e.trans f) n =
      singularHomologyIso k e n ≪≫ singularHomologyIso k f n := by
  apply Iso.ext
  exact CategoryTheory.Functor.map_comp
    ((singularHomologyFunctor (ModuleCat.{u} k) n).obj (ModuleCat.of k k))
      (TopCat.ofHom e.toFun) (TopCat.ofHom f.toFun)


theorem finiteHomologyType_iff_of_homotopyEquiv (e : X ≃ₕ Y) :
    finiteHomologyType k X ↔ finiteHomologyType k Y := by
  suffices h : ∀ {A B : TopCat.{u}}, A ≃ₕ B →
      finiteHomologyType k A → finiteHomologyType k B from ⟨h e, h e.symm⟩
  intro A B e hA
  constructor
  · intro n
    have := hA.1 n
    exact (singularHomologyIso k e n).toLinearEquiv.finiteDimensional
  · obtain ⟨N, hN⟩ := hA.2
    exact ⟨N, fun n hn ↦ (hN n hn).of_iso (singularHomologyIso k e n).symm⟩


theorem finiteHomologyType_iff_of_homeomorph (e : X ≃ₜ Y) :
    finiteHomologyType k X ↔ finiteHomologyType k Y :=
  finiteHomologyType_iff_of_homotopyEquiv k e.toHomotopyEquiv


theorem eulerChar_eq_of_homotopyEquiv (e : X ≃ₕ Y) :
    eulerChar k X = eulerChar k Y := by
  apply finsum_congr
  intro n
  rw [(singularHomologyIso k e n).toLinearEquiv.finrank_eq]


theorem eulerChar_eq_of_homeomorph (e : X ≃ₜ Y) :
    eulerChar k X = eulerChar k Y :=
  eulerChar_eq_of_homotopyEquiv k e.toHomotopyEquiv

theorem eulerChar_eq_sum (N : ℕ)
    (hN : ∀ n : ℕ, N < n →
      IsZero (((singularHomologyFunctor (ModuleCat.{u} k) n).obj (ModuleCat.of k k)).obj X)) :
    eulerChar k X = ∑ n ∈ Finset.range (N + 1), (-1 : ℤ) ^ n * Module.finrank k
      (((singularHomologyFunctor (ModuleCat.{u} k) n).obj (ModuleCat.of k k)).obj X) := by
  unfold eulerChar
  convert GradedObject.eulerChar_eq_sum_finSet_of_finrankSupport_subset
    (ComplexShape.down ℕ)
    (fun n ↦ ((singularHomologyFunctor (ModuleCat.{u} k) n).obj (ModuleCat.of k k)).obj X)
    (Finset.range (N + 1)) ?_ using 1
  · simp [ComplexShape.χ]
  · rw [GradedObject.finrankSupport_subset_iff]
    intro n hn
    have hz := hN n (by simpa [Finset.mem_range] using hn)
    have := ModuleCat.subsingleton_of_isZero hz
    exact Module.finrank_zero_of_subsingleton


theorem isZero_singularHomology_of_isEmpty [IsEmpty X] (n : ℕ) :
    IsZero (((singularHomologyFunctor (ModuleCat.{u} k) n).obj (ModuleCat.of k k)).obj X) := by
  by_cases hn : n = 0
  · subst n
    have hz : IsZero (∐ fun _ : X ↦ ModuleCat.of k k) := by
      rw [IsZero.iff_id_eq_zero]
      apply Sigma.hom_ext
      intro x
      exact isEmptyElim x
    exact hz.of_iso (singularHomologyFunctorZeroOfTotallyDisconnectedSpace
      (ModuleCat.{u} k) (ModuleCat.of k k) X)
  · exact isZero_singularHomologyFunctor_of_totallyDisconnectedSpace
      (ModuleCat.{u} k) n (ModuleCat.of k k) X hn

private def homologyZeroEquivPi [Fintype X] [TotallyDisconnectedSpace X] :
    ((singularHomologyFunctor (ModuleCat.{u} k) 0).obj (ModuleCat.of k k)).obj X ≃ₗ[k]
      (X → k) := by
  classical
  exact ((singularHomologyFunctorZeroOfTotallyDisconnectedSpace (ModuleCat.{u} k)
    (ModuleCat.of k k) X).trans (ModuleCat.coprodIsoDirectSum
      (fun _ : X ↦ ModuleCat.of k k))).toLinearEquiv.trans
        (DirectSum.linearEquivFunOnFintype k X (fun _ ↦ k))

theorem finiteHomologyType_of_finite_totallyDisconnected [Finite X] [TotallyDisconnectedSpace X] :
    finiteHomologyType k X := by
  let := Fintype.ofFinite X
  constructor
  · intro n
    by_cases hn : n = 0
    · subst n
      exact (homologyZeroEquivPi k (X := X)).symm.finiteDimensional
    · have := ModuleCat.subsingleton_of_isZero
        (isZero_singularHomologyFunctor_of_totallyDisconnectedSpace
          (ModuleCat.{u} k) n (ModuleCat.of k k) X hn)
      infer_instance
  · exact ⟨0, fun n hn ↦ isZero_singularHomologyFunctor_of_totallyDisconnectedSpace
      (ModuleCat.{u} k) n (ModuleCat.of k k) X hn.ne'⟩

theorem eulerChar_of_finite_totallyDisconnected [Finite X] [TotallyDisconnectedSpace X] :
    eulerChar k X = Nat.card X := by
  let := Fintype.ofFinite X
  rw [eulerChar_eq_sum k 0 (fun n hn ↦
    isZero_singularHomologyFunctor_of_totallyDisconnectedSpace
      (ModuleCat.{u} k) n (ModuleCat.of k k) X hn.ne')]
  simp [(homologyZeroEquivPi k (X := X)).finrank_eq, Nat.card_eq_fintype_card]


theorem finiteHomologyType_of_subsingleton [Subsingleton X] : finiteHomologyType k X :=
  finiteHomologyType_of_finite_totallyDisconnected k


@[simp]
theorem eulerChar_of_isEmpty [IsEmpty X] : eulerChar k X = 0 := by
  rw [eulerChar_of_finite_totallyDisconnected k]
  simp


@[simp]
theorem eulerChar_of_unique [Unique X] : eulerChar k X = 1 := by
  rw [eulerChar_of_finite_totallyDisconnected k]
  simp


theorem finiteHomologyType_of_contractible [ContractibleSpace X] : finiteHomologyType k X := by
  obtain ⟨e⟩ := ContractibleSpace.hequiv X PUnit.{u + 1}
  exact (finiteHomologyType_iff_of_homotopyEquiv k
    (Y := TopCat.of PUnit.{u + 1}) e).mpr (finiteHomologyType_of_subsingleton k)


theorem eulerChar_of_contractible [ContractibleSpace X] : eulerChar k X = 1 := by
  obtain ⟨e⟩ := ContractibleSpace.hequiv X PUnit.{u + 1}
  exact (eulerChar_eq_of_homotopyEquiv k
    (Y := TopCat.of PUnit.{u + 1}) e).trans (eulerChar_of_unique k)

end DifferentialGeometry.Homology
