import Mathlib.Algebra.Homology.EulerCharacteristic
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace DifferentialGeometry.ShortComplex

variable {k : Type u} [Field k] (S : CategoryTheory.ShortComplex (ModuleCat.{v} k))


theorem finiteDimensional_homology [FiniteDimensional k S.X₂] :
    FiniteDimensional k S.homology := by
  have : FiniteDimensional k S.moduleCatLeftHomologyData.H := by
    change FiniteDimensional k (LinearMap.ker S.g.hom ⧸ LinearMap.range S.moduleCatToCycles)
    infer_instance
  exact S.moduleCatHomologyIso.symm.toLinearEquiv.finiteDimensional


theorem finrank_eq_homology_add_range [FiniteDimensional k S.X₂] :
    Module.finrank k S.X₂ = Module.finrank k S.homology +
      Module.finrank k (LinearMap.range S.f.hom) + Module.finrank k (LinearMap.range S.g.hom) := by
  have hmap : (LinearMap.range S.moduleCatToCycles).map (LinearMap.ker S.g.hom).subtype =
      LinearMap.range S.f.hom := by
    rw [← LinearMap.range_comp]
    rfl
  have hdim := Submodule.finrank_map_subtype_eq (LinearMap.ker S.g.hom)
    (LinearMap.range S.moduleCatToCycles)
  rw [hmap] at hdim
  have hquot := (LinearMap.range S.moduleCatToCycles).finrank_quotient_add_finrank
  have hhom := S.moduleCatHomologyIso.toLinearEquiv.finrank_eq
  change Module.finrank k S.homology =
    Module.finrank k (LinearMap.ker S.g.hom ⧸ LinearMap.range S.moduleCatToCycles) at hhom
  have hrank := S.g.hom.finrank_range_add_finrank_ker
  omega

end DifferentialGeometry.ShortComplex

namespace DifferentialGeometry.HomologicalComplex

variable {k : Type u} [Field k]

private theorem finrank_range_eq_zero {A B : ModuleCat.{v} k} {f : A ⟶ B} (hf : f = 0) :
    Module.finrank k (LinearMap.range f.hom) = 0 := by
  subst f
  change Module.finrank k (LinearMap.range (0 : A →ₗ[k] B)) = 0
  have : Subsingleton (LinearMap.range (0 : A →ₗ[k] B)) := by
    rw [LinearMap.range_zero]
    infer_instance
  exact Module.finrank_zero_of_subsingleton


theorem finiteDimensional_homology {ι : Type*} {c : ComplexShape ι}
    (K : _root_.HomologicalComplex (ModuleCat.{v} k) c) (i : ι)
    [FiniteDimensional k (K.X i)] : FiniteDimensional k (K.homology i) := by
  have : FiniteDimensional k (K.sc i).X₂ := by
    change FiniteDimensional k (K.X i)
    infer_instance
  exact DifferentialGeometry.ShortComplex.finiteDimensional_homology (K.sc i)

private theorem alternating_sum_telescope (a h r : ℕ → ℤ)
    (hzero : a 0 = h 0 + r 0)
    (hsucc : ∀ n, a (n + 1) = h (n + 1) + r (n + 1) + r n) (N : ℕ) :
    ∑ n ∈ Finset.range (N + 1), (-1 : ℤ) ^ n * a n =
      (∑ n ∈ Finset.range (N + 1), (-1 : ℤ) ^ n * h n) + (-1 : ℤ) ^ N * r N := by
  induction N with
  | zero => simpa using hzero
  | succ N ih =>
    conv_lhs => rw [Finset.sum_range_succ, ih]
    conv_rhs => rw [Finset.sum_range_succ]
    rw [hsucc, pow_succ]
    ring

variable (K : ChainComplex (ModuleCat.{v} k) ℕ) [∀ n : ℕ, FiniteDimensional k (K.X n)]

private theorem finrank_zero :
    Module.finrank k (K.X 0) = Module.finrank k (K.homology 0) +
      Module.finrank k (LinearMap.range (K.d 1 0).hom) := by
  have : FiniteDimensional k (K.sc' 1 0 0).X₂ := by
    change FiniteDimensional k (K.X 0)
    infer_instance
  have h := DifferentialGeometry.ShortComplex.finrank_eq_homology_add_range (K.sc' 1 0 0)
  have hiso := (CategoryTheory.ShortComplex.homologyMapIso
    (K.isoSc' 1 0 0 (by simp) _root_.ChainComplex.next_nat_zero)).toLinearEquiv.finrank_eq
  change Module.finrank k (K.homology 0) = Module.finrank k (K.sc' 1 0 0).homology at hiso
  change Module.finrank k (K.X 0) = Module.finrank k (K.sc' 1 0 0).homology +
    Module.finrank k (LinearMap.range (K.d 1 0).hom) +
    Module.finrank k (LinearMap.range (K.d 0 0).hom) at h
  rw [← hiso] at h
  have hzero : K.d 0 0 = 0 := K.shape _ _ (by decide)
  have hzrank := finrank_range_eq_zero hzero
  omega

private theorem finrank_succ (n : ℕ) :
    Module.finrank k (K.X (n + 1)) = Module.finrank k (K.homology (n + 1)) +
      Module.finrank k (LinearMap.range (K.d (n + 2) (n + 1)).hom) +
      Module.finrank k (LinearMap.range (K.d (n + 1) n).hom) := by
  have : FiniteDimensional k (K.sc' (n + 2) (n + 1) n).X₂ := by
    change FiniteDimensional k (K.X (n + 1))
    infer_instance
  have h := DifferentialGeometry.ShortComplex.finrank_eq_homology_add_range (K.sc' (n + 2) (n + 1) n)
  have hiso := (CategoryTheory.ShortComplex.homologyMapIso
    (K.isoSc' (n + 2) (n + 1) n (by simp [Nat.add_assoc])
      (_root_.ChainComplex.next_nat_succ n))).toLinearEquiv.finrank_eq
  change Module.finrank k (K.homology (n + 1)) =
    Module.finrank k (K.sc' (n + 2) (n + 1) n).homology at hiso
  change Module.finrank k (K.X (n + 1)) = Module.finrank k (K.sc' (n + 2) (n + 1) n).homology +
    Module.finrank k (LinearMap.range (K.d (n + 2) (n + 1)).hom) +
    Module.finrank k (LinearMap.range (K.d (n + 1) n).hom) at h
  rwa [← hiso] at h

theorem sum_finrank_eq_sum_homology_add_range (N : ℕ) :
    ∑ n ∈ Finset.range (N + 1), (-1 : ℤ) ^ n * Module.finrank k (K.X n) =
      (∑ n ∈ Finset.range (N + 1), (-1 : ℤ) ^ n * Module.finrank k (K.homology n)) +
        (-1 : ℤ) ^ N * Module.finrank k (LinearMap.range (K.d (N + 1) N).hom) := by
  apply alternating_sum_telescope
  · exact_mod_cast finrank_zero K
  · intro n
    exact_mod_cast finrank_succ K n

theorem eulerChar_eq_homologyEulerChar
    (hbounded : ∃ N : ℕ, ∀ n : ℕ, N < n → IsZero (K.X n)) :
    K.eulerChar = K.homologyEulerChar := by
  obtain ⟨N, hN⟩ := hbounded
  have hchain : GradedObject.finrankSupport K.X ⊆ Finset.range (N + 1) := by
    rw [GradedObject.finrankSupport_subset_iff]
    intro n hn
    have := ModuleCat.subsingleton_of_isZero (hN n (by simpa [Finset.mem_range] using hn))
    exact Module.finrank_zero_of_subsingleton
  have hhomology : GradedObject.finrankSupport (fun n ↦ K.homology n) ⊆
      Finset.range (N + 1) := by
    rw [GradedObject.finrankSupport_subset_iff]
    intro n hn
    have hz := (_root_.HomologicalComplex.ExactAt.of_isZero
      (hN n (by simpa [Finset.mem_range] using hn))).isZero_homology
    have := ModuleCat.subsingleton_of_isZero hz
    exact Module.finrank_zero_of_subsingleton
  rw [_root_.HomologicalComplex.eulerChar_eq_sum_finSet_of_finrankSupport_subset
      K (Finset.range (N + 1)) hchain,
    _root_.HomologicalComplex.homologyEulerChar_eq_sum_finSet_of_finrankSupport_subset
      K (Finset.range (N + 1)) hhomology]
  have hd : K.d (N + 1) N = 0 := (hN (N + 1) (Nat.lt_succ_self N)).eq_of_src _ _
  have hzrank := finrank_range_eq_zero hd
  simpa [ComplexShape.χ, hzrank] using sum_finrank_eq_sum_homology_add_range K N

end DifferentialGeometry.HomologicalComplex
