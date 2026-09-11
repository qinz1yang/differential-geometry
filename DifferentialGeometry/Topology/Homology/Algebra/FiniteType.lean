import DifferentialGeometry.Topology.Homology.Algebra.ExactSequenceEuler

set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits
noncomputable section
universe u v

namespace DifferentialGeometry.ShortComplex
variable {k : Type u} [Field k]


theorem finiteDimensional_of_exact (S : CategoryTheory.ShortComplex (ModuleCat.{v} k))
    (hS : S.Exact) [FiniteDimensional k S.X₁] [FiniteDimensional k S.X₃] :
    FiniteDimensional k S.X₂ := by
  have hker : FiniteDimensional k (LinearMap.ker S.g.hom) := by
    rw [← S.moduleCat_exact_iff_range_eq_ker.mp hS]
    infer_instance
  have ht : FiniteDimensional k (Submodule.comap S.g.hom (⊤ : Submodule k S.X₃)) :=
    inferInstance
  rw [Submodule.comap_top] at ht
  exact (Submodule.topEquiv : (⊤ : Submodule k S.X₂) ≃ₗ[k] S.X₂).finiteDimensional

end DifferentialGeometry.ShortComplex

namespace DifferentialGeometry.HomologicalComplex
variable {k : Type u} [Field k]


def finiteHomologyType (K : ChainComplex (ModuleCat.{v} k) ℕ) : Prop :=
  (∀ n : ℕ, FiniteDimensional k (K.homology n)) ∧
    ∃ N : ℕ, ∀ n : ℕ, N < n → IsZero (K.homology n)

variable (S : CategoryTheory.ShortComplex (ChainComplex (ModuleCat.{v} k) ℕ))
  (hS : S.ShortExact)

include hS


theorem finiteHomologyType_middle
    (h₁ : finiteHomologyType S.X₁) (h₃ : finiteHomologyType S.X₃) :
    finiteHomologyType S.X₂ := by
  constructor
  · intro n
    have := h₁.1 n
    have := h₃.1 n
    exact DifferentialGeometry.ShortComplex.finiteDimensional_of_exact _ (hS.homology_exact₂ n)
  · obtain ⟨N₁, h₁⟩ := h₁.2
    obtain ⟨N₃, h₃⟩ := h₃.2
    refine ⟨max N₁ N₃, fun n hn ↦ ?_⟩
    exact (hS.homology_exact₂ n).isZero_of_both_isZero
      (h₁ n (lt_of_le_of_lt (le_max_left _ _) hn))
      (h₃ n (lt_of_le_of_lt (le_max_right _ _) hn))


theorem finiteHomologyType_first
    (h₂ : finiteHomologyType S.X₂) (h₃ : finiteHomologyType S.X₃) :
    finiteHomologyType S.X₁ := by
  constructor
  · intro n
    have := h₂.1 n
    have := h₃.1 (n + 1)
    exact DifferentialGeometry.ShortComplex.finiteDimensional_of_exact _ (hS.homology_exact₁ (n + 1) n rfl)
  · obtain ⟨N₂, h₂⟩ := h₂.2
    obtain ⟨N₃, h₃⟩ := h₃.2
    refine ⟨max N₂ N₃, fun n hn ↦ ?_⟩
    exact (hS.homology_exact₁ (n + 1) n rfl).isZero_of_both_isZero
      (h₃ (n + 1) (lt_of_le_of_lt (le_max_right _ _) (hn.trans (Nat.lt_succ_self n))))
      (h₂ n (lt_of_le_of_lt (le_max_left _ _) hn))


theorem finiteHomologyType_last
    (h₁ : finiteHomologyType S.X₁) (h₂ : finiteHomologyType S.X₂) :
    finiteHomologyType S.X₃ := by
  constructor
  · intro n
    cases n with
    | zero =>
      have := h₂.1 0
      have := hS.epi_g
      have := _root_.HomologicalComplex.epi_homologyMap_of_epi_of_not_rel S.g 0 (by
        intro j
        change ¬ j + 1 = 0
        omega)
      exact Module.Finite.of_surjective (_root_.HomologicalComplex.homologyMap S.g 0).hom
        (ModuleCat.epi_iff_surjective _ |>.mp inferInstance)
    | succ n =>
      have := h₁.1 n
      have := h₂.1 (n + 1)
      exact DifferentialGeometry.ShortComplex.finiteDimensional_of_exact _ (hS.homology_exact₃ (n + 1) n rfl)
  · obtain ⟨N₁, h₁⟩ := h₁.2
    obtain ⟨N₂, h₂⟩ := h₂.2
    refine ⟨max N₁ N₂ + 1, fun n hn ↦ ?_⟩
    cases n with
    | zero => omega
    | succ n =>
      exact (hS.homology_exact₃ (n + 1) n rfl).isZero_of_both_isZero
        (h₂ (n + 1) (by omega)) (h₁ n (by omega))

end DifferentialGeometry.HomologicalComplex
