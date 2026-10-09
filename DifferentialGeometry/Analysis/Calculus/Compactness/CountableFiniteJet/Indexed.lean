import DifferentialGeometry.Analysis.Calculus.Compactness.CountableFiniteJet.Eventual
import Mathlib.Basic.Countable.Defs






set_option autoImplicit false
noncomputable section
open Filter Topology
open scoped ContDiff
namespace DifferentialGeometry.CheegerGromovCompactness
universe u v w

theorem exists_countable_indexed_finite_order_subsequence_of_eventual_regularity
    {ι : Type w} [Countable ι]
    (E : ι → Type u) (F : ι → Type v)
    [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℝ (E i)]
    [∀ i, NormedAddCommGroup (F i)] [∀ i, NormedSpace ℝ (F i)]
    [∀ i, FiniteDimensional ℝ (E i)] [∀ i, FiniteDimensional ℝ (F i)]
    (U : ∀ i, Set (E i)) (hU : ∀ i, IsOpen (U i)) (p : ι → ℕ)
    (f : ∀ i, ℕ → E i → F i)
    (hf : ∀ i, ∀ᶠ k in atTop,
      ContDiffOn ℝ ((p i + 1 : ℕ) : ℕ∞ω) (f i k) (U i))
    (hjets : ∀ i q, q ≤ p i + 1 → ∀ S : Set (E i), IsCompact S → S ⊆ U i →
      ∃ C : ℝ, ∀ᶠ k in atTop, ∀ x ∈ S, ‖iteratedFDeriv ℝ q (f i k) x‖ ≤ C) :
    ∃ (φ : ℕ → ℕ) (fLimit : ∀ i, E i → F i), StrictMono φ ∧ ∀ i,
      ContDiffOn ℝ (p i : ℕ∞ω) (fLimit i) (U i) ∧
      ∀ S : Set (E i), IsCompact S → S ⊆ U i →
        MapCPConvergenceOn S (p i) (fun k => f i (φ k)) (fLimit i) := by
  classical
  rcases isEmpty_or_nonempty ι with hempty | hnonempty
  · let : IsEmpty ι := hempty
    exact ⟨id, (fun _ _ => 0), strictMono_id, fun i => isEmptyElim i⟩
  · let : Nonempty ι := hnonempty
    obtain ⟨enumerate, henum⟩ := exists_surjective_nat ι
    obtain ⟨φ, g, hφ, hg⟩ :=
      exists_countable_family_finite_order_subsequence_of_eventual_regularity
        (fun j => E (enumerate j)) (fun j => F (enumerate j))
        (fun j => U (enumerate j)) (fun j => hU (enumerate j))
        (fun j => p (enumerate j)) (fun j => f (enumerate j))
        (fun j => hf (enumerate j)) (fun j => hjets (enumerate j))
    have hex (i : ι) : ∃ gᵢ : E i → F i,
        ContDiffOn ℝ (p i : ℕ∞ω) gᵢ (U i) ∧
        ∀ S : Set (E i), IsCompact S → S ⊆ U i →
          MapCPConvergenceOn S (p i) (fun k => f i (φ k)) gᵢ := by
      obtain ⟨j, rfl⟩ := henum i
      exact ⟨g j, hg j⟩
    choose fLimit hlimit using hex
    exact ⟨φ, fLimit, hφ, hlimit⟩

end DifferentialGeometry.CheegerGromovCompactness
