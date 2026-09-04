import Mathlib.Topology.Order.Compact


import Mathlib.Topology.Sequences
import Mathlib.Topology.UniformSpace.Real
import Lean.Elab.Tactic.Omega

set_option autoImplicit false

namespace DifferentialGeometry
namespace CheegerGromovCompactness

open Filter Topology

theorem exists_subseq_tendsto_pi {C : ℕ → ℝ} (f : ℕ → ℕ → ℝ)
    (hbd : ∀ n k, f n k ∈ Set.Icc (0 : ℝ) (C n)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∀ n, ∃ L ∈ Set.Icc (0 : ℝ) (C n),
        Tendsto (fun k => f n (φ k)) atTop (𝓝 L) := by
  have : ∀ n : ℕ, CompactSpace (Set.Icc (0 : ℝ) (C n)) :=
    fun n => isCompact_iff_compactSpace.mp isCompact_Icc
  set x : ℕ → (Π n : ℕ, Set.Icc (0 : ℝ) (C n)) := fun k n => ⟨f n k, hbd n k⟩ with hx
  obtain ⟨a, -, φ, hφ, ha⟩ :=
    (isCompact_univ : IsCompact (Set.univ : Set (Π n : ℕ, Set.Icc (0 : ℝ) (C n)))).tendsto_subseq
      (x := x) (fun k => Set.mem_univ _)
  refine ⟨φ, hφ, fun n => ⟨(a n : ℝ), (a n).2, ?_⟩⟩
  have h1 : Tendsto (fun k => x (φ k) n) atTop (𝓝 (a n)) := by
    exact (tendsto_pi_nhds.mp ha) n
  have h2 := (continuous_subtype_val.tendsto (a n)).comp h1
  change Tendsto (fun k => (x (φ k) n : ℝ)) atTop (𝓝 (a n : ℝ)) at h2
  rw [hx] at h2
  exact h2

theorem exists_subseq_eventually_eq {ι : Type*} [Countable ι] (b : ι → ℕ → Bool) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∀ i, ∃ v : Bool, ∀ᶠ k in atTop, b i (φ k) = v := by
  set x : ℕ → (ι → Bool) := fun k i => b i k with hx
  obtain ⟨a, -, φ, hφ, ha⟩ :=
    (isCompact_univ : IsCompact (Set.univ : Set (ι → Bool))).tendsto_subseq
      (x := x) (fun k => Set.mem_univ _)
  refine ⟨φ, hφ, fun i => ⟨a i, ?_⟩⟩
  have h1 : Tendsto (fun k => x (φ k) i) atTop (𝓝 (a i)) := by
    exact (tendsto_pi_nhds.mp ha) i
  rw [nhds_discrete Bool] at h1
  exact tendsto_pure.mp h1

theorem exists_strictMono_ge (T : ℕ → ℕ) :
    ∃ σ : ℕ → ℕ, StrictMono σ ∧ ∀ j, T j ≤ σ j := by
  classical
  refine ⟨fun j => j + Finset.sup (Finset.range (j + 1)) T, ?_, ?_⟩
  · apply strictMono_nat_of_lt_succ
    intro n
    change n + Finset.sup (Finset.range (n + 1)) T
        < (n + 1) + Finset.sup (Finset.range (n + 1 + 1)) T
    have hsub : Finset.range (n + 1) ⊆ Finset.range (n + 1 + 1) :=
      Finset.range_mono (Nat.le_succ (n + 1))
    have hmono : Finset.sup (Finset.range (n + 1)) T
        ≤ Finset.sup (Finset.range (n + 1 + 1)) T :=
      Finset.sup_mono hsub
    calc n + Finset.sup (Finset.range (n + 1)) T
        ≤ n + Finset.sup (Finset.range (n + 1 + 1)) T := Nat.add_le_add_left hmono n
      _ < (n + 1) + Finset.sup (Finset.range (n + 1 + 1)) T := by omega
  · intro j
    change T j ≤ j + Finset.sup (Finset.range (j + 1)) T
    exact le_trans (Finset.le_sup (Finset.self_mem_range_succ j)) (Nat.le_add_left _ j)

end CheegerGromovCompactness
end DifferentialGeometry
