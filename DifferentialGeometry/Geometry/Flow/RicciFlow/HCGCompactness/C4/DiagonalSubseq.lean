import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Sequences
import Mathlib.Topology.UniformSpace.Real

set_option autoImplicit false

/-!
# Simultaneous subsequence extraction via compact products

Two diagonal-free "diagonalization" lemmas: one strictly monotone subsequence along
which countably many uniformly bounded real sequences all converge
(`exists_subseq_tendsto_pi`), respectively countably many Boolean sequences all become
eventually constant (`exists_subseq_eventually_eq`).  Instead of an explicit diagonal
construction, the sequence is packaged into a countable product of compact metrizable
fibers — `Π n, Icc 0 (C n)`, resp. `ι → Bool` — which is compact and first countable,
hence sequentially compact; one subsequence works for every coordinate at once.

These serve the MSM135 Chapter 4 net diagonalization (`lbl389` → `lbl390`: radii
convergence, net-size and intersection-pattern stabilization), and are generic enough
for the spacetime Arzelà–Ascoli diagonalization of Lemma 3.11/P3.
-/

namespace DifferentialGeometry
namespace HCGCompactness

open Filter Topology

/-- Bolzano--Weierstrass for countably many uniformly bounded real sequences at once:
one strictly monotone subsequence along which every coordinate converges (with limit in
the same interval). -/
theorem exists_subseq_tendsto_pi {C : ℕ → ℝ} (f : ℕ → ℕ → ℝ)
    (hbd : ∀ n k, f n k ∈ Set.Icc (0 : ℝ) (C n)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∀ n, ∃ L ∈ Set.Icc (0 : ℝ) (C n),
        Tendsto (fun k => f n (φ k)) atTop (𝓝 L) := by
  haveI : ∀ n : ℕ, CompactSpace (Set.Icc (0 : ℝ) (C n)) :=
    fun n => isCompact_iff_compactSpace.mp isCompact_Icc
  set x : ℕ → (Π n : ℕ, Set.Icc (0 : ℝ) (C n)) := fun k n => ⟨f n k, hbd n k⟩ with hx
  obtain ⟨a, -, φ, hφ, ha⟩ :=
    (isCompact_univ : IsCompact (Set.univ : Set (Π n : ℕ, Set.Icc (0 : ℝ) (C n)))).tendsto_subseq
      (x := x) (fun k => Set.mem_univ _)
  refine ⟨φ, hφ, fun n => ⟨(a n : ℝ), (a n).2, ?_⟩⟩
  have h1 : Tendsto (fun k => x (φ k) n) atTop (𝓝 (a n)) := by
    exact (tendsto_pi_nhds.mp ha) n
  have h2 := (continuous_subtype_val.tendsto (a n)).comp h1
  simpa [hx, Function.comp] using h2

/-- Simultaneous stabilization of countably many Boolean sequences: one strictly
monotone subsequence along which each becomes eventually constant. -/
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

end HCGCompactness
end DifferentialGeometry
