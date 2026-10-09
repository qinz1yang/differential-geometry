import DifferentialGeometry.Analysis.Calculus.Compactness.CountableFiniteJet

set_option autoImplicit false

noncomputable section
open Filter Topology
open scoped ContDiff

namespace DifferentialGeometry.CheegerGromovCompactness

universe u v

theorem exists_countable_family_finite_order_subsequence_of_eventual_regularity
    (E : ℕ → Type u) (F : ℕ → Type v)
    [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℝ (E i)]
    [∀ i, NormedAddCommGroup (F i)] [∀ i, NormedSpace ℝ (F i)]
    [∀ i, FiniteDimensional ℝ (E i)] [∀ i, FiniteDimensional ℝ (F i)]
    (U : ∀ i, Set (E i)) (hU : ∀ i, IsOpen (U i)) (p : ℕ → ℕ)
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
  let f' (i k : ℕ) : E i → F i :=
    if ContDiffOn ℝ ((p i + 1 : ℕ) : ℕ∞ω) (f i k) (U i) then f i k else 0
  have hf' (i k : ℕ) : ContDiffOn ℝ ((p i + 1 : ℕ) : ℕ∞ω) (f' i k) (U i) := by
    dsimp only [f']
    split_ifs with h
    · exact h
    · exact contDiffOn_const
  have hjets' : ∀ i q, q ≤ p i + 1 → ∀ S : Set (E i), IsCompact S → S ⊆ U i →
      ∃ C : ℝ, ∀ᶠ k in atTop, ∀ x ∈ S, ‖iteratedFDeriv ℝ q (f' i k) x‖ ≤ C := by
    intro i q hq S hS hSU
    obtain ⟨C, hC⟩ := hjets i q hq S hS hSU
    refine ⟨C, ?_⟩
    filter_upwards [hf i, hC] with k hk hc
    simpa only [f', ite_eq_left hk] using hc
  obtain ⟨φ, fLimit, hφ, hlimit⟩ :=
    exists_countable_family_finite_order_subsequence E F U hU p f' hf' hjets'
  refine ⟨φ, fLimit, hφ, fun i => ⟨(hlimit i).1, ?_⟩⟩
  intro S hS hSU ε hε
  obtain ⟨N, hN⟩ := (hlimit i).2 S hS hSU ε hε
  obtain ⟨Nreg, hNreg⟩ := eventually_atTop.mp (hφ.tendsto_atTop (hf i))
  refine ⟨max N Nreg, fun k hk q hq x hx => ?_⟩
  have hb := hN k ((le_max_left _ _).trans hk) q hq x hx
  have hreg : ContDiffOn ℝ ((p i + 1 : ℕ) : ℕ∞ω) (f i (φ k)) (U i) :=
    hNreg k ((le_max_right _ _).trans hk)
  have heq : f' i (φ k) = f i (φ k) := by
    dsimp only [f']
    exact ite_eq_left hreg
  change mapDerivNorm q (f' i (φ k)) (fLimit i) x ≤ ε at hb
  rwa [heq] at hb

end DifferentialGeometry.CheegerGromovCompactness
