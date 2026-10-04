import DifferentialGeometry.Analysis.Calculus.Compactness.FiniteJet
import DifferentialGeometry.Topology.Sequences.DiagonalSubsequence

set_option autoImplicit false
noncomputable section
open Filter Topology

namespace DifferentialGeometry.CheegerGromovCompactness

universe u v

theorem exists_countable_family_finite_order_subsequence
    (E : ℕ → Type u) (F : ℕ → Type v)
    [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℝ (E i)]
    [∀ i, NormedAddCommGroup (F i)] [∀ i, NormedSpace ℝ (F i)]
    [∀ i, FiniteDimensional ℝ (E i)] [∀ i, FiniteDimensional ℝ (F i)]
    (U : ∀ i, Set (E i)) (hU : ∀ i, IsOpen (U i)) (p : ℕ → ℕ)
    (f : ∀ i, ℕ → E i → F i)
    (hf : ∀ i k, ContDiffOn ℝ ((p i + 1 : ℕ) : WithTop ℕ∞) (f i k) (U i))
    (hjets : ∀ i q, q ≤ p i + 1 → ∀ S : Set (E i), IsCompact S → S ⊆ U i →
      ∃ C : ℝ, ∀ᶠ k in atTop, ∀ x ∈ S, ‖iteratedFDeriv ℝ q (f i k) x‖ ≤ C) :
    ∃ (φ : ℕ → ℕ) (fLimit : ∀ i, E i → F i), StrictMono φ ∧ ∀ i,
      ContDiffOn ℝ (p i : WithTop ℕ∞) (fLimit i) (U i) ∧
      ∀ S : Set (E i), IsCompact S → S ⊆ U i →
        MapCPConvergenceOn S (p i) (fun k => f i (φ k)) (fLimit i) := by
  classical
  have hextract (i : ℕ) (σ : {σ : ℕ → ℕ // StrictMono σ}) :
      ∃ (ρ : ℕ → ℕ) (L : E i → F i), StrictMono ρ ∧
        ContDiffOn ℝ (p i : WithTop ℕ∞) L (U i) ∧
        ∀ S : Set (E i), IsCompact S → S ⊆ U i →
          MapCPConvergenceOn S (p i) (fun k => f i (σ.1 (ρ k))) L := by
    apply exists_finite_order_subseq_on_of_eventually_bounded (hU i) (p i)
      (fun k => f i (σ.1 k)) (fun k => hf i (σ.1 k))
    intro r hr S hS hSU
    obtain ⟨C, hC⟩ := hjets i r hr S hS hSU
    exact ⟨C, hC.filter_mono σ.2.tendsto_atTop⟩
  choose ρ L hρ hL hconv using hextract
  let q : ℕ → {σ : ℕ → ℕ // StrictMono σ} :=
    fun n => Nat.rec ⟨id, strictMono_id⟩
      (fun i σ => ⟨σ.1 ∘ ρ i σ, σ.2.comp (hρ i σ)⟩) n
  have hnest (i : ℕ) : Set.range (q (i + 1)).1 ⊆ Set.range (q i).1 := by
    rintro _ ⟨k, rfl⟩
    exact ⟨ρ i (q i) k, rfl⟩
  obtain ⟨φ, hφ, htail⟩ :=
    DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.exists_strictMono_diagonal_of_nested_ranges
      (fun i => (q i).1) (fun i => (q i).2) hnest
  refine ⟨φ, fun i => L i (q i), hφ, fun i => ⟨hL i (q i), ?_⟩⟩
  intro S hS hSU
  have hc := hconv i (q i) S hS hSU
  change MapCPConvergenceOn S (p i) (fun k => f i ((q (i + 1)).1 k)) _ at hc
  obtain ⟨r, hr, heq⟩ := htail (i + 1)
  have hc' := hc.comp_subseq hr
  intro ε hε
  obtain ⟨N, hN⟩ := hc' ε hε
  refine ⟨i + 1 + N, fun k hk j hj x hx => ?_⟩
  have hk' : N ≤ k - (i + 1) := by omega
  have hb := hN (k - (i + 1)) hk' j hj x hx
  have hi : i + 1 ≤ k := by omega
  have heq' : φ k = (q (i + 1)).1 (r (k - (i + 1))) := by
    simpa only [Nat.add_sub_of_le hi] using heq (k - (i + 1))
  change mapDerivNorm j (f i (φ k)) (L i (q i)) x ≤ ε
  rw [heq']
  exact hb


theorem exists_countable_family_finite_order_bilinear_limits
    (E : ℕ → Type u)
    [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℝ (E i)]
    [∀ i, FiniteDimensional ℝ (E i)]
    (U : ∀ i, Set (E i)) (hU : ∀ i, IsOpen (U i)) (p : ℕ → ℕ)
    (g : ∀ i, ℕ → E i → E i →L[ℝ] E i →L[ℝ] ℝ)
    (hg : ∀ i k, ContDiffOn ℝ ((p i + 1 : ℕ) : WithTop ℕ∞) (g i k) (U i))
    (hjets : ∀ i q, q ≤ p i + 1 → ∀ S : Set (E i), IsCompact S → S ⊆ U i →
      ∃ C : ℝ, ∀ᶠ k in atTop, ∀ x ∈ S, ‖iteratedFDeriv ℝ q (g i k) x‖ ≤ C)
    (lower upper : ℕ → ℝ)
    (hsymm : ∀ i, ∀ᶠ k in atTop, ∀ x ∈ U i, ∀ v w,
      g i k x v w = g i k x w v)
    (helliptic : ∀ i, ∀ᶠ k in atTop, ∀ x ∈ U i, ∀ v,
      lower i * ‖v‖ ^ 2 ≤ g i k x v v ∧ g i k x v v ≤ upper i * ‖v‖ ^ 2) :
    ∃ (φ : ℕ → ℕ) (gLimit : ∀ i, E i → E i →L[ℝ] E i →L[ℝ] ℝ),
      StrictMono φ ∧ ∀ i,
      ContDiffOn ℝ (p i : WithTop ℕ∞) (gLimit i) (U i) ∧
      (∀ S : Set (E i), IsCompact S → S ⊆ U i →
        MapCPConvergenceOn S (p i) (fun k => g i (φ k)) (gLimit i)) ∧
      (∀ x ∈ U i, ∀ v w, gLimit i x v w = gLimit i x w v) ∧
      (∀ x ∈ U i, ∀ v,
        lower i * ‖v‖ ^ 2 ≤ gLimit i x v v ∧ gLimit i x v v ≤ upper i * ‖v‖ ^ 2) := by
  obtain ⟨φ, gLimit, hφ, hlimit⟩ :=
    exists_countable_family_finite_order_subsequence E (fun i => E i →L[ℝ] E i →L[ℝ] ℝ)
      U hU p g hg hjets
  refine ⟨φ, gLimit, hφ, fun i => ⟨(hlimit i).1, (hlimit i).2, ?_, ?_⟩⟩
  · intro x hx v w
    have htend := (tendstoUniformlyOn_of_cPConvergence
      (((hlimit i).2 {x} isCompact_singleton (Set.singleton_subset_iff.mpr hx)).mono_order
        (Nat.zero_le (p i)))).tendsto_at rfl
    have hcont : ∀ a b : E i, Continuous (fun c : E i →L[ℝ] E i →L[ℝ] ℝ => c a b) := by
      intro a b; fun_prop
    have he := (hsymm i).filter_mono hφ.tendsto_atTop
    exact tendsto_nhds_unique (((hcont v w).tendsto _).comp htend)
      ((((hcont w v).tendsto _).comp htend).congr'
        (he.mono fun _ hk => (hk x hx v w).symm))
  · intro x hx v
    have htend := (tendstoUniformlyOn_of_cPConvergence
      (((hlimit i).2 {x} isCompact_singleton (Set.singleton_subset_iff.mpr hx)).mono_order
        (Nat.zero_le (p i)))).tendsto_at rfl
    have hcont : Continuous (fun c : E i →L[ℝ] E i →L[ℝ] ℝ => c v v) := by fun_prop
    have heval := (hcont.tendsto _).comp htend
    have he := (helliptic i).filter_mono hφ.tendsto_atTop
    exact ⟨ge_of_tendsto heval (he.mono fun _ hk => (hk x hx v).1),
      le_of_tendsto heval (he.mono fun _ hk => (hk x hx v).2)⟩

end DifferentialGeometry.CheegerGromovCompactness
