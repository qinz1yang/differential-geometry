import DifferentialGeometry.Analysis.Calculus.Compactness.CountableFiniteJet.Indexed
import DifferentialGeometry.Analysis.Calculus.MapConvergence.Derivative


set_option autoImplicit false
noncomputable section
open Filter Topology Set
namespace DifferentialGeometry.CheegerGromovCompactness
universe u

theorem exists_mixed_finite_order_subsequence_with_prescribed_limits
    {ι κ : Type*} {E F : Type u} [Countable ι] [Countable κ]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    (m n : ℕ) {U : ι → Set E} {V : κ → Set E}
    (hU : ∀ i, IsOpen (U i)) (hV : ∀ j, IsOpen (V j))
    (B : ι → ℕ → E → F) (Φ : κ → ℕ → E → E) (T : κ → E → E)
    (hB : ∀ i, ∀ᶠ k in atTop, ContDiffOn ℝ (m + 1 : ℕ) (B i k) (U i))
    (hΦ : ∀ j, ∀ᶠ k in atTop, ContDiffOn ℝ (n + 1 : ℕ) (Φ j k) (V j))
    (hbB : ∀ i (D : Set E), IsCompact D → D ⊆ U i → ∀ r : ℕ, r ≤ m + 1 →
      ∃ M : ℝ, ∀ᶠ k in atTop, ∀ x ∈ D, ‖iteratedFDeriv ℝ r (B i k) x‖ ≤ M)
    (hbΦ : ∀ j (D : Set E), IsCompact D → D ⊆ V j → ∀ r : ℕ, r ≤ n + 1 →
      ∃ M : ℝ, ∀ᶠ k in atTop, ∀ x ∈ D, ‖iteratedFDeriv ℝ r (Φ j k) x‖ ≤ M)
    (hT : ∀ j x, x ∈ V j → Tendsto (fun k => Φ j k x) atTop (𝓝 (T j x))) :
    ∃ (σ : ℕ → ℕ) (b : ι → E → F), StrictMono σ ∧
      (∀ i, ContDiffOn ℝ m (b i) (U i) ∧
        ∀ D : Set E, IsCompact D → D ⊆ U i →
          MapCPConvergenceOn D m (fun k => B i (σ k)) (b i)) ∧
      (∀ j, ContDiffOn ℝ n (T j) (V j) ∧
        ∀ D : Set E, IsCompact D → D ⊆ V j →
          MapCPConvergenceOn D n (fun k => Φ j (σ k)) (T j)) := by
  let G : ι ⊕ κ → Type u := Sum.elim (fun _ => F) (fun _ => E)
  let : ∀ i, NormedAddCommGroup (G i) := fun i => match i with
    | .inl _ => (inferInstance : NormedAddCommGroup F)
    | .inr _ => (inferInstance : NormedAddCommGroup E)
  let : ∀ i, NormedSpace ℝ (G i) := fun i => match i with
    | .inl _ => (inferInstance : NormedSpace ℝ F)
    | .inr _ => (inferInstance : NormedSpace ℝ E)
  let : ∀ i, FiniteDimensional ℝ (G i) := fun i => match i with
    | .inl _ => (inferInstance : FiniteDimensional ℝ F)
    | .inr _ => (inferInstance : FiniteDimensional ℝ E)
  let W : ι ⊕ κ → Set E := Sum.elim U V
  let r : ι ⊕ κ → ℕ := Sum.elim (fun _ => m) (fun _ => n)
  let Ψ : ∀ i : ι ⊕ κ, ℕ → E → G i := fun i => match i with
    | .inl j => B j
    | .inr j => Φ j
  have hW : ∀ i, IsOpen (W i) := by intro i; cases i with
    | inl i => exact hU i
    | inr j => exact hV j
  have hΨ : ∀ i, ∀ᶠ k in atTop, ContDiffOn ℝ (r i + 1 : ℕ) (Ψ i k) (W i) := by
    intro i; cases i with
    | inl i => exact hB i
    | inr j => exact hΦ j
  have hbΨ : ∀ i (D : Set E), IsCompact D → D ⊆ W i → ∀ l : ℕ, l ≤ r i + 1 →
      ∃ M : ℝ, ∀ᶠ k in atTop, ∀ x ∈ D, ‖iteratedFDeriv ℝ l (Ψ i k) x‖ ≤ M := by
    intro i; cases i with
    | inl i => exact hbB i
    | inr j => exact hbΦ j
  obtain ⟨σ, g, hσ, hg⟩ :=
    exists_countable_indexed_finite_order_subsequence_of_eventual_regularity
      (fun _ : ι ⊕ κ => E) G W hW r Ψ hΨ
      (fun i q hq D hD hDW => hbΨ i D hD hDW q hq)
  refine ⟨σ, fun i => g (.inl i), hσ, fun i => hg (.inl i), fun j => ?_⟩
  have heq : Set.EqOn (T j) (g (.inr j)) (V j) := by
    intro x hx
    have hlimit := (tendstoUniformlyOn_of_cPConvergence
      (((hg (.inr j)).2 {x} isCompact_singleton (Set.singleton_subset_iff.mpr hx)).mono_order
        (Nat.zero_le n))).tendsto_at (Set.mem_singleton x)
    exact tendsto_nhds_unique ((hT j x hx).comp hσ.tendsto_atTop) hlimit
  refine ⟨(hg (.inr j)).1.congr (fun x hx => heq hx), ?_⟩
  intro D hD hDV
  exact ((hg (.inr j)).2 D hD hDV).congr (hV j) hDV
    (fun _ _ _ => rfl) heq

end DifferentialGeometry.CheegerGromovCompactness
