import DifferentialGeometry.Topology.Compactness.CountableSubsequence
import DifferentialGeometry.Analysis.Integration.Measure.CountableAEConvergence
import Mathlib.MeasureTheory.Function.LpSpace.Complete

section

open Filter
open scoped ENNReal Topology

namespace MeasureTheory

theorem exists_seq_tendsto_ae_of_countable_Lp_subseq
    {A I : Type*} {E : I → Type*} [MeasurableSpace A] [Countable I]
    [∀ i, NormedAddCommGroup (E i)] {μ : Measure A} {p : ℝ≥0∞}
    (hp : 1 ≤ p) (f : ℕ → ∀ i, A → E i)
    (hf : ∀ n i, MemLp (f n i) p μ)
    (hcompact : ∀ i (σ : ℕ → ℕ), StrictMono σ →
      ∃ τ : ℕ → ℕ, StrictMono τ ∧ ∃ g : A → E i, MemLp g p μ ∧
        Tendsto (fun n => eLpNorm (f (σ (τ n)) i - g) p μ) atTop (𝓝 0)) :
    ∃ (φ : ℕ → ℕ) (g : ∀ i, A → E i), StrictMono φ ∧
      (∀ i, MemLp (g i) p μ) ∧
      ∀ᵐ z ∂μ, ∀ i, Tendsto (fun n => f (φ n) i z) atTop (𝓝 (g i z)) := by
  classical
  let _ : Fact (1 ≤ p) := ⟨hp⟩
  let F : ℕ → ∀ i, Lp (E i) p μ := fun n i => (hf n i).toLp (f n i)
  have hF : ∀ i (σ : ℕ → ℕ), StrictMono σ →
      ∃ τ : ℕ → ℕ, StrictMono τ ∧ ∃ v : Lp (E i) p μ,
        Tendsto (fun n => F (σ (τ n)) i) atTop (𝓝 v) := by
    intro i σ hσ
    obtain ⟨τ, hτ, g, hg, hlim⟩ := hcompact i σ hσ
    refine ⟨τ, hτ, hg.toLp g, ?_⟩
    exact (Lp.tendsto_Lp_iff_tendsto_eLpNorm''
      (fun n => f (σ (τ n)) i) (fun n => hf (σ (τ n)) i) g hg).mpr hlim
  obtain ⟨φ, hφ, hlim⟩ := exists_subseq_tendsto_of_countable_coordinatewise_subseq F hF
  choose v hv using hlim
  let g : ∀ i, A → E i := fun i => v i
  have hraw : ∀ i, TendstoInMeasure μ (fun n => f (φ n) i) atTop (g i) := by
    intro i
    exact TendstoInMeasure.congr
      (fun n => (hf (φ n) i).coeFn_toLp) Filter.EventuallyEq.rfl
      (tendstoInMeasure_of_tendsto_Lp (hv i))
  obtain ⟨ψ, hψ, hae⟩ := exists_seq_tendsto_ae_of_countable_tendstoInMeasure hraw
  refine ⟨φ ∘ ψ, g, hφ.comp hψ, fun i => Lp.memLp (v i), ?_⟩
  exact hae

end MeasureTheory

end
