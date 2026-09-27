import DifferentialGeometry.Analysis.Calculus.MapConvergence.Composition
import DifferentialGeometry.Analysis.Calculus.MapConvergence.SmoothInverseOn

section

set_option autoImplicit false
noncomputable section
namespace DifferentialGeometry
namespace CheegerGromovCompactness
open Filter Topology

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

theorem exists_finite_smooth_inverse_limit_subsequence_on
    {ι : Type*} [Finite ι]
    (U : ι → Set E) (V : ι → Set F)
    (Φ : ι → ℕ → E → F) (Ψ : ι → ℕ → F → E)
    (hU : ∀ i, IsOpen (U i)) (hV : ∀ i, IsOpen (V i))
    (hΦ : ∀ i k, ContDiffOn ℝ (⊤ : ℕ∞) (Φ i k) (U i))
    (hΨ : ∀ i k, ContDiffOn ℝ (⊤ : ℕ∞) (Ψ i k) (V i))
    (hbΦ : ∀ i, iteratedFDerivBoundsOnCompactsWithin (U i) (Φ i))
    (hbΨ : ∀ i, iteratedFDerivBoundsOnCompactsWithin (V i) (Ψ i))
    (hLeft : ∀ i k, ∀ x ∈ U i, Ψ i k (Φ i k x) = x)
    (hRight : ∀ i k, ∀ y ∈ V i, Φ i k (Ψ i k y) = y) :
    ∃ (φ : ℕ → ℕ) (Φinf : ι → E → F) (Ψinf : ι → F → E),
      StrictMono φ ∧
      (∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (Φinf i) (U i) ∧
        ContDiffOn ℝ (⊤ : ℕ∞) (Ψinf i) (V i) ∧
        MapCInfConvergenceOnCompacts (U i) (fun k => Φ i (φ k)) (Φinf i) ∧
        MapCInfConvergenceOnCompacts (V i) (fun k => Ψ i (φ k)) (Ψinf i) ∧
        (∀ x ∈ U i, Φinf i x ∈ V i → Ψinf i (Φinf i x) = x) ∧
        (∀ y ∈ V i, Ψinf i y ∈ U i → Φinf i (Ψinf i y) = y)) := by
  classical
  let QΦ : (i : ι) → (E → F) → Prop :=
    fun i f => ContDiffOn ℝ (⊤ : ℕ∞) f (U i)
  have hstepΦ : ∀ i (τ : ℕ → ℕ), StrictMono τ →
      ∃ (σ : ℕ → ℕ) (f : E → F), StrictMono σ ∧
        MapCInfConvergenceOnCompacts (U i)
          (fun n => Φ i (τ (σ n))) f ∧ QΦ i f := by
    intro i τ _
    obtain ⟨σ, f, hσ, hf, hconv⟩ :=
      exists_c_inf_convergent_subsequence_on (hU i) (fun n => Φ i (τ n))
        (fun n => hΦ i (τ n)) ((hbΦ i).comp_subseq τ)
    exact ⟨σ, f, hσ, hconv, hf⟩
  obtain ⟨φ, hφ, hΦall⟩ := exists_cInf_finite U Φ QΦ hstepΦ
  let Φinf : ι → E → F := fun i => Classical.choose (hΦall i)
  have hΦspec (i : ι) :
      MapCInfConvergenceOnCompacts (U i) (fun k => Φ i (φ k)) (Φinf i) ∧
      QΦ i (Φinf i) := Classical.choose_spec (hΦall i)
  let QΨ : (i : ι) → (F → E) → Prop :=
    fun i f => ContDiffOn ℝ (⊤ : ℕ∞) f (V i)
  have hstepΨ : ∀ i (τ : ℕ → ℕ), StrictMono τ →
      ∃ (σ : ℕ → ℕ) (f : F → E), StrictMono σ ∧
        MapCInfConvergenceOnCompacts (V i)
          (fun n => Ψ i (φ (τ (σ n)))) f ∧ QΨ i f := by
    intro i τ _
    obtain ⟨σ, f, hσ, hf, hconv⟩ :=
      exists_c_inf_convergent_subsequence_on (hV i)
        (fun n => Ψ i (φ (τ n)))
        (fun n => hΨ i (φ (τ n)))
        ((hbΨ i).comp_subseq (φ ∘ τ))
    exact ⟨σ, f, hσ, hconv, hf⟩
  obtain ⟨ρ, hρ, hΨall⟩ := exists_cInf_finite V (fun i n => Ψ i (φ n)) QΨ hstepΨ
  let ψ : ℕ → ℕ := φ ∘ ρ
  let Ψinf : ι → F → E := fun i => Classical.choose (hΨall i)
  have hΨspec (i : ι) :
      MapCInfConvergenceOnCompacts (V i) (fun k => Ψ i (φ (ρ k))) (Ψinf i) ∧
      QΨ i (Ψinf i) := Classical.choose_spec (hΨall i)
  refine ⟨ψ, Φinf, Ψinf, hφ.comp hρ, ?_⟩
  intro i
  have hFconv : MapCInfConvergenceOnCompacts (U i)
      (fun k => Φ i (ψ k)) (Φinf i) := by
    simpa only [ψ, Function.comp_apply] using (hΦspec i).1.comp_subseq hρ
  have hRconv : MapCInfConvergenceOnCompacts (V i)
      (fun k => Ψ i (ψ k)) (Ψinf i) := by
    simpa only [ψ, Function.comp_apply] using (hΨspec i).1
  refine ⟨(hΦspec i).2, (hΨspec i).2, hFconv, hRconv, ?_, ?_⟩
  · intro x hx hxV
    exact comp_eq_id_of_mapCInfConvergenceOnCompacts_on (hV i) hRconv
      (hΨspec i).2.continuousOn hFconv (fun k x' hx' => hLeft i (ψ k) x' hx') hx hxV
  · intro y hy hyU
    exact comp_eq_id_of_mapCInfConvergenceOnCompacts_on (hU i) hFconv
      (hΦspec i).2.continuousOn hRconv (fun k y' hy' => hRight i (ψ k) y' hy') hy hyU

end CheegerGromovCompactness
end DifferentialGeometry

end

end
