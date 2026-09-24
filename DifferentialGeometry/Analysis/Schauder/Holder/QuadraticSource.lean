import DifferentialGeometry.Analysis.Schauder.Holder.Cutoff

noncomputable section
open Set
open scoped NNReal ENNReal

namespace DifferentialGeometry.Analysis.Schauder

variable {X ι κ : Type*} [PseudoMetricSpace X] [Fintype ι] [Fintype κ]

theorem exists_holderOnWith_quadratic_sum
    {s : Set X} (hs : IsCompact s) {α : ℝ≥0} (hα : 0 < α)
    {a : ι → ι → X → ℝ} {G : ι → κ → X → ℝ}
    {Ka : ι → ι → ℝ≥0} {KG : ι → κ → ℝ≥0}
    (ha : ∀ i j, HolderOnWith (Ka i j) α (a i j) s)
    (hG : ∀ i k, HolderOnWith (KG i k) α (G i k) s) :
    ∃ C : ℝ≥0, HolderOnWith C α
      (fun x => ∑ k, ∑ i, ∑ j, a i j x * G i k x * G j k x) s := by
  have hbound {f : X → ℝ} (hc : ContinuousOn f s) :
      ∃ B : ℝ≥0, ∀ x ∈ s, ‖f x‖ ≤ B := by
    obtain ⟨B, hB⟩ := hs.exists_bound_of_continuousOn hc
    exact ⟨⟨max B 0, le_max_right _ _⟩, fun x hx => (hB x hx).trans (le_max_left _ _)⟩
  choose Ma hMa using fun i j => hbound ((ha i j).continuousOn hα)
  choose MG hMG using fun i k => hbound ((hG i k).continuousOn hα)
  have hprod (i j : ι) (k : κ) : ∃ C : ℝ≥0, HolderWith C α
      (s.domRestrict (fun x => a i j x * G i k x * G j k x)) := by
    have h₁ := holderWith_smul_of_norm_le (ha i j).holderWith (hG i k).holderWith
      (fun x => hMa i j x x.2) (fun x => hMG i k x x.2)
    have hm (x : s) :
        ‖(s.domRestrict (a i j) • s.domRestrict (G i k)) x‖ ≤ (Ma i j * MG i k : ℝ≥0) := by
      change ‖a i j x * G i k x‖ ≤ (Ma i j * MG i k : ℝ≥0)
      rw [norm_mul, NNReal.coe_mul]
      exact mul_le_mul (hMa i j x x.2) (hMG i k x x.2) (norm_nonneg _) (Ma i j).coe_nonneg
    have h₂ := holderWith_smul_of_norm_le h₁ (hG j k).holderWith hm (fun x => hMG j k x x.2)
    exact ⟨_, h₂⟩
  choose C hC using hprod
  refine ⟨∑ k, ∑ i, ∑ j, C i j k, ?_⟩
  apply HolderWith.restrict_iff.mp
  exact holderWith_finset_sum Finset.univ fun k _ =>
    holderWith_finset_sum Finset.univ fun i _ =>
      holderWith_finset_sum Finset.univ fun j _ => hC i j k

theorem exists_holderOnWith_quadratic_sum_of_contDiffOn_coefficients
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {s : Set X} (hs : IsCompact s) {U : Set F} (hU : IsOpen U)
    {z : X → F} {α Kz : ℝ≥0} (hα : 0 < α) (hz : HolderOnWith Kz α z s)
    (hzU : MapsTo z s U) {a : ι → ι → F → ℝ}
    (ha : ∀ i j, ContDiffOn ℝ 1 (a i j) U)
    {G : ι → κ → X → ℝ} {KG : ι → κ → ℝ≥0}
    (hG : ∀ i k, HolderOnWith (KG i k) α (G i k) s) :
    ∃ C : ℝ≥0, HolderOnWith C α
      (fun x => ∑ k, ∑ i, ∑ j, a i j (z x) * G i k x * G j k x) s := by
  choose Ka hKa using fun i j =>
    exists_holderOnWith_comp_of_contDiffOn_isCompact hs hU hz hα hzU (ha i j)
  exact exists_holderOnWith_quadratic_sum hs hα hKa hG

end DifferentialGeometry.Analysis.Schauder

end
