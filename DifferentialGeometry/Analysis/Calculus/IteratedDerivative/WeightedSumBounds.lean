import Mathlib.Analysis.Calculus.ContDiff.Bounds

set_option autoImplicit false

noncomputable section

open scoped BigOperators Topology NNReal

variable {𝕜 E F ι : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

theorem norm_iteratedFDeriv_sum_smul_sub_le
    (S : Finset ι) {w : ι → E → 𝕜} (v : ι → F) (v₀ : F) {n : ℕ} {x : E}
    (hw : ∀ i ∈ S, ContDiffAt 𝕜 n (w i) x)
    (hsum : ∀ᶠ y in 𝓝 x, ∑ i ∈ S, w i y = 1) :
    ‖iteratedFDeriv 𝕜 n (fun y => (∑ i ∈ S, w i y • v i) - v₀) x‖ ≤
      ∑ i ∈ S, ‖iteratedFDeriv 𝕜 n (w i) x‖ * ‖v i - v₀‖ := by
  classical
  have heq : (fun y => (∑ i ∈ S, w i y • v i) - v₀) =ᶠ[𝓝 x]
      (fun y => ∑ i ∈ S, w i y • (v i - v₀)) := by
    filter_upwards [hsum] with y hy
    simp only [smul_sub, Finset.sum_sub_distrib, ← Finset.sum_smul, hy, one_smul]
  rw [(heq.iteratedFDeriv 𝕜 n).self_of_nhds,
    iteratedFDeriv_fun_sum_apply (fun i hi => (hw i hi).smul_const (v i - v₀))]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro i hi
  have h := (ContinuousLinearMap.toSpanSingleton 𝕜 (v i - v₀)).norm_iteratedFDeriv_comp_left
    (hw i hi) le_rfl
  simpa only [Function.comp_def, ContinuousLinearMap.toSpanSingleton_apply,
    ContinuousLinearMap.norm_toSpanSingleton, mul_comm] using h

theorem norm_iteratedFDeriv_sum_smul_sub_le_card_mul
    (S : Finset ι) {w : ι → E → 𝕜} (v : ι → F) (v₀ : F) {n : ℕ} {x : E}
    (hw : ∀ i ∈ S, ContDiffAt 𝕜 n (w i) x)
    (hsum : ∀ᶠ y in 𝓝 x, ∑ i ∈ S, w i y = 1) (B δ : ℝ≥0)
    (hB : ∀ i ∈ S, ‖iteratedFDeriv 𝕜 n (w i) x‖ ≤ B)
    (hδ : ∀ i ∈ S, ‖v i - v₀‖ ≤ δ) :
    ‖iteratedFDeriv 𝕜 n (fun y => (∑ i ∈ S, w i y • v i) - v₀) x‖ ≤
      S.card * (B : ℝ) * δ := by
  apply (norm_iteratedFDeriv_sum_smul_sub_le S v v₀ hw hsum).trans
  calc
    _ ≤ ∑ i ∈ S, (B : ℝ) * δ := by
      apply Finset.sum_le_sum
      intro i hi
      exact mul_le_mul (hB i hi) (hδ i hi) (norm_nonneg _) B.coe_nonneg
    _ = S.card * (B : ℝ) * δ := by simp only [Finset.sum_const, nsmul_eq_mul]; ring
