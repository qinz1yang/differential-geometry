import DifferentialGeometry.Analysis.Calculus.Cutoff.Clamp.Smooth
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace

open Filter Set
open scoped ContDiff Manifold Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

theorem ContMDiffOn.exists_extension_uIcc {n : ℕ∞} {γ : ℝ → M} {U : Set ℝ} {a b : ℝ}
    (hγ : ContMDiffOn 𝓘(ℝ, ℝ) I n γ U) (hU : IsOpen U) (hseg : uIcc a b ⊆ U) :
    ∃ Γ : ℝ → M, ContMDiff 𝓘(ℝ, ℝ) I n Γ ∧
      ∀ t ∈ uIcc a b, Γ =ᶠ[𝓝 t] γ := by
  obtain ⟨margin, hmargin, hbuffer⟩ :=
    isCompact_uIcc.exists_cthickening_subset_open hU hseg
  let lo := min a b - margin / 2
  let hi := max a b + margin / 2
  let eps := margin / 4
  have hlo : lo < min a b := by dsimp [lo]; linarith
  have hhi : max a b < hi := by dsimp [hi]; linarith
  have horder : min a b ≤ max a b := min_le_max
  obtain ⟨ρ, hρ, hρ_id, _, hρ_range⟩ :=
    DifferentialGeometry.exists_smooth_time_clamp lo hi eps
      (hlo.trans (horder.trans_lt hhi)) (by dsimp [eps]; linarith)
  have hρU : ∀ s : ℝ, ρ s ∈ U := by
    intro s
    apply hbuffer
    by_cases hsa : ρ s ≤ min a b
    · refine Metric.mem_cthickening_of_dist_le (ρ s) (min a b) margin (uIcc a b)
        ⟨le_rfl, horder⟩ ?_
      rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hsa)]
      have hlo' := (hρ_range s).1
      dsimp [lo, eps] at hlo'
      linarith
    · by_cases hsb : ρ s ≤ max a b
      · exact Metric.mem_cthickening_of_dist_le (ρ s) (ρ s) margin (uIcc a b)
          ⟨(not_le.mp hsa).le, hsb⟩ (by simpa only [dist_self] using hmargin.le)
      · refine Metric.mem_cthickening_of_dist_le (ρ s) (max a b) margin (uIcc a b)
          ⟨horder, le_rfl⟩ ?_
        rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr (not_le.mp hsb).le)]
        have hhi' := (hρ_range s).2
        dsimp [hi, eps] at hhi'
        linarith
  have hρn : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) n ρ := by
    rw [contMDiff_iff_contDiff]
    exact hρ.of_le (by exact_mod_cast (le_top : n ≤ ⊤))
  refine ⟨γ ∘ ρ, hγ.comp_contMDiff hρn hρU, ?_⟩
  intro t ht
  have hN : Ioo lo hi ∈ 𝓝 t :=
    Ioo_mem_nhds (hlo.trans_le ht.1) (ht.2.trans_lt hhi)
  filter_upwards [hN] with s hs
  change γ (ρ s) = γ s
  rw [hρ_id s ⟨hs.1.le, hs.2.le⟩]
