import DifferentialGeometry.Analysis.Calculus.Cutoff.Profile
import Mathlib.Geometry.Manifold.ContMDiffMap
import Mathlib.Geometry.Manifold.Algebra.Structures

noncomputable section

open Filter
open scoped ContDiff Manifold Topology

namespace DifferentialGeometry.Analysis

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M]

def sublevelCutoff (ρ : C^∞⟮I, M; ℝ⟯) (R : ℝ) : C^∞⟮I, M; ℝ⟯ :=
  ⟨fun x => CutoffProfile.value (ρ x / R),
    CutoffProfile.contDiff.contMDiff.comp (ρ.contMDiff.div_const R)⟩

theorem sublevelCutoff_mem_Icc (ρ : C^∞⟮I, M; ℝ⟯) (R : ℝ) (x : M) :
    sublevelCutoff ρ R x ∈ Set.Icc 0 1 :=
  CutoffProfile.mem_Icc _

theorem sublevelCutoff_eq_one (ρ : C^∞⟮I, M; ℝ⟯) {R : ℝ} (hR : 0 < R)
    {x : M} (hx : ρ x ≤ R) : sublevelCutoff ρ R x = 1 := by
  exact CutoffProfile.one_of_le_one ((div_le_one hR).2 hx)

theorem tsupport_sublevelCutoff_subset (ρ : C^∞⟮I, M; ℝ⟯) {R : ℝ} (hR : 0 < R) :
    tsupport (sublevelCutoff ρ R) ⊆ {x | ρ x ≤ 2 * R} :=
  CutoffProfile.tsupport_value_comp_div_subset_sublevel ρ.contMDiff.continuous hR

theorem hasCompactSupport_sublevelCutoff (ρ : C^∞⟮I, M; ℝ⟯) {R : ℝ} (hR : 0 < R)
    (hc : IsCompact {x | ρ x ≤ 2 * R}) : HasCompactSupport (sublevelCutoff ρ R) :=
  CutoffProfile.hasCompactSupport_value_comp_div ρ.contMDiff.continuous hR hc

theorem sublevelCutoff_eventually_eq_one (ρ : C^∞⟮I, M; ℝ⟯) (x : M) :
    ∀ᶠ R in atTop, sublevelCutoff ρ R x = 1 := by
  filter_upwards [eventually_gt_atTop (0 : ℝ), eventually_ge_atTop (ρ x)] with R hR hx
  exact sublevelCutoff_eq_one ρ hR hx

theorem sublevelCutoff_eventually_eq_one_on_compact (ρ : C^∞⟮I, M; ℝ⟯)
    {K : Set M} (hK : IsCompact K) :
    ∀ᶠ R in atTop, ∀ x ∈ K, sublevelCutoff ρ R x = 1 := by
  obtain ⟨B, hB⟩ := hK.bddAbove_image ρ.contMDiff.continuous.continuousOn
  filter_upwards [eventually_gt_atTop (0 : ℝ), eventually_ge_atTop B] with R hR hBR x hx
  exact sublevelCutoff_eq_one ρ hR ((hB (Set.mem_image_of_mem ρ hx)).trans hBR)

end DifferentialGeometry.Analysis
