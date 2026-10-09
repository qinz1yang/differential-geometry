import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Instances.Real.Lemmas

set_option autoImplicit false

open Set Filter Topology

namespace DifferentialGeometry.Analysis

/-- On a compact set of angles, all zeros at sufficiently small nonnegative
radii lie in any open set containing the zeros at radius zero. -/
theorem exists_pos_radius_zero_mem_open_of_isCompact
    {ε : ℝ} (hε : 0 < ε) {W : ℝ × ℝ → ℝ}
    (hW : ContinuousOn W (Ico 0 ε ×ˢ (univ : Set ℝ)))
    {J O : Set ℝ} (hJ : IsCompact J) (hO : IsOpen O)
    (hzero : ∀ θ ∈ J, W (0, θ) = 0 → θ ∈ O) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ ε ∧
      ∀ r ∈ Ico 0 δ, ∀ θ ∈ J, W (r, θ) = 0 → θ ∈ O := by
  let R := Ico (0 : ℝ) ε
  let r₀ : R := ⟨0, le_rfl, hε⟩
  have hWR : Continuous (fun p : R × ℝ => W ((p.1 : ℝ), p.2)) :=
    hW.comp_continuous
      ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)
      (fun p => ⟨p.1.property, mem_univ _⟩)
  have hevent : ∀ᶠ r : R in 𝓝 r₀, ∀ θ ∈ J \ O, W ((r : ℝ), θ) ≠ 0 := by
    apply (hJ.diff hO).eventually_forall_of_forall_eventually
    intro θ hθ
    exact hWR.continuousAt.eventually_ne (fun h => hθ.2 (hzero θ hθ.1 h))
  obtain ⟨d, hd, hnear⟩ := Metric.eventually_nhds_iff.mp hevent
  refine ⟨min ε d, lt_min hε hd, min_le_left _ _, ?_⟩
  intro r hr θ hθ hzeroR
  by_contra hθO
  let rR : R := ⟨r, hr.1, hr.2.trans_le (min_le_left _ _)⟩
  have hdist : dist rR r₀ < d := by
    change dist r (0 : ℝ) < d
    simpa only [Real.dist_eq, sub_zero, abs_of_nonneg hr.1] using
      hr.2.trans_le (min_le_right ε d)
  exact hnear hdist θ ⟨hθ, hθO⟩ hzeroR

end DifferentialGeometry.Analysis
