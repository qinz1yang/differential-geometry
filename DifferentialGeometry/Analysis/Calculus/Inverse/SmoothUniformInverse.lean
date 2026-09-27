import DifferentialGeometry.Analysis.Calculus.Inverse.ParameterizedInverse
import DifferentialGeometry.Analysis.Calculus.Inverse.UniformInverse
import DifferentialGeometry.Analysis.Calculus.SmoothExtension.BorelHalfLine.Parametric
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Analysis.Calculus.Deriv.Prod

noncomputable section
open Set Filter Topology
open scoped ContDiff

namespace DifferentialGeometry.Analysis

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

theorem contDiffOn_inverse_of_continuousOn
    {h : E × ℝ → ℝ} {U S : Set (E × ℝ)} {R : E × ℝ → ℝ}
    (hh : ContDiffOn ℝ ∞ h U) (hU : IsOpen U)
    (hR : ContinuousOn R S)
    (hRU : ∀ q ∈ S, (q.1, R q) ∈ U)
    (heq : ∀ q ∈ S, h (q.1, R q) = q.2)
    (hvertical : ∀ q ∈ S, fderiv ℝ h (q.1, R q) (0, 1) ≠ 0) :
    ContDiffOn ℝ ∞ R S := by
  intro q hq
  obtain ⟨e, hp, _, _, heinv, he, _⟩ := exists_localInverse_preserving_parameter
    hh hU (hRU q hq) (hvertical q hq)
  have heq' : e (q.1, R q) = q := by rw [he, heq q hq]
  have htarget : q ∈ e.target := heq' ▸ e.map_source hp
  have hinv := (heinv.contDiffAt (e.open_target.mem_nhds htarget)).snd
  have hnear : ∀ᶠ z in 𝓝[S] q, (z.1, R z) ∈ e.source :=
    (continuousWithinAt_fst.prodMk (hR q hq)).preimage_mem_nhdsWithin
      (e.open_source.mem_nhds hp)
  have hagree : R =ᶠ[𝓝[S] q] fun z ↦ (e.symm z).2 := by
    filter_upwards [hnear, self_mem_nhdsWithin] with z hz hzS
    have hz' : e (z.1, R z) = z := by rw [he, heq z hzS]
    have h := congrArg Prod.snd (e.left_inv hz)
    simpa only [hz'] using h.symm
  have hat : R q = (e.symm q).2 := by
    have h := congrArg Prod.snd (e.left_inv hp)
    simpa only [heq'] using h.symm
  exact hinv.contDiffWithinAt.congr_of_eventuallyEq hagree hat

theorem exists_uniform_contDiffOn_inverse
    {h : E × ℝ → ℝ} {K : Set E} {U : Set (E × ℝ)} {ρ : ℝ}
    (hK : IsCompact K) (hρ : 0 < ρ)
    (hh : ContDiffOn ℝ ∞ h U) (hU : IsOpen U) (hKU : K ×ˢ Icc 0 ρ ⊆ U)
    (hzero : ∀ p ∈ K, h (p, 0) = 0)
    (hpos : ∀ p ∈ K, 0 < fderiv ℝ h (p, 0) (0, 1)) :
    ∃ ε > 0, ε ≤ ρ ∧ ∃ σ > 0, ∃ R : E × ℝ → ℝ,
      ContDiffOn ℝ ∞ R (K ×ˢ Icc 0 σ) ∧
      (∀ p ∈ K, R (p, 0) = 0) ∧
      ∀ q ∈ K ×ˢ Icc 0 σ,
        R q ∈ Icc 0 ε ∧ h (q.1, R q) = q.2 ∧
        ∀ r ∈ Icc 0 ε, h (q.1, r) = q.2 → r = R q := by
  classical
  let dh : E × ℝ → ℝ := fun z ↦ fderiv ℝ h z (0, 1)
  have hdh : ContinuousOn dh (K ×ˢ Icc 0 ρ) := by
    intro z hz
    exact (((hh.contDiffAt (hU.mem_nhds (hKU hz))).continuousAt_fderiv (by simp)).clm_apply
      continuousAt_const).continuousWithinAt
  have hderiv : ∀ p ∈ K, ∀ r ∈ Icc 0 ρ,
      HasDerivAt (fun t ↦ h (p, t)) (dh (p, r)) r := by
    intro p hp r hr
    exact ((hh.contDiffAt (hU.mem_nhds (hKU ⟨hp, hr⟩))).differentiableAt
      (by simp)).hasFDerivAt.comp_hasDerivAt r
        ((hasDerivAt_const r p).prodMk (hasDerivAt_id r))
  obtain ⟨ε, hε, hερ, σ, hσ, R, hc, hRzero, hR⟩ :=
    exists_uniform_continuous_inverse_of_pos_deriv hK hρ (hh.continuousOn.mono hKU) hdh
      (fun p hp r hr ↦ (hderiv p hp r hr).hasDerivWithinAt) hzero hpos
  have hsub : Icc (0 : ℝ) ε ⊆ Icc 0 ρ := Icc_subset_Icc_right hερ
  refine ⟨ε, hε, hερ, σ, hσ, R, ?_, hRzero,
    fun q hq ↦ ⟨(hR q hq).1, (hR q hq).2.1, (hR q hq).2.2.1⟩⟩
  exact contDiffOn_inverse_of_continuousOn hh hU hc
    (fun q hq ↦ hKU ⟨hq.1, hsub (hR q hq).1⟩)
    (fun q hq ↦ (hR q hq).2.1)
    (fun q hq ↦ ne_of_gt (hR q hq).2.2.2)

omit [CompleteSpace E] in
theorem exists_uniform_contDiffOn_inverse_of_one_sided [FiniteDimensional ℝ E]
    {h : E × ℝ → ℝ} {K V : Set E} {ρ : ℝ}
    (hK : IsCompact K) (hV : IsOpen V) (hKV : K ⊆ V) (hρ : 0 < ρ)
    (hh : ContDiffOn ℝ ∞ h (V ×ˢ Icc 0 ρ))
    (hzero : ∀ p ∈ K, h (p, 0) = 0)
    (hpos : ∀ p ∈ K, 0 < fderivWithin ℝ h (V ×ˢ Icc 0 ρ) (p, 0) (0, 1)) :
    ∃ ε > 0, ε ≤ ρ ∧ ∃ σ > 0, ∃ R : E × ℝ → ℝ,
      ContDiffOn ℝ ∞ R (K ×ˢ Icc 0 σ) ∧
      (∀ p ∈ K, R (p, 0) = 0) ∧
      ∀ q ∈ K ×ˢ Icc 0 σ,
        R q ∈ Icc 0 ε ∧ h (q.1, R q) = q.2 ∧
        ∀ r ∈ Icc 0 ε, h (q.1, r) = q.2 → r = R q := by
  let dh : E × ℝ → ℝ := fun z ↦ fderivWithin ℝ h (V ×ˢ Icc 0 ρ) z (0, 1)
  have hdiff : UniqueDiffOn ℝ (V ×ˢ Icc 0 ρ) := hV.uniqueDiffOn.prod (uniqueDiffOn_Icc hρ)
  have hdh : ContinuousOn dh (K ×ˢ Icc 0 ρ) :=
    ((hh.continuousOn_fderivWithin hdiff (by simp)).clm_apply continuousOn_const).mono
      (prod_mono hKV Subset.rfl)
  have hderiv : ∀ p ∈ K, ∀ r ∈ Icc 0 ρ,
      HasDerivWithinAt (fun t ↦ h (p, t)) (dh (p, r)) (Icc 0 ρ) r := by
    intro p hp r hr
    exact ((hh (p, r) ⟨hKV hp, hr⟩).differentiableWithinAt
      (by simp)).hasFDerivWithinAt.comp_hasDerivWithinAt r
        ((hasDerivAt_const r p).prodMk (hasDerivAt_id r)).hasDerivWithinAt
        (fun t ht ↦ ⟨hKV hp, ht⟩)
  obtain ⟨ε, hε, hερ, σ, hσ, R, hc, hRzero, hR⟩ :=
    exists_uniform_continuous_inverse_of_pos_deriv hK hρ
      (hh.continuousOn.mono (prod_mono hKV Subset.rfl)) hdh hderiv hzero hpos
  have hsub : Icc (0 : ℝ) ε ⊆ Icc 0 ρ := Icc_subset_Icc_right hερ
  refine ⟨ε, hε, hερ, σ, hσ, R, ?_, hRzero,
    fun q hq ↦ ⟨(hR q hq).1, (hR q hq).2.1, (hR q hq).2.2.1⟩⟩
  intro q hq
  obtain ⟨gext, W₀, hW₀, hgext, hext⟩ := DifferentialGeometry.Analysis.borel_interval_extend_param
    (fun t p ↦ h (p, t)) ρ hρ V q.1 (by simpa only [hV.interior_eq] using hKV hq.1)
    (hh.comp (contDiffOn_snd.prodMk contDiffOn_fst) (fun z hz ↦ ⟨hz.2, hz.1⟩))
  obtain ⟨W, hWW₀, hW, hqW⟩ := mem_nhds_iff.mp hW₀
  let g : E × ℝ → ℝ := fun z ↦ gext z.2 z.1
  have hg : ContDiffOn ℝ ∞ g (W ×ˢ univ) :=
    hgext.comp (contDiffOn_snd.prodMk contDiffOn_fst) (fun z hz ↦ ⟨mem_univ _, hWW₀ hz.1⟩)
  have hgo : IsOpen (W ×ˢ (univ : Set ℝ)) := hW.prod isOpen_univ
  have hgeq : ∀ p ∈ W, ∀ r ∈ Icc 0 ρ, g (p, r) = h (p, r) :=
    fun p hp r hr ↦ hext r hr p (hWW₀ hp)
  let S := (K ×ˢ Icc 0 σ) ∩ (W ×ˢ (univ : Set ℝ))
  have hgderiv : ∀ z ∈ S,
      fderiv ℝ g (z.1, R z) (0, 1) = dh (z.1, R z) := by
    intro z hz
    have hr := hsub (hR z hz.1).1
    have hg' : HasDerivAt (fun r ↦ g (z.1, r))
        (fderiv ℝ g (z.1, R z) (0, 1)) (R z) :=
      ((hg.contDiffAt (hgo.mem_nhds (show (z.1, R z) ∈ W ×ˢ univ from
        ⟨hz.2.1, mem_univ _⟩))).differentiableAt
        (by simp)).hasFDerivAt.comp_hasDerivAt (R z)
          ((hasDerivAt_const (R z) z.1).prodMk (hasDerivAt_id (R z)))
    have hg'' : HasDerivWithinAt (fun r ↦ g (z.1, r)) (dh (z.1, R z)) (Icc 0 ρ) (R z) :=
      (hderiv z.1 hz.1.1 (R z) hr).congr (hgeq z.1 hz.2.1) (hgeq z.1 hz.2.1 (R z) hr)
    exact (hg'.hasDerivWithinAt.derivWithin (uniqueDiffOn_Icc hρ _ hr)).symm.trans
      (hg''.derivWithin (uniqueDiffOn_Icc hρ _ hr))
  have hs : ContDiffOn ℝ ∞ R S := contDiffOn_inverse_of_continuousOn hg hgo
    (hc.mono inter_subset_left) (fun z hz ↦ ⟨hz.2.1, mem_univ _⟩)
    (fun z hz ↦ (hgeq z.1 hz.2.1 (R z) (hsub (hR z hz.1).1)).trans (hR z hz.1).2.1)
    (fun z hz ↦ by rw [hgderiv z hz]; exact ne_of_gt (hR z hz.1).2.2.2)
  exact (contDiffWithinAt_inter (hgo.mem_nhds ⟨hqW, mem_univ _⟩)).mp (hs q ⟨hq, hqW, mem_univ _⟩)

end DifferentialGeometry.Analysis
