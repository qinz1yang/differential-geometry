import DifferentialGeometry.Topology.Compactness.UniformBounds
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Topology.Separation.Hausdorff

noncomputable section
open Set

namespace DifferentialGeometry.Analysis

theorem exists_uniform_unique_root_of_pos_deriv
    {P : Type*} [TopologicalSpace P] {K : Set P} (hK : IsCompact K)
    {h dh : P → ℝ → ℝ} {ρ : ℝ} (hρ : 0 < ρ)
    (hd : ContinuousOn (fun z : P × ℝ ↦ dh z.1 z.2) (K ×ˢ Icc 0 ρ))
    (hderiv : ∀ p ∈ K, ∀ r ∈ Icc 0 ρ, HasDerivWithinAt (h p) (dh p r) (Icc 0 ρ) r)
    (hzero : ∀ p ∈ K, h p 0 = 0) (hpos : ∀ p ∈ K, 0 < dh p 0) :
    ∃ ε > 0, ε ≤ ρ ∧ ∃ m > 0, ∀ p ∈ K,
      StrictMonoOn (h p) (Icc 0 ε) ∧
      (∀ r ∈ Icc 0 ε, m * r ≤ h p r) ∧
      ∀ s ∈ Icc 0 (m * ε), ∃! r : ℝ, r ∈ Icc 0 ε ∧ h p r = s := by
  obtain ⟨ε, hε, hερ, m, hm, hb⟩ :=
    DifferentialGeometry.Topology.Compactness.exists_pos_uniform_lower_bound_on_Icc hK hρ hd hpos
  refine ⟨ε, hε, hερ, m, hm, ?_⟩
  intro p hp
  have hsub : Icc (0 : ℝ) ε ⊆ Icc 0 ρ := Icc_subset_Icc_right hερ
  have hc : ContinuousOn (h p) (Icc 0 ε) := by
    intro r hr
    exact (hderiv p hp r (hsub hr)).continuousWithinAt.mono hsub
  have hda : ∀ r ∈ interior (Icc (0 : ℝ) ε), HasDerivAt (h p) (dh p r) r := by
    intro r hr
    rw [interior_Icc] at hr
    exact (hderiv p hp r (hsub ⟨hr.1.le, hr.2.le⟩)).hasDerivAt
      (Icc_mem_nhds hr.1 (hr.2.trans_le hερ))
  have hd' : DifferentiableOn ℝ (h p) (interior (Icc (0 : ℝ) ε)) :=
    fun r hr ↦ (hda r hr).differentiableAt.differentiableWithinAt
  have hge : ∀ r ∈ interior (Icc (0 : ℝ) ε), m ≤ deriv (h p) r := by
    intro r hr
    rw [(hda r hr).deriv]
    exact hb p hp r (interior_subset hr)
  have hgrowth := (convex_Icc (0 : ℝ) ε).mul_sub_le_image_sub_of_le_deriv hc hd' hge
  have hmono : StrictMonoOn (h p) (Icc 0 ε) := by
    intro x hx y hy hxy
    have h := hgrowth x hx y hy hxy.le
    have hpositive : 0 < m * (y - x) := mul_pos hm (sub_pos.mpr hxy)
    linarith
  have hbound : ∀ r ∈ Icc 0 ε, m * r ≤ h p r := by
    intro r hr
    have h := hgrowth 0 ⟨le_rfl, hε.le⟩ r hr hr.1
    simpa only [hzero p hp, sub_zero] using h
  refine ⟨hmono, hbound, ?_⟩
  intro s hs
  have hs' : s ∈ Icc (h p 0) (h p ε) :=
    ⟨by simpa only [hzero p hp] using hs.1,
      hs.2.trans (hbound ε ⟨hε.le, le_rfl⟩)⟩
  obtain ⟨r, hr, hrs⟩ := intermediate_value_Icc hε.le hc hs'
  refine ⟨r, ⟨hr, hrs⟩, ?_⟩
  intro r' hr'
  exact hmono.injOn hr'.1 hr (hr'.2.trans hrs.symm)

private theorem continuousOn_inverse_of_compact
    {P : Type*} [TopologicalSpace P] [T2Space P]
    {K : Set P} {J T : Set ℝ} (hK : IsCompact K) (hJ : IsCompact J)
    {h : P × ℝ → ℝ} {R : P × ℝ → ℝ}
    (hh : ContinuousOn h (K ×ˢ J))
    (hinj : ∀ p ∈ K, InjOn (fun r ↦ h (p, r)) J)
    (hR : ∀ q ∈ K ×ˢ T, R q ∈ J ∧ h (q.1, R q) = q.2) :
    ContinuousOn R (K ×ˢ T) := by
  let D := K ×ˢ J
  let S := K ×ˢ T
  let : CompactSpace D := isCompact_iff_compactSpace.mp (hK.prod hJ)
  let F : D → P × ℝ := fun z ↦ (z.1.1, h z.1)
  have hF : Continuous F := (continuous_fst.comp continuous_subtype_val).prodMk
    hh.domRestrict
  have hFi : Function.Injective F := by
    intro z w he
    change (z.1.1, h z.1) = (w.1.1, h w.1) at he
    have hp := (Prod.mk.inj he).1
    have hr : z.1.2 = w.1.2 := by
      apply hinj z.1.1 z.2.1 z.2.2 w.2.2
      have hv : h (z.1.1, z.1.2) = h (w.1.1, w.1.2) := congrArg Prod.snd he
      rwa [← hp] at hv
    exact Subtype.ext (Prod.ext hp hr)
  let G : S → D := fun q ↦ ⟨(q.1.1, R q.1), q.2.1, (hR q.1 q.2).1⟩
  have hFG : F ∘ G = (Subtype.val : S → P × ℝ) := by
    funext q
    exact Prod.ext rfl (hR q.1 q.2).2
  have hG : Continuous G := (hF.isClosedEmbedding hFi).isEmbedding.continuous_iff.mpr
    (hFG ▸ continuous_subtype_val)
  exact continuousOn_iff_continuous_domRestrict.mpr
    (continuous_snd.comp (continuous_subtype_val.comp hG))

theorem exists_uniform_continuous_inverse_of_pos_deriv
    {P : Type*} [TopologicalSpace P] [T2Space P]
    {h dh : P × ℝ → ℝ} {K : Set P} {ρ : ℝ}
    (hK : IsCompact K) (hρ : 0 < ρ)
    (hh : ContinuousOn h (K ×ˢ Icc 0 ρ))
    (hdh : ContinuousOn dh (K ×ˢ Icc 0 ρ))
    (hderiv : ∀ p ∈ K, ∀ r ∈ Icc 0 ρ,
      HasDerivWithinAt (fun t ↦ h (p, t)) (dh (p, r)) (Icc 0 ρ) r)
    (hzero : ∀ p ∈ K, h (p, 0) = 0)
    (hpos : ∀ p ∈ K, 0 < dh (p, 0)) :
    ∃ ε > 0, ε ≤ ρ ∧ ∃ σ > 0, ∃ R : P × ℝ → ℝ,
      ContinuousOn R (K ×ˢ Icc 0 σ) ∧
      (∀ p ∈ K, R (p, 0) = 0) ∧
      ∀ q ∈ K ×ˢ Icc 0 σ,
        R q ∈ Icc 0 ε ∧ h (q.1, R q) = q.2 ∧
        (∀ r ∈ Icc 0 ε, h (q.1, r) = q.2 → r = R q) ∧
        0 < dh (q.1, R q) := by
  classical
  obtain ⟨ε₀, hε₀, hε₀ρ, m₀, hm₀, hb⟩ :=
    DifferentialGeometry.Topology.Compactness.exists_pos_uniform_lower_bound_on_Icc hK hρ hdh hpos
  have hsub₀ : Icc (0 : ℝ) ε₀ ⊆ Icc 0 ρ := Icc_subset_Icc_right hε₀ρ
  obtain ⟨ε, hε, hεε₀, m, hm, hroots⟩ := exists_uniform_unique_root_of_pos_deriv hK hε₀
    (h := fun p r ↦ h (p, r)) (dh := fun p r ↦ dh (p, r))
    (hdh.mono (prod_mono Subset.rfl hsub₀))
    (fun p hp r hr ↦ (hderiv p hp r (hsub₀ hr)).mono hsub₀)
    hzero hpos
  let S := K ×ˢ Icc 0 (m * ε)
  let R : P × ℝ → ℝ := fun q ↦ if hq : q ∈ S then
    ((hroots q.1 hq.1).2.2 q.2 hq.2).exists.choose else 0
  have hR : ∀ q ∈ S, R q ∈ Icc 0 ε ∧ h (q.1, R q) = q.2 := by
    intro q hq
    simp only [R, dif_pos hq]
    exact ((hroots q.1 hq.1).2.2 q.2 hq.2).exists.choose_spec
  have hερ : ε ≤ ρ := hεε₀.trans hε₀ρ
  have hsub : Icc (0 : ℝ) ε ⊆ Icc 0 ρ := Icc_subset_Icc_right hερ
  have hc : ContinuousOn R S := continuousOn_inverse_of_compact hK isCompact_Icc
    (hh.mono (fun _ hz ↦ ⟨hz.1, hsub hz.2⟩))
    (fun p hp ↦ (hroots p hp).1.injOn) hR
  refine ⟨ε, hε, hερ, m * ε, mul_pos hm hε, R, hc, ?_, ?_⟩
  · intro p hp
    have hpS : (p, 0) ∈ S := ⟨hp, le_rfl, (mul_pos hm hε).le⟩
    exact ((hroots p hp).2.2 0 hpS.2).unique (hR (p, 0) hpS)
      ⟨⟨le_rfl, hε.le⟩, hzero p hp⟩
  · intro q hq
    refine ⟨(hR q hq).1, (hR q hq).2, ?_, ?_⟩
    · intro r hr heq
      exact ((hroots q.1 hq.1).2.2 q.2 hq.2).unique ⟨hr, heq⟩ (hR q hq)
    · exact hm₀.trans_le (hb q.1 hq.1 (R q) (Icc_subset_Icc_right hεε₀ (hR q hq).1))

end DifferentialGeometry.Analysis
