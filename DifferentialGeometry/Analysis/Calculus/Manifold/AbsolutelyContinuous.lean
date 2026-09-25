import Mathlib.MeasureTheory.Function.AbsolutelyContinuous
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv
import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import Mathlib.Topology.Compactness.Lindelof

set_option autoImplicit false

open Filter Function MeasureTheory Set
open scoped Manifold Topology Interval

namespace AbsolutelyContinuousOnInterval

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]

theorem ae_mdifferentiableAt_of_extChartAt
    {a b : ℝ} {gamma : ℝ → M} (p : M)
    (hAC : AbsolutelyContinuousOnInterval ((extChartAt I p) ∘ gamma) a b)
    (hsrc : MapsTo gamma (uIcc a b) (chartAt H p).source) :
    ∀ᵐ r ∂volume.restrict (uIcc a b), MDifferentiableAt 𝓘(ℝ, ℝ) I gamma r := by
  have hmaps : MapsTo ((extChartAt I p) ∘ gamma) (uIcc a b)
      (extChartAt I p).target := by
    intro r hr
    exact (extChartAt I p).map_source (by
      simpa only [extChartAt_source] using hsrc hr)
  have hcont : ContinuousOn gamma (uIcc a b) := by
    have h := (continuousOn_extChartAt_symm p).comp hAC.continuousOn hmaps
    refine h.congr ?_
    intro r hr
    exact ((extChartAt I p).left_inv (by
      simpa only [extChartAt_source] using hsrc hr)).symm
  have hmem : ∀ᵐ r ∂volume.restrict (uIcc a b), r ∈ Ioo (min a b) (max a b) := by
    rw [uIcc, ← restrict_Ioo_eq_restrict_Icc]
    exact ae_restrict_mem measurableSet_Ioo
  have hdiff : ∀ᵐ r ∂volume.restrict (uIcc a b),
      r ∈ uIcc a b → DifferentiableAt ℝ ((extChartAt I p) ∘ gamma) r :=
    ae_mono Measure.restrict_le_self
      hAC.boundedVariationOn.ae_differentiableAt_of_mem_uIcc
  filter_upwards [hdiff, hmem] with r hr hri
  have hcc : r ∈ uIcc a b := ⟨hri.1.le, hri.2.le⟩
  apply (mdifferentiableAt_iff_target_of_mem_source (hsrc hcc)).mpr
  refine ⟨(hcont r hcc).continuousAt (Icc_mem_nhds hri.1 hri.2), ?_⟩
  exact mdifferentiableAt_iff_differentiableAt.mpr (hr hcc)

end AbsolutelyContinuousOnInterval

namespace Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

def absolutelyContinuousOnInterval (gamma : ℝ → M) (a b : ℝ) : Prop :=
  ContinuousOn gamma (uIcc a b) ∧
    ∀ (p : M) (c d : ℝ), uIcc c d ⊆ uIcc a b →
      MapsTo gamma (uIcc c d) (chartAt H p).source →
      AbsolutelyContinuousOnInterval ((extChartAt I p) ∘ gamma) c d

variable {I} {gamma : ℝ → M} {a b c d : ℝ}

theorem absolutelyContinuousOnInterval_continuousOn
    (h : absolutelyContinuousOnInterval I gamma a b) :
    ContinuousOn gamma (uIcc a b) := h.1

theorem absolutelyContinuousOnInterval_mono
    (h : absolutelyContinuousOnInterval I gamma a b) (hsub : uIcc c d ⊆ uIcc a b) :
    absolutelyContinuousOnInterval I gamma c d :=
  ⟨h.1.mono hsub, fun p e f hef hmaps => h.2 p e f (hef.trans hsub) hmaps⟩

theorem absolutelyContinuousOnInterval_symm
    (h : absolutelyContinuousOnInterval I gamma a b) :
    absolutelyContinuousOnInterval I gamma b a := by
  simpa only [absolutelyContinuousOnInterval, uIcc_comm] using h

variable [IsManifold I 1 M]

theorem absolutelyContinuousOnInterval_of_contMDiffOn
    (h : ContMDiffOn 𝓘(ℝ, ℝ) I 1 gamma (uIcc a b)) :
    absolutelyContinuousOnInterval I gamma a b := by
  refine ⟨h.continuousOn, fun p c d hsub hmaps => ?_⟩
  exact ((contMDiffOn_extChartAt (I := I) (x := p) (n := 1)).comp
    (h.mono hsub) hmaps).contDiffOn.absolutelyContinuousOnInterval

variable [FiniteDimensional ℝ E]

theorem absolutelyContinuousOnInterval_ae_mdifferentiableAt
    (h : absolutelyContinuousOnInterval I gamma a b) :
    ∀ᵐ t ∂volume.restrict (uIcc a b), MDifferentiableAt 𝓘(ℝ, ℝ) I gamma t := by
  have hlocal : ∀ t ∈ Ioo (min a b) (max a b), ∃ c d : ℝ,
      Icc c d ∈ 𝓝 t ∧
      ∀ᵐ r ∂volume.restrict (Icc c d), MDifferentiableAt 𝓘(ℝ, ℝ) I gamma r := by
    intro t ht
    have htcc : t ∈ uIcc a b := ⟨ht.1.le, ht.2.le⟩
    have hcont := (h.1 t htcc).continuousAt (Icc_mem_nhds ht.1 ht.2)
    have hsrc : gamma ⁻¹' (chartAt H (gamma t)).source ∈ 𝓝 t :=
      hcont.preimage_mem_nhds ((chartAt H (gamma t)).open_source.mem_nhds (mem_chart_source H (gamma t)))
    obtain ⟨c, d, htcd, hnhds, hsub⟩ := exists_Icc_mem_subset_of_mem_nhds
      (inter_mem (Icc_mem_nhds ht.1 ht.2) hsrc)
    have hcd : c ≤ d := htcd.1.trans htcd.2
    have hmaps : MapsTo gamma (uIcc c d) (chartAt H (gamma t)).source := by
      rw [uIcc_of_le hcd]
      exact fun r hr => (hsub hr).2
    have hac := h.2 (gamma t) c d (by
      rw [uIcc_of_le hcd]
      exact fun r hr => (hsub hr).1) hmaps
    refine ⟨c, d, hnhds, ?_⟩
    simpa only [uIcc_of_le hcd] using hac.ae_mdifferentiableAt_of_extChartAt (gamma t) hmaps
  choose c d hnhds hae using hlocal
  obtain ⟨s, hs, hcover⟩ := (isLindelof_iff_lindelofSpace.mpr
    (inferInstance : LindelofSpace (Ioo (min a b) (max a b)))).elim_nhds_subcover'
      (fun t ht => Icc (c t ht) (d t ht)) hnhds
  have hunion : ∀ᵐ r ∂volume.restrict
      (⋃ t ∈ s, Icc (c t t.2) (d t t.2)), MDifferentiableAt 𝓘(ℝ, ℝ) I gamma r :=
    (ae_restrict_biUnion_iff _ hs _).mpr (fun t _ => hae t t.2)
  have hinner := ae_mono (Measure.restrict_mono_set volume hcover) hunion
  rw [uIcc, ← restrict_Ioo_eq_restrict_Icc]
  exact hinner

end Manifold
