/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.SingularNormalForm

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

omit [NormedSpace ℝ E] in
theorem mem_nhdsWithin_of_subset_of_inter {P P' P'' A : Set E} {a : E}
    (hA : A ∈ 𝓝[P] a) (hsub' : P'' ⊆ P') {V : Set E} (hV : V ∈ 𝓝 a)
    (hVsub : P' ∩ V ⊆ P) : A ∈ 𝓝[P''] a := by
  obtain ⟨V₁, hV₁, hV₁sub⟩ := mem_nhdsWithin_iff_exists_mem_nhds_inter.mp hA
  refine mem_nhdsWithin_iff_exists_mem_nhds_inter.mpr ⟨V ∩ V₁, Filter.inter_mem hV hV₁, ?_⟩
  rintro x ⟨⟨hxV, hxV₁⟩, hxP''⟩
  exact hV₁sub ⟨hxV₁, hVsub ⟨hsub' hxP'', hxV⟩⟩

theorem HasPLDoubleCrossingAt.mono_of_subset {f : E → F} {P P' P'' : Set E} {y : F}
    (hD : HasPLDoubleCrossingAt f P y) (hsub : P ⊆ P'') (hsub' : P'' ⊆ P')
    (hloc : ∀ a ∈ P, f a = y → ∃ V ∈ 𝓝 a, P' ∩ V ⊆ P)
    (hcover : ∀ᶠ z in 𝓝 y, P' ∩ f ⁻¹' {z} ⊆ P) :
    HasPLDoubleCrossingAt f P'' y := by
  obtain ⟨a, b, A, B, ha, hb, hfa, hfb, hAP, hBP, hdis, hA, hB, hfA, hfB, hcross, hcov⟩ := hD
  obtain ⟨V, hV, hVsub⟩ := hloc a (hAP ha) hfa
  obtain ⟨V', hV', hV'sub⟩ := hloc b (hBP hb) hfb
  refine ⟨a, b, A, B, ha, hb, hfa, hfb, hAP.trans hsub, hBP.trans hsub, hdis,
    mem_nhdsWithin_of_subset_of_inter hA hsub' hV hVsub,
    mem_nhdsWithin_of_subset_of_inter hB hsub' hV' hV'sub, hfA, hfB, hcross, ?_⟩
  filter_upwards [hcov, hcover] with z hz hz' x hx
  exact hz ⟨hz' ⟨hsub' hx.1, hx.2⟩, hx.2⟩

theorem HasPLBoundaryDoubleCrossingAt.mono_of_subset {f : E → F} {P P' P'' : Set E}
    {Mb : Set F} {y : F} (hD : HasPLBoundaryDoubleCrossingAt f P Mb y)
    (hsub : P ⊆ P'') (hsub' : P'' ⊆ P')
    (hloc : ∀ a ∈ P, f a = y → ∃ V ∈ 𝓝 a, P' ∩ V ⊆ P)
    (hcover : ∀ᶠ z in 𝓝 y, P' ∩ f ⁻¹' {z} ⊆ P) :
    HasPLBoundaryDoubleCrossingAt f P'' Mb y := by
  obtain ⟨a, b, A, B, ha, hb, hfa, hfb, hAP, hBP, hdis, hA, hB, hfA, hfB, hcross, hcov⟩ := hD
  obtain ⟨V, hV, hVsub⟩ := hloc a (hAP ha) hfa
  obtain ⟨V', hV', hV'sub⟩ := hloc b (hBP hb) hfb
  refine ⟨a, b, A, B, ha, hb, hfa, hfb, hAP.trans hsub, hBP.trans hsub, hdis,
    mem_nhdsWithin_of_subset_of_inter hA hsub' hV hVsub,
    mem_nhdsWithin_of_subset_of_inter hB hsub' hV' hV'sub, hfA, hfB, hcross, ?_⟩
  filter_upwards [hcov, hcover] with z hz hz' x hx
  exact hz ⟨hz' ⟨hsub' hx.1, hx.2⟩, hx.2⟩

theorem HasPLNormalDoubleCrossingAt.mono_of_subset {f : E → F} {P P' P'' : Set E}
    {Bd : Set F} {y : F} (hD : HasPLNormalDoubleCrossingAt f P Bd y)
    (hsub : P ⊆ P'') (hsub' : P'' ⊆ P')
    (hloc : ∀ a ∈ P, f a = y → ∃ V ∈ 𝓝 a, P' ∩ V ⊆ P)
    (hcover : ∀ᶠ z in 𝓝 y, P' ∩ f ⁻¹' {z} ⊆ P) :
    HasPLNormalDoubleCrossingAt f P'' Bd y := by
  rcases hD with ⟨hyB, Mb, hcross⟩ | ⟨hyB, hcross⟩
  · exact Or.inl ⟨hyB, Mb, hcross.mono_of_subset hsub hsub' hloc hcover⟩
  · exact Or.inr ⟨hyB, hcross.mono_of_subset hsub hsub' hloc hcover⟩

theorem HasPLDoubleCrossingAt.congr_source {f g : E → F} {P : Set E} {y : F}
    (hD : HasPLDoubleCrossingAt f P y) (hfg : EqOn f g P) :
    HasPLDoubleCrossingAt g P y := by
  obtain ⟨a, b, A, B, ha, hb, hfa, hfb, hAP, hBP, hdis, hA, hB, hfA, hfB, hcross, hcov⟩ := hD
  have himgA : g '' A = f '' A := Set.image_congr fun x hx => (hfg (hAP hx)).symm
  have himgB : g '' B = f '' B := Set.image_congr fun x hx => (hfg (hBP hx)).symm
  refine ⟨a, b, A, B, ha, hb, ?_, ?_, hAP, hBP, hdis, hA, hB, ?_, ?_, ?_, ?_⟩
  · rw [← hfg (hAP ha)]; exact hfa
  · rw [← hfg (hBP hb)]; exact hfb
  · rw [himgA]; exact hfA.congr fun x hx => (hfg (hAP hx)).symm
  · rw [himgB]; exact hfB.congr fun x hx => (hfg (hBP hx)).symm
  · rw [himgA, himgB]; exact hcross
  · filter_upwards [hcov] with z hz x hx
    exact hz ⟨hx.1, by rw [mem_preimage, hfg hx.1]; exact hx.2⟩

theorem HasPLBoundaryDoubleCrossingAt.congr_source {f g : E → F} {P : Set E}
    {Mb : Set F} {y : F} (hD : HasPLBoundaryDoubleCrossingAt f P Mb y) (hfg : EqOn f g P) :
    HasPLBoundaryDoubleCrossingAt g P Mb y := by
  obtain ⟨a, b, A, B, ha, hb, hfa, hfb, hAP, hBP, hdis, hA, hB, hfA, hfB, hcross, hcov⟩ := hD
  have himgA : g '' A = f '' A := Set.image_congr fun x hx => (hfg (hAP hx)).symm
  have himgB : g '' B = f '' B := Set.image_congr fun x hx => (hfg (hBP hx)).symm
  refine ⟨a, b, A, B, ha, hb, ?_, ?_, hAP, hBP, hdis, hA, hB, ?_, ?_, ?_, ?_⟩
  · rw [← hfg (hAP ha)]; exact hfa
  · rw [← hfg (hBP hb)]; exact hfb
  · rw [himgA]; exact hfA.congr fun x hx => (hfg (hAP hx)).symm
  · rw [himgB]; exact hfB.congr fun x hx => (hfg (hBP hx)).symm
  · rw [himgA, himgB]; exact hcross
  · filter_upwards [hcov] with z hz x hx
    exact hz ⟨hx.1, by rw [mem_preimage, hfg hx.1]; exact hx.2⟩

theorem HasPLNormalDoubleCrossingAt.congr_source {f g : E → F} {P : Set E}
    {Bd : Set F} {y : F} (hD : HasPLNormalDoubleCrossingAt f P Bd y) (hfg : EqOn f g P) :
    HasPLNormalDoubleCrossingAt g P Bd y := by
  rcases hD with ⟨hyB, Mb, hcross⟩ | ⟨hyB, hcross⟩
  · exact Or.inl ⟨hyB, Mb, hcross.congr_source hfg⟩
  · exact Or.inr ⟨hyB, hcross.congr_source hfg⟩

end DifferentialGeometry.Topology.PiecewiseLinear
