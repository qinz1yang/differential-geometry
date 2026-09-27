/-
Copyright (c) 2026 Yuan Liao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuan Liao
-/
import DifferentialGeometry.Analysis.ODE.Flow.IntegralCurveTransport
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace

open Set Filter Function
open scoped ContDiff Manifold Topology
open DifferentialGeometry.Analysis.ODE

namespace DifferentialGeometry.Morse

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]
  {I : ModelWithCorners ℝ E H}

def IsDescendingConnection (I : ModelWithCorners ℝ E H) (f : M → ℝ)
    (v : (x : M) → TangentSpace I x) (p q : M) (γ : ℝ → M) : Prop :=
  IsMIntegralCurve γ v ∧ Tendsto γ atBot (𝓝 p) ∧ Tendsto γ atTop (𝓝 q) ∧
    ∀ t, mvfderiv I f (γ t) (v (γ t)) < 0

def connectingLocus (I : ModelWithCorners ℝ E H) (f : M → ℝ)
    (v : (x : M) → TangentSpace I x) (p q : M) : Set M :=
  {x | ∃ γ, IsDescendingConnection I f v p q γ ∧ x ∈ range γ}

theorem IsDescendingConnection.strictAnti {f : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) {v : (x : M) → TangentSpace I x}
    {p q : M} {γ : ℝ → M} (hγ : IsDescendingConnection I f v p q γ) :
    StrictAnti (f ∘ γ) := by
  apply strictAnti_of_deriv_neg
  intro t
  rw [(hasDerivAt_df_comp_integralCurve f hf v hγ.1 t).deriv]
  exact hγ.2.2.2 t

theorem IsDescendingConnection.value_mem_Ioo {f : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) {v : (x : M) → TangentSpace I x}
    {p q : M} {γ : ℝ → M} (hγ : IsDescendingConnection I f v p q γ) (t : ℝ) :
    f (γ t) ∈ Ioo (f q) (f p) := by
  have ha := hγ.strictAnti hf
  have hupper (s : ℝ) : f (γ s) ≤ f p := by
    apply ge_of_tendsto ((hf.continuous.tendsto p).comp hγ.2.1)
    exact eventually_atBot.mpr ⟨s, fun u hu => ha.antitone hu⟩
  have hlower (s : ℝ) : f q ≤ f (γ s) := by
    apply le_of_tendsto ((hf.continuous.tendsto q).comp hγ.2.2.1)
    exact eventually_atTop.mpr ⟨s, fun u hu => ha.antitone hu⟩
  exact ⟨(hlower (t + 1)).trans_lt (ha (by linarith)),
    (ha (by linarith : t - 1 < t)).trans_le (hupper (t - 1))⟩

theorem IsDescendingConnection.existsUnique_level_time {f : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) {v : (x : M) → TangentSpace I x}
    {p q : M} {γ : ℝ → M} (hγ : IsDescendingConnection I f v p q γ)
    {c : ℝ} (hc : c ∈ Ioo (f q) (f p)) : ∃! t, f (γ t) = c := by
  have hcont : Continuous (f ∘ γ) :=
    continuous_iff_continuousAt.mpr fun t =>
      (hasDerivAt_df_comp_integralCurve f hf v hγ.1 t).continuousAt
  have hlow : ∀ᶠ t in atTop, f (γ t) ≤ c := by
    filter_upwards [((hf.continuous.tendsto q).comp hγ.2.2.1).eventually
      (gt_mem_nhds hc.1)] with t ht
    exact ht.le
  have hhigh : ∀ᶠ t in atBot, c ≤ f (γ t) := by
    filter_upwards [((hf.continuous.tendsto p).comp hγ.2.1).eventually
      (lt_mem_nhds hc.2)] with t ht
    exact ht.le
  obtain ⟨t, ht⟩ := intermediate_value_univ₂_eventually₂ hcont continuous_const hlow hhigh
  exact ⟨t, ht, fun s hs => (hγ.strictAnti hf).injective (hs.trans ht.symm)⟩

theorem IsDescendingConnection.connectingLocus_inter_level {f : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) {v : (x : M) → TangentSpace I x}
    {p q : M} {γ : ℝ → M} (hγ : IsDescendingConnection I f v p q γ)
    (hunique : ∀ η, IsDescendingConnection I f v p q η → ∃ d : ℝ, η = γ ∘ (· + d))
    (t : ℝ) : connectingLocus I f v p q ∩ f ⁻¹' {f (γ t)} = {γ t} := by
  ext x
  constructor
  · rintro ⟨⟨η, hη, s, rfl⟩, hs⟩
    obtain ⟨d, rfl⟩ := hunique η hη
    have he : s + d = t := (hγ.strictAnti hf).injective hs
    simp only [mem_singleton_iff, comp_apply, he]
  · rintro rfl
    exact ⟨⟨γ, hγ, t, rfl⟩, rfl⟩

variable [IsManifold I ∞ M] [BoundarylessManifold I M] [T2Space M]

theorem exists_time_translate_of_integralCurve_meet
    {v : (x : M) → TangentSpace I x}
    (hv : ContMDiff I I.tangent 1 (fun x => (v x : TangentBundle I M)))
    {γ η : ℝ → M} (hγ : IsMIntegralCurve γ v) (hη : IsMIntegralCurve η v)
    {s t : ℝ} (h : γ s = η t) : ∃ d : ℝ, η = γ ∘ (· + d) := by
  refine ⟨s - t, ?_⟩
  apply integralCurve_eq_of_agree v hv hη (hγ.comp_add (s - t)) (t₀ := t)
  simpa only [comp_apply, show t + (s - t) = s by ring] using h.symm

theorem unique_descendingConnection_iff_singleton_section {f : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) {v : (x : M) → TangentSpace I x}
    (hv : ContMDiff I I.tangent 1 (fun x => (v x : TangentBundle I M)))
    {p q : M} {γ : ℝ → M} (hγ : IsDescendingConnection I f v p q γ)
    {c : ℝ} (hc : c ∈ Ioo (f q) (f p)) :
    (∀ η, IsDescendingConnection I f v p q η → ∃ d : ℝ, η = γ ∘ (· + d)) ↔
      ∃ x : M, connectingLocus I f v p q ∩ f ⁻¹' {c} = {x} := by
  obtain ⟨s, hs, _⟩ := hγ.existsUnique_level_time hf hc
  constructor
  · intro hu
    refine ⟨γ s, ?_⟩
    simpa only [hs] using hγ.connectingLocus_inter_level hf hu s
  · rintro ⟨x, hx⟩ η hη
    obtain ⟨t, ht, _⟩ := hη.existsUnique_level_time hf hc
    have hgs : γ s = x := by
      have hm : γ s ∈ connectingLocus I f v p q ∩ f ⁻¹' {c} := ⟨⟨γ, hγ, s, rfl⟩, hs⟩
      rw [hx] at hm
      exact hm
    have het : η t = x := by
      have hm : η t ∈ connectingLocus I f v p q ∩ f ⁻¹' {c} := ⟨⟨η, hη, t, rfl⟩, ht⟩
      rw [hx] at hm
      exact hm
    exact exists_time_translate_of_integralCurve_meet hv hγ.1 hη.1 (hgs.trans het.symm)

end DifferentialGeometry.Morse
