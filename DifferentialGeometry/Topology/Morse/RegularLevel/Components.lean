import DifferentialGeometry.Topology.Morse.RegularLevel.NoCriticalValues
import Mathlib.Topology.Homeomorph.Lemmas

open Set Manifold
open scoped Manifold ContDiff
open DifferentialGeometry.Analysis.ODE

namespace DifferentialGeometry.Topology.Morse

theorem exists_diffeomorph_superlevel_components_of_no_critical_values
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]
    {I : ModelWithCorners ℝ E H} [I.Boundaryless] [IsManifold I ∞ M]
    [T2Space M] [SigmaCompactSpace M]
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) {a b : ℝ} (hab : a ≤ b)
    (hcompact : IsCompact (f ⁻¹' Icc a b))
    (hregular : ∀ x ∈ f ⁻¹' Icc a b, ¬ IsCriticalPointAt I f x) :
    ∃ Φ : Diffeomorph I I M M ∞,
      Φ '' {x | a ≤ f x} = {x | b ≤ f x} ∧
      Φ '' {x | a < f x} = {x | b < f x} ∧
      (∀ x, b ≤ f x → Φ '' connectedComponentIn {y | a ≤ f y} x =
        connectedComponentIn {y | b ≤ f y} x) ∧
      ∀ x, b < f x → Φ '' connectedComponentIn {y | a < f y} x =
        connectedComponentIn {y | b < f y} x := by
  obtain ⟨v, Φ, _, _, _, hrate, ⟨hcomplete, hsub, hflow⟩, _, hstrict, _, hstrict'⟩ :=
    no_critical_value_transport f hf hab hcompact hregular
  have hclosed : Φ '' {x | a ≤ f x} = {x | b ≤ f x} := by
    apply Subset.antisymm
    · rintro _ ⟨x, hx, rfl⟩
      change b ≤ f (Φ x)
      by_contra h
      have hh := hstrict' (Φ x) (lt_of_not_ge h)
      rw [Φ.symm_apply_apply] at hh
      exact (not_lt_of_ge hx) hh
    · intro y hy
      refine ⟨Φ.symm y, ?_, Φ.apply_symm_apply y⟩
      change a ≤ f (Φ.symm y)
      by_contra h
      have hh := hstrict (Φ.symm y) (lt_of_not_ge h)
      rw [Φ.apply_symm_apply] at hh
      exact (not_lt_of_ge hy) hh
  have hopen : Φ '' {x | a < f x} = {x | b < f x} := by
    have h := Φ.toEquiv.image_compl (sublevel f a)
    rw [hsub] at h
    have hcompl (t : ℝ) : (sublevel f t)ᶜ = {x | t < f x} := by
      ext x
      change ¬ f x ≤ t ↔ t < f x
      exact not_le
    change Φ.toEquiv '' {x | a < f x} = {x | b < f x}
    simpa only [hcompl] using h
  have hbound (x : M) (t : ℝ) (ht : 0 ≤ t) :
      f x ≤ f (curveAt v hcomplete x (-t)) := by
    simpa only [curveAt_zero] using
      (f_rate_bounds_of_integralCurve_back f hf v hrate (curveAt_integralCurve v hcomplete x) ht).1
  have hpath (x : M) {S : Set M}
      (hS : ∀ t ∈ Icc (0 : ℝ) (b - a), curveAt v hcomplete x (-t) ∈ S) :
      Φ x ∈ connectedComponentIn S x := by
    have hc : IsPreconnected ((fun t => curveAt v hcomplete x (-t)) '' Icc (0 : ℝ) (b - a)) :=
      isPreconnected_Icc.image _ ((curveAt_integralCurve v hcomplete x).continuous.comp
        continuous_neg).continuousOn
    have hx : x ∈ (fun t => curveAt v hcomplete x (-t)) '' Icc (0 : ℝ) (b - a) :=
      ⟨0, ⟨le_rfl, sub_nonneg.mpr hab⟩, by simp only [neg_zero, curveAt_zero]⟩
    apply hc.subset_connectedComponentIn hx (by rintro _ ⟨t, ht, rfl⟩; exact hS t ht)
    refine ⟨b - a, ⟨sub_nonneg.mpr hab, le_rfl⟩, ?_⟩
    change curveAt v hcomplete x (-(b - a)) = Φ.toEquiv x
    rw [hflow x, neg_sub]
  refine ⟨Φ, hclosed, hopen, ?_, ?_⟩
  · intro x hx
    have hm : Φ x ∈ connectedComponentIn {y | b ≤ f y} x :=
      hpath x (fun t ht => hx.trans (hbound x t ht.1))
    have h := Φ.toHomeomorph.image_connectedComponentIn (show x ∈ {y | a ≤ f y} from hab.trans hx)
    change Φ '' connectedComponentIn {y | a ≤ f y} x =
      connectedComponentIn (Φ '' {y | a ≤ f y}) (Φ x) at h
    rw [hclosed] at h
    exact h.trans (connectedComponentIn_eq hm).symm
  · intro x hx
    have hm : Φ x ∈ connectedComponentIn {y | b < f y} x :=
      hpath x (fun t ht => hx.trans_le (hbound x t ht.1))
    have h := Φ.toHomeomorph.image_connectedComponentIn
      (show x ∈ {y | a < f y} from hab.trans_lt hx)
    change Φ '' connectedComponentIn {y | a < f y} x =
      connectedComponentIn (Φ '' {y | a < f y}) (Φ x) at h
    rw [hopen] at h
    exact h.trans (connectedComponentIn_eq hm).symm

theorem connectedComponentIn_superlevel_inter_eq_of_no_critical_values
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]
    {I : ModelWithCorners ℝ E H} [I.Boundaryless] [IsManifold I ∞ M]
    [T2Space M] [SigmaCompactSpace M]
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) {a b : ℝ} (hab : a ≤ b)
    (hcompact : IsCompact (f ⁻¹' Icc a b))
    (hregular : ∀ x ∈ f ⁻¹' Icc a b, ¬ IsCriticalPointAt I f x)
    {p : M} (hp : b ≤ f p) :
    connectedComponentIn {x | a ≤ f x} p ∩ {x | b ≤ f x} =
      connectedComponentIn {x | b ≤ f x} p := by
  obtain ⟨Φ, _, _, hcomponents, _⟩ :=
    exists_diffeomorph_superlevel_components_of_no_critical_values hf hab hcompact hregular
  apply Subset.antisymm
  · rintro x ⟨hx, hxb⟩
    have heq : connectedComponentIn {x | b ≤ f x} p =
        connectedComponentIn {y | b ≤ f y} x := by
      rw [← hcomponents p hp, ← hcomponents x hxb, connectedComponentIn_eq hx]
    rw [heq]
    exact mem_connectedComponentIn hxb
  · intro x hx
    exact ⟨connectedComponentIn_mono p (fun y hy => hab.trans (show b ≤ f y from hy)) hx,
      connectedComponentIn_subset _ _ hx⟩

end DifferentialGeometry.Topology.Morse
