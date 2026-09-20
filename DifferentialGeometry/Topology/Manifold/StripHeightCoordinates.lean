/-
Copyright (c) 2026 Yuan Liao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuan Liao
-/
import DifferentialGeometry.Analysis.Calculus.Inverse.ParameterizedInverse
import DifferentialGeometry.Topology.Manifold.CompactLocalDiffeomorph
import DifferentialGeometry.Topology.Manifold.PartialDiffeomorph
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Topology.Order.IntermediateValue

/-! Height coordinates on a compact strip with strictly decreasing vertical fibers. -/

open Set Function
open scoped ContDiff Manifold Topology

namespace DifferentialGeometry.Topology.Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

theorem exists_height_coordinates_on_compact_strip
    {h : E × ℝ → ℝ} {U : Set (E × ℝ)} (hU : IsOpen U)
    (hh : ContDiffOn ℝ ∞ h U) {K : Set E} (hK : IsCompact K)
    {a b : ℝ} (hab : a ≤ b) (hKU : K ×ˢ Icc a b ⊆ U)
    (hvertical : ∀ s ∈ K, ∀ t ∈ Icc a b, fderiv ℝ h (s, t) (0, 1) < 0) :
    ∃ e : PartialDiffeomorph 𝓘(ℝ, E × ℝ) 𝓘(ℝ, E × ℝ) (E × ℝ) (E × ℝ) ∞,
      K ×ˢ Icc a b ⊆ e.source ∧ e.source ⊆ U ∧
      (∀ z, e z = (z.1, h z)) ∧
      (∀ z ∈ e.target, (e.symm z).1 = z.1 ∧ h (e.symm z) = z.2) ∧
      e '' (K ×ˢ Icc a b) = {z | z.1 ∈ K ∧ z.2 ∈ Icc (h (z.1, b)) (h (z.1, a))} := by
  have hder (s : E) (hs : s ∈ K) (t : ℝ) (ht : t ∈ Icc a b) :
      HasDerivAt (fun u => h (s, u)) (fderiv ℝ h (s, t) (0, 1)) t := by
    have hp : (s, t) ∈ U := hKU ⟨hs, ht⟩
    have hd := (hh.contDiffAt (hU.mem_nhds hp)).differentiableAt (by simp)
    exact hd.hasFDerivAt.comp_hasDerivAt t
      ((hasDerivAt_const t s).prodMk (hasDerivAt_id t))
  have hc (s : E) (hs : s ∈ K) : ContinuousOn (fun t => h (s, t)) (Icc a b) :=
    hh.continuousOn.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun _ ht => hKU ⟨hs, ht⟩)
  have hanti (s : E) (hs : s ∈ K) : StrictAntiOn (fun t => h (s, t)) (Icc a b) := by
    apply strictAntiOn_of_deriv_neg (convex_Icc a b) (hc s hs)
    intro t ht
    rw [(hder s hs t (interior_subset ht)).deriv]
    exact hvertical s hs t (interior_subset ht)
  have hinj : InjOn (fun z : E × ℝ => (z.1, h z)) (K ×ˢ Icc a b) := by
    rintro ⟨s, t⟩ ⟨hs, ht⟩ ⟨u, v⟩ ⟨hu, hv⟩ he
    have hsu : s = u := congrArg Prod.fst he
    subst u
    exact Prod.ext rfl ((hanti s hs).injOn ht hv (congrArg Prod.snd he))
  have hloc (z : E × ℝ) (hz : z ∈ K ×ˢ Icc a b) :
      IsLocalDiffeomorphAt 𝓘(ℝ, E × ℝ) 𝓘(ℝ, E × ℝ) ∞ (fun z => (z.1, h z)) z := by
    obtain ⟨d, hzd, _, hd, hdi, hde, _⟩ :=
      DifferentialGeometry.Analysis.exists_localInverse_preserving_parameter hh hU (hKU hz)
        (ne_of_lt (hvertical z.1 hz.1 z.2 hz.2))
    let d' : PartialDiffeomorph 𝓘(ℝ, E × ℝ) 𝓘(ℝ, E × ℝ) (E × ℝ) (E × ℝ) ∞ :=
      { toPartialEquiv := d.toPartialEquiv
        open_source := d.open_source
        open_target := d.open_target
        contMDiffOn_toFun := hd.contMDiffOn
        contMDiffOn_invFun := hdi.contMDiffOn }
    exact ⟨d', hzd, fun y _ => (hde y).symm⟩
  obtain ⟨d, hds, _, hde⟩ := exists_partialDiffeomorph_of_injOn_compact
    (hK.prod isCompact_Icc) hinj hloc isOpen_univ (subset_univ _)
  let e := DifferentialGeometry.Topology.PartialDiffeomorph.restrict d U hU
  have he (z : E × ℝ) : e z = (z.1, h z) := congrFun hde z
  have himage (s : E) (hs : s ∈ K) :
      (fun t => h (s, t)) '' Icc a b = Icc (h (s, b)) (h (s, a)) :=
    (hc s hs).image_Icc_of_antitoneOn hab (hanti s hs).antitoneOn
  refine ⟨e, fun z hz => ⟨hds hz, hKU hz⟩, fun _ hz => hz.2, he, ?_, ?_⟩
  · intro z hz
    have hr : e (e.symm z) = z := e.right_inv hz
    rw [he] at hr
    exact Prod.mk.inj hr
  · ext z
    constructor
    · rintro ⟨⟨s, t⟩, ⟨hs, ht⟩, heq⟩
      rw [he] at heq
      subst z
      exact ⟨hs, himage s hs ▸ mem_image_of_mem (fun t => h (s, t)) ht⟩
    · intro hz
      obtain ⟨t, ht, heq⟩ := (himage z.1 hz.1).symm ▸ hz.2
      refine ⟨(z.1, t), ⟨hz.1, ht⟩, ?_⟩
      rw [he]
      exact Prod.ext rfl heq

variable {F H M : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]
  {I : ModelWithCorners ℝ F H}

theorem exists_height_chart_of_compact_strip
    (d : PartialDiffeomorph (𝓘(ℝ, E).prod 𝓘(ℝ, ℝ)) I (E × ℝ) M ∞)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) {K : Set E} (hK : IsCompact K)
    {a b : ℝ} (hab : a ≤ b) (hKs : K ×ˢ Icc a b ⊆ d.source)
    (hnegative : ∀ s ∈ K, ∀ t ∈ Icc a b, deriv (fun u => f (d (s, u))) t < 0) :
    ∃ c : PartialDiffeomorph I 𝓘(ℝ, E × ℝ) M (E × ℝ) ∞,
      d '' (K ×ˢ Icc a b) ⊆ c.source ∧ c.source ⊆ d.target ∧
      (∀ x ∈ c.source, c x = ((d.symm x).1, f x)) ∧
      (∀ z ∈ c.target, (d.symm (c.symm z)).1 = z.1 ∧ f (c.symm z) = z.2) ∧
      (∀ z ∈ K ×ˢ Icc a b, c (d z) = (z.1, f (d z))) ∧
      c '' (d '' (K ×ˢ Icc a b)) =
        {z | z.1 ∈ K ∧ z.2 ∈ Icc (f (d (z.1, b))) (f (d (z.1, a)))} := by
  let P : Diffeomorph 𝓘(ℝ, E × ℝ) (𝓘(ℝ, E).prod 𝓘(ℝ, ℝ)) (E × ℝ) (E × ℝ) ∞ :=
    { toEquiv := Equiv.refl _
      contMDiff_toFun := contDiff_fst.contMDiff.prodMk contDiff_snd.contMDiff
      contMDiff_invFun := contMDiff_fst.prodMk_space contMDiff_snd }
  let g : E × ℝ → ℝ := fun z => f (d z)
  have hg : ContDiffOn ℝ ∞ g d.source :=
    ((hf.comp_contMDiffOn d.contMDiffOn).comp P.contMDiff.contMDiffOn
      (fun _ hz => hz)).contDiffOn
  have hvertical (s : E) (hs : s ∈ K) (t : ℝ) (ht : t ∈ Icc a b) :
      fderiv ℝ g (s, t) (0, 1) < 0 := by
    have hst : (s, t) ∈ d.source := hKs ⟨hs, ht⟩
    have hd := (hg.contDiffAt (d.open_source.mem_nhds hst)).differentiableAt (by simp)
    have hder : HasDerivAt (fun u => g (s, u)) (fderiv ℝ g (s, t) (0, 1)) t :=
      hd.hasFDerivAt.comp_hasDerivAt t
        ((hasDerivAt_const t s).prodMk (hasDerivAt_id t))
    exact hder.deriv ▸ hnegative s hs t ht
  obtain ⟨e, hes, heU, he, hei, heimage⟩ :=
    exists_height_coordinates_on_compact_strip d.open_source hg hK hab hKs hvertical
  let c := (P.toPartialDiffeomorph.trans d).symm.trans e
  have hsource (z : E × ℝ) (hz : z ∈ K ×ˢ Icc a b) : d z ∈ c.source := by
    have hl : d.symm (d z) = z := d.left_inv (hKs hz)
    refine ⟨?_, ?_⟩
    · exact ⟨d.map_source (hKs hz), mem_univ _⟩
    · change d.symm (d z) ∈ e.source
      rw [hl]
      exact hes hz
  have hc (x : M) (hx : x ∈ c.source) : c x = ((d.symm x).1, f x) := by
    change e (d.symm x) = _
    rw [he]
    change ((d.symm x).1, f (d (d.symm x))) = _
    have hr : d (d.symm x) = x := d.right_inv hx.1.1
    rw [hr]
  have hce (z : E × ℝ) (hz : z ∈ K ×ˢ Icc a b) :
      c (d z) = (z.1, f (d z)) := by
    rw [hc _ (hsource z hz)]
    have hl : d.symm (d z) = z := d.left_inv (hKs hz)
    rw [hl]
  refine ⟨c, ?_, fun _ hx => hx.1.1, hc, ?_, hce, ?_⟩
  · rintro x ⟨z, hz, rfl⟩
    exact hsource z hz
  · intro z hz
    have hr : c (c.symm z) = z := c.right_inv hz
    exact Prod.mk.inj ((hc (c.symm z) (c.map_target hz)).symm.trans hr)
  · rw [image_image, ← heimage]
    apply image_congr
    intro z hz
    exact (hce z hz).trans (he z).symm

end DifferentialGeometry.Topology.Manifold
