/-
Copyright (c) 2026 Yuan Liao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuan Liao
-/
import DifferentialGeometry.Topology.Morse.LocalizedCubicCancellation
import DifferentialGeometry.Topology.Manifold.PartialDiffeomorph.FunctionExtension

open Set Filter Function
open scoped ContDiff Manifold Topology
open DifferentialGeometry.Topology.Morse

namespace DifferentialGeometry.Morse

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M] [T2Space M]
  {I : ModelWithCorners ℝ E H}

theorem exists_regular_perturbation_of_cubic_chart
    (c : PartialDiffeomorph I 𝓘(ℝ, ℝ × ℝ) M (ℝ × ℝ) ∞)
    (h0 : (0 : ℝ × ℝ) ∈ c.target) {V : Set M} (hV : IsOpen V) (hV0 : c.symm 0 ∈ V) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (a b : ℝ), 0 < a → a < δ → ∀ f : M → ℝ,
      ContMDiff I 𝓘(ℝ, ℝ) ∞ f →
      (∀ z ∈ c.target, f (c.symm z) = b + (z.1 ^ 3 / 3 - a * z.1 + z.2 ^ 2)) →
      ∃ G : M → ℝ, ContMDiff I 𝓘(ℝ, ℝ) ∞ G ∧ HasCompactSupport (G - f) ∧
        tsupport (G - f) ⊆ V ∩ c.source ∧
        {x | IsCriticalPointAt I G x} = {x | IsCriticalPointAt I f x} \ c.source ∧
        (∃ N : Set M, IsOpen N ∧ Vᶜ ∪ c.sourceᶜ ⊆ N ∧ EqOn G f N) ∧
        ∃ g : ℝ × ℝ → ℝ, ContDiff ℝ ∞ g ∧
          (∀ z, ¬ IsCriticalPointAt 𝓘(ℝ, ℝ × ℝ) g z) ∧
          (∀ z ∈ c.target, G (c.symm z) = b + g z) ∧
          tsupport (G - f) = c.symm '' tsupport
            (fun z => g z - (z.1 ^ 3 / 3 - a * z.1 + z.2 ^ 2)) := by
  let U : Set (ℝ × ℝ) := c.target ∩ c.symm ⁻¹' V
  have hU : IsOpen U := c.symm.contMDiffOn.continuousOn.isOpen_inter_preimage c.open_target hV
  obtain ⟨δ, hδ, hsmall⟩ := exists_cubic_suspension_cancellation_tsupport_subset hU ⟨h0, hV0⟩
  refine ⟨δ, hδ, fun a b ha haδ f hf hnormal => ?_⟩
  obtain ⟨g, hg, hgc, hgs, hreg, _⟩ := hsmall a ha haδ
  let k : ℝ × ℝ → ℝ := fun z => g z - (z.1 ^ 3 / 3 - a * z.1 + z.2 ^ 2)
  have hk : ContMDiff 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ℝ) ∞ k := by
    apply contMDiff_iff_contDiff.mpr
    exact hg.sub (by fun_prop)
  obtain ⟨h, hh, hhc, hval, hts, hsource, _⟩ :=
    c.exists_contMDiff_extension_of_hasCompactSupport hk.contMDiffOn hgc
      (fun z hz => (hgs hz).1)
  let G : M → ℝ := f + h
  have hG : ContMDiff I 𝓘(ℝ, ℝ) ∞ G := hf.add hh
  have hdiff : G - f = h := by ext x; change f x + h x - f x = h x; ring
  have hsupportV : tsupport h ⊆ V := by
    rw [hts]
    rintro x ⟨z, hz, rfl⟩
    exact (hgs hz).2
  let N := (tsupport h)ᶜ
  have hN : IsOpen N := (isClosed_tsupport h).isOpen_compl
  have hNsub : Vᶜ ∪ c.sourceᶜ ⊆ N := by
    rintro x (hx | hx) hxt
    · exact hx (hsupportV hxt)
    · exact hx (hsource hxt)
  have hfix : EqOn G f N := by
    intro x hx
    change f x + h x = f x
    rw [image_eq_zero_of_notMem_tsupport hx, add_zero]
  have hcoordinates (z : ℝ × ℝ) (hz : z ∈ c.target) : G (c.symm z) = b + g z := by
    change f (c.symm z) + h (c.symm z) = _
    have hv : h (c.symm z) = k (c (c.symm z)) := hval (c.map_target hz)
    have hr : c (c.symm z) = z := c.right_inv hz
    rw [hnormal z hz, hv, hr]
    dsimp [k]
    ring
  have hregular (x : M) (hx : x ∈ c.source) : ¬ IsCriticalPointAt I G x := by
    intro hc
    let z := c x
    have hz : z ∈ c.target := c.map_source hx
    have heq : G ∘ c.symm =ᶠ[𝓝 z] (fun q => b + g q) := by
      filter_upwards [c.open_target.mem_nhds hz] with q hq
      exact hcoordinates q hq
    have hzero : mfderiv I 𝓘(ℝ, ℝ) G (c.symm z) = 0 := by
      let D : M → E →L[ℝ] ℝ := fun y => mfderiv I 𝓘(ℝ, ℝ) G y
      change D (c.symm (c x)) = 0
      have hl : c.symm (c x) = x := c.left_inv hx
      rw [hl]
      exact hc
    have hcomp : mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ℝ) (G ∘ c.symm) z = 0 := by
      rw [mfderiv_comp z (hG.mdifferentiable (by simp) _)
        (c.symm.mdifferentiableAt (by simp) hz), hzero, ContinuousLinearMap.zero_comp]
    have hD : fderiv ℝ (fun q => b + g q) z = 0 := by
      rw [heq.mfderiv_eq, mfderiv_eq_fderiv] at hcomp
      exact hcomp
    have hd : fderiv ℝ (fun q => b + g q) z = fderiv ℝ g z := by
      exact ((hg.differentiable (by simp) z).hasFDerivAt.const_add b).fderiv
    apply hreg z
    unfold IsCriticalPointAt
    rw [mfderiv_eq_fderiv]
    exact hd.symm.trans hD
  have hcrit : {x | IsCriticalPointAt I G x} = {x | IsCriticalPointAt I f x} \ c.source := by
    ext x
    by_cases hx : x ∈ c.source
    · exact ⟨fun hc => (hregular x hx hc).elim, fun hc => (hc.2 hx).elim⟩
    · have heq : G =ᶠ[𝓝 x] f := by
        filter_upwards [hN.mem_nhds (hNsub (Or.inr hx))] with y hy
        exact hfix hy
      change IsCriticalPointAt I G x ↔ IsCriticalPointAt I f x ∧ x ∉ c.source
      unfold IsCriticalPointAt
      rw [heq.mfderiv_eq]
      exact ⟨fun hc => ⟨hc, hx⟩, And.left⟩
  refine ⟨G, hG, hdiff.symm ▸ hhc, ?_, hcrit, ⟨N, hN, hNsub, hfix⟩,
    g, hg, hreg, hcoordinates, ?_⟩
  · rw [hdiff]
    exact fun x hx => ⟨hsupportV hx, hsource hx⟩
  · rw [hdiff]
    exact hts

end DifferentialGeometry.Morse
