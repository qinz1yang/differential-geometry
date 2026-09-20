/-
Copyright (c) 2026 Yuan Liao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuan Liao
-/
import DifferentialGeometry.Topology.Manifold.GermExtension
import DifferentialGeometry.Topology.Manifold.PartialDiffeomorph.CompactPasting

/-! Height-separated extensions along radial segments of quadratic coordinate charts. -/

open Set Filter Topology
open scoped ContDiff Manifold

namespace DifferentialGeometry.Morse

variable {E F H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]
  {I : ModelWithCorners ℝ E H}

theorem exists_diffeomorph_extending_radial_height_chart
    (χ : PartialDiffeomorph 𝓘(ℝ, F) I F M ∞)
    (C : PartialDiffeomorph I 𝓘(ℝ, ℂ) M ℂ ∞)
    {z : F} (hz : z ∈ χ.source) (hxC : χ z ∈ C.source)
    {f : M → ℝ} (hC : ∀ y ∈ C.source, (C y).im = f y)
    {a b : ℝ} (hab : a ≠ b)
    (hquad : ∀ t : ℝ, t • z ∈ χ.source → f (χ (t • z)) = a + t ^ 2 * (b - a)) :
    ∃ D : Diffeomorph 𝓘(ℝ, F) 𝓘(ℝ, ℂ) F ℂ ∞,
      D z = C (χ z) ∧
      (∀ t : ℝ, t < 1 → ((D (t • z)).im - b) * (a - b) > 0) ∧
      let c := χ.symm.trans D.toPartialDiffeomorph
      c.source = χ.target ∧ (c : M → ℂ) =ᶠ[𝓝 (χ z)] C ∧
      ∀ u ∈ χ.source, c (χ u) = D u := by
  let φ := χ.trans C
  have hzφ : z ∈ φ.source := ⟨hz, hxC⟩
  have hφ := (φ.contMDiffOn.contDiffOn.contDiffAt
    (φ.open_source.mem_nhds hzφ)).differentiableAt (by simp)
  have hd : HasDerivAt (fun t : ℝ => (φ (t • z)).im) ((fderiv ℝ φ z z).im) 1 := by
    have hdz : HasDerivAt (fun t : ℝ => t • z) z 1 := by
      simpa only [one_smul, id_eq] using (hasDerivAt_id (1 : ℝ)).smul_const z
    have hφ' : HasFDerivAt φ (fderiv ℝ φ z) ((1 : ℝ) • z) := by
      simpa only [one_smul] using hφ.hasFDerivAt
    exact Complex.imCLM.hasFDerivAt.comp_hasDerivAt 1 (hφ'.comp_hasDerivAt 1 hdz)
  have ht : Tendsto (fun t : ℝ => t • z) (𝓝 1) (𝓝 z) := by
    simpa only [one_smul] using
      (show Continuous (fun t : ℝ => t • z) from
        continuous_id.smul continuous_const).tendsto (1 : ℝ)
  have he : (fun t : ℝ => (φ (t • z)).im) =ᶠ[𝓝 1] (fun t => a + t ^ 2 * (b - a)) := by
    filter_upwards [ht.eventually (φ.open_source.mem_nhds hzφ)] with t htφ
    exact (hC _ htφ.2).trans (hquad t htφ.1)
  have hp : HasDerivAt (fun t : ℝ => a + t ^ 2 * (b - a)) (2 * (b - a)) 1 := by
    simpa only [Pi.pow_apply, id_eq, one_pow, mul_one, Nat.cast_ofNat] using
      (((hasDerivAt_id (1 : ℝ)).pow 2).mul_const (b - a)).const_add a
  have hdz : (fderiv ℝ φ z z).im = 2 * (b - a) :=
    hd.unique (hp.congr_of_eventuallyEq he)
  have hneg : (fderiv ℝ φ z (-z)).im = 2 * (a - b) := by
    rw [map_neg, Complex.neg_im, hdz]
    ring
  have hne : (fderiv ℝ φ z (-z)).im ≠ 0 := by
    rw [hneg]
    exact mul_ne_zero (by norm_num) (sub_ne_zero.mpr hab)
  obtain ⟨D, hD, hDgerm, hsep⟩ :=
    DifferentialGeometry.Topology.Manifold.exists_diffeomorph_realizing_germ_separating_ray
      φ hzφ hne
  have him : (φ z).im = b := by
    change (C (χ z)).im = b
    rw [hC _ hxC]
    have hh := hquad 1 (by simpa only [one_smul] using hz)
    simpa only [one_smul, one_pow, one_mul, add_sub_cancel] using hh
  let c := χ.symm.trans D.toPartialDiffeomorph
  refine ⟨D, hD, ?_, ?_, ?_, ?_⟩
  · intro t ht1
    have hh := hsep (1 - t) (sub_pos.mpr ht1)
    have hv : z + (1 - t) • (-z) = t • z := by module
    rw [hv, him, hneg] at hh
    nlinarith
  · ext y
    exact and_iff_left (mem_univ (χ.symm y))
  · have hχinv : Tendsto χ.symm (𝓝 (χ z)) (𝓝 z) := by
      have hh := (χ.symm.contMDiffOn.contMDiffAt
        (χ.open_target.mem_nhds (χ.map_source hz))).continuousAt.tendsto
      have hi : χ.symm (χ z) = z := χ.left_inv hz
      rwa [hi] at hh
    filter_upwards [hDgerm.comp_tendsto hχinv,
      χ.open_target.mem_nhds (χ.map_source hz)] with y hy hyt
    change D (χ.symm y) = C y
    change D (χ.symm y) = C (χ (χ.symm y)) at hy
    exact hy.trans (congrArg C (χ.right_inv hyt))
  · intro u hu
    change D (χ.symm (χ u)) = D u
    exact congrArg D (χ.left_inv hu)

theorem exists_chart_pasting_radial_segment [T2Space M]
    (χ : PartialDiffeomorph 𝓘(ℝ, F) I F M ∞)
    (C : PartialDiffeomorph I 𝓘(ℝ, ℂ) M ℂ ∞)
    (D : Diffeomorph 𝓘(ℝ, F) 𝓘(ℝ, ℂ) F ℂ ∞)
    {z : F} {K : Set M} (hK : IsCompact K) (hKC : K ⊆ C.source) (hxK : χ z ∈ K)
    {f : M → ℝ} {a b σ : ℝ} (hside : 0 < σ * (a - b))
    (hquad : ∀ t ∈ Icc (0 : ℝ) 1, f (χ (t • z)) = a + t ^ 2 * (b - a))
    (hKf : ∀ y ∈ K, σ * (f y - b) ≤ 0)
    (hKCim : ∀ y ∈ K, σ * ((C y).im - b) ≤ 0)
    (hDsep : ∀ t : ℝ, t < 1 → 0 < σ * ((D (t • z)).im - b))
    (hmatch : (χ.symm.trans D.toPartialDiffeomorph : M → ℂ) =ᶠ[𝓝 (χ z)] C)
    {O : Set M} (hO : IsOpen O) (hKO : K ⊆ O)
    (hray : ∀ t ∈ Icc (0 : ℝ) 1, t • z ∈ χ.source ∧ χ (t • z) ∈ O) :
    ∃ c : PartialDiffeomorph I 𝓘(ℝ, ℂ) M ℂ ∞,
      K ∪ (fun t : ℝ => χ (t • z)) '' Icc (0 : ℝ) 1 ⊆ c.source ∧ c.source ⊆ O ∧
      (∀ y ∈ K, (c : M → ℂ) =ᶠ[𝓝 y] C) ∧
      ∀ y ∈ (fun t : ℝ => χ (t • z)) '' Icc (0 : ℝ) 1,
        (c : M → ℂ) =ᶠ[𝓝 y] χ.symm.trans D.toPartialDiffeomorph := by
  let _ : Nonempty M := ⟨χ 0⟩
  let R := (fun t : ℝ => χ (t • z)) '' Icc (0 : ℝ) 1
  let e := χ.symm.trans D.toPartialDiffeomorph
  have hR : IsCompact R := isCompact_Icc.image_of_continuousOn
    (χ.contMDiffOn.continuousOn.comp (continuous_id.smul continuous_const).continuousOn
      (fun t ht => (hray t ht).1))
  have hRe : R ⊆ e.source := by
    rintro y ⟨t, ht, rfl⟩
    exact ⟨χ.map_source (hray t ht).1, mem_univ _⟩
  have hvalue (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : e (χ (t • z)) = D (t • z) :=
    congrArg D (χ.left_inv (hray t ht).1)
  have hstrict (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) (hlt : t < 1) :
      0 < σ * (f (χ (t • z)) - b) := by
    rw [hquad t ht]
    have hsquare : 0 < 1 - t ^ 2 := by nlinarith [ht.1]
    have heq : σ * (a + t ^ 2 * (b - a) - b) = (1 - t ^ 2) * (σ * (a - b)) := by ring
    rw [heq]
    exact mul_pos hsquare hside
  have hinter : K ∩ R ⊆ {χ z} := by
    rintro y ⟨hy, t, ht, rfl⟩
    have ht1 : t = 1 := by
      by_contra hn
      have hh := hstrict t ht (ht.2.lt_of_ne hn)
      exact (not_lt_of_ge (hKf _ hy)) hh
    simp only [ht1, one_smul, mem_singleton_iff]
  obtain ⟨V, hVm, hV, hxV⟩ := mem_nhds_iff.mp hmatch
  have hcross : ∀ y ∈ K, ∀ w ∈ R, C y = e w → y = w := by
    intro y hy w hw heq
    obtain ⟨t, ht, rfl⟩ := hw
    by_cases ht1 : t = 1
    · have heq' : C y = e (χ z) := by simpa only [ht1, one_smul] using heq
      have he : C y = C (χ z) := heq'.trans hmatch.eq_of_nhds
      have hyz := C.injOn (hKC hy) (hKC hxK) he
      simpa only [ht1, one_smul] using hyz
    · have hsep := hDsep t (ht.2.lt_of_ne ht1)
      have hi : (C y).im = (D (t • z)).im := congrArg Complex.im (heq.trans (hvalue t ht))
      rw [← hi] at hsep
      exact ((not_lt_of_ge (hKCim y hy)) hsep).elim
  exact C.exists_pasting_of_compact e hK hR hKC hRe hV
    (fun y hy => (show y = χ z from hinter hy) ▸ hxV) (fun y hy => (hVm hy).symm)
    hcross hO (union_subset hKO (by rintro y ⟨t, ht, rfl⟩; exact (hray t ht).2))
end DifferentialGeometry.Morse
