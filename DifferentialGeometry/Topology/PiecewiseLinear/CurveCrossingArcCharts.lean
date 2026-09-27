/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.BigonBoundaryCrossing

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

theorem HasPLCurveCrossingOnAt.eventually_mem_arc_iff_in_chart
    {M : Type*} [TopologicalSpace M] {S A B C : Set M} {x : M}
    (c : OpenPartialHomeomorph M E3) (hxc : x ∈ c.source)
    (hc : HasPLCurveCrossingOnAt (c '' (S ∩ c.source))
      (c '' (A ∩ c.source)) (c '' (B ∩ c.source)) (c x))
    {γ : ℝ → M} (hγc : ContinuousOn γ (Icc 0 1)) (hγinj : InjOn γ (Icc 0 1))
    (hγimage : γ '' Icc 0 1 = C) (hCB : C ⊆ B)
    (hx : x ∈ C \ {γ 0, γ 1}) : ∀ᶠ y in 𝓝 x, y ∈ C ↔ y ∈ B := by
  classical
  obtain ⟨U, V, φ, T, P, Q, hU, hV, hxU, hφ, -, -, -, hQ, -, -, -, hlocal⟩ := hc
  let e := c.trans (hφ.toOpenPartialHomeomorph hU hV)
  have hxe : x ∈ e.source := ⟨hxc, hxU⟩
  have hγmaps : MapsTo γ (Icc 0 1) C := fun t ht => hγimage ▸ mem_image_of_mem γ ht
  have hmem (Z : Set M) {y : M} (hy : y ∈ c.source) :
      y ∈ Z ↔ c y ∈ c '' (Z ∩ c.source) := by
    refine ⟨fun hyZ => ⟨y, ⟨hyZ, hy⟩, rfl⟩, ?_⟩
    rintro ⟨z, hz, hzy⟩
    exact c.injOn hz.2 hy hzy ▸ hz.1
  have hlocal : ∀ᶠ y in 𝓝 x,
      (y ∈ S ↔ e y ∈ T) ∧ (y ∈ A ↔ e y ∈ P) ∧ (y ∈ B ↔ e y ∈ Q) := by
    filter_upwards [(c.continuousAt hxc).tendsto.eventually hlocal,
      c.open_source.mem_nhds hxc] with y hy hyc
    exact ⟨(hmem S hyc).trans hy.1, (hmem A hyc).trans hy.2.1,
      (hmem B hyc).trans hy.2.2⟩
  have hsmall : ∀ᶠ y in 𝓝 x, y ∈ e.source ∧ (y ∈ B ↔ e y ∈ Q) := by
    filter_upwards [e.open_source.mem_nhds hxe, hlocal] with y hyU hy
    exact ⟨hyU, hy.2.2⟩
  obtain ⟨O, hOO, hO, hxO⟩ := _root_.mem_nhds_iff.mp hsmall
  have hQne : Q ≠ ⊥ := by
    intro heq
    rw [heq, finrank_bot] at hQ
    omega
  obtain ⟨v, hvQ, hv0⟩ := Q.ne_bot_iff.mp hQne
  obtain ⟨ℓ, hℓv⟩ := Module.Projective.exists_dual_ne_zero ℝ hv0
  have hspan : Submodule.span ℝ {v} = Q := by
    apply Submodule.eq_of_le_of_finrank_eq
    · rwa [Submodule.span_singleton_le_iff_mem]
    · rw [finrank_span_singleton hv0, hQ]
  have hℓinj : InjOn ℓ (Q : Set E3) := by
    intro y hy z hz hyz
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp (hspan.symm ▸ Q.sub_mem hy hz)
    have haz : a * ℓ v = 0 := by
      simpa only [map_smul, smul_eq_mul, map_sub, hyz, sub_self] using congrArg ℓ ha
    have ha0 : a = 0 := (mul_eq_zero.mp haz).resolve_right hℓv
    apply sub_eq_zero.mp
    rw [← ha, ha0, zero_smul]
  obtain ⟨t, ht, htx⟩ := hγimage.symm ▸ hx.1
  have ht0 : t ≠ 0 := fun h => hx.2 (Or.inl (htx.symm.trans (congrArg γ h)))
  have ht1 : t ≠ 1 := fun h => hx.2 (Or.inr (htx.symm.trans (congrArg γ h)))
  have htI : t ∈ Ioo (0 : ℝ) 1 := ⟨lt_of_le_of_ne ht.1 (Ne.symm ht0),
    lt_of_le_of_ne ht.2 ht1⟩
  let W := Ioo (0 : ℝ) 1 ∩ γ ⁻¹' O
  have hW : IsOpen W := (hγc.mono Ioo_subset_Icc_self).isOpen_inter_preimage isOpen_Ioo hO
  have htW : t ∈ W := ⟨htI, by change γ t ∈ O; rwa [htx]⟩
  have hγW : MapsTo γ W e.source := fun s hs => (hOO hs.2).1
  have hγQ : ∀ s ∈ W, e (γ s) ∈ Q := fun s hs =>
    (hOO hs.2).2.mp (hCB (hγmaps (Ioo_subset_Icc_self hs.1)))
  let f : M → ℝ := fun y => ℓ (e y)
  have hfc : ContinuousOn f e.source := ℓ.continuous_of_finiteDimensional.comp_continuousOn
    e.continuousOn
  have hcomp : ContinuousOn (f ∘ γ) W := hfc.comp
    (hγc.mono (inter_subset_left.trans Ioo_subset_Icc_self)) hγW
  have hinj : InjOn (f ∘ γ) W := by
    intro s hs r hr heq
    exact hγinj (Ioo_subset_Icc_self hs.1) (Ioo_subset_Icc_self hr.1)
      (e.injOn (hγW hs) (hγW hr) (hℓinj (hγQ s hs) (hγQ r hr) heq))
  have himg : IsOpen ((f ∘ γ) '' W) :=
    invariance_of_domain_isOpen_image_of_finrank_eq rfl hW hcomp hinj
  have hN : IsOpen (O ∩ f ⁻¹' ((f ∘ γ) '' W)) :=
    (hfc.mono fun y hy => (hOO hy).1).isOpen_inter_preimage hO himg
  have hxN : x ∈ O ∩ f ⁻¹' ((f ∘ γ) '' W) := ⟨hxO, t, htW, congrArg f htx⟩
  filter_upwards [hN.mem_nhds hxN] with y hy
  refine ⟨fun hyC => hCB hyC, fun hyB => ?_⟩
  obtain ⟨s, hs, hsy⟩ := hy.2
  have hφeq : e (γ s) = e y := hℓinj (hγQ s hs) ((hOO hy.1).2.mp hyB) hsy
  have hγeq : γ s = y := e.injOn (hγW hs) (hOO hy.1).1 hφeq
  exact hγeq ▸ hγmaps (Ioo_subset_Icc_self hs.1)

end DifferentialGeometry.Topology.PiecewiseLinear
