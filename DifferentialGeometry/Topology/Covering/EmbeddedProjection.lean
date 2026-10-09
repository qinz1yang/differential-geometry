/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Mathlib.Data.Set.Card
import Mathlib.Topology.Covering.Basic

open Set Topology

namespace DifferentialGeometry.Topology.Covering

variable {X Y Z : Type*}

theorem encard_fiber_comp_le {f : X → Y} {p : Y → Z} {s : Set X}
    (hf : InjOn f s) (z : Z) :
    (s ∩ (p ∘ f) ⁻¹' {z}).encard ≤ (p ⁻¹' {z}).encard :=
  encard_le_encard_of_injOn (fun _ hx => hx.2) (hf.mono inter_subset_left)

theorem exists_injOn_mem_nhdsWithin_comp
    [TopologicalSpace X] [TopologicalSpace Y]
    {p : Y → Z} (hp : IsLocallyInjective p) {f : X → Y} {s : Set X}
    (hf : ContinuousOn f s) (hinj : InjOn f s) {x : X} (hx : x ∈ s) :
    ∃ U ∈ 𝓝[s] x, InjOn (p ∘ f) U := by
  obtain ⟨V, hV, hfx, hpinj⟩ := hp (f x)
  refine ⟨s ∩ f ⁻¹' V, Filter.inter_mem self_mem_nhdsWithin
    ((hf x hx).preimage_mem_nhdsWithin (hV.mem_nhds hfx)), ?_⟩
  intro a ha b hb hab
  exact hinj ha.1 hb.1 (hpinj ha.2 hb.2 hab)

theorem locally_injective_fiber_le_of_isCoveringMap
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    {p : Y → Z} (hp : IsCoveringMap p) {f : X → Y} {s : Set X}
    (hf : ContinuousOn f s) (hinj : InjOn f s) {n : ℕ∞}
    (hcard : ∀ z, (p ⁻¹' {z}).encard ≤ n) :
    (∀ x ∈ s, ∃ U ∈ 𝓝[s] x, InjOn (p ∘ f) U) ∧
      ∀ z, (s ∩ (p ∘ f) ⁻¹' {z}).encard ≤ n :=
  ⟨fun _ hx => exists_injOn_mem_nhdsWithin_comp
    hp.isLocalHomeomorph.isLocallyInjective hf hinj hx,
    fun z => (encard_fiber_comp_le hinj z).trans (hcard z)⟩

theorem isLocallyInjective_domRestrict_iff [TopologicalSpace X] {f : X → Y} {s : Set X} :
    IsLocallyInjective (s.domRestrict f) ↔ ∀ x ∈ s, ∃ U ∈ 𝓝[s] x, InjOn f U := by
  rw [isLocallyInjective_iff_nhds]
  constructor
  · intro h x hx
    obtain ⟨U, hU, hinj⟩ := h ⟨x, hx⟩
    refine ⟨Subtype.val '' U, mem_nhds_subtype_iff_nhdsWithin.mp hU, ?_⟩
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ hab
    exact congrArg Subtype.val (hinj ha hb hab)
  · intro h x
    obtain ⟨U, hU, hinj⟩ := h x x.2
    refine ⟨Subtype.val ⁻¹' U, preimage_coe_mem_nhds_subtype.mpr hU, ?_⟩
    intro a ha b hb hab
    exact Subtype.ext (hinj ha hb hab)

theorem locally_injective_fiber_le_of_isCoveringMap_restrict
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    {s : Set X} {t : Set Y} {u : Set Z} {f : X → Y} {p : Y → Z} {q : t → u}
    (hq : IsCoveringMap q) (heq : ∀ y : t, (q y : Z) = p y)
    (hf : ContinuousOn f s) (hinj : InjOn f s) (hft : MapsTo f s t) {n : ℕ∞}
    (hcard : ∀ z, (q ⁻¹' {z}).encard ≤ n) :
    (∀ x ∈ s, ∃ U ∈ 𝓝[s] x, InjOn (p ∘ f) U) ∧
      ∀ z, (s ∩ (p ∘ f) ⁻¹' {z}).encard ≤ n := by
  let g : s → t := hft.restrict f s t
  have hg : Function.Injective g := by
    intro a b hab
    exact Subtype.ext (hinj a.2 b.2 (congrArg Subtype.val hab))
  have hloc := (hq.isLocalHomeomorph.isLocallyInjective.comp_right
    (hf.mapsToRestrict hft) hg).comp_left (Subtype.val_injective (p := (· ∈ u)))
  have hcomp : ((↑) : u → Z) ∘ q ∘ g = s.domRestrict (p ∘ f) :=
    funext fun x => heq (g x)
  refine ⟨isLocallyInjective_domRestrict_iff.mp (hcomp ▸ hloc), ?_⟩
  intro z
  by_cases hz : z ∈ u
  · let z' : u := ⟨z, hz⟩
    have himage : Subtype.val '' ((q ∘ g) ⁻¹' {z'}) = s ∩ (p ∘ f) ⁻¹' {z} := by
      ext x
      constructor
      · rintro ⟨a, ha, rfl⟩
        exact ⟨a.2, (heq (g a)).symm.trans (congrArg Subtype.val ha)⟩
      · rintro ⟨hxs, hx⟩
        refine ⟨⟨x, hxs⟩, ?_, rfl⟩
        exact Subtype.ext ((heq (g ⟨x, hxs⟩)).trans hx)
    calc
      (s ∩ (p ∘ f) ⁻¹' {z}).encard = ((q ∘ g) ⁻¹' {z'}).encard := by
        rw [← himage, Subtype.val_injective.encard_image]
      _ ≤ (q ⁻¹' {z'}).encard := by
        simpa only [univ_inter] using encard_fiber_comp_le (s := univ) hg.injOn z'
      _ ≤ n := hcard z'
  · have hempty : s ∩ (p ∘ f) ⁻¹' {z} = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      rintro x ⟨hxs, hx⟩
      have hmem : p (f x) ∈ u := (heq (g ⟨x, hxs⟩)) ▸ (q (g ⟨x, hxs⟩)).2
      exact hz (hx ▸ hmem)
    rw [hempty, encard_empty]
    exact bot_le
end DifferentialGeometry.Topology.Covering
