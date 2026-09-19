/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Mathlib.Data.Set.Card
import Mathlib.Topology.Covering.Basic

/-!
# Projections of embedded subsets through covering maps
-/

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

end DifferentialGeometry.Topology.Covering
