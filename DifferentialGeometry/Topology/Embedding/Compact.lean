/-
Copyright (c) 2026 Bennett Chow. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bennett Chow, OpenAI
-/
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Separation.Hausdorff

set_option autoImplicit false

open Filter Function Set Topology

namespace DifferentialGeometry.Topology

theorem exists_injOn_prod_nhds_of_compact
    {X T Y : Type*} [TopologicalSpace X] [CompactSpace X] [TopologicalSpace T]
    [TopologicalSpace Y] [T2Space Y] {f : X × T → Y} {t₀ : T}
    (hf : Continuous f) (hzero : Injective (fun x ↦ f (x, t₀)))
    (hloc : ∀ x, ∃ W ∈ nhds (x, t₀), InjOn f W) :
    ∃ U ∈ nhds t₀, InjOn f (univ ×ˢ U) := by
  let q₁ : (X × X) × (T × T) → X × T := fun p ↦ (p.1.1, p.2.1)
  let q₂ : (X × X) × (T × T) → X × T := fun p ↦ (p.1.2, p.2.2)
  have hq₁ : Continuous q₁ := by fun_prop
  have hq₂ : Continuous q₂ := by fun_prop
  let good : Set ((X × X) × (T × T)) := {p | f (q₁ p) = f (q₂ p) → q₁ p = q₂ p}
  have hgood (p : X × X) : good ∈ nhds (p, (t₀, t₀)) := by
    rcases p with ⟨x, y⟩
    by_cases hxy : x = y
    · subst y
      obtain ⟨W, hW, hinj⟩ := hloc x
      filter_upwards [hq₁.continuousAt.preimage_mem_nhds hW,
        hq₂.continuousAt.preimage_mem_nhds hW] with p hp₁ hp₂
      exact hinj hp₁ hp₂
    · have hne : f (q₁ ((x, y), (t₀, t₀))) ≠ f (q₂ ((x, y), (t₀, t₀))) :=
        fun h ↦ hxy (hzero h)
      filter_upwards [((hf.comp hq₁).continuousAt.ne_iff_eventually_ne
        (hf.comp hq₂).continuousAt).mp hne] with p hp
      exact fun h ↦ (hp h).elim
  have hprod : good ∈ (nhdsSet (univ : Set (X × X))) ×ˢ nhds (t₀, t₀) :=
    isCompact_univ.mem_nhdsSet_prod_of_forall (fun p _ ↦ by simpa [nhds_prod_eq] using hgood p)
  obtain ⟨V, hV, W, hW, hVW⟩ := Filter.mem_prod_iff.mp hprod
  have hVall : ∀ p, p ∈ V := by
    have hV' : V = univ := by simpa using hV
    simp [hV']
  rw [nhds_prod_eq] at hW
  obtain ⟨U₁, hU₁, U₂, hU₂, hU⟩ := Filter.mem_prod_iff.mp hW
  refine ⟨U₁ ∩ U₂, inter_mem hU₁ hU₂, ?_⟩
  intro p hp q hq heq
  exact hVW (show ((p.1, q.1), (p.2, q.2)) ∈ V ×ˢ W from
    ⟨hVall (p.1, q.1), hU ⟨hp.2.1, hq.2.2⟩⟩) heq

end DifferentialGeometry.Topology
