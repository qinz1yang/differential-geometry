/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Mathlib.Topology.OpenPartialHomeomorph.Composition
import DifferentialGeometry.Analysis.Calculus.Compactness.Superposition

open Set Topology

namespace OpenPartialHomeomorph

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

open Classical in
noncomputable def conjugateMap (e : _root_.OpenPartialHomeomorph X Y)
    (h : Y → Y) : X → X := e.source.piecewise (e.symm ∘ h ∘ e) id

theorem conjugateMap_of_mem (e : _root_.OpenPartialHomeomorph X Y)
    (h : Y → Y) {x : X} (hx : x ∈ e.source) : e.conjugateMap h x = e.symm (h (e x)) := by
  classical
  exact piecewise_eq_of_mem e.source (e.symm ∘ h ∘ e) id hx

theorem conjugateMap_of_notMem (e : _root_.OpenPartialHomeomorph X Y)
    (h : Y → Y) {x : X} (hx : x ∉ e.source) : e.conjugateMap h x = x := by
  classical
  exact piecewise_eq_of_notMem e.source (e.symm ∘ h ∘ e) id hx

theorem conjugateMap_eqOn_compl (e : _root_.OpenPartialHomeomorph X Y)
    {h : Y → Y} {C : Set Y} (hfix : EqOn h id Cᶜ) :
    EqOn (e.conjugateMap h) id (e.symm '' C)ᶜ := by
  classical
  intro x hx
  by_cases hxsource : x ∈ e.source
  · have hxC : e x ∉ C := fun heC => hx ⟨e x, heC, e.left_inv hxsource⟩
    rw [e.conjugateMap_of_mem h hxsource, hfix hxC, id_eq, e.left_inv hxsource]
    rfl
  · exact e.conjugateMap_of_notMem h hxsource

theorem continuous_conjugateMap [T2Space X]
    (e : _root_.OpenPartialHomeomorph X Y) {h : Y → Y} (hh : ContinuousOn h e.target)
    (hmap : MapsTo h e.target e.target) {C : Set Y} (hC : IsCompact C) (hCt : C ⊆ e.target)
    (hfix : EqOn h id Cᶜ) : Continuous (e.conjugateMap h) := by
  classical
  have hclosed : IsClosed (e.symm '' C) :=
    (hC.image_of_continuousOn (e.continuousOn_symm.mono hCt)).isClosed
  rw [continuous_iff_continuousAt]
  intro x
  by_cases hx : x ∈ e.source
  · have hc : ContinuousAt (e.symm ∘ h ∘ e) x :=
      ((e.continuousAt_symm (hmap (e.map_source hx))).comp
        (hh.continuousAt (e.open_target.mem_nhds (e.map_source hx)))).comp (e.continuousAt hx)
    apply hc.congr_of_eventuallyEq
    filter_upwards [e.open_source.mem_nhds hx] with z hz
    exact e.conjugateMap_of_mem h hz
  · have hxC : x ∉ e.symm '' C := by
      rintro ⟨y, hy, rfl⟩
      exact hx (e.map_target (hCt hy))
    apply continuousAt_id.congr_of_eventuallyEq
    filter_upwards [hclosed.isOpen_compl.mem_nhds hxC] with z hz
    exact e.conjugateMap_eqOn_compl hfix hz

noncomputable def conjugateHomeomorph [T2Space X]
    (e : _root_.OpenPartialHomeomorph X Y) (h : Y ≃ₜ Y)
    {C : Set Y} (hC : IsCompact C) (hCt : C ⊆ e.target) (hfix : EqOn h id Cᶜ) : X ≃ₜ X := by
  have hmaps : ∀ k : Y ≃ₜ Y, EqOn k id Cᶜ → MapsTo k e.target e.target := by
    intro k hk y hy
    by_contra hnot
    have hyC : k y ∉ C := fun hky => hnot (hCt hky)
    have heq : k y = y := k.injective (hk hyC)
    exact hnot (by rwa [heq])
  have hsymfix : EqOn h.symm id Cᶜ := by
    intro y hy
    have heq := congrArg h.symm (hfix hy)
    simpa only [Homeomorph.symm_apply_apply, id_eq] using heq.symm
  refine
    { toFun := e.conjugateMap h
      invFun := e.conjugateMap h.symm
      left_inv := ?_
      right_inv := ?_
      continuous_toFun := e.continuous_conjugateMap h.continuous.continuousOn (hmaps h hfix) hC hCt
          hfix
      continuous_invFun := e.continuous_conjugateMap h.symm.continuous.continuousOn
        (hmaps h.symm hsymfix) hC hCt hsymfix }
  · intro x
    by_cases hx : x ∈ e.source
    · rw [e.conjugateMap_of_mem h hx,
        e.conjugateMap_of_mem h.symm (e.map_target (hmaps h hfix (e.map_source hx))),
        e.right_inv (hmaps h hfix (e.map_source hx)), h.symm_apply_apply, e.left_inv hx]
    · rw [e.conjugateMap_of_notMem h hx, e.conjugateMap_of_notMem h.symm hx]
  · intro x
    by_cases hx : x ∈ e.source
    · rw [e.conjugateMap_of_mem h.symm hx,
        e.conjugateMap_of_mem h (e.map_target (hmaps h.symm hsymfix (e.map_source hx))),
        e.right_inv (hmaps h.symm hsymfix (e.map_source hx)), h.apply_symm_apply, e.left_inv hx]
    · rw [e.conjugateMap_of_notMem h.symm hx, e.conjugateMap_of_notMem h hx]

theorem conjugateHomeomorph_apply [T2Space X]
    (e : _root_.OpenPartialHomeomorph X Y) (h : Y ≃ₜ Y)
    {C : Set Y} (hC : IsCompact C) (hCt : C ⊆ e.target) (hfix : EqOn h id Cᶜ) (x : X) :
    e.conjugateHomeomorph h hC hCt hfix x = e.conjugateMap h x := rfl

theorem conjugateHomeomorph_symm_apply [T2Space X]
    (e : _root_.OpenPartialHomeomorph X Y) (h : Y ≃ₜ Y)
    {C : Set Y} (hC : IsCompact C) (hCt : C ⊆ e.target) (hfix : EqOn h id Cᶜ) (x : X) :
    (e.conjugateHomeomorph h hC hCt hfix).symm x = e.conjugateMap h.symm x := rfl

theorem conjugateMap_mem_iff (e : _root_.OpenPartialHomeomorph X Y)
    {h : Y → Y} (hmap : MapsTo h e.target e.target) {A : Set X} {B : Set Y}
    (hcoord : ∀ x ∈ e.source, x ∈ A ↔ e x ∈ B)
    (hB : ∀ y ∈ e.target, h y ∈ B ↔ y ∈ B) (x : X) :
    e.conjugateMap h x ∈ A ↔ x ∈ A := by
  by_cases hx : x ∈ e.source
  · rw [e.conjugateMap_of_mem h hx,
      hcoord _ (e.map_target (hmap (e.map_source hx))),
      e.right_inv (hmap (e.map_source hx)), hB _ (e.map_source hx)]
    exact (hcoord x hx).symm
  · rw [e.conjugateMap_of_notMem h hx]

theorem exists_uniform_conjugateMap_radius {E Z : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [PseudoMetricSpace Z] (e : OpenPartialHomeomorph Z E)
    {C : Set E} (hC : IsCompact C) (hCt : C ⊆ e.target) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ h : E → E, (∀ y ∈ C, dist (h y) y < δ) → EqOn h id Cᶜ →
      MapsTo h e.target e.target ∧ ∀ x, dist (e.conjugateMap h x) x < ε := by
  have : CompactSpace C := isCompact_iff_compactSpace.mp hC
  obtain ⟨δ, hδ, hbound⟩ := DifferentialGeometry.Analysis.exists_uniform_superposition_radius
    (c := (Subtype.val : C → E)) continuous_subtype_val e.open_target
    (fun _ ⟨y, hy⟩ => hy ▸ hCt y.property) e.continuousOn_symm hε
  refine ⟨δ, hδ, fun h hclose hfix => ⟨?_, ?_⟩⟩
  · intro y hy
    by_cases hyC : y ∈ C
    · exact (hbound ⟨y, hyC⟩ (h y) (hclose y hyC)).1
    · simpa only [hfix hyC, id_eq] using hy
  · intro x
    by_cases hx : x ∈ e.source
    · rw [e.conjugateMap_of_mem h hx]
      by_cases hxC : e x ∈ C
      · have hb := (hbound ⟨e x, hxC⟩ (h (e x)) (hclose (e x) hxC)).2
        simpa only [e.left_inv hx] using hb
      · rw [hfix hxC, id_eq, e.left_inv hx, dist_self]
        exact hε
    · rw [e.conjugateMap_of_notMem h hx, dist_self]
      exact hε
end OpenPartialHomeomorph
