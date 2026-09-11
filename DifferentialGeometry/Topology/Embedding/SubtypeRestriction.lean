/-
Copyright (c) 2026 Bennett Chow. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bennett Chow, OpenAI
-/
import Mathlib.Topology.OpenPartialHomeomorph.Constructions

set_option autoImplicit false

open Set Topology

noncomputable section

namespace DifferentialGeometry.Topology.OpenPartialHomeomorph

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

def restrictSubtypes (e : _root_.OpenPartialHomeomorph X Y) (s : Set X) (t : Set Y)
    (hs : s) (ht : t) (h : ∀ x ∈ e.source, x ∈ s ↔ e x ∈ t) :
    _root_.OpenPartialHomeomorph s t := by
  classical
  let f : s → t := fun x ↦ if hx : e x ∈ t then ⟨e x, hx⟩ else ht
  let g : t → s := fun y ↦ if hy : e.symm y ∈ s then ⟨e.symm y, hy⟩ else hs
  have hf (x : s) (hx : (x : X) ∈ e.source) : (f x : Y) = e x := by
    dsimp [f]
    rw [dif_pos ((h x hx).mp x.property)]
  have hg (y : t) (hy : (y : Y) ∈ e.target) : (g y : X) = e.symm y := by
    dsimp [g]
    rw [dif_pos ((h (e.symm y) (e.map_target hy)).mpr (by
      rw [e.right_inv hy]; exact y.property))]
  exact {
    toFun := f
    invFun := g
    source := Subtype.val ⁻¹' e.source
    target := Subtype.val ⁻¹' e.target
    map_source' := fun x hx ↦ by change (f x : Y) ∈ e.target; rw [hf x hx]; exact e.map_source hx
    map_target' := fun y hy ↦ by change (g y : X) ∈ e.source; rw [hg y hy]; exact e.map_target hy
    left_inv' := fun x hx ↦ by
      apply Subtype.ext
      rw [hg (f x) (by rw [hf x hx]; exact e.map_source hx), hf x hx, e.left_inv hx]
    right_inv' := fun y hy ↦ by
      apply Subtype.ext
      rw [hf (g y) (by rw [hg y hy]; exact e.map_target hy), hg y hy, e.right_inv hy]
    open_source := e.open_source.preimage continuous_subtype_val
    open_target := e.open_target.preimage continuous_subtype_val
    continuousOn_toFun := by
      have hc : ContinuousOn (fun x : s ↦ e (x : X)) (Subtype.val ⁻¹' e.source) :=
        e.continuousOn.comp continuous_subtype_val.continuousOn (fun _ hx ↦ hx)
      exact IsInducing.subtypeVal.continuousOn_iff.mpr (hc.congr (fun x hx ↦ hf x hx))
    continuousOn_invFun := by
      have hc : ContinuousOn (fun y : t ↦ e.symm (y : Y)) (Subtype.val ⁻¹' e.target) :=
        e.continuousOn_symm.comp continuous_subtype_val.continuousOn (fun _ hy ↦ hy)
      exact IsInducing.subtypeVal.continuousOn_iff.mpr (hc.congr (fun y hy ↦ hg y hy)) }

@[simp]
theorem restrictSubtypes_source (e : _root_.OpenPartialHomeomorph X Y) (s : Set X) (t : Set Y)
    (hs : s) (ht : t) (h : ∀ x ∈ e.source, x ∈ s ↔ e x ∈ t) :
    (restrictSubtypes e s t hs ht h).source = Subtype.val ⁻¹' e.source := rfl

@[simp]
theorem restrictSubtypes_target (e : _root_.OpenPartialHomeomorph X Y) (s : Set X) (t : Set Y)
    (hs : s) (ht : t) (h : ∀ x ∈ e.source, x ∈ s ↔ e x ∈ t) :
    (restrictSubtypes e s t hs ht h).target = Subtype.val ⁻¹' e.target := rfl

theorem restrictSubtypes_apply (e : _root_.OpenPartialHomeomorph X Y) (s : Set X) (t : Set Y)
    (hs : s) (ht : t) (h : ∀ x ∈ e.source, x ∈ s ↔ e x ∈ t)
    (x : s) (hx : (x : X) ∈ e.source) :
    (restrictSubtypes e s t hs ht h x : Y) = e x := by
  classical
  change (if hy : e x ∈ t then (⟨e x, hy⟩ : t) else ht).val = e x
  rw [dif_pos ((h x hx).mp x.property)]

theorem restrictSubtypes_symm_apply (e : _root_.OpenPartialHomeomorph X Y) (s : Set X) (t : Set Y)
    (hs : s) (ht : t) (h : ∀ x ∈ e.source, x ∈ s ↔ e x ∈ t)
    (y : t) (hy : (y : Y) ∈ e.target) :
    ((restrictSubtypes e s t hs ht h).symm y : X) = e.symm y := by
  classical
  change (if hx : e.symm y ∈ s then (⟨e.symm y, hx⟩ : s) else hs).val = e.symm y
  rw [dif_pos ((h (e.symm y) (e.map_target hy)).mpr (by rw [e.right_inv hy]; exact y.property))]

end DifferentialGeometry.Topology.OpenPartialHomeomorph
