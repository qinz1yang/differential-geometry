/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.CurveCrossingExtrema
import DifferentialGeometry.External.CanonicalTopology.Topology.LoopSpace.Basic
import Mathlib.Topology.Covering.AddCircle

open Set Topology Filter

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem HasPLCurveCrossingOnAt.not_isLocalExtr_lift
    {S A B : Set E} {Y : Type*} [TopologicalSpace Y] {p : ℝ → A} {t : ℝ}
    (hc : HasPLCurveCrossingOnAt S A B (p t)) (hAS : A ⊆ S)
    (ρ : S → Y) (hρ : Continuous ρ) (hρopen : IsOpenMap ρ)
    (hp : IsLocalHomeomorph p) (q : ℝ → Y) (hq : IsLocalHomeomorph q)
    (F : ℝ → ℝ) (hF : Continuous F)
    (hlift : ∀ u, ρ ⟨p u, hAS (p u).property⟩ = q (F u))
    (hB : ∀ y : S, ρ y = q (F t) ↔ (y : E) ∈ B) : ¬ IsLocalExtr F t := by
  classical
  let L := hq.localInverseAt (F t)
  let x : S := ⟨p t, hAS (p t).property⟩
  let f : E → ℝ := Function.extend Subtype.val (fun y : S => L (ρ y)) (fun _ => 0)
  have hfeq (y : S) : f y = L (ρ y) :=
    Subtype.val_injective.extend_apply _ _ y
  have hxρ : ρ x = q (F t) := hlift t
  have hxL : ρ x ∈ L.source := by
    rw [hxρ]
    exact hq.apply_self_mem_localInverseAt_source
  have hxval : f x = F t := by
    rw [hfeq, hxρ]
    exact hq.localInverseAt_apply_self
  have hO : IsOpen (ρ ⁻¹' L.source) := L.open_source.preimage hρ
  obtain ⟨U, hU, hUeq⟩ := isOpen_induced_iff.mp hO
  have hUS : ∀ y : S, (y : E) ∈ U ↔ ρ y ∈ L.source := by
    intro y
    exact Set.ext_iff.mp hUeq y
  have hxU : (x : E) ∈ U := (hUS x).mpr hxL
  have hf : ContinuousOn f (S ∩ U) := by
    apply continuousOn_iff_continuous_domRestrict.mpr
    have hi : Continuous (fun y : (S ∩ U : Set E) => (⟨y, y.property.1⟩ : S)) :=
      continuous_subtype_val.subtype_mk _
    have hρi := hρ.comp hi
    have hLi := L.continuousOn.comp_continuous hρi
      (fun y => (hUS ⟨y, y.property.1⟩).mp y.property.2)
    convert hLi using 1
    ext y
    exact hfeq ⟨y, y.property.1⟩
  have hlevel : ∀ y ∈ S ∩ U, f y = f x ↔ y ∈ B := by
    intro y hy
    rw [hfeq ⟨y, hy.1⟩, hxval]
    have hyL := (hUS ⟨y, hy.1⟩).mp hy.2
    constructor
    · intro heq
      apply (hB ⟨y, hy.1⟩).mp
      have hqeq := congrArg q heq
      rw [hq.apply_localInverseAt_of_mem hyL] at hqeq
      exact hqeq
    · intro hyB
      rw [(hB ⟨y, hy.1⟩).mpr hyB]
      exact hq.localInverseAt_apply_self
  have hmap : Filter.map f (𝓝[S] (x : E)) = 𝓝 (f x) := by
    rw [← map_nhds_subtype_val x, Filter.map_map]
    have hcomp : f ∘ Subtype.val = L ∘ ρ := funext hfeq
    rw [hcomp, ← Filter.map_map, hρopen.map_nhds_eq hρ.continuousAt,
      L.map_nhds_eq hxL, hfeq]
  have hnot : ¬ IsLocalExtrOn f A (x : E) :=
    hc.not_isLocalExtrOn_of_level hU hxU hf hlevel hmap.ge
  intro hext
  have hagree : (fun u => f (p u)) =ᶠ[𝓝 t] F := by
    have htarget : L.target ∈ 𝓝 (F t) :=
      L.open_target.mem_nhds hq.self_mem_localInverseAt_target
    filter_upwards [hF.continuousAt.preimage_mem_nhds htarget] with u hu
    rw [hfeq ⟨p u, hAS (p u).property⟩, hlift]
    have hright := L.right_inv hu
    simpa only [L, hq.localInverseAt_symm] using hright
  have hext' : IsLocalExtr (fun u => f (p u)) t :=
    hext.congr hagree.symm
  have hparam : Filter.map (fun u : ℝ => (p u : E)) (𝓝 t) = 𝓝[A] (x : E) := by
    rw [← map_nhds_subtype_val (p t), ← hp.map_nhds_eq t, Filter.map_map]
    rfl
  apply hnot
  rw [IsLocalExtrOn, ← hparam]
  exact hext'

theorem HasPLCurveCrossingOnAt.not_isLocalExtr_longitude_lift
    {M Q X J : Set E} (φ : (M × Q) ≃ₜ X) (hJX : J ⊆ X)
    (eJ : loopCircle ≃ₜ J) (eQ : loopCircle ≃ₜ Q)
    (F : ℝ → ℝ) (hF : Continuous F)
    (hlift : ∀ u : ℝ, eQ (F u : loopCircle) =
      (φ.symm ⟨eJ (u : loopCircle), hJX (eJ (u : loopCircle)).property⟩).2)
    {t : ℝ} {q : Q} (ht : eQ (F t : loopCircle) = q)
    (hc : HasPLCurveCrossingOnAt X J
      (Set.range (fun m : M => (φ (m, q) : E))) (eJ (t : loopCircle))) :
    ¬ IsLocalExtr F t := by
  let ρ : X → Q := fun y => (φ.symm y).2
  apply hc.not_isLocalExtr_lift hJX ρ (continuous_snd.comp φ.symm.continuous)
    (isOpenMap_snd.comp φ.symm.isOpenMap)
    (eJ.isLocalHomeomorph.comp (AddCircle.isLocalHomeomorph_coe (1 : ℝ)))
    (fun u : ℝ => eQ (u : loopCircle))
    (eQ.isLocalHomeomorph.comp (AddCircle.isLocalHomeomorph_coe (1 : ℝ)))
    F hF (fun u => (hlift u).symm)
  intro y
  rw [ht]
  constructor
  · intro hy
    refine ⟨(φ.symm y).1, ?_⟩
    have heq : φ ((φ.symm y).1, q) = y := by
      rw [← hy]
      exact φ.apply_symm_apply y
    exact congrArg Subtype.val heq
  · rintro ⟨m, hm⟩
    have heq : φ (m, q) = y := Subtype.ext hm
    have hcoord := congrArg (fun z : X => (φ.symm z).2) heq
    simpa only [φ.symm_apply_apply] using hcoord.symm

end DifferentialGeometry.Topology.PiecewiseLinear
