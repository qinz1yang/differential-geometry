/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.CurveCrossingLiftExtrema

open Set Topology Filter

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u v

local notation "E3" => EuclideanSpace ℝ (Fin 3)

theorem HasPLCurveCrossingOnAt.not_isLocalExtrOn_of_level_in_chart
    {M : Type*} [TopologicalSpace M] {S A B U : Set M} {x : M}
    (c : OpenPartialHomeomorph M E3) (hxc : x ∈ c.source) (hxA : x ∈ A)
    (hc : HasPLCurveCrossingOnAt (c '' (S ∩ c.source))
      (c '' (A ∩ c.source)) (c '' (B ∩ c.source)) (c x))
    {f : M → ℝ} (hU : IsOpen U) (hxU : x ∈ U) (hf : ContinuousOn f (S ∩ U))
    (hlevel : ∀ y ∈ S ∩ U, f y = f x ↔ y ∈ B)
    (hopen : 𝓝 (f x) ≤ Filter.map f (𝓝[S] x)) : ¬ IsLocalExtrOn f A x := by
  let V := c.target ∩ c.symm ⁻¹' U
  have hV : IsOpen V := c.isOpen_inter_preimage_symm hU
  have hxV : c x ∈ V := ⟨c.map_source hxc, by rwa [mem_preimage, c.left_inv hxc]⟩
  have hmem (Z : Set M) {z : E3} (hz : z ∈ c '' (Z ∩ c.source)) :
      c.symm z ∈ Z ∩ c.source := by
    obtain ⟨y, hy, rfl⟩ := hz
    rwa [c.left_inv hy.2]
  have htarget (Z : Set M) : c '' (Z ∩ c.source) ⊆ c.target := by
    rintro z ⟨y, hy, rfl⟩
    exact c.map_source hy.2
  have hfc : ContinuousOn (f ∘ c.symm) ((c '' (S ∩ c.source)) ∩ V) :=
    hf.comp (c.continuousOn_symm.mono (fun _ hz => hz.2.1))
      (fun _ hz => ⟨(hmem S hz.1).1, hz.2.2⟩)
  have hlevelc : ∀ z ∈ (c '' (S ∩ c.source)) ∩ V,
      (f ∘ c.symm) z = (f ∘ c.symm) (c x) ↔ z ∈ c '' (B ∩ c.source) := by
    intro z hz
    simp only [Function.comp_apply, c.left_inv hxc]
    rw [hlevel _ ⟨(hmem S hz.1).1, hz.2.2⟩]
    exact ⟨fun h => ⟨c.symm z, ⟨h, c.map_target hz.2.1⟩, c.right_inv hz.2.1⟩,
      fun h => (hmem B h).1⟩
  have hforward : Filter.map c (𝓝[S] x) = 𝓝[c '' (S ∩ c.source)] (c x) := by
    simpa only [inter_comm] using c.map_nhdsWithin_eq hxc S
  have hback : Filter.map c.symm (𝓝[c '' (S ∩ c.source)] (c x)) = 𝓝[S] x := by
    rw [← hforward, Filter.map_map]
    have hcomp : (c.symm ∘ c) =ᶠ[𝓝[S] x] id :=
      (c.eventually_left_inverse hxc).filter_mono nhdsWithin_le_nhds
    rw [Filter.map_congr hcomp, Filter.map_id]
  have hopenc : 𝓝 ((f ∘ c.symm) (c x)) ≤
      Filter.map (f ∘ c.symm) (𝓝[c '' (S ∩ c.source)] (c x)) := by
    rw [← Filter.map_map, hback, Function.comp_apply, c.left_inv hxc]
    exact hopen
  intro hext
  apply hc.not_isLocalExtrOn_of_level hV hxV hfc hlevelc hopenc
  have hext' : IsLocalExtrOn f A (c.symm (c x)) := by rwa [c.left_inv hxc]
  exact hext'.comp_continuousOn c.symm (fun _ hz => (hmem A hz).1)
    (c.continuousOn_symm.mono (htarget A)) ⟨x, ⟨hxA, hxc⟩, rfl⟩

theorem HasPLCurveCrossingOnAt.not_isLocalExtr_lift_in_chart
    {M : Type u} {Y : Type v} [TopologicalSpace M] [TopologicalSpace Y]
    {S A B : Set M} {p : ℝ → A} {t : ℝ}
    (c : OpenPartialHomeomorph M E3) (hpc : (p t : M) ∈ c.source)
    (hc : HasPLCurveCrossingOnAt (c '' (S ∩ c.source))
      (c '' (A ∩ c.source)) (c '' (B ∩ c.source)) (c (p t)))
    (hAS : A ⊆ S) (ρ : S → Y) (hρ : Continuous ρ) (hρopen : IsOpenMap ρ)
    (hp : IsLocalHomeomorph p) (q : ℝ → Y) (hq : IsLocalHomeomorph q)
    (F : ℝ → ℝ) (hF : Continuous F)
    (hlift : ∀ u, ρ ⟨p u, hAS (p u).property⟩ = q (F u))
    (hB : ∀ y : S, ρ y = q (F t) ↔ (y : M) ∈ B) : ¬ IsLocalExtr F t := by
  classical
  let L := hq.localInverseAt (F t)
  let x : S := ⟨p t, hAS (p t).property⟩
  let f : M → ℝ := Function.extend Subtype.val (fun y : S => L (ρ y)) (fun _ => 0)
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
  have hUS : ∀ y : S, (y : M) ∈ U ↔ ρ y ∈ L.source := by
    intro y
    exact Set.ext_iff.mp hUeq y
  have hxU : (x : M) ∈ U := (hUS x).mpr hxL
  have hf : ContinuousOn f (S ∩ U) := by
    apply continuousOn_iff_continuous_domRestrict.mpr
    have hi : Continuous (fun y : (S ∩ U : Set M) => (⟨y, y.property.1⟩ : S)) :=
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
  have hmap : Filter.map f (𝓝[S] (x : M)) = 𝓝 (f x) := by
    rw [← map_nhds_subtype_val x, Filter.map_map]
    have hcomp : f ∘ Subtype.val = L ∘ ρ := funext hfeq
    rw [hcomp, ← Filter.map_map, hρopen.map_nhds_eq hρ.continuousAt,
      L.map_nhds_eq hxL, hfeq]
  have hnot : ¬ IsLocalExtrOn f A (x : M) :=
    HasPLCurveCrossingOnAt.not_isLocalExtrOn_of_level_in_chart c hpc (p t).property hc
      hU hxU hf hlevel hmap.ge
  intro hext
  have hagree : (fun u => f (p u)) =ᶠ[𝓝 t] F := by
    have htarget : L.target ∈ 𝓝 (F t) :=
      L.open_target.mem_nhds hq.self_mem_localInverseAt_target
    filter_upwards [hF.continuousAt.preimage_mem_nhds htarget] with u hu
    rw [hfeq ⟨p u, hAS (p u).property⟩, hlift]
    have hright := L.right_inv hu
    simpa only [L, hq.localInverseAt_symm] using hright
  have hext' : IsLocalExtr (fun u => f (p u)) t := hext.congr hagree.symm
  have hparam : Filter.map (fun u : ℝ => (p u : M)) (𝓝 t) = 𝓝[A] (x : M) := by
    rw [← map_nhds_subtype_val (p t), ← hp.map_nhds_eq t, Filter.map_map]
    rfl
  apply hnot
  rw [IsLocalExtrOn, ← hparam]
  exact hext'

end DifferentialGeometry.Topology.PiecewiseLinear
