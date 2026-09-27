/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.CrossingFiber
import DifferentialGeometry.Topology.PiecewiseLinear.HeightRegularity

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem isPreconnected_inter_lt_of_circle_height_section_encard_le_two
    (L : Geometry.SimplicialComplex ℝ E) (hL : IsPLSphere 1 L.space)
    (ℓ : E →L[ℝ] ℝ) (r : ℝ) (havoid : ∀ v ∈ L.vertices, ℓ v ≠ r)
    (hcard : (L.space ∩ {x | ℓ x = r}).encard ≤ 2) :
    IsPreconnected (L.space ∩ {x | ℓ x < r}) := by
  rcases height_section_eq_empty_or_pair_of_encard_le_two L hL ℓ r havoid hcard with
    hempty | ⟨a, b, hab, hpair⟩
  · have hcover : L.space ⊆ {x | ℓ x < r} ∪ {x | r < ℓ x} := by
      intro x hx
      have hne : ℓ x ≠ r := fun heq => by
        have hz : x ∈ L.space ∩ ℓ ⁻¹' ({r} : Set ℝ) := ⟨hx, heq⟩
        exact hempty.subset hz
      exact lt_or_gt_of_ne hne
    have hsplit := IsPreconnected.subset_or_subset
      (isOpen_lt ℓ.continuous continuous_const) (isOpen_lt continuous_const ℓ.continuous)
      (disjoint_left.mpr fun x hx hy => lt_asymm (show ℓ x < r from hx) (show r < ℓ x from hy))
          hcover hL.isConnected.isPreconnected
    rcases hsplit with hbelow | habove
    · rw [inter_eq_left.mpr hbelow]
      exact hL.isConnected.isPreconnected
    · have heq : L.space ∩ {x | ℓ x < r} = ∅ := by
        apply eq_empty_iff_forall_notMem.mpr
        rintro x ⟨hx, hxr⟩
        exact lt_asymm (show ℓ x < r from hxr) (show r < ℓ x from habove hx)
      rw [heq]
      exact isPreconnected_empty
  · have hpair' : L.space ∩ {x | ℓ x = r} = {a, b} := hpair
    have ha : a ∈ L.space ∩ ℓ ⁻¹' ({r} : Set ℝ) :=
      hpair.symm.subset (Set.mem_insert a {b})
    obtain ⟨hneg, hpos⟩ := exists_lt_and_gt_of_mem_height_section_of_avoids_vertices L ℓ r havoid ha
    obtain ⟨γ, δ, -, hδ, -, -, hδ0, hδ1⟩ :=
      exists_isPLHomeomorphOn_Icc_inter_of_fiber_pair hL ℓ.continuous.continuousOn hpair' hab hpos
          hneg
    have hconn := hδ.isConnected_sdiff_endpoints (show (0 : ℝ) < 1 by norm_num)
    rw [hδ0, hδ1] at hconn
    have heq : (L.space ∩ {x | ℓ x ≤ r}) \ {a, b} = L.space ∩ {x | ℓ x < r} := by
      ext x
      constructor
      · rintro ⟨⟨hxL, hxle⟩, hxends⟩
        exact ⟨hxL, lt_of_le_of_ne hxle (fun heq => hxends (hpair'.subset ⟨hxL, heq⟩))⟩
      · rintro ⟨hxL, hxlt⟩
        have hxlt' : ℓ x < r := hxlt
        exact ⟨⟨hxL, hxlt'.le⟩, fun hxends => hxlt'.ne (hpair'.symm.subset hxends).2⟩
    rw [heq] at hconn
    exact hconn.isPreconnected

theorem isPreconnected_inter_gt_of_circle_height_section_encard_le_two
    (L : Geometry.SimplicialComplex ℝ E) (hL : IsPLSphere 1 L.space)
    (ℓ : E →L[ℝ] ℝ) (r : ℝ) (havoid : ∀ v ∈ L.vertices, ℓ v ≠ r)
    (hcard : (L.space ∩ {x | ℓ x = r}).encard ≤ 2) :
    IsPreconnected (L.space ∩ {x | r < ℓ x}) := by
  have havoid' : ∀ v ∈ L.vertices, (-ℓ) v ≠ -r := by
    intro v hv heq
    exact havoid v hv (neg_injective heq)
  have hcard' : (L.space ∩ {x | (-ℓ) x = -r}).encard ≤ 2 := by
    simpa only [neg_apply, neg_inj] using hcard
  simpa only [neg_apply, neg_lt_neg_iff] using
    isPreconnected_inter_lt_of_circle_height_section_encard_le_two L hL (-ℓ) (-r) havoid' hcard'

theorem isPreconnected_geometricLink_halfSpaces_of_notMem_heightSingularPoints
    [DecidableEq E] (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsPLSphere 2 K.space) (ℓ : E →L[ℝ] ℝ) (hinj : InjOn ℓ K.vertices)
    {p : E} (hp : {p} ∈ K.faces) (hregular : p ∉ heightSingularPoints K.space ℓ) :
    IsPreconnected ((SimplicialComplex.geometricLink K {p}).space ∩ {x | ℓ x < ℓ p}) ∧
      IsPreconnected ((SimplicialComplex.geometricLink K {p}).space ∩ {x | ℓ p < ℓ x}) := by
  have hlink : IsPLSphere 1 (SimplicialComplex.geometricLink K {p}).space :=
    isPLSphere_geometricLink_of_isPLSphere K hK hp
  have havoid : ∀ v ∈ (SimplicialComplex.geometricLink K {p}).vertices, ℓ v ≠ ℓ p := by
    intro v hv heq
    have hvK : v ∈ K.vertices := SimplicialComplex.geometricLink_le K {p} hv
    have hvp : v = p := hinj hvK hp heq
    exact notMem_geometricLink_space K
      (hvp ▸ (SimplicialComplex.geometricLink K {p}).vertices_subset_space hv)
  have hcard : ((SimplicialComplex.geometricLink K {p}).space ∩ {x | ℓ x = ℓ p}).encard ≤ 2 :=
    encard_geometricLink_fiber_le_two_of_notMem_heightSingularPoints K hp ℓ.toLinearMap hregular
  exact ⟨isPreconnected_inter_lt_of_circle_height_section_encard_le_two _ hlink ℓ (ℓ p) havoid
      hcard,
    isPreconnected_inter_gt_of_circle_height_section_encard_le_two _ hlink ℓ (ℓ p) havoid hcard⟩

theorem isPreconnected_geometricLink_halfSpaces_of_heightIndex_eq_zero
    [DecidableEq E] (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsPLSphere 2 K.space) (hdimE : Module.finrank ℝ E = 3)
    (ℓ : E →L[ℝ] ℝ) (hℓ : ℓ ≠ 0) (hinj : InjOn ℓ K.vertices)
    (hzero : heightIndex K.space ℓ = 0) {p : E} (hp : {p} ∈ K.faces) :
    IsPreconnected ((SimplicialComplex.geometricLink K {p}).space ∩ {x | ℓ x < ℓ p}) ∧
      IsPreconnected ((SimplicialComplex.geometricLink K {p}).space ∩ {x | ℓ p < ℓ x}) := by
  apply isPreconnected_geometricLink_halfSpaces_of_notMem_heightSingularPoints K hK ℓ hinj hp
  rw [heightSingularPoints_eq_empty_of_heightIndex_eq_zero K hK hdimE ℓ hℓ hinj hzero]
  exact notMem_empty p

end DifferentialGeometry.Topology.PiecewiseLinear
