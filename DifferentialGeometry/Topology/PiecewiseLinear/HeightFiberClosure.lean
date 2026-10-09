/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.Connected.CompactIntersection
import DifferentialGeometry.Topology.Connected.Dense
import DifferentialGeometry.Topology.PiecewiseLinear.HeightSublevelConnected

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem mem_closure_inter_lt_of_notMem_vertices
    (K : Geometry.SimplicialComplex ℝ E) (ℓ : E →L[ℝ] ℝ) (hinj : InjOn ℓ K.vertices)
    {x : E} (hx : x ∈ K.space) (hxv : x ∉ K.vertices) :
    x ∈ closure (K.space ∩ {y | ℓ y < ℓ x}) := by
  obtain ⟨s, hs, hxs⟩ := exists_face_mem_openSimplex K hx
  have hverts (v : E) (hv : v ∈ s) : v ∈ K.vertices :=
    K.down_closed hs (Finset.singleton_subset_iff.mpr hv) (Finset.singleton_nonempty v)
  have hnotconst : ¬ ∀ v ∈ s, ℓ v = ℓ x := by
    intro hconst
    obtain ⟨v, hv⟩ := K.nonempty_of_mem_faces hs
    have hsub : (s : Set E) ⊆ {v} := fun w hw =>
      hinj (hverts w hw) (hverts v hv) ((hconst w hw).trans (hconst v hv).symm)
    have hxv' : x = v := convexHull_min hsub (convex_singleton v)
      (openSimplex_subset_convexHull s hxs)
    exact hxv (hxv' ▸ hverts v hv)
  obtain ⟨v, hv, hvlt⟩ : ∃ v ∈ s, ℓ v < ℓ x := by
    by_contra h
    push Not at h
    exact hnotconst ((affineMap_eq_iff_of_mem_openSimplex_of_ge
      ℓ.toLinearMap.toAffineMap hxs h).mp rfl)
  have hsegment : openSegment ℝ x v ⊆ K.space ∩ {y | ℓ y < ℓ x} := by
    intro y hy
    refine ⟨K.convexHull_subset_space hs ((convex_convexHull ℝ (s : Set E)).segment_subset
      (openSimplex_subset_convexHull s hxs) (subset_convexHull ℝ _ hv)
      (openSegment_subset_segment ℝ x v hy)), ?_⟩
    obtain ⟨a, b, ha, hb, hab, rfl⟩ := hy
    change ℓ (a • x + b • v) < ℓ x
    rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
    calc
      a * ℓ x + b * ℓ v < a * ℓ x + b * ℓ x := add_lt_add_of_le_of_lt le_rfl (mul_lt_mul_of_pos_left
          hvlt hb)
      _ = ℓ x := by rw [← add_mul, hab, one_mul]
  exact closure_mono hsegment (segment_subset_closure_openSegment (left_mem_segment ℝ x v))

theorem closure_inter_lt_eq_inter_le_of_preconnected
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (ℓ : E →L[ℝ] ℝ) (hinj : InjOn ℓ K.vertices) (r : ℝ)
    (hconn : IsPreconnected (K.space ∩ {x | ℓ x ≤ r}))
    (hne : (K.space ∩ {x | ℓ x ≤ r}).Nontrivial) :
    closure (K.space ∩ {x | ℓ x < r}) = K.space ∩ {x | ℓ x ≤ r} := by
  have hcompact : IsCompact K.space := by
    rw [Geometry.SimplicialComplex.space, biUnion_eq_iUnion]
    exact isCompact_iUnion fun s : K.faces => s.1.finite_toSet.isCompact_convexHull ℝ
  apply Subset.antisymm
  · exact closure_minimal (fun _ hx => ⟨hx.1, le_of_lt (show ℓ _ < r from hx.2)⟩)
      (hcompact.isClosed.inter (isClosed_le ℓ.continuous continuous_const))
  · have hdense := Topology.IsPreconnected.subset_closure_sdiff_finite hconn hne
      (SimplicialComplex.finite_vertices K)
    apply hdense.trans
    apply closure_minimal _ isClosed_closure
    rintro x ⟨⟨hxK, hxr⟩, hxv⟩
    rcases lt_or_eq_of_le (show ℓ x ≤ r from hxr) with hxlt | hxeq
    · exact subset_closure ⟨hxK, hxlt⟩
    · have h := mem_closure_inter_lt_of_notMem_vertices K ℓ hinj hxK hxv
      rwa [hxeq] at h

theorem closure_halfSpaces_of_heightIndex_eq_zero [FiniteDimensional ℝ E]
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsPLSphere 2 K.space) (hdimE : Module.finrank ℝ E = 3)
    (ℓ : E →L[ℝ] ℝ) (hℓ : ℓ ≠ 0) (hinj : InjOn ℓ K.vertices)
    (hzero : heightIndex K.space ℓ = 0) (r : ℝ)
    (hbelow : ∃ y ∈ K.space, ℓ y < r) (habove : ∃ z ∈ K.space, r < ℓ z) :
    closure (K.space ∩ {x | ℓ x < r}) = K.space ∩ {x | ℓ x ≤ r} ∧
      closure (K.space ∩ {x | r < ℓ x}) = K.space ∩ {x | r ≤ ℓ x} := by
  have hstrict (t : ℝ) := isPreconnected_halfSpaces_of_heightIndex_eq_zero K hK hdimE ℓ hℓ hinj
      hzero t
  have hle := Topology.isPreconnected_inter_le_of_isCompact_of_forall_inter_lt
    hK.isPolyhedron.isCompact ℓ.continuous.continuousOn r (fun t _ => (hstrict t).1)
  have hge := Topology.isPreconnected_inter_ge_of_isCompact_of_forall_inter_gt
    hK.isPolyhedron.isCompact ℓ.continuous.continuousOn r (fun t _ => (hstrict t).2)
  obtain ⟨y, hy, hyr⟩ := hbelow
  obtain ⟨z, hz, hrz⟩ := habove
  obtain ⟨x, hx, hxr⟩ := hK.isConnected.isPreconnected.intermediate_value hy hz
    ℓ.continuous.continuousOn ⟨hyr.le, hrz.le⟩
  have hnele : (K.space ∩ {w | ℓ w ≤ r}).Nontrivial :=
    ⟨y, ⟨hy, hyr.le⟩, x, ⟨hx, hxr.le⟩, fun h => hyr.ne (h ▸ hxr)⟩
  refine ⟨closure_inter_lt_eq_inter_le_of_preconnected K ℓ hinj r hle hnele, ?_⟩
  have hinj' : InjOn (-ℓ) K.vertices := fun u hu v hv huv => hinj hu hv (neg_injective huv)
  have hge' : IsPreconnected (K.space ∩ {w | (-ℓ) w ≤ -r}) := by
    simpa only [neg_apply, neg_le_neg_iff] using hge
  have hnege' : (K.space ∩ {w | (-ℓ) w ≤ -r}).Nontrivial := by
    refine ⟨z, ⟨hz, neg_le_neg hrz.le⟩, x, ⟨hx, neg_le_neg hxr.ge⟩, ?_⟩
    intro h
    exact hrz.ne (h ▸ hxr.symm)
  have h := closure_inter_lt_eq_inter_le_of_preconnected K (-ℓ) hinj' (-r) hge' hnege'
  simpa only [neg_apply, neg_lt_neg_iff, neg_le_neg_iff] using h

end DifferentialGeometry.Topology.PiecewiseLinear
