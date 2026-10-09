/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.CompactEmbeddingComplement
import DifferentialGeometry.Topology.PiecewiseLinear.DerivedNeighborhoodRay
import DifferentialGeometry.Topology.PiecewiseLinear.FrontierBoundary
import DifferentialGeometry.Topology.PiecewiseLinear.PseudoCell
import Mathlib.Topology.LocalAtTarget

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

section Coordinates

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem barycentricCoordinate_pos_of_mem_openSimplex {L : Geometry.SimplicialComplex ℝ E}
    {e : Finset E} (he : e ∈ L.faces) {x : E} (hx : x ∈ openSimplex e) {v : E} (hv : v ∈ e) :
    0 < barycentricCoordinate L v x := by
  have hxe := openSimplex_subset_convexHull e hx
  rw [barycentricCoordinate_eq L he hxe, ite_eq_left hv]
  exact (mem_openSimplex_self_iff (L.indep he) hxe).mp hx v hv

theorem barycentricCoordinate_eq_zero_of_notMem_vertices {L : Geometry.SimplicialComplex ℝ E}
    {x : E} (hx : x ∈ L.space) {v : E} (hv : v ∉ L.vertices) :
    barycentricCoordinate L v x = 0 := by
  obtain ⟨e, he, hxe⟩ := L.mem_space_iff.mp hx
  rw [barycentricCoordinate_eq L he hxe, ite_eq_right]
  intro hve
  exact hv (L.down_closed he (Finset.singleton_subset_iff.mpr hve) (Finset.singleton_nonempty v))

theorem sum_barycentricCoordinate {L : Geometry.SimplicialComplex ℝ E} [Finite L.faces] {x : E}
    (hx : x ∈ L.space) :
    ∑ v ∈ simplicialComplexVertices L, barycentricCoordinate L v x = 1 := by
  obtain ⟨e, he, hxe⟩ := L.mem_space_iff.mp hx
  have hsub : e ⊆ simplicialComplexVertices L := fun v hv =>
    (mem_simplicialComplexVertices L).mpr
      (L.down_closed he (Finset.singleton_subset_iff.mpr hv) (Finset.singleton_nonempty v))
  have hzero : ∀ v ∈ simplicialComplexVertices L, v ∉ e → barycentricCoordinate L v x = 0 :=
    fun v _ hve => by rw [barycentricCoordinate_eq L he hxe, ite_eq_right hve]
  rw [← Finset.sum_subset hsub hzero, ← sum_weights hxe]
  exact Finset.sum_congr rfl fun v hv => by rw [barycentricCoordinate_eq L he hxe, ite_eq_left hv]

theorem barycentricCoordinate_pos_of_forall_le {L : Geometry.SimplicialComplex ℝ E} {x : E}
    (hx : x ∈ L.space) {v : E}
    (hle : ∀ w, barycentricCoordinate L w x ≤ barycentricCoordinate L v x) :
    0 < barycentricCoordinate L v x := by
  obtain ⟨e, he, hxo⟩ := exists_face_mem_openSimplex L hx
  obtain ⟨w, hw⟩ := L.nonempty_of_mem_faces he
  exact (barycentricCoordinate_pos_of_mem_openSimplex he hxo hw).trans_le (hle w)

theorem barycentricCoordinate_add_smul {L : Geometry.SimplicialComplex ℝ E} {s : Finset E}
    (hs : s ∈ L.faces) {y z : E} (hy : y ∈ convexHull ℝ (s : Set E))
    (hz : z ∈ convexHull ℝ (s : Set E)) {α γ : ℝ} (hαγ : α + γ = 1)
    (hq : α • y + γ • z ∈ convexHull ℝ (s : Set E)) (v : E) :
    barycentricCoordinate L v (α • y + γ • z) =
      α * barycentricCoordinate L v y + γ * barycentricCoordinate L v z := by
  have key : ∀ u ∈ s, weights s (α • y + γ • z) u = α * weights s y u + γ * weights s z u := by
    refine weights_eq (L.indep hs) hq ?_ ?_
    · rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, sum_weights hy,
        sum_weights hz, mul_one, mul_one, hαγ]
    · simp_rw [add_smul, mul_smul]
      rw [Finset.sum_add_distrib, ← Finset.smul_sum, ← Finset.smul_sum, sum_weights_smul hy,
        sum_weights_smul hz]
  rw [barycentricCoordinate_eq L hs hq, barycentricCoordinate_eq L hs hy,
    barycentricCoordinate_eq L hs hz]
  by_cases hv : v ∈ s
  · rw [ite_eq_left hv, ite_eq_left hv, ite_eq_left hv, key v hv]
  · rw [ite_eq_right hv, ite_eq_right hv, ite_eq_right hv, mul_zero, mul_zero, add_zero]

theorem add_smul_mem_convexHull_of_barycentricCoordinate_nonneg
    {L : Geometry.SimplicialComplex ℝ E} {s : Finset E} (hs : s ∈ L.faces) {y z : E}
    (hy : y ∈ convexHull ℝ (s : Set E)) (hz : z ∈ convexHull ℝ (s : Set E)) {α γ : ℝ}
    (hαγ : α + γ = 1)
    (hnonneg : ∀ u ∈ s,
      0 ≤ α * barycentricCoordinate L u y + γ * barycentricCoordinate L u z) :
    α • y + γ • z ∈ convexHull ℝ (s : Set E) := by
  have h₀ : ∀ u ∈ s, 0 ≤ α * weights s y u + γ * weights s z u := fun u hu => by
    have h := hnonneg u hu
    rwa [barycentricCoordinate_eq L hs hy, barycentricCoordinate_eq L hs hz, ite_eq_left hu,
      ite_eq_left hu] at h
  have h₁ : ∑ u ∈ s, (α * weights s y u + γ * weights s z u) = 1 := by
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, sum_weights hy,
      sum_weights hz, mul_one, mul_one, hαγ]
  have h₂ : ∑ u ∈ s, (α * weights s y u + γ * weights s z u) • u = α • y + γ • z := by
    simp_rw [add_smul, mul_smul]
    rw [Finset.sum_add_distrib, ← Finset.smul_sum, ← Finset.smul_sum, sum_weights_smul hy,
      sum_weights_smul hz]
  exact mem_convexHull_iff_exists_weights.mpr
    ⟨fun u => α * weights s y u + γ * weights s z u, h₀, h₁, h₂⟩

open Classical in
theorem barycentricCoordinate_vertex_of_mem {L : Geometry.SimplicialComplex ℝ E} {s : Finset E}
    (hs : s ∈ L.faces) {w : E} (hw : w ∈ s) (v : E) :
    barycentricCoordinate L v w = if v = w then 1 else 0 := by
  have hwc : w ∈ convexHull ℝ (s : Set E) := subset_convexHull ℝ _ (Finset.mem_coe.mpr hw)
  have key := weights_eq (L.indep hs) hwc (w := fun u => if u = w then (1 : ℝ) else 0)
    (by rw [Finset.sum_ite_eq' s w]; simp [hw])
    (by simp only [ite_smul, one_smul, zero_smul]; rw [Finset.sum_ite_eq' s w]; simp [hw])
  rw [barycentricCoordinate_eq L hs hwc]
  by_cases hv : v ∈ s
  · rw [ite_eq_left hv, key v hv]
  · rw [ite_eq_right hv, ite_eq_right fun h : v = w => hv (h ▸ hw)]

open Classical in
theorem barycentricCoordinate_subcomplexBarycentricProjection
    (L L₀ : Geometry.SimplicialComplex ℝ E) [Finite L.faces] {x : E} (hx : x ∈ L.space)
    (hm : 0 < subcomplexBarycentricMass L L₀ x) (v : E) :
    barycentricCoordinate L v (subcomplexBarycentricProjection L L₀ x) =
      if v ∈ L₀.vertices then
        (subcomplexBarycentricMass L L₀ x)⁻¹ * barycentricCoordinate L v x else 0 := by
  obtain ⟨e, he, hxe⟩ := L.mem_space_iff.mp hx
  have hp : subcomplexBarycentricProjection L L₀ x ∈ convexHull ℝ (e : Set E) :=
    convexHull_mono (Finset.coe_subset.mpr (Finset.filter_subset _ _))
      (subcomplexBarycentricProjection_mem_convexHull_filter L L₀ he hxe hm)
  rw [barycentricCoordinate_eq L he hp, barycentricCoordinate_eq L he hxe]
  by_cases hve : v ∈ e
  · rw [ite_eq_left hve, ite_eq_left hve, weights_subcomplexBarycentricProjection L L₀ he hxe hm hve]
    by_cases hv₀ : v ∈ L₀.vertices
    · rw [ite_eq_left (Finset.mem_filter.mpr ⟨hve, hv₀⟩), ite_eq_left hv₀]
    · rw [ite_eq_right fun h => hv₀ (Finset.mem_filter.mp h).2, ite_eq_right hv₀]
  · rw [ite_eq_right hve, ite_eq_right hve, mul_zero, ite_self]

open Classical in
theorem subcomplexBarycentricMass_eq_mul_of_barycentricCoordinate_eq_mul
    (L L₀ : Geometry.SimplicialComplex ℝ E) [Finite L.faces] {x y : E} {c : ℝ}
    (h : ∀ v ∈ L₀.vertices, barycentricCoordinate L v y = c * barycentricCoordinate L v x) :
    subcomplexBarycentricMass L L₀ y = c * subcomplexBarycentricMass L L₀ x := by
  rw [subcomplexBarycentricMass, subcomplexBarycentricMass, Finset.mul_sum]
  exact Finset.sum_congr rfl fun v hv => h v (Finset.mem_filter.mp hv).2

open Classical in
theorem subcomplexBarycentricProjection_eq_of_barycentricCoordinate_eq_mul
    (L L₀ : Geometry.SimplicialComplex ℝ E) [Finite L.faces] {x y : E} {c : ℝ} (hc : c ≠ 0)
    (h : ∀ v ∈ L₀.vertices, barycentricCoordinate L v y = c * barycentricCoordinate L v x) :
    subcomplexBarycentricProjection L L₀ y = subcomplexBarycentricProjection L L₀ x := by
  have hmoment :
      subcomplexBarycentricMoment L L₀ y = c • subcomplexBarycentricMoment L L₀ x := by
    rw [subcomplexBarycentricMoment, subcomplexBarycentricMoment, Finset.smul_sum]
    refine Finset.sum_congr rfl fun v hv => ?_
    rw [h v (Finset.mem_filter.mp hv).2, mul_smul]
  rw [subcomplexBarycentricProjection, subcomplexBarycentricProjection,
    subcomplexBarycentricMass_eq_mul_of_barycentricCoordinate_eq_mul L L₀ h, hmoment, smul_smul,
    mul_inv, mul_comm c⁻¹, mul_assoc, inv_mul_cancel₀ hc, mul_one]

end Coordinates

section Neighborhood

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

open Classical in
theorem exists_barycentricCoordinate_le_of_mem_derivedNeighborhood
    {A K : Geometry.SimplicialComplex ℝ E} {x : E} (hx : x ∈ (derivedNeighborhood A K).space) :
    ∃ v ∈ (barycentricSubdivision K).vertices, ∀ w,
      barycentricCoordinate (barycentricSubdivision A) w x ≤
        barycentricCoordinate (barycentricSubdivision A) v x := by
  obtain ⟨e, he, hf, hxe⟩ := exists_faceNeighborhood_of_mem_derivedNeighborhood hx
  obtain ⟨hxc, v, hvf, hmax⟩ := (mem_faceNeighborhood_space_iff
    ((barycentricSubdivision A).indep he) (Finset.filter_subset _ _) hf).mp hxe
  obtain ⟨hve, hvK⟩ := Finset.mem_filter.mp hvf
  refine ⟨v, hvK, fun w => ?_⟩
  rw [barycentricCoordinate_eq _ he hxc, barycentricCoordinate_eq _ he hxc, ite_eq_left hve]
  by_cases hwe : w ∈ e
  · rw [ite_eq_left hwe]
    exact hmax w hwe
  · rw [ite_eq_right hwe]
    exact weights_nonneg hxc hve

open Classical in
theorem mem_derivedNeighborhood_of_barycentricCoordinate_le
    {A K : Geometry.SimplicialComplex ℝ E} {x : E} (hx : x ∈ (barycentricSubdivision A).space)
    {v : E} (hv : v ∈ (barycentricSubdivision K).vertices)
    (hle : ∀ w ∉ (barycentricSubdivision K).vertices,
      barycentricCoordinate (barycentricSubdivision A) w x ≤
        barycentricCoordinate (barycentricSubdivision A) v x) :
    x ∈ (derivedNeighborhood A K).space := by
  obtain ⟨e, he, hxo⟩ := exists_face_mem_openSimplex _ hx
  have hxe := openSimplex_subset_convexHull e hxo
  obtain ⟨u, hu, humax⟩ := e.exists_max_image (weights e x)
    ((barycentricSubdivision A).nonempty_of_mem_faces he)
  have key : ∃ v' ∈ e.filter (fun w => w ∈ (barycentricSubdivision K).vertices),
      ∀ w ∈ e, weights e x w ≤ weights e x v' := by
    by_cases huK : u ∈ (barycentricSubdivision K).vertices
    · exact ⟨u, Finset.mem_filter.mpr ⟨hu, huK⟩, humax⟩
    · have h1 := hle u huK
      rw [barycentricCoordinate_eq _ he hxe, barycentricCoordinate_eq _ he hxe, ite_eq_left hu] at h1
      by_cases hve : v ∈ e
      · rw [ite_eq_left hve] at h1
        exact ⟨v, Finset.mem_filter.mpr ⟨hve, hv⟩, fun w hw => (humax w hw).trans h1⟩
      · rw [ite_eq_right hve] at h1
        exact absurd h1 (not_le.mpr ((mem_openSimplex_self_iff
          ((barycentricSubdivision A).indep he) hxe).mp hxo u hu))
  obtain ⟨v', hv'f, hv'max⟩ := key
  exact faceNeighborhood_space_subset_derivedNeighborhood he
    ((mem_faceNeighborhood_space_iff ((barycentricSubdivision A).indep he)
      (Finset.filter_subset _ _) ⟨v', hv'f⟩).mpr ⟨hxe, v', hv'f, hv'max⟩)

open Classical in
theorem barycentricCoordinate_eq_zero_of_mem_subcomplex {A K : Geometry.SimplicialComplex ℝ E}
    (hKA : K.faces ⊆ A.faces) {x : E} (hx : x ∈ K.space) {w : E}
    (hw : w ∉ (barycentricSubdivision K).vertices) :
    barycentricCoordinate (barycentricSubdivision A) w x = 0 := by
  rw [← (barycentricSubdivision_isSubdivision K).space_eq] at hx
  obtain ⟨u, hu, hxu⟩ := (barycentricSubdivision K).mem_space_iff.mp hx
  rw [barycentricCoordinate_eq _ (barycentricSubdivision_faces_subset hKA hu) hxu, ite_eq_right]
  intro hwu
  exact hw ((barycentricSubdivision K).down_closed hu (Finset.singleton_subset_iff.mpr hwu)
    (Finset.singleton_nonempty w))

open Classical in
theorem mem_subcomplex_of_barycentricCoordinate_eq_zero {A K : Geometry.SimplicialComplex ℝ E}
    (hKA : K.faces ⊆ A.faces) {x : E} (hx : x ∈ (barycentricSubdivision A).space)
    (hzero : ∀ w ∉ (barycentricSubdivision K).vertices,
      barycentricCoordinate (barycentricSubdivision A) w x = 0) : x ∈ K.space := by
  obtain ⟨e, he, hxo⟩ := exists_face_mem_openSimplex _ hx
  have hfilter : e.filter (fun v => v ∈ (barycentricSubdivision K).vertices) = e := by
    refine Finset.filter_true_of_mem fun v hv => ?_
    by_contra hvK
    exact (barycentricCoordinate_pos_of_mem_openSimplex he hxo hv).ne' (hzero v hvK)
  have hmem := barycentricSubdivision_filter_mem hKA he
    (by rw [hfilter]; exact (barycentricSubdivision A).nonempty_of_mem_faces he)
  rw [hfilter] at hmem
  rw [← (barycentricSubdivision_isSubdivision K).space_eq]
  exact (barycentricSubdivision K).convexHull_subset_space hmem
    (openSimplex_subset_convexHull e hxo)

open Classical in
theorem notMem_interior_derivedNeighborhood_of_barycentricCoordinate_le
    {A K : Geometry.SimplicialComplex ℝ E} {y : E} (hy : y ∈ (barycentricSubdivision A).space)
    {w : E} (hw : w ∉ (barycentricSubdivision K).vertices)
    (hpos : 0 < barycentricCoordinate (barycentricSubdivision A) w y)
    (hle : ∀ v ∈ (barycentricSubdivision K).vertices,
      barycentricCoordinate (barycentricSubdivision A) v y ≤
        barycentricCoordinate (barycentricSubdivision A) w y) :
    y ∉ interior (derivedNeighborhood A K).space := by
  obtain ⟨e, he, hye⟩ := (barycentricSubdivision A).mem_space_iff.mp hy
  have hwe : w ∈ e := by
    by_contra hwe
    rw [barycentricCoordinate_eq _ he hye, ite_eq_right hwe] at hpos
    exact lt_irrefl 0 hpos
  have hwc : w ∈ convexHull ℝ (e : Set E) := subset_convexHull ℝ _ (Finset.mem_coe.mpr hwe)
  have hout : ∀ s : ℝ, 0 < s → s ≤ 1 →
      (1 - s) • y + s • w ∉ (derivedNeighborhood A K).space := by
    intro s hs0 hs1 hmem
    obtain ⟨v, hvK, hvmax⟩ := exists_barycentricCoordinate_le_of_mem_derivedNeighborhood hmem
    have hq : (1 - s) • y + s • w ∈ convexHull ℝ (e : Set E) :=
      (convex_convexHull ℝ _) hye hwc (sub_nonneg.mpr hs1) hs0.le (by ring)
    have hw' : barycentricCoordinate (barycentricSubdivision A) w ((1 - s) • y + s • w) =
        (1 - s) * barycentricCoordinate (barycentricSubdivision A) w y + s := by
      rw [barycentricCoordinate_add_smul he hye hwc (by ring) hq,
        barycentricCoordinate_vertex_of_mem he hwe, ite_eq_left rfl, mul_one]
    have hv' : barycentricCoordinate (barycentricSubdivision A) v ((1 - s) • y + s • w) =
        (1 - s) * barycentricCoordinate (barycentricSubdivision A) v y := by
      rw [barycentricCoordinate_add_smul he hye hwc (by ring) hq,
        barycentricCoordinate_vertex_of_mem he hwe, ite_eq_right fun h : v = w => hw (h ▸ hvK), mul_zero,
        add_zero]
    have h1 := hvmax w
    rw [hw', hv'] at h1
    have h2 := mul_le_mul_of_nonneg_left (hle v hvK) (sub_nonneg.mpr hs1)
    linarith
  intro hint
  have hnhds : (derivedNeighborhood A K).space ∈ 𝓝 y := mem_interior_iff_mem_nhds.mp hint
  have hcont : Continuous fun s : ℝ => (1 - s) • y + s • w := by fun_prop
  have htend : Filter.Tendsto (fun s : ℝ => (1 - s) • y + s • w) (𝓝[>] 0) (𝓝 y) :=
    (hcont.tendsto' 0 y (by simp)).mono_left nhdsWithin_le_nhds
  obtain ⟨s, hsN, hs⟩ := Filter.nonempty_of_mem
    (Filter.inter_mem (Filter.mem_map.mp (htend hnhds)) (Ioo_mem_nhdsGT zero_lt_one))
  exact hout s hs.1 hs.2.le hsN

open Classical in
theorem mem_interior_derivedNeighborhood_of_barycentricCoordinate_lt [FiniteDimensional ℝ E]
    {A K : Geometry.SimplicialComplex ℝ E} [Finite A.faces] {x : E} (hx : x ∈ interior A.space)
    {v : E} (hv : v ∈ (barycentricSubdivision K).vertices)
    (hlt : ∀ w ∉ (barycentricSubdivision K).vertices,
      barycentricCoordinate (barycentricSubdivision A) w x <
        barycentricCoordinate (barycentricSubdivision A) v x) :
    x ∈ interior (derivedNeighborhood A K).space := by
  have hAx : (barycentricSubdivision A).space ∈ 𝓝 x := by
    rw [(barycentricSubdivision_isSubdivision A).space_eq]
    exact mem_interior_iff_mem_nhds.mp hx
  have hev : ∀ w ∈ (simplicialComplexVertices (barycentricSubdivision A)).filter
      (fun w => w ∉ (barycentricSubdivision K).vertices), ∀ᶠ y in 𝓝 x,
        barycentricCoordinate (barycentricSubdivision A) w y <
          barycentricCoordinate (barycentricSubdivision A) v y := fun w hw =>
    ((continuousOn_barycentricCoordinate (barycentricSubdivision A) w).continuousAt
      hAx).eventually_lt
      ((continuousOn_barycentricCoordinate (barycentricSubdivision A) v).continuousAt hAx)
      (hlt w (Finset.mem_filter.mp hw).2)
  refine mem_interior_iff_mem_nhds.mpr ?_
  filter_upwards [(Filter.eventually_all_finset _).mpr hev, hAx] with y hy hyA
  refine mem_derivedNeighborhood_of_barycentricCoordinate_le hyA hv fun w hw => ?_
  by_cases hwA : w ∈ (barycentricSubdivision A).vertices
  · exact (hy w (Finset.mem_filter.mpr ⟨(mem_simplicialComplexVertices _).mpr hwA, hw⟩)).le
  · rw [barycentricCoordinate_eq_zero_of_notMem_vertices hyA hwA]
    exact barycentricCoordinate_nonneg _ hyA v

open Classical in
theorem frontier_derivedNeighborhood_space_subset (A K : Geometry.SimplicialComplex ℝ E)
    [Finite A.faces] :
    frontier (derivedNeighborhood A K).space ⊆ (derivedNeighborhood A K).space := by
  let _ : Finite (derivedNeighborhood A K).faces :=
    (derivedNeighborhood_faces_finite A K).to_subtype
  exact (SimplicialComplex.isCompact_geometricSpace _).isClosed.frontier_subset

open Classical in
theorem exists_barycentricCoordinate_eq_of_mem_frontier_derivedNeighborhood
    [FiniteDimensional ℝ E] {A K : Geometry.SimplicialComplex ℝ E} [Finite A.faces]
    (hN : (derivedNeighborhood A K).space ⊆ interior A.space) {b : E}
    (hb : b ∈ frontier (derivedNeighborhood A K).space) :
    ∃ v ∈ (barycentricSubdivision K).vertices, ∃ w ∉ (barycentricSubdivision K).vertices,
      (∀ u, barycentricCoordinate (barycentricSubdivision A) u b ≤
        barycentricCoordinate (barycentricSubdivision A) v b) ∧
      barycentricCoordinate (barycentricSubdivision A) w b =
        barycentricCoordinate (barycentricSubdivision A) v b := by
  have hbN := frontier_derivedNeighborhood_space_subset A K hb
  obtain ⟨v, hvK, hvmax⟩ := exists_barycentricCoordinate_le_of_mem_derivedNeighborhood hbN
  refine ⟨v, hvK, ?_⟩
  by_contra hcon
  push Not at hcon
  exact hb.2 (mem_interior_derivedNeighborhood_of_barycentricCoordinate_lt (hN hbN) hvK
    fun w hw => lt_of_le_of_ne (hvmax w) (hcon w hw hvmax))

open Classical in
theorem barycentricCoordinate_smul_add_smul_subcomplexBarycentricProjection
    {A K : Geometry.SimplicialComplex ℝ E} [Finite A.faces] {b : E}
    (hb : b ∈ (derivedNeighborhood A K).space) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (∀ u ∈ (barycentricSubdivision K).vertices,
      barycentricCoordinate (barycentricSubdivision A) u ((1 - t) • b + t •
        subcomplexBarycentricProjection (barycentricSubdivision A) (barycentricSubdivision K) b) =
        (1 - t + t * (subcomplexBarycentricMass (barycentricSubdivision A)
          (barycentricSubdivision K) b)⁻¹) *
            barycentricCoordinate (barycentricSubdivision A) u b) ∧
    ∀ u ∉ (barycentricSubdivision K).vertices,
      barycentricCoordinate (barycentricSubdivision A) u ((1 - t) • b + t •
        subcomplexBarycentricProjection (barycentricSubdivision A) (barycentricSubdivision K) b) =
        (1 - t) * barycentricCoordinate (barycentricSubdivision A) u b := by
  have hbA := derivedNeighborhood_space_subset_barycentricSubdivision A K hb
  have hm := subcomplexBarycentricMass_pos_on_derivedNeighborhood hb
  obtain ⟨e, he, hbe⟩ := (barycentricSubdivision A).mem_space_iff.mp hbA
  have hp : subcomplexBarycentricProjection (barycentricSubdivision A)
      (barycentricSubdivision K) b ∈ convexHull ℝ (e : Set E) :=
    convexHull_mono (Finset.coe_subset.mpr (Finset.filter_subset _ _))
      (subcomplexBarycentricProjection_mem_convexHull_filter _ _ he hbe hm)
  have hq := (convex_convexHull ℝ (e : Set E)) hbe hp (sub_nonneg.mpr ht1) ht0 (by ring)
  have key := barycentricCoordinate_add_smul he hbe hp (by ring) hq
  have hproj := barycentricCoordinate_subcomplexBarycentricProjection _ _ hbA hm
  refine ⟨fun u hu => ?_, fun u hu => ?_⟩
  · rw [key, hproj, ite_eq_left hu]
    ring
  · rw [key, hproj, ite_eq_right hu]
    ring

open Classical in
theorem smul_add_smul_subcomplexBarycentricProjection_notMem [FiniteDimensional ℝ E]
    {A K : Geometry.SimplicialComplex ℝ E} [Finite A.faces] (hKA : K.faces ⊆ A.faces)
    (hN : (derivedNeighborhood A K).space ⊆ interior A.space) {b : E}
    (hb : b ∈ frontier (derivedNeighborhood A K).space) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) :
    (1 - t) • b + t • subcomplexBarycentricProjection (barycentricSubdivision A)
      (barycentricSubdivision K) b ∉ K.space := by
  obtain ⟨v, -, w, hwK, hmax, htie⟩ :=
    exists_barycentricCoordinate_eq_of_mem_frontier_derivedNeighborhood hN hb
  have hbN := frontier_derivedNeighborhood_space_subset A K hb
  have hpos := barycentricCoordinate_pos_of_forall_le
    (derivedNeighborhood_space_subset_barycentricSubdivision A K hbN) hmax
  intro hx
  have h0 := barycentricCoordinate_eq_zero_of_mem_subcomplex hKA hx hwK
  rw [(barycentricCoordinate_smul_add_smul_subcomplexBarycentricProjection hbN ht0
    ht1.le).2 w hwK, htie] at h0
  exact (mul_pos (sub_pos.mpr ht1) hpos).ne' h0

open Classical in
theorem smul_add_smul_subcomplexBarycentricProjection_mem_interior [FiniteDimensional ℝ E]
    {A K : Geometry.SimplicialComplex ℝ E} [Finite A.faces]
    (hN : (derivedNeighborhood A K).space ⊆ interior A.space) {b : E}
    (hb : b ∈ frontier (derivedNeighborhood A K).space) {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    (1 - t) • b + t • subcomplexBarycentricProjection (barycentricSubdivision A)
      (barycentricSubdivision K) b ∈ interior (derivedNeighborhood A K).space := by
  obtain ⟨v, hvK, -, -, hmax, -⟩ :=
    exists_barycentricCoordinate_eq_of_mem_frontier_derivedNeighborhood hN hb
  have hbN := frontier_derivedNeighborhood_space_subset A K hb
  have hpos := barycentricCoordinate_pos_of_forall_le
    (derivedNeighborhood_space_subset_barycentricSubdivision A K hbN) hmax
  have hm := subcomplexBarycentricMass_pos_on_derivedNeighborhood hbN
  obtain ⟨hcore, hnon⟩ :=
    barycentricCoordinate_smul_add_smul_subcomplexBarycentricProjection hbN ht0.le ht1.le
  have hxN : (1 - t) • b + t • subcomplexBarycentricProjection (barycentricSubdivision A)
      (barycentricSubdivision K) b ∈ (derivedNeighborhood A K).space :=
    subcomplexBarycentricHomotopy_mem_derivedNeighborhood hbN ⟨t, ht0.le, ht1.le⟩
  refine mem_interior_derivedNeighborhood_of_barycentricCoordinate_lt (hN hxN) hvK
    fun u hu => ?_
  rw [hnon u hu, hcore v hvK]
  have h1 := mul_le_mul_of_nonneg_left (hmax u) (sub_nonneg.mpr ht1.le)
  have h2 := mul_pos (mul_pos ht0 (inv_pos.mpr hm)) hpos
  nlinarith

open Classical in
theorem eq_of_smul_add_smul_subcomplexBarycentricProjection_eq [FiniteDimensional ℝ E]
    {A K : Geometry.SimplicialComplex ℝ E} [Finite A.faces]
    (hN : (derivedNeighborhood A K).space ⊆ interior A.space) {b b' : E}
    (hb : b ∈ frontier (derivedNeighborhood A K).space)
    (hb' : b' ∈ frontier (derivedNeighborhood A K).space) {t t' : ℝ} (ht0 : 0 ≤ t)
    (ht1 : t < 1) (ht0' : 0 ≤ t') (ht1' : t' < 1)
    (heq : (1 - t) • b + t • subcomplexBarycentricProjection (barycentricSubdivision A)
        (barycentricSubdivision K) b =
      (1 - t') • b' + t' • subcomplexBarycentricProjection (barycentricSubdivision A)
        (barycentricSubdivision K) b') :
    b = b' ∧ t = t' := by
  obtain ⟨v, hvK, w, hwK, hmax, htie⟩ :=
    exists_barycentricCoordinate_eq_of_mem_frontier_derivedNeighborhood hN hb
  obtain ⟨v', hvK', w', hwK', hmax', htie'⟩ :=
    exists_barycentricCoordinate_eq_of_mem_frontier_derivedNeighborhood hN hb'
  have hbN := frontier_derivedNeighborhood_space_subset A K hb
  have hbN' := frontier_derivedNeighborhood_space_subset A K hb'
  have hpos := barycentricCoordinate_pos_of_forall_le
    (derivedNeighborhood_space_subset_barycentricSubdivision A K hbN) hmax
  have hm := subcomplexBarycentricMass_pos_on_derivedNeighborhood hbN
  have hm' := subcomplexBarycentricMass_pos_on_derivedNeighborhood hbN'
  obtain ⟨hcore, hnon⟩ :=
    barycentricCoordinate_smul_add_smul_subcomplexBarycentricProjection hbN ht0 ht1.le
  obtain ⟨hcore', hnon'⟩ :=
    barycentricCoordinate_smul_add_smul_subcomplexBarycentricProjection hbN' ht0' ht1'.le
  rw [← heq] at hcore' hnon'
  have hc : 0 < 1 - t + t * (subcomplexBarycentricMass (barycentricSubdivision A)
      (barycentricSubdivision K) b)⁻¹ := by
    have := mul_nonneg ht0 (inv_nonneg.mpr hm.le)
    linarith
  have hc' : 0 < 1 - t' + t' * (subcomplexBarycentricMass (barycentricSubdivision A)
      (barycentricSubdivision K) b')⁻¹ := by
    have := mul_nonneg ht0' (inv_nonneg.mpr hm'.le)
    linarith
  have hp := subcomplexBarycentricProjection_eq_of_barycentricCoordinate_eq_mul _ _ hc.ne' hcore
  have hp' :=
    subcomplexBarycentricProjection_eq_of_barycentricCoordinate_eq_mul _ _ hc'.ne' hcore'
  have hmx := subcomplexBarycentricMass_eq_mul_of_barycentricCoordinate_eq_mul _ _ hcore
  have hmx' := subcomplexBarycentricMass_eq_mul_of_barycentricCoordinate_eq_mul _ _ hcore'
  have hinv := mul_inv_cancel₀ hm.ne'
  have hinv' := mul_inv_cancel₀ hm'.ne'
  generalize (1 - t) • b + t • subcomplexBarycentricProjection (barycentricSubdivision A)
    (barycentricSubdivision K) b = x at hcore hnon hcore' hnon' hmx hmx'
  generalize barycentricCoordinate (barycentricSubdivision A) = β
    at hcore hnon hcore' hnon' hmax hmax' htie htie' hpos
  generalize subcomplexBarycentricMass (barycentricSubdivision A) (barycentricSubdivision K) x = M
    at hmx hmx'
  generalize subcomplexBarycentricMass (barycentricSubdivision A) (barycentricSubdivision K) b = m
    at hm hc hcore hmx hinv
  generalize subcomplexBarycentricMass (barycentricSubdivision A) (barycentricSubdivision K) b'
    = m' at hm' hc' hcore' hmx' hinv'
  have ha : β v x = β v' x := le_antisymm
    (by rw [hcore' v hvK, hcore' v' hvK']; exact mul_le_mul_of_nonneg_left (hmax' v) hc'.le)
    (by rw [hcore v' hvK', hcore v hvK]; exact mul_le_mul_of_nonneg_left (hmax v') hc.le)
  have hB : β w x = β w' x := le_antisymm
    (by
      rw [hnon' w hwK, hnon' w' hwK', htie']
      exact mul_le_mul_of_nonneg_left (hmax' w) (sub_nonneg.mpr ht1'.le))
    (by
      rw [hnon w' hwK', hnon w hwK, htie]
      exact mul_le_mul_of_nonneg_left (hmax w') (sub_nonneg.mpr ht1.le))
  have hkey : t * β v x = M * (β v x - β w x) := by
    rw [hmx, hcore v hvK, hnon w hwK, htie]
    linear_combination (-(t * (1 - t + t * m⁻¹) * β v b)) * hinv
  have hkey' : t' * β v' x = M * (β v' x - β w' x) := by
    rw [hmx', hcore' v' hvK', hnon' w' hwK', htie']
    linear_combination (-(t' * (1 - t' + t' * m'⁻¹) * β v' b')) * hinv'
  have hapos : 0 < β v x := by
    rw [hcore v hvK]
    exact mul_pos hc hpos
  have htt : t = t' := by
    apply mul_right_cancel₀ hapos.ne'
    rw [hkey, ha, hB, ← hkey']
  subst htt
  rw [← hp.symm.trans hp'] at heq
  exact ⟨smul_right_injective E (sub_pos.mpr ht1).ne' (add_right_cancel heq), rfl⟩

open Classical in
theorem exists_mem_frontier_derivedNeighborhood_of_mem_interior
    {A K : Geometry.SimplicialComplex ℝ E} [Finite A.faces] (hKA : K.faces ⊆ A.faces)
    {x : E} (hx : x ∈ interior (derivedNeighborhood A K).space) (hxK : x ∉ K.space) :
    ∃ b ∈ frontier (derivedNeighborhood A K).space, ∃ t ∈ Ioo (0 : ℝ) 1,
      (1 - t) • b + t • subcomplexBarycentricProjection (barycentricSubdivision A)
        (barycentricSubdivision K) b = x := by
  have hxN : x ∈ (derivedNeighborhood A K).space := interior_subset hx
  have hxA := derivedNeighborhood_space_subset_barycentricSubdivision A K hxN
  have hm := subcomplexBarycentricMass_pos_on_derivedNeighborhood hxN
  obtain ⟨v, hvK, hvmax⟩ := exists_barycentricCoordinate_le_of_mem_derivedNeighborhood hxN
  obtain ⟨w₁, hw₁K, hw₁⟩ : ∃ w ∉ (barycentricSubdivision K).vertices,
      barycentricCoordinate (barycentricSubdivision A) w x ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hxK (mem_subcomplex_of_barycentricCoordinate_eq_zero hKA hxA hcon)
  have hw₁A : w₁ ∈ simplicialComplexVertices (barycentricSubdivision A) := by
    rw [mem_simplicialComplexVertices]
    by_contra h
    exact hw₁ (barycentricCoordinate_eq_zero_of_notMem_vertices hxA h)
  obtain ⟨w, hwS, hwmax⟩ := ((simplicialComplexVertices (barycentricSubdivision A)).filter
    fun u => u ∉ (barycentricSubdivision K).vertices).exists_max_image
      (fun u => barycentricCoordinate (barycentricSubdivision A) u x)
      ⟨w₁, Finset.mem_filter.mpr ⟨hw₁A, hw₁K⟩⟩
  have hwK := (Finset.mem_filter.mp hwS).2
  have hwle : ∀ u ∉ (barycentricSubdivision K).vertices,
      barycentricCoordinate (barycentricSubdivision A) u x ≤
        barycentricCoordinate (barycentricSubdivision A) w x := by
    intro u hu
    by_cases huA : u ∈ (barycentricSubdivision A).vertices
    · exact hwmax u (Finset.mem_filter.mpr ⟨(mem_simplicialComplexVertices _).mpr huA, hu⟩)
    · rw [barycentricCoordinate_eq_zero_of_notMem_vertices hxA huA]
      exact barycentricCoordinate_nonneg _ hxA w
  have hBpos : 0 < barycentricCoordinate (barycentricSubdivision A) w x :=
    ((barycentricCoordinate_nonneg _ hxA w₁).lt_of_ne (Ne.symm hw₁)).trans_le (hwle w₁ hw₁K)
  have hBa : barycentricCoordinate (barycentricSubdivision A) w x <
      barycentricCoordinate (barycentricSubdivision A) v x :=
    (hvmax w).lt_of_ne fun hBa =>
      notMem_interior_derivedNeighborhood_of_barycentricCoordinate_le hxA hwK hBpos
        (fun u _ => (hvmax u).trans hBa.ge) hx
  have hmB : subcomplexBarycentricMass (barycentricSubdivision A) (barycentricSubdivision K) x +
      barycentricCoordinate (barycentricSubdivision A) w x ≤ 1 := by
    have hsum := sum_barycentricCoordinate hxA
    rw [← Finset.sum_filter_add_sum_filter_not _
      (fun u => u ∈ (barycentricSubdivision K).vertices)] at hsum
    have hle : barycentricCoordinate (barycentricSubdivision A) w x ≤
        ∑ u ∈ (simplicialComplexVertices (barycentricSubdivision A)).filter
          (fun u => u ∉ (barycentricSubdivision K).vertices),
            barycentricCoordinate (barycentricSubdivision A) u x :=
      Finset.single_le_sum (fun u _ => barycentricCoordinate_nonneg _ hxA u) hwS
    rw [subcomplexBarycentricMass]
    linarith
  generalize hmdef : subcomplexBarycentricMass (barycentricSubdivision A)
    (barycentricSubdivision K) x = m at hm hmB
  generalize hadef : barycentricCoordinate (barycentricSubdivision A) v x = a at hBa hvmax
  generalize hBdef : barycentricCoordinate (barycentricSubdivision A) w x = B at hBa hBpos hmB hwle
  have hapos : 0 < a := hBpos.trans hBa
  have hainv := mul_inv_cancel₀ hapos.ne'
  have hminv := mul_inv_cancel₀ hm.ne'
  obtain ⟨t, ht⟩ : ∃ t : ℝ, t = m * (a - B) * a⁻¹ := ⟨_, rfl⟩
  have ht0 : 0 < t := by
    rw [ht]
    exact mul_pos (mul_pos hm (sub_pos.mpr hBa)) (inv_pos.mpr hapos)
  have ht1 : t < 1 := by
    have htm : t = m - m * B * a⁻¹ := by
      rw [ht]
      linear_combination m * hainv
    have := mul_pos (mul_pos hm hBpos) (inv_pos.mpr hapos)
    linarith
  have hlam : (1 - t * m⁻¹) * a = B := by
    linear_combination (-(m⁻¹ * a)) * ht + (-(a - B)) * hminv + (-(a - B) * m * m⁻¹) * hainv
  have hlampos : 0 < 1 - t * m⁻¹ := by
    have h' : 1 - t * m⁻¹ = B / a := by
      rw [eq_div_iff hapos.ne']
      exact hlam
    rw [h']
    exact div_pos hBpos hapos
  have h1t : 1 - t ≠ 0 := (sub_pos.mpr ht1).ne'
  have hκ : 0 < (1 - t)⁻¹ := inv_pos.mpr (sub_pos.mpr ht1)
  obtain ⟨e, he, hxe⟩ := (barycentricSubdivision A).mem_space_iff.mp hxA
  have hmx : 0 < subcomplexBarycentricMass (barycentricSubdivision A)
      (barycentricSubdivision K) x := hmdef ▸ hm
  have hpe : subcomplexBarycentricProjection (barycentricSubdivision A)
      (barycentricSubdivision K) x ∈ convexHull ℝ (e : Set E) :=
    convexHull_mono (Finset.coe_subset.mpr (Finset.filter_subset _ _))
      (subcomplexBarycentricProjection_mem_convexHull_filter _ _ he hxe hmx)
  have hproj := barycentricCoordinate_subcomplexBarycentricProjection _ _ hxA hmx
  rw [hmdef] at hproj
  have hαγ : (1 - t)⁻¹ + -(t * (1 - t)⁻¹) = 1 := by
    rw [show (1 - t)⁻¹ + -(t * (1 - t)⁻¹) = (1 - t) * (1 - t)⁻¹ by ring, mul_inv_cancel₀ h1t]
  have hnonneg : ∀ u ∈ e, 0 ≤ (1 - t)⁻¹ * barycentricCoordinate (barycentricSubdivision A) u x +
      -(t * (1 - t)⁻¹) * barycentricCoordinate (barycentricSubdivision A) u
        (subcomplexBarycentricProjection (barycentricSubdivision A)
          (barycentricSubdivision K) x) := by
    intro u _
    have hβu := barycentricCoordinate_nonneg _ hxA u
    rw [hproj u]
    split_ifs
    · rw [show (1 - t)⁻¹ * barycentricCoordinate (barycentricSubdivision A) u x +
          -(t * (1 - t)⁻¹) * (m⁻¹ * barycentricCoordinate (barycentricSubdivision A) u x) =
          (1 - t)⁻¹ * (1 - t * m⁻¹) * barycentricCoordinate (barycentricSubdivision A) u x by
        ring]
      exact mul_nonneg (mul_pos hκ hlampos).le hβu
    · rw [mul_zero, add_zero]
      exact mul_nonneg hκ.le hβu
  have hbe := add_smul_mem_convexHull_of_barycentricCoordinate_nonneg he hxe hpe hαγ hnonneg
  have hbcoord := barycentricCoordinate_add_smul he hxe hpe hαγ hbe
  generalize hbdef : (1 - t)⁻¹ • x + -(t * (1 - t)⁻¹) •
    subcomplexBarycentricProjection (barycentricSubdivision A) (barycentricSubdivision K) x = b
    at hbe hbcoord
  have hbA : b ∈ (barycentricSubdivision A).space :=
    (barycentricSubdivision A).convexHull_subset_space he hbe
  have hbcore : ∀ u ∈ (barycentricSubdivision K).vertices,
      barycentricCoordinate (barycentricSubdivision A) u b =
        (1 - t)⁻¹ * (1 - t * m⁻¹) * barycentricCoordinate (barycentricSubdivision A) u x := by
    intro u hu
    rw [hbcoord u, hproj u, ite_eq_left hu]
    ring
  have hbnon : ∀ u ∉ (barycentricSubdivision K).vertices,
      barycentricCoordinate (barycentricSubdivision A) u b =
        (1 - t)⁻¹ * barycentricCoordinate (barycentricSubdivision A) u x := by
    intro u hu
    rw [hbcoord u, hproj u, ite_eq_right hu]
    ring
  have hbv : barycentricCoordinate (barycentricSubdivision A) v b = (1 - t)⁻¹ * B := by
    rw [hbcore v hvK, hadef, mul_assoc, hlam]
  have hbN : b ∈ (derivedNeighborhood A K).space :=
    mem_derivedNeighborhood_of_barycentricCoordinate_le hbA hvK fun u hu => by
      rw [hbnon u hu, hbv]
      exact mul_le_mul_of_nonneg_left (hwle u hu) hκ.le
  have hbint : b ∉ interior (derivedNeighborhood A K).space := by
    refine notMem_interior_derivedNeighborhood_of_barycentricCoordinate_le hbA hwK ?_ ?_
    · rw [hbnon w hwK, hBdef]
      exact mul_pos hκ hBpos
    · intro u hu
      rw [hbcore u hu, hbnon w hwK, hBdef, mul_assoc, ← hlam]
      refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ hlampos.le) hκ.le
      exact hvmax u
  have hpb := subcomplexBarycentricProjection_eq_of_barycentricCoordinate_eq_mul _ _
    (mul_pos hκ hlampos).ne' hbcore
  refine ⟨b, ⟨subset_closure hbN, hbint⟩, t, ⟨ht0, ht1⟩, ?_⟩
  have hinv1 := mul_inv_cancel₀ h1t
  rw [hpb, ← hbdef, smul_add, smul_smul, smul_smul, hinv1, one_smul,
    show (1 - t) * -(t * (1 - t)⁻¹) = -t by linear_combination (-t) * hinv1, neg_smul,
    add_assoc, neg_add_cancel, add_zero]

open Classical in
theorem range_derivedNeighborhoodRay_of_subset_interior [FiniteDimensional ℝ E]
    (A K : Geometry.SimplicialComplex ℝ E) [Finite A.faces] (hKA : K.faces ⊆ A.faces)
    (hN : (derivedNeighborhood A K).space ⊆ interior A.space) :
    Set.range (derivedNeighborhoodRay A K) =
      interior (derivedNeighborhood A K).space \ K.space := by
  apply Subset.antisymm
  · rintro _ ⟨⟨⟨b, hb⟩, ⟨t, ht0, ht1⟩⟩, rfl⟩
    exact ⟨smul_add_smul_subcomplexBarycentricProjection_mem_interior hN hb ht0 ht1,
      smul_add_smul_subcomplexBarycentricProjection_notMem hKA hN hb ht0.le ht1⟩
  · rintro x ⟨hx, hxK⟩
    obtain ⟨b, hb, t, ht, hbt⟩ := exists_mem_frontier_derivedNeighborhood_of_mem_interior hKA hx hxK
    exact ⟨(⟨b, hb⟩, ⟨t, ht⟩), hbt⟩

open Classical in
theorem isEmbedding_derivedNeighborhoodRay_of_subset_interior [FiniteDimensional ℝ E]
    (A K : Geometry.SimplicialComplex ℝ E) [Finite A.faces] (hKA : K.faces ⊆ A.faces)
    (hN : (derivedNeighborhood A K).space ⊆ interior A.space) :
    _root_.Topology.IsEmbedding (derivedNeighborhoodRay A K) := by
  have hfront := frontier_derivedNeighborhood_space_subset A K
  let _ : Finite (derivedNeighborhood A K).faces :=
    (derivedNeighborhood_faces_finite A K).to_subtype
  have _ : CompactSpace (frontier (derivedNeighborhood A K).space) :=
    isCompact_iff_compactSpace.mp
      ((SimplicialComplex.isCompact_geometricSpace _).of_isClosed_subset isClosed_frontier hfront)
  let R : frontier (derivedNeighborhood A K).space × Set.Icc (0 : ℝ) 1 → E := fun q =>
    (1 - (q.2 : ℝ)) • (q.1 : E) + (q.2 : ℝ) •
      subcomplexBarycentricProjection (barycentricSubdivision A) (barycentricSubdivision K) q.1
  have hp : Continuous (fun x : frontier (derivedNeighborhood A K).space =>
      subcomplexBarycentricProjection (barycentricSubdivision A) (barycentricSubdivision K) x) :=
    (continuousOn_subcomplexBarycentricProjection_derivedNeighborhood.mono hfront).domRestrict
  have hR : Continuous R :=
    ((continuous_const.sub (continuous_subtype_val.comp continuous_snd)).smul
      (continuous_subtype_val.comp continuous_fst)).add
      ((continuous_subtype_val.comp continuous_snd).smul (hp.comp continuous_fst))
  have hlt : ∀ q : frontier (derivedNeighborhood A K).space × Set.Icc (0 : ℝ) 1,
      R q ∉ K.space → (q.2 : ℝ) < 1 := by
    intro q hq
    refine lt_of_le_of_ne q.2.2.2 fun h1 => hq ?_
    change (1 - (q.2 : ℝ)) • (q.1 : E) + (q.2 : ℝ) •
      subcomplexBarycentricProjection (barycentricSubdivision A) (barycentricSubdivision K) q.1
        ∈ K.space
    rw [h1, sub_self, zero_smul, one_smul, zero_add]
    exact subcomplexBarycentricProjection_mem_subcomplex hKA (hfront q.1.2)
  have hinj : Function.Injective ((K.space)ᶜ.restrictPreimage R) := by
    rintro ⟨q, hq⟩ ⟨q', hq'⟩ heq
    obtain ⟨hbb, htt⟩ := eq_of_smul_add_smul_subcomplexBarycentricProjection_eq hN q.1.2 q'.1.2
      q.2.2.1 (hlt q hq) q'.2.2.1 (hlt q' hq') (congrArg Subtype.val heq)
    exact Subtype.ext (Prod.ext (Subtype.ext hbb) (Subtype.ext htt))
  have hemb : _root_.Topology.IsEmbedding ((K.space)ᶜ.restrictPreimage R) :=
    (_root_.Topology.IsClosedEmbedding.of_continuous_injective_isClosedMap hR.restrictPreimage
      hinj (IsClosedMap.restrictPreimage hR.isClosedMap _)).isEmbedding
  have hmem : ∀ q : frontier (derivedNeighborhood A K).space × Set.Ioo (0 : ℝ) 1,
      Prod.map id (Set.inclusion Set.Ioo_subset_Icc_self) q ∈ R ⁻¹' (K.space)ᶜ := fun q =>
    smul_add_smul_subcomplexBarycentricProjection_notMem hKA hN q.1.2 q.2.2.1.le q.2.2.2
  exact (_root_.Topology.IsEmbedding.subtypeVal.comp hemb).comp
    ((_root_.Topology.IsEmbedding.id.prodMap
      (_root_.Topology.IsEmbedding.inclusion Set.Ioo_subset_Icc_self)).codRestrict _ hmem)

open Classical in
theorem nonempty_homeomorph_derivedNeighborhood_interior_sdiff_of_subset_interior
    [FiniteDimensional ℝ E] (A K : Geometry.SimplicialComplex ℝ E) [Finite A.faces]
    (hKA : K.faces ⊆ A.faces) (hN : (derivedNeighborhood A K).space ⊆ interior A.space) :
    Nonempty ((frontier (derivedNeighborhood A K).space × Set.Ioo (0 : ℝ) 1) ≃ₜ
      ↥(interior (derivedNeighborhood A K).space \ K.space)) :=
  ⟨(isEmbedding_derivedNeighborhoodRay_of_subset_interior A K hKA hN).toHomeomorph.trans
    (Homeomorph.setCongr (range_derivedNeighborhoodRay_of_subset_interior A K hKA hN))⟩

open Classical in
theorem derivedNeighborhood_space_subset_interior [FiniteDimensional ℝ E] {n : ℕ}
    (hn : Module.finrank ℝ E = n + 1) {A K : Geometry.SimplicialComplex ℝ E} [Finite A.faces]
    (hA : IsCombinatorialManifoldWithBoundary (n + 1) A) (hKA : K.faces ⊆ A.faces)
    (hK : K.space ⊆ interior A.space) :
    (derivedNeighborhood A K).space ⊆ interior A.space := by
  have hfr := frontier_space_eq_boundaryComplex_space_of_finrank hn A hA
  intro x hx
  have hxA' := derivedNeighborhood_space_subset_barycentricSubdivision A K hx
  have hxA := derivedNeighborhood_space_subset A K hx
  have hm := subcomplexBarycentricMass_pos_on_derivedNeighborhood hx
  obtain ⟨e, he, hxo⟩ := exists_face_mem_openSimplex _ hxA'
  have hxe := openSimplex_subset_convexHull e hxo
  rw [subcomplexBarycentricMass_eq_sum_filter _ _ he hxe] at hm
  obtain ⟨v, hv, -⟩ := Finset.exists_ne_zero_of_sum_ne_zero hm.ne'
  obtain ⟨hve, hvK⟩ := Finset.mem_filter.mp hv
  obtain ⟨τ, hτ, hτv⟩ := exists_eq_centroid_of_singleton_mem_barycentricSubdivision K hvK
  by_contra hxint
  have hxB : x ∈ (boundaryComplex (n + 1) A).space := by
    rw [← hfr, (SimplicialComplex.isCompact_geometricSpace A).isClosed.frontier_eq]
    exact ⟨hxA, hxint⟩
  rw [← (barycentricSubdivision_isSubdivision (boundaryComplex (n + 1) A)).space_eq] at hxB
  obtain ⟨u, hu, hxu⟩ :=
    (barycentricSubdivision (boundaryComplex (n + 1) A)).mem_space_iff.mp hxB
  have heu := face_subset_of_mem_openSimplex_of_mem_convexHull _ he
    (barycentricSubdivision_faces_subset (boundaryComplex_faces_subset (n + 1) A) hu) hxo hxu
  obtain ⟨d, hd, -, rfl⟩ := hu
  obtain ⟨ρ, hρ, hρv⟩ := Finset.mem_image.mp (heu hve)
  have hρB := hd.mem_faces hρ
  have hρτ : ρ = τ := injOn_faces_of_mem_openSimplex A (centroid_mem_openSimplex_of_mem_faces A)
    (boundaryComplex_faces_subset (n + 1) A hρB) (hKA hτ) (hρv.trans hτv.symm)
  rw [hρτ] at hρB
  have hc : τ.centroid ℝ id ∈ convexHull ℝ (τ : Set E) :=
    openSimplex_subset_convexHull τ (centroid_mem_openSimplex_of_mem_faces A τ (hKA hτ))
  have hcB : τ.centroid ℝ id ∈ frontier A.space := by
    rw [hfr]
    exact (boundaryComplex (n + 1) A).convexHull_subset_space hρB hc
  exact hcB.2 (hK (K.convexHull_subset_space hτ hc))

end Neighborhood

section Tube

variable {K : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3))}
  {N N' : Set (EuclideanSpace ℝ (Fin 3))}
  {C Cpp : EuclideanSpace ℝ (Fin 3) → Set (EuclideanSpace ℝ (Fin 3))}
  {D Dbd Ec Eint Ebd : Finset (EuclideanSpace ℝ (Fin 3)) → Set (EuclideanSpace ℝ (Fin 3))}
  {h : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)}
  {XK : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3))}
  {AK : EuclideanSpace ℝ (Fin 3) → Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3))}

theorem section33_tube_product (ht : IsTube K N C D Dbd h N') :
    Nonempty ((frontier N × Set.Ioo (0 : ℝ) 1) ≃ₜ ↥(interior N' \ h '' K.space)) := by
  classical
  let _ : DecidableEq (EuclideanSpace ℝ (Fin 3)) := fun a b => Classical.propDecidable (a = b)
  obtain ⟨A, hAfin, hA, hKA, hC, -⟩ := ht.derivedModel
  let _ : Finite A.faces := hAfin.to_subtype
  have hN : N = (derivedNeighborhood A K).space := by
    rw [ht.unionEq, ← iUnion_graphDualCell_space A K hKA]
    exact iUnion₂_congr hC
  have hKN : K.space ⊆ interior N := subset_interior_iff_mem_nhdsSet.mpr ht.isNeighborhood
  have hNA : N ⊆ A.space := by
    rw [hN]
    exact derivedNeighborhood_space_subset A K
  have hKint : K.space ⊆ interior A.space := hKN.trans (interior_mono hNA)
  have hprod : Nonempty ((frontier N × Set.Ioo (0 : ℝ) 1) ≃ₜ ↥(interior N \ K.space)) := by
    rw [hN]
    exact nonempty_homeomorph_derivedNeighborhood_interior_sdiff_of_subset_interior A K hKA
      (derivedNeighborhood_space_subset_interior (n := 2) finrank_euclideanSpace_fin hA hKA
        hKint)
  have hcompact : IsCompact N := by
    rw [hN]
    let _ : Finite (derivedNeighborhood A K).faces :=
      (derivedNeighborhood_faces_finite A K).to_subtype
    exact SimplicialComplex.isCompact_geometricSpace (derivedNeighborhood A K)
  obtain ⟨e⟩ := hprod
  obtain ⟨e'⟩ := nonempty_homeomorph_interior_sdiff_image_of_isCompact hcompact
    (hKN.trans interior_subset)
    (continuousOn_iff_continuous_domRestrict.mpr ht.isEmbedding.continuous)
    (injOn_iff_injective.mpr ht.isEmbedding.injective)
  rw [ht.imageEq]
  exact ⟨e.trans e'⟩

end Tube

end DifferentialGeometry.Topology.PiecewiseLinear
