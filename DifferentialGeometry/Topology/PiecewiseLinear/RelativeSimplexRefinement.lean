/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.RelativeDerivedNeighborhood
import DifferentialGeometry.Topology.PiecewiseLinear.Gluing
import Mathlib.Analysis.Normed.Module.Convex

open Set Topology Metric

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

open Classical in
private theorem exists_relative_centers
    (K A : Geometry.SimplicialComplex ℝ E) {ε : ℝ} (hε : 0 < ε) :
    ∃ c : Finset E → E, ∀ s ∈ K.faces, c s ∈ openSimplex s ∧
      ((s.filter (· ∈ A.vertices)).Nonempty →
        c s ∈ cthickening ε (convexHull ℝ ((s.filter (· ∈ A.vertices) : Finset E) : Set E))) := by
  have hex (s : Finset E) : ∃ p : E, s ∈ K.faces → p ∈ openSimplex s ∧
      ((s.filter (· ∈ A.vertices)).Nonempty →
        p ∈ cthickening ε (convexHull ℝ ((s.filter (· ∈ A.vertices) : Finset E) : Set E))) := by
    by_cases hs : s ∈ K.faces
    · by_cases hne : (s.filter (· ∈ A.vertices)).Nonempty
      · let t := s.filter (· ∈ A.vertices)
        let z := t.centroid ℝ id
        have hz : z ∈ convexHull ℝ (t : Set E) := t.centroid_mem_convexHull hne
        have hzcl : z ∈ closure (openSimplex s) :=
          convexHull_subset_closure_openSimplex (K.nonempty_of_mem_faces hs)
            (convexHull_mono (Finset.coe_subset.mpr (Finset.filter_subset _ _)) hz)
        obtain ⟨p, hp, hdist⟩ := Metric.mem_closure_iff.mp hzcl ε hε
        exact ⟨p, fun _ => ⟨hp, fun _ =>
          mem_cthickening_of_dist_le p z ε _ hz (by simpa only [dist_comm] using hdist.le)⟩⟩
      · exact ⟨s.centroid ℝ id, fun _ =>
          ⟨centroid_mem_openSimplex_of_mem_faces K s hs, fun h => (hne h).elim⟩⟩
    · exact ⟨0, fun h => (hs h).elim⟩
  choose c hc using hex
  exact ⟨c, hc⟩

open Classical in
private theorem exists_refinement_small_star_of_full
    (K A : Geometry.SimplicialComplex ℝ E) [Finite K.faces] (hA : A.faces ⊆ K.faces)
    (hfull : ∀ s ∈ K.faces, (∀ v ∈ s, v ∈ A.vertices) → s ∈ A.faces)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ R : Geometry.SimplicialComplex ℝ E, IsSubdivision R K ∧ R.faces.Finite ∧
      A.faces ⊆ R.faces ∧ (regularNeighborhoodIn R A.space).space ⊆ cthickening ε A.space := by
  let _ : Finite A.faces := ((Set.toFinite K.faces).subset hA).to_subtype
  obtain ⟨c, hc⟩ := exists_relative_centers K A hε
  have hcopen : ∀ s ∈ K.faces, c s ∈ openSimplex s := fun s hs => (hc s hs).1
  let R := relDerived hA (IsSubdivision.refl A) hcopen
  have hAR : A.faces ⊆ R.faces := faces_subset_relDerived hA (IsSubdivision.refl A) hcopen
  have hvertex {s : Finset E} (hs : s ∈ K.faces) {v : E} (hvA : v ∈ A.vertices)
      (hv : v ∈ convexHull ℝ (s : Set E)) : v ∈ s :=
    Finset.singleton_subset_iff.mp
      (face_subset_of_mem_openSimplex_of_mem_convexHull K (hA hvA) hs
        (mem_openSimplex_singleton v) hv)
  refine ⟨R, relDerived_isSubdivision hA (IsSubdivision.refl A) hcopen,
    relDerived_faces_finite hA (IsSubdivision.refl A) hcopen, hAR, ?_⟩
  intro x hx
  obtain ⟨u, ⟨hu, t, ht, hut, y, hyt, hyA⟩, hxu⟩ :=
    (regularNeighborhoodIn R A.space).mem_space_iff.mp hx
  have hxt := convexHull_mono (Finset.coe_subset.mpr hut) hxu
  obtain ⟨τ, d, hrel, rfl⟩ := (mem_relDerived_faces_iff hA (IsSubdivision.refl A) hcopen).mp ht
  obtain ⟨q, hq, hyq⟩ := A.mem_space_iff.mp hyA
  have hyinter : y ∈ convexHull ℝ (((τ ∪ d.image c) ∩ q : Finset E) : Set E) := by
    rw [Finset.coe_inter]
    exact R.inter_subset_convexHull ht (hAR hq) ⟨hyt, hyq⟩
  obtain ⟨v, hv⟩ := nonempty_of_mem_convexHull hyinter
  have hvq := (Finset.mem_inter.mp hv).2
  have hvA : v ∈ A.vertices :=
    A.down_closed hq (Finset.singleton_subset_iff.mpr hvq) (Finset.singleton_nonempty v)
  have hvτ : v ∈ τ := by
    rcases Finset.mem_union.mp (Finset.mem_inter.mp hv).1 with hvτ | hvc
    · exact hvτ
    · obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hvc
      exact (c_notMem_space hA hcopen (hrel.flag.mem_faces hs) (hrel.notMem s hs)
        (A.vertices_subset_space hvA)).elim
  have hτ : τ ∈ A.faces := hrel.base.resolve_left (Finset.nonempty_iff_ne_empty.mp ⟨v, hvτ⟩)
  have hτvertex : ∀ w ∈ τ, w ∈ A.vertices := fun w hw =>
    A.down_closed hτ (Finset.singleton_subset_iff.mpr hw) (Finset.singleton_nonempty w)
  rcases d.eq_empty_or_nonempty with hd | hd
  · have hxτ : x ∈ convexHull ℝ (τ : Set E) := by
      simpa only [hd, Finset.image_empty, Finset.union_empty] using hxt
    exact self_subset_cthickening A.space (A.convexHull_subset_space hτ hxτ)
  · obtain ⟨s, hs, htop⟩ := hrel.flag.exists_top hd
    have hsK := hrel.flag.mem_faces hs
    let w := s.filter (· ∈ A.vertices)
    have hτw : τ ⊆ w := by
      intro z hz
      exact Finset.mem_filter.mpr
        ⟨hvertex hsK (hτvertex z hz) (hrel.subset s hs hz), hτvertex z hz⟩
    have hwne : w.Nonempty := ⟨v, hτw hvτ⟩
    have hwK : w ∈ K.faces := K.down_closed hsK (Finset.filter_subset _ _) hwne
    have hwA : w ∈ A.faces := hfull w hwK (fun z hz => (Finset.mem_filter.mp hz).2)
    have hpts : ((τ ∪ d.image c : Finset E) : Set E) ⊆
        cthickening ε (convexHull ℝ (w : Set E)) := by
      intro z hz
      rcases Finset.mem_union.mp hz with hzτ | hzc
      · exact self_subset_cthickening _ (subset_convexHull ℝ _ (hτw hzτ))
      · obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hzc
        have hrK := hrel.flag.mem_faces hr
        have hrne : (r.filter (· ∈ A.vertices)).Nonempty :=
          ⟨v, Finset.mem_filter.mpr ⟨hvertex hrK hvA (hrel.subset r hr hvτ), hvA⟩⟩
        have hfilter : r.filter (· ∈ A.vertices) ⊆ w := by
          intro z hz
          exact Finset.mem_filter.mpr
            ⟨htop r hr (Finset.mem_filter.mp hz).1, (Finset.mem_filter.mp hz).2⟩
        exact cthickening_subset_of_subset ε (convexHull_mono (Finset.coe_subset.mpr hfilter))
          ((hc r hrK).2 hrne)
    exact cthickening_subset_of_subset ε (A.convexHull_subset_space hwA)
      (convexHull_min hpts ((convex_convexHull ℝ (w : Set E)).cthickening ε) hxt)

open Classical in
theorem exists_isSubdivision_regularNeighborhoodIn_subset_cthickening
    (K A : Geometry.SimplicialComplex ℝ E) [Finite K.faces] (hA : A.faces ⊆ K.faces)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ R : Geometry.SimplicialComplex ℝ E, IsSubdivision R K ∧ R.faces.Finite ∧
      A.faces ⊆ R.faces ∧ (regularNeighborhoodIn R A.space).space ⊆ cthickening ε A.space := by
  let _ : Finite A.faces := ((Set.toFinite K.faces).subset hA).to_subtype
  let B := relativeBarycentricSubdivision hA
  let _ : Finite B.faces := (relativeBarycentricSubdivision_faces_finite hA).to_subtype
  have hAB : A.faces ⊆ B.faces := faces_subset_relativeBarycentricSubdivision hA
  have hfull : ∀ s ∈ B.faces, (∀ v ∈ s, v ∈ A.vertices) → s ∈ A.faces :=
    fun _ hs hv => mem_faces_of_mem_relDerived_of_forall_singleton_mem hA
      (IsSubdivision.refl A) (centroid_mem_openSimplex_of_mem_faces K) hs hv
  obtain ⟨R, hR, hfin, hAR, hsmall⟩ := exists_refinement_small_star_of_full B A hAB hfull hε
  exact ⟨R, hR.trans (relativeBarycentricSubdivision_isSubdivision hA), hfin, hAR, hsmall⟩

open Classical in
theorem exists_isSubdivision_regularNeighborhoodIn_subset_of_isOpen [FiniteDimensional ℝ E]
    (K A : Geometry.SimplicialComplex ℝ E) [Finite K.faces] (hA : A.faces ⊆ K.faces)
    {U : Set E} (hU : IsOpen U) (hAU : A.space ⊆ U) :
    ∃ R : Geometry.SimplicialComplex ℝ E, IsSubdivision R K ∧ R.faces.Finite ∧
      A.faces ⊆ R.faces ∧ (regularNeighborhoodIn R A.space).space ⊆ U := by
  let _ : Finite A.faces := ((Set.toFinite K.faces).subset hA).to_subtype
  obtain ⟨ε, hε, hthick⟩ := (isPolyhedron_space A).isCompact.exists_cthickening_subset_open hU hAU
  obtain ⟨R, hR, hfin, hAR, hsmall⟩ :=
    exists_isSubdivision_regularNeighborhoodIn_subset_cthickening K A hA hε
  exact ⟨R, hR, hfin, hAR, hsmall.trans hthick⟩

end DifferentialGeometry.Topology.PiecewiseLinear
