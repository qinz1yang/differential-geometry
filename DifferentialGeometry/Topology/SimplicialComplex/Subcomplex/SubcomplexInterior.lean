import DifferentialGeometry.Topology.SimplicialComplex.Refinement.RefinementSupport
import Mathlib.Topology.UnitInterval

namespace DifferentialGeometry.Topology.Engulfing

open Set _root_.Geometry Metric _root_.Topology

variable {E : Type*} [DecidableEq E] [NormedAddCommGroup E] [NormedSpace ℝ E]

omit [DecidableEq E] in
theorem face_subset_of_lineMap_centroid_mem (K : SimplicialComplex ℝ E)
    {s t : Finset E} (hs : s ∈ K.faces) (ht : t ∈ K.faces)
    {x : E} (hx : x ∈ convexHull ℝ (s : Set E)) {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1)
    (hy : AffineMap.lineMap x (s.centroid ℝ id) a ∈ convexHull ℝ (t : Set E)) : s ⊆ t := by
  classical
  obtain ⟨A, hA⟩ := exists_affineMap_of_affineIndependent (K.indep hs)
    (fun z : E => if z ∈ t then (0 : ℝ) else 1)
  have hnonneg : ∀ z ∈ convexHull ℝ (s : Set E), 0 ≤ A z := by
    apply convexHull_min _ ((convex_Ici (0 : ℝ)).affine_preimage A)
    intro z hz
    change 0 ≤ A z
    rw [hA z hz]
    split_ifs <;> norm_num
  have hzero : ∀ z ∈ convexHull ℝ ((s : Set E) ∩ (t : Set E)), A z = 0 := by
    apply convexHull_min _ ((convex_singleton (0 : ℝ)).affine_preimage A)
    intro z hz
    change A z = 0
    rw [hA z hz.1]
    exact ite_eq_left (show z ∈ t from hz.2)
  have hc : s.centroid ℝ id ∈ convexHull ℝ (s : Set E) :=
    s.centroid_mem_convexHull (K.nonempty_of_mem_faces hs)
  have hline := (convex_convexHull ℝ (s : Set E)).lineMap_mem hx hc ⟨ha.le, ha1⟩
  have hAzero := hzero _ (K.inter_subset_convexHull hs ht ⟨hline, hy⟩)
  have hAc : A (s.centroid ℝ id) = 0 := by
    have hAx := hnonneg x hx
    have hAc := hnonneg _ hc
    have hmap := A.apply_lineMap x (s.centroid ℝ id) a
    rw [hmap, AffineMap.lineMap_apply_ring] at hAzero
    nlinarith [mul_nonneg (sub_nonneg.mpr ha1) hAx]
  have hfilter : s.filter (fun z => A z = 0) = s ∩ t := by
    ext z
    simp only [Finset.mem_filter, Finset.mem_inter]
    apply and_congr_right
    intro hz
    rw [hA z hz]
    split_ifs <;> simp_all
  have hcst : s.centroid ℝ id ∈ convexHull ℝ ((s ∩ t : Finset E) : Set E) := by
    rw [← hfilter, ← convexHull_inter_affine_zero_of_nonneg s A
      (fun z hz => hnonneg z (subset_convexHull ℝ _ hz))]
    exact ⟨hc, hAc⟩
  apply face_subset_of_centroid_mem K hs ht
  exact convexHull_mono (show (s ∩ t : Finset E) ⊆ t from Finset.inter_subset_right) hcst

omit [DecidableEq E] in
theorem face_mem_subcomplex_of_mem_interior (K J : SimplicialComplex ℝ E)
    (hJK : J.faces ⊆ K.faces) {s : Finset E} (hs : s ∈ K.faces)
    {x : K.space} (hxs : x.val ∈ convexHull ℝ (s : Set E))
    (hxJ : x ∈ interior (Subtype.val ⁻¹' J.space : Set K.space)) : s ∈ J.faces := by
  classical
  let c := s.centroid ℝ id
  have hc : c ∈ convexHull ℝ (s : Set E) := s.centroid_mem_convexHull (K.nonempty_of_mem_faces hs)
  let w : unitInterval → K.space := fun a =>
    ⟨AffineMap.lineMap x.val c a.val,
      K.convexHull_subset_space hs ((convex_convexHull ℝ _).lineMap_mem hxs hc a.property)⟩
  have hw : Continuous w := by
    apply Continuous.subtype_mk
    simp only [AffineMap.lineMap_apply_module]
    fun_prop
  have hw0 : w 0 = x := by
    apply Subtype.ext
    simp [w]
  have hopen : IsOpen (w ⁻¹' interior (Subtype.val ⁻¹' J.space : Set K.space)) :=
    isOpen_interior.preimage hw
  have hzero : (0 : unitInterval) ∈ w ⁻¹' interior (Subtype.val ⁻¹' J.space : Set K.space) := by
    change w 0 ∈ interior (Subtype.val ⁻¹' J.space : Set K.space)
    rwa [hw0]
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp hopen 0 hzero
  let a : ℝ := min (δ / 2) (1 / 2)
  have ha : 0 < a := lt_min (half_pos hδ) (by norm_num)
  have ha1 : a ≤ 1 := (min_le_right _ _).trans (by norm_num)
  let aI : unitInterval := ⟨a, ha.le, ha1⟩
  have hnear : aI ∈ ball (0 : unitInterval) δ := by
    change dist a 0 < δ
    rw [Real.dist_eq, sub_zero, abs_of_pos ha]
    have := min_le_left (δ / 2) (1 / 2 : ℝ)
    dsimp [a]
    linarith
  have hyJ : (w aI).val ∈ J.space :=
    show w aI ∈ (Subtype.val ⁻¹' J.space : Set K.space) from
      interior_subset (hball hnear)
  obtain ⟨t, ht, hyt⟩ := SimplicialComplex.mem_space_iff.mp hyJ
  have hst := face_subset_of_lineMap_centroid_mem K hs (hJK ht) hxs ha ha1 hyt
  exact J.down_closed ht hst (K.nonempty_of_mem_faces hs)

end DifferentialGeometry.Topology.Engulfing
