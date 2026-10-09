/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactCarriers
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactDualSource

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [PseudoMetricSpace F]

theorem dist_image_lt_of_mem_closedStar {M : Geometry.SimplicialComplex ℝ E}
    {h : E → F} {δ η : ℝ}
    (hmesh : ∀ s ∈ M.faces, Metric.diam (convexHull ℝ (s : Set E)) < δ)
    (hclose : ∀ x ∈ M.space, ∀ y ∈ M.space, dist x y < δ → dist (h x) (h y) < η)
    {v x : E} (hx : x ∈ closedStar M v) : dist (h x) (h v) < η := by
  obtain ⟨s, ⟨hs, hvs⟩, hxs⟩ := mem_iUnion₂.mp hx
  exact hclose x (M.convexHull_subset_space hs hxs) v
    (M.convexHull_subset_space hs hvs)
    ((Metric.dist_le_diam_of_mem (s.finite_toSet.isCompact_convexHull ℝ).isBounded
      hxs hvs).trans_lt (hmesh s hs))

local notation "E3" => EuclideanSpace ℝ (Fin 3)

open Classical in
theorem exists_compactGraphCarriers
    (M K : Geometry.SimplicialComplex ℝ E3) [Finite M.faces]
    (hKM : K.faces ⊆ M.faces) {h : E3 → E3} (hh : ContinuousOn h M.space)
    {ε : ℝ} (hε : 0 < ε)
    (hstar : ∀ v ∈ K.vertices, ∀ x ∈ closedStar M v, dist (h x) (h v) < ε / 100) :
    ∃ H : Finset E3 → Set E3, Section34CompactCarrierControl K h ε H ∧
      ∀ t ∈ K.faces, ∀ v ∈ t,
        h '' (graphDualCell M (restrict K (section34CompactGraphSkeleton K)) v).space ⊆
          interior (H t) := by
  classical
  let : DecidableEq E3 := Classical.decEq E3
  let X : Finset E3 → Set E3 := fun t => h '' ⋃ v ∈ (t : Set E3), closedStar M v
  have hXM (t : Finset E3) : (⋃ v ∈ (t : Set E3), closedStar M v) ⊆ M.space :=
    iUnion₂_subset fun v _ => closedStar_subset_space M v
  have hXb (t : Finset E3) : Bornology.IsBounded (X t) :=
    ((SimplicialComplex.isCompact_geometricSpace M).image_of_continuousOn hh).isBounded.subset
      (image_mono (hXM t))
  have hvK {t : Finset E3} (ht : t ∈ K.faces) {v : E3} (hv : v ∈ t) : v ∈ K.vertices :=
    K.down_closed ht (Finset.singleton_subset_iff.mpr hv) (Finset.singleton_nonempty v)
  have hXd (t : Finset E3) (ht : t ∈ K.faces) : Metric.diam (X t) < ε / 4 := by
    obtain ⟨c, hc⟩ := K.nonempty_of_mem_faces ht
    have hrad : ∀ y ∈ X t, dist y (h c) < ε / 50 := by
      rintro y ⟨x, hx, rfl⟩
      obtain ⟨v, hv, hxv⟩ := mem_iUnion₂.mp hx
      have hcv : v ∈ closedStar M c := mem_iUnion₂.mpr
        ⟨t, ⟨hKM ht, subset_convexHull ℝ _ hc⟩, subset_convexHull ℝ _ hv⟩
      have h1 := hstar v (hvK ht hv) x hxv
      have h2 := hstar c (hvK ht hc) v hcv
      exact (dist_triangle (h x) (h v) (h c)).trans_lt (by linarith)
    have hdiam : Metric.diam (X t) ≤ ε / 25 :=
      Metric.diam_le_of_forall_dist_le (by positivity) fun y hy z hz =>
        (dist_triangle_right y z (h c)).trans (by linarith [hrad y hy, hrad z hz])
    exact hdiam.trans_lt (by linarith)
  have hsupport (t : Finset E3) (_ht : t ∈ K.faces) :
      h '' section34CompactCarrierSupport K t ⊆ X t := by
    apply image_mono
    rintro x hx
    obtain ⟨v, hvt, hx⟩ := mem_iUnion₂.mp hx
    obtain ⟨s, hs, hxs⟩ := mem_iUnion₂.mp hx
    exact mem_iUnion₂.mpr ⟨v, hvt, mem_iUnion₂.mpr
      ⟨s, ⟨hKM hs.1, subset_convexHull ℝ _ hs.2⟩, hxs⟩⟩
  obtain ⟨H, hH, hXH⟩ := exists_section34CompactCarrierControl K hε hsupport
    (fun t _ => hXb t) hXd
  refine ⟨H, hH, fun t ht v hv => (image_mono ?_).trans (hXH t ht)⟩
  exact (graphDualCell_space_subset_closedStar M _ v).trans
    ((closedStar_subset_of_isSubdivision (barycentricSubdivision_isSubdivision M) v).trans
      (subset_iUnion₂_of_subset v hv subset_rfl))

end DifferentialGeometry.Topology.PiecewiseLinear
