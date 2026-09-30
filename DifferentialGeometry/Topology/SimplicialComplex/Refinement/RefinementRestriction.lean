import DifferentialGeometry.Topology.PiecewiseLinear.Polyhedral.Maps.PolyhedralMap

namespace DifferentialGeometry.Topology.Engulfing

open Set _root_.Geometry

variable {E : Type*} [DecidableEq E] [NormedAddCommGroup E] [NormedSpace ℝ E]

omit [DecidableEq E] in
theorem simplicialRefines.face_card_le_bound
    {G K : SimplicialComplex ℝ E} (href : simplicialRefines G K)
    {d : ℕ} (hd : ∀ s ∈ K.faces, s.card ≤ d) :
    ∀ s ∈ G.faces, s.card ≤ d := by
  intro s hs
  obtain ⟨t, ht, hst⟩ := href s hs
  exact ((G.indep hs).card_le_card_of_subset_affineSpan
    (fun x hx => convexHull_subset_affineSpan _ (hst (subset_convexHull ℝ _ hx)))).trans
      (hd t ht)

omit [DecidableEq E] in
theorem simplicialRefines.convexHull_inter_old_face
    {G K : SimplicialComplex ℝ E} (href : simplicialRefines G K)
    {s t : Finset E} [DecidablePred (fun x => x ∈ convexHull ℝ (t : Set E))]
    (hs : s ∈ G.faces) (ht : t ∈ K.faces) :
    convexHull ℝ (s : Set E) ∩ convexHull ℝ (t : Set E) =
      convexHull ℝ (s.filter (fun x => x ∈ convexHull ℝ (t : Set E)) : Set E) := by
  classical
  obtain ⟨r, hr, hsr⟩ := href s hs
  obtain ⟨A, hA⟩ := exists_affineMap_of_affineIndependent (K.indep hr)
    (fun x : E => if x ∈ t then (0 : ℝ) else 1)
  have hAnonneg : ∀ x ∈ convexHull ℝ (r : Set E), 0 ≤ A x := by
    apply convexHull_min _ ((convex_Ici (0 : ℝ)).affine_preimage A)
    intro x hx
    change 0 ≤ A x
    rw [hA x hx]
    split_ifs <;> norm_num
  have hfilter : r.filter (fun x => A x = 0) = r ∩ t := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_inter]
    apply and_congr_right
    intro hx
    rw [hA x hx]
    split_ifs <;> simp_all
  have hparent : convexHull ℝ (r : Set E) ∩ {x | A x = 0} =
      convexHull ℝ (r : Set E) ∩ convexHull ℝ (t : Set E) := by
    rw [convexHull_inter_affine_zero_of_nonneg r A
      (fun x hx => hAnonneg x (subset_convexHull ℝ _ hx)), hfilter,
      K.convexHull_inter_convexHull hr ht]
    simp only [Finset.coe_inter]
  have hiff (x : E) (hx : x ∈ convexHull ℝ (s : Set E)) :
      A x = 0 ↔ x ∈ convexHull ℝ (t : Set E) := by
    have h := Set.ext_iff.mp hparent x
    simpa only [mem_inter_iff, mem_ofPred_eq, hsr hx, true_and] using h
  have hinter : convexHull ℝ (s : Set E) ∩ convexHull ℝ (t : Set E) =
      convexHull ℝ (s : Set E) ∩ {x | A x = 0} := by
    ext x
    exact and_congr_right (fun hx => (hiff x hx).symm)
  rw [hinter, convexHull_inter_affine_zero_of_nonneg s A
    (fun x hx => hAnonneg x (hsr (subset_convexHull ℝ _ hx)))]
  congr 2
  apply Finset.filter_congr
  intro x hx
  exact hiff x (subset_convexHull ℝ _ hx)

omit [DecidableEq E] in
theorem simplicialRefines.vertexRestriction_space
    {G K : SimplicialComplex ℝ E} (href : simplicialRefines G K)
    {t : Finset E} (ht : t ∈ K.faces) :
    (vertexRestriction G (convexHull ℝ (t : Set E))).space =
      G.space ∩ convexHull ℝ (t : Set E) := by
  classical
  exact vertexRestriction_space_of_facewise_inter G _
    (fun s hs => href.convexHull_inter_old_face hs ht)

omit [DecidableEq E] in
theorem complexRestriction_space_of_refines
    (G K H : SimplicialComplex ℝ E) (href : simplicialRefines G K)
    (hspace : G.space = K.space) (hHK : H.faces ⊆ K.faces) :
    (complexRestriction G H).space = H.space := by
  classical
  rw [complexRestriction_space_of_compatible G H
    (fun _ ht => href.vertexRestriction_space (hHK ht)), hspace]
  apply inter_eq_right.mpr
  intro x hx
  obtain ⟨s, hs, hxs⟩ := SimplicialComplex.mem_space_iff.mp hx
  exact K.convexHull_subset_space (hHK hs) hxs

end DifferentialGeometry.Topology.Engulfing
