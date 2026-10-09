import DifferentialGeometry.Topology.SimplicialComplex.Stellar.StellarEdgeWeights
import DifferentialGeometry.Topology.SimplicialComplex.Barycentric.Subdivision.FineSubdivision
import DifferentialGeometry.Topology.SimplicialComplex.Stellar.StellarEdgeCoverage

namespace DifferentialGeometry.Topology.Engulfing

open Set _root_.Geometry

set_option linter.unusedSectionVars false

variable {E : Type*} [DecidableEq E] [NormedAddCommGroup E] [NormedSpace ℝ E]

structure EdgeSubdivisionPoint (K : SimplicialComplex ℝ E) where
  a : E
  b : E
  p : E
  alpha : ℝ
  beta : ℝ
  endpoints_ne : a ≠ b
  edge_mem : {a, b} ∈ K.faces
  alpha_pos : 0 < alpha
  beta_pos : 0 < beta
  total : alpha + beta = 1
  point_eq : p = alpha • a + beta • b

namespace EdgeSubdivisionPoint

variable {K : SimplicialComplex ℝ E} (d : EdgeSubdivisionPoint K)

theorem point_mem_openSegment : d.p ∈ openSegment ℝ d.a d.b :=
  ⟨d.alpha, d.beta, d.alpha_pos, d.beta_pos, d.total, d.point_eq.symm⟩

theorem point_ne_left : d.p ≠ d.a := by
  intro h
  have hm := d.point_mem_openSegment
  rw [h, left_mem_openSegment_iff] at hm
  exact d.endpoints_ne hm

theorem point_ne_right : d.p ≠ d.b := by
  intro h
  have hm := d.point_mem_openSegment
  rw [h, right_mem_openSegment_iff] at hm
  exact d.endpoints_ne hm

theorem point_mem_edge : d.p ∈ convexHull ℝ ({d.a, d.b} : Set E) := by
  rw [convexHull_pair]
  exact openSegment_subset_segment _ _ _ d.point_mem_openSegment

theorem point_not_vertex : d.p ∉ K.vertices := by
  intro hp
  have hm : d.p ∈ ({d.a, d.b} : Finset E) :=
    (K.vertex_mem_convexHull_iff hp d.edge_mem).mp (by simpa using d.point_mem_edge)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  exact hm.elim d.point_ne_left d.point_ne_right

theorem point_not_mem_face {V : Finset E} (hV : V ∈ K.faces) : d.p ∉ V := by
  intro hp
  exact d.point_not_vertex (K.down_closed hV (Finset.singleton_subset_iff.mpr hp)
    (Finset.singleton_nonempty d.p))

def isFace (s : Finset E) : Prop :=
  s.Nonempty ∧ (d.a ∉ s ∨ d.b ∉ s) ∧
    ∃ V ∈ K.faces, s ⊆ insert d.p V ∧ (d.p ∈ s → d.a ∈ V ∧ d.b ∈ V)

theorem isFace.mono {s t : Finset E} (hs : d.isFace s) (hts : t ⊆ s)
    (ht : t.Nonempty) : d.isFace t :=
  ⟨ht, hs.2.1.imp (fun ha ht => ha (hts ht)) (fun hb ht => hb (hts ht)),
    let ⟨V, hV, hsV, hedge⟩ := hs.2.2
    ⟨V, hV, hts.trans hsV, fun hp => hedge (hts hp)⟩⟩

theorem old_face_isFace {s : Finset E} (hs : s ∈ K.faces)
    (hend : d.a ∉ s ∨ d.b ∉ s) : d.isFace s :=
  ⟨K.nonempty_of_mem_faces hs, hend, s, hs, Finset.subset_insert _ _,
    fun hp => (d.point_not_mem_face hs hp).elim⟩

theorem left_piece_isFace {V : Finset E} (hV : V ∈ K.faces)
    (ha : d.a ∈ V) (hb : d.b ∈ V) : d.isFace (insert d.p (V.erase d.a)) := by
  refine ⟨Finset.insert_nonempty _ _, Or.inl ?_, V, hV,
    Finset.insert_subset_insert _ (Finset.erase_subset _ _), fun _ => ⟨ha, hb⟩⟩
  simp [d.point_ne_left.symm]

theorem right_piece_isFace {V : Finset E} (hV : V ∈ K.faces)
    (ha : d.a ∈ V) (hb : d.b ∈ V) : d.isFace (insert d.p (V.erase d.b)) := by
  refine ⟨Finset.insert_nonempty _ _, Or.inr ?_, V, hV,
    Finset.insert_subset_insert _ (Finset.erase_subset _ _), fun _ => ⟨ha, hb⟩⟩
  simp [d.point_ne_right.symm]

theorem isFace.mem_original_of_point_not_mem {s : Finset E} (hs : d.isFace s)
    (hp : d.p ∉ s) : s ∈ K.faces := by
  obtain ⟨V, hV, hsV, -⟩ := hs.2.2
  apply K.down_closed hV _ hs.1
  intro x hx
  exact (Finset.mem_insert.mp (hsV hx)).resolve_left (fun he => hp (he ▸ hx))

theorem isFace.zero_endpoint {s : Finset E} (hs : d.isFace s) {w : E →₀ ℝ}
    (hw : w.support ⊆ s) : w d.a = 0 ∨ w d.b = 0 := by
  rcases hs.2.1 with ha | hb
  · exact Or.inl (Finsupp.notMem_support_iff.mp (fun h => ha (hw h)))
  · exact Or.inr (Finsupp.notMem_support_iff.mp (fun h => hb (hw h)))

theorem expand_support_subset {s V : Finset E} (hsV : s ⊆ insert d.p V)
    (hedge : d.p ∈ s → d.a ∈ V ∧ d.b ∈ V) {w : E →₀ ℝ} (hw : w.support ⊆ s) :
    (expandEdgeWeights d.a d.b d.p d.alpha d.beta w).support ⊆ V := by
  intro v hv
  by_contra hn
  apply Finsupp.mem_support_iff.mp hv
  rw [expandEdgeWeights_apply]
  by_cases hp : d.p ∈ s
  · have hva : d.a ≠ v := fun h => hn (h ▸ (hedge hp).1)
    have hvb : d.b ≠ v := fun h => hn (h ▸ (hedge hp).2)
    simp only [hva, hvb, ite_false, add_zero]
    by_cases hpe : d.p = v
    · subst v
      simp
    · have hwv : w v = 0 := Finsupp.notMem_support_iff.mp (fun h =>
        (Finset.mem_insert.mp (hsV (hw h))).elim (fun h => hpe h.symm) hn)
      simp [hpe, hwv]
  · have hwp : w d.p = 0 := Finsupp.notMem_support_iff.mp (fun h => hp (hw h))
    have hwv : w v = 0 := Finsupp.notMem_support_iff.mp (fun hmem =>
      (Finset.mem_insert.mp (hsV (hw hmem))).elim
        (fun he => hp (he ▸ hw hmem)) hn)
    simp [hwp, hwv]

theorem isFace.affineIndependent {s : Finset E} (hs : d.isFace s) :
    AffineIndependent ℝ ((↑) : s → E) := by
  apply affineIndependent_of_weights_eq_zero
  intro w hw hm hp
  obtain ⟨V, hV, hsV, hedge⟩ := hs.2.2
  have hz : expandEdgeWeights d.a d.b d.p d.alpha d.beta w = 0 :=
    weights_eq_zero_of_affineIndependent (K.indep hV)
      (d.expand_support_subset hsV hedge hw)
      ((expandEdgeWeights_mass _ _ _ d.total w).trans hm)
      ((expandEdgeWeights_point d.point_eq w).trans hp)
  exact expandEdgeWeights_eq_zero d.endpoints_ne d.point_ne_left d.point_ne_right
    d.alpha_pos.ne' d.beta_pos.ne' (hs.zero_endpoint d hw) hz

theorem isFace.convexHull_inter {s t : Finset E} (hs : d.isFace s) (ht : d.isFace t) :
    convexHull ℝ (s : Set E) ∩ convexHull ℝ (t : Set E) =
      convexHull ℝ ((s : Set E) ∩ (t : Set E)) := by
  apply Subset.antisymm
  · intro x hx
    obtain ⟨w, hws, hw, hwm, hwp⟩ := (mem_convexHull_iff_weights s x).mp hx.1
    obtain ⟨z, hzt, hz, hzm, hzp⟩ := (mem_convexHull_iff_weights t x).mp hx.2
    obtain ⟨V, hV, hsV, hedgeV⟩ := hs.2.2
    obtain ⟨W, hW, htW, hedgeW⟩ := ht.2.2
    have hexp := convexWeights_eq_of_complex K hV hW
      (d.expand_support_subset hsV hedgeV hws) (d.expand_support_subset htW hedgeW hzt)
      (expandEdgeWeights_nonneg d.point_ne_left d.point_ne_right d.alpha_pos.le d.beta_pos.le hw)
      (expandEdgeWeights_nonneg d.point_ne_left d.point_ne_right d.alpha_pos.le d.beta_pos.le hz)
      ((expandEdgeWeights_mass _ _ _ d.total w).trans hwm)
      ((expandEdgeWeights_mass _ _ _ d.total z).trans hzm)
      ((expandEdgeWeights_point d.point_eq w).trans
        (hwp.trans (hzp.symm.trans (expandEdgeWeights_point d.point_eq z).symm)))
    have heq : w = z := expandEdgeWeights_inj d.endpoints_ne d.point_ne_left d.point_ne_right
      d.alpha_pos d.beta_pos hw hz (hs.zero_endpoint d hws) (ht.zero_endpoint d hzt) hexp
    have hwt : w.support ⊆ t := heq ▸ hzt
    have hm := (mem_convexHull_iff_weights (s ∩ t) x).mpr
      ⟨w, Finset.subset_inter hws hwt, hw, hwm, hwp⟩
    simpa only [Finset.coe_inter] using hm
  · intro x hx
    exact ⟨convexHull_mono inter_subset_left hx, convexHull_mono inter_subset_right hx⟩

noncomputable def subdivision : SimplicialComplex ℝ E where
  faces := {s | d.isFace s}
  isRelLowerSet_faces := fun _ hs => ⟨hs.1, fun _ hts ht => hs.mono d hts ht⟩
  indep := fun hs => hs.affineIndependent d
  inter_subset_convexHull := fun hs ht => (hs.convexHull_inter d ht).subset

theorem convexHull_subset_parent {s V : Finset E} (hsV : s ⊆ insert d.p V)
    (hedge : d.p ∈ s → d.a ∈ V ∧ d.b ∈ V) :
    convexHull ℝ (s : Set E) ⊆ convexHull ℝ (V : Set E) := by
  apply convexHull_min _ (convex_convexHull ℝ (V : Set E))
  intro v hv
  rcases Finset.mem_insert.mp (hsV hv) with rfl | hV
  · apply convexHull_mono _ d.point_mem_edge
    intro x hx
    rcases hx with rfl | rfl
    · exact (hedge hv).1
    · exact (hedge hv).2
  · exact subset_convexHull ℝ _ hV

theorem subdivision_refines : simplicialRefines d.subdivision K := by
  intro s hs
  obtain ⟨V, hV, hsV, hedge⟩ := hs.2.2
  exact ⟨V, hV, d.convexHull_subset_parent hsV hedge⟩

theorem subdivision_space_subset : d.subdivision.space ⊆ K.space := by
  intro x hx
  obtain ⟨s, hs, hxs⟩ := SimplicialComplex.mem_space_iff.mp hx
  obtain ⟨V, hV, hsV⟩ := d.subdivision_refines s hs
  exact K.convexHull_subset_space hV (hsV hxs)

theorem subdivision_space : d.subdivision.space = K.space := by
  apply d.subdivision_space_subset.antisymm
  intro x hx
  obtain ⟨V, hV, hxV⟩ := SimplicialComplex.mem_space_iff.mp hx
  by_cases ha : d.a ∈ V
  · by_cases hb : d.b ∈ V
    · have hcover := convexHull_eq_union_stellar_edge ha hb d.endpoints_ne
        (openSegment_subset_segment _ _ _ d.point_mem_openSegment)
      rw [hcover] at hxV
      rcases hxV with hxleft | hxright
      · exact d.subdivision.convexHull_subset_space (d.left_piece_isFace hV ha hb) hxleft
      · exact d.subdivision.convexHull_subset_space (d.right_piece_isFace hV ha hb) hxright
    · exact d.subdivision.convexHull_subset_space (d.old_face_isFace hV (Or.inr hb)) hxV
  · exact d.subdivision.convexHull_subset_space (d.old_face_isFace hV (Or.inl ha)) hxV

theorem subdivision_finite_faces (hK : K.faces.Finite) : d.subdivision.faces.Finite := by
  apply (hK.biUnion (fun V _ => (insert d.p V).powerset.finite_toSet)).subset
  intro s hs
  obtain ⟨V, hV, hsV, -⟩ := hs.2.2
  exact mem_biUnion hV (Finset.mem_powerset.mpr hsV)

theorem isFace.card_le_parent {s V : Finset E} (hs : d.isFace s)
    (hV : V ∈ K.faces) (hsV : s ⊆ insert d.p V)
    (hedge : d.p ∈ s → d.a ∈ V ∧ d.b ∈ V) : s.card ≤ V.card := by
  by_cases hp : d.p ∈ s
  · obtain ⟨e, hes, heV⟩ : ∃ e, e ∉ s ∧ e ∈ V := by
      rcases hs.2.1 with ha | hb
      · exact ⟨d.a, ha, (hedge hp).1⟩
      · exact ⟨d.b, hb, (hedge hp).2⟩
    have hsub : insert e s ⊆ insert d.p V := Finset.insert_subset_iff.mpr
      ⟨Finset.mem_insert_of_mem heV, hsV⟩
    have hcard := Finset.card_le_card hsub
    rw [Finset.card_insert_of_notMem hes,
      Finset.card_insert_of_notMem (d.point_not_mem_face hV)] at hcard
    omega
  · apply Finset.card_le_card
    intro x hx
    exact (Finset.mem_insert.mp (hsV hx)).resolve_left (fun he => hp (he ▸ hx))

theorem subdivision_face_card_le {n : ℕ} (hK : ∀ V ∈ K.faces, V.card ≤ n + 1) :
    ∀ s ∈ d.subdivision.faces, s.card ≤ n + 1 := by
  intro s hs
  obtain ⟨V, hV, hsV, hedge⟩ := hs.2.2
  exact (hs.card_le_parent d hV hsV hedge).trans (hK V hV)

end EdgeSubdivisionPoint

end DifferentialGeometry.Topology.Engulfing
