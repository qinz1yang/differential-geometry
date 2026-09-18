import DifferentialGeometry.Topology.LoopSpace.InjectiveLoop
import DifferentialGeometry.Topology.PiecewiseLinear.CocycleWalkLift

namespace DifferentialGeometry.Topology.PiecewiseLinear

open Set SimpleGraph

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {K : Geometry.SimplicialComplex ℝ E}

open Classical in
theorem vertexPoint_coe (a : K.vertices) : ((vertexPoint K a : K.space) : E) = (a : E) := rfl

open Classical in
theorem edgePath_apply {a b : K.vertices} (hab : (SimplicialComplex.edgeGraph K).Adj a b)
    (t : unitInterval) :
    ((edgePath hab t : K.space) : E) = (1 - (t : ℝ)) • (a : E) + (t : ℝ) • (b : E) := rfl

open Classical in
theorem pair_mem_faces {a b : K.vertices} (hab : (SimplicialComplex.edgeGraph K).Adj a b) :
    ({(a : E), (b : E)} : Finset E) ∈ K.faces :=
  ((SimplicialComplex.edgeGraph_adj K a b).mp hab).2

theorem singleton_mem_faces (a : K.vertices) : ({(a : E)} : Finset E) ∈ K.faces := a.2

theorem faceHull_inter_subset {s t : Finset E} (hs : s ∈ K.faces) (ht : t ∈ K.faces)
    {S : Set E} (hS : Convex ℝ S) (hst : ∀ x ∈ s, x ∈ t → x ∈ S) :
    convexHull ℝ (s : Set E) ∩ convexHull ℝ (t : Set E) ⊆ S := by
  rw [Geometry.SimplicialComplex.convexHull_inter_convexHull hs ht]
  exact convexHull_min (fun x hx => hst x hx.1 hx.2) hS

open Classical in
theorem segment_eq_convexHull_pair (a b : E) :
    segment ℝ a b = convexHull ℝ (({a, b} : Finset E) : Set E) := by
  rw [Finset.coe_insert, Finset.coe_singleton, convexHull_pair]

open Classical in
theorem singleton_eq_convexHull (a : E) :
    ({a} : Set E) = convexHull ℝ (({a} : Finset E) : Set E) := by
  rw [Finset.coe_singleton, convexHull_singleton]

def pathCarrier {A B : K.space} (p : Path A B) : Set E :=
  Set.range fun t => ((p t : K.space) : E)

theorem pathCarrier_eq_image {A B : K.space} (p : Path A B) :
    pathCarrier p = (fun z : K.space => (z : E)) '' Set.range p :=
  Set.range_comp _ _

theorem pathCarrier_refl (A : K.space) : pathCarrier (Path.refl A) = {(A : E)} := by
  change Set.range (fun _ : unitInterval => (A : E)) = {(A : E)}
  exact Set.range_const

theorem pathCarrier_trans {A B C : K.space} (p : Path A B) (q : Path B C) :
    pathCarrier (p.trans q) = pathCarrier p ∪ pathCarrier q := by
  rw [pathCarrier_eq_image, pathCarrier_eq_image, pathCarrier_eq_image, Path.trans_range,
    Set.image_union]

open Classical in
theorem pathCarrier_edgePath {a b : K.vertices}
    (hab : (SimplicialComplex.edgeGraph K).Adj a b) :
    pathCarrier (edgePath hab) = segment ℝ (a : E) (b : E) := by
  have hfun : (fun t : unitInterval => ((edgePath hab t : K.space) : E)) =
      (fun θ : ℝ => (1 - θ) • (a : E) + θ • (b : E)) ∘ (fun t : unitInterval => (t : ℝ)) :=
    funext fun t => edgePath_apply hab t
  change Set.range (fun t : unitInterval => ((edgePath hab t : K.space) : E)) = _
  rw [hfun, Set.range_comp, Subtype.range_coe, segment_eq_image]

open Classical in
theorem edgePath_injective {a b : K.vertices} (hab : (SimplicialComplex.edgeGraph K).Adj a b) :
    Function.Injective (edgePath hab) := by
  intro s t hst
  have hval : (1 - (s : ℝ)) • (a : E) + (s : ℝ) • (b : E) =
      (1 - (t : ℝ)) • (a : E) + (t : ℝ) • (b : E) := by
    rw [← edgePath_apply hab s, ← edgePath_apply hab t, hst]
  have hne : (b : E) - (a : E) ≠ 0 := by
    intro h
    exact hab.1 (Subtype.ext (sub_eq_zero.mp h).symm)
  have hzero : ((s : ℝ) - (t : ℝ)) • ((b : E) - (a : E)) = 0 := by
    linear_combination (norm := module) hval
  rcases smul_eq_zero.mp hzero with h | h
  · exact Subtype.ext (by linarith [sub_eq_zero.mp h])
  · exact absurd h hne

open Classical in
noncomputable def arcPath : {u w : K.vertices} → (SimplicialComplex.edgeGraph K).Walk u w →
    Path (vertexPoint K u) (vertexPoint K w)
  | _, _, .nil => Path.refl _
  | _, _, .cons h .nil => edgePath h
  | _, _, .cons h (.cons h' p) => (edgePath h).trans (arcPath (.cons h' p))

open Classical in
theorem arcPath_nil (u : K.vertices) :
    arcPath (Walk.nil : (SimplicialComplex.edgeGraph K).Walk u u) =
      Path.refl (vertexPoint K u) := rfl

open Classical in
theorem arcPath_cons_nil {u v : K.vertices} (h : (SimplicialComplex.edgeGraph K).Adj u v) :
    arcPath (Walk.cons h Walk.nil) = edgePath h := rfl

open Classical in
theorem arcPath_cons_cons {u v w x : K.vertices}
    (h : (SimplicialComplex.edgeGraph K).Adj u v)
    (h' : (SimplicialComplex.edgeGraph K).Adj v w)
    (p : (SimplicialComplex.edgeGraph K).Walk w x) :
    arcPath (Walk.cons h (Walk.cons h' p)) = (edgePath h).trans (arcPath (Walk.cons h' p)) := rfl

open Classical in
theorem homotopic_walkPath_arcPath : ∀ {u w : K.vertices}
    (p : (SimplicialComplex.edgeGraph K).Walk u w), (walkPath p).Homotopic (arcPath p)
  | _, _, .nil => Path.Homotopic.refl _
  | _, _, .cons _ .nil => ⟨Path.Homotopy.transRefl _⟩
  | _, _, .cons _ (.cons h' p) =>
      (Path.Homotopic.refl _).hcomp (homotopic_walkPath_arcPath (Walk.cons h' p))

open Classical in
noncomputable def arcCarrier {u w : K.vertices}
    (p : (SimplicialComplex.edgeGraph K).Walk u w) : Set E := pathCarrier (arcPath p)

open Classical in
theorem arcCarrier_def {u w : K.vertices} (p : (SimplicialComplex.edgeGraph K).Walk u w) :
    arcCarrier p = pathCarrier (arcPath p) := rfl

open Classical in
theorem arcCarrier_nil (u : K.vertices) :
    arcCarrier (Walk.nil : (SimplicialComplex.edgeGraph K).Walk u u) = {(u : E)} :=
  pathCarrier_refl _

open Classical in
theorem arcCarrier_cons {u v w : K.vertices} (h : (SimplicialComplex.edgeGraph K).Adj u v)
    (p : (SimplicialComplex.edgeGraph K).Walk v w) :
    arcCarrier (Walk.cons h p) = segment ℝ (u : E) (v : E) ∪ arcCarrier p := by
  cases p with
  | nil =>
      rw [arcCarrier_def, arcPath_cons_nil, pathCarrier_edgePath, arcCarrier_def, arcPath_nil,
        pathCarrier_refl]
      exact (Set.union_eq_self_of_subset_right
        (Set.singleton_subset_iff.mpr (right_mem_segment ℝ _ _))).symm
  | cons h' q =>
      rw [arcCarrier_def, arcPath_cons_cons, pathCarrier_trans, pathCarrier_edgePath,
        arcCarrier_def]

open Classical in
theorem segment_inter_arcCarrier_eq_empty {a b : K.vertices}
    (hab : (SimplicialComplex.edgeGraph K).Adj a b) :
    ∀ {u w : K.vertices} (p : (SimplicialComplex.edgeGraph K).Walk u w),
      (∀ z ∈ p.support, z ≠ a ∧ z ≠ b) →
      segment ℝ (a : E) (b : E) ∩ arcCarrier p = ∅ := by
  intro u w p
  induction p with
  | @nil u =>
      intro hsup
      obtain ⟨hua, hub⟩ := hsup u (by simp)
      rw [arcCarrier_nil, segment_eq_convexHull_pair, singleton_eq_convexHull]
      refine Set.subset_eq_empty (faceHull_inter_subset (pair_mem_faces hab)
        (singleton_mem_faces u) convex_empty ?_) rfl
      intro x hx hx'
      simp only [Finset.mem_singleton] at hx'
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      subst hx'
      rcases hx with hx | hx
      · exact absurd (Subtype.ext hx.symm) hua.symm
      · exact absurd (Subtype.ext hx.symm) hub.symm
  | @cons u v w h q ih =>
      intro hsup
      have hq : ∀ z ∈ q.support, z ≠ a ∧ z ≠ b := fun z hz =>
        hsup z (by rw [Walk.support_cons]; exact List.mem_cons_of_mem _ hz)
      obtain ⟨hua, hub⟩ := hsup u (by rw [Walk.support_cons]; simp)
      obtain ⟨hva, hvb⟩ := hq v q.start_mem_support
      rw [arcCarrier_cons, Set.inter_union_distrib_left, ih hq, Set.union_empty]
      rw [segment_eq_convexHull_pair (a : E) (b : E), segment_eq_convexHull_pair (u : E) (v : E)]
      refine Set.subset_eq_empty (faceHull_inter_subset (pair_mem_faces hab)
        (pair_mem_faces h) convex_empty ?_) rfl
      intro x hx hx'
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx hx'
      rcases hx with hx | hx <;> rcases hx' with hx' | hx' <;> subst hx
      · exact absurd (Subtype.ext hx'.symm) hua
      · exact absurd (Subtype.ext hx'.symm) hva
      · exact absurd (Subtype.ext hx'.symm) hub
      · exact absurd (Subtype.ext hx'.symm) hvb

open Classical in
theorem segment_inter_arcCarrier_subset_singleton {a b : K.vertices}
    (hab : (SimplicialComplex.edgeGraph K).Adj a b) {w : K.vertices}
    (p : (SimplicialComplex.edgeGraph K).Walk b w)
    (ha : a ∉ p.support) (hb : b ∉ p.support.tail) :
    segment ℝ (a : E) (b : E) ∩ arcCarrier p ⊆ {(b : E)} := by
  cases p with
  | nil => rw [arcCarrier_nil]; exact Set.inter_subset_right
  | @cons _ c _ h' q =>
      rw [Walk.support_cons, List.tail_cons] at hb
      rw [Walk.support_cons] at ha
      have hac : a ≠ c := fun hh => ha (List.mem_cons_of_mem _ (hh ▸ q.start_mem_support))
      have hqsup : ∀ z ∈ q.support, z ≠ a ∧ z ≠ b :=
        fun z hz => ⟨fun hh => ha (List.mem_cons_of_mem _ (hh ▸ hz)), fun hh => hb (hh ▸ hz)⟩
      rw [arcCarrier_cons, Set.inter_union_distrib_left,
        segment_inter_arcCarrier_eq_empty hab q hqsup, Set.union_empty]
      rw [segment_eq_convexHull_pair (a : E) (b : E), segment_eq_convexHull_pair (b : E) (c : E)]
      refine faceHull_inter_subset (pair_mem_faces hab) (pair_mem_faces h')
        (convex_singleton _) ?_
      intro x hx hx'
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx hx'
      rcases hx with hx | hx <;> rcases hx' with hx' | hx' <;> subst hx
      · exact absurd (Subtype.ext hx'.symm) hab.1.symm
      · exact absurd (Subtype.ext hx'.symm) hac.symm
      · exact Set.mem_singleton _
      · exact Set.mem_singleton _

theorem range_inter_subset_of_pathCarrier_inter {A B C D : K.space} (p : Path A B) (q : Path C D)
    {z : E} (h : pathCarrier p ∩ pathCarrier q ⊆ {z}) :
    ∀ x ∈ Set.range p ∩ Set.range q, (x : E) = z := by
  rintro x ⟨⟨s, hs⟩, ⟨t, ht⟩⟩
  exact h ⟨⟨s, congrArg (fun z : K.space => (z : E)) hs⟩,
    ⟨t, congrArg (fun z : K.space => (z : E)) ht⟩⟩

open Classical in
theorem arcPath_injective : ∀ {u w : K.vertices} (p : (SimplicialComplex.edgeGraph K).Walk u w),
    p.IsPath → 0 < p.length → Function.Injective (arcPath p)
  | _, _, .nil, _, hlen => absurd hlen (by simp)
  | _, _, .cons h .nil, _, _ => by rw [arcPath_cons_nil]; exact edgePath_injective h
  | _, _, .cons h (.cons h' p), hpath, _ => by
      rw [arcPath_cons_cons]
      obtain ⟨hcons, hnotmem⟩ := (Walk.cons_isPath_iff _ _).mp hpath
      have hsub := segment_inter_arcCarrier_subset_singleton h (Walk.cons h' p) hnotmem
        (by rw [Walk.support_cons, List.tail_cons]
            exact ((Walk.cons_isPath_iff _ _).mp hcons).2)
      rw [← pathCarrier_edgePath h, arcCarrier_def] at hsub
      refine injective_trans (edgePath_injective h)
        (arcPath_injective (Walk.cons h' p) hcons (by simp)) fun x hx =>
          Subtype.ext (range_inter_subset_of_pathCarrier_inter _ _ hsub x hx)


open Classical in
theorem arcPath_cons_of_pos {u v w : K.vertices} (h : (SimplicialComplex.edgeGraph K).Adj u v)
    (p : (SimplicialComplex.edgeGraph K).Walk v w) (hp : 0 < p.length) :
    arcPath (Walk.cons h p) = (edgePath h).trans (arcPath p) := by
  cases p with
  | nil => exact absurd hp (by simp)
  | cons h' q => rfl

theorem pathCarrier_subset_space {A B : K.space} (p : Path A B) : pathCarrier p ⊆ K.space := by
  rintro x ⟨t, rfl⟩
  exact (p t).2

open Classical in
theorem mem_arcCarrier_of_mem_edges : ∀ {u w : K.vertices}
    (p : (SimplicialComplex.edgeGraph K).Walk u w) {a b : K.vertices},
    s(a, b) ∈ p.edges → segment ℝ (a : E) (b : E) ⊆ arcCarrier p := by
  intro u w p
  induction p with
  | nil => intro a b hab; simp at hab
  | @cons u v w h q ih =>
      intro a b hab
      rw [Walk.edges_cons, List.mem_cons] at hab
      rw [arcCarrier_cons]
      rcases hab with hab | hab
      · rw [Sym2.eq_iff] at hab
        rcases hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact Set.subset_union_left
        · rw [segment_symm]
          exact Set.subset_union_left
      · exact (ih hab).trans Set.subset_union_right

open Classical in
theorem mem_arcCarrier_of_mem_support : ∀ {u w : K.vertices}
    (p : (SimplicialComplex.edgeGraph K).Walk u w) {a : K.vertices},
    a ∈ p.support → (a : E) ∈ arcCarrier p := by
  intro u w p
  induction p with
  | @nil u =>
      intro a ha
      rw [arcCarrier_nil]
      simp only [Walk.support_nil, List.mem_singleton] at ha
      rw [ha]
      exact Set.mem_singleton _
  | @cons u v w h q ih =>
      intro a ha
      rw [Walk.support_cons, List.mem_cons] at ha
      rw [arcCarrier_cons]
      rcases ha with rfl | ha
      · exact Set.mem_union_left _ (left_mem_segment ℝ _ _)
      · exact Set.mem_union_right _ (ih ha)

open Classical in
theorem exists_edge_of_mem_arcCarrier : ∀ {u w : K.vertices}
    (p : (SimplicialComplex.edgeGraph K).Walk u w), 0 < p.length → ∀ x ∈ arcCarrier p,
    ∃ c d : K.vertices, s(c, d) ∈ p.edges ∧ x ∈ segment ℝ (c : E) (d : E)
  | _, _, .nil, hlen, _, _ => absurd hlen (by simp)
  | _, _, .cons h .nil, _, x, hx => by
      rename_i u v _
      rw [arcCarrier_cons, arcCarrier_nil] at hx
      refine ⟨u, v, by simp, ?_⟩
      rcases hx with hx | hx
      · exact hx
      · rw [Set.mem_singleton_iff] at hx
        rw [hx]
        exact right_mem_segment ℝ _ _
  | _, _, .cons h (.cons h' q), _, x, hx => by
      rw [arcCarrier_cons] at hx
      rcases hx with hx | hx
      · exact ⟨_, _, by simp, hx⟩
      · obtain ⟨c, d, hcd, hxcd⟩ :=
          exists_edge_of_mem_arcCarrier (Walk.cons h' q) (by simp) x hx
        exact ⟨c, d, by rw [Walk.edges_cons]; exact List.mem_cons_of_mem _ hcd, hxcd⟩

open Classical in
theorem segment_inter_arcCarrier_subset_pair {a b : K.vertices}
    (hab : (SimplicialComplex.edgeGraph K).Adj a b) {u w : K.vertices}
    (p : (SimplicialComplex.edgeGraph K).Walk u w) (hlen : 0 < p.length)
    (hnot : s(a, b) ∉ p.edges) :
    segment ℝ (a : E) (b : E) ∩ arcCarrier p ⊆ {(a : E), (b : E)} := by
  rintro x ⟨hx1, hx2⟩
  obtain ⟨c, d, hcd, hxcd⟩ := exists_edge_of_mem_arcCarrier p hlen x hx2
  have hcdadj : (SimplicialComplex.edgeGraph K).Adj c d := p.adj_of_mem_edges hcd
  have hne : s(a, b) ≠ s(c, d) := fun hh => hnot (hh ▸ hcd)
  have hkey : ¬ ((a = c ∨ a = d) ∧ (b = c ∨ b = d)) := by
    rintro ⟨h1, h2⟩
    apply hne
    rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
    · exact absurd (h1.trans h2.symm) hab.1
    · rw [h1, h2]
    · rw [h1, h2, Sym2.eq_swap]
    · exact absurd (h1.trans h2.symm) hab.1
  have hx1' : x ∈ convexHull ℝ ((({(a : E), (b : E)} : Finset E) : Set E)) := by
    rwa [← segment_eq_convexHull_pair]
  have hx2' : x ∈ convexHull ℝ ((({(c : E), (d : E)} : Finset E) : Set E)) := by
    rwa [← segment_eq_convexHull_pair]
  rcases not_and_or.mp hkey with hA | hB
  · replace hA := not_or.mp hA
    refine Or.inr (faceHull_inter_subset (pair_mem_faces hab) (pair_mem_faces hcdadj)
      (convex_singleton ((b : E))) ?_ ⟨hx1', hx2'⟩)
    intro y hy hy'
    simp only [Finset.mem_insert, Finset.mem_singleton] at hy hy'
    rcases hy with rfl | rfl
    · rcases hy' with hy' | hy'
      · exact absurd (Subtype.ext hy') hA.1
      · exact absurd (Subtype.ext hy') hA.2
    · exact Set.mem_singleton _
  · replace hB := not_or.mp hB
    refine Or.inl ?_
    have := faceHull_inter_subset (pair_mem_faces hab) (pair_mem_faces hcdadj)
      (convex_singleton ((a : E))) ?_ ⟨hx1', hx2'⟩
    · exact this
    · intro y hy hy'
      simp only [Finset.mem_insert, Finset.mem_singleton] at hy hy'
      rcases hy with rfl | rfl
      · exact Set.mem_singleton _
      · rcases hy' with hy' | hy'
        · exact absurd (Subtype.ext hy') hB.1
        · exact absurd (Subtype.ext hy') hB.2

end DifferentialGeometry.Topology.PiecewiseLinear
