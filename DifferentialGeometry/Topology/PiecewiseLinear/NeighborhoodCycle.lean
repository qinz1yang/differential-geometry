import DifferentialGeometry.Topology.PiecewiseLinear.BallChain
import DifferentialGeometry.Topology.PiecewiseLinear.BoundaryDerivedNeighborhood
import DifferentialGeometry.Topology.PiecewiseLinear.OneManifoldClassification
import DifferentialGeometry.Topology.PiecewiseLinear.SurfaceSpanningTrees

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

open Classical in
noncomputable def barycentricVertexEquiv (K : Geometry.SimplicialComplex ℝ E) :
    K.faces ≃ (barycentricSubdivision K).vertices :=
  Equiv.ofBijective
    (fun s => ⟨s.val.centroid ℝ id, singleton_centroid_mem_barycentricSubdivision K s.property⟩)
    ⟨fun s t h => Subtype.ext (injOn_faces_of_mem_openSimplex K
      (centroid_mem_openSimplex_of_mem_faces K) s.property t.property (congrArg Subtype.val h)),
      fun v => by
        obtain ⟨s, hs, hsv⟩ := exists_eq_centroid_of_singleton_mem_barycentricSubdivision K v.property
        exact ⟨⟨s, hs⟩, Subtype.ext hsv⟩⟩

open Classical in
theorem barycentricVertexEquiv_apply (K : Geometry.SimplicialComplex ℝ E) (s : K.faces) :
    (barycentricVertexEquiv K s : E) = s.val.centroid ℝ id := rfl

open Classical in
theorem edgeGraph_barycentricVertexEquiv_adj_iff (K : Geometry.SimplicialComplex ℝ E)
    (s t : K.faces) :
    (SimplicialComplex.edgeGraph (barycentricSubdivision K)).Adj
      (barycentricVertexEquiv K s) (barycentricVertexEquiv K t) ↔
      s ≠ t ∧ (s.val ⊆ t.val ∨ t.val ⊆ s.val) := by
  rw [SimplicialComplex.edgeGraph_adj]
  constructor
  · intro h
    refine ⟨fun heq => h.1 (congrArg (barycentricVertexEquiv K) heq), ?_⟩
    exact subset_or_subset_of_centroid_mem_face K s.property t.property h.2
      (Finset.mem_insert_self _ _) (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
  · rintro ⟨hne, hcomp⟩
    exact ⟨fun heq => hne ((barycentricVertexEquiv K).injective heq),
      pair_centroid_mem_barycentricSubdivision_of_subset_or_subset K s.property t.property hcomp⟩

open Classical in
theorem exists_cyclic_face_order [FiniteDimensional ℝ E]
    (L : Geometry.SimplicialComplex ℝ E) [Finite L.faces]
    (hL : IsCombinatorialManifold 1 L) (hconn : IsConnected L.space) :
    ∃ n : ℕ, 3 ≤ n ∧ ∃ e : Fin n ≃ L.faces,
      ∀ i j, (SimpleGraph.cycleGraph n).Adj i j ↔
        e i ≠ e j ∧ ((e i).val ⊆ (e j).val ∨ (e j).val ⊆ (e i).val) := by
  let B := barycentricSubdivision L
  let _ : Fintype B.vertices := (SimplicialComplex.finite_vertices B).fintype
  have hB : IsCombinatorialManifold 1 B := hL.barycentricSubdivision
  have hBc : (SimplicialComplex.edgeGraph B).Connected :=
    edgeGraph_connected_of_isConnected_space B ((barycentricSubdivision_isSubdivision L).space_eq.symm ▸ hconn)
  have hdegree (v : B.vertices) : ((SimplicialComplex.edgeGraph B).neighborSet v).ncard = 2 := by
    rw [SimplicialComplex.ncard_neighborSet_edgeGraph]
    obtain ⟨a, b, hab, hpair⟩ := (isCombinatorialManifold_one_iff B).mp hB |>.2 v v.property
    convert hpair ▸ Set.ncard_pair hab using 1
  obtain ⟨g⟩ := (SimplicialComplex.edgeGraph B).exists_cycleGraphIsoOfConnectedDegreeTwo hBc hdegree
  let e := g.toEquiv.trans (barycentricVertexEquiv L).symm
  refine ⟨Fintype.card B.vertices,
    (SimplicialComplex.edgeGraph B).three_le_card_of_connected_degree_two hBc hdegree, e, ?_⟩
  intro i j
  have hgi : barycentricVertexEquiv L (e i) = g i := (barycentricVertexEquiv L).apply_symm_apply _
  have hgj : barycentricVertexEquiv L (e j) = g j := (barycentricVertexEquiv L).apply_symm_apply _
  rw [← edgeGraph_barycentricVertexEquiv_adj_iff, hgi, hgj]
  exact g.map_rel_iff.symm

open Classical in
theorem exists_cyclic_derivedNeighborhoodCell_decomposition [FiniteDimensional ℝ E]
    (K L : Geometry.SimplicialComplex ℝ E) [Finite K.faces] [Finite L.faces]
    (hK : IsCombinatorialManifoldWithBoundary 3 K) (hLK : L.faces ⊆ K.faces)
    (hL : IsCombinatorialManifold 1 L) (hconn : IsConnected L.space) :
    ∃ n : ℕ, 3 ≤ n ∧ ∃ e : Fin n ≃ L.faces,
      (⋃ i, (derivedNeighborhoodCell K (e i).val).space) = (derivedNeighborhood K L).space ∧
      (∀ i, IsPLBall 3 (derivedNeighborhoodCell K (e i).val).space) ∧
      ∀ i j, i ≠ j →
        (((derivedNeighborhoodCell K (e i).val).space ∩
          (derivedNeighborhoodCell K (e j).val).space).Nonempty ↔
            (SimpleGraph.cycleGraph n).Adj i j) ∧
        ((SimpleGraph.cycleGraph n).Adj i j →
          IsPLBall 2 ((derivedNeighborhoodCell K (e i).val).space ∩
            (derivedNeighborhoodCell K (e j).val).space) ∧
          (derivedNeighborhoodCell K (e i).val).space ∩
            (derivedNeighborhoodCell K (e j).val).space ⊆
              (boundaryComplex 3 (derivedNeighborhoodCell K (e i).val)).space ∧
          (derivedNeighborhoodCell K (e i).val).space ∩
            (derivedNeighborhoodCell K (e j).val).space ⊆
              (boundaryComplex 3 (derivedNeighborhoodCell K (e j).val)).space) := by
  obtain ⟨n, hn, e, hadj⟩ := exists_cyclic_face_order L hL hconn
  refine ⟨n, hn, e, ?_, fun i => hK.isPLBall_derivedNeighborhoodCell (hLK (e i).property), ?_⟩
  · calc
      (⋃ i, (derivedNeighborhoodCell K (e i).val).space) =
          ⋃ s : L.faces, (derivedNeighborhoodCell K s.val).space := e.surjective.iUnion_comp
            (fun s : L.faces => (derivedNeighborhoodCell K s.val).space)
      _ = (derivedNeighborhood K L).space := by
        simpa only [iUnion_subtype] using iUnion_derivedNeighborhoodCell_space K L hLK
  · intro i j hij
    have hne : (e i).val ≠ (e j).val := fun heq => hij (e.injective (Subtype.ext heq))
    have hs := hLK (e i).property
    have ht := hLK (e j).property
    have hball (hcomp : (e i).val ⊆ (e j).val ∨ (e j).val ⊆ (e i).val) :=
      hK.isPLBall_derivedNeighborhoodCell_inter hs ht hne hcomp
    refine ⟨⟨fun h => (hadj i j).mpr ⟨e.injective.ne hij,
      subset_or_subset_of_nonempty_derivedNeighborhoodCell_inter K hs ht h⟩,
      fun h => (hball ((hadj i j).mp h).2).nonempty⟩, fun h =>
        ⟨hball ((hadj i j).mp h).2,
          hK.derivedNeighborhoodCell_inter_subset_boundaryComplex hs ht hne, ?_⟩⟩
    simpa only [inter_comm] using hK.derivedNeighborhoodCell_inter_subset_boundaryComplex ht hs hne.symm

open Classical in
theorem disjoint_derivedNeighborhoodCell_inter_of_card_le_two
    (K L : Geometry.SimplicialComplex ℝ E) (hLK : L.faces ⊆ K.faces)
    (hcard : ∀ f ∈ L.faces, Finset.card f ≤ 2) {s t u : Finset E}
    (hs : s ∈ L.faces) (ht : t ∈ L.faces) (hu : u ∈ L.faces)
    (hst : s ≠ t) (hsu : s ≠ u) (htu : t ≠ u) :
    Disjoint ((derivedNeighborhoodCell K s).space ∩ (derivedNeighborhoodCell K t).space)
      (derivedNeighborhoodCell K u).space := by
  classical
  apply disjoint_left.mpr
  rintro x ⟨hxs, hxt⟩ hxu
  have hcs := subset_or_subset_of_nonempty_derivedNeighborhoodCell_inter K (hLK hs) (hLK ht)
    ⟨x, hxs, hxt⟩
  have hct := subset_or_subset_of_nonempty_derivedNeighborhoodCell_inter K (hLK hs) (hLK hu)
    ⟨x, hxs, hxu⟩
  have hcu := subset_or_subset_of_nonempty_derivedNeighborhoodCell_inter K (hLK ht) (hLK hu)
    ⟨x, hxt, hxu⟩
  have hne {a b : Finset E} (hab : a ≠ b) (hc : a ⊆ b ∨ b ⊆ a) : a.card ≠ b.card := by
    intro heq
    rcases hc with hc | hc
    · exact hab (Finset.eq_of_subset_of_card_le hc heq.ge)
    · exact hab (Finset.eq_of_subset_of_card_le hc heq.le).symm
  have hspos := Finset.card_pos.mpr (L.nonempty_of_mem_faces hs)
  have htpos := Finset.card_pos.mpr (L.nonempty_of_mem_faces ht)
  have hupos := Finset.card_pos.mpr (L.nonempty_of_mem_faces hu)
  have hsle := hcard s hs
  have htle := hcard t ht
  have hule := hcard u hu
  have hstcard := hne hst hcs
  have hsucard := hne hsu hct
  have htucard := hne htu hcu
  omega

private theorem cycleGraph_adj_last_iff {n : ℕ} (i : Fin (n + 2)) :
    (SimpleGraph.cycleGraph (n + 3)).Adj i.castSucc (Fin.last (n + 2)) ↔
      i = 0 ∨ i = Fin.last (n + 1) := by
  have hlt : i.castSucc < Fin.last (n + 2) := by
    change i.val < n + 2
    exact i.isLt
  rw [SimpleGraph.cycleGraph_adj', Fin.coe_sub_iff_lt.mpr hlt, Fin.sub_val_of_le hlt.le]
  simp only [Fin.val_castSucc, Fin.val_last]
  constructor
  · rintro (h | h)
    · exact Or.inl (Fin.ext (show i.val = 0 by omega))
    · exact Or.inr (Fin.ext (show i.val = n + 1 by omega))
  · rintro (rfl | rfl) <;> simp

open Classical in
theorem exists_isPLBall_pair_cover_derivedNeighborhood_circle_with_boundary [FiniteDimensional ℝ E]
    (K L : Geometry.SimplicialComplex ℝ E) [Finite K.faces] [Finite L.faces]
    (hK : IsCombinatorialManifoldWithBoundary 3 K) (hLK : L.faces ⊆ K.faces)
    (hL : IsCombinatorialManifold 1 L) (hconn : IsConnected L.space) :
    ∃ A B D₀ D₁ : Set E,
      IsPLBall 3 A ∧ IsPLBall 3 B ∧ IsPLBall 2 D₀ ∧ IsPLBall 2 D₁ ∧ Disjoint D₀ D₁ ∧
      A ∪ B = (derivedNeighborhood K L).space ∧ A ∩ B = D₀ ∪ D₁ ∧
      ∃ Q : Geometry.SimplicialComplex ℝ E, Q.faces.Finite ∧ Q.space = B ∧
        D₀ ⊆ (boundaryComplex 3 Q).space ∧ D₁ ⊆ (boundaryComplex 3 Q).space := by
  classical
  obtain ⟨n, hn, e, hcover, hball, hpair⟩ :=
    exists_cyclic_derivedNeighborhoodCell_decomposition K L hK hLK hL hconn
  obtain ⟨m, hm⟩ := Nat.exists_eq_add_of_le hn
  have hn' : n = m + 3 := by omega
  clear hm
  subst n
  let C : Fin (m + 3) → Set E := fun i => (derivedNeighborhoodCell K (e i).val).space
  let a : Fin (m + 3) := 0
  let b : Fin (m + 3) := (Fin.last (m + 1)).castSucc
  let c : Fin (m + 3) := Fin.last (m + 2)
  have hab : a ≠ b := by intro h; have := congrArg Fin.val h; dsimp [a, b] at this; omega
  have hac : a ≠ c := by intro h; have := congrArg Fin.val h; dsimp [a, c] at this; omega
  have hbc : b ≠ c := by intro h; have := congrArg Fin.val h; dsimp [b, c] at this; omega
  have hac_adj : (SimpleGraph.cycleGraph (m + 3)).Adj a c :=
    (cycleGraph_adj_last_iff (0 : Fin (m + 2))).mpr (Or.inl rfl)
  have hbc_adj : (SimpleGraph.cycleGraph (m + 3)).Adj b c :=
    (cycleGraph_adj_last_iff (Fin.last (m + 1))).mpr (Or.inr rfl)
  have hA : IsPLBall 3 (⋃ i : Fin (m + 2), C i.castSucc) :=
    hK.isPLBall_iUnion_castSucc_of_cycle C hball
      (fun i => derivedNeighborhoodCell_space_subset K (e i).val)
      (fun i j hij => ((hpair i j (SimpleGraph.Adj.ne hij)).2 hij).1)
      (fun i j hij hnot => disjoint_left.mpr fun x hxi hxj =>
        hnot ((hpair i j hij).1.mp ⟨x, hxi, hxj⟩))
  have hdis : Disjoint (C a ∩ C c) (C b ∩ C c) := by
    have ht := disjoint_derivedNeighborhoodCell_inter_of_card_le_two K L hLK
      (fun s hs => hL.card_le L hs) (e a).property (e b).property (e c).property
      (fun h => hab (e.injective (Subtype.ext h)))
      (fun h => hac (e.injective (Subtype.ext h)))
      (fun h => hbc (e.injective (Subtype.ext h)))
    exact disjoint_left.mpr fun x hx hy => disjoint_left.mp ht ⟨hx.1, hy.1⟩ hx.2
  refine ⟨⋃ i : Fin (m + 2), C i.castSucc, C c, C a ∩ C c, C b ∩ C c,
    hA, hball c, ((hpair a c hac).2 hac_adj).1, ((hpair b c hbc).2 hbc_adj).1,
    hdis, ?_, ?_, ?_⟩
  · rw [← hcover]
    ext x
    simp only [mem_union, mem_iUnion]
    constructor
    · rintro (⟨i, hi⟩ | hi)
      · exact ⟨i.castSucc, hi⟩
      · exact ⟨c, hi⟩
    · rintro ⟨i, hi⟩
      by_cases hic : i.val = m + 2
      · exact Or.inr ((show i = c from Fin.ext hic) ▸ hi)
      · let j : Fin (m + 2) := ⟨i.val, by omega⟩
        exact Or.inl ⟨j, show x ∈ C j.castSucc from (show i = j.castSucc from Fin.ext rfl) ▸ hi⟩
  · apply Subset.antisymm
    · rintro x ⟨hx, hxc⟩
      obtain ⟨i, hi⟩ := mem_iUnion.mp hx
      have hic : i.castSucc ≠ c := by
        intro heq
        have := congrArg Fin.val heq
        change i.val = m + 2 at this
        omega
      have hadj := (hpair i.castSucc c hic).1.mp ⟨x, hi, hxc⟩
      rcases (cycleGraph_adj_last_iff i).mp hadj with rfl | rfl
      · exact Or.inl ⟨hi, hxc⟩
      · exact Or.inr ⟨hi, hxc⟩
    · rintro x (hx | hx)
      · exact ⟨mem_iUnion.mpr ⟨0, hx.1⟩, hx.2⟩
      · exact ⟨mem_iUnion.mpr ⟨Fin.last (m + 1), hx.1⟩, hx.2⟩
  · exact ⟨derivedNeighborhoodCell K (e c).val, derivedNeighborhoodCell_faces_finite K (e c).val, rfl,
      ((hpair a c hac).2 hac_adj).2.2, ((hpair b c hbc).2 hbc_adj).2.2⟩

open Classical in
theorem exists_isPLBall_pair_cover_derivedNeighborhood_circle [FiniteDimensional ℝ E]
    (K L : Geometry.SimplicialComplex ℝ E) [Finite K.faces] [Finite L.faces]
    (hK : IsCombinatorialManifoldWithBoundary 3 K) (hLK : L.faces ⊆ K.faces)
    (hL : IsCombinatorialManifold 1 L) (hconn : IsConnected L.space) :
    ∃ A B D₀ D₁ : Set E,
      IsPLBall 3 A ∧ IsPLBall 3 B ∧ IsPLBall 2 D₀ ∧ IsPLBall 2 D₁ ∧ Disjoint D₀ D₁ ∧
      A ∪ B = (derivedNeighborhood K L).space ∧ A ∩ B = D₀ ∪ D₁ := by
  obtain ⟨A, B, D₀, D₁, hA, hB, hD₀, hD₁, hdis, hcover, hinter, _⟩ :=
    exists_isPLBall_pair_cover_derivedNeighborhood_circle_with_boundary K L hK hLK hL hconn
  exact ⟨A, B, D₀, D₁, hA, hB, hD₀, hD₁, hdis, hcover, hinter⟩

end DifferentialGeometry.Topology.PiecewiseLinear
