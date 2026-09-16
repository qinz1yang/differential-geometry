import DifferentialGeometry.Topology.PiecewiseLinear.ManifoldConnectivity
import DifferentialGeometry.Topology.PiecewiseLinear.Orientation
import DifferentialGeometry.Topology.SimplicialComplex.ConnectedSpace
import DifferentialGeometry.Topology.Combinatorics.EvenDegree
import Mathlib.Combinatorics.SimpleGraph.Acyclic

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

open Classical in
theorem edgeGraph_connected_of_isConnected_space
    [FiniteDimensional ℝ E] (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsConnected K.space) : (SimplicialComplex.edgeGraph K).Connected := by
  let _ : Finite K.vertices := (SimplicialComplex.finite_vertices K).to_subtype
  obtain ⟨x, hx⟩ := hK.nonempty
  obtain ⟨s, hs, -⟩ := K.mem_space_iff.mp hx
  obtain ⟨v, hv⟩ := K.nonempty_of_mem_faces hs
  let a : K.vertices := ⟨v, K.down_closed hs (Finset.singleton_subset_iff.mpr hv)
    (Finset.singleton_nonempty v)⟩
  let _ : Nonempty K.vertices := ⟨a⟩
  refine ⟨fun u w => ?_⟩
  by_contra huw
  let P : Set E := ⋃ z : {z : K.vertices //
      (SimplicialComplex.edgeGraph K).Reachable u z}, closedStar K z
  let Q : Set E := ⋃ z : {z : K.vertices //
      ¬(SimplicialComplex.edgeGraph K).Reachable u z}, closedStar K z
  have hP : IsClosed P := isClosed_iUnion_of_finite fun z => by
    rw [← starComplex_space K z z.1.2]
    let _ : Finite (starComplex K z).faces := (starComplex_faces_finite K z).to_subtype
    exact (isPolyhedron_space (starComplex K z)).isClosed
  have hQ : IsClosed Q := isClosed_iUnion_of_finite fun z => by
    rw [← starComplex_space K z z.1.2]
    let _ : Finite (starComplex K z).faces := (starComplex_faces_finite K z).to_subtype
    exact (isPolyhedron_space (starComplex K z)).isClosed
  have hcover : K.space ⊆ P ∪ Q := by
    rw [space_eq_iUnion_closedStar K]
    apply iUnion_subset
    intro z y hy
    by_cases hz : (SimplicialComplex.edgeGraph K).Reachable u z
    · exact Or.inl (mem_iUnion.mpr ⟨⟨z, hz⟩, hy⟩)
    · exact Or.inr (mem_iUnion.mpr ⟨⟨z, hz⟩, hy⟩)
  have huP : (u : E) ∈ K.space ∩ P := by
    refine ⟨K.vertices_subset_space u.2, mem_iUnion.mpr ⟨⟨u, SimpleGraph.Reachable.rfl⟩, ?_⟩⟩
    exact mem_closedStar_of_singleton_mem K u.2
  have hwQ : (w : E) ∈ K.space ∩ Q := by
    refine ⟨K.vertices_subset_space w.2, mem_iUnion.mpr ⟨⟨w, huw⟩, ?_⟩⟩
    exact mem_closedStar_of_singleton_mem K w.2
  obtain ⟨y, -, hyP, hyQ⟩ := isPreconnected_closed_iff.mp hK.isPreconnected P Q hP hQ hcover
    ⟨_, huP⟩ ⟨_, hwQ⟩
  obtain ⟨z, hyz⟩ := mem_iUnion.mp hyP
  obtain ⟨z', hyz'⟩ := mem_iUnion.mp hyQ
  rw [← starComplex_space K z z.1.2] at hyz
  rw [← starComplex_space K z' z'.1.2] at hyz'
  obtain ⟨s, hs, hys⟩ := (starComplex K z).mem_space_iff.mp hyz
  obtain ⟨t, ht, hyt⟩ := (starComplex K z').mem_space_iff.mp hyz'
  have hinter := K.inter_subset_convexHull hs.1 ht.1 ⟨hys, hyt⟩
  obtain ⟨p, hp⟩ := convexHull_nonempty_iff.mp ⟨y, hinter⟩
  have hpK : p ∈ K.vertices := K.down_closed hs.1
    (Finset.singleton_subset_iff.mpr hp.1) (Finset.singleton_nonempty p)
  let p' : K.vertices := ⟨p, hpK⟩
  have hzp : (SimplicialComplex.edgeGraph K).Reachable z p' := by
    by_cases h : z = p'
    · exact h ▸ SimpleGraph.Reachable.rfl
    · exact SimpleGraph.Adj.reachable ⟨h, by
        apply K.down_closed hs.2
        · intro q hq
          simp only [Finset.mem_insert, Finset.mem_singleton] at hq
          rcases hq with rfl | rfl
          · exact Finset.mem_insert_self _ _
          · exact Finset.mem_insert_of_mem hp.1
        · simp⟩
  have hz'p : (SimplicialComplex.edgeGraph K).Reachable z' p' := by
    by_cases h : z' = p'
    · exact h ▸ SimpleGraph.Reachable.rfl
    · exact SimpleGraph.Adj.reachable ⟨h, by
        apply K.down_closed ht.2
        · intro q hq
          simp only [Finset.mem_insert, Finset.mem_singleton] at hq
          rcases hq with rfl | rfl
          · exact Finset.mem_insert_self _ _
          · exact Finset.mem_insert_of_mem hp.2
        · simp⟩
  exact z'.2 (z.2.trans (hzp.trans hz'p.symm))

open Classical in
theorem exists_edgeGraph_spanningTree
    [FiniteDimensional ℝ E] (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsConnected K.space) :
    ∃ T ≤ SimplicialComplex.edgeGraph K, T.IsTree :=
  (edgeGraph_connected_of_isConnected_space K hK).exists_isTree_le

open Classical in
noncomputable def edgeGraphFace (K : Geometry.SimplicialComplex ℝ E)
    (e : Sym2 K.vertices) : Finset E :=
  (e.map ((↑) : K.vertices → E)).toFinset

private theorem sym2_eq_of_toFinset_eq_of_not_isDiag {α : Type*} [DecidableEq α]
    {e f : Sym2 α} (he : ¬e.IsDiag) (hf : ¬f.IsDiag) (h : e.toFinset = f.toFinset) : e = f := by
  induction e using Sym2.inductionOn with
  | _ a b =>
    induction f using Sym2.inductionOn with
    | _ c d =>
      rw [Sym2.mk_isDiag_iff] at he hf
      rw [Sym2.toFinset_mk_eq, Sym2.toFinset_mk_eq] at h
      have ha : a = c ∨ a = d := by
        have : a ∈ ({c, d} : Finset α) := by rw [← h]; simp
        simpa using this
      have hb : b = c ∨ b = d := by
        have : b ∈ ({c, d} : Finset α) := by rw [← h]; simp
        simpa using this
      rw [Sym2.eq_iff]
      rcases ha with hac | had
      · exact Or.inl ⟨hac, hb.resolve_left fun hbc => he (hac.trans hbc.symm)⟩
      · exact Or.inr ⟨had, hb.resolve_right fun hbd => he (had.trans hbd.symm)⟩

open Classical in
theorem edgeGraphFace_mem_facesOfCard_two
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    {e : Sym2 K.vertices} (he : e ∈ (SimplicialComplex.edgeGraph K).edgeSet) :
    edgeGraphFace K e ∈
      SimplicialComplex.facesOfCard K.toPreAbstractSimplicialComplex 2 := by
  induction e using Sym2.inductionOn with
  | _ u v =>
    have huv : (SimplicialComplex.edgeGraph K).Adj u v :=
      (SimplicialComplex.edgeGraph K).mem_edgeSet.mp he
    have huv' : (u : E) ≠ (v : E) := fun h => huv.1 (Subtype.ext h)
    rw [SimplicialComplex.mem_facesOfCard]
    constructor
    · change edgeGraphFace K s(u, v) ∈ K.faces
      simpa only [edgeGraphFace, Sym2.map_mk, Sym2.toFinset_mk_eq] using huv.2
    · simpa only [edgeGraphFace, Sym2.map_mk, Sym2.toFinset_mk_eq] using
        Finset.card_pair huv'

open Classical in
theorem edgeGraphFace_injOn_edgeSet
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces] :
    Set.InjOn (edgeGraphFace K) (SimplicialComplex.edgeGraph K).edgeSet := by
  intro e he f hf h
  apply (Sym2.map.injective Subtype.val_injective)
  apply sym2_eq_of_toFinset_eq_of_not_isDiag
  · rw [Sym2.isDiag_map Subtype.val_injective]
    exact (SimplicialComplex.edgeGraph K).not_isDiag_of_mem_edgeSet he
  · rw [Sym2.isDiag_map Subtype.val_injective]
    exact (SimplicialComplex.edgeGraph K).not_isDiag_of_mem_edgeSet hf
  · exact h

open Classical in
theorem edgeGraphFace_surjOn_facesOfCard_two
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces] :
    Set.SurjOn (edgeGraphFace K) (SimplicialComplex.edgeGraph K).edgeSet
      {s | s ∈ SimplicialComplex.facesOfCard K.toPreAbstractSimplicialComplex 2} := by
  intro s hs
  obtain ⟨hsK, hscard⟩ :=
    (SimplicialComplex.mem_facesOfCard K.toPreAbstractSimplicialComplex).mp hs
  obtain ⟨u, v, huv, rfl⟩ := Finset.card_eq_two.mp hscard
  have huK : u ∈ K.vertices := K.down_closed hsK (by simp) (Finset.singleton_nonempty u)
  have hvK : v ∈ K.vertices := K.down_closed hsK (by simp) (Finset.singleton_nonempty v)
  let u' : K.vertices := ⟨u, huK⟩
  let v' : K.vertices := ⟨v, hvK⟩
  refine ⟨s(u', v'), ?_, ?_⟩
  · rw [(SimplicialComplex.edgeGraph K).mem_edgeSet]
    exact ⟨fun h => huv (congrArg Subtype.val h), hsK⟩
  · simp only [edgeGraphFace, Sym2.map_mk, Sym2.toFinset_mk_eq, u', v']

open Classical in
theorem ncard_edgeSet_edgeGraph_eq_facesOfCard_two
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces] :
    (SimplicialComplex.edgeGraph K).edgeSet.ncard =
      (SimplicialComplex.facesOfCard K.toPreAbstractSimplicialComplex 2).card := by
  let _ : Finite K.vertices := (SimplicialComplex.finite_vertices K).to_subtype
  let G := SimplicialComplex.edgeGraph K
  let S : Set (Finset E) :=
    {s | s ∈ SimplicialComplex.facesOfCard K.toPreAbstractSimplicialComplex 2}
  have hb : Set.BijOn (edgeGraphFace K) G.edgeSet S :=
    ⟨fun e he => edgeGraphFace_mem_facesOfCard_two K he,
      edgeGraphFace_injOn_edgeSet K, edgeGraphFace_surjOn_facesOfCard_two K⟩
  calc
    G.edgeSet.ncard = S.ncard := hb.ncard_eq
    _ = (SimplicialComplex.facesOfCard K.toPreAbstractSimplicialComplex 2).card := by
      rw [show S = ↑(SimplicialComplex.facesOfCard
        K.toPreAbstractSimplicialComplex 2) by
          ext s
          change (s ∈ SimplicialComplex.facesOfCard K.toPreAbstractSimplicialComplex 2) ↔ _
          rfl]
      simp

open Classical in
noncomputable def vertexFace (K : Geometry.SimplicialComplex ℝ E)
    (v : K.vertices) : Finset E :=
  {(v : E)}

open Classical in
theorem vertexFace_bijOn_facesOfCard_one
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces] :
    Set.BijOn (vertexFace K) Set.univ
      {s | s ∈ SimplicialComplex.facesOfCard K.toPreAbstractSimplicialComplex 1} := by
  refine ⟨?_, ?_, ?_⟩
  · intro v _
    apply (SimplicialComplex.mem_facesOfCard K.toPreAbstractSimplicialComplex).mpr
    exact ⟨v.2, Finset.card_singleton _⟩
  · intro u _ v _ h
    apply Subtype.ext
    simpa only [vertexFace, Finset.singleton_inj] using h
  · intro s hs
    obtain ⟨hsK, hscard⟩ :=
      (SimplicialComplex.mem_facesOfCard K.toPreAbstractSimplicialComplex).mp hs
    obtain ⟨v, rfl⟩ := Finset.card_eq_one.mp hscard
    refine ⟨⟨v, hsK⟩, Set.mem_univ _, ?_⟩
    rfl

open Classical in
theorem ncard_vertices_eq_facesOfCard_one
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces] :
    K.vertices.ncard =
      (SimplicialComplex.facesOfCard K.toPreAbstractSimplicialComplex 1).card := by
  let S : Set (Finset E) :=
    {s | s ∈ SimplicialComplex.facesOfCard K.toPreAbstractSimplicialComplex 1}
  have hb : Set.BijOn (vertexFace K) Set.univ S := vertexFace_bijOn_facesOfCard_one K
  calc
    K.vertices.ncard = (Set.univ : Set K.vertices).ncard := by simp
    _ = S.ncard := hb.ncard_eq
    _ = (SimplicialComplex.facesOfCard K.toPreAbstractSimplicialComplex 1).card := by
      rw [show S = ↑(SimplicialComplex.facesOfCard
        K.toPreAbstractSimplicialComplex 1) by
          ext s
          change (s ∈ SimplicialComplex.facesOfCard K.toPreAbstractSimplicialComplex 1) ↔ _
          rfl]
      simp

open Classical in
noncomputable def dualGraphSharedFace (K : Geometry.SimplicialComplex ℝ E)
    (e : Sym2 {s : Finset E // s ∈ K.faces ∧ s.card = 3}) : Finset E :=
  Sym2.lift ⟨fun s t => s.1 ∩ t.1, fun s t => Finset.inter_comm s.1 t.1⟩ e

open Classical in
theorem dualGraph_sharedFace_mem_facesOfCard_two
    [FiniteDimensional ℝ E] (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    {s t : {s : Finset E // s ∈ K.faces ∧ s.card = 3}}
    (hst : (dualGraph 2 K).Adj s t) :
    s.1 ∩ t.1 ∈ SimplicialComplex.facesOfCard K.toPreAbstractSimplicialComplex 2 := by
  obtain ⟨hstne, f, hfK, hfcard, hfs, hft⟩ := hst
  have hfsub : f ⊆ s.1 ∩ t.1 := Finset.subset_inter hfs hft
  have hlower : 2 ≤ (s.1 ∩ t.1).card := by
    rw [← hfcard]
    exact Finset.card_le_card hfsub
  have hupper : (s.1 ∩ t.1).card ≤ 3 := by
    calc
      (s.1 ∩ t.1).card ≤ s.1.card := Finset.card_le_card Finset.inter_subset_left
      _ = 3 := s.2.2
  have hnotthree : (s.1 ∩ t.1).card ≠ 3 := by
    intro hcard
    have hinterS : s.1 ∩ t.1 = s.1 := Finset.eq_of_subset_of_card_le
      Finset.inter_subset_left (by rw [hcard, s.2.2])
    have hstsub : s.1 ⊆ t.1 := hinterS ▸ Finset.inter_subset_right
    have hsteq : s = t := Subtype.ext (Finset.eq_of_subset_of_card_le hstsub (by
      rw [s.2.2, t.2.2]))
    exact hstne hsteq
  have hintercard : (s.1 ∩ t.1).card = 2 := by omega
  apply (SimplicialComplex.mem_facesOfCard K.toPreAbstractSimplicialComplex).mpr
  refine ⟨K.down_closed s.2.1 Finset.inter_subset_left ?_, hintercard⟩
  exact Finset.card_pos.mp (by omega)

open Classical in
theorem dualGraphSharedFace_mem_facesOfCard_two
    [FiniteDimensional ℝ E] (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    {e : Sym2 {s : Finset E // s ∈ K.faces ∧ s.card = 3}}
    (he : e ∈ (dualGraph 2 K).edgeSet) :
    dualGraphSharedFace K e ∈
      SimplicialComplex.facesOfCard K.toPreAbstractSimplicialComplex 2 := by
  induction e using Sym2.inductionOn with
  | _ s t =>
    simpa only [dualGraphSharedFace, Sym2.lift_mk] using
      dualGraph_sharedFace_mem_facesOfCard_two K ((dualGraph 2 K).mem_edgeSet.mp he)

open Classical in
theorem faceCofaces_sharedFace_eq_pair
    [FiniteDimensional ℝ E] (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsCombinatorialManifold 2 K)
    {s t : {s : Finset E // s ∈ K.faces ∧ s.card = 3}}
    (hst : (dualGraph 2 K).Adj s t) :
    faceCofaces K (s.1 ∩ t.1) 3 = {s.1, t.1} := by
  have hface := dualGraph_sharedFace_mem_facesOfCard_two K hst
  have hcard := (SimplicialComplex.mem_facesOfCard K.toPreAbstractSimplicialComplex).mp hface |>.2
  have hcofaces := hK.card_faceCofaces_eq_two K
    ((SimplicialComplex.mem_facesOfCard K.toPreAbstractSimplicialComplex).mp hface |>.1) hcard
  have hstval : s.1 ≠ t.1 := fun h => hst.1 (Subtype.ext h)
  have hpairsub : {s.1, t.1} ⊆ faceCofaces K (s.1 ∩ t.1) 3 := by
    intro u hu
    simp only [Finset.mem_insert, Finset.mem_singleton] at hu
    rcases hu with rfl | rfl
    · exact (mem_faceCofaces K).mpr
        ⟨s.2.1, s.2.2, Finset.inter_subset_left⟩
    · exact (mem_faceCofaces K).mpr
        ⟨t.2.1, t.2.2, Finset.inter_subset_right⟩
  exact (Finset.eq_of_subset_of_card_le hpairsub (by
    rw [hcofaces, Finset.card_pair hstval])).symm

open Classical in
theorem dualGraphSharedFace_injOn_edgeSet
    [FiniteDimensional ℝ E] (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsCombinatorialManifold 2 K) :
    Set.InjOn (dualGraphSharedFace K) (dualGraph 2 K).edgeSet := by
  intro e he f hf hef
  induction e using Sym2.inductionOn with
  | _ s t =>
    induction f using Sym2.inductionOn with
    | _ u v =>
      have hst := (dualGraph 2 K).mem_edgeSet.mp he
      have huv := (dualGraph 2 K).mem_edgeSet.mp hf
      have hpairs : ({s.1, t.1} : Finset (Finset E)) = {u.1, v.1} := by
        rw [← faceCofaces_sharedFace_eq_pair K hK hst,
          ← faceCofaces_sharedFace_eq_pair K hK huv]
        simpa only [dualGraphSharedFace, Sym2.lift_mk] using congrArg
          (fun q => faceCofaces K q 3) hef
      have hs : s.1 = u.1 ∨ s.1 = v.1 := by
        have : s.1 ∈ ({u.1, v.1} : Finset (Finset E)) := by rw [← hpairs]; simp
        simpa using this
      have ht : t.1 = u.1 ∨ t.1 = v.1 := by
        have : t.1 ∈ ({u.1, v.1} : Finset (Finset E)) := by rw [← hpairs]; simp
        simpa using this
      rw [Sym2.eq_iff]
      rcases hs with hsu | hsv
      · have htu : t.1 ≠ u.1 := fun h => hst.1 (Subtype.ext (hsu.trans h.symm))
        exact Or.inl ⟨Subtype.ext hsu, Subtype.ext (ht.resolve_left htu)⟩
      · have htv : t.1 ≠ v.1 := fun h => hst.1 (Subtype.ext (hsv.trans h.symm))
        exact Or.inr ⟨Subtype.ext hsv, Subtype.ext (ht.resolve_right htv)⟩

open Classical in
theorem dualGraphSharedFace_surjOn_facesOfCard_two
    [FiniteDimensional ℝ E] (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsCombinatorialManifold 2 K) :
    Set.SurjOn (dualGraphSharedFace K) (dualGraph 2 K).edgeSet
      {s | s ∈ SimplicialComplex.facesOfCard K.toPreAbstractSimplicialComplex 2} := by
  intro q hq
  obtain ⟨hqK, hqcard⟩ :=
    (SimplicialComplex.mem_facesOfCard K.toPreAbstractSimplicialComplex).mp hq
  have htwo := hK.card_faceCofaces_eq_two K hqK hqcard
  obtain ⟨s, t, hst, hpairs⟩ := Finset.card_eq_two.mp htwo
  have hsco : s ∈ faceCofaces K q 3 := by rw [hpairs]; simp
  have htco : t ∈ faceCofaces K q 3 := by rw [hpairs]; simp
  obtain ⟨hsK, hscard, hqs⟩ := (mem_faceCofaces K).mp hsco
  obtain ⟨htK, htcard, hqt⟩ := (mem_faceCofaces K).mp htco
  let s' : {s : Finset E // s ∈ K.faces ∧ s.card = 3} := ⟨s, hsK, hscard⟩
  let t' : {s : Finset E // s ∈ K.faces ∧ s.card = 3} := ⟨t, htK, htcard⟩
  have hadj : (dualGraph 2 K).Adj s' t' :=
    ⟨fun h => hst (congrArg Subtype.val h), q, hqK, hqcard, hqs, hqt⟩
  refine ⟨s(s', t'), (dualGraph 2 K).mem_edgeSet.mpr hadj, ?_⟩
  simp only [dualGraphSharedFace, Sym2.lift_mk]
  have hinter := dualGraph_sharedFace_mem_facesOfCard_two K hadj
  have hintercard :=
    (SimplicialComplex.mem_facesOfCard K.toPreAbstractSimplicialComplex).mp hinter |>.2
  exact (Finset.eq_of_subset_of_card_le (Finset.subset_inter hqs hqt) (by
    rw [hqcard, hintercard])).symm

open Classical in
theorem ncard_edgeSet_dualGraph_two_eq_facesOfCard_two
    [FiniteDimensional ℝ E] (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsCombinatorialManifold 2 K) :
    (dualGraph 2 K).edgeSet.ncard =
      (SimplicialComplex.facesOfCard K.toPreAbstractSimplicialComplex 2).card := by
  let S : Set (Finset E) :=
    {s | s ∈ SimplicialComplex.facesOfCard K.toPreAbstractSimplicialComplex 2}
  have hb : Set.BijOn (dualGraphSharedFace K) (dualGraph 2 K).edgeSet S :=
    ⟨fun e he => dualGraphSharedFace_mem_facesOfCard_two K he,
      dualGraphSharedFace_injOn_edgeSet K hK,
      dualGraphSharedFace_surjOn_facesOfCard_two K hK⟩
  calc
    (dualGraph 2 K).edgeSet.ncard = S.ncard := hb.ncard_eq
    _ = (SimplicialComplex.facesOfCard K.toPreAbstractSimplicialComplex 2).card := by
      rw [show S = ↑(SimplicialComplex.facesOfCard
        K.toPreAbstractSimplicialComplex 2) by
          ext s
          change (s ∈ SimplicialComplex.facesOfCard K.toPreAbstractSimplicialComplex 2) ↔ _
          rfl]
      simp

open Classical in
noncomputable def spanningTreeFaces (K : Geometry.SimplicialComplex ℝ E)
    (T : SimpleGraph K.vertices) : Set (Finset E) :=
  edgeGraphFace K '' T.edgeSet

open Classical in
theorem spanningTreeFaces_subset_facesOfCard_two
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    {T : SimpleGraph K.vertices} (hT : T ≤ SimplicialComplex.edgeGraph K) :
    spanningTreeFaces K T ⊆
      {s | s ∈ SimplicialComplex.facesOfCard K.toPreAbstractSimplicialComplex 2} := by
  rintro q ⟨e, he, rfl⟩
  exact edgeGraphFace_mem_facesOfCard_two K
    (SimpleGraph.edgeSet_mono hT he)

open Classical in
theorem ncard_spanningTreeFaces
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    {T : SimpleGraph K.vertices} (hT : T ≤ SimplicialComplex.edgeGraph K) :
    (spanningTreeFaces K T).ncard = T.edgeSet.ncard := by
  exact ((edgeGraphFace_injOn_edgeSet K).mono (SimpleGraph.edgeSet_mono hT)).ncard_image

open Classical in
noncomputable def dualCotreeGraph (K : Geometry.SimplicialComplex ℝ E)
    (T : SimpleGraph K.vertices) :
    SimpleGraph {s : Finset E // s ∈ K.faces ∧ s.card = 3} where
  Adj s t := (dualGraph 2 K).Adj s t ∧ s.1 ∩ t.1 ∉ spanningTreeFaces K T
  symm := ⟨fun s t h => ⟨h.1.symm, by simpa only [Finset.inter_comm] using h.2⟩⟩
  loopless := ⟨fun s h => h.1.ne rfl⟩

open Classical in
theorem dualCotreeGraph_le_dualGraph (K : Geometry.SimplicialComplex ℝ E)
    (T : SimpleGraph K.vertices) : dualCotreeGraph K T ≤ dualGraph 2 K :=
  fun _ _ h => h.1

open Classical in
theorem mem_edgeSet_dualCotreeGraph_iff
    (K : Geometry.SimplicialComplex ℝ E) (T : SimpleGraph K.vertices)
    {e : Sym2 {s : Finset E // s ∈ K.faces ∧ s.card = 3}} :
    e ∈ (dualCotreeGraph K T).edgeSet ↔
      e ∈ (dualGraph 2 K).edgeSet ∧
        dualGraphSharedFace K e ∉ spanningTreeFaces K T := by
  induction e using Sym2.inductionOn with
  | _ s t =>
      rfl

open Classical in
theorem dualGraphSharedFace_bijOn_dualCotreeGraph
    [FiniteDimensional ℝ E] (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsCombinatorialManifold 2 K) (T : SimpleGraph K.vertices) :
    Set.BijOn (dualGraphSharedFace K) (dualCotreeGraph K T).edgeSet
      ({s | s ∈ SimplicialComplex.facesOfCard K.toPreAbstractSimplicialComplex 2} \
        spanningTreeFaces K T) := by
  refine ⟨?_, ?_, ?_⟩
  · intro e he
    rw [mem_edgeSet_dualCotreeGraph_iff] at he
    exact ⟨dualGraphSharedFace_mem_facesOfCard_two K he.1, he.2⟩
  · exact (dualGraphSharedFace_injOn_edgeSet K hK).mono
      (fun _ he => (mem_edgeSet_dualCotreeGraph_iff K T).mp he |>.1)
  · intro q hq
    obtain ⟨e, he, heq⟩ := dualGraphSharedFace_surjOn_facesOfCard_two K hK hq.1
    refine ⟨e, ?_, heq⟩
    rw [mem_edgeSet_dualCotreeGraph_iff]
    exact ⟨he, heq.symm ▸ hq.2⟩

open Classical in
theorem ncard_edgeSet_dualCotreeGraph
    [FiniteDimensional ℝ E] (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsCombinatorialManifold 2 K) {T : SimpleGraph K.vertices}
    (hT : T ≤ SimplicialComplex.edgeGraph K) :
    (dualCotreeGraph K T).edgeSet.ncard =
      (SimplicialComplex.facesOfCard K.toPreAbstractSimplicialComplex 2).card -
        T.edgeSet.ncard := by
  let S : Set (Finset E) :=
    {s | s ∈ SimplicialComplex.facesOfCard K.toPreAbstractSimplicialComplex 2}
  have hsub : spanningTreeFaces K T ⊆ S := spanningTreeFaces_subset_facesOfCard_two K hT
  have hfinS : S.Finite := by
    change (↑(SimplicialComplex.facesOfCard
      K.toPreAbstractSimplicialComplex 2) : Set (Finset E)).Finite
    exact Finset.finite_toSet _
  calc
    (dualCotreeGraph K T).edgeSet.ncard = (S \ spanningTreeFaces K T).ncard :=
      (dualGraphSharedFace_bijOn_dualCotreeGraph K hK T).ncard_eq
    _ = S.ncard - (spanningTreeFaces K T).ncard :=
      Set.ncard_sdiff' hsub hfinS
    _ = (SimplicialComplex.facesOfCard
        K.toPreAbstractSimplicialComplex 2).card - T.edgeSet.ncard := by
      rw [ncard_spanningTreeFaces K hT]
      congr 1
      change (↑(SimplicialComplex.facesOfCard
        K.toPreAbstractSimplicialComplex 2) : Set (Finset E)).ncard = _
      simp

open Classical in
theorem natCard_topFaces_eq_facesOfCard_three
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces] :
    Nat.card {s : Finset E // s ∈ K.faces ∧ s.card = 3} =
      (SimplicialComplex.facesOfCard K.toPreAbstractSimplicialComplex 3).card := by
  change Nat.card ({s : Finset E | s ∈ K.faces ∧ s.card = 3} : Set (Finset E)) = _
  rw [Nat.card_coe_set_eq]
  rw [show {s : Finset E | s ∈ K.faces ∧ s.card = 3} =
      ↑(SimplicialComplex.facesOfCard K.toPreAbstractSimplicialComplex 3) by
    ext s
    exact (SimplicialComplex.mem_facesOfCard
      K.toPreAbstractSimplicialComplex).symm]
  simp

open Classical in
theorem ncard_edgeSet_dualCotreeGraph_add_one_eq_natCard
    [FiniteDimensional ℝ E] (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsCombinatorialManifold 2 K)
    (hEuler : SimplicialComplex.faceEulerChar K.toPreAbstractSimplicialComplex = 2)
    {T : SimpleGraph K.vertices} (hT : T ≤ SimplicialComplex.edgeGraph K)
    (hTree : T.IsTree) :
    (dualCotreeGraph K T).edgeSet.ncard + 1 =
      Nat.card {s : Finset E // s ∈ K.faces ∧ s.card = 3} := by
  let _ : Finite K.vertices := (SimplicialComplex.finite_vertices K).to_subtype
  have htreeCard : T.edgeSet.ncard + 1 = K.vertices.ncard := by
    simpa using (SimpleGraph.isTree_iff_connected_and_card.mp hTree).2
  have htreeEdgeLe : T.edgeSet.ncard ≤
      (SimplicialComplex.facesOfCard K.toPreAbstractSimplicialComplex 2).card := by
    rw [← ncard_edgeSet_edgeGraph_eq_facesOfCard_two K]
    exact Set.ncard_le_ncard (SimpleGraph.edgeSet_mono hT)
  have hEuler' := hEuler
  rw [SimplicialComplex.faceEulerChar_eq_of_card_le_three
    K.toPreAbstractSimplicialComplex (fun s hs => by
      simpa using hK.card_le K hs)] at hEuler'
  rw [ncard_edgeSet_dualCotreeGraph K hK hT,
    natCard_topFaces_eq_facesOfCard_three K]
  rw [ncard_vertices_eq_facesOfCard_one K] at htreeCard
  omega

open Classical in
noncomputable def dualReachableCutGraph
    (K : Geometry.SimplicialComplex ℝ E) (T : SimpleGraph K.vertices)
    (r : {s : Finset E // s ∈ K.faces ∧ s.card = 3}) :
    SimpleGraph K.vertices where
  Adj u v := (SimplicialComplex.edgeGraph K).Adj u v ∧
    ∃ s t, (dualGraph 2 K).Adj s t ∧
      dualGraphSharedFace K s(s, t) = edgeGraphFace K s(u, v) ∧
      ¬((dualCotreeGraph K T).Reachable r s ↔
        (dualCotreeGraph K T).Reachable r t)
  symm := ⟨by
    rintro u v ⟨huv, s, t, hst, hface, hcross⟩
    refine ⟨huv.symm, s, t, hst, ?_, hcross⟩
    simpa only [edgeGraphFace, Sym2.map_mk, Sym2.toFinset_mk_eq,
      Finset.pair_comm] using hface⟩
  loopless := ⟨fun u h => h.1.ne rfl⟩

open Classical in
theorem dualReachableCutGraph_le
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    {T : SimpleGraph K.vertices} (hT : T ≤ SimplicialComplex.edgeGraph K)
    (r : {s : Finset E // s ∈ K.faces ∧ s.card = 3}) :
    dualReachableCutGraph K T r ≤ T := by
  intro u v huv
  obtain ⟨huvK, s, t, hst, hface, hcross⟩ := huv
  have hsharedTree : dualGraphSharedFace K s(s, t) ∈ spanningTreeFaces K T := by
    by_contra hnot
    have hcotree : (dualCotreeGraph K T).Adj s t := ⟨hst, by
      simpa only [dualGraphSharedFace, Sym2.lift_mk] using hnot⟩
    apply hcross
    constructor
    · exact fun hs => hs.trans hcotree.reachable
    · exact fun ht => ht.trans hcotree.symm.reachable
  obtain ⟨e, heT, heface⟩ := hsharedTree
  have heK : e ∈ (SimplicialComplex.edgeGraph K).edgeSet :=
    SimpleGraph.edgeSet_mono hT heT
  have huvEdge : s(u, v) ∈ (SimplicialComplex.edgeGraph K).edgeSet :=
    (SimplicialComplex.edgeGraph K).mem_edgeSet.mpr huvK
  have heu : e = s(u, v) := edgeGraphFace_injOn_edgeSet K heK huvEdge
    (heface.trans hface)
  exact T.mem_edgeSet.mp (heu ▸ heT)

open Classical in
theorem dualReachableCutGraph_nonempty_of_not_reachable
    [FiniteDimensional ℝ E] (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsCombinatorialManifold 2 K) (hconn : IsConnected K.space)
    (T : SimpleGraph K.vertices)
    {r q : {s : Finset E // s ∈ K.faces ∧ s.card = 3}}
    (hrq : ¬(dualCotreeGraph K T).Reachable r q) :
    ∃ u v, (dualReachableCutGraph K T r).Adj u v := by
  have hdual : (dualGraph 2 K).Preconnected :=
    hK.isCombinatorialManifoldWithBoundary.dualGraph_preconnected hconn.isPreconnected
  obtain ⟨p⟩ := hdual r q
  obtain ⟨⟨⟨s, t⟩, hst⟩, -, hs, ht⟩ := p.exists_boundary_dart
    {z | (dualCotreeGraph K T).Reachable r z} SimpleGraph.Reachable.rfl hrq
  have hface := dualGraph_sharedFace_mem_facesOfCard_two K hst
  obtain ⟨e, he, heq⟩ := edgeGraphFace_surjOn_facesOfCard_two K hface
  induction e using Sym2.inductionOn with
  | _ u v =>
      refine ⟨u, v, (SimplicialComplex.edgeGraph K).mem_edgeSet.mp he,
        s, t, hst, ?_, ?_⟩
      · simpa only [dualGraphSharedFace, Sym2.lift_mk] using heq.symm
      · exact fun hiff => ht (hiff.mp hs)

open Classical in
theorem dualGraph_one_sharedFace_mem_facesOfCard_one
    [FiniteDimensional ℝ E] (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    {s t : {s : Finset E // s ∈ K.faces ∧ s.card = 2}}
    (hst : (dualGraph 1 K).Adj s t) :
    s.1 ∩ t.1 ∈ SimplicialComplex.facesOfCard K.toPreAbstractSimplicialComplex 1 := by
  obtain ⟨hstne, f, hfK, hfcard, hfs, hft⟩ := hst
  have hfsub : f ⊆ s.1 ∩ t.1 := Finset.subset_inter hfs hft
  have hlower : 1 ≤ (s.1 ∩ t.1).card := by
    rw [← hfcard]
    exact Finset.card_le_card hfsub
  have hupper : (s.1 ∩ t.1).card ≤ 2 := by
    calc
      (s.1 ∩ t.1).card ≤ s.1.card := Finset.card_le_card Finset.inter_subset_left
      _ = 2 := s.2.2
  have hnotTwo : (s.1 ∩ t.1).card ≠ 2 := by
    intro hcard
    have hinterS : s.1 ∩ t.1 = s.1 := Finset.eq_of_subset_of_card_le
      Finset.inter_subset_left (by rw [hcard, s.2.2])
    have hstsub : s.1 ⊆ t.1 := hinterS ▸ Finset.inter_subset_right
    exact hstne (Subtype.ext (Finset.eq_of_subset_of_card_le hstsub (by
      rw [s.2.2, t.2.2])))
  have hintercard : (s.1 ∩ t.1).card = 1 := by omega
  apply (SimplicialComplex.mem_facesOfCard K.toPreAbstractSimplicialComplex).mpr
  refine ⟨K.down_closed s.2.1 Finset.inter_subset_left ?_, hintercard⟩
  exact Finset.card_pos.mp (by omega)

open Classical in
theorem faceCofaces_one_sharedFace_eq_pair
    [FiniteDimensional ℝ E] (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsCombinatorialManifold 1 K)
    {s t : {s : Finset E // s ∈ K.faces ∧ s.card = 2}}
    (hst : (dualGraph 1 K).Adj s t) :
    faceCofaces K (s.1 ∩ t.1) 2 = {s.1, t.1} := by
  have hface := dualGraph_one_sharedFace_mem_facesOfCard_one K hst
  have hcard := (SimplicialComplex.mem_facesOfCard
    K.toPreAbstractSimplicialComplex).mp hface |>.2
  have hcofaces := hK.card_faceCofaces_eq_two K
    ((SimplicialComplex.mem_facesOfCard
      K.toPreAbstractSimplicialComplex).mp hface |>.1) hcard
  have hstval : s.1 ≠ t.1 := fun h => hst.1 (Subtype.ext h)
  have hpairsub : {s.1, t.1} ⊆ faceCofaces K (s.1 ∩ t.1) 2 := by
    intro u hu
    simp only [Finset.mem_insert, Finset.mem_singleton] at hu
    rcases hu with rfl | rfl
    · exact (mem_faceCofaces K).mpr ⟨s.2.1, s.2.2, Finset.inter_subset_left⟩
    · exact (mem_faceCofaces K).mpr ⟨t.2.1, t.2.2, Finset.inter_subset_right⟩
  exact (Finset.eq_of_subset_of_card_le hpairsub (by
    rw [hcofaces, Finset.card_pair hstval])).symm

open Classical in
theorem dualGraph_one_neighborSet_ncard_eq_two
    [FiniteDimensional ℝ E] (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsCombinatorialManifold 1 K)
    (s : {s : Finset E // s ∈ K.faces ∧ s.card = 2}) :
    ((dualGraph 1 K).neighborSet s).ncard = 2 := by
  have hTop : Set.Finite {t : Finset E | t ∈ K.faces ∧ t.card = 2} :=
    (Set.toFinite K.faces).subset fun _ h => h.1
  let _ : Finite {t : Finset E // t ∈ K.faces ∧ t.card = 2} := hTop.to_subtype
  let N := (dualGraph 1 K).neighborSet s
  let P := s.1.powersetCard 1
  let f : N → P := fun t => ⟨s.1 ∩ t.1.1, Finset.mem_powersetCard.mpr
    ⟨Finset.inter_subset_left,
      (SimplicialComplex.mem_facesOfCard K.toPreAbstractSimplicialComplex).mp
        (dualGraph_one_sharedFace_mem_facesOfCard_one K t.2) |>.2⟩⟩
  have hinj : Function.Injective f := by
    intro t u htu
    apply Subtype.ext
    have hinter : s.1 ∩ t.1.1 = s.1 ∩ u.1.1 := congrArg Subtype.val htu
    have hpairs : ({s.1, t.1.1} : Finset (Finset E)) = {s.1, u.1.1} := by
      rw [← faceCofaces_one_sharedFace_eq_pair K hK t.2,
        ← faceCofaces_one_sharedFace_eq_pair K hK u.2, hinter]
    have htmem : t.1.1 ∈ ({s.1, u.1.1} : Finset (Finset E)) := by
      rw [← hpairs]
      simp
    simp only [Finset.mem_insert, Finset.mem_singleton] at htmem
    have htadj : (dualGraph 1 K).Adj s t.1 := t.2
    exact Subtype.ext (htmem.resolve_left fun h => htadj.ne (Subtype.ext h.symm))
  have hsurj : Function.Surjective f := by
    intro q
    have hqsub : q.1 ⊆ s.1 := (Finset.mem_powersetCard.mp q.2).1
    have hqcard : q.1.card = 1 := (Finset.mem_powersetCard.mp q.2).2
    have hqK : q.1 ∈ K.faces := K.down_closed s.2.1 hqsub
      (Finset.card_pos.mp (by omega))
    have hcoCard := hK.card_faceCofaces_eq_two K hqK hqcard
    have hsco : s.1 ∈ faceCofaces K q.1 2 :=
      (mem_faceCofaces K).mpr ⟨s.2.1, s.2.2, hqsub⟩
    have hother : ∃ t ∈ faceCofaces K q.1 2, t ≠ s.1 := by
      by_contra h
      push Not at h
      have hsub : faceCofaces K q.1 2 ⊆ {s.1} := by
        intro t ht
        simpa using h t ht
      have hle := Finset.card_le_card hsub
      rw [hcoCard, Finset.card_singleton] at hle
      omega
    obtain ⟨t, htco, hts⟩ := hother
    obtain ⟨htK, htcard, hqt⟩ := (mem_faceCofaces K).mp htco
    let t' : {t : Finset E // t ∈ K.faces ∧ t.card = 2} := ⟨t, htK, htcard⟩
    have hst : (dualGraph 1 K).Adj s t' :=
      ⟨fun h => hts (congrArg Subtype.val h).symm, q.1, hqK, hqcard, hqsub, hqt⟩
    refine ⟨⟨t', hst⟩, ?_⟩
    apply Subtype.ext
    change s.1 ∩ t = q.1
    have hinter := dualGraph_one_sharedFace_mem_facesOfCard_one K hst
    have hintercard := (SimplicialComplex.mem_facesOfCard
      K.toPreAbstractSimplicialComplex).mp hinter |>.2
    exact (Finset.eq_of_subset_of_card_le (Finset.subset_inter hqsub hqt) (by
      rw [hqcard, hintercard])).symm
  let _ : Fintype N := Fintype.ofFinite N
  have hcard := Fintype.card_congr (Equiv.ofBijective f ⟨hinj, hsurj⟩)
  change Nat.card N = 2
  rw [Nat.card_eq_fintype_card]
  simpa only [P, Fintype.card_coe, Finset.card_powersetCard, s.2.2,
    Nat.choose_one_right] using hcard

open Classical in
theorem dualGraphLinkHom_injective
    (n : ℕ) (K : Geometry.SimplicialComplex ℝ E) (v : E) :
    Function.Injective (dualGraphLinkHom n K v) := by
  intro s t hst
  apply Subtype.ext
  have h := congrArg (fun u : {u : Finset E // u ∈ K.faces ∧ u.card = n + 1 + 1} =>
    u.1.erase v) hst
  have hsv := (SimplicialComplex.mem_geometricLink_singleton K v s.1).mp s.2.1 |>.2.1
  have htv := (SimplicialComplex.mem_geometricLink_singleton K v t.1).mp t.2.1 |>.2.1
  change (insert v s.1).erase v = (insert v t.1).erase v at h
  simpa only [Finset.erase_insert hsv, Finset.erase_insert htv] using h

open Classical in
theorem exists_dualReachableCutGraph_adj_of_link_crossing
    [FiniteDimensional ℝ E] (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (T : SimpleGraph K.vertices)
    (r : {s : Finset E // s ∈ K.faces ∧ s.card = 3})
    (v : K.vertices)
    {a b : {s : Finset E //
      s ∈ (SimplicialComplex.geometricLink K {(v : E)}).faces ∧ s.card = 2}}
    (hab : (dualGraph 1 (SimplicialComplex.geometricLink K {(v : E)})).Adj a b)
    (hcross : ¬((dualCotreeGraph K T).Reachable r (dualGraphLinkHom 1 K v a) ↔
      (dualCotreeGraph K T).Reachable r (dualGraphLinkHom 1 K v b))) :
    ∃ w, (dualReachableCutGraph K T r).Adj v w ∧
      dualGraphSharedFace K s(dualGraphLinkHom 1 K v a, dualGraphLinkHom 1 K v b) =
        edgeGraphFace K s(v, w) := by
  let s := dualGraphLinkHom 1 K v a
  let t := dualGraphLinkHom 1 K v b
  have hst : (dualGraph 2 K).Adj s t := (dualGraphLinkHom 1 K v).map_rel hab
  have hface := dualGraph_sharedFace_mem_facesOfCard_two K hst
  have hfaceK := (SimplicialComplex.mem_facesOfCard
    K.toPreAbstractSimplicialComplex).mp hface |>.1
  have hfaceCard := (SimplicialComplex.mem_facesOfCard
    K.toPreAbstractSimplicialComplex).mp hface |>.2
  have hvface : (v : E) ∈ s.1 ∩ t.1 := by
    change (v : E) ∈ insert (v : E) a.1 ∩ insert (v : E) b.1
    simp
  have heraseCard : ((s.1 ∩ t.1).erase (v : E)).card = 1 := by
    rw [Finset.card_erase_of_mem hvface, hfaceCard]
  obtain ⟨w, hw⟩ := Finset.card_eq_one.mp heraseCard
  have hwmemErase : w ∈ (s.1 ∩ t.1).erase (v : E) := by rw [hw]; simp
  have hwface : w ∈ s.1 ∩ t.1 := (Finset.mem_erase.mp hwmemErase).2
  have hwv : w ≠ (v : E) := (Finset.mem_erase.mp hwmemErase).1
  have hfacePair : s.1 ∩ t.1 = {(v : E), w} := by
    have hins := Finset.insert_erase hvface
    rw [hw] at hins
    exact hins.symm
  have hwK : {w} ∈ K.faces := K.down_closed hfaceK
    (Finset.singleton_subset_iff.mpr hwface) (Finset.singleton_nonempty w)
  let w' : K.vertices := ⟨w, hwK⟩
  have hvw : (SimplicialComplex.edgeGraph K).Adj v w' := by
    refine ⟨fun h => hwv (congrArg Subtype.val h).symm, ?_⟩
    change {(v : E), w} ∈ K.faces
    rw [← hfacePair]
    exact hfaceK
  have hshared : dualGraphSharedFace K s(s, t) = edgeGraphFace K s(v, w') := by
    simp only [dualGraphSharedFace, Sym2.lift_mk, edgeGraphFace, Sym2.map_mk,
      Sym2.toFinset_mk_eq, s, t, w']
    exact hfacePair
  refine ⟨w', ⟨hvw, s, t, hst, hshared, ?_⟩, ?_⟩
  · simpa only [s, t] using hcross
  · simpa only [s, t] using hshared

open Classical in
theorem exists_dualGraph_link_lift_of_mem_sharedFace
    [FiniteDimensional ℝ E] (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    {s t : {s : Finset E // s ∈ K.faces ∧ s.card = 3}}
    (hst : (dualGraph 2 K).Adj s t) {v : E} (hv : v ∈ s.1 ∩ t.1) :
    ∃ (a b : {q : Finset E //
        q ∈ (SimplicialComplex.geometricLink K {v}).faces ∧ q.card = 2}),
      (dualGraph 1 (SimplicialComplex.geometricLink K {v})).Adj a b ∧
      dualGraphLinkHom 1 K v a = s ∧ dualGraphLinkHom 1 K v b = t := by
  have hvs : v ∈ s.1 := (Finset.mem_inter.mp hv).1
  have hvt : v ∈ t.1 := (Finset.mem_inter.mp hv).2
  have hsL : s.1.erase v ∈ (SimplicialComplex.geometricLink K {v}).faces := by
    apply (SimplicialComplex.mem_geometricLink_singleton K v _).mpr
    refine ⟨Finset.card_pos.mp ?_, Finset.notMem_erase _ _, ?_⟩
    · rw [Finset.card_erase_of_mem hvs, s.2.2]
      omega
    · rw [Finset.insert_erase hvs]
      exact s.2.1
  have htL : t.1.erase v ∈ (SimplicialComplex.geometricLink K {v}).faces := by
    apply (SimplicialComplex.mem_geometricLink_singleton K v _).mpr
    refine ⟨Finset.card_pos.mp ?_, Finset.notMem_erase _ _, ?_⟩
    · rw [Finset.card_erase_of_mem hvt, t.2.2]
      omega
    · rw [Finset.insert_erase hvt]
      exact t.2.1
  have hsCard : (s.1.erase v).card = 2 := by
    rw [Finset.card_erase_of_mem hvs, s.2.2]
  have htCard : (t.1.erase v).card = 2 := by
    rw [Finset.card_erase_of_mem hvt, t.2.2]
  let a : {q : Finset E //
      q ∈ (SimplicialComplex.geometricLink K {v}).faces ∧ q.card = 2} :=
    ⟨s.1.erase v, hsL, hsCard⟩
  let b : {q : Finset E //
      q ∈ (SimplicialComplex.geometricLink K {v}).faces ∧ q.card = 2} :=
    ⟨t.1.erase v, htL, htCard⟩
  have hface := dualGraph_sharedFace_mem_facesOfCard_two K hst
  have hfaceK := (SimplicialComplex.mem_facesOfCard
    K.toPreAbstractSimplicialComplex).mp hface |>.1
  have hfaceCard := (SimplicialComplex.mem_facesOfCard
    K.toPreAbstractSimplicialComplex).mp hface |>.2
  let q := (s.1 ∩ t.1).erase v
  have hqCard : q.card = 1 := by
    change ((s.1 ∩ t.1).erase v).card = 1
    rw [Finset.card_erase_of_mem hv, hfaceCard]
  have hqL : q ∈ (SimplicialComplex.geometricLink K {v}).faces := by
    apply (SimplicialComplex.mem_geometricLink_singleton K v _).mpr
    refine ⟨Finset.card_pos.mp (by rw [hqCard]; decide), Finset.notMem_erase _ _, ?_⟩
    change insert v ((s.1 ∩ t.1).erase v) ∈ K.faces
    rw [Finset.insert_erase hv]
    exact hfaceK
  have hqa : q ⊆ a.1 := by
    intro x hx
    have hx' := (Finset.mem_erase.mp hx)
    exact Finset.mem_erase.mpr ⟨hx'.1, (Finset.mem_inter.mp hx'.2).1⟩
  have hqb : q ⊆ b.1 := by
    intro x hx
    have hx' := (Finset.mem_erase.mp hx)
    exact Finset.mem_erase.mpr ⟨hx'.1, (Finset.mem_inter.mp hx'.2).2⟩
  have hab : (dualGraph 1 (SimplicialComplex.geometricLink K {v})).Adj a b := by
    refine ⟨?_, q, hqL, hqCard, hqa, hqb⟩
    intro heq
    apply hst.1
    have heq' := congrArg (fun u : {q : Finset E //
      q ∈ (SimplicialComplex.geometricLink K {v}).faces ∧ q.card = 2} => insert v u.1) heq
    exact Subtype.ext (by
      simpa only [a, b, Finset.insert_erase hvs, Finset.insert_erase hvt] using heq')
  refine ⟨a, b, hab, ?_, ?_⟩
  · exact Subtype.ext (Finset.insert_erase hvs)
  · exact Subtype.ext (Finset.insert_erase hvt)

open Classical in
theorem dualReachableCutGraph_neighborSet_ncard_ne_one
    [FiniteDimensional ℝ E] (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsCombinatorialManifold 2 K) (T : SimpleGraph K.vertices)
    (r : {s : Finset E // s ∈ K.faces ∧ s.card = 3}) (v : K.vertices) :
    ((dualReachableCutGraph K T r).neighborSet v).ncard ≠ 1 := by
  intro hcard
  obtain ⟨w, hw⟩ := Set.ncard_eq_one.mp hcard
  have hvw : (dualReachableCutGraph K T r).Adj v w := by
    change w ∈ (dualReachableCutGraph K T r).neighborSet v
    rw [hw]
    simp
  obtain ⟨-, s, t, hst, hface, hcross⟩ := hvw
  have hvshared : (v : E) ∈ s.1 ∩ t.1 := by
    change (v : E) ∈ dualGraphSharedFace K s(s, t)
    rw [hface]
    simp only [edgeGraphFace, Sym2.map_mk, Sym2.toFinset_mk_eq,
      Finset.mem_insert, Finset.mem_singleton, true_or]
  obtain ⟨a, b, hab, ha, hb⟩ := exists_dualGraph_link_lift_of_mem_sharedFace K hst hvshared
  have hcrossAB :
      ¬((dualCotreeGraph K T).Reachable r (dualGraphLinkHom 1 K v a) ↔
        (dualCotreeGraph K T).Reachable r (dualGraphLinkHom 1 K v b)) := by
    rwa [ha, hb]
  let L := SimplicialComplex.geometricLink K {(v : E)}
  have hL : IsCombinatorialManifold 1 L := by
    exact (hK v v.2).isCombinatorialManifold
  let G := dualGraph 1 L
  have hTopL : Set.Finite {q : Finset E | q ∈ L.faces ∧ q.card = 2} :=
    (Set.toFinite L.faces).subset fun _ h => h.1
  let _ : Finite {q : Finset E // q ∈ L.faces ∧ q.card = 2} := hTopL.to_subtype
  have hdegree (x : {q : Finset E // q ∈ L.faces ∧ q.card = 2}) :
      (G.neighborSet x).ncard = 2 := dualGraph_one_neighborSet_ncard_eq_two L hL x
  have heven (x : {q : Finset E // q ∈ L.faces ∧ q.card = 2}) :
      Even (G.neighborSet x).ncard := by
    rw [hdegree]
    exact even_two
  have hnotBridge : ¬G.IsBridge s(a, b) :=
    Combinatorics.not_isBridge_of_even_neighborSet_ncard G heven hab
  have hreach : (G.deleteEdges {s(a, b)}).Reachable a b := by
    rw [SimpleGraph.isBridge_iff] at hnotBridge
    exact not_not.mp hnotBridge
  have hfaceAB :
      dualGraphSharedFace K s(dualGraphLinkHom 1 K v a, dualGraphLinkHom 1 K v b) =
        edgeGraphFace K s(v, w) := by
    simpa only [Sym2.map_mk, ha, hb] using hface
  have hunique {x y : {q : Finset E // q ∈ L.faces ∧ q.card = 2}}
      (hxy : G.Adj x y)
      (hxyCross : ¬((dualCotreeGraph K T).Reachable r (dualGraphLinkHom 1 K v x) ↔
        (dualCotreeGraph K T).Reachable r (dualGraphLinkHom 1 K v y))) :
      s(x, y) = s(a, b) := by
    obtain ⟨z, hvz, hfaceXY⟩ :=
      exists_dualReachableCutGraph_adj_of_link_crossing K T r v hxy hxyCross
    have hzw : z = w := by
      have hzmem : z ∈ (dualReachableCutGraph K T r).neighborSet v := hvz
      rw [hw] at hzmem
      simpa using hzmem
    subst z
    apply (Sym2.map.injective (dualGraphLinkHom_injective 1 K v))
    apply dualGraphSharedFace_injOn_edgeSet K hK
    · exact (dualGraph 2 K).mem_edgeSet.mpr ((dualGraphLinkHom 1 K v).map_rel hxy)
    · exact (dualGraph 2 K).mem_edgeSet.mpr ((dualGraphLinkHom 1 K v).map_rel hab)
    · exact hfaceXY.trans hfaceAB.symm
  have hpreserve {x y : {q : Finset E // q ∈ L.faces ∧ q.card = 2}}
      (hxy : (G.deleteEdges {s(a, b)}).Adj x y) :
      ((dualCotreeGraph K T).Reachable r (dualGraphLinkHom 1 K v x) ↔
        (dualCotreeGraph K T).Reachable r (dualGraphLinkHom 1 K v y)) := by
    rw [SimpleGraph.deleteEdges_adj] at hxy
    by_contra hcrossXY
    exact hxy.2 (Set.mem_singleton_iff.mpr (hunique hxy.1 hcrossXY))
  have hwalk : ∀ {x y : {q : Finset E // q ∈ L.faces ∧ q.card = 2}},
      (p : (G.deleteEdges {s(a, b)}).Walk x y) →
        ((dualCotreeGraph K T).Reachable r (dualGraphLinkHom 1 K v x) ↔
          (dualCotreeGraph K T).Reachable r (dualGraphLinkHom 1 K v y)) := by
    intro x y p
    induction p with
    | nil => rfl
    | cons h p ih => exact (hpreserve h).trans ih
  obtain ⟨p⟩ := hreach
  have hsameroute :
      ((dualCotreeGraph K T).Reachable r (dualGraphLinkHom 1 K v a) ↔
        (dualCotreeGraph K T).Reachable r (dualGraphLinkHom 1 K v b)) := by
    exact hwalk p
  exact hcrossAB hsameroute

open Classical in
theorem exists_neighborSet_ncard_eq_one_of_nonempty_of_le_tree
    {V : Type*} [Finite V] (C T : SimpleGraph V) (hCT : C ≤ T) (hT : T.IsTree)
    (hne : ∃ u v, C.Adj u v) : ∃ v, (C.neighborSet v).ncard = 1 := by
  obtain ⟨u, v, huv⟩ := hne
  let c := C.connectedComponentMk u
  have huC : u ∈ c.supp := rfl
  have hvC : v ∈ c.supp := c.mem_supp_of_adj_mem_supp huC huv
  let u' : c.supp := ⟨u, huC⟩
  let v' : c.supp := ⟨v, hvC⟩
  have huv' : u' ≠ v' := by
    intro h
    exact huv.ne (congrArg Subtype.val h)
  let _ : Nontrivial c.supp := ⟨⟨u', v', huv'⟩⟩
  let _ : Fintype c.supp := Fintype.ofFinite c.supp
  have hC : C.IsAcyclic := hT.isAcyclic.anti hCT
  have hcTree : c.toSimpleGraph.IsTree := hC.isTree_connectedComponent c
  obtain ⟨x, hx⟩ := hcTree.exists_vert_degree_one_of_nontrivial
  refine ⟨x.1, ?_⟩
  have hbij : Set.BijOn (fun y : c => (y : V)) (c.toSimpleGraph.neighborSet x)
      (C.neighborSet x.1) := by
    refine ⟨?_, Set.injOn_of_injective Subtype.val_injective, ?_⟩
    · intro y hy
      change c.toSimpleGraph.Adj x y at hy
      exact (c.toSimpleGraph_adj x.2 y.2).mp hy
    · intro y hy
      have hyC : y ∈ c.supp := c.mem_supp_of_adj_mem_supp x.2 hy
      let y' : c := ⟨y, hyC⟩
      refine ⟨y', ?_, rfl⟩
      change c.toSimpleGraph.Adj x y'
      exact (c.toSimpleGraph_adj x.2 hyC).mpr hy
  rw [← hbij.ncard_eq]
  rw [← Set.fintypeCard_eq_ncard, c.toSimpleGraph.card_neighborSet_eq_degree]
  exact hx

open Classical in
theorem dualCotreeGraph_connected
    [FiniteDimensional ℝ E] (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsCombinatorialManifold 2 K) (hconn : IsConnected K.space)
    {T : SimpleGraph K.vertices} (hT : T ≤ SimplicialComplex.edgeGraph K)
    (hTree : T.IsTree) : (dualCotreeGraph K T).Connected := by
  let _ : Finite K.vertices := (SimplicialComplex.finite_vertices K).to_subtype
  let F := {s : Finset E // s ∈ K.faces ∧ s.card = 3}
  have hFFinite : Set.Finite {s : Finset E | s ∈ K.faces ∧ s.card = 3} :=
    (Set.toFinite K.faces).subset fun _ h => h.1
  let _ : Finite F := hFFinite.to_subtype
  obtain ⟨x, hx⟩ := hconn.nonempty
  obtain ⟨s, hs, -⟩ := K.mem_space_iff.mp hx
  obtain ⟨r, hr, -, hrcard⟩ :=
    hK.isCombinatorialManifoldWithBoundary.exists_face_superset_card_eq hs
  let r' : F := ⟨r, hr, by simpa using hrcard⟩
  let _ : Nonempty F := ⟨r'⟩
  refine ⟨?_⟩
  intro a b
  by_contra hab
  obtain ⟨u, v, huv⟩ :=
    dualReachableCutGraph_nonempty_of_not_reachable K hK hconn T hab
  obtain ⟨w, hw⟩ := exists_neighborSet_ncard_eq_one_of_nonempty_of_le_tree
    (dualReachableCutGraph K T a) T (dualReachableCutGraph_le K hT a) hTree ⟨u, v, huv⟩
  exact dualReachableCutGraph_neighborSet_ncard_ne_one K hK T a w hw

open Classical in
theorem IsCombinatorialManifold.faceEulerChar_le_two
    [FiniteDimensional ℝ E] (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsCombinatorialManifold 2 K) (hconn : IsConnected K.space) :
    SimplicialComplex.faceEulerChar K.toPreAbstractSimplicialComplex ≤ 2 := by
  let _ : Finite K.vertices := (SimplicialComplex.finite_vertices K).to_subtype
  have hFFinite : Set.Finite {s : Finset E | s ∈ K.faces ∧ s.card = 3} :=
    (Set.toFinite K.faces).subset fun _ h => h.1
  let _ : Finite {s : Finset E // s ∈ K.faces ∧ s.card = 3} := hFFinite.to_subtype
  obtain ⟨T, hT, hTree⟩ := exists_edgeGraph_spanningTree K hconn
  have htreeCard : T.edgeSet.ncard + 1 = K.vertices.ncard := by
    simpa using (SimpleGraph.isTree_iff_connected_and_card.mp hTree).2
  have htreeEdgeLe : T.edgeSet.ncard ≤
      (SimplicialComplex.facesOfCard K.toPreAbstractSimplicialComplex 2).card := by
    rw [← ncard_edgeSet_edgeGraph_eq_facesOfCard_two K]
    exact Set.ncard_le_ncard (SimpleGraph.edgeSet_mono hT)
  have hdualCard :=
    (dualCotreeGraph_connected K hK hconn hT hTree).card_vert_le_card_edgeSet_add_one
  rw [Nat.card_coe_set_eq] at hdualCard
  rw [natCard_topFaces_eq_facesOfCard_three K,
    ncard_edgeSet_dualCotreeGraph K hK hT] at hdualCard
  have hEuler := SimplicialComplex.faceEulerChar_eq_of_card_le_three
    K.toPreAbstractSimplicialComplex (fun s hs => by simpa using hK.card_le K hs)
  rw [ncard_vertices_eq_facesOfCard_one K] at htreeCard
  rw [hEuler]
  omega

open Classical in
theorem dualCotreeGraph_isTree
    [FiniteDimensional ℝ E] (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsCombinatorialManifold 2 K) (hconn : IsConnected K.space)
    (hEuler : SimplicialComplex.faceEulerChar K.toPreAbstractSimplicialComplex = 2)
    {T : SimpleGraph K.vertices} (hT : T ≤ SimplicialComplex.edgeGraph K)
    (hTree : T.IsTree) : (dualCotreeGraph K T).IsTree := by
  let _ : Finite K.vertices := (SimplicialComplex.finite_vertices K).to_subtype
  have hFFinite : Set.Finite {s : Finset E | s ∈ K.faces ∧ s.card = 3} :=
    (Set.toFinite K.faces).subset fun _ h => h.1
  let _ : Finite {s : Finset E // s ∈ K.faces ∧ s.card = 3} := hFFinite.to_subtype
  apply SimpleGraph.isTree_iff_connected_and_card.mpr
  refine ⟨dualCotreeGraph_connected K hK hconn hT hTree, ?_⟩
  simpa using ncard_edgeSet_dualCotreeGraph_add_one_eq_natCard K hK hEuler hT hTree

open Classical in
theorem exists_primalTree_dualCotree
    [FiniteDimensional ℝ E] (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsCombinatorialManifold 2 K) (hconn : IsConnected K.space)
    (hEuler : SimplicialComplex.faceEulerChar K.toPreAbstractSimplicialComplex = 2) :
    ∃ T ≤ SimplicialComplex.edgeGraph K,
      T.IsTree ∧ (dualCotreeGraph K T).IsTree := by
  obtain ⟨T, hT, hTree⟩ := exists_edgeGraph_spanningTree K hconn
  exact ⟨T, hT, hTree, dualCotreeGraph_isTree K hK hconn hEuler hT hTree⟩

end DifferentialGeometry.Topology.PiecewiseLinear
