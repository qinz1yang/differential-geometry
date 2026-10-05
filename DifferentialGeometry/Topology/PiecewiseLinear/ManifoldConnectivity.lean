import DifferentialGeometry.Topology.PiecewiseLinear.ManifoldInvariance
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*}

def dualGraph [AddCommGroup E] [Module ℝ E]
    (n : ℕ) (K : Geometry.SimplicialComplex ℝ E) :
    SimpleGraph {s : Finset E // s ∈ K.faces ∧ s.card = n + 1} where
  Adj s t := s ≠ t ∧ ∃ f ∈ K.faces, f.card = n ∧ f ⊆ s.1 ∧ f ⊆ t.1
  symm := ⟨by
    rintro s t ⟨hne, f, hf, hcard, hfs, hft⟩
    exact ⟨hne.symm, f, hf, hcard, hft, hfs⟩⟩
  loopless := ⟨by
    intro s h
    exact h.1 rfl⟩

open Classical in
theorem IsCombinatorialManifoldWithBoundary.exists_face_superset_card_eq
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {n : ℕ} {K : Geometry.SimplicialComplex ℝ E} [Finite K.faces]
    (hK : IsCombinatorialManifoldWithBoundary n K) {s : Finset E} (hs : s ∈ K.faces) :
    ∃ t ∈ K.faces, s ⊆ t ∧ t.card = n + 1 := by
  classical
  cases n with
  | zero =>
    refine ⟨s, hs, Finset.Subset.refl _, ?_⟩
    have hle := hK.card_le_one hs
    have hpos := Finset.card_pos.mpr (K.nonempty_of_mem_faces hs)
    omega
  | succ n =>
    obtain ⟨v, hv⟩ := K.nonempty_of_mem_faces hs
    have hvK : {v} ∈ K.faces := K.down_closed hs
      (Finset.singleton_subset_iff.mpr hv) (Finset.singleton_nonempty v)
    let L := SimplicialComplex.geometricLink K {v}
    have hL : IsPLBall n L.space ∨ IsPLSphere n L.space := (hK v hvK).symm
    obtain ⟨t, ht, hst, hcard⟩ : ∃ t ∈ L.faces, s.erase v ⊆ t ∧ t.card = n + 1 := by
      by_cases hne : (s.erase v).Nonempty
      · have hsL : s.erase v ∈ L.faces := by
          apply (SimplicialComplex.mem_geometricLink_singleton K v (s.erase v)).mpr
          refine ⟨hne, Finset.notMem_erase v s, ?_⟩
          rwa [Finset.insert_erase hv]
        exact exists_face_superset_card_eq_of_isPLBall_or_isPLSphere L hL hsL
      · obtain ⟨x, hx⟩ := hL.elim IsPLBall.nonempty IsPLSphere.nonempty
        obtain ⟨r, hr, _⟩ := L.mem_space_iff.mp hx
        obtain ⟨t, ht, _, hcard⟩ :=
          exists_face_superset_card_eq_of_isPLBall_or_isPLSphere L hL hr
        refine ⟨t, ht, ?_, hcard⟩
        rw [Finset.not_nonempty_iff_eq_empty.mp hne]
        exact Finset.empty_subset t
    have htL := (SimplicialComplex.mem_geometricLink_singleton K v t).mp ht
    refine ⟨insert v t, htL.2.2, ?_, ?_⟩
    · intro w hw
      by_cases hwv : w = v
      · exact Finset.mem_insert.mpr (Or.inl hwv)
      · exact Finset.mem_insert_of_mem (hst (Finset.mem_erase.mpr ⟨hwv, hw⟩))
    · rw [Finset.card_insert_of_notMem htL.2.1, hcard]

theorem dualGraph_preconnected_of_common_vertex
    [NormedAddCommGroup E] [NormedSpace ℝ E] {n : ℕ}
    {K : Geometry.SimplicialComplex ℝ E} [Finite K.faces]
    (hpure : ∀ s ∈ K.faces, ∃ t ∈ K.faces, s ⊆ t ∧ t.card = n + 1)
    (hc : IsPreconnected K.space)
    (hvertex : ∀ s t : {s : Finset E // s ∈ K.faces ∧ s.card = n + 1},
      ∀ v ∈ s.1, v ∈ t.1 → (dualGraph n K).Reachable s t) :
    (dualGraph n K).Preconnected := by
  classical
  let T := {s : Finset E // s ∈ K.faces ∧ s.card = n + 1}
  let _ : Finite T := ((Set.toFinite K.faces).subset (fun _ h => h.1)).to_subtype
  intro s t
  by_contra hst
  let P : Set E := ⋃ u : {u : T // (dualGraph n K).Reachable s u},
    convexHull ℝ (u.1.1 : Set E)
  let Q : Set E := ⋃ u : {u : T // ¬ (dualGraph n K).Reachable s u},
    convexHull ℝ (u.1.1 : Set E)
  have hP : IsClosed P := isClosed_iUnion_of_finite fun u =>
    (u.1.1.finite_toSet.isCompact_convexHull ℝ).isClosed
  have hQ : IsClosed Q := isClosed_iUnion_of_finite fun u =>
    (u.1.1.finite_toSet.isCompact_convexHull ℝ).isClosed
  have hcover : K.space ⊆ P ∪ Q := by
    intro x hx
    obtain ⟨f, hf, hxf⟩ := K.mem_space_iff.mp hx
    obtain ⟨u, hu, hfu, hucard⟩ := hpure f hf
    let U : T := ⟨u, hu, hucard⟩
    have hxU : x ∈ convexHull ℝ (u : Set E) := convexHull_mono hfu hxf
    by_cases hreach : (dualGraph n K).Reachable s U
    · exact Or.inl (mem_iUnion.mpr ⟨⟨U, hreach⟩, hxU⟩)
    · exact Or.inr (mem_iUnion.mpr ⟨⟨U, hreach⟩, hxU⟩)
  obtain ⟨a, ha⟩ := K.nonempty_of_mem_faces s.2.1
  obtain ⟨b, hb⟩ := K.nonempty_of_mem_faces t.2.1
  have haHull : a ∈ convexHull ℝ (s.1 : Set E) := subset_convexHull ℝ _ ha
  have hbHull : b ∈ convexHull ℝ (t.1 : Set E) := subset_convexHull ℝ _ hb
  obtain ⟨x, _, hxP, hxQ⟩ := isPreconnected_closed_iff.mp hc P Q hP hQ hcover
    ⟨a, K.convexHull_subset_space s.2.1 haHull,
      mem_iUnion.mpr ⟨⟨s, SimpleGraph.Reachable.rfl⟩, haHull⟩⟩
    ⟨b, K.convexHull_subset_space t.2.1 hbHull,
      mem_iUnion.mpr ⟨⟨t, hst⟩, hbHull⟩⟩
  obtain ⟨u, hxu⟩ := mem_iUnion.mp hxP
  obtain ⟨w, hxw⟩ := mem_iUnion.mp hxQ
  have hxint := K.inter_subset_convexHull u.1.2.1 w.1.2.1 ⟨hxu, hxw⟩
  obtain ⟨v, hv⟩ := convexHull_nonempty_iff.mp ⟨x, hxint⟩
  have hv' : v ∈ u.1.1 ∧ v ∈ w.1.1 := hv
  exact w.2 (u.2.trans (hvertex u.1 w.1 v hv'.1 hv'.2))

open Classical in
noncomputable def dualGraphLinkHom [NormedAddCommGroup E] [NormedSpace ℝ E]
    (n : ℕ) (K : Geometry.SimplicialComplex ℝ E) (v : E) :
    dualGraph n (SimplicialComplex.geometricLink K {v}) →g dualGraph (n + 1) K where
  toFun s := ⟨insert v s.1,
    ((SimplicialComplex.mem_geometricLink_singleton K v s.1).mp s.2.1).2.2, by
      rw [Finset.card_insert_of_notMem
        ((SimplicialComplex.mem_geometricLink_singleton K v s.1).mp s.2.1).2.1, s.2.2]⟩
  map_rel' := by
    rintro s t ⟨hne, f, hf, hcard, hfs, hft⟩
    have hslink := (SimplicialComplex.mem_geometricLink_singleton K v s.1).mp s.2.1
    have htlink := (SimplicialComplex.mem_geometricLink_singleton K v t.1).mp t.2.1
    have hflink := (SimplicialComplex.mem_geometricLink_singleton K v f).mp hf
    refine ⟨?_, insert v f, hflink.2.2, ?_,
      Finset.insert_subset_insert v hfs, Finset.insert_subset_insert v hft⟩
    · intro heq
      apply hne
      apply Subtype.ext
      have heq' := congrArg (fun s : {s : Finset E // s ∈ K.faces ∧ s.card = n + 1 + 1}
        => s.1.erase v) heq
      simpa only [Finset.erase_insert hslink.2.1, Finset.erase_insert htlink.2.1] using heq'
    · rw [Finset.card_insert_of_notMem hflink.2.1, hcard]

open Classical in
theorem dualGraph_reachable_of_geometricLink_preconnected
    [NormedAddCommGroup E] [NormedSpace ℝ E] {n : ℕ}
    {K : Geometry.SimplicialComplex ℝ E} {v : E}
    (hconn : (dualGraph n (SimplicialComplex.geometricLink K {v})).Preconnected)
    (s t : {s : Finset E // s ∈ K.faces ∧ s.card = n + 1 + 1})
    (hvs : v ∈ s.1) (hvt : v ∈ t.1) : (dualGraph (n + 1) K).Reachable s t := by
  classical
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
  have hsCard : (s.1.erase v).card = n + 1 := by
    rw [Finset.card_erase_of_mem hvs, s.2.2]
    omega
  have htCard : (t.1.erase v).card = n + 1 := by
    rw [Finset.card_erase_of_mem hvt, t.2.2]
    omega
  have hreach := (hconn ⟨s.1.erase v, hsL, hsCard⟩ ⟨t.1.erase v, htL, htCard⟩).map
    (dualGraphLinkHom n K v)
  have hsEq : dualGraphLinkHom n K v ⟨s.1.erase v, hsL, hsCard⟩ = s :=
    Subtype.ext (Finset.insert_erase hvs)
  have htEq : dualGraphLinkHom n K v ⟨t.1.erase v, htL, htCard⟩ = t :=
    Subtype.ext (Finset.insert_erase hvt)
  rwa [hsEq, htEq] at hreach

open Classical in
theorem IsCombinatorialManifoldWithBoundary.dualGraph_preconnected
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {n : ℕ} {K : Geometry.SimplicialComplex ℝ E} [Finite K.faces]
    (hK : IsCombinatorialManifoldWithBoundary n K) (hc : IsPreconnected K.space) :
    (dualGraph n K).Preconnected := by
  classical
  induction n generalizing K with
  | zero =>
    apply dualGraph_preconnected_of_common_vertex
      (fun _ hs => hK.exists_face_superset_card_eq hs) hc
    intro s t v hvs hvt
    have hs : ({v} : Finset E) = s.1 := Finset.eq_of_subset_of_card_le
      (Finset.singleton_subset_iff.mpr hvs) (by rw [s.2.2]; simp)
    have ht : ({v} : Finset E) = t.1 := Finset.eq_of_subset_of_card_le
      (Finset.singleton_subset_iff.mpr hvt) (by rw [t.2.2]; simp)
    have heq : s = t := Subtype.ext (hs.symm.trans ht)
    rw [heq]
  | succ n ih =>
    apply dualGraph_preconnected_of_common_vertex
      (fun _ hs => hK.exists_face_superset_card_eq hs) hc
    intro s t v hvs hvt
    have hvK : {v} ∈ K.faces := K.down_closed s.2.1
      (Finset.singleton_subset_iff.mpr hvs) (Finset.singleton_nonempty v)
    cases n with
    | zero =>
      by_cases heq : s = t
      · rw [heq]
      · exact SimpleGraph.Adj.reachable ⟨heq, {v}, hvK, Finset.card_singleton _,
          Finset.singleton_subset_iff.mpr hvs, Finset.singleton_subset_iff.mpr hvt⟩
    | succ n =>
      let L := SimplicialComplex.geometricLink K {v}
      have hL : IsCombinatorialManifoldWithBoundary (n + 1) L := by
        rcases hK v hvK with hs | hb
        · exact hs.isCombinatorialManifold.isCombinatorialManifoldWithBoundary
        · exact hb.isCombinatorialManifoldWithBoundary
      have hLc : IsPreconnected L.space := by
        rcases hK v hvK with hs | hb
        · exact hs.isConnected.isPreconnected
        · exact hb.isConnected.isPreconnected
      exact dualGraph_reachable_of_geometricLink_preconnected (ih hL hLc) s t hvs hvt

end DifferentialGeometry.Topology.PiecewiseLinear
