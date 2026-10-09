/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.BallRegularClosed
import DifferentialGeometry.Topology.PiecewiseLinear.SplitDiskPseudoCellFamily

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

private theorem connectedComponentIn_eq_of_finite_closed_partition
    {X : Type*} [TopologicalSpace X] {ι : Type*} [Finite ι]
    {S : Set X} {P : ι → Set X}
    (hcover : S = ⋃ i, P i ∩ S)
    (hclosed : ∀ i, IsClosed (P i))
    (hdisj : ∀ i j, i ≠ j → Disjoint (P i ∩ S) (P j ∩ S))
    (hconn : ∀ i, IsConnected (P i ∩ S))
    (i : ι) {x : X} (hx : x ∈ P i ∩ S) :
    connectedComponentIn S x = P i ∩ S := by
  let T : Set S := (Subtype.val : S → X) ⁻¹' P i
  have hTclosed : IsClosed T := (hclosed i).preimage continuous_subtype_val
  have hother : IsClosed (⋃ j, ⋃ (_ : j ≠ i), P j) :=
    isClosed_iUnion_of_finite fun j =>
      isClosed_iUnion_of_finite fun _ => hclosed j
  have hcomp : Tᶜ = (Subtype.val : S → X) ⁻¹'
      (⋃ j, ⋃ (_ : j ≠ i), P j) := by
    ext q
    constructor
    · intro hqi
      have hqcover : (q : X) ∈ ⋃ j, P j ∩ S := hcover ▸ q.property
      obtain ⟨j, hqj⟩ := mem_iUnion.mp hqcover
      have hji : j ≠ i := by
        intro h
        subst j
        exact hqi hqj.1
      exact mem_iUnion₂.mpr ⟨j, hji, hqj.1⟩
    · intro hq
      obtain ⟨j, hji, hqj⟩ := mem_iUnion₂.mp hq
      intro hqi
      exact disjoint_left.mp (hdisj i j hji.symm)
        ⟨hqi, q.property⟩ ⟨hqj, q.property⟩
  have hTopen : IsOpen T := by
    have hTc : IsClosed Tᶜ := hcomp ▸ hother.preimage continuous_subtype_val
    simpa only [compl_compl] using hTc.isOpen_compl
  have hTclopen : IsClopen T := ⟨hTclosed, hTopen⟩
  have hxS : x ∈ S := hx.2
  have hxT : (⟨x, hxS⟩ : S) ∈ T := hx.1
  have hsubset : connectedComponentIn S x ⊆ P i ∩ S := by
    rw [connectedComponentIn_eq_image hxS]
    rintro y ⟨q, hq, rfl⟩
    exact ⟨hTclopen.connectedComponent_subset hxT hq, q.property⟩
  exact Subset.antisymm hsubset
    ((hconn i).isPreconnected.subset_connectedComponentIn hx inter_subset_right)

open Classical in
theorem IsTube.interior_dualCell_disjoint_splitDisk
    {K : Geometry.SimplicialComplex ℝ E3} {N N' : Set E3}
    {C : E3 → Set E3} {D Dbd : Finset E3 → Set E3} {h : E3 → E3}
    (ht : IsTube K N C D Dbd h N') {v : E3} (hv : v ∈ K.vertices)
    {e : Finset E3} (he : e ∈ K.faces) (hc : e.card = 2) :
    Disjoint (interior (C v)) (D e) := by
  obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp hc
  have ha : a ∈ K.vertices :=
    K.down_closed he (Finset.singleton_subset_iff.mpr
      (Finset.mem_insert_self a {b})) (Finset.singleton_nonempty a)
  have hDa : D {a, b} ⊆ C a :=
    (ht.splitDisk_subset_frontier ha he (Finset.card_pair hab)
      (Finset.mem_insert_self a {b})).trans
      (ht.dualBall a ha).isPolyhedron.isClosed.frontier_subset
  apply disjoint_left.mpr
  intro x hxint hxD
  have hfr : x ∈ frontier (C v) := by
    by_cases hva : v = a
    · subst v
      exact ht.splitDisk_subset_frontier ha he (Finset.card_pair hab)
        (Finset.mem_insert_self a {b}) hxD
    · exact ht.dualCell_inter_subset_frontier hv ha hva
        ⟨interior_subset hxint, hDa hxD⟩
  exact disjoint_left.mp disjoint_interior_frontier hxint hfr

open Classical in
theorem IsTube.connected_dualCell_sdiff_splitDisks
    {K : Geometry.SimplicialComplex ℝ E3} {N N' : Set E3}
    {C : E3 → Set E3} {D Dbd : Finset E3 → Set E3} {h : E3 → E3}
    (ht : IsTube K N C D Dbd h N') {v : E3} (hv : v ∈ K.vertices) :
    IsConnected (C v \
      ⋃ e ∈ {e : Finset E3 | e ∈ K.faces ∧ e.card = 2}, D e) ∧
    closure (C v \
      ⋃ e ∈ {e : Finset E3 | e ∈ K.faces ∧ e.card = 2}, D e) = C v := by
  let E : Set E3 :=
    ⋃ e ∈ {e : Finset E3 | e ∈ K.faces ∧ e.card = 2}, D e
  have hInt : interior (C v) ⊆ C v \ E := by
    intro x hx
    refine ⟨interior_subset hx, ?_⟩
    rintro hxE
    obtain ⟨e, ⟨he, hc⟩, hxD⟩ := mem_iUnion₂.mp hxE
    exact disjoint_left.mp (ht.interior_dualCell_disjoint_splitDisk hv he hc) hx hxD
  have hcl : closure (interior (C v)) = C v :=
    (ht.dualBall v hv).closure_interior_of_finrank finrank_euclideanSpace_fin
  have hclosed : IsClosed (C v) := (ht.dualBall v hv).isPolyhedron.isClosed
  have hclE : closure (C v \ E) = C v := by
    apply Subset.antisymm
    · exact closure_minimal sdiff_subset hclosed
    · calc
        C v = closure (interior (C v)) := hcl.symm
        _ ⊆ closure (C v \ E) := closure_mono hInt
  have hconn : IsConnected (interior (C v)) :=
    (ht.dualBall v hv).isConnected_interior_of_finrank finrank_euclideanSpace_fin
  exact ⟨hconn.subset_closure hInt (by rw [hcl]; exact sdiff_subset),
    hclE⟩

open Classical in
theorem IsTube.vertex_notMem_splitDisk
    {K : Geometry.SimplicialComplex ℝ E3} {N N' : Set E3}
    {C : E3 → Set E3} {D Dbd : Finset E3 → Set E3} {h : E3 → E3}
    (ht : IsTube K N C D Dbd h N') {v : E3} (hv : v ∈ K.vertices)
    {e : Finset E3} (he : e ∈ K.faces) (hc : e.card = 2) :
    v ∉ D e := by
  have hcent : v ≠ e.centroid ℝ id := by
    intro h
    have hx : e.centroid ℝ id ∈ convexHull ℝ (({v} : Finset E3) : Set E3) := by
      rw [← h]
      exact subset_convexHull ℝ _ (Finset.mem_coe.mpr (Finset.mem_singleton_self v))
    have hsub := face_subset_of_mem_openSimplex_of_mem_convexHull K he hv
      (centroid_mem_openSimplex (K.nonempty_of_mem_faces he)) hx
    have hle := Finset.card_le_card hsub
    rw [hc, Finset.card_singleton] at hle
    omega
  intro hvD
  have hmem : v ∈ D e ∩ K.space :=
    ⟨hvD, Geometry.SimplicialComplex.vertices_subset_space hv⟩
  rw [ht.splitMidpoint he hc] at hmem
  exact hcent (mem_singleton_iff.mp hmem)

open Classical in
theorem IsTube.dualCell_inter_subset_splitDisks
    {K : Geometry.SimplicialComplex ℝ E3} {N N' : Set E3}
    {C : E3 → Set E3} {D Dbd : Finset E3 → Set E3} {h : E3 → E3}
    (ht : IsTube K N C D Dbd h N') {u v : E3}
    (hu : u ∈ K.vertices) (hv : v ∈ K.vertices) (huv : u ≠ v) :
    C u ∩ C v ⊆
      ⋃ e ∈ {e : Finset E3 | e ∈ K.faces ∧ e.card = 2}, D e := by
  intro x hx
  by_cases he : ({u, v} : Finset E3) ∈ K.faces
  · rw [ht.interEdge hu hv huv he] at hx
    exact mem_iUnion₂.mpr ⟨{u, v}, ⟨he, Finset.card_pair huv⟩, hx⟩
  · rw [ht.interNonEdge hu hv huv he] at hx
    simp at hx

open Classical in
theorem IsTube.connectedComponentIn_splitDisk_complement
    {K : Geometry.SimplicialComplex ℝ E3} {N N' : Set E3}
    {C : E3 → Set E3} {D Dbd : Finset E3 → Set E3} {h : E3 → E3}
    (ht : IsTube K N C D Dbd h N') {v : E3} (hv : v ∈ K.vertices) :
    connectedComponentIn
      (N \ ⋃ e ∈ {e : Finset E3 | e ∈ K.faces ∧ e.card = 2}, D e) v =
        C v \ ⋃ e ∈ {e : Finset E3 | e ∈ K.faces ∧ e.card = 2}, D e ∧
    closure (connectedComponentIn
      (N \ ⋃ e ∈ {e : Finset E3 | e ∈ K.faces ∧ e.card = 2}, D e) v) = C v := by
  let E : Set E3 :=
    ⋃ e ∈ {e : Finset E3 | e ∈ K.faces ∧ e.card = 2}, D e
  let X : Set E3 := N \ E
  let _ : Finite K.vertices := ht.finite_vertices.to_subtype
  let P : K.vertices → Set E3 := fun w => C w
  have hcover : X = ⋃ w : K.vertices, P w ∩ X := by
    ext x
    constructor
    · intro hx
      obtain ⟨w, hw, hxw⟩ := mem_iUnion₂.mp (ht.unionEq ▸ hx.1)
      exact mem_iUnion.mpr ⟨⟨w, hw⟩, hxw, hx⟩
    · intro hx
      obtain ⟨w, hw⟩ := mem_iUnion.mp hx
      exact hw.2
  have hclosed : ∀ w : K.vertices, IsClosed (P w) :=
    fun w => (ht.dualBall w w.property).isPolyhedron.isClosed
  have hdisj : ∀ w z : K.vertices, w ≠ z →
      Disjoint (P w ∩ X) (P z ∩ X) := by
    intro w z hwz
    apply disjoint_left.mpr
    intro x hxw hxz
    have hxE : x ∈ E :=
      ht.dualCell_inter_subset_splitDisks w.property z.property
        (fun h => hwz (Subtype.ext h)) ⟨hxw.1, hxz.1⟩
    exact hxw.2.2 hxE
  have hconn : ∀ w : K.vertices, IsConnected (P w ∩ X) := by
    intro w
    have heq : P w ∩ X = C w \ E := by
      ext x
      constructor
      · rintro ⟨hxC, hxX⟩
        exact ⟨hxC, hxX.2⟩
      · rintro ⟨hxC, hxE⟩
        exact ⟨hxC, ⟨ht.dualCell_subset w.property hxC, hxE⟩⟩
    rw [heq]
    exact (ht.connected_dualCell_sdiff_splitDisks w.property).1
  have hvX : v ∈ X := by
    refine ⟨ht.dualCell_subset hv (ht.mem_dualCell hv), ?_⟩
    rintro hvE
    obtain ⟨e, ⟨he, hc⟩, hve⟩ := mem_iUnion₂.mp hvE
    exact ht.vertex_notMem_splitDisk hv he hc hve
  have hvP : v ∈ P ⟨v, hv⟩ ∩ X := ⟨ht.mem_dualCell hv, hvX⟩
  have hcomp := connectedComponentIn_eq_of_finite_closed_partition
    hcover hclosed hdisj hconn ⟨v, hv⟩ hvP
  have heq : P ⟨v, hv⟩ ∩ X = C v \ E := by
    ext x
    constructor
    · rintro ⟨hxC, hxX⟩
      exact ⟨hxC, hxX.2⟩
    · rintro ⟨hxC, hxE⟩
      exact ⟨hxC, ⟨ht.dualCell_subset hv hxC, hxE⟩⟩
  rw [heq] at hcomp
  exact ⟨hcomp, by rw [hcomp]; exact
    (ht.connected_dualCell_sdiff_splitDisks hv).2⟩

end DifferentialGeometry.Topology.PiecewiseLinear
