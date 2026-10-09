/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactResidualOuterArc
import DifferentialGeometry.Topology.PiecewiseLinear.PolygonCircleParametrization

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

variable {C : Set E3} {K K' : Geometry.SimplicialComplex ℝ E3}
  {src srcBd : Section34CompactLabelOf K K' → Set E3}

theorem Section34CompactCutFrame.exists_boundaryLink_cycle
    (hcut : Section34CompactCutFrame C K K' src srcBd) {u : E3}
    (huK : ({u} : Finset E3) ∈ K.faces) (hub : u ∈ frontier K.space) :
    ∃ (m : ℕ) (v : Fin (m + 2) → E3), 1 ≤ m ∧ Function.Injective v ∧ (∀ k, v k ≠ u) ∧
      (∀ k, ∃ τ ∈ K.faces, convexHull ℝ (τ : Set E3) ⊆ frontier K.space ∧ u ∈ τ ∧
        v (k - 1) ∈ τ ∧ v k ∈ τ) ∧
      (∀ τ ∈ K.faces, convexHull ℝ (τ : Set E3) ⊆ frontier K.space → τ.card = 3 → u ∈ τ →
        ∃ k, v (k - 1) ∈ τ ∧ v k ∈ τ) ∧
      ∀ z : E3, z ≠ u → ∀ τ ∈ K.faces, convexHull ℝ (τ : Set E3) ⊆ frontier K.space →
        u ∈ τ → z ∈ τ → ∃ k, z = v k := by
  let _ : DecidableEq E3 := Classical.decEq E3
  obtain ⟨-, hK, -, hman, -⟩ := id hcut
  let _ : Finite K.faces := hK.to_subtype
  let _ : Finite (boundaryComplex 3 K).faces := (boundaryComplex_faces_finite 3 K).to_subtype
  have hfr : frontier K.space = (boundaryComplex 3 K).space :=
    frontier_space_eq_boundaryComplex_space (n := 2) hman
  have hLK := boundaryComplex_faces_subset 3 K
  have hL : IsCombinatorialManifold 2 (boundaryComplex 3 K) :=
    isCombinatorialManifold_boundaryComplex (n := 2) K hman
  have hLb : ∀ s ∈ (boundaryComplex 3 K).faces,
      convexHull ℝ (s : Set E3) ⊆ frontier K.space := fun s hs => by
    rw [hfr]
    exact (boundaryComplex 3 K).convexHull_subset_space hs
  have hbL : ∀ s ∈ K.faces, convexHull ℝ (s : Set E3) ⊆ frontier K.space →
      s ∈ (boundaryComplex 3 K).faces := fun s hs hsb =>
    mem_faces_of_mem_openSimplex_of_mem_space hLK hs
      (centroid_mem_openSimplex (K.nonempty_of_mem_faces hs))
      (by rw [← hfr]; exact hsb (s.centroid_mem_convexHull (K.nonempty_of_mem_faces hs)))
  have huL : ({u} : Finset E3) ∈ (boundaryComplex 3 K).faces := hbL _ huK (by
    rw [Finset.coe_singleton, convexHull_singleton, singleton_subset_iff]
    exact hub)
  let Lk := SimplicialComplex.geometricLink (boundaryComplex 3 K) {u}
  let _ : Finite Lk.faces := ((boundaryComplex_faces_finite 3 K).subset
    (geometricLink_faces_subset (boundaryComplex 3 K) {u})).to_subtype
  have hmemLk : ∀ t : Finset E3, t ∈ Lk.faces ↔
      t.Nonempty ∧ Disjoint {u} t ∧ {u} ∪ t ∈ (boundaryComplex 3 K).faces := fun t =>
    mem_geometricLink_faces_iff (boundaryComplex 3 K)
  have hsphere : IsPLSphere 1 Lk.space := hL u huL
  have hLk1 : IsCombinatorialManifold 1 Lk := by
    rw [isCombinatorialManifold_one_iff]
    refine ⟨fun s hs => ?_, fun v hv => ?_⟩
    · obtain ⟨-, hdisj, hU⟩ := (hmemLk s).mp hs
      have h1 := hL.card_le (boundaryComplex 3 K) hU
      rw [Finset.card_union_of_disjoint hdisj, Finset.card_singleton] at h1
      omega
    · obtain ⟨-, hdisj, hU⟩ := (hmemLk {v}).mp hv
      have hcard : ({u} ∪ {v} : Finset E3).card = 1 + 1 := by
        rw [Finset.card_union_of_disjoint hdisj]
        simp
      obtain ⟨a, b, hab, hset⟩ := hL.codimension_one_cofaces (boundaryComplex 3 K) hU hcard
      refine ⟨a, b, hab, ?_⟩
      rw [← hset]
      ext x
      simp only [mem_ofPred_eq]
      have heq : ({u} ∪ {v, x} : Finset E3) = insert x ({u} ∪ {v}) := by
        ext y
        simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
        tauto
      constructor
      · rintro ⟨hxv, hx⟩
        obtain ⟨-, hdx, hUx⟩ := (hmemLk {v, x}).mp hx
        refine ⟨fun hx' => ?_, by rw [← heq]; exact hUx⟩
        rcases Finset.mem_union.mp hx' with h | h
        · exact Finset.disjoint_left.mp hdx h (by simp)
        · exact hxv (Finset.mem_singleton.mp h)
      · rintro ⟨hx', hx⟩
        refine ⟨fun h => hx' (Finset.mem_union_right _ (by rw [h]; simp)), ?_⟩
        refine (hmemLk {v, x}).mpr ⟨Finset.insert_nonempty _ _, ?_, by rw [heq]; exact hx⟩
        rw [Finset.disjoint_singleton_left]
        intro hu
        rcases Finset.mem_insert.mp hu with h | h
        · exact Finset.disjoint_singleton_left.mp hdisj (by rw [← h]; simp)
        · exact hx' (Finset.mem_union_left _ (by rw [Finset.mem_singleton.mp h]; simp))
  let _ : Fintype Lk.vertices := (SimplicialComplex.finite_vertices Lk).fintype
  have hconn := edgeGraph_connected_of_isConnected_space Lk hsphere.isConnected
  have hdeg := ncard_neighborSet_edgeGraph_eq_two hLk1
  obtain ⟨g⟩ := (SimplicialComplex.edgeGraph Lk).exists_cycleGraphIsoOfConnectedDegreeTwo hconn hdeg
  have h3 := (SimplicialComplex.edgeGraph Lk).three_le_card_of_connected_degree_two hconn hdeg
  generalize Fintype.card Lk.vertices = N at g h3
  obtain ⟨m, rfl⟩ : ∃ m, N = m + 2 := ⟨N - 2, by omega⟩
  have hvert : ∀ k : Fin (m + 2), ({(g k : E3)} : Finset E3) ∈ Lk.faces := fun k => (g k).2
  have hvu : ∀ k : Fin (m + 2), (g k : E3) ≠ u := fun k h => by
    obtain ⟨-, hdisj, -⟩ := (hmemLk _).mp (hvert k)
    exact Finset.disjoint_singleton.mp hdisj h.symm
  have hadj : ∀ k l : Fin (m + 2), (SimplicialComplex.edgeGraph Lk).Adj (g k) (g l) ↔
      k - l = 1 ∨ l - k = 1 := fun k l => by
    rw [g.map_adj_iff]
    exact SimpleGraph.cycleGraph_adj
  refine ⟨m, fun k => (g k : E3), by omega, fun k l h => g.injective (Subtype.ext h), hvu,
    fun k => ?_, fun τ hτ hτb hτ3 huτ => ?_, fun z hzu τ hτ hτb huτ hzτ => ?_⟩
  · obtain ⟨-, -, hU⟩ := (hmemLk _).mp ((hadj (k - 1) k).mpr (Or.inr (sub_sub_cancel k 1))).2
    refine ⟨_, hLK hU, hLb _ hU, Finset.mem_union_left _ (Finset.mem_singleton_self u),
      Finset.mem_union_right _ (Finset.mem_insert_self _ _),
      Finset.mem_union_right _ (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))⟩
  · have hτL := hbL τ hτ hτb
    have hcardt : (τ.erase u).card = 2 := by
      rw [Finset.card_erase_of_mem huτ, hτ3]
    obtain ⟨a, b, hab, hteq⟩ := Finset.card_eq_two.mp hcardt
    have htLk : ({a, b} : Finset E3) ∈ Lk.faces := by
      rw [← hteq]
      refine (hmemLk _).mpr ⟨?_, ?_, ?_⟩
      · rw [hteq]
        exact Finset.insert_nonempty _ _
      · rw [Finset.disjoint_singleton_left]
        exact Finset.notMem_erase u τ
      · rw [← Finset.insert_eq, Finset.insert_erase huτ]
        exact hτL
    have haτ : a ∈ τ := Finset.mem_of_mem_erase (by rw [hteq]; simp)
    have hbτ : b ∈ τ := Finset.mem_of_mem_erase (by rw [hteq]; simp)
    have ha : ({a} : Finset E3) ∈ Lk.faces := Lk.down_closed htLk (by simp)
      (Finset.singleton_nonempty a)
    have hb : ({b} : Finset E3) ∈ Lk.faces := Lk.down_closed htLk (by simp)
      (Finset.singleton_nonempty b)
    obtain ⟨ka, hka⟩ := g.surjective ⟨a, ha⟩
    obtain ⟨kb, hkb⟩ := g.surjective ⟨b, hb⟩
    have hga : (g ka : E3) = a := by rw [hka]
    have hgb : (g kb : E3) = b := by rw [hkb]
    have hadjab : (SimplicialComplex.edgeGraph Lk).Adj (g ka) (g kb) := by
      rw [hka, hkb]
      exact ⟨fun h => hab (congrArg Subtype.val h), htLk⟩
    rcases (hadj ka kb).mp hadjab with h | h
    · refine ⟨ka, ?_, by change (g ka : E3) ∈ τ; rw [hga]; exact haτ⟩
      have hkb' : kb = ka - 1 := by rw [← h, sub_sub_cancel]
      change (g (ka - 1) : E3) ∈ τ
      rw [← hkb', hgb]
      exact hbτ
    · refine ⟨kb, ?_, by change (g kb : E3) ∈ τ; rw [hgb]; exact hbτ⟩
      have hka' : ka = kb - 1 := by rw [← h, sub_sub_cancel]
      change (g (kb - 1) : E3) ∈ τ
      rw [← hka', hga]
      exact haτ
  · have hτL := hbL τ hτ hτb
    have hzLk : ({z} : Finset E3) ∈ Lk.faces := by
      refine (hmemLk _).mpr ⟨Finset.singleton_nonempty z, Finset.disjoint_singleton.mpr hzu.symm,
        (boundaryComplex 3 K).down_closed hτL ?_
          ⟨u, Finset.mem_union_left _ (Finset.mem_singleton_self u)⟩⟩
      intro q hq
      rcases Finset.mem_union.mp hq with hq | hq
      · rw [Finset.mem_singleton.mp hq]
        exact huτ
      · rw [Finset.mem_singleton.mp hq]
        exact hzτ
    obtain ⟨k, hk⟩ := g.surjective ⟨z, hzLk⟩
    exact ⟨k, by change z = (g k : E3); rw [hk]⟩

theorem Section34CompactCutFrame.exists_outerEnum_of_vertex
    (hcut : Section34CompactCutFrame C K K' src srcBd) {w : Section34CompactVertexIndex K K'}
    {u : E3} (hwu : w.1 = {u}) (huK : ({u} : Finset E3) ∈ K.faces)
    (hub : u ∈ frontier K.space) :
    ∃ (m : ℕ) (sK : Fin (m + 2) → Section34CompactSimplexIndex K 3)
      (eK : Fin (m + 2) → Section34CompactEdgeIndex K K'),
      (∀ k, convexHull ℝ ((sK k).1 : Set E3) ⊆ frontier K.space) ∧
      (∀ k, Section34Incident w.1 (sK k).1) ∧
      (∀ k, w.1 ⊆ (eK k).1) ∧ Function.Injective sK ∧ Function.Injective eK ∧
      (∀ k l, Section34Incident (eK l).1 (sK k).1 ↔ l = k ∨ l + 1 = k) ∧
      (∀ s : Section34CompactSimplexIndex K 3, convexHull ℝ (s.1 : Set E3) ⊆ frontier K.space →
        Section34Incident w.1 s.1 → ∃ k, s = sK k) ∧
      ∀ e : Section34CompactEdgeIndex K K', convexHull ℝ (e.1 : Set E3) ⊆ frontier K.space →
        w.1 ⊆ e.1 → ∃ k, e = eK k := by
  obtain ⟨-, -, -, -, hsub, -⟩ := id hcut
  obtain ⟨m, v, hm1, hvinj, hvu, htri, htricomp, hvcomp⟩ :=
    hcut.exists_boundaryLink_cycle huK hub
  have hkk : ∀ k : Fin (m + 2), k - 1 ≠ k := fun k h => one_ne_zero (sub_eq_self.mp h)
  have huv : ∀ k : Fin (m + 2), ({u, v k} : Finset E3) ∈ K.faces := fun k => by
    obtain ⟨τ, hτ, -, huτ, -, hvτ⟩ := htri k
    exact K.down_closed hτ (Finset.insert_subset huτ (Finset.singleton_subset_iff.mpr hvτ))
      (Finset.insert_nonempty _ _)
  have hedge : ∀ k : Fin (m + 2), ∃ e : Section34CompactEdgeIndex K K', u ∈ e.1 ∧
      convexHull ℝ (e.1 : Set E3) ⊆ segment ℝ u (v k) ∧
      ∀ e' : Section34CompactEdgeIndex K K', u ∈ e'.1 →
        convexHull ℝ (e'.1 : Set E3) ⊆ segment ℝ u (v k) → e' = e := fun k =>
    hcut.exists_edgeIndex_mem_subset_segment (hvu k).symm (huv k)
  choose eK hueK heKseg heKu using hedge
  have hsub3 : ∀ k : Fin (m + 2), ∃ τ ∈ K.faces, convexHull ℝ (τ : Set E3) ⊆ frontier K.space ∧
      ({u, v (k - 1), v k} : Finset E3) ⊆ τ := fun k => by
    obtain ⟨τ, hτ, hτb, huτ, hv1τ, hvτ⟩ := htri k
    exact ⟨τ, hτ, hτb, Finset.insert_subset huτ (Finset.insert_subset hv1τ
      (Finset.singleton_subset_iff.mpr hvτ))⟩
  choose τK hτK hτKb hτKsub using hsub3
  have htri3 : ∀ k : Fin (m + 2), ({u, v (k - 1), v k} : Finset E3).card = 3 := fun k =>
    Finset.card_eq_three.mpr ⟨u, _, _, (hvu _).symm, (hvu _).symm,
      fun h => hkk k (hvinj h), rfl⟩
  let sK : Fin (m + 2) → Section34CompactSimplexIndex K 3 := fun k =>
    ⟨{u, v (k - 1), v k}, K.down_closed (hτK k) (hτKsub k) (Finset.insert_nonempty _ _),
      htri3 k⟩
  have hsKu : ∀ k, u ∈ (sK k).1 := fun k => Finset.mem_insert_self _ _
  have hcard2 : ∀ e : Section34CompactEdgeIndex K K', 1 < e.1.card := fun e => by
    rw [e.2.2.1]
    norm_num
  have h2ne : (1 : Fin (m + 2)) + 1 ≠ 0 := by
    intro h
    have hv := congrArg Fin.val h
    rw [Fin.val_add, Fin.val_one, Fin.val_zero, Nat.mod_eq_of_lt (by omega)] at hv
    omega
  have hsKinj : Function.Injective sK := by
    intro i j hij
    have hmem : ∀ x, x ∈ (sK i).1 → x ∈ (sK j).1 := fun x hx => by
      rw [← hij]
      exact hx
    have hgi := hmem (v i) (by simp [sK])
    have hgi' := hmem (v (i - 1)) (by simp [sK])
    simp only [sK, Finset.mem_insert, Finset.mem_singleton] at hgi hgi'
    rcases hgi with h | h | h
    · exact absurd h (hvu i)
    · have hij1 := hvinj h
      rcases hgi' with h' | h' | h'
      · exact absurd h' (hvu _)
      · exact absurd (hvinj h') (by rw [hij1]; exact hkk (j - 1))
      · have hij2 := hvinj h'
        exfalso
        apply h2ne
        have hii : i - 1 - 1 = i := by rw [hij2, hij1]
        rw [sub_sub] at hii
        exact sub_eq_self.mp hii
    · exact hvinj h
  have heKinj : Function.Injective eK := by
    intro i j hij
    by_contra hne
    obtain ⟨x, hx, hxu⟩ := Finset.exists_mem_ne (hcard2 (eK i)) u
    have hx1 : x ∈ segment ℝ u (v i) := heKseg i (subset_convexHull ℝ _ hx)
    have hx2 : x ∈ segment ℝ u (v j) := heKseg j (by rw [← hij]; exact subset_convexHull ℝ _ hx)
    have h := segment_inter_segment_subset_of_mem_faces (huv i) (huv j) ⟨hx1, hx2⟩
    have hsubu : ({u, v i} : Set E3) ∩ {u, v j} ⊆ {u} := by
      rintro y ⟨hy1, hy2⟩
      rcases hy1 with hy1 | hy1
      · exact hy1
      · rcases hy2 with hy2 | hy2
        · exact hy2
        · exact absurd (hvinj ((mem_singleton_iff.mp hy1).symm.trans
            (mem_singleton_iff.mp hy2))) hne
    have h' := convexHull_mono hsubu h
    rw [convexHull_singleton] at h'
    exact hxu h'
  refine ⟨m, sK, eK, fun k => (convexHull_mono (Finset.coe_subset.mpr (hτKsub k))).trans
    (hτKb k), fun k => ?_, fun k => ?_, hsKinj, heKinj, fun k l => ?_, fun s hs hws => ?_,
    fun e he hwe => ?_⟩
  · intro z hz
    rw [hwu, Finset.coe_singleton, mem_singleton_iff] at hz
    rw [hz]
    exact subset_convexHull ℝ _ (hsKu k)
  · rw [hwu]
    exact Finset.singleton_subset_iff.mpr (hueK k)
  · rw [section34Incident_iff_mem_of_subset_segment (sK k).2.1 (huv l) (hcard2 (eK l))
      (heKseg l) (hsKu k)]
    simp only [sK, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro (h | h | h)
      · exact absurd h (hvu l)
      · exact Or.inr (eq_sub_iff_add_eq.mp (hvinj h))
      · exact Or.inl (hvinj h)
    · rintro (h | h)
      · rw [h]
        exact Or.inr (Or.inr rfl)
      · refine Or.inr (Or.inl ?_)
        rw [← h, add_sub_cancel_right]
  · have hus : u ∈ s.1 := by
      by_contra hus
      exact not_section34Incident_of_notMem_left s.2.1 huK (by rw [hwu]; simp) hus hws
    obtain ⟨k, hv1s, hvs⟩ := htricomp s.1 s.2.1 hs s.2.2 hus
    refine ⟨k, Subtype.ext (Finset.eq_of_subset_of_card_le ?_ ?_).symm⟩
    · exact Finset.insert_subset hus (Finset.insert_subset hv1s
        (Finset.singleton_subset_iff.mpr hvs))
    · rw [s.2.2]
      exact (htri3 k).ge
  · have hue : u ∈ e.1 := hwe (by rw [hwu]; exact Finset.mem_singleton_self u)
    obtain ⟨s₁, s₂, -, hs1b, -, hes1, -, -⟩ := hcut.exists_boundaryTriangle_pair e he
    obtain ⟨x, hx, y, hy, hxy, hexy⟩ :=
      exists_segment_of_incident_section34CompactEdgeIndex hsub s₁.2.1 e hes1
    have hxyK : ({x, y} : Finset E3) ∈ K.faces :=
      K.down_closed s₁.2.1 (Finset.insert_subset hx (Finset.singleton_subset_iff.mpr hy))
        (Finset.insert_nonempty _ _)
    have hux : u ∈ segment ℝ x y := hexy (subset_convexHull ℝ _ hue)
    have hu' := mem_convexHull_inter_of_mem_segment huK hxyK hux
      (by rw [Finset.coe_singleton, convexHull_singleton]; exact mem_singleton u)
    have huxy : u = x ∨ u = y := by
      by_contra hne
      rw [not_or] at hne
      have hnot : u ∉ ({x, y} : Finset E3) := by
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact hne
      rw [Finset.inter_singleton_of_notMem hnot, Finset.coe_empty, convexHull_empty] at hu'
      exact hu'
    have hus1 : u ∈ s₁.1 := by
      rcases huxy with h | h
      · rw [h]
        exact hx
      · rw [h]
        exact hy
    obtain ⟨z, hz, hzu, hez⟩ : ∃ z ∈ s₁.1, z ≠ u ∧
        convexHull ℝ (e.1 : Set E3) ⊆ segment ℝ u z := by
      rcases huxy with h | h
      · rw [← h] at hexy hxy
        exact ⟨y, hy, hxy.symm, hexy⟩
      · rw [← h, segment_symm] at hexy
        rw [← h] at hxy
        exact ⟨x, hx, hxy, hexy⟩
    obtain ⟨k, hk⟩ := hvcomp z hzu s₁.1 s₁.2.1 hs1b hus1 hz
    refine ⟨k, heKu k e hue ?_⟩
    rw [← hk]
    exact hez

theorem Section34CompactCutFrame.exists_edgePair_of_mem_segment
    (hcut : Section34CompactCutFrame C K K' src srcBd) {a b : E3} (hab : a ≠ b)
    (habK : ({a, b} : Finset E3) ∈ K.faces) {w : Section34CompactVertexIndex K K'} {p : E3}
    (hwp : w.1 = {p}) (hp : p ∈ segment ℝ a b) (hpa : p ≠ a) (hpb : p ≠ b) :
    ∃ e₀ e₁ : Section34CompactEdgeIndex K K', e₀ ≠ e₁ ∧ w.1 ⊆ e₀.1 ∧ w.1 ⊆ e₁.1 ∧
      convexHull ℝ (e₀.1 : Set E3) ⊆ segment ℝ a b ∧
      convexHull ℝ (e₁.1 : Set E3) ⊆ segment ℝ a b ∧
      ∀ e : Section34CompactEdgeIndex K K', w.1 ⊆ e.1 →
        convexHull ℝ (e.1 : Set E3) ⊆ segment ℝ a b → e = e₀ ∨ e = e₁ := by
  have hpw : p ∈ w.1 := by
    rw [hwp]
    exact Finset.mem_singleton_self p
  have hcard2 : ∀ e : Section34CompactEdgeIndex K K', 1 < e.1.card := fun e => by
    rw [e.2.2.1]
    norm_num
  have hedge_eq : ∀ e e' : Section34CompactEdgeIndex K K', e.1 ⊆ e'.1 → e = e' := fun e e' h =>
    Subtype.ext (Finset.eq_of_subset_of_card_le h (by rw [e.2.2.1, e'.2.2.1]))
  obtain ⟨n, wv, ev, -, hw0, hwn, hwpt, hev, -, hsurj, hfar⟩ :=
    hcut.exists_vertexIndex_path hab habK
  obtain ⟨i, hi, hwi⟩ := hsurj w ⟨p, hp, hwp⟩
  have hi0 : i ≠ 0 := by
    rintro rfl
    rw [← hwi, hwp] at hw0
    exact hpa (Finset.singleton_injective hw0)
  have hin : i ≠ n := by
    intro h
    rw [h] at hwi
    rw [← hwi, hwp] at hwn
    exact hpb (Finset.singleton_injective hwn)
  obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
  have hj2 : j + 2 ≤ n := by omega
  have hevseg : ∀ i < n, convexHull ℝ ((ev i).1 : Set E3) ⊆ segment ℝ a b := by
    intro i hi
    refine convexHull_min (fun z hz => ?_) (convex_segment a b)
    rw [Finset.mem_coe, hev i hi, Finset.mem_union] at hz
    rcases hz with hz | hz
    · obtain ⟨q, hq, hwq, -⟩ := hwpt i hi.le
      rw [hwq, Finset.mem_singleton] at hz
      rw [hz]
      exact hq
    · obtain ⟨q, hq, hwq, -⟩ := hwpt (i + 1) hi
      rw [hwq, Finset.mem_singleton] at hz
      rw [hz]
      exact hq
  have hwe0 : w.1 ⊆ (ev j).1 := by
    rw [hwi, hev j (by omega)]
    exact Finset.subset_union_right
  have hwe1 : w.1 ⊆ (ev (j + 1)).1 := by
    rw [hwi, hev (j + 1) (by omega)]
    exact Finset.subset_union_left
  have hne_e : ev j ≠ ev (j + 1) := by
    intro h
    have h1 : (wv j).1 ⊆ (ev (j + 1)).1 := by
      rw [← h, hev j (by omega)]
      exact Finset.subset_union_left
    have h2 : (wv (j + 2)).1 ⊆ (ev (j + 1)).1 := by
      rw [hev (j + 1) (by omega)]
      exact Finset.subset_union_right
    exact hfar j (by omega) (j + 2) hj2 (by omega) (ev (j + 1)) h1 h2
  refine ⟨ev j, ev (j + 1), hne_e, hwe0, hwe1, hevseg j (by omega), hevseg (j + 1) (by omega),
    fun e hwe hes => ?_⟩
  obtain ⟨q, hq, hqp⟩ := Finset.exists_mem_ne (hcard2 e) p
  have hqK : ({q} : Finset E3) ∈ K'.faces :=
    K'.down_closed e.2.1 (Finset.singleton_subset_iff.mpr hq) (Finset.singleton_nonempty q)
  obtain ⟨wq, hwq⟩ := exists_section34CompactVertexIndex_eq_singleton hqK
    (e.2.2.2 (subset_convexHull ℝ _ hq))
  obtain ⟨i', hi', rfl⟩ := hsurj wq ⟨q, hes (subset_convexHull ℝ _ hq), hwq⟩
  have hqe : (wv i').1 ⊆ e.1 := by
    rw [hwq]
    exact Finset.singleton_subset_iff.mpr hq
  have hpe' : (wv (j + 1)).1 ⊆ e.1 := by
    rw [← hwi]
    exact hwe
  have hi'ne : i' ≠ j + 1 := by
    intro h
    rw [h, ← hwi, hwp] at hwq
    exact hqp (Finset.singleton_injective hwq).symm
  have hcase : i' = j ∨ i' = j + 2 := by
    by_contra hne
    rw [not_or] at hne
    rcases Nat.lt_or_gt_of_ne hi'ne with h | h
    · exact hfar i' hi' (j + 1) (by omega) (by omega) e hqe hpe'
    · exact hfar (j + 1) (by omega) i' hi' (by omega) e hpe' hqe
  rcases hcase with h | h
  · refine Or.inl (hedge_eq (ev j) e ?_).symm
    rw [hev j (by omega)]
    rw [h] at hqe
    exact Finset.union_subset hqe hpe'
  · refine Or.inr (hedge_eq (ev (j + 1)) e ?_).symm
    rw [hev (j + 1) (by omega)]
    rw [h] at hqe
    exact Finset.union_subset hpe' hqe

theorem Section34CompactCutFrame.exists_outerEnum_of_edge
    (hcut : Section34CompactCutFrame C K K' src srcBd) {a b : E3} (hab : a ≠ b)
    (habK : ({a, b} : Finset E3) ∈ K.faces) (habb : segment ℝ a b ⊆ frontier K.space)
    {w : Section34CompactVertexIndex K K'} {p : E3} (hwp : w.1 = {p}) (hp : p ∈ segment ℝ a b)
    (hpa : p ≠ a) (hpb : p ≠ b) :
    ∃ (sK : Fin 2 → Section34CompactSimplexIndex K 3)
      (eK : Fin 2 → Section34CompactEdgeIndex K K'),
      (∀ k, convexHull ℝ ((sK k).1 : Set E3) ⊆ frontier K.space) ∧
      (∀ k, Section34Incident w.1 (sK k).1) ∧
      (∀ k, w.1 ⊆ (eK k).1) ∧ Function.Injective sK ∧ Function.Injective eK ∧
      (∀ k l, Section34Incident (eK l).1 (sK k).1 ↔ l = k ∨ l + 1 = k) ∧
      (∀ s : Section34CompactSimplexIndex K 3, convexHull ℝ (s.1 : Set E3) ⊆ frontier K.space →
        Section34Incident w.1 s.1 → ∃ k, s = sK k) ∧
      ∀ e : Section34CompactEdgeIndex K K', convexHull ℝ (e.1 : Set E3) ⊆ frontier K.space →
        w.1 ⊆ e.1 → ∃ k, e = eK k := by
  obtain ⟨-, -, -, -, hsub, -⟩ := id hcut
  have hpw : p ∈ w.1 := by
    rw [hwp]
    exact Finset.mem_singleton_self p
  have hbaK : ({b, a} : Finset E3) ∈ K.faces := by
    rw [Finset.pair_comm]
    exact habK
  obtain ⟨e₀, e₁, he01, hwe0, hwe1, he0s, he1s, heuniq⟩ :=
    hcut.exists_edgePair_of_mem_segment hab habK hwp hp hpa hpb
  obtain ⟨s₁, s₂, hs12, hs1b, hs2b, hes1, hes2, hsuniq⟩ :=
    hcut.exists_boundaryTriangle_pair e₀ (he0s.trans habb)
  have hab_s : ∀ s : Section34CompactSimplexIndex K 3, Section34Incident w.1 s.1 →
      a ∈ s.1 ∧ b ∈ s.1 := fun s hws => by
    refine ⟨?_, ?_⟩
    · by_contra has
      exact not_section34Incident_of_notMem_right s.2.1 hbaK hpw
        (by rw [segment_symm]; exact hp) hpb has hws
    · by_contra hbs
      exact not_section34Incident_of_notMem_right s.2.1 habK hpw hp hpa hbs hws
  have hws_of : ∀ s : Section34CompactSimplexIndex K 3, Section34Incident e₀.1 s.1 →
      Section34Incident w.1 s.1 := fun s h z hz => h (hwe0 hz)
  have hinc_all : ∀ s : Section34CompactSimplexIndex K 3, Section34Incident w.1 s.1 →
      ∀ e : Section34CompactEdgeIndex K K', convexHull ℝ (e.1 : Set E3) ⊆ segment ℝ a b →
        Section34Incident e.1 s.1 := fun s hws e hes =>
    section34Incident_of_subset_segment hes (hab_s s hws).1 (hab_s s hws).2
  refine ⟨![s₁, s₂], ![e₀, e₁], fun k => ?_, fun k => ?_, fun k => ?_, fun i j hij => ?_,
    fun i j hij => ?_, fun k l => ?_, fun s hs hws => ?_, fun e he hwe => ?_⟩
  · fin_cases k
    · exact hs1b
    · exact hs2b
  · fin_cases k
    · exact hws_of s₁ hes1
    · exact hws_of s₂ hes2
  · fin_cases k
    · exact hwe0
    · exact hwe1
  · fin_cases i <;> fin_cases j
    all_goals first
      | rfl
      | exact absurd hij hs12
      | exact absurd hij hs12.symm
  · fin_cases i <;> fin_cases j
    all_goals first
      | rfl
      | exact absurd hij he01
      | exact absurd hij he01.symm
  · fin_cases k <;> fin_cases l
    · exact iff_of_true hes1 (by decide)
    · exact iff_of_true (hinc_all s₁ (hws_of s₁ hes1) e₁ he1s) (by decide)
    · exact iff_of_true hes2 (by decide)
    · exact iff_of_true (hinc_all s₂ (hws_of s₂ hes2) e₁ he1s) (by decide)
  · rcases hsuniq s hs (hinc_all s hws e₀ he0s) with h | h
    · exact ⟨0, h⟩
    · exact ⟨1, h⟩
  · obtain ⟨s', s'', -, -, -, hes', -, -⟩ := hcut.exists_boundaryTriangle_pair e he
    obtain ⟨x, hx, y, hy, -, hexy⟩ :=
      exists_segment_of_incident_section34CompactEdgeIndex hsub s'.2.1 e hes'
    have hxyK : ({x, y} : Finset E3) ∈ K.faces :=
      K.down_closed s'.2.1 (Finset.insert_subset hx (Finset.singleton_subset_iff.mpr hy))
        (Finset.insert_nonempty _ _)
    have hpe : p ∈ e.1 := hwe hpw
    have hpxy : p ∈ segment ℝ x y := hexy (subset_convexHull ℝ _ hpe)
    have hpc := segment_inter_segment_subset_of_mem_faces hxyK habK ⟨hpxy, hp⟩
    have hax := eq_or_eq_of_mem_convexHull_inter_pair hpc hpb
    rw [Set.pair_comm a b] at hpc
    have hbx := eq_or_eq_of_mem_convexHull_inter_pair hpc hpa
    have hseg : segment ℝ x y = segment ℝ a b := by
      rcases hax with h1 | h1 <;> rcases hbx with h2 | h2
      · exact absurd (h1.trans h2.symm) hab
      · rw [← h1, ← h2]
      · rw [← h1, ← h2, segment_symm]
      · exact absurd (h1.trans h2.symm) hab
    have hes : convexHull ℝ (e.1 : Set E3) ⊆ segment ℝ a b := by
      rw [← hseg]
      exact hexy
    rcases heuniq e hwe hes with h | h
    · exact ⟨0, h⟩
    · exact ⟨1, h⟩

theorem Section34CompactCutFrame.exists_outerEnum
    (hcut : Section34CompactCutFrame C K K' src srcBd) {w : Section34CompactVertexIndex K K'}
    (hw : (w.1 : Set E3) ⊆ frontier K.space) :
    ∃ (m : ℕ) (sK : Fin (m + 2) → Section34CompactSimplexIndex K 3)
      (eK : Fin (m + 2) → Section34CompactEdgeIndex K K'),
      (∀ k, convexHull ℝ ((sK k).1 : Set E3) ⊆ frontier K.space) ∧
      (∀ k, Section34Incident w.1 (sK k).1) ∧
      (∀ k, w.1 ⊆ (eK k).1) ∧ Function.Injective sK ∧ Function.Injective eK ∧
      (∀ k l, Section34Incident (eK l).1 (sK k).1 ↔ l = k ∨ l + 1 = k) ∧
      (∀ s : Section34CompactSimplexIndex K 3, convexHull ℝ (s.1 : Set E3) ⊆ frontier K.space →
        Section34Incident w.1 s.1 → ∃ k, s = sK k) ∧
      ∀ e : Section34CompactEdgeIndex K K', convexHull ℝ (e.1 : Set E3) ⊆ frontier K.space →
        w.1 ⊆ e.1 → ∃ k, e = eK k := by
  obtain ⟨-, hK, -, hman, -⟩ := id hcut
  obtain ⟨p, hwp⟩ := Finset.card_eq_one.mp w.2.2.1
  have hpw : p ∈ (w.1 : Set E3) := by
    rw [hwp]
    exact Finset.mem_coe.mpr (Finset.mem_singleton_self p)
  have hpb : p ∈ frontier K.space := hw hpw
  let _ : Finite K.faces := hK.to_subtype
  have hpK : p ∈ K.space := (isPolyhedron_space K).isClosed.frontier_subset hpb
  obtain ⟨σ, hσ, hpσ⟩ := exists_face_mem_openSimplex K hpK
  obtain ⟨σ', ⟨hσ', hσ'card⟩, hpσ'⟩ := mem_iUnion₂.mp (w.2.2.2 (subset_convexHull ℝ _ hpw))
  have hle := Finset.card_le_card (face_subset_of_mem_openSimplex_of_mem_convexHull K hσ hσ'
    hpσ hpσ')
  have hpos := Finset.card_pos.mpr (K.nonempty_of_mem_faces hσ)
  have hpconv := openSimplex_subset_convexHull σ hpσ
  by_cases h1 : σ.card = 1
  · obtain ⟨q, rfl⟩ := Finset.card_eq_one.mp h1
    rw [Finset.coe_singleton, convexHull_singleton, mem_singleton_iff] at hpconv
    rw [hpconv] at hwp hpb
    obtain ⟨m, sK, eK, h⟩ := hcut.exists_outerEnum_of_vertex hwp hσ hpb
    exact ⟨m, sK, eK, h⟩
  · obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp (by omega : σ.card = 2)
    have hpab : p ∈ segment ℝ a b := by
      rw [← convexHull_pair, ← Finset.coe_pair]
      exact hpconv
    have hvert : ∀ x : E3, ({x} : Finset E3) ∈ K.faces → p = x → False := fun x hx hpx => by
      have hs := face_subset_of_mem_openSimplex_of_mem_convexHull K hσ hx hpσ
        (by rw [Finset.coe_singleton, convexHull_singleton, hpx]; exact mem_singleton x)
      have := Finset.card_le_card hs
      rw [Finset.card_singleton, Finset.card_pair hab] at this
      omega
    have ha : ({a} : Finset E3) ∈ K.faces :=
      K.down_closed hσ (by simp) (Finset.singleton_nonempty a)
    have hb : ({b} : Finset E3) ∈ K.faces :=
      K.down_closed hσ (by simp) (Finset.singleton_nonempty b)
    have hsegσ : segment ℝ a b = convexHull ℝ (({a, b} : Finset E3) : Set E3) := by
      rw [Finset.coe_pair, convexHull_pair]
    have habb : segment ℝ a b ⊆ frontier K.space := by
      let _ : DecidableEq E3 := Classical.decEq E3
      have hfr : frontier K.space = (boundaryComplex 3 K).space :=
        frontier_space_eq_boundaryComplex_space (n := 2) hman
      have hσL := mem_faces_of_mem_openSimplex_of_mem_space (boundaryComplex_faces_subset 3 K) hσ
        hpσ (by rw [← hfr]; exact hpb)
      rw [hsegσ, hfr]
      exact (boundaryComplex 3 K).convexHull_subset_space hσL
    obtain ⟨sK, eK, h⟩ := hcut.exists_outerEnum_of_edge hab hσ habb hwp hpab (hvert a ha)
      (hvert b hb)
    exact ⟨0, sK, eK, h⟩

end DifferentialGeometry.Topology.PiecewiseLinear
